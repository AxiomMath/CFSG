module

public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge
import CFSG.LocalAnalysis.StandardType.GGLatPerp
import CFSG.LocalAnalysis.StandardType.GGLatPermExc

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

private lemma latGram_smul {N : ℕ} (k : ℤ) (S : Matrix (Fin N) (Fin N) ℤ) (α β : Fin N → ℤ) :
    latGram (k • S) α β = k * latGram S α β := by
  simp only [latGram, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma latGram_single {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (i : Fin N) (α : Fin N → ℤ) :
    latGram S (Pi.single i 1) α = ∑ j, S i j * α j := by
  simp only [latGram]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have hb' : (Pi.single i (1 : ℤ) : Fin N → ℤ) b = 0 := Pi.single_eq_of_ne hb 1
    simp [hb']
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma latLinked_mem_iff {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (Φ : Set (Fin N → ℤ))
    {a b : Fin N → ℤ} (h : latLinked S Φ a b) : a ∈ Φ ↔ b ∈ Φ := by
  induction h with
  | rel x y hab => exact ⟨fun _ => hab.2.1, fun _ => hab.1⟩
  | refl x => exact Iff.rfl
  | symm x y a ih => exact ih.symm
  | trans x y z a a' ih1 ih2 => exact ih1.trans ih2

private lemma perp_latPerm_mem {N : ℕ} {S : Matrix (Fin N) (Fin N) ℤ} {π : Equiv.Perm (Fin N)}
    (hGram : ∀ a b, latGram S (latPerm π a) (latPerm π b) = latGram S a b)
    {R : Set (Fin N → ℤ)} (hR : ∀ β ∈ R, latPerm π β ∈ R)
    {α : Fin N → ℤ} (hα : latPerm π α = α) {β : Fin N → ℤ}
    (hβ : β ∈ perp R S α) : latPerm π β ∈ perp R S α := by
  obtain ⟨hβR, hβ0⟩ := hβ
  have h := hGram α β
  rw [hα] at h
  exact ⟨hR β hβR, by rw [h, hβ0]⟩

private lemma isCompOrbit_perp {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (π : Equiv.Perm (Fin N))
    (R : Set (Fin N → ℤ)) {α : Fin N → ℤ}
    (hne : (perp R S α).Nonempty)
    (hlink : ∀ β ∈ perp R S α, ∀ γ ∈ perp R S α, latLinked S (perp R S α) β γ)
    (hstable : ∀ β ∈ perp R S α, latPerm π β ∈ perp R S α) :
    IsCompOrbit S π (perp R S α) (perp R S α) := by
  obtain ⟨a, ha⟩ := hne
  refine ⟨a, ha, ?_⟩
  ext β
  constructor
  · intro hβ
    exact ⟨0, hlink a ha β hβ⟩
  · rintro ⟨k, hk⟩
    have hpow : ∀ k : ℕ, (latPerm π)^[k] a ∈ perp R S α := by
      intro k
      induction k with
      | zero => simpa using ha
      | succ k ih =>
        simpa only [Function.iterate_succ_apply', Function.comp_apply] using hstable _ ih
    exact (latLinked_mem_iff S (perp R S α) hk).mp (hpow k)

private lemma not_latSolv_of_ncard {N : ℕ} {π : Equiv.Perm (Fin N)} {O : Set (Fin N → ℤ)}
    (h7 : 7 ≤ O.ncard) (q2 : Prop) : ¬ LatSolv q2 π O := by
  rintro ⟨-, h | ⟨h6, -⟩⟩
  · obtain ⟨γ, hγ⟩ := h
    have hle : O.ncard ≤ 2 := by
      rw [hγ]
      have h := Set.ncard_insert_le γ ({-γ} : Set (Fin N → ℤ))
      rw [Set.ncard_singleton] at h
      omega
    omega
  · omega

private lemma card_fixed_ann_perp_le {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ)
    (π : Equiv.Perm (Fin N)) (R : Set (Fin N → ℤ)) (p : ℕ) (hp : p.Prime) {α : Fin N → ℤ}
    (hcard : Nat.card {f : Fin N → ZMod p // ∀ β ∈ perp R S α, latChar p f β = 0} = p) :
    Nat.card {g : Fin N → ZMod p // (∀ i, g (π i) = g i) ∧
      ∀ β ∈ perp R S α, latChar p g β = 0} ≤ p ^ 2 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set T := {g : Fin N → ZMod p // (∀ i, g (π i) = g i) ∧ ∀ β ∈ perp R S α, latChar p g β = 0}
  have hinj : Function.Injective (fun g : T =>
      (⟨g.1, g.2.2⟩ : {f : Fin N → ZMod p // ∀ β ∈ perp R S α, latChar p f β = 0})) := by
    intro g h hgh
    have hval : (g : Fin N → ZMod p) = (h : Fin N → ZMod p) :=
      congrArg (fun x : {f : Fin N → ZMod p // ∀ β ∈ perp R S α, latChar p f β = 0} =>
        (x : Fin N → ZMod p)) hgh
    exact Subtype.ext hval
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [hcard] at hle
  calc Nat.card T ≤ p := hle
    _ ≤ p ^ 2 := by
      have h := Nat.le_mul_self p
      rw [pow_two]
      exact h

private lemma corootCoord_latPerm_fixed {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ)
    (π : Equiv.Perm (Fin N)) (p : ℕ)
    (hGram : ∀ a b, latGram S (latPerm π a) (latPerm π b) = latGram S a b)
    {α : Fin N → ℤ} (hα : latPerm π α = α) :
    ∀ i, corootCoord p S α (π i) = corootCoord p S α i := by
  intro i
  have hsingle : latPerm π (Pi.single i 1) = Pi.single (π i) 1 := by
    ext j
    simp only [latPerm, Pi.single_apply, Equiv.symm_apply_eq]
  have h1 := hGram (Pi.single i 1) α
  rw [hsingle, hα] at h1
  unfold corootCoord
  rw [h1]

private lemma corootCoord_ne_zero {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ)
    (R : Set (Fin N → ℤ)) (p : ℕ) {α : Fin N → ℤ} (hα : α ∈ R)
    (hPhi : latPhi R p (corootCoord p S α) = perp R S α)
    (hself : latGram S α α ≠ 0) : corootCoord p S α ≠ 0 := by
  intro hzero
  have hperp_eq : perp R S α = R := by
    rw [← hPhi, hzero]
    ext β
    simp only [latPhi, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hβ, -⟩; exact hβ
    · intro hβ; exact ⟨hβ, by simp [latChar]⟩
  have h0 : latGram S α α = 0 := (show α ∈ perp R S α from by rw [hperp_eq]; exact hα).2
  exact hself h0

private lemma latGram_self_ne_zero_of_smul {N : ℕ} (M : Matrix (Fin N) (Fin N) ℤ)
    (S : Matrix (Fin N) (Fin N) ℤ) (k : ℕ) (hk : 0 < k) (hkS : S = (k : ℤ) • M)
    {α : Fin N → ℤ} (hpos : 0 < latGram M α α) : latGram S α α ≠ 0 := by
  rw [hkS, latGram_smul]
  have hkz : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  exact ne_of_gt (mul_pos hkz hpos)

private lemma exists_compOrbit_ann_le {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ)
    (π : Equiv.Perm (Fin N)) (R : Set (Fin N → ℤ)) (p : ℕ) (hp : p.Prime) {α : Fin N → ℤ}
    (hPhi : latPhi R p (corootCoord p S α) = perp R S α)
    (hlink : ∀ β ∈ perp R S α, ∀ γ ∈ perp R S α, latLinked S (perp R S α) β γ)
    (hcard : Nat.card {f : Fin N → ZMod p // ∀ β ∈ perp R S α, latChar p f β = 0} = p)
    (h7 : 7 ≤ (perp R S α).ncard)
    (hGram : ∀ a b, latGram S (latPerm π a) (latPerm π b) = latGram S a b)
    (hRstable : ∀ β ∈ R, latPerm π β ∈ R)
    (hαfix : latPerm π α = α) :
    ∀ q2 : Prop, ∃ O, IsCompOrbit S π (latPhi R p (corootCoord p S α)) O ∧
      ¬ LatSolv q2 π O ∧
      Nat.card {g : Fin N → ZMod p // (∀ i, g (π i) = g i) ∧
        ∀ β ∈ O, latChar p g β = 0} ≤ p ^ 2 := by
  intro q2
  refine ⟨perp R S α, ?_, ?_, ?_⟩
  · rw [hPhi]
    exact isCompOrbit_perp S π R (by
      rw [Set.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty, Set.ncard_empty] at h7
      omega) hlink (fun β hβ => perp_latPerm_mem hGram hRstable hαfix hβ)
  · exact not_latSolv_of_ncard h7 q2
  · exact card_fixed_ann_perp_le S π R p hp hcard

private theorem latGram_symCartan_pos_F4 :
    ∀ α ∈ rootFinset Tag.F4, 0 < latGram (Tag.symmetrizedCartan .F4) α α := by
  decide +kernel

private theorem latGram_symCartan_pos_E7 :
    ∀ α ∈ rootFinset Tag.E7, 0 < latGram (Tag.symmetrizedCartan .E7) α α := by
  decide +kernel

private theorem latGram_symCartan_pos_E8 :
    ∀ α ∈ rootFinset Tag.E8, 0 < latGram (Tag.symmetrizedCartan .E8) α α := by
  decide +kernel

private theorem latGram_cartan_E6_two :
    ∀ α ∈ rootFinset Tag.E6, latGram (Tag.cartan .E6) α α = 2 := by
  decide +kernel

private theorem cartan_E6_symm (i j : Fin 6) : Tag.cartan .E6 i j = Tag.cartan .E6 j i := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem symmetrizedCartan_E6 :
    Tag.symmetrizedCartan .E6 = (Tag.cartan .E6 : Matrix (Fin 6) (Fin 6) ℤ) := by
  rw [Tag.symmetrizedCartan, Tag.symmetrizer, Matrix.one_mul]

private lemma excFive_F4 : GGExcFive .F4 := Or.inl rfl

private lemma excFive_E6 : GGExcFive .E6 := Or.inr (Or.inl rfl)

private lemma excFive_E7 : GGExcFive .E7 := Or.inr (Or.inr (Or.inl rfl))

private lemma excFive_E8 : GGExcFive .E8 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))

private def CorootConj {U' : Type} [Group U'] (Δ : UniversalRootDatum U')
    (S : Matrix (Fin Δ.rank) (Fin Δ.rank) ℤ) (π : Equiv.Perm (Fin Δ.rank)) (p : ℕ)
    (α : Fin Δ.rank → ℤ) : Prop :=
  corootCoord p S α ∈ LatCorootSpan Δ p ∧
  (∀ i, corootCoord p S α (π i) = corootCoord p S α i) ∧
  corootCoord p S α ≠ 0 ∧
  ∀ q2 : Prop, ∃ O,
    IsCompOrbit S π (latPhi Δ.roots p (corootCoord p S α)) O ∧
    ¬ LatSolv q2 π O ∧
    Nat.card {g : Fin Δ.rank → ZMod p //
      (∀ i, g (π i) = g i) ∧ ∀ β ∈ O, latChar p g β = 0} ≤ p ^ 2

section Coroot

private lemma corootCoord_mem_latCorootSpan_E6_three (f : ℕ)
    (S : Matrix (Fin (ggU .E6 6 f).D.rank) (Fin (ggU .E6 6 f).D.rank) ℤ)
    (hS : IsRootGram (ggU .E6 6 f).D S)
    (α : Fin (ggU .E6 6 f).D.rank → ℤ) (hα : α ∈ (ggU .E6 6 f).D.roots) :
    corootCoord 3 S α ∈ LatCorootSpan (ggU .E6 6 f).D 3 := by
  obtain ⟨k, hkpos, hkS⟩ := isRootGram_E6 6 f S hS
  have hroot : α ∈ rootFinset Tag.E6 := (mem_roots_E6 6 f α).mp hα
  have hquad : latGram (Tag.cartan .E6) α α = 2 := latGram_cartan_E6_two α hroot
  have hk2 : (k : ℤ) * 2 ≠ 0 := by
    have hkz : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hkpos
    exact mul_ne_zero (ne_of_gt hkz) (by norm_num)
  have hME : Tag.symmetrizedCartan .E6 = (Tag.cartan .E6 : Matrix (Fin 6) (Fin 6) ℤ) :=
    symmetrizedCartan_E6
  refine ⟨α, ?_⟩
  intro i
  have hsingle : latGram (Tag.cartan .E6) (Pi.single i 1) α
      = ∑ j, Tag.cartan .E6 i j * α j := latGram_single _ i α
  have hl : latGram S (Pi.single i 1) α
      = (k : ℤ) * ∑ j, Tag.cartan .E6 i j * α j := by
    rw [hkS]
    calc latGram ((k : ℤ) • Tag.symmetrizedCartan .E6) (Pi.single i 1) α
        = (k : ℤ) * latGram (Tag.symmetrizedCartan .E6) (Pi.single i 1) α :=
          latGram_smul (k : ℤ) (Tag.symmetrizedCartan .E6) (Pi.single i 1) α
      _ = (k : ℤ) * latGram (Tag.cartan .E6) (Pi.single i 1) α := by rw [hME]
      _ = (k : ℤ) * ∑ j, Tag.cartan .E6 i j * α j := by rw [hsingle]
  have hr : latGram S α α = (k : ℤ) * 2 := by
    rw [hkS]
    calc latGram ((k : ℤ) • Tag.symmetrizedCartan .E6) α α
        = (k : ℤ) * latGram (Tag.symmetrizedCartan .E6) α α :=
          latGram_smul (k : ℤ) (Tag.symmetrizedCartan .E6) α α
      _ = (k : ℤ) * latGram (Tag.cartan .E6) α α := by rw [hME]
      _ = (k : ℤ) * 2 := by rw [hquad]
  have hq : 2 * latGram S (Pi.single i 1) α / latGram S α α
      = ∑ j, Tag.cartan .E6 i j * α j := by
    rw [hl, hr]
    have hn : 2 * ((k : ℤ) * (∑ j, Tag.cartan .E6 i j * α j))
        = (∑ j, Tag.cartan .E6 i j * α j) * ((k : ℤ) * 2) := by ring
    rw [hn]
    exact Int.mul_ediv_cancel _ hk2
  unfold corootCoord
  rw [hq, ggU_cartan_E6 6 f]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cartan_E6_symm i j]
  ring

private lemma coroot_F4 (f : ℕ)
    (S : Matrix (Fin (ggU .F4 6 f).D.rank) (Fin (ggU .F4 6 f).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU .F4 6 f).D.rank))
    (hS : IsRootGram (ggU .F4 6 f).D S) (hπ : IsDiagAut (ggU .F4 6 f).D π)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : Fin (ggU .F4 6 f).D.rank → ℤ) (hα : α ∈ (ggU .F4 6 f).D.roots)
    (hαfix : latPerm π α = α) : CorootConj (ggU .F4 6 f).D S π p α := by
  unfold CorootConj
  have hconn : NodesConnected (ggU .F4 6 f).D Set.univ :=
    nodesConnected_univ_exc .F4 f excFive_F4
  have hGram : ∀ a b, latGram S (latPerm π a) (latPerm π b) = latGram S a b :=
    fun a b => latGram_latPerm _ S hS π hπ hconn a b
  have hRstable : ∀ β ∈ (ggU .F4 6 f).D.roots, latPerm π β ∈ (ggU .F4 6 f).D.roots :=
    fun β hβ => latPerm_mem_roots_exc .F4 f excFive_F4 π hπ hβ
  obtain ⟨hPhi, hlink, hcard, h7⟩ :=
    ggLatPerpExc_holds .F4 f excFive_F4 S hS α hα p hp hp2
  obtain ⟨k, hkpos, hkS⟩ := isRootGram_F4 6 f S hS
  have hroot : α ∈ rootFinset Tag.F4 := (mem_roots_F4 6 f α).mp hα
  have hself : latGram S α α ≠ 0 :=
    latGram_self_ne_zero_of_smul _ _ k hkpos hkS (latGram_symCartan_pos_F4 α hroot)
  have hspan : corootCoord p S α ∈ LatCorootSpan (ggU .F4 6 f).D p := by
    refine latCorootSpan_eq_top (ggU .F4 6 f).D p hp ?_ (corootCoord p S α)
    change ¬ (p : ℤ) ∣ (Tag.cartan .F4).det
    rw [det_cartan_F4]
    intro h
    have h1 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h
    have hp2' : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    omega
  refine ⟨hspan, corootCoord_latPerm_fixed S π p hGram hαfix, ?_, ?_⟩
  · exact corootCoord_ne_zero S _ p hα hPhi hself
  · exact exists_compOrbit_ann_le S π _ p hp hPhi hlink hcard h7 hGram hRstable hαfix

private lemma coroot_E6 (f : ℕ)
    (S : Matrix (Fin (ggU .E6 6 f).D.rank) (Fin (ggU .E6 6 f).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU .E6 6 f).D.rank))
    (hS : IsRootGram (ggU .E6 6 f).D S) (hπ : IsDiagAut (ggU .E6 6 f).D π)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : Fin (ggU .E6 6 f).D.rank → ℤ) (hα : α ∈ (ggU .E6 6 f).D.roots)
    (hαfix : latPerm π α = α) : CorootConj (ggU .E6 6 f).D S π p α := by
  unfold CorootConj
  have hconn : NodesConnected (ggU .E6 6 f).D Set.univ :=
    nodesConnected_univ_exc .E6 f excFive_E6
  have hGram : ∀ a b, latGram S (latPerm π a) (latPerm π b) = latGram S a b :=
    fun a b => latGram_latPerm _ S hS π hπ hconn a b
  have hRstable : ∀ β ∈ (ggU .E6 6 f).D.roots, latPerm π β ∈ (ggU .E6 6 f).D.roots :=
    fun β hβ => latPerm_mem_roots_exc .E6 f excFive_E6 π hπ hβ
  obtain ⟨hPhi, hlink, hcard, h7⟩ :=
    ggLatPerpExc_holds .E6 f excFive_E6 S hS α hα p hp hp2
  obtain ⟨k, hkpos, hkS⟩ := isRootGram_E6 6 f S hS
  have hroot : α ∈ rootFinset Tag.E6 := (mem_roots_E6 6 f α).mp hα
  have hself : latGram S α α ≠ 0 :=
    latGram_self_ne_zero_of_smul (Tag.symmetrizedCartan .E6) S k hkpos hkS
      (by rw [symmetrizedCartan_E6, latGram_cartan_E6_two α hroot]; norm_num)
  have hspan : corootCoord p S α ∈ LatCorootSpan (ggU .E6 6 f).D p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact corootCoord_mem_latCorootSpan_E6_three f S hS α hα
    · refine latCorootSpan_eq_top (ggU .E6 6 f).D p hp ?_ (corootCoord p S α)
      change ¬ (p : ℤ) ∣ (Tag.cartan .E6).det
      rw [det_cartan_E6]
      intro h
      have h' : p ∣ 3 := by exact_mod_cast h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp h')
  refine ⟨hspan, corootCoord_latPerm_fixed S π p hGram hαfix, ?_, ?_⟩
  · exact corootCoord_ne_zero S _ p hα hPhi hself
  · exact exists_compOrbit_ann_le S π _ p hp hPhi hlink hcard h7 hGram hRstable hαfix

private lemma coroot_E7 (f : ℕ)
    (S : Matrix (Fin (ggU .E7 6 f).D.rank) (Fin (ggU .E7 6 f).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU .E7 6 f).D.rank))
    (hS : IsRootGram (ggU .E7 6 f).D S) (hπ : IsDiagAut (ggU .E7 6 f).D π)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : Fin (ggU .E7 6 f).D.rank → ℤ) (hα : α ∈ (ggU .E7 6 f).D.roots)
    (hαfix : latPerm π α = α) : CorootConj (ggU .E7 6 f).D S π p α := by
  unfold CorootConj
  have hconn : NodesConnected (ggU .E7 6 f).D Set.univ :=
    nodesConnected_univ_exc .E7 f excFive_E7
  have hGram : ∀ a b, latGram S (latPerm π a) (latPerm π b) = latGram S a b :=
    fun a b => latGram_latPerm _ S hS π hπ hconn a b
  have hRstable : ∀ β ∈ (ggU .E7 6 f).D.roots, latPerm π β ∈ (ggU .E7 6 f).D.roots :=
    fun β hβ => latPerm_mem_roots_exc .E7 f excFive_E7 π hπ hβ
  obtain ⟨hPhi, hlink, hcard, h7⟩ :=
    ggLatPerpExc_holds .E7 f excFive_E7 S hS α hα p hp hp2
  obtain ⟨k, hkpos, hkS⟩ := isRootGram_E7 6 f S hS
  have hroot : α ∈ rootFinset Tag.E7 := (mem_roots_E7 6 f α).mp hα
  have hself : latGram S α α ≠ 0 :=
    latGram_self_ne_zero_of_smul _ _ k hkpos hkS (latGram_symCartan_pos_E7 α hroot)
  have hspan : corootCoord p S α ∈ LatCorootSpan (ggU .E7 6 f).D p := by
    refine latCorootSpan_eq_top (ggU .E7 6 f).D p hp ?_ (corootCoord p S α)
    change ¬ (p : ℤ) ∣ (Tag.cartan .E7).det
    rw [det_cartan_E7]
    intro h
    have h' : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  refine ⟨hspan, corootCoord_latPerm_fixed S π p hGram hαfix, ?_, ?_⟩
  · exact corootCoord_ne_zero S _ p hα hPhi hself
  · exact exists_compOrbit_ann_le S π _ p hp hPhi hlink hcard h7 hGram hRstable hαfix

private lemma coroot_E8 (f : ℕ)
    (S : Matrix (Fin (ggU .E8 6 f).D.rank) (Fin (ggU .E8 6 f).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU .E8 6 f).D.rank))
    (hS : IsRootGram (ggU .E8 6 f).D S) (hπ : IsDiagAut (ggU .E8 6 f).D π)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : Fin (ggU .E8 6 f).D.rank → ℤ) (hα : α ∈ (ggU .E8 6 f).D.roots)
    (hαfix : latPerm π α = α) : CorootConj (ggU .E8 6 f).D S π p α := by
  unfold CorootConj
  have hconn : NodesConnected (ggU .E8 6 f).D Set.univ :=
    nodesConnected_univ_exc .E8 f excFive_E8
  have hGram : ∀ a b, latGram S (latPerm π a) (latPerm π b) = latGram S a b :=
    fun a b => latGram_latPerm _ S hS π hπ hconn a b
  have hRstable : ∀ β ∈ (ggU .E8 6 f).D.roots, latPerm π β ∈ (ggU .E8 6 f).D.roots :=
    fun β hβ => latPerm_mem_roots_exc .E8 f excFive_E8 π hπ hβ
  obtain ⟨hPhi, hlink, hcard, h7⟩ :=
    ggLatPerpExc_holds .E8 f excFive_E8 S hS α hα p hp hp2
  obtain ⟨k, hkpos, hkS⟩ := isRootGram_E8 6 f S hS
  have hroot : α ∈ rootFinset Tag.E8 := (mem_roots_E8 6 f α).mp hα
  have hself : latGram S α α ≠ 0 :=
    latGram_self_ne_zero_of_smul _ _ k hkpos hkS (latGram_symCartan_pos_E8 α hroot)
  have hspan : corootCoord p S α ∈ LatCorootSpan (ggU .E8 6 f).D p := by
    refine latCorootSpan_eq_top (ggU .E8 6 f).D p hp ?_ (corootCoord p S α)
    change ¬ (p : ℤ) ∣ (Tag.cartan .E8).det
    rw [det_cartan_E8]
    intro h
    have h1 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h
    have hp2' : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    omega
  refine ⟨hspan, corootCoord_latPerm_fixed S π p hGram hαfix, ?_, ?_⟩
  · exact corootCoord_ne_zero S _ p hα hPhi hself
  · exact exists_compOrbit_ann_le S π _ p hp hPhi hlink hcard h7 hGram hRstable hαfix

@[expose] def GGLatCorootExc : Prop :=
  ∀ (τ : StatedLieTag) (f : ℕ), GGExcFive τ →
    ∀ (S : Matrix (Fin (ggU (absTag τ) 6 f).D.rank) (Fin (ggU (absTag τ) 6 f).D.rank) ℤ)
      (π : Equiv.Perm (Fin (ggU (absTag τ) 6 f).D.rank)),
      IsRootGram (ggU (absTag τ) 6 f).D S → IsDiagAut (ggU (absTag τ) 6 f).D π →
      ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ α ∈ (ggU (absTag τ) 6 f).D.roots, latPerm π α = α →
        corootCoord p S α ∈ LatCorootSpan (ggU (absTag τ) 6 f).D p ∧
        (∀ i, corootCoord p S α (π i) = corootCoord p S α i) ∧
        corootCoord p S α ≠ 0 ∧
        ∀ q2 : Prop, ∃ O,
          IsCompOrbit S π (latPhi (ggU (absTag τ) 6 f).D.roots p (corootCoord p S α)) O ∧
          ¬ LatSolv q2 π O ∧
          Nat.card {g : Fin (ggU (absTag τ) 6 f).D.rank → ZMod p //
            (∀ i, g (π i) = g i) ∧ ∀ β ∈ O, latChar p g β = 0} ≤ p ^ 2

theorem ggLatCorootExc_holds : GGLatCorootExc := by
  unfold GGLatCorootExc
  intro τ f hτ S π hS hπ p hp hp2 α hα hαfix
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact coroot_F4 f S π hS hπ p hp hp2 α hα hαfix
  · exact coroot_E6 f S π hS hπ p hp hp2 α hα hαfix
  · exact coroot_E7 f S π hS hπ p hp hp2 α hα hαfix
  · exact coroot_E8 f S π hS hπ p hp hp2 α hα hαfix
  · exact coroot_E6 f S π hS hπ p hp hp2 α hα hαfix

end Coroot

end CFSG.StandardType

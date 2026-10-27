module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KJ3
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import Certificates.Certificate799250

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Blueprint Subgroup
open scoped Pointwise

section Group

theorem exists_sylow_mem_pair {C : Type*} [Group C] [Finite C] {x y : C} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) (hxy : x * y = y * x) :
    ∃ Q : Sylow 3 C, x ∈ (Q : Subgroup C) ∧ y ∈ (Q : Subgroup C) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K : Subgroup C := closure ({x, y} : Set C) with hK
  have hpair : ({x, y} : Set C).Pairwise Commute := by
    intro u hu v hv _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact Commute.refl _
    · exact hxy
    · exact hxy.symm
    · exact Commute.refl _
  have hKcomm : ∀ u ∈ K, ∀ v ∈ K, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val ((Subgroup.isMulCommutative_closure hpair).is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hKexp : ∀ k ∈ K, k ^ 3 = 1 := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem a ha =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact hx
      · exact hy
    | one => exact one_pow 3
    | mul a b ha hb hae hbe =>
      rw [(Commute.mul_pow (hKcomm a ha b hb) 3 :), hae, hbe, one_mul]
    | inv a ha hae => rw [inv_pow, hae, inv_one]
  have hKp : IsPGroup 3 K := fun g => ⟨1, Subtype.ext (by simpa using hKexp g.1 g.2)⟩
  obtain ⟨Q, hQ⟩ := hKp.exists_le_sylow
  exact ⟨Q, hQ (subset_closure (Set.mem_insert _ _)),
    hQ (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩

theorem mem_zpowers_of_zpowers_nine {C : Type*} [Group C] {c x y : C} (hc : orderOf c = 9)
    (hxc : x ∈ zpowers c) (hyc : y ∈ zpowers c) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hx1 : x ≠ 1) :
    y ∈ zpowers x := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hxc
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hyc
  have hdvd : ∀ m : ℤ, (c ^ m) ^ 3 = 1 → (3 : ℤ) ∣ m := by
    intro m hm
    rw [← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hc] at hm
    omega
  obtain ⟨a, rfl⟩ := hdvd i hx
  obtain ⟨b, rfl⟩ := hdvd j hy
  have ha : ¬ (3 : ℤ) ∣ a := by
    rintro ⟨a', rfl⟩
    apply hx1
    rw [show (3 * (3 * a') : ℤ) = 9 * a' by ring, zpow_mul, zpow_ofNat, ← hc, pow_orderOf_eq_one,
      one_zpow]
  have h3 : (3 : ℤ) ∣ 1 - a ^ 2 := by
    have hz : (a : ZMod 3) ≠ 0 := fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp h)
    have h0 : ((1 - a ^ 2 : ℤ) : ZMod 3) = 0 := by
      push_cast
      revert hz
      generalize (a : ZMod 3) = z
      revert z
      decide
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (1 - a ^ 2) 3).mp h0
  obtain ⟨q, hq⟩ := h3
  refine mem_zpowers_iff.mpr ⟨a * b, ?_⟩
  rw [← zpow_mul, zpow_eq_zpow_iff_modEq, hc]
  refine (Int.modEq_iff_dvd).2 ⟨q * b, ?_⟩
  push_cast
  linear_combination (3 * b) * hq

theorem mem_zpowers_of_sylow_nine {C : Type*} [Group C] [Finite C]
    (hfac : (Nat.card C).factorization 3 = 2) {c : C} (hc : orderOf c = 9) {x y : C}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) :
    y ∈ zpowers x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q₁, hxQ, hyQ⟩ := exists_sylow_mem_pair hx hy hxy
  have hcp : IsPGroup 3 (zpowers c) := by
    intro g
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp g.2
    refine ⟨2, Subtype.ext ?_⟩
    show (g : C) ^ 3 ^ 2 = 1
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      show 3 ^ 2 = orderOf c by rw [hc]; norm_num, pow_orderOf_eq_one, one_zpow]
  obtain ⟨Q₂, hQ₂⟩ := hcp.exists_le_sylow
  have hQ₂card : Nat.card Q₂ = 9 := by rw [Sylow.card_eq_multiplicity, hfac]; norm_num
  have hQ₂eq : zpowers c = (Q₂ : Subgroup C) :=
    Subgroup.eq_of_le_of_card_ge hQ₂ (by rw [hQ₂card, Nat.card_zpowers, hc])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Q₂ Q₁
  have hQ₁eq : (Q₁ : Subgroup C) = zpowers (g * c * g⁻¹) := by
    have h1 : (Q₁ : Subgroup C) = MulAut.conj g • (Q₂ : Subgroup C) := by rw [← hg]; rfl
    rw [h1, ← hQ₂eq]
    ext z
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hk' : g⁻¹ * z * g = c ^ k := by
        simpa [MulAut.smul_def, MulAut.conj_apply] using hk.symm
      rw [conj_zpow]
      calc g * c ^ k * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hk']
        _ = z := by group
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [conj_zpow] at hk
      have hinv : (MulAut.conj g)⁻¹ • z = g⁻¹ * z * g := by
        rw [← map_inv (MulAut.conj : C →* MulAut C) g, MulAut.smul_def, MulAut.conj_apply,
          inv_inv]
      rw [hinv, ← hk]
      group
  have hord : orderOf (g * c * g⁻¹) = 9 := by
    rw [← hc]
    exact (MulAut.conj g).orderOf_eq c
  rw [hQ₁eq] at hxQ hyQ
  exact mem_zpowers_of_zpowers_nine hord hxQ hyQ hx hy hx1

theorem mem_zpowers_of_sylow_three {C : Type*} [Group C] [Finite C]
    (hfac : (Nat.card C).factorization 3 = 1) {x y : C}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) :
    y ∈ zpowers x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hxQ, hyQ⟩ := exists_sylow_mem_pair hx hy hxy
  have hQcard : Nat.card Q = 3 := by rw [Sylow.card_eq_multiplicity, hfac]; norm_num
  have hxo : orderOf x = 3 := orderOf_eq_prime hx hx1
  have hle : zpowers x ≤ (Q : Subgroup C) := (zpowers_le).mpr hxQ
  have heq : zpowers x = (Q : Subgroup C) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hQcard, Nat.card_zpowers, hxo])
  rw [heq]
  exact hyQ

end Group

section Perm

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem j3_fold_spec
    {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    ∀ (T : Table) (g : Equiv.Perm (Fin 6156)), Rep 6156 T g → g ∈ j3P →
      Rep 6156 (w.foldl (fun T l => compT 6156 T j3PGTbls[l]!) T)
        (w.foldl (fun g l => g * j3Gen l) g) ∧ w.foldl (fun g l => g * j3Gen l) g ∈ j3P := by
  induction w with
  | nil => intro T g hT hg; exact ⟨hT, hg⟩
  | cons l w ih =>
    intro T g hT hg
    have hl : l < j3PGTbls.size := by
      have hsz : j3PGTbls.size = 2 := rfl
      rw [hsz]
      exact hw l List.mem_cons_self
    simp only [List.foldl_cons]
    exact ih (fun l' hl' => hw l' (List.mem_cons_of_mem l hl')) (compT 6156 T j3PGTbls[l]!)
      (g * j3Gen l) (Rep.compT hT (j3_groupData.rep l hl))
      (j3P.mul_mem hg (j3_groupData.mem hl))

theorem j3_nine :
    ∃ c ∈ j3P, c * tp 6156 (j3CentTbl 21) = tp 6156 (j3CentTbl 21) * c ∧ orderOf c = 9 := by
  have hOK : (permOK 6156 (j3CentTbl 21) && permOK 6156 (j3NineTbl ()) &&
      commTT 6156 (j3NineTbl ()) (j3CentTbl 21) && ordTest 6156 9 (j3NineTbl ())) = true :=
    Certificates.certificate799250
  simp only [Bool.and_eq_true] at hOK
  obtain ⟨⟨⟨hp2, hpc⟩, hcomm⟩, hord⟩ := hOK
  have hw : ∀ l ∈ j3NineWord, l < 2 := by decide
  obtain ⟨hrep, hmem⟩ := j3_fold_spec hw (idT 6156) 1 (Rep.idT (by norm_num)) (one_mem _)
  have hT : j3NineTbl () = j3NineWord.foldl (fun T l => compT 6156 T j3PGTbls[l]!) (idT 6156) :=
    rfl
  rw [hT] at hcomm hord
  refine ⟨_, hmem, ?_, ?_⟩
  · exact (commTT_iff hrep (rep_tp hp2)).mp hcomm
  · exact (ordTest_iff_perm hrep (by norm_num)).mp hord

theorem j3_perm_aux {t g x y : Equiv.Perm (Fin 6156)} (hg : g ∈ j3P) (hx : x ∈ j3P) (hy : y ∈ j3P)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1)
    (hrx : g * t * g⁻¹ * x = x * (g * t * g⁻¹)) (hry : g * t * g⁻¹ * y = y * (g * t * g⁻¹))
    (hsyl : ∀ X Y : ↥(j3P ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 6156)))),
      X ^ 3 = 1 → Y ^ 3 = 1 → X * Y = Y * X → X ≠ 1 → Y ∈ Subgroup.zpowers X) :
    y ∈ Subgroup.zpowers x := by
  set C := j3P ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 6156))) with hC
  have hcomm : ∀ z, z ∈ j3P → g * t * g⁻¹ * z = z * (g * t * g⁻¹) → g⁻¹ * z * g ∈ C := by
    intro z hz hrz
    refine Subgroup.mem_inf.mpr ⟨j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hg) hz) hg, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    calc h * (g⁻¹ * z * g) = g⁻¹ * (g * h * g⁻¹ * z) * g := by group
      _ = g⁻¹ * (z * (g * h * g⁻¹)) * g := by rw [hrz]
      _ = g⁻¹ * z * g * h := by group
  have hcube : ∀ z : Equiv.Perm (Fin 6156), z ^ 3 = 1 → (g⁻¹ * z * g) ^ 3 = 1 := by
    intro z hz
    have h := conj_pow (a := g⁻¹) (b := z) (i := 3)
    rw [inv_inv] at h
    rw [h, hz]
    group
  let X : C := ⟨g⁻¹ * x * g, hcomm x hx hrx⟩
  let Y : C := ⟨g⁻¹ * y * g, hcomm y hy hry⟩
  have hXY : X * Y = Y * X := Subtype.ext (by
    show g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * y * g * (g⁻¹ * x * g)
    calc g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
      _ = g⁻¹ * (y * x) * g := by rw [hxy]
      _ = g⁻¹ * y * g * (g⁻¹ * x * g) := by group)
  have hX1 : X ≠ 1 := fun h => hx1 (by
    have h' : g⁻¹ * x * g = 1 := congrArg Subtype.val h
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h']; group)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp
    (hsyl X Y (Subtype.ext (hcube x hx3)) (Subtype.ext (hcube y hy3)) hXY hX1)
  have hk' : (g⁻¹ * x * g) ^ k = g⁻¹ * y * g := congrArg Subtype.val hk
  refine mem_zpowers_iff.mpr ⟨k, ?_⟩
  have h2 : (g⁻¹ * x * g) ^ k = g⁻¹ * x ^ k * g := by
    rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by group, conj_zpow]
    simp
  rw [h2] at hk'
  calc x ^ k = g * (g⁻¹ * x ^ k * g) * g⁻¹ := by group
    _ = g * (g⁻¹ * y * g) * g⁻¹ := by rw [hk']
    _ = y := by group

theorem j3Rows_cases {ρ : ClassRow} (hρ : ρ ∈ j3Rows) :
    (ρ.rep = j3CentTbl 9 ∧ ρ.centOrder = 1920) ∨ (ρ.rep = j3CentTbl 21 ∧ ρ.centOrder = 2448) := by
  simp only [j3Rows, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl
  · exact Or.inl ⟨by simp, by simp⟩
  · exact Or.inr ⟨by simp, by simp⟩

theorem j3_perm_no_involution
    {r x y : Equiv.Perm (Fin 6156)} (hr : r ∈ j3R) (hr2 : r * r = 1) (hr1 : r ≠ 1)
    (hx : x ∈ j3P) (hy : y ∈ j3P) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x)
    (hx1 : x ≠ 1) (hrx : r * x = x * r) (hry : r * y = y * r) : y ∈ Subgroup.zpowers x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ :=
    ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  have hord : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hr2) hr1
  obtain ⟨ρ, hρ, g, hg, hrg⟩ := hcover r hr hord
  obtain ⟨-, -, -, -, hcard, -⟩ := hrows ρ hρ
  rw [hrg] at hrx hry
  rcases j3Rows_cases hρ with ⟨hrep, hcent⟩ | ⟨hrep, hcent⟩
  ·
    rw [hrep] at hrx hry hcard
    rw [hcent] at hcard
    refine j3_perm_aux hg hx hy hx3 hy3 hxy hx1 hrx hry ?_
    intro X Y hX hY hXY hX1
    refine mem_zpowers_of_sylow_three ?_ hX hY hXY hX1
    rw [hcard, Nat.factorization_def _ Nat.prime_three]
    decide +kernel
  ·
    rw [hrep] at hrx hry hcard
    rw [hcent] at hcard
    obtain ⟨c, hcP, hcomm, hcord⟩ := j3_nine
    have hcC : c ∈ j3P ⊓ Subgroup.centralizer ({tp 6156 (j3CentTbl 21)} :
        Set (Equiv.Perm (Fin 6156))) := by
      refine Subgroup.mem_inf.mpr ⟨hcP, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hcomm.symm
    refine j3_perm_aux hg hx hy hx3 hy3 hxy hx1 hrx hry ?_
    intro X Y hX hY hXY hX1
    refine mem_zpowers_of_sylow_nine (c := (⟨c, hcC⟩ : ↥(j3P ⊓ Subgroup.centralizer
      ({tp 6156 (j3CentTbl 21)} : Set (Equiv.Perm (Fin 6156)))))) ?_ ?_ hX hY hXY hX1
    · rw [hcard, Nat.factorization_def _ Nat.prime_three]
      decide +kernel
    · rw [← Subgroup.orderOf_coe]
      exact hcord

end Perm

section Aut

open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore

theorem j3_aut_to_perm
    {G : Type} [Group G] (ψ : G ≃* j3P) {x y : G} {τ : MulAut G} (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1)
    (hx : τ * MulAut.conj x = MulAut.conj x * τ) (hy : τ * MulAut.conj y = MulAut.conj y * τ) :
    ∃ r ∈ j3R, r * r = 1 ∧ r ≠ 1 ∧
      r * (ψ x : Equiv.Perm (Fin 6156)) = (ψ x : Equiv.Perm (Fin 6156)) * r ∧
      r * (ψ y : Equiv.Perm (Fin 6156)) = (ψ y : Equiv.Perm (Fin 6156)) * r := by
  obtain ⟨e, he, -⟩ := ctuc_j3_full_automorphism_permutation_model
  let Φ : MulAut G ≃* MulAut j3P := MulAut.congr ψ
  have hΦconj : ∀ z : G, Φ (MulAut.conj z) = MulAut.conj (ψ z) := by
    intro z
    ext q
    simp [Φ, MulAut.congr_apply, MulAut.conj_apply]
  have hle : j3P ≤ j3R := le_sup_left
  have hinc : ∀ p : j3P, e ⟨(p : Equiv.Perm (Fin 6156)), hle p.2⟩ = MulAut.conj p := by
    intro p
    ext q
    rw [he]
    simp [MulAut.conj_apply]
  set r₀ : j3R := e.symm (Φ τ) with hr₀
  have her₀ : e r₀ = Φ τ := e.apply_symm_apply _
  have hr2 : r₀ * r₀ = 1 := by
    apply e.injective
    rw [map_mul, her₀, map_one, ← map_mul, hτ2, map_one]
  have hr1 : r₀ ≠ 1 := by
    intro h
    apply hτ1
    apply Φ.injective
    rw [← her₀, h, map_one, map_one]
  have hcommute : ∀ z : G, τ * MulAut.conj z = MulAut.conj z * τ →
      r₀ * ⟨(ψ z : Equiv.Perm (Fin 6156)), hle (ψ z).2⟩ =
        ⟨(ψ z : Equiv.Perm (Fin 6156)), hle (ψ z).2⟩ * r₀ := by
    intro z hz
    apply e.injective
    rw [map_mul, map_mul, her₀, hinc, ← hΦconj, ← map_mul, ← map_mul, hz]
  refine ⟨(r₀ : Equiv.Perm (Fin 6156)), r₀.2, ?_, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val hr2
  · intro h
    exact hr1 (Subtype.ext h)
  · exact congrArg Subtype.val (hcommute x hx)
  · exact congrArg Subtype.val (hcommute y hy)

theorem j3SylowDichotomy_of_cert :
    J3SylowDichotomy := by
  obtain ⟨hfin, -, -⟩ := CFSG.Sporadic.J3.fam_j3_simplicity
  haveI := hfin
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow 3 NativeSporadic.J3))
  refine ⟨P₀, fun x y _ _ hx3 hy3 hxy hx1 hyx => Or.inr fun τ hτ2 hτ1 ⟨hτx, hτy⟩ => ?_⟩
  obtain ⟨r, hrR, hr2, hr1, hrx, hry⟩ :=
    @j3_aut_to_perm NativeSporadic.J3 Units.instGroup j3PermEquiv x y τ hτ2 hτ1 hτx hτy
  have hψ : ∀ z : NativeSporadic.J3, ((j3PermEquiv z : j3P) : Equiv.Perm (Fin 6156)) = 1 → z = 1 :=
    fun z hz => j3PermEquiv.injective (Subtype.ext (by simpa using hz))
  have hcube : ∀ z : NativeSporadic.J3, z ^ 3 = 1 →
      ((j3PermEquiv z : j3P) : Equiv.Perm (Fin 6156)) ^ 3 = 1 := fun z hz => by
    simpa using congrArg (fun w => ((j3PermEquiv w : j3P) : Equiv.Perm (Fin 6156))) hz
  have hcomm : ((j3PermEquiv x : j3P) : Equiv.Perm (Fin 6156)) *
      ((j3PermEquiv y : j3P) : Equiv.Perm (Fin 6156)) =
      ((j3PermEquiv y : j3P) : Equiv.Perm (Fin 6156)) *
        ((j3PermEquiv x : j3P) : Equiv.Perm (Fin 6156)) := by
    simpa using congrArg (fun w => ((j3PermEquiv w : j3P) : Equiv.Perm (Fin 6156))) hxy
  have hmem := j3_perm_no_involution hrR hr2 hr1 (j3PermEquiv x).2 (j3PermEquiv y).2
    (hcube x hx3) (hcube y hy3) hcomm (fun h => hx1 (hψ x h)) hrx hry
  apply hyx
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  refine mem_zpowers_iff.mpr ⟨k, ?_⟩
  apply j3PermEquiv.injective
  exact Subtype.ext (by simpa using hk)

theorem item214BarJ3Simple_of_cert :
    Item214BarJ3Simple :=
  item214BarJ3Simple_of_dichotomy j3SylowDichotomy_of_cert

end Aut

end CFSG.RankThree.PartTwo.Sec21.Hering214

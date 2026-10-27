module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338MC
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338One
import CFSG.Adapters.StatedSLPerfect
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338MA
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338MB

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.M338

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch3Sec3
open scoped commutatorElement

variable {V : Type} [CommGroup V]

@[expose] def ModType (H : Subgroup (MulAut V)) (U Z : Subgroup V) : Prop :=
  (∃ n : ℕ, BinaryNaturalSL H U Z 2 n) ∨ AlternatingNatural H U Z 5 ∨
    BinaryNaturalSL H U Z 3 1 ∨ DirectSumOfCopies H U Z (FFModel.nat (StatedSL 3 (ZMod 2))) 2

theorem isPerfect_of_surjective {Γ : Type*} [Group Γ] (hΓ : Group.IsPerfect Γ)
    {G : Subgroup (MulAut V)} (π : Γ →* ↥G) (hπ : Function.Surjective π) :
    Group.IsPerfect ↥G := by
  refine ⟨?_⟩
  have h1 : (⊤ : Subgroup Γ).map π = ⊤ := Subgroup.map_top_of_surjective π hπ
  rw [commutator, ← h1, ← Subgroup.map_commutator, ← commutator, hΓ.commutator_eq_top, h1]

theorem isPerfect_of_equiv {Γ : Type*} [Group Γ] (hΓ : Group.IsPerfect Γ)
    {G : Subgroup (MulAut V)} (e : Γ ≃* ↥G) : Group.IsPerfect ↥G :=
  isPerfect_of_surjective hΓ e.toMonoidHom e.surjective

theorem isPerfect_statedSL_two {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    Group.IsPerfect ↥(StatedSL 2 F) :=
  CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card h4

theorem isPerfect_statedSL_three {F : Type} [Field F] :
    Group.IsPerfect ↥(StatedSL 3 F) :=
  CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) F

theorem isPerfect_alt5 : Group.IsPerfect ↥(alternatingGroup (Fin 5)) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥(alternatingGroup (Fin 5))) with
    h | h
  · exfalso
    have hc : ∀ a b : ↥(alternatingGroup (Fin 5)), a * b = b * a := by
      intro a b
      have h1 : ⁅a, b⁆ ∈ commutator ↥(alternatingGroup (Fin 5)) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have := hc ⟨cyc 0 1 2, cyc_mem 0 1 2 (by decide) (by decide)⟩
      ⟨cyc 2 3 4, cyc_mem 2 3 4 (by decide) (by decide)⟩
    revert this
    decide +kernel
  · exact h

variable {G K : Subgroup (MulAut V)} {W C : Subgroup V}

theorem eq_of_isPerfect (hKG : K ≤ G) (hmax : ∀ N ≤ G, Group.IsPerfect ↥N → N ≤ K)
    (hG : Group.IsPerfect ↥G) : K = G :=
  le_antisymm hKG (hmax G le_rfl hG)

theorem not_isSolvable_of_isQuasisimple (hq : CFSG.IsQuasisimple ↥K) : ¬ Group.IsSolvable ↥K := by
  intro hs
  have : Group.IsPerfect ↥K := hq.1
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact Group.IsPerfect.not_isSolvable ↥K hs

theorem commutator_self_of_isPerfect {Q : Subgroup (MulAut V)} (h : Group.IsPerfect ↥Q) :
    ⁅Q, Q⁆ = Q := by
  have h1 : (⊤ : Subgroup ↥Q).map Q.subtype = Q := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  conv_rhs => rw [← h1, ← h.commutator_eq_top]
  rw [commutator, Subgroup.map_commutator, h1]

@[expose] def PieceOut (K : Subgroup (MulAut V)) (W C : Subgroup V) : Prop :=
  (∀ w ∈ W, (∀ k ∈ K, k w * w⁻¹ ∈ C) → w ∈ C) ∧ commV K ⊔ C ≤ W ∧ ModType K (commV K ⊔ C) C

variable (hKG : K ≤ G) (hmax : ∀ N ≤ G, Group.IsPerfect ↥N → N ≤ K)
  (hq : CFSG.IsQuasisimple ↥K)

include hKG hmax hq in
theorem out_sl2 (hW : W = commV G ⊔ C) {n : ℕ} (h : BinaryNaturalSL G W C 2 n) :
    PieceOut K W C := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hF2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hF4 : 4 ≤ Nat.card F := by
    by_contra h4
    have hF2' : Nat.card F = 2 := by
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n <;> simp_all
      · have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        omega
    apply not_isSolvable_of_isQuasisimple hq
    have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :=
      isSolvable_sl_two_zmodTwo
    have : Group.IsSolvable ↥(StatedSL 2 F) :=
      Group.isSolvable_of_surjective (f := (statedSLEquivZModTwo (n := 2) hF2').symm.toMonoidHom)
        (statedSLEquivZModTwo (n := 2) hF2').symm.surjective
    have : Group.IsSolvable (FFModel.nat (StatedSL 2 F)).Gam := this
    have : Group.IsSolvable ↥G := Group.isSolvable_of_surjective (f := π) hπ.1
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKG)
  have hKeq : K = G :=
    eq_of_isPerfect hKG hmax (isPerfect_of_surjective (isPerfect_statedSL_two hF4) π hπ.1)
  subst hKeq
  refine ⟨fun w hw hfix => mem_of_forall_mul_inv_mem hπ (nat_fix (by norm_num)) hw hfix,
    hW ▸ le_rfl, Or.inl ⟨n, ?_⟩⟩
  rw [← hW]
  exact ⟨F, inferInstance, inferInstance, hF, π, hπ⟩

include hKG hmax hq in
theorem out_s5 (hW : W = commV G ⊔ C) (h : SymmetricNatural G W C 5) : PieceOut K W C := by
  obtain ⟨π, hπ⟩ := h
  set π₀ : Equiv.Perm (Fin 5) →* ↥G := π with hπ₀
  have hπ₀s : Function.Surjective π₀ := hπ.1
  have hfG : (⊤ : Subgroup (Equiv.Perm (Fin 5))).map (G.subtype.comp π₀) = G := by
    rw [← Subgroup.map_map, Subgroup.map_top_of_surjective π₀ hπ₀s, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hKπ : K = (alternatingGroup (Fin 5)).map (G.subtype.comp π₀) := by
    apply le_antisymm
    · have h1 : commutator (Equiv.Perm (Fin 5)) ≤ alternatingGroup (Fin 5) :=
        Abelianization.commutator_subset_ker Equiv.Perm.sign
      calc K = ⁅K, K⁆ := (commutator_self_of_isPerfect hq.1).symm
        _ ≤ ⁅G, G⁆ := Subgroup.commutator_mono hKG hKG
        _ = (commutator (Equiv.Perm (Fin 5))).map (G.subtype.comp π₀) := by
          rw [commutator, Subgroup.map_commutator, hfG]
        _ ≤ (alternatingGroup (Fin 5)).map (G.subtype.comp π₀) := Subgroup.map_mono h1
    · refine hmax _ ?_ ?_
      · conv_rhs => rw [← hfG]
        exact Subgroup.map_mono le_top
      · exact isPerfect_of_surjective isPerfect_alt5
          ((((G.subtype.comp π₀).comp (alternatingGroup (Fin 5)).subtype).codRestrict _
            fun σ => ⟨σ.1, σ.2, rfl⟩))
          (by rintro ⟨_, σ, hσ, rfl⟩; exact ⟨⟨σ, hσ⟩, rfl⟩)
  have hKmem : ∀ x, x ∈ K ↔ ∃ σ ∈ alternatingGroup (Fin 5), ((π σ : ↥G) : MulAut V) = x := by
    intro x
    rw [hKπ]
    rfl
  obtain ⟨π', hπ'⟩ := realizesVia_alt hπ hKmem
  have hle : commV K ⊔ C ≤ W := by
    rw [hW]
    exact sup_le_sup_right (commV_le_of_le hKG) C
  have heq : commV K ⊔ C = W := le_antisymm hle (le_commV_sup hπ' alt5_gen)
  refine ⟨fun w hw hfix => mem_of_forall_mul_inv_mem hπ' alt5_fix hw hfix, hle,
    Or.inr (Or.inl ?_)⟩
  rw [heq]
  exact ⟨π', hπ'⟩

include hKG hmax in
theorem out_sl3 (hA38 : A38Types ↥K) (hSL3 : A38TypesSLThree) (hW : W = commV G ⊔ C) {m : ℕ}
    (h : BinaryNaturalSL G W C 3 m) : PieceOut K W C := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hKeq : K = G :=
    eq_of_isPerfect hKG hmax (isPerfect_of_surjective isPerfect_statedSL_three π hπ.1)
  subst hKeq
  have e : ↥(StatedSL 3 F) ≃* ↥K := MulEquiv.ofBijective π ⟨injective_of_nat hπ, hπ.1⟩
  have hm : m = 1 := hSL3 ↥K F m hF ⟨e.symm⟩ hA38
  subst hm
  refine ⟨fun w hw hfix => mem_of_forall_mul_inv_mem hπ (nat_fix (by norm_num)) hw hfix,
    hW ▸ le_rfl, Or.inr (Or.inr (Or.inl ?_))⟩
  rw [← hW]
  exact ⟨F, inferInstance, inferInstance, hF, π, hπ⟩

include hKG hmax in
theorem out_sum (hA38 : A38Types ↥K) (hSL3 : A38TypesSLThree) (hW : W = commV G ⊔ C) {m : ℕ}
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ m)
    (h : DirectSumOfCopies G W C (FFModel.nat (StatedSL 3 F)) 2) : PieceOut K W C := by
  obtain ⟨I, π, hCI, hind, hsup, hreal⟩ := h
  have hKeq : K = G :=
    eq_of_isPerfect hKG hmax (isPerfect_of_surjective isPerfect_statedSL_three π (hreal 0).1)
  subst hKeq
  have e : ↥(StatedSL 3 F) ≃* ↥K := MulEquiv.ofBijective π ⟨injective_of_nat (hreal 0), (hreal 0).1⟩
  have hm : m = 1 := hSL3 ↥K F m hF ⟨e.symm⟩ hA38
  subst hm
  rw [pow_one] at hF
  set e₂ : ZMod 2 ≃+* F := (ringEquivZModTwo hF).symm
  have hs : (⨆ i, I i) = I 0 ⊔ I 1 := by
    refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup I 0) (le_iSup I 1))
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hW' : W = I 0 ⊔ I 1 := by
    rw [← hsup, hs]
    exact sup_eq_right.mpr (le_sup_of_le_left (hCI 0))
  have hII : I 0 ⊓ I 1 = C := by
    have h0 := hind 0
    have hs1 : (⨆ (j : Fin 2) (_ : j ≠ 0), I j) = I 1 := by
      refine le_antisymm (iSup₂_le fun j hj => ?_) (le_iSup₂_of_le (1 : Fin 2) (by decide) le_rfl)
      fin_cases j
      · exact absurd rfl hj
      · exact le_rfl
    rwa [hs1, sup_eq_right.mpr (hCI 1)] at h0
  refine ⟨fun w hw hfix => ?_, hW ▸ le_rfl, Or.inr (Or.inr (Or.inr ?_))⟩
  · rw [hW'] at hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    have hinv₀ := (hreal 0).2.2.2.1
    have hinv₁ := (hreal 1).2.2.2.1
    have key : ∀ k ∈ K, k a * a⁻¹ ∈ C ∧ k b * b⁻¹ ∈ C := by
      intro k hk
      have h1 := hfix k hk
      have hka : k a * a⁻¹ ∈ I 0 := (I 0).mul_mem (hinv₀ ⟨k, hk⟩ a ha) ((I 0).inv_mem ha)
      have hkb : k b * b⁻¹ ∈ I 1 := (I 1).mul_mem (hinv₁ ⟨k, hk⟩ b hb) ((I 1).inv_mem hb)
      have e1 : k (a * b) * (a * b)⁻¹ = (k a * a⁻¹) * (k b * b⁻¹) := by
        rw [map_mul, mul_inv, mul_mul_mul_comm]
      rw [e1] at h1
      have hka' : k a * a⁻¹ ∈ I 1 := by
        have : k a * a⁻¹ = ((k a * a⁻¹) * (k b * b⁻¹)) * (k b * b⁻¹)⁻¹ := by group
        rw [this]
        exact (I 1).mul_mem (hCI 1 h1) ((I 1).inv_mem hkb)
      have hkb' : k b * b⁻¹ ∈ I 0 := by
        have : k b * b⁻¹ = (k a * a⁻¹)⁻¹ * ((k a * a⁻¹) * (k b * b⁻¹)) := by group
        rw [this]
        exact (I 0).mul_mem ((I 0).inv_mem hka) (hCI 0 h1)
      exact ⟨hII ▸ ⟨hka, hka'⟩, hII ▸ ⟨hkb', hkb⟩⟩
    have ha' := mem_of_forall_mul_inv_mem (hreal 0) (nat_fix (by norm_num)) ha
      fun k hk => (key k hk).1
    have hb' := mem_of_forall_mul_inv_mem (hreal 1) (nat_fix (by norm_num)) hb
      fun k hk => (key k hk).2
    exact C.mul_mem ha' hb'
  · rw [← hW]
    exact ⟨I, π.comp (mapSL e₂), hCI, hind, hsup, fun i => realizesVia_map e₂ (hreal i)⟩

theorem card_of_nat_three [Finite V] {H : Subgroup (MulAut V)} {U Z : Subgroup V} {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2) {π : (FFModel.nat (StatedSL 3 F)).Gam →* ↥H}
    (h : (FFModel.nat (StatedSL 3 F)).RealizesVia H U Z π) :
    Nat.card ↥U = 8 * Nat.card ↥Z := by
  obtain ⟨-, hZU, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hker : β.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv] at h1
  rw [h1]
  congr 1
  rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv]
  have h2 : ((FFModel.nat (StatedSL 3 F)).ker.subgroupOf (FFModel.nat (StatedSL 3 F)).sec) = ⊥ := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · intro hx
      exact Subtype.ext hx
    · intro hx
      rw [hx]
      exact Subgroup.one_mem _
  rw [h2, Nat.card_congr (QuotientGroup.quotientBot).toEquiv]
  show Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 3 → F))) = 8
  rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, hF]
  rfl

theorem mem_zpowers_of_sq {w x : V} (hw : w ^ 2 = 1) (hx : x ∈ Subgroup.zpowers w) :
    x = 1 ∨ x = w := by
  rw [Subgroup.zpowers_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact Or.inr hx
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl (by rw [← sq]; exact hw)
  | inv x _ hx =>
    rcases hx with rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hw))

include hKG hmax in
theorem out_four [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) (hWinv : ∀ g ∈ G, ∀ w ∈ W, g w ∈ W)
    (hcomm : commV G ≤ modComm G W ⊔ C) (hCW : C ≤ W)
    (he : Nonempty (↥G ≃* ↥(StatedSL 3 (ZMod 2)))) (hcW : commV G ≤ W)
    (hcard : Nat.card ↥W = 2 ^ 4 * Nat.card ↥C)
    (hind : ¬ ∃ A B : Subgroup V, C < A ∧ C < B ∧ XMod.IsInv ↥G A ∧ XMod.IsInv ↥G B ∧
      A ⊔ B = W ∧ A ⊓ B = C)
    (hnat : BinaryNaturalSL G (modComm G W ⊔ C) C 3 1) : PieceOut K W C := by
  obtain ⟨e⟩ := he
  have hKeq : K = G := eq_of_isPerfect hKG hmax (isPerfect_of_equiv isPerfect_statedSL_three e.symm)
  subst hKeq
  set U' := modComm K W ⊔ C with hU'
  have hmc : modComm K W ≤ commV K := by
    rw [modComm, XMod.commOf, Subgroup.closure_le]
    rintro _ ⟨a, l, -, rfl⟩
    exact gen_mem_commV a.2 l
  have hmW : modComm K W ≤ W := by
    rw [modComm, XMod.commOf, Subgroup.closure_le]
    rintro _ ⟨a, l, hl, rfl⟩
    exact W.mul_mem (hWinv a a.2 l hl) (W.inv_mem hl)
  have heq : commV K ⊔ C = U' := le_antisymm (sup_le hcomm le_sup_right) (sup_le_sup_right hmc C)
  have hU'W : U' ≤ W := sup_le hmW hCW
  refine ⟨fun w hw hfix => ?_, sup_le hcW hCW, Or.inr (Or.inr (Or.inl (heq ▸ hnat)))⟩
  obtain ⟨F, _, _, hF, π, hπ⟩ := hnat
  rw [pow_one] at hF
  by_cases hwU : w ∈ U'
  · exact mem_of_forall_mul_inv_mem hπ (nat_fix (by norm_num)) hwU hfix
  exfalso
  have hcU := card_of_nat_three hF hπ
  obtain ⟨-, -, -, hUinv, hCinv, -⟩ := hπ
  set B : Subgroup V := Subgroup.zpowers w ⊔ C with hB
  have hwB : w ∈ B := Subgroup.mem_sup_left (Subgroup.mem_zpowers w)
  have hwC : w ∉ C := fun h => hwU (Subgroup.mem_sup_right h)
  have hBW : B ≤ W := sup_le ((Subgroup.zpowers_le).mpr hw) hCW
  have hinf : U' ⊓ B = C := by
    refine le_antisymm (fun x ⟨hxU, hxB⟩ => ?_) (le_inf le_sup_right le_sup_right)
    obtain ⟨y, hy, c, hc, rfl⟩ := Subgroup.mem_sup.mp hxB
    rcases mem_zpowers_of_sq (hV2 w) hy with rfl | rfl
    · rw [one_mul]
      exact hc
    · exfalso
      apply hwU
      have : y = y * c * c⁻¹ := by group
      rw [this]
      exact U'.mul_mem hxU (U'.inv_mem (Subgroup.mem_sup_right hc))
  have hsup : U' ⊔ B = W := by
    have hlt : U' < U' ⊔ B :=
      lt_of_le_of_ne le_sup_left fun h => hwU (h ▸ Subgroup.mem_sup_right hwB)
    have hle : U' ⊔ B ≤ W := sup_le hU'W hBW
    have hdvd : Nat.card ↥U' ∣ Nat.card ↥(U' ⊔ B) := Subgroup.card_dvd_of_le le_sup_left
    have hcl : Nat.card ↥(U' ⊔ B) ≤ Nat.card ↥W := Subgroup.card_le_of_le hle
    have hgt : Nat.card ↥U' < Nat.card ↥(U' ⊔ B) :=
      lt_of_le_of_ne (Subgroup.card_le_of_le le_sup_left)
        fun h => hlt.ne (Subgroup.eq_of_le_of_card_ge le_sup_left h.ge)
    obtain ⟨q, hq⟩ := hdvd
    have hC0 : 0 < Nat.card ↥C := Nat.card_pos
    have hq2 : q = 2 := by
      rw [hq] at hcl hgt
      rw [hcard, hcU] at hcl
      rw [hcU] at hgt
      have h1 : q ≤ 2 := by nlinarith
      have h2 : 1 < q := by nlinarith
      omega
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hq, hq2, hcU, hcard]
    omega
  apply hind
  refine ⟨U', B, lt_of_le_of_ne le_sup_right fun h => ?_, lt_of_le_of_ne le_sup_right
    fun h => hwC (h ▸ hwB), fun a l hl => hUinv a l hl, fun a l hl => ?_, hsup, hinf⟩
  · have := hcU
    rw [← h] at this
    have hC0 : 0 < Nat.card ↥C := Nat.card_pos
    omega
  · obtain ⟨y, hy, c, hc, rfl⟩ := Subgroup.mem_sup.mp hl
    rw [smul_mul']
    refine B.mul_mem ?_ (Subgroup.mem_sup_right (hCinv a c hc))
    rcases mem_zpowers_of_sq (hV2 w) hy with hy1 | hy1
    · rw [hy1, smul_one]
      exact B.one_mem
    · have hfa := hfix a a.2
      have e1 : a • w = ((a : MulAut V) w * w⁻¹) * w := by
        show (a : MulAut V) w = _
        group
      rw [hy1, e1]
      exact B.mul_mem (Subgroup.mem_sup_right hfa) hwB

theorem commV_le_of_piece (h : B56Piece G W C) : commV G ≤ W := by
  rcases h with ⟨hW, -⟩ | ⟨hW, -⟩ | ⟨-, hcW, -⟩
  · exact hW ▸ le_sup_left
  · exact hW ▸ le_sup_left
  · exact hcW

include hKG hmax hq in
theorem piece_out [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) (hA38 : A38Types ↥K)
    (hSL3 : A38TypesSLThree) (hWinv : ∀ g ∈ G, ∀ w ∈ W, g w ∈ W)
    (hcomm : commV G ≤ modComm G W ⊔ C) (hCW : C ≤ W) (h : B56Piece G W C) :
    PieceOut K W C := by
  rcases h with ⟨hW, ⟨n, h2⟩ | h5 | ⟨m, h3⟩⟩ | ⟨hW, m, F, _, _, hF, hsum⟩ |
    ⟨he, hcW, hcard, hind, hnat⟩
  · exact out_sl2 hKG hmax hq hW h2
  · exact out_s5 hKG hmax hq hW h5
  · exact out_sl3 hKG hmax hA38 hSL3 hW h3
  · exact out_sum hKG hmax hA38 hSL3 hW hF hsum
  · exact out_four hKG hmax hV2 hWinv hcomm hCW he hcW hcard hind hnat

end CFSG.Quasithin.H13.M338

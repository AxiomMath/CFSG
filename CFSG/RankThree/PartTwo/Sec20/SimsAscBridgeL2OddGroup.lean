module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.GH74.GLS.IVK.L2.KI2Aux
import CFSG.GH74.GLS.IVK.L2.Lemma13
import CFSG.GH74.GLS.IVK.Proofs2.Lemma18
import CFSG.GH74.GLS.IVK.Proofs2.Pgl2Three
import CFSG.Quasithin.Background.DicksonPerfectBasic
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L3Group
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.RankThree.PartTwo.Sec20.L2OddGroup

open Matrix CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped MatrixGroups

theorem eq_bot_of_isPerfect_of_isSolvable {G : Type*} [Group G] {L : Subgroup G}
    (hL : Group.IsPerfect L) (hsolv : Group.IsSolvable L) : L = ⊥ := by
  by_contra h
  have : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr h
  exact Group.IsPerfect.not_isSolvable L hsolv

theorem isSolvable_of_isDihedralOrder {Y : Type} [Group Y] {m : ℕ} (h : IsDihedralOrder Y m) :
    Group.IsSolvable Y := by
  obtain ⟨k, -, -, ⟨φ⟩⟩ := h
  have := CFSG.Quasithin.Dickson.isSolvable_dihedral k
  exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective

theorem isSolvable_pgl2_of_card_eq_three {F₀ : Type} [Field F₀] [Finite F₀]
    (h3 : Nat.card F₀ = 3) : Group.IsSolvable (PGL2 F₀) := by
  obtain ⟨φ⟩ := CFSG.GH74.GLS.IVK.Proofs2.exists_pgl2_equiv_perm h3
  have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
  exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective

theorem odd_card_of_ringChar_eq {F₀ : Type*} [Field F₀] [Finite F₀] {p : ℕ} (hp : Odd p)
    (h : ringChar F₀ = p) : Odd (Nat.card F₀) := by
  have := Fintype.ofFinite F₀
  have : CharP F₀ p := ringChar.of_eq h
  obtain ⟨m, -, hm⟩ := FiniteField.card F₀ p
  rw [Nat.card_eq_fintype_card, hm]
  exact hp.pow

theorem index_range_toPGL {F₀ : Type*} [Field F₀] [Finite F₀] (hodd : Odd (Nat.card F₀)) :
    (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).range.index = 2 := by
  have h := (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).range.card_mul_index
  rw [← Nat.card_congr (MonoidHom.ofInjective
      (ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := F₀))).toEquiv,
    psl2_card_formula F₀ (isOddPrimePower_of_odd_card hodd), pgl2_card_formula] at h
  have h1 : 1 < Nat.card F₀ := Finite.one_lt_card
  have heven : Even (Nat.card F₀ ^ 2 - 1) := Nat.Odd.sub_odd hodd.pow odd_one
  obtain ⟨m, hm⟩ := heven
  have hm0 : 0 < Nat.card F₀ * m := by
    have : 1 < Nat.card F₀ ^ 2 := Nat.one_lt_pow two_ne_zero h1
    exact Nat.mul_pos (by omega) (by omega)
  rw [hm, show Nat.card F₀ * (m + m) = 2 * (Nat.card F₀ * m) by ring,
    Nat.mul_div_cancel_left _ two_pos] at h
  exact Nat.eq_of_mul_eq_mul_left hm0 (h.trans (mul_comm _ _))

theorem commutator_le_range_toPGL {F₀ : Type*} [Field F₀] [Finite F₀]
    (hodd : Odd (Nat.card F₀)) :
    commutator (PGL2 F₀) ≤ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).range := by
  have hidx := index_range_toPGL hodd
  set S := (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).range
  have : S.Normal := Subgroup.normal_of_index_eq_two hidx
  have : IsCyclic (PGL2 F₀ ⧸ S) := isCyclic_of_prime_card (p := 2) hidx
  let : CommGroup (PGL2 F₀ ⧸ S) := IsCyclic.commGroup
  simpa only [QuotientGroup.ker_mk'] using
    Abelianization.commutator_subset_ker (QuotientGroup.mk' S)

theorem le_of_isPerfect {G : Type*} [Group G] {N R : Subgroup G} (hN : Group.IsPerfect N)
    (hR : commutator G ≤ R) : N ≤ R :=
  calc N = ⁅N, N⁆ := Subgroup.commutator_eq_self.symm
    _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top
    _ ≤ R := hR

theorem not_isPerfect_pgl2 {F₀ : Type*} [Field F₀] [Finite F₀] (hodd : Odd (Nat.card F₀)) :
    ¬ Group.IsPerfect (PGL2 F₀) := by
  intro h
  have h1 := commutator_le_range_toPGL hodd
  rw [h.commutator_eq_top, top_le_iff] at h1
  have h2 := index_range_toPGL hodd
  rw [h1, Subgroup.index_top] at h2
  omega

theorem two_mul_card_of_normal_isPerfect_pgl2 {F₀ : Type} [Field F₀] [Finite F₀]
    (hodd : Odd (Nat.card F₀)) {N : Subgroup (PGL2 F₀)} (hN : N.Normal)
    (hNp : Group.IsPerfect N) (hN1 : N ≠ ⊥) :
    2 * Nat.card N = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) := by
  set S := (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).range
  have hNS : N ≤ S := le_of_isPerfect hNp (commutator_le_range_toPGL hodd)
  have h1 : 1 < Nat.card F₀ := Finite.one_lt_card
  by_cases h3 : Nat.card F₀ = 3
  · exfalso
    have := isSolvable_pgl2_of_card_eq_three h3
    exact hN1 (eq_bot_of_isPerfect_of_isSolvable hNp inferInstance)
  · have h4 : 4 ≤ Nat.card F₀ := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have : IsSimpleGroup (PSL2 F₀) := ProjectiveSpecialLinearGroup.rank_two_simple h4
    have : IsSimpleGroup S := (MonoidHom.ofInjective
      (ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := F₀))).symm.isSimpleGroup
    have : (N.subgroupOf S).Normal := hN.subgroupOf S
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf S) with h | h
    · exact absurd ((Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hNS) hN1
    · have hNeq : N = S := le_antisymm hNS (Subgroup.subgroupOf_eq_top.mp h)
      have hc := S.card_mul_index
      rw [index_range_toPGL hodd, pgl2_card_formula, ← hNeq] at hc
      rw [← hc, mul_comm]

theorem nonempty_fixedSubgroup_equiv_of_conj {G : Type*} [Group G] {y f a : MulAut G}
    (h : a * y * a⁻¹ = f) :
    Nonempty (CFSG.GH74.GLS.fixedSubgroup G y ≃* CFSG.GH74.GLS.fixedSubgroup G f) := by
  have hmap : (CFSG.GH74.GLS.fixedSubgroup G y).map (a : G ≃* G).toMonoidHom =
      CFSG.GH74.GLS.fixedSubgroup G f := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : y k = k := hk
      show f (a k) = a k
      rw [← h]
      simp [hk']
    · intro hx
      have hx' : f x = x := hx
      refine ⟨a⁻¹ x, ?_, by simp⟩
      show y (a⁻¹ x) = a⁻¹ x
      have h2 : y = a⁻¹ * f * a := by rw [← h]; group
      rw [h2]
      show a⁻¹ (f (a (a⁻¹ x))) = a⁻¹ x
      simp [hx']
  exact ⟨((a : G ≃* G).subgroupMap _).trans (MulEquiv.subgroupCongr hmap)⟩

theorem fixedSubgroup_conj {G : Type*} [Group G] (u : G) :
    CFSG.GH74.GLS.fixedSubgroup G (MulAut.conj u) = Subgroup.centralizer {u} := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  show u * x * u⁻¹ = x ↔ _
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_comm

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem exists_eps {q : ℕ} (hq : Odd q) : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (q : ℤ) ≡ ε [ZMOD 4] := by
  obtain ⟨k, rfl⟩ := hq
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; push_cast; omega⟩
  · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; push_cast; omega⟩

theorem eq_bot_of_isPerfect_of_le_fixedSubgroup (hF : L2Field F) (e : K ≃* L2 F)
    {v : MulAut K} (hv : v ∈ innDiagSub e) (hv2 : orderOf v = 2)
    {L : Subgroup K} (hL : Group.IsPerfect L) (hLv : L ≤ CFSG.GH74.GLS.fixedSubgroup K v) :
    L = ⊥ := by
  obtain ⟨ε, hε1, hε⟩ := exists_eps hF.1
  have hq3 := hF.2
  have hC : Group.IsSolvable (CFSG.GH74.GLS.fixedSubgroup K v) := by
    by_cases hvi : v ∈ innAut K
    · obtain ⟨u, rfl⟩ := hvi
      have hu : orderOf u = 2 := by
        rw [← orderOf_injective _ (conj_injective_of_L2 e) u]
        exact hv2
      obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F - ε :=
        ⟨(Nat.card F - ε).toNat, Int.toNat_of_nonneg (by rcases hε1 with rfl | rfl <;> omega)⟩
      rw [fixedSubgroup_conj]
      exact isSolvable_of_isDihedralOrder (ivk_1_3a F hF K e ε hε1 hε d hd u hu).2.1
    · obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F + ε :=
        ⟨(Nat.card F + ε).toNat, Int.toNat_of_nonneg (by rcases hε1 with rfl | rfl <;> omega)⟩
      exact isSolvable_of_isDihedralOrder (ivk_1_3b F hF K e ε hε1 hε d hd v hv hvi hv2).2.1
  exact eq_bot_of_isPerfect_of_isSolvable hL
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLv)
      (Subgroup.inclusion_injective hLv))

theorem isCyclic_of_fixes_isPerfect (hF : L2Field F) (e : K ≃* L2 F)
    {R : Subgroup (MulAut K)} (hR : IsPGroup 2 R) (_hRinn : R ⊓ innAut K = ⊥)
    {L : Subgroup K} (hL : Group.IsPerfect L) (hL1 : L ≠ ⊥)
    (hfix : ∀ r ∈ R, L ≤ CFSG.GH74.GLS.fixedSubgroup K r) :
    R ⊓ innDiagSub e = ⊥ ∧ IsCyclic R ∧ Nat.card R ∣ Nat.card (F ≃+* F) := by
  have hD : R ⊓ innDiagSub e = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxR, hxD⟩
    by_contra hx1
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hR ⟨x, hxR⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hx1 hk
    have h2 : 2 ∣ orderOf x := by
      rw [hk]
      exact dvd_pow_self 2 hk0
    have hx0 : orderOf x ≠ 0 := by
      rw [hk]
      exact pow_ne_zero k two_ne_zero
    exact hL1 (eq_bot_of_isPerfect_of_le_fixedSubgroup hF e ((innDiagSub e).pow_mem hxD _)
      (orderOf_pow_orderOf_div hx0 h2) hL (hfix _ (R.pow_mem hxR _)))
  let φ : R →* (F ≃+* F) := (fieldProj e).comp R.subtype
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : MulAut K) ∈ R ⊓ innDiagSub e :=
      ⟨x.2, (mem_innDiagSub_iff e x).2 (MonoidHom.mem_ker.mp hx)⟩
    rw [hD, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.2 (Subtype.ext hx')
  have := ringAut_isCyclic F
  refine ⟨hD, isCyclic_of_injective φ hφ, ?_⟩
  rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
  exact Subgroup.card_subgroup_dvd_card φ.range

omit [Finite K] in
theorem isPGL2_fixedSubgroup_of_not_mem_innDiagSub (e : K ≃* L2 F) {u : MulAut K}
    (hu : orderOf u = 2) (hud : u ∉ innDiagSub e) :
    IsPGL2 (CFSG.GH74.GLS.fixedSubgroup K u) (fun q₀ => q₀ ^ 2 = Nat.card F) := by
  obtain ⟨a, -, ha⟩ := exists_conj_fieldAut e u hu hud
  set σ := fieldProj e u with hσ
  have hσ1 : σ ≠ 1 := fun h => hud ((mem_innDiagSub_iff e u).2 h)
  have hσ2 : σ ^ 2 = 1 := by
    rw [hσ, ← map_pow, ← hu, pow_orderOf_eq_one, map_one]
  have hσo : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
  obtain ⟨χ⟩ := nonempty_fixedSubgroup_equiv_of_conj (a := a⁻¹) (y := u)
    (f := fieldAutHom e σ) (by rw [inv_inv]; exact ha)
  refine ⟨fixedField σ, inferInstance, inferInstance, ?_,
    ⟨χ.trans (fixedSubgroupEquivPGL2 e σ (hσo ▸ even_two))⟩⟩
  rw [← hσo]
  exact fixedField_card_pow σ

omit [Finite K] in
theorem two_mul_card_of_isPerfect_of_normal_fixedSubgroup (hF : L2Field F) (e : K ≃* L2 F)
    {p : ℕ} (_hp : p.Prime) (hFp : Nat.card F = p ^ 2)
    {u : MulAut K} (hu : orderOf u = 2) (hud : u ∉ innDiagSub e)
    {L : Subgroup K} (hL : Group.IsPerfect L) (hL1 : L ≠ ⊥)
    (hLu : L ≤ CFSG.GH74.GLS.fixedSubgroup K u)
    (hLn : ∀ y ∈ CFSG.GH74.GLS.fixedSubgroup K u, ∀ l ∈ L, y * l * y⁻¹ ∈ L) :
    2 * Nat.card L = p * (p ^ 2 - 1) := by
  obtain ⟨F₀, _, _, hF₀2, ⟨ψ⟩⟩ := isPGL2_fixedSubgroup_of_not_mem_innDiagSub e hu hud
  have hF₀ : Nat.card F₀ = p := by
    have h : Nat.card F₀ ^ 2 = p ^ 2 := hF₀2.trans hFp
    exact Nat.pow_left_injective two_ne_zero h
  have hpodd : Odd p := by
    have h := hF.1
    rw [hFp] at h
    exact (Nat.odd_pow_iff two_ne_zero).mp h
  let L₁ : Subgroup (CFSG.GH74.GLS.fixedSubgroup K u) :=
    L.subgroupOf (CFSG.GH74.GLS.fixedSubgroup K u)
  have hL₁n : L₁.Normal := ⟨fun x hx g => hLn g g.2 x hx⟩
  have : Group.IsPerfect L₁ := Group.IsPerfect.ofSurjective
    (f := (Subgroup.subgroupOfEquivOfLe hLu).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hLu).symm.surjective
  have hcard : Nat.card (L₁.map ψ.toMonoidHom) = Nat.card L := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLu).toEquiv
  have hN1 : L₁.map ψ.toMonoidHom ≠ ⊥ := by
    intro h
    apply hL1
    rw [← Subgroup.card_eq_one] at h ⊢
    rw [← hcard, h]
  have h := two_mul_card_of_normal_isPerfect_pgl2 (hF₀ ▸ hpodd)
    (hL₁n.map ψ.toMonoidHom ψ.surjective) (Group.IsPerfect.map ψ.toMonoidHom) hN1
  rw [hcard, hF₀] at h
  exact h

theorem exists_rootSubgroup {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i ≠ j)
    (F₂ : Type*) [Field F₂] [CharP F₂ 2] :
    ∃ E : Subgroup (SpecialLinearGroup ι F₂), Nat.card E = Nat.card F₂ ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x * x = 1 := by
  let τ : Multiplicative F₂ →* SpecialLinearGroup ι F₂ :=
    { toFun := fun t => SpecialLinearGroup.transvection hij (Multiplicative.toAdd t)
      map_one' := SpecialLinearGroup.transvection_coeff_zero hij
      map_mul' := fun s t => SpecialLinearGroup.transvection_add hij _ _ }
  have hτ : Function.Injective τ := by
    intro s t hst
    have h := congrArg (fun g : SpecialLinearGroup ι F₂ => (g : Matrix ι ι F₂) i j) hst
    simp [τ, SpecialLinearGroup.transvection_coe, hij] at h
    exact h
  refine ⟨τ.range, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv]
    exact Nat.card_congr Multiplicative.toAdd
  · rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨s, rfl⟩
    have hs : s * s = 1 := by
      apply Multiplicative.toAdd.injective
      simp [CharTwo.add_self_eq_zero]
    rw [← map_mul, hs, map_one]

omit [Finite K] in
theorem card_le_four_of_injective (hF : L2Field F) (e : K ≃* L2 F) {G : Type*} [Group G]
    (κ : G →* K) (hκ : Function.Injective κ) (E : Subgroup G)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 4 := by
  let κ' : G →* PSL2 F := (toPSL e).toMonoidHom.comp κ
  have hκ' : Function.Injective κ' := (toPSL e).injective.comp hκ
  have h := card_le_four_of_dihedralSylow
    (psl2_odd_hasDihedralSylowTwo_model F (isOddPrimePower_of_L2Field hF)) (E.map κ')
    (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; rw [← map_mul, ← map_mul, hcomm x hx y hy])
    (by rintro _ ⟨x, hx, rfl⟩; rw [← map_mul, hsq x hx, map_one])
  rwa [Subgroup.card_map_of_injective hκ'] at h

theorem isSimpleGroup_of_isPerfect (hF : L2Field F)
    (e : K ≃* L2 F) {L : Subgroup K} (hL : Group.IsPerfect L) (hL1 : L ≠ ⊥) :
    IsSimpleGroup L := by
  have hns : ¬ Group.IsSolvable L := fun h => hL1 (eq_bot_of_isPerfect_of_isSolvable hL h)
  obtain ⟨p, n, hp, hpodd, -, hq⟩ := isOddPrimePower_of_L2Field hF
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hq)
  have hchF : ringChar F = p := ringChar.eq F p
  rcases CFSG.GH74.GLS.IVK.Proofs2.ivk_1_8_i F hF K e L hns with
    ⟨F₀, _, _, hch, -, hL2 | hPGL⟩ | ⟨F₀, _, _, h5, ⟨eL⟩⟩
  · obtain ⟨eL⟩ := hL2
    have hodd : Odd (Nat.card F₀) := odd_card_of_ringChar_eq hpodd (hch.trans hchF)
    have h1 : 1 < Nat.card F₀ := Finite.one_lt_card
    by_cases h3 : Nat.card F₀ = 3
    · exfalso
      apply hns
      have := isSolvable_pgl2_of_card_eq_three h3
      exact Group.isSolvable_of_isSolvable_injective
        (f := (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).comp
          (eL.trans (L2.equivPSL F₀)).toMonoidHom)
        (ProjectiveSpecialLinearGroup.toPGL_injective.comp (eL.trans (L2.equivPSL F₀)).injective)
    · obtain ⟨k, hk⟩ := hodd
      have : IsSimpleGroup (PSL2 F₀) := ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
      exact (eL.trans (L2.equivPSL F₀)).isSimpleGroup
  · obtain ⟨eL⟩ := hPGL
    exfalso
    exact not_isPerfect_pgl2 (odd_card_of_ringChar_eq hpodd (hch.trans hchF))
      (Group.IsPerfect.ofSurjective (f := eL.toMonoidHom) eL.surjective)
  · have h5' : Nat.card F₀ = 5 := h5
    have : IsSimpleGroup (PSL2 F₀) := ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact (eL.trans (L2.equivPSL F₀)).isSimpleGroup

omit [Finite K] in
theorem injective_and_card_le_four (hF : L2Field F) (e : K ≃* L2 F) {L : Subgroup K}
    (hsimple : IsSimpleGroup L) {Q : Type*} [Group Q] (φ : ↥L →* Q)
    (hφ : Function.Surjective φ) {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι}
    (hij : i ≠ j) {F₂ : Type*} [Field F₂] [Finite F₂] [CharP F₂ 2]
    (θ : SpecialLinearGroup ι F₂ ≃* Q) :
    Function.Injective φ ∧ Nat.card F₂ ≤ 4 := by
  obtain ⟨E, hEcard, hcomm, hsq⟩ := exists_rootSubgroup hij F₂
  have : Nontrivial (SpecialLinearGroup ι F₂) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    calc 1 < Nat.card F₂ := Finite.one_lt_card
      _ = Nat.card E := hEcard.symm
      _ ≤ Nat.card (SpecialLinearGroup ι F₂) := Subgroup.card_le_card_group E
  have : Nontrivial Q := θ.injective.nontrivial
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (1 : Q)
      obtain ⟨l, rfl⟩ := hφ x
      exact hx (φ.mem_ker.mp (h ▸ Subgroup.mem_top l))
  refine ⟨hinj, ?_⟩
  let ψ : ↥L ≃* Q := MulEquiv.ofBijective φ ⟨hinj, hφ⟩
  rw [← hEcard]
  exact card_le_four_of_injective hF e (L.subtype.comp (ψ.symm.toMonoidHom.comp θ.toMonoidHom))
    (L.subtype_injective.comp (ψ.symm.injective.comp θ.injective)) E hcomm hsq

theorem isSimpleGroup_and_card_of_surjective (hF : L2Field F)
    (e : K ≃* L2 F) {L : Subgroup K} (hL : Group.IsPerfect L) (hL1 : L ≠ ⊥)
    {Q : Type*} [Group Q] (φ : ↥L →* Q) (hφ : Function.Surjective φ)
    (hQ : (∃ n : ℕ, Even n ∧ 0 < n ∧
        Nonempty (Q ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))) ∨
      (∃ n : ℕ, Odd n ∧ Nonempty (Q ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)))) :
    IsSimpleGroup ↥L ∧ Function.Injective φ ∧ (Nat.card L = 60 ∨ Nat.card L = 168) := by
  have hsimple := isSimpleGroup_of_isPerfect hF e hL hL1
  rcases hQ with ⟨n, hn, hn0, ⟨χ⟩⟩ | ⟨n, hn, ⟨χ⟩⟩
  · obtain ⟨hinj, h4⟩ := injective_and_card_le_four hF e hsimple φ hφ
      (i := (0 : Fin 2)) (j := 1) (by decide)
      ((CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).symm.trans
        ((Sec4.projSLEquivPSL (GaloisField 2 n)).symm.trans χ.symm))
    rw [GaloisField.card 2 n hn0.ne'] at h4
    have hn3 : n < 3 := by
      by_contra h
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hn2 : n = 2 := by
      obtain ⟨k, hk⟩ := hn
      omega
    subst hn2
    refine ⟨hsimple, hinj, Or.inl ?_⟩
    rw [Nat.card_congr (MulEquiv.ofBijective φ ⟨hinj, hφ⟩).toEquiv, Nat.card_congr χ.toEquiv,
      Nat.card_congr (Sec4.projSLEquivPSL (GaloisField 2 2)).toEquiv,
      CFSG.Walter.psl2_even_card two_ne_zero]
    norm_num
  · have hn0 : n ≠ 0 := by
      obtain ⟨k, hk⟩ := hn
      omega
    obtain ⟨hinj, h4⟩ := injective_and_card_le_four hF e hsimple φ hφ
      (i := (0 : Fin 3)) (j := 1) (by decide) ((slThreeEquivProjSL hn).trans χ.symm)
    rw [GaloisField.card 2 n hn0] at h4
    have hn3 : n < 3 := by
      by_contra h
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hn1 : n = 1 := by
      obtain ⟨k, hk⟩ := hn
      omega
    subst hn1
    refine ⟨hsimple, hinj, Or.inr ?_⟩
    have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 1)
    rw [GaloisField.card 2 1 one_ne_zero] at h
    rw [Nat.card_congr (MulEquiv.ofBijective φ ⟨hinj, hφ⟩).toEquiv, Nat.card_congr χ.toEquiv]
    have hg : Nat.gcd 3 (2 ^ 1 - 1) = 1 := by decide
    rw [hg, mul_one] at h
    rw [h]
    norm_num

end CFSG.RankThree.PartTwo.Sec20.L2OddGroup

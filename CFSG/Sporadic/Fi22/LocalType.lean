module

public import CFSG.Sporadic.Fi22.Centralizer
public import CFSG.Fischer.T46Simple

public section

namespace CFSG.Sporadic.Fi22

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.F4.Native CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem t46_not_commute :
    t46xE * t46yE ≠ t46yE * t46xE := by
  intro h
  have h6 : (t46xE * t46yE) ^ 6 = 1 := by
    rw [(Commute.mul_pow h 6), show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, pow_mul',
      ← orderOf_t46xE, pow_orderOf_eq_one, one_pow, ← orderOf_t46yE, pow_orderOf_eq_one,
      one_pow, one_mul]
  have := orderOf_dvd_of_pow_eq_one h6
  rw [orderOf_t46xE_t46yE] at this
  norm_num at this

theorem center_T46 :
    Subgroup.center T46 = ⊥ := by
  have := isSimpleGroup_T46
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T46) with h | h
  · exact h
  · exfalso
    apply t46_not_commute
    have hx : t46xE ∈ Subgroup.center T46 := by rw [h]; trivial
    exact (Subgroup.mem_center_iff.1 hx t46yE).symm

theorem commutator_T46 :
    commutator T46 = ⊤ := by
  have := isSimpleGroup_T46
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator T46) with h | h
  · exfalso
    apply t46_not_commute
    have h2 : (⊤ : Subgroup T46) ≤ Subgroup.centralizer (⊤ : Subgroup T46) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [← commutator_def]; exact h)
    exact (Subgroup.mem_centralizer_iff.1 (h2 (Subgroup.mem_top t46xE)) t46yE
      (Subgroup.mem_top _)).symm
  · exact h

theorem center_Ca :
    Subgroup.center Ca = rho.ker := by
  apply le_antisymm
  · intro z hz
    rw [MonoidHom.mem_ker]
    have h1 : rho z ∈ T46 := rho_mem_T46 z
    have hcent : (⟨rho z, h1⟩ : T46) ∈ Subgroup.center T46 := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨g, hg⟩
      rw [← range_rho] at hg
      obtain ⟨g', rfl⟩ := hg
      apply Subtype.ext
      show rho g' * rho z = rho z * rho g'
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g']
    rw [center_T46, Subgroup.mem_bot] at hcent
    exact congrArg Subtype.val hcent
  · rw [ker_rho, Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, aCa_val]
    exact mem_Ca.1 g.2

theorem center_Ca_eq :
    Subgroup.center Ca = Subgroup.zpowers aCa := by rw [center_Ca, ker_rho]

theorem card_center_Ca :
    Nat.card (Subgroup.center Ca) = 2 := by
  rw [center_Ca, card_ker_rho]

noncomputable def caQuotEquiv :
    (Ca ⧸ Subgroup.center Ca) ≃* T46 :=
  (QuotientGroup.quotientMulEquivOfEq center_Ca).trans
    ((QuotientGroup.quotientKerEquivRange rho).trans (MulEquiv.subgroupCongr range_rho))

theorem caQuotEquiv_mk
    (g : Ca) : (caQuotEquiv (QuotientGroup.mk g) : Equiv.Perm (Fin 693)) =
    rho g := by
  simp only [caQuotEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    MulEquiv.subgroupCongr_apply, QuotientGroup.quotientKerEquivRange,
    MulEquiv.ofBijective_apply, QuotientGroup.rangeKerLift]
  rfl

theorem ptE_conj
    (u v : Fin 693) : ∃ g : Ca, (g : J) * ptE u * (g : J)⁻¹ = ptE v := by
  obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq T46 u v
  have hτ' : (τ : Equiv.Perm (Fin 693)) ∈ rho.range := by rw [range_rho]; exact τ.2
  obtain ⟨g, hg⟩ := hτ'
  refine ⟨g, ?_⟩
  have h1 : rho g u = v := by rw [hg]; exact hτ
  rw [rho_apply] at h1
  have h2 : g • ptE u = ptE v := by rw [← h1, Equiv.apply_symm_apply]
  have := congrArg Subtype.val h2
  rwa [starAction_val] at this

noncomputable def starOf (x : star) : Ca := ⟨x, mem_Ca.2 x.2.2.2⟩

theorem starOf_mul_mem
    (x y : star) : starOf x * starOf y ∈ commutator Ca := by
  obtain ⟨u, rfl⟩ := ptE.surjective x
  obtain ⟨v, rfl⟩ := ptE.surjective y
  obtain ⟨g, hg⟩ := ptE_conj u v
  have hinv : (starOf (ptE u))⁻¹ = starOf (ptE u) := by
    apply Subtype.ext
    show ((ptE u : J))⁻¹ = ptE u
    obtain ⟨hD, -, -⟩ := (ptE u).2
    rw [inv_eq_iff_mul_eq_one, ← sq, ← orderOf_of_mem_D hD, pow_orderOf_eq_one]
  have : starOf (ptE u) * starOf (ptE v) =
      (starOf (ptE u))⁻¹ * g * (starOf (ptE u))⁻¹⁻¹ * g⁻¹ := by
    rw [inv_inv, hinv]
    apply Subtype.ext
    show (ptE u : J) * ptE v = ptE u * g * ptE u * (g : J)⁻¹
    rw [← hg]; group
  rw [this, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem aCa_mem_commutator :
    aCa ∈ commutator Ca := by
  have hmem : ∀ k ∈ aWord2, conjPt k ∈ star :=
    fun k hk => conjPt_mem_star (aWord2_mem k hk)
  let s : ℕ → Ca := fun k => if h : k ∈ aWord2 then starOf ⟨conjPt k, hmem k h⟩ else 1
  have hs : ∀ k ∈ aWord2, (s k : J) = conjPt k := fun k hk => by simp [s, hk, starOf]
  have hP : ((s 889 * s 1897) * (s 2614 * s 929) * (s 3173 * s 762)) ^ 11 = aCa := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_mul, hs 889 (by decide), hs 1897 (by decide), hs 2614 (by decide),
      hs 929 (by decide), hs 3173 (by decide), hs 762 (by decide), aCa_val, ← a_eq_word2]
    simp only [aWord2, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      mul_assoc]
  have hpair : ∀ k ∈ aWord2, ∀ k' ∈ aWord2, s k * s k' ∈ commutator Ca := by
    intro k hk k' hk'
    simp only [s, hk, hk', dite_true]
    exact starOf_mul_mem _ _
  rw [← hP]
  apply Subgroup.pow_mem
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_ <;>
    exact hpair _ (by decide) _ (by decide)

theorem T46_le_commutator :
    T46 ≤ ⁅T46, T46⁆ := by
  intro x hx
  have h := commutator_T46
  rw [commutator_def] at h
  have hx' : (⟨x, hx⟩ : T46) ∈ ⁅(⊤ : Subgroup T46), (⊤ : Subgroup T46)⁆ := by
    rw [h]; trivial
  have := Subgroup.mem_map_of_mem T46.subtype hx'
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  exact this

theorem commutator_Ca :
    commutator Ca = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : rho g ∈ (commutator Ca).map rho := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_rho]
    exact T46_le_commutator (rho_mem_T46 g)
  obtain ⟨h, hh, hgh⟩ := hg
  have hk : h⁻¹ * g ∈ rho.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, inv_mul_cancel]
  rw [ker_rho] at hk
  have hk' : h⁻¹ * g ∈ commutator Ca := (Subgroup.zpowers_le.2 aCa_mem_commutator) hk
  have := (commutator Ca).mul_mem hh hk'
  rwa [mul_inv_cancel_left] at this

end CFSG.Sporadic.Fi22

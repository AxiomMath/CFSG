module

public import CFSG.Sporadic.Fi23.Fischer
public import CFSG.Fischer.LocalProduct
public import CFSG.Sporadic.Fi24.ExtCentralizer

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Blueprint.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem isConj_d_of_orderOf
    {g : J} (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1)
    (h : ∀ w : J, orderOf (g * (w * g * w⁻¹)) ∈ ({1, 2, 3} : Set ℕ)) : IsConj d g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgo : orderOf g = 2 := orderOf_eq_prime hg2 hg1
  obtain ⟨c, hc⟩ := exists_conj_mem_slvl hgo
  have hte : IsConj g (c * g * c⁻¹) := isConj_iff.2 ⟨c, rfl⟩
  have ht2 : (c * g * c⁻¹) ^ 2 = 1 := by rw [conj_pow, hg2, mul_one, mul_inv_cancel]
  have ht1 : c * g * c⁻¹ ≠ 1 := by
    intro h1
    apply hg1
    calc g = c⁻¹ * (c * g * c⁻¹) * c := by group
      _ = 1 := by rw [h1]; group
  rcases invClass_of_mem hc ht2 ht1 with hD | ⟨w, hw⟩
  · exact hD.trans hte.symm
  · exfalso
    apply hw
    have e : c * g * c⁻¹ * (w * (c * g * c⁻¹) * w⁻¹) =
        c * (g * ((c⁻¹ * w * c) * g * (c⁻¹ * w * c)⁻¹)) * c⁻¹ := by group
    rw [e, orderOf_conj]
    exact h _

end CFSG.Sporadic.Fi23

namespace CFSG.Sporadic.Fi24

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem tR_mem_D24 :
    tR ∈ D24 := IsConj.refl tR

theorem not_mem_JR_of_mem_D24
    {x : R} (hx : x ∈ D24) : x ∉ JR := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hx
  intro h
  apply tR_not_mem_JR
  have h' := normal_JR.conj_mem _ h g⁻¹
  rwa [show g⁻¹ * (g * tR * g⁻¹) * g⁻¹⁻¹ = tR by group] at h'

theorem MR_le_JR : MR ≤ JR := by
  rintro _ ⟨g, -, rfl⟩
  exact jR_mem_JR g

theorem tR_not_mem_MR :
    tR ∉ MR := fun h => tR_not_mem_JR (MR_le_JR h)

theorem commute_tR_of_mem_MR
    {m : R} (hm : m ∈ MR) : m * tR = tR * m := by
  obtain ⟨g, hg, rfl⟩ := hm
  exact (commute_tR_iff g).2 hg

theorem mem_MR_or_of_commute
    {c : R} (hc : c ∈ Subgroup.centralizer ({tR} : Set R)) :
    c ∈ MR ∨ c * tR ∈ MR := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  obtain ⟨g, rfl | rfl⟩ := eq_jR_or c
  · exact Or.inl ⟨g, (commute_tR_iff g).1 hc, rfl⟩
  · right
    have hg : g ∈ M := by
      apply (commute_tR_iff g).1
      calc jR g * tR = jR g * tR * tR * tR := by
            rw [mul_assoc (jR g * tR), tR_mul_tR, mul_one]
        _ = tR * (jR g * tR) * tR := by rw [hc]
        _ = tR * jR g := by simp only [mul_assoc, tR_mul_tR, mul_one]
    rw [mul_assoc, tR_mul_tR, mul_one]
    exact ⟨g, hg, rfl⟩

theorem mul_tR_mem_MR
    {f : R} (hf : f ∈ LocalClass D24 tR) : f * tR ∈ MR := by
  have hc : f * tR ∈ Subgroup.centralizer ({tR} : Set R) := by
    rw [Subgroup.mem_centralizer_singleton_iff, mul_assoc, tR_mul_tR, mul_one, ← mul_assoc,
      ← hf.2.2, mul_assoc, tR_mul_tR, mul_one]
  rcases mem_MR_or_of_commute hc with h | h
  · exact h
  · rw [mul_assoc, tR_mul_tR, mul_one] at h
    exact absurd (MR_le_JR h) (not_mem_JR_of_mem_D24 hf.1)

instance isSimpleGroup_MR :
    IsSimpleGroup MR :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_M mREquiv

theorem center_MR :
    Subgroup.center MR = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : mREquiv z ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have := congrArg mREquiv (hz (mREquiv.symm g))
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    exact this
  rw [center_M, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  calc z = mREquiv.symm (mREquiv z) := (MulEquiv.symm_apply_apply _ _).symm
    _ = 1 := by rw [hz', map_one]

theorem exists_two_mem_localClass :
    ∃ f₁ ∈ LocalClass D24 tR, ∃ f₂ ∈ LocalClass D24 tR, f₁ ≠ f₂ := by
  have : Finite (LocalClass D24 tR) := Subtype.finite
  have h : 1 < Nat.card (LocalClass D24 tR) := by rw [card_localClass]; norm_num
  obtain ⟨⟨f₁, hf₁⟩, ⟨f₂, hf₂⟩, hne⟩ :=
    (Finite.one_lt_card_iff_nontrivial.1 h).exists_pair_ne
  exact ⟨f₁, hf₁, f₂, hf₂, fun e => hne (Subtype.ext e)⟩

theorem exists_localQuotientEquiv_MR :
    ∃ φ : LocalQuotient D24 tR ≃* MR,
      (fun q => ((φ q : MR) : R)) '' LocalImages D24 tR =
        (fun f => f * tR) '' LocalClass D24 tR :=
  exists_localQuotientEquiv pair_R tR_mem_D24 (fun _ hc => mem_MR_or_of_commute hc)
    (fun _ hm => commute_tR_of_mem_MR hm) tR_not_mem_MR (fun _ hf => mul_tR_mem_MR hf)
    center_MR exists_two_mem_localClass

@[expose] noncomputable def fi23EquivJMR :
    MR ≃* Fi23.J := mREquiv.trans fi23EquivM

theorem mul_tR_mul_mul_tR
    {f f' : R} (hf' : f' ∈ LocalClass D24 tR) :
    f * tR * (f' * tR) = f * f' := by
  rw [show f * tR * (f' * tR) = f * (tR * f') * tR by group, ← hf'.2.2, mul_assoc,
    mul_assoc, tR_mul_tR, mul_one]

theorem isConj_d_fi23EquivJMR
    {f : R} (hf : f ∈ LocalClass D24 tR) :
    IsConj Fi23.d (fi23EquivJMR ⟨f * tR, mul_tR_mem_MR hf⟩) := by
  set s : MR := ⟨f * tR, mul_tR_mem_MR hf⟩
  have hs2 : s * s = 1 := by
    apply Subtype.ext
    show f * tR * (f * tR) = 1
    rw [mul_tR_mul_mul_tR hf, Pair.mul_self pair_R hf.1]
  have hs1 : s ≠ 1 := by
    intro h
    apply hf.2.1
    have h' : f * tR = 1 := by
      have := congrArg Subtype.val h
      rwa [OneMemClass.coe_one] at this
    calc f = f * tR * tR := by rw [mul_assoc, tR_mul_tR, mul_one]
      _ = tR := by rw [h', one_mul]
  apply Fi23.isConj_d_of_orderOf
  · rw [sq, ← map_mul, hs2, map_one]
  · rw [Ne, MulEquiv.map_eq_one_iff]
    exact hs1
  · intro w
    obtain ⟨m, rfl⟩ := fi23EquivJMR.surjective w
    rw [← map_mul, ← map_inv, ← map_mul, ← map_mul, MulEquiv.orderOf_eq]
    have hm := commute_tR_of_mem_MR m.2
    have hf' : (m : R) * f * (m : R)⁻¹ ∈ LocalClass D24 tR :=
      conj_mem_localClass_of_commute pair_R hm hf
    have hconj : m * s * m⁻¹ = ⟨(m : R) * f * (m : R)⁻¹ * tR, mul_tR_mem_MR hf'⟩ := by
      apply Subtype.ext
      show (m : R) * (f * tR) * (m : R)⁻¹ = (m : R) * f * (m : R)⁻¹ * tR
      have hmi : (m : R)⁻¹ * tR = tR * (m : R)⁻¹ := by
        calc (m : R)⁻¹ * tR = (m : R)⁻¹ * (tR * (m : R)) * (m : R)⁻¹ := by group
          _ = (m : R)⁻¹ * ((m : R) * tR) * (m : R)⁻¹ := by rw [hm]
          _ = tR * (m : R)⁻¹ := by group
      rw [show (m : R) * (f * tR) * (m : R)⁻¹ = (m : R) * f * (tR * (m : R)⁻¹) by group, ← hmi]
      group
    rw [hconj, ← Subgroup.orderOf_coe]
    show orderOf (f * tR * ((m : R) * f * (m : R)⁻¹ * tR)) ∈ _
    rw [mul_tR_mul_mul_tR hf']
    exact pair_R.2.2.2.1 f hf.1 _ hf'.1

theorem exists_localQuotientEquiv_fi23 :
    ∃ Φ : LocalQuotient D24 tR ≃* Fi23.J, Φ '' LocalImages D24 tR = Fi23.D23 := by
  obtain ⟨φ, hφ⟩ := exists_localQuotientEquiv_MR
  refine ⟨φ.trans fi23EquivJMR, ?_⟩
  have hinj : Function.Injective (fun q => ((φ q : MR) : R)) :=
    Subtype.val_injective.comp φ.injective
  have hsub : (φ.trans fi23EquivJMR) '' LocalImages D24 tR ⊆ Fi23.D23 := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨f, hf, hfq⟩ : ((φ q : MR) : R) ∈ (fun f => f * tR) '' LocalClass D24 tR :=
      hφ ▸ ⟨q, hq, rfl⟩
    have : φ q = ⟨f * tR, mul_tR_mem_MR hf⟩ := Subtype.ext hfq.symm
    show IsConj Fi23.d (fi23EquivJMR (φ q))
    rw [this]
    exact isConj_d_fi23EquivJMR hf
  have hcard1 : (LocalImages D24 tR).ncard = 31671 := by
    have h1 := congrArg Set.ncard hφ
    have h2 : (LocalClass D24 tR).ncard = 31671 := by
      rw [← Nat.card_coe_set_eq]; exact card_localClass
    rw [Set.ncard_image_of_injective _ hinj,
      Set.ncard_image_of_injective _ (mul_left_injective tR), h2] at h1
    exact h1
  have hcard2 : (Fi23.D23).ncard = 31671 := by
    rw [← Nat.card_coe_set_eq]
    exact Fi23.card_class_d
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  have h3 := Set.ncard_image_of_injective (LocalImages D24 tR) (φ.trans fi23EquivJMR).injective
  omega

theorem f24_R :
    F24 R D24 := by
  obtain ⟨Φ, hΦ⟩ := exists_localQuotientEquiv_fi23
  have h : F23 (LocalQuotient D24 tR) (LocalImages D24 tR) :=
    (@F23_congr (LocalQuotient D24 tR) (↥Fi23.J) inferInstance inferInstance
      (LocalImages D24 tR) Fi23.D23 Φ hΦ).2 Fi23.f23_J
  exact ⟨pair_R, tR, tR_mem_D24, h⟩

theorem localStructureAt_tR :
    LocalStructureAt 2 tR :=
  ⟨fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun _ => ⟨MR, ⟨fi23EquivMR⟩, centralizer_tR, zpowers_tR_inf_MR,
      zpowers_tR_le_centralizer_MR⟩⟩

theorem localStructureAt_of_mem
    {x : R} (hx : x ∈ D24) : LocalStructureAt 2 x := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hx
  exact localStructureAt_tR.map (MulAut.conj g)

end CFSG.Sporadic.Fi24

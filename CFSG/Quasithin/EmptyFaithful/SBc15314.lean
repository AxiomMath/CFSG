module

public import CFSG.Quasithin.EmptyFaithful.S153GExtra
public import CFSG.Quasithin.EmptyFaithful.S153YCases
public import CFSG.Quasithin.EmptyFaithful.S153Syl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc

section Basic

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

omit [Finite G] in
private theorem conj_inv_eq_conj {V : Subgroup G} {t v : G}
    (ht : t * t ∈ Subgroup.centralizer (V : Set G)) (hv : v ∈ V) :
    t⁻¹ * v * t = t * v * t⁻¹ := by
  have hv' : v * (t * t) = (t * t) * v := Subgroup.mem_centralizer_iff.mp ht v hv
  calc t⁻¹ * v * t = t⁻¹ * (v * (t * t)) * t⁻¹ := by group
    _ = t⁻¹ * ((t * t) * v) * t⁻¹ := by rw [hv']
    _ = t * v * t⁻¹ := by group

private theorem conj_inv_mem_V₁ (D : Decomp153 T M V₁ V₂ t) {v : G} (hv : v ∈ V₂) :
    t⁻¹ * v * t ∈ V₁ := by
  rw [conj_inv_eq_conj D.t_sq (D.le₂ hv)]
  exact D.swap₂ v hv

theorem Y153_not_le_centralizer_V₁ (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (D : Decomp153 T M V₁ V₂ t) :
    ¬ Y153 Mc M ≤ Subgroup.centralizer (V₁ : Set G) := by
  intro hle
  refine h.Y153_not_le_centralizer h113 ?_
  rw [← D.sup]
  have hV₁ : V₁ ≤ Subgroup.centralizer (Y153 Mc M : Set G) := Subgroup.le_centralizer_iff.mp hle
  have hV₂ : V₂ ≤ Subgroup.centralizer (Y153 Mc M : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : t⁻¹ * y * t ∈ Y153 Mc M := by
      have h2 : t⁻¹ ∈ Subgroup.normalizer (Y153 Mc M : Set G) :=
        inv_mem (le_normalizer_Y153 Mc M D.t_mem)
      have := (Subgroup.mem_normalizer_iff.mp h2 y).mp hy
      simpa using this
    have hcomm : (t⁻¹ * y * t) * (t⁻¹ * v * t) = (t⁻¹ * v * t) * (t⁻¹ * y * t) :=
      Subgroup.mem_centralizer_iff.mp (hV₁ (conj_inv_mem_V₁ D hv)) _ hy'
    calc y * v = t * ((t⁻¹ * y * t) * (t⁻¹ * v * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * v * t) * (t⁻¹ * y * t)) * t⁻¹ := by rw [hcomm]
      _ = v * y := by group
  rw [Subgroup.le_centralizer_iff]
  exact sup_le hV₁ hV₂

end Basic

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I : Subgroup G} {t : G}

private theorem card_nine_of_isElemAbelianOfRank {X : Type} [Group X]
    (h : IsElemAbelianOfRank 3 2 X) : Nat.card X = 9 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

private theorem not_caseOne (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    (hrank : CFSG.Open.pRank 3 Yp = 2)
    (hYp : Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)))
    (hcore : pCoreOf 2 (Y153 Mc M) = Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G))
    (hE : IsElemAbelianOfRank 3 2 (OTwoQuot (Y153 Mc M))) : False := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := Y153 Mc M with hY
  have hYV₁ := Y153_not_le_centralizer_V₁ h113 h.hyp h.decomp
  have hYple : Yp ≤ Y ⊓ Subgroup.centralizer (V₁ : Set G) := hYp ▸ oTwoUpper_le _
  have hYpY : Yp ≤ Y := hYple.trans inf_le_left
  have hYpC : Yp ≤ Subgroup.centralizer (V₁ : Set G) := hYple.trans inf_le_right
  have hOC : pCoreOf 2 Y ≤ Subgroup.centralizer (V₁ : Set G) := by
    rw [hcore]
    exact inf_le_right.trans (Subgroup.centralizer_le h.decomp.le₁)
  obtain ⟨E, hEYp, hE3, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) Yp
  rw [hrank] at hEcard
  have hEY : E ≤ Y := hEYp.trans hYpY
  let f : ↥E →* OTwoQuot Y :=
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)).comp (Subgroup.inclusion hEY)
  have hmem : ∀ x : ↥E, f x = 1 → (x : G) ∈ pCoreOf 2 Y := fun x hx =>
    (mk_eq_one_iff_mem_pCoreOf (⟨(x : G), hEY x.2⟩ : ↥Y)).mp hx
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO := hmem x hx
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 Y ⟨(x : G), hxO⟩
    have h2k : (x : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h3 : (x : G) ^ 3 = 1 := hE3.2 x x.2
    have hord : orderOf (x : G) = 1 := by
      have d1 : orderOf (x : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2k
      have d2 : orderOf (x : G) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
      have d3 := Nat.dvd_gcd d1 d2
      rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))] at d3
      exact Nat.dvd_one.mp d3
    exact Subtype.ext (orderOf_eq_one_iff.mp hord)
  have hcardQ : Nat.card (OTwoQuot Y) = 9 := card_nine_of_isElemAbelianOfRank hE
  have hrange : f.range = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top]
    rw [Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv.symm, hEcard, hcardQ]
    norm_num
  apply hYV₁
  intro y hy
  have hq : (QuotientGroup.mk (⟨y, hy⟩ : ↥Y) : OTwoQuot Y) ∈ f.range := by
    rw [hrange]; exact Subgroup.mem_top _
  obtain ⟨e, he⟩ := hq
  have hdiff : ((⟨(e : G), hEY e.2⟩ : ↥Y)⁻¹ * ⟨y, hy⟩) ∈ CFSG.Open.pCore 2 ↥Y := by
    rw [← QuotientGroup.eq]
    exact he
  have hdiff' : (e : G)⁻¹ * y ∈ pCoreOf 2 Y := by
    have : (⟨(e : G), hEY e.2⟩ : ↥Y)⁻¹ * ⟨y, hy⟩ = ⟨(e : G)⁻¹ * y, Y.mul_mem (Y.inv_mem (hEY e.2)) hy⟩ := rfl
    rw [this] at hdiff
    exact (Subgroup.mem_map_iff_mem Y.subtype_injective).mpr hdiff
  have : y = (e : G) * ((e : G)⁻¹ * y) := by group
  rw [this]
  exact Subgroup.mul_mem _ (hYpC (hEYp e.2)) (hOC hdiff')

private theorem caseTwo_relIndex (h : Hyp153 G T Mc M)
    (hP : IsPOnePlusTwo 3 (OTwoQuot (Y153 Mc M)))
    (hZ : O2Z (Y153 Mc M) = Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)) :
    (pCoreOf 2 (Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G))).relIndex
      (Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)) = 3 := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := Y153 Mc M with hY
  set C : Subgroup G := Y ⊓ Subgroup.centralizer (VZ T M : Set G) with hC
  have hCY : C ≤ Y := inf_le_left
  have hYN : Y ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg,
        normalizer_le_normalizer_centralizer _ (((Y153_le Mc M).trans h.le_normalizer) hg)⟩
  have hPC : pCoreOf 2 Y ≤ C := by
    intro y hy
    rw [← hZ, mem_O2Z_iff]
    refine ⟨pCoreOf_le 2 Y hy, ?_⟩
    have : (QuotientGroup.mk (⟨y, pCoreOf_le 2 Y hy⟩ : ↥Y) : OTwoQuot Y) = 1 :=
      (mk_eq_one_iff_mem_pCoreOf _).mpr hy
    rw [this]
    exact Subgroup.one_mem _
  have hcore : pCoreOf 2 C = pCoreOf 2 Y := by
    apply le_antisymm
    · exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 C).trans hCY)
        (hYN.trans (normalizer_le_normalizer_pCoreOf 2 C)) (pCoreOf_isPGroup 2 C)
    · exact le_pCoreOf_of_le_normalizer 2 hPC (fun g hg => le_normalizer_pCoreOf 2 Y (hCY hg))
        (pCoreOf_isPGroup 2 Y)
  rw [hcore]
  let f : ↥C →* OTwoQuot Y :=
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)).comp (Subgroup.inclusion hCY)
  have hker : f.ker = (pCoreOf 2 Y).subgroupOf C := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact mk_eq_one_iff_mem_pCoreOf (⟨(x : G), hCY x.2⟩ : ↥Y)
  have hrange : f.range = Subgroup.center (OTwoQuot Y) := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      have hxO : (x : G) ∈ O2Z Y := by
        rw [hZ]
        exact x.2
      obtain ⟨hy, hc⟩ := mem_O2Z_iff.mp hxO
      exact hc
    · intro hq
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      have hyC : (y : G) ∈ C := by
        rw [← hZ, mem_O2Z_iff]
        exact ⟨y.2, hq⟩
      exact ⟨⟨(y : G), hyC⟩, rfl⟩
  have h1 : Subgroup.relIndex (pCoreOf 2 Y) C = f.ker.index := by
    rw [hker]
    rfl
  rw [h1, Subgroup.index_ker, hrange]
  have := hP.1
  exact CFSG.IsExtraspecial.center_order_p 3 (OTwoQuot Y)

end Main

theorem input15314Two_holds (h113 : StageLemma14113) : Input15314Two := by
  intro G _ _ T Mc M V₁ V₂ Yp I t c hc2
  obtain ⟨-, hYp⟩ := hc2
  have h := c.hyp
  rcases h.hyp.lemma_15_3_7_cases h113 with ⟨hcore, hE⟩ | ⟨hP, hZ⟩
  · exact (not_caseOne h113 h c.rank hYp hcore hE).elim
  · exact ⟨hP, caseTwo_relIndex h.hyp hP hZ⟩

end SBc

end CFSG.Quasithin

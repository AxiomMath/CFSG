module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeAxB
public import CFSG.Quasithin.Background.A3Structure38Basic
public import CFSG.Quasithin.Vol2.Ch4Sec4L443EFact

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
open scoped Pointwise commutatorElement

variable {H : Type} [Group H]

theorem ker_conj_eq_center (K : Type) [Group K] :
    (MulAut.conj : K →* MulAut K).ker = Subgroup.center K := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have h1 := congrArg (fun φ : MulAut K => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc x * g = g * x * g⁻¹ * g := by rw [h1]
      _ = g * x := by group
  · intro h
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h x]
    group

theorem sup_centralizer_le_normalizer (K : Subgroup H) :
    K ⊔ Subgroup.centralizer (K : Set H) ≤ Subgroup.normalizer (K : Set H) :=
  sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)

theorem normalizerMonoidHom_mem_range (K : Subgroup H)
    (y : ↥(K ⊔ Subgroup.centralizer (K : Set H))) :
    Subgroup.normalizerMonoidHom K (Subgroup.inclusion (sup_centralizer_le_normalizer K) y) ∈
      (MulAut.conj : ↥K →* MulAut ↥K).range := by
  have hKC : K ≤ Subgroup.normalizer (Subgroup.centralizer (K : Set H) : Set H) :=
    Subgroup.le_normalizer.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer K)
  have hy : (y : H) ∈ (K : Set H) * (Subgroup.centralizer (K : Set H) : Set H) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K _ hKC]
    exact y.2
  obtain ⟨k, hk, c, hc, hkc⟩ := hy
  refine ⟨⟨k, hk⟩, ?_⟩
  ext x
  rw [MulAut.conj_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
  rw [← hkc]
  have h1 := Subgroup.mem_centralizer_iff.mp hc _ x.2
  calc k * x * k⁻¹ = k * (c * x * c⁻¹) * k⁻¹ := by
        rw [← h1]
        group
    _ = k * c * x * (k * c)⁻¹ := by group

noncomputable def innEquiv (K : Subgroup H) :
    ↥(MulAut.conj : ↥K →* MulAut ↥K).range ≃* ↥K ⧸ Subgroup.center ↥K :=
  (QuotientGroup.quotientKerEquivRange _).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (ker_conj_eq_center ↥K))

noncomputable def innerQuot (K : Subgroup H) :
    ↥(K ⊔ Subgroup.centralizer (K : Set H)) →* ↥K ⧸ Subgroup.center ↥K :=
  (innEquiv K).toMonoidHom.comp
    (((Subgroup.normalizerMonoidHom K).comp
      (Subgroup.inclusion (sup_centralizer_le_normalizer K))).codRestrict _
      (normalizerMonoidHom_mem_range K))

theorem mem_centralizer_of_innerQuot_eq_one {K : Subgroup H}
    {y : ↥(K ⊔ Subgroup.centralizer (K : Set H))} (hy : innerQuot K y = 1) :
    (y : H) ∈ Subgroup.centralizer (K : Set H) := by
  have h1 : ((Subgroup.normalizerMonoidHom K).comp
      (Subgroup.inclusion (sup_centralizer_le_normalizer K))) y = 1 := by
    have h2 := (innEquiv K).injective (hy.trans (map_one (innEquiv K)).symm)
    exact congrArg Subtype.val h2
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h3 := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : H)) h1
  simp only [MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
    MulAut.one_apply, Subgroup.coe_inclusion] at h3
  calc x * (y : H) = (y : H) * x * (y : H)⁻¹ * (y : H) := by rw [h3]
    _ = (y : H) * x := by group

theorem commutator_subgroupOf_eq {V X Y : Subgroup H} (hVY : V ≤ Y)
    (hXY : X ≤ Y) (hV : ⁅V, X⁆ = V) : ⁅V.subgroupOf Y, X.subgroupOf Y⁆ = V.subgroupOf Y := by
  apply Subgroup.map_injective Y.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hVY,
    Subgroup.map_subgroupOf_eq_of_le hXY, hV]

variable [Finite H]

theorem normal_of_fact4411 (hF : A38Facts) (h4411 : Fact4411) (hQ : IsQuasithin H)
    (hKg : CFSG.SectionRank.IsKGroupCat H) {K LB V : Subgroup H} (hK : CFSG.IsComponent K)
    (hO2K : CFSG.pCore 2 ↥K = ⊥) (hLBY : LB ≤ K ⊔ Subgroup.centralizer (K : Set H))
    (hVY : V ≤ K ⊔ Subgroup.centralizer (K : Set H)) (hLB : ⁅LB, LB⁆ = LB)
    (hV2 : IsPGroup 2 V) (hVeq : V = ⁅V, LB⁆)
    (hKV : ⁅K, V⁆ ≠ ⊥) : K.Normal := by
  by_contra hn
  obtain ⟨-, hlist⟩ := A38.a38_part12 hF H hQ hKg K hK hO2K hn
  set Y := K ⊔ Subgroup.centralizer (K : Set H) with hY
  set ρ := innerQuot K with hρ
  set U := (V.subgroupOf Y).map ρ with hU
  set Z := (LB.subgroupOf Y).map ρ with hZ
  have hV' : ⁅V.subgroupOf Y, LB.subgroupOf Y⁆ = V.subgroupOf Y :=
    commutator_subgroupOf_eq hVY hLBY hVeq.symm
  have hL' : ⁅LB.subgroupOf Y, LB.subgroupOf Y⁆ = LB.subgroupOf Y :=
    commutator_subgroupOf_eq hLBY hLBY hLB
  have hUZ : ⁅U, Z⁆ = U := by rw [hU, hZ, ← Subgroup.map_commutator, hV']
  have hZZ : ⁅Z, Z⁆ = Z := by rw [hZ, ← Subgroup.map_commutator, hL']
  have hU2 : IsPGroup 2 U :=
    (hV2.comap_of_injective Y.subtype Y.subtype_injective).map ρ
  have hZU : Z ≤ Subgroup.normalizer (U : Set (↥K ⧸ Subgroup.center ↥K)) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hUZ.le
  have h1 := h4411 ↥K hK.1 hlist U Z hU2 hZZ hZU
  rw [hUZ] at h1
  apply hKV
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  have hvU : ρ ⟨v, hVY hv⟩ ∈ U := ⟨⟨v, hVY hv⟩, hv, rfl⟩
  rw [h1, Subgroup.mem_bot] at hvU
  exact mem_centralizer_of_innerQuot_eq_one hvU

end CFSG.Quasithin.H13.Ch4.E443

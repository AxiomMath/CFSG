module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5Sigma2
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5Defs
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Data
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Esimple6

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (KProper InCatalog)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

theorem sec35_sigma_core {b : G} {U U₂ : Subgroup G} (hb : b ∈ Nor U) (hb3 : b ^ 3 = 1)
    (hQodd : Odd (Nat.card (pPrimeCore 3 ↥(CenS U))))
    (hU₂ : IsElemAb 3 2 U₂) (hU₂E : U₂ ≤ OppE 3 (CenS U)) (hbU₂ : b ∈ Nor U₂)
    (σ' : ↥(layer (CQ U)))
    (hσ'o : orderOf σ' = 2) (hσ'f : layerMulAut (CQ U) (cqβ U b hb) σ' = σ')
    (hσ'i : ∀ s : ↥(layer (CQ U)), (s : CQ U) ∈ cqImg U U₂ → σ' * s * σ'⁻¹ = s⁻¹) :
    ∃ σ : G, orderOf σ = 2 ∧ σ ∈ Cen b ∧ σ ∈ CenS U ∧ ∀ x ∈ U₂, σ * x * σ⁻¹ = x⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hQn : (pPrimeCore 3 ↥(CenS U)).Normal := pPrimeCore_normal
  have hU₂C : U₂ ≤ CenS U := fun x hx => OppE_le _ (hU₂E hx)
  have hU₂3 : IsPGroup 3 U₂ := IsPGroup.of_card hU₂.2
  have hbU₂' : ∀ x : G, x ∈ U₂ ↔ b * x * b⁻¹ ∈ U₂ := fun x =>
    Subgroup.mem_set_normalizer_iff.mp hbU₂ x
  set y : CQ U := (σ' : CQ U) with hy
  have hyfix : cqβ U b hb y = y := by
    have := congrArg (fun e : ↥(layer (CQ U)) => (e : CQ U)) hσ'f
    simpa [layerMulAut_coe] using this
  have hy2 : y ^ 2 = 1 := by
    have := pow_orderOf_eq_one σ'
    rw [hσ'o] at this
    exact congrArg (fun e : ↥(layer (CQ U)) => (e : CQ U)) this
  have hy1 : y ≠ 1 := by
    intro h1
    have : σ' = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hσ'o
    omega
  obtain ⟨ĉ, hĉb, hĉy⟩ := cq_lift_fixed hb hb3 hyfix
  have hinv : ∀ x : ↥(CenS U), (x : G) ∈ U₂ →
      y * (QuotientGroup.mk x : CQ U) * y⁻¹ = (QuotientGroup.mk x : CQ U)⁻¹ := by
    intro x hx
    have hxE : (QuotientGroup.mk x : CQ U) ∈ layer (CQ U) := by
      have := (mem_OppE.mp (hU₂E hx)).2
      exact this
    have hmem : ((⟨_, hxE⟩ : ↥(layer (CQ U))) : CQ U) ∈ cqImg U U₂ := mk_mem_cqImg x hx
    have := congrArg (fun e : ↥(layer (CQ U)) => (e : CQ U)) (hσ'i _ hmem)
    simpa using this
  obtain ⟨g', hg'τ, hg'P, hg'Q⟩ := sigma_frattini_fix (Γ := ↥(CenS U))
    (pPrimeCore 3 ↥(CenS U)) pPrimeCore_coprime_card (U₂.subgroupOf (CenS U))
    (isPGroup_subgroupOf hU₂3 hU₂C) (conjAut (CenS U) b (nor_cenS_of_nor hb))
    (conjAut_pow3 (nor_cenS_of_nor hb) hb3)
    (fun q hq => by
      have := Subgroup.mem_map_of_mem (conjAut (CenS U) b (nor_cenS_of_nor hb)).toMonoidHom hq
      rwa [pPrimeCore_map_iso 3 (conjAut (CenS U) b (nor_cenS_of_nor hb))] at this)
    (fun x => by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hbU₂' x)
    ĉ (by
      apply Subtype.ext
      show b * (ĉ : G) * b⁻¹ = ĉ
      exact mul_inv_eq_iff_eq_mul.mpr
        (Subgroup.mem_centralizer_iff.mp hĉb b (Set.mem_singleton b)))
    (fun x hx => by
      have hx' : (x : G) ∈ U₂ := hx
      have h1 : (QuotientGroup.mk (ĉ * x * ĉ⁻¹) : CQ U) = QuotientGroup.mk x⁻¹ := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hĉy,
          QuotientGroup.mk_inv, hinv x hx']
      have h2 : x * (ĉ * x * ĉ⁻¹) ∈ pPrimeCore 3 ↥(CenS U) := by
        have := QuotientGroup.eq.mp h1.symm
        simpa using this
      have h3 : ĉ * x * ĉ⁻¹ = x⁻¹ * (x * (ĉ * x * ĉ⁻¹)) := by group
      rw [h3]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ((U₂.subgroupOf (CenS U)).inv_mem hx))
        (Subgroup.mem_sup_left h2))
  have hg'y : (QuotientGroup.mk g' : CQ U) = y := by
    rw [← hĉy]
    exact QuotientGroup.eq.mpr hg'Q
  have hg'sq : g' ^ 2 ∈ pPrimeCore 3 ↥(CenS U) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hg'y, hy2]
  have hmodd : Odd (orderOf (g' ^ 2)) := by
    have h1 : orderOf (⟨g' ^ 2, hg'sq⟩ : ↥(pPrimeCore 3 ↥(CenS U))) ∣
        Nat.card (pPrimeCore 3 ↥(CenS U)) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hQodd h1
  set m := orderOf (g' ^ 2) with hm
  have hσ2 : (g' ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_orderOf_eq_one _
  have hπσ : (QuotientGroup.mk (g' ^ m) : CQ U) = y := by
    obtain ⟨k, hk⟩ := hmodd
    rw [QuotientGroup.mk_pow, hg'y, hk, pow_succ, pow_mul, hy2, one_pow, one_mul]
  have hσne : g' ^ m ≠ 1 := by
    intro h1
    apply hy1
    rw [← hπσ, h1]
    rfl
  have hord : orderOf (g' ^ m) = 2 := orderOf_eq_prime hσ2 hσne
  have hg'nor : g' ∈ Nor (U₂.subgroupOf (CenS U)) := L41.mem_nor_of_forall hg'P
  have hσnor : g' ^ m ∈ Nor (U₂.subgroupOf (CenS U)) := Subgroup.pow_mem _ hg'nor m
  refine ⟨((g' ^ m : ↥(CenS U)) : G), ?_, ?_, (g' ^ m).2, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hord
  · have h1 : conjAut (CenS U) b (nor_cenS_of_nor hb) (g' ^ m) = g' ^ m := by
      rw [map_pow, hg'τ]
    have h2 := congrArg Subtype.val h1
    change b * ((g' ^ m : ↥(CenS U)) : G) * b⁻¹ = (g' ^ m : ↥(CenS U)) at h2
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact mul_inv_eq_iff_eq_mul.mp h2
  · intro x hx
    obtain ⟨xt, rfl⟩ : ∃ xt : ↥(CenS U), (xt : G) = x := ⟨⟨x, hU₂C hx⟩, rfl⟩
    have hxP : xt ∈ U₂.subgroupOf (CenS U) := hx
    have h1 : g' ^ m * xt * (g' ^ m)⁻¹ ∈ U₂.subgroupOf (CenS U) :=
      (Subgroup.mem_set_normalizer_iff.mp hσnor xt).mp hxP
    have h2 : xt⁻¹ ∈ U₂.subgroupOf (CenS U) := Subgroup.inv_mem _ hxP
    have hmk : (QuotientGroup.mk (g' ^ m * xt * (g' ^ m)⁻¹) : CQ U) =
        QuotientGroup.mk xt⁻¹ := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hπσ,
        QuotientGroup.mk_inv, hinv _ hx]
    have := cq_eq_of_mk_eq hU₂3 hU₂C
      (x := g' ^ m * xt * (g' ^ m)⁻¹) (y := xt⁻¹) h1 h2 hmk
    simpa using congrArg Subtype.val this

variable {b : G} {J B A P D : Subgroup G} {a : G}

theorem sec35_sigma (hKL : FF79KL35a) (hG : IsSimpleGroup G) (hna : ∃ x y : G, x * y ≠ y * x)
    (hKp : KProper InCatalog G) (hs : FF79Sec3 b J) (h : FF79Sec34In b J B A P D)
    (hU : FF79Sec34UFacts b a J A) (hoa : orderOf a = 3)
    (hK : IsLnq 2 2 2 (Lay (J ⊓ Cen a))) (haC : a ∈ CenS (U34 b a J A))
    (hL : IsLnq 3 2 2 (⊤ : Subgroup (layer (CenS (U34 b a J A) ⧸
      pPrimeCore 3 (CenS (U34 b a J A))))))
    (hU₂ : IsElemAb 3 2 (A ⊓ OppE 3 (CenS (U34 b a J A))))
    (hbU₂ : b ∈ Nor (A ⊓ OppE 3 (CenS (U34 b a J A)))) :
    ∃ σ : G, orderOf σ = 2 ∧ σ ∈ Cen b ∧ σ ∈ CenS (U34 b a J A) ∧
      ∀ x ∈ A ⊓ OppE 3 (CenS (U34 b a J A)), σ * x * σ⁻¹ = x⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb3 : b ^ 3 = 1 := by rw [← h.hyp.ord]; exact pow_orderOf_eq_one b
  have hd := sec34_APData hG hna hKp hs h hU hoa hK haC
  have hKE := (ap_E_simple hd).2.2.1
  have hQodd : Odd (Nat.card (pPrimeCore 3 ↥(CenS (U34 b a J A)))) := by
    have := sec34_odd_opp hs h hU
    unfold Opp inSubgroup at this
    rwa [Subgroup.card_map_of_injective (CenS (U34 b a J A)).subtype_injective] at this
  set U : Subgroup G := U34 b a J A with hUdef
  set U₂ : Subgroup G := A ⊓ OppE 3 (CenS U) with hU₂def
  have hU₂E : U₂ ≤ OppE 3 (CenS U) := inf_le_right
  have hU₂C : U₂ ≤ CenS U := fun x hx => OppE_le _ (hU₂E hx)
  have hU₂3 : IsPGroup 3 U₂ := IsPGroup.of_card hU₂.2
  have hbU₂' : ∀ x : G, x ∈ U₂ ↔ b * x * b⁻¹ ∈ U₂ := fun x =>
    Subgroup.mem_set_normalizer_iff.mp hbU₂ x
  have hSle : cqImg U U₂ ≤ layer (CQ U) := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := mem_cqImg.mp hy
    exact (mem_OppE.mp (hU₂E hc)).2
  have hLE : StatedClassicalModel ↥(layer (CQ U)) .PSL 3 2 2 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv Subgroup.topEquiv hL
  have hβ3 : layerMulAut (CQ U) (cqβ U b hU.b_nor) ^ 3 = 1 := by
    rw [← map_pow, cqβ_pow_three hU.b_nor hb3, map_one]
  have hScard : Nat.card ((cqImg U U₂).subgroupOf (layer (CQ U))) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSle).toEquiv,
      cqImg_card hU₂3 hU₂C, hU₂.2]
    norm_num
  have hSstab : ∀ s ∈ (cqImg U U₂).subgroupOf (layer (CQ U)),
      layerMulAut (CQ U) (cqβ U b hU.b_nor) s ∈ (cqImg U U₂).subgroupOf (layer (CQ U)) := by
    intro s hs'
    obtain ⟨c, hc, hcs⟩ := mem_cqImg.mp (Subgroup.mem_subgroupOf.mp hs')
    rw [Subgroup.mem_subgroupOf, layerMulAut_coe, ← hcs, mk_conjAut_eq]
    exact mk_mem_cqImg _ ((hbU₂' _).mp hc)
  obtain ⟨hKa5, hKfix, -, -⟩ := sec34_ap_K hs h hU hoa hK
  have hKmod : StatedClassicalModel
      ↥((cqImg U (Lay (J ⊓ Cen a))).subgroupOf (layer (CQ U))) .PSL 2 2 2 := by
    obtain ⟨f⟩ := mapEquiv_of_injOn ((Lay (J ⊓ Cen a)).subgroupOf (CenS U))
      (QuotientGroup.mk' (pPrimeCore 3 ↥(CenS U))) (by
        intro x hx y hy hxy
        have hmem : x⁻¹ * y ∈ pPrimeCore 3 ↥(CenS U) := QuotientGroup.eq.mp hxy
        have := sec34_K_inf_core hU hK _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy) hmem
        exact inv_mul_eq_one.mp this)
    have e : ↥(Lay (J ⊓ Cen a)) ≃*
        ↥((cqImg U (Lay (J ⊓ Cen a))).subgroupOf (layer (CQ U))) :=
      ((Subgroup.subgroupOfEquivOfLe hU.K_cen_U).symm.trans f).trans
        (Subgroup.subgroupOfEquivOfLe hKE).symm
    exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e hK
  obtain ⟨σ', hσ'o, hσ'f, hσ'i⟩ := hKL _ hLE _ hβ3 _ hScard hSstab
    ⟨_, hKmod, fun x hx => Subtype.ext (by
      rw [layerMulAut_coe]
      exact hKfix _ (Subgroup.mem_subgroupOf.mp hx))⟩
  exact sec35_sigma_core hU.b_nor hb3 hQodd hU₂ hU₂E hbU₂ σ' hσ'o
    hσ'f
    (fun s hs' => hσ'i s (Subgroup.mem_subgroupOf.mpr hs'))

end CFSG.RankThree.PartTwo.Sec21.FF79

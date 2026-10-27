module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5Iii
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5Defs
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4StructMain
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4LoAut
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Data

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (KProper InCatalog)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem kl35b_apply (hKL : FF79KL35b) {H : Type} [Group H] [Finite H] {β : MulAut H}
    {K L : Subgroup H} (hβ : β ^ 3 = 1) (hS : FF79APStruct β K L)
    (hKfix : ∀ k ∈ K, β k = k) (hKm : IsLnq 2 2 2 K)
    (hL : IsLnq 3 2 2 (⊤ : Subgroup ↥(layer H))) :
    ∀ y ∈ layer H, β y = y → y ∈ K := by
  have hLe := hS.layer_eq
  subst hLe
  have hm := hS.β_mem
  let x : MulAut ↥(layer H) := restrAut β (layer H) hβ hm
  have hx3 : x ^ 3 = 1 := by
    refine MulEquiv.ext fun l => Subtype.ext ?_
    have h1 : ((x ^ 3) l : ↥(layer H)) = x (x (x l)) := by simp [pow_succ]
    rw [h1]
    show β (β (β (l : H))) = (l : H)
    exact aut_cube_apply hβ _
  have hxconj : ∀ c : ↥(layer H), x ≠ MulAut.conj c := by
    intro c hc
    apply hS.outer c c.2
    intro l hl
    have e : β l = c * l * (c : H)⁻¹ :=
      congrArg (fun f : MulAut ↥(layer H) => ((f ⟨l, hl⟩ : ↥(layer H)) : H)) hc
    exact e
  have hEm : StatedClassicalModel ↥(layer H) .PSL 3 2 2 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv Subgroup.topEquiv hL
  have hKm' : StatedClassicalModel ↥(K.subgroupOf (layer H)) .PSL 2 2 2 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hS.K_le).symm hKm
  intro y hy hfix
  exact hKL ↥(layer H) hEm x hx3 hxconj (K.subgroupOf (layer H)) hKm'
    (fun l hl => Subtype.ext (hKfix _ hl)) ⟨y, hy⟩ (Subtype.ext hfix)

section Main

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D : Subgroup G} {a : G}

theorem mem_oppE {U : Subgroup G} {x : G} :
    x ∈ OppE 3 (CenS U) ↔ ∃ c : ↥(CenS U), (c : G) = x ∧
      (QuotientGroup.mk c : CQ U) ∈ layer (CQ U) := by
  simp only [OppE, Subgroup.mem_map, Subgroup.mem_comap, QuotientGroup.mk'_apply,
    Subgroup.subtype_apply]
  exact ⟨fun ⟨c, hc, h⟩ => ⟨c, h, hc⟩, fun ⟨c, h, hc⟩ => ⟨c, hc, h⟩⟩

theorem mem_opp {U : Subgroup G} {x : G} :
    x ∈ Opp 3 (CenS U) ↔ ∃ c : ↥(CenS U), (c : G) = x ∧ c ∈ pPrimeCore 3 ↥(CenS U) := by
  simp only [Opp, inSubgroup, Subgroup.mem_map, Subgroup.subtype_apply]
  exact ⟨fun ⟨c, hc, h⟩ => ⟨c, h, hc⟩, fun ⟨c, h, hc⟩ => ⟨c, hc, h⟩⟩

theorem sec35_iii (hKL : FF79KL35b) (hG : IsSimpleGroup G) (hna : ∃ x y : G, x * y ≠ y * x)
    (hKp : KProper InCatalog G) (hs : FF79Sec3 b J) (h : FF79Sec34In b J B A P D)
    (hU : FF79Sec34UFacts b a J A) (hoa : orderOf a = 3)
    (hK : IsLnq 2 2 2 (Lay (J ⊓ Cen a))) (haC : a ∈ CenS (U34 b a J A))
    (hL : IsLnq 3 2 2 (⊤ : Subgroup (layer (CenS (U34 b a J A) ⧸
      pPrimeCore 3 (CenS (U34 b a J A)))))) :
    IsLnq 2 2 2 (OUpp 2 (OppE 3 (CenS (U34 b a J A)) ⊓ Cen b)) := by
  set U := U34 b a J A with hUdef
  have hd := sec34_APData hG hna hKp hs h hU hoa hK haC
  obtain ⟨L, hS⟩ := ap_struct hd
  have hKe : Nonempty (↥(Lay (J ⊓ Cen a)) ≃* alternatingGroup (Fin 5)) :=
    nonempty_equiv_alt5_of_isLnq hK
  obtain ⟨e1⟩ := hKe
  obtain ⟨e2⟩ := sec34_ap_K_a5 hU hK
  have hKm : IsLnq 2 2 2 (cqImg U (Lay (J ⊓ Cen a))) :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv (e1.trans e2.symm) hK
  have hfix := kl35b_apply hKL hd.beta3 hS hd.K_fix hKm hL
  have hKle : cqImg U (Lay (J ⊓ Cen a)) ≤ layer (CQ U) := hS.layer_eq ▸ hS.K_le
  have hQodd : Odd (Nat.card (Opp 3 (CenS U))) := sec34_odd_opp hs h hU
  haveI : (pPrimeCore 3 ↥(CenS U)).Normal := pPrimeCore_normal
  have hsimp : IsSimpleGroup ↥(Lay (J ⊓ Cen a)) := by
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
    exact e1.isSimpleGroup
  have hKeven : Even (Nat.card (Lay (J ⊓ Cen a))) := by
    rw [Nat.card_congr e1.toEquiv, nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card, Nat.factorial]
    decide
  have hKb : ∀ k ∈ Lay (J ⊓ Cen a), k ∈ Cen b := fun k hk => hU.K_cen_b hk
  set X := OppE 3 (CenS U) ⊓ Cen b with hX
  have hKX : Lay (J ⊓ Cen a) ≤ X := by
    intro k hk
    refine ⟨mem_oppE.mpr ⟨⟨k, hU.K_cen_U hk⟩, rfl, ?_⟩, hKb k hk⟩
    exact hKle (mk_mem_cqImg ⟨k, hU.K_cen_U hk⟩ hk)
  have hOpp : ∀ k ∈ Lay (J ⊓ Cen a), ∀ r ∈ Opp 3 (CenS U), k * r * k⁻¹ ∈ Opp 3 (CenS U) := by
    intro k hk r hr
    obtain ⟨q, rfl, hq⟩ := mem_opp.mp hr
    refine mem_opp.mpr ⟨⟨k, hU.K_cen_U hk⟩ * q * ⟨k, hU.K_cen_U hk⟩⁻¹, rfl, ?_⟩
    exact (inferInstance : (pPrimeCore 3 ↥(CenS U)).Normal).conj_mem q hq _
  have hRodd : Odd (Nat.card (Opp 3 (CenS U) ⊓ X : Subgroup G)) :=
    hQodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have heq := oupp_two_eq_of_split (X := X) (K := Lay (J ⊓ Cen a)) (R := Opp 3 (CenS U) ⊓ X)
    hKX inf_le_right hsimp hKeven hRodd
    (fun k hk r hr => ⟨hOpp k hk r hr.1, X.mul_mem (X.mul_mem (hKX hk) hr.2)
      (X.inv_mem (hKX hk))⟩)
    (fun r hr => by
      refine hU.K_nor r ⟨?_, hr.2.2⟩
      obtain ⟨q, hq, -⟩ := mem_opp.mp hr.1
      subst hq
      exact Subgroup.mem_centralizer_iff.mpr fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Subgroup.mem_centralizer_iff.mp q.2 x hU.a_mem)
    (fun x hx => by
      obtain ⟨c, rfl, hc⟩ := mem_oppE.mp hx.1
      have hfixy : cqβ U b hU.b_nor (QuotientGroup.mk c : CQ U) = QuotientGroup.mk c :=
        cqβ_mk_of_cen hU.b_nor c hx.2
      obtain ⟨c', hc'K, hc'eq⟩ := mem_cqImg.mp (hfix _ hc hfixy)
      refine ⟨(c' : G), hc'K, ((c'⁻¹ * c : ↥(CenS U)) : G), ⟨mem_opp.mpr ⟨c'⁻¹ * c, rfl,
        QuotientGroup.eq.mp hc'eq⟩, X.mul_mem (X.inv_mem (hKX hc'K)) hx⟩, ?_⟩
      simp)
  rw [heq]
  exact hK

end Main

end CFSG.RankThree.PartTwo.Sec21.FF79

module

public import CFSG.LocalAnalysis.StandardType.GGCellWitness
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
public import CFSG.LocalAnalysis.StandardType.GGReflectionBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification Subgroup


theorem ggAut_eq_one_of_commutator_le_primeCore {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2)
    {Y Bs L : Subgroup G} {x n : G} {t : MulAut ↥Bs} (hBsY : Bs ≤ Y) (hLY : L ≤ Y) (hnY : n ∈ Y)
    (hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a) (hexp : ∀ b ∈ Bs, b ^ p = 1)
    (hLq : CFSG.Assembly.IsQuasisimple L) (hpL : p ∣ Nat.card L)
    (hBsL : Bs ≤ normalizer (L : Set G)) (hxBs : x ∈ Bs)
    (hC : Bs ⊓ centralizer (L : Set G) = zpowers x)
    (hn : ∀ b : ↥Bs, ((t b : ↥Bs) : G) = n * b * n⁻¹)
    (hnL : ∀ l ∈ L, n * l * n⁻¹ * l⁻¹ ∈ CFSG.Open.lBalancePrimeCore p Y)
    (htx : t ⟨x, hxBs⟩ = ⟨x, hxBs⟩) (ht2 : t ^ 2 = 1) : t = 1 := by
  set O := CFSG.Open.lBalancePrimeCore p Y with hOdef
  have hOY : O ≤ Y := LBalance.primeCore_le p Y
  have hYO : Y ≤ normalizer (O : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hOY).mp (LBalance.primeCore_normal p Y)
  have hconj : ∀ g ∈ Y, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    (mem_normalizer_iff.mp (hYO hg) o).mp ho
  let T : Subgroup G :=
    { carrier := {g | g ∈ Y ∧ ∀ l ∈ L, g * l * g⁻¹ * l⁻¹ ∈ O}
      mul_mem' := by
        rintro g h ⟨hgY, hg⟩ ⟨hhY, hh⟩
        refine ⟨Y.mul_mem hgY hhY, fun l hl => ?_⟩
        have e : g * h * l * (g * h)⁻¹ * l⁻¹ =
            (g * (h * l * h⁻¹ * l⁻¹) * g⁻¹) * (g * l * g⁻¹ * l⁻¹) := by group
        rw [e]
        exact O.mul_mem (hconj g hgY _ (hh l hl)) (hg l hl)
      one_mem' := ⟨Y.one_mem, fun l _ => by simp [O.one_mem]⟩
      inv_mem' := by
        rintro g ⟨hgY, hg⟩
        refine ⟨Y.inv_mem hgY, fun l hl => ?_⟩
        have e : g⁻¹ * l * g⁻¹⁻¹ * l⁻¹ = g⁻¹ * (g * l * g⁻¹ * l⁻¹)⁻¹ * g⁻¹⁻¹ := by group
        rw [e]
        exact hconj _ (Y.inv_mem hgY) _ (O.inv_mem (hg l hl)) }
  have hcx : ∀ b ∈ Bs, n * b * n⁻¹ * b⁻¹ ∈ zpowers x := by
    intro b hb
    have hnN : n * b * n⁻¹ ∈ Bs := by
      have := hn ⟨b, hb⟩
      rw [← this]; exact (t ⟨b, hb⟩).2
    have hcB : n * b * n⁻¹ * b⁻¹ ∈ Bs := Bs.mul_mem hnN (Bs.inv_mem hb)
    have hcT : n * b * n⁻¹ * b⁻¹ ∈ T := by
      refine ⟨Y.mul_mem (Y.mul_mem (Y.mul_mem hnY (hBsY hb)) (Y.inv_mem hnY))
        (Y.inv_mem (hBsY hb)), fun l hl => ?_⟩
      have hl' : b⁻¹ * l * b⁻¹⁻¹ ∈ L := (mem_normalizer_iff.mp (hBsL (Bs.inv_mem hb)) l).mp hl
      have e : n * b * n⁻¹ * b⁻¹ * l * (n * b * n⁻¹ * b⁻¹)⁻¹ * l⁻¹ =
          (n * (b * (n⁻¹ * ((n * (b⁻¹ * l * b⁻¹⁻¹) * n⁻¹ * (b⁻¹ * l * b⁻¹⁻¹)⁻¹)⁻¹) * n⁻¹⁻¹) * b⁻¹)
            * n⁻¹) * (n * l * n⁻¹ * l⁻¹) := by group
      rw [e]
      refine O.mul_mem (hconj n hnY _ (hconj b (hBsY hb) _ (hconj _ (Y.inv_mem hnY) _
        (O.inv_mem (hnL _ hl'))))) (hnL l hl)
    have hzT : zpowers (n * b * n⁻¹ * b⁻¹) ≤ T := zpowers_le.mpr hcT
    have hcomm' : (⁅L, zpowers (n * b * n⁻¹ * b⁻¹)⁆ : Subgroup G) ≤ O := by
      refine Subgroup.commutator_le.mpr ?_
      intro l hl z hz
      have h1 := (hzT hz).2 l hl
      have e : l * z * l⁻¹ * z⁻¹ = (z * l * z⁻¹ * l⁻¹)⁻¹ := by group
      rw [commutatorElement_def, e]; exact O.inv_mem h1
    have hcent := mem_centralizer_of_commutator_le_coprime (Fact.out : p.Prime) hLq hpL
      (LBalance.primeCore_coprime p Y) (hLY.trans hYO) (hBsL hcB) hcomm'
    rw [← hC]; exact ⟨hcB, hcent⟩
  refine MulEquiv.ext fun b => Subtype.ext ?_
  set c := n * (b : G) * n⁻¹ * (b : G)⁻¹ with hcdef
  have hnN : n * (b : G) * n⁻¹ ∈ Bs := by rw [← hn b]; exact (t b).2
  have hcB : c ∈ Bs := Bs.mul_mem hnN (Bs.inv_mem b.2)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hcx b b.2)
  have hck : (⟨c, hcB⟩ : ↥Bs) = (⟨x, hxBs⟩ : ↥Bs) ^ k :=
    Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hk.symm)
  have htc : t ⟨c, hcB⟩ = ⟨c, hcB⟩ := by rw [hck, map_zpow, htx]
  have htb : t b = ⟨c, hcB⟩ * b := Subtype.ext (by rw [hn b]; simp [hcdef])
  have htt : t (t b) = b := by
    have := congrArg (fun f : MulAut ↥Bs => f b) ht2
    simpa [pow_two] using this
  rw [htb, map_mul, htc, htb] at htt
  have hc2 : c ^ 2 = 1 := by
    have h := congrArg Subtype.val htt
    simp only [Subgroup.coe_mul] at h
    have : c * c * b = 1 * b := by rw [one_mul, mul_assoc]; exact h
    rw [pow_two]; exact mul_right_cancel this
  have hcp : c ^ p = 1 := hexp c hcB
  have hgcd : Nat.gcd 2 p = 1 :=
    (Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr (Ne.symm hp2)
  have hc1 : c = 1 := by
    have := (pow_gcd_eq_one (a := c)).mpr ⟨hc2, hcp⟩
    rwa [hgcd, pow_one] at this
  rw [hn b]
  have : n * (b : G) * n⁻¹ = c * b := by rw [hcdef]; group
  rw [this, hc1, one_mul]; rfl

theorem ggFixedRealizedInL_of_config {G : Type} [Group G] [Finite G] (hL : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hInn : GGInnerDiagOn Bs L) : GGFixedRealizedInL p Bs L x := by
  rintro t hr - hxE ⟨Jt, hind, hJC, hpc⟩
  obtain ⟨hp, hBsabel, hxBs, hLx, -⟩ := hcfg.tableB_facts
  obtain ⟨hI, hBsB, hDJ⟩ := hcfg
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup G := hI.1
  have hp2 : p ≠ 2 := hI.2.2.2.2.2.1.2.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsabel.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := hBsabel.2
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hDJ
  obtain ⟨hJL, hLpc, -⟩ := eq_of_le_of_stdSub hI hDJ hpJ
  have hBsL : Bs ≤ normalizer (L : Set G) := GGDichotomy.le_normalizer_of_innerDiagOn hInn
  have hEBs : ggFixG Bs t ≤ Bs := Subgroup.map_subtype_le _
  have hT : CFSG.Open.lBalanceIsPComponent p (centralizer (ggFixG Bs t : Set G)) Jt :=
    (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p _ Jt hJC).mp hpc
  have hKx : CFSG.Open.lBalanceIsKGroup ↥(centralizer ({x} : Set G)) :=
    lBalanceIsKGroup_of_kProper hI.2.2.1
      (centralizer_singleton_ne_top_of_isSimpleGroup hI.2.1 hx1)
  obtain ⟨n, hnJt, hnN, hn⟩ := hind
  rcases GGDichotomy.dichotomy_core hL hp hcomm hexp hEBs hxE hKx hBsL
      ((largeEvenPComponent_iff_lBalance p _ L).1 hLpc).2 hT with h | h
  · exact Subgroup.subset_closure ⟨n, h hnJt, hnN, hn⟩
  · exfalso
    refine hr.ne_one hp ?_
    have hLC : IsComponentOf L (centralizer ({x} : Set G)) := hS.2.2.2.1
    have hBsY : Bs ≤ centralizer ({x} : Set G) := fun b hb =>
      mem_centralizer_singleton_iff.mpr (hcomm b hb x hxBs)
    have hEY : centralizer (ggFixG Bs t : Set G) ≤ centralizer ({x} : Set G) :=
      centralizer_le (Set.singleton_subset_iff.mpr hxE)
    obtain ⟨y, hy, hyx⟩ := hxE
    have hyx' : y = ⟨x, hxBs⟩ := Subtype.ext hyx
    subst hyx'
    exact ggAut_eq_one_of_commutator_le_primeCore hp2 hBsY hLx (hEY (hJC hnJt)) hcomm hexp
      hLC.2.2 (hpJ.trans (Subgroup.card_dvd_of_le hJL)) hBsL hxBs
      (GGConfig.bstar_inf_centralizer_L ⟨hI, hBsB, hDJ⟩) hn
      (fun l hl => h (Subgroup.commutator_mem_commutator hnJt hl)) (mem_ggFix.mp hy) hr.1


end CFSG.StandardType

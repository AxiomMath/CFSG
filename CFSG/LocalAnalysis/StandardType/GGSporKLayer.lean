module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMPreds
import CFSG.Assembly.Subnormal
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

private theorem gk5_fittingSubgroup_le_pCore_sup_pPrimeCore {G : Type*} [Group G] [Finite G]
    (p : ℕ) :
    CFSG.fittingSubgroup G ≤ CFSG.pCore p G ⊔ CFSG.pPrimeCore p G := by
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun q => ?_
  have hqprime : Nat.Prime (q : ℕ) := Nat.prime_of_mem_primeFactors q.2
  by_cases hqp : (q : ℕ) = p
  · rw [hqp]
    exact le_sup_left
  · by_cases hdvd : (q : ℕ) ∣ p
    · have hpgroup : IsPGroup p (CFSG.pCore (q : ℕ) G) :=
        (CFSG.pCore_isPGroup (p := (q : ℕ)) (G := G)).mono hdvd
      have hle : CFSG.pCore (q : ℕ) G ≤ CFSG.pCore p G :=
        le_sSup (show CFSG.pCore (q : ℕ) G ∈
          {K : Subgroup G | K.Normal ∧ IsPGroup p K} from
            ⟨CFSG.pCore_normal, hpgroup⟩)
      exact hle.trans le_sup_left
    · haveI : Fact (Nat.Prime (q : ℕ)) := ⟨hqprime⟩
      have hcop : Nat.Coprime p (Nat.card (CFSG.pCore (q : ℕ) G)) := by
        obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := (q : ℕ)) (G := G)).exists_card_eq
        rw [hn]
        exact Nat.Prime.coprime_pow_of_not_dvd hqprime hdvd
      have hle : CFSG.pCore (q : ℕ) G ≤ CFSG.pPrimeCore p G :=
        le_sSup (show CFSG.pCore (q : ℕ) G ∈
          {K : Subgroup G | K.Normal ∧ Nat.Coprime p (Nat.card K)} from
            ⟨CFSG.pCore_normal, hcop⟩)
      exact hle.trans le_sup_right

private theorem gk5_fittingSubgroup_eq_bot_of_pCore_eq_bot {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hP' : CFSG.pPrimeCore p G = ⊥) (hP : CFSG.pCore p G = ⊥) :
    CFSG.fittingSubgroup G = ⊥ := by
  have hle := gk5_fittingSubgroup_le_pCore_sup_pPrimeCore (G := G) p
  rw [hP, hP', sup_bot_eq] at hle
  exact le_bot_iff.mp hle

theorem ggSporK_components_simple {W : Type} [Group W] [Finite W] {p : ℕ} {H : Subgroup W}
    (hP' : LargeEvenPPrimeCore p ↥H = ⊥) (hP : CFSG.pCore p ↥H = ⊥) {J : Subgroup W}
    (hJ : IsComponentOf J H) : IsSimpleGroup ↥J ∧ ∃ a b : ↥J, a * b ≠ b * a := by
  have hF : CFSG.fittingSubgroup ↥H = ⊥ :=
    gk5_fittingSubgroup_eq_bot_of_pCore_eq_bot (G := ↥H) (p := p)
      (show CFSG.pPrimeCore p ↥H = ⊥ from hP') hP
  let K : Subgroup ↥H := J.subgroupOf H
  have hsub : CFSG.Assembly.IsSubnormal K ⊤ :=
    CFSG.Assembly.IsSubnormal.of_mathlib
      ((CFSG.Assembly.IsSubnormal.iff_subgroupOf hJ.1).mp hJ.2.1)
  have hqs : CFSG.Assembly.IsQuasisimple ↥K :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ.1) hJ.2.2
  have hKcomp : CFSG.Assembly.IsComponentOf K ⊤ := ⟨le_top, hsub, hqs⟩
  have hK : CFSG.IsComponent K :=
    (CFSG.isComponent_iff_open K).mpr (CFSG.Assembly.isComponentOf_iff_open.mp hKcomp)
  have hZbot : (Subgroup.center ↥K).map K.subtype = ⊥ := by
    have hle := CFSG.LocalCores.center_component_le_center_layer hK
    have hle' : (Subgroup.center ↥K).map K.subtype ≤ CFSG.fittingSubgroup ↥H :=
      hle.trans CFSG.WholeGroup.center_layer_le_fittingSubgroup
    rw [hF] at hle'
    exact le_bot_iff.mp hle'
  have hZK : Subgroup.center ↥K = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥K) K.subtype_injective).mp hZbot
  have hcenterJ : Subgroup.center ↥J = ⊥ := by
    have hmap := Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hJ.1)
    rw [hZK, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hsimpleJ : IsSimpleGroup ↥J := by
    have hq : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
    have hq2 : IsSimpleGroup (↥J ⧸ (⊥ : Subgroup ↥J)) :=
      (QuotientGroup.quotientMulEquivOfEq hcenterJ).isSimpleGroup_congr.mp hq
    exact (QuotientGroup.quotientBot.isSimpleGroup_congr).mp hq2
  refine ⟨hsimpleJ, ?_⟩
  by_contra hcon
  have hcomm : ∀ a b : ↥J, a * b = b * a := by
    intro a b
    by_contra hab
    exact hcon ⟨a, b, hab⟩
  haveI : IsMulCommutative ↥J := IsMulCommutative.of_comm hcomm
  have hbot : commutator ↥J = ⊥ := commutator_eq_bot ↥J
  rw [hJ.2.2.1] at hbot
  obtain ⟨a, b, hab⟩ := hsimpleJ.toNontrivial.exists_pair_ne
  have ha : a = 1 := by
    have : a ∈ (⊥ : Subgroup ↥J) := by rw [← hbot]; exact Subgroup.mem_top a
    exact Subgroup.mem_bot.mp this
  have hb : b = 1 := by
    have : b ∈ (⊥ : Subgroup ↥J) := by rw [← hbot]; exact Subgroup.mem_top b
    exact Subgroup.mem_bot.mp this
  exact hab (ha.trans hb.symm)

theorem ggSporK_eq_one_of_centralizes_components {W : Type} [Group W] [Finite W] {p : ℕ}
    {H : Subgroup W} (hP' : LargeEvenPPrimeCore p ↥H = ⊥) (hP : CFSG.pCore p ↥H = ⊥) {h : W}
    (hH : h ∈ H) (hc : ∀ J : Subgroup W, IsComponentOf J H → ∀ x ∈ J, h * x = x * h) : h = 1 := by
  let hg : ↥H := ⟨h, hH⟩
  have hF : CFSG.fittingSubgroup ↥H = ⊥ :=
    gk5_fittingSubgroup_eq_bot_of_pCore_eq_bot (G := ↥H) (p := p)
      (show CFSG.pPrimeCore p ↥H = ⊥ from hP') hP
  have hgen : CFSG.generalizedFitting ↥H = CFSG.layer ↥H := by
    rw [CFSG.generalizedFitting.eq_sup, hF, bot_sup_eq]
  have hleLayer : CFSG.layer ↥H ≤ Subgroup.centralizer ({hg} : Set ↥H) := by
    rw [CFSG.layer.eq_sSup]
    refine sSup_le fun K hK => ?_
    intro x hxK
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hJcomp : IsComponentOf (K.map H.subtype) H := by
      refine ⟨Subgroup.map_subtype_le K, ?_, ?_⟩
      · have hsub : CFSG.Assembly.IsSubnormal K ⊤ :=
          CFSG.Assembly.IsSubnormal.of_mathlib hK.2
        have hmap := hsub.map H.subtype
        rwa [Subgroup.map_top, Subgroup.range_subtype] at hmap
      · have hqK : CFSG.Assembly.IsQuasisimple ↥K :=
          ⟨hK.1.1.commutator_eq_top, hK.1.2.1⟩
        exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
          (K.equivMapOfInjective H.subtype H.subtype_injective).symm hqK
    have hcommW : h * (x : W) = (x : W) * h :=
      hc (K.map H.subtype) hJcomp (x : W) (Subgroup.mem_map_of_mem H.subtype hxK)
    apply Subtype.ext
    simpa using hcommW.symm
  have hcenLayer : hg ∈ Subgroup.centralizer (CFSG.layer ↥H : Set ↥H) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hleLayer hy)
  have hcenGen : hg ∈ Subgroup.centralizer (CFSG.generalizedFitting ↥H : Set ↥H) := by
    rw [hgen]
    exact hcenLayer
  have hgGen : hg ∈ CFSG.generalizedFitting ↥H :=
    CFSG.centralizer_generalizedFitting_le ↥H hcenGen
  have hgLayer : hg ∈ CFSG.layer ↥H := by
    rw [← hgen]
    exact hgGen
  have hgCenter : (⟨hg, hgLayer⟩ : ↥(CFSG.layer ↥H)) ∈ Subgroup.center ↥(CFSG.layer ↥H) := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcenLayer (z : ↥H) z.2)
  have hgBot : hg ∈ (⊥ : Subgroup ↥H) := by
    have hmem : hg ∈ (Subgroup.center ↥(CFSG.layer ↥H)).map (CFSG.layer ↥H).subtype :=
      ⟨⟨hg, hgLayer⟩, hgCenter, rfl⟩
    have hle := CFSG.WholeGroup.center_layer_le_fittingSubgroup (G := ↥H) hmem
    rwa [hF] at hle
  have hg1 : hg = 1 := Subgroup.mem_bot.mp hgBot
  simpa [hg] using hg1

end CFSG.StandardType.SporadicShape

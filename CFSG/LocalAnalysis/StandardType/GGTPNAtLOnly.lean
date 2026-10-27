module

public import CFSG.LocalAnalysis.StandardType.GGTPNPCompDefs
import CFSG.LocalAnalysis.StandardType.GGTPNTrOnlyPComp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {y : G}

theorem ggTPNOnlyComp_atL (hQ : GGPCompCentQuasisimple fun _ => True)
    (hc : GGConfig p B Bs x L D J) (hL : GGInnerDiagOn Bs L) (hpJ : p ∣ Nat.card J)
    (hD : D = Subgroup.closure {x, y}) (hy : y ∈ Subgroup.normalizer (L : Set G)) :
    GGTPNOnlyComp p (L.normalizerMonoidHom ⟨y, hy⟩) (J.subgroupOf L) := by
  have hp : p.Prime := hc.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hc.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hSstar : LargeEvenSStar p B x L := hc.1.2.2.2.2.2.2.1
  have hDJ : LargeEvenStdSubPre p B x L D J := hc.2.2.1
  have hx1 : x ≠ 1 := hSstar.2.2.1
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := hSstar.2.2.2.1.1
  have hxp : x ^ p = 1 := hSstar.1.1.2 x hSstar.2.1
  have hcardD : Nat.card D = p ^ 2 := hDJ.2.2.1
  have hxD : x ∈ D := hDJ.2.2.2.1
  have hJeq : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) := hDJ.2.2.2.2.1
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hDJ.2.2.2.2.2.1
  have hCD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hD, Subgroup.centralizer_closure]
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  have hyNotZp : y ∉ Subgroup.zpowers x := by
    intro hy
    have hDle : D ≤ Subgroup.zpowers x := by
      rw [hD]
      rw [Subgroup.closure_le]
      intro z hz
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hzx | hzy
      · rw [hzx]; exact Subgroup.mem_zpowers x
      · rw [hzy]; exact hy
    have hxcard : Nat.card (Subgroup.zpowers x) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
    have hle : p ^ 2 ≤ p := by
      rw [← hcardD]
      exact (Subgroup.card_le_of_le hDle).trans_eq hxcard
    have hle' : p * p ≤ p := by rwa [Nat.pow_two] at hle
    have hmul : p * p ≤ p * 1 := by simpa using hle'
    have hp1 : p ≤ 1 := Nat.le_of_mul_le_mul_left hmul hp.pos
    have h2p : 2 ≤ p := hp.two_le
    omega
  have hyD : y ∈ D := hD ▸ Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hyB : y ∈ B := hDJ.1 hyD
  have hyBs : y ∈ Bs := hc.2.1.1 hyB
  have hNB : Bs ≤ Subgroup.normalizer (L : Set G) := ggInnerDiagOn_le_normalizer hL
  let E : Subgroup (MulAut ↥L) := ggAutsOf L Bs hNB
  let ybar : MulAut ↥L := L.normalizerMonoidHom ⟨y, hy⟩
  change GGTPNOnlyComp p ybar (J.subgroupOf L)
  have hybarE : ybar ∈ E := by
    change L.normalizerMonoidHom ⟨y, hy⟩ ∈ ggAutsOf L Bs hNB
    exact (mem_ggAutsOf hNB).2 ⟨y, hyBs, rfl⟩
  have hCBL : B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_sstar hp hSstar
  have hybar_ne : ybar ≠ 1 := by
    intro h1
    have hyC : y ∈ Subgroup.centralizer (L : Set G) :=
      (normalizerMonoidHom_eq_one_iff hy).1 h1
    have hmem : y ∈ B ⊓ Subgroup.centralizer (L : Set G) := ⟨hyB, hyC⟩
    rw [hCBL] at hmem
    exact hyNotZp hmem
  have hy1 : y ≠ 1 := fun h => hyNotZp (h.symm ▸ Subgroup.one_mem (Subgroup.zpowers x))
  have horder_y : orderOf y = p :=
    orderOf_eq_prime (hSstar.1.1.2 y hyB) hy1
  have hord : orderOf ybar = p := by
    have hdvd : orderOf ybar ∣ p := by
      have h1 : orderOf (L.normalizerMonoidHom ⟨y, hy⟩) ∣
          orderOf (⟨y, hy⟩ : ↥(Subgroup.normalizer (L : Set G))) := orderOf_map_dvd _ _
      rw [Subgroup.orderOf_mk, horder_y] at h1
      exact h1
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hybar_ne
    · exact h1
  have hmark' : LargeEvenMarking ↥L fun _ _ _ I _ θ => GGInducedInn E θ I :=
    largeEvenMarking_mono (fun _ _ _ I _ θ h => ggInducedInn_of_clause3 h.1 θ h.2) hL
  obtain ⟨lab, hlab, hhas, R, _instR, I, F, θ, _hP⟩ := largeEvenMarking_exists_hasLabel hL
  intro J' hJ
  have hquasi : CFSG.IsQuasisimple ↥J' :=
    hQ p hp hp2 ↥L E ybar lab hlab trivial hhas hybarE hord hmark' J' hJ
  let S : Subgroup G := J'.map L.subtype
  have hSleL : S ≤ L := Subgroup.map_subtype_le J'
  have hSsub : S.subgroupOf L = J' := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSleL]
  let K : Subgroup G := L ⊓ Subgroup.centralizer (D : Set G)
  have hKleL : K ≤ L := inf_le_left
  have hHeq : K = L ⊓ Subgroup.centralizer ({y} : Set G) := by
    change L ⊓ Subgroup.centralizer (D : Set G) = _
    rw [hCD, ← inf_assoc, inf_eq_left.mpr hxL]
  have hfix : ggAutFixedSubgroup ybar = K.subgroupOf L := by
    have h1 := ggAutFixedSubgroup_normalizerMonoidHom hy
    rw [h1]
    exact congrArg (fun H : Subgroup G => H.subgroupOf L) hHeq.symm
  have hScompFixedK : LargeEvenPComponent p (K.subgroupOf L) (S.subgroupOf L) := by
    rw [← hfix, hSsub]
    exact hJ
  have hScompFixedK' := (ggLargeEvenPComponent_iff p (K.subgroupOf L) (S.subgroupOf L)).1
    hScompFixedK
  have hSpcInside : CFSG.IsPComponent p ((S.subgroupOf L).subgroupOf (K.subgroupOf L)) :=
    hScompFixedK'.2
  have hSpcK : CFSG.IsPComponent p (S.subgroupOf K) :=
    (CFSG.ComponentClassification.UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (X := L) (Y := K) (L := S) hKleL p hp).1 hSpcInside
  have hSleK : S ≤ K := by
    intro s hs
    have hx : (⟨s, hSleL hs⟩ : ↥L) ∈ S.subgroupOf L := hs
    exact hScompFixedK'.1 hx
  rw [← hSsub] at hquasi
  have hquasiS : CFSG.IsQuasisimple ↥S :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSleL).symm hquasi
  have hSdata := (ggPComponent_iff_data p hSleK).1 hSpcK
  have hSsubK : IsSubnormal S K := hSdata.1
  have hScompK : IsComponentOf S K :=
    ⟨hSleK, hSsubK, ⟨Group.isPerfect_def.mp hquasiS.1, hquasiS.2.1⟩⟩
  have hJeqK : J = LargeEvenLayer K := hJeq
  have hJcompK : IsComponentOf J K := hJcomp
  have hSleJ : S ≤ J := by
    have hle : S ≤ LargeEvenLayer K := le_sSup hScompK
    rwa [← hJeqK] at hle
  have hJnotO : ¬ J ≤ CFSG.Open.lBalancePrimeCore p K :=
    not_le_lBalancePrimeCore_of_dvd hpJ
  have hSpK : CFSG.Open.lBalanceIsPComponent p K S :=
    (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance
      p K S hSleK).1 hSpcK
  rcases lBalanceIsPComponent_eq_or_commute hJcompK hJnotO hSpK with hEq | hComm
  · calc J' = S.subgroupOf L := hSsub.symm
      _ = J.subgroupOf L := by rw [hEq]
  · exfalso
    have hSS : ⁅S, S⁆ = ⊥ := by
      have h1 : ⁅S, S⁆ ≤ ⁅S, J⁆ := Subgroup.commutator_mono le_rfl hSleJ
      rw [hComm] at h1
      exact le_bot_iff.mp h1
    have hqAsm : CFSG.Assembly.IsQuasisimple ↥S :=
      ⟨Group.isPerfect_def.mp hquasiS.1, hquasiS.2.1⟩
    have hSperf : ⁅S, S⁆ = S := commutator_self_eq_of_isQuasisimple hqAsm
    have hSbot : S = ⊥ := by rw [← hSperf, hSS]
    have hsub : Subsingleton (↥S ⧸ Subgroup.center ↥S) := by
      rw [hSbot]
      infer_instance
    have hnt : Nontrivial (↥S ⧸ Subgroup.center ↥S) := hquasiS.2.1.toNontrivial
    exact (not_subsingleton_iff_nontrivial (α := ↥S ⧸ Subgroup.center ↥S)).mpr hnt hsub

end CFSG.StandardType

end

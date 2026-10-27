module

public import CFSG.Quasithin.EmptyFaithful.SzN17Aut
public import CFSG.Quasithin.EmptyFaithful.S153LList3
public import CFSG.Quasithin.EmptyFaithful.SzN17Abs

public section

namespace CFSG.Quasithin.SzN17

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped commutatorElement IsMulCommutative

theorem quasisimple_of_mem_cComp {V : Type} [CommGroup V] [Finite V] (h56 : AsB56)
    (hV : ∀ v : V, v ^ 2 = 1) {Js : Subgroup (MulAut V)} (hJne : Js ≠ ⊥) (hB53 : B53Hyp Js)
    {K : Subgroup (MulAut V)} (hK : K ∈ cComp Js) :
    CFSG.IsQuasisimple ↥K ∧ B56QuasisimpleList ↥K := by
  have hcases := h56 V hV Js hJne hB53
  have hKne : K ≠ ⊥ := ne_bot_of_mem_cComp hK
  have hKJ : K ≤ Js := le_of_mem_cComp hK
  have hK0 : K ≤ perfectCore Js := le_perfectCore_of_perfect hKJ (perfect_of_mem_cComp hK)
  rcases S153L.b56_components hcases with ⟨h6, -⟩ | ⟨G₁, G₂, hsup, hinf, hc, ⟨h1, -⟩, ⟨h2, -⟩⟩ |
      ⟨N₁, N₂, -, -, -, -, -, hq₁, hq₂, hall⟩
  · exfalso
    have hsolv : Group.IsSolvable ↥Js := S153L.comp_solvable_of_card_six h6
    have h0 : perfectCore Js = ⊥ := (isSolvable_iff_perfectCore_eq_bot Js).1 hsolv
    exact hKne (le_bot_iff.1 (h0 ▸ hK0))
  · exfalso
    have hs₁ : perfectCore G₁ = ⊥ :=
      (isSolvable_iff_perfectCore_eq_bot G₁).1 (S153L.comp_solvable_of_card_six h1)
    have hs₂ : perfectCore G₂ = ⊥ :=
      (isSolvable_iff_perfectCore_eq_bot G₂).1 (S153L.comp_solvable_of_card_six h2)
    have hle := S153L.comp_perfectCore_sup_le hc
    rw [hsup, hs₁, hs₂, sup_bot_eq] at hle
    exact hKne (le_bot_iff.1 (hK0.trans hle))
  · rcases hall K hK with rfl | rfl
    · rcases hq₁ with h | h
      · exact absurd h hKne
      · exact h
    · rcases hq₂ with h | h
      · exact absurd h hKne
      · exact h

section Setting

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I : Subgroup G} {t : G}

theorem isTwoReduced_UI' (hh : Hyp15310 G T Mc M V₁ V₂ Yp t) (hc : CharTwo I)
    (hF : Facts153 T M V₁ Yp I) :
    IsElemAbelian 2 (UI153 T I) ∧ IsTwoReducedIn I (UI153 T I) := by
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hZ := SBc3.omegaOneCenter_le_Sgp153 hh
  exact ⟨(conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 hc hZ).2,
    isTwoReducedIn_conjClosure_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 hc hZ⟩

omit [Finite G] in
theorem card_autOn_dvd {U L : Subgroup G} (hLN : L ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card ↥(autOn L U) ∣ Nat.card ↥L := by
  have h1 : Nat.card ↥(autOn L U) ∣
      Nat.card ↥(L.subgroupOf (Subgroup.normalizer (U : Set G))) := by
    unfold autOn
    exact Subgroup.card_dvd_of_surjective
      (MonoidHom.subgroupMap_surjective (conjAct U) (L.subgroupOf (Subgroup.normalizer (U : Set G))))
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv] at h1

theorem one_le_pRank_three_of_dvd {L : Subgroup G} (h3 : 3 ∣ Nat.card ↥L) :
    1 ≤ CFSG.Open.pRank 3 L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3
  have hxo : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hE : IsElemAbelian 3 (Subgroup.zpowers (x : G)) := by
    refine ⟨inferInstance, fun e he => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    have : (x : G) ^ 3 = 1 := hxo ▸ pow_orderOf_eq_one _
    rw [this, one_zpow]
  have hEcard : Nat.card (Subgroup.zpowers (x : G)) = 3 ^ 1 := by
    rw [Nat.card_zpowers, hxo]; norm_num
  exact le_pRank Nat.prime_three (Subgroup.zpowers_le.2 x.2) hE hEcard

theorem exists_cComp_not_le (h56 : AsB56) (h39 : A39ForSQTK)
    (hh : Hyp15310 G T Mc M V₁ V₂ Yp t) (hI : IsHPlus Yp (Sgp153 T V₁) M I) (hc : CharTwo I)
    (hF : Facts153 T M V₁ Yp I) :
    ∃ L : Subgroup G, L ∈ cComp (thompsonJ I) ∧ ¬ L ≤ M ⊓ I ∧ 1 ≤ CFSG.Open.pRank 3 L ∧
      CFSG.IsQuasisimple ↥(autOn L (UI153 T I)) ∧ B56QuasisimpleList ↥(autOn L (UI153 T I)) := by
  obtain ⟨hWe, hred⟩ := isTwoReduced_UI' hh hc hF
  have : IsMulCommutative ↥(UI153 T I) := hWe.1
  have hUN : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hSQ : SQTKGroup ↥I :=
    sqtkGroup_of_pCoreOf_ne_bot hh.hyp.qtfe.qtke hh.hyp.qtfe.simple hh.hyp.qtfe.nonabelian hI.1.2
  have hO2 : pCoreOf 2 (autOn I (UI153 T I)) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hJI : thompsonJ I ≤ I := thompsonJ_le_self I
  have hIJn : I ≤ Subgroup.normalizer ((thompsonJ I : Subgroup G) : Set G) := fun g hg =>
    GammaExtra.normalizer_le_normalizer_thompsonJ I (Subgroup.le_normalizer hg)
  have hJn : ∀ h ∈ autOn I (UI153 T I), ∀ j ∈ autOn (thompsonJ I) (UI153 T I),
      h * j * h⁻¹ ∈ autOn (thompsonJ I) (UI153 T I) := InternalSec.autOn_normal_of hIJn
  have hJH : autOn (thompsonJ I) (UI153 T I) ≤ autOn I (UI153 T I) :=
    InternalSec.autOn_le_autOn_of_le hJI
  have hJnorm : ((autOn (thompsonJ I) (UI153 T I)).subgroupOf (autOn I (UI153 T I))).Normal :=
    (Subgroup.normal_subgroupOf_iff hJH).2 fun h k hh hk => hJn k hk h hh
  have hffJ : autOn (thompsonJ I) (UI153 T I) = ffJ (autOn (thompsonJ I) (UI153 T I)) :=
    le_antisymm (autOn_thompsonJ_le_ffJ_self hWe hred.1 hUN) (B6.ffJ_le _)
  have hB53 : B53Hyp (autOn (thompsonJ I) (UI153 T I)) :=
    b53Hyp_of_normal hUN hSQ hO2 hJH hJnorm hffJ
  have hYI : Yp ≤ I := le_sup_left.trans hI.1.1
  have hYH : autOn Yp (UI153 T I) ≤ autOn I (UI153 T I) := InternalSec.autOn_le_autOn_of_le hYI
  have hYgen := autOn_closure_orderThree (W := UI153 T I) (S := M ⊓ I) hF.theta (hYI.trans hUN)
  have hSyl : IsSylowTwoOf (autOn (Sgp153 T V₁) (UI153 T I)) (autOn I (UI153 T I)) :=
    Setup.isSylowTwoOf_autOn hF.sylow hUN
  have hSM : autOn (Sgp153 T V₁) (UI153 T I) ≤ autOn (M ⊓ I) (UI153 T I) :=
    InternalSec.autOn_le_autOn_of_le (le_inf (inf_le_left.trans hh.hyp.T_le) hF.sylow.1)
  have hKL : ∀ x ∈ autOn I (UI153 T I), (∀ y ∈ autOn Yp (UI153 T I), x * y = y * x) →
      x ∈ autOn (M ⊓ I) (UI153 T I) := by
    intro x hx hcomm
    have hxc : x ∈ Subgroup.centralizer ((autOn Yp (UI153 T I) : Subgroup _) : Set _) :=
      Subgroup.mem_centralizer_iff.2 fun y hy => (hcomm y hy).symm
    have h2 : x ∈ Star153 T I (M ⊓ I) := by
      rw [← hF.star_norm]
      exact ⟨Subgroup.centralizer_le_normalizer _ hxc, hx⟩
    exact h2
  have hV : ∀ v : ↥(UI153 T I), v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hWe.2 v v.2)
  have hperf := not_perfectCore_le_of_not_le h56 hV hJH hJn hB53 hYH hYgen hSyl hSM hKL hF.J_not_le
  have hJne : autOn (thompsonJ I) (UI153 T I) ≠ ⊥ := fun h =>
    hF.J_not_le (by rw [show Star153 T I (thompsonJ I) = ⊥ from h]; exact bot_le)
  have hSQJ : SQTKGroup ↥(thompsonJ I) := B5.sqtk_of_le hSQ hJI
  have hspan : cCompSpan (thompsonJ I) = perfectCore (thompsonJ I) :=
    cCompSpan_eq_perfectCore_of_subgroup _ (h39 _ (SQTKHyp.of_sqtkGroup ↥(thompsonJ I) hSQJ)).1
  have hex : ∃ L ∈ cComp (thompsonJ I), ¬ L ≤ M ⊓ I := by
    by_contra hall
    push Not at hall
    apply hperf
    have hspanle : perfectCore (thompsonJ I) ≤ M ⊓ I := by
      rw [← hspan]
      exact sSup_le fun L hL => hall L hL
    intro φ hφ
    have hmap : perfectCore (autOn (thompsonJ I) (UI153 T I)) =
        (perfectCore ((thompsonJ I).subgroupOf (Subgroup.normalizer (UI153 T I : Set G)))).map
          (conjAct (UI153 T I)) := by
      unfold autOn
      exact (map_perfectCore (conjAct (UI153 T I)) _).symm
    rw [hmap] at hφ
    obtain ⟨x, hx, rfl⟩ := hφ
    have hxJ : (x : G) ∈ perfectCore (thompsonJ I) := by
      have h1 := map_perfectCore (Subgroup.normalizer (UI153 T I : Set G)).subtype
        ((thompsonJ I).subgroupOf (Subgroup.normalizer (UI153 T I : Set G)))
      rw [Subgroup.map_subgroupOf_eq_of_le (hJI.trans hUN)] at h1
      rw [← h1]
      exact ⟨x, hx, rfl⟩
    exact Setup.mem_autOn_iff.2 ⟨x, hspanle hxJ, rfl⟩
  obtain ⟨L, hL, hLn⟩ := hex
  have hLI : L ≤ I := (le_of_mem_cComp hL).trans hJI
  have hLN : L ≤ Subgroup.normalizer (UI153 T I : Set G) := hLI.trans hUN
  have hne : autOn L (UI153 T I) ≠ ⊥ := by
    intro h
    exact hLn (S153D.le_of_autOn_le hUN hLI inf_le_right hF.cent_le (by rw [h]; exact bot_le))
  have hK : autOn L (UI153 T I) ∈ cComp (autOn (thompsonJ I) (UI153 T I)) :=
    autOn_mem_cComp (hJI.trans hUN) hL hne
  obtain ⟨hq, hlist⟩ := quasisimple_of_mem_cComp h56 hV hJne hB53 hK
  have h3 : 3 ∣ Nat.card ↥(autOn L (UI153 T I)) := S153L.three_dvd_card_of_b56QL hlist hq
  have h3L : 3 ∣ Nat.card ↥L := h3.trans (card_autOn_dvd hLN)
  exact ⟨L, hL, hLn, one_le_pRank_three_of_dvd h3L, hq, hlist⟩

end Setting

end CFSG.Quasithin.SzN17

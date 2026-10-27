module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SevenS4
public import CFSG.GroupTheory.CardMapInfKer
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.Quasithin.Background.HTriPermute
import CFSG.RankThree.PartTwo.Sec14.Ronan134SupQ
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rB
import CFSG.Quasithin.Recognition.GoldschmidtFan86ModelCore
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMax
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenOuter
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem map_conj_ne_of_mem_calC {D : Data G} {L : Subgroup G} {X : Subgroup G} {t : G}
    (hL : L ∈ calC D.M) (h7 : IsL2Over17 (Bar2 L) 7) (htM : t ∈ D.M)
    (hLt : L.map (MulAut.conj t).toMonoidHom ≠ L)
    (hXL : X ≤ L) (hXcard : Nat.card X = 3) :
    X.map (MulAut.conj t).toMonoidHom ≠ X := by
  classical
  intro hXt
  set Lt : Subgroup G := L.map (MulAut.conj t).toMonoidHom with hLtdef
  have hMt : D.M.map (MulAut.conj t).toMonoidHom = D.M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htM)
  have hLt_mem : Lt ∈ calC D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map D.M (MulAut.conj t) hMt hL
  have h7t : IsL2Over17 (Bar2 Lt) 7 := by
    obtain ⟨r, f, hr, hr2, hq, hf, hlie⟩ := h7
    exact ⟨r, f, hr, hr2, hq, hf, CFSG.Blueprint.LieModel.of_mulEquiv
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.bar2Equiv
        (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom
          (MulAut.conj t).injective)) hlie⟩
  have hZ : Subgroup.center (Bar2 L) = ⊥ :=
    center_eq_bot_of_isL3 (isL3_one_of_isL2Over17_seven h7)
  have hZt : Subgroup.center (Bar2 Lt) = ⊥ :=
    center_eq_bot_of_isL3 (isL3_one_of_isL2Over17_seven h7t)
  have hle : X ≤ pCoreOf 2 L := by
    have hXinf : X ≤ L ⊓ Lt := by
      refine le_inf hXL ?_
      rw [← hXt]
      exact Subgroup.map_mono hXL
    exact fun x hx => (calC_inf_le_pCore_of_ne hL hLt_mem hLt.symm hZ hZt (hXinf hx)).1
  have hdvd : 3 ∣ Nat.card ↥(pCoreOf 2 L) := by
    rw [← hXcard]
    exact Subgroup.card_dvd_of_le hle
  have h3 : ¬ 3 ∣ Nat.card ↥(pCoreOf 2 L) := by
    rw [CFSG.Quasithin.Fan86.Model.card_pCoreOf]
    exact CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two Nat.prime_three
      (by norm_num)
  exact h3 hdvd

theorem ntl17_le_sup_pCoreOf {D : Data G} {L : Subgroup G} {r q : ℕ}
    {V₀ V : Subgroup G} (hC : Ctx17_6 D V₀ V L r q)
    (h7 : IsL2Over17 (Bar2 L) 7) (h7S : IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7) :
    NTL17 D L ≤ (D.T ⊓ L) ⊔ pCoreOf 2 (L ⊔ NTL17 D L) := by
  classical
  set S : Subgroup G := NTL17 D L with hS
  set N : Subgroup G := L ⊔ S with hN
  have hLN : L ≤ N := le_sup_left
  have hSN : S ≤ N := le_sup_right
  have hSNL : S ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hST : S ≤ D.T := inf_le_left
  have hLM : L ≤ D.M := hC.memL.1.le
  have hS0 : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ L) L :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal
      (CFSG.QuasithinUnique.Setup.Lift.isSylowTwoOf_of_isSylowOf D.sylowM) hLM
      ((CFSG.Quasithin.isSubnormal_iff_subgroupOf hLM).mp hC.memL.1)
  have hLnormal : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr
      (sup_le Subgroup.le_normalizer hSNL)
  have hsimple : IsSimpleGroup (Bar2 N) := by
    obtain ⟨p, f, hp, hp2, hq, hf, hlie⟩ := h7S
    exact CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hlie
  let πN : ↥N →* Bar2 N := QuotientGroup.mk' (CFSG.pCore 2 ↥N)
  let K : Subgroup (Bar2 N) := (L.subgroupOf N).map πN
  have hKnormal : K.Normal :=
    Subgroup.Normal.map hLnormal πN (QuotientGroup.mk'_surjective _)
  have hKtop : K = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top K with h | h
    · exfalso
      have hLbot : L ≤ pCoreOf 2 N := by
        intro l hl
        have hmem : (QuotientGroup.mk ⟨l, hLN hl⟩ : Bar2 N) = 1 := by
          have h2 : (QuotientGroup.mk ⟨l, hLN hl⟩ : Bar2 N) ∈ K :=
            Subgroup.mem_map_of_mem πN (Subgroup.mem_subgroupOf.mpr hl)
          rw [h] at h2
          exact Subgroup.mem_bot.mp h2
        exact (CFSG.mem_openPCoreOf_iff (⟨l, hLN hl⟩ : ↥N)).mpr
          ((QuotientGroup.eq_one_iff (⟨l, hLN hl⟩ : ↥N)).mp hmem)
      have hL2 : IsPGroup 2 ↥L :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le hLbot
      have hbar : IsPGroup 2 (Bar2 L) :=
        IsPGroup.of_surjective hL2 (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
          (QuotientGroup.mk'_surjective _)
      have hcard : Nat.card (Bar2 L) = 168 :=
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.card_of_isL2Odd_seven
          (isL2Odd_seven_of_isL2Over17_seven h7)
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hbar
      have h3 : 3 ∣ Nat.card (Bar2 L) := by rw [hcard]; norm_num
      rw [hn] at h3
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
    · exact h
  have hS2 : IsPGroup 2 S := (D.sylowM.isPGroup).to_le inf_le_left
  have hS_sylN : CFSG.QuasithinUnique.IsSylowTwoOf S N := by
    refine ⟨hSN, hS2, ?_⟩
    show ¬ 2 ∣ (S.subgroupOf N).index
    rw [show (S.subgroupOf N).index = S.relIndex N from rfl]
    change ¬ 2 ∣ S.relIndex (L ⊔ S)
    rw [show L ⊔ S = S ⊔ L from sup_comm L S,
      (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hSNL).1]
    have hLS : S ⊓ L = D.T ⊓ L := by
      ext x
      constructor
      · rintro ⟨hxS, hxL⟩
        exact ⟨hxS.1, hxL⟩
      · rintro ⟨hxT, hxL⟩
        exact ⟨Subgroup.mem_inf.mpr ⟨hxT, Subgroup.le_normalizer hxL⟩, hxL⟩
    rw [hLS]
    exact hS0.2.2
  have hpT : pCoreOf 2 N ≤ D.T :=
    (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hS_sylN).trans hST
  intro s hs
  have hsN : s ∈ N := Subgroup.mem_sup_right hs
  have hmemK : πN ⟨s, hsN⟩ ∈ K := by rw [hKtop]; exact Subgroup.mem_top _
  obtain ⟨l, hl, hlq⟩ := Subgroup.mem_map.mp hmemK
  have hmemO : ((l : N)⁻¹ * ⟨s, hsN⟩ : ↥N) ∈ CFSG.pCore 2 ↥N := by
    rw [← QuotientGroup.eq_one_iff]
    show πN ((l : N)⁻¹ * ⟨s, hsN⟩) = 1
    rw [map_mul, map_inv, hlq, inv_mul_cancel]
  have hs_eq : s = (l : G) * ((((l : N)⁻¹ * ⟨s, hsN⟩ : ↥N)) : G) := by
    have h1 : (⟨s, hsN⟩ : ↥N) = (l : N) * ((l : N)⁻¹ * ⟨s, hsN⟩) := by group
    exact congrArg Subtype.val h1
  have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
  have hzO : (((l : N)⁻¹ * ⟨s, hsN⟩ : ↥N) : G) ∈ pCoreOf 2 N :=
    Subgroup.mem_map_of_mem N.subtype hmemO
  have hzT : (((l : N)⁻¹ * ⟨s, hsN⟩ : ↥N) : G) ∈ D.T :=
    hpT hzO
  let z : G := ((((l : N)⁻¹ * ⟨s, hsN⟩ : ↥N)) : G)
  have hz_eq : (l : G) * z = s := by
    have h1 : (l : N) * (l⁻¹ * ⟨s, hsN⟩) = ⟨s, hsN⟩ := by group
    exact congrArg Subtype.val h1
  have hlT : (l : G) ∈ D.T := by
    have h1 : (l : G) = s * z⁻¹ := by
      calc (l : G) = (l : G) * z * z⁻¹ := by group
        _ = s * z⁻¹ := by rw [hz_eq]
    rw [h1]
    exact D.T.mul_mem hs.1 (D.T.inv_mem (hpT hzO))
  have hs_eq' : s = (l : G) * z := hz_eq.symm
  rw [hs_eq']
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hlT, hlL⟩) hzO

theorem ntl17_le_normalizer_P1 {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) {X : Subgroup G} (h7 : IsL2Over17 (Bar2 L) 7)
    (h7S : IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7) (hXL : X ≤ L) :
    NTL17 D L ≤ Subgroup.normalizer
      ((X ⊔ (D.T ⊓ L) ⊔ pCoreOf 2 L : Subgroup G) : Set G) := by
  classical
  set S : Subgroup G := NTL17 D L with hS
  set N : Subgroup G := L ⊔ S with hN
  set S0 : Subgroup G := D.T ⊓ L with hS0def
  set P1 : Subgroup G := X ⊔ S0 ⊔ pCoreOf 2 L with hP1def
  have hLN : L ≤ N := le_sup_left
  have hSN : S ≤ N := le_sup_right
  have hST : S ≤ D.T := inf_le_left
  have hSNL : S ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hS2 : IsPGroup 2 S := (D.sylowM.isPGroup).to_le hST
  have hLM : L ≤ D.M := hC.memL.1.le
  have hS0syl : CFSG.QuasithinUnique.IsSylowTwoOf S0 L :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal
      (CFSG.QuasithinUnique.Setup.Lift.isSylowTwoOf_of_isSylowOf D.sylowM) hLM
      ((CFSG.Quasithin.isSubnormal_iff_subgroupOf hLM).mp hC.memL.1)
  have hS_sylN : CFSG.QuasithinUnique.IsSylowTwoOf S N := by
    refine ⟨hSN, hS2, ?_⟩
    show ¬ 2 ∣ (S.subgroupOf N).index
    rw [show (S.subgroupOf N).index = S.relIndex N from rfl]
    change ¬ 2 ∣ S.relIndex (L ⊔ S)
    rw [show L ⊔ S = S ⊔ L from sup_comm L S,
      (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hSNL).1]
    have hLS : S ⊓ L = S0 := by
      ext x
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, Subgroup.le_normalizer h.2⟩, h.2⟩⟩
    rw [hLS]; exact hS0syl.2.2
  have hO2_le_S : pCoreOf 2 N ≤ S :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hS_sylN
  have hO2N_normal : N ≤ Subgroup.normalizer ((pCoreOf 2 N : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hO2_le_S.trans hSN)).mp
      (inferInstance : ((pCoreOf 2 N).subgroupOf N).Normal)
  have hO2L_le : pCoreOf 2 L ≤ P1 := le_sup_right
  have hz_le : ∀ z ∈ S, P1.map (MulAut.conj z).toMonoidHom ≤ P1 := by
    intro z hz
    have hzT : z ∈ D.T := hST hz
    have hzNL : z ∈ Subgroup.normalizer (L : Set G) := hSNL hz
    have hzN : z ∈ N := hSN hz
    have hzTnorm : z ∈ Subgroup.normalizer (D.T : Set G) := Subgroup.le_normalizer hzT
    have hTmap : D.T.map (MulAut.conj z).toMonoidHom = D.T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hzTnorm
    have hLmap : L.map (MulAut.conj z).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hzNL
    have hS0map : S0.map (MulAut.conj z).toMonoidHom = S0 := by
      rw [hS0def, Subgroup.map_inf _ _ _ (MulAut.conj z).injective, hTmap, hLmap]
    have hO2Lmap : (pCoreOf 2 L).map (MulAut.conj z).toMonoidHom = pCoreOf 2 L := by
      rw [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj z) L, hLmap]
    have hmem : z ∈ S0 ⊔ pCoreOf 2 N := ntl17_le_sup_pCoreOf hC h7 h7S hz
    have hmem' : (⟨z, hzN⟩ : ↥N) ∈ S0.subgroupOf N ⊔ (pCoreOf 2 N).subgroupOf N := by
      rw [← Subgroup.subgroupOf_sup (show S0 ≤ N from inf_le_right.trans hLN)
        (hO2_le_S.trans hSN)]
      exact Subgroup.mem_subgroupOf.mpr hmem
    have : ((pCoreOf 2 N).subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hO2_le_S.trans hSN)).mpr hO2N_normal
    obtain ⟨s0, hs0, w, hw, hzw⟩ := Subgroup.mem_sup_of_normal_right.mp hmem'
    have hs0G : (s0 : G) ∈ S0 := Subgroup.mem_subgroupOf.mp hs0
    have hwG : (w : G) ∈ pCoreOf 2 N := Subgroup.mem_subgroupOf.mp hw
    have hwS : (w : G) ∈ S := hO2_le_S hwG
    have hwT : (w : G) ∈ D.T := hST hwS
    have hwNL : (w : G) ∈ Subgroup.normalizer (L : Set G) := hSNL hwS
    have hwLmap : L.map (MulAut.conj (w : G)).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hwNL
    have hzwG : (s0 : G) * (w : G) = z := congrArg Subtype.val hzw
    have hXw : X.map (MulAut.conj (w : G)).toMonoidHom ≤ X ⊔ pCoreOf 2 L := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      have hcomm : (w : G) * x * (w : G)⁻¹ = ⁅(w : G), x⁆ * x := by
        rw [commutatorElement_def]; group
      change (w : G) * x * (w : G)⁻¹ ∈ X ⊔ pCoreOf 2 L
      rw [hcomm]
      have h1 : ⁅(w : G), x⁆ ∈ pCoreOf 2 N := by
        have hcomm_le : ⁅pCoreOf 2 N, N⁆ ≤ pCoreOf 2 N :=
          Subgroup.le_normalizer_iff_commutator_le_left.mp hO2N_normal
        exact hcomm_le (Subgroup.commutator_mem_commutator hwG (hLN (hXL hx)))
      have h2 : ⁅(w : G), x⁆ ∈ L := by
        have hconj : (w : G) * x * (w : G)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp hwNL x).mp (hXL hx)
        rw [commutatorElement_def]
        exact L.mul_mem hconj (L.inv_mem (hXL hx))
      have h3 : L ⊓ pCoreOf 2 N = pCoreOf 2 L := by
        apply le_antisymm
        · refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left ?_
            ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le inf_le_right)
          refine ⟨fun x hx l => ?_⟩
          obtain ⟨hxL, hxO⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)
          refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
          · exact L.mul_mem (L.mul_mem l.2 hxL) (L.inv_mem l.2)
          · exact (Subgroup.mem_normalizer_iff.mp (hO2N_normal (hLN l.2)) x).mp hxO
        · exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
            (CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2
              (CFSG.Open.IsSubnormal.step hLN ((Subgroup.normal_subgroupOf_iff_le_normalizer
                hLN).mpr (sup_le Subgroup.le_normalizer hSNL)) (CFSG.Open.IsSubnormal.refl N)))
      have hmemL : ⁅(w : G), x⁆ ∈ pCoreOf 2 L := by
        rw [← h3]; exact ⟨h2, h1⟩
      rw [sup_comm]
      exact Subgroup.mul_mem_sup hmemL hx
    have hs0P1 : (s0 : G) ∈ P1 := by
      rw [hP1def]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hs0G)
    have hcomp : (MulAut.conj z).toMonoidHom =
        (MulAut.conj (s0 : G)).toMonoidHom.comp (MulAut.conj (w : G)).toMonoidHom := by
      ext x
      show z * x * z⁻¹ = (s0 : G) * ((w : G) * x * (w : G)⁻¹) * (s0 : G)⁻¹
      rw [← hzwG, mul_inv_rev]
      group
    have hXz : X.map (MulAut.conj z).toMonoidHom ≤ P1 := by
      rw [hcomp, ← Subgroup.map_map]
      have hP1s0 : P1.map (MulAut.conj (s0 : G)).toMonoidHom = P1 :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hs0P1)
      calc (X.map (MulAut.conj (w : G)).toMonoidHom).map
            (MulAut.conj (s0 : G)).toMonoidHom
          ≤ (X ⊔ pCoreOf 2 L).map (MulAut.conj (s0 : G)).toMonoidHom :=
            Subgroup.map_mono hXw
        _ ≤ P1.map (MulAut.conj (s0 : G)).toMonoidHom :=
            Subgroup.map_mono (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        _ = P1 := hP1s0
    rw [hP1def, Subgroup.map_sup, Subgroup.map_sup, hS0map, hO2Lmap]
    exact sup_le (sup_le hXz (le_sup_right.trans le_sup_left)) le_sup_right
  intro z hz
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (hz_le z hz) ?_
  have hzinv : z⁻¹ ∈ S := S.inv_mem hz
  intro x hx
  refine Subgroup.mem_map.mpr ⟨z⁻¹ * x * z, ?_, ?_⟩
  · exact hz_le z⁻¹ hzinv
      (by simpa [MulAut.conj_apply] using
        Subgroup.mem_map_of_mem (MulAut.conj z⁻¹).toMonoidHom hx)
  · show z * (z⁻¹ * x * z) * z⁻¹ = x
    group

@[expose] def P17 (D : Data G) (X L : Subgroup G) : Subgroup G := X ⊔ (D.T ⊓ L) ⊔ pCoreOf 2 L

@[expose] def W17 (D : Data G) (X L : Subgroup G) (t : G) : Subgroup G :=
  pCoreOf 2 (P17 D X L) ⊔ (pCoreOf 2 (P17 D X L)).map (MulAut.conj t).toMonoidHom ⊔
    pCoreOf 2 D.M

@[expose] def Gap17_15_swapOrbit (D : Data G) (L : Subgroup G) : Prop :=
  D.T ≤ Subgroup.normalizer ((NTL17 D L : Subgroup G) : Set G) ∧
    ∃ t ∈ D.T, t ∉ NTL17 D L ∧ ∀ s ∈ D.T, s ∈ NTL17 D L ∨ t⁻¹ * s ∈ NTL17 D L

theorem map_conj_pCoreOf_sup_eq_of_mem {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) {X : Subgroup G} (h7 : IsL2Over17 (Bar2 L) 7)
    (h7S : IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7) (hXL : X ≤ L)
    {s : G} (hs : s ∈ NTL17 D L) :
    (pCoreOf 2 (P17 D X L)).map (MulAut.conj s).toMonoidHom =
      pCoreOf 2 (P17 D X L) := by
  set P1 : Subgroup G := P17 D X L with hP1def
  have h : P1.map (MulAut.conj s).toMonoidHom = P1 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (ntl17_le_normalizer_P1 hC h7 h7S hXL hs)
  rw [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj s) P1, h]

theorem map_conj_pCoreOf_sup_eq_of_notMem {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) {X : Subgroup G} (h7 : IsL2Over17 (Bar2 L) 7)
    (h7S : IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7) (hXL : X ≤ L)
    {t s : G} (hcoset : s ∈ NTL17 D L ∨ t⁻¹ * s ∈ NTL17 D L) (hs : s ∉ NTL17 D L) :
    (pCoreOf 2 (P17 D X L)).map (MulAut.conj s).toMonoidHom =
      (pCoreOf 2 (P17 D X L)).map (MulAut.conj t).toMonoidHom := by
  have hmul : ∀ (x y : G) (A : Subgroup G),
      A.map (MulAut.conj (x * y)).toMonoidHom =
        (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    intro x y A
    rw [Subgroup.map_map]
    congr 1
    ext a
    simp [mul_assoc]
  have hs1 : t⁻¹ * s ∈ NTL17 D L := hcoset.resolve_left hs
  have hkey : (pCoreOf 2 (P17 D X L)).map (MulAut.conj s).toMonoidHom =
      ((pCoreOf 2 (P17 D X L)).map
        (MulAut.conj (t⁻¹ * s)).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    have h2 := hmul t (t⁻¹ * s) (pCoreOf 2 (P17 D X L))
    rw [show t * (t⁻¹ * s) = s by group] at h2
    exact h2
  rw [hkey, map_conj_pCoreOf_sup_eq_of_mem hC h7 h7S hXL hs1]

theorem sq_mem_ntl17 {D : Data G} {L : Subgroup G} {t : G} (htT : t ∈ D.T)
    (htS : t ∉ NTL17 D L)
    (hcoset : ∀ s ∈ D.T, s ∈ NTL17 D L ∨ t⁻¹ * s ∈ NTL17 D L) :
    t ^ 2 ∈ NTL17 D L := by
  rcases hcoset (t * t) (D.T.mul_mem htT htT) with h | h
  · simpa [pow_two] using h
  · exact absurd (by simpa [pow_two, mul_assoc] using h) htS

theorem map_conj_mul_pCoreOf_sup_eq_of_mem {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) {X : Subgroup G} (h7 : IsL2Over17 (Bar2 L) 7)
    (h7S : IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7) (hXL : X ≤ L)
    {t s : G} (hSnorm : D.T ≤ Subgroup.normalizer ((NTL17 D L : Subgroup G) : Set G))
    (htT : t ∈ D.T) (hs : s ∈ NTL17 D L) :
    (pCoreOf 2 (P17 D X L)).map (MulAut.conj (s * t)).toMonoidHom =
      (pCoreOf 2 (P17 D X L)).map (MulAut.conj t).toMonoidHom := by
  have hmul : ∀ (x y : G) (A : Subgroup G),
      A.map (MulAut.conj (x * y)).toMonoidHom =
        (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    intro x y A
    rw [Subgroup.map_map]
    congr 1
    ext a
    simp [mul_assoc]
  have hσ : t⁻¹ * s * t ∈ NTL17 D L := by
    have h : (NTL17 D L).map (MulAut.conj t⁻¹).toMonoidHom = NTL17 D L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSnorm (D.T.inv_mem htT))
    have h2 := Subgroup.mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hs
    rw [h] at h2
    simpa [MulAut.conj_apply] using h2
  have hkey := hmul t (t⁻¹ * s * t) (pCoreOf 2 (P17 D X L))
  rw [show t * (t⁻¹ * s * t) = s * t by group] at hkey
  rw [hkey, map_conj_pCoreOf_sup_eq_of_mem hC h7 h7S hXL hσ]

theorem map_conj_mul_pCoreOf_sup_eq_of_notMem {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) {X : Subgroup G} (h7 : IsL2Over17 (Bar2 L) 7)
    (h7S : IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7) (hXL : X ≤ L)
    {t s : G} (hSnorm : D.T ≤ Subgroup.normalizer ((NTL17 D L : Subgroup G) : Set G))
    (htT : t ∈ D.T) (ht2 : t ^ 2 ∈ NTL17 D L)
    (hcoset : s ∈ NTL17 D L ∨ t⁻¹ * s ∈ NTL17 D L) (hs : s ∉ NTL17 D L) :
    (pCoreOf 2 (P17 D X L)).map (MulAut.conj (s * t)).toMonoidHom =
      pCoreOf 2 (P17 D X L) := by
  have hmul : ∀ (x y : G) (A : Subgroup G),
      A.map (MulAut.conj (x * y)).toMonoidHom =
        (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    intro x y A
    rw [Subgroup.map_map]
    congr 1
    ext a
    simp [mul_assoc]
  have hσ : t⁻¹ * s ∈ NTL17 D L := hcoset.resolve_left hs
  have hσ₂ : t⁻¹ * (t⁻¹ * s) * t ∈ NTL17 D L := by
    have h : (NTL17 D L).map (MulAut.conj t⁻¹).toMonoidHom = NTL17 D L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSnorm (D.T.inv_mem htT))
    have h2 := Subgroup.mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hσ
    rw [h] at h2
    simpa [MulAut.conj_apply] using h2
  have hstep2 : (pCoreOf 2 (P17 D X L)).map
      (MulAut.conj (t⁻¹ * s * t)).toMonoidHom =
      (pCoreOf 2 (P17 D X L)).map (MulAut.conj t).toMonoidHom := by
    have h := hmul t (t⁻¹ * (t⁻¹ * s) * t) (pCoreOf 2 (P17 D X L))
    rw [show t * (t⁻¹ * (t⁻¹ * s) * t) = t⁻¹ * s * t by group] at h
    rw [h, map_conj_pCoreOf_sup_eq_of_mem hC h7 h7S hXL hσ₂]
  have hstep1 : (pCoreOf 2 (P17 D X L)).map
      (MulAut.conj (s * t)).toMonoidHom =
      ((pCoreOf 2 (P17 D X L)).map
        (MulAut.conj (t⁻¹ * s * t)).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    have h := hmul t (t⁻¹ * s * t) (pCoreOf 2 (P17 D X L))
    rw [show t * (t⁻¹ * s * t) = s * t by group] at h
    exact h
  have hstep3 : ((pCoreOf 2 (P17 D X L)).map
      (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      (pCoreOf 2 (P17 D X L)).map (MulAut.conj (t ^ 2)).toMonoidHom := by
    have h := hmul t t (pCoreOf 2 (P17 D X L))
    rw [show t * t = t ^ 2 by rw [pow_two]] at h
    exact h.symm
  rw [hstep1, hstep2, hstep3, map_conj_pCoreOf_sup_eq_of_mem hC h7 h7S hXL ht2]


theorem isPGroup_W17 {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) {X : Subgroup G} (h7 : IsL2Over17 (Bar2 L) 7)
    (h7S : IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7) (hXL : X ≤ L)
    {t : G} (htT : t ∈ D.T) (htS : t ∉ NTL17 D L) :
    IsPGroup 2 (W17 D X L t) := by
  have hP1L : P17 D X L ≤ L :=
    sup_le (sup_le hXL inf_le_right) (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  have hO2L_O2M : pCoreOf 2 L ≤ pCoreOf 2 D.M :=
    CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hC.memL.1
  have hMnorm : D.M ≤ Subgroup.normalizer ((pCoreOf 2 D.M : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
  have hUL : pCoreOf 2 (P17 D X L) ≤ L :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (P17 D X L)).trans hP1L
  have hLtcal : L.map (MulAut.conj t).toMonoidHom ∈ calC D.M := by
    have hMt : D.M.map (MulAut.conj t).toMonoidHom = D.M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (D.sylowM.le htT))
    exact CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map D.M (MulAut.conj t) hMt hC.memL
  have hLt_ne : L ≠ L.map (MulAut.conj t).toMonoidHom := by
    intro h
    exact htS (Subgroup.mem_inf.mpr ⟨htT, Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm⟩)
  have hcomm' : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ ≤ pCoreOf 2 D.M :=
    ((calC_commutator_le_of_ne hC.memL hLtcal hLt_ne).trans inf_le_left).trans hO2L_O2M
  have hcomm : ⁅pCoreOf 2 (P17 D X L),
      (pCoreOf 2 (P17 D X L)).map (MulAut.conj t).toMonoidHom⁆ ≤ pCoreOf 2 D.M :=
    (Subgroup.commutator_mono hUL (Subgroup.map_mono hUL)).trans hcomm'
  have hAn : pCoreOf 2 (P17 D X L) ≤
      Subgroup.normalizer ((pCoreOf 2 D.M : Subgroup G) : Set G) :=
    hUL.trans (hC.memL.1.le.trans hMnorm)
  have hBn : (pCoreOf 2 (P17 D X L)).map (MulAut.conj t).toMonoidHom ≤
      Subgroup.normalizer ((pCoreOf 2 D.M : Subgroup G) : Set G) :=
    (Subgroup.map_mono hUL).trans (hLtcal.1.le.trans hMnorm)
  have hUt2 : IsPGroup 2 ↥((pCoreOf 2 (P17 D X L)).map (MulAut.conj t).toMonoidHom) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P17 D X L)).of_equiv
      (Subgroup.equivMapOfInjective _ (MulAut.conj t).toMonoidHom (MulAut.conj t).injective)
  have hUp := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P17 D X L)
  have h := CFSG.AGLEmbedding.isPGroup_iSup_sup_of_pairwise_commutator_le
    (fun b : Bool => cond b (pCoreOf 2 (P17 D X L))
      ((pCoreOf 2 (P17 D X L)).map (MulAut.conj t).toMonoidHom))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
    (fun b => by cases b <;> assumption) (fun b => by cases b <;> assumption)
    (by
      rintro (_ | _) (_ | _) hij
      · exact absurd rfl hij
      · simpa [Subgroup.commutator_comm] using hcomm
      · simpa using hcomm
      · exact absurd rfl hij)
  rw [iSup_bool_eq] at h
  exact h

theorem le_normalizer_W17_of_X {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) {X : Subgroup G} (h7 : IsL2Over17 (Bar2 L) 7)
    (h7S : IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7) (hXL : X ≤ L)
    {t : G} (htT : t ∈ D.T) (htS : t ∉ NTL17 D L) :
    X ≤ Subgroup.normalizer ((W17 D X L t : Subgroup G) : Set G) := by
  have hP1L : P17 D X L ≤ L :=
    sup_le (sup_le hXL inf_le_right) (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  have hO2L_O2M : pCoreOf 2 L ≤ pCoreOf 2 D.M :=
    CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hC.memL.1
  have hMnorm : D.M ≤ Subgroup.normalizer ((pCoreOf 2 D.M : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
  have hUL : pCoreOf 2 (P17 D X L) ≤ L :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (P17 D X L)).trans hP1L
  have hLtcal : L.map (MulAut.conj t).toMonoidHom ∈ calC D.M := by
    have hMt : D.M.map (MulAut.conj t).toMonoidHom = D.M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (D.sylowM.le htT))
    exact CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map D.M (MulAut.conj t) hMt hC.memL
  have hLt_ne : L ≠ L.map (MulAut.conj t).toMonoidHom := by
    intro h
    exact htS (Subgroup.mem_inf.mpr ⟨htT, Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm⟩)
  have hcomm' : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ ≤ pCoreOf 2 D.M :=
    ((calC_commutator_le_of_ne hC.memL hLtcal hLt_ne).trans inf_le_left).trans hO2L_O2M
  have hXU : X ≤ Subgroup.normalizer ((pCoreOf 2 (P17 D X L) : Subgroup G) : Set G) :=
    (show X ≤ P17 D X L from le_sup_left.trans le_sup_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P17 D X L))
  have hXN : X ≤ Subgroup.normalizer ((pCoreOf 2 D.M : Subgroup G) : Set G) :=
    hXL.trans (hC.memL.1.le.trans hMnorm)
  have hXUt : X ≤ Subgroup.normalizer
      (((pCoreOf 2 (P17 D X L)).map (MulAut.conj t).toMonoidHom ⊔ pCoreOf 2 D.M : Subgroup G) :
        Set G) :=
    CFSG.RankThree.PartTwo.Sec14.Ronan134Q.le_normalizer_sup_of_commutator_le hXN
      ((Subgroup.commutator_mono hXL (Subgroup.map_mono hUL)).trans hcomm')
  have h2 := (le_inf hXU hXUt).trans (Subgroup.inf_normalizer_le_normalizer_sup
    (pCoreOf 2 (P17 D X L))
    ((pCoreOf 2 (P17 D X L)).map (MulAut.conj t).toMonoidHom ⊔ pCoreOf 2 D.M))
  simpa only [W17, sup_assoc] using h2

theorem le_normalizer_W17_of_T {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) {X : Subgroup G} (h7 : IsL2Over17 (Bar2 L) 7)
    (h7S : IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7) (hXL : X ≤ L)
    {t : G} (hSnorm : D.T ≤ Subgroup.normalizer ((NTL17 D L : Subgroup G) : Set G))
    (htT : t ∈ D.T) (htS : t ∉ NTL17 D L)
    (hcoset : ∀ s ∈ D.T, s ∈ NTL17 D L ∨ t⁻¹ * s ∈ NTL17 D L) :
    D.T ≤ Subgroup.normalizer ((W17 D X L t : Subgroup G) : Set G) := by
  have ht2 : t ^ 2 ∈ NTL17 D L := sq_mem_ntl17 htT htS hcoset
  have hMnorm : D.M ≤ Subgroup.normalizer ((pCoreOf 2 D.M : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
  have hmul : ∀ (x y : G) (A : Subgroup G),
      A.map (MulAut.conj (x * y)).toMonoidHom =
        (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    intro x y A
    rw [Subgroup.map_map]
    congr 1
    ext a
    simp [mul_assoc]
  intro s hsT
  have hNs : (pCoreOf 2 D.M).map (MulAut.conj s).toMonoidHom = pCoreOf 2 D.M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMnorm (D.sylowM.le hsT))
  have hcomp : ((pCoreOf 2 (P17 D X L)).map (MulAut.conj t).toMonoidHom).map
      (MulAut.conj s).toMonoidHom =
      (pCoreOf 2 (P17 D X L)).map (MulAut.conj (s * t)).toMonoidHom := (hmul s t _).symm
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  have hmain : (W17 D X L t).map (MulAut.conj s).toMonoidHom = W17 D X L t := by
    rw [show W17 D X L t = pCoreOf 2 (P17 D X L) ⊔
      (pCoreOf 2 (P17 D X L)).map (MulAut.conj t).toMonoidHom ⊔ pCoreOf 2 D.M from rfl]
    rw [Subgroup.map_sup, Subgroup.map_sup, hNs, hcomp]
    by_cases hs : s ∈ NTL17 D L
    · rw [map_conj_pCoreOf_sup_eq_of_mem hC h7 h7S hXL hs,
        map_conj_mul_pCoreOf_sup_eq_of_mem hC h7 h7S hXL hSnorm htT hs]
    · rw [map_conj_pCoreOf_sup_eq_of_notMem hC h7 h7S hXL (hcoset s hsT) hs,
        map_conj_mul_pCoreOf_sup_eq_of_notMem hC h7 h7S hXL hSnorm htT ht2 (hcoset s hsT) hs]
      ac_rfl
  exact hmain

theorem pCoreOf_P1_le_pCoreOf_H {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) {X : Subgroup G} (h7 : IsL2Over17 (Bar2 L) 7)
    (h7S : IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7) (hXL : X ≤ L)
    (horb : Gap17_15_swapOrbit D L) :
    pCoreOf 2 (P17 D X L) ≤ pCoreOf 2 (X ⊔ D.T) := by
  obtain ⟨hSnorm, t, htT, htS, hcoset⟩ := horb
  have hO2L_O2M : pCoreOf 2 L ≤ pCoreOf 2 D.M :=
    CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hC.memL.1
  have hO2M_T : pCoreOf 2 D.M ≤ D.T :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf
      (CFSG.QuasithinUnique.Setup.Lift.isSylowTwoOf_of_isSylowOf D.sylowM)
  have hO2L_T : pCoreOf 2 L ≤ D.T := hO2L_O2M.trans hO2M_T
  have hP1L : P17 D X L ≤ L :=
    sup_le (sup_le hXL inf_le_right) (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  have hP1H : P17 D X L ≤ X ⊔ D.T :=
    sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) (hO2L_T.trans le_sup_right)
  have hUH : pCoreOf 2 (P17 D X L) ≤ X ⊔ D.T :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (P17 D X L)).trans hP1H
  have hUtH : (pCoreOf 2 (P17 D X L)).map (MulAut.conj t).toMonoidHom ≤ X ⊔ D.T := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    exact (X ⊔ D.T).mul_mem ((X ⊔ D.T).mul_mem (Subgroup.mem_sup_right htT) (hUH hu))
      ((X ⊔ D.T).inv_mem (Subgroup.mem_sup_right htT))
  have hWH : W17 D X L t ≤ X ⊔ D.T :=
    sup_le (sup_le hUH hUtH) (hO2M_T.trans le_sup_right)
  have hpW : IsPGroup 2 (W17 D X L t) := isPGroup_W17 hC h7 h7S hXL htT htS
  have hnorm : X ⊔ D.T ≤ Subgroup.normalizer ((W17 D X L t : Subgroup G) : Set G) :=
    sup_le (le_normalizer_W17_of_X hC h7 h7S hXL htT htS)
      (le_normalizer_W17_of_T hC h7 h7S hXL hSnorm htT htS hcoset)
  exact (show pCoreOf 2 (P17 D X L) ≤ W17 D X L t from le_sup_left.trans le_sup_left).trans
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWH hnorm hpW)

theorem exists_inverting_of_permutes {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hK : K_L27PermutesS3) (hC : Ctx17_6 D V₀ V L r q) {X : Subgroup G}
    (h7 : IsL2Over17 (Bar2 L) 7) (hXL : X ≤ L) (hXcard : Nat.card X = 3)
    (hperm : Permutes X (NTL17 D L)) :
    ∃ d ∈ D.T ⊓ L, ∀ x ∈ X, d * x * d⁻¹ * x ∈ pCoreOf 2 (X ⊔ (D.T ⊓ L) ⊔ pCoreOf 2 L) := by
  classical
  set S0 : Subgroup G := D.T ⊓ L with hS0def
  set P1 : Subgroup G := X ⊔ S0 ⊔ pCoreOf 2 L with hP1def
  have hLM : L ≤ D.M := hC.memL.1.le
  have hS0L : S0 ≤ L := inf_le_right
  have hS0S : S0 ≤ NTL17 D L := fun x hx =>
    Subgroup.mem_inf.mpr ⟨hx.1, Subgroup.le_normalizer hx.2⟩
  have hP1L : P1 ≤ L :=
    sup_le (sup_le hXL hS0L) (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  have hS0syl2 : CFSG.QuasithinUnique.IsSylowTwoOf S0 L :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal
      (CFSG.QuasithinUnique.Setup.Lift.isSylowTwoOf_of_isSylowOf D.sylowM) hLM
      ((CFSG.Quasithin.isSubnormal_iff_subgroupOf hLM).mp hC.memL.1)
  have hS0sylIn : IsSylowIn 2 S0 L :=
    (CFSG.ABGLocalTools.isSylowOf_iff).mp
      ((CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf).mp hS0syl2)
  let πL : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let Xbar : Subgroup (Bar2 L) := (X.subgroupOf L).map πL
  let S0bar : Subgroup (Bar2 L) := (S0.subgroupOf L).map πL
  have hS0bar_syl : IsSylowIn 2 S0bar ⊤ :=
    CFSG.LocalAnalysis.WeakClosure81.isSylowIn_barImage hS0sylIn
  have hXp : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by rw [hXcard]; norm_num)
  have hXO : X ⊓ pCoreOf 2 L = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) X (pCoreOf 2 L) hXp
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L))
  have hXker : (X.subgroupOf L) ⊓ πL.ker = ⊥ := by
    rw [show πL.ker = CFSG.pCore 2 ↥L from QuotientGroup.ker_mk' _]
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzX, hzP⟩ := Subgroup.mem_inf.mp hz
    have hzG : (z : G) ∈ X ⊓ pCoreOf 2 L := by
      refine ⟨Subgroup.mem_subgroupOf.mp hzX, ?_⟩
      have hpcmap : (CFSG.pCore 2 ↥L).map L.subtype = pCoreOf 2 L :=
        (CFSG.openPCoreOf_eq_map_pCore 2 L).symm
      rw [← hpcmap]
      exact Subgroup.mem_map_of_mem L.subtype hzP
    rw [hXO] at hzG
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hzG))
  have hXbar_card : Nat.card Xbar = 3 := by
    rw [show Nat.card Xbar = Nat.card ↥(X.subgroupOf L) from
      CFSG.card_map_eq_card_of_inf_ker_eq_bot πL hXker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv, hXcard]
  have hpermS0 : Permutes X S0 := by
    have hsub : ((X : Set G) * (S0 : Set G)) ⊆ ((S0 : Set G) * (X : Set G)) := by
      rintro _ ⟨x, hx, s, hs, rfl⟩
      have hsS : s ∈ NTL17 D L := hS0S hs
      have hmem : x * s ∈ (NTL17 D L : Set G) * (X : Set G) := by
        rw [← hperm]
        exact Set.mul_mem_mul hx hsS
      obtain ⟨s', hs', x', hx', hxs⟩ := hmem
      have hs'L : s' ∈ L := by
        have e : s' = x * s * x'⁻¹ := by rw [← hxs]; group
        rw [e]
        exact L.mul_mem (L.mul_mem (hXL hx) (hS0L hs)) (L.inv_mem (hXL hx'))
      exact ⟨s', ⟨hs'.1, hs'L⟩, x', hx', hxs⟩
    have hsub' : ((S0 : Set G) * (X : Set G)) ⊆ ((X : Set G) * (S0 : Set G)) := by
      rintro _ ⟨s, hs, x, hx, rfl⟩
      have hsS : s ∈ NTL17 D L := hS0S hs
      have hmem : s * x ∈ (NTL17 D L : Set G) * (X : Set G) := Set.mul_mem_mul hsS hx
      rw [← hperm] at hmem
      obtain ⟨x', hx', s', hs', hxs⟩ := hmem
      have hs'L : s' ∈ L := by
        have e : s' = x'⁻¹ * (s * x) := by rw [← hxs]; group
        rw [e]
        exact L.mul_mem (L.inv_mem (hXL hx')) (L.mul_mem (hS0L hs) (hXL hx))
      exact ⟨x', hx', s', ⟨hs'.1, hs'L⟩, hxs⟩
    exact Set.Subset.antisymm hsub hsub'
  have hpermSub : Permutes (X.subgroupOf L) (S0.subgroupOf L) :=
    CFSG.Quasithin.H.Tri.subgroupOf_mul_comm hXL hS0L hpermS0
  have hpermbar : Permutes Xbar S0bar := CFSG.GroupTheory.map_permutes_map πL hpermSub
  have hL2odd : IsL2Odd (Bar2 L) 7 := isL2Odd_seven_of_isL2Over17_seven h7
  obtain ⟨-, -, ⟨eS3⟩, dbar, hdbar_mem, hdbar_notin, hdbar_inv⟩ :=
    hK (Bar2 L) hL2odd S0bar hS0bar_syl Xbar hXbar_card hpermbar
  obtain ⟨y, hy, hyd⟩ := Subgroup.mem_map.mp hdbar_mem
  have hyS0 : (y : G) ∈ S0 := Subgroup.mem_subgroupOf.mp hy
  refine ⟨(y : G), hyS0, ?_⟩
  let ψ : ↥P1 →* Bar2 L := πL.comp (Subgroup.inclusion hP1L)
  have hψrange : ψ.range = Xbar ⊔ S0bar := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    have hsub : P1.subgroupOf L = X.subgroupOf L ⊔ S0.subgroupOf L ⊔ CFSG.pCore 2 ↥L := by
      rw [hP1def]
      rw [Subgroup.subgroupOf_sup (sup_le hXL hS0L) (CFSG.LieType.BorelTits.pCoreOf_le 2 L),
        Subgroup.subgroupOf_sup hXL hS0L]
      congr 1
      exact CFSG.Quasithin.A4.subgroupOf_map_subtype' L (CFSG.pCore 2 ↥L)
    rw [hsub, Subgroup.map_sup, Subgroup.map_sup]
    have hbot : (CFSG.pCore 2 ↥L).map πL = ⊥ :=
      (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 ↥L) (f := πL)).mpr
        (by rw [QuotientGroup.ker_mk'])
    rw [hbot, sup_bot_eq]
  have hψmem : ∀ z : ↥P1, ψ z ∈ Xbar ⊔ S0bar := by
    intro z
    rw [← hψrange]
    exact ⟨z, rfl⟩
  let φ : ↥P1 →* ↥(Xbar ⊔ S0bar) := ψ.codRestrict _ hψmem
  have hφsurj : Function.Surjective φ := by
    intro w
    have hw : (w : Bar2 L) ∈ ψ.range := by rw [hψrange]; exact w.2
    obtain ⟨z, hz⟩ := hw
    exact ⟨z, Subtype.ext hz⟩
  have hφker_eq : φ.ker = (pCoreOf 2 L).subgroupOf P1 := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hz
      have h1 : (φ z : Bar2 L) = 1 := congrArg Subtype.val hz
      rw [show (φ z : Bar2 L) = πL ⟨(z : G), hP1L z.2⟩ from rfl,
        show πL ⟨(z : G), hP1L z.2⟩ = QuotientGroup.mk ⟨(z : G), hP1L z.2⟩ from rfl,
        QuotientGroup.eq_one_iff] at h1
      exact (CFSG.mem_openPCoreOf_iff (⟨(z : G), hP1L z.2⟩ : ↥L)).mpr h1
    · intro hz
      have h1 : πL ⟨(z : G), hP1L z.2⟩ = 1 := by
        rw [show πL ⟨(z : G), hP1L z.2⟩ = QuotientGroup.mk ⟨(z : G), hP1L z.2⟩ from rfl]
        exact (QuotientGroup.eq_one_iff _).mpr ((CFSG.mem_openPCoreOf_iff _).mp hz)
      apply Subtype.ext
      change (φ z : Bar2 L) = 1
      rwa [show (φ z : Bar2 L) = πL ⟨(z : G), hP1L z.2⟩ from rfl]
  have hφker : IsPGroup 2 φ.ker := by
    rw [hφker_eq]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).of_equiv
      (Subgroup.subgroupOfEquivOfLe (show pCoreOf 2 L ≤ P1 from le_sup_right)).symm
  have hmap := CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker φ hφsurj hφker
  have hUpre : ∀ z : ↥P1, z ∈ CFSG.pCore 2 ↥P1 ↔
      φ z ∈ CFSG.pCore 2 ↥(Xbar ⊔ S0bar) := by
    intro z
    constructor
    · intro hz
      rw [← hmap]
      exact Subgroup.mem_map_of_mem φ hz
    · intro hz
      rw [← hmap] at hz
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
      have hker : w⁻¹ * z ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hwz, inv_mul_cancel]
      have hkle : φ.ker ≤ CFSG.pCore 2 ↥P1 := le_sSup ⟨φ.normal_ker, hφker⟩
      have h := (CFSG.pCore 2 ↥P1).mul_mem hw (hkle hker)
      simpa using h
  intro x hx
  have hxL : x ∈ L := hXL hx
  have hxP1 : x ∈ P1 := by
    rw [hP1def]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)
  have hdP1 : (y : G) ∈ P1 := by
    rw [hP1def]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hyS0))
  have hzP1 : (y : G) * x * (y : G)⁻¹ * x ∈ P1 :=
    P1.mul_mem (P1.mul_mem (P1.mul_mem hdP1 hxP1) (P1.inv_mem hdP1)) hxP1
  have hxbar : πL ⟨x, hxL⟩ ∈ Xbar :=
    Subgroup.mem_map_of_mem πL (Subgroup.mem_subgroupOf.mpr hx)
  let dy : ↥L := ⟨(y : G), hP1L hdP1⟩
  let dx : ↥L := ⟨x, hxL⟩
  have hz_eq : (⟨(y : G) * x * (y : G)⁻¹ * x, hP1L hzP1⟩ : ↥L) = dy * dx * dy⁻¹ * dx := by
    apply Subtype.ext
    rfl
  have hdy : πL dy = dbar := by
    change πL ⟨(y : G), hP1L hdP1⟩ = dbar
    rw [show (⟨(y : G), hP1L hdP1⟩ : ↥L) = y from Subtype.ext rfl]
    exact hyd
  have hdx : πL dx = πL ⟨x, hxL⟩ := rfl
  have hφz : (φ ⟨(y : G) * x * (y : G)⁻¹ * x, hzP1⟩ : Bar2 L) =
      dbar * πL ⟨x, hxL⟩ * dbar⁻¹ * πL ⟨x, hxL⟩ := by
    change πL ⟨(y : G) * x * (y : G)⁻¹ * x, hP1L hzP1⟩ = _
    rw [hz_eq]
    simp only [map_mul, map_inv, hdy, hdx]
  have hzO : (φ ⟨(y : G) * x * (y : G)⁻¹ * x, hzP1⟩ : Bar2 L) ∈
      pCoreOf 2 (Xbar ⊔ S0bar) := by
    rw [hφz]
    exact hdbar_inv (πL ⟨x, hxL⟩) hxbar
  have hzO' : φ ⟨(y : G) * x * (y : G)⁻¹ * x, hzP1⟩ ∈
      CFSG.pCore 2 ↥(Xbar ⊔ S0bar) :=
    (CFSG.mem_openPCoreOf_iff (φ ⟨(y : G) * x * (y : G)⁻¹ * x, hzP1⟩)).mp hzO
  have hzcore : (⟨(y : G) * x * (y : G)⁻¹ * x, hzP1⟩ : ↥P1) ∈ CFSG.pCore 2 ↥P1 :=
    (hUpre ⟨(y : G) * x * (y : G)⁻¹ * x, hzP1⟩).mpr hzO'
  exact (CFSG.mem_openPCoreOf_iff
    (⟨(y : G) * x * (y : G)⁻¹ * x, hzP1⟩ : ↥P1)).mpr hzcore

@[expose] def Gap17_15_swapStep1 (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  IsL2Over17 (Bar2 L) 7 → ¬ IsL2Over17 (Bar2 (L ⊔ D.T)) 7 →
    IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7 →
    ¬ (L.subgroupOf (L ⊔ D.T)).Normal →
    ¬ 2 < (CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf D.M L).ncard →
      ∀ X : Subgroup G, X ≤ L → Nat.card X = 3 → Permutes X (NTL17 D L) →
        ∃ R : Subgroup (Bar2 (X ⊔ D.T)),
          R.Normal ∧
            (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧
              IsPGroup 3 R ∧ R ≠ ⊥ ∧
                (∀ N : Subgroup (Bar2 (X ⊔ D.T)), N.Normal → N ≤ R → N = ⊥ ∨ N = R) ∧
                  R ⊔ ((D.T.subgroupOf (X ⊔ D.T)).map
                    (QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ D.T)))) = ⊤

theorem gap17_15_swapInFSq_of (D : Data G)
    {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    (h3 : Gap17_15_threeConj D V₀ V L r q hC)
    (hStep : Gap17_15_swapStep1 D V₀ V L r q hC) :
    Gap17_15_swapInFSq D V₀ V L r q hC := by
  intro h7 hYs h7S hN X hXL hXcard hperm
  obtain ⟨R, hRn, -, hRp, -, hRmin, hRT⟩ :=
    hStep h7 hYs h7S hN (h3 h7 hYs) X hXL hXcard hperm
  classical
  have hXM : X ≤ D.M := hXL.trans hC.memL.1.le
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hTsylIn : IsSylowIn 2 D.T (X ⊔ D.T) :=
    (CFSG.ABGLocalTools.isSylowOf_iff).mp
      (D.sylowM.of_le le_sup_right (sup_le hXM hTM))
  have hT0syl : IsSylowIn 2 ((D.T.subgroupOf (X ⊔ D.T)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ D.T)))) ⊤ :=
    CFSG.LocalAnalysis.WeakClosure81.isSylowIn_barImage hTsylIn
  have hO2 : CFSG.pCore 2 (Bar2 (X ⊔ D.T)) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (H := ↥(X ⊔ D.T)) (p := 2)
  have := hRn
  have hQR : IsPGroup 2 (Bar2 (X ⊔ D.T) ⧸ R) := by
    have hmap : ((D.T.subgroupOf (X ⊔ D.T)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(X ⊔ D.T)))).map (QuotientGroup.mk' R) = ⊤ := by
      have h := congrArg (Subgroup.map (QuotientGroup.mk' R)) hRT
      rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective R)] at h
    have h2 := hT0syl.isPGroup.map (QuotientGroup.mk' R)
    rw [hmap] at h2
    exact h2.of_equiv Subgroup.topEquiv
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s21rb_inF_one_frattini Nat.prime_three
    (by norm_num) hRp hQR hO2
    (fun N hN hNR => (hRmin N hN hNR).imp (fun h => by rw [h]; exact bot_le) id)

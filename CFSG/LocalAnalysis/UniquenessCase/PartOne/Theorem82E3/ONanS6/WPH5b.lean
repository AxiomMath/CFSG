module

public import CFSG.Quasithin.Background.C124AsmPre
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH3s
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
import CFSG.GroupTheory.PGroup.CardCoprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal (isPSolvable_of_mulEquiv)
open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Opp IsSpor IsAlt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem pI_image_eq_commutator' (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3) (hxZ : x ∉ zSub P c.L) :
    ((pI x c.L).subgroupOf c.L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)) =
      ⁅Subgroup.centralizer ({(QuotientGroup.mk (⟨x, hx.2⟩ : ↥c.L) : c.Lbar)} : Set c.Lbar),
        Subgroup.centralizer ({(QuotientGroup.mk (⟨x, hx.2⟩ : ↥c.L) : c.Lbar)} :
          Set c.Lbar)⁆ := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥c.L := CFSG.pCore 2 ↥c.L
  let q : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let xL : ↥c.L := ⟨x, hx.2⟩
  let xb : c.Lbar := QuotientGroup.mk xL
  let C : Subgroup c.Lbar := Subgroup.centralizer ({xb} : Set c.Lbar)
  let J : Subgroup c.Lbar := ⁅C, C⁆
  have hxL3 : orderOf xL = 3 := by
    rw [Subgroup.orderOf_mk, hx3]
  have hxLne : xL ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxL3
    omega
  have hN2 : IsPGroup 2 ↥N := CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)
  have hxLnotN : xL ∉ N := by
    intro hxN
    have h3dvd : 3 ∣ Nat.card ↥N := by
      have h := orderOf_dvd_natCard (⟨xL, hxN⟩ : ↥N)
      rwa [Subgroup.orderOf_mk, hxL3] at h
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup hN2 Nat.prime_three (by norm_num) h3dvd
  have hxb3 : orderOf xb = 3 := by
    have hdvd : orderOf xb ∣ 3 := by
      have h := orderOf_map_dvd q xL
      rwa [hxL3] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      have hxb1 : xb = 1 := orderOf_eq_one_iff.mp h1
      exact hxLnotN ((QuotientGroup.eq_one_iff xL).mp hxb1)
    · exact h3
  have hxb_not_center : xb ∉ Subgroup.center c.Lbar := by
    intro hxb
    apply hxZ
    refine ⟨hx, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    have hyP : y ∈ P := hy.1
    have hyL : y ∈ c.L := hy.2
    let yL : ↥c.L := ⟨y, hyL⟩
    have hcomm_bar : (QuotientGroup.mk yL : c.Lbar) * xb = xb * QuotientGroup.mk yL :=
      Subgroup.mem_center_iff.mp hxb (QuotientGroup.mk yL)
    have hmemN : ⁅xL, yL⁆ ∈ N := by
      rw [← QuotientGroup.eq_one_iff (⁅xL, yL⁆)]
      show (QuotientGroup.mk' N) ⁅xL, yL⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm_bar.symm
    have hmemO : ⁅x, y⁆ ∈ N.map c.L.subtype :=
      Subgroup.mem_map.mpr ⟨⁅xL, yL⁆, hmemN, by
        simp only [Subgroup.coe_subtype, commutatorElement_def]
        rfl⟩
    have hmemP : ⁅x, y⁆ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem hx.1 hyP) (P.inv_mem hx.1)) (P.inv_mem hyP)
    have hO2 : IsPGroup 2 ↥(N.map c.L.subtype) := hN2.map c.L.subtype
    have hdisj : P ⊓ N.map c.L.subtype = ⊥ :=
      (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (N.map c.L.subtype)
        hP.isPGroup hO2).eq_bot
    have h1 : ⁅x, y⁆ = 1 := by
      have hmem : ⁅x, y⁆ ∈ P ⊓ N.map c.L.subtype := ⟨hmemP, hmemO⟩
      rwa [hdisj, Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hN3 : ¬ 3 ∣ Nat.card ↥N :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hN2 Nat.prime_three (by norm_num)
  have hcop : Nat.Coprime 3 (Nat.card ↥N) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3
  have hxT : IsPGroup 3 ↥(Subgroup.zpowers xL) := by
    have hcard : Nat.card ↥(Subgroup.zpowers xL) = 3 ^ 1 := by
      rw [Nat.card_zpowers, hxL3]
      norm_num
    exact IsPGroup.of_card hcard
  haveI : Fact (IsPGroup 3 ↥(Subgroup.zpowers xL)) := ⟨hxT⟩
  have hcentmap : Subgroup.centralizer ({xb} : Set c.Lbar) =
      (Subgroup.centralizer ({xL} : Set ↥c.L)).map q := by
    have h1 := CFSG.centralizer_map_quotient_eq_map_centralizer (G := ↥c.L) 3
      (Subgroup.zpowers xL) N (CFSG.pCore_normal (p := 2) (G := ↥c.L)) hcop
    dsimp only at h1
    rwa [MonoidHom.map_zpowers, CFSG.centralizer_zpowers_eq_centralizer_singleton,
      CFSG.centralizer_zpowers_eq_centralizer_singleton] at h1
  have hH : (pH x ⊓ c.L).subgroupOf c.L = Subgroup.centralizer ({xL} : Set ↥c.L) := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hy.1)
    · intro hy
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨?_, y.2⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext_iff.mp (Subgroup.mem_centralizer_singleton_iff.mp hy))
  have hperfect : ((pI x c.L).subgroupOf c.L).map q =
      CFSG.Quasithin.perfectCore C := by
    have hI : (pI x c.L).subgroupOf c.L =
        CFSG.Quasithin.perfectCore ((pH x ⊓ c.L).subgroupOf c.L) := by
      rw [CFSG.Quasithin.C124.perfectCore_subgroupOf' inf_le_right]
    rw [hI, CFSG.Quasithin.map_perfectCore, hH, ← hcentmap]
  obtain ⟨hCcard, hZleJ, hJcard, hCeq, hAlt⟩ :=
    hK2 c.Lbar hON xb hxb3 hxb_not_center
  have hxbar_center : (⟨xb, Subgroup.mem_centralizer_singleton_iff.mpr
      (rfl : xb * xb = xb * xb)⟩ : C) ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  let xC : C := ⟨xb, Subgroup.mem_centralizer_singleton_iff.mpr (rfl : xb * xb = xb * xb)⟩
  have hJeq : J.subgroupOf C = ⁅(⊤ : Subgroup C), (⊤ : Subgroup C)⁆ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_self C)]
    change J = Subgroup.map C.subtype (commutator ↥C)
    rw [Subgroup.map_subtype_commutator]
  have hzp : (Subgroup.zpowers xb).subgroupOf C = Subgroup.zpowers xC := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le, MonoidHom.map_zpowers]
    · rfl
    · exact Subgroup.zpowers_le.mpr xC.2
  have hCeq_sub : (⊤ : Subgroup C) = Subgroup.center C ⊔ J.subgroupOf C := by
    have h1 := congrArg (fun K : Subgroup c.Lbar => K.subgroupOf C) hCeq
    rw [Subgroup.subgroupOf_sup (Subgroup.zpowers_le.mpr xC.2)
      (Subgroup.commutator_le_self C), Subgroup.subgroupOf_self, hzp] at h1
    refine le_antisymm ?_ le_top
    change (⊤ : Subgroup C) ≤ Subgroup.center C ⊔ ⁅C, C⁆.subgroupOf C
    rw [h1]
    exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hxbar_center)) le_sup_right
  have hJperfect : ⁅J, J⁆ = J := by
    have hJsubperf : ⁅J.subgroupOf C, J.subgroupOf C⁆ = J.subgroupOf C := by
      have h1 : ⁅Subgroup.center C, Subgroup.center C ⊔ J.subgroupOf C⁆ = ⊥ := by
        rw [Subgroup.commutator_sup_left, Subgroup.commutator_center_left,
          Subgroup.commutator_center_left, sup_bot_eq]
      have h2 : ⁅J.subgroupOf C, Subgroup.center C ⊔ J.subgroupOf C⁆ =
          ⁅J.subgroupOf C, J.subgroupOf C⁆ := by
        rw [Subgroup.commutator_sup_left, Subgroup.commutator_center_right, bot_sup_eq]
      have hmain : ⁅Subgroup.center C ⊔ J.subgroupOf C,
          Subgroup.center C ⊔ J.subgroupOf C⁆ = ⁅J.subgroupOf C, J.subgroupOf C⁆ := by
        rw [Subgroup.commutator_sup_right, h1, h2, bot_sup_eq]
      calc ⁅J.subgroupOf C, J.subgroupOf C⁆
          = ⁅Subgroup.center C ⊔ J.subgroupOf C,
              Subgroup.center C ⊔ J.subgroupOf C⁆ := hmain.symm
        _ = ⁅(⊤ : Subgroup C), (⊤ : Subgroup C)⁆ := by rw [← hCeq_sub]
        _ = J.subgroupOf C := hJeq.symm
    have hmap : ⁅⁅C, C⁆, ⁅C, C⁆⁆ = ⁅C, C⁆ := by
      have h := congrArg (Subgroup.map C.subtype) hJsubperf
      simpa only [J, Subgroup.map_commutator,
        Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_self C)] using h
    change ⁅⁅C, C⁆, ⁅C, C⁆⁆ = ⁅C, C⁆
    exact hmap
  have hJnormal : (J.subgroupOf C).Normal := by
    rw [hJeq]
    exact Subgroup.commutator_normal _ _
  have hJleC : J ≤ C := Subgroup.commutator_le_self C
  have hcoreJ : CFSG.Quasithin.perfectCore C = J := by
    apply le_antisymm
    · exact CFSG.Quasithin.perfectCore_le_of_sup_solvable hJleC hJnormal
        (by change Subgroup.centralizer ({xb} : Set c.Lbar) = J ⊔ Subgroup.zpowers xb
            rw [hCeq, sup_comm])
        (inferInstance : Group.IsSolvable ↥(Subgroup.zpowers xb))
    · exact CFSG.Quasithin.le_perfectCore_of_perfect hJleC hJperfect
  rw [hperfect, hcoreJ]

theorem pCore_two_pI_image' (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3) (hxZ : x ∉ zSub P c.L) :
    (CFSG.pCore 2 ↥(pI x c.L)).map (pI x c.L).subtype =
      pI x c.L ⊓ (CFSG.pCore 2 ↥c.L).map c.L.subtype := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let I : Subgroup G := pI x c.L
  let N : Subgroup ↥c.L := CFSG.pCore 2 ↥c.L
  let q : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let xL : ↥c.L := ⟨x, hx.2⟩
  let xb : c.Lbar := QuotientGroup.mk xL
  let C : Subgroup c.Lbar := Subgroup.centralizer ({xb} : Set c.Lbar)
  let J : Subgroup c.Lbar := ⁅C, C⁆
  have hIleL : I ≤ c.L := (CFSG.Quasithin.perfectCore_le _).trans inf_le_right
  have hImgI : (I.subgroupOf c.L).map q = J := by
    simpa only [I, N, q, J, C, xL, xb] using
      pI_image_eq_commutator' hK2 c hON hP hx hx3 hxZ
  have hxL3 : orderOf xL = 3 := by
    rw [Subgroup.orderOf_mk, hx3]
  have hN2 : IsPGroup 2 ↥N := CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)
  have hxLnotN : xL ∉ N := by
    intro hxN
    have h3dvd : 3 ∣ Nat.card ↥N := by
      have h := orderOf_dvd_natCard (⟨xL, hxN⟩ : ↥N)
      rwa [Subgroup.orderOf_mk, hxL3] at h
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup hN2 Nat.prime_three (by norm_num) h3dvd
  have hxb3 : orderOf xb = 3 := by
    have hdvd : orderOf xb ∣ 3 := by
      have h := orderOf_map_dvd q xL
      rwa [hxL3] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      have hxb1 : xb = 1 := orderOf_eq_one_iff.mp h1
      exact hxLnotN ((QuotientGroup.eq_one_iff xL).mp hxb1)
    · exact h3
  have hxb_not_center : xb ∉ Subgroup.center c.Lbar := by
    intro hxbc
    apply hxZ
    refine ⟨hx, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    have hyP : y ∈ P := hy.1
    have hyL : y ∈ c.L := hy.2
    let yL : ↥c.L := ⟨y, hyL⟩
    have hcomm_bar : (QuotientGroup.mk yL : c.Lbar) * xb = xb * QuotientGroup.mk yL :=
      Subgroup.mem_center_iff.mp hxbc (QuotientGroup.mk yL)
    have hmemN : ⁅xL, yL⁆ ∈ N := by
      rw [← QuotientGroup.eq_one_iff (⁅xL, yL⁆)]
      show (QuotientGroup.mk' N) ⁅xL, yL⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm_bar.symm
    have hmemO : ⁅x, y⁆ ∈ N.map c.L.subtype :=
      Subgroup.mem_map.mpr ⟨⁅xL, yL⁆, hmemN, by
        simp only [Subgroup.coe_subtype, commutatorElement_def]
        rfl⟩
    have hmemP : ⁅x, y⁆ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem hx.1 hyP) (P.inv_mem hx.1)) (P.inv_mem hyP)
    have hO2 : IsPGroup 2 ↥(N.map c.L.subtype) := hN2.map c.L.subtype
    have hdisj : P ⊓ N.map c.L.subtype = ⊥ :=
      (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (N.map c.L.subtype)
        hP.isPGroup hO2).eq_bot
    have h1 : ⁅x, y⁆ = 1 := by
      have hmem : ⁅x, y⁆ ∈ P ⊓ N.map c.L.subtype := ⟨hmemP, hmemO⟩
      rwa [hdisj, Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  obtain ⟨-, hZleJ, -, hCeq, hAlt⟩ := hK2 c.Lbar hON xb hxb3 hxb_not_center
  let Z : Subgroup c.Lbar := Subgroup.center c.Lbar
  let ZJ : Subgroup ↥J := Z.subgroupOf J
  obtain ⟨e⟩ := hAlt
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by norm_num)
  haveI : IsSimpleGroup (↥J ⧸ ZJ) := e.isSimpleGroup
  have hncA6 : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
    refine ⟨⟨Equiv.swap (0 : Fin 6) 1 * Equiv.swap 0 2, ?_⟩,
      ⟨Equiv.swap (0 : Fin 6) 3 * Equiv.swap 0 4, ?_⟩, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup]; decide
    · rw [Equiv.Perm.mem_alternatingGroup]; decide
    · intro h
      have h' := congrArg Subtype.val h
      exact absurd h' (by decide)
  have hnabQ : ∃ a b : ↥J ⧸ ZJ, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hncA6
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have h' := congrArg e h
    simpa using h'
  have hQbot : CFSG.pCore 2 (↥J ⧸ ZJ) = ⊥ :=
    CFSG.CGT.PushingUp.pCore_eq_bot_of_isSimpleGroup hnabQ
  let r : ↥J →* (↥J ⧸ ZJ) := QuotientGroup.mk' ZJ
  have hmap_le : (CFSG.pCore 2 ↥J).map r ≤ CFSG.pCore 2 (↥J ⧸ ZJ) := by
    refine le_sSup ⟨?_, ?_⟩
    · exact (CFSG.pCore_normal (p := 2) (G := ↥J)).map r
        (QuotientGroup.mk'_surjective ZJ)
    · exact (CFSG.pCore_isPGroup (p := 2) (G := ↥J)).map r
  rw [hQbot, le_bot_iff] at hmap_le
  have hleZ : CFSG.pCore 2 ↥J ≤ ZJ := by
    rw [Subgroup.map_eq_bot_iff] at hmap_le
    rwa [QuotientGroup.ker_mk'] at hmap_le
  have hZJcard : Nat.card ↥ZJ = 3 := by
    change Nat.card ↥((Subgroup.center c.Lbar).subgroupOf J) = 3
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleJ).toEquiv]
    exact hON.2.1
  have hbotJ : CFSG.pCore 2 ↥J = ⊥ := by
    have hdvd3 : Nat.card ↥(CFSG.pCore 2 ↥J) ∣ 3 := by
      have hd := Subgroup.card_dvd_of_le hleZ
      rwa [hZJcard] at hd
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥J))
    have hn0 : n = 0 := by
      by_contra hnne
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnne
      have hdvd : 2 ^ (m + 1) ∣ 3 := by
        rw [← hn]
        exact hdvd3
      have h23 : 2 ∣ 3 := (dvd_pow_self 2 (Nat.succ_ne_zero m)).trans hdvd
      norm_num at h23
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hn, hn0, pow_zero])
  have hfval : ∀ i : ↥I, q.comp (Subgroup.inclusion hIleL) i ∈ J := by
    intro i
    rw [← hImgI]
    exact Subgroup.mem_map.mpr
      ⟨Subgroup.inclusion hIleL i, Subgroup.mem_subgroupOf.mpr i.2, rfl⟩
  let f' : ↥I →* ↥J :=
    MonoidHom.codRestrict (q.comp (Subgroup.inclusion hIleL)) J hfval
  have hfsurj : Function.Surjective f' := by
    intro j
    have hj : (j : c.Lbar) ∈ (I.subgroupOf c.L).map q := by
      rw [hImgI]
      exact j.2
    obtain ⟨iL, hiL, hqiL⟩ := Subgroup.mem_map.mp hj
    refine ⟨⟨iL.1, Subgroup.mem_subgroupOf.mp hiL⟩, ?_⟩
    exact Subtype.ext hqiL
  let K' : Subgroup ↥J := (CFSG.pCore 2 ↥I).map f'
  have hK'normal : K'.Normal :=
    (CFSG.pCore_normal (p := 2) (G := ↥I)).map f' hfsurj
  have hK'2 : IsPGroup 2 ↥K' := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).map f'
  have hK'bot : K' = ⊥ := by
    have hle : K' ≤ CFSG.pCore 2 ↥J :=
      le_sSup ⟨hK'normal, hK'2⟩
    exact le_bot_iff.mp (hle.trans (le_of_eq hbotJ))
  apply le_antisymm
  · intro y hy
    obtain ⟨yI, hyI, rfl⟩ := Subgroup.mem_map.mp hy
    have hmemK' : f' yI ∈ K' := Subgroup.mem_map.mpr ⟨yI, hyI, rfl⟩
    have hfone : f' yI = 1 := by
      rw [hK'bot] at hmemK'
      exact Subgroup.mem_bot.mp hmemK'
    have hqone : q (Subgroup.inclusion hIleL yI) = 1 := by
      have h' := congrArg (fun z : ↥J => (z : c.Lbar)) hfone
      simpa [f'] using h'
    have hmemN : Subgroup.inclusion hIleL yI ∈ N :=
      (QuotientGroup.eq_one_iff _).mp hqone
    exact ⟨yI.2, Subgroup.mem_map.mpr
      ⟨Subgroup.inclusion hIleL yI, hmemN, rfl⟩⟩
  · intro y hy
    obtain ⟨hyI, hyO⟩ := hy
    exact CFSG.RankThree.GroupTheory.SteinbergBY.inf_inSubgroup_pCore_le
      (p := 2) (X := c.L) (Y := I) hIleL ⟨hyI, hyO⟩

@[expose] def Step41ThreeCase (c : Ctx82E3 D) (P : Subgroup G) (x : G) : Prop :=
  ((pI x c.L ⊓ ((pDK x).map (pH x).subtype)).subgroupOf c.L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)) = ⊥

theorem image_inf_dK_eq_bot' (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3) (hxZ : x ∉ zSub P c.L)
    (hStep : Step41ThreeCase c P x) :
    ((pI x c.L ⊓ ((pDK x).map (pH x).subtype)).subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)) = ⊥ :=
  hStep

theorem propositionH_step41'' (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3) (hxZ : x ∉ zSub P c.L)
    (hStep : Step41ThreeCase c P x) :
    pI x c.L ⊓ ((pDK x).map (pH x).subtype) ≤
      (CFSG.pCore 2 ↥(pI x c.L)).map (pI x c.L).subtype := by
  intro y hy
  obtain ⟨hyI, hyD⟩ := hy
  have hIlecL : pI x c.L ≤ c.L := (CFSG.Quasithin.perfectCore_le _).trans inf_le_right
  have hyL : y ∈ c.L := hIlecL hyI
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L) ⟨y, hyL⟩) ∈
      ((pI x c.L ⊓ ((pDK x).map (pH x).subtype)).subgroupOf c.L).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨hyI, hyD⟩)
  rw [image_inf_dK_eq_bot' hK2 c hON hP hx hx3 hxZ hStep, Subgroup.mem_bot] at h1
  have h2 : (⟨y, hyL⟩ : ↥c.L) ∈ CFSG.pCore 2 ↥c.L := (QuotientGroup.eq_one_iff _).mp h1
  rw [pCore_two_pI_image' hK2 c hON hP hx hx3 hxZ]
  exact ⟨hyI, Subgroup.mem_map_of_mem c.L.subtype h2⟩

theorem not_isPSolvable_three_alt_six :
    ¬ CFSG.HallHigman.IsPSolvable 3 (alternatingGroup (Fin 6)) := by
  intro h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  let e : (↥(⊤ : Subgroup (alternatingGroup (Fin 6))) ⧸
      (⊥ : Subgroup ↥(⊤ : Subgroup (alternatingGroup (Fin 6))))) ≃*
        alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientBot).trans Subgroup.topEquiv
  have hsimple := e.isSimpleGroup
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    norm_num
  rcases h ⊤ (Subgroup.IsSubnormal.top) ⊥ hsimple with h3 | h3
  · rw [Subgroup.index_bot, Subgroup.card_top, hcard] at h3
    omega
  · rw [Subgroup.index_bot, Subgroup.card_top, hcard] at h3
    have : Nat.gcd 3 360 = 1 := h3
    norm_num at this

@[expose] def Step42Surjection (c : Ctx82E3 D) {P : Subgroup G} {x : G} (hx : x ∈ P ⊓ c.L) : Prop :=
  ∃ f : ↥(pIbar x c.L) →*
      ↥⁅Subgroup.centralizer ({(QuotientGroup.mk (⟨x, hx.2⟩ : ↥c.L) : c.Lbar)} : Set c.Lbar),
        Subgroup.centralizer ({(QuotientGroup.mk (⟨x, hx.2⟩ : ↥c.L) : c.Lbar)} :
          Set c.Lbar)⁆,
    Function.Surjective f

@[expose] def Step42Opp (c : Ctx82E3 D) (P : Subgroup G) (x : G) : Prop :=
  pIbar x c.L ≤ Opp 3 (⊤ : Subgroup (pX x))

theorem propositionH_step42'' (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3) (hxZ : x ∉ zSub P c.L)
    (hSurj : Step42Surjection c hx) (hOpp : Step42Opp c P x) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(pIbar x c.L) ∧
      360 < Nat.card ↥(pIbar x c.L) ∧
      pIbar x c.L ≤ Opp 3 (⊤ : Subgroup (pX x)) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥c.L := CFSG.pCore 2 ↥c.L
  let q : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let xL : ↥c.L := ⟨x, hx.2⟩
  let xb : c.Lbar := QuotientGroup.mk xL
  let C : Subgroup c.Lbar := Subgroup.centralizer ({xb} : Set c.Lbar)
  let J : Subgroup c.Lbar := ⁅C, C⁆
  have hxL3 : orderOf xL = 3 := by rw [Subgroup.orderOf_mk, hx3]
  have hN2 : IsPGroup 2 ↥N := CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)
  have hxLnotN : xL ∉ N := by
    intro hxN
    have h3dvd : 3 ∣ Nat.card ↥N := by
      have h := orderOf_dvd_natCard (⟨xL, hxN⟩ : ↥N)
      rwa [Subgroup.orderOf_mk, hxL3] at h
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup hN2 Nat.prime_three (by norm_num) h3dvd
  have hxb3 : orderOf xb = 3 := by
    have hdvd : orderOf xb ∣ 3 := by
      have h := orderOf_map_dvd q xL
      rwa [hxL3] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      have hxb1 : xb = 1 := orderOf_eq_one_iff.mp h1
      exact hxLnotN ((QuotientGroup.eq_one_iff xL).mp hxb1)
    · exact h3
  have hxb_not_center : xb ∉ Subgroup.center c.Lbar := by
    intro hxbc
    apply hxZ
    refine ⟨hx, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    have hyP : y ∈ P := hy.1
    have hyL : y ∈ c.L := hy.2
    let yL : ↥c.L := ⟨y, hyL⟩
    have hcomm_bar : (QuotientGroup.mk yL : c.Lbar) * xb = xb * QuotientGroup.mk yL :=
      Subgroup.mem_center_iff.mp hxbc (QuotientGroup.mk yL)
    have hmemN : ⁅xL, yL⁆ ∈ N := by
      rw [← QuotientGroup.eq_one_iff (⁅xL, yL⁆)]
      show (QuotientGroup.mk' N) ⁅xL, yL⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm_bar.symm
    have hmemO : ⁅x, y⁆ ∈ N.map c.L.subtype :=
      Subgroup.mem_map.mpr ⟨⁅xL, yL⁆, hmemN, by
        simp only [Subgroup.coe_subtype, commutatorElement_def]
        rfl⟩
    have hmemP : ⁅x, y⁆ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem hx.1 hyP) (P.inv_mem hx.1)) (P.inv_mem hyP)
    have hO2 : IsPGroup 2 ↥(N.map c.L.subtype) := hN2.map c.L.subtype
    have hdisj : P ⊓ N.map c.L.subtype = ⊥ :=
      (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (N.map c.L.subtype)
        hP.isPGroup hO2).eq_bot
    have h1 : ⁅x, y⁆ = 1 := by
      have hmem : ⁅x, y⁆ ∈ P ⊓ N.map c.L.subtype := ⟨hmemP, hmemO⟩
      rwa [hdisj, Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  obtain ⟨-, hZleJ, hJcard, hCeq, hAlt⟩ := hK2 c.Lbar hON xb hxb3 hxb_not_center
  have hJcard' : Nat.card ↥J = 1080 := hJcard
  let Z : Subgroup c.Lbar := Subgroup.center c.Lbar
  let ZJ : Subgroup ↥J := Z.subgroupOf J
  obtain ⟨e⟩ := hAlt
  have hnotJ : ¬ CFSG.HallHigman.IsPSolvable 3 ↥J := by
    intro hJ
    let r : ↥J →* (↥J ⧸ ZJ) := QuotientGroup.mk' ZJ
    have hJtop : CFSG.HallHigman.IsPSolvable 3 ↥(⊤ : Subgroup ↥J) :=
      CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
        (Subgroup.topEquiv (G := ↥J)).symm hJ
    have hmap := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map
      r (N := ⊤) hJtop
    rw [Subgroup.map_top_of_surjective r (QuotientGroup.mk'_surjective ZJ)] at hmap
    have hQ : CFSG.HallHigman.IsPSolvable 3 (↥J ⧸ ZJ) :=
      CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
        (Subgroup.topEquiv (G := ↥J ⧸ ZJ)) hmap
    exact not_isPSolvable_three_alt_six
      (isPSolvable_of_mulEquiv
        e hQ)
  obtain ⟨f, hf⟩ := hSurj
  constructor
  · intro hsolv
    have htop : CFSG.HallHigman.IsPSolvable 3 ↥(⊤ : Subgroup ↥(pIbar x c.L)) :=
      CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
        (Subgroup.topEquiv (G := ↥(pIbar x c.L))).symm hsolv
    have hmap := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map
      f (N := ⊤) htop
    rw [Subgroup.map_top_of_surjective f hf] at hmap
    exact hnotJ
      (isPSolvable_of_mulEquiv
        (Subgroup.topEquiv (G := ↥J)) hmap)
  · constructor
    · have hle : Nat.card ↥J ≤ Nat.card ↥(pIbar x c.L) :=
        Nat.card_le_card_of_surjective f hf
      rw [hJcard'] at hle
      omega
    · exact hOpp

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

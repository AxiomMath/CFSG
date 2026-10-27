module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ComponentModO2Sup
public import CFSG.Quasithin.Vol2.Ch10SecC9S49d
public import CFSG.Quasithin.Background.F918V7

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isTwoReducedIn_of_hyp125_bot {D : Data G} {V : Subgroup G} (h : Hyp125 D ⊥ V) :
    IsTwoReducedIn D.M V := by
  have hpf := h.pairFacts
  have hred : TwoReduced D.M V := by
    rcases h.1 with ⟨hW, -⟩ | ⟨h0, -⟩
    · exact hW.1.2.2
    · exact absurd rfl h0.1.1
  refine ⟨hpf.le_M, hpf.le_normalizer, h.isElemAbelian, ?_⟩
  intro Dsub hDM hMD hD
  have hfact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer (V : Set G) with hC
  set K : Subgroup G := Dsub ⊔ C with hK
  have hCM : C ≤ D.M := by
    rw [hC, ← h.normalizer_eq]
    exact Subgroup.centralizer_le_normalizer (V : Set G)
  have hCD : C ≤ Subgroup.normalizer (Dsub : Set G) := hCM.trans hMD
  have hDsubC : Dsub ≤ Subgroup.normalizer (C : Set G) :=
    hDM.trans (A1a.le_normalizer_centralizer hpf.le_normalizer)
  have hCK : K ≤ Subgroup.normalizer (C : Set G) :=
    sup_le hDsubC Subgroup.le_normalizer
  have hKM : K ≤ D.M := sup_le hDM hCM
  have hNK : D.M ≤ Subgroup.normalizer (K : Set G) :=
    A1a.le_normalizer_sup hMD (A1a.le_normalizer_centralizer hpf.le_normalizer)
  have hCKnormal : (C.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 hCK
  have hidx : ∃ n : ℕ, (C.subgroupOf K).index = 2 ^ n := by
    have hquot : IsPGroup 2 (↥K ⧸ (C.subgroupOf K)) := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro x
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
      have hmem : (k : G) ∈ (↑Dsub : Set G) * (↑C : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left Dsub C hCD]
        exact k.2
      obtain ⟨d, hd, c, hc, hdc⟩ := Set.mem_mul.mp hmem
      obtain ⟨n, hn⟩ := hD d hd
      refine ⟨n, ?_⟩
      have hdk : d ∈ K := Subgroup.mem_sup_left hd
      have hck : c ∈ K := Subgroup.mem_sup_right hc
      have hk : k = (⟨d, hdk⟩ : ↥K) * ⟨c, hck⟩ := Subtype.ext (by simpa using hdc.symm)
      have hc1 : QuotientGroup.mk' (C.subgroupOf K) (⟨c, hck⟩ : ↥K) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hc
      change QuotientGroup.mk' (C.subgroupOf K) k ^ 2 ^ n = 1
      rw [hk, map_mul, hc1, mul_one, ← map_pow, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact hn
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hquot
    exact ⟨n, by rw [Subgroup.index_eq_card, hn]⟩
  have hKC : K ≤ C := hred K hKM hNK (inf_le_right.trans le_sup_right) hidx
  intro d hd
  exact hKC (Subgroup.mem_sup_left hd)

theorem barSub_jOf_le_ffJ {D : Data G} {V : Subgroup G} (h : Hyp125 D ⊥ V) :
    barSub ⊥ V h.isElemAbelian (F12.jOf D.T) ≤ ffJ (Mbar D.M ⊥ V h.isElemAbelian) := by
  have hfact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf D.T D.M := by
    obtain ⟨hle, hP, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM
    exact ⟨hle, hP, hdvd⟩
  have hjOf : F12.jOf D.T = thompsonJ D.T := by
    rw [F12.jOf, CFSG.inSubgroup, elemThompson_map_subtype_eq_thompsonJ]
  have h1 : autI h.isElemAbelian (thompsonJ D.T) ≤ ffJ (autI h.isElemAbelian D.M) :=
    CFSG.Quasithin.Vol2.Ch10.SecC.autI_thompsonJ_le_ffJ h.isElemAbelian
      (isTwoReducedIn_of_hyp125_bot h) hS
  have hMbar : Mbar D.M ⊥ V h.isElemAbelian =
      (autI h.isElemAbelian D.M).map
        (MulAut.congr (TwelveShort.mkTilEquiv V h.isElemAbelian)).toMonoidHom :=
    TwelveTwentyThree.barSub_bot_eq_map_autI V h.isElemAbelian D.M
  rw [hjOf, TwelveTwentyThree.barSub_bot_eq_map_autI V h.isElemAbelian (thompsonJ D.T),
    hMbar, ffJ_map_mulAutCongr]
  exact Subgroup.map_mono h1

theorem barSub_conjClosure_sup_pCoreOf {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {L : Subgroup G} (hLM : L ≤ D.M) :
    barSub V₀ V h.isElemAbelian (UC22.conjClosure D.M (L ⊔ pCoreOf 2 D.M)) =
      barSub V₀ V h.isElemAbelian (UC22.conjClosure D.M L) := by
  have hEq : UC22.conjClosure D.M (L ⊔ pCoreOf 2 D.M) =
      UC22.conjClosure D.M L ⊔ pCoreOf 2 D.M := by
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun K hK => ?_
      obtain ⟨g, hg, rfl⟩ := hK
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · exact (le_iSup₂_of_le (f := fun K (_ : K ∈ UC22.conjSetOf D.M L) => K)
          _ ⟨g, hg, rfl⟩ le_rfl).trans le_sup_left
      · have hgA : (pCoreOf 2 D.M).map (MulAut.conj g).toMonoidHom = pCoreOf 2 D.M :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M hg)
        rw [hgA]
        exact le_sup_right
    · refine sup_le ?_ ?_
      · refine iSup₂_le fun K hK => ?_
        obtain ⟨g, hg, rfl⟩ := hK
        exact le_iSup₂_of_le
          (f := fun K (_ : K ∈ UC22.conjSetOf D.M (L ⊔ pCoreOf 2 D.M)) => K)
          ((L ⊔ pCoreOf 2 D.M).map (MulAut.conj g).toMonoidHom) ⟨g, hg, rfl⟩
          (Subgroup.map_mono le_sup_left)
      · exact le_sup_right.trans
          (TwelveTwentyThree.le_conjClosure D.M (L ⊔ pCoreOf 2 D.M))
  rw [hEq, barSub_sup_pCoreOf_eq_of_hyp125 h (TwelveTwentyThree.conjClosure_le hLM)]

theorem commPset_eq_of_isComponentOf {W : Type} [CommGroup W] [Finite W]
    {Y L X : Subgroup (MulAut W)} (hL : IsComponentOf L Y) (hXY : X ≤ Y)
    (hXn : (X.subgroupOf Y).Normal) (hXg : X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom)
    (hA : ∃ A ∈ Pset Y, ⁅A, L⁆ ≠ ⊥) : commPset Y X = X := by
  obtain ⟨N, hN⟩ : ∃ N : Subgroup (MulAut W), N = commPset Y X := ⟨_, rfl⟩
  rw [← hN]
  have hYnorm : Y ≤ Subgroup.normalizer (X : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXY).1 hXn
  have hNX : N ≤ X := by
    rw [hN]
    refine iSup₂_le fun A hA => ?_
    rw [Subgroup.commutator_le]
    intro a ha x hx
    have hnorm : a ∈ Subgroup.normalizer (X : Set (MulAut W)) := hYnorm (hA.1 ha)
    exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp hnorm x).mp hx) (X.inv_mem hx)
  have hcomm : N = ⨆ A : {A : Subgroup (MulAut W) // A ∈ Pset Y},
      ⁅(A : Subgroup (MulAut W)), X⁆ := by
    rw [hN]
    unfold commPset
    rw [iSup_subtype']
  have hcomm' : N = ⨆ (A : Subgroup (MulAut W)) (_ : A ∈ Pset Y), ⁅A, X⁆ := by
    rw [hcomm, iSup_subtype']
  have key : ∀ z ∈ Y, N.map (MulAut.conj z).toMonoidHom ≤ N := by
    intro z hz
    have hXz : X.map (MulAut.conj z).toMonoidHom = X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYnorm hz)
    rw [hcomm, Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_commutator]
    refine (Subgroup.commutator_mono le_rfl (le_of_eq hXz)).trans ?_
    exact le_iSup (fun A' : {A : Subgroup (MulAut W) // A ∈ Pset Y} =>
      ⁅(A' : Subgroup (MulAut W)), X⁆)
      ⟨A.1.map (MulAut.conj z).toMonoidHom, isFFStarOffender_map_conj A.2 hz⟩
  have hNY : Y ≤ Subgroup.normalizer (N : Set (MulAut W)) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hcomp : ((MulAut.conj y).toMonoidHom.comp (MulAut.conj y⁻¹).toMonoidHom) =
        MonoidHom.id (MulAut W) := by
      ext z w
      simp [MulAut.conj_apply]
    refine le_antisymm (key y hy) ?_
    calc N = N.map
          ((MulAut.conj y).toMonoidHom.comp (MulAut.conj y⁻¹).toMonoidHom) := by
          rw [hcomp, Subgroup.map_id]
      _ = (N.map (MulAut.conj y⁻¹).toMonoidHom).map
            (MulAut.conj y).toMonoidHom := by rw [Subgroup.map_map]
      _ ≤ N.map (MulAut.conj y).toMonoidHom :=
          Subgroup.map_mono (key y⁻¹ (Y.inv_mem hy))
  have hsub : IsSubnormal N Y :=
    A3.subnormal_of_normal (hNX.trans hXY)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hNX.trans hXY)).2 hNY)
  have hLX : L ≤ X := by
    rw [hXg]
    have hone : (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) := by
      ext z w
      simp [MulAut.conj_apply]
    have hL1 : L.map (MulAut.conj (1 : MulAut W)).toMonoidHom = L := by
      rw [hone, Subgroup.map_id]
    calc L = L.map (MulAut.conj (1 : MulAut W)).toMonoidHom := hL1.symm
      _ ≤ ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom :=
          le_iSup₂_of_le (f := fun K (_ : K ∈ Y) => L.map (MulAut.conj K).toMonoidHom)
            1 Y.one_mem le_rfl
  rcases B113.component_le_or_commutator_eq_bot hL hsub with hLN | hNL
  · have hXN : X ≤ N := by
      have h : (⨆ (g : MulAut W) (_ : g ∈ Y), L.map (MulAut.conj g).toMonoidHom) ≤ N := by
        refine iSup₂_le fun g hg => ?_
        calc L.map (MulAut.conj g).toMonoidHom ≤ N.map (MulAut.conj g).toMonoidHom :=
              Subgroup.map_mono hLN
          _ = N := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNY hg)
      rwa [← hXg] at h
    exact le_antisymm hNX hXN
  · exfalso
    obtain ⟨B, hB, hBL⟩ := hA
    have hAX : ⁅B, X⁆ ≤ N := by
      have h := le_iSup₂_of_le (f := fun A (_ : A ∈ Pset Y) => ⁅A, X⁆) B hB le_rfl
      rwa [← hcomm'] at h
    have hNL' : ⁅N, L⁆ = ⊥ := by
      rwa [Subgroup.commutator_comm (H₁ := L) (H₂ := N)] at hNL
    have hmono : ⁅⁅B, L⁆, L⁆ ≤ ⁅N, L⁆ :=
      (Subgroup.commutator_mono (Subgroup.commutator_mono_right hLX) (le_refl L)).trans
        (Subgroup.commutator_mono hAX (le_refl L))
    have h1 : ⁅⁅B, L⁆, L⁆ = ⊥ := by
      have hle := hmono
      rw [hNL'] at hle
      exact le_bot_iff.1 hle
    have h2 : ⁅⁅L, B⁆, L⁆ = ⊥ := by
      rwa [Subgroup.commutator_comm (H₁ := B) (H₂ := L)] at h1
    have hrot : ⁅⁅L, L⁆, B⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := L) (H₂ := L) (H₃ := B) h2 h1
    have hPerf : Group.IsPerfect ↥L := (Group.isPerfect_def).2 hL.2.2.1
    have hLL : ⁅L, L⁆ = L := (Subgroup.isPerfect_iff).mp hPerf
    rw [hLL] at hrot
    exact hBL (by rwa [Subgroup.commutator_comm] at hrot)

theorem fixV_or_commPset_of_hyp18 (D : Data G) (h640 : UC6.R6_40_2 D)
    (hFF : W4Thm12McClurg) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hUL : UniqueMax D.M L)
    (hLb : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥) :
    fixV (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ ∨
      commPset (Mbar D.M V₀ V h.hyp125.isElemAbelian)
        (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) =
        barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) := by
  have hLM : L ≤ D.M := h.hL.1.1.le
  have hcomp : F12.IsComponentModO2 D.M (L ⊔ pCoreOf 2 D.M) :=
    isComponentModO2_sup_pCoreOf_of_mem_calC h.hL.1
  have hU : UniqueMax D.M ((L ⊔ pCoreOf 2 D.M) ⊔ D.T) :=
    uc22p22u_uniqueMax_mono D
      ((le_sup_left : L ≤ L ⊔ pCoreOf 2 D.M).trans le_sup_left)
      (sup_le (sup_le hLM (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)) D.sylowM.le) hUL
  have hbar : barSub V₀ V h.hyp125.isElemAbelian
      (UC22.conjClosure D.M (L ⊔ pCoreOf 2 D.M)) =
      barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) :=
    barSub_conjClosure_sup_pCoreOf h.hyp125 hLM
  have hH : barSub V₀ V h.hyp125.isElemAbelian
      (UC22.conjClosure D.M (L ⊔ pCoreOf 2 D.M)) ≠ ⊥ := by
    rw [hbar]
    exact TwelveTwentyThree.barSub_conjClosure_ne_bot h.hyp125.isElemAbelian hLb
  rcases eq_or_ne V₀ ⊥ with rfl | hV0ne
  ·
    rcases twelve_twentySix D h640 hFF h.hyp125 hcomp hU hH with hfix | ⟨-, -, hJ⟩
    · left
      rwa [hbar] at hfix
    · right
      have hKbar : barSub ⊥ V h.hyp125.isElemAbelian (L ⊔ pCoreOf 2 D.M) =
          barSub ⊥ V h.hyp125.isElemAbelian L :=
        barSub_sup_pCoreOf_eq_of_hyp125 h.hyp125 hLM
      have hJ' : ⁅barSub ⊥ V h.hyp125.isElemAbelian (F12.jOf D.T),
          barSub ⊥ V h.hyp125.isElemAbelian L⁆ ≠ ⊥ := by
        rwa [hKbar] at hJ
      have hJle : barSub ⊥ V h.hyp125.isElemAbelian (F12.jOf D.T) ≤
          ffJ (Mbar D.M ⊥ V h.hyp125.isElemAbelian) :=
        barSub_jOf_le_ffJ h.hyp125
      have hA : ∃ A ∈ Pset (Mbar D.M ⊥ V h.hyp125.isElemAbelian),
          ⁅A, barSub ⊥ V h.hyp125.isElemAbelian L⁆ ≠ ⊥ := by
        by_contra hcon
        push Not at hcon
        have hffJ : ffJ (Mbar D.M ⊥ V h.hyp125.isElemAbelian) ≤
            Subgroup.centralizer
              (barSub ⊥ V h.hyp125.isElemAbelian L :
                Set (MulAut (Vtil ⊥ V h.hyp125.isElemAbelian))) := by
          refine iSup₂_le fun A hA => ?_
          exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 (hcon A hA)
        have hbot : ⁅barSub ⊥ V h.hyp125.isElemAbelian (F12.jOf D.T),
            barSub ⊥ V h.hyp125.isElemAbelian L⁆ = ⊥ := by
          refine le_bot_iff.1 ?_
          calc ⁅barSub ⊥ V h.hyp125.isElemAbelian (F12.jOf D.T),
                barSub ⊥ V h.hyp125.isElemAbelian L⁆
              ≤ ⁅ffJ (Mbar D.M ⊥ V h.hyp125.isElemAbelian),
                  barSub ⊥ V h.hyp125.isElemAbelian L⁆ :=
                Subgroup.commutator_mono hJle le_rfl
            _ = ⊥ := (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hffJ
        exact hJ' hbot
      have hcomp2 : IsComponentOf (barSub ⊥ V h.hyp125.isElemAbelian L)
          (Mbar D.M ⊥ V h.hyp125.isElemAbelian) :=
        barSub_mem_compBar_of_ne_bot h.hyp125 h.hL.1 hLb
      have hXY : barSub ⊥ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ≤
          Mbar D.M ⊥ V h.hyp125.isElemAbelian :=
        barSub_mono ⊥ V h.hyp125.isElemAbelian (TwelveTwentyThree.conjClosure_le hLM)
      have hXn : ((barSub ⊥ V h.hyp125.isElemAbelian
          (UC22.conjClosure D.M L)).subgroupOf
            (Mbar D.M ⊥ V h.hyp125.isElemAbelian)).Normal :=
        barSub_subgroupOf_mbar_normal h.hyp125.isElemAbelian
          (TwelveTwentyThree.conjClosure_le hLM)
          (TwelveTwentyThree.le_normalizer_conjClosure D.M L)
      have hXg : barSub ⊥ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) =
          ⨆ g ∈ Mbar D.M ⊥ V h.hyp125.isElemAbelian,
            (barSub ⊥ V h.hyp125.isElemAbelian L).map
              (MulAut.conj g).toMonoidHom := by
        rw [barSub_conjClosure_eq_iSup h, iSup_subtype']
      exact commPset_eq_of_isComponentOf hcomp2 hXY hXn hXg hA
  ·
    left
    rcases twelve_twentySix D h640 hFF h.hyp125 hcomp hU hH with hfix | ⟨hbot, -⟩
    · rwa [hbar] at hfix
    · exact absurd hbot hV0ne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

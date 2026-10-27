module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.BarOfInterTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactA7Offender
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeRadical
public import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPL
public import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPLAux
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Setting
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeAltSeven
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeAltSevenSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSixteenSetting
public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofCensus194

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.AGLEmbedding
open CFSG.AGLEmbedding.AltSevenInv
open CFSG.AGLEmbedding.BlockAltSevenPL
open CFSG.Quasithin
open CFSG.QuasithinUnique
open CFSG.QuasithinUnique.C5
open CFSG.RankThree.PartTwo.Sec19.Item19Res3Proof (barMEquiv starImEquiv)

variable {G : Type} [Group G] [Finite G]

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G} {B : Subgroup G}
  {r : ℕ} {Y N Dsub H S : Subgroup G}

theorem p19_16_of_nineThreeFive
    (h85 : CFSG.AGLEmbedding.Asc81bEightFive)
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h11 : R19_11At D V₀ V p L A t B r h.ctx)
    (h15 : R19_15At D V₀ V p L A t B r Y N Dsub H S h)
    (h5 : CFSG.AGLEmbedding.NineThreeFive H Dsub) : P19_16 D Dsub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsh, ⟨eH⟩, hU⟩ := h5
  have hX := ctx19_14_isKGroup h
  have hhyp := ctx19_14_asc81bHyp h h11
  have hK := ctx19_14_isWeakSBlock h h11
  have hKc := hK.toIsTwoPrimeComponent
  have hnotX : ¬ CFSG.AGLEmbedding.InClassXBlock Dsub :=
    ctx19_14_not_inClassXBlock h h15
  have hnotSyl : ¬ IsSylowTwoOf (S ⊓ Dsub) Dsub := fun hs =>
    hnotX (h85 G H S Dsub hX hhyp hKc hs)
  have h86 : CFSG.AGLEmbedding.Asc81bEightSix :=
    CFSG.AGLEmbedding.asc81bEightSix_of_bhs
      CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have hSL : S ≤ Subgroup.normalizer (Dsub : Set G) :=
    hKc.le_normalizer (h86 G H S hX hhyp _ hKc.component) hhyp.twoRadical.1
  set Nn : Subgroup G := Subgroup.normalizer (Dsub : Set G) with hNndef
  have hLN : Dsub ≤ Nn := Subgroup.le_normalizer
  have hNU : Nn ≤ Subgroup.normalizer (blockU Dsub : Set G) := fun _ hg =>
    CFSG.QuasithinUnique.C1.mem_normalizer_blockU hg
  set ρ : ↥Nn →* MulAut ↥(blockU Dsub) :=
    (blockU Dsub).normalizerMonoidHom.comp (Subgroup.inclusion hNU) with hρdef
  have hρ : ∀ (n : ↥Nn) (u : ↥(blockU Dsub)),
      ((ρ n u : ↥(blockU Dsub)) : G) = n * u * n⁻¹ := fun _ _ => rfl
  obtain ⟨hΓ, hΓs⟩ := card_mulAut_eq_and_isSimpleGroup (W := ↥(blockU Dsub))
    (fun a b => Subtype.ext (CFSG.QuasithinUnique.C1.blockU_comm hsh a a.2 b
      (CFSG.QuasithinUnique.C1.blockU_le_blockQ hsh b.2)))
    (fun a => Subtype.ext (CFSG.QuasithinUnique.C1.blockU_sq hsh a a.2)) hU
  have : Finite (MulAut ↥(blockU Dsub)) := Nat.finite_of_card_ne_zero (by rw [hΓ]; norm_num)
  set π : ↥Dsub →* ↥H ⧸ CFSG.pCore 2 ↥H :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hKc.le) with hπdef
  set ρL : ↥Dsub →* MulAut ↥(blockU Dsub) := ρ.comp (Subgroup.inclusion hLN) with hρLdef
  have hker : π.ker = ρL.ker := by
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have e1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (Subgroup.inclusion hKc.le l) = 1 ↔
        Subgroup.inclusion hKc.le l ∈ CFSG.pCore 2 ↥H := QuotientGroup.eq_one_iff _
    change QuotientGroup.mk' _ (Subgroup.inclusion hKc.le l) = 1 ↔ ρ ⟨l, hLN l.2⟩ = 1
    rw [e1, CFSG.AGLEmbedding.BlockAltSevenPL.conj_eq_one_iff_mem_pCoreOf hsh hρ
      (n := ⟨l, hLN l.2⟩) l.2, ← hKc.inf_twoCore]
    constructor
    · intro h
      have h' : (l : G) ∈ (CFSG.pCore 2 ↥H).map H.subtype := ⟨_, h, rfl⟩
      exact ⟨l.2, h'⟩
    · rintro ⟨-, m, hm, hml⟩
      rw [show Subgroup.inclusion hKc.le l = m from Subtype.ext hml.symm]
      exact hm
  have hbar : ∀ X : Subgroup G, X ≤ Dsub → barM H X = (X.subgroupOf Dsub).map π :=
    fun X hXL => by
      rw [barM, ← map_inclusion_subgroupOf hXL hKc.le, Subgroup.map_map]
  have himg : ∀ X : Subgroup G, X ≤ Dsub →
      (X.subgroupOf Dsub).map ρL = (X.subgroupOf Nn).map ρ :=
    fun X hXL => by rw [← Subgroup.map_map, map_inclusion_subgroupOf hXL hLN]
  set Hb : Subgroup (MulAut ↥(blockU Dsub)) := (Dsub.subgroupOf Nn).map ρ with hHbdef
  obtain ⟨θ₀⟩ := nonempty_mulEquiv_range_of_ker_eq hker
  have hHr : ρL.range = Hb := by
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self Dsub, himg Dsub le_rfl]
  have hπr : π.range = barM H Dsub := by
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self Dsub, hbar Dsub le_rfl]
  let θ : ↥Hb ≃* alternatingGroup (Fin 7) :=
    (MulEquiv.subgroupCongr hHr.symm).trans
      (θ₀.symm.trans ((MulEquiv.subgroupCongr hπr).trans eH))
  have hHcard : Nat.card Hb = 2520 := by
    rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hNH : ∀ n : ↥Nn, ρ n ∈ Hb := fun n => by
    have hn : Subgroup.normalizer ((Dsub.subgroupOf Nn : Subgroup ↥Nn) : Set ↥Nn) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_in_normalizer
    exact mem_of_mem_normalizer_of_index_eight hΓ hHcard
      (Subgroup.le_normalizer_map ρ ⟨n, by rw [hn]; trivial, rfl⟩)
  set T : Subgroup (MulAut ↥(blockU Dsub)) := (S.subgroupOf Nn).map ρ with hTdef
  set P : Subgroup (MulAut ↥(blockU Dsub)) :=
    ((Subgroup.normalizer (S : Set G) ⊓ Dsub).subgroupOf Nn).map ρ with hPdef
  have hTH : T ≤ Hb := by
    rintro _ ⟨n, -, rfl⟩
    exact hNH n
  have hPH : P ≤ Hb := by
    rintro _ ⟨n, -, rfl⟩
    exact hNH n
  have hT2 : IsPGroup 2 T := (hhyp.twoRadical.isPGroup.comap_subtype (K := Nn)).map ρ
  have hT1 : T ≠ ⊥ := by
    obtain ⟨s, hs, hρs⟩ := CFSG.AGLEmbedding.BlockAltSevenPL.exists_mem_conj_blockU_ne_one
      hhyp hK hsh hρ hSL
    intro hbot
    have hmem : ρ ⟨s, hSL hs⟩ ∈ T := ⟨⟨s, hSL hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hρs hmem
  have hkerρ : ∀ n : ↥Nn, ρ n = 1 → (n : G) ∈ Subgroup.centralizer (blockU Dsub : Set G) := by
    intro n h1
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h2 := congrArg (fun φ : MulAut ↥(blockU Dsub) =>
      ((φ ⟨u, hu⟩ : ↥(blockU Dsub)) : G)) h1
    simp only [hρ, MulAut.one_apply, Subgroup.coe_inv] at h2
    calc u * n = (n * u * (n : G)⁻¹) * n := by rw [h2]
      _ = n * u := by group
  have hW := CFSG.AGLEmbedding.BlockInvThree.inf_centralizer_blockU_le_S hhyp hKc hsh hSL
  have hPleN : P ≤ Subgroup.normalizer (T : Set (MulAut ↥(blockU Dsub))) := by
    refine le_trans (Subgroup.map_mono fun n hn => ?_) (Subgroup.le_normalizer_map ρ)
    rw [← Subgroup.subgroupOf_normalizer_eq hSL]
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hn).1
  have hNPleP : Subgroup.normalizer (T : Set (MulAut ↥(blockU Dsub))) ⊓ Hb ≤ P := by
    rintro h ⟨hhT, ⟨n, hnL, rfl⟩⟩
    have hnL' : (n : G) ∈ Dsub := Subgroup.mem_subgroupOf.mp hnL
    refine ⟨n, Subgroup.mem_subgroupOf.mpr ⟨?_, hnL'⟩, rfl⟩
    apply Subgroup.mem_normalizer_fintype
    intro s hs
    have hsN : s ∈ Nn := hSL hs
    have himgT : ρ n * ρ ⟨s, hsN⟩ * (ρ n)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp hhT _).mp
        ⟨⟨s, hsN⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    obtain ⟨s', hs', hs'e⟩ := himgT
    have hs'S : (s' : G) ∈ S := Subgroup.mem_subgroupOf.mp hs'
    set w : ↥Nn := s'⁻¹ * (n * ⟨s, hsN⟩ * n⁻¹) with hwdef
    have hw1 : ρ w = 1 := by
      rw [hwdef, map_mul, map_inv, hs'e, map_mul, map_mul, map_inv, inv_mul_cancel]
    have hwC := hkerρ w hw1
    have hwLS : (w : G) ∈ Dsub ⊔ S := by
      have e2 : (w : G) = (s' : G)⁻¹ * ((n : G) * s * (n : G)⁻¹) := by
        simp [hwdef]
      rw [e2]
      refine (Dsub ⊔ S).mul_mem ((Dsub ⊔ S).inv_mem (Subgroup.mem_sup_right hs'S)) ?_
      exact (Dsub ⊔ S).mul_mem
        ((Dsub ⊔ S).mul_mem (Subgroup.mem_sup_left hnL') (Subgroup.mem_sup_right hs))
        ((Dsub ⊔ S).inv_mem (Subgroup.mem_sup_left hnL'))
    have hwS : (w : G) ∈ S := hW ⟨hwLS, hwC⟩
    have e3 : (n : G) * s * (n : G)⁻¹ = (s' : G) * w := by
      simp [hwdef]
    rw [e3]
    exact S.mul_mem hs'S hwS
  have hPiso : Nonempty (↥(barM H (Subgroup.normalizer (S : Set G) ⊓ Dsub)) ≃* ↥P) := by
    set X := (Subgroup.normalizer (S : Set G) ⊓ Dsub).subgroupOf Dsub
    have hk : (π.domRestrict X).ker = (ρL.domRestrict X).ker := by
      rw [MonoidHom.ker_domRestrict, MonoidHom.ker_domRestrict, hker]
    obtain ⟨φ⟩ := nonempty_mulEquiv_range_of_ker_eq hk
    have h1 : (π.domRestrict X).range = barM H (Subgroup.normalizer (S : Set G) ⊓ Dsub) := by
      rw [MonoidHom.domRestrict_range, hbar _ inf_le_right]
    have h2 : (ρL.domRestrict X).range = P := by
      rw [MonoidHom.domRestrict_range, himg _ inf_le_right]
    exact ⟨(MulEquiv.subgroupCongr h1.symm).trans (φ.trans (MulEquiv.subgroupCongr h2))⟩
  obtain ⟨ψ⟩ := hPiso
  have hPnot : ¬ IsPGroup 2 P := fun h2 =>
    CFSG.AGLEmbedding.not_isPGroup_blockPL h86 hX hhyp hK hnotSyl (h2.of_equiv ψ.symm)
  have hPeq : P = Subgroup.normalizer (T : Set (MulAut ↥(blockU Dsub))) ⊓ Hb :=
    le_antisymm (le_inf hPleN hPH) hNPleP
  letI : CommGroup ↥(blockU Dsub) :=
    { (inferInstance : Group ↥(blockU Dsub)) with
      mul_comm := fun a b =>
        Subtype.ext (CFSG.QuasithinUnique.C1.blockU_comm hsh a a.2 b
          (CFSG.QuasithinUnique.C1.blockU_le_blockQ hsh b.2)) }
  have hO2LleH : pCoreOf 2 Dsub ≤ pCoreOf 2 H := by
    rw [← hKc.inf_twoCore]
    exact inf_le_right
  have hUleS : blockU Dsub ≤ S :=
    (CFSG.QuasithinUnique.C1.blockU_le_blockQ hsh).trans
      (hO2LleH.trans hhyp.twoCore_le)
  have hCQ : (Dsub ⊔ S) ⊓ Subgroup.centralizer (blockU Dsub : Set G) ≤
      pCoreOf 2 (Dsub ⊔ S) := by
    refine CFSG.QuasithinUnique.C1.le_pCoreOf_of_normalized inf_le_left ?_
      (CFSG.AGLEmbedding.BlockInvThree.isPGroup_inf_centralizer_blockU hsh
        hhyp.twoRadical.isPGroup hSL)
    intro x hx
    refine mem_normalizer_inf (Subgroup.le_normalizer hx) ?_
    exact mem_normalizer_centralizer
      (CFSG.QuasithinUnique.C1.mem_normalizer_blockU
        ((sup_le Subgroup.le_normalizer hSL) hx))
  obtain ⟨Aoff, hAmax, hAQ⟩ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.exists_isMaxElemAbelian_not_le hhyp hK hSL
  have hAS : Aoff ≤ S := hAmax.1
  have hAN : Aoff ≤ Nn := hAS.trans hSL
  have hA2 : IsElemAbelian 2 Aoff := hAmax.2.1
  set E : Subgroup (MulAut ↥(blockU Dsub)) := (Aoff.subgroupOf Nn).map ρ with hEdef
  have hEH : E ≤ Hb := by
    rintro _ ⟨a, -, rfl⟩
    exact hNH a
  have hE2 : IsElemAbelian 2 E := by
    have hsub : IsElemAbelian 2 (Aoff.subgroupOf Nn) := hA2.subgroupOf Nn
    exact hsub.map ρ
  have hE1 : E ≠ ⊥ := by
    intro hbot
    apply hAQ
    intro a ha
    have haN : a ∈ Nn := hAN ha
    have hmem : ρ ⟨a, haN⟩ ∈ E :=
      ⟨⟨a, haN⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hC : a ∈ (Dsub ⊔ S) ⊓ Subgroup.centralizer (blockU Dsub : Set G) :=
      ⟨Subgroup.mem_sup_right (hAS ha), hkerρ ⟨a, haN⟩ hmem⟩
    exact hCQ hC
  have hoff : Nat.card ↥(blockU Dsub) ≤ Nat.card E * Nat.card (fixV E) := by
    set CAU : Subgroup G := Aoff ⊓ Subgroup.centralizer (blockU Dsub : Set G) with hCAUdef
    set CU : Subgroup G := blockU Dsub ⊓ Subgroup.centralizer (Aoff : Set G) with hCUdef
    have hCAU2 : IsElemAbelian 2 CAU := hA2.mono inf_le_left
    have hUelem : IsElemAbelian 2 (blockU Dsub) :=
      ⟨⟨⟨fun a b => Subtype.ext (CFSG.QuasithinUnique.C1.blockU_comm hsh a a.2 b
        (CFSG.QuasithinUnique.C1.blockU_le_blockQ hsh b.2))⟩⟩,
        fun x hx => CFSG.QuasithinUnique.C1.blockU_sq hsh x hx⟩
    have hcomm : ∀ a ∈ CAU, ∀ b ∈ blockU Dsub, a * b = b * a := fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.mp ha.2 b hb).symm
    have hCUelem : IsElemAbelian 2 (CAU ⊔ blockU Dsub) :=
      IsElemAbelian.sup_of_commute hCAU2 hUelem hcomm
    have hCUS : CAU ⊔ blockU Dsub ≤ S :=
      sup_le (inf_le_left.trans hAmax.1) hUleS
    have hmax : Nat.card ↥(CAU ⊔ blockU Dsub) ≤ Nat.card ↥Aoff :=
      hAmax.2.2 (CAU ⊔ blockU Dsub) hCUS hCUelem
    have hinf : CAU ⊓ blockU Dsub = Aoff ⊓ blockU Dsub := by
      ext x
      constructor
      · rintro ⟨⟨hx1, -⟩, hx2⟩
        exact ⟨hx1, hx2⟩
      · rintro ⟨hx1, hx2⟩
        refine ⟨⟨hx1, ?_⟩, hx2⟩
        change x ∈ Subgroup.centralizer (blockU Dsub : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (CFSG.QuasithinUnique.C1.blockU_comm hsh x hx2 y
          (CFSG.QuasithinUnique.C1.blockU_le_blockQ hsh hy)).symm
    have hleCU : Aoff ⊓ blockU Dsub ≤ CU := by
      rintro x ⟨hx1, hx2⟩
      refine ⟨hx2, ?_⟩
      change x ∈ Subgroup.centralizer (Aoff : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hA2.comm hx1 hy).symm
    have hCUcard : Nat.card ↥(Aoff ⊓ blockU Dsub) ≤ Nat.card ↥CU :=
      Subgroup.card_le_of_le hleCU
    have hkey : Nat.card CAU * Nat.card (blockU Dsub) ≤
        Nat.card Aoff * Nat.card CU := by
      have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute CAU (blockU Dsub) hcomm).1
      rw [hinf] at hc
      calc Nat.card CAU * Nat.card (blockU Dsub)
          = Nat.card ↥(CAU ⊔ blockU Dsub) * Nat.card ↥(Aoff ⊓ blockU Dsub) := hc.symm
        _ ≤ Nat.card Aoff * Nat.card ↥(Aoff ⊓ blockU Dsub) :=
            Nat.mul_le_mul_right _ hmax
        _ ≤ Nat.card Aoff * Nat.card CU := Nat.mul_le_mul_left _ hCUcard
    have hkerA : Nat.card CAU * Nat.card E = Nat.card Aoff := by
      let f : ↥Aoff →* MulAut ↥(blockU Dsub) := ρ.comp (Subgroup.inclusion hAN)
      have hkerf : f.ker = CAU.subgroupOf Aoff := by
        ext a
        rw [MonoidHom.mem_ker]
        change ρ ⟨a, hAN a.2⟩ = 1 ↔ (a : G) ∈ CAU
        rw [hCAUdef]
        constructor
        · intro h1
          exact ⟨a.2, hkerρ ⟨a, hAN a.2⟩ h1⟩
        · rintro ⟨-, hc⟩
          refine MulEquiv.ext fun u => Subtype.ext ?_
          rw [MulAut.one_apply, hρ]
          have hu := Subgroup.mem_centralizer_iff.mp hc u u.2
          calc (a : G) * (u : G) * (a : G)⁻¹ = ((u : G) * a) * (a : G)⁻¹ := by rw [hu]
            _ = (u : G) := by group
      have hrange : f.range = E := by
        rw [MonoidHom.range_eq_map]
        ext x
        constructor
        · rintro ⟨a, -, rfl⟩
          exact ⟨⟨a, hAN a.2⟩, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
        · rintro ⟨b, hb, rfl⟩
          refine ⟨⟨(b : G), Subgroup.mem_subgroupOf.mp hb⟩, Subgroup.mem_top _, ?_⟩
          exact congrArg ρ (Subtype.ext rfl)
      have h := Subgroup.card_ker_mul_card_range f
      rw [hkerf, hrange] at h
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
    have hfixmap : (fixV E).map (blockU Dsub).subtype = CU := by
      ext u
      constructor
      · intro hu
        obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
        refine ⟨v.2, ?_⟩
        change (v : G) ∈ Subgroup.centralizer (Aoff : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have hfix := (mem_fixV.mp hv) (ρ ⟨a, hAN ha⟩)
          ⟨⟨a, hAN ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
        have hcoe : ((ρ ⟨a, hAN ha⟩ v : ↥(blockU Dsub)) : G) = a * (v : G) * a⁻¹ := hρ _ _
        have hval := congrArg (fun w : ↥(blockU Dsub) => (w : G)) hfix
        rw [hcoe] at hval
        calc a * (v : G) = (a * (v : G) * a⁻¹) * a := by group
          _ = (v : G) * a := by rw [hval]
      · rintro ⟨huU, huC⟩
        refine Subgroup.mem_map.mpr ⟨⟨u, huU⟩, ?_, rfl⟩
        rw [mem_fixV]
        rintro e ⟨a, ha, rfl⟩
        apply Subtype.ext
        rw [hρ]
        have hu := Subgroup.mem_centralizer_iff.mp huC a ha
        show (a : G) * u * (a : G)⁻¹ = u
        calc (a : G) * u * (a : G)⁻¹ = (u * (a : G)) * (a : G)⁻¹ := by rw [hu]
          _ = u := by group
    have hfixcard : Nat.card (fixV E) = Nat.card CU := by
      rw [← Subgroup.card_map_of_injective (blockU Dsub).subtype_injective, hfixmap]
    have hkey' : Nat.card CAU * Nat.card (blockU Dsub) ≤
        Nat.card CAU * (Nat.card E * Nat.card (fixV E)) := by
      calc Nat.card CAU * Nat.card (blockU Dsub)
          ≤ Nat.card Aoff * Nat.card CU := hkey
        _ = (Nat.card CAU * Nat.card E) * Nat.card CU := by rw [hkerA.symm]
        _ = Nat.card CAU * (Nat.card E * Nat.card CU) := by ring
        _ = Nat.card CAU * (Nat.card E * Nat.card (fixV E)) := by rw [hfixcard]
    exact Nat.le_of_mul_le_mul_left hkey' (Nat.card_pos)
  have hHE : IsAlt 7 ↥Hb := ⟨θ⟩
  have hU2 : ∀ u : ↥(blockU Dsub), u ^ 2 = 1 := fun u => by
    rw [pow_two]
    exact Subtype.ext (by simpa [pow_two] using CFSG.QuasithinUnique.C1.blockU_sq hsh u u.2)
  obtain ⟨hEcard, hNEcard⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.a7_offender
      (U := ↥(blockU Dsub)) hU2 hU hHE hEH hE2 hE1 hoff
  have hET : E ≤ T := Subgroup.map_mono (Subgroup.subgroupOf_mono Nn hAS)
  obtain ⟨S7, hS7⟩ := CFSG.LieType.SteinbergBR.SmallAlt.exists_selfNormalizing_seven
  obtain ⟨P8, hP8⟩ := CFSG.LieType.SteinbergBR.OddSylow.exists_selfNormalizing_of_equiv θ S7 hS7
  have hself8 : ∀ {K : Subgroup Hb}, Nat.card K = 8 →
      Subgroup.normalizer (K : Set Hb) = K := fun {K} hK => by
    have hK2 : IsPGroup 2 K := IsPGroup.of_card (n := 3) (by rw [hK]; norm_num)
    have hKidx : ¬ 2 ∣ K.index := by
      have h := Subgroup.card_mul_index K
      rw [hHcard, hK] at h
      omega
    exact CFSG.LieType.SteinbergBR.OddSylow.normalizer_eq_of_one P8 hP8 (hK2.toSylow hKidx)
  have hTcard48 : Nat.card T = 4 ∨ Nat.card T = 8 := by
    have h4dvd : 4 ∣ Nat.card T := by
      rw [← hEcard]
      exact Subgroup.card_dvd_of_le hET
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    have hdvd : 2 ^ k ∣ 2520 := by
      rw [← hk, ← hHcard]
      exact Subgroup.card_dvd_of_le hTH
    have hk2 : 2 ≤ k := by
      have h : 2 ^ 2 ∣ 2 ^ k := by rw [← hk]; exact h4dvd
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < (2 : ℕ))).mp h
    have hk3 : k ≤ 3 := by
      by_contra h
      have h4 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have : 2 ^ 4 ∣ 2520 := h4.trans hdvd
      norm_num at this
    rcases (by omega : k = 2 ∨ k = 3) with rfl | rfl
    · left; rw [hk]; norm_num
    · right; rw [hk]; norm_num
  have hNT' : ((Subgroup.normalizer (T.subgroupOf Hb : Subgroup ↥Hb)) : Subgroup ↥Hb).map
      Hb.subtype = Subgroup.normalizer (T : Set (MulAut ↥(blockU Dsub))) ⊓ Hb := by
    rw [← Subgroup.subgroupOf_normalizer_eq hTH, Subgroup.subgroupOf_map_subtype]
  have hPeqN : Subgroup.normalizer (T : Set (MulAut ↥(blockU Dsub))) ⊓ Hb =
      ((Subgroup.normalizer (T.subgroupOf Hb : Subgroup ↥Hb)) : Subgroup ↥Hb).map Hb.subtype :=
    hNT'.symm
  have hNTeqT (h8 : Nat.card T = 8) :
      Subgroup.normalizer (T : Set (MulAut ↥(blockU Dsub))) ⊓ Hb = T := by
    have hT'card : Nat.card ↥(T.subgroupOf Hb) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv, h8]
    rw [hPeqN, hself8 hT'card, Subgroup.map_subgroupOf_eq_of_le hTH]
  have hTeq : T = E := by
    by_contra hne
    have hcard4 : Nat.card T ≠ 4 := fun h4 =>
      hne (Subgroup.eq_of_le_of_card_ge hET (by rw [h4, hEcard])).symm
    have h8 : Nat.card T = 8 := by
      rcases hTcard48 with h4 | h8
      · exact absurd h4 hcard4
      · exact h8
    have hP2 : IsPGroup 2 P := by
      rw [hPeq, hNTeqT h8]
      exact hT2
    exact hPnot hP2
  have hPcard : Nat.card P = 72 := by
    have hPE : Subgroup.normalizer (T : Set (MulAut ↥(blockU Dsub))) ⊓ Hb =
        ((Subgroup.normalizer (E.subgroupOf Hb : Subgroup ↥Hb)) : Subgroup ↥Hb).map Hb.subtype := by
      rw [hTeq]
      have h := hPeqN
      rw [hTeq] at h
      exact h
    rw [hPeq, hPE, Subgroup.card_map_of_injective Hb.subtype_injective]
    exact hNEcard
  have hPbar : Nat.card (barM H (Subgroup.normalizer (S : Set G) ⊓ Dsub)) = 72 := by
    rw [← hPcard]
    exact Nat.card_congr ψ.toEquiv
  have hbar72 : Nat.card (barOfInter D.M Dsub) = 72 := by
    rw [ctx19_14_barOfInter_eq h h11]
    exact (Nat.card_congr (starImEquiv hKc.le hKc.inf_twoCore _).toEquiv).trans hPbar
  have hIsAlt : IsAlt (Bar2 Dsub) 7 :=
    ⟨(barMEquiv hKc.le hKc.inf_twoCore).trans eH⟩
  have hidx : (Dsub ⊓ D.M).relIndex Dsub = 35 := by
    rw [← index_barOfInter (M := D.M) (L := Dsub) h.hO2]
    have hmul := Subgroup.card_mul_index (barOfInter D.M Dsub)
    have hBar2card : Nat.card (Bar2 Dsub) = 2520 := by
      rw [Nat.card_congr (barMEquiv hKc.le hKc.inf_twoCore).toEquiv,
        Nat.card_congr eH.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    rw [hbar72, hBar2card] at hmul
    omega
  exact Or.inr (Or.inr (Or.inl ⟨hIsAlt, hidx⟩))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

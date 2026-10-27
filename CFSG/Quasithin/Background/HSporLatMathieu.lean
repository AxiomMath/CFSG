module

public import CFSG.Quasithin.Background.HSporLatInputs
public import CFSG.Quasithin.Background.HNPrimeHall
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import CFSG.Quasithin.Background.HSporLatM12Sg
public import CFSG.Quasithin.Background.HSporLatM22Sg
public import CFSG.Quasithin.Background.HSporLatM23Sg
public import Certificates.Certificate7116
public import Certificates.Certificate7117
public import Certificates.Certificate7118
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.HFF
public import CFSG.Quasithin.Background.HSL3Inner
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H.MathieuLat

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H.NPrimeHall CFSG.Quasithin.E3
open CFSG.Sporadic.Mathieu (m12a m12b m22a m22b card_M12 card_M22 m12_hyp m22_hyp)
open CFSG.Sporadic.Schreier (m23GenA m23GenB m23_card m23_eq_closure)

section Generic

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] {Lab : Type}
  [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

theorem latSylow (C : LatCtx Γ n Lab) (hO : Odd C.D.O.lbl.size) :
    IsSylowIn 2 C.S ⊤ := by
  refine ⟨le_top, C.S_isPGroup, ?_⟩
  rw [Subgroup.relIndex_top_right]
  have h1 := C.S.card_mul_index
  rw [C.S_card, C.hΓ, mul_comm] at h1
  have hidx : C.S.index = C.D.O.lbl.size := Nat.eq_of_mul_eq_mul_right (by positivity) h1
  rw [hidx]
  exact fun h => (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h)

theorem latIndexThree (C : LatCtx Γ n Lab) (hO : Odd C.D.O.lbl.size)
    (h3O : 3 ∣ C.D.O.lbl.size)
    (hsz : ∀ j < C.J, C.D.Om[j]!.lbl.size = 1 ∨ 3 ∣ C.D.Om[j]!.lbl.size) :
    IndexThree (⊤ : Subgroup Γ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro S H hS hSH -
  have hC := latSylow C hO
  let P : Sylow 2 Γ := hS.isPGroup.toSylow (by
    have := hS.not_dvd_relIndex
    rwa [Subgroup.relIndex_top_right] at this)
  let P₀ : Sylow 2 Γ := hC.isPGroup.toSylow (by
    have := hC.not_dvd_relIndex
    rwa [Subgroup.relIndex_top_right] at this)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ P P₀
  have hSg : S.map (MulAut.conj g).toMonoidHom = C.S := by
    have := congrArg (fun Q : Sylow 2 Γ => (Q : Subgroup Γ)) hg
    exact this
  have hSH' : C.S ≤ H.map (MulAut.conj g).toMonoidHom := hSg ▸ Subgroup.map_mono hSH
  obtain ⟨j, -, hH'⟩ := C.complete _ hSH'
  have hcH : Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcS : Nat.card S = 2 ^ C.k := by
    rw [← C.S_card, ← hSg]
    exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm
  rw [← hcH, hcS, hH']
  by_cases hjJ : j < C.J
  · rw [memberOrTop, ite_eq_left_iff.mpr (fun h => absurd hjJ h), C.Y_card hjJ]
    rcases hsz j hjJ with h | h
    · left
      rw [h, one_mul]
    · right
      exact Nat.mul_dvd_mul_right h _
  · right
    rw [memberOrTop, ite_eq_right_iff.mpr (fun h => absurd h hjJ), Subgroup.card_top, C.hΓ]
    exact Nat.mul_dvd_mul_right h3O _

omit [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] in
theorem om_size_eq {D : LatData Lab} {L : Array ℕ} (h : D.Om.map (fun o => o.lbl.size) = L)
    {j : ℕ} (hj : j < L.size) : D.Om[j]!.lbl.size = L[j]! := by
  subst h
  have hj' : j < D.Om.size := by simpa using hj
  rw [getElem!_pos D.Om j hj', getElem!_pos _ j hj, Array.getElem_map]

theorem latTwoLeNPrime (C : LatCtx Γ n Lab) (hO : Odd C.D.O.lbl.size) {j : ℕ}
    (hj : j < C.J) (h3 : C.D.Om[j]!.lbl.size = 3) : 2 ≤ nPrime (⊤ : Subgroup Γ) :=
  two_le_nPrime_of_three (latSylow C hO) (C.S_le_Y j) le_top
    (by rw [C.Y_card hj, h3, C.S_card])

end Generic

theorem m12_delta_valid : CodeSetValid 12 m12Delta := by
  have h : ∀ l ∈ m12Sets, PtValid 12 l := by decide
  refine ⟨sortN_sorted _, fun c hc => ?_⟩
  rw [m12Delta, mem_sortN] at hc
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
  exact ⟨l, h l hl, rfl⟩

theorem m12_ta : (tab 12 m12a).toArray = m12ta.toArray := by rw [m12_tab_a]

theorem m12_tb : (tab 12 m12b).toArray = m12tb.toArray := by rw [m12_tab_b]

theorem m12_sGens :
    genTabs 12 m12Sg = m12STabs ∧ Nat.card (Subgroup.closure {x | x ∈ m12Sg}) = 2 ^ 6 := by
  have hc : BaseCertS 12 (List.range 12)
      (slpTabsA (tab 12 m12a).toArray (tab 12 m12b).toArray m12Prog) m12Qp
      153 204 208 206 210 m12Enum.1 m12Enum.2.1 m12Enum.2.2 6 := by
    rw [m12_ta, m12_tb]
    exact m12_cert
  have := sGens_of_baseCertS (n := 12) (List.range 12) (fun b hb => List.mem_range.mp hb)
    base_of_faithful m12a m12b m12Prog m12_valid m12Qp 153 204 208 206 210 m12Enum.1
    m12Enum.2.1 m12Enum.2.2 6 hc
  refine ⟨?_, this.2⟩
  rw [m12Sg, this.1, m12_ta, m12_tb]
  rfl

noncomputable def m12Ctx :
    LatCtx ↥CFSG.Blueprint.NativeSporadic.M12 12 (List ℕ) :=
  LatFactsK.ctx codeSetLab_lawful m12_delta_valid m12_ta m12_tb m12_hyp.gen m12_sGens.1
    m12_sGens.2 1485 (by rw [card_M12]; norm_num) Certificates.certificate7116.choose_spec.1

theorem m12_lat_cert :
    LatOK (codeSetAct 12) 12 m12ta.toArray m12tb.toArray m12Delta m12Ctx.D ∧
      m12Ctx.D.O.lbl.size = 1485 ∧ m12Ctx.D.Om.map (fun o => o.lbl.size) = #[1, 3, 3] :=
  ⟨m12Ctx.hD, LatFactsK.ctx_O_size .., Certificates.certificate7116.choose_spec.2⟩

theorem m12_J :
    m12Ctx.J = 3 := by
  have h1 := m12_lat_cert.2.2
  have h2 : m12Ctx.D.Om.size = m12Ctx.D.mw.size := m12Ctx.membersOK.2.2.2.1
  have : m12Ctx.D.Om.size = 3 := by simpa using congrArg Array.size h1
  unfold LatCtx.J
  omega

theorem m12_indexThree :
    IndexThree (⊤ : Subgroup ↥CFSG.Blueprint.NativeSporadic.M12) := by
  have hO : m12Ctx.D.O.lbl.size = 1485 := m12_lat_cert.2.1
  have hsz : ∀ j < m12Ctx.J, m12Ctx.D.Om[j]!.lbl.size = 1 ∨ 3 ∣ m12Ctx.D.Om[j]!.lbl.size := by
    intro j hj
    rw [m12_J] at hj
    rw [om_size_eq m12_lat_cert.2.2 (by simpa using hj)]
    interval_cases j <;> decide
  exact latIndexThree m12Ctx (by rw [hO]; decide) (by rw [hO]; norm_num) hsz

theorem m12_two_le_nPrime :
    2 ≤ nPrime (⊤ : Subgroup ↥CFSG.Blueprint.NativeSporadic.M12) := by
  have hO : m12Ctx.D.O.lbl.size = 1485 := m12_lat_cert.2.1
  refine latTwoLeNPrime m12Ctx (j := 1) (by rw [hO]; decide) (by rw [m12_J]; norm_num) ?_
  rw [om_size_eq m12_lat_cert.2.2 (by decide)]
  decide

theorem m22_delta_valid : CodeSetValid 22 m22Delta := by
  have h : ∀ l ∈ m22Sets, PtValid 22 l := by decide
  refine ⟨sortN_sorted _, fun c hc => ?_⟩
  rw [m22Delta, mem_sortN] at hc
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
  exact ⟨l, h l hl, rfl⟩

theorem m22_ta : (tab 22 m22a).toArray = m22ta.toArray := by rw [m22_tab_a]

theorem m22_tb : (tab 22 m22b).toArray = m22tb.toArray := by rw [m22_tab_b]

theorem m22_sGens :
    genTabs 22 m22Sg = m22STabs ∧ Nat.card (Subgroup.closure {x | x ∈ m22Sg}) = 2 ^ 7 := by
  have hc : BaseCertS 22 (List.range 22)
      (slpTabsA (tab 22 m22a).toArray (tab 22 m22b).toArray m22Prog) m22Qp
      163 205 209 207 211 m22Enum.1 m22Enum.2.1 m22Enum.2.2 7 := by
    rw [m22_ta, m22_tb]
    exact m22_cert
  have := sGens_of_baseCertS (n := 22) (List.range 22) (fun b hb => List.mem_range.mp hb)
    base_of_faithful m22a m22b m22Prog m22_valid m22Qp 163 205 209 207 211 m22Enum.1
    m22Enum.2.1 m22Enum.2.2 7 hc
  refine ⟨?_, this.2⟩
  rw [m22Sg, this.1, m22_ta, m22_tb]
  rfl

noncomputable def m22Ctx :
    LatCtx ↥CFSG.Blueprint.NativeSporadic.M22 22 (List ℕ) :=
  LatFactsK.ctx codeSetLab_lawful m22_delta_valid m22_ta m22_tb m22_hyp.gen m22_sGens.1
    m22_sGens.2 3465 (by rw [card_M22]; norm_num) Certificates.certificate7117.choose_spec.1

theorem m22_lat_cert :
    LatOK (codeSetAct 22) 22 m22ta.toArray m22tb.toArray m22Delta m22Ctx.D ∧
      m22Ctx.D.O.lbl.size = 3465 ∧ m22Ctx.D.Om.map (fun o => o.lbl.size) = #[1, 45, 3, 15, 3] :=
  ⟨m22Ctx.hD, LatFactsK.ctx_O_size .., Certificates.certificate7117.choose_spec.2⟩

theorem m22_J :
    m22Ctx.J = 5 := by
  have h1 := m22_lat_cert.2.2
  have h2 : m22Ctx.D.Om.size = m22Ctx.D.mw.size := m22Ctx.membersOK.2.2.2.1
  have : m22Ctx.D.Om.size = 5 := by simpa using congrArg Array.size h1
  unfold LatCtx.J
  omega

theorem m22_indexThree :
    IndexThree (⊤ : Subgroup ↥CFSG.Blueprint.NativeSporadic.M22) := by
  have hO : m22Ctx.D.O.lbl.size = 3465 := m22_lat_cert.2.1
  have hsz : ∀ j < m22Ctx.J, m22Ctx.D.Om[j]!.lbl.size = 1 ∨ 3 ∣ m22Ctx.D.Om[j]!.lbl.size := by
    intro j hj
    rw [m22_J] at hj
    rw [om_size_eq m22_lat_cert.2.2 (by simpa using hj)]
    interval_cases j <;> decide
  exact latIndexThree m22Ctx (by rw [hO]; decide) (by rw [hO]; norm_num) hsz

theorem m22_two_le_nPrime :
    2 ≤ nPrime (⊤ : Subgroup ↥CFSG.Blueprint.NativeSporadic.M22) := by
  have hO : m22Ctx.D.O.lbl.size = 3465 := m22_lat_cert.2.1
  refine latTwoLeNPrime m22Ctx (j := 2) (by rw [hO]; decide) (by rw [m22_J]; norm_num) ?_
  rw [om_size_eq m22_lat_cert.2.2 (by decide)]
  decide

theorem m23_delta_valid : CodeSetValid 23 m23Delta := by
  have h : ∀ l ∈ m23Sets, PtValid 23 l := by decide
  refine ⟨sortN_sorted _, fun c hc => ?_⟩
  rw [m23Delta, mem_sortN] at hc
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
  exact ⟨l, h l hl, rfl⟩

theorem m23_ta : (tab 23 m23GenA).toArray = m23ta.toArray := by rw [m23_tab_a]

theorem m23_tb : (tab 23 m23GenB).toArray = m23tb.toArray := by rw [m23_tab_b]

theorem m23_sGens :
    genTabs 23 m23Sg = m23STabs ∧ Nat.card (Subgroup.closure {x | x ∈ m23Sg}) = 2 ^ 7 := by
  have hc : BaseCertS 23 (List.range 23)
      (slpTabsA (tab 23 m23GenA).toArray (tab 23 m23GenB).toArray m23Prog) m23Qp
      159 199 203 201 205 m23Enum.1 m23Enum.2.1 m23Enum.2.2 7 := by
    rw [m23_ta, m23_tb]
    exact m23_cert
  have := sGens_of_baseCertS (n := 23) (List.range 23) (fun b hb => List.mem_range.mp hb)
    base_of_faithful m23GenA m23GenB m23Prog m23_valid m23Qp 159 199 203 201 205 m23Enum.1
    m23Enum.2.1 m23Enum.2.2 7 hc
  refine ⟨?_, this.2⟩
  rw [m23Sg, this.1, m23_ta, m23_tb]
  rfl

@[expose] noncomputable def m23Ctx :
    LatCtx ↥CFSG.Blueprint.NativeSporadic.M23 23 (List ℕ) :=
  LatFactsK.ctx codeSetLab_lawful m23_delta_valid m23_ta m23_tb
    (CFSG.Sporadic.Mathieu.closure_pair_eq_top m23_eq_closure _ _) m23_sGens.1 m23_sGens.2 79695
    (by rw [m23_card]; norm_num) Certificates.certificate7118.choose_spec.1

theorem m23_lat_cert :
    LatOK (codeSetAct 23) 23 m23ta.toArray m23tb.toArray m23Delta m23Ctx.D ∧
      m23Ctx.D.O.lbl.size = 79695 ∧
      m23Ctx.D.Om.map (fun o => o.lbl.size) =
        #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9] :=
  ⟨m23Ctx.hD, LatFactsK.ctx_O_size .., Certificates.certificate7118.choose_spec.2.1⟩

theorem m23_mw :
    m23Ctx.D.mw = CFSG.Quasithin.A312M23.m23MwLit :=
  Certificates.certificate7118.choose_spec.2.2

theorem m23Ctx_Y
    (j : ℕ) : m23Ctx.Y j = m23Member j := by
  unfold LatCtx.Y LatCtx.gens m23Member
  rw [m23_mw]
  rfl

theorem m23Ctx_S :
    m23Ctx.S = m23SylTwo :=
  m23Ctx.hSeq.symm

theorem m23_J :
    m23Ctx.J = 16 := by
  unfold LatCtx.J
  rw [m23_mw]
  rfl

theorem m23_indexThree :
    IndexThree (⊤ : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23) := by
  have hO : m23Ctx.D.O.lbl.size = 79695 := m23_lat_cert.2.1
  have hsz : ∀ j < m23Ctx.J, m23Ctx.D.Om[j]!.lbl.size = 1 ∨ 3 ∣ m23Ctx.D.Om[j]!.lbl.size := by
    intro j hj
    rw [m23_J] at hj
    rw [om_size_eq m23_lat_cert.2.2 (by simpa using hj)]
    interval_cases j <;> decide
  exact latIndexThree m23Ctx (by rw [hO]; decide) (by rw [hO]; norm_num) hsz

theorem m23_two_le_nPrime :
    2 ≤ nPrime (⊤ : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23) := by
  have hO : m23Ctx.D.O.lbl.size = 79695 := m23_lat_cert.2.1
  refine latTwoLeNPrime m23Ctx (j := 10) (by rw [hO]; decide) (by rw [m23_J]; norm_num) ?_
  rw [om_size_eq m23_lat_cert.2.2 (by decide)]
  decide

section M24

open CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.Sporadic.Mathieu (m24a m24b m24_hyp)

noncomputable def m24Ctx' :
    LatCtx ↥CFSG.Blueprint.NativeSporadic.M24 24 (List ℕ) :=
  m24Ctx

theorem m24_J' :
    m24Ctx'.J = 13 := m24_J

theorem m24_indexThree :
    IndexThree (⊤ : Subgroup ↥CFSG.Blueprint.NativeSporadic.M24) := by
  have hO : m24Ctx'.D.O.lbl.size = 239085 := m24_O_size
  have hsz : ∀ j < m24Ctx'.J,
      m24Ctx'.D.Om[j]!.lbl.size = 1 ∨ 3 ∣ m24Ctx'.D.Om[j]!.lbl.size := by
    intro j hj
    rw [m24_J'] at hj
    change m24Ctx.D.Om[j]!.lbl.size = 1 ∨ 3 ∣ m24Ctx.D.Om[j]!.lbl.size
    rw [om_size_eq m24_Om_map (by simpa using hj)]
    interval_cases j <;> decide
  exact latIndexThree m24Ctx' (by rw [hO]; decide) (by rw [hO]; norm_num) hsz

theorem m24_two_le_nPrime :
    2 ≤ nPrime (⊤ : Subgroup ↥CFSG.Blueprint.NativeSporadic.M24) := by
  have hO : m24Ctx'.D.O.lbl.size = 239085 := m24_O_size
  refine latTwoLeNPrime m24Ctx' (j := 7) (by rw [hO]; decide) (by rw [m24_J']; norm_num) ?_
  change m24Ctx.D.Om[7]!.lbl.size = 3
  rw [om_size_eq m24_Om_map (by decide)]
  decide

end M24

end CFSG.Quasithin.H.MathieuLat

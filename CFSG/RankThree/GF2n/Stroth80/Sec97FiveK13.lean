module

public import CFSG.RankThree.GF2n.Stroth80.Sec97FiveDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec97FivePoint
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CStmt
import CFSG.RankThree.GF2n.Stroth80.Sec97FiveTrans
import CFSG.RankThree.GF2n.Stroth80.Sec97FiveYLines
import CFSG.RankThree.GF2n.Stroth80.Sec97FiveComm
import CFSG.RankThree.GF2n.Stroth80.HeringSec96Line
import CFSG.RankThree.GF2n.Stroth80.HeringSec9RTwo
import CFSG.LocalAnalysis.AGLEmbedding.TheoremZAux
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Line
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Schur

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

private theorem conjSubgroup_Vt_nn_eq (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    {g₀ nn : G} (hYg₀ : conjSubgroup g₀ Y = Y)
    (hVg₀ : conjSubgroup g₀ (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z nn)
    {y : G} (hy : y ∈ Y) :
    conjSubgroup y (Vt M (LB M Q B) B Z nn) = Vt M (LB M Q B) B Z nn := by
  obtain ⟨⟨-, -, -, hYR, -, -, -⟩, -, -⟩ := hsplit
  have hy' : g₀⁻¹ * y * g₀ ∈ Y := by
    have hyY : y ∈ conjSubgroup g₀ Y := by rw [hYg₀]; exact hy
    exact mem_conjSubgroup.mp hyY
  have hVt : conjSubgroup (g₀⁻¹ * y * g₀) (Vt M (LB M Q B) B Z t) =
      Vt M (LB M Q B) B Z t :=
    conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt hs.mem (hYR hy'))
  calc conjSubgroup y (Vt M (LB M Q B) B Z nn)
      = conjSubgroup (g₀ * (g₀⁻¹ * y * g₀) * g₀⁻¹)
          (conjSubgroup g₀ (Vt M (LB M Q B) B Z t)) := by
        rw [hVg₀]
        congr 1
        group
    _ = conjSubgroup g₀ (conjSubgroup (g₀⁻¹ * y * g₀) (Vt M (LB M Q B) B Z t)) := by
        rw [conjSubgroup_mul, conjSubgroup_mul,
          show conjSubgroup g₀⁻¹ (conjSubgroup g₀ (Vt M (LB M Q B) B Z t)) =
            Vt M (LB M Q B) B Z t by
            rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]]
    _ = conjSubgroup g₀ (Vt M (LB M Q B) B Z t) := by rw [hVt]
    _ = Vt M (LB M Q B) B Z nn := hVg₀

private theorem Vt_nn_ne_of_K (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {r : G} (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hVn : Sec97VnStatement)
    {nn : G} (hnn : nn ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t) (hnZ : nn ∉ Z0) :
    Vt M (LB M Q B) B Z nn ≠ Vt M (LB M Q B) B Z t := by
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  set e : G := r⁻¹ * nn * r with hedef
  have heL : e ∈ LB M Q B := by
    have h : nn ∈ conjSubgroup r (LB M Q B) := by
      simpa [hc.LB_conj hrM] using hnn.1
    exact mem_conjSubgroup.mp h
  have heN : e ∈ hc.CN t := by
    have h := hc.CN_conj_mem hs.mem ((Rt M (LB M Q B) t).inv_mem hrR) hnn.2
    simpa [hedef] using h
  have heZ0 : e ∉ Z0 := by
    intro he
    have hei : e⁻¹ ∈ Z0 := Z0.inv_mem he
    have hcomm : ⁅e⁻¹, r⁆ ∈ Q := ((hZ0 e⁻¹).mp hei).2 r hrR
    have hcommZ : ⁅e⁻¹, r⁆ ∈ Z0 := hc.Q_le_centre hs.mem hZ0 hcomm
    have hnnZ : nn ∈ Z0 := by
      have e1 : nn = e * ⁅e⁻¹, r⁆ := by
        rw [hedef]
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact Z0.mul_mem he hcommZ
    exact hnZ hnnZ
  have hVne : Vt M (LB M Q B) B Z e ≠ Vt M (LB M Q B) B Z t :=
    hVn G M Q Z B hc n t hs Z0 hZ0 e ⟨heL, heN⟩ heZ0
  intro hEq
  apply hVne
  have hconj : conjSubgroup r (Vt M (LB M Q B) B Z e) =
      conjSubgroup r (Vt M (LB M Q B) B Z t) := by
    rw [conjSubgroup_Vt_eq hrM (hc.conj_Z_eq hrM) e,
      show r * e * r⁻¹ = nn by rw [hedef]; group, hEq,
      conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt hs.mem hrR)]
  calc Vt M (LB M Q B) B Z e
      = conjSubgroup r⁻¹ (conjSubgroup r (Vt M (LB M Q B) B Z e)) := by
        rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    _ = conjSubgroup r⁻¹ (conjSubgroup r (Vt M (LB M Q B) B Z t)) := by rw [hconj]
    _ = Vt M (LB M Q B) B Z t := by
        rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]

private theorem planeST_eq_conj (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) {g₀ x y nn : G} (hg₀ : g₀ ∈ M) (hx : x ∈ X)
    (hy : y ∈ Y)
    (hVnn : conjSubgroup g₀ (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z nn) :
    planeST M Q Z B X nn (g₀ * x * y) = conjSubgroup (g₀ * x) (Uline Z B Y) := by
  have hsplit0 := hsplit
  obtain ⟨⟨-, hXR, -, hYR, -, -, -⟩, -, -⟩ := hsplit
  have hYM : Y ≤ M := hYR.trans (Rt_le_M hc.LB_le_M t)
  have hxyR : x * y ∈ Rt M (LB M Q B) t :=
    (Rt M (LB M Q B) t).mul_mem (hXR hx) (hYR hy)
  have hxyM : x * y ∈ M := hc.Rt_le_M t hxyR
  have hMxy : g₀ * (x * y) ∈ M := M.mul_mem hg₀ hxyM
  have hVxy : conjSubgroup (x * y) (Vt M (LB M Q B) B Z t) =
      Vt M (LB M Q B) B Z t :=
    conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt hs.mem hxyR)
  have hVg : conjSubgroup (g₀ * (x * y)) (Vt M (LB M Q B) B Z t) =
      conjSubgroup g₀ (Vt M (LB M Q B) B Z t) := by
    rw [conjSubgroup_mul, hVxy]
  have hU : ⁅Vt M (LB M Q B) B Z t, LB M Q B ⊓ X⁆ ⊔ Z = Uline Z B Y :=
    comm_Vt_E_sup_eq h34 h311a hc hs hsplit0
  unfold planeST
  rw [← hVnn, show g₀ * x * y = g₀ * (x * y) by group]
  calc ⁅conjSubgroup g₀ (Vt M (LB M Q B) B Z t),
        conjSubgroup (g₀ * (x * y)) (LB M Q B ⊓ X)⁆ ⊔ Z
      = ⁅conjSubgroup (g₀ * (x * y)) (Vt M (LB M Q B) B Z t),
          conjSubgroup (g₀ * (x * y)) (LB M Q B ⊓ X)⁆ ⊔ Z := by rw [hVg]
    _ = conjSubgroup (g₀ * (x * y))
          (⁅Vt M (LB M Q B) B Z t, LB M Q B ⊓ X⁆ ⊔ Z) := by
        rw [conjSubgroup_sup', conjSubgroup_commutator, hc.conj_Z_eq hMxy]
    _ = conjSubgroup (g₀ * (x * y)) (Uline Z B Y) := by rw [hU]
    _ = conjSubgroup (g₀ * x) (Uline Z B Y) := by
        rw [show g₀ * (x * y) = (g₀ * x) * y by group,
          conjSubgroup_mul (g₀ * x) y (Uline Z B Y)]
        rw [conj_Uline hc hYM hy]

private theorem exists_x_ne (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) {g₀ r : G}
    (hYg₀ : conjSubgroup g₀ Y = Y) :
    ∃ x ∈ X, conjSubgroup (g₀ * x) (Uline Z B Y) ≠ Uline Z (conjSubgroup r B) Y ∧
      conjSubgroup (g₀ * x) Y = Y := by
  classical
  have hsplit0 := hsplit
  obtain ⟨⟨-, hXR, hQY, hYR, -, -, hcomm⟩, -, -⟩ := hsplit
  obtain ⟨hUcard, hUirr, -⟩ :=
    sec97LineNat_of h34 h311a G M Q Z B hc n t hs X Y hsplit0
  have hUneZ : Uline Z B Y ≠ Z := (ne_of_lt hUirr.2.2.1).symm
  have hXn : X ≤ Subgroup.normalizer (Y : Set G) :=
    normalizer_of_commutator_le hQY (fun a ha y hy => by
      have := Q.inv_mem (hcomm y hy a ha)
      rwa [commutatorElement_inv] at this)
  by_cases h0 : conjSubgroup g₀ (Uline Z B Y) = Uline Z (conjSubgroup r B) Y
  · obtain ⟨x₁, hx₁, hinf, -⟩ := exists_ulineY_compl h34 h311a hc hs hsplit0
    refine ⟨x₁, hx₁, ?_, ?_⟩
    · intro hEq
      have hconj : conjSubgroup g₀ (conjSubgroup x₁ (Uline Z B Y)) =
          conjSubgroup g₀ (Uline Z B Y) := by
        rw [← conjSubgroup_mul g₀ x₁ (Uline Z B Y), hEq, h0]
      have hcancel : conjSubgroup x₁ (Uline Z B Y) = Uline Z B Y := by
        have := congrArg (conjSubgroup g₀⁻¹) hconj
        simpa [← conjSubgroup_mul, conjSubgroup_one] using this
      have hZU : Uline Z B Y ⊓ conjSubgroup x₁ (Uline Z B Y) = Uline Z B Y := by
        rw [hcancel, inf_idem]
      exact hUneZ (hZU.symm.trans hinf)
    · calc conjSubgroup (g₀ * x₁) Y = conjSubgroup g₀ (conjSubgroup x₁ Y) :=
            conjSubgroup_mul g₀ x₁ Y
        _ = conjSubgroup g₀ Y := by rw [conjSubgroup_eq_self_iff.mpr (hXn hx₁)]
        _ = Y := hYg₀
  · refine ⟨1, X.one_mem, ?_, ?_⟩
    · simpa [conjSubgroup_one] using h0
    · simpa using hYg₀

theorem exists_conj_SY (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (h4 : Sec4Concl M Q Z B X Y) {k : G} (hkY : conjSubgroup k Y = Y) :
    ∃ y ∈ Y, conjSubgroup (k * y) (LB M Q B ⊓ Y) = LB M Q B ⊓ Y := by
  classical
  obtain ⟨⟨hQX, -, hQY, -, -, -, -⟩, hYsl, -⟩ := hsplit
  obtain ⟨m, kk, hm, -⟩ := hc.hyp.cp
  have hm0 : m ≠ 0 := by
    rintro rfl
    have h4 := hc.hyp.q4
    rw [hm] at h4
    simp at h4
  have hqeven : 2 ∣ Nat.card Z := by
    rw [hm]
    exact dvd_pow_self 2 hm0
  have hqodd : Odd (Nat.card Z ^ 2 - 1) := odd_sq_sub_one hqeven Nat.card_pos
  have hkYinv : conjSubgroup k⁻¹ Y = Y := by
    have := congrArg (conjSubgroup k⁻¹) hkY
    simpa [← conjSubgroup_mul, conjSubgroup_one] using this.symm
  set S : Subgroup G := LB M Q B ⊓ Y with hSdef
  set S' : Subgroup G := conjSubgroup k⁻¹ S with hS'def
  have hSY : S ≤ Y := by rw [hSdef]; exact inf_le_right
  have hS'Y : S' ≤ Y := by
    rw [hS'def]
    calc conjSubgroup k⁻¹ S ≤ conjSubgroup k⁻¹ Y := Subgroup.map_mono hSY
      _ = Y := hkYinv
  have hQS : Q ≤ S := by
    rw [hSdef]
    exact le_inf sec39_Q_le_LB hQY
  have hLB2 : IsPGroup 2 ↥(LB M Q B) :=
    hc.isPGroup_LB h34 hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen
  have hS2 : IsPGroup 2 ↥S := hLB2.to_le (by rw [hSdef]; exact inf_le_left)
  have hS'2 : IsPGroup 2 ↥S' := by
    rw [hS'def]
    change IsPGroup 2 ↥(S.map (MulAut.conj k⁻¹).toMonoidHom)
    exact hS2.map (MulAut.conj k⁻¹).toMonoidHom
  have hcardS : Nat.card ↥S' = Nat.card ↥S := by
    rw [hS'def]
    exact card_conjSubgroup k⁻¹ S
  have hYrel : Q.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1) := by
    obtain ⟨hN, hmod⟩ := hYsl
    haveI := hN
    have hcardY := (isSLModel_two_data hc.hyp.q4 ⟨m, hm⟩ hmod).1
    rw [Subgroup.relIndex, Subgroup.index]
    exact hcardY
  have hrelQ : Q.relIndex S = Nat.card Z := by
    rw [hSdef]
    exact h4.2.1
  have hSrel : S.relIndex Y = Nat.card Z ^ 2 - 1 := by
    have htower := Subgroup.relIndex_mul_relIndex Q S Y hQS hSY
    rw [hrelQ, hYrel] at htower
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos htower
  have hnotdvd : ¬ 2 ∣ (S.subgroupOf Y).index := by
    rw [show (S.subgroupOf Y).index = S.relIndex Y from rfl, hSrel]
    exact fun hd => (Nat.not_even_iff_odd.mpr hqodd) (even_iff_two_dvd.mpr hd)
  obtain ⟨l, hlY, hl⟩ := CFSG.AGLEmbedding.exists_mem_map_conj_eq_of_card_eq
    (p := 2) hSY hS'Y hS2 hS'2 hnotdvd hcardS
  refine ⟨l, hlY, ?_⟩
  have hlS : conjSubgroup l S = S' := by simpa [conjSubgroup] using hl
  have hmain : conjSubgroup (k * l) S = S := by
    rw [conjSubgroup_mul k l, hlS, hS'def]
    rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  simpa [hSdef] using hmain

private theorem inf_eq_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) {r nn : G} (hr : Sec7A hc t r)
    (hnn : nn ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t)
    (hVnnInv : ∀ y ∈ Y, conjSubgroup y (Vt M (LB M Q B) B Z nn) =
      Vt M (LB M Q B) B Z nn)
    (hcardVnn : Nat.card (Vt M (LB M Q B) B Z nn) = Nat.card Z ^ 5)
    (hVnn_ne : Vt M (LB M Q B) B Z nn ≠ Vt M (LB M Q B) B Z t) :
    Vt M (LB M Q B) B Z t ⊓ Vt M (LB M Q B) B Z nn =
      Uline Z (conjSubgroup r B) Y := by
  have hsplit0 := hsplit
  obtain ⟨⟨-, -, -, hYR, -, -, -⟩, -, -⟩ := hsplit
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hYM : Y ≤ M := hYR.trans (Rt_le_M hc.LB_le_M t)
  have hVtInv : ∀ y ∈ Y, conjSubgroup y (Vt M (LB M Q B) B Z t) =
      Vt M (LB M Q B) B Z t :=
    fun y hy => conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt hs.mem (hYR hy))
  have hBrVt : conjSubgroup r B ≤ Vt M (LB M Q B) B Z t := by
    calc conjSubgroup r B ≤ conjSubgroup r (Vt M (LB M Q B) B Z t) :=
          Subgroup.map_mono (hc.B_le_Vt hs.mem)
      _ = Vt M (LB M Q B) B Z t :=
          conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt hs.mem hrR)
  have hnnL : nn ∈ conjSubgroup r (LB M Q B) := by
    simpa [hc.LB_conj hrM] using hnn.1
  have hBrVnn : conjSubgroup r B ≤ Vt M (LB M Q B) B Z nn :=
    sec39_conjB_le_Vt hrM hnnL
  have hle : Uline Z (conjSubgroup r B) Y ≤
      Vt M (LB M Q B) B Z t ⊓ Vt M (LB M Q B) B Z nn := by
    refine sup_le (le_inf sec39_Z_le_Vt sec39_Z_le_Vt) ?_
    refine iSup₂_le fun y hy => ?_
    refine le_inf ?_ ?_
    · calc conjSubgroup y (conjSubgroup r B)
          ≤ conjSubgroup y (Vt M (LB M Q B) B Z t) := Subgroup.map_mono hBrVt
        _ = Vt M (LB M Q B) B Z t := hVtInv y hy
    · calc conjSubgroup y (conjSubgroup r B)
          ≤ conjSubgroup y (Vt M (LB M Q B) B Z nn) := Subgroup.map_mono hBrVnn
        _ = Vt M (LB M Q B) B Z nn := hVnnInv y hy
  have hD : ∀ y ∈ Y, conjSubgroup y
      (Vt M (LB M Q B) B Z t ⊓ Vt M (LB M Q B) B Z nn) =
      Vt M (LB M Q B) B Z t ⊓ Vt M (LB M Q B) B Z nn := by
    intro y hy
    rw [conjSubgroup_inf, hVtInv y hy, hVnnInv y hy]
  have hne : ¬ Vt M (LB M Q B) B Z t ≤
      Vt M (LB M Q B) B Z t ⊓ Vt M (LB M Q B) B Z nn := by
    intro hle'
    have hleV : Vt M (LB M Q B) B Z t ≤ Vt M (LB M Q B) B Z nn :=
      hle'.trans inf_le_right
    have hcard : Nat.card (Vt M (LB M Q B) B Z nn) ≤
        Nat.card (Vt M (LB M Q B) B Z t) := by
      rw [hcardVnn, hs.card_V]
    exact hVnn_ne (Subgroup.eq_of_le_of_card_ge hleV hcard).symm
  exact eq_ulineY_of_inv h34 h311a hc hs hsplit0 (k := r) hr.mem hD hle inf_le_left hne

private theorem inf_Z_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) {r g₀ x y nn : G}
    (hrM : r ∈ M) (hYr : conjSubgroup r Y = Y) (hgxM : g₀ * x ∈ M)
    (hYgx : conjSubgroup (g₀ * x) Y = Y)
    (hUne : conjSubgroup (g₀ * x) (Uline Z B Y) ≠ Uline Z (conjSubgroup r B) Y)
    (hP : planeST M Q Z B X nn (g₀ * x * y) =
      conjSubgroup (g₀ * x) (Uline Z B Y)) :
    Uline Z (conjSubgroup r B) Y ⊓ planeST M Q Z B X nn (g₀ * x * y) = Z := by
  classical
  have hsplit0 := hsplit
  obtain ⟨⟨-, -, -, hYR, -, -, -⟩, -, -⟩ := hsplit
  have hYM : Y ≤ M := hYR.trans (Rt_le_M hc.LB_le_M t)
  obtain ⟨hUcard, hUirr, -⟩ :=
    sec97LineNat_of h34 h311a G M Q Z B hc n t hs X Y hsplit0
  have hUAcard : Nat.card ↥(Uline Z (conjSubgroup r B) Y) = Nat.card Z ^ 3 := by
    calc Nat.card ↥(Uline Z (conjSubgroup r B) Y)
        = Nat.card ↥(conjSubgroup r (Uline Z B Y)) := by
          rw [uline_conj (hc.conj_Z_eq hrM) hYr]
      _ = Nat.card ↥(Uline Z B Y) := card_conjSubgroup r (Uline Z B Y)
      _ = Nat.card Z ^ 3 := hUcard
  have hPcard : Nat.card ↥(conjSubgroup (g₀ * x) (Uline Z B Y)) = Nat.card Z ^ 3 := by
    rw [card_conjSubgroup, hUcard]
  have hPirr : IsIrredModule Y (conjSubgroup (g₀ * x) (Uline Z B Y)) Z :=
    isIrredModule_conj (hR := hYgx) (hI := hc.conj_Z_eq hgxM) hUirr
  have hUAnorm : Y ≤ Subgroup.normalizer (Uline Z (conjSubgroup r B) Y : Set G) :=
    le_normalizer_uline (hc.conj_of_mem hrM) hYM
  have hPnorm : Y ≤ Subgroup.normalizer
      (conjSubgroup (g₀ * x) (Uline Z B Y) : Set G) := by
    have hP' : conjSubgroup (g₀ * x) (Uline Z B Y) =
        Uline Z (conjSubgroup (g₀ * x) B) Y :=
      uline_conj (hc.conj_Z_eq hgxM) hYgx
    rw [hP']
    exact le_normalizer_uline (hc.conj_of_mem hgxM) hYM
  have hZP : Z ≤ conjSubgroup (g₀ * x) (Uline Z B Y) := by
    have hP' : conjSubgroup (g₀ * x) (Uline Z B Y) =
        Uline Z (conjSubgroup (g₀ * x) B) Y :=
      uline_conj (hc.conj_Z_eq hgxM) hYgx
    rw [hP']
    exact Z_le_Uline Z (conjSubgroup (g₀ * x) B) Y
  have hAinv : ∀ y ∈ Y,
      conjSubgroup y (Uline Z (conjSubgroup r B) Y ⊓
        conjSubgroup (g₀ * x) (Uline Z B Y)) =
      Uline Z (conjSubgroup r B) Y ⊓ conjSubgroup (g₀ * x) (Uline Z B Y) := by
    intro y hy
    rw [conjSubgroup_inf,
      conjSubgroup_eq_self_iff.mpr (hUAnorm hy),
      conjSubgroup_eq_self_iff.mpr (hPnorm hy)]
  rcases hPirr.2.2.2 (Uline Z (conjSubgroup r B) Y ⊓
      conjSubgroup (g₀ * x) (Uline Z B Y))
      (le_inf (Z_le_Uline Z (conjSubgroup r B) Y) hZP) inf_le_right hAinv with hA | hA
  · rw [hP]
    exact hA
  · have hle : conjSubgroup (g₀ * x) (Uline Z B Y) ≤ Uline Z (conjSubgroup r B) Y :=
      hA ▸ inf_le_left
    have hcard : Nat.card ↥(Uline Z (conjSubgroup r B) Y) ≤
        Nat.card ↥(conjSubgroup (g₀ * x) (Uline Z B Y)) := by
      rw [hUAcard, hPcard]
    exact (hUne (Subgroup.eq_of_le_of_card_ge hle hcard)).elim

private theorem sup_eq_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    {r g₀ x y nn : G} (hrM : r ∈ M) (hx : x ∈ X) (hYr : conjSubgroup r Y = Y)
    (hVg₀ : conjSubgroup g₀ (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z nn)
    (hInf : Vt M (LB M Q B) B Z t ⊓ Vt M (LB M Q B) B Z nn =
      Uline Z (conjSubgroup r B) Y)
    (hInfZ : Uline Z (conjSubgroup r B) Y ⊓
      planeST M Q Z B X nn (g₀ * x * y) = Z)
    (hP : planeST M Q Z B X nn (g₀ * x * y) =
      conjSubgroup (g₀ * x) (Uline Z B Y)) :
    Uline Z (conjSubgroup r B) Y ⊔ planeST M Q Z B X nn (g₀ * x * y) =
      Vt M (LB M Q B) B Z nn := by
  have hsplit0 := hsplit
  obtain ⟨⟨-, hXR, -, hYR, -, -, -⟩, -, -⟩ := hsplit
  have hYM : Y ≤ M := hYR.trans (Rt_le_M hc.LB_le_M t)
  have hUV : Uline Z B Y ≤ Vt M (LB M Q B) B Z t :=
    sec96Line_of G M Q Z B hc n t hs X Y hsplit0
  have hcardVnn : Nat.card (Vt M (LB M Q B) B Z nn) = Nat.card Z ^ 5 := by
    rw [← hVg₀, card_conjSubgroup, hs.card_V]
  obtain ⟨hUcard, -, -⟩ :=
    sec97LineNat_of h34 h311a G M Q Z B hc n t hs X Y hsplit0
  set P : Subgroup G := planeST M Q Z B X nn (g₀ * x * y) with hPdef
  have hPeq : P = conjSubgroup (g₀ * x) (Uline Z B Y) := hPdef.trans hP
  have hInfZ' : Uline Z (conjSubgroup r B) Y ⊓ P = Z := by
    rw [hPdef]
    exact hInfZ
  have hxV : conjSubgroup x (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt hs.mem (hXR hx))
  have hgxV : conjSubgroup (g₀ * x) (Vt M (LB M Q B) B Z t) =
      Vt M (LB M Q B) B Z nn := by
    rw [conjSubgroup_mul, hxV, hVg₀]
  have hUA_le : Uline Z (conjSubgroup r B) Y ≤ Vt M (LB M Q B) B Z nn := by
    rw [← hInf]
    exact inf_le_right
  have hP_le : P ≤ Vt M (LB M Q B) B Z nn := by
    rw [hPeq]
    calc conjSubgroup (g₀ * x) (Uline Z B Y)
        ≤ conjSubgroup (g₀ * x) (Vt M (LB M Q B) B Z t) := Subgroup.map_mono hUV
      _ = Vt M (LB M Q B) B Z nn := hgxV
  have hUAQ : Uline Z (conjSubgroup r B) Y ≤ Q := Uline_le_Q (hc.conj_of_mem hrM) hYM
  have hPQ : P ≤ Q := hP_le.trans (hc.Vt_le_Q nn)
  have hnorm : P ≤ Subgroup.normalizer (Uline Z (conjSubgroup r B) Y : Set G) :=
    normalizer_of_commutator_le (Z_le_Uline Z (conjSubgroup r B) Y)
      (fun a ha p hp => hc.hyp.toHyp79.comm_mem_V (hUAQ ha) (hPQ hp))
  have hUAcard : Nat.card ↥(Uline Z (conjSubgroup r B) Y) = Nat.card Z ^ 3 := by
    calc Nat.card ↥(Uline Z (conjSubgroup r B) Y)
        = Nat.card ↥(conjSubgroup r (Uline Z B Y)) := by
          rw [uline_conj (hc.conj_Z_eq hrM) hYr]
      _ = Nat.card ↥(Uline Z B Y) := card_conjSubgroup r (Uline Z B Y)
      _ = Nat.card Z ^ 3 := hUcard
  have hPcard : Nat.card ↥P = Nat.card Z ^ 3 := by
    rw [hPeq, card_conjSubgroup]
    exact hUcard
  have hprod := card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hInfZ', hUAcard, hPcard] at hprod
  have hcardsup : Nat.card ↥(Uline Z (conjSubgroup r B) Y ⊔ P) = Nat.card Z ^ 5 := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥Z))
    calc Nat.card ↥(Uline Z (conjSubgroup r B) Y ⊔ P) * Nat.card Z
        = Nat.card Z ^ 3 * Nat.card Z ^ 3 := hprod
      _ = Nat.card Z ^ 5 * Nat.card Z := by ring
  exact Subgroup.eq_of_le_of_card_ge (sup_le hUA_le hP_le)
    (by rw [hcardsup, hcardVnn])

private theorem pointT_eq_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {nn g : G}
    (hgM : g ∈ M) (hSY : conjSubgroup g (LB M Q B ⊓ Y) = LB M Q B ⊓ Y)
    (hP : planeST M Q Z B X nn g = conjSubgroup g (Uline Z B Y)) :
    pointT hc X Y nn g = conjSubgroup g B ⊔ Z := by
  have hCQt : conjSubgroup g (CQtGrp hc (LB M Q B ⊓ Y)) = CQtGrp hc (LB M Q B ⊓ Y) := by
    ext u
    rw [mem_conjSubgroup, mem_CQtGrp, mem_CQtGrp]
    have h := hc.mem_CQt_conj_iff hgM (LB M Q B ⊓ Y) u
    rw [hSY] at h
    exact h.symm
  unfold pointT
  rw [hP, ← hCQt, ← conjSubgroup_inf, uline_inf_CQt h34 h311a hc hs hsplit h4,
    conjSubgroup_sup', hc.conj_Z_eq hgM]

theorem sec97K13_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) (h1 : OneConcl hc X Y)
    {r : G} (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hcen : Centre95 hc t Z0) (hVn : Sec97VnStatement) {s nn : G} (hs0 : s ∈ Z0)
    (hsn : ConjMod M Q s nn) (hnn : nn ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t)
    (hnZ : nn ∉ Z0) :
    ∃ g : G, Sec97K13 hc t X Y r nn g ∧ conjSubgroup g Y = Y ∧
      pointT hc X Y nn g = conjSubgroup g B ⊔ Z := by
  classical
  have hsplit0 := hsplit
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, hYsl, -⟩ := hsplit
  have hYM : Y ≤ M := hYR.trans (Rt_le_M hc.LB_le_M t)
  obtain ⟨g₀, hg₀, hq, hYg₀, hVg₀, hRg₀⟩ :=
    five_transport h34 h311a hc hs hsplit0 h1 hr hZ0 hcen hs0 hsn hnn hnZ
  have hVnnInv : ∀ y ∈ Y, conjSubgroup y (Vt M (LB M Q B) B Z nn) =
      Vt M (LB M Q B) B Z nn :=
    fun y hy => conjSubgroup_Vt_nn_eq hc hs hsplit0 hYg₀ hVg₀ hy
  have hVnn_ne : Vt M (LB M Q B) B Z nn ≠ Vt M (LB M Q B) B Z t :=
    Vt_nn_ne_of_K hc hs hr hZ0 hVn hnn hnZ
  obtain ⟨x, hxX, hUne, hYgx⟩ := exists_x_ne h34 h311a hc hs hsplit0 hYg₀
  have hgxM : g₀ * x ∈ M := M.mul_mem hg₀ (hc.Rt_le_M t (hXR hxX))
  have hYr : conjSubgroup r Y = Y := hsplit0.conjSubgroup_eq_self_of_mem_Rt r hr.mem
  obtain ⟨y, hyY, hSYg⟩ := exists_conj_SY h34 hc hs hsplit0 h4 hYgx
  have hgM : g₀ * x * y ∈ M :=
    M.mul_mem hgxM (hc.Rt_le_M t (hYR hyY))
  have hYg : conjSubgroup (g₀ * x * y) Y = Y := by
    rw [conjSubgroup_mul, conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hyY),
      hYgx]
  have hPeq : planeST M Q Z B X nn (g₀ * x * y) =
      conjSubgroup (g₀ * x) (Uline Z B Y) :=
    planeST_eq_conj h34 h311a hc hs hsplit0 hg₀ hxX hyY hVg₀
  have hPeq' : planeST M Q Z B X nn (g₀ * x * y) =
      conjSubgroup (g₀ * x * y) (Uline Z B Y) := by
    rw [hPeq, conjSubgroup_mul (g₀ * x) y (Uline Z B Y)]
    rw [conj_Uline hc hYM hyY]
  have hcardVnn : Nat.card (Vt M (LB M Q B) B Z nn) = Nat.card Z ^ 5 := by
    rw [← hVg₀, card_conjSubgroup, hs.card_V]
  have hInf : Vt M (LB M Q B) B Z t ⊓ Vt M (LB M Q B) B Z nn =
      Uline Z (conjSubgroup r B) Y :=
    inf_eq_of h34 h311a hc hs hsplit0 hr hnn hVnnInv hcardVnn hVnn_ne
  have hInfZ : Uline Z (conjSubgroup r B) Y ⊓
      planeST M Q Z B X nn (g₀ * x * y) = Z :=
    inf_Z_of h34 h311a hc hs hsplit0 (hc.Rt_le_M t hr.mem) hYr hgxM hYgx hUne hPeq
  have hSup : Uline Z (conjSubgroup r B) Y ⊔
      planeST M Q Z B X nn (g₀ * x * y) = Vt M (LB M Q B) B Z nn :=
    sup_eq_of h34 h311a hc hs hsplit0 (hc.Rt_le_M t hr.mem) hxX hYr hVg₀ hInf hInfZ hPeq
  have hYle : Y ≤ Subgroup.normalizer
      (planeST M Q Z B X nn (g₀ * x * y) : Set G) := by
    have hP' : planeST M Q Z B X nn (g₀ * x * y) =
        Uline Z (conjSubgroup (g₀ * x) B) Y :=
      hPeq.trans (uline_conj (hc.conj_Z_eq hgxM) hYgx)
    rw [hP']
    exact le_normalizer_uline (hc.conj_of_mem hgxM) hYM
  have hPt : pointT hc X Y nn (g₀ * x * y) = conjSubgroup (g₀ * x * y) B ⊔ Z :=
    pointT_eq_of h34 h311a hc hs hsplit0 h4 hgM hSYg hPeq'
  refine ⟨g₀ * x * y, ?_, hYg, hPt⟩
  exact ⟨hgM, hInf, hSup, hInfZ, hYle, ⟨g₀ * x * y, hgM, hPt⟩⟩

end HS9

end CFSG.RankThree.GF2n.Stroth80

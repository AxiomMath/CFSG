module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourSz
public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightTwoB
public import CFSG.LocalAnalysis.WeakClosure81.W16Setup
public import CFSG.LocalAnalysis.WeakClosure81.W19Basic
import CFSG.LocalAnalysis.WeakClosure81.FourteenEightTwo
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem w183l31_N_ne_bot {M V₀ V : Subgroup G} {g : G} (h : Hyp64 2 M V₀ V g)
    (hm : 2 < mBar M V₀ V h.elemAbelian) (hU : E3.mQuot V (conjSubgroup M g) = 2) :
    NOf M V g ≠ ⊥ := by
  intro hNbot
  have hcomm0 : ⁅UOf M V g, BOf M V g⁆ ≤ NOf M V g := commutator_U_B_le_N h
  rw [hNbot] at hcomm0
  have hUle : UOf M V g ≤ Subgroup.centralizer (BOf M V g : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 (le_bot_iff.mp hcomm0)
  have hV0 : UOf M V g ≤ V₀ :=
    calc UOf M V g ≤ V ⊓ Subgroup.centralizer (BOf M V g : Set G) := by
          intro x hx
          exact ⟨(Subgroup.mem_inf.1 hx).1, hUle hx⟩
      _ = NOf M V g ⊔ V₀ := six_four_four_centralizer_V h
      _ = V₀ := by rw [hNbot, bot_sup_eq]
  have hmq : E3.mQuot V V₀ ≤ 2 := by
    have h1 : E3.mQuot V V₀ ≤ E3.mQuot V (UOf M V g) := E3.mQuot_mono hV0
    rwa [show UOf M V g = V ⊓ conjSubgroup M g from rfl, mQuot_inf_left, hU] at h1
  exact absurd (lt_of_lt_of_le hm (le_trans (mBar_le_mQuot h.elemAbelian h.le) hmq))
    (not_lt.2 le_rfl)

theorem w183l31_conjV₀_le_P {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g) :
    conjSubgroup V₀ g ≤ FourteenTwo.PSub M V₀ V ∧
      M ≤ Subgroup.normalizer ((FourteenTwo.PSub M V₀ V : Subgroup G) : Set G) := by
  have hB := six_four_four_centralizer_B_uncond h
  have hsub : conjSubgroup V₀ g ≤ BOf M V g ⊓ F11.CTilde M V₀ V := by
    rw [hB]; exact le_sup_right
  have hleCT : conjSubgroup V₀ g ≤ F11.CTilde M V₀ V := hsub.trans inf_le_right
  have hleB : conjSubgroup V₀ g ≤ BOf M V g := hsub.trans inf_le_left
  have hleM : conjSubgroup V₀ g ≤ M := hleB.trans inf_le_right
  have hV0cent : V₀ ≤ Subgroup.centralizer (BOf M V g : Set G) := by
    have h1 : V₀ ≤ NOf M V g ⊔ V₀ := le_sup_right
    rw [← six_four_four_centralizer_V h] at h1
    exact h1.trans inf_le_right
  have hleCent : conjSubgroup V₀ g ≤ Subgroup.centralizer (V₀ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact ((Subgroup.mem_centralizer_iff.1 (hV0cent hw)) x (hleB hx)).symm
  have hleP : conjSubgroup V₀ g ≤ FourteenTwo.PSub M V₀ V := fun x hx =>
    ⟨hleCT hx, hleM hx, hleCent hx⟩
  have hCn : M ≤ Subgroup.normalizer (Subgroup.centralizer (V₀ : Set G) : Set G) :=
    CFSG.Quasithin.B2F.le_normalizer_centralizer h.le_normalizer₀
  have hMn : M ≤ Subgroup.normalizer
      ((M ⊓ Subgroup.centralizer (V₀ : Set G) : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hCn).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hnorm : M ≤ Subgroup.normalizer ((FourteenTwo.PSub M V₀ V : Subgroup G) : Set G) :=
    (le_inf (le_normalizer_cTilde h) hMn).trans Subgroup.inf_normalizer_le_normalizer_inf
  exact ⟨hleP, hnorm⟩

theorem w183l31_not_centralizes {D : Data G} {V₀ V : Subgroup G}
    (hW : WeakClosureSetting D V₀ V) (hV₀ : V₀ ≠ ⊥) {h : G} (hyp : Hyp64 2 D.M V₀ V h)
    (hVh : ¬ V ≤ conjSubgroup D.M h) (hN : NOf D.M V h ≠ ⊥) :
    ∃ m ∈ D.M, ⁅NOf D.M V h, conjSubgroup (conjSubgroup V₀ h) m⁆ ≠ ⊥ := by
  classical
  by_contra hcon
  have hcon' : ∀ m ∈ D.M, ⁅NOf D.M V h, conjSubgroup (conjSubgroup V₀ h) m⁆ = ⊥ := by
    intro m hm
    by_contra hne
    exact hcon ⟨m, hm, hne⟩
  set V₁ : Subgroup G := conjSubgroup V₀ h with hV₁def
  set S : Set G := {x : G | ∃ m ∈ D.M, x ∈ conjSubgroup V₁ m} with hSdef
  have hSconj : ∀ m ∈ D.M, ∀ x ∈ S, m⁻¹ * x * m ∈ S := by
    rintro m hm x ⟨m', hm', hx'⟩
    refine ⟨m' * m, D.M.mul_mem hm' hm, ?_⟩
    have hmem : m⁻¹ * x * m ∈ conjSubgroup (conjSubgroup V₁ m') m := by
      rw [mem_conjSubgroup_iff]
      show m * (m⁻¹ * x * m) * m⁻¹ ∈ conjSubgroup V₁ m'
      rw [show m * (m⁻¹ * x * m) * m⁻¹ = x by group]
      exact hx'
    rwa [conjSubgroup_conjSubgroup] at hmem
  have hMW : D.M ≤
      Subgroup.normalizer ((V ⊓ Subgroup.centralizer S : Subgroup G) : Set G) := by
    intro m hm
    have hmV : m ∈ Subgroup.normalizer (V : Set G) := by
      rw [hW.normalizer_eq]
      exact hm
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rw [Subgroup.mem_inf] at hw
      rw [Subgroup.mem_centralizer_iff] at hw
      refine ⟨(Subgroup.mem_normalizer_iff.1 hmV w).1 hw.1, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
      have hyS : m⁻¹ * x * m ∈ S := hSconj m hm x hx
      calc x * (m * w * m⁻¹) = m * ((m⁻¹ * x * m) * w) * m⁻¹ := by group
        _ = m * (w * (m⁻¹ * x * m)) * m⁻¹ := by rw [hw.2 (m⁻¹ * x * m) hyS]
        _ = (m * w * m⁻¹) * x := by group
    · intro hw
      rw [Subgroup.mem_inf] at hw
      rw [Subgroup.mem_centralizer_iff] at hw
      refine ⟨(Subgroup.mem_normalizer_iff.1 hmV w).2 hw.1, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
      have hyS : m * x * m⁻¹ ∈ S := by
        have h1 := hSconj m⁻¹ (D.M.inv_mem hm) x hx
        rwa [inv_inv] at h1
      calc x * w = m⁻¹ * ((m * x * m⁻¹) * (m * w * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * w * m⁻¹) * (m * x * m⁻¹)) * m := by
              rw [hw.2 (m * x * m⁻¹) hyS]
        _ = w * x := by group
  have hNOf_le_W : NOf D.M V h ≤ V ⊓ Subgroup.centralizer S := by
    intro n hn
    refine ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hn).1).1, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    obtain ⟨m, hm, hxm⟩ := hx
    have hbot := hcon' m hm
    have hle : NOf D.M V h ≤ Subgroup.centralizer (conjSubgroup V₁ m : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hbot
    exact (Subgroup.mem_centralizer_iff.1 (hle hn)) x hxm
  have hWne : V ⊓ Subgroup.centralizer S ≠ V := by
    intro heq
    have hVleC : V ≤ Subgroup.centralizer S := by
      rw [← heq]
      exact inf_le_right
    have hV₁ne : V₁ ≠ ⊥ := by
      rw [hV₁def]
      intro hh
      exact hV₀ (conjSubgroup_eq_bot_iff.mp hh)
    obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hV₁ne
    have hwV₁ : (w : G) ∈ V₁ := w.2
    have hwne : (w : G) ≠ 1 := fun hh => hw1 (Subtype.ext hh)
    have hwV₀h : (w : G) ∈ conjSubgroup V₀ h := by simpa [hV₁def] using hwV₁
    have hwS : (w : G) ∈ S := by
      refine ⟨1, D.M.one_mem, ?_⟩
      rw [conjSubgroup_one]
      exact hwV₁
    have hsubw : ({(w : G)} : Set G) ⊆ S := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hwS
    have hVw : V ≤ Subgroup.centralizer ({(w : G)} : Set G) :=
      hVleC.trans (Subgroup.centralizer_le hsubw)
    exact hVh (hVw.trans (centralizer_le_conj_M hW hV₀ h hwV₀h hwne))
  have hWleV₀ : V ⊓ Subgroup.centralizer S ≤ V₀ :=
    le_of_normalizer_of_ne_of_conjGenerated (conjGenerated_of_weakClosureSetting hW hV₀)
      inf_le_left hMW hWne
  exact hN (by
    rw [← inf_eq_left.2 (hNOf_le_W.trans hWleV₀)]
    exact NOf_inf_eq_bot hyp)

theorem w183l31_conj_into_T {M T V₀ V P D B : Subgroup G} (hT : IsSylowIn 2 T M) (hPM : P ≤ M)
    (hPn : M ≤ Subgroup.normalizer (P : Set G)) (hV : IsElemAbelian 2 V)
    (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hPV : ∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ * v⁻¹ ∈ V₀) (hPV₀ : ∀ p ∈ P, ∀ w ∈ V₀, p * w = w * p)
    (hV₀V : V₀ ≤ V) (hDV : D ≤ V) (hBP : B ≤ P) (hB : IsElemAbelian 2 B) (hDB : ⁅D, B⁆ ≠ ⊥) :
    ∃ B' : Subgroup G, B' ≤ T ⊓ P ∧ IsElemAbelian 2 B' ∧ ⁅D, B'⁆ ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTP : IsSylowIn 2 (T ⊓ P) P :=
    hT.inf_normal hPM ((Subgroup.normal_subgroupOf_iff_le_normalizer hPM).2 hPn)
  have hB2 : IsPGroup 2 B := IsElemAbelian.isPGroup hB
  obtain ⟨p, hpP, hBp⟩ := CFSG.Quasithin.E3.exists_le_conj_of_isSylowIn hTP hBP hB2
  refine ⟨conjSubgroup B p⁻¹, ?_, CFSG.Quasithin.E3.isElemAbelian_conjSubgroup hB p⁻¹, ?_⟩
  · calc conjSubgroup B p⁻¹ ≤ conjSubgroup (conjSubgroup (T ⊓ P) p) p⁻¹ :=
        CFSG.Quasithin.E3.conjSubgroup_mono_left p⁻¹ hBp
      _ = T ⊓ P := CFSG.Quasithin.E3.conjSubgroup_conj_inv (T ⊓ P) p
  · have hex : ∃ d ∈ D, ∃ b ∈ B, ⁅d, b⁆ ≠ 1 := by
      by_contra hc
      have hle : ⁅D, B⁆ ≤ ⊥ := (Subgroup.commutator_le).2 fun d hd b hb => by
        have h1 : ⁅d, b⁆ = 1 := by
          by_contra hne
          exact hc ⟨d, hd, b, hb, hne⟩
        rw [h1]
        exact Subgroup.one_mem ⊥
      exact hDB (le_bot_iff.mp hle)
    obtain ⟨d, hd, b, hb, hdb⟩ := hex
    have hdV : d ∈ V := hDV hd
    have hbP : b ∈ P := hBP hb
    have hb' : p * b * p⁻¹ ∈ conjSubgroup B p⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have h : p⁻¹ * (p * b * p⁻¹) * p⁻¹⁻¹ = b := by group
      rwa [h]
    intro hbot
    have hmem : ⁅d, p * b * p⁻¹⁆ ∈ ⁅D, conjSubgroup B p⁻¹⁆ :=
      Subgroup.commutator_mem_commutator hd hb'
    rw [hbot, Subgroup.mem_bot] at hmem
    have hz : p⁻¹ * d * p * d⁻¹ ∈ V₀ := by
      simpa [inv_inv] using hPV p⁻¹ (P.inv_mem hpP) d hdV
    have hzV : p⁻¹ * d * p * d⁻¹ ∈ V := hV₀V hz
    have hbz : b * (p⁻¹ * d * p * d⁻¹) = (p⁻¹ * d * p * d⁻¹) * b :=
      hPV₀ b hbP (p⁻¹ * d * p * d⁻¹) hz
    have hbz' : (p⁻¹ * d * p * d⁻¹)⁻¹ * b⁻¹ =
        b⁻¹ * (p⁻¹ * d * p * d⁻¹)⁻¹ := by
      simpa [mul_inv_rev] using congrArg Inv.inv hbz
    have hcV : d * b * d⁻¹ * b⁻¹ ∈ V := by
      have h1 : b * d⁻¹ * b⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 (hMV (hPM hbP)) d⁻¹).1 (V.inv_mem hdV)
      rw [show d * b * d⁻¹ * b⁻¹ = d * (b * d⁻¹ * b⁻¹) by group]
      exact V.mul_mem hdV h1
    have hzc : (p⁻¹ * d * p * d⁻¹) * (d * b * d⁻¹ * b⁻¹) *
        (p⁻¹ * d * p * d⁻¹)⁻¹ = d * b * d⁻¹ * b⁻¹ := by
      rw [IsElemAbelian.comm hV hzV hcV]
      group
    have heq : ⁅p⁻¹ * d * p, b⁆ = d * b * d⁻¹ * b⁻¹ := by
      have hzd : p⁻¹ * d * p = (p⁻¹ * d * p * d⁻¹) * d := by group
      rw [hzd, commutatorElement_def]
      rw [show ((p⁻¹ * d * p * d⁻¹) * d)⁻¹ = d⁻¹ * (p⁻¹ * d * p * d⁻¹)⁻¹ by group]
      rw [show (p⁻¹ * d * p * d⁻¹) * d * b * (d⁻¹ * (p⁻¹ * d * p * d⁻¹)⁻¹) * b⁻¹
          = (p⁻¹ * d * p * d⁻¹) * (d * b * d⁻¹) *
            ((p⁻¹ * d * p * d⁻¹)⁻¹ * b⁻¹) by group]
      rw [hbz']
      rw [show (p⁻¹ * d * p * d⁻¹) * (d * b * d⁻¹) *
            (b⁻¹ * (p⁻¹ * d * p * d⁻¹)⁻¹)
          = (p⁻¹ * d * p * d⁻¹) * (d * b * d⁻¹ * b⁻¹) *
            (p⁻¹ * d * p * d⁻¹)⁻¹ by group]
      exact hzc
    have hne1 : ⁅p⁻¹ * d * p, b⁆ ≠ 1 := by
      rw [heq, ← commutatorElement_def]
      exact hdb
    have hconj : ⁅d, p * b * p⁻¹⁆ = p * ⁅p⁻¹ * d * p, b⁆ * p⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    have hne : ⁅d, p * b * p⁻¹⁆ ≠ 1 := by
      rw [hconj]
      intro h1
      exact hne1 (by
        have h2 : ⁅p⁻¹ * d * p, b⁆ =
            p⁻¹ * (p * ⁅p⁻¹ * d * p, b⁆ * p⁻¹) * p := by group
        rw [h1] at h2
        simpa using h2)
    exact hne hmem

theorem w183l31_exists_conj {D : Data G} {V₀ V : Subgroup G} (hW : WeakClosureSetting D V₀ V)
    (hV₀ : V₀ ≠ ⊥) {h : G} (hyp : Hyp64 2 D.M V₀ V h) (hVh : ¬ V ≤ conjSubgroup D.M h)
    (hN : NOf D.M V h ≠ ⊥) :
    ∃ B : Subgroup G, B ≤ D.T ⊓ FourteenTwo.PSub D.M V₀ V ∧ IsElemAbelian 2 B ∧
      ⁅NOf D.M V h, B⁆ ≠ ⊥ := by
  obtain ⟨m, hmM, hmne⟩ := w183l31_not_centralizes hW hV₀ hyp hVh hN
  have hP := w183l31_conjV₀_le_P hyp
  have hB0P : conjSubgroup (conjSubgroup V₀ h) m ≤ FourteenTwo.PSub D.M V₀ V := by
    calc conjSubgroup (conjSubgroup V₀ h) m ≤ conjSubgroup (FourteenTwo.PSub D.M V₀ V) m :=
          CFSG.Quasithin.E3.conjSubgroup_mono_left m hP.1
      _ = FourteenTwo.PSub D.M V₀ V :=
          (conjSubgroup_eq_iff_mem_normalizer).2 (hP.2 hmM)
  have hB0elem : IsElemAbelian 2 (conjSubgroup (conjSubgroup V₀ h) m) :=
    CFSG.Quasithin.E3.isElemAbelian_conjSubgroup
      (IsElemAbelian.mono (CFSG.Quasithin.E3.isElemAbelian_conjSubgroup hyp.elemAbelian h)
        (CFSG.Quasithin.E3.conjSubgroup_mono_left h hyp.le)) m
  have hT : IsSylowIn 2 D.T D.M := isSylowOf_two_iff_isSylowIn.mp D.sylowM
  have hPM : FourteenTwo.PSub D.M V₀ V ≤ D.M := inf_le_right.trans inf_le_left
  have hPV : ∀ p ∈ FourteenTwo.PSub D.M V₀ V, ∀ v ∈ V, p * v * p⁻¹ * v⁻¹ ∈ V₀ := by
    intro p hp v hv
    have hpCT : p ∈ F11.CTilde D.M V₀ V := (Subgroup.mem_inf.1 hp).1
    exact (FourteenTwo.mem_cTilde_iff_comm.1 hpCT).2.2 v hv
  have hPV₀ : ∀ p ∈ FourteenTwo.PSub D.M V₀ V, ∀ w ∈ V₀, p * w = w * p := by
    intro p hp w hw
    have hpC : p ∈ Subgroup.centralizer (V₀ : Set G) :=
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hp).2).2
    exact (Subgroup.mem_centralizer_iff.1 hpC w hw).symm
  have hDV : NOf D.M V h ≤ V := inf_le_left.trans inf_le_left
  have hMV : D.M ≤ Subgroup.normalizer (V : Set G) := hyp.normalizer_eq.symm.le
  exact w183l31_conj_into_T hT hPM hP.2 hyp.elemAbelian hMV hPV hPV₀ hyp.le hDV
    hB0P hB0elem hmne

theorem w183l31_false_of_normalizes {D : Data G} {V₀ V : Subgroup G}
    (hW : WeakClosureSetting D V₀ V) (hV₀ : V₀ ≠ ⊥) {h : G} (hyp : Hyp64 2 D.M V₀ V h)
    (hVh : ¬ V ≤ conjSubgroup D.M h) (hN : NOf D.M V h ≠ ⊥)
    (hTN : D.T ≤ Subgroup.normalizer ((NOf D.M V h : Subgroup G) : Set G)) : False := by
  obtain ⟨B, hBle, -, hBne⟩ := w183l31_exists_conj hW hV₀ hyp hVh hN
  have hcomm_le : ⁅NOf D.M V h, B⁆ ≤ NOf D.M V h ⊓ V₀ := by
    rw [Subgroup.commutator_le]
    intro d hd b hb
    refine ⟨?_, ?_⟩
    · have hbT : b ∈ D.T := (Subgroup.mem_inf.1 (hBle hb)).1
      have hbN : b * d⁻¹ * b⁻¹ ∈ NOf D.M V h :=
        (Subgroup.mem_normalizer_iff.1 (hTN hbT) d⁻¹).1 ((NOf D.M V h).inv_mem hd)
      rw [commutatorElement_def]
      rw [show d * b * d⁻¹ * b⁻¹ = d * (b * d⁻¹ * b⁻¹) by group]
      exact (NOf D.M V h).mul_mem hd hbN
    · have hbP : b ∈ FourteenTwo.PSub D.M V₀ V := (Subgroup.mem_inf.1 (hBle hb)).2
      have hdV : d ∈ V := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hd).1).1
      have h1 : b * d * b⁻¹ * d⁻¹ ∈ V₀ :=
        (FourteenTwo.mem_cTilde_iff_comm.1 (Subgroup.mem_inf.1 hbP).1).2.2 d hdV
      rw [commutatorElement_def]
      rw [show d * b * d⁻¹ * b⁻¹ = (b * d * b⁻¹ * d⁻¹)⁻¹ by group]
      exact V₀.inv_mem h1
  have hbot : ⁅NOf D.M V h, B⁆ = ⊥ :=
    le_bot_iff.mp (hcomm_le.trans (le_of_eq (NOf_inf_eq_bot hyp)))
  exact hBne hbot

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end

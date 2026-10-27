module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsCentre
public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77PairModel
public import CFSG.RankThree.GF2n.Stroth80.Sec7HypConj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem comm_Ut_of_vanish_mod_Z (hc : Ctx M Q Z B) {y a : G} (hyH : y ∈ H0 M Z) (haQ : a ∈ Q)
    (hya : ⁅y, a⁆ ∈ Z) : ∀ b ∈ Ut Q Z y, ⁅a, b⁆ = 1 := by
  have hZQ : ∀ z ∈ Z, ∀ v ∈ Q, v * z * v⁻¹ = z := fun z hz v hv => by
    have h := hc.hyp.toHyp79.V_central hz hv
    calc v * z * v⁻¹ = (v * z) * v⁻¹ := by group
      _ = (z * v) * v⁻¹ := by rw [← h]
      _ = z := by group
  let S₁ : Subgroup G :=
    { carrier := {v | v ∈ Q ∧ ⁅y, v⁆ ∈ Z}
      mul_mem' := fun {v v'} hv hv' => ⟨Q.mul_mem hv.1 hv'.1, by
        have e : ⁅y, v * v'⁆ = ⁅y, v⁆ * (v * ⁅y, v'⁆ * v⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e, hZQ _ hv'.2 v hv.1]
        exact Z.mul_mem hv.2 hv'.2⟩
      one_mem' := ⟨Q.one_mem, by
        rw [commutatorElement_one_right]
        exact Z.one_mem⟩
      inv_mem' := fun {v} hv => ⟨Q.inv_mem hv.1, by
        have e : ⁅y, v⁻¹⁆ = v⁻¹ * (⁅y, v⁆)⁻¹ * v⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e, hZQ _ (Z.inv_mem hv.2) v⁻¹ (Q.inv_mem hv.1)]
        exact Z.inv_mem hv.2⟩ }
  have hVQ : Subgroup.zpowers a ≤ Q := Subgroup.zpowers_le.mpr haQ
  have hvan : ∀ v ∈ Subgroup.zpowers a, ⁅y, v⁆ ∈ Z := fun v hv =>
    ((Subgroup.zpowers_le.mpr (show a ∈ S₁ from ⟨haQ, hya⟩)) hv).2
  have hUW := Ut_le_Wt_of_vanish hc hVQ hyH hvan
  intro b hb
  have hbW := hUW hb
  have h1 := Subgroup.mem_centralizer_iff.mp hbW.2 a (Subgroup.mem_zpowers a)
  exact commutatorElement_eq_one_iff_mul_comm.mpr h1

theorem conc71abcd_of_conj (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) (t : G) (n : ℕ)
    (h : Conc71abcd (hc.conj_of_mem hm) n (m * t * m⁻¹)) : Conc71abcd hc n t := by
  have hQn : ∀ x ∈ Q, m⁻¹ * x * m ∈ Q := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hm)) x).mp hx
    simpa using this
  unfold Conc71abcd at h ⊢
  rcases h with h | h | h | h
  · left
    unfold Conc71a at h ⊢
    obtain ⟨s', hs'R, hcomm, g', hg'M, hg'L, hg'N⟩ := h
    rw [rt_conj_of_mem hc hm t] at hs'R hcomm
    rw [hc.LB_conj hm] at hg'L
    rw [cn_conj_of_mem hc hm t] at hg'N
    refine ⟨m⁻¹ * s' * m, mem_conjSubgroup.mp hs'R, fun r hr => ?_, m⁻¹ * g' * m,
      M.mul_mem (M.mul_mem (M.inv_mem hm) hg'M) hm, ?_, ?_⟩
    · have hr' : m * r * m⁻¹ ∈ conjSubgroup m (Rt M (LB M Q B) t) := by
        rw [mem_conjSubgroup]
        have e : m⁻¹ * (m * r * m⁻¹) * m = r := by group
        rw [e]
        exact hr
      have h1 := hcomm _ hr'
      have e : ⁅m⁻¹ * s' * m, r⁆ = m⁻¹ * ⁅s', m * r * m⁻¹⁆ * m := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hQn _ h1
    · have h1 := mem_conjSubgroup.mp hg'L
      have e : (m⁻¹ * g' * m) * (m⁻¹ * s' * m) * (m⁻¹ * g' * m)⁻¹ =
          m⁻¹ * (g' * s' * g'⁻¹) * m := by group
      rw [e]
      exact h1
    · intro hcn
      apply hg'N
      rw [mem_conjSubgroup]
      have e : m⁻¹ * (g' * s' * g'⁻¹) * m =
          (m⁻¹ * g' * m) * (m⁻¹ * s' * m) * (m⁻¹ * g' * m)⁻¹ := by group
      rw [e]
      exact hcn
  · right
    left
    unfold Conc71b at h ⊢
    exact ⟨(omegaMinusNat_conj_of_mem hc hm t 3).mp h.1, h.2⟩
  · right
    right
    left
    unfold Conc71c at h ⊢
    exact ⟨(omegaPlusNat_conj_of_mem hc hm t 3).mp h.1, h.2⟩
  · right
    right
    right
    unfold Conc71d at h ⊢
    exact ⟨(omegaPlusNat_conj_of_mem hc hm t 4).mp h.1, h.2⟩

theorem step76EightTamePair_of (hV : Step71VanishStatement) (hZV : Sec7ZVStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec7Hyp hc n t → ¬ Conc71abcd hc n t →
      ∀ f ∈ LB M Q B, ConjMod M Q t f → ∀ f' ∈ LB M Q B, ConjMod M Q t f' →
      ∀ a ∈ Ut Q Z f, ∀ b ∈ Ut Q Z f', ⁅a, b⁆ = 1 := by
  intro G _ _ M Q Z B hc n t hs hno f hfL hfc f' hf'L hf'c a ha b hb
  classical
  haveI := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hQn : ∀ m ∈ M, ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) y).mp hy
  obtain ⟨hfM, g, hgM, hq⟩ := hfc
  obtain ⟨hf'M, g', hg'M, hq'⟩ := hf'c
  have hf'H : f' ∈ H0 M Z := hc.LB_le_H0 hf'L
  have hu : g * t * g⁻¹ ∈ H0 M Z := sec7_conj_mem_H0 hc hgM (hc.LB_le_H0 ht)
  have hfq : f = (f * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) := by group
  have hUtf : Ut Q Z f = conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    refine (congrArg (Ut Q Z) hfq).trans ((Ut_mul_Q hc hu hq).trans ?_)
    rw [Ut_conj_of_normalizes (hc.conj_Q_eq hgM) (hc.conj_Z_eq hgM) t,
      hZV G M Q Z B hc n t hs Z0 hZ0 t htZ0 hs.toSec5.notQ]
  have hs' := sec7Hyp_conj_of_mem hc hs hgM
  have hno' : ¬ Conc71abcd (hc.conj_of_mem hgM) n (g * t * g⁻¹) := fun h =>
    hno (conc71abcd_of_conj hc hgM t n h)
  have hx : ConjMod M Q (g * t * g⁻¹) f' := ⟨hf'M, g' * g⁻¹, M.mul_mem hg'M (M.inv_mem hgM), by
    have e : (g' * g⁻¹) * (g * t * g⁻¹) * (g' * g⁻¹)⁻¹ = g' * t * g'⁻¹ := by group
    rw [e]
    exact hq'⟩
  have hxt : ⁅f', g * t * g⁻¹⁆ ∈ Q := by
    have hq1 : (f * (g * t * g⁻¹)⁻¹)⁻¹ ∈ Q := Q.inv_mem hq
    have e : ⁅f', g * t * g⁻¹⁆ = ⁅f', (f * (g * t * g⁻¹)⁻¹)⁻¹⁆ *
        ((f * (g * t * g⁻¹)⁻¹)⁻¹ * ⁅f', f⁆ * (f * (g * t * g⁻¹)⁻¹)) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine Q.mul_mem ?_ (Q.mul_mem (Q.mul_mem hq1 ?_) hq)
    · exact Q.mul_mem (hQn f' hf'M _ hq1) (Q.inv_mem hq1)
    · exact hc.commutator_LB_le_Q (Subgroup.commutator_mem_commutator hf'L hfL)
  have hvan := hV G M Q Z (conjSubgroup g B) (hc.conj_of_mem hgM) n (g * t * g⁻¹) hs' hno' f' hx
    hxt
  rw [vt_conj_of_mem hc hgM t] at hvan
  rw [hUtf] at ha
  have haQ : a ∈ Q := hc.conjSubgroup_le_Q (hc.Vt_le_Q t) hgM ha
  exact comm_Ut_of_vanish_mod_Z hc hf'H haQ (hvan a ha) b hb

end CFSG.RankThree.GF2n.Stroth80

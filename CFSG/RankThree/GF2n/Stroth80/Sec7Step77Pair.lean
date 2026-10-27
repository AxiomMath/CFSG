module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsComm
public import CFSG.RankThree.GF2n.Stroth80.Sec7LinA0
public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77FromOneParts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_pair_vanish (h71 : Stroth71Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hno : ¬ Conc71abcd hc n t) {g s : G} (hgM : g ∈ M)
    (hs1 : s * (g * t * g⁻¹)⁻¹ ∈ Q) (hs2 : ⁅s, t⁆ ∈ Q) :
    ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅s, v⁆ ∈ Z := by
  rcases h71 G M Q Z B hc n t hs with h | he
  · exact absurd h hno
  have htM : t ∈ M := hc.LB_le_M hs.toSec5.mem
  have hguM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM htM) (M.inv_mem hgM)
  have hsM : s ∈ M := by
    have h1 : s = (s * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) := by group
    rw [h1]
    exact M.mul_mem (hc.hyp.Q_normal.1 hs1) hguM
  exact he.2.2 s ⟨hsM, g, hgM, hs1⟩ hs2

theorem sec7_pair_conj_mem_W (h71 : Stroth71Statement) (h310chi : Stroth310ChiStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hno : ¬ Conc71abcd hc n t)
    {g s : G} (hgM : g ∈ M) (hs1 : s * (g * t * g⁻¹)⁻¹ ∈ Q) (hs2 : ⁅s, t⁆ ∈ Q) :
    ∀ v ∈ Vt M (LB M Q B) B Z t, g⁻¹ * v * g ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
  intro v hv
  have htM : t ∈ M := hc.LB_le_M hs.toSec5.mem
  have hguM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM htM) (M.inv_mem hgM)
  have hvQ : v ∈ Q := hc.Vt_le_Q t hv
  have hv'Q : g⁻¹ * v * g ∈ Q := (hc.conj_mem_Q_of_mem_M hgM).2 v hvQ
  have hsv := sec7_pair_vanish h71 hc hs hno hgM hs1 hs2 v hv
  have hq' : (g * t * g⁻¹)⁻¹ * s ∈ Q := by
    have h1 := (hc.conj_mem_Q_of_mem_M (M.inv_mem hguM)).1 _ hs1
    have e : (g * t * g⁻¹)⁻¹ * (s * (g * t * g⁻¹)⁻¹) * ((g * t * g⁻¹)⁻¹)⁻¹ =
        (g * t * g⁻¹)⁻¹ * s := by group
    rwa [e] at h1
  have hs_eq : s = (g * t * g⁻¹) * ((g * t * g⁻¹)⁻¹ * s) := by group
  have huv : ⁅g * t * g⁻¹, v⁆ ∈ Z := by
    rw [hs_eq] at hsv
    exact (comm_mul_Q_mem_Z_iff hc hguM hq' hvQ).mp hsv
  have htv : ⁅t, g⁻¹ * v * g⁆ ∈ Z := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hgM)) _).mp huv
    have e : g⁻¹ * ⁅g * t * g⁻¹, v⁆ * g⁻¹⁻¹ = ⁅t, g⁻¹ * v * g⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h1
  have hW := (h310chi G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat)).2
  rw [hW, hc.mem_Q1_iff htM]
  exact ⟨hv'Q, htv⟩

theorem step77FromOneNotCentre_of_inputs (h71 : Stroth71Statement)
    (h310chi : Stroth310ChiStatement) (hZV : Sec7ZVStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) : Step77FromOneNotCentreStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 hV y hy ⟨v, hv, hyv⟩ hyZ0
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hd : g⁻¹ * y * g ∈ LB M Q B ⊓ hc.CN t := mem_conjSubgroup.mp hy
  have hdM : g⁻¹ * y * g ∈ M := hc.LB_le_M hd.1
  have hyM : y ∈ M := by
    have h3 := M.mul_mem (M.mul_mem hgM hdM) (M.inv_mem hgM)
    simpa [mul_assoc] using h3
  have hyt : y * t * y⁻¹ ∉ Q := by
    intro h
    apply hs.toSec5.notQ
    have h4 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hyM))
      (y * t * y⁻¹)).mp h
    have h3 : y⁻¹ * (y * t * y⁻¹) * y⁻¹⁻¹ = t := by group
    rwa [h3] at h4
  have hZu : Ut Q Z t = Vt M (LB M Q B) B Z t := hZV G M Q Z B hc n t hs Z0 hZ0 t htZ0
    hs.toSec5.notQ
  have hZu' : Ut Q Z (y * t * y⁻¹) = Vt M (LB M Q B) B Z t :=
    hZV G M Q Z B hc n t hs Z0 hZ0 (y * t * y⁻¹) hyZ0 hyt
  have hconj := Ut_conj_of_normalizes (hc.conj_Q_eq hyM) (hc.conj_Z_eq hyM) t
  have hyV : conjSubgroup y (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    ((congrArg (conjSubgroup y) hZu).symm.trans hconj.symm).trans hZu'
  have hyN : y ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    conjSubgroup_eq_self_iff.mp hyV
  have h1 : ⁅y, v⁆ ∈ Vt M (LB M Q B) B Z t := by
    have h2 : y * v * y⁻¹ ∈ Vt M (LB M Q B) B Z t := (Subgroup.mem_normalizer_iff.mp hyN v).mp hv
    have e : ⁅y, v⁆ = (y * v * y⁻¹) * v⁻¹ := rfl
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem h2 ((Vt M (LB M Q B) B Z t).inv_mem hv)
  have hv' := sec7_pair_conj_mem_W h71 h310chi hc hs hno hgM hs1 hs2 v hv
  have h3 := sec7_N_comm_W_le_V h52a hA hc hs (g⁻¹ * y * g) hd.2 (g⁻¹ * v * g) hv'
  have h4 : ⁅y, v⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    rw [mem_conjSubgroup]
    have e : g⁻¹ * ⁅y, v⁆ * g = ⁅g⁻¹ * y * g, g⁻¹ * v * g⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h3
  have h5 : ⁅y, v⁆ ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    ⟨h1, h4⟩
  rw [hV] at h5
  exact hyv h5


theorem sec7_pair_mem_W (h71 : Stroth71Statement) (h310chi : Stroth310ChiStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hno : ¬ Conc71abcd hc n t)
    {g s : G} (hgM : g ∈ M) (hs1 : s * (g * t * g⁻¹)⁻¹ ∈ Q) (hs2 : ⁅s, t⁆ ∈ Q) :
    ∀ v ∈ Vt M (LB M Q B) B Z t, g * v * g⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
  intro v hv
  refine ⟨(hc.conj_mem_Q_of_mem_M hgM).1 v (hc.Vt_le_Q t hv),
    Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  have hu := (sec7_pair_conj_mem_W h71 h310chi hc hs hno hgM hs1 hs2 w hw).2
  have h1 := Subgroup.mem_centralizer_iff.mp hu v hv
  calc w * (g * v * g⁻¹) = g * ((g⁻¹ * w * g) * v) * g⁻¹ := by group
    _ = g * (v * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
    _ = g * v * g⁻¹ * w := by group

theorem sec7_D1_comm_mem (h71 : Stroth71Statement) (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hno : ¬ Conc71abcd hc n t)
    {g s : G} (hgM : g ∈ M) (hs1 : s * (g * t * g⁻¹)⁻¹ ∈ Q) (hs2 : ⁅s, t⁆ ∈ Q)
    {y : G} (hy : y ∈ conjSubgroup g (LB M Q B ⊓ hc.CN t)) :
    ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅y, v⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
  intro v hv
  have hd : g⁻¹ * y * g ∈ LB M Q B ⊓ hc.CN t := mem_conjSubgroup.mp hy
  have hv' := sec7_pair_conj_mem_W h71 h310chi hc hs hno hgM hs1 hs2 v hv
  have h3 := sec7_N_comm_W_le_V h52a hA hc hs (g⁻¹ * y * g) hd.2 (g⁻¹ * v * g) hv'
  rw [mem_conjSubgroup]
  have e : g⁻¹ * ⁅y, v⁆ * g = ⁅g⁻¹ * y * g, g⁻¹ * v * g⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact h3

theorem sec7_comm_mul_inv_mem_Z (hc : Ctx M Q Z B) {a b v : G} (ha : a ∈ M) (hb : b ∈ M)
    (hav : ⁅a, v⁆ ∈ Z) (hbv : ⁅b, v⁆ ∈ Z) : ⁅a * b⁻¹, v⁆ ∈ Z := by
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  have h1 : ⁅b⁻¹, v⁆ = (b⁻¹ * ⁅b, v⁆ * b)⁻¹ := by
    simp only [commutatorElement_def]
    group
  have h2 : b⁻¹ * ⁅b, v⁆ * b ∈ Z := by
    have := hZn b⁻¹ (M.inv_mem hb) _ hbv
    simpa using this
  have h3 : ⁅a * b⁻¹, v⁆ = a * ⁅b⁻¹, v⁆ * a⁻¹ * ⁅a, v⁆ := by
    simp only [commutatorElement_def]
    group
  rw [h3, h1]
  exact Z.mul_mem (hZn a ha _ (Z.inv_mem h2)) hav

theorem step77FromOneComm_of_inputs (h34 : Stroth34Statement) (h71 : Stroth71Statement)
    (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hZcard : Sec7ZCardStatement) (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement) :
    Step77FromOneCommStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 hV y hy
  haveI := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) :=
    sec7_V_le_W h310chi hc hs
  have hWQ1 : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅t, w⁆ ∈ Z := by
    intro w hw
    have hW := (h310chi G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat)).2
    rw [hW, hc.mem_Q1_iff htM] at hw
    exact hw.2
  have hD1 : ∀ y ∈ conjSubgroup g (LB M Q B ⊓ hc.CN t), y ∈ M ∧ y ∈ H0 M Z ∧
      ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅y, v⁆ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
    intro y hy
    have hd : g⁻¹ * y * g ∈ LB M Q B ⊓ hc.CN t := mem_conjSubgroup.mp hy
    have hdM : g⁻¹ * y * g ∈ M := hc.LB_le_M hd.1
    have hyM : y ∈ M := by
      have h3 := M.mul_mem (M.mul_mem hgM hdM) (M.inv_mem hgM)
      simpa [mul_assoc] using h3
    refine ⟨hyM, ⟨hyM, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩, fun v hv => ?_⟩
    · have hz' : g⁻¹ * z * g ∈ Z := by
        have : z ∈ conjSubgroup g Z := by rw [hc.conj_Z_eq hgM]; exact hz
        exact mem_conjSubgroup.mp this
      have h1 := hc.LB_centralizes_Z hd.1 _ hz'
      calc z * y = g * (g⁻¹ * z * g) * g⁻¹ * y := by group
        _ = g * ((g⁻¹ * y * g) * (g⁻¹ * z * g) * (g⁻¹ * y * g)⁻¹) * g⁻¹ * y := by rw [h1]
        _ = y * z := by group
    · have hmem := sec7_D1_comm_mem h71 h310chi h52a hA hc hs hno hgM hs1 hs2 hy v hv
      have h2 := sec7_pair_mem_W h71 h310chi hc hs hno hgM hs1 hs2 (g⁻¹ * ⁅y, v⁆ * g)
        (mem_conjSubgroup.mp hmem)
      have e : g * (g⁻¹ * ⁅y, v⁆ * g) * g⁻¹ = ⁅y, v⁆ := by group
      rwa [e] at h2
  obtain ⟨hyM, hyH, hyW⟩ := hD1 y hy
  obtain ⟨-, -, hyiW⟩ := hD1 y⁻¹ ((conjSubgroup g (LB M Q B ⊓ hc.CN t)).inv_mem hy)
  have htH : t ∈ H0 M Z := hc.LB_le_H0 ht
  have hty : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅y * t * y⁻¹, v⁆ ∈ Z := by
    intro v hv
    have h1 : y⁻¹ * v * y ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
      have e : y⁻¹ * v * y = ⁅y⁻¹, v⁆ * v := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (Wt Q (Vt M (LB M Q B) B Z t)).mul_mem (hyiW v hv) (hVW hv)
    have h2 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hyM) _).mp (hWQ1 _ h1)
    have e : y * ⁅t, y⁻¹ * v * y⁆ * y⁻¹ = ⁅y * t * y⁻¹, v⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h2
  have htv : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅t, v⁆ ∈ Z := fun v hv => hWQ1 v (hVW hv)
  have hytM : y * t * y⁻¹ ∈ M := M.mul_mem (M.mul_mem hyM htM) (M.inv_mem hyM)
  have hcV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅t * (y * t * y⁻¹)⁻¹, v⁆ ∈ Z := fun v hv =>
    sec7_comm_mul_inv_mem_Z hc htM hytM (htv v hv) (hty v hv)
  have hcH : t * (y * t * y⁻¹)⁻¹ ∈ H0 M Z :=
    (H0 M Z).mul_mem htH ((H0 M Z).inv_mem
      ((H0 M Z).mul_mem ((H0 M Z).mul_mem hyH htH) ((H0 M Z).inv_mem hyH)))
  have hc0 := sec7_comm_Z0_of_vanish h34 h310chi hZc hZV hZcard hc hs hZ0 hcH hcV t htZ0
  have hnorm : ∀ m ∈ M, ∀ x ∈ Q, m * x * m⁻¹ ∈ Q := fun m hm x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) x).mp hx
  have e : ⁅y * t * y⁻¹, t⁆ =
      ((y * t * y⁻¹) * (t⁻¹ * ⁅t * (y * t * y⁻¹)⁻¹, t⁆ * t) * (y * t * y⁻¹)⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  refine Q.inv_mem (hnorm _ hytM _ ?_)
  have := hnorm t⁻¹ (M.inv_mem htM) _ hc0
  simpa using this


theorem step77FromOneCore_of_moves_meet (h34 : Stroth34Statement) (h71 : Stroth71Statement)
    (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hZcard : Sec7ZCardStatement) (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (hMoves : Step77FromOneMovesStatement) (hMeet : Step77FromOneMeetStatement) :
    Step77FromOneCoreStatement :=
  step77FromOneCore_of_parts hMoves
    (step77FromOneComm_of_inputs h34 h71 h310chi hZc hZV hZcard h52a hA)
    (step77FromOneNotCentre_of_inputs h71 h310chi hZV h52a hA) hMeet

end CFSG.RankThree.GF2n.Stroth80

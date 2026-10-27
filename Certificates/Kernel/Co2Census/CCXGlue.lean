module

public import Certificates.Kernel.Co2Census.CCXDefs
public import Certificates.Kernel.Co2Census.CCRep

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.KC.Co2InvS
  CFSG.KC.Co2Census CFSG.KC.Loop Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

set_option maxRecDepth 100000

section CC


theorem rec_elt {NC ng nr : ℕ} {CP CX CG CGR : ℕ → ℕ}
    (htree : ∀ i < NC, treeK (rmStep CGR) ng NC CP CX i = true)
    (hroot : ∀ i < NC, Nat.beq (rtOf CX i) 0 = true) (hmisc : centMisc CP CG CGR ng nr = true)
    (hcent : {y | ∃ i < NC, repK y (CP i)} = centS0 (sElt nr)) :
    (∀ i < NC, ∃ s ∈ centS0 (sElt nr), repK s (CP i)) ∧
      ∀ i < NC, ∀ j < NC, CP i = CP j → i = j := by
  simp only [centMisc, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_range] at hmisc
  obtain ⟨h0, hg⟩ := hmisc
  have hsteps : MulSteps repK (rmStep CGR) ng fun l => sElt (CG l) := by
    intro l hl x M hx
    have e : rmStep CGR l M = mulV M (SK (CG l)) := by
      rw [rmStep, (hg l hl).1]
    rw [e]
    exact repK_mul hx (repK_sElt _)
  have h1 : repK 1 (CP 0) := by
    rw [h0]
    exact repK_one
  have tf := treeK_sound htree
  refine ⟨fun i hi => ?_, tf.2⟩
  obtain ⟨-, -, hr⟩ := tf.1 i hi
  rw [Nat.eq_of_beq_eq_true (hroot i hi)] at hr
  obtain ⟨w, -, hw⟩ := reach_mul hsteps hr h1
  rw [one_mul] at hw
  have hm : w ∈ {y | ∃ i < NC, repK y (CP i)} := ⟨i, hi, hw⟩
  rw [hcent] at hm
  exact ⟨w, hm, hw⟩

theorem piC_eq_one_iff (u : Cz) : piC u = 1 ↔ u ∈ CFSG.pCore 2 Cz := by
  constructor
  · intro h
    have h' : cfgCz.rho u = 1 := Subtype.ext h
    rw [SmithConfig.rho_eq_iff, map_one, inv_one, one_mul] at h'
    exact h'
  · intro h
    show ((cfgCz.rho u : S0) : K) = 1
    rw [cfgCz.rho_E ⟨u, h⟩, Subgroup.coe_one]

theorem piC_qE (e : ℕ) : piC (qE e : Cz) = 1 := (piC_eq_one_iff _).2 (qE e).2

theorem mem_dlK {R : ℕ} {r : Cz} (hr : repK (r : K) R) {e : ℕ} :
    e ∈ dlK QKt R ↔ e < 512 ∧ (qE e : Cz) * r = r * qE e := by
  unfold dlK commK
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨he, h⟩
    exact ⟨he, (cz_eq_iff (repK_czmul (repK_qE he) hr) (repK_czmul hr (repK_qE he))).2
      (Nat.eq_of_beq_eq_true h)⟩
  · rintro ⟨he, h⟩
    refine ⟨he, ?_⟩
    rw [Nat.beq_eq]
    exact (cz_eq_iff (repK_czmul (repK_qE he) hr) (repK_czmul hr (repK_qE he))).1 h

noncomputable def recS {NC nr : ℕ} {CP : ℕ → ℕ}
    (hex : ∀ i < NC, ∃ s ∈ centS0 (sElt nr), repK s (CP i)) (j : ℕ) : K :=
  if h : j < NC then (hex j h).choose else 1

theorem recS_spec {NC nr : ℕ} {CP : ℕ → ℕ}
    (hex : ∀ i < NC, ∃ s ∈ centS0 (sElt nr), repK s (CP i)) {j : ℕ} (hj : j < NC) :
    recS hex j ∈ centS0 (sElt nr) ∧ repK (recS hex j) (CP j) := by
  simp only [recS, dif_pos hj]
  exact (hex j hj).choose_spec

noncomputable def liftX {NC nr : ℕ} {CP : ℕ → ℕ}
    (hex : ∀ i < NC, ∃ s ∈ centS0 (sElt nr), repK s (CP i)) (L : ℕ → ℕ) (j : ℕ) : Cz :=
  if h : j < NC then ⟨recS hex j, S0_le_Cz (recS_spec hex h).1.1⟩ * (qE (L j) : Cz) else 1

theorem liftX_spec {NC nr : ℕ} {CP : ℕ → ℕ}
    (hex : ∀ i < NC, ∃ s ∈ centS0 (sElt nr), repK s (CP i)) {L : ℕ → ℕ} {j : ℕ} (hj : j < NC)
    (hL : L j < 512) :
    repK ((liftX hex L j : Cz) : K) (mulV (CP j) (QKt (L j))) ∧
      repK (piC (liftX hex L j)) (CP j) := by
  simp only [liftX, dif_pos hj]
  refine ⟨repK_czmul (recS_spec hex hj).2 (repK_qE hL), ?_⟩
  rw [map_mul, piC_qE, mul_one, piC_S0 (recS_spec hex hj).1.1]
  exact (recS_spec hex hj).2

theorem mem_Xs {er nr NC : ℕ} {CP : ℕ → ℕ} (her : er < 512) {x : ℕ → Cz}
    (hx : ∀ j < NC, repK (piC (x j)) (CP j) ∧ x j * cE er nr = cE er nr * x j)
    {u : Cz} (hu : u * cE er nr = cE er nr * u) (hc : ∃ i < NC, repK (piC u) (CP i)) :
    ∃ j < NC, ∃ e ∈ dlK QKt (mulV (SK nr) (QKt er)), u = x j * qE e := by
  have hr := repK_cE QK_eq her nr
  obtain ⟨j, hj, hrep⟩ := hc
  obtain ⟨hxπ, hxr⟩ := hx j hj
  have hπ : piC ((x j)⁻¹ * u) = 1 := by
    rw [map_mul, map_inv, repK_fun hxπ hrep, inv_mul_cancel]
  obtain ⟨e, he, -, -, hq⟩ := exists_qE ⟨(x j)⁻¹ * u, (piC_eq_one_iff _).1 hπ⟩
  have hq' : (qE e : Cz) = (x j)⁻¹ * u := congrArg Subtype.val hq
  refine ⟨j, hj, e, (mem_dlK hr).2 ⟨he, ?_⟩, by rw [hq', mul_inv_cancel_left]⟩
  rw [hq']
  have hxr' : (x j)⁻¹ * cE er nr = cE er nr * (x j)⁻¹ :=
    (show Commute (x j) (cE er nr) from hxr).inv_left.eq
  calc (x j)⁻¹ * u * cE er nr = (x j)⁻¹ * (cE er nr * u) := by rw [mul_assoc, hu]
    _ = (x j)⁻¹ * cE er nr * u := by rw [mul_assoc]
    _ = cE er nr * (x j)⁻¹ * u := by rw [hxr']
    _ = cE er nr * ((x j)⁻¹ * u) := by rw [mul_assoc]

theorem mem_Xg {er nr NC : ℕ} {CP : ℕ → ℕ} (her : er < 512)
    (hcent : {y | ∃ i < NC, repK y (CP i)} = centS0 (sElt nr)) {x : ℕ → Cz}
    (hx : ∀ j < NC, repK (piC (x j)) (CP j) ∧ x j * cE er nr = cE er nr * x j)
    {u : Cz} (hu : u * cE er nr = cE er nr * u) :
    ∃ j < NC, ∃ e ∈ dlK QKt (mulV (SK nr) (QKt er)), u = x j * qE e := by
  have hc : piC u ∈ centS0 (sElt nr) := by
    refine ⟨piC_mem u, ?_⟩
    have := congrArg piC hu
    rwa [map_mul, map_mul, piC_cE] at this
  rw [← hcent] at hc
  exact mem_Xs her hx hu hc

theorem mem_X {er nr NC : ℕ} {CP L : ℕ → ℕ} (her : er < 512)
    (hcent : {y | ∃ i < NC, repK y (CP i)} = centS0 (sElt nr))
    (hex : ∀ i < NC, ∃ s ∈ centS0 (sElt nr), repK s (CP i))
    (hL : ∀ j < NC, L j < 512 ∧ commK (mulV (CP j) (QKt (L j))) (mulV (SK nr) (QKt er)) = true)
    {u : Cz} (hu : u * cE er nr = cE er nr * u) :
    ∃ j < NC, ∃ e ∈ dlK QKt (mulV (SK nr) (QKt er)), u = liftX hex L j * qE e := by
  have hr := repK_cE QK_eq her nr
  refine mem_Xg her hcent (fun j hj => ⟨(liftX_spec hex hj (hL j hj).1).2, ?_⟩) hu
  have hx := (liftX_spec hex hj (hL j hj).1).1
  have h := (hL j hj).2
  unfold commK at h
  exact (cz_eq_iff (repK_czmul hx hr) (repK_czmul hr hx)).2 (Nat.eq_of_beq_eq_true h)

theorem liftX_comm {er nr NC : ℕ} {CP L : ℕ → ℕ} (her : er < 512)
    (hex : ∀ i < NC, ∃ s ∈ centS0 (sElt nr), repK s (CP i))
    (hL : ∀ j < NC, L j < 512 ∧ commK (mulV (CP j) (QKt (L j))) (mulV (SK nr) (QKt er)) = true)
    {j : ℕ} (hj : j < NC) : liftX hex L j * cE er nr = cE er nr * liftX hex L j := by
  have hr := repK_cE QK_eq her nr
  have hx := (liftX_spec hex hj (hL j hj).1).1
  have h := (hL j hj).2
  unfold commK at h
  exact (cz_eq_iff (repK_czmul hx hr) (repK_czmul hr hx)).2 (Nat.eq_of_beq_eq_true h)

theorem liftX_inj {NC nr : ℕ} {CP L : ℕ → ℕ}
    (hex : ∀ i < NC, ∃ s ∈ centS0 (sElt nr), repK s (CP i))
    (hinj : ∀ i < NC, ∀ j < NC, CP i = CP j → i = j) (hL : ∀ j < NC, L j < 512)
    {j j' e e' : ℕ} (hj : j < NC) (hj' : j' < NC)
    (h : liftX hex L j * qE e = liftX hex L j' * qE e') : j = j' ∧ (qE e : Cz) = qE e' := by
  have hπ := congrArg piC h
  rw [map_mul, map_mul, piC_qE, piC_qE, mul_one, mul_one] at hπ
  have h1 := (liftX_spec hex hj (hL j hj)).2
  rw [hπ] at h1
  have hjj := hinj j hj j' hj' (repK_unique h1 (liftX_spec hex hj' (hL j' hj')).2)
  subst hjj
  exact ⟨rfl, mul_left_cancel h⟩

end CC

end CertificateChecks.KernelCo2Census

end

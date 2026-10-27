module

public import CFSG.RankThree.GF2n.Smith81.OrthAct
public import CFSG.RankThree.GF2n.Stroth80.Sec34CaseB

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

theorem pi_conj_of_mem_Q {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) {p y : G} (hp : p ∈ Q) (hy : y ∈ Q) :
    M₀.π (p * y * p⁻¹) = M₀.π y := by
  have hc : ⁅p, y⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hp hy) (Q.inv_mem hp)) (Q.inv_mem hy)
  have e : p * y * p⁻¹ = ⁅p, y⁆ * y := by
    rw [commutatorElement_def]
    group
  rw [e, M₀.π_mul _ hc _ hy, (M₀.π_ker _ hc).mpr (M₀.comm_mem p hp y hy), zero_add]

variable [Finite G] {M Q Z C : Subgroup G}

theorem exists_normalizes_of_conj_le (hc : Ctx M Q Z C) {s : G} (hs : s ∈ M)
    (hsC : conjSubgroup s C ≤ C ⊔ Z) : ∃ p ∈ Q, conjSubgroup (p⁻¹ * s) C = C := by
  obtain ⟨p, hpQ, hp⟩ :=
    hc.exists_conj_of_le_ZB (hc.conj_of_mem hs) (by rw [sup_comm]; exact hsC)
  refine ⟨p, hpQ, ?_⟩
  rw [conjSubgroup_mul, ← hp, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]

theorem conj_mem_inf_QB_of_normalizes (hc : Ctx M Q Z C) {t : G} (ht : t ∈ M)
    (htC : conjSubgroup t C = C) {x : G} (hx : x ∈ Q ⊓ QB C) : t * x * t⁻¹ ∈ Q ⊓ QB C := by
  refine Subgroup.mem_inf.mpr ⟨(hc.conj_mem_Q_of_mem_M ht).1 x (Subgroup.mem_inf.mp hx).1, ?_⟩
  have h := QB_conj t C
  rw [htC] at h
  rw [h, mem_conjSubgroup]
  have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
  rw [e]
  exact (Subgroup.mem_inf.mp hx).2

theorem pi_conj_mem_img_inf_QB (hc : Ctx M Q Z C) {K : Type} [Field K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) {s : G} (hs : s ∈ M) (hsC : conjSubgroup s C ≤ C ⊔ Z)
    {x : G} (hx : x ∈ Q ⊓ QB C) : M₀.π (s * x * s⁻¹) ∈ M₀.img (Q ⊓ QB C) := by
  obtain ⟨p, hpQ, hpC⟩ := exists_normalizes_of_conj_le hc hs hsC
  have hpM : p ∈ M := hc.hyp.Q_normal.1 hpQ
  have htM : p⁻¹ * s ∈ M := M.mul_mem (M.inv_mem hpM) hs
  have hy := conj_mem_inf_QB_of_normalizes hc htM hpC hx
  have hyQ : p⁻¹ * s * x * (p⁻¹ * s)⁻¹ ∈ Q := (Subgroup.mem_inf.mp hy).1
  have e : s * x * s⁻¹ = p * (p⁻¹ * s * x * (p⁻¹ * s)⁻¹) * p⁻¹ := by group
  rw [e, pi_conj_of_mem_Q M₀ hpQ hyQ]
  exact M₀.pi_mem_img hy hyQ

theorem conj_le_sup_of_line (hc : Ctx M Q Z C) {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {c : M₀.E} (hline : IsLineGen M₀ C c) {s : G} (hs : s ∈ M)
    {T : M₀.E → M₀.E} (hT : ∀ x ∈ Q, M₀.π (s * x * s⁻¹) = T (M₀.π x))
    (hTc : ∀ a : K, ∃ b : K, T (a • c) = b • c) : conjSubgroup s C ≤ C ⊔ Z := by
  intro y hy
  rw [mem_conjSubgroup] at hy
  set c' := s⁻¹ * y * s with hc'
  have hc'Q : c' ∈ Q := hc.le hy
  have hyeq : y = s * c' * s⁻¹ := by rw [hc']; group
  have hyQ : y ∈ Q := by rw [hyeq]; exact (hc.conj_mem_Q_of_mem_M hs).1 c' hc'Q
  obtain ⟨a, ha⟩ := (hline _).mp (M₀.pi_mem_img hy hc'Q)
  obtain ⟨b, hb⟩ := hTc a
  have hZCZ : Z ≤ C ⊔ Z := le_sup_right
  have himg : M₀.π y ∈ M₀.img (C ⊔ Z) := by
    rw [hyeq, hT c' hc'Q, ha, hb]
    exact M₀.img_mono le_sup_left ((hline _).mpr ⟨b, rfl⟩)
  exact (M₀.mem_img_iff hZCZ hyQ).mp himg

theorem orthTensor_mem_img_inf_QB (hc : Ctx M Q Z C) {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)} {s : G} (hs : s ∈ M) (hsC : conjSubgroup s C ≤ C ⊔ Z)
    {g : Matrix (Fin 2) (Fin 2) K} {o : (ι → K) → (ι → K)}
    (hact : ActsAsTensor Q Z M₀ φ s g o) {e : M₀.E} (he : e ∈ M₀.img (Q ⊓ QB C)) :
    φ.symm (orthTensor g o (φ e)) ∈ M₀.img (Q ⊓ QB C) := by
  obtain ⟨x, hx, hxQ, rfl⟩ := he
  rw [← hact x hxQ, LinearEquiv.symm_apply_apply]
  exact pi_conj_mem_img_inf_QB hc M₀ hs hsC hx

end CFSG.RankThree.GF2n.Smith81

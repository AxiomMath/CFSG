module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Fuse

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {M Q Z B X : Subgroup G} {x : G}

private def alphaCommHom (hc : Ctx M Q Z B) {t α : G} (htM : t ∈ M) (hαQ : α ∈ Q) :
    ↥(Q1 hc t) →* ↥Z where
  toFun h := ⟨⁅(h : G), α⁆, comm_mem_Z hc.hyp ((hc.mem_Q1_iff htM).mp h.2).1 hαQ⟩
  map_one' := Subtype.ext (by simp [commutatorElement_def])
  map_mul' h₁ h₂ := by
    refine Subtype.ext ?_
    have h₁Q : (h₁ : G) ∈ Q := ((hc.mem_Q1_iff htM).mp h₁.2).1
    have h₁Z : ⁅(h₁ : G), α⁆ ∈ Z := comm_mem_Z hc.hyp h₁Q hαQ
    have h₂Z : ⁅(h₂ : G), α⁆ ∈ Z :=
      comm_mem_Z hc.hyp ((hc.mem_Q1_iff htM).mp h₂.2).1 hαQ
    have hconj : (h₁ : G) * ⁅(h₂ : G), α⁆ * (h₁ : G)⁻¹ = ⁅(h₂ : G), α⁆ := by
      rw [← Z_central hc.hyp h₂Z h₁Q]
      group
    have e : ⁅((h₁ : G) * h₂), α⁆ = ⁅(h₂ : G), α⁆ * ⁅(h₁ : G), α⁆ := by
      rw [show ⁅((h₁ : G) * h₂), α⁆ =
        (h₁ : G) * ⁅(h₂ : G), α⁆ * (h₁ : G)⁻¹ * ⁅(h₁ : G), α⁆ by
        simp only [commutatorElement_def]; group, hconj]
    show ⁅((h₁ : G) * h₂), α⁆ = ⁅(h₁ : G), α⁆ * ⁅(h₂ : G), α⁆
    rw [e, Z_central hc.hyp h₂Z (hc.hyp.Z_normal.1 h₁Z)]

private theorem alphaCommHom_surjective (hc : Ctx M Q Z B) (hs : Sit M Q Z X x)
    {α : G} (hαQ : α ∈ Q) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (R : Tim79.GammaReg Q Z γ) (A : XAct M₀ x) {f : M₀.E}
    (hf : A.T f = f) (hfB : M₀.B f (M₀.π α) ≠ 0) :
    Function.Surjective (alphaCommHom hc (t := x) (α := α) hs.memM hαQ) := by
  intro z'
  obtain ⟨h, hhQ, hπh⟩ := M₀.π_surj ((γ z' / M₀.B f (M₀.π α)) • f)
  have hQ1 : h ∈ Q1 hc x := by
    refine (hc.mem_Q1_iff hs.memM).mpr ⟨hhQ, ?_⟩
    refine (comm_mem_iff_fix (t := x) (T := A.T)
      (fun y hy => (Subgroup.mem_normalizer_iff.mp (hs.hyp.Q_normal.2 hs.memM) y).mp hy)
      A.hπ (x := h) hhQ).mpr ?_
    rw [hπh, map_smul, hf]
  have hγ : γ ⁅h, α⁆ = γ z' := by
    rw [M₀.comm_eq h hhQ α hαQ, hπh, map_smul, LinearMap.smul_apply, smul_eq_mul,
      div_mul_cancel₀ _ hfB]
  refine ⟨⟨h, hQ1⟩, Subtype.ext ?_⟩
  exact R.eq_of_γ_eq (comm_mem_Z hs.hyp hhQ hαQ) z'.2 hγ

private theorem mem_Ut_of_eq_sub_one (hs : Sit M Q Z X x)
    {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (A : XAct M₀ x)
    {α : G} (hαQ : α ∈ Q) {f : M₀.E}
    (hf : (A.T : M₀.E →ₗ[K] M₀.E) f - f = M₀.π α) : α ∈ Ut Q Z x := by
  obtain ⟨q, hq, hπq⟩ := M₀.π_surj f
  have hxqQ : x * q * x⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hs.hyp.Q_normal.2 hs.memM) q).mp hq
  have hπd : M₀.π (x * q * x⁻¹ * q⁻¹) = M₀.π α := by
    rw [M₀.π_mul (x * q * x⁻¹) hxqQ q⁻¹ (Q.inv_mem hq), A.hπ q hq,
      Tim79.QuadModel.pi_inv M₀ hq, hπq]
    simpa [sub_eq_add_neg] using hf
  have hz : α⁻¹ * (x * q * x⁻¹ * q⁻¹) ∈ Z := by
    refine (M₀.π_ker _ (Q.mul_mem (Q.inv_mem hαQ) (Q.mul_mem hxqQ (Q.inv_mem hq)))).mp ?_
    rw [M₀.π_mul (α⁻¹) (Q.inv_mem hαQ) (x * q * x⁻¹ * q⁻¹)
      (Q.mul_mem hxqQ (Q.inv_mem hq)), Tim79.QuadModel.pi_inv M₀ hαQ, hπd]
    exact neg_add_cancel _
  have hcomm : (x * q * x⁻¹ * q⁻¹) ∈ ⁅Q, Subgroup.zpowers x⁆ := by
    have h := Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers x)
    have e : (x * q * x⁻¹ * q⁻¹) = ⁅q, x⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (⁅Q, Subgroup.zpowers x⁆).inv_mem h
  have hαd : α = (x * q * x⁻¹ * q⁻¹) * (α⁻¹ * (x * q * x⁻¹ * q⁻¹))⁻¹ := by group
  rw [hαd]
  simpa [Ut] using Subgroup.mul_mem_sup hcomm (Z.inv_mem hz)

private theorem alphaCommHom_surjective_of_not_mem_Ut (hc : Ctx M Q Z B) (hs : Sit M Q Z X x)
    {α : G} (hα : α ∈ Q ⊓ QB X) (hαU : α ∉ Ut Q Z x) :
    Function.Surjective (alphaCommHom hc (t := x) (α := α) hs.memM hα.1) := by
  classical
  obtain ⟨K, _, _, γ, M₀, hD, -, -, ⟨A⟩⟩ :=
    exists_model hs.hyp hs.memM (hs.x_cent (smith_1_12 hs))
  let N : M₀.E →ₗ[K] M₀.E := (A.T : M₀.E →ₗ[K] M₀.E) - 1
  have hrange_eq : LinearMap.range N = M₀.B.orthogonal (LinearMap.ker N) :=
    range_sub_one_eq_orthogonal_ker M₀.B (modelB_nondegenerate M₀)
      (fun e f h => by rw [Tim79.QuadModel.B_comm, h, neg_zero])
      (A.T : M₀.E →ₗ[K] M₀.E) A.hB (fun e => A.T_T hs.hyp hs.memM hs.x_sq e)
  have hnotrange : M₀.π α ∉ LinearMap.range N := by
    rintro ⟨f, hf⟩
    exact hαU (mem_Ut_of_eq_sub_one hs A hα.1 (by simpa [N] using hf))
  obtain ⟨f, hfker, hfB⟩ : ∃ f, f ∈ LinearMap.ker N ∧ M₀.B f (M₀.π α) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hnotrange (by
      rw [hrange_eq]
      exact LinearMap.BilinForm.mem_orthogonal_iff.mpr hcon)
  have hf : A.T f = f := by
    have h0 : N f = 0 := LinearMap.mem_ker.mp hfker
    exact sub_eq_zero.mp (by simpa [N] using h0)
  exact alphaCommHom_surjective hc hs hα.1 hD.reg A hf hfB

private theorem ker_alphaCommHom_le (hc : Ctx M Q Z B) (hs : Sit M Q Z X x) {α : G}
    (hα : α ∈ Q ⊓ QB X) (hαU : α ∉ Ut Q Z x) :
    (alphaCommHom hc (t := x) (α := α) hs.memM hα.1).ker ≤
      (Ctx.commQ1Hom hc (t := x) hs.memM).ker := by
  set φ := alphaCommHom hc (t := x) (α := α) hs.memM hα.1
  set θ := Ctx.commQ1Hom hc (t := x) hs.memM
  have hle : θ.ker ≤ φ.ker := by
    intro u hu
    have hu_cent : (u : G) ∈ Q ⊓ Subgroup.centralizer ({x} : Set G) := by
      rw [Ctx.ker_commQ1Hom hc (t := x) hs.memM, Subgroup.mem_subgroupOf] at hu
      exact hu
    have hαu : α * (u : G) = (u : G) * α := (smith_1_13 hs).2.2.2.2 α hα (u : G) hu_cent
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr hαu.symm)
  have hφ : φ.ker.index = Nat.card Z := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr
      (alphaCommHom_surjective_of_not_mem_Ut hc hs hα hαU), Subgroup.card_top]
  have hθ : θ.ker.index ≤ Nat.card Z := by
    rw [Subgroup.index_ker]
    exact Nat.card_le_card_of_injective (fun y => (y.1 : ↥Z)) (fun a b h => Subtype.ext h)
  have hcard : Nat.card φ.ker ≤ Nat.card θ.ker := by
    have e1 := Subgroup.card_mul_index φ.ker
    have e2 := Subgroup.card_mul_index θ.ker
    rw [hφ] at e1
    have h3 : Nat.card φ.ker * Nat.card Z ≤ Nat.card θ.ker * Nat.card Z :=
      e1.trans_le (e2.symm.trans_le (Nat.mul_le_mul_left _ hθ))
    exact Nat.le_of_mul_le_mul_right h3 Nat.card_pos
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).ge

theorem Ctx.mul_comm_ne_of_not_mem_Ut (hc : Ctx M Q Z B) {Y : Subgroup G} {w : G}
    (hs : Sit M Q Z Y w) {α : G} (hα : α ∈ Q ⊓ QB Y) (hαU : α ∉ Ut Q Z w) {h : G}
    (hh : h ∈ Q) (hhw : ⁅h, w⁆ ∈ Z) (hhw1 : ⁅h, w⁆ ≠ 1) : h * α ≠ α * h := by
  intro hcomm
  have hwh : ⁅w, h⁆ ∈ Z := by rw [← commutatorElement_inv]; exact Z.inv_mem hhw
  have hQ1 : h ∈ Q1 hc w := (hc.mem_Q1_iff hs.memM).mpr ⟨hh, hwh⟩
  have hker : (⟨h, hQ1⟩ : ↥(Q1 hc w)) ∈ (alphaCommHom hc hs.memM hα.1).ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr hcomm)
  have h1 := ker_alphaCommHom_le hc hs hα hαU hker
  rw [Ctx.ker_commQ1Hom, Subgroup.mem_subgroupOf] at h1
  exact hhw1 (commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp h1.2))

end CFSG.RankThree.GF2n.Stroth80

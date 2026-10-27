module

public import CFSG.RankThree.GF2n.Stroth80.Sec33Action
public import CFSG.RankThree.GF2n.Stroth80.DictA2

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def A0 (Q Z B : Subgroup G) : Subgroup G where
  carrier := {a | a ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) ∧ ∀ r ∈ Q ⊓ QB B, ⁅a, r⁆ ∈ Z}
  mul_mem' := by
    rintro a b ⟨ha, haA⟩ ⟨hb, hbA⟩
    refine ⟨(QB B ⊓ Subgroup.centralizer (Z : Set G)).mul_mem ha hb, fun r hr => ?_⟩
    have h2 : a * ⁅b, r⁆ * a⁻¹ = ⁅b, r⁆ := by
      have := Subgroup.mem_centralizer_iff.mp ha.2 _ (hbA r hr)
      rw [← this]; group
    have h1 : ⁅a * b, r⁆ = a * ⁅b, r⁆ * a⁻¹ * ⁅a, r⁆ := by
      simp only [commutatorElement_def]; group
    rw [h1, h2]
    exact Z.mul_mem (hbA r hr) (haA r hr)
  one_mem' := ⟨(QB B ⊓ Subgroup.centralizer (Z : Set G)).one_mem, fun r _ => by
    simp only [commutatorElement_def]; group; exact Z.one_mem⟩
  inv_mem' := by
    rintro a ⟨ha, haA⟩
    refine ⟨(QB B ⊓ Subgroup.centralizer (Z : Set G)).inv_mem ha, fun r hr => ?_⟩
    have h1 : ⁅a⁻¹, r⁆ = a⁻¹ * ⁅a, r⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    have h2 : a⁻¹ * ⁅a, r⁆⁻¹ * a = ⁅a, r⁆⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp ha.2 _ (Z.inv_mem (haA r hr))
      have h3 : a⁻¹ * ⁅a, r⁆⁻¹ = ⁅a, r⁆⁻¹ * a⁻¹ :=
        calc a⁻¹ * ⁅a, r⁆⁻¹ = a⁻¹ * (⁅a, r⁆⁻¹ * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * ⁅a, r⁆⁻¹) * a⁻¹ := by rw [this]
          _ = ⁅a, r⁆⁻¹ * a⁻¹ := by group
      rw [h3]; group
    rw [h1, h2]
    exact Z.inv_mem (haA r hr)

theorem mem_A0 {Q Z B : Subgroup G} {a : G} :
    a ∈ A0 Q Z B ↔ a ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) ∧ ∀ r ∈ Q ⊓ QB B, ⁅a, r⁆ ∈ Z :=
  Iff.rfl

variable [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.act_sub_perp (hc : Ctx M Q Z B) {a : G}
    (ha : a ∈ QB B ⊓ Subgroup.centralizer (Z : Set G)) (haA : ∀ r ∈ Q ⊓ QB B, ⁅a, r⁆ ∈ Z)
    {b : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    {T : M₀.E → M₀.E} (hT : ∀ y ∈ Q, M₀.π (a * y * a⁻¹) = T (M₀.π y)) :
    ∀ v : M₀.E, M₀.B v b = 0 → ∃ c : K, T v = v + c • b := by
  intro v hv
  obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj v
  have hyC : y ∈ Q ⊓ Subgroup.centralizer (B : Set G) := ⟨hyQ, (hcent y hyQ).mpr hv⟩
  have h1 := hc.comm_mem_Z_sup_B ha haA hyC
  have hnorm : a * y * a⁻¹ ∈ Q := hc.L0_normalizes_Q ha y hyQ
  have hπ : M₀.π ⁅a, y⁆ = T (M₀.π y) - M₀.π y := by
    rw [show ⁅a, y⁆ = (a * y * a⁻¹) * y⁻¹ by rw [commutatorElement_def],
      M₀.π_mul _ hnorm _ (Q.inv_mem hyQ), hT y hyQ,
      Tim79.QuadModel.pi_inv M₀ hyQ, sub_eq_add_neg]
  have hQ1 : ⁅a, y⁆ ∈ Q := by
    rw [commutatorElement_def]; exact Q.mul_mem hnorm (Q.inv_mem hyQ)
  have h2 : M₀.π ⁅a, y⁆ ∈ M₀.img B := by
    have hle : Z ⊔ B ≤ M₀.lift (M₀.img B) := sup_le
      (fun z hz => ⟨hc.Z_le_Q hz, by
        rw [(M₀.π_ker z (hc.Z_le_Q hz)).mpr hz]; exact AddSubgroup.zero_mem _⟩)
      (fun b' hb' => ⟨hc.le hb', M₀.pi_mem_img hb' (hc.le hb')⟩)
    exact (hle h1).2
  obtain ⟨c, hc'⟩ := (hB _).mp h2
  refine ⟨c, ?_⟩
  rw [hπ] at hc'
  rw [show T (M₀.π y) = (T (M₀.π y) - M₀.π y) + M₀.π y by abel, hc']
  exact add_comm _ _

theorem Ctx.isA2_of_qf_zero (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) [Finite K]
    {a : G} (ha : a ∈ QB B ⊓ Subgroup.centralizer (Z : Set G)) (haQ : a ∉ Q)
    {b : M₀.E} (hb0 : b ≠ 0) (hbs : M₀.Qf b = 0) (T : M₀.E ≃ₗ[K] M₀.E)
    (hTπ : ∀ x ∈ Q, M₀.π (a * x * a⁻¹) = T (M₀.π x)) (hTQ : ∀ e, M₀.Qf (T e) = M₀.Qf e)
    (hr : ∀ v : M₀.E, M₀.B v b = 0 → ∃ c : K, T v = v + c • b)
    (hQf : ∀ w ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1), M₀.Qf w = 0) : IsA2 Q Z a := by
  obtain ⟨g, hg⟩ := hc.conj
  have hK : 1 < Nat.card K := by
    rw [h.card]
    have := hc.hyp.q4
    omega
  have haM : a ∈ M := by rw [← hc.QB_inf_M_eq] at ha; exact ha.2
  have haN : a ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 haM
  have hnorm : ∀ y ∈ Q, a * y * a⁻¹ ∈ Q := fun y hy => (Subgroup.mem_normalizer_iff.mp haN y).mp hy
  have hnorm' : ∀ y ∈ Q, a⁻¹ * y * a ∈ Q := fun y hy => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) y).mp hy
    simpa using this
  have hTne : ∃ e, (T : M₀.E →ₗ[K] M₀.E) e ≠ e := by
    by_contra hcon
    push Not at hcon
    exact haQ (hc.hyp.centralizer_Qt a haM fun y hy =>
      (M₀.comm_mem_iff hy (hnorm y hy)).mpr (by rw [hTπ y hy]; exact hcon _))
  have hfin2 := Tim79.QuadModel.finrank_range_eq_two (M₀ := M₀)
    (T := (T : M₀.E →ₗ[K] M₀.E)) hTQ hb0 hbs hr hTne
  have ha2 : a ^ 2 ∈ Q := by
    have hlg : a ∈ conjSubgroup g Q := (Ctx.QB_eq hc hg).2 ▸ ha.1
    exact hc.le (hg ▸ hc.hyp.toHyp79.sq_mem_conj g hlg)
  exact (isA2_iff M₀ h.reg h.card hK (T := T) hnorm hnorm' hTπ).mpr ⟨haQ, ha2, hfin2, hQf⟩

theorem Ctx.isA2_of_A0_qf (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) [Finite K]
    {a : G} (ha : a ∈ A0 Q Z B) (haQ : a ∉ Q) {b : M₀.E} (hb0 : b ≠ 0) (hbs : M₀.Qf b = 0)
    (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    (T : M₀.E ≃ₗ[K] M₀.E) (hTπ : ∀ x ∈ Q, M₀.π (a * x * a⁻¹) = T (M₀.π x))
    (hTQ : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hTb : T b = b) {f₀ : M₀.E} (hf₀ : M₀.B b f₀ = 1)
    (hqv : M₀.Qf (T f₀ - f₀) = 0) : IsA2 Q Z a := by
  have hr : ∀ w : M₀.E, M₀.B w b = 0 → ∃ c : K, T w = w + c • b :=
    hc.act_sub_perp ha.1 ha.2 hB hcent hTπ
  have hvb : M₀.B (T f₀ - f₀) b = 0 := by
    have := Tim79.QuadModel.B_iso (M₀ := M₀) (T := (T : M₀.E →ₗ[K] M₀.E)) hTQ f₀ b
    rw [show (T : M₀.E →ₗ[K] M₀.E) b = b from hTb] at this
    rw [map_sub, LinearMap.sub_apply]
    exact sub_eq_zero.mpr this
  have hbv : M₀.B b (T f₀ - f₀) = 0 := by
    rw [Tim79.QuadModel.B_comm, hvb, neg_zero]
  have hQf : ∀ w ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1), M₀.Qf w = 0 := by
    rintro _ ⟨e, rfl⟩
    have hbf' : M₀.B f₀ b = -1 := by rw [Tim79.QuadModel.B_comm, hf₀]
    obtain ⟨l, hl⟩ : ∃ l : K, l = M₀.B e b := ⟨_, rfl⟩
    have he' : M₀.B (e + l • f₀) b = 0 := by
      rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hbf', hl]
      ring
    obtain ⟨c, hc'⟩ := hr _ he'
    have hTe : T e = (e + l • f₀) + c • b - l • T f₀ := by
      have h1 : e = (e + l • f₀) - l • f₀ := by abel
      conv_lhs => rw [h1]
      rw [map_sub, map_smul, hc']
    have hrange : ((T : M₀.E →ₗ[K] M₀.E) - 1) e = c • b + (-l) • (T f₀ - f₀) := by
      simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe]
      rw [hTe]
      module
    have hB' : M₀.B (c • b) ((-l) • (T f₀ - f₀)) = 0 := by
      simp [map_smul, LinearMap.smul_apply, hbv]
    rw [hrange, M₀.Qf_add, M₀.Qf_smul, M₀.Qf_smul, hbs, hqv, hB']
    simp
  exact hc.isA2_of_qf_zero h ha.1 haQ hb0 hbs T hTπ hTQ hr hQf

end CFSG.RankThree.GF2n.Stroth80

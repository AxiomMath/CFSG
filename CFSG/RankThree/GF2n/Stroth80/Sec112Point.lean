module

public import CFSG.RankThree.GF2n.Stroth80.Sec111Order

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

omit [Finite K] in
private lemma pi_commutator_eq (hc : Ctx M Q Z B)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    {l : G} (hl : l ∈ LB M Q B) {x₀ : G} (hx₀ : x₀ ∈ Q) :
    M₀.π ⁅l, x₀⁆ = φ ⟨l, hc.LB_le_H0 hl⟩ (M₀.π x₀) - M₀.π x₀ := by
  have hxQ : l * x₀ * l⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M (hc.LB_le_M hl)).1 x₀ hx₀
  have e : ⁅l, x₀⁆ = (l * x₀ * l⁻¹) * x₀⁻¹ := commutatorElement_def l x₀
  rw [e, M₀.π_mul _ hxQ _ (Q.inv_mem hx₀), M₀.pi_inv hx₀,
    hφπ ⟨l, hc.LB_le_H0 hl⟩ x₀ hx₀, sub_eq_add_neg]

private lemma commutator_mem_Z_of_mem_W (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    {b : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    {W : Submodule K M₀.E} (hWst : ∀ g : ↥(H0 M Z), ∀ w ∈ W, φ g w ∈ W) (hbW : b ∉ W)
    {d : G} (hd : d ∈ Q ⊓ QB B) (hdW : M₀.π d ∈ W) :
    ∀ r ∈ LB M Q B, ⁅r, d⁆ ∈ Z := by
  intro r hr
  have hrH : r ∈ H0 M Z := hc.LB_le_H0 hr
  have hT : ∀ y ∈ Q,
      M₀.π (r * y * r⁻¹) = (φ ⟨r, hrH⟩ : M₀.E →ₗ[K] M₀.E) (M₀.π y) :=
    fun y hy => hφπ ⟨r, hrH⟩ y hy
  obtain ⟨-, hline⟩ := hc.LB_act_fix_line h hB hr hT
  obtain ⟨c, hc_eq⟩ := hline (M₀.π d) (M₀.pi_mem_img hd hd.1)
  have hcW : c • b ∈ W := by
    rw [← hc_eq]
    exact W.sub_mem (hWst ⟨r, hrH⟩ _ hdW) hdW
  have hc0 : c = 0 := by
    by_contra hcne
    exact hbW ((W.smul_mem_iff hcne).mp hcW)
  have hfix : (φ ⟨r, hrH⟩ : M₀.E →ₗ[K] M₀.E) (M₀.π d) = M₀.π d := by
    have hzero : (φ ⟨r, hrH⟩ : M₀.E →ₗ[K] M₀.E) (M₀.π d) - M₀.π d = 0 := by
      rw [hc_eq, hc0, zero_smul]
    exact sub_eq_zero.mp hzero
  have hQ' : r * d * r⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M (hc.LB_le_M hr)).1 d hd.1
  have hπ : M₀.π (r * d * r⁻¹) = M₀.π d := by
    rw [hT d hd.1, hfix]
  exact (M₀.comm_mem_iff hd.1 hQ').mpr hπ

omit [Finite K] in
private lemma pi_mem_img_B_of_mem_sup (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    {d : G} (hd : d ∈ Z ⊔ B) : M₀.π d ∈ M₀.img B := by
  have hle : (Z ⊔ B : Subgroup G) ≤ M₀.lift (M₀.img B) := by
    rw [sup_comm]
    exact stroth_sup_le_lift h hc.le
  exact ((M₀.mem_lift (R := M₀.img B)).mp (hle hd)).2

theorem Ctx.LB_fixes_of_perp (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    {b : M₀.E} (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    {W : Submodule K M₀.E} (hWst : ∀ g : ↥(H0 M Z), ∀ w ∈ W, φ g w ∈ W) (hbW : b ∉ W)
    {l : G} (hl : l ∈ LB M Q B) {x : M₀.E} (hxW : x ∈ W) (hxb : M₀.B x b = 0) :
    φ ⟨l, hc.LB_le_H0 hl⟩ x = x := by
  obtain ⟨x₀, hx₀Q, rfl⟩ := M₀.π_surj x
  let d : G := ⁅l, x₀⁆
  have hx₀C : x₀ ∈ Subgroup.centralizer (B : Set G) := (hcent x₀ hx₀Q).mpr hxb
  have hd : d ∈ Q ⊓ QB B := hc.comm_mem_inf_of_mem_LB hl ⟨hx₀Q, hx₀C⟩
  have hπd : M₀.π d = φ ⟨l, hc.LB_le_H0 hl⟩ (M₀.π x₀) - M₀.π x₀ :=
    pi_commutator_eq hc hφπ hl hx₀Q
  have hπdW : M₀.π d ∈ W := by
    rw [hπd]
    exact W.sub_mem (hWst ⟨l, hc.LB_le_H0 hl⟩ _ hxW) hxW
  have hcomm : ∀ r ∈ LB M Q B, ⁅r, d⁆ ∈ Z :=
    commutator_mem_Z_of_mem_W hc h hφπ hB hWst hbW hd hπdW
  have hdB : M₀.π d ∈ M₀.img B :=
    pi_mem_img_B_of_mem_sup hc h (hc.mem_sup_of_comm_LB hd hcomm)
  obtain ⟨s, hs⟩ := (hB (M₀.π d)).mp hdB
  have hs0 : s = 0 := by
    by_contra hsne
    exact hbW ((W.smul_mem_iff hsne).mp (hs ▸ hπdW))
  have hπd0 : M₀.π d = 0 := by rw [hs, hs0, zero_smul]
  have hmain : φ ⟨l, hc.LB_le_H0 hl⟩ (M₀.π x₀) - M₀.π x₀ = 0 := by
    rw [← hπd, hπd0]
  exact sub_eq_zero.mp hmain

end CFSG.RankThree.GF2n.Stroth80

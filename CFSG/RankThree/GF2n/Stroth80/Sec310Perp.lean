module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Spure
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5SL

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.exists_submodule_inf_QB (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hcard : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1))
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (h : GlobalModelData M Q Z γ M₀) :
    ∃ W : Submodule K M₀.E, ∀ v, v ∈ W ↔ v ∈ M₀.img (Q ⊓ QB B) := by
  have hXQ : Q ⊓ QB B ≤ Q := inf_le_left
  have hZX : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have hUs : ∀ e ∈ M₀.img (Q ⊓ QB B), M₀.Qf e = 0 :=
    (M₀.isElemAbelian_iff h.reg hXQ).mp hc.inf_QB_elemAbelian
  have hcardX : Nat.card ↥(Q ⊓ QB B) = Nat.card Z * Nat.card (M₀.img (Q ⊓ QB B)) :=
    M₀.card_eq hXQ hZX
  have hKZ : Nat.card K = Nat.card Z := h.card
  have hcardU : Nat.card (M₀.img (Q ⊓ QB B)) = Nat.card K ^ n := by
    rw [hKZ]
    have h1 : Nat.card Z * Nat.card (M₀.img (Q ⊓ QB B)) = Nat.card Z * Nat.card Z ^ n := by
      rw [← hcardX, hcard, pow_succ, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hK : 1 < Nat.card K := by
    rw [hKZ]
    have := hc.hyp.q4
    omega
  have hdimE := h.finrank_E hw hK
  obtain ⟨W, hWU, -⟩ := exists_submodule_of_card_eq M₀ hdimE hUs hcardU
  exact ⟨W, hWU⟩

theorem stroth310Perp_of_34 (h34 : Stroth34Statement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec5Hyp hc n t → ¬ Vt M (LB M Q B) B Z t ≤ QB B →
        ∀ v ∈ Vt M (LB M Q B) B Z t,
          (v ∈ QB B ↔ ∀ b ∈ B, ∀ y ∈ Q, ⁅y, t⁆ * v⁻¹ ∈ Z → ⁅b, y⁆ = 1) := by
  classical
  intro G _ _ M Q Z B hc n t hs hnot v hv
  have h35all := stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen
  have h35 := h35all.2.1
  have hcard := h35all.2.2.2
  obtain ⟨hVU, -⟩ := hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB h35 hs.mem hs.notQ hnot
  have hchi := hc.isChiIso_Q1_Ut hs.mem
  have htM : t ∈ M := hc.LB_le_M hs.mem
  have htH : t ∈ H0 M Z := hc.LB_le_H0 hs.mem
  have hVQ : ∀ x ∈ Vt M (LB M Q B) B Z t, x ∈ Q := fun x hx => hc.Vt_le_Q t hx
  have hrep : ∀ u ∈ Vt M (LB M Q B) B Z t, ∃ x ∈ Q, ⁅x, t⁆ * u⁻¹ ∈ Z := fun u hu =>
    hchi.2.1 u (hVU ▸ hu)
  have hZQB : Z ≤ QB B := hc.Z_le_QB.1
  have hcomm : ∀ x ∈ Q ⊓ Subgroup.centralizer (B : Set G), ⁅x, t⁆ ∈ Q ⊓ QB B := fun x hx => by
    have := hc.comm_mem_inf_of_mem_LB hs.mem hx
    rw [← commutatorElement_inv]
    exact (Q ⊓ QB B).inv_mem this
  constructor
  ·
    intro hvB b hb y hyQ hy
    obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
    obtain ⟨φ, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hc.hyp h
    obtain ⟨b₀, hb0, hbs, hB, hcent, -⟩ := hc.dictB h
    obtain ⟨UB, hUB⟩ := hc.exists_submodule_inf_QB hs.width hcard h
    have hQnorm : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 htM) x).mp hx
    have hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = φ ⟨t, htH⟩ (M₀.π x) := fun x hx =>
      hφπ ⟨t, htH⟩ x hx
    have hπc : ∀ x ∈ Q, M₀.π ⁅x, t⁆ = M₀.π x - φ ⟨t, htH⟩ (M₀.π x) := fun x hx =>
      pi_comm_eq_sub (T := φ ⟨t, htH⟩) hQnorm hTπ hx
    have hπrep : ∀ x ∈ Q, ∀ w ∈ Q, ⁅x, t⁆ * w⁻¹ ∈ Z →
        M₀.π w = M₀.π x - φ ⟨t, htH⟩ (M₀.π x) := by
      intro x hx w hw hz
      have hcQ : ⁅x, t⁆ ∈ Q := hc.comm_mem_Q htM hx
      have h0 := (M₀.π_ker _ (Q.mul_mem hcQ (Q.inv_mem hw))).mpr hz
      rw [M₀.π_mul _ hcQ _ (Q.inv_mem hw), M₀.pi_inv hw, hπc x hx] at h0
      exact (sub_eq_zero.mp (by rw [← h0]; abel)).symm
    have hyC : y ∈ Subgroup.centralizer (B : Set G) := by
      rw [hcent y hyQ]
      by_contra hc0
      obtain ⟨u₀, hu₀V, hu₀B⟩ := SetLike.not_le_iff_exists.mp hnot
      obtain ⟨x₀, hx₀Q, hx₀⟩ := hrep u₀ hu₀V
      have hu₀Q : u₀ ∈ Q := hVQ u₀ hu₀V
      have hπu₀ := hπrep x₀ hx₀Q u₀ hu₀Q hx₀
      set c : GaloisField 2 n' := M₀.B (M₀.π x₀) b₀ / M₀.B (M₀.π y) b₀ with hcdef
      obtain ⟨x₁, hx₁Q, hx₁π⟩ := M₀.π_surj (M₀.π x₀ - c • M₀.π y)
      have hx₁C : x₁ ∈ Subgroup.centralizer (B : Set G) := by
        rw [hcent x₁ hx₁Q, hx₁π, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
          smul_eq_mul, hcdef, div_mul_cancel₀ _ hc0, sub_self]
      have hw₁ : ⁅x₁, t⁆ ∈ Q ⊓ QB B := hcomm x₁ ⟨hx₁Q, hx₁C⟩
      have hπv : M₀.π v = M₀.π y - φ ⟨t, htH⟩ (M₀.π y) :=
        hπrep y hyQ v (hVQ v hv) hy
      have hπw₁ : M₀.π ⁅x₁, t⁆ = M₀.π x₁ - φ ⟨t, htH⟩ (M₀.π x₁) := hπc x₁ hx₁Q
      have hu₀eq : M₀.π u₀ = M₀.π ⁅x₁, t⁆ + c • M₀.π v := by
        rw [hπu₀, hπw₁, hπv, hx₁π, map_sub, map_smul]
        module
      have hmem : M₀.π u₀ ∈ UB := by
        rw [hu₀eq]
        refine UB.add_mem ((hUB _).mpr (M₀.pi_mem_img hw₁ hw₁.1)) (UB.smul_mem _ ?_)
        exact (hUB _).mpr (M₀.pi_mem_img ⟨hVQ v hv, hvB⟩ (hVQ v hv))
      have hu₀X : u₀ ∈ Q ⊓ QB B :=
        (M₀.mem_img_iff (le_inf hc.Z_le_Q hZQB) hu₀Q).mp ((hUB _).mp hmem)
      exact hu₀B hu₀X.2
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hyC b hb)
  ·
    intro hP
    obtain ⟨y₀, hy₀Q, hy₀⟩ := hrep v hv
    have hy₀C : y₀ ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have := hP b hb y₀ hy₀Q hy₀
      exact commutatorElement_eq_one_iff_mul_comm.mp this
    have h1 := hcomm y₀ ⟨hy₀Q, hy₀C⟩
    have h2 : v = (⁅y₀, t⁆ * v⁻¹)⁻¹ * ⁅y₀, t⁆ := by group
    rw [h2]
    exact (QB B).mul_mem ((QB B).inv_mem (hZQB hy₀)) h1.2

end CFSG.RankThree.GF2n.Stroth80

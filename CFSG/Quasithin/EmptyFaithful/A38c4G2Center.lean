module

public import CFSG.Quasithin.Background.JonesParshallG2Torus
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Eq
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Two
public import CFSG.Quasithin.Background.JonesParshallG2Perfect

public section

namespace CFSG.Quasithin.A318Excl

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall Matrix
open CFSG.QuasithinUnique.Bridge.Alt57Model

theorem center_cayleyGroup_eq_bot {K : Type} [Field K] [CharP K 2] {c : K} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) : Subgroup.center ↥(cayleyGroup K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hcomm : ∀ (g : ↥(cayleyGroup K)) (x : quasithinZorn K),
      cgE g (cgE z x) = cgE z (cgE g x) := by
    intro g x
    have h := Subgroup.mem_center_iff.mp hz g
    exact congrArg (fun w : ↥(cayleyGroup K) => cgE w x) h
  have hc' : c⁻¹ ≠ 1 := fun h => hc1 (inv_eq_one.mp h)
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hD : (1 : K) * c * c⁻¹ = 1 := by rw [one_mul, mul_inv_cancel₀ hc0]
  set Dg : ↥(cayleyGroup K) := g2A (diag3 1 c c⁻¹ hD) with hDg
  set Yg : ↥(cayleyGroup K) := g2Y ![0, 1, 0] with hYg
  have hDp : cgE Dg (zU0 K) = zU0 K := by
    rw [zU0]
    change gAFun _ _ = _
    rw [gAFun_diag3]
    apply zmk_congr <;> simp
  have hYp : cgE Yg (zU0 K) = zU0 K := by
    rw [zU0]
    change ybFun _ _ = _
    rw [ybFun_zmk]
    apply zmk_congr <;> simp
  have hDy : cgE Dg (cgE z (zU0 K)) = cgE z (zU0 K) := by rw [hcomm, hDp]
  have hYy : cgE Yg (cgE z (zU0 K)) = cgE z (zU0 K) := by rw [hcomm, hYp]
  obtain ⟨r, u₀, u₁, u₂, v₀, v₁, v₂, s, hy⟩ : ∃ r u₀ u₁ u₂ v₀ v₁ v₂ s : K,
      cgE z (zU0 K) = zmk r u₀ u₁ u₂ v₀ v₁ v₂ s :=
    ⟨_, _, _, _, _, _, _, _, zorn_eta _⟩
  rw [hy] at hDy hYy
  have key : ∀ (a x : K), a ≠ 1 → a * x = x → x = 0 := fun a x ha h => by
    have : (a - 1) * x = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') ha
    · exact h'
  change gAFun _ _ = _ at hDy
  rw [gAFun_diag3] at hDy
  obtain ⟨-, -, hu1, hu2, -, hv1, hv2, -⟩ := zmk_inj hDy
  have hu1' : u₁ = 0 := key c u₁ hc1 hu1
  have hu2' : u₂ = 0 := key c⁻¹ u₂ hc' hu2
  have hv1' : v₁ = 0 := key c⁻¹ v₁ hc' (by simpa using hv1)
  have hv2' : v₂ = 0 := key c v₂ hc1 (by simpa using hv2)
  change ybFun _ _ = _ at hYy
  rw [ybFun_zmk] at hYy
  obtain ⟨-, -, -, hY3, -, hY5, -, -⟩ := zmk_inj hYy
  subst hu1' hu2' hv1' hv2'
  simp at hY3 hY5
  have hv0' : v₀ = 0 := hY3
  have hrs : r + s = 0 := hY5
  have hsr : s = r := by linear_combination hrs - r * h2
  subst hv0' hsr
  have hN := cg_norm z (zU0 K)
  rw [hy, zU0, cayleyNorm_zmk, cayleyNorm_zmk] at hN
  have hr0 : s = 0 := by
    have : s * s = 0 := by linear_combination hN
    exact mul_self_eq_zero.mp this
  subst hr0
  have hyU : cgE z (zU0 K) = u₀ • zU0 K := by
    rw [hy, zU0, zmk_smul]
    apply zmk_congr <;> simp
  have hX : ∀ x ∈ nullPts K, cgE z x = u₀ • x := by
    intro x hx
    rw [← orbit_zU0_eq] at hx
    obtain ⟨g, rfl⟩ := hx
    change cgE z (cgE g (zU0 K)) = u₀ • cgE g (zU0 K)
    rw [← hcomm g, hyU, map_smul]
  have hne : ∀ {r u₀ u₁ u₂ v₀ v₁ v₂ s : K}, (r ≠ 0 ∨ u₀ ≠ 0 ∨ u₁ ≠ 0 ∨ u₂ ≠ 0 ∨ v₀ ≠ 0 ∨
      v₁ ≠ 0 ∨ v₂ ≠ 0 ∨ s ≠ 0) → zmk r u₀ u₁ u₂ v₀ v₁ v₂ s ≠ 0 := by
    intro r u₀ u₁ u₂ v₀ v₁ v₂ s h h0
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := zmk_inj (h0.trans zmk_zero.symm)
    rcases h with h | h | h | h | h | h | h | h <;> contradiction
  have hU0 : zU0 K ∈ nullPts K := by
    refine ⟨hne (Or.inr (Or.inl one_ne_zero)), ?_, ?_⟩
    · rw [zU0, cayleyTr_zmk]; ring
    · rw [zU0, cayleyNorm_zmk]; ring
  have hU1 : zmk (0 : K) 0 1 0 0 0 0 0 ∈ nullPts K := by
    refine ⟨hne (Or.inr (Or.inr (Or.inl one_ne_zero))), ?_, ?_⟩
    · rw [cayleyTr_zmk]; ring
    · rw [cayleyNorm_zmk]; ring
  have hV0 : zmk (0 : K) 0 0 0 1 0 0 0 ∈ nullPts K := by
    refine ⟨hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl one_ne_zero))))), ?_, ?_⟩
    · rw [cayleyTr_zmk]; ring
    · rw [cayleyNorm_zmk]; ring
  have hV1 : zmk (0 : K) 0 0 0 0 1 0 0 ∈ nullPts K := by
    refine ⟨hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl one_ne_zero)))))), ?_, ?_⟩
    · rw [cayleyTr_zmk]; ring
    · rw [cayleyNorm_zmk]; ring
  have hW : zmk (1 : K) 0 1 0 0 1 0 1 ∈ nullPts K := by
    refine ⟨hne (Or.inl one_ne_zero), ?_, ?_⟩
    · rw [cayleyTr_zmk]; linear_combination h2
    · rw [cayleyNorm_zmk]; linear_combination h2
  have hsum : zmk (1 : K) 0 1 0 0 1 0 1 + zmk (0 : K) 0 1 0 0 0 0 0 + zmk (0 : K) 0 0 0 0 1 0 0 =
      cayleyOne K := by
    rw [cayleyOne_eq, zmk_add, zmk_add]
    apply zmk_congr <;> first | ring1 | linear_combination h2
  have h1 : cgE z (cayleyOne K) = u₀ • cayleyOne K := by
    rw [← hsum, map_add, map_add, hX _ hW, hX _ hU1, hX _ hV1, ← smul_add, ← smul_add]
  rw [cg_one] at h1
  have hu : u₀ = 1 := by
    have := congrArg Prod.fst h1
    simpa [cayleyOne] using this.symm
  subst hu
  have hfix : ∀ x ∈ nullPts K, cgE z x = x := fun x hx => by rw [hX x hx, one_smul]
  have hE : cgE z (zmk (1 : K) 0 0 0 0 0 0 0) = zmk 1 0 0 0 0 0 0 0 := by
    have hprod : cayleyMul (zmk (0 : K) 1 0 0 0 0 0 0) (zmk (0 : K) 0 0 0 1 0 0 0) =
        zmk 1 0 0 0 0 0 0 0 := by
      rw [cayleyMul_zmk]
      apply zmk_congr <;> ring
    rw [← hprod, cg_mul]
    have hU0' : zmk (0 : K) 1 0 0 0 0 0 0 ∈ nullPts K := hU0
    rw [hfix _ hU0', hfix _ hV0]
  have hU2 : zmk (0 : K) 0 0 1 0 0 0 0 ∈ nullPts K := by
    refine ⟨hne (Or.inr (Or.inr (Or.inr (Or.inl one_ne_zero)))), ?_, ?_⟩
    · rw [cayleyTr_zmk]; ring
    · rw [cayleyNorm_zmk]; ring
  have hV2 : zmk (0 : K) 0 0 0 0 0 1 0 ∈ nullPts K := by
    refine ⟨hne (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl one_ne_zero))))))), ?_, ?_⟩
    · rw [cayleyTr_zmk]; ring
    · rw [cayleyNorm_zmk]; ring
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  obtain ⟨r, a₀, a₁, a₂, b₀, b₁, b₂, s', hx⟩ : ∃ r a₀ a₁ a₂ b₀ b₁ b₂ s' : K,
      x = zmk r a₀ a₁ a₂ b₀ b₁ b₂ s' := ⟨_, _, _, _, _, _, _, _, zorn_eta x⟩
  have hdec : zmk r a₀ a₁ a₂ b₀ b₁ b₂ s' =
      (r + s') • zmk (1 : K) 0 0 0 0 0 0 0 + a₀ • zmk (0 : K) 1 0 0 0 0 0 0 +
        a₁ • zmk (0 : K) 0 1 0 0 0 0 0 + a₂ • zmk (0 : K) 0 0 1 0 0 0 0 +
        b₀ • zmk (0 : K) 0 0 0 1 0 0 0 + b₁ • zmk (0 : K) 0 0 0 0 1 0 0 +
        b₂ • zmk (0 : K) 0 0 0 0 0 1 0 + s' • cayleyOne K := by
    rw [cayleyOne_eq]
    simp only [zmk_smul, zmk_add]
    apply zmk_congr <;> first | ring1 | linear_combination (-s') * h2
  have hU0' : zmk (0 : K) 1 0 0 0 0 0 0 ∈ nullPts K := hU0
  show cgE z x = x
  rw [hx, hdec]
  simp only [map_add, map_smul]
  rw [hE, hfix _ hU0', hfix _ hU1, hfix _ hU2, hfix _ hV0, hfix _ hV1, hfix _ hV2, cg_one]


theorem center_commutator_quasithinG2_eq_bot {K : Type} [Field K] [CharP K 2] {c : K} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) : Subgroup.center ↥⁅quasithinG2 K, quasithinG2 K⁆ = ⊥ := by
  have h : ⁅quasithinG2 K, quasithinG2 K⁆ = cayleyGroup K := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
      cayley_commutator_eq hc0 hc1]
  generalize ⁅quasithinG2 K, quasithinG2 K⁆ = H at h ⊢
  subst h
  exact center_cayleyGroup_eq_bot hc0 hc1

end CFSG.Quasithin.A318Excl

module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveBasis
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveAutSl3
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveCentralizes

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂)

include h

private theorem eq_of_conj_eq_range {a b : SpecialLinearGroup (Fin 6) F2}
    (hact : ∀ k ∈ K, φ₂ a * k * (φ₂ a)⁻¹ = φ₂ b * k * (φ₂ b)⁻¹) : a = b := by
  have hcomm : ∀ m : SpecialLinearGroup (Fin 6) F2,
      φ₂ (a⁻¹ * b) * φ₂ m = φ₂ m * φ₂ (a⁻¹ * b) := by
    intro m
    have hm : φ₂ m ∈ K := by rw [← h.coords.range₂]; exact ⟨m, rfl⟩
    have hh := hact (φ₂ m) hm
    have h' : a * m * a⁻¹ = b * m * b⁻¹ := by
      apply h.coords.inj₂
      simpa only [map_mul, map_inv] using hh
    rw [← map_mul, ← map_mul]
    congr 1
    calc a⁻¹ * b * m = a⁻¹ * (b * m) := by group
      _ = a⁻¹ * (b * m * b⁻¹ * b) := by group
      _ = a⁻¹ * (a * m * a⁻¹ * b) := by rw [h']
      _ = m * (a⁻¹ * b) := by group
  have h1 : a⁻¹ * b = 1 := eq_one_of_commute_range h.coords.inj₂ hcomm
  exact inv_mul_eq_one.mp h1

theorem autK_pres {e : Fin 4 → ↥Bs} (he0 : (e 0 : G) = vElt φ₁) (he1 : (e 1 : G) = uElt φ₂)
    (he2 : (e 2 : G) = φ₁ (omegaBlock 5 4)) (he3 : (e 3 : G) = wElt φ₂)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer K Bs) :
    φ (e 0) = e 0 ∧ ∀ i : Fin 4, i ≠ 0 → ∃ j : Fin 4, j ≠ 0 ∧ (φ (e i) = e j ∨ φ (e i) = (e j)⁻¹) := by
  let P : MulAut ↥Bs → Prop := fun ψ => ψ (e 0) = e 0 ∧
    ∀ i : Fin 4, i ≠ 0 → ∃ j : Fin 4, j ≠ 0 ∧ (ψ (e i) = e j ∨ ψ (e i) = (e j)⁻¹)
  change P φ
  have hident : ∀ i : Fin 4, i ≠ 0 →
      ∃ k : Fin 5, (k = 0 ∨ k = 2 ∨ k = 4) ∧ (e i : G) = φ₂ (omegaBlock 5 k) := by
    intro i hi
    have hi123 : i = 1 ∨ i = 2 ∨ i = 3 := by
      rcases i with ⟨n, hn⟩
      have hn4 : n < 4 := hn
      interval_cases n
      · exact absurd rfl hi
      · exact Or.inl (Fin.ext rfl)
      · exact Or.inr (Or.inl (Fin.ext rfl))
      · exact Or.inr (Or.inr (Fin.ext rfl))
    rcases hi123 with rfl | rfl | rfl
    · exact ⟨0, Or.inl rfl, by rw [he1]; rfl⟩
    · exact ⟨2, Or.inr (Or.inl rfl), by rw [he2, phi1_omega4_eq h]⟩
    · exact ⟨4, Or.inr (Or.inr rfl), by rw [he3]; rfl⟩
  have hblock : ∀ k : Fin 5, (k = 0 ∨ k = 2 ∨ k = 4) →
      ∃ j : Fin 4, j ≠ 0 ∧ (e j : G) = φ₂ (omegaBlock 5 k) := by
    intro k hk
    rcases hk with rfl | rfl | rfl
    · exact ⟨1, by decide, by rw [he1]; rfl⟩
    · exact ⟨2, by decide, by rw [he2, phi1_omega4_eq h]⟩
    · exact ⟨3, by decide, by rw [he3]; rfl⟩
  have hone : P 1 := by
    refine ⟨?_, ?_⟩
    · rfl
    · intro i hi
      exact ⟨i, hi, Or.inl rfl⟩
  have hmul : ∀ u v : MulAut ↥Bs, P u → P v → P (u * v) := by
    intro u v hu hv
    refine ⟨?_, ?_⟩
    · change u (v (e 0)) = e 0
      rw [hv.1, hu.1]
    · intro i hi
      obtain ⟨j, hj, hvj⟩ := hv.2 i hi
      obtain ⟨l, hl, hulj⟩ := hu.2 j hj
      refine ⟨l, hl, ?_⟩
      change u (v (e i)) = e l ∨ u (v (e i)) = (e l)⁻¹
      rcases hvj with hvj | hvj
      · rw [hvj]
        rcases hulj with hulj | hulj
        · exact Or.inl hulj
        · exact Or.inr hulj
      · rw [hvj, map_inv]
        rcases hulj with hulj | hulj
        · exact Or.inr (by rw [hulj])
        · exact Or.inl (by rw [hulj, inv_inv])
  have hpow : ∀ (u : MulAut ↥Bs) (n : ℕ), P u → P (u ^ n) := by
    intro u n hu
    induction n with
    | zero => simpa using hone
    | succ n ih =>
        rw [pow_succ]
        exact hmul _ _ ih hu
  have hinv : ∀ u : MulAut ↥Bs, P u → P u⁻¹ := by
    intro u hu
    have huinv : u⁻¹ = u ^ (orderOf u - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (orderOf_pos u),
        pow_orderOf_eq_one]
    rw [huinv]
    exact hpow u (orderOf u - 1) hu
  change φ ∈ Subgroup.closure (ggInduced K Bs) at hφ
  refine Subgroup.closure_induction (p := fun g _ => P g) ?_ hone ?_ ?_ hφ
  ·
    intro ψ hψ
    obtain ⟨g, hgK, hgN, hψconj⟩ := hψ
    obtain ⟨s, hs_eq⟩ : ∃ s : SpecialLinearGroup (Fin 6) F2, φ₂ s = g := by
      have : g ∈ φ₂.range := by rw [h.coords.range₂]; exact hgK
      exact this
    subst g
    have hs_norm : ∀ t ∈ halfTorus 5, s * t * s⁻¹ ∈ halfTorus 5 := by
      intro t ht
      have htK : t ∈ halfTorusK 5 := by rwa [halfTorusK_five_eq]
      have hcB : φ₂ t ∈ Bs := h.torusK_le (Subgroup.mem_map.mpr ⟨t, htK, rfl⟩)
      have hgcB : φ₂ s * φ₂ t * (φ₂ s)⁻¹ ∈ Bs :=
        (Subgroup.mem_normalizer_iff.mp hgN (φ₂ t)).mp hcB
      obtain ⟨t', ht'K, ht'k⟩ := h.coords.actK (φ₂ s * φ₂ t * (φ₂ s)⁻¹) hgcB
      have ht' : t' ∈ halfTorus 5 := halfTorusK_five_eq ▸ ht'K
      have hact : ∀ k ∈ K, φ₂ (s * t * s⁻¹) * k * (φ₂ (s * t * s⁻¹))⁻¹ =
          φ₂ t' * k * (φ₂ t')⁻¹ := by
        intro k hk
        have := ht'k k hk
        simpa only [map_mul, map_inv] using this
      have heq : s * t * s⁻¹ = t' := eq_of_conj_eq_range h hact
      rw [heq]
      exact ht'
    refine ⟨?_, ?_⟩
    ·
      apply Subtype.ext
      rw [hψconj (e 0), he0]
      have hv_y : vElt φ₁ ∈ Subgroup.zpowers y := by
        rw [zpowers_y h]
        exact Subgroup.mem_zpowers _
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hv_y
      rw [← ha]
      obtain ⟨-, -, -, -, -, -, -, hyK, -, -⟩ := h.basic
      have hcomm : Commute (φ₂ s) y := (hyK (φ₂ s) hgK).symm
      calc φ₂ s * y ^ a * (φ₂ s)⁻¹ = y ^ a * φ₂ s * (φ₂ s)⁻¹ := by
            rw [(hcomm.zpow_right a).eq]
        _ = y ^ a := by group
    ·
      intro i hi
      obtain ⟨k, hk, hik⟩ := hident i hi
      obtain ⟨k', hk', hconj⟩ := conj_omegaBlock_mem_blocks hs_norm hk
      obtain ⟨j, hj, hej⟩ := hblock k' hk'
      refine ⟨j, hj, ?_⟩
      have hψconj' : (ψ (e i) : G) = φ₂ (s * omegaBlock 5 k * s⁻¹) := by
        rw [hψconj (e i), hik, ← map_mul, ← map_inv, ← map_mul]
      rcases hconj with hconj | hconj
      · left
        apply Subtype.ext
        rw [hψconj', hconj]
        exact hej.symm
      · right
        apply Subtype.ext
        rw [hψconj', hconj, map_inv, Subgroup.coe_inv, hej]
  ·
    intro u v hu hv hpu hpv
    exact hmul u v hpu hpv
  ·
    intro u hu hpu
    exact hinv u hpu

end GGHalfCtx

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveBasis
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveAutSl3

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂)

include h

private theorem eq_of_conj_eq_range {a b : SpecialLinearGroup (Fin 6) F2}
    (hact : ∀ l ∈ L, φ₁ a * l * (φ₁ a)⁻¹ = φ₁ b * l * (φ₁ b)⁻¹) : a = b := by
  have hcomm : ∀ m : SpecialLinearGroup (Fin 6) F2,
      φ₁ (a⁻¹ * b) * φ₁ m = φ₁ m * φ₁ (a⁻¹ * b) := by
    intro m
    have hm : φ₁ m ∈ L := by rw [← h.coords.range₁]; exact ⟨m, rfl⟩
    have hh := hact (φ₁ m) hm
    have h' : a * m * a⁻¹ = b * m * b⁻¹ := by
      apply h.coords.inj₁
      simpa only [map_mul, map_inv] using hh
    rw [← map_mul, ← map_mul]
    congr 1
    calc a⁻¹ * b * m = a⁻¹ * (b * m) := by group
      _ = a⁻¹ * (b * m * b⁻¹ * b) := by group
      _ = a⁻¹ * (a * m * a⁻¹ * b) := by rw [h']
      _ = m * (a⁻¹ * b) := by group
  have h1 : a⁻¹ * b = 1 := eq_one_of_commute_range h.coords.inj₁ hcomm
  exact inv_mul_eq_one.mp h1

theorem autL_pres {e : Fin 4 → ↥Bs} (he0 : (e 0 : G) = vElt φ₁) (he1 : (e 1 : G) = uElt φ₂)
    (he2 : (e 2 : G) = φ₁ (omegaBlock 5 4)) (he3 : (e 3 : G) = wElt φ₂)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer L Bs) :
    φ (e 3) = e 3 ∧ ∀ i : Fin 4, i ≠ 3 → ∃ j : Fin 4, j ≠ 3 ∧ (φ (e i) = e j ∨ φ (e i) = (e j)⁻¹) := by
  let P : MulAut ↥Bs → Prop := fun ψ => ψ (e 3) = e 3 ∧
    ∀ i : Fin 4, i ≠ 3 → ∃ j : Fin 4, j ≠ 3 ∧ (ψ (e i) = e j ∨ ψ (e i) = (e j)⁻¹)
  change P φ
  have hident : ∀ i : Fin 4, i ≠ 3 →
      ∃ k : Fin 5, (k = 0 ∨ k = 2 ∨ k = 4) ∧ (e i : G) = φ₁ (omegaBlock 5 k) := by
    intro i hi
    have hi012 : i = 0 ∨ i = 1 ∨ i = 2 := by
      rcases i with ⟨n, hn⟩
      have hn4 : n < 4 := hn
      interval_cases n
      · exact Or.inl (Fin.ext rfl)
      · exact Or.inr (Or.inl (Fin.ext rfl))
      · exact Or.inr (Or.inr (Fin.ext rfl))
      · exact absurd rfl hi
    rcases hi012 with rfl | rfl | rfl
    · exact ⟨0, Or.inl rfl, by rw [he0]; rfl⟩
    · exact ⟨2, Or.inr (Or.inl rfl), by rw [he1, uElt_eq h]; rfl⟩
    · exact ⟨4, Or.inr (Or.inr rfl), he2⟩
  have hblock : ∀ k : Fin 5, (k = 0 ∨ k = 2 ∨ k = 4) →
      ∃ j : Fin 4, j ≠ 3 ∧ (e j : G) = φ₁ (omegaBlock 5 k) := by
    intro k hk
    rcases hk with rfl | rfl | rfl
    · exact ⟨0, by decide, by rw [he0]; rfl⟩
    · exact ⟨1, by decide, by rw [he1, uElt_eq h]; rfl⟩
    · exact ⟨2, by decide, by rw [he2]⟩
  have hone : P 1 := by
    refine ⟨?_, ?_⟩
    · rfl
    · intro i hi
      exact ⟨i, hi, Or.inl rfl⟩
  have hmul : ∀ u v : MulAut ↥Bs, P u → P v → P (u * v) := by
    intro u v hu hv
    refine ⟨?_, ?_⟩
    · change u (v (e 3)) = e 3
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
  change φ ∈ Subgroup.closure (ggInduced L Bs) at hφ
  refine Subgroup.closure_induction (p := fun g _ => P g) ?_ hone ?_ ?_ hφ
  ·
    intro ψ hψ
    obtain ⟨g, hgL, hgN, hψconj⟩ := hψ
    obtain ⟨s, hs_eq⟩ : ∃ s : SpecialLinearGroup (Fin 6) F2, φ₁ s = g := by
      have : g ∈ φ₁.range := by rw [h.coords.range₁]; exact hgL
      exact this
    subst g
    have hs_norm : ∀ t ∈ halfTorus 5, s * t * s⁻¹ ∈ halfTorus 5 := by
      intro t ht
      have hcB : φ₁ t ∈ Bs := h.torusL_le (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
      have hgcB : φ₁ s * φ₁ t * (φ₁ s)⁻¹ ∈ Bs :=
        (Subgroup.mem_normalizer_iff.mp hgN (φ₁ t)).mp hcB
      obtain ⟨t', ht', ht'l⟩ := h.coords.actL (φ₁ s * φ₁ t * (φ₁ s)⁻¹) hgcB
      have hact : ∀ l ∈ L, φ₁ (s * t * s⁻¹) * l * (φ₁ (s * t * s⁻¹))⁻¹ =
          φ₁ t' * l * (φ₁ t')⁻¹ := by
        intro l hl
        have := ht'l l hl
        simpa only [map_mul, map_inv] using this
      have heq : s * t * s⁻¹ = t' := eq_of_conj_eq_range h hact
      rw [heq]
      exact ht'
    refine ⟨?_, ?_⟩
    ·
      apply Subtype.ext
      rw [hψconj (e 3), he3]
      have hw_x : wElt φ₂ ∈ Subgroup.zpowers x := by
        rw [zpowers_x h]
        exact Subgroup.mem_zpowers _
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hw_x
      rw [← ha]
      obtain ⟨-, -, -, -, -, -, hxL, -, -, -⟩ := h.basic
      have hcomm : Commute (φ₁ s) x := (hxL (φ₁ s) hgL).symm
      calc φ₁ s * x ^ a * (φ₁ s)⁻¹ = x ^ a * φ₁ s * (φ₁ s)⁻¹ := by
            rw [(hcomm.zpow_right a).eq]
        _ = x ^ a := by group
    ·
      intro i hi
      obtain ⟨k, hk, hik⟩ := hident i hi
      obtain ⟨k', hk', hconj⟩ := conj_omegaBlock_mem_blocks hs_norm hk
      obtain ⟨j, hj, hej⟩ := hblock k' hk'
      refine ⟨j, hj, ?_⟩
      have hψconj' : (ψ (e i) : G) = φ₁ (s * omegaBlock 5 k * s⁻¹) := by
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

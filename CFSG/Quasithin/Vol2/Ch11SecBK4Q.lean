module

public import CFSG.Quasithin.Vol2.Ch11G2Q8ParG2
public import CFSG.Quasithin.Vol2.Ch11G2Q8SiegelM

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit

namespace BK4

variable {F : Type} [Field F] [CharP F 2]

theorem g2Act_tL_sub (s : F) (w : Ix3 → F) :
    g2Act (G2Q8.tL s) w - w = q6 (s * w (.inl 2)) 0 0 0 0 (s * w (.inr 0)) := by
  conv_lhs => rw [q6_eta w, G2Q8.g2Act_tL]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem tL_mem_U0 (s : F) : G2Q8.tL s ∈ G2Q8.U0 F := by
  intro h w hw
  rw [g2Act_tL_sub]
  refine G2Q8.inF_q6_iff.mpr ⟨fun hh => ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun hh => ?_⟩
  · have h1 : h = 0 := by omega
    subst h1
    rw [hw (.inl 2) (by decide), mul_zero]
  · have h1 : w (.inr 0) = 0 := hw (.inr 0) (by
      have : G2Q8.ht (.inr 0) = 5 := rfl
      omega)
    rw [h1, mul_zero]

theorem mem_stabQ_two_of_comm {s : F} (hs : s ≠ 0) {n : ↥(cayleyGroup F)}
    (hn : n * G2Q8.tL s = G2Q8.tL s * n) : n ∈ G2Q8.stabQ (G2Q8.stdF F 2) := by
  have key : ∀ m : ↥(cayleyGroup F), m * G2Q8.tL s = G2Q8.tL s * m →
      ∀ w ∈ G2Q8.stdF F 2, g2Act m w ∈ G2Q8.stdF F 2 := by
    intro m hm w hw
    obtain ⟨h1, h2, h3, h4⟩ := G2Q8.mem_stdF_two.mp hw
    set z : Ix3 → F := q6 0 0 (s⁻¹ * w (.inl 0)) (s⁻¹ * w (.inr 2)) 0 0 with hz
    have hwz : w = g2Act (G2Q8.tL s) z - z := by
      rw [g2Act_tL_sub, hz]
      conv_lhs => rw [q6_eta w]
      simp only [q6, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, Matrix.cons_val_zero]
      rw [h1, h2, h3, h4, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hs, one_mul, one_mul]
    have e : g2Act m w = g2Act (G2Q8.tL s) (g2Act m z) - g2Act m z := by
      rw [hwz, map_sub, ← G2Q8.g2Act_mul_apply, hm, G2Q8.g2Act_mul_apply]
    rw [e]
    exact G2Q8.g2Act_tL_sub_mem s _
  have hn' : n⁻¹ * G2Q8.tL s = G2Q8.tL s * n⁻¹ := by
    calc n⁻¹ * G2Q8.tL s = n⁻¹ * (G2Q8.tL s * n) * n⁻¹ := by group
      _ = n⁻¹ * (n * G2Q8.tL s) * n⁻¹ := by rw [hn]
      _ = G2Q8.tL s * n⁻¹ := by group
  refine G2Q8.mem_stabQ.mpr fun w => ⟨key n hn w, fun hw => ?_⟩
  have := key n⁻¹ hn' _ hw
  rwa [G2Q8.g2Act_inv_apply] at this

theorem polarQ_g2Act_eq_zero {S : Submodule F (Ix3 → F)} {g : ↥(cayleyGroup F)}
    (hg : g ∈ G2Q8.stabQ S) {x : Ix3 → F} (hx : ∀ y ∈ S, G2Q8.polarQ x y = 0) :
    ∀ y ∈ S, G2Q8.polarQ (g2Act g x) y = 0 := by
  intro y hy
  have h1 : g2Act g⁻¹ y ∈ S := by
    rw [G2Q8.mem_stabQ.mp hg, G2Q8.g2Act_apply_inv]
    exact hy
  rw [← G2Q8.g2Act_apply_inv g y, G2Q8.polarQ_g2Act]
  exact hx _ h1

omit [CharP F 2] in
theorem perp_four_iff (x : Ix3 → F) :
    (∀ y ∈ G2Q8.stdF F 4, G2Q8.polarQ x y = 0) ↔ x ∈ G2Q8.stdF F 2 := by
  have hm4 : ∀ a b e f : F, q6 a b 0 0 e f ∈ G2Q8.stdF F 4 := fun a b e f => by
    refine G2Q8.mem_stdF.mpr fun k hk => ?_
    rcases k with k | k <;> fin_cases k <;> simp_all [G2Q8.ht, q6]
  constructor
  · intro h
    have e1 := h _ (hm4 1 0 0 0)
    have e2 := h _ (hm4 0 1 0 0)
    have e3 := h _ (hm4 0 0 1 0)
    have e4 := h _ (hm4 0 0 0 1)
    simp [G2Q8.polarQ, q6] at e1 e2 e3 e4
    exact G2Q8.mem_stdF_two.mpr ⟨e3, e4, e1, e2⟩
  · intro hx y hy
    obtain ⟨h1, h2, h3, h4⟩ := G2Q8.mem_stdF_two.mp hx
    have hy1 : y (.inl 2) = 0 := hy (.inl 2) (by decide)
    have hy2 : y (.inr 0) = 0 := hy (.inr 0) (by decide)
    simp [G2Q8.polarQ, h1, h2, h3, h4, hy1, hy2]

omit [CharP F 2] in
theorem perp_five_iff (x : Ix3 → F) :
    (∀ y ∈ G2Q8.stdF F 5, G2Q8.polarQ x y = 0) ↔ x ∈ G2Q8.stdF F 1 := by
  have hm5 : ∀ a b c e f : F, q6 a b c 0 e f ∈ G2Q8.stdF F 5 := fun a b c e f => by
    refine G2Q8.mem_stdF.mpr fun k hk => ?_
    rcases k with k | k <;> fin_cases k <;> simp_all [G2Q8.ht, q6]
  constructor
  · intro h
    have e1 := h _ (hm5 1 0 0 0 0)
    have e2 := h _ (hm5 0 1 0 0 0)
    have e3 := h _ (hm5 0 0 1 0 0)
    have e4 := h _ (hm5 0 0 0 1 0)
    have e5 := h _ (hm5 0 0 0 0 1)
    simp [G2Q8.polarQ, q6] at e1 e2 e3 e4 e5
    refine G2Q8.mem_stdF.mpr fun k hk => ?_
    rcases k with k | k <;> fin_cases k <;> simp_all [G2Q8.ht]
  · intro hx y hy
    have hy1 : y (.inr 0) = 0 := hy (.inr 0) (by decide)
    have hx' : ∀ k, 1 ≤ G2Q8.ht k → x k = 0 := hx
    have h1 : x (.inl 1) = 0 := hx' _ (by decide)
    have h2 : x (.inl 2) = 0 := hx' _ (by decide)
    have h3 : x (.inr 0) = 0 := hx' _ (by decide)
    have h4 : x (.inr 1) = 0 := hx' _ (by decide)
    have h5 : x (.inr 2) = 0 := hx' _ (by decide)
    simp [G2Q8.polarQ, h1, h2, h3, h4, h5, hy1]

theorem mem_stabQ_two_of_four {g : ↥(cayleyGroup F)} (hg : g ∈ G2Q8.stabQ (G2Q8.stdF F 4)) :
    g ∈ G2Q8.stabQ (G2Q8.stdF F 2) := by
  have hg' := (G2Q8.stabQ (G2Q8.stdF F 4)).inv_mem hg
  refine G2Q8.mem_stabQ.mpr fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · exact (perp_four_iff _).mp (polarQ_g2Act_eq_zero hg ((perp_four_iff w).mpr hw))
  · have := (perp_four_iff _).mp (polarQ_g2Act_eq_zero hg' ((perp_four_iff _).mpr hw))
    rwa [G2Q8.g2Act_inv_apply] at this

theorem mem_stabQ_one_of_five {g : ↥(cayleyGroup F)} (hg : g ∈ G2Q8.stabQ (G2Q8.stdF F 5)) :
    g ∈ G2Q8.stabQ (G2Q8.stdF F 1) := by
  have hg' := (G2Q8.stabQ (G2Q8.stdF F 5)).inv_mem hg
  refine G2Q8.mem_stabQ.mpr fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · exact (perp_five_iff _).mp (polarQ_g2Act_eq_zero hg ((perp_five_iff w).mpr hw))
  · have := (perp_five_iff _).mp (polarQ_g2Act_eq_zero hg' ((perp_five_iff _).mpr hw))
    rwa [G2Q8.g2Act_inv_apply] at this

theorem stabQ_stdF_le {h : ℕ} (h1 : 1 ≤ h) (h5 : h ≤ 5) :
    G2Q8.stabQ (G2Q8.stdF F h) ≤ G2Q8.stabQ (G2Q8.stdF F 1) ∨
      G2Q8.stabQ (G2Q8.stdF F h) ≤ G2Q8.stabQ (G2Q8.stdF F 2) := by
  interval_cases h
  · exact Or.inl le_rfl
  · exact Or.inr le_rfl
  · exact Or.inl G2Q8.stabQ_three_le_one
  · exact Or.inr fun g hg => mem_stabQ_two_of_four hg
  · exact Or.inl fun g hg => mem_stabQ_one_of_five hg

theorem eq_one_of_comm_U0 [Finite F] {n : ↥(cayleyGroup F)} {k : ℕ} (hk : Odd k)
    (hnk : n ^ k = 1) (hn : ∀ u ∈ G2Q8.U0 F, n * u = u * n) : n = 1 := by
  have hcomm : ∀ u ∈ G2Q8.U0 F, ∀ w, g2Act n (g2Act u w) = g2Act u (g2Act n w) := by
    intro u hu w
    rw [← G2Q8.g2Act_mul_apply, hn u hu, G2Q8.g2Act_mul_apply]
  obtain ⟨c, hc⟩ : ∃ c : F, g2Act n (G2Q8.eu 0 1) = c • G2Q8.eu 0 1 := by
    refine G2Q8.mem_stdF_one_iff.mp (G2Q8.fixed_U0 fun u hu => ?_)
    rw [← hcomm u hu, G2Q8.U0_fix_one hu (G2Q8.mem_stdF_one_iff.mpr ⟨1, (one_smul _ _).symm⟩)]
  let N : (Ix3 → F) →ₗ[F] (Ix3 → F) :=
    { toFun := fun w => g2Act n w - c • w
      map_add' := fun a b => by rw [map_add, smul_add]; abel
      map_smul' := fun a w => by rw [G2Q8.g2Act_smul, smul_sub, smul_comm]; rfl }
  have hN : ∀ w, N w = g2Act n w - c • w := fun w => rfl
  have hNu : ∀ u ∈ G2Q8.U0 F, ∀ w, N (g2Act u w) = g2Act u (N w) := by
    intro u hu w
    rw [hN, hN, map_sub, G2Q8.g2Act_smul, hcomm u hu]
  have hker : G2Q8.U0Stable (LinearMap.ker N) := by
    intro u hu w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [hNu u hu, hw, map_zero]
  obtain ⟨h, h6, hkerh⟩ := G2Q8.eq_stdF_of_stable hker
  have hu0 : G2Q8.eu 0 (1 : F) ∈ LinearMap.ker N := by
    rw [LinearMap.mem_ker, hN, hc, sub_self]
  have hN0 : ∀ w, N w = 0 := by
    by_cases h6' : h = 6
    · intro w
      have : w ∈ LinearMap.ker N := by rw [hkerh, h6', G2Q8.stdF_six]; exact Submodule.mem_top
      exact this
    exfalso
    have hh1 : 1 ≤ h := by
      by_contra h0
      have h00 : h = 0 := by omega
      rw [hkerh, h00, G2Q8.stdF_zero] at hu0
      exact G2Q8.g2Act_eu_ne_zero 1 (by rw [map_one]; exact hu0)
    set e : Ix3 → F := Pi.single (G2Q8.bv h) 1 with he
    have hht : G2Q8.ht (G2Q8.bv h) = h := G2Q8.ht_bv (by omega)
    have he1 : G2Q8.InF (h + 1) e := by
      intro j hj
      rw [he, Pi.single_apply]
      have : j ≠ G2Q8.bv h := fun hjb => by rw [hjb, hht] at hj; omega
      simp [this]
    have he0 : e ∉ LinearMap.ker N := by
      rw [hkerh]
      intro hmem
      have := (G2Q8.mem_stdF.mp hmem) (G2Q8.bv h) (by rw [hht])
      simp [he] at this
    have hNe : N e ∈ G2Q8.stdF F 1 := by
      refine G2Q8.fixed_U0 fun u hu => ?_
      have h1 : g2Act u e - e ∈ LinearMap.ker N := by
        rw [hkerh]
        exact (G2Q8.mem_U0.mp hu) h e he1
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
      rw [← hNu u hu, h1]
    have hNNe : N (N e) = 0 := by
      have : N e ∈ LinearMap.ker N := by
        rw [hkerh]
        exact G2Q8.stdF_mono hh1 hNe
      exact this
    have hn1 : g2Act n e = c • e + N e := by rw [hN]; abel
    have hn2 : g2Act n (N e) = c • N e := by
      have := hNNe
      rw [hN, sub_eq_zero] at this
      exact this
    have hQ : ∀ j : ℕ, g2Act (n ^ (j + 1)) e =
        c ^ (j + 1) • e + (((j : F) + 1) * c ^ j) • N e := by
      intro j
      induction j with
      | zero => rw [zero_add, pow_one, hn1]; simp
      | succ j ih =>
        rw [pow_succ' n (j + 1), G2Q8.g2Act_mul_apply, ih, map_add, G2Q8.g2Act_smul,
          G2Q8.g2Act_smul, hn1, hn2, smul_add, smul_smul, smul_smul, add_assoc, ← add_smul]
        have e1 : c ^ (j + 1) * c = c ^ (j + 1 + 1) := by ring
        have e2 : c ^ (j + 1) + ((j : F) + 1) * c ^ j * c =
            (((j + 1 : ℕ) : F) + 1) * c ^ (j + 1) := by push_cast; ring
        rw [e1, e2]
    obtain ⟨m, hm⟩ := hk
    have h1 := hQ (2 * m)
    rw [← hm, hnk, map_one, AddMonoid.End.coe_one, id_eq] at h1
    have hcoef : (((2 * m : ℕ) : F) + 1) = 1 := by
      push_cast
      rw [CharTwo.two_eq_zero, zero_mul, zero_add]
    have hNe0 : (N e) (G2Q8.bv h) = 0 := (G2Q8.mem_stdF.mp hNe) _ (by rw [hht]; exact hh1)
    have hck : c ^ k = 1 := by
      have h3 := congrFun h1 (G2Q8.bv h)
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hNe0, smul_zero, add_zero, he,
        Pi.single_eq_same, smul_eq_mul, mul_one] at h3
      exact h3.symm
    have hc0 : c ^ (2 * m) ≠ 0 := by
      intro h0
      have : c ^ k = 0 := by rw [hm, pow_succ, h0, zero_mul]
      rw [this] at hck
      exact zero_ne_one hck
    rw [hck, one_smul, hcoef, one_mul, left_eq_add, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact hc0 h1
    · exact he0 (LinearMap.mem_ker.mpr h1)
  have hsc : ∀ w, g2Act n w = c • w := fun w => sub_eq_zero.mp (hN0 w)
  have hc1 : c = 1 := G2Q8.scalar_eq_one hsc
  exact G2Q8.cayley_eq_one fun w => by rw [hsc, hc1, one_smul]

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB

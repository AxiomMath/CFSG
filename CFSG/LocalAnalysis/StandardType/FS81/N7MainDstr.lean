module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainFone
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainSyl
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainInvolCount
public import CFSG.LocalAnalysis.StandardType.FS81.N7FixQuotTwo
public import CFSG.LocalAnalysis.StandardType.FS81.N7FixDentGrp

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix symmDiff

private def nmhF2 {X : Type} [Group X] [Finite X] (S : N7MSetup X) (A₀ : Finset (Fin 8)) :
    Subgroup X where
  carrier := {x | ∃ B : Finset (Fin 8), B ⊆ A₀ ∧ Even B.card ∧ S.ρ x = nmSgn B}
  mul_mem' := by
    rintro a b ⟨A, hA, hAe, hAa⟩ ⟨B, hB, hBe, hBa⟩
    obtain ⟨C, hCe, hC⟩ := exists_nmSgn_of_mem_nmF
      (nmF_mul (nmSgn_mem_nmF hAe) (nmSgn_mem_nmF hBe))
    have hCeq : C = A ∆ B := by
      have hAB : nmSgn A * nmSgn B = nmSgn (A ∆ B) := nmSgn_mul
      exact q2nN7_sgn_injective (hC.symm.trans hAB)
    refine ⟨C, ?_, hCe, ?_⟩
    · rw [hCeq]
      intro i hi
      rcases Finset.mem_symmDiff.mp hi with ⟨hiA, -⟩ | ⟨hiB, -⟩
      · exact hA hiA
      · exact hB hiB
    · rw [map_mul, hAa, hBa]
      exact hC
  one_mem' := ⟨∅, Finset.empty_subset A₀, ⟨0, rfl⟩, by rw [map_one]; simp [nmSgn]⟩
  inv_mem' := by
    rintro x ⟨B, hB, hBe, hx⟩
    refine ⟨B, hB, hBe, ?_⟩
    calc S.ρ x⁻¹ = S.ρ x⁻¹ * 1 := by rw [mul_one]
      _ = S.ρ x⁻¹ * (S.ρ x * nmSgn B) := by rw [hx, nmSgn_mul_self]
      _ = (S.ρ x⁻¹ * S.ρ x) * nmSgn B := by rw [mul_assoc]
      _ = 1 * nmSgn B := by rw [← map_mul, inv_mul_cancel, map_one]
      _ = nmSgn B := one_mul _

private def nmhQ {X : Type} [Group X] [Finite X] (S : N7MSetup X) (A₀ : Finset (Fin 8)) :
    Subgroup X where
  carrier := {x | ∀ v : Coords 8, (∀ i ∈ A₀, v i = 0) → S.ρ x *ᵥ v = v}
  mul_mem' := by
    rintro x y hx hy v hv
    rw [map_mul, ← Matrix.mulVec_mulVec, hy v hv, hx v hv]
  one_mem' := by
    intro v _
    rw [map_one, Matrix.one_mulVec]
  inv_mem' := by
    rintro x hx v hv
    calc S.ρ x⁻¹ *ᵥ v = S.ρ x⁻¹ *ᵥ (S.ρ x *ᵥ v) := by rw [hx v hv]
      _ = (S.ρ x⁻¹ * S.ρ x) *ᵥ v := by rw [Matrix.mulVec_mulVec]
      _ = v := by rw [← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

private theorem nmh_vanishes_mulVec_of_comm {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {A₀ : Finset (Fin 8)} {t h : X} (hh : h * t = t * h) (ht : S.ρ t = nmSgn A₀)
    {v : Coords 8} (hv : ∀ i ∈ A₀, v i = 0) : ∀ i ∈ A₀, (S.ρ h *ᵥ v) i = 0 := by
  change VanishesOn A₀ (S.ρ h *ᵥ v)
  rw [N7Setup.vanishesOn_iff_sgn_mulVec]
  have hmat : S.ρ h * sgn A₀ = sgn A₀ * S.ρ h := by
    have h := congrArg S.ρ hh
    rwa [map_mul, map_mul, ht] at h
  rw [Matrix.mulVec_mulVec, ← hmat, ← Matrix.mulVec_mulVec]
  have hv' : sgn A₀ *ᵥ v = v :=
    (N7Setup.vanishesOn_iff_sgn_mulVec (S0 := A₀) (v := v)).mp hv
  rw [hv']

private theorem nmh_conj_mem_Q {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {A₀ : Finset (Fin 8)} {t g : X} (hg : g * t = t * g) (ht : S.ρ t = nmSgn A₀)
    {q : X} (hq : q ∈ nmhQ S A₀) : g * q * g⁻¹ ∈ nmhQ S A₀ := by
  intro v hv
  have hgv : ∀ i ∈ A₀, (S.ρ g⁻¹ *ᵥ v) i = 0 :=
    nmh_vanishes_mulVec_of_comm S (Commute.inv_left hg).eq ht hv
  have hqv : S.ρ q *ᵥ (S.ρ g⁻¹ *ᵥ v) = S.ρ g⁻¹ *ᵥ v := hq _ hgv
  calc S.ρ (g * q * g⁻¹) *ᵥ v
      = S.ρ g *ᵥ (S.ρ q *ᵥ (S.ρ g⁻¹ *ᵥ v)) := by
        rw [map_mul, map_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = S.ρ g *ᵥ (S.ρ g⁻¹ *ᵥ v) := by rw [hqv]
    _ = v := by
        rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]

private theorem nmhF2_le_Q {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {A₀ : Finset (Fin 8)} : nmhF2 S A₀ ≤ nmhQ S A₀ := by
  rintro x ⟨B, hB, -, hx⟩ v hv
  rw [hx, nmSgn_mulVec]
  funext i
  by_cases hi : i ∈ B
  · rw [if_pos hi, hv i (hB hi)]
    exact neg_zero
  · rw [if_neg hi]

private theorem nmh_perm_apply_eq_self_of_mulVec_single {σ : Equiv.Perm (Fin 8)}
    {s : Fin 8 → ZMod 3} (hs : IsSign s) {j : Fin 8}
    (h : spMat σ s *ᵥ (Pi.single j 1 : Coords 8) = Pi.single j 1) : σ j = j := by
  have hval := congrFun h (σ j)
  rw [spMat_mulVec] at hval
  dsimp only at hval
  rw [Equiv.symm_apply_apply, Pi.single_eq_same, mul_one] at hval
  by_cases hfix : σ j = j
  · exact hfix
  · rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hfix (1 : ZMod 3)] at hval
    rcases hs j with h1 | h1 <;> rw [h1] at hval <;> exact absurd hval (by decide)

private theorem nmh_conj_mem_F2 {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {A₀ : Finset (Fin 8)} (hA0 : 0 ∉ A₀) {q : X} (hq : q ∈ nmhQ S A₀) {f : X}
    (hf : f ∈ nmhF2 S A₀) : q * f * q⁻¹ ∈ nmhF2 S A₀ := by
  obtain ⟨B, hB, hBe, hfB⟩ := hf
  have hq0 : S.ρ q *ᵥ nmE0 = nmE0 :=
    hq nmE0 (fun i hi => Pi.single_eq_of_ne (fun h : i = 0 => hA0 (h ▸ hi)) 1)
  obtain ⟨σ, s, hs, ⟨hσ0, hs0, hps⟩, hqσ⟩ := (S.fix_iff q).mp hq0
  have hfixOut : ∀ j, j ∉ A₀ → σ j = j := by
    intro j hj
    have hfix : S.ρ q *ᵥ (Pi.single j 1 : Coords 8) = Pi.single j 1 :=
      hq _ (fun i hi => Pi.single_eq_of_ne (fun h : i = j => hj (h ▸ hi)) 1)
    rw [hqσ] at hfix
    exact nmh_perm_apply_eq_self_of_mulVec_single hs hfix
  have hmap : B.map σ.toEmbedding ⊆ A₀ := by
    intro x hx
    obtain ⟨i, hiB, hix⟩ := Finset.mem_map.mp hx
    subst hix
    by_contra hxA
    have hfix : σ (σ i) = σ i := hfixOut (σ i) hxA
    have hii : σ i = i := σ.injective hfix
    exact hxA (hii.symm ▸ hB hiB)
  refine ⟨B.map σ.toEmbedding, hmap, ?_, ?_⟩
  · rw [Finset.card_map]
    exact hBe
  · have hqinv : S.ρ q * S.ρ q⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h1 : S.ρ (q * f * q⁻¹) = spMat σ s * nmSgn B * S.ρ q⁻¹ := by
      rw [map_mul, map_mul, hqσ, hfB]
    rw [h1]
    change spMat σ s * sgn B * S.ρ q⁻¹ = sgn (B.map σ.toEmbedding)
    rw [q2nN7_spMat_mul_sgn, Matrix.mul_assoc,
      show spMat σ s * S.ρ q⁻¹ = 1 by rw [← hqσ, hqinv], Matrix.mul_one]

private theorem nmh_conj_mem_conjF2 {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {A₀ : Finset (Fin 8)} (hA0 : 0 ∉ A₀) {t d : X} (hd : d * t = t * d)
    (ht : S.ρ t = nmSgn A₀) {q : X} (hq : q ∈ nmhQ S A₀) {z : X}
    (hz : z ∈ Subgroup.map (MulAut.conj d).toMonoidHom (nmhF2 S A₀)) :
    q * z * q⁻¹ ∈ Subgroup.map (MulAut.conj d).toMonoidHom (nmhF2 S A₀) := by
  obtain ⟨f, hf, hfz⟩ := Subgroup.mem_map.mp hz
  have hq' : d⁻¹ * q * d ∈ nmhQ S A₀ := by
    simpa using nmh_conj_mem_Q S (Commute.inv_left hd).eq ht hq
  have hf' : (d⁻¹ * q * d) * f * (d⁻¹ * q * d)⁻¹ ∈ nmhF2 S A₀ :=
    nmh_conj_mem_F2 S hA0 hq' hf
  refine Subgroup.mem_map.mpr ⟨(d⁻¹ * q * d) * f * (d⁻¹ * q * d)⁻¹, hf', ?_⟩
  rw [← hfz]
  show d * ((d⁻¹ * q * d) * f * (d⁻¹ * q * d)⁻¹) * d⁻¹ = q * (d * f * d⁻¹) * q⁻¹
  group

private def nmhPerm {X : Type} [Group X] [Finite X] (S : N7MSetup X) (G : Subgroup X) :
    Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {m | ∃ z ∈ G, ∃ s : Fin 8 → ZMod 3, IsSign s ∧ S.ρ z = spMat m s}
  mul_mem' := by
    rintro m₁ m₂ ⟨z₁, hz₁, s₁, hs₁, hρ₁⟩ ⟨z₂, hz₂, s₂, hs₂, hρ₂⟩
    refine ⟨z₁ * z₂, G.mul_mem hz₁ hz₂, fun j => s₁ (m₂ j) * s₂ j, ?_, ?_⟩
    · intro j
      rcases hs₁ (m₂ j) with h | h <;> rcases hs₂ j with h' | h' <;> simp only [h, h'] <;> decide
    · rw [map_mul, hρ₁, hρ₂, spMat_mul]
  one_mem' := ⟨1, G.one_mem, fun _ => 1, fun _ => Or.inl rfl, by rw [map_one, spMat_one]⟩
  inv_mem' := by
    rintro m ⟨z, hz, s, hs, hρ⟩
    refine ⟨z⁻¹, G.inv_mem hz, fun j => s (m⁻¹ j), fun j => hs (m⁻¹ j), ?_⟩
    have hw : spMat m⁻¹ (fun j => s (m⁻¹ j)) * spMat m s = 1 := by
      rw [spMat_mul, inv_mul_cancel]
      have hfun : (fun j => s (m⁻¹ (m j)) * s j) = (fun _ => 1) := by
        funext j
        have hmm : m⁻¹ (m j) = j := by simp
        rw [hmm]
        rcases hs j with h | h <;> rw [h] <;> decide
      rw [hfun, spMat_one]
    calc S.ρ z⁻¹ = 1 * S.ρ z⁻¹ := by rw [one_mul]
      _ = (spMat m⁻¹ (fun j => s (m⁻¹ j)) * S.ρ z) * S.ρ z⁻¹ := by rw [hρ, hw]
      _ = spMat m⁻¹ (fun j => s (m⁻¹ j)) * (S.ρ z * S.ρ z⁻¹) := by rw [mul_assoc]
      _ = spMat m⁻¹ (fun j => s (m⁻¹ j)) * 1 := by
          rw [← map_mul, mul_inv_cancel, map_one]
      _ = spMat m⁻¹ (fun j => s (m⁻¹ j)) := mul_one _

private theorem nmhPerm_apply_of_mem {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {A₀ : Finset (Fin 8)} {G : Subgroup X} (hGQ : G ≤ nmhQ S A₀)
    {m : Equiv.Perm (Fin 8)} (hm : m ∈ nmhPerm S G) {j : Fin 8} (hj : j ∉ A₀) :
    m j = j := by
  obtain ⟨z, hz, s, hs, hρ⟩ := hm
  have hfix : S.ρ z *ᵥ (Pi.single j 1 : Coords 8) = Pi.single j 1 :=
    hGQ hz _ (fun i hi => Pi.single_eq_of_ne (fun h : i = j => hj (h ▸ hi)) 1)
  rw [hρ] at hfix
  exact nmh_perm_apply_eq_self_of_mulVec_single hs hfix

private theorem nmhPerm_conj_mem {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {A₀ : Finset (Fin 8)} (hA0 : 0 ∉ A₀) {t d : X} (hd : d * t = t * d)
    (ht : S.ρ t = nmSgn A₀) {m : Equiv.Perm (Fin 8)}
    (hm : m ∈ nmhPerm S (Subgroup.map (MulAut.conj d).toMonoidHom (nmhF2 S A₀)))
    {g : Equiv.Perm (Fin 8)} (hg : ∀ i, i ∉ A₀ → g i = i) :
    g * m * g⁻¹ ∈ nmhPerm S (Subgroup.map (MulAut.conj d).toMonoidHom (nmhF2 S A₀)) := by
  obtain ⟨z, hz, s, hs, hρ⟩ := hm
  have hmem : spMat g (fun _ => (1 : ZMod 3)) ∈ evenAll0 7 :=
    ⟨g, fun _ => 1, fun _ => Or.inl rfl, ⟨hg 0 hA0, by simp⟩, rfl⟩
  obtain ⟨q, hqρ⟩ := S.surj_H1 _ hmem
  have hqQ : q ∈ nmhQ S A₀ := by
    intro v hv
    rw [hqρ, spMat_mulVec]
    funext i
    rw [one_mul]
    show v (g.symm i) = v i
    by_cases hi : i ∈ A₀
    · have hgi : g.symm i ∈ A₀ := by
        by_contra h
        have h1 : g (g.symm i) = g.symm i := hg _ h
        have h2 : g.symm i = i := by simpa using h1.symm
        exact (h2 ▸ h) hi
      exact (hv (g.symm i) hgi).trans (hv i hi).symm
    · have hgi : g.symm i = i := by
        have h1 : g i = i := hg i hi
        calc g.symm i = g.symm (g i) := by rw [h1]
          _ = i := by simp
      rw [hgi]
  have hconj : q * z * q⁻¹ ∈ Subgroup.map (MulAut.conj d).toMonoidHom (nmhF2 S A₀) :=
    nmh_conj_mem_conjF2 S hA0 hd ht hqQ hz
  have hqinv : S.ρ q * S.ρ q⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hg1 : spMat g⁻¹ (fun _ => (1 : ZMod 3)) * spMat g (fun _ => 1) = 1 := by
    rw [spMat_mul, inv_mul_cancel]
    rw [show (fun j => (fun _ => (1 : ZMod 3)) (g j) * 1) = (fun _ => 1) by
      funext j; rw [one_mul], spMat_one]
  have hq'inv : S.ρ q⁻¹ = spMat g⁻¹ (fun _ => (1 : ZMod 3)) := by
    calc S.ρ q⁻¹ = 1 * S.ρ q⁻¹ := by rw [one_mul]
      _ = (spMat g⁻¹ (fun _ => 1) * S.ρ q) * S.ρ q⁻¹ := by rw [hqρ, hg1]
      _ = spMat g⁻¹ (fun _ => 1) * (S.ρ q * S.ρ q⁻¹) := by rw [mul_assoc]
      _ = spMat g⁻¹ (fun _ => 1) * 1 := by rw [hqinv]
      _ = spMat g⁻¹ (fun _ => 1) := mul_one _
  refine ⟨q * z * q⁻¹, hconj, fun j => s (g⁻¹ j), fun j => hs (g⁻¹ j), ?_⟩
  have h1 : S.ρ (q * z * q⁻¹) = spMat g (fun _ => 1) * spMat m s * S.ρ q⁻¹ := by
    rw [map_mul, map_mul, hqρ, hρ]
  rw [h1, hq'inv, spMat_mul, spMat_mul]
  congr 1
  funext j
  simp

private theorem nmhPerm_pow_two {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {A₀ : Finset (Fin 8)} {d : X} {m : Equiv.Perm (Fin 8)}
    (hm : m ∈ nmhPerm S (Subgroup.map (MulAut.conj d).toMonoidHom (nmhF2 S A₀))) :
    m ^ 2 ^ 1 = 1 := by
  obtain ⟨z, hz, s, hs, hρ⟩ := hm
  obtain ⟨f, hf, hfz⟩ := Subgroup.mem_map.mp hz
  have hz_eq : z = d * f * d⁻¹ := by rw [← hfz]; simp [MulAut.conj_apply]
  obtain ⟨B, -, -, hfB⟩ := hf
  have hf2 : f * f = 1 := by
    apply S.ρ_inj
    rw [map_mul, map_one, hfB, nmSgn_mul_self]
  have hz2 : z * z = 1 := by
    rw [hz_eq]
    calc (d * f * d⁻¹) * (d * f * d⁻¹) = d * (f * f) * d⁻¹ := by group
      _ = 1 := by rw [hf2]; group
  have hm2 : m * m = 1 := by
    have hρ2 : S.ρ (z * z) = spMat (m * m) (fun j => s (m j) * s j) := by
      rw [map_mul, hρ, spMat_mul]
    rw [hz2, map_one] at hρ2
    have his : IsSign (fun j => s (m j) * s j) := IsSign.mul (fun j => hs (m j)) hs
    have h1 : spMat (m * m) (fun j => s (m j) * s j) = spMat 1 (fun _ => 1) := by
      rw [← hρ2, spMat_one]
    exact (nm_spMat_inj his (fun _ => Or.inl rfl) h1).1
  simpa [pow_two] using hm2

private theorem nmhPerm_conjF2_eq_bot {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {A₀ : Finset (Fin 8)} (hA0 : 0 ∉ A₀) (hA6 : A₀.card = 6) {t d : X}
    (hd : d * t = t * d) (ht : S.ρ t = nmSgn A₀) :
    nmhPerm S (Subgroup.map (MulAut.conj d).toMonoidHom (nmhF2 S A₀)) = ⊥ := by
  let G : Subgroup X := Subgroup.map (MulAut.conj d).toMonoidHom (nmhF2 S A₀)
  have hGQ : G ≤ nmhQ S A₀ := by
    rintro z ⟨y, hy, hzy⟩
    rw [← hzy]
    simpa [MulAut.conj_apply] using nmh_conj_mem_Q S hd ht (nmhF2_le_Q S hy)
  refine perm_eq_bot_of_normal_of_two_power A₀ (by rw [hA6]; norm_num)
    (M := nmhPerm S G) ?_ ?_ ?_
  · intro m hm j hj
    exact nmhPerm_apply_of_mem S hGQ hm hj
  · intro g hg m hm
    exact nmhPerm_conj_mem S hA0 hd ht hm hg
  · intro m hm
    exact ⟨1, nmhPerm_pow_two S hm⟩

private theorem nmhF2_of_diag {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {A₀ : Finset (Fin 8)} {z : X} {s : Fin 8 → ZMod 3} (hs : IsSign s)
    (hout : ∀ j, j ∉ A₀ → s j = 1) (hprod : (∏ i : Fin 8, s i) = 1)
    (hρ : S.ρ z = spMat 1 s) : z ∈ nmhF2 S A₀ := by
  set B' : Finset (Fin 8) := Finset.univ.filter (fun i => s i = -1) with hB'def
  have hsgn : s = fun i => if i ∈ B' then (-1 : ZMod 3) else 1 := by
    funext i
    by_cases hi : s i = -1
    · have hmem : i ∈ B' := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      rw [if_pos hmem, hi]
    · have hmem : i ∉ B' := fun h => hi (Finset.mem_filter.mp h).2
      rw [if_neg hmem]
      rcases hs i with h | h
      · exact h
      · exact absurd h hi
  have hB'e : Even B'.card := by
    have h1 : (∏ i : Fin 8, s i) = (-1 : ZMod 3) ^ B'.card := by
      rw [hsgn, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
        Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hprod] at h1
    exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1)).mp h1.symm
  have hB'sub : B' ⊆ A₀ := by
    intro i hi
    rw [hB'def] at hi
    have h2 : s i = -1 := (Finset.mem_filter.mp hi).2
    by_contra h
    have h1 : s i = 1 := hout i h
    rw [h1] at h2
    exact absurd h2 (by decide)
  refine ⟨B', hB'sub, hB'e, ?_⟩
  rw [hρ]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [spMat_apply, nmSgn, hsgn]
  · simp [spMat_apply, nmSgn, Matrix.diagonal, hij]

private theorem nmh_exists_diag_of_mem_H1 {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {A₀ : Finset (Fin 8)} (hA0 : 0 ∉ A₀) (hA6 : A₀.card = 6) {a' : X}
    (haH : a' ∈ S.H1grp) (hcommF2 : ∀ f ∈ nmhF2 S A₀, a' * f = f * a') :
    ∃ s : Fin 8 → ZMod 3, IsSign s ∧ (∏ i : Fin 8, s i) = 1 ∧ S.ρ a' = spMat 1 s := by
  obtain ⟨σ, s, hs, ⟨hσ0, hps⟩, hρ⟩ := (S.mem_H1grp a').mp haH
  have hcommPair : ∀ i m : Fin 8, i ∈ A₀ → m ∈ A₀ → i ≠ m →
      spMat σ s * nmSgn ({i, m} : Finset (Fin 8)) =
        nmSgn ({i, m} : Finset (Fin 8)) * spMat σ s := by
    intro i m hi hm him
    have hsub : ({i, m} : Finset (Fin 8)) ⊆ A₀ := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact hi
      · rw [Finset.mem_singleton.mp hz']
        exact hm
    have heven : Even ({i, m} : Finset (Fin 8)).card := by
      rw [Finset.card_pair him]
      exact ⟨1, rfl⟩
    obtain ⟨f, hfρ⟩ := S.exists_of_mem_nmF (nmSgn_mem_nmF heven)
    have hfF2 : f ∈ nmhF2 S A₀ := ⟨{i, m}, hsub, heven, hfρ⟩
    have hmat : S.ρ a' * S.ρ f = S.ρ f * S.ρ a' := by
      have := congrArg S.ρ (hcommF2 f hfF2)
      rwa [map_mul, map_mul] at this
    rw [hρ, hfρ] at hmat
    exact hmat
  have hfixA : ∀ i ∈ A₀, σ i = i := nm_perm_fixes_A0 hs hA6 hcommPair
  have hσ1 : σ = 1 := nm_perm_eq_one_of_fixes hA0 hA6 hσ0 hfixA
  exact ⟨s, hs, hps, by rw [hρ, hσ1]⟩

private theorem nmh_mem_nmF1_of_spMat_one {s : Fin 8 → ZMod 3} (hs : IsSign s) (hs0 : s 0 = 1)
    (hprod : (∏ i : Fin 8, s i) = 1) : spMat (1 : Equiv.Perm (Fin 8)) s ∈ nmF1 := by
  set B : Finset (Fin 8) := Finset.univ.filter (fun i => s i = -1) with hBdef
  have hsgn : s = fun i => if i ∈ B then (-1 : ZMod 3) else 1 := by
    funext i
    by_cases hi : s i = -1
    · have hmem : i ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      rw [if_pos hmem, hi]
    · have hmem : i ∉ B := fun h => hi (Finset.mem_filter.mp h).2
      rw [if_neg hmem]
      rcases hs i with h | h
      · exact h
      · exact absurd h hi
  have hB0 : 0 ∉ B := by
    intro h
    rw [hBdef] at h
    have h1 : s 0 = -1 := (Finset.mem_filter.mp h).2
    rw [hs0] at h1
    exact absurd h1 (by decide)
  have hBe : Even B.card := by
    have h1 : (∏ i : Fin 8, s i) = (-1 : ZMod 3) ^ B.card := by
      rw [hsgn, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
        Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hprod] at h1
    exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1)).mp h1.symm
  refine ⟨B, hB0, hBe, ?_⟩
  rw [← nmh_diagonal_eq_spMat s, hsgn]
  rfl

theorem nm_F2_conj {X : Type} [Group X] [Finite X] (S : N7MSetup X) {A₀ : Finset (Fin 8)}
    (hA0 : 0 ∉ A₀) (hA6 : A₀.card = 6) {t : X} (ht : S.ρ t = nmSgn A₀) {d : X}
    (hd : d * t = t * d)
    {f : X} (hf : ∃ B : Finset (Fin 8), B ⊆ A₀ ∧ Even B.card ∧ S.ρ f = nmSgn B) :
    ∃ B : Finset (Fin 8), B ⊆ A₀ ∧ Even B.card ∧ S.ρ (d * f * d⁻¹) = nmSgn B := by
  obtain ⟨B, hB, hBe, hfB⟩ := hf
  have hfF2 : f ∈ nmhF2 S A₀ := ⟨B, hB, hBe, hfB⟩
  let G : Subgroup X := Subgroup.map (MulAut.conj d).toMonoidHom (nmhF2 S A₀)
  have hfG : d * f * d⁻¹ ∈ G := by
    refine Subgroup.mem_map.mpr ⟨f, hfF2, ?_⟩
    simp [MulAut.conj_apply]
  have hM_bot : nmhPerm S G = ⊥ := nmhPerm_conjF2_eq_bot S hA0 hA6 hd ht
  have hzQ : d * f * d⁻¹ ∈ nmhQ S A₀ := nmh_conj_mem_Q S hd ht (nmhF2_le_Q S hfF2)
  have hz0 : S.ρ (d * f * d⁻¹) *ᵥ nmE0 = nmE0 :=
    hzQ nmE0 (fun i hi => Pi.single_eq_of_ne (fun h : i = 0 => hA0 (h ▸ hi)) 1)
  obtain ⟨m, s, hs, ⟨hm0, hs0, hps⟩, hρm⟩ := (S.fix_iff _).mp hz0
  have hmMem : m ∈ nmhPerm S G := ⟨d * f * d⁻¹, hfG, s, hs, hρm⟩
  have hm1 : m = 1 := by
    rw [hM_bot] at hmMem
    exact Subgroup.mem_bot.mp hmMem
  have hρ1 : S.ρ (d * f * d⁻¹) = spMat 1 s := by rw [hρm, hm1]
  have hout : ∀ j, j ∉ A₀ → s j = 1 := by
    intro j hj
    have hfix : S.ρ (d * f * d⁻¹) *ᵥ (Pi.single j 1 : Coords 8) = Pi.single j 1 :=
      hzQ _ (fun i hi => Pi.single_eq_of_ne (fun h : i = j => hj (h ▸ hi)) 1)
    have hdiag : spMat (1 : Equiv.Perm (Fin 8)) s = Matrix.diagonal s :=
      (nmh_diagonal_eq_spMat s).symm
    rw [hρ1, hdiag] at hfix
    have hval := congrFun hfix j
    rw [Matrix.mulVec_diagonal] at hval
    simpa using hval
  have hprod : (∏ i : Fin 8, s i) = 1 := by
    rw [Fin.prod_univ_succ, hs0, one_mul]
    exact hps
  obtain ⟨B', hB'sub, hB'e, hρB'⟩ := nmhF2_of_diag S hs hout hprod hρ1
  exact ⟨B', hB'sub, hB'e, hρB'⟩

private theorem nmh_a'_comm_F2 {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {A₀ : Finset (Fin 8)} (hA0 : 0 ∉ A₀) (hA6 : A₀.card = 6) {t : X}
    (ht : S.ρ t = nmSgn A₀) {a d : X} (ha : a ∈ S.F1grp) (hd : d * t = t * d) :
    ∀ f ∈ nmhF2 S A₀, (d⁻¹ * a * d) * f = f * (d⁻¹ * a * d) := by
  intro f hf
  have hdfd : d * f * d⁻¹ ∈ nmhF2 S A₀ := nm_F2_conj S hA0 hA6 ht hd hf
  have hdfdF1 : d * f * d⁻¹ ∈ S.F1grp := by
    obtain ⟨B, hB, hBe, hρB⟩ := hdfd
    rw [S.mem_F1grp]
    exact ⟨B, fun h => hA0 (hB h), hBe, hρB⟩
  have hcomm : a * (d * f * d⁻¹) = (d * f * d⁻¹) * a :=
    congrArg Subtype.val
      ((N7MSetup.F1grp_comm S).is_comm.comm ⟨a, ha⟩ ⟨d * f * d⁻¹, hdfdF1⟩)
  calc (d⁻¹ * a * d) * f = d⁻¹ * (a * (d * f * d⁻¹)) * d := by group
    _ = d⁻¹ * ((d * f * d⁻¹) * a) * d := by rw [hcomm]
    _ = f * (d⁻¹ * a * d) := by group

private theorem nmh_nmSgn_mulVec_neg {A : Finset (Fin 8)} {k : Fin 8} (hk : k ∈ A)
    {w : Coords 8} (hsupp : ∀ i, i ≠ k → w i = 0) : nmSgn A *ᵥ w = -w := by
  rw [nmSgn_mulVec]
  funext i
  rw [Pi.neg_apply]
  by_cases hik : i = k
  · subst hik
    rw [if_pos hk]
  · rw [hsupp i hik]
    by_cases hi : i ∈ A
    · rw [if_pos hi]
    · rw [if_neg hi]
      exact neg_zero.symm

private theorem nmh_mulVec_conj {X : Type} [Group X] [Finite X] (S : N7MSetup X) {d t₁ : X}
    {w : Coords 8} (hw : w = S.ρ d⁻¹ *ᵥ nmE0) (hdw : S.ρ d *ᵥ w = nmE0)
    (hneg : S.ρ t₁ *ᵥ w = -w) : S.ρ (d * t₁ * d⁻¹) *ᵥ nmE0 = -nmE0 := by
  calc S.ρ (d * t₁ * d⁻¹) *ᵥ nmE0
      = S.ρ d *ᵥ (S.ρ t₁ *ᵥ (S.ρ d⁻¹ *ᵥ nmE0)) := by
        rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = S.ρ d *ᵥ (-w) := by rw [← hw, hneg]
    _ = -(S.ρ d *ᵥ w) := Matrix.mulVec_neg w (S.ρ d)
    _ = -nmE0 := by rw [hdw]

private theorem nmh_notMem_nmE6_of_mulVec_neg {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {y : X} (hvec : S.ρ y *ᵥ nmE0 = -nmE0) : S.ρ y ∉ nmE6 := by
  rintro ⟨C, hC0, -, hC⟩
  have hfix : S.ρ y *ᵥ nmE0 = nmE0 := by
    rw [hC, nmSgn_mulVec]
    funext i
    by_cases hi : i ∈ C
    · have hi0 : i ≠ 0 := fun h => hC0 (h ▸ hi)
      rw [if_pos hi, nmE0, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hi0 1]
      exact neg_zero
    · rw [if_neg hi]
  rw [hvec] at hfix
  have h0 := congrFun hfix 0
  rw [Pi.neg_apply] at h0
  have h1 : (-1 : ZMod 3) = 1 := by simpa [nmE0] using h0
  exact absurd h1 (by decide)

private theorem nmh_false_of_support {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    (hW : S.Weak) {d : X} {k : Fin 8} (hk0 : k ≠ 0)
    (hsupp : ∀ i, i ≠ k → (S.ρ d⁻¹ *ᵥ nmE0) i = 0) : False := by
  have hcard : ({0, k} : Finset (Fin 8)).card < (Finset.univ : Finset (Fin 8)).card := by
    rw [Finset.card_pair (Ne.symm hk0), Finset.card_univ, Fintype.card_fin]
    decide
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hj0 : j ≠ 0 := fun h => hj (h ▸ by simp)
  have hjk : j ≠ k := fun h => hj (h ▸ by simp)
  let A₁ : Finset (Fin 8) := Finset.univ \ {0, j}
  have hA1card : A₁.card = 6 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_pair hj0.symm]
  have hA10 : 0 ∉ A₁ := by
    rw [Finset.mem_sdiff]
    intro h
    exact h.2 (by simp)
  have hkA1 : k ∈ A₁ := by
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ k, by simp [hk0, Ne.symm hjk]⟩
  have hA1even : Even A₁.card := by rw [hA1card]; exact ⟨3, rfl⟩
  obtain ⟨t₁, ht₁⟩ := S.exists_of_mem_nmF (nmSgn_mem_nmF hA1even)
  have ht₁E6 : S.ρ t₁ ∈ nmE6 := ⟨A₁, hA10, hA1card, ht₁⟩
  set w : Coords 8 := S.ρ d⁻¹ *ᵥ nmE0 with hwdef
  have hdw : S.ρ d *ᵥ w = nmE0 := by
    rw [hwdef, Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
  have hneg : S.ρ t₁ *ᵥ w = -w := by
    rw [ht₁]
    exact nmh_nmSgn_mulVec_neg hkA1 hsupp
  have hvec : S.ρ (d * t₁ * d⁻¹) *ᵥ nmE0 = -nmE0 :=
    nmh_mulVec_conj S hwdef hdw hneg
  have hmem : S.ρ (d * t₁ * d⁻¹) ∈ evenAll0 7 := by
    refine (S.norm_iff _).mp ⟨-1, ?_⟩
    rw [hvec]
    funext i
    rw [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    exact (neg_one_mul (nmE0 i)).symm
  exact nmh_notMem_nmE6_of_mulVec_neg S hvec (hW t₁ d ht₁E6 hmem)

private theorem nmh_false_of_gap {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    (hW : S.Weak) {A₀ : Finset (Fin 8)} (hA0 : 0 ∉ A₀) (hA6 : A₀.card = 6) {d : X}
    {w : Coords 8} (hw : w = S.ρ d⁻¹ *ᵥ nmE0)
    (hvan : ∀ i ∈ A₀, w i = 0) (hw0 : w 0 = 0) : False := by
  have hcard : (Finset.univ \ insert 0 A₀).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_insert_of_notMem hA0,
      Finset.card_univ, Fintype.card_fin, hA6]
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
  have hk0 : k ≠ 0 := by
    intro h
    have hk' : k ∈ Finset.univ \ insert 0 A₀ := by rw [hk]; simp
    exact (Finset.mem_sdiff.mp hk').2 (by simp [h])
  have huniq : ∀ i, i ∉ A₀ → i ≠ 0 → i = k := by
    intro i hi hi0
    have hi' : i ∈ Finset.univ \ insert 0 A₀ :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ i,
        fun h => (Finset.mem_insert.mp h).elim hi0 hi⟩
    rw [hk] at hi'
    exact Finset.mem_singleton.mp hi'
  have hsupp : ∀ i, i ≠ k → (S.ρ d⁻¹ *ᵥ nmE0) i = 0 := by
    intro i hik
    rw [← hw]
    by_cases hiA : i ∈ A₀
    · exact hvan i hiA
    · by_cases hi0 : i = 0
      · rw [hi0]; exact hw0
      · exact absurd (huniq i hiA hi0) hik
  exact nmh_false_of_support S hW hk0 hsupp

theorem nm_strong_D {X : Type} [Group X] [Finite X] (S : N7MSetup X) (hW : S.Weak) {t : X}
    (ht : S.ρ t ∈ nmE6) {a : X} (ha : a ∈ S.F1grp) {d : X} (hd : d * t = t * d)
    {P : Subgroup X} (hP : P ≤ S.H1grp) (hPd : d⁻¹ * a * d ∈ P) : d⁻¹ * a * d ∈ S.F1grp := by
  obtain ⟨A₀, hA0, hA6, htA⟩ := ht
  have ha'H : d⁻¹ * a * d ∈ S.H1grp := hP hPd
  have hcommF2 := nmh_a'_comm_F2 S hA0 hA6 htA ha hd
  obtain ⟨s, hs, hprod, hρ1⟩ := nmh_exists_diag_of_mem_H1 S hA0 hA6 ha'H hcommF2
  have hae0 : S.ρ a *ᵥ nmE0 = nmE0 := by
    obtain ⟨B, hB0, -, hρa⟩ := (S.mem_F1grp a).mp ha
    rw [hρa, nmSgn_mulVec]
    funext i
    by_cases hi : i ∈ B
    · have hi0 : i ≠ 0 := fun h => hB0 (h ▸ hi)
      rw [if_pos hi, nmE0, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hi0 1]
      exact neg_zero
    · rw [if_neg hi]
  set w : Coords 8 := S.ρ d⁻¹ *ᵥ nmE0 with hwdef
  have hdw : S.ρ d *ᵥ w = nmE0 := by
    rw [hwdef, Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
  have hfixw : S.ρ (d⁻¹ * a * d) *ᵥ w = w := by
    have h1 : S.ρ (d⁻¹ * a * d) *ᵥ w = S.ρ d⁻¹ *ᵥ (S.ρ a *ᵥ (S.ρ d *ᵥ w)) := by
      rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [h1, hdw, hae0, hwdef]
  have hfixw' : Matrix.diagonal s *ᵥ w = w := by
    rw [nmh_diagonal_eq_spMat s, ← hρ1]
    exact hfixw
  have hw0eq : s 0 * w 0 = w 0 := by
    have h := congrFun hfixw' 0
    rwa [Matrix.mulVec_diagonal] at h
  by_cases hw0 : w 0 = 0
  · have hvan : ∀ i ∈ A₀, w i = 0 := by
      rw [hwdef]
      refine nmh_vanishes_mulVec_of_comm S (Commute.inv_left hd).eq htA (v := nmE0) ?_
      intro i hi
      rw [nmE0]
      exact Pi.single_eq_of_ne (M := fun _ => ZMod 3)
        (fun h : i = 0 => hA0 (h ▸ hi)) 1
    exact (nmh_false_of_gap S hW hA0 hA6 hwdef hvan hw0).elim
  · have hs0 : s 0 = 1 :=
      mul_right_cancel₀ hw0 (by rw [one_mul]; exact hw0eq)
    rw [S.mem_F1grp, hρ1]
    exact nmh_mem_nmF1_of_spMat_one hs hs0 hprod

end CFSG.StandardType.FrameRoute.FS81

end

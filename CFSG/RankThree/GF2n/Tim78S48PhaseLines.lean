module

public import CFSG.RankThree.GF2n.Tim78S48PhaseSwap

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open Matrix
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

theorem exists_sl2_apply_eq {F : Type} [Field F] {v : Fin 2 → F} (hv : v ≠ 0) :
    ∃ P : SL(2, F), (P : Matrix (Fin 2) (Fin 2) F) *ᵥ v = ![1, 0] := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i
      · exact h0
      · exact h1
    refine ⟨⟨!![0, (v 1)⁻¹; -(v 1), 0], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h1]
    · ext i
      fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h1]
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![(v 0)⁻¹, 0; -(v 1), v 0], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h0]
    · ext i
      fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        ring

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H

section Lines

variable {F : Type} [Field F]

theorem exists_conj_of_ne_one (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTK : ∃ t ∈ T, t ∉ kernel48 B T g) {D : L2Coords B T g F} {Θ : (Fin 2 → F) → G}
    (N : IsNatCoords D Θ) {w : G} (hw : w ∈ B ⊔ conjSubgroup g B) (hw1 : w ≠ 1) :
    ∃ y ∈ T ⊔ conjSubgroup g T, w ∈ conjSubgroup y B := by
  obtain ⟨v, rfl⟩ := N.surj w hw
  have hv : v ≠ 0 := fun h => hw1 (by rw [h]; exact N.zero)
  obtain ⟨P, hPv⟩ := exists_sl2_apply_eq hv
  obtain ⟨z, hz⟩ := D.surj P
  refine ⟨(z : G)⁻¹, (T ⊔ conjSubgroup g T).inv_mem z.2, ?_⟩
  rw [mem_conjSubgroup, inv_inv]
  have h := N.conj z v
  rw [hz, hPv] at h
  rw [h]
  exact H.Θ_mem_B h48 hP hTK N 1

theorem conj_mem_classIn (h48 : Hyp48 M B T g) {y : G} (hy : y ∈ T ⊔ conjSubgroup g T) :
    conjSubgroup y B ∈ classIn B (B ⊔ conjSubgroup g B) := by
  refine ⟨⟨y, rfl⟩, fun x hx => ?_⟩
  rw [mem_conjSubgroup] at hx
  have hxW : y * (y⁻¹ * x * y) * y⁻¹ ∈ B ⊔ conjSubgroup g B :=
    (Subgroup.mem_normalizer_iff.mp (H.X_le_normalizer_W h48 hy) _).mp (Subgroup.mem_sup_left hx)
  rwa [show y * (y⁻¹ * x * y) * y⁻¹ = x by group] at hxW

theorem partition_W (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTK : ∃ t ∈ T, t ∉ kernel48 B T g) {D : L2Coords B T g F} {Θ : (Fin 2 → F) → G}
    (N : IsNatCoords D Θ) :
    ∀ w ∈ B ⊔ conjSubgroup g B, w ≠ 1 →
      ∃! U, U ∈ classIn B (B ⊔ conjSubgroup g B) ∧ w ∈ U := by
  intro w hw hw1
  obtain ⟨y, hy, hwy⟩ := H.exists_conj_of_ne_one h48 hP hTK N hw hw1
  refine ⟨conjSubgroup y B, ⟨H.conj_mem_classIn h48 hy, hwy⟩, ?_⟩
  rintro U ⟨⟨⟨z, rfl⟩, -⟩, hwU⟩
  refine H.conj_B_eq_of_inf_ne_bot fun hbot => hw1 ?_
  have : w ∈ conjSubgroup z B ⊓ conjSubgroup y B := ⟨hwU, hwy⟩
  rwa [hbot, Subgroup.mem_bot] at this

theorem trans_W (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTK : ∃ t ∈ T, t ∉ kernel48 B T g) {D : L2Coords B T g F} {Θ : (Fin 2 → F) → G}
    (N : IsNatCoords D Θ) :
    ∀ U ∈ classIn B (B ⊔ conjSubgroup g B), ∃ h ∈ T ⊔ conjSubgroup g T,
      U = conjSubgroup h B := by
  rintro U ⟨⟨z, rfl⟩, hUW⟩
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp H.B_ne_bot
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hu : z * b * z⁻¹ ∈ conjSubgroup z B := by
    rw [mem_conjSubgroup, show z⁻¹ * (z * b * z⁻¹) * z = b by group]
    exact hb
  have hu1 : z * b * z⁻¹ ≠ 1 := fun h => hb1' (by
    calc b = z⁻¹ * (z * b * z⁻¹) * z := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨y, hy, huy⟩ := H.exists_conj_of_ne_one h48 hP hTK N (hUW hu) hu1
  refine ⟨y, hy, H.conj_B_eq_of_inf_ne_bot fun hbot => hu1 ?_⟩
  have : z * b * z⁻¹ ∈ conjSubgroup z B ⊓ conjSubgroup y B := ⟨hu, huy⟩
  rwa [hbot, Subgroup.mem_bot] at this

omit H in
theorem torus_param {D : L2Coords B T g F} {K₁ : Subgroup G} (hK₁ : IsTorusLift D K₁) {k : G}
    (hk : k ∈ K₁) (hk1 : k ≠ 1) :
    ∃ c : Fˣ, (c : F) ≠ 1 ∧ D.ε ⟨k, hK₁.le_X hk⟩ = torusElt c := by
  obtain ⟨c, hc⟩ := mem_torus_iff.mp (hK₁.eps_mem ⟨k, hK₁.le_X hk⟩ hk)
  refine ⟨c, fun h1 => hk1 ?_, hc⟩
  have h2 : D.ε ⟨k, hK₁.le_X hk⟩ = 1 := by
    rw [hc, show c = 1 from Units.ext h1]
    exact map_one (CFSG.Glauberman.Dickson.splitTorusSLHom F)
  have h3 : k ∈ K₁ ⊓ kernel48 B T g := ⟨hk, (D.ker_iff _).mp h2⟩
  rw [hK₁.inf_ker, Subgroup.mem_bot] at h3
  exact h3

theorem K₁_regular (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTK : ∃ t ∈ T, t ∉ kernel48 B T g) {D : L2Coords B T g F} {Θ : (Fin 2 → F) → G}
    (N : IsNatCoords D Θ) {K₁ : Subgroup G} (hK₁ : IsTorusLift D K₁) :
    ∀ x ∈ K₁, x ≠ 1 → ∀ b ∈ B, x * b * x⁻¹ = b → b = 1 := by
  intro x hx hx1 b hb hxb
  obtain ⟨c, hc1, hc⟩ := torus_param hK₁ hx hx1
  obtain ⟨t, rfl⟩ := H.exists_Θ_B N hb
  have h := N.conj ⟨x, hK₁.le_X hx⟩ ![t, 0]
  rw [hc, torusElt_mulVec] at h
  change x * Θ ![t, 0] * x⁻¹ = _ at h
  rw [hxb] at h
  have h3 := N.inj h
  have h4 : t = (c : F) * t := by simpa using congrFun h3 0
  have ht : t = 0 := by
    by_contra ht
    exact hc1 (mul_right_cancel₀ ht (by rw [one_mul]; exact h4.symm))
  have hz : (![t, 0] : Fin 2 → F) = 0 := by
    ext i; fin_cases i
    · exact ht
    · rfl
  rw [hz]
  exact N.zero

theorem eq_of_normalized [CharP F 2] (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTK : ∃ t ∈ T, t ∉ kernel48 B T g) (hTgK : ∃ t ∈ conjSubgroup g T, t ∉ kernel48 B T g)
    {D : L2Coords B T g F} {Θ : (Fin 2 → F) → G} (N : IsNatCoords D Θ) {K₁ : Subgroup G}
    (hK₁ : IsTorusLift D K₁) (hK₁ne : K₁ ≠ ⊥) :
    ∀ U ∈ classIn B (B ⊔ conjSubgroup g B), (∀ k ∈ K₁, conjSubgroup k U = U) →
      U = B ∨ U = conjSubgroup g B := by
  intro U hU hK
  obtain ⟨y, hy, rfl⟩ := H.trans_W h48 hP hTK N U hU
  obtain ⟨⟨k, hk⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK₁ne
  have hk1' : k ≠ 1 := fun h => hk1 (Subtype.ext h)
  obtain ⟨c, hc1, hc⟩ := torus_param hK₁ hk hk1'
  have hΘ1 : Θ ![1, 0] ∈ B := H.Θ_mem_B h48 hP hTK N 1
  have huU : y * Θ ![1, 0] * y⁻¹ ∈ conjSubgroup y B := mul_mul_inv_mem_conjSubgroup y hΘ1
  obtain ⟨m, hmdef⟩ : ∃ m : Fin 2 → F,
      m = (D.ε ⟨y, hy⟩ : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] := ⟨_, rfl⟩
  have hum : y * Θ ![1, 0] * y⁻¹ = Θ m := by
    rw [hmdef]; exact N.conj ⟨y, hy⟩ ![1, 0]
  obtain ⟨m0, m1, rfl⟩ : ∃ m0 m1 : F, m = ![m0, m1] :=
    ⟨m 0, m 1, by ext i; fin_cases i <;> rfl⟩
  have hu1 : Θ ![m0, m1] ≠ 1 := by
    intro h
    rw [← hum] at h
    have h1 : Θ ![1, 0] = 1 := by
      calc Θ ![1, 0] = y⁻¹ * (y * Θ ![1, 0] * y⁻¹) * y := by group
        _ = 1 := by rw [h]; group
    have h2 := N.inj (h1.trans N.zero.symm)
    have := congrFun h2 0
    simp at this
  have huy : Θ ![m0, m1] ∈ conjSubgroup y B := hum ▸ huU
  have hkU : k * Θ ![m0, m1] * k⁻¹ ∈ conjSubgroup y B := by
    have := mul_mul_inv_mem_conjSubgroup k huy
    rwa [hK k hk] at this
  have hk2 := N.conj ⟨k, hK₁.le_X hk⟩ ![m0, m1]
  rw [hc, torusElt_mulVec] at hk2
  change k * Θ ![m0, m1] * k⁻¹ = _ at hk2
  rw [hk2, mem_conjSubgroup] at hkU
  obtain ⟨x, hx⟩ := H.exists_Θ_B N hkU
  have hx2 : y * Θ ![x, 0] * y⁻¹ = Θ ((D.ε ⟨y, hy⟩ : Matrix (Fin 2) (Fin 2) F) *ᵥ ![x, 0]) :=
    N.conj ⟨y, hy⟩ ![x, 0]
  have hx3 : Θ ![(c : F) * m0, ((c⁻¹ : Fˣ) : F) * m1] =
      Θ ((D.ε ⟨y, hy⟩ : Matrix (Fin 2) (Fin 2) F) *ᵥ ![x, 0]) := by
    rw [← hx2, hx]; group
  have hMx : (D.ε ⟨y, hy⟩ : Matrix (Fin 2) (Fin 2) F) *ᵥ ![x, 0] = ![x * m0, x * m1] := by
    have e : (![x, 0] : Fin 2 → F) = x • ![1, 0] := by ext i; fin_cases i <;> simp
    rw [e, Matrix.mulVec_smul, ← hmdef]
    ext i; fin_cases i <;> simp
  have hx4 := N.inj hx3
  rw [hMx] at hx4
  have hxa : (c : F) * m0 = x * m0 := by simpa using congrFun hx4 0
  have hxb : ((c⁻¹ : Fˣ) : F) * m1 = x * m1 := by simpa using congrFun hx4 1
  by_cases h0 : m0 = 0
  · right
    have hmem : Θ ![m0, m1] ∈ conjSubgroup g B := by
      rw [h0]; exact H.Θ_mem_Bg h48 hP hTgK N m1
    refine H.conj_B_eq_of_inf_ne_bot fun hbot => hu1 ?_
    have : Θ ![m0, m1] ∈ conjSubgroup y B ⊓ conjSubgroup g B := ⟨huy, hmem⟩
    rwa [hbot, Subgroup.mem_bot] at this
  by_cases h1 : m1 = 0
  · left
    have hmem : Θ ![m0, m1] ∈ B := by
      rw [h1]; exact H.Θ_mem_B h48 hP hTK N m0
    have := H.conj_B_eq_of_inf_ne_bot (z := y) (z' := 1) fun hbot => hu1 (by
      have h3 : Θ ![m0, m1] ∈ conjSubgroup y B ⊓ conjSubgroup 1 B := by
        rw [conjSubgroup_one]; exact ⟨huy, hmem⟩
      rwa [hbot, Subgroup.mem_bot] at h3)
    rwa [conjSubgroup_one] at this
  · exfalso
    have hcx : (c : F) = x := mul_right_cancel₀ h0 hxa
    have hcx' : ((c⁻¹ : Fˣ) : F) = x := mul_right_cancel₀ h1 hxb
    have hceq : (c : F) = ((c⁻¹ : Fˣ) : F) := hcx.trans hcx'.symm
    have hcc : (c : F) * (c : F) = 1 := by
      calc (c : F) * (c : F) = (c : F) * ((c⁻¹ : Fˣ) : F) := by rw [← hceq]
        _ = 1 := Units.mul_inv c
    exact hc1 (eq_one_of_sq_eq_one_char_two (by rw [sq]; exact hcc))

theorem induces_natural {f : ℕ} {D : L2Coords B T g (GaloisField 2 f)}
    {Θ : (Fin 2 → GaloisField 2 f) → G} (N : IsNatCoords D Θ) :
    InducesNaturalSL2 f (T ⊔ conjSubgroup g T) (B ⊔ conjSubgroup g B) := by
  let ψ₀ : Multiplicative (Fin 2 → GaloisField 2 f) →* ↥(B ⊔ conjSubgroup g B) :=
    { toFun := fun v => ⟨Θ (Multiplicative.toAdd v), N.mem _⟩
      map_one' := Subtype.ext N.zero
      map_mul' := fun v v' => Subtype.ext (N.mul _ _) }
  have hψ₀ : Function.Bijective ψ₀ := by
    refine ⟨fun v v' h => Multiplicative.toAdd.injective (N.inj (congrArg Subtype.val h)), ?_⟩
    rintro ⟨w, hw⟩
    obtain ⟨v, hv⟩ := N.surj w hw
    exact ⟨Multiplicative.ofAdd v, Subtype.ext hv⟩
  unfold InducesNaturalSL2
  refine ⟨D.ε, (MulEquiv.ofBijective ψ₀ hψ₀).symm, D.surj, ?_, ?_⟩
  · rw [D.ker]
    exact Subgroup.inf_subgroupOf_left _ _
  · intro z w w' hww'
    set e := MulEquiv.ofBijective ψ₀ hψ₀ with he
    have hw : e (e.symm w) = w := e.apply_symm_apply w
    have hwv : (w : G) = Θ (Multiplicative.toAdd (e.symm w)) := by
      have := congrArg Subtype.val hw
      exact this.symm
    have hw' : (w' : G) = Θ ((D.ε z : Matrix (Fin 2) (Fin 2) _) *ᵥ
        Multiplicative.toAdd (e.symm w)) := by
      rw [hww', hwv]
      exact N.conj z _
    have h1 : e.symm w' = Multiplicative.ofAdd ((D.ε z : Matrix (Fin 2) (Fin 2) _) *ᵥ
        Multiplicative.toAdd (e.symm w)) := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      exact hw'
    rw [h1]
    rfl

end Lines

end Hyp4

end CFSG.RankThree.GF2n.Tim78

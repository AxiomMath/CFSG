module

public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.RankThree.GF2n

open Module Polynomial

theorem add_self_eq_zero_of_charTwo (K : Type*) {V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] (v : V) : v + v = 0 := by
  rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_map_add_finrank_inf_ker (f : V →ₗ[K] V) (P : Submodule K V) :
    finrank K (P.map f) + finrank K ↥(P ⊓ LinearMap.ker f) = finrank K P := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict P)
  rw [LinearMap.range_domRestrict] at h
  have hk : LinearMap.ker (f.domRestrict P) = (LinearMap.ker f).comap P.subtype := by
    ext x
    simp
  rw [hk, ← Submodule.finrank_map_subtype_eq P, Submodule.map_comap_subtype] at h
  exact h

variable [CharP K 2]


omit [FiniteDimensional K V] [CharP K 2] in
theorem apply_apply_of_mul_self {a : End K V} (ha : a * a = 1) (v : V) : a (a v) = v := by
  have := congrArg (fun f : End K V => f v) ha
  simpa using this

omit [FiniteDimensional K V] in
theorem sub_one_apply_sub_one_apply {a : End K V} (ha : a * a = 1) (v : V) :
    (a - 1) ((a - 1) v) = 0 := by
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, apply_apply_of_mul_self ha]
  calc v - a v - (a v - v) = (v + v) - (a v + a v) := by abel
    _ = 0 := by rw [add_self_eq_zero_of_charTwo K, add_self_eq_zero_of_charTwo K, sub_zero]

omit [FiniteDimensional K V] [CharP K 2] in
theorem mem_ker_sub_one {a : End K V} {v : V} : v ∈ LinearMap.ker (a - 1) ↔ a v = v := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

theorem finrank_le_two_mul_finrank_inf_ker {a : End K V} (ha : a * a = 1) {P : Submodule K V}
    (hP : P ≤ P.comap a) : finrank K P ≤ 2 * finrank K ↥(P ⊓ LinearMap.ker (a - 1)) := by
  have h := finrank_map_add_finrank_inf_ker (a - 1) P
  have hle : P.map (a - 1) ≤ P ⊓ LinearMap.ker (a - 1) := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨?_, ?_⟩
    · show (a - 1) v ∈ P
      rw [LinearMap.sub_apply, Module.End.one_apply]
      exact P.sub_mem (hP hv) hv
    · exact sub_one_apply_sub_one_apply ha v
  have := Submodule.finrank_mono hle
  omega

theorem dihedral_split {a b : End K V} (ha : a * a = 1) (hb : b * b = 1)
    (hfix : ∀ v, a v = v → b v = v → v = 0) {P : Submodule K V} (hPa : P ≤ P.comap a)
    (hPb : P ≤ P.comap b) :
    finrank K P = 2 * finrank K ↥(P ⊓ LinearMap.ker (a - 1)) ∧
      finrank K P = 2 * finrank K ↥(P ⊓ LinearMap.ker (b - 1)) ∧
      (P ⊓ LinearMap.ker (a - 1)) ⊔ (P ⊓ LinearMap.ker (b - 1)) = P := by
  have h1 := finrank_le_two_mul_finrank_inf_ker ha hPa
  have h2 := finrank_le_two_mul_finrank_inf_ker hb hPb
  have hdis : (P ⊓ LinearMap.ker (a - 1)) ⊓ (P ⊓ LinearMap.ker (b - 1)) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨-, hva⟩, ⟨-, hvb⟩⟩
    exact (Submodule.mem_bot K).mpr (hfix v (mem_ker_sub_one.mp hva) (mem_ker_sub_one.mp hvb))
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (P ⊓ LinearMap.ker (a - 1))
    (P ⊓ LinearMap.ker (b - 1))
  rw [hdis, finrank_bot, add_zero] at h3
  have hle : (P ⊓ LinearMap.ker (a - 1)) ⊔ (P ⊓ LinearMap.ker (b - 1)) ≤ P :=
    sup_le inf_le_left inf_le_left
  have h4 := Submodule.finrank_mono hle
  refine ⟨by omega, by omega, Submodule.eq_of_le_of_finrank_eq hle (by omega)⟩

omit [FiniteDimensional K V] in
theorem isSemisimple_of_pow_eq_one {c : End K V} {k : ℕ} (hk : Odd k) (hc : c ^ k = 1) :
    c.IsSemisimple := by
  have hk0 : (k : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    exact fun h => (Nat.not_even_iff_odd.mpr hk) (even_iff_two_dvd.mpr h)
  have hsep : (X ^ k - C (1 : K)).Separable := separable_X_pow_sub_C 1 hk0 one_ne_zero
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree ?_
  simp [hc]

theorem exists_isCompl_of_dihedral {a b : End K V} (ha : a * a = 1) (hb : b * b = 1)
    {k : ℕ} (hk : Odd k) (hab : (a * b) ^ k = 1) (hfix : ∀ v, a v = v → b v = v → v = 0)
    {U : Submodule K V} (hUa : U ≤ U.comap a) (hUb : U ≤ U.comap b) :
    ∃ W : Submodule K V, W ≤ W.comap a ∧ W ≤ W.comap b ∧ IsCompl U W := by
  obtain ⟨La, hLa⟩ : ∃ L : Submodule K V, L = LinearMap.ker (a - 1) := ⟨_, rfl⟩
  obtain ⟨Lb, hLb⟩ : ∃ L : Submodule K V, L = LinearMap.ker (b - 1) := ⟨_, rfl⟩
  have hmLa : ∀ v, v ∈ La ↔ a v = v := fun v => by rw [hLa, mem_ker_sub_one]
  have hmLb : ∀ v, v ∈ Lb ↔ b v = v := fun v => by rw [hLb, mem_ker_sub_one]
  have htop : (⊤ : Submodule K V) ≤ (⊤ : Submodule K V).comap a := fun _ _ => trivial
  have htop' : (⊤ : Submodule K V) ≤ (⊤ : Submodule K V).comap b := fun _ _ => trivial
  obtain ⟨hV1, hV2, hV3⟩ := dihedral_split ha hb hfix htop htop'
  rw [top_inf_eq, finrank_top, ← hLa] at hV1
  rw [top_inf_eq, finrank_top, ← hLb] at hV2
  rw [top_inf_eq, top_inf_eq, ← hLa, ← hLb] at hV3
  obtain ⟨hU1, -, -⟩ := dihedral_split ha hb hfix hUa hUb
  rw [← hLa] at hU1
  have hβLb : ∀ v, (b - 1) v ∈ Lb := fun v => by
    rw [hLb]
    exact LinearMap.mem_ker.mpr (sub_one_apply_sub_one_apply hb v)
  have hrange : LinearMap.range (b - 1) = Lb := by
    have hle : LinearMap.range (b - 1) ≤ Lb := by
      rintro _ ⟨v, rfl⟩
      exact hβLb v
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    have := LinearMap.finrank_range_add_finrank_ker (b - 1)
    rw [← hLb] at this
    omega
  have hβL : La.map (b - 1) = Lb := by
    have h0 : Lb.map (b - 1) = ⊥ := le_antisymm
      (by
        rintro _ ⟨v, hv, rfl⟩
        rw [LinearMap.sub_apply, Module.End.one_apply, (hmLb v).mp hv, sub_self]
        exact Submodule.zero_mem _) bot_le
    rw [← hrange, LinearMap.range_eq_map, ← hV3, Submodule.map_sup, h0, sup_bot_eq]
  have hcba : (a * b) * (b * a) = 1 := by
    rw [mul_assoc, ← mul_assoc b b a, hb, one_mul, ha]
  have hck1 : (a * b) ^ (k - 1) = b * a := by
    have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk.pos
    calc (a * b) ^ (k - 1) = (a * b) ^ (k - 1) * ((a * b) * (b * a)) := by rw [hcba, mul_one]
      _ = (a * b) ^ (k - 1 + 1) * (b * a) := by rw [pow_succ]; simp only [mul_assoc]
      _ = b * a := by rw [hk1, hab, one_mul]
  obtain ⟨d, hd⟩ : ∃ d : End K V, d = a * b + b * a := ⟨_, rfl⟩
  have hds : d.IsSemisimple := by
    have := (isSemisimple_of_pow_eq_one hk hab).aeval (X + X ^ (k - 1))
    simpa [hck1, hd] using this
  have hdL : ∀ x ∈ La, d x = (a - 1) ((b - 1) x) := by
    intro x hx
    have hax : a x = x := (hmLa x).mp hx
    simp only [hd, LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_sub, hax]
    calc a (b x) + b x = a (b x) - b x + (b x + b x) := by abel
      _ = a (b x) - b x := by rw [add_self_eq_zero_of_charTwo K, add_zero]
      _ = a (b x) - b x - (x - x) := by rw [sub_self, sub_zero]
  have hLd : ∀ x ∈ La, d x ∈ La := fun x hx => by
    rw [hdL x hx, hLa]
    exact LinearMap.mem_ker.mpr (sub_one_apply_sub_one_apply ha _)
  have hUd : ∀ x ∈ U, d x ∈ U := fun x hx => by
    rw [hd]
    exact U.add_mem (hUa (hUb hx)) (hUb (hUa hx))
  have hU₁d : U ⊓ La ∈ d.invtSubmodule := by
    rw [Module.End.mem_invtSubmodule]
    exact fun x hx => ⟨hUd x hx.1, hLd x hx.2⟩
  obtain ⟨W', hW'd, hcompl⟩ := (Module.End.isSemisimple_iff.mp hds) _ hU₁d
  rw [Module.End.mem_invtSubmodule] at hW'd
  obtain ⟨W₁, hW₁⟩ : ∃ W : Submodule K V, W = W' ⊓ La := ⟨_, rfl⟩
  have hW₁L : W₁ ≤ La := hW₁ ▸ inf_le_right
  have hW₁d : ∀ w ∈ W₁, d w ∈ W₁ := fun w hw => by
    rw [hW₁] at hw ⊢
    exact ⟨hW'd hw.1, hLd w hw.2⟩
  have hU₁W₁ : U ⊓ La ⊔ W₁ = La := by
    rw [hW₁, ← sup_inf_assoc_of_le W' (inf_le_right : U ⊓ La ≤ La), hcompl.sup_eq_top,
      top_inf_eq]
  have hU₁W₁' : U ⊓ La ⊓ W₁ = ⊥ := by
    rw [hW₁]
    exact le_bot_iff.mp ((inf_le_inf_left _ inf_le_left).trans hcompl.inf_eq_bot.le)
  obtain ⟨W, hW⟩ : ∃ W : Submodule K V, W = W₁ ⊔ W₁.map (b - 1) := ⟨_, rfl⟩
  have hW₁W : W₁ ≤ W := hW ▸ le_sup_left
  have hβW : ∀ w ∈ W₁, (b - 1) w ∈ W := fun w hw => hW ▸ Submodule.mem_sup_right ⟨w, hw, rfl⟩
  have hβ : ∀ v, b v = v + (b - 1) v := fun v => by
    rw [LinearMap.sub_apply, Module.End.one_apply]; abel
  have hα : ∀ v, a v = v + (a - 1) v := fun v => by
    rw [LinearMap.sub_apply, Module.End.one_apply]; abel
  have hWa : W ≤ W.comap a := by
    rw [hW]
    refine sup_le (fun w hw => ?_) ?_
    · rw [Submodule.mem_comap, (hmLa w).mp (hW₁L hw), ← hW]
      exact hW₁W hw
    · rintro _ ⟨w, hw, rfl⟩
      rw [Submodule.mem_comap, hα, ← hdL w (hW₁L hw), ← hW]
      exact W.add_mem (hβW w hw) (hW₁W (hW₁d w hw))
  have hWb : W ≤ W.comap b := by
    rw [hW]
    refine sup_le (fun w hw => ?_) ?_
    · rw [Submodule.mem_comap, hβ, ← hW]
      exact W.add_mem (hW₁W hw) (hβW w hw)
    · rintro _ ⟨w, hw, rfl⟩
      rw [Submodule.mem_comap, hβ, sub_one_apply_sub_one_apply hb, add_zero, ← hW]
      exact hβW w hw
  have hsup : U ⊔ W = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hV3]
    refine sup_le ?_ ?_
    · rw [← hU₁W₁]
      exact sup_le_sup inf_le_left hW₁W
    · rw [← hβL, ← hU₁W₁, Submodule.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨u, hu, rfl⟩
        rw [LinearMap.sub_apply, Module.End.one_apply]
        exact U.sub_mem (hUb hu.1) hu.1
      · rintro _ ⟨w, hw, rfl⟩
        exact hβW w hw
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ La) W₁
  rw [hU₁W₁, hU₁W₁', finrank_bot, add_zero] at h1
  have h2 : finrank K W ≤ finrank K W₁ + finrank K ↥(W₁.map (b - 1)) := by
    rw [hW]
    exact Submodule.finrank_add_le_finrank_add_finrank _ _
  have h3 := Submodule.finrank_map_le (b - 1) W₁
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [hsup, finrank_top] at h4
  exact ⟨W, hWa, hWb, IsCompl.of_eq (Submodule.finrank_eq_zero.mp (by omega)) hsup⟩

end CFSG.RankThree.GF2n

module

public import CFSG.Quasithin.Background.SmithB45Alt7Res

public section

namespace CFSG.Quasithin.A7Q528

open CFSG.Quasithin.B45Alt7

section Gen

variable {Γ : Type} [Group Γ] {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
  {ρ : Representation (ZMod 2) Γ M} {U : Submodule (ZMod 2) M}

theorem add_self_eq_zero₂ (v : M) : v + v = 0 := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  rw [← one_smul (ZMod 2) v, ← add_smul, h, zero_smul]

theorem fpf_conj (hinv : ∀ g, ∀ u ∈ U, ρ g u ∈ U) {s : Γ} (hs : ∀ v, ρ s v - v ∈ U → v ∈ U)
    (g : Γ) : ∀ v, ρ (g * s * g⁻¹) v - v ∈ U → v ∈ U := by
  intro v hv
  have h1 := hinv g⁻¹ _ hv
  have e : ρ g⁻¹ (ρ (g * s * g⁻¹) v) = ρ s (ρ g⁻¹ v) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  rw [map_sub, e] at h1
  have h2 := hinv g _ (hs _ h1)
  rwa [Representation.self_inv_apply] at h2

theorem sub_eq_zero_of_mem (hU : ∀ g, ∀ u ∈ U, ρ g u = u) {s : Γ} (hs3 : s ^ 3 = 1) {v : M}
    (hv : ρ s v - v ∈ U) : ρ s v - v = 0 := by
  set c := ρ s v - v with hcdef
  have hc : ρ s c = c := hU s c hv
  have e1 : ρ s v = v + c := by rw [hcdef]; abel
  have e3 : ρ (s * (s * s)) v = v + c + c + c := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e1, map_add, e1, hc,
      map_add, map_add, e1, hc]
  rw [← pow_three, hs3, map_one, Module.End.one_apply] at e3
  have h2 : v + c + c + c = v + c := by
    rw [add_assoc v c c, add_self_eq_zero₂, add_zero]
  rw [h2] at e3
  have h := congrArg (· - v) e3
  simp only [sub_self, add_sub_cancel_left] at h
  exact h.symm

theorem exists_sub_eq_of_comm [Finite M] (hU : ∀ g, ∀ u ∈ U, ρ g u = u) {s s' : Γ}
    (hs3 : s ^ 3 = 1) (hs' : ∀ v, ρ s' v - v ∈ U → v ∈ U) (hcomm : s * s' = s' * s) (v : M) :
    ∃ w, ρ s v - v = ρ s' w - w := by
  have hc : ∀ x, ρ s' (ρ s x) = ρ s (ρ s' x) := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, ← hcomm, map_mul, Module.End.mul_apply]
  let C : Set M := Set.range fun x => ρ s x - x
  have hmem : ∀ c ∈ C, ρ s' c - c ∈ C := by
    rintro _ ⟨x, rfl⟩
    refine ⟨ρ s' x - x, ?_⟩
    simp only [map_sub, hc]
    abel
  let f : C → C := fun c => ⟨ρ s' c - c, hmem c c.2⟩
  have hf : Function.Injective f := by
    rintro ⟨_, x₁, rfl⟩ ⟨_, x₂, rfl⟩ h
    have h0 : ρ s' ((ρ s x₁ - x₁) - (ρ s x₂ - x₂)) - ((ρ s x₁ - x₁) - (ρ s x₂ - x₂)) = 0 := by
      have h1 : ρ s' (ρ s x₁ - x₁) - (ρ s x₁ - x₁) = ρ s' (ρ s x₂ - x₂) - (ρ s x₂ - x₂) :=
        congrArg Subtype.val h
      rw [map_sub, sub_eq_zero]
      rw [sub_eq_iff_eq_add] at h1
      rw [h1]
      abel
    have h2 := hs' ((ρ s x₁ - x₁) - (ρ s x₂ - x₂)) (by rw [h0]; exact U.zero_mem)
    have e : (ρ s x₁ - x₁) - (ρ s x₂ - x₂) = ρ s (x₁ - x₂) - (x₁ - x₂) := by
      rw [map_sub]
      abel
    rw [e] at h2
    have h3 := sub_eq_zero_of_mem hU hs3 h2
    rw [← e, sub_eq_zero] at h3
    exact Subtype.ext h3
  obtain ⟨⟨w, _⟩, hw⟩ := (Finite.injective_iff_surjective.mp hf) ⟨ρ s v - v, v, rfl⟩
  exact ⟨w, (congrArg Subtype.val hw).symm⟩

end Gen

section Alt

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
  {ρ : Representation (ZMod 2) A7 M}

theorem inv_of_gen7_rep {C : Submodule (ZMod 2) M} (h : ∀ b, ∀ c ∈ C, ρ (gen7 b) c ∈ C) :
    ∀ g, ∀ c ∈ C, ρ g c ∈ C := by
  let T : Subgroup A7 :=
    { carrier := {g | ∀ c ∈ C, ρ g c ∈ C}
      mul_mem' := fun {a b} ha hb c hc => by
        rw [map_mul, Module.End.mul_apply]
        exact ha _ (hb c hc)
      one_mem' := fun c hc => by rwa [map_one, Module.End.one_apply]
      inv_mem' := fun {a} ha c hc => by
        let f : C → C := fun x => ⟨ρ a x, ha x x.2⟩
        have hf : Function.Injective f := fun x y hxy => Subtype.ext (by
          have h1 := congrArg (fun z : C => ρ a⁻¹ (z : M)) hxy
          simpa [f] using h1)
        obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hf) ⟨c, hc⟩
        have h1 : ρ a y = c := congrArg Subtype.val hy
        rw [← h1, Representation.inv_self_apply]
        exact y.2 }
  have hT : (⊤ : Subgroup A7) ≤ T := by
    rw [← closure_gen7, Subgroup.closure_le]
    rintro _ ⟨b, rfl⟩
    exact h b
  intro g c hc
  exact hT (Subgroup.mem_top g) c hc

theorem three_facts :
    gen7 false ^ 3 = 1 ∧ (gen7 true * gen7 false * (gen7 true)⁻¹) ^ 3 = 1 ∧
    (gen7 true ^ 4 * gen7 false * (gen7 true ^ 4)⁻¹) ^ 3 = 1 ∧
    (gen7 true * gen7 false * (gen7 true)⁻¹) * (gen7 true ^ 4 * gen7 false * (gen7 true ^ 4)⁻¹) =
      (gen7 true ^ 4 * gen7 false * (gen7 true ^ 4)⁻¹) * (gen7 true * gen7 false * (gen7 true)⁻¹) ∧
    (gen7 true ^ 4 * gen7 false * (gen7 true ^ 4)⁻¹) * gen7 false =
      gen7 false * (gen7 true ^ 4 * gen7 false * (gen7 true ^ 4)⁻¹) := by
  decide +kernel

theorem eq_bot_of_split {U : Submodule (ZMod 2) M} (hU : ∀ g, ∀ u ∈ U, ρ g u = u)
    (hfpf : ∀ v, ρ (gen7 false) v - v ∈ U → v ∈ U)
    (hspan : ∀ C : Submodule (ZMod 2) M, (∀ g v, ρ g v - v ∈ C) → C = ⊤) : U = ⊥ := by
  obtain ⟨ht3, hs13, hs43, h14, h4t⟩ := three_facts
  set t := gen7 false with ht
  set b := gen7 true with hb
  have hinvU : ∀ g, ∀ u ∈ U, ρ g u ∈ U := fun g u hu => (hU g u hu).symm ▸ hu
  let C : Submodule (ZMod 2) M := LinearMap.range (ρ t - 1)
  have hmemC : ∀ v, ρ t v - v ∈ C := fun v => LinearMap.mem_range.mpr ⟨v, rfl⟩
  have hCt : ∀ c ∈ C, ∃ w, c = ρ t w - w := by
    intro c hc
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hc
    exact ⟨w, rfl⟩
  have hinv_t : ∀ c ∈ C, ρ t c ∈ C := by
    intro c hc
    obtain ⟨w, rfl⟩ := hCt c hc
    rw [map_sub]
    exact hmemC (ρ t w)
  have hinv_b : ∀ c ∈ C, ρ b c ∈ C := by
    intro c hc
    obtain ⟨w, rfl⟩ := hCt c hc
    have e : ρ (b * t * b⁻¹) (ρ b w) = ρ b (ρ t w) := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply]
    rw [map_sub, ← e]
    have hf4 := fpf_conj hinvU hfpf (b ^ 4)
    obtain ⟨w1, hw1⟩ := exists_sub_eq_of_comm hU hs13 hf4 h14 (ρ b w)
    obtain ⟨w2, hw2⟩ := exists_sub_eq_of_comm hU hs43 hfpf h4t w1
    rw [hw1, hw2]
    exact hmemC w2
  have hinv : ∀ g, ∀ c ∈ C, ρ g c ∈ C := inv_of_gen7_rep fun b' => by
    cases b'
    · exact hinv_t
    · exact hinv_b
  have hall : ∀ g v, ρ g v - v ∈ C := by
    intro g v
    set n := v + ρ t v + ρ t (ρ t v) with hn
    have hρt3 : ρ t (ρ t (ρ t v)) = v := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, ← pow_three',
        ht3, map_one, Module.End.one_apply]
    have hnU : n ∈ U := by
      apply hfpf n
      have : ρ t n = n := by
        rw [hn, map_add, map_add, hρt3]
        abel
      rw [this, sub_self]
      exact U.zero_mem
    have hv : v = n + (ρ t (ρ t v) - ρ t v) := by
      have h2 := add_self_eq_zero₂ (ρ t (ρ t v))
      rw [hn]
      calc v = v + (ρ t (ρ t v) + ρ t (ρ t v)) := by rw [h2, add_zero]
        _ = v + ρ t v + ρ t (ρ t v) + (ρ t (ρ t v) - ρ t v) := by abel
    have e : ρ g v - v = ρ g (ρ t (ρ t v) - ρ t v) - (ρ t (ρ t v) - ρ t v) := by
      conv_lhs => rw [hv, map_add, hU g n hnU]
      abel
    rw [e]
    exact C.sub_mem (hinv g _ (hmemC _)) (hmemC _)
  have hC := hspan C hall
  rw [eq_bot_iff]
  intro u hu
  have huC : u ∈ C := hC ▸ Submodule.mem_top
  obtain ⟨w, rfl⟩ := hCt u huC
  rw [Submodule.mem_bot]
  exact sub_eq_zero_of_mem hU ht3 hu

end Alt

end CFSG.Quasithin.A7Q528

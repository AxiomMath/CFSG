module

public import CFSG.Sporadic.Co2Smith.RigidCompare

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Certificates.ExtraspecialNF

universe u v

namespace SmithConfig

variable (c₁ : SmithConfig.{u}) (c₂ : SmithConfig.{v})

theorem frS1_y1 : frS 1 * frS 0 = frS 0 * frS 0 * frS 1 := by
  calc frS 1 * frS 0 = frS 1 * frS 0 * (frS 1 * frS 1) := by rw [frS_s1_sq, mul_one]
    _ = frS 1 * frS 0 * frS 1 * frS 1 := by rw [← mul_assoc]
    _ = frS 0 * frS 0 * frS 1 := by rw [frS_s1_y1]

theorem frS_mem_eqvSub
    (k : ℕ) (hk : k < 9) : frS k ∈ c₁.eqvSub c₂ := by
  have hy := c₁.y1_mem_eqvSub c₂
  have hc : ∀ k, k < 6 → k / 2 ≠ 0 → frS k ∈ c₁.eqvSub c₂ := fun k hk hk0 =>
    c₁.mem_eqvSub_of_frame c₂ (by omega) hy (frS_comm' hk (by norm_num) hk0)
  have h2 : frS 2 ∈ c₁.eqvSub c₂ := hc 2 (by norm_num) (by norm_num)
  interval_cases k
  · exact hy
  · exact c₁.mem_eqvSub_of_frame c₂ (by norm_num) (Subgroup.mul_mem _ hy hy) frS1_y1
  · exact h2
  · exact hc 3 (by norm_num) (by norm_num)
  · exact hc 4 (by norm_num) (by norm_num)
  · exact hc 5 (by norm_num) (by norm_num)
  · exact c₁.mem_eqvSub_of_frame c₂ (by norm_num) h2 (p12_rel 0 (by norm_num))
  · exact c₁.mem_eqvSub_of_frame c₂ (by norm_num) hy (p23_rel 0 (by norm_num))
  · exact c₁.mem_eqvSub_of_frame c₂ (by norm_num) hy frS_x_y1

theorem frWordS_mem_eqvSub :
    ∀ w : List ℕ, (∀ k ∈ w, k < 9) → frWordS w ∈ c₁.eqvSub c₂
  | [], _ => Subgroup.one_mem _
  | k :: w, hw => Subgroup.mul_mem _ (c₁.frS_mem_eqvSub c₂ k (hw k List.mem_cons_self))
      (frWordS_mem_eqvSub w fun j hj => hw j (List.mem_cons_of_mem _ hj))

theorem eqvSub_eq_top :
    c₁.eqvSub c₂ = ⊤ := by
  have ha : (⟨aE, aE_mem_S0⟩ : S0) ∈ c₁.eqvSub c₂ := by
    rw [← frWordS_genA]
    exact c₁.frWordS_mem_eqvSub c₂ _ fun k hk => by have := genAWord_lt k hk; decide +revert
  have hb : (⟨bE, bE_mem_S0⟩ : S0) ∈ c₁.eqvSub c₂ := by
    rw [← frWordS_genB]
    exact c₁.frWordS_mem_eqvSub c₂ _ fun k hk => by have := genBWord_lt k hk; decide +revert
  have hle : S0 ≤ (c₁.eqvSub c₂).map S0.subtype := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, ha, rfl⟩
    · exact ⟨_, hb, rfl⟩
  rw [eq_top_iff]
  intro g _
  obtain ⟨g', hg', he⟩ := hle g.2
  have : g' = g := Subtype.ext he
  rw [← this]
  exact hg'

theorem θE_cE
    (g : S0) (e : c₁.E) :
    c₁.θE c₂ (c₁.cE (c₁.ι g) e) = c₂.cE (c₂.ι g) (c₁.θE c₂ e) := by
  have hg : g ∈ c₁.eqvSub c₂ := (c₁.eqvSub_eq_top c₂).symm ▸ Subgroup.mem_top g
  exact hg e

@[expose] noncomputable def esMap (c : SmithConfig.{u}) (p : c.E × S0) : c.H := p.1 * c.ι p.2

theorem esMap_mul (c : SmithConfig.{u}) (e e' : c.E) (s s' : S0) :
    c.esMap (e, s) * c.esMap (e', s') = c.esMap (e * c.cE (c.ι s) e', s * s') := by
  simp only [esMap, Subgroup.coe_mul, c.cE_val, map_mul]
  group

theorem esMap_injective (c : SmithConfig.{u}) : Function.Injective c.esMap := by
  rintro ⟨e, s⟩ ⟨e', s'⟩ h
  have h1 : (e : c.H) * c.ι s = e' * c.ι s' := h
  have h2 : (e' : c.H)⁻¹ * e = c.ι (s' * s⁻¹) := by
    rw [map_mul, map_inv]
    calc (e' : c.H)⁻¹ * e = (e' : c.H)⁻¹ * (e * c.ι s) * (c.ι s)⁻¹ := by group
      _ = (e' : c.H)⁻¹ * (e' * c.ι s') * (c.ι s)⁻¹ := by rw [h1]
      _ = c.ι s' * (c.ι s)⁻¹ := by group
  have hmem : (e' : c.H)⁻¹ * e ∈ c.ι.range ⊓ CFSG.pCore 2 c.H :=
    ⟨⟨_, h2.symm⟩, Subgroup.mul_mem _ (Subgroup.inv_mem _ e'.2) e.2⟩
  rw [c.inf_eq, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hs : c.ι (s' * s⁻¹) = 1 := by rw [← h2, hmem, inv_mul_cancel]
  rw [← map_one c.ι] at hs
  have hss := c.inj hs
  rw [mul_inv_eq_one] at hss
  exact Prod.ext (Subtype.ext hmem.symm) hss.symm

theorem esMap_bijective
    (c : SmithConfig.{u}) : Function.Bijective c.esMap :=
  c.esMap_injective.bijective_of_nat_card_le (by
    rw [Nat.card_prod, c.card_E, card_S0, c.card_H]
    norm_num)

@[expose] noncomputable def compareEquiv :
    c₁.H ≃* c₂.H :=
  MulEquiv.mk ((Equiv.ofBijective _ c₁.esMap_bijective).symm.trans
    ((Equiv.prodCongr (c₁.θE c₂).toEquiv (Equiv.refl S0)).trans
      (Equiv.ofBijective _ c₂.esMap_bijective))) (by
    intro x y
    obtain ⟨⟨e, s⟩, rfl⟩ := c₁.esMap_bijective.2 x
    obtain ⟨⟨e', s'⟩, rfl⟩ := c₁.esMap_bijective.2 y
    have hsymm : ∀ p, (Equiv.ofBijective _ c₁.esMap_bijective).symm (c₁.esMap p) = p :=
      fun p => (Equiv.ofBijective _ c₁.esMap_bijective).symm_apply_apply p
    show (Equiv.ofBijective _ c₂.esMap_bijective) ((Equiv.prodCongr (c₁.θE c₂).toEquiv
        (Equiv.refl S0)) ((Equiv.ofBijective _ c₁.esMap_bijective).symm
          (c₁.esMap (e, s) * c₁.esMap (e', s')))) =
      (Equiv.ofBijective _ c₂.esMap_bijective) ((Equiv.prodCongr (c₁.θE c₂).toEquiv
        (Equiv.refl S0)) ((Equiv.ofBijective _ c₁.esMap_bijective).symm (c₁.esMap (e, s)))) *
      (Equiv.ofBijective _ c₂.esMap_bijective) ((Equiv.prodCongr (c₁.θE c₂).toEquiv
        (Equiv.refl S0)) ((Equiv.ofBijective _ c₁.esMap_bijective).symm (c₁.esMap (e', s'))))
    rw [c₁.esMap_mul, hsymm, hsymm, hsymm]
    simp only [Equiv.prodCongr_apply, Prod.map, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
      Equiv.refl_apply, Equiv.ofBijective_apply]
    rw [map_mul, c₁.θE_cE, c₂.esMap_mul])

end SmithConfig

end CFSG.Sporadic.Co2Smith

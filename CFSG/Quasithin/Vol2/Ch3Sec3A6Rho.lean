module

public import CFSG.Quasithin.Vol2.Ch3Sec3A6Transport

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace A6Coc

theorem bP_fix : ∀ x : Fin 6, bP x = x → x = 0 := by decide

theorem bP_orbit : ∀ v : Fin 6, v ≠ 0 → ∃ k : Fin 5, (bP ^ (k : ℕ)) 1 = v := by decide

theorem bP_pow_zero : ∀ k : ℕ, (bP ^ k) 0 = 0 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, Equiv.Perm.mul_apply, show bP 0 = 0 by decide, ih]

theorem bP_pow_comm : ∀ k : Fin 5, bP ^ (k : ℕ) * aP = aP * bP ^ (k : ℕ) → bP ^ (k : ℕ) = 1 := by
  decide

theorem eq_one_of_comm {τ : Equiv.Perm (Fin 6)} (ha : τ * aP = aP * τ) (hb : τ * bP = bP * τ) :
    τ = 1 := by
  have hcb : Commute τ bP := hb
  have h0 : τ 0 = 0 := by
    apply bP_fix
    have := congrArg (fun f : Equiv.Perm (Fin 6) => f 0) hb
    simp only [Equiv.Perm.mul_apply, show bP 0 = 0 by decide] at this
    exact this.symm
  have h1 : τ 1 ≠ 0 := fun h => absurd (τ.injective (h.trans h0.symm)) (by decide)
  obtain ⟨k, hk⟩ := bP_orbit (τ 1) h1
  have hτ : τ = bP ^ (k : ℕ) := by
    ext x
    by_cases hx : x = 0
    · rw [hx, h0, bP_pow_zero]
    · obtain ⟨j, rfl⟩ := bP_orbit x hx
      have e1 : τ ((bP ^ (j : ℕ)) 1) = (bP ^ (j : ℕ)) (τ 1) := by
        rw [← Equiv.Perm.mul_apply, (hcb.pow_right (j : ℕ)).eq, Equiv.Perm.mul_apply]
      rw [e1, ← hk, ← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_add, ← pow_add,
        add_comm]
  rw [hτ] at ha ⊢
  exact bP_pow_comm k ha

@[expose] def duad (i j : Fin 6) : Fin 6 → ZMod 2 := Pi.single i 1 + Pi.single j 1

theorem sum_duad : ∀ i j : Fin 6, ∑ k, duad i j k = 0 := by decide +kernel

theorem duad_check : ∀ i j a b : Fin 6, i ≠ j → crd (duad a b) = crd (duad i j) →
    (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
  decide +kernel

theorem act_duad (τ : Equiv.Perm (Fin 6)) (i j : Fin 6) :
    act τ (crd (duad i j)) = crd (duad (τ i) (τ j)) := by
  rw [act_crd τ _ (sum_duad i j)]
  congr 1
  funext k
  simp only [duad, Pi.add_apply, Pi.single_apply, Equiv.Perm.inv_eq_iff_eq]

theorem eq_one_of_act {τ : Equiv.Perm (Fin 6)} (h : ∀ v, act τ v = v) : τ = 1 := by
  have hd : ∀ i j : Fin 6, i ≠ j → (τ i = i ∧ τ j = j) ∨ (τ i = j ∧ τ j = i) := by
    intro i j hij
    have h1 := h (crd (duad i j))
    rw [act_duad] at h1
    exact duad_check i j (τ i) (τ j) hij h1
  have hne : ∀ x : Fin 6, x ≠ x + 1 ∧ x ≠ x + 2 ∧ x + 1 ≠ x + 2 := by decide
  refine Equiv.ext fun x => ?_
  obtain ⟨h1, h2, h3⟩ := hne x
  show τ x = x
  rcases hd x (x + 1) h1 with ⟨ha, -⟩ | ⟨ha, -⟩
  · exact ha
  · rcases hd x (x + 2) h2 with ⟨hb, -⟩ | ⟨hb, -⟩
    · exact hb
    · exact absurd (ha.symm.trans hb) h3

theorem eq_of_heartAct_eq {σ σ' : Equiv.Perm (Fin 6)} (h : ∀ y, heartAct 6 σ y = heartAct 6 σ' y) :
    σ = σ' := by
  have h1 : σ'⁻¹ * σ = 1 := by
    apply eq_one_of_act
    intro v
    calc act (σ'⁻¹ * σ) v = act (σ'⁻¹ * σ) (eps (epsInv v)) := by rw [eps_epsInv]
      _ = eps (heartAct 6 (σ'⁻¹ * σ) (epsInv v)) := (eps_heartAct _ _).symm
      _ = eps (epsInv v) := by
        rw [heartAct_mul, h, ← heartAct_mul, inv_mul_cancel, heartAct_one]
      _ = v := eps_epsInv v
  calc σ = σ' * (σ'⁻¹ * σ) := by group
    _ = σ' := by rw [h1, mul_one]

end A6Coc

namespace A6Trans

open A6Coc

theorem perm_unique {σ σ' : Equiv.Perm (Fin 6)}
    (h : ∀ x : A6Coc.Γ, σ * (x : Equiv.Perm (Fin 6)) * σ⁻¹ = σ' * (x : Equiv.Perm (Fin 6)) * σ'⁻¹) :
    σ = σ' := by
  have key : ∀ x : A6Coc.Γ, σ⁻¹ * σ' * (x : Equiv.Perm (Fin 6)) =
      (x : Equiv.Perm (Fin 6)) * (σ⁻¹ * σ') := by
    intro x
    calc σ⁻¹ * σ' * (x : Equiv.Perm (Fin 6)) =
        σ⁻¹ * (σ' * (x : Equiv.Perm (Fin 6)) * σ'⁻¹) * σ' := by group
      _ = σ⁻¹ * (σ * (x : Equiv.Perm (Fin 6)) * σ⁻¹) * σ' := by rw [h x]
      _ = (x : Equiv.Perm (Fin 6)) * (σ⁻¹ * σ') := by group
  have h1 := eq_one_of_comm (key aL) (key bL)
  calc σ = σ * (σ⁻¹ * σ') := by rw [h1, mul_one]
    _ = σ' := by group

variable {G : Type} [Group G] {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 6)}

theorem exists_perm_conj (hA : IsAltBlockTypeWith L 6 α) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    ∃ σ : Equiv.Perm (Fin 6), ∀ ℓ ℓ' : ↥L, (ℓ' : G) = g * ℓ * g⁻¹ →
      (α ℓ' : Equiv.Perm (Fin 6)) = σ * (α ℓ : Equiv.Perm (Fin 6)) * σ⁻¹ := by
  obtain ⟨hαs, hαk, β, hβs, hβk, hβe⟩ := hA
  obtain ⟨σ, h1, -⟩ := exists_perm hαs hαk hβs hβk hβe hg
  exact ⟨σ, h1⟩

@[expose] noncomputable def rhoFun (hA : IsAltBlockTypeWith L 6 α)
    (g : ↥(Subgroup.normalizer (L : Set G))) : Equiv.Perm (Fin 6) :=
  Classical.choose (exists_perm_conj hA g.2)

theorem rhoFun_spec (hA : IsAltBlockTypeWith L 6 α)
    (g : ↥(Subgroup.normalizer (L : Set G))) (ℓ ℓ' : ↥L) (h : (ℓ' : G) = g * ℓ * g⁻¹) :
    (α ℓ' : Equiv.Perm (Fin 6)) = rhoFun hA g * (α ℓ : Equiv.Perm (Fin 6)) * (rhoFun hA g)⁻¹ :=
  Classical.choose_spec (exists_perm_conj hA g.2) ℓ ℓ' h

theorem rhoFun_unique (hA : IsAltBlockTypeWith L 6 α)
    (g : ↥(Subgroup.normalizer (L : Set G))) {σ : Equiv.Perm (Fin 6)}
    (hσ : ∀ ℓ ℓ' : ↥L, (ℓ' : G) = g * ℓ * g⁻¹ →
      (α ℓ' : Equiv.Perm (Fin 6)) = σ * (α ℓ : Equiv.Perm (Fin 6)) * σ⁻¹) :
    σ = rhoFun hA g := by
  apply perm_unique
  intro x
  obtain ⟨ℓ, rfl⟩ := hA.1 x
  have hm : (g : G) * ℓ * (g : G)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp g.2 ℓ).mp ℓ.2
  rw [← hσ ℓ ⟨_, hm⟩ rfl, ← rhoFun_spec hA g ℓ ⟨_, hm⟩ rfl]

@[expose] noncomputable def rho (hA : IsAltBlockTypeWith L 6 α) :
    ↥(Subgroup.normalizer (L : Set G)) →* Equiv.Perm (Fin 6) :=
  MonoidHom.mk' (rhoFun hA) fun g h => by
    symm
    apply rhoFun_unique
    intro ℓ ℓ' hℓ
    have hm : (h : G) * ℓ * (h : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp h.2 ℓ).mp ℓ.2
    have hℓ' : (ℓ' : G) = g * ((h : G) * ℓ * (h : G)⁻¹) * (g : G)⁻¹ := by
      rw [hℓ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul]
      group
    rw [rhoFun_spec hA g ⟨_, hm⟩ ℓ' hℓ', rhoFun_spec hA h ℓ ⟨_, hm⟩ rfl]
    group

theorem rho_apply (hA : IsAltBlockTypeWith L 6 α)
    (g : ↥(Subgroup.normalizer (L : Set G))) : rho hA g = rhoFun hA g := rfl

theorem rho_conj (hA : IsAltBlockTypeWith L 6 α)
    (g : ↥(Subgroup.normalizer (L : Set G))) (ℓ ℓ' : ↥L) (h : (ℓ' : G) = g * ℓ * g⁻¹) :
    (α ℓ' : Equiv.Perm (Fin 6)) = rho hA g * (α ℓ : Equiv.Perm (Fin 6)) * (rho hA g)⁻¹ :=
  rhoFun_spec hA g ℓ ℓ' h

theorem rho_of_mem (hA : IsAltBlockTypeWith L 6 α) (ℓ : ↥L) :
    rho hA ⟨ℓ, Subgroup.le_normalizer ℓ.2⟩ = (α ℓ : Equiv.Perm (Fin 6)) := by
  symm
  refine rhoFun_unique hA _ fun ℓ₁ ℓ' h => ?_
  have e : ℓ' = ℓ * ℓ₁ * ℓ⁻¹ := Subtype.ext (by simpa using h)
  rw [e, map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem rho_heart (hA : IsAltBlockTypeWith L 6 α)
    {β : ↥(blockU L) →* Multiplicative (AltHeart 6)}
    (hβs : Function.Surjective β) (hβk : β.ker = (blockZ L).subgroupOf (blockU L))
    (hβe : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
        (QuotientAddGroup.mk (permWeight 6 (α ℓ : Equiv.Perm (Fin 6)) x) : AltHeart 6) =
          Multiplicative.toAdd (β v))
    (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)) (h : (u' : G) = g * u * g⁻¹) :
    Multiplicative.toAdd (β u') = heartAct 6 (rho hA g) (Multiplicative.toAdd (β u)) := by
  obtain ⟨σ, h1, h2⟩ := exists_perm hA.1 hA.2.1 hβs hβk hβe g.2
  rw [rho_apply, ← rhoFun_unique hA g h1]
  exact h2 u u' h

end A6Trans

end CFSG.Quasithin.H13

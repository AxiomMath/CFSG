module

public import CFSG.Quasithin.Background.SzG11M12Beta
public import CFSG.Quasithin.Background.SzG11M12Vec

public section

namespace CFSG.Quasithin.G11.SzG11S

namespace M12Vec

open CFSG.Blueprint M12Syl CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Mathieu
  CFSG.Sporadic.Schreier

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {H : Subgroup (GLV V)}

@[expose] def conjAut (c : PCore H) (x : GLV V) (hx : ∀ h ∈ H, x * h * x⁻¹ ∈ H)
    (hx' : ∀ h ∈ H, x⁻¹ * h * x ∈ H) : MulAut ↥NativeSporadic.M12 where
  toFun m := c.φ ⟨x * (c.φ.symm m : GLV V) * x⁻¹, hx _ (c.φ.symm m).2⟩
  invFun m := c.φ ⟨x⁻¹ * (c.φ.symm m : GLV V) * x, hx' _ (c.φ.symm m).2⟩
  left_inv m := by
    apply c.φ.symm.injective
    simp only [MulEquiv.symm_apply_apply]
    apply Subtype.ext
    simp only
    group
  right_inv m := by
    apply c.φ.symm.injective
    simp only [MulEquiv.symm_apply_apply]
    apply Subtype.ext
    simp only
    group
  map_mul' m n := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    group

theorem conjAut_apply (c : PCore H) (x : GLV V) (hx : ∀ h ∈ H, x * h * x⁻¹ ∈ H)
    (hx' : ∀ h ∈ H, x⁻¹ * h * x ∈ H) (h : ↥H) :
    conjAut c x hx hx' (c.φ h) = c.φ ⟨x * (h : GLV V) * x⁻¹, hx _ h.2⟩ := by
  simp [conjAut]

@[expose] def InnerAct (c : PCore H) (x : GLV V) : Prop :=
  ∃ g : ↥NativeSporadic.M12, ∀ h η : ↥H, x * (h : GLV V) * x⁻¹ = (η : GLV V) →
    c.φ η = g * c.φ h * g⁻¹

@[expose] def OuterAct
    (c : PCore H) (x : GLV V) : Prop :=
  ∃ g : ↥NativeSporadic.M12, ∀ h η : ↥H, x * (h : GLV V) * x⁻¹ = (η : GLV V) →
    c.φ η = g * beta (c.φ h) * g⁻¹

theorem classify
    (c : PCore H) (x : GLV V) (hx : ∀ h ∈ H, x * h * x⁻¹ ∈ H)
    (hx' : ∀ h ∈ H, x⁻¹ * h * x ∈ H) : InnerAct c x ∨ OuterAct c x := by
  obtain ⟨g, hg | hg⟩ := exists_conj_or_conj_mul_beta (conjAut c x hx hx')
  · refine Or.inl ⟨g, fun h η hη => ?_⟩
    have h1 : c.φ η = conjAut c x hx hx' (c.φ h) := by
      rw [conjAut_apply]
      congr 1
      exact Subtype.ext hη.symm
    rw [h1, hg, MulAut.conj_apply]
  · refine Or.inr ⟨g, fun h η hη => ?_⟩
    have h1 : c.φ η = conjAut c x hx hx' (c.φ h) := by
      rw [conjAut_apply]
      congr 1
      exact Subtype.ext hη.symm
    rw [h1, hg, MulAut.mul_apply, MulAut.conj_apply]

theorem mem_of_inner (c : PCore H) (Γ : Subgroup (GLV V)) (hHΓ : H ≤ Γ)
    (hC : ∀ x ∈ Γ, (∀ h ∈ H, x * h = h * x) → x = 1) (x : GLV V) (hxΓ : x ∈ Γ)
    (hx : ∀ h ∈ H, x * h * x⁻¹ ∈ H) (hin : InnerAct c x) : x ∈ H := by
  obtain ⟨g, hg⟩ := hin
  set η : ↥H := c.φ.symm g with hη
  have hcomm : ∀ h ∈ H, (η : GLV V)⁻¹ * x * h = h * ((η : GLV V)⁻¹ * x) := by
    intro h hh
    have h1 := hg ⟨h, hh⟩ ⟨x * h * x⁻¹, hx h hh⟩ rfl
    have h2 : (⟨x * h * x⁻¹, hx h hh⟩ : ↥H) = η * ⟨h, hh⟩ * η⁻¹ := by
      apply c.φ.injective
      rw [h1, map_mul, map_mul, map_inv, hη, MulEquiv.apply_symm_apply]
    have h3 : x * h * x⁻¹ = (η : GLV V) * h * (η : GLV V)⁻¹ := congrArg Subtype.val h2
    calc (η : GLV V)⁻¹ * x * h = (η : GLV V)⁻¹ * (x * h * x⁻¹) * x := by group
      _ = (η : GLV V)⁻¹ * ((η : GLV V) * h * (η : GLV V)⁻¹) * x := by rw [h3]
      _ = h * ((η : GLV V)⁻¹ * x) := by group
  have h1 := hC _ (Γ.mul_mem (Γ.inv_mem (hHΓ η.2)) hxΓ) hcomm
  have h2 : x = (η : GLV V) := by
    calc x = (η : GLV V) * ((η : GLV V)⁻¹ * x) := by group
      _ = (η : GLV V) := by rw [h1, mul_one]
  rw [h2]
  exact η.2

theorem inner_of_outer_mul
    (c : PCore H) (x y : GLV V) (hy : ∀ h ∈ H, y * h * y⁻¹ ∈ H)
    (hox : OuterAct c x) (hoy : OuterAct c y) : InnerAct c (x * y) := by
  obtain ⟨g, hg⟩ := hox
  obtain ⟨g', hg'⟩ := hoy
  refine ⟨g * beta g', fun h η hη => ?_⟩
  have h1 := hg' h ⟨y * h * y⁻¹, hy h h.2⟩ rfl
  have h2 := hg ⟨y * h * y⁻¹, hy h h.2⟩ η (by
    rw [← hη]
    simp only [mul_inv_rev]
    group)
  rw [h2, h1, map_mul, map_mul, map_inv]
  have h3 : beta (beta (c.φ h)) = c.φ h := by
    have := congrArg (fun a : MulAut ↥NativeSporadic.M12 => a (c.φ h)) beta_mul_self
    simpa using this
  rw [h3]
  group

theorem exists_two_trans
    {i j k l : Fin 12} (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ m : ↥NativeSporadic.M12, (m : Equiv.Perm (Fin 12)) k = i ∧
      (m : Equiv.Perm (Fin 12)) l = j := by
  obtain ⟨m₁, h10, h11⟩ := exists_smul_eq_two m12_hyp (by decide) (by norm_num) i j hij
  obtain ⟨m₂, h20, h21⟩ := exists_smul_eq_two m12_hyp (by decide) (by norm_num) k l hkl
  have h10' : (m₁ : Equiv.Perm (Fin 12)) 0 = i := h10
  have h11' : (m₁ : Equiv.Perm (Fin 12)) 1 = j := h11
  have h20' : (m₂ : Equiv.Perm (Fin 12)) 0 = k := h20
  have h21' : (m₂ : Equiv.Perm (Fin 12)) 1 = l := h21
  refine ⟨m₁ * m₂⁻¹, ?_, ?_⟩
  · have : (m₂⁻¹ : ↥NativeSporadic.M12).1 k = 0 := by rw [← h20']; simp
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, this, h10']
  · have : (m₂⁻¹ : ↥NativeSporadic.M12).1 l = 1 := by rw [← h21']; simp
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, this, h11']

theorem presD_conj {σ m : Equiv.Perm (Fin 12)} {i j k l : Fin 12} (hk : m k = i) (hl : m l = j)
    (h : PresD σ k l) : PresD (m * σ * m⁻¹) i j := by
  have hmi : m⁻¹ i = k := by rw [← hk]; simp
  have hmj : m⁻¹ j = l := by rw [← hl]; simp
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨by simp [Equiv.Perm.mul_apply, hmi, h1, hk], by simp [Equiv.Perm.mul_apply, hmj, h2, hl]⟩
  · right
    exact ⟨by simp [Equiv.Perm.mul_apply, hmi, h1, hl], by simp [Equiv.Perm.mul_apply, hmj, h2, hk]⟩

theorem outer_pr_ne
    (c : PCore H) (x : GLV V) (hx : ∀ h ∈ H, x * h * x⁻¹ ∈ H) (hout : OuterAct c x)
    {i j k l : Fin 12} (hij : i ≠ j) (hkl : k ≠ l) : x (c.pr i j) ≠ c.pr k l := by
  intro hxv
  obtain ⟨g, hg⟩ := hout
  have hD : ∀ s : ↥NativeSporadic.M12, PresD (s : Equiv.Perm (Fin 12)) i j →
      PresD ((g * beta s * g⁻¹ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) k l := by
    intro s hs
    set h : ↥H := c.φ.symm s with hh
    have hφh : c.φ h = s := by rw [hh, MulEquiv.apply_symm_apply]
    have hperm : c.perm h = (s : Equiv.Perm (Fin 12)) := by
      simp only [PCore.perm, hφh]
    have hfix : (h : GLV V) (c.pr i j) = c.pr i j := by
      rw [c.act_pr h, hperm]
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, c.pr_comm]
    set η : ↥H := ⟨x * (h : GLV V) * x⁻¹, hx h h.2⟩ with hηdef
    have hη := hg h η rfl
    rw [hφh] at hη
    have hinv : (x⁻¹ : GLV V) (c.pr k l) = c.pr i j := by
      rw [← hxv]
      exact LinearEquiv.symm_apply_apply x _
    have hηk : (η : GLV V) (c.pr k l) = c.pr k l := by
      show x ((h : GLV V) ((x⁻¹ : GLV V) (c.pr k l))) = c.pr k l
      rw [hinv, hfix, hxv]
    have hact := c.act_pr η k l
    rw [hηk] at hact
    have hne : c.perm η k ≠ c.perm η l := fun h' => hkl ((c.perm η).injective h')
    have hperm' : c.perm η = ((g * beta s * g⁻¹ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) := by
      simp only [PCore.perm, hη]
    rw [← hperm']
    rcases pr_eq c hkl hne hact with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩
  obtain ⟨m, hmk, hml⟩ := exists_two_trans hij hkl
  refine outer_no_stab (m * g) hij (fun s hs => ?_)
  have := presD_conj hmk hml (hD s hs)
  have e : ((m * g * beta s * (m * g)⁻¹ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) =
      (m : Equiv.Perm (Fin 12)) *
        ((g * beta s * g⁻¹ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) *
        (m : Equiv.Perm (Fin 12))⁻¹ := by
    simp [mul_assoc]
  rw [e]
  exact this

end M12Vec

end CFSG.Quasithin.G11.SzG11S

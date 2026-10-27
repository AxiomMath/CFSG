module

public import CFSG.Quasithin.Background.H156Gen
public import CFSG.Quasithin.Background.H153Defs

public section

namespace CFSG.Quasithin.H153

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H156

section Transport

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem congrHom_mem_map {eg : V ≃* W} {G : Subgroup (MulAut V)} {y : MulAut V} (hy : y ∈ G) :
    congrHom eg y ∈ G.map (congrHom eg) := Subgroup.mem_map_of_mem _ hy

theorem mem_map_eg {eg : V ≃* W} {X : Subgroup V} {v : V} :
    eg v ∈ X.map eg.toMonoidHom ↔ v ∈ X := Subgroup.mem_map_iff_mem eg.injective

theorem chief_of_map (eg : V ≃* W) {G : Subgroup (MulAut V)} {X Y : Subgroup V}
    (h : IsChiefFactorUnder (actsOnModule (G.map (congrHom eg))) (X.map eg.toMonoidHom)
      (Y.map eg.toMonoidHom)) : IsChiefFactorUnder (actsOnModule G) X Y := by
  obtain ⟨hlt, hX, hY, hmin⟩ := h
  have hinv : ∀ {Z : Subgroup V}, IsActsInv (actsOnModule (G.map (congrHom eg)))
      (Z.map eg.toMonoidHom) → IsActsInv (actsOnModule G) Z := by
    intro Z hZ f hf u hu
    obtain ⟨y, hy, rfl⟩ := hf
    have h1 := hZ (fun w => congrHom eg y w) ⟨congrHom eg y, congrHom_mem_map hy, rfl⟩ (eg u)
      (mem_map_eg.2 hu)
    rw [congrHom_apply_eg] at h1
    exact mem_map_eg.1 h1
  refine ⟨(Subgroup.map_lt_map_iff_of_injective eg.injective).1 hlt, hinv hX, hinv hY, ?_⟩
  intro Z hXZ hZY hZ
  have hZ' : IsActsInv (actsOnModule (G.map (congrHom eg))) (Z.map eg.toMonoidHom) := by
    intro f hf u hu
    obtain ⟨y', hy', rfl⟩ := hf
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hy'
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hu
    have h1 := hZ (fun v => y v) ⟨y, hy, rfl⟩ w hw
    have : congrHom eg y (eg w) = eg (y w) := congrHom_apply_eg eg y w
    show congrHom eg y (eg w) ∈ Z.map eg.toMonoidHom
    rw [this]
    exact mem_map_eg.2 h1
  rcases hmin _ (Subgroup.map_mono hXZ) (Subgroup.map_mono hZY) hZ' with h | h
  · left
    exact Subgroup.map_injective eg.injective h
  · right
    exact Subgroup.map_injective eg.injective h

theorem fullTransp_of_map (eg : V ≃* W) {G X : Subgroup (MulAut V)} {A V₁ : Subgroup V}
    (h : FullTranspCenter' (G.map (congrHom eg)) (X.map (congrHom eg)) (A.map eg.toMonoidHom)
      (V₁.map eg.toMonoidHom)) : FullTranspCenter' G X A V₁ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun g hg x hx => ?_, ?_, fun g hg hfix => ?_, fun g hg x hx => ?_⟩
  · have := h1 (congrHom eg g) (congrHom_mem_map hg) (eg x) (mem_map_eg.2 hx)
    rw [congrHom_apply_eg, ← map_inv, ← map_mul] at this
    exact mem_map_eg.1 this
  · intro τ hτ
    let φ : ↥A ≃* ↥(A.map eg.toMonoidHom) := A.equivMapOfInjective eg.toMonoidHom eg.injective
    have hφ : ∀ u : ↥A, ((φ u : ↥(A.map eg.toMonoidHom)) : W) = eg (u : V) := fun u => rfl
    let τ' : MulAut ↥(A.map eg.toMonoidHom) := φ.symm.trans (τ.trans φ)
    have hτ' : ∀ x : ↥A, τ' (φ x) = φ (τ x) := fun x => by
      show φ (τ (φ.symm (φ x))) = φ (τ x)
      rw [MulEquiv.symm_apply_apply]
    obtain ⟨g', hg', hgτ⟩ := h2 τ' (by
      intro x'
      obtain ⟨x, rfl⟩ := φ.surjective x'
      rw [hτ' x, hφ, hφ, ← map_inv, ← map_mul]
      exact Subgroup.mem_map_of_mem _ (hτ x))
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hg'
    refine ⟨g, hg, fun x => ?_⟩
    have e1 := hgτ (φ x)
    rw [hτ' x, hφ, hφ, congrHom_apply_eg] at e1
    exact eg.injective e1
  · have : congrHom eg g = 1 := by
      refine h3 _ (congrHom_mem_map hg) fun x' hx' => ?_
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hx'
      show congrHom eg g (eg x) = eg x
      rw [congrHom_apply_eg, hfix x hx]
    exact congrHom_injective eg (by rw [this, map_one])
  · have := h4 (congrHom eg g) (congrHom_mem_map hg) (congrHom eg x) (congrHom_mem_map hx)
    rw [← map_mul, ← map_inv, ← map_mul] at this
    exact (Subgroup.mem_map_iff_mem (congrHom_injective eg)).1 this

theorem xiSub_map_le (eg : V ≃* W) (A : Subgroup (MulAut V)) :
    xiSub (A.map (congrHom eg)) ≤ (xiSub A).map eg.toMonoidHom := by
  refine iSup_le fun a' => iSup_le fun ha' => iSup_le fun ha1 => ?_
  obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.1 ha'
  have ha1' : a ≠ 1 := fun h => ha1 (by rw [h, map_one])
  have h1 : fixV (Subgroup.zpowers (congrHom eg a)) =
      (fixV (Subgroup.zpowers a)).map eg.toMonoidHom := by
    rw [← fixV_map_congrHom, MonoidHom.map_zpowers]
  rw [h1]
  refine Subgroup.map_mono ?_
  exact le_iSup₂_of_le a haA (le_iSup_of_le ha1' le_rfl)

theorem xiSub_eq_top_of_map (eg : V ≃* W) {A : Subgroup (MulAut V)}
    (h : xiSub (A.map (congrHom eg)) = ⊤) : xiSub A = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  have h1 : eg v ∈ (xiSub A).map eg.toMonoidHom := xiSub_map_le eg A (by rw [h]; exact trivial)
  exact mem_map_eg.1 h1

end Transport

section Pairing

variable {V : Type*} [CommGroup V]

open scoped Classical in
@[expose] noncomputable def valOne (c : V) : ZMod 2 := if c = 1 then 0 else 1

theorem valOne_one : valOne (1 : V) = 0 := by simp [valOne]

theorem valOne_of_ne {c : V} (h : c ≠ 1) : valOne c = 1 := by simp [valOne, h]

theorem valOne_mul {z c c' : V} (hz : z * z = 1) (hc : c = 1 ∨ c = z) (hc' : c' = 1 ∨ c' = z) :
    valOne (c * c') = valOne c + valOne c' := by
  rcases hc with hc | hc
  · rw [hc, one_mul, valOne_one, zero_add]
  rcases hc' with hc' | hc'
  · rw [hc', mul_one, valOne_one, add_zero]
  · rw [hc, hc', hz, valOne_one]
    by_cases h : z = 1
    · rw [h, valOne_one]
      rfl
    · rw [valOne_of_ne h]
      decide

theorem eq_one_or_of_mem_zpowers {z c : V} (hz : z * z = 1) (hc : c ∈ Subgroup.zpowers z) :
    c = 1 ∨ c = z := by
  obtain ⟨k, rfl⟩ := hc
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz]
  change z ^ k = 1 ∨ z ^ k = z
  rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp

theorem valOne_eq_zero_iff {c : V} : valOne c = 0 ↔ c = 1 := by
  unfold valOne
  by_cases h : c = 1 <;> simp [h]

theorem valOne_ne_zero_iff {c : V} : valOne c ≠ 0 ↔ c ≠ 1 := not_congr valOne_eq_zero_iff

theorem isDualOfConj_of {Γ : Subgroup S24} (ρ : ↥Γ →* MulAut V) (G K : Subgroup S24)
    (hKΓ : K ≤ Γ) (hKG : K ≤ G) (A : Subgroup V) (z : V) (hz : z * z = 1)
    (hGz : ∀ g : ↥Γ, (g : S24) ∈ G → ρ g z = z)
    (hcomm : ∀ k : ↥Γ, (k : S24) ∈ K → ∀ x ∈ A, ρ k x * x⁻¹ ∈ Subgroup.zpowers z)
    (hnd1 : ∀ x ∈ A, x ∉ Subgroup.zpowers z → ∃ k : ↥Γ, (k : S24) ∈ K ∧ ρ k x ≠ x)
    (hnd2 : ∀ k : ↥Γ, (k : S24) ∈ K → (k : S24) ≠ 1 → ∃ x ∈ A, ρ k x ≠ x)
    (hKn : ∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    IsDualOfConj' ρ G A (Subgroup.zpowers z) K := by
  classical
  let pr : V → S24 → ZMod 2 := fun x k =>
    if hk : k ∈ Γ then valOne (ρ ⟨k, hk⟩ x * x⁻¹) else 0
  have hpr : ∀ (x : V) (k : ↥Γ), pr x (k : S24) = valOne (ρ k x * x⁻¹) := by
    intro x k
    simp only [pr, dif_pos k.2]
  have hfixc : ∀ (g : ↥Γ), (g : S24) ∈ G → ∀ c ∈ Subgroup.zpowers z, ρ g c = c := by
    intro g hg c hc
    rcases eq_one_or_of_mem_zpowers hz hc with rfl | rfl
    · exact map_one _
    · exact hGz g hg
  refine ⟨pr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx k hk k' hk'
    have hkΓ := hKΓ hk
    have hk'Γ := hKΓ hk'
    have e : (⟨k * k', Γ.mul_mem hkΓ hk'Γ⟩ : ↥Γ) = ⟨k, hkΓ⟩ * ⟨k', hk'Γ⟩ := rfl
    rw [show pr x (k * k') = valOne (ρ (⟨k, hkΓ⟩ * ⟨k', hk'Γ⟩) x * x⁻¹) from by
      rw [← e]; exact hpr x ⟨k * k', Γ.mul_mem hkΓ hk'Γ⟩, hpr x ⟨k, hkΓ⟩, hpr x ⟨k', hk'Γ⟩]
    have hc : ρ ⟨k, hkΓ⟩ x * x⁻¹ ∈ Subgroup.zpowers z := hcomm _ hk x hx
    have hc' : ρ ⟨k', hk'Γ⟩ x * x⁻¹ ∈ Subgroup.zpowers z := hcomm _ hk' x hx
    have hkfix := hfixc ⟨k, hkΓ⟩ (hKG hk) _ hc'
    have key : ρ (⟨k, hkΓ⟩ * ⟨k', hk'Γ⟩) x * x⁻¹ =
        (ρ ⟨k', hk'Γ⟩ x * x⁻¹) * (ρ ⟨k, hkΓ⟩ x * x⁻¹) := by
      have h1 : ρ ⟨k, hkΓ⟩ (ρ ⟨k', hk'Γ⟩ x) =
          ρ ⟨k, hkΓ⟩ (ρ ⟨k', hk'Γ⟩ x * x⁻¹) * ρ ⟨k, hkΓ⟩ x := by
        rw [← map_mul, inv_mul_cancel_right]
      rw [map_mul, MulAut.mul_apply, h1, hkfix, mul_assoc]
    rw [key, valOne_mul hz (eq_one_or_of_mem_zpowers hz hc') (eq_one_or_of_mem_zpowers hz hc),
      add_comm]
  · intro x hx x' hx' k hk
    have hkΓ := hKΓ hk
    rw [hpr (x * x') ⟨k, hkΓ⟩, hpr x ⟨k, hkΓ⟩, hpr x' ⟨k, hkΓ⟩]
    have key : ρ ⟨k, hkΓ⟩ (x * x') * (x * x')⁻¹ =
        (ρ ⟨k, hkΓ⟩ x * x⁻¹) * (ρ ⟨k, hkΓ⟩ x' * x'⁻¹) := by
      rw [map_mul, mul_inv_rev, mul_comm x'⁻¹ x⁻¹]
      exact mul_mul_mul_comm _ _ _ _
    rw [key]
    exact valOne_mul hz (eq_one_or_of_mem_zpowers hz (hcomm _ hk x hx))
      (eq_one_or_of_mem_zpowers hz (hcomm _ hk x' hx'))
  · intro x hx k hk
    have hkΓ := hKΓ hk
    rw [hpr x ⟨k, hkΓ⟩, hfixc ⟨k, hkΓ⟩ (hKG hk) x hx, mul_inv_cancel]
    exact valOne_eq_zero_iff.2 rfl
  · intro x hx hxB
    obtain ⟨κ, hκ, hne⟩ := hnd1 x hx hxB
    refine ⟨(κ : S24), hκ, ?_⟩
    rw [hpr x κ]
    exact valOne_ne_zero_iff.2 (fun h => hne (mul_inv_eq_one.1 h))
  · intro k hk hk1
    obtain ⟨x, hx, hne⟩ := hnd2 ⟨k, hKΓ hk⟩ hk hk1
    refine ⟨x, hx, ?_⟩
    rw [hpr x ⟨k, hKΓ hk⟩]
    exact valOne_ne_zero_iff.2 (fun h => hne (mul_inv_eq_one.1 h))
  · intro g hg x hx k hk
    have hkΓ := hKΓ hk
    have hk' : (g : S24) * k * (g : S24)⁻¹ ∈ K := hKn _ hg k hk
    have hk'Γ := hKΓ hk'
    have e : (⟨(g : S24) * k * (g : S24)⁻¹, hk'Γ⟩ : ↥Γ) = g * ⟨k, hkΓ⟩ * g⁻¹ := rfl
    rw [hpr (ρ g x) ⟨_, hk'Γ⟩, hpr x ⟨k, hkΓ⟩, e]
    have hc : ρ ⟨k, hkΓ⟩ x * x⁻¹ ∈ Subgroup.zpowers z := hcomm _ hk x hx
    have e1 : ρ (g * ⟨k, hkΓ⟩ * g⁻¹) (ρ g x) = ρ g (ρ ⟨k, hkΓ⟩ x) := by
      rw [map_mul, map_mul, map_inv]
      show ρ g (ρ ⟨k, hkΓ⟩ ((ρ g)⁻¹ (ρ g x))) = _
      rw [MulAut.inv_apply_self]
    have h1 : ρ (g * ⟨k, hkΓ⟩ * g⁻¹) (ρ g x) * (ρ g x)⁻¹ = ρ g (ρ ⟨k, hkΓ⟩ x * x⁻¹) := by
      rw [e1, map_mul, map_inv]
    rw [h1, hfixc g hg _ hc]

end Pairing

end CFSG.Quasithin.H153

module

public import CFSG.Quasithin.Background.G119Basic
public import CFSG.Quasithin.Background.G11BridgeRestrict
public import CFSG.Quasithin.Background.G119Group2

public section

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section General

variable {I : Submodule (ZMod 2) V}

theorem g119_restrictRange_eq_map_subgroupOf {H K : Subgroup (GLV V)} (hHK : H ≤ K)
    (hH : Invariant H I) (hK : Invariant K I) :
    restrictRange H I hH = (H.subgroupOf K).map (restrictHom K I hK) := by
  ext g
  constructor
  · rintro ⟨⟨h, hh⟩, rfl⟩
    exact ⟨⟨h, hHK hh⟩, hh, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨(y : GLV V), hy⟩, rfl⟩

theorem g119_restrictRange_sup_eq {H X : Subgroup (GLV V)} (hH : Invariant H I) (hX : Invariant X I)
    (hK : Invariant (H ⊔ X) I) :
    restrictRange (H ⊔ X) I hK = restrictRange H I hH ⊔ restrictRange X I hX := by
  rw [g119_restrictRange_eq_map_subgroupOf le_sup_left hH hK,
    g119_restrictRange_eq_map_subgroupOf le_sup_right hX hK, ← Subgroup.map_sup]
  have hcod : H.subgroupOf (H ⊔ X) ⊔ X.subgroupOf (H ⊔ X) = ⊤ :=
    codisjoint_iff.1 (Subgroup.codisjoint_subgroupOf_sup H X)
  rw [hcod]
  exact MonoidHom.range_eq_map _

theorem g119_restrictRange_mono {H K : Subgroup (GLV V)} (hHK : H ≤ K) (hH : Invariant H I)
    (hK : Invariant K I) : restrictRange H I hH ≤ restrictRange K I hK := by
  rw [g119_restrictRange_eq_map_subgroupOf hHK hH hK]
  exact Subgroup.map_le_range _ _

theorem g119_restrictEquiv_mul {a b : GLV V} (hab : conjSub (a * b) I = I) (ha : conjSub a I = I)
    (hb : conjSub b I = I) :
    restrictEquiv (a * b) I hab = restrictEquiv a I ha * restrictEquiv b I hb := by
  ext i
  rfl

theorem g119_restrictEquiv_one (h : conjSub (1 : GLV V) I = I) :
    restrictEquiv (1 : GLV V) I h = 1 := by
  ext i
  rfl

theorem g119_restrictEquiv_inv {a : GLV V} (ha : conjSub a I = I) (ha' : conjSub a⁻¹ I = I) :
    restrictEquiv a⁻¹ I ha' = (restrictEquiv a I ha)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← g119_restrictEquiv_mul (by rw [mul_inv_cancel, conjSub_one]) ha ha',
    ← g119_restrictEquiv_one (by rw [conjSub_one])]
  congr 1
  exact mul_inv_cancel a

theorem g119_mem_normalizer_of_involution {G : Type*} [Group G] {S : Subgroup G} {g : G}
    (hg : g * g = 1) (h : ∀ s ∈ S, g * s * g⁻¹ ∈ S) : g ∈ Subgroup.normalizer (S : Set G) := by
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [Subgroup.mem_set_normalizer_iff]
  intro s
  refine ⟨fun hs => h s hs, fun hs => ?_⟩
  have := h _ hs
  have e : g * (g * s * g⁻¹) * g⁻¹ = s := by
    rw [hgi, ← mul_assoc, ← mul_assoc, hg, one_mul, mul_assoc, hg, mul_one]
  rwa [e] at this

end General

@[expose] def G119NatSymAction {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (G : Subgroup (GLV M)) (n : ℕ) : Prop :=
  ∃ (θ : ↥G ≃* Equiv.Perm (Fin n)) (β : ↥(permCore n) →ₗ[ZMod 2] M),
    LinearMap.range β = ⊤ ∧
    (∀ u : ↥(permCore n), β u = 0 ↔ (u = 0 ∨ (Even n ∧ ∀ i, (u : Fin n → ZMod 2) i = 1))) ∧
    (∀ (g : ↥G) (u u' : ↥(permCore n)),
      (u' : Fin n → ZMod 2) = permAct (θ g : Equiv.Perm (Fin n)) (u : Fin n → ZMod 2) →
        β u' = (g : GLV M) (β u)) ∧
    (∀ g : ↥G, Module.finrank (ZMod 2)
      (LinearMap.range ((g : GLV M).toLinearMap - LinearMap.id)) = 1 → (θ g).IsSwap)


namespace G119Ctx

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
  [Finite V] (c : G119Ctx B Γ v₁ W X X₀ L I)

include c

theorem restrictRange_X_normalizes {x : GLV V} (hx : x ∈ X)
    {g : GLV ↥I} (hg : g ∈ restrictRange (normalClosure Γ L) I c.irrPlus.1) :
    restrictEquiv x I (c.conjSub_I hx) * g * (restrictEquiv x I (c.conjSub_I hx))⁻¹ ∈
      restrictRange (normalClosure Γ L) I c.irrPlus.1 := by
  obtain ⟨⟨h, hh⟩, rfl⟩ := hg
  have hxi : x⁻¹ ∈ X := X.inv_mem hx
  have hmem : x * h * x⁻¹ ∈ normalClosure Γ L := c.X_normalizes x hx h hh
  have hK : x * h * x⁻¹ ∈ normalClosure Γ L ⊔ X := Subgroup.mem_sup_left hmem
  have h1 : conjSub (x * h * x⁻¹) I = I := c.irr_sup.1.conjSub_eq hK
  have h2 : conjSub (x * h) I = I := by
    refine c.irr_sup.1.conjSub_eq ((normalClosure Γ L ⊔ X).mul_mem (Subgroup.mem_sup_right hx)
      (Subgroup.mem_sup_left hh))
  have e : restrictEquiv x I (c.conjSub_I hx) * restrictEquiv h I (c.irrPlus.1.conjSub_eq hh) *
      (restrictEquiv x I (c.conjSub_I hx))⁻¹ = restrictEquiv (x * h * x⁻¹) I h1 := by
    rw [← g119_restrictEquiv_inv (c.conjSub_I hx) (c.conjSub_I hxi),
      ← g119_restrictEquiv_mul h2 (c.conjSub_I hx) (c.irrPlus.1.conjSub_eq hh),
      ← g119_restrictEquiv_mul h1 h2 (c.conjSub_I hxi)]
  show restrictEquiv x I (c.conjSub_I hx) * restrictEquiv h I (c.irrPlus.1.conjSub_eq hh) *
      (restrictEquiv x I (c.conjSub_I hx))⁻¹ ∈ _
  rw [e]
  exact restrictEquiv_mem_restrictRange c.irrPlus.1 hmem

theorem restrictEquiv_sq {x : GLV V} (hx : x ∈ X) :
    restrictEquiv x I (c.conjSub_I hx) * restrictEquiv x I (c.conjSub_I hx) = 1 := by
  rw [← g119_restrictEquiv_mul (by rw [c.X_sq hx, conjSub_one]) (c.conjSub_I hx) (c.conjSub_I hx)]
  rw [← g119_restrictEquiv_one (by rw [conjSub_one])]
  congr 1
  exact c.X_sq hx

theorem restrictEquiv_comm {x y : GLV V} (hx : x ∈ X) (hy : y ∈ X) :
    restrictEquiv x I (c.conjSub_I hx) * restrictEquiv y I (c.conjSub_I hy) =
      restrictEquiv y I (c.conjSub_I hy) * restrictEquiv x I (c.conjSub_I hx) := by
  have hxy : x * y ∈ X := X.mul_mem hx hy
  have hyx : y * x ∈ X := X.mul_mem hy hx
  rw [← g119_restrictEquiv_mul (c.conjSub_I hxy) (c.conjSub_I hx) (c.conjSub_I hy),
    ← g119_restrictEquiv_mul (c.conjSub_I hyx) (c.conjSub_I hy) (c.conjSub_I hx)]
  congr 1
  exact c.X_comm hx hy

theorem restrictEquiv_mem_normalizer_H {x : GLV V} (hx : x ∈ X) :
    restrictEquiv x I (c.conjSub_I hx) ∈
      Subgroup.normalizer (restrictRange (normalClosure Γ L) I c.irrPlus.1 : Set (GLV ↥I)) :=
  g119_mem_normalizer_of_involution (c.restrictEquiv_sq hx) fun _ hs =>
    c.restrictRange_X_normalizes hx hs

theorem restrictRange_le_normalizer_H :
    restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1 ≤
      Subgroup.normalizer (restrictRange (normalClosure Γ L) I c.irrPlus.1 : Set (GLV ↥I)) := by
  rw [g119_restrictRange_sup_eq c.irrPlus.1 c.invX c.irr_sup.1]
  refine sup_le Subgroup.le_normalizer ?_
  rintro _ ⟨⟨x, hx⟩, rfl⟩
  exact c.restrictEquiv_mem_normalizer_H hx

theorem restrictEquiv_mem_normalizer_M {x₀ x : GLV V} (hx₀ : x₀ ∈ X) (hx : x ∈ X) :
    restrictEquiv x I (c.conjSub_I hx) ∈
      Subgroup.normalizer ((restrictRange (normalClosure Γ L) I c.irrPlus.1 ⊔
        Subgroup.zpowers (restrictEquiv x₀ I (c.conjSub_I hx₀)) : Subgroup (GLV ↥I)) :
          Set (GLV ↥I)) := by
  refine g119_mem_normalizer_of_involution (c.restrictEquiv_sq hx) fun s hs => ?_
  have hmap : (restrictRange (normalClosure Γ L) I c.irrPlus.1 ⊔
      Subgroup.zpowers (restrictEquiv x₀ I (c.conjSub_I hx₀))).map
        (MulAut.conj (restrictEquiv x I (c.conjSub_I hx))).toMonoidHom ≤
      restrictRange (normalClosure Γ L) I c.irrPlus.1 ⊔
        Subgroup.zpowers (restrictEquiv x₀ I (c.conjSub_I hx₀)) := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      exact Subgroup.mem_sup_left (c.restrictRange_X_normalizes hx hg)
    · rw [MonoidHom.map_zpowers]
      refine Subgroup.zpowers_le.2 ?_
      have hcomm := c.restrictEquiv_comm hx hx₀
      have : (MulAut.conj (restrictEquiv x I (c.conjSub_I hx))).toMonoidHom
          (restrictEquiv x₀ I (c.conjSub_I hx₀)) = restrictEquiv x₀ I (c.conjSub_I hx₀) := by
        show restrictEquiv x I (c.conjSub_I hx) * restrictEquiv x₀ I (c.conjSub_I hx₀) *
          (restrictEquiv x I (c.conjSub_I hx))⁻¹ = _
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [this]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  exact hmap ⟨s, hs, rfl⟩

theorem restrictRange_le_normalizer_M {x₀ : GLV V} (hx₀ : x₀ ∈ X) :
    restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1 ≤
      Subgroup.normalizer ((restrictRange (normalClosure Γ L) I c.irrPlus.1 ⊔
        Subgroup.zpowers (restrictEquiv x₀ I (c.conjSub_I hx₀)) : Subgroup (GLV ↥I)) :
          Set (GLV ↥I)) := by
  rw [g119_restrictRange_sup_eq c.irrPlus.1 c.invX c.irr_sup.1]
  refine sup_le (le_trans le_sup_left Subgroup.le_normalizer) ?_
  rintro _ ⟨⟨x, hx⟩, rfl⟩
  exact c.restrictEquiv_mem_normalizer_M hx₀ hx

theorem mem_or_mul_mem {x₀ : GLV V} (hx₀ : x₀ ∈ X)
    (hcl : restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1 =
      normalClosure (restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1)
        (Subgroup.zpowers (restrictEquiv x₀ I (c.conjSub_I hx₀))))
    {g : GLV ↥I} (hg : g ∈ restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1) :
    g ∈ restrictRange (normalClosure Γ L) I c.irrPlus.1 ∨
      g * restrictEquiv x₀ I (c.conjSub_I hx₀) ∈
        restrictRange (normalClosure Γ L) I c.irrPlus.1 := by
  have hgM : g ∈ restrictRange (normalClosure Γ L) I c.irrPlus.1 ⊔
      Subgroup.zpowers (restrictEquiv x₀ I (c.conjSub_I hx₀)) := by
    have hg' := hg
    rw [hcl] at hg'
    refine (Subgroup.closure_le (restrictRange (normalClosure Γ L) I c.irrPlus.1 ⊔
      Subgroup.zpowers (restrictEquiv x₀ I (c.conjSub_I hx₀)))).2 ?_ hg'
    rintro _ ⟨γ, hγ, l, hl, rfl⟩
    have hlM : l ∈ restrictRange (normalClosure Γ L) I c.irrPlus.1 ⊔
        Subgroup.zpowers (restrictEquiv x₀ I (c.conjSub_I hx₀)) := Subgroup.mem_sup_right hl
    exact (Subgroup.mem_set_normalizer_iff.1 (c.restrictRange_le_normalizer_M hx₀ hγ) l).1 hlM
  exact g119_mem_or_mul_mem_of_sup_zpowers (c.restrictEquiv_sq hx₀)
    (fun n hn => c.restrictRange_X_normalizes hx₀ hn) hgM

end G119Ctx

end G11

end CFSG.Quasithin

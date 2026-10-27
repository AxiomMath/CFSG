module

public import CFSG.Monster.B.Recog.GenericTits

public section

namespace CFSG.Monster.GMS

open CFSG.Monster.B.Recog

structure TitsData {V : Type*} (Γ : SimpleGraph V) (X : Type*) [Group X] [MulAction X V]
    (ι : Type*) where
  v : V
  w : V
  u : ι → V
  Xv : Subgroup X
  Xe : Subgroup X
  Xt : ι → Subgroup X
  hadj : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b)
  hconn : Γ.Preconnected
  hΓ : Triangulable Γ
  hvw : Γ.Adj v w
  hloc : ∀ y, Γ.Adj v y → ∃ g : X, g • v = v ∧ g • w = y
  hswap : ∃ g : X, g • v = w ∧ g • w = v
  hXv : ∀ g, g ∈ Xv ↔ g • v = v
  hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v)
  hXt : ∀ j, ∀ g ∈ Xt j, g • v = v ∨ g • v = w ∨ g • v = u j
  hτ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = v
  hρ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = u j ∧ g • u j = v
  htri : ∀ y₁ y₂, Γ.Adj v y₁ → Γ.Adj y₁ y₂ → Γ.Adj y₂ v →
    ∃ j, ∃ g : X, g • v = v ∧ g • w = y₁ ∧ g • u j = y₂

namespace TitsData

variable {V : Type*} {Γ : SimpleGraph V} {X : Type*} [Group X] [MulAction X V] {ι : Type*}

theorem existsUnique_hom (D : TitsData Γ X ι) {Y : Type*} [Group Y] (φv : D.Xv →* Y)
    (φe : D.Xe →* Y) (φt : ∀ j, D.Xt j →* Y)
    (hve : ∀ a (ha : a ∈ D.Xv) (hb : a ∈ D.Xe), φv ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hvt : ∀ j a (ha : a ∈ D.Xv) (hb : a ∈ D.Xt j), φv ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ D.Xe) (hb : a ∈ D.Xt j), φe ⟨a, ha⟩ = φt j ⟨a, hb⟩) :
    ∃! Φ : X →* Y, (∀ a : D.Xv, Φ a = φv a) ∧ (∀ a : D.Xe, Φ a = φe a) ∧
      ∀ j (a : D.Xt j), Φ a = φt j a :=
  tits_universal_completion D.hadj D.hconn D.hΓ D.hvw D.hloc D.hswap D.Xv D.Xe D.hXv D.hXe D.u
    D.Xt D.hXt D.hτ D.hρ D.htri φv φe φt hve hvt het

theorem hom_eq_id (D : TitsData Γ X ι) (Φ : X →* X) (hv : ∀ a : D.Xv, Φ a = a)
    (he : ∀ a : D.Xe, Φ a = a) (ht : ∀ j (a : D.Xt j), Φ a = a) : Φ = MonoidHom.id X := by
  obtain ⟨Ψ, -, hΨ⟩ := D.existsUnique_hom D.Xv.subtype D.Xe.subtype (fun j => (D.Xt j).subtype)
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  rw [hΨ Φ ⟨hv, he, ht⟩, hΨ (MonoidHom.id X) ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩]

end TitsData

theorem nonempty_mulEquiv_of_amalgam {V V' : Type*} {Γ : SimpleGraph V} {Γ' : SimpleGraph V'}
    {X X' : Type*} [Group X] [Group X'] [MulAction X V] [MulAction X' V'] {ι : Type*}
    (D : TitsData Γ X ι) (D' : TitsData Γ' X' ι)
    (σv : D.Xv ≃* D'.Xv) (σe : D.Xe ≃* D'.Xe) (σt : ∀ j, D.Xt j ≃* D'.Xt j)
    (hve : ∀ a (ha : a ∈ D.Xv) (hb : a ∈ D.Xe), (σv ⟨a, ha⟩ : X') = σe ⟨a, hb⟩)
    (hvt : ∀ j a (ha : a ∈ D.Xv) (hb : a ∈ D.Xt j), (σv ⟨a, ha⟩ : X') = σt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ D.Xe) (hb : a ∈ D.Xt j), (σe ⟨a, ha⟩ : X') = σt j ⟨a, hb⟩)
    (hve' : ∀ a (ha : a ∈ D'.Xv) (hb : a ∈ D'.Xe), (σv.symm ⟨a, ha⟩ : X) = σe.symm ⟨a, hb⟩)
    (hvt' : ∀ j a (ha : a ∈ D'.Xv) (hb : a ∈ D'.Xt j),
      (σv.symm ⟨a, ha⟩ : X) = (σt j).symm ⟨a, hb⟩)
    (het' : ∀ j a (ha : a ∈ D'.Xe) (hb : a ∈ D'.Xt j),
      (σe.symm ⟨a, ha⟩ : X) = (σt j).symm ⟨a, hb⟩) :
    Nonempty (X ≃* X') := by
  obtain ⟨Φ, ⟨hΦv, hΦe, hΦt⟩, -⟩ := D.existsUnique_hom
    (D'.Xv.subtype.comp σv.toMonoidHom) (D'.Xe.subtype.comp σe.toMonoidHom)
    (fun j => (D'.Xt j).subtype.comp (σt j).toMonoidHom) hve hvt het
  obtain ⟨Ψ, ⟨hΨv, hΨe, hΨt⟩, -⟩ := D'.existsUnique_hom
    (D.Xv.subtype.comp σv.symm.toMonoidHom) (D.Xe.subtype.comp σe.symm.toMonoidHom)
    (fun j => (D.Xt j).subtype.comp (σt j).symm.toMonoidHom) hve' hvt' het'
  have hΨΦ : Ψ.comp Φ = MonoidHom.id X := by
    refine D.hom_eq_id _ (fun a => ?_) (fun a => ?_) (fun j a => ?_)
    · have h1 : Φ a = (σv a : X') := hΦv a
      have h2 := hΨv (σv a)
      simp only [MonoidHom.coe_comp, Function.comp_apply, h1]
      rw [h2]
      simp
    · have h1 : Φ a = (σe a : X') := hΦe a
      have h2 := hΨe (σe a)
      simp only [MonoidHom.coe_comp, Function.comp_apply, h1]
      rw [h2]
      simp
    · have h1 : Φ a = (σt j a : X') := hΦt j a
      have h2 := hΨt j (σt j a)
      simp only [MonoidHom.coe_comp, Function.comp_apply, h1]
      rw [h2]
      simp
  have hΦΨ : Φ.comp Ψ = MonoidHom.id X' := by
    refine D'.hom_eq_id _ (fun a => ?_) (fun a => ?_) (fun j a => ?_)
    · have h1 : Ψ a = (σv.symm a : X) := hΨv a
      have h2 := hΦv (σv.symm a)
      simp only [MonoidHom.coe_comp, Function.comp_apply, h1]
      rw [h2]
      simp
    · have h1 : Ψ a = (σe.symm a : X) := hΨe a
      have h2 := hΦe (σe.symm a)
      simp only [MonoidHom.coe_comp, Function.comp_apply, h1]
      rw [h2]
      simp
    · have h1 : Ψ a = ((σt j).symm a : X) := hΨt j a
      have h2 := hΦt j ((σt j).symm a)
      simp only [MonoidHom.coe_comp, Function.comp_apply, h1]
      rw [h2]
      simp
  exact ⟨MulEquiv.ofBijective Φ ⟨fun x y h => by
      have := congrArg Ψ h
      simpa [← MonoidHom.comp_apply, hΨΦ] using this,
    fun y => ⟨Ψ y, by simpa using DFunLike.congr_fun hΦΨ y⟩⟩⟩

end CFSG.Monster.GMS

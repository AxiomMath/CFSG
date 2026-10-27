module

public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Vol2.Ch10SecALiftMain
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

structure NatData (L W : Subgroup G) where
  ρ : ↥L →* L3.Γ
  b : G → L3.Vec
  ρ_surj : Function.Surjective ρ
  ker_ρ : ∀ l : ↥L, ρ l = 1 ↔ (l : G) ∈ Subgroup.centralizer (W : Set G)
  b_mul : ∀ a₁ ∈ W, ∀ a₂ ∈ W, b (a₁ * a₂) = b a₁ + b a₂
  b_inj : ∀ a₁ ∈ W, ∀ a₂ ∈ W, b a₁ = b a₂ → a₁ = a₂
  b_surj : ∀ x, ∃ a ∈ W, b a = x
  equi : ∀ l : ↥L, ∀ a ∈ W, b ((l : G) * a * (l : G)⁻¹) = L3.act (ρ l) (b a)

theorem exists_natData {L W : Subgroup G} [IsMulCommutative ↥W]
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hnat : BinaryNaturalSL (V := ↥W) (autOn L W) ⊤ ⊥ 3 1) : Nonempty (NatData L W) := by
  classical
  obtain ⟨D⟩ := hnat.toL3Coord
  set πe : L3.Γ ≃* ↥(autOn L W) := MulEquiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩ with hπe
  set ρ : ↥L →* L3.Γ := πe.symm.toMonoidHom.comp (SecA.autOnHomOf hLW) with hρ
  have hρrho : ∀ l : ↥L, D.rho (ρ l) = (SecA.autOnHomOf hLW l : MulAut ↥W) := by
    intro l
    show ((D.π (πe.symm (SecA.autOnHomOf hLW l)) : ↥(autOn L W)) : MulAut ↥W) = _
    rw [show D.π (πe.symm (SecA.autOnHomOf hLW l)) = πe (πe.symm (SecA.autOnHomOf hLW l)) from rfl,
      MulEquiv.apply_symm_apply]
  have hβinj : Function.Injective D.β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 := (D.ker_β u).mp hu
    rw [Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  set b : G → L3.Vec := fun a =>
    if h : a ∈ W then Multiplicative.toAdd (D.β ⟨⟨a, h⟩, trivial⟩) else 0 with hb
  have hbW : ∀ a (h : a ∈ W), b a = Multiplicative.toAdd (D.β ⟨⟨a, h⟩, trivial⟩) :=
    fun a h => by rw [hb]; simp only [h, ↓reduceDIte]
  refine ⟨⟨ρ, b, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact πe.symm.surjective.comp (SecA.autOnHomOf_surjective hLW)
  · intro l
    rw [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    constructor
    · intro h
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 := SecA.autOnHomOf_apply hLW l ⟨a, ha⟩
      rw [h] at h1
      have h2 : (a : G) = l * a * (l : G)⁻¹ := h1
      calc a * (l : G) = l * a * (l : G)⁻¹ * l := by rw [← h2]
        _ = l * a := by group
    · intro h
      apply Subtype.ext
      ext ⟨a, ha⟩
      rw [SecA.autOnHomOf_apply]
      show (l : G) * a * (l : G)⁻¹ = a
      rw [← Subgroup.mem_centralizer_iff.mp h a ha, mul_inv_cancel_right]
  · intro a₁ h₁ a₂ h₂
    rw [hbW _ h₁, hbW _ h₂, hbW _ (W.mul_mem h₁ h₂), ← toAdd_mul, ← map_mul]
    rfl
  · intro a₁ h₁ a₂ h₂ h
    rw [hbW _ h₁, hbW _ h₂] at h
    have := hβinj (Multiplicative.toAdd.injective h)
    exact congrArg (fun u : ↥(⊤ : Subgroup ↥W) => ((u : ↥W) : G)) this
  · intro x
    obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd x)
    refine ⟨((u : ↥W) : G), (u : ↥W).2, ?_⟩
    rw [hbW _ (u : ↥W).2, show (⟨⟨((u : ↥W) : G), (u : ↥W).2⟩, trivial⟩ :
      ↥(⊤ : Subgroup ↥W)) = u from rfl, hu, toAdd_ofAdd]
  · intro l a ha
    have hla : (l : G) * a * (l : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hLW l.2) a).mp ha
    have h1 := D.β_rho (ρ l) ⟨a, ha⟩ trivial trivial
    have e1 : D.rho (ρ l) ⟨a, ha⟩ = ⟨(l : G) * a * (l : G)⁻¹, hla⟩ := by
      rw [hρrho]
      exact Subtype.ext (SecA.autOnHomOf_apply hLW l ⟨a, ha⟩)
    rw [hbW _ hla, hbW _ ha]
    rw [e1] at h1
    rw [h1, toAdd_ofAdd]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

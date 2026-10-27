module

public import CFSG.Quasithin.Vol2.GoldschmidtSevenInner
public import CFSG.Quasithin.Vol2.GoldschmidtJ4SevenDef
public import CFSG.Quasithin.Vol2.Ch1Sec3L42J4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4IsPSL

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Blueprint

theorem sl4_of_isPSL {X : Type} [Group X] (h : IsPSL 4 2 1 X) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  obtain ⟨e⟩ := CFSG.Quasithin.J4L4.alt8_of_isPSL h
  exact ⟨e.trans (CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.trans
    (CFSG.QuasithinUnique.Setup.Family.slEquivGL 4).symm)⟩

theorem factJ4L42Inner_of_notReal (h : J4SevenNotReal) :
    L139L42.FactJ4L42Inner := by
  intro X _ _ hX B hB t ht
  obtain ⟨e⟩ := sl4_of_isPSL hB
  let ρ : ↥B →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥B))
  have hρ : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = CFSG.pCore 2 ↥B := by
    ext y
    simp [ρ]
  obtain ⟨y₀, hy₀⟩ := Seven.innerOn_of_not_real (card_not_dvd_forty_nine hX)
    (fun x g hx => h X hX x g hx) (Y := B) (Or.inr rfl) ρ hρ
    (hker ▸ CFSG.pCore_isPGroup) ht
  refine ⟨y₀, y₀.2, fun x hx => ?_⟩
  have htB : t * x * t⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 ht x).1 hx
  have h1 := hy₀ ⟨x, hx⟩ ⟨t * x * t⁻¹, htB⟩ rfl
  have h2 : (⟨t * x * t⁻¹, htB⟩ : ↥B)⁻¹ * (y₀ * ⟨x, hx⟩ * y₀⁻¹) ∈ CFSG.pCore 2 ↥B := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  have h3 : (⟨t * x * t⁻¹, htB⟩ : ↥B)⁻¹ * (y₀ * ⟨x, hx⟩ * y₀⁻¹) ∈ CFSG.Open.pCore 2 ↥B := by
    exact h2
  refine ⟨_, h3, ?_⟩
  simp [mul_assoc]

end CFSG.Quasithin.H13

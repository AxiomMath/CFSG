module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UPlane
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UData

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

@[expose] def UPlaneToralAt
    (τ : Tag) (p : ℕ) (K : Type) [Field K] [Finite K] : Prop :=
  ∀ E : Subgroup ↥(adjointGroup τ K), IsElemAbelian p E → Nat.card E = p ^ 2 →
    ∃ g ∈ adjointGroup τ (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g ∈
        torusGroup τ (AlgebraicClosure K)

theorem exists_uframe_untwD
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {X : Type} [Group X] {G₀ B D : Subgroup X} {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) τ (2 ^ f))
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hin : ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X))
    (hfaith : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) (hBel : IsElemAbelian p B)
    (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2)
    (htorD : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f → UPlaneToralAt τ p K) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (S : LangSetup τ (AlgebraicClosure K) 5) (fr : GGTCUFrame S.Γ G₀ B), S.D.q = 2 ^ f ∧
      (∃ w : WeylGroup τ, ∀ γ, IsRoot τ γ → S.ρ γ = w • γ) ∧ fr.DLang D ≤ S.D.torus := by
  classical
  obtain ⟨K, instF, instFin, hKcard, ⟨eK⟩⟩ := hmod
  haveI : CharP K 2 := charP_two_of_finite_field_card_two_pow hKcard
  have hZadj : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  let θ : (↥G₀ ⧸ Subgroup.center ↥G₀) ≃* ↥(adjointGroup τ K) :=
    eK.trans ((QuotientGroup.quotientMulEquivOfEq hZadj).trans QuotientGroup.quotientBot)
  have hcl : Subgroup.center (↥G₀ ⧸ Subgroup.center ↥G₀) = ⊥ := by
    have h1 := Subgroup.map_center_eq θ
    rw [hZadj] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ θ.injective).1 h1
  obtain ⟨ν, hνinj, hνact⟩ := exists_inner_hom_of_faithful_inner hBN hin hfaith hcl
  set E : Subgroup ↥(adjointGroup τ K) := ((D.subgroupOf B).map ν).map θ.toMonoidHom with hE
  have hDsub : D.subgroupOf B ≤ B.subgroupOf B := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hDB hx
  have hEel : IsElemAbelian p E := by
    have h1 : IsElemAbelian p (B.subgroupOf B) := hBel.subgroupOf B
    exact ((h1.mono hDsub).map ν).map θ.toMonoidHom
  have hEcard : Nat.card E = p ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective θ.injective, Subgroup.card_map_of_injective hνinj,
      ← hDcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv
  obtain ⟨S, ι, hq, ⟨Fr, hFr1, hFr2⟩, ⟨w, hn⟩, hinj, hrange, hEtor⟩ :=
    exists_langSetup_of_tcPlane hτ hKcard hp hp2 E (fun x hx => hEel.2 x hx)
      (htorD K hKcard E hEel hEcard)
  let fr : GGTCUFrame S.Γ G₀ B :=
    ⟨ν, hνinj, hνact, θ.trans ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))⟩
  refine ⟨K, instF, instFin, inferInstance, S, fr, hq, ⟨w, fun γ hγ => ?_⟩, ?_⟩
  · exact S.rho_eq_smul_of_frob (Fr := Fr) hFr1 hFr2 hn hγ
  · rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact hEtor _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩

end CFSG.StandardType.TableCRes

end

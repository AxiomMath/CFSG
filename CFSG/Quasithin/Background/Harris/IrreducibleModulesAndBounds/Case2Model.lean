module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case2Rank
public import CFSG.Quasithin.Background.H12OneHatM22PfIrr

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Blueprint CFSG.CharacterTheory.SteinbergBY
  CFSG.Quasithin.HatM22

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem isHat_toMulSub {L : Subgroup (GLV V)} {S : Type} [Group S]
    (hq : CFSG.Open.IsQuasisimple ↥L) (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* S) : IsHat ↥(toMulSub L) S := by
  refine ⟨isQuasisimple_toMulSub hq, ?_, ⟨cqEquiv_toMulSub_comp e⟩⟩
  rw [← hZ]
  exact (Nat.card_congr (Subgroup.centerCongr (toMulSubEquiv L)).toEquiv).symm

theorem isHat_of_hyp {L : Subgroup (GLV V)} {S : Type} [Group S]
    (hq : CFSG.Open.IsQuasisimple ↥L) (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* S) : IsHat ↥L S :=
  ⟨(CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hq, hZ, ⟨e⟩⟩

theorem isIrrSec_of_isIrrOn {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (h : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L) : XMod.IsIrrSec ↥L (⊥ : Subgroup W) ⊤ := by
  obtain ⟨hnt, hJ⟩ := h
  refine ⟨?_, fun J hJi _ _ => hJ J (fun g hg u hu => ?_)⟩
  · obtain ⟨x, hx⟩ := exists_ne (1 : W)
    refine lt_of_le_of_ne bot_le fun h => hx ?_
    have : x ∈ (⊤ : Subgroup W) := trivial
    rw [← h] at this
    simpa using this
  · have := hJi ⟨g, hg⟩ u hu
    simpa [Subgroup.smul_def, MulAut.smul_def] using this

variable [Finite V]

theorem case2_model
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M22)
    (hZ : Nat.card (Subgroup.center ↥L) = 3) :
    Module.finrank (ZMod 2) V = 12 ∧
      ∃ ψ : V ≃ₗ[ZMod 2] (Fin 6 → FieldFour), ∀ k ∈ L, ∃ γ : ↥hatM22Γ₀, ∀ v : V,
        ψ (k v) = (((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour)).mulVec (ψ v) := by
  obtain ⟨hm5, -⟩ := case2_rank h e
  have hd : Module.finrank (ZMod 2) V ≤ 12 := by have := h.bound; omega
  have hHat := isHat_toMulSub h.L_comp.2.2 hZ e
  have hirr := isIrrSec_of_isIrrOn (isIrrOn_toMulSub h.H_irr)
  have hcard : Nat.card (Multiplicative V) < 2 ^ 30 := by
    rw [natCard_multiplicative]
    calc 2 ^ Module.finrank (ZMod 2) V ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hd
      _ < 2 ^ 30 := by norm_num
  have hV2 : ∀ v : Multiplicative V, v ^ 2 = 1 := fun v => by
    rw [pow_two]; exact mul_self_eq_one_multiplicative v
  obtain ⟨π, hπ⟩ := hatM22SmallModules_holds (Multiplicative V) hV2 (toMulSub L) hHat hirr hcard
  have hc := CFSG.Quasithin.H.Mathieu.H12Pf.card_eq_of_realizesVia hπ
  rw [natCard_multiplicative, FieldFour.natCard_eq, Fintype.card_fin] at hc
  have hd12 : Module.finrank (ZMod 2) V = 12 := by
    have : (2 : ℕ) ^ Module.finrank (ZMod 2) V = 2 ^ 12 := by rw [hc]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  refine ⟨hd12, ?_⟩
  obtain ⟨E, hE⟩ := CFSG.Quasithin.H.Mathieu.H12Pf.exists_coord_of_realizesVia hπ
  have hc2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  let ψ : V ≃ₗ[ZMod 2] (Fin 6 → FieldFour) :=
    { toFun := fun v => Multiplicative.toAdd (E (Multiplicative.ofAdd v))
      invFun := fun x => Multiplicative.toAdd (E.symm (Multiplicative.ofAdd x))
      left_inv := fun v => by simp
      right_inv := fun x => by simp
      map_add' := fun a b => by simp [ofAdd_add]
      map_smul' := fun c v => by
        rcases hc2 c with rfl | rfl <;> simp }
  refine ⟨ψ, fun k hk => ?_⟩
  have hg' : linEquivMulAut k ∈ toMulSub L := linEquivMulAut_mem_toMulSub.2 hk
  obtain ⟨γ, hγ⟩ := hπ.1 ⟨linEquivMulAut k, hg'⟩
  refine ⟨γ, fun v => ?_⟩
  have h2 : ψ (k v) = Multiplicative.toAdd (E (((π γ : ↥(toMulSub L)) :
      MulAut (Multiplicative V)) (Multiplicative.ofAdd v))) :=
    congrArg (fun x : ↥(toMulSub L) => Multiplicative.toAdd (E ((x : MulAut (Multiplicative V))
      (Multiplicative.ofAdd v)))) hγ.symm
  exact h2.trans (hE γ _)

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

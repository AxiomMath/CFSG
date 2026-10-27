module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.Quasithin.Background.G11Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem isIrrOn_toMulSub {L : Subgroup (GLV V)} (h : IsIrr L ⊤) :
    CFSG.QuasithinUnique.Setup.X1.IsIrrOn (toMulSub L) := by
  obtain ⟨-, hlt, hJ⟩ := h
  refine ⟨?_, fun U hU => ?_⟩
  · obtain ⟨b, -, hb⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (bot_lt_iff_ne_bot.1 hlt).symm.symm
    exact ⟨⟨Multiplicative.ofAdd b, 1, fun h => hb (by simpa using h)⟩⟩
  · have hinv : Invariant L (subToSubgroup.symm U) := fun k hk u hu =>
      hU (linEquivMulAut k) (linEquivMulAut_mem_toMulSub.2 hk) (Multiplicative.ofAdd u) hu
    rcases hJ _ hinv bot_le le_top with h1 | h1
    · left
      rw [← subToSubgroup.apply_symm_apply U, h1]
      exact map_bot _
    · right
      rw [← subToSubgroup.apply_symm_apply U, h1]
      exact map_top _

theorem isElemAbelian2_toMulSub {A : Subgroup (GLV V)} (hA : CFSG.Open.IsElemAbelian 2 A) :
    CFSG.Quasithin.IsElemAbelian2 (toMulSub A) := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨h, hh, rfl⟩ := hb
    have := hA.1.is_comm.comm (⟨g, hg⟩ : ↥A) ⟨h, hh⟩
    have h2 := congrArg (fun x : ↥A => linEquivMulAut (x : GLV V)) this
    simpa using h2
  · obtain ⟨g, hg, rfl⟩ := ha
    have := hA.2 g hg
    show linEquivMulAut g ^ 2 = 1
    rw [← map_pow, this, map_one]

theorem natCard_toMulSub (K : Subgroup (GLV V)) : Nat.card ↥(toMulSub K) = Nat.card ↥K :=
  Nat.card_congr (toMulSubEquiv K).toEquiv.symm

theorem natCard_multiplicative [Finite V] :
    Nat.card (Multiplicative V) = 2 ^ Module.finrank (ZMod 2) V := by
  have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  rw [Nat.card_zmod] at this
  exact this

theorem toMulSub_le_normalizer {Γ H A : Subgroup (GLV V)}
    (hHn : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hA : A ≤ Γ) :
    toMulSub A ≤ Subgroup.normalizer (toMulSub H : Set (MulAut (Multiplicative V))) := by
  rintro _ ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro f
  obtain ⟨h, rfl⟩ := linEquivMulAut.surjective f
  have e : (linEquivMulAut.toMonoidHom γ) * linEquivMulAut h * (linEquivMulAut.toMonoidHom γ)⁻¹
      = linEquivMulAut (γ * h * γ⁻¹) := by simp
  show linEquivMulAut h ∈ toMulSub H ↔ _
  rw [e, linEquivMulAut_mem_toMulSub,
    linEquivMulAut_mem_toMulSub]
  constructor
  · exact hHn γ (hA hγ) h
  · intro hh
    have := hHn γ⁻¹ (Γ.inv_mem (hA hγ)) _ hh
    simpa [mul_assoc] using this

theorem map_center_toMulSubEquiv (L : Subgroup (GLV V)) :
    (Subgroup.center ↥L).map (toMulSubEquiv L : ↥L →* ↥(toMulSub L)) =
      Subgroup.center ↥(toMulSub L) :=
  Subgroup.map_center_eq (toMulSubEquiv L)

noncomputable def cqEquiv_toMulSub (L : Subgroup (GLV V)) :
    (↥(toMulSub L) ⧸ Subgroup.center ↥(toMulSub L)) ≃* (↥L ⧸ Subgroup.center ↥L) :=
  QuotientGroup.congr _ _ (toMulSubEquiv L).symm (by
    rw [← map_center_toMulSubEquiv L]
    exact (Subgroup.map_symm_eq_iff_map_eq _).2 rfl)

noncomputable def cqEquiv_toMulSub_comp {L : Subgroup (GLV V)} {S : Type*} [Group S]
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* S) :
    CFSG.QuasithinUnique.Setup.Family.CQ (toMulSub L) ≃* S :=
  (cqEquiv_toMulSub L).trans e

theorem isQuasisimple_toMulSub {L : Subgroup (GLV V)} (h : CFSG.Open.IsQuasisimple ↥L) :
    CFSG.IsQuasisimple ↥(toMulSub L) := by
  obtain ⟨hp, hs⟩ := h
  have hc := map_center_toMulSubEquiv L
  have e' := cqEquiv_toMulSub L
  have h' : CFSG.Open.IsQuasisimple ↥(toMulSub L) := by
    refine ⟨?_, e'.isSimpleGroup⟩
    rw [_root_.commutator_def] at hp ⊢
    rw [← Subgroup.map_top_of_surjective (toMulSubEquiv L : ↥L →* ↥(toMulSub L))
      (toMulSubEquiv L).surjective, ← Subgroup.map_commutator, hp]
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 h'

theorem exists_mulaut_data [Finite V] {Γ A L : Subgroup (GLV V)} {m : ℕ}
    (hLn : ∀ γ ∈ Γ, ∀ l ∈ L, γ * l * γ⁻¹ ∈ L) (hAΓ : A ≤ Γ)
    (hAe : CFSG.Open.IsElemAbelian 2 A) (hAc : Nat.card ↥A = 2 ^ m) (hirr : IsIrr L ⊤) :
    toMulSub A ≤ Subgroup.normalizer (toMulSub L : Set (MulAut (Multiplicative V))) ∧
      CFSG.Quasithin.IsElemAbelian2 (toMulSub A) ∧ Nat.card ↥(toMulSub A) = 2 ^ m ∧
      CFSG.QuasithinUnique.Setup.X1.IsIrrOn (toMulSub L) :=
  ⟨toMulSub_le_normalizer hLn hAΓ, isElemAbelian2_toMulSub hAe,
    (natCard_toMulSub A).trans hAc, isIrrOn_toMulSub hirr⟩

theorem two_pow_card_fixedSpace (A : Subgroup (GLV V)) :
    Nat.card ↥(CFSG.Quasithin.fixV (toMulSub A)) = Nat.card ↥(fixedSpace A) := by
  rw [fixV_toMulSub, natCard_subToSubgroup]

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

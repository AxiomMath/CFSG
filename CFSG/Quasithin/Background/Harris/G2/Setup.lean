module

public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.OneCompActions
public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic

public section

namespace CFSG.Quasithin.G11.Harris.G2

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def cayleyEquiv {F F' : Type} [Field F] [Field F'] (e : F ≃+* F') :
    ↥(cayleyGroup F) ≃* ↥(cayleyGroup F') :=
  ((zornConj e).subgroupMap (cayleyGroup F)).trans (MulEquiv.subgroupCongr (map_cayleyGroup e))

@[expose] noncomputable def repC {F : Type} [Field F] (L : Subgroup (GLV V))
    (e : ↥L ≃* ↥(cayleyGroup F)) : Representation (ZMod 2) ↥(cayleyGroup F) V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (L.subtype.comp e.symm.toMonoidHom)

theorem repC_apply {F : Type} [Field F] (L : Subgroup (GLV V)) (e : ↥L ≃* ↥(cayleyGroup F))
    (g : ↥(cayleyGroup F)) (v : V) : repC L e g v = ((e.symm g : ↥L) : GLV V) v := rfl

theorem repC_isIrreducible {F : Type} [Field F] {L : Subgroup (GLV V)}
    (e : ↥L ≃* ↥(cayleyGroup F)) (hL : IsIrr L ⊤) : (repC L e).IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  obtain ⟨-, hlt, hirr⟩ := hL
  refine ⟨?_, fun U hU => ?_⟩
  · obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hlt
    exact ⟨⟨v, 0, fun h => hv (h ▸ Submodule.zero_mem _)⟩⟩
  · have hinv : CFSG.Quasithin.G11.Invariant L U := fun l hl u hu => by
      have := hU (e ⟨l, hl⟩) u hu
      simpa [repC_apply] using this
    exact hirr U hinv bot_le le_top

theorem repC_toHomUnits_injective {F : Type} [Field F] (L : Subgroup (GLV V))
    (e : ↥L ≃* ↥(cayleyGroup F)) : Function.Injective (repC L e).toHomUnits := by
  intro g h hgh
  have h1 : ∀ v, repC L e g v = repC L e h v := fun v => by
    have := congrArg (fun u : (Module.End (ZMod 2) V)ˣ => (u : Module.End (ZMod 2) V) v) hgh
    simpa using this
  have h2 : (e.symm g : ↥L) = e.symm h :=
    Subtype.ext (LinearEquiv.ext fun v => h1 v)
  exact e.symm.injective h2

theorem repC_nontrivial {F : Type} [Field F] (L : Subgroup (GLV V)) (e : ↥L ≃* ↥(cayleyGroup F))
    [Nontrivial ↥(cayleyGroup F)] : ∃ g, repC L e g ≠ 1 := by
  obtain ⟨g, hg⟩ := exists_ne (1 : ↥(cayleyGroup F))
  refine ⟨g, fun h => hg ?_⟩
  apply repC_toHomUnits_injective L e
  ext v
  simp [h]

theorem m_le_of_autRank [Finite V] {Γ A L : Subgroup (GLV V)} {m : ℕ}
    (hs : OneCompSetting Γ A L m) {S : Type} [Group S] (e : ↥L ≃* S) {r : ℕ}
    (hr : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r) : m ≤ r := by
  let ψ' : ↥A →* MulAut S :=
    (MulAut.congr e).toMonoidHom.comp (CFSG.Quasithin.Background.Harris.OrdinaryProofs.oneCompConjHom hs)
  have hinj' : Function.Injective ψ' :=
    (MulAut.congr e).injective.comp
      (CFSG.Quasithin.Background.Harris.OrdinaryProofs.oneCompConjHom_injective hs)
  have hcard : Nat.card ψ'.range = 2 ^ m := by
    rw [← hs.A_card]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv).symm
  have hcomm : ∀ x ∈ ψ'.range, ∀ y ∈ ψ'.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact hs.A_elem.1.is_comm.comm a b
  have hsq : ∀ x ∈ ψ'.range, x * x = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have := hs.A_elem.2 (a : GLV V) a.2
    have h3 : a * a = 1 := Subtype.ext (by simpa [sq] using this)
    rw [h3, map_one]
  have := hr _ hcomm hsq
  rw [hcard] at this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

theorem finrank_eq_mul_of_card [Finite V] {D : Type*} [Field D] [Module D V] {d : ℕ}
    (hD : Nat.card D = 2 ^ d) : Module.finrank (ZMod 2) V = d * Module.finrank D V := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have : Module.Finite D V := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  have h2 := Module.natCard_eq_pow_finrank (K := D) (V := V)
  rw [Nat.card_zmod] at h1
  rw [hD, ← pow_mul] at h2
  rw [h1] at h2
  exact Nat.pow_right_injective le_rfl h2

theorem concl_of_case10 {Γ H : Subgroup (GLV V)} {m : ℕ} (h : G93Case10 H m) :
    G93Concl Γ H m := by
  unfold G93Concl
  iterate 10 right
  left
  exact h

theorem exists_equiv_cayley {X : Type} [Group X] {f : ℕ}
    (h : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 f) :
    2 ≤ f ∧ Nonempty (X ≃* ↥(cayleyGroup (GaloisField 2 f))) := by
  obtain ⟨hf, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.Quasithin.B42G2Id.exists_cayleyGroup_of_chevalleyExceptionalModel h
  refine ⟨hf, ⟨e.trans (cayleyEquiv ?_)⟩⟩
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  refine FiniteField.ringEquivOfCardEq ?_
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
    GaloisField.card 2 f (by omega)]

end CFSG.Quasithin.G11.Harris.G2

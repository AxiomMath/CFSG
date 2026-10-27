module

public import CFSG.Quasithin.Background.Harris.Sp4.Setup
public import CFSG.Quasithin.Background.Harris.Interfaces

public section

namespace CFSG.Quasithin.G11.Harris.Sp4

open CFSG.Open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section Outer

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem outer_cyclic_card {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    IsCyclic (Outer (antiSp K)) ∧ Nat.card (Outer (antiSp K)) = 2 * f := by
  obtain ⟨Fr, hFr, hord, hzp⟩ := exists_frobenius_data (by omega) hK
  obtain ⟨-, -, -, -, hcyc, hcard, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure
      (by omega) hFr hord hzp
  let eO := CFSG.ComponentClassification.OuterAutomorphisms.equivalence (antiProjEquiv K)
  refine ⟨isCyclic_of_surjective eO.symm.toMonoidHom eO.symm.surjective, ?_⟩
  rw [Nat.card_congr eO.toEquiv]
  exact hcard

theorem card_le_of_fixed_even {f : ℕ} (hf : 2 ≤ f) (hev : Even f) (hK : Nat.card K = 2 ^ f)
    (θ : MulAut (antiSp K)) (hθ : θ * θ = 1) (hout : θ ∉ inner (antiSp K))
    (E : Subgroup (antiSp K)) (hE : E ≤ fixedSubgroup θ) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 ^ (3 * (f / 2)) := by
  obtain ⟨c, hc⟩ := outer_involution_conj hf hK θ hθ hout
  obtain ⟨m, rfl⟩ := hev
  have hm : 1 ≤ m := by omega
  have h2m : m + m = 2 * m := by ring
  rw [h2m] at hK hc ⊢
  rw [show 2 * m / 2 = m by omega]
  exact rank_bound_of_conj c hc (b := 2 ^ (3 * m))
    (fun E' hE' hsq' => even_rank_bound hm hK E' hE' hsq') E hE hsq

end Outer

section Offender

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {M : Type} [AddCommGroup M]
  [Module (ZMod 2) M] {π : antiSp K →* (M ≃ₗ[ZMod 2] M)} {A : Subgroup (M ≃ₗ[ZMod 2] M)}

theorem card_le_of_offender {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (H : Offender π A) :
    Nat.card A ≤ 2 ^ (3 * f + 1) ∧ (Even f → Nat.card A ≤ 2 ^ (3 * f)) ∧
      ((∀ a : A, normAut π H.inj A H.norm a ∈ inner (antiSp K)) → Nat.card A ≤ 2 ^ (3 * f)) := by
  classical
  obtain ⟨hcyc, hcard⟩ := outer_cyclic_card hf hK
  have : Finite (Outer (antiSp K)) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  set Ψ := outerHom π A H.inj H.norm with hΨ
  have hcardA := H.card_eq
  have hq := H.card_range_le_two hcyc
  set Ê : Subgroup (antiSp K) := A.comap π with hÊ
  have hÊsq : ∀ x ∈ Ê, x * x = 1 := fun x hx => by
    apply H.inj
    rw [map_mul, map_one]
    exact H.sq _ hx
  have hÊle : Nat.card Ê ≤ 2 ^ (3 * f) :=
    (involution_rank_pairs_and_maximal_elementary_witness hK).2.2 Ê hÊsq |>.1
  have hpowle : ∀ {m n : ℕ}, m ≤ n → 2 ^ m ≤ 2 ^ n := fun h => Nat.pow_le_pow_right (by norm_num) h
  have hcard2 : Nat.card A ≤ 2 * Nat.card Ê := by
    calc Nat.card A = Nat.card Ê * Nat.card Ψ.range := hcardA
      _ ≤ Nat.card Ê * 2 := Nat.mul_le_mul_left _ hq
      _ = 2 * Nat.card Ê := mul_comm _ _
  have hinner : (∀ a : A, normAut π H.inj A H.norm a ∈ inner (antiSp K)) →
      Nat.card A ≤ 2 ^ (3 * f) := by
    intro hin
    have hrange : Ψ.range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨a, rfl⟩
      exact (mem_ker_outerHom H a).mpr (hin a)
    rw [hcardA, hrange, Subgroup.card_bot, mul_one]
    exact hÊle
  refine ⟨?_, fun hev => ?_, hinner⟩
  · calc Nat.card A ≤ 2 * Nat.card Ê := hcard2
      _ ≤ 2 * 2 ^ (3 * f) := Nat.mul_le_mul_left _ hÊle
      _ = 2 ^ (3 * f + 1) := by rw [pow_succ, mul_comm]
  · by_cases hin : ∀ a : A, normAut π H.inj A H.norm a ∈ inner (antiSp K)
    · exact hinner hin
    · push Not at hin
      obtain ⟨a₀, hout⟩ := hin
      have hθθ : normAut π H.inj A H.norm a₀ * normAut π H.inj A H.norm a₀ = 1 := by
        rw [← map_mul]
        have : a₀ * a₀ = 1 := Subtype.ext (H.sq a₀.1 a₀.2)
        rw [this, map_one]
      have hfix : Ê ≤ fixedSubgroup (normAut π H.inj A H.norm a₀) := by
        intro x hx
        rw [mem_fixedSubgroup]
        apply H.inj
        rw [π_normAut]
        have := H.comm a₀.1 a₀.2 (π x) hx
        calc a₀.1 * π x * a₀.1⁻¹ = (π x * a₀.1) * a₀.1⁻¹ := by rw [this]
          _ = π x := by group
      have hÊ2 := card_le_of_fixed_even hf hev hK _ hθθ hout Ê hfix hÊsq
      calc Nat.card A ≤ 2 * Nat.card Ê := hcard2
        _ ≤ 2 * 2 ^ (3 * (f / 2)) := Nat.mul_le_mul_left _ hÊ2
        _ = 2 ^ (3 * (f / 2) + 1) := by rw [pow_succ, mul_comm]
        _ ≤ 2 ^ (3 * f) := hpowle (by obtain ⟨m, rfl⟩ := hev; omega)

end Offender

section Setting

variable {F : Type} [Field F] [CharP F 2]

theorem offender_of_setting [Finite V] {Γ A L : Subgroup (GLV V)} {m : ℕ}
    (hs : OneCompSetting Γ A L m) (φ : ↥L ≃* antiSp F) : Offender (piOf L φ) A := by
  classical
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by
    rw [← _root_.sq]
    exact hs.A_elem.2 a ha
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    exact congrArg Subtype.val (hs.A_elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * piOf L φ x * a⁻¹ = piOf L φ y := fun a ha x => by
    refine ⟨φ ⟨a * ((φ.symm x : ↥L) : GLV V) * a⁻¹, hs.L_normal a (hs.A_le ha) _ (φ.symm x).2⟩, ?_⟩
    simp [piOf_apply]
  have : Fact (CFSG.Quasithin.B42Sp4.repOf (piOf L φ)).IsIrreducible :=
    ⟨repOf_piOf_isIrreducible φ hs.L_irr⟩
  obtain ⟨hnontriv, hirr⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mp
    (Fact.out : (CFSG.Quasithin.B42Sp4.repOf (piOf L φ)).IsIrreducible)
  have hnt : ∃ g, CFSG.Quasithin.B42Sp4.repOf (piOf L φ) g ≠ 1 :=
    ⟨invX F, fun h1 => invX_ne_one (piOf_injective L φ (LinearEquiv.toLinearMap_injective
      (h1.trans (map_one (CFSG.Quasithin.B42Sp4.repOf (piOf L φ))).symm)))⟩
  have hsum : SimpleSummandsStable (piOf L φ) A := by
    obtain ⟨g, hg⟩ := hnt
    obtain ⟨x, hx⟩ : ∃ x, CFSG.Quasithin.B42Sp4.repOf (piOf L φ) g x ≠ x := by
      by_contra h
      push Not at h
      exact hg (LinearMap.ext fun x => by rw [h x]; rfl)
    refine ⟨Unit, fun _ => ⊤, iSupIndep_subsingleton _, iSup_const, fun _ =>
      ⟨top_ne_bot, ⟨x, Submodule.mem_top, g, hx⟩, fun _ _ _ => Submodule.mem_top,
        fun U _ hU => hirr U hU, fun _ _ _ _ => Submodule.mem_top⟩⟩
  exact ⟨piOf_injective L φ, hnorm, hsq, hcomm, hsum⟩

end Setting

end CFSG.Quasithin.G11.Harris.Sp4

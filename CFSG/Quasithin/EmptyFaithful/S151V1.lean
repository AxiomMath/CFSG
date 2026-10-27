module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.FLcNat
public import CFSG.Quasithin.EmptyFaithful.S151ZP
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc

variable {G : Type} [Group G]

structure LnStr (L : Subgroup G) (e : ↥L →* SLt 3)
    (β : ↥(blockU L) →* Multiplicative (Vt 3)) : Prop where
  surj : Function.Surjective e
  ker : e.ker = CFSG.pCore 2 ↥L
  βsurj : Function.Surjective β
  βker : β.ker = (blockZ L).subgroupOf (blockU L)
  equiv : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β v) =
      (e ℓ : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (Multiplicative.toAdd (β u))

theorem exists_lnStr {L : Subgroup G} (h : IsLnBlock L 3) :
    ∃ (e : ↥L →* SLt 3) (β : ↥(blockU L) →* Multiplicative (Vt 3)), LnStr L e β := by
  obtain ⟨-, α, hα, hker, β, hβ, hβk, heq⟩ := h
  let φ := (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm
  refine ⟨φ.toMonoidHom.comp α, β, ?_, ?_, hβ, hβk, ?_⟩
  · exact φ.surjective.comp hα
  · rw [← hker]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  · intro ℓ u v huv
    rw [heq ℓ u v huv]
    have h1 := specialLinearGroupEquivStatedSL_coe 3 (ZMod 2) (φ (α ℓ))
    have h2 : (specialLinearGroupEquivStatedSL 3 (ZMod 2)) (φ (α ℓ)) = α ℓ :=
      (specialLinearGroupEquivStatedSL 3 (ZMod 2)).apply_symm_apply (α ℓ)
    rw [h2] at h1
    change ((α ℓ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec _ =
      ((φ (α ℓ) : SLt 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec _
    rw [h1]

theorem sl3_fix_two_card (a b : Vt 3) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (H : Subgroup (SLt 3))
    (hH : ∀ h ∈ H, (h : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a = a ∧
      (h : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec b = b) : Nat.card H ≤ 4 := by
  have key : ∀ a b : Vt 3, a ≠ 0 → b ≠ 0 → a ≠ b →
      (Finset.univ.filter (fun g : SLt 3 =>
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a = a ∧
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec b = b)).card ≤ 4 := by
    decide +kernel
  have h1 := key a b ha hb hab
  calc Nat.card H
      ≤ Nat.card {g : SLt 3 // (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a = a ∧
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec b = b} :=
        Nat.card_le_card_of_injective (fun h => ⟨h.1, hH h.1 h.2⟩) (fun x y hxy =>
          Subtype.ext (Subtype.mk.inj hxy))
    _ = (Finset.univ.filter (fun g : SLt 3 =>
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec a = a ∧
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec b = b)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ 4 := h1

theorem sylow_image_card [Finite G] {L B : Subgroup G} {e : ↥L →* SLt 3} (he : Function.Surjective e)
    (hB : IsSylowTwoOf B L) : Nat.card ↥((B.subgroupOf L).map e) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf hB
  let Q : Sylow 2 (SLt 3) := Sylow.mapSurjective (f := e) he P
  have hQ : (Q : Subgroup (SLt 3)) = (P : Subgroup ↥L).map e := Sylow.coe_mapSurjective (f := e) he P
  have h1 := Sylow.card_eq_multiplicity Q
  rw [card_SLt_three] at h1
  have h2 : (168 : ℕ).factorization 2 = 3 := by
    have h168 : (168 : ℕ) = 2 ^ 3 * 21 := by norm_num
    rw [h168, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 21)]
  rw [h2] at h1
  rw [← hP, ← hQ]
  simpa using h1

end CFSG.Quasithin

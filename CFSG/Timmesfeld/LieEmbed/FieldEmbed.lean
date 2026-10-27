module

public import CFSG.LieType.Steinberg.Exceptional.Fields

public noncomputable section

namespace CFSG.Timmesfeld.LieEmbed

open Polynomial CFSG.LieType.Steinberg.Exceptional

variable (p f : ℕ) [hp : Fact p.Prime]

theorem X_pow_sub_X_dvd :
    (X ^ p ^ f - X : (ZMod p)[X]) ∣ X ^ p ^ (2 * f) - X := by
  have hq : (X ^ p ^ f - X : (ZMod p)[X]) ^ p ^ f = X ^ p ^ (2 * f) - X ^ p ^ f := by
    rw [sub_pow_char_pow, ← pow_mul, ← pow_add, two_mul]
  refine ⟨(X ^ p ^ f - X) ^ (p ^ f - 1) + 1, ?_⟩
  have hpos : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.out.pos
  calc (X ^ p ^ (2 * f) - X : (ZMod p)[X]) = (X ^ p ^ f - X) ^ p ^ f + (X ^ p ^ f - X) := by
        rw [hq]; ring
    _ = (X ^ p ^ f - X) * ((X ^ p ^ f - X) ^ (p ^ f - 1) + 1) := by
        rw [mul_add, mul_one, ← pow_succ', Nat.sub_add_cancel hpos]

@[expose] def gfEmbed (hf : 1 ≤ f) : GaloisField p f →ₐ[ZMod p] GaloisField p (2 * f) :=
  haveI := FiniteField.isSplittingField_of_nat_card_eq p f (GaloisField.card p f (by omega))
  IsSplittingField.lift (GaloisField p f) (X ^ p ^ f - X : (ZMod p)[X]) (by
    have hs := FiniteField.splits_X_pow_nat_card_sub_X (p := p) (K := GaloisField p (2 * f))
    rw [GaloisField.card p (2 * f) (by omega)] at hs
    refine hs.of_dvd ?_ (Polynomial.map_dvd _ (X_pow_sub_X_dvd p f))
    exact map_ne_zero (FiniteField.X_pow_card_pow_sub_X_ne_zero (ZMod p) (by omega)
      (by have := hp.out.two_le; omega)))

theorem frobQ_gfEmbed (hf : 1 ≤ f) (c : GaloisField p f) :
    frobQ p f (gfEmbed p f hf c) = gfEmbed p f hf c := by
  classical
  have : Fintype (GaloisField p f) := Fintype.ofFinite _
  have hc : c ^ p ^ f = c := by
    have h := FiniteField.pow_card c
    rwa [Fintype.card_eq_nat_card, GaloisField.card p f (by omega)] at h
  rw [frobQ_apply, ← map_pow, hc]

theorem gfEmbed_injective (hf : 1 ≤ f) : Function.Injective (gfEmbed p f hf) :=
  (gfEmbed p f hf).toRingHom.injective

theorem frobQ_eq_iff_mem_range (hf : 1 ≤ f) (c : GaloisField p (2 * f)) :
    frobQ p f c = c ↔ c ∈ Set.range (gfEmbed p f hf) := by
  classical
  refine ⟨fun hc => ?_, ?_⟩
  · have : Fintype (GaloisField p f) := Fintype.ofFinite _
    have : Fintype (GaloisField p (2 * f)) := Fintype.ofFinite _
    set P : (GaloisField p (2 * f))[X] := X ^ p ^ f - X
    have hP : P ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero _ (by omega)
      (by have := hp.out.two_le; omega)
    have hdeg : P.natDegree = p ^ f := FiniteField.X_pow_card_pow_sub_X_natDegree_eq _
      (by omega) (by have := hp.out.two_le; omega)
    set S : Finset (GaloisField p (2 * f)) := Finset.univ.image (gfEmbed p f hf)
    have hS : S ⊆ P.roots.toFinset := by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
      rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, eval_sub, eval_pow, eval_X,
        ← frobQ_apply, frobQ_gfEmbed p f hf, sub_self]
    have hcard : P.roots.toFinset.card ≤ S.card := by
      rw [Finset.card_image_of_injective _ (gfEmbed_injective p f hf), Finset.card_univ,
        Fintype.card_eq_nat_card, GaloisField.card p f (by omega)]
      exact (Multiset.toFinset_card_le _).trans ((card_roots' P).trans hdeg.le)
    have heq := Finset.eq_of_subset_of_card_le hS hcard
    have hmem : c ∈ P.roots.toFinset := by
      rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, eval_sub, eval_pow, eval_X,
        ← frobQ_apply, hc, sub_self]
    rw [← heq] at hmem
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hmem
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact frobQ_gfEmbed p f hf y

end CFSG.Timmesfeld.LieEmbed

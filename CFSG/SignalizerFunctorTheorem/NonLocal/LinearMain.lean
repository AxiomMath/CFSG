module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.NonLocal.Linear

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne CFSG.SignalizerFunctorTheorem.CatalogBridge
open scoped commutatorElement

local notation "SL" => Matrix.SpecialLinearGroup

namespace CFSG.SignalizerFunctorTheorem.NonLocal

variable {K : Type*} [Field K] [Finite K] {n : ℕ}

theorem nonLocalized_linearSubfield (hn : 3 ≤ n) (k : Subfield K) :
    NonLocalized (linearSubfieldInclusion n k).range := by
  classical
  obtain ⟨r, hrK⟩ := CharP.exists K
  have hr : r.Prime := CharP.char_is_prime K r
  have : Fact r.Prime := ⟨hr⟩
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hkr : CharP k r := (RingHom.charP_iff k.subtype k.subtype.injective r).mpr hrK
  let P := linearProjData n K
  let φH : SL (Fin n) k →* SL (Fin n) K := Matrix.SpecialLinearGroup.map k.subtype
  have hrange : (P.π.comp φH).range = (linearSubfieldInclusion n k).range := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨proj n k g, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨g, rfl⟩ := proj_surjective n k y
      exact ⟨g, rfl⟩
  obtain ⟨hsimple₀, hnonab₀⟩ := simple_nonabelian_range_linearSubfieldInclusion hn k
  have hsimple : IsSimpleGroup (P.π.comp φH).range := by rw [hrange]; exact hsimple₀
  have hnonab : ∃ a b : (P.π.comp φH).range, a * b ≠ b * a := by
    rw [hrange]
    push Not at hnonab₀
    exact hnonab₀
  rw [← hrange]
  refine P.nonLocalized_of_heisenberg φH (fun W hW => linear_irreducible k (by omega) W hW)
    hsimple (linear_centralizer_eq_one k (by omega)) (rowSub hn) (zSub hn) (rowSub_comm hn)
    (rowSub_isPGroup hn) (zSub_le_rowSub hn) (yElt hn) (heis_comm k hn) (heis_nt k hn) ?_ ?_
  · intro s _ F _ _ ξ h1 h2 h3 v v' hvv
    exact heis_dist k hn ξ h1 h2 h3 v v' hvv
  · intro s hs hsr V _ hVcomm hVexp hVnorm hfaith hlow hup
    have : Fact s.Prime := ⟨hs⟩
    have : Finite (projectiveSL n K) := Finite.of_surjective P.π P.hπ
    have : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVcomm _ a.2 _ b.2)⟩⟩
    have hVp : IsPGroup s V := by
      refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
      have h1 : orderOf g ∣ s := orderOf_dvd_of_pow_eq_one (Subtype.ext (hVexp g g.2))
      rcases (Nat.dvd_prime hs).mp h1 with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hVp
    have hq0 : 2 ≤ Nat.card k := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    have hcardfun : Nat.card (Mid hn → k) = Nat.card k ^ (n - 2) := by
      rw [Nat.card_fun, card_mid hn]
    have hLm : Nat.card k ^ (n - 2) ≤ m := by
      rw [hcardfun, hm] at hlow
      exact (Nat.pow_le_pow_iff_right hs.one_lt).mp hlow
    have hq2 : Nat.card k = 2 → s ≠ 2 := by
      intro hk2 hs2
      have h2k : (2 : k) = 0 := by
        have h1 : Nat.card k • (1 : k) = 0 := card_nsmul_eq_zero'
        rw [hk2] at h1
        simpa using h1
      have hr2 : r ∣ 2 := by
        rw [← CharP.cast_eq_zero_iff k r 2]
        exact_mod_cast h2k
      exact hsr (hs2.trans ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hr2).symm)
    have hfin : Nat.card k = 2 ∧ m = 2 := by
      rcases hup with h | ⟨e, he, hdvd, hle⟩
      · rw [hm, Fintype.card_fin] at h
        obtain ⟨-, h1, h2⟩ := linear_numerics (j := 0) hn hq0 hs.two_le hq2 rfl hLm
          (Or.inl ((Nat.pow_le_pow_iff_right hs.one_lt).mp h))
        exact ⟨h1, h2⟩
      · rw [hm] at hdvd hle
        obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hs).mp hdvd
        rw [Fintype.card_fin] at he
        have hmj : m ≤ 2 * j := by
          rw [← pow_mul, mul_comm] at hle
          exact (Nat.pow_le_pow_iff_right hs.one_lt).mp hle
        obtain ⟨-, h1, h2⟩ := linear_numerics hn hq0 hs.two_le hq2 rfl hLm (Or.inr ⟨he, hmj⟩)
        exact ⟨h1, h2⟩
    obtain ⟨hk2, hm2⟩ := hfin
    have hV2 : Nat.card V = s ^ 2 := by rw [hm, hm2]
    exact linear_special_case hn k hk2 hs (hq2 hk2) hsimple hnonab V hVexp hVnorm hfaith hV2

end CFSG.SignalizerFunctorTheorem.NonLocal

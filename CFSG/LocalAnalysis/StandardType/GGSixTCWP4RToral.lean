module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrameD
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityProof
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Flag

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.Open

theorem uPlaneToralAt_E6_three
    {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : f % 2 = 1) :
    UPlaneToralAt .E6 3 K := by
  classical
  intro E hEel hEcard
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hcen : Nat.card (Subgroup.center (e6Data_valid.minGroup K)) = 1 := by
    obtain ⟨hc, -⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 K
    rw [hc, hK]
    have h1 := CFSG.StandardType.TableCRes.tc_two_pow_mod_three f
    have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    rw [if_neg (by omega)] at h1
    have : ¬ 3 ∣ 2 ^ f - 1 := by omega
    exact (Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 this))
  have hker : (e6Isogeny K).ker = ⊥ := by
    rw [CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center]
    exact Subgroup.eq_bot_of_card_eq _ hcen
  have hab : ∀ x ∈ E.comap (e6Isogeny K), ∀ y ∈ E.comap (e6Isogeny K), x * y = y * x := by
    intro x hx y hy
    have hcomm : e6Isogeny K x * e6Isogeny K y = e6Isogeny K y * e6Isogeny K x :=
      congrArg Subtype.val (hEel.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
    have hinj : Function.Injective (e6Isogeny K) := (MonoidHom.ker_eq_bot_iff _).1 hker
    apply hinj
    rw [map_mul, map_mul]
    exact hcomm
  obtain ⟨w, Fr, hFr, g0, hg0, hg0w, hEtor⟩ :=
    e6IsotropicToral_of_planeToralLang e6PlaneToralLang_proved K h3 E
      (fun x hx => hEel.2 x hx) hEcard hab
  refine ⟨g0, hg0, fun x hx => ?_⟩
  obtain ⟨t, ht, hteq⟩ := hEtor x hx
  have ht' : t ∈ torusGroup Tag.E6 (AlgebraicClosure K) := ((mem_twistedTorusOf).1 ht).1
  have hconj : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.E6 K) * g0 =
      t := by
    rw [← hteq]
    show g0⁻¹ * (g0 * t * g0⁻¹) * g0 = t
    group
  rw [hconj]
  exact ht'

end CFSG.StandardType.TableCRes

end

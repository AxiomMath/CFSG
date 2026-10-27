module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE6
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.CentralCover TableB TableBSymp NbrInnerRest

theorem ggCenterPrime_recipe_E6_of_coprime
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p (Nat.gcd 3 (Nat.card K - 1))) :
    GGCenterPrime p (TableBExc.RecipeGroup .E6 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fact.mk hp
  have := CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' (K := K) e6Data_valid
  obtain ⟨-, ⟨O⟩, -, -⟩ := CFSG.LieType.Steinberg.e6_conclusionB K
  obtain ⟨C, -, hC⟩ := e6Datum_commutatorFormula K _ (roots_eq isFiniteType_cartan_E6) O
  set f := CFSG.LieType.Steinberg.Isogeny.e6Isogeny K with hf
  set q : e6Data_valid.minGroup K →* TableBExc.RecipeGroup .E6 K :=
    (TableBExc.recipeEquiv .E6 K).symm.toMonoidHom.comp f with hqdef
  have hq : Function.Surjective q := (TableBExc.recipeEquiv .E6 K).symm.surjective.comp
    (CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective K)
  have hnp : ∀ z ∈ q.ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    have hz' : z ∈ f.ker := by
      rw [MonoidHom.mem_ker] at hz ⊢
      have h1 : (TableBExc.recipeEquiv .E6 K).symm (f z) = 1 := hz
      rwa [MulEquiv.map_eq_one_iff] at h1
    rw [hf, CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center] at hz'
    obtain ⟨hcard, -⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 K
    have h1 : orderOf (⟨z, hz'⟩ : Subgroup.center (e6Data_valid.minGroup K)) ∣
        Nat.card (Subgroup.center (e6Data_valid.minGroup K)) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hcard] at h1
    have h3 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h3 h1)
  intro L' _ _ ψ hψ hker hperf hdvd
  have hnpL := StdSubRestU.noTorsion_ker_of_section hq
    (fun E _ _ π hπ hcen hc =>
      CFSG.LieType.Steinberg.CentralExt.FieldFour.exists_section_of_coprime
        (e6Datum_isCTGroupDatum K) (e6Datum_steinbergExtras K) (e6_chevalleyExtras K O C hC)
        E π hπ hcen hc) hp hp2 hnp hψ hker hperf
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzk : (z : L') ∈ ψ.ker := by
    have h1 : ψ z ∈ Subgroup.center (TableBExc.RecipeGroup .E6 K) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.2 l]
    rw [TableBExc.center_recipeGroup_eq_bot .E6 K, Subgroup.mem_bot] at h1
    exact h1
  have hzp : (z : L') ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have h1 : z = 1 := Subtype.ext (hnpL _ hzk hzp)
  rw [h1, orderOf_one] at hz
  exact hp.one_lt.ne hz

theorem ggCenterPrime_twE6_of_coprime
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p (Nat.gcd 3 (2 ^ n + 1))) :
    GGCenterPrime p (TwE6Delta.RecipeR K n) := by
  obtain ⟨q, hq, hqk⟩ := TwE6Delta.exists_sc_surjection hn hK
  have : Finite (twistedE6Group 2 n) := by
    have : Finite (Module.End (GaloisField 2 (2 * n)) (Fin e6Data.d →₀ GaloisField 2 (2 * n))) :=
      Module.finite_of_finite (GaloisField 2 (2 * n))
    infer_instance
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* twistedE6Group 2 n),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : twistedE6Group 2 n →* E, ∀ h, π (s h) = h :=
    fun E _ _ π hπ hc hcop => TwistedE6Closed.twistedE6_exists_section_of_coprime
      (k := GaloisField 2 (2 * n)) (θ := frobQ 2 n) (frobQ_frobQ 2 n hn) (p := 2) hπ hc hcop
  have hnp : ∀ z ∈ q.ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    have hzc := hqk hz
    have hcard : Nat.card (Subgroup.center (twistedE6Group 2 n)) = Nat.gcd 3 (2 ^ n + 1) :=
      (TwistedE6Closed.card_center_fixedGroup (k := GaloisField 2 (2 * n)) (θ := frobQ 2 n)
        (q := 2 ^ n) (card_galoisField_two_mul 2 n hn) (fun c => by rw [frobQ_apply])).1
    have h1 : orderOf (⟨z, hzc⟩ : Subgroup.center (twistedE6Group 2 n)) ∣
        Nat.card (Subgroup.center (twistedE6Group 2 n)) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hcard] at h1
    have h3 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h3 h1)
  intro L' _ _ ψ hψ hker hperf hdvd
  have hnt := StdSubRestU.noTorsion_ker_of_section hq hsplit hp hp2 hnp hψ hker hperf
  have hkc := TableBUR.ker_eq_center_of_surjective hψ hker
    (TwE6Delta.center_recipeR_eq_bot hn hK)
  have := Fact.mk hp
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzk : (z : L') ∈ ψ.ker := by
    rw [hkc]
    exact z.2
  have hzp : (z : L') ^ p = 1 := by
    have h1 := pow_orderOf_eq_one z
    rw [hz] at h1
    exact congrArg Subtype.val h1
  have h1 : z = 1 := Subtype.ext (hnt _ hzk hzp)
  rw [h1, orderOf_one] at hz
  exact hp.one_lt.ne hz

end CFSG.StandardType

end

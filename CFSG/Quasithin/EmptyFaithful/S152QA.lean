module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.S152NWreath
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem conj_mem_oPrimeResidualOf {p : ℕ} {X : Subgroup G} {g x : G} (hg : g ∈ X)
    (hx : x ∈ oPrimeResidualOf p X) : g * x * g⁻¹ ∈ oPrimeResidualOf p X := by
  unfold oPrimeResidualOf at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ⟨X.mul_mem (X.mul_mem hg hx.1) (X.inv_mem hg), ?_⟩
    obtain ⟨k, hk⟩ := hx.2
    refine ⟨k, ?_⟩
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    simpa [MulAut.conj_apply, hk] using this
  | one => simp
  | mul x y _ _ ihx ihy => simpa [mul_assoc] using Subgroup.mul_mem _ ihx ihy
  | inv x _ ih => simpa [mul_assoc] using Subgroup.inv_mem _ ih

private theorem exists_pow_three_of_odd {H : Subgroup G} (φ : OTwoQuot H ≃* S152N.W3) {x : G}
    (hx : x ∈ H) (hodd : Odd (orderOf x)) : ∃ k : ℕ, orderOf x = 3 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥H)
  have hq : Nat.card (↥H ⧸ CFSG.Open.pCore 2 ↥H) = 72 :=
    (Nat.card_congr φ.toEquiv).trans S152N.W3.card_eq
  obtain ⟨n, hn'⟩ := (IsPGroup.iff_card).1
    (CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := ↥H))
  have hdvd : orderOf x ∣ 2 ^ (n + 3) * 9 := by
    have h1 : orderOf x ∣ Nat.card ↥H := by
      have := Subgroup.orderOf_dvd_natCard H hx
      exact this
    have h2 : Nat.card ↥H = 2 ^ (n + 3) * 9 := by
      rw [hcard, hq, hn']; ring
    rwa [h2] at h1
  have hcop : Nat.Coprime (orderOf x) (2 ^ (n + 3)) :=
    ((Nat.coprime_two_left.mpr hodd).pow_left (n + 3)).symm
  have h9 : orderOf x ∣ 9 := hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (by simpa using h9 : orderOf x ∣ 3 ^ 2)
  exact ⟨k, hk⟩

theorem conjClosure_oTwoUpper_le_oPrimeResidualOf_three {Mc H : Subgroup G} (hHMc : H ≤ Mc)
    (φ : OTwoQuot H ≃* S152N.W3) : conjClosure (oTwoUpper H) Mc ≤ oPrimeResidualOf 3 Mc := by
  have hK : oTwoUpper H ≤ oPrimeResidualOf 3 Mc := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨k, hk⟩ := exists_pow_three_of_odd φ hx.1 hx.2
    exact Subgroup.subset_closure ⟨hHMc hx.1, k, hk⟩
  exact conjClosure_le fun g hg z hz => conj_mem_oPrimeResidualOf hg (hK hz)

end CFSG.Quasithin

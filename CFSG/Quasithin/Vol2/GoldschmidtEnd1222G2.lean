module

public import CFSG.Quasithin.Vol2.GoldschmidtEnd1222Basic
public import CFSG.Quasithin.EmptyFaithfulMultiple.FixFactsG2

public section

namespace CFSG.Quasithin.H13

namespace End1222

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.EmptyFaithfulMultiple
  CFSG.Quasithin.EmptyFaithfulMultiple.FFL
open CFSG.Open (quasithinG2 quasithinZorn)

namespace G2

variable {K : Type} [Field K]

noncomputable def u0 (K : Type) [Field K] : Multiplicative (quasithinZorn K) :=
  Multiplicative.ofAdd (zmk 0 1 0 0 0 0 0 0)

theorem u0_mem_sec : u0 K ∈ zornO0 K := by
  show (zmk (0 : K) 1 0 0 0 0 0 0).1 + (zmk (0 : K) 1 0 0 0 0 0 0).2.2.2 = 0
  simp [zmk]

theorem u0_not_mem_ker : u0 K ∉ zornR K := by
  rintro ⟨c, hc⟩
  have h := congrFun (congrArg (fun x : quasithinZorn K => x.2.1) hc) 0
  simp [u0, zmk] at h

theorem zornAct_g2τ_u0 [CharP K 2] :
    zornAct ⁅quasithinG2 K, quasithinG2 K⁆ ⟨_, g2τ_mem (K := K)⟩ (u0 K) = u0 K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  change Multiplicative.ofAdd (g2E (g2τ K) (zmk 0 1 0 0 0 0 0 0)) = Multiplicative.ofAdd _
  rw [g2τ_zmk]
  congr 1
  apply zmk_congr <;> ring_nf


theorem zmk_eq_pair (r : K) : zmk r 0 0 0 0 0 0 r = (r, 0, 0, r) := by
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;> funext i <;> fin_cases i <;> rfl

theorem unique_fixed_of_zmk [CharP K 2] [Finite K] (hK : Nat.card K = 2)
    {Γ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)} (τ : ↥Γ)
    (hτ : ∀ r a b c d e f s : K, (τ : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      (zmk r a b c d e f s) = zmk (r + c + d) (r + a + b + e + s) c (b + d) d
        (r + b + c + d + f + s) (c + d + e) (c + d + s))
    (m : Multiplicative (quasithinZorn K)) (hm : m ∈ zornO0 K)
    (hτm : zornAct Γ τ m * m⁻¹ ∈ zornR K) :
    m ∈ zornR K ∨ m * (u0 K)⁻¹ ∈ zornR K := by
  obtain ⟨x, rfl⟩ : ∃ x : quasithinZorn K, Multiplicative.ofAdd x = m := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ := hτm
  have htr : x.1 + x.2.2.2 = 0 := hm
  have ht2 : (τ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x = x + (t, 0, 0, t) := by
    have h0 : (τ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x + -x = (t, 0, 0, t) := ht
    rw [← h0]
    abel
  obtain ⟨r, a, b, c, d, e, f, s, rfl⟩ :
      ∃ r a b c d e f s : K, x = zmk r a b c d e f s :=
    ⟨_, _, _, _, _, _, _, _, zorn_eta x⟩
  rw [hτ, ← zmk_eq_pair, zmk_add] at ht2
  obtain ⟨-, ha, hb, hc, -, he, hf, -⟩ := zmk_inj ht2
  have htr' : r + s = 0 := htr
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hd : d = 0 := by linear_combination hc - hb + (c - b) * h2
  have hb0 : b = 0 := by linear_combination he + hf - htr' - (c + d) * h2
  have hc0 : c = 0 := by linear_combination hb + hb0
  have he0 : e = 0 := by linear_combination ha - htr' - hb0
  have hf0 : f = 0 := by linear_combination -hf + hc0 + hd + he0
  have hs : s = r := by linear_combination htr' - r * h2
  subst hb0 hc0 hd he0 hf0 hs
  rcases G64.eq_zero_or_eq_one_of_card_two hK a with rfl | rfl
  · left
    exact ⟨s, zmk_eq_pair s⟩
  · right
    refine ⟨s, ?_⟩
    change zmk s 1 0 0 0 0 0 s + -(zmk 0 1 0 0 0 0 0 0) = (s, 0, 0, s)
    rw [← zmk_eq_pair]
    have hneg : ∀ y : K, -y = y := CharTwo.neg_eq
    simp only [zmk, Prod.mk_add_mk, Prod.neg_mk]
    refine Prod.ext (by simp) (Prod.ext ?_ (Prod.ext ?_ (by simp [hneg]))) <;>
      funext i <;> fin_cases i <;> simp [hneg, CharTwo.add_self_eq_zero]

theorem exists_move_of_zornQ {W : Type*} [CommGroup W] (hK : Nat.card K = 2)
    {H : Subgroup (MulAut W)} {Z : Subgroup W}
    (hR : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Realizes H ⊤ Z) (hZ : fixV H = Z)
    {c : MulAut W} (hc : ∀ g ∈ H, c * g = g * c) : ∃ v : W, v ∉ Z ∧ c v * v⁻¹ ∈ Z := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hchar : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := 1)
      (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  obtain ⟨π, hπ⟩ := hR
  refine exists_move_of_realizesVia hπ hZ hc {⟨_, g2τ_mem (K := K)⟩} (m₀ := u0 K)
    u0_mem_sec u0_not_mem_ker ?_ ?_
  · intro γ hγ
    obtain rfl : γ = ⟨_, g2τ_mem (K := K)⟩ := hγ
    exact zornAct_g2τ_u0
  · intro m hm hS
    exact unique_fixed_of_zmk hK ⟨_, g2τ_mem (K := K)⟩ g2τ_zmk m hm (hS _ rfl)

end G2

end End1222

end CFSG.Quasithin.H13

module

public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
import CFSG.Quasithin.EmptyFaithful.S146xU1Orb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

theorem coprime_index_of_subset_mul {G : Type*} [Group G] {R H T : Subgroup G} [Finite R]
    (hTR : T ≤ R) (hRTH : (R : Set G) ⊆ (T : Set G) * (H : Set G)) {p : ℕ}
    (hp : p.Prime) (hT : ∀ t ∈ T, t ^ p = 1 → t = 1) :
    Nat.Coprime (H.subgroupOf R).index p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite T := Finite.of_injective (Subgroup.inclusion hTR)
    (Subgroup.inclusion_injective hTR)
  have hmul : ∀ g ∈ R, ∃ a ∈ T, ∃ b ∈ H, g = a * b := by
    intro g hg
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 (hRTH hg)
    exact ⟨a, ha, b, hb, by rw [← hab]⟩
  have hidx : (H.subgroupOf R).index = (H.subgroupOf T).index := by
    have h := CFSG.Quasithin.relIndex_inf_eq_of_forall_mul (H₁ := T) (T := H) (H := R)
      hTR hmul
    unfold Subgroup.relIndex at h
    rw [Subgroup.inf_subgroupOf_right] at h
    exact h.symm
  have hdvd : (H.subgroupOf T).index ∣ Nat.card T := Subgroup.index_dvd_card _
  have hpndvd : ¬ p ∣ Nat.card T := by
    intro hpdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := T) p hpdvd
    have hxpow : x ^ p = 1 := by rw [← hx, pow_orderOf_eq_one]
    have hxG : ((x : G) ^ p) = 1 := by
      simpa using congrArg (fun y : T => (y : G)) hxpow
    have hx1 : x = 1 := Subtype.ext (hT x x.2 hxG)
    rw [hx1, orderOf_one] at hx
    exact hp.ne_one hx.symm
  have hnotdvd : ¬ p ∣ (H.subgroupOf R).index := by
    rw [hidx]
    exact fun h => hpndvd (h.trans hdvd)
  exact (Nat.coprime_comm).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hnotdvd)

theorem eq_one_of_mem_torusGroup_of_pow_eq_one
    {τ : Tag} {k : Type} [Field k] {p : ℕ} [Fact p.Prime]
    [CharP k p] {t : ModGL τ k} (ht : t ∈ torusGroup τ k) (htp : t ^ p = 1) : t = 1 := by
  classical
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  rw [rootDiagUnit_pow, ← rootDiagUnit_one] at htp
  have hb : b ^ p = 1 := rootDiagUnit_injective htp
  have hb1 : b = 1 := funext fun i => by
    have hval : ((b i : k)) ^ p = 1 := by
      simpa using congrArg (fun u : kˣ => (u : k)) (congrFun hb i)
    have hzero : ((b i : k) - 1) ^ p = 0 := by
      rw [sub_pow_char, hval, one_pow, sub_self]
    have hp0 : p ≠ 0 := Nat.Prime.ne_zero (Fact.out : p.Prime)
    exact Units.ext (sub_eq_zero.mp ((pow_eq_zero_iff hp0).1 hzero))
  rw [hb1, rootDiagUnit_one]

theorem coprime_index_twistedFixedGroup
    (t : TwistTag) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hodd : Odd (p ^ f)) (K : Type) [Field K]
    (hK : Nat.card K = (p ^ f) ^ t.order) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (p ^ f)) :
    Nat.Coprime (((graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L))).subgroupOf
      (twistedFixedGroup t L Fr)).index p := by
  classical
  obtain ⟨-, hfin, -, -, hset, -, -⟩ :=
    odd_diagram_Frobenius_fixed_derived_root_group t hp hf hodd K hK σ hσ L Fr hFr
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (twistedFixedGroup t L Fr) := hfin
  have htord : 1 ≤ t.order := by cases t <;> simp [TwistTag.order]
  have hf1 : 1 ≤ f * t.order := by
    simpa using Nat.mul_le_mul hf htord
  have hK' : Nat.card K = p ^ (f * t.order) := by
    rw [hK, ← pow_mul]
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf1 hK'
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  exact coprime_index_of_subset_mul (graphFixedTorus_le t L Fr) hset.le hp
    (fun x hx hxp => eq_one_of_mem_torusGroup_of_pow_eq_one (Subgroup.mem_inf.1 hx).1 hxp)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

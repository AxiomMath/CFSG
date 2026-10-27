module

public import CFSG.LocalAnalysis.StandardType.GGSmallKGInputsTwE6Six
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.Minuscule

@[expose] def GGTwE6ScThreeRankInput :
    Prop :=
  ∀ n : ℕ, 1 ≤ n → 3 ∣ 2 ^ n + 1 →
    ∃ E : Subgroup (twistedE6Group 2 n), IsElemAbelian 3 E ∧ 3 ^ 6 ≤ Nat.card E

section Center


theorem ggTwE6ThreeCoverCenterInput_of_sc (hU : GGTwE6ScThreeRankInput) :
    GGTwE6ThreeCoverCenterInput := by
  intro K _ _ n hn hK h3 L' _ _ ψ hψ hker hperf hz
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
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
  have hcardZ : Nat.card (Subgroup.center (twistedE6Group 2 n)) = 3 := by
    have h := (TwistedE6Closed.card_center_fixedGroup (k := GaloisField 2 (2 * n))
      (θ := frobQ 2 n) (q := 2 ^ n) (card_galoisField_two_mul 2 n hn)
      (fun c => by rw [frobQ_apply])).1
    rw [h]
    exact Nat.gcd_eq_left h3
  have hkc := TableBUR.ker_eq_center_of_surjective hψ hker
    (TwE6Delta.center_recipeR_eq_bot hn hK)
  set N := TableBU.twoPartOf ψ.ker hker (Nat.card L') with hNdef
  have hNk : N ≤ ψ.ker := TableBU.twoPartOf_le _ hker _
  set π : L' →* L' ⧸ N := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hkerπ : π.ker = N := QuotientGroup.ker_mk' N
  set ψb : L' ⧸ N →* TwE6Delta.RecipeR K n := QuotientGroup.lift N ψ hNk with hψb
  have hψbπ : ∀ l, ψb (π l) = ψ l := fun l => QuotientGroup.lift_mk N hNk l
  have hψbs : Function.Surjective ψb := by
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    exact ⟨π l, hψbπ l⟩
  have hψbc : ψb.ker ≤ Subgroup.center (L' ⧸ N) := by
    intro y hy
    obtain ⟨z, rfl⟩ := hπs y
    have hz' : z ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hψbπ]
      exact hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨v, rfl⟩ := hπs w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hker hz') v]
  have hψbodd : ∀ y ∈ ψb.ker, y ^ 2 = 1 → y = 1 := fun y hy hy2 =>
    TableBU.sq_eq_one_ker_lift hker y hy hy2
  have hperfb : commutator (L' ⧸ N) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨l, rfl⟩ := hπs y
    have hl : l ∈ commutator L' := by rw [hperf]; exact Subgroup.mem_top l
    have h1 := Subgroup.mem_map_of_mem π hl
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hπs, ← commutator_def] at h1
  obtain ⟨α, hα, hαs⟩ :=
    StdSubRestU.exists_surjective_of_oddKernel hq hsplit hψbs hψbc hperfb hψbodd
  have hinj : Function.Injective α := by
    refine (injective_iff_map_eq_one α).2 fun s hs => ?_
    by_contra hs1
    have hsq : s ∈ q.ker := by
      rw [MonoidHom.mem_ker, ← hα, hs, map_one]
    have hsZ : s ∈ Subgroup.center (twistedE6Group 2 n) := hqk hsq
    have hZs : Subgroup.center (twistedE6Group 2 n) ≤ Subgroup.zpowers s := by
      have hle : Subgroup.zpowers s ≤ Subgroup.center (twistedE6Group 2 n) :=
        (Subgroup.zpowers_le).2 hsZ
      have hord : orderOf s ∣ 3 := by
        have h1 := Subgroup.orderOf_dvd_natCard (Subgroup.center _) hsZ
        rwa [hcardZ] at h1
      have hord3 : orderOf s = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 hord with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) hs1
        · exact h
      have hcard : Nat.card (Subgroup.center (twistedE6Group 2 n)) ≤
          Nat.card (Subgroup.zpowers s) := by
        rw [hcardZ, Nat.card_zpowers, hord3]
      exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm.le
    have hkq : ∀ t ∈ q.ker, α t = 1 := by
      intro t ht
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hZs (hqk ht))
      rw [map_zpow, hs, one_zpow]
    have h3k : 3 ∣ Nat.card ψ.ker := by
      rw [hkc]
      exact hz
    obtain ⟨z, hz3⟩ := exists_prime_orderOf_dvd_card' 3 h3k
    obtain ⟨t, ht⟩ := hαs (π z)
    have htq : t ∈ q.ker := by
      rw [MonoidHom.mem_ker, ← hα, ht, hψbπ]
      exact z.2
    have hπz : π z = 1 := by
      rw [← ht]
      exact hkq t htq
    have hzN : (z : L') ∈ N := by
      rw [← hkerπ]
      exact hπz
    have h2 : orderOf (z : L') ∣ 2 ^ Nat.card L' := orderOf_dvd_of_pow_eq_one hzN.2
    rw [Subgroup.orderOf_coe, hz3] at h2
    have h32 := Nat.le_of_dvd (by norm_num) (Nat.prime_three.dvd_of_dvd_pow h2)
    omega
  obtain ⟨E, hE, hEc⟩ := hU n hn h3
  have hE1 : IsElemAbelian 3 (E.map α) := TableB.isElemAbelian_map hE α
  have hE1c : Nat.card (E.map α) = Nat.card E := Subgroup.card_map_of_injective hinj
  have hNodd : ¬ 3 ∣ Nat.card π.ker := by
    rw [hkerπ]
    intro h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (TableBU.isPGroup_twoPartOf ψ.ker hker (Nat.card L')).exists_card_eq
    rw [hk] at h
    have h32 := Nat.le_of_dvd (by norm_num) (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  obtain ⟨E', hE', hE'c⟩ := SmallKG.exists_isElemAbelian_lift hπs hNodd hE1
  exact ⟨E', hE', by rw [hE'c, hE1c]; exact hEc⟩

theorem ggTwE6ThreeCoverRankInput_of_sc (hU : GGTwE6ScThreeRankInput) :
    GGTwE6ThreeCoverRankInput :=
  ggTwE6ThreeCoverRankInput_of_center (ggTwE6ThreeCoverCenterInput_of_sc hU)

end Center

end CFSG.StandardType

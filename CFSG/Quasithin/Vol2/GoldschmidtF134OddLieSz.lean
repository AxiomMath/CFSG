module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieBridge
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSzArith
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSzCore

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.SteinbergBR CFSG.LieType
open scoped Pointwise

variable {a : ℕ} {K : Type} [Field K]

theorem isCyclic_of_isPGroup_le_suzukiB [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {Q : Subgroup (suzukiGroup a K)} (hQ : IsPGroup p Q) (hQB : Q ≤ suzukiB a K) :
    IsCyclic Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := suzukiB a K with hBdef
  set N : Subgroup B := (suzukiU a K).subgroupOf B with hN
  have hUB : suzukiU a K ≤ B := le_sup_left
  have hTB : suzukiT a K ≤ B := le_sup_right
  have hBnorm : B ≤ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) :=
    sup_le Subgroup.le_normalizer (suzukiT_le_normalizer hK)
  have : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).mpr hBnorm
  let D : Kˣ →* suzukiGroup a K :=
    { toFun := suzukiDElt a K
      map_one' := suzukiDElt_one
      map_mul' := fun x y => (suzukiDElt_mul x y).symm }
  let ψ : Kˣ →* B ⧸ N :=
    (QuotientGroup.mk' N).comp (D.codRestrict B fun l => hTB (suzukiDElt_mem_suzukiT a K l))
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have hb : (b : suzukiGroup a K) ∈
        (suzukiU a K : Set (suzukiGroup a K)) * (suzukiT a K : Set (suzukiGroup a K)) := by
      rw [← (suzuki_borel_structure hK).2.2.2.2.2.1]
      exact b.2
    obtain ⟨u, hu, t, ht, hbut⟩ := hb
    obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 ht
    refine ⟨l, ?_⟩
    change QuotientGroup.mk _ = QuotientGroup.mk b
    rw [QuotientGroup.eq, hN, Subgroup.mem_subgroupOf]
    have h1 : (suzukiDElt a K l)⁻¹ * (u * suzukiDElt a K l) ∈ suzukiU a K := by
      have := (Subgroup.mem_normalizer_iff.1 (suzukiT_le_normalizer hK
        (inv_mem (suzukiDElt_mem_suzukiT a K l))) u).1 hu
      simpa [mul_assoc] using this
    show (D l)⁻¹ * (b : suzukiGroup a K) ∈ suzukiU a K
    rw [← hbut]
    exact h1
  have : IsCyclic (B ⧸ N) := isCyclic_of_surjective ψ hsurj
  let φ : Q →* B ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hQB)
  refine isCyclic_of_injective φ ((injective_iff_map_eq_one φ).2 fun x hx => ?_)
  have hxU : (x : suzukiGroup a K) ∈ suzukiU a K := by
    have := (QuotientGroup.eq_one_iff _).1 hx
    exact Subgroup.mem_subgroupOf.1 this
  have hdisj := IsPGroup.disjoint_of_ne p 2 hp2 Q (suzukiU a K) hQ (isPGroup_suzukiU hK)
  have : (x : suzukiGroup a K) ∈ Q ⊓ suzukiU a K := ⟨x.2, hxU⟩
  rw [hdisj.eq_bot, Subgroup.mem_bot] at this
  exact Subtype.ext this

theorem isCyclic_of_isPGroup_le_conj_suzukiB [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Q : Subgroup (suzukiGroup a K)} (hQ : IsPGroup p Q) (g : suzukiGroup a K)
    (hQB : Q ≤ (suzukiB a K).map (MulAut.conj g).toMonoidHom) : IsCyclic Q := by
  set Q' : Subgroup (suzukiGroup a K) := Q.map (MulAut.conj g⁻¹).toMonoidHom with hQ'
  have hQ'B : Q' ≤ suzukiB a K := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb, hbx⟩ := hQB hx
    have : (MulAut.conj g⁻¹).toMonoidHom x = b := by
      rw [← hbx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hb
  have hc : IsCyclic Q' := isCyclic_of_isPGroup_le_suzukiB hK hp2 (hQ.map _) hQ'B
  have hinj := (MulAut.conj g⁻¹).injective
  exact isCyclic_of_surjective
    (Q.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom hinj).symm.toMonoidHom
    (Q.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom hinj).symm.surjective

theorem sz_noPExt (n : ℕ) :
    NoPExt fun (X : Type) [Group X] => SuzukiModel X 2 n := by
  intro X _ _ hX p m hp hp5 hm S H Q hS2 hSi hSH hQH hH hQ hQe
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hX
  set S' : Subgroup (suzukiGroup a K) := S.map e.toMonoidHom with hS'
  set H' : Subgroup (suzukiGroup a K) := H.map e.toMonoidHom with hH'
  set Q' : Subgroup (suzukiGroup a K) := Q.map e.toMonoidHom with hQ'
  have hS'2 : IsPGroup 2 S' := hS2.map _
  have hS'i : ¬ 2 ∣ S'.index := by
    have h : S'.index = S.index := Subgroup.index_map_equiv S e
    rw [h]
    exact hSi
  have hS'c : Nat.card S' = Nat.card S := Subgroup.card_map_of_injective e.injective
  have hH'c : Nat.card H' = p ^ m * Nat.card S' := by
    rw [hH', Subgroup.card_map_of_injective e.injective, hH, hS'c]
  have hn : ∀ r : ℕ, r.Prime → r ∣ Nat.card H' → r = 2 ∨ r = p := by
    intro r hr hrd
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS'2
    rw [hH'c, hk] at hrd
    rcases (Nat.Prime.dvd_mul hr).1 hrd with h1 | h1
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow h1))
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h1))
  have hN : H' ≤ Subgroup.normalizer (S' : Set (suzukiGroup a K)) :=
    le_normalizer_of_not_dvd_card ha hK hS'2 hS'i (Subgroup.map_mono hSH)
      (not_dvd_of_prime_factors hp ha hn)
  have hS'bot : S' ≠ ⊥ := by
    intro h
    apply hS'i
    rw [h, Subgroup.index_bot, suzuki_order hK]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow (dvd_pow_self 2 (by omega))
      two_ne_zero) _) _
  obtain ⟨⟨g, hg⟩, -⟩ := suzuki_nontrivial_two_subgroup_normalizer_solvable hK S' hS'2 hS'bot
  have hQp : IsPGroup p Q := fun x => ⟨1, Subtype.ext (by simpa using hQe x x.2)⟩
  have hcyc : IsCyclic Q' := isCyclic_of_isPGroup_le_conj_suzukiB hK (p := p) (by omega)
    (hQp.map _) g fun x hx => hg (hN (Subgroup.map_mono hQH hx))
  have hcycQ : IsCyclic Q :=
    isCyclic_of_surjective (Q.equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom
      (Q.equivMapOfInjective e.toMonoidHom e.injective).symm.surjective
  exact not_isCyclic_of_card_pow (by omega) hQ hQe hcycQ

theorem sz_simple (n : ℕ) :
    NoOddCfg fun (X : Type) [Group X] => SuzukiModel X 2 n :=
  noOddCfg_of_noPExt (sz_noPExt n)

theorem lieSz : LieSz := fun n =>
  noOddConfigQ_of_noOddCfg (isoInvariant_suzuki 2 n) (sz_simple n)

end CFSG.Quasithin.H13.NQCore

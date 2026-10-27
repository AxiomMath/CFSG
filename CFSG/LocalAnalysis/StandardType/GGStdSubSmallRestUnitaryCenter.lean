module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitary

public section

namespace CFSG.StandardType

namespace StdSubRestU

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag TableBUE
open CFSG.LieType.Steinberg (pullback mem_pullback pullbackFst pullbackFst_surjective
  ker_pullbackFst_le_center snd_mem_ker_of_mem_ker_pullbackFst
  commutatorElement_mul_mul_of_mem_center)
open scoped commutatorElement

section Odd

variable {H R L : Type} [Group H] [Group R] [Group L]

theorem exists_surjective_of_oddKernel [Finite L] {q : H →* R} (hq : Function.Surjective q)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : H →* E, ∀ h, π (s h) = h)
    [Finite H] {ψ : L →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) (hodd : ∀ y ∈ ψ.ker, y ^ 2 = 1 → y = 1) :
    ∃ α : H →* L, (∀ s, ψ (α s) = q s) ∧ Function.Surjective α := by
  have hfst := pullbackFst_surjective (β := q) hψ
  have hfstc := ker_pullbackFst_le_center (β := q) hker
  have hcop : Nat.Coprime 2 (Nat.card (pullbackFst q ψ).ker) := by
    refine TableBU.coprime_two_card_of_sq fun y hy2 => ?_
    obtain ⟨h1, h2⟩ := snd_mem_ker_of_mem_ker_pullbackFst y.2
    have h3 : (((y : pullback q ψ) : H × L).2) ^ 2 = 1 := by
      have := congrArg (fun z : (pullbackFst q ψ).ker => ((z : pullback q ψ) : H × L).2) hy2
      simpa using this
    have h4 := hodd _ h2 h3
    exact Subtype.ext (Subtype.ext (Prod.ext h1 h4))
  obtain ⟨σ, hσ⟩ := hsplit (pullback q ψ) (pullbackFst q ψ) hfst hfstc hcop
  let α : H →* L := ((MonoidHom.snd H L).comp (pullback q ψ).subtype).comp σ
  have hα : ∀ s, ψ (α s) = q s := fun s => by
    have hmem := mem_pullback.1 (σ s).2
    have h1 : ((σ s : pullback q ψ) : H × L).1 = s := hσ s
    change ψ ((σ s : pullback q ψ) : H × L).2 = q s
    rw [← hmem, h1]
  have hdecomp : ∀ x : L, ∃ s, x * (α s)⁻¹ ∈ Subgroup.center L := fun x => by
    obtain ⟨s, hs⟩ := hq (ψ x)
    refine ⟨s, hker ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hα, hs, mul_inv_cancel]
  refine ⟨α, hα, ?_⟩
  have hcomm : commutator L ≤ α.range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨s, hs⟩ := hdecomp x
    obtain ⟨t, ht⟩ := hdecomp y
    have e : ⁅x, y⁆ = ⁅α s, α t⁆ := by
      have h := commutatorElement_mul_mul_of_mem_center hs ht (α s) (α t)
      rwa [inv_mul_cancel_right, inv_mul_cancel_right] at h
    rw [e, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  intro x
  exact hcomm (by rw [hperf]; exact Subgroup.mem_top x)

theorem noTorsion_ker_of_section [Finite H] [Finite L] {q : H →* R}
    (hq : Function.Surjective q)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : H →* E, ∀ h, π (s h) = h)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hnp : ∀ z ∈ q.ker, z ^ p = 1 → z = 1)
    {ψ : L →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) : ∀ z ∈ ψ.ker, z ^ p = 1 → z = 1 := by
  classical
  have := Fact.mk hp
  set N := TableBU.twoPartOf ψ.ker hker (Nat.card L) with hNdef
  have hNk : N ≤ ψ.ker := TableBU.twoPartOf_le _ hker _
  set π : L →* L ⧸ N := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hkerπ : π.ker = N := QuotientGroup.ker_mk' N
  set ψb : L ⧸ N →* R := QuotientGroup.lift N ψ hNk with hψb
  have hψbπ : ∀ l, ψb (π l) = ψ l := fun l => QuotientGroup.lift_mk N hNk l
  have hψbs : Function.Surjective ψb := by
    intro r
    obtain ⟨l, rfl⟩ := hψ r
    exact ⟨π l, hψbπ l⟩
  have hψbc : ψb.ker ≤ Subgroup.center (L ⧸ N) := by
    intro y hy
    obtain ⟨z, rfl⟩ := hπs y
    have hz : z ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hψbπ]
      exact hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨v, rfl⟩ := hπs w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hker hz) v]
  have hψbodd : ∀ y ∈ ψb.ker, y ^ 2 = 1 → y = 1 := fun y hy hy2 =>
    TableBU.sq_eq_one_ker_lift hker y hy hy2
  have hperfb : commutator (L ⧸ N) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨l, rfl⟩ := hπs y
    have hl : l ∈ commutator L := by rw [hperf]; exact Subgroup.mem_top l
    have h1 := Subgroup.mem_map_of_mem π hl
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hπs, ← commutator_def] at h1
  obtain ⟨α, hα, hαs⟩ :=
    exists_surjective_of_oddKernel hq hsplit hψbs hψbc hperfb hψbodd
  have hkerq : ¬ p ∣ Nat.card q.ker := by
    intro hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have h1 : (z : H) = 1 := hnp z z.2 (by
      have := pow_orderOf_eq_one z
      rw [hz] at this
      exact congrArg Subtype.val this)
    have : z = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  intro z hz hzp
  obtain ⟨s, hs⟩ := hαs (π z)
  have hsq : s ∈ q.ker := by
    rw [MonoidHom.mem_ker, ← hα, hs, hψbπ]
    exact hz
  have hmem : π z ∈ q.ker.map α := ⟨s, hsq, hs⟩
  have h1 : orderOf (π z) ∣ Nat.card q.ker :=
    (Subgroup.orderOf_dvd_natCard _ hmem).trans (Subgroup.card_map_dvd _ _)
  have h2 : orderOf (π z) ∣ p := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hzp, map_one])
  have hcop : Nat.Coprime p (Nat.card q.ker) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hkerq
  have h3 : orderOf (π z) = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
  rw [orderOf_eq_one_iff] at h3
  have hzN : z ∈ N := by
    rw [← hkerπ]
    exact h3
  have hz2 : z ^ 2 ^ Nat.card L = 1 := hzN.2
  have h4 : orderOf z ∣ Nat.gcd p (2 ^ Nat.card L) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzp) (orderOf_dvd_of_pow_eq_one hz2)
  have hcop2 : Nat.gcd p (2 ^ Nat.card L) = 1 :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  rw [hcop2, Nat.dvd_one, orderOf_eq_one_iff] at h4
  exact h4

end Odd

section Unitary

variable {K : Type} [Field K] [Finite K] {n d p : ℕ}

theorem ggCenterPrime_unitary
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ d) :
    GGCenterPrime p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
  have := Fact.mk hp
  have h := TableBU.unitaryFieldData_of_card hK hn
  have : CharP K 2 := h.charP
  have hsplit : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* LargeEvenSUGroup (Fin d) K (2 ^ n)), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : LargeEvenSUGroup (Fin d) K (2 ^ n) →* E, ∀ h, π (s h) = h := by
    intro E _ _ π hπ hcen hC
    by_cases he : Even d
    · exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_coprime
        (F := K) (p := 2) (f := n) hK he (by omega) E π hπ hcen hC
    · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
        (F := K) (p := 2) (f := n) hK hn hd he hdq hπ hcen
  have : Finite (LargeEvenSUGroup (Fin d) K (2 ^ n)) := Finite.of_injective
    (fun x : LargeEvenSUGroup (Fin d) K (2 ^ n) =>
      ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  intro L' _ _ ψ hψ hker hperf hdvd
  have hnp := noTorsion_ker_of_section
    (q := LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    (QuotientGroup.mk'_surjective _) hsplit hp hp2
    (fun z hz hzp => eq_one_of_mem_suScalars h hp hpd hz hzp) hψ hker hperf
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzk : (z : L') ∈ ψ.ker := by
    have h1 : ψ z ∈ Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.2 l]
    rw [TableBUE.center_proj_eq_bot hK hd hdq, Subgroup.mem_bot] at h1
    exact h1
  have hzp : (z : L') ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have h1 : z = 1 := Subtype.ext (hnp _ hzk hzp)
  rw [h1, orderOf_one] at hz
  exact hp.one_lt.ne hz

end Unitary

end StdSubRestU

end CFSG.StandardType

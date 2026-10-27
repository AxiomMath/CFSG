module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSp
public import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggCenterPrime_sp
    {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ}
    [NeZero m] (hp : p.Prime) (hp2 : p ≠ 2) :
    GGCenterPrime p (LargeEvenProj (LargeEvenSpGroup K m)) := by
  have := Fact.mk hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* LargeEvenSpGroup K m),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : LargeEvenSpGroup K m →* E, ∀ h, π (s h) = h :=
    fun E _ _ π hπ hcen hC =>
      CFSG.LieType.Steinberg.CentralExt.SpClosed.sp_exists_section_of_coprime (n := m) (K := K)
        (p := 2) E π hπ hcen hC
  have : Finite (LargeEvenSpGroup K m) := Finite.of_injective
    (fun x : LargeEvenSpGroup K m =>
      ((x : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K))
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  have hinj : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K m)) :=
    AutPSp.proj_injective (n := m) (K := K)
  intro L' _ _ ψ hψ hker hperf hdvd
  have hnp := StdSubRestU.noTorsion_ker_of_section
    (q := LargeEvenProjMk (LargeEvenSpGroup K m)) (QuotientGroup.mk'_surjective _) hsplit hp hp2
    (fun z hz _ => hinj ((MonoidHom.mem_ker.mp hz).trans (map_one _).symm)) hψ hker hperf
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzk : (z : L') ∈ ψ.ker := by
    have h1 : ψ z ∈ Subgroup.center (LargeEvenProj (LargeEvenSpGroup K m)) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.2 l]
    rw [TableBSymp.center_spProj_eq_bot, Subgroup.mem_bot] at h1
    exact h1
  have hzp : (z : L') ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have h1 : z = 1 := Subtype.ext (hnp _ hzk hzp)
  rw [h1, orderOf_one] at hz
  exact hp.one_lt.ne hz

@[expose] def GGSpNonsplitSignedEltInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (m p : ℕ), 2 ≤ m → p.Prime →
    p ∣ Nat.card K + 1 → GGTorusSignedEltSC p (LargeEvenProj (LargeEvenSpGroup K m))

theorem ggSpNonsplitTorusInput_of_signedEltSC
    (h : GGSpNonsplitSignedEltInput) : GGSpNonsplitTorusInput := by
  intro K _ _ _ m p hm hp hpK
  have : NeZero m := ⟨by omega⟩
  refine ⟨h K m p hm hp hpK, ggCenterPrime_sp hp fun h2 => ?_⟩
  subst h2
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn] at hpK
  have h2 : 2 ∣ 2 ^ (n : ℕ) := dvd_pow_self 2 n.ne_zero
  have := (Nat.dvd_add_right h2).mp hpK
  omega

end CFSG.StandardType

module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.GH74.GLS.Basic
import CFSG.RankThree.PartTwo.Sec14.Item148ResProofThetaK
import CFSG.RankThree.PartTwo.Sec11.Item116R1Quot
import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofEnd

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow1523K

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem le_inSubgroup_theta {K N : Subgroup G} (hNK : N ≤ K)
    (hnorm : K ≤ Subgroup.normalizer (N : Set G)) (hsol : Group.IsSolvable N)
    (h3 : ¬ 3 ∣ Nat.card N) : N ≤ inSubgroup (aschbacherSolvableCore 3) K := by
  obtain ⟨-, -, -, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  set N' := N.subgroupOf K with hN'
  have e : N' ≃* N := Subgroup.subgroupOfEquivOfLe hNK
  have hN'n : N'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hnorm g.2) n).mp hn
  have hsol' : Group.IsSolvable N' :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have h3' : ¬ 3 ∣ Nat.card N' := by rwa [Nat.card_congr e.toEquiv]
  have hle := hmax N' hN'n hsol' h3'
  rw [inSubgroup, ← Subgroup.map_subgroupOf_eq_of_le hNK]
  exact Subgroup.map_mono hle

theorem nonempty_theta_quot_equiv {X K : Subgroup G} (hXK : X ≤ K)
    (hK : K ≤ X ⊔ inSubgroup (aschbacherSolvableCore 3) K) :
    Nonempty (↥X ⧸ aschbacherSolvableCore 3 ↥X ≃* ↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
  set θK := aschbacherSolvableCore 3 ↥K with hθK
  obtain ⟨hθs, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  obtain ⟨-, -, -, hmaxX, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  set ψ : ↥X →* ↥K ⧸ θK := (QuotientGroup.mk' θK).comp (Subgroup.inclusion hXK) with hψ
  have hmemker : ∀ x : ↥X, x ∈ ψ.ker ↔ Subgroup.inclusion hXK x ∈ θK := fun x => by
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hψs : Function.Surjective ψ := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective θK q
    have h2 : (X ⊔ inSubgroup (aschbacherSolvableCore 3) K).subgroupOf K =
        X.subgroupOf K ⊔ θK := by
      rw [inSubgroup, Subgroup.subgroupOf_sup hXK (Subgroup.map_subtype_le _)]
      congr 1
      rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    have hk : k ∈ X.subgroupOf K ⊔ θK := by
      rw [← h2, Subgroup.mem_subgroupOf]
      exact hK k.2
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hk
    refine ⟨⟨(y : G), hy⟩, ?_⟩
    have hy' : Subgroup.inclusion hXK ⟨(y : G), hy⟩ = y := Subtype.ext rfl
    rw [hψ, MonoidHom.comp_apply, hy', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, inv_mul_cancel_left]
    exact hz
  let f : ψ.ker →* θK :=
    { toFun := fun x => ⟨Subgroup.inclusion hXK x, (hmemker x).mp x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b h
    have h' : ((a : ↥X) : G) = ((b : ↥X) : G) := congrArg (fun t : θK => ((t : ↥K) : G)) h
    exact Subtype.ext (Subtype.ext h')
  have : Group.IsSolvable θK := hθs
  have hker3 : ¬ 3 ∣ Nat.card ψ.ker := fun h3 =>
    hθ3 (h3.trans (Subgroup.card_dvd_of_injective f hf))
  have hkerθ : ψ.ker ≤ aschbacherSolvableCore 3 ↥X :=
    hmaxX _ (MonoidHom.normal_ker ψ) (Group.isSolvable_of_isSolvable_injective hf) hker3
  obtain ⟨-, ⟨e⟩⟩ := Sec14.Res148.theta_quot_of_ker_le ψ hψs hkerθ hker3
  have hbot : aschbacherSolvableCore 3 (↥K ⧸ θK) = ⊥ :=
    Sec11.aschbacherSolvableCore_quotient_eq_bot ↥K
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot)⟩

theorem isPerfect_of_le_sup_coprime {K X S : Subgroup G} (hK : K = oPrimeResidualOf 3 K)
    (hXp : Group.IsPerfect ↥X) (hXK : X ≤ K) (hSK : S ≤ K)
    (hcop : Nat.Coprime 3 (Nat.card S)) (hKXS : K ≤ X ⊔ S) : Group.IsPerfect ↥K := by
  have hTK : ⁅K, K⁆ ≤ K := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
  have hKN : K ≤ Subgroup.normalizer ((⁅K, K⁆ : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (Subgroup.commutator_mono hTK le_rfl)
  have hXT : X ≤ ⁅K, K⁆ := by
    calc X = ⁅X, X⁆ := (Subgroup.isPerfect_iff.mp hXp).symm
      _ ≤ ⁅K, K⁆ := Subgroup.commutator_mono hXK hXK
  have hle : K ≤ ⁅K, K⁆ :=
    calc K = oPrimeResidualOf 3 K := hK
      _ ≤ ⁅K, K⁆ := Proof15Res7.oPrimeResidualOf_le_of_le_sup_coprime hcop (hSK.trans hKN)
        (hKXS.trans (sup_le_sup_right hXT S))
  exact Subgroup.isPerfect_iff.mpr (le_antisymm hTK hle)

theorem card_dvd_card_theta_quot {K P : Subgroup G} (hPK : P ≤ K) {T : Type*} [Group T]
    [IsSimpleGroup T] (φ : ↥P →* T) (hφ : Function.Surjective φ) (hT3 : 3 ∣ Nat.card T) :
    Nat.card T ∣ Nat.card (↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
  set θK := aschbacherSolvableCore 3 ↥K with hθK
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  set ρ : ↥P →* ↥K ⧸ θK := (QuotientGroup.mk' θK).comp (Subgroup.inclusion hPK) with hρ
  have hmemker : ∀ x : ↥P, x ∈ ρ.ker ↔ Subgroup.inclusion hPK x ∈ θK := fun x => by
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  let f : ρ.ker →* θK :=
    { toFun := fun x => ⟨Subgroup.inclusion hPK x, (hmemker x).mp x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b h
    have h' : ((a : ↥P) : G) = ((b : ↥P) : G) := congrArg (fun t : θK => ((t : ↥K) : G)) h
    exact Subtype.ext (Subtype.ext h')
  have hker3 : ¬ 3 ∣ Nat.card ρ.ker := fun h3 =>
    hθ3 (h3.trans (Subgroup.card_dvd_of_injective f hf))
  have hnorm : (ρ.ker.map φ).Normal := Subgroup.Normal.map (MonoidHom.normal_ker ρ) φ hφ
  have hbot : ρ.ker.map φ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map φ) with h | h
    · exact h
    · exfalso
      have h1 := Subgroup.card_map_dvd ρ.ker φ
      rw [h, Subgroup.card_top] at h1
      exact hker3 (hT3.trans h1)
  have hle : ρ.ker ≤ φ.ker := (Subgroup.map_eq_bot_iff _).mp hbot
  have h1 : φ.ker.index ∣ ρ.ker.index := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ,
    Subgroup.card_top] at h1
  exact h1.trans (Subgroup.card_subgroup_dvd_card _)

end CFSG.RankThree.PartTwo.Sec15.Sylow1523K

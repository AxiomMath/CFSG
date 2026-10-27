module

public import CFSG.RankThree.PartTwo.Sec21.Implications
import CFSG.RankThree.PartTwo.Sec18.Item18ResProofL34
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2129Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_inv_mul_mem_theta {Le H : Subgroup G}
    (ψ : lBar Le ≃* projSL 3 (GaloisField 2 2)) (hHL : H ≤ Le) (hH9 : Nat.card H = 9)
    (hH3 : IsPGroup 3 H) {u : G} (hu : u ∈ Le) (huH : u ∈ Subgroup.centralizer (H : Set G)) :
    ∃ h ∈ H, h⁻¹ * u ∈ inSubgroup (aschbacherSolvableCore 3) Le := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  set N := aschbacherSolvableCore 3 Le with hN
  have hN3 : ¬ 3 ∣ Nat.card N :=
    (solvable_prime_complement_core_characterization (H := Le) Nat.prime_three).2.2.1
  set ψ' := ψ.trans (Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with hψ'
  set f : Le →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2) :=
    ψ'.toMonoidHom.comp (QuotientGroup.mk' N) with hf
  have hker : ∀ x : Le, f x = 1 → x ∈ N := by
    intro x hx
    have h1 : ψ' (QuotientGroup.mk' N x) = ψ' 1 := by rw [map_one]; exact hx
    have h2 := ψ'.injective h1
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  set H' := H.subgroupOf Le with hH'
  have hinj : Function.Injective (f.comp H'.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : Le) ∈ N := hker _ hx
    have hxH : ((x : Le) : G) ∈ H := Subgroup.mem_subgroupOf.mp x.2
    obtain ⟨j, hj⟩ := hH3 ⟨_, hxH⟩
    have hx3 : ((x : Le) : G) ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hxo3 : orderOf (x : Le) ∣ 3 ^ j := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hx3
    have hxoN : orderOf (x : Le) ∣ Nat.card N := by
      rw [← Subgroup.orderOf_mk (x : Le) hxN]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (3 ^ j) (Nat.card N) :=
      Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3)
    have h1 : orderOf (x : Le) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hxo3 hxoN
    rw [orderOf_eq_one_iff] at h1
    exact Subtype.ext h1
  have hrange : (f.comp H'.subtype).range = H'.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hE9 : Nat.card (H'.map f) = 9 := by
    rw [← hrange, ← hH9]
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
  have hHne : H ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hH9
    omega
  obtain ⟨⟨h₀, hh₀⟩, hh₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hHne
  have hh₀1' : h₀ ≠ 1 := fun h => hh₀1 (Subtype.ext h)
  have hh₀' : (⟨h₀, hHL hh₀⟩ : Le) ∈ H' := Subgroup.mem_subgroupOf.mpr hh₀
  have hxE : f ⟨h₀, hHL hh₀⟩ ∈ H'.map f := ⟨_, hh₀', rfl⟩
  have hx1 : f ⟨h₀, hHL hh₀⟩ ≠ 1 := by
    intro h
    have h2 : (f.comp H'.subtype) ⟨_, hh₀'⟩ = (f.comp H'.subtype) 1 := by
      rw [map_one]
      exact h
    have h3 := hinj h2
    exact hh₀1' (congrArg (fun y : H' => ((y : Le) : G)) h3)
  have hC := Sec18.Item18ResProof.l34_centralizer_eq_of_mem hk hE9 hxE hx1
  have huC : f ⟨u, hu⟩ ∈ Subgroup.centralizer ({f ⟨h₀, hHL hh₀⟩} : Set _) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (⟨u, hu⟩ : Le) * ⟨h₀, hHL hh₀⟩ = ⟨h₀, hHL hh₀⟩ * ⟨u, hu⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp huH h₀ hh₀).symm
    rw [← map_mul, h1, map_mul]
  rw [hC] at huC
  obtain ⟨h', hh', hfh⟩ := huC
  have hpi : QuotientGroup.mk' N h' = QuotientGroup.mk' N ⟨u, hu⟩ := ψ'.injective hfh
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hpi
  refine ⟨(h' : G), Subgroup.mem_subgroupOf.mp hh', ⟨h'⁻¹ * ⟨u, hu⟩, hpi, ?_⟩⟩
  simp

end CFSG.RankThree.PartTwo.Sec21.Item2129Res3Proof

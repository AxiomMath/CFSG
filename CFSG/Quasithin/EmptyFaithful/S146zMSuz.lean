module

public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.StronglyEmbedded.BenderBorelTransport
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree
open scoped Pointwise

theorem exists_prime_dvd_two_pow_odd_sub_one (a : ℕ) (ha : 1 ≤ a) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ 2 ^ (2 * a + 1) - 1 ∧ ℓ ≠ 2 ∧ ℓ ≠ 3 := by
  have h2 : 2 ^ (2 * a + 1) % 2 = 0 := by
    rw [pow_succ]; simp
  have h3 : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    simp
  have hpos : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hne : 2 ^ (2 * a + 1) - 1 ≠ 1 := by omega
  refine ⟨(2 ^ (2 * a + 1) - 1).minFac, Nat.minFac_prime hne, Nat.minFac_dvd _, ?_, ?_⟩
  · intro h
    have := Nat.minFac_dvd (2 ^ (2 * a + 1) - 1)
    rw [h] at this
    omega
  · intro h
    have := Nat.minFac_dvd (2 ^ (2 * a + 1) - 1)
    rw [h] at this
    omega

section Model

variable {a : ℕ} {K : Type} [Field K]

theorem suzukiGroup_normalizer_dvd [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (S : Sylow 2 (suzukiGroup a K)) :
    (2 ^ (2 * a + 1) - 1) ∣ Nat.card ↥(Subgroup.normalizer
      ((S : Subgroup (suzukiGroup a K)) : Set (suzukiGroup a K))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q : ℕ := 2 ^ (2 * a + 1) with hq
  have hU : Nat.card (suzukiU a K) = q ^ 2 := (suzuki_unipotent_structure hK).2.1
  have hG : Nat.card (suzukiGroup a K) = q ^ 2 * (q - 1) * (q ^ 2 + 1) := suzuki_order hK
  have hq2 : q % 2 = 0 := by rw [hq, pow_succ]; simp
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hidx : (suzukiU a K).index = (q - 1) * (q ^ 2 + 1) := by
    have h := Subgroup.card_mul_index (suzukiU a K)
    rw [hU, hG] at h
    have hqpos : 0 < q ^ 2 := by positivity
    exact Nat.eq_of_mul_eq_mul_left hqpos (by rw [h]; ring)
  have hUp : IsPGroup 2 (suzukiU a K) := IsPGroup.of_card (n := 2 * (2 * a + 1)) (by
    rw [hU, hq, ← pow_mul]; ring_nf)
  have hodd : ¬ 2 ∣ (suzukiU a K).index := by
    rw [hidx]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h | h
    · omega
    · have : (q ^ 2 + 1) % 2 = 1 := by
        rw [Nat.add_mod, Nat.pow_mod, hq2]
      omega
  let SU : Sylow 2 (suzukiGroup a K) := hUp.toSylow hodd
  have hB : suzukiB a K ≤ Subgroup.normalizer ((suzukiU a K : Subgroup (suzukiGroup a K)) : Set _) :=
    sup_le Subgroup.le_normalizer (suzukiT_le_normalizer hK)
  have hBcard : Nat.card (suzukiB a K) = q ^ 2 * (q - 1) := by
    have := (suzuki_borel_structure hK).2.2.2.2.2.2.2
    rw [this]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (suzukiGroup a K) SU S
  have hmap : (SU : Subgroup (suzukiGroup a K)).map (MulAut.conj g).toMonoidHom = S := by
    change (g • SU : Sylow 2 (suzukiGroup a K)).toSubgroup = S.toSubgroup
    rw [hg]
  have hN : Subgroup.normalizer ((S : Subgroup (suzukiGroup a K)) : Set (suzukiGroup a K)) =
      (Subgroup.normalizer ((SU : Subgroup (suzukiGroup a K)) : Set (suzukiGroup a K))).map
        (MulAut.conj g).toMonoidHom := by
    rw [← hmap]
    exact (Subgroup.map_equiv_normalizer_eq (SU : Subgroup (suzukiGroup a K)) (MulAut.conj g)).symm
  rw [hN, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have h1 : Nat.card (suzukiB a K) ∣ Nat.card ↥(Subgroup.normalizer
      ((SU : Subgroup (suzukiGroup a K)) : Set (suzukiGroup a K))) :=
    Subgroup.card_dvd_of_le hB
  rw [hBcard] at h1
  exact (Dvd.intro_left _ rfl).trans h1

end Model

section Solv

variable {J : Type} [Group J] [Finite J]

theorem solvable_normalizer_of_cyclic_complement (S : Sylow 2 J) {D : Subgroup J} (hD : IsCyclic D)
    (hSD : (S : Subgroup J) ⊔ D = Subgroup.normalizer ((S : Subgroup J) : Set J)) :
    Group.IsSolvable ↥(Subgroup.normalizer ((S : Subgroup J) : Set J)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer ((S : Subgroup J) : Set J) with hNdef
  have hSN : (S : Subgroup J) ≤ N := Subgroup.le_normalizer
  have hDN : D ≤ N := hSD ▸ le_sup_right
  set S' : Subgroup ↥N := (S : Subgroup J).subgroupOf N with hS'
  have hSn : S'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSN).mpr le_rfl
  have hS'p : IsPGroup 2 ↥S' := S.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hSN).symm
  have hS's : Group.IsSolvable ↥S' := by
    have : Group.IsNilpotent ↥S' := hS'p.isNilpotent
    infer_instance
  have hmul : ((↑((S : Subgroup J) ⊔ D) : Set J)) = ↑(S : Subgroup J) * ↑D :=
    Subgroup.coe_mul_of_right_le_normalizer_left (S : Subgroup J) D hDN
  have hcomm : ∀ n : ↥N, ∃ d : ↥D, (QuotientGroup.mk n : ↥N ⧸ S') = QuotientGroup.mk ⟨(d : J), hDN d.2⟩ := by
    intro n
    have hn : (n : J) ∈ (↑((S : Subgroup J) ⊔ D) : Set J) := by rw [hSD]; exact n.2
    rw [hmul] at hn
    obtain ⟨s, hs, d, hd, hsd⟩ := hn
    refine ⟨⟨d, hd⟩, ?_⟩
    rw [QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    show ((n : J)⁻¹ * d) ∈ (S : Subgroup J)
    have hsd' : s * d = (n : J) := hsd
    have hdn : d⁻¹ ∈ Subgroup.normalizer ((S : Subgroup J) : Set J) := N.inv_mem (hDN hd)
    have h1 := (Subgroup.mem_normalizer_iff.mp hdn s⁻¹).mp ((S : Subgroup J).inv_mem hs)
    have : (n : J)⁻¹ * d = d⁻¹ * s⁻¹ * (d⁻¹)⁻¹ := by
      rw [← hsd']; group
    rw [this]
    exact h1
  have hq : Group.IsSolvable (↥N ⧸ S') := by
    refine Group.isSolvable_of_comm fun x y => ?_
    induction x using QuotientGroup.induction_on with
    | H n =>
      induction y using QuotientGroup.induction_on with
      | H n' =>
        obtain ⟨d, hd⟩ := hcomm n
        obtain ⟨d', hd'⟩ := hcomm n'
        rw [hd, hd', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        have := hD.isMulCommutative
        have h2 := mul_comm' d d'
        have h3 : (d : J) * (d' : J) = (d' : J) * (d : J) := congrArg Subtype.val h2
        exact h3
  exact Group.isSolvable_of_ker_le_range S'.subtype (QuotientGroup.mk' S')
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem suzuki_normalizer_solvable {f : ℕ} (hf : SuzukiModel J 2 f) (S : Sylow 2 J) :
    Group.IsSolvable ↥(Subgroup.normalizer ((S : Subgroup J) : Set J)) := by
  obtain ⟨-, a, ha, K, hKf, hKfin, hfa, hKcard, ⟨e⟩⟩ := hf
  subst hfa
  let e' : J ≃* Sz a := e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
    (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hKcard))
  have hB : fusionBenderBorel J (2 ^ (2 * a + 1)) 2 :=
    (bender_suzuki_borel_full a ha).map_mulEquiv e'.symm
  obtain ⟨-, ⟨D, hDc, -, -, hSD⟩, -⟩ := hB S
  exact solvable_normalizer_of_cyclic_complement S hDc hSD

theorem suzuki_normalizer_sylow {f : ℕ} (hf : SuzukiModel J 2 f)
    (S : Sylow 2 J) :
    Group.IsSolvable ↥(Subgroup.normalizer ((S : Subgroup J) : Set J)) ∧
      ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ 3 ∧
        ℓ ∣ Nat.card ↥(Subgroup.normalizer ((S : Subgroup J) : Set J)) := by
  refine ⟨suzuki_normalizer_solvable hf S, ?_⟩
  obtain ⟨-, a, ha, K, hKf, hKfin, hfa, hKcard, ⟨e⟩⟩ := hf
  subst hfa
  let S' : Sylow 2 (suzukiGroup a K) := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap : (S' : Subgroup (suzukiGroup a K)) = (S : Subgroup J).map e.toMonoidHom := rfl
  have hN : Subgroup.normalizer ((S' : Subgroup (suzukiGroup a K)) : Set (suzukiGroup a K)) =
      (Subgroup.normalizer ((S : Subgroup J) : Set J)).map e.toMonoidHom := by
    rw [hmap]
    exact (Subgroup.map_equiv_normalizer_eq (S : Subgroup J) e).symm
  have hdvd := suzukiGroup_normalizer_dvd (a := a) (K := K) hKcard S'
  rw [hN, Subgroup.card_map_of_injective e.injective] at hdvd
  obtain ⟨ℓ, hℓ, hℓd, h2, h3⟩ := exists_prime_dvd_two_pow_odd_sub_one a ha
  exact ⟨ℓ, hℓ, h2, h3, hℓd.trans hdvd⟩

end Solv

end CFSG.Quasithin

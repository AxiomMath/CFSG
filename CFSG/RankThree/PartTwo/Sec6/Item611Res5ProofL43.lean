module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res5ProofL43Unip
public import CFSG.RankThree.PartTwo.Sec6.Item611Res5ProofL43Inv
public import CFSG.RankThree.PartTwo.Sec21.ThreeLocalSporProofKS611
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemL43

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res5.L43

open Matrix CFSG.RankThree.PartTwo.Sec4.Item434RemL43
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem card_centralizer_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Nat.card (Subgroup.centralizer ({e x} : Set H)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun y => ?_)).symm
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  change y * x = x * y ↔ e y * e x = e x * e y
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

@[expose] def negOneSL : SL4 := ⟨-1, by decide⟩

theorem card_scalars : Nat.card (scalars 4 (ZMod 3)) = 2 := by
  have hdvd : Nat.card (scalars 4 (ZMod 3)) ∣ 2 := by
    have h := card_scalars_dvd (K := ZMod 3) (n := 4) (by norm_num)
    rwa [Nat.card_zmod] at h
  have hmem : negOneSL ∈ scalars 4 (ZMod 3) := mem_scalars_of_val (Or.inr rfl)
  have hne : negOneSL ≠ 1 := fun h => by
    have := congrArg (fun x : SL4 => (x : Mat4) 0 0) h
    revert this
    decide
  have h1 : Nat.card (scalars 4 (ZMod 3)) ≠ 1 := fun h => by
    rw [Subgroup.card_eq_one] at h
    rw [h, Subgroup.mem_bot] at hmem
    exact hne hmem
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd h h1
  · exact h

theorem card_comap_piL (H : Subgroup PSL43) : Nat.card (H.comap piL) = Nat.card H * 2 := by
  have h1 := (H.comap piL).card_mul_index
  have h2 := H.card_mul_index
  rw [Subgroup.index_comap_of_surjective (H := H) (f := piL) (proj_surjective 4 (ZMod 3))] at h1
  have h3 : Nat.card SL4 = Nat.card PSL43 * 2 := by
    rw [(scalars 4 (ZMod 3)).card_eq_card_quotient_mul_card_subgroup, card_scalars]
  have hidx : 0 < H.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h4 : Nat.card (H.comap piL) * H.index = Nat.card H * 2 * H.index := by
    rw [h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hidx h4

theorem comap_centralizer_piL {u : SL4} (hu : u ^ 3 = 1) :
    (Subgroup.centralizer ({piL u} : Set PSL43)).comap piL =
      Subgroup.centralizer ({u} : Set SL4) := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · exact mul_comm_of_proj_mul_comm hu
  · intro h
    rw [← map_mul, h, map_mul]

theorem card_centralizer_piL_mul_two {u : SL4} (hu : u ^ 3 = 1) :
    Nat.card (Subgroup.centralizer ({piL u} : Set PSL43)) * 2 =
      Nat.card (Subgroup.centralizer ({u} : Set SL4)) := by
  rw [← card_comap_piL, comap_centralizer_piL hu]

theorem exists_conj_mem_projUnitriangular {z : PSL43} (hz : orderOf z = 3) :
    ∃ g : PSL43, g⁻¹ * z * g ∈ projUnitriangular 4 (ZMod 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := ZMod 3) 3 (n := 4) (by norm_num)
  have hzp : IsPGroup 3 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL43 P Q
  refine ⟨g, ?_⟩
  have hzQ : z ∈ ((g • P : Sylow 3 PSL43) : Subgroup PSL43) := by
    rw [hg]
    exact hQ (Subgroup.mem_zpowers z)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply] at hzQ
  rw [← hP]
  exact hzQ

theorem card_centralizer_of_orderOf_eq_three {z : PSL43} (hz : orderOf z = 3) :
    Nat.card (Subgroup.centralizer ({z} : Set PSL43)) = 5832 ∨
      Nat.card (Subgroup.centralizer ({z} : Set PSL43)) = 1944 ∨
      Nat.card (Subgroup.centralizer ({z} : Set PSL43)) = 81 := by
  obtain ⟨g, hg⟩ := exists_conj_mem_projUnitriangular hz
  have hconj : Nat.card (Subgroup.centralizer ({g⁻¹ * z * g} : Set PSL43)) =
      Nat.card (Subgroup.centralizer ({z} : Set PSL43)) := by
    have h := card_centralizer_mulEquiv (MulAut.conj g⁻¹) z
    rwa [MulAut.conj_apply, inv_inv] at h
  have hz' : orderOf (g⁻¹ * z * g) = 3 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, hz]
  rw [← hconj]
  obtain ⟨u, hu, hzu⟩ := Subgroup.mem_map.mp hg
  rw [← hzu] at hz' ⊢
  have hu3 : u ^ 3 = 1 := by
    have h1 : piL (u ^ 3) = 1 := by
      have h := pow_orderOf_eq_one (piL u)
      rw [hz'] at h
      rw [map_pow, h]
    have h2 : u ^ 3 ∈ unitriangular 4 (ZMod 3) ⊓ scalars 4 (ZMod 3) :=
      ⟨(unitriangular 4 (ZMod 3)).pow_mem hu 3, proj_eq_one_iff.mp h1⟩
    rwa [unitriangular_inf_scalars, Subgroup.mem_bot] at h2
  have hu1 : u ≠ 1 := by
    rintro rfl
    change orderOf (piL 1) = 3 at hz'
    rw [map_one, orderOf_one] at hz'
    exact absurd hz' (by norm_num)
  have h2 := card_centralizer_piL_mul_two hu3
  change Nat.card (Subgroup.centralizer ({piL u} : Set PSL43)) = 5832 ∨
    Nat.card (Subgroup.centralizer ({piL u} : Set PSL43)) = 1944 ∨
    Nat.card (Subgroup.centralizer ({piL u} : Set PSL43)) = 81
  rcases card_centralizer_of_mem_unitriangular hu hu3 hu1 with h | h | h <;> rw [h] at h2 <;>
    omega

theorem mul_comm_of_pow_27 {k T : SL4} (hk : k ^ 27 = 1) (h : piL k * piL T = piL T * piL k) :
    k * T = T * k := by
  obtain ⟨c, hc⟩ : ∃ c, c = k * T * k⁻¹ * T⁻¹ := ⟨_, rfl⟩
  have hcZ : c ∈ scalars 4 (ZMod 3) := by
    rw [← proj_eq_one_iff, hc]
    change piL (k * T * k⁻¹ * T⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hcC : c ∈ Subgroup.center SL4 := scalars_le_center 4 (ZMod 3) hcZ
  have hconj : k * T * k⁻¹ = c * T := by rw [hc]; group
  have hpow : ∀ n : ℕ, k ^ n * T * (k ^ n)⁻¹ = c ^ n * T := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc k ^ (n + 1) * T * (k ^ (n + 1))⁻¹ = k * (k ^ n * T * (k ^ n)⁻¹) * k⁻¹ := by group
        _ = k * (c ^ n * T) * k⁻¹ := by rw [ih]
        _ = (k * c ^ n) * T * k⁻¹ := by group
        _ = (c ^ n * k) * T * k⁻¹ := by
          have hcn : c ^ n ∈ Subgroup.center SL4 := Subgroup.pow_mem _ hcC n
          rw [Subgroup.mem_center_iff.mp hcn k]
        _ = c ^ n * (k * T * k⁻¹) := by group
        _ = c ^ (n + 1) * T := by rw [hconj]; group
  have h27 := hpow 27
  rw [hk, one_mul, inv_one, mul_one] at h27
  have hc27 : c ^ 27 = 1 := by
    have := congrArg (· * T⁻¹) h27
    simpa using this.symm
  have hc2 : c ^ 2 = 1 := by
    have h := pow_card_eq_one' (G := scalars 4 (ZMod 3)) (x := ⟨c, hcZ⟩)
    rw [card_scalars] at h
    have h' := congrArg (fun x : scalars 4 (ZMod 3) => (x : SL4)) h
    simpa using h'
  have hc1 : c = 1 := by
    have : c ^ 27 = c := by
      rw [show 27 = 2 * 13 + 1 by norm_num, pow_succ, pow_mul, hc2, one_pow, one_mul]
    rw [← this, hc27]
  rw [hc1, one_mul] at hconj
  calc k * T = k * T * k⁻¹ * k := by group
    _ = T * k := by rw [hconj]

theorem not_dvd_card_centralizer_of_orderOf_eq_two {t : PSL43} (ht : orderOf t = 2) :
    ¬ 27 ∣ Nat.card (Subgroup.centralizer ({t} : Set PSL43)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, rfl⟩ := proj_surjective 4 (ZMod 3) t
  change orderOf (piL T) = 2 at ht
  have hT2 : T ^ 2 ∈ scalars 4 (ZMod 3) := by
    rw [← proj_eq_one_iff]
    change piL (T ^ 2) = 1
    rw [map_pow, ← ht, pow_orderOf_eq_one]
  have hT1 : T ∉ scalars 4 (ZMod 3) := by
    intro h
    have h1 : piL T = 1 := proj_eq_one_iff.mpr h
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hsq : (T : Mat4) * T = 1 ∨ (T : Mat4) * T = -1 := by
    rcases val_eq_one_or_neg_one_of_mem_scalars hT2 with h | h
    · left
      exact (congrArg (fun x : SL4 => (x : Mat4)) (pow_two T)).symm.trans h
    · right
      have h' : (T : Mat4) * T = ((T ^ 2 : SL4) : Mat4) :=
        (congrArg (fun x : SL4 => (x : Mat4)) (pow_two T)).symm
      exact h'.trans h
  have hne1 : (T : Mat4) ≠ 1 := fun h => hT1 (mem_scalars_of_val (Or.inl h))
  have hnem1 : (T : Mat4) ≠ -1 := fun h => hT1 (mem_scalars_of_val (Or.inr h))
  have hC := card_centralizer_of_sq hsq hne1 hnem1
  intro h27
  set H := Subgroup.centralizer ({piL T} : Set PSL43)
  have hN : 27 ∣ Nat.card (H.comap piL) := by
    rw [card_comap_piL]
    exact h27.mul_right 2
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H.comap piL) 3 (n := 3)
    (by norm_num; exact hN)
  have hle : K.map (H.comap piL).subtype ≤ Subgroup.centralizer ({T} : Set SL4) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk27 : (k : SL4) ^ 27 = 1 := by
      have h1 : ((k : H.comap piL) : SL4) ^ 27 = ((k ^ 27 : H.comap piL) : SL4) := by
        simp
      have h2 : (k : H.comap piL) ^ 27 = 1 := by
        have := pow_card_eq_one' (G := K) (x := ⟨k, hk⟩)
        rw [hK] at this
        exact congrArg Subtype.val this
      rw [h1, h2, Subgroup.coe_one]
    have hkc : piL (k : SL4) * piL T = piL T * piL (k : SL4) :=
      Subgroup.mem_centralizer_singleton_iff.mp (k : H.comap piL).2
    exact mul_comm_of_pow_27 hk27 hkc
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (H.comap piL).subtype_injective, hK] at hdvd
  rcases hC with h | h <;> rw [h] at hdvd <;> norm_num at hdvd

end CFSG.RankThree.PartTwo.Sec6.Res611Res5.L43

namespace CFSG.RankThree.PartTwo.Sec6

open Res611Res5.L43 CFSG.RankThree.PartTwo.Sec4.Item434RemL43
open CFSG.Assembly.RankThreeEven (projSL)

theorem kL43ThreeClassData_holds : KL43ThreeClassData := by
  set e := projSLEquivPSL43
  refine ⟨fun z hz => ?_, fun t ht => ?_⟩
  · have hz' : orderOf (e z) = 3 := by rw [MulEquiv.orderOf_eq, hz]
    rw [← card_centralizer_mulEquiv e z]
    rcases card_centralizer_of_orderOf_eq_three hz' with h | h | h <;> rw [h]
    · exact ⟨3, 6, by norm_num, Or.inr (Or.inr ⟨rfl, by norm_num⟩)⟩
    · exact ⟨3, 5, by norm_num, Or.inr (Or.inr ⟨rfl, le_rfl⟩)⟩
    · exact ⟨0, 4, by norm_num, Or.inl ⟨by norm_num, by norm_num⟩⟩
  · have ht' : orderOf (e t) = 2 := by rw [MulEquiv.orderOf_eq, ht]
    rw [← card_centralizer_mulEquiv e t]
    exact not_dvd_card_centralizer_of_orderOf_eq_two ht'

theorem kCentCharThreeL43_holds : KCentCharThreeL43 :=
  kCentCharThreeL43_of kL43ThreeClassData_holds

end CFSG.RankThree.PartTwo.Sec6

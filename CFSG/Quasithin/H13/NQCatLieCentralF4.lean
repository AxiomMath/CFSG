module

public import CFSG.Quasithin.H13.NQCatLieCentralCore
public import CFSG.LieType.Ree.LargeReeInvolutionFusionCoords

public section

namespace CFSG.Quasithin.H13.NQCat.LieCentral.F4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom f4i)

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

omit [Finite K] [CharP K F4.prime] in
theorem sylowL_zero_eq :
    sylowL m K (0 : K) = 1 := by
  simp [sylowL, sylowX, largeReeSigma_zero, pinnedX_zero]

omit [Finite K] [CharP K F4.prime] in
theorem sylowV_eq_sylowB (b c : K) :
    sylowV m K 0 b c 0 0 0 0 0 0 0 0 0 = sylowB m K b c := by
  simp [sylowV, sylowA, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL, sylowX,
    largeReeSigma_zero, pinnedX_zero]

omit [Finite K] [CharP K F4.prime] in
theorem sylowV_eq_sylowH_mul_sylowL
    (i l : K) : sylowV m K 0 0 0 0 0 0 0 0 i 0 0 l = sylowH m K 0 i * sylowL m K l := by
  simp [sylowV, sylowA, sylowB, sylowD, sylowF, sylowJ, sylowK, sylowX, largeReeSigma_zero,
    pinnedX_zero]

theorem sylowA_mem
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (s : K) : sylowA m K s ∈ F4.reeFixedPosUnipotent K m :=
  reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK s)

theorem sylowB_mem
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (b c : K) :
    sylowB m K b c ∈ F4.reeFixedPosUnipotent K m :=
  reeFixedOrbitUnipotent_le _ (sylowB_mem_U2 hK b c)

theorem sylowB_one_zero_mul
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (b : K) :
    sylowB m K 1 0 * sylowB m K b 0 = sylowB m K (1 + b) b := by
  have h := largeReeCoord_mul hK 1 0 b 0
  rw [largeReeSigma_one, zero_add, zero_add, one_mul] at h
  rw [sylowB_eq_largeReeCoord, sylowB_eq_largeReeCoord, sylowB_eq_largeReeCoord]
  exact h

theorem sylowB_one_zero_sq
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    sylowB m K 1 0 * sylowB m K 1 0 = sylowB m K 0 1 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [sylowB_one_zero_mul hK, CharTwo.add_self_eq_zero]

omit [Finite K] in
theorem eq_zero_of_commute
    {b c : K} (h : sylowB m K b c * sylowL m K 1 = sylowL m K 1 * sylowB m K b c) : b = 0 := by
  rw [← sylowV_eq_sylowB] at h
  exact ((sylowV_commute_sylowL_one_iff 0 b c 0 0 0 0 0 0 0 0 0).1 h).1

theorem not_relIndex_le_two
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) (i : K) {l : K} (hl : l ≠ 0) :
    ¬ (F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer
        ({sylowH m K 0 i * sylowL m K l} : Set (ModGL F4.tag K))).relIndex
          (F4.reeFixedPosUnipotent K m) ≤ 2 := by
  intro hidx
  have : CharP K 2 := ‹CharP K F4.prime›
  have : Finite (ModGL F4.tag K) := finite_modGL
  set r : Kˣ := Units.mk0 l⁻¹ (inv_ne_zero hl) with hr
  set t := pairedTorusHom m (f4i 1) (f4i 2) (r ^ ((2 : ℤ) * 2 ^ m + 2)) with ht
  have htN : t ∈ Subgroup.normalizer (F4.reeFixedPosUnipotent K m : Set (ModGL F4.tag K)) :=
    reeFixedBorel_le_normalizer_reeFixedPosUnipotent
      (reeFixedTorus_le_reeFixedBorel (torusTwo_mem hK _))
  have e : t * (sylowH m K 0 i * sylowL m K l) * t⁻¹ = sylowH m K 0 i * sylowL m K 1 := by
    rw [weyl_conj_mul, ht, torusTwo_conj_sylowH hK, torusTwo_conj_sylowL hK, zpow_one_sub_surj hK,
      hr, Units.val_mk0, inv_mul_cancel₀ hl]
  rw [← relIndex_inf_centralizer_conj htN, e] at hidx
  have hnot : ∀ b c : K, b ≠ 0 → sylowB m K b c ∉
      Subgroup.centralizer ({sylowH m K 0 i * sylowL m K 1} : Set (ModGL F4.tag K)) := by
    intro b c hb hmem
    rw [Subgroup.mem_centralizer_singleton_iff] at hmem
    have hzB := commute_centralZ hm hK (sylowB_mem hK b c) i
    rw [← sylowH_zero_eq_centralZ] at hzB
    refine hb (eq_zero_of_commute (m := m) (c := c) (mul_left_cancel (a := sylowH m K 0 i) ?_))
    calc sylowH m K 0 i * (sylowB m K b c * sylowL m K 1) =
        sylowB m K b c * sylowH m K 0 i * sylowL m K 1 := by rw [← mul_assoc, ← hzB]
      _ = sylowH m K 0 i * sylowL m K 1 * sylowB m K b c := by rw [mul_assoc, hmem]
      _ = sylowH m K 0 i * (sylowL m K 1 * sylowB m K b c) := by rw [mul_assoc]
  obtain ⟨b, hb0, hb1⟩ : ∃ b : K, b ≠ 0 ∧ b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun b _ => by
      by_cases hb : b = 0
      · exact Or.inl hb
      · exact Or.inr (hcon b hb)
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ, hK, Set.ncard_pair zero_ne_one] at h2
    have h8 : 8 ≤ 2 ^ (2 * m + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h1 := mul_mem_of_relIndex_le_two hidx (sylowB_mem hK 1 0) (sylowB_mem hK b 0)
    (hnot 1 0 one_ne_zero) (hnot b 0 hb0)
  rw [sylowB_one_zero_mul hK] at h1
  exact hnot (1 + b) b (fun h0 => hb1 (eq_of_add_eq_zero_two h0).symm) h1

theorem mem_centralizer_of_relIndex_le_two
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) {x : ModGL F4.tag K}
    (hx : x ∈ F4.reeFixedPosUnipotent K m)
    (hidx : (F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer
      ({x} : Set (ModGL F4.tag K))).relIndex (F4.reeFixedPosUnipotent K m) ≤ 2) :
    x ∈ Subgroup.centralizer (F4.reeFixedPosUnipotent K m : Set (ModGL F4.tag K)) := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hq : 2 < Nat.card K := by
    rw [hK]
    calc 2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let φ : Multiplicative K →* ModGL F4.tag K :=
    { toFun := fun s => sylowA m K (Multiplicative.toAdd s)
      map_one' := sylowA_zero
      map_mul' := fun s s' => (sylowA_mul hK _ _).symm }
  obtain ⟨a, ha, hxa⟩ : ∃ a : K, a ≠ 0 ∧ sylowA m K a * x = x * sylowA m K a :=
    exists_ne_zero_commute_of_hom (P := F4.reeFixedPosUnipotent K m) φ
      (fun s s' hss => Multiplicative.toAdd.injective (sylowA_injective hss))
      (fun s => sylowA_mem hK _) hq hidx
  set s : Kˣ := Units.mk0 (a⁻¹ ^ 2 ^ m) (pow_ne_zero _ (inv_ne_zero ha)) with hs
  set t := pairedTorusHom m (f4i 0) (f4i 3) s with ht
  have htN : t ∈ Subgroup.normalizer (F4.reeFixedPosUnipotent K m : Set (ModGL F4.tag K)) :=
    reeFixedBorel_le_normalizer_reeFixedPosUnipotent
      (reeFixedTorus_le_reeFixedBorel (torusOne_mem hK s))
  have htA : t * sylowA m K a * t⁻¹ = sylowA m K 1 := by
    rw [ht, torusOne_conj_sylowA hK, hs, Units.val_mk0, largeReeSigma_pow hK, inv_mul_cancel₀ ha]
  have hyU : t * x * t⁻¹ ∈ F4.reeFixedPosUnipotent K m :=
    (Subgroup.mem_normalizer_iff.1 htN x).1 hx
  have hidx' : (F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer
      ({t * x * t⁻¹} : Set (ModGL F4.tag K))).relIndex (F4.reeFixedPosUnipotent K m) ≤ 2 := by
    rw [relIndex_inf_centralizer_conj htN]
    exact hidx
  have hyA := conj_mul_conj_comm (g := t) hxa
  rw [htA] at hyA
  have hyB := mul_self_mem_of_relIndex_le_two hidx' (sylowB_mem hK 1 0)
  rw [sylowB_one_zero_sq hK, Subgroup.mem_centralizer_singleton_iff] at hyB
  obtain ⟨z, -, hz⟩ := (bijOn_sylowVec hK).2.2 hyU
  rw [sylowVec] at hz
  rw [← hz] at hyA hyB hidx'
  obtain ⟨hb, hc, hf, hg, hh, hj⟩ :=
    (sylowV_commute_sylowA_one_iff _ _ _ _ _ _ _ _ _ _ _ _).1 hyA.symm
  obtain ⟨ha', hd, he, hk⟩ := (sylowV_commute_sylowB_iff _ _ _ _ _ _ _ _ _ _ _ _).1 hyB.symm
  rw [ha', hb, hc, hd, he, hf, hg, hh, hj, hk, sylowV_eq_sylowH_mul_sylowL] at hz hidx'
  have hl : z 11 = 0 := by
    by_contra hl
    exact not_relIndex_le_two hm hK (z 8) hl hidx'
  rw [hl, sylowL_zero_eq, mul_one, sylowH_zero_eq_centralZ] at hz
  refine mem_centralizer_of_conj htN (Subgroup.mem_centralizer_iff.2 fun u hu => ?_)
  rw [← hz]
  exact commute_centralZ hm hK hu (z 8)

theorem centralIndex_f4
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    CentralIndex ↥(F4.reeGamma K m) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hUC : F4.reeFixedPosUnipotent K m ≤ F4.reeGamma K m := reeFixedPosUnipotent_le_reeGamma
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (F4.reeFixedPosUnipotent K m) (F4.reeGamma K m) :=
    ⟨hUC, isPGroup_reeFixedPosUnipotent_subgroupOf.of_equiv (Subgroup.subgroupOfEquivOfLe hUC),
      not_dvd_index_reeFixedPosUnipotent⟩
  exact centralIndex_of_le hUC hU fun x hx hidx =>
    mem_centralizer_of_relIndex_le_two hm hK hx hidx

end CFSG.Quasithin.H13.NQCat.LieCentral.F4

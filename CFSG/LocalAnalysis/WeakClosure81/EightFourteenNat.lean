module

public import CFSG.LocalAnalysis.WeakClosure81.EightFourteenTwelveTwo
public import CFSG.LocalAnalysis.WeakClosure81.NatSumMain
public import CFSG.LocalAnalysis.WeakClosure81.W15Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Open Subgroup

private theorem no_index_lt_four_lt_five {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hcard : Nat.card X = 60) {L : Subgroup X} (h1 : 1 < L.index) (h5 : L.index < 5) : False := by
  have hne : L ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at h1
    omega
  have hcore : L.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ Subgroup.normalCore_le L)) hne
  have hidx := Subgroup.index_normalCore_le_factorial_index L
  rw [hcore, Subgroup.index_bot, hcard] at hidx
  interval_cases L.index <;> norm_num at hidx

theorem isPSL_two_two_two_klein {X : Type} [Group X] (hX : CFSG.Quasithin.IsPSL 2 2 2 X)
    {B F : Subgroup X} (hB : B.index = 5) (hF : IsElemAbelian 2 F) (hFc : Nat.card F = 4)
    (hFB : F ≤ B) :
    CFSG.Quasithin.IsBorelIn (⊤ : Subgroup X) B ∧ (F.subgroupOf B).Normal ∧
      ∀ L : Subgroup X, F ≤ L → ¬ L ≤ B → L = ⊤ := by
  classical
  have hXcard : Nat.card X = 60 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four hX
  haveI hXfin : Finite X := Nat.finite_of_card_ne_zero (by rw [hXcard]; norm_num)
  have hBender : CFSG.Open.fusionIsBenderGroup X :=
    CFSG.QuasithinUnique.A5.C25.fusionIsBenderGroup_of_isPSL hX
  haveI hsimp : IsSimpleGroup X :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hBender
  have hBne : B ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at hB
    omega
  have hBcard : Nat.card B = 12 := by
    have h := Subgroup.card_mul_index (H := B)
    rw [hB, hXcard] at h
    omega
  have hFpg : IsPGroup 2 F := hF.isPGroup
  have hFindex : F.index = 15 := by
    have h := Subgroup.card_mul_index (H := F)
    rw [hFc, hXcard] at h
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFnotdvd : ¬ 2 ∣ F.index := by rw [hFindex]; norm_num
  let Q : Sylow 2 X := hFpg.toSylow hFnotdvd
  have hQcoe : (Q : Subgroup X) = F := IsPGroup.toSylow_coe hFpg hFnotdvd
  have hFsyl : CFSG.QuasithinUnique.IsSylowTwoOf F ⊤ := by
    refine ⟨le_top, hFpg, ?_⟩
    have hidx : (F.subgroupOf ⊤).index = F.index := Subgroup.relIndex_top_right F
    rw [hidx, hFindex]
    norm_num
  have hBN : B ≤ Subgroup.normalizer (F : Set X) := by
    have h := CFSG.QuasithinUnique.Bridge.Over.le_normalizer_of_bender hBender Q
      (hQcoe.symm ▸ hFB) hBne
    simpa [hQcoe] using h
  have hFnormB : (F.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFB).mpr hBN
  have hNne : Subgroup.normalizer (F : Set X) ≠ ⊤ := by
    intro htop
    have hFnormal : F.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal F with hb | ht
    · have h1 : Nat.card F = 1 := by rw [hb, Subgroup.card_bot]
      omega
    · have htop4 : Nat.card (⊤ : Subgroup X) = 4 := by rw [← ht, hFc]
      rw [Subgroup.card_top] at htop4
      omega
  have hNidx_dvd : (Subgroup.normalizer (F : Set X)).index ∣ 5 := by
    have h := Subgroup.index_dvd_of_le hBN
    rw [hB] at h
    exact h
  have hNidx : (Subgroup.normalizer (F : Set X)).index = 5 := by
    have hmem : (Subgroup.normalizer (F : Set X)).index ∈ Nat.divisors 5 :=
      Nat.mem_divisors.mpr ⟨hNidx_dvd, by norm_num⟩
    rw [show Nat.divisors 5 = {1, 5} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have hN1 : (Subgroup.normalizer (F : Set X)).index ≠ 1 :=
      fun h => hNne (Subgroup.index_eq_one.mp h)
    rcases hmem with h | h
    · exact absurd h hN1
    · exact h
  have hNcard : Nat.card (Subgroup.normalizer (F : Set X)) = 12 := by
    have hcardN := Subgroup.card_mul_index (Subgroup.normalizer (F : Set X))
    rw [hNidx, hXcard] at hcardN
    omega
  have hNF : Subgroup.normalizer (F : Set X) = B := by
    refine le_antisymm ?_ hBN
    exact (Subgroup.eq_of_le_of_card_ge hBN (by rw [hBcard, hNcard])).ge
  refine ⟨?_, hFnormB, ?_⟩
  · refine ⟨F, hFsyl, ?_⟩
    rw [hNF, top_inf_eq]
  · intro L hFL hLB
    have hidx_dvd : L.index ∣ 15 := by
      have h := Subgroup.index_dvd_of_le hFL
      rw [hFindex] at h
      exact h
    have hmem : L.index ∈ Nat.divisors 15 := Nat.mem_divisors.mpr ⟨hidx_dvd, by norm_num⟩
    rw [show Nat.divisors 15 = {1, 3, 5, 15} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact Subgroup.index_eq_one.mp h
    · exact (no_index_lt_four_lt_five hXcard (L := L)
        (by rw [h]; norm_num) (by rw [h]; norm_num)).elim
    · have hLne : L ≠ ⊤ := by
        intro htop
        rw [htop, Subgroup.index_top] at h
        omega
      have hLN : L ≤ Subgroup.normalizer (F : Set X) := by
        have h' := CFSG.QuasithinUnique.Bridge.Over.le_normalizer_of_bender hBender Q
          (hQcoe.symm ▸ hFL) hLne
        simpa [hQcoe] using h'
      rw [hNF] at hLN
      exact absurd hLN hLB
    · have hcardL : Nat.card L = 4 := by
        have hcard := Subgroup.card_mul_index (H := L)
        rw [h, hXcard] at hcard
        omega
      have hLF : F = L := Subgroup.eq_of_le_of_card_ge hFL (by rw [hcardL, hFc])
      exact absurd (hLF ▸ hFB) hLB

theorem commSub_top_eq_top {X : Type} [Group X] (hX : CFSG.Quasithin.IsPSL 2 2 2 X)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : X →* LGL 2 W)
    {B : Subgroup X} {Z : Submodule (ZMod 2) W} (hB : B.index = 5)
    (hstab : ∀ g : X, g ∈ B ↔ ∀ z ∈ Z, ρ g z ∈ Z)
    (hreg : ∀ x ∈ B, Odd (orderOf x) → x ≠ 1 → ∀ z ∈ Z, ρ x z = z → z = 0)
    (hgen : ⨆ g : X, Z.map (ρ g : W →ₗ[ZMod 2] W) = ⊤) :
    commSub ((⊤ : Subgroup X).map ρ) = ⊤ := by
  classical
  have hXcard : Nat.card X = 60 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four hX
  haveI hXfin : Finite X := Nat.finite_of_card_ne_zero (by rw [hXcard]; norm_num)
  have hBcard : Nat.card B = 12 := by
    have h := Subgroup.card_mul_index (H := B)
    rw [hB, hXcard] at h
    omega
  have h3 : 3 ∣ Nat.card B := by rw [hBcard]; norm_num
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 h3
  have hx3' : orderOf (x : X) = 3 := by
    rw [Subgroup.orderOf_coe, hx3]
  have hodd : Odd (orderOf (x : X)) := by rw [hx3']; norm_num
  have hxne : (x : X) ≠ 1 := by
    intro h1
    have : orderOf (x : X) = 1 := by rw [h1, orderOf_one]
    omega
  have hxmem : (x : X) ∈ B := x.2
  let T : Z →ₗ[ZMod 2] Z :=
    { toFun := fun z => ⟨ρ (x : X) (z : W) - (z : W), by
        exact Z.sub_mem ((hstab (x : X)).mp hxmem (z : W) z.2) z.2⟩
      map_add' := fun a b => Subtype.ext (by
        simp only [LinearEquiv.map_add, Submodule.coe_add, map_add, add_sub_add_comm])
      map_smul' := fun c a => Subtype.ext (by
        simp only [LinearEquiv.map_smul, Submodule.coe_smul, smul_sub, RingHom.id_apply]) }
  have hinj : Function.Injective T := by
    intro a b hab
    have h' : ρ (x : X) (a : W) - (a : W) = ρ (x : X) (b : W) - (b : W) :=
      congrArg Subtype.val hab
    have hzero : ρ (x : X) ((a : W) - (b : W)) - ((a : W) - (b : W)) = 0 := by
      rw [map_sub]
      calc ρ (x : X) (a : W) - ρ (x : X) (b : W) - ((a : W) - (b : W))
          = (ρ (x : X) (a : W) - (a : W)) - (ρ (x : X) (b : W) - (b : W)) := by abel
        _ = 0 := by rw [h', sub_self]
    have hz : (a : W) - (b : W) = 0 :=
      hreg (x : X) hxmem hodd hxne _ (Z.sub_mem a.2 b.2) (sub_eq_zero.mp hzero)
    exact Subtype.ext (sub_eq_zero.mp hz)
  have hsurj : Function.Surjective T := Finite.injective_iff_surjective.mp hinj
  have hZle : Z ≤ commSub ((⊤ : Subgroup X).map ρ) := by
    intro z hz
    obtain ⟨z', hz'⟩ := hsurj ⟨z, hz⟩
    have hval : ρ (x : X) (z' : W) - (z' : W) = z := congrArg Subtype.val hz'
    rw [← hval]
    exact sub_mem_commSub ((⊤ : Subgroup X).map ρ)
      (Subgroup.mem_map.mpr ⟨x, Subgroup.mem_top x, rfl⟩) (z' : W)
  have hsup_le : (⨆ g : X, Z.map (ρ g : W →ₗ[ZMod 2] W)) ≤ commSub ((⊤ : Subgroup X).map ρ) := by
    refine iSup_le fun g => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro z hz
    exact map_mem_commSub ((⊤ : Subgroup X).map ρ)
      (Subgroup.mem_map.mpr ⟨g, Subgroup.mem_top g, rfl⟩) (hZle hz)
  exact top_le_iff.mp (hgen ▸ hsup_le)

theorem natural_of_klein_fixed (h122one : W3Lem122One) (h122two : W3Lem122Two)
    {X : Type} [Group X] (hX : CFSG.Quasithin.IsPSL 2 2 2 X)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : X →* LGL 2 W)
    {B F : Subgroup X} {Z : Submodule (ZMod 2) W} (hB : B.index = 5)
    (hstab : ∀ g : X, g ∈ B ↔ ∀ z ∈ Z, ρ g z ∈ Z) (hF : IsElemAbelian 2 F) (hFc : Nat.card F = 4)
    (hFB : F ≤ B) (hquad : RepQuad ρ F) (hFZ : ∀ f ∈ F, ∀ z ∈ Z, ρ f z = z)
    (hZ : Module.finrank (ZMod 2) Z ≤ 2)
    (hgen : ⨆ g : X, Z.map (ρ g : W →ₗ[ZMod 2] W) = ⊤) :
    Module.finrank (ZMod 2) Z = 2 ∧
      (∀ x ∈ B, Odd (orderOf x) → x ≠ 1 → ∀ z ∈ Z, ρ x z = z → z = 0) ∧
      IsNatSL2Section ρ ⊥ ⊤ (fixSub ((⊤ : Subgroup X).map ρ)) 2 := by
  obtain ⟨hBor, _hFnorm, hmin⟩ := isPSL_two_two_two_klein hX hB hF hFc hFB
  have hS : Setting12One ρ B Z F 2 2 :=
    { type := Or.inl hX
      borel := hBor
      stab := hstab
      A_le_B := hFB
      A_elem := hF
      A_card := by rw [hFc]; norm_num
      one_lt_m := by norm_num
      quad := hquad }
  obtain ⟨_hn, hZfin, hreg⟩ := h122two ρ B Z F 2 2 hS hmin hZ
  refine ⟨hZfin, hreg, ?_⟩
  have hcomm : commSub ((⊤ : Subgroup X).map ρ) = ⊤ :=
    commSub_top_eq_top hX ρ hB hstab hreg hgen
  have hsum := h122one ρ B Z F 2 2 hS hmin
  have hcE : cE ((⊤ : Subgroup X).map ρ) = fixSub ((⊤ : Subgroup X).map ρ) := by
    unfold cE
    rw [hcomm, inf_top_eq]
  rw [hcE, hcomm] at hsum
  exact NatSum.isNatSL2Section_of_isSumNatSection_of_line hX ρ hB hstab hF hFc hFB hFZ hZfin hreg
    hgen hsum

end CFSG.LocalAnalysis.WeakClosure81

end

module

public import CFSG.ClassicalGroups.UnitaryFlag.SplitTorus
public import CFSG.LocalAnalysis.UniquenessCase.Lie.BorelSU
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanQuotientBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanQuotientTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)

private theorem card_map_hypUnitriangular {f R ε : ℕ} {L : Type} [Field L] [Finite L]
    {K : Type} [Group K] [Finite K] (h : UnitaryFieldData 2 f L)
    (α : hypSU h R ε →* K) (hα : Function.Surjective α)
    (hker : ∀ s, α s = 1 → s ∈ hypScalars h R ε) (hR : 1 ≤ R) (hε : ε ≤ 1) :
    Nat.card ((hypUnitriangular h R ε).map α) =
      2 ^ (Nat.card K).factorization 2 := by
  have hf1 : 1 ≤ f := h.one_le
  have hkerodd : Odd (Nat.card α.ker) := by
    have hZcard : Nat.card (hypScalars h R ε) = Nat.gcd (2 * R + ε) (2 ^ f + 1) := by
      have := card_hypScalars (p := 2) (f := f) (K := L) (r := R) (ε := ε) h (by omega)
      simpa using this
    have hkerdvd : Nat.card α.ker ∣ Nat.card (hypScalars h R ε) := Subgroup.card_dvd_of_le hker
    have hoddq : Odd (2 ^ f + 1) :=
      (Nat.even_pow.2 ⟨even_two, by omega⟩).add_odd odd_one
    have hoddgcd : Odd (Nat.gcd (2 * R + ε) (2 ^ f + 1)) :=
      Odd.of_dvd_nat hoddq (Nat.gcd_dvd_right _ _)
    rw [hZcard] at hkerdvd
    exact Odd.of_dvd_nat hoddgcd hkerdvd
  have hUcard : Nat.card (hypUnitriangular h R ε) =
      2 ^ (Nat.card (hypSU h R ε)).factorization 2 := by
    rw [(unitary_order_and_Sylow h (by omega) hε).1, ← (card_hypSU h (by omega)).2]
  have hdisj : hypUnitriangular h R ε ⊓ α.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx1 : x ∈ hypScalars h R ε := hker x hx.2
    have hx2 : x ∈ hypUnitriangular h R ε ⊓ hypScalars h R ε := ⟨hx.1, hx1⟩
    rw [hypUnitriangular_inf_hypScalars h (by omega) hε, Subgroup.mem_bot] at hx2
    exact hx2
  have hαU_inj : Set.InjOn α ((hypUnitriangular h R ε : Subgroup (hypSU h R ε)) :
      Set (hypSU h R ε)) := by
    intro x hx y hy hxy
    have hmem : x * y⁻¹ ∈ hypUnitriangular h R ε ⊓ α.ker := by
      refine ⟨(hypUnitriangular h R ε).mul_mem hx ((hypUnitriangular h R ε).inv_mem hy), ?_⟩
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp hmem
  have hcardUmap : Nat.card ((hypUnitriangular h R ε).map α) =
      Nat.card (hypUnitriangular h R ε) := by
    let f : (hypUnitriangular h R ε) → ((hypUnitriangular h R ε).map α) :=
      fun x => ⟨α x, Subgroup.mem_map_of_mem α x.2⟩
    have hf : Function.Bijective f := by
      refine ⟨fun x y hxy => ?_, fun y => ?_⟩
      · exact Subtype.ext (hαU_inj x.2 y.2 (congrArg Subtype.val hxy))
      · obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
        refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
        change α x = (y : K)
        exact hxy
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
  have hfacK2 : (Nat.card K).factorization 2 = (Nat.card (hypSU h R ε)).factorization 2 := by
    have hmul := Subgroup.card_ker_mul_card_of_surjective hα
    have hker2 : (Nat.card α.ker).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hkerodd.not_two_dvd_nat
    have hmain := congrArg (fun n : ℕ => n.factorization 2) hmul
    have hk0 : Nat.card α.ker ≠ 0 := Nat.card_pos.ne'
    have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
    rw [Nat.factorization_mul hk0 hK0, Finsupp.add_apply, hker2, zero_add] at hmain
    exact hmain
  rw [hcardUmap, hUcard, hfacK2]

private theorem isSylowTwoOf_map_hypUnitriangular {f R ε : ℕ} {L : Type} [Field L] [Finite L]
    {K : Type} [Group K] [Finite K] (h : UnitaryFieldData 2 f L)
    (α : hypSU h R ε →* K) (hα : Function.Surjective α)
    (hker : ∀ s, α s = 1 → s ∈ hypScalars h R ε) (hR : 1 ≤ R) (hε : ε ≤ 1) :
    CFSG.QuasithinUnique.IsSylowTwoOf ((hypUnitriangular h R ε).map α) ⊤ := by
  have hcardUmapSylow := card_map_hypUnitriangular h α hα hker hR hε
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P2 : Sylow 2 K := Sylow.ofCard ((hypUnitriangular h R ε).map α) hcardUmapSylow
  have hP2 : (P2 : Subgroup K) = (hypUnitriangular h R ε).map α := Sylow.coe_ofCard _ _
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hP2]
    exact P2.isPGroup'
  · have hP2' : ((hypUnitriangular h R ε).map α : Subgroup K) = (P2 : Subgroup K) := hP2.symm
    rw [hP2']
    change ¬ 2 ∣ (P2 : Subgroup K).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact P2.not_dvd_index

private theorem exists_splitTorus_data {f R ε : ℕ} {L : Type} [Field L] [Finite L]
    (h : UnitaryFieldData 2 f L) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrd : r ∣ 2 ^ f - 1) (hR : 1 ≤ R) (hε : ε ≤ 1) :
    ∃ (μ : Subgroup Lˣ) (hμ : SplitInv h μ) (D : Subgroup (hypSU h R ε)),
      Odd (Nat.card μ) ∧ Nat.card μ = r ∧
        D = (splitTorusHom h R ε μ hμ).range ∧
        IsElemAbelian r D ∧ Nat.card D = r ^ R ∧
        D ≤ Subgroup.normalizer (hypUnitriangular h R ε : Set (hypSU h R ε)) := by
  have hdvdq : r ∣ Nat.card L - 1 := by
    rw [h.card, show 2 * f = f * 2 by ring, pow_mul]
    have hsq : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      rw [mul_comm, ← Nat.sq_sub_sq (2 ^ f) 1, one_pow]
    rw [hsq]
    exact dvd_mul_of_dvd_left hrd _
  obtain ⟨ζ, hζ⟩ := CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq (L := L) hdvdq
  let μ : Subgroup Lˣ := Subgroup.zpowers ζ
  have hcardμ : Nat.card μ = r := by
    rw [show μ = Subgroup.zpowers ζ from rfl, Nat.card_zpowers, hζ]
  have hoddμ : Odd (Nat.card μ) := by
    rw [hcardμ]
    exact hr.odd_of_ne_two hr2
  have hsplit : SplitInv h μ := by
    rw [show μ = Subgroup.zpowers ζ from rfl]
    exact splitInv_zpowers h (d := r) hr.one_lt
      (by rw [← hζ]; exact pow_orderOf_eq_one ζ) hrd
  let D : Subgroup (hypSU h R ε) := (splitTorusHom h R ε μ hsplit).range
  refine ⟨μ, hsplit, D, hoddμ, hcardμ, rfl, ?_, ?_, ?_⟩
  · exact splitTorusHom_range_isElemAbelian hsplit fun a => by
      rw [← hcardμ]
      exact pow_card_eq_one'
  · rw [show D = (splitTorusHom h R ε μ hsplit).range from rfl, splitTorusHom_range_card,
      hcardμ]
  · intro x hx
    obtain ⟨a, rfl⟩ := hx
    rw [(CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_Sylow_normalizers h hR hε).1]
    exact hypTorus_le_hypBorel h (splitTorusHom_mem_hypTorus hsplit a)

theorem k_CartanRankLarge_psu :
    ∀ (K : Type) [Group K] [Finite K] (m f : ℕ),
      CFSG.Open.StatedLieAdmissible .PSU m 2 f → 2 < 2 ^ f →
      LieModel (K ⧸ Subgroup.center K) .PSU m 2 f →
      CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
      ∀ S : Subgroup K, IsSylowTwoOf S ⊤ →
        4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank .PSU m →
          ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 ∧
            3 < CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S)) := by
  intro K _ _ m f hadm hfbig hL hqs _ S hS hrank
  have hf2 : 2 ≤ f := by
    by_contra hf
    interval_cases f <;> norm_num at hfbig
  set ε := m % 2 with hεdef
  set R := m / 2 with hRdef
  have hε1 : ε ≤ 1 := by
    rw [hεdef]
    exact Nat.le_of_lt_succ (Nat.mod_lt m (by norm_num))
  have hmR : 2 * R + ε = m := by
    have h := Nat.div_add_mod m 2
    rw [hRdef, hεdef]
    omega
  have hR4 : 4 ≤ R := by
    have h := hrank
    rw [show CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank .PSU m = m / 2
      from rfl] at h
    simpa [hRdef] using h
  have hm3 : 3 ≤ 2 * R + ε := by omega
  obtain ⟨r, hr, hr2, -, hrd⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_odd_prime_dvd_two_pow_sub_one_ne_five hf2
  obtain ⟨L, hFld, hFin, h, ⟨e⟩⟩ :=
    uc22pwliu_exists_hypPSU (Y := K ⧸ Subgroup.center K) (n := f) (r := R) (ε := ε)
      (by omega) (by omega) (by simpa [hmR] using hL)
  letI : Field L := hFld
  letI : Finite L := hFin
  haveI : CharP L 2 := h.charP
  obtain ⟨α, hα, hker, -⟩ :=
    uc22pwliu_exists_cover (K := L) h (r := R) (ε := ε) hε1 hm3 hf2 hqs e
  obtain ⟨μ, hsplit, D, hoddμ, hcardμ, hDdef, hDEA, hDcard, hDU⟩ :=
    exists_splitTorus_data (R := R) (ε := ε) h hr hr2 hrd (by omega) hε1
  have hSylowAU := isSylowTwoOf_map_hypUnitriangular (L := L) h α hα hker
    (by omega) hε1
  have hmap_le : D.map α ≤ Subgroup.normalizer
      ((hypUnitriangular h R ε).map α : Set K) :=
    (Subgroup.map_mono (f := α) hDU).trans
      (Subgroup.le_normalizer_map (H := hypUnitriangular h R ε) α)
  have hDEAmap : IsElemAbelian r (D.map α) := CFSG.SectionRank.isElemAbelian_map hDEA α
  have hDmapcard : Nat.card (D.map α) = r ^ R := by
    rw [hDdef]
    change Nat.card ((splitTorusHom h R ε μ hsplit).range.map α) = r ^ R
    rw [splitTorusHom_range_map_card (r := R) (ε := ε) hsplit hoddμ α hker, hcardμ]
  have hbridge := le_pRank_normalizerQuotient_of_le_normalizer (K := K) hr hr2
    hSylowAU.2.1 hmap_le hDEAmap hDmapcard
  obtain ⟨eQ⟩ := normalizerQuotient_equiv_of_isSylowTwoOf (Y := K) (Y' := K)
    (MulEquiv.refl K) hS hSylowAU
  have hprank : CFSG.Open.pRank r
        (⊤ : Subgroup (normalizerQuotient ((hypUnitriangular h R ε).map α))) =
      CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv
      (G := normalizerQuotient ((hypUnitriangular h R ε).map α))
      (G' := normalizerQuotient S) hr.one_lt eQ.symm
  refine ⟨r, hr, hr2, hrd, ?_⟩
  rw [← hprank]
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

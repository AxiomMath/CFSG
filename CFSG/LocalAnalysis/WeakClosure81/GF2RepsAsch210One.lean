module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch210Pi
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch210Elem
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Three
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch210

open Subgroup
open scoped MatrixGroups

variable {ι : Type} [Fintype ι] [DecidableEq ι] {B : ι → Type} [∀ i, Group (B i)]
  [∀ i, Finite (B i)]

omit [Fintype ι] in
theorem SimpleFactors.exists_threeElem_at (hB : SimpleFactors B) {Y : Type} [Group Y] [Finite Y]
    (θ : Y →* ∀ i, B i) {F : Finset ι} {R : Subgroup Y} (hRF : R.map θ = prodSub B F)
    {i : ι} (hi : i ∈ F) :
    ∃ y ∈ R, (∃ k : ℕ, y ^ 3 ^ k = 1) ∧ orderOf (θ y) = 3 ∧ ∀ l, l ≠ i → θ y l = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 3 (hB.three_dvd i)
  have hx3 : orderOf (Pi.mulSingle i b) = 3 :=
    (orderOf_injective (MonoidHom.mulSingle B i) (Pi.mulSingle_injective i) b).trans hb
  have hxmem : Pi.mulSingle i b ∈ prodSub B F := by
    intro l hl
    exact Pi.mulSingle_eq_of_ne (fun hli => hl (by rw [hli]; exact hi)) b
  have hxmap : Pi.mulSingle i b ∈ R.map θ := by
    rw [hRF]
    exact hxmem
  obtain ⟨y, hyR, hy3, hyθ⟩ := exists_threeElem_lift θ hxmap hx3
  exact ⟨y, hyR, hy3, by rw [hyθ, hx3], fun l hl => by
    rw [hyθ]
    exact Pi.mulSingle_eq_of_ne hl b⟩

omit [Fintype ι] in
theorem SimpleFactors.false_of_centralizer_le (hB : SimpleFactors B)
    {Y : Type} [Group Y] [Finite Y] (θ : Y →* ∀ i, B i) (hQ : IsPGroup 3 θ.ker)
    (hY : CFSG.pRank 3 Y ≤ 3) {F : Finset ι} (h2 : 2 ≤ F.card) {R : Subgroup Y}
    (hR : Group.IsPerfect ↥R) (hRF : R.map θ = prodSub B F)
    (hC : ∀ r ∈ R, (∀ q ∈ R ⊓ θ.ker, r * q = q * r) → r ∈ θ.ker) : False := by
  classical
  let θR : ↥R →* ∀ i, B i := θ.domRestrict R
  have hθR : θR = θ.domRestrict R := rfl
  have hRrange : θR.range = prodSub B F := by
    rw [hθR, MonoidHom.domRestrict_range, hRF]
  have hker_iff : ∀ x : ↥R, x ∈ θR.ker ↔ (x : Y) ∈ θ.ker := by
    intro x
    simp only [MonoidHom.mem_ker, hθR, MonoidHom.domRestrict_apply]
  have hker_eq : θR.ker = θ.ker.comap R.subtype := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, hθR, MonoidHom.domRestrict_apply]
    rfl
  have hQR : IsPGroup 3 ↥θR.ker := by
    have h := hQ.comap_of_injective R.subtype R.subtype_injective
    rw [← hker_eq] at h
    exact h
  have hker_le : θR.ker ≤ pCore 3 ↥R :=
    le_sSup ⟨MonoidHom.normal_ker θR, hQR⟩
  have hpCore_le : pCore 3 ↥R ≤ θR.ker := by
    have hNF : (pCore 3 ↥R).map θR ≤ prodSub B F := by
      calc (pCore 3 ↥R).map θR ≤ (⊤ : Subgroup ↥R).map θR := Subgroup.map_mono le_top
        _ = θR.range := Subgroup.map_top θR
        _ = prodSub B F := hRrange
    have hNnorm : ∀ s ∈ prodSub B F, ∀ n ∈ (pCore 3 ↥R).map θR,
        s * n * s⁻¹ ∈ (pCore 3 ↥R).map θR := by
      intro s hs n hn
      rw [← hRrange] at hs
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hs
      obtain ⟨m, hmP, hm⟩ := Subgroup.mem_map.mp hn
      rw [← hy, ← hm]
      have hconj : y * m * y⁻¹ ∈ pCore 3 ↥R :=
        (pCore_normal (p := 3) (G := ↥R)).conj_mem m hmP y
      rw [show θR y * θR m * (θR y)⁻¹ = θR (y * m * y⁻¹) by simp]
      exact Subgroup.mem_map_of_mem θR hconj
    have h3N : IsPGroup 3 ↥((pCore 3 ↥R).map θR) :=
      (pCore_isPGroup (p := 3) (G := ↥R)).map θR
    have hNbot := SimpleFactors.eq_bot_of_pGroup hB hNF hNnorm h3N
    rwa [Subgroup.map_eq_bot_iff] at hNbot
  have hpCore_eq : pCore 3 ↥R = θR.ker := le_antisymm hpCore_le hker_le
  have hC' : Subgroup.centralizer (pCore 3 ↥R : Set ↥R) ≤ pCore 3 ↥R := by
    intro x hx
    rw [hpCore_eq]
    apply (hker_iff x).mpr
    refine hC (x : Y) x.2 ?_
    intro q hq
    have hqR : (⟨q, hq.1⟩ : ↥R) ∈ θR.ker := (hker_iff ⟨q, hq.1⟩).mpr hq.2
    have hqP : (⟨q, hq.1⟩ : ↥R) ∈ pCore 3 ↥R := by rw [hpCore_eq]; exact hqR
    exact congrArg (fun z : ↥R => (z : Y))
      ((Subgroup.mem_centralizer_iff.mp hx) (⟨q, hq.1⟩ : ↥R) hqP).symm
  have hne_top : pCore 3 ↥R ≠ ⊤ := by
    intro htop
    have hkertop : θR.ker = ⊤ := by rw [← hpCore_eq]; exact htop
    have hrange_bot : θR.range = ⊥ := by
      rw [eq_bot_iff]
      rintro z ⟨y, rfl⟩
      rw [Subgroup.mem_bot]
      exact MonoidHom.mem_ker.mp (hkertop.symm ▸ Subgroup.mem_top y)
    have hbot : prodSub B F = ⊥ := by rw [← hRrange]; exact hrange_bot
    obtain ⟨i, hiF, j, hjF, -⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
    obtain ⟨a, b, hab⟩ := hB.nonab i
    have ha1 : a ≠ 1 := fun ha => hab (by rw [ha, one_mul, mul_one])
    have hmem : Pi.mulSingle i a ∈ prodSub B F := by
      intro l hl
      exact Pi.mulSingle_eq_of_ne (fun hli => hl (by rw [hli]; exact hiF)) a
    have hone : Pi.mulSingle i a = 1 := by
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact ha1 (by simpa using congrFun hone i)
  have hr3 : CFSG.pRank 3 ↥R ≤ 3 := by
    have h1 : CFSG.pRank 3 ↥R ≤ CFSG.pRank 3 Y := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥R,
        CFSG.SectionRank.pRank_eq_open_pRank_top 3 Y]
      exact CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num) R.subtype
        R.subtype_injective
    exact h1.trans hY
  have hcases : Nonempty (↥R ⧸ pCore 3 ↥R ≃* SL(3, ZMod 3)) ∨
      Nonempty (↥R ⧸ pCore 3 ↥R ≃* SL(2, ZMod 5)) :=
    CFSG.RankThree.PartTwo.Sec4.Census.primeThreeLinear (Y := ↥R) hR hC' hr3 hne_top
  have e : ↥R ⧸ pCore 3 ↥R ≃* ↥(prodSub B F) :=
    (QuotientGroup.quotientMulEquivOfEq hpCore_eq).trans
      ((QuotientGroup.quotientKerEquivRange θR).trans (MulEquiv.subgroupCongr hRrange))
  obtain ⟨N, hNnormal, hNne, hNnotcen⟩ := SimpleFactors.exists_normal_not_top_not_central hB h2
  rcases hcases with hcase | hcase
  · obtain ⟨e3⟩ := hcase
    have hq : CFSG.IsQuasisimple ↥(prodSub B F) :=
      CFSG.IsQuasisimple.of_mulEquiv (e.symm.trans e3)
        CFSG.RankThree.PartTwo.Sec4.Census.isQuasisimple_SL3_three
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNnormal with h | h
    · exact hNne h
    · exact hNnotcen h
  · obtain ⟨e2⟩ := hcase
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hq : CFSG.IsQuasisimple ↥(prodSub B F) :=
      CFSG.IsQuasisimple.of_mulEquiv (e.symm.trans e2)
        (CFSG.RankThree.PartTwo.Sec4.Census.isQuasisimple_SL2 (p := 5) le_rfl)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNnormal with h | h
    · exact hNne h
    · exact hNnotcen h

end CFSG.LocalAnalysis.WeakClosure81.Asch210

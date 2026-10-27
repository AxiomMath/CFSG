module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.Quasithin.Background.F8Basic
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251c
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Shape
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.RankThree.PartOne.S11d.OutCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R8107E3

open CFSG.Open Subgroup

variable {G : Type} [Group G]

@[expose] def CubesInner (S L : Subgroup G) : Prop :=
  ∀ s (hs : s ∈ normalizer (L : Set G)), s ∈ S → s ^ 3 = 1 →
    CFSG.RankThree.PartTwo.KFacts.IsInnerAut (UC6S846.rhoL L ⟨s, hs⟩)

theorem exists_not_isInnerAut_of_not_cubesInner {S L : Subgroup G}
    (hS : S ≤ normalizer (L : Set G)) (h : ¬ CubesInner S L) :
    ∃ a₀, ∃ ha₀ : a₀ ∈ S, a₀ ^ 3 = 1 ∧
      ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut (UC6S846.rhoL L ⟨a₀, hS ha₀⟩) := by
  by_contra hne
  refine h fun s hs hsS hs3 => ?_
  by_contra hin
  exact hne ⟨s, hsS, hs3, hin⟩

variable [Finite G]

theorem exists_inv_mul_mem_centralizerMod {M L R : Subgroup G} (hLM : L ≤ M)
    (hZ : center (Bar2 L) = ⊥) (hR : CFSG.ABGLocalTools.IsSylowOf 3 R M)
    (hRN : R ≤ normalizer (L : Set G)) {r : G} (hr : r ∈ R)
    (hin : CFSG.RankThree.PartTwo.KFacts.IsInnerAut (UC6S846.rhoL L ⟨r, hRN hr⟩)) :
    ∃ r₁ ∈ R ⊓ L,
      r₁⁻¹ * r ∈ CFSG.Quasithin.centralizerMod (pCoreOf 2 L) (normalizer (L : Set G)) L := by
  obtain ⟨S, hS⟩ := (hR.of_le le_sup_left (sup_le hR.le hLM)).inf_of_le_normalizer le_sup_right
    (sup_le hRN le_normalizer)
  have hSmem : ∀ u : ↥L, u ∈ (S : Subgroup L) ↔ (u : G) ∈ R ⊓ L := fun u => by
    rw [← hS]
    exact ⟨fun h => mem_map_of_mem _ h, fun ⟨v, hv, hvu⟩ => Subtype.ext hvu ▸ hv⟩
  let Sb : Sylow 3 (Bar2 L) := S.mapSurjective (QuotientGroup.mk'_surjective _)
  obtain ⟨k, hk⟩ := hR.isPGroup ⟨r, hr⟩
  have hr3 : r ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hθ : UC6S846.rhoL L ⟨r, hRN hr⟩ ^ 3 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨r, hRN hr⟩ : ↥(normalizer (L : Set G))) ^ 3 ^ k = 1 := Subtype.ext (by simp [hr3])
    rw [this, map_one]
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hin
  have hx3 : x ^ 3 ^ k = 1 := by
    have h1 : MulAut.conj (x ^ 3 ^ k) = 1 := by rw [map_pow, hx, hθ]
    have hc : x ^ 3 ^ k ∈ center (Bar2 L) := mem_center_iff.2 fun y => by
      have h2 := congrArg (fun φ : MulAut (Bar2 L) => φ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc y * x ^ 3 ^ k = x ^ 3 ^ k * y * (x ^ 3 ^ k)⁻¹ * x ^ 3 ^ k := by rw [h2]
        _ = x ^ 3 ^ k * y := by group
    rw [hZ] at hc
    exact mem_bot.1 hc
  have hSb : ∀ y ∈ (Sb : Subgroup (Bar2 L)), x * y * x⁻¹ ∈ (Sb : Subgroup (Bar2 L)) := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 : x * QuotientGroup.mk' _ t * x⁻¹ =
        UC6S846.rhoL L ⟨r, hRN hr⟩ (QuotientGroup.mk t) := by
      rw [← hx]; rfl
    rw [h1]
    refine ⟨Subgroup.normalizerMonoidHom L ⟨r, hRN hr⟩ t, ?_, (UC6S846.rhoL_mk L _ t).symm⟩
    have htRL := (hSmem t).1 ht
    refine (hSmem _).2 ?_
    rw [UC6S846.rhoL_mk_coe]
    exact mem_inf.2 ⟨mul_mem (mul_mem hr (mem_inf.1 htRL).1) (inv_mem hr),
      (mem_normalizer_iff.1 (hRN hr) _).1 (mem_inf.1 htRL).2⟩
  have hxN : x ∈ normalizer ((Sb : Subgroup (Bar2 L)) : Set (Bar2 L)) := by
    refine mem_normalizer_iff_map_conj_eq.2
      (Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj x).injective]))
    rintro _ ⟨y, hy, rfl⟩
    exact hSb y hy
  have hxS : x ∈ (Sb : Subgroup (Bar2 L)) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hx3)
    exact ((IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])).inf_normalizer_sylow Sb).le
      ⟨mem_zpowers x, hxN⟩ |>.2
  obtain ⟨s, hsS, hsx⟩ := hxS
  have hmN : (s : G)⁻¹ * r ∈ normalizer (L : Set G) :=
    mul_mem (inv_mem (le_normalizer s.2)) (hRN hr)
  have hρ : UC6S846.rhoL L ⟨(s : G)⁻¹ * r, hmN⟩ = 1 := by
    have he : (⟨(s : G)⁻¹ * r, hmN⟩ : ↥(normalizer (L : Set G))) =
        (⟨(s : G), le_normalizer s.2⟩ : ↥(normalizer (L : Set G)))⁻¹ * ⟨r, hRN hr⟩ := rfl
    rw [he, map_mul, map_inv, UC6S846.rhoL_inner L (s : G) s.2, ← hx, ← hsx]
    exact inv_mul_cancel _
  refine ⟨s, (hSmem s).1 hsS, hmN, UC6S846.normalizer_le_normalizer_pCoreOf L hmN, fun u hu => ?_⟩
  exact (UC6S846.rhoL_fix_iff L ⟨_, hmN⟩ ⟨u, hu⟩).1 (by rw [hρ]; rfl)

private theorem eq_one_of_mem_of_mem_pCoreOf {R L : Subgroup G} (hR : IsPGroup 3 R) {x : G}
    (hxR : x ∈ R) (hxO : x ∈ pCoreOf 2 L) : x = 1 :=
  Subgroup.disjoint_def.1 (IsPGroup.disjoint_of_ne 3 2 (by norm_num) R (pCoreOf 2 L) hR
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)) hxR hxO

private theorem commute_of_mem_centralizerMod {R L : Subgroup G} (hR : IsPGroup 3 R) {c x : G}
    (hcR : c ∈ R) (hxR : x ∈ R)
    (hc : c ∈ CFSG.Quasithin.centralizerMod (pCoreOf 2 L) (normalizer (L : Set G)) L)
    (hxL : x ∈ L) : Commute c x := by
  have h1 := eq_one_of_mem_of_mem_pCoreOf hR
    (mul_mem (mul_mem (mul_mem hcR hxR) (inv_mem hcR)) (inv_mem hxR)) (hc.2.2 x hxL)
  calc c * x = c * x * c⁻¹ * x⁻¹ * (x * c) := by group
    _ = x * c := by rw [h1, one_mul]

private theorem exists_pow_eq_of_mem_isCyclic {C : Subgroup G} (hC : IsCyclic C) {a c : G}
    (haC : a ∈ C) (hcC : c ∈ C) (ha : orderOf a = 3) (hc : c ^ 3 = 1) : ∃ i : ℕ, c = a ^ i := by
  by_cases hc1 : c = 1
  · exact ⟨0, by rw [hc1, pow_zero]⟩
  haveI := hC
  have hz : zpowers (⟨c, hcC⟩ : C) = zpowers ⟨a, haC⟩ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk,
      Subgroup.orderOf_mk, orderOf_eq_prime hc hc1, ha]
  obtain ⟨i, hi⟩ := mem_powers_iff_mem_zpowers.2 (hz ▸ mem_zpowers (⟨c, hcC⟩ : C))
  exact ⟨i, by simpa using (congrArg Subtype.val hi).symm⟩

theorem omega_of_cubesInner {M L₁ L₂ R : Subgroup G} (hL₁ : L₁ ∈ calC M)
    (hL₂ : L₂ ∈ calC M) (h12 : L₁ ≠ L₂) (r₁ : CFSG.Open.pRank 3 L₁ = 1)
    (r₂ : CFSG.Open.pRank 3 L₂ = 1) (hZ₁ : center (Bar2 L₁) = ⊥) (hZ₂ : center (Bar2 L₂) = ⊥)
    (hM3 : CFSG.Open.pRank 3 M ≤ 3) (hR : CFSG.ABGLocalTools.IsSylowOf 3 R M)
    (hRN₁ : R ≤ normalizer (L₁ : Set G)) (hRN₂ : R ≤ normalizer (L₂ : Set G))
    (hI₁ : CubesInner R L₁) (hI₂ : CubesInner R L₂) {a₁ a₂ : G} (ha₁ : a₁ ∈ L₁ ⊓ R)
    (ha₂ : a₂ ∈ L₂ ⊓ R) (ho₁ : orderOf a₁ = 3) (ho₂ : orderOf a₂ = 3) :
    a₁ * a₂ = a₂ * a₁ ∧ ∃ a₀ ∈ R, a₀ ^ 3 = 1 ∧ a₀ * a₁ = a₁ * a₀ ∧ a₀ * a₂ = a₂ * a₀ ∧
      a₀ ∈ CFSG.Quasithin.centralizerMod (pCoreOf 2 L₁) (normalizer (L₁ : Set G)) L₁ ∧
      a₀ ∈ CFSG.Quasithin.centralizerMod (pCoreOf 2 L₂) (normalizer (L₂ : Set G)) L₂ ∧
      (∀ c ∈ R, c ∈ CFSG.Quasithin.centralizerMod (pCoreOf 2 L₁) (normalizer (L₁ : Set G)) L₁ →
        c ∈ CFSG.Quasithin.centralizerMod (pCoreOf 2 L₂) (normalizer (L₂ : Set G)) L₂ →
          c ^ 3 = 1 → ∃ i : ℕ, c = a₀ ^ i) ∧
      ∀ x ∈ R, x ^ 3 = 1 → ∃ i j k : ℕ, x = a₀ ^ i * a₁ ^ j * a₂ ^ k := by
  set C₁ := CFSG.Quasithin.centralizerMod (pCoreOf 2 L₁) (normalizer (L₁ : Set G)) L₁
  set C₂ := CFSG.Quasithin.centralizerMod (pCoreOf 2 L₂) (normalizer (L₂ : Set G)) L₂
  have hR3 := hR.isPGroup
  have hL₂C₁ : L₂ ≤ C₁ := P2251c.le_centralizerMod_of_ne hL₁ hL₂ h12
  have hL₁C₂ : L₁ ≤ C₂ := P2251c.le_centralizerMod_of_ne hL₂ hL₁ h12.symm
  have hone₁ : ∀ {x : G}, x ∈ R → x ∈ L₁ → x ∈ C₁ → x = 1 := fun hxR hxL hxC =>
    eq_one_of_mem_of_mem_pCoreOf hR3 hxR (P2251c.mem_pCoreOf_of_mem_centralizerMod hZ₁ hxL hxC)
  have hone₂ : ∀ {x : G}, x ∈ R → x ∈ L₂ → x ∈ C₂ → x = 1 := fun hxR hxL hxC =>
    eq_one_of_mem_of_mem_pCoreOf hR3 hxR (P2251c.mem_pCoreOf_of_mem_centralizerMod hZ₂ hxL hxC)
  have hdec : ∀ x ∈ R, x ^ 3 = 1 → ∃ s₁ ∈ R ⊓ L₁, ∃ s₂ ∈ R ⊓ L₂, ∃ c ∈ R, c ∈ C₁ ∧ c ∈ C₂ ∧
      x = s₁ * s₂ * c := fun x hx hx3 => by
    obtain ⟨s₁, hs₁, hc₁⟩ :=
      exists_inv_mul_mem_centralizerMod hL₁.1.le hZ₁ hR hRN₁ hx (hI₁ x (hRN₁ hx) hx hx3)
    obtain ⟨s₂, hs₂, hc₂⟩ :=
      exists_inv_mul_mem_centralizerMod hL₂.1.le hZ₂ hR hRN₂ hx (hI₂ x (hRN₂ hx) hx hx3)
    have h21 := (commute_of_mem_centralizerMod hR3 hs₂.1 hs₁.1 (hL₂C₁ hs₂.2) hs₁.2).eq
    refine ⟨s₁, hs₁, s₂, hs₂, s₂⁻¹ * (s₁⁻¹ * x), mul_mem (inv_mem hs₂.1)
      (mul_mem (inv_mem hs₁.1) hx), mul_mem (inv_mem (hL₂C₁ hs₂.2)) hc₁, ?_, by group⟩
    rw [← mul_assoc, ← mul_inv_rev, ← h21, mul_inv_rev, mul_assoc]
    exact mul_mem (inv_mem (hL₁C₂ hs₁.2)) hc₂
  have hR₁c : IsCyclic ↥(R ⊓ L₁) :=
    R8107Shape.isCyclic_of_isPGroup_of_pRank_eq_one r₁ inf_le_right (hR3.to_le inf_le_left)
  have hR₂c : IsCyclic ↥(R ⊓ L₂) :=
    R8107Shape.isCyclic_of_isPGroup_of_pRank_eq_one r₂ inf_le_right (hR3.to_le inf_le_left)
  set C := R ⊓ C₁ ⊓ C₂ with hCdef
  have hCR : C ≤ R := inf_le_left.trans inf_le_left
  have hCrk : CFSG.Open.pRank 3 C ≤ 1 := by
    by_contra h
    obtain ⟨B, hBC, hB, hBc⟩ :=
      UC6S846.exists_elemAbelian_card_of_le_pRank Nat.prime_three
        (show 2 ≤ CFSG.Open.pRank 3 C by omega)
    have hBR : B ≤ R := hBC.trans hCR
    have hBC₂ : B ≤ C₂ := hBC.trans inf_le_right
    obtain ⟨hB₂, hB₂c⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hB ho₂
      (fun e he => commute_of_mem_centralizerMod hR3 (hBR he) ha₂.2 (hBC₂ he) ha₂.1)
      fun h => P2251c.not_mem_of_orderOf_eq_three (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₂)
        ho₂ (P2251c.mem_pCoreOf_of_mem_centralizerMod hZ₂ ha₂.1 (hBC₂ h))
    have hB₂C₁ : B ⊔ zpowers a₂ ≤ C₁ :=
      sup_le (hBC.trans (inf_le_left.trans inf_le_right)) (zpowers_le.2 (hL₂C₁ ha₂.1))
    have hB₂R : B ⊔ zpowers a₂ ≤ R := sup_le hBR (zpowers_le.2 ha₂.2)
    obtain ⟨hB₁, hB₁c⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hB₂ ho₁
      (fun e he => commute_of_mem_centralizerMod hR3 (hB₂R he) ha₁.2 (hB₂C₁ he) ha₁.1)
      fun h => P2251c.not_mem_of_orderOf_eq_three (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁)
        ho₁ (P2251c.mem_pCoreOf_of_mem_centralizerMod hZ₁ ha₁.1 (hB₂C₁ h))
    have h4 := UC6S846.le_pRank' Nat.prime_three
      (sup_le (hB₂R.trans hR.le) (zpowers_le.2 (hR.le ha₁.2))) hB₁ (k := 4)
      (by rw [hB₁c, hB₂c, hBc]; norm_num)
    omega
  have hCc : IsCyclic C :=
    CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num) le_rfl
      (hR3.to_le hCR) (((CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥C).trans
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) C).symm).trans_le hCrk)
  obtain ⟨a₀, ha₀C, ha₀3, ha₀⟩ :
      ∃ a₀ ∈ C, a₀ ^ 3 = 1 ∧ ∀ c ∈ C, c ^ 3 = 1 → ∃ i : ℕ, c = a₀ ^ i := by
    by_cases hex : ∃ c ∈ C, orderOf c = 3
    · obtain ⟨c₀, hc₀C, hc₀⟩ := hex
      exact ⟨c₀, hc₀C, by rw [← hc₀, pow_orderOf_eq_one], fun c hcC hc3 =>
        exists_pow_eq_of_mem_isCyclic hCc hc₀C hcC hc₀ hc3⟩
    · refine ⟨1, one_mem _, one_pow 3, fun c hcC hc3 => ⟨0, ?_⟩⟩
      rw [pow_zero]
      by_contra hc1
      exact hex ⟨c, hcC, orderOf_eq_prime hc3 hc1⟩
  have h₁₂ := commute_of_mem_centralizerMod hR3 ha₂.2 ha₁.2 (hL₂C₁ ha₂.1) ha₁.1
  have h₀₁ := commute_of_mem_centralizerMod hR3 (hCR ha₀C) ha₁.2 ha₀C.1.2 ha₁.1
  have h₀₂ := commute_of_mem_centralizerMod hR3 (hCR ha₀C) ha₂.2 ha₀C.2 ha₂.1
  refine ⟨h₁₂.eq.symm, a₀, hCR ha₀C, ha₀3, h₀₁.eq, h₀₂.eq, ha₀C.1.2, ha₀C.2,
    fun c hcR hc₁ hc₂ hc3 => ha₀ c ⟨⟨hcR, hc₁⟩, hc₂⟩ hc3, fun x hxR hx3 => ?_⟩
  obtain ⟨s₁, hs₁, s₂, hs₂, c, hcR, hc₁, hc₂, rfl⟩ := hdec x hxR hx3
  have k₁₂ := (commute_of_mem_centralizerMod hR3 hs₂.1 hs₁.1 (hL₂C₁ hs₂.2) hs₁.2).symm
  have k₁c := (commute_of_mem_centralizerMod hR3 hcR hs₁.1 hc₁ hs₁.2).symm
  have k₂c := (commute_of_mem_centralizerMod hR3 hcR hs₂.1 hc₂ hs₂.2).symm
  have hx3' : s₁ ^ 3 * (s₂ ^ 3 * c ^ 3) = 1 := by
    rw [← mul_assoc, ← k₁₂.mul_pow, ← (k₁c.mul_left k₂c).mul_pow]
    exact hx3
  have h1 : s₁ ^ 3 = 1 := hone₁ (pow_mem hs₁.1 3) (pow_mem hs₁.2 3) (by
    rw [eq_inv_of_mul_eq_one_left hx3']
    exact inv_mem (mul_mem (pow_mem (hL₂C₁ hs₂.2) 3) (pow_mem hc₁ 3)))
  rw [h1, one_mul] at hx3'
  have h2 : s₂ ^ 3 = 1 := hone₂ (pow_mem hs₂.1 3) (pow_mem hs₂.2 3) (by
    rw [eq_inv_of_mul_eq_one_left hx3']
    exact inv_mem (pow_mem hc₂ 3))
  rw [h2, one_mul] at hx3'
  obtain ⟨j, rfl⟩ := exists_pow_eq_of_mem_isCyclic hR₁c ⟨ha₁.2, ha₁.1⟩ hs₁ ho₁ h1
  obtain ⟨k, rfl⟩ := exists_pow_eq_of_mem_isCyclic hR₂c ⟨ha₂.2, ha₂.1⟩ hs₂ ho₂ h2
  obtain ⟨i, rfl⟩ := ha₀ c ⟨⟨hcR, hc₁⟩, hc₂⟩ hx3'
  refine ⟨i, j, k, ?_⟩
  rw [((h₀₁.pow_pow i j).mul_right (h₀₂.pow_pow i k)).symm.eq, mul_assoc]

end CFSG.LocalAnalysis.UniquenessCase.UC22.R8107E3

end

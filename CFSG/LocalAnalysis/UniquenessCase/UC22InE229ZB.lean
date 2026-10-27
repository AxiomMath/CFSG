module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229G898
public import CFSG.LocalAnalysis.UniquenessCase.UCKU3b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_normalizer_le_of_mem_sig {D : Data G} (hSg : UC6S846.SigmaStd D)
    {Y : Subgroup G} (hY : Y ∈ calC D.M) {q : ℕ} (hq : q ∈ D.sig) {X : Subgroup G}
    (hXY : X ≤ Y) (hX : X ≠ ⊥) (hXq : IsPGroup q X) : normalizer (X : Set G) ≤ D.M := by
  haveI : Fact q.Prime := ⟨(D.sig_prime q hq).1⟩
  exact (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) hq).normalizer_le hX hXq
    (hXY.trans hY.1.le)

theorem uc22ine229_pRank_le_three {D : Data G} (hSg : UC6S846.SigmaStd D) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hqs : q ∉ D.sig) : CFSG.Open.pRank q D.M ≤ 3 := by
  by_contra h
  exact hqs (hSg.four_mem q hq hq2 (by omega))

theorem uc22ine229_pCoreOf_le_of_isSubnormal {K L : Subgroup G} (h : IsSubnormal K L) :
    pCoreOf 2 K ≤ pCoreOf 2 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction h with
  | refl A => exact le_rfl
  | @step A B C hAB hn _ ih =>
    refine le_trans ?_ ih
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 A).trans hAB) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A)
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hAB).mp hn).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A)

private theorem conj_mem_pCoreOf {M : Subgroup G} {x o : G} (hx : x ∈ M)
    (ho : o ∈ pCoreOf 2 M) : x * o * x⁻¹ ∈ pCoreOf 2 M :=
  (Subgroup.mem_normalizer_iff.1
    ((Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf M)) hx) o).1 ho

private def centMO2 (M Y : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ M ∧ ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 M}
  mul_mem' := by
    rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
    refine ⟨M.mul_mem haM hbM, fun y hy => ?_⟩
    have h1 : a * b * y * (a * b)⁻¹ * y⁻¹ =
        a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ * (a * y * a⁻¹ * y⁻¹) := by group
    rw [h1]
    exact (pCoreOf 2 M).mul_mem (conj_mem_pCoreOf haM (hb y hy)) (ha y hy)
  one_mem' := ⟨M.one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro a ⟨haM, ha⟩
    refine ⟨M.inv_mem haM, fun y hy => ?_⟩
    have h1 : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [h1]
    exact conj_mem_pCoreOf (M.inv_mem haM) (inv_mem (ha y hy))

theorem uc22ine229_le_normalizer {M Y : Subgroup G} (hY : Y ∈ calC M) {p q : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hq : q.Prime) (hq2 : q ≠ 2) {X : Subgroup G} (hXY : X ≤ Y)
    (hXc : Nat.card X = q) (hZ : ¬ q ∣ Nat.card (center (Bar2 Y)))
    (hrank : CFSG.Open.pRank q M ≤ 3) {B : Subgroup G} (hBM : B ≤ M) (hBel : IsElemAbelian p B) :
    B ≤ normalizer (Y : Set G) := by
  intro y hy
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  haveI : Fact p.Prime := ⟨hp⟩
  exact uc22ine229_normalizes_of_pRank_le_three hY (hBM hy) hp hp5
    (orderOf_eq_prime (hBel.2 y hy) hy1) hq hq2 hXY hXc hZ hrank

theorem uc22ine229_exists_kernel {M Y : Subgroup G} (hY : IsSubnormal Y M) {p : ℕ} (hp : p.Prime)
    {B : Subgroup G} (hBN : B ≤ normalizer (Y : Set G)) (hBel : IsElemAbelian p B)
    (hBc : Nat.card B = p ^ 4)
    (hR : Nat.card ((B.subgroupOf (normalizer (Y : Set G))).map (UC6S846.rhoL Y)) ≤ p ^ 2) :
    ∃ B₀ : Subgroup G, B₀ ≤ B ∧ IsElemAbelian p B₀ ∧ Nat.card B₀ = p ^ 2 ∧
      ∀ b ∈ B₀, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  haveI : Fact p.Prime := ⟨hp⟩
  let BN : Subgroup ↥(normalizer (Y : Set G)) := B.subgroupOf (normalizer (Y : Set G))
  let φ : ↥BN →* MulAut (Bar2 Y) := (UC6S846.rhoL Y).comp BN.subtype
  have hφrange : φ.range = BN.map (UC6S846.rhoL Y) := by
    ext y
    simp only [φ, MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.comp_apply,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hBNcard : Nat.card BN = p ^ 4 := by
    rw [← hBc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
  have hker : p ^ 4 = Nat.card φ.range * Nat.card φ.ker := by
    rw [← hBNcard, Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  let K : Subgroup G := (φ.ker.map BN.subtype).map (normalizer (Y : Set G)).subtype
  have hKB : K ≤ B :=
    calc K ≤ BN.map (normalizer (Y : Set G)).subtype :=
          Subgroup.map_mono (Subgroup.map_subtype_le _)
      _ = B := Subgroup.map_subgroupOf_eq_of_le hBN
  have hKc : p ^ 2 ≤ Nat.card K := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    have h1 : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card φ.ker :=
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ = _ := hker
        _ ≤ p ^ 2 * Nat.card φ.ker := Nat.mul_le_mul_right _ (hφrange ▸ hR)
    exact Nat.le_of_mul_le_mul_left h1 (pow_pos hp.pos 2)
  obtain ⟨B₀, hB₀K, hB₀el, hB₀c⟩ := UC6S846.exists_card_p_sq hp (hBel.mono hKB) hKc
  refine ⟨B₀, hB₀K.trans hKB, hB₀el, hB₀c, fun b hb y hy => ?_⟩
  obtain ⟨_, ⟨k, hk, rfl⟩, rfl⟩ := hB₀K hb
  have h1 : UC6S846.rhoL Y (k : ↥(normalizer (Y : Set G))) = 1 := (MonoidHom.mem_ker).1 hk
  exact uc22ine229_pCoreOf_le_of_isSubnormal hY
    ((UC6S846.rhoL_fix_iff Y (k : ↥(normalizer (Y : Set G))) ⟨y, hy⟩).1
      (by rw [h1, MulAut.one_apply]))

open scoped commutatorElement in
theorem uc22ine229_commutator_mem_of_ne {M L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ calC M)
    (h₂ : L₂ ∈ calC M) (hne : L₁ ≠ L₂) {x y : G} (hx : x ∈ L₁) (hy : y ∈ L₂) :
    x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  obtain ⟨hs₁, hp₁, hq₁, -⟩ := UC6S846.calC_subgroupOf h₁
  obtain ⟨hs₂, hp₂, hq₂, -⟩ := UC6S846.calC_subgroupOf h₂
  let π : ↥M →* ↥M ⧸ CFSG.pCore 2 ↥M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hne' : (L₁.subgroupOf M).map π ≠ (L₂.subgroupOf M).map π := fun h => by
    have h' := congrArg (Subgroup.map M.subtype) (UC6S846.image_injective hs₁ hp₁ hs₂ hp₂ h)
    rw [Subgroup.map_subgroupOf_eq_of_le h₁.1.le, Subgroup.map_subgroupOf_eq_of_le h₂.1.le] at h'
    exact hne h'
  have hcomm := (CFSG.LocalCores.distinct_components_commute (UC6S846.isComponent_image hs₁ hq₁)
    (UC6S846.isComponent_image hs₂ hq₂)).resolve_left hne'
  have hxM : x ∈ M := h₁.1.le hx
  have hyM : y ∈ M := h₂.1.le hy
  have hmem : ⁅(⟨x, hxM⟩ : ↥M), (⟨y, hyM⟩ : ↥M)⁆ ∈ CFSG.pCore 2 ↥M := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥M), MonoidHom.mem_ker, map_commutatorElement]
    have h1 : ⁅π ⟨x, hxM⟩, π ⟨y, hyM⟩⁆ ∈ ⁅(L₁.subgroupOf M).map π, (L₂.subgroupOf M).map π⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx))
        (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hy))
    rw [hcomm] at h1
    exact h1
  exact ⟨_, hmem, rfl⟩

theorem uc22ine229_exists_elemAbelian_sq (hSyl : UCK.U3SylOmega) {Y : Subgroup G} {n : ℕ}
    (hX : IsSU3 (Bar2 Y) n) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpn : p ∣ 2 ^ n + 1) :
    ∃ E : Subgroup G, E ≤ Y ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S⟩ : Nonempty (Sylow p (Bar2 Y)) := inferInstance
  obtain ⟨Eb, -, hEbel, hEbc, -⟩ :=
    hSyl (Bar2 Y) n hX p hp hp3 hpn (S : Subgroup (Bar2 Y)) S.isPGroup' S.not_dvd_index
  let π : ↥Y →* Bar2 Y := QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  obtain ⟨Q, -, hQmap, hQdisj⟩ := UC6S846.exists_lift_pGroup π (QuotientGroup.mk'_surjective _)
    hker hp (by omega) Eb hEbel.isPGroup
  refine ⟨Q.map Y.subtype, Subgroup.map_subtype_le _,
    (UC6S846.isElemAbelian_of_disjoint_ker π Q hQdisj (by rw [hQmap]; exact hEbel)).map _, ?_⟩
  rw [Subgroup.card_map_of_injective Y.subtype_injective,
    ← UC6S846.card_map_of_disjoint_ker π Q hQdisj, hQmap, hEbc]

theorem uc22ine229_exists_conj_sq (hSyl : UCK.U3SylOmega) {M Y : Subgroup G} (hY : Y ∈ calC M)
    {n : ℕ} (hX : IsSU3 (Bar2 Y) n) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpn : p ∣ 2 ^ n + 1)
    (hnorm : ¬ M ≤ normalizer (Y : Set G)) :
    ∃ B₀ : Subgroup G, B₀ ≤ M ∧ IsElemAbelian p B₀ ∧ Nat.card B₀ = p ^ 2 ∧
      ∀ b ∈ B₀, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  obtain ⟨m, hmM, hmN⟩ := SetLike.not_le_iff_exists.1 hnorm
  obtain ⟨E, hEY, hEel, hEc⟩ := uc22ine229_exists_elemAbelian_sq hSyl hX hp hp3 hpn
  let f : MulAut G := MulAut.conj m
  have hM : M.map f.toMonoidHom = M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hmM)
  have hY' : Y.map f.toMonoidHom ∈ calC M := UC6S846.calC_map M f hM hY
  have hne : Y.map f.toMonoidHom ≠ Y := fun h => hmN (UC6S846.mem_normalizer_iff_map_conj.2 h)
  refine ⟨E.map f.toMonoidHom, (Subgroup.map_mono hEY).trans hY'.1.le, hEel.map _, ?_,
    fun b hb y hy => uc22ine229_commutator_mem_of_ne hY' hY hne (Subgroup.map_mono hEY hb) hy⟩
  rw [Subgroup.card_map_of_injective f.injective, hEc]

theorem uc22ine229_exists_copy {M Y : Subgroup G} (hYM : Y ≤ M) {p q : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2) {B₀ : Subgroup G} (hB₀M : B₀ ≤ M)
    (hB₀ : IsElemAbelian p B₀) (hB₀c : Nat.card B₀ = p ^ 2)
    (hB₀Y : ∀ b ∈ B₀, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M) {E : Subgroup G} (hEY : E ≤ Y)
    (hE : IsPGroup q E) :
    ∃ B₁ : Subgroup G, B₁ ≤ M ∧ IsElemAbelian p B₁ ∧ Nat.card B₁ = p ^ 2 ∧
      B₁ ≤ centralizer (E : Set G) ∧ ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  have hMN : M ≤ normalizer (pCoreOf 2 M : Set G) :=
    Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf M)
  obtain ⟨B₁, hB₁C, hB₁le, ⟨e⟩⟩ := UC6S846.exists_centralizing_copy hq hq2 hp hp2
    (pCoreOf 2 M) B₀ E (UC6S846.isPGroup_pCoreOf M) (hB₀M.trans hMN)
    ((hEY.trans hYM).trans hMN) hB₀.isPGroup hE (fun x hx b hb => by
      have h1 : x * b * x⁻¹ * b⁻¹ = (b * x * b⁻¹ * x⁻¹)⁻¹ := by group
      rw [h1]
      exact inv_mem (hB₀Y b hb x (hEY hx)))
  have hOle : pCoreOf 2 M ≤ centMO2 M Y := fun o ho =>
    ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 M ho, fun y hy => by
      have h1 : o * y * o⁻¹ * y⁻¹ = o * (y * o⁻¹ * y⁻¹) := by group
      rw [h1]
      exact (pCoreOf 2 M).mul_mem ho (conj_mem_pCoreOf (hYM hy) (inv_mem ho))⟩
  have hle : B₁ ≤ centMO2 M Y := hB₁le.trans (sup_le (fun b hb => ⟨hB₀M hb, hB₀Y b hb⟩) hOle)
  exact ⟨B₁, fun x hx => (hle hx).1, UC6S846.isElemAbelian_of_mulEquiv e hB₀,
    by rw [Nat.card_congr e.toEquiv, hB₀c], hB₁C, fun b hb => (hle hb).2⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

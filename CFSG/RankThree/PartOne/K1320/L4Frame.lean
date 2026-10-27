module

public import CFSG.RankThree.PartOne.KF.F132Row8Frame
public import CFSG.RankThree.PartOne.K1320.L4Blocks
public import CFSG.RankThree.PartOne.K1320.L4Weyl
public import CFSG.RankThree.PartOne.K1320.L4Transport
public import CFSG.RankThree.PartOne.K1320.L4Rank
public import CFSG.RankThree.PartOne.K1320.L4Psl2
public import CFSG.RankThree.PartOne.K1320.FrameGen
public import CFSG.RankThree.PartOne.K1320.Members
public import CFSG.RankThree.PartOne.S13K.Pair134

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL)


variable {G : Type} [Group G] [Finite G]

structure Row8Frame (p : ℕ) (A L E : Subgroup G) (f : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K 2] where
  hK : Nat.card K = 2 ^ f
  ε : ↥L →* StatedProj (StatedSL 4 K)
  central : IsCentralPQuot p ε
  hAT : ((A ⊓ L).subgroupOf L).map ε = (T8 p K).map (q8 K)
  r₀ : MulAut E
  r₁ : MulAut E
  r₀' : MulAut E
  mem₀ : r₀ ∈ reflectionSet p E
  mem₀L : r₀ ∈ torusImage E L
  mem₁ : r₁ ∈ reflectionSet p E
  mem₁L : r₁ ∈ torusImage E L
  mem₀' : r₀' ∈ reflectionSet p E
  mem₀'L : r₀' ∈ torusImage E L
  ord₀₁ : orderOf (r₀ * r₁) = 4
  kf₀ : KFAt p E f r₀
  kf₁ : KFAt p E (2 * f) r₁
  kf₀' : KFAt p E f r₀'
  img₀ : ((kZero p E r₀).subgroupOf L).map ε = (blkA (K := K) 0).range.map (q8 K)
  img₁ : ((kZero p E r₁).subgroupOf L).map ε = (blk8M (K := K)).range.map (q8 K)
  img₀' : ((kZero p E r₀').subgroupOf L).map ε = (blkA (K := K) 1).range.map (q8 K)
  w : G
  wL : w ∈ L
  wE : w ∈ Subgroup.normalizer (E : Set G)
  hw : r₀' = conjAut E w wE * r₀ * (conjAut E w wE)⁻¹
  εw : ε ⟨w, wL⟩ = q8 K swapM

theorem row8Frame_of
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hEA : E = A) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f) :
    Subgroup.center L = ⊥ ∧
      (∀ s ∈ reflectionSet p E, s ∈ torusImage E L → KFAt p E f s ∨ KFAt p E (2 * f) s) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
        Nonempty (Row8Frame p A L E f K) := by
  obtain ⟨hZ, hAt, K, hKf, hKfin, hchar, hK, ε, hε, hAT, r₀, r₁, r₀', h0, h0L, h1, h1L, h0', h0'L,
    hord, hk0, hk1, hk0', hi0, hi1, hi0', -, w, hwL, hwE, hw, hεw⟩ :=
    KF132.kf132Row8_frame hGA h hF hF13 hEA hf1 hpq hmod
  exact ⟨hZ, hAt, K, hKf, hKfin, hchar, ⟨⟨hK, ε, hε, hAT, r₀, r₁, r₀', h0, h0L, h1, h1L, h0', h0'L,
    hord, hk0, hk1, hk0', hi0, hi1, hi0', w, hwL, hwE, hw, hεw⟩⟩⟩


namespace Row8Frame

variable {p : ℕ} {A L E : Subgroup G} {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
  (fr : Row8Frame p A L E f K)

omit [Finite G] in
theorem inj (hZ : Subgroup.center L = ⊥) : Function.Injective fr.ε := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact eq_bot_iff.mpr (fr.central.central.trans hZ.le)

omit [Finite G] in
theorem surj : Function.Surjective fr.ε := fr.central.surjective

theorem q8_inj : Function.Injective (q8 K) := (KFOUT3.m8Iso (K := K)).injective

theorem kz₀ {c : G} (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hZ : Subgroup.center L = ⊥) :
    kZero p E fr.r₀ = pullG fr.ε ((slB K 0 1).map (q8 K)) := by
  refine eq_pullG_of_map (fr.inj hZ) (kZero_le_of_reflection h hF13 fr.mem₀ fr.mem₀L) ?_
  rw [fr.img₀, blkA_zero_range]

theorem kz₀' {c : G} (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hZ : Subgroup.center L = ⊥) :
    kZero p E fr.r₀' = pullG fr.ε ((slB K 2 3).map (q8 K)) := by
  refine eq_pullG_of_map (fr.inj hZ) (kZero_le_of_reflection h hF13 fr.mem₀' fr.mem₀'L) ?_
  rw [fr.img₀', blkA_one_range]

theorem kz₁ {c : G} (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hZ : Subgroup.center L = ⊥) :
    kZero p E fr.r₁ = pullG fr.ε ((blk8M (K := K)).range.map (q8 K)) := by
  refine eq_pullG_of_map (fr.inj hZ) (kZero_le_of_reflection h hF13 fr.mem₁ fr.mem₁L) ?_
  rw [fr.img₁]

theorem map_le_centralizer {Q₁ Q₂ : Subgroup ↥(M8 K)}
    (hc : Q₁ ≤ Subgroup.centralizer (Q₂ : Set ↥(M8 K))) :
    Q₁.map (q8 K) ≤ Subgroup.centralizer ((Q₂.map (q8 K) : Subgroup _) : Set _) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 (hc ha) b hb]

theorem kz_comm {c : G} (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hZ : Subgroup.center L = ⊥) :
    kZero p E fr.r₀ ≤ Subgroup.centralizer (kZero p E fr.r₀' : Set G) ∧
      kZero p E fr.r₀ ⊓ kZero p E fr.r₀' = ⊥ := by
  rw [fr.kz₀ h hF13 hZ, fr.kz₀' h hF13 hZ]
  refine ⟨pullG_le_centralizer (fr.inj hZ) (map_le_centralizer slB_zero_one_le_centralizer), ?_⟩
  have h1 : (slB K 0 1).map (q8 K) ⊓ (slB K 2 3).map (q8 K) = ⊥ := by
    rw [← Subgroup.map_inf (slB K 0 1) (slB K 2 3) (q8 K) (q8_inj (K := K)),
      slB_zero_one_inf_two_three, Subgroup.map_bot]
  rw [← pullG_inf, h1]
  exact pullG_bot (fr.inj hZ)


omit [Finite G] in
theorem slB_zero_one_ne_bot : slB K 0 1 ≠ ⊥ := by
  intro hbot
  have hu : (PSL2EvenBorel.uni (1 : K) : Matrix.SpecialLinearGroup (Fin 2) K) ≠ 1 := by
    intro h1
    exact PSL2EvenBorel.uni_not_mem_center one_ne_zero (h1 ▸ Subgroup.one_mem _)
  have hmem : blkA (K := K) 0 (PSL2EvenBorel.uni 1) ∈ slB K 0 1 := by
    rw [← blkA_zero_range]
    exact ⟨_, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hu (blkA_injective (K := K) 0 (hmem.trans (map_one _).symm))

theorem r₀_ne {c : G} (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hZ : Subgroup.center L = ⊥) : fr.r₀ ≠ fr.r₀' := by
  intro heq
  have h1 : kZero p E fr.r₀ = kZero p E fr.r₀' := by rw [heq]
  rw [fr.kz₀ h hF13 hZ, fr.kz₀' h hF13 hZ] at h1
  have h2 := (pullG_le_iff fr.surj).1 h1.le
  have h3 := (pullG_le_iff fr.surj).1 h1.ge
  have h4 : slB K 0 1 ≤ slB K 2 3 := by
    intro x hx
    have := h2 (Subgroup.mem_map_of_mem _ hx)
    obtain ⟨y, hy, hyx⟩ := this
    have := q8_inj hyx
    rwa [← this]
  have h5 : slB K 0 1 ≤ ⊥ := by
    rw [← slB_zero_one_inf_two_three]
    exact le_inf le_rfl h4
  exact slB_zero_one_ne_bot (le_bot_iff.1 h5)

end Row8Frame

set_option maxRecDepth 100000 in
theorem d8_reflection_pair : ∀ a x : DihedralGroup 4, a * a = 1 → a ≠ x * a * x⁻¹ →
    a * (x * a * x⁻¹) = (x * a * x⁻¹) * a ∧ a * (x * a * x⁻¹) ≠ 1 ∧
      ∀ y : DihedralGroup 4, y * (a * (x * a * x⁻¹)) = (a * (x * a * x⁻¹)) * y := by
  decide



theorem exists_eL {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hcard : Nat.card E = p ^ 3)
    {z : MulAut E} (hz : Inverter p E z) {f : ℕ} (hf2 : 2 ≤ f)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f) :
    Nonempty (↥(torusImage E L) ≃* DihedralGroup 4) := by
  have hcE : c ∈ E := h.A_le_E h.c_mem
  obtain ⟨r, hr, hrow, hW⟩ := member_row h hF hcard hz.six hz.no_eight
    (inverter_not_mem_torusImage h hcE h.c_ne_one hz.inv)
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exfalso
    obtain ⟨f', -, -, h3⟩ := hrow
    exact S13K.not_psl_three_and_psl_four hf2 h3 hmod
  · exact hW
  · exact hW
  · exact hW
  · exact hW

namespace Row8Frame

variable {p : ℕ} {A L E : Subgroup G} {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
  (fr : Row8Frame p A L E f K)

theorem u_data {c : G} (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hZ : Subgroup.center L = ⊥) (eL : ↥(torusImage E L) ≃* DihedralGroup 4) :
    fr.r₀ * fr.r₀' = fr.r₀' * fr.r₀ ∧ (fr.r₀ * fr.r₀') * (fr.r₀ * fr.r₀') = 1 ∧
      fr.r₀ * fr.r₀' ≠ 1 ∧ ∀ g ∈ torusImage E L, g * (fr.r₀ * fr.r₀') = (fr.r₀ * fr.r₀') * g := by
  have hxL : conjAut E fr.w fr.wE ∈ torusImage E L :=
    Sec12Three.mem_torusImage_iff.2 ⟨fr.w, fr.wL, fr.wE, rfl⟩
  set a : DihedralGroup 4 := eL ⟨fr.r₀, fr.mem₀L⟩ with ha
  set x : DihedralGroup 4 := eL ⟨conjAut E fr.w fr.wE, hxL⟩ with hx
  have hr02 : fr.r₀ * fr.r₀ = 1 := RefFacts.mul_self_eq_one fr.mem₀.1
  have hr0'2 : fr.r₀' * fr.r₀' = 1 := RefFacts.mul_self_eq_one fr.mem₀'.1
  have ha2 : a * a = 1 := by
    rw [ha, ← map_mul]
    have : (⟨fr.r₀, fr.mem₀L⟩ * ⟨fr.r₀, fr.mem₀L⟩ : ↥(torusImage E L)) = 1 := Subtype.ext hr02
    rw [this, map_one]
  have hconj : eL ⟨fr.r₀', fr.mem₀'L⟩ = x * a * x⁻¹ := by
    rw [ha, hx, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simpa using fr.hw
  have hne : a ≠ x * a * x⁻¹ := by
    intro h1
    apply fr.r₀_ne h hF13 hZ
    have := eL.injective (hconj.trans h1.symm)
    exact (congrArg Subtype.val this).symm
  obtain ⟨hcomm, hne1, hcen⟩ := d8_reflection_pair a x ha2 hne
  have hcomm' : fr.r₀ * fr.r₀' = fr.r₀' * fr.r₀ := by
    have h1 : eL (⟨fr.r₀, fr.mem₀L⟩ * ⟨fr.r₀', fr.mem₀'L⟩) =
        eL (⟨fr.r₀', fr.mem₀'L⟩ * ⟨fr.r₀, fr.mem₀L⟩) := by
      rw [map_mul, map_mul, hconj]
      exact hcomm
    exact congrArg Subtype.val (eL.injective h1)
  refine ⟨hcomm', ?_, ?_, ?_⟩
  · calc fr.r₀ * fr.r₀' * (fr.r₀ * fr.r₀') = fr.r₀ * (fr.r₀' * fr.r₀) * fr.r₀' := by group
      _ = fr.r₀ * (fr.r₀ * fr.r₀') * fr.r₀' := by rw [← hcomm']
      _ = (fr.r₀ * fr.r₀) * (fr.r₀' * fr.r₀') := by group
      _ = 1 := by rw [hr02, hr0'2, one_mul]
  · intro h1
    apply hne1
    have h2 : (⟨fr.r₀, fr.mem₀L⟩ * ⟨fr.r₀', fr.mem₀'L⟩ : ↥(torusImage E L)) = 1 :=
      Subtype.ext h1
    have h3 := congrArg eL h2
    rw [map_mul, hconj, map_one] at h3
    exact h3
  · intro g hg
    have h1 : eL (⟨g, hg⟩ * (⟨fr.r₀, fr.mem₀L⟩ * ⟨fr.r₀', fr.mem₀'L⟩)) =
        eL ((⟨fr.r₀, fr.mem₀L⟩ * ⟨fr.r₀', fr.mem₀'L⟩) * ⟨g, hg⟩) := by
      rw [map_mul, map_mul, map_mul, map_mul, hconj]
      exact hcen _
    exact congrArg Subtype.val (eL.injective h1)

end Row8Frame


omit [Finite G] in
theorem mem_normalizer_kZero {p : ℕ} {E : Subgroup G} (t : MulAut E) {ρ : G}
    (hρ : ∀ e ∈ E, ρ * e = e * ρ) : ρ ∈ Subgroup.normalizer (kZero p E t : Set G) := by
  have hρ' : ∀ e ∈ E, ρ * e * ρ⁻¹ = e := fun e he => by
    calc ρ * e * ρ⁻¹ = (e * ρ) * ρ⁻¹ := by rw [hρ e he]
      _ = e := by group
  have hρN : ρ ∈ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      rw [hρ' e he]; exact he
    · intro he
      have hx := hρ _ he
      have h3 : ρ * e * ρ⁻¹ = e := by
        refine mul_left_cancel (a := ρ) ?_
        calc ρ * (ρ * e * ρ⁻¹) = (ρ * e * ρ⁻¹) * ρ := hx
          _ = ρ * e := by group
      rw [h3] at he
      exact he
  have h1 : conjAut E ρ hρN = 1 := by
    refine MulEquiv.ext fun e => Subtype.ext ?_
    rw [Equivariance.coe_conjAut hρN]
    exact hρ' e e.2
  have h2 := kZero_conj p t hρN
  rw [h1, one_mul, inv_one, mul_one] at h2
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h3 : ∀ y, y ∈ kZero p E t ↔ ρ⁻¹ * y * ρ ∈ kZero p E t := fun y => by
    conv_lhs => rw [h2]
    exact Equivariance.mem_conjBy
  rw [h3 (ρ * x * ρ⁻¹)]
  have : ρ⁻¹ * (ρ * x * ρ⁻¹) * ρ = x := by group
  rw [this]


omit [Finite G] in
theorem commClause_conj {p : ℕ} {E : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) {s t : MulAut E}
    (h : kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) ∧
      kZero p E s ⊓ kZero p E t = ⊥) :
    kZero p E (conjAut E w hw * s * (conjAut E w hw)⁻¹) ≤
        Subgroup.centralizer (kZero p E (conjAut E w hw * t * (conjAut E w hw)⁻¹) : Set G) ∧
      kZero p E (conjAut E w hw * s * (conjAut E w hw)⁻¹) ⊓
        kZero p E (conjAut E w hw * t * (conjAut E w hw)⁻¹) = ⊥ := by
  obtain ⟨h1, h2⟩ := h
  rw [kZero_conj p s hw, kZero_conj p t hw, Equivariance.centralizer_conjBy]
  refine ⟨(conjBy_le_conjBy_iff w).2 h1, ?_⟩
  rw [← conjBy_inf, h2, conjBy_bot]

omit [Finite G] in
theorem commClause_symm {K K' : Subgroup G}
    (h : K ≤ Subgroup.centralizer (K' : Set G) ∧ K ⊓ K' = ⊥) :
    K' ≤ Subgroup.centralizer (K : Set G) ∧ K' ⊓ K = ⊥ := by
  refine ⟨fun x hx => ?_, by rw [inf_comm]; exact h.2⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.1 (h.1 hy) x hx).symm


namespace Row8Frame

variable {p : ℕ} {A L E : Subgroup G} {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
  (fr : Row8Frame p A L E f K)

theorem not_conj_zstar {c : G} (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hZ : Subgroup.center L = ⊥) (hcard : Nat.card E = p ^ 3)
    (B : Bridge p E) (hcomm : fr.r₀ * fr.r₀' = fr.r₀' * fr.r₀) {zs : MulAut E}
    (hzs : zs ∈ reflectionSet p E) (hzsc : ∀ g ∈ torusImage E L, g * zs = zs * g)
    (hzsL : zs ∉ torusImage E L) (hzsmov : autMovedInG E zs = Subgroup.zpowers c)
    (hpf : p ∣ 2 ^ f + 1) {r : ℕ} {R : Subgroup G} (hr : r.Prime) (hrf : r ∣ 2 ^ f - 1)
    (hRcard : Nat.card R = r) (hR0 : R ≤ Subgroup.centralizer (kZero p E fr.r₀ : Set G))
    (hR0' : R ≤ Subgroup.centralizer (kZero p E fr.r₀' : Set G))
    (hRE : ∀ x ∈ R, ∀ e ∈ E, x * e = e * x) (he : CFSG.twoLocalOddRank G = 3) :
    ∀ g ∈ reflectionGroup p E, g * fr.r₀ * g⁻¹ ≠ zs := by
  intro g hgX hg
  have hp := h.prime
  have hp2 : p ≠ 2 := by
    have := h.three_lt
    omega
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hr2 : r ≠ 2 := by
    rintro rfl
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hf1 : 1 ≤ f := fr.kf₀.2.1.1.2.1
    have : Odd (2 ^ f - 1) :=
      Nat.Even.sub_odd hq1 (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    exact (Nat.not_even_iff_odd.2 this) (even_iff_two_dvd.2 hrf)
  obtain ⟨y, hy, hyg⟩ := Sec1322.exists_lift (Sec1322.reflectionGroup_le E hgX)
  have hkfs : KFAt p E f zs := by
    rw [← hg, ← hyg]
    exact fr.kf₀.conj hy
  have hwL : conjAut E fr.w fr.wE ∈ reflectionGroup p E :=
    torusImage_le_reflectionGroup hF (Sec12Three.mem_torusImage_iff.2 ⟨fr.w, fr.wL, fr.wE, rfl⟩)
  have hne0 : fr.r₀ ≠ zs := fun h1 => hzsL (h1 ▸ fr.mem₀L)
  have hne0' : fr.r₀' ≠ zs := fun h1 => hzsL (h1 ▸ fr.mem₀'L)
  obtain ⟨⟨g₁, hg₁X, hg₁a, hg₁b⟩, ⟨g₂, hg₂X, hg₂a, hg₂b⟩⟩ :=
    B.triangle h hcard fr.mem₀ fr.mem₀' hzs (fr.r₀_ne h hF13 hZ) hne0 hne0' hcomm
      (hzsc _ fr.mem₀L) (hzsc _ fr.mem₀'L) hwL hgX fr.hw.symm hg
  obtain ⟨y₁, hy₁, hy₁g⟩ := Sec1322.exists_lift (Sec1322.reflectionGroup_le E hg₁X)
  obtain ⟨y₂, hy₂, hy₂g⟩ := Sec1322.exists_lift (Sec1322.reflectionGroup_le E hg₂X)
  have hc00 := fr.kz_comm h hF13 hZ
  have hcK0 : kZero p E zs ≤ Subgroup.centralizer (kZero p E fr.r₀ : Set G) ∧
      kZero p E zs ⊓ kZero p E fr.r₀ = ⊥ := by
    have := commClause_conj (p := p) hy₁ (commClause_symm hc00)
    rw [hy₁g, hg₁a, hg₁b] at this
    exact this
  have hcK0' : kZero p E zs ≤ Subgroup.centralizer (kZero p E fr.r₀' : Set G) ∧
      kZero p E zs ⊓ kZero p E fr.r₀' = ⊥ := by
    have := commClause_conj (p := p) hy₂ hc00
    rw [hy₂g, hg₂a, hg₂b] at this
    exact (commClause_symm this)
  have hRN : R ≤ Subgroup.normalizer (kZero p E zs : Set G) := fun x hx =>
    mem_normalizer_kZero zs (hRE x hx)
  have hRK : R ⊓ kZero p E zs = ⊥ := by
    rw [eq_bot_iff]
    intro ρ hρ
    rw [Subgroup.mem_bot]
    by_contra hρ1
    have hρord : orderOf ρ = r := by
      have hd : orderOf ρ ∣ r := hRcard ▸ Subgroup.orderOf_dvd_natCard R hρ.1
      rcases (Nat.dvd_prime hr).1 hd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.1 h1) hρ1
      · exact h1
    have hcK : c ∈ kZero p E zs := by
      have hm : autMovedInG E zs ≤ kZero p E zs := hkfs.2.2.2.1
      rw [hzsmov] at hm
      exact hm (Subgroup.mem_zpowers c)
    have hcord : orderOf c = p := Sec12Three.orderOf_c h
    have hcm : c * ρ = ρ * c := (hRE ρ hρ.1 c hcE).symm
    exact not_commute_psl2 hkfs.2.1 hp hr hp2 hpf hrf (x := ⟨c, hcK⟩) (y := ⟨ρ, hρ.2⟩)
      (by rw [← Subgroup.orderOf_coe]; exact hcord)
      (by rw [← Subgroup.orderOf_coe]; exact hρord) (Subtype.ext hcm)
  have h4 := four_le_localRank_of_blocks hr hr2 hkfs.2.1 fr.kf₀.2.1 fr.kf₀'.2.1 hrf hrf hrf
    hcK0.1 hcK0'.1 hc00.1 hRcard hRN hRK hR0 hR0'
  exact false_of_four_le_localRank hr hr2 h4 he


theorem E_eq_sup {c : G} (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hZ : Subgroup.center L = ⊥) :
    E = Subgroup.zpowers c ⊔ (E ⊓ L) := by
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hpZ : ¬ p ∣ Nat.card (Subgroup.center L) := by
    rw [hZ, Subgroup.card_bot]
    exact fun hd => h.prime.one_lt.ne' (Nat.dvd_one.1 hd)
  have hCN := hF13.centralizer hpZ
  have hEN : ∀ e ∈ E, e ∈ Subgroup.normalizer (L : Set G) := by
    intro e he
    refine hCN ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val (h.E_elem.is_comm.comm ⟨c, hcE⟩ ⟨e, he⟩)).symm
  obtain ⟨hcls, hsplit⟩ := hF.four
  have hE1 : E = Subgroup.zpowers c ⊔ ⁅E, L ⊓ torusNormalizer E⁆ := by
    rcases hsplit with ⟨hE, -⟩ | ⟨⟨hr11, -⟩, -⟩
    · exact hE
    · exfalso
      have hcenter : Nat.card (Subgroup.center L) = 5 := hr11.2.1
      rw [hZ, Subgroup.card_bot] at hcenter
      omega
  have hcomm : ⁅E, L ⊓ torusNormalizer E⁆ ≤ E ⊓ L := by
    rw [Subgroup.commutator_le]
    intro e he ℓ hℓ
    have hℓL : ℓ ∈ L := hℓ.1
    have hℓN : ℓ ∈ Subgroup.normalizer (E : Set G) := hℓ.2
    have hℓe : ℓ * e⁻¹ * ℓ⁻¹ ∈ E := by
      have := (Subgroup.mem_normalizer_iff.1 hℓN e⁻¹).1 (E.inv_mem he)
      exact this
    rw [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · have : e * ℓ * e⁻¹ * ℓ⁻¹ = e * (ℓ * e⁻¹ * ℓ⁻¹) := by group
      rw [this]
      exact E.mul_mem he hℓe
    · have h1 : e * ℓ * e⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hEN e he) ℓ).1 hℓL
      exact L.mul_mem h1 (L.inv_mem hℓL)
  apply le_antisymm
  · calc E = Subgroup.zpowers c ⊔ ⁅E, L ⊓ torusNormalizer E⁆ := hE1
      _ ≤ Subgroup.zpowers c ⊔ (E ⊓ L) := sup_le_sup_left hcomm _
  · exact sup_le (Subgroup.zpowers_le.2 hcE) inf_le_left


theorem R_data {c : G} (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hZ : Subgroup.center L = ⊥) (hEA : E = A)
    {Rm : Subgroup ↥(M8 K)} (hRm : Rm ≤ (Tl K).range) :
    pullG fr.ε (Rm.map (q8 K)) ≤ L ∧
      pullG fr.ε (Rm.map (q8 K)) ≤ Subgroup.centralizer (kZero p E fr.r₀ : Set G) ∧
      pullG fr.ε (Rm.map (q8 K)) ≤ Subgroup.centralizer (kZero p E fr.r₀' : Set G) ∧
      ∀ x ∈ pullG fr.ε (Rm.map (q8 K)), ∀ e ∈ E, x * e = e * x := by
  have hTl01 : (Tl K).range ≤
      Subgroup.centralizer ((slB K 0 1 : Subgroup ↥(M8 K)) : Set ↥(M8 K)) := by
    rw [← centralizer_slB_blocks]
    exact Subgroup.centralizer_le (by exact_mod_cast le_sup_left)
  have hTl23 : (Tl K).range ≤
      Subgroup.centralizer ((slB K 2 3 : Subgroup ↥(M8 K)) : Set ↥(M8 K)) := by
    rw [← centralizer_slB_blocks]
    exact Subgroup.centralizer_le (by exact_mod_cast le_sup_right)
  refine ⟨pullG_le _ _, ?_, ?_, ?_⟩
  · rw [fr.kz₀ h hF13 hZ]
    exact pullG_le_centralizer (fr.inj hZ) (map_le_centralizer (hRm.trans hTl01))
  · rw [fr.kz₀' h hF13 hZ]
    exact pullG_le_centralizer (fr.inj hZ) (map_le_centralizer (hRm.trans hTl23))
  · intro x hx e he
    obtain ⟨hxL, hxQ⟩ := mem_pullG.1 hx
    obtain ⟨ρ, hρ, hρx⟩ := hxQ
    obtain ⟨a, rfl⟩ := hRm hρ
    have hle : E ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [E_eq_sup h hF hF13 hZ]
      refine sup_le (Subgroup.zpowers_le.2 ?_) ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Sec12Three.comm_c_L h x hxL
      · intro b hb
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hbA : b ∈ A ⊓ L := hEA ▸ hb
        have hb1 : fr.ε ⟨b, hb.2⟩ ∈ (T8 p K).map (q8 K) := by
          rw [← fr.hAT]
          exact ⟨⟨b, hb.2⟩, Subgroup.mem_subgroupOf.2 hbA, rfl⟩
        obtain ⟨t, ht, hth⟩ := hb1
        have hcomm : fr.ε ⟨b, hb.2⟩ * fr.ε ⟨x, hxL⟩ = fr.ε ⟨x, hxL⟩ * fr.ε ⟨b, hb.2⟩ := by
          rw [← hth, ← hρx, ← map_mul, ← map_mul, ← (Tl_comm_T8 ht a)]
        have := (fr.inj hZ) (a₁ := (⟨b, hb.2⟩ : ↥L) * ⟨x, hxL⟩)
          (a₂ := (⟨x, hxL⟩ : ↥L) * ⟨b, hb.2⟩) (by rw [map_mul, map_mul]; exact hcomm)
        exact congrArg Subtype.val this
    exact Subgroup.mem_centralizer_iff.1 (hle he) x (Set.mem_singleton x)


omit [Finite G] in
theorem card_R (hZ : Subgroup.center L = ⊥) (Rm : Subgroup ↥(M8 K)) :
    Nat.card (pullG fr.ε (Rm.map (q8 K))) = Nat.card Rm := by
  rw [card_pullG fr.surj (fr.inj hZ), Subgroup.card_map_of_injective (q8_inj (K := K))]

theorem kfAt_zstar {c : G} (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hZ : Subgroup.center L = ⊥) (hcard : Nat.card E = p ^ 3)
    (B : Bridge p E) (hcomm : fr.r₀ * fr.r₀' = fr.r₀' * fr.r₀) {zs : MulAut E}
    (hzs : zs ∈ reflectionSet p E) (hzsc : ∀ g ∈ torusImage E L, g * zs = zs * g)
    (hzsL : zs ∉ torusImage E L) (hzsmov : autMovedInG E zs = Subgroup.zpowers c)
    (hpf : p ∣ 2 ^ f + 1) {r : ℕ} {R : Subgroup G} (hr : r.Prime) (hrf : r ∣ 2 ^ f - 1)
    (hRcard : Nat.card R = r) (hR0 : R ≤ Subgroup.centralizer (kZero p E fr.r₀ : Set G))
    (hR0' : R ≤ Subgroup.centralizer (kZero p E fr.r₀' : Set G))
    (hRE : ∀ x ∈ R, ∀ e ∈ E, x * e = e * x) (he : CFSG.twoLocalOddRank G = 3) :
    KFAt p E (2 * f) zs := by
  have hnot := fr.not_conj_zstar h hF hF13 hZ hcard B hcomm hzs hzsc hzsL hzsmov hpf hr hrf hRcard
    hR0 hR0' hRE he
  have hL₀ := fr.mem₀L
  have hL₁ := fr.mem₁L
  have hmem : ∀ x ∈ torusImage E L, zs ≠ x := fun x hx h1 => hzsL (h1 ▸ hx)
  have hcls := B.zstar_class h hcard fr.mem₀ fr.mem₁ hzs fr.ord₀₁ (hzsc _ hL₀) (hzsc _ hL₁)
    (hmem _ hL₀) (hmem _ hL₁)
    (hmem _ ((torusImage E L).mul_mem ((torusImage E L).mul_mem hL₀ hL₁)
      ((torusImage E L).inv_mem hL₀)))
    (hmem _ ((torusImage E L).mul_mem ((torusImage E L).mul_mem hL₁ hL₀)
      ((torusImage E L).inv_mem hL₁)))
  rcases hcls with ⟨g, hgX, hg⟩ | ⟨g, hgX, hg⟩
  · exact absurd hg (hnot g hgX)
  · obtain ⟨y, hy, hyg⟩ := Sec1322.exists_lift (Sec1322.reflectionGroup_le E hgX)
    rw [← hg, ← hyg]
    exact fr.kf₁.conj hy

end Row8Frame


end CFSG.RankThree.PartOne.K1320

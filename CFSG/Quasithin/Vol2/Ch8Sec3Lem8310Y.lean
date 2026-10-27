module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8310X
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8310KG
public import CFSG.RankThree.PartTwo.Sec3.OrderThreeFixedPointFreeModule
public import CFSG.Quasithin.Vol2.Ch11SecBE22NParam
public import CFSG.Quasithin.Vol2.Ch11SecB35C

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

namespace Ch8310Y

section Quot

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem mem_uFamHat_map {R T H M : Subgroup Γ} [R.Normal] (hRT : R ≤ T) (hTH : T ≤ H)
    (hU : IsUniqueMaxOver H T M) (hnn : ¬ H ≤ Subgroup.normalizer (T : Set Γ)) :
    H.map (QuotientGroup.mk' R) ∈ uFamHat ⊤ (T.map (QuotientGroup.mk' R)) := by
  set π := QuotientGroup.mk' R with hπ
  have hker : π.ker = R := QuotientGroup.ker_mk' R
  obtain ⟨⟨hMH, hMmax⟩, hTM, huniq⟩ := isUniqueMaxOver_iff.mp hU
  have hcm : ∀ Z : Subgroup Γ, R ≤ Z → (Z.map π).comap π = Z := fun Z hZ => by
    rw [Subgroup.comap_map_eq, hker, sup_eq_left.mpr hZ]
  have hmc : ∀ Z : Subgroup (Γ ⧸ R), (Z.comap π).map π = Z := fun Z =>
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R) Z
  have hcs : ∀ A B : Subgroup (Γ ⧸ R), A < B → A.comap π < B.comap π := fun A B hAB =>
    lt_of_le_of_ne (Subgroup.comap_mono hAB.le) fun he => hAB.ne (by rw [← hmc A, he, hmc B])
  have hRM : R ≤ M := hRT.trans hTM
  have hRH : R ≤ H := hRT.trans hTH
  have hMbH : M.map π < H.map π := by
    refine lt_of_le_of_ne (Subgroup.map_mono hMH.le) fun h => hMH.ne ?_
    rw [← hcm M hRM, h, hcm H hRH]
  have hMbmax : IsMaxSubgroupIn (H.map π) (M.map π) := by
    refine ⟨hMbH, fun Z hMZ hZH => ?_⟩
    have h1 : M < Z.comap π := by
      rw [← hcm M hRM]
      exact hcs _ _ hMZ
    have h2 : Z.comap π ≤ H := by
      rw [← hcm H hRH]
      exact Subgroup.comap_mono hZH
    rw [← hmc Z, hMmax _ h1 h2]
  refine ⟨⟨le_top, lt_of_le_of_ne (Subgroup.map_mono hTH) fun h => ?_, ?_⟩, fun h => ?_⟩
  ·
    apply hnn
    have : T = H := by rw [← hcm T hRT, h, hcm H hRH]
    rw [← this]
    exact Subgroup.le_normalizer
  ·
    have hset : maxOver (H.map π) (T.map π) = {M.map π} := by
      ext N
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro ⟨hN, hTN⟩
        have hTN' : T ≤ N.comap π := by
          rw [← hcm T hRT]
          exact Subgroup.comap_mono hTN
        have hNH : N.comap π < H := by
          rw [← hcm H hRH]
          exact hcs _ _ hN.1
        have hNM : N ≤ M.map π := by
          rw [← hmc N]
          exact Subgroup.map_mono (Vol2.Ch11.SecB.le_of_isUniqueMaxOver hU hTN' hNH)
        rcases eq_or_lt_of_le hNM with h | h
        · exact h
        · exact absurd (hN.2 _ h hMbH.le) hMbH.ne
      · rintro rfl
        exact ⟨hMbmax, Subgroup.map_mono hTM⟩
    rw [hset, Set.ncard_singleton]
  ·
    apply hnn
    intro x hx
    refine A4.mem_normalizer_of_conj_mem fun t ht => ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp (h ⟨x, hx, rfl⟩) (π t)).mp ⟨t, ht, rfl⟩
    have h2 : π (x * t * x⁻¹) ∈ T.map π := by
      rw [map_mul, map_mul, map_inv]
      exact h1
    rw [← hcm T hRT]
    exact h2

end Quot

section Sub

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isUniqueMaxOver_subgroupOf {Y H T M : Subgroup G} (hHY : H ≤ Y)
    (hU : IsUniqueMaxOver H T M) :
    IsUniqueMaxOver (H.subgroupOf Y) (T.subgroupOf Y) (M.subgroupOf Y) := by
  obtain ⟨⟨hMH, hMmax⟩, hTM, huniq⟩ := isUniqueMaxOver_iff.mp hU
  have hMY : M ≤ Y := hMH.le.trans hHY
  have hTY : T ≤ Y := hTM.trans hMY
  have hback : ∀ A : Subgroup ↥Y, (A.map Y.subtype).subgroupOf Y = A := fun A =>
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective A
  have hfwd : ∀ Z : Subgroup G, Z ≤ Y → (Z.subgroupOf Y).map Y.subtype = Z := fun Z hZ =>
    Subgroup.map_subgroupOf_eq_of_le hZ
  have hle : ∀ A B : Subgroup ↥Y, A.map Y.subtype ≤ B.map Y.subtype ↔ A ≤ B := fun A B =>
    Subgroup.map_le_map_iff_of_injective Y.subtype_injective
  have hmax : ∀ N : Subgroup ↥Y, IsMaxSubgroupIn (H.subgroupOf Y) N →
      IsMaxSubgroupIn H (N.map Y.subtype) := by
    rintro N ⟨hNH, hNmax⟩
    refine ⟨?_, fun K hNK hKH => ?_⟩
    · rw [← hfwd H hHY]
      exact lt_of_le_of_ne ((hle _ _).mpr hNH.le) fun h => hNH.ne
        (by rw [← hback N, h, hback])
    · have hKY : K ≤ Y := hKH.trans hHY
      have h1 : N < K.subgroupOf Y := by
        refine lt_of_le_of_ne ?_ fun h => hNK.ne (by rw [h, hfwd K hKY])
        rw [← hle, hfwd K hKY]
        exact hNK.le
      have h2 : K.subgroupOf Y ≤ H.subgroupOf Y := Subgroup.subgroupOf_mono Y hKH
      rw [← hfwd K hKY, hNmax _ h1 h2, hfwd H hHY]
  refine isUniqueMaxOver_iff.mpr ⟨⟨?_, fun K hMK hKH => ?_⟩, ?_, fun N hN hTN => ?_⟩
  · refine lt_of_le_of_ne ?_ fun h => hMH.ne (by rw [← hfwd M hMY, h, hfwd H hHY])
    rw [← hle, hfwd M hMY, hfwd H hHY]
    exact hMH.le
  · have h1 : M < K.map Y.subtype := by
      rw [← hfwd M hMY]
      exact lt_of_le_of_ne ((hle _ _).mpr hMK.le) fun h => hMK.ne
        (by rw [← hback (M.subgroupOf Y), h, hback])
    have h2 : K.map Y.subtype ≤ H := by
      rw [← hfwd H hHY]
      exact (hle _ _).mpr hKH
    rw [← hback K, hMmax _ h1 h2]
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hTM (Subgroup.mem_subgroupOf.mp hx))
  · have h1 := huniq _ (hmax N hN) (by
      rw [← hfwd T hTY]
      exact (hle _ _).mpr hTN)
    rw [← hback N, h1]

end Sub

theorem center_eq_bot_of_not_prime {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (h : ¬ (Nat.card S).Prime) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hc | hc
  · exact hc
  · exfalso
    apply h
    let _ : CommGroup S := { (inferInstance : Group S) with
      mul_comm := fun a b =>
        (Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top a : a ∈ Subgroup.center S) b).symm }
    exact IsSimpleGroup.prime_card

section Cases

variable {G : Type} [Group G] [Finite G]

theorem simple_center_of_alt {Kz : Subgroup G}
    (halt : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥Kz ⧸ CFSG.pCore 2 ↥Kz) .PSL 4 2 1 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥Kz ⧸ CFSG.pCore 2 ↥Kz) .PSL 5 2 1 ∨
      Nonempty (↥Kz ⧸ CFSG.pCore 2 ↥Kz ≃* CFSG.Blueprint.NativeSporadic.Carrier .He)) :
    IsSimpleGroup (↥Kz ⧸ CFSG.pCore 2 ↥Kz) ∧
      Subgroup.center (↥Kz ⧸ CFSG.pCore 2 ↥Kz) = ⊥ := by
  have hordA : ∀ n : ℕ, 2 ≤ n → ¬ (CFSG.Open.ordA n (2 ^ 1)).Prime := by
    intro n hn
    rw [CFSG.Open.ordA, pow_one, show (2 : ℕ) - 1 = 1 from rfl, Nat.gcd_one_right, Nat.div_one]
    have h3 : (2 ^ 2 - 1 : ℕ) ∣ ∏ i ∈ Finset.Icc 2 (n + 1), (2 ^ i - 1) :=
      Finset.dvd_prod_of_mem (fun i => 2 ^ i - 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    refine Nat.not_prime_mul ?_ ?_
    · have : 2 ≤ n * (n + 1) / 2 := by
        have : 2 * 3 ≤ n * (n + 1) := Nat.mul_le_mul hn (by omega)
        omega
      have h4 : 2 ^ 2 ≤ 2 ^ (n * (n + 1) / 2) := Nat.pow_le_pow_right (by norm_num) this
      omega
    · intro h1
      rw [h1] at h3
      exact absurd (Nat.le_of_dvd one_pos h3) (by norm_num)
  have key : IsSimpleGroup (↥Kz ⧸ CFSG.pCore 2 ↥Kz) ∧
      ¬ (Nat.card (↥Kz ⧸ CFSG.pCore 2 ↥Kz)).Prime := by
    rcases halt with h | h | he
    · refine ⟨CFSG.RankThree.PartTwo.Sec3.isSimpleGroup_of_statedClassicalModel_psl h, ?_⟩
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl]
      exact hordA 3 (by norm_num)
    · refine ⟨CFSG.RankThree.PartTwo.Sec3.isSimpleGroup_of_statedClassicalModel_psl h, ?_⟩
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl]
      exact hordA 4 (by norm_num)
    · obtain ⟨e⟩ := he
      have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .He) :=
        CFSG.Sporadic.He.isSimpleGroup_He
      refine ⟨e.isSimpleGroup, ?_⟩
      rw [Nat.card_congr e.toEquiv]
      have h1 : Nat.card CFSG.Blueprint.NativeSporadic.He = 4030387200 :=
        CFSG.Sporadic.He.card_He
      change ¬ (Nat.card CFSG.Blueprint.NativeSporadic.He).Prime
      rw [h1]
      norm_num
  have := key.1
  exact ⟨key.1, center_eq_bot_of_not_prime key.2⟩

theorem false_of_case_ii_iii (hLn2 : KG8310MinParLn2)
    (hHe : KG8310MinParHe) {T L : Subgroup G} {z : G} (hT2 : IsPGroup 2 T)
    (hTodd : ¬ 2 ∣ T.index) (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    (halt : CFSG.Assembly.LowTwoRank.StatedClassicalModel
          (↥(ch83Kz T L z) ⧸ CFSG.pCore 2 ↥(ch83Kz T L z)) .PSL 4 2 1 ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel
          (↥(ch83Kz T L z) ⧸ CFSG.pCore 2 ↥(ch83Kz T L z)) .PSL 5 2 1 ∨
        Nonempty (↥(ch83Kz T L z) ⧸ CFSG.pCore 2 ↥(ch83Kz T L z) ≃*
          CFSG.Blueprint.NativeSporadic.Carrier .He))
    {H M : Subgroup G} (hTH : T ≤ H) (hHK : H ≤ ch83Kz T L z ⊔ T)
    (hU : IsUniqueMaxOver H T (H ⊓ M)) (hnn : ¬ H ≤ Subgroup.normalizer (T : Set G))
    (h5 : 5 ∣ Nat.card H) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Gz := Subgroup.centralizer ({z} : Set G) with hGz
  set Kz := ch83Kz T L z with hKzdef
  have hXGz : ch83X T L z ≤ Gz := (twoResidual_le _).trans inf_le_right
  have hKzGz : Kz ≤ Gz := conjClosure_le fun h hh x hx =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hh (hXGz hx)) (Subgroup.inv_mem _ hh)
  have hGzKz : Gz ≤ Subgroup.normalizer (Kz : Set G) := le_normalizer_conjClosure _ _
  set Y := Kz ⊔ T with hYdef
  have hYGz : Y ≤ Gz := sup_le hKzGz hTz
  have hKzY : Kz ≤ Y := le_sup_left
  have hTY : T ≤ Y := le_sup_right
  have hHY : H ≤ Y := hHK
  have hYKz : Y ≤ Subgroup.normalizer (Kz : Set G) := hYGz.trans hGzKz
  obtain ⟨-, hZ⟩ := simple_center_of_alt halt
  set Q₀ := pCoreOf 2 Kz with hQ₀
  have hQ₀Kz : Q₀ ≤ Kz := CFSG.LieType.BorelTits.pCoreOf_le 2 Kz
  have hYQ₀ : Y ≤ Subgroup.normalizer (Q₀ : Set G) := fun y hy =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Kz (hYKz hy)
  have hR1 : ∀ g ∈ Kz, (∀ x ∈ Kz, g * x * g⁻¹ * x⁻¹ ∈ Q₀) → g ∈ Q₀ := by
    intro g hg hgx
    set π₀ := QuotientGroup.mk' (CFSG.pCore 2 ↥Kz) with hπ₀
    have hc : π₀ ⟨g, hg⟩ ∈ Subgroup.center (↥Kz ⧸ CFSG.pCore 2 ↥Kz) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
      have h2 : ⁅(⟨g, hg⟩ : ↥Kz), x⁆ ∈ CFSG.pCore 2 ↥Kz := by
        rw [commutatorElement_def]
        obtain ⟨y, hy, hyx⟩ := hgx x x.2
        have : y = ⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹ * x⁻¹ := Subtype.ext hyx
        rw [← this]
        exact hy
      have h3 : ⁅π₀ ⟨g, hg⟩, π₀ x⁆ = 1 := by
        rw [← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff _).mpr h2
      exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
    rw [hZ, Subgroup.mem_bot] at hc
    have h4 : (⟨g, hg⟩ : ↥Kz) ∈ CFSG.pCore 2 ↥Kz := (QuotientGroup.eq_one_iff _).mp hc
    exact ⟨⟨g, hg⟩, h4, rfl⟩
  set RG := sectionCentralizer Kz Q₀ ⊓ Y with hRGdef
  have hRGKz : ∀ g ∈ RG, g ∈ Kz → g ∈ Q₀ := fun g hg hgK => hR1 g hgK hg.1.2.2
  have hQ₀RG : Q₀ ≤ RG := by
    intro o ho
    have hoK := hQ₀Kz ho
    refine ⟨⟨Subgroup.le_normalizer hoK,
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Kz hoK, fun x hx => ?_⟩, hKzY hoK⟩
    have h1 : x * o⁻¹ * x⁻¹ ∈ Q₀ :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Kz hx)
        o⁻¹).mp (Q₀.inv_mem ho)
    have e : o * x * o⁻¹ * x⁻¹ = o * (x * o⁻¹ * x⁻¹) := by group
    rw [e]
    exact Q₀.mul_mem ho h1
  have hRG2 : ∀ g ∈ RG, ∃ k : ℕ, g ^ 2 ^ k = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := B6.isTwoQuotient_of_sup_eq (C := Kz) (D := Y) hT2 hYKz (sup_comm T Kz) g
      hg.2
    have hgk : g ^ 2 ^ k ∈ Q₀ := hRGKz _ (RG.pow_mem hg _) hk
    obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Kz ⟨_, hgk⟩
    refine ⟨k + m, ?_⟩
    have : (g ^ 2 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    rw [pow_add, pow_mul, this]
  have hRGn : ∀ y ∈ Y, ∀ g ∈ RG, y * g * y⁻¹ ∈ RG := by
    intro y hy g hg
    refine ⟨⟨(Subgroup.normalizer (Kz : Set G)).mul_mem ((Subgroup.normalizer
      (Kz : Set G)).mul_mem (hYKz hy) hg.1.1) ((Subgroup.normalizer _).inv_mem (hYKz hy)),
      (Subgroup.normalizer (Q₀ : Set G)).mul_mem ((Subgroup.normalizer (Q₀ : Set G)).mul_mem
        (hYQ₀ hy) hg.1.2.1) ((Subgroup.normalizer _).inv_mem (hYQ₀ hy)), fun x hx => ?_⟩,
      Y.mul_mem (Y.mul_mem hy hg.2) (Y.inv_mem hy)⟩
    have hx' : y⁻¹ * x * y ∈ Kz := by
      have := (Subgroup.mem_normalizer_iff.mp (hYKz (Y.inv_mem hy)) x).mp hx
      simpa using this
    have h1 := hg.1.2.2 _ hx'
    have h2 := (Subgroup.mem_normalizer_iff.mp (hYQ₀ hy) _).mp h1
    have e : y * g * y⁻¹ * x * (y * g * y⁻¹)⁻¹ * x⁻¹ =
        y * (g * (y⁻¹ * x * y) * g⁻¹ * (y⁻¹ * x * y)⁻¹) * y⁻¹ := by group
    rw [e]
    exact h2
  set R := RG.subgroupOf Y with hRdef
  have hRn : R.Normal := ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr
    (hRGn g g.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
  have hR2 : IsPGroup 2 R := fun r => by
    obtain ⟨k, hk⟩ := hRG2 _ (Subgroup.mem_subgroupOf.mp r.2)
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using hk))⟩
  set T' := T.subgroupOf Y with hT'def
  have hT'syl : IsPGroup 2 T' ∧ ¬ 2 ∣ T'.index := by
    refine ⟨hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTY).symm, fun h => hTodd ?_⟩
    exact h.trans (Subgroup.relIndex_dvd_index_of_le hTY)
  have hRT : R ≤ T' := hR2.le_sylow_of_normal (hT'syl.1.toSylow hT'syl.2)
  set H' := H.subgroupOf Y with hH'def
  have hT'H' : T' ≤ H' := Subgroup.subgroupOf_mono Y hTH
  have hU' := isUniqueMaxOver_subgroupOf (M := H ⊓ M) hHY hU
  have hnn' : ¬ H' ≤ Subgroup.normalizer (T' : Set ↥Y) := by
    intro h
    apply hnn
    intro x hx
    refine A4.mem_normalizer_of_conj_mem fun t ht => ?_
    have hxH' : (⟨x, hHY hx⟩ : ↥Y) ∈ H' := Subgroup.mem_subgroupOf.mpr hx
    have h1 := (Subgroup.mem_normalizer_iff.mp (h hxH')
      ⟨t, hTY ht⟩).mp (Subgroup.mem_subgroupOf.mpr ht)
    simpa using Subgroup.mem_subgroupOf.mp h1
  have hP := mem_uFamHat_map hRT hT'H' hU' hnn'
  set π := QuotientGroup.mk' R with hπ
  set Lx := (Kz.subgroupOf Y).map π with hLxdef
  have hLn : Lx.Normal := by
    have h1 : (Kz.subgroupOf Y).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKzY).mpr hYKz
    exact h1.map π (QuotientGroup.mk'_surjective R)
  set f : ↥Kz →* ↥Y ⧸ R := π.comp (Subgroup.inclusion hKzY) with hfdef
  have hfr : f.range = Lx := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hKzY x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hfk : f.ker = CFSG.pCore 2 ↥Kz := by
    ext x
    rw [MonoidHom.mem_ker, hfdef, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hRdef, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hRGKz _ hx x.2
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact hQ₀RG ⟨x, hx, rfl⟩
  have eL : (↥Kz ⧸ CFSG.pCore 2 ↥Kz) ≃* ↥Lx :=
    (QuotientGroup.quotientMulEquivOfEq hfk.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hfr))
  have hC : Subgroup.centralizer (Lx : Set (↥Y ⧸ R)) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective R q
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hRdef,
      Subgroup.mem_subgroupOf]
    have hyKz := hYKz y.2
    have hyQ₀ := hYQ₀ y.2
    refine ⟨⟨hyKz, hyQ₀, fun x hx => ?_⟩, y.2⟩
    have hxL : π ⟨x, hKzY hx⟩ ∈ Lx := ⟨⟨x, hKzY hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hq _ hxL
    have h2 : π (⁅y, ⟨x, hKzY hx⟩⁆) = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h1.symm
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hRdef,
      Subgroup.mem_subgroupOf] at h2
    have hcK : ((⁅y, ⟨x, hKzY hx⟩⁆ : ↥Y) : G) ∈ Kz := by
      have h3 : (y : G) * x * (y : G)⁻¹ ∈ Kz :=
        (Subgroup.mem_normalizer_iff.mp hyKz x).mp hx
      simpa [commutatorElement_def] using Kz.mul_mem h3 (Kz.inv_mem hx)
    have := hRGKz _ h2 hcK
    simpa [commutatorElement_def] using this
  have hS : IsSylowTwoOf (T'.map π) ⊤ := by
    let Sy : Sylow 2 (↥Y ⧸ R) :=
      (hT'syl.1.toSylow hT'syl.2).mapSurjective (QuotientGroup.mk'_surjective R)
    have hSy : (Sy : Subgroup (↥Y ⧸ R)) = T'.map π := by
      rw [Sylow.coe_mapSurjective]
      rfl
    refine ⟨le_top, hSy ▸ Sy.isPGroup', ?_⟩
    show ¬ 2 ∣ (T'.map π).relIndex ⊤
    rw [Subgroup.relIndex_top_right, ← hSy]
    exact Sy.not_dvd_index
  have h5P : ¬ 5 ∣ Nat.card ↥(H'.map π) := by
    rcases halt with h | h | he
    · exact hLn2 _ Lx (T'.map π) (H'.map π) hLn
        (Or.inl (CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv eL h)) hC hS hP
    · exact hLn2 _ Lx (T'.map π) (H'.map π) hLn
        (Or.inr (CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv eL h)) hC hS hP
    · obtain ⟨e⟩ := he
      exact hHe _ Lx (T'.map π) (H'.map π) hLn ⟨eL.symm.trans e⟩ hC hS hP
  apply h5P
  set φ : ↥H' →* ↥Y ⧸ R := π.comp H'.subtype with hφ
  have hφr : φ.range = H'.map π := by rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hφk : IsPGroup 2 φ.ker := by
    intro x
    have hx : (QuotientGroup.mk' R) ((x : ↥H') : ↥Y) = 1 := x.2
    have hxR : ((x : ↥H') : ↥Y) ∈ R := (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨k, hk⟩ := hR2 ⟨_, hxR⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  obtain ⟨a, ha⟩ := hφk.exists_card_eq
  have hcard : Nat.card ↥H' = 2 ^ a * Nat.card ↥(H'.map π) := by
    rw [← hφr, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, ← ha,
      mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have hH' : Nat.card ↥H' = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHY).toEquiv
  rw [← hH', hcard] at h5
  exact (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 5 2)).dvd_of_dvd_mul_left h5

end Cases

end Ch8310Y

open Ch8310Y in
theorem claim8310Excl_of
    (hE22 : E2.E22StatementC) (h443 : Stmt4_4_3Orbit')
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h3228 : Stmt3_2_2_eight) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h326 : Stmt3_2_6C) (h3108 : Stmt3_2_10_eight)
    (hLn2 : KG8310MinParLn2) (hHe : KG8310MinParHe) : Claim8310Excl := by
  intro G _ _ T L I hyp _ _ hrow z hz2 hzV halt H hH hHK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hyp.fsu.simple
  have h37' := a37ForSQTK_of_cat h37
  have h38' := a38ForSQTK_of_cat h38
  have h39' := a39ForSQTK_of_cat h39
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hTH : T ≤ H := hH.1.1
  have hTsyl : IsSylowTwoOf T H := Ch837.isSylowTwoOf_of_le hyp.fsu.sylow hTH
  have hTM : T ≤ fsuM T L := le_normalizer_conjClosure L T
  have hU : IsUniqueMaxOver H T (H ⊓ fsuM T L) := by
    obtain ⟨S, hS⟩ := exists_sylow_coe_eq hyp.fsu.sylow
    have := IsHStar.isUniqueMaxOver S (hS ▸ hH) (hS ▸ hTM)
    rwa [hS] at this
  have hNT : Subgroup.normalizer (T : Set G) ≤ fsuM T L := by
    have hJ := thompsonJ_le_centralizer_fsuV h37' h38' h39' hyp hV hN
    have hVVM := Ch8313.fsuV_eq_fsuVM h326 hyp hrow
    have hVp : IsVplus T L I (fsuV T I) := by
      by_cases hc' : L ≠ conjClosure L T ∧ Case326VM T L I
      · exact Or.inl ⟨hc'.1, hc'.2, hVVM⟩
      · exact Or.inr ⟨hc', rfl⟩
    exact (h3108 G T L I (fsuV T I) hyp.fsu hVp hJ T hyp.fsu.sylow.1 (thompsonJ_le_self T)).2
  have hnn : ¬ H ≤ Subgroup.normalizer (T : Set G) := fun hle => hH.2.1 (hle.trans hNT)
  have hmin : MinParabolic H T (H ⊓ fsuM T L) := ⟨hTsyl, hnn, hU⟩
  refine le_antisymm ?_ (E2.E22A.one_le_nParam hmin)
  by_contra hn
  have hn1 : 1 < E1.nParam H := not_le.mp hn
  have hns : ¬ Group.IsSolvable ↥H := fun hs => hn (E1.solvable_nParam_le_one hs)
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian hH.1.2
  obtain ⟨⟨K', hK'c, hHK', -, hcases⟩, -⟩ := hE22.exists_cases hmin hSQ hns
  have hlie := Vol2.Ch11.SecB.e22LieCases_of_e22CasesC hn1 hcases
  have hloc := (local_structure_wreath_lie_of h326
    (Ch4.stmt4_4_14Lie_of_steps h443 hC58 h317 h37' h38' h39') hC58 h317 h37' h38' h39' h3228 hyp
    hrow H hH ⟨K', hK'c, hHK', hlie⟩).2
  obtain ⟨n, hn2, hty, hB⟩ := hlie.exists_borel
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have hXGz : ch83X T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    (twoResidual_le _).trans inf_le_right
  have hKzGz : ch83Kz T L z ≤ Subgroup.centralizer ({z} : Set G) := conjClosure_le
    fun h hh x hx => Subgroup.mul_mem _ (Subgroup.mul_mem _ hh (hXGz hx)) (Subgroup.inv_mem _ hh)
  have hHGz : H ≤ Subgroup.centralizer ({z} : Set G) := hHK.trans (sup_le hKzGz hTz)
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
  ·
    have hK'H : K' ≤ H := le_of_mem_cComp hK'c
    have h5 : 5 ∣ Nat.card H :=
      (Ch8310P.five_dvd_card_lie_two hty).trans ((Ch838.card_star_dvd hK'H).trans
        (Subgroup.card_dvd_of_le hK'H))
    rcases halt with ⟨K, s, hsT, hsN, hKC, hKz, p, hp, hp5, hKp⟩ | h4 | h5' | hHe'
    · exact Ch8310X.false_of_case_i h37 h38 h326 hyp hrow hV hN hz2 hzV hsT hsN hKC hKz hp
        hp5 hKp hH hHK hU hK'c hHK' hty hloc
    · exact false_of_case_ii_iii hLn2 hHe hyp.fsu.sylow.1 hyp.fsu.sylow.2 hTz (Or.inl h4)
        hTH hHK hU hnn h5
    · exact false_of_case_ii_iii hLn2 hHe hyp.fsu.sylow.1 hyp.fsu.sylow.2 hTz
        (Or.inr (Or.inl h5')) hTH hHK hU hnn h5
    · exact false_of_case_ii_iii hLn2 hHe hyp.fsu.sylow.1 hyp.fsu.sylow.2 hTz
        (Or.inr (Or.inr hHe')) hTH hHK hU hnn h5
  ·
    obtain ⟨r, hr, hrd, hr2, hr3⟩ := Ch837.exists_prime_dvd_two_pow_sub_one hn3
    obtain ⟨x, ⟨hxM, -⟩, hxo⟩ := Ch837.exists_orderOf_eq_of_isBorelIn hn2 hty hB hr hrd
    exact Ch837.false_of_mem_inf_of_orderOf_prime h326 hyp hrow hV hz2 hzV hloc hxM.1 hxM.2
      (hHGz hxM.1) hr hr2 hr3 hxo

end CFSG.Quasithin.H13

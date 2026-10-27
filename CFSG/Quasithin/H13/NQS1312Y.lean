module

public import CFSG.Quasithin.H13.NQS1312X
public import CFSG.Quasithin.EmptyFaithful.SBc17SL2Syl
public import CFSG.Quasithin.EmptyFaithful.SBc17SL2Coc
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.H13.NQS1312W

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique SBc17
open CFSG.Quasithin.SteinbergCB CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

section SL2

variable {F : Type} [Field F]

theorem fix_conj_upperSub_one {g : SL2 F} {v : Fin 2 → F}
    (h : ((g * uElt 1 * g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec v = v) :
    ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec v 1 = 0 := by
  have h2 : ((g⁻¹ * (g * uElt 1 * g⁻¹) : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec v =
      ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec v := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h]
  have h3 : (g⁻¹ * (g * uElt 1 * g⁻¹) : SL2 F) = uElt 1 * g⁻¹ := by group
  rw [h3, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec] at h2
  set w := ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec v
  have h4 := congrFun h2 0
  simp [uElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h4
  exact h4

theorem eq_zero_of_tElt_fix {a : Fˣ} (ha : a ≠ 1) {w : Fin 2 → F} (hw1 : w 1 = 0)
    (h : ((tElt a : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec w = w) : w = 0 := by
  have h0 := congrFun h 0
  simp [tElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hw1] at h0
  have h1 : ((a : F) - 1) * w 0 = 0 := by
    rw [sub_mul, one_mul, h0, sub_self]
  have hw0 : w 0 = 0 := by
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd (Units.ext (sub_eq_zero.1 h2)) ha
    · exact h2
  ext i
  fin_cases i
  · exact hw0
  · exact hw1

theorem center_sl2_eq_bot [CharP F 2] : Subgroup.center (SL2 F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h2 : (r + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, hr, one_pow, CharTwo.add_self_eq_zero]
    have h3 : r + 1 = 0 := (pow_eq_zero_iff two_ne_zero).1 h2
    rw [← sub_eq_zero, CharTwo.sub_eq_add]
    exact h3
  rw [Subgroup.mem_bot]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [← hrA, hr1]
  simp

end SL2

theorem three_pow_mod_eight (k : ℕ) : 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> simp

theorem exists_prime_dvd_two_pow_sub_one {n : ℕ} (hn : 3 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ n - 1 ∧ r ≠ 2 ∧ r ≠ 3 := by
  have hN8 : (2 ^ n - 1) % 8 = 7 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h8 : 2 ^ (m + 3) = 8 * 2 ^ m := by rw [pow_add]; ring
    have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  obtain ⟨v, m, hm3, hNm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := 2 ^ n - 1)
    (by omega) 3 (by norm_num)
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hNm
    have := three_pow_mod_eight v
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hNm
    omega
  refine ⟨m.minFac, Nat.minFac_prime hm1, ?_, ?_, ?_⟩
  · rw [hNm]
    exact Dvd.dvd.mul_left (Nat.minFac_dvd m) _
  · intro h2
    have h2m : 2 ∣ m := h2 ▸ Nat.minFac_dvd m
    have : 2 ∣ 2 ^ n - 1 := hNm ▸ Dvd.dvd.mul_left h2m _
    omega
  · intro h3
    exact hm3 (h3 ▸ Nat.minFac_dvd m)

theorem charP_two_of_card_line {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) : CharP F 2 := by
  have h2 : ringChar F = 2 := by
    rw [FiniteField.even_card_iff_char_two, hcard]
    simp [Nat.pow_mod, Nat.pos_iff_ne_zero.mp hn]
  rw [← h2]
  exact ringChar.charP F

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem coe_mem_pCoreOf_iff_line (H : Subgroup G) (x : ↥H) :
    (x : G) ∈ pCoreOf 2 H ↔ x ∈ CFSG.pCore 2 ↥H := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem mem_of_isSylowTwoOf_of_mem_normalizer {P X : Subgroup G}
    (hP : IsSylowTwoOf P X) {y : G} (hyX : y ∈ X) (hyP : y ∈ normalizer (P : Set G))
    (hy2 : IsPGroup 2 (zpowers y)) : y ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : IsPGroup 2 (zpowers y ⊔ P : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hy2 hP.2.1 (zpowers_le.2 hyP)
  have h := eq_of_isSylowTwoOf_le hP le_sup_right (sup_le (zpowers_le.2 hyX) hP.1) hsup
  exact h ▸ mem_sup_left (mem_zpowers y)

omit [Finite G] in
theorem tElt_pow {F : Type} [Field F] (a : Fˣ) (k : ℕ) :
    (tElt a : SL2 F) ^ k = tElt (a ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [tElt]
  | succ k ih => rw [pow_succ, ih, SBc17.Coc.tElt_mul, ← pow_succ]

omit [Finite G] in
theorem isSylowTwoOf_autOn {K S V : Subgroup G} (hKV : K ≤ normalizer (V : Set G))
    (hS : IsSylowTwoOf S K) : IsSylowTwoOf (autOn S V) (autOn K V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSK : S ≤ K := hS.1
  set π : ↥K →* MulAut ↥V := (conjAct V).comp (Subgroup.inclusion hKV) with hπ
  have hrange : π.range = autOn K V := by
    ext φ
    rw [SBc17.mem_autOn_iff]
    constructor
    · rintro ⟨⟨k, hk⟩, rfl⟩
      exact ⟨k, hKV hk, hk, rfl⟩
    · rintro ⟨k, hkN, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  set π' : ↥K →* ↥(autOn K V) := π.codRestrict (autOn K V) (fun k => hrange ▸ ⟨k, rfl⟩)
    with hπ'
  have hπs : Function.Surjective π' := by
    rintro ⟨φ, hφ⟩
    rw [← hrange] at hφ
    obtain ⟨k, rfl⟩ := hφ
    exact ⟨k, rfl⟩
  have hmap : (S.subgroupOf K).map π' = (autOn S V).subgroupOf (autOn K V) := by
    ext ⟨φ, hφ⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, SBc17.mem_autOn_iff]
    constructor
    · rintro ⟨⟨k, hk⟩, hkS, hkφ⟩
      refine ⟨k, hKV hk, Subgroup.mem_subgroupOf.1 hkS, ?_⟩
      have := congrArg Subtype.val hkφ
      exact this
    · rintro ⟨k, hkN, hkS, rfl⟩
      exact ⟨⟨k, hSK hkS⟩, Subgroup.mem_subgroupOf.2 hkS, rfl⟩
  refine ⟨fun φ hφ => ?_, ?_, ?_⟩
  · obtain ⟨k, hkN, hkS, rfl⟩ := SBc17.mem_autOn_iff.1 hφ
    exact SBc17.mem_autOn_iff.2 ⟨k, hkN, hSK hkS, rfl⟩
  · have h2 : IsPGroup 2 (S.subgroupOf K) := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
    have h3 := h2.map π'
    rw [hmap] at h3
    exact h3.of_equiv (Subgroup.subgroupOfEquivOfLe (by
      intro φ hφ
      obtain ⟨k, hkN, hkS, rfl⟩ := SBc17.mem_autOn_iff.1 hφ
      exact SBc17.mem_autOn_iff.2 ⟨k, hkN, hSK hkS, rfl⟩))
  · intro h2
    apply hS.2.2
    rw [← hmap] at h2
    exact h2.trans (Subgroup.index_map_dvd _ hπs)

theorem false_of_c27L2_line
    (h1332 : Stmt13_3_2) (hA3 : A3Orbits G) (h38 : A38ForSQTK) {T L V : Subgroup G} {z : G}
    [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k)
    (hΦT : ∀ (t : G) (ht : t ∈ T), ∃ s ∈ S0, linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨t, hF.2.2.2.2.2.2.2.1 ht⟩) = glLin s)
    {K : Subgroup G} (hK : K ∈ cComp (lineH Φ)) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hQK : pCoreOf 2 (L ⊔ T) ≤ normalizer (K : Set G))
    (hC1 : (K ⊔ pCoreOf 2 (L ⊔ T)) ⊓
      centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T))) : Set G) ≤
        pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T)) ⊔ oTwoZIn K)
    (h : SBc17.C27L2 (lineH Φ) (pCoreOf 2 (L ⊔ T)) (lineH Φ ⊓ normalizer (L : Set G)) K
      (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T))))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hV64, hVQ, -, hLV, -, -, -, hTC, -, -⟩ := id hF
  obtain ⟨-, -, -, -, hTI⟩ := u3_selected_local_normalizer_and_TI_of_1332 h1332 hH hF
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  set VK := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hVK
  set Mh := lineH Φ ⊓ normalizer (L : Set G) with hMh
  obtain ⟨-, ⟨n, hn, F, _, _, hcard, α, hα, hker, β, -, hβker, hβ⟩, -, ⟨Sst, hSst, hBor⟩⟩ := h
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQC : Q ≤ centralizer (V : Set G) := hTC ▸ inf_le_right
  have hKV : K ≤ normalizer (VK : Set G) := SBc17.le_normalizer_V K Q
  have hKH : K ≤ lineH Φ := le_of_mem_cComp hK
  have hchar : CharP F 2 := charP_two_of_card_line (by omega) hcard
  have hF2 : (1 : F) + 1 = 0 := one_add_one_eq_zero_of_card_line (by omega) hcard
  have hq4 : 4 ≤ Fintype.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨A₃, hA₃⟩ := exists_orderOf_three_sl2 hF2
  have hK3 : 3 ∣ Nat.card K := three_dvd_card_of_surjective α hα hA₃
  obtain ⟨k₁, hk₁L, x, hxL, hk₁3, hx3, hxk, hk₁τ, hxτ⟩ := exists_e9 hU3 hF hΦLs
  have hk₁H := mem_lineH_of_tau_k (hLV hk₁L) hk₁τ
  obtain ⟨hk₁K, -⟩ := le_normalizer_of_commute_three hA3 h38 (isSQTKIn_lineN hH) lineH_le_lineN
    lineN_le_normalizer_lineH (cComp_mem_of_subnormal isSubnormal_lineH hK) hKH
    hK3 (mem_lineN_of_tau_k2 (hLV hxL) hxτ) (lineH_le_lineN hk₁H) hx3 hk₁3 hxk hk₁H
    (not_mem_lineH_of_tau_k2 (hLV hxL) hxτ)
  have hk₁M : k₁ ∈ Mh ⊓ K := ⟨⟨hk₁H, Subgroup.le_normalizer hk₁L⟩, hk₁K⟩
  have hCK : ∀ y (hy : y ∈ K), y ∈ centralizer (VK : Set G) → y ∈ pCoreOf 2 K := by
    intro y hyK hyC
    have h1 := alpha_eq_one_of_mem_oTwoZIn_of_center center_sl2_eq_bot hα hker
      (SBc17.inf_centralizer_le_oTwoZIn hC1 ⟨hyK, hyC⟩) hyK
    have h2 : (⟨y, hyK⟩ : ↥K) ∈ α.ker := h1
    rw [hker] at h2
    exact (coe_mem_pCoreOf_iff_line K ⟨y, hyK⟩).2 h2
  have hO2p : IsPGroup 2 (pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  obtain ⟨S, hS, hQS, -, hSM, hSQ, hidx⟩ := exists_sylow_lineH h1332 hH hF hΦN
  have hSK : IsSylowTwoOf (S ⊓ K) K :=
    C2Push.isSylowTwoOf_inf_of_isSubnormal (subnormal_of_mem_cComp hK) hS
  have hSMh : S ⊓ K ≤ Mh ⊓ K := fun s hs => ⟨⟨hS.1 hs.1, hSM hs.1⟩, hs.2⟩
  have hO2S : pCoreOf 2 K ≤ S ⊓ K := B6.pCoreOf_two_le_of_isSylowTwoOf hSK
  have hHu : lineH Φ ≤ centralizer ({ptOf Φ (vecOf 15)} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
  have hMhV : Mh ≤ normalizer (V : Set G) := fun y hy =>
    hTI _ (ptOf_mem _) ptOf_fifteen_ne_one ⟨hy.2, hHu hy.1⟩
  have hcen : ∀ y ∈ lineH Φ, y * ptOf Φ (vecOf 15) * y⁻¹ = ptOf Φ (vecOf 15) ∧
      y * ptOf Φ (vecOf 52) * y⁻¹ = ptOf Φ (vecOf 52) := by
    intro y hy
    rw [lineH, mem_centralizer_iff] at hy
    refine ⟨?_, ?_⟩
    · rw [← hy _ (Set.mem_insert _ _)]; group
    · rw [← hy _ (Set.mem_insert_of_mem _ rfl)]; group
  set R : Subgroup G := (Mh ⊓ K) ⊓ ((Sst.comap (conjAct VK)).map (normalizer (VK : Set G)).subtype)
    with hR
  have hmemR : ∀ y (hy : y ∈ Mh ⊓ K), conjAct VK ⟨y, hKV hy.2⟩ ∈ Sst → y ∈ R :=
    fun y hy hyS => ⟨hy, ⟨y, hKV hy.2⟩, hyS, rfl⟩
  have hRS : ∀ y ∈ R, ∃ hy : y ∈ K, conjAct VK ⟨y, hKV hy⟩ ∈ Sst := by
    rintro y ⟨hy, ⟨n, hn⟩, hnS, rfl⟩
    exact ⟨hy.2, hnS⟩
  have hRp : IsPGroup 2 R := by
    rintro ⟨y, hyR⟩
    obtain ⟨hyK, hyS⟩ := hRS y hyR
    obtain ⟨a, ha⟩ := hSst.2.1 ⟨_, hyS⟩
    have ha' : (conjAct VK ⟨y, hKV hyK⟩) ^ 2 ^ a = 1 := congrArg Subtype.val ha
    have hyK' : y ^ 2 ^ a ∈ K := K.pow_mem hyK _
    have h1 : conjAct VK ⟨y ^ 2 ^ a, hKV hyK'⟩ = 1 := by
      rw [← ha', ← map_pow]
      rfl
    obtain ⟨b, hb⟩ := hO2p ⟨_, hCK _ hyK' (A4.conjAct_eq_one_iff.1 h1)⟩
    have hb' : (y ^ 2 ^ a) ^ 2 ^ b = 1 := congrArg Subtype.val hb
    refine ⟨a + b, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, hb']
  have hstarS : ∀ s (hs : s ∈ S ⊓ K), conjAct VK ⟨s, hKV hs.2⟩ ∈ Sst := by
    intro s hs
    have hsA : conjAct VK ⟨s, hKV hs.2⟩ ∈ autOn (Mh ⊓ K) VK :=
      SBc17.mem_autOn_iff.2 ⟨s, hKV hs.2, hSMh hs, rfl⟩
    rw [hBor] at hsA
    obtain ⟨a, ha⟩ := hS.2.1 ⟨s, hs.1⟩
    have ha' : s ^ 2 ^ a = 1 := congrArg Subtype.val ha
    have h2 : IsPGroup 2 (zpowers (conjAct VK ⟨s, hKV hs.2⟩)) := by
      rintro ⟨g, hg⟩
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
      refine ⟨a, Subtype.ext ?_⟩
      have h3 : (conjAct VK ⟨s, hKV hs.2⟩) ^ 2 ^ a = 1 := by
        rw [← map_pow]
        have : (⟨s, hKV hs.2⟩ : normalizer (VK : Set G)) ^ 2 ^ a = 1 := Subtype.ext ha'
        rw [this, map_one]
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3, one_zpow]
    exact mem_of_isSylowTwoOf_of_mem_normalizer hSst hsA.1 hsA.2 h2
  have hSR : S ⊓ K ≤ R := fun s hs => hmemR s (hSMh hs) (hstarS s hs)
  have hk₁A : conjAct VK ⟨k₁, hKV hk₁K⟩ ∈ autOn (Mh ⊓ K) VK :=
    SBc17.mem_autOn_iff.2 ⟨k₁, hKV hk₁K, hk₁M, rfl⟩
  rw [hBor] at hk₁A
  have hkR : ∀ r ∈ R, k₁ * r * k₁⁻¹ ∈ R := by
    intro r hr
    obtain ⟨hrK, hrS⟩ := hRS r hr
    have hrM : r ∈ Mh ⊓ K := hr.1
    have hm : k₁ * r * k₁⁻¹ ∈ Mh ⊓ K := (Mh ⊓ K).mul_mem ((Mh ⊓ K).mul_mem hk₁M hrM)
      ((Mh ⊓ K).inv_mem hk₁M)
    refine hmemR _ hm ?_
    have e : (⟨k₁ * r * k₁⁻¹, hKV hm.2⟩ : normalizer (VK : Set G)) =
        ⟨k₁, hKV hk₁K⟩ * ⟨r, hKV hrK⟩ * ⟨k₁, hKV hk₁K⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.1 hk₁A.2 _).1 hrS
  have hRV : R ≤ centralizer (V : Set G) :=
    le_centralizer_of_isPGroup hΦN (hLV hk₁L) hk₁τ hRp (fun r hr => hMhV hr.1.1)
      (fun r hr => hcen r hr.1.1.1) hkR
  have hSKQ : S ⊓ K ≤ Q := fun s hs => by
    have h1 : s ∈ S ⊓ centralizer (V : Set G) := ⟨hs.1, hRV (hSR hs)⟩
    rw [hSQ] at h1
    exact h1
  have hyp : HypC23 (lineH Φ) Q (lineH Φ ⊓ normalizer (L : Set G)) :=
    hypC23_line h1332 hH hF hΦLs hΦN
  have hKc : CharTwo K :=
    charTwo_of_isSubnormal_line (subnormal_of_mem_cComp hK) (charTwo_lineH hH hF hΦT)
  have hKQc : CharTwo (K ⊔ Q) := Vol2Native.L239.charTwo_sup_of_le_normalizer hKc hQp hQK
  have hO : pCoreOf 2 (K ⊔ Q) ≤ Q :=
    c2_1_pCore_le (C2Push.isTwoRadicalIn_sup_of_le_normalizer hyp.radical hK hq hQK)
  have hVO := inf_le_pCoreOf_of_pCoreOf_le hKQc hO hVQ hQC
  have hU : ∀ c ∈ lperpList, ptOf Φ (vecOf c) ∈ blockU K := fun c hc =>
    ptOf_lperp_mem_blockU hk₁K (hLV hk₁L) hk₁τ (hVQ.trans hQK) hVO hc
  set P := ((S ⊓ K).subgroupOf K).map α with hP
  have hP2 : IsPGroup 2 P := (hSK.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSK.1).symm).map α
  obtain ⟨g, hg⟩ := exists_conj_upperSub hq4 hP2 (not_two_dvd_index_map hSK hα)
  set v : ℕ → Fin 2 → F := fun c => if hc : c ∈ lperpList then
    Multiplicative.toAdd (β ⟨ptOf Φ (vecOf c), hU c hc⟩) else 0 with hv
  have hvc : ∀ c (hc : c ∈ lperpList), v c = Multiplicative.toAdd (β ⟨ptOf Φ (vecOf c), hU c hc⟩) :=
    fun c hc => by simp only [hv, hc, ↓reduceDIte]
  have hvinj : ∀ c ∈ lperpList, ∀ c' ∈ lperpList, v c = v c' → c = c' := by
    intro c hc c' hc' hcc
    rw [hvc c hc, hvc c' hc'] at hcc
    have h1 : β ⟨ptOf Φ (vecOf c), hU c hc⟩ = β ⟨ptOf Φ (vecOf c'), hU c' hc'⟩ :=
      Multiplicative.toAdd.injective hcc
    have h2 : (⟨ptOf Φ (vecOf c), hU c hc⟩ : ↥(blockU K))⁻¹ * ⟨ptOf Φ (vecOf c'), hU c' hc'⟩ ∈
        β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    rw [hβker, Subgroup.mem_subgroupOf] at h2
    exact lperp_eq_of_mem_centralizer hk₁K (hLV hk₁L) hk₁τ hc hc' h2.2
  have hfix : ∀ (y : G) (hyK : y ∈ K), y ∈ centralizer (V : Set G) → ∀ c (hc : c ∈ lperpList),
      ((α ⟨y, hyK⟩ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec (v c) = v c := by
    intro y hyK hyC c hc
    have hc' : y * ptOf Φ (vecOf c) * y⁻¹ = ptOf Φ (vecOf c) := by
      rw [← (mem_centralizer_iff.1 hyC) _ (ptOf_mem _)]
      group
    rw [hvc c hc]
    exact (hβ ⟨y, hyK⟩ ⟨ptOf Φ (vecOf c), hU c hc⟩ ⟨ptOf Φ (vecOf c), hU c hc⟩ hc'.symm).symm
  have hline : ∀ c ∈ lperpList,
      ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec (v c) 1 = 0 := by
    intro c hc
    have hmem : g * uElt 1 * g⁻¹ ∈ P := by
      rw [hg]
      have : g⁻¹ * (g * uElt 1 * g⁻¹) * g = uElt 1 := by group
      rw [this, mem_upperSub_iff]
      exact ⟨1, rfl⟩
    obtain ⟨⟨y, hyK⟩, hy, hyα⟩ := Subgroup.mem_map.1 hmem
    have hyS : y ∈ S ⊓ K := Subgroup.mem_subgroupOf.1 hy
    have h1 := hfix y hyK (hQC (hSKQ hyS)) c hc
    rw [hyα] at h1
    exact fix_conj_upperSub_one h1
  have h16 : 16 ≤ Fintype.card F := by
    let f : ℕ → F := fun c => ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec (v c) 0
    have hinj : Set.InjOn f lperpList.toFinset := by
      intro c hc c' hc' hcc
      rw [Finset.mem_coe, List.mem_toFinset] at hc hc'
      apply hvinj c hc c' hc'
      have h1 : ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec (v c) =
          ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec (v c') := by
        ext i
        fin_cases i
        · exact hcc
        · simp only [Fin.mk_one, Fin.isValue]
          rw [hline c hc, hline c' hc']
      have h3 : ∀ w : Fin 2 → F, ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec
          (((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec w) = w := by
        intro w
        rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
      rw [← h3 (v c), ← h3 (v c'), h1]
    have h1 := Finset.card_le_card_of_injOn f (fun c _ => Finset.mem_univ (f c)) hinj
    rwa [List.toFinset_card_of_nodup lperp_spec.2.2.2.1, lperp_spec.2.2.2.2,
      Finset.card_univ] at h1
  have hn3 : 3 ≤ n := by
    by_contra hn3
    have : n ≤ 2 := by omega
    have h4 : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    rw [hcard] at h16
    omega
  obtain ⟨r, hr, hrN, hr2, hr3⟩ := exists_prime_dvd_two_pow_sub_one hn3
  have : Fact r.Prime := ⟨hr⟩
  have hcardU : Nat.card Fˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hcard]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' r (hcardU ▸ hrN)
  obtain ⟨y, hyα⟩ := hα (g * tElt a * g⁻¹)
  have hαP : ∀ p ∈ P, α y * p * (α y)⁻¹ ∈ P := by
    intro p hp
    rw [hg] at hp ⊢
    have e : g⁻¹ * (α y * p * (α y)⁻¹) * g = tElt a * (g⁻¹ * p * g) * (tElt a)⁻¹ := by
      rw [hyα]
      group
    rw [e]
    exact (mem_normalizer_iff.1 (borelSub_le_normalizer_upperSub (SBc17.Coc.tElt_mem_borelSub a))
      _).1 hp
  have hyN : (y : G) ∈ normalizer ((S ⊓ K : Subgroup G) : Set G) := by
    refine mem_normalizer_of_map_le ?_
    rintro _ ⟨s, hs, rfl⟩
    change (y : G) * s * (y : G)⁻¹ ∈ S ⊓ K
    have hsK : s ∈ K := hs.2
    have hysK : (y : G) * s * (y : G)⁻¹ ∈ K := K.mul_mem (K.mul_mem y.2 hsK) (K.inv_mem y.2)
    have hmem : α ⟨(y : G) * s * (y : G)⁻¹, hysK⟩ ∈ P := by
      have e : (⟨(y : G) * s * (y : G)⁻¹, hysK⟩ : ↥K) = y * ⟨s, hsK⟩ * y⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact hαP _ ⟨⟨s, hsK⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    obtain ⟨⟨s', hs'K⟩, hs', hs'α⟩ := Subgroup.mem_map.1 hmem
    have hk : (⟨s', hs'K⟩ : ↥K)⁻¹ * ⟨(y : G) * s * (y : G)⁻¹, hysK⟩ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs'α, inv_mul_cancel]
    rw [hker] at hk
    have hk' := hO2S ((coe_mem_pCoreOf_iff_line K _).2 hk)
    have e2 : (y : G) * s * (y : G)⁻¹ = s' * (s'⁻¹ * ((y : G) * s * (y : G)⁻¹)) := by group
    rw [e2]
    exact (S ⊓ K).mul_mem (Subgroup.mem_subgroupOf.1 hs') hk'
  have hSst : Sst = autOn (S ⊓ K) VK :=
    eq_of_isSylowTwoOf_le (isSylowTwoOf_autOn hKV hSK) (fun φ hφ => by
      obtain ⟨s, hsN, hs, rfl⟩ := SBc17.mem_autOn_iff.1 hφ
      exact hstarS s hs) hSst.1 hSst.2.1
  have hyA : conjAct VK ⟨y, hKV y.2⟩ ∈ autOn (Mh ⊓ K) VK := by
    rw [hBor]
    refine ⟨SBc17.mem_autOn_iff.2 ⟨y, hKV y.2, y.2, rfl⟩, mem_normalizer_iff.2 fun φ => ?_⟩
    rw [hSst]
    constructor
    · intro hφ
      obtain ⟨s, hsN, hs, rfl⟩ := SBc17.mem_autOn_iff.1 hφ
      have hys : (y : G) * s * (y : G)⁻¹ ∈ S ⊓ K := (mem_normalizer_iff.1 hyN s).1 hs
      refine SBc17.mem_autOn_iff.2 ⟨_, hKV hys.2, hys, ?_⟩
      have e : (⟨(y : G) * s * (y : G)⁻¹, hKV hys.2⟩ : normalizer (VK : Set G)) =
          ⟨y, hKV y.2⟩ * ⟨s, hsN⟩ * ⟨y, hKV y.2⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
    · intro hφ
      obtain ⟨s, hsN, hs, hsφ⟩ := SBc17.mem_autOn_iff.1 hφ
      have hys : (y : G)⁻¹ * s * (y : G) ∈ S ⊓ K := by
        have := (mem_normalizer_iff.1 hyN ((y : G)⁻¹ * s * (y : G))).2
        apply this
        simpa [mul_assoc] using hs
      refine SBc17.mem_autOn_iff.2 ⟨_, hKV hys.2, hys, ?_⟩
      have e : (⟨(y : G)⁻¹ * s * (y : G), hKV hys.2⟩ : normalizer (VK : Set G)) =
          ⟨y, hKV y.2⟩⁻¹ * ⟨s, hsN⟩ * ⟨y, hKV y.2⟩ := rfl
      rw [e, map_mul, map_mul, map_inv, hsφ]
      group
  obtain ⟨m, hmN, hmM, hmy⟩ := SBc17.mem_autOn_iff.1 hyA
  have hyM : (y : G) ∈ Mh ⊓ K := by
    have hmy' : conjAct VK ⟨m⁻¹ * y, hKV (K.mul_mem (K.inv_mem hmM.2) y.2)⟩ = 1 := by
      have e : (⟨m⁻¹ * y, hKV (K.mul_mem (K.inv_mem hmM.2) y.2)⟩ : normalizer (VK : Set G)) =
          ⟨m, hmN⟩⁻¹ * ⟨y, hKV y.2⟩ := rfl
      rw [e, map_mul, map_inv, hmy, inv_mul_cancel]
    have h1 := hO2S (hCK _ (K.mul_mem (K.inv_mem hmM.2) y.2) (A4.conjAct_eq_one_iff.1 hmy'))
    have e : (y : G) = m * (m⁻¹ * y) := by group
    rw [e]
    exact (Mh ⊓ K).mul_mem hmM (hSMh h1)
  have hαyr : α y ^ r = 1 := by
    rw [hyα]
    have e : (g * tElt a * g⁻¹) ^ r = g * (tElt a) ^ r * g⁻¹ := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← map_pow]
    rw [e, tElt_pow, ← ha, pow_orderOf_eq_one]
    have h1 : (tElt (1 : Fˣ) : SL2 F) = 1 := by rw [← pow_zero (tElt a), tElt_pow, pow_zero]
    rw [h1, mul_one, mul_inv_cancel]
  have hyr : ((y : G) ^ r) ∈ pCoreOf 2 K := by
    have hk : y ^ r ∈ α.ker := by rw [MonoidHom.mem_ker, map_pow, hαyr]
    rw [hker] at hk
    exact (coe_mem_pCoreOf_iff_line K _).2 hk
  obtain ⟨j, hj⟩ := hO2p ⟨_, hyr⟩
  have hj' : ((y : G) ^ r) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  set d : G := (y : G) ^ 2 ^ j with hd
  have hdM : d ∈ Mh ⊓ K := (Mh ⊓ K).pow_mem hyM _
  have hdr : d ^ r = 1 := by
    rw [hd, ← pow_mul, mul_comm, pow_mul, hj']
  have hdV : d ∈ centralizer (V : Set G) := by
    obtain ⟨κ, -, hκ, e, he, hκe⟩ := exists_c6List_of_centralizes hΦN (hMhV hdM.1)
      (hcen d hdM.1.1).1 (hcen d hdM.1.1).2
    have hτ : tau Φ ⟨d, hMhV hdM.1⟩ = κ := tau_eq_iff.2 hκ
    have hκr : κ ^ r = 1 := by
      rw [← hτ, ← map_pow]
      have : (⟨d, hMhV hdM.1⟩ : normalizer (V : Set G)) ^ r = 1 := Subtype.ext hdr
      rw [this, map_one]
    have hκ1 : κ = 1 := by
      rcases c6List_cases' e he with rfl | ⟨h3, -⟩ | ⟨h2, -⟩
      · exact Units.ext (by rw [hκe, colMat_id6, Units.val_one])
      · have hκ3 : κ ^ 3 = 1 := Units.ext (by
          rw [Units.val_pow_eq_pow_val, hκe, pow_three, ← colMat_mul6, ← colMat_mul6, h3,
            colMat_id6, Units.val_one])
        have hcop : Nat.gcd r 3 = 1 := (Nat.coprime_primes hr Nat.prime_three).2 hr3
        have := (pow_gcd_eq_one (a := κ) (m := r) (n := 3)).2 ⟨hκr, hκ3⟩
        rwa [hcop, pow_one] at this
      · have hκ2 : κ ^ 2 = 1 := Units.ext (by
          rw [Units.val_pow_eq_pow_val, hκe, pow_two, ← colMat_mul6, h2, colMat_id6,
            Units.val_one])
        have hcop : Nat.gcd r 2 = 1 := (Nat.coprime_primes hr Nat.prime_two).2 hr2
        have := (pow_gcd_eq_one (a := κ) (m := r) (n := 2)).2 ⟨hκr, hκ2⟩
        rwa [hcop, pow_one] at this
    rw [hκ1] at hτ
    exact mem_centralizer_of_tau (hMhV hdM.1) hτ
  have ha' : a ^ 2 ^ j ≠ 1 := by
    intro h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [ha] at h2
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2)
    exact hr2 this
  have hαd : α ⟨d, hdM.2⟩ = g * tElt (a ^ 2 ^ j) * g⁻¹ := by
    have e : (⟨d, hdM.2⟩ : ↥K) = y ^ 2 ^ j := rfl
    rw [e, map_pow, hyα, ← tElt_pow, ← MulAut.conj_apply, ← MulAut.conj_apply, ← map_pow]
  have h3 : ∀ w : Fin 2 → F, ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec
      (((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hzero : ∀ c ∈ lperpList, v c = 0 := by
    intro c hc
    have h1 := hfix d hdM.2 hdV c hc
    rw [hαd] at h1
    have h2 : ((tElt (a ^ 2 ^ j) : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec
        (((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec (v c)) =
        ((g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F).mulVec (v c) := by
      have e : (tElt (a ^ 2 ^ j) : SL2 F) * g⁻¹ = g⁻¹ * (g * tElt (a ^ 2 ^ j) * g⁻¹) := by
        generalize (tElt (a ^ 2 ^ j) : SL2 F) = t'
        group
      conv_rhs => rw [← h1]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, e]
    have h4 := eq_zero_of_tElt_fix ha' (hline c hc) h2
    rw [← h3 (v c), h4, Matrix.mulVec_zero]
  have h04 := hvinj 0 (by decide) 4 (by decide)
    ((hzero 0 (by decide)).trans (hzero 4 (by decide)).symm)
  omega

end CFSG.Quasithin.H13.U3.NLine

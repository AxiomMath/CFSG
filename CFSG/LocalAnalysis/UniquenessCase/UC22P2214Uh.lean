module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Ug
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p2214_six_faith (D : Data G) (Ch : Choice2011 G)
    (h17 : S21_17 D Ch) (hn : SpU3NotList D) (hV : S22_V D Ch)
    (h8 : S22_8 D Ch) (hSg : UC6S846.SigmaStd D) (h1930 : H1930 D) (c : Ctx22b D Ch)
    (hc6 : c.n = 6) {p : ℕ} (hp : p ∈ D.sig) {K : Subgroup G} (hKC : K ∈ calC D.M) {n : ℕ}
    (hpre : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] ∨
      (IsSz ↥(mbarImage D.M c.V K) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)]))
    (hcl : (IsSp4 ↥(mbarImage D.M c.V K) n ∧ Odd n) ∨
      (IsSU3 ↥(mbarImage D.M c.V K) n ∧ n ≡ 1 [MOD 6]) ∨
      ((IsL2 ↥(mbarImage D.M c.V K) n ∨ IsSz ↥(mbarImage D.M c.V K) n) ∧
        (conjSetOf D.M K).ncard = 2))
    (hfaith : ∀ b ∈ c.B0, b ≠ 1 →
      ∃ K' ∈ conjSetOf D.M K, ∃ k ∈ K', b * k * b⁻¹ * k⁻¹ ∉ centralizer (c.V : Set G)) :
    c.n ≤ n := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [hc6]
  by_contra hlt
  push Not at hlt
  obtain ⟨hKV, hq, hshape, hfix, -⟩ := uc22p2214_case_data D Ch h17 hn hV h1930 c hKC hcl
  have hn1 : 1 ≤ n := uc22p2214_one_le_of_shape hshape
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hKC.1
  have h7 : 7 ∈ piSet c.B0 := by
    rw [c.hpi, hc6]
    exact ⟨by norm_num, by norm_num⟩
  have h3 : 3 ∈ piSet c.B0 := by
    rw [c.hpi, hc6]
    exact ⟨Nat.prime_three, by norm_num⟩
  obtain ⟨a₇, ha₇, ha₇o⟩ := uc22p22i_exists_elt_of_mem_piSet h7
  obtain ⟨a₃, ha₃, ha₃o⟩ := uc22p22i_exists_elt_of_mem_piSet h3
  obtain ⟨Y, _, _, ⟨e⟩, S, hS, h7N⟩ := uc22p2214_borel_of_elt_faith D Ch hV h1930 c hKC
    hKV hshape hfix hfaith ha₇ (by norm_num) ha₇o (by omega) (by norm_num)
  have h7n : 7 ∣ 2 ^ n - 1 := by
    rcases hcl with ⟨hsp, -⟩ | ⟨hsu, hmod⟩ | ⟨hL | hSz, -⟩
    · haveI := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hsp
      obtain ⟨e'⟩ := uc22p2214_quotCenter_of_simple hq
      exact uc22p2214_borel_prime_Sp4
        (CFSG.Blueprint.LieModel.of_mulEquiv (e'.trans e.symm) hsp) hS (by norm_num)
        (by norm_num) h7N
    · exfalso
      have h2 := uc22p22a_two_le_of_isU3 hsu.2
      have h6 : n % 6 = 1 := hmod
      omega
    · haveI := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
      obtain ⟨e'⟩ := uc22p2214_quotCenter_of_simple hq
      exact uc22p2214_borel_prime_L2
        (CFSG.Blueprint.LieModel.of_mulEquiv (e'.trans e.symm) hL) hS (by norm_num)
        (by norm_num) h7N
    · haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
      obtain ⟨e'⟩ := uc22p2214_quotCenter_of_simple hq
      exact uc22p2214_borel_prime_Sz
        (CFSG.Blueprint.LieModel.of_mulEquiv (e'.trans e.symm) hSz) hS (by norm_num)
        (by norm_num) h7N
  have hn3 : n = 3 := by
    interval_cases n <;> first | rfl | (exfalso; norm_num at h7n)
  subst hn3
  have hp3 : p ≠ 3 := fun h => uc22p2214_not_mem_piSet D Ch h8 hSg h1930 c hp (h ▸ h3)
  have hSz8 : IsSz ↥(mbarImage D.M c.V K) 3 := by
    rcases hpre with h | ⟨h, -⟩
    · exfalso
      have h9 : (p : ℤ) ∣ 9 := by
        have := Int.ModEq.dvd h
        have e9 : (-1 : ℤ) - 2 ^ 3 = -9 := by norm_num
        rw [e9] at this
        exact (Int.dvd_neg).1 this
      have h9' : p ∣ 3 ^ 2 := by exact_mod_cast h9
      exact hp3 ((Nat.prime_dvd_prime_iff_eq (D.sig_prime p hp).1 Nat.prime_three).1
        ((D.sig_prime p hp).1.dvd_of_dvd_pow h9'))
    · exact h
  have hno3 := CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz8
  have hc2 : (conjSetOf D.M K).ncard = 2 := by
    rcases hcl with ⟨hsp, -⟩ | ⟨-, hmod⟩ | ⟨-, hc2⟩
    · exact absurd (uc22p2214_three_dvd_card_sp4 hsp) hno3
    · exfalso
      have h6 : 3 % 6 = 1 := hmod
      omega
    · exact hc2
  obtain ⟨-, hB0c, -, -, -, -, -, -, -, hperm, -⟩ := c.hB0
  have hTp : IsPGroup 2 D.T := (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).2.1
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hTK : ¬ D.T ≤ normalizer (K : Set G) := fun h =>
    uc22p22a_not_two_dvd_ncard D.sylowM h ⟨1, by omega⟩
  have h7p : IsPGroup 7 ↥(zpowers (⟨a₇, ha₇⟩ : ↥c.B0)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ha₇o, pow_one])
  obtain ⟨Q₇, hQ₇⟩ := h7p.exists_le_sylow
  set A : Subgroup G := (Q₇ : Subgroup ↥c.B0).map c.B0.subtype with hAdef
  have hA : CFSG.ABGLocalTools.IsSylowOf 7 A c.B0 := ⟨Q₇, rfl⟩
  have ha₇A : a₇ ∈ A := ⟨⟨a₇, ha₇⟩, hQ₇ (mem_zpowers _), rfl⟩
  obtain ⟨x, hxM, hxK, hxA⟩ := uc22p2214_swap (by norm_num) hc2 c.hBM hTM
    (hfix K ⟨1, D.M.one_mem, by ext; simp⟩) (uc22p2214_odd_card_B0 D c) hperm hTp hTK hA
  have ha₃1 : a₃ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha₃o
    omega
  have ha₇1 : a₇ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha₇o
    omega
  obtain ⟨Ki, hKi, k, hk, hkV⟩ := hfaith a₃ ha₃ ha₃1
  obtain ⟨Kj, hKj, k', hk', hk'V⟩ := hfaith a₇ ha₇ ha₇1
  obtain ⟨a', ha'B, ha'o, k'', hk''Ki, hk''V⟩ : ∃ a' ∈ c.B0, orderOf a' = 7 ∧
      ∃ k'' ∈ Ki, a' * k'' * a'⁻¹ * k''⁻¹ ∉ centralizer (c.V : Set G) := by
    by_cases hij : Kj = Ki
    · exact ⟨a₇, ha₇, ha₇o, k', hij ▸ hk', hk'V⟩
    · have hc2j : (conjSetOf D.M Kj).ncard = 2 := by
        rw [uc22p2214_conjSetOf_eq hKj]
        exact hc2
      have hKKj : K ∈ conjSetOf D.M Kj := by
        rw [uc22p2214_conjSetOf_eq hKj]
        exact ⟨1, D.M.one_mem, by ext; simp⟩
      have hxKj : Kj.map (MulAut.conj x).toMonoidHom ≠ Kj := fun h =>
        hxK (uc22p2214_normalizes_of_pair hc2j hKKj hxM
          (Subgroup.mem_normalizer_iff_map_conj_eq.2 h))
      have hpair := uc22p22d_conjSet_pair hxM hxKj hc2j
      have hKij : Ki ∈ conjSetOf D.M Kj := by
        rw [uc22p2214_conjSetOf_eq hKj]
        exact hKi
      rw [hpair] at hKij
      have hmap : Kj.map (MulAut.conj x).toMonoidHom = Ki := by
        rcases hKij with h | h
        · exact absurd h.symm hij
        · exact h.symm
      refine ⟨x * a₇ * x⁻¹, hA.le ((mem_normalizer_iff.1 hxA a₇).1 ha₇A), ?_, x * k' * x⁻¹, ?_,
        ?_⟩
      · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ha₇o]
      · rw [← hmap]
        exact ⟨k', hk', rfl⟩
      · intro hc
        apply hk'V
        have e1 : x * a₇ * x⁻¹ * (x * k' * x⁻¹) * (x * a₇ * x⁻¹)⁻¹ * (x * k' * x⁻¹)⁻¹ =
            x * (a₇ * k' * a₇⁻¹ * k'⁻¹) * x⁻¹ := by group
        rw [e1] at hc
        rw [mem_centralizer_iff] at hc ⊢
        intro v hv
        have hxv : x * v * x⁻¹ ∈ c.V := (mem_normalizer_iff.1 (c.hVM hxM) v).1 hv
        have h1 := hc _ hxv
        have h2 : x * (v * (a₇ * k' * a₇⁻¹ * k'⁻¹)) * x⁻¹ =
            x * ((a₇ * k' * a₇⁻¹ * k'⁻¹) * v) * x⁻¹ := by
          calc x * (v * (a₇ * k' * a₇⁻¹ * k'⁻¹)) * x⁻¹ =
                x * v * x⁻¹ * (x * (a₇ * k' * a₇⁻¹ * k'⁻¹) * x⁻¹) := by group
            _ = x * (a₇ * k' * a₇⁻¹ * k'⁻¹) * x⁻¹ * (x * v * x⁻¹) := h1
            _ = x * ((a₇ * k' * a₇⁻¹ * k'⁻¹) * v) * x⁻¹ := by group
        simpa using h2
  have hred : TwoReduced D.M c.V := (hV h1930 c).1.2.2
  have hO2 : CFSG.pCore 2 (MBar D.M c.V) = ⊥ := (uc22br4_pCore_bot_iff D.M c.V c.hVM).2 hred
  have hKiC := uc22p2214_calC_of_mem_conjSetOf hKC hKi
  have hKiV := uc22p2214_not_le_centralizer_of_mem_conjSetOf c.hVM hKV hKi
  have hcompi := uc22br4_isComponentOf_mbarImage D.M c.V Ki c.hVM hO2 hKiC hKiV
  have hfixi := hfix Ki hKi
  have hSzi : IsSz (↥(mbarImage D.M c.V Ki) ⧸ center ↥(mbarImage D.M c.V Ki)) 3 := by
    haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz8
    obtain ⟨e₁⟩ := uc22p2214_quotCenter_of_simple hq
    obtain ⟨g, hg, rfl⟩ := hKi
    obtain ⟨e₂⟩ := uc22p2214_quotCenter_conj D.M c.V K hg
    exact CFSG.Blueprint.LieModel.of_mulEquiv (e₁.trans e₂) hSz8
  have ha₃M : a₃ ∈ D.M := c.hBM ha₃
  have ha'M : a' ∈ D.M := c.hBM ha'B
  have hkM : k ∈ D.M := uc22p22a_le_of_isSubnormal hKiC.1 hk
  have hk''M : k'' ∈ D.M := uc22p22a_le_of_isSubnormal hKiC.1 hk''Ki
  have ha₃N := uc22p2214_mk_mem_normalizer (V := c.V) ha₃M (hfixi ha₃)
  have ha'N := uc22p2214_mk_mem_normalizer (V := c.V) ha'M (hfixi ha'B)
  have hnt : ∀ {b l : G} (hbM : b ∈ D.M) (hlM : l ∈ D.M), l ∈ Ki →
      b * l * b⁻¹ * l⁻¹ ∉ centralizer (c.V : Set G) →
      ∃ kb ∈ mbarImage D.M c.V Ki, (QuotientGroup.mk ⟨b, hbM⟩ : MBar D.M c.V) * kb *
        (QuotientGroup.mk ⟨b, hbM⟩)⁻¹ * kb⁻¹ ≠ 1 := by
    intro b l hbM hlM hl hblV
    refine ⟨QuotientGroup.mk ⟨l, hlM⟩, uc22p2214_mem_mbarImage hlM hl, fun h1 => hblV ?_⟩
    have h2 : (QuotientGroup.mk (⟨b, hbM⟩ * ⟨l, hlM⟩ * ⟨b, hbM⟩⁻¹ * ⟨l, hlM⟩⁻¹ : ↥D.M) :
        MBar D.M c.V) = 1 := by
      rw [← h1]
      rfl
    exact (uc22br_gt_mk_eq_one_iff c.hVM _).1 h2
  set ψ := uc22p2214_autQuot (mbarImage D.M c.V Ki) with hψ
  set α₃ := ψ ⟨_, ha₃N⟩ with hα₃
  set α' := ψ ⟨_, ha'N⟩ with hα'
  have hα₃1 : α₃ ≠ 1 := uc22p2214_autQuot_ne_one hcompi.2.2 ha₃N (hnt ha₃M hkM hk hkV)
  have hα'1 : α' ≠ 1 := uc22p2214_autQuot_ne_one hcompi.2.2 ha'N (hnt ha'M hk''M hk''Ki hk''V)
  have hpow : ∀ {b : G} (hbM : b ∈ D.M) (hbN : (QuotientGroup.mk ⟨b, hbM⟩ : MBar D.M c.V) ∈
      normalizer (mbarImage D.M c.V Ki : Set (MBar D.M c.V))) {m : ℕ}, b ^ m = 1 →
      ψ ⟨_, hbN⟩ ^ m = 1 := by
    intro b hbM hbN m hbm
    rw [← map_pow]
    have h1 : (⟨_, hbN⟩ : ↥(normalizer (mbarImage D.M c.V Ki : Set (MBar D.M c.V)))) ^ m = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← QuotientGroup.mk_pow]
      have h2 : (⟨b, hbM⟩ : ↥D.M) ^ m = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hbm)
      rw [h2, QuotientGroup.mk_one]
      rfl
    rw [h1, map_one]
  have hα₃3 : α₃ ^ 3 = 1 := hpow ha₃M ha₃N (by rw [← ha₃o, pow_orderOf_eq_one])
  have hα'7 : α' ^ 7 = 1 := hpow ha'M ha'N (by rw [← ha'o, pow_orderOf_eq_one])
  obtain ⟨y, hy⟩ := uc22p2214_inner_of_prime_Sz hSzi (r := 7) (by norm_num) (by norm_num) hα'7
  have hα'o : orderOf α' = 7 := orderOf_eq_prime hα'7 hα'1
  have hyo : orderOf y = 7 := by
    rw [← orderOf_injective _ (uc22p2214_conj_injective hcompi.2.2) y, hy, hα'o]
  have hcomm : α₃ * α' = α' * α₃ := by
    rw [hα₃, hα', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (QuotientGroup.mk ⟨a₃, ha₃M⟩ : MBar D.M c.V) * QuotientGroup.mk ⟨a', ha'M⟩ =
      QuotientGroup.mk ⟨a', ha'M⟩ * QuotientGroup.mk ⟨a₃, ha₃M⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have h := congrArg (fun z : ↥c.B0 => (z : G)) (hB0c.is_comm.comm ⟨a₃, ha₃⟩ ⟨a', ha'B⟩)
    exact h
  have hfixy : α₃ y = y := by
    apply uc22p2214_conj_injective hcompi.2.2
    rw [← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, hy, hcomm, mul_inv_cancel_right]
  exact hα₃1 (uc22p2214_sz8_fix hSzi hα₃3 hyo hfixy)

end CFSG.LocalAnalysis.UniquenessCase.UC22

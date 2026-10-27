module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenB8Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySeven
public import CFSG.GroupTheory.ZpowersSupExponent
public import CFSG.Quasithin.Recognition.WBN.Statement
public import CFSG.GroupTheory.TwoReflections
public import CFSG.Timmesfeld.Orders.BangNotDvd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem zpowers_sup_le_bigB {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    {K : Subgroup G} {a b : G} (haK : a ∈ K)
    (haT : a ∈ Subgroup.normalizer (D.T : Set G)) (hbB0 : b ∈ c.B0) :
    Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ CFSG.Quasithin.bigB K c.L D.T := by
  have haNK : a ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer haK
  have haNTK : a ∈ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨haT, haNK⟩
  have haBK : a ∈ CFSG.Quasithin.borelOf K D.T := Subgroup.mem_inf.mpr ⟨haK, haNTK⟩
  have hbBL : b ∈ CFSG.Quasithin.borelOf c.L D.T :=
    Ctx23L.B0_le_borelOf_L D Ch h4 h23 h1930 c hbB0
  exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left
    (Subgroup.mem_sup_left haBK))) (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left
      (Subgroup.mem_sup_right hbBL)))

private theorem pow_exp_eq_one_of_mem {D : Data G} {a b : G} {r : ℕ}
    (hpow : ∀ e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b, e ^ r = 1)
    {f₁ : ℕ} (hrf₁ : r ∣ 2 ^ f₁ - 1) (hrn : r ∣ 2 ^ CFSG.Open.pRank 2 D.Z - 1) :
    ∀ e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b,
      e ^ (2 ^ f₁ - 1) = 1 ∧ e ^ (2 ^ CFSG.Open.pRank 2 D.Z - 1) = 1 := by
  intro e he
  constructor
  · obtain ⟨t, ht⟩ := hrf₁
    rw [ht, pow_mul, hpow e he, one_pow]
  · obtain ⟨t, ht⟩ := hrn
    rw [ht, pow_mul, hpow e he, one_pow]

private theorem false_of_wbn_inversion {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h54 : S23_5_4 D Ch)
    (h847 : R847ThinCZ D)
    {K : Subgroup G} (hK : K ∈ calC D.M) {f₁ : ℕ}
    (hKf : IsL2 (Bar2 K) f₁ ∨ IsSz (Bar2 K) f₁)
    {a b : G} (haK : a ∈ K) (hbB0 : b ∈ c.B0) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (har : orderOf a = r) (hbr : orderOf b = r) (hb1 : b ≠ 1)
    {w : G} (hinv : ∀ e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b, w * e * w⁻¹ = e⁻¹) :
    False := by
  have hnorm : w ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
    CFSG.GroupTheory.mem_normalizer_zpowers_of_inv
      (hinv a (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)))
  have hwM : w ∈ D.M :=
    Ctx23L.normalizer_zpowers_le_M c h1930 h4 h847 hK hKf haK hr hr2 har hnorm
  have hinvB : InvertedIn D.M (Subgroup.zpowers b) :=
    ⟨w, hwM, fun y hy => hinv y (Subgroup.mem_sup_right hy)⟩
  have hbZ : b ∉ Subgroup.centralizer (D.Z : Set G) :=
    Ctx23L.not_mem_centralizer_Z_of_mem_B0 D Ch h4 h23 h1930 c hbB0 hb1
  let c₀ : Ctx23L D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  exact (h54 h1930 c₀ b hbB0 hbZ).1 hinvB

private theorem false_of_wbn_centralizer {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKCZ : K ≤ Subgroup.centralizer (D.Z : Set G))
    (hC : CFSG.Open.pCoreOf 2 (K ⊔ CFSG.Quasithin.bigB K c.L D.T) ⊓
      Subgroup.centralizer (K : Set G) = ⊥) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : K ≤ D.M := CFSG.Open.IsSubnormal.le hK.1
  have hMZ : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    have h4c := h4 h1930 c
    simpa [h4c.1] using h4c.2.2
  have hN3 : CFSG.Quasithin.borelOf c.L D.T ≤
      Subgroup.normalizer (D.T : Set G) ⊓ D.M :=
    Ctx23L.normalizer_TL_le_normalizer_T D Ch h4 h23 h1930 c
  have hbigBM : CFSG.Quasithin.bigB K c.L D.T ≤ D.M := by
    refine sup_le (sup_le ?_ ?_) D.sylowM.le
    · exact (CFSG.Quasithin.F1.borelOf_le K D.T).trans hKM
    · intro x hx
      exact (Subgroup.mem_inf.mp (hN3 hx)).2
  have hZle : D.Z ≤ CFSG.Open.pCoreOf 2 (K ⊔ CFSG.Quasithin.bigB K c.L D.T) := by
    have hZbig : D.Z ≤ CFSG.Quasithin.bigB K c.L D.T :=
      (uc22main1_Z_le_T D).trans le_sup_right
    have hZB : D.Z ≤ K ⊔ CFSG.Quasithin.bigB K c.L D.T := hZbig.trans le_sup_right
    have hKNZ : K ≤ Subgroup.normalizer (D.Z : Set G) :=
      hKCZ.trans (Subgroup.centralizer_le_normalizer (D.Z : Set G))
    have hbigNZ : CFSG.Quasithin.bigB K c.L D.T ≤
        Subgroup.normalizer (D.Z : Set G) := hbigBM.trans hMZ
    have hsupNZ : K ⊔ CFSG.Quasithin.bigB K c.L D.T ≤
        Subgroup.normalizer (D.Z : Set G) := sup_le hKNZ hbigNZ
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZB hsupNZ
      (CFSG.Open.IsElemAbelian.isPGroup (c.isElemAbelian_Z h4 h1930))
  have hZcent : D.Z ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.le_centralizer_iff.mp hKCZ
  have hZleC : D.Z ≤ CFSG.Open.pCoreOf 2 (K ⊔ CFSG.Quasithin.bigB K c.L D.T) ⊓
      Subgroup.centralizer (K : Set G) := le_inf hZle hZcent
  rw [hC] at hZleC
  exact uc22main1_Z_ne_bot D (le_bot_iff.mp hZleC)

theorem Ctx23L.false_of_wbn {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h54 : S23_5_4 D Ch)
    (h847 : R847ThinCZ D) (hWBN : CFSG.Quasithin.WBN.WBNInversionL2)
    {K : Subgroup G} (hK : K ∈ calC D.M) {f₁ : ℕ} (hf₁ : 2 ≤ f₁)
    (hKf : IsL2 (Bar2 K) f₁ ∨ IsSz (Bar2 K) f₁) (hHyp : CFSG.Quasithin.Hyp111 K c.L D.T)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrf₁ : r ∣ 2 ^ f₁ - 1)
    (hrn : r ∣ 2 ^ CFSG.Open.pRank 2 D.Z - 1)
    {a b : G} (haK : a ∈ K) (haT : a ∈ Subgroup.normalizer (D.T : Set G)) (har : orderOf a = r)
    (hbB0 : b ∈ c.B0) (hbr : orderOf b = r) (hab : Commute a b) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb1 : b ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hbr
    exact hr.ne_one hbr.symm
  have hKCZ : K ≤ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_Z_of_perfect D Ch h4 h1930 c (CFSG.Open.IsSubnormal.le hK.1) hK.2.1
  let E : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  have hEbigB : E ≤ CFSG.Quasithin.bigB K c.L D.T :=
    zpowers_sup_le_bigB c h1930 h4 h23 haK haT hbB0
  have hpow : ∀ e ∈ E, e ^ r = 1 := fun e he =>
    CFSG.GroupTheory.pow_eq_one_of_mem_zpowers_sup hab ⟨1, by rw [har, mul_one]⟩
      ⟨1, by rw [hbr, mul_one]⟩ he
  have hexp : ∀ e ∈ E, e ^ (2 ^ f₁ - 1) = 1 ∧
      e ^ (2 ^ CFSG.Open.pRank 2 D.Z - 1) = 1 :=
    pow_exp_eq_one_of_mem hpow hrf₁ hrn
  have hfield₁ : IsRankOneField (CFSG.Quasithin.oTwoQuot ↥K) f₁ :=
    hKf.elim (fun h => isRankOneField_oTwoQuot_of_isL2 h)
      (fun h => isRankOneField_oTwoQuot_of_isSz h)
  have hL2n : IsL2 (Bar2 c.L) (CFSG.Open.pRank 2 D.Z) := (h23 h1930 c).2.1
  have hf₂ : 2 ≤ CFSG.Open.pRank 2 D.Z :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_two_le_of_isL2 hL2n
  have hnorm : (D.T.subgroupOf (D.T ⊔ CFSG.Quasithin.borelOf c.L D.T)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer
      ((Ctx23L.normalizer_TL_le_normalizer_T D Ch h4 h23 h1930 c).trans inf_le_left))
  rcases hWBN G K c.L D.T f₁ (CFSG.Open.pRank 2 D.Z) hHyp hnorm hf₁ hfield₁ hf₂
      (nonempty_psl_oTwoQuot_of_isL2 hL2n) with hinvAll | hC
  · rcases hinvAll E hEbigB hexp with ⟨w, -, hinv⟩
    exact false_of_wbn_inversion c h1930 h4 h23 h54 h847 hK hKf haK hbB0 hr hr2 har hbr
      hb1 hinv
  · exact false_of_wbn_centralizer c h1930 h4 h23 hK hKCZ hC

private theorem false_of_cartan_sz {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h54 : S23_5_4 D Ch)
    (h208 : S20_8 D) (h847 : R847ThinCZ D)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) (hPush : Push2329 D Ch) (hSzAut : KSzTwoAut)
    (hD2337 : D2337 D Ch) (hWBN : CFSG.Quasithin.WBN.WBNInversionL2)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal)
    {m : ℕ} (hm2 : 2 ≤ m) (hSz : IsSz (Bar2 K) m)
    {A : Subgroup G} (hA : IsInnerCartanOnL A K c.L D.T m)
    {a b : G} (haK : a ∈ K) (haT : a ∈ Subgroup.normalizer (D.T : Set G))
    (hbB0 : b ∈ c.B0) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (har : orderOf a = r)
    (hbr : orderOf b = r) (hab : Commute a b) (hrdvd : r ∣ 2 ^ m - 1)
    (hrn : r ∣ 2 ^ CFSG.Open.pRank 2 D.Z - 1) : False := by
  have hDK : CFSG.Quasithin.borelOf K D.T ≤ c.N :=
    c.borelOf_le_N h1930 h4 h3 hPush hSzAut hD2337 hK hKn hm2 (Or.inl hSz)
      hA.1 hA.2.2.1
  have hHyp : CFSG.Quasithin.Hyp111 K c.L D.T :=
    c.wbn_hyp_of_D h1930 h4 h23 h208 h847 hK hKn (Or.inr hSz) haK hr hr2 har hDK
  exact c.false_of_wbn h1930 h4 h23 h54 h847 hWBN hK hm2 (Or.inr hSz) hHyp hr hr2
    hrdvd hrn haK haT har hbB0 hbr hab

private theorem false_of_cartan_l2 {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h54 : S23_5_4 D Ch)
    (h208 : S20_8 D) (h847 : R847ThinCZ D)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) (hPush : Push2329 D Ch) (hSzAut : KSzTwoAut)
    (hD2337 : D2337 D Ch) (hWBN : CFSG.Quasithin.WBN.WBNInversionL2)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal)
    {m : ℕ} (hm2 : 2 ≤ m) (hmdvd : m ∣ CFSG.Open.pRank 2 D.Z) {e : ℕ}
    (hL2 : IsL2 (Bar2 K) (2 ^ e * m))
    {A : Subgroup G} (hA : IsInnerCartanOnL A K c.L D.T m)
    {a b : G} (haK : a ∈ K) (haT : a ∈ Subgroup.normalizer (D.T : Set G))
    (hbB0 : b ∈ c.B0) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (har : orderOf a = r)
    (hbr : orderOf b = r) (hab : Commute a b) (hrdvd : r ∣ 2 ^ m - 1)
    (hrn : r ∣ 2 ^ CFSG.Open.pRank 2 D.Z - 1) : False := by
  have hf₁ : 2 ≤ 2 ^ e * m := by
    have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    calc 2 ≤ m := hm2
      _ = 1 * m := (one_mul m).symm
      _ ≤ 2 ^ e * m := Nat.mul_le_mul_right m h1
  have hrf₁ : r ∣ 2 ^ (2 ^ e * m) - 1 :=
    hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_left m (2 ^ e)))
  have hDK : CFSG.Quasithin.borelOf K D.T ≤ c.N :=
    c.borelOf_le_N h1930 h4 h3 hPush hSzAut hD2337 hK hKn hm2 (Or.inr ⟨e, hL2⟩)
      hA.1 hA.2.2.1
  have hHyp : CFSG.Quasithin.Hyp111 K c.L D.T :=
    c.wbn_hyp_of_D h1930 h4 h23 h208 h847 hK hKn (Or.inl hL2) haK hr hr2 har hDK
  exact c.false_of_wbn h1930 h4 h23 h54 h847 hWBN hK hf₁ (Or.inl hL2) hHyp hr hr2
    hrf₁ hrn haK haT har hbB0 hbr hab

theorem Ctx23L.false_of_cartan_wbn {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h54 : S23_5_4 D Ch)
    (h8 : S23_8 D Ch) (h52 : S23_5_2 D Ch) (h847 : R847ThinCZ D)
    (h208 : S20_8 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) (hPush : Push2329 D Ch)
    (hB2 : S23_37_B2 D Ch) (hSzAut : KSzTwoAut) (hD2337 : D2337 D Ch)
    (hWBN : CFSG.Quasithin.WBN.WBNInversionL2)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    {m : ℕ} (hm2 : 2 ≤ m) (hmdvd : m ∣ CFSG.Open.pRank 2 D.Z)
    (hshape : IsSz (Bar2 K) m ∨ ∃ e : ℕ, IsL2 (Bar2 K) (2 ^ e * m))
    {A₀ : Subgroup G} (hA₀ : IsInnerCartanOnL A₀ K c.L D.T m) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn : (K.subgroupOf D.M).Normal := (h8 h1930 c K hK).1
  have hKCZ : K ≤ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_Z_of_perfect D Ch h4 h1930 c (CFSG.Open.IsSubnormal.le hK.1) hK.2.1
  obtain ⟨r, hr, hrdvd, hr2m⟩ :=
    CFSG.Timmesfeld.exists_prime_dvd_two_pow_sub_one_not_dvd_two_mul hm2
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact hr2m (dvd_mul_right 2 m)
  obtain ⟨A, hA, hAB⟩ := hB2 h1930 c K hK hKn m A₀ hA₀
  obtain ⟨a, haA, b, hbB0, har, hbr, hab, -⟩ :=
    c.exists_order_r_pair h1930 h4 h23 h52 hKCZ hm2 hmdvd hA hAB hr hrdvd hr2m
  have haK : a ∈ K := (hA.1.trans inf_le_left) haA
  have haT : a ∈ Subgroup.normalizer (D.T : Set G) := (hA.1.trans inf_le_right) haA
  have hrn : r ∣ 2 ^ CFSG.Open.pRank 2 D.Z - 1 :=
    hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hmdvd)
  rcases hshape with hSz | ⟨e, hL2⟩
  · exact false_of_cartan_sz c h1930 h4 h23 h54 h208 h847 h3 hPush hSzAut hD2337 hWBN
      hK hKn hm2 hSz hA haK haT hbB0 hr hr2 har hbr hab hrdvd hrn
  · exact false_of_cartan_l2 c h1930 h4 h23 h54 h208 h847 h3 hPush hSzAut hD2337 hWBN
      hK hKn hm2 hmdvd hL2 hA haK haT hbB0 hr hr2 har hbr hab hrdvd hrn

theorem s23_37_of_wbn (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h54 : S23_5_4 D Ch) (h52 : S23_5_2 D Ch) (h8 : S23_8 D Ch) (h2112 : S21_12 D Ch)
    (h847 : R847ThinCZ D) (h208 : S20_8 D) (h29 : S23_29 D Ch) (hB2 : S23_37_B2 D Ch)
    (h3 : H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z) (hPush : Push2329 D Ch)
    (hSzAut : KSzTwoAut) (hD2337 : D2337 D Ch) (hWBN : CFSG.Quasithin.WBN.WBNInversionL2) :
    S23_37 D Ch := by
  intro h1930 c K hK
  rcases h29 h1930 c K hK with ⟨m, hm1, hmdvd, hshape, A, hA⟩ |
    ⟨q, hq, hq2, hL2, hcomm⟩
  · rcases Nat.lt_or_ge m 2 with hm | hm
    ·
      have hm1' : m = 1 := by omega
      subst hm1'
      rcases hshape with hSz | ⟨e, hguard, hL2⟩
      · obtain ⟨-, h3'⟩ :=
          CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_odd_three_le_of_isSz hSz
        exact absurd h3' (by omega)
      · have he : e = 0 ∨ e = 1 := by omega
        rcases he with rfl | rfl
        · have h2 :=
            CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_two_le_of_isL2 (by simpa using hL2)
          exact absurd h2 (by omega)
        · exact c.cartan_conclusion_of_isL2_four h2112 h1930 hK (by simpa using hL2)
    ·
      have hshape' : IsSz (Bar2 K) m ∨ ∃ e : ℕ, IsL2 (Bar2 K) (2 ^ e * m) := by
        rcases hshape with hSz | ⟨e, -, hL2⟩
        · exact Or.inl hSz
        · exact Or.inr ⟨e, hL2⟩
      exact (c.false_of_cartan_wbn h1930 h4 h23 h54 h8 h52 h847 h208 (h3 h1930 c)
        hPush hB2 hSzAut hD2337 hWBN hK hm hmdvd hshape' hA).elim
  · exact ⟨⟨q, hq, hq2, hL2⟩, hcomm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

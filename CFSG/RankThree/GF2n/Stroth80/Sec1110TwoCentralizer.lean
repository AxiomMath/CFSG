module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Model
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec11Ebar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem Ctx.card_bar_LB_ge (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 1 ≤ n) :
    Nat.card Z ^ (n - 1) ≤ Nat.card (bar M Q (LB M Q B)) := by
  have hbar : Nat.card (bar M Q (LB M Q B)) * Nat.card Q = Nat.card (LB M Q B) :=
    bar_card_mul_card_of_le (M := M) (S := LB M Q B) le_sup_left hc.LB_le_M
  have hge : Nat.card Q * Nat.card Z ^ (n - 1) ≤ Nat.card (LB M Q B) :=
    hc.card_LB_ge hw hn
  have h2 : Nat.card Z ^ (n - 1) * Nat.card Q ≤
      Nat.card (bar M Q (LB M Q B)) * Nat.card Q := by
    calc Nat.card Z ^ (n - 1) * Nat.card Q = Nat.card Q * Nat.card Z ^ (n - 1) :=
          Nat.mul_comm _ _
      _ ≤ Nat.card (LB M Q B) := hge
      _ = Nat.card (bar M Q (LB M Q B)) * Nat.card Q := hbar.symm
  exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos

theorem Ctx.card_bar_LB_ge_two (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) :
    Nat.card Z ^ 2 ≤ Nat.card (bar M Q (LB M Q B)) := by
  have h4 := hc.hyp.q4
  calc Nat.card Z ^ 2 ≤ Nat.card Z ^ (n - 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ Nat.card (bar M Q (LB M Q B)) := hc.card_bar_LB_ge hw (by omega)

theorem Ctx.isPGroup_bar_LB (hc : Ctx M Q Z B) :
    IsPGroup 2 (bar M Q (LB M Q B)) :=
  hc.isElemAbelian_bar_LB.isPGroup

noncomputable def barLBConjAct (hc : Ctx M Q Z B) :
    bar M Q (LB M Q B) →* MulAut (Xbar M Q Z B) :=
  letI : (Xbar M Q Z B).Normal := hc.Xbar_normal
  (MulAut.conjNormal : Mbar M Q →* MulAut (Xbar M Q Z B)).comp
    (bar M Q (LB M Q B)).subtype

theorem barLBConjAct_apply (hc : Ctx M Q Z B) (x : bar M Q (LB M Q B))
    (y : Xbar M Q Z B) :
    (barLBConjAct hc x) y =
      ⟨(x : Mbar M Q) * (y : Mbar M Q) * (x : Mbar M Q)⁻¹,
        hc.Xbar_normal.conj_mem (y : Mbar M Q) y.2 (x : Mbar M Q)⟩ := by
  haveI : (Xbar M Q Z B).Normal := hc.Xbar_normal
  rfl

theorem barLBConjAct_ker (hc : Ctx M Q Z B) :
    (barLBConjAct hc).ker =
      (bar M Q (LB M Q B) ⊓
        Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).subgroupOf
          (bar M Q (LB M Q B)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hx
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have h2 : (barLBConjAct hc x) ⟨y, hy⟩ = ⟨y, hy⟩ := by
      rw [hx]
      rfl
    have h3 : (x : Mbar M Q) * y * (x : Mbar M Q)⁻¹ = y := by
      have h4 := congrArg Subtype.val h2
      simpa [barLBConjAct, MulAut.conjNormal_apply] using h4
    calc y * (x : Mbar M Q) = ((x : Mbar M Q) * y * (x : Mbar M Q)⁻¹) * (x : Mbar M Q) := by
          rw [h3]
      _ = (x : Mbar M Q) * y := by group
  · rintro ⟨-, hxC⟩
    have hval : ∀ y : Xbar M Q Z B, ((barLBConjAct hc x) y : Mbar M Q) = (y : Mbar M Q) := by
      intro y
      have hcomm := Subgroup.mem_centralizer_iff.mp hxC (y : Mbar M Q) y.2
      have h1 : ((barLBConjAct hc x) y : Mbar M Q) =
          (x : Mbar M Q) * (y : Mbar M Q) * (x : Mbar M Q)⁻¹ := by
        simp only [barLBConjAct, MonoidHom.comp_apply, Subgroup.subtype_apply,
          MulAut.conjNormal_apply]
      rw [h1, ← hcomm]
      group
    ext y
    simpa using hval y

theorem barLBConjAct_ker_eq_bot_iff (hc : Ctx M Q Z B) :
    (barLBConjAct hc).ker = ⊥ ↔
      bar M Q (LB M Q B) ⊓
        Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) = ⊥ := by
  rw [barLBConjAct_ker]
  constructor
  · intro h
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hx.1⟩ : bar M Q (LB M Q B)) ∈
        (bar M Q (LB M Q B) ⊓
          Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).subgroupOf
            (bar M Q (LB M Q B)) := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    rw [h, Subgroup.mem_bot] at h1
    exact Subtype.ext_iff.mp h1
  · intro h
    rw [h]
    simp

theorem card_twoSubgroup_mulAut_psl2GF_two_dvd {x : ℕ} (hx : 1 ≤ x)
    (A : Subgroup (MulAut (CFSG.AGLEmbedding.PSL2GF 2 x))) (hA : IsPGroup 2 A) :
    Nat.card A ∣ 2 ^ x * x := by
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hdvd : Nat.card A ∣ Nat.card (MulAut (CFSG.AGLEmbedding.PSL2GF 2 x)) :=
    Subgroup.card_subgroup_dvd_card A
  rw [hk, CFSG.AGLEmbedding.card_mulAut_psl2GF 2 x hx] at hdvd
  have hodd : Odd ((2 ^ x) ^ 2 - 1) := by
    have heven : Even ((2 ^ x) ^ 2) := by
      rw [even_iff_two_dvd]
      exact (dvd_pow_self 2 (by omega : x ≠ 0)).trans (dvd_pow_self (2 ^ x) two_ne_zero)
    have h1 : 1 ≤ (2 ^ x) ^ 2 :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (pow_ne_zero x two_ne_zero))
    exact Nat.Even.sub_odd h1 heven odd_one
  have hcop : Nat.Coprime (2 ^ k) ((2 ^ x) ^ 2 - 1) :=
    (Nat.coprime_two_left.mpr hodd).pow_left k
  rw [hk]
  refine hcop.dvd_of_dvd_mul_left ?_
  rwa [show 2 ^ x * ((2 ^ x) ^ 2 - 1) * x =
    ((2 ^ x) ^ 2 - 1) * (2 ^ x * x) by ring] at hdvd

theorem bar_LB_inf_centralizer_Xbar_ne_bot_two_of_equiv_PSL2 (hc : Ctx M Q Z B)
    {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n) (hx : 1 ≤ x) (hZ : Nat.card Z = 2 ^ x)
    (he : Nonempty (Xbar M Q Z B ≃* CFSG.AGLEmbedding.PSL2GF 2 x)) :
    bar M Q (LB M Q B) ⊓
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) ≠ ⊥ := by
  intro hbot
  obtain ⟨e⟩ := he
  let f : bar M Q (LB M Q B) →* MulAut (CFSG.AGLEmbedding.PSL2GF 2 x) :=
    (MulAut.congr e).toMonoidHom.comp (barLBConjAct hc)
  have hact : Function.Injective (barLBConjAct hc) := by
    rw [← MonoidHom.ker_eq_bot_iff, barLBConjAct_ker_eq_bot_iff hc]
    exact hbot
  have hinj : Function.Injective f := (MulAut.congr e).injective.comp hact
  have hcard : Nat.card (bar M Q (LB M Q B)) = Nat.card f.range :=
    Nat.card_congr (Equiv.ofInjective f hinj)
  have hA2 : IsPGroup 2 f.range :=
    hc.isPGroup_bar_LB.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hdvd : Nat.card (bar M Q (LB M Q B)) ∣ 2 ^ x * x := by
    rw [hcard]
    exact card_twoSubgroup_mulAut_psl2GF_two_dvd hx f.range hA2
  have hpos : 0 < 2 ^ x * x :=
    Nat.mul_pos (pow_pos (by norm_num) x) (by omega)
  have hle : Nat.card (bar M Q (LB M Q B)) ≤ 2 ^ x * x := Nat.le_of_dvd hpos hdvd
  have hge := hc.card_bar_LB_ge_two hw hn
  rw [hZ] at hge
  have hlt : 2 ^ x * x < (2 ^ x) ^ 2 := by
    calc 2 ^ x * x < 2 ^ x * 2 ^ x :=
          (Nat.mul_lt_mul_left (pow_pos (by norm_num) x)).mpr x.lt_two_pow_self
      _ = (2 ^ x) ^ 2 := by ring
  exact (not_le.mpr hlt) (hge.trans hle)

theorem bar_LB_inf_centralizer_Xbar_ne_bot_two_of_lieModel (hc : Ctx M Q Z B)
    {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcent : Subgroup.center (Xbar M Q Z B) = ⊥) (hZ : Nat.card Z = 2 ^ x) :
    bar M Q (LB M Q B) ⊓
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) ≠ ⊥ := by
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · exfalso
      have h4 : 4 ≤ Nat.card Z := hc.hyp.q4
      rw [hZ, h] at h4
      norm_num at h4
    · exact h
  obtain ⟨e⟩ : Nonempty (Xbar M Q Z B ≃* CFSG.AGLEmbedding.PSL2GF 2 x) := by
    have hStated := hLm2.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
    simp only [CFSG.Open.StatedClassicalModel] at hStated
    obtain ⟨-, K, hKf, hKfin, hKcard, he⟩ := hStated
    letI : Field K := hKf
    letI : Finite K := hKfin
    obtain ⟨eK⟩ := he
    have hx0 : x ≠ 0 := by omega
    classical
    letI : Fintype K := Fintype.ofFinite K
    letI : Fintype (GaloisField 2 x) := Fintype.ofFinite _
    have hcard : Nat.card K = Nat.card (GaloisField 2 x) := by
      rw [hKcard, GaloisField.card 2 x hx0]
    have hcardF : Fintype.card K = Fintype.card (GaloisField 2 x) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact hcard
    let iso : K ≃+* GaloisField 2 x := FiniteField.ringEquivOfCardEq hcardF
    have hquot : XbarMod M Q Z B ≃* Xbar M Q Z B :=
      (QuotientGroup.quotientMulEquivOfEq hcent).trans QuotientGroup.quotientBot
    exact ⟨hquot.symm.trans (eK.trans
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
        (CFSG.GorensteinWalter.psl2RingEquiv iso)))⟩
  exact bar_LB_inf_centralizer_Xbar_ne_bot_two_of_equiv_PSL2 hc hw hn hx1 hZ ⟨e⟩

end CFSG.RankThree.GF2n.Stroth80

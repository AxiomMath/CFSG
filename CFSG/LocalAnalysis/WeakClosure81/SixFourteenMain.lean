module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenAbs
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenStruct
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteenQ
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.WeakClosure81.SixFourSz
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteen
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section CalOStar

theorem six_fourteen_of_calOStar (h139 : Hyp139) {k p : ℕ} {M V₀ V : Subgroup G} {g : G}
    (hk : k = 1 ∨ k = 2) (hp : p.Prime) (hpk : 2 ^ (k + 1) - 1 ≤ p) (h : Hyp64 k M V₀ V g)
    (hirr : ConjGenerated M V₀ V) (hK : CFSG.Open.IsKGroup ↥(Mbar M V₀ V h.elemAbelian))
    (hkm : k < mBar M V₀ V h.elemAbelian)
    {X : Subgroup (MulAut (Vtil V₀ V h.elemAbelian))} (hXM : X ≤ Mbar M V₀ V h.elemAbelian)
    (hXcard : Nat.card X = p)
    (hXnorm : ∀ m ∈ Mbar M V₀ V h.elemAbelian, ∀ x ∈ X, m * x * m⁻¹ ∈ X) :
    Concl614 (Vtil V₀ V h.elemAbelian) (Mbar M V₀ V h.elemAbelian) X := by
  have hV := h.elemAbelian
  have hM : M ≤ normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM₀ : M ≤ normalizer (V₀ : Set G) := h.le_normalizer₀
  have hgen : GenHyp M V g := genHyp_of_hyp64 h
  have hk1 : 1 ≤ k := by omega
  have hp3 : 3 ≤ p := by
    have h4 : 2 ^ 2 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hp2 : p ≠ 2 := by omega
  have hkd : k < dParam p := lt_dParam_of_two_pow_sub_one_le hk1 hp hpk
  obtain ⟨x, hxord, hXeq⟩ := exists_generator_of_card_eq_prime hp hXcard
  have hXp : IsPGroup p X := IsPGroup.of_card (n := 1) (by rw [hXcard, pow_one])
  have hX1 : X ≠ ⊥ := by
    intro hX
    rw [hX, Subgroup.card_bot] at hXcard
    exact hp.one_lt.ne hXcard
  have hirrW : ∀ Z : Subgroup (Vtil V₀ V hV),
      (∀ φ ∈ Mbar M V₀ V hV, ∀ z ∈ Z, φ z ∈ Z) → Z = ⊥ ∨ Z = ⊤ := by
    intro Z hZ
    by_cases hZ0 : Z = ⊥
    · exact Or.inl hZ0
    · exact Or.inr (eq_top_of_invariant_of_conjGenerated hV hM hM₀ hirr hZ hZ0)
  have hfix : fixV X = ⊥ := fixV_eq_bot_of_normal hirrW hXnorm hX1
  have hfixx : fixV (Subgroup.zpowers x) = ⊥ := by rw [← hXeq]; exact hfix
  have hBbM : barSub V₀ V hV (BOf M V g) ≤ Mbar M V₀ V hV :=
    barSub_mono V₀ V hV inf_le_right
  have hBab := isElemAbelian2_barSub_BOf h
  have hcomm := commutator_barSub_BOf_ne_bot h hgen hirr hp hp2 hkd hX1 hXnorm hXp
  obtain ⟨b, hbB, hbx⟩ : ∃ b ∈ barSub V₀ V hV (BOf M V g), b * x ≠ x * b := by
    by_contra hall
    push Not at hall
    apply hcomm
    rw [← le_bot_iff, Subgroup.commutator_le]
    intro y hy b hb
    rw [hXeq] at hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have hc : Commute x b := (hall b hb).symm
    exact hc.zpow_left i
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hbx (by rw [one_mul, mul_one])
  have hbord : orderOf b = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (hBab.2 b hbB) hb1
  have hXx : ∀ a ∈ barSub V₀ V hV (BOf M V g), a * x * a⁻¹ ∈ Subgroup.zpowers x := by
    intro a ha
    rw [← hXeq]
    exact hXnorm a (hBbM ha) x (by rw [hXeq]; exact Subgroup.mem_zpowers x)
  have hinv : b * x * b⁻¹ = x⁻¹ :=
    mul_mul_inv_eq_inv_of_not_commute hp hp2 hxord hbord (hXx b hbB) hbx
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := Vtil_pow_two hV
  have hbMb : b ∈ Mbar M V₀ V hV := hBbM hbB
  have hkT : k < rkIdx (fixV (Subgroup.zpowers b)) := by
    have hA : IsPGroup 2 (Subgroup.zpowers b) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hbord, pow_one]
    have hA1 : Subgroup.zpowers b ≠ ⊥ := by
      rw [Ne, Subgroup.zpowers_eq_bot]
      exact hb1
    exact lt_of_lt_of_le hkm (E3.mParam_le_rkIdx_fixV (Subgroup.zpowers_le.2 hbMb) hA hA1)
  obtain ⟨-, hp3', n, Y, hWcard, hn2, hDcard, hYD, hYX, hYrk⟩ :=
    hyp139_data_of_dihedral hW hk hp hpk hxord hbord hinv hfixx
      (fixV_zpowers_le_imgTil_UOf h hgen hbB hb1)
      (fun u hu => apply_mul_inv_mem_imgTil_NOf h hgen hbB hb1 hu)
      (fun w hw => mem_imgTil_UOf_of_apply_mul_inv_mem h hgen hbB hb1 hw)
      (rkIdx_imgTil_UOf_le h hgen) hBab hbB hXx
      (fun a ha β hβ => mem_fixV.1 (imgTil_NOf_le_fixV_barSub h ha) β hβ)
      (card_barSub_mul_index_eq h hgen) hkT
  subst hp3'
  haveI : Nontrivial (Vtil V₀ V hV) := Finite.one_lt_card_iff_nontrivial.1
    (by rw [hWcard]; exact Nat.one_lt_pow (by omega) (by norm_num))
  have hO2 : pCoreOf 2 (Mbar M V₀ V hV) = ⊥ := pCoreOf_eq_bot_of_irreducible hW hirrW
  have hDne : 1 < Nat.card ↥(barSub V₀ V hV (BOf M V g) ⊓
      Subgroup.centralizer ({x} : Set (MulAut (Vtil V₀ V hV)))) := by
    rw [hDcard]
    exact Nat.one_lt_two_pow (by omega)
  haveI : Finite ↥(barSub V₀ V hV (BOf M V g) ⊓
      Subgroup.centralizer ({x} : Set (MulAut (Vtil V₀ V hV)))) :=
    Nat.finite_of_card_ne_zero (by omega)
  haveI := Finite.one_lt_card_iff_nontrivial.1 hDne
  obtain ⟨⟨t, htD⟩, ht1⟩ := exists_ne (1 : ↥(barSub V₀ V hV (BOf M V g) ⊓
      Subgroup.centralizer ({x} : Set (MulAut (Vtil V₀ V hV)))))
  have ht1' : t ≠ 1 := fun h' => ht1 (Subtype.ext h')
  have htord : orderOf t = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (hBab.2 t htD.1) ht1'
  have htrk : rkIdx (fixV (Subgroup.zpowers t)) ≤ 3 := by
    have h1 : Y ≤ fixV (Subgroup.zpowers t) := fun y hy =>
      mem_fixV.2 fun z hz => mem_fixV.1 (hYD hy) z (Subgroup.zpowers_le.2 htD hz)
    have h2 := rkIdx_anti h1
    omega
  have hDMb : barSub V₀ V hV (BOf M V g) ⊓
      Subgroup.centralizer ({x} : Set (MulAut (Vtil V₀ V hV))) ≤ Mbar M V₀ V hV :=
    inf_le_left.trans hBbM
  have hDX : ∀ d ∈ barSub V₀ V hV (BOf M V g) ⊓
      Subgroup.centralizer ({x} : Set (MulAut (Vtil V₀ V hV))), ∀ y ∈ X, d * y = y * d := by
    intro d hd y hy
    rw [hXeq] at hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hdx : x * d = d * x := Subgroup.mem_centralizer_iff.1 hd.2 x (Set.mem_singleton x)
    exact (Commute.zpow_right hdx.symm i)
  have hDs : ∀ d ∈ barSub V₀ V hV (BOf M V g) ⊓
      Subgroup.centralizer ({x} : Set (MulAut (Vtil V₀ V hV))), d * b = b * d :=
    fun d hd => hBab.1 d hd.1 b hbB
  have hDab : IsElemAbelian2 (barSub V₀ V hV (BOf M V g) ⊓
      Subgroup.centralizer ({x} : Set (MulAut (Vtil V₀ V hV)))) :=
    ⟨fun a ha c hc => hBab.1 a ha.1 c hc.1, fun a ha => hBab.2 a ha.1⟩
  have hbX : b ∉ Subgroup.centralizer (X : Set (MulAut (Vtil V₀ V hV))) := by
    intro hb
    apply hbx
    exact (Subgroup.mem_centralizer_iff.1 hb x (by rw [hXeq]; exact Subgroup.mem_zpowers x)).symm
  have hYX' : ∀ y ∈ X, ∀ w ∈ Y, y w ∈ Y := by
    rw [hXeq]
    exact hYX
  rcases h139 (Vtil V₀ V hV) hW (Mbar M V₀ V hV) X _ b Y n hK hO2 hirrW
      ⟨t, hDMb htD, htord, htrk⟩ hXM hXnorm hXcard hbMb hbord hbX hYX' hYrk hWcard hDMb hDX
      hDs hDab hDcard hYD with (h1 | h2 | ⟨h3, hn3⟩) | h4
  · exact Or.inl (Or.inr (Or.inl ⟨n, h1⟩))
  · exact Or.inl (Or.inl ⟨n, h2⟩)
  · exact Or.inl (Or.inr (Or.inr ⟨h3, by rw [hWcard, hn3]; norm_num⟩))
  · exact Or.inr ⟨n, h4⟩

end CalOStar

end CFSG.LocalAnalysis.WeakClosure81

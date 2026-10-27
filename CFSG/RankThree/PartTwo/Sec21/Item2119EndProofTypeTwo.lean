module

import CFSG.RankThree.PartTwo.KFacts.KS222SL3Tools
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofJArith
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec6.Item68
public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofDefs
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2Proof2120
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2119EndProof

open Matrix CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits diagE)
open CFSG.Assembly.RankThreeEven (projImage projSL)

section Matrices

variable {K : Type} [Field K]

@[expose] def swapZO : GL (Fin 3) K :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

@[expose] def swapZT : GL (Fin 3) K :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩

theorem swapZO_inv : (swapZO : GL (Fin 3) K)⁻¹ = swapZO := by
  rw [inv_eq_iff_mul_eq_one]
  apply Units.ext
  show !![(0 : K), 1, 0; 1, 0, 0; 0, 0, 1] * !![0, 1, 0; 1, 0, 0; 0, 0, 1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

theorem swapZT_inv : (swapZT : GL (Fin 3) K)⁻¹ = swapZT := by
  rw [inv_eq_iff_mul_eq_one]
  apply Units.ext
  show !![(0 : K), 0, 1; 0, 1, 0; 1, 0, 0] * !![0, 0, 1; 0, 1, 0; 1, 0, 0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

theorem swapZO_mul_diagUnits (a b c : Kˣ) :
    swapZO * diagUnits a b c = diagUnits b a c * swapZO := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagUnits, coe_diagUnits]
  show !![(0 : K), 1, 0; 1, 0, 0; 0, 0, 1] * diagonal ![(a : K), b, c] =
    diagonal ![(b : K), a, c] * !![0, 1, 0; 1, 0, 0; 0, 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, diagonal]

theorem swapZT_mul_diagUnits (a b c : Kˣ) :
    swapZT * diagUnits a b c = diagUnits c b a * swapZT := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagUnits, coe_diagUnits]
  show !![(0 : K), 0, 1; 0, 1, 0; 1, 0, 0] * diagonal ![(a : K), b, c] =
    diagonal ![(c : K), b, a] * !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, diagonal]

theorem swapZO_mul_self : (swapZO : GL (Fin 3) K) * swapZO = 1 := by
  calc (swapZO : GL (Fin 3) K) * swapZO = swapZO * swapZO⁻¹ := by rw [swapZO_inv]
    _ = 1 := mul_inv_cancel _

theorem swapZT_mul_self : (swapZT : GL (Fin 3) K) * swapZT = 1 := by
  calc (swapZT : GL (Fin 3) K) * swapZT = swapZT * swapZT⁻¹ := by rw [swapZT_inv]
    _ = 1 := mul_inv_cancel _

theorem swapZO_conj (a b c : Kˣ) :
    swapZO * diagUnits a b c * swapZO = diagUnits b a c := by
  rw [swapZO_mul_diagUnits, mul_assoc, swapZO_mul_self, mul_one]

theorem swapZT_conj (a b c : Kˣ) :
    swapZT * diagUnits a b c * swapZT = diagUnits c b a := by
  rw [swapZT_mul_diagUnits, mul_assoc, swapZT_mul_self, mul_one]

theorem scalar_mem_zPi_true (q : ℕ) (u : Kˣ) :
    GeneralLinearGroup.scalar (Fin 3) u ∈ Sec4.zPi true 3 q K :=
  ⟨⟨GeneralLinearGroup.scalar (Fin 3) u, Sec4.mem_glPi_true _ _⟩,
    Subgroup.mem_center_iff.mpr fun h => Subtype.ext (SL3Lines.scalar_mul_comm u h).symm, rfl⟩

theorem type123_two_of_frame {q : ℕ} {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {y g : GL (Fin 3) K} {l s t : Kˣ} (hs : (s : K) ^ 3 = 1) (ht : (t : K) ^ 3 = 1)
    (hst : s * t ≠ 1)
    (hy : g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) :
    Sec4.Type123 true q K y 2 := by
  have hsc : ∀ (X : GL (Fin 3) K) (v : Kˣ), X * GeneralLinearGroup.scalar (Fin 3) v =
      GeneralLinearGroup.scalar (Fin 3) v * X := fun X v => (SL3Lines.scalar_mul_comm v X).symm
  have hs3 : s ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hs, Units.val_one])
  have ht3 : t ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, ht, Units.val_one])
  by_cases hs1 : s = 1
  ·
    subst hs1
    have ht1 : t ≠ 1 := by
      intro h
      apply hst
      rw [h, one_mul]
    refine ⟨t, ht, ht1, _, scalar_mem_zPi_true q l⁻¹, g * swapZT, Sec4.mem_glPi_true _ _, ?_⟩
    calc (g * swapZT)⁻¹ * (y * GeneralLinearGroup.scalar (Fin 3) l⁻¹) * (g * swapZT)
        = swapZT * g⁻¹ * y * (GeneralLinearGroup.scalar (Fin 3) l⁻¹ * g) * swapZT := by
          rw [_root_.mul_inv_rev, swapZT_inv]
          group
      _ = swapZT * g⁻¹ * y * g * (GeneralLinearGroup.scalar (Fin 3) l⁻¹ * swapZT) := by
          rw [← hsc g l⁻¹]
          group
      _ = swapZT * (g⁻¹ * y * g) * swapZT * GeneralLinearGroup.scalar (Fin 3) l⁻¹ := by
          rw [← hsc swapZT l⁻¹]
          group
      _ = GeneralLinearGroup.scalar (Fin 3) l * (swapZT * diagUnits 1 1 t * swapZT) *
            GeneralLinearGroup.scalar (Fin 3) l⁻¹ := by
          rw [hy]
          calc swapZT * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 1 t) * swapZT *
                GeneralLinearGroup.scalar (Fin 3) l⁻¹ =
              (swapZT * GeneralLinearGroup.scalar (Fin 3) l) * diagUnits 1 1 t * swapZT *
                GeneralLinearGroup.scalar (Fin 3) l⁻¹ := by group
            _ = _ := by rw [hsc swapZT l]; group
      _ = diagE t := by
          rw [swapZT_conj, ← hsc (diagUnits t 1 1) l, mul_assoc, ← map_mul, mul_inv_cancel,
            map_one, mul_one]
          rfl
  by_cases ht1 : t = 1
  ·
    subst ht1
    refine ⟨s, hs, hs1, _, scalar_mem_zPi_true q l⁻¹, g * swapZO, Sec4.mem_glPi_true _ _, ?_⟩
    calc (g * swapZO)⁻¹ * (y * GeneralLinearGroup.scalar (Fin 3) l⁻¹) * (g * swapZO)
        = swapZO * g⁻¹ * y * (GeneralLinearGroup.scalar (Fin 3) l⁻¹ * g) * swapZO := by
          rw [_root_.mul_inv_rev, swapZO_inv]
          group
      _ = swapZO * g⁻¹ * y * g * (GeneralLinearGroup.scalar (Fin 3) l⁻¹ * swapZO) := by
          rw [← hsc g l⁻¹]
          group
      _ = swapZO * (g⁻¹ * y * g) * swapZO * GeneralLinearGroup.scalar (Fin 3) l⁻¹ := by
          rw [← hsc swapZO l⁻¹]
          group
      _ = GeneralLinearGroup.scalar (Fin 3) l * (swapZO * diagUnits 1 s 1 * swapZO) *
            GeneralLinearGroup.scalar (Fin 3) l⁻¹ := by
          rw [hy]
          calc swapZO * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s 1) * swapZO *
                GeneralLinearGroup.scalar (Fin 3) l⁻¹ =
              (swapZO * GeneralLinearGroup.scalar (Fin 3) l) * diagUnits 1 s 1 * swapZO *
                GeneralLinearGroup.scalar (Fin 3) l⁻¹ := by group
            _ = _ := by rw [hsc swapZO l]; group
      _ = diagE s := by
          rw [swapZO_conj, ← hsc (diagUnits s 1 1) l, mul_assoc, ← map_mul, mul_inv_cancel,
            map_one, mul_one]
          rfl
  ·
    have hst' : s = t := by
      have hs1' : (s : K) ≠ 1 := fun h => hs1 (Units.ext h)
      have ht1' : (t : K) ≠ 1 := fun h => ht1 (Units.ext h)
      have hst1 : (s : K) * t ≠ 1 := fun h => hst (Units.ext (by rw [Units.val_mul, h]; rfl))
      apply Units.ext
      rcases Sec4.cube_root_cases hτ hτ1 hs with h | h | h
      · exact absurd h hs1'
      · rcases Sec4.cube_root_cases hτ hτ1 ht with h' | h' | h'
        · exact absurd h' ht1'
        · rw [h, h']
        · exfalso
          apply hst1
          rw [h, h', ← pow_succ']
          exact hτ
      · rcases Sec4.cube_root_cases hτ hτ1 ht with h' | h' | h'
        · exact absurd h' ht1'
        · exfalso
          apply hst1
          rw [h, h', ← pow_succ]
          exact hτ
        · rw [h, h']
    subst hst'
    refine ⟨s⁻¹, ?_, ?_, _, scalar_mem_zPi_true q (l * s)⁻¹, g, Sec4.mem_glPi_true _ _, ?_⟩
    · rw [Units.val_inv_eq_inv_val, inv_pow, hs, inv_one]
    · exact fun h => hs1 (inv_eq_one.mp h)
    · calc g⁻¹ * (y * GeneralLinearGroup.scalar (Fin 3) (l * s)⁻¹) * g
          = g⁻¹ * y * (GeneralLinearGroup.scalar (Fin 3) (l * s)⁻¹ * g) := by group
        _ = (g⁻¹ * y * g) * GeneralLinearGroup.scalar (Fin 3) (l * s)⁻¹ := by
            rw [← hsc g (l * s)⁻¹]
            group
        _ = diagE s⁻¹ := by
            rw [hy]
            apply Units.ext
            rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar,
              GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.scalar_apply,
              coe_diagUnits, Sec4.diagE, coe_diagUnits, diagonal_mul_diagonal,
              diagonal_mul_diagonal]
            congr 1
            funext i
            fin_cases i <;> simp [Units.val_mul] <;> field_simp

end Matrices

section Config

variable {G : Type} [Group G] [Finite G]

theorem inducesTypeOn_two_of_end (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    {A E U L U₀ X : Subgroup G} {c d a : G} (hE : Config2119End G A E U c L d U₀ a X)
    (hcfgX : Config2119 G A E U₀ a X) (hdX : d ∈ X) (hdT : Sec4.InducesTypeOn X d 1)
    (haCD : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d) : Sec4.InducesTypeOn X c 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcL : c ∉ L := (Item21Late2Proof.frame_of h45 h66 hE.cfg).1
  obtain ⟨hpair, ⟨m, hm0, hmev, ⟨eX⟩⟩, hC, -, -⟩ := hcfgX
  have hm : 2 ≤ m := by
    obtain ⟨k, hk⟩ := hmev
    omega
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hpairsL := mem_lThreeStarPairs_iff.mp hE.cfg.pair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have haA : a ∈ A := hpair.mem_E.2 hpairs.1.1
  have ha1 : a ≠ 1 := hpairs.2.1
  have ha3 : orderOf a = 3 := orderOf_eq_prime (h3 a haA) ha1
  have hcA : c ∈ A := hE.cfg.pair.mem_E.2 hpairsL.1.1
  have hc1 : c ≠ 1 := hpairsL.2.1
  have hdA : d ∈ A := hE.mem_d.1
  have hdL : d ∈ L := hE.mem_d.2
  have hd1 := hE.ne_one_d
  have hca : c ∉ Subgroup.zpowers a := fun h =>
    haCD (Subgroup.mem_sup_left (Item21Late2Proof.mem_zpowers_of_mem (h3 a haA) h hc1
      (Subgroup.mem_zpowers a)))
  have hda : d ∉ Subgroup.zpowers a := fun h =>
    haCD (Subgroup.mem_sup_right (Item21Late2Proof.mem_zpowers_of_mem (h3 a haA) h hd1
      (Subgroup.mem_zpowers a)))
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  have hnotin : c ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers d := by
    intro h
    have hdc' : d ∉ Subgroup.zpowers c := fun h' => hcd
      (Item21Late2Proof.mem_zpowers_of_mem (h3 c hcA) h' hd1 (Subgroup.mem_zpowers c))
    have hB : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) = 9 :=
      Item21LateProof.card_zpowers_sup_zpowers (hcomm c hcA d hdA) (h3 c hcA) (h3 d hdA) hc1 hdc'
    have hB' : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers d : Subgroup G) = 9 :=
      Item21LateProof.card_zpowers_sup_zpowers (hcomm a haA d hdA) (h3 a haA) (h3 d hdA) ha1 hda
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers d :=
      sup_le (Subgroup.zpowers_le.mpr h) le_sup_right
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hB, hB'])
    apply haCD
    rw [heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hXa : X ∈ thetaComponentsAt 3 a := lZeroStarAt_subset A a hpairs.2.2.1
  have hG4 := hpair.standing.toTheoremFourHyp
  have hAL : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe haA ha1 X hXa
  have hXs : X ∈ lStar A :=
    lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A a hpairs.2.2.1)
  have hCA : A ⊓ Sec4.thetaQuotCentralizer X = Subgroup.zpowers a := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr
      ⟨haA, Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hXa⟩) ?_
    rw [Nat.card_zpowers, ha3]
    exact Sec6.card_le_three_of_isCyclic (h66 G hpair.standing A hpair.mem_S X hXs)
      fun y hy => h3 y hy.1
  set T : Subgroup.normalizer (X : Set G) →* MulAut (lBar X) :=
    (Sec4.thetaQuotMulAut X).comp X.normalizerMonoidHom with hT
  have hTinner : ∀ (l₀ : G) (hl₀ : l₀ ∈ X) (z : lBar X),
      T ⟨l₀, Subgroup.le_normalizer hl₀⟩ z =
        ((⟨l₀, hl₀⟩ : X) : lBar X) * z * ((⟨l₀, hl₀⟩ : X) : lBar X)⁻¹ :=
    fun l₀ hl₀ z => Item21Late2Proof.thetaQuotMulAut_inner hl₀ _ z
  have htriv : ∀ (x : G) (hx : x ∈ A), (∀ z, T ⟨x, hAL hx⟩ z = z) → x ∈ Subgroup.zpowers a := by
    intro x hx h
    have hmem : x ∈ A ⊓ Sec4.thetaQuotCentralizer X :=
      ⟨hx, ⟨⟨x, hAL hx⟩, MonoidHom.mem_ker.mpr (MulEquiv.ext h), rfl⟩⟩
    rwa [hCA] at hmem
  obtain ⟨π, p, f, K, _, hPi, hmod, e, D, hD, hconj, -⟩ := hC
  have hcard := Sec13.card_projImage_slPi_mul_three hPi hmod
  rw [← Nat.card_congr e.toEquiv] at hcard
  obtain ⟨rfl, rfl, hfn⟩ := Sec19.Step1917EqProof.eq_two_of_card hPi.prime hPi.one_le
    (by omega) hmod hcard (Sec19.Step1917EqProof.card_kStar (by omega) (Or.inr ⟨eX⟩))
  subst hfn
  have h2 : (2 : K) = 0 := Item21Late2Proof.two_eq_zero_of_piField hPi
  have hq2 : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := Sec4.exists_tau hPi hmod
  set ψ : lBar X →* ProjGenLinGroup (Fin 3) K :=
    (projImage (Sec4.slPi true 3 (2 ^ f) K)).subtype.comp e.toMonoidHom with hψ
  have hψinj : Function.Injective ψ :=
    (projImage (Sec4.slPi true 3 (2 ^ f) K)).subtype_injective.comp e.injective
  have hψe : ∀ z, ψ z = (e z : ProjGenLinGroup (Fin 3) K) := fun z => rfl
  have hyA : ∀ (x : G) (hx : x ∈ A), ∃ y ∈ D, ∀ z,
      ψ (T ⟨x, hAL hx⟩ z) = ProjGenLinGroup.mk y * ψ z * (ProjGenLinGroup.mk y)⁻¹ := by
    intro x hx
    obtain ⟨y, hyD, hy⟩ := hconj _ (Sec4.mem_autThetaQuot_iff.mpr ⟨x, hAL hx, hx, rfl⟩)
    exact ⟨y, hyD, fun z => hy z⟩
  obtain ⟨g, -, hdiag, -⟩ := Sec4.isTypeC_conj_std hPi hmod hD
  have hsc : ∀ (Y : GL (Fin 3) K) (v : Kˣ), Y * GeneralLinearGroup.scalar (Fin 3) v =
      GeneralLinearGroup.scalar (Fin 3) v * Y := fun Y v => (SL3Lines.scalar_mul_comm v Y).symm
  have hscal : ∀ (x : G) (hx : x ∈ A) (y : GL (Fin 3) K) (l : Kˣ),
      (∀ z, ψ (T ⟨x, hAL hx⟩ z) = ProjGenLinGroup.mk y * ψ z * (ProjGenLinGroup.mk y)⁻¹) →
      g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l → x ∈ Subgroup.zpowers a := by
    intro x hx y l hy hyl
    have hy1 : ProjGenLinGroup.mk y = 1 := by
      have e1 : y = GeneralLinearGroup.scalar (Fin 3) l := by
        calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
          _ = GeneralLinearGroup.scalar (Fin 3) l := by rw [hyl, hsc g l, mul_inv_cancel_right]
      rw [e1, ProjGenLinGroup.mk_scalar]
    refine htriv x hx fun z => hψinj ?_
    rw [hy, hy1, one_mul, inv_one, mul_one]
  have hroots : ∀ v : Kˣ, v ∈ rootsOfUnity 3 K → (v : K) ^ 3 = 1 := fun v hv => by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 v).mp hv, Units.val_one]
  obtain ⟨yd, hydD, hyd⟩ := hyA d hdA
  obtain ⟨ld, sd, td, hsd, htd, hgd⟩ := hdiag yd hydD
  have hψd : ψ ((⟨d, hdX⟩ : X) : lBar X) = ProjGenLinGroup.mk yd := by
    refine Item21Late2Proof.coe_e_eq_mk_of_inner hPi hmod hq2 e _ yd fun z => ?_
    have h1 := hyd z
    rw [show T ⟨d, hAL hdA⟩ z = ((⟨d, hdX⟩ : X) : lBar X) * z * ((⟨d, hdX⟩ : X) : lBar X)⁻¹ from
      hTinner d hdX z] at h1
    exact h1
  obtain ⟨m₀, hm₀⟩ := Item21Late2Proof.exists_conj_inv_of_inducesTypeOn_one hm eX hdX hdT
  obtain ⟨r, -, hrm⟩ := (e m₀).2
  have hψm : ψ m₀ = ProjGenLinGroup.mk r := by
    rw [hψe]
    exact hrm.symm
  have hr1 : ProjGenLinGroup.mk (r * yd * r⁻¹) = ProjGenLinGroup.mk yd⁻¹ := by
    have h0 := congrArg ψ hm₀
    rw [map_mul, map_mul, map_inv, map_inv, hψd, hψm] at h0
    rw [map_mul, map_mul, map_inv, map_inv]
    exact h0
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hr1
  have hr3 : (g⁻¹ * r * g) * (g⁻¹ * yd * g) * (g⁻¹ * r * g)⁻¹ *
      GeneralLinearGroup.scalar (Fin 3) u = (g⁻¹ * yd * g)⁻¹ := by
    calc (g⁻¹ * r * g) * (g⁻¹ * yd * g) * (g⁻¹ * r * g)⁻¹ * GeneralLinearGroup.scalar (Fin 3) u
        = g⁻¹ * (r * yd * r⁻¹) * (g * GeneralLinearGroup.scalar (Fin 3) u) := by group
      _ = g⁻¹ * (r * yd * r⁻¹ * GeneralLinearGroup.scalar (Fin 3) u) * g := by
          rw [hsc g u]
          group
      _ = (g⁻¹ * yd * g)⁻¹ := by rw [hu]; group
  rw [hgd] at hr3
  have hsdtd : sd * td = 1 := by
    have hsd3 := hroots sd hsd
    have htd3 := hroots td htd
    rcases Item21Late2Proof.eq_of_conj_inv h2 hτ₀ hτ₀1 hsd3 htd3 hr3 with
      ⟨h1, h1'⟩ | ⟨h1, h1'⟩ | ⟨h1, h1'⟩
    · exact Units.ext (by rw [Units.val_mul, h1, h1', mul_one, Units.val_one])
    · exact Units.ext (by rw [Units.val_mul, h1, h1', ← pow_succ', hτ₀, Units.val_one])
    · exact Units.ext (by rw [Units.val_mul, h1, h1', ← pow_succ, hτ₀, Units.val_one])
  obtain ⟨yc, hycD, hyc⟩ := hyA c hcA
  obtain ⟨lc, sc, tc, hsc', htc, hgc⟩ := hdiag yc hycD
  have hsctc : sc * tc ≠ 1 := by
    intro hst
    have htc' : tc = sc⁻¹ := eq_inv_of_mul_eq_one_right hst
    have htd' : td = sd⁻¹ := eq_inv_of_mul_eq_one_right hsdtd
    by_cases hsc1 : sc = 1
    · exact hca (hscal c hcA yc lc hyc (by
        rw [hgc, htc', hsc1, inv_one, SL3Lines.diagUnits_one_one_one, mul_one]))
    by_cases hsd1 : sd = 1
    · exact hda (hscal d hdA yd ld hyd (by
        rw [hgd, htd', hsd1, inv_one, SL3Lines.diagUnits_one_one_one, mul_one]))
    have hk : sc * sd = 1 ∨ sc * sd * sd = 1 := by
      have hsc1' : (sc : K) ≠ 1 := fun h => hsc1 (Units.ext h)
      have hsd1' : (sd : K) ≠ 1 := fun h => hsd1 (Units.ext h)
      rcases Sec4.cube_root_cases hτ₀ hτ₀1 (hroots sc hsc') with h | h | h
      · exact absurd h hsc1'
      · rcases Sec4.cube_root_cases hτ₀ hτ₀1 (hroots sd hsd) with h' | h' | h'
        · exact absurd h' hsd1'
        · right
          exact Units.ext (by rw [Units.val_mul, Units.val_mul, h, h', ← pow_two, ← pow_succ,
            hτ₀, Units.val_one])
        · left
          exact Units.ext (by rw [Units.val_mul, h, h', ← pow_succ', hτ₀, Units.val_one])
      · rcases Sec4.cube_root_cases hτ₀ hτ₀1 (hroots sd hsd) with h' | h' | h'
        · exact absurd h' hsd1'
        · left
          exact Units.ext (by rw [Units.val_mul, h, h', ← pow_succ, hτ₀, Units.val_one])
        · right
          exact Units.ext (by
            rw [Units.val_mul, Units.val_mul, h, h', Units.val_one]
            linear_combination (τ₀ ^ 3 + 1) * hτ₀)
    have hTd : ∀ z, ψ (T ⟨d, hAL hdA⟩ z) =
        ProjGenLinGroup.mk yd * ψ z * (ProjGenLinGroup.mk yd)⁻¹ := hyd
    rcases hk with hk | hk
    ·
      have hxA : c * d ∈ A := A.mul_mem hcA hdA
      have hact : ∀ z, ψ (T ⟨c * d, hAL hxA⟩ z) =
          ProjGenLinGroup.mk (yc * yd) * ψ z * (ProjGenLinGroup.mk (yc * yd))⁻¹ := by
        intro z
        have e1 : T ⟨c * d, hAL hxA⟩ = T ⟨c, hAL hcA⟩ * T ⟨d, hAL hdA⟩ := by
          rw [← map_mul]
          rfl
        rw [e1, MulAut.mul_apply, hyc, hTd, map_mul]
        group
      have hgl : g⁻¹ * (yc * yd) * g = GeneralLinearGroup.scalar (Fin 3) (lc * ld) := by
        calc g⁻¹ * (yc * yd) * g = (g⁻¹ * yc * g) * (g⁻¹ * yd * g) := by group
          _ = GeneralLinearGroup.scalar (Fin 3) (lc * ld) * diagUnits 1 (sc * sd) (tc * td) := by
              rw [hgc, hgd, Sec4.scalar_diagUnits_mul]
          _ = GeneralLinearGroup.scalar (Fin 3) (lc * ld) := by
              rw [htc', htd', ← mul_inv, hk, inv_one, SL3Lines.diagUnits_one_one_one, mul_one]
      have hcda := hscal _ hxA _ _ hact hgl
      apply hnotin
      have e2 : c = (c * d) * d⁻¹ := by group
      rw [e2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcda)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers d)))
    ·
      have hxA : c * d * d ∈ A := A.mul_mem (A.mul_mem hcA hdA) hdA
      have hact : ∀ z, ψ (T ⟨c * d * d, hAL hxA⟩ z) =
          ProjGenLinGroup.mk (yc * yd * yd) * ψ z * (ProjGenLinGroup.mk (yc * yd * yd))⁻¹ := by
        intro z
        have e1 : T ⟨c * d * d, hAL hxA⟩ = T ⟨c, hAL hcA⟩ * T ⟨d, hAL hdA⟩ * T ⟨d, hAL hdA⟩ := by
          rw [← map_mul, ← map_mul]
          rfl
        rw [e1, MulAut.mul_apply, MulAut.mul_apply, hyc, hTd, hTd, map_mul, map_mul]
        group
      have hgl : g⁻¹ * (yc * yd * yd) * g =
          GeneralLinearGroup.scalar (Fin 3) (lc * ld * ld) := by
        calc g⁻¹ * (yc * yd * yd) * g = (g⁻¹ * yc * g) * (g⁻¹ * yd * g) * (g⁻¹ * yd * g) := by
              group
          _ = GeneralLinearGroup.scalar (Fin 3) (lc * ld * ld) *
                diagUnits 1 (sc * sd * sd) (tc * td * td) := by
              rw [hgc, hgd, Sec4.scalar_diagUnits_mul, Sec4.scalar_diagUnits_mul]
          _ = GeneralLinearGroup.scalar (Fin 3) (lc * ld * ld) := by
              rw [htc', htd', ← mul_inv, ← mul_inv, hk, inv_one, SL3Lines.diagUnits_one_one_one,
                mul_one]
      have hcda := hscal _ hxA _ _ hact hgl
      apply hnotin
      have e2 : c = (c * d * d) * (d⁻¹ * d⁻¹) := by group
      rw [e2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcda)
        (Subgroup.mem_sup_right (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers d))
          (Subgroup.inv_mem _ (Subgroup.mem_zpowers d))))
  have htype := type123_two_of_frame (q := 2 ^ f) hτ₀ hτ₀1 (hroots sc hsc') (hroots tc htc) hsctc
    hgc
  exact ⟨hAL hcA, true, 2, f, K, inferInstance, hPi, hmod, e, yc, Sec4.mem_glPi_true _ _, htype,
    fun z => hyc z⟩

end Config

end CFSG.RankThree.PartTwo.Sec21.Item2119EndProof

module

public import CFSG.RankThree.PartOne.SEITZ6.G2MU
public import CFSG.RankThree.PartOne.SEITZ3.MaxDefs
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] noncomputable def Tg (K : Type) [Field K] : Subgroup (adjointGroup .G2 K) :=
  ⨆ i, torus (τ := .G2) K i

theorem torusElement_conj_xp (i : Fin (Tag.rank .G2)) {p : ℕ} (hp : p < 12) (t : Kˣ) (c : K) :
    torusElement .G2 K i t * xp p c * (torusElement .G2 K i t)⁻¹ =
      xp p (((t ^ (∑ j, (Tag.G2).cartan i j * (rt p) j) : Kˣ) : K) * c) := by
  have hγ : IsRoot .G2 (rt p) := isRoot_rt hp
  have := (rootOperatorFamily .G2).torusElement_mul_eltElement_mul_inv (K := K) i t
    ⟨rt p, hγ⟩ c
  rw [← xPar_of_isRoot hγ] at this
  rw [← xPar_of_isRoot hγ] at this
  exact this

theorem torusElement_mul' (i : Fin (Tag.rank .G2)) (s s' : Kˣ) :
    torusElement .G2 K i (s * s') = torusElement .G2 K i s * torusElement .G2 K i s' :=
  (torusHom K i).map_mul s s'

theorem torusElement_comm (i j : Fin (Tag.rank .G2)) (s s' : Kˣ) :
    torusElement .G2 K i s * torusElement .G2 K j s' =
      torusElement .G2 K j s' * torusElement .G2 K i s :=
  (torus_commute (mem_torus.2 ⟨s, rfl⟩) (mem_torus.2 ⟨s', rfl⟩)).eq

theorem mem_Tg_iff {t : adjointGroup .G2 K} :
    t ∈ Tg K ↔ ∃ a b : Kˣ, t = torusElement .G2 K e0 a * torusElement .G2 K e1 b := by
  constructor
  · intro ht
    refine Subgroup.iSup_induction (fun i => torus (τ := .G2) K i)
      (C := fun t => ∃ a b : Kˣ,
        t = torusElement .G2 K e0 a * torusElement .G2 K e1 b) ht ?_ ?_ ?_
    · intro i x hx
      obtain ⟨s, rfl⟩ := mem_torus.1 hx
      fin_cases i
      · exact ⟨s, 1, by simp [torusElement_one_eq, e0]⟩
      · exact ⟨1, s, by simp [torusElement_one_eq, e1]⟩
    · exact ⟨1, 1, by simp [torusElement_one_eq]⟩
    · rintro x y ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
      refine ⟨a * a', b * b', ?_⟩
      rw [torusElement_mul', torusElement_mul']
      calc torusElement .G2 K e0 a * torusElement .G2 K e1 b *
            (torusElement .G2 K e0 a' * torusElement .G2 K e1 b')
          = torusElement .G2 K e0 a * (torusElement .G2 K e1 b *
            torusElement .G2 K e0 a') * torusElement .G2 K e1 b' := by group
        _ = _ := by rw [torusElement_comm e1 e0 b a']; group
  · rintro ⟨a, b, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_iSup_of_mem e0 (mem_torus.2 ⟨a, rfl⟩))
      (Subgroup.mem_iSup_of_mem e1 (mem_torus.2 ⟨b, rfl⟩))

theorem Tg_conj_xp {t : adjointGroup .G2 K} (ht : t ∈ Tg K) {p : ℕ} (hp : p < 12) :
    ∃ μ : K, μ ≠ 0 ∧ ∀ c, t * xp p c * t⁻¹ = xp p (μ * c) := by
  obtain ⟨a, b, rfl⟩ := mem_Tg_iff.1 ht
  refine ⟨(((a ^ (∑ j, (Tag.G2).cartan e0 j * (rt p) j) : Kˣ) : K)) *
    (((b ^ (∑ j, (Tag.G2).cartan e1 j * (rt p) j) : Kˣ) : K)), mul_ne_zero (Units.ne_zero _)
      (Units.ne_zero _), fun c => ?_⟩
  rw [show torusElement .G2 K e0 a * torusElement .G2 K e1 b * xp p c *
      (torusElement .G2 K e0 a * torusElement .G2 K e1 b)⁻¹ =
      torusElement .G2 K e0 a * (torusElement .G2 K e1 b * xp p c *
        (torusElement .G2 K e1 b)⁻¹) * (torusElement .G2 K e0 a)⁻¹ by group,
    torusElement_conj_xp e1 hp, torusElement_conj_xp e0 hp, mul_assoc]

theorem torus_conj_xp7 (a b : Kˣ) (c : K) :
    (torusElement .G2 K e0 a * torusElement .G2 K e1 b) * xp 7 c *
      (torusElement .G2 K e0 a * torusElement .G2 K e1 b)⁻¹ = xp 7 ((a : K) * c) := by
  rw [show torusElement .G2 K e0 a * torusElement .G2 K e1 b * xp 7 c *
      (torusElement .G2 K e0 a * torusElement .G2 K e1 b)⁻¹ =
      torusElement .G2 K e0 a * (torusElement .G2 K e1 b * xp 7 c *
        (torusElement .G2 K e1 b)⁻¹) * (torusElement .G2 K e0 a)⁻¹ by group,
    torusElement_conj_xp e1 (by norm_num), torusElement_conj_xp e0 (by norm_num)]
  have h0 : (∑ j, (Tag.G2).cartan e0 j * (rt 7) j) = 1 := by decide +kernel
  have h1 : (∑ j, (Tag.G2).cartan e1 j * (rt 7) j) = 0 := by decide +kernel
  rw [h0, h1]
  simp

theorem Tg_conj_Up [CharP K 2] {t g : adjointGroup .G2 K} (ht : t ∈ Tg K) (hg : g ∈ Up K) :
    t * g * t⁻¹ ∈ Up K := by
  obtain ⟨a, b, rfl⟩ := mem_Up_iff.1 hg
  obtain ⟨μ, -, h7⟩ := Tg_conj_xp ht (p := 7) (by norm_num)
  obtain ⟨ν, -, h1⟩ := Tg_conj_xp ht (p := 1) (by norm_num)
  rw [show t * (xp 7 a * xp 1 b) * t⁻¹ = (t * xp 7 a * t⁻¹) * (t * xp 1 b * t⁻¹) by group,
    h7, h1]
  exact mem_Up_iff.2 ⟨_, _, rfl⟩

theorem Tg_conj_Up_iff [CharP K 2] {t g : adjointGroup .G2 K} (ht : t ∈ Tg K) :
    g ∈ Up K ↔ t * g * t⁻¹ ∈ Up K := by
  refine ⟨Tg_conj_Up ht, fun h => ?_⟩
  have := Tg_conj_Up (Subgroup.inv_mem _ ht) h
  rwa [show t⁻¹ * (t * g * t⁻¹) * t⁻¹⁻¹ = g by group] at this

theorem torusElement_pow' (i : Fin (Tag.rank .G2)) (s : Kˣ) (m : ℕ) :
    torusElement .G2 K i s ^ m = torusElement .G2 K i (s ^ m) :=
  ((torusHom K i).map_pow s m).symm

theorem card_sub_one_odd [Finite K] [CharP K 2] : Odd (Nat.card K - 1) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  have hev : Even (2 ^ (n : ℕ)) := (Nat.even_pow' n.ne_zero).2 even_two
  exact Nat.Even.sub_odd (Nat.one_le_two_pow) hev odd_one

theorem unit_pow_card_sub_one [Finite K] (a : Kˣ) : a ^ (Nat.card K - 1) = 1 := by
  have : Fintype K := Fintype.ofFinite K
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one _ a.ne_zero

theorem Tg_odd_order [Finite K] [CharP K 2] {t : adjointGroup .G2 K} (ht : t ∈ Tg K) :
    Odd (orderOf t) := by
  obtain ⟨a, b, rfl⟩ := mem_Tg_iff.1 ht
  have hcomm : Commute (torusElement .G2 K e0 a) (torusElement .G2 K e1 b) :=
    torusElement_comm e0 e1 a b
  have h : (torusElement .G2 K e0 a * torusElement .G2 K e1 b) ^ (Nat.card K - 1) = 1 := by
    rw [hcomm.mul_pow, torusElement_pow', torusElement_pow', unit_pow_card_sub_one,
      unit_pow_card_sub_one, torusElement_one_eq, torusElement_one_eq, mul_one]
  exact Odd.of_dvd_nat card_sub_one_odd (orderOf_dvd_of_pow_eq_one h)

@[expose] noncomputable def Wg (K : Type) [Field K] : adjointGroup .G2 K :=
  weylElement .G2 K e0 * weylElement .G2 K e1

theorem Wg_conj_xp [CharP K 2] {p q r : ℕ} (hp : p < 12) (hq : q < 12)
    (h1 : reflect .G2 e1 (rt p) = rt q) (h2 : reflect .G2 e0 (rt q) = rt r) (c : K) :
    Wg K * xp p c * (Wg K)⁻¹ = xp r c := by
  rw [Wg, show weylElement .G2 K e0 * weylElement .G2 K e1 * xp p c *
      (weylElement .G2 K e0 * weylElement .G2 K e1)⁻¹ =
      weylElement .G2 K e0 * (weylElement .G2 K e1 * xp p c * (weylElement .G2 K e1)⁻¹) *
        (weylElement .G2 K e0)⁻¹ by group,
    weylElement_conj_xp e1 hp h1, weylElement_conj_xp e0 hq h2]

theorem Wg_xp0 [CharP K 2] (c : K) : Wg K * xp 0 c * (Wg K)⁻¹ = xp 7 c :=
  Wg_conj_xp (q := 3) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) c

theorem Wg_xp2 [CharP K 2] (c : K) : Wg K * xp 2 c * (Wg K)⁻¹ = xp 10 c :=
  Wg_conj_xp (q := 6) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) c

theorem Wg_xp8 [CharP K 2] (c : K) : Wg K * xp 8 c * (Wg K)⁻¹ = xp 1 c :=
  Wg_conj_xp (q := 4) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) c

theorem Wg_xp11 [CharP K 2] (c : K) : Wg K * xp 11 c * (Wg K)⁻¹ = xp 5 c :=
  Wg_conj_xp (q := 9) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) c

theorem pinnedX_xp [CharP K 2] {q : ℕ} (hq : q < 12) (c : K) :
    pinnedX .G2 K (rt q) c = ((xp q c : adjointGroup .G2 K) : ModGL .G2 K) := by
  rw [pinnedX_eq_eltVec _ (isRoot_rt hq)]
  have hs : (((rootOperatorFamily .G2).pinnedFamilySign (rt q) : ℤ) : K) = 1 := by
    rcases (rootOperatorFamily .G2).pinnedFamilySign_eq (rt q) with h | h <;> rw [h] <;>
      simp [CharTwo.neg_eq]
  rw [hs, one_mul, (rootOperatorFamily .G2).eltVec_of_isRoot (isRoot_rt hq)]
  simp [xp, xPar_of_isRoot (isRoot_rt hq)]

theorem rootSL2_uSL_xp [CharP K 2] {p : ℕ} (hp : p < 12) (c : K) :
    rootSL2 .G2 K (rt p) (uSL c) = ((xp p c : adjointGroup .G2 K) : ModGL .G2 K) := by
  rw [rootSL2_uSL_of_charTwo (isRoot_rt hp), pinnedX_xp hp]

theorem rootSL2_vSL_xp [CharP K 2] {p q : ℕ} (hp : p < 12) (hq : q < 12) (h : rt q = -rt p)
    (c : K) :
    rootSL2 .G2 K (rt p) (vSL c) = ((xp q c : adjointGroup .G2 K) : ModGL .G2 K) := by
  rw [rootSL2_vSL_of_charTwo (isRoot_rt hp), ← pinnedX_xp hq]
  exact congrArg (fun v => pinnedX .G2 K v c) h.symm

theorem g2a_eq : g2a = rt 0 := by decide +kernel

theorem g2v_eq : g2v = rt 8 := by decide +kernel

theorem rt2_neg : rt 2 = -rt 0 := by decide +kernel

theorem rt11_neg : rt 11 = -rt 8 := by decide +kernel

theorem a1a1Hom_uSL_inl [CharP K 2] (c : K) : a1a1Hom K (uSL c, 1) = xp 0 c := by
  apply Subtype.ext
  rw [a1a1Hom_apply_inl, g2a_eq]
  exact rootSL2_uSL_xp (by norm_num) c

theorem a1a1Hom_vSL_inl [CharP K 2] (c : K) : a1a1Hom K (vSL c, 1) = xp 2 c := by
  apply Subtype.ext
  rw [a1a1Hom_apply_inl, g2a_eq]
  exact rootSL2_vSL_xp (by norm_num) (by norm_num) rt2_neg c

theorem a1a1Hom_uSL_inr [CharP K 2] (c : K) : a1a1Hom K (1, uSL c) = xp 8 c := by
  apply Subtype.ext
  rw [a1a1Hom_apply_inr, g2v_eq]
  exact rootSL2_uSL_xp (by norm_num) c

theorem a1a1Hom_vSL_inr [CharP K 2] (c : K) : a1a1Hom K (1, vSL c) = xp 11 c := by
  apply Subtype.ext
  rw [a1a1Hom_apply_inr, g2v_eq]
  exact rootSL2_vSL_xp (by norm_num) (by norm_num) rt11_neg c

@[expose] noncomputable def Lp (K : Type) [Field K] : Subgroup (adjointGroup .G2 K) :=
  (stdA1A1 K).map (MulAut.conj (Wg K)).toMonoidHom

@[expose] noncomputable def phiP (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
      adjointGroup .G2 K :=
  (MulAut.conj (Wg K)).toMonoidHom.comp (a1a1Hom K)

theorem range_phiP : (phiP K).range = Lp K := by
  unfold phiP Lp stdA1A1
  rw [MonoidHom.range_comp]

theorem phiP_injective [CharP K 2] : Function.Injective (phiP K) :=
  (MulAut.conj (Wg K)).injective.comp (a1a1Hom_injective)

theorem phiP_apply (A B : Matrix.SpecialLinearGroup (Fin 2) K) :
    phiP K (A, B) = Wg K * a1a1Hom K (A, B) * (Wg K)⁻¹ := rfl

theorem xp7_mem_Lp [CharP K 2] (c : K) : xp 7 c ∈ Lp K := by
  rw [← range_phiP, ← Wg_xp0]
  exact ⟨(uSL c, 1), by rw [phiP_apply, a1a1Hom_uSL_inl]⟩

theorem xp10_mem_Lp [CharP K 2] (c : K) : xp 10 c ∈ Lp K := by
  rw [← range_phiP, ← Wg_xp2]
  exact ⟨(vSL c, 1), by rw [phiP_apply, a1a1Hom_vSL_inl]⟩

theorem xp1_mem_Lp [CharP K 2] (c : K) : xp 1 c ∈ Lp K := by
  rw [← range_phiP, ← Wg_xp8]
  exact ⟨(1, uSL c), by rw [phiP_apply, a1a1Hom_uSL_inr]⟩

theorem xp5_mem_Lp [CharP K 2] (c : K) : xp 5 c ∈ Lp K := by
  rw [← range_phiP, ← Wg_xp11]
  exact ⟨(1, vSL c), by rw [phiP_apply, a1a1Hom_vSL_inr]⟩

theorem torusElement_e0_eq (t : Kˣ) :
    torusElement .G2 K e0 t =
      xp 0 (t : K) * xp 2 (-((t⁻¹ : Kˣ) : K)) * xp 0 (t : K) * (weylElement .G2 K e0)⁻¹ := by
  have h := weylElement_xPar (F := rootOperatorFamily .G2) (K := K) e0 t
  rw [CFSG.LieType.Steinberg.weylElement] at h
  simp only [xp, rt0_eq, rt2_eq]
  rw [h, mul_inv_cancel_right]

theorem xp0_mem_std [CharP K 2] (c : K) : xp 0 c ∈ stdA1A1 K :=
  ⟨(uSL c, 1), a1a1Hom_uSL_inl c⟩

theorem xp2_mem_std [CharP K 2] (c : K) : xp 2 c ∈ stdA1A1 K :=
  ⟨(vSL c, 1), a1a1Hom_vSL_inl c⟩

theorem torus0_mem_std [CharP K 2] (s : Kˣ) : torusElement .G2 K e0 s ∈ stdA1A1 K := by
  rw [torusElement_e0_eq, weylElement_e0_eq]
  exact mul_mem (mul_mem (mul_mem (xp0_mem_std _) (xp2_mem_std _)) (xp0_mem_std _))
    (inv_mem (mul_mem (mul_mem (xp0_mem_std _) (xp2_mem_std _)) (xp0_mem_std _)))

theorem torus1_mem_Lp [CharP K 2] (b : Kˣ) : torusElement .G2 K e1 b ∈ Lp K := by
  rw [torusElement_e1_eq, weylElement_e1_eq]
  exact mul_mem (mul_mem (mul_mem (xp1_mem_Lp _) (xp5_mem_Lp _)) (xp1_mem_Lp _))
    (inv_mem (mul_mem (mul_mem (xp1_mem_Lp _) (xp5_mem_Lp _)) (xp1_mem_Lp _)))

theorem weylElement_torus (i j : Fin (Tag.rank .G2)) (t : Kˣ) :
    weylElement .G2 K i * torusElement .G2 K j t * (weylElement .G2 K i)⁻¹ =
      torusElement .G2 K j t * torusElement .G2 K i (t ^ (-(Tag.G2).cartan j i)) := by
  apply Subtype.ext
  exact weylElt_one_mul_torusElt_mul_inv .G2 K i j t

theorem Wg_torus0 (s : Kˣ) :
    Wg K * torusElement .G2 K e0 s * (Wg K)⁻¹ =
      torusElement .G2 K e0 (s ^ 2) * torusElement .G2 K e1 s := by
  have h1 := weylElement_torus (K := K) e1 e0 s
  have h2 := weylElement_torus (K := K) e0 e0 s
  have h3 := weylElement_torus (K := K) e0 e1 s
  have c01 : (Tag.G2).cartan e0 e1 = -1 := by decide +kernel
  have c00 : (Tag.G2).cartan e0 e0 = 2 := by decide +kernel
  have c10 : (Tag.G2).cartan e1 e0 = -3 := by decide +kernel
  rw [c01] at h1
  rw [c00] at h2
  rw [c10] at h3
  have h1' : weylElement .G2 K e1 * torusElement .G2 K e0 s * (weylElement .G2 K e1)⁻¹ =
      torusElement .G2 K e0 s * torusElement .G2 K e1 s := by
    rw [h1]
    simp
  have h3' : weylElement .G2 K e0 * torusElement .G2 K e1 s * (weylElement .G2 K e0)⁻¹ =
      torusElement .G2 K e1 s * torusElement .G2 K e0 (s ^ (3 : ℤ)) := by
    rw [h3]
    norm_num
  calc Wg K * torusElement .G2 K e0 s * (Wg K)⁻¹
      = weylElement .G2 K e0 * (weylElement .G2 K e1 * torusElement .G2 K e0 s *
          (weylElement .G2 K e1)⁻¹) * (weylElement .G2 K e0)⁻¹ := by rw [Wg]; group
    _ = weylElement .G2 K e0 * (torusElement .G2 K e0 s * torusElement .G2 K e1 s) *
          (weylElement .G2 K e0)⁻¹ := by rw [h1']
    _ = (weylElement .G2 K e0 * torusElement .G2 K e0 s * (weylElement .G2 K e0)⁻¹) *
          (weylElement .G2 K e0 * torusElement .G2 K e1 s * (weylElement .G2 K e0)⁻¹) := by
        group
    _ = (torusElement .G2 K e0 s * torusElement .G2 K e0 (s ^ (-2 : ℤ))) *
          (torusElement .G2 K e1 s * torusElement .G2 K e0 (s ^ (3 : ℤ))) := by
        rw [h2, h3']
    _ = (torusElement .G2 K e0 s * torusElement .G2 K e0 (s ^ (-2 : ℤ)) *
          torusElement .G2 K e0 (s ^ (3 : ℤ))) * torusElement .G2 K e1 s := by
        rw [torusElement_comm e1 e0 s (s ^ (3 : ℤ))]
        group
    _ = torusElement .G2 K e0 (s ^ 2) * torusElement .G2 K e1 s := by
        rw [← torusElement_mul', ← torusElement_mul']
        congr 2
        group

theorem Tg_le_Lp [CharP K 2] [Finite K] : Tg K ≤ Lp K := by
  intro t ht
  obtain ⟨a, b, rfl⟩ := mem_Tg_iff.1 ht
  refine Subgroup.mul_mem _ ?_ (torus1_mem_Lp b)
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (a : K)
  have hr0 : r ≠ 0 := fun h => a.ne_zero (by rw [hr, h, mul_zero])
  set s : Kˣ := Units.mk0 r hr0 with hs
  have has : a = s ^ 2 := Units.ext (by simp [s, hr, sq])
  rw [has]
  have hW : Wg K * torusElement .G2 K e0 s * (Wg K)⁻¹ ∈ Lp K :=
    ⟨_, torus0_mem_std s, rfl⟩
  rw [Wg_torus0] at hW
  have := Subgroup.mul_mem _ hW (Subgroup.inv_mem _ (torus1_mem_Lp s))
  simpa using this

end CFSG.RankThree.PartOne.SEITZ6

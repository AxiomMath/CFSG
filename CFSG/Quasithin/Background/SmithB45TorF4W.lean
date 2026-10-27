module

public import CFSG.Quasithin.Background.SmithB42F4Lang
public import CFSG.Quasithin.Background.SmithB45TorOrbit

public noncomputable section

namespace CFSG.Quasithin.B45Tor

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.Quasithin.B42F4
open scoped commutatorElement

section Transport

variable {G G' : Type*} [Group G] [Group G'] {R S : Subgroup G} (φ : S →* G')

theorem mem_normalizer_map {g : G} (hgS : g ∈ S) (hg : g ∈ Subgroup.normalizer (R : Set G)) :
    φ ⟨g, hgS⟩ ∈ Subgroup.normalizer (((R.subgroupOf S).map φ : Subgroup G') : Set G') := by
  refine Subgroup.le_normalizer_map φ ⟨⟨g, hgS⟩, ?_, rfl⟩
  refine Subgroup.mem_normalizer_iff.2 fun r => ?_
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.1 hg r

theorem invOn_map {c : G} (hcS : c ∈ S) (hc : InvOn R c) :
    InvOn ((R.subgroupOf S).map φ) (φ ⟨c, hcS⟩) := by
  rintro _ ⟨r, hr, rfl⟩
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
  congr 1
  exact Subtype.ext (hc r hr)

theorem agreeOn_map {x y : G} (hxS : x ∈ S) (hyS : y ∈ S) (h : AgreeOn R x y) :
    AgreeOn ((R.subgroupOf S).map φ) (φ ⟨x, hxS⟩) (φ ⟨y, hyS⟩) := by
  rintro _ ⟨r, hr, rfl⟩
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (h r hr)

theorem commutatorElement_mem' {i j : G} (hi : i ∈ S) (hj : j ∈ S) : ⁅i, j⁆ ∈ S := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hi hj) (inv_mem hi)) (inv_mem hj)

theorem IsQ8Data.map {i j h : G} (hd : IsQ8Data R i j h) (hi : i ∈ S) (hj : j ∈ S) (hh : h ∈ S) :
    IsQ8Data ((R.subgroupOf S).map φ) (φ ⟨i, hi⟩) (φ ⟨j, hj⟩) (φ ⟨h, hh⟩) := by
  refine ⟨mem_normalizer_map φ hi hd.mem_i, mem_normalizer_map φ hj hd.mem_j,
    mem_normalizer_map φ hh hd.mem_h, ?_, ?_, ?_, ?_, ?_⟩
  · have := invOn_map φ (commutatorElement_mem' hi hj) hd.inv_comm
    rwa [show (⟨⁅i, j⁆, commutatorElement_mem' hi hj⟩ : S) =
      ⁅(⟨i, hi⟩ : S), (⟨j, hj⟩ : S)⁆ from rfl, map_commutatorElement] at this
  · have := invOn_map φ (mul_mem hi hi) hd.inv_ii
    rwa [show (⟨i * i, mul_mem hi hi⟩ : S) = ⟨i, hi⟩ * ⟨i, hi⟩ from rfl, map_mul] at this
  · have := invOn_map φ (mul_mem hj hj) hd.inv_jj
    rwa [show (⟨j * j, mul_mem hj hj⟩ : S) = ⟨j, hj⟩ * ⟨j, hj⟩ from rfl, map_mul] at this
  · have := agreeOn_map φ (mul_mem (mul_mem hh hi) (inv_mem hh)) hj hd.conj_i
    rwa [show (⟨h * i * h⁻¹, mul_mem (mul_mem hh hi) (inv_mem hh)⟩ : S) =
      ⟨h, hh⟩ * ⟨i, hi⟩ * ⟨h, hh⟩⁻¹ from rfl, map_mul, map_mul, map_inv] at this
  · have := agreeOn_map φ (mul_mem (mul_mem hh hj) (inv_mem hh)) (mul_mem hi hj) hd.conj_j
    rwa [show (⟨h * j * h⁻¹, mul_mem (mul_mem hh hj) (inv_mem hh)⟩ : S) =
      ⟨h, hh⟩ * ⟨j, hj⟩ * ⟨h, hh⟩⁻¹ from rfl, show (⟨i * j, mul_mem hi hj⟩ : S) =
      ⟨i, hi⟩ * ⟨j, hj⟩ from rfl, map_mul, map_mul, map_mul, map_inv] at this

theorem IsGL23Data.map {i j h t : G} (hd : IsGL23Data R i j h t) (hi : i ∈ S) (hj : j ∈ S)
    (hh : h ∈ S) (ht : t ∈ S) :
    IsGL23Data ((R.subgroupOf S).map φ) (φ ⟨i, hi⟩) (φ ⟨j, hj⟩) (φ ⟨h, hh⟩) (φ ⟨t, ht⟩) := by
  refine ⟨hd.toIsQ8Data.map φ hi hj hh, mem_normalizer_map φ ht hd.mem_t, ?_⟩
  set I : S := ⟨i, hi⟩
  set J : S := ⟨j, hj⟩
  set Hh : S := ⟨h, hh⟩
  set T : S := ⟨t, ht⟩
  have hlist : ∀ a' ∈ [1, φ I, φ J, φ I * φ J], ∃ a ∈ [1, i, j, i * j], ∃ ha : a ∈ S,
      a' = φ ⟨a, ha⟩ := by
    intro a' ha'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha'
    rcases ha' with rfl | rfl | rfl | rfl
    · exact ⟨1, by simp, one_mem _, by rw [← map_one φ]; rfl⟩
    · exact ⟨i, by simp, hi, rfl⟩
    · exact ⟨j, by simp, hj, rfl⟩
    · exact ⟨i * j, by simp, mul_mem hi hj, by rw [← map_mul]; rfl⟩
  intro a' ha' b' hb'
  obtain ⟨a, ha, haS, rfl⟩ := hlist a' ha'
  obtain ⟨b, hb, hbS, rfl⟩ := hlist b' hb'
  obtain ⟨h12, m, hm⟩ := hd.comm a ha b hb
  set c : S := ⁅⟨a, haS⟩⁻¹ * Hh, ⟨b, hbS⟩⁻¹ * T⁆ with hc
  have hcv : (c : G) = ⁅a⁻¹ * h, b⁻¹ * t⁆ := rfl
  have hφc : ⁅(φ ⟨a, haS⟩)⁻¹ * φ Hh, (φ ⟨b, hbS⟩)⁻¹ * φ T⁆ = φ c := by
    rw [hc, map_commutatorElement, map_mul, map_mul, map_inv, map_inv]
  rw [hφc]
  refine ⟨?_, m, ?_⟩
  · rw [← map_pow]
    have : c ^ 12 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hcv, h12]; rfl)
    rw [this, map_one]
  · have hcS : (c : G) * i * (c : G)⁻¹ ∈ S := mul_mem (mul_mem c.2 hi) (inv_mem c.2)
    have hmS : i ^ m * j ∈ S := mul_mem (zpow_mem hi m) hj
    have := agreeOn_map φ hcS hmS (by rw [hcv]; exact hm)
    rwa [show (⟨(c : G) * i * (c : G)⁻¹, hcS⟩ : S) = c * I * c⁻¹ from rfl,
      show (⟨i ^ m * j, hmS⟩ : S) = I ^ m * J from rfl, map_mul, map_mul, map_inv, map_mul,
      map_zpow] at this

end Transport

section Words


@[expose] def f4wI : List (Fin ReeTag.F4.tag.rank) := [2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 1, 3]

@[expose] def f4wJ : List (Fin ReeTag.F4.tag.rank) := [1, 0, 2, 1, 0, 2, 3, 2, 1, 0, 2, 3]

@[expose] def f4wH : List (Fin ReeTag.F4.tag.rank) :=
  [0, 1, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2]

@[expose] def f4wT : List (Fin ReeTag.F4.tag.rank) := [1, 2]

@[expose] def f4wW0 : List (Fin ReeTag.F4.tag.rank) :=
  [0, 1, 0, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3]

@[expose] def f4wV : Fin 4 → List (Fin ReeTag.F4.tag.rank) := ![[], f4wI, f4wJ, f4wI ++ f4wJ]

@[expose] def f4wCr : Fin 4 → Fin 4 → List (Fin ReeTag.F4.tag.rank) :=
  ![![[0, 1, 0, 2, 1, 2, 3, 2], [0, 2, 1, 0, 2, 3, 2, 1],
      [1, 0, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3], [1, 2, 1, 2, 3, 2, 1, 0]],
    ![[0, 1, 0, 2, 1, 2, 3, 2], [1, 0, 2, 1, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2],
      [0, 3, 2, 1, 0, 2, 1, 2], [1, 2, 1, 2, 3, 2, 1, 0]],
    ![[0, 2, 1, 0, 2, 3, 2, 1], [0, 1, 0, 2, 1, 2, 3, 2],
      [0, 1, 2, 1, 0, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 2], [0, 3, 2, 1, 0, 2, 1, 2]],
    ![[0, 2, 1, 0, 2, 3, 2, 1], [2, 1, 0, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1],
      [1, 2, 1, 2, 3, 2, 1, 0], [0, 3, 2, 1, 0, 2, 1, 2]]]

@[expose] def f4wM : Fin 4 → Fin 4 → ℕ :=
  ![![3, 1, 1, 3], ![3, 1, 1, 3], ![1, 3, 3, 1], ![1, 3, 3, 1]]

@[expose] def f4Lw (l : List (Fin ReeTag.F4.tag.rank)) : List (List ℤ) :=
  lword ReeTag.F4.tag.rank (cartanList ReeTag.F4.tag) (l.map Fin.val)

@[expose] def f4wC (la lb : List (Fin ReeTag.F4.tag.rank)) : List (Fin ReeTag.F4.tag.rank) :=
  la.reverse ++ f4wH ++ lb.reverse ++ f4wT ++ f4wH.reverse ++ la ++ f4wT.reverse ++ lb

theorem wordProd_f4wC (la lb : List (Fin ReeTag.F4.tag.rank)) :
    (coxeterSystem ReeTag.F4.tag).wordProd (f4wC la lb) =
      ⁅((coxeterSystem ReeTag.F4.tag).wordProd la)⁻¹ * (coxeterSystem ReeTag.F4.tag).wordProd f4wH,
        ((coxeterSystem ReeTag.F4.tag).wordProd lb)⁻¹ *
          (coxeterSystem ReeTag.F4.tag).wordProd f4wT⁆ := by
  simp only [f4wC, CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_reverse,
    commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]

theorem wordProd_replicate (l : List (Fin ReeTag.F4.tag.rank)) (n : ℕ) :
    (coxeterSystem ReeTag.F4.tag).wordProd (List.replicate n l).flatten =
      (coxeterSystem ReeTag.F4.tag).wordProd l ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, CoxeterSystem.wordProd_append, ih, pow_succ']

theorem f4wW0_eq : (coxeterSystem ReeTag.F4.tag).wordProd f4wW0 = w0 := rfl

theorem f4_twisted {w : WeylGroup ReeTag.F4.tag}
    (hw : w = CFSG.RankThree.PartOne.KLR.wPhi4m ∨ w = CFSG.RankThree.PartOne.KLR.wPhi4p)
    {l : List (Fin ReeTag.F4.tag.rank)} (hl : l = f4wI ∨ l = f4wJ ∨ l = f4wH ∨ l = f4wT) :
    w * ReeTag.F4.weylPerm ((coxeterSystem ReeTag.F4.tag).wordProd l) * w⁻¹ =
      (coxeterSystem ReeTag.F4.tag).wordProd l := by
  rw [mul_inv_eq_iff_eq_mul, weylPerm_wordProd, map_perm_eq]
  rcases hw with rfl | rfl <;> rcases hl with rfl | rfl | rfl | rfl <;>
    first
      | (rw [CFSG.RankThree.PartOne.KLR.wPhi4m, ← CoxeterSystem.wordProd_append,
          ← CoxeterSystem.wordProd_append]
         exact wordProd_eq_of_lword_eq (by decide +kernel))
      | (rw [CFSG.RankThree.PartOne.KLR.wPhi4p, ← CoxeterSystem.wordProd_append,
          ← CoxeterSystem.wordProd_append]
         exact wordProd_eq_of_lword_eq (by decide +kernel))

theorem f4_relations :
    (coxeterSystem ReeTag.F4.tag).wordProd (f4wI ++ f4wI) =
        (coxeterSystem ReeTag.F4.tag).wordProd f4wW0 ∧
      (coxeterSystem ReeTag.F4.tag).wordProd (f4wJ ++ f4wJ) =
        (coxeterSystem ReeTag.F4.tag).wordProd f4wW0 ∧
      (coxeterSystem ReeTag.F4.tag).wordProd (f4wI ++ f4wJ ++ f4wI.reverse ++ f4wJ.reverse) =
        (coxeterSystem ReeTag.F4.tag).wordProd f4wW0 ∧
      (coxeterSystem ReeTag.F4.tag).wordProd (f4wH ++ f4wI ++ f4wH.reverse) =
        (coxeterSystem ReeTag.F4.tag).wordProd f4wJ ∧
      (coxeterSystem ReeTag.F4.tag).wordProd (f4wH ++ f4wJ ++ f4wH.reverse) =
        (coxeterSystem ReeTag.F4.tag).wordProd (f4wI ++ f4wJ) ∧
      (coxeterSystem ReeTag.F4.tag).wordProd (f4wH ++ f4wH ++ f4wH) =
        (coxeterSystem ReeTag.F4.tag).wordProd [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact wordProd_eq_of_lword_eq (by decide +kernel)

theorem f4wH_ne_one : (coxeterSystem ReeTag.F4.tag).wordProd f4wH ≠ 1 :=
  wordProd_ne_one_of_lget (M := lword 4 (cartanList ReeTag.F4.tag) (f4wH.map Fin.val)) rfl 0 0
    (by decide +kernel)

theorem f4_comm_check : ∀ x y : Fin 4,
    f4Lw (f4wC (f4wV x) (f4wV y)) = f4Lw (f4wCr x y) ∧
      f4Lw (List.replicate 6 (f4wCr x y)).flatten = f4Lw [] ∧
      f4Lw (f4wCr x y ++ f4wI ++ (f4wCr x y).reverse) =
        f4Lw ((List.replicate (f4wM x y) f4wI).flatten ++ f4wJ) := by
  decide +kernel

theorem f4_comm (x y : Fin 4) :
    ⁅((coxeterSystem ReeTag.F4.tag).wordProd (f4wV x))⁻¹ *
        (coxeterSystem ReeTag.F4.tag).wordProd f4wH,
      ((coxeterSystem ReeTag.F4.tag).wordProd (f4wV y))⁻¹ *
        (coxeterSystem ReeTag.F4.tag).wordProd f4wT⁆ ^ 6 = 1 ∧
    ⁅((coxeterSystem ReeTag.F4.tag).wordProd (f4wV x))⁻¹ *
        (coxeterSystem ReeTag.F4.tag).wordProd f4wH,
      ((coxeterSystem ReeTag.F4.tag).wordProd (f4wV y))⁻¹ *
        (coxeterSystem ReeTag.F4.tag).wordProd f4wT⁆ * (coxeterSystem ReeTag.F4.tag).wordProd f4wI *
      ⁅((coxeterSystem ReeTag.F4.tag).wordProd (f4wV x))⁻¹ *
        (coxeterSystem ReeTag.F4.tag).wordProd f4wH,
      ((coxeterSystem ReeTag.F4.tag).wordProd (f4wV y))⁻¹ *
        (coxeterSystem ReeTag.F4.tag).wordProd f4wT⁆⁻¹ =
      (coxeterSystem ReeTag.F4.tag).wordProd f4wI ^ f4wM x y *
        (coxeterSystem ReeTag.F4.tag).wordProd f4wJ := by
  obtain ⟨h1, h2, h3⟩ := f4_comm_check x y
  have e1 := wordProd_eq_of_lword_eq h1
  have e2 := wordProd_eq_of_lword_eq h2
  have e3 := wordProd_eq_of_lword_eq h3
  rw [← wordProd_f4wC, e1]
  refine ⟨?_, ?_⟩
  · rw [← wordProd_replicate, e2, CoxeterSystem.wordProd_nil]
  · rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append,
      CoxeterSystem.wordProd_reverse, CoxeterSystem.wordProd_append, wordProd_replicate] at e3
    exact e3

end Words

section Lifts

variable (L : Type) [Field L] [CharP L 2]

@[expose] def nuF4 : WeylGroup ReeTag.F4.tag →* ModGL ReeTag.F4.tag L where
  toFun := canonicalRep (coxeterSystem ReeTag.F4.tag) L
  map_one' := canonicalRep_one _ L
  map_mul' := fun v w => CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo v w

variable {L}

theorem nuF4_apply (v : WeylGroup ReeTag.F4.tag) :
    nuF4 L v = canonicalRep (coxeterSystem ReeTag.F4.tag) L v := rfl

omit [CharP L 2] in
theorem canonicalRep_conj_rootDiagUnit_F4 (w : WeylGroup ReeTag.F4.tag)
    (b : Fin ReeTag.F4.tag.rank → Lˣ) :
    canonicalRep (coxeterSystem ReeTag.F4.tag) L w * rootDiagUnit ReeTag.F4.tag b *
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)⁻¹ =
      rootDiagUnit ReeTag.F4.tag
        (fun i => rootChar b (w⁻¹ • (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ))) := by
  refine ((rootDiagUnit_eq_conj_canonicalRep_iff _ b w).2 fun v => ?_).symm
  conv_rhs => rw [← inv_smul_smul w v]
  set u := w • v
  conv_rhs => rw [pi_eq_sum_univ u]
  rw [Finset.smul_sum, rootChar_sum, rootChar]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : (fun j => if i = j then (1 : ℤ) else 0) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [e, smul_comm, rootChar_zsmul]

omit [CharP L 2] in
theorem canonicalRep_conj_mem_torusGroup_F4 [IsAlgClosed L] (w : WeylGroup ReeTag.F4.tag)
    {x : ModGL ReeTag.F4.tag L} (hx : x ∈ torusGroup ReeTag.F4.tag L) :
    canonicalRep (coxeterSystem ReeTag.F4.tag) L w * x *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)⁻¹ ∈ torusGroup ReeTag.F4.tag L := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  rw [canonicalRep_conj_rootDiagUnit_F4]
  exact rootDiagUnit_mem_torusGroup _

end Lifts

section Torsion

variable {L : Type} [Field L] [CharP L 2] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

variable (F) in
@[expose] def twTorsion (w : WeylGroup ReeTag.F4.tag) (p : ℕ) :
    Subgroup (ModGL ReeTag.F4.tag L) where
  carrier := {u | u ∈ torusGroup ReeTag.F4.tag L ∧
    u ∈ CFSG.RankThree.PartOne.KLR.twistedFixed F
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧ u ^ p = 1}
  mul_mem' := by
    rintro u v ⟨hu, hu', hup⟩ ⟨hv, hv', hvp⟩
    refine ⟨mul_mem hu hv, mul_mem hu' hv', ?_⟩
    have hc : Commute u v := (triangular_borel_structure.{0, 0} ReeTag.F4.tag L).1 u hu v hv
    rw [hc.mul_pow, hup, hvp, one_mul]
  one_mem' := ⟨one_mem _, one_mem _, one_pow p⟩
  inv_mem' := by
    rintro u ⟨hu, hu', hup⟩
    exact ⟨inv_mem hu, inv_mem hu', by rw [inv_pow, hup, inv_one]⟩

omit [CharP L 2] in
theorem twTorsion_comm {w : WeylGroup ReeTag.F4.tag} {p : ℕ} :
    ∀ x ∈ twTorsion F w p, ∀ y ∈ twTorsion F w p, x * y = y * x := fun x hx y hy =>
  (triangular_borel_structure.{0, 0} ReeTag.F4.tag L).1 x hx.1 y hy.1

theorem canonicalRep_mem_normalizer_twTorsion [IsAlgClosed L]
    (hF : CFSG.RankThree.PartOne.KLR.IsReeFrob a F)
    {w v : WeylGroup ReeTag.F4.tag} (hv : w * ReeTag.F4.weylPerm v * w⁻¹ = v) (p : ℕ) :
    canonicalRep (coxeterSystem ReeTag.F4.tag) L v ∈
      Subgroup.normalizer (twTorsion F w p : Set (ModGL ReeTag.F4.tag L)) := by
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L v with hn
  have hnF := canonicalRep_mem_twistedFixed (L := L) hF hv
  have hninv : n⁻¹ = canonicalRep (coxeterSystem ReeTag.F4.tag) L v⁻¹ :=
    CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_inv_of_charTwo v
  refine Subgroup.mem_normalizer_iff.2 fun u => ⟨fun hu => ?_, fun hu => ?_⟩
  · exact ⟨canonicalRep_conj_mem_torusGroup_F4 v hu.1, mul_mem (mul_mem hnF hu.2.1) (inv_mem hnF),
      by rw [conj_pow, hu.2.2, mul_one, mul_inv_cancel]⟩
  · have e : u = n⁻¹ * (n * u * n⁻¹) * n⁻¹⁻¹ := by group
    rw [e]
    refine ⟨?_, mul_mem (mul_mem (inv_mem hnF) hu.2.1) (inv_mem (inv_mem hnF)),
      by rw [conj_pow, hu.2.2, mul_one, mul_inv_cancel]⟩
    have := canonicalRep_conj_mem_torusGroup_F4 v⁻¹ hu.1
    rwa [← hninv] at this

omit [CharP L 2] in
theorem exists_injective_twTorsion {w : WeylGroup ReeTag.F4.tag} {p : ℕ}
    (hcol : ∀ b : Fin ReeTag.F4.tag.rank → Lˣ, (∀ i, b i ^ p = 1) →
      rootDiagUnit ReeTag.F4.tag b ∈ CFSG.RankThree.PartOne.KLR.twistedFixed F
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) → b 0 = 1 → b 1 = 1 → b = 1) :
    ∃ f : twTorsion F w p → rootsOfUnity p L × rootsOfUnity p L, Function.Injective f := by
  classical
  have hex : ∀ u : twTorsion F w p, ∃ b : Fin ReeTag.F4.tag.rank → Lˣ,
      (u : ModGL ReeTag.F4.tag L) = rootDiagUnit ReeTag.F4.tag b :=
    fun u => exists_rootDiagUnit_eq_of_mem_torusGroup u.2.1
  choose b hb using hex
  have hbp : ∀ u i, b u i ^ p = 1 := by
    intro u i
    have h1 : rootDiagUnit ReeTag.F4.tag (b u ^ p) = rootDiagUnit ReeTag.F4.tag 1 := by
      have e := map_pow (rootDiagUnitHom ReeTag.F4.tag L) (b u) p
      have e1 := map_one (rootDiagUnitHom ReeTag.F4.tag L)
      change rootDiagUnit ReeTag.F4.tag (b u ^ p) = rootDiagUnit ReeTag.F4.tag (b u) ^ p at e
      change rootDiagUnit ReeTag.F4.tag 1 = 1 at e1
      rw [e, ← hb u, u.2.2.2, e1]
    have h2 := congrFun (rootDiagUnit_injective h1) i
    simpa using h2
  let f : twTorsion F w p → rootsOfUnity p L × rootsOfUnity p L := fun u =>
    (⟨b u 0, (mem_rootsOfUnity p _).2 (hbp u 0)⟩, ⟨b u 1, (mem_rootsOfUnity p _).2 (hbp u 1)⟩)
  have hf : Function.Injective f := by
    intro u u' huu
    have h0 : b u 0 = b u' 0 := congrArg (fun z => ((z.1 : rootsOfUnity p L) : Lˣ)) huu
    have h1 : b u 1 = b u' 1 := congrArg (fun z => ((z.2 : rootsOfUnity p L) : Lˣ)) huu
    have hc : rootDiagUnit ReeTag.F4.tag (b u * (b u')⁻¹) =
        (u : ModGL ReeTag.F4.tag L) * (u' : ModGL ReeTag.F4.tag L)⁻¹ := by
      rw [hb u, hb u', rootDiagUnit_inv]
      exact map_mul (rootDiagUnitHom ReeTag.F4.tag L) _ _
    have hcF : rootDiagUnit ReeTag.F4.tag (b u * (b u')⁻¹) ∈
        CFSG.RankThree.PartOne.KLR.twistedFixed F
          (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) := by
      rw [hc]
      exact mul_mem u.2.2.1 (inv_mem u'.2.2.1)
    have hcp : ∀ i, (b u * (b u')⁻¹) i ^ p = 1 := fun i => by
      rw [Pi.mul_apply, Pi.inv_apply, mul_pow, inv_pow, hbp, hbp, inv_one, one_mul]
    have h1' := hcol _ hcp hcF (by rw [Pi.mul_apply, Pi.inv_apply, h0, mul_inv_cancel])
      (by rw [Pi.mul_apply, Pi.inv_apply, h1, mul_inv_cancel])
    have hbb : b u = b u' := mul_inv_eq_one.1 h1'
    exact Subtype.ext (by rw [hb u, hb u', hbb])
  exact ⟨f, hf⟩

omit [CharP L 2] in
theorem card_twTorsion_le {w : WeylGroup ReeTag.F4.tag} {p : ℕ} (hp : p.Prime)
    (hcol : ∀ b : Fin ReeTag.F4.tag.rank → Lˣ, (∀ i, b i ^ p = 1) →
      rootDiagUnit ReeTag.F4.tag b ∈ CFSG.RankThree.PartOne.KLR.twistedFixed F
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) → b 0 = 1 → b 1 = 1 → b = 1) :
    Nat.card (twTorsion F w p) ≤ p ^ 2 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨f, hf⟩ := exists_injective_twTorsion hcol
  calc Nat.card (twTorsion F w p) ≤ Nat.card (rootsOfUnity p L × rootsOfUnity p L) :=
        Nat.card_le_card_of_injective f hf
    _ = Nat.card (rootsOfUnity p L) ^ 2 := by rw [Nat.card_prod, sq]
    _ ≤ p ^ 2 := Nat.pow_le_pow_left (card_rootsOfUnity L p) 2


theorem le_card_twTorsion [IsAlgClosed L] {w : WeylGroup ReeTag.F4.tag} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hfin : Finite (twTorsion F w p))
    {Φ : rootsOfUnity p L × rootsOfUnity p L →* ModGL ReeTag.F4.tag L}
    (hΦ : Function.Injective Φ) (hΦT : Φ.range ≤ torusGroup ReeTag.F4.tag L)
    (hΦF : Φ.range ≤ CFSG.RankThree.PartOne.KLR.twistedFixed F
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) :
    p ^ 2 ≤ Nat.card (twTorsion F w p) := by
  have hp0 : (p : L) ≠ 0 := fun h0 => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
    ((CharP.cast_eq_zero_iff L 2 p).1 h0)).symm
  have : NeZero (p : L) := ⟨hp0⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  have hcard := hζ.card_rootsOfUnity
  have hmem : ∀ z, Φ z ∈ twTorsion F w p := fun z => by
    refine ⟨hΦT ⟨z, rfl⟩, hΦF ⟨z, rfl⟩, ?_⟩
    have hz : z ^ p = 1 := Prod.ext (Subtype.ext (by simpa using (mem_rootsOfUnity p _).1 z.1.2))
      (Subtype.ext (by simpa using (mem_rootsOfUnity p _).1 z.2.2))
    rw [← map_pow, hz, map_one]
  calc p ^ 2 = Nat.card (rootsOfUnity p L × rootsOfUnity p L) := by
        rw [Nat.card_prod, hcard, sq]
    _ ≤ Nat.card (twTorsion F w p) :=
        Nat.card_le_card_of_injective (fun z => ⟨Φ z, hmem z⟩)
          (fun z z' h => hΦ (congrArg Subtype.val h))

end Torsion

section Columns

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

omit [CharP L 2] [IsAlgClosed L] in
theorem eq_one_of_pow_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : Lˣ} (n : ℕ)
    (hx : x ^ p = 1) (hx' : x ^ (2 ^ n) = 1) : x = 1 := by
  have hg : Nat.gcd (2 ^ n) p = 1 :=
    Nat.Coprime.pow_left n ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have : x ^ Nat.gcd (2 ^ n) p = 1 := pow_gcd_eq_one.2 ⟨hx', hx⟩
  rwa [hg, pow_one] at this

omit [CharP L 2] [IsAlgClosed L] in
theorem rootChar_neg_single (b : Fin ReeTag.F4.tag.rank → Lˣ) (k : Fin ReeTag.F4.tag.rank) :
    rootChar b (-(Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) = (b k)⁻¹ := by
  rw [← zero_sub, rootChar_sub, rootChar_zero, CTTorus.rootChar_single, one_mul]

theorem eq_one_of_phi4m (hF : CFSG.RankThree.PartOne.KLR.IsReeFrob a F) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (b : Fin ReeTag.F4.tag.rank → Lˣ) (hbp : ∀ i, b i ^ p = 1)
    (hb : rootDiagUnit ReeTag.F4.tag b ∈ CFSG.RankThree.PartOne.KLR.twistedFixed F
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L CFSG.RankThree.PartOne.KLR.wPhi4m))
    (h0 : b 0 = 1) (h1 : b 1 = 1) : b = 1 := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  have hfix := (CFSG.RankThree.PartOne.KLR.rootDiagUnit_mem_twistedFixed_canonicalRep_iff hF _
    b).1 hb
  have hk : ∀ k : Fin ReeTag.F4.tag.rank,
      rootChar b (CFSG.RankThree.PartOne.KLR.wPhi4m •
        (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) =
      b (ReeTag.F4.perm k) ^ ReeTag.F4.relationExponent a (ReeTag.F4.perm k) := by
    intro k
    rw [hfix, CTTorus.rootChar_single]
    rfl
  have c1 : CFSG.RankThree.PartOne.KLR.wPhi4m • (Pi.single 1 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      -(Pi.single 1 1) := by
    funext l
    rw [CFSG.RankThree.PartOne.KLR.wPhi4m, CFSG.RankThree.PartOne.KLR.smul_single_eq_lget _ _ hW]
    fin_cases l <;> decide
  have c0 : CFSG.RankThree.PartOne.KLR.wPhi4m • (Pi.single 0 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      -(Pi.single 0 1) - Pi.single 1 1 - (2 : ℕ) • Pi.single 2 1 := by
    funext l
    rw [CFSG.RankThree.PartOne.KLR.wPhi4m, CFSG.RankThree.PartOne.KLR.smul_single_eq_lget _ _ hW]
    fin_cases l <;> decide
  have e1 := hk 1
  have e0 := hk 0
  rw [c1, rootChar_neg_single, h1, inv_one, show ReeTag.F4.perm 1 = 2 by decide,
    CFSG.RankThree.PartOne.KLR.relExp_short a _ (by decide)] at e1
  have h2 : b 2 = 1 := eq_one_of_pow_two_pow hp hp2 (a + 1) (hbp 2) e1.symm
  rw [c0, rootChar_sub, rootChar_sub, rootChar_neg_single, CTTorus.rootChar_single,
    rootChar_nsmul_single, h0, h1, h2, show ReeTag.F4.perm 0 = 3 by decide,
    CFSG.RankThree.PartOne.KLR.relExp_short a _ (by decide)] at e0
  simp only [inv_one, one_pow, mul_one] at e0
  have h3 : b 3 = 1 := eq_one_of_pow_two_pow hp hp2 (a + 1) (hbp 3) e0.symm
  funext i
  fin_cases i
  exacts [h0, h1, h2, h3]

theorem eq_one_of_phi4p (hF : CFSG.RankThree.PartOne.KLR.IsReeFrob a F)
    (b : Fin ReeTag.F4.tag.rank → Lˣ)
    (hb : rootDiagUnit ReeTag.F4.tag b ∈ CFSG.RankThree.PartOne.KLR.twistedFixed F
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L CFSG.RankThree.PartOne.KLR.wPhi4p))
    (h0 : b 0 = 1) (h1 : b 1 = 1) : b = 1 := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 0, 2, 1, 3, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 0, 0, 0], [-1, -1, 0, 1], [-2, -2, 1, 1], [-2, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  have hfix := (CFSG.RankThree.PartOne.KLR.rootDiagUnit_mem_twistedFixed_canonicalRep_iff hF _
    b).1 hb
  have hk : ∀ k : Fin ReeTag.F4.tag.rank,
      rootChar b (CFSG.RankThree.PartOne.KLR.wPhi4p •
        (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) =
      b (ReeTag.F4.perm k) ^ ReeTag.F4.relationExponent a (ReeTag.F4.perm k) := by
    intro k
    rw [hfix, CTTorus.rootChar_single]
    rfl
  have c2 : CFSG.RankThree.PartOne.KLR.wPhi4p • (Pi.single 2 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      Pi.single 2 1 := by
    funext l
    rw [CFSG.RankThree.PartOne.KLR.wPhi4p, CFSG.RankThree.PartOne.KLR.smul_single_eq_lget _ _ hW]
    fin_cases l <;> decide
  have c3 : CFSG.RankThree.PartOne.KLR.wPhi4p • (Pi.single 3 1 : Fin ReeTag.F4.tag.rank → ℤ) =
      Pi.single 1 1 + Pi.single 2 1 + Pi.single 3 1 := by
    funext l
    rw [CFSG.RankThree.PartOne.KLR.wPhi4p, CFSG.RankThree.PartOne.KLR.smul_single_eq_lget _ _ hW]
    fin_cases l <;> decide
  have e2 := hk 2
  have e3 := hk 3
  rw [c2, CTTorus.rootChar_single, show ReeTag.F4.perm 2 = 1 by decide, h1, one_pow] at e2
  rw [c3, rootChar_add, rootChar_add, CTTorus.rootChar_single, CTTorus.rootChar_single,
    CTTorus.rootChar_single, show ReeTag.F4.perm 3 = 0 by decide, h0, h1, e2, one_pow,
    one_mul, one_mul] at e3
  funext i
  fin_cases i
  exacts [h0, h1, e2, e3]

end Columns

section Plane

variable {K : Type}
  [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem exists_reePlane (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : (p : ℤ) ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 ∨
      (p : ℤ) ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) :
    ∃ (R : Subgroup (F4.reeGamma K a)) (i j h t : F4.reeGamma K a),
      (∀ x ∈ R, ∀ y ∈ R, x * y = y * x) ∧ (∀ r ∈ R, r ^ p = 1) ∧ Nat.card R = p ^ 2 ∧
      IsGL23Data R i j h t ∧ i * i * (i * i) = 1 ∧
      IsTConj a K ((i * i : F4.reeGamma K a) : ModGL F4.tag K) := by
  classical
  let L := AlgebraicClosure K
  have : CharP L 2 := by
    have : CharP K 2 := ‹CharP K F4.prime›
    exact charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨D⟩ := CFSG.RankThree.PartOne.KLR.reeFrameData_nonempty (L := L) hK
  have hF := D.isFrob
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨w, hw, Φ, hΦ, hΦT, hΦF, hcol⟩ : ∃ w : WeylGroup ReeTag.F4.tag,
      (w = CFSG.RankThree.PartOne.KLR.wPhi4m ∨ w = CFSG.RankThree.PartOne.KLR.wPhi4p) ∧
      ∃ Φ : rootsOfUnity p L × rootsOfUnity p L →* ModGL ReeTag.F4.tag L,
        Function.Injective Φ ∧ Φ.range ≤ torusGroup ReeTag.F4.tag L ∧
        Φ.range ≤ CFSG.RankThree.PartOne.KLR.twistedFixed D.F
          (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
        ∀ b : Fin ReeTag.F4.tag.rank → Lˣ, (∀ i, b i ^ p = 1) →
          rootDiagUnit ReeTag.F4.tag b ∈ CFSG.RankThree.PartOne.KLR.twistedFixed D.F
            (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) → b 0 = 1 → b 1 = 1 → b = 1 := by
    rcases hpd with h | h
    · obtain ⟨Φ, h1, h2, h3⟩ := CFSG.RankThree.PartOne.K128.torus_hom_m_phi4m hF hpodd h
      exact ⟨_, Or.inl rfl, Φ, h1, h2, h3, fun b hb hbF h0 h1 =>
        eq_one_of_phi4m hF hp hp2 b hb hbF h0 h1⟩
    · obtain ⟨Φ, h1, h2, h3⟩ := CFSG.RankThree.PartOne.K128.torus_hom_m_phi4p hF hpodd h
      exact ⟨_, Or.inr rfl, Φ, h1, h2, h3, fun b _ hbF h0 h1 => eq_one_of_phi4p hF b hbF h0 h1⟩
  set R₀ := twTorsion D.F w p with hR₀
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨f₀, hf₀⟩ := exists_injective_twTorsion hcol
  have hfin : Finite R₀ := Finite.of_injective f₀ hf₀
  have hR₀card : Nat.card R₀ = p ^ 2 :=
    le_antisymm (card_twTorsion_le hp hcol) (le_card_twTorsion hp hp2 hfin hΦ hΦT hΦF)
  set nI := nuF4 L ((coxeterSystem ReeTag.F4.tag).wordProd f4wI) with hnI
  set nJ := nuF4 L ((coxeterSystem ReeTag.F4.tag).wordProd f4wJ) with hnJ
  set nH := nuF4 L ((coxeterSystem ReeTag.F4.tag).wordProd f4wH) with hnH
  set nT := nuF4 L ((coxeterSystem ReeTag.F4.tag).wordProd f4wT) with hnT
  set n₀ := nuF4 L ((coxeterSystem ReeTag.F4.tag).wordProd f4wW0) with hn₀
  have htw : ∀ l, (l = f4wI ∨ l = f4wJ ∨ l = f4wH ∨ l = f4wT) →
      nuF4 L ((coxeterSystem ReeTag.F4.tag).wordProd l) ∈
        CFSG.RankThree.PartOne.KLR.twistedFixed D.F
          (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) :=
    fun l hl => canonicalRep_mem_twistedFixed hF (f4_twisted hw hl)
  have hnorm : ∀ l, (l = f4wI ∨ l = f4wJ ∨ l = f4wH ∨ l = f4wT) →
      nuF4 L ((coxeterSystem ReeTag.F4.tag).wordProd l) ∈
        Subgroup.normalizer (R₀ : Set (ModGL ReeTag.F4.tag L)) :=
    fun l hl => canonicalRep_mem_normalizer_twTorsion hF (f4_twisted hw hl) p
  have hinv₀ : InvOn R₀ n₀ := fun r hr => canonicalRep_w0_conj_torus hr.1
  obtain ⟨rII, rJJ, rIJ, rHI, rHJ, rHHH⟩ := f4_relations
  have eII : nI * nI = n₀ := by rw [← map_mul, ← CoxeterSystem.wordProd_append, rII]
  have eJJ : nJ * nJ = n₀ := by rw [← map_mul, ← CoxeterSystem.wordProd_append, rJJ]
  have eIJ : ⁅nI, nJ⁆ = n₀ := by
    rw [← map_commutatorElement, commutatorElement_def, ← CoxeterSystem.wordProd_reverse,
      ← CoxeterSystem.wordProd_reverse, ← CoxeterSystem.wordProd_append,
      ← CoxeterSystem.wordProd_append, ← CoxeterSystem.wordProd_append, rIJ]
  have eHI : nH * nI * nH⁻¹ = nJ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← CoxeterSystem.wordProd_reverse,
      ← CoxeterSystem.wordProd_append, ← CoxeterSystem.wordProd_append, rHI]
  have eHJ : nH * nJ * nH⁻¹ = nI * nJ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← CoxeterSystem.wordProd_reverse,
      ← CoxeterSystem.wordProd_append, ← CoxeterSystem.wordProd_append, rHJ,
      CoxeterSystem.wordProd_append]
  have eHHH : nH ^ 3 = 1 := by
    rw [pow_succ, pow_two, ← map_mul, ← map_mul, ← CoxeterSystem.wordProd_append,
      ← CoxeterSystem.wordProd_append, rHHH, CoxeterSystem.wordProd_nil, map_one]
  have e₀₀ : n₀ * n₀ = 1 := by rw [← map_mul, f4wW0_eq, w0_mul_self, map_one]
  have e₀H : n₀ * nH = nH * n₀ := by
    rw [← map_mul, ← map_mul, f4wW0_eq]
    exact congrArg _ (w0_mul_comm _).symm
  have hn₀1 : n₀ ≠ 1 := by
    intro h1
    apply w0_ne_one
    apply CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_injective ReeTag.F4.tag L
    rw [← f4wW0_eq, ← nuF4_apply, ← hn₀, h1, canonicalRep_one]
  have hnH1 : nH ≠ 1 := by
    intro h1
    apply f4wH_ne_one
    apply CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_injective ReeTag.F4.tag L
    rw [← nuF4_apply, ← hnH, h1, canonicalRep_one]
  have hd : IsGL23Data R₀ nI nJ nH nT := by
    refine ⟨⟨hnorm _ (Or.inl rfl), hnorm _ (Or.inr (Or.inl rfl)),
      hnorm _ (Or.inr (Or.inr (Or.inl rfl))), by rw [eIJ]; exact hinv₀,
      by rw [eII]; exact hinv₀, by rw [eJJ]; exact hinv₀, by rw [eHI]; exact AgreeOn.refl _,
      by rw [eHJ]; exact AgreeOn.refl _⟩, hnorm _ (Or.inr (Or.inr (Or.inr rfl))), ?_⟩
    have hlist : ∀ a' ∈ [1, nI, nJ, nI * nJ],
        ∃ x : Fin 4, a' = nuF4 L ((coxeterSystem ReeTag.F4.tag).wordProd (f4wV x)) := by
      intro a' ha'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha'
      rcases ha' with rfl | rfl | rfl | rfl
      · exact ⟨0, by rw [show f4wV 0 = [] from rfl, CoxeterSystem.wordProd_nil, map_one]⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, by
          rw [show f4wV 3 = f4wI ++ f4wJ from rfl, CoxeterSystem.wordProd_append, map_mul]⟩
    intro a' ha' b' hb'
    obtain ⟨x, rfl⟩ := hlist a' ha'
    obtain ⟨y, rfl⟩ := hlist b' hb'
    obtain ⟨c6, cI⟩ := f4_comm x y
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_commutatorElement]
    refine ⟨?_, (f4wM x y : ℤ), ?_⟩
    · rw [← map_pow, show (12 : ℕ) = 6 * 2 from rfl, pow_mul, c6, one_pow, map_one]
    · rw [← map_inv, ← map_mul, ← map_mul, cI, map_mul, map_pow, zpow_natCast]
      exact AgreeOn.refl _
  set S := Subgroup.closure ((R₀ : Set (ModGL ReeTag.F4.tag L)) ∪ {nI, nJ, nH, nT}) with hS
  have hSF : S ≤ CFSG.RankThree.PartOne.KLR.twistedFixed D.F
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) := by
    rw [hS, Subgroup.closure_le]
    rintro g (hg | hg)
    · exact hg.2.1
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      exacts [htw _ (Or.inl rfl), htw _ (Or.inr (Or.inl rfl)),
        htw _ (Or.inr (Or.inr (Or.inl rfl))), htw _ (Or.inr (Or.inr (Or.inr rfl)))]
  obtain ⟨Ψ, hΨ⟩ := CFSG.RankThree.PartOne.K128.exists_hom_reeGamma D w S.subtype
    S.subtype_injective (by rw [Subgroup.range_subtype]; exact hSF)
  have hRS : R₀ ≤ S := fun u hu => Subgroup.subset_closure (Or.inl hu)
  have hIS : nI ∈ S := Subgroup.subset_closure (Or.inr (by simp))
  have hJS : nJ ∈ S := Subgroup.subset_closure (Or.inr (by simp))
  have hHS : nH ∈ S := Subgroup.subset_closure (Or.inr (by simp))
  have hTS : nT ∈ S := Subgroup.subset_closure (Or.inr (by simp))
  have hn₀S : n₀ ∈ S := eII ▸ mul_mem hIS hIS
  have hII : (⟨nI, hIS⟩ : S) * ⟨nI, hIS⟩ = ⟨n₀, hn₀S⟩ := Subtype.ext eII
  have hy4 : Ψ ⟨nI, hIS⟩ * Ψ ⟨nI, hIS⟩ * (Ψ ⟨nI, hIS⟩ * Ψ ⟨nI, hIS⟩) = 1 := by
    rw [← map_mul, hII, ← map_mul]
    have : (⟨n₀, hn₀S⟩ * ⟨n₀, hn₀S⟩ : S) = 1 := Subtype.ext e₀₀
    rw [this, map_one]
  have hcomm : Ψ ⟨nI, hIS⟩ * Ψ ⟨nI, hIS⟩ * Ψ ⟨nH, hHS⟩ =
      Ψ ⟨nH, hHS⟩ * (Ψ ⟨nI, hIS⟩ * Ψ ⟨nI, hIS⟩) := by
    rw [← map_mul, hII, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext e₀H
  refine ⟨(R₀.subgroupOf S).map Ψ, Ψ ⟨nI, hIS⟩, Ψ ⟨nJ, hJS⟩, Ψ ⟨nH, hHS⟩, Ψ ⟨nT, hTS⟩, ?_, ?_,
    ?_, hd.map Ψ hIS hJS hHS hTS, hy4, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg Ψ (Subtype.ext (twTorsion_comm _ hx _ hy))
  · rintro _ ⟨r, hr, rfl⟩
    rw [← map_pow]
    have : r ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hr.2.2)
    rw [this, map_one]
  · rw [Subgroup.card_map_of_injective hΨ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRS).toEquiv, hR₀card]
  ·
    refine isTConj_of_commute_order_three ha hK (Ψ ⟨nI, hIS⟩ * Ψ ⟨nI, hIS⟩).2
      (Ψ ⟨nH, hHS⟩).2 ?_ ?_ ?_ ?_ ?_
    · rw [sq, ← Subgroup.coe_mul, hy4, Subgroup.coe_one]
    · intro h1
      have h2 : Ψ ⟨nI, hIS⟩ * Ψ ⟨nI, hIS⟩ = 1 := Subtype.ext h1
      rw [← map_mul, hII] at h2
      have h3 := hΨ (h2.trans (map_one Ψ).symm)
      exact hn₀1 (congrArg Subtype.val h3)
    · rw [← Subgroup.coe_pow, ← map_pow]
      have : (⟨nH, hHS⟩ : S) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact eHHH)
      rw [this, map_one, Subgroup.coe_one]
    · intro h1
      have h2 : Ψ ⟨nH, hHS⟩ = 1 := Subtype.ext h1
      have h3 := hΨ (h2.trans (map_one Ψ).symm)
      exact hnH1 (congrArg Subtype.val h3)
    · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm]

end Plane

end CFSG.Quasithin.B45Tor

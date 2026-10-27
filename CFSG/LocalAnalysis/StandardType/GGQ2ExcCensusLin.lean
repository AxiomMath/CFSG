module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusChecks
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusTypes
public import CFSG.LocalAnalysis.StandardType.GGQ2InLLeafSel
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtCoverFrame

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open Module

noncomputable section

variable {m : Fin 6} {T : Chk.Tabs} {w : Chk.LinW}


private theorem lin_sgnN_eq (w : Chk.LinW) (i : ℕ) : Chk.sgnN w i = 1 ∨ Chk.sgnN w i = -1 := by
  unfold Chk.sgnN
  split <;> simp

private theorem lin_sgnN_mul_self (w : Chk.LinW) (i : ℕ) :
    (Chk.sgnN w i : ZMod 3) * (Chk.sgnN w i : ZMod 3) = 1 := by
  rcases lin_sgnN_eq w i with h | h <;> rw [h] <;> norm_num

private theorem lin_sgnN_ne_zero (w : Chk.LinW) (i : ℕ) : (Chk.sgnN w i : ZMod 3) ≠ 0 := by
  rcases lin_sgnN_eq w i with h | h <;> rw [h] <;> norm_num

private theorem lin_nat_all_eq_true_iff {n : ℕ} {f : (i : ℕ) → i < n → Bool} :
    Nat.all n f = true ↔ ∀ i (h : i < n), f i h = true := by
  induction n with
  | zero => rw [Nat.all_zero]; simp
  | succ n ih =>
    rw [Nat.all_succ, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_ge i n with h | h
      · exact ih.mp h1 i h
      · have : i = n := by omega
        subst this
        simpa using h2
    · intro h
      exact ⟨ih.mpr fun i hi => h i (by omega), h n (by omega)⟩

private theorem lin_testBit_shiftLeft_one (i j : ℕ) :
    ((1 : ℕ) <<< j).testBit i = true ↔ j = i := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff]

private theorem lin_testBit_fold_nodeMask (w : Chk.LinW) (p : ℕ → Bool) (k init t : ℕ) :
    (Nat.fold k (fun i _ acc => if p i then acc ||| 1 <<< Chk.nodeN w i else acc) init).testBit t =
        true ↔
      init.testBit t = true ∨ ∃ i, i < k ∧ p i = true ∧ Chk.nodeN w i = t := by
  induction k generalizing init with
  | zero =>
    rw [Nat.fold_zero]
    constructor
    · exact Or.inl
    · rintro (h | ⟨i, hi, -⟩)
      · exact h
      · omega
  | succ k ih =>
    rw [Nat.fold_succ]
    split
    · rename_i hp
      rw [Nat.testBit_lor, Bool.or_eq_true, lin_testBit_shiftLeft_one, ih]
      constructor
      · rintro (h | h)
        · rcases h with h | ⟨i, hi, hpi, hni⟩
          · exact Or.inl h
          · exact Or.inr ⟨i, by omega, hpi, hni⟩
        · exact Or.inr ⟨k, by omega, hp, h⟩
      · rintro (h | ⟨i, hi, hpi, hni⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
          · exact Or.inl (Or.inr ⟨i, hlt, hpi, hni⟩)
          · rw [heq] at hni
            exact Or.inr hni
    · rename_i hp
      rw [ih]
      constructor
      · rintro (h | ⟨i, hi, hpi, hni⟩)
        · exact Or.inl h
        · exact Or.inr ⟨i, by omega, hpi, hni⟩
      · rintro (h | ⟨i, hi, hpi, hni⟩)
        · exact Or.inl h
        · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
          · exact Or.inr ⟨i, hlt, hpi, hni⟩
          · rw [heq] at hpi
            exact absurd hpi hp

private theorem lin_typeOK_pair {r : ℕ} (h : Chk.typeOK T r w = true)
    (i j : Fin (Chk.rkN w.tc w.n)) :
    Chk.sgnN w i * Chk.sgnN w j * (T.pair[Chk.nodeN w i]!)[Chk.nodeN w j]! =
      Chk.cartanN w.tc w.n i j := by
  simp only [Chk.typeOK, Bool.and_eq_true, beq_iff_eq] at h
  have hinner := lin_nat_all_eq_true_iff.mp h.2 i i.2
  exact beq_iff_eq.mp (lin_nat_all_eq_true_iff.mp hinner j j.2)

@[expose] def nodeRoot (m : Fin 6) (w : Chk.LinW)
    (hw : ∀ i : Fin (Chk.rkN w.tc w.n), Chk.nodeN w i < nroots m) (i : Fin (Chk.rkN w.tc w.n)) :
    Root m :=
  ⟨Chk.nodeN w i, hw i⟩

theorem mem_ofMask_nodeMask (hw : ∀ i : Fin (Chk.rkN w.tc w.n), Chk.nodeN w i < nroots m)
    (p : ℕ → Bool) (t : Root m) :
    t ∈ ofMask m (Chk.nodeMask w p) ↔
      ∃ i : Fin (Chk.rkN w.tc w.n), p i = true ∧ nodeRoot m w hw i = t := by
  rw [mem_ofMask, Chk.nodeMask, lin_testBit_fold_nodeMask]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨i, hi, hpi, hni⟩
    exact ⟨⟨i, hi⟩, hpi, Fin.ext hni⟩
  · rintro ⟨i, hpi, hri⟩
    exact ⟨i.val, i.2, hpi, congrArg Fin.val hri⟩

theorem mem_nodeList (p : ℕ → Bool) (t : ℕ) :
    t ∈ Chk.nodeList w p ↔ ∃ i : Fin (Chk.rkN w.tc w.n), p i = true ∧ Chk.nodeN w i = t := by
  unfold Chk.nodeList
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.mem_filter, List.mem_range] at hi
    exact ⟨⟨i, hi.1⟩, hi.2, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.val, by rw [List.mem_filter, List.mem_range]; exact ⟨i.2, hi⟩, rfl⟩

theorem linOf_pairing (hT : Chk.tabsOK m T = true) (hw : Chk.typeOK T (nroots m) w = true)
    (i j : Fin (Chk.rkN w.tc w.n)) :
    ((Chk.sgnN w i : ZMod 3) • root m (nodeRoot m w (typeOK_node_lt hw) i))
        ((Chk.sgnN w j : ZMod 3) • coroot m (nodeRoot m w (typeOK_node_lt hw) j)) =
      (cartanOf w.tc w.n i j : ZMod 3) := by
  have hpair := lin_typeOK_pair (T := T) (r := nroots m) hw i j
  have htabs := tabsOK_pair (m := m) hT (nodeRoot m w (typeOK_node_lt hw) i)
    (nodeRoot m w (typeOK_node_lt hw) j)
  have hp : Chk.sgnN w i * Chk.sgnN w j *
      pairing m (nodeRoot m w (typeOK_node_lt hw) i) (nodeRoot m w (typeOK_node_lt hw) j) =
      Chk.cartanN w.tc w.n i j := by
    rw [← htabs]
    exact hpair
  have hpc : ((Chk.sgnN w i : ZMod 3) * (Chk.sgnN w j : ZMod 3) *
      (pairing m (nodeRoot m w (typeOK_node_lt hw) i) (nodeRoot m w (typeOK_node_lt hw) j) :
        ZMod 3)) = ((Chk.cartanN w.tc w.n i j : ℤ) : ZMod 3) := by
    rw [← hp]
    push_cast
    rfl
  rw [LinearMap.smul_apply, map_smul, smul_smul, smul_eq_mul, pairing_eq]
  exact hpc

@[expose] def linOf (m : Fin 6) (T : Chk.Tabs) (hT : Chk.tabsOK m T = true) (w : Chk.LinW)
    (hw : Chk.linOK T (nroots m) w = true) : GGQ2LinOn 3 (V m) where
  ι := Fin (Chk.rkN w.tc w.n)
  coxeter := coxOf w.tc w.n
  cartan := cartanOf w.tc w.n
  coroot i :=
    (Chk.sgnN w i : ZMod 3) • coroot m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i)
  root i := (Chk.sgnN w i : ZMod 3) • root m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i)
  a := ⟨w.a, linOK_a_lt hw⟩
  b := ⟨w.b, linOK_b_lt hw⟩
  a_ne_b h := linOK_a_ne_b hw (congrArg Fin.val h)
  a_leaf := linOK_a_leaf hw
  isWeyl := ggIsWeylMatrix_coxOf (typeOK_validN (linOK_typeOK hw))
  isCartan := ggIntCartan_coxOf (typeOK_validN (linOK_typeOK hw))
  pairing := linOf_pairing hT (linOK_typeOK hw)

section linOf

variable (hT : Chk.tabsOK m T = true) (hw : Chk.linOK T (nroots m) w = true)

theorem linOf_cartan : (linOf m T hT w hw).cartan = cartanOf w.tc w.n := rfl

theorem linOf_root (i : Fin (Chk.rkN w.tc w.n)) :
    (linOf m T hT w hw).root i =
      (Chk.sgnN w i : ZMod 3) • root m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i) :=
  rfl

theorem linOf_coroot (i : Fin (Chk.rkN w.tc w.n)) :
    (linOf m T hT w hw).coroot i =
      (Chk.sgnN w i : ZMod 3) • coroot m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i) :=
  rfl

theorem linOf_a : ((linOf m T hT w hw).a : Fin (Chk.rkN w.tc w.n)) = ⟨w.a, linOK_a_lt hw⟩ := rfl

theorem linOf_b : ((linOf m T hT w hw).b : Fin (Chk.rkN w.tc w.n)) = ⟨w.b, linOK_b_lt hw⟩ := rfl

private theorem lin_smul_scaled_apply (s : ZMod 3) (hs : s * s = 1)
    (α : Module.Dual (ZMod 3) (V m)) (x v : V m) :
    ((s • α) v) • (s • x) = α v • x := by
  simp only [LinearMap.smul_apply, smul_eq_mul, smul_smul]
  have h : (s * α v) * s = α v := by
    calc (s * α v) * s = (s * s) * α v := by ring
      _ = α v := by rw [hs, one_mul]
  rw [h]

theorem linOf_simpleRefl (i : Fin (Chk.rkN w.tc w.n)) :
    (linOf m T hT w hw).toLin.simpleRefl i =
      reflection m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i) := by
  apply LinearEquiv.ext
  intro v
  unfold GGQ2Lin.simpleRefl
  have e1 : (linOf m T hT w hw).toLin.simpleRefl i v =
      v - ((linOf m T hT w hw).toLin.root i) v • ((linOf m T hT w hw).toLin.coroot i) :=
    Module.reflection_apply v _
  have hroot : (linOf m T hT w hw).toLin.root i =
      (Chk.sgnN w i : ZMod 3) • root m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i) :=
    linOf_root (m := m) (T := T) hT hw i
  have hcoroot : (linOf m T hT w hw).toLin.coroot i =
      (Chk.sgnN w i : ZMod 3) • coroot m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i) :=
    linOf_coroot (m := m) (T := T) hT hw i
  have e2 : v - ((linOf m T hT w hw).toLin.root i) v •
        ((linOf m T hT w hw).toLin.coroot i) =
      v - ((Chk.sgnN w i : ZMod 3) •
          root m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i)) v •
        ((Chk.sgnN w i : ZMod 3) •
          coroot m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i)) :=
    congrArg₂ (fun a b => v - a • b)
      (congrArg (fun f : Dual (ZMod 3) (V m) => f (v : V m)) hroot) hcoroot
  have e3 : v - ((Chk.sgnN w i : ZMod 3) •
          root m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i)) v •
        ((Chk.sgnN w i : ZMod 3) •
          coroot m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i)) =
      v - root m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i) v •
        coroot m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i) := by
    rw [lin_smul_scaled_apply (Chk.sgnN w i : ZMod 3) (lin_sgnN_mul_self w i)]
  have e4 : (reflection m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i)) v =
      v - root m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i) v •
        coroot m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i) :=
    reflection_apply m _ v
  exact e1.trans (e2.trans (e3.trans e4.symm))

theorem linOf_parab (S : Set (Fin (Chk.rkN w.tc w.n))) :
    (linOf m T hT w hw).toLin.parab S =
      Subgroup.closure
        (reflection m '' (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) '' S)) := by
  unfold GGQ2Lin.parab
  rw [show (linOf m T hT w hw).toLin.simpleRefl =
      fun i => reflection m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i) from
    funext (linOf_simpleRefl (m := m) (T := T) hT hw)]
  rw [Set.image_image]
  rfl

private theorem lin_parab_set_a (hT : Chk.tabsOK m T = true)
    (hw : Chk.linOK T (nroots m) w = true) :
    {i : Fin (Chk.rkN w.tc w.n) | i ≠ (linOf m T hT w hw).a} =
      {i : Fin (Chk.rkN w.tc w.n) | (fun i : ℕ => i != w.a) i = true} := by
  ext i
  have ha := linOf_a (m := m) (T := T) hT hw
  simp only [Set.mem_setOf_eq, ha, Fin.ext_iff, bne_iff_ne, ne_eq]

private theorem lin_parab_set_b (hT : Chk.tabsOK m T = true)
    (hw : Chk.linOK T (nroots m) w = true) :
    {i : Fin (Chk.rkN w.tc w.n) | i ≠ (linOf m T hT w hw).b} =
      {i : Fin (Chk.rkN w.tc w.n) | (fun i : ℕ => i != w.b) i = true} := by
  ext i
  have hb := linOf_b (m := m) (T := T) hT hw
  simp only [Set.mem_setOf_eq, hb, Fin.ext_iff, bne_iff_ne, ne_eq]

theorem linOf_parab_eq {p : ℕ → Bool} {c : ℕ} {L : List (ℕ × ℕ)}
    (hg : Chk.genOK T (nroots m) (Chk.nodeMask w p) c L = true) (hb : Chk.notB2 m c = true) :
    (linOf m T hT w hw).toLin.parab ({i | p i = true} : Set (Fin (Chk.rkN w.tc w.n))) =
      normalizerGroup m (ofMask m c) := by
  rw [linOf_parab]
  have hset : nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) '' {i | p i = true} =
      (ofMask m (Chk.nodeMask w p) : Set (Root m)) := by
    ext t
    rw (config := { transparency := .all }) [Set.mem_image, Set.mem_setOf_eq, mem_ofMask_nodeMask]
    exact Iff.rfl
  rw [hset, genOK_sound hT hg]
  exact (normalizerGroup_ofMask (m := m) hb).symm

theorem linOf_kernel {p : ℕ → Bool} {cz : ℕ} {B : Array (Array ℤ)}
    (hl : Chk.lineOK T (dim m) (nroots m) (Chk.nodeList w p) cz B = true) (v : V m) :
    (∀ i ∈ {i : Fin (Chk.rkN w.tc w.n) | p i = true}, (linOf m T hT w hw).root i v = 0) ↔
      v ∈ Submodule.span (ZMod 3) {vec m cz} := by
  have hroot : ∀ i : Fin (Chk.rkN w.tc w.n),
      (linOf m T hT w hw).root i v =
        (Chk.sgnN w i : ZMod 3) *
          root m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i) v := by
    intro i
    rw (config := { transparency := .all }) [linOf_root, LinearMap.smul_apply, smul_eq_mul]
  rw (config := { transparency := .all }) [show (∀ i ∈ {i : Fin (Chk.rkN w.tc w.n) | p i = true},
        (linOf m T hT w hw).root i v = 0) ↔
      ∀ t : Root m, t.val ∈ Chk.nodeList w p → root m t v = 0 from by
    constructor
    · intro h t ht
      obtain ⟨i, hi, hni⟩ := (mem_nodeList (p := p) (t := t.val)).mp ht
      have hti : nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i = t := Fin.ext hni
      have hz : (linOf m T hT w hw).root i v = 0 := h i hi
      have hz' : (Chk.sgnN w i : ZMod 3) *
          root m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i) v = 0 := by
        rw (config := { transparency := .all }) [hroot i] at hz
        exact hz
      rw [← hti]
      exact (mul_eq_zero.mp hz').resolve_left (lin_sgnN_ne_zero w i)
    · intro h i hi
      rw (config := { transparency := .all }) [hroot i]
      have hmem : (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i).val ∈
          Chk.nodeList w p := by
        rw [mem_nodeList]
        exact ⟨i, hi, rfl⟩
      rw (config := { transparency := .all }) [h _ hmem, mul_zero]]
  exact lineOK_sound hT hl v

theorem linOf_linearIndependent {B : Array (Array ℤ)} (h : Chk.indepOK T (dim m) w B = true) :
    LinearIndependent (ZMod 3) (linOf m T hT w hw).coroot := by
  have hind := indepOK_sound hT h (typeOK_node_lt (linOK_typeOK hw))
  have hunits := hind.units_smul
    (fun i => Units.mk0 (Chk.sgnN w i : ZMod 3) (lin_sgnN_ne_zero w i))
  have hfun : (linOf m T hT w hw).coroot =
      fun i : Fin (Chk.rkN w.tc w.n) =>
        (Units.mk0 (Chk.sgnN w i : ZMod 3) (lin_sgnN_ne_zero w i) : ZMod 3) •
        coroot m (nodeRoot m w (typeOK_node_lt (linOK_typeOK hw)) i) := rfl
  rw [hfun]
  exact hunits

theorem linOf_basis {B : Array (Array ℤ)} (h : Chk.basisOK T (dim m) w B = true) :
    (linOf m T hT w hw).toLin.Basis := by
  simp only [Chk.basisOK, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨linOf_linearIndependent hT hw h.2, ?_⟩
  have hc : Fintype.card (linOf m T hT w hw).toLin.ι = Chk.rkN w.tc w.n := Fintype.card_fin _
  have hfr : Module.finrank (ZMod 3) (V m) = dim m := Module.finrank_fin_fun (ZMod 3)
  rw [hc, h.1]
  exact hfr.symm

theorem linOf_det_ne_zero {B : Array (Array ℤ)}
    (h : Chk.invOK (Chk.rkN w.tc w.n) (Chk.cartanN w.tc w.n) B = true) :
    (((linOf m T hT w hw).cartan.det : ℤ) : ZMod 3) ≠ 0 := by
  have hM : cartanOf w.tc w.n =
      Matrix.of (fun i j : Fin (Chk.rkN w.tc w.n) => Chk.cartanN w.tc w.n i j) := rfl
  rw [linOf_cartan, hM]
  exact invOK_det_ne_zero (M := Chk.cartanN w.tc w.n) h

theorem linOf_det_eq_zero {x : Array ℤ}
    (h : Chk.singOK (Chk.rkN w.tc w.n) (Chk.cartanN w.tc w.n) x = true) :
    (((linOf m T hT w hw).cartan.det : ℤ) : ZMod 3) = 0 := by
  have hM : cartanOf w.tc w.n =
      Matrix.of (fun i j : Fin (Chk.rkN w.tc w.n) => Chk.cartanN w.tc w.n i j) := rfl
  rw [linOf_cartan, hM]
  exact singOK_det_eq_zero (M := Chk.cartanN w.tc w.n) h

theorem nbrLinAt_linOf {cz k : ℕ} {L : List (ℕ × ℕ)} {B : Array (Array ℤ)}
    (h : Chk.nbrOK T m cz k w L B = true) :
    NbrLinAt (excRaw m) (vec m cz) (ofMask m k) (linOf m T hT w hw) := by
  simp only [Chk.nbrOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hlin, hgen⟩, hline⟩, hnotB2⟩ := h
  constructor
  · unfold GGQ2Lin.weyl
    have hset : (Set.univ : Set (Fin (Chk.rkN w.tc w.n))) =
        {i : Fin (Chk.rkN w.tc w.n) | (fun _ : ℕ => true) i = true} := by
      ext i
      simp
    exact (congrArg (fun S => (linOf m T hT w hw).toLin.parab S) hset).trans
      ((linOf_parab_eq (m := m) hT hw (p := fun _ => true) hgen hnotB2).trans rfl)
  · intro v
    have hrewrite : (∀ i : (linOf m T hT w hw).ι, (linOf m T hT w hw).root i v = 0) ↔
        ∀ i ∈ {i : Fin (Chk.rkN w.tc w.n) | (fun _ : ℕ => true) i = true},
          (linOf m T hT w hw).root i v = 0 := by
      constructor
      · intro h i hi
        exact h i
      · intro h i
        exact h i (by rfl)
    exact hrewrite.trans (linOf_kernel (m := m) hT hw hline v)

end linOf

theorem commonWitness_of_commonOK (hT : Chk.tabsOK m T = true) {cv cz ℓ k : ℕ}
    {W : Chk.CommonW} (h : Chk.commonOK T m cv cz ℓ k W = true) :
    CommonWitness (excRaw m) (vec m cv) (vec m cz) (ofMask m ℓ) (ofMask m k) := by
  simp only [Chk.commonOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hlin, hgenL⟩, hgenK⟩, hlineL⟩, hlineK⟩, hnotL⟩, hnotK⟩ := h
  refine ⟨linOf m T hT W.w hlin, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun S => (linOf m T hT W.w hlin).toLin.parab S)
        (lin_parab_set_a (m := m) (T := T) (w := W.w) hT hlin)).trans
      ((linOf_parab_eq (m := m) hT hlin hgenL hnotL).trans rfl)
  · exact (congrArg (fun S => (linOf m T hT W.w hlin).toLin.parab S)
        (lin_parab_set_b (m := m) (T := T) (w := W.w) hT hlin)).trans
      ((linOf_parab_eq (m := m) hT hlin hgenK hnotK).trans rfl)
  · intro v
    have hset := lin_parab_set_a (m := m) (T := T) (w := W.w) hT hlin
    exact (show (∀ i ∈ {i : Fin (Chk.rkN W.w.tc W.w.n) | i ≠ (linOf m T hT W.w hlin).a},
          (linOf m T hT W.w hlin).root i v = 0) ↔
        ∀ i ∈ {i : Fin (Chk.rkN W.w.tc W.w.n) | (fun i : ℕ => i != W.w.a) i = true},
          (linOf m T hT W.w hlin).root i v = 0 from by rw [hset]).trans
      (linOf_kernel (m := m) hT hlin hlineL v)
  · intro v
    have hset := lin_parab_set_b (m := m) (T := T) (w := W.w) hT hlin
    exact (show (∀ i ∈ {i : Fin (Chk.rkN W.w.tc W.w.n) | i ≠ (linOf m T hT W.w hlin).b},
          (linOf m T hT W.w hlin).root i v = 0) ↔
        ∀ i ∈ {i : Fin (Chk.rkN W.w.tc W.w.n) | (fun i : ℕ => i != W.w.b) i = true},
          (linOf m T hT W.w hlin).root i v = 0 from by rw [hset]).trans
      (linOf_kernel (m := m) hT hlin hlineK v)

theorem inLLeafAt_of_leafModelOK (hT : Chk.tabsOK m T = true) {cv cz ℓ k : ℕ}
    {W : Chk.CommonW} (h : Chk.leafModelOK T m cv cz ℓ k W = true) :
    InLLeafAt (excRaw m) (vec m cv) (vec m cz) (ofMask m ℓ) (ofMask m k) := by
  simp only [Chk.leafModelOK, Chk.commonOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hlin, hgenL⟩, hgenK⟩, hlineL⟩, hlineK⟩, hnotL⟩, hnotK⟩, hleaf⟩ := h
  refine ⟨linOf m T hT W.w hlin, ?_, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun S => (linOf m T hT W.w hlin).toLin.parab S)
        (lin_parab_set_a (m := m) (T := T) (w := W.w) hT hlin)).trans
      ((linOf_parab_eq (m := m) hT hlin hgenL hnotL).trans rfl)
  · exact (congrArg (fun S => (linOf m T hT W.w hlin).toLin.parab S)
        (lin_parab_set_b (m := m) (T := T) (w := W.w) hT hlin)).trans
      ((linOf_parab_eq (m := m) hT hlin hgenK hnotK).trans rfl)
  · intro v
    have hset := lin_parab_set_a (m := m) (T := T) (w := W.w) hT hlin
    exact (show (∀ i ∈ {i : Fin (Chk.rkN W.w.tc W.w.n) | i ≠ (linOf m T hT W.w hlin).a},
          (linOf m T hT W.w hlin).root i v = 0) ↔
        ∀ i ∈ {i : Fin (Chk.rkN W.w.tc W.w.n) | (fun i : ℕ => i != W.w.a) i = true},
          (linOf m T hT W.w hlin).root i v = 0 from by rw [hset]).trans
      (linOf_kernel (m := m) hT hlin hlineL v)
  · intro v
    have hset := lin_parab_set_b (m := m) (T := T) (w := W.w) hT hlin
    exact (show (∀ i ∈ {i : Fin (Chk.rkN W.w.tc W.w.n) | i ≠ (linOf m T hT W.w hlin).b},
          (linOf m T hT W.w hlin).root i v = 0) ↔
        ∀ i ∈ {i : Fin (Chk.rkN W.w.tc W.w.n) | (fun i : ℕ => i != W.w.b) i = true},
          (linOf m T hT W.w hlin).root i v = 0 from by rw [hset]).trans
      (linOf_kernel (m := m) hT hlin hlineK v)
  · obtain ⟨c, hc1, hc2⟩ :=
      leafN_existsUnique (tc := W.w.tc) (n := W.w.n) (b := W.w.b) (linOK_b_lt hlin) hleaf
    refine ⟨c, ?_, ?_⟩
    · change c ≠ (linOf m T hT W.w hlin).b ∧
        (linOf m T hT W.w hlin).cartan (linOf m T hT W.w hlin).b c ≠ 0
      rw [linOf_b, linOf_cartan]
      exact hc1
    · intro y hy
      apply hc2 y
      have hy' : y ≠ (linOf m T hT W.w hlin).b ∧
          (linOf m T hT W.w hlin).cartan (linOf m T hT W.w hlin).b y ≠ 0 := hy
      rwa [linOf_b, linOf_cartan] at hy'

theorem genOK_cent (hT : Chk.tabsOK m T = true) {gens c : ℕ} {L : List (ℕ × ℕ)}
    (h : Chk.genOK T (nroots m) gens c L = true) (v : V m) :
    (∀ t ∈ ofMask m gens, root m t v = 0) ↔ v ∈ cent m (ofMask m c) := by
  have hfix : ∀ t : Root m, reflection m t v = v ↔ root m t v = 0 := fun t => by
    rw [reflection_apply, sub_eq_self, smul_eq_zero, or_iff_left]
    intro h0
    have h2 := root_coroot m t
    rw [h0, map_zero] at h2
    exact absurd h2 (by decide)
  simp only [cent, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hv i hi
    have hle : Subgroup.closure (reflection m '' (ofMask m gens : Set (Root m))) ≤
        MulAction.stabilizer (V m ≃ₗ[ZMod 3] V m) v := by
      rw [Subgroup.closure_le]
      rintro _ ⟨t, ht, rfl⟩
      exact MulAction.mem_stabilizer_iff.mpr ((LinearEquiv.smul_def _ _).trans ((hfix t).2 (hv t ht)))
    rw [genOK_sound hT h] at hle
    exact (hfix i).1 ((LinearEquiv.smul_def _ _).symm.trans
      (MulAction.mem_stabilizer_iff.mp (hle (Subgroup.subset_closure ⟨i, hi, rfl⟩))))
  · intro hv t ht
    exact hv t (genOK_subset h ht)

theorem finrank_le_card_add_finrank_cent (hT : Chk.tabsOK m T = true) {gens c : ℕ}
    {L : List (ℕ × ℕ)} (h : Chk.genOK T (nroots m) gens c L = true) :
    finrank (ZMod 3) (V m) ≤ (ofMask m gens).card + finrank (ZMod 3) (cent m (ofMask m c)) := by
  set S := ofMask m gens
  let φ : V m →ₗ[ZMod 3] (Fin S.card → ZMod 3) := LinearMap.pi fun j => root m (S.equivFin.symm j)
  have hker : LinearMap.ker φ = cent m (ofMask m c) := by
    ext v
    rw [LinearMap.mem_ker, ← genOK_cent hT h v]
    constructor
    · intro hv t ht
      simpa [φ] using congrFun hv (S.equivFin ⟨t, ht⟩)
    · intro hv
      funext j
      simpa [φ] using hv _ (S.equivFin.symm j).2
  have hrn : finrank (ZMod 3) (LinearMap.range φ) + finrank (ZMod 3) (LinearMap.ker φ) =
      finrank (ZMod 3) (V m) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact LinearMap.finrank_range_add_finrank_ker φ
  have hrange : finrank (ZMod 3) (LinearMap.range φ) ≤ S.card := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact (Submodule.finrank_le _).trans (Module.finrank_fin_fun (ZMod 3)).le
  rw [← hker]
  omega

end

end CFSG.StandardType.GGQ2Frame.ExcRaw

end

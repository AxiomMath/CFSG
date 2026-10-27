module

public import Mathlib
public import CFSG.Milestones.ASVolI.H1
public import CFSG.Quasithin.Background.HMathieuStatements
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Monster.Code.LatticeCount
public import CFSG.Quasithin.Background.HMathieuNorm
public import CFSG.Quasithin.Background.HMathieuCent
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Monster.B.TwoA.Base.PairStab
public import CFSG.Quasithin.Background.H132Irr
public import Certificates.Certificate260402
public import Certificates.Certificate260431
public import Certificates.Certificate260433
public import Certificates.Certificate7061

public section

open scoped Pointwise

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

abbrev S24 : Type := Equiv.Perm (Fin 24)

abbrev PM24 : Type := G6.PermMod 24

open scoped Classical in
@[expose] noncomputable def eY (Y : Finset (Fin 24)) : PM24 :=
  Multiplicative.ofAdd fun i => if i ∈ Y then 1 else 0

@[expose] def dot24 (u v : PM24) : ZMod 2 :=
  ∑ i, Multiplicative.toAdd u i * Multiplicative.toAdd v i

@[expose] noncomputable def wt24 (v : PM24) : ℕ := Nat.card {i : Fin 24 // Multiplicative.toAdd v i ≠ 0}

abbrev Cocode24 : Type := PM24 ⧸ golayC

abbrev ComplementQuotient24 : Type := PM24 ⧸ Subgroup.zpowers (G6.allOnes 24)

@[expose] noncomputable def cocodeWt24 (coset : Cocode24) : ℕ :=
  sInf {weight : ℕ | ∃ representative : PM24,
    (QuotientGroup.mk representative : Cocode24) = coset ∧ wt24 representative = weight}

@[expose] def HasComplementWeight24 (coset : ComplementQuotient24) (weight : ℕ) : Prop :=
  ∃ representative : PM24,
    (QuotientGroup.mk representative : ComplementQuotient24) = coset ∧
      wt24 representative = weight

theorem wt24_eq_card (v : PM24) :
    wt24 v = (Finset.univ.filter fun i : Fin 24 => Multiplicative.toAdd v i ≠ 0).card := by
  unfold wt24
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem allOnes24_mul_self : G6.allOnes 24 * G6.allOnes 24 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  change (1 : ZMod 2) + 1 = 0
  decide

theorem sq24 (x : PM24) : x * x = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  change Multiplicative.toAdd x i + Multiplicative.toAdd x i = 0
  generalize Multiplicative.toAdd x i = y
  revert y
  decide

theorem inv24_eq (x : PM24) : x⁻¹ = x := inv_eq_of_mul_eq_one_right (sq24 x)

theorem allOnes24_zpow (k : ℤ) :
    G6.allOnes 24 ^ k = 1 ∨ G6.allOnes 24 ^ k = G6.allOnes 24 := by
  have hsq : G6.allOnes 24 ^ (2 : ℤ) = 1 := (zpow_two _).trans allOnes24_mul_self
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    have h2 : G6.allOnes 24 ^ (2 * n) = (G6.allOnes 24 ^ (2 : ℤ)) ^ n := zpow_mul _ _ _
    rw [h2, hsq]
    exact one_zpow n
  · right
    have h3 : G6.allOnes 24 ^ (2 * n + 1) = G6.allOnes 24 ^ (2 * n) * G6.allOnes 24 :=
      zpow_add_one _ _
    have h2 : G6.allOnes 24 ^ (2 * n) = (G6.allOnes 24 ^ (2 : ℤ)) ^ n := zpow_mul _ _ _
    rw [h3, h2, hsq]
    exact (congrArg (fun x => x * G6.allOnes 24) (one_zpow n)).trans (one_mul _)

theorem cocodeWt24_spec (coset : Cocode24) :
    (∃ representative : PM24,
      (QuotientGroup.mk representative : Cocode24) = coset ∧
        wt24 representative = cocodeWt24 coset) ∧
    (∀ representative : PM24,
      (QuotientGroup.mk representative : Cocode24) = coset →
        cocodeWt24 coset ≤ wt24 representative) := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective coset
  have hne : {weight : ℕ | ∃ representative : PM24,
      (QuotientGroup.mk representative : Cocode24) = QuotientGroup.mk r ∧
        wt24 representative = weight}.Nonempty :=
    ⟨wt24 r, r, rfl, rfl⟩
  exact ⟨Nat.sInf_mem hne, fun representative hrep => Nat.sInf_le ⟨representative, hrep, rfl⟩⟩

theorem hasComplementWeight24_mk_iff (representative : PM24) (weight : ℕ) :
    HasComplementWeight24 (QuotientGroup.mk representative) weight ↔
      weight = wt24 representative ∨
        weight = wt24 (representative * G6.allOnes 24) := by
  have e : (representative * G6.allOnes 24)⁻¹ * representative = G6.allOnes 24 := by
    rw [inv24_eq, mul_right_comm, sq24, one_mul]
  have key : ∀ r : PM24,
      (QuotientGroup.mk r : ComplementQuotient24) = QuotientGroup.mk representative ↔
        r = representative ∨ r = representative * G6.allOnes 24 := by
    intro r
    rw [QuotientGroup.eq, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      rcases allOnes24_zpow k with h | h
      · left
        exact inv_mul_eq_one.1 (hk.symm.trans h)
      · right
        have h1 : r⁻¹ * representative = G6.allOnes 24 := hk.symm.trans h
        have h2 : representative = r * G6.allOnes 24 := inv_mul_eq_iff_eq_mul.1 h1
        rw [h2, mul_assoc, allOnes24_mul_self, mul_one]
    · rintro (rfl | rfl)
      · exact ⟨0, (zpow_zero _).trans (inv_mul_cancel _).symm⟩
      · exact ⟨1, (zpow_one _).trans e.symm⟩
  unfold HasComplementWeight24
  constructor
  · rintro ⟨r, hr, hw⟩
    rcases (key r).1 hr with rfl | rfl
    · exact Or.inl hw.symm
    · exact Or.inr hw.symm
  · rintro (h | h)
    · exact ⟨representative, rfl, h.symm⟩
    · exact ⟨representative * G6.allOnes 24, (key _).2 (Or.inr rfl), h.symm⟩

theorem wt24_complement (representative : PM24) :
    wt24 (representative * G6.allOnes 24) = 24 - wt24 representative := by
  have hz : ∀ x : ZMod 2, x + 1 ≠ 0 ↔ x = 0 := by decide
  rw [wt24_eq_card, wt24_eq_card]
  have hfilt : (Finset.univ.filter fun i : Fin 24 =>
      Multiplicative.toAdd (representative * G6.allOnes 24) i ≠ 0) =
        Finset.univ.filter fun i : Fin 24 => Multiplicative.toAdd representative i = 0 :=
    Finset.filter_congr fun i _ => hz _
  rw [hfilt]
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 24)))
    (fun i : Fin 24 => Multiplicative.toAdd representative i = 0)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  simp only [ne_eq] at hsplit ⊢
  omega

theorem wt24_eY (support : Finset (Fin 24)) : wt24 (eY support) = support.card := by
  rw [wt24_eq_card]
  congr 1
  ext i
  by_cases h : i ∈ support <;> simp [eY, h]

theorem pairVec_eq_eY_pair (a b : Fin 24) (distinct : a ≠ b) :
    pairVec a b = eY {a, b} := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [pairVec, unitVec, toAdd_mul, toAdd_ofAdd, Pi.add_apply, eY, Finset.mem_insert,
    Finset.mem_singleton, Pi.single_apply]
  by_cases ha : i = a
  · have hb : ¬ i = b := fun h => distinct (ha.symm.trans h)
    simp [ha, hb, distinct]
  · by_cases hb : i = b
    · simp [ha, hb, Ne.symm distinct]
    · simp [ha, hb]

theorem mem_pairKer_iff_dot24 (a b : Fin 24) (representative : PM24) :
    representative ∈ pairKer a b ↔ dot24 representative (pairVec a b) = 0 := by
  have hdot : dot24 representative (pairVec a b) =
      Multiplicative.toAdd representative a + Multiplicative.toAdd representative b := by
    simp [dot24, pairVec, unitVec, Pi.single_apply, mul_add, mul_ite, Finset.sum_add_distrib]
  rw [hdot]
  exact Iff.rfl

theorem h13_zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem mem_golayC_iff' (x : PM24) : x ∈ golayC ↔ Multiplicative.toAdd x ∈ CFSG.Monster.Code.C :=
  Iff.rfl

theorem toAdd_eY (Y : Finset (Fin 24)) (i : Fin 24) :
    Multiplicative.toAdd (eY Y) i = if i ∈ Y then 1 else 0 := by
  by_cases h : i ∈ Y <;> simp [eY, h]

theorem eY_empty : eY (∅ : Finset (Fin 24)) = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp [toAdd_eY]

theorem eY_inj {S T : Finset (Fin 24)} (h : eY S = eY T) : S = T := by
  ext i
  have h' := congrArg (fun v : PM24 => Multiplicative.toAdd v i) h
  simp only [toAdd_eY] at h'
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT] at h' ⊢

theorem dot24_comm (x y : PM24) : dot24 x y = dot24 y x := by
  unfold dot24
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem dot24_mul_left (x y z : PM24) : dot24 (x * y) z = dot24 x z + dot24 y z := by
  unfold dot24
  simp only [toAdd_mul, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dot24_eY (c : PM24) (S : Finset (Fin 24)) :
    dot24 c (eY S) = ∑ k ∈ S, Multiplicative.toAdd c k := by
  unfold dot24
  simp only [toAdd_eY, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp

theorem sum_toAdd_eY (Y : Finset (Fin 24)) :
    ∑ k, Multiplicative.toAdd (eY Y) k = (Y.card : ZMod 2) := by
  simp only [toAdd_eY]
  rw [Finset.sum_boole]
  congr 1
  congr 1
  ext k
  simp

theorem mem_coreMod_iff_dot_allOnes (v : PM24) :
    v ∈ G6.coreMod 24 ↔ dot24 v (G6.allOnes 24) = 0 := by
  rw [G6.mem_coreMod]
  unfold dot24
  simp [G6.allOnes]

theorem golay_dot_eq_zero {c d : PM24} (hc : c ∈ golayC) (hd : d ∈ golayC) : dot24 c d = 0 :=
  CFSG.Monster.Code.dotProduct_eq_zero ((mem_golayC_iff' c).1 hc) ((mem_golayC_iff' d).1 hd)

theorem allOnes_mem_golayC : G6.allOnes 24 ∈ golayC :=
  (mem_golayC_iff' _).2 CFSG.Monster.Code.Ω_mem_C

theorem golayC_le_coreMod : golayC ≤ G6.coreMod 24 := fun x hx =>
  (mem_coreMod_iff_dot_allOnes x).2 (golay_dot_eq_zero hx allOnes_mem_golayC)

theorem golay_mem_of_dot (w : PM24) (h : ∀ c ∈ golayC, dot24 w c = 0) : w ∈ golayC := by
  refine (mem_golayC_iff' w).2 ((CFSG.Monster.Code.mem_C_iff_forall_dotProduct _).2 fun y hy => ?_)
  exact h (Multiplicative.ofAdd y) ((mem_golayC_iff' _).2 (by simpa using hy))

theorem hammingNorm_le_of_support (x : Fin 24 → ZMod 2) (S : Finset (Fin 24))
    (h : ∀ i, x i ≠ 0 → i ∈ S) : hammingNorm x ≤ S.card := by
  unfold hammingNorm
  exact Finset.card_le_card fun i hi => h i (Finset.mem_filter.1 hi).2

theorem eY_mem_golayC_iff (S : Finset (Fin 24)) (hS : S.card < 8) :
    eY S ∈ golayC ↔ S = ∅ := by
  constructor
  · intro h
    by_contra hne
    have hne0 : Multiplicative.toAdd (eY S) ≠ 0 := by
      intro h0
      apply hne
      ext i
      have h1 := congrFun h0 i
      by_cases hi : i ∈ S
      · simp [toAdd_eY, hi] at h1
      · simp [hi]
    have h8 := CFSG.Monster.Code.eight_le_wt ((mem_golayC_iff' _).1 h) hne0
    have hle := hammingNorm_le_of_support (Multiplicative.toAdd (eY S)) S (fun i hi => by
      by_contra hiS
      apply hi
      simp [toAdd_eY, hiS])
    omega
  · rintro rfl
    rw [eY_empty]
    exact Subgroup.one_mem _

theorem eY_mul_eY_mem_golayC_iff (S T : Finset (Fin 24)) (hST : S.card + T.card < 8) :
    eY S * eY T ∈ golayC ↔ S = T := by
  constructor
  · intro h
    by_contra hne
    have hne0 : Multiplicative.toAdd (eY S * eY T) ≠ 0 := by
      intro h0
      apply hne
      ext i
      have h1 := congrFun h0 i
      simp only [toAdd_mul, Pi.add_apply, toAdd_eY, Pi.zero_apply] at h1
      by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT] at h1 ⊢
    have h8 := CFSG.Monster.Code.eight_le_wt ((mem_golayC_iff' _).1 h) hne0
    have hle := hammingNorm_le_of_support (Multiplicative.toAdd (eY S * eY T)) (S ∪ T) (fun i hi => by
      by_contra hiST
      apply hi
      simp only [Finset.mem_union, not_or] at hiST
      simp [toAdd_eY, hiST.1, hiST.2])
    have hu := Finset.card_union_le S T
    omega
  · rintro rfl
    rw [sq24]
    exact Subgroup.one_mem _

theorem permAct_eY (σ : Equiv.Perm (Fin 24)) (S : Finset (Fin 24)) :
    G6.permAct 24 σ (eY S) = eY (S.map σ.toEmbedding) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [G6.permAct_apply, toAdd_eY, Finset.mem_map_equiv, Equiv.Perm.inv_def]

theorem smul_finset_eq_map (g : Equiv.Perm (Fin 24)) (S : Finset (Fin 24)) :
    g • S = S.map g.toEmbedding := by
  ext x
  simp only [Finset.mem_smul_finset, Finset.mem_map_equiv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨g.symm x, hx, by simp⟩

theorem dot24_permAct (σ : Equiv.Perm (Fin 24)) (u v : PM24) :
    dot24 (G6.permAct 24 σ u) (G6.permAct 24 σ v) = dot24 u v := by
  unfold dot24
  simp only [G6.permAct_apply]
  exact Equiv.sum_comp σ⁻¹ (fun i => Multiplicative.toAdd u i * Multiplicative.toAdd v i)

theorem exists_dot24_ne_zero {u : PM24} (hu : u ≠ 1) : ∃ v : PM24, dot24 u v ≠ 0 := by
  have hex : ∃ i, Multiplicative.toAdd u i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu
    apply Multiplicative.toAdd.injective
    funext i
    simpa using h i
  obtain ⟨i, hi⟩ := hex
  refine ⟨eY {i}, ?_⟩
  rw [dot24_eY, Finset.sum_singleton]
  exact hi

theorem exists_dot_coreMod_of_golay_not_zpowers (c : PM24) (hc : c ∈ golayC)
    (hcz : c ∉ Subgroup.zpowers (G6.allOnes 24)) :
    ∃ w ∈ G6.coreMod 24, dot24 c w ≠ 0 := by
  have hnc : ∃ i j : Fin 24, Multiplicative.toAdd c i ≠ Multiplicative.toAdd c j := by
    by_contra h
    push_neg at h
    apply hcz
    have hc' : c = 1 ∨ c = G6.allOnes 24 := by
      rcases h13_zmod2_cases (Multiplicative.toAdd c 0) with h0 | h0
      · left
        apply Multiplicative.toAdd.injective
        funext i
        rw [h i 0, h0]
        rfl
      · right
        apply Multiplicative.toAdd.injective
        funext i
        rw [h i 0, h0]
        rfl
    rcases hc' with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  obtain ⟨i, j, hij⟩ := hnc
  have hne : i ≠ j := fun h => hij (congrArg _ h)
  refine ⟨eY {i, j}, ?_, ?_⟩
  · rw [G6.mem_coreMod, sum_toAdd_eY, Finset.card_pair hne]
    decide
  · rw [dot24_eY, Finset.sum_pair hne]
    revert hij
    generalize Multiplicative.toAdd c i = x
    generalize Multiplicative.toAdd c j = y
    revert x y
    decide

theorem zmod2_add_eq_zero_iff (x y : ZMod 2) : x + y = 0 ↔ x = y := by
  revert x y
  decide

theorem h13_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

theorem exists_golay_dot_of_not_mem_coreMod_pair (a b : Fin 24) (hab : a ≠ b) (w : PM24)
    (hw : ∀ c ∈ golayC ⊓ pairKer a b, dot24 c w = 0) :
    w ∈ golayC ⊔ Subgroup.zpowers (pairVec a b) := by
  have hp_not : pairVec a b ∉ golayC := by
    rw [pairVec_eq_eY_pair a b hab]
    intro h
    have h2 := (eY_mem_golayC_iff {a, b} (by rw [Finset.card_pair hab]; norm_num)).1 h
    simp at h2
  have hc0 : ∃ c0 ∈ golayC, dot24 c0 (pairVec a b) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hp_not (golay_mem_of_dot _ fun c hc => by rw [dot24_comm]; exact h c hc)
  obtain ⟨c0, hc0g, hc0p⟩ := hc0
  have hkey : ∀ c ∈ golayC, dot24 c w = dot24 c (pairVec a b) * dot24 c0 w := by
    intro c hc
    rcases h13_zmod2_cases (dot24 c (pairVec a b)) with hg | hg
    · have hD : c ∈ golayC ⊓ pairKer a b := ⟨hc, (mem_pairKer_iff_dot24 a b c).2 hg⟩
      rw [hw c hD, hg, zero_mul]
    · have hc0' : dot24 c0 (pairVec a b) = 1 := by
        rcases h13_zmod2_cases (dot24 c0 (pairVec a b)) with h0 | h0
        · exact absurd h0 hc0p
        · exact h0
      have hmem : c * c0 ∈ golayC ⊓ pairKer a b := by
        refine ⟨Subgroup.mul_mem golayC hc hc0g, (mem_pairKer_iff_dot24 a b _).2 ?_⟩
        rw [dot24_mul_left, hg, hc0']
        decide
      have h1 := hw _ hmem
      rw [dot24_mul_left] at h1
      rw [hg, one_mul]
      exact (zmod2_add_eq_zero_iff _ _).1 h1
  rcases h13_zmod2_cases (dot24 c0 w) with hl | hl
  · have hw0 : ∀ c ∈ golayC, dot24 w c = 0 := fun c hc => by
      rw [dot24_comm, hkey c hc, hl, mul_zero]
    exact (le_sup_left : golayC ≤ golayC ⊔ Subgroup.zpowers (pairVec a b))
      (golay_mem_of_dot w hw0)
  · have hu : w * pairVec a b ∈ golayC := by
      apply golay_mem_of_dot
      intro c hc
      rw [dot24_mul_left, dot24_comm w c, dot24_comm (pairVec a b) c, hkey c hc, hl, mul_one]
      exact h13_add_self _
    have hwp : w = (w * pairVec a b) * pairVec a b := by
      rw [mul_assoc, sq24, mul_one]
    rw [hwp]
    exact (golayC ⊔ Subgroup.zpowers (pairVec a b)).mul_mem
      ((le_sup_left : golayC ≤ golayC ⊔ Subgroup.zpowers (pairVec a b)) hu)
      ((le_sup_right : Subgroup.zpowers (pairVec a b) ≤ golayC ⊔ Subgroup.zpowers (pairVec a b))
        (Subgroup.mem_zpowers _))

theorem zpow_involution (x : PM24) (k : ℤ) : x ^ k = 1 ∨ x ^ k = x := by
  have hsq : x ^ (2 : ℤ) = 1 := (zpow_two _).trans (sq24 x)
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    have h2 : x ^ (2 * n) = (x ^ (2 : ℤ)) ^ n := zpow_mul _ _ _
    rw [h2, hsq]
    exact one_zpow n
  · right
    have h3 : x ^ (2 * n + 1) = x ^ (2 * n) * x := zpow_add_one _ _
    have h2 : x ^ (2 * n) = (x ^ (2 : ℤ)) ^ n := zpow_mul _ _ _
    rw [h3, h2, hsq]
    exact (congrArg (fun y => y * x) (one_zpow n)).trans (one_mul _)

theorem allOnes_ne_one : G6.allOnes 24 ≠ 1 := by
  intro h
  have h0 := congrArg (fun v : PM24 => Multiplicative.toAdd v 0) h
  simp [G6.allOnes] at h0

theorem card_zpowers_involution (x : PM24) (hx : x ≠ 1) :
    Nat.card (Subgroup.zpowers x) = 2 := by
  rw [Nat.card_zpowers]
  apply orderOf_eq_prime
  · rw [pow_two]
    exact sq24 x
  · exact hx

theorem natCard_eq_two_mul_of_cover {G : Type*} [Group G] (H K : Subgroup G) (g : G)
    (hgK : g ∉ K) (hg : g * g = 1) (hgH : g ∈ H) (hKH : K ≤ H)
    (hcov : ∀ x ∈ H, x ∈ K ∨ x * g ∈ K) :
    Nat.card H = 2 * Nat.card K := by
  let f : K × Bool → H := fun p =>
    ⟨(p.1 : G) * (if p.2 then g else 1), by
      cases p.2
      · simpa using hKH p.1.2
      · exact H.mul_mem (hKH p.1.2) hgH⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨k1, hk1⟩, b1⟩ ⟨⟨k2, hk2⟩, b2⟩ h
      have h' : k1 * (if b1 then g else 1) = k2 * (if b2 then g else 1) := congrArg Subtype.val h
      cases b1 <;> cases b2
      · have hk : k1 = k2 := by simpa using h'
        subst hk
        rfl
      · exfalso
        have hk : k1 = k2 * g := by simpa using h'
        apply hgK
        have hgeq : g = (k2 : G)⁻¹ * k1 := by rw [hk, inv_mul_cancel_left]
        rw [hgeq]
        exact K.mul_mem (K.inv_mem hk2) hk1
      · exfalso
        have hk : k1 * g = k2 := by simpa using h'
        apply hgK
        have hgeq : g = (k1 : G)⁻¹ * k2 := by rw [← hk, inv_mul_cancel_left]
        rw [hgeq]
        exact K.mul_mem (K.inv_mem hk1) hk2
      · have hk : k1 = k2 := by simpa using h'
        subst hk
        rfl
    · rintro ⟨x, hx⟩
      rcases hcov x hx with hxK | hxK
      · exact ⟨(⟨⟨x, hxK⟩, false⟩), Subtype.ext (by simp [f])⟩
      · refine ⟨(⟨⟨x * g, hxK⟩, true⟩), Subtype.ext ?_⟩
        simp only [f, if_true]
        rw [mul_assoc, hg, mul_one]
  have hcard := Nat.card_eq_of_bijective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hcard
  omega

theorem natCard_golayC : Nat.card golayC = 4096 := by
  rw [← CFSG.Monster.Code.card_CFin, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd (x : PM24), (CFSG.Monster.Code.mem_CFin).2 x.2⟩
      invFun := fun y => ⟨Multiplicative.ofAdd (y : Fin 24 → ZMod 2),
        (CFSG.Monster.Code.mem_CFin).1 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem natCard_PM24 : Nat.card PM24 = 2 ^ 24 := by
  rw [Nat.card_congr Multiplicative.ofAdd.symm]
  simp [Nat.card_eq_fintype_card]

theorem natCard_top_PM24 : Nat.card (⊤ : Subgroup PM24) = 2 ^ 24 := by
  rw [Nat.card_congr Subgroup.topEquiv.toEquiv, natCard_PM24]

theorem natCard_coreMod : Nat.card (G6.coreMod 24) = 2 ^ 23 := by
  have h := natCard_eq_two_mul_of_cover (⊤ : Subgroup PM24) (G6.coreMod 24) (eY {0}) ?_ ?_
    ?_ le_top ?_
  · rw [natCard_top_PM24] at h
    have h2 : (2 : ℕ) ^ 24 = 2 * 2 ^ 23 := by norm_num
    rw [h2] at h
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h).symm
  · rw [G6.mem_coreMod, sum_toAdd_eY]
    simp
  · exact sq24 _
  · exact Subgroup.mem_top _
  · intro x _
    have hs : ∑ i, Multiplicative.toAdd (x * eY {0}) i = ∑ i, Multiplicative.toAdd x i + 1 := by
      simp only [toAdd_mul, Pi.add_apply, Finset.sum_add_distrib, sum_toAdd_eY,
        Finset.card_singleton]
      norm_num
    rcases h13_zmod2_cases (∑ i, Multiplicative.toAdd x i) with h0 | h0
    · left
      rw [G6.mem_coreMod]
      exact h0
    · right
      rw [G6.mem_coreMod, hs, h0]
      decide

theorem natCard_golay_sup (p : PM24) (hpG : p ∉ golayC) (hp : p * p = 1) :
    Nat.card ↥(golayC ⊔ Subgroup.zpowers p) = 2 * Nat.card golayC := by
  refine natCard_eq_two_mul_of_cover (golayC ⊔ Subgroup.zpowers p) golayC p hpG hp ?_ le_sup_left ?_
  · exact (le_sup_right : Subgroup.zpowers p ≤ golayC ⊔ Subgroup.zpowers p) (Subgroup.mem_zpowers p)
  intro x hx
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  rcases zpow_involution p k with h | h
  · left
    have e1 : y * p ^ k = y := by
      rw [h]
      exact mul_one y
    have hxy : x = y := hyz.symm.trans e1
    rw [hxy]
    exact hy
  · right
    have e2 : y * p ^ k * p = y := by
      rw [h, mul_assoc, hp, mul_one]
    have hxy : x * p = y := by
      rw [← hyz]
      exact e2
    rw [hxy]
    exact hy

theorem pairVec_not_mem_golayC (a b : Fin 24) (hab : a ≠ b) : pairVec a b ∉ golayC := by
  rw [pairVec_eq_eY_pair a b hab]
  intro h'
  have h2 := (eY_mem_golayC_iff {a, b} (by rw [Finset.card_pair hab]; norm_num)).1 h'
  simp at h2

theorem exists_golay_dot_pairVec_ne (a b : Fin 24) (hab : a ≠ b) :
    ∃ c0 ∈ golayC, dot24 c0 (pairVec a b) ≠ 0 := by
  by_contra h
  push_neg at h
  exact pairVec_not_mem_golayC a b hab (golay_mem_of_dot _ fun c hc => by
    rw [dot24_comm]
    exact h c hc)

theorem natCard_golay_pair (a b : Fin 24) (hab : a ≠ b) :
    Nat.card ↥(golayC ⊓ pairKer a b) = 2048 := by
  obtain ⟨c0, hc0, hc0p⟩ := exists_golay_dot_pairVec_ne a b hab
  have hc1 : dot24 c0 (pairVec a b) = 1 := by
    rcases h13_zmod2_cases (dot24 c0 (pairVec a b)) with h0 | h0
    · exact absurd h0 hc0p
    · exact h0
  have h := natCard_eq_two_mul_of_cover golayC (golayC ⊓ pairKer a b) c0 ?_ (sq24 c0) hc0
    inf_le_left ?_
  · rw [natCard_golayC] at h
    omega
  · intro hK
    have h1 := (mem_pairKer_iff_dot24 a b c0).1 (Subgroup.mem_inf.1 hK).2
    rw [hc1] at h1
    exact one_ne_zero h1
  · intro x hx
    by_cases hxp : dot24 x (pairVec a b) = 0
    · left
      exact Subgroup.mem_inf.2 ⟨hx, (mem_pairKer_iff_dot24 a b x).2 hxp⟩
    · right
      have hx1 : dot24 x (pairVec a b) = 1 := by
        rcases h13_zmod2_cases (dot24 x (pairVec a b)) with h0 | h0
        · exact absurd h0 hxp
        · exact h0
      refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem golayC hx hc0, (mem_pairKer_iff_dot24 a b _).2 ?_⟩
      rw [dot24_mul_left, hx1, hc1]
      decide

theorem rk_eq_of_natCard {W : Type*} [Group W] (k : ℕ) (h : Nat.card W = 2 ^ k) :
    CFSG.Quasithin.rk W = k := by
  unfold CFSG.Quasithin.rk
  rw [h, padicValNat.prime_pow]

theorem rk_golayC : CFSG.Quasithin.rk ↥golayC = 12 :=
  rk_eq_of_natCard 12 (by rw [natCard_golayC]; norm_num)

theorem rk_top_PM24 : CFSG.Quasithin.rk ↥(⊤ : Subgroup PM24) = 24 :=
  rk_eq_of_natCard 24 natCard_top_PM24

theorem rk_coreMod : CFSG.Quasithin.rk ↥(G6.coreMod 24) = 23 :=
  rk_eq_of_natCard 23 natCard_coreMod

theorem rk_zpowers_allOnes : CFSG.Quasithin.rk ↥(Subgroup.zpowers (G6.allOnes 24)) = 1 :=
  rk_eq_of_natCard 1 (by rw [card_zpowers_involution _ allOnes_ne_one]; norm_num)

theorem rk_golay_sup (a b : Fin 24) (hab : a ≠ b) :
    CFSG.Quasithin.rk ↥(golayC ⊔ Subgroup.zpowers (pairVec a b)) = 13 :=
  rk_eq_of_natCard 13 (by
    rw [natCard_golay_sup _ (pairVec_not_mem_golayC a b hab) (sq24 _), natCard_golayC]
    norm_num)

theorem rk_golay_pair (a b : Fin 24) (hab : a ≠ b) :
    CFSG.Quasithin.rk ↥(golayC ⊓ pairKer a b) = 11 :=
  rk_eq_of_natCard 11 (by rw [natCard_golay_pair a b hab]; norm_num)

@[expose] def M24g : Subgroup S24 := AutPerm

@[expose] def M23g (a : Fin 24) : Subgroup S24 := M24g ⊓ MulAction.stabilizer S24 a

@[expose] def M22g (a b : Fin 24) : Subgroup S24 :=
  M24g ⊓ MulAction.stabilizer S24 a ⊓ MulAction.stabilizer S24 b

@[expose] def M2ab (a b : Fin 24) : Subgroup S24 :=
  M24g ⊓ MulAction.stabilizer S24 ({a, b} : Finset (Fin 24))

@[expose] def IsOctad (O : Finset (Fin 24)) : Prop := O.card = 8 ∧ eY O ∈ golayC

@[expose] def IsTrio (Tr : Finset (Finset (Fin 24))) : Prop :=
  Tr.card = 3 ∧ (∀ O ∈ Tr, IsOctad O) ∧
    (∀ O ∈ Tr, ∀ O' ∈ Tr, O ≠ O' → Disjoint O O') ∧ Tr.biUnion id = Finset.univ

@[expose] def IsSextet (S : Finset (Finset (Fin 24))) : Prop :=
  S.card = 6 ∧ (∀ B ∈ S, B.card = 4) ∧ (∀ B ∈ S, ∀ B' ∈ S, B ≠ B' → Disjoint B B') ∧
    S.biUnion id = Finset.univ ∧ (∀ B ∈ S, ∀ B' ∈ S, B ≠ B' → IsOctad (B ∪ B'))

@[expose] noncomputable def mathModel (isCode : Bool) (d : ℕ) (a b : Fin 24) (Γ : Subgroup S24) :
    FFModel :=
  FFModel.golaySec Γ
    (if isCode then (if d = 22 then golayC ⊓ pairKer a b else golayC) else G6.coreMod 24)
    (if isCode then Subgroup.zpowers (G6.allOnes 24)
      else (if d = 22 then golayC ⊔ Subgroup.zpowers (pairVec a b) else golayC))

@[expose] noncomputable def IsMathModule {V : Type*} [CommGroup V] (isCode : Bool) (d : ℕ)
    (a b : Fin 24) (Γ : Subgroup S24) (ρ : ↥Γ →* MulAut V) : Prop :=
  ∃ β, RealizesBy (mathModel isCode d a b Γ) ρ.range ⊤ ⊥ ρ.rangeRestrict β

@[expose] def rImg {V : Type*} [CommGroup V] {Γ : Subgroup S24} (ρ : ↥Γ →* MulAut V)
    (A : Subgroup S24) : Subgroup (MulAut V) :=
  (A.subgroupOf Γ).map ρ

@[expose] def Ld (d : ℕ) (a b : Fin 24) : Subgroup S24 :=
  if d = 24 then M24g else if d = 23 then M23g a else M22g a b

@[expose] def AutLd (d : ℕ) (a b : Fin 24) : Subgroup S24 :=
  if d = 22 then M2ab a b else Ld d a b

@[expose] def IsAbsIrredMod {V : Type*} [CommGroup V] (M : Subgroup (MulAut V)) : Prop :=
  IsIrredOn M ⊤ ∧ ∀ θ : V →* V, (∀ g ∈ M, ∀ v, θ (g v) = g (θ v)) → θ = 1 ∨ θ = MonoidHom.id V

end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu

theorem golayC_eq_closure_octads :
    golayC = Subgroup.closure {vector : PM24 |
      ∃ octad : Finset (Fin 24), IsOctad octad ∧ eY octad = vector} := by
  set S : Set PM24 := {vector : PM24 |
    ∃ octad : Finset (Fin 24), IsOctad octad ∧ eY octad = vector} with hS
  have hbasis : ∀ i : Fin 12, Multiplicative.ofAdd (CFSG.Monster.Code.B i) ∈ Subgroup.closure S := by
    intro i
    have hsupp : (Finset.univ.filter fun j : Fin 24 => CFSG.Monster.Code.B i j ≠ 0).card = 8 := by
      have h8 := CFSG.Monster.Code.wt_B i
      unfold hammingNorm at h8
      exact h8
    have heY : eY (Finset.univ.filter fun j : Fin 24 => CFSG.Monster.Code.B i j ≠ 0) =
        Multiplicative.ofAdd (CFSG.Monster.Code.B i) := by
      unfold eY
      congr 1
      funext j
      rcases h13_zmod2_cases (CFSG.Monster.Code.B i j) with h0 | h0 <;> simp [h0]
    have hoct : IsOctad (Finset.univ.filter fun j : Fin 24 => CFSG.Monster.Code.B i j ≠ 0) := by
      refine ⟨hsupp, ?_⟩
      rw [heY]
      exact (mem_golayC_iff' _).2 (by simpa using CFSG.Monster.Code.B_mem_C i)
    have hmem : eY (Finset.univ.filter fun j : Fin 24 => CFSG.Monster.Code.B i j ≠ 0) ∈ S :=
      ⟨_, hoct, rfl⟩
    have := Subgroup.subset_closure hmem
    rwa [heY] at this
  let K : Submodule (ZMod 2) (Fin 24 → ZMod 2) :=
    { carrier := {x | Multiplicative.ofAdd x ∈ Subgroup.closure S}
      add_mem' := fun {x y} hx hy => by
        have e : Multiplicative.ofAdd (x + y) = Multiplicative.ofAdd x * Multiplicative.ofAdd y :=
          ofAdd_add x y
        show Multiplicative.ofAdd (x + y) ∈ Subgroup.closure S
        rw [e]
        exact Subgroup.mul_mem _ hx hy
      zero_mem' := by
        show Multiplicative.ofAdd (0 : Fin 24 → ZMod 2) ∈ Subgroup.closure S
        rw [ofAdd_zero]
        exact Subgroup.one_mem _
      smul_mem' := fun c {x} hx => by
        show Multiplicative.ofAdd (c • x) ∈ Subgroup.closure S
        rcases h13_zmod2_cases c with h0 | h0
        · rw [h0, zero_smul, ofAdd_zero]
          exact Subgroup.one_mem _
        · rw [h0, one_smul]
          exact hx }
  have hle : Submodule.span (ZMod 2) (Set.range CFSG.Monster.Code.B) ≤ K := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hbasis i
  rw [CFSG.Monster.Code.span_B] at hle
  apply le_antisymm
  · intro x hx
    have h : Multiplicative.ofAdd (Multiplicative.toAdd x) ∈ Subgroup.closure S :=
      hle ((mem_golayC_iff' x).1 hx)
    rwa [ofAdd_toAdd] at h
  · refine (Subgroup.closure_le _).2 ?_
    rintro v ⟨O, hO, rfl⟩
    exact hO.2

theorem mem_M23g_iff (a : Fin 24) (g : Equiv.Perm (Fin 24)) :
    g ∈ M23g a ↔ g ∈ M24g ∧ g a = a := by
  simp [M23g, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]

theorem mem_M22g_iff (a b : Fin 24) (g : Equiv.Perm (Fin 24)) :
    g ∈ M22g a b ↔ g ∈ M24g ∧ g a = a ∧ g b = b := by
  simp [M22g, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, and_assoc]

theorem smul_pair_eq_iff (g : Equiv.Perm (Fin 24)) (a b : Fin 24) (hab : a ≠ b) :
    g • ({a, b} : Finset (Fin 24)) = {a, b} ↔
      (g a = a ∧ g b = b) ∨ (g a = b ∧ g b = a) := by
  have hmem : ∀ x, x ∈ g • ({a, b} : Finset (Fin 24)) ↔
      ∃ y ∈ ({a, b} : Finset (Fin 24)), g y = x := by
    intro x
    rw [Finset.mem_smul_finset]
    simp
  constructor
  · intro h
    have ha : g a = a ∨ g a = b := by
      have hm : g a ∈ ({a, b} : Finset (Fin 24)) := by
        rw [← h, hmem]
        exact ⟨a, by simp, rfl⟩
      simpa using hm
    have hb : g b = a ∨ g b = b := by
      have hm : g b ∈ ({a, b} : Finset (Fin 24)) := by
        rw [← h, hmem]
        exact ⟨b, by simp, rfl⟩
      simpa using hm
    have hA : ∃ y, (y = a ∨ y = b) ∧ g y = a := by
      have hm : a ∈ g • ({a, b} : Finset (Fin 24)) := by
        rw [h]
        simp
      rw [hmem] at hm
      obtain ⟨y, hy, hgy⟩ := hm
      exact ⟨y, by simpa using hy, hgy⟩
    have hinj : g a ≠ g b := fun e => hab (g.injective e)
    obtain ⟨y, hy, hgy⟩ := hA
    rcases hy with hy | hy <;> rw [hy] at hgy
    · left
      refine ⟨hgy, ?_⟩
      rcases hb with hb | hb
      · exact absurd (hb.trans hgy.symm).symm hinj
      · exact hb
    · right
      refine ⟨?_, hgy⟩
      rcases ha with ha | ha
      · exact absurd (ha.trans hgy.symm) hinj
      · exact ha
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [smul_finset_eq_map]
      ext x
      simp [h1, h2]
    · rw [smul_finset_eq_map]
      ext x
      simp [h1, h2]
      tauto

theorem mem_M2ab_iff (a b : Fin 24) (hab : a ≠ b) (g : Equiv.Perm (Fin 24)) :
    g ∈ M2ab a b ↔ g ∈ M24g ∧ ((g a = a ∧ g b = b) ∨ (g a = b ∧ g b = a)) := by
  simp only [M2ab, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rw [smul_pair_eq_iff g a b hab]

theorem map_conj_eq_of_iff (τ : Equiv.Perm (Fin 24)) (hτ : τ ∈ M24g)
    (H T : Subgroup (Equiv.Perm (Fin 24)))
    (P Q : Equiv.Perm (Fin 24) → Prop)
    (hT : ∀ x, x ∈ T ↔ x ∈ M24g ∧ P x)
    (hH : ∀ h, h ∈ H ↔ h ∈ M24g ∧ Q h)
    (hPQ : ∀ h, P (τ * h * τ⁻¹) ↔ Q h) :
    H.map (MulAut.conj τ).toMonoidHom = T := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hhh := (hH h).1 hh
    rw [hT]
    refine ⟨?_, (hPQ h).2 hhh.2⟩
    exact M24g.mul_mem (M24g.mul_mem hτ hhh.1) (M24g.inv_mem hτ)
  · intro hx
    rw [hT] at hx
    have hconj : (MulAut.conj τ).toMonoidHom (τ⁻¹ * x * τ) = x := by
      show τ * (τ⁻¹ * x * τ) * τ⁻¹ = x
      group
    refine ⟨τ⁻¹ * x * τ, (hH _).2 ⟨?_, (hPQ _).1 ?_⟩, hconj⟩
    · exact M24g.mul_mem (M24g.mul_mem (M24g.inv_mem hτ) hx.1) hτ
    · rw [show τ * (τ⁻¹ * x * τ) * τ⁻¹ = x by group]
      exact hx.2

@[expose] def H_13_1_partial : Prop :=
  ((∀ g ∈ M24g, ∀ u v : PM24, dot24 (G6.permAct 24 g u) (G6.permAct 24 g v) = dot24 u v) ∧
    (∀ u : PM24, u ≠ 1 → ∃ v : PM24, dot24 u v ≠ 0) ∧
    (∀ v : PM24, v ∈ G6.coreMod 24 ↔ dot24 v (G6.allOnes 24) = 0) ∧
    golayC ≤ G6.coreMod 24 ∧ G6.allOnes 24 ∈ golayC) ∧
  ((∀ u ∈ golayC, ∀ v ∈ golayC, dot24 u v = 0) ∧
    (∀ w : PM24, (∀ c ∈ golayC, dot24 w c = 0) → w ∈ golayC)) ∧
  (rk ↥golayC = 12 ∧ rk ↥(⊤ : Subgroup PM24) - rk ↥golayC = 12 ∧
    rk ↥(G6.coreMod 24) - rk ↥golayC = 11 ∧ rk ↥golayC - rk ↥(Subgroup.zpowers (G6.allOnes 24)) = 11) ∧
  ((∀ c ∈ golayC, c ∉ Subgroup.zpowers (G6.allOnes 24) → ∃ w ∈ G6.coreMod 24, dot24 c w ≠ 0) ∧
    (∀ w ∈ G6.coreMod 24, w ∉ golayC → ∃ c ∈ golayC, dot24 c w ≠ 0)) ∧
  ∀ a b : Fin 24, a ≠ b →
    ((∀ g ∈ M24g, (G6.permAct 24 g (eY {a}) = eY {a} ↔ g a = a) ∧
        (G6.permAct 24 g (eY {a}) * (eY {a})⁻¹ ∈ golayC ↔ g a = a)) ∧
      Nonempty (↥(M23g a) ≃* ↥CFSG.Blueprint.NativeSporadic.M23) ∧
      (∀ g ∈ M24g,
        ((G6.permAct 24 g (eY {a}) = eY {a} ∧ G6.permAct 24 g (eY {b}) = eY {b}) ↔ g ∈ M22g a b) ∧
        ((G6.permAct 24 g (eY {a}) * (eY {a})⁻¹ ∈ golayC ∧
            G6.permAct 24 g (eY {b}) * (eY {b})⁻¹ ∈ golayC) ↔ g ∈ M22g a b)) ∧
      Nonempty (↥(M22g a b) ≃* ↥CFSG.Blueprint.NativeSporadic.M22) ∧
      (∀ g ∈ M24g, (G6.permAct 24 g (eY {a, b}) = eY {a, b} ↔ g ∈ M2ab a b) ∧
        (G6.permAct 24 g (eY {a, b}) * (eY {a, b})⁻¹ ∈ golayC ↔ g ∈ M2ab a b)) ∧
      Nonempty (↥(M2ab a b) ≃* MulAut ↥CFSG.Blueprint.NativeSporadic.M22)) ∧
    (pairVec a b ∈ G6.coreMod 24 ∧ rk ↥(G6.coreMod 24) - rk ↥(golayC ⊔ Subgroup.zpowers (pairVec a b)) = 10 ∧
      rk ↥(golayC ⊓ pairKer a b) - rk ↥(Subgroup.zpowers (G6.allOnes 24)) = 10 ∧
      (∀ c ∈ golayC ⊓ pairKer a b, c ∉ Subgroup.zpowers (G6.allOnes 24) →
        ∃ w ∈ G6.coreMod 24, dot24 c w ≠ 0) ∧
      (∀ w ∈ G6.coreMod 24, w ∉ golayC ⊔ Subgroup.zpowers (pairVec a b) →
        ∃ c ∈ golayC ⊓ pairKer a b, dot24 c w ≠ 0))

@[expose] def H_13_1 : Prop :=
  H_13_1_partial ∧
  golayC = Subgroup.closure {vector : PM24 |
    ∃ octad : Finset (Fin 24), IsOctad octad ∧ eY octad = vector} ∧
  (∀ support : Finset (Fin 24), wt24 (eY support) = support.card) ∧
  (∀ coset : Cocode24,
    (∃ representative : PM24,
      (QuotientGroup.mk representative : Cocode24) = coset ∧
        wt24 representative = cocodeWt24 coset) ∧
    (∀ representative : PM24,
      (QuotientGroup.mk representative : Cocode24) = coset →
        cocodeWt24 coset ≤ wt24 representative)) ∧
  (∀ representative : PM24, ∀ weight : ℕ,
    HasComplementWeight24 (QuotientGroup.mk representative) weight ↔
      weight = wt24 representative ∨
        weight = wt24 (representative * G6.allOnes 24)) ∧
  (∀ representative : PM24,
    wt24 (representative * G6.allOnes 24) = 24 - wt24 representative) ∧
  (∀ a b : Fin 24, a ≠ b → pairVec a b = eY {a, b}) ∧
  (∀ a b : Fin 24, ∀ representative : PM24,
    representative ∈ pairKer a b ↔ dot24 representative (pairVec a b) = 0)

theorem permAct_eY_eq_iff (g : Equiv.Perm (Fin 24)) (S T : Finset (Fin 24)) :
    G6.permAct 24 g (eY S) = eY T ↔ S.map g.toEmbedding = T := by
  rw [permAct_eY]
  constructor
  · exact eY_inj
  · intro h
    rw [h]

theorem perm_single_eq_iff (g : Equiv.Perm (Fin 24)) (a : Fin 24) :
    G6.permAct 24 g (eY {a}) = eY {a} ↔ g a = a := by
  rw [permAct_eY_eq_iff, Finset.map_singleton, Finset.singleton_inj]
  rfl

theorem perm_single_mem_iff (g : Equiv.Perm (Fin 24)) (a : Fin 24) :
    G6.permAct 24 g (eY {a}) * (eY {a})⁻¹ ∈ golayC ↔ g a = a := by
  rw [inv24_eq, permAct_eY, eY_mul_eY_mem_golayC_iff (({a} : Finset (Fin 24)).map g.toEmbedding) ({a} : Finset (Fin 24))
    (by simp),
    Finset.map_singleton, Finset.singleton_inj]
  rfl

theorem perm_pair_eq_iff (g : Equiv.Perm (Fin 24)) (a b : Fin 24) (hab : a ≠ b) :
    G6.permAct 24 g (eY {a, b}) = eY {a, b} ↔ (g a = a ∧ g b = b) ∨ (g a = b ∧ g b = a) := by
  rw [permAct_eY_eq_iff, ← smul_finset_eq_map, smul_pair_eq_iff g a b hab]

theorem perm_pair_mem_iff (g : Equiv.Perm (Fin 24)) (a b : Fin 24) (hab : a ≠ b) :
    G6.permAct 24 g (eY {a, b}) * (eY {a, b})⁻¹ ∈ golayC ↔
      (g a = a ∧ g b = b) ∨ (g a = b ∧ g b = a) := by
  rw [inv24_eq, permAct_eY, eY_mul_eY_mem_golayC_iff (({a, b} : Finset (Fin 24)).map g.toEmbedding)
    ({a, b} : Finset (Fin 24)) (by rw [Finset.card_map, Finset.card_pair hab]; norm_num), ← smul_finset_eq_map,
    smul_pair_eq_iff g a b hab]

theorem pairVec_mem_coreMod_of_ne (a b : Fin 24) (hab : a ≠ b) :
    pairVec a b ∈ G6.coreMod 24 := by
  rw [pairVec_eq_eY_pair a b hab, G6.mem_coreMod, sum_toAdd_eY, Finset.card_pair hab]
  decide

@[expose] noncomputable def conjOn22 (g : ↥mog22plus) : ↥mog22 ≃* ↥mog22 where
  toFun h := ⟨(g : Equiv.Perm (Fin 24)) * h * (g : Equiv.Perm (Fin 24))⁻¹,
    mog22_normal_in_plus g.2 h.2⟩
  invFun h := ⟨(g : Equiv.Perm (Fin 24))⁻¹ * h * ((g : Equiv.Perm (Fin 24))⁻¹)⁻¹,
    mog22_normal_in_plus (mog22plus.inv_mem g.2) h.2⟩
  left_inv h := Subtype.ext (by
    show (g : Equiv.Perm (Fin 24))⁻¹ * ((g : Equiv.Perm (Fin 24)) * h * (g : Equiv.Perm (Fin 24))⁻¹)
      * ((g : Equiv.Perm (Fin 24))⁻¹)⁻¹ = h
    group)
  right_inv h := Subtype.ext (by
    show (g : Equiv.Perm (Fin 24)) * ((g : Equiv.Perm (Fin 24))⁻¹ * h * ((g : Equiv.Perm (Fin 24))⁻¹)⁻¹)
      * (g : Equiv.Perm (Fin 24))⁻¹ = h
    group)
  map_mul' x y := Subtype.ext (by
    show (g : Equiv.Perm (Fin 24)) * ((x : Equiv.Perm (Fin 24)) * (y : Equiv.Perm (Fin 24)))
      * (g : Equiv.Perm (Fin 24))⁻¹ = ((g : Equiv.Perm (Fin 24)) * (x : Equiv.Perm (Fin 24))
      * (g : Equiv.Perm (Fin 24))⁻¹) * ((g : Equiv.Perm (Fin 24)) * (y : Equiv.Perm (Fin 24))
      * (g : Equiv.Perm (Fin 24))⁻¹)
    group)

theorem conjOn22_mul (g k : ↥mog22plus) : conjOn22 (g * k) = conjOn22 g * conjOn22 k := by
  apply MulEquiv.ext
  intro h
  apply Subtype.ext
  show ((g * k : ↥mog22plus) : Equiv.Perm (Fin 24)) * (h : Equiv.Perm (Fin 24)) *
      ((g * k : ↥mog22plus) : Equiv.Perm (Fin 24))⁻¹ =
    (g : Equiv.Perm (Fin 24)) * ((k : Equiv.Perm (Fin 24)) * (h : Equiv.Perm (Fin 24)) *
      (k : Equiv.Perm (Fin 24))⁻¹) * (g : Equiv.Perm (Fin 24))⁻¹
  rw [Subgroup.coe_mul]
  group

theorem conjOn22_one : conjOn22 (1 : ↥mog22plus) = 1 := by
  apply MulEquiv.ext
  intro h
  apply Subtype.ext
  show (1 : Equiv.Perm (Fin 24)) * (h : Equiv.Perm (Fin 24)) * (1 : Equiv.Perm (Fin 24))⁻¹ = h
  group

@[expose] noncomputable def conjHom22 : ↥mog22plus →* MulAut ↥mog22 where
  toFun g := conjOn22 g
  map_one' := conjOn22_one
  map_mul' g k := conjOn22_mul g k

section H13Cert

theorem conjHom22_injective : Function.Injective conjHom22 := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hconj : ∀ h : ↥mog22, (g : Equiv.Perm (Fin 24)) * h * (g : Equiv.Perm (Fin 24))⁻¹ = h := by
    intro h
    have e : conjOn22 g = 1 := hg
    have h1 : conjOn22 g h = h := by
      rw [e]
      rfl
    exact congrArg Subtype.val h1
  have hcent : rho10 mog22plus le_rfl g ∈
      Subgroup.centralizer ((rho10 mog22 mog22_le_mog22plus).range : Set (MulAut W10)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases (MonoidHom.mem_range).1 hy with ⟨x, rfl⟩
    have hcomm : ((⟨(x : Equiv.Perm (Fin 24)), mog22_le_mog22plus x.2⟩ : ↥mog22plus)) * g =
        g * ⟨(x : Equiv.Perm (Fin 24)), mog22_le_mog22plus x.2⟩ := by
      apply Subtype.ext
      show (x : Equiv.Perm (Fin 24)) * (g : Equiv.Perm (Fin 24)) =
        (g : Equiv.Perm (Fin 24)) * (x : Equiv.Perm (Fin 24))
      have := hconj x
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    have hx : rho10 mog22 mog22_le_mog22plus x =
        rho10 mog22plus le_rfl ⟨(x : Equiv.Perm (Fin 24)), mog22_le_mog22plus x.2⟩ := rfl
    rw [hx, ← map_mul, ← map_mul, hcomm]
  rw [centralizer_rho10_mog22, Subgroup.mem_bot] at hcent
  exact rho10_mog22plus_injective (by rw [hcent, map_one])

theorem conjHom22_bijective : Function.Bijective conjHom22 := by
  haveI : Finite (MulAut ↥mog22) := finite_mulAut ↥mog22
  apply Function.Injective.bijective_of_nat_card_le conjHom22_injective
  have h1 := CFSG.Sporadic.Schreier.m22_mulAut_card
  rw [CFSG.Sporadic.Schreier.m22_card] at h1
  rw [card_mulAut_congr mog22EquivM22, card_mog22plus]
  omega

@[expose] noncomputable def mog22plusIso : ↥mog22plus ≃* MulAut ↥mog22 :=
  MulEquiv.ofBijective conjHom22 conjHom22_bijective

theorem nonempty_iso_M23g (a : Fin 24) :
    Nonempty (↥(M23g a) ≃* ↥CFSG.Blueprint.NativeSporadic.M23) := by
  obtain ⟨b, hb⟩ := exists_ne a
  obtain ⟨τ, hτ, hτ0, -⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two a b hb.symm
  have hmap : mog23.map (MulAut.conj τ).toMonoidHom = M23g a := by
    refine map_conj_eq_of_iff τ hτ mog23 (M23g a) (fun x => x a = a) (fun h => h 0 = 0)
      (fun x => mem_M23g_iff a x) (fun h => ?_) (fun h => ?_)
    · show h ∈ M24g ⊓ stab 0 ↔ _
      rw [Subgroup.mem_inf, mem_stab_iff]
    · have e : τ⁻¹ a = 0 := by rw [← hτ0, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      show (τ * h * τ⁻¹) a = a ↔ h 0 = 0
      simp only [Equiv.Perm.mul_apply, e]
      rw [← hτ0, EmbeddingLike.apply_eq_iff_eq]
  exact ⟨(MulEquiv.subgroupCongr hmap).symm.trans
    ((MulEquiv.subgroupMap (MulAut.conj τ) mog23).symm.trans mog23EquivM23)⟩

theorem nonempty_iso_M22g (a b : Fin 24) (hab : a ≠ b) :
    Nonempty (↥(M22g a b) ≃* ↥CFSG.Blueprint.NativeSporadic.M22) := by
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two a b hab
  have hmap : mog22.map (MulAut.conj τ).toMonoidHom = M22g a b := by
    refine map_conj_eq_of_iff τ hτ mog22 (M22g a b) (fun x => x a = a ∧ x b = b)
      (fun h => h 0 = 0 ∧ h 1 = 1) (fun x => mem_M22g_iff a b x) (fun h => ?_) (fun h => ?_)
    · show h ∈ M24g ⊓ stab 0 ⊓ stab 1 ↔ _
      rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_stab_iff, mem_stab_iff]
      exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
    · have e0 : τ⁻¹ a = 0 := by rw [← hτ0, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      have e1 : τ⁻¹ b = 1 := by rw [← hτ1, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      show (τ * h * τ⁻¹) a = a ∧ (τ * h * τ⁻¹) b = b ↔ h 0 = 0 ∧ h 1 = 1
      simp only [Equiv.Perm.mul_apply, e0, e1]
      rw [← hτ0, ← hτ1, EmbeddingLike.apply_eq_iff_eq, EmbeddingLike.apply_eq_iff_eq]
  exact ⟨(MulEquiv.subgroupCongr hmap).symm.trans
    ((MulEquiv.subgroupMap (MulAut.conj τ) mog22).symm.trans mog22EquivM22)⟩

theorem nonempty_iso_M2ab (a b : Fin 24) (hab : a ≠ b) :
    Nonempty (↥(M2ab a b) ≃* MulAut ↥CFSG.Blueprint.NativeSporadic.M22) := by
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two a b hab
  have hmap : mog22plus.map (MulAut.conj τ).toMonoidHom = M2ab a b := by
    refine map_conj_eq_of_iff τ hτ mog22plus (M2ab a b)
      (fun x => (x a = a ∧ x b = b) ∨ (x a = b ∧ x b = a))
      (fun h => (h 0 = 0 ∧ h 1 = 1) ∨ (h 0 = 1 ∧ h 1 = 0))
      (fun x => mem_M2ab_iff a b hab x) (fun h => ?_) (fun h => ?_)
    · show h ∈ M24g ⊓ stabPair01 ↔ _
      rw [Subgroup.mem_inf]
      exact Iff.rfl
    · have e0 : τ⁻¹ a = 0 := by rw [← hτ0, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      have e1 : τ⁻¹ b = 1 := by rw [← hτ1, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      show ((τ * h * τ⁻¹) a = a ∧ (τ * h * τ⁻¹) b = b) ∨ ((τ * h * τ⁻¹) a = b ∧ (τ * h * τ⁻¹) b = a)
        ↔ (h 0 = 0 ∧ h 1 = 1) ∨ (h 0 = 1 ∧ h 1 = 0)
      simp only [Equiv.Perm.mul_apply, e0, e1]
      rw [← hτ0, ← hτ1]
      simp only [EmbeddingLike.apply_eq_iff_eq]
  exact ⟨(MulEquiv.subgroupCongr hmap).symm.trans
    ((MulEquiv.subgroupMap (MulAut.conj τ) mog22plus).symm.trans
      (mog22plusIso.trans (MulAut.congr mog22EquivM22)))⟩

theorem H_13_1_partial_holds : H_13_1_partial := by
  refine ⟨⟨fun g _ u v => dot24_permAct g u v, fun u hu => exists_dot24_ne_zero hu,
      fun v => mem_coreMod_iff_dot_allOnes v, golayC_le_coreMod, allOnes_mem_golayC⟩,
    ⟨fun u hu v hv => golay_dot_eq_zero hu hv, fun w hw => golay_mem_of_dot w hw⟩,
    ⟨rk_golayC, ?_, ?_, ?_⟩,
    ⟨fun c hc hcz => exists_dot_coreMod_of_golay_not_zpowers c hc hcz, ?_⟩, ?_⟩
  · rw [rk_top_PM24, rk_golayC]
  · rw [rk_coreMod, rk_golayC]
  · rw [rk_golayC, rk_zpowers_allOnes]
  · intro w _ hw
    by_contra h
    push_neg at h
    exact hw (golay_mem_of_dot w fun c hc => by
      rw [dot24_comm]
      exact h c hc)
  · intro a b hab
    refine ⟨⟨fun g _ => ⟨perm_single_eq_iff g a, perm_single_mem_iff g a⟩,
      nonempty_iso_M23g a, ?_, nonempty_iso_M22g a b hab, ?_, nonempty_iso_M2ab a b hab⟩,
      pairVec_mem_coreMod_of_ne a b hab, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rw [mem_M22g_iff]
      refine ⟨?_, ?_⟩
      · simp only [perm_single_eq_iff, hg, true_and]
      · simp only [perm_single_mem_iff, hg, true_and]
    · intro g hg
      rw [mem_M2ab_iff a b hab]
      refine ⟨?_, ?_⟩
      · simp only [perm_pair_eq_iff g a b hab, hg, true_and]
      · simp only [perm_pair_mem_iff g a b hab, hg, true_and]
    · rw [rk_coreMod, rk_golay_sup a b hab]
    · rw [rk_golay_pair a b hab, rk_zpowers_allOnes]
    · exact fun c hc hcz => exists_dot_coreMod_of_golay_not_zpowers c (Subgroup.mem_inf.1 hc).1 hcz
    · intro w _ hw
      by_contra h
      push_neg at h
      exact hw (exists_golay_dot_of_not_mem_coreMod_pair a b hab w fun c hc => h c hc)

theorem as_H_13_1 : H_13_1 := by
  refine ⟨H_13_1_partial_holds, golayC_eq_closure_octads, fun support => wt24_eY support,
    cocodeWt24_spec, fun representative weight => hasComplementWeight24_mk_iff representative weight,
    fun representative => wt24_complement representative,
    fun a b hab => pairVec_eq_eY_pair a b hab, fun a b representative =>
      mem_pairKer_iff_dot24 a b representative⟩

end H13Cert

@[expose] def H_13_2 : Prop :=
  ∀ (isCode : Bool) (d : ℕ), (d = 22 ∨ d = 23 ∨ d = 24) → ∀ a b : Fin 24, a ≠ b →
  ∀ (V : Type) [CommGroup V] (ρ : ↥(Ld d a b) →* MulAut V),
    IsMathModule isCode d a b (Ld d a b) ρ →
      Nat.card V = 2 ^ (if d = 22 then 10 else 11) ∧ IsAbsIrredMod ρ.range

private theorem isAbsIrredMod_of_facts {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {m : ℕ}
    (hm : m ≠ 0) (hcard : Nat.card V = 2 ^ m) (hirr : CFSG.Quasithin.H.ModelIrr.IrredAct L)
    (hC : Subgroup.centralizer (L : Set (MulAut V)) = ⊥) : IsAbsIrredMod L := by
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hnt : Nontrivial V := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [hcard]
    exact Nat.one_lt_two_pow hm
  obtain ⟨x, hx⟩ := exists_ne (1 : V)
  refine ⟨⟨fun h => hx (Subgroup.mem_bot.1 (h ▸ Subgroup.mem_top x)), fun U _ hU => hirr U hU⟩,
    fun θ hθ => CFSG.Quasithin.H.ModelIrr.endo_eq_zero_or_id hirr hC θ hθ⟩

section H13Two

theorem as_H_13_2 : H_13_2 := by
  intro isCode d hd a b hab V _ ρ hρ
  obtain ⟨β, hβ⟩ := hρ
  rcases hd with rfl | rfl | rfl
  · cases isCode
    · have hM : MathieuCocode22 ρ.range ⊤ ⊥ :=
        ⟨a, b, hab, ρ.rangeRestrict, (realizesVia_iff _ _ _ _ _).2 ⟨β, hβ⟩⟩
      obtain ⟨hcard, hirr, hC⟩ := CFSG.Quasithin.H.ModelIrr.cocode22_facts hM
      exact ⟨hcard, isAbsIrredMod_of_facts (m := 10) (by norm_num) hcard hirr hC⟩
    · have hM : MathieuCode22 ρ.range ⊤ ⊥ :=
        ⟨a, b, hab, ρ.rangeRestrict, (realizesVia_iff _ _ _ _ _).2 ⟨β, hβ⟩⟩
      obtain ⟨hcard, hirr, hC⟩ := CFSG.Quasithin.H.ModelIrr.code22_facts hM
      exact ⟨hcard, isAbsIrredMod_of_facts (m := 10) (by norm_num) hcard hirr hC⟩
  · cases isCode
    · have hM : MathieuCocode23 ρ.range ⊤ ⊥ :=
        ⟨a, ρ.rangeRestrict, (realizesVia_iff _ _ _ _ _).2 ⟨β, hβ⟩⟩
      obtain ⟨hcard, hirr, hC⟩ := CFSG.Quasithin.H.ModelIrr.cocode23_facts hM
      exact ⟨hcard, isAbsIrredMod_of_facts (m := 11) (by norm_num) hcard hirr hC⟩
    · have hM : MathieuCode23 ρ.range ⊤ ⊥ :=
        ⟨a, ρ.rangeRestrict, (realizesVia_iff _ _ _ _ _).2 ⟨β, hβ⟩⟩
      obtain ⟨hcard, hirr, hC⟩ := CFSG.Quasithin.H.ModelIrr.code23_facts hM
      exact ⟨hcard, isAbsIrredMod_of_facts (m := 11) (by norm_num) hcard hirr hC⟩
  · cases isCode
    · have hM : MathieuCocode24 ρ.range ⊤ ⊥ :=
        ⟨ρ.rangeRestrict, (realizesVia_iff _ _ _ _ _).2 ⟨β, hβ⟩⟩
      obtain ⟨hcard, hirr, hC⟩ := CFSG.Quasithin.H.ModelIrr.cocode24_facts hM
      exact ⟨hcard, isAbsIrredMod_of_facts (m := 11) (by norm_num) hcard hirr hC⟩
    · have hM : MathieuCode24 ρ.range ⊤ ⊥ :=
        ⟨ρ.rangeRestrict, (realizesVia_iff _ _ _ _ _).2 ⟨β, hβ⟩⟩
      obtain ⟨hcard, hirr, hC⟩ := CFSG.Quasithin.H.ModelIrr.code24_facts hM
      exact ⟨hcard, isAbsIrredMod_of_facts (m := 11) (by norm_num) hcard hirr hC⟩

end H13Two

end CFSG.ASVolI

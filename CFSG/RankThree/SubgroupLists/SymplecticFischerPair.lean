module

public import CFSG.RankThree.SubgroupLists.SymplecticInvolutionPairs
public import CFSG.RankThree.SubgroupLists.CliffordModel
public import CFSG.RankThree.SubgroupLists.SymplecticFischerExcl
public import CFSG.Fischer.Classification.Step1

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K] {G : Subgroup (GL V₄ K)}

@[expose] def ncImage (G : Subgroup (GL V₄ K)) (t : G) : Set (G ⧸ Subgroup.center G) :=
  {ω | IsConj (QuotientGroup.mk t : G ⧸ Subgroup.center G) ω}

theorem exists_eq_mk_of_mem_ncImage {t : G} {ω : G ⧸ Subgroup.center G}
    (hω : ω ∈ ncImage G t) : ∃ g : G, ω = QuotientGroup.mk (g * t * g⁻¹) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hω
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  exact ⟨g, by rw [← hc]; rfl⟩

section Center

variable (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
  (hneg : (-1 : GL V₄ K) ∈ G)
include hZ hneg

theorem mk_eq_mk_iff {g h : G} :
    (QuotientGroup.mk g : G ⧸ Subgroup.center G) = QuotientGroup.mk h ↔
      (h : GL V₄ K) = g ∨ (h : GL V₄ K) = -g := by
  rw [QuotientGroup.eq]
  constructor
  · intro hz
    rcases hZ _ hz with h1 | h1
    · left
      have h1' : (g : GL V₄ K)⁻¹ * h = 1 := by simpa using h1
      calc (h : GL V₄ K) = g * ((g : GL V₄ K)⁻¹ * h) := by group
        _ = g := by rw [h1', mul_one]
    · right
      have h1' : (g : GL V₄ K)⁻¹ * h = -1 := by simpa using h1
      calc (h : GL V₄ K) = g * ((g : GL V₄ K)⁻¹ * h) := by group
        _ = -g := by rw [h1', mul_neg_one]
  · rintro (h1 | h1)
    · rw [show h = g from Subtype.ext h1, inv_mul_cancel]
      exact one_mem _
    · have hm : g⁻¹ * h = ⟨-1, hneg⟩ := Subtype.ext (by simp [h1])
      rw [hm, Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      simp

theorem mk_eq_one_iff {g : G} :
    (QuotientGroup.mk g : G ⧸ Subgroup.center G) = 1 ↔
      (g : GL V₄ K) = 1 ∨ (g : GL V₄ K) = -1 := by
  have h := mk_eq_mk_iff hZ hneg (g := 1) (h := g)
  rw [QuotientGroup.mk_one] at h
  rw [eq_comm, h]
  simp

end Center

section Pairs

variable (h2 : (2 : K) ≠ 0)
  (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
  (hneg : (-1 : GL V₄ K) ∈ G)
include h2 hZ hneg

theorem mk_commute_iff {d e : G} (hd : IsNCInv (d : GL V₄ K)) (he : IsNCInv (e : GL V₄ K)) :
    (QuotientGroup.mk d : G ⧸ Subgroup.center G) * QuotientGroup.mk e =
        QuotientGroup.mk e * QuotientGroup.mk d ↔
      (e : GL V₄ K) = d ∨ (e : GL V₄ K) = -d ∨
        cliffB ((d : GL V₄ K) : Matrix V₄ V₄ K) ((e : GL V₄ K) : Matrix V₄ V₄ K) = 0 := by
  obtain ⟨hdS, hd2, hd1, hdm⟩ := hd
  obtain ⟨heS, he2, he1, hem⟩ := he
  have hdM := (mem_cliffSpace_of_involution h2 hdS hd2 hd1 hdm).1
  have heM := (mem_cliffSpace_of_involution h2 heS he2 he1 hem).1
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mk_eq_mk_iff hZ hneg]
  simp only [Subgroup.coe_mul]
  constructor
  · rintro (h | h)
    · rcases eq_of_commute_involution h2 hdS heS hd2 he2 h.symm hd1 hdm with h' | h' | h' | h'
      · exact absurd h' he1
      · exact absurd h' hem
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · right; right
      rw [← mul_eq_neg_mul_iff h2 hdM heM]
      have := congrArg (fun x : GL V₄ K => (x : Matrix V₄ V₄ K)) h
      simp only [Units.val_mul, Units.val_neg] at this
      rw [this, neg_neg]
  · rintro (h | h | h)
    · left; rw [h]
    · left; rw [h, neg_mul, mul_neg]
    · right
      apply Units.ext
      have := (mul_eq_neg_mul_iff h2 hdM heM).mpr h
      simp only [Units.val_mul, Units.val_neg]
      rw [this, neg_neg]

theorem orderOf_mk_mul_mem {d e : G} (hd : IsNCInv (d : GL V₄ K)) (he : IsNCInv (e : GL V₄ K))
    (hB : (e : GL V₄ K) = d ∨ (e : GL V₄ K) = -d ∨
      cliffB ((d : GL V₄ K) : Matrix V₄ V₄ K) ((e : GL V₄ K) : Matrix V₄ V₄ K) = 0 ∨
      cliffB ((d : GL V₄ K) : Matrix V₄ V₄ K) ((e : GL V₄ K) : Matrix V₄ V₄ K) = 2⁻¹ ∨
      cliffB ((d : GL V₄ K) : Matrix V₄ V₄ K) ((e : GL V₄ K) : Matrix V₄ V₄ K) = -2⁻¹) :
    orderOf ((QuotientGroup.mk d : G ⧸ Subgroup.center G) * QuotientGroup.mk e) ∈
      ({1, 2, 3} : Set ℕ) := by
  obtain ⟨hdS, hd2, hd1, hdm⟩ := hd
  obtain ⟨heS, he2, he1, hem⟩ := he
  have hdM := (mem_cliffSpace_of_involution h2 hdS hd2 hd1 hdm).1
  have heM := (mem_cliffSpace_of_involution h2 heS he2 he1 hem).1
  have hdd : ((d : GL V₄ K) : Matrix V₄ V₄ K) * (d : GL V₄ K) = 1 := by
    rw [← Units.val_mul, hd2, Units.val_one]
  have hee : ((e : GL V₄ K) : Matrix V₄ V₄ K) * (e : GL V₄ K) = 1 := by
    rw [← Units.val_mul, he2, Units.val_one]
  have hsq := mul_sq_of_involutions h2 hdM heM hdd hee
  set X : Matrix V₄ V₄ K := ((d : GL V₄ K) : Matrix V₄ V₄ K) * (e : GL V₄ K) with hX
  rw [← QuotientGroup.mk_mul]
  have hxM : (((d * e : G) : GL V₄ K) : Matrix V₄ V₄ K) = X := by
    rw [Subgroup.coe_mul, Units.val_mul]
  have key : ∀ n : ℕ, X ^ n = 1 ∨ X ^ n = -1 →
      orderOf (QuotientGroup.mk (d * e) : G ⧸ Subgroup.center G) ∣ n := by
    intro n hn
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, mk_eq_one_iff hZ hneg]
    rcases hn with hn | hn
    · left
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hxM, hn, Units.val_one]
    · right
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hxM, hn, Units.val_neg, Units.val_one]
  have mem12 : orderOf (QuotientGroup.mk (d * e) : G ⧸ Subgroup.center G) ∣ 2 →
      orderOf (QuotientGroup.mk (d * e) : G ⧸ Subgroup.center G) ∈ ({1, 2, 3} : Set ℕ) := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h' | h' <;> rw [h'] <;> simp
  have mem13 : orderOf (QuotientGroup.mk (d * e) : G ⧸ Subgroup.center G) ∣ 3 →
      orderOf (QuotientGroup.mk (d * e) : G ⧸ Subgroup.center G) ∈ ({1, 2, 3} : Set ℕ) := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h' | h' <;> rw [h'] <;> simp
  rcases hB with h | h | h | h | h
  · refine mem12 (key 2 (Or.inl ?_))
    rw [hX, h, pow_two, hdd, mul_one]
  · refine mem12 (key 2 (Or.inl ?_))
    rw [hX, h, Units.val_neg, mul_neg, pow_two, hdd, neg_mul_neg, mul_one]
  · refine mem12 (key 2 (Or.inr ?_))
    rw [pow_two, hsq, h, mul_zero, zero_smul, zero_sub]
  · refine mem13 (key 3 (Or.inr ?_))
    have hX2 : X * X = X - 1 := by rw [hsq, h, mul_inv_cancel₀ h2, one_smul]
    calc X ^ 3 = X * X * X := by rw [pow_succ, pow_two]
      _ = (X - 1) * X := by rw [hX2]
      _ = X * X - X := by rw [sub_mul, one_mul]
      _ = -1 := by rw [hX2]; abel
  · refine mem13 (key 3 (Or.inl ?_))
    have hX2 : X * X = -X - 1 := by
      rw [hsq, h, mul_neg, mul_inv_cancel₀ h2, neg_smul, one_smul]
    calc X ^ 3 = X * X * X := by rw [pow_succ, pow_two]
      _ = (-X - 1) * X := by rw [hX2]
      _ = -(X * X) - X := by rw [sub_mul, one_mul, neg_mul]
      _ = 1 := by rw [hX2]; abel

end Pairs

@[expose] def IsThreePair (d e : GL V₄ K) : Prop :=
  e = d ∨ e = -d ∨ cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K) = 0 ∨
    cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K) = 2⁻¹ ∨
    cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K) = -2⁻¹

theorem IsThreePair.conj (h2 : (2 : K) ≠ 0) {d e : GL V₄ K}
    (hd : (d : Matrix V₄ V₄ K) ∈ (cliffSpace : Submodule K _))
    (he : (e : Matrix V₄ V₄ K) ∈ (cliffSpace : Submodule K _)) (h : IsThreePair d e)
    (c : GL V₄ K) : IsThreePair (c * d * c⁻¹) (c * e * c⁻¹) := by
  have hB : cliffB ((c * d * c⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)
      ((c * e * c⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = cliffB (d : Matrix V₄ V₄ K) e := by
    simp only [Units.val_mul]
    exact cliffB_conj h2 c hd he
  rcases h with h | h | h | h | h
  · left; rw [h]
  · right; left; rw [h, mul_neg, neg_mul]
  · right; right; left; rw [hB, h]
  · right; right; right; left; rw [hB, h]
  · right; right; right; right; rw [hB, h]

theorem isThreePair_zmod_three (d e : GL V₄ (ZMod 3)) : IsThreePair d e := by
  have hinv : (2 : ZMod 3)⁻¹ = 2 := inv_eq_of_mul_eq_one_right (by decide)
  have h : ∀ x : ZMod 3, x = 0 ∨ x = 2⁻¹ ∨ x = -2⁻¹ := by
    rw [hinv]
    decide
  rcases h (cliffB (d : Matrix V₄ V₄ (ZMod 3)) (e : Matrix V₄ V₄ (ZMod 3))) with h | h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem conj_isNCInv (hGS : G ≤ StatedSp 2 K) {t : G} (ht : IsNCInv (t : GL V₄ K)) (g : G) :
    IsNCInv ((g * t * g⁻¹ : G) : GL V₄ K) := by
  have := ht.conj (hGS g.2)
  simpa using this

theorem isThreePair_conj_conj (h2 : (2 : K) ≠ 0) (hGS : G ≤ StatedSp 2 K) {t : G}
    (ht : IsNCInv (t : GL V₄ K))
    (hθ : ∀ g : G, IsThreePair (t : GL V₄ K) ((g * t * g⁻¹ : G) : GL V₄ K)) (g h : G) :
    IsThreePair ((g * t * g⁻¹ : G) : GL V₄ K) ((h * t * h⁻¹ : G) : GL V₄ K) := by
  have htM := (mem_cliffSpace_of_involution h2 ht.1 ht.2.1 ht.2.2.1 ht.2.2.2).1
  have hs := conj_isNCInv hGS ht (g⁻¹ * h)
  have hsM := (mem_cliffSpace_of_involution h2 hs.1 hs.2.1 hs.2.2.1 hs.2.2.2).1
  have := (hθ (g⁻¹ * h)).conj h2 htM hsM (g : GL V₄ K)
  have e1 : ((g * t * g⁻¹ : G) : GL V₄ K) = (g : GL V₄ K) * t * (g : GL V₄ K)⁻¹ := by simp
  have e2 : ((h * t * h⁻¹ : G) : GL V₄ K) =
      (g : GL V₄ K) * (((g⁻¹ * h) * t * (g⁻¹ * h)⁻¹ : G) : GL V₄ K) * (g : GL V₄ K)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e1, e2]
  exact this

theorem fischerHyp_ncImage [Finite G] (h2 : (2 : K) ≠ 0) (hGS : G ≤ StatedSp 2 K)
    (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) {t : G} (ht : IsNCInv (t : GL V₄ K))
    (hθ : ∀ g : G, IsThreePair (t : GL V₄ K) ((g * t * g⁻¹ : G) : GL V₄ K)) :
    CFSG.Fischer.Classification.Hyp (G ⧸ Subgroup.center G) (ncImage G t) := by
  classical
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2.1
  have : Group.IsPerfect G := hq.1
  have hτ1 : (QuotientGroup.mk t : G ⧸ Subgroup.center G) ≠ 1 := by
    rw [Ne, mk_eq_one_iff hZ hneg]
    rintro (h | h)
    · exact ht.2.2.1 h
    · exact ht.2.2.2 h
  refine ⟨⟨inferInstance, ⟨QuotientGroup.mk t, rfl⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro ω hω
    obtain ⟨g, rfl⟩ := exists_eq_mk_of_mem_ncImage hω
    have hs := conj_isNCInv hGS ht g
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← QuotientGroup.mk_mul, mk_eq_one_iff hZ hneg]
      left
      rw [Subgroup.coe_mul]
      exact hs.2.1
    · rw [Ne, mk_eq_one_iff hZ hneg]
      rintro (h | h)
      · exact hs.2.2.1 h
      · exact hs.2.2.2 h
  · intro ω₁ hω₁ ω₂ hω₂
    obtain ⟨g, rfl⟩ := exists_eq_mk_of_mem_ncImage hω₁
    obtain ⟨h, rfl⟩ := exists_eq_mk_of_mem_ncImage hω₂
    exact orderOf_mk_mul_mem h2 hZ hneg (conj_isNCInv hGS ht g) (conj_isNCInv hGS ht h)
      (isThreePair_conj_conj h2 hGS ht hθ g h)
  · have hcl : Subgroup.closure (ncImage G t) =
        Subgroup.normalClosure {(QuotientGroup.mk t : G ⧸ Subgroup.center G)} := by
      unfold Subgroup.normalClosure
      congr 1
      ext ω
      rw [Group.mem_conjugatesOfSet_iff]
      constructor
      · intro hω
        exact ⟨_, rfl, hω⟩
      · rintro ⟨a, ha, hω⟩
        rw [Set.mem_singleton_iff] at ha
        subst ha
        exact hω
    rw [hcl]
    rcases (inferInstance : (Subgroup.normalClosure
        {(QuotientGroup.mk t : G ⧸ Subgroup.center G)}).Normal).eq_bot_or_eq_top with h | h
    · exfalso
      apply hτ1
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.subset_normalClosure rfl
    · exact h
  · rcases (inferInstance : (Subgroup.center (G ⧸ Subgroup.center G)).Normal).eq_bot_or_eq_top
      with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hq.2.2
      apply hab
      have : b ∈ Subgroup.center (G ⧸ Subgroup.center G) := h ▸ Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp this a
  · have hc : commutator (G ⧸ Subgroup.center G) = ⊤ := Group.IsPerfect.commutator_eq_top
    exact ((MulEquiv.subgroupCongr hc).trans Subgroup.topEquiv).isSimpleGroup

theorem cliffB_zero_left (Y : Matrix V₄ V₄ K) : cliffB 0 Y = 0 := by simp [cliffB]

theorem cliffB_smul_sub_right (Z Y Y' : Matrix V₄ V₄ K) (x : K) :
    cliffB Z (x • Y - Y') = x * cliffB Z Y - cliffB Z Y' := by
  simp only [cliffB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem cliffB_sum_smul_left {ι : Type*} (S : Finset ι) (c : ι → K) (v : ι → Matrix V₄ V₄ K)
    (Y : Matrix V₄ V₄ K) : cliffB (∑ i ∈ S, c i • v i) Y = ∑ i ∈ S, c i * cliffB (v i) Y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [cliffB_zero_left]
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, cliffB_add_left, cliffB_smul_left, ih]

theorem cliffMat_zero : cliffMat (0 : K) 0 0 0 0 = 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp [cliffMat]

theorem isSymplecticType_ncImage (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (hGS : G ≤ StatedSp 2 K)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) {t : G} (ht : IsNCInv (t : GL V₄ K))
    (hθ : ∀ g : G, IsThreePair (t : GL V₄ K) ((g * t * g⁻¹ : G) : GL V₄ K)) :
    CFSG.Fischer.Classification.IsSymplecticType (ncImage G t) := by
  intro ω₁ hω₁ ω₂ hω₂ ω₃ hω₃ hne
  obtain ⟨g, rfl⟩ := exists_eq_mk_of_mem_ncImage hω₁
  obtain ⟨h, rfl⟩ := exists_eq_mk_of_mem_ncImage hω₂
  obtain ⟨k, rfl⟩ := exists_eq_mk_of_mem_ncImage hω₃
  have ha := conj_isNCInv hGS ht g
  have hb := conj_isNCInv hGS ht h
  have hc := conj_isNCInv hGS ht k
  have hab := isThreePair_conj_conj h2 hGS ht hθ g h
  have hca := isThreePair_conj_conj h2 hGS ht hθ k g
  have hcb := isThreePair_conj_conj h2 hGS ht hθ k h
  set a : G := g * t * g⁻¹ with ha_def
  set b : G := h * t * h⁻¹ with hb_def
  set c : G := k * t * k⁻¹ with hc_def
  have haM := (mem_cliffSpace_of_involution h2 ha.1 ha.2.1 ha.2.2.1 ha.2.2.2).1
  have hbM := (mem_cliffSpace_of_involution h2 hb.1 hb.2.1 hb.2.2.1 hb.2.2.2).1
  have hAA : ((a : GL V₄ K) : Matrix V₄ V₄ K) * (a : GL V₄ K) = 1 := by
    rw [← Units.val_mul, ha.2.1, Units.val_one]
  have haa : a * a = 1 := Subtype.ext (by rw [Subgroup.coe_mul]; exact ha.2.1)
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hw : a * b * a = (a * h) * t * (a * h)⁻¹ := by
    calc a * b * a = a * b * a⁻¹ := by rw [hainv]
      _ = (a * h) * t * (a * h)⁻¹ := by rw [hb_def]; group
  have hwN := conj_isNCInv hGS ht (a * h)
  have hcw := isThreePair_conj_conj h2 hGS ht hθ k (a * h)
  rw [← hw] at hwN hcw
  have hmkw : (QuotientGroup.mk a : G ⧸ Subgroup.center G) * QuotientGroup.mk b *
      QuotientGroup.mk a = QuotientGroup.mk (a * b * a) := rfl
  rw [hmkw, mk_commute_iff h2 hZ hneg hc ha, mk_commute_iff h2 hZ hneg hc hb,
    mk_commute_iff h2 hZ hneg hc hwN]
  rw [Ne, mk_commute_iff h2 hZ hneg ha hb] at hne
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨hca1, hca2, hca3⟩, ⟨hcb1, hcb2, hcb3⟩, ⟨hcw1, hcw2, hcw3⟩⟩ := hcon
  push Not at hne
  obtain ⟨hab1, hab2, hab3⟩ := hne
  have pm : ∀ {d e : GL V₄ K}, IsThreePair d e → e ≠ d → e ≠ -d →
      cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K) ≠ 0 →
      cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K) *
        cliffB (d : Matrix V₄ V₄ K) (e : Matrix V₄ V₄ K) = 2⁻¹ * 2⁻¹ := by
    intro d e hde h1 h2' h3'
    rcases hde with h | h | h | h | h
    · exact absurd h h1
    · exact absurd h h2'
    · exact absurd h h3'
    · rw [h]
    · rw [h]; ring
  have hβ := pm hab hab1 hab2 hab3
  have hγ := pm hca hca1 hca2 hca3
  have hδ := pm hcb hcb1 hcb2 hcb3
  have hσ := pm hcw hcw1 hcw2 hcw3
  have hwM : (((a * b * a : G) : GL V₄ K) : Matrix V₄ V₄ K) =
      (2 * cliffB ((a : GL V₄ K) : Matrix V₄ V₄ K) ((b : GL V₄ K) : Matrix V₄ V₄ K)) •
        ((a : GL V₄ K) : Matrix V₄ V₄ K) - ((b : GL V₄ K) : Matrix V₄ V₄ K) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
    exact mul_mul_eq_reflection h2 haM hAA hbM
  rw [hwM, cliffB_smul_sub_right] at hσ
  set β := cliffB ((a : GL V₄ K) : Matrix V₄ V₄ K) ((b : GL V₄ K) : Matrix V₄ V₄ K)
  set γ := cliffB ((c : GL V₄ K) : Matrix V₄ V₄ K) ((a : GL V₄ K) : Matrix V₄ V₄ K)
  set δ := cliffB ((c : GL V₄ K) : Matrix V₄ V₄ K) ((b : GL V₄ K) : Matrix V₄ V₄ K)
  have h22 : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have hr : (2 : K)⁻¹ ≠ 0 := inv_ne_zero h2
  have hu : (2 * β * γ) * (2 * β * γ) = 2⁻¹ * 2⁻¹ := by
    calc (2 * β * γ) * (2 * β * γ) = 4 * (β * β) * (γ * γ) := by ring
      _ = 4 * (2⁻¹ * 2⁻¹) * (2⁻¹ * 2⁻¹) := by rw [hβ, hγ]
      _ = 2⁻¹ * 2⁻¹ := by
        linear_combination (2⁻¹ * 2⁻¹ * (2 * 2⁻¹ + 1) : K) * h22
  have hfac : (2 * β * γ - δ) * (2 * β * γ + δ) = 0 := by linear_combination hu - hδ
  rcases mul_eq_zero.mp hfac with h0 | h0
  · rw [h0, mul_zero] at hσ
    exact mul_ne_zero hr hr hσ.symm
  · have hσ' : (2 * β * γ - δ) * (2 * β * γ - δ) = 4 * (δ * δ) := by
      have : 2 * β * γ = -δ := by linear_combination h0
      rw [this]; ring
    rw [hσ', hδ] at hσ
    apply h3
    have : (3 : K) * (2⁻¹ * 2⁻¹) = 0 := by linear_combination hσ
    exact (mul_eq_zero.mp this).resolve_right (mul_ne_zero hr hr)

theorem false_of_six_commuting (h2 : (2 : K) ≠ 0) (hGS : G ≤ StatedSp 2 K)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) {t : G} (ht : IsNCInv (t : GL V₄ K))
    (s : Fin 6 → G ⧸ Subgroup.center G) (hs : Function.Injective s)
    (hsD : ∀ i, s i ∈ ncImage G t) (hcomm : ∀ i j, s i * s j = s j * s i) : False := by
  classical
  choose g hg using fun i => exists_eq_mk_of_mem_ncImage (hsD i)
  have hN : ∀ i, IsNCInv ((g i * t * (g i)⁻¹ : G) : GL V₄ K) := fun i => conj_isNCInv hGS ht (g i)
  set d : Fin 6 → Matrix V₄ V₄ K :=
    fun i => (((g i * t * (g i)⁻¹ : G) : GL V₄ K) : Matrix V₄ V₄ K) with hd_def
  have hdM : ∀ i, d i ∈ (cliffSpace : Submodule K _) := fun i =>
    (mem_cliffSpace_of_involution h2 (hN i).1 (hN i).2.1 (hN i).2.2.1 (hN i).2.2.2).1
  have hQ : ∀ i, cliffB (d i) (d i) = 1 := fun i => by
    rw [cliffB_self h2]
    exact (mem_cliffSpace_of_involution h2 (hN i).1 (hN i).2.1 (hN i).2.2.1 (hN i).2.2.2).2
  have horth : ∀ i j, i ≠ j → cliffB (d i) (d j) = 0 := by
    intro i j hij
    have hc := hcomm i j
    rw [hg i, hg j] at hc
    rcases (mk_commute_iff h2 hZ hneg (hN i) (hN j)).mp hc with h | h | h
    · exact absurd (hs (by rw [hg i, hg j, mk_eq_mk_iff hZ hneg]; exact Or.inl h)) hij
    · exact absurd (hs (by rw [hg i, hg j, mk_eq_mk_iff hZ hneg]; exact Or.inr h)) hij
    · exact h
  have hli : LinearIndependent K d := by
    rw [linearIndependent_iff']
    intro S c hc i hi
    have := congrArg (fun Z => cliffB Z (d i)) hc
    simp only [cliffB_sum_smul_left, cliffB_zero_left] at this
    rwa [Finset.sum_eq_single i (fun j _ hji => by rw [horth j i hji, mul_zero])
      (fun h => absurd hi h), hQ, mul_one] at this
  let φ : Matrix V₄ V₄ K →ₗ[K] (Fin 5 → K) :=
    { toFun := fun Z => ![Z (Sum.inl 0) (Sum.inl 0), Z (Sum.inl 0) (Sum.inl 1),
        Z (Sum.inl 1) (Sum.inl 0), Z (Sum.inl 0) (Sum.inr 1), Z (Sum.inr 0) (Sum.inl 1)]
      map_add' := fun Z Y => by ext k; fin_cases k <;> rfl
      map_smul' := fun c Z => by ext k; fin_cases k <;> rfl }
  have hdisj : Disjoint (Submodule.span K (Set.range d)) (LinearMap.ker φ) := by
    rw [Submodule.disjoint_def]
    intro Z hZ hZk
    have hZM : Z ∈ (cliffSpace : Submodule K _) :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hdM i) hZ
    rw [LinearMap.mem_ker] at hZk
    have c0 : Z (Sum.inl 0) (Sum.inl 0) = 0 := congrFun hZk 0
    have c1 : Z (Sum.inl 0) (Sum.inl 1) = 0 := congrFun hZk 1
    have c2 : Z (Sum.inl 1) (Sum.inl 0) = 0 := congrFun hZk 2
    have c3 : Z (Sum.inl 0) (Sum.inr 1) = 0 := congrFun hZk 3
    have c4 : Z (Sum.inr 0) (Sum.inl 1) = 0 := congrFun hZk 4
    rw [eq_cliffMat_of_mem h2 hZM, c0, c1, c2, c3, c4, cliffMat_zero]
  have := (hli.map hdisj).fintype_card_le_finrank
  simp at this

open CFSG.Fischer.Classification CFSG.Blueprint.Fischer CFSG.Open in
theorem sym_or_sp_or_o_of_symplecticType {X : Type} [Group X] {E : Set X} (hH : Hyp X E)
    (hsymp : IsSymplecticType E) :
    (∃ m : ℕ, (m = 3 ∨ 5 ≤ m) ∧ ∃ φ : X ≃* Equiv.Perm (Fin m), ∀ g : X, g ∈ E ↔ (φ g).IsSwap) ∨
    (∃ m : ℕ, 2 ≤ m ∧ ∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, b x x = 0) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      fischerLinearModel E
        (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
        (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) ∨
    (∃ m : ℕ, 2 ≤ m ∧ ∃ Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) ∧
      (m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
        Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) ∧
      fischerLinearModel E
        (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
        (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) := by
  have htrans : ∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, ∀ e ∈ E, a ≠ b → a * b = b * a → c ≠ e →
      c * e = e * c → ∃ g : X, g * a * g⁻¹ = c ∧ g * b * g⁻¹ = e :=
    fun _ ha _ hb _ hc _ he hab habc hce hcec =>
      Pair.exists_conj_pair_of_commute hH.pair hH.center hH.simple ha hb hc he hab habc hce hcec
  rcases (Symplectic.sympConfig hH.pair hH.center hH.simple hsymp htrans).trichotomy with
    ⟨hall, hpair⟩ | ⟨⟨Q, hpol, hQ⟩, hpair⟩ | hTN
  · exact Or.inr (Or.inl (Symplectic.classicalConclusion_sp hH.pair hH.center hH.simple hsymp
      htrans hall hpair))
  · exact Or.inr (Or.inr (Symplectic.classicalConclusion_o hH.pair hH.center hH.simple hsymp
      htrans hpol hQ hpair))
  · exact Or.inl (Symplectic.classicalConclusion_sym hH.pair hH.center hH.simple hsymp htrans hTN)

theorem false_of_threeTranspositions (hSpC : FischerSpClique) (hOC : FischerOrthClique)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (hGS : G ≤ StatedSp 2 K) [Finite G]
    (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) {t : G} (ht : IsNCInv (t : GL V₄ K))
    (hθ : ∀ g : G, IsThreePair (t : GL V₄ K) ((g * t * g⁻¹ : G) : GL V₄ K)) : False := by
  unfold FischerSpClique at hSpC
  unfold FischerOrthClique at hOC
  have hH := fischerHyp_ncImage h2 hGS hq hZ hneg ht hθ
  have hsymp := isSymplecticType_ncImage h2 h3 hGS hZ hneg ht hθ
  have : Group.IsPerfect G := hq.1
  rcases sym_or_sp_or_o_of_symplecticType hH hsymp with
    ⟨m, hm, φ, -⟩ | ⟨m, hm, b, halt, hnd, φ, hφ⟩ | ⟨m, hm, Q, hpol, -, φ, hφ⟩
  · have : Group.IsPerfect (Equiv.Perm (Fin m)) :=
      Group.IsPerfect.ofSurjective (f := φ.toMonoidHom) φ.surjective
    exact fischerSymNotPerfect m (by omega) this
  · have hHP : Group.IsPerfect (CFSG.Open.fischerMatrixGroup fun A =>
        ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) :=
      Group.IsPerfect.ofSurjective (f := φ.toMonoidHom) φ.surjective
    obtain ⟨s, hs, hsT, hsc⟩ := hSpC m hm b halt hnd hHP
    refine false_of_six_commuting h2 hGS hZ hneg ht (fun i => φ.symm (s i))
      (φ.symm.injective.comp hs) (fun i => ?_) (fun i j => ?_)
    · rw [hφ, MulEquiv.apply_symm_apply]
      exact hsT i
    · rw [← map_mul, ← map_mul, hsc]
  · have hHP : Group.IsPerfect (CFSG.Open.fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x) :=
      Group.IsPerfect.ofSurjective (f := φ.toMonoidHom) φ.surjective
    obtain ⟨s, hs, hsT, hsc⟩ := hOC m hm Q hpol hHP
    refine false_of_six_commuting h2 hGS hZ hneg ht (fun i => φ.symm (s i))
      (φ.symm.injective.comp hs) (fun i => ?_) (fun i j => ?_)
    · rw [hφ, MulEquiv.apply_symm_apply]
      exact hsT i
    · rw [← map_mul, ← map_mul, hsc]

end CFSG.RankThree.SubgroupLists

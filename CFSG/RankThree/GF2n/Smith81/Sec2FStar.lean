module

public import CFSG.RankThree.GF2n.Smith81.Sec2Defs
public import CFSG.RankThree.GF2n.Smith81.TiRecognition

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

section Frattini

variable [Finite G] {M Q Z : Subgroup G}

theorem inf_centralizer_ne_bot_of_isPGroup {P : Subgroup G} (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    P ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hne' : (⊤ : Subgroup P) ≠ ⊥ := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨a, Subgroup.mem_top a⟩, fun h => ha (by
      simpa using congrArg Subtype.val h)⟩
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal (H := (⊤ : Subgroup P)) hne')
  intro h
  have hyP : (y : G) ∈ P := y.2
  have hyC : (y : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  have hmem : (y : G) ∈ P ⊓ Subgroup.centralizer (P : Set G) := ⟨hyP, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem normalizer_le_M_of_le (H : StrothHyp M Q Z) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hQP : Q ≤ P) : Subgroup.normalizer (P : Set G) ≤ M := by
  have hZP : Z ≤ P := H.Z_normal.1.trans hQP
  have hZne : Z ≠ ⊥ := by
    intro h
    have := H.q4
    rw [h, Subgroup.card_bot] at this
    omega
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff] at hZP
    exact hZne hZP
  set Z₀ : Subgroup G := P ⊓ Subgroup.centralizer (P : Set G) with hZ₀
  have hZ₀ne : Z₀ ≠ ⊥ := inf_centralizer_ne_bot_of_isPGroup hP hPne
  have hZ₀Z : Z₀ ≤ Z := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (Q : Set G) := Subgroup.centralizer_le hQP hx.2
    rwa [H.centralizer_Q] at hxC
  intro n hn
  have hnZ₀ : n ∈ Subgroup.normalizer (Z₀ : Set G) :=
    mem_normalizer_inf hn (mem_normalizer_centralizer hn)
  exact H.toTim81Hyp.normalizer_le_M hZ₀Z hZ₀ne hnZ₀

theorem exists_sylow_of_normal (H : StrothHyp M Q Z) {X : Subgroup G} [X.Normal] (hQX : Q ≤ X) :
    ∃ P : Sylow 2 ↥X, Q ≤ (P : Subgroup ↥X).map X.subtype ∧
      Subgroup.normalizer (((P : Subgroup ↥X).map X.subtype : Subgroup G) : Set G) ≤ M ∧
      Subgroup.normalizer (((P : Subgroup ↥X).map X.subtype : Subgroup G) : Set G) ⊔ X = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (Q.subgroupOf X) := by
    intro y
    obtain ⟨k, hk⟩ := isPGroup_Q' H (⟨(y : G), y.2⟩ : Q)
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  obtain ⟨P, hQP⟩ := hQ2.exists_le_sylow
  have hfr := Sylow.normalizer_sup_eq_top P
  have hQP' : Q ≤ (P : Subgroup ↥X).map X.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hQX]
    exact Subgroup.map_mono hQP
  have hP'2 : IsPGroup 2 ((P : Subgroup ↥X).map X.subtype) := P.isPGroup'.map X.subtype
  exact ⟨P, hQP', normalizer_le_M_of_le H hP'2 hQP', hfr⟩

theorem exists_mul_of_normal (H : StrothHyp M Q Z) {X : Subgroup G} [X.Normal] (hQX : Q ≤ X)
    (g : G) : ∃ x ∈ X, ∃ m ∈ M, g = x * m := by
  obtain ⟨P, -, hnM, hfr⟩ := exists_sylow_of_normal H hQX
  have hg : g ∈ X ⊔ Subgroup.normalizer
      (((P : Subgroup ↥X).map X.subtype : Subgroup G) : Set G) := by
    rw [sup_comm, hfr]
    exact Subgroup.mem_top g
  obtain ⟨x, hx, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  exact ⟨x, hx, m, hnM hm, rfl⟩

theorem exists_mul_of_normalClosure (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (g : G) : ∃ x ∈ Subgroup.normalClosure ({z} : Set G), ∃ m ∈ M, g = x * m := by
  haveI : (Subgroup.normalClosure ({z} : Set G)).Normal := Subgroup.normalClosure_normal
  exact exists_mul_of_normal H (Q_le_normalClosure H hz hz1) g

theorem exists_involution_center_sylow (H : StrothHyp M Q Z) {X : Subgroup G} [X.Normal]
    (hQX : Q ≤ X) : ∃ (P : Sylow 2 ↥X) (z₀ : G), z₀ ∈ Z ∧ z₀ ≠ 1 ∧
      z₀ ∈ (P : Subgroup ↥X).map X.subtype ∧
      ∀ p ∈ (P : Subgroup ↥X).map X.subtype, p * z₀ = z₀ * p := by
  obtain ⟨P, hQP', -, -⟩ := exists_sylow_of_normal H hQX
  set P' : Subgroup G := (P : Subgroup ↥X).map X.subtype with hP'
  have hP'2 : IsPGroup 2 P' := P.isPGroup'.map X.subtype
  have hZne : Z ≠ ⊥ := by
    intro h
    have := H.q4
    rw [h, Subgroup.card_bot] at this
    omega
  have hP'ne : P' ≠ ⊥ := by
    intro h
    have := H.Z_normal.1.trans hQP'
    rw [h, le_bot_iff] at this
    exact hZne this
  obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (inf_centralizer_ne_bot_of_isPGroup hP'2 hP'ne)
  have hz₀Z : z₀ ∈ Z := by
    have : z₀ ∈ Subgroup.centralizer (Q : Set G) := Subgroup.centralizer_le hQP' hz₀.2
    rwa [H.centralizer_Q] at this
  exact ⟨P, z₀, hz₀Z, fun h => hz₀1 (Subtype.ext h), hz₀.1,
    fun p hp => Subgroup.mem_centralizer_iff.mp hz₀.2 p hp⟩

theorem exists_pow_conj_of_cartan (H : StrothHyp M Q Z) {k : G} (hkM : k ∈ M)
    (hkreg : ∀ i : ℕ, 0 < i → i < Nat.card Z - 1 → ∀ v ∈ Z, k ^ i * v = v * k ^ i → v = 1)
    {z z' : G} (hz : z ∈ Z) (hz1 : z ≠ 1) (hz' : z' ∈ Z) (hz1' : z' ≠ 1) :
    ∃ i : ℕ, k ^ i * z * (k ^ i)⁻¹ = z' := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  set q := Nat.card Z with hq
  have hq4 : 4 ≤ q := H.q4
  have hconjZ : ∀ (m : G), m ∈ M → ∀ v ∈ Z, m * v * m⁻¹ ∈ Z := fun m hm v hv =>
    (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 hm) v).mp hv
  let f : ℕ → G := fun i => k ^ i * z * (k ^ i)⁻¹
  have hfmem : ∀ i, f i ∈ Z := fun i => hconjZ _ (pow_mem hkM i) z hz
  have hfne : ∀ i, f i ≠ 1 := by
    intro i h
    apply hz1
    have : z = (k ^ i)⁻¹ * f i * k ^ i := by simp only [f]; group
    rw [this, h]; group
  have hinj : ∀ i j, i < j → j < q - 1 → f i ≠ f j := by
    intro i j hij hjq hfe
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    have hd0 : 0 < d := by omega
    have hdq : d < q - 1 := by omega
    have h1 : k ^ d * z = z * k ^ d := by
      have h2 : k ^ i * z * (k ^ i)⁻¹ = k ^ i * (k ^ d * z * (k ^ d)⁻¹) * (k ^ i)⁻¹ := by
        have := hfe
        simp only [f, pow_add, mul_inv_rev] at this
        calc k ^ i * z * (k ^ i)⁻¹ = k ^ i * k ^ d * z * ((k ^ d)⁻¹ * (k ^ i)⁻¹) := this
          _ = _ := by group
      have h3 : z = k ^ d * z * (k ^ d)⁻¹ := by
        have := mul_left_cancel (mul_right_cancel (b := (k ^ i)⁻¹) h2)
        simpa [mul_assoc] using this
      calc k ^ d * z = (k ^ d * z * (k ^ d)⁻¹) * k ^ d := by group
        _ = z * k ^ d := by rw [← h3]
    exact hz1 (hkreg d hd0 (by omega) z hz h1)
  let S : Finset G := Finset.univ.filter (fun x => x ∈ Z ∧ x ≠ 1)
  have hSc : S.card = q - 1 := by
    have h1 : (Finset.univ.filter (fun x => x ∈ Z)).card = q := by
      rw [hq, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h2 : S = (Finset.univ.filter (fun x => x ∈ Z)).erase 1 := by
      ext x
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      tauto
    rw [h2, Finset.card_erase_of_mem (by simp [Z.one_mem]), h1]
  let T : Finset G := (Finset.range (q - 1)).image f
  have hTc : T.card = q - 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hinj i j h hj hij
    · exact hinj j i h hi hij.symm
  have hTS : T ⊆ S := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hfmem i, hfne i⟩
  have hTS' : T = S := Finset.eq_of_subset_of_card_le hTS (by rw [hSc, hTc])
  have hz'S : z' ∈ S := by simp [S, hz', hz1']
  rw [← hTS'] at hz'S
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hz'S
  exact ⟨i, hi⟩

theorem Z_conj_mem_normalClosure (H : StrothHyp M Q Z) {z z' : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (hz' : z' ∈ Z) (hz1' : z' ≠ 1) :
    ∃ x ∈ Subgroup.normalClosure ({z} : Set G), x * z * x⁻¹ = z' := by
  classical
  obtain ⟨B, hc⟩ := exists_ctx_of_strothHyp H
  obtain ⟨k, hkMQ, hko, hkreg⟩ := hc.cartan
  have hkM' : k ∈ M := (Subgroup.mem_inf.mp hkMQ).1
  have hkX : k ∈ Subgroup.normalClosure ({z} : Set G) := by
    have hQX : Q ≤ Subgroup.normalClosure ({z} : Set G) := Q_le_normalClosure H hz hz1
    have hBX : QB B ≤ Subgroup.normalClosure ({z} : Set G) := by
      obtain ⟨g, hg⟩ := hc.conj
      rw [(Ctx.QB_eq hc hg).2]
      intro y hy
      have hy' : g⁻¹ * y * g ∈ Q := mem_conjSubgroup.mp hy
      have := Subgroup.normalClosure_normal.conj_mem _ (hQX hy') g
      simpa [mul_assoc] using this
    exact (sup_le hQX hBX) (Subgroup.mem_inf.mp hkMQ).2
  obtain ⟨i, hi⟩ := exists_pow_conj_of_cartan H hkM' hkreg hz hz1 hz' hz1'
  exact ⟨k ^ i, pow_mem hkX i, hi⟩

theorem isConj_normalClosure (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) (w : G)
    (hw : IsConj z w) : ∃ x ∈ Subgroup.normalClosure ({z} : Set G), w = x * z * x⁻¹ := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hw
  obtain ⟨x, hx, m, hm, rfl⟩ := exists_mul_of_normalClosure H hz hz1 g
  have hmz : m * z * m⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 hm) z).mp hz
  have hmz1 : m * z * m⁻¹ ≠ 1 := by
    intro h
    apply hz1
    have : z = m⁻¹ * (m * z * m⁻¹) * m := by group
    rw [this, h]; group
  obtain ⟨x', hx', hxz⟩ := Z_conj_mem_normalClosure H hz hz1 hmz hmz1
  refine ⟨x * x', Subgroup.mul_mem _ hx hx', ?_⟩
  calc x * m * z * (x * m)⁻¹ = x * (m * z * m⁻¹) * x⁻¹ := by group
    _ = x * (x' * z * x'⁻¹) * x⁻¹ := by rw [hxz]
    _ = x * x' * z * (x * x')⁻¹ := by group

end Frattini

section Outcome

theorem timmesfeldOutcome_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Timmesfeld.Outcome X) : Timmesfeld.Outcome Y := by
  unfold Timmesfeld.Outcome at h ⊢
  rcases h with ⟨n, f, h1, h2, hL⟩ | ⟨n, f, h1, h2, hL⟩ | ⟨n, f, h1, h2, hL | hL⟩ |
      ⟨f, h1, hL⟩ | ⟨f, h1, t, ht, hL⟩ | hL | hL | hL
  · exact Or.inl ⟨n, f, h1, h2, CFSG.Blueprint.LieModel.of_mulEquiv e hL⟩
  · exact Or.inr (Or.inl ⟨n, f, h1, h2, CFSG.Blueprint.LieModel.of_mulEquiv e hL⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, f, h1, h2,
      Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hL)⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨n, f, h1, h2,
      Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e hL)⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h1, CFSG.Blueprint.LieModel.of_mulEquiv e hL⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨f, h1, t, ht, CFSG.Blueprint.LieModel.of_mulEquiv e hL⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (CFSG.Blueprint.LieModel.of_mulEquiv e hL))))))
  · obtain ⟨hL'⟩ := hL
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans hL'⟩))))))
  · obtain ⟨hL'⟩ := hL
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans hL'⟩))))))

variable [Finite G] {M Q Z : Subgroup G}

theorem outcome_of_conjClassSet (hT : TimmesfeldOutcomeStatement) (H : StrothHyp M Q Z) {z : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) (hroot : Timmesfeld.IsRootInvolutionSet (conjClassSet z)) :
    Timmesfeld.Outcome (FStar G) := by
  have hodd : pPrimeCore 2 G = ⊥ := H.toTim81Hyp.pPrimeCore_eq_bot H.q4
  have hnd : ∃ d e : G, IsConj z d ∧ IsConj z e ∧ orderOf (d * e) = 4 := by
    obtain ⟨d, hd, e, he, h4⟩ := exists_orderOf_mul_eq_four H hz hz1
    exact ⟨d, e, hd, he, h4⟩
  have h := outcome_normalClosure hT (z := z) hroot (isConj_normalClosure H hz hz1) hodd H.o2 hnd
  exact timmesfeldOutcome_of_mulEquiv
    (MulEquiv.subgroupCongr (generalizedFitting_eq_normalClosure H hz hz1).1).symm h

end Outcome

end CFSG.RankThree.GF2n.Smith81

module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailRecogGroup
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailRecogRadical
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCorBList
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailFStarSimple
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailFlagArith

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem isPerfect_of_simple_nonabelian {A : Type*} [Group A] [IsSimpleGroup A]
    (h : ∃ a b : A, a * b ≠ b * a) : Group.IsPerfect A := by
  refine ⟨?_⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top (commutator A) with h0 | h0
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    apply hab
    have : ⁅a, b⁆ ∈ commutator A := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
      (Subgroup.mem_top b)
    rw [h0, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  · exact h0

theorem natCard_center_eq_of_center {Y : Type*} [Group Y] {N V : Subgroup Y} (hVN : V ≤ N)
    (hZN : ∀ x ∈ N, (∀ n ∈ N, x * n = n * x) → x ∈ V)
    (hVc : ∀ v ∈ V, ∀ n ∈ N, v * n = n * v) :
    Nat.card ↥(Subgroup.center ↥N) = Nat.card V := by
  have h : Subgroup.center ↥N = V.subgroupOf N := by
    ext x
    rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact hZN _ x.2 (fun n hn => by
        have := hx ⟨n, hn⟩
        exact congrArg Subtype.val this.symm)
    · intro hx z
      exact Subtype.ext (hVc _ hx _ z.2).symm
  rw [h]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv

theorem recog_abstract
    (hCorB' : CorollaryBStmt) (hOut : OutSolvableListStatement)
    (hRank : TwoRankSporadicAltStatement) (hBorel : BorelRankOneSolvableStatement)
    (hArtin : ArtinLinearOrdersStatement) (hRad : RadicalTwoSubgroupLinearStatement)
    {Y : Type} [Group Y] [Finite Y] (q : ℕ) (hq4 : 4 ≤ q) (hq2 : ∃ g : ℕ, q = 2 ^ g)
    (V L N R K : Subgroup Y)
    (hO2 : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥)
    (hO : ∀ P : Subgroup Y, P.Normal → Odd (Nat.card P) → P = ⊥)
    (hC : ∀ X : Subgroup Y, X.Normal → V ≤ X → ∀ c : Y, (∀ x ∈ X, c * x = x * c) → c = 1)
    (hKV : ∀ g ∈ normalizer (V : Set Y), g ∈ K)
    (hVL : V ≤ L) (hLN : L ≤ N) (hNR : N ≤ R) (hRK : R ≤ K) (hN2 : IsPGroup 2 N)
    (hpc : ∀ P : Subgroup Y, P ≤ K → (∀ k ∈ K, k ∈ normalizer (P : Set Y)) → IsPGroup 2 P →
      P ≤ N)
    (hNn : ∀ k ∈ K, k ∈ normalizer (N : Set Y)) (hRn : ∀ k ∈ K, k ∈ normalizer (R : Set Y))
    (hLn : ∀ k ∈ K, k ∈ normalizer (L : Set Y))
    (hZN : ∀ x ∈ N, (∀ n ∈ N, x * n = n * x) → x ∈ V)
    (hVc : ∀ v ∈ V, ∀ n ∈ N, v * n = n * v)
    (hVcard : Nat.card V = q) (hNcard : Nat.card N = q ^ 9) (hLcard : Nat.card L = q ^ 5)
    (hLab : IsElemAbelian 2 L) (hCorBL : CorBHyp L)
    (K₀ : Type) [Field K₀] [Finite K₀] (hK₀ : Nat.card K₀ = q)
    (hRN : ∃ _ : (N.subgroupOf R).Normal,
      Nonempty ((↥R ⧸ N.subgroupOf R) ≃* StatedProj (StatedSL 4 K₀)))
    (hy : ∃ y ∈ R, orderOf y = 3 ∧ ∀ x ∈ N, y * x = x * y → x ∈ V) :
    ∃ (K₁ : Type) (_ : Field K₁) (_ : Finite K₁), Nat.card K₁ = q ∧
      Nonempty (↥(generalizedFitting Y) ≃* StatedProj (StatedSL 6 K₁)) := by
  classical
  obtain ⟨hnormNR, ⟨eRN⟩⟩ := hRN
  have hVne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hVcard
    omega
  have hLne : L ≠ ⊥ := fun h => hVne (le_bot_iff.mp (h ▸ hVL))
  have hL2 : IsPGroup 2 ↥L := corB_isPGroup_of_isElemAbelian L hLab
  have hThm : ThmAConclusion L := hCorB' Y L hCorBL
  have hlist : ListGroup ↥(Subgroup.normalClosure (L : Set Y)) :=
    corB_listGroup hLne hL2 hThm hO2 hO
  set Gs : Subgroup Y := Subgroup.normalClosure (L : Set Y) with hGs
  haveI hGsn : Gs.Normal := inferInstance
  have hLGs : L ≤ Gs := Subgroup.le_normalClosure
  have hVGs : V ≤ Gs := hVL.trans hLGs
  have hCGs : ∀ c : Y, (∀ s ∈ Gs, c * s = s * c) → c = 1 := hC Gs hGsn hVGs
  obtain ⟨hsimp4, hnab4⟩ := statedProj_statedSL_four_simple_nonabelian K₀
  haveI : IsSimpleGroup (StatedProj (StatedSL 4 K₀)) := hsimp4
  have hperf4 : Group.IsPerfect (StatedProj (StatedSL 4 K₀)) :=
    isPerfect_of_simple_nonabelian hnab4
  have hperfRN : commutator (↥R ⧸ N.subgroupOf R) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := eRN.symm.toMonoidHom) eRN.symm.surjective
      (G := StatedProj (StatedSL 4 K₀))).commutator_eq_top
  obtain ⟨E, hER, hEperf, hEN, hEn⟩ := exists_perfect_sup_eq hNR hperfRN
  have hEGs : E ≤ Gs := perfect_le_of_out_solvable hCGs (hOut ↥Gs hlist) hEperf
  have hEne : E ≠ ⊥ := by
    intro h
    have hRN' : R ≤ N := by
      rw [← hEN, h, bot_sup_eq]
    haveI : Subsingleton (↥R ⧸ N.subgroupOf R) := by
      have : N.subgroupOf R = ⊤ := Subgroup.subgroupOf_eq_top.mpr hRN'
      rw [this]
      exact QuotientGroup.subsingleton_quotient_top
    obtain ⟨a, b, hab⟩ := hnab4
    exact hab (by
      have := Subsingleton.elim (eRN.symm a) (eRN.symm b)
      have h2 := eRN.symm.injective this
      rw [h2])
  obtain ⟨y, hyR, hy3, hyC⟩ := hy
  have hyGs : y ∈ Gs := mem_of_orderOf_three hEGs hN2 hy3 (by rw [hEN]; exact hyR)
  have hNGs : N ≤ Gs :=
    le_normal_of_coprime_element hN2 hy3 (hNn y (hRK hyR)) hyGs hyC hVGs
  have hRGs : R ≤ Gs := by rw [← hEN]; exact sup_le hEGs hNGs
  obtain ⟨r, K1, hKf, hKfin, hr3, hK2, ⟨e⟩⟩ := exists_psl_of_listGroup hBorel hRank hlist hEGs
    hEperf hEne (fun k hk => hLn k (hRK (hER hk))) hLGs hLab
    (by
      rw [hLcard]
      have h1 : 4 ^ 5 ≤ q ^ 5 := Nat.pow_le_pow_left hq4 5
      omega) hLne
  have hKN : normalizer (N : Set Y) = K := by
    refine le_antisymm (fun g hg => hKV g ?_) (fun k hk => ?_)
    · exact normalizer_le_normalizer_of_center (hVL.trans hLN) hZN hVc hg
    · exact hNn k hk
  have hNK : N ≤ K := hNR.trans hRK
  have hrad : inSubgroup (pCore 2) (normalizer ((N.subgroupOf Gs : Subgroup ↥Gs) : Set ↥Gs)) =
      N.subgroupOf Gs := by
    rw [← Subgroup.subgroupOf_normalizer_eq hNGs, hKN]
    have h1 : K.subgroupOf Gs = (K ⊓ Gs).subgroupOf Gs := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [h1, inSubgroup_pCore_subgroupOf inf_le_right,
      inSubgroup_pCore_inf_eq hNGs hNK hNn hN2 hpc]
  have hU1 : N.subgroupOf Gs ≠ ⊥ := by
    intro h
    have h1 : N = ⊥ := by
      have hd : Disjoint N Gs := Subgroup.subgroupOf_eq_bot.mp h
      exact hd.eq_bot_of_le hNGs
    exact hVne (le_bot_iff.mp (h1 ▸ (hVL.trans hLN)))
  have hU2 : IsPGroup 2 ↥(N.subgroupOf Gs) :=
    hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNGs).symm
  have hZ : Nat.card ↥(Subgroup.center ↥(N.subgroupOf Gs)) = q := by
    rw [← hVcard, ← natCard_center_eq_of_center (hVL.trans hLN) hZN hVc]
    exact Nat.card_congr (Subgroup.centerCongr (Subgroup.subgroupOfEquivOfLe hNGs)).toEquiv
  have hcard : Nat.card ↥(N.subgroupOf Gs) = q ^ 9 := by
    rw [← hNcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNGs).toEquiv
  have hUP : N.subgroupOf Gs ≤ R.subgroupOf Gs := fun x hx => hNR hx
  have hPn : R.subgroupOf Gs ≤ normalizer ((N.subgroupOf Gs : Subgroup ↥Gs) : Set ↥Gs) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hNGs, hKN]
    exact fun x hx => hRK hx
  have hPN : ∀ k ∈ normalizer ((N.subgroupOf Gs : Subgroup ↥Gs) : Set ↥Gs),
      k ∈ normalizer ((R.subgroupOf Gs : Subgroup ↥Gs) : Set ↥Gs) := by
    intro k hk
    rw [← Subgroup.subgroupOf_normalizer_eq hNGs, hKN] at hk
    have hkK : (k : Y) ∈ K := hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := (Subgroup.mem_normalizer_iff.mp (hRn _ hkK) (x : Y))
    exact this
  have hPU := nonempty_quot_equiv_subgroupOf hRGs hNR ⟨eRN⟩
  have hflag := flag_type_of_radical_equiv hRad hArtin r K1 hr3 hK2 e q hq4 K₀ hK₀ hq2
    (N.subgroupOf Gs) (R.subgroupOf Gs) hU1 hU2 hrad hZ hcard hUP hPn hPN hPU
  obtain ⟨hr6, hKq⟩ := hflag
  subst hr6
  haveI : IsSimpleGroup (StatedProj (StatedSL 6 K1)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K1 (d := 6) (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
  haveI hsimpGs : IsSimpleGroup ↥Gs := e.isSimpleGroup
  have hnabGs : ∃ a ∈ Gs, ∃ b ∈ Gs, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab4
    obtain ⟨x0, hx0⟩ := QuotientGroup.mk_surjective (eRN.symm a)
    obtain ⟨y0, hy0⟩ := QuotientGroup.mk_surjective (eRN.symm b)
    refine ⟨x0, hRGs x0.2, y0, hRGs y0.2, fun h => hab ?_⟩
    have h2 : x0 * y0 = y0 * x0 := Subtype.ext h
    have h3 : eRN.symm a * eRN.symm b = eRN.symm b * eRN.symm a := by
      rw [← hx0, ← hy0, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h2]
    have h4 := congrArg eRN h3
    simpa using h4
  have hFG : generalizedFitting Y = Gs := fstar_eq_of_simple hsimpGs hnabGs hCGs hO2 hO
  exact ⟨K1, hKf, hKfin, hKq, ⟨(MulEquiv.subgroupCongr hFG).trans e⟩⟩

end CFSG.RankThree.GF2n.Stroth80


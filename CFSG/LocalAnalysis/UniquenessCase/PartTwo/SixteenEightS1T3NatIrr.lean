module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Def
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.HSL
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.Background.C41PfT
public import CFSG.RankThree.GF2n.Stroth80.Sec83NatSection
public import CFSG.RankThree.GF2n.Stroth80.Sec78NatIrredOmega
public import CFSG.RankThree.GF2n.Stroth80.Sec78NatIrredOmegaTwo
public import CFSG.HardMathSupport.Cooperstein.Proving.EvenWeightCard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique
open scoped Matrix

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}

private theorem s16t3_isIrrOn_of_action {M : Type} [Group M] {G : Type} [Group G]
    {π : G →* ↥L} (hπs : Function.Surjective π) (act : G → M → M)
    {β : ↥U →* M} (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥U, β u = 1 ↔ (u : W) ∈ Z)
    (hβe : ∀ (γ : G) (u : ↥U) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ U),
      β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ = act γ (β u))
    (hZU : Z ≤ U) (hUinv : ∀ h : ↥L, ∀ u ∈ U, (h : MulAut W) u ∈ U)
    (hZinv : ∀ h : ↥L, ∀ z ∈ Z, (h : MulAut W) z ∈ Z)
    (hirr : ∀ A : Subgroup M, (∀ γ : G, ∀ x ∈ A, act γ x ∈ A) → A = ⊥ ∨ A = ⊤)
    (hne : ∃ m : M, m ≠ 1) : IsIrrOn L U Z := by
  have hlt : Z < U := by
    refine lt_of_le_of_ne hZU (Ne.symm fun hZUeq => ?_)
    obtain ⟨m, hm⟩ := hne
    obtain ⟨u, hu⟩ := hβs m
    have hmem : (u : W) ∈ Z := by rw [← hZUeq]; exact u.2
    have h1 : β u = 1 := (hβk u).2 hmem
    rw [hu] at h1
    exact hm h1
  refine ⟨hlt, ?_, ?_, ?_⟩
  · intro h hh u hu
    exact hUinv ⟨h, hh⟩ u hu
  · intro h hh u hu
    exact hZinv ⟨h, hh⟩ u hu
  · intro J hJ hZJ hJU
    set A : Subgroup M := (J.subgroupOf U).map β with hA
    have hAinv : ∀ γ : G, ∀ x ∈ A, act γ x ∈ A := by
      intro γ x hx
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hx
      have hju : (j : W) ∈ U := j.2
      have hlu : ((π γ : ↥L) : MulAut W) (j : W) ∈ U := hUinv (π γ) j hju
      have hJmem : ((π γ : ↥L) : MulAut W) (j : W) ∈ J :=
        hJ (π γ) (π γ).2 (j : W) (Subgroup.mem_subgroupOf.1 hj)
      refine Subgroup.mem_map.2 ⟨⟨((π γ : ↥L) : MulAut W) (j : W), hlu⟩,
        Subgroup.mem_subgroupOf.2 hJmem, ?_⟩
      exact hβe γ j hlu
    rcases hirr A hAinv with hA0 | hAtop
    · left
      refine le_antisymm ?_ hZJ
      intro x hx
      have hxU : x ∈ U := hJU hx
      have hmem : β ⟨x, hxU⟩ ∈ A :=
        Subgroup.mem_map.2 ⟨⟨x, hxU⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
      rw [hA0, Subgroup.mem_bot] at hmem
      exact (hβk _).1 hmem
    · right
      refine le_antisymm hJU fun x hx => ?_
      have hxU : x ∈ U := hx
      have hmem : β ⟨x, hxU⟩ ∈ A := by rw [hAtop]; exact Subgroup.mem_top _
      obtain ⟨j, hj, hjb⟩ := Subgroup.mem_map.1 hmem
      have hxj : (j : W) ∈ J := Subgroup.mem_subgroupOf.1 hj
      have hβeq : β (⟨x, hxU⟩ * j⁻¹) = 1 := by
        rw [map_mul, map_inv, hjb, mul_inv_cancel]
      have hZmem : x * (j : W)⁻¹ ∈ Z := (hβk _).1 hβeq
      have hJmem : x * (j : W)⁻¹ ∈ J := hZJ hZmem
      have hprod : (x * (j : W)⁻¹) * (j : W) ∈ J := J.mul_mem hJmem hxj
      have heq : (x * (j : W)⁻¹) * (j : W) = x := by group
      rwa [heq] at hprod


private theorem s16t3_isIrrOn_of_natReal {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {X : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} {π : ↥X →* ↥H}
    (R : CFSG.Quasithin.SzN15.NatReal H U Z X π) (hZU : Z ≤ U)
    (hirr : ∀ A : Subgroup (Multiplicative (ι → K)),
      (∀ g : ↥X, ∀ x ∈ A, natAct X g x ∈ A) → A = ⊥ ∨ A = ⊤)
    (hne : ∃ m : Multiplicative (ι → K), m ≠ 1) : IsIrrOn H U Z := by
  obtain ⟨β, hβs, hβk, hβe⟩ := R.exists_β
  exact s16t3_isIrrOn_of_action (β := β) R.surj (natAct X) hβs hβk hβe hZU R.U_inv R.Z_inv
    hirr hne

private theorem s16t3_eq_one_of_trivial_of_model {D : FFModel} (hf : D.Faithful)
    {π : D.Gam →* ↥L} (hR : D.RealizesVia L U Z π) {l : MulAut W} (hl : l ∈ L)
    (htriv : ∀ u ∈ U, l u * u⁻¹ ∈ Z) : l = 1 := by
  obtain ⟨hπs, hZU, hkersec, hUinv, hZinv, hsec, hkerinv, β, hβs, hβk, hβe⟩ := hR
  obtain ⟨γ, hγ⟩ := hπs ⟨l, hl⟩
  have hγl : ((π γ : ↥L) : MulAut W) = l := congrArg Subtype.val hγ
  have hact : ∀ m ∈ D.sec, D.act γ m * m⁻¹ ∈ D.ker := by
    intro m hm
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
    have hu' : ((π γ : ↥L) : MulAut W) (u : W) ∈ U := hUinv (π γ) u u.2
    have h1 := hβe γ u ⟨m, hm⟩ hu' (hsec γ m hm) hu
    have hmem : ((π γ : ↥L) : MulAut W) (u : W) * (u : W)⁻¹ ∈ Z := by
      rw [hγl]; exact htriv (u : W) u.2
    have h3 : β (⟨((π γ : ↥L) : MulAut W) (u : W) * (u : W)⁻¹,
        U.mul_mem hu' (U.inv_mem u.2)⟩ : ↥U) = 1 := (hβk _).2 hmem
    have h4 : β ⟨((π γ : ↥L) : MulAut W) (u : W), hu'⟩ * (β u)⁻¹ = 1 := by
      rw [← map_inv, ← map_mul]
      exact h3
    have h2 : β ⟨((π γ : ↥L) : MulAut W) (u : W), hu'⟩ = β u :=
      mul_inv_eq_one.1 h4
    have h5 : (QuotientGroup.mk (⟨D.act γ m, hsec γ m hm⟩ : ↥D.sec)
        : ↥D.sec ⧸ D.ker.subgroupOf D.sec) =
        QuotientGroup.mk (⟨m, hm⟩ : ↥D.sec) := by
      rw [← h1, h2, hu]
    have h6 : (⟨D.act γ m, hsec γ m hm⟩ : ↥D.sec)⁻¹ * ⟨m, hm⟩ ∈
        D.ker.subgroupOf D.sec := QuotientGroup.eq.mp h5
    have h6' : (⟨m, hm⟩ : ↥D.sec)⁻¹ * ⟨D.act γ m, hsec γ m hm⟩ ∈
        D.ker.subgroupOf D.sec := by
      have hinv := (D.ker.subgroupOf D.sec).inv_mem h6
      simpa [mul_inv_rev] using hinv
    have h7 : m⁻¹ * D.act γ m ∈ D.ker := Subgroup.mem_subgroupOf.1 h6'
    rw [mul_comm]
    exact h7
  have hγ1 : γ = 1 := hf γ hact
  calc l = ((π γ : ↥L) : MulAut W) := hγl.symm
    _ = ((π (1 : D.Gam) : ↥L) : MulAut W) := by rw [hγ1]
    _ = 1 := by simp

private theorem s16t3_card_of_quotient {M : Type} [Group M] {β : ↥U →* M}
    (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥U, β u = 1 ↔ (u : W) ∈ Z)
    (hZU : Z ≤ U) (hM : 8 ≤ Nat.card M) : 8 * Nat.card Z ≤ Nat.card U := by
  have hker : β.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, hβk u, Subgroup.mem_subgroupOf]
  have hcardZ : Nat.card ↥(Z.subgroupOf U) = Nat.card ↥Z :=
    Nat.card_congr
      { toFun := fun z => (⟨(z : W), Subgroup.mem_subgroupOf.1 z.2⟩ : ↥Z)
        invFun := fun z =>
          (⟨⟨z, hZU z.2⟩, Subgroup.mem_subgroupOf.2 z.2⟩ : ↥(Z.subgroupOf U))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hquot : Nat.card (↥U ⧸ Z.subgroupOf U) = Nat.card M := by
    rw [← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv
  have hcardU : Nat.card ↥U =
      Nat.card (↥U ⧸ Z.subgroupOf U) * Nat.card ↥(Z.subgroupOf U) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf U)
  calc 8 * Nat.card ↥Z ≤ Nat.card M * Nat.card ↥Z := Nat.mul_le_mul_right _ hM
    _ = Nat.card (↥U ⧸ Z.subgroupOf U) * Nat.card ↥(Z.subgroupOf U) := by
          rw [hquot, hcardZ]
    _ = Nat.card ↥U := hcardU.symm

private theorem s16t3_natIrr_of_natIrred {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] {X : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (hirr : CFSG.RankThree.GF2n.Stroth80.NatIrred X)
    (hcomm : CFSG.RankThree.GF2n.Stroth80.AddCommutantScalar X) :
    ∀ A : Subgroup (Multiplicative (ι → K)),
      (∀ g : ↥X, ∀ x ∈ A, natAct X g x ∈ A) → A = ⊥ ∨ A = ⊤ := by
  intro A hA
  set A' : AddSubgroup (ι → K) := Subgroup.toAddSubgroup' A with hA'
  by_cases h0 : A' = ⊥
  · left
    refine le_bot_iff.1 fun x hx => ?_
    have hx' : Multiplicative.toAdd x ∈ A' := (Subgroup.mem_toAddSubgroup' A _).2 hx
    rw [h0, AddSubgroup.mem_bot] at hx'
    exact Multiplicative.toAdd.injective (by simpa using hx')
  · right
    have hinv : ∀ g ∈ X, ∀ v ∈ A', (g : Matrix ι ι K) *ᵥ v ∈ A' := by
      intro g hg v hv
      have hvA : Multiplicative.ofAdd v ∈ A := (Subgroup.mem_toAddSubgroup' A v).1 hv
      have h := hA ⟨g, hg⟩ (Multiplicative.ofAdd v) hvA
      exact (Subgroup.mem_toAddSubgroup' A _).2 (by simpa [natAct] using h)
    have htop := CFSG.RankThree.GF2n.Stroth80.eq_top_of_addInvariant hirr hcomm h0 hinv
    refine le_antisymm le_top fun x _ => ?_
    have hx' : Multiplicative.toAdd x ∈ A' := by rw [htop]; exact AddSubgroup.mem_top _
    exact (Subgroup.mem_toAddSubgroup' A _).1 hx'

private theorem s16t3_natIrr_statedSL {m : ℕ} {K : Type} [Field K] (hm : 2 ≤ m) :
    ∀ A : Subgroup (Multiplicative (Fin m → K)),
      (∀ g : ↥(StatedSL m K), ∀ x ∈ A, natAct (StatedSL m K) g x ∈ A) →
      A = ⊥ ∨ A = ⊤ := by
  intro A hA
  set A' : AddSubgroup (Fin m → K) := Subgroup.toAddSubgroup' A with hA'
  have hinv : ∀ i j : Fin m, i ≠ j → ∀ c : K, ∀ v ∈ A',
      Matrix.transvection i j c *ᵥ v ∈ A' := by
    intro i j hij c v hv
    have hvA : Multiplicative.ofAdd v ∈ A := (Subgroup.mem_toAddSubgroup' A v).1 hv
    let g : ↥(StatedSL m K) :=
      ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
        (by rw [Matrix.det_transvection_of_ne i j hij c]; exact one_ne_zero),
       Subgroup.subset_closure (by
        change (Matrix.transvection i j c).det = 1
        exact Matrix.det_transvection_of_ne i j hij c)⟩
    have h := hA g (Multiplicative.ofAdd v) hvA
    have heq : natAct (StatedSL m K) g (Multiplicative.ofAdd v) =
        Multiplicative.ofAdd (Matrix.transvection i j c *ᵥ v) := rfl
    exact (Subgroup.mem_toAddSubgroup' A _).2 (heq ▸ h)
  rcases CFSG.Quasithin.H.eq_bot_or_eq_top_of_transvection_inv hm A' hinv with h | h
  · left
    refine le_bot_iff.1 fun x hx => ?_
    have hx' : Multiplicative.toAdd x ∈ A' := (Subgroup.mem_toAddSubgroup' A _).2 hx
    rw [h, AddSubgroup.mem_bot] at hx'
    exact Multiplicative.toAdd.injective (by simpa using hx')
  · right
    refine le_antisymm le_top fun x _ => ?_
    have hx' : Multiplicative.toAdd x ∈ A' := by rw [h]; exact AddSubgroup.mem_top _
    exact (Subgroup.mem_toAddSubgroup' A _).1 hx'

private theorem s16t3_natIrr_statedSp {m : ℕ} {K : Type} [Field K] [Finite K] :
    ∀ A : Subgroup (Multiplicative (Fin m ⊕ Fin m → K)),
      (∀ g : ↥(StatedSp m K), ∀ x ∈ A, natAct (StatedSp m K) g x ∈ A) →
      A = ⊥ ∨ A = ⊤ :=
  s16t3_natIrr_of_natIrred (K := K)
    CFSG.RankThree.GF2n.Stroth80.natIrred_statedSp
    CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedSp

private theorem s16t3_natIrr_statedOmegaPlus {m : ℕ} {K : Type} [Field K] [Finite K]
    (hm : 3 ≤ m) :
    ∀ A : Subgroup (Multiplicative (Fin m ⊕ Fin m → K)),
      (∀ g : ↥(StatedOmega (StatedQuadPlus m K)), ∀ x ∈ A,
        natAct (StatedOmega (StatedQuadPlus m K)) g x ∈ A) → A = ⊥ ∨ A = ⊤ :=
  s16t3_natIrr_of_natIrred (K := K)
    (CFSG.RankThree.GF2n.Stroth80.natIrred_statedOmegaPlus hm)
    (CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedOmegaPlus hm)

private theorem s16t3_natIrr_statedOmegaMinus {m : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hm : 2 ≤ m) (hpoly : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ A : Subgroup (Multiplicative (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)),
      (∀ g : ↥(StatedOmega (StatedQuadMinus m K b c)), ∀ x ∈ A,
        natAct (StatedOmega (StatedQuadMinus m K b c)) g x ∈ A) → A = ⊥ ∨ A = ⊤ := by
  by_cases hm3 : 3 ≤ m
  · exact s16t3_natIrr_of_natIrred (K := K)
      (CFSG.RankThree.GF2n.Stroth80.natIrred_statedOmegaMinus_of_three_le hm3 hpoly)
      (CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedOmegaMinus hm hpoly)
  · have hm2 : m = 2 := by omega
    subst hm2
    exact s16t3_natIrr_of_natIrred (K := K)
      (CFSG.RankThree.GF2n.Stroth80.natIrred_statedOmegaMinus_two hpoly)
      (CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedOmegaMinus hm hpoly)

private theorem s16t3_card_natReal {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {X : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {H : Subgroup (MulAut W)} {π : ↥X →* ↥H}
    (R : CFSG.Quasithin.SzN15.NatReal H U Z X π) (hZU : Z ≤ U)
    (hK : Nat.card K = 2) (hι : 3 ≤ Fintype.card ι) : 8 * Nat.card Z ≤ Nat.card U := by
  obtain ⟨β, hβs, hβk, -⟩ := R.exists_β
  refine s16t3_card_of_quotient hβs hβk hZU ?_
  have hcard : Nat.card (Multiplicative (ι → K)) = 2 ^ Fintype.card ι := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hK, Nat.card_eq_fintype_card]
  rw [hcard]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ Fintype.card ι := Nat.pow_le_pow_right (by norm_num) hι

private theorem s16t3_altHeart_irr {n : ℕ} (hn : 4 ≤ n) :
    ∀ A : Subgroup (Multiplicative (AltHeart n)),
      (∀ γ : ↥(alternatingGroup (Fin n)), ∀ x ∈ A,
        Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
          (Multiplicative.toAdd x)) ∈ A) →
      A = ⊥ ∨ A = ⊤ := by
  intro A hA
  set Y : AddSubgroup (AltHeart n) := Subgroup.toAddSubgroup' A with hY
  have hYinv : ∀ σ ∈ alternatingGroup (Fin n), ∀ y ∈ Y,
      CFSG.Quasithin.C41Pf.AltN.hAct n σ y ∈ Y := by
    intro σ hσ y hy
    have hyA : Multiplicative.ofAdd y ∈ A := (Subgroup.mem_toAddSubgroup' A y).1 hy
    have h := hA ⟨σ, hσ⟩ (Multiplicative.ofAdd y) hyA
    exact (Subgroup.mem_toAddSubgroup' A _).2 (by simpa using h)
  rcases CFSG.Quasithin.C41Pf.AltN.heart_irreducible hn Y hYinv with h | h
  · left
    refine le_bot_iff.1 fun x hx => ?_
    have hx' : Multiplicative.toAdd x ∈ Y := (Subgroup.mem_toAddSubgroup' A _).2 hx
    rw [h, AddSubgroup.mem_bot] at hx'
    exact Multiplicative.toAdd.injective (by simpa using hx')
  · right
    refine le_antisymm le_top fun x _ => ?_
    have hx' : Multiplicative.toAdd x ∈ Y := by rw [h]; exact AddSubgroup.mem_top _
    exact (Subgroup.mem_toAddSubgroup' A _).1 hx'

private theorem s16t3_alt_exists_beta {n : ℕ} (hn0 : 0 < n) {H : Subgroup (MulAut W)}
    {π : ↥(alternatingGroup (Fin n)) →* ↥H}
    (hR : (FFModel.altDn n).RealizesVia H U Z π) :
    ∃ β' : ↥U →* Multiplicative (AltHeart n),
      Function.Surjective β' ∧
      (∀ u : ↥U, β' u = 1 ↔ (u : W) ∈ Z) ∧
      ∀ (γ : ↥(alternatingGroup (Fin n))) (u : ↥U)
        (hu : ((π γ : ↥H) : MulAut W) (u : W) ∈ U),
        β' ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ =
          Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
            (Multiplicative.toAdd (β' u))) := by
  obtain ⟨-, -, -, -, -, hsecinv, -, β, hβs, hβk, hβe⟩ := hR
  let e : (↥(FFModel.altDn n).sec ⧸
      (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec) ≃* Multiplicative (AltHeart n) :=
    CFSG.Quasithin.C124.altQuotEquiv n hn0
  refine ⟨e.toMonoidHom.comp β, e.surjective.comp hβs, ?_, ?_⟩
  · intro u
    rw [MonoidHom.comp_apply]
    change e (β u) = 1 ↔ (u : W) ∈ Z
    rw [e.map_eq_one_iff, hβk u]
  · intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hmu : β u = QuotientGroup.mk m := hm.symm
    have hsec : (FFModel.altDn n).act γ (m : (FFModel.altDn n).Amb) ∈
        (FFModel.altDn n).sec := hsecinv γ m m.2
    have h1 := hβe γ u m hu hsec hmu
    calc e (β ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩) =
        e (QuotientGroup.mk ⟨(FFModel.altDn n).act γ (m : (FFModel.altDn n).Amb), hsec⟩) :=
          congrArg e h1
      _ = Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n
            (γ : Equiv.Perm (Fin n))
            (Multiplicative.toAdd (e (QuotientGroup.mk m)))) := rfl
      _ = Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n
            (γ : Equiv.Perm (Fin n)) (Multiplicative.toAdd (e (β u)))) := by
          rw [← hmu]

private theorem s16t3_isIrrOn_altDn {n : ℕ} (hn : 4 ≤ n) {H : Subgroup (MulAut W)}
    {π : ↥(alternatingGroup (Fin n)) →* ↥H}
    (hR : (FFModel.altDn n).RealizesVia H U Z π) : IsIrrOn H U Z := by
  have hn0 : 0 < n := by omega
  obtain ⟨β', hβs, hβk, hβe⟩ := s16t3_alt_exists_beta hn0 hR
  obtain ⟨hπs, hZU, -, hUinv, hZinv, -⟩ := hR
  let π' : ↥(alternatingGroup (Fin n)) →* ↥H := π
  have hπs' : Function.Surjective π' := hπs
  have hβe' : ∀ (γ : ↥(alternatingGroup (Fin n))) (u : ↥U)
      (hu : ((π' γ : ↥H) : MulAut W) (u : W) ∈ U),
      β' ⟨((π' γ : ↥H) : MulAut W) (u : W), hu⟩ =
        Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n
          (γ : Equiv.Perm (Fin n)) (Multiplicative.toAdd (β' u))) := by
    intro γ u hu
    simpa [π'] using hβe γ u hu
  refine s16t3_isIrrOn_of_action (β := β') hπs'
    (fun γ x => Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n
      (γ : Equiv.Perm (Fin n)) (Multiplicative.toAdd x)))
    hβs hβk hβe' hZU hUinv hZinv (s16t3_altHeart_irr hn) ?_
  refine ⟨Multiplicative.ofAdd (QuotientAddGroup.mk
    (CFSG.Quasithin.C41Pf.AltN.pairVec (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n))),
    ?_⟩
  intro h
  have h' : (QuotientAddGroup.mk (CFSG.Quasithin.C41Pf.AltN.pairVec
      (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)) : AltHeart n) = 0 := by
    have := congrArg Multiplicative.toAdd h
    simpa using this
  exact CFSG.Quasithin.C41Pf.AltN.mk_pairVec_ne_zero (by omega) (by simp) h'

private theorem s16t3_card_altHeart {n : ℕ} (hn : 5 ≤ n) :
    8 ≤ Nat.card (Multiplicative (AltHeart n)) := by
  have hn1 : 1 ≤ n := by omega
  let i0 : Fin n := ⟨0, by omega⟩
  have hquot : Nat.card (AltHeart n) * Nat.card ↥(constWeight n) =
      Nat.card ↥(evenWeight n) :=
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (constWeight n)).symm
  have heven : Nat.card ↥(evenWeight n) = 2 ^ (n - 1) :=
    CFSG.HardMathSupport.Cooperstein.Proving.card_evenWeight n hn1
  have hcle : Nat.card ↥(constWeight n) ≤ 2 := by
    let f : ↥(constWeight n) → ZMod 2 := fun x => (x : Fin n → ZMod 2) i0
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      funext i
      calc (x : Fin n → ZMod 2) i = (x : Fin n → ZMod 2) i0 := x.2 i i0
        _ = (y : Fin n → ZMod 2) i0 := hxy
        _ = (y : Fin n → ZMod 2) i := (y.2 i i0).symm
    have hle := Nat.card_le_card_of_injective f hf
    simpa [Nat.card_zmod] using hle
  have hcpos : 0 < Nat.card ↥(constWeight n) := Nat.card_pos
  have hmain : 8 * Nat.card ↥(constWeight n) ≤
      Nat.card (AltHeart n) * Nat.card ↥(constWeight n) := by
    calc 8 * Nat.card ↥(constWeight n) ≤ 16 := by omega
      _ = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = Nat.card (AltHeart n) * Nat.card ↥(constWeight n) := by rw [hquot, heven]
  have h8 : 8 ≤ Nat.card (AltHeart n) := Nat.le_of_mul_le_mul_right hmain hcpos
  have hcard : Nat.card (Multiplicative (AltHeart n)) = Nat.card (AltHeart n) :=
    Nat.card_congr Multiplicative.toAdd
  rwa [hcard]

private theorem s16t3_summand_one {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} (h : SumOfNat N L U Z 1) :
    ∃ I : Subgroup W, Z ≤ I ∧ I = U ∧ N L I Z := by
  obtain ⟨I, hZI, -, hsup, hN⟩ := h
  refine ⟨I 0, hZI 0, ?_, hN 0⟩
  have hsup' : Z ⊔ I 0 = U := by
    rw [← hsup]
    congr 1
    simpa using (iSup_unique I).symm
  exact (sup_eq_right.mpr (hZI 0)).symm.trans hsup'

private theorem s16t3_quasisimple_ne_bot {L : Subgroup (MulAut W)}
    (hq : CFSG.Open.IsQuasisimple ↥L) : L ≠ ⊥ := by
  intro hbot
  haveI : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hq.2.toNontrivial
  haveI : Subsingleton ↥L := by rw [hbot]; infer_instance
  haveI : Subsingleton (↥L ⧸ Subgroup.center ↥L) := inferInstance
  exact (not_subsingleton _) ‹Subsingleton _›

theorem SumOfNatShape.isIrrOn (hq : CFSG.Open.IsQuasisimple ↥L) (h : SumOfNatShape L U Z 1) :
    IsIrrOn L U Z := by
  rcases h with ⟨n, hSL | hSp | hOp | hOm | hAlt⟩
  · obtain ⟨hIs, hsum⟩ := hSL
    obtain ⟨I, hZI, hIU, hN⟩ := s16t3_summand_one hsum
    subst U
    obtain ⟨K, hKfield, hKfin, hKcard, hReal⟩ := hN
    letI := hKfield
    letI := hKfin
    have hKcard2 : Nat.card K = 2 := by simpa using hKcard
    obtain ⟨π, hπ⟩ := hReal
    have hn3 := s16k_three_le_of_isSLn hq hIs
    let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
    refine s16t3_isIrrOn_of_natReal R hZI (s16t3_natIrr_statedSL (by omega)) ?_
    refine ⟨Multiplicative.ofAdd (Pi.single (⟨0, by omega⟩ : Fin n) (1 : K)), ?_⟩
    intro hcontra
    have h0 := congrFun (Multiplicative.toAdd.injective hcontra) (⟨0, by omega⟩ : Fin n)
    have h0' : (1 : K) = 0 := by simpa using h0
    exact one_ne_zero h0' 
  · obtain ⟨hIs, hsum⟩ := hSp
    obtain ⟨I, hZI, hIU, hN⟩ := s16t3_summand_one hsum
    subst U
    obtain ⟨hEven, K, hKfield, hKfin, hKcard, hReal⟩ := hN
    letI := hKfield
    letI := hKfin
    have hKcard2 : Nat.card K = 2 := by simpa using hKcard
    obtain ⟨π, hπ⟩ := hReal
    have hn6 := s16k_six_le_of_isSpn hq hIs
    let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
    refine s16t3_isIrrOn_of_natReal R hZI (s16t3_natIrr_statedSp (m := n / 2) (K := K)) ?_
    refine ⟨Multiplicative.ofAdd (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n / 2)))
      (1 : K)), ?_⟩
    intro hcontra
    have h0 := congrFun (Multiplicative.toAdd.injective hcontra)
      (Sum.inl (⟨0, by omega⟩ : Fin (n / 2)))
    have h0' : (1 : K) = 0 := by simpa using h0
    exact one_ne_zero h0' 
  · obtain ⟨hIs, hsum⟩ := hOp
    obtain ⟨I, hZI, hIU, hN⟩ := s16t3_summand_one hsum
    subst U
    obtain ⟨hEven, K, hKfield, hKfin, hKcard, hReal⟩ := hN
    letI := hKfield
    letI := hKfin
    have hKcard2 : Nat.card K = 2 := by simpa using hKcard
    obtain ⟨π, hπ⟩ := hReal
    have hn6 := s16k_six_le_of_isOmegaPlus hq hIs
    have hm3 : 3 ≤ n / 2 := by omega
    let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
    refine s16t3_isIrrOn_of_natReal R hZI
      (s16t3_natIrr_statedOmegaPlus (m := n / 2) (K := K) hm3) ?_
    refine ⟨Multiplicative.ofAdd (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (n / 2)))
      (1 : K)), ?_⟩
    intro hcontra
    have h0 := congrFun (Multiplicative.toAdd.injective hcontra)
      (Sum.inl (⟨0, by omega⟩ : Fin (n / 2)))
    have h0' : (1 : K) = 0 := by simpa using h0
    exact one_ne_zero h0' 
  · obtain ⟨hIs, hsum⟩ := hOm
    obtain ⟨I, hZI, hIU, hN⟩ := s16t3_summand_one hsum
    subst U
    obtain ⟨hEven, K, hKfield, hKfin, b, c, hKcard, hpoly, hReal⟩ := hN
    letI := hKfield
    letI := hKfin
    have hKcard2 : Nat.card K = 2 := by simpa using hKcard
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hKcardF : Fintype.card K = 2 := by
      rw [← Nat.card_eq_fintype_card]; exact hKcard2
    haveI : CharP K 2 := charP_of_card_eq_prime hKcardF
    obtain ⟨π, hπ⟩ := hReal
    have hn4 := s16k_four_le_of_isOmegaMinus hq hIs
    have hm2 : 2 ≤ n / 2 := by omega
    let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
    refine s16t3_isIrrOn_of_natReal R hZI
      (s16t3_natIrr_statedOmegaMinus (b := b) (c := c) hm2 hpoly) ?_
    refine ⟨Multiplicative.ofAdd
      (Pi.single (Sum.inr (Sum.inr (⟨0, by norm_num⟩ : Fin 2))) (1 : K)), ?_⟩
    intro hcontra
    have h0 := congrFun (Multiplicative.toAdd.injective hcontra)
      (Sum.inr (Sum.inr (⟨0, by norm_num⟩ : Fin 2)))
    have h0' : (1 : K) = 0 := by simpa using h0
    exact one_ne_zero h0' 
  · obtain ⟨hIs, hsum⟩ := hAlt
    obtain ⟨I, hZI, hIU, hN⟩ := s16t3_summand_one hsum
    subst U
    obtain ⟨π, hπ⟩ := hN
    exact s16t3_isIrrOn_altDn (n := n) (by have := s16k_five_le_of_isAlt hq hIs; omega) hπ

theorem SumOfNatShape.eq_one_of_trivial (hq : CFSG.Open.IsQuasisimple ↥L)
    (h : SumOfNatShape L U Z 1) {l : MulAut W} (hl : l ∈ L)
    (htriv : ∀ u ∈ U, l u * u⁻¹ ∈ Z) : l = 1 := by
  rcases h with ⟨n, hSL | hSp | hOp | hOm | hAlt⟩
  · obtain ⟨hIs, hsum⟩ := hSL
    obtain ⟨I, hZI, hIU, hN⟩ := s16t3_summand_one hsum
    subst U
    obtain ⟨K, hKfield, hKfin, hKcard, hReal⟩ := hN
    letI := hKfield
    letI := hKfin
    obtain ⟨π, hπ⟩ := hReal
    exact s16t3_eq_one_of_trivial_of_model (FFModel.nat_faithful (StatedSL n K)) hπ hl htriv
  · obtain ⟨hIs, hsum⟩ := hSp
    obtain ⟨I, hZI, hIU, hN⟩ := s16t3_summand_one hsum
    subst U
    obtain ⟨hEven, K, hKfield, hKfin, hKcard, hReal⟩ := hN
    letI := hKfield
    letI := hKfin
    obtain ⟨π, hπ⟩ := hReal
    exact s16t3_eq_one_of_trivial_of_model (FFModel.nat_faithful (StatedSp (n / 2) K)) hπ hl htriv
  · obtain ⟨hIs, hsum⟩ := hOp
    obtain ⟨I, hZI, hIU, hN⟩ := s16t3_summand_one hsum
    subst U
    obtain ⟨hEven, K, hKfield, hKfin, hKcard, hReal⟩ := hN
    letI := hKfield
    letI := hKfin
    obtain ⟨π, hπ⟩ := hReal
    exact s16t3_eq_one_of_trivial_of_model
      (FFModel.nat_faithful (StatedOmega (StatedQuadPlus (n / 2) K))) hπ hl htriv
  · obtain ⟨hIs, hsum⟩ := hOm
    obtain ⟨I, hZI, hIU, hN⟩ := s16t3_summand_one hsum
    subst U
    obtain ⟨hEven, K, hKfield, hKfin, b, c, hKcard, hpoly, hReal⟩ := hN
    letI := hKfield
    letI := hKfin
    obtain ⟨π, hπ⟩ := hReal
    exact s16t3_eq_one_of_trivial_of_model
      (FFModel.nat_faithful (StatedOmega (StatedQuadMinus (n / 2) K b c))) hπ hl htriv
  · obtain ⟨hIs, hsum⟩ := hAlt
    obtain ⟨I, hZI, hIU, hN⟩ := s16t3_summand_one hsum
    subst U
    obtain ⟨π, hπ⟩ := hN
    exact s16t3_eq_one_of_trivial_of_model
      (CFSG.Quasithin.FFC.altDn_faithful (n := n) (by have := s16k_five_le_of_isAlt hq hIs; omega))
      hπ hl htriv

theorem SumOfNatShape.exists_move (hq : CFSG.Open.IsQuasisimple ↥L) (h : SumOfNatShape L U Z 1) :
    ∃ l ∈ L, ∃ u ∈ U, l u * u⁻¹ ∉ Z := by
  by_contra hcon
  have hcon' : ∀ l ∈ L, ∀ u ∈ U, l u * u⁻¹ ∈ Z := by
    intro l hl u hu
    by_contra hZ
    exact hcon ⟨l, hl, u, hu, hZ⟩
  have hLle : L ≤ ⊥ := fun l hl => by
    rw [Subgroup.mem_bot]
    exact SumOfNatShape.eq_one_of_trivial hq h hl (hcon' l hl)
  exact s16t3_quasisimple_ne_bot hq (le_antisymm hLle bot_le)

theorem SumOfNatShape.eight_mul_card_le (hq : CFSG.Open.IsQuasisimple ↥L)
    (h : SumOfNatShape L U Z 1) : 8 * Nat.card ↥Z ≤ Nat.card ↥U := by
  rcases h with ⟨n, hSL | hSp | hOp | hOm | hAlt⟩
  · obtain ⟨hIs, hsum⟩ := hSL
    obtain ⟨I, hZI, hIU, hN⟩ := s16t3_summand_one hsum
    subst U
    obtain ⟨K, hKfield, hKfin, hKcard, hReal⟩ := hN
    letI := hKfield
    letI := hKfin
    have hKcard2 : Nat.card K = 2 := by simpa using hKcard
    obtain ⟨π, hπ⟩ := hReal
    have hn3 := s16k_three_le_of_isSLn hq hIs
    let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
    have hι : 3 ≤ Fintype.card (Fin n) := by simpa using hn3
    exact s16t3_card_natReal R hZI hKcard2 hι
  · obtain ⟨hIs, hsum⟩ := hSp
    obtain ⟨I, hZI, hIU, hN⟩ := s16t3_summand_one hsum
    subst U
    obtain ⟨hEven, K, hKfield, hKfin, hKcard, hReal⟩ := hN
    letI := hKfield
    letI := hKfin
    have hKcard2 : Nat.card K = 2 := by simpa using hKcard
    obtain ⟨π, hπ⟩ := hReal
    have hn6 := s16k_six_le_of_isSpn hq hIs
    let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
    have hι : 3 ≤ Fintype.card (Fin (n / 2) ⊕ Fin (n / 2)) := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      have := Nat.two_mul_div_two_of_even hEven
      omega
    exact s16t3_card_natReal R hZI hKcard2 hι
  · obtain ⟨hIs, hsum⟩ := hOp
    obtain ⟨I, hZI, hIU, hN⟩ := s16t3_summand_one hsum
    subst U
    obtain ⟨hEven, K, hKfield, hKfin, hKcard, hReal⟩ := hN
    letI := hKfield
    letI := hKfin
    have hKcard2 : Nat.card K = 2 := by simpa using hKcard
    obtain ⟨π, hπ⟩ := hReal
    have hn6 := s16k_six_le_of_isOmegaPlus hq hIs
    let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
    have hι : 3 ≤ Fintype.card (Fin (n / 2) ⊕ Fin (n / 2)) := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      have := Nat.two_mul_div_two_of_even hEven
      omega
    exact s16t3_card_natReal R hZI hKcard2 hι
  · obtain ⟨hIs, hsum⟩ := hOm
    obtain ⟨I, hZI, hIU, hN⟩ := s16t3_summand_one hsum
    subst U
    obtain ⟨hEven, K, hKfield, hKfin, b, c, hKcard, hpoly, hReal⟩ := hN
    letI := hKfield
    letI := hKfin
    have hKcard2 : Nat.card K = 2 := by simpa using hKcard
    obtain ⟨π, hπ⟩ := hReal
    have hn4 := s16k_four_le_of_isOmegaMinus hq hIs
    let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
    have hι : 3 ≤ Fintype.card (Fin (n / 2 - 1) ⊕ Fin (n / 2 - 1) ⊕ Fin 2) := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      have := Nat.two_mul_div_two_of_even hEven
      omega
    exact s16t3_card_natReal R hZI hKcard2 hι
  · obtain ⟨hIs, hsum⟩ := hAlt
    obtain ⟨I, hZI, hIU, hN⟩ := s16t3_summand_one hsum
    subst U
    obtain ⟨π, hπ⟩ := hN
    have hn5 := s16k_five_le_of_isAlt hq hIs
    have hn0 : 0 < n := by omega
    obtain ⟨β', hβs, hβk, -⟩ := s16t3_alt_exists_beta hn0 hπ
    exact s16t3_card_of_quotient hβs hβk hZI (s16t3_card_altHeart hn5)

theorem exists_fixed_of_stable_subgroup {W : Type} [CommGroup W] [Finite W]
    {L T : Subgroup (MulAut W)} {I : Subgroup W}
    (hTI : StableUnder T I) (hShape : SumOfNatShape L I (I ⊓ fixV L) 1)
    (hq : CFSG.Open.IsQuasisimple ↥L)
    (h2 : ∀ w : W, w ^ 2 = 1) (hT2 : IsPGroup 2 T) :
    ∃ w ∈ I, w ≠ 1 ∧ ∀ t : ↥T, (t : MulAut W) w = w := by
  classical
  have hI8 : 8 ≤ Nat.card ↥I := by
    have h8 := SumOfNatShape.eight_mul_card_le hq hShape
    have hZ : 1 ≤ Nat.card ↥(I ⊓ fixV L) := by
      have hpos : 0 < Nat.card ↥(I ⊓ fixV L) :=
        Nat.card_pos_iff.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
      omega
    calc 8 = 8 * 1 := by ring
      _ ≤ 8 * Nat.card ↥(I ⊓ fixV L) := Nat.mul_le_mul_left 8 hZ
      _ ≤ Nat.card ↥I := h8
  have hI2group : IsPGroup 2 ↥I := by
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (h2 (x : W))
  obtain ⟨k, hk⟩ := hI2group.exists_card_eq
  have hI2 : 2 ∣ Nat.card ↥I := by
    rw [hk]
    refine dvd_pow_self 2 ?_
    intro hk0
    subst k
    rw [pow_zero] at hk
    omega
  let : MulAction ↥T ↥I :=
    { smul := fun t x => ⟨(t : MulAut W) (x : W), hTI t t.2 x x.2⟩
      one_smul := fun _ => Subtype.ext rfl
      mul_smul := fun _ _ _ => Subtype.ext rfl }
  have h1fix : (1 : ↥I) ∈ MulAction.fixedPoints ↥T ↥I := by
    rw [MulAction.mem_fixedPoints]
    intro t
    exact Subtype.ext (map_one (t : MulAut W))
  obtain ⟨w, hwfix, hwne⟩ :=
    hT2.exists_fixed_point_of_prime_dvd_card_of_fixed_point (hp := ⟨Nat.prime_two⟩)
      (α := ↥I) hI2 h1fix
  refine ⟨(w : W), w.2, ?_, fun t => congrArg Subtype.val
    (MulAction.mem_fixedPoints.1 hwfix t)⟩
  intro h1
  exact hwne (Subtype.ext (by simpa using h1.symm))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

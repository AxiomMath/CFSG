module

public import CFSG.RankThree.GF2n.Stroth80.Sec41iiIrred
public import CFSG.RankThree.GF2n.Stroth80.Sec44
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorAlg

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section TensorNat

@[expose] def PointBound {ι : Type} [Fintype ι] [DecidableEq ι] (K : Type) [Field K]
    (X : Subgroup (GL ι K)) : Prop :=
  ∀ u : ι → K, u ≠ 0 → ∀ P : Subgroup (GL ι K), P ≤ X → (∀ p ∈ P, p * p = 1) →
    (∀ p ∈ P, (p : Matrix ι ι K) *ᵥ u = u) →
    (∀ g ∈ X, (∃ c : K, (g : Matrix ι ι K) *ᵥ u = c • u) → ∀ p ∈ P, g * p * g⁻¹ ∈ P) →
    Nat.card ↥P ≤ Nat.card K ^ (Fintype.card ι - 1) ∧
      (Fintype.card ι = 3 → ∀ p ∈ P, ∀ v : ι → K,
        (p : Matrix ι ι K) *ᵥ v - v ∈ Submodule.span K {u})

structure ClassicalNat {ι : Type} [Fintype ι] [DecidableEq ι] (K : Type) [Field K]
    (X : Subgroup (GL ι K)) : Prop where
  three_le : 3 ≤ Fintype.card ι
  quasisimple : CFSG.IsQuasisimple ↥X
  addComm : AddCommutantScalar X
  point : PointBound K X

variable {E : Type*} [AddCommGroup E] {K : Type*} [Field K] [Module K E] {Γ : Type*} [Group Γ]
  {K' : Type} [Field K'] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem natIrred_of_irred (ρ : Γ →* Multiplicative (AddAut E)) (X : Subgroup Γ)
    (W : Submodule K E) (Xcl : Subgroup (GL ι K')) (θ : K ≃+* K') (Ψ : W ≃+ (ι → K'))
    (hΨ : ∀ (c : K) (w : W), Ψ (c • w) = θ c • Ψ w)
    (φ : ↥X →* GL ι K') (hφ : φ.range = Xcl)
    (hinv : ∀ x ∈ X, ∀ w ∈ W, (ρ x).toAdd w ∈ W)
    (hΨφ : ∀ (x : ↥X) (w : W), Ψ ⟨(ρ (x : Γ)).toAdd w, hinv x x.2 w w.2⟩ =
      (φ x : Matrix ι ι K') *ᵥ Ψ w)
    (hirred : ∀ S : Submodule K E, S ≤ W → (∀ x ∈ X, ∀ v ∈ S, (ρ x).toAdd v ∈ S) →
      S = ⊥ ∨ S = W) :
    NatIrred Xcl := by
  intro S' hS'
  let S : Submodule K E :=
    { carrier := {v : E | ∃ hv : v ∈ W, Ψ ⟨v, hv⟩ ∈ S'}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨W.add_mem ha hb, ?_⟩
        have hab : Ψ ⟨a + b, W.add_mem ha hb⟩ = Ψ ⟨a, ha⟩ + Ψ ⟨b, hb⟩ :=
          map_add Ψ ⟨a, ha⟩ ⟨b, hb⟩
        rw [hab]
        exact S'.add_mem ha' hb'
      zero_mem' := by
        refine ⟨W.zero_mem, ?_⟩
        have h0 : Ψ ⟨0, W.zero_mem⟩ = 0 := map_zero Ψ
        rw [h0]
        exact S'.zero_mem
      smul_mem' := by
        rintro c a ⟨ha, ha'⟩
        refine ⟨W.smul_mem c ha, ?_⟩
        have hc : Ψ ⟨c • a, W.smul_mem c ha⟩ = θ c • Ψ ⟨a, ha⟩ := hΨ c ⟨a, ha⟩
        rw [hc]
        exact S'.smul_mem _ ha' }
  have hmem : ∀ v : E, v ∈ S ↔ ∃ hv : v ∈ W, Ψ ⟨v, hv⟩ ∈ S' := fun v => Iff.rfl
  have hSW : S ≤ W := fun v hv => ((hmem v).mp hv).1
  have hSinv : ∀ x ∈ X, ∀ v ∈ S, (ρ x).toAdd v ∈ S := by
    intro x hx v hv
    obtain ⟨hvW, hvS⟩ := (hmem v).mp hv
    have hxX : φ ⟨x, hx⟩ ∈ Xcl := by
      rw [← hφ]
      exact MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
    have h1 : Ψ ⟨(ρ x).toAdd v, hinv x hx v hvW⟩ =
        (φ ⟨x, hx⟩ : Matrix ι ι K') *ᵥ Ψ ⟨v, hvW⟩ :=
      hΨφ ⟨x, hx⟩ ⟨v, hvW⟩
    refine (hmem _).mpr ⟨hinv x hx v hvW, ?_⟩
    rw [h1]
    exact hS' _ hxX _ hvS
  rcases hirred S hSW hSinv with hS0 | hSeq
  · left
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨w, hw⟩ := Ψ.surjective y
    have hwy : Ψ w ∈ S' := by
      rw [hw]
      exact hy
    have hwS : (w : E) ∈ S := (hmem (w : E)).mpr ⟨w.2, hwy⟩
    rw [hS0, Submodule.mem_bot] at hwS
    have hw0 : w = 0 := Subtype.ext hwS
    rw [Submodule.mem_bot, ← hw, hw0, map_zero]
  · right
    rw [eq_top_iff]
    intro y _
    have hyS : (Ψ.symm y : E) ∈ S := by
      rw [hSeq]
      exact (Ψ.symm y).2
    obtain ⟨_, h2⟩ := (hmem _).mp hyS
    have h3 : Ψ (Ψ.symm y) ∈ S' := h2
    rwa [AddEquiv.apply_symm_apply] at h3

theorem simple_of_natural [Finite K'] (ρ : Γ →* Multiplicative (AddAut E)) (X : Subgroup Γ)
    (W : Submodule K E) (Xcl : Subgroup (GL ι K')) (Ψ : W ≃+ (ι → K'))
    (φ : ↥X →* GL ι K') (hφ : φ.range = Xcl)
    (hinv : ∀ x ∈ X, ∀ w ∈ W, (ρ x).toAdd w ∈ W)
    (hΨφ : ∀ (x : ↥X) (w : W), Ψ ⟨(ρ (x : Γ)).toAdd w, hinv x x.2 w w.2⟩ =
      (φ x : Matrix ι ι K') *ᵥ Ψ w)
    (hirr : NatIrred Xcl) (hcomm : AddCommutantScalar Xcl) :
    ∀ T : AddSubgroup E, T ≤ W.toAddSubgroup → (∀ x ∈ X, ∀ v ∈ T, (ρ x).toAdd v ∈ T) →
      T = ⊥ ∨ T = W.toAddSubgroup := by
  intro T hT hTinv
  by_cases hT0 : T = ⊥
  · exact Or.inl hT0
  right
  let T' : AddSubgroup (ι → K') :=
    AddSubgroup.map Ψ.toAddMonoidHom (AddSubgroup.comap W.subtype.toAddMonoidHom T)
  have hmemT' : ∀ y, y ∈ T' ↔ ∃ w : W, (w : E) ∈ T ∧ Ψ w = y := by
    intro y
    constructor
    · intro hy
      obtain ⟨w, hw, hwy⟩ := AddSubgroup.mem_map.mp hy
      exact ⟨w, AddSubgroup.mem_comap.mp hw, hwy⟩
    · rintro ⟨w, hw, rfl⟩
      exact AddSubgroup.mem_map.mpr ⟨w, AddSubgroup.mem_comap.mpr hw, rfl⟩
  have hT'0 : T' ≠ ⊥ := by
    intro hbot
    obtain ⟨⟨v, hvT⟩, hv0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hT0
    have hvW : v ∈ W := hT hvT
    have hmem : Ψ ⟨v, hvW⟩ ∈ T' := (hmemT' _).mpr ⟨⟨v, hvW⟩, hvT, rfl⟩
    rw [hbot, AddSubgroup.mem_bot] at hmem
    have hw0 : (⟨v, hvW⟩ : W) = 0 := Ψ.injective (by rw [hmem, map_zero])
    have hw0' := congrArg (fun w : W => (w : E)) hw0
    exact hv0 (Subtype.ext hw0')
  have hT'inv : ∀ A ∈ Xcl, ∀ y ∈ T', (A : Matrix ι ι K') *ᵥ y ∈ T' := by
    intro A hA y hy
    obtain ⟨w, hwT, rfl⟩ := (hmemT' y).mp hy
    have hAφ : A ∈ φ.range := by
      rw [hφ]
      exact hA
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hAφ
    rw [← hΨφ x w]
    exact (hmemT' _).mpr ⟨⟨(ρ (x : Γ)).toAdd w, hinv x x.2 w w.2⟩, hTinv x x.2 w hwT, rfl⟩
  have hT'top : T' = ⊤ := eq_top_of_addInvariant hirr hcomm hT'0 hT'inv
  apply le_antisymm hT
  intro v hv
  have hvW : v ∈ W := hv
  have hmem : Ψ ⟨v, hvW⟩ ∈ T' := by
    rw [hT'top]
    exact AddSubgroup.mem_top _
  obtain ⟨w, hwT, hwy⟩ := (hmemT' _).mp hmem
  have hweq : w = ⟨v, hvW⟩ := Ψ.injective hwy
  rw [hweq] at hwT
  exact hwT

theorem card_of_natural [Finite K] (W : Submodule K E) (θ : K ≃+* K') (Ψ : W ≃+ (ι → K'))
    [Finite K'] : Nat.card W = Nat.card K ^ Fintype.card ι := by
  rw [Nat.card_congr Ψ.toEquiv, Nat.card_fun, ← Nat.card_congr θ.toEquiv,
    Nat.card_eq_fintype_card (α := ι)]


theorem nontriv_of_natural (ρ : Γ →* Multiplicative (AddAut E)) (X : Subgroup Γ)
    (W : Submodule K E) (Xcl : Subgroup (GL ι K')) (Ψ : W ≃+ (ι → K'))
    (φ : ↥X →* GL ι K') (hφ : φ.range = Xcl) (hφinj : Function.Injective φ)
    (hinv : ∀ x ∈ X, ∀ w ∈ W, (ρ x).toAdd w ∈ W)
    (hΨφ : ∀ (x : ↥X) (w : W), Ψ ⟨(ρ (x : Γ)).toAdd w, hinv x x.2 w w.2⟩ =
      (φ x : Matrix ι ι K') *ᵥ Ψ w)
    (hq : CFSG.IsQuasisimple ↥Xcl) :
    ∃ x ∈ X, ∃ w ∈ W, (ρ x).toAdd w ≠ w := by
  obtain ⟨-, -, a, b, hab⟩ := hq
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  have hne : a' * b' ≠ b' * a' := fun h => hab (by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])
  obtain ⟨g, hg1⟩ : ∃ g : ↥Xcl, g ≠ 1 :=
    ⟨a' * b' * (b' * a')⁻¹, fun h => hne (mul_inv_eq_one.mp h)⟩
  have hgX : (g : GL ι K') ∈ φ.range := by
    rw [hφ]
    exact g.2
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hgX
  have hM : (φ x : Matrix ι ι K') ≠ 1 := by
    intro h
    apply hg1
    apply Subtype.ext
    rw [← hx]
    exact Units.ext h
  obtain ⟨y, hy⟩ : ∃ y : ι → K', (φ x : Matrix ι ι K') *ᵥ y ≠ y := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    apply hM
    ext i j
    have h := congrFun (hcon (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.one_apply,
      Pi.single_apply] using h
  refine ⟨(x : Γ), x.2, ((Ψ.symm y : ↥W) : E), (Ψ.symm y).2, ?_⟩
  intro h
  apply hy
  have h2 : (⟨(ρ (x : Γ)).toAdd ((Ψ.symm y : ↥W) : E), hinv x x.2 _ (Ψ.symm y).2⟩ : ↥W) =
      Ψ.symm y := Subtype.ext h
  have h3 := hΨφ x (Ψ.symm y)
  rw [h2, AddEquiv.apply_symm_apply] at h3
  exact h3.symm

theorem perfect_of_natural (X : Subgroup Γ) (Xcl : Subgroup (GL ι K'))
    (φ : ↥X →* GL ι K') (hφ : φ.range = Xcl) (hφinj : Function.Injective φ)
    (hq : CFSG.IsQuasisimple ↥Xcl) : ⁅X, X⁆ = X := by
  have hXcl : ⁅Xcl, Xcl⁆ = Xcl := Subgroup.isPerfect_iff.mp hq.1
  have hφtop : (⊤ : Subgroup ↥X).map φ = Xcl := by
    rw [← MonoidHom.range_eq_map, hφ]
  have hXtop : ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ = (⊤ : Subgroup ↥X) := by
    apply Subgroup.map_injective hφinj
    rw [Subgroup.map_commutator, hφtop]
    exact hXcl
  exact Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hXtop)

theorem point_of_natural [Finite K] [Finite K'] (ρ : Γ →* Multiplicative (AddAut E))
    (X P : Subgroup Γ) (W : Submodule K E) (Xcl : Subgroup (GL ι K')) (θ : K ≃+* K')
    (Ψ : W ≃+ (ι → K')) (hΨ : ∀ (c : K) (w : W), Ψ (c • w) = θ c • Ψ w)
    (φ : ↥X →* GL ι K') (hφ : φ.range = Xcl) (hφinj : Function.Injective φ)
    (hinv : ∀ x ∈ X, ∀ w ∈ W, (ρ x).toAdd w ∈ W)
    (hΨφ : ∀ (x : ↥X) (w : W), Ψ ⟨(ρ (x : Γ)).toAdd w, hinv x x.2 w w.2⟩ =
      (φ x : Matrix ι ι K') *ᵥ Ψ w)
    (hcl : PointBound K' Xcl) {b : E} (hbW : b ∈ W) (hb0 : b ≠ 0) (hP : P ≤ X)
    (hP2 : ∀ p ∈ P, p * p = 1) (hPb : ∀ p ∈ P, (ρ p).toAdd b = b)
    (hPnorm : ∀ x ∈ X, (∃ c : K, (ρ x).toAdd b = c • b) → ∀ p ∈ P, x * p * x⁻¹ ∈ P) :
    Nat.card P ≤ Nat.card K ^ (Fintype.card ι - 1) ∧
      (Fintype.card ι = 3 → ∀ p ∈ P, ∀ w ∈ W, (ρ p).toAdd w - w ∈ Submodule.span K {b}) := by
  have hw0 : (⟨b, hbW⟩ : ↥W) ≠ 0 := fun h => hb0 (congrArg Subtype.val h)
  have hu0 : Ψ ⟨b, hbW⟩ ≠ 0 := fun h => hw0 (Ψ.injective (by rw [h, map_zero]))
  have hscal : ∀ c' : K', Ψ (θ.symm c' • (⟨b, hbW⟩ : ↥W)) = c' • Ψ ⟨b, hbW⟩ := by
    intro c'
    rw [hΨ, RingEquiv.apply_symm_apply]
  have hPm_le : (P.subgroupOf X).map φ ≤ Xcl := by
    rintro _ ⟨s, -, rfl⟩
    rw [← hφ]
    exact MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have hPm_sq : ∀ p ∈ (P.subgroupOf X).map φ, p * p = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    have hss : s * s = 1 := Subtype.ext (hP2 _ (Subgroup.mem_subgroupOf.mp hs))
    rw [← map_mul φ, hss, map_one φ]
  have hPm_fix : ∀ p ∈ (P.subgroupOf X).map φ, (p : Matrix ι ι K') *ᵥ Ψ ⟨b, hbW⟩ = Ψ ⟨b, hbW⟩ := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← hΨφ s ⟨b, hbW⟩]
    have hs' : (s : Γ) ∈ P := Subgroup.mem_subgroupOf.mp hs
    congr 1
    exact Subtype.ext (hPb _ hs')
  have hPm_norm : ∀ g ∈ Xcl, (∃ c : K', (g : Matrix ι ι K') *ᵥ Ψ ⟨b, hbW⟩ = c • Ψ ⟨b, hbW⟩) →
      ∀ p ∈ (P.subgroupOf X).map φ, g * p * g⁻¹ ∈ (P.subgroupOf X).map φ := by
    rintro g hg ⟨c', hc'⟩ _ ⟨s, hs, rfl⟩
    rw [← hφ] at hg
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg
    have h3 : Ψ ⟨(ρ (x : Γ)).toAdd b, hinv x x.2 b hbW⟩ =
        Ψ (θ.symm c' • (⟨b, hbW⟩ : ↥W)) := by
      rw [hscal c']
      exact (hΨφ x ⟨b, hbW⟩).trans hc'
    have hcb : (ρ (x : Γ)).toAdd b = θ.symm c' • b :=
      congrArg Subtype.val (Ψ.injective h3)
    have hxs := hPnorm (x : Γ) x.2 ⟨θ.symm c', hcb⟩ (s : Γ) (Subgroup.mem_subgroupOf.mp hs)
    have hmem : x * s * x⁻¹ ∈ P.subgroupOf X := Subgroup.mem_subgroupOf.mpr hxs
    rw [← map_inv φ, ← map_mul φ, ← map_mul φ]
    exact Subgroup.mem_map_of_mem φ hmem
  have hcl' := hcl (Ψ ⟨b, hbW⟩) hu0 ((P.subgroupOf X).map φ) hPm_le hPm_sq hPm_fix hPm_norm
  have hcardPm : Nat.card ↥((P.subgroupOf X).map φ) = Nat.card ↥P :=
    (Subgroup.card_map_of_injective hφinj).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv)
  have hcardK : Nat.card K = Nat.card K' := Nat.card_congr θ.toEquiv
  refine ⟨?_, ?_⟩
  · rw [← hcardPm, hcardK]
    exact hcl'.1
  · intro hcard p hp w hw
    have hpX : (⟨p, hP hp⟩ : ↥X) ∈ P.subgroupOf X := Subgroup.mem_subgroupOf.mpr hp
    have hmem := hcl'.2 hcard (φ ⟨p, hP hp⟩) (Subgroup.mem_map_of_mem φ hpX) (Ψ ⟨w, hw⟩)
    rw [← hΨφ ⟨p, hP hp⟩ ⟨w, hw⟩] at hmem
    have hΨd : Ψ (⟨(ρ p).toAdd w, hinv p (hP hp) w hw⟩ - (⟨w, hw⟩ : ↥W)) ∈
        Submodule.span K' {Ψ ⟨b, hbW⟩} := by
      rw [map_sub]
      exact hmem
    obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.mp hΨd
    have h5 : Ψ (θ.symm c' • (⟨b, hbW⟩ : ↥W)) =
        Ψ (⟨(ρ p).toAdd w, hinv p (hP hp) w hw⟩ - (⟨w, hw⟩ : ↥W)) := by
      rw [hscal c']
      exact hc'
    have h7 : (ρ p).toAdd w - w = θ.symm c' • b :=
      (congrArg Subtype.val (Ψ.injective h5)).symm
    rw [h7]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b)



@[expose] def ClassicalPointSLStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ m : ℕ, 3 ≤ m → PointBound K (StatedSL m K)

@[expose] def ClassicalPointSpStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ m : ℕ, 2 ≤ m → PointBound K (StatedSp m K)

@[expose] def ClassicalPointStatement : Prop :=
  ClassicalPointSLStatement ∧ ClassicalPointSpStatement ∧ (∀ (K : Type) [Field K] [Finite K] [CharP
      K 2], 4 ≤ Nat.card K → ∀ m : ℕ, 3 ≤ m → PointBound K (StatedOmega (StatedQuadPlus m K))) ∧
    (∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → ∀ (m : ℕ) (b c : K), 2 ≤ m → (∀
        s : K, s ^ 2 + b * s + c ≠ 0) → PointBound K (StatedOmega (StatedQuadMinus m K b c)))

@[expose] def PointTrivial {ι : Type} [Fintype ι] [DecidableEq ι] (K : Type) [Field K]
    (X : Subgroup (GL ι K)) (u : ι → K) : Prop :=
  ∀ P : Subgroup (GL ι K), P ≤ X → (∀ p ∈ P, p * p = 1) →
    (∀ p ∈ P, (p : Matrix ι ι K) *ᵥ u = u) →
    (∀ g ∈ X, (∃ c : K, (g : Matrix ι ι K) *ᵥ u = c • u) → ∀ p ∈ P, g * p * g⁻¹ ∈ P) →
    P = ⊥

@[expose] def ClassicalPointNonsingularStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    (∀ m : ℕ, 3 ≤ m → ∀ u : Fin m ⊕ Fin m → K, u ≠ 0 → StatedQuadPlus m K u ≠ 0 →
      PointTrivial K (StatedOmega (StatedQuadPlus m K)) u) ∧
    (∀ (m : ℕ) (b c : K), 2 ≤ m → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∀ u : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K, u ≠ 0 → StatedQuadMinus m K b c u ≠ 0 →
        PointTrivial K (StatedOmega (StatedQuadMinus m K b c)) u)

theorem tensorSide_of_natural [Finite K] [Finite K'] (ρ : Γ →* Multiplicative (AddAut E))
    (X P : Subgroup Γ) (b : E) (W : Submodule K E) (Xcl : Subgroup (GL ι K'))
    (hcl : ClassicalNat K' Xcl) (θ : K ≃+* K') (Ψ : W ≃+ (ι → K'))
    (hΨ : ∀ (c : K) (w : W), Ψ (c • w) = θ c • Ψ w)
    (φ : ↥X →* GL ι K') (hφ : φ.range = Xcl) (hφinj : Function.Injective φ)
    (hinv : ∀ x ∈ X, ∀ w ∈ W, (ρ x).toAdd w ∈ W)
    (hΨφ : ∀ (x : ↥X) (w : W), Ψ ⟨(ρ (x : Γ)).toAdd w, hinv x x.2 w w.2⟩ =
      (φ x : Matrix ι ι K') *ᵥ Ψ w)
    (hlin : ∀ x ∈ X, ∀ (c : K) (v : E), (ρ x).toAdd (c • v) = c • (ρ x).toAdd v)
    (hirred : ∀ S : Submodule K E, S ≤ W → (∀ x ∈ X, ∀ v ∈ S, (ρ x).toAdd v ∈ S) →
      S = ⊥ ∨ S = W)
    (hbW : b ∈ W) (hb0 : b ≠ 0) (hP : P ≤ X) (hP2 : ∀ p ∈ P, p * p = 1)
    (hPfix : ∀ v ∈ W, ((∀ p ∈ P, (ρ p).toAdd v = v) ↔ v ∈ Submodule.span K {b}))
    (hPnorm : ∀ x ∈ X, (∃ c : K, (ρ x).toAdd b = c • b) → ∀ p ∈ P, x * p * x⁻¹ ∈ P) :
    TensorSide ρ b X P W (Fintype.card ι) := by
  have hirrN := natIrred_of_irred ρ X W Xcl θ Ψ hΨ φ hφ hinv hΨφ hirred
  have hsimple := simple_of_natural ρ X W Xcl Ψ φ hφ hinv hΨφ hirrN hcl.addComm
  have hPb : ∀ p ∈ P, (ρ p).toAdd b = b :=
    (hPfix b hbW).mpr (Submodule.mem_span_singleton_self b)
  have hpt := point_of_natural ρ X P W Xcl θ Ψ hΨ φ hφ hφinj hinv hΨφ hcl.point hbW hb0 hP hP2
    hPb hPnorm
  exact
    { le := hP
      b_mem := hbW
      b_ne := hb0
      inv := hinv
      lin := hlin
      simple := hsimple
      card := card_of_natural W θ Ψ
      fixed := hPfix
      nontriv := nontriv_of_natural ρ X W Xcl Ψ φ hφ hφinj hinv hΨφ hcl.quasisimple
      perfect := perfect_of_natural X Xcl φ hφ hφinj hcl.quasisimple
      three := hcl.three_le
      pcard := hpt.1
      d3 := hpt.2 }

end TensorNat

section PerType

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem classicalNat_statedSL (hCQ : ClassicalQuasisimpleStatement)
    (hCG : ClassicalPointStatement) (hq : 4 ≤ Nat.card K) {m : ℕ} (hm : 3 ≤ m) :
    ClassicalNat K (StatedSL m K) :=
  ⟨by simpa using hm, (hCQ K hq).1 m (by omega), addCommutantScalar_statedSL (by omega),
    hCG.1 K hq m hm⟩

theorem classicalNat_statedSp (hCQ : ClassicalQuasisimpleStatement)
    (hCG : ClassicalPointStatement) (hq : 4 ≤ Nat.card K) {m : ℕ} (hm : 2 ≤ m) :
    ClassicalNat K (StatedSp m K) :=
  ⟨by simp; omega, (hCQ K hq).2.1 m (by omega), addCommutantScalar_statedSp,
    hCG.2.1 K hq m hm⟩

theorem classicalNat_statedOmegaPlus (hCQ : ClassicalQuasisimpleStatement)
    (hCG : ClassicalPointStatement) (hq : 4 ≤ Nat.card K) {m : ℕ} (hm : 3 ≤ m) :
    ClassicalNat K (StatedOmega (StatedQuadPlus m K)) :=
  ⟨by simp; omega, (hCQ K hq).2.2.1 m hm, addCommutantScalar_statedOmegaPlus hm,
    hCG.2.2.1 K hq m hm⟩

theorem classicalNat_statedOmegaMinus (hCQ : ClassicalQuasisimpleStatement)
    (hCG : ClassicalPointStatement) (hq : 4 ≤ Nat.card K) {m : ℕ} (b c : K) (hm : 2 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ClassicalNat K (StatedOmega (StatedQuadMinus m K b c)) :=
  ⟨by simp; omega, (hCQ K hq).2.2.2.1 m b c hm hirr, addCommutantScalar_statedOmegaMinus hm hirr,
    hCG.2.2.2 K hq m b c hm hirr⟩

end PerType

end CFSG.RankThree.GF2n.Stroth80

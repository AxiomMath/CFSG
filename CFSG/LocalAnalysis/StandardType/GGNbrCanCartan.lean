module

public import CFSG.LocalAnalysis.StandardType.GGNbrCan
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineAux
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS4aAuxA
public import CFSG.LocalAnalysis.StandardType.GGPZCartanRank
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureRefl
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
public import CFSG.LocalAnalysis.StandardType.GGLineStabNormalizes

public section
namespace CFSG.StandardType
open CFSG.Assembly
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggIntCartan_rank_eq_three {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (hn : Fintype.card Λ = 3) : Matrix.rank (C.map (Int.castRingHom (ZMod p))) = 3 := by
  have hp : p.Prime := Fact.out
  have key (C0 : Matrix (Fin 3) (Fin 3) ℤ) (e : Fin 3 ≃ Λ)
      (hC0 : ∀ i j, C (e i) (e j) = C0 i j)
      (hzero : ∀ c : Fin 3 → ZMod p, (∀ j, ∑ k, (C0 j k : ZMod p) * c k = 0) → c = 0) :
      Matrix.rank (C.map (Int.castRingHom (ZMod p))) = 3 := by
    let A := C0.map (Int.castRingHom (ZMod p))
    have hker : LinearMap.ker A.mulVecLin = ⊥ := by
      ext c
      simp only [LinearMap.mem_ker, Submodule.mem_bot]
      constructor
      · intro h
        apply hzero c
        intro j
        have hj := congrFun h j
        simpa [A, Matrix.mulVec, dotProduct] using hj
      · rintro rfl
        simp
    have hsum := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have hr : Matrix.rank A = 3 := by
      change Module.finrank (ZMod p) A.mulVecLin.range = 3
      rw [hker] at hsum
      simpa using hsum
    have heq : C.submatrix e e = C0 := Matrix.ext hC0
    change Matrix.rank (C0.map (Int.castRingHom (ZMod p))) = 3 at hr
    rw [← heq, ← Matrix.submatrix_map] at hr
    rwa [Matrix.rank_submatrix] at hr
  rcases ggIntCartan_models hM hC with
    ⟨n,e,hn1,hA | ⟨hn2,hB | hCC⟩ | ⟨hn4,hD⟩⟩ | ⟨e,hE6⟩ | ⟨e,hE7⟩ | ⟨e,hE8⟩ |
      ⟨e,hF4 | hF4⟩ | ⟨e,hG2 | hG2⟩
  · have hn3 : n = 3 := by simpa [hn] using Fintype.card_congr e
    subst n
    exact key _ e hA (ggCartanAInd_ker_zero (by
      intro h; have hd : p ∣ 4 := by simpa using h
      have hsmall : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        ((hp.dvd_of_dvd_pow (show p ∣ 2^2 by simpa using hd)))
      exact hp2 hsmall))
  · have hn3 : n = 3 := by simpa [hn] using Fintype.card_congr e
    subst n
    exact key _ e hB (ggCartanB_ker_zero hp2 (by norm_num))
  · have hn3 : n = 3 := by simpa [hn] using Fintype.card_congr e
    subst n
    exact key _ e hCC (ggCartanC_ker_zero hp2 (by norm_num))
  · have hn3 : n = 3 := by simpa [hn] using Fintype.card_congr e
    omega
  all_goals have hc := Fintype.card_congr e; simp [hn] at hc

theorem ggIntCartan_rank_eq_card_of_typeD4 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (e : Fin 4 ≃ Λ) (hM : M = (ggCoxeterMatrixD 4).reindex e) :
    Matrix.rank (C.map (Int.castRingHom (ZMod p))) = Fintype.card Λ := by
  classical
  subst hM
  have hD : GGIntCartan ((ggCoxeterMatrixD 4).reindex e)
      (Matrix.reindex e e (CartanMatrix.D 4)) := (ggIntCartan_D 4).reindex e
  have hEq : C = Matrix.reindex e e (CartanMatrix.D 4) := by
    rcases hC.eq_or_eq_transpose hD ((ggAtMostOneMultipleEdge_D 4).reindex e) with h|h
    · exact h
    · rw [h]
      ext i j
      exact (CartanMatrix.D_isSymm 4).apply _ _
  rw [hEq]
  have hecard : Fintype.card Λ = 4 := (Fintype.card_congr e).symm.trans (Fintype.card_fin 4)
  have hr : Matrix.rank ((CartanMatrix.D 4).map (Int.castRingHom (ZMod p))) = 4 := by
    let A := (CartanMatrix.D 4).map (Int.castRingHom (ZMod p))
    have hk : A.mulVecLin.ker = ⊥ := by
      ext c
      simp only [LinearMap.mem_ker,Submodule.mem_bot]
      constructor
      · intro h
        exact ggCartanD_ker_zero hp2 (by norm_num) c (by
          intro j
          have hj := congrFun h j
          simpa [A,Matrix.mulVec,dotProduct] using hj)
      · rintro rfl
        simp
    have hsum := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [hk] at hsum
    change Module.finrank (ZMod p) A.mulVecLin.range = 4
    simpa using hsum
  rw [hecard]
  change Matrix.rank ((CartanMatrix.D 4).submatrix e.symm e.symm |>.map (Int.castRingHom (ZMod p))) = 4
  rw [← Matrix.submatrix_map,Matrix.rank_submatrix]
  exact hr

theorem ggCard_inf_of_cartan_rank {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Bs X : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Fin n → MulAut ↥Bs)
    (h : Fin n → V) (α : Fin n → Module.Dual (ZMod p) V)
    (hφ : ∀ i, φ i ∈ ggAutomizer X Bs) (hC : ∀ i, C i i = 2)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (hrank : 3 ≤ Matrix.rank (C.map (Int.castRingHom (ZMod p)))) :
    p ^ 3 ≤ Nat.card ↥(Bs ⊓ X) := by
  classical
  let W : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h)
  have hFin : Finite V := Finite.of_equiv (Additive Bs) ι.toEquiv
  have : Finite V := hFin
  have hmem : ∀ i, ((Additive.toMul (ι.symm (h i)) : Bs) : G) ∈ X := by
    intro i
    exact ggCoroot_mem hp2 hN ι (hlin i)
      (by simpa only [hC i, Int.cast_ofNat] using hpair i i) (hφ i)
  let hW : Fin n → W := fun i => ⟨h i, Submodule.subset_span ⟨i, rfl⟩⟩
  let αW : Fin n → Module.Dual (ZMod p) W := fun i => (α i).comp W.subtype
  have hpairW : ∀ i j, αW i (hW j) = (C i j : ZMod p) := hpair
  have hthree : 3 ≤ Module.finrank (ZMod p) W :=
    hrank.trans (LevTwo.levTwoS4a_rank_core (h := hW) (α := αW) hpairW)
  have hle : ggSpanSub ι W ≤ Bs ⊓ X :=
    le_inf (ggSpanSub_le_bs ι W) (ggSpanSub_le ι hmem)
  have hcard : p ^ 3 ≤ Nat.card ↥(Bs ⊓ X) := by
    calc p ^ 3 ≤ p ^ Module.finrank (ZMod p) W :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos hthree
      _ = Nat.card W := FiniteField.pow_finrank_eq_natCard p W
      _ = Nat.card (ggSpanSub ι W) := (card_ggSpanSub ι W).symm
      _ ≤ Nat.card ↥(Bs ⊓ X) := Subgroup.card_le_of_le hle
  exact hcard

theorem ggCard_inf_of_weyl_rank_three {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Bs X : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M)
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hφ : ∀ i, φ i ∈ ggAutomizer X Bs)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (hrank : 3 ≤ Fintype.card Λ) : p ^ 3 ≤ Nat.card ↥(Bs ⊓ X) := by
  classical
  let e : Fin (Fintype.card Λ) ≃ Λ := (Fintype.equivFin Λ).symm
  let C' : Matrix (Fin (Fintype.card Λ)) (Fin (Fintype.card Λ)) ℤ := C.submatrix e e
  have hC' : ∀ i, C' i i = 2 := fun i => hC.1 _
  have hpair' : ∀ i j, (α (e i)) (h (e j)) = (C' i j : ZMod p) := fun i j => hpair _ _
  have hlin' : ∀ i v, ggLin (p := p) ι (φ (e i)) v = v - α (e i) v • h (e i) :=
    fun i v => hlin _ v
  have hr0 : Fintype.card Λ ≤ Matrix.rank (C.map (Int.castRingHom (ZMod p))) + 1 :=
    ggIntCartan_card_le_rank_add_one hM hC p hp2
  have hrEq : Matrix.rank (C'.map (Int.castRingHom (ZMod p))) =
      Matrix.rank (C.map (Int.castRingHom (ZMod p))) :=
    by
      change Matrix.rank ((C.submatrix e e).map (Int.castRingHom (ZMod p))) = _
      rw [← Matrix.submatrix_map]
      exact Matrix.rank_submatrix _ e e
  have hr' : 3 ≤ Matrix.rank (C'.map (Int.castRingHom (ZMod p))) := by
    rw [hrEq]
    by_cases h4 : 4 ≤ Fintype.card Λ
    · omega
    · rw [ggIntCartan_rank_eq_three hp2 hM hC (by omega)]
  exact ggCard_inf_of_cartan_rank hp2 hN ι (φ ∘ e) (h ∘ e) (α ∘ e)
    (fun i => hφ _) hC' hpair' hlin' hr'

theorem ggNbr_card_inf_of_weyl_rank_three {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M)
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hφ : ∀ i, φ i ∈ ggAutomizer K Bs)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (hrank : 3 ≤ Fintype.card Λ) : p ^ 3 ≤ Nat.card ↥(Bs ⊓ K) :=
  ggCard_inf_of_weyl_rank_three hp2 (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer hM hC ι φ h α hφ
    hpair hlin hrank

theorem ggNbr_stabilizer_le_normalizer_of_card_inf {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hcard : p ^ 3 ≤ Nat.card ↥(Bs ⊓ K)) (hy : y ∈ Bs) :
    (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs) ≤
        Subgroup.normalizer (ggAutomizer K Bs : Set (MulAut ↥Bs)) := by
  intro φ hφ
  have hφtop : φ ∈ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ.1
  have hfix : φ ⟨y, hy⟩ = ⟨y, hy⟩ := MulAction.mem_stabilizer_iff.mp hφ.2
  have hφC := mem_ggAutomizer_centralizer_of_apply_eq hy hφtop hfix
  have hKC : K ≤ Subgroup.centralizer ({y} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (GGResHyp.data_K hH).1 k hk
  have hN : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
    intro g hg
    apply ggNbr_mem_normalizer_of_card_inf hH hcard hg.1
    apply CFSG.GroupTheory.GL52.mem_normalizer_zpowers_of_conj_mem
    have hgy : g * y = y * g := Subgroup.mem_centralizer_singleton_iff.mp hg.2
    have he : g * y * g⁻¹ = y := by rw [hgy]; group
    rw [he]
    exact Subgroup.mem_zpowers y
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  constructor
  · intro hψ
    exact ggAutomizer_conj_mem_of_normalizer_le hKC le_rfl hN hφC hψ
  · intro hψ
    have h := ggAutomizer_conj_mem_of_normalizer_le hKC le_rfl hN
      (Subgroup.inv_mem _ hφC) hψ
    convert h using 1; group

end CFSG.StandardType

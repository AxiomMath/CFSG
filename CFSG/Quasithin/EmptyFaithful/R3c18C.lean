module

public import CFSG.Quasithin.EmptyFaithful.R3c18A
public import CFSG.Quasithin.EmptyFaithful.R3c18Fam
public import CFSG.Quasithin.EmptyFaithful.R3c18G
public import CFSG.Quasithin.Background.A318PSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinAbs

public section

namespace CFSG.Quasithin

namespace R3c18

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.SteinbergBR.EvenSp CFSG.QuasithinUnique.Fin257
open scoped MatrixGroups

theorem mem_of_index_le_two_of_odd_orderOf {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    [Finite G] (hH : H.index ≤ 2) {g : G} (hg : Odd (orderOf g)) : g ∈ H := by
  have hsq := CFSG.Quasithin.A318P.sq_mem_of_index_le_two hH g
  obtain ⟨m, hm⟩ := hg
  have hpow : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  have h : g = (g ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    have : 2 * (m + 1) = orderOf g + 1 := by omega
    rw [this, pow_succ, hpow, one_mul]
  rw [h]
  exact pow_mem hsq _

variable {K : Type} [Field K] [Finite K]

theorem sp4_p_mem {p : ℕ} (hp : Odd p) {α : MulAut (StatedProj (StatedSp 2 K))} {k : ℕ}
    (hα : orderOf α = p ^ k) :
    ∃ (A : gsp 2 K) (σ : K ≃+* K), α = conjAut 2 K A * fieldAut 2 K σ := by
  obtain ⟨-, -, hnorm, hidx⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := K)
  exact mem_spSemilinearAutGroup_iff.1
    (mem_of_index_le_two_of_odd_orderOf hidx (by rw [hα]; exact hp.pow))

section Plane

variable [CharP K 2]

@[expose] noncomputable def planeSL : (Fin 2 → SL(2, K)) →* StatedProj (StatedSp 2 K) :=
  (projEquiv (K := K) (n := 2) (by norm_num)).symm.toMonoidHom.comp
    ((planeHom.comp (MonoidHom.compLeft (Matrix.SpecialLinearGroup.toGL : SL(2, K) →* GL (Fin 2) K)
      (Fin 2))).codRestrict (StatedSp 2 K) fun x => planeHom_mem_statedSp _ fun j => (x j).2)

omit [Finite K] in
theorem planeSL_injective : Function.Injective (planeSL (K := K)) := by
  intro x y hxy
  have h1 := (projEquiv (K := K) (n := 2) (by norm_num)).symm.injective hxy
  have h2 := planeHom_injective (congrArg Subtype.val h1)
  funext j
  exact Matrix.SpecialLinearGroup.toGL_injective (congrFun h2 j)

omit [Finite K] [CharP K 2] in
theorem planeMat_map {n : ℕ} (h : Fin n → Matrix (Fin 2) (Fin 2) K) (σ : K ≃+* K) :
    (planeMat h).map σ = planeMat fun j => (h j).map σ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [planeMat, Matrix.fromBlocks, Matrix.diagonal_apply] <;> split_ifs <;> simp

omit [Finite K] in
theorem fieldAut_planeSL (σ : K ≃+* K) (x : Fin 2 → SL(2, K))
    (hx : ∀ j, Matrix.SpecialLinearGroup.map σ.toRingHom (x j) = x j) :
    fieldAut 2 K σ (planeSL x) = planeSL x := by
  have hn : 1 ≤ 2 := by norm_num
  set g : StatedSp 2 K := ⟨planeHom (fun j => Matrix.SpecialLinearGroup.toGL (x j)),
    planeHom_mem_statedSp _ fun j => (x j).2⟩ with hg
  have h1 : planeSL x = proj 2 K g := by
    change (projEquiv hn).symm g = proj 2 K g
    exact (MulEquiv.symm_apply_eq _).2 (CFSG.Quasithin.A318P.projEquiv_proj hn g).symm
  have h2 : fieldSp 2 K σ g = g := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_fieldSp]
    change ((planeHom (fun j => Matrix.SpecialLinearGroup.toGL (x j)) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map σ = _
    rw [planeHom_val]
    have hmap : ∀ j : Fin 2,
        ((Matrix.SpecialLinearGroup.toGL (x j) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map σ =
          ((Matrix.SpecialLinearGroup.toGL (x j) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
      fun j => congrArg Subtype.val (hx j)
    rw [planeMat_map]
    congr 1
    funext j
    exact hmap j
  rw [h1, fieldAut_proj, h2]

omit [Finite K] in
theorem exists_sq_sp4 (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) {a : SL(2, K)} (ha : orderOf a = p)
    (hfix : Matrix.SpecialLinearGroup.map σ.toRingHom a = a) :
    ∃ E : Subgroup (StatedProj (StatedSp 2 K)), Nat.card E = p ^ 2 ∧
      CFSG.Open.IsElemAbelian p E ∧ ∀ y ∈ E, fieldAut 2 K σ y = y := by
  classical
  have hap : a ^ p = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  set H : Subgroup (StatedProj (StatedSp 2 K)) :=
    (fieldAut 2 K σ).toMonoidHom.eqLocus (MonoidHom.id _) with hH
  have hfixS : ∀ (i : Fin 2) (j : Fin 2),
      Matrix.SpecialLinearGroup.map σ.toRingHom ((Pi.mulSingle i a : Fin 2 → SL(2, K)) j) =
        (Pi.mulSingle i a : Fin 2 → SL(2, K)) j := by
    intro i j
    by_cases hij : j = i
    · subst hij
      rw [Pi.mulSingle_eq_same, hfix]
    · rw [Pi.mulSingle_eq_of_ne hij, map_one]
  have hu₁ : planeSL (Pi.mulSingle 0 a : Fin 2 → SL(2, K)) ∈ H :=
    fieldAut_planeSL σ _ (hfixS 0)
  have hu₂ : planeSL (Pi.mulSingle 1 a : Fin 2 → SL(2, K)) ∈ H :=
    fieldAut_planeSL σ _ (hfixS 1)
  set v₁ : H := ⟨_, hu₁⟩ with hv₁
  set v₂ : H := ⟨_, hu₂⟩ with hv₂
  have hc : v₁ * v₂ = v₂ * v₁ := by
    apply Subtype.ext
    change planeSL (Pi.mulSingle 0 a : Fin 2 → SL(2, K)) * planeSL (Pi.mulSingle 1 a) =
      planeSL (Pi.mulSingle 1 a) * planeSL (Pi.mulSingle 0 a)
    rw [← map_mul, ← map_mul]
    congr 1
    exact (Pi.mulSingle_commute (f := fun _ : Fin 2 => SL(2, K)) (show (0 : Fin 2) ≠ 1 by decide)
      a a).eq
  have hv₁p : v₁ ^ p = 1 := by
    apply Subtype.ext
    change (planeSL (Pi.mulSingle 0 a : Fin 2 → SL(2, K))) ^ p = 1
    rw [← map_pow, ← Pi.mulSingle_pow, hap, Pi.mulSingle_one, map_one]
  have hv₂p : v₂ ^ p = 1 := by
    apply Subtype.ext
    change (planeSL (Pi.mulSingle 1 a : Fin 2 → SL(2, K))) ^ p = 1
    rw [← map_pow, ← Pi.mulSingle_pow, hap, Pi.mulSingle_one, map_one]
  have hind : ∀ i j : ℕ, v₁ ^ i * v₂ ^ j = 1 → p ∣ i ∧ p ∣ j := by
    intro i j h
    have h0 := congrArg (fun w : H => (w : StatedProj (StatedSp 2 K))) h
    have h1 : planeSL ((Pi.mulSingle 0 a : Fin 2 → SL(2, K)) ^ i *
        (Pi.mulSingle 1 a : Fin 2 → SL(2, K)) ^ j) = 1 := by
      change (planeSL (Pi.mulSingle 0 a : Fin 2 → SL(2, K))) ^ i *
        (planeSL (Pi.mulSingle 1 a : Fin 2 → SL(2, K))) ^ j = 1 at h0
      rwa [map_mul, map_pow, map_pow]
    have h2 := planeSL_injective (h1.trans (map_one planeSL).symm)
    have h20 := congrFun h2 0
    have h21 := congrFun h2 1
    simp only [Pi.mul_apply, ← Pi.mulSingle_pow, Pi.one_apply] at h20 h21
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide), mul_one] at h20
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide), one_mul] at h21
    rw [← ha]
    exact ⟨orderOf_dvd_of_pow_eq_one h20, orderOf_dvd_of_pow_eq_one h21⟩
  obtain ⟨P₀, hel, hcard, -, -⟩ := exists_elemAbelian_pair hp hc hv₁p hv₂p hind
  refine ⟨P₀.map H.subtype, ?_, CFSG.SectionRank.isElemAbelian_map hel H.subtype, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hcard]
  · rintro _ ⟨w, -, rfl⟩
    exact w.2

end Plane

@[expose] def Sp4PRankShape : Prop :=
  ∀ (K : Type) [Field K] [Finite K] {p : ℕ}, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card K →
    (if Even (orderOf (Nat.card K : ZMod p)) then 2 * 2 else 2) / orderOf (Nat.card K : ZMod p) ≤ 1 →
    CFSG.pRank p ↥(StatedSp 2 K) ≤ 1

theorem dvd_sq_sub_one_of_sq_eq {p Q : ℕ} (hQ : 0 < Q) (h : (Q : ZMod p) ^ 2 = 1) :
    p ∣ Q ^ 2 - 1 := by
  have h1 : ((Q ^ 2 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    push_cast
    exact h
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hQ)).1 h2.symm

theorem dvd_sq_sub_one_of_two_le_pRank_sp4 (hshape : Sp4PRankShape) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K) (h : 2 ≤ CFSG.pRank p ↥(StatedSp 2 K)) :
    p ∣ Nat.card K ^ 2 - 1 := by
  by_contra hnd
  have : Fact p.Prime := ⟨hp⟩
  have hQ0 : 0 < Nat.card K := Nat.card_pos
  set e := orderOf (Nat.card K : ZMod p) with he
  have he1 : e ≠ 1 := fun h1 => hnd (dvd_sq_sub_one_of_sq_eq hQ0 (by
    rw [orderOf_eq_one_iff.1 h1, one_pow]))
  have he2 : e ≠ 2 := fun h2 => hnd (dvd_sq_sub_one_of_sq_eq hQ0 (by
    rw [← h2, he]
    exact pow_orderOf_eq_one _))
  have hcond : (if Even e then 2 * 2 else 2) / e ≤ 1 := by
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · rw [h0, Nat.div_zero]
      omega
    · apply Nat.div_le_of_le_mul
      split_ifs with hev
      · obtain ⟨m, hm⟩ := hev
        omega
      · obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.1 hev
        omega
  have := hshape K hp hp2 hpK hcond
  omega

@[expose] noncomputable def pFrameSp4 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hshape : Sp4PRankShape)
    (K : Type) [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) :
    PFrame p (StatedProj (StatedSp 2 K)) (K ≃+* K) where
  fld := fieldAut 2 K
  fld_inter := fun c hc =>
    (fieldAut_mem_range_conjAut_iff (by norm_num)).1 (innAut_le_range_spConjAut 2 K hc)
  conj_mem := fun α k hα => by
    obtain ⟨A, σ, h⟩ := sp4_p_mem (hp.odd_of_ne_two (by omega)) hα
    obtain ⟨y, hy⟩ := conjAut_mem_inner_of_charTwo A
    exact ⟨1, conjAut 2 K A, ⟨y, hy⟩, σ, by rw [h]; simp⟩
  sq := fun h2 c hc => by
    have h2' : 2 ≤ CFSG.pRank p ↥(StatedSp 2 K) := by
      rw [← pRank_congr hp.one_lt (projEquiv (K := K) (n := 2) (by norm_num))]
      exact h2
    have hpK : ¬ p ∣ Nat.card K := by
      intro h
      rw [hK] at h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
      omega
    have hd : p ∣ Nat.card K ^ 2 - 1 :=
      dvd_sq_sub_one_of_two_le_pRank_sp4 hshape hp (by omega) hpK h2'
    obtain ⟨hpf, k, hk, hkcard⟩ := exists_fixed_subfield hf hK c hc
    have hKk : Nat.card K = Nat.card k ^ p := by
      rw [hK, hkcard, ← pow_mul, Nat.div_mul_cancel hpf]
    have hq0 : 0 < Nat.card k := by
      rw [hkcard]
      exact pow_pos (by norm_num) _
    have hd' : p ∣ Nat.card k ^ 2 - 1 := by
      rw [hKk] at hd
      exact (dvd_pow_sub_one_iff_of_pow hp hq0 2).1 hd
    obtain ⟨a, ha, hfix⟩ := exists_fixed_sl2_elem c hk hp hd'
    exact exists_sq_sp4 c hp ha hfix

theorem qLiePRankFam_sp4 (hshape : Sp4PRankShape) :
    QLiePRankFam (fun S _ => ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel S .PSp 2 2 f) := by
  intro p hp hp5 X _ _ S _ hC _ ⟨f, hf, hm⟩ hS2 hX
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hm
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have : Fact p.Prime := ⟨hp⟩
  exact pframe_core hC ((pFrameSp4 hp hp5 hshape K hK (by omega)).ofMulEquiv hp.one_lt e) hS2 hX

end R3c18

end CFSG.Quasithin

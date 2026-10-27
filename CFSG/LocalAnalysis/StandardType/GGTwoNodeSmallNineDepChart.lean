module

public import Certificates.Data.CFSGNative.TwoNodeSmall.Check
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import TauCeti.LinearAlgebra.RootSystem.Chain
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure NineDepChart (D : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 8 → V) (α : Fin 8 → Module.Dual (ZMod 3) V) (x : V) (u : Fin 8 → ZMod 3) where
  e : V ≃ₗ[ZMod 3] (Fin D → ZMod 3)
  h_eq : ∀ (i : Fin 8) (j : Fin D), e (h i) j = (((hvec8 i).getD j 0 : ℕ) : ZMod 3)
  x_eq : ∀ j : Fin D, e x j = ((([0, 0, 0, 0, 0, 0, 0, 1, 0] : List ℕ).getD j 0 : ℕ) : ZMod 3)
  α_eq : ∀ (i : Fin 8) (w : V), α i w =
    ∑ j : Fin D, ((((alpha8 i).getD j 0 : ℕ) : ZMod 3) + (if j.val = 8 then u i else 0)) * e w j

private theorem pk2_finite {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (α : Fin 8 → Module.Dual (ZMod 3) V) (x : V) (hxne : x ≠ 0)
    (hx : ∀ i, α i x = 0)
    (hfix : ∀ v, (∀ i, α i v = 0) → v ∈ Submodule.span (ZMod 3) ({x} : Set V)) :
    Module.Finite (ZMod 3) V := by
  let ψ : V →ₗ[ZMod 3] (Fin 8 → ZMod 3) :=
    { toFun := fun v i => α i v
      map_add' := by intro a b; funext i; simp
      map_smul' := by intro c a; funext i; simp }
  have hker : LinearMap.ker ψ = Submodule.span (ZMod 3) ({x} : Set V) := by
    apply le_antisymm
    · intro v hv
      exact hfix v (fun i => by
        have := congrFun (LinearMap.mem_ker.mp hv) i
        simpa [ψ] using this)
    · rw [Submodule.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      funext i
      simp [ψ, hx i]
  obtain ⟨β, hβx, -⟩ :=
    Submodule.exists_le_ker_of_notMem (p := (⊥ : Submodule (ZMod 3) V)) (v := x)
      (by rw [Submodule.mem_bot]; exact hxne)
  let f : V →ₗ[ZMod 3] ((Fin 8 → ZMod 3) × ZMod 3) :=
    { toFun := fun v => (ψ v, β v)
      map_add' := by intro a b; ext <;> simp [ψ]
      map_smul' := by intro c a; ext <;> simp [ψ] }
  have hf : Function.Injective f := by
    intro u v huv
    have hψ : ψ (u - v) = 0 := by
      have h1 : (f (u - v)).1 = 0 := by
        rw [map_sub]; simp [congrArg Prod.fst huv]
      simpa [f] using h1
    have hβ : β (u - v) = 0 := by
      have h1 : (f (u - v)).2 = 0 := by
        rw [map_sub]; simp [congrArg Prod.snd huv]
      simpa [f] using h1
    have hmem : u - v ∈ Submodule.span (ZMod 3) ({x} : Set V) := by
      rw [← hker]; exact LinearMap.mem_ker.mpr hψ
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hc0 : c = 0 := by
      have hcz : c * β x = 0 := by
        rw [← hc] at hβ
        simpa [smul_eq_mul] using hβ
      exact (mul_eq_zero.mp hcz).resolve_right hβx
    rw [hc0, zero_smul] at hc
    exact sub_eq_zero.mp hc.symm
  exact FiniteDimensional.of_injective f hf

private lemma pk2_cartan_cast (i j : Fin 8) :
    (CartanMatrix.A 8 i j : ZMod 3) = ((cl i.val j.val : ℕ) : ZMod 3) := by
  rw [← TauCeti.chainEntry_eq_cartanMatrix_A (n := 8) i j]
  simp only [TauCeti.chainEntry_def, cl]
  split_ifs <;> push_cast <;> first | omega | decide

private lemma pk2_alpha8_getD (i : Fin 8) (j : Fin 7) :
    (alpha8 i).getD j 0 = cl i.val j.val := by
  fin_cases j <;> rfl

private lemma pk2_alpha8_getD7 (i : Fin 8) : (alpha8 i).getD (7 : ℕ) 0 = 0 := rfl

private lemma pk2_alpha8_getD8 (i : Fin 8) : (alpha8 i).getD (8 : ℕ) 0 = 0 := rfl

private lemma pk2_sum_castSucc {n : ℕ} (c : Fin n → ZMod 3) (j : Fin (n + 1)) :
    (∑ k : Fin n, c k * (if j = k.castSucc then (1 : ZMod 3) else 0))
      = if h : (j : ℕ) < n then c ⟨j, h⟩ else 0 := by
  classical
  by_cases hj : (j : ℕ) < n
  · rw [dif_pos hj]
    have hmain : (∑ k : Fin n, c k * (if j = k.castSucc then (1 : ZMod 3) else 0))
        = c ⟨j, hj⟩ * (if j = (⟨j, hj⟩ : Fin n).castSucc then (1 : ZMod 3) else 0) :=
      Finset.sum_eq_single (⟨j, hj⟩ : Fin n) (fun b _ hb => by
        have hne : ¬ (j = b.castSucc) := by
          intro h
          exact hb (Fin.ext (by have := congrArg Fin.val h; simpa using this.symm))
        simp [hne]) (fun h => absurd (Finset.mem_univ _) h)
    rw [hmain]
    have hjc : (⟨j, hj⟩ : Fin n).castSucc = j := Fin.ext rfl
    simp [hjc]
  · rw [dif_neg hj]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hne : ¬ (j = b.castSucc) := by
      intro h; exact hj (by rw [h]; exact b.isLt)
    simp [hne]

private lemma pk2_sum_castSucc9 (c : Fin 7 → ZMod 3) (j : Fin 9) :
    (∑ k : Fin 7, c k * (if j = k.castSucc.castSucc then (1 : ZMod 3) else 0))
      = if h : (j : ℕ) < 7 then c ⟨j, h⟩ else 0 := by
  classical
  by_cases hj : (j : ℕ) < 7
  · rw [dif_pos hj]
    have hmain : (∑ k : Fin 7, c k * (if j = k.castSucc.castSucc then (1 : ZMod 3) else 0))
        = c ⟨j, hj⟩
          * (if j = ((⟨j, hj⟩ : Fin 7).castSucc.castSucc) then (1 : ZMod 3) else 0) :=
      Finset.sum_eq_single (⟨j, hj⟩ : Fin 7) (fun b _ hb => by
        have hne : ¬ (j = b.castSucc.castSucc) := by
          intro h
          exact hb (Fin.ext (by have := congrArg Fin.val h; simpa using this.symm))
        simp [hne]) (fun h => absurd (Finset.mem_univ _) h)
    rw [hmain]
    have hjc : ((⟨j, hj⟩ : Fin 7).castSucc.castSucc : Fin 9) = j := Fin.ext rfl
    simp [hjc]
  · rw [dif_neg hj]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hne : ¬ (j = b.castSucc.castSucc) := by
      intro h; exact hj (by rw [h]; exact b.isLt)
    simp [hne]

private lemma pk2_cast_mod3 (n : ℕ) : ((n : ℕ) : ZMod 3) = (((n % 3 : ℕ)) : ZMod 3) := by
  nth_rewrite 1 [← Nat.mod_add_div n 3]
  push_cast
  rw [show (3 : ZMod 3) = 0 by decide, zero_mul, add_zero]

private lemma pk2_hvec8_last_val (j : Fin 8) :
    ((hvec8 (Fin.last 7)).getD j 0 : ℕ) = if (j : ℕ) < 7 then ((j : ℕ) + 1) % 3 else 0 := by
  fin_cases j <;> rfl

private lemma pk2_hvec8_last_val9 (j : Fin 9) :
    ((hvec8 (Fin.last 7)).getD j 0 : ℕ) = if (j : ℕ) < 7 then ((j : ℕ) + 1) % 3 else 0 := by
  fin_cases j <;> rfl

private lemma pk2_h_last {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 8 → V)
    (hrel : ∑ i : Fin 8, ((((i : ℕ) + 1 : ℕ)) : ZMod 3) • h i = 0) :
    h (Fin.last 7) = ∑ i : Fin 7, ((((i : ℕ) + 1 : ℕ)) : ZMod 3) • h i.castSucc := by
  set S : V := ∑ i : Fin 7, ((((i : ℕ) + 1 : ℕ)) : ZMod 3) • h i.castSucc with hSdef
  have hrel' := hrel
  rw [Fin.sum_univ_castSucc] at hrel'
  simp only [Fin.val_castSucc] at hrel'
  rw [← hSdef] at hrel'
  have hlast : ((((Fin.last 7 : Fin 8) : ℕ) + 1 : ℕ) : ZMod 3) = 2 := by decide
  rw [hlast] at hrel'
  have hS : (2 : ZMod 3) • h (Fin.last 7) = -S := by
    rw [eq_neg_iff_add_eq_zero]
    rw [add_comm]
    exact hrel'
  have h2 : (2 : ZMod 3) * 2 = 1 := by decide
  calc h (Fin.last 7) = (2 * 2 : ZMod 3) • h (Fin.last 7) := by rw [h2, one_smul]
    _ = (2 : ZMod 3) • ((2 : ZMod 3) • h (Fin.last 7)) := by rw [smul_smul]
    _ = (2 : ZMod 3) • (-S) := by rw [hS]
    _ = -((2 : ZMod 3) • S) := by rw [smul_neg]
    _ = -(-S) := by rw [show (2 : ZMod 3) = -1 from by decide, neg_smul, one_smul]
    _ = S := neg_neg S

theorem ninedep_chart {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (hV : Module.finrank (ZMod 3) V ≤ 9) (h : Fin 8 → V) (α : Fin 8 → Module.Dual (ZMod 3) V)
    (x : V) (hF : CFSG.StandardType.GGDepAFrame 3 9 h α x) :
    ∃ (D : ℕ) (u : Fin 8 → ZMod 3), (D = 8 ∨ D = 9) ∧ Nonempty (NineDepChart D h α x u) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Module.Finite (ZMod 3) V := pk2_finite α x hF.x_ne hF.x_ker hF.fix
  obtain ⟨hrel, hxH, hHfin⟩ := CFSG.StandardType.ggDepA_relation (p := 3) (N := 9) hF
  have hHfin' : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) = 7 := by
    rw [show 9 - 2 = 7 by norm_num] at hHfin
    exact hHfin
  let b7 : Fin 7 → V := fun i => h i.castSucc
  have h7eq : h (Fin.last 7) = ∑ i : Fin 7, ((((i : ℕ) + 1 : ℕ)) : ZMod 3) • h i.castSucc :=
    pk2_h_last h hrel
  have h7mem : h (Fin.last 7) ∈ Submodule.span (ZMod 3) (Set.range b7) := by
    rw [h7eq]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span (ZMod 3) (Set.range h) = Submodule.span (ZMod 3) (Set.range b7) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro v ⟨j, rfl⟩
      exact Fin.lastCases h7mem (fun i => Submodule.subset_span ⟨i, rfl⟩) j
    · rw [Submodule.span_le]
      rintro v ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i.castSucc, rfl⟩
  have hx7 : x ∉ Submodule.span (ZMod 3) (Set.range b7) := by
    rw [← hspan]; exact hxH
  have hb7 : LinearIndependent (ZMod 3) b7 := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    change Fintype.card (Fin 7) =
      Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range b7))
    rw [← hspan, hHfin']
    norm_num
  let bfull : Fin 8 → V := Fin.snoc b7 x
  have hbfull : LinearIndependent (ZMod 3) bfull := by
    have := (linearIndependent_finSnoc (K := ZMod 3) (v := b7) (x := x)).mpr ⟨hb7, hx7⟩
    simpa [bfull] using this
  have h8low : 8 ≤ Module.finrank (ZMod 3) V := by
    have := LinearIndependent.fintype_card_le_finrank hbfull
    simpa using this
  have hbfull_castSucc : ∀ i : Fin 7, bfull i.castSucc = h i.castSucc := by
    intro i
    have h : bfull i.castSucc = b7 i := by simp [bfull]
    rw [h]
  have hbfull_last : bfull (Fin.last 7) = x := rfl
  have hfr : Module.finrank (ZMod 3) V = 8 ∨ Module.finrank (ZMod 3) V = 9 := by omega
  rcases hfr with h8 | h9
  ·
    have hcard8 : Fintype.card (Fin 8) = Module.finrank (ZMod 3) V := by simp [h8]
    let b : Module.Basis (Fin 8) (ZMod 3) V := basisOfLinearIndependentOfCardEqFinrank hbfull hcard8
    have hb_eq : (b : Fin 8 → V) = bfull :=
      coe_basisOfLinearIndependentOfCardEqFinrank hbfull hcard8
    have hb_apply : ∀ i : Fin 8, b i = bfull i := fun i => congrFun hb_eq i
    refine ⟨8, (fun _ => 0), Or.inl rfl, ?_⟩
    refine ⟨b.equivFun, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ ?_ i
      · have hh : b.equivFun (h (Fin.last 7)) =
            ∑ k : Fin 7, ((((k : ℕ) + 1 : ℕ)) : ZMod 3) •
              (Pi.single k.castSucc (1 : ZMod 3) : Fin 8 → ZMod 3) := by
          rw [h7eq, map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_smul]
          congr 1
          ext j
          rw [show h k.castSucc = b k.castSucc from by
                rw [hb_apply k.castSucc]; exact (hbfull_castSucc k).symm,
            Module.Basis.equivFun_self b k.castSucc j]
          simp [Pi.single_apply, eq_comm]
        rw [hh, Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        rw [pk2_sum_castSucc, pk2_hvec8_last_val]
        by_cases hj : (j : ℕ) < 7
        · rw [dif_pos hj, if_pos hj]
          exact pk2_cast_mod3 ((j : ℕ) + 1)
        · rw [dif_neg hj, if_neg hj]
          simp
      · intro i'
        have hhi : h i'.castSucc = b i'.castSucc := by
          rw [hb_apply i'.castSucc]; exact (hbfull_castSucc i').symm
        rw [hhi, Module.Basis.equivFun_self b i'.castSucc j]
        fin_cases i' <;> fin_cases j <;> norm_num [hvec8]
    · intro j
      have hx : x = b (Fin.last 7) := by
        rw [hb_apply (Fin.last 7)]; exact hbfull_last.symm
      rw [hx, Module.Basis.equivFun_self b (Fin.last 7) j]
      fin_cases j <;> norm_num
    · intro i w
      have hbα : ∀ j : Fin 8, α i (b j) = (((alpha8 i).getD j 0 : ℕ) : ZMod 3) := by
        intro j
        refine Fin.lastCases ?_ ?_ j
        · rw [hb_apply (Fin.last 7), hbfull_last, hF.x_ker i]
          rw [show (alpha8 i).getD (Fin.last 7) 0 = 0 from pk2_alpha8_getD7 i]
          norm_num
        · intro j'
          rw [hb_apply j'.castSucc, hbfull_castSucc j', hF.pair i j'.castSucc]
          rw [show (alpha8 i).getD j'.castSucc 0 = cl i.val j'.val from pk2_alpha8_getD i j']
          exact pk2_cartan_cast i j'.castSucc
      have hw : w = ∑ j : Fin 8, b.equivFun w j • b j := by
        simpa [Module.Basis.equivFun_apply] using (b.sum_repr w).symm
      conv_lhs => rw [hw]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hbα j]
      have hj : ¬ (j.val = 8) := by have := j.isLt; omega
      rw [if_neg hj, add_zero, mul_comm]
  ·
    have hcard9 : Fintype.card (Fin 9) = Module.finrank (ZMod 3) V := by simp [h9]
    have hbfull_fin : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range bfull)) = 8 := by
      rw [finrank_span_eq_card hbfull]; simp
    have hlt : Submodule.span (ZMod 3) (Set.range bfull) < ⊤ := by
      refine Submodule.lt_top_of_finrank_lt_finrank ?_
      rw [hbfull_fin, h9]; norm_num
    obtain ⟨e₀, -, he₀⟩ := IsConcreteLE.exists_of_lt hlt
    let b'full : Fin 9 → V := Fin.snoc bfull e₀
    have hb'full : LinearIndependent (ZMod 3) b'full := by
      have := (linearIndependent_finSnoc (K := ZMod 3) (v := bfull) (x := e₀)).mpr ⟨hbfull, he₀⟩
      simpa [b'full] using this
    let b' : Module.Basis (Fin 9) (ZMod 3) V := basisOfLinearIndependentOfCardEqFinrank hb'full hcard9
    have hb'_eq : (b' : Fin 9 → V) = b'full :=
      coe_basisOfLinearIndependentOfCardEqFinrank hb'full hcard9
    have hb'_apply : ∀ i : Fin 9, b' i = b'full i := fun i => congrFun hb'_eq i
    have hb'full_castSucc : ∀ i : Fin 8, b'full i.castSucc = bfull i := by
      intro i; simp [b'full]
    have hb'full_last : b'full (Fin.last 8) = e₀ := rfl
    refine ⟨9, (fun i => α i e₀), Or.inr rfl, ?_⟩
    refine ⟨b'.equivFun, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ ?_ i
      · have hh : b'.equivFun (h (Fin.last 7)) =
            ∑ k : Fin 7, ((((k : ℕ) + 1 : ℕ)) : ZMod 3) •
              (Pi.single k.castSucc.castSucc (1 : ZMod 3) : Fin 9 → ZMod 3) := by
          rw [h7eq, map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_smul]
          congr 1
          ext j
          rw [show h k.castSucc = b' k.castSucc.castSucc from by
                rw [hb'_apply k.castSucc.castSucc, hb'full_castSucc k.castSucc,
                  hbfull_castSucc k],
            Module.Basis.equivFun_self b' k.castSucc.castSucc j]
          simp [Pi.single_apply, eq_comm]
        rw [hh, Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        rw [pk2_sum_castSucc9, pk2_hvec8_last_val9]
        by_cases hj : (j : ℕ) < 7
        · rw [dif_pos hj, if_pos hj]
          exact pk2_cast_mod3 ((j : ℕ) + 1)
        · rw [dif_neg hj, if_neg hj]
          simp
      · intro i'
        have hhi : h i'.castSucc = b' i'.castSucc.castSucc := by
          rw [hb'_apply i'.castSucc.castSucc, hb'full_castSucc i'.castSucc, hbfull_castSucc i']
        rw [hhi, Module.Basis.equivFun_self b' i'.castSucc.castSucc j]
        fin_cases i' <;> fin_cases j <;> norm_num [hvec8]
    · intro j
      have hx : x = b' ⟨7, by norm_num⟩ := by
        rw [hb'_apply (⟨7, by norm_num⟩ : Fin 9)]
        have h2 : (⟨7, by norm_num⟩ : Fin 9) = (Fin.last 7 : Fin 8).castSucc := by ext; rfl
        rw [h2, hb'full_castSucc (Fin.last 7), hbfull_last]
      rw [hx, Module.Basis.equivFun_self b' ⟨7, by norm_num⟩ j]
      fin_cases j <;> norm_num
    · intro i w
      have hbα : ∀ j : Fin 9, α i (b' j) =
          (((alpha8 i).getD j 0 : ℕ) : ZMod 3) + (if j.val = 8 then α i e₀ else 0) := by
        intro j
        refine Fin.lastCases ?_ ?_ j
        · rw [hb'_apply (Fin.last 8), hb'full_last]
          rw [show (alpha8 i).getD (Fin.last 8) 0 = 0 from pk2_alpha8_getD8 i,
            if_pos (by decide)]
          simp
        · intro j'
          rw [hb'_apply j'.castSucc, hb'full_castSucc j']
          rw [if_neg (by rw [Fin.val_castSucc]; exact ne_of_lt j'.isLt)]
          refine Fin.lastCases ?_ ?_ j'
          · rw [hbfull_last, hF.x_ker i]
            rw [show (alpha8 i).getD ((Fin.last 7).castSucc : Fin 9) 0 = 0 from
              pk2_alpha8_getD7 i]
            norm_num
          · intro j''
            rw [hbfull_castSucc j'', hF.pair i j''.castSucc]
            rw [show (alpha8 i).getD (j''.castSucc.castSucc : Fin 9) 0 = cl i.val j''.val from
              pk2_alpha8_getD i j'']
            rw [add_zero]
            exact pk2_cartan_cast i j''.castSucc
      have hw : w = ∑ j : Fin 9, b'.equivFun w j • b' j := by
        simpa [Module.Basis.equivFun_apply] using (b'.sum_repr w).symm
      conv_lhs => rw [hw]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hbα j, mul_comm]

end CFSG.TwoNodeSmall

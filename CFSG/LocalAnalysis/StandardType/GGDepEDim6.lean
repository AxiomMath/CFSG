module

public import CFSG.LocalAnalysis.StandardType.GGDepEDefs
public import CFSG.LocalAnalysis.StandardType.GGDepERelation
public import CFSG.LocalAnalysis.StandardType.GGDepEFrame
public import CFSG.LocalAnalysis.StandardType.GGDepAYFixed
public import CFSG.LocalAnalysis.StandardType.GGResDepType
public import CFSG.LocalAnalysis.StandardType.GGResLeaves
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def lr7d6_kN : Fin 6 → ℕ := ![1, 0, 2, 0, 1, 2]

private def lr7d6_k : Fin 6 → ZMod 3 := fun i => (lr7d6_kN i : ZMod 3)

private theorem lr7d6_E6_symm (i j : Fin 6) :
    CartanMatrix.E 6 i j = CartanMatrix.E 6 j i := by
  rw [CartanMatrix.E_six_eq]
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem lr7d6_E6_kernel (j : Fin 6) :
    ∑ i : Fin 6, (CartanMatrix.E 6 j i : ZMod 3) * lr7d6_k i = 0 := by
  rw [CartanMatrix.E_six_eq]
  fin_cases j <;> decide +kernel

private theorem lr7d6_pos_fact {b : Fin 6} (hb : b = 0 ∨ b = 1 ∨ b = 5)
    (h : lr7d6_k b = 0) : b = 1 := by
  rcases hb with rfl | rfl | rfl
  · exact absurd h (by decide +kernel)
  · rfl
  · exact absurd h (by decide +kernel)

theorem ggDepE_dim6_pos {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod p) V} {x : V}
    (F : GGDepEFrame p h α x) (hdim : Module.finrank (ZMod p) V = 6) (b : Fin 6)
    (hb : b = 0 ∨ b = 1 ∨ b = 5)
    (hy : ∃ y : V, y ∉ Submodule.span (ZMod p) {x} ∧ ∀ c, c ≠ b → α c y = 0) : b = 1 := by
  obtain rfl : p = 3 := F.p3
  classical
  obtain ⟨y, hyx, hyc⟩ := hy
  set T : V →ₗ[ZMod 3] (Fin 6 → ZMod 3) := LinearMap.pi α with hT
  have hT_apply : ∀ v i, T v i = α i v := fun v i => LinearMap.pi_apply α v i
  have hker_le : T.ker ≤ Submodule.span (ZMod 3) {x} := by
    intro v hv
    rw [LinearMap.mem_ker] at hv
    exact F.fix v (fun i => by
      have := congrFun hv i
      rwa [hT_apply] at this)
  have hspan_le : Submodule.span (ZMod 3) {x} ≤ T.ker := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    show T x = 0
    funext i
    rw [hT_apply]
    exact F.x_ker i
  have hker : T.ker = Submodule.span (ZMod 3) {x} := le_antisymm hker_le hspan_le
  have hx1 : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {x}) = 1 := by
    simpa using finrank_span_singleton (K := ZMod 3) (v := x) F.x_ne
  have hkerfin : Module.finrank (ZMod 3) T.ker = 1 := by rw [hker, hx1]
  have hrank : Module.finrank (ZMod 3) T.range = 5 := by
    have := LinearMap.finrank_range_add_finrank_ker T
    rw [hkerfin, hdim] at this
    omega
  obtain ⟨-, hxnot, hHfin⟩ := ggDepE_relation (p := 3) F
  let H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h)
  have hHfin' : Module.finrank (ZMod 3) H = 5 := hHfin
  have hdisj : H ⊓ Submodule.span (ZMod 3) {x} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hvH, hvx⟩ := hv
    rw [Submodule.mem_span_singleton] at hvx
    obtain ⟨a, ha⟩ := hvx
    by_cases ha0 : a = 0
    · rw [← ha, ha0, zero_smul]
    · exfalso
      apply hxnot
      have hxv : x = a⁻¹ • v := by rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [hxv]
      exact Submodule.smul_mem H a⁻¹ hvH
  let T₀ : H →ₗ[ZMod 3] (Fin 6 → ZMod 3) := T.comp H.subtype
  have hT₀_ker : T₀.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    have hv' : (v : V) ∈ T.ker := by rw [LinearMap.mem_ker]; exact hv
    have hmem : (v : V) ∈ H ⊓ T.ker := ⟨v.2, hv'⟩
    rw [hker, hdisj] at hmem
    exact Subtype.ext hmem
  have hT₀_range : Module.finrank (ZMod 3) T₀.range = 5 := by
    have := LinearMap.finrank_range_add_finrank_ker T₀
    rw [hT₀_ker, finrank_bot, add_zero, hHfin'] at this
    exact this
  have hT₀_range_eq : T₀.range = Submodule.map T H := by
    ext w
    rw [LinearMap.mem_range, Submodule.mem_map]
    constructor
    · rintro ⟨v, rfl⟩; exact ⟨v, v.2, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨⟨v, hv⟩, rfl⟩
  have hmap_le : Submodule.map T H ≤ T.range := by
    intro w hw
    rw [Submodule.mem_map] at hw
    obtain ⟨v, -, rfl⟩ := hw
    exact ⟨v, rfl⟩
  have hmap_eq : Submodule.map T H = T.range :=
    Submodule.eq_of_le_of_finrank_eq hmap_le (by rw [← hT₀_range_eq, hT₀_range, hrank])
  have he_b : (Pi.single b (1 : ZMod 3)) ∈ T.range := by
    have hTη : T y = α b y • Pi.single b 1 := by
      funext i
      rw [hT_apply]
      by_cases hi : i = b
      · subst hi; rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      · rw [hyc i hi, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]
    have hηne : α b y ≠ 0 := by
      intro h0
      have hyker : y ∈ T.ker := by
        rw [LinearMap.mem_ker]
        funext i
        rw [hT_apply]
        by_cases hi : i = b
        · subst hi; exact h0
        · exact hyc i hi
      exact hyx (hker_le hyker)
    refine ⟨(α b y)⁻¹ • y, ?_⟩
    rw [map_smul, hTη, smul_smul, inv_mul_cancel₀ hηne, one_smul]
  have he_b' : (Pi.single b (1 : ZMod 3)) ∈ Submodule.map T H := by
    rw [hmap_eq]; exact he_b
  obtain ⟨w, hwH, hw⟩ := he_b'
  change w ∈ Submodule.span (ZMod 3) (Set.range h) at hwH
  rw [Submodule.mem_span_range_iff_exists_fun] at hwH
  obtain ⟨a, ha⟩ := hwH
  have heq : ∀ i : Fin 6, (∑ j, (CartanMatrix.E 6 i j : ZMod 3) * a j) =
      (Pi.single b (1 : ZMod 3) : Fin 6 → ZMod 3) i := by
    intro i
    rw [← congrFun hw i, hT_apply, ← ha, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, F.pair]
    push_cast
    ring
  have hk_b : lr7d6_k b = 0 := by
    have hksum : ∑ i : Fin 6, lr7d6_k i * (∑ j, (CartanMatrix.E 6 i j : ZMod 3) * a j) =
        lr7d6_k b := by
      calc ∑ i : Fin 6, lr7d6_k i * (∑ j, (CartanMatrix.E 6 i j : ZMod 3) * a j)
          = ∑ i : Fin 6, lr7d6_k i *
              (Pi.single b (1 : ZMod 3) : Fin 6 → ZMod 3) i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [heq i]
        _ = lr7d6_k b := by
            rw [Finset.sum_eq_single b]
            · simp
            · intro i _ hi; rw [Pi.single_eq_of_ne hi, mul_zero]
            · intro hbnot; exact absurd (Finset.mem_univ b) hbnot
    rw [← hksum]
    calc ∑ i : Fin 6, lr7d6_k i * (∑ j, (CartanMatrix.E 6 i j : ZMod 3) * a j)
        = ∑ i, ∑ j, lr7d6_k i * ((CartanMatrix.E 6 i j : ZMod 3) * a j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ j, ∑ i, lr7d6_k i * ((CartanMatrix.E 6 i j : ZMod 3) * a j) := Finset.sum_comm
      _ = ∑ j, (∑ i, lr7d6_k i * (CartanMatrix.E 6 i j : ZMod 3)) * a j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = ∑ j, (∑ i, (CartanMatrix.E 6 j i : ZMod 3) * lr7d6_k i) * a j := by
          refine Finset.sum_congr rfl fun j _ => congrArg (· * a j) ?_
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [lr7d6_E6_symm i j]
          ring
      _ = ∑ j, (0 : ZMod 3) * a j := by
          refine Finset.sum_congr rfl fun j _ => congrArg (· * a j) ?_
          exact lr7d6_E6_kernel j
      _ = 0 := by simp
  exact lr7d6_pos_fact hb hk_b

theorem ggDepE_K_type_of_dep {p : ℕ} [Fact p.Prime] (hp3 : p = 3) {ι : Type} [Fintype ι]
    [DecidableEq ι] (hcard : Fintype.card ι = 6) {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (h : ι → V) (α : ι → Module.Dual (ZMod p) V)
    (hP : ∀ i j, α i (h j) = (C i j : ZMod p)) (hdep : ¬ LinearIndependent (ZMod p) h) :
    GGIsTypeE6 M := by
  have hzero : ((C.det : ℤ) : ZMod p) = 0 := l05nL3_det_cast_eq_zero h α C hP hdep
  have hdvd : (p : ℤ) ∣ C.det := (ZMod.intCast_zmod_eq_zero_iff_dvd C.det p).1 hzero
  have hp2 : p ≠ 2 := by rw [hp3]; norm_num
  rcases l05nL3_det_of_weyl hM hC with hA | ⟨hE6, hdet3⟩ | hdet1 | hdet2 | hdet4
  · obtain ⟨n, e, hn1, hML⟩ := hA
    have hn : n = 6 := by
      have := Fintype.card_congr e
      rwa [Fintype.card_fin, hcard] at this
    subst hn
    have hC' : GGIntCartan ((CoxeterMatrix.A 6).reindex e) C := hML ▸ hC
    have hdet : C.det = 7 := by
      rw [l05nL3_det_eq_of_reindex (ggIntCartan_A 6) (ggAtMostOneMultipleEdge_A 6) e hC',
        CartanMatrix.A_det]
      norm_num
    rw [hdet, hp3] at hdvd
    norm_num at hdvd
  · exact hE6
  · exact absurd hdvd (l05nL3_not_dvd_one_two_four Fact.out hp2 (Or.inl hdet1))
  · exact absurd hdvd (l05nL3_not_dvd_one_two_four Fact.out hp2 (Or.inr (Or.inl hdet2)))
  · exact absurd hdvd (l05nL3_not_dvd_one_two_four Fact.out hp2 (Or.inr (Or.inr hdet4)))

theorem ggDepE_dim6_shape (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hdat : GGResLeviDatum p Bs L J K ggSelDep ggTypLE6) (hcard : Nat.card Bs = 3 ^ 6)
    (hp3 : p = 3) : GGResLeviDatum p Bs L J K ggSelDep ggTypLKE6 := by
  obtain rfl : p = 3 := hp3
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hWL, hCL, hWK, hCK, htyp, hφ, hrefl, hL, hK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩,
    hAL, hAK, hdel, hJ⟩ := hdat
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hcardV : Nat.card V = 3 ^ 6 := (card_eq_of_ggLin ι).symm.trans hcard
  have hdim : Module.finrank (ZMod 3) V = 6 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod, hcardV] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  obtain ⟨e, hbe, hCartan, F⟩ :=
    ggDepE_frame_of_config hFix (rfl : 3 = 3) hH hxBs hCL htyp hdel hφ hL hsel hAL
  have hαL : ∀ c : Λ, α (some c) (h (some c)) = 2 := by
    intro c
    have h1 := hL c c
    rw [hCL.1 c] at h1
    simpa using h1
  obtain ⟨y', hy'x, hy'α⟩ := ggDepA_y_fixed hp2 hH hxBs hφ hαL hJ
  set b' : Fin 6 := e.symm b with hb'def
  have hb' : b' = 0 ∨ b' = 1 ∨ b' = 5 := by rw [hb'def]; exact hbe
  let h' : Fin 6 → V := fun i => h (some (e i))
  let α' : Fin 6 → Module.Dual (ZMod 3) V := fun i => α (some (e i))
  let x' : V := ι (Additive.ofMul ⟨x, hxBs⟩)
  have hF : GGDepEFrame 3 h' α' x' := F
  have hy : ∃ y : V, y ∉ Submodule.span (ZMod 3) {x'} ∧ ∀ c : Fin 6, c ≠ b' → α' c y = 0 := by
    refine ⟨y', hy'x, ?_⟩
    intro c hc
    exact hy'α (e c) (fun hec => hc (by rw [hb'def, ← hec, Equiv.symm_apply_apply]))
  have hb1 : b' = 1 := ggDepE_dim6_pos hF hdim b' hb' hy
  have hrel : ∑ i : Fin 6, (lr7d6_kN i : ZMod 3) • h' i = 0 := by
    obtain ⟨hrel, -, -⟩ := ggDepE_relation hF
    simpa only [lr7d6_kN] using hrel
  let e' : {i : Fin 6 // i ≠ b'} ≃ {j : Λ // j ≠ b} :=
    { toFun := fun i => ⟨e i.1, fun hh => i.2 (by
        rw [← Equiv.symm_apply_apply e i.1, hh, hb'def])⟩
      invFun := fun j => ⟨e.symm j.1, fun hh => j.2 (by
        have h2 : e (e.symm j.1) = e b' := by rw [hh]
        rwa [Equiv.apply_symm_apply, hb'def, Equiv.apply_symm_apply] at h2)⟩
      left_inv := fun i => Subtype.ext (Equiv.symm_apply_apply e i.1)
      right_inv := fun j => Subtype.ext (Equiv.apply_symm_apply e j.1) }
  have hsub0 : ∑ i : {i : Fin 6 // i ≠ b'}, (lr7d6_kN i.1 : ZMod 3) • h' i.1 = 0 := by
    have hpne : ∀ x ∈ (Finset.univ : Finset (Fin 6)),
        ((lr7d6_kN x : ZMod 3) • h' x) ≠ 0 → x ≠ b' := by
      intro x _ hx hxb
      apply hx
      rw [hxb, hb1]
      simp [lr7d6_kN]
    have hfilt : (Finset.univ.filter (fun i : Fin 6 => i ≠ b')).sum
        (fun x => (lr7d6_kN x : ZMod 3) • h' x) = 0 := by
      rw [Finset.sum_filter_of_ne hpne]
      simpa using hrel
    rw [Finset.sum_subtype (s := Finset.univ.filter (fun i : Fin 6 => i ≠ b'))
      (p := fun i : Fin 6 => i ≠ b') (h := fun x => by simp)
      (f := fun i => (lr7d6_kN i : ZMod 3) • h' i)] at hfilt
    exact hfilt
  have hsub : ∑ j : {j : Λ // j ≠ b}, (lr7d6_kN (e'.symm j).1 : ZMod 3) • h (some j.1) = 0 := by
    have h1 : ∑ i : {i : Fin 6 // i ≠ b'}, (lr7d6_kN i.1 : ZMod 3) • h' i.1 =
        ∑ j : {j : Λ // j ≠ b}, (lr7d6_kN (e'.symm j).1 : ZMod 3) • h (some j.1) := by
      refine Fintype.sum_equiv e'
        (fun i : {i : Fin 6 // i ≠ b'} => (lr7d6_kN i.1 : ZMod 3) • h' i.1)
        (fun j : {j : Λ // j ≠ b} => (lr7d6_kN (e'.symm j).1 : ZMod 3) • h (some j.1))
        (fun i => ?_)
      rw [Equiv.symm_apply_apply e' i]
      rfl
    rw [← h1]
    exact hsub0
  have hsubdep : ¬ LinearIndependent (ZMod 3) (fun j : {j : Λ // j ≠ b} => h (some j.1)) := by
    have he0 : e 0 ≠ b := by
      intro h0
      have hzero : (0 : Fin 6) = b' := by rw [hb'def, ← h0, Equiv.symm_apply_apply]
      rw [hb1] at hzero
      exact absurd hzero (by decide)
    let j0 : {j : Λ // j ≠ b} := ⟨e 0, he0⟩
    have hc0 : (lr7d6_kN (e'.symm j0).1 : ZMod 3) ≠ 0 := by
      have h0 : (e'.symm j0).1 = 0 := Equiv.symm_apply_apply e 0
      rw [h0]
      change (1 : ZMod 3) ≠ 0
      exact one_ne_zero
    rw [Fintype.not_linearIndependent_iff]
    exact ⟨fun j => (lr7d6_kN (e'.symm j).1 : ZMod 3), hsub, j0, hc0⟩
  have hoptdep : ¬ LinearIndependent (ZMod 3)
      (fun o : Option {j : Λ // j ≠ b} => h (o.map Subtype.val)) := by
    intro hLI
    exact hsubdep (hLI.comp (some : {j : Λ // j ≠ b} → Option {j : Λ // j ≠ b})
      (Option.some_injective _))
  have hcardΛ : Fintype.card Λ = 6 := by
    have := Fintype.card_congr e.symm
    simpa using this
  have hcardι : Fintype.card (Option {j : Λ // j ≠ b}) = 6 := by
    rw [Fintype.card_congr (Equiv.optionSubtypeNe b), hcardΛ]
  have hE6K : GGIsTypeE6 MK :=
    ggDepE_K_type_of_dep (rfl : 3 = 3) hcardι hWK hCK (fun o => h (o.map Subtype.val))
      (fun o => α (o.map Subtype.val)) hK hoptdep
  exact ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hWL, hCL, hWK, hCK, ⟨htyp, hE6K⟩, hφ, hrefl, hL, hK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hAL, hAK, hdel, hJ⟩

end CFSG.StandardType

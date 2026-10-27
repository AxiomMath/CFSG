module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open Matrix
open scoped commutatorElement

@[expose] def tSL (K : Type) [CommRing K] : SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal ![-1, -1, 1], by simp [det_diagonal, Fin.prod_univ_three]⟩

theorem isConj_tSL {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {g : SpecialLinearGroup (Fin 3) K} (hg : orderOf g = 2) : IsConj (tSL K) g := by
  classical
  have hneg1 : (-1 : K) ≠ 1 := fun h1 => h2 (by linear_combination -h1)
  set A : Matrix (Fin 3) (Fin 3) K := (g : Matrix (Fin 3) (Fin 3) K) with hA
  set a := Matrix.toLin' A with ha
  have hg2 : g * g = 1 := by rw [← sq, ← hg, pow_orderOf_eq_one]
  have hAA : A * A = 1 := by
    have := congrArg (fun x : SpecialLinearGroup (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hg2
    simpa using this
  have haa : ∀ y, a (a y) = y := fun y => by
    rw [ha, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hAA,
      Matrix.one_mulVec]
  have hdet : LinearMap.det a = 1 := by
    rw [ha, LinearMap.det_toLin']
    exact g.2
  have hne : ∃ y, a y ≠ y := by
    by_contra hcon
    push Not at hcon
    have hg1 : g = 1 := by
      apply Subtype.ext
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun y => ?_
      change a y = _
      rw [hcon y]
      simp
    rw [hg1, orderOf_one] at hg
    exact absurd hg (by norm_num)
  set Vp : Submodule K (Fin 3 → K) := LinearMap.ker (a - LinearMap.id) with hVp
  set Vm : Submodule K (Fin 3 → K) := LinearMap.ker (a + LinearMap.id) with hVm
  have hmemVp : ∀ y, y ∈ Vp ↔ a y = y := fun y => by
    rw [hVp, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  have hmemVm : ∀ y, y ∈ Vm ↔ a y = -y := fun y => by
    rw [hVm, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]
  have hyp : ∀ y, (2 : K)⁻¹ • (y + a y) ∈ Vp := fun y => by
    rw [hmemVp, map_smul, map_add, haa, add_comm]
  have hym : ∀ y, (2 : K)⁻¹ • (y - a y) ∈ Vm := fun y => by
    rw [hmemVm, map_smul, map_sub, haa, ← smul_neg, neg_sub]
  have hsum : ∀ y, y = (2 : K)⁻¹ • (y + a y) + (2 : K)⁻¹ • (y - a y) := fun y => by
    rw [← smul_add, show y + a y + (y - a y) = (2 : K) • y by rw [two_smul]; abel, smul_smul,
      inv_mul_cancel₀ h2, one_smul]
  have hinf : Vp ⊓ Vm = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have h1 := (hmemVp y).mp hy.1
    have h3 := (hmemVm y).mp hy.2
    rw [Submodule.mem_bot]
    have h4 : (2 : K) • y = 0 := by rw [two_smul]; nth_rewrite 1 [← h1]; rw [h3, neg_add_cancel]
    exact (smul_eq_zero.mp h4).resolve_left h2
  have hsup : Vp ⊔ Vm = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [hsum y]
    exact Submodule.add_mem_sup (hyp y) (hym y)
  have hcompl : IsCompl Vp Vm := ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
  have hdim : Module.finrank K Vp + Module.finrank K Vm = 3 := by
    rw [Submodule.finrank_add_eq_of_isCompl hcompl, Module.finrank_fin_fun]
  set e := Submodule.prodEquivOfIsCompl Vp Vm hcompl with he
  have hconj : a = (e : (Vp × Vm) →ₗ[K] (Fin 3 → K)) ∘ₗ
      LinearMap.prodMap LinearMap.id (-LinearMap.id) ∘ₗ
        (e.symm : (Fin 3 → K) →ₗ[K] (Vp × Vm)) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
      LinearMap.neg_apply, LinearMap.id_apply, he, Submodule.coe_prodEquivOfIsCompl',
      Submodule.coe_prodEquivOfIsCompl', map_add, (hmemVp _).mp y.1.2, (hmemVm _).mp y.2.2]
    rfl
  have hdetm : LinearMap.det a = (-1) ^ Module.finrank K Vm := by
    rw [hconj, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, one_mul,
      ← neg_one_smul K (LinearMap.id : Vm →ₗ[K] Vm), LinearMap.det_smul, LinearMap.det_id,
      mul_one]
  have heven : Even (Module.finrank K Vm) := by
    rw [hdet] at hdetm
    exact (neg_one_pow_eq_one_iff_even hneg1).mp hdetm.symm
  have hVm0 : Module.finrank K Vm ≠ 0 := by
    intro h0
    obtain ⟨y, hy⟩ := hne
    have hm := hym y
    rw [Submodule.finrank_eq_zero.mp h0, Submodule.mem_bot] at hm
    have : y - a y = 0 := (smul_eq_zero.mp hm).resolve_left (inv_ne_zero h2)
    exact hy (sub_eq_zero.mp this).symm
  have hm2 : Module.finrank K Vm = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hp1 : Module.finrank K Vp = 1 := by omega
  let bp := Module.finBasisOfFinrankEq K Vp hp1
  let bm := Module.finBasisOfFinrankEq K Vm hm2
  set v : Fin 3 → (Fin 3 → K) :=
    ![(bm 0 : Fin 3 → K), (bm 1 : Fin 3 → K), (bp 0 : Fin 3 → K)] with hv
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_three] at hc
    have hxm : ((c 0 • bm 0 + c 1 • bm 1 : Vm) : Fin 3 → K) =
        -((c 2 • bp 0 : Vp) : Fin 3 → K) := by
      rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul]
      exact eq_neg_of_add_eq_zero_left hc
    have hxm0 : (c 0 • bm 0 + c 1 • bm 1 : Vm) = 0 := by
      have h1 : ((c 0 • bm 0 + c 1 • bm 1 : Vm) : Fin 3 → K) ∈ Vp ⊓ Vm :=
        ⟨by rw [hxm]; exact Vp.neg_mem (c 2 • bp 0).2, (c 0 • bm 0 + c 1 • bm 1).2⟩
      rw [hinf, Submodule.mem_bot] at h1
      exact Subtype.ext h1
    have hxp0 : (c 2 • bp 0 : Vp) = 0 := by
      apply Subtype.ext
      have h1 := hxm
      rw [hxm0, Submodule.coe_zero] at h1
      rw [Submodule.coe_zero]
      exact neg_eq_zero.mp h1.symm
    have hm := Fintype.linearIndependent_iff.mp bm.linearIndependent ![c 0, c 1]
      (by rw [Fin.sum_univ_two]; simpa using hxm0)
    have hp := Fintype.linearIndependent_iff.mp bp.linearIndependent ![c 2]
      (by simpa using hxp0)
    intro i
    fin_cases i
    · simpa using hm 0
    · simpa using hm 1
    · simpa using hp 0
  set u : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => v j i with hu
  have huU : IsUnit u := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    convert hli using 1
    funext j i
    rfl
  have hd0 : u.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det u).mp huU).ne_zero
  have hav : ∀ k, A *ᵥ v k = (![-1, -1, 1] : Fin 3 → K) k • v k := by
    intro k
    rw [← Matrix.toLin'_apply, ← ha]
    fin_cases k
    · simpa [hv] using (hmemVm _).mp (bm 0).2
    · simpa [hv] using (hmemVm _).mp (bm 1).2
    · simpa [hv] using (hmemVp _).mp (bp 0).2
  have hu2 : A * u = u * diagonal ![-1, -1, 1] := by
    ext i k
    rw [mul_diagonal]
    change ∑ l, A i l * v k l = v k i * ![-1, -1, 1] k
    rw [mul_comm]
    exact congrFun (hav k) i
  set d := u.det with hd
  set D : Matrix (Fin 3) (Fin 3) K := diagonal ![d⁻¹, 1, 1] with hD
  set u' := u * D with hu'
  have hdet' : u'.det = 1 := by
    rw [hu', det_mul, hD, det_diagonal, Fin.prod_univ_three, ← hd]
    simp [hd0]
  have hu2' : A * u' = u' * diagonal ![-1, -1, 1] := by
    rw [hu', ← Matrix.mul_assoc, hu2, Matrix.mul_assoc, Matrix.mul_assoc]
    congr 1
    rw [hD, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [isConj_iff]
  refine ⟨⟨u', hdet'⟩, mul_inv_eq_iff_eq_mul.mpr ?_⟩
  ext i j
  exact congrFun (congrFun hu2'.symm i) j

@[expose] def IsBlk5 (M : Matrix (Fin 3) (Fin 3) (ZMod 5)) : Prop :=
  M 0 2 = 0 ∧ M 1 2 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0

theorem IsBlk5.mul {M N : Matrix (Fin 3) (Fin 3) (ZMod 5)} (hM : IsBlk5 M) (hN : IsBlk5 N) :
    IsBlk5 (M * N) ∧ (M * N) 2 2 = M 2 2 * N 2 2 := by
  obtain ⟨a, b, c, d⟩ := hM
  obtain ⟨a', b', c', d'⟩ := hN
  simp [IsBlk5, Matrix.mul_apply, Fin.sum_univ_three, a, b, c, d, a', b', c', d']

theorem isBlk5_inv {g : SpecialLinearGroup (Fin 3) (ZMod 5)}
    (hg : IsBlk5 (g : Matrix (Fin 3) (Fin 3) (ZMod 5))) :
    IsBlk5 ((g⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) ∧
      ((g⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 *
        (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 = 1 := by
  have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 5)).det = 1 := g.2
  have hinv : ((g⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) =
      adjugate (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) := Matrix.SpecialLinearGroup.coe_inv g
  obtain ⟨a, b, c, d⟩ := hg
  rw [Matrix.det_fin_three, a, b, c, d] at hdet
  rw [hinv]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [Matrix.adjugate_fin_three, a, b, c, d]
  linear_combination hdet

theorem isBlk5_of_comm {g : SpecialLinearGroup (Fin 3) (ZMod 5)}
    (h : g * tSL (ZMod 5) = tSL (ZMod 5) * g) : IsBlk5 (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) := by
  have h1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) * diagonal ![-1, -1, 1] =
      diagonal ![-1, -1, 1] * (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) :=
    congrArg (fun x : SpecialLinearGroup (Fin 3) (ZMod 5) =>
      (x : Matrix (Fin 3) (Fin 3) (ZMod 5))) h
  have k1 : ∀ m : ZMod 5, m = -m → m = 0 := by decide
  refine ⟨k1 _ ?_, k1 _ ?_, k1 _ ?_, k1 _ ?_⟩
  · have := congrFun (congrFun h1 0) 2
    simpa [mul_diagonal, diagonal_mul] using this
  · have := congrFun (congrFun h1 1) 2
    simpa [mul_diagonal, diagonal_mul] using this
  · have := congrFun (congrFun h1 2) 0
    simpa [mul_diagonal, diagonal_mul] using this.symm
  · have := congrFun (congrFun h1 2) 1
    simpa [mul_diagonal, diagonal_mul] using this.symm

@[expose] def Ysl : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 5)) where
  carrier := {g | IsBlk5 (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 = 1}
  mul_mem' {a b} ha hb := by
    obtain ⟨h1, h2⟩ := IsBlk5.mul ha.1 hb.1
    refine ⟨h1, ?_⟩
    show ((a : Matrix (Fin 3) (Fin 3) (ZMod 5)) * (b : Matrix (Fin 3) (Fin 3) (ZMod 5))) 2 2 = 1
    rw [h2, ha.2, hb.2, one_mul]
  one_mem' := ⟨by simp [IsBlk5], by simp⟩
  inv_mem' {a} ha := by
    obtain ⟨h1, h2⟩ := isBlk5_inv ha.1
    exact ⟨h1, by rwa [ha.2, mul_one] at h2⟩

theorem card_detPairs :
    Nat.card {p : ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5 // p.1 * p.2.2.2 - p.2.1 * p.2.2.1 = 1} =
      120 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_Ysl : Nat.card Ysl ≤ 120 := by
  have hrow : ∀ g ∈ Ysl, (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 0 *
      (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 1 - (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 1 *
        (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 0 = 1 := by
    intro g hg
    obtain ⟨⟨a, b, c, d⟩, e⟩ := hg
    have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 5)).det = 1 := g.2
    rw [Matrix.det_fin_three, a, b, c, d, e] at hdet
    linear_combination hdet
  let f : Ysl → {p : ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5 // p.1 * p.2.2.2 - p.2.1 * p.2.2.1 = 1} :=
    fun g => ⟨((g : SpecialLinearGroup (Fin 3) (ZMod 5)) 0 0,
      (g : SpecialLinearGroup (Fin 3) (ZMod 5)) 0 1, (g : SpecialLinearGroup (Fin 3) (ZMod 5)) 1 0,
      (g : SpecialLinearGroup (Fin 3) (ZMod 5)) 1 1), hrow _ g.2⟩
  have hf : Function.Injective f := by
    intro g g' h
    have h1 := congrArg (fun p => p.1.1) h
    have h2 := congrArg (fun p => p.1.2.1) h
    have h3 := congrArg (fun p => p.1.2.2.1) h
    have h4 := congrArg (fun p => p.1.2.2.2) h
    simp only [f] at h1 h2 h3 h4
    obtain ⟨⟨a, b, c, d⟩, e⟩ := g.2
    obtain ⟨⟨a', b', c', d'⟩, e'⟩ := g'.2
    apply Subtype.ext
    apply Subtype.ext
    ext r s
    fin_cases r <;> fin_cases s
    · exact h1
    · exact h2
    · exact a.trans a'.symm
    · exact h3
    · exact h4
    · exact b.trans b'.symm
    · exact c.trans c'.symm
    · exact d.trans d'.symm
    · exact e.trans e'.symm
  calc Nat.card Ysl
      ≤ Nat.card {p : ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5 // p.1 * p.2.2.2 - p.2.1 * p.2.2.1 = 1} :=
        Nat.card_le_card_of_injective f hf
    _ = 120 := card_detPairs

theorem card_commutator_centralizer_tSL :
    Nat.card ↥⁅Subgroup.centralizer {tSL (ZMod 5)}, Subgroup.centralizer {tSL (ZMod 5)}⁆ ≤
      120 := by
  have hle : ⁅Subgroup.centralizer {tSL (ZMod 5)}, Subgroup.centralizer {tSL (ZMod 5)}⁆ ≤
      Ysl := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have bx := isBlk5_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hx)
    have bh := isBlk5_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hy)
    obtain ⟨bx', ex⟩ := isBlk5_inv bx
    obtain ⟨bh', eh⟩ := isBlk5_inv bh
    have e : ((⁅x, y⁆ : SpecialLinearGroup (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) =
        (x : Matrix (Fin 3) (Fin 3) (ZMod 5)) * (y : Matrix (Fin 3) (Fin 3) (ZMod 5)) *
          ((x⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) *
          ((y⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) := rfl
    show IsBlk5 ((⁅x, y⁆ : SpecialLinearGroup (Fin 3) (ZMod 5)) :
        Matrix (Fin 3) (Fin 3) (ZMod 5)) ∧
      ((⁅x, y⁆ : SpecialLinearGroup (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 = 1
    rw [e]
    refine ⟨?_, ?_⟩
    · exact ((bx.mul bh).1.mul bx').1.mul bh' |>.1
    · rw [((bx.mul bh).1.mul bx').1.mul bh' |>.2, ((bx.mul bh).1.mul bx').2, (bx.mul bh).2]
      calc (x : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 * (y : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 *
            ((x⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 *
            ((y⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 =
          (((x⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 *
            (x : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2) *
          (((y⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 5)) : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2 *
            (y : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 2) := by ring
        _ = 1 := by rw [ex, eh, one_mul]
  exact (Subgroup.card_le_of_le hle).trans card_Ysl

theorem card_commutator_centralizer_le_of_injective {X Y : Type} [Group X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Injective f) (x : X) :
    Nat.card ↥⁅Subgroup.centralizer ({x} : Set X), Subgroup.centralizer ({x} : Set X)⁆ ≤
      Nat.card ↥⁅Subgroup.centralizer ({f x} : Set Y), Subgroup.centralizer ({f x} : Set Y)⁆ := by
  have h1 : (Subgroup.centralizer ({x} : Set X)).map f ≤ Subgroup.centralizer ({f x} : Set Y) := by
    have := Subgroup.map_centralizer_le_centralizer_image ({x} : Set X) f
    rwa [Set.image_singleton] at this
  have h2 : (⁅Subgroup.centralizer ({x} : Set X), Subgroup.centralizer ({x} : Set X)⁆).map f ≤
      ⁅Subgroup.centralizer ({f x} : Set Y), Subgroup.centralizer ({f x} : Set Y)⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono h1 h1
  rw [← Subgroup.card_map_of_injective hf]
  exact Subgroup.card_le_of_le h2

theorem card_commutator_centralizer_le_of_isConj {X : Type} [Group X] [Finite X] {x y : X}
    (h : IsConj x y) :
    Nat.card ↥⁅Subgroup.centralizer ({y} : Set X), Subgroup.centralizer ({y} : Set X)⁆ ≤
      Nat.card ↥⁅Subgroup.centralizer ({x} : Set X), Subgroup.centralizer ({x} : Set X)⁆ := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have h1 := card_commutator_centralizer_le_of_injective (MulAut.conj c⁻¹).toMonoidHom
    (MulAut.conj c⁻¹).injective y
  have h2 : (MulAut.conj c⁻¹).toMonoidHom y = x := by
    rw [← hc]
    simp [mul_assoc]
  rwa [h2] at h1

theorem card_commutator_centralizer_sl35 {w : SpecialLinearGroup (Fin 3) (ZMod 5)}
    (hw : orderOf w = 2) :
    Nat.card ↥⁅Subgroup.centralizer ({w} : Set (SpecialLinearGroup (Fin 3) (ZMod 5))),
      Subgroup.centralizer ({w} : Set (SpecialLinearGroup (Fin 3) (ZMod 5)))⁆ ≤ 120 := by
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact (card_commutator_centralizer_le_of_isConj (isConj_tSL h2 hw)).trans
    card_commutator_centralizer_tSL

end CFSG.Quasithin.H13.NQCat.A314D

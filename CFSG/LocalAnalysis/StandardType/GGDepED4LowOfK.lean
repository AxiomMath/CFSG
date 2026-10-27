module

public import CFSG.LocalAnalysis.StandardType.GGDepED4LowDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4UpOf
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLFinite
public import CFSG.LocalAnalysis.StandardType.GGRowKFrameDim

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nLKE_exists_psi {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {Λ Λa : Type} (φ : Λ ⊕ Λa → MulAut ↥Bs) :
    ∀ g ∈ Subgroup.closure (Set.range fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o)),
      ∃ ψ ∈ Subgroup.closure (Set.range φ), ggLin (p := p) ι ψ = g := by
  intro g hg
  have himg : Set.range (fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o)) =
      (ggLin (p := p) ι) '' Set.range φ := by
    ext z; constructor
    · rintro ⟨o, rfl⟩; exact ⟨φ o, ⟨o, rfl⟩, rfl⟩
    · rintro ⟨ψ, ⟨o, rfl⟩, rfl⟩; exact ⟨o, rfl⟩
  rw [himg, ← MonoidHom.map_closure] at hg
  exact Subgroup.mem_map.mp hg

private theorem l05nLKE_sup_eq {G : Type} [Group G] {Bs L K : Subgroup G}
    {Λ Λa : Type} {b₁ b₂ : Λ} (φ : Λ ⊕ Λa → MulAut ↥Bs)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) ∪
        Set.range fun a : Λa => φ (Sum.inr a))) :
    ggAutomizer L Bs ⊔ ggAutomizer K Bs = Subgroup.closure (Set.range φ) := by
  rw [hAL, hAK, ← Subgroup.closure_union]
  congr 1
  ext z; constructor
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inl j.1, rfl⟩
    · exact ⟨Sum.inr a, rfl⟩
  · rintro ⟨o, rfl⟩
    cases o with
    | inl i => exact Or.inl ⟨i, rfl⟩
    | inr a => exact Or.inr (Or.inr ⟨a, rfl⟩)

private theorem l05nLK_cartan_of_reindex {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (e : Fin 6 ≃ Λ)
    (hCL : GGIntCartan ML CL) (hML : ML = CoxeterMatrix.E₆.reindex e) :
    ∀ i j : Fin 6, CL (e i) (e j) = CartanMatrix.E 6 i j := by
  intro i j
  by_cases hij : i = j
  · subst hij; rw [hCL.1]; fin_cases i <;> decide
  · have heij : e i ≠ e j := fun h => hij (e.injective h)
    have h₂ : GGIntCartan ML (Matrix.reindex e e (CartanMatrix.E 6)) := by
      rw [hML]; exact GGIntCartan.reindex e ggIntCartan_E₆
    have hMle : ML.M (e i) (e j) ≤ 3 := by
      rw [hML, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      fin_cases i <;> fin_cases j <;> decide
    have h1 := (hCL.pair h₂ heij).2 hMle
    rw [h1.1]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

private theorem l05nLK_cartanE_eq (i j : Fin 6) :
    E6Dep.cartanE6 i j = (((CartanMatrix.E 6 i j : ℤ) : ZMod 3)) := by
  rw [CartanMatrix.E_six_eq]
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem l05nLK_alpha_y {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hy : y ∈ Bs)
    {Λ : Type} {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod 3) V}
    (hφ : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α i (h j) = (CK i j : ZMod 3))
    (hCK : GGIntCartan MK CK)
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ)) :
    ∀ j : Λ, α j (ι (Additive.ofMul ⟨y, hy⟩)) = 0 := by
  intro j
  have hfix := ggRC_automizer_fixes_y hy hH.2.2.2.2.1.1.2.2.2.1
  have hmem : φ j ∈ ggAutomizer K Bs := by
    rw [hAK]; exact Subgroup.subset_closure ⟨j, rfl⟩
  have hlin : ggLin (p := 3) ι (φ j) (ι (Additive.ofMul ⟨y, hy⟩)) =
      ι (Additive.ofMul ⟨y, hy⟩) :=
    (ggLin_fix_iff (p := 3) ι (φ j) ⟨y, hy⟩).mp (hfix (φ j) hmem)
  have h1 := hφ j (ι (Additive.ofMul ⟨y, hy⟩))
  rw [hlin] at h1
  have h2 : α j (ι (Additive.ofMul ⟨y, hy⟩)) • h j = 0 := sub_eq_self.mp h1.symm
  have h3 : α j (α j (ι (Additive.ofMul ⟨y, hy⟩)) • h j) = 0 := by rw [h2, map_zero]
  have hpair : α j (h j) = (2 : ZMod 3) := by rw [hL j j, hCK.1 j]; norm_num
  rw [map_smul, smul_eq_mul, hpair] at h3
  exact (mul_eq_zero.mp h3).resolve_right (zmod_two_ne_zero (p := 3) (by norm_num))

private theorem l05nLK_h_mem_K {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {Λ : Type} {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ}
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ)) :
    ∀ i : Λ, ((Additive.toMul (ι.symm (h i)) : ↥Bs) : G) ∈ K := by
  intro i
  obtain ⟨g, hgK, -, hgconj⟩ := (mem_ggAutomizer_iff (H := K) (φ := φ i)).mp
    (by rw [hAK]; exact Subgroup.subset_closure (Set.mem_range_self i))
  have hBsN : Bs ≤ Subgroup.normalizer (K : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn (hH.2.2.1.2 y K hH.2.2.2.2.1)
  have hαii : α i (h i) = 2 := by rw [hpair i i, hCK.1]; norm_num
  let b : ↥Bs := Additive.toMul (ι.symm ((-((2 : ZMod p)⁻¹)) • h i))
  have hbw : ι (Additive.ofMul b) = (-((2 : ZMod p)⁻¹)) • h i := by
    dsimp only [b]; rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  have hαb : α i (ι (Additive.ofMul b)) = -1 := by
    rw [hbw, map_smul, smul_eq_mul, hαii, neg_mul, inv_mul_cancel₀ (zmod_two_ne_zero hp2)]
  have h1 : ggLin (p := p) ι (φ i) (ι (Additive.ofMul b)) = ι (Additive.ofMul b) + h i := by
    have hh := hφ i (ι (Additive.ofMul b)); rw [hαb] at hh
    simpa [neg_smul, one_smul, sub_neg_eq_add] using hh
  have hhi : h i = ι (Additive.ofMul (b⁻¹ * φ i b)) := by
    rw [show ι (Additive.ofMul (b⁻¹ * φ i b)) =
        -ι (Additive.ofMul b) + ι (Additive.ofMul (φ i b)) by
          simp only [ofMul_mul, ofMul_inv, map_add, map_neg], ← ggLin_apply_ofMul (p := p), h1]
    abel
  have hmemK : ((b⁻¹ * φ i b : ↥Bs) : G) ∈ K := by
    have hbg : (b : G)⁻¹ * g * (b : G) ∈ K := by
      have hbN : (b : G) ∈ Subgroup.normalizer (K : Set G) := hBsN b.2
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbN) g).mp hgK
    have hEq : ((b⁻¹ * φ i b : ↥Bs) : G) = ((b : G)⁻¹ * g * (b : G)) * g⁻¹ := by
      change (b : G)⁻¹ * ((φ i b : ↥Bs) : G) = ((b : G)⁻¹ * g * (b : G)) * g⁻¹
      rw [hgconj b]; group
    rw [hEq]; exact K.mul_mem hbg (K.inv_mem hgK)
  rw [show (Additive.toMul (ι.symm (h i)) : ↥Bs) = b⁻¹ * φ i b by rw [hhi]; simp]
  exact hmemK

private theorem l05nLK_ker_le_one {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (hdim : Module.finrank (ZMod 3) V = 6)
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V}
    (hpair : ∀ i j, α i (h j) = (((CartanMatrix.E 6) i j : ℤ) : ZMod 3))
    {v w : V} (hv : ∀ i, α i v = 0) (hw : ∀ i, α i w = 0) (hw0 : w ≠ 0) :
    ∃ c : ZMod 3, v = c • w := by
  haveI : FiniteDimensional (ZMod 3) V :=
    FiniteDimensional.of_finrank_pos (by rw [hdim]; norm_num)
  let T : V →ₗ[ZMod 3] (Fin 6 → ZMod 3) :=
    { toFun := fun v => fun i => α i v
      map_add' := by intro v w; ext i; simp
      map_smul' := by intro a v; ext i; simp [smul_eq_mul] }
  have hkerfin : Module.finrank (ZMod 3) (LinearMap.ker T) ≤ 1 := by
    let Φ : (Fin 6 → ZMod 3) →ₗ[ZMod 3] (Fin 6 → ZMod 3) :=
      { toFun := fun c => ∑ k : Fin 6, c k • T (h k)
        map_add' := by
          intro c d
          simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := by
          intro a c
          simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, RingHom.id_apply] }
    have hkerle : LinearMap.ker Φ ≤
        Submodule.span (ZMod 3) ({E6Dep.ZL.kappa} : Set (Fin 6 → ZMod 3)) := by
      intro c hc
      have hc0 : Φ c = 0 := LinearMap.mem_ker.mp hc
      have heq : E6Dep.ZL.cartanM.mulVec c = 0 := by
        funext a
        show (E6Dep.ZL.cartanM.mulVec c) a = 0
        have hrow : (Φ c) a = 0 := by rw [hc0]; rfl
        have happ : (Φ c) a = ∑ k : Fin 6,
            c k * (((CartanMatrix.E 6) a k : ℤ) : ZMod 3) := by
          change (∑ k : Fin 6, c k • T (h k)) a = _
          rw [Finset.sum_apply]
          exact Finset.sum_congr rfl fun k _ => by
            rw [Pi.smul_apply, smul_eq_mul]
            exact congrArg (fun x => c k * x) (hpair a k)
        rw [happ] at hrow
        calc (E6Dep.ZL.cartanM.mulVec c) a
            = ∑ k : Fin 6, E6Dep.cartanE6 a k * c k := rfl
          _ = ∑ k : Fin 6, (((CartanMatrix.E 6) a k : ℤ) : ZMod 3) * c k :=
              Finset.sum_congr rfl fun k _ => by rw [l05nLK_cartanE_eq a k]
          _ = ∑ k : Fin 6, c k * (((CartanMatrix.E 6) a k : ℤ) : ZMod 3) :=
              Finset.sum_congr rfl fun k _ => mul_comm _ _
          _ = 0 := hrow
      obtain ⟨a, ha⟩ := E6Dep.ZL.rad_eq c heq
      rw [ha]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton E6Dep.ZL.kappa))
    have hkerfinΦ : Module.finrank (ZMod 3) (LinearMap.ker Φ) ≤ 1 := by
      calc Module.finrank (ZMod 3) (LinearMap.ker Φ)
          ≤ Module.finrank (ZMod 3)
              (Submodule.span (ZMod 3) ({E6Dep.ZL.kappa} : Set (Fin 6 → ZMod 3))) :=
            Submodule.finrank_mono hkerle
        _ = 1 := finrank_span_singleton (by decide : E6Dep.ZL.kappa ≠ 0)
    have hΦrank : 5 ≤ Module.finrank (ZMod 3) (LinearMap.range Φ) := by
      have hrn := LinearMap.finrank_range_add_finrank_ker (f := Φ)
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrn
      omega
    have hrange : LinearMap.range Φ ≤ LinearMap.range T := by
      rintro x ⟨c, rfl⟩
      change (∑ k : Fin 6, c k • T (h k)) ∈ LinearMap.range T
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (LinearMap.mem_range_self T (h k))
    have hTrank : 5 ≤ Module.finrank (ZMod 3) (LinearMap.range T) :=
      le_trans hΦrank (Submodule.finrank_mono hrange)
    have hrn := LinearMap.finrank_range_add_finrank_ker (f := T)
    rw [hdim] at hrn
    omega
  have hvK : v ∈ LinearMap.ker T := by rw [LinearMap.mem_ker]; ext i; exact hv i
  have hwK : w ∈ LinearMap.ker T := by rw [LinearMap.mem_ker]; ext i; exact hw i
  by_contra hcon
  push Not at hcon
  have hli2 : LinearIndependent (ZMod 3) ![w, v] :=
    (LinearIndependent.pair_iff' hw0).mpr fun a => (hcon a).symm
  have hspan2 : Submodule.span (ZMod 3) (Set.range ![w, v]) ≤ LinearMap.ker T := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact hwK
    · exact hvK
  have h2 : (2 : ℕ) ≤ Module.finrank (ZMod 3) (LinearMap.ker T) :=
    calc (2 : ℕ) =
          Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range ![w, v])) := by
          rw [finrank_span_eq_card hli2, Fintype.card_fin]
      _ ≤ Module.finrank (ZMod 3) (LinearMap.ker T) := Submodule.finrank_mono hspan2
  omega

private theorem l05nLK_yV_ne {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hy : y ∈ Bs)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Additive ↥Bs ≃+ V} :
    ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) ≠ 0 := by
  intro h0
  have hy1 : (⟨y, hy⟩ : ↥Bs) ≠ 1 := by
    intro h1; exact ggRC_y_ne_one hH (by simpa using congrArg Subtype.val h1)
  apply hy1
  have h1 : Additive.ofMul (⟨y, hy⟩ : ↥Bs) = 0 := ι.injective (by simpa using h0)
  simpa using congrArg Additive.toMul h1

private theorem l05nLK_frame_K_dim {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hy : y ∈ Bs) (hyK : y ∉ K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (e : Fin 6 ≃ Λ) (hML : ML = CoxeterMatrix.E₆.reindex e) (hCL : GGIntCartan ML CL)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod 3) V}
    (hφ : ∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod 3))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hdim : Module.finrank (ZMod 3) V = 6) :
    GGDepEFrame 3 (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨y, hy⟩)) := by
  classical
  have hcart : ∀ i j : Fin 6, CL (e i) (e j) = CartanMatrix.E 6 i j :=
    l05nLK_cartan_of_reindex e hCL hML
  have hp6 : ∀ i j : Fin 6, α (e i) (h (e j)) = (((CartanMatrix.E 6) i j : ℤ) : ZMod 3) :=
    fun i j => by rw [hpair (e i) (e j), hcart i j]
  have hαy : ∀ j : Λ, α j (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) = 0 :=
    l05nLK_alpha_y hH hy hφ hpair hCL hAK
  have hx_ne : ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) ≠ 0 := l05nLK_yV_ne hH hy
  have hdep : ¬ LinearIndependent (ZMod 3) h := by
    intro hli
    let M : AddSubgroup V :=
      { carrier := {w | ∃ b : ↥Bs, (b : G) ∈ K ∧ ι (Additive.ofMul b) = w}
        zero_mem' := by refine ⟨1, K.one_mem, ?_⟩; rw [ofMul_one, map_zero]
        add_mem' := by
          rintro w1 w2 ⟨b1, hb1, rfl⟩ ⟨b2, hb2, rfl⟩
          exact ⟨b1 * b2, K.mul_mem hb1 hb2, by rw [ofMul_mul, map_add]⟩
        neg_mem' := by
          rintro w ⟨b, hb, rfl⟩
          exact ⟨b⁻¹, K.inv_mem hb, by rw [ofMul_inv, map_neg]⟩ }
    have hM : ∀ i : Λ, h i ∈ M := fun i =>
      ⟨Additive.toMul (ι.symm (h i)),
        l05nLK_h_mem_K (p := 3) (by norm_num) hH hCL hφ hpair hAK i,
        by rw [ofMul_toMul, AddEquiv.apply_symm_apply]⟩
    have hlie : LinearIndependent (ZMod 3) (fun i : Fin 6 => h (e i)) :=
      (linearIndependent_equiv e).mpr hli
    let kappa : Fin 6 → ZMod 3 := E6Dep.ZL.kappa
    let v : V := ∑ i : Fin 6, kappa i • h (e i)
    have hv_ne : v ≠ 0 := by
      intro hv
      have hk0 : kappa = 0 := funext fun i =>
        (Fintype.linearIndependent_iff.mp hlie) kappa (by simpa [v] using hv) i
      exact one_ne_zero
        (by simpa [kappa, E6Dep.ZL.kappa] using congrFun hk0 0 : (1 : ZMod 3) = 0)
    have hαv : ∀ k : Λ, α k v = 0 := by
      intro k
      obtain ⟨j, rfl⟩ := e.surjective k
      have hsum : α (e j) v = ∑ i : Fin 6,
          kappa i * (((CartanMatrix.E 6) j i : ℤ) : ZMod 3) := by
        change α (e j) (∑ i : Fin 6, kappa i • h (e i)) = _
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, hp6 j i]
      rw [hsum]
      have hkC : ∑ i : Fin 6, (((CartanMatrix.E 6) j i : ℤ) : ZMod 3) * kappa i = 0 := by
        have h := congrFun E6Dep.ZL.cartanM_kappa j
        have hs : (E6Dep.ZL.cartanM.mulVec kappa) j =
            ∑ i : Fin 6, (((CartanMatrix.E 6) j i : ℤ) : ZMod 3) * kappa i := by
          show (E6Dep.ZL.cartanM.mulVec kappa) j = _
          rw [show (E6Dep.ZL.cartanM.mulVec kappa) j =
              ∑ i : Fin 6, E6Dep.cartanE6 j i * kappa i from rfl]
          exact Finset.sum_congr rfl fun i _ => by rw [l05nLK_cartanE_eq j i]
        rwa [hs] at h
      calc ∑ i : Fin 6, kappa i * (((CartanMatrix.E 6) j i : ℤ) : ZMod 3)
          = ∑ i : Fin 6, (((CartanMatrix.E 6) j i : ℤ) : ZMod 3) * kappa i :=
            Finset.sum_congr rfl fun i _ => mul_comm _ _
        _ = 0 := hkC
    obtain ⟨c, hc⟩ := l05nLK_ker_le_one hdim hp6
      (fun i => hαy (e i)) (fun i => hαv (e i)) hv_ne
    have hv_mem : v ∈ M := by
      rw [show v = ∑ i : Fin 6, kappa i • h (e i) from rfl]
      refine M.sum_mem fun i _ => ?_
      rw [← ZMod.natCast_zmod_val (kappa i), Nat.cast_smul_eq_nsmul]
      exact M.nsmul_mem (hM (e i)) (kappa i).val
    have hy_mem : ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) ∈ M := by
      rw [hc, ← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
      exact M.nsmul_mem hv_mem c.val
    obtain ⟨b, hbK, hbw⟩ := hy_mem
    exact hyK (by rwa [Additive.ofMul.injective (ι.injective hbw)] at hbK)
  refine ⟨rfl, hp6, hx_ne, ?_, ?_, ?_⟩
  · intro i; exact hαy (e i)
  · intro v hv
    obtain ⟨c, hc⟩ := l05nLK_ker_le_one hdim hp6 (fun i => hv i) (fun i => hαy (e i)) hx_ne
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · intro hli
    exact hdep ((linearIndependent_equiv (R := ZMod 3) e).mp hli)

theorem ggDepED4LowCfg_of_alignedK (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hyK : y ∉ K) {k : ℕ} (hp3 : p = 3) (hCard : Nat.card ↥Bs = 3 ^ 6)
    (hHK : k = 1 → Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y →
      GGTWHLAt p Bs K y)
    (hHL : k = 1 → GGTWHLAt p Bs L x) (hA : GGDepED4Aligned p k Bs K J L) :
    GGDepED4LowCfg p k Bs K J L y x := by
  classical
  subst hp3
  obtain ⟨Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, ML, CL, MK, CK, V, hVadd, hVmod,
    ι, φ, h, α, e, hb1, hb2, hcardΛa, hML, hMLweyl, hCLcartan, hMKweyl, hCKcartan,
    hk2, hform, hrefl, hpairL, hpairK, hAL, hAK, hAJ⟩ := hA
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod 3) V := hVmod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hy : y ∈ Bs := hH.1.2.1.1 hH.2.2.2.2.1.1.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  let xV : V := ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
  let yV : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  let ΦL : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa → MulAut ↥Bs := fun o => φ (o.map Subtype.val id)
  have hAKrange : Set.range ΦL =
      Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) ∪
        Set.range (fun a : Λa => φ (Sum.inr a)) := by
    ext z; constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr a, rfl⟩
  have hAK' : ggAutomizer L Bs = Subgroup.closure (Set.range ΦL) := by rw [hAK, ← hAKrange]
  have hsup : ggAutomizer K Bs ⊔ ggAutomizer L Bs = Subgroup.closure (Set.range φ) :=
    l05nLKE_sup_eq φ hAL hAK
  have hfinrank : Module.finrank (ZMod 3) V = 6 := by
    haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
    have hVcard : Nat.card V = 3 ^ Module.finrank (ZMod 3) V := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
      rwa [Nat.card_zmod] at h
    have hcardV : Nat.card V = Nat.card ↥Bs := by
      rw [Nat.card_congr (Additive.ofMul (α := ↥Bs))]
      exact (Nat.card_congr ι.toEquiv).symm
    have heq : 3 ^ Module.finrank (ZMod 3) V = 3 ^ 6 := by rw [← hVcard, hcardV, hCard]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) heq
  have hframe : GGDepEFrame 3 (fun i : Fin 6 => h (Sum.inl (e i)))
      (fun i : Fin 6 => α (Sum.inl (e i))) xV :=
    l05nLK_frame_K_dim hH hy hyK e hML hCLcartan
      (φ := fun i : Λ => φ (Sum.inl i)) (h := fun i : Λ => h (Sum.inl i))
      (α := fun i : Λ => α (Sum.inl i))
      (fun i w => hform (Sum.inl i) w) (fun i j => hpairL i j) hAL hfinrank
  have hxker : ∀ i : Λ, α (Sum.inl i) xV = 0 := by
    intro i; simpa using hframe.x_ker (e.symm i)
  have hguard : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y :=
    ggNbr_cent_le_of_fix hp2 hy (ι := ι) (φ := fun i : Λ => φ (Sum.inl i))
      (h := fun i : Λ => h (Sum.inl i)) (α := fun i : Λ => α (Sum.inl i))
      (fun i w => hform (Sum.inl i) w)
      (fun i => by rw [hpairL i i, hCLcartan.1 i]; norm_num) hAL
      (fun v hv => hframe.fix v (fun i => hv (e i)))
  have hfixx : ∀ ψ ∈ ggAutomizer L Bs, ψ ⟨x, hx⟩ = ⟨x, hx⟩ :=
    ggRC_automizer_fixes_y hx hLx
  refine ⟨Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, MK, CK, V, hVadd, hVmod, ι, e, φ, h, α,
    xV, yV, hy, hx, rfl, rfl, ?_, hfinrank, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨hb1, hb2, hcardΛa, hMKweyl, hCKcartan, hk2, hform, hframe, hpairK, ?_, ?_, hsup,
      hAJ⟩
    · intro g hg
      obtain ⟨ψ, hψ, hψg⟩ := l05nLKE_exists_psi (p := 3) ι φ g hg
      rw [← hψg]
      exact ggTT_nt_sup hH ι (by rw [sup_comm, hsup]; exact hψ)
    · by_contra hno
      push Not at hno
      have hfixgen : ∀ o : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa, ΦL o ⟨y, hy⟩ = ⟨y, hy⟩ := by
        intro o
        apply (ggLin_fix_iff (p := 3) ι (ΦL o) (⟨y, hy⟩ : ↥Bs)).mpr
        cases o with
        | inl j =>
            show ggLin (p := 3) ι (φ (Sum.inl j.1)) xV = xV
            rw [hform (Sum.inl j.1) xV, hxker j.1, zero_smul, sub_zero]
        | inr a =>
            show ggLin (p := 3) ι (φ (Sum.inr a)) xV = xV
            rw [hform (Sum.inr a) xV, hno a, zero_smul, sub_zero]
      have hfix : ∀ ψ ∈ ggAutomizer L Bs, ψ ⟨y, hy⟩ = ⟨y, hy⟩ := by
        intro ψ hψ
        rw [hAK'] at hψ
        exact ggFixed_of_mem_closure ΦL (⟨y, hy⟩ : ↥Bs) hfixgen ψ hψ
      exact ggRK_not_fixed hFix hH hy hfix
  · intro hk1 g hg hgref hgy
    obtain ⟨ψ, hψ, hψg⟩ := l05nLKE_exists_psi (p := 3) ι φ g hg
    have hψind : ψ ∈ ggInduced ⊤ Bs := by
      have hle : ggAutomizer K Bs ⊔ ggAutomizer L Bs ≤ ggAutomizer ⊤ Bs :=
        sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
      have hmem : ψ ∈ ggAutomizer K Bs ⊔ ggAutomizer L Bs := by rw [hsup]; exact hψ
      have hmem' := hle hmem
      rwa [ggAutomizer_eq] at hmem'
    have hψrefl : GGIsReflection 3 ψ := by
      rw [ggIsReflection_iff_ggLinRefl hp2 ι ψ]; rw [hψg]; exact hgref
    have hψy : ψ ⟨y, hy⟩ = ⟨y, hy⟩ := by
      rw [ggLin_fix_iff (p := 3) ι ψ ⟨y, hy⟩]; rw [hψg]; exact hgy
    obtain ⟨hyB, hHLbody⟩ := hHK hk1 hguard
    have hb_eq : (⟨y, hyB⟩ : ↥Bs) = ⟨y, hy⟩ := Subtype.ext rfl
    have hψy' : ψ ⟨y, hyB⟩ = ⟨y, hyB⟩ := by rw [hb_eq]; exact hψy
    have hlines := hHLbody (M := ML) (C := CL) hMLweyl hCLcartan ι
      (fun i : Λ => φ (Sum.inl i)) (fun i : Λ => h (Sum.inl i)) (fun i : Λ => α (Sum.inl i))
      (fun i w => hform (Sum.inl i) w) (fun i => hrefl (Sum.inl i))
      (fun i j => hpairL i j) hAL ψ hψind hψrefl hψy'
    simpa only [hb_eq, hψg] using hlines
  · intro hxV0
    apply ggTK_x_ne_one hH
    have h1 : Additive.ofMul (⟨x, hx⟩ : ↥Bs) = 0 := by
      apply ι.injective
      simpa only [yV, map_zero] using hxV0
    have h2 : (⟨x, hx⟩ : ↥Bs) = 1 := by simpa using congrArg Additive.toMul h1
    exact congrArg Subtype.val h2
  · intro i
    have hmem : φ (Sum.inl i.1) ∈ ggAutomizer L Bs := by
      rw [hAK']; exact Subgroup.subset_closure ⟨Sum.inl i, rfl⟩
    exact (ggLin_fix_iff (p := 3) ι (φ (Sum.inl i.1)) (⟨x, hx⟩ : ↥Bs)).mp
      (hfixx (φ (Sum.inl i.1)) hmem)
  · intro a
    have hmem : φ (Sum.inr a) ∈ ggAutomizer L Bs := by
      rw [hAK']; exact Subgroup.subset_closure ⟨Sum.inr a, rfl⟩
    exact (ggLin_fix_iff (p := 3) ι (φ (Sum.inr a)) (⟨x, hx⟩ : ↥Bs)).mp
      (hfixx (φ (Sum.inr a)) hmem)
  · intro hk1 g hg hgref hgy
    obtain ⟨ψ, hψ, hψg⟩ := l05nLKE_exists_psi (p := 3) ι φ g hg
    have hψind : ψ ∈ ggInduced ⊤ Bs := by
      have hle : ggAutomizer K Bs ⊔ ggAutomizer L Bs ≤ ggAutomizer ⊤ Bs :=
        sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
      have hmem : ψ ∈ ggAutomizer K Bs ⊔ ggAutomizer L Bs := by rw [hsup]; exact hψ
      have hmem' := hle hmem
      rwa [ggAutomizer_eq] at hmem'
    have hψrefl : GGIsReflection 3 ψ := by
      rw [ggIsReflection_iff_ggLinRefl hp2 ι ψ]; rw [hψg]; exact hgref
    have hψx : ψ ⟨x, hx⟩ = ⟨x, hx⟩ := by
      rw [ggLin_fix_iff (p := 3) ι ψ ⟨x, hx⟩]; rw [hψg]; exact hgy
    obtain ⟨hxB, hHLbody⟩ := hHL hk1
    have hb_eq : (⟨x, hxB⟩ : ↥Bs) = ⟨x, hx⟩ := Subtype.ext rfl
    have hψx' : ψ ⟨x, hxB⟩ = ⟨x, hxB⟩ := by rw [hb_eq]; exact hψx
    have hlines := hHLbody (M := MK) (C := CK) hMKweyl hCKcartan ι
      ΦL (fun o => h (o.map Subtype.val id)) (fun o => α (o.map Subtype.val id))
      (fun o w => hform (o.map Subtype.val id) w) (fun o => hrefl (o.map Subtype.val id))
      (fun o o' => hpairK o o') hAK' ψ hψind hψrefl hψx'
    simpa only [ΦL, hb_eq, hψg] using hlines

end CFSG.StandardType

end

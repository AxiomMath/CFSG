module

public import CFSG.OddTranspositions.QHypTransvection
public import CFSG.Fischer.Classification.Basic.Reduced
public import CFSG.Fischer.Classification.Symplectic.OrthoGenSymplectic
public import CFSG.Fischer.Classification.PartIII.Symp.Exact

public section
namespace CFSG.OddTranspositions
open CFSG.Open Matrix CFSG.Blueprint.Fischer CFSG.Timmesfeld.Transvection.QTwo
open CFSG.Fischer.Classification CFSG.Fischer.Classification.LocalSymp

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem qHyp_symp {G : Type} [Group G] {D : Set G}
    (hP : Pair G D) (hZ : Subgroup.center G = ⊥) (hS : IsSimpleGroup (commutator G))
    (hna : ∃ a b : commutator G, a * b ≠ b * a)
    {m : ℕ} (hm : 2 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hskew : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hM : fischerLinearModel D
      (fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
        ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    QHyp G D := by
  have hna' : ¬ ∀ a b : commutator G, a * b = b * a := by
    intro h
    obtain ⟨a, b, hab⟩ := hna
    exact hab (h a b)
  refine ⟨⟨hP, hZ, hS⟩, Pair.exists_ne_commute hP hS hna', ?_, ?_⟩
  · intro e he f hf h
    exact Pair.eq_of_forall_commute_iff hP hZ hS he hf h
  · intro e he f hf hef hc
    obtain ⟨φ, hφ⟩ := hM
    obtain ⟨v, hv0, hve⟩ := (hφ e).1 he
    obtain ⟨w, hw0, hwf⟩ := (hφ f).1 hf
    let act : G → (Fin (2 * m) → ZMod 2) → (Fin (2 * m) → ZMod 2) :=
      fun g x =>
        ((φ g : GL (Fin (2 * m)) (ZMod 2)) : Matrix (Fin (2 * m)) (Fin (2 * m))
          (ZMod 2)) *ᵥ x
    have hmul : ∀ a b : G, act (a * b) = act a ∘ act b := by
      intro a b
      funext x
      simp only [act, Function.comp_apply, map_mul, Subgroup.coe_mul, Units.val_mul,
        Matrix.mulVec_mulVec]
    have hinj : Function.Injective act := by
      intro a b h
      apply φ.injective
      apply Subtype.ext
      apply Units.ext
      apply Matrix.ext_of_mulVec_single
      intro i
      simpa only [act] using congrFun h (Pi.single i 1)
    have he_tv : act e = tv b v := by
      funext x
      simpa only [act, tv_apply] using hve x
    have hf_tv : act f = tv b w := by
      funext x
      simpa only [act, tv_apply] using hwf x
    have hsymm : ∀ x y, b x y = b y x := by
      intro x y
      have hb : b.IsAlt := hskew
      calc b x y = -b y x := (hb.neg_eq y x).symm
        _ = b y x := CharTwo.neg_eq (b y x)
    have hnd' : ∀ x, (∀ y, b y x = 0) → x = 0 := by
      intro x hx
      exact hnd x fun y => by rw [hsymm]; exact hx y
    have hvw : v + w ≠ 0 := by
      intro h0
      have hwv : w = v :=
        (CFSG.Fischer.Classification.Symplectic.zmod_two_eq_of_add_eq_zero h0).symm
      exact hef (hinj (by rw [he_tv, hf_tv, hwv]))
    let T : GL (Fin (2 * m)) (ZMod 2) := sympTransvectionGL b hskew (v + w)
    have hTmem : T ∈ fischerMatrixGroup (fun A : Matrix (Fin (2 * m)) (Fin (2 * m))
        (ZMod 2) => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) :=
      sympTransvectionGL_mem_fischerMatrixGroup (v + w)
    have hTfischer : T ∈ fischerTransvections (fun x y => b x y) (fun v => v ≠ 0) :=
      sympTransvectionGL_mem_fischerTransvections hvw
    let g : G := φ.symm ⟨T, hTmem⟩
    have hφg : φ g = ⟨T, hTmem⟩ := φ.apply_symm_apply _
    have hgD : g ∈ D := (hφ g).2 (by simpa only [hφg] using hTfischer)
    have hg_tv : act g = tv b (v + w) := by
      funext x
      simpa only [act, tv_apply, hφg] using
        sympTransvectionGL_mulVec (b := b) (halt := hskew) (v + w) x
    have hge : g ≠ e := by
      intro h
      have hact : tv b (v + w) = tv b v := by
        rw [← hg_tv, h, he_tv]
      have hvw' : v + w = v := eq_of_tv_eq b hnd' hvw hact
      have hw' : w = 0 := by
        have h' : v + w = v + 0 := by simpa using hvw'
        exact add_left_cancel h'
      exact hw0 hw'
    have hgf : g ≠ f := by
      intro h
      have hact : tv b (v + w) = tv b w := by
        rw [← hg_tv, h, hf_tv]
      have hvw' : v + w = w := eq_of_tv_eq b hnd' hvw hact
      have hv' : v = 0 := by
        have h' : v + w = 0 + w := by simpa using hvw'
        exact add_right_cancel h'
      exact hv0 hv'
    refine ⟨g, hgD, hge, hgf, ?_⟩
    intro d hd hde hdf
    obtain ⟨u, hu0, hdu⟩ := (hφ d).1 hd
    have hd_tv : act d = tv b u := by
      funext x
      simpa only [act, tv_apply] using hdu x
    have hbuv : b u v = 0 :=
      (commute_iff_of_tv b act hsymm hmul hinj hd_tv he_tv (hskew u)).1 hde
    have hbuw : b u w = 0 :=
      (commute_iff_of_tv b act hsymm hmul hinj hd_tv hf_tv (hskew u)).1 hdf
    have hbuvw : b u (v + w) = 0 := by
      rw [LinearMap.BilinForm.add_right, hbuv, hbuw, add_zero]
    exact (commute_iff_of_tv b act hsymm hmul hinj hd_tv hg_tv (hskew u)).2 hbuvw

theorem transvectionHyp_of_symp {G : Type} [Group G] {D : Set G}
    (hP : Pair G D) (hZ : Subgroup.center G = ⊥) (hS : IsSimpleGroup (commutator G))
    (hna : ∃ a b : commutator G, a * b ≠ b * a)
    {m : ℕ} (hm : 2 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hskew : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hM : fischerLinearModel D
      (fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
        ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    CFSG.Timmesfeld.Transvection.TransvectionHyp G
      {A | ∃ d ∈ D, A = Subgroup.zpowers d} :=
  transvectionHyp_of_qHyp (qHyp_symp hP hZ hS hna hm hskew hnd hM)

end CFSG.OddTranspositions

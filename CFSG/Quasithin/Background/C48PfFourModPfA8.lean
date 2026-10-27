module

public import CFSG.Quasithin.Background.C124BlkAlt
public import CFSG.Quasithin.Background.JonesParshallNatural
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.Background.C48PfFourModPfGrp
public import CFSG.Quasithin.Background.F918F2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C48Pf.FMod

open Matrix CFSG.Quasithin.JonesParshall CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem fix_ut_minors4 : ∀ x : Fin 6 → ZMod 2,
    (∀ a b : Fin 4, a < b → minors4 (1 + Matrix.single a b (1 : ZMod 2)) *ᵥ x = x) →
      x = 0 ∨ x = Pi.single 0 1 := by
  decide +kernel

@[expose] def orbM : Fin 6 → Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ![!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0],
    !![0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1],
    !![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0],
    !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]]

theorem orbM_det : ∀ k, (orbM k).det = 1 := by
  decide +kernel

theorem orbM_mulVec : ∀ k, minors4 (orbM k) *ᵥ (Pi.single 0 1 : Fin 6 → ZMod 2) =
    Pi.single k 1 := by
  decide +kernel

theorem eq_top_of_minors4_invariant (W : AddSubgroup (Fin 6 → ZMod 2)) (hW : W ≠ ⊥)
    (hinv : ∀ g : SpecialLinearGroup (Fin 4) (ZMod 2), ∀ w ∈ W,
      minors4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w ∈ W) : W = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction ↥(unitriangular 4 (ZMod 2)) ↥W :=
    { smul := fun g w => ⟨minors4 ((g : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w, hinv g w w.2⟩
      one_smul := fun w => Subtype.ext (by
        show minors4 (((1 : ↥(unitriangular 4 (ZMod 2))) : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ (w : Fin 6 → ZMod 2) = w
        simp [minors4_one])
      mul_smul := fun g h w => Subtype.ext (by
        show minors4 (((g * h : ↥(unitriangular 4 (ZMod 2))) : SpecialLinearGroup (Fin 4)
          (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ (w : Fin 6 → ZMod 2) = _
        simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, minors4_mul,
          ← Matrix.mulVec_mulVec]
        rfl) }
  have hcard : 2 ∣ Nat.card ↥W := by
    have h1 : Nat.card ↥W ∣ 2 ^ 6 := by
      have := AddSubgroup.card_addSubgroup_dvd_card W
      rwa [Nat.card_fun, Nat.card_zmod, Nat.card_fin] at this
    obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    have hne : Nat.card ↥W ≠ 1 := by
      intro h
      exact hW ((AddSubgroup.card_eq_one).1 h)
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact absurd hie (by simpa using hne)
    · rw [hie]
      exact dvd_pow_self 2 (by omega)
  have h0 : (0 : ↥W) ∈ MulAction.fixedPoints ↥(unitriangular 4 (ZMod 2)) ↥W := by
    intro g
    apply Subtype.ext
    show minors4 _ *ᵥ (0 : Fin 6 → ZMod 2) = 0
    exact Matrix.mulVec_zero _
  obtain ⟨b, hb, hb0⟩ := IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (isPGroup_unitriangular_charTwo (K := ZMod 2) (n := 4) (by norm_num)) ↥W hcard h0
  have hbfix : ∀ a c : Fin 4, a < c →
      minors4 (1 + Matrix.single a c (1 : ZMod 2)) *ᵥ (b : Fin 6 → ZMod 2) = b := by
    intro a c hac
    have hT := hb ⟨SpecialLinearGroup.transvection (ne_of_lt hac) (1 : ZMod 2),
      transvection_mem_unitriangular hac⟩
    have := congrArg Subtype.val hT
    have e : ((⟨SpecialLinearGroup.transvection (ne_of_lt hac) (1 : ZMod 2),
        transvection_mem_unitriangular hac⟩ : ↥(unitriangular 4 (ZMod 2))) • b : ↥W) =
        ⟨minors4 (1 + Matrix.single a c (1 : ZMod 2)) *ᵥ (b : Fin 6 → ZMod 2), by
          rw [← CFSG.LinearGroups.coe_transvection (ne_of_lt hac)]
          exact hinv _ _ b.2⟩ := rfl
    rw [e] at this
    exact this
  have hbe : (b : Fin 6 → ZMod 2) = Pi.single 0 1 := by
    rcases fix_ut_minors4 b hbfix with h | h
    · exact absurd (Subtype.ext h.symm) hb0
    · exact h
  have hmem : ∀ k : Fin 6, (Pi.single k 1 : Fin 6 → ZMod 2) ∈ W := by
    intro k
    rw [← orbM_mulVec k, ← hbe]
    exact hinv ⟨orbM k, orbM_det k⟩ _ b.2
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_sum_single x]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  rcases zmod2_cases (x k) with h | h
  · rw [h, Pi.single_zero]
    exact W.zero_mem
  · rw [h]
    exact hmem k


theorem minors4_transpose (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    minors4 gᵀ = (minors4 g)ᵀ := by
  ext k l
  fin_cases k <;> fin_cases l <;>
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp [minors4, pr4', Matrix.transpose_apply]
    ring

open CFSG.ComponentClassification.PresentationLocal CFSG.GH74.Exceptional
  CFSG.Quasithin.SteinbergCB.I16 CFSG.QuasithinUnique

theorem alt8WedgeB_minors4 (φ : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))
    (hφ : ∀ k, φ (carmichaelCycle k) = l42Gen k) (g : SpecialLinearGroup (Fin 4) (ZMod 2))
    (y : Fin 6 → ZMod 2) :
    alt8WedgeB *ᵥ (minors4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y) =
      coords8.actA (φ.symm (Matrix.SpecialLinearGroup.toGL (invTransposeSL 4 (ZMod 2) g)))
        (alt8WedgeB *ᵥ y) := by
  have h := alt8WedgeDual_intertwine φ.toMonoidHom hφ
    (φ.symm (Matrix.SpecialLinearGroup.toGL (invTransposeSL 4 (ZMod 2) g))) y
  have h2 : alt8WedgeDual (φ.toMonoidHom (φ.symm (Matrix.SpecialLinearGroup.toGL
      (invTransposeSL 4 (ZMod 2) g)))) = minors4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    show (minors4 (((Matrix.SpecialLinearGroup.toGL (invTransposeSL 4 (ZMod 2) g))⁻¹ :
      GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))ᵀ = _
    rw [← map_inv, ← map_inv]
    show (minors4 ((((g⁻¹)⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ))ᵀ = _
    rw [inv_inv, minors4_transpose, Matrix.transpose_transpose]
  rw [h2] at h
  exact h

@[expose] def heartOf : (Fin 6 → ZMod 2) →+ AltHeart 8 :=
  (QuotientAddGroup.mk' (constWeight 8)).comp
    { toFun := fun y => ⟨coords8.incl (alt8WedgeB *ᵥ y), coords8.sum_incl _⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun y y' => by
        apply Subtype.ext
        simp [Matrix.mulVec_add] }

theorem heartOf_apply (y : Fin 6 → ZMod 2) :
    heartOf y = QuotientAddGroup.mk ⟨coords8.incl (alt8WedgeB *ᵥ y), coords8.sum_incl _⟩ := rfl

theorem incl_proj_sub_mem (x : ↥(evenWeight 8)) :
    -x + ⟨coords8.incl (coords8.proj x), coords8.sum_incl _⟩ ∈ constWeight 8 := by
  have hsum : ∑ i, ((x : Fin 8 → ZMod 2) i - coords8.incl (coords8.proj x) i) = 0 := by
    rw [Finset.sum_sub_distrib, coords8.sum_incl]
    have : ∑ i, (x : Fin 8 → ZMod 2) i = 0 := x.2
    rw [this, sub_zero]
  have hproj : coords8.proj ((x : Fin 8 → ZMod 2) - coords8.incl (coords8.proj x)) = 0 := by
    rw [map_sub, coords8.proj_incl, sub_self]
  intro i j
  show -(x : Fin 8 → ZMod 2) i + coords8.incl (coords8.proj (x : Fin 8 → ZMod 2)) i =
    -(x : Fin 8 → ZMod 2) j + coords8.incl (coords8.proj (x : Fin 8 → ZMod 2)) j
  have e : ∀ k, -(x : Fin 8 → ZMod 2) k + coords8.incl (coords8.proj (x : Fin 8 → ZMod 2)) k =
      -(((x : Fin 8 → ZMod 2) - coords8.incl (coords8.proj (x : Fin 8 → ZMod 2))) k) := by
    intro k
    simp only [Pi.sub_apply]
    ring
  rw [e i, e j]
  rcases coords8.ker_proj _ hsum hproj with h | h
  · have h' : (x : Fin 8 → ZMod 2) - coords8.incl (coords8.proj (x : Fin 8 → ZMod 2)) = 0 := h
    rw [h']
    rfl
  · have h' : (x : Fin 8 → ZMod 2) - coords8.incl (coords8.proj (x : Fin 8 → ZMod 2)) =
        fun _ => 1 := h
    rw [h']

theorem heartOf_injective : Function.Injective heartOf := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [heartOf_apply, QuotientAddGroup.eq_zero_iff] at hy
  have hc : ∀ i j : Fin 8, coords8.incl (alt8WedgeB *ᵥ y) i =
      coords8.incl (alt8WedgeB *ᵥ y) j := hy
  have hB : alt8WedgeB *ᵥ y = 0 := by
    have hconst : coords8.incl (alt8WedgeB *ᵥ y) =
        fun _ => coords8.incl (alt8WedgeB *ᵥ y) 0 := funext fun i => hc i 0
    rw [← coords8.proj_incl (alt8WedgeB *ᵥ y), hconst]
    rcases zmod2_cases (coords8.incl (alt8WedgeB *ᵥ y) 0) with h | h
    · rw [h]
      exact map_zero coords8.proj
    · rw [h]
      exact coords8.proj_one (by decide)
  have := congrArg (alt8WedgeBInv *ᵥ ·) hB
  simpa [Matrix.mulVec_mulVec, alt8WedgeBInv_mul] using this

theorem heartOf_surjective : Function.Surjective heartOf := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  refine ⟨alt8WedgeBInv *ᵥ coords8.proj x, ?_⟩
  rw [heartOf_apply, Matrix.mulVec_mulVec, alt8WedgeB_mul_inv, Matrix.one_mulVec,
    QuotientAddGroup.eq]
  have h := incl_proj_sub_mem x
  have h2 := (constWeight 8).neg_mem h
  rw [neg_add, neg_neg] at h2
  simpa [add_comm] using h2

theorem heartOf_minors4 (φ : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))
    (hφ : ∀ k, φ (carmichaelCycle k) = l42Gen k) (g : SpecialLinearGroup (Fin 4) (ZMod 2))
    (y : Fin 6 → ZMod 2) (x : ↥(evenWeight 8)) (hx : (QuotientAddGroup.mk x : AltHeart 8) =
      heartOf y) :
    (QuotientAddGroup.mk (permWeight 8 ((φ.symm (Matrix.SpecialLinearGroup.toGL
      (invTransposeSL 4 (ZMod 2) g)) : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) x) :
        AltHeart 8) = heartOf (minors4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y) := by
  set σ := φ.symm (Matrix.SpecialLinearGroup.toGL (invTransposeSL 4 (ZMod 2) g)) with hσ
  set x₀ : ↥(evenWeight 8) := ⟨coords8.incl (alt8WedgeB *ᵥ y), coords8.sum_incl _⟩ with hx₀
  have h1 : -x + x₀ ∈ constWeight 8 := by
    rw [← QuotientAddGroup.eq]
    exact hx
  have h2 := C124.permWeight_sub_mem (σ : Equiv.Perm (Fin 8)) h1
  rw [heartOf_apply, alt8WedgeB_minors4 φ hφ g y, ← hσ, QuotientAddGroup.eq]
  have h3 := incl_proj_sub_mem (permWeight 8 (σ : Equiv.Perm (Fin 8)) x₀)
  have hpv : coords8.actA σ (alt8WedgeB *ᵥ y) =
      coords8.proj ((permWeight 8 (σ : Equiv.Perm (Fin 8)) x₀ : ↥(evenWeight 8)) :
        Fin 8 → ZMod 2) := rfl
  have h4 := (constWeight 8).add_mem h2 h3
  convert h4 using 1
  rw [hpv]
  abel


theorem isAltNaturalSection_of_minors4 {G : Type} [Group G] {A V : Subgroup G} {N : Subgroup ↥A}
    (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (α : ↥A →* SpecialLinearGroup (Fin 4) (ZMod 2)) (hα : Function.Surjective α)
    (hker : α.ker = N) (Ψ : ↥V →* Multiplicative (Fin 6 → ZMod 2)) (hΨ : Function.Bijective Ψ)
    (hequiv : ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (Ψ v) = minors4 ((α a : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Multiplicative.toAdd (Ψ u)) :
    IsAltNaturalSection A V ⊥ N 8 := by
  classical
  obtain ⟨φ, hφ⟩ := exists_iso_alt8_carm
  have hdet : ∀ g : GL (Fin 4) (ZMod 2), (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).det = 1 := by
    intro g
    have hu : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hu (Matrix.GeneralLinearGroup.det g),
      Units.val_one]
  let θ : SpecialLinearGroup (Fin 4) (ZMod 2) →* ↥(alternatingGroup (Fin 8)) :=
    φ.symm.toMonoidHom.comp (Matrix.SpecialLinearGroup.toGL.comp
      (invTransposeSL 4 (ZMod 2)).toMonoidHom)
  have hθ : ∀ g, θ g = φ.symm (Matrix.SpecialLinearGroup.toGL (invTransposeSL 4 (ZMod 2) g)) :=
    fun g => rfl
  have hθinj : Function.Injective θ := by
    intro g h hgh
    have h1 : Matrix.SpecialLinearGroup.toGL (invTransposeSL 4 (ZMod 2) g) =
        Matrix.SpecialLinearGroup.toGL (invTransposeSL 4 (ZMod 2) h) := by
      apply φ.symm.injective
      rw [← hθ, ← hθ]
      exact hgh
    have h2 : invTransposeSL 4 (ZMod 2) g = invTransposeSL 4 (ZMod 2) h :=
      Matrix.SpecialLinearGroup.toGL_injective h1
    exact (invTransposeSL 4 (ZMod 2)).injective h2
  have hθsurj : Function.Surjective θ := by
    intro σ
    set g₀ : SpecialLinearGroup (Fin 4) (ZMod 2) :=
      ⟨(φ σ : Matrix (Fin 4) (Fin 4) (ZMod 2)), hdet _⟩ with hg₀
    refine ⟨(invTransposeSL 4 (ZMod 2)).symm g₀, ?_⟩
    have e : invTransposeSL 4 (ZMod 2) ((invTransposeSL 4 (ZMod 2)).symm g₀) = g₀ :=
      MulEquiv.apply_symm_apply _ _
    rw [hθ, e, MulEquiv.symm_apply_eq]
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  refine ⟨hAV, θ.comp α, hθsurj.comp hα, ?_, ?_⟩
  · rw [← hker]
    ext a
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h
      exact hθinj (h.trans (map_one θ).symm)
    · intro h
      rw [h, map_one]
  let β : ↥V →* Multiplicative (AltHeart 8) := (AddMonoidHom.toMultiplicative heartOf).comp Ψ
  refine ⟨β, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨y, hy⟩ := heartOf_surjective (Multiplicative.toAdd q)
    obtain ⟨v, hv⟩ := hΨ.2 (Multiplicative.ofAdd y)
    refine ⟨v, ?_⟩
    show Multiplicative.ofAdd (heartOf (Multiplicative.toAdd (Ψ v))) = q
    rw [hv, toAdd_ofAdd, hy, ofAdd_toAdd]
  · ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · intro h
      have h1 : heartOf (Multiplicative.toAdd (Ψ v)) = 0 := congrArg Multiplicative.toAdd h
      have h2 : Multiplicative.toAdd (Ψ v) = 0 := heartOf_injective (h1.trans (map_zero _).symm)
      have h3 : Ψ v = Ψ 1 := by
        rw [map_one]
        exact Multiplicative.toAdd.injective h2
      exact congrArg Subtype.val (hΨ.1 h3)
    · intro h
      have : v = 1 := Subtype.ext h
      rw [this, map_one]
  · intro a u v huv x hx
    have h1 := hequiv a u v huv
    show (QuotientAddGroup.mk (permWeight 8 ((θ (α a) : ↥(alternatingGroup (Fin 8))) :
      Equiv.Perm (Fin 8)) x) : AltHeart 8) = heartOf (Multiplicative.toAdd (Ψ v))
    rw [h1, hθ]
    exact heartOf_minors4 φ hφ (α a) _ x hx

end CFSG.Quasithin.C48Pf.FMod

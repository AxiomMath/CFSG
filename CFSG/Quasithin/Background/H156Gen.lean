module

public import CFSG.Quasithin.Background.HMathieuBits
public import CFSG.Quasithin.Background.HTransport
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Milestones.ASVolI.H1
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open scoped Matrix

namespace CFSG.Quasithin.H156

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

@[expose] def maskHom (n k : ℕ) (cs : List ℕ) : Wn n →* Wn k where
  toFun v := Multiplicative.ofAdd (∑ j : Fin n, Multiplicative.toAdd v j • bvec k (cs.getD j 0))
  map_one' := by simp
  map_mul' v w := by
    simp only [toAdd_mul, Pi.add_apply, add_smul, Finset.sum_add_distrib, ofAdd_add]

theorem maskHom_toW {n k : ℕ} {cs : List ℕ} (hcs : cs.length = n) (m : ℕ) :
    maskHom n k cs (toW n m) = toW k (actM cs m) := by
  unfold maskHom toW
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  congr 1
  rw [bvec_actM k cs m, hcs, ← Fin.sum_univ_eq_sum_range
    (fun j => if m.testBit j then bvec k (cs.getD j 0) else 0) n]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bvec_apply]
  split_ifs <;> simp

@[expose] def colMat (n : ℕ) (cs : List ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => bvec n (cs.getD j 0) i

theorem mulVec_colMat {n : ℕ} {cs : List ℕ} (hcs : cs.length = n) (m : ℕ) :
    (colMat n cs).mulVec (bvec n m) = bvec n (actM cs m) := by
  funext i
  rw [bvec_actM n cs m, hcs, Finset.sum_apply, ← Fin.sum_univ_eq_sum_range
    (fun j => (if m.testBit j then bvec n (cs.getD j 0) else 0) i) n]
  simp only [Matrix.mulVec, dotProduct, colMat, Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bvec_apply n m j]
  by_cases h : m.testBit j = true
  · simp [h]
  · simp [h]

@[expose] def mkGL (n : ℕ) (cs ics : List ℕ) (h1 : colMat n cs * colMat n ics = 1)
    (h2 : colMat n ics * colMat n cs = 1) : GL (Fin n) (ZMod 2) :=
  ⟨colMat n cs, colMat n ics, h1, h2⟩

theorem natHom_mkGL {n : ℕ} {cs ics : List ℕ} (hcs : cs.length = n)
    (h1 : colMat n cs * colMat n ics = 1) (h2 : colMat n ics * colMat n cs = 1) (m : ℕ) :
    natHom n (ZMod 2) (mkGL n cs ics h1 h2) (toW n m) = toW n (actM cs m) := by
  show Multiplicative.ofAdd ((colMat n cs).mulVec (bvec n m)) = _
  rw [mulVec_colMat hcs]
  rfl

@[expose] def invTGL (n : ℕ) : GL (Fin n) (ZMod 2) →* GL (Fin n) (ZMod 2) where
  toFun a := ⟨((a⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ,
    ((a : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ, by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one], by
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    simp [Matrix.transpose_mul]

theorem invTGL_invTGL {n : ℕ} (a : GL (Fin n) (ZMod 2)) : invTGL n (invTGL n a) = a := by
  apply Units.ext
  show ((invTGL n a)⁻¹ : GL (Fin n) (ZMod 2)).1ᵀ = a.1
  have : ((invTGL n a)⁻¹ : GL (Fin n) (ZMod 2)).1 = (a.1)ᵀ := rfl
  rw [this, Matrix.transpose_transpose]

theorem natHom_injective (n : ℕ) : Function.Injective (natHom n (ZMod 2)) := by
  rw [injective_iff_map_eq_one]
  intro a h
  apply Units.ext
  ext i j
  have h1 := congrArg (fun φ : MulAut (Multiplicative (Fin n → ZMod 2)) =>
    Multiplicative.toAdd (φ (Multiplicative.ofAdd (Pi.single j 1))) i) h
  simp only [natHom, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    toAdd_ofAdd, MulAut.one_apply, Matrix.mulVec_single_one] at h1
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h1

@[expose] def ix (i : Fin 3) (j : Fin 2) : Fin 6 := ⟨i + 3 * j, by omega⟩

abbrev Mat32 : Type := Multiplicative (Matrix (Fin 3) (Fin 2) (ZMod 2))

@[expose] def matOfW : Wn 6 →* Mat32 where
  toFun v := Multiplicative.ofAdd (Matrix.of fun i j => Multiplicative.toAdd v (ix i j))
  map_one' := by
    ext i j
    simp
  map_mul' v w := by
    ext i j
    simp

theorem matOfW_bijective : Function.Bijective matOfW := by
  decide +kernel

section Transport

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem congrHom_apply_eg (eg : V ≃* W) (g : MulAut V) (v : V) :
    congrHom eg g (eg v) = eg (g v) := by
  rw [congrHom_apply, MulEquiv.symm_apply_apply]

theorem inducesOn_of_map (eg : V ≃* W) {G : Subgroup (MulAut V)} {U Z : Subgroup V}
    {A : Type*} [CommGroup A] {Γ : Subgroup (MulAut A)}
    (h : InducesOn (G.map (congrHom eg)) (U.map eg.toMonoidHom) (Z.map eg.toMonoidHom) A Γ) :
    InducesOn G U Z A Γ := by
  obtain ⟨hZU, hGU, hGZ, β, hsurj, hker, hind1, hind2⟩ := h
  let φ : ↥U ≃* ↥(U.map eg.toMonoidHom) := U.equivMapOfInjective eg.toMonoidHom eg.injective
  have hφ : ∀ u : ↥U, ((φ u : ↥(U.map eg.toMonoidHom)) : W) = eg (u : V) := fun u => rfl
  have hmem : ∀ (X : Subgroup V) (v : V), eg v ∈ X.map eg.toMonoidHom ↔ v ∈ X := fun X v =>
    Subgroup.mem_map_iff_mem eg.injective
  refine ⟨(Subgroup.map_le_map_iff_of_injective eg.injective).1 hZU, ?_, ?_, β.comp φ.toMonoidHom,
    hsurj.comp φ.surjective, ?_, ?_, ?_⟩
  · intro g hg u hu
    have := hGU (congrHom eg g) (Subgroup.mem_map_of_mem _ hg) (eg u)
      ((hmem U u).2 hu)
    rw [congrHom_apply_eg] at this
    exact (hmem U _).1 this
  · intro g hg z hz
    have := hGZ (congrHom eg g) (Subgroup.mem_map_of_mem _ hg) (eg z)
      ((hmem Z z).2 hz)
    rw [congrHom_apply_eg] at this
    exact (hmem Z _).1 this
  · intro u
    show β (φ u) = 1 ↔ _
    rw [hker (φ u), hφ, hmem]
  · intro g hg
    obtain ⟨γ, hγ, hγu⟩ := hind1 (congrHom eg g) (Subgroup.mem_map_of_mem _ hg)
    refine ⟨γ, hγ, fun u u' h => hγu (φ u) (φ u') ?_⟩
    rw [hφ, hφ, h, congrHom_apply_eg]
  · intro γ hγ
    obtain ⟨g₁, hg₁, hgu⟩ := hind2 γ hγ
    obtain ⟨g, hgG, rfl⟩ := Subgroup.mem_map.1 hg₁
    refine ⟨g, hgG, fun u u' h => hgu (φ u) (φ u') ?_⟩
    rw [hφ, hφ, h, congrHom_apply_eg]

theorem chief_of_inducesOn {G : Subgroup (MulAut V)} {U Z : Subgroup V} {A : Type*} [CommGroup A]
    {Γ : Subgroup (MulAut A)} (h : InducesOn G U Z A Γ) (hlt : Z < U)
    (hirr : ∀ W' : Subgroup A, (∀ γ ∈ Γ, ∀ w ∈ W', γ w ∈ W') → W' = ⊥ ∨ W' = ⊤) :
    IsChiefFactorUnder (actsOnModule G) Z U := by
  obtain ⟨hZU, hGU, hGZ, β, hsurj, hker, hind1, hind2⟩ := h
  refine ⟨hlt, ?_, ?_, ?_⟩
  · rintro f ⟨g, hg, rfl⟩ z hz
    exact hGZ g hg z hz
  · rintro f ⟨g, hg, rfl⟩ u hu
    exact hGU g hg u hu
  · intro Wd hZW hWU hWinv
    have hinv'' : ∀ γ ∈ Γ, ∀ w ∈ (Wd.subgroupOf U).map β, γ w ∈ (Wd.subgroupOf U).map β := by
      intro γ hγ w hw
      obtain ⟨g, hg, hgi⟩ := hind2 γ hγ
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hw
      have hguW : g (u : V) ∈ Wd :=
        hWinv (fun v => g v) ⟨g, hg, rfl⟩ u (Subgroup.mem_subgroupOf.1 hu)
      have hguU : g (u : V) ∈ U := hGU g hg u u.2
      refine Subgroup.mem_map.2 ⟨⟨g u, hguU⟩, Subgroup.mem_subgroupOf.2 hguW, ?_⟩
      exact hgi u ⟨g u, hguU⟩ rfl
    rcases hirr _ hinv'' with h0 | h1
    · left
      refine le_antisymm (fun w hw => ?_) hZW
      have : β ⟨w, hWU hw⟩ ∈ (Wd.subgroupOf U).map β :=
        Subgroup.mem_map.2 ⟨⟨w, hWU hw⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      exact (hker ⟨w, hWU hw⟩).1 this
    · right
      refine le_antisymm hWU (fun u hu => ?_)
      have : β ⟨u, hu⟩ ∈ (Wd.subgroupOf U).map β := by
        rw [h1]
        exact Subgroup.mem_top _
      obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 this
      have hwW : (w : V) ∈ Wd := Subgroup.mem_subgroupOf.1 hw
      have hker1 : β (w⁻¹ * ⟨u, hu⟩) = 1 := by rw [map_mul, map_inv, hwu, inv_mul_cancel]
      have hz : ((w⁻¹ * ⟨u, hu⟩ : ↥U) : V) ∈ Z := (hker _).1 hker1
      have hzW := hZW hz
      have : u = (w : V) * ((w⁻¹ * ⟨u, hu⟩ : ↥U) : V) := by
        show u = (w : V) * ((w : V)⁻¹ * u)
        rw [mul_inv_cancel_left]
      rw [this]
      exact Wd.mul_mem hwW hzW

end Transport

end CFSG.Quasithin.H156

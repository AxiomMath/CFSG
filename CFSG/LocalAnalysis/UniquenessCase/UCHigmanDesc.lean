module

public import CFSG.LocalAnalysis.UniquenessCase.UCHigmanClass
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.SimpleModule.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Higman

open Matrix CFSG.Quasithin.SmithCurtis
open scoped MatrixGroups

section Descent

variable {K : Type} [Field K] [CharP K 2]

@[expose] def AmatK (i : ℕ) (g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K :=
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  (g : Matrix (Fin 2) (Fin 2) K).map (iterateFrobenius K 2 i)

theorem AmatK_uMat (i : ℕ) (a : K) : AmatK i (uMat a) = !![1, a ^ 2 ^ i; 0, 1] := by
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  ext x y
  fin_cases x <;> fin_cases y <;> simp [AmatK, iterateFrobenius_def]

theorem AmatK_lMat (i : ℕ) (a : K) : AmatK i (lMat a) = !![1, 0; a ^ 2 ^ i, 1] := by
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  ext x y
  fin_cases x <;> fin_cases y <;> simp [AmatK, iterateFrobenius_def]

theorem frob_surjective [Finite K] (i : ℕ) : ∀ t : K, ∃ a : K, a ^ 2 ^ i = t := by
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  have hinj : Function.Injective (iterateFrobenius K 2 i) := (iterateFrobenius K 2 i).injective
  intro t
  obtain ⟨a, ha⟩ := Finite.surjective_of_injective hinj t
  exact ⟨a, by simpa [iterateFrobenius_def] using ha⟩

theorem addSubgroup_top_of_axes (W : AddSubgroup (Fin 2 → K))
    (h0 : ∀ t : K, (![t, 0] : Fin 2 → K) ∈ W) (h1 : ∀ t : K, (![0, t] : Fin 2 → K) ∈ W) :
    W = ⊤ := by
  rw [eq_top_iff]
  intro w _
  have : w = ![w 0, 0] + ![0, w 1] := by
    ext j; fin_cases j <;> simp
  rw [this]
  exact W.add_mem (h0 _) (h1 _)

theorem uMat_sub_self (i : ℕ) (a : K) (w : Fin 2 → K) :
    (AmatK i (uMat a)) *ᵥ w - w = ![a ^ 2 ^ i * w 1, 0] := by
  rw [AmatK_uMat]
  ext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem lMat_sub_self (i : ℕ) (a : K) (w : Fin 2 → K) :
    (AmatK i (lMat a)) *ᵥ w - w = ![0, a ^ 2 ^ i * w 0] := by
  rw [AmatK_lMat]
  ext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem natK_simple [Finite K] (i : ℕ) (W : AddSubgroup (Fin 2 → K))
    (hW : ∀ (g : SL(2, K)) (w : Fin 2 → K), w ∈ W → (AmatK i g) *ᵥ w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  obtain ⟨⟨w, hwW⟩, hw0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.1 hb
  have hw0' : w ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hu : ∀ (a : K) (v : Fin 2 → K), v ∈ W → (![a ^ 2 ^ i * v 1, 0] : Fin 2 → K) ∈ W := by
    intro a v hv
    rw [← uMat_sub_self]
    exact W.sub_mem (hW _ v hv) hv
  have hl : ∀ (a : K) (v : Fin 2 → K), v ∈ W → (![0, a ^ 2 ^ i * v 0] : Fin 2 → K) ∈ W := by
    intro a v hv
    rw [← lMat_sub_self]
    exact W.sub_mem (hW _ v hv) hv
  by_cases hy : w 1 = 0
  · have hx : w 0 ≠ 0 := by
      intro h
      apply hw0'
      ext j; fin_cases j <;> simp [h, hy]
    have h1 : ∀ t : K, (![0, t] : Fin 2 → K) ∈ W := by
      intro t
      obtain ⟨a, ha⟩ := frob_surjective (K := K) i (t / w 0)
      have := hl a w hwW
      rwa [ha, div_mul_cancel₀ _ hx] at this
    have h0 : ∀ t : K, (![t, 0] : Fin 2 → K) ∈ W := by
      intro t
      obtain ⟨a, ha⟩ := frob_surjective (K := K) i t
      have := hu a ![0, 1] (h1 1)
      simpa [ha] using this
    exact addSubgroup_top_of_axes W h0 h1
  · have h0 : ∀ t : K, (![t, 0] : Fin 2 → K) ∈ W := by
      intro t
      obtain ⟨a, ha⟩ := frob_surjective (K := K) i (t / w 1)
      have := hu a w hwW
      rwa [ha, div_mul_cancel₀ _ hy] at this
    have h1 : ∀ t : K, (![0, t] : Fin 2 → K) ∈ W := by
      intro t
      obtain ⟨a, ha⟩ := frob_surjective (K := K) i t
      have := hl a ![1, 0] (h0 1)
      simpa [ha] using this
    exact addSubgroup_top_of_axes W h0 h1

end Descent

section Coord

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_matrix_model (ρ : Representation (ZMod 2) G V) :
    ∃ (m : ℕ) (R : G →* Matrix (Fin m) (Fin m) (ZMod 2)) (c : V ≃ₗ[ZMod 2] (Fin m → ZMod 2)),
      ∀ (g : G) (v : V), c (ρ g v) = R g *ᵥ c v := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let b := Module.finBasis (ZMod 2) V
  refine ⟨Module.finrank (ZMod 2) V,
    (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ, b.equivFun, fun g v => ?_⟩
  have := LinearMap.toMatrix_mulVec_repr b b (ρ g) v
  exact this.symm

end Coord

section KRep

variable {k : Type*} [Field k] {G : Type*} [Group G]

@[expose] noncomputable def kRep (ι : ZMod 2 →+* k) {m : ℕ}
    (R : G →* Matrix (Fin m) (Fin m) (ZMod 2)) : Representation k G (Fin m → k) where
  toFun g := Matrix.mulVecLin ((R g).map ι)
  map_one' := by
    rw [map_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.mulVecLin_one
  map_mul' g h := by
    rw [map_mul, Matrix.map_mul]
    exact Matrix.mulVecLin_mul _ _

theorem kRep_apply (ι : ZMod 2 →+* k) {m : ℕ} (R : G →* Matrix (Fin m) (Fin m) (ZMod 2)) (g : G)
    (w : Fin m → k) : kRep ι R g w = ((R g).map ι) *ᵥ w := rfl

theorem exists_simple_sub {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Nontrivial W] (ρ : Representation k G W) :
    ∃ (S : Submodule k W) (hS : ∀ g : G, ∀ w ∈ S, ρ g w ∈ S), S ≠ ⊥ ∧
      CFSG.Quasithin.SmithCurtis.IsSimpleRep (restrictRep ρ S hS) := by
  classical
  have hex : ∃ r : ℕ, ∃ S : Submodule k W, (∀ g : G, ∀ w ∈ S, ρ g w ∈ S) ∧ S ≠ ⊥ ∧
      Module.finrank k S = r :=
    ⟨_, ⊤, fun g w _ => Submodule.mem_top, top_ne_bot, rfl⟩
  obtain ⟨S, hS, hne, hr⟩ := Nat.find_spec hex
  refine ⟨S, hS, hne, ?_⟩
  haveI : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr hne
  refine ⟨inferInstance, fun W' hW' => ?_⟩
  by_cases hbot : W' = ⊥
  · exact Or.inl hbot
  right
  have hmap : ∀ g : G, ∀ w ∈ W'.map S.subtype, ρ g w ∈ W'.map S.subtype := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨restrictRep ρ S hS g x, hW' g x hx, rfl⟩
  have hnebot : W'.map S.subtype ≠ ⊥ := by
    intro h
    apply hbot
    exact Submodule.map_injective_of_injective S.injective_subtype
      (h.trans (Submodule.map_bot _).symm)
  have hmin := Nat.find_min' hex ⟨W'.map S.subtype, hmap, hnebot, rfl⟩
  rw [Submodule.finrank_map_subtype_eq] at hmin
  have hle : Module.finrank k W' ≤ Module.finrank k S := Submodule.finrank_le W'
  refine Submodule.eq_top_of_finrank_eq ?_
  omega

end KRep

section Main

variable {K : Type} [Field K] [CharP K 2]

theorem Amat_eq_map_AmatK {k : Type} [Field k] [Algebra K k] (i : ℕ) (g : SL(2, K)) :
    (Amat i g : Matrix (Fin 2) (Fin 2) k) = (AmatK i g).map (algebraMap K k) := by
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  ext x y
  simp [Amat, AmatK, frobK_apply, iterateFrobenius_def]

@[expose] def zmod2Submodule {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (H : AddSubgroup V) :
    Submodule (ZMod 2) V where
  carrier := H
  add_mem' := H.add_mem
  zero_mem' := H.zero_mem
  smul_mem' c v hv := by
    have hc : c = 0 ∨ c = 1 := by decide +revert
    rcases hc with rfl | rfl
    · rw [zero_smul]; exact H.zero_mem
    · rw [one_smul]; exact hv

theorem descent_natural [Finite K] {n : ℕ} (hn : Nat.card K = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] [Nontrivial V]
    (ρ : Representation (ZMod 2) SL(2, K) V)
    (hsimple : ∀ W : Submodule (ZMod 2) V, (∀ (g : SL(2, K)), ∀ w ∈ W, ρ g w ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (d : SL(2, K)) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hdV : ∀ v : V, ρ d (ρ d v) + ρ d v + v = 0) :
    ∃ i : ℕ, i < n ∧ ∃ ψ : V ≃+ (Fin 2 → K), ∀ (g : SL(2, K)) (v : V),
      ψ (ρ g v) = (AmatK i g) *ᵥ ψ v := by
  classical
  let k := AlgebraicClosure K
  letI : Algebra (ZMod 2) k := (ZMod.castHom (dvd_refl 2) k).toAlgebra
  obtain ⟨m, R, c, hc⟩ := exists_matrix_model ρ
  let ι : ZMod 2 →+* k := algebraMap (ZMod 2) k
  let ρk : Representation k SL(2, K) (Fin m → k) := kRep ι R
  haveI : Nontrivial (Fin m → k) := by
    haveI : Nonempty (Fin m) := by
      by_contra h
      rw [not_nonempty_iff] at h
      haveI : Subsingleton (Fin m → ZMod 2) := inferInstance
      exact not_subsingleton V (c.toEquiv.subsingleton_congr.2 inferInstance)
    infer_instance
  haveI : FiniteDimensional k (Fin m → k) := inferInstance
  obtain ⟨S, hS, hSne, hSsimple⟩ := exists_simple_sub ρk
  have hx : ∀ x : Fin m → ZMod 2, R d *ᵥ (R d *ᵥ x) + R d *ᵥ x + x = 0 := by
    intro x
    obtain ⟨v, rfl⟩ := c.surjective x
    have := congrArg c (hdV v)
    rwa [map_add, map_add, hc, hc, map_zero] at this
  have hmat : R d * R d + R d + 1 = 0 := by
    refine (LinearEquiv.map_eq_zero_iff (Matrix.toLin' (R := ZMod 2) (n := Fin m)
      (m := Fin m))).1 (LinearMap.ext fun x => ?_)
    simp only [Matrix.toLin'_apply, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      LinearMap.zero_apply]
    exact hx x
  have hmatk : (R d).map ι * (R d).map ι + (R d).map ι + 1 = 0 := by
    have := congrArg (fun M : Matrix (Fin m) (Fin m) (ZMod 2) => M.map ι) hmat
    simpa [Matrix.map_mul, Matrix.map_add, Matrix.map_one _ (map_zero ι) (map_one ι)] using this
  have hdk : ∀ s : S, restrictRep ρk S hS d (restrictRep ρk S hS d s) +
      restrictRep ρk S hS d s + s = 0 := by
    intro s
    apply Subtype.ext
    have := congrArg (fun M : Matrix (Fin m) (Fin m) k => M *ᵥ (s : Fin m → k)) hmatk
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec,
      ← Matrix.mulVec_mulVec] at this
    simp only [Submodule.coe_add, Submodule.coe_zero, restrictRep_apply]
    rw [kRep_apply, kRep_apply]
    exact this
  obtain ⟨i, hi, β, hβ⟩ := simple_natural hn (restrictRep ρk S hS) hSsimple d hd3 hd1 hdk
  have hβs : ∀ (g : SL(2, K)) (w : Fin 2 → k),
      β.symm ((Amat i g : Matrix (Fin 2) (Fin 2) k) *ᵥ w) = restrictRep ρk S hS g (β.symm w) := by
    intro g w
    apply β.injective
    rw [hβ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let ι1' : (Fin 2 → K) →+ (Fin m → k) := AddMonoidHom.mk'
    (fun x => (β.symm (fun j => algebraMap K k (x j)) : S))
    (fun x y => by
      have : (fun j => algebraMap K k ((x + y) j)) =
          (fun j => algebraMap K k (x j)) + (fun j => algebraMap K k (y j)) := by
        funext j; simp
      rw [this, map_add]; rfl)
  have hι1_G : ∀ (g : SL(2, K)) (x : Fin 2 → K), ι1' ((AmatK i g) *ᵥ x) = ρk g (ι1' x) := by
    intro g x
    have h1 : (fun j => algebraMap K k ((AmatK i g *ᵥ x) j)) =
        (Amat i g : Matrix (Fin 2) (Fin 2) k) *ᵥ (fun j => algebraMap K k (x j)) := by
      funext j
      rw [Amat_eq_map_AmatK]
      exact RingHom.map_mulVec (algebraMap K k) (AmatK i g) x j
    show ((β.symm (fun j => algebraMap K k ((AmatK i g *ᵥ x) j)) : S) : Fin m → k) = _
    rw [h1, hβs]
    rfl
  have hι1_ne : ι1' (![1, 0]) ≠ 0 := by
    intro h
    have h0 : β.symm (fun j => algebraMap K k ((![1, 0] : Fin 2 → K) j)) = 0 :=
      Subtype.ext h
    have h00 := congrFun (β.symm.injective (h0.trans (map_zero _).symm)) 0
    simp at h00
  obtain ⟨j₀, hj₀⟩ : ∃ j, ι1' ![1, 0] j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hι1_ne (funext hcon)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ZMod 2) k, φ (ι1' ![1, 0] j₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hj₀ ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).1 hcon)
  let Λ : (Fin m → k) →+ (Fin m → ZMod 2) := AddMonoidHom.mk' (fun w j => φ (w j))
    (fun a b => by funext j; simp)
  have hΛ : ∀ (g : SL(2, K)) (w : Fin m → k), Λ (ρk g w) = R g *ᵥ Λ w := by
    intro g w
    funext j
    show φ ((((R g).map ι) *ᵥ w) j) = _
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have : ι (R g j l) * w l = (R g j l) • w l := (Algebra.smul_def _ _).symm
    rw [this, LinearMap.map_smul, smul_eq_mul]
    rfl
  let f : (Fin 2 → K) →+ V := c.symm.toAddMonoidHom.comp (Λ.comp ι1')
  have hf_G : ∀ (g : SL(2, K)) (x : Fin 2 → K), f ((AmatK i g) *ᵥ x) = ρ g (f x) := by
    intro g x
    show c.symm (Λ (ι1' (AmatK i g *ᵥ x))) = ρ g (c.symm (Λ (ι1' x)))
    rw [hι1_G, hΛ]
    apply c.injective
    rw [hc, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hfne : f ![1, 0] ≠ 0 := by
    intro h
    have h1 : Λ (ι1' ![1, 0]) = 0 := by
      have := c.symm.injective (h.trans (map_zero c.symm).symm)
      exact this
    exact hφ (congrFun h1 j₀)
  have hker : f.ker = ⊥ := by
    rcases natK_simple i f.ker (fun g w hw => by
        rw [AddMonoidHom.mem_ker] at hw ⊢
        rw [hf_G, hw, map_zero]) with h | h
    · exact h
    · exfalso
      apply hfne
      have : (![1, 0] : Fin 2 → K) ∈ f.ker := by rw [h]; exact AddSubgroup.mem_top _
      exact this
  have hinj : Function.Injective f := (AddMonoidHom.ker_eq_bot_iff f).1 hker
  have hrange : f.range = ⊤ := by
    have hst : ∀ (g : SL(2, K)), ∀ w ∈ zmod2Submodule f.range, ρ g w ∈ zmod2Submodule f.range := by
      intro g w hw
      obtain ⟨x, rfl⟩ := (AddMonoidHom.mem_range).1 hw
      exact (AddMonoidHom.mem_range).2 ⟨AmatK i g *ᵥ x, hf_G g x⟩
    rcases hsimple _ hst with h | h
    · exfalso
      apply hfne
      have : f ![1, 0] ∈ zmod2Submodule f.range := (AddMonoidHom.mem_range).2 ⟨_, rfl⟩
      rw [h] at this
      exact (Submodule.mem_bot _).1 this
    · rw [eq_top_iff]
      intro v _
      have : v ∈ zmod2Submodule f.range := by rw [h]; exact Submodule.mem_top
      exact this
  have hsurj : Function.Surjective f := AddMonoidHom.range_eq_top.1 hrange
  let e : (Fin 2 → K) ≃+ V := AddEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨i, hi, e.symm, fun g v => ?_⟩
  apply e.injective
  rw [AddEquiv.apply_symm_apply]
  show ρ g v = f (AmatK i g *ᵥ e.symm v)
  rw [hf_G]
  congr 1
  exact (e.apply_symm_apply v).symm

end Main

end CFSG.LocalAnalysis.UniquenessCase.UCK.Higman

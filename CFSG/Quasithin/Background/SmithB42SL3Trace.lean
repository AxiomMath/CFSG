module

public import CFSG.Quasithin.Background.SmithB42SL3Kron
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOrbit

public section

namespace CFSG.Quasithin

namespace B42SL3

open CFSG.QuasithinUnique.Setup.X7a Matrix
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply)
open CFSG.QuasithinUnique.Setup.X7b (toMatRep)
open scoped MatrixGroups Matrix

section Positions

variable {f : ℕ}

theorem trivial_of_not_mem {a b : Fin f → Bool} (hH : cntH a b = 0) {p : Fin f}
    (hp : a p = b p) : (a p, b p) = (false, false) := by
  have hpH : ¬ (a p = true ∧ b p = true) := by
    intro hab
    have : p ∈ Finset.univ.filter fun i => a i = true ∧ b i = true := by simp [hab]
    have h0 : (Finset.univ.filter fun i => a i = true ∧ b i = true).card = 0 := hH
    rw [Finset.card_eq_zero] at h0
    rw [h0] at this
    simp at this
  cases ha : a p <;> cases hb : b p <;> simp_all

theorem isSingle_of_ne {a b : Fin f → Bool} {p : Fin f} (hp : a p ≠ b p) :
    IsSingle (a p, b p) := by
  unfold IsSingle
  cases ha : a p <;> cases hb : b p <;> simp_all

theorem exists_single_pos {a b : Fin f → Bool} (hS : cntS a b = 1) (hH : cntH a b = 0) :
    ∃ i₀ : Fin f, IsSingle (a i₀, b i₀) ∧ ∀ p, p ≠ i₀ → (a p, b p) = (false, false) := by
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hS
  have hmem : ∀ p, a p ≠ b p ↔ p = i₀ := by
    intro p
    have := congrArg (fun s : Finset (Fin f) => p ∈ s) hi₀
    simpa using this
  refine ⟨i₀, isSingle_of_ne ((hmem i₀).mpr rfl), fun p hp => trivial_of_not_mem hH ?_⟩
  by_contra h
  exact hp ((hmem p).mp h)

theorem exists_two_pos {a b : Fin f → Bool} (hS : cntS a b = 2) (hH : cntH a b = 0) :
    ∃ i i' : Fin f, i ≠ i' ∧ IsSingle (a i, b i) ∧ IsSingle (a i', b i') ∧
      ∀ p, p ≠ i → p ≠ i' → (a p, b p) = (false, false) := by
  obtain ⟨i, i', hii', hset⟩ := Finset.card_eq_two.mp hS
  have hmem : ∀ p, a p ≠ b p ↔ p = i ∨ p = i' := by
    intro p
    have := congrArg (fun s : Finset (Fin f) => p ∈ s) hset
    simpa using this
  refine ⟨i, i', hii', isSingle_of_ne ((hmem i).mpr (Or.inl rfl)),
    isSingle_of_ne ((hmem i').mpr (Or.inr rfl)), fun p hp hp' => trivial_of_not_mem hH ?_⟩
  by_contra h
  rcases (hmem p).mp h with h1 | h1
  · exact hp h1
  · exact hp' h1

end Positions

section Stable

variable {F : Type} [Field F] [CharP F 2] [Fintype F]

theorem frK_surjective (j : ℕ) : Function.Surjective (frK F j : F →+* F) :=
  Finite.injective_iff_surjective.mp (frK_injective j)

theorem eq_top_of_stable (j : ℕ) (X : AddSubgroup (Fin 3 → F))
    (hX : ∀ g : SL(3, F), ∀ v ∈ X, twistMat F j g *ᵥ v ∈ X) (hne : X ≠ ⊥) : X = ⊤ := by
  classical
  have hup : ∀ x y z : F, ∀ v ∈ X, upMat x y z *ᵥ v ∈ X := by
    intro x y z v hv
    obtain ⟨x', rfl⟩ := frK_surjective (F := F) j x
    obtain ⟨y', rfl⟩ := frK_surjective (F := F) j y
    obtain ⟨z', rfl⟩ := frK_surjective (F := F) j z
    have := hX (up3 x' y' z') v hv
    rwa [twistMat_up3] at this
  have hlo : ∀ x y z : F, ∀ v ∈ X, u3Mat x y z *ᵥ v ∈ X := by
    intro x y z v hv
    obtain ⟨x', rfl⟩ := frK_surjective (F := F) j x
    obtain ⟨y', rfl⟩ := frK_surjective (F := F) j y
    obtain ⟨z', rfl⟩ := frK_surjective (F := F) j z
    have := hX (u3 x' y' z') v hv
    rwa [twistMat_u3] at this
  have hsub : ∀ M : Matrix (Fin 3) (Fin 3) F, (∀ v ∈ X, M *ᵥ v ∈ X) →
      ∀ v ∈ X, M *ᵥ v - v ∈ X := fun M hM v hv => X.sub_mem (hM v hv) hv
  have hfrom0 : (∀ c : F, Pi.single 0 c ∈ X) → X = ⊤ := by
    intro h0
    have h1 : ∀ c : F, Pi.single 1 c ∈ X := by
      intro c
      have := hsub _ (hlo c 0 0) _ (h0 1)
      convert this using 1
      funext k
      fin_cases k <;> simp [u3Mat]
    have h2 : ∀ c : F, Pi.single 2 c ∈ X := by
      intro c
      have := hsub _ (hlo 0 c 0) _ (h0 1)
      convert this using 1
      funext k
      fin_cases k <;> simp [u3Mat]
    rw [eq_top_iff]
    intro w _
    have hw : w = Pi.single 0 (w 0) + Pi.single 1 (w 1) + Pi.single 2 (w 2) := by
      funext k
      fin_cases k <;> simp
    rw [hw]
    exact X.add_mem (X.add_mem (h0 _) (h1 _)) (h2 _)
  obtain ⟨⟨v, hvX⟩, hv0'⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hne
  have hv0 : v ≠ 0 := fun h => hv0' (Subtype.ext h)
  apply hfrom0
  intro c
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · have h2 : v 2 ≠ 0 := by
        intro h2
        apply hv0
        ext k
        fin_cases k <;> simp [h0, h1, h2]
      have := hsub _ (hup 0 (c / v 2) 0) _ hvX
      convert this using 1
      funext k
      fin_cases k <;> simp [upMat, dotProduct, Fin.sum_univ_three, h0, h1,
        div_mul_cancel₀ c h2]
    · have := hsub _ (hup 0 0 (c / v 1)) _ hvX
      convert this using 1
      funext k
      fin_cases k <;> simp [upMat, dotProduct, Fin.sum_univ_three, h0,
        div_mul_cancel₀ c h1]
  ·
    have he2 : ∀ d : F, Pi.single 2 d ∈ X := by
      intro d
      have := hsub _ (hlo 0 (d / v 0) 0) _ hvX
      convert this using 1
      funext k
      fin_cases k <;> simp [u3Mat, dotProduct, Fin.sum_univ_three,
        div_mul_cancel₀ d h0]
    have := hsub _ (hup 0 c 0) _ (he2 1)
    convert this using 1
    funext k
    fin_cases k <;> simp [upMat]

end Stable

section Reindex

variable {F : Type} [Field F] [CharP F 2] {ι : Type} [Fintype ι] [DecidableEq ι]
  (τ : ι → Bool × Bool) (e : ι → ℕ) {i₀ : ι}

theorem tensorRepGen_apply_one (hrest : ∀ p, p ≠ i₀ → τ p = (false, false)) (g : SL(3, F))
    (y z : ∀ p, Fin (locDim (τ p).1 (τ p).2)) :
    tensorRepGen F τ e g y z = locRep F (τ i₀).1 (τ i₀).2 (e i₀) g (y i₀) (z i₀) := by
  rw [tensorRepGen_apply, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀),
    Finset.prod_eq_one, mul_one]
  intro p hp
  exact locRep_trivial_apply (hrest p (Finset.mem_erase.mp hp).1) (e p) g (y p) (z p)

omit [DecidableEq ι] [Fintype ι] in
theorem bijective_eval [DecidableEq ι] (hrest : ∀ p, p ≠ i₀ → τ p = (false, false)) :
    Function.Bijective (fun y : (∀ p, Fin (locDim (τ p).1 (τ p).2)) => y i₀) := by
  constructor
  · intro y z h
    funext p
    by_cases hp : p = i₀
    · subst hp
      exact h
    · exact (subsingleton_of_trivial (hrest p hp)).elim _ _
  · intro c
    let y₀ : ∀ p, Fin (locDim (τ p).1 (τ p).2) := fun p => ⟨0, locDim_pos _ _⟩
    exact ⟨Function.update y₀ i₀ c, Function.update_self _ _ _⟩

theorem nonempty_equiv_locRep (hrest : ∀ p, p ≠ i₀ → τ p = (false, false)) :
    Nonempty ((matRep (tensorRepGen (F := F) F τ e)).Equiv
      (matRep (locRep (F := F) F (τ i₀).1 (τ i₀).2 (e i₀)))) := by
  classical
  set σ := Equiv.ofBijective _ (bijective_eval τ hrest) with hσ
  refine ⟨Representation.Equiv.mk (LinearEquiv.funCongrLeft F F σ.symm) (fun g => ?_)⟩
  refine LinearMap.ext fun v => ?_
  funext c
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, matRep_apply]
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun z _ => ?_
  have h1 : (σ.symm c) i₀ = c := σ.apply_symm_apply c
  have h2 : σ z = z i₀ := rfl
  rw [tensorRepGen_apply_one τ e hrest, h1, h2, LinearMap.funLeft_apply, ← h2,
    Equiv.symm_apply_apply]

end Reindex

section Single

variable {F : Type} [Field F] [CharP F 2]

theorem exists_natRep_equiv {ℓ : Bool × Bool} (hℓ : IsSingle ℓ) (j : ℕ) :
    ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧
      Nonempty ((matRep (locRep (F := F) F ℓ.1 ℓ.2 j)).Equiv
        (matRep ((natRep (F := F) F j).comp ψ))) := by
  rcases hℓ with rfl | rfl
  · exact ⟨MonoidHom.id _, fun g => rfl, ⟨Representation.Equiv.refl _⟩⟩
  · refine ⟨tauSL F, tauSL_tauSL, ⟨?_⟩⟩
    have h : (natRep F j).comp (tauSL F) = locRep F false true j :=
      MonoidHom.ext fun g => natRep_tauSL (F := F) F j g
    rw [h]
    exact Representation.Equiv.refl _

end Single

section Trace

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

open Classical in
@[expose] noncomputable def trZ (f : ℕ) (x : F) : ZMod 2 :=
  if ∑ j ∈ Finset.range f, x ^ 2 ^ j = 0 then 0 else 1

theorem cast_trZ (hF : Fintype.card F = 2 ^ f) (x : F) :
    ZMod.castHom (dvd_refl 2) F (trZ f x) = ∑ j ∈ Finset.range f, x ^ 2 ^ j := by
  unfold trZ
  set t := ∑ j ∈ Finset.range f, x ^ 2 ^ j with ht
  have h2 : t ^ 2 = t := trace_sq hF x
  split_ifs with h0
  · rw [map_zero, h0]
  · rw [map_one]
    have : t * (t - 1) = 0 := by rw [mul_sub, mul_one, ← sq, h2, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h0
    · exact (sub_eq_zero.mp h).symm

omit [Fintype F] in
theorem frob_sum_add (x y : F) (j : ℕ) : (x + y) ^ 2 ^ j = x ^ 2 ^ j + y ^ 2 ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact add_pow_char_pow x y 2 j

theorem trZ_add (hF : Fintype.card F = 2 ^ f) (x y : F) :
    trZ f (x + y) = trZ f x + trZ f y := by
  apply (ZMod.castHom (dvd_refl 2) F).injective
  rw [map_add, cast_trZ hF, cast_trZ hF, cast_trZ hF, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => frob_sum_add x y j

theorem trZ_cast_mul (hF : Fintype.card F = 2 ^ f) (c : ZMod 2) (x : F) :
    trZ f (ZMod.castHom (dvd_refl 2) F c * x) = c * trZ f x := by
  apply (ZMod.castHom (dvd_refl 2) F).injective
  rw [map_mul, cast_trZ hF, cast_trZ hF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow]
  congr 1
  have hc : ∀ m : ℕ, c ^ 2 ^ m = c := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, pow_mul, ih]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact ZMod.pow_card c
  rw [← map_pow, hc]

theorem trZ_zero (hF : Fintype.card F = 2 ^ f) : trZ f (0 : F) = 0 := by
  have h := trZ_add hF (0 : F) 0
  rw [add_zero] at h
  calc trZ f (0 : F) = trZ f 0 + trZ f 0 := h
    _ = 0 := CharTwo.add_self_eq_zero _

theorem trZ_sum (hF : Fintype.card F = 2 ^ f) {ι : Type} (s : Finset ι) (x : ι → F) :
    trZ f (∑ i ∈ s, x i) = ∑ i ∈ s, trZ f (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using trZ_zero hF
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, trZ_add hF, ih]

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

theorem exists_addEquiv_of_sub (hF : Fintype.card F = 2 ^ f) {n : ℕ}
    (ρ : Representation (ZMod 2) SL(3, F) U) (bas : Module.Basis (Fin n) (ZMod 2) U)
    (hirr : ρ.IsIrreducible)
    (W₀ : Subrepresentation (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas))))
    {j : ℕ} {ψ : SL(3, F) →* SL(3, F)} (hψ : ∀ g, ψ (ψ g) = g)
    (e₀ : W₀.toRepresentation.Equiv (matRep ((natRep (F := F) F j).comp ψ))) :
    ∃ E : U ≃+ (Fin 3 → F), ∀ g u, E (ρ g u) = twistMat F j (ψ g) *ᵥ E u := by
  classical
  let ι : (Fin 3 → F) →ₗ[F] (Fin n → F) := W₀.toSubmodule.subtype ∘ₗ e₀.symm.toLinearMap
  have hι : ∀ g v, ι (twistMat F j (ψ g) *ᵥ v) =
      matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas) g *ᵥ ι v := by
    intro g v
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ e₀.symm.toIntertwiningMap g v
    show ((e₀.symm (twistMat F j (ψ g) *ᵥ v) : W₀.toSubmodule) : Fin n → F) = _
    have h2 : twistMat F j (ψ g) *ᵥ v = matRep ((natRep (F := F) F j).comp ψ) g v := rfl
    rw [h2]
    have h3 : e₀.symm (matRep ((natRep (F := F) F j).comp ψ) g v) =
        W₀.toRepresentation g (e₀.symm v) := h1
    rw [h3]
    rfl
  have hιinj : Function.Injective ι := by
    intro v w h
    exact e₀.symm.injective (Subtype.ext h)
  let h : (Fin 3 → F) →+ (Fin n → ZMod 2) :=
    { toFun := fun v k => trZ f (ι v k)
      map_zero' := by
        funext k
        simp [trZ_zero hF]
      map_add' := fun v w => by
        funext k
        simp [trZ_add hF] }
  have hh : ∀ g v, h (twistMat F j (ψ g) *ᵥ v) = toMatRep ρ bas g *ᵥ h v := by
    intro g v
    funext k
    show trZ f (ι (twistMat F j (ψ g) *ᵥ v) k) = (toMatRep ρ bas g *ᵥ fun k => trZ f (ι v k)) k
    rw [hι]
    simp only [matMap_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [trZ_sum hF]
    exact Finset.sum_congr rfl fun l _ => trZ_cast_mul hF _ _
  let H : (Fin 3 → F) →+ U := bas.equivFun.symm.toAddEquiv.toAddMonoidHom.comp h
  have hH : ∀ g v, H (twistMat F j (ψ g) *ᵥ v) = ρ g (H v) := by
    intro g v
    show bas.equivFun.symm (h (twistMat F j (ψ g) *ᵥ v)) = ρ g (bas.equivFun.symm (h v))
    rw [hh]
    apply bas.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    have := Representation.IntertwiningMap.isIntertwining _ _
      (CFSG.QuasithinUnique.Setup.X7b.matRepEquiv ρ bas).toIntertwiningMap g
      (bas.equivFun.symm (h v))
    have e1 : (CFSG.QuasithinUnique.Setup.X7b.matRepEquiv ρ bas).toIntertwiningMap
        (bas.equivFun.symm (h v)) = h v := by
      show bas.equivFun (bas.equivFun.symm (h v)) = h v
      rw [LinearEquiv.apply_symm_apply]
    rw [e1] at this
    exact this.symm
  have hH0 : ∃ v, H v ≠ 0 := by
    obtain ⟨b, hb⟩ := trace_exists hF
    have hne : ι (Pi.single 0 1) ≠ 0 := by
      intro h0
      have := hιinj (h0.trans (map_zero ι).symm)
      have h1 := congrFun this 0
      simp at h1
    obtain ⟨k, hk⟩ : ∃ k, ι (Pi.single 0 1) k ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (funext hcon)
    refine ⟨(b / ι (Pi.single 0 1) k) • Pi.single 0 1, fun h0 => ?_⟩
    have h1 : h ((b / ι (Pi.single 0 1) k) • Pi.single 0 1) = 0 := by
      apply bas.equivFun.symm.injective
      rw [map_zero]
      exact h0
    have h2 := congrFun h1 k
    change trZ f (ι ((b / ι (Pi.single 0 1) k) • Pi.single 0 1) k) = 0 at h2
    rw [map_smul, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ b hk] at h2
    apply hb
    rw [← cast_trZ hF, h2, map_zero]
  have hsurj : Function.Surjective H := by
    let R : Submodule (ZMod 2) U :=
      { carrier := Set.range H
        add_mem' := by
          rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
          exact ⟨v + w, map_add H v w⟩
        zero_mem' := ⟨0, map_zero H⟩
        smul_mem' := by
          rintro c _ ⟨v, rfl⟩
          fin_cases c
          · exact ⟨0, by rw [map_zero]; exact (zero_smul _ _).symm⟩
          · exact ⟨v, (one_smul _ _).symm⟩ }
    have hR : ∀ g, ∀ u ∈ R, ρ g u ∈ R := by
      rintro g _ ⟨v, rfl⟩
      obtain ⟨g', rfl⟩ : ∃ g', ψ g' = g := ⟨ψ g, hψ g⟩
      exact ⟨twistMat F j (ψ (ψ g')) *ᵥ v, by rw [hH]⟩
    rcases ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).2 R hR with h0 | h1
    · exfalso
      obtain ⟨v, hv⟩ := hH0
      have : H v ∈ R := ⟨v, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact hv this
    · intro u
      have : u ∈ R := by rw [h1]; exact Submodule.mem_top
      exact this
  have hinj : Function.Injective H := by
    rw [injective_iff_map_eq_zero]
    have hker := eq_top_of_stable (F := F) j H.ker (fun g v hv => by
      obtain ⟨g', rfl⟩ : ∃ g', ψ g' = g := ⟨ψ g, hψ g⟩
      show H (twistMat F j (ψ g') *ᵥ v) = 0
      rw [hH, show H v = 0 from hv, map_zero])
    by_contra hne
    push Not at hne
    obtain ⟨v, hv0, hv⟩ := hne
    have hk : H.ker ≠ ⊥ := by
      intro hbot
      have : v ∈ H.ker := hv0
      rw [hbot, AddSubgroup.mem_bot] at this
      exact hv this
    have htop := hker hk
    obtain ⟨w, hw⟩ := hH0
    exact hw (show w ∈ H.ker by rw [htop]; trivial)
  let E := (AddEquiv.ofBijective H ⟨hinj, hsurj⟩).symm
  refine ⟨E, fun g u => ?_⟩
  apply (AddEquiv.ofBijective H ⟨hinj, hsurj⟩).injective
  show H (E (ρ g u)) = H (twistMat F j (ψ g) *ᵥ E u)
  rw [hH]
  have h1 : H (E (ρ g u)) = ρ g u := (AddEquiv.ofBijective H ⟨hinj, hsurj⟩).apply_symm_apply _
  have h2 : H (E u) = u := (AddEquiv.ofBijective H ⟨hinj, hsurj⟩).apply_symm_apply _
  rw [h1, h2]

theorem exists_untwist (ρ : Representation (ZMod 2) SL(3, F) U) (j : ℕ)
    {ψ : SL(3, F) →* SL(3, F)} (E : U ≃+ (Fin 3 → F))
    (hE : ∀ g u, E (ρ g u) = twistMat F j (ψ g) *ᵥ E u) :
    ∃ E' : U ≃+ (Fin 3 → F), ∀ g u,
      E' (ρ g u) = ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E' u := by
  have hbij : Function.Bijective (frK F j : F →+* F) :=
    ⟨frK_injective j, frK_surjective j⟩
  let κ : F ≃+* F := RingEquiv.ofBijective (frK F j) hbij
  let K : (Fin 3 → F) ≃+ (Fin 3 → F) := AddEquiv.piCongrRight fun _ => κ.toAddEquiv
  have hK : ∀ (M : Matrix (Fin 3) (Fin 3) F) (v : Fin 3 → F),
      K (M *ᵥ v) = (frK F j).mapMatrix M *ᵥ K v := by
    intro M v
    funext a
    show frK F j ((M *ᵥ v) a) = ((frK F j).mapMatrix M *ᵥ fun b => frK F j (v b)) a
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, RingHom.mapMatrix_apply,
      Matrix.map_apply]
  refine ⟨E.trans K.symm, fun g u => ?_⟩
  apply K.injective
  show K (K.symm (E (ρ g u))) = K (((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
    K.symm (E u))
  rw [AddEquiv.apply_symm_apply, hK, AddEquiv.apply_symm_apply, hE]
  rfl

theorem exists_natural_of_single (hF : Fintype.card F = 2 ^ f) {n : ℕ}
    (ρ : Representation (ZMod 2) SL(3, F) U) (bas : Module.Basis (Fin n) (ZMod 2) U)
    (hirr : ρ.IsIrreducible) {a b : Fin f → Bool} (hS : cntS a b = 1) (hH : cntH a b = 0)
    (W₀ : Subrepresentation (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas))))
    (e₀ : W₀.toRepresentation.Equiv (matRep (tensorRep (F := F) F a b))) :
    ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧ ∃ E : U ≃+ (Fin 3 → F), ∀ g u,
      E (ρ g u) = ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E u := by
  obtain ⟨i₀, hsingle, hrest⟩ := exists_single_pos hS hH
  obtain ⟨e₁⟩ := nonempty_equiv_locRep (F := F) (fun i : Fin f => (a i, b i))
    (fun i => (i : ℕ)) (i₀ := i₀) hrest
  obtain ⟨ψ, hψ, ⟨e₂⟩⟩ := exists_natRep_equiv (F := F) hsingle (i₀ : ℕ)
  obtain ⟨E, hE⟩ := exists_addEquiv_of_sub hF ρ bas hirr W₀ hψ ((e₀.trans e₁).trans e₂)
  exact ⟨ψ, hψ, exists_untwist ρ (i₀ : ℕ) E hE⟩

omit [Fintype F] in
theorem quad_of_sub {n : ℕ} (ρ : Representation (ZMod 2) SL(3, F) U)
    (bas : Module.Basis (Fin n) (ZMod 2) U)
    (W₀ : Subrepresentation (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas))))
    {κ : Type} [Fintype κ] [DecidableEq κ] {T : SL(3, F) →* Matrix κ κ F}
    (e₀ : W₀.toRepresentation.Equiv (matRep T)) {t₁ t₂ : SL(3, F)}
    (h : (ρ t₂ - 1) ∘ₗ (ρ t₁ - 1) = 0) : (T t₂ - 1) * (T t₁ - 1) = 0 := by
  classical
  have h₀ : (toMatRep ρ bas t₂ - 1) * (toMatRep ρ bas t₁ - 1) = 0 := by
    have e : toMatRep ρ bas t₂ - 1 = LinearMap.toMatrix bas bas (ρ t₂ - 1) := by
      rw [map_sub, LinearMap.toMatrix_one]
      rfl
    have e' : toMatRep ρ bas t₁ - 1 = LinearMap.toMatrix bas bas (ρ t₁ - 1) := by
      rw [map_sub, LinearMap.toMatrix_one]
      rfl
    rw [e, e', ← LinearMap.toMatrix_comp, h, map_zero]
  have hF : (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas) t₂ - 1) *
      (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas) t₁ - 1) = 0 := by
    have := congrArg (fun M => (ZMod.castHom (dvd_refl 2) F).mapMatrix M) h₀
    simpa [matMap_apply, map_sub, map_mul] using this
  have hW : ∀ w : W₀.toSubmodule, W₀.toRepresentation t₂ (W₀.toRepresentation t₁ w - w) -
      (W₀.toRepresentation t₁ w - w) = 0 := by
    intro w
    apply Subtype.ext
    have := congrArg (fun M => M *ᵥ (w : Fin n → F)) hF
    simp only [Matrix.zero_mulVec] at this
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
    exact this
  have heq : ∀ g (w : W₀.toSubmodule), T g *ᵥ e₀ w = e₀ (W₀.toRepresentation g w) := by
    intro g w
    exact (Representation.IntertwiningMap.isIntertwining _ _ e₀.toIntertwiningMap g w).symm
  refine Matrix.ext_iff_mulVec.mpr fun x => ?_
  obtain ⟨w, rfl⟩ := EquivLike.surjective e₀ x
  rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.one_mulVec, heq, ← map_sub, heq, ← map_sub, hW, map_zero]

end Trace

end B42SL3

end CFSG.Quasithin

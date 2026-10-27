module

public import CFSG.LocalAnalysis.StandardType.GGTorusDCoordinates
public import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterD
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEven
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylFrame

@[expose] public noncomputable section

namespace CFSG.StandardType.DScalarTorus

open Multiplicative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p N : ℕ} [Fact p.Prime]

private def coordAddEquiv (p N : ℕ) :
    Additive (Fin N → Multiplicative (ZMod p)) ≃+ (Fin N → ZMod p) :=
  MulEquiv.toAdditiveLeft (MulEquiv.piMultiplicative fun _ : Fin N => ZMod p).symm

private theorem lin_basis_iff {a : MulAut (Fin N → Multiplicative (ZMod p))}
    (σ : Equiv.Perm (Fin N)) (c : Fin N → ZMod p) :
    (∀ i, ggLin (p := p) (coordAddEquiv p N) a (Pi.basisFun (ZMod p) (Fin N) i) =
      c i • Pi.basisFun (ZMod p) (Fin N) (σ i)) ↔
    ∀ f i, toAdd (a f (σ i)) = c i * toAdd (f i) := by
  constructor
  · intro hb f i
    let v : Fin N → ZMod p := fun j => toAdd (f j)
    have hv : ∀ j, ggLin (p := p) (coordAddEquiv p N) a v j = toAdd (a f j) := fun j => rfl
    rw [← hv]
    conv_lhs => rw [← Module.Basis.sum_repr (Pi.basisFun (ZMod p) (Fin N)) v]
    simp only [map_sum, map_smul]
    simp only [hb]
    simp only [Pi.basisFun_repr, Finset.sum_apply, Pi.smul_apply,
      Pi.basisFun_apply, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp [v, mul_comm]
    · intro j _ hji
      simp [Ne.symm (σ.injective.ne hji)]
    · simp
  · intro h i
    funext j
    have hj : j = σ (σ.symm j) := (σ.apply_symm_apply j).symm
    rw [hj]
    change toAdd (a (fun k => ofAdd ((Pi.basisFun (ZMod p) (Fin N) i) k))
      (σ (σ.symm j))) = _
    rw [h]
    simp only [toAdd_ofAdd, Pi.basisFun_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases hij : σ.symm j = i
    · subst i
      simp
    · have hji : j ≠ σ i := by
        intro hji
        exact hij (by rw [hji, Equiv.symm_apply_apply])
      simp [hij, hji]

theorem exists_coxeterEquiv (hp2 : p ≠ 2) (hN : 4 ≤ N)
    (A : Subgroup (MulAut (Fin N → Multiplicative (ZMod p))))
    (hA : ∀ a, a ∈ A ↔ ∃ (σ : Equiv.Perm (Fin N)) (c : Fin N → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧
        ∀ f i, toAdd (a f (σ i)) = c i * toAdd (f i)) :
    ∃ e : (ggCoxeterMatrixD N).Group ≃* A, ∀ i,
      (e ((ggCoxeterMatrixD N).simple i) : MulAut (Fin N → Multiplicative (ZMod p))) =
        simpleReflection hN i := by
  classical
  let ι := coordAddEquiv p N
  let L := ggLin (p := p) ι
  have hL : Function.Injective L := ggLin_injective ι
  let AL := A.map L
  have hAL : ∀ u, u ∈ AL ↔ ∃ (σ : Equiv.Perm (Fin N)) (c : Fin N → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧
        ∀ i, u (Pi.basisFun (ZMod p) (Fin N) i) =
          c i • Pi.basisFun (ZMod p) (Fin N) (σ i) := by
    intro u
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨σ, c, hc, hprod, hf⟩ := (hA a).mp ha
      exact ⟨σ, c, hc, hprod, (lin_basis_iff σ c).mpr hf⟩
    · rintro ⟨σ, c, hc, hprod, hb⟩
      let pi := MulEquiv.piMultiplicative fun _ : Fin N => ZMod p
      let a : MulAut (Fin N → Multiplicative (ZMod p)) :=
        MulAut.congr pi (AddEquiv.toMultiplicative u.toAddEquiv)
      have hLa : L a = u := LinearEquiv.ext fun v => rfl
      refine ⟨a, (hA a).mpr ⟨σ, c, hc, hprod, ?_⟩, hLa⟩
      apply (lin_basis_iff σ c).mp
      rwa [show ggLin (p := p) (coordAddEquiv p N) a = u from hLa]
  obtain ⟨eL, heL⟩ := ggRC_coxeterD_equiv_evenSigned hp2 hN
    (Pi.basisFun (ZMod p) (Fin N)) AL hAL
  let eA : A ≃* AL := A.equivMapOfInjective L hL
  refine ⟨eL.trans eA.symm, ?_⟩
  intro i
  apply hL
  have he : L ((eL.trans eA.symm) ((ggCoxeterMatrixD N).simple i)) =
      (eL ((ggCoxeterMatrixD N).simple i) : (Fin N → ZMod p) ≃ₗ[ZMod p] (Fin N → ZMod p)) := by
    exact congrArg Subtype.val (eA.apply_symm_apply (eL ((ggCoxeterMatrixD N).simple i)))
  rw [he, heL]
  apply LinearEquiv.ext
  intro v
  have hb : ∀ j, (if hi : i.val = N - 1 then
      ZS.permMap p (Pi.basisFun (ZMod p) (Fin N))
        (Equiv.swap ⟨N - 2, by omega⟩ ⟨N - 1, by omega⟩) *
        ZS.diagMap p (Pi.basisFun (ZMod p) (Fin N)) (fun k =>
          if k = (⟨N - 2, by omega⟩ : Fin N) ∨ k = ⟨N - 1, by omega⟩ then -1 else 1)
      else ZS.permMap p (Pi.basisFun (ZMod p) (Fin N))
        (Equiv.swap i ⟨i.val + 1, by have := i.isLt; omega⟩))
        (Pi.basisFun (ZMod p) (Fin N) j) =
      L (simpleReflection hN i) (Pi.basisFun (ZMod p) (Fin N) j) := by
    intro j
    by_cases hi : i.val + 1 < N
    · have hlast : i.val ≠ N - 1 := by omega
      rw [dif_neg hlast, simpleReflection, dif_pos hi]
      rw [ZS.permMap, Module.Basis.equiv_apply]
      symm
      have hlin := (lin_basis_iff (p := p)
        (a := SpCoord.permAut (Equiv.swap i ⟨i.val + 1, hi⟩))
        (Equiv.swap i ⟨i.val + 1, hi⟩) (fun _ => 1)).mpr
          (fun f k => by simp [SpCoord.permAut_apply, Equiv.swap_inv])
      simpa only [one_smul] using hlin j
    · have hlast : i.val = N - 1 := by have := i.isLt; omega
      rw [dif_pos hlast, simpleReflection, dif_neg hi]
      let s : Equiv.Perm (Fin N) := Equiv.swap ⟨N - 2, by omega⟩ ⟨N - 1, by omega⟩
      let d : Fin N → (ZMod p)ˣ := fun k =>
        if k = (⟨N - 2, by omega⟩ : Fin N) ∨ k = ⟨N - 1, by omega⟩ then -1 else 1
      have hdiag : ZS.diagMap p (Pi.basisFun (ZMod p) (Fin N)) d
          (Pi.basisFun (ZMod p) (Fin N) j) =
          (d j : ZMod p) • Pi.basisFun (ZMod p) (Fin N) j := by
        simp only [ZS.diagMap, LinearEquiv.trans_apply, Pi.basisFun_equivFun,
          LinearEquiv.refl_symm, LinearEquiv.refl_apply]
        funext k
        simp only [LinearEquiv.piCongrRight_apply, LinearEquiv.smulOfUnit,
          DistribMulAction.toLinearEquiv_apply, Units.smul_def,
          Pi.smul_apply, smul_eq_mul, Pi.basisFun_apply]
        change (d k : ZMod p) * ((Pi.single j (1 : ZMod p) : Fin N → ZMod p) k) =
          (d j : ZMod p) * ((Pi.single j (1 : ZMod p) : Fin N → ZMod p) k)
        by_cases hkj : j = k
        · subst k
          rfl
        · simp [Ne.symm hkj]
      have hsgn : ∀ (f : Fin N → Multiplicative (ZMod p)) (k : Fin N),
          toAdd (((SpCoord.sgnAut ⟨N - 2, by omega⟩ *
          SpCoord.sgnAut ⟨N - 1, by omega⟩ * SpCoord.permAut s) :
            MulAut (Fin N → Multiplicative (ZMod p)))
            f (s k)) = (d k : ZMod p) * toAdd (f k) := by
        intro f k
        have hlast' : (⟨N - 2, by omega⟩ : Fin N) ≠ ⟨N - 1, by omega⟩ :=
          Fin.ne_of_val_ne (by simp; omega)
        simp only [MulAut.mul_apply, SpCoord.sgnAut_apply, SpCoord.permAut_apply,
          Function.comp_apply, Function.update_apply, s, Equiv.swap_inv, Equiv.swap_apply_self]
        by_cases hk2 : k = (⟨N - 2, by omega⟩ : Fin N)
        · subst k
          simp [d, Equiv.swap_apply_left, hlast', Ne.symm hlast']
        · by_cases hk1 : k = (⟨N - 1, by omega⟩ : Fin N)
          · subst k
            simp [d, Equiv.swap_apply_right, hlast', Ne.symm hlast']
          · simp [d, hk2, hk1, Equiv.swap_apply_of_ne_of_ne hk2 hk1]
      have hlin := (lin_basis_iff (p := p)
        (a := SpCoord.sgnAut ⟨N - 2, by omega⟩ *
          SpCoord.sgnAut ⟨N - 1, by omega⟩ * SpCoord.permAut s) s
        (fun k => (d k : ZMod p))).mpr hsgn
      change (ZS.permMap p (Pi.basisFun (ZMod p) (Fin N)) s *
        ZS.diagMap p (Pi.basisFun (ZMod p) (Fin N)) d)
        (Pi.basisFun (ZMod p) (Fin N) j) = _
      rw [LinearEquiv.mul_apply, hdiag, map_smul, ZS.permMap, Module.Basis.equiv_apply]
      exact (hlin j).symm
  have hlin := (Pi.basisFun (ZMod p) (Fin N)).ext hb
  exact congrArg (fun f : (Fin N → ZMod p) →ₗ[ZMod p] (Fin N → ZMod p) => f v) hlin

end CFSG.StandardType.DScalarTorus

namespace CFSG.StandardType.DScalarTorus

open Multiplicative SpCoord

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p N : ℕ} [Fact p.Prime]

def evenSignedGroup : Subgroup (MulAut (Fin N → Multiplicative (ZMod p))) where
  carrier := {a | ∃ (σ : Equiv.Perm (Fin N)) (c : Fin N → ZMod p),
    (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧
      ∀ f i, toAdd (a f (σ i)) = c i * toAdd (f i)}
  one_mem' := ⟨1, 1, fun _ => Or.inl rfl, by simp, fun _ _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨σ, c, hc, hcp, ha⟩ ⟨τ, d, hd, hdp, hb⟩
    refine ⟨σ * τ, fun i => c (τ i) * d i, ?_, ?_, ?_⟩
    · intro i
      change c (τ i) * d i = 1 ∨ c (τ i) * d i = -1
      rcases hc (τ i) with h | h <;> rcases hd i with h' | h' <;>
        rw [h, h'] <;> norm_num
    · rw [Finset.prod_mul_distrib, Equiv.prod_comp, hcp, hdp, mul_one]
    · intro f i
      rw [MulAut.mul_apply, Equiv.Perm.mul_apply, ha, hb, mul_assoc]
  inv_mem' := by
    rintro a ⟨σ, c, hc, hcp, ha⟩
    refine ⟨σ.symm, fun i => c (σ.symm i), fun i => hc (σ.symm i), ?_, ?_⟩
    · rw [Equiv.prod_comp, hcp]
    · intro f i
      have h := ha (a⁻¹ f) (σ.symm i)
      rw [Equiv.apply_symm_apply] at h
      have haaf : a (a⁻¹ f) = f := a.apply_symm_apply f
      rw [haaf] at h
      rw [h, ← mul_assoc, coord_sign_mul_self (hc _), one_mul]

theorem permAut_mem_evenSignedGroup (σ : Equiv.Perm (Fin N)) :
    permAut (p := p) σ ∈ evenSignedGroup (p := p) :=
  ⟨σ, 1, fun _ => Or.inl rfl, by simp,
    fun f i => by simp [permAut_apply]⟩

theorem sgnAut_pair_mem_evenSignedGroup {i j : Fin N} (hij : i ≠ j) :
    (sgnAut i * sgnAut j : MulAut (Fin N → Multiplicative (ZMod p))) ∈
      evenSignedGroup (p := p) := by
  classical
  let c : Fin N → ZMod p := fun k => if k = i ∨ k = j then -1 else 1
  refine ⟨1, c, fun k => by dsimp [c]; split_ifs <;> simp, ?_, ?_⟩
  · have he : c = fun k => (if k = i then (-1 : ZMod p) else 1) *
        (if k = j then -1 else 1) := by
      funext k
      by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all [c]
    rw [he, Finset.prod_mul_distrib]
    simp
  · intro f k
    simp only [Equiv.Perm.one_apply, MulAut.mul_apply, sgnAut_apply, Function.update_apply]
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [c, toAdd_inv]

theorem evenSignedGroup_le {H : Subgroup (MulAut (Fin N → Multiplicative (ZMod p)))}
    (hp2 : p ≠ 2) (hd : ∀ i j : Fin N, i ≠ j → sgnAut i * sgnAut j ∈ H)
    (ht : ∀ σ : Equiv.Perm (Fin N), permAut σ ∈ H) : evenSignedGroup ≤ H := by
  classical
  rintro a ⟨σ, c, hc, hcp, ha⟩
  set S := Finset.univ.filter fun i => c i = -1 with hS
  have he : ∏ i, c i = (-1 : ZMod p) ^ S.card := by
    have hc' : c = fun i => if i ∈ S then (-1 : ZMod p) else 1 := by
      funext i
      by_cases hi : i ∈ S
      · simp only [if_pos hi]
        exact (Finset.mem_filter.mp hi).2
      · simp only [if_neg hi]
        exact (hc i).resolve_right (by simpa [hS] using hi)
    rw [hc', Finset.prod_ite_mem_eq, Finset.prod_const]
  have hneg : (-1 : ZMod p) ≠ 1 := by
    intro h
    have htwo := zmod_two_ne_zero hp2
    apply htwo
    have h' := congrArg (fun x : ZMod p => x + 1) h
    simpa only [neg_add_cancel, ← two_mul, mul_one] using h'.symm
  obtain ⟨n, hn⟩ := (neg_one_pow_eq_one_iff_even hneg).mp (he.symm.trans hcp)
  let u : MulAut (Fin N → Multiplicative (ZMod p)) := (permAut σ)⁻¹ * a
  have hu : ∀ f i, toAdd (u f i) = c i * toAdd (f i) := by
    intro f i
    simpa only [u, MulAut.mul_apply, permAut_inv_apply, Function.comp_apply] using ha f i
  have huH : u ∈ H := OrthExcEven.mem_of_diag_even hd n S (by omega) u c
    (fun i hi => (hc i).resolve_right (by simpa [hS] using hi))
    (fun i hi => (Finset.mem_filter.mp hi).2) hu
  have haeq : a = permAut σ * u := by dsimp [u]; group
  rw [haeq]
  exact H.mul_mem (ht σ) huH

theorem exists_evenSignedCoxeterEquiv (hp2 : p ≠ 2) (hN : 4 ≤ N) :
    ∃ e : (ggCoxeterMatrixD N).Group ≃* evenSignedGroup (p := p) (N := N), ∀ i,
      (e ((ggCoxeterMatrixD N).simple i) : MulAut (Fin N → Multiplicative (ZMod p))) =
        simpleReflection hN i :=
  exists_coxeterEquiv hp2 hN _ fun _ => Iff.rfl

theorem exists_markedAutomizer {G : Type} [Group G] (hp2 : p ≠ 2) (hN : 4 ≤ N)
    (τ : (Fin N → Multiplicative (ZMod p)) →* G) (hτ : Function.Injective τ)
    (n : Fin N → G)
    (hn : ∀ i f, n i * τ f * (n i)⁻¹ = τ (simpleReflection hN i f))
    (hNsig : ∀ g ∈ Subgroup.normalizer (τ.range : Set G),
      ∀ u : MulAut (Fin N → Multiplicative (ZMod p)),
        (∀ f, g * τ f * g⁻¹ = τ (u f)) → IsSignedPerm u)
    (hno : ∀ g : G, ∀ i : Fin N,
      (∀ f, g * τ f * g⁻¹ = τ (sgnAut i f)) → False) :
    ∃ hnN : ∀ i, n i ∈ Subgroup.normalizer (τ.range : Set G),
      ∃ e : (ggCoxeterMatrixD N).Group ≃* ↥(ggAutomizer (⊤ : Subgroup G) τ.range),
        ∀ i, (e ((ggCoxeterMatrixD N).simple i) : MulAut ↥τ.range) =
          ggConjAut τ.range (hnN i) := by
  classical
  let κ : (Fin N → Multiplicative (ZMod p)) ≃* τ.range := MonoidHom.ofInjective hτ
  have hκ : ∀ f, (κ f : G) = τ f := fun _ => MonoidHom.ofInjective_apply hτ
  obtain ⟨eS, heS⟩ := exists_evenSignedCoxeterEquiv hp2 hN
  let ρ : (ggCoxeterMatrixD N).Group →* MulAut ↥τ.range :=
    (MulAut.congr κ).toMonoidHom.comp (evenSignedGroup.subtype.comp eS.toMonoidHom)
  have hρ : Function.Injective ρ :=
    (MulAut.congr κ).injective.comp (evenSignedGroup.subtype_injective.comp eS.injective)
  have hnN : ∀ i, n i ∈ Subgroup.normalizer (τ.range : Set G) := by
    intro i
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨simpleReflection hN i f, (hn i f).symm⟩
    · rintro ⟨f, hf⟩
      obtain ⟨f', hf'⟩ := (simpleReflection hN i).surjective f
      refine ⟨f', ?_⟩
      have heq : n i * τ f' * (n i)⁻¹ = n i * x * (n i)⁻¹ := by
        rw [hn, hf', hf]
      exact (MulAut.conj (n i)).injective heq
  have hρsimple : ∀ i, ρ ((ggCoxeterMatrixD N).simple i) = ggConjAut τ.range (hnN i) := by
    intro i
    apply MulEquiv.ext
    intro a
    obtain ⟨f, rfl⟩ := κ.surjective a
    apply Subtype.ext
    change (κ (((eS ((ggCoxeterMatrixD N).simple i) : evenSignedGroup) :
      MulAut (Fin N → Multiplicative (ZMod p))) (κ.symm (κ f))) : G) = _
    rw [MulEquiv.symm_apply_apply, heS, hκ, ggConjAut_apply, hκ, hn]
  have hρle : ρ.range ≤ ggAutomizer (⊤ : Subgroup G) τ.range := by
    have hgen : Subgroup.closure (Set.range (ggCoxeterMatrixD N).simple) = ⊤ := by
      simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
        (ggCoxeterMatrixD N).toCoxeterSystem.subgroup_closure_range_simple
    have hle : Subgroup.closure (Set.range (ggCoxeterMatrixD N).simple) ≤
        (ggAutomizer (⊤ : Subgroup G) τ.range).comap ρ := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      change ρ ((ggCoxeterMatrixD N).simple i) ∈ ggAutomizer (⊤ : Subgroup G) τ.range
      rw [hρsimple]
      exact ggConjAut_mem_ggAutomizer (Subgroup.mem_top _) (hnN i)
    rintro _ ⟨w, rfl⟩
    exact hle (by rw [hgen]; trivial)
  have hρrange : ρ.range = ggAutomizer (⊤ : Subgroup G) τ.range := by
    refine le_antisymm hρle ?_
    intro a ha
    obtain ⟨g, -, hg, hga⟩ := mem_ggAutomizer_iff.mp ha
    let u : MulAut (Fin N → Multiplicative (ZMod p)) := (MulAut.congr κ).symm a
    have hau : a = MulAut.congr κ u := (MulEquiv.apply_symm_apply _ a).symm
    have hgu : ∀ f, g * τ f * g⁻¹ = τ (u f) := by
      intro f
      have h := hga (κ f)
      rw [hau, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, hκ, hκ] at h
      exact h.symm
    have hu : IsSignedPerm u := hNsig g hg u hgu
    let i₀ : Fin N := ⟨0, by omega⟩
    rcases OrthExcEven.mem_or_mul_mem_of_isSignedPerm
      (fun i j hij => sgnAut_pair_mem_evenSignedGroup hij)
      (fun i j _ => permAut_mem_evenSignedGroup (Equiv.swap i j)) i₀ hu with huS | huS
    · refine ⟨eS.symm ⟨u, huS⟩, ?_⟩
      change MulAut.congr κ ↑(eS (eS.symm ⟨u, huS⟩)) = a
      rw [MulEquiv.apply_symm_apply]
      exact hau.symm
    · have hus : MulAut.congr κ (u * sgnAut i₀) ∈ ggAutomizer (⊤ : Subgroup G) τ.range := by
        apply hρle
        refine ⟨eS.symm ⟨u * sgnAut i₀, huS⟩, ?_⟩
        change MulAut.congr κ ↑(eS (eS.symm ⟨u * sgnAut i₀, huS⟩)) = _
        rw [MulEquiv.apply_symm_apply]
      have hsi : MulAut.congr κ (sgnAut i₀) ∈ ggAutomizer (⊤ : Subgroup G) τ.range := by
        have h := (ggAutomizer (⊤ : Subgroup G) τ.range).mul_mem
          ((ggAutomizer (⊤ : Subgroup G) τ.range).inv_mem ha) hus
        rw [hau, ← map_inv, ← map_mul] at h
        simpa only [inv_mul_cancel_left] using h
      obtain ⟨g', -, -, hg'⟩ := mem_ggAutomizer_iff.mp hsi
      exact (hno g' i₀ (fun f => by
        have h := hg' (κ f)
        rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply, hκ, hκ] at h
        exact h.symm)).elim
  let e : (ggCoxeterMatrixD N).Group ≃* ↥(ggAutomizer (⊤ : Subgroup G) τ.range) :=
    (MonoidHom.ofInjective hρ).trans (MulEquiv.subgroupCongr hρrange)
  refine ⟨hnN, e, ?_⟩
  intro i
  change ρ ((ggCoxeterMatrixD N).simple i) = ggConjAut τ.range (hnN i)
  exact hρsimple i

theorem exists_ggTorusTorWit_of_planeCoordinates {m : ℕ} {G : Type} [Group G]
    {μ : Type} [CommGroup μ] (hp2 : p ≠ 2) (hm : Odd m) (hN : 4 ≤ N)
    (l : μ ≃* Multiplicative (ZMod m)) (D : (Fin N → μ) →* G) (hD : Function.Injective D)
    (τ : (Fin N → Multiplicative (ZMod p)) →* G) (hτ : Function.Injective τ)
    (hE : ∀ g, g ∈ τ.range ↔ g ^ p = 1 ∧ g ∈ D.range)
    (ζ : μ) (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1) (n : Fin N → G)
    (hnfull : ∀ i a, n i * D a * (n i)⁻¹ =
      D (a * (corTuple (Matrix.of (TauCeti.DynkinType.typeDSimpleRoot N hN))
        i (rootCoordinates hN a i))⁻¹))
    (hnprime : ∀ i f, n i * τ f * (n i)⁻¹ = τ (simpleReflection hN i f))
    (hZ : Subgroup.center G = ⊥) (hcent : Subgroup.centralizer (τ.range : Set G) ≤ D.range)
    (hNsig : ∀ g ∈ Subgroup.normalizer (τ.range : Set G),
      ∀ u : MulAut (Fin N → Multiplicative (ZMod p)),
        (∀ f, g * τ f * g⁻¹ = τ (u f)) → IsSignedPerm u)
    (hno : ∀ g : G, ∀ i : Fin N,
      (∀ f, g * τ f * g⁻¹ = τ (sgnAut i f)) → False) :
    ∃ w : GGTorusTorWit m N G (scalarA τ.range),
      w.Holds (CartanMatrix.D N) (ggCoxeterMatrixD N) ∧
        w.Tsc = D.range ∧ (∀ i, w.n i = n i) ∧
        (∀ i z, w.cor i z =
          D (corTuple (Matrix.of (TauCeti.DynkinType.typeDSimpleRoot N hN)) i (l.symm z))) ∧
        (∀ a ∈ w.T, ∃ t ∈ w.Tsc, a = MulAut.conj t) ∧ Odd (Nat.card w.Tsc) := by
  classical
  have : NeZero m := ⟨hm.pos.ne'⟩
  let R := rootCoordinateEquiv hN hm l
  let φ := D.comp R.symm.toMonoidHom
  have hφ : Function.Injective φ := hD.comp R.symm.injective
  have hφrange : φ.range = D.range := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨R.symm a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨R a, by change D (R.symm (R a)) = _; rw [R.symm_apply_apply]⟩
  have hRcor : ∀ i z, R.symm (corTuple (CartanMatrix.D N).transpose i z) =
      corTuple (Matrix.of (TauCeti.DynkinType.typeDSimpleRoot N hN)) i z := by
    intro i z
    apply R.injective
    rw [MulEquiv.apply_symm_apply, rootCoordinateEquiv_apply, rootCoordinates_corTuple]
  have hnformula : ∀ i a, n i * φ a * (n i)⁻¹ =
      φ a * (φ (corTuple (CartanMatrix.D N).transpose i (a i)))⁻¹ := by
    intro i a
    have hRa : rootCoordinates hN (R.symm a) = a := by
      rw [← rootCoordinateEquiv_apply hN hm l,
        ← show rootCoordinateEquiv hN hm l = R from rfl, MulEquiv.apply_symm_apply]
    change n i * D (R.symm a) * (n i)⁻¹ = _
    rw [hnfull, hRa]
    change D (R.symm a * _) = D (R.symm a) * (D (R.symm _))⁻¹
    rw [hRcor, map_mul, map_inv]
  obtain ⟨hnN, eW, heW⟩ := exists_markedAutomizer hp2 hN τ hτ n hnprime hNsig hno
  obtain ⟨hnA, eA, heA⟩ := markedWeyl_innerImage τ.range
    (CFSG.mulAutConj_injective_of_center_eq_bot hZ) n hnN eW heW
  let ρ : (ggCoxeterMatrixD N).Group →* MulAut ↥(scalarA τ.range) :=
    (ggAutomizer (MulAut.conj : G →* MulAut G).range (scalarA τ.range)).subtype.comp
      eA.toMonoidHom
  have hρrange : ρ.range = ggAutomizer (MulAut.conj : G →* MulAut G).range (scalarA τ.range) := by
    ext a
    constructor
    · rintro ⟨w, rfl⟩
      exact (eA w).2
    · intro ha
      obtain ⟨w, hw⟩ := eA.surjective ⟨a, ha⟩
      exact ⟨w, congrArg Subtype.val hw⟩
  have hρsimple : ∀ i (a : ↥(scalarA τ.range)),
      ((ρ ((ggCoxeterMatrixD N).simple i) a : ↥(scalarA τ.range)) : MulAut G) =
        MulAut.conj (n i) * a * (MulAut.conj (n i))⁻¹ := by
    intro i a
    change (((eA ((ggCoxeterMatrixD N).simple i) : MulAut ↥(scalarA τ.range)) a :
      ↥(scalarA τ.range)) : MulAut G) = _
    rw [heA, ggConjAut_apply]
  obtain ⟨B, hCB, hBC⟩ := exists_int_matrix_inverse_mod_D (by omega : 2 ≤ N) hm
  obtain ⟨w, hwT, hwTsc, hwcor, hwn, hw⟩ := exists_ggTorusTorWit_of_scalarRootCoordinates_columns_mod
    l φ hφ (CartanMatrix.D N) B hCB hBC hZ τ.range
    (fun g => by rw [hφrange]; exact hE g) ζ hζp hζ1 n hnA hnformula
    (hφrange.symm ▸ hcent) (ggCoxeterMatrixD N) ρ
    ((ggAutomizer _ _).subtype_injective.comp eA.injective) hρrange hρsimple
  refine ⟨w, hw, hwTsc.trans hφrange, hwn, ?_, ?_, ?_⟩
  · intro i z
    rw [hwcor]
    change D (R.symm (corTuple (CartanMatrix.D N).transpose i (l.symm z))) = _
    rw [hRcor]
  · rw [hwT, hwTsc]
    rintro _ ⟨a, rfl⟩
    exact ⟨φ a, ⟨a, rfl⟩, rfl⟩
  · rw [hwTsc, hφrange, Nat.card_congr (MonoidHom.ofInjective hD).toEquiv.symm,
      Nat.card_fun, Nat.card_congr l.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod m) ≃ ZMod m),
      Nat.card_zmod, Nat.card_fin]
    exact hm.pow

end CFSG.StandardType.DScalarTorus

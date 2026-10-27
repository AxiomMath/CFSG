module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusion
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityMain

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace LinTorus

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]

theorem conjSL_scalar (c : Fˣ) (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL (GeneralLinearGroup.scalar (Fin (m + 1)) c) u = u := by
  apply Subtype.ext
  rw [InnerDiagA.coe_conjSL, ← map_inv, GeneralLinearGroup.coe_scalar,
    GeneralLinearGroup.coe_scalar]
  ext a b
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    mul_right_comm, Units.mul_inv, one_mul]

theorem one_scalar_mem_ggInducedPairs (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (c : Fˣ) :
    ((1 : G), GeneralLinearGroup.scalar (Fin (m + 1)) c) ∈ LinFusion.ggInducedPairs ψ :=
  LinFusion.mem_ggInducedPairs.mpr fun u => by rw [one_mul, inv_one, mul_one, conjSL_scalar]

theorem transvection_mul_self [CharP F 2] {i j : Fin (m + 1)} (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.transvection hij (1 : F) *
      Matrix.SpecialLinearGroup.transvection hij 1 = 1 := by
  ext a b
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.coe_one]
  change (Matrix.transvection i j (1 : F) * Matrix.transvection i j 1 :
    Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b
  rw [transvection_mul_transvection_same _ _ hij, CharTwo.add_self_eq_zero, transvection_zero]

theorem exists_unit_of_coe_eq_scalar {A : GL (Fin (m + 1)) F} {c : F}
    (hA : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.scalar (Fin (m + 1)) c) :
    ∃ u : Fˣ, A = GeneralLinearGroup.scalar (Fin (m + 1)) u := by
  have hc0 : c ≠ 0 := by
    intro hc
    have h1 : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        ((A⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hA, hc, map_zero, Matrix.zero_mul] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simp at h2
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, hA, Units.val_mk0]

theorem exists_scalar_of_mem_ggInducedPairs_one [CharP F 2]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {B : GL (Fin (m + 1)) F} (hB : ((1 : G), B) ∈ LinFusion.ggInducedPairs ψ) :
    ∃ c : Fˣ, B = GeneralLinearGroup.scalar (Fin (m + 1)) c := by
  have hcomm : ∀ i j : Fin (m + 1), i ≠ j →
      Commute (single i j (1 : F)) (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    intro i j hij
    set t := Matrix.SpecialLinearGroup.transvection hij (1 : F) with ht
    set s := InnerDiagA.conjSL B t with hs
    have h1 : ψ s = ψ t := by
      have h := LinFusion.mem_ggInducedPairs.mp hB t
      rw [one_mul, inv_one, mul_one] at h
      exact h.symm
    set z := s⁻¹ * t with hz
    have hzc : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) :=
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel])
    have ht2 : t * t = 1 := transvection_mul_self hij
    have hs2 : s * s = 1 := by rw [hs, ← map_mul, ht2, map_one]
    have hts : t = s * z := by rw [hz, mul_inv_cancel_left]
    have hzs : z * s = s * z := (Subgroup.mem_center_iff.mp hzc s).symm
    have hz2 : z ^ 2 = 1 := by
      calc z ^ 2 = (s * s) * (z * z) := by rw [hs2, one_mul, pow_two]
        _ = s * (z * s) * z := by rw [hzs]; group
        _ = t * t := by rw [hts]; group
        _ = 1 := ht2
    have hst : s = t := by rw [hts, eq_one_of_mem_center_of_sq_eq_one hzc hz2, mul_one]
    have hmat := congrArg (fun X : Matrix.SpecialLinearGroup (Fin (m + 1)) F =>
      (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) hst
    simp only [hs, InnerDiagA.coe_conjSL, ht, Matrix.SpecialLinearGroup.transvection_coe] at hmat
    have hB1 : ((B⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h4 : (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (1 + single i j 1) =
        (1 + single i j 1) * (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
      calc (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (1 + single i j 1)
          = (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (1 + single i j 1) *
              (((B⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
                (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) := by rw [hB1, Matrix.mul_one]
        _ = (1 + single i j 1) * (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
          rw [← Matrix.mul_assoc, hmat]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h4
    exact (add_left_cancel h4).symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single
    (M := (B : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) fun i j hij => hcomm i j hij
  exact exists_unit_of_coe_eq_scalar hc.symm

theorem exists_scalar_mul_of_mem_ggInducedPairs [CharP F 2]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) {e : G}
    {A A' : GL (Fin (m + 1)) F} (hA : (e, A) ∈ LinFusion.ggInducedPairs ψ)
    (hA' : (e, A') ∈ LinFusion.ggInducedPairs ψ) :
    ∃ c : Fˣ, A' = GeneralLinearGroup.scalar (Fin (m + 1)) c * A := by
  have h := (LinFusion.ggInducedPairs ψ).mul_mem ((LinFusion.ggInducedPairs ψ).inv_mem hA) hA'
  rw [Prod.inv_mk, Prod.mk_mul_mk, inv_mul_cancel] at h
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_ggInducedPairs_one hker h
  refine ⟨c, ?_⟩
  rw [TypeA.PGLTor.scalar_mul_comm, ← hc, mul_inv_cancel_left]


theorem conjSL_injective (P : GL (Fin (m + 1)) F) : Function.Injective (InnerDiagA.conjSL P) := by
  intro u v h
  have h1 := congrArg (InnerDiagA.conjSL P⁻¹) h
  rwa [← LinFusion.conjSL_mul, ← LinFusion.conjSL_mul, inv_mul_cancel, LinFusion.conjSL_one,
    LinFusion.conjSL_one] at h1

theorem conjSL_surjective (P : GL (Fin (m + 1)) F) : Function.Surjective (InnerDiagA.conjSL P) :=
  fun v => ⟨InnerDiagA.conjSL P⁻¹ v, by
    rw [← LinFusion.conjSL_mul, mul_inv_cancel, LinFusion.conjSL_one]⟩

theorem range_comp_conjSL (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (P : GL (Fin (m + 1)) F) : (ψ.comp (InnerDiagA.conjSL P)).range = ψ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (conjSL_surjective P),
    ← MonoidHom.range_eq_map]

theorem ker_comp_conjSL_le {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (P : GL (Fin (m + 1)) F) :
    (ψ.comp (InnerDiagA.conjSL P)).ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) := by
  intro u hu
  have hz : InnerDiagA.conjSL P u ∈ Subgroup.center _ := hker hu
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro v
  have h := hz (InnerDiagA.conjSL P v)
  rw [← map_mul, ← map_mul] at h
  exact conjSL_injective P h

theorem mem_ggInducedPairs_frame {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    {P : GL (Fin (m + 1)) F} {e : G} {d : Fin (m + 1) → Fˣ}
    (h : (e, LinFusion.ggFrameDiag P d) ∈ LinFusion.ggInducedPairs ψ) :
    (e, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs (ψ.comp (InnerDiagA.conjSL P⁻¹)) := by
  refine LinFusion.mem_ggInducedPairs.mpr fun u => ?_
  have h1 := LinFusion.mem_ggInducedPairs.mp h (InnerDiagA.conjSL P⁻¹ u)
  simp only [MonoidHom.comp_apply]
  rw [h1, LinFusion.ggFrameDiag, ← LinFusion.conjSL_mul, ← LinFusion.conjSL_mul]
  congr 2
  group

variable (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G) in
@[expose] def inducedMatrices (E : Subgroup G) : Subgroup (GL (Fin (m + 1)) F) :=
  ((E.prod ⊤) ⊓ LinFusion.ggInducedPairs ψ).map (MonoidHom.snd G (GL (Fin (m + 1)) F))

theorem mem_inducedMatrices {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    {E : Subgroup G} {A : GL (Fin (m + 1)) F} :
    A ∈ inducedMatrices ψ E ↔ ∃ e ∈ E, (e, A) ∈ LinFusion.ggInducedPairs ψ := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, (Subgroup.mem_prod.mp (Subgroup.mem_inf.mp hx).1).1, (Subgroup.mem_inf.mp hx).2⟩
  · rintro ⟨e, he, h⟩
    exact ⟨(e, A), Subgroup.mem_inf.mpr ⟨Subgroup.mem_prod.mpr ⟨he, Subgroup.mem_top A⟩, h⟩, rfl⟩

theorem isProjElem_inducedMatrices [CharP F 2] {p : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {E : Subgroup G} (hE : IsElemAbelian p E) :
    TypeA.PGLTor.IsProjElem p (inducedMatrices ψ E) where
  scalar_mem u := mem_inducedMatrices.mpr ⟨1, E.one_mem, one_scalar_mem_ggInducedPairs ψ u⟩
  pow_scalar g hg := by
    obtain ⟨e, he, h⟩ := mem_inducedMatrices.mp hg
    have h1 := (LinFusion.ggInducedPairs ψ).pow_mem h p
    rw [Prod.pow_mk, hE.2 e he] at h1
    exact exists_scalar_of_mem_ggInducedPairs_one hker h1
  comm_scalar g hg h hh := by
    obtain ⟨e, he, hge⟩ := mem_inducedMatrices.mp hg
    obtain ⟨e', he', hhe'⟩ := mem_inducedMatrices.mp hh
    have hc : e * e' = e' * e := congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨e', he'⟩)
    have h1 := (LinFusion.ggInducedPairs ψ).mul_mem
      ((LinFusion.ggInducedPairs ψ).mul_mem hge hhe')
      ((LinFusion.ggInducedPairs ψ).inv_mem ((LinFusion.ggInducedPairs ψ).mul_mem hhe' hge))
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk, hc, mul_inv_cancel] at h1
    obtain ⟨u, hu⟩ := exists_scalar_of_mem_ggInducedPairs_one hker h1
    exact ⟨u, by rw [← hu, inv_mul_cancel_right]⟩

theorem card_inducedMatrices [CharP F 2] [Finite F]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {E : Subgroup G} (hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ LinFusion.ggInducedPairs ψ)
    (hEC : E ⊓ Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    Nat.card (inducedMatrices ψ E) = Nat.card E * (Nat.card F - 1) := by
  set P := (E.prod ⊤) ⊓ LinFusion.ggInducedPairs ψ with hP
  set g := (MonoidHom.snd G (GL (Fin (m + 1)) F)).comp P.subtype with hg
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ hx1
    have hx2 : x.2 = 1 := hx1
    have hxP := Subgroup.mem_inf.mp hx
    have h1 : (x.1, (1 : GL (Fin (m + 1)) F)) ∈ LinFusion.ggInducedPairs ψ := by
      rw [← hx2]
      exact hxP.2
    have h3 : x.1 ∈ E ⊓ Subgroup.centralizer (ψ.range : Set G) :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_prod.mp hxP.1).1,
        LinFusion.mem_centralizer_of_mem_ggInducedPairs_one h1⟩
    rw [hEC, Subgroup.mem_bot] at h3
    exact Subtype.ext (Prod.ext h3 hx2)
  have hgr : g.range = inducedMatrices ψ E := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have h1 : Nat.card P = Nat.card (inducedMatrices ψ E) := by
    rw [← hgr]
    exact Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv
  set f := (MonoidHom.fst G (GL (Fin (m + 1)) F)).comp P.subtype with hf
  have hfr : f.range = E := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (Subgroup.mem_prod.mp (Subgroup.mem_inf.mp x.2).1).1
    · intro e he
      obtain ⟨A, hA⟩ := hEA e he
      exact ⟨⟨(e, A), Subgroup.mem_inf.mpr ⟨Subgroup.mem_prod.mpr ⟨he, Subgroup.mem_top A⟩, hA⟩⟩,
        rfl⟩
  have hfk : Nat.card f.ker = Nat.card Fˣ := by
    symm
    refine Nat.card_eq_of_bijective (fun u => ⟨⟨(1, GeneralLinearGroup.scalar (Fin (m + 1)) u),
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_prod.mpr ⟨E.one_mem, Subgroup.mem_top _⟩,
        one_scalar_mem_ggInducedPairs ψ u⟩⟩, rfl⟩) ⟨fun u v huv => ?_, fun x => ?_⟩
    · have h := congrArg (fun y : f.ker => ((y : P) : G × GL (Fin (m + 1)) F).2) huv
      exact TypeA.PGLTor.scalar_injective h
    · obtain ⟨⟨⟨e, A⟩, hx⟩, hxk⟩ := x
      have he : e = 1 := hxk
      subst he
      obtain ⟨u, hu⟩ := exists_scalar_of_mem_ggInducedPairs_one hker (Subgroup.mem_inf.mp hx).2
      subst hu
      exact ⟨u, rfl⟩
  rw [← h1, ← Subgroup.card_ker_mul_card_range f, hfr, hfk, Nat.card_units, mul_comm]

theorem exists_eq_diagGL {M : GL (Fin (m + 1)) F}
    (hM : ∀ i j, i ≠ j → (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j = 0) :
    ∃ d : Fin (m + 1) → Fˣ, M = InnerDiagA.diagGL d := by
  have hne : ∀ i, (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i ≠ 0 := by
    intro i h0
    have h1 : ((M * M⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i = 1 := by
      rw [mul_inv_cancel, Units.val_one, one_apply_eq]
    rw [Units.val_mul, mul_apply, Finset.sum_eq_single i
      (fun k _ hki => by rw [hM i k (Ne.symm hki), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), h0, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨fun i => Units.mk0 _ (hne i), Units.ext ?_⟩
  rw [InnerDiagA.coe_diagGL]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [hM i j hij, diagonal_apply_ne _ hij]

theorem exists_le_ggFrameTorus [CharP F 2] [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : p ∣ Nat.card F - 1) {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {E : Subgroup G} (hE : IsElemAbelian p E) (hbig : p ^ ((m + 1) / p + 1) < Nat.card E)
    (hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ LinFusion.ggInducedPairs ψ)
    (hEC : E ⊓ Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    ∃ P : GL (Fin (m + 1)) F, E ≤ LinFusion.ggFrameTorus F ψ P := by
  rcases TypeA.PGLTor.toral_or_card_le hp hp2 hpF (isProjElem_inducedMatrices hker hE) with
    ⟨A₀, hA₀⟩ | hle
  · refine ⟨A₀, fun e he => ?_⟩
    obtain ⟨A, hA⟩ := hEA e he
    obtain ⟨d, hd⟩ := exists_eq_diagGL (M := A₀ * A * A₀⁻¹) fun i j hij => by
      rw [Units.val_mul, Units.val_mul]
      exact hA₀ A (mem_inducedMatrices.mpr ⟨e, he, hA⟩) i j hij
    have hAeq : A = LinFusion.ggFrameDiag A₀ d := by
      rw [LinFusion.ggFrameDiag, ← hd]
      group
    exact ⟨d, hAeq ▸ hA⟩
  · exfalso
    rw [card_inducedMatrices hker hEA hEC, Fintype.card_fin] at hle
    have hF1 : 0 < Nat.card F - 1 := by
      have := Finite.one_lt_card (α := F)
      omega
    have := Nat.le_of_mul_le_mul_right hle hF1
    omega

end LinTorus

end CFSG.StandardType

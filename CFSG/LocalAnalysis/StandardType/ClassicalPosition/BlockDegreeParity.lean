module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.ReducedAlgebra
public import TauCeti.RingTheory.PrimitiveIdempotent
public import TauCeti.FieldTheory.Galois.FixedField

public section

namespace CFSG.StandardType.ClassicalPosition

private lemma bdp_isReduced {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) :
    IsReduced (Algebra.adjoin F (Units.val '' S)) := by
  let E : Matrix ι ι F ≃ₐ[F] Module.End F (ι → F) := Matrix.toLinAlgEquiv'
  let T : Set (Module.End F (ι → F)) := E '' (Units.val '' S)
  have hcomm : ∀ t ∈ T, ∀ t' ∈ T, Commute t t' := by
    rintro t ⟨x, hx, rfl⟩ t' ⟨y, hy, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨s', hs', rfl⟩ := hy
    have hsval : (s : Matrix ι ι F) * (s' : Matrix ι ι F) =
        (s' : Matrix ι ι F) * (s : Matrix ι ι F) := by
      rw [← Units.val_mul, ← Units.val_mul, hS s hs s' hs']
    change E (s : Matrix ι ι F) * E (s' : Matrix ι ι F) =
      E (s' : Matrix ι ι F) * E (s : Matrix ι ι F)
    rw [← map_mul, ← map_mul, hsval]
  have hoddT : ∀ t ∈ T, ∃ o : ℕ, Odd o ∧ t ^ o = 1 := by
    rintro t ⟨x, hx, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hx
    refine ⟨orderOf s, hodd s hs, ?_⟩
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
  have hred : IsReduced (Algebra.adjoin F T) :=
    isReduced_adjoin_of_commute_of_odd T hcomm hoddT
  have hmap : Algebra.adjoin F T = (Algebra.adjoin F (Units.val '' S)).map E := by
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      rintro y ⟨x, hx, rfl⟩
      exact Subalgebra.mem_map.mpr ⟨x, Algebra.subset_adjoin hx, rfl⟩
    · rw [Subalgebra.map_le, Algebra.adjoin_le_iff]
      rintro x hx
      exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
  rw [isReduced_iff] at hred ⊢
  intro x hx
  have hmem : E (x : Matrix ι ι F) ∈ Algebra.adjoin F T := by
    rw [hmap]
    exact Subalgebra.mem_map.mpr ⟨(x : Matrix ι ι F), x.2, rfl⟩
  have hnil : IsNilpotent (⟨E (x : Matrix ι ι F), hmem⟩ : Algebra.adjoin F T) := by
    obtain ⟨n, hn⟩ := (hx.map (Algebra.adjoin F (Units.val '' S)).val).map E.toRingHom
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hzero : E (x : Matrix ι ι F) = 0 := by
    have hsub := hred ⟨E (x : Matrix ι ι F), hmem⟩ hnil
    simpa using congrArg Subtype.val hsub
  exact Subtype.ext (E.injective (hzero.trans (map_zero E).symm))

private lemma bdp_isPrime_span_one_sub {A : Type} [CommRing A] [IsSemisimpleRing A]
    {e : A} (hidem : IsIdempotentElem e) (hne : e ≠ 0)
    (hprim : ∀ f : A, IsIdempotentElem f → f * e = f → f = 0 ∨ f = e) :
    (Ideal.span {1 - e}).IsPrime := by
  have hidem' : IsIdempotentElem (1 - e) := IsIdempotentElem.one_sub_iff.mpr hidem
  have hmem : ∀ x : A, x ∈ Ideal.span ({1 - e} : Set A) ↔ x * e = 0 := by
    intro x
    rw [TauCeti.mem_span_singleton_iff_mul_eq_self hidem', mul_sub, mul_one, sub_eq_self]
  refine Ideal.IsPrime.mk ?_ ?_
  · intro htop
    have h1 : (1 : A) ∈ Ideal.span ({1 - e} : Set A) := htop ▸ Submodule.mem_top
    rw [hmem 1] at h1
    exact hne (by simpa using h1)
  · intro x y hxy
    have hxy' : (x * y) * e = 0 := (hmem (x * y)).mp hxy
    rw [hmem x, hmem y]
    by_contra h
    push_neg at h
    obtain ⟨hx, hy⟩ := h
    obtain ⟨f, hfidem, hspan⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {x * e})
    have hfmem : f ∈ Ideal.span ({x * e} : Set A) := by
      rw [hspan]; exact Ideal.mem_span_singleton_self f
    have humem : x * e ∈ Ideal.span ({f} : Set A) := by
      rw [← hspan]; exact Ideal.mem_span_singleton_self (x * e)
    rw [TauCeti.mem_span_singleton_iff_mul_eq_self hfidem] at humem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hfmem
    have hc' : f = c * (x * e) := by rw [← hc, smul_eq_mul]
    have hfe : f * e = f := by
      rw [hc']
      ring_nf
      rw [pow_two, hidem.eq]
    have hfne : f ≠ 0 := by
      intro hf0
      exact hx (by rw [← humem, hf0, mul_zero])
    have hfnee : f ≠ e := by
      intro hfeq
      have hye : y * e = e * (y * e) := by
        rw [← mul_assoc, mul_comm e y, mul_assoc, hidem.eq]
      have hy0 : y * e = 0 := by
        calc y * e = e * (y * e) := hye
          _ = f * (y * e) := by rw [← hfeq]
          _ = (c * (x * e)) * (y * e) := by rw [hc']
          _ = c * ((x * y) * e) := by
                ring_nf
                rw [pow_two, hidem.eq]
          _ = 0 := by rw [hxy', mul_zero]
      exact hy hy0
    exact hfnee ((hprim f hfidem hfe).resolve_left hfne)

private lemma bdp_formAdj_inv_mem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    {G : Matrix ι ι F} (hG : IsUnit G.det) {S : Set (GL ι F)}
    (hSG : ∀ s ∈ S, Matrix.transpose (s : Matrix ι ι F) * G * (s : Matrix ι ι F) = G)
    {a : Matrix ι ι F} (ha : a ∈ Algebra.adjoin F (Units.val '' S)) :
    formAdj (RingHom.id F) G a ∈ Algebra.adjoin F (Units.val '' S) :=
  Geo.formAdj_mem_adjoin (RingHom.id F) hG (by intro s hs; simpa using hSG s hs) ha

private lemma bdp_formAdj_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G : Matrix ι ι F} (hG : IsUnit G.det) {S : Set (GL ι F)}
    (hSG : ∀ s ∈ S, Matrix.transpose (s : Matrix ι ι F) * G * (s : Matrix ι ι F) = G)
    {a : Matrix ι ι F} (ha : a ∈ Algebra.adjoin F (Units.val '' S)) :
    formAdj (RingHom.id F) G (formAdj (RingHom.id F) G a) = a := by
  have hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map (RingHom.id F)) * G *
      (s : Matrix ι ι F) = G := by intro s hs; simpa using hSG s hs
  refine Algebra.adjoin_induction
    (p := fun x _ => formAdj (RingHom.id F) G (formAdj (RingHom.id F) G x) = x)
    ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    have hfs : formAdj (RingHom.id F) G (s : Matrix ι ι F) =
        ((s⁻¹ : GL ι F) : Matrix ι ι F) :=
      Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hG s (hSU s hs)
    have hprod : formAdj (RingHom.id F) G ((s⁻¹ : GL ι F) : Matrix ι ι F) *
        formAdj (RingHom.id F) G (s : Matrix ι ι F) = 1 := by
      rw [← Geo.formAdj_mul (RingHom.id F) hG (s : Matrix ι ι F)
        ((s⁻¹ : GL ι F) : Matrix ι ι F)]
      rw [show (s : Matrix ι ι F) * ((s⁻¹ : GL ι F) : Matrix ι ι F) = 1 from by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]]
      exact Geo.formAdj_one (RingHom.id F) hG
    rw [hfs] at hprod
    rw [hfs]
    calc formAdj (RingHom.id F) G ((s⁻¹ : GL ι F) : Matrix ι ι F)
        = formAdj (RingHom.id F) G ((s⁻¹ : GL ι F) : Matrix ι ι F) * 1 := (mul_one _).symm
      _ = formAdj (RingHom.id F) G ((s⁻¹ : GL ι F) : Matrix ι ι F) *
            (((s⁻¹ : GL ι F) : Matrix ι ι F) * (s : Matrix ι ι F)) := by
            rw [show ((s⁻¹ : GL ι F) : Matrix ι ι F) * (s : Matrix ι ι F) = 1 from by
              rw [← Units.val_mul, inv_mul_cancel, Units.val_one]]
      _ = (formAdj (RingHom.id F) G ((s⁻¹ : GL ι F) : Matrix ι ι F) *
            ((s⁻¹ : GL ι F) : Matrix ι ι F)) * (s : Matrix ι ι F) := by rw [mul_assoc]
      _ = 1 * (s : Matrix ι ι F) := by rw [hprod]
      _ = (s : Matrix ι ι F) := one_mul _
  · intro r
    rw [Algebra.algebraMap_eq_smul_one]
    rw [Geo.formAdj_smul, Geo.formAdj_one (RingHom.id F) hG]
    rw [Geo.formAdj_smul, Geo.formAdj_one (RingHom.id F) hG]
    rfl
  · intro x y _ _ hx hy
    rw [Geo.formAdj_add, Geo.formAdj_add, hx, hy]
  · intro x y _ _ hx hy
    rw [Geo.formAdj_mul (RingHom.id F) hG, Geo.formAdj_mul (RingHom.id F) hG, hx, hy]

theorem exists_blockField {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : Finite K)
      (π : Algebra.adjoin F (Units.val '' S) →ₐ[F] K),
      Function.Surjective π ∧ (∀ a, π a = 0 ↔ (a : Matrix ι ι F) * e = 0) ∧
        Module.finrank F K = blockDegree (Algebra.adjoin F (Units.val '' S)) e := by
  classical
  have hcommP : (Units.val '' S : Set (Matrix ι ι F)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    have h := hS s hs s' hs'
    show (s : Matrix ι ι F) * (s' : Matrix ι ι F) = (s' : Matrix ι ι F) * (s : Matrix ι ι F)
    rw [← Units.val_mul, ← Units.val_mul, h]
  let A : Subalgebra F (Matrix ι ι F) := Algebra.adjoin F (Units.val '' S)
  letI : CommRing A := by
    change CommRing (Algebra.adjoin F (Units.val '' S))
    exact Algebra.adjoinCommRingOfComm F hcommP
  have hredA : IsReduced A := bdp_isReduced hS hodd
  haveI : IsReduced A := by
    rw [isReduced_iff] at hredA ⊢
    exact hredA
  haveI : IsArtinianRing A := IsArtinianRing.of_finite F A
  haveI : IsSemisimpleRing A :=
    @IsArtinianRing.isSemisimpleRing_of_isReduced A ‹CommRing A› ‹IsArtinianRing A› ‹IsReduced A›
  let eA : A := ⟨e, he.1⟩
  have heA : IsIdempotentElem eA := Subtype.ext he.2.1
  have hneA : eA ≠ 0 := by
    intro h0
    exact he.2.2.1 (by simpa [eA] using congrArg Subtype.val h0)
  have hprimA : ∀ f : A, IsIdempotentElem f → f * eA = f → f = 0 ∨ f = eA := by
    intro f hf hfe
    have hfval : IsIdempotentElem (f : Matrix ι ι F) := by
      rw [isIdempotentElem_iff] at hf ⊢
      simpa using congrArg Subtype.val hf
    have hfmem : (f : Matrix ι ι F) ∈ Algebra.adjoin F (Units.val '' S) := by
      simpa [A] using f.2
    have hfeval : (f : Matrix ι ι F) * e = (f : Matrix ι ι F) := by
      simpa [eA] using congrArg Subtype.val hfe
    rcases he.2.2.2 (f : Matrix ι ι F) hfmem hfval hfeval with h0 | hee
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr (Subtype.ext hee)
  let I : Ideal A := Ideal.span {1 - eA}
  haveI hIprime : I.IsPrime := bdp_isPrime_span_one_sub heA hneA hprimA
  haveI hImax : I.IsMaximal := (IsArtinianRing.isPrime_iff_isMaximal I).mp hIprime
  let K := A ⧸ I
  letI : Field K := Ideal.Quotient.field I
  have hmem : ∀ x : A, x ∈ I ↔ x * eA = 0 := by
    intro x
    unfold I
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hx
      rw [hc, mul_assoc, mul_comm c eA, ← mul_assoc, IsIdempotentElem.one_sub_mul_self heA,
        zero_mul]
    · intro hx
      refine Ideal.mem_span_singleton.mpr ⟨x, ?_⟩
      rw [sub_mul, one_mul, mul_comm eA x, hx, sub_zero]
  let g : A →ₗ[F] Matrix ι ι F :=
    (LinearMap.mulRight F e).comp (Subalgebra.val A).toLinearMap
  have hker : LinearMap.ker g = I.restrictScalars F := by
    ext x
    change (x : Matrix ι ι F) * e = 0 ↔ x ∈ I
    rw [hmem x, ← Subtype.coe_inj]
    rfl
  have hrange : LinearMap.range g = (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : Matrix ι ι F), x.2, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      exact ⟨⟨z, hz⟩, hzy⟩
  have h1 : Module.finrank F (A ⧸ I) = Module.finrank F (A ⧸ I.restrictScalars F) := rfl
  have h3 : Module.finrank F (A ⧸ I.restrictScalars F) = Module.finrank F (LinearMap.range g) := by
    rw [← hker]
    exact (LinearMap.quotKerEquivRange g).finrank_eq
  have hdeg : Module.finrank F K = blockDegree (Algebra.adjoin F (Units.val '' S)) e := by
    rw [h1, h3, hrange]
    rfl
  haveI : Finite K := Finite.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let π : A →ₐ[F] K := Ideal.Quotient.mkₐ F I
  refine ⟨K, inferInstance, inferInstance, inferInstance, π, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, ha⟩
  · intro a
    change Ideal.Quotient.mk I a = 0 ↔ (a : Matrix ι ι F) * e = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hmem a, ← Subtype.coe_inj]
    rfl
  · exact hdeg

theorem blockDegree_eq_one_or_even_of_formAdj_eq {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Finite F] [CharP F 2] {G : Matrix ι ι F} (hG : IsUnit G.det)
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hSG : ∀ s ∈ S, Matrix.transpose (s : Matrix ι ι F) * G * (s : Matrix ι ι F) = G)
    {e : Matrix ι ι F} (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id F) G e = e) :
    blockDegree (Algebra.adjoin F (Units.val '' S)) e = 1 ∨
      Even (blockDegree (Algebra.adjoin F (Units.val '' S)) e) := by
  classical
  have hcommP : (Units.val '' S : Set (Matrix ι ι F)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    have h := hS s hs s' hs'
    show (s : Matrix ι ι F) * (s' : Matrix ι ι F) = (s' : Matrix ι ι F) * (s : Matrix ι ι F)
    rw [← Units.val_mul, ← Units.val_mul, h]
  let A : Subalgebra F (Matrix ι ι F) := Algebra.adjoin F (Units.val '' S)
  letI : CommRing A := by
    change CommRing (Algebra.adjoin F (Units.val '' S))
    exact Algebra.adjoinCommRingOfComm F hcommP
  let eA : A := ⟨e, he.1⟩
  have heA : IsIdempotentElem eA := Subtype.ext he.2.1
  letI : IsMulCommutative A := Algebra.isMulCommutative_adjoin F hcommP
  let gfun : A → A := fun a =>
    ⟨formAdj (RingHom.id F) G (a : Matrix ι ι F), bdp_formAdj_inv_mem hG hSG a.2⟩
  let f : A →ₐ[F] A :=
    { toFun := gfun
      map_one' := Subtype.ext (Geo.formAdj_one (RingHom.id F) hG)
      map_mul' := by
        intro a b
        apply Subtype.ext
        change formAdj (RingHom.id F) G ((a : Matrix ι ι F) * (b : Matrix ι ι F)) =
          formAdj (RingHom.id F) G (a : Matrix ι ι F) *
            formAdj (RingHom.id F) G (b : Matrix ι ι F)
        rw [Geo.formAdj_mul (RingHom.id F) hG]
        exact (congrArg Subtype.val (mul_comm' (gfun a) (gfun b))).symm
      map_zero' := Subtype.ext (by
        change formAdj (RingHom.id F) G (0 : Matrix ι ι F) = 0
        unfold formAdj
        rw [Matrix.map_zero, Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul]
        rfl)
      map_add' := by
        intro a b
        apply Subtype.ext
        change formAdj (RingHom.id F) G ((a : Matrix ι ι F) + (b : Matrix ι ι F)) =
          formAdj (RingHom.id F) G (a : Matrix ι ι F) +
            formAdj (RingHom.id F) G (b : Matrix ι ι F)
        rw [Geo.formAdj_add]
      commutes' := by
        intro r
        apply Subtype.ext
        have h1 : ((algebraMap F A) r : Matrix ι ι F) = r • (1 : Matrix ι ι F) := by
          change (algebraMap F (Matrix ι ι F)) r = r • (1 : Matrix ι ι F)
          rw [Algebra.algebraMap_eq_smul_one]
        show formAdj (RingHom.id F) G (((algebraMap F A) r) : Matrix ι ι F) =
          ((algebraMap F A) r : Matrix ι ι F)
        rw [h1, Geo.formAdj_smul, Geo.formAdj_one (RingHom.id F) hG]
        rfl }
  have hff : f.comp f = AlgHom.id F A :=
    AlgHom.ext fun a => by
      apply Subtype.ext
      show formAdj (RingHom.id F) G (formAdj (RingHom.id F) G (a : Matrix ι ι F)) =
        (a : Matrix ι ι F)
      exact bdp_formAdj_formAdj hG hSG a.2
  have htau_e : f eA = eA := by
    apply Subtype.ext
    change formAdj (RingHom.id F) G e = e
    exact hadj
  obtain ⟨K, fieldK, algK, finiteK, π, hπsurj, hπker, hπdeg⟩ :=
    exists_blockField hS hodd he
  letI : Field K := fieldK
  letI : Algebra F K := algK
  letI : Finite K := finiteK
  have hH : RingHom.ker π ≤ RingHom.ker (π.comp f) := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [AlgHom.comp_apply]
    rw [hπker (f a), hπker a] at *
    have hxe : (f a) * eA = f (a * eA) := by rw [map_mul, htau_e]
    have h2 : ((f a : A) : Matrix ι ι F) * e = ((f (a * eA) : A) : Matrix ι ι F) := by
      simpa using congrArg Subtype.val hxe
    rw [h2]
    have hae : a * eA = 0 := by
      rw [← Subtype.coe_inj]
      simpa using ha
    rw [hae, map_zero]
    rfl
  let fK : K →ₐ[F] K := AlgHom.liftOfSurjective π hπsurj (π.comp f) hH
  have hfK2 : fK.comp fK = AlgHom.id F K := by
    apply AlgHom.ext
    intro x
    obtain ⟨a, rfl⟩ := hπsurj x
    have h1 : fK (π a) = (π.comp f) a :=
      AlgHom.liftOfSurjective_apply π hπsurj (π.comp f) hH a
    have h2 : fK (π (f a)) = (π.comp f) (f a) :=
      AlgHom.liftOfSurjective_apply π hπsurj (π.comp f) hH (f a)
    change fK (fK (π a)) = π a
    rw [h1]
    change fK (π (f a)) = π a
    rw [h2]
    exact congrArg π (AlgHom.congr_fun hff a)
  let tauK : K ≃ₐ[F] K := AlgEquiv.ofAlgHom fK fK hfK2 hfK2
  haveI : FiniteDimensional F K := Module.Finite.of_finite
  by_cases htau : tauK = 1
  · left
    have hfK_id : fK = AlgHom.id F K := by
      have h := congrArg AlgEquiv.toAlgHom htau
      rw [show tauK.toAlgHom = fK from AlgEquiv.toAlgHom_ofAlgHom fK fK hfK2 hfK2] at h
      rw [h]
      rfl
    have hgen : ∀ (s : GL ι F) (hs : s ∈ S), π (⟨(s : Matrix ι ι F),
        Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ : A) = 1 := by
      intro s hs
      let sA : A := ⟨(s : Matrix ι ι F), Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩
      have hmem_inv : ((s⁻¹ : GL ι F) : Matrix ι ι F) ∈ Algebra.adjoin F (Units.val '' S) := by
        rw [← Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hG s (by simpa using hSG s hs)]
        exact bdp_formAdj_inv_mem hG hSG (Algebra.subset_adjoin ⟨s, hs, rfl⟩)
      let sAinv : A := ⟨((s⁻¹ : GL ι F) : Matrix ι ι F), hmem_inv⟩
      have hsA_mul : sA * sAinv = 1 := by
        apply Subtype.ext
        change (s : Matrix ι ι F) * ((s⁻¹ : GL ι F) : Matrix ι ι F) = 1
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hfsA : f sA = sAinv := by
        apply Subtype.ext
        change formAdj (RingHom.id F) G (s : Matrix ι ι F) = ((s⁻¹ : GL ι F) : Matrix ι ι F)
        exact Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hG s (by simpa using hSG s hs)
      have hπeq : π sAinv = π sA := by
        have h1 : fK (π sA) = π (f sA) := by
          simpa using AlgHom.liftOfSurjective_apply π hπsurj (π.comp f) hH sA
        rw [hfsA] at h1
        have h2 := AlgHom.congr_fun hfK_id (π sA)
        rw [h1] at h2
        exact h2
      have hx2 : (π sA) ^ 2 = 1 := by
        rw [pow_two]
        calc π sA * π sA = π sA * π sAinv := by rw [← hπeq]
          _ = π (sA * sAinv) := (map_mul _ _ _).symm
          _ = 1 := by rw [hsA_mul, map_one]
      have hsA_pow : sA ^ orderOf s = 1 := by
        apply Subtype.ext
        change (s : Matrix ι ι F) ^ orderOf s = 1
        rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
      have hxo : (π sA) ^ orderOf s = 1 := by
        rw [← map_pow, hsA_pow, map_one]
      obtain ⟨k, hk⟩ := hodd s hs
      have hxodd : (π sA) ^ (2 * k + 1) = 1 := by
        rw [← hk]; exact hxo
      rw [pow_succ, pow_mul, hx2, one_pow, one_mul] at hxodd
      exact hxodd
    have hspan : Submodule.span F ({1} : Set K) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨a, rfl⟩ := hπsurj x
      have hmem : ∀ b : A, π b ∈ (⊥ : Subalgebra F K) := by
        intro b
        refine Algebra.adjoin_induction
          (p := fun z hz => π (⟨z, hz⟩ : A) ∈ (⊥ : Subalgebra F K))
          ?_ ?_ ?_ ?_ b.2
        · rintro z ⟨s, hs, rfl⟩
          simpa only using (show π (⟨(s : Matrix ι ι F),
              Algebra.subset_adjoin ⟨s, hs, rfl⟩⟩ : A) ∈ (⊥ : Subalgebra F K) from by
                rw [hgen s hs]
                exact Subalgebra.one_mem (⊥ : Subalgebra F K))
        · intro r
          have hz : (algebraMap F (Matrix ι ι F)) r ∈ Algebra.adjoin F (Units.val '' S) :=
            Subalgebra.algebraMap_mem _ r
          have heq : (⟨(algebraMap F (Matrix ι ι F)) r, hz⟩ : A) = algebraMap F A r :=
            Subtype.ext rfl
          rw [heq, AlgHom.commutes]
          exact Subalgebra.algebraMap_mem (⊥ : Subalgebra F K) r
        · intro y z hy hz ihy ihz
          have hyz : y + z ∈ Algebra.adjoin F (Units.val '' S) := Subalgebra.add_mem _ hy hz
          have heq : (⟨y + z, hyz⟩ : A) = ⟨y, hy⟩ + ⟨z, hz⟩ := Subtype.ext rfl
          rw [heq, map_add]
          exact Subalgebra.add_mem _ ihy ihz
        · intro y z hy hz ihy ihz
          have hyz : y * z ∈ Algebra.adjoin F (Units.val '' S) := Subalgebra.mul_mem _ hy hz
          have heq : (⟨y * z, hyz⟩ : A) = ⟨y, hy⟩ * ⟨z, hz⟩ := Subtype.ext rfl
          rw [heq, map_mul]
          exact Subalgebra.mul_mem _ ihy ihz
      have hxbot : π a ∈ (⊥ : Subalgebra F K) := hmem a
      rw [Algebra.mem_bot] at hxbot
      obtain ⟨c, hc⟩ := hxbot
      rw [← hc, Algebra.algebraMap_eq_smul_one]
      exact (Submodule.mem_span_singleton).mpr ⟨c, rfl⟩
    have hfin : Module.finrank F K = 1 :=
      (finrank_eq_one_iff_of_nonzero (1 : K) one_ne_zero).mpr hspan
    rw [← hπdeg, hfin]
  · right
    have h2 : tauK ^ 2 = 1 := by
      rw [sq]
      ext x
      change tauK (tauK x) = x
      exact AlgHom.congr_fun hfK2 x
    have hdvd : orderOf tauK ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    have hne1 : orderOf tauK ≠ 1 := by
      intro h
      exact htau (orderOf_eq_one_iff.mp h)
    have horder : orderOf tauK = 2 := by
      have hle : orderOf tauK ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < orderOf tauK := orderOf_pos tauK
      interval_cases orderOf tauK
      · exact absurd rfl hne1
      · rfl
    have hdvd1 : orderOf tauK ∣ Nat.card (K ≃ₐ[F] K) := orderOf_dvd_natCard tauK
    have hdvd2 : Nat.card (K ≃ₐ[F] K) ∣ Module.finrank F K :=
      TauCeti.natCard_algEquiv_dvd_finrank F K
    have h2dvd : 2 ∣ Module.finrank F K := by
      rw [← horder]
      exact dvd_trans hdvd1 hdvd2
    rw [← hπdeg, even_iff_two_dvd]
    exact h2dvd

end CFSG.StandardType.ClassicalPosition

module

public import CFSG.Milestones.ASVolI.I1
public import CFSG.Quasithin.SteinbergCBI16
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

theorem burnsideI16h_h1Dim_eq {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [Finite G] [Finite V] (ρ : Representation (ZMod 2) G V) :
    h1Dim ρ = Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 ρ) := by
  have h := CFSG.Open.ASVolIRegistered.card_groupCohomology_one ρ
  have hpos : Nat.card (groupCohomology (Rep.of ρ) 1) ≠ 0 := by
    rw [h]
    positivity
  haveI : Finite (groupCohomology (Rep.of ρ) 1) := Nat.finite_of_card_ne_zero hpos
  haveI : Module.Finite (ZMod 2) (groupCohomology (Rep.of ρ) 1) := Module.Finite.of_finite
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := groupCohomology (Rep.of ρ) 1)
  rw [Nat.card_zmod] at h2
  unfold h1Dim
  exact Nat.pow_right_injective (le_refl 2) (h2.symm.trans h)

section JPHelpers

theorem burnsideI16h_p2 :
    ∀ n : ℕ, 2 ≤ n → h1Dim (slNaturalRep 2 (GaloisField 2 n)) = n := by
  intro n hn
  obtain ⟨j2, -⟩ := CFSG.Quasithin.JonesParshall.natural_binary_first_cohomology_sector.{0, 0}
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 n (by omega)
  rw [burnsideI16h_h1Dim_eq]
  exact j2 (a := n) hcard (by omega)
    (CFSG.Open.ASVolIRegistered.binaryNaturalSL_matrixRep 2 _)

theorem burnsideI16h_p4 :
    (∀ n : ℕ, 2 ≤ n → h1Dim (slNaturalRep 3 (GaloisField 2 n)) = 0) ∧
      h1Dim (slNaturalRep 3 (ZMod 2)) = 1 := by
  obtain ⟨-, -, j3, -⟩ := CFSG.Quasithin.JonesParshall.natural_binary_first_cohomology_sector.{0, 0}
  refine ⟨fun n hn => ?_, ?_⟩
  · let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card 2 n (by omega)
    rw [burnsideI16h_h1Dim_eq]
    have := j3 (a := n) hcard (by omega)
      (CFSG.Open.ASVolIRegistered.binaryNaturalSL_matrixRep 3 _)
    exact this.trans (if_neg (by omega))
  · rw [burnsideI16h_h1Dim_eq]
    have := j3 (F := ZMod 2) (a := 1) (by rw [ZMod.card, pow_one]) (by norm_num)
      (CFSG.Open.ASVolIRegistered.binaryNaturalSL_matrixRep 3 (ZMod 2))
    exact this.trans (if_pos rfl)

theorem burnsideI16h_p6 :
    h1Dim (slNaturalRep 4 (ZMod 2)) = 0 ∧ h1Dim (slNaturalRep 5 (ZMod 2)) = 0 := by
  obtain ⟨-, -, -, -, -, j6, -⟩ :=
    CFSG.Quasithin.JonesParshall.natural_binary_first_cohomology_sector.{0, 0}
  refine ⟨?_, ?_⟩
  · rw [burnsideI16h_h1Dim_eq]
    exact j6 (d := 4) (Or.inl rfl) (ZMod.card 2)
      (CFSG.Open.ASVolIRegistered.binaryNaturalSL_matrixRep 4 (ZMod 2))
  · rw [burnsideI16h_h1Dim_eq]
    exact j6 (d := 5) (Or.inr rfl) (ZMod.card 2)
      (CFSG.Open.ASVolIRegistered.binaryNaturalSL_matrixRep 5 (ZMod 2))

theorem burnsideI16h_p7 :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
      (ρ : Representation (ZMod 2) SL(5, ZMod 2) V),
      ρ.IsIrreducible → Module.finrank (ZMod 2) V = 10 → h1Dim ρ = 0 := by
  intro V _ _ ρ hρ hdim
  obtain ⟨-, -, -, -, -, -, j7⟩ :=
    CFSG.Quasithin.JonesParshall.natural_binary_first_cohomology_sector.{0, 0}
  haveI : Module.Finite (ZMod 2) V :=
    Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  rw [burnsideI16h_h1Dim_eq]
  exact j7 (MulEquiv.refl _) hρ hdim

end JPHelpers

open CFSG.Quasithin.SteinbergCB.I16 in
noncomputable def burnsideI16h_altE {n k : ℕ} (C : DnCoords n k) :
    (evenWeight n ⧸ constInEven n) ≃+ (Fin k → ZMod 2) := by
  let f : evenWeight n →ₗ[ZMod 2] (Fin k → ZMod 2) :=
    (C.proj.toZModLinearMap 2).comp (evenWeight n).subtype
  have hker : constInEven n ≤ LinearMap.ker f := by
    intro v hv
    have hv' : (v : Fin n → ZMod 2) ∈
        Submodule.span (ZMod 2) {fun _ : Fin n => (1 : ZMod 2)} := hv
    rw [Submodule.mem_span_singleton] at hv'
    obtain ⟨c, hc⟩ := hv'
    rw [LinearMap.mem_ker]
    show C.proj (v : Fin n → ZMod 2) = 0
    have hs : ∑ i, (v : Fin n → ZMod 2) i = 0 := v.2
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with h0 | h1
    · rw [← hc, h0, zero_smul, map_zero]
    · rw [← hc, h1, one_smul]
      rw [← hc, h1, one_smul] at hs
      exact C.proj_one hs
  have hinj : Function.Injective ((constInEven n).liftQ f hker) := by
    intro a b hab
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.liftQ_apply, Submodule.liftQ_apply] at hab
    rw [Submodule.Quotient.eq]
    have hsum : ∑ i, ((x - y : evenWeight n) : Fin n → ZMod 2) i = 0 := (x - y).2
    have hp : C.proj ((x - y : evenWeight n) : Fin n → ZMod 2) = 0 := by
      have : C.proj (x : Fin n → ZMod 2) = C.proj (y : Fin n → ZMod 2) := hab
      show C.proj ((x : Fin n → ZMod 2) - y) = 0
      rw [map_sub, this, sub_self]
    rcases C.ker_proj _ hsum hp with h | h
    · have : x - y = 0 := Subtype.ext h
      rw [this]
      exact Submodule.zero_mem _
    · show ((x - y : evenWeight n) : Fin n → ZMod 2) ∈
        Submodule.span (ZMod 2) {fun _ : Fin n => (1 : ZMod 2)}
      rw [h]
      exact Submodule.mem_span_singleton_self _
  have hsurj : Function.Surjective ((constInEven n).liftQ f hker) := by
    intro y
    refine ⟨Submodule.Quotient.mk ⟨C.incl y, C.sum_incl y⟩, ?_⟩
    rw [Submodule.liftQ_apply]
    exact C.proj_incl y
  exact (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).toAddEquiv

open CFSG.Quasithin.SteinbergCB.I16 in
theorem burnsideI16h_altE_intertwine {n k : ℕ} (C : DnCoords n k)
    (σ : alternatingGroup (Fin n)) (w : evenWeight n ⧸ constInEven n) :
    burnsideI16h_altE C (altNaturalRep n σ w) = C.actA σ (burnsideI16h_altE C w) := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hx' : ∑ i, x i = 0 := hx
  have e1 : burnsideI16h_altE C (Submodule.Quotient.mk ⟨x, hx⟩) = C.proj x := rfl
  rw [e1]
  have e2 : burnsideI16h_altE C (altNaturalRep n σ (Submodule.Quotient.mk ⟨x, hx⟩)) =
      C.proj (pv (σ : Equiv.Perm (Fin n)) x) := rfl
  rw [e2]
  exact (C.act_proj (σ : Equiv.Perm (Fin n)) hx').symm

open CFSG.Quasithin.SteinbergCB.I16 in
theorem burnsideI16h_altNatural {n k : ℕ} (C : DnCoords n k) :
    CFSG.Quasithin.Explicit.AlternatingNatural (altNaturalRep n) n .alternating :=
  C.alternatingNatural_of_intertwiner (θ := MulEquiv.refl _) (e := burnsideI16h_altE C)
    (fun γ w => burnsideI16h_altE_intertwine C γ w)

open CFSG.Quasithin.SteinbergCB.I16 in
theorem burnsideI16h_alt_finite {n k : ℕ} (C : DnCoords n k) :
    Finite (evenWeight n ⧸ constInEven n) :=
  Finite.of_equiv _ (burnsideI16h_altE C).symm.toEquiv

theorem burnsideI16h_p1 :
    h1Dim (altNaturalRep 5) = 0 ∧ h1Dim (altNaturalRep 7) = 0 ∧
      h1Dim (altNaturalRep 6) = 1 ∧ h1Dim (altNaturalRep 8) = 1 ∧
      Module.Projective (MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 5)))
        (altNaturalRep 5).asModule := by
  have h5 := burnsideI16h_altNatural CFSG.Quasithin.SteinbergCB.I16.coords5
  have h6 := burnsideI16h_altNatural CFSG.Quasithin.SteinbergCB.I16.coords6
  have h7 := burnsideI16h_altNatural CFSG.Quasithin.SteinbergCB.I16.coords7
  have h8 := burnsideI16h_altNatural CFSG.Quasithin.SteinbergCB.I16.coords8
  haveI := burnsideI16h_alt_finite CFSG.Quasithin.SteinbergCB.I16.coords5
  haveI := burnsideI16h_alt_finite CFSG.Quasithin.SteinbergCB.I16.coords6
  haveI := burnsideI16h_alt_finite CFSG.Quasithin.SteinbergCB.I16.coords7
  haveI := burnsideI16h_alt_finite CFSG.Quasithin.SteinbergCB.I16.coords8
  refine ⟨?_, ?_, ?_, ?_, CFSG.Quasithin.SteinbergCB.I16.projective_alternatingNatural_five h5⟩
  · rw [burnsideI16h_h1Dim_eq]
    exact CFSG.Quasithin.SteinbergCB.I16.finrank_H1_alternatingNatural_five h5
  · rw [burnsideI16h_h1Dim_eq]
    exact CFSG.Quasithin.SteinbergCB.I16.finrank_H1_alternatingNatural_seven h7
  · rw [burnsideI16h_h1Dim_eq]
    exact CFSG.Quasithin.SteinbergCB.I16.finrank_H1_alternatingNatural_six h6
  · rw [burnsideI16h_h1Dim_eq]
    exact CFSG.Quasithin.SteinbergCB.I16.finrank_H1_alternatingNatural_eight h8

theorem burnsideI16h_faithful_of_simple {G V : Type} [Group G] [IsSimpleGroup G]
    [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (hρ : ρ.IsIrreducible) (hdim : 2 ≤ Module.finrank (ZMod 2) V) : Function.Injective ρ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker ρ) with h | h
  · exact h
  · exfalso
    have htriv : ∀ g, ρ g = 1 := fun g => MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top g)
    have hpos : 0 < Module.finrank (ZMod 2) V := by omega
    haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos hpos
    haveI : Nontrivial V := Module.finrank_pos_iff.1 hpos
    obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := exists_ne 0
    let U : Subrepresentation ρ :=
      { toSubmodule := Submodule.span (ZMod 2) {v}
        apply_mem_toSubmodule := fun g w hw => by rw [htriv g]; exact hw }
    rcases hρ.eq_bot_or_eq_top U with hU | hU
    · have := congrArg Subrepresentation.toSubmodule hU
      have hv' : v ∈ (⊥ : Subrepresentation ρ).toSubmodule := by
        rw [← this]
        exact Submodule.mem_span_singleton_self v
      exact hv hv'
    · have h1 := congrArg Subrepresentation.toSubmodule hU
      have h2 : Module.finrank (ZMod 2) V = 1 := by
        have : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) = 1 :=
          finrank_span_singleton hv
        have h3 : Submodule.span (ZMod 2) {v} = ⊤ := h1
        rw [h3, finrank_top] at this
        exact this
      omega

theorem burnsideI16h_p8 :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
      (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V),
      ρ.IsIrreducible → Module.finrank (ZMod 2) V = 4 → h1Dim ρ = 0 := by
  intro V _ _ ρ hρ hdim
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hinj := burnsideI16h_faithful_of_simple ρ hρ (by omega)
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  rw [burnsideI16h_h1Dim_eq]
  exact CFSG.Quasithin.SteinbergCB.I16.finrank_H1_faithful_alt7 (MulEquiv.refl _) hinj hdim

theorem burnsideI16h_p9 :
    ∀ (G : Type) [Group G] [Finite G], IsHatCover G (alternatingGroup (Fin 6)) →
      ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V),
        Function.Injective ρ → ρ.IsIrreducible → Module.finrank (ZMod 2) V = 6 →
          h1Dim ρ = 0 := by
  intro G _ _ hG V _ _ ρ hinj hirr hdim
  obtain ⟨-, hcard, -⟩ := hG
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic (Subgroup.center G) := isCyclic_of_prime_card hcard
  haveI : IsCyclic (Multiplicative (ZMod 3)) := inferInstance
  let e : Subgroup.center G ≃* Multiplicative (ZMod 3) :=
    mulEquivOfCyclicCardEq (by rw [hcard]; exact (Nat.card_zmod 3).symm)
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  rw [burnsideI16h_h1Dim_eq]
  exact CFSG.Quasithin.SteinbergCB.I16.finrank_H1_faithful_center e hinj hirr
    (by rw [hdim]; norm_num)

theorem burnsideI16h_sp4_isModel (F : Type) [Field F] [CharP F 2] [Algebra (ZMod 2) F] :
    CFSG.Quasithin.Explicit.BinaryNaturalSp4Derived (sp4NaturalRep F) F := by
  let ψ : ↥(Matrix.symplecticGroup (Fin 2) F) ≃* ↥(TauCeti.GLSymplectic (Fin 2) F) :=
    (TauCeti.GLSymplectic.mulEquivSymplecticGroup (Fin 2) F).symm
  let θ₁ : sp4Derived F →* GL (Fin 2 ⊕ Fin 2) F :=
    ((TauCeti.GLSymplectic (Fin 2) F).subtype.comp ψ.toMonoidHom).comp (sp4Derived F).subtype
  have hinj : Function.Injective θ₁ := by
    intro x y h
    exact Subtype.ext (ψ.injective (Subtype.ext h))
  have hrange : θ₁.range = ⁅CFSG.Quasithin.Explicit.sp4 F, CFSG.Quasithin.Explicit.sp4 F⁆ := by
    have h1 : θ₁.range = Subgroup.map ((TauCeti.GLSymplectic (Fin 2) F).subtype.comp ψ.toMonoidHom)
        (sp4Derived F) := by
      rw [show θ₁ = ((TauCeti.GLSymplectic (Fin 2) F).subtype.comp ψ.toMonoidHom).comp
        (sp4Derived F).subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
    have h2 : Subgroup.map ψ.toMonoidHom (sp4Derived F) =
        commutator ↥(TauCeti.GLSymplectic (Fin 2) F) := by
      rw [sp4Derived, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ ψ.surjective]
      rfl
    rw [h1, ← Subgroup.map_map, h2, Subgroup.map_subtype_commutator,
      CFSG.Open.ASVolIRegistered.sp4_eq_statedSp,
      CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
  let θ : sp4Derived F ≃* ↥⁅CFSG.Quasithin.Explicit.sp4 F, CFSG.Quasithin.Explicit.sp4 F⁆ :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  refine CFSG.Open.ASVolIRegistered.isModel_nat _ _ θ (fun γ => ?_)
  show (((ψ (γ : ↥(Matrix.symplecticGroup (Fin 2) F)) : ↥(TauCeti.GLSymplectic (Fin 2) F)) :
    GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = _
  have h1 := TauCeti.GLSymplectic.coe_mulEquivSymplecticGroup (Fin 2) F
    (ψ (γ : ↥(Matrix.symplecticGroup (Fin 2) F)))
  have h2 : (TauCeti.GLSymplectic.mulEquivSymplecticGroup (Fin 2) F)
      (ψ (γ : ↥(Matrix.symplecticGroup (Fin 2) F))) = (γ : ↥(Matrix.symplecticGroup (Fin 2) F)) :=
    MulEquiv.apply_symm_apply _ _
  rw [h2] at h1
  exact h1.symm

section G2Model

variable (K : Type) [Field K] [CharP K 2]

theorem burnsideI16h_zornMul_eq (x y : quasithinZorn K) :
    quasithinZornMul x y = CFSG.Quasithin.Explicit.cayleyMul x y := by
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · funext i
    simp only [quasithinZornMul, CFSG.Quasithin.Explicit.cayleyMul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [CharTwo.sub_eq_add]
  · funext i
    simp only [quasithinZornMul, CFSG.Quasithin.Explicit.cayleyMul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]

theorem burnsideI16h_cayleyNorm_eq (x : quasithinZorn K) :
    CFSG.Quasithin.Explicit.cayleyNorm x = zornNorm K x := by
  simp only [CFSG.Quasithin.Explicit.cayleyNorm, zornNorm]
  rw [CharTwo.sub_eq_add]

theorem burnsideI16h_g2_eq_cayley :
    quasithinG2 K = CFSG.Quasithin.Explicit.cayleyGroup K := by
  apply le_antisymm
  · rw [quasithinG2, Subgroup.closure_le]
    intro g hg
    obtain ⟨h1, htr⟩ := g2_gen K g hg
    have hnorm : ∀ x, CFSG.Quasithin.Explicit.cayleyNorm (g x) =
        CFSG.Quasithin.Explicit.cayleyNorm x := by
      intro x
      have h2 := hg x x
      rw [zornMul_self, zornMul_self] at h2
      rw [map_sub, map_smul, map_smul, h1, htr x] at h2
      have h3 : zornNorm K x • zornOne K = zornNorm K (g x) • zornOne K := sub_right_injective h2
      have h4 := congrArg Prod.fst h3
      have h5 : zornNorm K x = zornNorm K (g x) := by simpa [zornOne] using h4
      rw [burnsideI16h_cayleyNorm_eq, burnsideI16h_cayleyNorm_eq, h5]
    refine ⟨h1, fun x y => ?_, htr, hnorm⟩
    rw [← burnsideI16h_zornMul_eq, ← burnsideI16h_zornMul_eq]
    exact hg x y
  · intro g hg
    obtain ⟨-, hm, -, -⟩ := hg
    refine Subgroup.subset_closure (fun x y => ?_)
    rw [burnsideI16h_zornMul_eq, burnsideI16h_zornMul_eq]
    exact hm x y

end G2Model

section G2Coords

variable (K : Type) [Field K] [CharP K 2]

@[expose] def burnsideI16h_zπ : quasithinZorn K →+ (Fin 3 → K) × (Fin 3 → K) where
  toFun x := (x.2.1, x.2.2.1)
  map_zero' := rfl
  map_add' _ _ := rfl

@[expose] def burnsideI16h_zι : (Fin 3 → K) × (Fin 3 → K) →+ quasithinZorn K where
  toFun y := (0, y.1, y.2, 0)
  map_zero' := rfl
  map_add' y y' := by
    refine Prod.ext (by simp) (Prod.ext rfl (Prod.ext rfl (by simp)))

theorem burnsideI16h_zπ_ι (y : (Fin 3 → K) × (Fin 3 → K)) :
    burnsideI16h_zπ K (burnsideI16h_zι K y) = y := rfl

theorem burnsideI16h_zornO0_form {x : quasithinZorn K} (hx : x.1 + x.2.2.2 = 0) :
    x.2.2.2 = x.1 := by
  have := CharTwo.add_eq_zero.1 hx
  exact this.symm

theorem burnsideI16h_zπ_ker {x : quasithinZorn K} (hx : x.1 + x.2.2.2 = 0)
    (hπ : burnsideI16h_zπ K x = 0) : ∃ c : K, x = (c, 0, 0, c) := by
  have h2 := burnsideI16h_zornO0_form K hx
  have hu : x.2.1 = 0 := congrArg Prod.fst hπ
  have hv : x.2.2.1 = 0 := congrArg Prod.snd hπ
  refine ⟨x.1, ?_⟩
  obtain ⟨a, u, v, b⟩ := x
  simp only at h2 hu hv ⊢
  rw [hu, hv, h2]

@[expose] def burnsideI16h_secHom :
    ↥(CFSG.Quasithin.zornO0 K) →* Multiplicative ((Fin 3 → K) × (Fin 3 → K)) where
  toFun m := Multiplicative.ofAdd
    (burnsideI16h_zπ K (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))))
  map_one' := by
    change Multiplicative.ofAdd (burnsideI16h_zπ K 0) = 1
    rw [map_zero]
    rfl
  map_mul' m m' := by
    change Multiplicative.ofAdd (burnsideI16h_zπ K
      (Multiplicative.toAdd ((m : Multiplicative (quasithinZorn K)) *
        (m' : Multiplicative (quasithinZorn K))))) = _
    rw [toAdd_mul, map_add]
    rfl

theorem burnsideI16h_secHom_eq_one {m : ↥(CFSG.Quasithin.zornO0 K)}
    (hm : (m : Multiplicative (quasithinZorn K)) ∈ CFSG.Quasithin.zornR K) : burnsideI16h_secHom K m = 1 := by
  obtain ⟨c, hc⟩ := hm
  change Multiplicative.ofAdd (burnsideI16h_zπ K (Multiplicative.toAdd (m : Multiplicative _))) = 1
  rw [hc]
  rfl

@[expose] noncomputable def burnsideI16h_secEquiv :
    (↥(CFSG.Quasithin.zornO0 K) ⧸ (CFSG.Quasithin.zornR K).subgroupOf (CFSG.Quasithin.zornO0 K)) ≃*
      Multiplicative ((Fin 3 → K) × (Fin 3 → K)) :=
  MulEquiv.ofBijective
    (QuotientGroup.lift ((CFSG.Quasithin.zornR K).subgroupOf (CFSG.Quasithin.zornO0 K)) (burnsideI16h_secHom K)
      fun x hx => by
        rw [Subgroup.mem_subgroupOf] at hx
        exact burnsideI16h_secHom_eq_one K hx)
    ⟨fun x y hxy => by
      induction x using QuotientGroup.induction_on with
      | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
      rw [QuotientGroup.lift_mk, QuotientGroup.lift_mk] at hxy
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h : burnsideI16h_zπ K (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))) =
          burnsideI16h_zπ K (Multiplicative.toAdd (y : Multiplicative (quasithinZorn K))) :=
        congrArg Multiplicative.toAdd hxy
      have hxm : (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).1 +
          (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).2.2.2 = 0 := x.2
      have hym : (Multiplicative.toAdd (y : Multiplicative (quasithinZorn K))).1 +
          (Multiplicative.toAdd (y : Multiplicative (quasithinZorn K))).2.2.2 = 0 := y.2
      have hd : burnsideI16h_zπ K (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K)) +
          Multiplicative.toAdd (y : Multiplicative (quasithinZorn K))) = 0 := by
        rw [map_add, h]
        have : ∀ z : (Fin 3 → K) × (Fin 3 → K), z + z = 0 := by
          intro z
          ext i
          · simp [CharTwo.add_self_eq_zero]
          · simp [CharTwo.add_self_eq_zero]
        exact this _
      have hsum : (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K)) +
          Multiplicative.toAdd (y : Multiplicative (quasithinZorn K))).1 +
          (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K)) +
            Multiplicative.toAdd (y : Multiplicative (quasithinZorn K))).2.2.2 = 0 := by
        simp only [Prod.fst_add, Prod.snd_add]
        calc _ = ((Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).1 +
            (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).2.2.2) +
            ((Multiplicative.toAdd (y : Multiplicative (quasithinZorn K))).1 +
            (Multiplicative.toAdd (y : Multiplicative (quasithinZorn K))).2.2.2) := by ring
          _ = 0 := by rw [hxm, hym, add_zero]
      obtain ⟨c, hc⟩ := burnsideI16h_zπ_ker K hsum hd
      refine ⟨c, ?_⟩
      show Multiplicative.toAdd (((x⁻¹ * y : ↥(CFSG.Quasithin.zornO0 K)) : Multiplicative (quasithinZorn K))) =
        (c, 0, 0, c)
      rw [Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, toAdd_inv]
      have : -Multiplicative.toAdd (x : Multiplicative (quasithinZorn K)) =
          Multiplicative.toAdd (x : Multiplicative (quasithinZorn K)) := by
        ext <;> simp [CharTwo.neg_eq]
      rw [this]
      exact hc,
    fun z => ⟨QuotientGroup.mk ⟨Multiplicative.ofAdd (burnsideI16h_zι K (Multiplicative.toAdd z)),
      by change (0 : K) + 0 = 0; exact add_zero 0⟩, by
        rw [QuotientGroup.lift_mk]
        change Multiplicative.ofAdd (burnsideI16h_zπ K (burnsideI16h_zι K (Multiplicative.toAdd z))) = z
        exact ofAdd_toAdd z⟩⟩

end G2Coords

section G2Model2

variable (K : Type) [Field K] [CharP K 2] [Algebra (ZMod 2) K]

@[expose] noncomputable def burnsideI16h_zE :
    (zornTraceZero K ⧸ zornLine K) ≃+ (Fin 3 → K) × (Fin 3 → K) := by
  let f : zornTraceZero K →ₗ[ZMod 2] (Fin 3 → K) × (Fin 3 → K) :=
    ((burnsideI16h_zπ K).toZModLinearMap 2).comp (zornTraceZero K).subtype
  have hker : zornLine K ≤ LinearMap.ker f := by
    intro x hx
    have hx' : (x : quasithinZorn K) ∈ Submodule.span K {zornOne K} := hx
    rw [Submodule.mem_span_singleton] at hx'
    obtain ⟨c, hc⟩ := hx'
    rw [LinearMap.mem_ker]
    show burnsideI16h_zπ K (x : quasithinZorn K) = 0
    rw [← hc]
    simp [burnsideI16h_zπ, zornOne]
  have hinj : Function.Injective ((zornLine K).liftQ f hker) := by
    intro a b hab
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.liftQ_apply, Submodule.liftQ_apply] at hab
    rw [Submodule.Quotient.eq]
    have hxy : burnsideI16h_zπ K ((x - y : zornTraceZero K) : quasithinZorn K) = 0 := by
      have : burnsideI16h_zπ K (x : quasithinZorn K) = burnsideI16h_zπ K (y : quasithinZorn K) :=
        hab
      show burnsideI16h_zπ K ((x : quasithinZorn K) - y) = 0
      rw [map_sub, this, sub_self]
    have htr : ((x - y : zornTraceZero K) : quasithinZorn K).1 +
        ((x - y : zornTraceZero K) : quasithinZorn K).2.2.2 = 0 := (x - y).2
    obtain ⟨c, hc⟩ := burnsideI16h_zπ_ker K htr hxy
    show ((x - y : zornTraceZero K) : quasithinZorn K) ∈ Submodule.span K {zornOne K}
    rw [hc, Submodule.mem_span_singleton]
    exact ⟨c, by simp [zornOne]⟩
  have hsurj : Function.Surjective ((zornLine K).liftQ f hker) := by
    intro y
    refine ⟨Submodule.Quotient.mk ⟨burnsideI16h_zι K y, ?_⟩, ?_⟩
    · show (0 : K) + 0 = 0
      exact add_zero 0
    · rw [Submodule.liftQ_apply]
      exact burnsideI16h_zπ_ι K y
  exact (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).toAddEquiv

end G2Model2

section G2Model3

variable (K : Type) [Field K] [CharP K 2] [Algebra (ZMod 2) K]

@[expose] noncomputable def burnsideI16h_coordEquiv :
    Additive (↥(CFSG.Quasithin.zornO0 K) ⧸ (CFSG.Quasithin.zornR K).subgroupOf
      (CFSG.Quasithin.zornO0 K)) ≃+ (Fin 3 → K) × (Fin 3 → K) :=
  (MulEquiv.toAdditive (burnsideI16h_secEquiv K)).trans (AddEquiv.additiveMultiplicative _)

theorem burnsideI16h_coord_mk (m : ↥(CFSG.Quasithin.zornO0 K)) :
    burnsideI16h_coordEquiv K (Additive.ofMul (QuotientGroup.mk m)) =
      burnsideI16h_zπ K (Multiplicative.toAdd (m : Multiplicative (quasithinZorn K))) := rfl

theorem burnsideI16h_cayley_fix_line {g : quasithinZorn K ≃ₗ[K] quasithinZorn K}
    (hg : g ∈ CFSG.Quasithin.Explicit.cayleyGroup K) (c : K) :
    g ((c, 0, 0, c) : quasithinZorn K) = (c, 0, 0, c) := by
  have h : ((c, 0, 0, c) : quasithinZorn K) = c • CFSG.Quasithin.Explicit.cayleyOne K := by
    simp [CFSG.Quasithin.Explicit.cayleyOne]
  rw [h, map_smul, hg.1]

theorem burnsideI16h_zornR_le : CFSG.Quasithin.zornR K ≤ CFSG.Quasithin.zornO0 K := by
  rintro x ⟨c, hc⟩
  show (Multiplicative.toAdd x).1 + (Multiplicative.toAdd x).2.2.2 = 0
  rw [hc]
  exact CharTwo.add_self_eq_zero c

theorem burnsideI16h_act_sec {Γ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)}
    (hΓ : Γ ≤ CFSG.Quasithin.Explicit.cayleyGroup K) (g : ↥Γ)
    {m : Multiplicative (quasithinZorn K)} (hm : m ∈ CFSG.Quasithin.zornO0 K) :
    CFSG.Quasithin.zornAct Γ g m ∈ CFSG.Quasithin.zornO0 K := by
  have h1 := (hΓ g.2).2.2.1 (Multiplicative.toAdd m)
  have h2 : (Multiplicative.toAdd m).1 + (Multiplicative.toAdd m).2.2.2 = 0 := hm
  show ((g : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd m)).1 +
    ((g : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd m)).2.2.2 = 0
  exact h1.trans h2

theorem burnsideI16h_act_line {Γ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)}
    (hΓ : Γ ≤ CFSG.Quasithin.Explicit.cayleyGroup K) (g : ↥Γ)
    {m : Multiplicative (quasithinZorn K)} (hm : m ∈ CFSG.Quasithin.zornR K) :
    CFSG.Quasithin.zornAct Γ g m ∈ CFSG.Quasithin.zornR K := by
  obtain ⟨c, hc⟩ := hm
  refine ⟨c, ?_⟩
  show (g : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd m) = (c, 0, 0, c)
  rw [hc]
  exact burnsideI16h_cayley_fix_line K (hΓ g.2) c

theorem burnsideI16h_g2_range :
    ((quasithinG2 K).subtype.comp (commutator ↥(quasithinG2 K)).subtype).range =
      ⁅CFSG.Quasithin.Explicit.cayleyGroup K, CFSG.Quasithin.Explicit.cayleyGroup K⁆ := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_subtype_commutator,
    burnsideI16h_g2_eq_cayley]

@[expose] noncomputable def burnsideI16h_g2θ :
    ↥(commutator ↥(quasithinG2 K)) ≃*
      ↥⁅CFSG.Quasithin.Explicit.cayleyGroup K, CFSG.Quasithin.Explicit.cayleyGroup K⁆ :=
  (MonoidHom.ofInjective (f := (quasithinG2 K).subtype.comp (commutator ↥(quasithinG2 K)).subtype)
    (fun _ _ h => Subtype.ext (Subtype.ext h))).trans
    (MulEquiv.subgroupCongr (burnsideI16h_g2_range K))

theorem burnsideI16h_zE_rep (γ : ↥(commutator ↥(quasithinG2 K))) (x : zornTraceZero K) :
    burnsideI16h_zE K (g2DerivedNaturalRep K γ (Submodule.Quotient.mk x)) =
      burnsideI16h_zπ K (((γ : ↥(quasithinG2 K)) : quasithinZorn K ≃ₗ[K] quasithinZorn K)
        (x : quasithinZorn K)) := rfl

theorem burnsideI16h_cayley_coord {g : quasithinZorn K ≃ₗ[K] quasithinZorn K}
    (hg : g ∈ CFSG.Quasithin.Explicit.cayleyGroup K) {x y : quasithinZorn K}
    (hx : x.1 + x.2.2.2 = 0) (hy : y.1 + y.2.2.2 = 0)
    (h : burnsideI16h_zπ K x = burnsideI16h_zπ K y) :
    burnsideI16h_zπ K (g x) = burnsideI16h_zπ K (g y) := by
  have hxy : burnsideI16h_zπ K (x - y) = 0 := by rw [map_sub, h, sub_self]
  have htr : (x - y).1 + (x - y).2.2.2 = 0 := by
    simp only [Prod.fst_sub, Prod.snd_sub]
    calc _ = (x.1 + x.2.2.2) - (y.1 + y.2.2.2) := by ring
      _ = 0 := by rw [hx, hy, sub_zero]
  obtain ⟨c, hc⟩ := burnsideI16h_zπ_ker K htr hxy
  have h1 : g (x - y) = (c, 0, 0, c) := by
    rw [hc]
    exact burnsideI16h_cayley_fix_line K hg c
  rw [map_sub] at h1
  have h2 : burnsideI16h_zπ K (g x - g y) = 0 := by rw [h1]; rfl
  rw [map_sub, sub_eq_zero] at h2
  exact h2

theorem burnsideI16h_g2_mem_cayley (g : ↥(quasithinG2 K)) :
    (g : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈ CFSG.Quasithin.Explicit.cayleyGroup K := by
  rw [← burnsideI16h_g2_eq_cayley]
  exact g.2

theorem burnsideI16h_g2_final (γ : ↥(commutator ↥(quasithinG2 K))) (x : zornTraceZero K)
    (m : Multiplicative (quasithinZorn K)) (hm0 : m ∈ CFSG.Quasithin.zornO0 K)
    (hm : CFSG.Quasithin.zornAct ⁅CFSG.Quasithin.Explicit.cayleyGroup K,
      CFSG.Quasithin.Explicit.cayleyGroup K⁆ (burnsideI16h_g2θ K γ) m ∈
        CFSG.Quasithin.zornO0 K)
    (hw : ((burnsideI16h_zE K).trans (burnsideI16h_coordEquiv K).symm)
        (Submodule.Quotient.mk x) =
      Additive.ofMul (QuotientGroup.mk (⟨m, hm0⟩ : ↥(CFSG.Quasithin.zornO0 K)) :
        ↥(CFSG.Quasithin.zornO0 K) ⧸ (CFSG.Quasithin.zornR K).subgroupOf
          (CFSG.Quasithin.zornO0 K))) :
    ((burnsideI16h_zE K).trans (burnsideI16h_coordEquiv K).symm)
        (g2DerivedNaturalRep K γ (Submodule.Quotient.mk x)) =
      Additive.ofMul (QuotientGroup.mk (⟨CFSG.Quasithin.zornAct ⁅CFSG.Quasithin.Explicit.cayleyGroup K,
        CFSG.Quasithin.Explicit.cayleyGroup K⁆ (burnsideI16h_g2θ K γ) m, hm⟩ :
          ↥(CFSG.Quasithin.zornO0 K)) :
        ↥(CFSG.Quasithin.zornO0 K) ⧸ (CFSG.Quasithin.zornR K).subgroupOf
          (CFSG.Quasithin.zornO0 K)) := by
  have hw' : burnsideI16h_zπ K (x : quasithinZorn K) =
      burnsideI16h_zπ K (Multiplicative.toAdd m) := by
    have h := congrArg (burnsideI16h_coordEquiv K) hw
    rw [AddEquiv.trans_apply, AddEquiv.apply_symm_apply] at h
    exact h.trans (burnsideI16h_coord_mk K ⟨m, hm0⟩)
  rw [AddEquiv.trans_apply, AddEquiv.symm_apply_eq, burnsideI16h_zE_rep,
    burnsideI16h_coord_mk]
  exact burnsideI16h_cayley_coord K (burnsideI16h_g2_mem_cayley K (γ : ↥(quasithinG2 K)))
    x.2 hm0 hw'

theorem burnsideI16h_g2_isModel :
    CFSG.Quasithin.Explicit.G2Natural (g2DerivedNaturalRep K) K .derived := by
  show (CFSG.Quasithin.FFModel.zornQ ⁅CFSG.Quasithin.Explicit.cayleyGroup K,
    CFSG.Quasithin.Explicit.cayleyGroup K⁆).IsModel (g2DerivedNaturalRep K)
  have hΓ₀ : ⁅CFSG.Quasithin.Explicit.cayleyGroup K, CFSG.Quasithin.Explicit.cayleyGroup K⁆ ≤
      CFSG.Quasithin.Explicit.cayleyGroup K := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  refine ⟨burnsideI16h_g2θ K, (burnsideI16h_zE K).trans (burnsideI16h_coordEquiv K).symm,
    burnsideI16h_zornR_le K, fun g m hm => burnsideI16h_act_sec K hΓ₀ g hm,
    fun g m hm => burnsideI16h_act_line K hΓ₀ g hm, ?_⟩
  intro γ w m hm hw
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨m, hm0⟩ := m
  exact burnsideI16h_g2_final K γ x m hm0 hm hw

end G2Model3

section G2Finite

variable (K : Type) [Field K] [Finite K] [Algebra (ZMod 2) K]

theorem burnsideI16h_zorn_finite : Finite (quasithinZorn K) := by
  unfold quasithinZorn
  infer_instance

theorem burnsideI16h_g2_finite : Finite ↥(quasithinG2 K) := by
  haveI := burnsideI16h_zorn_finite K
  haveI : Finite (quasithinZorn K → quasithinZorn K) := inferInstance
  refine Finite.of_injective (fun g : ↥(quasithinG2 K) =>
    ((g : quasithinZorn K ≃ₗ[K] quasithinZorn K) : quasithinZorn K → quasithinZorn K))
    (fun a b h => Subtype.ext (LinearEquiv.coe_injective h))

theorem burnsideI16h_g2_module_finite : Finite (zornTraceZero K ⧸ zornLine K) := by
  haveI := burnsideI16h_zorn_finite K
  haveI : Finite (zornTraceZero K) := Subtype.finite
  exact Quotient.finite _

end G2Finite

section JPHelpers2

theorem burnsideI16h_p5 :
    ∀ n : ℕ, 1 ≤ n → h1Dim (sp4NaturalRep (GaloisField 2 n)) = n ∧
      h1Dim (g2DerivedNaturalRep (GaloisField 2 n)) = n := by
  intro n hn
  obtain ⟨-, -, -, j4, j5, -⟩ := CFSG.Quasithin.JonesParshall.natural_binary_first_cohomology_sector.{0, 0}
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 n (by omega)
  refine ⟨?_, ?_⟩
  · rw [burnsideI16h_h1Dim_eq]
    exact j4 hcard hn (burnsideI16h_sp4_isModel _)
  · haveI := burnsideI16h_g2_finite (GaloisField 2 n)
    haveI := burnsideI16h_g2_module_finite (GaloisField 2 n)
    haveI : Finite ↥(commutator ↥(quasithinG2 (GaloisField 2 n))) := Subtype.finite
    rw [burnsideI16h_h1Dim_eq]
    exact j5 hcard hn (burnsideI16h_g2_isModel _)

end JPHelpers2

section QuadExt

open Polynomial in
theorem burnsideI16h_exists_quad_ext {K : Type} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (ω : F),
      Module.finrank K F = 2 ∧ ω ^ 2 + algebraMap K F b * ω + algebraMap K F c = 0 := by
  have hdeg : (X ^ 2 + C b * X + C c : K[X]).natDegree = 2 := by compute_degree!
  have hirr' : Irreducible (X ^ 2 + C b * X + C c : K[X]) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]; simp
    · intro s hs
      apply hirr s
      simpa using hs
  haveI : Fact (Irreducible (X ^ 2 + C b * X + C c : K[X])) := ⟨hirr'⟩
  refine ⟨AdjoinRoot (X ^ 2 + C b * X + C c : K[X]), inferInstance, inferInstance,
    AdjoinRoot.root _, ?_, ?_⟩
  · rw [PowerBasis.finrank (AdjoinRoot.powerBasis hirr'.ne_zero)]
    simp [hdeg]
  · have := AdjoinRoot.eval₂_root (X ^ 2 + C b * X + C c : K[X])
    simpa using this

end QuadExt

section QuadField

open CFSG.Quasithin CFSG.Quasithin.JonesParshall

variable {K : Type} [Field K] [Fintype K] [CharP K 2]
  {F : Type} [Field F] [Fintype F] [Algebra K F] [CharP F 2]

theorem burnsideI16h_sig_alg {n : ℕ} (hK : Fintype.card K = 2 ^ n) (k : K) :
    sig n (algebraMap K F k) = algebraMap K F k := by
  rw [sig_apply, ← map_pow, ← hK, FiniteField.pow_card]

theorem burnsideI16h_sig_fixed {n : ℕ} (hK : Fintype.card K = 2 ^ n) (hn : 1 ≤ n) {x : F}
    (hx : sig n x = x) : ∃ k : K, algebraMap K F k = x := by
  classical
  have hq1 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  let S : Finset F := Finset.univ.filter (fun x : F => x ^ 2 ^ n = x)
  let T : Finset F := Finset.univ.image (algebraMap K F)
  have hTS : T ⊆ S := by
    intro y hy
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hy
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have := burnsideI16h_sig_alg (F := F) hK k
    rwa [sig_apply] at this
  have hTc : T.card = 2 ^ n := by
    rw [Finset.card_image_of_injective _ (algebraMap K F).injective, Finset.card_univ, hK]
  have hSc : S.card ≤ 2 ^ n := by
    have h := Polynomial.card_le_degree_of_subset_roots
      (p := (Polynomial.X ^ 2 ^ n - Polynomial.X : Polynomial F)) (Z := S) (by
        intro y hy
        rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero F hq1)]
        have hy' := (Finset.mem_filter.1 hy).2
        simp [Polynomial.IsRoot, hy'])
    rwa [FiniteField.X_pow_card_sub_X_natDegree_eq F hq1] at h
  have hTS' : T = S := Finset.eq_of_subset_of_card_le hTS (by omega)
  have hxS : x ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, by rwa [sig_apply] at hx⟩
  rw [← hTS'] at hxS
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hxS
  exact ⟨k, hk⟩

variable {b c : K}

theorem burnsideI16h_sig_omega {n : ℕ} (hK : Fintype.card K = 2 ^ n) (hn : 1 ≤ n) {ω : F}
    (hω : ω ^ 2 + algebraMap K F b * ω + algebraMap K F c = 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : sig n ω = ω + algebraMap K F b := by
  have h2c : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h1 : (sig n ω) ^ 2 + algebraMap K F b * sig n ω + algebraMap K F c = 0 := by
    have := congrArg (sig n) hω
    simpa [map_add, map_mul, map_pow, burnsideI16h_sig_alg (F := F) hK] using this
  have h3 : (sig n ω + ω) * (sig n ω + ω + algebraMap K F b) = 0 := by
    linear_combination h1 + hω + (sig n ω * ω - algebraMap K F c) * h2c
  rcases mul_eq_zero.1 h3 with h | h
  · exfalso
    have hfix : sig n ω = ω := CharTwo.add_eq_zero.1 h
    obtain ⟨k, hk⟩ := burnsideI16h_sig_fixed hK hn hfix
    apply hirr k
    apply (algebraMap K F).injective
    rw [map_zero, map_add, map_add, map_mul, map_pow, hk]
    exact hω
  · have := CharTwo.add_eq_zero.1 h
    linear_combination this - ω * h2c

end QuadField

section Setup

open CFSG.Quasithin CFSG.Quasithin.JonesParshall

structure burnsideI16h_Setup (K F : Type) [Field K] [Fintype K] [CharP K 2] [Field F] [Fintype F]
    [Algebra K F] [CharP F 2] where
  n : ℕ
  b : K
  c : K
  hn : 1 ≤ n
  hK : Fintype.card K = 2 ^ n
  ω : F
  hω : ω ^ 2 + algebraMap K F b * ω + algebraMap K F c = 0
  hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0
  hrank : Module.finrank K F = 2

variable {K F : Type} [Field K] [Fintype K] [CharP K 2] [Field F] [Fintype F] [Algebra K F]
  [CharP F 2] (S : burnsideI16h_Setup K F)

@[expose] noncomputable def burnsideI16h_coordMap (ω : F) : (K × K) →ₗ[K] F :=
  (Algebra.linearMap K F).coprod (LinearMap.toSpanSingleton K F ω)

theorem burnsideI16h_coordMap_apply (ω : F) (u v : K) :
    burnsideI16h_coordMap ω (u, v) = algebraMap K F u + algebraMap K F v * ω := by
  simp [burnsideI16h_coordMap, Algebra.smul_def]

theorem burnsideI16h_coordMap_bijective : Function.Bijective (burnsideI16h_coordMap (K := K) S.ω) := by
  have hinj : Function.Injective (burnsideI16h_coordMap (K := K) S.ω) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, v⟩ h
    rw [burnsideI16h_coordMap_apply] at h
    have hv : v = 0 := by
      by_contra hv0
      have hv0' : algebraMap K F v ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).2 hv0
      have hω' : S.ω = algebraMap K F (-u / v) := by
        rw [map_div₀, map_neg]
        field_simp
        linear_combination h
      refine S.hirr (-u / v) ((algebraMap K F).injective ?_)
      rw [map_zero, map_add, map_add, map_mul, map_pow, ← hω']
      exact S.hω
    subst hv
    simp only [map_zero, zero_mul, add_zero] at h
    have hu : u = 0 := (algebraMap K F).injective (by rw [h, map_zero])
    rw [hu]
    rfl
  refine ⟨hinj, ?_⟩
  have hcard : Nat.card F = Nat.card (K × K) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := F), S.hrank, Nat.card_prod, sq]
  exact (Function.Injective.bijective_of_nat_card_le hinj hcard.le).2

@[expose] noncomputable def burnsideI16h_ocoordEquiv : (K × K) ≃ₗ[K] F :=
  LinearEquiv.ofBijective _ (burnsideI16h_coordMap_bijective S)

theorem burnsideI16h_ocoordEquiv_apply (u v : K) :
    burnsideI16h_ocoordEquiv S (u, v) = algebraMap K F u + algebraMap K F v * S.ω :=
  burnsideI16h_coordMap_apply S.ω u v

theorem burnsideI16h_coord_spec (z : F) :
    algebraMap K F ((burnsideI16h_ocoordEquiv S).symm z).1 +
      algebraMap K F ((burnsideI16h_ocoordEquiv S).symm z).2 * S.ω = z := by
  set p := (burnsideI16h_ocoordEquiv S).symm z with hp
  have h : burnsideI16h_ocoordEquiv S p = z := (burnsideI16h_ocoordEquiv S).apply_symm_apply z
  rw [← h]
  exact (burnsideI16h_ocoordEquiv_apply S p.1 p.2).symm

end Setup

section Hermitian

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix

variable {K F : Type} [Field K] [Fintype K] [CharP K 2] [Field F] [Fintype F] [Algebra K F]
  [CharP F 2] (S : burnsideI16h_Setup K F)

abbrev burnsideI16h_OI : Type := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

theorem burnsideI16h_fin1 (i : Fin (2 - 1)) : i = 0 := Fin.fin_one_eq_zero i

theorem burnsideI16h_hF : Fintype.card F = 2 ^ (2 * S.n) := by
  rw [Module.card_eq_pow_finrank (K := K) (V := F), S.hrank, S.hK, ← pow_mul, mul_comm]

theorem burnsideI16h_hσ : ∀ x : F, sig S.n (sig S.n x) = x := sig_sig (burnsideI16h_hF S)

theorem burnsideI16h_sig_coord (u v : K) :
    sig S.n (algebraMap K F u + algebraMap K F v * S.ω) =
      algebraMap K F u + algebraMap K F v * (S.ω + algebraMap K F S.b) := by
  rw [map_add, map_mul, burnsideI16h_sig_alg (F := F) S.hK, burnsideI16h_sig_alg (F := F) S.hK,
    burnsideI16h_sig_omega S.hK S.hn S.hω S.hirr]

theorem burnsideI16h_norm_coord (u v : K) :
    (algebraMap K F u + algebraMap K F v * S.ω) *
        sig S.n (algebraMap K F u + algebraMap K F v * S.ω) =
      algebraMap K F (u ^ 2 + S.b * u * v + S.c * v ^ 2) := by
  have h2c : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [burnsideI16h_sig_coord S]
  simp only [map_add, map_mul, map_pow]
  linear_combination (algebraMap K F v) ^ 2 * S.hω +
    (algebraMap K F u * algebraMap K F v * S.ω - algebraMap K F S.c * algebraMap K F v ^ 2) * h2c

@[expose] noncomputable def burnsideI16h_c0 : F →ₗ[K] K :=
  (LinearMap.fst K K K).comp (burnsideI16h_ocoordEquiv S).symm.toLinearMap

@[expose] noncomputable def burnsideI16h_c1 : F →ₗ[K] K :=
  (LinearMap.snd K K K).comp (burnsideI16h_ocoordEquiv S).symm.toLinearMap

theorem burnsideI16h_coord_symm (u v : K) :
    (burnsideI16h_ocoordEquiv S).symm (algebraMap K F u + algebraMap K F v * S.ω) = (u, v) := by
  rw [← burnsideI16h_ocoordEquiv_apply, LinearEquiv.symm_apply_apply]

theorem burnsideI16h_c0_coord (u v : K) :
    burnsideI16h_c0 S (algebraMap K F u + algebraMap K F v * S.ω) = u := by
  simp [burnsideI16h_c0, burnsideI16h_coord_symm S]

theorem burnsideI16h_c1_coord (u v : K) :
    burnsideI16h_c1 S (algebraMap K F u + algebraMap K F v * S.ω) = v := by
  simp [burnsideI16h_c1, burnsideI16h_coord_symm S]

theorem burnsideI16h_c0_alg (x : K) : burnsideI16h_c0 S (algebraMap K F x) = x := by
  have := burnsideI16h_c0_coord S x 0
  simpa using this

@[expose] noncomputable def burnsideI16h_zf (u v : K) : F :=
  algebraMap K F u + algebraMap K F v * S.ω

@[expose] noncomputable def burnsideI16h_hmat (x y u v : K) : Matrix (Fin 2) (Fin 2) F :=
  !![algebraMap K F x, burnsideI16h_zf S u v; sig S.n (burnsideI16h_zf S u v), algebraMap K F y]

@[expose] noncomputable def burnsideI16h_H : (burnsideI16h_OI → K) →ₗ[K] Matrix (Fin 2) (Fin 2) F where
  toFun w := burnsideI16h_hmat S (w (Sum.inl 0)) (w (Sum.inr (Sum.inl 0)))
    (w (Sum.inr (Sum.inr 0))) (w (Sum.inr (Sum.inr 1)))
  map_add' w w' := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [burnsideI16h_hmat, burnsideI16h_zf, add_mul, add_add_add_comm]
  map_smul' k w := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [burnsideI16h_hmat, burnsideI16h_zf, Algebra.smul_def, mul_add, mul_assoc,
        burnsideI16h_sig_alg (F := F) S.hK]

theorem burnsideI16h_H_mem (w : burnsideI16h_OI → K) : burnsideI16h_H S w ∈ hermA S.n F := by
  refine mem_hermA_of fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [burnsideI16h_H, burnsideI16h_hmat, burnsideI16h_zf, burnsideI16h_hσ S,
      burnsideI16h_sig_alg (F := F) S.hK]

@[expose] noncomputable def burnsideI16h_eps : Matrix (Fin 2) (Fin 2) F →ₗ[K] (burnsideI16h_OI → K) where
  toFun X := Sum.elim (fun _ => burnsideI16h_c0 S (X 0 0))
    (Sum.elim (fun _ => burnsideI16h_c0 S (X 1 1))
      ![burnsideI16h_c0 S (X 0 1), burnsideI16h_c1 S (X 0 1)])
  map_add' X Y := by
    funext i
    rcases i with i | i | j
    · simp
    · simp
    · fin_cases j <;> simp
  map_smul' k X := by
    funext i
    rcases i with i | i | j
    · simp
    · simp
    · fin_cases j <;> simp

theorem burnsideI16h_eps_H (w : burnsideI16h_OI → K) :
    burnsideI16h_eps S (burnsideI16h_H S w) = w := by
  funext i
  rcases i with i | i | j
  · rw [burnsideI16h_fin1 i]
    simp [burnsideI16h_eps, burnsideI16h_H, burnsideI16h_hmat, burnsideI16h_c0_alg]
  · rw [burnsideI16h_fin1 i]
    simp [burnsideI16h_eps, burnsideI16h_H, burnsideI16h_hmat, burnsideI16h_c0_alg]
  · fin_cases j
    · simp [burnsideI16h_eps, burnsideI16h_H, burnsideI16h_hmat, burnsideI16h_zf,
        burnsideI16h_c0_coord]
    · simp [burnsideI16h_eps, burnsideI16h_H, burnsideI16h_hmat, burnsideI16h_zf,
        burnsideI16h_c1_coord]

theorem burnsideI16h_H_eps {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ hermA S.n F) :
    burnsideI16h_H S (burnsideI16h_eps S X) = X := by
  have h00 := hermA_apply hX 0 0
  have h11 := hermA_apply hX 1 1
  have h10 := hermA_apply hX 1 0
  obtain ⟨k0, hk0⟩ := burnsideI16h_sig_fixed S.hK S.hn h00
  obtain ⟨k1, hk1⟩ := burnsideI16h_sig_fixed S.hK S.hn h11
  have hz : burnsideI16h_zf S (burnsideI16h_c0 S (X 0 1)) (burnsideI16h_c1 S (X 0 1)) = X 0 1 :=
    burnsideI16h_coord_spec S (X 0 1)
  ext i j
  fin_cases i <;> fin_cases j
  · simp [burnsideI16h_H, burnsideI16h_eps, burnsideI16h_hmat, ← hk0, burnsideI16h_c0_alg]
  · simpa [burnsideI16h_H, burnsideI16h_eps, burnsideI16h_hmat] using hz
  · simp [burnsideI16h_H, burnsideI16h_eps, burnsideI16h_hmat, hz, h10]
  · simp [burnsideI16h_H, burnsideI16h_eps, burnsideI16h_hmat, ← hk1, burnsideI16h_c0_alg]

@[expose] noncomputable def burnsideI16h_Tg (g : SL(2, F)) :
    Matrix (Fin 2) (Fin 2) F →ₗ[K] Matrix (Fin 2) (Fin 2) F :=
  (LinearMap.mulLeft K (g : Matrix (Fin 2) (Fin 2) F)).comp
    (LinearMap.mulRight K (frobPow S.n (g : Matrix (Fin 2) (Fin 2) F))ᵀ)

theorem burnsideI16h_Tg_apply (g : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F) :
    burnsideI16h_Tg S g X =
      (g : Matrix (Fin 2) (Fin 2) F) * X * (frobPow S.n (g : Matrix (Fin 2) (Fin 2) F))ᵀ := by
  simp [burnsideI16h_Tg, Matrix.mul_assoc]

theorem burnsideI16h_Tg_mem {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ hermA S.n F) (g : SL(2, F)) :
    burnsideI16h_Tg S g X ∈ hermA S.n F := by
  rw [burnsideI16h_Tg_apply]
  exact twist_mem S.n (burnsideI16h_hσ S) hX _

theorem burnsideI16h_Tg_mul (g h : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) F) :
    burnsideI16h_Tg S (g * h) X = burnsideI16h_Tg S g (burnsideI16h_Tg S h X) := by
  simp only [burnsideI16h_Tg_apply, Matrix.SpecialLinearGroup.coe_mul,
    JonesParshall.frobPow_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem burnsideI16h_Tg_one (X : Matrix (Fin 2) (Fin 2) F) :
    burnsideI16h_Tg S (1 : SL(2, F)) X = X := by
  simp [burnsideI16h_Tg_apply, JonesParshall.frobPow_eq_map]

@[expose] noncomputable def burnsideI16h_L (g : SL(2, F)) :
    (burnsideI16h_OI → K) →ₗ[K] (burnsideI16h_OI → K) :=
  (burnsideI16h_eps S).comp ((burnsideI16h_Tg S g).comp (burnsideI16h_H S))

theorem burnsideI16h_H_L (g : SL(2, F)) (w : burnsideI16h_OI → K) :
    burnsideI16h_H S (burnsideI16h_L S g w) = burnsideI16h_Tg S g (burnsideI16h_H S w) :=
  burnsideI16h_H_eps S (burnsideI16h_Tg_mem S (burnsideI16h_H_mem S w) g)

theorem burnsideI16h_L_mul (g h : SL(2, F)) : burnsideI16h_L S (g * h) = burnsideI16h_L S g *
    burnsideI16h_L S h := by
  refine LinearMap.ext fun w => ?_
  change burnsideI16h_eps S (burnsideI16h_Tg S (g * h) (burnsideI16h_H S w)) =
    burnsideI16h_L S g (burnsideI16h_L S h w)
  rw [burnsideI16h_Tg_mul]
  change _ = burnsideI16h_eps S (burnsideI16h_Tg S g (burnsideI16h_H S (burnsideI16h_L S h w)))
  rw [burnsideI16h_H_L]

theorem burnsideI16h_L_one : burnsideI16h_L S (1 : SL(2, F)) = 1 := by
  refine LinearMap.ext fun w => ?_
  change burnsideI16h_eps S (burnsideI16h_Tg S 1 (burnsideI16h_H S w)) = w
  rw [burnsideI16h_Tg_one, burnsideI16h_eps_H]

@[expose] noncomputable def burnsideI16h_Lhom : SL(2, F) →* Module.End K (burnsideI16h_OI → K) where
  toFun := burnsideI16h_L S
  map_one' := burnsideI16h_L_one S
  map_mul' := burnsideI16h_L_mul S

@[expose] noncomputable def burnsideI16h_Θ :
    SL(2, F) →* ((burnsideI16h_OI → K) ≃ₗ[K] (burnsideI16h_OI → K)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (burnsideI16h_OI → K)).toMonoidHom.comp
    (MonoidHom.toHomUnits (burnsideI16h_Lhom S))

theorem burnsideI16h_Θ_apply (g : SL(2, F)) (w : burnsideI16h_OI → K) :
    burnsideI16h_Θ S g w = burnsideI16h_L S g w := rfl

theorem burnsideI16h_Q_apply (w : burnsideI16h_OI → K) :
    CFSG.LieType.Universal.Spin.quadMinus 2 K S.b S.c w =
      w (Sum.inl 0) * w (Sum.inr (Sum.inl 0)) + w (Sum.inr (Sum.inr 0)) ^ 2 +
        S.b * w (Sum.inr (Sum.inr 0)) * w (Sum.inr (Sum.inr 1)) +
          S.c * w (Sum.inr (Sum.inr 1)) ^ 2 := by
  rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
  congr 3
  exact Finset.sum_eq_single_of_mem 0 (Finset.mem_univ _)
    (fun b _ hb => absurd (burnsideI16h_fin1 b) hb)

theorem burnsideI16h_det_H (w : burnsideI16h_OI → K) :
    (burnsideI16h_H S w).det =
      algebraMap K F (CFSG.LieType.Universal.Spin.quadMinus 2 K S.b S.c w) := by
  rw [burnsideI16h_Q_apply, Matrix.det_fin_two]
  simp only [burnsideI16h_H, LinearMap.coe_mk, AddHom.coe_mk, burnsideI16h_hmat, of_apply,
    cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  have hn := burnsideI16h_norm_coord S (w (Sum.inr (Sum.inr 0))) (w (Sum.inr (Sum.inr 1)))
  unfold burnsideI16h_zf
  rw [hn, CharTwo.sub_eq_add]
  simp only [map_add, map_mul, map_pow]
  ring

theorem burnsideI16h_det_frob (g : SL(2, F)) :
    (frobPow S.n (g : Matrix (Fin 2) (Fin 2) F)).det = 1 := by
  rw [JonesParshall.frobPow_eq_map, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]

theorem burnsideI16h_Q_L (g : SL(2, F)) (w : burnsideI16h_OI → K) :
    CFSG.LieType.Universal.Spin.quadMinus 2 K S.b S.c (burnsideI16h_L S g w) =
      CFSG.LieType.Universal.Spin.quadMinus 2 K S.b S.c w := by
  apply (algebraMap K F).injective
  rw [← burnsideI16h_det_H, ← burnsideI16h_det_H, burnsideI16h_H_L, burnsideI16h_Tg_apply,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, burnsideI16h_det_frob,
    Matrix.SpecialLinearGroup.det_coe, one_mul, mul_one]

theorem burnsideI16h_H_x : burnsideI16h_H S (Pi.single (Sum.inl 0) 1) =
    !![(1 : F), 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideI16h_H, burnsideI16h_hmat, burnsideI16h_zf, Pi.single_apply]

theorem burnsideI16h_H_y : burnsideI16h_H S (Pi.single (Sum.inr (Sum.inl 0)) 1) =
    !![(0 : F), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideI16h_H, burnsideI16h_hmat, burnsideI16h_zf, Pi.single_apply]

theorem burnsideI16h_H_u : burnsideI16h_H S (Pi.single (Sum.inr (Sum.inr 0)) 1) =
    !![(0 : F), 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideI16h_H, burnsideI16h_hmat, burnsideI16h_zf, Pi.single_apply]

theorem burnsideI16h_Θ_injective : Function.Injective (burnsideI16h_Θ S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg' : burnsideI16h_Θ S g = 1 := hg
  have key : ∀ w, (g : Matrix (Fin 2) (Fin 2) F) * burnsideI16h_H S w *
      (frobPow S.n (g : Matrix (Fin 2) (Fin 2) F))ᵀ = burnsideI16h_H S w := by
    intro w
    have h1 : burnsideI16h_L S g w = w := by
      have := congrArg (fun f => f w) hg'
      exact this
    have h2 := burnsideI16h_H_L S g w
    rw [h1, burnsideI16h_Tg_apply] at h2
    exact h2.symm
  have kx := key (Pi.single (Sum.inl 0) 1)
  have ky := key (Pi.single (Sum.inr (Sum.inl 0)) 1)
  have ku := key (Pi.single (Sum.inr (Sum.inr 0)) 1)
  rw [burnsideI16h_H_x] at kx
  rw [burnsideI16h_H_y] at ky
  rw [burnsideI16h_H_u] at ku
  have hinj : Function.Injective (sig (F := F) S.n) := RingHom.injective (sig (F := F) S.n)
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hdet
  have x00 := congrFun (congrFun kx 0) 0
  have x01 := congrFun (congrFun kx 0) 1
  have y00 := congrFun (congrFun ky 0) 0
  have y11 := congrFun (congrFun ky 1) 1
  have u01 := congrFun (congrFun ku 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, JonesParshall.frobPow_eq_map] at x00 x01 y00 y11 u01
  have h2c : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hp0 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul] at x00
    exact zero_ne_one x00
  have hs : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := x01.resolve_left hp0
  rw [y00, hs] at u01 hdet
  simp only [zero_mul, zero_add, mul_zero, sub_zero] at u01 hdet
  have hσt : sig S.n ((g : Matrix (Fin 2) (Fin 2) F) 1 1) = (g : Matrix (Fin 2) (Fin 2) F) 1 1 :=
    mul_left_cancel₀ hp0 (u01.trans hdet.symm)
  rw [hσt] at y11
  have ht : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    have h2 : ((g : Matrix (Fin 2) (Fin 2) F) 1 1 + 1) ^ 2 = 0 := by
      linear_combination y11 + ((g : Matrix (Fin 2) (Fin 2) F) 1 1 + 1) * h2c
    exact CharTwo.add_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h2)
  have hp : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    rw [ht, mul_one] at hdet
    exact hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hp, ht, y00, hs]

theorem burnsideI16h_comm_le_of_card {G : Type} [Group G] (O R : Subgroup G) [Finite O]
    (hRO : R ≤ O) (hcard : Nat.card O = 2 * Nat.card R) : ⁅O, O⁆ ≤ R := by
  classical
  set N : Subgroup O := R.subgroupOf O with hN
  have hNcard : Nat.card N = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRO).toEquiv
  have hidx : N.index = 2 := by
    have h := Subgroup.card_mul_index N
    rw [hNcard, hcard] at h
    have hfin : Finite R :=
      Finite.of_injective (Subgroup.inclusion hRO) (Subgroup.inclusion_injective hRO)
    have hpos : 0 < Nat.card R := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hpos (by rw [h]; ring))
  haveI : N.Normal := Subgroup.normal_of_index_eq_two hidx
  have hQcard : Nat.card (O ⧸ N) = 2 := by rw [← Subgroup.index_eq_card, hidx]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic (O ⧸ N) := isCyclic_of_prime_card hQcard
  letI : CommGroup (O ⧸ N) := IsCyclic.commGroup
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have : ((⟨x, hx⟩ : O) * ⟨y, hy⟩ * (⟨x, hx⟩ : O)⁻¹ * (⟨y, hy⟩ : O)⁻¹) ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_comm (QuotientGroup.mk (⟨x, hx⟩ : O) : O ⧸ N) (QuotientGroup.mk (⟨y, hy⟩ : O))]
    group
  rw [commutatorElement_def]
  exact this

theorem burnsideI16h_omega_ne (k : K) : algebraMap K F k ≠ S.ω := by
  intro h
  apply S.hirr k
  apply (algebraMap K F).injective
  rw [map_zero, map_add, map_add, map_mul, map_pow, h]
  exact S.hω

include S in
theorem burnsideI16h_perfect : commutator SL(2, F) = ⊤ := by
  have h2c : (2 : F) = 0 := CharP.cast_eq_zero F 2
  refine Matrix.SL2.commutator_eq_top (a := S.ω) ?_ ?_
  · intro h
    exact burnsideI16h_omega_ne S 0 (by rw [map_zero, h])
  · intro h
    have h' : (S.ω + 1) ^ 2 = 0 := by linear_combination h + (S.ω + 1) * h2c
    have h'' : S.ω = 1 := CharTwo.add_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h')
    exact burnsideI16h_omega_ne S 1 (by rw [map_one, h''])

noncomputable abbrev burnsideI16h_O : Subgroup ((burnsideI16h_OI → K) ≃ₗ[K] (burnsideI16h_OI → K)) :=
  TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadMinus 2 K S.b S.c)

theorem burnsideI16h_finite_linEquiv : Finite ((burnsideI16h_OI → K) ≃ₗ[K] (burnsideI16h_OI → K)) :=
  Finite.of_injective (fun g : (burnsideI16h_OI → K) ≃ₗ[K] (burnsideI16h_OI → K) =>
    (g : (burnsideI16h_OI → K) → (burnsideI16h_OI → K))) DFunLike.coe_injective

theorem burnsideI16h_range_le : (burnsideI16h_Θ S).range ≤ burnsideI16h_O S := by
  rintro _ ⟨g, rfl⟩
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w => burnsideI16h_Q_L S g w

theorem burnsideI16h_card_O :
    Nat.card (burnsideI16h_O S) = 2 * Nat.card SL(2, F) := by
  haveI : Finite K := Finite.of_fintype K
  haveI : Finite F := Finite.of_fintype F
  have hO : (Nat.card (burnsideI16h_O S) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (1 * (1 + 1)) * ((Nat.card K : ℤ) ^ (1 + 1) + 1) *
        ∏ i ∈ Finset.Icc 1 1, (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
    CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus (K := K) S.hirr 1
  have hSL : Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← CFSG.Open.StatedAPI.card_statedSL, CFSG.Open.StatedAPI.card_statedSL_two]
  have hF : Nat.card F = Nat.card K ^ 2 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, burnsideI16h_hF S, S.hK, ← pow_mul,
      mul_comm]
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have h1 : 1 ≤ (Nat.card K ^ 2) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  rw [hSL, hF]
  zify [h1]
  rw [hO]
  simp only [Finset.Icc_self, Finset.prod_singleton]
  push_cast
  ring

end Hermitian

section Converse

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank Matrix

theorem burnsideI16h_bof_of_intertwiner {Γ W : Type*} [Group Γ] [AddCommGroup W]
    [Module (ZMod 2) W] {F : Type} [Field F] [CharP F 2] {a : ℕ}
    (hσ : ∀ x : F, sig a (sig a x) = x) {ρ : Representation (ZMod 2) Γ W}
    (θ : Γ ≃* SL(2, F)) (β : W ≃+ ↥(hermA a F))
    (h : ∀ γ w, β (ρ γ w) = hermAct a hσ (θ γ) (β w)) :
    Explicit.BinaryOrthogonalFour ρ F a := by
  let e := specialLinearGroupEquivStatedSL 2 F
  let D := FFModel.twistTensor a (StatedSL 2 F)
  have hk : D.ker = ⊥ := rfl
  let βs : W ≃+ Additive D.Sec :=
    β.trans ((hermEquiv a F).symm.trans (secEquivSub D hk).toAdditive.symm)
  refine ⟨θ.trans e, βs, bot_le, ?_, ?_, ?_⟩
  · intro g m hm
    exact twist_mem a hσ (X := Multiplicative.toAdd m) hm _
  · intro g m hm
    have hm1 : m = 1 := hm
    subst hm1
    refine Subgroup.mem_bot.2 ?_
    show twistAct a (StatedSL 2 F) g 1 = 1
    simp [twistAct]
  · intro γ w m hm hw
    obtain ⟨m0, hm0⟩ := m
    have hsymm : ∀ x : ↥D.sec, (secEquivSub D hk).toAdditive.symm (Additive.ofMul x) =
        Additive.ofMul (QuotientGroup.mk x : D.Sec) := fun x =>
      congrArg Additive.ofMul ((secEquivSub D hk).symm_apply_eq.2 (secEquivSub_mk D hk x).symm)
    let mm : ↥(hermSub a (Fin 2) F) := ⟨m0, hm0⟩
    have h1 : (hermEquiv a F).symm (β w) = Additive.ofMul mm := by
      apply (secEquivSub D hk).toAdditive.symm.injective
      exact (hsymm ⟨m0, hm0⟩).trans hw.symm |>.symm
    have h2 : β w = hermEquiv a F (Additive.ofMul mm) := by
      apply (hermEquiv a F).symm.injective
      rw [AddEquiv.symm_apply_apply]
      exact h1
    have h3 : (hermEquiv a F).symm (β (ρ γ w)) =
        Additive.ofMul (⟨D.act ((θ.trans e) γ) m0, hm⟩ : ↥(hermSub a (Fin 2) F)) := by
      apply (hermEquiv a F).injective
      rw [AddEquiv.apply_symm_apply, h]
      apply Subtype.ext
      rw [hermAct_coe, h2]
      rfl
    change (secEquivSub D hk).toAdditive.symm ((hermEquiv a F).symm (β (ρ γ w))) = _
    rw [h3]
    exact hsymm ⟨D.act ((θ.trans e) γ) m0, hm⟩

end Converse

section Final

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix CFSG.ClassicalGroups.Orthogonal

variable {K F : Type} [Field K] [Fintype K] [CharP K 2] [Field F] [Fintype F] [Algebra K F]
  [CharP F 2] (S : burnsideI16h_Setup K F)

theorem burnsideI16h_range_eq :
    (burnsideI16h_Θ S).range = ⁅burnsideI16h_O S, burnsideI16h_O S⁆ := by
  haveI := burnsideI16h_finite_linEquiv (K := K)
  have hinj := burnsideI16h_Θ_injective S
  apply le_antisymm
  · have h1 : (burnsideI16h_Θ S).range =
        Subgroup.map (burnsideI16h_Θ S) ⁅(⊤ : Subgroup SL(2, F)), ⊤⁆ := by
      rw [← commutator_def, burnsideI16h_perfect S, ← MonoidHom.range_eq_map]
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map] at h1
    calc (burnsideI16h_Θ S).range
        = ⁅(burnsideI16h_Θ S).range, (burnsideI16h_Θ S).range⁆ := h1
      _ ≤ _ := Subgroup.commutator_mono (burnsideI16h_range_le S) (burnsideI16h_range_le S)
  · apply burnsideI16h_comm_le_of_card _ _ (burnsideI16h_range_le S)
    rw [burnsideI16h_card_O, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]

@[expose] noncomputable def burnsideI16h_ΘEquiv :
    SL(2, F) ≃* ↥⁅burnsideI16h_O S, burnsideI16h_O S⁆ :=
  (MonoidHom.ofInjective (burnsideI16h_Θ_injective S)).trans
    (MulEquiv.subgroupCongr (burnsideI16h_range_eq S))

@[expose] noncomputable def burnsideI16h_gammaEquiv :
    StatedOmega (StatedQuadMinus 2 K S.b S.c) ≃* ↥⁅burnsideI16h_O S, burnsideI16h_O S⁆ :=
  ((toLinEquiv burnsideI16h_OI K).subgroupMap (StatedOmega (StatedQuadMinus 2 K S.b S.c))).trans
    (MulEquiv.subgroupCongr (by
      rw [statedOmega_eq_comap (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K S.b S.c)]
      exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv burnsideI16h_OI K).surjective _))

@[expose] noncomputable def burnsideI16h_β : (burnsideI16h_OI → K) ≃+ ↥(hermA S.n F) where
  toFun w := ⟨burnsideI16h_H S w, burnsideI16h_H_mem S w⟩
  invFun X := burnsideI16h_eps S (X : Matrix (Fin 2) (Fin 2) F)
  left_inv w := burnsideI16h_eps_H S w
  right_inv X := Subtype.ext (burnsideI16h_H_eps S X.2)
  map_add' w w' := Subtype.ext (map_add (burnsideI16h_H S) w w')

theorem burnsideI16h_β_Θ (g : SL(2, F)) (w : burnsideI16h_OI → K) :
    burnsideI16h_β S (burnsideI16h_Θ S g w) =
      hermAct S.n (burnsideI16h_hσ S) g (burnsideI16h_β S w) := by
  apply Subtype.ext
  rw [hermAct_coe]
  change burnsideI16h_H S (burnsideI16h_L S g w) = _
  rw [burnsideI16h_H_L, burnsideI16h_Tg_apply]
  rfl

@[expose] noncomputable def burnsideI16h_θ :
    StatedOmega (StatedQuadMinus 2 K S.b S.c) ≃* SL(2, F) :=
  (burnsideI16h_gammaEquiv S).trans (burnsideI16h_ΘEquiv S).symm

theorem burnsideI16h_bof [Algebra (ZMod 2) K] :
    CFSG.Quasithin.Explicit.BinaryOrthogonalFour (orthMinusRep K S.b S.c) F S.n := by
  refine burnsideI16h_bof_of_intertwiner (burnsideI16h_hσ S) (burnsideI16h_θ S)
    (burnsideI16h_β S) fun γ w => ?_
  have h1 : burnsideI16h_ΘEquiv S (burnsideI16h_θ S γ) = burnsideI16h_gammaEquiv S γ :=
    (burnsideI16h_ΘEquiv S).apply_symm_apply _
  have h2 : burnsideI16h_Θ S (burnsideI16h_θ S γ) = toLinEquiv burnsideI16h_OI K γ.1 :=
    congrArg Subtype.val h1
  rw [← burnsideI16h_β_Θ]
  congr 1
  rw [burnsideI16h_Θ_apply] at *
  have := congrArg (fun f => f w) h2
  exact this.symm

end Final

section JPHelpers3

theorem burnsideI16h_p3a :
    ∀ n : ℕ, 1 ≤ n → ∀ b c : GaloisField 2 n, (∀ s : GaloisField 2 n, s ^ 2 + b * s + c ≠ 0) →
      h1Dim (orthMinusRep (GaloisField 2 n) b c) = 0 := by
  intro n hn b c hirr
  obtain ⟨-, j2, -⟩ := CFSG.Quasithin.JonesParshall.natural_binary_first_cohomology_sector.{0, 0}
  letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hK : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 n (by omega)
  obtain ⟨F, _, _, ω, hrank, hω⟩ := burnsideI16h_exists_quad_ext hirr
  haveI : Module.Finite (GaloisField 2 n) F := Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
  haveI : Finite F := Module.finite_of_finite (GaloisField 2 n)
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_injective_algebraMap (algebraMap (GaloisField 2 n) F).injective 2
  let S : burnsideI16h_Setup (GaloisField 2 n) F := ⟨n, b, c, hn, hK, ω, hω, hirr, hrank⟩
  have hbof := burnsideI16h_bof S
  rw [burnsideI16h_h1Dim_eq]
  exact j2 (burnsideI16h_hF S) hn hbof

end JPHelpers3

open CFSG.Quasithin.SteinbergCB.I16 in
theorem burnsideI16h_p3b :
    ∀ b c : ZMod 2, (∀ s : ZMod 2, s ^ 2 + b * s + c ≠ 0) →
      (∃ (φ : StatedOmega (StatedQuadMinus 2 (ZMod 2) b c) ≃* alternatingGroup (Fin 5))
        (e : (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
          (evenWeight 5 ⧸ constInEven 5)),
        ∀ (g : StatedOmega (StatedQuadMinus 2 (ZMod 2) b c))
          (v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 2),
          e (orthMinusRep (ZMod 2) b c g v) = altNaturalRep 5 (φ g) (e v)) ∧
      Module.Projective (MonoidAlgebra (ZMod 2) (StatedOmega (StatedQuadMinus 2 (ZMod 2) b c)))
        (orthMinusRep (ZMod 2) b c).asModule := by
  intro b c hirr
  obtain ⟨F, _, _, ω, hrank, hω⟩ := burnsideI16h_exists_quad_ext hirr
  haveI : Module.Finite (ZMod 2) F := Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
  haveI : Finite F := Module.finite_of_finite (ZMod 2)
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let S : burnsideI16h_Setup (ZMod 2) F :=
    ⟨1, b, c, le_refl 1, by rw [ZMod.card, pow_one], ω, hω, hirr, hrank⟩
  have hbof := burnsideI16h_bof S
  have hAlt := Orth4.alternatingNatural_of_binaryOrthogonalFour (burnsideI16h_hF S) hbof
  refine ⟨?_, projective_alternatingNatural_five hAlt⟩
  obtain ⟨θ, e, he⟩ := coords5.exists_intertwiner hAlt
  let E : (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 2) ≃+ (evenWeight 5 ⧸ constInEven 5) :=
    e.trans (burnsideI16h_altE coords5).symm
  refine ⟨θ, LinearEquiv.ofBijective (E.toAddMonoidHom.toZModLinearMap 2)
    ⟨E.injective, E.surjective⟩, fun g v => ?_⟩
  change E (orthMinusRep (ZMod 2) b c g v) = altNaturalRep 5 (θ g) (E v)
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, he]
  apply (burnsideI16h_altE coords5).injective
  rw [AddEquiv.apply_symm_apply, burnsideI16h_altE_intertwine, AddEquiv.apply_symm_apply]

section

theorem as_I_1_6 : I_1_6 := by
  exact ⟨burnsideI16h_p1, burnsideI16h_p2, ⟨burnsideI16h_p3a, burnsideI16h_p3b⟩, burnsideI16h_p4,
    burnsideI16h_p5, burnsideI16h_p6, burnsideI16h_p7, burnsideI16h_p8, burnsideI16h_p9⟩

end

end CFSG.ASVolI

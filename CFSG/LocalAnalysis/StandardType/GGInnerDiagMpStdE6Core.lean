module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectExcE6
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace MpStdE6

section Core

variable {τ : Tag} {F : Type} [Field F]

theorem ggPsiInnerDiag_of_conj_diag {S : Type*} [Group S] (Δ : UniversalRootDatum S)
    {C : Subgroup (ModGL τ F)} {π : S →* C} (hπker : π.ker ≤ Subgroup.center S)
    (hodd : Odd (Nat.card π.ker))
    (hinv : ∀ δ ∈ Δ.roots, ∀ z ∈ Δ.rootGroup δ, z * z = 1) (a : Fin τ.rank → Fˣ)
    (hdiag : ∀ δ ∈ Δ.roots, ∃ h ∈ ggTorus Δ, ∀ z ∈ Δ.rootGroup δ,
      ((π (h * z * h⁻¹) : C) : ModGL τ F) =
        rootDiagUnit τ a * ((π z : C) : ModGL τ F) * (rootDiagUnit τ a)⁻¹)
    {G : Type*} [Group G] {ψ : S →* G} {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (a₀ : S)
    (hact : ∀ y y' : S, ψ y' = c⁻¹ * ψ y * c →
      ((π y' : C) : ModGL τ F) =
        ((π a₀ : C) : ModGL τ F) * rootDiagUnit τ a *
          ((π y : C) : ModGL τ F) * (rootDiagUnit τ a)⁻¹ *
            ((π a₀ : C) : ModGL τ F)⁻¹) :
    GGPsiInnerDiag Δ ψ c := by
  refine ⟨ψ a₀, ⟨a₀, rfl⟩, fun δ hδ => ?_⟩
  obtain ⟨h, hh, hhz⟩ := hdiag δ hδ
  refine ⟨h, hh, fun z hz => ?_⟩
  obtain ⟨z₁, hz₁⟩ := RootDetect.exists_conj_preimage hc z
  have hπz₁ : π z₁ = π (a₀ * (h * z * h⁻¹) * a₀⁻¹) := by
    refine Subtype.ext ?_
    rw [hact z z₁ hz₁, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hhz z hz]
    group
  obtain ⟨ζ, hζ⟩ : ∃ ζ : S, ζ = (a₀ * (h * z * h⁻¹) * a₀⁻¹)⁻¹ * z₁ := ⟨_, rfl⟩
  have hζker : ζ ∈ π.ker := by
    rw [MonoidHom.mem_ker, hζ, map_mul, map_inv, hπz₁, inv_mul_cancel]
  have hζc : ζ ∈ Subgroup.center S := hπker hζker
  have heq : z₁ = a₀ * (h * z * h⁻¹) * a₀⁻¹ * ζ := by rw [hζ]; group
  have hhzh : h * z * h⁻¹ ∈ Δ.rootGroup δ := by
    have hhn : h ∈ Subgroup.normalizer (Δ.rootGroup δ : Set S) := by
      simp only [ggTorus, Subgroup.mem_iInf] at hh
      exact hh δ hδ
    exact (Subgroup.mem_normalizer_iff.mp hhn z).mp hz
  have hw2 : (h * z * h⁻¹) * (h * z * h⁻¹) = 1 := hinv δ hδ _ hhzh
  have hz2 : z * z = 1 := hinv δ hδ z hz
  have hψz₁ : ψ z₁ * ψ z₁ = 1 := by
    calc ψ z₁ * ψ z₁ = c⁻¹ * (ψ z * ψ z) * c := by rw [hz₁]; group
      _ = 1 := by rw [← map_mul, hz2, map_one]; group
  have hzz : z₁ * z₁ = ζ * ζ := by
    have hcomm := Subgroup.mem_center_iff.mp hζc (a₀ * (h * z * h⁻¹) * a₀⁻¹)
    calc z₁ * z₁ = a₀ * (h * z * h⁻¹) * a₀⁻¹ * ζ * (a₀ * (h * z * h⁻¹) * a₀⁻¹ * ζ) := by
          rw [heq]
      _ = a₀ * (h * z * h⁻¹) * a₀⁻¹ * (ζ * (a₀ * (h * z * h⁻¹) * a₀⁻¹)) * ζ := by group
      _ = a₀ * (h * z * h⁻¹) * a₀⁻¹ * (a₀ * (h * z * h⁻¹) * a₀⁻¹ * ζ) * ζ := by rw [hcomm]
      _ = a₀ * ((h * z * h⁻¹) * (h * z * h⁻¹)) * a₀⁻¹ * (ζ * ζ) := by group
      _ = ζ * ζ := by rw [hw2]; group
  have hζ2 : ψ ζ * ψ ζ = 1 := by
    rw [← map_mul, ← hzz, map_mul, hψz₁]
  have hζodd : Odd (orderOf ζ) := by
    have h1 : orderOf (⟨ζ, hζker⟩ : π.ker) ∣ Nat.card π.ker := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hodd.of_dvd_nat h1
  have hψζ : ψ ζ = 1 := by
    obtain ⟨m, hm⟩ := hζodd
    have h1 : ψ ζ ^ orderOf ζ = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [hm, pow_succ, pow_mul, sq, hζ2, one_pow, one_mul] at h1
    exact h1
  have hcomm' := Subgroup.mem_center_iff.mp hζc a₀⁻¹
  calc (c * ψ a₀)⁻¹ * ψ z * (c * ψ a₀) = (ψ a₀)⁻¹ * (c⁻¹ * ψ z * c) * ψ a₀ := by group
    _ = (ψ a₀)⁻¹ * ψ z₁ * ψ a₀ := by rw [hz₁]
    _ = ψ (a₀⁻¹ * z₁ * a₀) := by rw [map_mul, map_mul, map_inv]
    _ = ψ ((h * z * h⁻¹) * (a₀⁻¹ * ζ * a₀)) := by rw [heq]; group
    _ = ψ ((h * z * h⁻¹) * ζ) := by rw [hcomm', inv_mul_cancel_right]
    _ = ψ (h * z * h⁻¹) := by rw [map_mul, hψζ, mul_one]

end Core

section BaseChange

variable
  {F K : Type} [Field F] [Field K] (σ : F ≃+* K) (t : Tag)

@[expose] noncomputable def adjEquiv : adjointGroup t F ≃* adjointGroup t K where
  toFun g := ⟨baseChangeGL σ.toRingHom g, baseChangeGL_mem_adjointGroup _ g.2⟩
  invFun g := ⟨baseChangeGL σ.symm.toRingHom g, baseChangeGL_mem_adjointGroup _ g.2⟩
  left_inv g := Subtype.ext (by
    show baseChangeGL σ.symm.toRingHom (baseChangeGL σ.toRingHom (g : ModGL t F)) = g
    rw [baseChangeGL_baseChangeGL, RingEquiv.symm_toRingHom_comp_toRingHom, baseChangeGL_id])
  right_inv g := Subtype.ext (by
    show baseChangeGL σ.toRingHom (baseChangeGL σ.symm.toRingHom (g : ModGL t K)) = g
    rw [baseChangeGL_baseChangeGL, RingEquiv.toRingHom_comp_symm_toRingHom, baseChangeGL_id])
  map_mul' g h := Subtype.ext (map_mul (baseChangeGL σ.toRingHom) (g : ModGL t F) h)

theorem coe_adjEquiv (g : adjointGroup t F) :
    ((adjEquiv σ t g : adjointGroup t K) : ModGL t K) = baseChangeGL σ.toRingHom g :=
  rfl

theorem coe_adjEquiv_symm (g : adjointGroup t K) :
    (((adjEquiv σ t).symm g : adjointGroup t F) : ModGL t F) =
      baseChangeGL σ.symm.toRingHom g :=
  rfl

theorem baseChangeGL_conj_rootDiag (a : Fin t.rank → Fˣ) (g : ModGL t F) :
    baseChangeGL σ.toRingHom (rootDiagUnit t a * g * (rootDiagUnit t a)⁻¹) =
      rootDiagUnit t (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) *
        baseChangeGL σ.toRingHom g *
        (rootDiagUnit t (fun i => Units.map σ.toRingHom.toMonoidHom (a i)))⁻¹ := by
  rw [map_mul, map_mul, map_inv, baseChangeGL_rootDiagUnit]

end BaseChange

section Diag

variable {t : Tag} {K : Type}
  [Field K]

theorem conj_rootDiag_mem (a : Fin t.rank → Kˣ) {g : ModGL t K} (hg : g ∈ adjointGroup t K) :
    rootDiagUnit t a * g * (rootDiagUnit t a)⁻¹ ∈ adjointGroup t K :=
  ((Subgroup.mem_normalizer_iff.mp (root_diagonal_conjugation t K a).2.2) g).mp hg

theorem rootDiagUnit_inv (a : Fin t.rank → Kˣ) :
    (rootDiagUnit t a)⁻¹ = rootDiagUnit t a⁻¹ :=
  rfl

theorem rootDiagUnit_mul (a b : Fin t.rank → Kˣ) :
    rootDiagUnit t a * rootDiagUnit t b = rootDiagUnit t (a * b) :=
  Units.ext (rootDiag_mul_rootDiag a b)

theorem rootDiagUnit_one : rootDiagUnit t (1 : Fin t.rank → Kˣ) = 1 :=
  Units.ext rootDiag_one

theorem rootDiagUnit_mem_normalizer (a : Fin t.rank → Kˣ) :
    rootDiagUnit t a ∈ Subgroup.normalizer (adjointGroup t K : Set (ModGL t K)) :=
  (root_diagonal_conjugation t K a).2.2

variable (t K) in
@[expose] def diagAdj :
    Subgroup (Subgroup.normalizer (adjointGroup t K : Set (ModGL t K))) where
  carrier := {x | ∃ g ∈ adjointGroup t K, ∃ a : Fin t.rank → Kˣ,
    (x : ModGL t K) = g * rootDiagUnit t a}
  mul_mem' := by
    rintro x y ⟨g, hg, a, hx⟩ ⟨g', hg', b, hy⟩
    refine ⟨g * (rootDiagUnit t a * g' * (rootDiagUnit t a)⁻¹),
      mul_mem hg (conj_rootDiag_mem a hg'), a * b, ?_⟩
    rw [Subgroup.coe_mul, hx, hy, ← rootDiagUnit_mul]
    group
  one_mem' := ⟨1, one_mem _, 1, by rw [rootDiagUnit_one, mul_one]; rfl⟩
  inv_mem' := by
    rintro x ⟨g, hg, a, hx⟩
    refine ⟨(rootDiagUnit t a)⁻¹ * g⁻¹ * rootDiagUnit t a, ?_, a⁻¹, ?_⟩
    · have h := conj_rootDiag_mem a⁻¹ (inv_mem hg)
      rwa [← rootDiagUnit_inv, inv_inv] at h
    · rw [Subgroup.coe_inv, hx, ← rootDiagUnit_inv]
      group

end Diag

section Transfer

variable {K : Type} [Field K]

theorem transfer_conj_rootDiag (t : Tag)
    (T : adjointGroup t K ≃* LargeEvenChevGroup t.cartan K)
    (hTx : ∀ (i : Fin t.rank) (c : K),
      ((T (xElement i c) : LargeEvenChevGL t.cartan K) :
        Module.End K (LargeEvenChevModule t.cartan K)) = LargeEvenXOp t.cartan K i c)
    (hTy : ∀ (i : Fin t.rank) (c : K),
      ((T (yElement i c) : LargeEvenChevGL t.cartan K) :
        Module.End K (LargeEvenChevModule t.cartan K)) = LargeEvenYOp t.cartan K i c)
    (a : Fin t.rank → Kˣ) (x : adjointGroup t K) :
    ((T ⟨rootDiagUnit t a * x * (rootDiagUnit t a)⁻¹, conj_rootDiag_mem a x.2⟩ :
        LargeEvenChevGroup t.cartan K) : LargeEvenChevGL t.cartan K) =
      TableB.diagHom t.cartan K a * T x * (TableB.diagHom t.cartan K a)⁻¹ := by
  let cd : adjointGroup t K →* adjointGroup t K :=
    { toFun := fun x => ⟨rootDiagUnit t a * x * (rootDiagUnit t a)⁻¹, conj_rootDiag_mem a x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        show rootDiagUnit t a * ((x : ModGL t K) * y) * (rootDiagUnit t a)⁻¹ =
          rootDiagUnit t a * x * (rootDiagUnit t a)⁻¹ * (rootDiagUnit t a * y *
            (rootDiagUnit t a)⁻¹)
        group) }
  let f₁ : adjointGroup t K →* LargeEvenChevGL t.cartan K :=
    (LargeEvenChevGroup t.cartan K).subtype.comp (T.toMonoidHom.comp cd)
  let f₂ : adjointGroup t K →* LargeEvenChevGL t.cartan K :=
    (MulAut.conj (TableB.diagHom t.cartan K a)).toMonoidHom.comp
      ((LargeEvenChevGroup t.cartan K).subtype.comp T.toMonoidHom)
  have hgen : ∀ (i : Fin t.rank) (c : K),
      f₁ (xElement i c) = f₂ (xElement i c) ∧ f₁ (yElement i c) = f₂ (yElement i c) := by
    intro i c
    obtain ⟨hx, hy, -⟩ := root_diagonal_conjugation t K a
    have ex : cd (xElement i c) = xElement i ((a i : K) * c) := Subtype.ext (hx i c)
    have ey : cd (yElement i c) = yElement i (((a i)⁻¹ : Kˣ) * c) := Subtype.ext (hy i c)
    refine ⟨Units.ext ?_, Units.ext ?_⟩
    · show ((T (cd (xElement i c)) : LargeEvenChevGL t.cartan K) :
          Module.End K (LargeEvenChevModule t.cartan K)) =
        ((TableB.diagHom t.cartan K a * T (xElement i c) * (TableB.diagHom t.cartan K a)⁻¹ :
          LargeEvenChevGL t.cartan K) : Module.End K (LargeEvenChevModule t.cartan K))
      rw [ex, hTx, InnerDiagE6.diagHom_conj_xOp t a (hTx i c)]
    · show ((T (cd (yElement i c)) : LargeEvenChevGL t.cartan K) :
          Module.End K (LargeEvenChevModule t.cartan K)) =
        ((TableB.diagHom t.cartan K a * T (yElement i c) * (TableB.diagHom t.cartan K a)⁻¹ :
          LargeEvenChevGL t.cartan K) : Module.End K (LargeEvenChevModule t.cartan K))
      rw [ey, hTy, InnerDiagE6.diagHom_conj_yOp t a (hTy i c)]
  have hf : f₁ = f₂ := by
    refine MonoidHom.eq_of_eqOn_dense (Subgroup.closure_closure_coe_preimage
      (k := {g : ModGL t K | ∃ (i : Fin t.rank) (c : K),
        (g : Module.End K (RootModule t K)) = xOp t K i c ∨
          (g : Module.End K (RootModule t K)) = yOp t K i c})) ?_
    rintro x ⟨i, c, hxc | hxc⟩
    · have e : x = xElement i c := Subtype.ext (Units.ext (hxc.trans (coe_xUnit i c).symm))
      rw [e]
      exact (hgen i c).1
    · have e : x = yElement i c := Subtype.ext (Units.ext (hxc.trans (coe_yUnit i c).symm))
      rw [e]
      exact (hgen i c).2
  exact DFunLike.congr_fun hf x

end Transfer

end MpStdE6

end CFSG.StandardType

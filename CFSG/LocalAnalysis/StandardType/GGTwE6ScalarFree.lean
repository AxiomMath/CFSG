module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeWeylDiagGen
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Conj

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem scalarFree_transport
    {τ : Tag} {p : ℕ} [NeZero p] {L : Type} [Field L] {H : Type} [Group H]
    (j : H →* ModGL τ L) (hj : Function.Injective j)
    (ι : Multiplicative (Fin τ.rank → ZMod p) →* H)
    (ζ : Lˣ) (hζ : ζ ^ p = 1) (g0 : ModGL τ L) (hg0 : g0 ∈ adjointGroup τ L)
    (hbase : ∀ s : Fin τ.rank → ZMod p,
      j (ι (Multiplicative.ofAdd s)) = g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹)
    (β : MulAut H) (x : ModGL τ L) (hx : x ∈ adjointGroup τ L)
    (hact : ∀ h : H, j (β h) = x * j h * x⁻¹)
    (hstab : ∀ z ∈ ι.range, β z ∈ ι.range) :
    ∃ w : WeylGroup τ, ∀ s : Fin τ.rank → ZMod p,
      β (ι (Multiplicative.ofAdd s)) =
        ι (Multiplicative.ofAdd (TableBExc.torusAct τ p w s)) := by
  classical
  set d : (Fin τ.rank → ZMod p) → ModGL τ L := fun s => ExcFrames.frameDiag ζ hζ s with hd
  set V : Set (ModGL τ L) := Set.range d with hV
  set b : ModGL τ L := g0⁻¹ * x * g0 with hb
  have hbC : b ∈ adjointGroup τ L :=
    mul_mem (mul_mem (inv_mem hg0) hx) hg0
  have hbV : ∀ y ∈ V, b * y * b⁻¹ ∈ V := by
    rintro y ⟨s, rfl⟩
    obtain ⟨z, hz⟩ := hstab (ι (Multiplicative.ofAdd s)) ⟨_, rfl⟩
    set s' : Fin τ.rank → ZMod p := Multiplicative.toAdd z with hs'
    have hz' : β (ι (Multiplicative.ofAdd s)) = ι (Multiplicative.ofAdd s') := by
      rw [hs', ← hz]
      rfl
    have h1 : j (ι (Multiplicative.ofAdd s')) = x * j (ι (Multiplicative.ofAdd s)) * x⁻¹ := by
      rw [← hz', hact]
    have h2 : g0 * d s' * g0⁻¹ = x * (g0 * d s * g0⁻¹) * x⁻¹ := by
      rw [← hbase s', ← hbase s]
      exact h1
    have h3 : g0 * (b * d s * b⁻¹) * g0⁻¹ = g0 * d s' * g0⁻¹ := by
      rw [show g0 * (b * d s * b⁻¹) * g0⁻¹ =
          x * (g0 * d s * g0⁻¹) * x⁻¹ by
        rw [hb]
        group]
      exact h2.symm
    have h4 : b * d s * b⁻¹ = d s' := by
      have := congrArg (fun t => g0⁻¹ * t * g0) h3
      simpa [mul_assoc] using this
    exact ⟨s', h4.symm⟩
  have hVD : ∀ y ∈ V, ∃ a : Fin τ.rank → Lˣ, y = rootDiagUnit τ a := by
    rintro y ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  obtain ⟨w, hw⟩ :=
    NoOffE6Three.exists_conj_eq_canonicalRep_of_mem_normalizer_rootDiag
      (τ := τ) (k := L) hVD hbC hbV
  refine ⟨w, fun s => ?_⟩
  obtain ⟨z, hz⟩ := hstab (ι (Multiplicative.ofAdd s)) ⟨_, rfl⟩
  set s' : Fin τ.rank → ZMod p := Multiplicative.toAdd z with hs'
  have hz' : β (ι (Multiplicative.ofAdd s)) = ι (Multiplicative.ofAdd s') := by
    rw [hs', ← hz]
    rfl
  have hj' : j (ι (Multiplicative.ofAdd s')) =
      j (ι (Multiplicative.ofAdd (TableBExc.torusAct τ p w s))) := by
    calc j (ι (Multiplicative.ofAdd s'))
        = x * j (ι (Multiplicative.ofAdd s)) * x⁻¹ := by rw [← hz', hact]
      _ = x * (g0 * d s * g0⁻¹) * x⁻¹ := by rw [hbase s]
      _ = g0 * (b * d s * b⁻¹) * g0⁻¹ := by
        rw [hb]
        group
      _ = g0 * (canonicalRep (coxeterSystem τ) L w * d s *
            (canonicalRep (coxeterSystem τ) L w)⁻¹) * g0⁻¹ := by rw [hw (d s) ⟨s, rfl⟩]
      _ = g0 * d (TableBExc.torusAct τ p w s) * g0⁻¹ := by
        rw [hd, ExcFrames.canonicalRep_conj_frameDiag]
      _ = j (ι (Multiplicative.ofAdd (TableBExc.torusAct τ p w s))) := by rw [hbase]
  exact hz'.trans (hj hj')

theorem exists_scalarFree_twConj
    {n p : ℕ} [NeZero p] (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {ζK : Kˣ} {hζ : (Units.map (algebraMap K L).toMonoidHom ζK) ^ p = 1}
    {g₀ : ModGL TwistTag.E6.tag L} (hg₀C : g₀ ∈ adjointGroup TwistTag.E6.tag L)
    (ι₀ : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →*
      ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hbase : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      baseChangeGL (algebraMap K L)
        ((ι₀ (Multiplicative.ofAdd s) : _) : ModGL TwistTag.E6.tag K) =
        g₀ * ExcFrames.frameDiag (τ := TwistTag.E6.tag)
          (Units.map (algebraMap K L).toMonoidHom ζK) hζ s * g₀⁻¹)
    (w : RecipeExcLang.twInndiagGroup K σ)
    (hstab : ∀ b ∈ ι₀.range, RecipeExcLang.twConj K σ w b ∈ ι₀.range) :
    ∃ u : WeylGroup TwistTag.E6.tag, ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      RecipeExcLang.twConj K σ w (ι₀ (Multiplicative.ofAdd s)) =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct TwistTag.E6.tag p u s)) := by
  classical
  let C₀ := ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
  let j : C₀ →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype
  have hj : Function.Injective j :=
    (baseChangeGL_injective (algebraMap K L)).comp
      (Subgroup.subtype_injective (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
  let x : ModGL TwistTag.E6.tag L :=
    baseChangeGL (algebraMap K L) (w : ModGL TwistTag.E6.tag K)
  have hx : x ∈ adjointGroup TwistTag.E6.tag L :=
    (twistedFixedGroup_le_adjointGroup TwistTag.E6 L Fr)
      (RecipeExcLang.baseChangeGL_mem_twistedFixed_of_mem_twInndiag hn hK hσ hFr w.2)
  have hact : ∀ h : C₀, j (RecipeExcLang.twConj K σ w h) = x * j h * x⁻¹ := by
    intro h
    simp only [j, x, MonoidHom.comp_apply]
    have hcoe : (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype
        (RecipeExcLang.twConj K σ w h) =
        (w : ModGL TwistTag.E6.tag K) *
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype h *
          (w : ModGL TwistTag.E6.tag K)⁻¹ :=
      RecipeExcLang.coe_twConj σ w h
    rw [hcoe]
    simp only [map_mul, map_inv]
  obtain ⟨u, hu⟩ :=
    scalarFree_transport (τ := TwistTag.E6.tag) (p := p) (L := L) (H := C₀)
      j hj ι₀ (Units.map (algebraMap K L).toMonoidHom ζK) hζ g₀ hg₀C
      (by
        intro s
        exact hbase s)
      (RecipeExcLang.twConj K σ w) x hx hact hstab
  exact ⟨u, hu⟩

end CFSG.StandardType

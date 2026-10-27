module

public import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistWitness
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelCentE

public noncomputable section

namespace CFSG.StandardType.TwE6ThreeLang

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.StandardType.TwE6Lang CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc
  CFSG.StandardType.TBE6IndTwist CFSG.LocalAnalysis.StandardType.GGTBE6Cover
  CFSG.StandardType.TableBExc.E6Three

variable {K L : Type} [Field K] [Finite K] [CharP K 2] [Group L]
  (θ : K ≃+* K) (hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c)
  (l : K) (hl : θ.toRingHom l = l + 1)
  (φ : fixedGroup K θ.toRingHom →* L)
  (δ : (Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) →* MulAut L)

@[expose] def frameB (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ 3 = 1) :
    Multiplicative (Fin Tag.E6.rank → ZMod 3) →*
      (Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) :=
  (MonoidHom.compLeft (zmodPowHom ζ hζ) _).comp (MulEquiv.funMultiplicative _ _).toMonoidHom

theorem frameB_coe_apply (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ 3 = 1)
    (v : Fin Tag.E6.rank → ZMod 3) (i : Fin Tag.E6.rank) :
    ((frameB θ ζ hζ (Multiplicative.ofAdd v) i :
        CFSG.LieType.Steinberg.normOne θ) : Kˣ) =
      CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) (congrArg Subtype.val hζ) v i :=
  rfl

@[expose] noncomputable def langDiagMat
    (b : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) : ModGL .E6 K :=
  (e6Isogeny K (langG K θ.toRingHom l) : ModGL .E6 K) *
    rootDiagUnit .E6 (fun i => (b i : Kˣ)) *
      (e6Isogeny K (langG K θ.toRingHom l) : ModGL .E6 K)⁻¹

theorem isogeny_fixedDiagonalHom {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f))
    (b : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ)
    (x : fixedGroup K θ.toRingHom) :
    (show ModGL .E6 K from
        ((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq
          (fixedDiagonalHom K (f * 2) (by rw [hK, ← pow_mul]) θ hθ l hl b x) :
          graphFixedRootGroup TwistTag.E6 K θ.toRingHom) : ModGL TwistTag.E6.tag K)) =
      langDiagMat θ l b *
        (show ModGL .E6 K from
          ((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq x :
            graphFixedRootGroup TwistTag.E6 K θ.toRingHom) : ModGL TwistTag.E6.tag K)) *
          (langDiagMat θ l b)⁻¹ := by
  have hcoe : ∀ y : fixedGroup K θ.toRingHom,
      (show ModGL .E6 K from
        ((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq y :
          graphFixedRootGroup TwistTag.E6 K θ.toRingHom) : ModGL TwistTag.E6.tag K)) =
      (e6Isogeny K (y : e6Data_valid.minGroup K) : ModGL .E6 K) := fun _ => rfl
  rw [hcoe, hcoe, fixedDiagonalHom_apply]
  rw [map_mul, map_mul, map_inv, diagonalHom_isogeny]
  simp only [rootDiagAutHom, MonoidHom.coe_mk, OneHom.coe_mk]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_rootDiagAut, langDiagMat]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  group

theorem mem_langTorus_of_commute_hyp {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f))
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ 3 = 1)
    (hζo : orderOf (ζ : Kˣ) = 3)
    {x : fixedGroup K θ.toRingHom}
    (hx : ∀ v ∈ NoOffRest.hypE6,
      langDiagMat θ l (frameB θ ζ hζ (Multiplicative.ofAdd v)) *
        (show ModGL .E6 K from
          ((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq x :
            graphFixedRootGroup TwistTag.E6 K θ.toRingHom) : ModGL TwistTag.E6.tag K)) =
      (show ModGL .E6 K from
        ((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq x :
          graphFixedRootGroup TwistTag.E6 K θ.toRingHom) : ModGL TwistTag.E6.tag K)) *
        langDiagMat θ l (frameB θ ζ hζ (Multiplicative.ofAdd v))) :
    x ∈ (langTorusHom K θ hθ l hl).range := by
  let G : adjointGroup .E6 K := e6Isogeny K (langG K θ.toRingHom l)
  let y : adjointGroup .E6 K := e6Isogeny K (x : e6Data_valid.minGroup K)
  let z : adjointGroup .E6 K := G⁻¹ * y * G
  have hζ' : (ζ : Kˣ) ^ 3 = 1 := congrArg Subtype.val hζ
  have hz : (z : ModGL .E6 K) ∈ torusGroup .E6 K := by
    refine CFSG.StandardType.E6ThreeModel.mem_torusGroup_of_commute_zetaVec (k := K)
      (ζ := (ζ : Kˣ)) hζo hζ' z.2 ?_
    intro v hv
    have hcomm := hx v hv
    have hD : langDiagMat θ l (frameB θ ζ hζ (Multiplicative.ofAdd v)) =
        (G : ModGL .E6 K) *
          rootDiagUnit .E6 (CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' v) *
            (G : ModGL .E6 K)⁻¹ := by
      rw [langDiagMat]
      have hb : (fun i => ((frameB θ ζ hζ (Multiplicative.ofAdd v) i :
          CFSG.LieType.Steinberg.normOne θ) : Kˣ)) =
          CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' v := by
        funext i
        exact frameB_coe_apply θ ζ hζ v i
      rw [hb]
    rw [hD] at hcomm
    change (G : ModGL .E6 K) *
        rootDiagUnit .E6 (CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' v) *
          (G : ModGL .E6 K)⁻¹ * (y : ModGL .E6 K) =
      (y : ModGL .E6 K) *
        ((G : ModGL .E6 K) *
          rootDiagUnit .E6 (CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' v) *
            (G : ModGL .E6 K)⁻¹) at hcomm
    have hzG : (z : ModGL .E6 K) =
        (G : ModGL .E6 K)⁻¹ * (y : ModGL .E6 K) * (G : ModGL .E6 K) := by
      simp only [z, Subgroup.coe_mul, Subgroup.coe_inv]
    have hcomm' : rootDiagUnit .E6 (CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' v) *
        (z : ModGL .E6 K) =
        (z : ModGL .E6 K) *
          rootDiagUnit .E6 (CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' v) := by
      rw [hzG]
      calc rootDiagUnit .E6 (CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' v) *
            ((G : ModGL .E6 K)⁻¹ * (y : ModGL .E6 K) * (G : ModGL .E6 K)) =
          (G : ModGL .E6 K)⁻¹ *
            (((G : ModGL .E6 K) *
              rootDiagUnit .E6 (CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' v) *
                (G : ModGL .E6 K)⁻¹) * (y : ModGL .E6 K)) * (G : ModGL .E6 K) := by
            group
        _ = (G : ModGL .E6 K)⁻¹ *
            ((y : ModGL .E6 K) *
              ((G : ModGL .E6 K) *
                rootDiagUnit .E6 (CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' v) *
                  (G : ModGL .E6 K)⁻¹)) * (G : ModGL .E6 K) := by
            rw [hcomm]
        _ = ((G : ModGL .E6 K)⁻¹ * (y : ModGL .E6 K) * (G : ModGL .E6 K)) *
              rootDiagUnit .E6 (CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' v) := by
            group
    rw [hcomm']
    group
  apply mem_range_langTorusHom K θ hθ l hl
  apply TBE6.mem_minTorus_range_of_isogeny_mem_torus
  simpa only [z, G, y, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using hz

theorem cover_centralizer_three {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f))
    (hφs : Function.Surjective φ)
    (ψ : L →* graphFixedRootGroup TwistTag.E6 K θ.toRingHom)
    (hψ : Function.Surjective ψ)
    (hφ : ∀ x, ψ (φ x) =
      CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq x)
    (hδ : ∀ b x, δ b (φ x) =
      φ (fixedDiagonalHom K (f * 2) (by rw [hK, ← pow_mul]) θ hθ l hl b x))
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ 3 = 1)
    (hζo : orderOf (ζ : Kˣ) = 3)
    (A : Subgroup (MulAut L))
    (hAH : ∀ v ∈ NoOffRest.hypE6, δ (frameB θ ζ hζ (Multiplicative.ofAdd v)) ∈ A)
    (x : L) (hx : ∀ a ∈ A, MulAut.conj x * a = a * MulAut.conj x) :
    x ∈ (φ.comp (langTorusHom K θ hθ l hl)).range := by
  obtain ⟨x₀, rfl⟩ := hφs x
  have hZ : ∀ z ∈ Subgroup.center L, ψ z = 1 := by
    intro z hz
    have hz' : ψ z ∈ Subgroup.center (graphFixedRootGroup TwistTag.E6 K θ.toRingHom) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨y, rfl⟩ := hψ w
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
    rw [center_graphFixedRootGroup_eq_bot θ.surjective, Subgroup.mem_bot] at hz'
    exact hz'
  have hcomm : ∀ v ∈ NoOffRest.hypE6,
      langDiagMat θ l (frameB θ ζ hζ (Multiplicative.ofAdd v)) *
        (show ModGL .E6 K from
          ((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq x₀ :
            graphFixedRootGroup TwistTag.E6 K θ.toRingHom) : ModGL TwistTag.E6.tag K)) =
      (show ModGL .E6 K from
        ((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq x₀ :
          graphFixedRootGroup TwistTag.E6 K θ.toRingHom) : ModGL TwistTag.E6.tag K)) *
        langDiagMat θ l (frameB θ ζ hζ (Multiplicative.ofAdd v)) := by
    intro v hv
    set b : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ :=
      frameB θ ζ hζ (Multiplicative.ofAdd v) with hb
    have ha : δ b ∈ A := by rw [hb]; exact hAH v hv
    have hcy : MulAut.conj (δ b (φ x₀)) = MulAut.conj (φ x₀) := by
      rw [show MulAut.conj (δ b (φ x₀)) = δ b * MulAut.conj (φ x₀) * (δ b)⁻¹ from by
        apply MulEquiv.ext
        intro z
        simp only [MulAut.mul_apply, MulAut.conj_apply]
        rw [map_mul, map_mul, map_inv]
        simp]
      rw [← hx (δ b) ha]
      group
    have hcZ : (δ b (φ x₀)) * (φ x₀)⁻¹ ∈ Subgroup.center L := by
      rw [← CFSG.GroupTheory.ker_conj_eq_center, MonoidHom.mem_ker, map_mul, map_inv, hcy]
      group
    have h1 : ψ (δ b (φ x₀)) = ψ (φ x₀) := by
      have h := hZ ((δ b (φ x₀)) * (φ x₀)⁻¹) hcZ
      rw [map_mul, map_inv] at h
      exact mul_inv_eq_one.mp h
    have h1' : CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq
        (fixedDiagonalHom K (f * 2) (by rw [hK, ← pow_mul]) θ hθ l hl b x₀) =
        CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq x₀ := by
      rw [← hφ, ← hφ, ← hδ b x₀]
      exact h1
    have h2m : (show ModGL .E6 K from
        ((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq
          (fixedDiagonalHom K (f * 2) (by rw [hK, ← pow_mul]) θ hθ l hl b x₀) :
          graphFixedRootGroup TwistTag.E6 K θ.toRingHom) : ModGL TwistTag.E6.tag K)) =
        (show ModGL .E6 K from
          ((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq x₀ :
            graphFixedRootGroup TwistTag.E6 K θ.toRingHom) : ModGL TwistTag.E6.tag K)) :=
      congrArg (fun z : graphFixedRootGroup TwistTag.E6 K θ.toRingHom =>
        (z : ModGL TwistTag.E6.tag K)) h1'
    have hm := isogeny_fixedDiagonalHom θ hθ l hl hf hK hθq b x₀
    rw [h2m] at hm
    have hcoe : (show ModGL .E6 K from
        ((CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq x₀ :
          graphFixedRootGroup TwistTag.E6 K θ.toRingHom) : ModGL TwistTag.E6.tag K)) =
        (e6Isogeny K (x₀ : e6Data_valid.minGroup K) : ModGL .E6 K) := rfl
    rw [hcoe] at hm
    calc langDiagMat θ l b * (e6Isogeny K (x₀ : e6Data_valid.minGroup K) : ModGL .E6 K) =
        (langDiagMat θ l b * (e6Isogeny K (x₀ : e6Data_valid.minGroup K) : ModGL .E6 K) *
          (langDiagMat θ l b)⁻¹) * langDiagMat θ l b := by group
      _ = (e6Isogeny K (x₀ : e6Data_valid.minGroup K) : ModGL .E6 K) *
            langDiagMat θ l b := by rw [← hm]
  have hxr := mem_langTorus_of_commute_hyp (K := K) θ hθ l hl hf hK hθq ζ hζ hζo hcomm
  obtain ⟨u, hu⟩ := hxr
  exact ⟨u, by rw [MonoidHom.comp_apply, hu]⟩

theorem conj_langWeyl_delta {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hφs : Function.Surjective φ)
    (hδ : ∀ b x, δ b (φ x) =
      φ (fixedDiagonalHom K (f * 2) (by rw [hK, ← pow_mul]) θ hθ l hl b x))
    (i : Fin Tag.E6.rank)
    (b : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) :
    MulAut.conj (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) * δ b *
      (MulAut.conj (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))))⁻¹ =
      δ (b * (fun j => b i ^ Tag.E6.cartan i j)⁻¹) := by
  have hform := scalar_descent_formulas θ hθ l hl φ δ hK hδ
  set n : L := φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i)) with hn
  set cor : L := φ (langCoroot K θ hθ l hl i (b i)) with hcor
  set t : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ :=
    fun j => b i ^ Tag.E6.cartan i j with ht
  have hmove : δ b n = cor * n := by
    rw [hn, hcor]
    exact hform.2.1 b i
  have hfix : δ b cor = cor := by
    rw [hcor]
    exact hform.1 b i (b i)
  have hconj : δ t = MulAut.conj cor := by
    rw [ht, hcor]
    exact scalar_descent_conj θ hθ l hl φ δ hK hφs hδ i (b i)
  apply MulEquiv.ext
  intro y
  have h1 : (MulAut.conj n * δ b * (MulAut.conj n)⁻¹) y = cor⁻¹ * δ b y * cor := by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
    rw [map_mul, map_mul, map_inv, hmove]
    group
  have h2 : δ b ((δ t)⁻¹ y) = cor⁻¹ * δ b y * cor := by
    rw [hconj, MulAut.conj_inv_apply, map_mul, map_mul, map_inv, hfix]
  calc (MulAut.conj n * δ b * (MulAut.conj n)⁻¹) y = cor⁻¹ * δ b y * cor := h1
    _ = δ b ((δ t)⁻¹ y) := h2.symm
    _ = (δ b * (δ t)⁻¹) y := by rw [MulAut.mul_apply]
    _ = (δ (b * t⁻¹)) y := by rw [map_mul, map_inv]

theorem conj_langWeyl_frame {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hφs : Function.Surjective φ)
    (hδ : ∀ b x, δ b (φ x) =
      φ (fixedDiagonalHom K (f * 2) (by rw [hK, ← pow_mul]) θ hθ l hl b x))
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ 3 = 1)
    (i : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ZMod 3) :
    MulAut.conj (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) *
      δ (frameB θ ζ hζ (Multiplicative.ofAdd x)) *
        (MulAut.conj (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))))⁻¹ =
      δ (frameB θ ζ hζ (Multiplicative.ofAdd (adRefl .E6 3 i x))) := by
  have hb : frameB θ ζ hζ (Multiplicative.ofAdd x) *
      (fun j => frameB θ ζ hζ (Multiplicative.ofAdd x) i ^ Tag.E6.cartan i j)⁻¹ =
      frameB θ ζ hζ (Multiplicative.ofAdd (adRefl .E6 3 i x)) := by
    have hζ' : (ζ : Kˣ) ^ 3 = 1 := congrArg Subtype.val hζ
    funext j
    apply Subtype.ext
    simp only [Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_zpow, frameB_coe_apply]
    let c : Fin Tag.E6.rank → ZMod 3 := fun k => (Tag.E6.cartan i k : ZMod 3) * x i
    have hpow : CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' x i ^
        Tag.E6.cartan i j = CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' c j := by
      change zmodPowHom (ζ : Kˣ) hζ' (Multiplicative.ofAdd (x i)) ^ Tag.E6.cartan i j =
        CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' c j
      rw [CFSG.StandardType.TableBExc.E6Three.zmodPowHom_zpow]
      rfl
    rw [hpow]
    have h0 : CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ'
        (0 : Fin Tag.E6.rank → ZMod 3) = 1 := by
      funext k
      simp [CFSG.StandardType.TableBExc.E6Three.zetaVec,
        CFSG.RankThree.CentralCover.zmodPowHom_apply]
    have hneg : CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' (-c) =
        (CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' c)⁻¹ := by
      have hadd := CFSG.StandardType.ExcFrames.zetaVec_add (ζ := (ζ : Kˣ)) hζ' c (-c)
      rw [add_neg_cancel, h0] at hadd
      exact eq_inv_of_mul_eq_one_right hadd.symm
    have hnegj : (CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' c j)⁻¹ =
        CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' (-c) j :=
      (congrFun hneg j).symm
    rw [hnegj]
    have hzj : CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' x j *
        CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' (-c) j =
        CFSG.StandardType.TableBExc.E6Three.zetaVec (ζ : Kˣ) hζ' (x + -c) j := by
      rw [← Pi.mul_apply]
      exact (congrFun (CFSG.StandardType.ExcFrames.zetaVec_add (ζ := (ζ : Kˣ)) hζ' x (-c)) j).symm
    rw [hzj]
    have hvec : x + -c = adRefl .E6 3 i x := by
      funext k
      simp [c, adRefl, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg, mul_comm]
    rw [hvec]
  rw [← hb]
  exact conj_langWeyl_delta θ hθ l hl φ δ hK hφs hδ i
    (frameB θ ζ hζ (Multiplicative.ofAdd x))

theorem adRefl_mem_hypE6 {x : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ NoOffRest.hypE6)
    (i : Fin Tag.E6.rank) : adRefl .E6 3 i x ∈ NoOffRest.hypE6 :=
  CFSG.StandardType.E6ThreeModel.adRefl_mem_hypE6 hx i

theorem ofAdd_mem_range_of_mem_hyp {A : Subgroup (MulAut L)}
    (κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3))
    (hκr : κ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6)
    {v : Fin Tag.E6.rank → ZMod 3} (hv : v ∈ NoOffRest.hypE6) :
    Multiplicative.ofAdd v ∈ κ.range := by
  rcases hκr with h | h
  · rw [h]
    exact Subgroup.mem_top _
  · exact (h v).2 hv

theorem frame_le_range (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ 3 = 1)
    {A : Subgroup (MulAut L)} (κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3))
    (hκ : ∀ a : A, (a : MulAut L) = δ (frameB θ ζ hζ (κ a))) :
    A ≤ δ.range := by
  intro a ha
  exact ⟨frameB θ ζ hζ (κ ⟨a, ha⟩), by simpa using (hκ ⟨a, ha⟩).symm⟩

theorem hyp_le (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ 3 = 1)
    {A : Subgroup (MulAut L)} (κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3))
    (hκ : ∀ a : A, (a : MulAut L) = δ (frameB θ ζ hζ (κ a)))
    (hκr : κ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6)
    {v : Fin Tag.E6.rank → ZMod 3} (hv : v ∈ NoOffRest.hypE6) :
    δ (frameB θ ζ hζ (Multiplicative.ofAdd v)) ∈ A := by
  obtain ⟨a, ha⟩ := ofAdd_mem_range_of_mem_hyp κ hκr hv
  have h : δ (frameB θ ζ hζ (Multiplicative.ofAdd v)) = (a : MulAut L) := by
    rw [← ha, hκ a]
  rw [h]
  exact a.2

theorem frame_act {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hφs : Function.Surjective φ)
    (hδ : ∀ b x, δ b (φ x) =
      φ (fixedDiagonalHom K (f * 2) (by rw [hK, ← pow_mul]) θ hθ l hl b x))
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ 3 = 1)
    {A : Subgroup (MulAut L)} (κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3))
    (hκ : ∀ a : A, (a : MulAut L) = δ (frameB θ ζ hζ (κ a)))
    (hκr : κ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6)
    (i : Fin Tag.E6.rank) (a : A) :
    ∃ b : A,
      MulAut.conj (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) * (a : MulAut L) *
        (MulAut.conj (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))))⁻¹ = b ∧
      Multiplicative.toAdd (κ b) =
        adRefl .E6 3 i (Multiplicative.toAdd (κ a)) := by
  let y : Fin Tag.E6.rank → ZMod 3 := adRefl .E6 3 i (Multiplicative.toAdd (κ a))
  have hy : Multiplicative.ofAdd y ∈ κ.range := by
    rcases hκr with h | h
    · rw [h]
      exact Subgroup.mem_top _
    · refine (h y).2 ?_
      exact adRefl_mem_hypE6
        ((h (Multiplicative.toAdd (κ a))).1 (MonoidHom.mem_range.mpr ⟨a, rfl⟩)) i
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 hy
  refine ⟨b, ?_, ?_⟩
  · rw [hκ a, hκ b, hb]
    exact conj_langWeyl_frame θ hθ l hl φ δ hK hφs hδ ζ hζ i
      (Multiplicative.toAdd (κ a))
  · rw [hb]
    rfl

theorem root_nontrivial_three {m : ℕ}
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ 3 = 1)
    (hζo : orderOf (ζ : Kˣ) = 3)
    (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m))
    (hδi : Function.Injective δ)
    {A : Subgroup (MulAut L)} (κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3))
    (hκ : ∀ a : A, (a : MulAut L) = δ (frameB θ ζ hζ (κ a)))
    (hκr : κ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6) :
    ∀ i, ∃ a ∈ A, scalarRoot θ δ e i a ≠ 1 := by
  intro i
  let x : Fin Tag.E6.rank → ZMod 3 := fun _ => 1
  have hx : x ∈ NoOffRest.hypE6 := by
    rw [NoOffRest.mem_hypE6]
    decide
  have hA : δ (frameB θ ζ hζ (Multiplicative.ofAdd x)) ∈ A := hyp_le θ δ ζ hζ κ hκ hκr hx
  refine ⟨δ (frameB θ ζ hζ (Multiplicative.ofAdd x)), hA, ?_⟩
  rw [scalarRoot_apply θ δ e hδi]
  intro h
  have h1 : frameB θ ζ hζ (Multiplicative.ofAdd x) i = 1 :=
    e.injective (h.trans (map_one e).symm)
  have h2 : ((frameB θ ζ hζ (Multiplicative.ofAdd x) i :
      CFSG.LieType.Steinberg.normOne θ) : Kˣ) = 1 := congrArg Subtype.val h1
  rw [frameB_coe_apply] at h2
  have hzu : (ζ : Kˣ) = 1 := by
    have h2' : (ζ : Kˣ) ^ (1 : ZMod 3).val = 1 := by
      simpa [CFSG.StandardType.TableBExc.E6Three.zetaVec, x,
        CFSG.RankThree.CentralCover.zmodPowHom_apply] using h2
    rw [ZMod.val_one] at h2'
    simpa using h2'
  have hne : (ζ : Kˣ) ≠ 1 := by
    intro hh
    rw [hh, orderOf_one] at hζo
    omega
  exact hne hzu

end CFSG.StandardType.TwE6ThreeLang

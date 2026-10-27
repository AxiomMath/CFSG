module

public import CFSG.RankThree.GF2n.Stroth80.Sec717LayerModelDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec717Layers
import CFSG.RankThree.GF2n.Stroth80.Sec717TwistedHom
import CFSG.RankThree.GF2n.Stroth80.Sec714ModelLin

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {K E X : Type} [Field K] [AddCommGroup E] [Module K E] [Group X]
  {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)} {V Nb Rb : Subgroup X}
  {T : Submodule K E}

namespace Sec717LayerData

private theorem isom_one_add (D : Sec717LayerData B φ V Nb Rb T) (n : X) (x y : E) :
    B (x + opm (φ n) x) (y + opm (φ n) y) = B x y := by
  have e : ∀ z, z + opm (φ n) z = φ n z := fun z => by rw [opm_apply]; abel
  rw [e, e]
  exact D.isom n x y

theorem isLayerCorner_of_eqOn [FiniteDimensional K E] (D : Sec717LayerData B φ V Nb Rb T)
    {n n' : X} (hn : n ∈ Nb) (hn' : n' ∈ Nb) {c : K}
    (h : ∀ w ∈ B.orthogonal T, opm (φ n') w = c • opm (φ n) w) :
    IsLayerCorner T (B.orthogonal T) (opm (φ n') - c • opm (φ n)) := by
  have hadj : ∀ {g : X}, g ∈ Nb → ∀ {w : E}, w ∈ B.orthogonal T → ∀ x,
      B w (opm (φ g) x) = -B (opm (φ g) w) x := fun hg w hw x => by
    rw [S714.bilin_D_left (D.isom_one_add _) (D.Nb_low _ hg).top (D.Nb_low _ hg).mid
      (fun v hv w hw => (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) v hv) hw x, neg_neg]
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [← LinearMap.BilinForm.orthogonal_orthogonal D.nondeg D.refl T,
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    show B w ((opm (φ n') - c • opm (φ n)) x) = 0
    rw [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, hadj hn' hw, hadj hn hw,
      h w hw, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  · rw [LinearMap.sub_apply, LinearMap.smul_apply, h x hx, sub_self]

theorem mem_of_eqOn_zero [FiniteDimensional K E] (D : Sec717LayerData B φ V Nb Rb T) {n : X}
    (hn : n ∈ Nb) (h : ∀ w ∈ B.orthogonal T, opm (φ n) w = 0) : n ∈ V := by
  have hc := D.isLayerCorner_of_eqOn hn hn (c := 0) fun w hw => by rw [h w hw, zero_smul]
  rw [zero_smul, sub_zero] at hc
  exact D.corner_mem n hn hc

theorem exists_opm_eq_smul_of_layerModel [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
    [FiniteDimensional K E] (hW3 : SL4HomW3Statement) (hK : 4 ≤ Nat.card K)
    (D : Sec717LayerData B φ V Nb Rb T) {L : Subgroup X} (hLN : L ≤ Nb) (hVL : V ≤ L)
    (hLR : ∀ r ∈ Rb, ∀ l ∈ L, r * l * r⁻¹ ∈ L) (hcent : ∀ r ∈ Rb, ∀ a ∈ V, r * a = a * r)
    (hDD : ∀ l ∈ L, ∀ l' ∈ L, ∀ x, opm (φ l) (opm (φ l') x) = 0) {a₀ : X} (ha₀ : a₀ ∈ V)
    (ha₀1 : a₀ ≠ 1) (hroot : ∀ a ∈ V, ∃ c : K, opm (φ a) = c • opm (φ a₀))
    (hroot' : ∀ c : K, ∃ a ∈ V, opm (φ a) = c • opm (φ a₀))
    (hΔ : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, ∀ w ∈ B.orthogonal T, opm (φ l') w = c • opm (φ l) w)
    (η : ↥Rb →* Matrix.SpecialLinearGroup (Fin 4) K) (hη : Function.Surjective η)
    (θ : ↥L →* Multiplicative (Fin 4 → K)) (hθ : Function.Surjective θ)
    (hθker : ∀ l, θ l = 1 ↔ (l : X) ∈ V)
    (hθeq : ∀ (r : ↥Rb) (l l' : ↥L), (l' : X) = (r : X) * l * (r : X)⁻¹ →
      Multiplicative.toAdd (θ l') = η r • Multiplicative.toAdd (θ l))
    (ψ : ↥T ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K))
    (hψ : ∀ (r : ↥Rb) (w w' : ↥T), (w' : E) = φ (r : X) w →
      ψ w' = PartOne.K159.Klein.rho (η r) (ψ w)) :
    ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, opm (φ l') = c • opm (φ l) := by
  classical
  intro l₀ hl₀ c
  set D₀ := opm (φ a₀) with hD₀
  have hopm1 : opm (1 : E ≃ₗ[K] E) = 0 := LinearMap.ext fun w => by simp [opm_apply]
  have hadd : ∀ x ∈ L, ∀ y ∈ L, opm (φ (x * y)) = opm (φ x) + opm (φ y) := fun x hx y hy =>
    LinearMap.ext fun w => by
      rw [map_mul, opm_mul_apply_layer, hDD x hx y hy, add_zero]
      rfl
  have hinv : ∀ z ∈ L, opm (φ z⁻¹) = -opm (φ z) := fun z hz => by
    have h := hadd z hz z⁻¹ (L.inv_mem hz)
    rw [mul_inv_cancel, map_one, hopm1] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  have hratio : ∀ x ∈ L, ∀ y ∈ L, (∀ w ∈ B.orthogonal T, opm (φ x) w = opm (φ y) w) →
      x⁻¹ * y ∈ V := by
    intro x hx y hy h
    refine D.mem_of_eqOn_zero (hLN (L.mul_mem (L.inv_mem hx) hy)) fun w hw => ?_
    rw [hadd _ (L.inv_mem hx) _ hy, hinv x hx, LinearMap.add_apply, LinearMap.neg_apply, h w hw,
      neg_add_cancel]
  choose lc hlcL hlc using fun x (hx : x ∈ L) => hΔ x hx c
  set F : (x : X) → x ∈ L → (E →ₗ[K] E) := fun x hx => opm (φ (lc x hx)) - c • opm (φ x)
    with hFdef
  have hF : ∀ x (hx : x ∈ L), IsLayerCorner T (B.orthogonal T) (F x hx) := fun x hx =>
    D.isLayerCorner_of_eqOn (hLN hx) (hLN (hlcL x hx)) (hlc x hx)
  have hC1 : ∀ x (hx : x ∈ L) y (hy : y ∈ L), x⁻¹ * y ∈ V →
      ∃ d : K, F y hy = F x hx + d • D₀ := by
    intro x hx y hy hxy
    have hu : (lc x hx)⁻¹ * lc y hy ∈ V := by
      refine hratio _ (hlcL x hx) _ (hlcL y hy) fun w hw => ?_
      have e : opm (φ y) w = opm (φ x) w := by
        rw [show y = x * (x⁻¹ * y) by group, hadd x hx _ (hVL hxy), LinearMap.add_apply,
          (D.V_corner _ hxy).mid w hw, add_zero]
      rw [hlc x hx w hw, hlc y hy w hw, e]
    obtain ⟨d₁, hd₁⟩ := hroot _ hu
    obtain ⟨d₂, hd₂⟩ := hroot _ hxy
    have e1 : opm (φ (lc y hy)) = opm (φ (lc x hx)) + d₁ • D₀ := by
      conv_lhs => rw [show lc y hy = lc x hx * ((lc x hx)⁻¹ * lc y hy) by group]
      rw [hadd _ (hlcL x hx) _ (hVL hu), hd₁]
    have e2 : opm (φ y) = opm (φ x) + d₂ • D₀ := by
      conv_lhs => rw [show y = x * (x⁻¹ * y) by group]
      rw [hadd x hx _ (hVL hxy), hd₂]
    refine ⟨d₁ - c * d₂, ?_⟩
    simp only [hFdef, e1, e2]
    module
  have hC2 : ∀ x (hx : x ∈ L) y (hy : y ∈ L),
      ∃ d : K, F (x * y) (L.mul_mem hx hy) = F x hx + F y hy + d • D₀ := by
    intro x hx y hy
    have hu : (lc x hx * lc y hy)⁻¹ * lc (x * y) (L.mul_mem hx hy) ∈ V := by
      refine hratio _ (L.mul_mem (hlcL x hx) (hlcL y hy)) _ (hlcL _ _) fun w hw => ?_
      rw [hadd _ (hlcL x hx) _ (hlcL y hy), LinearMap.add_apply, hlc x hx w hw, hlc y hy w hw,
        hlc _ _ w hw, hadd x hx y hy, LinearMap.add_apply, smul_add]
    obtain ⟨d, hd⟩ := hroot _ hu
    refine ⟨d, ?_⟩
    have e1 : opm (φ (lc (x * y) (L.mul_mem hx hy))) =
        opm (φ (lc x hx)) + opm (φ (lc y hy)) + d • D₀ := by
      conv_lhs => rw [show lc (x * y) (L.mul_mem hx hy) = lc x hx * lc y hy *
        ((lc x hx * lc y hy)⁻¹ * lc (x * y) (L.mul_mem hx hy)) by group]
      rw [hadd _ (L.mul_mem (hlcL x hx) (hlcL y hy)) _ (hVL hu),
        hadd _ (hlcL x hx) _ (hlcL y hy), hd]
    simp only [hFdef, e1, hadd x hx y hy]
    module
  have hC3 : ∀ r (hr : r ∈ Rb) x (hx : x ∈ L), ∃ d : K,
      F (r * x * r⁻¹) (hLR r hr x hx) =
        (φ r).toLinearMap ∘ₗ F x hx ∘ₗ (φ r⁻¹).toLinearMap + d • D₀ := by
    intro r hr x hx
    have hconj : ∀ g w, opm (φ (r * g * r⁻¹)) w = φ r (opm (φ g) (φ r⁻¹ w)) := fun g w =>
      opm_conj φ r g w
    have hu : (r * lc x hx * r⁻¹)⁻¹ * lc (r * x * r⁻¹) (hLR r hr x hx) ∈ V := by
      refine hratio _ (hLR r hr _ (hlcL x hx)) _ (hlcL _ _) fun w hw => ?_
      have hw' : φ r⁻¹ w ∈ B.orthogonal T := D.Rb_P _ (Rb.inv_mem hr) w hw
      rw [hconj, hlc x hx _ hw', hlc _ _ w hw, hconj, map_smul]
    obtain ⟨d, hd⟩ := hroot _ hu
    refine ⟨d, ?_⟩
    have e1 : opm (φ (lc (r * x * r⁻¹) (hLR r hr x hx))) =
        (φ r).toLinearMap ∘ₗ opm (φ (lc x hx)) ∘ₗ (φ r⁻¹).toLinearMap + d • D₀ := by
      conv_lhs => rw [show lc (r * x * r⁻¹) (hLR r hr x hx) = r * lc x hx * r⁻¹ *
        ((r * lc x hx * r⁻¹)⁻¹ * lc (r * x * r⁻¹) (hLR r hr x hx)) by group]
      rw [hadd _ (hLR r hr _ (hlcL x hx)) _ (hVL hu), hd]
      congr 1
      exact LinearMap.ext fun w => hconj _ w
    have e2 : opm (φ (r * x * r⁻¹)) = (φ r).toLinearMap ∘ₗ opm (φ x) ∘ₗ (φ r⁻¹).toLinearMap :=
      LinearMap.ext fun w => hconj _ w
    simp only [hFdef, e1, e2, LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_smul,
      LinearMap.smul_comp]
    module
  have hmemT : ∀ x, D₀ x ∈ T := fun x => by
    rw [← D.range_V a₀ ha₀ ha₀1]
    exact LinearMap.mem_range_self _ x
  obtain ⟨s, hs⟩ : ∃ s : ↥T →ₗ[K] E, ∀ t : ↥T, D₀ (s t) = t := by
    obtain ⟨s', hs'⟩ := LinearMap.exists_rightInverse_of_surjective (D₀.codRestrict T hmemT)
      (LinearMap.range_eq_top.mpr fun t => by
        have ht : (t : E) ∈ LinearMap.range D₀ := by rw [D.range_V a₀ ha₀ ha₀1]; exact t.2
        obtain ⟨x, hx⟩ := ht
        exact ⟨x, Subtype.ext hx⟩)
    exact ⟨s', fun t => congrArg Subtype.val (LinearMap.congr_fun hs' t)⟩
  obtain ⟨pr, hpr⟩ : ∃ pr : E →ₗ[K] ↥T, ∀ t : ↥T, pr t = t := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective T.subtype (Submodule.ker_subtype T)
    exact ⟨g, fun t => LinearMap.congr_fun hg t⟩
  let Ψ : (E →ₗ[K] E) →ₗ[K] Module.End K (Fin 3 ⊕ Fin 3 → K) :=
    { toFun := fun G => ψ.toLinearMap ∘ₗ pr ∘ₗ G ∘ₗ s ∘ₗ ψ.symm.toLinearMap
      map_add' := fun G G' => by ext u; simp
      map_smul' := fun c G => by ext u; simp }
  have hΨ : ∀ G u, Ψ G u = ψ (pr (G (s (ψ.symm u)))) := fun G u => rfl
  have hcs : ∀ G : E →ₗ[K] E, IsLayerCorner T (B.orthogonal T) G →
      ∀ x, G x = G (s ⟨D₀ x, hmemT x⟩) := fun G hG x => by
    rw [← sub_eq_zero, ← map_sub]
    refine hG.mid _ ?_
    rw [← D.ker_V a₀ ha₀ ha₀1, LinearMap.mem_ker, map_sub, hs, sub_self]
  have hprT : ∀ G : E →ₗ[K] E, IsLayerCorner T (B.orthogonal T) G →
      ∀ x, ((pr (G x) : ↥T) : E) = G x := fun G hG x => by
    rw [show pr (G x) = pr ((⟨G x, hG.top x⟩ : ↥T) : E) from rfl, hpr]
  have hΨinj : ∀ G : E →ₗ[K] E, IsLayerCorner T (B.orthogonal T) G → Ψ G = 0 → G = 0 := by
    intro G hG h0
    ext x
    rw [hcs G hG x, LinearMap.zero_apply]
    have h1 := LinearMap.congr_fun h0 (ψ ⟨D₀ x, hmemT x⟩)
    rw [hΨ, LinearEquiv.symm_apply_apply, LinearMap.zero_apply,
      LinearEquiv.map_eq_zero_iff] at h1
    rw [← hprT G hG, h1, Submodule.coe_zero]
  have hD₀c : IsLayerCorner T (B.orthogonal T) D₀ := D.V_corner a₀ ha₀
  have hΨD₀ : Ψ D₀ = LinearMap.id := LinearMap.ext fun u => by
    rw [hΨ, LinearMap.id_apply, show pr (D₀ (s (ψ.symm u))) = ψ.symm u by
      rw [show D₀ (s (ψ.symm u)) = ((ψ.symm u : ↥T) : E) from hs _, hpr],
      LinearEquiv.apply_symm_apply]
  have hcomm₀ : ∀ r ∈ Rb, ∀ y, D₀ (φ r y) = φ r (D₀ y) := by
    intro r hr y
    have h := DFunLike.congr_fun (congrArg φ (hcent r hr a₀ ha₀)) y
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
    rw [hD₀, opm_apply, opm_apply, map_sub, h]
  have hΨconj : ∀ (r : ↥Rb) (G : E →ₗ[K] E), IsLayerCorner T (B.orthogonal T) G →
      Ψ ((φ (r : X)).toLinearMap ∘ₗ G ∘ₗ (φ (r : X)⁻¹).toLinearMap) =
        (PartOne.K159.Klein.rho (η r)).toLinearMap ∘ₗ Ψ G ∘ₗ
          (PartOne.K159.Klein.rho (η r)⁻¹).toLinearMap := by
    intro r G hG
    refine LinearMap.ext fun u => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hΨ]
    set t := ψ.symm u with ht
    have hrT' : φ (r : X)⁻¹ t ∈ T := D.Rb_T _ (Rb.inv_mem r.2) t t.2
    set t' : ↥T := ⟨φ (r : X)⁻¹ t, hrT'⟩ with ht'
    have e1 : G (φ (r : X)⁻¹ (s t)) = G (s t') := by
      rw [hcs G hG (φ (r : X)⁻¹ (s t))]
      congr 2
      exact Subtype.ext (by
        show D₀ (φ (r : X)⁻¹ (s t)) = φ (r : X)⁻¹ t
        rw [hcomm₀ _ (Rb.inv_mem r.2), hs])
    have hT1 : G (s t') ∈ T := hG.top _
    have hT2 : φ (r : X) (G (s t')) ∈ T := D.Rb_T _ r.2 _ hT1
    have e2 : pr (φ (r : X) (G (φ (r : X)⁻¹ (s t)))) = ⟨φ (r : X) (G (s t')), hT2⟩ := by
      rw [e1]
      exact hpr ⟨φ (r : X) (G (s t')), hT2⟩
    have e3 : ψ ⟨φ (r : X) (G (s t')), hT2⟩ =
        PartOne.K159.Klein.rho (η r) (ψ ⟨G (s t'), hT1⟩) := hψ r _ _ rfl
    have e4 : ψ.symm (PartOne.K159.Klein.rho (η r)⁻¹ u) = t' := by
      rw [LinearEquiv.symm_apply_eq]
      have h := hψ r⁻¹ t t' rfl
      rw [map_inv] at h
      rw [h, ht, LinearEquiv.apply_symm_apply]
    have e5 : pr (G (s (ψ.symm (PartOne.K159.Klein.rho (η r)⁻¹ u)))) = ⟨G (s t'), hT1⟩ := by
      rw [e4]
      exact hpr ⟨G (s t'), hT1⟩
    rw [e2, e3, e5]
  choose xs hxsθ using fun v : Fin 4 → K => hθ (Multiplicative.ofAdd v)
  have hθV : ∀ x (hx : x ∈ L) y (hy : y ∈ L), θ ⟨x, hx⟩ = θ ⟨y, hy⟩ → x⁻¹ * y ∈ V := by
    intro x hx y hy h
    have h1 : θ (⟨x, hx⟩⁻¹ * ⟨y, hy⟩) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    exact (hθker _).mp h1
  let g : (Fin 4 → K) → Module.End K (Fin 3 ⊕ Fin 3 → K) := fun v =>
    Ψ (F (xs v : X) (xs v).2)
  have hgadd : ∀ v w, ∃ d : K, g (v + w) = g v + g w + d • LinearMap.id := by
    intro v w
    obtain ⟨d₁, hd₁⟩ := hC1 _ (L.mul_mem (xs v).2 (xs w).2) _ (xs (v + w)).2
      (hθV _ (L.mul_mem (xs v).2 (xs w).2) _ (xs (v + w)).2 (by
        rw [hxsθ (v + w)]
        show θ (xs v * xs w) = _
        rw [map_mul, hxsθ, hxsθ]
        rfl))
    obtain ⟨d₂, hd₂⟩ := hC2 _ (xs v).2 _ (xs w).2
    refine ⟨d₂ + d₁, ?_⟩
    show Ψ (F _ _) = Ψ (F _ _) + Ψ (F _ _) + (d₂ + d₁) • LinearMap.id
    rw [hd₁, hd₂, map_add, map_add, map_add, map_smul, map_smul, hΨD₀, add_smul]
    abel
  have hgeq : ∀ (A : Matrix.SpecialLinearGroup (Fin 4) K) (v : Fin 4 → K), ∃ d : K,
      g (A • v) = (PartOne.K159.Klein.rho A).toLinearMap ∘ₗ g v ∘ₗ
        (PartOne.K159.Klein.rho A⁻¹).toLinearMap + d • LinearMap.id := by
    intro A v
    obtain ⟨r, rfl⟩ := hη A
    have hx' : (r : X) * (xs v : X) * (r : X)⁻¹ ∈ L := hLR _ r.2 _ (xs v).2
    obtain ⟨d₁, hd₁⟩ := hC1 _ hx' _ (xs (η r • v)).2 (hθV _ hx' _ (xs (η r • v)).2 (by
      rw [hxsθ (η r • v)]
      apply Multiplicative.toAdd.injective
      rw [hθeq r (xs v) ⟨_, hx'⟩ rfl, hxsθ]
      rfl))
    obtain ⟨d₂, hd₂⟩ := hC3 _ r.2 _ (xs v).2
    refine ⟨d₂ + d₁, ?_⟩
    show Ψ (F _ _) = _
    rw [hd₁, hd₂, map_add, map_add, map_smul, map_smul, hΨD₀, hΨconj r _ (hF _ (xs v).2),
      add_smul, add_assoc]
  obtain ⟨d, hd⟩ := eq_scalar_of_sl4HomW3 hW3 hK g hgadd hgeq
    (Multiplicative.toAdd (θ ⟨l₀, hl₀⟩))
  obtain ⟨d', hd'⟩ := hC1 _ (xs (Multiplicative.toAdd (θ ⟨l₀, hl₀⟩))).2 _ hl₀
    (hθV _ (xs _).2 _ hl₀ (by rw [hxsθ]; rfl))
  have hFl₀ : F l₀ hl₀ = (d + d') • D₀ := by
    have hcor : IsLayerCorner T (B.orthogonal T) (F l₀ hl₀ - (d + d') • D₀) := by
      refine ⟨fun x => T.sub_mem ((hF l₀ hl₀).top x) (T.smul_mem _ (hD₀c.top x)),
        fun x hx => ?_⟩
      rw [LinearMap.sub_apply, LinearMap.smul_apply, (hF l₀ hl₀).mid x hx, hD₀c.mid x hx,
        smul_zero, sub_zero]
    refine sub_eq_zero.mp (hΨinj _ hcor ?_)
    rw [map_sub, hd', map_add, map_smul, map_smul, hΨD₀]
    have e : Ψ (F _ (xs (Multiplicative.toAdd (θ ⟨l₀, hl₀⟩))).2) = d • LinearMap.id := hd
    rw [e, add_smul, sub_self]
  obtain ⟨a, haV, ha⟩ := hroot' (d + d')
  refine ⟨lc l₀ hl₀ * a⁻¹, L.mul_mem (hlcL l₀ hl₀) (L.inv_mem (hVL haV)), ?_⟩
  rw [hadd _ (hlcL l₀ hl₀) _ (L.inv_mem (hVL haV)), hinv a (hVL haV), ha, ← hFl₀]
  simp only [hFdef]
  abel


end Sec717LayerData

end CFSG.RankThree.GF2n.Stroth80

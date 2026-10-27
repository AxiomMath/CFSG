module

public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogue
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImageNormB
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotNorm
import CFSG.LocalAnalysis.StandardType.GGFrameRouteEndLabel
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneSignedPerm
import CFSG.LocalAnalysis.StandardType.GGQ2SignedPermMem
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix

public section

namespace CFSG.StandardType

open GGQ2Frame

@[expose] noncomputable def cornerFrameVec {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r)) :
    (Fin r → Multiplicative (ZMod 3)) →* G :=
  L.subtype.comp ((Bs.subgroupOf L).subtype.comp
    ((AddEquiv.toMultiplicativeRight R.coord).symm.toMonoidHom.comp
      (MulEquiv.piMultiplicative fun _ : Fin r => ZMod 3).symm.toMonoidHom))

private noncomputable def cornerFrameEquiv {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r)) :
    (Fin r → Multiplicative (ZMod 3)) ≃* ↥(Bs.subgroupOf L) :=
  (MulEquiv.piMultiplicative (fun _ : Fin r => ZMod 3)).symm.trans
    (AddEquiv.toMultiplicativeRight R.coord).symm

private noncomputable def toAddVec {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (_R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    (w : Fin r → Multiplicative (ZMod 3)) : (planeEntry .symplectic r).V :=
  fun j => Multiplicative.toAdd (w j)

private theorem toAddVec_apply {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    (w : Fin r → Multiplicative (ZMod 3)) :
    toAddVec R w = fun j => Multiplicative.toAdd (w j) := rfl

private theorem cornerFrameVec_apply {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    (w : Fin r → Multiplicative (ZMod 3)) :
    cornerFrameVec R w = (((cornerFrameEquiv R w : ↥(Bs.subgroupOf L)) : ↥L) : G) := rfl

private theorem cornerFrameEquiv_coord {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    (w : Fin r → Multiplicative (ZMod 3)) :
    R.coord (Additive.ofMul (cornerFrameEquiv R w)) = toAddVec R w := by
  change R.coord ((R.coord).symm (toAddVec R w)) = toAddVec R w
  rw [AddEquiv.apply_symm_apply]

private theorem cornerFrameEquiv_eq_of_coord {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    {a : ↥(Bs.subgroupOf L)} {w : Fin r → Multiplicative (ZMod 3)}
    (h : R.coord (Additive.ofMul a) = toAddVec R w) :
    cornerFrameEquiv R w = a := by
  refine Additive.ofMul.injective ((R.coord).injective ?_)
  rw [cornerFrameEquiv_coord, h]

theorem cornerFrameVec_mem {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    (w : Fin r → Multiplicative (ZMod 3)) : cornerFrameVec R w ∈ Bs ⊓ L := by
  rw [cornerFrameVec_apply]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp (cornerFrameEquiv R w).2
  · exact (((cornerFrameEquiv R w : ↥(Bs.subgroupOf L)) : ↥L)).2

theorem cornerFrameVec_injective {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r)) :
    Function.Injective (cornerFrameVec R) := by
  intro w w' h
  rw [cornerFrameVec_apply, cornerFrameVec_apply] at h
  exact (cornerFrameEquiv R).injective (Subtype.ext (Subtype.ext h))

theorem cornerFrameVec_coord {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    (a : ↥(Bs.subgroupOf L)) :
    cornerFrameVec R (fun k => Multiplicative.ofAdd
      ((R.coord (Additive.ofMul a) : PlaneRaw.V r) k)) = ((a : ↥L) : G) := by
  rw [cornerFrameVec_apply,
    cornerFrameEquiv_eq_of_coord R (a := a) (w := fun k => Multiplicative.ofAdd
      ((R.coord (Additive.ofMul a) : PlaneRaw.V r) k)) (by funext k; simp [toAddVec_apply])]

theorem eta_eq_mulSingle_of_mem_centralizer {G : Type} [Group G] {Bs L : Subgroup G} {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    {b : ↥Bs} (hbL : (b : G) ∈ Subgroup.centralizer (L : Set G)) :
    eta b = Pi.mulSingle i0 (eta b i0) := by
  have haxis : ∀ u ∈ (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom,
      u (eta b) = eta b := by
    rintro u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    change MulAut.congr eta v (eta b) = eta b
    rw [congr_apply_tau,
      FrameRoute.ggAutomizer_apply_eq_of_mem_centralizer hv hbL]
  rw [hb] at haxis
  have hoff : ∀ k, k ≠ i0 → eta b k = 1 :=
    (forall_bCoordinateBlock_fix_iff (p := 3) (by norm_num) (by norm_num) i0 (eta b)).mp haxis
  funext k
  by_cases hk : k = i0
  · subst hk
    rw [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hk]
    exact hoff k hk

private theorem cornerFrameVec_range_eq {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r)) :
    (cornerFrameVec R).range = Bs ⊓ L := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, rfl⟩
    exact cornerFrameVec_mem R w
  · intro b hb
    let a : ↥(Bs.subgroupOf L) := ⟨⟨b, hb.2⟩, Subgroup.mem_subgroupOf.mpr hb.1⟩
    refine ⟨fun k => Multiplicative.ofAdd (R.coord (Additive.ofMul a) k), ?_⟩
    simpa using cornerFrameVec_coord R a

private theorem inf_sup_zpowers_eq {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hx : x ∈ Bs)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k) :
    Bs ⊓ L ⊔ Subgroup.zpowers x = Bs := by
  refine le_antisymm (sup_le inf_le_left (Subgroup.zpowers_le.mpr hx)) ?_
  intro b hb
  obtain ⟨a, ha, k, rfl⟩ := hsplit b hb
  exact Subgroup.mul_mem_sup ha (Subgroup.zpow_mem_zpowers x k)

private theorem cornerFrameVec_sup_zpowers {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {r : ℕ} (hx : x ∈ Bs)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r)) :
    (cornerFrameVec R).range ⊔ Subgroup.zpowers x = Bs := by
  rw [cornerFrameVec_range_eq R]
  exact inf_sup_zpowers_eq hx hsplit

private theorem cornerFrameVec_inf_zpowers {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {r : ℕ} (hxL' : Subgroup.zpowers x ⊓ L = ⊥)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r)) :
    (cornerFrameVec R).range ⊓ Subgroup.zpowers x = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro y ⟨⟨w, rfl⟩, hy⟩
  have hmem : cornerFrameVec R w ∈ Subgroup.zpowers x ⊓ L :=
    ⟨hy, (cornerFrameVec_mem R w).2⟩
  rwa [hxL', Subgroup.mem_bot] at hmem

private theorem exists_cornerFrame_prodEquiv {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {r : ℕ} (hBs : CFSG.Open.IsElemAbelian 3 Bs) (hx : x ∈ Bs)
    (hxL' : Subgroup.zpowers x ⊓ L = ⊥)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r)) :
    ∃ Θ : ((Fin r → Multiplicative (ZMod 3)) × ↥(Subgroup.zpowers x)) ≃* ↥Bs,
      ∀ (w : Fin r → Multiplicative (ZMod 3)) (c : ↥(Subgroup.zpowers x)),
        ((Θ (w, c) : ↥Bs) : G) = cornerFrameVec R w * c := by
  refine TypeBDatum.exists_prodEquiv_of_frame (p := 3) hBs (cornerFrameVec R)
    (cornerFrameVec_injective R) ?_ (Subgroup.zpowers x) ?_ ?_ ?_
  · rintro _ ⟨w, rfl⟩
    exact (cornerFrameVec_mem R w).1
  · exact Subgroup.zpowers_le.mpr hx
  · exact cornerFrameVec_sup_zpowers hx hsplit R
  · exact cornerFrameVec_inf_zpowers hxL' R

private theorem conj_eq_of_mem_zpowers {G : Type} [Group G] {L : Subgroup G} {x g u : G}
    (hxL : x ∈ Subgroup.centralizer (L : Set G)) (hg : g ∈ L)
    (hu : u ∈ Subgroup.zpowers x) : g * u * g⁻¹ = u := by
  have hu' : u ∈ Subgroup.centralizer (L : Set G) := Subgroup.zpowers_le.mpr hxL hu
  have hcomm : g * u = u * g := Subgroup.mem_centralizer_iff.mp hu' g hg
  calc g * u * g⁻¹ = (u * g) * g⁻¹ := by rw [hcomm]
    _ = u := by group

private theorem mem_normalizer_subgroupOf_of_mem_normalizer {G : Type} [Group G]
    {Bs L : Subgroup G} {g : G} (hg : g ∈ L)
    (hgN : g ∈ Subgroup.normalizer (Bs : Set G)) :
    (⟨g, hg⟩ : ↥L) ∈ Subgroup.normalizer ((Bs.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  rw [Subgroup.mem_normalizer_iff] at hgN ⊢
  intro x
  constructor
  · intro hx
    refine Subgroup.mem_subgroupOf.mpr ?_
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (hgN (x : G)).mp (Subgroup.mem_subgroupOf.mp hx)
  · intro hx
    refine Subgroup.mem_subgroupOf.mpr ((hgN (x : G)).mpr ?_)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using Subgroup.mem_subgroupOf.mp hx

private theorem conj_mem_of_mem_normalizer_subgroupOf {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} (hx : x ∈ Bs)
    (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    {g : ↥L} (hg : g ∈ Subgroup.normalizer ((Bs.subgroupOf L : Subgroup ↥L) : Set ↥L))
    {y : G} (hy : y ∈ Bs) : (g : G) * y * (g : G)⁻¹ ∈ Bs := by
  obtain ⟨a, ha, k, rfl⟩ := hsplit y hy
  have haE : (⟨a, ha.2⟩ : ↥L) ∈ Bs.subgroupOf L := Subgroup.mem_subgroupOf.mpr ha.1
  have hconj : (g : G) * a * (g : G)⁻¹ ∈ Bs :=
    Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hg ⟨a, ha.2⟩).mp haE)
  have hxfix : (g : G) * x * (g : G)⁻¹ = x :=
    conj_eq_of_mem_zpowers hxL g.2 (Subgroup.mem_zpowers x)
  have h1 : (g : G) * (a * x ^ k) * (g : G)⁻¹ =
      ((g : G) * a * (g : G)⁻¹) * x ^ k := by
    calc (g : G) * (a * x ^ k) * (g : G)⁻¹
        = ((g : G) * a * (g : G)⁻¹) * ((g : G) * x * (g : G)⁻¹) ^ k := by
          rw [conj_zpow]
          group
      _ = ((g : G) * a * (g : G)⁻¹) * x ^ k := by rw [hxfix]
  rw [h1]
  exact Bs.mul_mem hconj (Bs.zpow_mem hx k)

private theorem mem_normalizer_of_mem_normalizer_subgroupOf {G : Type} [Group G]
    {Bs L : Subgroup G} {x : G} (hx : x ∈ Bs)
    (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    {g : ↥L} (hg : g ∈ Subgroup.normalizer ((Bs.subgroupOf L : Subgroup ↥L) : Set ↥L)) :
    (g : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact conj_mem_of_mem_normalizer_subgroupOf hx hxL hsplit hg hy
  · intro hy
    have h1 := conj_mem_of_mem_normalizer_subgroupOf hx hxL hsplit (Subgroup.inv_mem _ hg)
      (y := (g : G) * y * (g : G)⁻¹) hy
    convert h1 using 1
    simp only [Subgroup.coe_inv, inv_inv]
    group

private theorem negEquiv_apply (r : ℕ) (k : Fin r) (u : PlaneRaw.V r) (i : Fin r) :
    PlaneRaw.negEquiv r k u i = if i = k then -u i else u i := by
  simp only [PlaneRaw.negEquiv, LinearEquiv.piCongrRight_apply]
  by_cases h : i = k
  · simp only [h, if_true, LinearEquiv.neg_apply]
    rfl
  · simp only [h, if_false, LinearEquiv.refl_apply]

private theorem negEquiv_toAdd_sgnAut {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    (k : Fin r) (w : Fin r → Multiplicative (ZMod 3)) :
    PlaneRaw.negEquiv r k (toAddVec R w) = toAddVec R (SpCoord.sgnAut k w) := by
  change PlaneRaw.negEquiv r k (fun i => Multiplicative.toAdd (w i)) =
    fun i => Multiplicative.toAdd (SpCoord.sgnAut k w i)
  funext i
  rw [SpCoord.sgnAut_apply]
  by_cases h : i = k
  · rw [h, negEquiv_apply, if_pos rfl, Function.update_self, toAdd_inv]
    rfl
  · rw [negEquiv_apply, if_neg h, Function.update_of_ne h]

private theorem swapEquiv_apply (r : ℕ) (a b : Fin r) (u : PlaneRaw.V r) (i : Fin r) :
    PlaneRaw.swapEquiv r a b u i = u (Equiv.swap a b i) := by
  simp [PlaneRaw.swapEquiv]

private theorem swapEquiv_toAdd_permAut {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    (a b : Fin r) (w : Fin r → Multiplicative (ZMod 3)) :
    PlaneRaw.swapEquiv r a b (toAddVec R w) =
      toAddVec R (SpCoord.permAut (Equiv.swap a b) w) := by
  change PlaneRaw.swapEquiv r a b (fun i => Multiplicative.toAdd (w i)) =
    fun i => Multiplicative.toAdd (SpCoord.permAut (Equiv.swap a b) w i)
  funext i
  rw [swapEquiv_apply, SpCoord.permAut_apply]
  rfl

private theorem toAdd_congr_symm_apply {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    (ψ : MulAut ↥(Bs.subgroupOf L)) (w : Fin r → Multiplicative (ZMod 3)) (i : Fin r) :
    Multiplicative.toAdd ((MulAut.congr (cornerFrameEquiv R).symm ψ) w i) =
      ggLin (p := 3) R.coord ψ (toAddVec R w) i := by
  have h1 : (MulAut.congr (cornerFrameEquiv R).symm ψ) w =
      (cornerFrameEquiv R).symm (ψ (cornerFrameEquiv R w)) := by
    have h := congr_apply_tau (cornerFrameEquiv R).symm ψ (cornerFrameEquiv R w)
    rwa [MulEquiv.symm_apply_apply] at h
  rw [h1]
  have h2 := cornerFrameEquiv_coord R ((cornerFrameEquiv R).symm (ψ (cornerFrameEquiv R w)))
  rw [MulEquiv.apply_symm_apply] at h2
  have h3 := ggLin_apply_ofMul (p := 3) R.coord ψ (cornerFrameEquiv R w)
  rw [cornerFrameEquiv_coord R w] at h3
  rw [h3, h2]
  rfl

private theorem isSignedPerm_congr_symm {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    {ψ : MulAut ↥(Bs.subgroupOf L)}
    (hT : ggLin (p := 3) R.coord ψ ∈ PlaneRaw.signedPermGroup r) :
    SpCoord.IsSignedPerm (MulAut.congr (cornerFrameEquiv R).symm ψ) := by
  obtain ⟨π, ε, hε, hπε⟩ := PlaneRaw.exists_signedPerm_of_mem_signedPermGroup hT
  have hπε' : ∀ (u : (planeEntry .symplectic r).V) (i : Fin r),
      ggLin (p := 3) R.coord ψ u i = ε i * u (π.symm i) := hπε
  refine ⟨π, fun i => ε (π i), fun i => hε (π i), fun f i => ?_⟩
  rw [toAdd_congr_symm_apply]
  simpa [toAddVec_apply] using hπε' (toAddVec R f) (π i)

private theorem mem_signedAut_congr_symm {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    {ψ : MulAut ↥(Bs.subgroupOf L)}
    (hT : ggLin (p := 3) R.coord ψ ∈ PlaneRaw.signedPermGroup r) :
    MulAut.congr (cornerFrameEquiv R).symm ψ ∈ TypeBDatum.signedAut r 3 := by
  show MulAut.congr (cornerFrameEquiv R).symm ψ ∈ TypeBDatum.signedSupportedAut r 3 Finset.univ
  refine SpCoord.mem_of_isSignedPerm ?_ ?_ (isSignedPerm_congr_symm R hT)
  · intro i
    exact Subgroup.subset_closure (Or.inl ⟨i, Finset.mem_univ i, rfl⟩)
  · intro a b hab
    exact Subgroup.subset_closure
      (Or.inr ⟨a, Finset.mem_univ a, b, Finset.mem_univ b, hab, rfl⟩)

private theorem cornerFrame_ambientNormalizer {G : Type} [Group G] {Bs L : Subgroup G} {r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r)) :
    (ggAutomizer (⊤ : Subgroup ↥L) (Bs.subgroupOf L)).map
      (ggLin (p := 3) R.coord) = PlaneRaw.signedPermGroup r := by
  have h := R.ambientNormalizer_eq
  change (ggAutomizer (⊤ : Subgroup ↥L) (Bs.subgroupOf L)).map
    (ggLin (p := 3) R.coord) = PlaneRaw.signedPermGroup r at h
  exact h

private theorem eq_liftBs_conjAut {G : Type} [Group G] {Bs L : Subgroup G} {x : G} {r : ℕ}
    (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    (Θ : ((Fin r → Multiplicative (ZMod 3)) × ↥(Subgroup.zpowers x)) ≃* ↥Bs)
    (hΘ : ∀ (w : Fin r → Multiplicative (ZMod 3)) (c : ↥(Subgroup.zpowers x)),
      ((Θ (w, c) : ↥Bs) : G) = cornerFrameVec R w * c)
    {g : ↥L}
    (hgE : g ∈ Subgroup.normalizer ((Bs.subgroupOf L : Subgroup ↥L) : Set ↥L))
    (hgN : (g : G) ∈ Subgroup.normalizer (Bs : Set G))
    {τ : MulAut (Fin r → Multiplicative (ZMod 3))}
    (hτ : ∀ w, ggLin (p := 3) R.coord (ggConjAut (Bs.subgroupOf L) hgE)
      (toAddVec R w) = toAddVec R (τ w)) :
    ggConjAut Bs hgN = TypeBDatum.liftBs Θ τ := by
  refine TypeBDatum.eq_liftBs_of_apply Θ (ggConjAut Bs hgN) τ ?_ ?_
  · intro w
    apply Subtype.ext
    rw [ggConjAut_apply, hΘ w 1, hΘ (τ w) 1]
    simp only [Subgroup.coe_one, mul_one]
    have hframe : ggConjAut (Bs.subgroupOf L) hgE (cornerFrameEquiv R w) =
        cornerFrameEquiv R (τ w) := by
      refine Additive.ofMul.injective ((R.coord).injective ?_)
      have h3 := ggLin_apply_ofMul (p := 3) R.coord
        (ggConjAut (Bs.subgroupOf L) hgE) (cornerFrameEquiv R w)
      rw [cornerFrameEquiv_coord R w, hτ] at h3
      rw [cornerFrameEquiv_coord R (τ w)]
      exact h3.symm
    have hX : (((ggConjAut (Bs.subgroupOf L) hgE (cornerFrameEquiv R w) :
        ↥(Bs.subgroupOf L)) : ↥L) : G) = (g : G) * cornerFrameVec R w * (g : G)⁻¹ := by
      have h := congrArg (fun y : ↥L => (y : G))
        (ggConjAut_apply (Bs.subgroupOf L) hgE (cornerFrameEquiv R w))
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, cornerFrameVec_apply] using h
    have hY : (((ggConjAut (Bs.subgroupOf L) hgE (cornerFrameEquiv R w) :
        ↥(Bs.subgroupOf L)) : ↥L) : G) = cornerFrameVec R (τ w) := by
      rw [hframe, cornerFrameVec_apply]
    rw [← hX, hY]
  · intro u
    apply Subtype.ext
    rw [ggConjAut_apply, hΘ 1 u]
    simp only [map_one, one_mul]
    exact conj_eq_of_mem_zpowers hxL g.2 u.2

private theorem liftBs_sgnAut_mem_ggAutomizer {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {r : ℕ} (hx : x ∈ Bs) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    (Θ : ((Fin r → Multiplicative (ZMod 3)) × ↥(Subgroup.zpowers x)) ≃* ↥Bs)
    (hΘ : ∀ (w : Fin r → Multiplicative (ZMod 3)) (c : ↥(Subgroup.zpowers x)),
      ((Θ (w, c) : ↥Bs) : G) = cornerFrameVec R w * c)
    (k : Fin r) : TypeBDatum.liftBs Θ (SpCoord.sgnAut k) ∈ ggAutomizer L Bs := by
  have hAN := cornerFrame_ambientNormalizer R
  have hmem : PlaneRaw.negEquiv r k ∈
      (ggAutomizer (⊤ : Subgroup ↥L) (Bs.subgroupOf L)).map (ggLin (p := 3) R.coord) := by
    rw [hAN]
    exact Subgroup.subset_closure (Or.inr ⟨k, rfl⟩)
  obtain ⟨ψ, hψ, hψT⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨g', -, hgE, hgψ⟩ := mem_ggAutomizer_iff.mp hψ
  have hψeq : ψ = ggConjAut (Bs.subgroupOf L) hgE := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [hgψ b, ggConjAut_apply]
  have hgN : (g' : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    mem_normalizer_of_mem_normalizer_subgroupOf hx hxL hsplit hgE
  have hmemφ : ggConjAut Bs hgN ∈ ggAutomizer L Bs :=
    ggConjAut_mem_ggAutomizer g'.2 hgN
  have heq : ggConjAut Bs hgN = TypeBDatum.liftBs Θ (SpCoord.sgnAut k) := by
    refine eq_liftBs_conjAut hxL R Θ hΘ hgE hgN (fun w => ?_)
    have hψT' : (ggLin (p := 3) R.coord) ψ = PlaneRaw.negEquiv r k := hψT
    rw [← hψeq, hψT']
    exact negEquiv_toAdd_sgnAut R k w
  rw [← heq]
  exact hmemφ

private theorem liftBs_permAut_mem_ggAutomizer {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {r : ℕ} (hx : x ∈ Bs) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    (Θ : ((Fin r → Multiplicative (ZMod 3)) × ↥(Subgroup.zpowers x)) ≃* ↥Bs)
    (hΘ : ∀ (w : Fin r → Multiplicative (ZMod 3)) (c : ↥(Subgroup.zpowers x)),
      ((Θ (w, c) : ↥Bs) : G) = cornerFrameVec R w * c)
    (a b : Fin r) :
    TypeBDatum.liftBs Θ (SpCoord.permAut (Equiv.swap a b)) ∈ ggAutomizer L Bs := by
  have hAN := cornerFrame_ambientNormalizer R
  have hmem : PlaneRaw.swapEquiv r a b ∈
      (ggAutomizer (⊤ : Subgroup ↥L) (Bs.subgroupOf L)).map (ggLin (p := 3) R.coord) := by
    rw [hAN]
    exact Subgroup.subset_closure (Or.inl ⟨a, b, rfl⟩)
  obtain ⟨ψ, hψ, hψT⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨g', -, hgE, hgψ⟩ := mem_ggAutomizer_iff.mp hψ
  have hψeq : ψ = ggConjAut (Bs.subgroupOf L) hgE := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [hgψ b, ggConjAut_apply]
  have hgN : (g' : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    mem_normalizer_of_mem_normalizer_subgroupOf hx hxL hsplit hgE
  have hmemφ : ggConjAut Bs hgN ∈ ggAutomizer L Bs :=
    ggConjAut_mem_ggAutomizer g'.2 hgN
  have heq : ggConjAut Bs hgN = TypeBDatum.liftBs Θ (SpCoord.permAut (Equiv.swap a b)) := by
    refine eq_liftBs_conjAut hxL R Θ hΘ hgE hgN (fun w => ?_)
    have hψT' : (ggLin (p := 3) R.coord) ψ = PlaneRaw.swapEquiv r a b := hψT
    rw [← hψeq, hψT']
    exact swapEquiv_toAdd_permAut R a b w
  rw [← heq]
  exact hmemφ

private theorem ggAutomizer_eq_map_liftBs_corner {G : Type} [Group G] {Bs L : Subgroup G}
    {x : G} {r : ℕ} (hx : x ∈ Bs)
    (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    (Θ : ((Fin r → Multiplicative (ZMod 3)) × ↥(Subgroup.zpowers x)) ≃* ↥Bs)
    (hΘ : ∀ (w : Fin r → Multiplicative (ZMod 3)) (c : ↥(Subgroup.zpowers x)),
      ((Θ (w, c) : ↥Bs) : G) = cornerFrameVec R w * c) :
    ggAutomizer L Bs = (TypeBDatum.signedAut r 3).map (TypeBDatum.liftBs Θ) := by
  have hAN := cornerFrame_ambientNormalizer R
  refine le_antisymm ?_ ?_
  · intro φ hφ
    obtain ⟨g, hgL, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp hφ
    let g' : ↥L := ⟨g, hgL⟩
    have hgE : g' ∈ Subgroup.normalizer ((Bs.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      mem_normalizer_subgroupOf_of_mem_normalizer hgL hgN
    have hφeq : φ = ggConjAut Bs hgN := by
      refine MulEquiv.ext fun b => Subtype.ext ?_
      rw [hgφ b, ggConjAut_apply]
    have hψ : ggConjAut (Bs.subgroupOf L) hgE ∈
        ggAutomizer (⊤ : Subgroup ↥L) (Bs.subgroupOf L) := by
      refine mem_ggAutomizer_iff.mpr ⟨g', Subgroup.mem_top g', hgE, fun b => ?_⟩
      exact ggConjAut_apply (Bs.subgroupOf L) hgE b
    have hT : ggLin (p := 3) R.coord (ggConjAut (Bs.subgroupOf L) hgE) ∈
        PlaneRaw.signedPermGroup r := by
      rw [← hAN]
      exact Subgroup.mem_map_of_mem _ hψ
    refine Subgroup.mem_map.mpr ⟨MulAut.congr (cornerFrameEquiv R).symm
      (ggConjAut (Bs.subgroupOf L) hgE), mem_signedAut_congr_symm R hT, ?_⟩
    rw [hφeq]
    exact (eq_liftBs_conjAut hxL R Θ hΘ hgE hgN (fun w => funext fun i =>
      (toAdd_congr_symm_apply R _ w i).symm)).symm
  · refine TypeBDatum.map_liftBs_signedSupportedAut_le (p := 3) Θ Finset.univ ?_ ?_
    · intro i _
      exact liftBs_sgnAut_mem_ggAutomizer hx hxL hsplit R Θ hΘ i
    · intro a _ b _ _hab
      exact liftBs_permAut_mem_ggAutomizer hx hxL hsplit R Θ hΘ a b

private theorem cornerFrame_iota_injective {G : Type} [Group G] {Bs : Subgroup G} {x : G}
    {n : ℕ} {Θ : ((Fin (n - 1) → Multiplicative (ZMod 3)) × ↥(Subgroup.zpowers x)) ≃* ↥Bs}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {ι : Fin (n - 1) → Fin n}
    (hι : ∀ k, MulAut.congr eta (TypeBDatum.liftBs Θ (SpCoord.sgnAut k)) =
      SpCoord.sgnAut (ι k)) :
    Function.Injective ι := by
  intro k l hkl
  have h1 : MulAut.congr eta (TypeBDatum.liftBs Θ (SpCoord.sgnAut k)) =
      MulAut.congr eta (TypeBDatum.liftBs Θ (SpCoord.sgnAut l)) := by
    rw [hι k, hι l, hkl]
  have h2 : TypeBDatum.liftBs Θ (SpCoord.sgnAut k) =
      TypeBDatum.liftBs Θ (SpCoord.sgnAut l) := (MulAut.congr eta).injective h1
  by_contra hne
  have hval := congrArg (fun u : MulAut ↥Bs =>
    u (Θ (Pi.mulSingle k (Multiplicative.ofAdd (1 : ZMod 3)), 1))) h2
  rw [TypeBDatum.liftBs_apply, TypeBDatum.liftBs_apply] at hval
  have h5 := congrArg (fun p : ((Fin (n - 1) → Multiplicative (ZMod 3)) ×
    ↥(Subgroup.zpowers x)) => Multiplicative.toAdd (p.1 k)) (Θ.injective hval)
  have hL : Multiplicative.toAdd
      ((SpCoord.sgnAut k (Pi.mulSingle k (Multiplicative.ofAdd (1 : ZMod 3)))) k) = -1 := by
    rw [SpCoord.sgnAut_mulSingle_self, ← Pi.mulSingle_inv, ← ofAdd_neg,
      SpCoord.toAdd_mulSingle, if_pos rfl]
    rfl
  have hR : Multiplicative.toAdd
      ((SpCoord.sgnAut l (Pi.mulSingle k (Multiplicative.ofAdd (1 : ZMod 3)))) k) = 1 := by
    rw [SpCoord.sgnAut_mulSingle_of_ne (i := l) (j := k) hne,
      SpCoord.toAdd_mulSingle, if_pos rfl]
  rw [hL, hR] at h5
  exact (by decide : (-1 : ZMod 3) ≠ 1) h5

private theorem cornerFrame_iota_surjective {n : ℕ} {i0 : Fin n}
    {ι : Fin (n - 1) → Fin n} (hinj : Function.Injective ι)
    (hι0 : ∀ k, ι k ≠ i0) : ∀ i, i ≠ i0 → ∃ k, ι k = i := by
  intro i hi0
  let f : Fin (n - 1) → {j : Fin n // j ≠ i0} := fun k => ⟨ι k, hι0 k⟩
  have hf : Function.Injective f := fun k l hkl => hinj (congrArg Subtype.val hkl)
  have hcard : Fintype.card {j : Fin n // j ≠ i0} = n - 1 := by
    rw [Fintype.card_subtype_compl (fun j : Fin n => j = i0)]
    simp
  obtain ⟨k, hk⟩ := ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hf, by simp [hcard]⟩).2 ⟨i, hi0⟩
  exact ⟨k, congrArg Subtype.val hk⟩

private theorem cornerFrame_sgnAut_inv {G : Type} [Group G] {Bs : Subgroup G} {x : G}
    {n : ℕ} {Θ : ((Fin (n - 1) → Multiplicative (ZMod 3)) × ↥(Subgroup.zpowers x)) ≃* ↥Bs}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {ι : Fin (n - 1) → Fin n}
    (hι : ∀ k, MulAut.congr eta (TypeBDatum.liftBs Θ (SpCoord.sgnAut k)) =
      SpCoord.sgnAut (ι k))
    {aB : ↥Bs} {k : Fin (n - 1)} {s : ZMod 3}
    (hframe : aB = Θ ((Pi.mulSingle k (Multiplicative.ofAdd s) :
      Fin (n - 1) → Multiplicative (ZMod 3)), 1)) :
    SpCoord.sgnAut (ι k) (eta aB) = (eta aB)⁻¹ := by
  have hinv : TypeBDatum.liftBs Θ (SpCoord.sgnAut k) aB = aB⁻¹ := by
    rw [hframe, TypeBDatum.liftBs_apply, SpCoord.sgnAut_mulSingle_self, ← map_inv]
    congr 1
    ext <;> simp
  rw [← hι k]
  change MulAut.congr eta (TypeBDatum.liftBs Θ (SpCoord.sgnAut k)) (eta aB) = _
  rw [congr_apply_tau, hinv, map_inv]

private theorem cornerFrame_coord_off {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {n : ℕ}
    {R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1))}
    {Θ : ((Fin (n - 1) → Multiplicative (ZMod 3)) × ↥(Subgroup.zpowers x)) ≃* ↥Bs}
    (hΘ : ∀ (w : Fin (n - 1) → Multiplicative (ZMod 3)) (c : ↥(Subgroup.zpowers x)),
      ((Θ (w, c) : ↥Bs) : G) = cornerFrameVec R w * c)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {ι : Fin (n - 1) → Fin n}
    (hι : ∀ k, MulAut.congr eta (TypeBDatum.liftBs Θ (SpCoord.sgnAut k)) =
      SpCoord.sgnAut (ι k))
    {a : ↥(Bs.subgroupOf L)} {k : Fin (n - 1)} {s : ZMod 3}
    (hsk : (R.coord (Additive.ofMul a) : PlaneRaw.V (n - 1)) = Pi.single k s) :
    ∀ j, j ≠ ι k →
      eta ⟨((a : ↥L) : G), Subgroup.mem_subgroupOf.mp a.2⟩ j = 1 := by
  set w : Fin (n - 1) → Multiplicative (ZMod 3) :=
    fun j => Multiplicative.ofAdd ((R.coord (Additive.ofMul a) : PlaneRaw.V (n - 1)) j)
    with hwdef
  set aB : ↥Bs := ⟨((a : ↥L) : G), Subgroup.mem_subgroupOf.mp a.2⟩ with haBdef
  have hwc : w = (Pi.mulSingle k (Multiplicative.ofAdd s) :
      Fin (n - 1) → Multiplicative (ZMod 3)) := by
    funext j
    rw [show w j = Multiplicative.ofAdd
      ((R.coord (Additive.ofMul a) : PlaneRaw.V (n - 1)) j) from congrFun hwdef j, hsk]
    by_cases hj : j = k
    · rw [hj, Pi.single_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.single_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj]
      simp
  have hframeVec : cornerFrameVec R w = (aB : G) := by
    rw [hwdef, haBdef]
    exact cornerFrameVec_coord R a
  have hframe : aB = Θ ((Pi.mulSingle k (Multiplicative.ofAdd s) :
      Fin (n - 1) → Multiplicative (ZMod 3)), 1) := by
    apply Subtype.ext
    rw [hΘ, Subgroup.coe_one, mul_one, ← hwc]
    exact hframeVec.symm
  have hsign := cornerFrame_sgnAut_inv hι hframe
  intro j hj
  have h1 := congrArg (fun f : Fin n → Multiplicative (ZMod 3) =>
    Multiplicative.toAdd (f j)) hsign
  rw [SpCoord.sgnAut_apply, Pi.inv_apply, Function.update_of_ne hj, toAdd_inv] at h1
  have hzero : Multiplicative.toAdd (eta aB j) = 0 :=
    SpCoord.coord_eq_zero_of_eq_neg (p := 3) (by norm_num) (by norm_num) h1
  rw [← ofAdd_toAdd (eta aB j), hzero, ofAdd_zero]

private theorem cornerFrame_coord_ne_one {G : Type} [Group G] {Bs L : Subgroup G}
    {n : ℕ}
    {R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1))}
    {a : ↥(Bs.subgroupOf L)} {k : Fin (n - 1)} {s : ZMod 3}
    (hsk : (R.coord (Additive.ofMul a) : PlaneRaw.V (n - 1)) = Pi.single k s)
    (hs : s ≠ 0) : (⟨((a : ↥L) : G), Subgroup.mem_subgroupOf.mp a.2⟩ : ↥Bs) ≠ 1 := by
  intro h1
  apply hs
  set w : Fin (n - 1) → Multiplicative (ZMod 3) :=
    fun j => Multiplicative.ofAdd ((R.coord (Additive.ofMul a) : PlaneRaw.V (n - 1)) j)
    with hwdef
  have hwc : w = (Pi.mulSingle k (Multiplicative.ofAdd s) :
      Fin (n - 1) → Multiplicative (ZMod 3)) := by
    funext j
    rw [show w j = Multiplicative.ofAdd
      ((R.coord (Additive.ofMul a) : PlaneRaw.V (n - 1)) j) from congrFun hwdef j, hsk]
    by_cases hj : j = k
    · rw [hj, Pi.single_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.single_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj]
      simp
  have hframeVec : cornerFrameVec R w = ((⟨((a : ↥L) : G),
      Subgroup.mem_subgroupOf.mp a.2⟩ : ↥Bs) : G) := by
    rw [hwdef]
    exact cornerFrameVec_coord R a
  have h2 : (Pi.mulSingle k (Multiplicative.ofAdd s) :
      Fin (n - 1) → Multiplicative (ZMod 3)) = 1 := by
    refine cornerFrameVec_injective R ?_
    rw [← hwc, hframeVec, h1, map_one, Subgroup.coe_one]
  have h4 := congrFun h2 k
  rw [Pi.mulSingle_eq_same, Pi.one_apply] at h4
  exact Multiplicative.ofAdd.injective (by simpa using h4)

private theorem cornerFrame_coord_exists {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {n : ℕ}
    {R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1))}
    {Θ : ((Fin (n - 1) → Multiplicative (ZMod 3)) × ↥(Subgroup.zpowers x)) ≃* ↥Bs}
    (hΘ : ∀ (w : Fin (n - 1) → Multiplicative (ZMod 3)) (c : ↥(Subgroup.zpowers x)),
      ((Θ (w, c) : ↥Bs) : G) = cornerFrameVec R w * c)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {ι : Fin (n - 1) → Fin n}
    (hι : ∀ k, MulAut.congr eta (TypeBDatum.liftBs Θ (SpCoord.sgnAut k)) =
      SpCoord.sgnAut (ι k))
    {a : ↥(Bs.subgroupOf L)} {k : Fin (n - 1)} {s : ZMod 3}
    (hsk : (R.coord (Additive.ofMul a) : PlaneRaw.V (n - 1)) = Pi.single k s) :
    ∃ t : ZMod 3, (s ≠ 0 → t ≠ 0) ∧
      eta ⟨((a : ↥L) : G), Subgroup.mem_subgroupOf.mp a.2⟩ =
        Pi.mulSingle (ι k) (Multiplicative.ofAdd t) := by
  set aB : ↥Bs := ⟨((a : ↥L) : G), Subgroup.mem_subgroupOf.mp a.2⟩ with haBdef
  have hoff : ∀ j, j ≠ ι k → eta aB j = 1 := by
    have h := cornerFrame_coord_off hΘ hι hsk
    simpa [haBdef] using h
  refine ⟨Multiplicative.toAdd (eta aB (ι k)), ?_, ?_⟩
  · intro hs ht
    have hne : aB ≠ 1 := by
      simpa [haBdef] using cornerFrame_coord_ne_one hsk hs
    apply hne
    apply eta.injective
    rw [map_one]
    funext j
    by_cases hj : j = ι k
    · rw [hj, Pi.one_apply, ← ofAdd_toAdd (eta aB (ι k)), ht, ofAdd_zero]
    · rw [Pi.one_apply]
      exact hoff j hj
  · funext j
    by_cases hj : j = ι k
    · rw [hj, Pi.mulSingle_eq_same]
      exact (ofAdd_toAdd (eta aB (ι k))).symm
    · rw [Pi.mulSingle_eq_of_ne hj]
      exact hoff j hj

private theorem cornerFrame_sign_transfer {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {n : ℕ} (hx : x ∈ Bs) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    {R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1))}
    {Θ : ((Fin (n - 1) → Multiplicative (ZMod 3)) × ↥(Subgroup.zpowers x)) ≃* ↥Bs}
    (hΘ : ∀ (w : Fin (n - 1) → Multiplicative (ZMod 3)) (c : ↥(Subgroup.zpowers x)),
      ((Θ (w, c) : ↥Bs) : G) = cornerFrameVec R w * c)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {ι : Fin (n - 1) → Fin n}
    (hι : ∀ k, MulAut.congr eta (TypeBDatum.liftBs Θ (SpCoord.sgnAut k)) =
      SpCoord.sgnAut (ι k))
    {J' : Subgroup ↥L} {k : Fin (n - 1)}
    (hneg : PlaneRaw.negEquiv (n - 1) k ∈
      (ggAutomizer J' (Bs.subgroupOf L)).map (ggLin (p := 3) R.coord)) :
    SpCoord.sgnAut (ι k) ∈
      (ggAutomizer (J'.map L.subtype) Bs).map (MulAut.congr eta).toMonoidHom := by
  obtain ⟨ψ, hψ, hψT⟩ := Subgroup.mem_map.mp hneg
  obtain ⟨g', hg'J, hgE, hgψ⟩ := mem_ggAutomizer_iff.mp hψ
  have hψeq : ψ = ggConjAut (Bs.subgroupOf L) hgE := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [hgψ b, ggConjAut_apply]
  have hgN : (g' : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    mem_normalizer_of_mem_normalizer_subgroupOf hx hxL hsplit hgE
  have hgJ : (g' : G) ∈ J'.map L.subtype := Subgroup.mem_map_of_mem L.subtype hg'J
  have hmemφ : ggConjAut Bs hgN ∈ ggAutomizer (J'.map L.subtype) Bs :=
    ggConjAut_mem_ggAutomizer hgJ hgN
  have heq : ggConjAut Bs hgN = TypeBDatum.liftBs Θ (SpCoord.sgnAut k) := by
    refine eq_liftBs_conjAut hxL R Θ hΘ hgE hgN (fun w => ?_)
    have hψT' : (ggLin (p := 3) R.coord) ψ = PlaneRaw.negEquiv (n - 1) k := hψT
    rw [← hψeq, hψT']
    exact negEquiv_toAdd_sgnAut R k w
  refine Subgroup.mem_map.mpr ⟨ggConjAut Bs hgN, hmemφ, ?_⟩
  rw [heq]
  exact hι k

theorem exists_eta_frame_of_realization {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    {n : ℕ} (hn : 4 ≤ n) (hBs : CFSG.Open.IsElemAbelian 3 Bs) (hx : x ∈ Bs)
    (hxL : x ∈ Subgroup.centralizer (L : Set G)) (hxL' : Subgroup.zpowers x ⊓ L = ⊥)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0) :
    ∃ ι : Fin (n - 1) → Fin n, Function.Injective ι ∧ (∀ k, ι k ≠ i0) ∧
      (∀ i, i ≠ i0 → ∃ k, ι k = i) ∧
      (∀ (a : ↥(Bs.subgroupOf L)) (k : Fin (n - 1)) (s : ZMod 3),
        (R.coord (Additive.ofMul a) : PlaneRaw.V (n - 1)) = Pi.single k s →
        ∃ t : ZMod 3, (s ≠ 0 → t ≠ 0) ∧
          eta ⟨((a : ↥L) : G), Subgroup.mem_subgroupOf.mp a.2⟩ =
            Pi.mulSingle (ι k) (Multiplicative.ofAdd t)) ∧
      ∀ (J' : Subgroup ↥L) (k : Fin (n - 1)),
        PlaneRaw.negEquiv (n - 1) k ∈
            (ggAutomizer J' (Bs.subgroupOf L)).map (ggLin (p := 3) R.coord) →
          SpCoord.sgnAut (ι k) ∈
            (ggAutomizer (J'.map L.subtype) Bs).map (MulAut.congr eta).toMonoidHom := by
  classical
  obtain ⟨Θ, hΘ⟩ := exists_cornerFrame_prodEquiv hBs hx hxL' hsplit R
  have hc : ggAutomizer L Bs = (TypeBDatum.signedAut (n - 1) 3).map
      (TypeBDatum.liftBs Θ) :=
    ggAutomizer_eq_map_liftBs_corner hx hxL hsplit R Θ hΘ
  have hcoord : ((TypeBDatum.signedAut (n - 1) 3).map (TypeBDatum.liftBs Θ)).map
      (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0 := by
    rw [← hc, hb]
  choose ι hι0 hι using fun k =>
    exists_sgnAut_eq_congr_liftBs (p := 3) (by norm_num) (by norm_num) hn Θ eta i0 hcoord k
  exact ⟨ι, cornerFrame_iota_injective hι, hι0,
    cornerFrame_iota_surjective (cornerFrame_iota_injective hι) hι0,
    fun a k s hsk => cornerFrame_coord_exists hΘ hι hsk,
    fun J' k hneg => cornerFrame_sign_transfer hx hxL hsplit hΘ hι hneg⟩

end CFSG.StandardType

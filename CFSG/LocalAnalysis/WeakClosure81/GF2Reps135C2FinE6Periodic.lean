module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.BinRep
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.OffenderUnits
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Normalizer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.SmithCurtis CFSG.QuasithinUnique.Setup
open CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

structure ModuleCoordinates (W : Type) [CommGroup W] (L : Subgroup (MulAut W)) (k : Type) [Field k]
    (m : ℕ) where
  rep : Representation k ↥L (Fin m → k)
  coord : W ≃* Multiplicative (Fin m → k)
  coord_apply : ∀ (s : ↥L) (w : W),
    coord ((s : MulAut W) w) = Multiplicative.ofAdd (rep s (Multiplicative.toAdd (coord w)))

private noncomputable def binaryRep {W V : Type} [CommGroup W] [AddCommGroup V] [Module (ZMod 2) V]
    (θ : W ≃* Multiplicative V) (L : Subgroup (MulAut W)) : Representation (ZMod 2) ↥L V :=
  (Units.coeHom (Module.End (ZMod 2) V)).comp ((binUnits θ).toMonoidHom.comp L.subtype)

private theorem binaryRep_apply {W V : Type} [CommGroup W] [AddCommGroup V] [Module (ZMod 2) V]
    (θ : W ≃* Multiplicative V) (L : Subgroup (MulAut W)) (s : ↥L) (v : V) :
    binaryRep θ L s v =
      Multiplicative.toAdd (θ ((s : MulAut W) (θ.symm (Multiplicative.ofAdd v)))) :=
  rfl

private theorem binaryRep_isIrreducible {W V : Type} [CommGroup W] [AddCommGroup V]
    [Module (ZMod 2) V] (θ : W ≃* Multiplicative V) (L : Subgroup (MulAut W))
    (hirr : X1.IsIrrOn L) : (binaryRep θ L).IsIrreducible := by
  rw [isIrreducible_iff]
  haveI : Nontrivial W := hirr.1
  have hVnt : Nontrivial V := by
    obtain ⟨x, hx⟩ := exists_ne (1 : W)
    exact ⟨⟨Multiplicative.toAdd (θ x), 0, fun h => hx (θ.injective (by simpa using h))⟩⟩
  refine ⟨hVnt, fun U hU => ?_⟩
  let U₀ : Subgroup W :=
    { carrier := {x | Multiplicative.toAdd (θ x) ∈ U}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        have h1 : Multiplicative.toAdd (θ (x * y)) =
            Multiplicative.toAdd (θ x) + Multiplicative.toAdd (θ y) := by simp
        show Multiplicative.toAdd (θ (x * y)) ∈ U
        rw [h1]; exact U.add_mem hx hy
      inv_mem' := fun {x} hx => by
        have h1 : Multiplicative.toAdd (θ x⁻¹) = - Multiplicative.toAdd (θ x) := by simp
        show Multiplicative.toAdd (θ x⁻¹) ∈ U
        rw [h1]; exact U.neg_mem hx }
  have hU₀inv : ∀ g ∈ L, ∀ u ∈ U₀, g u ∈ U₀ := by
    intro g hg u hu
    have h1 := hU ⟨g, hg⟩ (Multiplicative.toAdd (θ u)) hu
    have he : binaryRep θ L ⟨g, hg⟩ (Multiplicative.toAdd (θ u)) =
        Multiplicative.toAdd (θ (g u)) := by
      rw [binaryRep_apply]
      simp
    show Multiplicative.toAdd (θ (g u)) ∈ U
    rwa [← he]
  rcases hirr.2 U₀ hU₀inv with h0 | h0
  · left
    rw [eq_bot_iff]
    intro w hw
    have hx : θ.symm (Multiplicative.ofAdd w) ∈ U₀ := by
      show Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd w))) ∈ U
      simpa using hw
    rw [h0, Subgroup.mem_bot] at hx
    rw [Submodule.mem_bot]
    have h2 := congrArg (fun x => Multiplicative.toAdd (θ x)) hx
    simpa using h2
  · right
    rw [eq_top_iff]
    intro w _
    have hx : θ.symm (Multiplicative.ofAdd w) ∈ U₀ := by
      rw [h0]; exact Subgroup.mem_top _
    have hx' : Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd w))) ∈ U := hx
    simpa using hx'

private theorem exists_coordinates_of_irreducible
    {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (hρ : ρ.IsIrreducible) (hinj : Function.Injective ρ) :
    ∃ (δ m : ℕ) (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
      (r : Representation k G (Fin m → k)) (e : V ≃+ (Fin m → k)),
      1 ≤ δ ∧ 1 ≤ m ∧ Nat.card k = 2 ^ δ ∧ Nat.card V = 2 ^ (δ * m) ∧
        r.IsIrreducible ∧ Function.Injective r ∧ ∀ g v, e (ρ g v) = r g (e v) := by
  classical
  haveI : Fact ρ.IsIrreducible := ⟨hρ⟩
  have hnt : Nontrivial V := ((isIrreducible_iff ρ).mp hρ).1
  haveI : Nontrivial V := hnt
  have hDchar : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  haveI hDfin : Finite (EndRing ρ) := finite_endRing ρ
  haveI : Fintype (EndRing ρ) := Fintype.ofFinite _
  obtain ⟨δp, -, hδp⟩ := FiniteField.card (EndRing ρ) 2
  let δ : ℕ := (δp : ℕ)
  have hDcard : Nat.card (EndRing ρ) = 2 ^ δ := by
    rw [Nat.card_eq_fintype_card]
    exact hδp
  have hδ : 1 ≤ δ := δp.pos
  haveI : Module.Finite (EndRing ρ) V := Module.Finite.of_finite
  let m : ℕ := Module.finrank (EndRing ρ) V
  let b : Module.Basis (Fin m) (EndRing ρ) V := Module.finBasis (EndRing ρ) V
  have hm1 : 1 ≤ m := Module.finrank_pos
  have hVcard : Nat.card V = 2 ^ (δ * m) := by
    calc Nat.card V = Nat.card (EndRing ρ) ^ Module.finrank (EndRing ρ) V :=
          natCard_eq_pow_finrank (ρ := ρ)
      _ = (2 ^ δ) ^ Module.finrank (EndRing ρ) V := by rw [hDcard]
      _ = 2 ^ (δ * Module.finrank (EndRing ρ) V) := (pow_mul 2 δ _).symm
      _ = 2 ^ (δ * m) := rfl
  let r : Representation (EndRing ρ) G (Fin m → EndRing ρ) := matRepE b (RingHom.id (EndRing ρ))
  have hr_irr : r.IsIrreducible := matRepE_isIrreducible b (RingHom.id (EndRing ρ))
  have hr_inj : Function.Injective r := by
    intro g g' h
    have h1 : (matRep b g).map (RingHom.id (EndRing ρ)) =
        (matRep b g').map (RingHom.id (EndRing ρ)) := Matrix.toLin'.injective h
    have h2 : matRep b g = matRep b g' := by simpa using h1
    have h3 : repD ρ g = repD ρ g' := (LinearMap.toMatrix b b).injective h2
    exact hinj (LinearMap.ext fun w => congrArg (fun φ : Module.End (EndRing ρ) V => φ w) h3)
  let e : V ≃+ (Fin m → EndRing ρ) := b.equivFun.toAddEquiv
  have he : ∀ g v, e (ρ g v) = r g (e v) := by
    intro g v
    have hL : e (ρ g v) = b.repr (ρ g v) := by
      show b.equivFun (ρ g v) = b.repr (ρ g v)
      rw [Module.Basis.equivFun_apply]
    have hR : r g (e v) = (LinearMap.toMatrix b b (repD ρ g)).mulVec (b.repr v) := by
      have h0 : r g (e v) = (matRep b g).mulVec (e v) := by
        show matRepE b (RingHom.id (EndRing ρ)) g (e v) = _
        rw [matRepE_apply]
        simp
      rw [h0]
      have hv : e v = b.repr v := by
        show b.equivFun v = b.repr v
        rw [Module.Basis.equivFun_apply]
      rw [hv]
      rfl
    rw [hL, hR]
    exact (LinearMap.toMatrix_mulVec_repr b b (repD ρ g) v).symm
  exact ⟨δ, m, EndRing ρ, inferInstance, inferInstance, hDchar, r, e, hδ, hm1, hDcard, hVcard,
    hr_irr, hr_inj, he⟩

theorem exists_moduleCoordinates
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L) (hL : L ≠ ⊥) (hirr : X1.IsIrrOn L) :
    ∃ (δ m : ℕ) (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
      (c : ModuleCoordinates W L k m),
      1 ≤ δ ∧ 1 ≤ m ∧ Nat.card k = 2 ^ δ ∧ Nat.card W = 2 ^ (δ * m) ∧
        c.rep.IsIrreducible ∧ Function.Injective c.rep := by
  classical
  obtain ⟨V, _, _, _, ⟨θ⟩⟩ := Layer.Actor.exists_binModel_of_binary (V := W) hW
  haveI : Finite V := Finite.of_equiv W (θ.toEquiv.trans Multiplicative.toAdd)
  have hρirr : (binaryRep θ L).IsIrreducible := binaryRep_isIrreducible θ L hirr
  have hρinj : Function.Injective (binaryRep θ L) := by
    intro s s' h
    apply Subtype.ext
    apply (binUnits θ).injective
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact congrArg (fun φ : Module.End (ZMod 2) V => φ v) h
  obtain ⟨δ, m, k, hk_field, hk_fin, hk_char, r, e, hδ, hm1, hkcard, hVcard, hr_irr, hr_inj,
    he⟩ := exists_coordinates_of_irreducible (binaryRep θ L) hρirr hρinj
  letI : Field k := hk_field
  letI : Finite k := hk_fin
  let coord : W ≃* Multiplicative (Fin m → k) := θ.trans (AddEquiv.toMultiplicative e)
  have hcoord_apply : ∀ (s : ↥L) (w : W),
      coord ((s : MulAut W) w) =
        Multiplicative.ofAdd (r s (Multiplicative.toAdd (coord w))) := by
    intro s w
    have hb : binaryRep θ L s (Multiplicative.toAdd (θ w)) =
        Multiplicative.toAdd (θ ((s : MulAut W) w)) := by
      rw [binaryRep_apply]
      simp
    have h := he s (Multiplicative.toAdd (θ w))
    rw [hb] at h
    have hcw : Multiplicative.toAdd (coord w) = e (Multiplicative.toAdd (θ w)) := rfl
    have hcs : Multiplicative.toAdd (coord ((s : MulAut W) w)) =
        e (Multiplicative.toAdd (θ ((s : MulAut W) w))) := rfl
    rw [← hcs, ← hcw] at h
    exact congrArg Multiplicative.ofAdd h
  let c : ModuleCoordinates W L k m := { rep := r, coord := coord, coord_apply := hcoord_apply }
  refine ⟨δ, m, k, hk_field, hk_fin, hk_char, c, hδ, hm1, hkcard, ?_, ?_, ?_⟩
  · rw [Layer.Actor.natCard_eq θ, hVcard]
  · exact hr_irr
  · exact hr_inj

theorem natCard_fixV_map_subtype
    {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {k : Type} [Field k] [Finite k]
    {m : ℕ} (c : ModuleCoordinates W L k m) (A : Subgroup ↥L) :
    Nat.card ↥(fixV (A.map L.subtype)) =
      Nat.card k ^ Module.finrank k ↥(fixSub c.rep A) := by
  classical
  let e : W ≃ (Fin m → k) := c.coord.toEquiv.trans Multiplicative.toAdd
  have hmem : ∀ w, w ∈ fixV (A.map L.subtype) ↔ e w ∈ fixSub c.rep A := by
    intro w
    rw [mem_fixV, mem_fixSub]
    constructor
    · intro h a ha
      have hx : (a : MulAut W) ∈ A.map L.subtype := Subgroup.mem_map.2 ⟨a, ha, rfl⟩
      have haw : (a : MulAut W) w = w := h _ hx
      have h1 := congrArg Multiplicative.toAdd (c.coord_apply a w)
      rw [haw] at h1
      exact h1.symm
    · intro h x hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
      apply c.coord.injective
      change c.coord ((a : MulAut W) w) = c.coord w
      rw [c.coord_apply a w]
      rw [show c.rep a (Multiplicative.toAdd (c.coord w)) =
          Multiplicative.toAdd (c.coord w) from h a ha]
      simp
  have hcard : Nat.card ↥(fixV (A.map L.subtype)) = Nat.card ↥(fixSub c.rep A) :=
    Nat.card_congr (Equiv.subtypeEquiv e hmem)
  rw [hcard]
  exact Module.natCard_eq_pow_finrank

theorem exists_intertwiner_of_card_eq_two
    {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {k : Type} [Field k] [Finite k]
    {m : ℕ} (c : ModuleCoordinates W L k m) (hk : Nat.card k = 2) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    ∃ B : Module.End k (Fin m → k), IsUnit B ∧
      ∀ s : ↥L, B * c.rep s = c.rep (X1.conjAut L hb s) * B := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  have hcases : ∀ x : k, x = 0 ∨ x = 1 := by
    have hx2 : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card]; exact hk
    have h01 : (0 : k) ≠ 1 := zero_ne_one
    intro x
    have hpair : ({0, 1} : Finset k) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_insert_of_notMem (by simp [h01]), Finset.card_singleton]
      exact hx2.symm
    have hxmem : x ∈ ({0, 1} : Finset k) := by rw [hpair]; exact Finset.mem_univ x
    simpa using hxmem
  let ψ : (Fin m → k) ≃ (Fin m → k) :=
    Multiplicative.ofAdd.trans (c.coord.symm.toEquiv.trans
      (b.toEquiv.trans (c.coord.toEquiv.trans Multiplicative.toAdd)))
  have hψ : ∀ v, ψ v = Multiplicative.toAdd
      (c.coord (b (c.coord.symm (Multiplicative.ofAdd v)))) := fun v => rfl
  let B : Module.End k (Fin m → k) :=
    { toFun := ψ
      map_add' := by
        intro v w
        simp only [hψ, ofAdd_add, map_mul, toAdd_mul]
      map_smul' := by
        intro x v
        rcases hcases x with rfl | rfl <;> simp [hψ] }
  have hBunit : IsUnit B := (Module.End.isUnit_iff B).2 (by simpa [B] using ψ.bijective)
  refine ⟨B, hBunit, fun s => ?_⟩
  apply LinearMap.ext
  intro v
  change B (c.rep s v) = c.rep (X1.conjAut L hb s) (B v)
  let w : W := c.coord.symm (Multiplicative.ofAdd v)
  have hw : c.coord w = Multiplicative.ofAdd v := c.coord.apply_symm_apply _
  have hv : Multiplicative.toAdd (c.coord w) = v := by rw [hw]; rfl
  have hBapply : ∀ x : Fin m → k, B x =
      Multiplicative.toAdd (c.coord (b (c.coord.symm (Multiplicative.ofAdd x)))) :=
    fun x => rfl
  have hs : c.rep s v = Multiplicative.toAdd (c.coord ((s : MulAut W) w)) := by
    have h := c.coord_apply s w
    rw [hv] at h
    exact (congrArg Multiplicative.toAdd h).symm
  have h1 : B (c.rep s v) = Multiplicative.toAdd (c.coord (b ((s : MulAut W) w))) := by
    rw [hs, hBapply]
    simp
  have h2 : B v = Multiplicative.toAdd (c.coord (b w)) := by
    rw [hBapply, ← hw]
    simp
  have hconj : (X1.conjAut L hb s : MulAut W) (b w) = b ((s : MulAut W) w) := by
    rw [X1.coe_conjAut]
    simp
  have h3 : c.rep (X1.conjAut L hb s) (B v) =
      Multiplicative.toAdd (c.coord (b ((s : MulAut W) w))) := by
    rw [h2]
    have h := c.coord_apply (X1.conjAut L hb s) (b w)
    rw [hconj] at h
    exact (congrArg Multiplicative.toAdd h).symm
  rw [h1, h3]

end CFSG.LocalAnalysis.WeakClosure81

module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover78Aux1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover78Aux2
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover78Aux4

public section

namespace CFSG.StandardType.RCKRP

variable {CoeffField : Type} [Field CoeffField] [IsAlgClosed CoeffField] [CharP CoeffField 2]
attribute [local instance] ZMod.algebra


open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Adjoint

noncomputable def rckTw78_e (h : ℕ) (hh : 0 < h) :
    GaloisField 2 (2 * h) ≃+* K2 CoeffField 2 h := by
  haveI : Finite (K2 CoeffField 2 h) :=
    finite_frobeniusFixedField (L := CoeffField) (ℓ := 2) (m := 2 * h) (by omega)
  have hcard : Nat.card (K2 CoeffField 2 h) = 2 ^ (2 * h) :=
    card_K2 (L := CoeffField) (ℓ := 2) (f := h) (by omega)
  exact (CFSG.ClassicalModels.finiteFieldEquivGaloisField (K2 CoeffField 2 h) 2 (2 * h) (by omega)
    hcard).symm

theorem rckTw78_e_theta (h : ℕ) (hh : 0 < h)
    (x : GaloisField 2 (2 * h)) :
    theta2 CoeffField 2 h (rckTw78_e (CoeffField := CoeffField) h hh x) = rckTw78_e (CoeffField := CoeffField) h hh (frobQ 2 h x) := by
  apply Subtype.ext
  simp only [theta2, frobQ, iterateFrobenius_def, map_pow]

theorem rckTw78_twistedE6Equiv_apply
    (h : ℕ) (hh : 0 < h) (x : twistedE6Group 2 h) :
    rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh x =
      (MulEquiv.subgroupCongr (rckTw78_fixedGroup_map (rckTw78_e (CoeffField := CoeffField) h hh) (frobQ 2 h)
        (theta2 CoeffField 2 h) (rckTw78_e_theta (CoeffField := CoeffField) h hh)))
        (((rckTw78_Tmin (rckTw78_e (CoeffField := CoeffField) h hh) e6Data e6Data_valid).subgroupMap
          (fixedGroup (GaloisField 2 (2 * h)) (frobQ 2 h))) x) := by
  unfold rckTw78_twistedE6Equiv
  rfl

theorem rckTw78_twistedE6Equiv_xFixed
    (h : ℕ) (hh : 0 < h) {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    (hfix : rho α = α) (c : GaloisField 2 (2 * h)) (hc : frobQ 2 h c = c) :
    ((rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh (xFixed (frobQ 2 h) hα hfix c hc) :
        fixedGroup (K2 CoeffField 2 h) (theta2 CoeffField 2 h)).1 :
      e6Data_valid.minGroup (K2 CoeffField 2 h)) =
      e6Data_valid.xm (K2 CoeffField 2 h) α (rckTw78_e (CoeffField := CoeffField) h hh c) := by
  rw [rckTw78_twistedE6Equiv_apply]
  change ((rckTw78_Tmin (rckTw78_e (CoeffField := CoeffField) h hh) e6Data e6Data_valid)
      (xFixed (frobQ 2 h) hα hfix c hc :
        fixedGroup (GaloisField 2 (2 * h)) (frobQ 2 h)) :
      e6Data_valid.minGroup (K2 CoeffField 2 h)) =
    e6Data_valid.xm (K2 CoeffField 2 h) α (rckTw78_e (CoeffField := CoeffField) h hh c)
  apply Subtype.ext
  rw [rckTw78_Tmin_coe]
  change rckTw78_endUnitMap (rckTw78_e (CoeffField := CoeffField) h hh) e6Data.d
      (e6Data_valid.xu (GaloisField 2 (2 * h)) α c) =
    e6Data_valid.xu (K2 CoeffField 2 h) α (rckTw78_e (CoeffField := CoeffField) h hh c)
  rw [rckTw78_endUnitMap_xu]

theorem rckTw78_psi2_T_xFixed_pos
    {τ : Tag} [M27Ok τ] [E6Sub τ]
    (h : ℕ) (hh : 0 < h) (hα : IsRoot .E6 (Pi.single (1 : Fin Tag.E6.rank) 1))
    (hfix : rho (Pi.single (1 : Fin Tag.E6.rank) 1) = Pi.single 1 1)
    (c : GaloisField 2 (2 * h)) (hc : frobQ 2 h c = c) :
    psi2 τ CoeffField 2 h (rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh
        (xFixed (frobQ 2 h) hα hfix c hc)) =
      pinnedX τ CoeffField (Pi.single (e6Idx 1) 1) ((rckTw78_e (CoeffField := CoeffField) h hh c : K2 CoeffField 2 h) : CoeffField) := by
  rw [psi2_apply]
  have hxm := rckTw78_twistedE6Equiv_xFixed (CoeffField := CoeffField) h hh hα hfix c hc
  have hsymm : (m27Equiv τ (K2 CoeffField 2 h)).symm
      (e6Data_valid.xm (K2 CoeffField 2 h) (Pi.single (1 : Fin Tag.E6.rank) 1) (rckTw78_e (CoeffField := CoeffField) h hh c)) =
      ⟨xUnit τ (K2 CoeffField 2 h) (e6Idx 1) (rckTw78_e (CoeffField := CoeffField) h hh c),
        xUnit_mem_subsystemGroup (e6Idx_mem_e6Set (τ := τ) 1) _⟩ := by
    apply (m27Equiv τ (K2 CoeffField 2 h)).injective
    rw [MulEquiv.apply_symm_apply, m27Equiv_apply, m27ResMin_xUnit]
  rw [hxm, hsymm]
  change baseChangeGL (frobeniusFixedField CoeffField 2 (2 * h)).subtype
      (xUnit τ (K2 CoeffField 2 h) (e6Idx 1) (rckTw78_e (CoeffField := CoeffField) h hh c)) =
    pinnedX τ CoeffField (Pi.single (e6Idx 1) 1) ((rckTw78_e (CoeffField := CoeffField) h hh c : K2 CoeffField 2 h) : CoeffField)
  rw [← pinnedX_single (τ := τ) (R := K2 CoeffField 2 h) (e6Idx 1) (rckTw78_e (CoeffField := CoeffField) h hh c)]
  rw [baseChangeGL_pinnedX]
  rfl

theorem rckTw78_psi2_T_xFixed_neg
    {τ : Tag} [M27Ok τ] [E6Sub τ]
    (h : ℕ) (hh : 0 < h) (hα : IsRoot .E6 (-Pi.single (1 : Fin Tag.E6.rank) 1))
    (hfix : rho (-Pi.single (1 : Fin Tag.E6.rank) 1) = -Pi.single 1 1)
    (c : GaloisField 2 (2 * h)) (hc : frobQ 2 h c = c) :
    psi2 τ CoeffField 2 h (rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh
        (xFixed (frobQ 2 h) hα hfix c hc)) =
      pinnedX τ CoeffField (-Pi.single (e6Idx 1) 1) ((rckTw78_e (CoeffField := CoeffField) h hh c : K2 CoeffField 2 h) : CoeffField) := by
  rw [psi2_apply]
  have hxm := rckTw78_twistedE6Equiv_xFixed (CoeffField := CoeffField) h hh hα hfix c hc
  have hsymm : (m27Equiv τ (K2 CoeffField 2 h)).symm
      (e6Data_valid.xm (K2 CoeffField 2 h) (-Pi.single (1 : Fin Tag.E6.rank) 1) (rckTw78_e (CoeffField := CoeffField) h hh c)) =
      ⟨yUnit τ (K2 CoeffField 2 h) (e6Idx 1) (rckTw78_e (CoeffField := CoeffField) h hh c),
        yUnit_mem_subsystemGroup (e6Idx_mem_e6Set (τ := τ) 1) _⟩ := by
    apply (m27Equiv τ (K2 CoeffField 2 h)).injective
    rw [MulEquiv.apply_symm_apply, m27Equiv_apply, m27ResMin_yUnit]
  rw [hxm, hsymm]
  change baseChangeGL (frobeniusFixedField CoeffField 2 (2 * h)).subtype
      (yUnit τ (K2 CoeffField 2 h) (e6Idx 1) (rckTw78_e (CoeffField := CoeffField) h hh c)) =
    pinnedX τ CoeffField (-Pi.single (e6Idx 1) 1) ((rckTw78_e (CoeffField := CoeffField) h hh c : K2 CoeffField 2 h) : CoeffField)
  rw [← pinnedX_neg_single (τ := τ) (R := K2 CoeffField 2 h) (e6Idx 1) (rckTw78_e (CoeffField := CoeffField) h hh c)]
  rw [baseChangeGL_pinnedX]
  rfl

section PinSource

open CFSG.LieType.Steinberg.TwistedE6

theorem rckTw78_pin_source_pos
    {τ : Tag} [M27Ok τ] [E6Sub τ]
    (h : ℕ) (hh : 0 < h) (σ : CoeffField ≃+* CoeffField)
    (hσ : σ.toRingHom = iterateFrobenius CoeffField 2 h) :
    ((twistedRootGroup (GaloisField 2 (2 * h)) (frobQ 2 h)
        (Pi.single (0 : Fin (Tag.rank .F4)) 1)).map
      ((psi2 τ CoeffField 2 h).comp (rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh).toMonoidHom)) =
      (rootSubgroup τ ↥(fixSubfield σ) (Pi.single (e6Idx 1) 1)).map
        (baseChangeGL (fixSubfield σ).subtype) := by
  have hα : IsRoot .E6 (Pi.single (1 : Fin Tag.E6.rank) 1) := isRoot_single .E6 1
  have hfix : rho (Pi.single (1 : Fin Tag.E6.rank) 1) = Pi.single 1 1 := by
    rw [rho_single, rhoPerm_eq_rho6]; rfl
  have hproj : proj (Pi.single (1 : Fin Tag.E6.rank) 1) =
      Pi.single (0 : Fin (Tag.rank .F4)) 1 := by decide
  have hσc : ∀ x : CoeffField, σ x = x ^ 2 ^ h := by
    intro x
    have h1 : σ.toRingHom x = (iterateFrobenius CoeffField 2 h) x := by rw [hσ]
    rw [iterateFrobenius_def] at h1
    exact h1
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hxm⟩ := (mem_twistedRootGroup_iff_of_fixed (frobQ 2 h) hα hproj hfix x).1 hx
    have hxeq : x = xFixed (frobQ 2 h) hα hfix c hc := Subtype.ext hxm
    rw [hxeq]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [rckTw78_psi2_T_xFixed_pos (τ := τ) h hh hα hfix c hc]
    have hd0 : ((rckTw78_e (CoeffField := CoeffField) h hh c : K2 CoeffField 2 h) : CoeffField) ∈ fixSubfield σ := by
      have h2 : theta2 CoeffField 2 h (rckTw78_e (CoeffField := CoeffField) h hh c) = rckTw78_e (CoeffField := CoeffField) h hh c := by
        rw [rckTw78_e_theta, hc]
      have h3 := congrArg Subtype.val h2
      rw [theta2_apply] at h3
      rw [mem_fixSubfield, hσc]
      exact h3
    refine Subgroup.mem_map.2 ⟨pinnedX τ ↥(fixSubfield σ) (Pi.single (e6Idx 1) 1)
      ⟨((rckTw78_e (CoeffField := CoeffField) h hh c : K2 CoeffField 2 h) : CoeffField), hd0⟩, ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨_, rfl⟩
    · rw [baseChangeGL_pinnedX]
      rfl
  · rw [rootSubgroup, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨x, ⟨c, rfl⟩, rfl⟩
    have hcG : (c : CoeffField) ^ 2 ^ h = (c : CoeffField) := by
      have h := (mem_fixSubfield σ).1 c.2
      rw [hσc] at h
      exact h
    have hcK : (c : CoeffField) ^ 2 ^ (2 * h) = (c : CoeffField) := by
      rw [show (2 : ℕ) ^ (2 * h) = 2 ^ h * 2 ^ h by rw [← pow_add]; ring, pow_mul, hcG, hcG]
    let c' : K2 CoeffField 2 h := ⟨(c : CoeffField), by rw [mem_frobeniusFixedField]; exact hcK⟩
    have hc'θ : theta2 CoeffField 2 h c' = c' := by
      apply Subtype.ext
      rw [theta2_apply]
      exact hcG
    let c0 : GaloisField 2 (2 * h) := (rckTw78_e (CoeffField := CoeffField) h hh).symm c'
    have hEc0 : rckTw78_e (CoeffField := CoeffField) h hh c0 = c' := (rckTw78_e (CoeffField := CoeffField) h hh).apply_symm_apply c'
    have hc0 : frobQ 2 h c0 = c0 := by
      apply (rckTw78_e (CoeffField := CoeffField) h hh).injective
      rw [← rckTw78_e_theta (CoeffField := CoeffField), hEc0]
      exact hc'θ
    refine Subgroup.mem_map.2 ⟨xFixed (frobQ 2 h) hα hfix c0 hc0, ?_, ?_⟩
    · exact (mem_twistedRootGroup_iff_of_fixed (frobQ 2 h) hα hproj hfix _).2 ⟨c0, hc0, rfl⟩
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [rckTw78_psi2_T_xFixed_pos (τ := τ) h hh hα hfix c0 hc0]
      rw [hEc0]
      rw [show ((c' : K2 CoeffField 2 h) : CoeffField) = (c : CoeffField) from rfl]
      exact (baseChangeGL_pinnedX (fixSubfield σ).subtype (Pi.single (e6Idx 1) 1) c).symm

theorem rckTw78_pin_source_neg
    {τ : Tag} [M27Ok τ] [E6Sub τ]
    (h : ℕ) (hh : 0 < h) (σ : CoeffField ≃+* CoeffField)
    (hσ : σ.toRingHom = iterateFrobenius CoeffField 2 h) :
    ((twistedRootGroup (GaloisField 2 (2 * h)) (frobQ 2 h)
        (-Pi.single (0 : Fin (Tag.rank .F4)) 1)).map
      ((psi2 τ CoeffField 2 h).comp (rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh).toMonoidHom)) =
      (rootSubgroup τ ↥(fixSubfield σ) (-Pi.single (e6Idx 1) 1)).map
        (baseChangeGL (fixSubfield σ).subtype) := by
  have hα : IsRoot .E6 (-Pi.single (1 : Fin Tag.E6.rank) 1) :=
    IsRoot.neg (isRoot_single .E6 1)
  have hfix : rho (-Pi.single (1 : Fin Tag.E6.rank) 1) = -Pi.single 1 1 := by
    rw [rho_neg_single, rhoPerm_eq_rho6]; rfl
  have hproj : proj (-Pi.single (1 : Fin Tag.E6.rank) 1) =
      -Pi.single (0 : Fin (Tag.rank .F4)) 1 := by
    rw [map_neg]; exact congrArg Neg.neg (by decide :
      proj (Pi.single (1 : Fin Tag.E6.rank) 1) = Pi.single (0 : Fin (Tag.rank .F4)) 1)
  have hσc : ∀ x : CoeffField, σ x = x ^ 2 ^ h := by
    intro x
    have h1 : σ.toRingHom x = (iterateFrobenius CoeffField 2 h) x := by rw [hσ]
    rw [iterateFrobenius_def] at h1
    exact h1
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hxm⟩ := (mem_twistedRootGroup_iff_of_fixed (frobQ 2 h) hα hproj hfix x).1 hx
    have hxeq : x = xFixed (frobQ 2 h) hα hfix c hc := Subtype.ext hxm
    rw [hxeq]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [rckTw78_psi2_T_xFixed_neg (τ := τ) h hh hα hfix c hc]
    have hd0 : ((rckTw78_e (CoeffField := CoeffField) h hh c : K2 CoeffField 2 h) : CoeffField) ∈ fixSubfield σ := by
      have h2 : theta2 CoeffField 2 h (rckTw78_e (CoeffField := CoeffField) h hh c) = rckTw78_e (CoeffField := CoeffField) h hh c := by
        rw [rckTw78_e_theta, hc]
      have h3 := congrArg Subtype.val h2
      rw [theta2_apply] at h3
      rw [mem_fixSubfield, hσc]
      exact h3
    refine Subgroup.mem_map.2 ⟨pinnedX τ ↥(fixSubfield σ) (-Pi.single (e6Idx 1) 1)
      ⟨((rckTw78_e (CoeffField := CoeffField) h hh c : K2 CoeffField 2 h) : CoeffField), hd0⟩, ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨_, rfl⟩
    · rw [baseChangeGL_pinnedX]
      rfl
  · rw [rootSubgroup, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨x, ⟨c, rfl⟩, rfl⟩
    have hcG : (c : CoeffField) ^ 2 ^ h = (c : CoeffField) := by
      have h := (mem_fixSubfield σ).1 c.2
      rw [hσc] at h
      exact h
    have hcK : (c : CoeffField) ^ 2 ^ (2 * h) = (c : CoeffField) := by
      rw [show (2 : ℕ) ^ (2 * h) = 2 ^ h * 2 ^ h by rw [← pow_add]; ring, pow_mul, hcG, hcG]
    let c' : K2 CoeffField 2 h := ⟨(c : CoeffField), by rw [mem_frobeniusFixedField]; exact hcK⟩
    have hc'θ : theta2 CoeffField 2 h c' = c' := by
      apply Subtype.ext
      rw [theta2_apply]
      exact hcG
    let c0 : GaloisField 2 (2 * h) := (rckTw78_e (CoeffField := CoeffField) h hh).symm c'
    have hEc0 : rckTw78_e (CoeffField := CoeffField) h hh c0 = c' := (rckTw78_e (CoeffField := CoeffField) h hh).apply_symm_apply c'
    have hc0 : frobQ 2 h c0 = c0 := by
      apply (rckTw78_e (CoeffField := CoeffField) h hh).injective
      rw [← rckTw78_e_theta (CoeffField := CoeffField), hEc0]
      exact hc'θ
    refine Subgroup.mem_map.2 ⟨xFixed (frobQ 2 h) hα hfix c0 hc0, ?_, ?_⟩
    · exact (mem_twistedRootGroup_iff_of_fixed (frobQ 2 h) hα hproj hfix _).2 ⟨c0, hc0, rfl⟩
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [rckTw78_psi2_T_xFixed_neg (τ := τ) h hh hα hfix c0 hc0]
      rw [hEc0]
      rw [show ((c' : K2 CoeffField 2 h) : CoeffField) = (c : CoeffField) from rfl]
      exact (baseChangeGL_pinnedX (fixSubfield σ).subtype (-Pi.single (e6Idx 1) 1) c).symm

omit [IsAlgClosed CoeffField] [CharP CoeffField 2] in
theorem rckTw78_pin_assemble
    {τ : Tag} {h : ℕ} (X : Subgroup (twistedE6Group 2 h))
    (ψ : twistedE6Group 2 h →* ModGL τ CoeffField) (R R' : Subgroup (ModGL τ CoeffField))
    (nv hL z : ModGL τ CoeffField) (φ : twistedE6Group 2 h →* ModGL τ CoeffField)
    (hφ : φ = (MulAut.conj (nv * hL⁻¹)).toMonoidHom.comp ψ) (hz : z = nv * hL⁻¹ * nv⁻¹)
    (hsrc : X.map ψ = R) (hconj : R'.map (MulAut.conj nv⁻¹).toMonoidHom = R) :
    X.map φ = R'.map (MulAut.conj z).toMonoidHom := by
  subst hφ hz
  rw [← Subgroup.map_map, hsrc, ← hconj, Subgroup.map_map]
  congr 1

theorem rckTw78_pin_core
    {τ : Tag} [M27Ok τ] [E6Sub τ]
    (h : ℕ) (hh : 0 < h) (σ : CoeffField ≃+* CoeffField)
    (hσ : σ.toRingHom = iterateFrobenius CoeffField 2 h)
    (v : WeylGroup τ) (nv hL : ModGL τ CoeffField)
    (φ : twistedE6Group 2 h →* ModGL τ CoeffField) (z : ModGL τ CoeffField)
    (hnv : nv = canonicalRep (coxeterSystem τ) CoeffField v)
    (hz : z = nv * hL⁻¹ * nv⁻¹)
    (hφ : φ = (MulAut.conj (nv * hL⁻¹)).toMonoidHom.comp
      ((psi2 τ CoeffField 2 h).comp (rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh).toMonoidHom)) :
    ((twistedRootGroup (GaloisField 2 (2 * h)) (frobQ 2 h)
        (Pi.single (0 : Fin (Tag.rank .F4)) 1)).map φ) =
      ((rootSubgroup τ ↥(fixSubfield σ) (v • Pi.single (e6Idx 1) 1)).map
        (baseChangeGL (fixSubfield σ).subtype)).map (MulAut.conj z).toMonoidHom := by
  subst hnv
  exact rckTw78_pin_assemble _ ((psi2 τ CoeffField 2 h).comp (rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh).toMonoidHom) _ _
    _ hL z φ hφ hz (rckTw78_pin_source_pos h hh σ hσ)
    (rckTw78_pin_conj v _ (isRoot_single τ (e6Idx 1)) σ)

theorem rckTw78_pin_core_neg
    {τ : Tag} [M27Ok τ] [E6Sub τ]
    (h : ℕ) (hh : 0 < h) (σ : CoeffField ≃+* CoeffField)
    (hσ : σ.toRingHom = iterateFrobenius CoeffField 2 h)
    (v : WeylGroup τ) (nv hL : ModGL τ CoeffField)
    (φ : twistedE6Group 2 h →* ModGL τ CoeffField) (z : ModGL τ CoeffField)
    (hnv : nv = canonicalRep (coxeterSystem τ) CoeffField v)
    (hz : z = nv * hL⁻¹ * nv⁻¹)
    (hφ : φ = (MulAut.conj (nv * hL⁻¹)).toMonoidHom.comp
      ((psi2 τ CoeffField 2 h).comp (rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh).toMonoidHom)) :
    ((twistedRootGroup (GaloisField 2 (2 * h)) (frobQ 2 h)
        (-Pi.single (0 : Fin (Tag.rank .F4)) 1)).map φ) =
      ((rootSubgroup τ ↥(fixSubfield σ) (v • -Pi.single (e6Idx 1) 1)).map
        (baseChangeGL (fixSubfield σ).subtype)).map (MulAut.conj z).toMonoidHom := by
  subst hnv
  exact rckTw78_pin_assemble _ ((psi2 τ CoeffField 2 h).comp (rckTw78_twistedE6Equiv (CoeffField := CoeffField) h hh).toMonoidHom) _ _
    _ hL z φ hφ hz (rckTw78_pin_source_neg h hh σ hσ)
    (rckTw78_pin_conj v _ (IsRoot.neg (isRoot_single τ (e6Idx 1))) σ)

end PinSource

end CFSG.StandardType.RCKRP

end

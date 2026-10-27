module

public import CFSG.Quasithin.H13.L32A756e

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.H13.Orbit
open scoped commutatorElement

namespace M755

@[expose] noncomputable def ptO (c : ℕ) : ModO := codeO (o0c c)

theorem ptO_eq_codeO {c : ℕ} (hc : c ∈ o0Codes) : ptO c = codeO ⟨c, hc⟩ := by
  simp [ptO, o0c, hc]

theorem g2OAct_ptO (g : ↥(quasithinG2 (ZMod 2))) {c : ℕ} (hc : c ∈ o0Codes) :
    g2OAct (ZMod 2) g (ptO c) = ptO (mact (matCode g.1) c) := by
  rw [ptO_eq_codeO hc, g2OAct_codeO, ptO_eq_codeO (mact_mem_o0Codes g.2 hc)]
  rfl

theorem ptO_mul {c d : ℕ} (hc : c ∈ o0Codes) (hd : d ∈ o0Codes) :
    ptO c * ptO d = ptO (c ^^^ d) := by
  rw [ptO_eq_codeO hc, ptO_eq_codeO hd, ptO_eq_codeO (xor_mem_o0Codes hc hd), ← codeO_xor]
  rfl

theorem ptO_inv (c : ℕ) : (ptO c)⁻¹ = ptO c := codeO_inv _

@[expose] noncomputable def projOQ : ModO →* ModQ :=
  QuotientGroup.map _ _ (MonoidHom.id _) fun x hx => by
    have h1 : x.1 = 1 := Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 hx)
    have h2 : x = 1 := Subtype.ext h1
    rw [h2]
    exact Subgroup.one_mem _

theorem projOQ_codeO (c : O0C) : projOQ (codeO c) = codeQ c := rfl

theorem projOQ_ptO (c : ℕ) : projOQ (ptO c) = ptQ c := rfl

theorem projOQ_act (g : ↥(quasithinG2 (ZMod 2))) (y : ModO) :
    projOQ (g2OAct (ZMod 2) g y) = g2QAct (ZMod 2) g (projOQ y) := by
  obtain ⟨c, rfl⟩ := codeO_surjective y
  rw [g2OAct_codeO, projOQ_codeO, projOQ_codeO, g2QAct_codeQ]

theorem projOQ_surjective : Function.Surjective projOQ := fun q => by
  obtain ⟨c, rfl⟩ := codeQ_surjective q
  exact ⟨codeO c, rfl⟩

theorem projOQ_eq_one_iff (y : ModO) : projOQ y = 1 ↔ y = 1 ∨ y = ptO 129 := by
  obtain ⟨c, rfl⟩ := codeO_surjective y
  have h129 : (129 : ℕ) ∈ o0Codes := by decide
  rw [projOQ_codeO, ← codeQ_zero, codeQ_eq_iff, ptO_eq_codeO h129, ← codeO_zero,
    codeO_injective.eq_iff, codeO_injective.eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h.symm)
    · refine Or.inr (Subtype.ext ?_)
      have h' : c.1 ^^^ 129 = 0 := h.symm
      rw [xor_eq_iff, Nat.xor_zero] at h'
      exact h'.symm
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Nat.xor_self 129).symm

theorem ptO_129_mem : ptO 129 ∈ fixV ((g2Derived (ZMod 2)).map (g2OAct (ZMod 2))) := by
  have h129 : (129 : ℕ) ∈ o0Codes := by decide
  rintro _ ⟨γ, -, rfl⟩
  rw [ptO_eq_codeO h129, g2OAct_codeO]
  congr 1
  apply o0Elt_injective
  apply Subtype.ext
  rw [o0Elt_act]
  change Multiplicative.ofAdd (γ.1 (decodeZ 129)) = Multiplicative.ofAdd (decodeZ 129)
  rw [decodeZ_129, (mem_quasithinG2_isZornAuto γ.2).map_one]

theorem ptO_129_ne : ptO 129 ≠ 1 := by
  have h129 : (129 : ℕ) ∈ o0Codes := by decide
  rw [ptO_eq_codeO h129, ← codeO_zero]
  intro h1
  have h2 : (129 : ℕ) = 0 := congrArg Subtype.val (codeO_injective h1)
  omega

end M755

namespace Ctx753

variable {G : Type} [Group G] [Finite G] {T L V K : Subgroup G}

@[expose] noncomputable def rhoO (C : Ctx753 T L V K)
    (ψ : ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))) ≃* ModO) :
    ↥(hz T V) →* MulAut ModO :=
  (MulAut.congr ψ).toMonoidHom.comp
    ((autIH (fsuV1 T V) V (hz T V) (hz T V)).subtype.comp C.actHX)

theorem rhoO_mem_range
    (C : Ctx753 T L V K)
    {ψ : ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))) ≃* ModO}
    (hψ : (autIH (fsuV1 T V) V (hz T V) K).map (MulAut.congr ψ).toMonoidHom =
      (g2Derived (ZMod 2)).map (g2OAct (ZMod 2))) (h : ↥(hz T V)) :
    C.rhoO ψ h ∈ (g2OAct (ZMod 2)).range := by
  have hφinj : Function.Injective (MulAut.congr ψ).toMonoidHom := (MulAut.congr ψ).injective
  have hx : ∀ l, l ∈ autIH (fsuV1 T V) V (hz T V) K ↔
      (C.actHX h : MulAut _) * l * (C.actHX h : MulAut _)⁻¹ ∈ autIH (fsuV1 T V) V (hz T V) K :=
    fun l => Subgroup.mem_normalizer_iff.mp (C.autH_le_normalizer (C.actHX h).2) l
  refine normalizer_two_O _ fun d => ?_
  obtain ⟨l, rfl⟩ := (MulAut.congr ψ).surjective d
  rw [← hψ]
  change (MulAut.congr ψ).toMonoidHom l ∈
      (autIH (fsuV1 T V) V (hz T V) K).map (MulAut.congr ψ).toMonoidHom ↔
    (MulAut.congr ψ).toMonoidHom (C.actHX h : MulAut _) * (MulAut.congr ψ).toMonoidHom l *
      ((MulAut.congr ψ).toMonoidHom (C.actHX h : MulAut _))⁻¹ ∈
        (autIH (fsuV1 T V) V (hz T V) K).map (MulAut.congr ψ).toMonoidHom
  rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hφinj,
    Subgroup.mem_map_iff_mem hφinj]
  exact hx l

theorem actHX_mem_K (C : Ctx753 T L V K) {k : G} (hk : k ∈ K) :
    (C.actHX ⟨k, C.le_hz hk⟩ : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V)))) ∈
      autIH (fsuV1 T V) V (hz T V) K := by
  rw [C.actHX_coe, autIH_eq_map C.f918 C.le_hz]
  exact ⟨⟨k, C.le_hz hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩

@[expose] noncomputable def ΦO
    (C : Ctx753 T L V K)
    {ψ : ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))) ≃* ModO}
    (hψ : (autIH (fsuV1 T V) V (hz T V) K).map (MulAut.congr ψ).toMonoidHom =
      (g2Derived (ZMod 2)).map (g2OAct (ZMod 2))) :
    ↥(hz T V) →* ↥(quasithinG2 (ZMod 2)) :=
  (MonoidHom.ofInjective g2OAct_injective).symm.toMonoidHom.comp
    ((C.rhoO ψ).codRestrict _ (C.rhoO_mem_range hψ))

theorem g2OAct_ΦO
    (C : Ctx753 T L V K)
    {ψ : ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))) ≃* ModO}
    (hψ : (autIH (fsuV1 T V) V (hz T V) K).map (MulAut.congr ψ).toMonoidHom =
      (g2Derived (ZMod 2)).map (g2OAct (ZMod 2))) (h : ↥(hz T V)) :
    g2OAct (ZMod 2) (C.ΦO hψ h) = C.rhoO ψ h := by
  have h1 := MonoidHom.ofInjective_apply (f := g2OAct (ZMod 2)) g2OAct_injective (x := C.ΦO hψ h)
  have h2 : MonoidHom.ofInjective g2OAct_injective (C.ΦO hψ h) =
      (C.rhoO ψ).codRestrict _ (C.rhoO_mem_range hψ) h := by
    simp only [ΦO, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rw [h2] at h1
  exact h1.symm

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem ψ_conj
    (C : Ctx753 T L V K)
    {ψ : ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))) ≃* ModO}
    (hψ : (autIH (fsuV1 T V) V (hz T V) K).map (MulAut.congr ψ).toMonoidHom =
      (g2Derived (ZMod 2)).map (g2OAct (ZMod 2))) (h : ↥(hz T V)) {u : G}
    (hu : u ∈ conjClosure V (hz T V)) :
    ψ (modMk C.U_le_normalizer ((h : G) * u * (h : G)⁻¹)
      ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V (hz T V) h.2) u).mp hu)) =
      g2OAct (ZMod 2) (C.ΦO hψ h) (ψ (modMk C.U_le_normalizer u hu)) := by
  rw [C.g2OAct_ΦO hψ h]
  change _ = ψ ((C.actHX h : MulAut _) (ψ.symm (ψ (modMk C.U_le_normalizer u hu))))
  rw [MulEquiv.symm_apply_apply, C.actHX_coe,
    actH_modMk C.f918.H_le_normalizer_V₁ C.U_le_normalizer (le_normalizer_conjClosure V (hz T V))]

theorem exists_g0
    (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hcard : Nat.card (fixV (autIH (fsuV1 T V) V (hz T V) K)) = 2)
    {ψ : ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))) ≃* ModO}
    (hψ : (autIH (fsuV1 T V) V (hz T V) K).map (MulAut.congr ψ).toMonoidHom =
      (g2Derived (ZMod 2)).map (g2OAct (ZMod 2))) :
    ∃ g₀ : ↥(quasithinG2 (ZMod 2)), (∀ h : ↥(hz T V), C.ΦO hψ h = g₀ * C.Φ E h * g₀⁻¹) ∧
      ∀ u : ↥(conjClosure V (hz T V)),
        g2QAct (ZMod 2) g₀ (C.θ e u) = M755.projOQ (ψ (modMk C.U_le_normalizer u u.2)) := by
  have hfix : ∀ v, v ∈ fixV (autIH (fsuV1 T V) V (hz T V) K) ↔
      ψ v ∈ fixV ((g2Derived (ZMod 2)).map (g2OAct (ZMod 2))) := by
    intro v
    rw [← hψ]
    constructor
    · rintro hv _ ⟨l, hl, rfl⟩
      change ψ (l (ψ.symm (ψ v))) = ψ v
      rw [MulEquiv.symm_apply_apply, hv l hl]
    · intro hv l hl
      have h1 := hv _ ⟨l, hl, rfl⟩
      change ψ (l (ψ.symm (ψ v))) = ψ v at h1
      rw [MulEquiv.symm_apply_apply] at h1
      exact ψ.injective h1
  have hcD : Nat.card (fixV ((g2Derived (ZMod 2)).map (g2OAct (ZMod 2)))) = 2 := by
    refine Eq.trans (Nat.card_congr ?_) hcard
    exact
      { toFun := fun v => ⟨ψ.symm v, (hfix _).2 (by rw [MulEquiv.apply_symm_apply]; exact v.2)⟩
        invFun := fun v => ⟨ψ v, (hfix _).1 v.2⟩
        left_inv := fun v => Subtype.ext (by simp)
        right_inv := fun v => Subtype.ext (by simp) }
  have hkerO : ∀ y, y ∈ fixV ((g2Derived (ZMod 2)).map (g2OAct (ZMod 2))) ↔
      M755.projOQ y = 1 := by
    intro y
    rw [M755.projOQ_eq_one_iff]
    constructor
    · intro hy
      exact M755.eq_one_or_eq_of_card_two hcD M755.ptO_129_mem M755.ptO_129_ne hy
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact M755.ptO_129_mem
  set θ₂ : ↥(conjClosure V (hz T V)) →* ModQ :=
    M755.projOQ.comp (ψ.toMonoidHom.comp (tildeHom C.U_le_normalizer)) with hθ₂
  have hθ₂a : ∀ u : ↥(conjClosure V (hz T V)),
      θ₂ u = M755.projOQ (ψ (modMk C.U_le_normalizer u u.2)) := fun _ => rfl
  have hker : (C.θ e).ker = θ₂.ker := by
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, C.θ_eq_one_iff e, hfix, hkerO, hθ₂a]
  have hsurj₁ := C.θ_surjective e
  have hsurj₂ : Function.Surjective θ₂ :=
    M755.projOQ_surjective.comp (ψ.surjective.comp (tildeHom_surjective C.U_le_normalizer))
  set τ₀ : ModQ →* ModQ := (C.θ e).liftOfRightInverse (Function.surjInv hsurj₁)
    (Function.rightInverse_surjInv hsurj₁) ⟨θ₂, hker.le⟩ with hτ₀def
  have hτ₀ : ∀ u, τ₀ (C.θ e u) = θ₂ u := fun u =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ u
  have hτinj : Function.Injective τ₀ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨u, rfl⟩ := hsurj₁ q
    rw [hτ₀] at hq
    have h1 : u ∈ θ₂.ker := hq
    rw [← hker] at h1
    exact h1
  have hτsurj : Function.Surjective τ₀ := fun q => by
    obtain ⟨u, rfl⟩ := hsurj₂ q
    exact ⟨C.θ e u, hτ₀ u⟩
  set τ : MulAut ModQ := MulEquiv.ofBijective τ₀ ⟨hτinj, hτsurj⟩ with hτdef
  have hτ : ∀ u, τ (C.θ e u) = θ₂ u := hτ₀
  have hint : ∀ h : ↥(hz T V), ∀ q, τ (g2QAct (ZMod 2) (C.Φ E h) q) =
      g2QAct (ZMod 2) (C.ΦO hψ h) (τ q) := by
    intro h q
    obtain ⟨u, rfl⟩ := hsurj₁ q
    rw [← C.θ_conj E h u, hτ, hτ, hθ₂a, hθ₂a, C.ψ_conj hψ h u.2, M755.projOQ_act]
  have hconj : ∀ h : ↥(hz T V),
      τ * g2QAct (ZMod 2) (C.Φ E h) * τ⁻¹ = g2QAct (ZMod 2) (C.ΦO hψ h) := by
    intro h
    ext q
    rw [MulAut.mul_apply, MulAut.mul_apply, hint, MulAut.apply_inv_self]
  have hKO : ∀ k (hk : k ∈ K), C.ΦO hψ ⟨k, C.le_hz hk⟩ ∈ g2Derived (ZMod 2) := by
    intro k hk
    have h1 : g2OAct (ZMod 2) (C.ΦO hψ ⟨k, C.le_hz hk⟩) ∈
        (g2Derived (ZMod 2)).map (g2OAct (ZMod 2)) := by
      rw [C.g2OAct_ΦO hψ, ← hψ]
      exact ⟨_, C.actHX_mem_K hk, rfl⟩
    obtain ⟨γ, hγ, hγe⟩ := h1
    rw [← g2OAct_injective hγe]
    exact hγ
  have hKO' : ∀ γ ∈ g2Derived (ZMod 2), ∃ k, ∃ hk : k ∈ K, C.ΦO hψ ⟨k, C.le_hz hk⟩ = γ := by
    intro γ hγ
    have h1 : g2OAct (ZMod 2) γ ∈
        (autIH (fsuV1 T V) V (hz T V) K).map (MulAut.congr ψ).toMonoidHom := by
      rw [hψ]
      exact ⟨γ, hγ, rfl⟩
    obtain ⟨κ, hκ, hκe⟩ := h1
    have hκ' := hκ
    rw [autIH_eq_map C.f918 C.le_hz] at hκ'
    obtain ⟨⟨k, hkH⟩, hk, rfl⟩ := hκ'
    have hkK : k ∈ K := Subgroup.mem_subgroupOf.mp hk
    refine ⟨k, hkK, g2OAct_injective ?_⟩
    rw [C.g2OAct_ΦO hψ, ← hκe]
    rfl
  have hnorm : ∀ x, x ∈ (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)) ↔
      τ * x * τ⁻¹ ∈ (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)) := by
    intro x
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      obtain ⟨k', hk', hke⟩ := C.exists_K_of_derived E hγ
      rw [← hke, C.ΦG_eq E (C.le_hz hk'), hconj]
      exact ⟨_, hKO k' hk', rfl⟩
    · rintro ⟨γ', hγ', hγ'e⟩
      obtain ⟨k, hk, hke⟩ := hKO' γ' hγ'
      rw [← hke, ← hconj] at hγ'e
      have hx' : x = g2QAct (ZMod 2) (C.Φ E ⟨k, C.le_hz hk⟩) :=
        (mul_left_cancel (mul_right_cancel hγ'e)).symm
      rw [hx']
      refine ⟨_, ?_, rfl⟩
      rw [← C.map_Φ_K E]
      exact ⟨⟨k, C.le_hz hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  obtain ⟨g₀, hg₀⟩ := normalizer_two_Q τ hnorm
  refine ⟨g₀, fun h => g2QAct_injective ?_, fun u => ?_⟩
  · rw [← hconj, ← hg₀, map_mul, map_mul, map_inv]
  · rw [hg₀, hτ, hθ₂a]

end Ctx753

end CFSG.Quasithin.H13.L32A

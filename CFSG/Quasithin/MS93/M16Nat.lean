module

public import CFSG.Quasithin.MS93.M16Ind

public section

namespace CFSG.Quasithin.MS93.M16

open CFSG.Quasithin Matrix

variable {F : Type} [Field F] {V : Type*} [CommGroup V]

theorem mem_qPt_iff' {g : SL3 F} :
    g ∈ (qPt : Subgroup (SL3 F)) ↔ ∃ a b : F, rootElt 0 1 a * rootElt 0 2 b = g := by
  have hc : ∀ a b : F, rootElt 0 2 b * rootElt 0 1 a = rootElt 0 1 a * rootElt 0 2 b :=
    fun a b => ((rootElt_commute (by decide) (by decide) a b).eq).symm
  let P : Subgroup (SL3 F) :=
    { carrier := {g | ∃ a b : F, rootElt 0 1 a * rootElt 0 2 b = g}
      mul_mem' := by
        rintro _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
        refine ⟨a + a', b + b', ?_⟩
        have e : rootElt 0 1 a' * (rootElt 0 2 b * rootElt 0 2 b') =
            rootElt 0 2 b * (rootElt 0 1 a' * rootElt 0 2 b') := by
          rw [← mul_assoc, ← mul_assoc, hc]
        rw [rootElt_add, rootElt_add]
        simp only [mul_assoc, e]
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, b, rfl⟩
        refine ⟨-a, -b, ?_⟩
        rw [rootElt_neg, rootElt_neg, ← _root_.mul_inv_rev, hc] }
  constructor
  · intro hg
    have hle : qPt ≤ P := by
      rw [qPt]
      refine sup_le ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact ⟨a, 0, by simp⟩
      · rintro _ ⟨b, rfl⟩
        exact ⟨0, b, by simp⟩
    exact hle hg
  · rintro ⟨a, b, rfl⟩
    exact Subgroup.mul_mem_sup (rootElt_mem_rootGroup _ _ _) (rootElt_mem_rootGroup _ _ _)

@[expose] def fixer (ρ : SL3 F →* MulAut V) (A : Subgroup V) : Subgroup (SL3 F) where
  carrier := {g | ∀ v ∈ A, ρ g v = v}
  mul_mem' := fun {g k} hg hk v hv => by rw [rho_mul, hk v hv, hg v hv]
  one_mem' := fun v _ => by simp
  inv_mem' := fun {g} hg v hv => by
    have := rho_inv_rho ρ g v
    rwa [hg v hv] at this

theorem cyc_conj_rootElt01 (s : F) : cyc * rootElt 0 1 s * cyc⁻¹ = rootElt 1 2 s :=
  cyc_conj_rootElt 0 1 s

theorem cyc_conj_rootElt21 (s : F) : cyc * rootElt 2 1 s * cyc⁻¹ = rootElt 0 2 s :=
  cyc_conj_rootElt 2 1 s

theorem conj_rootElt01_rootElt12 (s : F) :
    rootElt 0 1 1 * rootElt 1 2 s * (rootElt 0 1 1)⁻¹ = rootElt 0 2 s * rootElt 1 2 s := by
  have h := rootElt_commutator (F := F) (i := 0) (j := 1) (l := 2) (by decide) (by decide)
    (by decide) 1 s
  rw [one_mul, commutatorElement_def] at h
  rw [← h]
  group

section CharTwo

variable [CharP F 2] {ρ : SL3 F →* MulAut V} {𝒲 : Subgroup V}

theorem rootElt02_mul_rootElt12_eq (s : F) :
    rootElt 0 2 s * rootElt 1 2 s =
      (rootElt 0 1 1 * p01) * rootElt 0 2 s * (rootElt 0 1 1 * p01)⁻¹ := by
  rw [← conj_rootElt01_rootElt12, _root_.mul_inv_rev, p01_inv]
  have h := p01_conj (F := F) 0 2 s
  rw [p01_inv, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)] at h
  rw [← h]
  group

variable [Finite F] [Finite V]
  (h𝒲 : ∀ g ∈ (lnStab : Subgroup (SL3 F)), ∀ v ∈ 𝒲, ρ g v ∈ 𝒲)
  (hR : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) ≤ Nat.card F)
  (hN : G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 ≠
      (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲).map (ρ p01).toMonoidHom)
  (hW2 : ∀ r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲, ρ cyc r ∈ 𝒲)
include h𝒲 hR hN hW2

theorem rootElt21_fix_R (s : F) {r : V}
    (hr : r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) :
    ρ (rootElt 2 1 s) r = r := by
  set R := G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 with hRdef
  set y := ρ cyc r with hy
  have hyW : y ∈ 𝒲 := hW2 r hr
  have h12 : ρ (rootElt 1 2 s) y = y :=
    rho_conj_fix (cyc_conj_rootElt01 s).symm (rootElt_fix_R h𝒲 hR (by decide) s hr)
  have ht : ρ (rootElt 0 2 s) y * y⁻¹ ∈ R :=
    G6.mem_commOn_of_mem (Subgroup.mem_map.mpr ⟨_, rootElt_mem_rootGroup 0 2 s, rfl⟩) hyW
  set g := rootElt 0 1 (1 : F) * p01 with hg
  have hgl : g ∈ (lnStab : Subgroup (SL3 F)) :=
    Subgroup.mul_mem _ (rootElt_mem_lnStab (by decide) 1) p01_mem_lnStab
  have ht' : ρ (rootElt 0 2 s) y * y⁻¹ ∈ R.map (ρ g).toMonoidHom := by
    have e1 : ρ (g * rootElt 0 2 s * g⁻¹) y = ρ g (ρ (rootElt 0 2 s) (ρ g⁻¹ y)) := by
      rw [rho_mul, rho_mul]
    have e2 : ρ g (ρ (rootElt 0 2 s) (ρ g⁻¹ y)) = ρ (rootElt 0 2 s) y := by
      rw [← e1, hg, ← rootElt02_mul_rootElt12_eq, rho_mul, h12]
    have he : ρ (rootElt 0 2 s) y * y⁻¹ = ρ g (ρ (rootElt 0 2 s) (ρ g⁻¹ y) * (ρ g⁻¹ y)⁻¹) := by
      rw [map_mul (ρ g), map_inv (ρ g), rho_rho_inv, e2]
    rw [he]
    exact rho_mem_map_rho g (G6.mem_commOn_of_mem (Subgroup.mem_map.mpr
      ⟨_, rootElt_mem_rootGroup 0 2 s, rfl⟩) (h𝒲 _ (inv_mem hgl) y hyW))
  have hbot := (caseN_inf_eq_bot h𝒲 hR hN).1
  have hmem : ρ (rootElt 0 2 s) y * y⁻¹ ∈ R ⊓ R.map (ρ g).toMonoidHom := ⟨ht, ht'⟩
  rw [hg, inf_map_rootElt01_p01 (ρ := ρ) (𝒲 := 𝒲) h𝒲 hR, hbot, Subgroup.mem_bot,
    mul_inv_eq_one] at hmem
  have h := rho_conj_fix (ρ := ρ) (g := cyc⁻¹) (x' := rootElt 0 2 s) (x := rootElt 2 1 s)
    (by rw [inv_inv, ← cyc_conj_rootElt21]; group) hmem
  rwa [hy, rho_inv_rho] at h

theorem ptLevi_fix_R {g : SL3 F} (hg : g ∈ (ptLevi : Subgroup (SL3 F))) {r : V}
    (hr : r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) : ρ g r = r := by
  have hle : (ptLevi : Subgroup (SL3 F)) ≤
      fixer ρ (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_ <;> rintro _ ⟨c, rfl⟩ <;> intro r hr
    · exact rootElt_fix_R h𝒲 hR (by decide) c hr
    · exact rootElt_fix_R h𝒲 hR (by decide) c hr
    · exact rootElt_fix_R h𝒲 hR (by decide) c hr
    · exact rootElt21_fix_R h𝒲 hR hN hW2 c hr
  exact hle hg r hr

theorem ptStab_mem_R {k : SL3 F} (hk : k ∈ (ptStab : Subgroup (SL3 F))) {r : V}
    (hr : r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) :
    ρ k r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 := by
  have hke := mulVec_e0_of_mem_ptStab hk
  set a := ((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 0 with ha
  have ha0 : a ≠ 0 := by
    intro h0
    apply ML3.mulVec_e0_ne_zero k
    rw [hke, h0, zero_smul]
  set t := tor a 1 ha0 one_ne_zero with ht
  have hl : t⁻¹ * k ∈ (ptLevi : Subgroup (SL3 F)) := by
    refine mem_ptLevi_of_mulVec_e0 ?_
    rw [coe_mul_mulVec, hke, ← tor_mulVec_e0 a 1 ha0 one_ne_zero, ← ht, ← coe_mul_mulVec,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hkt : k = t * (t⁻¹ * k) := by group
  rw [hkt, rho_mul, ptLevi_fix_R h𝒲 hR hN hW2 hl hr]
  exact rho_mem_commOn02 h𝒲 (tor_mem_ptStab _ _ _ _) (tor_mem_lnStab _ _ _ _) hr

end CharTwo

end CFSG.Quasithin.MS93.M16

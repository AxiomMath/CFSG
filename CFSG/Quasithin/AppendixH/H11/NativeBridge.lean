module

public import CFSG.Quasithin.Background.SmithB45MatM12
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case0M12Rep

public section

namespace CFSG.Quasithin.AppendixH.H11

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12
  CFSG.Quasithin.Vol2.Ch10.SecA.C10P01 CFSG.Quasithin.B45Mat.M12 CFSG.Quasithin.B45Mat Matrix
  CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

@[expose] noncomputable def m12NativeModel : FFModel where
  Gam := ↥CFSG.Blueprint.NativeSporadic.M12
  Amb := G6.PermMod 12
  act g x := G6.permAct 12 (g : Equiv.Perm (Fin 12)) x
  sec := G6.coreMod 12
  ker := Subgroup.zpowers (G6.allOnes 12)

abbrev Q12 : Type :=
  ↥(G6.coreMod 12) ⧸ (Subgroup.zpowers (G6.allOnes 12)).subgroupOf (G6.coreMod 12)

structure NativeCoords {V : Type*} [CommGroup V] (L : Subgroup (MulAut V)) where
  π : ↥CFSG.Blueprint.NativeSporadic.M12 →* ↥L
  ψ : V ≃* Q12
  surj : Function.Surjective π
  equivariant : ∀ (γ : ↥CFSG.Blueprint.NativeSporadic.M12) (v : V) (m : ↥(G6.coreMod 12)),
    ψ v = QuotientGroup.mk m →
      ψ ((π γ : MulAut V) v) =
        QuotientGroup.mk (G6.coreAct 12 (γ : Equiv.Perm (Fin 12)) m)

section Bridge

variable {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)}

theorem nonempty_nativeCoords_of_realizes (h : m12NativeModel.Realizes L ⊤ ⊥) :
    Nonempty (NativeCoords L) := by
  unfold FFModel.Realizes FFModel.RealizesVia at h
  obtain ⟨π, hπsurj, -, -, -, -, -, -, ⟨β, hβsurj, hβker, hβeq⟩⟩ := h
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : (a * b⁻¹ : ↥(⊤ : Subgroup V)) = 1 := by
      apply Subtype.ext
      have h3 := (hβker (a * b⁻¹)).1 h1
      rwa [Subgroup.mem_bot] at h3
    exact mul_inv_eq_one.mp h2
  let f : V →* Q12 := β.comp Subgroup.topEquiv.symm.toMonoidHom
  have hf : Function.Bijective f :=
    ⟨hβinj.comp Subgroup.topEquiv.symm.injective,
      hβsurj.comp Subgroup.topEquiv.symm.surjective⟩
  let ψ : V ≃* Q12 := MulEquiv.ofBijective f hf
  refine ⟨⟨π, ψ, hπsurj, ?_⟩⟩
  intro γ v m hm
  let u0 : ↥(⊤ : Subgroup V) := Subgroup.topEquiv.symm v
  have hbu : β u0 = QuotientGroup.mk m := hm
  have hmem : G6.permAct 12 (γ : Equiv.Perm (Fin 12)) (m : G6.PermMod 12) ∈ G6.coreMod 12 :=
    G6.permAct_mem_coreMod _ m.2
  have hhu : ((π γ : ↥L) : MulAut V) (u0 : V) ∈ (⊤ : Subgroup V) := Subgroup.mem_top _
  have hβ := hβeq γ u0 m hhu hmem hbu
  have harg : Subgroup.topEquiv.symm (((π γ : ↥L) : MulAut V) v) =
      ⟨((π γ : ↥L) : MulAut V) (u0 : V), hhu⟩ := by
    apply Subtype.ext
    rfl
  show β (Subgroup.topEquiv.symm (((π γ : ↥L) : MulAut V) v)) =
    QuotientGroup.mk (G6.coreAct 12 (γ : Equiv.Perm (Fin 12)) m)
  rw [harg, hβ]
  rfl

private theorem mem_zpowers_of_sq_eq_one {G : Type*} [Group G] {a x : G} (ha : a ^ 2 = 1) :
    x ∈ Subgroup.zpowers a ↔ x = 1 ∨ x = a := by
  constructor
  · intro hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      have h2 : a ^ (2 : ℤ) = 1 := by simpa [zpow_natCast] using ha
      rw [hm, _root_.zpow_mul, h2, _root_.one_zpow]
    · right
      have h2 : a ^ (2 : ℤ) = 1 := by simpa [zpow_natCast] using ha
      have h2m : a ^ ((2 : ℤ) * m) = 1 := by
        rw [_root_.zpow_mul, h2, _root_.one_zpow]
      rw [hm, _root_.zpow_add_one, h2m]
      simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

private theorem allOnes_sq : G6.allOnes 12 ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_one, pow_two, toAdd_mul, G6.allOnes, toAdd_ofAdd]
  funext i
  show (1 : ZMod 2) + 1 = 0
  decide

noncomputable def m12QuotHom : ↥(G6.coreMod 12) →* W10 where
  toFun u := Multiplicative.ofAdd (Case0M12.m12M *ᵥ Multiplicative.toAdd (u : G6.PermMod 12))
  map_one' := by simp
  map_mul' u v := by
    rw [← ofAdd_add, Subgroup.coe_mul, toAdd_mul, Matrix.mulVec_add]

private theorem m12QuotHom_apply (u : ↥(G6.coreMod 12)) :
    m12QuotHom u = Multiplicative.ofAdd
      (Case0M12.m12M *ᵥ Multiplicative.toAdd (u : G6.PermMod 12)) := rfl

theorem m12QuotHom_surjective : Function.Surjective m12QuotHom := by
  intro w
  obtain ⟨u, hu, hMu⟩ := Case0M12.m12M_surjective (Multiplicative.toAdd w)
  refine ⟨⟨Multiplicative.ofAdd u, G6.mem_coreMod.2 hu⟩, ?_⟩
  simp only [m12QuotHom_apply, Subgroup.coe_mk, toAdd_ofAdd, hMu, ofAdd_toAdd]

theorem m12QuotHom_ker :
    (Subgroup.zpowers (G6.allOnes 12)).subgroupOf (G6.coreMod 12) = m12QuotHom.ker := by
  ext u
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  constructor
  · intro h
    have hx : (u : G6.PermMod 12) = 1 ∨ (u : G6.PermMod 12) = G6.allOnes 12 :=
      (mem_zpowers_of_sq_eq_one allOnes_sq).1 h
    rcases hx with h1 | h1
    · rw [m12QuotHom_apply, h1, toAdd_one, Matrix.mulVec_zero, ofAdd_zero]
    · rw [m12QuotHom_apply, h1, G6.allOnes, toAdd_ofAdd, Case0M12.m12M_ones, ofAdd_zero]
  · intro h
    have h1 : Case0M12.m12M *ᵥ Multiplicative.toAdd (u : G6.PermMod 12) = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa [m12QuotHom_apply] using this
    rcases Case0M12.m12M_ker u.2 h1 with h0 | h2
    · have hu : (u : G6.PermMod 12) = 1 := by
        apply Multiplicative.toAdd.injective
        rw [h0, toAdd_one]
      rw [hu]
      exact Subgroup.one_mem _
    · have hu : (u : G6.PermMod 12) = G6.allOnes 12 := by
        apply Multiplicative.toAdd.injective
        funext i
        rw [h2 i]
        rfl
      rw [hu]
      exact Subgroup.mem_zpowers _

@[expose] noncomputable def m12QuotEquiv : Q12 ≃* W10 :=
  (QuotientGroup.quotientMulEquivOfEq m12QuotHom_ker).trans
    (QuotientGroup.quotientKerEquivOfSurjective m12QuotHom m12QuotHom_surjective)

theorem m12QuotEquiv_mk (u : ↥(G6.coreMod 12)) :
    m12QuotEquiv (QuotientGroup.mk u) = Multiplicative.ofAdd
      (Case0M12.m12M *ᵥ Multiplicative.toAdd (u : G6.PermMod 12)) := by
  unfold m12QuotEquiv
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem card_V_of_nativeCoords (c : NativeCoords L) : Nat.card V = 2 ^ 10 := by
  calc Nat.card V = Nat.card Q12 := Nat.card_congr c.ψ.toEquiv
    _ = Nat.card W10 := Nat.card_congr m12QuotEquiv.toEquiv
    _ = 2 ^ 10 := by
        rw [Nat.card_eq_fintype_card]
        simp [W10]

private theorem toAdd_permAct (γ : Equiv.Perm (Fin 12)) (m : G6.PermMod 12) :
    Multiplicative.toAdd (G6.permAct 12 γ m) = permAct γ (Multiplicative.toAdd m) := rfl

theorem exists_std_of_nativeCoords
    (c : NativeCoords L) :
    ∃ e : V ≃* W10,
      L.map (congrHom e) = (rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair).range := by
  let e : V ≃* W10 := c.ψ.trans m12QuotEquiv
  have heq : ∀ (γ : ↥CFSG.Blueprint.NativeSporadic.M12) (v : V),
      e ((c.π γ : MulAut V) v) =
        rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair (e12.symm γ) (e v) := by
    intro γ v
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (c.ψ v)
    have hψ := c.equivariant γ v m hm.symm
    have hv : e v = Multiplicative.ofAdd
        (Case0M12.m12M *ᵥ Multiplicative.toAdd (m : G6.PermMod 12)) := by
      show m12QuotEquiv (c.ψ v) = _
      rw [← hm, m12QuotEquiv_mk]
    have h2 : e ((c.π γ : MulAut V) v) = Multiplicative.ofAdd
        (Case0M12.m12M *ᵥ Multiplicative.toAdd
          (((G6.coreAct 12 (γ : Equiv.Perm (Fin 12)) m : ↥(G6.coreMod 12)) :
            G6.PermMod 12))) := by
      show m12QuotEquiv (c.ψ ((c.π γ : MulAut V) v)) = _
      rw [hψ, m12QuotEquiv_mk]
    have hρ : ∀ y : Fin 10 → ZMod 2,
        rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair (e12.symm γ)
            (Multiplicative.ofAdd y) =
          Multiplicative.ofAdd (rep10 γ *ᵥ y) := by
      intro y
      rw [← ofAdd_toAdd
        (rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair (e12.symm γ) (Multiplicative.ofAdd y))]
      congr 1
      rw [rep10_apply, mulAutMat_mulVec]
    rw [h2, hv, hρ (Case0M12.m12M *ᵥ Multiplicative.toAdd (m : G6.PermMod 12)),
      G6.coreAct_coe, toAdd_permAct,
      show Case0M12.m12M *ᵥ permAct (γ : Equiv.Perm (Fin 12))
            (Multiplicative.toAdd (m : G6.PermMod 12)) =
          rep10 γ *ᵥ (Case0M12.m12M *ᵥ Multiplicative.toAdd (m : G6.PermMod 12)) from
        Case0M12.equivariant γ m.2]
  have hcongr : ∀ γ : ↥CFSG.Blueprint.NativeSporadic.M12,
      congrHom e (c.π γ : MulAut V) =
        rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair (e12.symm γ) := by
    intro γ
    refine MulEquiv.ext fun w => ?_
    obtain ⟨v, rfl⟩ := e.surjective w
    change e ((c.π γ : MulAut V) (e.symm (e v))) =
      rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair (e12.symm γ) (e v)
    rw [MulEquiv.symm_apply_apply]
    exact heq γ v
  refine ⟨e, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ⟩ := c.surj ⟨x, hx⟩
    refine ⟨e12.symm γ, ?_⟩
    rw [show x = (c.π γ : MulAut V) from (congrArg Subtype.val hγ).symm, hcongr γ]
  · rintro _ ⟨σ, rfl⟩
    refine ⟨(c.π (e12 σ) : MulAut V), (c.π (e12 σ)).2, ?_⟩
    rw [hcongr (e12 σ), MulEquiv.symm_apply_apply]

theorem m12Ten_of_std {e : V ≃* W10}
    (he : L.map (congrHom e) = (rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair).range) :
    M12Ten L ⊤ ⊥ := by
  obtain ⟨eY, hY, hw, hR⟩ := m12Ten_rhoC12
  exact ⟨eY, hY, hw, realizes_of_map_congrHom e he hR⟩

end Bridge

end CFSG.Quasithin.AppendixH.H11

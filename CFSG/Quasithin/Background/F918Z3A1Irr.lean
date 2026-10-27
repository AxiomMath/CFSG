module

public import CFSG.Quasithin.Background.F918Z3A1Aux
public import CFSG.Quasithin.Background.F918Z6Def
public import CFSG.Quasithin.Background.F918Z0AuxCoord

public section

namespace CFSG.Quasithin

open scoped Pointwise

namespace Z3A1

variable {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)} {s : MulAut V}

theorem nonab_X (hZ : Z37 D X G T' s) : ∃ a ∈ X, ∃ b ∈ X, a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, hab⟩ := hZ.nonab
  refine ⟨s * a * s⁻¹, ?_, s * b * s⁻¹, ?_, fun h => hab ?_⟩
  · rw [hZ.swapDX]
    exact ⟨a, ha, rfl⟩
  · rw [hZ.swapDX]
    exact ⟨b, hb, rfl⟩
  · have h' : s * (a * b) * s⁻¹ = s * (b * a) * s⁻¹ := by
      simpa [mul_assoc] using h
    simpa using h'

theorem fixV_eq_bot (hZ : Z37 D X G T' s) : fixV D = ⊥ := by
  have hD : ∀ g ∈ D, ∀ u ∈ fixV D, g u ∈ fixV D := fun g hg u hu => by
    rw [hu g hg]
    exact hu
  have hX : ∀ g ∈ X, ∀ u ∈ fixV D, g u ∈ fixV D := by
    intro x hx u hu y hy
    have h1 := congrArg (fun f : MulAut V => f u) (hZ.comm y hy x hx)
    have h2 : y (x u) = x (y u) := by simpa using h1
    rw [h2, hu y hy]
  rcases hZ.irr _ (MatModel.invariant_sup_aut hD hX) with h | h
  · exact h
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hZ.nonab
    have h1 : ∀ g ∈ D, g = 1 := fun g hg => by
      ext v
      have : v ∈ fixV D := by rw [h]; trivial
      simpa using this g hg
    exact hab (by rw [h1 a ha, h1 b hb])

theorem faithful (hZ : Z37 D X G T' s) {I : Subgroup V} (hI : I ≠ ⊥)
    (hID : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I) : ∀ y ∈ D, (∀ v ∈ I, y v = v) → y = 1 := by
  have := hZ.simple
  let K : Subgroup ↥D :=
    { carrier := {y | ∀ v ∈ I, (y : MulAut V) v = v}
      one_mem' := fun v _ => rfl
      mul_mem' := fun {a b} ha hb v hv => by
        have h1 : ((a * b : ↥D) : MulAut V) v = (a : MulAut V) ((b : MulAut V) v) := rfl
        rw [h1, hb v hv, ha v hv]
      inv_mem' := fun {a} ha v hv => by
        have h1 := ha v hv
        have h2 : ((a⁻¹ : ↥D) : MulAut V) v = (a : MulAut V)⁻¹ v := rfl
        rw [h2]
        calc (a : MulAut V)⁻¹ v = (a : MulAut V)⁻¹ ((a : MulAut V) v) := by rw [h1]
          _ = v := by simp }
  have hKn : K.Normal := ⟨fun n hn g v hv => by
    have h1 : ((g * n * g⁻¹ : ↥D) : MulAut V) v =
        (g : MulAut V) ((n : MulAut V) ((g : MulAut V)⁻¹ v)) := rfl
    have h2 : (g : MulAut V)⁻¹ v ∈ I := hID _ (D.inv_mem g.2) v hv
    rw [h1, hn _ h2]
    simp⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hK | hK
  · intro y hy hyI
    have hmem : (⟨y, hy⟩ : ↥D) ∈ K := hyI
    rw [hK, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    apply hI
    rw [eq_bot_iff, ← fixV_eq_bot hZ]
    intro v hv y hy
    have hmem : (⟨y, hy⟩ : ↥D) ∈ K := by rw [hK]; trivial
    exact hmem v hv

theorem X_comm_of_irr (hZ : Z37 D X G T' s)
    (hirr : ∀ U : Subgroup V, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
  have := hZ.nontrivial
  have hsec : XMod.IsIrrSec ↥D (⊥ : Subgroup V) ⊤ := by
    refine ⟨?_, fun J hJ _ _ => hirr J (isInv_iff.mp hJ)⟩
    obtain ⟨a, ha⟩ := exists_ne (1 : V)
    refine lt_of_le_of_ne bot_le fun h => ha ?_
    have : a ∈ (⊤ : Subgroup V) := Subgroup.mem_top a
    rw [← h] at this
    exact Subgroup.mem_bot.mp this
  have hfield := (XMod.eqvEnd_isField_charTwo (A := ↥D) (P := V) hZ.exp hsec).2.1
  have hmem : ∀ x ∈ X, ∃ e : AddMonoid.End (Additive V), e ∈ XMod.eqvEnd ↥D V ∧
      ∀ v : V, e (Additive.ofMul v) = Additive.ofMul (x v) := by
    intro x hx
    refine ⟨MonoidHom.toAdditive (x : MulAut V).toMonoidHom, ?_, fun v => rfl⟩
    refine XMod.mem_eqvEnd_iff.mpr fun a p => ?_
    have := congrArg (fun f : MulAut V => f p) (hZ.comm a a.2 x hx)
    change (x : MulAut V) ((a : MulAut V) p) = (a : MulAut V) ((x : MulAut V) p)
    simpa using this.symm
  intro x hx y hy
  obtain ⟨ex, hex, hexv⟩ := hmem x hx
  obtain ⟨ey, hey, heyv⟩ := hmem y hy
  have h := hfield.mul_comm ⟨ex, hex⟩ ⟨ey, hey⟩
  ext v
  have h' := congrArg
    (fun e : ↥(XMod.eqvEnd ↥D V) => (e : AddMonoid.End (Additive V)) (Additive.ofMul v)) h
  change ex (ey (Additive.ofMul v)) = ey (ex (Additive.ofMul v)) at h'
  rw [heyv v, hexv (y v), hexv v, heyv (x v)] at h'
  exact Additive.ofMul.injective h'

theorem not_irr_top (hZ : Z37 D X G T' s) :
    ¬ ∀ U : Subgroup V, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro h
  obtain ⟨a, ha, b, hb, hab⟩ := nonab_X hZ
  exact hab (X_comm_of_irr hZ h a ha b hb)

theorem iSup_smul_eq_top (hZ : Z37 D X G T' s) {J : Subgroup V} (hJ : XMod.IsIrr ↥D J) :
    (⨆ t : ↥X, t • J) = ⊤ := by
  have hN := normalizes_of_comm hZ.comm
  have hinv : ∀ t : ↥X, XMod.IsInv ↥D (t • J) := fun t => XMod.isInv_smul_of_normalizes hN t hJ.1
  have hDinv : XMod.IsInv ↥D (⨆ t : ↥X, t • J) := XMod.isInv_iSup hinv
  have hXinv : ∀ x ∈ X, ∀ u ∈ (⨆ t : ↥X, t • J), x u ∈ (⨆ t : ↥X, t • J) := by
    intro x hx u hu
    refine Subgroup.iSup_induction (fun t : ↥X => t • J)
      (C := fun u => x u ∈ ⨆ t : ↥X, t • J) hu ?_ ?_ ?_
    · intro t u hu
      obtain ⟨j, hj, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists u t J).mp hu
      refine Subgroup.mem_iSup_of_mem ((⟨x, hx⟩ : ↥X) * t)
        ((Subgroup.mem_smul_pointwise_iff_exists _ _ J).mpr ⟨j, hj, ?_⟩)
      rfl
    · rw [map_one]
      exact one_mem _
    · intro u w hu hw
      rw [map_mul]
      exact mul_mem hu hw
  rcases hZ.irr _ (MatModel.invariant_sup_aut (isInv_iff.mp hDinv) hXinv) with h | h
  · exfalso
    have h1 : J ≤ ⨆ t : ↥X, t • J := by
      have := le_iSup (fun t : ↥X => t • J) 1
      rwa [one_smul] at this
    rw [h] at h1
    exact (isIrr_iff.mp hJ).1 (le_bot_iff.mp h1)
  · exact h

theorem iso_of_isIrr (hZ : Z37 D X G T' s) {J J' : Subgroup V} (hJ : XMod.IsIrr ↥D J)
    (hJ' : XMod.IsIrr ↥D J') : XMod.Iso ↥D J J' := by
  have hN := normalizes_of_comm hZ.comm
  have hle : J ≤ ⨆ t : ↥X, t • J' := by
    rw [iSup_smul_eq_top hZ hJ']
    exact le_top
  obtain ⟨t, ht⟩ := exists_iso_of_le_iSup_smul hN hJ' hJ hle
  exact ht.trans (XMod.Iso.symm hJ'.1 (iso_smul_of_comm hZ.comm t J'))

theorem exists_isIrr [Nontrivial V] : ∃ I : Subgroup V, XMod.IsIrr ↥D I := by
  have hex : ({L : Subgroup V | XMod.IsInv ↥D L ∧ L ≠ ⊥} : Set (Subgroup V)).Nonempty := by
    refine ⟨⊤, XMod.isInv_top, ?_⟩
    obtain ⟨a, ha⟩ := exists_ne (1 : V)
    intro h
    exact ha (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_top a))
  obtain ⟨I, ⟨hIinv, hIne⟩, hmin⟩ := (wellFounded_lt (α := Subgroup V)).has_min _ hex
  refine ⟨I, hIinv, bot_lt_iff_ne_bot.mpr hIne, fun J hJ _ hJI => ?_⟩
  by_contra hcon
  push Not at hcon
  exact hmin J ⟨hJ, hcon.1⟩ (lt_of_le_of_ne hJI hcon.2)

theorem exists_irr_inv (hZ : Z37 D X G T' s) {A : Subgroup (MulAut V)} (hA2 : IsPGroup 2 ↥A)
    (hAD : ∀ a ∈ A, ∀ y ∈ D, a * y * a⁻¹ ∈ D) :
    ∃ I : Subgroup V, XMod.IsIrr ↥D I ∧ ∀ a ∈ A, ∀ v ∈ I, a v ∈ I := by
  have := hZ.nontrivial
  obtain ⟨L, hL⟩ := exists_isIrr (D := D)
  have hN := normalizes_of_conj hAD
  obtain ⟨L', -, hL', -, hH⟩ := XMod.exists_isHomComp_of_isIrr hZ.exp hN hA2 hL
  refine ⟨L', hL', ?_⟩
  have hfix := (XMod.forall_iso_smul_eq_iff_isHomComp hN hL').2 hH
  intro a ha v hv
  have h1 : (⟨a, ha⟩ : ↥A) • L' = L' :=
    hfix ⟨a, ha⟩ (iso_of_isIrr hZ (isIrr_smul hN _ hL') hL')
  have h2 : (⟨a, ha⟩ : ↥A) • v ∈ (⟨a, ha⟩ : ↥A) • L' :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hv
  rw [h1] at h2
  exact h2

end Z3A1

end CFSG.Quasithin

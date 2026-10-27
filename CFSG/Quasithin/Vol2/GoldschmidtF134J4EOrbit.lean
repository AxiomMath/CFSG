module

public import CFSG.Sporadic.J4.QT2LocUniq
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24

public section

namespace CFSG.Quasithin.F134.J4E9

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs CFSG.QuasithinUnique.Setup.X1

@[expose] noncomputable def basePt : J ⧸ Hj := ((1 : J) : J ⧸ Hj)

theorem smul_basePt_eq_iff {x y : J} : x • basePt = y • basePt ↔ y⁻¹ * x ∈ Hj := by
  have h1 : ∀ z : J, z • basePt = (z : J ⧸ Hj) := fun z => by
    show ((z * 1 : J) : J ⧸ Hj) = _
    rw [mul_one]
  rw [h1, h1, QuotientGroup.eq, ← Hj.inv_mem_iff, mul_inv_rev, inv_inv]

theorem smul_basePt_eq_self_iff {g : J} : g • basePt = basePt ↔ g ∈ Hj := by
  have := smul_basePt_eq_iff (x := g) (y := 1)
  rwa [one_smul, inv_one, one_mul] at this

@[expose] noncomputable def stabE (g : J) : Subgroup J :=
  Eg uJ 11 ⊓ MulAction.stabilizer J (g • basePt)

theorem mem_stabE_iff {g x : J} : x ∈ stabE g ↔ x ∈ Eg uJ 11 ∧ g⁻¹ * x * g ∈ Hj := by
  rw [stabE, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, smul_smul, smul_basePt_eq_iff,
    ← mul_assoc]

theorem card_stabE_le
    {g : J} (hg : g ∉ Hj) :
    Nat.card (stabE g) ≤ 2 ^ 9 := by
  have hM := j4Facts.mat
  have hEl := elem_uJ hM
  have hψ : ∀ x : stabE g, (MulAut.conj g⁻¹).toMonoidHom (x : J) ∈ Hj := fun x => by
    have := (mem_stabE_iff.mp x.2).2
    simpa [MulAut.conj_apply] using this
  let ψ : stabE g →* Hj :=
    MonoidHom.codRestrict ((MulAut.conj g⁻¹).toMonoidHom.comp (stabE g).subtype) Hj hψ
  let θ : stabE g →* Equiv.Perm (Fin 24) := starHom.comp ψ
  have hθ : ∀ x : stabE g, (θ x = 1) → g⁻¹ * (x : J) * g ∈ Eg uJ 11 := by
    intro x hx
    have h1 : ψ x ∈ starHom.ker := hx
    rw [ker_starHom, Subgroup.mem_subgroupOf] at h1
    simpa [ψ, MulAut.conj_apply] using h1
  have hker : Nat.card θ.ker ≤ 8 := by
    have hinj : Function.Injective
        (fun x : θ.ker => (⟨(x.1 : J), (mem_stabE_iff.mp x.1.2).1, hθ x.1 x.2⟩ :
          {x : J | x ∈ Eg uJ 11 ∧ g⁻¹ * x * g ∈ Eg uJ 11})) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_coe_set_eq] at h1
    exact h1.trans (card_inter_le j4Facts hg)
  have hrange : Nat.card θ.range ≤ 2 ^ 6 := by
    have hle : θ.range ≤ CFSG.Blueprint.NativeSporadic.M24 := by
      rw [← range_starHom_eq]
      rintro _ ⟨x, rfl⟩
      exact ⟨ψ x, rfl⟩
    have hc : ∀ a b : stabE g, θ a * θ b = θ b * θ a := by
      intro a b
      rw [← map_mul, ← map_mul]
      exact congrArg θ (Subtype.ext (Eg_comm hEl (mem_stabE_iff.mp a.2).1
        (mem_stabE_iff.mp b.2).1))
    have hs : ∀ a : stabE g, θ a * θ a = 1 := by
      intro a
      rw [← map_mul, show a * a = 1 from Subtype.ext (Eg_sq hEl (mem_stabE_iff.mp a.2).1),
        map_one]
    have hB := m24_rank_le (θ.range.subgroupOf CFSG.Blueprint.NativeSporadic.M24)
      (by
        rintro ⟨x, hx⟩ hxB ⟨y, hy⟩ hyB
        obtain ⟨a, rfl⟩ := Subgroup.mem_subgroupOf.mp hxB
        obtain ⟨b, rfl⟩ := Subgroup.mem_subgroupOf.mp hyB
        exact Subtype.ext (hc a b))
      (by
        rintro ⟨x, hx⟩ hxB
        obtain ⟨a, rfl⟩ := Subgroup.mem_subgroupOf.mp hxB
        exact Subtype.ext (hs a))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hB
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv] at hcard
  calc Nat.card (stabE g) = Nat.card θ.range * Nat.card θ.ker := hcard
    _ ≤ 2 ^ 6 * 8 := Nat.mul_le_mul hrange hker
    _ = 2 ^ 9 := by norm_num

theorem four_le_ncard_orbit
    {g : J}
    (hg : g • basePt ≠ basePt) :
    4 ≤ {w : J ⧸ Hj | ∃ e ∈ Eg uJ 11, e • (g • basePt) = w}.ncard := by
  have hM := j4Facts.mat
  have hgH : g ∉ Hj := fun h => hg (smul_basePt_eq_self_iff.mpr h)
  have horb : {w : J ⧸ Hj | ∃ e ∈ Eg uJ 11, e • (g • basePt) = w} =
      MulAction.orbit ↥(Eg uJ 11) (g • basePt) := by
    ext w
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, rfl⟩
    · rintro ⟨e, rfl⟩
      exact ⟨e, e.2, rfl⟩
  rw [horb, ← MulAction.index_stabilizer]
  have hinj : Function.Injective
      (fun e : MulAction.stabilizer ↥(Eg uJ 11) (g • basePt) =>
        (⟨((e : ↥(Eg uJ 11)) : J),
          Subgroup.mem_inf.mpr ⟨(e : ↥(Eg uJ 11)).2, e.2⟩⟩ : stabE g)) := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))
  have hstab : Nat.card (MulAction.stabilizer ↥(Eg uJ 11) (g • basePt)) ≤ 2 ^ 9 :=
    (Nat.card_le_card_of_injective _ hinj).trans (card_stabE_le hgH)
  have h1 := (MulAction.stabilizer ↥(Eg uJ 11) (g • basePt)).card_mul_index
  rw [card_Eg_uJ hM] at h1
  have hpos : 0 < Nat.card (MulAction.stabilizer ↥(Eg uJ 11) (g • basePt)) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : Nat.card (MulAction.stabilizer ↥(Eg uJ 11) (g • basePt)) *
      (MulAction.stabilizer ↥(Eg uJ 11) (g • basePt)).index ≤ 2 ^ 9 * 3 :=
    Nat.mul_le_mul hstab (by omega)
  omega

end CFSG.Quasithin.F134.J4E9

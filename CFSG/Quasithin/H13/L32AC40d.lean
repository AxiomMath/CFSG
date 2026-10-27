module

public import CFSG.Quasithin.H13.L32AC40a
public import CFSG.Quasithin.Background.B3Sec
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.H13.L32A.C.A5Mod

open CFSG.Quasithin.B3

variable {W : Type*} [CommGroup W] [Finite W]

theorem card_map_mul_relIndex_le {f : W →* W} {Y Z : Subgroup W} (hYZ : Y ≤ Z)
    (hfY : Y.map f ≤ Y) : Nat.card (Y.map f) * Y.relIndex (Z.map f) ≤ Nat.card (Z.map f) := by
  have h1 := Subgroup.relIndex_mul_card Y (Z.map f)
  have h2 : Nat.card (Y.map f) ≤ Nat.card ↥(Y ⊓ Z.map f) :=
    Subgroup.card_le_of_le (le_inf hfY (Subgroup.map_mono hYZ))
  calc Nat.card (Y.map f) * Y.relIndex (Z.map f)
      ≤ Nat.card ↥(Y ⊓ Z.map f) * Y.relIndex (Z.map f) := Nat.mul_le_mul_right _ h2
    _ = Nat.card (Z.map f) := by rw [mul_comm, h1]

theorem four_le_relIndex_map (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (e : ↥L ≃* alternatingGroup (Fin 5)) {Y Z : Subgroup W}
    (hY : ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y) (hZ : ∀ l ∈ L, ∀ z ∈ Z, l z ∈ Z)
    (hnt : ∃ l ∈ L, ∃ z ∈ Z, l z * z⁻¹ ∉ Y) {u : MulAut W} (hu : u ∈ L) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) : 4 ≤ Y.relIndex (Z.map (commHom u)) := by
  set ρ : ↥L →* MulAut W := L.subtype with hρ
  have hZ' : IsInv ρ Z := fun g z hz => hZ g g.2 z hz
  have hY' : IsInv ρ Y := fun g y hy => hY g g.2 y hy
  set σ := secAct ρ hZ' hY' with hσ
  have hσmk : ∀ (g : ↥L) (z : ↥Z), σ g (QuotientGroup.mk z) =
      QuotientGroup.mk (restrictEquiv ρ Z hZ' g z) := fun _ _ => rfl
  have hS2 : ∀ q : Sec Z Y, q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H z =>
      rw [← QuotientGroup.mk_mul, show z * z = 1 from Subtype.ext (hW z), QuotientGroup.mk_one]
  have : IsSimpleGroup ↥L := e.isSimpleGroup
  have hσinj : Function.Injective σ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal σ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨l, hl, z, hz, hlz⟩ := hnt
      have h1 : σ ⟨l, hl⟩ = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top _
      have h2 := congrArg (fun φ : MulAut (Sec Z Y) => φ (QuotientGroup.mk ⟨z, hz⟩)) h1
      simp only [hσmk, MulAut.one_apply] at h2
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
      apply hlz
      have e2 : l z * z⁻¹ = ((restrictEquiv ρ Z hZ' ⟨l, hl⟩ ⟨z, hz⟩)⁻¹ * ⟨z, hz⟩ : ↥Z)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, restrictEquiv_apply, mul_inv_rev, inv_inv]
        exact mul_comm _ _
      rw [e2]
      exact Y.inv_mem h2
  set Γ := σ.range with hΓ
  let eΓ : ↥Γ ≃* alternatingGroup (Fin 5) := (MonoidHom.ofInjective hσinj).symm.trans e
  set γu : ↥L := ⟨u, hu⟩ with hγu
  have hγ2 : σ γu * σ γu = 1 := by
    rw [← map_mul, show γu * γu = 1 from Subtype.ext hu2, map_one]
  have hγ1 : σ γu ≠ 1 := fun h => hu1 (congrArg Subtype.val (hσinj (h.trans (map_one σ).symm)))
  have h4 := four_le_card_range hS2 eΓ (MonoidHom.mem_range.mpr ⟨γu, rfl⟩) hγ2 hγ1
  set K' := Z.map (commHom u) with hK'
  have hK'Z : K' ≤ Z := by
    rintro _ ⟨z, hz, rfl⟩
    exact Z.mul_mem (hZ u hu z hz) (Z.inv_mem hz)
  let g : ↥K' →* Sec Z Y := (QuotientGroup.mk' (Y.subgroupOf Z)).comp (Subgroup.inclusion hK'Z)
  have hpt : ∀ z : ↥Z, commHom (σ γu) (QuotientGroup.mk z) =
      g ⟨commHom u z, z, z.2, rfl⟩ := by
    intro z
    rw [commHom_apply, hσmk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  have hrange : g.range = (commHom (σ γu)).range := by
    ext q
    constructor
    · rintro ⟨⟨_, z, hz, rfl⟩, rfl⟩
      exact ⟨QuotientGroup.mk ⟨z, hz⟩, hpt ⟨z, hz⟩⟩
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H z => exact ⟨⟨commHom u z, z, z.2, rfl⟩, (hpt z).symm⟩
  have hker : g.ker = Y.subgroupOf K' := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk (Subgroup.inclusion hK'Z k) = (1 : Sec Z Y) ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  calc 4 ≤ Nat.card (commHom (σ γu)).range := h4
    _ = Nat.card g.range := by rw [hrange]
    _ = g.ker.index := (Subgroup.index_ker g).symm
    _ = Y.relIndex K' := by rw [hker]; rfl

theorem sixteen_le_card_range (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (e : ↥L ≃* alternatingGroup (Fin 5)) {Y Z : Subgroup W} (hYZ : Y ≤ Z)
    (hY : ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y) (hZ : ∀ l ∈ L, ∀ z ∈ Z, l z ∈ Z)
    (hntY : ∃ l ∈ L, ∃ y ∈ Y, l y * y⁻¹ ≠ 1) (hntZ : ∃ l ∈ L, ∃ z ∈ Z, l z * z⁻¹ ∉ Y)
    {u : MulAut W} (hu : u ∈ L) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    16 ≤ Nat.card (commHom u).range := by
  have h1 : 4 ≤ (⊥ : Subgroup W).relIndex (Y.map (commHom u)) :=
    four_le_relIndex_map hW e
      (fun _ _ _ h => by rw [Subgroup.mem_bot.mp h, map_one]; exact one_mem _) hY (by
        obtain ⟨l, hl, y, hy, hly⟩ := hntY
        exact ⟨l, hl, y, hy, fun h => hly (Subgroup.mem_bot.mp h)⟩) hu hu2 hu1
  rw [Subgroup.relIndex_bot_left] at h1
  have h2 := four_le_relIndex_map hW e hY hZ hntZ hu hu2 hu1
  have hfY : Y.map (commHom u) ≤ Y := by
    rintro _ ⟨y, hy, rfl⟩
    exact Y.mul_mem (hY u hu y hy) (Y.inv_mem hy)
  have h3 := card_map_mul_relIndex_le hYZ hfY
  have h4 : Nat.card (Z.map (commHom u)) ≤ Nat.card (commHom u).range :=
    Subgroup.card_le_of_le (Subgroup.map_le_range _ _)
  nlinarith

end CFSG.Quasithin.H13.L32A.C.A5Mod

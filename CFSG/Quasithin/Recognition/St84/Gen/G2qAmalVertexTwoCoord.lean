module

public import CFSG.Quasithin.Recognition.St84.Gen.NatSecDefs
public import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalDefs

import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalModule
import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalSchur
import CFSG.Quasithin.Recognition.St84.Gen.SL2Semilinear
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalSquare

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

section Conj

private theorem exists_comp_eq_of_ker_le {A B C : Type*} [Group A] [Group B] [Monoid C]
    (f : A →* B) (hf : Function.Surjective f) (g : A →* C) (h : f.ker ≤ g.ker) :
    ∃ k : B →* C, ∀ a, k (f a) = g a := by
  refine ⟨(QuotientGroup.lift f.ker g h).comp
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom, fun a => ?_⟩
  have h2 : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f a) =
      (QuotientGroup.mk a : A ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  change QuotientGroup.lift f.ker g h
    ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f a)) = g a
  rw [h2]
  rfl

private def conjOn (X : Subgroup G) (g : G) (hg : ∀ u ∈ X, g * u * g⁻¹ ∈ X) : ↥X →* ↥X where
  toFun u := ⟨g * u * g⁻¹, hg u u.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

private theorem coe_conjOn (X : Subgroup G) (g : G) (hg : ∀ u ∈ X, g * u * g⁻¹ ∈ X) (u : ↥X) :
    ((conjOn X g hg u : ↥X) : G) = g * u * g⁻¹ := rfl

variable {Q Z : Subgroup G}

private theorem normal_subgroupOf_of_central (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z) :
    (Z.subgroupOf Q).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have e : ((g * n * g⁻¹ : ↥Q) : G) = n := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hZc n hn g g.2]
    group
  rw [e]
  exact hn

private theorem quot_mul_comm (hQ2 : ∀ x ∈ Q, x ^ 2 ∈ Z) [(Z.subgroupOf Q).Normal]
    (a b : ↥Q ⧸ Z.subgroupOf Q) : a * b = b * a := by
  have hU2 : ∀ u : ↥Q ⧸ Z.subgroupOf Q, u * u = 1 := by
    intro u
    induction u using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa [sq] using hQ2 (x : G) x.2
  calc a * b = a * (a * b * (a * b)) * b := by rw [hU2, mul_one]
    _ = (a * a) * b * a * (b * b) := by group
    _ = b * a := by rw [hU2, hU2, one_mul, mul_one]

private theorem commutator_mem_of_sq (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z)
    (hQ2 : ∀ x ∈ Q, x ^ 2 ∈ Z) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) :
    x * y * x⁻¹ * y⁻¹ ∈ Z := by
  haveI := normal_subgroupOf_of_central hZc
  have h := quot_mul_comm hQ2 (QuotientGroup.mk (⟨x, hx⟩ : ↥Q))
    (QuotientGroup.mk (⟨y, hy⟩ : ↥Q))
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at h
  have e : x * y * x⁻¹ * y⁻¹ = (y * x) * ((x * y)⁻¹ * (y * x))⁻¹ * (y * x)⁻¹ := by group
  rw [e]
  have hc := Z.inv_mem h
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at hc
  have hyx : y * x ∈ Q := Q.mul_mem hy hx
  rw [← hZc _ hc _ hyx, mul_inv_cancel_right]
  exact hc

variable [(Z.subgroupOf Q).Normal]

private theorem mk_conjOn_eq (hZQ : Z ≤ Q) {g : G} (hg : ∀ u ∈ Q, g * u * g⁻¹ ∈ Q) {u : ↥Q}
    (h : g * u * g⁻¹ * (u : G)⁻¹ ∈ Z) :
    (QuotientGroup.mk (conjOn Q g hg u) : ↥Q ⧸ Z.subgroupOf Q) = QuotientGroup.mk u := by
  have e : conjOn Q g hg u = ⟨g * u * g⁻¹ * (u : G)⁻¹, hZQ h⟩ * u :=
    Subtype.ext (by simp only [coe_conjOn, Subgroup.coe_mul, Subgroup.coe_mk]; group)
  rw [e, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr h), one_mul]

private noncomputable def conjQuot (g : G) (hg : ∀ u ∈ Q, g * u * g⁻¹ ∈ Q)
    (hgZ : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z) : ↥Q ⧸ Z.subgroupOf Q →* ↥Q ⧸ Z.subgroupOf Q :=
  QuotientGroup.map _ _ (conjOn Q g hg) (fun z hz => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_conjOn]
    exact hgZ z (Subgroup.mem_subgroupOf.mp hz))

private theorem conjQuot_mk (g : G) (hg : ∀ u ∈ Q, g * u * g⁻¹ ∈ Q)
    (hgZ : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z) (u : ↥Q) :
    conjQuot g hg hgZ (QuotientGroup.mk u) = QuotientGroup.mk (conjOn Q g hg u) := rfl

variable {L : Subgroup G}

private noncomputable def conjQuotHom (hLQ : ∀ ℓ ∈ L, ∀ u ∈ Q, ℓ * u * ℓ⁻¹ ∈ Q)
    (hLZ : ∀ ℓ ∈ L, ∀ z ∈ Z, ℓ * z * ℓ⁻¹ ∈ Z) :
    ↥L →* AddMonoid.End (Additive (↥Q ⧸ Z.subgroupOf Q)) where
  toFun ℓ := MonoidHom.toAdditive (conjQuot (ℓ : G) (hLQ ℓ ℓ.2) (hLZ ℓ ℓ.2))
  map_one' := by
    refine AddMonoidHom.ext fun v => ?_
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    rw [show v = Additive.ofMul (QuotientGroup.mk u) by rw [hu]; rfl]
    change Additive.ofMul (conjQuot ((1 : ↥L) : G) (hLQ _ (1 : ↥L).2) (hLZ _ (1 : ↥L).2)
      (QuotientGroup.mk u)) = Additive.ofMul (QuotientGroup.mk u)
    rw [conjQuot_mk]
    congr 2
    exact Subtype.ext (by simp [coe_conjOn])
  map_mul' ℓ m := by
    refine AddMonoidHom.ext fun v => ?_
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    rw [show v = Additive.ofMul (QuotientGroup.mk u) by rw [hu]; rfl]
    change Additive.ofMul (conjQuot ((ℓ * m : ↥L) : G) (hLQ _ (ℓ * m).2) (hLZ _ (ℓ * m).2)
        (QuotientGroup.mk u)) =
      Additive.ofMul (conjQuot (ℓ : G) (hLQ ℓ ℓ.2) (hLZ ℓ ℓ.2)
        (conjQuot (m : G) (hLQ m m.2) (hLZ m m.2) (QuotientGroup.mk u)))
    rw [conjQuot_mk, conjQuot_mk, conjQuot_mk]
    congr 2
    exact Subtype.ext (by simp only [coe_conjOn, Subgroup.coe_mul]; group)

end Conj

section Orth

variable {F : Type} [Field F] [Finite F] [CharP F 2] {L Q Z W : Subgroup G}

theorem exists_radCoord_quot [Finite G] (hF : 4 ≤ Nat.card F) (hZQ : Z ≤ Q)
    (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z) (hQ2 : ∀ x ∈ Q, x ^ 2 ∈ Z)
    (hLQ : ∀ ℓ ∈ L, ∀ u ∈ Q, ℓ * u * ℓ⁻¹ ∈ Q) (hLZ : ∀ ℓ ∈ L, ∀ z ∈ Z, ℓ * z * ℓ⁻¹ ∈ Z)
    (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (hker : ∀ ℓ : ↥L, α ℓ = 1 → (ℓ : G) ∈ Q) (hIndec : ⁅Q, L⁆ = Q)
    (hZW : Z ≤ W) (hWL : ∀ w ∈ W, ∀ ℓ ∈ L, ℓ * w * ℓ⁻¹ * w⁻¹ ∈ Z)
    (hnatW : IsNatSecOf L Q W α) (hcard : Nat.card Q = Nat.card F ^ 3 * Nat.card Z)
    {E : Subgroup G} (hEQ : E ≤ Q) (hE : Nat.card F ^ 2 * Nat.card Z ≤ Nat.card E)
    (hES : ∀ x ∈ E, ∀ s : ↥L, (∃ t : F, (α s : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]) →
      (s : G) * x * (s : G)⁻¹ * x⁻¹ ∈ Z) :
    ∃ γ : ↥Q →* Multiplicative (Fin 3 → F), Function.Surjective γ ∧
      γ.ker = Z.subgroupOf Q ∧
      (∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
        Multiplicative.toAdd (γ v) = (sp4RadMat (α ℓ)).mulVec (Multiplicative.toAdd (γ u))) ∧
      ∀ u : ↥Q, (u : G) ∈ W ↔
        Multiplicative.toAdd (γ u) 1 = 0 ∧ Multiplicative.toAdd (γ u) 2 = 0 := by
  classical
  haveI : (Z.subgroupOf Q).Normal := normal_subgroupOf_of_central hZc
  set N := Z.subgroupOf Q with hNdef
  obtain ⟨β₀, hβ₀surj, hβ₀ker, hβ₀eq⟩ := hnatW
  have hNβ : N ≤ β₀.ker := by
    intro z hz
    rw [hβ₀ker, Subgroup.mem_subgroupOf]
    exact hZW (Subgroup.mem_subgroupOf.mp hz)
  let β : Additive (↥Q ⧸ N) →+ (Fin 2 → F) := (QuotientGroup.lift N β₀ hNβ).toAdditiveLeft
  have hβmk : ∀ u : ↥Q, β (Additive.ofMul (QuotientGroup.mk u)) =
      Multiplicative.toAdd (β₀ u) := fun _ => rfl
  let φ := conjQuotHom (L := L) hLQ hLZ
  have hle : α.ker ≤ φ.ker := by
    intro ℓ hℓ
    rw [MonoidHom.mem_ker] at hℓ ⊢
    have hℓQ := hker ℓ hℓ
    refine AddMonoidHom.ext fun v => ?_
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    rw [show v = Additive.ofMul (QuotientGroup.mk u) by rw [hu]; rfl]
    change Additive.ofMul (QuotientGroup.mk (conjOn Q ℓ (hLQ ℓ ℓ.2) u) : ↥Q ⧸ N) =
      Additive.ofMul (QuotientGroup.mk u)
    refine congrArg Additive.ofMul ?_
    have e : conjOn Q ℓ (hLQ ℓ ℓ.2) u = ⟨ℓ, hℓQ⟩ * u * (⟨ℓ, hℓQ⟩ : ↥Q)⁻¹ := Subtype.ext rfl
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      quot_mul_comm hQ2 (QuotientGroup.mk (⟨ℓ, hℓQ⟩ : ↥Q)), mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨ρ, hρ⟩ := exists_comp_eq_of_ker_le α hα φ hle
  have hρmk : ∀ (ℓ : ↥L) (u : ↥Q), ρ (α ℓ) (Additive.ofMul (QuotientGroup.mk u)) =
      Additive.ofMul (QuotientGroup.mk (conjOn Q ℓ (hLQ ℓ ℓ.2) u)) := by
    intro ℓ u
    rw [hρ]
    rfl
  have hβsurj : Function.Surjective β := by
    intro y
    obtain ⟨u, hu⟩ := hβ₀surj (Multiplicative.ofAdd y)
    exact ⟨Additive.ofMul (QuotientGroup.mk u), by rw [hβmk, hu]; rfl⟩
  have hβρ : ∀ (k : SL(2, F)) (v : Additive (↥Q ⧸ N)),
      β (ρ k v) = (k : Matrix (Fin 2) (Fin 2) F).mulVec (β v) := by
    intro k v
    obtain ⟨ℓ, rfl⟩ := hα k
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    rw [show v = Additive.ofMul (QuotientGroup.mk u) by rw [hu]; rfl, hρmk, hβmk, hβmk]
    exact hβ₀eq ℓ u _ rfl
  have hkerρ : ∀ (k : SL(2, F)) (v : Additive (↥Q ⧸ N)), β v = 0 → ρ k v = v := by
    intro k v hv
    obtain ⟨ℓ, rfl⟩ := hα k
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    rw [show v = Additive.ofMul (QuotientGroup.mk u) by rw [hu]; rfl] at hv ⊢
    rw [hρmk]
    rw [hβmk] at hv
    have huW : (u : G) ∈ W := by
      have h1 : u ∈ β₀.ker := by
        rw [MonoidHom.mem_ker]
        exact Multiplicative.toAdd.injective hv
      rw [hβ₀ker] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    exact congrArg Additive.ofMul (mk_conjOn_eq hZQ _ (hWL u huW ℓ ℓ.2))
  have hgen : ∀ W' : AddSubgroup (Additive (↥Q ⧸ N)),
      (∀ (k : SL(2, F)) (v : Additive (↥Q ⧸ N)), ρ k v - v ∈ W') → W' = ⊤ := by
    intro W' hW'
    let T : Subgroup G :=
      { carrier := {g | ∃ h : g ∈ Q,
          Additive.ofMul (QuotientGroup.mk (⟨g, h⟩ : ↥Q) : ↥Q ⧸ N) ∈ W'}
        one_mem' := ⟨Q.one_mem, by
          rw [show (⟨1, Q.one_mem⟩ : ↥Q) = 1 from rfl, QuotientGroup.mk_one, ofMul_one]
          exact W'.zero_mem⟩
        mul_mem' := fun {a b} ha hb => by
          obtain ⟨ha, ha'⟩ := ha
          obtain ⟨hb, hb'⟩ := hb
          refine ⟨Q.mul_mem ha hb, ?_⟩
          have h := W'.add_mem ha' hb'
          rwa [← ofMul_mul, ← QuotientGroup.mk_mul] at h
        inv_mem' := fun {a} ha => by
          obtain ⟨ha, ha'⟩ := ha
          refine ⟨Q.inv_mem ha, ?_⟩
          have h := W'.neg_mem ha'
          rwa [← ofMul_inv, ← QuotientGroup.mk_inv] at h }
    have hLQT : ⁅L, Q⁆ ≤ T := by
      rw [Subgroup.commutator_le]
      intro b hb a ha
      have hc : ⁅b, a⁆ ∈ Q := by
        rw [commutatorElement_def]
        exact Q.mul_mem (hLQ b hb a ha) (Q.inv_mem ha)
      refine ⟨hc, ?_⟩
      have h := hW' (α ⟨b, hb⟩) (Additive.ofMul (QuotientGroup.mk ⟨a, ha⟩))
      rw [hρmk] at h
      have e : (⟨⁅b, a⁆, hc⟩ : ↥Q) = conjOn Q b (hLQ b hb) ⟨a, ha⟩ * (⟨a, ha⟩ : ↥Q)⁻¹ :=
        Subtype.ext (by simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
          coe_conjOn])
      rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ofMul_mul, ofMul_inv,
        ← sub_eq_add_neg]
      exact h
    have hQT : Q ≤ T := by
      calc Q = ⁅Q, L⁆ := hIndec.symm
        _ = ⁅L, Q⁆ := Subgroup.commutator_comm _ _
        _ ≤ T := hLQT
    rw [eq_top_iff]
    intro v _
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    obtain ⟨h, hmem⟩ := hQT u.2
    rw [show v = Additive.ofMul (QuotientGroup.mk u) by rw [hu]; rfl]
    exact hmem
  have hcardV : Nat.card (Additive (↥Q ⧸ N)) = Nat.card F ^ 3 := by
    have h1 : Nat.card ↥Q = Nat.card (↥Q ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have h2 : Nat.card N = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    rw [h2, hcard] at h1
    exact (Nat.eq_of_mul_eq_mul_right hZpos h1).symm
  have h2V : ∀ v : Additive (↥Q ⧸ N), v + v = 0 := by
    intro v
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    rw [show v = Additive.ofMul (QuotientGroup.mk u) by rw [hu]; rfl, ← ofMul_mul,
      ← QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by
        simpa [sq] using hQ2 (u : G) u.2)), ofMul_one]
  have hC : Nat.card F ^ 2 ≤ Nat.card {v : Additive (↥Q ⧸ N) // ∀ k : SL(2, F),
      (∃ t : F, (k : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]) → ρ k v = v} := by
    let πE : ↥E →* ↥Q ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hEQ)
    have hfix : ∀ e : ↥E, ∀ k : SL(2, F),
        (∃ t : F, (k : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]) →
          ρ k (Additive.ofMul (πE e)) = Additive.ofMul (πE e) := by
      intro e k hk
      obtain ⟨s, rfl⟩ := hα k
      change ρ (α s) (Additive.ofMul (QuotientGroup.mk (Subgroup.inclusion hEQ e))) = _
      rw [hρmk]
      exact congrArg Additive.ofMul (mk_conjOn_eq hZQ _ (hES e e.2 s hk))
    have hker_le : Nat.card πE.ker ≤ Nat.card Z := by
      refine Nat.card_le_card_of_injective (fun x => ⟨((x : ↥E) : G), ?_⟩) ?_
      · have hx : πE (x : ↥E) = 1 := x.2
        have hx' : (QuotientGroup.mk (Subgroup.inclusion hEQ (x : ↥E)) : ↥Q ⧸ N) = 1 := hx
        have hx'' : Subgroup.inclusion hEQ (x : ↥E) ∈ N := (QuotientGroup.eq_one_iff _).mp hx'
        exact Subgroup.mem_subgroupOf.mp hx''
      · intro x y hxy
        have h1 := congrArg Subtype.val hxy
        exact Subtype.ext (Subtype.ext h1)
    have hEcard : Nat.card ↥E = Nat.card πE.range * Nat.card πE.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup πE.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange πE).toEquiv]
    have hrange : Nat.card F ^ 2 ≤ Nat.card πE.range := by
      have hZpos : 0 < Nat.card Z := Nat.card_pos
      have h : Nat.card F ^ 2 * Nat.card Z ≤ Nat.card πE.range * Nat.card Z :=
        hE.trans (hEcard ▸ Nat.mul_le_mul_left _ hker_le)
      exact Nat.le_of_mul_le_mul_right h hZpos
    refine hrange.trans (Nat.card_le_card_of_injective
      (fun y => ⟨Additive.ofMul (y : ↥Q ⧸ N), ?_⟩) ?_)
    · obtain ⟨e, he⟩ := MonoidHom.mem_range.mp y.2
      intro k hk
      rw [← he]
      exact hfix e k hk
    · intro y y' h
      have h1 := congrArg Subtype.val h
      exact Subtype.ext h1
  haveI : Finite (Additive (↥Q ⧸ N)) := inferInstanceAs (Finite (↥Q ⧸ N))
  obtain ⟨γ, hγ, hγβ⟩ := @exists_o3Coord F _ _ _ hF (Additive (↥Q ⧸ N))
    { (inferInstance : AddGroup (Additive (↥Q ⧸ N))) with
      add_comm := fun a b => quot_mul_comm hQ2 (Additive.toMul a) (Additive.toMul b) }
    _ h2V hcardV ρ β hβsurj hβρ hkerρ hgen hC
  let γQ : ↥Q →* Multiplicative (Fin 3 → F) :=
    { toFun := fun u => Multiplicative.ofAdd (γ (Additive.ofMul (QuotientGroup.mk u)))
      map_one' := by simp
      map_mul' := fun u w => by
        simp only [QuotientGroup.mk_mul, ofMul_mul, map_add, ofAdd_add] }
  have hγQ : ∀ u : ↥Q, Multiplicative.toAdd (γQ u) = γ (Additive.ofMul (QuotientGroup.mk u)) :=
    fun _ => rfl
  refine ⟨γQ, ?_, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨u, hu⟩ :=
      QuotientGroup.mk_surjective (Additive.toMul (γ.symm (Multiplicative.toAdd w)))
    refine ⟨u, Multiplicative.toAdd.injective ?_⟩
    rw [hγQ, hu, ofMul_toMul, AddEquiv.apply_symm_apply]
  · ext u
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (γ (Additive.ofMul (QuotientGroup.mk u))) = 1 ↔ u ∈ N
    rw [ofAdd_eq_one, AddEquiv.map_eq_zero_iff, ofMul_eq_zero, QuotientGroup.eq_one_iff]
  · intro ℓ u v hv
    have e : v = conjOn Q ℓ (hLQ ℓ ℓ.2) u := Subtype.ext hv
    rw [e, hγQ, hγQ, ← hρmk, hγ]
  · intro u
    rw [hγQ, (hγβ _).1, (hγβ _).2, hβmk, pow_eq_zero_iff two_ne_zero,
      pow_eq_zero_iff two_ne_zero, ← Subgroup.mem_subgroupOf, ← hβ₀ker, MonoidHom.mem_ker]
    constructor
    · intro h
      rw [h]
      exact ⟨rfl, rfl⟩
    · rintro ⟨h0, h1⟩
      apply Multiplicative.toAdd.injective
      ext i
      fin_cases i
      · exact h0
      · exact h1

end Orth

section Schur

private theorem exists_addHom_conj {X : Subgroup G} {V : Type*} [AddCommGroup V]
    (γ : ↥X →* Multiplicative V) (hγ : Function.Surjective γ) {g : G}
    (hg : ∀ u ∈ X, g * u * g⁻¹ ∈ X) (hker : ∀ u : ↥X, γ u = 1 → γ (conjOn X g hg u) = 1) :
    ∃ A : V →+ V, ∀ u : ↥X,
      A (Multiplicative.toAdd (γ u)) = Multiplicative.toAdd (γ (conjOn X g hg u)) := by
  obtain ⟨k, hk⟩ := exists_comp_eq_of_ker_le γ hγ (γ.comp (conjOn X g hg)) (fun u hu => by
    rw [MonoidHom.mem_ker] at hu ⊢
    exact hker u hu)
  refine ⟨AddMonoidHom.toMultiplicative.symm k, fun u => ?_⟩
  change Multiplicative.toAdd (k (Multiplicative.ofAdd (Multiplicative.toAdd (γ u)))) = _
  rw [ofAdd_toAdd, hk]
  rfl

variable {F : Type} [Field F]

theorem exists_natCoord_of_bot {L E : Subgroup G} {α : ↥L →* SL(2, F)}
    (h : IsNatSecOf L E ⊥ α) :
    ∃ δ : ↥E ≃* Multiplicative (Fin 2 → F), ∀ (ℓ : ↥L) (u v : ↥E), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (δ v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (δ u)) := by
  obtain ⟨β, hβ, hker, heq⟩ := h
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, Subgroup.bot_subgroupOf]
  exact ⟨MulEquiv.ofBijective β ⟨hinj, hβ⟩, heq⟩

theorem exists_smul_radCoord_conj [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    {L Q Z : Subgroup G} (hLQ : ∀ ℓ ∈ L, ∀ u ∈ Q, ℓ * u * ℓ⁻¹ ∈ Q)
    (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (γ : ↥Q →* Multiplicative (Fin 3 → F)) (hγ : Function.Surjective γ)
    (hγker : γ.ker = Z.subgroupOf Q)
    (hγeq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (γ v) = (sp4RadMat (α ℓ)).mulVec (Multiplicative.toAdd (γ u)))
    {g : G} (hgQ : ∀ u ∈ Q, g * u * g⁻¹ ∈ Q) (hgZ : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z)
    (hgL : ∀ ℓ : ↥L, ∃ ℓ' : ↥L, (ℓ' : G) = g * ℓ * g⁻¹ ∧ α ℓ' = α ℓ) :
    ∃ μ : F, ∀ u v : ↥Q, (v : G) = g * u * g⁻¹ →
      Multiplicative.toAdd (γ v) = μ • Multiplicative.toAdd (γ u) := by
  have hkerZ : ∀ u : ↥Q, γ u = 1 ↔ (u : G) ∈ Z := fun u => by
    rw [← MonoidHom.mem_ker, hγker, Subgroup.mem_subgroupOf]
  obtain ⟨A, hA⟩ := exists_addHom_conj γ hγ hgQ (fun u hu =>
    (hkerZ _).mpr (hgZ _ ((hkerZ u).mp hu)))
  have hAc : ∀ (M : SL(2, F)) (w : Fin 3 → F),
      A ((sp4RadMat M).mulVec w) = (sp4RadMat M).mulVec (A w) := by
    intro M w
    obtain ⟨ℓ, rfl⟩ := hα M
    obtain ⟨u, hu⟩ := hγ (Multiplicative.ofAdd w)
    obtain ⟨ℓ', hℓ', hαℓ'⟩ := hgL ℓ
    have hw : w = Multiplicative.toAdd (γ u) := by rw [hu]; rfl
    have e1 := hγeq ℓ u (conjOn Q ℓ (hLQ ℓ ℓ.2) u) rfl
    have e2 := hγeq ℓ' (conjOn Q g hgQ u) (conjOn Q g hgQ (conjOn Q ℓ (hLQ ℓ ℓ.2) u)) (by
      simp only [coe_conjOn, Subgroup.coe_inv, hℓ']
      group)
    rw [hw, ← e1, hA, e2, hαℓ', ← hA]
  obtain ⟨c, hc⟩ := exists_eq_smul_of_commute_sp4RadMat hF A hAc
  refine ⟨c, fun u v hv => ?_⟩
  have e : v = conjOn Q g hgQ u := Subtype.ext hv
  rw [e, ← hA, hc]

theorem exists_smul_natCoord_conj {L Z : Subgroup G} (hLZ : ∀ ℓ ∈ L, ∀ z ∈ Z, ℓ * z * ℓ⁻¹ ∈ Z)
    (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (δ : ↥Z ≃* Multiplicative (Fin 2 → F))
    (hδeq : ∀ (ℓ : ↥L) (u v : ↥Z), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (δ v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (δ u)))
    {g : G} (hgZ : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z)
    (hgL : ∀ ℓ : ↥L, ∃ ℓ' : ↥L, (ℓ' : G) = g * ℓ * g⁻¹ ∧ α ℓ' = α ℓ) :
    ∃ c : F, ∀ z w : ↥Z, (w : G) = g * z * g⁻¹ →
      Multiplicative.toAdd (δ w) = c • Multiplicative.toAdd (δ z) := by
  obtain ⟨A, hA'⟩ := exists_addHom_conj δ.toMonoidHom δ.surjective hgZ (fun u hu => by
    have hu1 : u = 1 := δ.injective (hu.trans (map_one δ).symm)
    rw [hu1, map_one, map_one])
  have hA : ∀ u : ↥Z,
      A (Multiplicative.toAdd (δ u)) = Multiplicative.toAdd (δ (conjOn Z g hgZ u)) := hA'
  have hAc : ∀ (M : SL(2, F)) (w : Fin 2 → F),
      A ((M : Matrix (Fin 2) (Fin 2) F).mulVec w) = (M : Matrix (Fin 2) (Fin 2) F).mulVec (A w) := by
    intro M w
    obtain ⟨ℓ, rfl⟩ := hα M
    obtain ⟨u, hu⟩ := δ.surjective (Multiplicative.ofAdd w)
    obtain ⟨ℓ', hℓ', hαℓ'⟩ := hgL ℓ
    have hw : w = Multiplicative.toAdd (δ u) := by rw [hu]; rfl
    have e1 := hδeq ℓ u (conjOn Z ℓ (hLZ ℓ ℓ.2) u) rfl
    have e2 := hδeq ℓ' (conjOn Z g hgZ u) (conjOn Z g hgZ (conjOn Z ℓ (hLZ ℓ ℓ.2) u)) (by
      simp only [coe_conjOn, Subgroup.coe_inv, hℓ']
      group)
    rw [hw, ← e1, hA, e2, hαℓ', ← hA]
  obtain ⟨c, hc⟩ := exists_eq_smul_of_commute_SL2 A hAc
  refine ⟨c, fun z w hw => ?_⟩
  have e : w = conjOn Z g hgZ z := Subtype.ext hw
  rw [e, ← hA, hc]

end Schur

section Square

variable {F : Type} [Field F] [Finite F] [CharP F 2] {L Q Z : Subgroup G}

private theorem commutator_mul_central_left (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z)
    {a b z : G} (hz : z ∈ Z) (hb : b ∈ Q) :
    (a * z) * b * (a * z)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h := hZc z hz b hb
  calc (a * z) * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem commutator_mul_central_right (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z)
    {a b z : G} (hz : z ∈ Z) (ha : a ∈ Q) :
    a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h := hZc z hz a⁻¹ (Q.inv_mem ha)
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem exists_sq_radCoord (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z)
    (hQ2 : ∀ x ∈ Q, x ^ 2 ∈ Z) (hZcen : ∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x ∈ Z)
    (hLQ : ∀ ℓ ∈ L, ∀ u ∈ Q, ℓ * u * ℓ⁻¹ ∈ Q)
    (α : ↥L →* SL(2, F)) (hα : Function.Surjective α)
    (γ : ↥Q →* Multiplicative (Fin 3 → F)) (hγ : Function.Surjective γ)
    (hγker : γ.ker = Z.subgroupOf Q)
    (hγeq : ∀ (ℓ : ↥L) (u v : ↥Q), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (γ v) = (sp4RadMat (α ℓ)).mulVec (Multiplicative.toAdd (γ u)))
    (δ : ↥Z ≃* Multiplicative (Fin 2 → F))
    (hδeq : ∀ (ℓ : ↥L) (u v : ↥Z), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (δ v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (δ u)))
    {g : G} (hgQ : ∀ u ∈ Q, g * u * g⁻¹ ∈ Q) {l χ : F} (hl0 : l ≠ 0) (hl1 : l ≠ 1)
    (hgγ : ∀ u v : ↥Q, (v : G) = g * u * g⁻¹ →
      Multiplicative.toAdd (γ v) = l ^ 2 • Multiplicative.toAdd (γ u))
    (hgδ : ∀ z w : ↥Z, (w : G) = g * z * g⁻¹ →
      Multiplicative.toAdd (δ w) = χ • Multiplicative.toAdd (δ z)) :
    ∃ c : F, c ≠ 0 ∧ χ = l ^ 3 ∧ ∀ (u : ↥Q) (hu : (u : G) ^ 2 ∈ Z) (x b₀ b₁ : F),
      Multiplicative.toAdd (γ u) = ![x, b₀ ^ 2, b₁ ^ 2] →
        Multiplicative.toAdd (δ ⟨(u : G) ^ 2, hu⟩) = (c * (x + b₀ * b₁)) • ![b₀, b₁] := by
  classical
  have hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Z :=
    fun x hx y hy => commutator_mem_of_sq hZc hQ2 hx hy
  have hδval : ∀ (a b : G) (ha : a ∈ Z) (hb : b ∈ Z), a = b → δ ⟨a, ha⟩ = δ ⟨b, hb⟩ := by
    rintro a b ha hb rfl
    rfl
  have hZ2 : ∀ z ∈ Z, z * z = 1 := by
    intro z hz
    have h1 : δ (⟨z, hz⟩ * ⟨z, hz⟩) = δ 1 := by
      rw [map_mul, map_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      ext i
      simp only [Pi.add_apply, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero _
    exact congrArg Subtype.val (δ.injective h1)
  let pre : (Fin 3 → F) → ↥Q := fun w => Function.surjInv hγ (Multiplicative.ofAdd w)
  have hpre : ∀ w, γ (pre w) = Multiplicative.ofAdd w := fun w => Function.surjInv_eq hγ _
  have hpre' : ∀ w, Multiplicative.toAdd (γ (pre w)) = w := fun w => by rw [hpre, toAdd_ofAdd]
  have hdiff : ∀ u u' : ↥Q, γ u = γ u' → (u : G)⁻¹ * u' ∈ Z := by
    intro u u' h
    have h1 : u⁻¹ * u' ∈ γ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [hγker] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hsq_eq : ∀ u u' : ↥Q, γ u = γ u' → (u' : G) ^ 2 = (u : G) ^ 2 := by
    intro u u' h
    have hz := hdiff u u' h
    have hzc := hZc _ hz u u.2
    have e1 : (u' : G) = u * ((u : G)⁻¹ * u') := by group
    rw [e1, sq, sq]
    calc (u : G) * ((u : G)⁻¹ * u') * (u * ((u : G)⁻¹ * u')) =
        u * (((u : G)⁻¹ * u') * u) * ((u : G)⁻¹ * u') := by group
      _ = u * (u * ((u : G)⁻¹ * u')) * ((u : G)⁻¹ * u') := by rw [hzc]
      _ = u * u * (((u : G)⁻¹ * u') * ((u : G)⁻¹ * u')) := by group
      _ = u * u := by rw [hZ2 _ hz, mul_one]
  have hcomm_eq : ∀ u u' y y' : ↥Q, γ u = γ u' → γ y = γ y' →
      (u' : G) * y' * (u' : G)⁻¹ * (y' : G)⁻¹ = (u : G) * y * (u : G)⁻¹ * (y : G)⁻¹ := by
    intro u u' y y' hu hy
    have e1 : (u' : G) = u * ((u : G)⁻¹ * u') := by group
    have e2 : (y' : G) = y * ((y : G)⁻¹ * y') := by group
    calc (u' : G) * y' * (u' : G)⁻¹ * (y' : G)⁻¹
        = (u * ((u : G)⁻¹ * u')) * y' * (u * ((u : G)⁻¹ * u'))⁻¹ * (y' : G)⁻¹ := by
          rw [← e1]
      _ = u * y' * (u : G)⁻¹ * (y' : G)⁻¹ :=
          commutator_mul_central_left hZc (hdiff u u' hu) y'.2
      _ = u * (y * ((y : G)⁻¹ * y')) * (u : G)⁻¹ * (y * ((y : G)⁻¹ * y'))⁻¹ := by
          rw [← e2]
      _ = u * y * (u : G)⁻¹ * (y : G)⁻¹ :=
          commutator_mul_central_right hZc (hdiff y y' hy) u.2
  let s : (Fin 3 → F) → (Fin 2 → F) := fun w =>
    Multiplicative.toAdd (δ ⟨((pre w : ↥Q) : G) ^ 2, hQ2 _ (pre w).2⟩)
  let P : (Fin 3 → F) → (Fin 3 → F) → (Fin 2 → F) := fun v w =>
    Multiplicative.toAdd (δ ⟨((pre v : ↥Q) : G) * (pre w : ↥Q) * ((pre v : ↥Q) : G)⁻¹ *
      ((pre w : ↥Q) : G)⁻¹, hcomm _ (pre v).2 _ (pre w).2⟩)
  have hs : ∀ u : ↥Q, s (Multiplicative.toAdd (γ u)) =
      Multiplicative.toAdd (δ ⟨(u : G) ^ 2, hQ2 _ u.2⟩) := by
    intro u
    exact congrArg Multiplicative.toAdd
      (hδval _ _ _ _ (hsq_eq u _ (by rw [hpre, ofAdd_toAdd])))
  have hP : ∀ u y : ↥Q, P (Multiplicative.toAdd (γ u)) (Multiplicative.toAdd (γ y)) =
      Multiplicative.toAdd (δ ⟨(u : G) * y * (u : G)⁻¹ * (y : G)⁻¹, hcomm _ u.2 _ y.2⟩) := by
    intro u y
    exact congrArg Multiplicative.toAdd
      (hδval _ _ _ _ (hcomm_eq u _ y _ (by rw [hpre, ofAdd_toAdd]) (by rw [hpre, ofAdd_toAdd])))
  have hγadd : ∀ u y : ↥Q, Multiplicative.toAdd (γ (u * y)) =
      Multiplicative.toAdd (γ u) + Multiplicative.toAdd (γ y) := by
    intro u y
    rw [map_mul, toAdd_mul]
  have hpol' : ∀ u y : ↥Q, Multiplicative.toAdd (δ ⟨((u * y : ↥Q) : G) ^ 2, hQ2 _ (u * y).2⟩) =
      Multiplicative.toAdd (δ ⟨(u : G) ^ 2, hQ2 _ u.2⟩) +
        Multiplicative.toAdd (δ ⟨(y : G) ^ 2, hQ2 _ y.2⟩) +
        Multiplicative.toAdd (δ ⟨(u : G) * y * (u : G)⁻¹ * (y : G)⁻¹, hcomm _ u.2 _ y.2⟩) := by
    intro u y
    have hyu := hZc _ (hQ2 _ u.2) _ y.2
    rw [sq] at hyu
    have key : ((u * y : ↥Q) : G) ^ 2 =
        ((u : G) * y * (u : G)⁻¹ * (y : G)⁻¹) * (u : G) ^ 2 * (y : G) ^ 2 := by
      rw [Subgroup.coe_mul, sq, sq, sq]
      calc (u : G) * y * ((u : G) * y) = (u : G) * y * (u : G)⁻¹ * (y : G)⁻¹ *
            ((y : G) * ((u : G) * u)) * y := by group
        _ = (u : G) * y * (u : G)⁻¹ * (y : G)⁻¹ * (((u : G) * u) * y) * y := by rw [hyu]
        _ = _ := by group
    have e : (⟨((u * y : ↥Q) : G) ^ 2, hQ2 _ (u * y).2⟩ : ↥Z) =
        ⟨_, hcomm _ u.2 _ y.2⟩ * ⟨_, hQ2 _ u.2⟩ * ⟨_, hQ2 _ y.2⟩ := Subtype.ext key
    rw [e, map_mul δ, map_mul δ, toAdd_mul, toAdd_mul]
    abel
  have hpol : ∀ v w, s (v + w) = s v + s w + P v w := by
    intro v w
    have hvw : v + w = Multiplicative.toAdd (γ (pre v * pre w)) := by rw [hγadd, hpre', hpre']
    rw [hvw, hs, hpol']
  have hP₁' : ∀ x x' y : ↥Q, Multiplicative.toAdd (δ ⟨((x * x' : ↥Q) : G) * y *
      ((x * x' : ↥Q) : G)⁻¹ * (y : G)⁻¹, hcomm _ (x * x').2 _ y.2⟩) =
      Multiplicative.toAdd (δ ⟨(x : G) * y * (x : G)⁻¹ * (y : G)⁻¹, hcomm _ x.2 _ y.2⟩) +
        Multiplicative.toAdd (δ ⟨(x' : G) * y * (x' : G)⁻¹ * (y : G)⁻¹, hcomm _ x'.2 _ y.2⟩) := by
    intro x x' y
    have hc2 := hZc _ (hcomm _ x'.2 _ y.2) _ (Q.inv_mem x.2)
    have key : ((x * x' : ↥Q) : G) * y * ((x * x' : ↥Q) : G)⁻¹ * (y : G)⁻¹ =
        ((x' : G) * y * (x' : G)⁻¹ * (y : G)⁻¹) * ((x : G) * y * (x : G)⁻¹ * (y : G)⁻¹) := by
      rw [Subgroup.coe_mul]
      calc (x : G) * x' * y * ((x : G) * x')⁻¹ * (y : G)⁻¹ =
          (x : G) * (((x' : G) * y * (x' : G)⁻¹ * (y : G)⁻¹) * (x : G)⁻¹) *
            ((x : G) * y * (x : G)⁻¹ * (y : G)⁻¹) := by group
        _ = (x : G) * ((x : G)⁻¹ * ((x' : G) * y * (x' : G)⁻¹ * (y : G)⁻¹)) *
            ((x : G) * y * (x : G)⁻¹ * (y : G)⁻¹) := by rw [hc2]
        _ = _ := by group
    have e : (⟨((x * x' : ↥Q) : G) * y * ((x * x' : ↥Q) : G)⁻¹ * (y : G)⁻¹,
        hcomm _ (x * x').2 _ y.2⟩ : ↥Z) = ⟨_, hcomm _ x'.2 _ y.2⟩ * ⟨_, hcomm _ x.2 _ y.2⟩ :=
      Subtype.ext key
    rw [e, map_mul δ, toAdd_mul, add_comm]
  have hP₁ : ∀ a b c, P (a + b) c = P a c + P b c := by
    intro a b c
    calc P (a + b) c = P (Multiplicative.toAdd (γ (pre a * pre b)))
          (Multiplicative.toAdd (γ (pre c))) := by rw [hγadd, hpre', hpre', hpre']
      _ = _ := hP _ _
      _ = P a c + P b c := hP₁' _ _ _
  have hP₂' : ∀ x y y' : ↥Q, Multiplicative.toAdd (δ ⟨(x : G) * ((y * y' : ↥Q) : G) *
      (x : G)⁻¹ * ((y * y' : ↥Q) : G)⁻¹, hcomm _ x.2 _ (y * y').2⟩) =
      Multiplicative.toAdd (δ ⟨(x : G) * y * (x : G)⁻¹ * (y : G)⁻¹, hcomm _ x.2 _ y.2⟩) +
        Multiplicative.toAdd (δ ⟨(x : G) * y' * (x : G)⁻¹ * (y' : G)⁻¹, hcomm _ x.2 _ y'.2⟩) := by
    intro x y y'
    have hc2 := hZc _ (hcomm _ x.2 _ y'.2) _ y.2
    have key : (x : G) * ((y * y' : ↥Q) : G) * (x : G)⁻¹ * ((y * y' : ↥Q) : G)⁻¹ =
        ((x : G) * y * (x : G)⁻¹ * (y : G)⁻¹) * ((x : G) * y' * (x : G)⁻¹ * (y' : G)⁻¹) := by
      rw [Subgroup.coe_mul]
      calc (x : G) * ((y : G) * y') * (x : G)⁻¹ * ((y : G) * y')⁻¹ =
          ((x : G) * y * (x : G)⁻¹ * (y : G)⁻¹) *
            ((y : G) * ((x : G) * y' * (x : G)⁻¹ * (y' : G)⁻¹)) * (y : G)⁻¹ := by group
        _ = ((x : G) * y * (x : G)⁻¹ * (y : G)⁻¹) *
            (((x : G) * y' * (x : G)⁻¹ * (y' : G)⁻¹) * y) * (y : G)⁻¹ := by rw [hc2]
        _ = _ := by group
    have e : (⟨(x : G) * ((y * y' : ↥Q) : G) * (x : G)⁻¹ * ((y * y' : ↥Q) : G)⁻¹,
        hcomm _ x.2 _ (y * y').2⟩ : ↥Z) = ⟨_, hcomm _ x.2 _ y.2⟩ * ⟨_, hcomm _ x.2 _ y'.2⟩ :=
      Subtype.ext key
    rw [e, map_mul δ, toAdd_mul]
  have hP₂ : ∀ a b c, P a (b + c) = P a b + P a c := by
    intro a b c
    calc P a (b + c) = P (Multiplicative.toAdd (γ (pre a)))
          (Multiplicative.toAdd (γ (pre b * pre c))) := by rw [hγadd, hpre', hpre', hpre']
      _ = _ := hP _ _
      _ = P a b + P a c := hP₂' _ _ _
  have hM : ∀ (M : SL(2, F)) (v : Fin 3 → F),
      s ((sp4RadMat M).mulVec v) = (M : Matrix (Fin 2) (Fin 2) F).mulVec (s v) := by
    intro M v
    obtain ⟨ℓ, rfl⟩ := hα M
    set u := pre v
    let u' : ↥Q := ⟨(ℓ : G) * u * (ℓ : G)⁻¹, hLQ _ ℓ.2 _ u.2⟩
    have hv : (sp4RadMat (α ℓ)).mulVec v = Multiplicative.toAdd (γ u') := by
      rw [hγeq ℓ u u' rfl, hpre']
    rw [hv, hs]
    have hu2 := hQ2 _ u.2
    have h := hδeq ℓ ⟨_, hu2⟩ ⟨_, hQ2 _ u'.2⟩ (by
      change ((ℓ : G) * u * (ℓ : G)⁻¹) ^ 2 = (ℓ : G) * (u : G) ^ 2 * (ℓ : G)⁻¹
      simp only [sq]
      group)
    rw [h]
  have hT : ∀ v, s (l ^ 2 • v) = χ • s v := by
    intro v
    set u := pre v
    let u' : ↥Q := ⟨g * u * g⁻¹, hgQ _ u.2⟩
    have hv : l ^ 2 • v = Multiplicative.toAdd (γ u') := by
      rw [hgγ u u' rfl, hpre']
    rw [hv, hs]
    have hu2 := hQ2 _ u.2
    have h := hgδ ⟨_, hu2⟩ ⟨_, hQ2 _ u'.2⟩ (by
      change (g * u * g⁻¹) ^ 2 = g * (u : G) ^ 2 * g⁻¹
      simp only [sq]
      group)
    rw [h]
  have hnd : ∀ x : F, x ≠ 0 → ∃ v, P ![x, 0, 0] v ≠ 0 := by
    intro x hx
    set u := pre ![x, 0, 0]
    have huZ : (u : G) ∉ Z := by
      intro huZ
      have h1 : u ∈ γ.ker := by rw [hγker]; exact Subgroup.mem_subgroupOf.mpr huZ
      rw [MonoidHom.mem_ker, hpre, ← ofAdd_zero] at h1
      have h2 := congrFun (Multiplicative.ofAdd.injective h1) 0
      exact hx (by simpa using h2)
    have hnc : ¬ ∀ y ∈ Q, (u : G) * y = y * u := fun h => huZ (hZcen _ u.2 h)
    push Not at hnc
    obtain ⟨y, hyQ, hyu⟩ := hnc
    refine ⟨Multiplicative.toAdd (γ ⟨y, hyQ⟩), ?_⟩
    have h := hP u ⟨y, hyQ⟩
    rw [hpre'] at h
    rw [h]
    intro h0
    apply hyu
    have h1 : δ ⟨(u : G) * y * (u : G)⁻¹ * y⁻¹, hcomm _ u.2 _ hyQ⟩ = δ 1 := by
      rw [map_one]
      exact Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
    have h2 := congrArg Subtype.val (δ.injective h1)
    change (u : G) * y * (u : G)⁻¹ * y⁻¹ = 1 at h2
    calc (u : G) * y = ((u : G) * y * (u : G)⁻¹ * y⁻¹) * y * u := by group
      _ = y * u := by rw [h2, one_mul]
  obtain ⟨c, hc0, hχ, hform⟩ := G2q.exists_squareMap_eq s P hpol hP₁ hP₂ hM hl0 hl1 hT hnd
  refine ⟨c, hc0, hχ, fun u hu x b₀ b₁ hγu => ?_⟩
  rw [← hform, ← hγu, hs]

end Square

end CFSG.Quasithin.F112R.St84

end

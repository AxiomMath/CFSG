module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312B
public import CFSG.Quasithin.Vol2.Ch3Sec3KGSylow

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

namespace L3312

theorem eq_one_of_odd_of_mem {X : Type} [Group X] {S : Subgroup X} (hS : IsPGroup 2 ↥S) {d : X}
    (hdS : d ∈ S) (hodd : Odd (orderOf d)) : d = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨d, hdS⟩
  have h1 : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  rcases i with _ | i
  · rw [pow_zero] at hi
    exact orderOf_eq_one_iff.mp hi
  · exfalso
    obtain ⟨m, hm⟩ := hodd
    rw [hi, pow_succ] at hm
    omega

theorem AutSylowSelfNorm.oddNorm {Q : Type} [Group Q] (h : AutSylowSelfNorm Q) (B : Subgroup Q) :
    OddNorm Q B := by
  intro A S hA hS _ d hd hodd
  rw [eq_one_of_odd_of_mem hS.2.1 (h A S hA hS hd) hodd]
  exact Subgroup.one_mem _

theorem oddNorm_top (Q : Type) [Group Q] : OddNorm Q ⊤ := by
  intro A S _ _ _ d _ _
  rw [mem_stabilizer_subgroup_iff, Subgroup.map_top_of_surjective _ d.surjective]

@[expose] noncomputable def quotCenterHom (Q : Type) [Group Q] :
    MulAut Q →* MulAut (Q ⧸ Subgroup.center Q) where
  toFun a := QuotientGroup.congr (Subgroup.center Q) (Subgroup.center Q) a
    (Subgroup.map_center_eq a)
  map_one' := by
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]
  map_mul' := by
    intro a b
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]

theorem quotCenterHom_mk {Q : Type} [Group Q] (a : MulAut Q) (x : Q) :
    quotCenterHom Q a (QuotientGroup.mk x) = QuotientGroup.mk (a x) := rfl

theorem quotCenterHom_conj {Q : Type} [Group Q] (q : Q) :
    quotCenterHom Q (MulAut.conj q) = MulAut.conj (QuotientGroup.mk q : Q ⧸ Subgroup.center Q) := by
  apply MulEquiv.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro y
  rfl

theorem quotCenterHom_injective {Q : Type} [Group Q] (hQ : Group.IsPerfect Q) :
    Function.Injective (quotCenterHom Q) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have hz : ∀ x : Q, x⁻¹ * a x ∈ Subgroup.center Q := by
    intro x
    have h1 := congrArg (fun f : MulAut (Q ⧸ Subgroup.center Q) => f (QuotientGroup.mk x))
      (MonoidHom.mem_ker.mp ha)
    simp only [quotCenterHom_mk, MulAut.one_apply] at h1
    exact QuotientGroup.eq.mp h1.symm
  have key : ∀ x y z w : Q, z ∈ Subgroup.center Q → w ∈ Subgroup.center Q →
      ⁅x * z, y * w⁆ = ⁅x, y⁆ := by
    intro x y z w hz hw
    have hz' := Subgroup.mem_center_iff.mp hz
    have hw' := Subgroup.mem_center_iff.mp hw
    rw [commutatorElement_def, commutatorElement_def]
    calc x * z * (y * w) * (x * z)⁻¹ * (y * w)⁻¹
        = x * (z * y) * (w * z⁻¹) * x⁻¹ * w⁻¹ * y⁻¹ := by group
      _ = x * (y * z) * (z⁻¹ * w) * x⁻¹ * w⁻¹ * y⁻¹ := by rw [← hz' y, ← hw' z⁻¹]
      _ = x * y * (w * x⁻¹) * w⁻¹ * y⁻¹ := by group
      _ = x * y * (x⁻¹ * w) * w⁻¹ * y⁻¹ := by rw [← hw' x⁻¹]
      _ = x * y * x⁻¹ * y⁻¹ := by group
  have hc : ∀ x y : Q, a ⁅x, y⁆ = ⁅x, y⁆ := by
    intro x y
    have hax : a x = x * (x⁻¹ * a x) := by group
    have hay : a y = y * (y⁻¹ * a y) := by group
    rw [map_commutatorElement, hax, hay]
    exact key x y _ _ (hz x) (hz y)
  let F : Subgroup Q :=
    { carrier := {x | a x = x}
      mul_mem' := fun {x y} (hx : a x = x) (hy : a y = y) => by
        show a (x * y) = x * y
        rw [map_mul, hx, hy]
      one_mem' := map_one a
      inv_mem' := fun {x} (hx : a x = x) => by
        show a x⁻¹ = x⁻¹
        rw [map_inv, hx] }
  have hF : commutator Q ≤ F := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨x, y, rfl⟩
    exact hc x y
  rw [hQ.commutator_eq_top] at hF
  rw [Subgroup.mem_bot]
  exact MulEquiv.ext fun x => hF (Subgroup.mem_top x)

theorem autSylowSelfNorm_of_quotCenter {Q : Type} [Group Q] (hQ : Group.IsPerfect Q)
    (h : AutSylowSelfNorm (Q ⧸ Subgroup.center Q)) : AutSylowSelfNorm Q := by
  intro A S hA hS d hd
  have hinj := quotCenterHom_injective hQ
  have hA' : (MulAut.conj : (Q ⧸ Subgroup.center Q) →* MulAut (Q ⧸ Subgroup.center Q)).range ≤
      A.map (quotCenterHom Q) := by
    rintro _ ⟨qb, rfl⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective qb
    exact ⟨MulAut.conj q, hA ⟨q, rfl⟩, quotCenterHom_conj q⟩
  have hS' : IsSylowTwoOf (S.map (quotCenterHom Q)) (A.map (quotCenterHom Q)) := by
    refine ⟨Subgroup.map_mono hS.1, hS.2.1.map _, fun h2 => hS.2.2 ?_⟩
    have h3 := Subgroup.relIndex_map_map_of_injective S A hinj
    have h4 : 2 ∣ (S.map (quotCenterHom Q)).relIndex (A.map (quotCenterHom Q)) := h2
    rw [h3] at h4
    exact h4
  have hd' : quotCenterHom Q d ∈ Subgroup.normalizer
      ((S.map (quotCenterHom Q) : Subgroup (MulAut (Q ⧸ Subgroup.center Q))) :
        Set (MulAut (Q ⧸ Subgroup.center Q))) ⊓ A.map (quotCenterHom Q) :=
    ⟨Subgroup.le_normalizer_map _ ⟨d, hd.1, rfl⟩, ⟨d, hd.2, rfl⟩⟩
  obtain ⟨s, hs, hsd⟩ := h _ _ hA' hS' hd'
  rwa [hinj hsd] at hs

end L3312

end CFSG.Quasithin.H13

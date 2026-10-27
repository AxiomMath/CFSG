module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Projection along a central direct factor

If two subgroups commute and intersect trivially, their join is their internal
direct product.  This owner records the equivalence with explicit values on
the two factors, so downstream equation-(11) centralizer arguments can use
the second coordinate as the projection along the selected central `P`
factor.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The internal direct-product equivalence for commuting disjoint subgroups,
with its values on the two canonical factors pinned explicitly. -/
public theorem subgroup_sup_exists_prod_equiv_of_commute_of_disjoint
    {G : Type u} [Group G]
    (P E : Subgroup G)
    (hdisj : P ⊓ E = ⊥)
    (hcomm : ∀ p e, p ∈ P → e ∈ E → Commute p e) :
    ∃ f : (P ⊔ E : Subgroup G) ≃* P × E,
      (∀ p : P, f ⟨p, Subgroup.mem_sup_left p.2⟩ = (p, 1)) ∧
      (∀ e : E, f ⟨e, Subgroup.mem_sup_right e.2⟩ = (1, e)) := by
  classical
  let psub : P →* G := P.subtype
  let esub : E →* G := E.subtype
  let hcomm' : ∀ p e, Commute (psub p) (esub e) :=
    fun p e => hcomm (psub p) (esub e) p.2 e.2
  let φ : P × E →* G :=
    psub.noncommCoprod esub hcomm'
  have hφinj : Function.Injective φ := by
    dsimp [φ]
    rw [MonoidHom.noncommCoprod_injective psub esub]
    refine ⟨Subgroup.subtype_injective _, Subgroup.subtype_injective _, ?_⟩
    rw [disjoint_iff_inf_le]
    intro x hx
    have hxP : x ∈ P := by
      rcases (Subgroup.mem_inf.mp hx).1 with ⟨p, rfl⟩
      exact p.2
    have hxE : x ∈ E := by
      rcases (Subgroup.mem_inf.mp hx).2 with ⟨e, rfl⟩
      exact e.2
    have hbot : x ∈ (⊥ : Subgroup G) := by
      rw [← hdisj]
      exact Subgroup.mem_inf.mpr ⟨hxP, hxE⟩
    exact Subgroup.mem_bot.mp hbot
  let e0 : P × E ≃* φ.range := MonoidHom.ofInjective hφinj
  have hrange : φ.range = P ⊔ E := by
    have h := MonoidHom.noncommCoprod_range psub esub
      hcomm'
    simpa [psub, esub, Subgroup.range_subtype] using h
  let e : P × E ≃* (P ⊔ E : Subgroup G) :=
    e0.trans (MulEquiv.subgroupCongr hrange)
  refine ⟨e.symm, ?_, ?_⟩
  · intro p
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change (p : G) = (p : G) * (1 : G)
    simp
  · intro x
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change (x : G) = (1 : G) * (x : G)
    simp

/-- If `D ≤ P ⊔ E` contains `X` but not the whole join `P ⊔ X`, then
projection along the prime-order factor `P` is injective on `D`. -/
public theorem exists_injective_second_projection_of_not_sup_le
    {G : Type u} [Group G] [Finite G]
    (P E X D : Subgroup G) {p : ℕ} (hp : p.Prime)
    (hPcard : Nat.card P = p)
    (hPE : P ⊓ E = ⊥)
    (hcomm : ∀ a b, a ∈ P → b ∈ E → Commute a b)
    (hDle : D ≤ P ⊔ E) (hXleD : X ≤ D)
    (hnot : ¬ P ⊔ X ≤ D) :
    ∃ φ : D →* E, Function.Injective φ := by
  classical
  obtain ⟨e, heP, _heE⟩ :=
    subgroup_sup_exists_prod_equiv_of_commute_of_disjoint P E hPE hcomm
  let inc : D →* (P ⊔ E : Subgroup G) := Subgroup.inclusion hDle
  let φ : D →* E := (MonoidHom.snd P E).comp (e.toMonoidHom.comp inc)
  have hDP : D ⊓ P = ⊥ := by
    by_contra hne
    have hcardDiv : Nat.card (↥(D ⊓ P)) ∣ p := by
      rw [← hPcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hcardEq : Nat.card (↥(D ⊓ P)) = p := by
      rcases (Nat.dvd_prime hp).mp hcardDiv with hone | hp'
      · exact False.elim (hne (Subgroup.card_eq_one.mp hone))
      · exact hp'
    have hEq : D ⊓ P = P :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hPcard, hcardEq])
    have hP_le_D : P ≤ D := by
      rw [← hEq]
      exact inf_le_left
    exact hnot (sup_le hP_le_D hXleD)
  refine ⟨φ, (MonoidHom.ker_eq_bot_iff φ).mp ?_⟩
  apply le_bot_iff.mp
  intro d hd
  have hsnd : (e (inc d)).2 = 1 := by simpa [φ] using hd
  let a : P := (e (inc d)).1
  have heq : e (inc d) = (a, 1) := by
    apply Prod.ext
    · rfl
    · exact hsnd
  have hpa : e ⟨(a : G), Subgroup.mem_sup_left a.2⟩ = (a, 1) := heP a
  have hincEq : inc d = ⟨(a : G), Subgroup.mem_sup_left a.2⟩ :=
    e.injective (heq.trans hpa.symm)
  have hdP : (d : G) ∈ P := by
    have hv := congrArg Subtype.val hincEq
    change (d : G) = (a : G) at hv
    rw [hv]
    exact a.2
  have hdInf : (d : G) ∈ D ⊓ P := ⟨d.2, hdP⟩
  have hdOne : (d : G) = 1 := by
    rw [hDP] at hdInf
    exact Subgroup.mem_bot.mp hdInf
  exact Subtype.ext hdOne

/-- A subgroup of the internal product whose order divides a prime-power
field order has trivial projection to the prime-order factor, when the two
primes are distinct; hence it lies in the second factor. -/
public theorem subgroup_le_second_factor_of_card_dvd_prime_power
    {G : Type u} [Group G] [Finite G]
    {P E W : Subgroup G} {p r f q : ℕ}
    [Fact p.Prime] [Fact r.Prime]
    (hPcard : Nat.card P = p) (hPE : P ⊓ E = ⊥)
    (hcomm : ∀ a b, a ∈ P → b ∈ E → Commute a b)
    (hq : q = r ^ f) (hpne : p ≠ r)
    (hWle : W ≤ P ⊔ E) (hWdvd : Nat.card W ∣ q) : W ≤ E := by
  classical
  obtain ⟨ePE, heP, heE⟩ :=
    subgroup_sup_exists_prod_equiv_of_commute_of_disjoint P E hPE hcomm
  let ψP : (P ⊔ E : Subgroup G) →* P :=
    (MonoidHom.fst P E).comp ePE.toMonoidHom
  let WI : Subgroup (P ⊔ E : Subgroup G) := W.subgroupOf (P ⊔ E)
  let IP : Subgroup P := WI.map ψP
  have hIPdvdW : Nat.card IP ∣ Nat.card W := by
    have h := Subgroup.card_map_dvd WI ψP
    have hWI : Nat.card WI = Nat.card W := by
      calc
        Nat.card WI = Nat.card (WI.map (P ⊔ E).subtype) :=
          (Subgroup.card_map_of_injective (P ⊔ E).subtype_injective).symm
        _ = Nat.card (W ⊓ (P ⊔ E) : Subgroup G) := by
          rw [Subgroup.subgroupOf_map_subtype]
        _ = Nat.card W := by rw [inf_eq_left.mpr hWle]
    rw [hWI] at h
    exact h
  have hIPdvdp : Nat.card IP ∣ p := by
    have h := Subgroup.card_dvd_of_le
      (H := IP) (K := (⊤ : Subgroup P)) le_top
    simpa [hPcard] using h
  have hpr : ¬ p ∣ r := by
    intro h
    exact hpne ((Nat.prime_dvd_prime_iff_eq
      (Fact.out : Nat.Prime p) (Fact.out : Nat.Prime r)).mp h)
  have hpcopr : Nat.Coprime p r :=
    (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hpr
  have hcop : Nat.Coprime p q := by
    rw [hq]
    exact hpcopr.pow_right f
  have hIPdvdq : Nat.card IP ∣ q := hIPdvdW.trans hWdvd
  have hIPone : Nat.card IP = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hIPdvdp hIPdvdq
  have hIPbot : IP = ⊥ := Subgroup.card_eq_one.mp hIPone
  intro z hz
  let zi : (P ⊔ E : Subgroup G) := ⟨z, hWle hz⟩
  have hψone : ψP zi = 1 := by
    have himg : ψP zi ∈ IP :=
      Subgroup.mem_map.mpr ⟨zi, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
    rw [hIPbot] at himg
    exact Subgroup.mem_bot.mp himg
  let e0 : E := (ePE zi).2
  have heqprod : ePE zi = (1, e0) := by
    apply Prod.ext
    · simpa [ψP] using hψone
    · rfl
  have hembed : ePE (⟨(e0 : G), Subgroup.mem_sup_right e0.2⟩ :
      (P ⊔ E : Subgroup G)) = (1, e0) := heE e0
  have hsubeq : zi =
      (⟨(e0 : G), Subgroup.mem_sup_right e0.2⟩ :
        (P ⊔ E : Subgroup G)) :=
    ePE.injective (heqprod.trans hembed.symm)
  have hval : z = (e0 : G) := congrArg Subtype.val hsubeq
  rw [hval]
  exact e0.2

/-- The second coordinate of an internal direct-product equivalence is
injective on a subgroup disjoint from the first factor. -/
public theorem second_projection_restriction_injective_of_disjoint
    {G : Type u} [Group G] [Finite G]
    (P E X : Subgroup G) (hXle : X ≤ P ⊔ E)
    (ePE : (P ⊔ E : Subgroup G) ≃* P × E)
    (heP : ∀ p : P,
      ePE ⟨p, Subgroup.mem_sup_left p.2⟩ = (p, 1))
    (hPX : P ⊓ X = ⊥) :
    Function.Injective ((MonoidHom.snd P E).comp ePE.toMonoidHom |>.comp
      (Subgroup.inclusion hXle)) := by
  let π : (P ⊔ E : Subgroup G) →* E :=
    (MonoidHom.snd P E).comp ePE.toMonoidHom
  intro a b hab
  have hdiff : (a : G) * (b : G)⁻¹ ∈ P := by
    let d : (P ⊔ E : Subgroup G) :=
      ⟨(a : G) * (b : G)⁻¹, (P ⊔ E).mul_mem
        (hXle a.2) ((P ⊔ E).inv_mem (hXle b.2))⟩
    have hab' :
        (ePE (Subgroup.inclusion hXle a)).2 =
          (ePE (Subgroup.inclusion hXle b)).2 := by
      simpa [π] using hab
    have hπone : π d = 1 := by
      have hdprod : d =
          (Subgroup.inclusion hXle a) *
            (Subgroup.inclusion hXle b)⁻¹ := by
        apply Subtype.ext
        rfl
      change (ePE d).2 = 1
      rw [hdprod, map_mul, map_inv]
      simp [hab']
    let p : P := (ePE d).1
    have heq : ePE d = (p, 1) := by
      apply Prod.ext
      · rfl
      · simpa [π] using hπone
    have hpa : ePE ⟨(p : G), Subgroup.mem_sup_left p.2⟩ = (p, 1) := heP p
    have hdeq : d =
        ⟨(p : G), Subgroup.mem_sup_left p.2⟩ :=
      ePE.injective (heq.trans hpa.symm)
    have hval : (a : G) * (b : G)⁻¹ = (p : G) :=
      congrArg Subtype.val hdeq
    rw [hval]
    exact p.2
  have hdiffX : (a : G) * (b : G)⁻¹ ∈ X :=
    X.mul_mem a.2 (X.inv_mem b.2)
  have hdiffbot : (a : G) * (b : G)⁻¹ = 1 := by
    have hi : (a : G) * (b : G)⁻¹ ∈ P ⊓ X := ⟨hdiff, hdiffX⟩
    rw [hPX] at hi
    exact Subgroup.mem_bot.mp hi
  apply Subtype.ext
  calc
    (a : G) = (a : G) * (b : G)⁻¹ * (b : G) := by simp
    _ = (b : G) := by rw [hdiffbot]; simp

end CFSG.GorensteinWalter

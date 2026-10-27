module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P1Eq

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
  CFSG.Quasithin.S1417
open scoped commutatorElement

section Z2

variable {G : Type} [Group G] [Finite G]

theorem eq_of_card_two_subgroup {Y : Subgroup G} (hY : Nat.card Y = 2) {y y' : G} (hy : y ∈ Y)
    (hy' : y' ∈ Y) (hy1 : y ≠ 1) (hy1' : y' ≠ 1) : y = y' := by
  have hord : ∀ z (hz : z ∈ Y), z ≠ 1 → orderOf z = 2 := by
    intro z hz hz1
    have hdvd : orderOf (⟨z, hz⟩ : ↥Y) ∣ 2 := hY ▸ orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with e | e
    · exact absurd (congrArg Subtype.val (orderOf_eq_one_iff.mp e)) hz1
    · rwa [Subgroup.orderOf_mk] at e
  have h2 := hord y hy hy1
  have hz : Nat.card (Subgroup.zpowers y) = 2 := by rw [Nat.card_zpowers, h2]
  have hle : Subgroup.zpowers y ≤ Y := Subgroup.zpowers_le.mpr hy
  have hY' : Subgroup.zpowers y = Y := Subgroup.eq_of_le_of_card_ge hle (by rw [hY, hz])
  rw [← hY'] at hy'
  exact ((E9Z4Str.eq_one_or_eq_of_mem_zpowers h2 hy').resolve_left hy1').symm

end Z2

section Cen

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem comm_conjSub_Z (S : Setting146 G T M) (hH : IsHTM T M H) {k : G}
    (hUle : conjClosure (VZ T M) H ≤ conjSub k H) {a w : G}
    (ha : a ∈ conjClosure (VZ T M) H) (hw : w ∈ conjSub k (quasithinOmegaOneCenter T)) :
    a * w * a⁻¹ * w⁻¹ = 1 := by
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have h1 : k⁻¹ * a * k ∈ H := mem_conjSub.mp (hUle ha)
  have hwz : k⁻¹ * w * k ∈ quasithinOmegaOneCenter T := mem_conjSub.mp hw
  have hconj : a * w * a⁻¹ ∈ conjSub k (quasithinOmegaOneCenter T) := by
    rw [mem_conjSub]
    have e : k⁻¹ * (a * w * a⁻¹) * k =
        (k⁻¹ * a * k) * (k⁻¹ * w * k) * (k⁻¹ * a * k)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hHN h1) _).mp hwz
  by_cases hw1 : w = 1
  · simp [hw1]
  · have hne : a * w * a⁻¹ ≠ 1 := fun e => hw1 (by simpa using e)
    have hcard : Nat.card (conjSub k (quasithinOmegaOneCenter T)) = 2 :=
      (CosetGeom.card_conjSub _ _).trans S.card_Z
    rw [eq_of_card_two_subgroup hcard hconj hw hne hw1]
    group

omit [Finite G] in
theorem uK_sup_Z_le_conjClosure (T M H : Subgroup G) :
    uK T M H ⊔ quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) H :=
  sup_le (S145.commutator_le_of_le_normalizer (le_normalizer_conjClosure _ _))
    (Z_le_conjClosure_VZ T M H)

theorem exists_decomp_UH
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Tb P : Subgroup (MulAut ↥(kOf (rhoH h)))} (hstr : E9Z4Str (resBeta (rhoH h)).range Tb P)
    {u₀ : G} (hu₀ : u₀ ∈ conjClosure (VZ T M) H) :
    ∃ uk ∈ uK T M H ⊔ quasithinOmegaOneCenter T, ∃ c : G, c ∈ conjClosure (VZ T M) H ∧
      (∀ y ∈ H, y * c * y⁻¹ * c⁻¹ ∈ quasithinOmegaOneCenter T) ∧
        ∃ z ∈ quasithinOmegaOneCenter T, u₀ = uk * c * z := by
  obtain ⟨a, ha, ct, hct, hac⟩ := hsplit (clsU h hu₀)
  have hmem : (⟨a, ha⟩ : ↥(kOf (rhoH h))) ∈ commV (resBeta (rhoH h)).range := by
    rw [hstr.commV_X]
    exact Subgroup.mem_top _
  have h2 : valK h ⟨a, ha⟩ ∈ tildeOf (quasithinOmegaOneCenter T)
      (uK T M H ⊔ quasithinOmegaOneCenter T) := by
    rw [tildeOf_uK_sup_Z_eq h hsplit]
    exact ⟨_, hmem, rfl⟩
  obtain ⟨uk', huk', hukeq⟩ := mem_secImg.mp h2
  have hukU : (uk' : G) ∈ conjClosure (VZ T M) H := uK_sup_Z_le_conjClosure T M H huk'
  have hcls_a : clsU h hukU = a := by
    apply IntMod.val_injective
    rw [clsU_val]
    exact hukeq
  obtain ⟨c, hcU, rfl⟩ := exists_clsU h ct
  have hcH : ∀ y ∈ H, y * c * y⁻¹ * c⁻¹ ∈ quasithinOmegaOneCenter T := fun y hy =>
    (rhoH_clsU_eq_iff h ⟨y, hy⟩ hcU).mp (hct (rhoH h ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩)
  have hprod : (uk' : G) * c ∈ conjClosure (VZ T M) H :=
    (conjClosure (VZ T M) H).mul_mem hukU hcU
  have heq : clsU h hu₀ = clsU h hprod := by
    rw [hac, ← hcls_a, clsU_mul h hukU hcU]
  have hz : (u₀⁻¹ * ((uk' : G) * c)) ∈ quasithinOmegaOneCenter T :=
    (clsU_eq_iff h hu₀ hprod).mp heq
  refine ⟨uk', huk', c, hcU, hcH, (u₀⁻¹ * ((uk' : G) * c))⁻¹,
    (quasithinOmegaOneCenter T).inv_mem hz, ?_⟩
  group

theorem comm_conjSub_c (hcls : ClassAutShapeStmt) (h35 : Lemma1435) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p)
    (h98 : HypF98 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H) {k : G}
    (hUkH : conjSub k (conjClosure (VZ T M) H) ≤ H)
    (hUle : conjClosure (VZ T M) H ≤ conjSub k H)
    (hZZ : conjSub k (quasithinOmegaOneCenter T) ⊓ quasithinOmegaOneCenter T = ⊥) {c : G}
    (hcU : c ∈ conjClosure (VZ T M) H)
    (hcH : ∀ y ∈ H, y * c * y⁻¹ * c⁻¹ ∈ quasithinOmegaOneCenter T) {u : G}
    (hu : u ∈ conjClosure (VZ T M) H) :
    (k * c * k⁻¹) * u * (k * c * k⁻¹)⁻¹ * u⁻¹ = 1 := by
  have hx : k * c * k⁻¹ ∈ conjSub k (conjClosure (VZ T M) H) := mul_mem_conjSub hcU
  have hxH : k * c * k⁻¹ ∈ H := hUkH hx
  have hZk : ∀ u' ∈ conjClosure (VZ T M) H,
      (k * c * k⁻¹) * u' * (k * c * k⁻¹)⁻¹ * u'⁻¹ ∈ conjSub k (quasithinOmegaOneCenter T) := by
    intro u' hu'
    have h1 : k⁻¹ * u' * k ∈ H := mem_conjSub.mp (hUle hu')
    have h2 := hcH _ h1
    have h3 : (k⁻¹ * u' * k) * c * (k⁻¹ * u' * k)⁻¹ * c⁻¹ ∈ quasithinOmegaOneCenter T := h2
    have h4 := (quasithinOmegaOneCenter T).inv_mem h3
    have e : (k * c * k⁻¹) * u' * (k * c * k⁻¹)⁻¹ * u'⁻¹ =
        k * ((k⁻¹ * u' * k) * c * (k⁻¹ * u' * k)⁻¹ * c⁻¹)⁻¹ * k⁻¹ := by group
    rw [e]
    exact mul_mem_conjSub h4
  have hZk' : ∀ u' ∈ conjClosure (VZ T M) H,
      (k * c * k⁻¹) * u' * (k * c * k⁻¹)⁻¹ * u'⁻¹ ∈
        conjSub k (quasithinOmegaOneCenter T) ⊓ conjClosure (VZ T M) H := fun u' hu' =>
    ⟨hZk u' hu', (conjClosure (VZ T M) H).mul_mem (conj_mem_UH hxH hu')
      ((conjClosure (VZ T M) H).inv_mem hu')⟩
  have hcard : Nat.card ↥(conjSub k (quasithinOmegaOneCenter T) ⊓ conjClosure (VZ T M) H) ≤ 2 := by
    refine (Subgroup.card_le_of_le inf_le_left).trans ?_
    rw [CosetGeom.card_conjSub, S.card_Z]
  have hρ := rhoH_eq_one_of_comm_le hcls h35 S hred hshape h98 hxH inf_le_right hcard hZk'
  have hZ : (k * c * k⁻¹) * u * (k * c * k⁻¹)⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T :=
    (rhoH_clsU_eq_iff h98.toHypF91 ⟨_, hxH⟩ hu).mp (by rw [hρ]; rfl)
  have hboth : (k * c * k⁻¹) * u * (k * c * k⁻¹)⁻¹ * u⁻¹ ∈
      conjSub k (quasithinOmegaOneCenter T) ⊓ quasithinOmegaOneCenter T := ⟨hZk u hu, hZ⟩
  rw [hZZ, Subgroup.mem_bot] at hboth
  exact hboth

theorem conjSub_U_le_centralizerMod (hcls : ClassAutShapeStmt) (h35 : Lemma1435)
    (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p)
    (h98 : HypF98 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H) {k : G}
    (hUkH : conjSub k (conjClosure (VZ T M) H) ≤ H)
    (hUle : conjClosure (VZ T M) H ≤ conjSub k H)
    (hZZ : conjSub k (quasithinOmegaOneCenter T) ⊓ quasithinOmegaOneCenter T = ⊥)
    {B : Subgroup G} (hBU : B ≤ conjClosure (VZ T M) H)
    (hK : conjSub k (uK T M H) ≤
      centralizerMod (quasithinOmegaOneCenter T) H B) :
    conjSub k (conjClosure (VZ T M) H) ≤ centralizerMod (quasithinOmegaOneCenter T) H B := by
  have hH : IsHTM T M H := hred.isHTM
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  obtain ⟨hsplit, -, -⟩ := shape_splitting h35 S hred h98
  have hstr := e9z4Str_of_shape hcls h35 S hred hshape h98
  have hZ : conjSub k (quasithinOmegaOneCenter T) ≤
      centralizerMod (quasithinOmegaOneCenter T) H B := by
    intro w hw
    have hwU : w ∈ conjSub k (conjClosure (VZ T M) H) :=
      conjSub_mono k (Z_le_conjClosure_VZ T M H) hw
    refine ⟨hUkH hwU, hHN (hUkH hwU), fun b hb => ?_⟩
    have := comm_conjSub_Z S hH hUle (hBU hb) hw
    have e : w * b * w⁻¹ * b⁻¹ = (b * w * b⁻¹ * w⁻¹)⁻¹ := by group
    rw [e, this, inv_one]
    exact (quasithinOmegaOneCenter T).one_mem
  intro w hw
  have hu₀ : k⁻¹ * w * k ∈ conjClosure (VZ T M) H := mem_conjSub.mp hw
  obtain ⟨uk, huk, c, hcU, hcH, z, hz, hdec⟩ := exists_decomp_UH h98.toHypF91 hsplit hstr hu₀
  have e : w = (k * uk * k⁻¹) * (k * c * k⁻¹) * (k * z * k⁻¹) := by
    have : w = k * (k⁻¹ * w * k) * k⁻¹ := by group
    rw [this, hdec]
    group
  have h1 : k * uk * k⁻¹ ∈ centralizerMod (quasithinOmegaOneCenter T) H B := by
    have : k * uk * k⁻¹ ∈ conjSub k (uK T M H ⊔ quasithinOmegaOneCenter T) := mul_mem_conjSub huk
    rw [conjSub_sup] at this
    exact (sup_le hK hZ) this
  have h2 : k * c * k⁻¹ ∈ centralizerMod (quasithinOmegaOneCenter T) H B := by
    have hx : k * c * k⁻¹ ∈ conjSub k (conjClosure (VZ T M) H) := mul_mem_conjSub hcU
    refine ⟨hUkH hx, hHN (hUkH hx), fun b hb => ?_⟩
    rw [comm_conjSub_c hcls h35 S hred hshape h98 hUkH hUle hZZ hcU hcH (hBU hb)]
    exact (quasithinOmegaOneCenter T).one_mem
  have h3 : k * z * k⁻¹ ∈ centralizerMod (quasithinOmegaOneCenter T) H B :=
    hZ (mul_mem_conjSub hz)
  rw [e]
  exact (centralizerMod (quasithinOmegaOneCenter T) H B).mul_mem
    ((centralizerMod (quasithinOmegaOneCenter T) H B).mul_mem h1 h2) h3

end Cen

end CFSG.Quasithin

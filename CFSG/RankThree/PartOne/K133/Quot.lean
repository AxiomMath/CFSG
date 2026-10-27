module

public import CFSG.RankThree.PartOne.K133.MaxItems
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K

theorem mulAut_eq_one_of_central {Q : Type*} [Group Q] (hQ : Group.IsPerfect Q) (α : MulAut Q)
    (h : ∀ q, q⁻¹ * α q ∈ Subgroup.center Q) : α = 1 := by
  let δ : Q →* Subgroup.center Q :=
    { toFun := fun q => ⟨q⁻¹ * α q, h q⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        have hc := Subgroup.mem_center_iff.1 (h x) y⁻¹
        show (x * y)⁻¹ * α (x * y) = x⁻¹ * α x * (y⁻¹ * α y)
        calc (x * y)⁻¹ * α (x * y) = y⁻¹ * (x⁻¹ * α x) * α y := by simp [mul_assoc]
          _ = x⁻¹ * α x * y⁻¹ * α y := by rw [hc]
          _ = x⁻¹ * α x * (y⁻¹ * α y) := by simp [mul_assoc] }
  have hker : commutator Q ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [hQ.commutator_eq_top] at hker
  ext q
  have hq : δ q = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top q))
  have := congrArg Subtype.val hq
  simp only [OneMemClass.coe_one] at this
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.1 this).symm

theorem isElementaryAbelian_range {G H : Type*} [Group G] [Group H] {p : ℕ} {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (φ : ↥E →* H) : IsElementaryAbelian p φ.range := by
  have hpow : ∀ x : ↥E, x ^ p = 1 := fun x => Subtype.ext (by
    have := hE
    exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) x.1 x.2)
  exact
    { toIsMulCommutative := ⟨⟨fun a b => by
        obtain ⟨x, hx⟩ := a.2
        obtain ⟨y, hy⟩ := b.2
        apply Subtype.ext
        show (a : H) * b = b * a
        rw [← hx, ← hy, ← map_mul, ← map_mul]
        exact congrArg φ (Subtype.ext (congrArg Subtype.val (hE.is_comm.comm x y)))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun y => by
        obtain ⟨x, hx⟩ := y.2
        apply Subtype.ext
        show (y : H) ^ p = 1
        rw [← hx, ← map_pow, hpow x, map_one] }

section Action

variable {G : Type} [Group G] (p : ℕ) {E J : Subgroup G}

@[expose] noncomputable def simpleQuotAction (hEJ : E ≤ Subgroup.normalizer (J : Set G)) :
    ↥E →* MulAut (SimpleQuot p J) :=
  (mulAutQuotientHom (Subgroup.center (↥J ⧸ aschbacherSolvableCore p ↥J))).comp
    (thetaQuotientAction p hEJ)

theorem ker_simpleQuotAction (hQ : Group.IsPerfect (↥J ⧸ aschbacherSolvableCore p ↥J))
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) (x : ↥E) :
    x ∈ (simpleQuotAction p hEJ).ker ↔ x ∈ (thetaQuotientAction p hEJ).ker := by
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx ⊢
    apply mulAut_eq_one_of_central hQ
    intro q
    have h1 := congrArg (fun φ : MulAut (SimpleQuot p J) =>
      φ ((q : ↥J ⧸ aschbacherSolvableCore p ↥J) :
        (↥J ⧸ aschbacherSolvableCore p ↥J) ⧸ Subgroup.center (↥J ⧸ aschbacherSolvableCore p ↥J))) hx
    simp only [simpleQuotAction, MonoidHom.comp_apply, mulAutQuotientHom_mk, MulAut.one_apply] at h1
    exact QuotientGroup.eq.1 h1.symm
  · intro hx
    rw [MonoidHom.mem_ker] at hx ⊢
    simp [simpleQuotAction, hx]

end Action

section Residue

theorem card_E_of_ne {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (hF : Sec12Facts G p A c L E) (hEA : E ≠ A) : Nat.card E = p ^ 4 := by
  obtain ⟨-, r, -, -, -, -, hrA, hr9⟩ := hF.three
  have hr9' : 9 ≤ r := by
    by_contra hlt
    exact hEA (hrA (by omega))
  exact hr9 hr9'

theorem KF133ResMaxAt.of_noRankThree {P : (X : Type) → [Group X] → Prop}
    (hP : ∀ (X : Type) [Group X] [Finite X], P X → ∀ p : ℕ, p.Prime → 5 ≤ p →
      ¬ ∃ Ē : Subgroup (MulAut X), IsElementaryAbelian p Ē ∧ Nat.card Ē = p ^ 3) :
    KF133ResMaxAt P := by
  intro G _ _ p A c L E h hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc hPJ
  exfalso
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have : Fact p.Prime := ⟨hp⟩
  have hbE : b ∈ E := (Subgroup.map_subtype_le _) hb
  have hEJ : E ≤ Subgroup.normalizer (J : Set G) :=
    h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components hbE hJ
  have hQ : Group.IsPerfect (↥J ⧸ aschbacherSolvableCore p ↥J) :=
    (isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hJ).1
  have hker : ((simpleQuotAction p hEJ).ker).map E.subtype = Subgroup.zpowers b := by
    rw [← hD, thetaQuotientCentralizer_eq_map_ker p hEJ]
    congr 1
    ext x
    exact ker_simpleQuotAction p hQ hEJ x
  have hbp : b ^ p = 1 := by
    have := h.E_elem
    exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) b hbE
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hcardker : Nat.card (simpleQuotAction p hEJ).ker = p := by
    rw [← Subgroup.card_map_of_injective E.subtype_injective (f := E.subtype), hker,
      Nat.card_zpowers, hbord]
  have hmul := Subgroup.card_ker_mul_card_range (simpleQuotAction p hEJ)
  rw [hcardker, card_E_of_ne hF hEA] at hmul
  have hcard3 : Nat.card (simpleQuotAction p hEJ).range = p ^ 3 := by
    have hp0 : 0 < p := hp.pos
    apply Nat.eq_of_mul_eq_mul_left hp0
    rw [hmul]
    ring
  exact hP _ hPJ p hp h5 ⟨_, isElementaryAbelian_range h.E_elem _, hcard3⟩

end Residue

end CFSG.RankThree.PartOne.K133

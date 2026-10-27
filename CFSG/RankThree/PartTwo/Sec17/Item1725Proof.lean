module

public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17Statements
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item148Solvable
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec17.Item17TailEnd
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

section General

variable {G : Type} [Group G]

theorem ne_of_ncard_eq_three {α : Type*} {a b c : α} (h : ({a, b, c} : Set α).ncard = 3) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨fun hab => ?_, fun hac => ?_, fun hbc => ?_⟩
  · subst hab
    rw [Set.insert_idem] at h
    have := Set.ncard_insert_le a ({c} : Set α)
    rw [Set.ncard_singleton] at this
    omega
  · subst hac
    rw [Set.insert_eq_of_mem (by simp : a ∈ ({b, a} : Set α))] at h
    have := Set.ncard_insert_le b ({a} : Set α)
    rw [Set.ncard_singleton] at this
    omega
  · subst hbc
    rw [Set.insert_eq_of_mem (by simp : b ∈ ({b} : Set α))] at h
    have := Set.ncard_insert_le a ({b} : Set α)
    rw [Set.ncard_singleton] at this
    omega

theorem le_normalizer_of_le_of_isMulCommutative {X H K : Subgroup G} (hX : IsMulCommutative X)
    (hH : H ≤ X) (hK : K ≤ X) : K ≤ Subgroup.normalizer (H : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hc : k * y = y * k := congrArg Subtype.val (hX.is_comm.comm ⟨k, hK hk⟩ ⟨y, hH hy⟩)
    rw [hc, mul_inv_cancel_right]
    exact hy
  · intro hy
    have hyX : y ∈ X := by
      have := X.mul_mem (X.mul_mem (X.inv_mem (hK hk)) (hH hy)) (hK hk)
      simpa [mul_assoc] using this
    have hc : k * y = y * k := congrArg Subtype.val (hX.is_comm.comm ⟨k, hK hk⟩ ⟨y, hyX⟩)
    rw [hc, mul_inv_cancel_right] at hy
    exact hy

theorem disjoint_sup_sup_of_isMulCommutative {ι : Type*} {X : Subgroup G}
    (hX : IsMulCommutative X) (f : ι → Subgroup G) (hf : ∀ i, f i ≤ X) (hind : iSupIndep f)
    {s t : Finset ι} (hst : Disjoint s t) : Disjoint (s.sup f) (t.sup f) := by
  classical
  let _ : CommGroup X := IsMulCommutative.instCommGroup
  set f' : ι → Subgroup X := fun i => (f i).subgroupOf X with hf'
  have hmap : ∀ i, (f' i).map X.subtype = f i := fun i => by
    rw [hf', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hf i)]
  have hsup : ∀ u : Finset ι, (u.sup f').map X.subtype = u.sup f := by
    intro u
    induction u using Finset.induction_on with
    | empty => simp
    | insert a u _ ih => rw [Finset.sup_insert, Finset.sup_insert, Subgroup.map_sup, hmap, ih]
  have hind' : iSupIndep f' := by
    rw [iSupIndep_def] at hind ⊢
    intro i
    rw [disjoint_iff]
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_inf_eq _ _ _ X.subtype_injective, Subgroup.map_bot]
    simp only [Subgroup.map_iSup, hmap]
    exact disjoint_iff.mp (hind i)
  have h := (hind'.supIndep' (s ∪ t)).disjoint_sup_sup Finset.subset_union_left
    Finset.subset_union_right hst
  rw [disjoint_iff] at h ⊢
  rw [← hsup s, ← hsup t, ← Subgroup.map_inf_eq _ _ _ X.subtype_injective, h, Subgroup.map_bot]

theorem mem_scriptQZero_of_inf_centralizer_eq_bot [Finite G] {A Q R : Subgroup G} {c : G}
    {LB : Subgroup G → Subgroup G} (hQ : Q ∈ scriptQ A LB) (hRQ : R ≤ Q)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hcA : c ∈ A)
    (hfix : R ⊓ Subgroup.centralizer ({c} : Set G) = ⊥) : R ∈ scriptQZero A LB := by
  refine ⟨mem_scriptQ_of_le hQ hRQ hAR, le_antisymm ?_ ?_⟩
  · have hcR : c ∈ Subgroup.normalizer (R : Set G) := hAR hcA
    have hmem : ∀ s : R, (s : G) * c * (s : G)⁻¹ * c⁻¹ ∈ R := fun s => by
      have h1 : c * (s : G)⁻¹ * c⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hcR _).mp (inv_mem s.2)
      have e : (s : G) * c * (s : G)⁻¹ * c⁻¹ = s * (c * (s : G)⁻¹ * c⁻¹) := by group
      rw [e]
      exact mul_mem s.2 h1
    let f : R → R := fun s => ⟨(s : G) * c * (s : G)⁻¹ * c⁻¹, hmem s⟩
    have hinj : Function.Injective f := by
      intro s t hst
      have h1 : (s : G) * c * (s : G)⁻¹ * c⁻¹ = t * c * (t : G)⁻¹ * c⁻¹ := congrArg Subtype.val hst
      have h2 : (t : G)⁻¹ * s ∈ R ⊓ Subgroup.centralizer ({c} : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem t.2) s.2,
          Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        calc (t : G)⁻¹ * s * c = (t : G)⁻¹ * ((s : G) * c * (s : G)⁻¹ * c⁻¹) * c * s := by group
          _ = (t : G)⁻¹ * (t * c * (t : G)⁻¹ * c⁻¹) * c * s := by rw [h1]
          _ = c * ((t : G)⁻¹ * s) := by group
      rw [hfix, Subgroup.mem_bot] at h2
      exact Subtype.ext (by rw [← mul_inv_cancel_left (t : G) s, h2, mul_one])
    have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
    intro r hr
    obtain ⟨s, hs⟩ := hsurj ⟨r, hr⟩
    have e : r = ⁅(s : G), c⁆ := by
      rw [commutatorElement_def]
      exact (congrArg Subtype.val hs).symm
    rw [e]
    exact Subgroup.commutator_mem_commutator s.2 hcA
  · rw [Subgroup.commutator_le]
    intro r hr a ha
    have h1 : a * r⁻¹ * a⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hAR ha) r⁻¹).mp (inv_mem hr)
    rw [commutatorElement_def]
    have e : r * a * r⁻¹ * a⁻¹ = r * (a * r⁻¹ * a⁻¹) := by group
    rw [e]
    exact mul_mem hr h1

end General

section Members

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G}

theorem Sec17Std.mem_scriptY1_of_not_le (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h : Sec17Std G A c L Y₀) {Y : Subgroup G}
    (hY : Y ∈ scriptY3 A (lB A)) (hM : ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G)) :
    Y ∈ scriptY1 A (lB A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := h.isE27
  have hYs : Group.IsSolvable ↥Y := by
    by_contra hns
    exact hM ((h166 Y₀ h.mem_y0Star).2 Y hY hns)
  have hYsc : Y ∈ scriptY A := hY.1.1
  have hYΔ : Y = delta A (lB A) Y := hY.2
  obtain ⟨hdelta, -, -⟩ := rank3II_14_5_lB hA hbot hYsc.2
  set R := pPrimeCoreOf 3 Y with hR
  set C' := xA A ⊓ Y with hC'
  have hDR : deltaZero A (lB A) Y ≤ R :=
    item148Solvable_of_mem_partTwoF h.mem_partTwoF Y hYsc hYs
  have hYRC : Y ≤ C' ⊔ R := by
    calc Y = delta A (lB A) Y := hYΔ
      _ = deltaZero A (lB A) Y ⊔ C' := hdelta
      _ ≤ R ⊔ C' := sup_le_sup_right hDR _
      _ = C' ⊔ R := sup_comm _ _
  have hC'R : C' ≤ Subgroup.normalizer (R : Set G) :=
    inf_le_right.trans (le_normalizer_pPrimeCoreOf 3 Y)
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    intro h3
    have hdvd := h3.trans ((Subgroup.card_dvd_of_le hYRC).trans (card_sup_dvd_card_mul hC'R))
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h1 | h1
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
        (h1.trans (Subgroup.card_dvd_of_le inf_le_left))
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y) h1
  refine ⟨hY, ?_⟩
  rw [oPrimeResidualOf_eq_closure, Subgroup.closure_eq_bot_iff]
  rintro x ⟨hxY, k, hk⟩
  have hdvd : orderOf (⟨x, hxY⟩ : Y) ∣ Nat.gcd (3 ^ k) (Nat.card Y) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk)))
      (orderOf_dvd_natCard _)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3)), Nat.dvd_one,
    orderOf_eq_one_iff] at hdvd
  exact congrArg Subtype.val hdvd

theorem Sec17Std.mem_scriptY3Star_of_not_le (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h : Sec17Std G A c L Y₀) {Y : Subgroup G}
    (hY : Y ∈ scriptY1Star A (lB A)) (hM : ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G)) :
    Y ∈ scriptY3Star A (lB A) := by
  refine ⟨hY.prop.1, fun Y' hY' hle => ?_⟩
  have hM' : ¬ Y' ≤ Subgroup.normalizer (Y₀ : Set G) := fun h' => hM (hle.trans h')
  exact hY.2 (h.mem_scriptY1_of_not_le h166 hbot hY' hM') hle

theorem Sec17W.yI_not_le (h : Sec17W G A c L Y₀ Y₁ S p P w Q) (i : ℕ) :
    ¬ yI Y₁ w i ≤ Subgroup.normalizer (Y₀ : Set G) := by
  intro hle
  apply h.not_le_M
  have hwM : w ^ (i - 1) ∈ Subgroup.normalizer (Y₀ : Set G) :=
    pow_mem (h.normalizer_le (Subgroup.mem_inf.mp h.w_mem).1) _
  intro y hy
  have h1 : w ^ (i - 1) * y * (w ^ (i - 1))⁻¹ ∈ Subgroup.normalizer (Y₀ : Set G) :=
    hle ⟨y, hy, rfl⟩
  have e : y = (w ^ (i - 1))⁻¹ * (w ^ (i - 1) * y * (w ^ (i - 1))⁻¹) * w ^ (i - 1) := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hwM) h1) hwM

theorem Sec17W.inf_centralizer_c_eq_bot' (h1724 : Item1724Three)
    (h : Sec17W G A c L Y₀ Y₁ S p P w Q) :
    Q ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ := by
  have h3 := h1724 G A c L Y₀ Y₁ S p P w Q h
  rw [eq_bot_iff, ← h3]
  refine inf_le_inf_left Q (le_trans ?_ h.normalizer_c_le)
  have hC : Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← hC]
  exact Subgroup.centralizer_le_normalizer _

end Members

section Steps

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G}

theorem Sec17WQ.eq_bot_of_le_inf (h1710 : Item1710 A (lB A)) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h1724 : Item1724Three)
    (h : Sec17WQ G A c L Y₀ Y₁ S p P w Q) {R : Subgroup G} (hRQ : R ≤ Q)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) {i j : ℕ}
    (hi : yI Y₁ w i ∈ scriptY1Star A (lB A)) (hj : yI Y₁ w j ∈ scriptY1Star A (lB A))
    (hij : yI Y₁ w i ≠ yI Y₁ w j) (hRi : R ≤ yI Y₁ w i) (hRj : R ≤ yI Y₁ w j) : R = ⊥ := by
  by_contra hR1
  have : Fact p.Prime := ⟨h.p_prime⟩
  have hQM := h1724 G A c L Y₀ Y₁ S p P w Q h.toSec17W
  have hRM : ¬ R ≤ Subgroup.normalizer (Y₀ : Set G) := fun hle =>
    hR1 (le_bot_iff.mp ((le_inf hRQ hle).trans hQM.le))
  have hR0 : R ∈ scriptQZero A (lB A) :=
    mem_scriptQZero_of_inf_centralizer_eq_bot h.mem_qStar_G.prop.1.1 hRQ hAR h.c_mem
      (le_bot_iff.mp ((inf_le_inf_right _ hRQ).trans
        (h.toSec17W.inf_centralizer_c_eq_bot' h1724).le))
  obtain ⟨Y, -, hYmin⟩ := Finite.exists_le_minimal (α := Subgroup G)
    (p := fun Y => R ≤ Y ∧ Y ≤ yI Y₁ w i ⊓ yI Y₁ w j) (a := yI Y₁ w i ⊓ yI Y₁ w j)
    ⟨le_inf hRi hRj, le_rfl⟩
  have hRf : R ≤ inSubgroup (oResidual 2) (deltaZero A (lB A) Y) := by
    rw [inSubgroup_oResidual_eq_closure]
    intro x hx
    refine Subgroup.subset_closure ⟨le_deltaZero hR0 hYmin.prop.1 hx, ?_⟩
    obtain ⟨k, hk⟩ := (h.isPGroup_Q.to_le hRQ) ⟨x, hx⟩
    have hdvd : orderOf x ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow h.p_prime).mp hdvd
    rw [hm]
    exact Nat.Coprime.pow_left m ((Nat.coprime_primes h.p_prime Nat.prime_two).mpr
      (by have := h.three_lt_p; omega))
  have hfY : inSubgroup (oResidual 2) (deltaZero A (lB A) Y) ≤ Y :=
    (inSubgroup_oResidual_le_self 2 _).trans (deltaZero_le Y)
  have hfeq : Y = inSubgroup (oResidual 2) (deltaZero A (lB A) Y) :=
    le_antisymm (hYmin.2 ⟨hRf, hfY.trans hYmin.prop.2⟩ hfY) hfY
  have hYM : ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G) := fun hle => hRM (hYmin.prop.1.trans hle)
  exact hij (h1710 Y₀ h.mem_y0Star Y hfeq hYM _
    (h.toSec17Std.mem_scriptY3Star_of_not_le h166 hbot hi (h.toSec17W.yI_not_le i)) _
    (h.toSec17Std.mem_scriptY3Star_of_not_le h166 hbot hj (h.toSec17W.yI_not_le j))
    (hYmin.prop.2.trans inf_le_left) (hYmin.prop.2.trans inf_le_right))

end Steps

end CFSG.RankThree.PartTwo.Sec17

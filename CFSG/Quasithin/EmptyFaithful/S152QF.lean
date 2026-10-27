module

public import CFSG.Quasithin.EmptyFaithful.S152QD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open scoped commutatorElement

@[expose] def IsF2RankTwoGroup (X : Type) [Group X] : Prop :=
  IsPSU 3 3 1 X ∨ IsPSL 4 2 1 X ∨ IsPSL 5 2 1 X ∨ IsTits X ∨ Is3D4 2 1 X

@[expose] def Cent3RankF2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsF2RankTwoGroup X → ∀ l : X, l * l = 1 → l ≠ 1 →
    ∀ P : Subgroup X, P ≤ Subgroup.centralizer ({l} : Set X) → Nat.card P = 9 →
      (∀ x ∈ P, x ^ 3 = 1) → False

variable {G : Type} [Group G] [Finite G]

private theorem le_of_exclusion (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    {I L P : Subgroup G} (hSQ : SQTKGroup ↥I) (hcomp : IsComponentIn L I)
    (hX : A318Exclusion ↥L) (hPI : P ≤ I) (hP3 : IsPGroup 3 P) : P ≤ L := by
  obtain ⟨q⟩ := quotPCore_equiv_of_simple hX.simple hX.three_dvd_card
  have hLq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hcomp
  have hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv q.symm hLq
  have hEq : L = oPrimeResidualOf 3 I :=
    eq_oPrimeResidualOf_three_of_exclusion hF h36 h38 hSQ (Id2519.mem_cComp_of_isComponentIn hcomp) hQ
      q hX
  intro x hx
  obtain ⟨k, hk⟩ : ∃ k : ℕ, orderOf x = 3 ^ k := by
    obtain ⟨n, hn⟩ := hP3 ⟨x, hx⟩
    have h1 : x ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨k, hk⟩
  rw [hEq]
  exact Subgroup.subset_closure ⟨hPI hx, k, hk⟩

private theorem false_of_caseA_f2 (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) (hc : Cent3RankF2) {I Mi L P : Subgroup G} {z : G}
    (hSQ : SQTKGroup ↥I) (hMi : Mi = I ⊓ Subgroup.centralizer ({z} : Set G))
    (hcomp : IsComponentIn L I) (hPM : P ≤ Mi) (hP3 : IsPGroup 3 P) (hP9 : Nat.card P = 9)
    (hPexp : ∀ x ∈ P, x ^ 3 = 1) (hz2 : z ^ 2 = 1) (hLz : ⁅L, Subgroup.zpowers z⁆ = L)
    (hF2 : IsF2RankTwoGroup ↥L) (hinn : InducesInner z L) : False := by
  have hX : A318Exclusion ↥L := by
    rcases hF2 with h | h | h | h | h
    exacts [hK.u33 _ h, hK.l42 _ h, hK.l52 _ h, hK.tits _ h, hK.d42 _ h]
  obtain ⟨l, hl, hact⟩ := hinn
  have hMiI : Mi ≤ I := by rw [hMi]; exact inf_le_left
  have hPL : P ≤ L := le_of_exclusion hF h36 h38 hSQ hcomp hX (hPM.trans hMiI) hP3
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : ↥L, l₀ = ⟨l, hl⟩ := ⟨_, rfl⟩
  have hl2 : ∀ x : ↥L, l₀⁻¹ * (l₀⁻¹ * x * l₀) * l₀ = x := by
    intro x
    have hx' : l⁻¹ * (x : G) * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) x.2) hl
    have h1 := hact (x : G) x.2
    have h2 := hact _ hx'
    have h3 : z⁻¹ * (z⁻¹ * (x : G) * z) * z = (x : G) := by
      rw [hzi]
      calc z * (z * (x : G) * z) * z = (z * z) * (x : G) * (z * z) := by group
        _ = (x : G) := by rw [hzz]; simp
    have h4 : z⁻¹ * (l⁻¹ * (x : G) * l) * z = (x : G) := by rw [← h1]; exact h3
    have h5 : (x : G) = l⁻¹ * (l⁻¹ * (x : G) * l) * l := h4.symm.trans h2
    rw [hl₀]
    exact Subtype.ext h5.symm
  have hgg : l₀ * l₀ = 1 := by
    have hcen : l₀ * l₀ ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro a
      have h2 : (l₀ * l₀)⁻¹ * a * (l₀ * l₀) = a := by
        calc (l₀ * l₀)⁻¹ * a * (l₀ * l₀) = l₀⁻¹ * (l₀⁻¹ * a * l₀) * l₀ := by group
          _ = a := hl2 a
      calc a * (l₀ * l₀) = (l₀ * l₀) * ((l₀ * l₀)⁻¹ * a * (l₀ * l₀)) := by group
        _ = (l₀ * l₀) * a := by rw [h2]
    rw [hX.center_eq_bot, Subgroup.mem_bot] at hcen
    exact hcen
  have hl1 : l₀ ≠ 1 := by
    intro h1
    have hl1' : l = 1 := by
      have := congrArg Subtype.val h1
      rw [hl₀] at this
      exact this
    have hcomm : ⁅L, Subgroup.zpowers z⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have h2 := hact x hx
      rw [hl1', inv_one, one_mul, mul_one, mul_assoc] at h2
      have h3 : x * z = z * x := inv_mul_eq_iff_eq_mul.mp h2
      exact (Commute.zpow_left (show Commute z x from h3.symm) n).eq
    rw [hLz] at hcomm
    exact Unc25G2.isComponentIn_ne_bot hcomp hcomm
  refine hc ↥L hF2 l₀ hgg hl1 (P.subgroupOf L) ?_ ?_ ?_
  · intro x hx
    have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hxMi : (x : G) ∈ I ⊓ Subgroup.centralizer ({z} : Set G) := hMi ▸ hPM hxP
    have hzx : z * (x : G) = (x : G) * z :=
      Subgroup.mem_centralizer_iff.mp hxMi.2 z (Set.mem_singleton z)
    have hxz : z⁻¹ * (x : G) * z = (x : G) := by rw [mul_assoc, ← hzx, inv_mul_cancel_left]
    have h1 : (x : G) = l⁻¹ * (x : G) * l := by
      have := hact (x : G) x.2
      rw [hxz] at this
      exact this
    have h2 : l * (x : G) = (x : G) * l := by
      calc l * (x : G) = l * (l⁻¹ * (x : G) * l) := by rw [← h1]
        _ = (x : G) * l := by group
    rw [hl₀]
    exact Subtype.ext h2
  · rw [← hP9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv
  · intro x hx
    have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
    exact Subtype.ext (by simpa using hPexp _ hxP)

@[expose] def Insp15224NoF2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Mi L L₀ P : Subgroup G) (z : G),
    SQTKGroup ↥I → oddCoreIn I = ⊥ → IsSylowTwoOf S I → z ∈ S →
    z ∈ Subgroup.centralizer (S : Set G) → z ^ 2 = 1 → z ≠ 1 →
    Mi = I ⊓ Subgroup.centralizer ({z} : Set G) → Mi ≠ I →
    (∀ J : Subgroup G, Mi ≤ J → J ≤ I → J = Mi ∨ J = I) →
    IsComponentIn L I → ¬ L ≤ Mi → ⁅L, Subgroup.zpowers z⁆ = L → Lemma115Cases L z →
    Lemma115LieCharTwo (↥L ⧸ Subgroup.center ↥L) →
    ¬ Lemma115CaseC L z →
    ¬ (Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∧ Lemma115CaseA L z) →
    ¬ (IsF2RankTwoGroup ↥L ∧ Lemma115CaseA L z) →
    L₀ = conjClosure L S → (L₀.subgroupOf I).Normal → I = L₀ ⊔ Mi →
    P ≤ Mi → IsPGroup 3 P → Nat.card P = 9 → (∀ x ∈ P, x ^ 3 = 1) → False

theorem insp15224NoA6_of_noF2 (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) (hc : Cent3RankF2) (hno : Insp15224NoF2) : Insp15224NoA6 := by
  intro G _ _ I S Mi L L₀ P z hSQ hO hS hzS hzC hz2 hz1 hMi hMiI hmax hcomp hLnot hLz hcases hlie
    hnC hnA hL₀ hL₀n hI hPM hP3 hP9 hPexp
  by_cases hF2 : IsF2RankTwoGroup ↥L ∧ Lemma115CaseA L z
  · exact false_of_caseA_f2 hF h36 h38 hK hc hSQ hMi hcomp hPM hP3 hP9 hPexp hz2 hLz hF2.1 hF2.2.2.2
  · exact hno G I S Mi L L₀ P z hSQ hO hS hzS hzC hz2 hz1 hMi hMiI hmax hcomp hLnot hLz hcases hlie
      hnC hnA hF2 hL₀ hL₀n hI hPM hP3 hP9 hPexp

end CFSG.Quasithin

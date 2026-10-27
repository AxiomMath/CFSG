module

public import CFSG.Quasithin.EmptyFaithful.Der6EMain
public import CFSG.Quasithin.EmptyFaithful.T1515eA
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux
import CFSG.Quasithin.EmptyFaithful.S152QDPack

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open scoped commutatorElement

theorem card_centralizer_swap_alt6 :
    ∀ i j : Fin 6, i ≠ j →
      Fintype.card {a : alternatingGroup (Fin 6) //
        (a : Equiv.Perm (Fin 6)) * Equiv.swap i j = Equiv.swap i j * (a : Equiv.Perm (Fin 6))} = 24 :=
  fun i j hij => S152QDPack.card_swap i j hij

theorem card_centralizer_invol_alt6 :
    ∀ g : alternatingGroup (Fin 6), g * g = 1 → g ≠ 1 →
      Fintype.card {a : alternatingGroup (Fin 6) //
        (a : Equiv.Perm (Fin 6)) * (g : Equiv.Perm (Fin 6)) =
          (g : Equiv.Perm (Fin 6)) * (a : Equiv.Perm (Fin 6))} = 8 :=
  fun g h2 h1 => S152QDPack.card_invol g h2 h1

@[expose] def altCentOf (σ : Equiv.Perm (Fin 6)) : Subgroup (alternatingGroup (Fin 6)) where
  carrier := {a | (a : Equiv.Perm (Fin 6)) * σ = σ * (a : Equiv.Perm (Fin 6))}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have ha' : Commute (a : Equiv.Perm (Fin 6)) σ := ha
    have hb' : Commute (b : Equiv.Perm (Fin 6)) σ := hb
    exact Commute.mul_left ha' hb'
  inv_mem' := fun {a} ha => by
    have ha' : Commute (a : Equiv.Perm (Fin 6)) σ := ha
    show Commute ((a⁻¹ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) σ
    rw [Subgroup.coe_inv]
    exact ha'.inv_left

theorem card_altCentOf_swap (i j : Fin 6) (hij : i ≠ j) :
    Nat.card ↥(altCentOf (Equiv.swap i j)) = 24 := by
  have h : Nat.card ↥(altCentOf (Equiv.swap i j)) = Nat.card {a : alternatingGroup (Fin 6) //
      (a : Equiv.Perm (Fin 6)) * Equiv.swap i j = Equiv.swap i j * (a : Equiv.Perm (Fin 6))} := rfl
  rw [h, Nat.card_eq_fintype_card]
  exact card_centralizer_swap_alt6 i j hij

theorem card_altCentOf_invol (g : alternatingGroup (Fin 6)) (h2 : g * g = 1) (h1 : g ≠ 1) :
    Nat.card ↥(altCentOf (g : Equiv.Perm (Fin 6))) = 8 := by
  have h : Nat.card ↥(altCentOf (g : Equiv.Perm (Fin 6))) = Nat.card {a : alternatingGroup (Fin 6) //
      (a : Equiv.Perm (Fin 6)) * (g : Equiv.Perm (Fin 6)) =
        (g : Equiv.Perm (Fin 6)) * (a : Equiv.Perm (Fin 6))} := rfl
  rw [h, Nat.card_eq_fintype_card]
  exact card_centralizer_invol_alt6 g h2 h1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem false_of_card_nine {L P : Subgroup G} (hPL : P ≤ L) (hP9 : Nat.card P = 9)
    {X : Type} [Group X] (e : ↥L ≃* X) (C : Subgroup X) (hC : ¬ 9 ∣ Nat.card C)
    (hPC : ∀ (x : G) (hx : x ∈ P), e ⟨x, hPL hx⟩ ∈ C) : False := by
  have hcardQ : Nat.card ((P.subgroupOf L).map e.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective e.injective, ← hP9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv
  have hle : (P.subgroupOf L).map e.toMonoidHom ≤ C := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ P := Subgroup.mem_subgroupOf.mp hy
    exact hPC y hy'
  exact hC (hcardQ ▸ Subgroup.card_dvd_of_le hle)

private theorem le_of_a6 (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h6 : A318Exclusion (alternatingGroup (Fin 6))) {I L P : Subgroup G} (hSQ : SQTKGroup ↥I)
    (hcomp : IsComponentIn L I) (e : ↥L ≃* alternatingGroup (Fin 6)) (hPI : P ≤ I)
    (hP3 : IsPGroup 3 P) : P ≤ L := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := h6.simple
  have hsimple : IsSimpleGroup ↥L := e.isSimpleGroup
  have h3 : 3 ∣ Nat.card ↥L := by
    rw [Nat.card_congr e.toEquiv]
    exact h6.three_dvd_card
  obtain ⟨q⟩ := quotPCore_equiv_of_simple hsimple h3
  have hLq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hcomp
  have hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv q.symm hLq
  have hEq : L = oPrimeResidualOf 3 I :=
    eq_oPrimeResidualOf_three_of_exclusion hF h36 h38 hSQ (Id2519.mem_cComp_of_isComponentIn hcomp) hQ
      (q.trans e) h6
  intro x hx
  obtain ⟨k, hk⟩ : ∃ k : ℕ, orderOf x = 3 ^ k := by
    obtain ⟨n, hn⟩ := hP3 ⟨x, hx⟩
    have h1 : x ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨k, hk⟩
  rw [hEq]
  exact Subgroup.subset_closure ⟨hPI hx, k, hk⟩

private theorem false_of_caseC (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h6 : A318Exclusion (alternatingGroup (Fin 6))) {I Mi L P : Subgroup G} {z : G}
    (hSQ : SQTKGroup ↥I) (hO : oddCoreIn I = ⊥) (hMi : Mi = I ⊓ Subgroup.centralizer ({z} : Set G))
    (hcomp : IsComponentIn L I) (hPM : P ≤ Mi) (hP3 : IsPGroup 3 P) (hP9 : Nat.card P = 9)
    (hC : Lemma115CaseC L z) : False := by
  obtain ⟨φ, σ, hZ, hσ, -, hact⟩ := hC
  have hcen : Subgroup.center ↥L = ⊥ := by
    rcases hZ with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥L)) 3 (by rw [h3])
      have hyG : orderOf (((y : ↥(Subgroup.center ↥L)) : ↥L) : G) = 3 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
      have hyc : ∀ w ∈ L, w * (((y : ↥(Subgroup.center ↥L)) : ↥L) : G) =
          (((y : ↥(Subgroup.center ↥L)) : ↥L) : G) * w := fun w hw =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp y.2 ⟨w, hw⟩)
      have hmem := Unc25G2.mem_oddCoreIn_of_central_odd hcomp (((y : ↥(Subgroup.center ↥L)) : ↥L)).2
        hyc (by rw [hyG]; decide)
      rw [hO, Subgroup.mem_bot] at hmem
      rw [hmem, orderOf_one] at hyG
      omega
  let e₀ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  let e : ↥L ≃* alternatingGroup (Fin 6) := e₀.symm.trans φ
  have he : ∀ x : ↥L, e x = φ (QuotientGroup.mk x) := fun x => rfl
  have hMiI : Mi ≤ I := by rw [hMi]; exact inf_le_left
  have hPL : P ≤ L := le_of_a6 hF h36 h38 h6 hSQ hcomp e (hPM.trans hMiI) hP3
  obtain ⟨i, j, hij, rfl⟩ := hσ
  refine false_of_card_nine hPL hP9 e (altCentOf (Equiv.swap i j)) ?_ ?_
  · rw [card_altCentOf_swap i j hij]
    omega
  · intro x hx
    have hxMi : x ∈ I ⊓ Subgroup.centralizer ({z} : Set G) := hMi ▸ hPM hx
    have hzx : z * x = x * z := Subgroup.mem_centralizer_iff.mp hxMi.2 z (Set.mem_singleton z)
    have hy : ((⟨x, hPL hx⟩ : ↥L) : G) = z⁻¹ * ((⟨x, hPL hx⟩ : ↥L) : G) * z := by
      show x = z⁻¹ * x * z
      rw [mul_assoc, ← hzx, inv_mul_cancel_left]
    have h1 := hact ⟨x, hPL hx⟩ ⟨x, hPL hx⟩ hy
    rw [← he] at h1
    show ((e ⟨x, hPL hx⟩ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) * Equiv.swap i j =
      Equiv.swap i j * ((e ⟨x, hPL hx⟩ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))
    set a : Equiv.Perm (Fin 6) := ((e ⟨x, hPL hx⟩ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))
      with ha
    have h2 : Equiv.swap i j * a = a * Equiv.swap i j := by
      calc Equiv.swap i j * a = Equiv.swap i j * (( Equiv.swap i j)⁻¹ * a * Equiv.swap i j) := by
            rw [← h1]
        _ = a * Equiv.swap i j := by group
    exact h2.symm

private theorem false_of_caseA_alt6 (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h6 : A318Exclusion (alternatingGroup (Fin 6))) {I Mi L P : Subgroup G} {z : G}
    (hSQ : SQTKGroup ↥I) (hMi : Mi = I ⊓ Subgroup.centralizer ({z} : Set G))
    (hcomp : IsComponentIn L I) (hPM : P ≤ Mi) (hP3 : IsPGroup 3 P) (hP9 : Nat.card P = 9)
    (hz2 : z ^ 2 = 1) (hLz : ⁅L, Subgroup.zpowers z⁆ = L) (e : ↥L ≃* alternatingGroup (Fin 6))
    (hinn : InducesInner z L) : False := by
  obtain ⟨l, hl, hact⟩ := hinn
  have hMiI : Mi ≤ I := by rw [hMi]; exact inf_le_left
  have hPL : P ≤ L := le_of_a6 hF h36 h38 h6 hSQ hcomp e (hPM.trans hMiI) hP3
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : ↥L, l₀ = ⟨l, hl⟩ := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : alternatingGroup (Fin 6), g = e l₀ := ⟨_, rfl⟩
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
  have hgg : g * g = 1 := by
    have hc : g * g ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro a
      have h1 := congrArg e (hl2 (e.symm a))
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, ← hg] at h1
      have h2 : (g * g)⁻¹ * a * (g * g) = a := by
        calc (g * g)⁻¹ * a * (g * g) = g⁻¹ * (g⁻¹ * a * g) * g := by group
          _ = a := h1
      calc a * (g * g) = (g * g) * ((g * g)⁻¹ * a * (g * g)) := by group
        _ = (g * g) * a := by rw [h2]
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
    exact hc
  have hg1 : g ≠ 1 := by
    intro h1
    have hl1 : l₀ = 1 := e.injective (by rw [← hg, h1, map_one])
    have hl1' : l = 1 := by
      have := congrArg Subtype.val hl1
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
  refine false_of_card_nine hPL hP9 e (altCentOf (g : Equiv.Perm (Fin 6))) ?_ ?_
  · rw [card_altCentOf_invol g hgg hg1]
    omega
  · intro x hx
    have hxMi : x ∈ I ⊓ Subgroup.centralizer ({z} : Set G) := hMi ▸ hPM hx
    have hzx : z * x = x * z := Subgroup.mem_centralizer_iff.mp hxMi.2 z (Set.mem_singleton z)
    have hxz : z⁻¹ * x * z = x := by rw [mul_assoc, ← hzx, inv_mul_cancel_left]
    have h1 : x = l⁻¹ * x * l := by
      have := hact x (hPL hx)
      rw [hxz] at this
      exact this
    have h2 : l * x = x * l := by
      calc l * x = l * (l⁻¹ * x * l) := by rw [← h1]
        _ = x * l := by group
    have h3 : l₀ * ⟨x, hPL hx⟩ = ⟨x, hPL hx⟩ * l₀ := by
      rw [hl₀]
      exact Subtype.ext h2
    have h4 := congrArg (fun w : ↥L => ((e w : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) h3
    simp only [map_mul, Subgroup.coe_mul, ← hg] at h4
    exact h4.symm

@[expose] def Insp15224NoA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Mi L L₀ P : Subgroup G) (z : G),
    SQTKGroup ↥I → oddCoreIn I = ⊥ → IsSylowTwoOf S I → z ∈ S →
    z ∈ Subgroup.centralizer (S : Set G) → z ^ 2 = 1 → z ≠ 1 →
    Mi = I ⊓ Subgroup.centralizer ({z} : Set G) → Mi ≠ I →
    (∀ J : Subgroup G, Mi ≤ J → J ≤ I → J = Mi ∨ J = I) →
    IsComponentIn L I → ¬ L ≤ Mi → ⁅L, Subgroup.zpowers z⁆ = L → Lemma115Cases L z →
    Lemma115LieCharTwo (↥L ⧸ Subgroup.center ↥L) →
    ¬ Lemma115CaseC L z →
    ¬ (Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∧ Lemma115CaseA L z) →
    L₀ = conjClosure L S → (L₀.subgroupOf I).Normal → I = L₀ ⊔ Mi →
    P ≤ Mi → IsPGroup 3 P → Nat.card P = 9 → (∀ x ∈ P, x ^ 3 = 1) → False

theorem insp15224_of_noA6 (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (h6 : A318Exclusion (alternatingGroup (Fin 6))) (hno : Insp15224NoA6) : Insp15224 := by
  intro G _ _ I S Mi L L₀ P z hSQ hO hS hzS hzC hz2 hz1 hMi hMiI hmax hcomp hLnot hLz hcases hlie
    hL₀ hL₀n hI hPM hP3 hP9 hPexp
  by_cases hC : Lemma115CaseC L z
  · exact false_of_caseC hF h36 h38 h6 hSQ hO hMi hcomp hPM hP3 hP9 hC
  by_cases hA : Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∧ Lemma115CaseA L z
  · obtain ⟨⟨e⟩, hAc⟩ := hA
    exact false_of_caseA_alt6 hF h36 h38 h6 hSQ hMi hcomp hPM hP3 hP9 hz2 hLz e hAc.2.2
  · exact hno G I S Mi L L₀ P z hSQ hO hS hzS hzC hz2 hz1 hMi hMiI hmax hcomp hLnot hLz hcases hlie
      hC hA hL₀ hL₀n hI hPM hP3 hP9 hPexp

end CFSG.Quasithin

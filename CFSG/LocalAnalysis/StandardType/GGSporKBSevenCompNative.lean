module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenJ
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenJQuasi
public import CFSG.LocalAnalysis.StandardType.GGSporKBSevenCompAt
public import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportA
import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.HardMathSupport.Dickson.BMRows.CensusB7
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenCensus
public import CFSG.Sporadic.Bridge.BBound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenElements

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

@[expose] noncomputable def jB7 : Subgroup NativeSporadic.B :=
  Subgroup.closure {yB7, eB7}

private theorem wordProd_img2_mem_closure {G : Type*} [Group G] (g h : G)
    (w : List (ℕ × Bool)) : wordProd (img2 g h) w ∈ Subgroup.closure ({g, h} : Set G) := by
  induction w with
  | nil => simpa [wordProd] using Subgroup.one_mem _
  | cons l w ih =>
    have e : wordProd (img2 g h) (l :: w) =
        (if l.2 then img2 g h l.1 else (img2 g h l.1)⁻¹) * wordProd (img2 g h) w := by
      simp only [wordProd, List.map_cons, List.prod_cons]
    rw [e]
    refine Subgroup.mul_mem _ ?_ ih
    have hl : img2 g h l.1 ∈ Subgroup.closure ({g, h} : Set G) := by
      unfold img2
      split_ifs <;> exact Subgroup.subset_closure (by simp)
    split_ifs
    · exact hl
    · exact Subgroup.inv_mem _ hl

private theorem not_mem_zpowers_of_sq {G : Type*} [Group G] {a u : G} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hu1 : u ≠ 1) (hua : u ≠ a) : u ∉ Subgroup.zpowers a := by
  intro h
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  have hord : orderOf a = 2 := orderOf_eq_prime (by rwa [sq]) ha1
  have hk : a ^ k = a ^ (k % 2) := by
    have := zpow_mod_orderOf a k
    rw [hord] at this
    simpa using this.symm
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · exact hu1 (by rw [hk, h0]; simp)
  · exact hua (by rw [hk, h1]; simp)

private theorem isQuasisimple_of_assembly {J : Type*} [Group J]
    (h : CFSG.Assembly.IsQuasisimple J) (hz : Nat.card (Subgroup.center J) = 2)
    (hc : Nat.card J = 40320) : CFSG.IsQuasisimple J := by
  refine ⟨⟨h.1⟩, h.2, ?_⟩
  by_contra hne
  push Not at hne
  haveI : Finite J := Nat.finite_of_card_ne_zero (by omega)
  haveI := h.2
  letI : CommGroup (J ⧸ Subgroup.center J) :=
    { (inferInstance : Group (J ⧸ Subgroup.center J)) with mul_comm := hne }
  have hp := IsSimpleGroup.prime_card (α := J ⧸ Subgroup.center J)
  have hcard : Nat.card (J ⧸ Subgroup.center J) = 20160 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center J)
    rw [hc, hz] at h1
    omega
  rw [hcard] at hp
  norm_num at hp

theorem jB7_facts :
    jB7 ≤ Subgroup.centralizer {xB7} ∧ CFSG.IsQuasisimple ↥jB7 ∧
      Nat.card ↥(Subgroup.center ↥jB7) = 2 ∧ Nat.card ↥jB7 = 40320 := by
  have hE := b7E_parts
  have hP := b7J_parts
  have hclos : Subgroup.closure ({yB7, eB7} : Set NativeSporadic.B) =
      Subgroup.closure ({uB7, vB7} : Set NativeSporadic.B) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · have hy : yB7 = vB7 ^ 2 := by
          have h1 : yB7 ^ 6 = yB7 := by
            rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, hP.y_pow, one_mul]
          calc yB7 = yB7 ^ 6 := h1.symm
            _ = vB7 ^ 2 := by rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul]; rfl
        rw [hy]
        exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
      · rw [← hP.e_word]
        exact wordProd_img2_mem_closure uB7 vB7 _
    · rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact wordProd_img2_mem_closure yB7 eB7 _
      · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 3
  obtain ⟨hq, hz, hc⟩ := quasisimple_closure_of_cover (a := a0B7) (e := eB7) (y := yB7)
    (u := uB7) (v := vB7) hclos hP.a_sq hE.ne_one_a hE.comm_a_y hE.comm_a_e hP.y_pow hP.e_pow
    hP.seven hP.rels_mem (not_mem_zpowers_of_sq hP.a_sq hE.ne_one_a hP.u_ne_one hP.u_ne_a)
  refine ⟨?_, isQuasisimple_of_assembly hq hz hc, hz, hc⟩
  rw [jB7, Subgroup.closure_le]
  rintro z (rfl | rfl)
  · exact (Subgroup.mem_centralizer_singleton_iff).2 hE.comm_x_y.symm
  · exact (Subgroup.mem_centralizer_singleton_iff).2 hE.comm_e_x

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem bSevenComp_of_conj_class {K : Type} [Group K] [Finite K] {x₀ : K}
    (hx₀ : orderOf x₀ = 7) (hconj : ∀ x : K, orderOf x = 7 → IsConj x₀ x)
    {J : Subgroup K} (hJle : J ≤ Subgroup.centralizer {x₀}) (hJq : IsQuasisimple ↥J)
    (hJz : Nat.card ↥(Subgroup.center ↥J) = 2) (hJcard : Nat.card ↥J = 40320)
    (hcard : ∀ x : K, orderOf x = 7 →
      Nat.card ↥(Subgroup.centralizer ({x} : Set K)) ∣ 564480)
    (hcore : ∀ x : K, orderOf x = 7 →
      Nat.card ↥(LargeEvenPPrimeCore 7 ↥(Subgroup.centralizer ({x} : Set K))) ≤ 2) :
    BSevenComp K := by
  intro x hx
  obtain ⟨g, hg⟩ := isConj_iff.mp (hconj x hx)
  let φ : K ≃* K := MulAut.conj g
  have hφx : φ x₀ = x := by simpa [φ, MulAut.conj_apply] using hg
  let Jx : Subgroup K := Subgroup.map φ.toMonoidHom J
  let e : ↥Jx ≃* ↥J := (Subgroup.equivMapOfInjective J φ.toMonoidHom φ.injective).symm
  have hle : Jx ≤ Subgroup.centralizer {x} := by
    rintro _ ⟨j, hj, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := (Subgroup.mem_centralizer_singleton_iff).1 (hJle hj)
    rw [← hφx]
    simpa only [MulEquiv.coe_toMonoidHom, map_mul] using congrArg φ h1
  have hq : IsQuasisimple ↥Jx := CFSG.IsQuasisimple.of_mulEquiv e hJq
  have hz : Nat.card ↥(Subgroup.center ↥Jx) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hJz
  have hc : Nat.card ↥Jx = 40320 := by
    rw [Subgroup.card_map_of_injective φ.injective]
    exact hJcard
  exact bSevenCompAt_of_quasisimple hx hle hq hz hc (hcard x hx) (hcore x hx)

theorem bSevenComp_native
    [Finite NativeSporadic.B] : BSevenComp NativeSporadic.B := by
  obtain ⟨hJle, hJq, hJz, hJcard⟩ := jB7_facts
  refine bSevenComp_of_conj_class b7E_parts.order_x
    (fun x hx => bSeven_isConj b7E_parts.order_x hx) hJle hJq hJz hJcard
    (fun x hx => CFSG.HardMathSupport.Dickson.BMRows.card_centralizer_seven_B_dvd x hx)
    (fun x hx => ?_)
  have h1 := BSeven.oPrimeCoreLeTwoAt_B_seven x hx
  have e1 : Nat.card (CFSG.Open.GLAPPrimeCoreOf 7
      (Subgroup.centralizer ({x} : Set NativeSporadic.B))) =
      Nat.card ↥(LargeEvenPPrimeCore 7 ↥(Subgroup.centralizer ({x} : Set NativeSporadic.B))) :=
    Subgroup.card_map_of_injective (Subgroup.centralizer _).subtype_injective
  rw [← e1]
  exact h1

theorem ggSporK_bSevenComp_B
    [Finite (TauCeti.CFSGIndex.sporadic .B).Group] :
    BSevenComp (TauCeti.CFSGIndex.sporadic .B).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
  let e' : NativeSporadic.B ≃* (TauCeti.CFSGIndex.sporadic .B).Group :=
    e.trans (MulEquiv.refl _)
  haveI : Finite NativeSporadic.B := Finite.of_equiv _ e'.symm.toEquiv
  exact @bSevenComp_of_mulEquiv NativeSporadic.B (TauCeti.CFSGIndex.sporadic .B).Group
    _ _ _ _ e' bSevenComp_native

end CFSG.StandardType.SporadicShape

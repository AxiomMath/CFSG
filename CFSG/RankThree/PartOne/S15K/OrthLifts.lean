module

public import CFSG.RankThree.PartOne.S15K.AutTorus
public import CFSG.RankThree.PartOne.S15K.OutBound
public import CFSG.RankThree.PartOne.S12.Facts13
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessBridge
public import CFSG.RankThree.PartOne.S12.Equivariance

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Classical2 CFSG.ComponentClassification Module

variable {G : Type} [Group G] [Finite G]

theorem orth_lifts {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (h13 : Sec13Facts G p A c L E) (hEA : E = A)
    {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hOut : OutStructure.OutPNice p (ProjOrthDerived Q))
    (hpI : p ∣ Nat.card (lieGenerated p E)) (φ : ↥(lieGenerated p E) ≃* ProjOrthDerived Q) :
    ∃ a : ↥E → ProjOrthDerived Q, (∀ e, a e ^ p = 1) ∧
      (∀ e : ↥E, MulAut.conj (a e) =
        actP φ ⟨(e : G), E_le_normalizer_lieGenerated h.prime e.2⟩) ∧
      (∀ e e' : ↥E, a e * a e' = a e' * a e) ∧ (∀ e : ↥E, e ≠ 1 → orderOf (a e) = p) ∧
      (∀ e e' : ↥E, a (e * e') = a e * a e') := by
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hEI : E ≤ Subgroup.normalizer (lieGenerated p E : Set G) :=
    E_le_normalizer_lieGenerated hp
  have hWI : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (lieGenerated p E : Set G) :=
    torusNormalizer_le_lieNormalizer hp E
  have hE : IsElementaryAbelian p E := h.E_elem
  have hEcard : p < Nat.card E := by
    have h3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
    rw [h3]
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hTcenter : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top b) a)
  have hTinj : Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
    KCOrthogonalD4.conj_injective_of_trivial_center hTcenter
  have hZ : lieGenerated p E ⊓ Subgroup.centralizer (lieGenerated p E : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxI : x ∈ lieGenerated p E := hx.1
    have hxc := hx.2
    have h1 : φ ⟨x, hxI⟩ ∈ Subgroup.center (ProjOrthDerived Q) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨y, rfl⟩ := φ.surjective z
      have := Subgroup.mem_centralizer_iff.1 hxc (y : G) y.2
      rw [← map_mul, ← map_mul]
      exact congrArg φ (Subtype.ext this)
    rw [hTcenter, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val (φ.injective (h1.trans (map_one φ).symm))
  have hfaith : E ⊓ Subgroup.centralizer (lieGenerated p E : Set G) = ⊥ :=
    centralizer_inf_eq_bot hp h.E_max_global hWI h13.irreducible hZ hpI
  have hEexp : ∀ e ∈ E, e ^ p = 1 := fun e he =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he
  have hEexp' : ∀ e : ↥E, e ^ p = 1 := fun e => Subtype.ext (hEexp e e.2)
  have hN : (OuterAutomorphisms.inner (ProjOrthDerived Q)).Normal :=
    OuterAutomorphisms.inner_normal _
  have hbound : ∀ ρ : ↥E →* MulAut (ProjOrthDerived Q),
      (∀ e : ↥E, ρ e ∈ OuterAutomorphisms.inner (ProjOrthDerived Q) → e = 1) →
        Nat.card ↥E ≤ p := fun ρ hρ => by
    have : Finite (ProjOrthDerived Q) := inferInstance
    exact card_le_of_outPNice hp hOut ρ hρ
  have hinn := actP_mem_normal_of_bound φ hEI hWI hEcard h13.irreducible
    (OuterAutomorphisms.inner (ProjOrthDerived Q)) hN hbound
  have hpow : ∀ e : ↥E, (actP φ ⟨(e : G), hEI e.2⟩) ^ p = 1 := by
    intro e
    rw [← map_pow]
    have : (⟨(e : G), hEI e.2⟩ : ↥(Subgroup.normalizer (lieGenerated p E : Set G))) ^ p = 1 :=
      Subtype.ext (hEexp e e.2)
    rw [this, map_one]
  have hne : ∀ e : ↥E, e ≠ 1 → actP φ ⟨(e : G), hEI e.2⟩ ≠ 1 := by
    intro e he h1
    have hc := mem_centralizer_of_actP_eq_one φ h1
    have hmem : (e : G) ∈ E ⊓ Subgroup.centralizer (lieGenerated p E : Set G) := ⟨e.2, hc⟩
    rw [hfaith, Subgroup.mem_bot] at hmem
    exact he (Subtype.ext hmem)
  have hlift : ∀ e : ↥E, ∃ y : ProjOrthDerived Q,
      MulAut.conj y = actP φ ⟨(e : G), hEI e.2⟩ := fun e => hinn e
  choose a hac using hlift
  have hap : ∀ e : ↥E, a e ^ p = 1 := by
    intro e
    apply hTinj
    rw [map_pow, hac, hpow e, map_one]
  refine ⟨a, hap, hac, fun e e' => ?_, fun e he => ?_, fun e e' => ?_⟩
  · have hcomm_act : actP φ ⟨(e : G), hEI e.2⟩ * actP φ ⟨(e' : G), hEI e'.2⟩ =
        actP φ ⟨(e' : G), hEI e'.2⟩ * actP φ ⟨(e : G), hEI e.2⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      have hcomm : (e : G) * e' = e' * e := congrArg Subtype.val (hE.is_comm.comm e e')
      exact Subtype.ext hcomm
    have h1 : MulAut.conj (a e * a e' * (a e)⁻¹) = MulAut.conj (a e') := by
      simp only [map_mul, map_inv, hac]
      rw [hcomm_act, mul_inv_cancel_right]
    have h2 : a e * a e' * (a e)⁻¹ = a e' := hTinj h1
    exact mul_inv_eq_iff_eq_mul.1 h2
  · have : Fact p.Prime := ⟨hp⟩
    have ha1 : a e ≠ 1 := by
      intro h1
      apply hne e he
      rw [← hac e, h1, map_one]
    exact orderOf_eq_prime (hap e) ha1
  · apply hTinj
    rw [map_mul, hac, hac, hac, ← map_mul]
    rfl

end CFSG.RankThree.PartOne.S15K

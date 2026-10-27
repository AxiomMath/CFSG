module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2QuotientTorusCard
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The reflection attached to the Section 4 quotient torus

This module packages the reflected-dihedral structure carried by
`SecondCasePSL2QuotientTorusCard`: the chosen torus in `E / Z(E)` admits an
involutory reflection which inverts it, and the centralizer of the quotient
involution is exactly the resulting reflected join.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The exact reflected-dihedral structure on the chosen quotient torus. -/
public theorem secondCase_psl2_quotient_torus_reflection
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (torus : SecondCasePSL2QuotientTorusCard d K) :
    let Q : Type u := d.E ⧸ Subgroup.center d.E
    let tQ : Q :=
      QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩
    ∃ s : Q,
      IsInvolution s ∧ s ∉ torus.T ∧
      (∀ x : Q, x ∈ torus.T → s * x * s⁻¹ = x⁻¹) ∧
      Subgroup.centralizer ({tQ} : Set Q) =
        torus.T ⊔ Subgroup.zpowers s := by
  classical
  let Q : Type u := d.E ⧸ Subgroup.center d.E
  let q : d.E →* Q := QuotientGroup.mk' (Subgroup.center d.E)
  let tQ : Q := q ⟨c.t, d.t_mem_E⟩
  change ∃ s : Q,
    IsInvolution s ∧ s ∉ torus.T ∧
    (∀ x : Q, x ∈ torus.T → s * x * s⁻¹ = x⁻¹) ∧
    Subgroup.centralizer ({tQ} : Set Q) =
      torus.T ⊔ Subgroup.zpowers s
  have htQ : IsInvolution tQ := by
    have htE : IsInvolution (⟨c.t, d.t_mem_E⟩ : d.E) := by
      constructor
      · intro h1
        exact c.t_involution.1 (congrArg Subtype.val h1)
      · apply Subtype.ext
        simpa [pow_two] using c.t_involution.2
    change IsInvolution
      (QuotientGroup.mk' (Subgroup.center d.E) ⟨c.t, d.t_mem_E⟩)
    exact quotient_involution_of_involution
      (Subgroup.center d.E) d.center_odd htE
  let e : Q ≃* PSL2 K := torus.modelEquiv.some
  let tP : PSL2 K := e tQ
  have htP : IsInvolution tP := by
    constructor
    · intro h1
      apply htQ.1
      simpa [tP] using congrArg (e.symm : PSL2 K → Q) h1
    · simpa using congrArg e htQ.2
  obtain ⟨T0, s0, hT0cyc, htP_T0, hs0I, hs0_not_T0, hinvT0, hC0⟩ :=
    psl2_reflected_join (K := K) torus.primePower htP
  let T0Q : Subgroup Q := T0.map e.symm.toMonoidHom
  let s0Q : Q := e.symm s0
  have hT0Qcyc : IsCyclic T0Q := by
    let eT : T0 ≃* T0Q := Subgroup.equivMapOfInjective T0
      e.symm.toMonoidHom e.symm.injective
    exact (MulEquiv.isCyclic eT).mp hT0cyc
  have htQ_T0Q : tQ ∈ T0Q := by
    exact Subgroup.mem_map.mpr ⟨tP, htP_T0, by
      simp [tP]⟩
  have hs0Q_I : IsInvolution s0Q := by
    constructor
    · intro h1
      apply hs0I.1
      have h : e.symm s0 = 1 := by simpa [s0Q] using h1
      have h' := congrArg e h
      simpa using h'
    · calc
        s0Q ^ 2 = e.symm.toMonoidHom (s0 ^ 2) := by
          simp [s0Q, map_pow]
        _ = 1 := by rw [hs0I.2]; simp
  have hs0Q_not_T0Q : s0Q ∉ T0Q := by
    intro hsT
    rcases Subgroup.mem_map.mp hsT with ⟨y, hyT0, hyeq⟩
    have hy_eq : y = s0 := by
      apply e.symm.injective
      calc
        e.symm y = s0Q := hyeq
        _ = e.symm s0 := rfl
    exact hs0_not_T0 (by simpa [hy_eq] using hyT0)
  have hinvT0Q : ∀ x : Q, x ∈ T0Q → s0Q * x * s0Q⁻¹ = x⁻¹ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyT0, hx_eq⟩
    calc
      s0Q * x * s0Q⁻¹ = e.symm.toMonoidHom (s0 * y * s0⁻¹) := by
        rw [← hx_eq]
        dsimp [s0Q]
        rw [e.symm.map_mul, e.symm.map_mul, e.symm.map_inv]
      _ = e.symm.toMonoidHom (y⁻¹) := by rw [hinvT0 y hyT0]
      _ = (e.symm.toMonoidHom y)⁻¹ := by rw [e.symm.toMonoidHom.map_inv]
      _ = x⁻¹ := by rw [hx_eq]
  have hC0Q : Subgroup.centralizer ({tQ} : Set Q) =
      T0Q ⊔ Subgroup.zpowers s0Q := by
    have hCmap :
        (Subgroup.centralizer ({tP} : Set (PSL2 K))).map e.symm.toMonoidHom =
          Subgroup.centralizer ({tQ} : Set Q) := by
      ext y
      constructor
      · intro hy
        rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hcomm : x * tP = tP * x :=
          Subgroup.mem_centralizer_singleton_iff.mp hx
        apply e.injective
        calc
          e (e.symm x * tQ) = x * tP := by simp [tP]
          _ = tP * x := hcomm
          _ = e (tQ * e.symm x) := by simp [tP]
      · intro hy
        have hx : e y ∈ Subgroup.centralizer ({tP} : Set (PSL2 K)) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hcomm : y * tQ = tQ * y :=
            Subgroup.mem_centralizer_singleton_iff.mp hy
          dsimp [tP]
          rw [← map_mul, ← map_mul]
          exact congrArg e hcomm
        exact Subgroup.mem_map.mpr ⟨e y, hx, by
          simp⟩
    calc
      Subgroup.centralizer ({tQ} : Set Q) =
          (Subgroup.centralizer ({tP} : Set (PSL2 K))).map
            e.symm.toMonoidHom := hCmap.symm
      _ = (T0 ⊔ Subgroup.zpowers s0).map e.symm.toMonoidHom := by rw [hC0]
      _ = T0Q ⊔ Subgroup.zpowers s0Q := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers]
        rfl
  have hT_cent : torus.T ≤ Subgroup.centralizer ({tQ} : Set Q) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases torus.T_cyclic with ⟨a, ha⟩
    rcases ha ⟨x, hx⟩ with ⟨n, hn⟩
    rcases ha ⟨tQ, torus.T_contains_t⟩ with ⟨m, hm⟩
    have hab :
        (⟨x, hx⟩ : torus.T) * (⟨tQ, torus.T_contains_t⟩ : torus.T) =
          (⟨tQ, torus.T_contains_t⟩ : torus.T) * (⟨x, hx⟩ : torus.T) := by
      calc
        (⟨x, hx⟩ : torus.T) * (⟨tQ, torus.T_contains_t⟩ : torus.T) =
            a ^ n * a ^ m := by simp [hn, hm]
        _ = a ^ (n + m) := by rw [zpow_add]
        _ = a ^ (m + n) := by rw [add_comm]
        _ = a ^ m * a ^ n := by rw [zpow_add]
        _ = (⟨tQ, torus.T_contains_t⟩ : torus.T) *
            (⟨x, hx⟩ : torus.T) := by simp [← hm, ← hn]
    simpa using congrArg Subtype.val hab
  have hT_le_T0Q : torus.T ≤ T0Q :=
    cyclic_subgroup_containing_involution_le_reflected_torus
      (G := Q) htQ T0Q s0Q hT0Qcyc htQ_T0Q hs0Q_I
      hs0Q_not_T0Q hinvT0Q hC0Q torus.T_cyclic hT_cent
      torus.T_contains_t
  have hs0Q_invT : ∀ x : Q, x ∈ torus.T → s0Q * x * s0Q⁻¹ = x⁻¹ := by
    intro x hx
    exact hinvT0Q x (hT_le_T0Q hx)
  have hs0Q_not_T : s0Q ∉ torus.T := by
    intro hsT
    exact hs0Q_not_T0Q (hT_le_T0Q hsT)
  have hs0Q_norm_T : s0Q ∈ Subgroup.normalizer (torus.T : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hs0Q_invT x hx]
      exact torus.T.inv_mem hx
    · intro hx
      have hs2 : s0Q * s0Q = 1 := by
        simpa [pow_two] using hs0Q_I.2
      have hss : s0Q⁻¹ = s0Q :=
        inv_eq_of_mul_eq_one_right hs2
      have hy := hs0Q_invT (s0Q * x * s0Q⁻¹) hx
      have hrecover : s0Q * (s0Q * x * s0Q⁻¹) * s0Q⁻¹ = x := by
        rw [hss]
        calc
          s0Q * (s0Q * x * s0Q) * s0Q =
              (s0Q * s0Q) * x * (s0Q * s0Q) := by group
          _ = x := by rw [hs2]; simp
      rw [hrecover] at hy
      rw [hy]
      exact torus.T.inv_mem hx
  let Zs : Subgroup Q := Subgroup.zpowers s0Q
  have hZs_le_norm : Zs ≤ Subgroup.normalizer (torus.T : Set Q) :=
    Subgroup.zpowers_le.mpr hs0Q_norm_T
  have hs0Q_order : orderOf s0Q = 2 :=
    orderOf_eq_prime (x := s0Q) (p := 2)
      (by simpa [pow_two] using hs0Q_I.2) hs0Q_I.1
  have hZs_card : Nat.card Zs = 2 := by
    simp [Zs, Nat.card_zpowers, hs0Q_order]
  have hT_disjoint_Zs : Disjoint torus.T Zs := by
    rw [Subgroup.disjoint_def]
    intro x hxT hxZ
    by_contra hx1
    have hxOrder : orderOf x = 2 := by
      have hdiv : orderOf x ∣ 2 := by
        rw [← hZs_card]
        exact Subgroup.orderOf_dvd_natCard Zs hxZ
      exact ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
        (fun h => hx1 (orderOf_eq_one_iff.mp h))
    have hzxle : Subgroup.zpowers x ≤ Zs := Subgroup.zpowers_le.mpr hxZ
    have hzxcard : Nat.card (Subgroup.zpowers x) = 2 := by
      rw [Nat.card_zpowers, hxOrder]
    have hzxEq : Subgroup.zpowers x = Zs :=
      Subgroup.eq_of_le_of_card_ge hzxle (by rw [hZs_card, hzxcard])
    have hs0Q_zx : s0Q ∈ Subgroup.zpowers x := by
      rw [hzxEq]
      exact Subgroup.mem_zpowers s0Q
    exact hs0Q_not_T ((Subgroup.zpowers_le.mpr hxT) hs0Q_zx)
  have hjoin_card :
      Nat.card (torus.T ⊔ Subgroup.zpowers s0Q : Subgroup Q) =
        2 * Nat.card torus.T := by
    change Nat.card (torus.T ⊔ Zs : Subgroup Q) = 2 * Nat.card torus.T
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer
      torus.T Zs hZs_le_norm hT_disjoint_Zs, hZs_card, Nat.mul_comm]
  have hjoin_le_C : torus.T ⊔ Subgroup.zpowers s0Q ≤
      Subgroup.centralizer ({tQ} : Set Q) := by
    apply sup_le
    · exact hT_cent
    · rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_centralizer_singleton_iff]
      have htinv : tQ⁻¹ = tQ :=
        inv_eq_of_mul_eq_one_right (by simpa [pow_two] using htQ.2)
      calc
        s0Q * tQ = tQ⁻¹ * s0Q := by
          exact mul_inv_eq_iff_eq_mul.mp (hinvT0Q tQ htQ_T0Q)
        _ = tQ * s0Q := by rw [htinv]
  have hC_T : Subgroup.centralizer ({tQ} : Set Q) =
      torus.T ⊔ Subgroup.zpowers s0Q := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hjoin_le_C
    rw [hjoin_card, torus.T_centralizer_card]
  exact ⟨s0Q, hs0Q_I, hs0Q_not_T, hs0Q_invT, hC_T⟩

end CFSG.GorensteinWalter

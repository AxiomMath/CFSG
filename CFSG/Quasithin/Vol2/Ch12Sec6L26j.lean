module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Quasithin

section Index

variable {X : Type*} [Group X] [Finite X]

theorem relIndex_dvd_index_of_normal (H K : Subgroup X) [K.Normal] : H.relIndex K ∣ H.index := by
  have h1 := Subgroup.relIndex_mul_relIndex (H ⊓ K) H (H ⊔ K) inf_le_left le_sup_left
  have h2 := Subgroup.relIndex_mul_relIndex (H ⊓ K) K (H ⊔ K) inf_le_right le_sup_right
  rw [Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_left H K] at h2
  have hne : (H ⊓ K).relIndex H ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h3 : H.relIndex (H ⊔ K) = (H ⊓ K).relIndex K := by
    have := h1.trans h2.symm
    rw [mul_comm ((H ⊓ K).relIndex K)] at this
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) this
  rw [← Subgroup.inf_relIndex_right, ← h3]
  exact ⟨_, (Subgroup.relIndex_mul_index le_sup_left).symm⟩

end Index

variable {Q : Type} [Group Q] [Finite Q]

theorem not_dvd_relIndex_inf {p : ℕ} {A B C : Subgroup Q} (hBC : B ≤ C)
    (hBn : C ≤ Subgroup.normalizer (B : Set Q)) (hA : ¬ p ∣ A.relIndex C) :
    ¬ p ∣ (A ⊓ B).relIndex B := by
  have : (B.subgroupOf C).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBC).mpr hBn
  rw [Subgroup.inf_relIndex_right, ← Subgroup.relIndex_subgroupOf hBC]
  exact fun h => hA (h.trans (relIndex_dvd_index_of_normal _ _))

theorem fitting_le_pPrimeCore (hO2 : CFSG.pCore 2 Q = ⊥) :
    CFSG.fittingSubgroup Q ≤ CFSG.pPrimeCore 2 Q := by
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun q => ?_
  have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
  have : Fact (q : ℕ).Prime := ⟨hq⟩
  by_cases hq2 : (q : ℕ) = 2
  · rw [hq2, hO2]
    exact bot_le
  · refine le_sSup ⟨CFSG.pCore_normal, ?_⟩
    obtain ⟨k, hk⟩ :=
      (CFSG.pCore_isPGroup : IsPGroup (q : ℕ) (CFSG.pCore (q : ℕ) Q)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))

theorem eq_one_of_mem_pPrimeCore {v : Q} (hv : v ∈ CFSG.pPrimeCore 2 Q) (hv2 : v ^ 2 = 1) :
    v = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := CFSG.pPrimeCore_coprime_card (p := 2) (G := Q)
  have h1 : orderOf (⟨v, hv⟩ : CFSG.pPrimeCore 2 Q) ∣ Nat.card (CFSG.pPrimeCore 2 Q) :=
    orderOf_dvd_natCard _
  have h2 : orderOf (⟨v, hv⟩ : CFSG.pPrimeCore 2 Q) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hv2))
  have h3 := (Nat.Coprime.coprime_dvd_left h2 hc).eq_one_of_dvd h1
  have := congrArg Subtype.val (orderOf_eq_one_iff.mp h3)
  simpa using this

omit [Finite Q] in
theorem center_fstar_le_fitting :
    CFSG.generalizedFitting Q ⊓ Subgroup.centralizer (CFSG.generalizedFitting Q : Set Q) ≤
      CFSG.fittingSubgroup Q := by
  have hEn : (CFSG.generalizedFitting Q).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  have hZn : (CFSG.generalizedFitting Q ⊓
      Subgroup.centralizer (CFSG.generalizedFitting Q : Set Q)).Normal :=
    Subgroup.normal_inf_normal _ _
  have hZc : IsMulCommutative ↥(CFSG.generalizedFitting Q ⊓
      Subgroup.centralizer (CFSG.generalizedFitting Q : Set Q)) :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_centralizer_iff.mp a.2.2 b b.2.1).symm⟩⟩
  have hZnil : Group.IsNilpotent ↥(CFSG.generalizedFitting Q ⊓
      Subgroup.centralizer (CFSG.generalizedFitting Q : Set Q)) := by
    let _ : CommGroup ↥(CFSG.generalizedFitting Q ⊓
        Subgroup.centralizer (CFSG.generalizedFitting Q : Set Q)) :=
      { mul_comm := fun a b => hZc.is_comm.comm a b }
    infer_instance
  exact le_sSup ⟨hZn, hZnil⟩

theorem two_dvd_card_of_isComponent {K : Subgroup Q} (hK : CFSG.IsComponent K) :
    2 ∣ Nat.card K := by
  by_contra hodd
  have hsolv : Group.IsSolvable ↥K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr
    (Nat.two_dvd_ne_zero.mp hodd))
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect ↥K := hK.1.1
  exact Group.IsPerfect.not_isSolvable ↥K hsolv

theorem exists_component (hO2 : CFSG.pCore 2 Q = ⊥) (h38 : A38Part3 Q) {T : Subgroup Q}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) {v : Q} (hvT : v ∈ T)
    (hvZ : ∀ t ∈ T, v * t = t * v) (hv1 : v ≠ 1) (hv2 : v ^ 2 = 1)
    (hF : ∀ f ∈ CFSG.fittingSubgroup Q, v * f = f * v) :
    ∃ K : Subgroup Q, CFSG.IsComponent K ∧ v ∈ Subgroup.normalizer (K : Set Q) ∧
      ∃ k ∈ K, v * k ≠ k * v := by
  classical
  have hnot : ¬ ∀ x ∈ CFSG.generalizedFitting Q, v * x = x * v := by
    intro hall
    have hvC : v ∈ Subgroup.centralizer (CFSG.generalizedFitting Q : Set Q) :=
      Subgroup.mem_centralizer_iff.mpr fun x hx => (hall x hx).symm
    have hvE := CFSG.centralizer_generalizedFitting_le Q hvC
    have hvF := center_fstar_le_fitting ⟨hvE, hvC⟩
    exact hv1 (eq_one_of_mem_pPrimeCore (fitting_le_pPrimeCore hO2 hvF) hv2)
  obtain ⟨K, hK, k, hk, hvk⟩ :
      ∃ K : Subgroup Q, CFSG.IsComponent K ∧ ∃ k ∈ K, v * k ≠ k * v := by
    by_contra hall
    push Not at hall
    apply hnot
    have hle : CFSG.generalizedFitting Q ≤ Subgroup.centralizer ({v} : Set Q) := by
      refine sup_le (fun f hf => ?_) (sSup_le fun K hK k hk => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hF f hf).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hall K hK k hk).symm
    exact fun x hx => (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm
  refine ⟨K, hK, ?_, k, hk, hvk⟩
  have hKc : K ∈ cComp (⊤ : Subgroup Q) := mem_cComp_top_of_isComponent hK
  obtain ⟨hG, hTpart⟩ := h38 K hKc
  rcases hTpart T hT with ⟨hKn, -, -⟩ | ⟨t, htT, -, hconj, -, hcomm, hinf, -, -⟩
  · rw [Subgroup.normalizer_eq_top_iff.mpr hKn]
    exact Subgroup.mem_top v
  by_contra hvN
  have hKv : K.map (MulAut.conj v).toMonoidHom ∈ conjSubgroupsBy T K := ⟨v, hvT, rfl⟩
  rw [hconj] at hKv
  rcases hKv with hKv | hKv
  · apply hvN
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : v * x * v⁻¹ ∈ K.map (MulAut.conj v).toMonoidHom := ⟨x, hx, rfl⟩
      rwa [hKv] at this
    · intro hx
      rw [← hKv] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
        exact mul_left_cancel (mul_right_cancel hyx)
      rwa [← this]
  have hTK : T ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxT, hxK⟩
    have hx' : x ∈ K.map (MulAut.conj v).toMonoidHom := by
      refine ⟨x, hxK, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hvZ x hxT, mul_inv_cancel_right]
    rw [hKv] at hx'
    have : x ∈ K ⊓ K.map (MulAut.conj t).toMonoidHom := ⟨hxK, hx'⟩
    rwa [hinf] at this
  rcases hG with hKn | ⟨-, t₁, -, hcomm₁, -, hD⟩
  · exact hvN (by rw [Subgroup.normalizer_eq_top_iff.mpr hKn]; exact Subgroup.mem_top v)
  have hDn : (conjClosure K ⊤).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_conjClosure K ⊤))
  have hKD : K ≤ conjClosure K ⊤ := le_conjClosure K ⊤
  have hDK : conjClosure K ⊤ ≤ Subgroup.normalizer (K : Set Q) := by
    rw [hD]
    refine sup_le Subgroup.le_normalizer ?_
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((Subgroup.commutator_comm _ _).trans hcomm₁))
  have h1 : ¬ 2 ∣ (T ⊓ conjClosure K ⊤).relIndex (conjClosure K ⊤) :=
    not_dvd_relIndex_inf (C := ⊤) le_top (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr hDn).ge)
      hT.2.2
  have h2 := not_dvd_relIndex_inf hKD hDK h1
  have h3 : T ⊓ conjClosure K ⊤ ⊓ K = ⊥ := by rw [inf_assoc, inf_eq_right.mpr hKD, hTK]
  rw [h3, Subgroup.relIndex_bot_left] at h2
  exact h2 (two_dvd_card_of_isComponent hK)

end CFSG.Quasithin.H13.S126C

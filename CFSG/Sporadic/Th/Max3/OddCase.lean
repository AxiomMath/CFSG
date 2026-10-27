module

public import CFSG.Sporadic.Th.Max3.CentA
public import CFSG.Sporadic.Th.KernelCentralizer
public import CFSG.Sporadic.Th.Max3.Quotient
public import CFSG.GroupTheory.OddSquareSwap
public import CFSG.LocalAnalysis.ZStar
public import CFSG.Sporadic.Th.Max3.OddCaseInputs
public import Certificates.Certificate9014
public import Certificates.Certificate1020
public import Certificates.Certificate1021
public import Certificates.Certificate1022
public import Certificates.Certificate10091
public import Certificates.Certificate10092
public import Certificates.Certificate9013
public import Certificates.Certificate10088
public import Certificates.Certificate10089
public meta import CFSG.Sporadic.Th.Max3.Relations
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAut
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.Sporadic.Th

open Native Max3

@[expose] noncomputable def eQ :
    Fin 4 → J := ![q 0, q 1 * q 2, q 1 * q 5, q 7]

@[expose] noncomputable def fQ :
    Fin 4 → J := ![q 1 * q 3 * q 4, q 3, q 3 * q 6, q 3 * q 4]

theorem isRows_eQ
    (i : Fin 4) : IsRows (rowsEQ i) (eQ i) := by
  fin_cases i
  · exact isRows_q 0
  · exact (isRows_q 1).mul (isRows_q 2)
  · exact (isRows_q 1).mul (isRows_q 5)
  · exact isRows_q 7

theorem isRows_fQ
    (i : Fin 4) : IsRows (rowsFQ i) (fQ i) := by
  fin_cases i
  · exact ((isRows_q 1).mul (isRows_q 3)).mul (isRows_q 4)
  · exact isRows_q 3
  · exact (isRows_q 3).mul (isRows_q 6)
  · exact (isRows_q 3).mul (isRows_q 4)

private theorem native_symplectic_facts :
    (∀ i : Fin 4, eqRows (mulRows (rowsEQ i) (rowsEQ i)) idRows = true) ∧
    (∀ i j : Fin 4, eqRows (mulRows (rowsEQ i) (rowsEQ j)) (mulRows (rowsEQ j) (rowsEQ i)) = true) ∧
    (∀ i : Fin 4, eqRows (mulRows (rowsFQ i) (rowsEQ i))
      (mulRows (mulRows (rowsEQ i) rowsZ) (rowsFQ i)) = true) ∧
    (∀ i j : Fin 4, i ≠ j →
      eqRows (mulRows (rowsFQ j) (rowsEQ i)) (mulRows (rowsEQ i) (rowsFQ j)) = true) := by
  exact Certificates.certificate9014

theorem symplectic_facts :
    (∀ i, eQ i * eQ i = 1) ∧ (∀ i j, eQ i * eQ j = eQ j * eQ i) ∧
      (∀ i, fQ i * eQ i * (fQ i)⁻¹ = eQ i * z) ∧ (∀ i j, i ≠ j → fQ j * eQ i = eQ i * fQ j) := by
  obtain ⟨h1, h2, h3, h4⟩ := native_symplectic_facts
  refine ⟨fun i => ((isRows_eQ i).mul (isRows_eQ i)).eq_of_eqRows IsRows.one (h1 i),
    fun i j => ((isRows_eQ i).mul (isRows_eQ j)).eq_of_eqRows
      ((isRows_eQ j).mul (isRows_eQ i)) (h2 i j), fun i => ?_,
    fun i j hij => ((isRows_fQ j).mul (isRows_eQ i)).eq_of_eqRows
      ((isRows_eQ i).mul (isRows_fQ j)) (h4 i j hij)⟩
  have e := ((isRows_fQ i).mul (isRows_eQ i)).eq_of_eqRows
    (((isRows_eQ i).mul isRows_z).mul (isRows_fQ i)) (h3 i)
  rw [e, mul_inv_cancel_right]

theorem eQ_mem_M (i : Fin 4) : eQ i ∈ M := by
  fin_cases i
  · exact q_mem_M 0
  · exact M.mul_mem (q_mem_M 1) (q_mem_M 2)
  · exact M.mul_mem (q_mem_M 1) (q_mem_M 5)
  · exact q_mem_M 7

theorem fQ_mem_M (i : Fin 4) : fQ i ∈ M := by
  fin_cases i
  · exact M.mul_mem (M.mul_mem (q_mem_M 1) (q_mem_M 3)) (q_mem_M 4)
  · exact q_mem_M 3
  · exact M.mul_mem (q_mem_M 3) (q_mem_M 6)
  · exact M.mul_mem (q_mem_M 3) (q_mem_M 4)

theorem orderOf_eQ
    (i : Fin 4) : orderOf (eQ i) = 2 := by
  have h1 := symplectic_facts.1 i
  have hne : eQ i ≠ 1 := by
    intro h
    have h3 := symplectic_facts.2.2.1 i
    rw [h, mul_one, one_mul, mul_inv_cancel] at h3
    exact z_ne_one h3.symm
  exact orderOf_eq_prime (by rw [sq]; exact h1) hne

theorem inf_M_eq_bot
    {A : Subgroup J} (hA : Odd (Nat.card A))
    (hAN : ∀ m ∈ M, m ∈ Subgroup.normalizer (A : Set J)) : A ⊓ M = ⊥ := by
  have hB : Odd (Nat.card ↥(A ⊓ M)) := Odd.of_dvd_nat hA (Subgroup.card_dvd_of_le inf_le_left)
  have hfin : Finite ↥(A ⊓ M) := CFSG.OddInversion.finite_of_odd_card hB
  have hcomm : ∀ b ∈ A ⊓ M, ∀ g ∈ Q, b * g = g * b := by
    intro b hb g hg
    obtain ⟨hbA, hbM⟩ := Subgroup.mem_inf.1 hb
    have hgM : g ∈ M := Q_le_M hg
    have hcA : b * g * b⁻¹ * g⁻¹ ∈ A := by
      have h1 : g * b⁻¹ * g⁻¹ ∈ A :=
        CFSG.OddInversion.conj_mem_of_mem_normalizer (hAN g hgM) (A.inv_mem hbA)
      have := A.mul_mem hbA h1
      rwa [show b * (g * b⁻¹ * g⁻¹) = b * g * b⁻¹ * g⁻¹ by group] at this
    have hcM : b * g * b⁻¹ * g⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem (M.mul_mem hbM hgM) (M.inv_mem hbM)) (M.inv_mem hgM)
    have hcQ : b * g * b⁻¹ * g⁻¹ ∈ Q := by
      have h1 : b * g * b⁻¹ ∈ Q :=
        CFSG.OddInversion.conj_mem_of_mem_normalizer (M_le_normalizer_Q hbM) hg
      exact Q.mul_mem h1 (Q.inv_mem hg)
    have hc1 : b * g * b⁻¹ * g⁻¹ = 1 := by
      have hodd : Odd (orderOf (b * g * b⁻¹ * g⁻¹)) := by
        have := orderOf_dvd_natCard (⟨_, Subgroup.mem_inf.2 ⟨hcA, hcM⟩⟩ : ↥(A ⊓ M))
        rw [Subgroup.orderOf_mk] at this
        exact Odd.of_dvd_nat hB this
      have h2 : orderOf (b * g * b⁻¹ * g⁻¹) ∣ 2 ^ 9 := by
        have := orderOf_dvd_natCard (⟨_, hcQ⟩ : ↥Q)
        rw [Subgroup.orderOf_mk, card_Q] at this
        simpa using this
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
      rcases k with _ | k
      · rw [pow_zero] at hk; exact orderOf_eq_one_iff.1 hk
      · rw [hk] at hodd
        exact absurd (Nat.even_pow.2 ⟨even_two, by omega⟩) (Nat.not_even_iff_odd.2 hodd)
    calc b * g = b * g * b⁻¹ * g⁻¹ * (g * b) := by group
      _ = g * b := by rw [hc1, one_mul]
  rw [eq_bot_iff]
  intro b hb
  have hbz : b ∈ Subgroup.zpowers z := by
    rw [← centralizer_Q_inf_M]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun g hg => ?_, (Subgroup.mem_inf.1 hb).2⟩
    exact (hcomm b hb g hg).symm
  rcases (Subgroup.mem_zpowers_iff.1 hbz) with ⟨k, rfl⟩
  have hz2 : z * z = 1 := z_mul_self
  have hzk : z ^ k = 1 ∨ z ^ k = z := by
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left; rw [← two_mul, zpow_mul, zpow_two, hz2, one_zpow]
    · right; rw [zpow_add, zpow_mul, zpow_two, hz2, one_zpow, one_mul, zpow_one]
  rcases hzk with h | h
  · rw [h]; exact Subgroup.one_mem _
  · exfalso
    rw [h] at hb
    have := orderOf_dvd_natCard (⟨z, hb⟩ : ↥(A ⊓ M))
    rw [Subgroup.orderOf_mk, orderOf_eq_prime (by rw [sq]; exact hz2) z_ne_one] at this
    exact (Nat.not_even_iff_odd.2 hB) (even_iff_two_dvd.2 this)

theorem eq_bot_of_inverted
    {A : Subgroup J} (hA : Odd (Nat.card A))
    (hAN : ∀ m ∈ M, m ∈ Subgroup.normalizer (A : Set J)) (hinv : ∀ u ∈ A, a * u * a⁻¹ = u⁻¹)
    (hdvd : Nat.card A ∣ 90745943887872000) : A = ⊥ := by
  obtain ⟨he1, he2, he3, he4⟩ := symplectic_facts
  obtain ⟨k, hk⟩ := CFSG.OddInversion.card_eq_pow_sixteen hA eQ fQ orderOf_eQ
    (fun i => hAN _ (eQ_mem_M i)) (fun i => hAN _ (fQ_mem_M i)) hinv
    (fun i => by rw [← z_eq_a]; exact (commute_z_of_mem_M (fQ_mem_M i)).eq) he2
    (fun i => by rw [← z_eq_a]; exact he3 i) he4
  have hk1 : k = 1 := CFSG.OddInversion.eq_one_of_pow_sixteen_dvd (hk ▸ hdvd)
  rw [hk1, one_pow] at hk
  exact Subgroup.eq_bot_of_card_eq A hk

theorem eq_M_of_isolated
    (hK : Kernel.KernelFacts) {F : Subgroup J} (hMF : M ≤ F)
    (hiso : ∀ g ∈ F, g * a * g⁻¹ * a = a * (g * a * g⁻¹) → g * a * g⁻¹ = a) : F = M := by
  classical
  have haM : a ∈ M := z_eq_a ▸ z_mem_M
  have haF : a ∈ F := hMF haM
  have ha2 : a * a = 1 := by rw [← z_eq_a]; exact z_mul_self
  have ha1 : a ≠ 1 := by rw [← z_eq_a]; exact z_ne_one
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨N, hNn, hNodd, hNc⟩ := CFSG.ZStar.glauberman_zStar F ⟨a, haF⟩
    (fun h => ha1 (by simpa using congrArg Subtype.val h))
    (Subtype.ext (by simpa using ha2))
    (fun g hg => by
      have hg' : (g : J) * a * (g : J)⁻¹ * a = a * ((g : J) * a * (g : J)⁻¹) := by
        simpa using congrArg Subtype.val hg
      apply Subtype.ext
      simpa using hiso g g.2 hg')
  set A : Subgroup J := N.map F.subtype with hAdef
  have hAcard : Nat.card A = Nat.card N :=
    Nat.card_congr (N.equivMapOfInjective F.subtype F.subtype_injective).toEquiv.symm
  have hAodd : Odd (Nat.card A) := hAcard ▸ hNodd
  have hAF : ∀ f ∈ F, f ∈ Subgroup.normalizer (A : Set J) := by
    intro f hf
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' := hNn.conj_mem v hv (⟨f, hf⟩ : F)
      exact ⟨_, hv', by simp⟩
    · rintro ⟨v, hv, hvu⟩
      have hvu' : (v : J) = f * u * f⁻¹ := by simpa using hvu
      have hu : u ∈ F := by
        have := F.mul_mem (F.mul_mem (F.inv_mem hf) v.2) hf
        rwa [hvu', show f⁻¹ * (f * u * f⁻¹) * f = u by group] at this
      refine ⟨⟨u, hu⟩, ?_, by simp⟩
      have := hNn.conj_mem v hv (⟨f, hf⟩⁻¹)
      have e : (⟨f, hf⟩⁻¹ * v * (⟨f, hf⟩⁻¹)⁻¹ : F) = ⟨u, hu⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        rw [hvu']; group
      rwa [e] at this
  have hAM : A ⊓ M = ⊥ := inf_M_eq_bot hAodd fun m hm => hAF m (hMF hm)
  have hCa := Kernel.centralizer_a_eq_M hK
  have hfix : ∀ u ∈ A, a * u * a⁻¹ = u → u = 1 := by
    intro u hu hau
    have huM : u ∈ M := by
      rw [← hCa, Subgroup.mem_centralizer_singleton_iff]
      calc u * a = a * u * a⁻¹ * a := by rw [hau]
        _ = a * u := by group
    have : u ∈ A ⊓ M := Subgroup.mem_inf.2 ⟨hu, huM⟩
    rw [hAM] at this
    exact (Subgroup.mem_bot.1 this)
  have hinv : ∀ u ∈ A, a * u * a⁻¹ = u⁻¹ := by
    have haN := hAF a haF
    let φ : A →* A := MonoidHom.mk' (fun u => ⟨a * u * a⁻¹,
        CFSG.OddInversion.conj_mem_of_mem_normalizer haN u.2⟩) (fun u v => by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      group)
    have hφ : ∀ u : A, ((φ u : A) : J) = a * u * a⁻¹ := fun u => by simp [φ]
    have hfpf : MonoidHom.FixedPointFree φ := fun u hu => by
      apply Subtype.ext
      have h1 : a * (u : J) * a⁻¹ = u := by rw [← hφ u, hu]
      simpa using hfix u u.2 h1
    have hinvol : Function.Involutive φ := fun u => by
      apply Subtype.ext
      rw [hφ, hφ]
      calc a * (a * (u : J) * a⁻¹) * a⁻¹ = (a * a) * u * (a * a)⁻¹ := by group
        _ = u := by rw [ha2]; group
    have hφinv := MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hfpf hinvol
    intro u hu
    have h1 := congrArg Subtype.val (congrFun hφinv ⟨u, hu⟩)
    rw [hφ] at h1
    simpa using h1
  have hdvd : Nat.card A ∣ 90745943887872000 := natCard_J ▸ Subgroup.card_subgroup_dvd_card A
  have hAbot := eq_bot_of_inverted hAodd (fun m hm => hAF m (hMF hm)) hinv hdvd
  apply le_antisymm _ hMF
  intro g hg
  rw [← hCa, Subgroup.mem_centralizer_singleton_iff]
  have hcA : g * a * g⁻¹ * a⁻¹ ∈ A := ⟨_, hNc ⟨g, hg⟩, by simp⟩
  rw [hAbot, Subgroup.mem_bot] at hcA
  have : g * a * g⁻¹ = a := by
    calc g * a * g⁻¹ = g * a * g⁻¹ * a⁻¹ * a := by group
      _ = a := by rw [hcA, one_mul]
  calc g * a = g * a * g⁻¹ * g := by group
    _ = a * g := by rw [this]

end CFSG.Sporadic.Th

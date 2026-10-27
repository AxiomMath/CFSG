module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFOmTrace
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFGU2
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFOmNorm2
public import CFSG.Mathlib.LinearAlgebra.QuadraticForm.OrthogonalSum

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)
open scoped commutatorElement
open CFSG.StandardType.NormFrame
open CFSG.StandardType.QTwoFrameTorus

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma sq_ne_self_of_cube {M : Type} [Field M] {c : M} (h2 : (2 : M) = 0)
    (hc3 : c ^ 3 = 1) (hc : c ≠ 1) : c ^ 2 ≠ c := by
  intro h
  have hquad := frame_sq_add_add_one_eq_zero hc3 hc
  rw [h] at hquad
  have hcc : c + c = 0 := by rw [← two_mul, h2, zero_mul]
  have hzero : (1 : M) = 0 := by
    rw [show (1 : M) = c + c + 1 by rw [hcc, zero_add], hquad]
  exact one_ne_zero hzero

private lemma trace_eq_one_of_cube {K M : Type} [Field K] [Finite K] [CharP K 2]
    [Field M] [Finite M] [Algebra K M] (hK : Nat.card K = 2) (hM : Nat.card M = 4)
    {c : M} (hc3 : c ^ 3 = 1) (hc : c ≠ 1) : Algebra.trace K M c = 1 := by
  have h2M : (2 : M) = 0 := by
    have hchar : CharP M 2 := (Algebra.charP_iff (K := K) (L := M) 2).mp inferInstance
    exact @CharP.cast_eq_zero M _ 2 hchar
  have hc2 : c ^ 2 ≠ c := sq_ne_self_of_cube h2M hc3 hc
  rcases CFSG.StandardType.TraceFrame.card_two_eq_zero_or_one hK
    (Algebra.trace K M c) with h0 | h1
  · exfalso
    have htrA : ∀ a : K, Algebra.trace K M (algebraMap K M a) = 0 := by
      intro a
      rw [Algebra.trace_algebraMap, CFSG.StandardType.TraceFrame.finrank_eq_two hK hM,
        nsmul_eq_mul, CharP.cast_eq_zero K 2, zero_mul]
    have hdecomp : ∀ m : M, ∃ a b : K, m = algebraMap K M a + algebraMap K M b * c :=
      CFSG.StandardType.TraceFrame.exists_eq_algebraMap_add_mul hK hM hc2
    have hzero : ∀ μ : M, Algebra.trace K M (μ * 1) = 0 := by
      intro μ
      obtain ⟨a, b, rfl⟩ := hdecomp μ
      have hb : Algebra.trace K M (algebraMap K M b * c) = 0 := by
        rw [← Algebra.smul_def, (Algebra.trace K M).map_smul, h0, smul_zero]
      rw [mul_one, map_add (Algebra.trace K M), htrA a, hb, zero_add]
    have h1zero := CFSG.StandardType.TraceFrame.eq_zero_of_trace_mul_eq_zero
      (y := (1 : M)) hzero
    exact one_ne_zero h1zero
  · exact h1

private lemma normFrame_coord {K M U V : Type} [Field K] [Finite K] [CharP K 2]
    [Field M] [Finite M] [Algebra K M] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {n : ℕ} {Q : QuadraticForm K V}
    {τ : M ≃+* M} (hτ : ∀ y, τ y = y ^ 2) {Φ : ((Fin n → M) × U) ≃ₗ[K] V}
    (hK : Nat.card K = 2) (hM : Nat.card M = 4)
    (hpolar : ∀ d d' w w', QuadraticMap.polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, Algebra.trace K M (τ (d i) * d' i) +
        QuadraticMap.polarBilin Q (Φ (0, w)) (Φ (0, w')))
    {A : Subgroup (V ≃ₗ[K] V)} (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (i : Fin n) (a : V ≃ₗ[K] V) (haA : a ∈ A)
    (hane : a (Φ (Pi.single i 1, 0)) ≠ Φ (Pi.single i 1, 0))
    {c : Fin n → M} (hc3 : ∀ j, c j ^ 3 = 1)
    (hact : ∀ d w, a (Φ (d, w)) = Φ (fun j => c j * d j, w)) :
    ∀ u : M, algebraMap K M (Q (Φ (Pi.single i u, 0))) = τ u * u := by
  classical
  let q : M → K := fun u => Q (Φ (Pi.single i u, 0))
  have hcharM : CharP M 2 := (Algebra.charP_iff (K := K) (L := M) 2).mp inferInstance
  have h2M : (2 : M) = 0 := @CharP.cast_eq_zero M _ 2 hcharM
  have hci0 : c i ≠ 0 := by
    intro h
    have h3 := hc3 i
    rw [h, zero_pow (by norm_num)] at h3
    exact zero_ne_one h3
  have hci1 : c i ≠ 1 := by
    intro h
    apply hane
    have hact1 := hact (Pi.single i (1 : M) : Fin n → M) 0
    rw [hact1]
    have hfun : (fun j => c j * ((Pi.single i (1 : M) : Fin n → M) j)) =
        (Pi.single i (c i) : Fin n → M) := by
      funext j
      by_cases hji : j = i
      · subst hji; simp
      · simp [hji]
    rw [hfun, h]
  have hact_i : ∀ u : M, a (Φ (Pi.single i u, 0)) =
      Φ ((Pi.single i (c i * u) : Fin n → M), 0) := by
    intro u
    have hfun : (fun j => c j * ((Pi.single i u : Fin n → M) j)) =
        (Pi.single i (c i * u) : Fin n → M) := by
      funext j
      by_cases hji : j = i
      · subst hji; simp
      · simp [hji]
    rw [hact, hfun]
  have hqinv : ∀ u : M, q (c i * u) = q u := by
    intro u
    have h := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hAO haA)
      (Φ (Pi.single i u, 0))
    rw [hact_i u] at h
    simpa [q] using h
  have hqadd : ∀ u v : M, q (u + v) = q u + q v + Algebra.trace K M (τ u * v) := by
    intro u v
    have hp : ((Pi.single i (u + v) : Fin n → M), (0 : U)) =
        ((Pi.single i u : Fin n → M), (0 : U)) +
          ((Pi.single i v : Fin n → M), (0 : U)) := by
      refine Prod.ext ?_ ?_
      · funext j
        by_cases hji : j = i <;> simp [hji]
      · simp
    have h := hpolar (Pi.single i u : Fin n → M) (Pi.single i v : Fin n → M) 0 0
    have hsum : (∑ j, Algebra.trace K M
        (τ ((Pi.single i u : Fin n → M) j) *
          ((Pi.single i v : Fin n → M) j))) =
        Algebra.trace K M (τ u * v) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Pi.single_eq_of_ne hji]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    have hbase : QuadraticMap.polarBilin Q (Φ ((0 : Fin n → M), (0 : U)))
        (Φ ((0 : Fin n → M), (0 : U))) = 0 := by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul,
        CharP.cast_eq_zero K 2, zero_mul]
    have hB : QuadraticMap.polarBilin Q (Φ (Pi.single i u, 0))
        (Φ (Pi.single i v, 0)) = Algebra.trace K M (τ u * v) := by
      rw [h, hsum, hbase, add_zero]
    calc q (u + v) = Q (Φ ((Pi.single i u, 0) + (Pi.single i v, 0))) := by
          change Q (Φ ((Pi.single i (u + v) : Fin n → M), (0 : U))) =
            Q (Φ ((Pi.single i u, 0) + (Pi.single i v, 0)))
          rw [hp]
      _ = Q (Φ (Pi.single i u, 0) + Φ (Pi.single i v, 0)) := by rw [map_add]
      _ = Q (Φ (Pi.single i u, 0)) + Q (Φ (Pi.single i v, 0)) +
            QuadraticMap.polarBilin Q (Φ (Pi.single i u, 0)) (Φ (Pi.single i v, 0)) := by
          rw [QuadraticMap.map_add Q, ← QuadraticMap.polarBilin_apply_apply]
      _ = q u + q v + Algebra.trace K M (τ u * v) := by rw [hB]
  have hqi : q (c i) = q 1 := by simpa using hqinv 1
  have hqci2 : q ((c i) ^ 2) = q (c i) := by
    simpa [pow_two] using hqinv (c i)
  have htrace : Algebra.trace K M (c i) = 1 :=
    trace_eq_one_of_cube hK hM (hc3 i) hci1
  have hq1 : q 1 = 1 := by
    have h1 := hqadd 1 (c i)
    have hsq : 1 + c i = (c i) ^ 2 := by
      rw [add_comm, @frame_sq_eq_add_one M _ hcharM (c i) (hc3 i) hci1]
    rw [hsq, hqci2, map_one, one_mul, htrace] at h1
    rw [hqi] at h1
    have hc : (0 : K) = q 1 + 1 := by
      have h := h1
      rw [add_assoc] at h
      exact add_left_cancel (a := q 1) (by simpa using h)
    have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hxx : q 1 + q 1 = 0 := by rw [← two_mul, h2K, zero_mul]
    calc q 1 = q 1 + 0 := by simp
      _ = q 1 + (q 1 + 1) := by rw [hc]
      _ = (q 1 + q 1) + 1 := by abel
      _ = 0 + 1 := by rw [hxx]
      _ = 1 := zero_add 1
  have hqc : q (c i) = 1 := by rw [hqi, hq1]
  have hqc2 : q ((c i) ^ 2) = 1 := by rw [hqci2, hqc]
  have hmem : ∀ u : M, u ≠ 0 → u ∈ ({1, c i, (c i) ^ 2} : Finset M) := by
    intro u hu
    have hc2ne1 : (c i) ^ 2 ≠ 1 := by
      intro hsq
      have h3 := hc3 i
      have hc1 : c i = 1 := by
        calc c i = 1 * c i := by rw [one_mul]
        _ = (c i) ^ 2 * c i := by rw [← hsq]
        _ = (c i) ^ 3 := by ring
        _ = 1 := h3
      exact hci1 hc1
    have hc2nec : (c i) ^ 2 ≠ c i := sq_ne_self_of_cube h2M (hc3 i) hci1
    have h1not : (1 : M) ∉ ({c i, (c i) ^ 2} : Finset M) := by
      intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hci1 h.symm
      · exact hc2ne1 h.symm
    have hcnot : c i ∉ ({(c i) ^ 2} : Finset M) := by
      intro h
      exact hc2nec (Finset.mem_singleton.mp h).symm
    have hcardS : ({1, c i, (c i) ^ 2} : Finset M).card = 3 := by
      rw [Finset.card_insert_of_notMem h1not,
        Finset.card_insert_of_notMem hcnot, Finset.card_singleton]
    let fM : Fintype M := Fintype.ofFinite M
    let UM : Finset M := @Finset.univ M fM
    have hcardUM : UM.card = 4 := by
      dsimp [UM]
      exact (Nat.card_eq_fintype_card).symm.trans hM
    have hS : ({1, c i, (c i) ^ 2} : Finset M) = UM.erase 0 := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact Finset.mem_erase.mpr ⟨zero_ne_one.symm, by
            dsimp [UM]; exact Finset.mem_univ _⟩
        · exact Finset.mem_erase.mpr ⟨hci0, by
            dsimp [UM]; exact Finset.mem_univ _⟩
        · exact Finset.mem_erase.mpr ⟨pow_ne_zero 2 hci0, by
            dsimp [UM]; exact Finset.mem_univ _⟩
      · rw [Finset.card_erase_of_mem (by dsimp [UM]; exact Finset.mem_univ _),
          hcardUM, hcardS]
    have hu' : u ∈ UM.erase 0 :=
      Finset.mem_erase.mpr ⟨hu, by dsimp [UM]; exact Finset.mem_univ _⟩
    rwa [← hS] at hu'
  have hqval : ∀ u : M, q u = if u = 0 then 0 else 1 := by
    intro u
    by_cases hu : u = 0
    · subst hu
      rw [if_pos rfl]
      have hz : Φ ((Pi.single i (0 : M) : Fin n → M), (0 : U)) = 0 := by simp
      change Q (Φ ((Pi.single i (0 : M) : Fin n → M), (0 : U))) = 0
      rw [hz, map_zero]
    · rw [if_neg hu]
      have hmemu := hmem u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmemu
      rcases hmemu with rfl | rfl | rfl
      · exact hq1
      · exact hqc
      · exact hqc2
  intro u
  change algebraMap K M (q u) = τ u * u
  have hnorm : τ u * u = if u = 0 then 0 else 1 := by
    by_cases hu : u = 0
    · simp [hu]
    · rw [if_neg hu]
      calc τ u * u = u ^ 2 * u := by rw [hτ]
        _ = u ^ 3 := by ring
        _ = 1 := frame_pow_three_eq_one hM hu
  rw [hqval u, hnorm]
  by_cases hu : u = 0 <;> simp [hu]

private lemma normFrame_Q {K M U V : Type} [Field K] [Finite K] [CharP K 2]
    [Field M] [Finite M] [Algebra K M] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {n : ℕ} {Q : QuadraticForm K V}
    {τ : M ≃+* M} {Φ : ((Fin n → M) × U) ≃ₗ[K] V}
    (hpolar : ∀ d d' w w', QuadraticMap.polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, Algebra.trace K M (τ (d i) * d' i) +
        QuadraticMap.polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (hcoord : ∀ (i : Fin n) (u : M),
      algebraMap K M (Q (Φ (Pi.single i u, 0))) = τ u * u) :
    ∀ d w, algebraMap K M (Q (Φ (d, w))) =
      ∑ i, τ (d i) * d i + algebraMap K M (Q (Φ (0, w))) := by
  classical
  intro d w
  let f : Fin n → V := fun i => Φ ((Pi.single i (d i) : Fin n → M), 0)
  let z : V := Φ ((0 : Fin n → M), w)
  have hdecomp : Φ (d, w) = ∑ i, f i + z := by
    have hsum : ∑ i, f i = Φ (d, (0 : U)) := by
      have hpair : (∑ i, ((Pi.single i (d i) : Fin n → M), (0 : U))) =
          (d, (0 : U)) := by
        ext j
        · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
        · simp [Prod.snd_sum]
      dsimp [f]
      rw [← map_sum, hpair]
    rw [hsum]
    dsimp [z]
    rw [← map_add]
    congr 1
    ext <;> simp
  have horth : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ j ∈ Finset.univ, i ≠ j →
      QuadraticMap.polar Q (f i) (f j) = 0 := by
    intro i _ j _ hij
    have h := hpolar (Pi.single i (d i) : Fin n → M) (Pi.single j (d j) : Fin n → M)
      (0 : U) (0 : U)
    have hsum : ∑ k, Algebra.trace K M
        (τ ((Pi.single i (d i) : Fin n → M) k) *
          ((Pi.single j (d j) : Fin n → M) k)) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hki : k = i
      · subst hki
        simp [Pi.single_eq_of_ne hij]
      · simp [Pi.single_eq_of_ne hki]
    have hbase : QuadraticMap.polarBilin Q (Φ ((0 : Fin n → M), (0 : U)))
        (Φ ((0 : Fin n → M), (0 : U))) = 0 := by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul,
        CharP.cast_eq_zero K 2, zero_mul]
    dsimp [f]
    rw [← QuadraticMap.polarBilin_apply_apply, h, hsum, hbase, add_zero]
  have horthz : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      QuadraticMap.polar Q (f i) z = 0 := by
    intro i _
    have h := hpolar (Pi.single i (d i) : Fin n → M) (0 : Fin n → M) (0 : U) w
    have hsum : ∑ k, Algebra.trace K M
        (τ ((Pi.single i (d i) : Fin n → M) k) * ((0 : Fin n → M) k)) = 0 := by
      refine Finset.sum_eq_zero fun k _ => by simp
    have hbase : QuadraticMap.polarBilin Q (Φ ((0 : Fin n → M), (0 : U)))
        (Φ ((0 : Fin n → M), w)) = 0 := by
      have hz0 : Φ ((0 : Fin n → M), (0 : U)) = 0 := by simp
      rw [hz0]
      simp
    dsimp [f, z]
    rw [← QuadraticMap.polarBilin_apply_apply, h, hsum, hbase, add_zero]
  have hQ := CFSG.QuadraticMap.map_sum_add_of_polar_eq_zero Q
    (Finset.univ : Finset (Fin n)) f z horth horthz
  have hQ' : Q (Φ (d, w)) = ∑ i, Q (f i) + Q z := by
    rw [hdecomp]
    exact hQ
  calc algebraMap K M (Q (Φ (d, w)))
      = algebraMap K M (∑ i, Q (f i) + Q z) := by rw [hQ']
    _ = ∑ i, algebraMap K M (Q (f i)) + algebraMap K M (Q z) := by
        rw [map_add, map_sum]
    _ = ∑ i, τ (d i) * d i + algebraMap K M (Q (Φ (0, w))) := by
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        exact hcoord i (d i)


theorem exists_normFrame_of_isElemAbelian_orth {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {E : Subgroup ↥(orthDerived Q)}
    (hEab : IsElemAbelian 3 E)
    (hsc : ∀ g ∈ Subgroup.centralizer (E : Set ↥(orthDerived Q)), g ^ 3 = 1 → g ∈ E) :
    ∃ (n : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (_ : Algebra K M) (τ : M ≃+* M)
      (U : Type) (_ : AddCommGroup U) (_ : Module K U) (Φ : ((Fin n → M) × U) ≃ₗ[K] V),
      Nat.card M = 4 ∧ (∀ y, τ y = y ^ 2) ∧
      (∀ d d' w w', QuadraticMap.polarBilin Q (Φ (d, w)) (Φ (d', w')) =
        ∑ i, Algebra.trace K M (τ (d i) * d' i) +
          QuadraticMap.polarBilin Q (Φ (0, w)) (Φ (0, w'))) ∧
      (∀ d w, algebraMap K M (Q (Φ (d, w))) =
        ∑ i, τ (d i) * d i + algebraMap K M (Q (Φ (0, w)))) ∧
      (∀ e ∈ E, ∃ a : Fin n → M, (∀ i, a i ^ 3 = 1) ∧
        ∀ d w, (e : V ≃ₗ[K] V) (Φ (d, w)) = Φ (fun i => a i * d i, w)) ∧
      ∀ a : Fin n → M, (∀ i, a i ^ 3 = 1) → ∃ e ∈ E,
        ∀ d w, (e : V ≃ₗ[K] V) (Φ (d, w)) = Φ (fun i => a i * d i, w) := by
  classical
  let A : Subgroup (V ≃ₗ[K] V) := E.map (orthDerived Q).subtype
  have hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.map_subtype_le E).trans
      (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (Q := Q))
  have hA : IsElemAbelian 3 A := CFSG.SectionRank.isElemAbelian_map hEab _
  obtain ⟨n, M, hMfield, hMfin, hMalg, τ, U, hUadd, hUmod, Φ, hcardM, hτsq, hpolar,
    hdiag, hmoved⟩ :=
    exists_traceFrame_of_isElemAbelian_orth hK hQ hAO hA
  have hN : ∀ d w, algebraMap K M (Q (Φ (d, w))) =
      ∑ i, τ (d i) * d i + algebraMap K M (Q (Φ (0, w))) := by
    have hcoord : ∀ (i : Fin n) (u : M),
        algebraMap K M (Q (Φ (Pi.single i u, 0))) = τ u * u := by
      intro i u
      obtain ⟨a, haA, hane⟩ := hmoved i
      obtain ⟨c, hc3, hact⟩ := hdiag a haA
      exact normFrame_coord hτsq hK hcardM hpolar hAO i a haA hane hc3 hact u
    exact normFrame_Q hpolar hcoord
  have hEdiag : ∀ e ∈ E, ∃ a : Fin n → M, (∀ i, a i ^ 3 = 1) ∧
      ∀ d w, (e : V ≃ₗ[K] V) (Φ (d, w)) = Φ (fun i => a i * d i, w) := by
    intro e he
    exact hdiag (e : V ≃ₗ[K] V) (Subgroup.mem_map.mpr ⟨e, he, rfl⟩)
  refine ⟨n, M, hMfield, hMfin, hMalg, τ, U, hUadd, hUmod, Φ, hcardM, hτsq, hpolar,
    hN, hEdiag, ?_⟩
  intro a ha3
  have ha0 : ∀ i, a i ≠ 0 := by
    intro i h
    have h3 := ha3 i
    rw [h, zero_pow (by norm_num)] at h3
    exact zero_ne_one h3
  let u : Fin n → Mˣ := fun i => Units.mk0 (a i) (ha0 i)
  have hu : ∀ i, (u i : M) ^ 3 = 1 := by
    intro i
    simpa [u] using ha3 i
  let t : V ≃ₗ[K] V := normFrameTorus Φ u
  have htapply : ∀ d w, t (Φ (d, w)) = Φ (fun i => a i * d i, w) := by
    intro d w
    change normFrameTorus Φ u (Φ (d, w)) = Φ (fun i => a i * d i, w)
    rw [normFrameTorus_apply]
    congr 1
  have htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    change normFrameTorus Φ u ∈ TauCeti.QuadraticMap.orthogonalGroup Q
    exact normFrameTorus_mem_orthogonal hτsq hN hu
  have ht3 : t ^ 3 = 1 := by
    change normFrameTorus Φ u ^ 3 = 1
    exact normFrameTorus_pow_three hu
  have hrO : normFrameFrob (τ := τ) hK Φ ∈
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    normFrameFrob_mem_orthogonal hK hcardM hτsq hN
  have hcomm : ⁅normFrameFrob (τ := τ) hK Φ, t⁆ = t := by
    change ⁅normFrameFrob (τ := τ) hK Φ, normFrameTorus Φ u⁆ = normFrameTorus Φ u
    exact normFrameFrob_commutator_torus hK hcardM hτsq
  have htD : t ∈ orthDerived Q := by
    have hmem := Subgroup.commutator_mem_commutator hrO htO
    rwa [hcomm] at hmem
  let e : ↥(orthDerived Q) := ⟨t, htD⟩
  have he3 : e ^ 3 = 1 := Subtype.ext ht3
  have hecomm : ∀ f ∈ E, e * f = f * e := by
    intro f hf
    obtain ⟨b, hb3, hfact⟩ := hEdiag f hf
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    have heapply : ∀ d w, (e : V ≃ₗ[K] V) (Φ (d, w)) =
        Φ (fun i => a i * d i, w) := by
      intro d w
      change t (Φ (d, w)) = Φ (fun i => a i * d i, w)
      exact htapply d w
    have hfapply : ∀ d w, (f : V ≃ₗ[K] V) (Φ (d, w)) =
        Φ (fun i => b i * d i, w) := hfact
    rw [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply]
    simp only [heapply, hfapply]
    congr 1
    refine Prod.ext ?_ rfl
    funext i
    ring
  refine ⟨e, hsc e (Subgroup.mem_centralizer_iff.mpr ?_) he3, ?_⟩
  · intro f hf
    exact (hecomm f hf).symm
  · intro d w
    exact htapply d w

end CFSG.StandardType

end

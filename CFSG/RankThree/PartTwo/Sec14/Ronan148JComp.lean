module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
public import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofComp

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG
open scoped commutatorElement Pointwise

variable {X : Type} [Group X]

theorem conj_mem_centralizer_of_mem_normalizer {J : Subgroup X} {g c : X}
    (hg : g ∈ Subgroup.normalizer (J : Set X)) (hc : c ∈ Subgroup.centralizer (J : Set X)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (J : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
  have h1 := Subgroup.mem_centralizer_iff.mp hc _ hx'
  simp only [inv_inv] at h1
  calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * x := by group

theorem le_centralizer_of_forall_inv_mul_mem {A E J R : Subgroup X}
    (hRJ : R ≤ Subgroup.normalizer (J : Set X)) (hEJ : E ≤ Subgroup.normalizer (J : Set X))
    (hRA : R ≤ ⁅R, A⁆) (hRE : R ≤ Subgroup.centralizer (E : Set X))
    (hA : ∀ a ∈ A, ∃ e ∈ E, e⁻¹ * a ∈ Subgroup.centralizer (J : Set X)) :
    R ≤ Subgroup.centralizer (J : Set X) := by
  refine hRA.trans ?_
  rw [Subgroup.commutator_le]
  intro r hr a ha
  obtain ⟨e, he, hc⟩ := hA a ha
  have hre : r * e = e * r := (Subgroup.mem_centralizer_iff.mp (hRE hr) e he).symm
  have hrc : r * (e⁻¹ * a) * r⁻¹ ∈ Subgroup.centralizer (J : Set X) :=
    conj_mem_centralizer_of_mem_normalizer (hRJ hr) hc
  have hmem : r * (e⁻¹ * a) * r⁻¹ * (e⁻¹ * a)⁻¹ ∈ Subgroup.centralizer (J : Set X) :=
    mul_mem hrc (inv_mem hc)
  have h1 : e * r * e⁻¹ = r := by rw [← hre]; group
  have heq : ⁅r, a⁆ = e * (r * (e⁻¹ * a) * r⁻¹ * (e⁻¹ * a)⁻¹) * e⁻¹ := by
    calc ⁅r, a⁆ = (e * r * e⁻¹) * a * r⁻¹ * a⁻¹ := by rw [h1, commutatorElement_def]
      _ = e * (r * (e⁻¹ * a) * r⁻¹ * (e⁻¹ * a)⁻¹) * e⁻¹ := by group
  rw [heq]
  exact conj_mem_centralizer_of_mem_normalizer (hEJ he) hmem

theorem le_of_forall_inv_mul_mem {A J R : Subgroup X}
    (hAJ : A ≤ Subgroup.normalizer (J : Set X)) (hRJ : R ≤ Subgroup.normalizer (J : Set X))
    (hRA : R ≤ ⁅R, A⁆)
    (hA : ∀ a ∈ A, ∃ e ∈ A, e ∈ Subgroup.centralizer (R : Set X) ∧ e⁻¹ * a ∈ J) :
    R ≤ J := by
  refine hRA.trans ?_
  rw [Subgroup.commutator_le]
  intro r hr a ha
  obtain ⟨e, he, heR, hu⟩ := hA a ha
  have hre : r * e = e * r := (Subgroup.mem_centralizer_iff.mp heR r hr)
  have hru : r * (e⁻¹ * a) * r⁻¹ ∈ J :=
    (Subgroup.mem_normalizer_iff.mp (hRJ hr) _).mp hu
  have hmem : r * (e⁻¹ * a) * r⁻¹ * (e⁻¹ * a)⁻¹ ∈ J := mul_mem hru (inv_mem hu)
  have h1 : e * r * e⁻¹ = r := by rw [← hre]; group
  have heq : ⁅r, a⁆ = e * (r * (e⁻¹ * a) * r⁻¹ * (e⁻¹ * a)⁻¹) * e⁻¹ := by
    calc ⁅r, a⁆ = (e * r * e⁻¹) * a * r⁻¹ * a⁻¹ := by rw [h1, commutatorElement_def]
      _ = e * (r * (e⁻¹ * a) * r⁻¹ * (e⁻¹ * a)⁻¹) * e⁻¹ := by group
  rw [heq]
  exact (Subgroup.mem_normalizer_iff.mp (hAJ he) _).mp hmem

theorem sup_eq_or_sup_eq {A E C D : Subgroup X} (hEA : E ≤ A) (hEne : E ≠ A)
    (hmax : ∀ H : Subgroup X, E ≤ H → H ≤ A → H = E ∨ H = A)
    (hCA : C ≤ A) (hDA : D ≤ A) (hCD : C ⊔ D = A) : E ⊔ C = A ∨ E ⊔ D = A := by
  rcases hmax (E ⊔ C) le_sup_left (sup_le hEA hCA) with hC | hC
  · rcases hmax (E ⊔ D) le_sup_left (sup_le hEA hDA) with hD | hD
    · exfalso
      apply hEne
      refine le_antisymm hEA ?_
      rw [← hCD]
      exact sup_le (hC ▸ le_sup_right) (hD ▸ le_sup_right)
    · exact Or.inr hD
  · exact Or.inl hC

theorem exists_inv_mul_mem_of_mem_sup {E C : Subgroup X} (hEC : E ≤ Subgroup.normalizer (C : Set X))
    {a : X} (ha : a ∈ E ⊔ C) : ∃ e ∈ E, e⁻¹ * a ∈ C := by
  have ha' : a ∈ ((E : Set X) * (C : Set X)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right E C hEC]
    exact ha
  obtain ⟨e, he, c, hc, rfl⟩ := ha'
  refine ⟨e, he, ?_⟩
  simpa using hc

theorem le_normalizer_of_mem_component [Finite X] {J R : Subgroup X} {j : X}
    (hJ : IsComponent J) (hjJ : j ∈ J) (hjZ : ∃ y ∈ J, j * y ≠ y * j) (hj3 : j ^ 3 = 1)
    (hR3 : Nat.Coprime 3 (Nat.card R)) (hjR : j ∈ Subgroup.normalizer (R : Set X)) :
    R ≤ Subgroup.normalizer (J : Set X) := by
  intro r hr
  set S := R ⊓ Subgroup.normalizer (J : Set X) with hS
  have hjN : j ∈ Subgroup.normalizer (J : Set X) := Subgroup.le_normalizer hjJ
  have hB3 : IsPGroup 3 (Subgroup.zpowers j) := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hj3, one_zpow]
  have hS3 : Nat.Coprime 3 (Nat.card S) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hR3
  set J' := J.map (MulAut.conj r).toMonoidHom with hJ'def
  have hJ' : IsComponent J' := Res2LBal.isComponent_conj hJ r
  have hjJ' : j ∈ Subgroup.normalizer (J' : Set X) := by
    by_cases h : J' = J
    · rw [h]; exact hjN
    · exact Subgroup.centralizer_le_normalizer _
        (Res2LBal.mem_centralizer_of_mem_of_ne hJ' hJ h hjJ)
  have hjS : j ∈ Subgroup.normalizer (S : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxR, hxN⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hjR x).mp hxR,
        (Subgroup.normalizer (J : Set X)).mul_mem
          ((Subgroup.normalizer (J : Set X)).mul_mem hjN hxN)
          ((Subgroup.normalizer (J : Set X)).inv_mem hjN)⟩
    · rintro ⟨hxR, hxN⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hjR x).mpr hxR, ?_⟩
      have := (Subgroup.normalizer (J : Set X)).mul_mem
        ((Subgroup.normalizer (J : Set X)).mul_mem
          ((Subgroup.normalizer (J : Set X)).inv_mem hjN) hxN) hjN
      simpa [mul_assoc] using this
  have hBS : Subgroup.zpowers j ≤ Subgroup.normalizer (S : Set X) :=
    Subgroup.zpowers_le.mpr hjS
  have hk : ∀ b ∈ Subgroup.zpowers j, r⁻¹ * (b * r * b⁻¹) ∈ S := by
    intro b hb
    have hbR : b ∈ Subgroup.normalizer (R : Set X) := (Subgroup.zpowers_le.mpr hjR) hb
    have hbN : b ∈ Subgroup.normalizer (J : Set X) := (Subgroup.zpowers_le.mpr hjN) hb
    have hbJ' : b ∈ Subgroup.normalizer (J' : Set X) := (Subgroup.zpowers_le.mpr hjJ') hb
    refine ⟨R.mul_mem (R.inv_mem hr) ((Subgroup.mem_normalizer_iff.mp hbR r).mp hr), ?_⟩
    have h1 : r⁻¹ * b * r ∈ Subgroup.normalizer (J : Set X) :=
      Item148Res5.mem_normalizer_map_conj_iff.mp hbJ'
    have h2 := (Subgroup.normalizer (J : Set X)).mul_mem h1
      ((Subgroup.normalizer (J : Set X)).inv_mem hbN)
    simpa [mul_assoc] using h2
  obtain ⟨y, hy, hyj⟩ := exists_commute_mem_coset148 hB3 hS3 hBS hk
  have hyN : r⁻¹ * y ∈ Subgroup.normalizer (J : Set X) := hy.2
  have hJy : J.map (MulAut.conj y).toMonoidHom = J' :=
    (Item148Res5.map_conj_eq_map_conj_iff.mpr hyN).symm
  have hjy : j ∈ J' := by
    rw [← hJy]
    have h := Res2LBal.conj_mem_map hjJ y
    have hc : y * j * y⁻¹ = j := by
      rw [← hyj j (Subgroup.mem_zpowers j)]; group
    rwa [hc] at h
  by_contra hrN
  have hne : J ≠ J' := by
    intro h
    apply hrN
    exact Item148Res5.map_conj_eq_iff.mp h.symm
  obtain ⟨x, hx, hjx⟩ := hjZ
  exact hjx (Subgroup.mem_centralizer_iff.mp
    (Res2LBal.mem_centralizer_of_mem_of_ne hJ hJ' hne hjy) x hx).symm

end CFSG.RankThree.PartTwo.Sec14.Ronan148J

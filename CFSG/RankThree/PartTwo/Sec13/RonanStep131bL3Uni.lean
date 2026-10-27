module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bL3Diag
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bL3Fix
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
import CFSG.RankThree.PartTwo.KFacts.AutPSUDet
import CFSG.RankThree.PartTwo.KFacts.AutPSUOrderThree

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b.L3

open Matrix CFSG.SectionRank.OddCover CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem diagHom_mem_unitaryIsom3 {d : Fin 3 → Kˣ} (hd : ∀ i, d i ∈ normOne K (p ^ f)) :
    diagHom 3 d ∈ unitaryIsom3 h := by
  have hp : p ≠ 0 := h.prime.ne_zero
  rw [mem_unitaryIsom3, coe_diagHom,
    Matrix.diagonal_map (by simp [h.bar_apply, zero_pow (pow_ne_zero f hp)]),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have hi := mem_normOne.1 (hd i)
  rw [h.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, hi, Units.val_one]

theorem cycGL_mem_unitaryIsom3 : (cycGL : GL (Fin 3) K) ∈ unitaryIsom3 h := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI := h.charP
  exact unitarySU_le_unitaryIsom3 (monomialData_statedSU (p := p) (f := f)).cyc_mem

theorem card_unitaryIsom3 (h : UnitaryFieldData p f K) :
    Nat.card (unitaryIsom3 h) =
      (p ^ f + 1) * ((p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
  haveI := h.finite
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI := h.charP
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  set δ : unitaryIsom3 h →* Kˣ := GeneralLinearGroup.det.comp (unitaryIsom3 h).subtype with hδ
  have hδx : ∀ x : unitaryIsom3 h,
      ((δ x : Kˣ) : K) = ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := fun x => by
    simp [hδ, GeneralLinearGroup.val_det_apply]
  have hker : δ.ker = (unitarySU p f K 3).subgroupOf (unitaryIsom3 h) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_unitarySU_iff h]
    refine ⟨fun hx => ⟨?_, mem_unitaryIsom3.mp x.2⟩, fun hx => ?_⟩
    · rw [← hδx, hx, Units.val_one]
    · apply Units.ext
      rw [hδx, Units.val_one]
      exact hx.1
  have hrange : δ.range = normOne K (p ^ f) := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      rw [mem_normOne]
      apply Units.ext
      have hn := norm_det_of_mem_unitaryIsom3 x.2
      rw [UnitaryFieldData.norm, h.bar_apply, ← pow_succ'] at hn
      rw [Units.val_pow_eq_pow_val, hδx, hn, Units.val_one]
    · intro hu
      have hd : ∀ i, (![u, 1, 1] : Fin 3 → Kˣ) i ∈ normOne K (p ^ f) := by
        intro i
        fin_cases i
        · exact hu
        · exact one_mem _
        · exact one_mem _
      refine ⟨⟨diagHom 3 ![u, 1, 1], diagHom_mem_unitaryIsom3 hd⟩, ?_⟩
      apply Units.ext
      rw [hδx]
      change ((diagHom 3 ![u, 1, 1] : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = _
      rw [det_diagHom_three]
      simp
  have h1 := Subgroup.card_mul_index δ.ker
  rw [Subgroup.index_ker, hrange, hker, card_normOne hK,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe unitarySU_le_unitaryIsom3).toEquiv,
    card_statedSU_three hK] at h1
  rw [← h1, mul_comm]

theorem card_GU_three_eq {q : ℕ} (hq : q % 3 = 2) :
    ∃ i : ℕ, ¬ 3 ∣ i ∧ (q + 1) * (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) = 3 * (q + 1) ^ 3 * i := by
  obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 2 := ⟨q / 3, by omega⟩
  refine ⟨(3 * t + 2) ^ 3 * (3 * t + 1) * (3 * t ^ 2 + 3 * t + 1), ?_, ?_⟩
  · intro h
    have := Nat.mod_eq_zero_of_dvd h
    simp [Nat.mul_mod, Nat.pow_mod, Nat.add_mod] at this
  · have h1 : 1 ≤ (3 * t + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1]
    ring

theorem signDiag_le_unitarySU (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) :
    (signDiag : Subgroup (GL (Fin 3) K)) ≤ unitarySU p f K 3 := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI := h.charP
  rintro _ ⟨d, rfl, hd, hd'⟩
  refine (monomialData_statedSU (p := p) (f := f)).diag_mem d (fun i => ?_) hd'
  rw [mem_normOne]
  obtain ⟨m, hm⟩ := hq.add_one
  rw [hm, ← two_mul, pow_mul, hd i, one_pow]

@[expose] def signSU (p f : ℕ) (K : Type) [Field K] : Subgroup (unitarySU p f K 3) :=
  (signDiag (K := K)).comap (unitarySU p f K 3).subtype

@[expose] noncomputable def signPSU (h : UnitaryFieldData p f K) : Subgroup (unitaryPSU h 3) :=
  (signSU p f K).map (unitaryProj h 3)

theorem isPGroup_signPSU : IsPGroup 2 (signPSU h) := by
  intro x
  obtain ⟨x, hx⟩ := x
  obtain ⟨g, hg, rfl⟩ := hx
  have hg' : g ∈ signSU p f K := hg
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have h1 : ((g : unitarySU p f K 3) : GL (Fin 3) K) ^ 2 = 1 := sq_eq_one_of_mem_signDiag hg'
  have h2 : g ^ 2 = 1 := Subtype.ext h1
  change unitaryProj h 3 g ^ 2 ^ 1 = 1
  rw [pow_one, ← map_pow, h2, map_one]

theorem psuConj_mem_signPSU {n : unitaryIsom3 h}
    (hn : (n : GL (Fin 3) K) ∈ Subgroup.normalizer (signDiag (K := K) : Set (GL (Fin 3) K)))
    {x : unitaryPSU h 3} (hx : x ∈ signPSU h) : psuConj h n x ∈ signPSU h := by
  obtain ⟨g, hg, rfl⟩ := hx
  have hg' : g ∈ signSU p f K := hg
  refine ⟨suConj h n g, ?_, rfl⟩
  rw [SetLike.mem_coe]
  show ((suConj h n g : unitarySU p f K 3) : GL (Fin 3) K) ∈ signDiag
  rw [coe_suConj]
  exact (Subgroup.mem_normalizer_iff.mp hn _).mp hg'

theorem signPSU_ne_bot (hq : Odd (p ^ f)) (hp2 : p ≠ 2) : signPSU h ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI := h.charP
  have hd : diagHom 3 ![(1 : Kˣ), -1, -1] ∈ unitarySU p f K 3 :=
    signDiag_le_unitarySU h hq ⟨![1, -1, -1], rfl,
      fun i => by fin_cases i <;> simp [neg_one_sq], by simp [neg_mul_neg]⟩
  have hmem : (⟨_, hd⟩ : unitarySU p f K 3) ∈ signSU p f K :=
    ⟨![1, -1, -1], rfl, fun i => by fin_cases i <;> simp [neg_one_sq], by simp [neg_mul_neg]⟩
  intro hbot
  have hx : unitaryProj h 3 ⟨_, hd⟩ ∈ signPSU h := ⟨_, hmem, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hx
  have hx' : (⟨_, hd⟩ : unitarySU p f K 3) ∈ unitaryScalars h 3 :=
    (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.mp hx'
  have h00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hc
  have h11 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) hc
  simp [coe_diagHom, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h00 h11
  have h2 : (2 : K) = 0 := by linear_combination h00 - h11
  have h2' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
  have := (CharP.cast_eq_zero_iff K p 2).mp h2'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp this)

theorem mem_range_psuConj_of_pow_three (hq : 2 < p ^ f) (hno : ∀ τ : K ≃+* K, orderOf τ ≠ 3)
    {σ : MulAut (unitaryPSU h 3)} (hσ : σ ^ 3 = 1) : σ ∈ (psuConj h).range := by
  by_contra hnot
  obtain ⟨τ, hτ, -⟩ := unitary_order_three_field_descent hq σ hσ hnot
  exact hno τ hτ

theorem norm2e_unitaryPSU (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f) (hq3 : p ^ f % 3 = 2)
    (hodd : Odd (p ^ f)) (hp2 : p ≠ 2) (hno : ∀ τ : K ≃+* K, orderOf τ ≠ 3)
    (P : Subgroup (MulAut (unitaryPSU h 3))) (hP : IsPGroup 3 P) (hP3 : ∀ σ ∈ P, σ ^ 3 = 1) :
    ∃ V : Subgroup (unitaryPSU h 3), V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ∀ σ ∈ P, V.map σ.toMonoidHom = V := by
  haveI := h.finite
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨i, hi3, hGU⟩ := card_GU_three_eq hq3
  have hle : diagSub (normOne K (p ^ f)) ⊔ Subgroup.zpowers (cycGL : GL (Fin 3) K) ≤
      unitaryIsom3 h := by
    refine sup_le ?_ (Subgroup.zpowers_le.mpr cycGL_mem_unitaryIsom3)
    intro g hg
    obtain ⟨d, hd, rfl⟩ := mem_diagSub.mp hg
    exact diagHom_mem_unitaryIsom3 hd
  have hNcard : Nat.card ((diagSub (normOne K (p ^ f)) ⊔
      Subgroup.zpowers (cycGL : GL (Fin 3) K)).subgroupOf (unitaryIsom3 h)) =
      3 * (p ^ f + 1) ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_diagSub_sup_cyc,
      card_normOne hK]
  have hN : ¬ 3 ∣ ((diagSub (normOne K (p ^ f)) ⊔
      Subgroup.zpowers (cycGL : GL (Fin 3) K)).subgroupOf (unitaryIsom3 h)).index := by
    rw [index_eq_of_card_eq _ (i := i) (by rw [hNcard, card_unitaryIsom3 h, hGU])]
    exact hi3
  exact exists_stable_subgroup (psuConj h) hN (signPSU_ne_bot hodd hp2) isPGroup_signPSU
    (fun n hn x hx => psuConj_mem_signPSU (diagSub_sup_cyc_le_normalizer_signDiag _
      (Subgroup.mem_subgroupOf.mp hn)) hx) hP
    (fun σ hσ => mem_range_psuConj_of_pow_three hq2 hno (hP3 σ hσ))

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b.L3

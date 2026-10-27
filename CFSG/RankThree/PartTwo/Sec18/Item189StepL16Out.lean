module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
import CFSG.RankThree.PartTwo.Sec18.Item189StepProofOddL2

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG.RankThree.PartOne.KCRootAxis CFSG.ComponentClassification.OuterAutomorphisms

section ExponentTwo

variable {X : Type*} [Group X]

theorem mul_comm_of_mul_self189 {T : Subgroup X} (hT2 : ∀ t ∈ T, t * t = 1) {s t : X}
    (hs : s ∈ T) (ht : t ∈ T) : s * t = t * s :=
  calc s * t = (s * t)⁻¹ := (inv_eq_of_mul_eq_one_right (hT2 _ (T.mul_mem hs ht))).symm
    _ = t⁻¹ * s⁻¹ := mul_inv_rev s t
    _ = t * s := by
      rw [inv_eq_of_mul_eq_one_right (hT2 s hs), inv_eq_of_mul_eq_one_right (hT2 t ht)]

theorem card_le_card_inf_centralizer_sq189 [Finite X] {T : Subgroup X}
    (hT2 : ∀ t ∈ T, t * t = 1) {σ : X} (hσT : ∀ t ∈ T, σ * t * σ⁻¹ ∈ T) (hσ2 : σ * σ ∈ T) :
    Nat.card T ≤ Nat.card ↥(T ⊓ Subgroup.centralizer {σ}) ^ 2 := by
  set E := T ⊓ Subgroup.centralizer {σ}
  have hc : ∀ {s t : X}, s ∈ T → t ∈ T → s * t = t * s := fun hs ht =>
    mul_comm_of_mul_self189 hT2 hs ht
  have hmem : ∀ t : T, (t : X) * (σ * t * σ⁻¹) ∈ E := by
    intro t
    refine Subgroup.mem_inf.mpr ⟨T.mul_mem t.2 (hσT t t.2),
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : σ * σ * (t : X) = t * (σ * σ) := hc hσ2 t.2
    have h2 : (t : X) * (σ * t * σ⁻¹) = σ * t * σ⁻¹ * t := hc t.2 (hσT t t.2)
    calc (t : X) * (σ * t * σ⁻¹) * σ = σ * t * σ⁻¹ * t * σ := by rw [h2]
      _ = σ * t * σ⁻¹ * (t * (σ * σ)) * σ⁻¹ := by group
      _ = σ * t * σ⁻¹ * (σ * σ * t) * σ⁻¹ := by rw [h1]
      _ = σ * ((t : X) * (σ * t * σ⁻¹)) := by group
  let f : T →* E := MonoidHom.mk' (fun t => ⟨(t : X) * (σ * t * σ⁻¹), hmem t⟩) (by
    intro s t
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have h3 : (t : X) * (σ * s * σ⁻¹) = σ * s * σ⁻¹ * t := hc t.2 (hσT s s.2)
    calc (s : X) * t * (σ * (s * t) * σ⁻¹) = s * (t * (σ * s * σ⁻¹)) * (σ * t * σ⁻¹) := by
          group
      _ = s * (σ * s * σ⁻¹ * t) * (σ * t * σ⁻¹) := by rw [h3]
      _ = s * (σ * s * σ⁻¹) * (t * (σ * t * σ⁻¹)) := by group)
  have hker : Nat.card f.ker ≤ Nat.card E := by
    have hk : ∀ k : f.ker, ((k : T) : X) ∈ E := by
      intro k
      have h : ((k : T) : X) * (σ * k * σ⁻¹) = 1 := congrArg Subtype.val k.2
      refine Subgroup.mem_inf.mpr ⟨(k : T).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h4 : σ * ((k : T) : X) * σ⁻¹ = k :=
        (eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right (hT2 _ (k : T).2))
      calc ((k : T) : X) * σ = σ * k * σ⁻¹ * σ := by rw [h4]
        _ = σ * k := by group
    refine Nat.card_le_card_of_injective (fun k => ⟨(k : T), hk k⟩) ?_
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun e : E => (e : X)) hab))
  rw [← Subgroup.card_ker_mul_card_range f, sq]
  exact Nat.mul_le_mul hker (Subgroup.card_le_card_group _)

end ExponentTwo

theorem eq_of_mul_self_eq_one189 {Y : Type*} [Group Y] [Finite Y] [IsCyclic Y] {a b : Y}
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  have := Fintype.ofFinite Y
  by_contra hab
  have hle := IsCyclic.card_pow_eq_one_le (α := Y) (n := 2) two_pos
  have hsub : ({1, a, b} : Finset Y) ⊆ Finset.univ.filter (fun g : Y => g ^ 2 = 1) := by
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, sq]
    rcases hg with rfl | rfl | rfl
    · exact one_mul 1
    · exact ha
    · exact hb
  have hcard : ({1, a, b} : Finset Y).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha1, Ne.symm hb1]), Finset.card_pair hab]
  have := (Finset.card_le_card hsub).trans hle
  omega

theorem mul_self_eq_one_of_mem_closure189 {X Y : Type*} [Group X] [Group Y] [IsMulCommutative Y]
    (Ψ : X →* Y) {S : Set X} (hS : ∀ z ∈ S, z * z = 1) {u : X} (hu : u ∈ Subgroup.closure S) :
    Ψ u * Ψ u = 1 := by
  induction hu using Subgroup.closure_induction with
  | mem z hz => rw [← map_mul, hS z hz, map_one]
  | one => rw [map_one, one_mul]
  | mul a b _ _ ha hb =>
    calc Ψ (a * b) * Ψ (a * b) = Ψ a * (Ψ b * Ψ a) * Ψ b := by rw [map_mul]; group
      _ = Ψ a * (Ψ a * Ψ b) * Ψ b := by rw [mul_comm' (Ψ b)]
      _ = (Ψ a * Ψ a) * (Ψ b * Ψ b) := by group
      _ = 1 := by rw [ha, hb, one_mul]
  | inv a _ ha => rw [map_inv, ← mul_inv_rev, ha, inv_one]

section Outer

variable {X : Type*} [Group X] {Kb : Subgroup X} [Kb.Normal]

theorem eq_of_conjNormal_eq189 (hC : Subgroup.centralizer (Kb : Set X) = ⊥) {x : X} {y : Kb}
    (hy : (MulAut.conjNormal x : MulAut Kb) = MulAut.conj y) : x = y := by
  have hmem : (y : X)⁻¹ * x ∈ Subgroup.centralizer (Kb : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun ψ : MulAut Kb => ((ψ ⟨k, hk⟩ : Kb) : X)) hy
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    calc k * ((y : X)⁻¹ * x) = (y : X)⁻¹ * ((y : X) * k * (y : X)⁻¹) * x := by group
      _ = (y : X)⁻¹ * (x * k * x⁻¹) * x := by rw [h1]
      _ = ((y : X)⁻¹ * x) * k := by group
  rw [hC, Subgroup.mem_bot] at hmem
  calc x = (y : X) * ((y : X)⁻¹ * x) := by group
    _ = y := by rw [hmem, mul_one]

theorem exists_hom_outer189 {Y : Type*} [Group Y] (φ : Kb ≃* Y)
    (hC : Subgroup.centralizer (Kb : Set X) = ⊥) :
    ∃ Ψ : X →* Outer Y, ∀ x, Ψ x = 1 ↔ x ∈ Kb := by
  refine ⟨(QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner Y)).comp
    ((MulAut.congr φ).toMonoidHom.comp MulAut.conjNormal), fun x => ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨M, hM⟩
    have hy : (MulAut.conjNormal x : MulAut Kb) = MulAut.conj (φ.symm M) := by
      apply (MulAut.congr φ).injective
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
      exact hM.symm
    rw [eq_of_conjNormal_eq189 hC hy]
    exact (φ.symm M).2
  · intro hx
    refine ⟨φ ⟨x, hx⟩, ?_⟩
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom]
    congr 1
    ext k
    simp [MulAut.conjNormal_apply]

end Outer

theorem mul_self_eq_one_of_le189 {X : Type*} [Group X] {Kb : Subgroup X} {F : Type} [Field F]
    [CharP F 2] [Finite F] (φ : Kb ≃* SL₂ F) {R : Subgroup X} (hR : IsPGroup 2 R)
    (hRK : R ≤ Kb) {t : X} (ht : t ∈ R) : t * t = 1 := by
  obtain ⟨v, hv0, hv⟩ := exists_fixed_ne_zero189 ((hR.comap_subtype (K := Kb)).map φ.toMonoidHom)
  have hmem : φ ⟨t, hRK ht⟩ ∈ (R.comap Kb.subtype).map φ.toMonoidHom :=
    Subgroup.mem_map_of_mem φ.toMonoidHom (show (⟨t, hRK ht⟩ : Kb) ∈ R.comap Kb.subtype from ht)
  have h := mul_self_eq_one_of_mulVec_eq189 hv0 (hv _ hmem)
  rw [← map_mul] at h
  exact congrArg Subtype.val (φ.injective (h.trans (map_one φ).symm))

theorem card_sl2_sixteen189 : Nat.card (SL₂ (GaloisField 2 4)) = 4080 := by
  have := Fintype.ofFinite (GaloisField 2 4)
  have hq : Fintype.card (GaloisField 2 4) = 16 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 4 (by norm_num)]
    norm_num
  rw [Matrix.card_SL_field, Fin.prod_univ_two, hq]
  norm_num

theorem pow_dvd_card_inf189 {X : Type*} [Group X] [Finite X] {Kb : Subgroup X} [Kb.Normal]
    (P : Sylow 2 X) {k : ℕ} (hk : 2 ^ k ∣ Nat.card Kb) :
    2 ^ k ∣ Nat.card ↥((P : Subgroup X) ⊓ Kb) := by
  have h2 := Subgroup.relIndex_mul_card Kb (P : Subgroup X)
  have h3 := Subgroup.relIndex_mul_card Kb ((P : Subgroup X) ⊔ Kb)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : Kb ≤ (P : Subgroup X) ⊔ Kb)]
    at h3
  have h4 := Subgroup.card_subgroup_dvd_card ((P : Subgroup X) ⊔ Kb)
  rw [← h3, ← Subgroup.card_mul_index (P : Subgroup X), ← h2, inf_comm, mul_assoc] at h4
  have hr : 0 < Kb.relIndex P := by
    rcases Nat.eq_zero_or_pos (Kb.relIndex P) with h0 | h0
    · rw [h0, zero_mul] at h2
      exact absurd h2.symm Nat.card_pos.ne'
    · exact h0
  have hcop : Nat.Coprime (2 ^ k) (P : Subgroup X).index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr P.not_dvd_index)
  exact hcop.dvd_of_dvd_mul_right (hk.trans (Nat.dvd_of_mul_dvd_mul_left hr h4))

theorem exists_le_centralizer_omega_sl2_sixteen189 {X : Type} [Group X] [Finite X]
    {Kb : Subgroup X} [Kb.Normal]
    (φ : Kb ≃* CFSG.RankThree.PartOne.KCRootAxis.SL₂ (GaloisField 2 4))
    (hC : Subgroup.centralizer (Kb : Set X) = ⊥) {Q : Subgroup X} (hQ : IsPGroup 2 Q) :
    ∃ E : Subgroup X, E ≤ Kb ∧
      E ≤ Subgroup.centralizer
        ((Subgroup.closure {z : X | z ∈ Q ∧ z * z = 1} : Subgroup X) : Set X) ∧
      4 ≤ Nat.card E ∧ ∀ e ∈ E, e * e = 1 := by
  obtain ⟨P, hQP⟩ := hQ.exists_le_sylow
  set T : Subgroup X := (P : Subgroup X) ⊓ Kb
  set Ω : Subgroup X := Subgroup.closure {z : X | z ∈ Q ∧ z * z = 1}
  have hΩP : Ω ≤ P := (Subgroup.closure_le _).mpr fun z hz => hQP hz.1
  have hT2 : ∀ t ∈ T, t * t = 1 := fun t ht =>
    mul_self_eq_one_of_le189 φ P.isPGroup'.to_inf_left inf_le_right ht
  have hc : ∀ {s t : X}, s ∈ T → t ∈ T → s * t = t * s := fun hs ht =>
    mul_comm_of_mul_self189 hT2 hs ht
  have h16 : 16 ≤ Nat.card T := by
    have hK : 2 ^ 4 ∣ Nat.card Kb := by
      rw [Nat.card_congr φ.toEquiv, card_sl2_sixteen189]
      norm_num
    exact Nat.le_of_dvd Nat.card_pos (pow_dvd_card_inf189 P hK)
  obtain ⟨Ψ, hΨ⟩ := exists_hom_outer189 φ hC
  have : IsCyclic (Outer (SL₂ (GaloisField 2 4))) := out_sl2_isCyclic
  have hΩ2 : ∀ u ∈ Ω, Ψ u * Ψ u = 1 := fun u hu =>
    mul_self_eq_one_of_mem_closure189 Ψ (fun z hz => hz.2) hu
  have hTmem : ∀ u ∈ Ω, Ψ u = 1 → u ∈ T := fun u hu h1 => ⟨hΩP hu, (hΨ u).mp h1⟩
  by_cases hall : ∀ u ∈ Ω, Ψ u = 1
  ·
    refine ⟨T, inf_le_right, fun e he => ?_, by omega, hT2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact hc (hTmem u hu (hall u hu)) he
  ·
    push Not at hall
    obtain ⟨σ, hσΩ, hσ1⟩ := hall
    have hσP : σ ∈ (P : Subgroup X) := hΩP hσΩ
    have hσT : ∀ t ∈ T, σ * t * σ⁻¹ ∈ T := fun t ht =>
      ⟨(P : Subgroup X).mul_mem ((P : Subgroup X).mul_mem hσP ht.1) ((P : Subgroup X).inv_mem hσP),
        (inferInstance : Kb.Normal).conj_mem t ht.2 σ⟩
    have hσ2 : σ * σ ∈ T :=
      ⟨(P : Subgroup X).mul_mem hσP hσP, (hΨ _).mp (by rw [map_mul]; exact hΩ2 σ hσΩ)⟩
    refine ⟨T ⊓ Subgroup.centralizer {σ}, inf_le_left.trans inf_le_right, fun e he => ?_, ?_,
      fun e he => hT2 e he.1⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have heσ : e * σ = σ * e := Subgroup.mem_centralizer_singleton_iff.mp he.2
      by_cases hu1 : Ψ u = 1
      · exact hc (hTmem u hu hu1) he.1
      · have heq : Ψ u = Ψ σ := eq_of_mul_self_eq_one189 (hΩ2 u hu) (hΩ2 σ hσΩ) hu1 hσ1
        have hv : σ⁻¹ * u ∈ T := hTmem _ (Ω.mul_mem (Ω.inv_mem hσΩ) hu)
          (by rw [map_mul, map_inv, heq, inv_mul_cancel])
        calc u * e = σ * ((σ⁻¹ * u) * e) := by group
          _ = σ * (e * (σ⁻¹ * u)) := by rw [hc hv he.1]
          _ = (σ * e) * (σ⁻¹ * u) := by group
          _ = (e * σ) * (σ⁻¹ * u) := by rw [heσ]
          _ = e * u := by group
    · have hle := card_le_card_inf_centralizer_sq189 hT2 hσT hσ2
      by_contra hlt
      have : Nat.card ↥(T ⊓ Subgroup.centralizer {σ}) ^ 2 ≤ 3 ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      omega

end CFSG.RankThree.PartTwo.Sec18

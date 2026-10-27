module

public import CFSG.Quasithin.H13.HSLocR
public import CFSG.Quasithin.H13.HSLocK

public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank CFSG.Quasithin.H13.LocDbl.Dc
open CFSG.RankThree.Native CFSG.Open

@[expose] def HasFix (E : Subgroup PG) (X : PG) : Prop :=
  ∀ q < 100, ((∀ z ∈ E, act 100 z q = q) ↔ q ∈ F0.map (act 100 X))

theorem act_conj' (g z : PG) {p : ℕ} (hp : p < 100) :
    act 100 (g⁻¹ * z * g) p = act 100 g⁻¹ (act 100 z (act 100 g p)) := by
  rw [act_mul _ _ hp, act_mul _ _ (act_lt _ hp)]

theorem act_inv_act (g : PG) {p : ℕ} (hp : p < 100) : act 100 g⁻¹ (act 100 g p) = p := by
  rw [← act_mul _ _ hp, inv_mul_cancel, act_one hp]

theorem exists_hasFix {B E : Subgroup PG} (hEab : IsElemAbelian 2 E) (hEcard : Nat.card E = 16)
    (hB5 : 5 ∣ Nat.card B) (hBnorm : B ≤ Subgroup.normalizer (E : Set PG)) :
    ∃ X : PG, HasFix E X := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y₀', hy₀'⟩ := exists_prime_orderOf_dvd_card' 5 hB5
  set y : PG := (y₀' : PG) with hy
  have hyB : y ∈ B := y₀'.2
  have hord : orderOf y = 5 := by rw [hy, Subgroup.orderOf_coe]; exact hy₀'
  have hnorm : ∀ z ∈ E, y * z * y⁻¹ ∈ E := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (hBnorm hyB) z).mp hz
  obtain ⟨X, hX, hfix⟩ := Certificates.certificate589206.2.2.2.2.2.2.2.2
    (E.map hs100P.subtype) (Subgroup.map_subtype_le E)
    (fun x hx => by
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, hEab.2 z hz, map_one])
    (by rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]; exact hEcard)
    (y : Equiv.Perm (Fin 100)) y.2 (by rw [Subgroup.orderOf_coe]; exact hord)
    (fun x hx => by
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_map.mpr ⟨_, hnorm z hz, by simp⟩)
  exact ⟨⟨X, hX⟩, fixF0_iff_perm.2 hfix⟩

theorem pres_of_hasFix {E : Subgroup PG} {X : PG} (hX : HasFix E X) {c : Equiv.Perm (Fin 100)}
    (hc : ∀ z ∈ E, ∃ z' ∈ E,
      (z : Equiv.Perm (Fin 100)) * c = c * (z' : Equiv.Perm (Fin 100))) :
    Pres ((X : Equiv.Perm (Fin 100))⁻¹ * c * (X : Equiv.Perm (Fin 100))) := by
  intro f hf
  have hfl := F0_lt f hf
  have hq : act 100 X f < 100 := act_lt _ hfl
  have hqfix : ∀ z ∈ E, act 100 z (act 100 X f) = act 100 X f :=
    (hX _ hq).mpr (List.mem_map_of_mem hf)
  have hcq : act 100 c (act 100 X f) < 100 := act_lt _ hq
  have hcfix : ∀ z ∈ E, act 100 z (act 100 c (act 100 X f)) = act 100 c (act 100 X f) := by
    intro z hz
    obtain ⟨z', hz', hzz⟩ := hc z hz
    have e1 : act 100 ((z : Equiv.Perm (Fin 100)) * c) (act 100 X f) =
        act 100 (c * (z' : Equiv.Perm (Fin 100))) (act 100 X f) := by rw [hzz]
    rw [act_mul _ _ hq, act_mul _ _ hq] at e1
    have e2 : act 100 (z' : Equiv.Perm (Fin 100)) (act 100 X f) = act 100 X f := hqfix z' hz'
    rw [e2] at e1
    exact e1
  obtain ⟨f', hf', hf'e⟩ := List.mem_map.mp ((hX _ hcq).mp hcfix)
  have e : act 100 ((X : Equiv.Perm (Fin 100))⁻¹ * c * (X : Equiv.Perm (Fin 100))) f =
      act 100 (X : Equiv.Perm (Fin 100))⁻¹ (act 100 c (act 100 X f)) := by
    rw [act_mul _ _ hfl, act_mul _ _ (act_lt _ hfl)]
    rfl
  rw [e, ← hf'e]
  have hf'l := F0_lt f' hf'
  have : act 100 (X : Equiv.Perm (Fin 100))⁻¹ (act 100 (X : Equiv.Perm (Fin 100)) f') = f' := by
    rw [← act_mul _ _ hf'l, inv_mul_cancel, act_one hf'l]
  rw [show act 100 X f' = act 100 (X : Equiv.Perm (Fin 100)) f' from rfl, this]
  exact hf'

theorem normLv_PG {B P E : Subgroup PG}
    (hperf : ⁅B, B⁆ = B) (hcardB : Nat.card B = 360 * Nat.card P) (hEP : E ≤ P)
    (hEab : IsElemAbelian 2 E) (hEcard : Nat.card E = 16)
    (hBnorm : B ≤ Subgroup.normalizer (E : Set PG))
    {r : Equiv.Perm (Fin 100)} (hr : r ∈ hs100R)
    (hrE : ∀ z ∈ E, r * (z : Equiv.Perm (Fin 100)) = (z : Equiv.Perm (Fin 100)) * r)
    (hrB : ∀ b ∈ B, r * (b : Equiv.Perm (Fin 100)) = (b : Equiv.Perm (Fin 100)) * r) : r = 1 := by
  classical
  haveI : Fintype PG := Fintype.ofFinite PG
  have h5 : 5 ∣ Nat.card B := by rw [hcardB]; exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨X, hX⟩ := exists_hasFix hEab hEcard h5 hBnorm
  set f : PG →* PG := (MulAut.conj X⁻¹).toMonoidHom with hf
  set B' : Subgroup PG := B.map f with hB'
  have hbnorm : ∀ b ∈ B, ∀ z ∈ E, ∃ z' ∈ E,
      (z : Equiv.Perm (Fin 100)) * (b : Equiv.Perm (Fin 100)) =
        (b : Equiv.Perm (Fin 100)) * (z' : Equiv.Perm (Fin 100)) := by
    intro b hb z hz
    have hbn := Subgroup.mem_normalizer_iff.mp (hBnorm hb)
    refine ⟨b⁻¹ * z * b, ?_, ?_⟩
    · have e : b * (b⁻¹ * z * b) * b⁻¹ = z := by group
      have := (hbn (b⁻¹ * z * b)).mpr (by rw [e]; exact hz)
      exact this
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
  have hB'Mg : B' ≤ Mg := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    have hpres := pres_of_hasFix hX (c := (b : Equiv.Perm (Fin 100))) (hbnorm b hb)
    rw [mem_Mg_iff]
    have e : f b = X⁻¹ * b * X := by simp [hf, MulAut.conj_apply]
    rw [e]
    exact hpres
  have hperf' : ⁅B', B'⁆ = B' := by
    rw [hB', ← Subgroup.map_commutator, hperf]
  have hB'Q0 : B' ≤ Q0 := by
    calc B' = ⁅B', B'⁆ := hperf'.symm
      _ ≤ Q0 := by
        refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
        rw [commutatorElement_def]
        exact comm_fix01 (Mg_le_Q01 (hB'Mg hg₁)) (Mg_le_Q01 (hB'Mg hg₂))
  have hP16 : 16 ≤ Nat.card P :=
    Nat.le_of_dvd Nat.card_pos (hEcard ▸ Subgroup.card_dvd_of_le hEP)
  have hB'card : 5760 ≤ Nat.card B' := by
    rw [hB', Subgroup.card_map_of_injective (MulAut.conj X⁻¹).injective, hcardB]
    omega
  let S : Finset PG := Finset.univ.filter (· ∈ B')
  have hScard : S.card = Nat.card B' := by
    simp [S, Nat.card_eq_fintype_card, Fintype.card_subtype]
  let S' : Finset PG := Finset.univ.filter fun g => g ∈ Mg ∧ act 100 g 0 = 0 ∧ act 100 g 1 = 1
  have hS'card : S'.card ≤ 5760 := card_fix01_le S' (fun g hg => by simpa [S'] using hg)
  have hSsub : S ⊆ S' := fun g hg => by
    have hgB' : g ∈ B' := by simpa [S] using hg
    simp only [S', Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hB'Mg hgB', (hB'Q0 hgB').1, (hB'Q0 hgB').2⟩
  have hSeq : S = S' := Finset.eq_of_subset_of_card_le hSsub (by omega)
  have hk1 : k1 ∈ B' := by
    have : k1 ∈ S' := by
      simp only [S', Finset.mem_filter, Finset.mem_univ, true_and]
      exact k_props.1
    rw [← hSeq] at this
    simpa [S] using this
  have hk2 : k2 ∈ B' := by
    have : k2 ∈ S' := by
      simp only [S', Finset.mem_filter, Finset.mem_univ, true_and]
      exact k_props.2
    rw [← hSeq] at this
    simpa [S] using this
  obtain ⟨b1, hb1, hb1e⟩ := Subgroup.mem_map.mp hk1
  obtain ⟨b2, hb2, hb2e⟩ := Subgroup.mem_map.mp hk2
  have hXR : (X : Equiv.Perm (Fin 100)) ∈ hs100R := hs100P_le_R X.2
  have hr' : (X : Equiv.Perm (Fin 100))⁻¹ * r * (X : Equiv.Perm (Fin 100)) ∈ hs100R :=
    hs100R.mul_mem (hs100R.mul_mem (hs100R.inv_mem hXR) hr) hXR
  have hpres' : Pres ((X : Equiv.Perm (Fin 100))⁻¹ * r * (X : Equiv.Perm (Fin 100))) :=
    pres_of_hasFix hX fun z hz => ⟨z, hz, (hrE z hz).symm⟩
  have hcomm : ∀ b ∈ B,
      ((X : Equiv.Perm (Fin 100))⁻¹ * r * (X : Equiv.Perm (Fin 100))) *
          ((X : Equiv.Perm (Fin 100))⁻¹ * (b : Equiv.Perm (Fin 100)) * (X : Equiv.Perm (Fin 100))) =
        ((X : Equiv.Perm (Fin 100))⁻¹ * (b : Equiv.Perm (Fin 100)) * (X : Equiv.Perm (Fin 100))) *
          ((X : Equiv.Perm (Fin 100))⁻¹ * r * (X : Equiv.Perm (Fin 100))) := by
    intro b hb
    calc _ = (X : Equiv.Perm (Fin 100))⁻¹ * (r * (b : Equiv.Perm (Fin 100))) *
          (X : Equiv.Perm (Fin 100)) := by group
      _ = (X : Equiv.Perm (Fin 100))⁻¹ * ((b : Equiv.Perm (Fin 100)) * r) *
          (X : Equiv.Perm (Fin 100)) := by rw [hrB b hb]
      _ = _ := by group
  have e1 : (k1 : Equiv.Perm (Fin 100)) =
      (X : Equiv.Perm (Fin 100))⁻¹ * (b1 : Equiv.Perm (Fin 100)) * (X : Equiv.Perm (Fin 100)) := by
    rw [← hb1e]; simp [hf, MulAut.conj_apply]
  have e2 : (k2 : Equiv.Perm (Fin 100)) =
      (X : Equiv.Perm (Fin 100))⁻¹ * (b2 : Equiv.Perm (Fin 100)) * (X : Equiv.Perm (Fin 100)) := by
    rw [← hb2e]; simp [hf, MulAut.conj_apply]
  have hk1c := hcomm b1 hb1
  have hk2c := hcomm b2 hb2
  rw [← e1] at hk1c
  rw [← e2] at hk2c
  have hrr := R_step hr' hpres' hk1c hk2c
  have : r = (X : Equiv.Perm (Fin 100)) * 1 * (X : Equiv.Perm (Fin 100))⁻¹ := by
    rw [← hrr]; group
  simpa using this

end CFSG.Quasithin.H13.LocDbl.HSLoc

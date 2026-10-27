module

public import CFSG.Quasithin.Vol2.Ch3E213MP6EB
public import CFSG.Quasithin.Vol2.E2StatementsAS
import all CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6Enc

public section

namespace CFSG.Quasithin.Ch3E213M.P6E

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Borel252.A6 Equiv

private theorem mem_S06_iff {x : P6} : x ∈ S06 ↔ x ∈ D0 ∨ x * zB ∈ D0 := Iff.rfl

private theorem D0_le_S06 : D0 ≤ S06 := fun _ hx => mem_S06_iff.2 (Or.inl hx)

private theorem enc_mem_S06_iff {x : P6} : x ∈ S06 ↔ R6.enc x ∈ d0L ++ d0L.map (· * R6.enc zB) := by
  refine ⟨enc_mem_s06L, fun h => ?_⟩
  rcases List.mem_append.1 h with h | h
  · exact mem_S06_iff.2 (Or.inl ((mem_D0 x).2 h))
  · obtain ⟨r, hr, hrx⟩ := List.mem_map.1 h
    obtain ⟨y, hy, rfl⟩ := sound_D0 r hr
    have hxy : x = y * zB := R6.enc_inj (by rw [R6.enc_mul]; exact hrx.symm)
    exact mem_S06_iff.2 (Or.inr (by rw [hxy, mul_assoc, zB_mul_self, mul_one]; exact hy))

private theorem card_S06 : Nat.card S06 = 16 := by
  have hnd : (d0L ++ d0L.map (· * R6.enc zB)).Nodup := by decide +kernel
  have hlen : (d0L ++ d0L.map (· * R6.enc zB)).length = 16 := by
    rw [List.length_append, List.length_map, sizes_ok.1]
  have hs : ∀ r ∈ d0L ++ d0L.map (· * R6.enc zB), ∃ x : P6, R6.enc x = r := by
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · obtain ⟨x, -, hx⟩ := sound_D0 r hr
      exact ⟨x, hx⟩
    · obtain ⟨r', hr', hr⟩ := List.mem_map.1 hr
      obtain ⟨x, -, hx⟩ := sound_D0 r' hr'
      refine ⟨x * zB, ?_⟩
      rw [R6.enc_mul, hx]
      exact hr
  exact (card_of_list R6.enc_inj S06 _ hnd (fun _ => enc_mem_S06_iff) hs).trans hlen

private theorem Nat_card_P6 : Nat.card P6 = 720 := by
  rw [Nat.card_perm, Nat.card_fin] <;> decide

theorem isSylowTwoOf_S06 : IsSylowTwoOf (S06 : Subgroup P6) ⊤ := by
  have h16 : Nat.card S06 = 2 ^ 4 := card_S06.trans (by norm_num)
  refine ⟨le_top, IsPGroup.of_card h16, ?_⟩
  rw [show (S06.subgroupOf ⊤).index = S06.index from Subgroup.relIndex_top_right S06]
  have h := Subgroup.card_mul_index S06
  rw [card_S06, Nat_card_P6] at h
  omega

private theorem conj_mem_D0_of_mem_normalizer_S06 {y : P6} (hy : y ∈ Subgroup.normalizer (S06 : Set P6))
    {d : P6} (hd : d ∈ D0) : y * d * y⁻¹ ∈ D0 := by
  have h1 : y * d * y⁻¹ ∈ S06 := (Subgroup.mem_normalizer_iff.1 hy d).1 (D0_le_S06 hd)
  have h2 : y * d * y⁻¹ ∈ A6s :=
    (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem d (D0_le_A6 hd) y
  exact mem_of_mem_extZ_of_mem (X := D0) (hX := le_rfl) h1 h2

theorem normalizer_S06_le : Subgroup.normalizer (S06 : Set P6) ≤ S06 := by
  intro x hx
  refine normalizer_D0_le (Subgroup.mem_normalizer_iff.2 fun d => ⟨fun hd => ?_, fun hd => ?_⟩)
  · exact conj_mem_D0_of_mem_normalizer_S06 hx hd
  · have hd' : x * d * x⁻¹ ∈ D0 := hd
    have h := conj_mem_D0_of_mem_normalizer_S06 (Subgroup.inv_mem _ hx) hd'
    have e : x⁻¹ * (x * d * x⁻¹) * x⁻¹⁻¹ = d := by group
    rwa [e] at h

private theorem zA_mem_Z6 : zA ∈ Z6 := Or.inl ⟨zA_mem_VA, zA_mem_VB⟩

private theorem enc_zA_comm_s06 :
    ∀ r ∈ d0L ++ d0L.map (· * R6.enc zB), R6.enc zA * r = r * R6.enc zA := by
  decide +kernel

private theorem enc_zB_comm_s06 :
    ∀ r ∈ d0L ++ d0L.map (· * R6.enc zB), R6.enc zB * r = r * R6.enc zB := by
  decide +kernel

private theorem zA_mem_centralizer_S06 : zA ∈ Subgroup.centralizer (S06 : Set P6) := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  rw [enc_eq_iff, R6.enc_mul, R6.enc_mul]
  exact (enc_zA_comm_s06 _ (enc_mem_S06_iff.1 hs)).symm

private theorem zB_mem_centralizer_S06 : zB ∈ Subgroup.centralizer (S06 : Set P6) := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  rw [enc_eq_iff, R6.enc_mul, R6.enc_mul]
  exact (enc_zB_comm_s06 _ (enc_mem_S06_iff.1 hs)).symm

private theorem mem_Z6_cases {z : P6} (hz : z ∈ Z6) : z = 1 ∨ z = zA ∨ z = zB ∨ z = zA * zB := by
  rcases hz with hz | hz
  · rcases mem_inf_VA_VB hz with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases mem_inf_VA_VB hz with h | h
    · refine Or.inr (Or.inr (Or.inl ?_))
      calc z = z * zB * zB := by rw [mul_assoc, zB_mul_self, mul_one]
        _ = zB := by rw [h, one_mul]
    · refine Or.inr (Or.inr (Or.inr ?_))
      calc z = z * zB * zB := by rw [mul_assoc, zB_mul_self, mul_one]
        _ = zA * zB := by rw [h]

theorem Z6_le_centralizer_S06 : Z6 ≤ Subgroup.centralizer (S06 : Set P6) := by
  intro z hz
  rcases mem_Z6_cases hz with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact zA_mem_centralizer_S06
  · exact zB_mem_centralizer_S06
  · exact Subgroup.mul_mem _ zA_mem_centralizer_S06 zB_mem_centralizer_S06

private theorem zA_apply_zero : zA 0 = 2 := by decide +kernel

private theorem zA_apply_one : zA 1 = 3 := by decide +kernel

private theorem zA_apply_four : zA 4 = 4 := by decide +kernel

private theorem zA_apply_five : zA 5 = 5 := by decide +kernel

private theorem zA_fixed : ∀ y : Fin 6, zA y = y → y = 4 ∨ y = 5 := by decide +kernel

private theorem tuple_mem_S06 : ∀ a b e f : Fin 6, [a, b, zA a, zA b, e, f].Nodup →
    (e = 4 ∨ e = 5) → (f = 4 ∨ f = 5) →
    (⟨a, b, zA a, zA b, e, f⟩ : R6) ∈ d0L ++ d0L.map (· * R6.enc zB) := by
  decide +kernel

theorem centralizer_Z6_le_S06 : Subgroup.centralizer (Z6 : Set P6) ≤ S06 := by
  intro x hx
  have hxz : x * zA = zA * x := (Subgroup.mem_centralizer_iff.1 hx zA zA_mem_Z6).symm
  have hc : ∀ i : Fin 6, x (zA i) = zA (x i) := fun i => by
    have h := congrArg (fun σ : P6 => σ i) hxz
    simpa only [Equiv.Perm.mul_apply] using h
  have h2 : x 2 = zA (x 0) := by
    have h := hc 0
    rwa [zA_apply_zero] at h
  have h3 : x 3 = zA (x 1) := by
    have h := hc 1
    rwa [zA_apply_one] at h
  have h4 : x 4 = 4 ∨ x 4 = 5 := zA_fixed (x 4) (by
    have h := hc 4
    rw [zA_apply_four] at h
    exact h.symm)
  have h5 : x 5 = 4 ∨ x 5 = 5 := zA_fixed (x 5) (by
    have h := hc 5
    rw [zA_apply_five] at h
    exact h.symm)
  have hnd : [x 0, x 1, x 2, x 3, x 4, x 5].Nodup := by
    have h := List.Nodup.map x.injective (by decide : ([0, 1, 2, 3, 4, 5] : List (Fin 6)).Nodup)
    simpa using h
  have hmem := tuple_mem_S06 (x 0) (x 1) (x 4) (x 5)
    (by rw [h2, h3] at hnd; exact hnd) h4 h5
  apply enc_mem_S06_iff.2
  have e : R6.enc x = ⟨x 0, x 1, zA (x 0), zA (x 1), x 4, x 5⟩ := by
    show (⟨x 0, x 1, x 2, x 3, x 4, x 5⟩ : R6) = _
    rw [h2, h3]
  rw [e]
  exact hmem

private def Q45 : Subgroup P6 where
  carrier := {σ | ∀ x : Fin 6, (x = 4 ∨ x = 5) ↔ (σ x = 4 ∨ σ x = 5)}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := by
    intro σ τ hσ hτ x
    exact (hτ x).trans (hσ (τ x))
  inv_mem' := by
    intro σ hσ x
    have e : σ (σ⁻¹ x) = x := by
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    have h := hσ (σ⁻¹ x)
    rw [e] at h
    exact h.symm

private theorem mem_Q45_iff {σ : P6} :
    σ ∈ Q45 ↔ ∀ x : Fin 6, (x = 4 ∨ x = 5) ↔ (σ x = 4 ∨ σ x = 5) :=
  Iff.rfl

private theorem d0L_fix : ∀ r ∈ d0L, ∀ i : Fin 6, (i = 4 ∨ i = 5) ↔ (r.get i = 4 ∨ r.get i = 5) := by
  decide +kernel

private theorem D0_le_Q45 : D0 ≤ Q45 := by
  intro d hd
  refine mem_Q45_iff.2 fun x => ?_
  have h := d0L_fix (R6.enc d) ((mem_D0 d).1 hd) x
  rwa [R6.get_enc] at h

private theorem zB_mem_Q45 : zB ∈ Q45 := mem_Q45_iff.2 (by decide +kernel)

private theorem S06_le_Q45 : S06 ≤ Q45 := by
  intro s hs
  rcases mem_S06_iff.1 hs with hs | hs
  · exact D0_le_Q45 hs
  · have h := Q45.mul_mem (D0_le_Q45 hs) zB_mem_Q45
    rwa [mul_assoc, zB_mul_self, mul_one] at h

private theorem Q45_ne_top : Q45 ≠ ⊤ := by
  intro h
  have h1 : swap (0 : Fin 6) 4 ∈ Q45 := by
    rw [h]
    exact Subgroup.mem_top _
  have h2 := (mem_Q45_iff.1 h1) 4
  have h3 : ¬ (swap (0 : Fin 6) 4 (4 : Fin 6) = 4 ∨ swap (0 : Fin 6) 4 (4 : Fin 6) = 5) := by
    decide
  exact h3 (h2.1 (Or.inl rfl))

private theorem c3_mem_Q45 : (swap (0 : Fin 6) 1 * swap (1 : Fin 6) 2 : P6) ∈ Q45 :=
  mem_Q45_iff.2 (by decide +kernel)

private theorem c3_not_mem_S06 : (swap (0 : Fin 6) 1 * swap (1 : Fin 6) 2 : P6) ∉ S06 := by
  intro h
  have h' : R6.enc (swap (0 : Fin 6) 1 * swap (1 : Fin 6) 2 : P6) ∉
      d0L ++ d0L.map (· * R6.enc zB) := by
    decide +kernel
  exact h' (enc_mem_S06_iff.1 h)

private theorem Q45_ne_S06 : Q45 ≠ S06 := by
  intro h
  exact c3_not_mem_S06 (by rw [← h]; exact c3_mem_Q45)

private theorem isParabolic2_Q45 : IsParabolic2 ⊤ Q45 :=
  ⟨le_top, S06, isSylowTwoOf_S06, fun _ hx => S06_le_Q45 (normalizer_S06_le hx.2)⟩

theorem exists_parabolic_S06_lt :
    ∃ Q : Subgroup P6, IsParabolic2 ⊤ Q ∧ Q ≠ ⊤ ∧ S06 ≤ Q ∧ Q ≠ S06 :=
  ⟨Q45, isParabolic2_Q45, Q45_ne_top, S06_le_Q45, Q45_ne_S06⟩

theorem not_le_rootGroupOf_Z6 {P : Subgroup P6} (hP : IsMaxParabolic2 ⊤ P) (hSP : S06 ≤ P) :
    ¬ Z6 ≤ CFSG.Quasithin.ASInputs.rootGroupOf P := by
  intro hZ
  have hA : ∀ w ∈ CFSG.Quasithin.ASInputs.twoGen P, w ∈ S06 := by
    intro w hw
    refine centralizer_Z6_le_S06 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hZ hz)).2 w hw
    exact hc.symm
  have hS2 : ∀ s ∈ S06, ∃ k : ℕ, s ^ 2 ^ k = 1 := by
    intro s hs
    obtain ⟨k, hk⟩ := isSylowTwoOf_S06.2.1 ⟨s, hs⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hconj : ∀ x ∈ P, ∀ s ∈ S06, x * s * x⁻¹ ∈ S06 := by
    intro x hx s hs
    obtain ⟨k, hk⟩ := hS2 s hs
    have hmem : x * s * x⁻¹ ∈ Subgroup.closure {y : P6 | y ∈ P ∧ ∃ k : ℕ, y ^ 2 ^ k = 1} :=
      Subgroup.subset_closure ⟨P.mul_mem (P.mul_mem hx (hSP hs)) (P.inv_mem hx), k,
        by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
    exact hA _ hmem
  have hB : P ≤ S06 := by
    intro x hx
    refine normalizer_S06_le (Subgroup.mem_normalizer_iff.2 fun s =>
      ⟨fun hs => hconj x hx s hs, fun hs => ?_⟩)
    have h := hconj x⁻¹ (P.inv_mem hx) (x * s * x⁻¹) hs
    have e : x⁻¹ * (x * s * x⁻¹) * x⁻¹⁻¹ = s := by group
    rwa [e] at h
  obtain ⟨Q, hQ, hQtop, hSQ, hQS⟩ := exists_parabolic_S06_lt
  have hQP : Q = P := hP.2.2 Q hQ hQtop (hB.trans hSQ)
  exact hQS (hQP.trans (le_antisymm hB hSP))

end CFSG.Quasithin.Ch3E213M.P6E

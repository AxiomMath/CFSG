module

public import CFSG.Quasithin.EmptyFaithful.A38c5FmDefs
public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

open CFSG.Open

namespace CFSG.Quasithin.A38c5.Fm

open Equiv

private def rankDm (m : Fin 16) : P8 :=
  (if m.val % 2 = 1 then swap (0 : Fin 8) 1 else 1) *
    (if m.val / 2 % 2 = 1 then swap (2 : Fin 8) 3 else 1) *
    (if m.val / 4 % 2 = 1 then swap (4 : Fin 8) 5 else 1) *
    (if m.val / 8 % 2 = 1 then swap (6 : Fin 8) 7 else 1)

private theorem rank_dm_mem (m : Fin 16) : rankDm m ∈ D8 := by
  have h0 : swap (0 : Fin 8) 1 ∈ D8 := Subgroup.subset_closure (by simp)
  have h1 : swap (2 : Fin 8) 3 ∈ D8 := Subgroup.subset_closure (by simp)
  have h2 : swap (4 : Fin 8) 5 ∈ D8 := Subgroup.subset_closure (by simp)
  have h3 : swap (6 : Fin 8) 7 ∈ D8 := Subgroup.subset_closure (by simp)
  unfold rankDm
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_ <;> split_ifs <;>
    first | exact one_mem _ | assumption

private theorem rank_dm_mul :
    ∀ m m' : Fin 16, ∃ m'' : Fin 16, rankDm m * rankDm m' = rankDm m'' := by
  decide +kernel

private theorem rank_dm_inv : ∀ m : Fin 16, (rankDm m)⁻¹ = rankDm m := by decide +kernel

private theorem rank_exists_dm {σ : P8} (hσ : σ ∈ D8) : ∃ m : Fin 16, σ = rankDm m := by
  unfold D8 at hσ
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨1, by decide +kernel⟩
    · exact ⟨2, by decide +kernel⟩
    · exact ⟨4, by decide +kernel⟩
    · exact ⟨8, by decide +kernel⟩
  | one => exact ⟨0, by decide +kernel⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨m', rfl⟩ := hy
    exact rank_dm_mul m m'
  | inv x _ hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨m, rank_dm_inv m⟩

private theorem rank_closure_comm {S : Set P8} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => hS y hy x hx
  intro x hx y hy
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.closure_le_centralizer_centralizer S hy) x (h1 hx)

private theorem rank_closure_sq {S : Set P8} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hsq : ∀ x ∈ S, x * x = 1) : ∀ x ∈ Subgroup.closure S, x * x = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hc := rank_closure_comm hS x hx y hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x _ ih => rw [← mul_inv_rev, ih, inv_one]

private def RankValid4 (B : Finset (Fin 8)) (u v w z : Fin 8) : Prop :=
  u ≠ v ∧ u ≠ w ∧ u ≠ z ∧ v ≠ w ∧ v ≠ z ∧ w ≠ z ∧
    ((u ∈ B ∧ v ∈ B ∧ w ∈ B ∧ z ∈ B) ∨ (u ∉ B ∧ v ∉ B ∧ w ∉ B ∧ z ∉ B))

private instance (B : Finset (Fin 8)) (u v w z : Fin 8) : Decidable (RankValid4 B u v w z) := by
  unfold RankValid4; infer_instance

private def RankCset (B : Finset (Fin 8)) : Set P8 :=
  {σ | ∃ u v w z, RankValid4 B u v w z ∧ σ = swap u v * swap w z}

private theorem rank_valid4_map {B : Finset (Fin 8)} {g : P8} (hg : g ∈ PStab B)
    {u v w z : Fin 8} (h : RankValid4 B u v w z) : RankValid4 B (g u) (g v) (g w) (g z) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨g.injective.ne h1, g.injective.ne h2, g.injective.ne h3, g.injective.ne h4,
    g.injective.ne h5, g.injective.ne h6, ?_⟩
  rcases hg with hg | hg
  · rcases h7 with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
    · exact Or.inl ⟨(hg u).2 a, (hg v).2 b, (hg w).2 c, (hg z).2 d⟩
    · exact Or.inr ⟨fun h => a ((hg u).1 h), fun h => b ((hg v).1 h), fun h => c ((hg w).1 h),
        fun h => d ((hg z).1 h)⟩
  · rcases h7 with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
    · exact Or.inr ⟨fun h => (hg u).1 h a, fun h => (hg v).1 h b, fun h => (hg w).1 h c,
        fun h => (hg z).1 h d⟩
    · exact Or.inl ⟨(hg u).2 a, (hg v).2 b, (hg w).2 c, (hg z).2 d⟩

private theorem rank_conj_Cset {B : Finset (Fin 8)} {g : P8} (hg : g ∈ PStab B) {σ : P8}
    (hσ : σ ∈ RankCset B) : g * σ * g⁻¹ ∈ RankCset B := by
  obtain ⟨u, v, w, z, hv, rfl⟩ := hσ
  refine ⟨g u, g v, g w, g z, rank_valid4_map hg hv, ?_⟩
  rw [Equiv.swap_apply_apply g u v, Equiv.swap_apply_apply g w z]
  group

private theorem rank_conj_closure {B : Finset (Fin 8)} {g : P8} (hg : g ∈ PStab B) {x : P8}
    (hx : x ∈ Subgroup.closure (RankCset B)) : g * x * g⁻¹ ∈ Subgroup.closure (RankCset B) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (rank_conj_Cset hg hx)
  | one => simp
  | mul x y _ _ ihx ihy =>
    have h : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [h]
    exact mul_mem ihx ihy
  | inv x _ ih =>
    have h : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [h]
    exact inv_mem ih

private theorem rank_residual_le {B : Finset (Fin 8)} :
    oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) ≤ PStab B := by
  unfold oPrimeResidualOf
  rw [Subgroup.closure_le]
  intro y hy
  exact hy.1.2

private theorem rank_mem_core {B : Finset (Fin 8)} {T₁ : Subgroup P8} (hT : T₁ ≤ PStab B)
    (hD : D8 ≤ T₁) (cl : Fin 6 → P8)
    (hCl : ∀ u v w z, RankValid4 B u v w z → ∃ i, swap u v * swap w z = cl i)
    (hCcomm : ∀ i j, cl i * cl j = cl j * cl i) (hCinv : ∀ i, cl i * cl i = 1)
    {x : P8} (hxD : x ∈ D8) (hxC : x ∈ RankCset B) :
    x ∈ pCoreOf 2 (oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) ⊔ T₁) := by
  set H := oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) ⊔ T₁ with hH
  have hHle : H ≤ PStab B := sup_le rank_residual_le hT
  have hCset_cl : ∀ σ ∈ RankCset B, ∃ i, σ = cl i := by
    rintro σ ⟨u, v, w, z, hv, rfl⟩
    exact hCl u v w z hv
  have hS : ∀ s ∈ RankCset B, ∀ t ∈ RankCset B, s * t = t * s := by
    intro s hs t ht
    obtain ⟨i, rfl⟩ := hCset_cl s hs
    obtain ⟨j, rfl⟩ := hCset_cl t ht
    exact hCcomm i j
  have hsq : ∀ s ∈ RankCset B, s * s = 1 := by
    intro s hs
    obtain ⟨i, rfl⟩ := hCset_cl s hs
    exact hCinv i
  set V := Subgroup.closure (RankCset B) with hV
  have hkey : ∀ g ∈ H, ∀ n ∈ V ⊓ H, g * n * g⁻¹ ∈ V ⊓ H := fun g hg n hn =>
    ⟨rank_conj_closure (hHle hg) hn.1, H.mul_mem (H.mul_mem hg hn.2) (H.inv_mem hg)⟩
  have hnorm : H ≤ Subgroup.normalizer ((V ⊓ H : Subgroup P8) : Set P8) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨hkey h hh n, fun hn => ?_⟩
    have := hkey h⁻¹ (H.inv_mem hh) _ hn
    have e : h⁻¹ * (h * n * h⁻¹) * h⁻¹⁻¹ = n := by group
    rwa [e] at this
  have hQp : IsPGroup 2 ↥(V ⊓ H) := by
    intro q
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    exact rank_closure_sq hS hsq q.1 q.2.1
  have hxV : x ∈ V := Subgroup.subset_closure hxC
  have hxH : x ∈ H := Subgroup.mem_sup_right (hD hxD)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm hQp ⟨hxV, hxH⟩

private theorem rank_pgroup_cube {N : Subgroup P8} (hN : IsPGroup 2 ↥N) {y : P8} (hy : y ∈ N)
    (h3 : y ^ 3 = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hN ⟨y, hy⟩
  have hk' : y ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa [Subgroup.coe_pow] using this
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have h4 : orderOf y ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd h1 h2
  rw [hcop.gcd_eq_one] at h4
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)

private def RankGoodR (B : Finset (Fin 8)) (r : P8) : Prop :=
  Equiv.Perm.sign r = 1 ∧ (∀ x, r x ∈ B ↔ x ∈ B) ∧ r ^ 3 = 1 ∧ r ≠ 1

private instance (B : Finset (Fin 8)) (r : P8) : Decidable (RankGoodR B r) := by
  unfold RankGoodR; infer_instance

private def RankCube3 (d r : P8) : Prop :=
  (d * (r * d⁻¹ * r⁻¹)) ^ 3 = 1 ∧ d * (r * d⁻¹ * r⁻¹) ≠ 1

private instance (d r : P8) : Decidable (RankCube3 d r) := by
  unfold RankCube3; infer_instance

private theorem rank_mem_residual {B : Finset (Fin 8)} {r : P8} (h : RankGoodR B r) :
    r ∈ oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) := by
  obtain ⟨hs, hB, h3, h1⟩ := h
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  unfold oPrimeResidualOf
  refine Subgroup.subset_closure ⟨⟨Equiv.Perm.mem_alternatingGroup.mpr hs, Or.inl hB⟩, 1, ?_⟩
  simpa using orderOf_eq_prime h3 h1

private theorem rank_abstract {B : Finset (Fin 8)} {T₁ : Subgroup P8} (hT : T₁ ≤ PStab B)
    (hD : D8 ≤ T₁) (cl : Fin 6 → P8) (m₁ m₂ : Fin 16) (r₁ r₂ : P8)
    (hCl : ∀ u v w z, RankValid4 B u v w z → ∃ i, swap u v * swap w z = cl i)
    (hCcomm : ∀ i j, cl i * cl j = cl j * cl i) (hCinv : ∀ i, cl i * cl i = 1)
    (hx₁ : ∃ u v w z, RankValid4 B u v w z ∧ rankDm m₁ = swap u v * swap w z)
    (hx₂ : ∃ u v w z, RankValid4 B u v w z ∧ rankDm m₂ = swap u v * swap w z)
    (hr₁ : RankGoodR B r₁) (hr₂ : RankGoodR B r₂)
    (hbad : ∀ m : Fin 16, rankDm m ≠ 1 → rankDm m ≠ rankDm m₁ → rankDm m ≠ rankDm m₂ →
      rankDm m ≠ rankDm m₁ * rankDm m₂ → RankCube3 (rankDm m) r₁ ∨ RankCube3 (rankDm m) r₂)
    (hcard : ({1, rankDm m₁, rankDm m₂, rankDm m₁ * rankDm m₂} : Finset P8).card = 4) :
    rk ↥(D8 ⊓ pCoreOf 2 (oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) ⊔ T₁)) = 2 := by
  set H := oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) ⊔ T₁ with hH
  set N := pCoreOf 2 H with hN
  have hx₁N : rankDm m₁ ∈ N := rank_mem_core hT hD cl hCl hCcomm hCinv (rank_dm_mem m₁) hx₁
  have hx₂N : rankDm m₂ ∈ N := rank_mem_core hT hD cl hCl hCcomm hCinv (rank_dm_mem m₂) hx₂
  have hNp : IsPGroup 2 ↥N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N := fun h hh n hn =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh) n).mp hn
  have hr₁H : r₁ ∈ H := Subgroup.mem_sup_left (rank_mem_residual hr₁)
  have hr₂H : r₂ ∈ H := Subgroup.mem_sup_left (rank_mem_residual hr₂)
  have hmem : ∀ σ : P8, σ ∈ D8 ⊓ N ↔
      σ ∈ ({1, rankDm m₁, rankDm m₂, rankDm m₁ * rankDm m₂} : Finset P8) := by
    intro σ
    constructor
    · rintro ⟨hσD, hσN⟩
      obtain ⟨m, rfl⟩ := rank_exists_dm hσD
      by_contra hne
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
      obtain ⟨h1, h2, h3, h4⟩ := hne
      have key : ∀ r ∈ H, RankCube3 (rankDm m) r → False := by
        rintro r hrH ⟨h3', hne1⟩
        have hy : rankDm m * (r * (rankDm m)⁻¹ * r⁻¹) ∈ N :=
          N.mul_mem hσN (hnorm r hrH _ (N.inv_mem hσN))
        exact hne1 (rank_pgroup_cube hNp hy h3')
      rcases hbad m h1 h2 h3 h4 with h | h
      · exact key r₁ hr₁H h
      · exact key r₂ hr₂H h
    · intro hσ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
      rcases hσ with rfl | rfl | rfl | rfl
      · exact ⟨one_mem _, one_mem _⟩
      · exact ⟨rank_dm_mem m₁, hx₁N⟩
      · exact ⟨rank_dm_mem m₂, hx₂N⟩
      · exact ⟨mul_mem (rank_dm_mem m₁) (rank_dm_mem m₂), mul_mem hx₁N hx₂N⟩
  have hcardN : Nat.card ↥(D8 ⊓ N) = 4 := by
    rw [← hcard, Nat.card_congr (Equiv.subtypeEquivRight hmem), Nat.card_eq_fintype_card,
      Fintype.card_coe]
  unfold rk
  rw [hcardN, show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact padicValNat.prime_pow 2

private theorem rank_case1 {T₁ : Subgroup P8} (hT : T₁ ≤ PStab {0, 1, 2, 3}) (hD : D8 ≤ T₁) :
    rk ↥(D8 ⊓ pCoreOf 2
      (oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab {0, 1, 2, 3}) ⊔ T₁)) = 2 :=
  rank_abstract hT hD
    ![swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2,
      swap 4 5 * swap 6 7, swap 4 6 * swap 5 7, swap 4 7 * swap 5 6]
    3 12 (swap 0 1 * swap 1 2) (swap 4 5 * swap 5 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨0, 1, 2, 3, by decide +kernel⟩ ⟨4, 5, 6, 7, by decide +kernel⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem rank_case2 {T₁ : Subgroup P8} (hT : T₁ ≤ PStab {0, 1, 4, 5}) (hD : D8 ≤ T₁) :
    rk ↥(D8 ⊓ pCoreOf 2
      (oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab {0, 1, 4, 5}) ⊔ T₁)) = 2 :=
  rank_abstract hT hD
    ![swap 0 1 * swap 4 5, swap 0 4 * swap 1 5, swap 0 5 * swap 1 4,
      swap 2 3 * swap 6 7, swap 2 6 * swap 3 7, swap 2 7 * swap 3 6]
    5 10 (swap 0 1 * swap 1 4) (swap 2 3 * swap 3 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨0, 1, 4, 5, by decide +kernel⟩ ⟨2, 3, 6, 7, by decide +kernel⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem rank_case3 {T₁ : Subgroup P8} (hT : T₁ ≤ PStab {0, 1, 6, 7}) (hD : D8 ≤ T₁) :
    rk ↥(D8 ⊓ pCoreOf 2
      (oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab {0, 1, 6, 7}) ⊔ T₁)) = 2 :=
  rank_abstract hT hD
    ![swap 0 1 * swap 6 7, swap 0 6 * swap 1 7, swap 0 7 * swap 1 6,
      swap 2 3 * swap 4 5, swap 2 4 * swap 3 5, swap 2 5 * swap 3 4]
    9 6 (swap 0 1 * swap 1 6) (swap 2 3 * swap 3 4)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨0, 1, 6, 7, by decide +kernel⟩ ⟨2, 3, 4, 5, by decide +kernel⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem final_rank {B : Finset (Fin 8)} (hB : B ∈ blocks3) {T₁ : Subgroup P8} (hT : T₁ ≤ PStab B)
    (hD : D8 ≤ T₁) :
    rk ↥(D8 ⊓ pCoreOf 2 (oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ PStab B) ⊔ T₁)) = 2 := by
  simp only [blocks3, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl
  · exact rank_case1 hT hD
  · exact rank_case2 hT hD
  · exact rank_case3 hT hD

end CFSG.Quasithin.A38c5.Fm

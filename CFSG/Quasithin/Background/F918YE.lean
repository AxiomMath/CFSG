module

public import CFSG.Quasithin.Background.D2Decomp
public import CFSG.Quasithin.Background.A1cA131
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open Matrix (SpecialLinearGroup)

private theorem ye_eq_one_of_eq_inv {G : Type*} [Group G] {x : G} (h3 : x ^ 3 = 1)
    (h : x = x⁻¹) : x = 1 := by
  have h2 : x * x = 1 := by
    nth_rewrite 2 [h]
    exact mul_inv_cancel x
  calc x = x * (x * x) := by rw [h2, mul_one]
    _ = x ^ 3 := (pow_three x).symm
    _ = 1 := h3

private theorem ye_cyclic_three {H : Type*} [Group H] [Finite H] [IsCyclic H] {x y : H}
    (hx : x ^ 3 = 1) (hx1 : x ≠ 1) (hy : y ^ 3 = 1) (hy1 : y ≠ 1) : y = x ∨ y = x⁻¹ := by
  classical
  have := Fintype.ofFinite H
  by_contra hne
  push Not at hne
  have hx2 : x ≠ x⁻¹ := fun h => hx1 (ye_eq_one_of_eq_inv hx h)
  have hsub : ({1, x, x⁻¹, y} : Finset H) ⊆ Finset.univ.filter (fun a : H => a ^ 3 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> simp [hx, hy, inv_pow]
  have h4 : ({1, x, x⁻¹, y} : Finset H).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simpa using hne.2.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hx2, hne.1.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hx1.symm, (inv_ne_one.2 hx1).symm, hy1.symm⟩
  have hle := IsCyclic.card_pow_eq_one_le (α := H) (n := 3) (by norm_num)
  have := Finset.card_le_card hsub
  omega

private theorem ye_exists_N {M : Type*} [Group M] {A B c T : M} (hA3 : A ^ 3 = 1)
    (hB3 : B ^ 3 = 1) (hc3 : c ^ 3 = 1) (hAB : Commute A B) (hAc : Commute A c)
    (hBc : Commute B c) (hT2 : T * T = 1) (hTA : T * A * T = A⁻¹) (hTB : T * B * T = B)
    (hTc : T * c * T = c) :
    ∃ N : Subgroup M, A ∈ N ∧ B ∈ N ∧ c ∈ N ∧ (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) ∧
      (∀ x ∈ N, x ^ 3 = 1) ∧ (∀ x ∈ N, T * x * T ∈ N) := by
  have hpw : ({A, B, c} : Set M).Pairwise Commute := by
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact Commute.refl _ | assumption | exact Commute.symm ‹_›
  have hcomm : IsMulCommutative ↥(Subgroup.closure ({A, B, c} : Set M)) :=
    Subgroup.isMulCommutative_closure hpw
  have hNcomm : ∀ x ∈ Subgroup.closure ({A, B, c} : Set M),
      ∀ y ∈ Subgroup.closure ({A, B, c} : Set M), x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hx⟩ : Subgroup.closure ({A, B, c} : Set M))
      ⟨y, hy⟩)
  have hTinv : T⁻¹ = T := inv_eq_of_mul_eq_one_right hT2
  refine ⟨Subgroup.closure ({A, B, c} : Set M), Subgroup.subset_closure (by simp),
    Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp), hNcomm, ?_, ?_⟩
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    | one => exact one_pow 3
    | mul x y hx hy hx3 hy3 =>
      rw [Commute.mul_pow (hNcomm x hx y hy), hx3, hy3, one_mul]
    | inv x hx hx3 => rw [inv_pow, hx3, inv_one]
  · have hle : Subgroup.closure ({A, B, c} : Set M) ≤
        (Subgroup.closure ({A, B, c} : Set M)).comap (MulAut.conj T).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, hTinv]
      rcases hx with rfl | rfl | rfl
      · rw [hTA]
        exact inv_mem (Subgroup.subset_closure (by simp))
      · rw [hTB]
        exact Subgroup.subset_closure (by simp)
      · rw [hTc]
        exact Subgroup.subset_closure (by simp)
    intro x hx
    have := hle hx
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hTinv] using this

private theorem ye_commute_of_conj {G : Type*} [Group G] {T x : G} (hT2 : T * T = 1)
    (h : T * x * T = x) : Commute T x := by
  show T * x = x * T
  calc T * x = T * x * (T * T) := by rw [hT2, mul_one]
    _ = T * x * T * T := (mul_assoc _ _ _).symm
    _ = x * T := by rw [h]

private theorem ye_zpowers_le_normalizer {M : Type*} [Group M] {N : Subgroup M} {T : M}
    (hT2 : T * T = 1) (hTN : ∀ x ∈ N, T * x * T ∈ N) :
    Subgroup.zpowers T ≤ Subgroup.normalizer (N : Set M) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro h
  rw [inv_eq_of_mul_eq_one_right hT2]
  refine ⟨fun hh => hTN h hh, fun hh => ?_⟩
  have h1 := hTN _ hh
  have h2 : T * (T * h * T) * T = h := by
    calc T * (T * h * T) * T = (T * T) * h * (T * T) := by simp only [mul_assoc]
      _ = h := by rw [hT2, one_mul, mul_one]
  rwa [h2] at h1

private theorem ye_mem_sup_zpowers {M : Type*} [Group M] {N : Subgroup M} {T : M}
    (hT2 : T * T = 1) (hnorm : Subgroup.zpowers T ≤ Subgroup.normalizer (N : Set M)) :
    ∀ x ∈ N ⊔ Subgroup.zpowers T, ∃ ν ∈ N, x = ν ∨ x = ν * T := by
  intro x hx
  have hx' : x ∈ (↑(N ⊔ Subgroup.zpowers T) : Set M) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N _ hnorm, Set.mem_mul] at hx'
  obtain ⟨ν, hν, s, hs, rfl⟩ := hx'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  refine ⟨ν, hν, ?_⟩
  have hT2' : T ^ (2 : ℤ) = 1 := by rw [zpow_two, hT2]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [zpow_eq_zpow_emod k hT2', hk]
    simp
  · right
    rw [zpow_eq_zpow_emod k hT2', hk]
    simp

private theorem ye_core {S : Type} {M : Type*} [Group S] [Finite S] [Group M] [Finite M]
    (φ : S →* M) (hφ : Function.Surjective φ) (hS : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 2)
    {A B c T : M} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hAB : Commute A B) (hAc : Commute A c)
    (hBc : Commute B c) (hT2 : T * T = 1) (hT1 : T ≠ 1) (hTA : T * A * T = A⁻¹)
    (hTB : T * B * T = B) (hTc : T * c * T = c) : c = B ∨ c = B⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hNA, hNB, hNc, hNcomm, hN3, hTN⟩ :=
    ye_exists_N hA3 hB3 hc3 hAB hAc hBc hT2 hTA hTB hTc
  have hnorm : Subgroup.zpowers T ≤ Subgroup.normalizer (N : Set M) :=
    ye_zpowers_le_normalizer hT2 hTN
  have hdecomp : ∀ x ∈ N ⊔ Subgroup.zpowers T, ∃ ν ∈ N, x = ν ∨ x = ν * T :=
    ye_mem_sup_zpowers hT2 hnorm
  set Q : Subgroup M := N ⊔ Subgroup.zpowers T with hQ
  have hNQ : N ≤ Q := le_sup_left
  have hTQ : T ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers T)
  have hQnorm : Q ≤ Subgroup.normalizer (N : Set M) := sup_le Subgroup.le_normalizer hnorm
  have hN'normal : (N.subgroupOf Q).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQnorm
  have hN'p : IsPGroup 3 ↥(N.subgroupOf Q) := by
    intro x
    exact ⟨1, Subtype.ext (Subtype.ext (by simpa using hN3 _ (Subgroup.mem_subgroupOf.1 x.2)))⟩
  have hN'P : N.subgroupOf Q ≤ CFSG.Open.pCore 3 ↥Q := le_pCore 3 hN'normal hN'p
  let A' : ↥Q := ⟨A, hNQ hNA⟩
  let B' : ↥Q := ⟨B, hNQ hNB⟩
  let c' : ↥Q := ⟨c, hNQ hNc⟩
  let T' : ↥Q := ⟨T, hTQ⟩
  have hA'P : A' ∈ CFSG.Open.pCore 3 ↥Q := hN'P (Subgroup.mem_subgroupOf.2 hNA)
  have hB'P : B' ∈ CFSG.Open.pCore 3 ↥Q := hN'P (Subgroup.mem_subgroupOf.2 hNB)
  have hc'P : c' ∈ CFSG.Open.pCore 3 ↥Q := hN'P (Subgroup.mem_subgroupOf.2 hNc)
  have hTA' : T * A = A⁻¹ * T := by
    rw [← hTA]
    simp [mul_assoc, hT2]
  have hF : Subgroup.centralizer (CFSG.Open.pCore 3 ↥Q : Set ↥Q) ≤ CFSG.Open.pCore 3 ↥Q := by
    intro x hx
    have hxA : A' * x = x * A' := Subgroup.mem_centralizer_iff.1 hx A' hA'P
    have hxA' : A * (x : M) = (x : M) * A := congrArg Subtype.val hxA
    obtain ⟨ν, hν, hcase⟩ := hdecomp x x.2
    rcases hcase with h | h
    · exact hN'P (Subgroup.mem_subgroupOf.2 (by rw [h]; exact hν))
    · exfalso
      rw [h] at hxA'
      have h1 : A * ν * T = ν * A⁻¹ * T := by
        calc A * ν * T = A * (ν * T) := mul_assoc _ _ _
          _ = ν * T * A := hxA'
          _ = ν * (T * A) := mul_assoc _ _ _
          _ = ν * (A⁻¹ * T) := by rw [hTA']
          _ = ν * A⁻¹ * T := (mul_assoc _ _ _).symm
      have h2 : A * ν = ν * A⁻¹ := mul_right_cancel h1
      have h3 : ν * A = ν * A⁻¹ := by rw [← h2]; exact (hNcomm A hNA ν hν).symm
      exact hA1 (ye_eq_one_of_eq_inv hA3 (mul_left_cancel h3))
  have hT'2 : T' * T' = 1 := Subtype.ext hT2
  have hT'1 : T' ≠ 1 := fun h => hT1 (congrArg Subtype.val h)
  have hTbarp : IsPGroup 2 ↥(Subgroup.zpowers T') := by
    have hord : orderOf T' = 2 := orderOf_eq_prime (by rw [pow_two]; exact hT'2) hT'1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hTbarne : Subgroup.zpowers T' ≠ ⊥ := fun h => hT'1 (Subgroup.zpowers_eq_bot.1 h)
  have hcyc : IsCyclic ↥(CFSG.Open.pCore 3 ↥Q ⊓
      Subgroup.centralizer ((Subgroup.zpowers T' : Subgroup ↥Q) : Set ↥Q)) := by
    have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Q.comap φ)) ≤ 2 :=
      le_trans (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num)
        (Q.comap φ).subtype (Q.comap φ).subtype_injective) hS
    exact (A1c.A131Concl_of_surjective (by norm_num) hF _ ↥(Q.comap φ) (φ.subgroupComap Q)
      (MonoidHom.subgroupComap_surjective φ Q hφ) rfl hrk).1 _ hTbarp hTbarne
  have hcent : ∀ {z : M} (hz : z ∈ Q), T * z * T = z →
      (⟨z, hz⟩ : ↥Q) ∈ Subgroup.centralizer ((Subgroup.zpowers T' : Subgroup ↥Q) : Set ↥Q) := by
    intro z hz hTz
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hcomm : Commute T' ⟨z, hz⟩ := Subtype.ext (ye_commute_of_conj hT2 hTz)
    exact (hcomm.zpow_left k).eq
  have hB'H : B' ∈ CFSG.Open.pCore 3 ↥Q ⊓
      Subgroup.centralizer ((Subgroup.zpowers T' : Subgroup ↥Q) : Set ↥Q) :=
    ⟨hB'P, hcent (hNQ hNB) hTB⟩
  have hc'H : c' ∈ CFSG.Open.pCore 3 ↥Q ⊓
      Subgroup.centralizer ((Subgroup.zpowers T' : Subgroup ↥Q) : Set ↥Q) :=
    ⟨hc'P, hcent (hNQ hNc) hTc⟩
  have := hcyc
  have key := ye_cyclic_three (x := (⟨B', hB'H⟩ : ↥(CFSG.Open.pCore 3 ↥Q ⊓
      Subgroup.centralizer ((Subgroup.zpowers T' : Subgroup ↥Q) : Set ↥Q))))
    (y := ⟨c', hc'H⟩) (Subtype.ext (Subtype.ext hB3)) (fun h => hB1 (congrArg (fun z => z.1.1) h))
    (Subtype.ext (Subtype.ext hc3)) (fun h => hc1 (congrArg (fun z => z.1.1) h))
  rcases key with h | h
  · exact Or.inl (congrArg (fun z => z.1.1) h)
  · exact Or.inr (congrArg (fun z => z.1.1) h)

private def ye_a4 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by decide +kernel⟩

private def ye_b4 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1], by decide +kernel⟩

private def ye_t4 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by decide +kernel⟩

private def ye_g4 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 1, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], by decide +kernel⟩

private def ye_a5 : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨!![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    by decide +kernel⟩

private def ye_b5 : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1],
    by decide +kernel⟩

private def ye_t5 : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨!![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    by decide +kernel⟩

private def ye_g5 : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨!![1, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    by decide +kernel⟩

private theorem ye_elements {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ∃ a b t g : SpecialLinearGroup (Fin n) (ZMod 2), a ^ 3 = 1 ∧ a ≠ 1 ∧ b ^ 3 = 1 ∧ b ≠ 1 ∧
      t * t = 1 ∧ t ≠ 1 ∧ a * b = b * a ∧ t * a * t = a⁻¹ ∧ t * b * t = b ∧
      g * b ≠ b * g := by
  rcases hn with rfl | rfl
  · refine ⟨ye_a4, ye_b4, ye_t4, ye_g4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      decide +kernel
  · refine ⟨ye_a5, ye_b5, ye_t5, ye_g5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      decide +kernel

theorem eq_one_of_pow_three_centralizes_statedSL {M : Type*} [Group M] [Finite M]
    (hM : IsQuotientOfSQTKTC M) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (ρ : ↥(StatedSL n (ZMod 2)) →* M) (hρ : Function.Injective ρ) {c : M} (hc3 : c ^ 3 = 1)
    (hcomm : ∀ g : ↥(StatedSL n (ZMod 2)), c * ρ g = ρ g * c) : c = 1 := by
  by_contra hc1
  obtain ⟨S, _, _, hS, -, φ, hφ⟩ := hM
  obtain ⟨a, b, t, g, ha3, ha1, hb3, hb1, ht2, ht1, hab, hta, htb, hgb⟩ := ye_elements hn
  let ρ' : SpecialLinearGroup (Fin n) (ZMod 2) →* M :=
    ρ.comp (specialLinearGroupEquivStatedSL n (ZMod 2)).toMonoidHom
  have hρ' : Function.Injective ρ' :=
    hρ.comp (specialLinearGroupEquivStatedSL n (ZMod 2)).injective
  have hne : ∀ {x : SpecialLinearGroup (Fin n) (ZMod 2)}, x ≠ 1 → ρ' x ≠ 1 := fun hx h =>
    hx (hρ' (h.trans (map_one ρ').symm))
  have hcom : ∀ x : SpecialLinearGroup (Fin n) (ZMod 2), Commute (ρ' x) c := fun x =>
    (hcomm (specialLinearGroupEquivStatedSL n (ZMod 2) x)).symm
  have hcore := ye_core φ hφ (hS 3 Nat.prime_three (by norm_num)) (A := ρ' a) (B := ρ' b)
    (c := c) (T := ρ' t) (by rw [← map_pow, ha3, map_one]) (hne ha1)
    (by rw [← map_pow, hb3, map_one]) (hne hb1) hc3 hc1 (Commute.map hab ρ') (hcom a)
    (hcom b) (by rw [← map_mul, ht2, map_one]) (hne ht1)
    (by rw [← map_mul, ← map_mul, hta, map_inv])
    (by rw [← map_mul, ← map_mul, htb])
    (by rw [(hcom t).eq, mul_assoc, ← map_mul, ht2, map_one, mul_one])
  have hbg : Commute (ρ' b) (ρ' g) := by
    have h1 : Commute c (ρ' g) := (hcom g).symm
    rcases hcore with h | h
    · rwa [h] at h1
    · rw [h] at h1
      exact Commute.inv_left_iff.1 h1
  exact hgb (hρ' (by rw [map_mul, map_mul]; exact hbg.eq.symm))

end CFSG.Quasithin

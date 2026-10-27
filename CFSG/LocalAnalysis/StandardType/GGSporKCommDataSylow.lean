module

public import CFSG.LocalAnalysis.StandardType.GGSporKCommDataF

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Monster.B.Pinned
open scoped Pointwise

private theorem commData_actMat_pow {G : Type} [Group G] {p n : ℕ} [NeZero p] {q : Fin n → G}
    {z : G} {M : Matrix (Fin n) (Fin n) (ZMod p)} (hD : CommData p q z M) {x : G}
    (hx : ∀ i, x⁻¹ * q i * x ∈ Subgroup.closure (Set.range q)) (k : ℕ) :
    CommData.actMat p q z M (x ^ k) = CommData.actMat p q z M x ^ k := by
  induction k with
  | zero => rw [pow_zero, hD.actMat_one, pow_zero]
  | succ k ih =>
    have hconj : ∀ i, (x ^ k)⁻¹ * q i * x ^ k ∈ Subgroup.closure (Set.range q) :=
      fun i => conj_pow_mem (fun g hg => CommData.conj_mem hx hg) k
        (Subgroup.subset_closure ⟨i, rfl⟩)
    rw [pow_succ, hD.actMat_mul hconj hx, ih, pow_succ]

theorem commData_card_le_of_sylow {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q S : Subgroup G} (hScard : Nat.card S = p ^ (Nat.card G).factorization p)
    (hSN : S ≤ Subgroup.normalizer (Q : Set G))
    (hSC : Nat.card ↥(S ⊓ Subgroup.centralizer (Q : Set G)) ≤ p)
    (P : Subgroup G) (hPC : P ≤ Subgroup.centralizer (Q : Set G)) (hP : IsPGroup p P) :
    Nat.card P ≤ p := by
  classical
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  have hCN : Subgroup.centralizer (Q : Set G) ≤ N :=
    Subgroup.centralizer_le_normalizer (Q : Set G)
  have hPN : P ≤ N := hPC.trans hCN
  have hdvdNG : Nat.card N ∣ Nat.card G := Subgroup.card_subgroup_dvd_card N
  have hle_fact : (Nat.card N).factorization p ≤ (Nat.card G).factorization p :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvdNG p
  have hSsub_card : Nat.card (S.subgroupOf N) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
  have hdvdSN : Nat.card S ∣ Nat.card N := by
    have h := Subgroup.card_subgroup_dvd_card (S.subgroupOf N)
    rwa [hSsub_card] at h
  have hle_fact2 : (Nat.card G).factorization p ≤ (Nat.card N).factorization p := by
    have h : p ^ (Nat.card G).factorization p ∣ Nat.card N := by rwa [hScard] at hdvdSN
    exact (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out : p.Prime)
      Nat.card_pos.ne').1 h
  have hfactN : (Nat.card N).factorization p = (Nat.card G).factorization p :=
    le_antisymm hle_fact hle_fact2
  have hS'card : Nat.card (S.subgroupOf N) = p ^ (Nat.card N).factorization p := by
    rw [hSsub_card, hScard, ← hfactN]
  let S₀ : Sylow p N := Sylow.ofCard (S.subgroupOf N) hS'card
  have hP' : IsPGroup p (P.subgroupOf N) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm
  obtain ⟨T, hPT⟩ := hP'.exists_le_sylow
  haveI : Finite (Sylow p N) := Sylow.finite_of_finiteIndex S₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N S₀ T
  have hPT' : P.subgroupOf N ≤ ((g • S₀ : Sylow p N) : Subgroup N) := by
    rw [hg]
    exact hPT
  let P'' : Subgroup G := MulAut.conj ((g : G)⁻¹) • P
  have hconjP : MulAut.conj (g⁻¹ : N) • (P.subgroupOf N) = P''.subgroupOf N := by
    rw [Subgroup.conj_smul_subgroupOf hPN (g⁻¹ : N)]
    rfl
  have hgS : MulAut.conj (g⁻¹ : N) • ((g • S₀ : Sylow p N) : Subgroup N) =
      (S₀ : Subgroup N) := by
    rw [Sylow.coe_subgroup_smul, smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hconj_le : MulAut.conj (g⁻¹ : N) • (P.subgroupOf N) ≤ (S₀ : Subgroup N) := by
    calc MulAut.conj (g⁻¹ : N) • (P.subgroupOf N)
        = (P.subgroupOf N).map (MulAut.conj (g⁻¹ : N)).toMonoidHom := rfl
      _ ≤ ((g • S₀ : Sylow p N) : Subgroup N).map
            (MulAut.conj (g⁻¹ : N)).toMonoidHom := Subgroup.map_mono hPT'
      _ = MulAut.conj (g⁻¹ : N) • ((g • S₀ : Sylow p N) : Subgroup N) := rfl
      _ = (S₀ : Subgroup N) := hgS
  have hP''sub_le : P''.subgroupOf N ≤ S.subgroupOf N := by
    rw [← hconjP]
    exact hconj_le
  have hP''N : P'' ≤ N := by
    intro t ht
    rw [show P'' = MulAut.conj ((g : G)⁻¹) • P from rfl] at ht
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp ht
    rw [MulAut.smul_def, MulAut.conj_apply, inv_inv]
    exact N.mul_mem (N.mul_mem (N.inv_mem g.2) (hPN hy)) g.2
  have hP''leS : P'' ≤ S := by
    have hmap := Subgroup.map_mono (f := N.subtype) hP''sub_le
    rwa [Subgroup.map_subgroupOf_eq_of_le hP''N,
      Subgroup.map_subgroupOf_eq_of_le hSN] at hmap
  have hP''leC : P'' ≤ Subgroup.centralizer (Q : Set G) := by
    intro t ht
    rw [show P'' = MulAut.conj ((g : G)⁻¹) • P from rfl] at ht
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp ht
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [MulAut.smul_def, MulAut.conj_apply, inv_inv]
    have hga : (g : G) * a * (g : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.1 g.2 a).1 ha
    have hyC : y * ((g : G) * a * (g : G)⁻¹) = ((g : G) * a * (g : G)⁻¹) * y :=
      ((Subgroup.mem_centralizer_iff.1 (hPC hy)) ((g : G) * a * (g : G)⁻¹) hga).symm
    change a * ((g : G)⁻¹ * y * (g : G)) = ((g : G)⁻¹ * y * (g : G)) * a
    calc a * ((g : G)⁻¹ * y * (g : G))
        = (g : G)⁻¹ * ((g : G) * a * (g : G)⁻¹) * y * (g : G) := by group
      _ = (g : G)⁻¹ * (((g : G) * a * (g : G)⁻¹) * y) * (g : G) := by group
      _ = (g : G)⁻¹ * (y * ((g : G) * a * (g : G)⁻¹)) * (g : G) := by rw [← hyC]
      _ = ((g : G)⁻¹ * y * (g : G)) * a := by group
  have hcardP'' : Nat.card P'' = Nat.card P :=
    (Nat.card_congr (Subgroup.equivSMul (MulAut.conj ((g : G)⁻¹)) P).toEquiv).symm
  calc Nat.card P = Nat.card P'' := hcardP''.symm
    _ ≤ Nat.card ↥(S ⊓ Subgroup.centralizer (Q : Set G)) :=
        Subgroup.card_le_of_le (le_inf hP''leS hP''leC)
    _ ≤ p := hSC

theorem commData_sup_zpowers_inf_centralizer {G : Type} [Group G] [Finite G] {p n : ℕ}
    [Fact p.Prime] {q : Fin n → G} {z : G} {M : Matrix (Fin n) (Fin n) (ZMod p)}
    (hD : CommData p q z M) {x : G} (hxp : x ^ p = 1)
    (hx : ∀ i, x⁻¹ * q i * x ∈ Subgroup.closure (Set.range q))
    (hxM : CommData.actMat p q z M x ≠ 1) :
    (Subgroup.closure (Set.range q) ⊔ Subgroup.zpowers x) ⊓
        Subgroup.centralizer (Subgroup.closure (Set.range q) : Set G) = Subgroup.zpowers z := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  set Q : Subgroup G := Subgroup.closure (Set.range q) with hQ
  have hxQ : ∀ g ∈ Q, x⁻¹ * g * x ∈ Q := fun g hg => CommData.conj_mem hx hg
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.zpowers_le.2 (mem_normalizer_of_conj hxQ)
  apply le_antisymm
  · rintro s ⟨hsQx, hsC⟩
    have hsup : ((Q ⊔ Subgroup.zpowers x : Subgroup G) : Set G) =
        (Subgroup.zpowers x : Set G) * (Q : Set G) := by
      rw [sup_comm]
      exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ hxN
    have hmem : s ∈ (Subgroup.zpowers x : Set G) * (Q : Set G) := by
      rw [← hsup]
      exact hsQx
    obtain ⟨w, hw, y, hy, hwy⟩ := Set.mem_mul.1 hmem
    have hxfin : IsOfFinOrder x :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨p, (Fact.out : p.Prime).pos, hxp⟩
    change w ∈ Subgroup.zpowers x at hw
    rw [hxfin.mem_zpowers_iff_mem_range_orderOf] at hw
    obtain ⟨k, hklt, hkw⟩ := Finset.mem_image.1 hw
    rw [Finset.mem_range] at hklt
    have hsi : ∀ i, s⁻¹ * q i * s = q i := by
      intro i
      have hc := (Subgroup.mem_centralizer_iff.1 hsC) (q i) (Subgroup.subset_closure ⟨i, rfl⟩)
      calc s⁻¹ * q i * s = s⁻¹ * (q i * s) := by group
        _ = s⁻¹ * (s * q i) := by rw [hc]
        _ = q i := by group
    have hs_act : CommData.actMat p q z M s = 1 := by
      have hfun : (fun i => coord p q z M (s⁻¹ * q i * s)) =
          fun i => Pi.single i 1 := by
        funext i
        rw [hsi i, hD.coord_q]
      unfold CommData.actMat
      rw [hfun]
      ext i j
      by_cases h : i = j
      · subst h; simp [Matrix.one_apply]
      · simp [Matrix.one_apply, Pi.single_eq_of_ne, h, Ne.symm h]
    have hxk_conj : ∀ i, (x ^ k)⁻¹ * q i * x ^ k ∈ Q :=
      fun i => conj_pow_mem hxQ k (Subgroup.subset_closure ⟨i, rfl⟩)
    have hy_conj : ∀ i, y⁻¹ * q i * y ∈ Q := by
      intro i
      exact Q.mul_mem (Q.mul_mem (Q.inv_mem hy) (Subgroup.subset_closure ⟨i, rfl⟩)) hy
    have hactk : CommData.actMat p q z M x ^ k = 1 := by
      have h1 : CommData.actMat p q z M (x ^ k * y) = 1 := by
        have hxy : x ^ k * y = s := by rw [hkw, hwy]
        rw [hxy]
        exact hs_act
      rw [hD.actMat_mul hxk_conj hy_conj, commData_actMat_pow hD hx k, hD.actMat_of_mem hy,
        mul_one] at h1
      exact h1
    by_cases hk0 : k = 0
    · have hw1 : w = 1 := by rw [← hkw, hk0, pow_zero]
      have hsQ : s ∈ Q := by
        rw [← hwy, hw1, one_mul]
        exact hy
      rw [← commData_inf_centralizer hD]
      exact ⟨hsQ, hsC⟩
    · exfalso
      have hxne : x ≠ 1 := by
        intro hx1
        exact hxM (by rw [hx1, hD.actMat_one])
      have hxord : orderOf x = p := by
        have hdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hxp
        rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (orderOf x) hdvd with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) hxne
        · exact h1
      have hkltp : k < p := by rw [← hxord]; exact hklt
      have hactp : CommData.actMat p q z M x ^ p = 1 := by
        have h := commData_actMat_pow hD hx p
        rw [hxp, hD.actMat_one] at h
        exact h.symm
      have hd1 : orderOf (CommData.actMat p q z M x) ∣ k :=
        orderOf_dvd_iff_pow_eq_one.mpr hactk
      have hd2 : orderOf (CommData.actMat p q z M x) ∣ p :=
        orderOf_dvd_iff_pow_eq_one.mpr hactp
      have hd : orderOf (CommData.actMat p q z M x) = 1 := by
        rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hd2 with h1 | h1
        · exact h1
        · exact absurd (h1 ▸ hd1) (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hkltp)
      exact hxM (orderOf_eq_one_iff.mp hd)
  · rw [Subgroup.zpowers_le]
    refine ⟨(le_sup_left : Q ≤ Q ⊔ Subgroup.zpowers x) hD.mem_z, ?_⟩
    change z ∈ Subgroup.centralizer (Q : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hD.commute_of_mem hh (Subgroup.mem_zpowers z)

end CFSG.StandardType.SporadicShape

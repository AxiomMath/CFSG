module

public import CFSG.RankThree.PartTwo.Sec21.FF84S32Base
public import CFSG.GH74.GLS.Balance.Bender.AuxSylow
public import CFSG.Quasithin.Background.F6SolvableQuotient

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.GH74.GLS.Balance (IsSylowIn)

section Helpers
variable {G : Type} [Group G] [Finite G]

theorem mem_Cen_iff {g x : G} : g ∈ Cen x ↔ g * x * g⁻¹ = x := by
  rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]

theorem O3_le (H : Subgroup G) : O3 H ≤ H :=
  (Subgroup.closure_le H).2 (fun x hx => hx.1)

theorem mem_Nor_O3 {H : Subgroup G} {h : G} (hh : h ∈ H) : h ∈ Nor (O3 H) := by
  have key : ∀ (h : G), h ∈ H → ∀ g ∈ O3 H, h * g * h⁻¹ ∈ O3 H := by
    intro h hh g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      apply Subgroup.subset_closure
      have hord : orderOf (h * x * h⁻¹) = orderOf x :=
        orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective x
      exact ⟨H.mul_mem (H.mul_mem hh hx.1) (H.inv_mem hh), by rw [hord]; exact hx.2⟩
    | one => simp
    | mul x y _ _ hx hy =>
      rw [show h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) by group]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [show h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ by group]
      exact inv_mem hx
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact key h hh g
  · intro hg
    have := key h⁻¹ (H.inv_mem hh) _ hg
    simpa [mul_assoc] using this

theorem O3_normal_sub (H : Subgroup G) : ((O3 H).subgroupOf H).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.1 (mem_Nor_O3 g.2) n).1 hn
    simpa using this⟩

theorem isSylowOf_iff_abg {p : ℕ} [Fact p.Prime] {P K : Subgroup G} :
    IsSylowOf p P K ↔ CFSG.ABGLocalTools.IsSylowOf p P K := by
  rw [isSylowOf_iff_isSylowIn, CFSG.GH74.GLS.Balance.BenderExt.isSylowIn_iff_isSylowOf]

theorem isSylowOf_inf_of_normal {P K N : Subgroup G} (hP : IsSylowOf 3 P K) (hNK : N ≤ K)
    (hn : K ≤ Nor N) : IsSylowOf 3 (P ⊓ N) N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [isSylowOf_iff_abg] at hP ⊢
  exact hP.inf_of_le_normalizer hNK hn

theorem inv_eq_sq {x : G} (hx : x ^ 3 = 1) : x⁻¹ = x ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hx)

end Helpers

section Main
variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ : G}

theorem c_mem_B (h : FF84Sec3 b L B b₁ b₂) : b₁ * b₂ ∈ B := mul_mem (mem_B_b₁ h) (mem_B_b₂ h)

theorem d_mem_B (h : FF84Sec3 b L B b₁ b₂) : b₁ * b₂ ^ 2 ∈ B :=
  mul_mem (mem_B_b₁ h) (Subgroup.pow_mem _ (mem_B_b₂ h) _)

theorem d_pow3 (h : FF84Sec3 b L B b₁ b₂) : (b₁ * b₂ ^ 2) ^ 3 = 1 := pow3_of_mem_B h (d_mem_B h)

theorem c_ne_one (h : FF84Sec3 b L B b₁ b₂) : b₁ * b₂ ≠ 1 := b₁b₂_ne_one h

theorem d_ne_one (h : FF84Sec3 b L B b₁ b₂) : b₁ * b₂ ^ 2 ≠ 1 := by
  intro hd
  have := P_basis h 0 1 2 (by simpa using hd)
  omega

theorem B_le_Cen_c (h : FF84Sec3 b L B b₁ b₂) : B ≤ Cen (b₁ * b₂) := by
  intro x hx
  rw [mem_Cen_iff]
  have := (comm_of_mem_B h hx (c_mem_B h)).eq
  rw [mul_inv_eq_iff_eq_mul]
  exact this

theorem B_isPGroup (h : FF84Sec3 b L B b₁ b₂) : IsPGroup 3 B :=
  IsPGroup.of_card (n := 3) (by rw [P_cardB h]; norm_num)

theorem S2_B_sylow (h : FF84Sec3 b L B b₁ b₂) : IsSylowOf 3 B (Cen (b₁ * b₂)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT, hBT⟩ := exists_isSylowOf_ge' (B_le_Cen_c h) (B_isPGroup h)
  have hTeq : T = B := by
    by_contra hne
    have hlt : B < T := lt_of_le_of_ne hBT (Ne.symm hne)
    obtain ⟨q, hqT, hqN, hqB⟩ := CFSG.GH74.GLS.Balance.exists_mem_normalizer_not_mem
      (p := 3) hT.2.1 hBT (fun hTB => hne (le_antisymm hTB hBT))
    have hqc : q * (b₁ * b₂) * q⁻¹ = b₁ * b₂ := mem_Cen_iff.1 (hT.1 hqT)
    obtain ⟨k, hk⟩ := hT.2.1 ⟨q, hqT⟩
    have hk' : q ^ 3 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hqCB : q ∈ CenS B := three_elt_cenS_B h hqN hqc hk'
    have hqb : q ∈ Cen b := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hqCB b (mem_B_b h)).symm
    have hzp : IsPGroup 3 (Subgroup.zpowers q) := by
      have : Subgroup.zpowers q ≤ T := Subgroup.zpowers_le.2 hqT
      exact hT.2.1.to_le this
    have hle := CFSG.GH74.GLS.Balance.BenderExt.le_of_isSylowIn_of_le_centralizer
      (N := Cen b) (isSylowOf_iff_isSylowIn.1 h.sylB)
      (Subgroup.zpowers_le.2 hqb) hzp (Subgroup.zpowers_le.2 hqCB)
    exact hqB (hle (Subgroup.mem_zpowers q))
  rw [← hTeq]
  exact hT

theorem mem_O3_of_inv (h : FF84Sec3 b L B b₁ b₂) {x n : G} (hxB : x ∈ B) (hn : n ∈ Nor B)
    (hnc : n ∈ Cen (b₁ * b₂)) (hnx : n * x * n⁻¹ = x⁻¹) : x ∈ O3 (Cen (b₁ * b₂)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, b', hab, -, ⟨e, hae⟩, hb'cop, han, hb'n⟩ :=
    CFSG.Quasithin.F6.exists_mul_eq_pPart Nat.prime_three n
  have hac : a ∈ Cen (b₁ * b₂) := (Subgroup.zpowers_le.2 hnc) han
  have haN : a ∈ Nor B := (Subgroup.zpowers_le.2 hn) han
  have hb'c : b' ∈ Cen (b₁ * b₂) := (Subgroup.zpowers_le.2 hnc) hb'n
  have haCB : a ∈ CenS B := three_elt_cenS_B h haN (mem_Cen_iff.1 hac) hae
  have hxa : x * a = a * x := Subgroup.mem_centralizer_iff.1 haCB x hxB
  have hb'x : b' * x * b'⁻¹ = x⁻¹ := by
    have e1 : b' = a⁻¹ * n := eq_inv_mul_of_mul_eq hab
    have hxa' : x⁻¹ * a = a * x⁻¹ := (Commute.inv_left (show Commute x a from hxa)).eq
    rw [e1, show a⁻¹ * n * x * (a⁻¹ * n)⁻¹ = a⁻¹ * (n * x * n⁻¹) * a by group, hnx]
    calc a⁻¹ * x⁻¹ * a = a⁻¹ * (x⁻¹ * a) := by group
      _ = x⁻¹ := by rw [hxa']; group
  have hx3 : x ^ 3 = 1 := pow3_of_mem_B h hxB
  have hxx : x = b' * (x * b'⁻¹ * x⁻¹) := by
    calc x = x⁻¹ * x⁻¹ := by
          rw [inv_eq_sq hx3]
          calc x = x ^ 3 * x := by rw [hx3, one_mul]
            _ = x ^ 2 * x ^ 2 := by group
      _ = (b' * x * b'⁻¹) * x⁻¹ := by rw [hb'x]
      _ = b' * (x * b'⁻¹ * x⁻¹) := by group
  have hb'ord : ¬ 3 ∣ orderOf b' :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hb'cop.symm
  have hxc : x ∈ Cen (b₁ * b₂) := B_le_Cen_c h hxB
  rw [hxx]
  refine mul_mem (Subgroup.subset_closure ⟨hb'c, hb'ord⟩) (Subgroup.subset_closure ⟨?_, ?_⟩)
  · exact mul_mem (mul_mem hxc (inv_mem hb'c)) (inv_mem hxc)
  · have hord : orderOf (x * b'⁻¹ * x⁻¹) = orderOf b'⁻¹ :=
      orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective b'⁻¹
    rw [hord, orderOf_inv]
    exact hb'ord

theorem S2_mem_H (h : FF84Sec3 b L B b₁ b₂) :
    b ∈ O3 (Cen (b₁ * b₂)) ∧ b₁ * b₂ ^ 2 ∈ O3 (Cen (b₁ * b₂)) := by
  have hcc : ∀ n : G, n * b₁ * n⁻¹ = b₁ ∧ n * b₂ * n⁻¹ = b₂ ∨
      n * b₁ * n⁻¹ = b₂ ∧ n * b₂ * n⁻¹ = b₁ → n ∈ Cen (b₁ * b₂) := by
    intro n hn
    rw [mem_Cen_iff, show n * (b₁ * b₂) * n⁻¹ = (n * b₁ * n⁻¹) * (n * b₂ * n⁻¹) by group]
    rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]
      exact (comm_of_mem_B h (mem_B_b₂ h) (mem_B_b₁ h)).eq
  constructor
  · obtain ⟨n, hn, hnb, hn1, hn2⟩ := h.mono.2.2.2.1
    exact mem_O3_of_inv h (mem_B_b h) hn (hcc n (Or.inl ⟨hn1, hn2⟩)) hnb
  · obtain ⟨n, hn, hn'⟩ := P_monomial h (Equiv.swap 1 2) 1
    have e1 : n * b₁ * n⁻¹ = b₂ := by simpa using hn' 1
    have e2 : n * b₂ * n⁻¹ = b₁ := by simpa using hn' 2
    refine mem_O3_of_inv h (d_mem_B h) hn (hcc n (Or.inr ⟨e1, e2⟩)) ?_
    have hb₂3 := pow3_of_mem_B h (mem_B_b₂ h)
    have hb₁3 := pow3_of_mem_B h (mem_B_b₁ h)
    have e3 : n * b₂ ^ 2 * n⁻¹ = b₁ ^ 2 := by rw [← conj_pow, e2]
    rw [show n * (b₁ * b₂ ^ 2) * n⁻¹ = (n * b₁ * n⁻¹) * (n * b₂ ^ 2 * n⁻¹) by group, e1, e3,
      mul_inv_rev, inv_eq_sq hb₁3]
    congr 1
    exact (inv_eq_of_mul_eq_one_right (by
      calc b₂ ^ 2 * b₂ = b₂ ^ 3 := by group
        _ = 1 := hb₂3)).symm

theorem zpow_d (h : FF84Sec3 b L B b₁ b₂) (i : ℤ) :
    (b₁ * b₂ ^ 2) ^ i = b ^ (0 : ℤ) * b₁ ^ i * b₂ ^ (2 * i) := by
  have hc : Commute b₁ (b₂ ^ 2) :=
    (comm_of_mem_B h (mem_B_b₁ h) (mem_B_b₂ h)).pow_right 2
  rw [hc.mul_zpow]
  simp only [zpow_zero, one_mul]
  congr 1
  rw [← zpow_natCast, ← zpow_mul]
  norm_num

theorem exists_coord_P (h : FF84Sec3 b L B b₁ b₂) {x : G}
    (hx : x ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2)) :
    ∃ i j : ℤ, x = b ^ i * b₁ ^ j * b₂ ^ (2 * j) := by
  obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup
    (comm_of_mem_B h (mem_B_b h) (d_mem_B h)) hx
  refine ⟨i, j, ?_⟩
  rw [zpow_d h, show b ^ i * (b ^ (0 : ℤ) * b₁ ^ j * b₂ ^ (2 * j)) =
    (b ^ i * b₁ ^ (0 : ℤ) * b₂ ^ (0 : ℤ)) * (b ^ (0 : ℤ) * b₁ ^ j * b₂ ^ (2 * j)) by simp, cmul h]
  simp

theorem P_le_B (h : FF84Sec3 b L B b₁ b₂) :
    Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2) ≤ B :=
  sup_le (Subgroup.zpowers_le.2 (mem_B_b h)) (Subgroup.zpowers_le.2 (d_mem_B h))

theorem d_notin_zpowers_b (h : FF84Sec3 b L B b₁ b₂) : b₁ * b₂ ^ 2 ∉ Subgroup.zpowers b := by
  rintro hd
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hd
  have := (ceq h (a := j) (c := 0) (d := 0) (a' := 0) (c' := 1) (d' := 2)).1 (by
    rw [show b ^ j * b₁ ^ (0 : ℤ) * b₂ ^ (0 : ℤ) = b ^ j by simp, hj]; simp)
  omega

theorem card_P_ge (h : FF84Sec3 b L B b₁ b₂) :
    9 ≤ Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2) : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb3 := pow3_of_mem_B h (mem_B_b h)
  have hbne : b ≠ 1 := b_ne_one' h
  have hpg : IsPGroup 3 ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2) : Subgroup G) :=
    (B_isPGroup h).to_le (P_le_B h)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hpg
  have hle : Nat.card ↥(Subgroup.zpowers b) ≤
      Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2) : Subgroup G) :=
    Subgroup.card_le_of_le le_sup_left
  rw [Nat.card_zpowers, orderOf_eq_prime hb3 hbne] at hle
  have hne : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2) : Subgroup G) ≠ 3 := by
    intro hc
    have heq : Subgroup.zpowers b =
        Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2) :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by
        rw [hc, Nat.card_zpowers, orderOf_eq_prime hb3 hbne])
    apply d_notin_zpowers_b h
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · interval_cases n
    · rw [pow_zero] at hn; omega
    · rw [pow_one] at hn; exact absurd hn hne
  · rw [hn]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hge

theorem P_eq_inf (h : FF84Sec3 b L B b₁ b₂) (hc : b₁ * b₂ ∉ O3 (Cen (b₁ * b₂))) :
    Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2) = B ⊓ O3 (Cen (b₁ * b₂)) := by
  obtain ⟨hbH, hdH⟩ := S2_mem_H h
  have hPle : Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2) ≤ B ⊓ O3 (Cen (b₁ * b₂)) :=
    le_inf (P_le_B h) (sup_le (Subgroup.zpowers_le.2 hbH) (Subgroup.zpowers_le.2 hdH))
  apply Subgroup.eq_of_le_of_card_ge hPle
  have h27 : Nat.card ↥(B ⊓ O3 (Cen (b₁ * b₂))) ∣ 27 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : B ⊓ O3 (Cen (b₁ * b₂)) ≤ B)
    rwa [P_cardB h] at this
  have hne : Nat.card ↥(B ⊓ O3 (Cen (b₁ * b₂))) ≠ 27 := by
    intro h27'
    have heq : B ⊓ O3 (Cen (b₁ * b₂)) = B :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27', P_cardB h])
    have hcB : b₁ * b₂ ∈ B ⊓ O3 (Cen (b₁ * b₂)) := by rw [heq]; exact c_mem_B h
    exact hc hcB.2
  have h27' : Nat.card ↥(B ⊓ O3 (Cen (b₁ * b₂))) ∣ 3 ^ 3 := by norm_num; exact h27
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h27'
  have := card_P_ge h
  rw [hk']
  interval_cases k <;> norm_num <;>
    first | omega | (exfalso; apply hne; rw [hk']; norm_num)

end Main

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end

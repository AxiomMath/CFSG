module

public import CFSG.RankThree.GF2n.Tim77.Sec3Basic
import CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
import CFSG.CGT.Timmesfeld75.Sec3Thirteen
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec78NormZ0
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly69
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssemblyFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarFrattini
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmts
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Defs

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.RootInvolutions CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem sec411_inv_eq_self {x : G} (h : x ^ 2 = 1) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h)

theorem sec411_conj_le {S T : Subgroup G} {g : G} (hg : g ∈ S) (hT : T ≤ S) :
    conjSubgroup g T ≤ S := by
  intro x hx
  rw [mem_conjSubgroup] at hx
  have hx' : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [hx']
  exact S.mul_mem (S.mul_mem hg (hT hx)) (S.inv_mem hg)

theorem sec411_orderOf_pow_two {S : Subgroup G} (hS : IsPGroup 2 ↥S) {r : G} (hr : r ∈ S) :
    ∃ n : ℕ, orderOf r = 2 ^ n := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hS) ⟨r, hr⟩
  exact ⟨n, by rw [← Subgroup.orderOf_mk r hr]; exact hn⟩

theorem sec411_comm_of_exists [Finite G] {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hTI : IsTI A) {g₁ g₂ : G}
    (hP : IsPGroup 2 ↥(conjSubgroup g₁ A ⊔ conjSubgroup g₂ A))
    {x y : G} (hx : x ∈ conjSubgroup g₁ A) (hx1 : x ≠ 1) (hy : y ∈ conjSubgroup g₂ A)
    (hy1 : y ≠ 1) (hxy : x * y = y * x) :
    ∀ a ∈ conjSubgroup g₁ A, ∀ b ∈ conjSubgroup g₂ A, a * b = b * a := by
  have hTIc : IsTI (conjSubgroup g₂ A) := isTI_conjSubgroup hTI g₂
  have hxN : x ∈ normalizer (conjSubgroup g₂ A : Set G) :=
    mem_normalizer_of_commute_of_isTI hTIc hy hy1 hxy
  have hN : normalizerIn (conjSubgroup g₁ A) (conjSubgroup g₂ A) ≠ ⊥ := by
    intro hbot
    have hmem : x ∈ normalizerIn (conjSubgroup g₁ A) (conjSubgroup g₂ A) := by
      unfold normalizerIn
      exact Subgroup.mem_inf.mpr ⟨hx, hxN⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  exact commute_of_isPGroup hA hTI hP hN

theorem sec411_orderOf_four [Finite G] {A S₀ : Subgroup G}
    (hA : IsElemAbelian 2 A) (hTI : IsTI A) (hS₀ : IsPGroup 2 ↥S₀)
    {g₂ v : G} (hC : conjSubgroup g₂ A ≤ S₀) (hvS : v ∈ S₀) (hv2 : v ^ 2 = 1)
    (hNC : ∀ u ∈ conjSubgroup g₂ A, u ≠ 1 → v * u ≠ u * v)
    {w : G} (hw : w ∈ conjSubgroup g₂ A) (hw1 : w ≠ 1) (h4 : (v * w) ^ 4 = 1) :
    ∀ u ∈ conjSubgroup g₂ A, u ≠ 1 → orderOf (v * u) = 4 := by
  have hvi : v⁻¹ = v := sec411_inv_eq_self hv2
  have hCel : IsElemAbelian 2 (conjSubgroup g₂ A) := isElemAbelian_conj hA g₂
  have hCTI : IsTI (conjSubgroup g₂ A) := isTI_conjSubgroup hTI g₂
  have hw2 : w ^ 2 = 1 := hCel.2 w hw
  have hZ : conjSubgroup v (conjSubgroup g₂ A) = conjSubgroup (v * g₂) A :=
    (conjSubgroup_mul v g₂ A).symm
  have hZTI : IsTI (conjSubgroup v (conjSubgroup g₂ A)) := isTI_conjSubgroup hCTI v
  have hZle : conjSubgroup (v * g₂) A ≤ S₀ := by
    rw [← hZ]
    exact sec411_conj_le hvS hC
  have hP : IsPGroup 2 ↥(conjSubgroup g₂ A ⊔ conjSubgroup (v * g₂) A) :=
    IsPGroup.to_le hS₀ (sup_le hC hZle)
  have hz_mem : v * w * v⁻¹ ∈ conjSubgroup v (conjSubgroup g₂ A) := by
    rw [mem_conjSubgroup, show v⁻¹ * (v * w * v⁻¹) * v = w by group]
    exact hw
  have hz1 : v * w * v⁻¹ ≠ 1 := by
    intro h
    apply hw1
    calc w = v⁻¹ * (v * w * v⁻¹) * v := by group
      _ = 1 := by rw [h]; group
  have hq : (v * w) ^ 2 * (v * w) ^ 2 = 1 := by
    rw [← pow_add]
    exact h4
  have hinv2 : ((v * w) ^ 2)⁻¹ = (v * w) ^ 2 := inv_eq_of_mul_eq_one_right hq
  have hwv : w * v = (v * w)⁻¹ := by
    rw [mul_inv_rev, sec411_inv_eq_self hw2, hvi]
  have hsq : (w * v) ^ 2 = (v * w) ^ 2 := by
    rw [hwv, inv_pow, hinv2]
  have hcomm_wz : w * (v * w * v⁻¹) = (v * w * v⁻¹) * w := by
    rw [hvi]
    calc w * (v * w * v) = (w * v) ^ 2 := by simp only [pow_two, mul_assoc]
      _ = (v * w) ^ 2 := hsq
      _ = v * w * v * w := by simp only [pow_two, mul_assoc]
  have hN : normalizerIn (conjSubgroup g₂ A) (conjSubgroup (v * g₂) A) ≠ ⊥ := by
    intro hbot
    have hwN : w ∈ normalizerIn (conjSubgroup g₂ A) (conjSubgroup (v * g₂) A) := by
      unfold normalizerIn
      refine Subgroup.mem_inf.mpr ⟨hw, ?_⟩
      rw [← hZ]
      exact mem_normalizer_of_commute_of_isTI hZTI hz_mem hz1 hcomm_wz
    rw [hbot, Subgroup.mem_bot] at hwN
    exact hw1 hwN
  have hkey := commute_of_isPGroup hA hTI hP hN
  intro u hu hu1
  have hu2 : u ^ 2 = 1 := hCel.2 u hu
  have hui : u⁻¹ = u := sec411_inv_eq_self hu2
  have hz'mem : v * u * v⁻¹ ∈ conjSubgroup (v * g₂) A := by
    rw [← hZ, mem_conjSubgroup, show v⁻¹ * (v * u * v⁻¹) * v = u by group]
    exact hu
  have hcomm_u : u * (v * u * v⁻¹) = (v * u * v⁻¹) * u := hkey u hu _ hz'mem
  have hsq_u : (v * u) ^ 2 = (v * u * v⁻¹) * u := by
    rw [hvi]
    simp only [pow_two, mul_assoc]
  have hv4 : (v * u) ^ 4 = 1 := by
    have hcz : Commute (v * u * v⁻¹) u := hcomm_u.symm
    have hz2 : (v * u * v⁻¹) ^ 2 = 1 := by
      rw [conj_pow, hu2]
      group
    calc (v * u) ^ 4 = (v * u) ^ (2 * 2) := rfl
      _ = ((v * u) ^ 2) ^ 2 := pow_mul _ _ _
      _ = ((v * u * v⁻¹) * u) ^ 2 := by rw [hsq_u]
      _ = (v * u * v⁻¹) ^ 2 * u ^ 2 := hcz.mul_pow 2
      _ = 1 := by rw [hz2, hu2, one_mul]
  have hnot2 : ¬ (v * u) ^ 2 = 1 := by
    intro h
    apply hNC u hu hu1
    have h1 : (v * u)⁻¹ = v * u := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h)
    have h2 : (v * u)⁻¹ = u * v := by
      rw [mul_inv_rev, hui, hvi]
    exact h1.symm.trans h2
  have h2' : ¬ (v * u) ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact hnot2
  have h4' : (v * u) ^ 2 ^ (1 + 1) = 1 := by
    norm_num
    exact hv4
  exact (orderOf_eq_prime_pow h2' h4').trans (by norm_num)

theorem sec411_false_of_four [Finite G] {A S₀ : Subgroup G}
    (hA : IsElemAbelian 2 A) (hTI : IsTI A) (hS₀ : IsPGroup 2 ↥S₀)
    (h48 : ∀ B' C' : Subgroup G, (∃ g : G, B' = conjSubgroup g A) →
      (∃ g : G, C' = conjSubgroup g A) →
      (∀ b ∈ B', b ≠ 1 → ∀ c ∈ C', c ≠ 1 → orderOf (b * c) = 2 ∨ orderOf (b * c) = 4) →
      ∀ b ∈ B', ∀ c ∈ C', b * c = c * b)
    {g₁ g₂ : G} (hB : conjSubgroup g₁ A ≤ S₀) (hC : conjSubgroup g₂ A ≤ S₀)
    (hNC : ∀ x ∈ conjSubgroup g₁ A, x ≠ 1 → ∀ y ∈ conjSubgroup g₂ A, y ≠ 1 → x * y ≠ y * x)
    {x y : G} (hx : x ∈ conjSubgroup g₁ A) (hx1 : x ≠ 1) (hy : y ∈ conjSubgroup g₂ A)
    (hy1 : y ≠ 1) (hxy4 : orderOf (x * y) = 4) : False := by
  have hxS : x ∈ S₀ := hB hx
  have hx2 : x ^ 2 = 1 := (isElemAbelian_conj hA g₁).2 x hx
  have hy2 : y ^ 2 = 1 := (isElemAbelian_conj hA g₂).2 y hy
  have hxy4' : (x * y) ^ 4 = 1 := by
    have h := pow_orderOf_eq_one (x * y)
    rwa [hxy4] at h
  have step1 : ∀ u ∈ conjSubgroup g₂ A, u ≠ 1 → orderOf (x * u) = 4 :=
    sec411_orderOf_four hA hTI hS₀ hC hxS hx2 (fun u hu hu1 => hNC x hx hx1 u hu hu1) hy hy1
      hxy4'
  have step2 : ∀ v ∈ conjSubgroup g₁ A, v ≠ 1 → ∀ u ∈ conjSubgroup g₂ A, u ≠ 1 →
      orderOf (v * u) = 4 := by
    intro v hv hv1 u hu hu1
    have hxu4 : (x * u) ^ 4 = 1 := by
      have h := pow_orderOf_eq_one (x * u)
      rwa [step1 u hu hu1] at h
    have hu2 : u ^ 2 = 1 := (isElemAbelian_conj hA g₂).2 u hu
    have hv2 : v ^ 2 = 1 := (isElemAbelian_conj hA g₁).2 v hv
    have hux4 : (u * x) ^ 4 = 1 := by
      have e : u * x = (x * u)⁻¹ := by
        rw [mul_inv_rev, sec411_inv_eq_self hx2, sec411_inv_eq_self hu2]
      rw [e, inv_pow, hxu4, inv_one]
    have h := sec411_orderOf_four hA hTI hS₀ hB (hC hu) hu2
      (fun v' hv' hv'1 h' => hNC v' hv' hv'1 u hu hu1 h'.symm) hx hx1 hux4 v hv hv1
    have e : v * u = (u * v)⁻¹ := by
      rw [mul_inv_rev, sec411_inv_eq_self hu2, sec411_inv_eq_self hv2]
    rw [e, orderOf_inv]
    exact h
  have hall := h48 (conjSubgroup g₁ A) (conjSubgroup g₂ A) ⟨g₁, rfl⟩ ⟨g₂, rfl⟩
    (fun b hb hb1 c hc hc1 => Or.inr (step2 b hb hb1 c hc hc1))
  exact hNC x hx hx1 y hy hy1 (hall x hx y hy)

theorem sec411_reduce {x y : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) {m : ℕ}
    (hr : orderOf (x * y) = 2 ^ (m + 3)) :
    orderOf (x * ((x * y) ^ 2 ^ m * x * ((x * y) ^ 2 ^ m)⁻¹)) = 4 := by
  have hxi : x⁻¹ = x := sec411_inv_eq_self hx
  have hyi : y⁻¹ = y := sec411_inv_eq_self hy
  have hxrx : x * (x * y) * x = (x * y)⁻¹ := by
    rw [mul_inv_rev, hxi, hyi]
    calc x * (x * y) * x = (x * x) * y * x := by simp only [mul_assoc]
      _ = y * x := by rw [← pow_two, hx, one_mul]
  have hxs : x * (x * y) ^ 2 ^ m * x = ((x * y) ^ 2 ^ m)⁻¹ := by
    have h1 : (x * (x * y) * x⁻¹) ^ 2 ^ m = x * (x * y) ^ 2 ^ m * x⁻¹ := conj_pow
    rw [hxi, hxrx, inv_pow] at h1
    exact h1.symm
  have hss : (x * y) ^ 2 ^ m * (x * y) ^ 2 ^ m = (x * y) ^ 2 ^ (m + 1) := by
    rw [← pow_add, pow_succ, mul_two]
  have hw : x * ((x * y) ^ 2 ^ m * x * ((x * y) ^ 2 ^ m)⁻¹) = ((x * y) ^ 2 ^ (m + 1))⁻¹ := by
    calc x * ((x * y) ^ 2 ^ m * x * ((x * y) ^ 2 ^ m)⁻¹)
        = (x * (x * y) ^ 2 ^ m * x) * ((x * y) ^ 2 ^ m)⁻¹ := by simp only [mul_assoc]
      _ = ((x * y) ^ 2 ^ m)⁻¹ * ((x * y) ^ 2 ^ m)⁻¹ := by rw [hxs]
      _ = ((x * y) ^ 2 ^ m * (x * y) ^ 2 ^ m)⁻¹ := (mul_inv_rev _ _).symm
      _ = ((x * y) ^ 2 ^ (m + 1))⁻¹ := by rw [hss]
  have hr_pow : ∀ k : ℕ, (x * y) ^ k = 1 ↔ 2 ^ (m + 3) ∣ k := fun k => by
    rw [← hr, orderOf_dvd_iff_pow_eq_one]
  have hfin : ((x * y) ^ 2 ^ (m + 1)) ^ 2 ^ (1 + 1) = 1 := by
    rw [← pow_mul, show 2 ^ (m + 1) * 2 ^ (1 + 1) = 2 ^ (m + 3) by ring]
    exact (hr_pow _).mpr dvd_rfl
  have hnot : ¬ ((x * y) ^ 2 ^ (m + 1)) ^ 2 ^ 1 = 1 := by
    intro h
    rw [← pow_mul, show 2 ^ (m + 1) * 2 ^ 1 = 2 ^ (m + 2) by ring, hr_pow] at h
    have hle := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h
    omega
  rw [hw, orderOf_inv]
  exact (orderOf_eq_prime_pow hnot hfin).trans (by norm_num)

theorem sec411_comm [Finite G] {A S₀ : Subgroup G}
    (hA : IsElemAbelian 2 A) (hTI : IsTI A) (hS₀ : IsPGroup 2 ↥S₀)
    (h48 : ∀ B' C' : Subgroup G, (∃ g : G, B' = conjSubgroup g A) →
      (∃ g : G, C' = conjSubgroup g A) →
      (∀ b ∈ B', b ≠ 1 → ∀ c ∈ C', c ≠ 1 → orderOf (b * c) = 2 ∨ orderOf (b * c) = 4) →
      ∀ b ∈ B', ∀ c ∈ C', b * c = c * b) :
    ∀ g₁ g₂ : G, conjSubgroup g₁ A ≤ S₀ → conjSubgroup g₂ A ≤ S₀ →
      ∀ x ∈ conjSubgroup g₁ A, ∀ y ∈ conjSubgroup g₂ A, x * y = y * x := by
  intro g₁ g₂ hB hC x hx y hy
  by_contra hxy
  have hP : IsPGroup 2 ↥(conjSubgroup g₁ A ⊔ conjSubgroup g₂ A) :=
    IsPGroup.to_le hS₀ (sup_le hB hC)
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hxy (by rw [one_mul, mul_one])
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hxy (by rw [one_mul, mul_one])
  have hNC : ∀ a ∈ conjSubgroup g₁ A, a ≠ 1 → ∀ b ∈ conjSubgroup g₂ A, b ≠ 1 →
      a * b ≠ b * a := fun a ha ha1 b hb hb1 hab =>
    hxy (sec411_comm_of_exists hA hTI hP ha ha1 hb hb1 hab x hx y hy)
  have hx2 : x ^ 2 = 1 := (isElemAbelian_conj hA g₁).2 x hx
  have hy2 : y ^ 2 = 1 := (isElemAbelian_conj hA g₂).2 y hy
  have hxi : x⁻¹ = x := sec411_inv_eq_self hx2
  have hyi : y⁻¹ = y := sec411_inv_eq_self hy2
  have hr_mem : x * y ∈ S₀ := S₀.mul_mem (hB hx) (hC hy)
  obtain ⟨n, hn⟩ := sec411_orderOf_pow_two hS₀ hr_mem
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · interval_cases n
    ·
      simp only [pow_zero] at hn
      have h1 : x * y = 1 := orderOf_eq_one_iff.mp hn
      have h2 : (x * y)⁻¹ = y * x := by rw [mul_inv_rev, hxi, hyi]
      rw [h1, inv_one] at h2
      exact hxy (h1.trans h2)
    ·
      simp only [pow_one] at hn
      have h2 : (x * y) ^ 2 = 1 := by
        have h := pow_orderOf_eq_one (x * y)
        rwa [hn] at h
      have h1 : (x * y)⁻¹ = x * y :=
        inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h2)
      have h3 : (x * y)⁻¹ = y * x := by rw [mul_inv_rev, hxi, hyi]
      exact hxy (h1.symm.trans h3)
    ·
      exact sec411_false_of_four hA hTI hS₀ h48 hB hC hNC hx hx1 hy hy1 (hn.trans (by norm_num))
  ·
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    obtain ⟨s, hs⟩ : ∃ s : G, s = (x * y) ^ 2 ^ m := ⟨_, rfl⟩
    obtain ⟨x', hx'⟩ : ∃ x' : G, x' = s * x * s⁻¹ := ⟨_, rfl⟩
    have hs_mem : s ∈ S₀ := by
      rw [hs]
      exact S₀.pow_mem hr_mem _
    have hx'B : x' ∈ conjSubgroup (s * g₁) A := by
      rw [conjSubgroup_mul, mem_conjSubgroup, hx', show s⁻¹ * (s * x * s⁻¹) * s = x by group]
      exact hx
    have hB3 : conjSubgroup (s * g₁) A ≤ S₀ := by
      rw [conjSubgroup_mul]
      exact sec411_conj_le hs_mem hB
    have hx'1 : x' ≠ 1 := by
      intro h1
      apply hx1
      rw [hx'] at h1
      calc x = s⁻¹ * (s * x * s⁻¹) * s := by group
        _ = 1 := by rw [h1]; group
    have hw4 : orderOf (x * x') = 4 := by
      rw [hx', hs]
      exact sec411_reduce hx2 hy2 hn
    have hNC' : ∀ a ∈ conjSubgroup g₁ A, a ≠ 1 → ∀ b ∈ conjSubgroup (s * g₁) A, b ≠ 1 →
        a * b ≠ b * a := by
      intro a ha ha1 b hb hb1 hab
      have hP' : IsPGroup 2 ↥(conjSubgroup g₁ A ⊔ conjSubgroup (s * g₁) A) :=
        IsPGroup.to_le hS₀ (sup_le hB hB3)
      have hcomm := sec411_comm_of_exists hA hTI hP' ha ha1 hb hb1 hab x hx x' hx'B
      have hc : Commute x x' := hcomm
      have hsq : (x * x') ^ 2 = 1 := by
        rw [hc.mul_pow 2, hx2, (isElemAbelian_conj hA (s * g₁)).2 x' hx'B, one_mul]
      have hdvd := orderOf_dvd_of_pow_eq_one hsq
      rw [hw4] at hdvd
      norm_num at hdvd
    exact sec411_false_of_four hA hTI hS₀ h48 hB hB3 hNC' hx hx1 hx'B hx'1 hw4

theorem sec411_of (h48 : Tim77Sec48Statement) : Tim77Sec411Statement := by
  intro G _ _ A Abar S₀ B h hq _
  have hA : IsElemAbelian 2 A := h.hyp.elemAbelian
  have hTI : IsTI A := h.hyp.ti
  have hS₀ : IsPGroup 2 ↥S₀ := Sec3Ctx.isPGroup_s0 h
  have hmain := sec411_comm hA hTI hS₀ (h48 G A Abar S₀ B h hq)
  have hsq : ∀ g : G, ∀ x ∈ (⨆ (_ : conjSubgroup g A ≤ S₀), conjSubgroup g A), x ^ 2 = 1 := by
    intro g x hx
    by_cases hP : conjSubgroup g A ≤ S₀
    · rw [iSup_pos hP] at hx
      exact (isElemAbelian_conj hA g).2 x hx
    · rw [iSup_neg hP, Subgroup.mem_bot] at hx
      rw [hx, one_pow]
  have hcomm : ∀ g₁ g₂ : G, ∀ a ∈ (⨆ (_ : conjSubgroup g₁ A ≤ S₀), conjSubgroup g₁ A),
      ∀ b ∈ (⨆ (_ : conjSubgroup g₂ A ≤ S₀), conjSubgroup g₂ A), a * b = b * a := by
    intro g₁ g₂ a ha b hb
    by_cases hP₁ : conjSubgroup g₁ A ≤ S₀
    · by_cases hP₂ : conjSubgroup g₂ A ≤ S₀
      · rw [iSup_pos hP₁] at ha
        rw [iSup_pos hP₂] at hb
        exact hmain g₁ g₂ hP₁ hP₂ a ha b hb
      · rw [iSup_neg hP₂, Subgroup.mem_bot] at hb
        rw [hb, mul_one, one_mul]
    · rw [iSup_neg hP₁, Subgroup.mem_bot] at ha
      rw [ha, one_mul, mul_one]
  exact isElemAbelian_iSup_of_comm (fun g : G => ⨆ (_ : conjSubgroup g A ≤ S₀), conjSubgroup g A)
    hsq hcomm

end CFSG.RankThree.GF2n.Tim77

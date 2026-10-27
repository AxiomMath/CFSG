module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Datum
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace X1512

variable {G : Type} [Group G] [Finite G]

theorem exists_odd_lift {H : Subgroup G} (y : OTwoQuot H) (hodd : Odd (orderOf y)) :
    ∃ h₀ ∈ H, ∃ j : ℕ, bar H h₀ = y ∧ (h₀ ^ orderOf y) ^ 2 ^ j = 1 ∧
      Odd (orderOf (h₀ ^ 2 ^ j)) := by
  obtain ⟨h₀, hH, rfl⟩ := bar_surjective H y
  have h1 : h₀ ^ orderOf (bar H h₀) ∈ pCoreOf 2 H := by
    rw [← bar_eq_one_iff (H.pow_mem hH _), bar_pow hH]
    exact pow_orderOf_eq_one _
  obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 H) ⟨_, h1⟩
  have hj' : (h₀ ^ orderOf (bar H h₀)) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  refine ⟨h₀, hH, j, rfl, hj', ?_⟩
  have hd : orderOf (h₀ ^ 2 ^ j) ∣ orderOf (bar H h₀) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, mul_comm, pow_mul]
    exact hj'
  exact Odd.of_dvd_nat hodd hd

theorem exists_X {T H P C A : Subgroup G} (hmp : MinParabolic H T P) (hCH : C ≤ H)
    (hCn : H ≤ Subgroup.normalizer (C : Set G)) (hQC : pCoreOf 2 H ≤ C)
    (hK : ¬ oTwoUpper H ≤ C) (hAT : A ≤ T) (hAe : IsElemAbelian 2 A) {x : G} (hxH : x ∈ H)
    (hxP : x ∉ P) (hx3 : x ^ 3 ∈ C)
    (hxA : ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ C ∨ a * x * a⁻¹ * x ∈ C)
    (hxinv : ∃ a ∈ A, a * x * a⁻¹ * x ∈ C) :
    ∃ X : Subgroup G, pCoreOf 2 H ≤ X ∧ X ≤ H ∧ A ≤ X ∧ ¬ A ≤ pCoreOf 2 X ∧ pCoreOf 2 X ≤ T ∧
      (A ⊓ pCoreOf 2 X).relIndex A = 2 ∧
      (∀ N : Subgroup G, N ≤ X → (N.subgroupOf X).Normal → ∀ a ∈ A, a ∈ N →
        a ∉ pCoreOf 2 X → ∀ z ∈ X, ∃ n ∈ N, n⁻¹ * z ∈ pCoreOf 2 X) ∧
      H = oTwoUpper X ⊔ T := by
  obtain ⟨hCP, hCsyl⟩ := le_and_isSylow hmp hCH hCn hQC hK
  have hxC : x ∉ C := fun h => hxP (hCP h)
  have hTH : T ≤ H := hmp.isSylow.1
  have hAH : A ≤ H := hAT.trans hTH
  have hQT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hmp.isSylow
  obtain ⟨y, A₀, a₁, ha₁A, hD, hyC⟩ :=
    exists_dihData hCH hCn hCsyl hAH hAe hxH hxC hx3 hxA hxinv
  have ha₁H : a₁ ∈ H := hAH ha₁A
  set Xh : Subgroup (OTwoQuot H) := imBar H A ⊔ Subgroup.zpowers y with hXh
  have hbarA : ∀ a ∈ A, bar H a ∈ Xh := fun a ha =>
    Subgroup.mem_sup_left (bar_mem_imBar (hAH ha) ha)
  have hyXh : y ∈ Xh := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hmemX : ∀ a ∈ A, a ∈ preimBar H Xh := fun a ha =>
    mem_preimBar.mpr ⟨hAH ha, hbarA a ha⟩
  have hO : ∀ g ∈ preimBar H Xh, g ∈ pCoreOf 2 (preimBar H Xh) ↔ bar H g ∈ pCoreOf 2 Xh :=
    fun g hg => mem_pCoreOf_preimBar_iff hg
  have hmemN : ∀ b ∈ A, b ∈ pCoreOf 2 (preimBar H Xh) ↔ bar H b ∈ A₀ := by
    intro b hb
    rw [hO b (hmemX b hb)]
    exact ⟨fun h => hD.mem_of_mem_pCoreOf (bar_mem_imBar (hAH hb) hb) h,
      fun h => hD.le_pCoreOf h⟩
  have ha1sq : (bar H a₁)⁻¹ = bar H a₁ := by
    have := hD.elem.2 (bar H a₁) (bar_mem_imBar ha₁H ha₁A)
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using this)
  refine ⟨preimBar H Xh, pCoreOf_le_preimBar H Xh, preimBar_le H Xh, hmemX, ?_, ?_, ?_, ?_, ?_⟩
  · intro hle
    exact hD.not_mem ((hmemN a₁ ha₁A).mp (hle ha₁A))
  · intro g hg
    have hgX : g ∈ preimBar H Xh := pCoreOf_le 2 _ hg
    have hgH : g ∈ H := preimBar_le H Xh hgX
    have hb : bar H g ∈ pCoreOf 2 Xh := (hO g hgX).mp hg
    obtain ⟨a, haH, haA, hag⟩ := mem_imBar.mp (hD.pCoreOf_le_left hb)
    have hq : a⁻¹ * g ∈ pCoreOf 2 H := (bar_eq_iff haH hgH).mp hag
    have : g = a * (a⁻¹ * g) := by group
    rw [this]
    exact T.mul_mem (hAT haA) (hQT hq)
  · rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨a₁, ha₁A, fun b hb => ?_⟩
    have hbH : b ∈ H := hAH hb
    have hz : bar H b ∈ imBar H A := bar_mem_imBar hbH hb
    have hba : b * a₁ ∈ A := A.mul_mem hb ha₁A
    have e1 : bar H (b * a₁) = bar H b * bar H a₁ := bar_mul hbH ha₁H
    by_cases h0 : bar H b ∈ A₀
    · refine Or.inr ⟨⟨hb, (hmemN b hb).mpr h0⟩, fun hN => hD.not_mem ?_⟩
      have h2 : bar H b * bar H a₁ ∈ A₀ := by rw [← e1]; exact (hmemN _ hba).mp hN.2
      have := A₀.mul_mem (A₀.inv_mem h0) h2
      simpa using this
    · refine Or.inl ⟨⟨hba, (hmemN _ hba).mpr ?_⟩, fun hN => h0 ((hmemN b hb).mp hN.2)⟩
      rcases hD.cover _ hz with h | h
      · exact absurd h h0
      · rw [e1]
        have hc : bar H b * bar H a₁ = bar H a₁ * bar H b :=
          B2F.isElemAbelian_comm hD.elem hz (bar_mem_imBar ha₁H ha₁A)
        rw [hc, ← ha1sq]
        exact h
  · intro N hNX hNn a haA haN haO z hz
    have hNn' : ∀ h ∈ preimBar H Xh, ∀ n ∈ N, h * n * h⁻¹ ∈ N := fun h hh n hn =>
      Subgroup.mem_subgroupOf.mp
        (hNn.conj_mem ⟨n, hNX hn⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨h, hh⟩)
    have haH : a ∈ H := hAH haA
    have ha' : bar H a ∈ imBar H A := bar_mem_imBar haH haA
    have haN' : bar H a ∈ imBar H N := bar_mem_imBar haH haN
    have haO' : bar H a ∉ pCoreOf 2 Xh := fun h => haO ((hO a (hmemX a haA)).mpr h)
    have hyN : y * bar H a * y⁻¹ ∈ imBar H N := by
      obtain ⟨h₀, hh₀H, hh₀⟩ := bar_surjective H y
      have hh₀X : h₀ ∈ preimBar H Xh := mem_preimBar.mpr ⟨hh₀H, by rw [hh₀]; exact hyXh⟩
      refine mem_imBar.mpr ⟨h₀ * a * h₀⁻¹, H.mul_mem (H.mul_mem hh₀H haH) (H.inv_mem hh₀H),
        hNn' h₀ hh₀X a haN, ?_⟩
      rw [bar_mul (H.mul_mem hh₀H haH) (H.inv_mem hh₀H), bar_mul hh₀H haH, bar_inv hh₀H, hh₀]
    have hzH : z ∈ H := preimBar_le H Xh hz
    obtain ⟨nh, hnhN, hnh⟩ := hD.exists_mul_mem_pCoreOf ha' haN' haO' hyN (bar H z)
      (mem_preimBar.mp hz).2
    obtain ⟨n, hnH, hnN, rfl⟩ := mem_imBar.mp hnhN
    refine ⟨n, hnN, ?_⟩
    have hnX : n ∈ preimBar H Xh := hNX hnN
    have hn'X : n⁻¹ * z ∈ preimBar H Xh :=
      (preimBar H Xh).mul_mem ((preimBar H Xh).inv_mem hnX) hz
    rw [hO _ hn'X, bar_mul (H.inv_mem hnH) hzH, bar_inv hnH]
    exact hnh
  · obtain ⟨h₀, hh₀H, j, hh₀y, hj, hoddy⟩ := exists_odd_lift y hD.odd
    have hytH : h₀ ^ 2 ^ j ∈ H := H.pow_mem hh₀H _
    have hytX : h₀ ^ 2 ^ j ∈ preimBar H Xh := by
      refine mem_preimBar.mpr ⟨hytH, ?_⟩
      rw [bar_pow hh₀H, hh₀y]
      exact Xh.pow_mem hyXh _
    have hytO : h₀ ^ 2 ^ j ∈ oTwoUpper (preimBar H Xh) := mem_oTwoUpper_of_odd hytX hoddy
    have hTY' : T ≤ oTwoUpper (preimBar H Xh) ⊔ T := le_sup_right
    have hY'H : oTwoUpper (preimBar H Xh) ⊔ T ≤ H :=
      sup_le ((oTwoUpper_le _).trans (preimBar_le H Xh)) hTH
    by_contra hne
    have hY'P : oTwoUpper (preimBar H Xh) ⊔ T ≤ P :=
      hmp.le_of_lt hTY' (lt_of_le_of_ne hY'H fun h => hne h.symm)
    have hytP : h₀ ^ 2 ^ j ∈ P := hY'P (Subgroup.mem_sup_left hytO)
    have hQy : h₀ ^ orderOf y ∈ pCoreOf 2 H := by
      rw [← bar_eq_one_iff (H.pow_mem hh₀H _), bar_pow hh₀H, hh₀y]
      exact pow_orderOf_eq_one _
    have hcop : Nat.Coprime (2 ^ j) (orderOf y) :=
      Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hD.odd)
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have hh₀P : h₀ ∈ P := by
      have e : h₀ = (h₀ ^ 2 ^ j) ^ u * (h₀ ^ orderOf y) ^ v := by
        calc h₀ = h₀ ^ (1 : ℤ) := (zpow_one h₀).symm
          _ = h₀ ^ (u * ((2 ^ j : ℕ) : ℤ) + v * ((orderOf y : ℕ) : ℤ)) := by rw [huv]
          _ = (h₀ ^ 2 ^ j) ^ u * (h₀ ^ orderOf y) ^ v := by
            rw [zpow_add, mul_comm u, zpow_mul, mul_comm v, zpow_mul, zpow_natCast, zpow_natCast]
      rw [e]
      exact P.mul_mem (P.zpow_mem hytP u) (P.zpow_mem (hmp.le (hQT hQy)) v)
    have hxh : x⁻¹ * h₀ ∈ C := by
      refine (bar_mem_imBar_iff hQC (H.mul_mem (H.inv_mem hxH) hh₀H)).mp ?_
      rw [bar_mul (H.inv_mem hxH) hh₀H, bar_inv hxH, hh₀y]
      exact hyC
    apply hxP
    have : x = h₀ * (x⁻¹ * h₀)⁻¹ := by group
    rw [this]
    exact P.mul_mem hh₀P (P.inv_mem (hCP hxh))

end X1512

end CFSG.Quasithin

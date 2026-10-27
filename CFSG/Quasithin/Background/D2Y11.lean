module

public import CFSG.Quasithin.Background.D2Y10

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem exists_central_mod {G : Type*} [Group G] [Group.IsNilpotent G] {Q Z : Subgroup G}
    [Q.Normal] (hQ : ¬ Q ≤ Z) : ∃ q ∈ Q, q ∉ Z ∧ ∀ y : G, q * y * q⁻¹ * y⁻¹ ∈ Z := by
  classical
  have hex : ∃ k, ¬ (Q ⊓ Subgroup.upperCentralSeries G k ≤ Z) := by
    refine ⟨Group.nilpotencyClass G, ?_⟩
    rw [Subgroup.upperCentralSeries_nilpotencyClass, inf_top_eq]
    exact hQ
  have hk_spec : ¬ (Q ⊓ Subgroup.upperCentralSeries G (Nat.find hex) ≤ Z) := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hk_spec
    rw [h0, Subgroup.upperCentralSeries_zero]
    simp
  obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hmin : Q ⊓ Subgroup.upperCentralSeries G k' ≤ Z := by
    by_contra hcon
    exact Nat.find_min hex (show k' < Nat.find hex by omega) hcon
  rw [hk'] at hk_spec
  obtain ⟨q, ⟨hqQ, hqZ⟩, hqnZ⟩ := IsConcreteLE.not_le_iff_exists.mp hk_spec
  refine ⟨q, hqQ, hqnZ, fun y => hmin ⟨?_, ?_⟩⟩
  · have : q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) := by group
    rw [this]
    exact Q.mul_mem hqQ (Subgroup.Normal.conj_mem inferInstance _ (Q.inv_mem hqQ) y)
  · exact (Subgroup.mem_upperCentralSeries_succ_iff.mp hqZ) y

section Q

variable {X : Subgroup (MulAut V)} {t x z : MulAut V}

theorem exists_good (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (htwo : ∃ Y₁ ∈ Yinv X, ∃ Y₂ ∈ Yinv X, Y₁ ≠ Y₂) (h : InvPair X t x) : ∃ z, Good X t x z := by
  obtain ⟨y, d⟩ := exists_EData hV c hX1 h htwo
  exact D2_28 hV c hX1 d

theorem exists_normR_not_centR (h229 : centR X x ≠ pCoreOf 3 X) :
    ∃ q ∈ normR X x, q ∉ centR X x := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨g, hgR, hgN, hgP⟩ := exists_mem_normalizer_of_ne (pCoreOf_isPGroup 3 X)
    (inf_le_left : centR X x ≤ pCoreOf 3 X) h229
  exact ⟨g, ⟨hgR, hgN⟩, hgP⟩

theorem normR_eq_pCoreOf (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (htwo : ∃ Y₁ ∈ Yinv X, ∃ Y₂ ∈ Yinv X, Y₁ ≠ Y₂) (h : InvPair X t x) (hg : Good X t x z) :
    normR X x = pCoreOf 3 X := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h229 := D2_29 hV c hX1 hg htwo
  have hne := exists_normR_not_centR h229
  have hQcard := card_normR hV c hX1 h hg hne
  by_contra hQR
  obtain ⟨g, hgR, hgN, hgQ⟩ := exists_mem_normalizer_of_ne (pCoreOf_isPGroup 3 X)
    (normR_le_pCoreOf (X := X) (x := x)) hQR
  obtain ⟨Nn, hNn⟩ : ∃ Nn : Subgroup (MulAut V),
      Nn = pCoreOf 3 X ⊓ Subgroup.normalizer (normR X x : Set (MulAut V)) := ⟨_, rfl⟩
  have hQN : normR X x ≤ Nn := fun q hq => by
    rw [hNn]
    exact ⟨normR_le_pCoreOf hq, Subgroup.le_normalizer hq⟩
  have hNnR : Nn ≤ pCoreOf 3 X := by rw [hNn]; exact inf_le_left
  have hgNn : g ∈ Nn := by rw [hNn]; exact ⟨hgR, hgN⟩
  have hNn3 : IsPGroup 3 Nn :=
    (pCoreOf_isPGroup 3 X).of_injective (Subgroup.inclusion hNnR) (Subgroup.inclusion_injective _)
  have : Group.IsNilpotent ↥Nn := hNn3.isNilpotent
  have hnormQ : ∀ n ∈ Nn, ∀ q ∈ normR X x, n * q * n⁻¹ ∈ normR X x := fun n hn q hq => by
    rw [hNn] at hn
    exact (Subgroup.mem_normalizer_iff.mp hn.2 q).mp hq
  have hQnormal : (normR X x).subgroupOf Nn |>.Normal := ⟨fun n hn y => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnormQ y y.2 n hn⟩
  have hzP : Subgroup.zpowers z ≤ centR X x := Subgroup.zpowers_le.mpr hg.hz
  have hQZ : ¬ ((normR X x).subgroupOf Nn ≤ (Subgroup.zpowers z).subgroupOf Nn) := by
    intro hle
    obtain ⟨q₀, hq₀, hq₀P⟩ := hne
    have hmem : (⟨q₀, hQN hq₀⟩ : ↥Nn) ∈ (Subgroup.zpowers z).subgroupOf Nn :=
      hle (by rw [Subgroup.mem_subgroupOf]; exact hq₀)
    rw [Subgroup.mem_subgroupOf] at hmem
    exact hq₀P (hzP hmem)
  obtain ⟨q', hq'Q, hq'Z, hq'c⟩ := exists_central_mod hQZ
  rw [Subgroup.mem_subgroupOf] at hq'Q hq'Z
  have hq₁Q : (q' : MulAut V) ∈ normR X x := hq'Q
  have hq₁Z : (q' : MulAut V) ∉ Subgroup.zpowers z := hq'Z
  have hcentral : ∀ n ∈ Nn, (q' : MulAut V) * n * (q' : MulAut V)⁻¹ * n⁻¹ ∈ Subgroup.zpowers z :=
    fun n hn => by
      have := hq'c ⟨n, hn⟩
      rw [Subgroup.mem_subgroupOf] at this
      exact this
  obtain ⟨q₁, hq₁⟩ : ∃ q₁ : MulAut V, q₁ = (q' : MulAut V) := ⟨_, rfl⟩
  rw [← hq₁] at hq₁Q hq₁Z hcentral
  obtain ⟨hxo, hzo, hxz, hne', hsup⟩ := Good.E9 hV c hX1 h hg
  have hq₁3 : q₁ ^ 3 = 1 := normR_cube hV c hX1 h hg hq₁Q
  have hq₁1 : q₁ ≠ 1 := fun e => hq₁Z (by rw [e]; exact Subgroup.one_mem _)
  have hq₁o : orderOf q₁ = 3 := orderOf_eq_prime hq₁3 hq₁1
  have hq₁z : q₁ * z = z * q₁ := normR_comm_z hV c hX1 h hg hq₁Q
  have hne2 : Subgroup.zpowers q₁ ≠ Subgroup.zpowers z := fun e =>
    hq₁Z (by rw [← e]; exact Subgroup.mem_zpowers q₁)
  obtain ⟨hMcard, hMcomm, hMform⟩ := E9_data hq₁o hzo hq₁z hne2
  obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut V), M = Subgroup.zpowers q₁ ⊔ Subgroup.zpowers z :=
    ⟨_, rfl⟩
  rw [← hM] at hMcard hMcomm hMform
  have hq₁M : q₁ ∈ M := by rw [hM]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers q₁)
  have hzM : z ∈ M := by rw [hM]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hZM : Subgroup.zpowers z ≤ M := Subgroup.zpowers_le.mpr hzM
  have hr := normR_refl hV c hX1 h hg hq₁Q
  have htq₁ : t * q₁ * t⁻¹ ∈ M := by
    have e : t * q₁ * t⁻¹ = (t * q₁ * t⁻¹ * q₁) * q₁⁻¹ := by group
    rw [e]
    exact M.mul_mem (hZM hr) (M.inv_mem hq₁M)
  set l := q₁⁻¹ * (t * q₁ * t⁻¹) with hl
  have hlM : l ∈ M := M.mul_mem (M.inv_mem hq₁M) htq₁
  have hlR : l ∈ pCoreOf 3 X := by
    have h1 : q₁ ∈ pCoreOf 3 X := normR_le_pCoreOf hq₁Q
    have h2 : t * q₁ * t⁻¹ ∈ pCoreOf 3 X :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X h.ht.1) q₁).mp h1
    exact (pCoreOf 3 X).mul_mem ((pCoreOf 3 X).inv_mem h1) h2
  have hl1 : l ≠ 1 := by
    intro e
    have h1 : q₁ = t * q₁ * t⁻¹ := inv_mul_eq_one.mp e
    have h2 : q₁ * q₁ ∈ Subgroup.zpowers z := by
      have := hr
      rw [← h1] at this
      exact this
    apply hq₁Z
    have : q₁ = (q₁ * q₁)⁻¹ := by
      calc q₁ = q₁ ^ 3 * (q₁ * q₁)⁻¹ := by group
        _ = (q₁ * q₁)⁻¹ := by rw [hq₁3, one_mul]
    rw [this]
    exact Subgroup.inv_mem _ h2
  have hlinv : t * l * t⁻¹ = l⁻¹ := inv_conj_of_involution q₁ h.ht.2.2.1
  have hpl : InvPair X t l := ⟨h.ht, hlR, hl1, hlinv⟩
  obtain ⟨zl, hgl⟩ := exists_good hV c hX1 htwo hpl
  have hMcent : M ≤ centR X l := fun m hm => by
    refine mem_centR.mpr ⟨?_, hMcomm m hm l hlM⟩
    rw [hM] at hm
    exact (sup_le (Subgroup.zpowers_le.mpr (normR_le_pCoreOf hq₁Q))
      (Subgroup.zpowers_le.mpr (mem_centR.mp hg.hz).1)) hm
  have hMeq : M = centR X l := Subgroup.eq_of_le_of_card_ge hMcent (by rw [hgl.card, hMcard])
  have hneL := exists_normR_not_centR (D2_29 hV c hX1 hgl htwo)
  have hLcard := card_normR hV c hX1 hpl hgl hneL
  have hconjM : ∀ n ∈ Nn, ∀ m ∈ M, n * m * n⁻¹ ∈ M := by
    intro n hn m hm
    have hnz : n * z * n⁻¹ = z := by
      have := z_central hV c hX1 h hg hne n (hNnR hn)
      rw [← this]
      group
    have hnq : n * q₁ * n⁻¹ ∈ M := by
      have e : n * q₁ * n⁻¹ = (q₁ * n * q₁⁻¹ * n⁻¹)⁻¹ * q₁ := by group
      rw [e]
      exact M.mul_mem (M.inv_mem (hZM (hcentral n hn))) hq₁M
    rw [hM] at hm
    obtain ⟨-, -, hform'⟩ := E9_data hq₁o hzo hq₁z hne2
    obtain ⟨i, j, hij⟩ := hform' m hm
    rw [hij]
    have : n * (q₁ ^ i * z ^ j) * n⁻¹ = (n * q₁ * n⁻¹) ^ i * (n * z * n⁻¹) ^ j := by
      calc n * (q₁ ^ i * z ^ j) * n⁻¹ = (n * q₁ ^ i * n⁻¹) * (n * z ^ j * n⁻¹) := by group
        _ = _ := by rw [← conj_zpow, ← conj_zpow]
    rw [this, hnz]
    exact M.mul_mem (M.zpow_mem hnq i) (M.zpow_mem hzM j)
  have hNnL : Nn ≤ normR X l := by
    intro n hn
    refine ⟨hNnR hn, ?_⟩
    rw [← hMeq]
    refine Subgroup.mem_normalizer_iff.mpr fun m => ?_
    constructor
    · exact hconjM n hn m
    · intro hm
      have := hconjM n⁻¹ (Nn.inv_mem hn) _ hm
      simpa [mul_assoc] using this
  have hQL : normR X x = normR X l := by
    refine Subgroup.eq_of_le_of_card_ge (hQN.trans hNnL) ?_
    rw [hLcard, hQcard]
  exact hgQ (by rw [hQL]; exact hNnL hgNn)

end Q

end CFSG.Quasithin

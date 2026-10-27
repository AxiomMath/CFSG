module

public import CFSG.RankThree.PartTwo.KFacts.K71G2
public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeOffCard
public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeOffTorsion

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.Chevalley (torusTorsion)

namespace G2OffAuxStd

private lemma isElemAbelian_map {H : Type*} [Group H] (e : MulAut H) {B : Subgroup H}
    {p : ℕ} (hB : IsElemAbelian p B) :
    IsElemAbelian p (B.map e.toMonoidHom) := by
  constructor
  · refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp y.2
    show (x : H) * (y : H) = (y : H) * (x : H)
    rw [← hax, ← hby, ← map_mul, ← map_mul]
    have hcomm : a * b = b * a := by
      have := congrArg Subtype.val (hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      simpa using this
    rw [hcomm]
  · intro x hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    show (x : H) ^ p = 1
    rw [← hax, ← map_pow, hB.2 a ha, map_one]

private lemma zpow_eq_zpow_emod {H : Type*} [Group H] {x : H} (hx : x ^ 3 = 1) (j : ℤ) :
    x ^ j = x ^ (j % (3 : ℤ)) :=
  zpow_eq_zpow_emod' j hx

private lemma exists_mem_mul_zpow_of_card {H : Type*} [Group H] [Finite H]
    {A₁ B : Subgroup H} (hBA : B ≤ A₁) (hcomm : IsMulCommutative ↥A₁)
    (hA : Nat.card ↥A₁ = 27) (hB : Nat.card ↥B = 9)
    {φ : H} (hφA : φ ∈ A₁) (hφB : φ ∉ B) (hφ3 : φ ^ 3 = 1)
    {x : H} (hxA : x ∈ A₁) :
    ∃ b ∈ B, ∃ j : ℕ, x = b * φ ^ j := by
  classical
  letI : IsMulCommutative ↥A₁ := hcomm
  let B' : Subgroup ↥A₁ := B.subgroupOf A₁
  haveI : B'.Normal := Subgroup.normal_of_comm B'
  have hB'card : Nat.card ↥B' = 9 := by
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective A₁)]
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBA]
    exact hB
  have hQ : Nat.card (↥A₁ ⧸ B') = 3 := by
    rw [← Subgroup.index_eq_card]
    have h := Subgroup.index_mul_card B'
    rw [hB'card, hA] at h
    omega
  let φ' : ↥A₁ := ⟨φ, hφA⟩
  have hφ'3 : φ' ^ 3 = 1 := Subtype.ext (by simpa using hφ3)
  have hqφ3 : QuotientGroup.mk (s := B') φ' ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hφ'3, QuotientGroup.mk_one]
  have hqφ1 : QuotientGroup.mk (s := B') φ' ≠ 1 := by
    intro h
    have h' : QuotientGroup.mk (s := B') φ' = QuotientGroup.mk (s := B') (1 : ↥A₁) := by
      simpa using h
    have hmem : φ'⁻¹ * 1 ∈ B' := (QuotientGroup.eq (s := B')).mp h'
    have hmem' : φ' ∈ B' := by simpa using B'.inv_mem hmem
    exact hφB (Subgroup.mem_subgroupOf.mp hmem')
  have htop : Subgroup.zpowers (QuotientGroup.mk (s := B') φ') = ⊤ := by
    refine Subgroup.eq_of_le_of_card_ge le_top ?_
    rw [Subgroup.card_top, hQ, Nat.card_zpowers, orderOf_eq_prime hqφ3 hqφ1]
  have hxmem : QuotientGroup.mk (s := B') (⟨x, hxA⟩ : ↥A₁) ∈
      Subgroup.zpowers (QuotientGroup.mk (s := B') φ') := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have hqj : QuotientGroup.mk (s := B') (φ' ^ j) =
      QuotientGroup.mk (s := B') (⟨x, hxA⟩ : ↥A₁) := by
    rw [QuotientGroup.mk_zpow]
    exact hj
  have hmem : (⟨x, hxA⟩ : ↥A₁)⁻¹ * φ' ^ j ∈ B' :=
    (QuotientGroup.eq (s := B')).mp hqj.symm
  have hmemH : x⁻¹ * φ ^ j ∈ B := by
    have h := Subgroup.mem_subgroupOf.mp hmem
    simpa [φ'] using h
  have hxφ : x * φ ^ j = φ ^ j * x := by
    have h := congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hxA⟩ (⟨φ, hφA⟩ ^ j))
    simpa using h
  have hfinal : x = (x⁻¹ * φ ^ j)⁻¹ * φ ^ j := by
    rw [mul_inv_rev, inv_inv]
    calc x = (φ ^ j)⁻¹ * (φ ^ j * x) := by group
      _ = (φ ^ j)⁻¹ * (x * φ ^ j) := by rw [hxφ]
      _ = (φ ^ j)⁻¹ * x * φ ^ j := by group
  have hpow : φ ^ j = φ ^ ((j % 3).toNat) := by
    rw [zpow_eq_zpow_emod hφ3 j, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg j (by norm_num))]
  have hfinal' : x = (x⁻¹ * φ ^ ((j % 3).toNat))⁻¹ * φ ^ ((j % 3).toNat) := by
    rw [hpow] at hfinal
    exact hfinal
  have hmemH' : x⁻¹ * φ ^ ((j % 3).toNat) ∈ B := by
    rw [← hpow]
    exact hmemH
  exact ⟨(x⁻¹ * φ ^ ((j % 3).toNat))⁻¹, B.inv_mem hmemH', (j % 3).toNat, hfinal'⟩

end G2OffAuxStd

theorem ggNbrG2Off_stdForm
    {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (h6 : 6 ∣ n) (A : Subgroup (MulAut (adjointGroup Tag.G2 K))) (hA : IsElemAbelian 3 A)
    (h27 : 27 ≤ Nat.card A) :
    ∃ (σ : K ≃+* K) (x : adjointGroup Tag.G2 K), orderOf σ = 3 ∧
      ∀ α ∈ A, ∃ (z : adjointGroup Tag.G2 K) (j : ℕ), (z : ModGL Tag.G2 K) ∈ torusTorsion K 3 ∧
        g2FieldHom K σ z = z ∧
        MulAut.conj x * α * (MulAut.conj x)⁻¹ = MulAut.conj z * g2FieldHom K σ ^ j := by
  classical
  haveI : CharP K 2 := charP_two_of_card hK
  have hring : ringChar K = 2 := ringChar.eq K 2
  have hK3 : ringChar K ≠ 3 := by
    rw [hring]
    norm_num
  have hK2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hK
    omega
  have h6' : 6 ∣ n := h6
  obtain ⟨m, hm⟩ := h6
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [hm, mul_zero, pow_zero] at hK
      omega
    · exact h
  have hn : 2 ≤ n := by
    rw [hm]
    omega
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨hcardA, hcardInn⟩ := ggNbrG2Off_elemAbelian_card hK hn A hA h27
  let Inn : Subgroup (MulAut (adjointGroup Tag.G2 K)) :=
    (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range
  have hnotle : ¬ A ≤ Inn := by
    intro hle
    have hAeq : A ⊓ Inn = A := inf_eq_left.mpr hle
    have : Nat.card A = 9 := by rw [← hcardInn, hAeq]
    omega
  have hex : ∃ α₀ ∈ A, α₀ ∉ Inn := by
    by_contra h
    push Not at h
    exact hnotle fun x hx => h x hx
  obtain ⟨α₀, hα₀A, hα₀out⟩ := hex
  have hα₀3 : α₀ ^ 3 = 1 := hA.2 α₀ hα₀A
  obtain ⟨σ, hσ, k, hα₀eq⟩ :=
    g2_order_three_field_descent (K := K) hK3 hK4 hα₀3 hα₀out
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    omega
  have hfaith := (g2_automorphism_normal_form hK3 hK4).2
  have hφnotinner : ¬ IsInnerAut (g2FieldHom K σ) := fun h => hσ1 (hfaith σ h)
  let φ : MulAut (adjointGroup Tag.G2 K) := g2FieldHom K σ
  have hσ3 : σ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one σ
    rwa [hσ] at h
  have hφ3 : φ ^ 3 = 1 := by
    rw [show φ = g2FieldHom K σ from rfl, ← map_pow, hσ3, map_one]
  let c : MulAut (adjointGroup Tag.G2 K) := (MulAut.conj k)⁻¹
  have hconj_inj : Function.Injective
      (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)) :=
    mulAut_conj_injective (center_adjointGroup_eq_bot (τ := Tag.G2) (K := K))
  have hφeq : g2FieldHom K σ = MulAut.conj c α₀ := by
    rw [hα₀eq, MulAut.conj_apply]
    simp only [c]
    group
  let A₁ : Subgroup (MulAut (adjointGroup Tag.G2 K)) := A.map (MulAut.conj c).toMonoidHom
  have hφA : φ ∈ A₁ := by
    show g2FieldHom K σ ∈ A.map (MulAut.conj c).toMonoidHom
    rw [hφeq]
    exact Subgroup.mem_map.mpr ⟨α₀, hα₀A, rfl⟩
  have hA₁ : IsElemAbelian 3 A₁ := G2OffAuxStd.isElemAbelian_map (MulAut.conj c) hA
  have hcardA₁ : Nat.card ↥A₁ = 27 := by
    show Nat.card ↥(A.map (MulAut.conj c).toMonoidHom) = 27
    rw [Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj c))]
    exact hcardA
  have hInn_map : Inn.map (MulAut.conj c).toMonoidHom = Inn := by
    ext τ
    constructor
    · intro hτ
      obtain ⟨ι, hι, rfl⟩ := Subgroup.mem_map.mp hτ
      obtain ⟨y, rfl⟩ := hι
      exact ⟨c y, (mul_mulAutConj_mul_inv c y).symm⟩
    · intro hτ
      obtain ⟨y, rfl⟩ := hτ
      refine Subgroup.mem_map.mpr ⟨MulAut.conj (c⁻¹ y), ?_, ?_⟩
      · exact ⟨c⁻¹ y, rfl⟩
      · change c * MulAut.conj (c⁻¹ y) * c⁻¹ = MulAut.conj y
        rw [mul_mulAutConj_mul_inv]
        simp
  have hcardB₁ : Nat.card ↥(A₁ ⊓ Inn) = 9 := by
    have hmap : (A ⊓ Inn).map (MulAut.conj c).toMonoidHom = A₁ ⊓ Inn := by
      rw [Subgroup.map_inf A Inn (MulAut.conj c).toMonoidHom
        (MulEquiv.injective (MulAut.conj c)), hInn_map]
    rw [← hmap, Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj c))]
    exact hcardInn
  let E₁ : Subgroup (adjointGroup Tag.G2 K) :=
    (A₁ ⊓ Inn).comap (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K))
  have hE₁ : IsElemAbelian 3 E₁ := by
    constructor
    · refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
      apply hconj_inj
      have hx : MulAut.conj (x : adjointGroup Tag.G2 K) ∈ A₁ :=
        (Subgroup.mem_comap.mp x.2).1
      have hy : MulAut.conj (y : adjointGroup Tag.G2 K) ∈ A₁ :=
        (Subgroup.mem_comap.mp y.2).1
      have hcomm := congrArg Subtype.val
        (hA₁.1.is_comm.comm ⟨MulAut.conj (x : adjointGroup Tag.G2 K), hx⟩
          ⟨MulAut.conj (y : adjointGroup Tag.G2 K), hy⟩)
      simp only [Subgroup.coe_mul] at hcomm
      show MulAut.conj ((x : adjointGroup Tag.G2 K) * (y : adjointGroup Tag.G2 K)) =
        MulAut.conj ((y : adjointGroup Tag.G2 K) * (x : adjointGroup Tag.G2 K))
      simp only [map_mul]
      exact hcomm
    · intro x hx
      apply hconj_inj
      rw [map_pow, map_one]
      exact hA₁.2 (MulAut.conj (x : adjointGroup Tag.G2 K)) (Subgroup.mem_comap.mp hx).1
  have hE₁fix : ∀ y ∈ E₁, g2FieldHom K σ y = y := by
    intro y hy
    have hyA : MulAut.conj y ∈ A₁ := (Subgroup.mem_comap.mp hy).1
    have hcomm := congrArg Subtype.val
      (hA₁.1.is_comm.comm ⟨φ, hφA⟩ ⟨MulAut.conj y, hyA⟩)
    simp only [Subgroup.coe_mul] at hcomm
    have h1 : MulAut.conj (g2FieldHom K σ y) = MulAut.conj y := by
      rw [← mul_mulAutConj_mul_inv]
      rw [hcomm]
      change MulAut.conj y * φ * φ⁻¹ = MulAut.conj y
      group
    exact hconj_inj h1
  obtain ⟨g', hg'fix, hg'tor⟩ :=
    ggNbrG2Off_conj_torsion hK h6' σ hσ hE₁ hE₁fix
  refine ⟨σ, g' * k⁻¹, hσ, fun α hα => ?_⟩
  have hα₁A : c * α * c⁻¹ ∈ A₁ := by
    have h : MulAut.conj c α ∈ A₁ := Subgroup.mem_map.mpr ⟨α, hα, rfl⟩
    rwa [MulAut.conj_apply] at h
  obtain ⟨b, hbB, j, hα₁_eq⟩ :=
    G2OffAuxStd.exists_mem_mul_zpow_of_card (B := A₁ ⊓ Inn) inf_le_left hA₁.1
      hcardA₁ hcardB₁ hφA (fun h => hφnotinner h.2) hφ3 hα₁A
  obtain ⟨y, hyb⟩ := hbB.2
  have hyE : y ∈ E₁ := by
    rw [Subgroup.mem_comap, hyb]
    exact hbB
  have hα₁_eq' : c * α * c⁻¹ = MulAut.conj y * g2FieldHom K σ ^ j := by
    rw [hα₁_eq, ← hyb]
  have hαeq : α = c⁻¹ * (MulAut.conj y * g2FieldHom K σ ^ j) * c := by
    rw [← hα₁_eq']
    group
  have hxconj : MulAut.conj (g' * k⁻¹) = MulAut.conj g' * c := by
    simp [c]
  have hstep1 : MulAut.conj (g' * k⁻¹) * α * (MulAut.conj (g' * k⁻¹))⁻¹
      = MulAut.conj g' * (MulAut.conj y * g2FieldHom K σ ^ j) *
        (MulAut.conj g')⁻¹ := by
    rw [hαeq]
    simp only [hxconj]
    group
  have hcommφg : Commute (g2FieldHom K σ) (MulAut.conj g')⁻¹ := by
    rw [Commute]
    have h1 : g2FieldHom K σ * (MulAut.conj g')⁻¹ * (g2FieldHom K σ)⁻¹ =
        (MulAut.conj g')⁻¹ := by
      rw [← map_inv]
      rw [mul_mulAutConj_mul_inv]
      rw [map_inv, hg'fix]
    calc g2FieldHom K σ * (MulAut.conj g')⁻¹
        = (g2FieldHom K σ * (MulAut.conj g')⁻¹ * (g2FieldHom K σ)⁻¹) *
            g2FieldHom K σ := by group
      _ = (MulAut.conj g')⁻¹ * g2FieldHom K σ := by rw [h1]
  have hstep2 : MulAut.conj g' * (MulAut.conj y * g2FieldHom K σ ^ j) *
        (MulAut.conj g')⁻¹
      = MulAut.conj (g' * y * g'⁻¹) * g2FieldHom K σ ^ j := by
    have hconjz : MulAut.conj g' * MulAut.conj y * (MulAut.conj g')⁻¹
        = MulAut.conj (g' * y * g'⁻¹) := by
      simp only [map_mul, map_inv]
    have hcommP : g2FieldHom K σ ^ j * (MulAut.conj g')⁻¹
        = (MulAut.conj g')⁻¹ * g2FieldHom K σ ^ j := (hcommφg.pow_left j).eq
    calc MulAut.conj g' * (MulAut.conj y * g2FieldHom K σ ^ j) * (MulAut.conj g')⁻¹
        = MulAut.conj g' * MulAut.conj y *
            (g2FieldHom K σ ^ j * (MulAut.conj g')⁻¹) := by group
      _ = MulAut.conj g' * MulAut.conj y *
            ((MulAut.conj g')⁻¹ * g2FieldHom K σ ^ j) := by rw [hcommP]
      _ = (MulAut.conj g' * MulAut.conj y * (MulAut.conj g')⁻¹) *
            g2FieldHom K σ ^ j := by group
      _ = MulAut.conj (g' * y * g'⁻¹) * g2FieldHom K σ ^ j := by rw [hconjz]
  have hzfix : g2FieldHom K σ (g' * y * g'⁻¹) = g' * y * g'⁻¹ := by
    simp only [map_mul, map_inv, hg'fix, hE₁fix y hyE]
  exact ⟨g' * y * g'⁻¹, j, hg'tor y hyE, hzfix, by rw [hstep1, hstep2]⟩

end CFSG.StandardType

end

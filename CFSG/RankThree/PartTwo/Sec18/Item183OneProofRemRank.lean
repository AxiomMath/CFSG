module

public import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRemTools
public import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
public import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank
import CFSG.RankThree.PartTwo.Sec18.Item181b

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open scoped Pointwise

namespace Rem187QProof

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mk_eq_one {X : Subgroup G} {x : X} (hx3 : (x : G) ^ 3 = 1)
    (hx : QuotientGroup.mk' (CFSG.pCore 2 X) x = 1) : (x : G) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at hx
  obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) ⟨_, hx⟩
  exact eq_one_of_pow_three_of_pow_two_pow hx3 (by simpa using congrArg Subtype.val hn)

theorem mem_normalizer_of_localRank {X K B : Subgroup G} (hX2 : CFSG.Open.pCoreOf 2 X ≠ ⊥)
    (hK : K ∈ oTwoComponentsIn X) (hBK : B ≤ K) (hBe : ∀ b ∈ B, b ^ 3 = 1)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hB9 : Nat.card B = 9)
    (hBC : ∀ b ∈ B, (∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 X) → b = 1)
    (hrank : CFSG.Assembly.RankThreeEven.localRank 3 G ≤ 3) {g : G} (hgX : g ∈ X) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set K' := K.map (MulAut.conj g).toMonoidHom with hK'def
  have hK' : K' ∈ oTwoComponentsIn X := map_conj_mem_oTwoComponentsIn hK hgX
  have hKX : K ≤ X := le_of_mem_oTwoComponentsIn hK
  have hK'X : K' ≤ X := le_of_mem_oTwoComponentsIn hK'
  set π := QuotientGroup.mk' (CFSG.pCore 2 X) with hπ
  have hBne : B ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hB9
    norm_num at hB9
  obtain ⟨⟨b₁, hb₁B⟩, hb₁1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hBne
  have hb₁1' : b₁ ≠ 1 := fun h => hb₁1 (Subtype.ext h)
  obtain ⟨b₂, hb₂B, hb₂z⟩ : ∃ b₂ ∈ B, b₂ ∉ Subgroup.zpowers b₁ := by
    by_contra hall
    push Not at hall
    have hle : B ≤ Subgroup.zpowers b₁ := hall
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card (Subgroup.zpowers b₁) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hBe b₁ hb₁B))
    omega
  have hconj : ∀ b ∈ B, g * b * g⁻¹ ∈ K' := fun b hb => ⟨b, hBK hb, rfl⟩
  set x₁ : X := ⟨b₁, hKX (hBK hb₁B)⟩ with hx₁
  set x₂ : X := ⟨b₂, hKX (hBK hb₂B)⟩ with hx₂
  set y₁ : X := ⟨g * b₁ * g⁻¹, hK'X (hconj b₁ hb₁B)⟩ with hy₁
  set y₂ : X := ⟨g * b₂ * g⁻¹, hK'X (hconj b₂ hb₂B)⟩ with hy₂
  have hcomm : ∀ y : X, (y : G) ∈ K' → ∀ k : X, (k : G) ∈ K → π y * π k = π k * π y :=
    fun y hy k hk => Sec19.Step1910Proof.mk_mul_comm_of_ne hK' hK hne hy hk
  have hBtriv : ∀ (b : X), (b : G) ∈ B → (∀ k : X, (k : G) ∈ K → π b * π k = π k * π b) →
      (b : G) = 1 := by
    intro b hb hbk
    refine hBC _ hb fun k hk => ?_
    have h1 : π (b * ⟨k, hKX hk⟩ * b⁻¹ * (⟨k, hKX hk⟩ : X)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hbk ⟨k, hKX hk⟩ hk]
      group
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at h1
    simpa using h1
  set Bs := (B.subgroupOf X).map π with hBs
  have hmemBs : ∀ b (hb : b ∈ B), π ⟨b, hKX (hBK hb)⟩ ∈ Bs := fun b hb =>
    ⟨⟨b, hKX (hBK hb)⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have hBstriv : ∀ w ∈ Bs, (∀ k : X, (k : G) ∈ K → w * π k = π k * w) → w = 1 := by
    rintro _ ⟨b, hb, rfl⟩ hbk
    have := hBtriv b (Subgroup.mem_subgroupOf.mp hb) hbk
    rw [show b = 1 from Subtype.ext this, map_one]
  have hpow : ∀ x : X, (x : G) ^ 3 = 1 → π x ^ 3 = 1 := fun x hx => by
    rw [← map_pow, show x ^ 3 = 1 from Subtype.ext (by simpa using hx), map_one]
  have hb₁3 := hBe b₁ hb₁B
  have hb₂3 := hBe b₂ hb₂B
  have hy₁3 : (y₁ : G) ^ 3 = 1 := by
    change (g * b₁ * g⁻¹) ^ 3 = 1
    rw [conj_pow, hb₁3, mul_one, mul_inv_cancel]
  have hy₂3 : (y₂ : G) ^ 3 = 1 := by
    change (g * b₂ * g⁻¹) ^ 3 = 1
    rw [conj_pow, hb₂3, mul_one, mul_inv_cancel]
  have hc12 : π x₁ * π x₂ = π x₂ * π x₁ := by
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (hBc b₁ hb₁B b₂ hb₂B))
  have hc34 : π y₁ * π y₂ = π y₂ * π y₁ := by
    rw [← map_mul, ← map_mul]
    refine congrArg π (Subtype.ext ?_)
    change g * b₁ * g⁻¹ * (g * b₂ * g⁻¹) = g * b₂ * g⁻¹ * (g * b₁ * g⁻¹)
    calc g * b₁ * g⁻¹ * (g * b₂ * g⁻¹) = g * (b₁ * b₂) * g⁻¹ := by group
      _ = g * (b₂ * b₁) * g⁻¹ := by rw [hBc b₁ hb₁B b₂ hb₂B]
      _ = g * b₂ * g⁻¹ * (g * b₁ * g⁻¹) := by group
  have hc13 : π x₁ * π y₁ = π y₁ * π x₁ := (hcomm y₁ (hconj b₁ hb₁B) x₁ (hBK hb₁B)).symm
  have hc14 : π x₁ * π y₂ = π y₂ * π x₁ := (hcomm y₂ (hconj b₂ hb₂B) x₁ (hBK hb₁B)).symm
  have hc23 : π x₂ * π y₁ = π y₁ * π x₂ := (hcomm y₁ (hconj b₁ hb₁B) x₂ (hBK hb₂B)).symm
  have hc24 : π x₂ * π y₂ = π y₂ * π x₂ := (hcomm y₂ (hconj b₂ hb₂B) x₂ (hBK hb₂B)).symm
  have hn₁ : π x₁ ≠ 1 := fun h => hb₁1' (eq_one_of_mk_eq_one hb₁3 h)
  have hn₂ : π x₂ ∉ Subgroup.zpowers (π x₁) := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have h1 : π (x₂ * (x₁ ^ k)⁻¹) = 1 := by rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
    have h3 : ((x₂ * (x₁ ^ k)⁻¹ : X) : G) ^ 3 = 1 := by
      have hm : b₂ * (b₁ ^ k)⁻¹ ∈ B := B.mul_mem hb₂B (B.inv_mem (B.zpow_mem hb₁B k))
      simpa using hBe _ hm
    have h4 := eq_one_of_mk_eq_one h3 h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow] at h4
    exact hb₂z (Subgroup.mem_zpowers_iff.mpr ⟨k, (mul_inv_eq_one.mp h4).symm⟩)
  have hzBs : Subgroup.zpowers (π x₁) ⊔ Subgroup.zpowers (π x₂) ≤ Bs :=
    sup_le (Subgroup.zpowers_le.mpr (hmemBs b₁ hb₁B)) (Subgroup.zpowers_le.mpr (hmemBs b₂ hb₂B))
  have hn₃ : π y₁ ∉ Subgroup.zpowers (π x₁) ⊔ Subgroup.zpowers (π x₂) := by
    intro h
    have h1 := hBstriv _ (hzBs h) (hcomm y₁ (hconj b₁ hb₁B))
    have h2 := eq_one_of_mk_eq_one hy₁3 h1
    change g * b₁ * g⁻¹ = 1 at h2
    exact hb₁1' (by
      calc b₁ = g⁻¹ * (g * b₁ * g⁻¹) * g := by group
        _ = 1 := by rw [h2]; group)
  have hn₄ : π y₂ ∉ Subgroup.zpowers (π x₁) ⊔ Subgroup.zpowers (π x₂) ⊔
      Subgroup.zpowers (π y₁) := by
    intro h
    have hle : Subgroup.zpowers (π x₁) ⊔ Subgroup.zpowers (π x₂) ⊔ Subgroup.zpowers (π y₁) ≤
        Bs ⊔ Subgroup.zpowers (π y₁) := sup_le_sup_right hzBs _
    have hBsN : Bs ≤ Subgroup.normalizer (Subgroup.zpowers (π y₁) : Set _) := by
      intro w hw
      refine centralizer_le_normalizer_zpowers (π y₁) ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨b, hb, rfl⟩ := hw
      exact (hcomm y₁ (hconj b₁ hb₁B) b (hBK (Subgroup.mem_subgroupOf.mp hb))).symm
    have h' : π y₂ ∈ ((Bs : Set (X ⧸ CFSG.pCore 2 X)) *
        (Subgroup.zpowers (π y₁) : Set (X ⧸ CFSG.pCore 2 X))) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Bs _ hBsN]
      exact hle h
    obtain ⟨w, hw, z, hz, hwz⟩ := h'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hwy : w = π (y₂ * (y₁ ^ k)⁻¹) := by
      rw [map_mul, map_inv, map_zpow, ← hwz]
      group
    have hmK' : ((y₂ * (y₁ ^ k)⁻¹ : X) : G) ∈ K' := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
      exact K'.mul_mem (hconj b₂ hb₂B) (K'.inv_mem (K'.zpow_mem (hconj b₁ hb₁B) k))
    have hw1 : w = 1 := hBstriv w hw (fun k' hk' => by rw [hwy]; exact hcomm _ hmK' k' hk')
    have h1 : π (y₂ * (y₁ ^ k)⁻¹) = 1 := hwy ▸ hw1
    have h3 : ((y₂ * (y₁ ^ k)⁻¹ : X) : G) ^ 3 = 1 := by
      have hm : b₂ * (b₁ ^ k)⁻¹ ∈ B := B.mul_mem hb₂B (B.inv_mem (B.zpow_mem hb₁B k))
      have e : ((y₂ * (y₁ ^ k)⁻¹ : X) : G) = g * (b₂ * (b₁ ^ k)⁻¹) * g⁻¹ := by
        simp only [hy₁, hy₂, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
        rw [conj_zpow]
        group
      rw [e, conj_pow, hBe _ hm, mul_one, mul_inv_cancel]
    have h4 := eq_one_of_mk_eq_one h3 h1
    have e : ((y₂ * (y₁ ^ k)⁻¹ : X) : G) = g * (b₂ * (b₁ ^ k)⁻¹) * g⁻¹ := by
      simp only [hy₁, hy₂, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
      rw [conj_zpow]
      group
    rw [e] at h4
    have h5 : b₂ * (b₁ ^ k)⁻¹ = 1 := by
      calc b₂ * (b₁ ^ k)⁻¹ = g⁻¹ * (g * (b₂ * (b₁ ^ k)⁻¹) * g⁻¹) * g := by group
        _ = 1 := by rw [h4]; group
    exact hb₂z (Subgroup.mem_zpowers_iff.mpr ⟨k, (mul_inv_eq_one.mp h5).symm⟩)
  have h4 := Sec19.Step1919NarrowRank.four_le_localRank_of_chain hX2 hc12 hc13 hc14 hc23 hc24 hc34
    (hpow x₁ hb₁3) (hpow x₂ hb₂3) (hpow y₁ hy₁3) (hpow y₂ hy₂3) hn₁ hn₂ hn₃ hn₄
  omega

end Rem187QProof

end CFSG.RankThree.PartTwo.Sec18

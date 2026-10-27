module

public import CFSG.RankThree.PartOne.RF4.Basic
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LieType.Ree.LargeReeInvolutionFusion
public import CFSG.LieType.Ree.LargeReeInvolutionFusionWord
public import Certificates.Certificate3951
public import Certificates.Certificate18000
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.LargeReeInvolution

theorem not_dvd_involution_centralizer_orders {q p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hq : 2 ≤ q) (hqp : ¬ p ∣ q) (h : p ∣ q ^ 2 - q + 1 ∨ p ∣ q ^ 4 - q ^ 2 + 1) :
    ¬ p ∣ q ^ 12 * (q - 1) * (q ^ 2 + 1) ∧ ¬ p ∣ q ^ 10 * (q ^ 2 - 1) := by
  have hq1 : 1 ≤ q := by omega
  have hqq : q ≤ q ^ 2 := by nlinarith
  have hq21 : 1 ≤ q ^ 2 := by nlinarith
  have hq42 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hpZ : ¬ (p : ℤ) ∣ 1 := fun hd => by
    have := Int.le_of_dvd one_pos hd
    omega
  have h3 : ¬ (p : ℤ) ∣ 3 := fun hd => by
    have := Int.le_of_dvd (by norm_num) hd
    omega
  have hqZ : ¬ (p : ℤ) ∣ (q : ℤ) := fun hd => hqp (Int.natCast_dvd_natCast.1 hd)
  have hz : (p : ℤ) ∣ (q : ℤ) ^ 2 - q + 1 ∨ (p : ℤ) ∣ (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 := by
    rcases h with h | h
    · left
      have := Int.natCast_dvd_natCast.2 h
      push_cast [Nat.cast_sub hqq] at this
      exact this
    · right
      have := Int.natCast_dvd_natCast.2 h
      push_cast [Nat.cast_sub hq42] at this
      exact this
  have hA : ¬ p ∣ q - 1 := by
    intro hd
    have h' : (p : ℤ) ∣ (q : ℤ) - 1 := by
      have := Int.natCast_dvd_natCast.2 hd
      push_cast [Nat.cast_sub hq1] at this
      exact this
    rcases hz with hz | hz
    · apply hpZ
      have h1 : (p : ℤ) ∣ (q : ℤ) * ((q : ℤ) - 1) := h'.mul_left _
      have := dvd_sub hz h1
      have e : (q : ℤ) ^ 2 - q + 1 - (q : ℤ) * ((q : ℤ) - 1) = 1 := by ring
      rwa [e] at this
    · apply hpZ
      have h1 : (p : ℤ) ∣ ((q : ℤ) ^ 3 + (q : ℤ) ^ 2) * ((q : ℤ) - 1) := h'.mul_left _
      have := dvd_sub hz h1
      have e : (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 -
          ((q : ℤ) ^ 3 + (q : ℤ) ^ 2) * ((q : ℤ) - 1) = 1 := by ring
      rwa [e] at this
  have hB : ¬ p ∣ q ^ 2 + 1 := by
    intro hd
    have h' : (p : ℤ) ∣ (q : ℤ) ^ 2 + 1 := by
      have := Int.natCast_dvd_natCast.2 hd
      push_cast at this
      exact this
    rcases hz with hz | hz
    · apply hqZ
      have := dvd_sub h' hz
      have e : (q : ℤ) ^ 2 + 1 - ((q : ℤ) ^ 2 - q + 1) = q := by ring
      rwa [e] at this
    · apply h3
      have h1 : (p : ℤ) ∣ ((q : ℤ) ^ 2 - 2) * ((q : ℤ) ^ 2 + 1) := h'.mul_left _
      have := dvd_sub h1 hz
      have e : ((q : ℤ) ^ 2 - 2) * ((q : ℤ) ^ 2 + 1) - ((q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1) = -3 := by
        ring
      rw [e] at this
      exact (dvd_neg).1 this
  have hC : ¬ p ∣ q ^ 2 - 1 := by
    intro hd
    have h' : (p : ℤ) ∣ (q : ℤ) ^ 2 - 1 := by
      have := Int.natCast_dvd_natCast.2 hd
      push_cast [Nat.cast_sub hq21] at this
      exact this
    rcases hz with hz | hz
    · apply h3
      have h1 : (p : ℤ) ∣ (q : ℤ) - 2 := by
        have := dvd_sub h' hz
        have e : (q : ℤ) ^ 2 - 1 - ((q : ℤ) ^ 2 - q + 1) = (q : ℤ) - 2 := by ring
        rwa [e] at this
      have h2 : (p : ℤ) ∣ ((q : ℤ) - 2) * ((q : ℤ) + 2) := h1.mul_right _
      have := dvd_sub h' h2
      have e : (q : ℤ) ^ 2 - 1 - ((q : ℤ) - 2) * ((q : ℤ) + 2) = 3 := by ring
      rwa [e] at this
    · apply hpZ
      have h1 : (p : ℤ) ∣ (q : ℤ) ^ 2 * ((q : ℤ) ^ 2 - 1) := h'.mul_left _
      have := dvd_sub hz h1
      have e : (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 - (q : ℤ) ^ 2 * ((q : ℤ) ^ 2 - 1) = 1 := by ring
      rwa [e] at this
  refine ⟨?_, ?_⟩
  · intro hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
    · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
      · exact hqp (hp.dvd_of_dvd_pow hd)
      · exact hA hd
    · exact hB hd
  · intro hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
    · exact hqp (hp.dvd_of_dvd_pow hd)
    · exact hC hd

theorem dvd_card_inf_centralizer_of_conj {G : Type*} [Group G] [Finite G] {Γ : Subgroup G}
    {p : ℕ} {c g u x : G} (hu : u ∈ Γ) (hgc : u * g * u⁻¹ = c) (hx : x ∈ Γ)
    (hxg : x * g = g * x) (hxp : orderOf x = p) :
    p ∣ Nat.card (Γ ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) := by
  have hmem : u * x * u⁻¹ ∈ Γ ⊓ Subgroup.centralizer ({c} : Set G) := by
    refine Subgroup.mem_inf.2 ⟨Γ.mul_mem (Γ.mul_mem hu hx) (Γ.inv_mem hu),
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hgc]
    calc u * x * u⁻¹ * (u * g * u⁻¹) = u * (x * g) * u⁻¹ := by group
      _ = u * (g * x) * u⁻¹ := by rw [hxg]
      _ = u * g * u⁻¹ * (u * x * u⁻¹) := by group
  have hord : orderOf (⟨u * x * u⁻¹, hmem⟩ : (Γ ⊓ Subgroup.centralizer ({c} : Set G) :
      Subgroup G)) = p := by
    rw [← hxp, ← Subgroup.orderOf_coe]
    exact orderOf_injective (MulAut.conj u).toMonoidHom (MulAut.conj u).injective x
  rw [← hord]
  exact orderOf_dvd_natCard _

section Main

variable
  {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

local notation "Γ₀" => ReeTag.F4.reeGamma K a

theorem not_two_dvd_card_centralizer_of_sixTwelve (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : p ∣ (2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1 ∨
      p ∣ (2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 + 1)
    (x : Γ₀) (hx : orderOf x = p) :
    ¬ 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set Γ₀)) := by
  classical
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have hq : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqp : ¬ p ∣ 2 ^ (2 * a + 1) := fun hd =>
    absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)) (by omega)
  obtain ⟨hz, ht⟩ := not_dvd_involution_centralizer_orders hp hp3 hq hqp h
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({x} : Set Γ₀))
    2 h2
  have hyc := (y : Subgroup.centralizer ({x} : Set Γ₀)).2
  set g : ModGL ReeTag.F4.tag K := (((y : Subgroup.centralizer ({x} : Set Γ₀)) : Γ₀) :
    ModGL ReeTag.F4.tag K) with hg
  have hgΓ : g ∈ Γ₀ := ((y : Subgroup.centralizer ({x} : Set Γ₀)) : Γ₀).2
  have hy2 : ((y : Subgroup.centralizer ({x} : Set Γ₀)) : Γ₀) ^ 2 = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy] at this
    exact congrArg Subtype.val this
  have hg2 : g ^ 2 = 1 := by
    have := congrArg (fun z : Γ₀ => (z : ModGL ReeTag.F4.tag K)) hy2
    simpa using this
  have hg1 : g ≠ 1 := by
    intro h1
    have h1' : ((y : Subgroup.centralizer ({x} : Set Γ₀)) : Γ₀) = 1 := Subtype.ext h1
    have : y = 1 := Subtype.ext h1'
    rw [this, orderOf_one] at hy
    omega
  have hxg : (x : ModGL ReeTag.F4.tag K) * g = g * (x : ModGL ReeTag.F4.tag K) := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hyc
    exact congrArg Subtype.val this.symm
  have hxp : orderOf (x : ModGL ReeTag.F4.tag K) = p := by rw [Subgroup.orderOf_coe, hx]
  obtain ⟨hfus, -⟩ := large_Ree_every_involution_fuses a ha K hK
  have hcard := large_Ree_two_involution_centralizers a ha K hK
  rcases hfus g hgΓ hg2 hg1 with ⟨u, hu, hug⟩ | ⟨u, hu, hug⟩
  · rw [sylowH_zero_eq_centralZ] at hug
    have hd := dvd_card_inf_centralizer_of_conj (p := p) hu hug x.2 hxg hxp
    rw [hcard.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at hd
    exact hz hd
  · have hd := dvd_card_inf_centralizer_of_conj (p := p) hu hug x.2 hxg hxp
    rw [hcard.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at hd
    exact ht hd

end Main

end CFSG.RankThree.PartOne.KLR

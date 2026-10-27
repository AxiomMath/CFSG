module

public import CFSG.RankThree.PartOne.S12.Sec12Fus
public import CFSG.RankThree.PartOne.S11d.FieldCase

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

variable {G : Type} [Group G]

namespace Sec12Fus

theorem p_dvd_center_card {K : Subgroup G} {x : G} (hxK : x ∈ K) (hx : ∀ y ∈ K, x * y = y * x)
    {p : ℕ} (hord : orderOf x = p) : p ∣ Nat.card (Subgroup.center ↥K) := by
  have hz : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (hx y y.2).symm
  set z : ↥(Subgroup.center ↥K) := ⟨⟨x, hxK⟩, hz⟩ with hzdef
  have hdvd : orderOf z ∣ Nat.card ↥(Subgroup.center ↥K) := orderOf_dvd_natCard z
  have h1 : orderOf z = orderOf (⟨x, hxK⟩ : ↥K) := (Subgroup.orderOf_coe z).symm
  have h2 : orderOf (⟨x, hxK⟩ : ↥K) = orderOf x := (Subgroup.orderOf_coe (⟨x, hxK⟩ : ↥K)).symm
  rw [h1, h2, hord] at hdvd
  exact hdvd

end Sec12Fus

theorem node1213Field_of_inputs
    (h112 : InSec11Two) (hLS : FieldAutCoset) : Node1213Field := by
  classical
  intro G _ _ p A c L E ctx b K I X P Q hL hC hne hcomm hmax htwo
  have h := ctx.hyp
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h3 := h.three_lt
    by_contra hlt
    have h4 : p = 4 := by omega
    exact absurd (h4 ▸ hp) (by decide)
  have hAel := h.A_elem
  have hApow : ∀ x ∈ A, x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) x hx
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, Commute x y := fun x hx y hy => by
    have := hAel.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  obtain ⟨hbA, hbL, hb1⟩ := hL.b_mem
  have hIθ : I ∈ thetaComponentsAt p b := hL.I_mem
  have hIb : I ≤ Subgroup.centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.mp hIθ).1
  obtain ⟨hEven, hZ, a, d, haA, hdA, hd1, hAeq, hdI, hfa⟩ :=
    h112 G p A h.setup b hbA hb1 I ⟨⟨hmax.1, htwo⟩, hmax.2⟩
  have hdp : d ^ p = 1 := hApow d hdA
  have hdord : orderOf d = p := orderOf_eq_prime hdp hd1
  have hKAI : A ⊓ K = A ⊓ I := by
    have hle : A ⊓ K ≤ A ⊓ I := inf_le_inf_left A hL.K_le
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hL.A_K, ← hdI, Nat.card_zpowers, hdord]
  have hdAI : d ∈ A ⊓ I := hdI ▸ Subgroup.mem_zpowers d
  have hdI' : d ∈ I := hdAI.2
  have hdK : d ∈ K := by
    have : d ∈ A ⊓ K := hKAI ▸ hdAI
    exact this.2
  have hc : c ∉ Subgroup.zpowers b ⊔ Subgroup.zpowers d := by
    intro hcmem
    obtain ⟨j, k, hjk⟩ := (S11d.mem_zpowers_sup_zpowers_iff (hAcomm b hbA d hdA)).1 hcmem
    have hbCAK : b ∈ A ⊓ Subgroup.centralizer (K : Set G) := by
      rw [hL.C_A]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
    have hcCAK : c ∈ A ⊓ Subgroup.centralizer (K : Set G) := by
      rw [hL.C_A]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
    have hdk : d ^ k = (b ^ j)⁻¹ * c := by rw [hjk]; group
    have hdkC : d ^ k ∈ Subgroup.centralizer (K : Set G) := by
      rw [hdk]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hbCAK.2 j)) hcCAK.2
    have hdkK : d ^ k ∈ K := Subgroup.zpow_mem _ hdK k
    have hdkpow : (d ^ k) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdp, one_zpow]
    by_cases hdk1 : d ^ k = 1
    · have : c = b ^ j := by rw [hjk, hdk1, mul_one]
      exact ctx.c_not_mem (this ▸ Subgroup.zpow_mem _ hbL j)
    · have hord : orderOf (d ^ k) = p := orderOf_eq_prime hdkpow hdk1
      exact hL.K_center (Sec12Fus.p_dvd_center_card hdkK
        (fun y hy => (Subgroup.mem_centralizer_iff.1 hdkC y hy).symm) hord)
  have hcA : c ∈ A := h.c_mem
  have hcomm_d : ∀ β ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b, Commute β d := by
    intro β hβ
    have hβA : β ∈ A := by
      rw [hAeq]
      exact Subgroup.mem_sup_left hβ
    exact hAcomm β hβA d hdA
  have hcmem : c ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers d := by
    rw [← hAeq]
    exact hcA
  obtain ⟨β, hβ, k, hck⟩ := (S11d.mem_sup_zpowers_iff hcomm_d).mp hcmem
  obtain ⟨i, j, hij⟩ := (S11d.mem_zpowers_sup_zpowers_iff (hAcomm a haA b hbA)).mp hβ
  have hap : a ^ p = 1 := hApow a haA
  have hi : ¬ (p : ℤ) ∣ i := by
    intro hdiv
    obtain ⟨m, hm⟩ := hdiv
    apply hc
    have h1 : a ^ i = 1 := by rw [hm, zpow_mul, zpow_natCast, hap, one_zpow]
    have : c = b ^ j * d ^ k := by rw [hck, hij, h1, one_mul]
    rw [this]
    exact Subgroup.mul_mem_sup (zpow_mem (Subgroup.mem_zpowers b) j)
      (zpow_mem (Subgroup.mem_zpowers d) k)
  have hq : CFSG.IsQuasisimple ↥I :=
    S11d.isQuasisimple_of_evenLie (isPerfect_of_mem_thetaComponentsAt hIθ) hEven
  have hdkI : d ^ k ∈ I := zpow_mem hdI' k
  have hdkp : (d ^ k) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdp, one_zpow]
  have hadk : a * d ^ k = d ^ k * a :=
    (Commute.zpow_right (hAcomm a haA d hdA) k).eq
  have hbp : b ^ p = 1 := hApow b hbA
  have hbC : b ∈ Subgroup.centralizer (I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp (hIb hg)
  have hrank : FieldAutRank p I a :=
    ⟨h.evenRank_eq.le, b, hbC, hb1, hbp, (hAcomm a haA b hbA).eq⟩
  have hind := hLS G p I a (d ^ k) hp hp5 hq hEven hZ hfa hap hrank hdkI hdkp hadk i hi
  have hz : b ^ j ∈ Subgroup.centralizer (I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hgb : g * b = b * g := Subgroup.mem_centralizer_singleton_iff.mp (hIb hg)
    exact ((Commute.zpow_right (show Commute g b from hgb) j).eq)
  have hbd : b ^ j * d ^ k = d ^ k * b ^ j :=
    ((hAcomm b hbA d hdA).zpow_zpow j k).eq
  have hceq : c = a ^ i * d ^ k * b ^ j := by
    rw [hck, hij, mul_assoc, hbd, ← mul_assoc]
  have hcp : c ^ p = 1 := hApow c hcA
  rw [hceq]
  refine hind.mul_centralizer hz ?_
  rw [← hceq, hcp]
  exact Subgroup.one_mem _

end CFSG.RankThree.PartOne

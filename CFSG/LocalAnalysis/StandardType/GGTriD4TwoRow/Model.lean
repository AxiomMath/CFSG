module

public import Certificates.Certificate707010
public import CFSG.Quasithin.Recognition.CertTriality

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434D42

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.Quasithin CFSG.AGLEmbedding.D4Two
  CFSG.AGLEmbedding.ChevOuter CFSG.StandardType.TriD4TwoRow

theorem d4Phi_facts :
    (∀ i : Fin 2457, lineCert.pts[(d4Phi i : ℕ)]! = frobCode lineCert.pts[(i : ℕ)]!) ∧
      Rep 2457 (phiArr ()) d4Phi ∧ d4Phi ^ 3 = 1 ∧
      ∀ k < 18,
        d4Phi * d4Rho (letterX k) = d4Rho (letterX (sg k)) * d4Phi :=
  Certificates.certificate707010

theorem d4Phi_pow_three : d4Phi ^ 3 = 1 :=
  d4Phi_facts.2.2.1

theorem d4Phi_mul_letter {k : ℕ}
    (hk : k < 18) : d4Phi * d4Rho (letterX k) = d4Rho (letterX (sg k)) * d4Phi :=
  d4Phi_facts.2.2.2 k hk

theorem d4Phi_conj_d4Rho
    (g : lineGroup) : d4Phi * d4Rho g * d4Phi⁻¹ = d4Rho (phiT g) := by
  obtain ⟨x, hx⟩ := g
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, rfl⟩ := hy
    have hk' : k < 18 := hk
    have hg : (⟨letterGL k, Subgroup.subset_closure ⟨k, hk, rfl⟩⟩ : lineGroup) = letterX k := by
      apply Subtype.ext
      simp [letterX, hk']
    rw [hg, phiT_letterX k hk', d4Phi_mul_letter hk', mul_inv_cancel_right]
  | one =>
    have h1 : (⟨1, Subgroup.one_mem _⟩ : lineGroup) = 1 := rfl
    rw [h1, map_one, map_one, mul_one, mul_inv_cancel, map_one]
  | mul y z hy hz ihy ihz =>
    have h1 : (⟨y * z, Subgroup.mul_mem _ hy hz⟩ : lineGroup) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
    rw [h1, map_mul, map_mul, map_mul, ← ihy, ← ihz]
    group
  | inv y hy ihy =>
    have h1 : (⟨y⁻¹, Subgroup.inv_mem _ hy⟩ : lineGroup) = (⟨y, hy⟩ : lineGroup)⁻¹ := rfl
    rw [h1, map_inv, map_inv, map_inv, ← ihy]
    group

theorem d4Phi_conj_mem
    {y : Equiv.Perm (Fin 2457)} (hy : y ∈ d4P) :
    d4Phi * y * d4Phi⁻¹ ∈ d4P := by
  rw [← d4Rho_range] at hy ⊢
  obtain ⟨g, rfl⟩ := hy
  exact ⟨phiT g, (d4Phi_conj_d4Rho g).symm⟩

theorem card_lineGroup : Nat.card lineGroup = 211341312 := by
  rw [lineGroup_eq]
  exact card_trialityGroup8

theorem d4Phi_not_inner :
    ¬ ∃ x ∈ d4P, ∀ y ∈ d4P, d4Phi * y * d4Phi⁻¹ = x * y * x⁻¹ := by
  rintro ⟨x, hx, hxy⟩
  rw [← d4Rho_range] at hx
  obtain ⟨g, rfl⟩ := hx
  apply phiT_ne_conj g
  refine MulEquiv.ext fun h => d4Rho_injective card_lineGroup ?_
  rw [← d4Phi_conj_d4Rho, hxy (d4Rho h) (d4Rho_mem h), MulAut.conj_apply, map_mul, map_mul,
    map_inv]

theorem d4Phi_not_mem :
    d4Phi ∉ d4P :=
  fun h => d4Phi_not_inner ⟨d4Phi, h, fun _ _ => rfl⟩

@[expose] noncomputable def d4G : Subgroup (Equiv.Perm (Fin 2457)) :=
  Subgroup.zpowers d4Phi ⊔ d4P

theorem d4P_le_d4G : d4P ≤ d4G := le_sup_right

theorem d4Phi_mem_d4G : d4Phi ∈ d4G := Subgroup.mem_sup_left (Subgroup.mem_zpowers d4Phi)

theorem zpowers_d4Phi_le_normalizer :
    Subgroup.zpowers d4Phi ≤ Subgroup.normalizer (d4P : Set (Equiv.Perm (Fin 2457))) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => d4Phi_conj_mem hy, fun hy => ?_⟩
  have h2 := d4Phi_conj_mem (d4Phi_conj_mem hy)
  have h3' : d4Phi * d4Phi * d4Phi = 1 := by rw [← d4Phi_pow_three, pow_three, mul_assoc]
  have e : d4Phi * (d4Phi * (d4Phi * y * d4Phi⁻¹) * d4Phi⁻¹) * d4Phi⁻¹ = y := by
    calc d4Phi * (d4Phi * (d4Phi * y * d4Phi⁻¹) * d4Phi⁻¹) * d4Phi⁻¹ =
          (d4Phi * d4Phi * d4Phi) * y * (d4Phi * d4Phi * d4Phi)⁻¹ := by group
      _ = y := by rw [h3']; group
  rw [← e]
  exact h2

theorem card_zpowers_d4Phi :
    Nat.card (Subgroup.zpowers d4Phi) = 3 := by
  rw [Nat.card_zpowers]
  refine orderOf_eq_prime d4Phi_pow_three fun h1 => d4Phi_not_mem ?_
  rw [h1]
  exact d4P.one_mem

theorem zpowers_d4Phi_inf :
    (d4P.subgroupOf (Subgroup.zpowers d4Phi)) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := card_zpowers_d4Phi
  have hdvd : Nat.card (d4P.subgroupOf (Subgroup.zpowers d4Phi)) ∣ 3 :=
    hcard ▸ Subgroup.card_subgroup_dvd_card _
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    have htop : d4P.subgroupOf (Subgroup.zpowers d4Phi) = ⊤ :=
      Subgroup.card_eq_iff_eq_top _ |>.mp (by rw [h3, hcard])
    apply d4Phi_not_mem
    have hmem : (⟨d4Phi, Subgroup.mem_zpowers d4Phi⟩ : Subgroup.zpowers d4Phi) ∈
        d4P.subgroupOf (Subgroup.zpowers d4Phi) := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem

theorem d4P_normal_d4G :
    (d4P.subgroupOf d4G).Normal :=
  Subgroup.normal_subgroupOf_sup_of_le_normalizer zpowers_d4Phi_le_normalizer

theorem index_d4P_d4G :
    (d4P.subgroupOf d4G).index = 3 := by
  have hLE := zpowers_d4Phi_le_normalizer
  let := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  let := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient (Subgroup.zpowers d4Phi) d4P hLE
  unfold d4G
  rw [Subgroup.index, ← Nat.card_congr e.toEquiv, ← Subgroup.index, zpowers_d4Phi_inf,
    Subgroup.index_bot, card_zpowers_d4Phi]

theorem card_d4G :
    Nat.card d4G = 634023936 := by
  have h := (d4P.subgroupOf d4G).card_mul_index
  rw [index_d4P_d4G, Nat.card_congr (Subgroup.subgroupOfEquivOfLe d4P_le_d4G).toEquiv,
    card_d4P] at h
  omega

theorem conj_mem_d4P
    {g y : Equiv.Perm (Fin 2457)} (hg : g ∈ d4G) (hy : y ∈ d4P) :
    g * y * g⁻¹ ∈ d4P := by
  have := d4P_normal_d4G
  have h := this.conj_mem ⟨y, d4P_le_d4G hy⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨g, hg⟩
  exact Subgroup.mem_subgroupOf.mp h

theorem conj_not_mem_d4P
    {g y : Equiv.Perm (Fin 2457)} (hg : g ∈ d4G) (hy : y ∉ d4P) :
    g * y * g⁻¹ ∉ d4P := by
  intro h
  apply hy
  have := conj_mem_d4P (d4G.inv_mem hg) h
  simpa [mul_assoc] using this

end CFSG.RankThree.PartTwo.Sec4.Item434D42

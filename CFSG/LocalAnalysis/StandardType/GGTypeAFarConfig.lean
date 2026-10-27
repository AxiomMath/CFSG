module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestBlocks
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Facts

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {n f : ℕ} {y : G} {K : Subgroup G}

theorem GGTypeANbrCfg.prime (hN : GGTypeANbrCfg p B Bs x L D J n f y K) : p.Prime := by
  obtain ⟨⟨hI, -, -⟩, -, -, -, -⟩ := hN
  exact hI.2.2.2.2.2.1.1

theorem GGTypeANbrCfg.exponent (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    ∀ b ∈ Bs, b ^ p = 1 := by
  obtain ⟨⟨-, hBs, -⟩, -, -, -, -⟩ := hN
  exact hBs.2.1.2

theorem GGTypeANbrCfg.bs_centralizer (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := by
  obtain ⟨⟨-, hBs, -⟩, -, -, -, -⟩ := hN
  exact hBs.2.2.2

theorem GGTypeANbrCfg.x_mem (hN : GGTypeANbrCfg p B Bs x L D J n f y K) : x ∈ Bs := by
  obtain ⟨⟨hI, hBs, -⟩, -, -, -, -⟩ := hN
  exact hBs.1 hI.2.2.2.2.2.2.1.2.1

theorem GGTypeANbrCfg.y_mem (hN : GGTypeANbrCfg p B Bs x L D J n f y K) : y ∈ Bs := by
  obtain ⟨⟨-, hBs, -⟩, -, -, -, htypeA⟩ := hN
  obtain ⟨-, -, -, -, hnbr, -⟩ := htypeA
  exact hBs.1 hnbr.1.2.1

theorem GGTypeANbrCfg.y_ne_one (hN : GGTypeANbrCfg p B Bs x L D J n f y K) : y ≠ 1 := by
  obtain ⟨-, -, -, -, htypeA⟩ := hN
  obtain ⟨-, -, -, -, hnbr, -⟩ := htypeA
  exact hnbr.1.2.2.1

theorem GGTypeANbrCfg.x_comm_of_mem_L (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    ∀ l ∈ L, x * l = l * x := by
  obtain ⟨⟨hI, -, -⟩, -, -, -, -⟩ := hN
  intro l hl
  exact (Subgroup.mem_centralizer_singleton_iff.mp
    (hI.2.2.2.2.2.2.1.2.2.2.1.1 hl)).symm

theorem GGTypeANbrCfg.y_comm_of_mem_K (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    ∀ k ∈ K, y * k = k * y := by
  obtain ⟨-, -, -, -, htypeA⟩ := hN
  obtain ⟨-, -, -, -, hnbr, -⟩ := htypeA
  intro k hk
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hnbr.1.2.2.2.1 hk)).symm

theorem GGTypeANbrCfg.not_x_comm_K (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    ¬ ∀ k ∈ K, x * k = k * x := by
  obtain ⟨-, -, -, -, htypeA⟩ := hN
  obtain ⟨-, -, -, -, hnbr, -⟩ := htypeA
  intro hcomm
  apply hnbr.2.2.2
  have hbot : (⁅K, Subgroup.zpowers x⁆ : Subgroup G) = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hcomm k hk).symm
  rw [hbot]
  exact bot_le

theorem GGTypeANbrCfg.mem_zpowers_x_of_comm_L (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    ∀ g ∈ Bs, (∀ l ∈ L, g * l = l * g) → g ∈ Subgroup.zpowers x := by
  obtain ⟨⟨hI, hBs, -⟩, -, -, -, -⟩ := hN
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have hSstar := hI.2.2.2.2.2.2.1
  have hxne : x ≠ 1 := hSstar.2.2.1
  have hxBs : x ∈ Bs := hBs.1 hSstar.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSstar.2.2.2.1.1
  have hxpow : x ^ p = 1 := hBs.2.1.2 x hxBs
  have hxord : orderOf x = p := by
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hxpow hxne
  intro g hg hgc
  let S : Subgroup G := Bs ⊓ Subgroup.centralizer (L : Set G)
  have hxS : x ∈ S := ⟨hxBs, Subgroup.mem_centralizer_iff.mpr (fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLx hl))⟩
  have hgS : g ∈ S := ⟨hg, Subgroup.mem_centralizer_iff.mpr (fun l hl =>
    (hgc l hl).symm)⟩
  have hSp : IsPGroup p ↥S := fun s => ⟨1, by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    exact hBs.2.1.2 (s : G) s.2.1⟩
  have hScyc : IsCyclic ↥S := hSstar.2.2.2.2 S inf_le_right hSp
  obtain ⟨s, hs⟩ := hScyc.exists_generator
  have hmap : (Subgroup.zpowers s).map S.subtype = Subgroup.zpowers (s : G) :=
    MonoidHom.map_zpowers S.subtype s
  have hSeq : S = Subgroup.zpowers (s : G) := by
    apply le_antisymm
    · intro y hy
      have hy' : y ∈ (Subgroup.zpowers s).map S.subtype :=
        ⟨⟨y, hy⟩, hs ⟨y, hy⟩, rfl⟩
      rwa [hmap] at hy'
    · rw [Subgroup.zpowers_le]
      exact s.2
  have hs_pow : s ^ p = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    exact hBs.2.1.2 (s : G) s.2.1
  have hsord_dvd : orderOf s ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hs_pow
  have hsord : orderOf s = p := by
    rcases (Nat.dvd_prime hp).mp hsord_dvd with h1 | hp'
    · exfalso
      have hs1 : s = 1 := orderOf_eq_one_iff.mp h1
      have hxmem : (⟨x, hxS⟩ : S) ∈ Subgroup.zpowers s := hs ⟨x, hxS⟩
      rw [hs1] at hxmem
      have hxe : (⟨x, hxS⟩ : S) = 1 := by simpa using hxmem
      exact hxne (Subtype.ext_iff.mp hxe)
    · exact hp'
  have hcardS : Nat.card S = p := by
    have hord : orderOf (s : G) = orderOf s :=
      orderOf_injective S.subtype Subtype.coe_injective s
    rw [hSeq, Nat.card_zpowers, hord, hsord]
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hxord]
  have hzxle : Subgroup.zpowers x ≤ S := Subgroup.zpowers_le.mpr hxS
  have heq : Subgroup.zpowers x = S :=
    Subgroup.eq_of_le_of_card_ge hzxle (by rw [hcardS, hcardx])
  rw [heq]
  exact hgS

theorem GGTypeANbrCfg.eq_one_of_comm_L_K (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    ∀ g ∈ Bs, (∀ l ∈ L, g * l = l * g) → (∀ k ∈ K, g * k = k * g) → g = 1 := by
  have hNc := hN
  obtain ⟨⟨hI, hBs, -⟩, -, -, -, -⟩ := hNc
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have hSstar := hI.2.2.2.2.2.2.1
  have hxne : x ≠ 1 := hSstar.2.2.1
  have hxpow : x ^ p = 1 := hBs.2.1.2 x (hBs.1 hSstar.2.1)
  have hxord : orderOf x = p := by
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hxpow hxne
  intro g hg hgL hgK
  by_contra hgne
  have hgzx : g ∈ Subgroup.zpowers x :=
    GGTypeANbrCfg.mem_zpowers_x_of_comm_L hN g hg hgL
  have hxmem : x ∈ Subgroup.zpowers g := by
    have hle : Subgroup.zpowers g ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hgzx
    have hgpow : g ^ p = 1 := hBs.2.1.2 g hg
    have hgord : orderOf g = p := by
      have : Fact p.Prime := ⟨hp⟩
      exact orderOf_eq_prime hgpow hgne
    have hcardg : Nat.card (Subgroup.zpowers g) = p := by rw [Nat.card_zpowers, hgord]
    have hcardx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxord]
    have heq : Subgroup.zpowers g = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardx, hcardg])
    rw [heq]
    exact Subgroup.mem_zpowers x
  have hgcent : g ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hgK k hk).symm
  have hxcent : x ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hgcent hxmem
  exact GGTypeANbrCfg.not_x_comm_K hN (fun k hk =>
    (Subgroup.mem_centralizer_iff.mp hxcent k hk).symm)

theorem GGTypeANbrCfg.dvd_two_pow_sub_one (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    p ∣ 2 ^ f - 1 := by
  obtain ⟨-, -, -, -, htypeA⟩ := hN
  exact htypeA.2.1

theorem GGTypeANbrCfg.three_le (hN : GGTypeANbrCfg p B Bs x L D J n f y K) : 3 ≤ n := by
  obtain ⟨-, -, -, -, htypeA⟩ := hN
  exact htypeA.2.2.1

theorem GGTypeANbrCfg.one_le_f (hN : GGTypeANbrCfg p B Bs x L D J n f y K) : 1 ≤ f := by
  obtain ⟨-, -, -, -, htypeA⟩ := hN
  exact htypeA.1.1.2.1

theorem GGTypeANbrCfg.dvd_natCard_units (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    p ∣ Nat.card (GaloisField 2 f)ˣ := by
  obtain ⟨-, -, -, -, htypeA⟩ := hN
  have hf : 1 ≤ f := htypeA.1.1.2.1
  have hpq : p ∣ 2 ^ f - 1 := htypeA.2.1
  rw [Nat.card_units, GaloisField.card 2 f (by omega)]
  exact hpq

theorem GGTypeANbrCfg.four_le_natCard (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    4 ≤ Nat.card (GaloisField 2 f) := by
  have hNc := hN
  obtain ⟨-, -, -, -, htypeA⟩ := hNc
  have hp : p.Prime := GGTypeANbrCfg.prime hN
  have hf : 1 ≤ f := htypeA.1.1.2.1
  have hpq : p ∣ 2 ^ f - 1 := htypeA.2.1
  have hf2 : 2 ≤ f := by
    by_contra h
    have hf1 : f = 1 := by omega
    have hp_dvd_one : p ∣ 1 := by simpa [hf1] using hpq
    exact hp.ne_one (Nat.dvd_one.mp hp_dvd_one)
  have h4 : 4 ≤ 2 ^ f := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  rw [GaloisField.card 2 f (by omega)]
  exact h4

theorem GGTypeANbrCfg.pComponent_K (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K := by
  obtain ⟨-, -, -, -, htypeA⟩ := hN
  obtain ⟨-, -, -, -, hnbr, -⟩ := htypeA
  exact hnbr.1.2.2.2.2.1

theorem GGTypeANbrCfg.pComponent_L (hN : GGTypeANbrCfg p B Bs x L D J n f y K)
    (hpJ : p ∣ Nat.card J) :
    LargeEvenPComponent p (Subgroup.centralizer ({x} : Set G)) L := by
  obtain ⟨⟨hI, -, hDJ⟩, -, -, -, -⟩ := hN
  exact (eq_of_le_of_stdSub hI hDJ hpJ).2.1

end Facts

end CFSG.StandardType

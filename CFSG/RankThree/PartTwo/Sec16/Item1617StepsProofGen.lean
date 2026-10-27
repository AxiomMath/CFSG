module

public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofFus
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec16.Item16TailEnd
public import CFSG.RankThree.PartTwo.Sec14.Item1411Strong
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofCore
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
public import CFSG.RankThree.PartTwo.Sec16.Item16TailMore

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open scoped Pointwise

@[expose] def KS1620Gen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 ≤ n → ¬ 3 ∣ n → Sec4.IsoLThreePi X 2 n →
    ∀ D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 → ∀ b ∈ D, b ≠ 1 →
    ∀ p : ℕ, p.Prime → 3 < p →
    ∀ U V : Subgroup X, IsPGroup p U → IsPGroup p V → U ≠ ⊥ → V ≠ ⊥ →
      U ≤ Subgroup.centralizer ({b} : Set X) → V ≤ Subgroup.centralizer ({b} : Set X) →
      D ≤ Subgroup.normalizer (U : Set X) → D ≤ Subgroup.normalizer (V : Set X) →
      ∀ w ∈ Subgroup.normalizer (D : Set X), w * b * w⁻¹ ∉ Subgroup.zpowers b →
        3 ∣ Nat.card (U ⊔ V.map (MulAut.conj w).toMonoidHom : Subgroup X)

variable {G : Type} [Group G] [Finite G]

theorem step1620Gen_of (h138 : Item138N) (h1612 : Step1612) (h1619 : Step1619One)
    (hF : KS1617Fus) (hK : KS1620Gen) : Step1620Gen := by
  intro G _ _ A c L h _ b n p P hD X hX hX1 S _ hFr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : p.Prime := hD.prime
  have : Fact p.Prime := ⟨hp⟩
  have hz := hD.isZ3
  have hLs : IsSimpleGroup ↥L :=
    (Proof1619.simple_of_steps h (h1612 G A c L h) (h1619 G A c L h) hz.2.2).1
  have hn3 := Proof1617.not_three_dvd_of_isZ3 h h138 hz
  obtain ⟨hcL, h9, hAle⟩ := Proof1617.facts_of_isZ3 h hz
  have hXL := Proof1617.isoLThreePi_of_isSimpleGroup hLs hz.1 hz.2.1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := h.le_centralizer
  have hAeq := Proof1617.eq_zpowers_sup_inf h.mem_A hAle hLc
  have hCN := Proof1617.centralizer_le_normalizer_L h hz
  set D := A ⊓ L with hDdef
  have hDab : CFSG.Assembly.IsElemAbelian 3 D :=
    Proof169.isElemAbelian_of_le h.isElemAbelian inf_le_left
  have hbA : b ∈ A := hD.mem_A
  have hbL : b ∈ L := hD.mem_L
  have hbD : b ∈ D := ⟨hbA, hbL⟩
  have hb1 : b ≠ 1 := fun h1 => hD.not_mem (h1 ▸ Subgroup.one_mem _)
  have hb3 : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (h.isElemAbelian.2 b hbA) hb1
  obtain ⟨b', hb'D, hb'b⟩ : ∃ b' ∈ D, b' ∉ Subgroup.zpowers b := by
    by_contra hall
    push Not at hall
    have hle : D ≤ Subgroup.zpowers b := fun x hx => hall x hx
    have := Subgroup.card_le_of_le hle
    omega
  have hb'1 : b' ≠ 1 := fun h1 => hb'b (h1 ▸ Subgroup.one_mem _)
  obtain ⟨w, hwLN, hwb⟩ := hF G L D n hz.1 hn3 hz.2.1 inf_le_right hDab h9 b hbD hb1 b' hb'D hb'1
  have hwL : w ∈ L := (Subgroup.mem_inf.mp hwLN).1
  have hwD : w ∈ Subgroup.normalizer (D : Set G) := (Subgroup.mem_inf.mp hwLN).2
  have hwW : w ∈ Subgroup.normalizer (A : Set G) :=
    Proof1617.mem_normalizer_of_mem_normalizer_inf hAeq hLc hwLN
  have hNC : Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) :=
    inf_le_left.trans (Proof169.normalizer_le_normalizer_centralizer A)
  have hw' : w ∈ ((Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G) :
      Subgroup G) : Set G) * (Subgroup.centralizer (A : Set G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hNC]
    exact hFr hwW
  obtain ⟨w', hw'NS, k, hkC, hwk⟩ := hw'
  simp only at hwk
  have hXP : X ≤ P := hX.2
  have hPLb : P ≤ L ⊓ Subgroup.centralizer ({b} : Set G) := hD.mem_Q.1.2
  have hP2 : IsPGroup p P := (isPiSubgroup_piOf_iff hp P).mp hD.mem_Q.2
  have hXp : IsPGroup p X := hP2.to_le hXP
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX.1.1.2.2
  have hXL' : X ≤ L := hXP.trans (hPLb.trans inf_le_left)
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) := hXP.trans (hPLb.trans inf_le_right)
  have hki : k⁻¹ ∈ Subgroup.centralizer (A : Set G) := inv_mem hkC
  have hkiL : k⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
    refine hCN (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    exact (Subgroup.mem_centralizer_iff.mp hki c h.mem_A).symm
  set Y := X.map (MulAut.conj k⁻¹).toMonoidHom with hY
  have hYL : Y ≤ L := by
    rw [hY, ← Subgroup.mem_normalizer_iff_map_conj_eq.mp hkiL]
    exact Subgroup.map_mono hXL'
  have hkb : b * k⁻¹ = k⁻¹ * b := Subgroup.mem_centralizer_iff.mp hki b hbA
  have hkb' : k * b = b * k := by
    calc k * b = k * (b * k⁻¹) * k := by group
      _ = k * (k⁻¹ * b) * k := by rw [hkb]
      _ = b * k := by group
  have hYb : Y ≤ Subgroup.centralizer ({b} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyb : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.mp (hXb hy)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc k⁻¹ * y * k * b = k⁻¹ * y * (k * b) := by group
      _ = k⁻¹ * y * (b * k) := by rw [hkb']
      _ = k⁻¹ * (y * b) * k := by group
      _ = k⁻¹ * (b * y) * k := by rw [hyb]
      _ = (k⁻¹ * b) * y * k := by group
      _ = (b * k⁻¹) * y * k := by rw [hkb]
      _ = b * (k⁻¹ * y * k) := by group
  have hYp : IsPGroup p Y := hXp.map _
  have hY1 : Y ≠ ⊥ := by
    intro hbot
    apply hX1
    rw [hY, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj k⁻¹).injective] at hbot
    exact hbot
  have hDY : D ≤ Subgroup.normalizer (Y : Set G) := by
    intro d hdD
    have hdk : d * k⁻¹ = k⁻¹ * d := Subgroup.mem_centralizer_iff.mp hki d hdD.1
    have hdk' : d * k = k * d := by
      calc d * k = k * (k⁻¹ * d) * k := by group
        _ = k * (d * k⁻¹) * k := by rw [hdk]
        _ = k * d := by group
    refine Subgroup.mem_normalizer_fintype fun y' hy' => ?_
    obtain ⟨y, hy, rfl⟩ := hy'
    have hdy : d * y * d⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hAX hdD.1) y).mp hy
    refine ⟨d * y * d⁻¹, hdy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc k⁻¹ * (d * y * d⁻¹) * k = (k⁻¹ * d) * y * (d⁻¹ * k) := by group
      _ = (d * k⁻¹) * y * (k * d⁻¹) := by
          rw [← hdk]
          congr 1
          calc d⁻¹ * k = d⁻¹ * (k * d) * d⁻¹ := by group
            _ = d⁻¹ * (d * k) * d⁻¹ := by rw [hdk']
            _ = k * d⁻¹ := by group
      _ = d * (k⁻¹ * y * k) * d⁻¹ := by group
  have hw'eq : w' = w * k⁻¹ := by rw [← hwk]; group
  have hXw' : X.map (MulAut.conj w').toMonoidHom = Y.map (MulAut.conj w).toMonoidHom := by
    rw [hY, Late.map_conj_map_conj, hw'eq]
  set DX : Subgroup ↥L := D.subgroupOf L with hDX
  have hDXab : CFSG.Assembly.IsElemAbelian 3 DX := Proof1617.isElemAbelian_subgroupOf hDab L
  have hDX9 : Nat.card DX = 9 := by rw [Proof1617.card_subgroupOf_of_le inf_le_right, h9]
  set bX : ↥L := ⟨b, hbL⟩ with hbX
  set wX : ↥L := ⟨w, hwL⟩ with hwX
  set UX : Subgroup ↥L := X.subgroupOf L with hUX
  set VX : Subgroup ↥L := Y.subgroupOf L with hVX
  have hUXmap : UX.map L.subtype = X := by
    rw [hUX, Subgroup.subgroupOf_map_subtype, inf_of_le_left hXL']
  have hVXmap : VX.map L.subtype = Y := by
    rw [hVX, Subgroup.subgroupOf_map_subtype, inf_of_le_left hYL]
  have hcen : ∀ {Z : Subgroup G}, Z ≤ Subgroup.centralizer ({b} : Set G) →
      Z.subgroupOf L ≤ Subgroup.centralizer ({bX} : Set ↥L) := by
    intro Z hZ z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hZ (Subgroup.mem_subgroupOf.mp hz))
  have hnorm : ∀ {Z : Subgroup G}, D ≤ Subgroup.normalizer (Z : Set G) →
      DX ≤ Subgroup.normalizer ((Z.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro Z hZ d hd
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hZ (Subgroup.mem_subgroupOf.mp hd)) z
  have hne : ∀ {Z : Subgroup G}, Z ≤ L → Z ≠ ⊥ → Z.subgroupOf L ≠ ⊥ := by
    intro Z hZL hZ1 hbot
    apply hZ1
    rw [← inf_of_le_left hZL, ← Subgroup.subgroupOf_map_subtype, hbot, Subgroup.map_bot]
  have hwXD : wX ∈ Subgroup.normalizer (DX : Set ↥L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [hwX, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hwD z
  have hwXb : wX * bX * wX⁻¹ ∉ Subgroup.zpowers bX := by
    intro hmem
    apply hb'b
    obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k', ?_⟩
    have := congrArg Subtype.val hk'
    simp only [hbX, hwX, Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow] at this
    rw [this, hwb]
  have h3 := hK ↥L n hz.1 hn3 hXL DX hDXab hDX9 bX (Subgroup.mem_subgroupOf.mpr hbD)
    (fun h1 => hb1 (congrArg Subtype.val h1)) p hp hD.three_lt UX VX
    hXp.comap_subtype hYp.comap_subtype (hne hXL' hX1) (hne hYL hY1) (hcen hXb) (hcen hYb)
    (hnorm (inf_le_left.trans hAX)) (hnorm hDY) wX hwXD hwXb
  have hmapeq : (UX ⊔ VX.map (MulAut.conj wX).toMonoidHom).map L.subtype =
      X ⊔ Y.map (MulAut.conj w).toMonoidHom := by
    rw [Subgroup.map_sup, hUXmap]
    congr 1
    rw [← hVXmap, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have h3G : 3 ∣ Nat.card (X ⊔ Y.map (MulAut.conj w).toMonoidHom : Subgroup G) := by
    rw [← hmapeq, Subgroup.card_map_of_injective L.subtype_injective]
    exact h3
  set J := ⨆ v ∈ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G),
    X.map (MulAut.conj v).toMonoidHom with hJ
  have hXJ : X ≤ J := by
    have h1 : (1 : G) ∈ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (S : Set G) :=
      Subgroup.one_mem _
    have := le_iSup₂_of_le (f := fun v (_ : v ∈ Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (S : Set G)) => X.map (MulAut.conj v).toMonoidHom) 1 h1 le_rfl
    rwa [Late.map_conj_one] at this
  have hXw'J : X.map (MulAut.conj w').toMonoidHom ≤ J :=
    le_iSup₂_of_le (f := fun v (_ : v ∈ Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (S : Set G)) => X.map (MulAut.conj v).toMonoidHom) w' hw'NS le_rfl
  have hle : X ⊔ Y.map (MulAut.conj w).toMonoidHom ≤ J := sup_le hXJ (hXw' ▸ hXw'J)
  intro hO
  exact Sec14.not_three_dvd_of_oPrimeResidualOf_eq_bot hO
    (h3G.trans (Subgroup.card_dvd_of_le hle))

end CFSG.RankThree.PartTwo.Sec16

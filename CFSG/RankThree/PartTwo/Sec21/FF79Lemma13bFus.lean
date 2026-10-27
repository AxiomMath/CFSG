module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma13bSyl
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.L13b

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G]

theorem mem_cen_iff' {x z : G} : z ∈ Cen x ↔ z * x = x * z :=
  Subgroup.mem_centralizer_singleton_iff

theorem cen_conj_iff {b k : G} (hk : k * b * k⁻¹ = b ∨ k * b * k⁻¹ = b⁻¹) (z : G) :
    z ∈ Cen b ↔ k * z * k⁻¹ ∈ Cen b := by
  rw [mem_cen_iff', mem_cen_iff']
  change Commute z b ↔ Commute (k * z * k⁻¹) b
  have h1 : Commute z b ↔ Commute (k * z * k⁻¹) (k * b * k⁻¹) := by
    constructor
    · intro h
      simpa [MulAut.conj_apply] using h.map (MulAut.conj k)
    · intro h
      simpa [MulAut.conj_apply, mul_assoc] using h.map (MulAut.conj k⁻¹)
  rw [h1]
  rcases hk with hk | hk
  · rw [hk]
  · rw [hk, Commute.inv_right_iff]

theorem three_dvd_card_of_sylow {J : Subgroup G} [Finite G]
    (hSyl : ∀ P : Sylow 3 ↥J, IsElemAb 3 2 ((P : Subgroup ↥J).map J.subtype)) :
    3 ∣ Nat.card ↥J := by
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥J) := inferInstance
  have h9 : Nat.card ((P : Subgroup ↥J).map J.subtype) = 3 ^ 2 := (hSyl P).2
  rw [Subgroup.card_map_of_injective J.subtype_injective] at h9
  have hd : Nat.card (P : Subgroup ↥J) ∣ Nat.card ↥J := Subgroup.card_subgroup_dvd_card _
  rw [h9] at hd
  exact (dvd_pow_self 3 (by norm_num)).trans hd

theorem conj_mem_J {b : G} {J : Subgroup G} (hstd : FFStandardJ b J) (h3 : 3 ∣ Nat.card ↥J)
    {k : G} (hk : ∀ z, z ∈ Cen b ↔ k * z * k⁻¹ ∈ Cen b) {j : G} (hj : j ∈ J) :
    k * j * k⁻¹ ∈ J := by
  obtain ⟨hJC, hcomp, huniq⟩ := hstd
  let φ : ↥(Cen b) ≃* ↥(Cen b) :=
    { toFun := fun z => ⟨k * z * k⁻¹, (hk z).mp z.2⟩
      invFun := fun z => ⟨k⁻¹ * z * k, by
        rw [hk]
        have : k * (k⁻¹ * (z : G) * k) * k⁻¹ = z := by group
        rw [this]
        exact z.2⟩
      left_inv := fun z => Subtype.ext (by simp [mul_assoc])
      right_inv := fun z => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hcomp' := CFSG.LocalCores.isComponent_map_mulEquiv φ hcomp
  have hjC : j ∈ Cen b := hJC hj
  have hdvd : 3 ∣ Nat.card ↥(J.subgroupOf (Cen b)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv]
  have hdvd' : 3 ∣ Nat.card ↥((J.subgroupOf (Cen b)).map φ.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective φ.injective]
  have heq := huniq _ hcomp' hdvd'
  have hmem : φ ⟨j, hjC⟩ ∈ (J.subgroupOf (Cen b)).map φ.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨_, hj, rfl⟩
  rw [heq] at hmem
  exact hmem


section Fusion

variable [Finite G]

theorem exists_nor_conj {b : G} {B : Subgroup G} (hB : IsSylowOf 3 B (Cen b))
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) {y k : G} (hy : y ∈ B) (hk : k * b * k⁻¹ = y) :
    ∃ n ∈ Nor B, n * b * n⁻¹ = y := by
  have hCy : (Cen b).map (MulAut.conj k).toMonoidHom = Cen y := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwb : w * b = b * w := mem_cen_iff'.mp hw
      rw [mem_cen_iff']
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hk]
      calc k * w * k⁻¹ * (k * b * k⁻¹) = k * (w * b) * k⁻¹ := by group
        _ = k * (b * w) * k⁻¹ := by rw [hwb]
        _ = k * b * k⁻¹ * (k * w * k⁻¹) := by group
    · intro hz
      rw [mem_cen_iff', ← hk] at hz
      refine ⟨k⁻¹ * z * k, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
      show k⁻¹ * z * k ∈ Cen b
      rw [mem_cen_iff']
      calc (k⁻¹ * z * k) * b = k⁻¹ * (z * (k * b * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * b * k⁻¹) * z) * k := by rw [hz]
        _ = b * (k⁻¹ * z * k) := by group
  have hcardCy : Nat.card ↥(Cen y) = Nat.card ↥(Cen b) := by
    rw [← hCy, Subgroup.card_map_of_injective (MulAut.conj k).injective]
  have hBle : B ≤ Cen y := fun β hβ => mem_cen_iff'.mpr (hcomm β hβ y hy)
  have hDle : B.map (MulAut.conj k).toMonoidHom ≤ Cen y :=
    hCy ▸ Subgroup.map_mono hB.1
  have hBy : IsSylowOf 3 B (Cen y) :=
    isSylowOf_of_card hBle (by rw [isSylowOf_card hB, hcardCy])
  obtain ⟨h, hhC, hh⟩ := exists_conj_le_sylowOf hBy hDle (hB.2.1.map _)
  have hN : ∀ β ∈ B, h * k * β * (h * k)⁻¹ ∈ B := by
    intro β hβ
    have := hh (k * β * k⁻¹) ⟨β, hβ, by simp [MulAut.conj_apply]⟩
    simpa [mul_assoc] using this
  have hhy : h * y = y * h := mem_cen_iff'.mp hhC
  refine ⟨h * k, mem_nor_of_forall hN, ?_⟩
  calc h * k * b * (h * k)⁻¹ = h * (k * b * k⁻¹) * h⁻¹ := by group
    _ = h * y * h⁻¹ := by rw [hk]
    _ = y := by rw [hhy]; group

theorem exists_nor_move {b : G} {B : Subgroup G} (hb3 : orderOf b = 3)
    (hB : IsSylowOf 3 B (Cen b)) (hbB : b ∈ B) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hnsc : FFNotStronglyClosed b) :
    ∃ n ∈ Nor B, n * b * n⁻¹ ∈ B ∧ n * b * n⁻¹ ∉ Subgroup.zpowers b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx, g, hg1, hg2⟩ := hnsc
  have hx3 : x ^ 3 = 1 := by
    have hd : orderOf x ∣ 3 := hb3 ▸ orderOf_dvd_of_mem_zpowers hx
    exact orderOf_dvd_iff_pow_eq_one.mp hd
  have hx1 : x ≠ 1 := by
    intro h
    apply hg2
    rw [h]
    simpa using Subgroup.one_mem _
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hbx : b ∈ Subgroup.zpowers x := by
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers b := Subgroup.zpowers_le.mpr hx
    have hcard : Nat.card (Subgroup.zpowers b) ≤ Nat.card (Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hb3, hxo]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard) ▸ Subgroup.mem_zpowers b
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hbx
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
  set b' : G := g * b * g⁻¹ with hb'
  have hb'C : b' ∈ Cen b := by
    have : b' = (g * x * g⁻¹) ^ j := by
      rw [hb', ← hj, conj_zpow]
    rw [this]
    exact Subgroup.zpow_mem _ hg1 j
  have hb'nm : b' ∉ Subgroup.zpowers b := by
    intro hmem
    apply hg2
    have : g * x * g⁻¹ = b' ^ m := by
      rw [hb', ← hm, conj_zpow]
    rw [this]
    exact Subgroup.zpow_mem _ hmem m
  have hb3pow : b ^ 3 = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb3] at this
  have hb'3 : b' ^ 3 = 1 := by
    rw [hb', conj_pow, hb3pow]
    group
  have hb'1 : b' ≠ 1 := fun h => hb'nm (h ▸ Subgroup.one_mem _)
  have hb'o : orderOf b' = 3 := orderOf_eq_prime hb'3 hb'1
  have hp : IsPGroup 3 (Subgroup.zpowers b') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb'o]; norm_num)
  have hle : Subgroup.zpowers b' ≤ Cen b := Subgroup.zpowers_le.mpr hb'C
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_sylowOf hB hle hp
  have hyB : c * b' * c⁻¹ ∈ B := hc b' (Subgroup.mem_zpowers b')
  have hcb : c * b = b * c := mem_cen_iff'.mp hcC
  have hyk : (c * g) * b * (c * g)⁻¹ = c * b' * c⁻¹ := by rw [hb']; group
  obtain ⟨n, hn, hnb⟩ := exists_nor_conj hB hcomm hyB hyk
  refine ⟨n, hn, hnb ▸ hyB, ?_⟩
  rw [hnb]
  intro hmem
  apply hb'nm
  obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hcy : c * (c * b' * c⁻¹) = (c * b' * c⁻¹) * c := by
    rw [← hs]
    exact (Commute.zpow_right (show Commute c b from hcb) s).eq
  have h' : b' = c⁻¹ * (c * b' * c⁻¹) * c := by group
  rw [h', mul_assoc, ← hcy]
  simpa using hmem

end Fusion

end CFSG.RankThree.PartTwo.Sec21.FF79.L13b

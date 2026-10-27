module

public import CFSG.RankThree.PartTwo.Sec12.Hering129LOTwoL3Defs
public import Mathlib.GroupTheory.Sylow
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwoL3

open Subgroup

theorem lift_exists_zpow_mul {G : Type*} [Group G] {a b x : G} (hab : a * b = b * a)
    (hx : x ∈ zpowers a ⊔ zpowers b) : ∃ i j : ℤ, x = a ^ i * b ^ j := by
  have hc : ∀ i j : ℤ, b ^ j * a ^ i = a ^ i * b ^ j := fun i j =>
    (Commute.zpow_zpow hab i j).eq.symm
  let P : Subgroup G :=
    { carrier := {g | ∃ i j : ℤ, g = a ^ i * b ^ j}
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
        refine ⟨i + k, j + l, ?_⟩
        rw [zpow_add, zpow_add]
        calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by group
          _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [hc]
          _ = a ^ i * a ^ k * (b ^ j * b ^ l) := by group
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨-i, -j, ?_⟩
        rw [mul_inv_rev, ← zpow_neg, ← zpow_neg, hc] }
  have hle : zpowers a ⊔ zpowers b ≤ P := sup_le
    (zpowers_le.mpr ⟨1, 0, by simp⟩) (zpowers_le.mpr ⟨0, 1, by simp⟩)
  exact hle hx

theorem lift_isPGroup_three {G : Type*} [Group G] {x₁ x₂ : G} (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1)
    (hc : x₁ * x₂ = x₂ * x₁) : IsPGroup 3 (zpowers x₁ ⊔ zpowers x₂ : Subgroup G) := by
  intro x
  obtain ⟨i, j, hx⟩ := lift_exists_zpow_mul hc x.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, hx, (Commute.zpow_zpow hc i j).mul_pow,
    ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm i, mul_comm j, zpow_mul,
    zpow_mul, zpow_natCast, zpow_natCast, h1, h2, one_zpow, one_zpow, one_mul]
  rfl

theorem lift_exists_pGroup_map_eq {Y L : Type*} [Group Y] [Finite Y] [Group L] (φ : Y →* L)
    (hφ : Function.Surjective φ) {E : Subgroup L} (hE : IsPGroup 3 E) :
    ∃ B : Subgroup Y, IsPGroup 3 B ∧ B.map φ = E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M : Subgroup Y := E.comap φ with hM
  obtain ⟨P⟩ : Nonempty (Sylow 3 M) := inferInstance
  let ψ : M →* E := (φ.comp M.subtype).codRestrict E (fun y => y.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨e, he⟩
    obtain ⟨y, rfl⟩ := hφ e
    exact ⟨⟨y, he⟩, rfl⟩
  have hEtop : IsPGroup 3 (⊤ : Subgroup E) := hE.of_equiv Subgroup.topEquiv.symm
  have htop := ((P.mapSurjective hψ).is_maximal' hEtop le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  refine ⟨(P : Subgroup M).map M.subtype, P.isPGroup'.map _, ?_⟩
  ext x
  constructor
  · rintro ⟨_, ⟨y, -, rfl⟩, rfl⟩
    exact y.2
  · intro hx
    have hmem : (⟨x, hx⟩ : E) ∈ (P : Subgroup M).map ψ := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hmem
    exact ⟨y, ⟨y, hy, rfl⟩, congrArg Subtype.val hyx⟩


theorem lift_eq_of_map_eq {Y L : Type*} [Group Y] [Finite Y] [Group L] (φ : Y →* L)
    (h3 : ¬ 3 ∣ Nat.card φ.ker) {B : Subgroup Y} (hB : IsPGroup 3 B) {a c : Y} (ha : a ∈ B)
    (hc : c ∈ B) (h : φ a = φ c) : a = c := by
  have hmem : a * c⁻¹ ∈ B := mul_mem ha (inv_mem hc)
  have hker : a * c⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨k, hk⟩ := hB ⟨a * c⁻¹, hmem⟩
  have hk' : (a * c⁻¹) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd1 : orderOf (a * c⁻¹) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hdvd2 : orderOf (a * c⁻¹) ∣ Nat.card φ.ker := by
    have := orderOf_dvd_natCard (⟨a * c⁻¹, hker⟩ : φ.ker)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (3 ^ k) (Nat.card φ.ker) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  have h1 : orderOf (a * c⁻¹) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have : a * c⁻¹ = 1 := orderOf_eq_one_iff.mp h1
  exact mul_inv_eq_one.mp this

theorem lift_exists_mem_normalizer {Y L : Type*} [Group Y] [Finite Y] [Group L] (φ : Y →* L)
    (hφ : Function.Surjective φ) (h3 : ¬ 3 ∣ Nat.card φ.ker) {B : Subgroup Y} (hB : IsPGroup 3 B)
    {n : L} (hn : n ∈ normalizer ((B.map φ : Subgroup L) : Set L)) :
    ∃ m ∈ normalizer (B : Set Y), φ m = n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (IsPGroup 3 B) := ⟨hB⟩
  have hcop : Nat.Coprime 3 (Nat.card φ.ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hFr := CFSG.normalizer_map_quotient_eq_map_normalizer 3 B φ.ker (MonoidHom.normal_ker φ)
    hcop
  simp only at hFr
  set e := QuotientGroup.quotientKerEquivOfSurjective φ hφ with he
  have h1 : (B.map (QuotientGroup.mk' φ.ker)).map e.toMonoidHom = B.map φ := by
    rw [Subgroup.map_map]
    congr 1
  have h2 := Subgroup.map_equiv_normalizer_eq (B.map (QuotientGroup.mk' φ.ker)) e
  rw [h1] at h2
  have hn' : n ∈ (normalizer (B.map (QuotientGroup.mk' φ.ker) : Set _)).map e.toMonoidHom := by
    rw [h2]
    exact hn
  obtain ⟨n', hn'N, hn'e⟩ := hn'
  rw [hFr] at hn'N
  obtain ⟨m, hm, hmq⟩ := hn'N
  refine ⟨m, hm, ?_⟩
  rw [← hn'e, ← hmq]
  rfl


theorem lift_conj_mem {L : Type*} [Group L] {x₁ x₂ n : L} (hc : x₁ * x₂ = x₂ * x₁)
    (h1 : n * x₁ * n⁻¹ ∈ (zpowers x₁ ⊔ zpowers x₂ : Subgroup L))
    (h2 : n * x₂ * n⁻¹ ∈ (zpowers x₁ ⊔ zpowers x₂ : Subgroup L)) {x : L}
    (hx : x ∈ (zpowers x₁ ⊔ zpowers x₂ : Subgroup L)) :
    n * x * n⁻¹ ∈ (zpowers x₁ ⊔ zpowers x₂ : Subgroup L) := by
  obtain ⟨i, j, rfl⟩ := lift_exists_zpow_mul hc hx
  have e : n * (x₁ ^ i * x₂ ^ j) * n⁻¹ = (n * x₁ * n⁻¹) ^ i * (n * x₂ * n⁻¹) ^ j := by
    rw [conj_zpow, conj_zpow]
    group
  rw [e]
  exact mul_mem (zpow_mem h1 i) (zpow_mem h2 j)

theorem exists_lift_e9Q8 {Y L : Type} [Group Y] [Finite Y] [Group L] (φ : Y →* L)
    (hφ : Function.Surjective φ) (h3 : ¬ 3 ∣ Nat.card φ.ker) (hE : E9Q8 L) :
    ∃ b₁ b₂ h₁ h₂ : Y, φ b₁ ≠ 1 ∧ b₂ ∉ Subgroup.zpowers b₁ ∧ b₁ ^ 3 = 1 ∧ b₂ ^ 3 = 1 ∧
      b₁ * b₂ = b₂ * b₁ ∧ h₁ * b₁ * h₁⁻¹ = b₂⁻¹ ∧ h₁ * b₂ * h₁⁻¹ = b₁ ∧
      h₂ * b₁ * h₂⁻¹ = b₁⁻¹ * b₂⁻¹ ∧ h₂ * b₂ * h₂⁻¹ = b₁⁻¹ * b₂ ∧
      ∀ b ∈ Subgroup.closure ({b₁, b₂} : Set Y), φ b = 1 → b = 1 := by
  obtain ⟨x₁, x₂, n₁, n₂, hx₁, hx₂, hx12, hx1, hx2n, r11, r12, r21, r22⟩ := hE
  set E : Subgroup L := zpowers x₁ ⊔ zpowers x₂ with hEdef
  have hE3 : IsPGroup 3 E := lift_isPGroup_three hx₁ hx₂ hx12
  obtain ⟨B, hB3, hBE⟩ := lift_exists_pGroup_map_eq φ hφ hE3
  have hx₁E : x₁ ∈ E := mem_sup_left (mem_zpowers x₁)
  have hx₂E : x₂ ∈ E := mem_sup_right (mem_zpowers x₂)
  have hFin : Finite (E : Set L) := by
    rw [← hBE]
    exact Set.Finite.image _ (Set.toFinite _) |>.to_subtype
  rw [← hBE] at hx₁E hx₂E
  obtain ⟨b₁, hb₁B, hb₁x⟩ := hx₁E
  obtain ⟨b₂, hb₂B, hb₂x⟩ := hx₂E
  have hinj : ∀ {a c : Y}, a ∈ B → c ∈ B → φ a = φ c → a = c := fun ha hc h =>
    lift_eq_of_map_eq φ h3 hB3 ha hc h
  have hnorm : ∀ n : L, n * x₁ * n⁻¹ ∈ E → n * x₂ * n⁻¹ ∈ E → ∃ m ∈ normalizer (B : Set Y),
      φ m = n := by
    intro n hn1 hn2
    refine lift_exists_mem_normalizer φ hφ h3 hB3 ?_
    rw [hBE]
    exact Subgroup.mem_normalizer_fintype fun x hx => lift_conj_mem hx12 hn1 hn2 hx
  have hE1 : x₁ ∈ E := mem_sup_left (mem_zpowers x₁)
  have hE2 : x₂ ∈ E := mem_sup_right (mem_zpowers x₂)
  obtain ⟨h₁, hh₁N, hh₁⟩ := hnorm n₁ (by rw [r11]; exact inv_mem hE2) (by rw [r12]; exact hE1)
  obtain ⟨h₂, hh₂N, hh₂⟩ := hnorm n₂ (by rw [r21]; exact mul_mem (inv_mem hE1) (inv_mem hE2))
    (by rw [r22]; exact mul_mem (inv_mem hE1) hE2)
  have hconj : ∀ {h b : Y}, h ∈ normalizer (B : Set Y) → b ∈ B → h * b * h⁻¹ ∈ B := fun hh hb =>
    (Subgroup.mem_normalizer_iff.mp hh _).mp hb
  have hb₁inv : b₁⁻¹ ∈ B := inv_mem hb₁B
  have hb₂inv : b₂⁻¹ ∈ B := inv_mem hb₂B
  refine ⟨b₁, b₂, h₁, h₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb₁x]
    exact hx1
  · intro h
    apply hx2n
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← hb₁x, ← hb₂x, ← hk, map_zpow]⟩
  · exact hinj (pow_mem hb₁B 3) (one_mem B) (by rw [map_pow, hb₁x, hx₁, map_one])
  · exact hinj (pow_mem hb₂B 3) (one_mem B) (by rw [map_pow, hb₂x, hx₂, map_one])
  · exact hinj (mul_mem hb₁B hb₂B) (mul_mem hb₂B hb₁B) (by rw [map_mul, map_mul, hb₁x, hb₂x, hx12])
  · exact hinj (hconj hh₁N hb₁B) hb₂inv (by
      rw [map_mul, map_mul, map_inv, map_inv, hh₁, hb₁x, hb₂x, r11])
  · exact hinj (hconj hh₁N hb₂B) hb₁B (by
      rw [map_mul, map_mul, map_inv, hh₁, hb₂x, hb₁x, r12])
  · exact hinj (hconj hh₂N hb₁B) (mul_mem hb₁inv hb₂inv) (by
      rw [map_mul, map_mul, map_inv, hh₂, hb₁x, map_mul, map_inv, map_inv, hb₁x, hb₂x, r21])
  · exact hinj (hconj hh₂N hb₂B) (mul_mem hb₁inv hb₂B) (by
      rw [map_mul, map_mul, map_inv, hh₂, hb₂x, map_mul, map_inv, hb₁x, hb₂x, r22])
  · intro b hb hφb
    have hle : Subgroup.closure ({b₁, b₂} : Set Y) ≤ B := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hb₁B
      · exact hb₂B
    exact hinj (hle hb) (one_mem B) (by rw [hφb, map_one])

end CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwoL3

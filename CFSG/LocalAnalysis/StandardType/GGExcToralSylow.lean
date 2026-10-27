module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEMain
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

@[expose] def excWeylBound : Tag → ℕ
  | .G2 => 5
  | .F4 => 5
  | .D4 => 5
  | .E6 => 7
  | .E7 => 11
  | .E8 => 11

namespace ExcToralSylow

section Sylow

variable {τ : Tag} {K : Type} [Field K]

theorem ggExcToral_of_not_dvd_index [Finite K] {p : ℕ} (hp : p.Prime)
    (hidx : ¬ p ∣ ((torusGroup τ K).subgroupOf (adjointGroup τ K)).index)
    {A : Subgroup ↥(adjointGroup τ K)} (hA : IsPGroup p A) : GGExcToral τ K A := by
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  obtain ⟨g, hg⟩ := TableBF4.exists_conj_le_of_not_dvd_index hp hidx hA
  exact ⟨g, fun x hx => Subgroup.mem_subgroupOf.mp (hg ⟨x, hx, rfl⟩)⟩

theorem isPGroup_zpowers_of_pow_eq_one {L : Type*} [Group L] {p : ℕ} {a : L} (ha : a ^ p = 1) :
    IsPGroup p (Subgroup.zpowers a) :=
  IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one ha)

end Sylow

section Split


theorem not_dvd_index_of_splitCoprime {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) (hb : excWeylBound τ ≤ p) :
    ¬ p ∣ ((torusGroup τ K).subgroupOf (adjointGroup τ K)).index := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact TableBF4.not_dvd_index_torusGroup hp hb hpq
  · exact TableBExc.not_dvd_index_torusGroup_E6 hp hb hpq
  · exact TableBExc.not_dvd_index_torusGroup_E7 hp hb hpq
  · exact TableBExc.not_dvd_index_torusGroup_E8 hp hb hpq

theorem ggExcToral_of_splitCoprime {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) (hb : excWeylBound τ ≤ p) {A : Subgroup ↥(adjointGroup τ K)}
    (hA : IsPGroup p A) : GGExcToral τ K A :=
  ggExcToral_of_not_dvd_index hp (not_dvd_index_of_splitCoprime hτ hp hpq hb) hA

theorem ggExcToral_zpowers_of_splitCoprime {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1) (hb : excWeylBound τ ≤ p)
    {a : ↥(adjointGroup τ K)} (ha : a ^ p = 1) : GGExcToral τ K (Subgroup.zpowers a) :=
  ggExcToral_of_splitCoprime hτ hp hpq hb (isPGroup_zpowers_of_pow_eq_one ha)

end Split

section Inndiag

variable {K : Type} [Field K]

theorem range_conj_normal {L : Type*} [Group L] : (MulAut.conj : L →* MulAut L).range.Normal := by
  refine ⟨fun _ ⟨x, hx⟩ φ => ⟨φ x, ?_⟩⟩
  rw [← hx]
  refine MulEquiv.ext fun g => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem rootDiagAutHom_pow_three_mem_range_conj (a : Fin Tag.E6.rank → Kˣ) :
    rootDiagAutHom .E6 K a ^ 3 ∈
      (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)).range := by
  rw [← map_pow]
  have hmem : rootDiagUnit .E6 (a ^ 3) ∈ torusGroup .E6 K :=
    TableBExc.rootDiagUnit_cube_mem_torusGroup_E6 a
  exact ⟨⟨rootDiagUnit .E6 (a ^ 3), CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup hmem⟩,
    MulEquiv.ext fun g => Subtype.ext rfl⟩

theorem mem_range_conj_of_inndiag_E6 {α : MulAut ↥(adjointGroup .E6 K)}
    (hα : α ∈ LayerSixE.inndiagAut .E6 K) {m : ℕ} (hm : Nat.Coprime 3 m) (hαm : α ^ m = 1) :
    α ∈ (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)).range := by
  have := range_conj_normal (L := ↥(adjointGroup .E6 K))
  set N := (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K)).range with hN
  have hmem : α ∈ ((N : Set (MulAut ↥(adjointGroup .E6 K))) *
      ((rootDiagAutHom .E6 K).range : Set (MulAut ↥(adjointGroup .E6 K)))) := by
    rw [← Subgroup.normal_mul]
    exact hα
  obtain ⟨ι, hι, δ, ⟨a, rfl⟩, rfl⟩ := Set.mem_mul.mp hmem
  rw [← QuotientGroup.eq_one_iff (N := N)]
  have h1 : ((ι * rootDiagAutHom .E6 K a : MulAut ↥(adjointGroup .E6 K)) :
      MulAut ↥(adjointGroup .E6 K) ⧸ N) =
        (rootDiagAutHom .E6 K a : MulAut ↥(adjointGroup .E6 K) ⧸ N) := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff ι).mpr hι, one_mul]
  rw [h1]
  have hcube : (rootDiagAutHom .E6 K a : MulAut ↥(adjointGroup .E6 K) ⧸ N) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact rootDiagAutHom_pow_three_mem_range_conj a
  have hpow : (rootDiagAutHom .E6 K a : MulAut ↥(adjointGroup .E6 K) ⧸ N) ^ m = 1 := by
    rw [← h1, ← QuotientGroup.mk_pow, hαm, QuotientGroup.mk_one]
  have hcop : Nat.gcd 3 m = 1 := hm
  have h2 := pow_gcd_eq_one.mpr ⟨hcube, hpow⟩
  rwa [hcop, pow_one] at h2

theorem conj_eq_rootDiagAutHom {τ : Tag} {y : ↥(adjointGroup τ K)} {l : Fin τ.rank → Kˣ}
    (hl : (y : ModGL τ K) = rootDiagUnit τ l) : MulAut.conj y = rootDiagAutHom τ K l := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  change ((y * g * y⁻¹ : ↥(adjointGroup τ K)) : ModGL τ K) =
    rootDiagUnit τ l * (g : ModGL τ K) * (rootDiagUnit τ l)⁻¹
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hl]


theorem mulAut_conj_injective_adjoint [Finite K] {τ : Tag} :
    Function.Injective (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgc : g ∈ Subgroup.center ↥(adjointGroup τ K) := Subgroup.mem_center_iff.mpr fun x => by
    have h1 := congrArg (fun φ : MulAut ↥(adjointGroup τ K) => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc x * g = g * x * g⁻¹ * g := by rw [h1]
      _ = g * x := by group
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hgc
  exact hgc


theorem ggInndiagToral_E6_of_splitCoprime [Finite K] {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : p ∣ Nat.card K - 1) {A : Subgroup (MulAut ↥(adjointGroup .E6 K))}
    (hAD : A ≤ LayerSixE.inndiagAut .E6 K) (hA : IsPGroup p A) :
    LayerSixE.GGInndiagToral .E6 K A := by
  have hA0 := hA.comap_of_injective _ (mulAut_conj_injective_adjoint (τ := .E6) (K := K))
  obtain ⟨c, hc⟩ := ggExcToral_of_not_dvd_index hp
    (TableBExc.not_dvd_index_torusGroup_E6 hp hp7 hpq) hA0
  refine ⟨c, fun α hα => ?_⟩
  obtain ⟨n, hn⟩ := hA ⟨α, hα⟩
  have hαn : α ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h3p : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)
  obtain ⟨x, rfl⟩ := mem_range_conj_of_inndiag_E6 (hAD hα) (h3p.pow_right n) hαn
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hc x hα)
  refine ⟨l, ?_⟩
  rw [← conj_eq_rootDiagAutHom hl, map_mul, map_mul, map_inv]

theorem ggInndiagToral_E6_zpowers_of_splitCoprime [Finite K] {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : p ∣ Nat.card K - 1) {α : MulAut ↥(adjointGroup .E6 K)}
    (hαD : α ∈ LayerSixE.inndiagAut .E6 K) (hαp : α ^ p = 1) :
    LayerSixE.GGInndiagToral .E6 K (Subgroup.zpowers α) :=
  ggInndiagToral_E6_of_splitCoprime hp hp7 hpq (Subgroup.zpowers_le.mpr hαD)
    (isPGroup_zpowers_of_pow_eq_one hαp)

end Inndiag

end ExcToralSylow

end CFSG.StandardType

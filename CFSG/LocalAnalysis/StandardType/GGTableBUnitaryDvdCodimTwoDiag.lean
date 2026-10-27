module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimTwoComb
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdNode

public section

namespace CFSG.StandardType

namespace TableBUDT

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.UnitaryFlag TableBUE TableBUD
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2

variable {K : Type} [Field K] {n d : ℕ}

section Ratio

variable (h : UnitaryFieldData 2 n K) [Finite K]

include h in
theorem exists_ratio (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} (hAb : IsElemAbelian p Ab)
    (hdiag : ∀ a ∈ Ab, ∃ (τ : Fin d → Kˣ) (hτ : diagHom d τ ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))),
        a = TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hτ⟩) (k₀ : Fin d) :
    ∃ ν : Ab →* (Fin d → Kˣ), Function.Injective ν ∧ (∀ a, ν a k₀ = 1) ∧
      (∀ a k, ν a k ∈ rootsOfUnity p K) ∧
      ∀ a : Ab, ∃ hN : diagHom d (ν a) ∈
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)),
          (a : MulAut _) = TableB.projConj (unitarySU 2 n K d) ⟨diagHom d (ν a), hN⟩ := by
  classical
  set N := Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) with hN
  set ρ := TableB.projConj (unitarySU 2 n K d) with hρ
  choose τf hτfN hτf using fun a : Ab => hdiag a a.2
  set Dn : Ab → N := fun a => ⟨diagHom d (τf a), hτfN a⟩ with hDn
  have hρDn : ∀ a : Ab, ρ (Dn a) = a := fun a => (hτf a).symm
  have hrat : ∀ {τ τ' : Fin d → Kˣ} (hD : diagHom d τ ∈ N) (hD' : diagHom d τ' ∈ N),
      ρ ⟨diagHom d τ, hD⟩ = ρ ⟨diagHom d τ', hD'⟩ →
      ∀ k, τ k * (τ k₀)⁻¹ = τ' k * (τ' k₀)⁻¹ := by
    intro τ τ' hD hD' he k
    obtain ⟨c, hc⟩ := exists_eq_mul_of_projConj_eq h hK hd hdq hp hpq hD hD' he
    exact ratio_eq_of_eq_mul hc k k₀
  have hone : diagHom d (1 : Fin d → Kˣ) ∈ N := by rw [map_one]; exact N.one_mem
  have hρone : ρ ⟨diagHom d 1, hone⟩ = 1 := by
    have : (⟨diagHom d 1, hone⟩ : N) = 1 := Subtype.ext (map_one _)
    rw [this, map_one]
  have hνone : ∀ k, τf 1 k * (τf 1 k₀)⁻¹ = 1 := by
    intro k
    have he : ρ ⟨diagHom d (τf 1), hτfN 1⟩ = ρ ⟨diagHom d 1, hone⟩ := by
      have h1 := hρDn 1
      rw [hρone]
      exact h1
    have h1 := hrat (hτfN 1) hone he k
    rw [h1]
    simp
  have hνmul : ∀ a b : Ab, ∀ k, τf (a * b) k * (τf (a * b) k₀)⁻¹ =
      τf a k * (τf a k₀)⁻¹ * (τf b k * (τf b k₀)⁻¹) := by
    intro a b k
    have hab : diagHom d (τf a * τf b) ∈ N := by
      rw [map_mul]
      exact N.mul_mem (hτfN a) (hτfN b)
    have hprod : ρ ⟨diagHom d (τf a * τf b), hab⟩ = ((a * b : Ab) : MulAut _) := by
      have : (⟨diagHom d (τf a * τf b), hab⟩ : N) = Dn a * Dn b :=
        Subtype.ext (map_mul _ _ _)
      rw [this, map_mul, hρDn, hρDn, Subgroup.coe_mul]
    have he : ρ ⟨diagHom d (τf (a * b)), hτfN (a * b)⟩ = ρ ⟨diagHom d (τf a * τf b), hab⟩ := by
      have h1 := hρDn (a * b)
      rw [hprod]
      exact h1
    rw [hrat (hτfN (a * b)) hab he k]
    apply Units.ext
    simp only [Pi.mul_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  let ν : Ab →* (Fin d → Kˣ) :=
    { toFun := fun a k => τf a k * (τf a k₀)⁻¹
      map_one' := funext hνone
      map_mul' := fun a b => funext (hνmul a b) }
  have hν : ∀ a k, ν a k = τf a k * (τf a k₀)⁻¹ := fun _ _ => rfl
  have hνD : ∀ a : Ab, diagHom d (ν a) =
      Matrix.GeneralLinearGroup.scalar (Fin d) (τf a k₀)⁻¹ * diagHom d (τf a) := by
    intro a
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_diagHom, coe_diagHom,
      Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    rw [hν, Units.val_mul, mul_comm]
  have hscalN : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ N := fun c =>
    TableB.scalar_mem_normalizer _ ⟨c, rfl⟩
  have hνN : ∀ a : Ab, diagHom d (ν a) ∈ N := fun a => by
    rw [hνD a]
    exact N.mul_mem (hscalN _) (hτfN a)
  have hρν : ∀ a : Ab, ρ ⟨diagHom d (ν a), hνN a⟩ = a := by
    intro a
    have he : (⟨diagHom d (ν a), hνN a⟩ : N) =
        ⟨Matrix.GeneralLinearGroup.scalar (Fin d) (τf a k₀)⁻¹, hscalN _⟩ * Dn a :=
      Subtype.ext (hνD a)
    rw [he, map_mul, hρDn, TableB.projConj_of_scalar _ ⟨_, rfl⟩, one_mul]
  have hνinj : Function.Injective ν := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hc : ∀ k, τf a k = τf a k₀ := fun k => by
      have h1 := congrFun ha k
      rw [hν, Pi.one_apply, mul_inv_eq_one] at h1
      exact h1
    have hs : diagHom d (τf a) = Matrix.GeneralLinearGroup.scalar (Fin d) (τf a k₀) :=
      diagHom_eq_scalar_iff.mpr hc
    have hz : diagHom d (τf a) ∈ LargeEvenScalars (Fin d) K := ⟨τf a k₀, hs.symm⟩
    apply Subtype.ext
    rw [← hρDn a, Subgroup.coe_one]
    exact TableB.projConj_of_scalar (unitarySU 2 n K d) hz
  have hνp : ∀ a k, ν a k ∈ rootsOfUnity p K := by
    intro a k
    rw [mem_rootsOfUnity]
    have hpow : diagHom d (τf a ^ p) ∈ N := by rw [map_pow]; exact N.pow_mem (hτfN a) p
    have hap : ρ ⟨diagHom d (τf a ^ p), hpow⟩ = 1 := by
      have : (⟨diagHom d (τf a ^ p), hpow⟩ : N) = Dn a ^ p := Subtype.ext (map_pow _ _ _)
      rw [this, map_pow, hρDn]
      exact hAb.2 _ a.2
    have h1 := hrat hpow hone (hap.trans hρone.symm) k
    rw [Pi.pow_apply, Pi.pow_apply, Pi.one_apply, Pi.one_apply, inv_one, mul_one, ← inv_pow,
      ← mul_pow] at h1
    rw [hν]
    exact h1
  exact ⟨ν, hνinj, fun a => by rw [hν, mul_inv_cancel], hνp, fun a => ⟨hνN a, (hρν a).symm⟩⟩

end Ratio

section Node

variable (h : UnitaryFieldData 2 n K) [Finite K]

include h in
theorem endNode_of_ratio (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 5 ≤ d) (hq : 2 < 2 ^ n ∨ 6 ≤ d)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} {ν : Ab →* (Fin d → Kˣ)}
    (hνinj : Function.Injective ν)
    (hνN : ∀ a : Ab, ∃ hN : diagHom d (ν a) ∈
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)),
          (a : MulAut _) = TableB.projConj (unitarySU 2 n K d) ⟨diagHom d (ν a), hN⟩)
    (hnode : HasNode ν.range) :
    ∃ a ∈ Ab, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
      ∀ a' ∈ Ab, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a) := by
  classical
  obtain ⟨y, ⟨a₁, rfl⟩, hy1, T, hTne, hT2, hyT, hyc, hyz⟩ := hnode
  choose hNf hνf using hνN
  set S : Finset (Fin d) := Tᶜ with hSdef
  have hnodeS : IsNodeOn (ν a₁) S := by
    refine ⟨fun i hi j hj => hyc i j (Finset.mem_compl.mp hi) (Finset.mem_compl.mp hj),
      fun i hi j hj => ?_⟩
    have hiT : i ∈ T := by simpa [hSdef] using hi
    exact hyT i hiT j hj
  have hScard : S.card = d - T.card := by
    rw [hSdef, Finset.card_compl, Fintype.card_fin]
  have hT2' : T.card ≤ 2 := hT2
  have hSc : Sᶜ.card < S.card := by
    rw [hSdef, compl_compl, hScard]
    omega
  have hS3 : 3 ≤ S.card := by
    rw [hScard]
    omega
  have hSq : (S.card, 2 ^ n) ≠ (3, 2) := by
    intro he
    have h1 : S.card = 3 := congrArg Prod.fst he
    have h2 : 2 ^ n = 2 := congrArg Prod.snd he
    rcases hq with hq | hq <;> omega
  obtain ⟨hlayer, hcomp⟩ := layer_ggFix_projConj h hK hnodeS hSc hS3 hSq (hNf a₁)
  have ha₁ := hνf a₁
  have hT' : ∃ k, k ∉ S := by
    obtain ⟨k, hk⟩ := hTne
    exact ⟨k, by simpa [hSdef] using hk⟩
  refine ⟨a₁, a₁.2, fun h1 => hy1 ?_, ?_, fun a' ha' => ?_⟩
  · have : a₁ = 1 := Subtype.ext h1
    rw [this, map_one]
  · rw [ha₁, hlayer]
    exact hcomp
  · constructor
    · intro hfix
      set b : Ab := ⟨a', ha'⟩ with hb
      have hb' : a' = TableB.projConj _ ⟨diagHom d (ν b), hNf b⟩ := hνf b
      rw [ha₁, hlayer, hb'] at hfix
      have hconst := (fix_blockSU_iff h hT' (hNf b)).mp hfix
      have hνc : ∀ k l, k ∉ T → l ∉ T → ν b k = ν b l := by
        intro k l hk hl
        exact hconst k (Finset.mem_compl.mpr hk) l (Finset.mem_compl.mpr hl)
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hyz (ν b) ⟨b, rfl⟩ hνc)
      have h3 : a₁ ^ m = b := hνinj (by rw [map_zpow, hm])
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨m, by rw [← Subgroup.coe_zpow, h3]⟩
    · intro hmem j hj
      rw [ha₁, hlayer] at hj
      have hj' : ((a₁ : Ab) : MulAut _) j = j := by
        rw [ha₁]
        exact mem_ggFix.mp (hcomp.1 hj)
      exact apply_eq_of_mem_zpowers hmem hj'

include h in
theorem endNode_of_eq (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hd : 6 ≤ d)
    {Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} (hAb : IsElemAbelian p Ab)
    (hdiag : ∀ a ∈ Ab, ∃ (τ : Fin d → Kˣ) (hτ : diagHom d τ ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))),
        a = TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hτ⟩)
    (hcard : p ^ (d - 3) ≤ Nat.card Ab) {s t : Fin d} (hst : s ≠ t)
    {ν₀ : Ab → (Fin d → Kˣ)}
    (hν₀ : ∀ a : Ab, (∃ hN : diagHom d (ν₀ a) ∈
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)),
          (a : MulAut _) = TableB.projConj (unitarySU 2 n K d) ⟨diagHom d (ν₀ a), hN⟩) ∧
        ν₀ a s = ν₀ a t) :
    ∃ a ∈ Ab, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
      ∀ a' ∈ Ab, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a) := by
  have hp2 := ne_two_of_dvd h hpq
  have hpK := dvd_card_sub_one' h hpq
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  obtain ⟨ν, hνinj, hν0, hνp, hνN⟩ := exists_ratio h hK hp hpq (by omega) hdq hAb hdiag s
  have hνt : ∀ a : Ab, ν a t = 1 := by
    intro a
    obtain ⟨hN, hνa⟩ := hνN a
    obtain ⟨⟨hN₀, hν₀a⟩, hst₀⟩ := hν₀ a
    obtain ⟨c, hc⟩ := exists_eq_mul_of_projConj_eq h hK (by omega) hdq hp hpq hN₀ hN
      (hν₀a.symm.trans hνa)
    rw [hc t, ← hst₀, ← hc s]
    exact hν0 a
  have hcardY : Nat.card ν.range = Nat.card Ab := Nat.card_range_of_injective hνinj
  refine endNode_of_ratio h hK (by omega) (Or.inr hd) hνinj hνN ?_
  refine hasNode_of_eq hp hp2 hpK (by omega) hst ?_ ?_ ?_ (hcardY ▸ hcard)
  · rintro _ ⟨a, rfl⟩
    exact hν0 a
  · rintro _ ⟨a, rfl⟩
    exact hνt a
  · rintro _ ⟨a, rfl⟩ k
    exact hνp a k

end Node

end TableBUDT

end CFSG.StandardType

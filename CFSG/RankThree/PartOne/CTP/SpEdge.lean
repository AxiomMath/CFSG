module

public import CFSG.RankThree.PartOne.CTP.SpAut
public import CFSG.RankThree.PartOne.CTP.SpPair
public import CFSG.RankThree.PartOne.CTP.LinearEdge

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

section Induced

variable {S G : Type*} [Group S] [Group G] (θ : S →* G)

theorem exists_aut_of_normalizes (hθ : Function.Injective θ) {e : G}
    (he : e ∈ Subgroup.normalizer (θ.range : Set G)) :
    ∃ ε : MulAut S, ∀ s, θ (ε s) = e * θ s * e⁻¹ := by
  let c : MulAut ↥θ.range := θ.range.normalizerMonoidHom ⟨e, he⟩
  let ι : S ≃* θ.range := MonoidHom.ofInjective hθ
  refine ⟨ι.trans (c.trans ι.symm), fun s => ?_⟩
  change θ (ι.symm (c (ι s))) = _
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

end Induced

section Elements

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem injective_of_ker_le_center {G : Type*} [Group G] (θ : StatedSp 2 K →* G)
    (hker : θ.ker ≤ Subgroup.center (StatedSp 2 K)) : Function.Injective θ := by
  refine (MonoidHom.ker_eq_bot_iff θ).mp (eq_bot_iff.mpr fun x hx => ?_)
  exact center_sp_eq_one_of_charTwo (hker hx)

theorem exists_sp_of_normalizes {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {G : Type}
    [Group G] (θ : StatedSp 2 K →* G) (hθ : Function.Injective θ) {e : G}
    (he : e ∈ Subgroup.normalizer (θ.range : Set G)) {p : ℕ} (hp : Odd p) (hep : e ^ p = 1)
    {x : StatedSp 2 K} (hx : orderOf x = Nat.card K - 1) (hex : e * θ x = θ x * e) :
    ∃ g : StatedSp 2 K, g ^ p = 1 ∧ ∀ s : StatedSp 2 K, θ (g * s * g⁻¹) = e * θ s * e⁻¹ := by
  obtain ⟨ε, hε⟩ := exists_aut_of_normalizes θ hθ he
  have hεpow : ∀ k : ℕ, ∀ s, θ ((ε ^ k) s) = e ^ k * θ s * (e ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro s; simp
    | succ k ih =>
      intro s
      rw [pow_succ, pow_succ, MulAut.mul_apply, ih, hε]
      group
  have hεp : ε ^ p = 1 := by
    refine MulEquiv.ext fun s => hθ ?_
    rw [hεpow, hep]
    simp
  have hεx : ε x = x := by
    apply hθ
    rw [hε, hex]
    group
  obtain ⟨g, hg⟩ := sp_aut_odd hf hK hp hεp hx hεx
  have hεk : ∀ k : ℕ, ∀ s, (ε ^ k) s = g ^ k * s * (g ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro s; simp
    | succ k ih =>
      intro s
      rw [pow_succ, MulAut.mul_apply, hg, ih]
      group
  refine ⟨g, ?_, fun s => by rw [← hg, hε]⟩
  refine center_sp_eq_one_of_charTwo (Subgroup.mem_center_iff.mpr fun s => ?_)
  have h1 : g ^ p * s * (g ^ p)⁻¹ = s := by
    rw [← hεk, hεp, MulAut.one_apply]
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

end Elements

section Standard

variable {K : Type} [Field K] {G : Type} [Group G]

theorem symplecticBlockStandardPair_of_conj (θ : StatedSp 2 K →* G) (hθ : Function.Injective θ)
    {c : StatedSp 2 K} {U V : Subgroup G} (hUle : U ≤ θ.range) (hVle : V ≤ θ.range)
    (hU : U.comap θ = (longBlock K 2 1).range.map (MulAut.conj c).toMonoidHom)
    (hV : V.comap θ = (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map
      (MulAut.conj c).toMonoidHom) :
    SymplecticBlockStandardPair K θ.range U V := by
  refine ⟨θ, c⁻¹, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff θ).mpr hθ]
    exact bot_le
  · rw [inv_inv]
    exact hθ.comp ((MulAut.conj c).injective.comp (longBlock_injective (K := K) (n := 2) 1))
  · rw [inv_inv]
    exact hθ.comp ((MulAut.conj c).injective.comp
      (shortBlock_injective (K := K) (n := 2) (zero_ne_one : (0 : Fin 2) ≠ 1)))
  · rw [inv_inv, ← hU, Subgroup.map_comap_eq, inf_of_le_right hUle]
  · rw [inv_inv, ← hV, Subgroup.map_comap_eq, inf_of_le_right hVle]

end Standard


section Edge

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G]

omit [CharP K 2] in
theorem card_range_sl2 {L H : Type} [Field L] [Finite L] [Group H] (hL : Nat.card L = Nat.card K)
    (φ : SL(2, L) →* H) (hφ : Function.Injective φ) :
    Nat.card φ.range = Nat.card SL(2, K) := by
  rw [← card_sl2_eq hL]
  exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm

theorem sp_edge_pair_cases {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (θ : StatedSp 2 K →* G) (hker : θ.ker ≤ Subgroup.center (StatedSp 2 K)) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ 2 ^ f - 1) {E A B : Subgroup G} [CFSG.IsElementaryAbelian p E]
    (hE : EdgeTorus p E A B) (hAB : A ⊔ B = θ.range) {KA KB : Type} [Field KA] [Field KB]
    [Finite KA] [Finite KB] (hKA : Nat.card KA = 2 ^ f) (hKB : Nat.card KB = 2 ^ f)
    (ρA : SL(2, KA) ≃* ↥A) (ρB : SL(2, KB) ≃* ↥B) :
    SymplecticBlockStandardPair K (A ⊔ B) A B ∨ SymplecticBlockStandardPair K (A ⊔ B) B A := by
  classical
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hθ : Function.Injective θ := injective_of_ker_le_center θ hker
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hmK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd_natCard_sub_one hmK
  have : NeZero p := ⟨hp.ne_zero⟩
  have hAle : A ≤ θ.range := by rw [← hAB]; exact le_sup_left
  have hBle : B ≤ θ.range := by rw [← hAB]; exact le_sup_right
  let φA : SL(2, KA) →* StatedSp 2 K := (MonoidHom.ofInjective hθ).symm.toMonoidHom.comp
    ((Subgroup.inclusion hAle).comp ρA.toMonoidHom)
  let φB : SL(2, KB) →* StatedSp 2 K := (MonoidHom.ofInjective hθ).symm.toMonoidHom.comp
    ((Subgroup.inclusion hBle).comp ρB.toMonoidHom)
  have hθφA : ∀ a, θ (φA a) = (ρA a : G) := fun a => by
    change θ ((MonoidHom.ofInjective hθ).symm (Subgroup.inclusion hAle (ρA a))) = _
    rw [MonoidHom.apply_ofInjective_symm]
    rfl
  have hθφB : ∀ b, θ (φB b) = (ρB b : G) := fun b => by
    change θ ((MonoidHom.ofInjective hθ).symm (Subgroup.inclusion hBle (ρB b))) = _
    rw [MonoidHom.apply_ofInjective_symm]
    rfl
  have hφA : Function.Injective φA := fun a a' h =>
    ρA.injective (Subtype.ext (by rw [← hθφA a, ← hθφA a', h]))
  have hφB : Function.Injective φB := fun b b' h =>
    ρB.injective (Subtype.ext (by rw [← hθφB b, ← hθφB b', h]))
  have hA₀ : A.comap θ = φA.range := by
    ext s
    constructor
    · intro hs
      refine ⟨ρA.symm ⟨θ s, hs⟩, hθ ?_⟩
      rw [hθφA]
      simp
    · rintro ⟨a, rfl⟩
      change θ (φA a) ∈ A
      rw [hθφA]
      exact (ρA a).2
  have hB₀ : B.comap θ = φB.range := by
    ext s
    constructor
    · intro hs
      refine ⟨ρB.symm ⟨θ s, hs⟩, hθ ?_⟩
      rw [hθφB]
      simp
    · rintro ⟨b, rfl⟩
      change θ (φB b) ∈ B
      rw [hθφB]
      exact (ρB b).2
  have hperfA : Group.IsPerfect (SL(2, KA)) := isPerfect_sl2 (by rw [hKA, ← hK]; exact hq4)
  have hperfB : Group.IsPerfect (SL(2, KB)) := isPerfect_sl2 (by rw [hKB, ← hK]; exact hq4)
  have : Group.IsPerfect (A.comap θ) := by
    rw [hA₀]
    exact Group.IsPerfect.range φA
  have : Group.IsPerfect (B.comap θ) := by
    rw [hB₀]
    exact Group.IsPerfect.range φB
  have hcardA : Nat.card (A.comap θ) = Nat.card SL(2, K) := by
    rw [hA₀]
    exact card_range_sl2 (by rw [hKA, hK]) φA hφA
  have hcardB : Nat.card (B.comap θ) = Nat.card SL(2, K) := by
    rw [hB₀]
    exact card_range_sl2 (by rw [hKB, hK]) φB hφB
  obtain ⟨tA, htA⟩ := exists_sl2_orderOf_eq (L := KA)
  obtain ⟨tB, htB⟩ := exists_sl2_orderOf_eq (L := KB)
  have hordA : orderOf (φA tA) = Nat.card K - 1 := by
    rw [orderOf_injective φA hφA, htA, hKA, hK]
  have hordB : orderOf (φB tB) = Nat.card K - 1 := by
    rw [orderOf_injective φB hφB, htB, hKB, hK]
  obtain ⟨eA, heAE, hAcen, ⟨yB, hyB, hyBne⟩, -, hAord⟩ := hE.exists_centralizing hp
  obtain ⟨eB, heBE, hBcen, ⟨yA, hyA, hyAne⟩, -, hBord⟩ := hE.symm.exists_centralizing hp
  have heAA : eA ∈ Subgroup.normalizer (A : Set G) := le_normalizer_of_dec hE.decA heAE
  have heAB : eA ∈ Subgroup.normalizer (B : Set G) := le_normalizer_of_dec hE.decB heAE
  have heBA : eB ∈ Subgroup.normalizer (A : Set G) := le_normalizer_of_dec hE.decA heBE
  have heBB : eB ∈ Subgroup.normalizer (B : Set G) := le_normalizer_of_dec hE.decB heBE
  have hXA : eA ∈ Subgroup.normalizer (θ.range : Set G) := by
    rw [← hAB]
    exact mem_normalizer_sup heAA heAB
  have hXB : eB ∈ Subgroup.normalizer (θ.range : Set G) := by
    rw [← hAB]
    exact mem_normalizer_sup heBA heBB
  have heApow : eA ^ p = 1 := by rw [← hAord]; exact pow_orderOf_eq_one eA
  have heBpow : eB ^ p = 1 := by rw [← hBord]; exact pow_orderOf_eq_one eB
  obtain ⟨gA, hgApow, hgA⟩ := exists_sp_of_normalizes (by omega) hK θ hθ hXA hpodd heApow hordA
    (by rw [hθφA]; exact hAcen _ (ρA tA).2)
  obtain ⟨gB, hgBpow, hgB⟩ := exists_sp_of_normalizes (by omega) hK θ hθ hXB hpodd heBpow hordB
    (by rw [hθφB]; exact hBcen _ (ρB tB).2)
  have hcA : ∀ a ∈ A.comap θ, a * gA = gA * a := by
    intro a ha
    have h1 := hgA a
    rw [Subgroup.mem_comap] at ha
    have h2 : eA * θ a * eA⁻¹ = θ a := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hAcen _ ha
    rw [h2] at h1
    have h3 := hθ h1
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  have hcB : ∀ b ∈ B.comap θ, b * gB = gB * b := by
    intro b hb
    have h1 := hgB b
    rw [Subgroup.mem_comap] at hb
    have h2 : eB * θ b * eB⁻¹ = θ b := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hBcen _ hb
    rw [h2] at h1
    have h3 := hθ h1
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : StatedSp 2 K, θ b₀ = yB := by
    obtain ⟨b₀, hb₀⟩ := hBle hyB
    exact ⟨b₀, hb₀⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : StatedSp 2 K, θ a₀ = yA := by
    obtain ⟨a₀, ha₀⟩ := hAle hyA
    exact ⟨a₀, ha₀⟩
  have hmovB : ∃ b ∈ B.comap θ, gA * b ≠ b * gA := by
    refine ⟨b₀, by rw [Subgroup.mem_comap, hb₀]; exact hyB, fun h => hyBne ?_⟩
    have h1 : gA * b₀ * gA⁻¹ = b₀ := by rw [mul_inv_eq_iff_eq_mul]; exact h
    have h2 := hgA b₀
    rw [h1, hb₀] at h2
    rw [eq_mul_inv_iff_mul_eq] at h2
    exact h2.symm
  have hmovA : ∃ a ∈ A.comap θ, gB * a ≠ a * gB := by
    refine ⟨a₀, by rw [Subgroup.mem_comap, ha₀]; exact hyA, fun h => hyAne ?_⟩
    have h1 : gB * a₀ * gB⁻¹ = a₀ := by rw [mul_inv_eq_iff_eq_mul]; exact h
    have h2 := hgB a₀
    rw [h1, ha₀] at h2
    rw [eq_mul_inv_iff_mul_eq] at h2
    exact h2.symm
  have hgA1 : gA ≠ 1 := by
    rintro rfl
    obtain ⟨b, -, hb⟩ := hmovB
    exact hb (by simp)
  have hgB1 : gB ≠ 1 := by
    rintro rfl
    obtain ⟨a, -, ha⟩ := hmovA
    exact ha (by simp)
  have hee : eA * eB = eB * eA := by
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := E)).comm (⟨eA, heAE⟩ : E) ⟨eB, heBE⟩)
  have hcom : gA * gB = gB * gA := by
    have h1 : ∀ s, (gB * gA) * s * (gB * gA)⁻¹ = (gA * gB) * s * (gA * gB)⁻¹ := by
      intro s
      apply hθ
      have e1 : (gA * gB) * s * (gA * gB)⁻¹ = gA * (gB * s * gB⁻¹) * gA⁻¹ := by group
      have e2 : (gB * gA) * s * (gB * gA)⁻¹ = gB * (gA * s * gA⁻¹) * gB⁻¹ := by group
      rw [e1, e2, hgA, hgB, hgB, hgA]
      have e3 : eB * (eA * θ s * eA⁻¹) * eB⁻¹ = (eB * eA) * θ s * (eB * eA)⁻¹ := by group
      have e4 : eA * (eB * θ s * eB⁻¹) * eA⁻¹ = (eA * eB) * θ s * (eA * eB)⁻¹ := by group
      rw [e3, e4, hee]
    have hz : (gB * gA)⁻¹ * (gA * gB) ∈ Subgroup.center (StatedSp 2 K) := by
      rw [Subgroup.mem_center_iff]
      intro s
      have h2 := h1 s
      have h3 : (gB * gA)⁻¹ * (gA * gB) * s * ((gB * gA)⁻¹ * (gA * gB))⁻¹ = s := by
        calc (gB * gA)⁻¹ * (gA * gB) * s * ((gB * gA)⁻¹ * (gA * gB))⁻¹
            = (gB * gA)⁻¹ * ((gA * gB) * s * (gA * gB)⁻¹) * (gB * gA) := by group
          _ = (gB * gA)⁻¹ * ((gB * gA) * s * (gB * gA)⁻¹) * (gB * gA) := by rw [← h2]
          _ = s := by group
      rw [mul_inv_eq_iff_eq_mul] at h3
      exact h3.symm
    exact (inv_mul_eq_one.mp (center_sp_eq_one_of_charTwo hz)).symm
  have hgen : A.comap θ ⊔ B.comap θ = ⊤ := by
    rw [Subgroup.comap_sup_eq_of_le_range θ hAle hBle, hAB]
    exact eq_top_iff.mpr fun s _ => ⟨s, rfl⟩
  have hA1 : A.comap θ ≠ ⊥ := by
    intro h
    have hmem : φA tA ∈ A.comap θ := by
      change θ (φA tA) ∈ A
      rw [hθφA]
      exact (ρA tA).2
    rw [h, Subgroup.mem_bot] at hmem
    have h4 := hordA
    rw [hmem, orderOf_one] at h4
    omega
  have hB1 : B.comap θ ≠ ⊥ := by
    intro h
    have hmem : φB tB ∈ B.comap θ := by
      change θ (φB tB) ∈ B
      rw [hθφB]
      exact (ρB tB).2
    rw [h, Subgroup.mem_bot] at hmem
    have h4 := hordB
    rw [hmem, orderOf_one] at h4
    omega
  obtain ⟨c, hc⟩ := sp_pair hq4 hζ hgApow hgBpow hgA1 hgB1 hcom hA1 hB1 hcardA hcardB hcA hcB
    hmovB hgen
  rcases hc with ⟨hcA', hcB'⟩ | ⟨hcB', hcA'⟩
  · left
    rw [hAB]
    exact symplecticBlockStandardPair_of_conj θ hθ hAle hBle hcA' hcB'
  · right
    rw [hAB]
    exact symplecticBlockStandardPair_of_conj θ hθ hBle hAle hcB' hcA'

end Edge

end CFSG.RankThree.PartOne.CTP

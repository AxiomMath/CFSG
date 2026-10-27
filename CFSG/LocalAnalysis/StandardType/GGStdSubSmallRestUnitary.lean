module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestLift
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperUnitary
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock

public section

namespace CFSG.StandardType

namespace StdSubRestU

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2 TableBUE IOneU

section Comb

variable {K : Type} [Field K] [Finite K] {d p : ℕ}

theorem exists_mem_of_pair (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    {W : Subgroup (Fin d → Kˣ)} (hWp : ∀ σ ∈ W, ∀ k, σ k ∈ rootsOfUnity p K)
    (hW1 : ∀ σ ∈ W, ∏ k, (σ k : K) = 1) {s t c : Fin d} (hst : s ≠ t) (hsc : s ≠ c)
    (hct : c ≠ t) (hWst : ∀ σ ∈ W, σ s = σ t) (hcard : p ^ (d - 2) ≤ Nat.card W)
    (v : Fin d → Kˣ) (hv : ∀ k, v k ∈ rootsOfUnity p K) :
    ∃ σ ∈ W, ∀ i ∈ freeSet t c, σ i = v i := by
  classical
  have := Fact.mk hp
  set F := freeSet t c with hF
  let f : W → (F → rootsOfUnity p K) := fun σ i => ⟨(σ : Fin d → Kˣ) i, hWp σ σ.2 i⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    refine eq_of_agree (hW1 _ a.2) (hW1 _ b.2) (hWst _ a.2) (hWst _ b.2) hst hsc fun i hi => ?_
    exact congrArg Subtype.val (congrFun hab ⟨i, hi⟩)
  have hcardF : Nat.card (F → rootsOfUnity p K) = p ^ (d - 2) := by
    rw [Nat.card_fun, TypeA.card_rootsOfUnity_of_dvd hp hpK, Nat.card_eq_finsetCard,
      card_freeSet hct]
  have hbij := hf.bijective_of_nat_card_le (hcardF ▸ hcard)
  obtain ⟨⟨σ, hσW⟩, hσ⟩ := hbij.2 fun i => ⟨v i, hv i⟩
  exact ⟨σ, hσW, fun i hi => congrArg Subtype.val (congrFun hσ ⟨i, hi⟩)⟩

theorem card_le_of_pair (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    {W : Subgroup (Fin d → Kˣ)} (hWp : ∀ σ ∈ W, ∀ k, σ k ∈ rootsOfUnity p K)
    (hW1 : ∀ σ ∈ W, ∏ k, (σ k : K) = 1) {s t c : Fin d} (hst : s ≠ t) (hsc : s ≠ c)
    (hct : c ≠ t) (hWst : ∀ σ ∈ W, σ s = σ t) : Nat.card W ≤ p ^ (d - 2) := by
  classical
  have := Fact.mk hp
  set F := freeSet t c with hF
  let f : W → (F → rootsOfUnity p K) := fun σ i => ⟨(σ : Fin d → Kˣ) i, hWp σ σ.2 i⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    refine eq_of_agree (hW1 _ a.2) (hW1 _ b.2) (hWst _ a.2) (hWst _ b.2) hst hsc fun i hi => ?_
    exact congrArg Subtype.val (congrFun hab ⟨i, hi⟩)
  have hcardF : Nat.card (F → rootsOfUnity p K) = p ^ (d - 2) := by
    rw [Nat.card_fun, TypeA.card_rootsOfUnity_of_dvd hp hpK, Nat.card_eq_finsetCard,
      card_freeSet hct]
  rw [← hcardF]
  exact Nat.card_le_card_of_injective f hf

theorem mem_freeSet_iff {t c i : Fin d} : i ∈ freeSet t c ↔ i ≠ c ∧ i ≠ t := by
  simp [freeSet]

end Comb

section Block

variable {K : Type} [Field K] {d : ℕ}

theorem isBlockOn_conj {S : Finset (Fin d)} {G Gi Y : Matrix (Fin d) (Fin d) K}
    (hGGi : G * Gi = 1) (hY : IsBlockOn S Y)
    (hG : ∀ i k, i ∉ S → k ∈ S → G i k = 0) (hGi : ∀ l j, l ∈ S → j ∉ S → Gi l j = 0) :
    IsBlockOn S (G * Y * Gi) := by
  intro i j hij
  have hY' : ∀ k l, (Y - 1) k l ≠ 0 → k ∈ S ∧ l ∈ S := by
    intro k l hkl
    by_contra hc
    apply hkl
    rw [Matrix.sub_apply, hY k l (by tauto), sub_self]
  have key : (G * (Y - 1) * Gi) i j = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hkl : (Y - 1) k l = 0
    · rw [hkl, mul_zero, zero_mul]
    · obtain ⟨hk, hl⟩ := hY' k l hkl
      rcases hij with hi | hj
      · rw [hG i k hi hk, zero_mul, zero_mul]
      · rw [hGi l j hl hj, mul_zero]
  have h1 : G * Y * Gi = G * (Y - 1) * Gi + 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hGGi, sub_add_cancel]
  rw [h1, Matrix.add_apply, key, zero_add]

variable {n : ℕ}

theorem conj_mem_blockSU_of_commute {σ : Fin d → Kˣ} {x g y : ↥(unitarySU 2 n K d)}
    (hx : (x : GL (Fin d) K) = diagHom d σ) (hg : g ∈ Subgroup.centralizer {x})
    {S : Finset (Fin d)} (hS : ∀ i ∈ S, ∀ j, j ∈ S ↔ σ j = σ i) (hy : y ∈ blockSU S) :
    g * y * g⁻¹ ∈ blockSU S := by
  have hc : ∀ g' ∈ Subgroup.centralizer {x},
      (g' : GL (Fin d) K) * diagHom d σ = diagHom d σ * g' := by
    intro g' hg'
    rw [← hx]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg')
  have hne : ∀ i k, i ∉ S → k ∈ S → σ i ≠ σ k := fun i k hi hk he =>
    hi ((hS k hk i).mpr he)
  have hgi := (Subgroup.centralizer {x}).inv_mem hg
  rw [mem_blockSU]
  have h1 : (((g * y * g⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          (((g⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    simp only [Subgroup.coe_mul, Units.val_mul]
  rw [h1]
  refine isBlockOn_conj ?_ hy (fun i k hi hk => entry_eq_zero_of_commute (hc g hg) (hne i k hi hk))
    (fun l j hl hj => entry_eq_zero_of_commute (hc _ hgi) (hne j l hj hl).symm)
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]

theorem isBlockOn_diagHom {S : Finset (Fin d)} {τ : Fin d → Kˣ} (hτ : ∀ k, k ∉ S → τ k = 1) :
    IsBlockOn S ((diagHom d τ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  intro i j hij
  rw [coe_diagHom]
  by_cases h : i = j
  · subst h
    have hi : i ∉ S := by tauto
    rw [Matrix.diagonal_apply_eq, hτ i hi, Units.val_one, Matrix.one_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem exists_scalar_of_projMk_eq_one {z : ↥(unitarySU 2 n K d)}
    (hz : LargeEvenProjMk (unitarySU 2 n K d) z = 1) :
    ∃ u : Kˣ, ∀ i j, ((z : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j =
      if i = j then (u : K) else 0 := by
  have hz' : z ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker := hz
  rw [LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, largeEvenScalars_def] at hz'
  obtain ⟨u, hu⟩ := hz'
  refine ⟨u, fun i j => ?_⟩
  rw [← hu]
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

theorem projMk_eq_one_of_const {z : ↥(unitarySU 2 n K d)} {σ : Fin d → Kˣ}
    (hz : (z : GL (Fin d) K) = diagHom d σ) {u : Kˣ} (hc : ∀ i, σ i = u) :
    LargeEvenProjMk (unitarySU 2 n K d) z = 1 := by
  show z ∈ (LargeEvenProjMk (unitarySU 2 n K d)).ker
  rw [LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, largeEvenScalars_def]
  refine ⟨u, Units.ext ?_⟩
  rw [hz, coe_diagHom]
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hc]

end Block

section Units

variable {M : Type} [Group M]

theorem eq_one_of_zpow_of_zpow_ne {p : ℕ} (hp : p.Prime) {a b : M} (ha : a ^ p = 1)
    (hb : b ^ p = 1) {m : ℤ} (ham : a ^ m = 1) (hbm : b ^ m ≠ 1) : a = 1 := by
  by_contra ha1
  have := Fact.mk hp
  have hoa : orderOf a = p := orderOf_eq_prime ha ha1
  have hpm : (p : ℤ) ∣ m := by
    rw [← hoa]
    exact orderOf_dvd_iff_zpow_eq_one.mpr ham
  apply hbm
  rw [← orderOf_dvd_iff_zpow_eq_one]
  exact (Int.natCast_dvd_natCast.mpr (orderOf_dvd_of_pow_eq_one hb)).trans hpm

end Units

section Diag

variable {K : Type} [Field K] [Finite K] {n d p : ℕ} (h : UnitaryFieldData 2 n K)

omit [Finite K] in
theorem diagHom_apply_self (σ : Fin d → Kˣ) (k : Fin d) :
    ((diagHom d σ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) k k = σ k := by
  rw [coe_diagHom, Matrix.diagonal_apply_eq]

omit [Finite K] in
theorem mulSingle_mem {X : Subgroup Kˣ} {i : Fin d} {u : Kˣ} (hu : u ∈ X) (k : Fin d) :
    (Pi.mulSingle i u : Fin d → Kˣ) k ∈ X := by
  classical
  by_cases hk : k = i
  · subst hk
    rw [Pi.mulSingle_eq_same]
    exact hu
  · rw [Pi.mulSingle_eq_of_ne hk]
    exact X.one_mem

include h in
theorem ggStdSubNormEltData_diag (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) {A : Subgroup ↥(unitarySU 2 n K d)}
    (hA : IsElemAbelian p A)
    (hdiag : ∀ x ∈ A, ∃ σ : Fin d → Kˣ, (x : GL (Fin d) K) = diagHom d σ)
    (hcard : p ^ (d - 2) ≤ Nat.card A) (h3 : p ^ 3 ≤ Nat.card A) {s t : Fin d} (hst : s ≠ t)
    (hpair : ∀ σ ∈ diagVec A, σ s = σ t) {x : ↥(unitarySU 2 n K d)} (hxA : x ∈ A)
    (hx1 : LargeEvenProjMk (unitarySU 2 n K d) x ≠ 1) :
    GGStdSubNormEltData p (A.map (LargeEvenProjMk (unitarySU 2 n K d)))
      (LargeEvenProjMk (unitarySU 2 n K d) x) := by
  classical
  set π := LargeEvenProjMk (unitarySU 2 n K d) with hπ
  have hpK := dvd_card_sub_one hK hpq
  set W := diagVec A with hW
  have hWp : ∀ σ ∈ W, ∀ k, σ k ∈ rootsOfUnity p K := fun σ hσ k => by
    rw [mem_rootsOfUnity]
    exact (diagVec_props h hA hσ).1 k
  have hW1 : ∀ σ ∈ W, ∏ k, (σ k : K) = 1 := fun σ hσ => (diagVec_props h hA hσ).2
  have hWc : p ^ (d - 2) ≤ Nat.card W := by
    rw [hW, card_diagVec hdiag]
    exact hcard
  have hnp : ∀ z ∈ π.ker, z ^ p = 1 → z = 1 := fun z hz hzp =>
    eq_one_of_mem_suScalars h hp hpd hz hzp
  have hker := ker_projMk_le_center (n := n) (d := d) (K := K)
  have hinj : ∀ y ∈ A, π y = 1 → y = 1 := fun y hy hy1 => hnp y hy1 (hA.2 y hy)
  obtain ⟨σx, hσx⟩ := hdiag x hxA
  have hσxW : σx ∈ W := mem_diagVec_of hxA hσx
  set S : Finset (Fin d) := Finset.univ.filter fun k => σx k = σx s with hSdef
  have hmemS : ∀ k, k ∈ S ↔ σx k = σx s := fun k => by simp [hSdef]
  have hsS : s ∈ S := (hmemS s).mpr rfl
  have htS : t ∈ S := (hmemS t).mpr (hpair σx hσxW).symm
  have hSeig : ∀ i ∈ S, ∀ j, j ∈ S ↔ σx j = σx i := fun i hi j => by
    rw [hmemS, (hmemS i).mp hi]
  have hSconst : ∀ i ∈ S, ∀ j ∈ S, σx i = σx j := fun i hi j hj => by
    rw [(hmemS i).mp hi, (hmemS j).mp hj]
  have hS2 : 2 ≤ S.card := by
    have hsub : ({s, t} : Finset (Fin d)) ⊆ S := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hsS
      · exact htS
    have h2 := Finset.card_le_card hsub
    rwa [Finset.card_pair hst] at h2
  set D := (blockSU S).map π with hD
  have hDq : CFSG.IsQuasisimple D :=
    (TableBSymp.isQuasisimple_iff _).mp
      (SURepair.isQuasisimple_map_blockSU_of_two_le h hn hker hS2)
  have hDC : D ≤ Subgroup.centralizer ({π x} : Set (LargeEvenProj (unitarySU 2 n K d))) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := blockSU_le_centralizer hSconst hσx hy
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
    rw [← map_mul, ← map_mul, h1]
  have hC := centralizer_map_eq_of_noTorsion π (QuotientGroup.mk'_surjective _) hker hnp
    (hA.2 x hxA)
  have hDn : ∀ c ∈ Subgroup.centralizer ({π x} : Set (LargeEvenProj (unitarySU 2 n K d))),
      ∀ e ∈ D, c * e * c⁻¹ ∈ D := by
    intro c hc e he
    rw [hC] at hc
    obtain ⟨g, hg, rfl⟩ := hc
    obtain ⟨y, hy, rfl⟩ := he
    exact ⟨g * y * g⁻¹, conj_mem_blockSU_of_commute hσx hg hSeig hy, by
      simp only [map_mul, map_inv]⟩
  have hwS : swapSU h s t ∈ blockSU S := isBlockOn_permGL_swap hsS htS
  set U := (Subgroup.zpowers (swapSU h s t)).map π with hU
  have hUD : U ≤ D := Subgroup.map_mono (Subgroup.zpowers_le.mpr hwS)
  have hU1 : U ≠ ⊥ := by
    intro hbot
    apply projMk_swapSU_ne_one h hst
    have h1 : π (swapSU h s t) ∈ U := ⟨_, Subgroup.mem_zpowers _, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact h1
  have hU2 : IsPGroup 2 U := (isPGroup_two_zpowers (swapSU_sq h s t)).map π
  have hAU : ∀ b ∈ A.map π, ∀ u ∈ U, b * u * b⁻¹ ∈ U := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨u, hu, rfl⟩
    obtain ⟨σ', hσ'⟩ := hdiag y hy
    have hyw := commute_swapSU h hσ' (hpair σ' (mem_diagVec_of hy hσ'))
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    refine ⟨swapSU h s t ^ m, Subgroup.zpow_mem_zpowers _ _, ?_⟩
    have hc : y * swapSU h s t ^ m * y⁻¹ = swapSU h s t ^ m := by
      rw [← (Commute.zpow_left hyw m).eq, mul_inv_cancel_right]
    rw [← map_inv, ← map_mul, ← map_mul, hc]
  refine ⟨D, hDC, hDn, hDq, U, hUD, hU1, hU2, hAU, fun hprov => ?_⟩
  have hcommD : ∀ τ ∈ W, (∀ i ∈ S, ∀ j ∈ S, τ i = τ j) → ∃ m : ℤ, τ = σx ^ m := by
    intro τ hτW hτS
    obtain ⟨y, hyA, hyτ⟩ := mem_diagVec.mp hτW
    have hyD : ∀ e ∈ D, π y * e = e * π y := by
      rintro _ ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul, (commute_blockSU_iff h hyτ).mpr hτS z hz]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hprov _ ⟨y, hyA, rfl⟩ hyD)
    refine ⟨m, ?_⟩
    have h1 : y = x ^ m := by
      have h2 : π (y * (x ^ m)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_zpow, hm, mul_inv_cancel]
      have h3 := hinj _ (A.mul_mem hyA (A.inv_mem (A.zpow_mem hxA m))) h2
      exact mul_inv_eq_one.mp h3
    apply diagHom_injective d
    rw [← hyτ, h1, Subgroup.coe_zpow, hσx, map_zpow]
  obtain ⟨ζ, hζo, hζq⟩ := exists_orderOf_eq_norm_one h hp hpq
  have hζp : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζo
    exact hp.one_lt.ne hζo
  have hζroot : ζ ∈ rootsOfUnity p K := by
    rw [mem_rootsOfUnity]
    exact hζp
  have hσxp : ∀ k, σx k ^ p = 1 := fun k => by
    have h1 := hWp σx hσxW k
    rwa [mem_rootsOfUnity] at h1
  have hone : ∀ k₁ k₂, k₁ ∉ S → k₂ ∉ S → k₁ = k₂ := by
    intro k₁ k₂ h1 h2
    by_contra h12
    have hk1t : k₁ ≠ t := fun h' => h1 (h' ▸ htS)
    have hk2t : k₂ ≠ t := fun h' => h2 (h' ▸ htS)
    have hsk1 : s ≠ k₁ := fun h' => h1 (h' ▸ hsS)
    have hsk2 : s ≠ k₂ := fun h' => h2 (h' ▸ hsS)
    obtain ⟨τ₁, hτ₁W, hτ₁⟩ := exists_mem_of_pair hp hpK hWp hW1 hst hsk2 hk2t hpair hWc
      (Pi.mulSingle k₁ ζ) (mulSingle_mem hζroot)
    obtain ⟨τ₃, hτ₃W, hτ₃⟩ := exists_mem_of_pair hp hpK hWp hW1 hst hsk1 hk1t hpair hWc
      (fun k => if k ∈ S then ζ else 1) (fun k => by
        split_ifs
        · exact hζroot
        · exact (rootsOfUnity p K).one_mem)
    have hτ₁S : ∀ i ∈ S, τ₁ i = 1 := by
      intro i hi
      have hsF : s ∈ freeSet t k₂ := mem_freeSet_iff.mpr ⟨hsk2, hst⟩
      by_cases hit : i = t
      · rw [hit, ← hpair τ₁ hτ₁W, hτ₁ s hsF, Pi.mulSingle_eq_of_ne hsk1]
      · have hik2 : i ≠ k₂ := fun h' => h2 (h' ▸ hi)
        have hik1 : i ≠ k₁ := fun h' => h1 (h' ▸ hi)
        rw [hτ₁ i (mem_freeSet_iff.mpr ⟨hik2, hit⟩), Pi.mulSingle_eq_of_ne hik1]
    have hτ₃S : ∀ i ∈ S, τ₃ i = ζ := by
      intro i hi
      have hsF : s ∈ freeSet t k₁ := mem_freeSet_iff.mpr ⟨hsk1, hst⟩
      by_cases hit : i = t
      · rw [hit, ← hpair τ₃ hτ₃W, hτ₃ s hsF]
        simp [hsS]
      · have hik1 : i ≠ k₁ := fun h' => h1 (h' ▸ hi)
        rw [hτ₃ i (mem_freeSet_iff.mpr ⟨hik1, hit⟩)]
        simp [hi]
    have hτ₁k : τ₁ k₁ = ζ := by
      rw [hτ₁ k₁ (mem_freeSet_iff.mpr ⟨h12, hk1t⟩), Pi.mulSingle_eq_same]
    obtain ⟨m₁, hm₁⟩ := hcommD τ₁ hτ₁W fun i hi j hj => by rw [hτ₁S i hi, hτ₁S j hj]
    obtain ⟨m₃, hm₃⟩ := hcommD τ₃ hτ₃W fun i hi j hj => by rw [hτ₃S i hi, hτ₃S j hj]
    have hs1 : σx s = 1 := by
      refine eq_one_of_zpow_of_zpow_ne hp (b := σx k₁) (m := m₁) (hσxp s) (hσxp k₁) ?_ ?_
      · have e1 := congrFun hm₁ s
        rw [Pi.pow_apply, hτ₁S s hsS] at e1
        exact e1.symm
      · have e1 := congrFun hm₁ k₁
        rw [Pi.pow_apply, hτ₁k] at e1
        rw [← e1]
        exact hζ1
    apply hζ1
    have e1 := congrFun hm₃ s
    rw [Pi.pow_apply, hτ₃S s hsS, hs1, _root_.one_zpow] at e1
    exact e1
  have hex : ∃ c', c' ∉ S := by
    by_contra hall
    push Not at hall
    exact hx1 (projMk_eq_one_of_const hσx (u := σx s) fun i => (hmemS i).mp (hall i))
  obtain ⟨c', hc'⟩ := hex
  have hc's : c' ≠ s := fun h' => hc' (h' ▸ hsS)
  have hc't : c' ≠ t := fun h' => hc' (h' ▸ htS)
  have hnotS : ∀ k, k ∉ S ↔ k = c' := fun k =>
    ⟨fun hk => hone k c' hk hc', fun hk => hk ▸ hc'⟩
  have hd5 : 5 ≤ d := by
    have h1 := card_le_of_pair hp hpK hWp hW1 hst hc's.symm hc't hpair
    rw [hW, card_diagVec hdiag] at h1
    have h4 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans h1)
    omega
  have hScard : S.card = d - 1 := by
    have h1 : S = Finset.univ.erase c' := by
      ext k
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · intro hk h'
        exact (hnotS k).mpr h' hk
      · intro hk
        by_contra hkS
        exact hk ((hnotS k).mp hkS)
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ c'), Finset.card_univ, Fintype.card_fin]
  set T := (S.erase s).erase t with hT
  have hTcard : 2 ≤ T.card := by
    rw [hT, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hst.symm, htS⟩),
      Finset.card_erase_of_mem hsS, hScard]
    omega
  obtain ⟨c, hcT, e, heT, hce⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
  have hcS : c ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcT)
  have heS : e ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase heT)
  have hct : c ≠ t := Finset.ne_of_mem_erase hcT
  have hcs : c ≠ s := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hcT)
  have het : e ≠ t := Finset.ne_of_mem_erase heT
  have hes : e ≠ s := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase heT)
  have hc'c : c' ≠ c := fun h' => hc' (h' ▸ hcS)
  set τ : Fin d → Kˣ := Pi.mulSingle s ζ * Pi.mulSingle t ζ * Pi.mulSingle c (ζ⁻¹ ^ 2) with hτ
  have hτs : τ s = ζ := by
    simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hst,
      Pi.mulSingle_eq_of_ne hcs.symm, mul_one]
  have hτt : τ t = ζ := by
    simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hst.symm,
      Pi.mulSingle_eq_of_ne hct.symm, mul_one, one_mul]
  have hτc : τ c = ζ⁻¹ ^ 2 := by
    simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hcs,
      Pi.mulSingle_eq_of_ne hct, one_mul]
  have hτe : τ e = 1 := by
    simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_of_ne hes, Pi.mulSingle_eq_of_ne het,
      Pi.mulSingle_eq_of_ne hce.symm, one_mul]
  have hτc' : τ c' = 1 := by
    simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_of_ne hc's, Pi.mulSingle_eq_of_ne hc't,
      Pi.mulSingle_eq_of_ne hc'c, one_mul]
  have hζQ : ζ ∈ rootsOfUnity (2 ^ n + 1) K := by
    rw [mem_rootsOfUnity]
    exact hζq
  have hτmem : ∀ X : Subgroup Kˣ, ζ ∈ X → ∀ k, τ k ∈ X := fun X hX k => by
    simp only [hτ, Pi.mul_apply]
    exact X.mul_mem (X.mul_mem (mulSingle_mem hX k) (mulSingle_mem hX k))
      (mulSingle_mem (X.pow_mem (X.inv_mem hX) 2) k)
  have hτq : ∀ k, τ k ^ (2 ^ n + 1) = 1 := fun k => by
    have h1 := hτmem _ hζQ k
    rwa [mem_rootsOfUnity] at h1
  have hτp : τ ^ p = 1 := by
    funext k
    have h1 := hτmem _ hζroot k
    rw [mem_rootsOfUnity] at h1
    rw [Pi.pow_apply, h1, Pi.one_apply]
  have hτprod : ∏ k, τ k = 1 := by
    simp only [hτ, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
    group
  set yt : ↥(unitarySU 2 n K d) := ⟨diagHom d τ, diagHom_mem_unitarySU h hτq hτprod⟩ with hyt
  have hytv : (yt : GL (Fin d) K) = diagHom d τ := rfl
  have hytS : yt ∈ blockSU S := isBlockOn_diagHom fun k hk => by
    rw [(hnotS k).mp hk, hτc']
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one (by omega) hpq
  refine ⟨π yt, ⟨yt, hytS, rfl⟩, ?_, ?_, ?_, π (swapSU h c e),
    ⟨_, isBlockOn_permGL_swap hcS heS, rfl⟩, ?_⟩
  · rw [← map_pow]
    have h1 : yt ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hytv, ← map_pow, hτp, map_one]
      rfl
    rw [h1, map_one]
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨σ', hσ'⟩ := hdiag y hy
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hσ', hytv]
    exact (diagHom_commute σ' τ).eq
  · have hwt : swapSU h s t * yt = yt * swapSU h s t :=
      commute_swapSU h hytv (by rw [hτs, hτt])
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [← map_mul, ← map_mul, (Commute.zpow_left hwt m).eq]
  · intro hcomm
    have hz : π (swapSU h c e * yt * (swapSU h c e)⁻¹ * yt⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
      group
    obtain ⟨u, hu⟩ := exists_scalar_of_projMk_eq_one hz
    have hzv : ((swapSU h c e * yt * (swapSU h c e)⁻¹ * yt⁻¹ : ↥(unitarySU 2 n K d)) :
        GL (Fin d) K) = diagHom d ((τ ∘ (Equiv.swap c e).symm) * τ⁻¹) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_inv]
      show permGL (Equiv.swap c e) * diagHom d τ * (permGL (Equiv.swap c e))⁻¹ *
        (diagHom d τ)⁻¹ = _
      rw [permGL_mul_diagHom_mul_inv, ← map_inv, ← map_mul]
    have e1 := hu s s
    have e2 := hu c c
    rw [hzv, diagHom_apply_self] at e1 e2
    simp only [↓reduceIte] at e1 e2
    have e3 : ((τ ∘ (Equiv.swap c e).symm) * τ⁻¹) s = ((τ ∘ (Equiv.swap c e).symm) * τ⁻¹) c :=
      Units.ext (e1.trans e2.symm)
    simp only [Pi.mul_apply, Pi.inv_apply, Function.comp_apply, Equiv.symm_swap,
      Equiv.swap_apply_of_ne_of_ne hcs.symm hes.symm, Equiv.swap_apply_left, hτc, hτe,
      mul_inv_cancel, one_mul, inv_pow, inv_inv] at e3
    have h2 : ζ ^ 2 = 1 := e3.symm
    have h4 := orderOf_dvd_of_pow_eq_one h2
    rw [hζo] at h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)

end Diag

section Transport

variable {R R' : Type} [Group R] [Group R']

theorem ggStdSubNormEltData_of_mulEquiv {p : ℕ} (e : R ≃* R') {A : Subgroup R} {a : R}
    (h : GGStdSubNormEltData p (A.map e.toMonoidHom) (e a)) : GGStdSubNormEltData p A a := by
  obtain ⟨D, hDC, hDn, hDq, U, hUD, hU1, hU2, hAU, hrest⟩ := h
  have hmemA : ∀ s ∈ A, e s ∈ A.map e.toMonoidHom := fun s hs => ⟨s, hs, rfl⟩
  have hmap : ∀ {X : Subgroup R'} {x : R}, x ∈ X.map e.symm.toMonoidHom ↔ e x ∈ X := by
    intro X x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e x, hx, by simp⟩
  refine ⟨D.map e.symm.toMonoidHom, ?_, ?_, ?_, U.map e.symm.toMonoidHom, Subgroup.map_mono hUD,
    ?_, hU2.map _, ?_, fun hprov => ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    have h1 := hDC hd
    rw [← e.apply_symm_apply d] at h1
    exact StdSubSp.symm_mem_centralizer_singleton e (by simpa using h1)
  · intro c hc d hd
    rw [hmap] at hd ⊢
    rw [map_mul, map_mul, map_inv]
    exact hDn (e c) (StdSubSp.apply_mem_centralizer_singleton e hc) (e d) hd
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (D.equivMapOfInjective _ e.symm.injective) hDq
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective]
    exact hU1
  · intro s hs u hu
    rw [hmap] at hu ⊢
    rw [map_mul, map_mul, map_inv]
    exact hAU (e s) (hmemA s hs) (e u) hu
  · have hprov' : ∀ b ∈ A.map e.toMonoidHom, (∀ d ∈ D, b * d = d * b) →
        b ∈ Subgroup.zpowers (e a) := by
      rintro _ ⟨b, hb, rfl⟩ hbD
      have h1 := hprov b hb (by
        rintro _ ⟨d, hd, rfl⟩
        apply e.injective
        have h2 := hbD d hd
        simpa using h2)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [← hk, map_zpow]
      rfl
    obtain ⟨t, htD, htp, htA, htU, j, hjD, hj⟩ := hrest hprov'
    refine ⟨e.symm t, ⟨t, htD, rfl⟩, ?_, ?_, ?_, e.symm j, ⟨j, hjD, rfl⟩, ?_⟩
    · rw [← map_pow, htp, map_one]
    · intro s hs
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact htA (e s) (hmemA s hs)
    · rw [Subgroup.mem_normalizer_iff] at htU ⊢
      intro x
      rw [hmap, hmap, map_mul, map_mul, map_inv, e.apply_symm_apply]
      exact htU (e x)
    · intro h1
      apply hj
      have := congrArg e h1
      simpa using this

end Transport

section Main

variable {K : Type} [Field K] [Finite K] {n d p : ℕ} (h : UnitaryFieldData 2 n K)

include h in
theorem ggStdSubTwoTorusEltNorm_unitary (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) :
    GGStdSubTwoTorusEltNorm p (d - 2) (LargeEvenProj (unitarySU 2 n K d)) := by
  intro Ab hAb hr h3 hU a haAb ha1
  set π := LargeEvenProjMk (unitarySU 2 n K d) with hπ
  have hnp : ∀ z ∈ π.ker, z ^ p = 1 → z = 1 := fun z hz hzp =>
    eq_one_of_mem_suScalars h hp hpd hz hzp
  obtain ⟨A, hmap, -, hA, hcardA⟩ :=
    exists_lift_of_noTorsion π (QuotientGroup.mk'_surjective _) hp hnp hAb
  obtain ⟨P, hP, hdiag⟩ := exists_conj_diag h hp hpq hA
  set c := conjSU h P hP with hc
  set A' := A.map (c : ↥(unitarySU 2 n K d) →* ↥(unitarySU 2 n K d)) with hA'
  have hA'ab : IsElemAbelian p A' := by
    have := isElemAbelian_range (H := A) (p := p)
      (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
      (fun a => Subtype.ext (by simpa using hA.2 a a.2))
      ((c : ↥(unitarySU 2 n K d) →* ↥(unitarySU 2 n K d)).comp A.subtype)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at this
  have hdiag' : ∀ x ∈ A', ∃ σ : Fin d → Kˣ, (x : GL (Fin d) K) = diagHom d σ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hdiag x hx
  have hcard' : Nat.card A' = Nat.card Ab := by
    rw [hA', ← hcardA]
    exact (Nat.card_congr (A.equivMapOfInjective _ c.injective).toEquiv).symm
  set cR := conjProj h P hP with hcR
  have hmap' : A'.map π = Ab.map (cR : LargeEvenProj (unitarySU 2 n K d) →*
      LargeEvenProj (unitarySU 2 n K d)) := by
    rw [← hmap, hA', Subgroup.map_map, Subgroup.map_map]
    congr 1
  obtain ⟨U, hU1, hU2, hAU⟩ := hU
  set U' := U.map (cR : LargeEvenProj (unitarySU 2 n K d) →* LargeEvenProj (unitarySU 2 n K d))
    with hU'
  have hU'1 : U' ≠ ⊥ := by
    intro hbot
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    have h1 : cR u ∈ U' := ⟨u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact cR.injective (h1.trans (map_one cR).symm)
  have hBU' : A'.map π ≤ Subgroup.normalizer (U' : Set _) := by
    rw [hmap']
    exact (Subgroup.map_mono hAU).trans (Subgroup.le_normalizer_map _)
  obtain ⟨s, t, hst, hpairF⟩ := SURepair.exists_framePair_of_twoSubgroup h
    (ker_projMk_le_center (n := n) (d := d) (K := K)) hU'1 (hU2.map _)
    (fun u _ => QuotientGroup.mk'_surjective _ u) hBU'
  have hpair : ∀ σ ∈ diagVec A', σ s = σ t := by
    intro σ hσ
    obtain ⟨x, hx, hxσ⟩ := mem_diagVec.mp hσ
    obtain ⟨hpow, -⟩ := diagVec_props h hA'ab hσ
    refine hpairF (π x) ⟨x, hx, rfl⟩ σ ⟨fun i => ?_, fun u u' hu' => ?_⟩
    · obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, ← Units.val_pow_eq_pow_val, hpow i, Units.val_one, one_pow]
    · have hu'' : u' = x * u * x⁻¹ := by
        apply Subtype.ext
        rw [hu', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hxσ]
      rw [hu'', map_mul, map_mul, map_inv]
  have hcRa : cR a ∈ A'.map π := by
    rw [hmap']
    exact ⟨a, haAb, rfl⟩
  obtain ⟨x, hxA', hxa⟩ := hcRa
  have hx1 : π x ≠ 1 := by
    rw [hxa]
    intro h1
    exact ha1 (cR.injective (h1.trans (map_one cR).symm))
  have hdata := ggStdSubNormEltData_diag h hK hn hp hpq hpd hA'ab hdiag' (hcard' ▸ hr)
    (hcard' ▸ h3) hst hpair hxA' hx1
  rw [hmap', hxa] at hdata
  exact ggStdSubNormEltData_of_mulEquiv cR hdata

include h in
theorem ggStdSubTwoTorusNorm_unitary (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) (hd : 3 ≤ d)
    (hZ : GGCenterPrime p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :
    GGStdSubTwoTorusNorm p (d - 2) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n))) ∧
      GGStdSubTwoTorusDelta p (d - 2) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro he
    have h1 : 2 ^ n = 2 := congrArg Prod.snd he
    have h2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hO : GGOutdiagPrime p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := fun φ hφ hφp =>
    TableBUE.mem_range_conj_of_pow_eq_one h hK hd hdq hp hpq hpd hφ hφp
  exact ⟨ggStdSubTwoTorusNorm_of_elt hp hO (TableBUE.center_proj_eq_bot hK hd hdq) hZ
      (ggStdSubTwoTorusEltNorm_unitary h hK hn hp hpq hpd),
    ggStdSubTwoTorusDelta_of_prime hO hZ⟩

include h in
theorem ggStdSubTwoTorusEltNorm_unitary_of_le_four (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hpd : ¬ p ∣ d) (hd3 : 3 ≤ d) (hd4 : d ≤ 4) :
    GGStdSubTwoTorusEltNorm p (d - 2) (LargeEvenProj (unitarySU 2 n K d)) := by
  classical
  intro Ab hAb _ h3 hU a _ _
  exfalso
  set π := LargeEvenProjMk (unitarySU 2 n K d) with hπ
  have hK := h.card_eq_sq
  have hpK := dvd_card_sub_one hK hpq
  have hnp : ∀ z ∈ π.ker, z ^ p = 1 → z = 1 := fun z hz hzp =>
    eq_one_of_mem_suScalars h hp hpd hz hzp
  obtain ⟨A, hmap, -, hA, hcardA⟩ :=
    exists_lift_of_noTorsion π (QuotientGroup.mk'_surjective _) hp hnp hAb
  obtain ⟨P, hP, hdiag⟩ := exists_conj_diag h hp hpq hA
  set c := conjSU h P hP with hc
  set A' := A.map (c : ↥(unitarySU 2 n K d) →* ↥(unitarySU 2 n K d)) with hA'
  have hA'ab : IsElemAbelian p A' := by
    have := isElemAbelian_range (H := A) (p := p)
      (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
      (fun a => Subtype.ext (by simpa using hA.2 a a.2))
      ((c : ↥(unitarySU 2 n K d) →* ↥(unitarySU 2 n K d)).comp A.subtype)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at this
  have hdiag' : ∀ x ∈ A', ∃ σ : Fin d → Kˣ, (x : GL (Fin d) K) = diagHom d σ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hdiag x hx
  have hcard' : Nat.card A' = Nat.card Ab := by
    rw [hA', ← hcardA]
    exact (Nat.card_congr (A.equivMapOfInjective _ c.injective).toEquiv).symm
  set cR := conjProj h P hP with hcR
  have hmap' : A'.map π = Ab.map (cR : LargeEvenProj (unitarySU 2 n K d) →*
      LargeEvenProj (unitarySU 2 n K d)) := by
    rw [← hmap, hA', Subgroup.map_map, Subgroup.map_map]
    congr 1
  obtain ⟨U, hU1, hU2, hAU⟩ := hU
  set U' := U.map (cR : LargeEvenProj (unitarySU 2 n K d) →* LargeEvenProj (unitarySU 2 n K d))
    with hU'
  have hU'1 : U' ≠ ⊥ := by
    intro hbot
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    have h1 : cR u ∈ U' := ⟨u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact cR.injective (h1.trans (map_one cR).symm)
  have hBU' : A'.map π ≤ Subgroup.normalizer (U' : Set _) := by
    rw [hmap']
    exact (Subgroup.map_mono hAU).trans (Subgroup.le_normalizer_map _)
  obtain ⟨s, t, hst, hpairF⟩ := SURepair.exists_framePair_of_twoSubgroup h
    (ker_projMk_le_center (n := n) (d := d) (K := K)) hU'1 (hU2.map _)
    (fun u _ => QuotientGroup.mk'_surjective _ u) hBU'
  have hpair : ∀ σ ∈ diagVec A', σ s = σ t := by
    intro σ hσ
    obtain ⟨x, hx, hxσ⟩ := mem_diagVec.mp hσ
    obtain ⟨hpow, -⟩ := diagVec_props h hA'ab hσ
    refine hpairF (π x) ⟨x, hx, rfl⟩ σ ⟨fun i => ?_, fun u u' hu' => ?_⟩
    · obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, ← Units.val_pow_eq_pow_val, hpow i, Units.val_one, one_pow]
    · have hu'' : u' = x * u * x⁻¹ := by
        apply Subtype.ext
        rw [hu', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hxσ]
      rw [hu'', map_mul, map_mul, map_inv]
  obtain ⟨c₀, hcs, hct⟩ : ∃ c₀ : Fin d, c₀ ≠ s ∧ c₀ ≠ t := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin d)) ⊆ {s, t} := fun c₀ _ => by
      by_cases hcs : c₀ = s
      · simp [hcs]
      · simp [hcon c₀ hcs]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have h2 : ({s, t} : Finset (Fin d)).card ≤ 2 := Finset.card_le_two
    omega
  have hWp : ∀ σ ∈ diagVec A', ∀ k, σ k ∈ rootsOfUnity p K := fun σ hσ k => by
    rw [mem_rootsOfUnity]
    exact (diagVec_props h hA'ab hσ).1 k
  have hW1 : ∀ σ ∈ diagVec A', ∏ k, (σ k : K) = 1 := fun σ hσ => (diagVec_props h hA'ab hσ).2
  have h1 := card_le_of_pair hp hpK hWp hW1 hst hcs.symm hct hpair
  rw [card_diagVec hdiag', hcard'] at h1
  have h4 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans h1)
  omega

include h in
theorem ggStdSubTwoTorusNorm_unitary_of_le_four (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) (hd : 3 ≤ d) (hd4 : d ≤ 4)
    (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hZ : GGCenterPrime p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :
    GGStdSubTwoTorusNorm p (d - 2) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n))) ∧
      GGStdSubTwoTorusDelta p (d - 2) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have hO : GGOutdiagPrime p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := fun φ hφ hφp =>
    TableBUE.mem_range_conj_of_pow_eq_one h hK hd hdq hp hpq hpd hφ hφp
  exact ⟨ggStdSubTwoTorusNorm_of_elt hp hO (TableBUE.center_proj_eq_bot hK hd hdq) hZ
      (ggStdSubTwoTorusEltNorm_unitary_of_le_four h hp hpq hpd hd hd4),
    ggStdSubTwoTorusDelta_of_prime hO hZ⟩

end Main

end StdSubRestU

end CFSG.StandardType

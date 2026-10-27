module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepMain

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
open CFSG.RankThree.Classical (permGL)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

namespace SUNS

variable {G : Type} [Group G] {n f : ℕ} {F : Type} [Field F]

@[expose] def midSet (n d : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun c => d ≤ (c : ℕ) ∧ (c : ℕ) < n - d

theorem mem_midSet {d : ℕ} {c : Fin n} : c ∈ midSet n d ↔ d ≤ (c : ℕ) ∧ (c : ℕ) < n - d := by
  simp [midSet]

theorem commute_permGL_of_isBlockOn {T : Finset (Fin n)} {a : Matrix (Fin n) (Fin n) F}
    (ha : TableBUE.IsBlockOn T a) {τ : Equiv.Perm (Fin n)} (hτ : ∀ x ∈ T, τ x = x) :
    a * ((permGL τ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((permGL τ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * a := by
  have hτT : ∀ x, τ x ∈ T ↔ x ∈ T := by
    intro x
    constructor
    · intro hx
      have h1 := hτ (τ x) hx
      rw [τ.injective h1] at hx
      exact hx
    · intro hx
      rw [hτ x hx]
      exact hx
  have hτi : ∀ x, τ⁻¹ x ∈ T ↔ x ∈ T := fun x => by
    rw [← hτT (τ⁻¹ x)]
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [TableBUE.permGL_apply]
  have e1 : ∑ k, a i k * (if τ⁻¹ k = j then (1 : F) else 0) = a i (τ j) := by
    have h : ∀ k, (τ⁻¹ k = j) ↔ (k = τ j) := fun k => Equiv.Perm.inv_eq_iff_eq
    simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have e2 : ∑ k, (if τ⁻¹ i = k then (1 : F) else 0) * a k j = a (τ⁻¹ i) j := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [e1, e2]
  by_cases hj : j ∈ T
  · rw [hτ j hj]
    by_cases hi : i ∈ T
    · have : τ⁻¹ i = i := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact (hτ i hi).symm
      rw [this]
    · have hi' : τ⁻¹ i ∉ T := by rwa [hτi]
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      have hij' : τ⁻¹ i ≠ j := fun h => hi' (h ▸ hj)
      rw [ha i j (Or.inl hi), ha (τ⁻¹ i) j (Or.inl hi'), one_apply_ne hij, one_apply_ne hij']
  · have hτj : τ j ∉ T := by rwa [hτT]
    rw [ha i (τ j) (Or.inr hτj), ha (τ⁻¹ i) j (Or.inr hj), one_apply, one_apply]
    congr 1
    apply propext
    constructor
    · intro h
      rw [h]
      simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
    · intro h
      rw [← h]
      simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]

theorem commute_of_isBlockOn_compl {S : Finset (Fin n)} {x a : Matrix (Fin n) (Fin n) F}
    (hx : TableBUE.IsBlockOn S x) (ha : TableBUE.IsBlockOn Sᶜ a) : x * a = a * x := by
  ext i j
  by_cases hj : j ∈ S
  · rw [TableBUE.IsBlockOn.mul_apply_right ha i (by simpa using hj)]
    by_cases hi : i ∈ S
    · rw [TableBUE.IsBlockOn.mul_apply_left ha (by simpa using hi) j]
    · have hij : i ≠ j := fun h => hi (h ▸ hj)
      rw [hx i j (Or.inl hi), one_apply_ne hij, Matrix.mul_apply]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      by_cases hk : k ∈ S
      · have hik : i ≠ k := fun h => hi (h ▸ hk)
        rw [ha i k (Or.inr (by simpa using hk)), one_apply_ne hik, zero_mul]
      · have hkj : k ≠ j := fun h => hk (h ▸ hj)
        rw [hx k j (Or.inl hk), one_apply_ne hkj, mul_zero]
  · rw [TableBUE.IsBlockOn.mul_apply_right hx i hj]
    by_cases hi : i ∈ S
    · have hij : i ≠ j := fun h => hj (h ▸ hi)
      rw [ha i j (Or.inl (by simpa using hi)), one_apply_ne hij, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k ∈ S
      · have hkj : k ≠ j := fun h => hj (h ▸ hk)
        rw [ha k j (Or.inl (by simpa using hk)), one_apply_ne hkj, mul_zero]
      · have hik : i ≠ k := fun h => hk (h ▸ hi)
        rw [hx i k (Or.inr hk), one_apply_ne hik, zero_mul]
    · rw [TableBUE.IsBlockOn.mul_apply_left hx hi j]

theorem entry_eq_zero_of_commute {S : Finset (Fin n)} {a c : Matrix (Fin n) (Fin n) F}
    (ha : TableBUE.IsBlockOn Sᶜ a) (hV : ∀ v : Fin n → F, a *ᵥ v = v → ∀ k ∉ S, v k = 0)
    (hV' : ∀ v : Fin n → F, v ᵥ* a = v → ∀ k ∉ S, v k = 0) (hc : c * a = a * c)
    (i j : Fin n) (hij : i ∈ S ↔ j ∉ S) : c i j = 0 := by
  by_cases hi : i ∈ S
  · have hj : j ∉ S := hij.mp hi
    refine hV' (fun k => c i k) ?_ j hj
    funext k
    have h1 : (c * a) i k = c i k := by
      rw [hc, TableBUE.IsBlockOn.mul_apply_left ha (by simpa using hi) k]
    rw [Matrix.mul_apply] at h1
    simp only [Matrix.vecMul, dotProduct]
    exact h1
  · have hj : j ∈ S := by
      by_contra hj
      exact hi (hij.mpr hj)
    refine hV (fun k => c k j) ?_ i hi
    funext k
    have h1 : (a * c) k j = c k j := by
      rw [← hc, TableBUE.IsBlockOn.mul_apply_right ha k (by simpa using hj)]
    rw [Matrix.mul_apply] at h1
    simp only [Matrix.mulVec, dotProduct]
    exact h1

theorem eq_one_of_scalar_mem [Finite F] (h : UnitaryFieldData 2 f F) {p : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ 2 ^ f + 1) {z : ↥(unitarySU 2 f F n)} {c : F} (i : Fin n)
    (hc : ((z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) c)
    (hzp : z ^ p = 1) : z = 1 := by
  have hcp : c ^ p = 1 := by
    have h1 := congrArg (fun t : ↥(unitarySU 2 f F n) =>
      ((t : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i) hzp
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hc, OneMemClass.coe_one,
      Units.val_one, one_apply_eq] at h1
    rwa [Matrix.scalar_apply, diagonal_pow, diagonal_apply_eq] at h1
  have hcq : c ^ (2 ^ f + 1) = 1 := by
    obtain ⟨-, hu⟩ := (mem_unitarySU_iff h).mp z.2
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i i) hu
    simp only [hc, Matrix.scalar_apply, one_apply_eq] at h1
    rw [diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
      diagonal_apply_eq, UnitaryFieldData.bar_apply] at h1
    rw [pow_succ]
    exact h1
  have hcop : p.gcd (2 ^ f + 1) = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpq
  have hc1 : c = 1 := by
    have h2 := pow_gcd_eq_one.mpr ⟨hcp, hcq⟩
    rwa [hcop, pow_one] at h2
  apply Subtype.ext
  apply Units.ext
  rw [hc, hc1, map_one]
  rfl

theorem commute_of_frame_commute [Finite F] (h : UnitaryFieldData 2 f F)
    {φ : ↥(unitarySU 2 f F n) →* G} (hker : SURep.GGFrameKer φ) {p : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ 2 ^ f + 1) {a s : ↥(unitarySU 2 f F n)} (hap : a ^ p = 1)
    (hcomm : φ a * φ s = φ s * φ a) : a * s = s * a := by
  rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
  · apply Subtype.ext
    apply Units.ext
    ext x
    exact isEmptyElim x
  set z := (s * a)⁻¹ * (a * s) with hz
  have hz1 : φ z = 1 := by
    rw [hz, map_mul, map_inv, map_mul, map_mul, hcomm, inv_mul_cancel]
  obtain ⟨c, hc⟩ := hker z hz1
  have hzc : ∀ g : ↥(unitarySU 2 f F n), g * z = z * g := by
    intro g
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hc]
    rw [scalar_commute c (fun _ => mul_comm _ _)]
  have has : a * s = s * a * z := by rw [hz]; group
  have hconj : s⁻¹ * a * s = a * z := by
    calc s⁻¹ * a * s = s⁻¹ * (a * s) := by group
      _ = s⁻¹ * (s * a * z) := by rw [has]
      _ = a * z := by group
  have hzp : z ^ p = 1 := by
    have h1 : (s⁻¹ * a * s) ^ p = (a * z) ^ p := by rw [hconj]
    have h2 : (s⁻¹ * a * s) ^ p = s⁻¹ * a ^ p * s := by
      have := _root_.conj_pow (a := s⁻¹) (b := a) (i := p)
      rwa [inv_inv] at this
    have h3 : (a * z) ^ p = a ^ p * z ^ p := (Commute.mul_pow (hzc a) p)
    rw [h2, h3, hap, mul_one, inv_mul_cancel, one_mul] at h1
    exact h1.symm
  rw [has, eq_one_of_scalar_mem h hp hpq i hc hzp, mul_one]

theorem range_inf_centralizer_eq_map [Finite F] (h : UnitaryFieldData 2 f F)
    {φ : ↥(unitarySU 2 f F n) →* G} (hker : SURep.GGFrameKer φ) {p : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ 2 ^ f + 1) {a : ↥(unitarySU 2 f F n)} (hap : a ^ p = 1) :
    φ.range ⊓ Subgroup.centralizer {φ a} = (Subgroup.centralizer {a}).map φ := by
  ext g
  simp only [Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨s, rfl⟩, hs⟩
    exact ⟨s, (commute_of_frame_commute h hker hp hpq hap hs.symm).symm, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, rfl⟩, by rw [← map_mul, ← map_mul, hs]⟩

theorem isComponentOf_map_blockSU_of_fix [Finite F] (hF : Nat.card F = (2 ^ f) ^ 2)
    (h : UnitaryFieldData 2 f F) {φ : ↥(unitarySU 2 f F n) →* G} (hker : SURep.GGFrameKer φ)
    {p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ 2 ^ f + 1) {a : ↥(unitarySU 2 f F n)} (hap : a ^ p = 1)
    {S : Finset (Fin n)}
    (ha : TableBUE.IsBlockOn Sᶜ ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (hV : ∀ v : Fin n → F, ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v = v →
      ∀ k ∉ S, v k = 0)
    (hV' : ∀ v : Fin n → F, v ᵥ* ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = v →
      ∀ k ∉ S, v k = 0)
    (hS3 : 3 ≤ S.card) (hSq : (S.card, 2 ^ f) ≠ (3, 2)) {i₀ : Fin n} (hi₀ : i₀ ∉ S) :
    IsComponentOf ((TableBUE.blockSU (K := F) (n := f) S).map φ)
      (φ.range ⊓ Subgroup.centralizer {φ a}) := by
  rw [range_inf_centralizer_eq_map h hker hp hpq hap]
  set C := Subgroup.centralizer {a} with hC
  set J₀ := TableBUE.blockSU (K := F) (n := f) S with hJ₀
  have hmat : ∀ c ∈ C, ((c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((c : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) := by
    intro c hc
    have h1 := (Subgroup.mem_centralizer_singleton_iff.mp hc)
    rw [← Units.val_mul, ← Units.val_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, h1]
  have hJ₀C : J₀ ≤ C := by
    intro x hx
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
    exact commute_of_isBlockOn_compl hx ha
  have hJn : ∀ c ∈ C, ∀ j ∈ J₀, c * j * c⁻¹ ∈ J₀ := by
    intro c hc j hj
    have hc' : c⁻¹ ∈ C := C.inv_mem hc
    change TableBUE.IsBlockOn S ((((c * j * c⁻¹ : ↥(unitarySU 2 f F n)) : GL (Fin n) F)) :
      Matrix (Fin n) (Fin n) F)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
    refine SURep.isBlockOn_conj (fun i k hik => entry_eq_zero_of_commute ha hV hV' (hmat c hc) i k hik)
      (fun i k hik => entry_eq_zero_of_commute ha hV hV' (hmat c⁻¹ hc') i k hik) ?_ hj
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  have hinj : ∀ j ∈ J₀, φ j = 1 → j = 1 := by
    intro j hj h1
    obtain ⟨c, hc⟩ := hker j h1
    have hii := hj i₀ i₀ (Or.inl hi₀)
    rw [hc, Matrix.scalar_apply, diagonal_apply_eq, Matrix.one_apply_eq] at hii
    apply Subtype.ext
    apply Units.ext
    rw [hc, hii, map_one, Subgroup.coe_one, Units.val_one]
  have hq : CFSG.IsQuasisimple J₀ := TableBUE.isQuasisimple_blockSU S h hF hS3 hSq
  have hinj' : Function.Injective (φ.comp J₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  have hrange : (φ.comp J₀.subtype).range = J₀.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hJq : CFSG.IsQuasisimple (J₀.map φ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MonoidHom.ofInjective hinj').trans (MulEquiv.subgroupCongr hrange)) hq
  have hJF : J₀.map φ ≤ C.map φ := Subgroup.map_mono hJ₀C
  have hJn' : ((J₀.map φ).subgroupOf (C.map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJF]
    rintro _ g ⟨j, hj, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨c * j * c⁻¹, hJn c hc j hj, by rw [map_mul, map_mul, map_inv]⟩
  exact ⟨hJF, IsSubnormal.step hJF hJn' (IsSubnormal.refl _),
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hJq⟩

theorem card_midSet (n d : ℕ) : (midSet n d).card = n - 2 * d := by
  have h : (midSet n d).map Fin.valEmbedding = Finset.Ico d (n - d) := by
    ext x
    simp only [Finset.mem_map, mem_midSet, Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact hc
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, h, Nat.card_Ico]
  omega

@[expose] def pairSupp (n l : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun c => (c : ℕ) < l ∨ (Fin.rev c : ℕ) < l

theorem card_pairSupp_le (n l : ℕ) : (pairSupp n l).card ≤ 2 * l := by
  have h1 : pairSupp n l ⊆ (Finset.univ.filter fun c : Fin n => (c : ℕ) < l) ∪
      (Finset.univ.filter fun c : Fin n => (Fin.rev c : ℕ) < l) := by
    intro c hc
    simp only [pairSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hc
  have h2 : (Finset.univ.filter fun c : Fin n => (c : ℕ) < l).card ≤ l := by
    have := Finset.card_le_card_of_injOn (fun c : Fin n => (c : ℕ))
      (s := Finset.univ.filter fun c : Fin n => (c : ℕ) < l)
      (t := Finset.range l) (fun c hc => by simpa using hc) (fun a _ b _ h => Fin.ext h)
    simpa using this
  have h3 : (Finset.univ.filter fun c : Fin n => (Fin.rev c : ℕ) < l).card ≤ l := by
    have := Finset.card_le_card_of_injOn (fun c : Fin n => (Fin.rev c : ℕ))
      (s := Finset.univ.filter fun c : Fin n => (Fin.rev c : ℕ) < l)
      (t := Finset.range l) (fun c hc => by simpa using hc)
      (fun a _ b _ h => Fin.rev_injective (Fin.ext h))
    simpa using this
  calc (pairSupp n l).card ≤ _ := Finset.card_le_card h1
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 2 * l := by omega

theorem ggPairPerm_eq_self_of_not_mem {l : ℕ} {c : Fin n} (hc : c ∉ pairSupp n l) :
    SURep.ggPairPerm n l c = c := by
  simp only [pairSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  rw [SURep.ggPairPerm_apply, SURep.ggPairInv, ite_eq_right hc]

theorem exists_perm_conj_fix {d l : ℕ} (hl : 2 * l ≤ (midSet n d).card) :
    ∃ ρ : Equiv.Perm (Fin n), ∀ x ∈ (midSet n d)ᶜ, (ρ * SURep.ggPairPerm n l * ρ⁻¹) x = x := by
  classical
  set X := pairSupp n l with hX
  obtain ⟨T, hTM, hTc⟩ := Finset.exists_subset_card_eq ((card_pairSupp_le n l).trans hl)
  let eqv : {x // x ∈ X} ≃ {x // x ∈ T} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hTc])
  refine ⟨eqv.extendSubtype, fun y hy => ?_⟩
  have hyT : y ∉ T := fun h => (Finset.mem_compl.mp hy) (hTM h)
  have hnX : eqv.extendSubtype⁻¹ y ∉ X := by
    intro h
    apply hyT
    have := eqv.extendSubtype_mem _ h
    simpa using this
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ggPairPerm_eq_self_of_not_mem hnX]
  simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]

theorem ggPairPerm_mul_fix {d l : ℕ} (hdl : d ≤ l) :
    ∀ x ∈ (midSet n d)ᶜ, (SURep.ggPairPerm n d * SURep.ggPairPerm n l) x = x := by
  intro x hx
  have hx' : (x : ℕ) < d ∨ n - d ≤ (x : ℕ) := by
    rw [Finset.mem_compl, mem_midSet] at hx
    omega
  have hrev : (Fin.rev x : ℕ) = n - 1 - x := by rw [Fin.val_rev]; omega
  have hxn := x.isLt
  have h1 : SURep.ggPairPerm n l x = Fin.rev x := by
    rw [SURep.ggPairPerm_apply, SURep.ggPairInv, ite_eq_left (by rw [hrev]; omega)]
  have h2 : SURep.ggPairPerm n d (Fin.rev x) = x := by
    rw [SURep.ggPairPerm_apply, SURep.ggPairInv, ite_eq_left (by rw [Fin.rev_rev, hrev]; omega),
      Fin.rev_rev]
  rw [Equiv.Perm.mul_apply, h1, h2]

theorem isBlockOn_pow {S : Finset (Fin n)} {M : Matrix (Fin n) (Fin n) F}
    (hM : TableBUE.IsBlockOn S M) (k : ℕ) : TableBUE.IsBlockOn S (M ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact TableBUE.IsBlockOn.one
  | succ k ih => rw [pow_succ]; exact ih.mul hM

theorem pow_eq_one_of_frame {φ : ↥(unitarySU 2 f F n) →* G} (hker : SURep.GGFrameKer φ)
    {S : Finset (Fin n)} {a : ↥(unitarySU 2 f F n)}
    (ha : TableBUE.IsBlockOn Sᶜ ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) {i : Fin n}
    (hi : i ∈ S) {p : ℕ} (hp : φ a ^ p = 1) : a ^ p = 1 := by
  obtain ⟨c, hc⟩ := hker (a ^ p) (by rw [map_pow, hp])
  have hpow := isBlockOn_pow ha p
  have h1 : ((((a ^ p : ↥(unitarySU 2 f F n)) : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) =
      ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ p := by
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
  have hii := hpow i i (Or.inl (by simpa using hi))
  rw [← h1, hc, Matrix.scalar_apply, diagonal_apply_eq, one_apply_eq] at hii
  apply Subtype.ext
  apply Units.ext
  rw [hc, hii, map_one]
  rfl

theorem frame_ne_one {φ : ↥(unitarySU 2 f F n) →* G} (hker : SURep.GGFrameKer φ)
    {S : Finset (Fin n)} {a : ↥(unitarySU 2 f F n)}
    (ha : TableBUE.IsBlockOn Sᶜ ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (hV : ∀ v : Fin n → F, ((a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v = v →
      ∀ k ∉ S, v k = 0) {i k : Fin n} (hi : i ∈ S) (hk : k ∉ S) : φ a ≠ 1 := by
  intro h1
  obtain ⟨c, hc⟩ := hker a h1
  have hii := ha i i (Or.inl (by simpa using hi))
  rw [hc, Matrix.scalar_apply, diagonal_apply_eq, one_apply_eq] at hii
  have h2 := hV (Pi.single k 1) (by rw [hc, hii, map_one, one_mulVec]) k hk
  simp at h2

end SUNS

end CFSG.StandardType

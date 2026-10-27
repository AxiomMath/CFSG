module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem commutator_normalClosure {Γ : Type} [Group Γ] {Y : Subgroup Γ}
    (hY : commutator ↥Y = ⊤) : commutator ↥(Subgroup.normalClosure (Y : Set Γ)) = ⊤ := by
  have hYY : ⁅Y, Y⁆ = Y := by
    have h := congrArg (Subgroup.map (Y.subtype : ↥Y →* Γ)) hY
    rwa [Subgroup.map_subtype_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  have hle : Y ≤ ⁅Subgroup.normalClosure (Y : Set Γ), Subgroup.normalClosure (Y : Set Γ)⁆ := by
    have hmono : ⁅Y, Y⁆ ≤
        ⁅Subgroup.normalClosure (Y : Set Γ), Subgroup.normalClosure (Y : Set Γ)⁆ :=
      Subgroup.commutator_mono Subgroup.le_normalClosure Subgroup.le_normalClosure
    rwa [hYY] at hmono
  have hfix : ⁅Subgroup.normalClosure (Y : Set Γ), Subgroup.normalClosure (Y : Set Γ)⁆ =
      Subgroup.normalClosure (Y : Set Γ) := by
    refine le_antisymm ?_ (Subgroup.normalClosure_le_normal hle)
    simpa using Subgroup.commutator_le_sup (Subgroup.normalClosure (Y : Set Γ))
      (Subgroup.normalClosure (Y : Set Γ))
  apply Subgroup.map_injective (Subgroup.normalClosure (Y : Set Γ)).subtype_injective
  rw [Subgroup.map_subtype_commutator, hfix, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem IsThreeGen.normalClosure {Γ : Type} [Group Γ] {Y : Subgroup Γ} (h : IsThreeGen Y) :
    IsThreeGen (Subgroup.normalClosure (Y : Set Γ)) := by
  set K : Subgroup Γ := Subgroup.normalClosure (Y : Set Γ) with hKdef
  haveI hKn : K.Normal := Subgroup.normalClosure_normal
  have hc : ∀ g : Γ, ∀ t : Γ, t ∈ K → (∃ k : ℕ, t ^ 3 ^ k = 1) →
      g * t * g⁻¹ ∈ K ∧ ∃ k : ℕ, (g * t * g⁻¹) ^ 3 ^ k = 1 := by
    rintro g t htK ⟨k, hk⟩
    exact ⟨hKn.conj_mem t htK g, k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
  haveI hnorm : (Subgroup.closure {a : Γ | a ∈ K ∧ ∃ k : ℕ, a ^ 3 ^ k = 1}).Normal :=
    ⟨fun n hn g => by
      induction hn using Subgroup.closure_induction with
      | mem x hx => exact Subgroup.subset_closure (hc g x hx.1 hx.2)
      | one => simp
      | mul x y hx hy ihx ihy =>
          rw [← conj_mul]
          exact Subgroup.mul_mem _ ihx ihy
      | inv x hx ihx =>
          rw [← conj_inv]
          exact Subgroup.inv_mem _ ihx⟩
  have hYgen : Y ≤ Subgroup.closure {a : Γ | a ∈ K ∧ ∃ k : ℕ, a ^ 3 ^ k = 1} := by
    have hsub : {a : Γ | a ∈ Y ∧ ∃ k : ℕ, a ^ 3 ^ k = 1} ⊆
        {a : Γ | a ∈ K ∧ ∃ k : ℕ, a ^ 3 ^ k = 1} := by
      rintro a ⟨haY, ha3⟩
      exact ⟨Subgroup.le_normalClosure haY, ha3⟩
    have h2 : Subgroup.closure {a : Γ | a ∈ Y ∧ ∃ k : ℕ, a ^ 3 ^ k = 1} ≤
        Subgroup.closure {a : Γ | a ∈ K ∧ ∃ k : ℕ, a ^ 3 ^ k = 1} :=
      Subgroup.closure_mono hsub
    have hYeq : Subgroup.closure {a : Γ | a ∈ Y ∧ ∃ k : ℕ, a ^ 3 ^ k = 1} = Y := h
    rwa [hYeq] at h2
  change Subgroup.closure {a : Γ | a ∈ K ∧ ∃ k : ℕ, a ^ 3 ^ k = 1} = K
  refine le_antisymm ((Subgroup.closure_le K).mpr fun _ ha => ha.1) ?_
  apply Subgroup.normalClosure_le_normal
  exact hYgen

theorem r925_eq_sup_of_commutator {Γ : Type} [Group Γ] {K Y W N : Subgroup Γ}
    (hK : commutator ↥K = ⊤) (hYK : Y ≤ K) (hKYW : K = Y ⊔ W) (hNK : N ≤ K)
    (hN : (N.subgroupOf K).Normal) (hWN : ∀ w ∈ W, ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ N) :
    K = Y ⊔ N := by
  haveI hKperf : Group.IsPerfect ↥K := ⟨hK⟩
  let S : Subgroup Γ := Y ⊔ N
  have hSle : S ≤ K := sup_le hYK hNK
  have hWle : W ≤ K := by rw [hKYW]; exact le_sup_right
  have hScl : S = Subgroup.closure ((Y : Set Γ) ∪ (N : Set Γ)) := by
    show Y ⊔ N = Subgroup.closure ((Y : Set Γ) ∪ (N : Set Γ))
    rw [Subgroup.sup_eq_closure]
  have hKW : K ≤ Subgroup.normalizer S := by
    rw [hKYW]
    refine sup_le ?_ ?_
    · rw [Subgroup.le_normalizer_iff]
      intro y hy k hk
      exact S.mul_mem (S.mul_mem (Subgroup.mem_sup_left hy) hk)
        (S.inv_mem (Subgroup.mem_sup_left hy))
    · have hnormeq : Subgroup.normalizer S =
          Subgroup.normalizer ((Subgroup.closure ((Y : Set Γ) ∪ (N : Set Γ)) : Subgroup Γ) :
            Set Γ) := by
        rw [hScl]
      rw [hnormeq, Subgroup.le_normalizer_closure_iff]
      intro w hw g hg
      have hwg : w * g * w⁻¹ * g⁻¹ ∈ N := by
        rcases hg with hgY | hgN
        · exact hWN w hw g (hYK hgY)
        · exact hWN w hw g (hNK hgN)
      have hconj : w * g * w⁻¹ = (w * g * w⁻¹ * g⁻¹) * g := by group
      rw [hconj]
      rcases hg with hgY | hgN
      · exact hScl ▸ S.mul_mem (Subgroup.mem_sup_right hwg) (Subgroup.mem_sup_left hgY)
      · exact hScl ▸ S.mul_mem (Subgroup.mem_sup_right hwg) (Subgroup.mem_sup_right hgN)
  haveI hSnormal : (S.subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKW
  let q : ↥K →* (↥K ⧸ S.subgroupOf K) := QuotientGroup.mk' (S.subgroupOf K)
  have hgen : Y.subgroupOf K ⊔ W.subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hYK hWle, ← hKYW, Subgroup.subgroupOf_self]
  have hqW : ∀ w : ↥K, (w : Γ) ∈ W →
      q w ∈ Subgroup.center (↥K ⧸ S.subgroupOf K) := by
    intro w hw
    rw [Subgroup.mem_center_iff]
    intro a
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (S.subgroupOf K) a
    show q k * q w = q w * q k
    rw [← map_mul, ← map_mul, eq_comm]
    show ((w * k : ↥K) : ↥K ⧸ S.subgroupOf K) = ((k * w : ↥K) : ↥K ⧸ S.subgroupOf K)
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    simpa [div_eq_mul_inv, mul_assoc] using Subgroup.mem_sup_right (hWN (w : Γ) hw (k : Γ) k.2)
  have hqY : ∀ y : ↥K, (y : Γ) ∈ Y → q y ∈ Subgroup.center (↥K ⧸ S.subgroupOf K) := by
    intro y hy
    have hyS : y ∈ S.subgroupOf K := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hy)
    have hy1 : q y = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hyS
    rw [hy1]
    exact Subgroup.one_mem _
  have hcenter : Subgroup.center (↥K ⧸ S.subgroupOf K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (S.subgroupOf K) x
    have hk : k ∈ Subgroup.closure
        ((Y.subgroupOf K : Set ↥K) ∪ (W.subgroupOf K : Set ↥K)) := by
      have htop : k ∈ Y.subgroupOf K ⊔ W.subgroupOf K := by
        rw [hgen]
        exact Subgroup.mem_top k
      rwa [Subgroup.sup_eq_closure] at htop
    refine Subgroup.closure_induction
      (p := fun z _ => q z ∈ Subgroup.center (↥K ⧸ S.subgroupOf K)) ?_ ?_ ?_ ?_ hk
    · intro z hz
      rcases hz with hzY | hzW
      · exact hqY z (Subgroup.mem_subgroupOf.mp hzY)
      · exact hqW z (Subgroup.mem_subgroupOf.mp hzW)
    · rw [map_one]; exact Subgroup.one_mem _
    · intro x y hx hy ihx ihy
      rw [map_mul]
      exact Subgroup.mul_mem _ ihx ihy
    · intro x hx ihx
      rw [map_inv]
      exact Subgroup.inv_mem _ ihx
  haveI hperf : Group.IsPerfect (↥K ⧸ S.subgroupOf K) :=
    Group.IsPerfect.ofSurjective (f := q) (QuotientGroup.mk'_surjective (S.subgroupOf K))
  haveI hcomm : IsMulCommutative (↥K ⧸ S.subgroupOf K) :=
    Subgroup.center_eq_top_iff.mp hcenter
  haveI : Subsingleton (↥K ⧸ S.subgroupOf K) :=
    Group.IsPerfect.subsingleton_of_isMulCommutative
  have hStop : S.subgroupOf K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : q x = 1 := Subsingleton.elim _ _
    rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx
  have hKS : K ≤ S := by
    intro k hk
    have hmem : (⟨k, hk⟩ : ↥K) ∈ S.subgroupOf K := by
      rw [hStop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  change K = S
  exact le_antisymm hKS hSle

theorem r925_eq_sup_inf_ker {Γ Λ : Type} [Group Γ] [Group Λ] (π : Γ →* Λ) {Y K : Subgroup Γ}
    (hYK : Y ≤ K) (h : Y.map π = K.map π) : K = Y ⊔ (K ⊓ π.ker) := by
  refine le_antisymm ?_ (sup_le hYK inf_le_left)
  intro k hk
  have hk' : π k ∈ Y.map π := by
    rw [h]
    exact ⟨k, hk, rfl⟩
  obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.mp hk'
  have hker : y⁻¹ * k ∈ π.ker := by
    show π (y⁻¹ * k) = 1
    rw [map_mul, map_inv, hyk]
    simp
  have hmem : y * (y⁻¹ * k) ∈ Y ⊔ (K ⊓ π.ker) :=
    Subgroup.mul_mem_sup hy
      (Subgroup.mem_inf.mpr ⟨K.mul_mem (K.inv_mem (hYK hy)) hk, hker⟩)
  rwa [show y * (y⁻¹ * k) = k by group] at hmem

noncomputable def r925QuotEquiv {Γ Λ : Type} [Group Γ] [Group Λ] (π : Γ →* Λ) (K : Subgroup Γ) :
    ↥K ⧸ (π.subgroupMap K).ker ≃* ↥(K.map π) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (π.subgroupMap_surjective K)

theorem r925_nonempty_equiv_map {Γ Λ : Type} [Group Γ] [Group Λ] (π : Γ →* Λ) {X : Subgroup Γ}
    (h : ∀ x ∈ X, π x = 1 → x = 1) : Nonempty (↥X ≃* ↥(X.map π)) :=
  ⟨MulEquiv.ofBijective (π.subgroupMap X) ⟨(injective_iff_map_eq_one _).2 fun x hx =>
    Subtype.ext (h x x.2 (by simpa [Subtype.ext_iff] using congrArg Subtype.val hx)),
    π.subgroupMap_surjective X⟩⟩

theorem IsL3Five.of_mulEquiv {X X' : Type} [Group X] [Group X'] (h : IsL3Five X) (e : X ≃* X') :
    IsL3Five X' :=
  CFSG.Blueprint.LieModel.of_mulEquiv e h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

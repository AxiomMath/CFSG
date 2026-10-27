module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

theorem exists_autAction {G : Type} [Group G] [Finite G] {K H L : Subgroup G}
    (hL : IsComponentModN K H L) {X : Type} [Group X] (φ : ↥L →* X)
    (hφs : Function.Surjective φ) (hφk : ∀ k : ↥L, φ k = 1 ↔ (k : G) ∈ K) :
    ∃ α : ↥(H ⊓ Subgroup.normalizer (L : Set G)) →* MulAut X,
      ∀ (n : ↥(H ⊓ Subgroup.normalizer (L : Set G))) (l l' : ↥L),
        (n : G) * (l : G) * (n : G)⁻¹ = (l' : G) → α n (φ l) = φ l' := by
  classical
  have hKL : K ≤ L := hL.2.1
  have hLH : L ≤ H := hL.2.2.1
  have hKN : (K.subgroupOf H).Normal := hL.1
  have hKconj : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
    intro h hh k hk
    have hkH : k ∈ H := hLH (hKL hk)
    have hkN : (⟨k, hkH⟩ : ↥H) ∈ K.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact hk
    have hconj := hKN.conj_mem ⟨k, hkH⟩ hkN ⟨h, hh⟩
    simpa [Subgroup.mem_subgroupOf] using hconj
  let cAut : ↥(H ⊓ Subgroup.normalizer (L : Set G)) → ↥L ≃* ↥L := fun n =>
    { toFun := fun l => ⟨(n : G) * (l : G) * (n : G)⁻¹, by
        have hn : (n : G) ∈ Subgroup.normalizer (L : Set G) := n.2.2
        exact (Subgroup.mem_set_normalizer_iff.mp hn (l : G)).mp l.2⟩
      invFun := fun l => ⟨(n : G)⁻¹ * (l : G) * (n : G), by
        have hn : (n : G) ∈ Subgroup.normalizer (L : Set G) := n.2.2
        exact (Subgroup.mem_set_normalizer_iff''.mp hn (l : G)).mp l.2⟩
      left_inv := by intro l; ext; group
      right_inv := by intro l; ext; group
      map_mul' := by
        intro a b
        ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group }
  have hcAut_apply : ∀ (n : ↥(H ⊓ Subgroup.normalizer (L : Set G))) (l : ↥L),
      (cAut n l : G) = (n : G) * (l : G) * (n : G)⁻¹ := fun n l => rfl
  have hker_iff : ∀ (n : ↥(H ⊓ Subgroup.normalizer (L : Set G))) (l : ↥L),
      φ (cAut n l) = 1 ↔ φ l = 1 := by
    intro n l
    rw [hφk (cAut n l), hφk l, hcAut_apply]
    constructor
    · intro h
      have h' := hKconj (n : G)⁻¹ (H.inv_mem n.2.1)
        ((n : G) * (l : G) * (n : G)⁻¹) h
      have h'' : (n : G)⁻¹ * ((n : G) * (l : G) * (n : G)⁻¹) * (n : G) = (l : G) := by
        group
      rw [inv_inv] at h'
      rwa [h''] at h'
    · intro h
      exact hKconj (n : G) n.2.1 (l : G) h
  have hker_map : ∀ n : ↥(H ⊓ Subgroup.normalizer (L : Set G)),
      (φ.ker).map (↑(cAut n) : ↥L →* ↥L) = φ.ker := by
    intro n
    apply le_antisymm
    · intro x hx
      obtain ⟨k, hk, hk_eq⟩ := Subgroup.mem_map.mp hx
      rw [← hk_eq]
      exact (hker_iff n k).mpr hk
    · intro x hx
      refine Subgroup.mem_map.mpr
        ⟨(cAut n).symm x, ?_, (cAut n).apply_symm_apply x⟩
      have hiff := hker_iff n ((cAut n).symm x)
      rw [MulEquiv.apply_symm_apply] at hiff
      exact hiff.mp hx
  let q : ↥(H ⊓ Subgroup.normalizer (L : Set G)) →* MulAut (↥L ⧸ φ.ker) :=
    { toFun := fun n => QuotientGroup.congr (φ.ker) (φ.ker) (cAut n) (hker_map n)
      map_one' := by
        ext x
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
        rw [QuotientGroup.congr_mk]
        congr 1
        apply Subtype.ext
        rw [hcAut_apply]
        simp
      map_mul' := by
        intro m n
        ext x
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
        rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
          QuotientGroup.congr_mk]
        congr 1
        apply Subtype.ext
        rw [hcAut_apply, hcAut_apply, hcAut_apply]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group }
  let ψ : ↥L ⧸ φ.ker ≃* X := QuotientGroup.quotientKerEquivOfSurjective φ hφs
  have hψ_mk : ∀ l : ↥L, ψ (QuotientGroup.mk l) = φ l := by
    intro l
    change QuotientGroup.kerLift φ (QuotientGroup.mk l) = φ l
    rw [QuotientGroup.kerLift_mk]
  have hψ_symm : ∀ l : ↥L, ψ.symm (φ l) = QuotientGroup.mk l := by
    intro l
    rw [← hψ_mk l, MulEquiv.symm_apply_apply]
  let αFun : ↥(H ⊓ Subgroup.normalizer (L : Set G)) → MulAut X :=
    fun n => (ψ.symm.trans (q n)).trans ψ
  have hα_apply : ∀ (n : ↥(H ⊓ Subgroup.normalizer (L : Set G))) (l : ↥L),
      αFun n (φ l) = φ (cAut n l) := by
    intro n l
    show ((ψ.symm.trans (q n)).trans ψ) (φ l) = φ (cAut n l)
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hψ_symm]
    have hq : q n (QuotientGroup.mk l) = QuotientGroup.mk (cAut n l) := by
      show QuotientGroup.congr (φ.ker) (φ.ker) (cAut n) (hker_map n)
        (QuotientGroup.mk l) = QuotientGroup.mk (cAut n l)
      rw [QuotientGroup.congr_mk]
    rw [hq, hψ_mk]
  refine ⟨{ toFun := αFun
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · apply MulEquiv.ext
    intro x
    obtain ⟨l, rfl⟩ := hφs x
    show αFun 1 (φ l) = φ l
    rw [hα_apply]
    apply congrArg φ
    apply Subtype.ext
    rw [hcAut_apply]
    simp
  · intro m n
    apply MulEquiv.ext
    intro x
    obtain ⟨l, rfl⟩ := hφs x
    show αFun (m * n) (φ l) = (αFun m * αFun n) (φ l)
    rw [MulAut.mul_apply, hα_apply, hα_apply, hα_apply]
    apply congrArg φ
    apply Subtype.ext
    rw [hcAut_apply, hcAut_apply, hcAut_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  · intro n l l' h
    change αFun n (φ l) = φ l'
    rw [hα_apply]
    apply congrArg φ
    exact Subtype.ext (by rw [hcAut_apply]; exact h)

end CFSG.LocalAnalysis.WeakClosure81

end

module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallLinTwoTv
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeNorm

public section

namespace CFSG.StandardType.SmallL2

open Polynomial Matrix CoordSL CFSG.RankThree.CALinearPlane Multiplicative CFSG CFSG.Assembly
  TableB

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {n s r : ℕ}
  (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {hC : (rootMat g).det = 1}

section Concl

variable {L' : Type} [Group L'] {A : Subgroup (MulAut L')}

theorem mem_normalizer_of_invariant {U : Subgroup L'}
    (hUA : ∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U) {x : L'} (hx : MulAut.conj x ∈ A) :
    x ∈ Subgroup.normalizer (U : Set L') := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have := hUA _ hx h hh
    simpa [MulAut.conj_apply] using this
  · intro hh
    have := hUA _ (A.inv_mem hx) _ hh
    rw [MulAut.conj_inv_apply] at this
    simpa [mul_assoc] using this

variable [CharP K 2] {ψ : Matrix.SpecialLinearGroup (Fin n) K →* L'}
  {A₀ : Matrix.SpecialLinearGroup (Fin n) K} {hCp : rootMat g ^ 3 = 1}

theorem concl_of_root (hψ : Function.Injective ψ) (hζ : AdjoinRoot.root g ^ 3 = 1)
    (hAT : ∀ a : MulAut L', a ∈ A ↔ ∃ t : Fin s → ZMod 3,
      a = MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd t)))
    {a : MulAut L'} {i j : Fin s} (h : i ≠ j)
    (hUK : ∀ x, rootHom ε (SLRep.ggFrame ψ A₀) h x ∈ LargeEvenLayer (ggFix a))
    (t₀ : Fin s → ZMod 3) (htK : frameHom ψ A₀ ε hC hCp (ofAdd t₀) ∈ LargeEvenLayer (ggFix a))
    (hne : AdjoinRoot.root g ^ (t₀ i).val * (AdjoinRoot.root g ^ 2) ^ (t₀ j).val ≠ 1) :
    GGStdSubTwoTorusConcl 3 A a := by
  set φ := SLRep.ggFrame ψ A₀ with hφ
  set ι := frameHom ψ A₀ ε hC hCp with hι
  have hφinj : Function.Injective φ := by
    intro x y hxy
    exact (MulAut.conj A₀).injective (hψ hxy)
  have hUA : ∀ a' ∈ A, ∀ u ∈ (rootHom ε φ h).range, a' u ∈ (rootHom ε φ h).range := by
    intro a' ha' u hu
    obtain ⟨t', rfl⟩ := (hAT a').mp ha'
    obtain ⟨x, rfl⟩ := hu
    rw [MulAut.conj_apply, ← ofAdd_toAdd x, hι, rootHom_conj ε hζ]
    exact ⟨_, rfl⟩
  have h1 : (1 : AdjoinRoot g) ≠ 0 := one_ne_zero
  refine ⟨(rootHom ε φ h).range, ?_, ?_, ?_, hUA, ι (ofAdd t₀), htK, ?_, ?_, ?_,
    rootHom ε φ h (ofAdd 1), hUK _, ?_⟩
  · rw [Ne, Subgroup.eq_bot_iff_forall]
    intro hbot
    have := hbot _ ⟨ofAdd 1, rfl⟩
    have h2 := (rootHom_injective ε φ hφinj h) (this.trans (map_one _).symm)
    exact h1 (ofAdd.injective h2)
  · intro u
    obtain ⟨x, hx⟩ := u.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, ← hx, rootHom_sq, Subgroup.coe_one]
  · rintro _ ⟨x, rfl⟩
    exact hUK x
  · exact frameHom_pow_p ψ A₀ ε hC hCp _
  · intro a' ha'
    obtain ⟨t', rfl⟩ := (hAT a').mp ha'
    rw [MulAut.conj_apply, hι, ← map_inv, ← map_mul, ← map_mul, mul_comm (ofAdd t'), mul_assoc,
      mul_inv_cancel, mul_one]
  · exact mem_normalizer_of_invariant hUA (by rw [hAT]; exact ⟨t₀, rfl⟩)
  · intro hcomm
    have h2 := rootHom_conj (ψ := ψ) (A₀ := A₀) (hC := hC) (hCp := hCp) ε hζ t₀ h 1
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one] at h2
    have h3 := (rootHom_injective ε φ hφinj h) h2.symm
    have h4 := ofAdd.injective h3
    apply hne
    rw [mul_one] at h4
    exact h4

theorem exists_zsmul_of_fix (hι : Function.Injective (frameHom ψ A₀ ε hC hCp))
    (hconj : ∀ x y : L', MulAut.conj x = MulAut.conj y → x = y)
    (hAT : ∀ a : MulAut L', a ∈ A ↔ ∃ t : Fin s → ZMod 3,
      a = MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd t)))
    {β : Fin s → ZMod 3} {Kl : Subgroup L'}
    (hcent : ∀ a' ∈ A, ((∀ j ∈ Kl, a' j = j) ↔
      a' ∈ Subgroup.zpowers (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β)))))
    (t : Fin s → ZMod 3)
    (hfix : ∀ j ∈ Kl, MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd t)) j = j) :
    ∃ z : ℤ, t = z • β := by
  have hmem := (hcent _ ((hAT _).mpr ⟨t, rfl⟩)).mp hfix
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine ⟨z, ?_⟩
  have h1 : MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β) ^ z) =
      MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd t)) := by
    rw [map_zpow]
    exact hz
  have h2 := hconj _ _ h1
  rw [← map_zpow] at h2
  have h3 := hι h2
  rw [← ofAdd_zsmul] at h3
  exact (ofAdd.injective h3).symm

theorem exists_two_ne (hs : 3 ≤ s) (j₀ : Fin s) :
    ∃ i₁ i₂ : Fin s, i₁ ≠ i₂ ∧ i₁ ≠ j₀ ∧ i₂ ≠ j₀ := by
  have h1 : 1 < (Finset.univ.erase j₀).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i₁, hi₁, i₂, hi₂, hne⟩ := Finset.one_lt_card.mp h1
  exact ⟨i₁, i₂, hne, (Finset.mem_erase.mp hi₁).1, (Finset.mem_erase.mp hi₂).1⟩

variable (hψ : Function.Injective ψ) (hζ : AdjoinRoot.root g ^ 3 = 1)
  (hprim : IsPrimitiveRoot (AdjoinRoot.root g) 3) (hs : 3 ≤ s)
  (hι : Function.Injective (frameHom ψ A₀ ε hC hCp))
  (hconj : ∀ x y : L', MulAut.conj x = MulAut.conj y → x = y)
  (hAT : ∀ a : MulAut L', a ∈ A ↔ ∃ t : Fin s → ZMod 3,
    a = MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd t)))
include hψ hζ hprim hs hι hconj hAT

theorem concl_zero_case {β : Fin s → ZMod 3} (hβ : β ≠ 0)
    (hcent : ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer
      (ggFix (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β)))), a' j = j) ↔
      a' ∈ Subgroup.zpowers (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β)))))
    (hK : LargeEvenLayer (ggFix (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β)))) =
      (coordBlockSL K (zeroCoords ε β)).map (SLRep.ggFrame ψ A₀)) :
    GGStdSubTwoTorusConcl 3 A (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β))) := by
  set ι := frameHom ψ A₀ ε hC hCp with hιdef
  set φ := SLRep.ggFrame ψ A₀ with hφ
  have hfixK : ∀ t : Fin s → ZMod 3, (∀ i, β i = 0 → t i = 0) →
      ∀ j ∈ LargeEvenLayer (ggFix (MulAut.conj (ι (ofAdd β)))),
        MulAut.conj (ι (ofAdd t)) j = j := by
    intro t ht j hj
    rw [hK] at hj
    obtain ⟨M, hM, rfl⟩ := hj
    rw [MulAut.conj_apply, hιdef, frameHom_eq_ggFrame, ← map_inv, ← map_mul, ← map_mul,
      comm_zeroBlock_of_torus (hC := hC) (k := fun i => (t i).val)
        (fun i hi => by rw [ht i hi, ZMod.val_zero]) hM, mul_inv_cancel_right]
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, β j₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hβ (funext h)
  obtain ⟨z, hz⟩ := exists_zsmul_of_fix ε hι hconj hAT hcent (Pi.single j₀ 1)
    (hfixK _ (fun i hi => by
      have hij : i ≠ j₀ := fun h => hj₀ (h ▸ hi)
      exact Pi.single_eq_of_ne hij _))
  have hz1 : (1 : ZMod 3) = (z : ZMod 3) * β j₀ := by
    have := congrFun hz j₀
    simpa [zsmul_eq_mul] using this
  have hsupp : ∀ i, i ≠ j₀ → β i = 0 := by
    intro i hi
    have := congrFun hz i
    simp only [Pi.single_eq_of_ne hi, Pi.smul_apply, zsmul_eq_mul] at this
    have hz0 : (z : ZMod 3) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hz1
      exact one_ne_zero hz1
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hz0
    · exact h
  obtain ⟨i₁, i₂, h12, hi₁, hi₂⟩ := exists_two_ne hs j₀
  have hUK : ∀ x, rootHom ε φ h12 x ∈ LargeEvenLayer (ggFix (MulAut.conj (ι (ofAdd β)))) := by
    intro x
    rw [hK, rootHom_apply]
    exact ⟨_, theta_tv_mem_zeroBlock ε h12 (hsupp i₁ hi₁) (hsupp i₂ hi₂) _, rfl⟩
  have htK : ι (ofAdd (Pi.single i₁ (1 : ZMod 3))) ∈
      LargeEvenLayer (ggFix (MulAut.conj (ι (ofAdd β)))) := by
    have hmem : SLNS.nsSL ε hC (fun i => ((Pi.single i₁ (1 : ZMod 3) : Fin s → ZMod 3) i).val) ∈
        coordBlockSL K (zeroCoords ε β) := by
      refine nsSL_mem_zeroBlock (hC := hC) (fun i hi => ?_)
      have hij : i = j₀ := by
        by_contra h
        exact hi (hsupp i h)
      rw [hij, Pi.single_eq_of_ne (Ne.symm hi₁ : j₀ ≠ i₁), ZMod.val_zero]
    rw [hK, hιdef, frameHom_eq_ggFrame]
    exact ⟨_, hmem, rfl⟩
  refine concl_of_root ε hψ hζ hAT h12 hUK (Pi.single i₁ 1) htK ?_
  have h1 : (Pi.single i₁ (1 : ZMod 3) : Fin s → ZMod 3) i₁ = 1 := by simp
  have h2 : (Pi.single i₁ (1 : ZMod 3) : Fin s → ZMod 3) i₂ = 0 :=
    Pi.single_eq_of_ne (Ne.symm h12) _
  have h3 : (1 : ZMod 3).val = 1 := rfl
  rw [h1, h2, h3, ZMod.val_zero, pow_one, pow_zero, mul_one]
  intro h
  exact root_pow_val_ne_one hprim (b := (1 : ZMod 3)) one_ne_zero (by rw [h3, pow_one]; exact h)

theorem concl_class_case {β : Fin s → ZMod 3} {c : ZMod 3} (hc : c ≠ 0)
    (hS : (classSet β c).Nonempty)
    (hcent : ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer
      (ggFix (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β)))), a' j = j) ↔
      a' ∈ Subgroup.zpowers (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β)))))
    (hK : LargeEvenLayer (ggFix (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β)))) =
      ((coordBlockSL (AdjoinRoot g) (classSet β c)).map (theta g ε)).map
        (SLRep.ggFrame ψ A₀)) :
    GGStdSubTwoTorusConcl 3 A (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β))) := by
  set ι := frameHom ψ A₀ ε hC hCp with hιdef
  set φ := SLRep.ggFrame ψ A₀ with hφ
  have hfixK : ∀ t : Fin s → ZMod 3, (∀ i j, β i = c → β j = c → t i = t j) →
      ∀ j ∈ LargeEvenLayer (ggFix (MulAut.conj (ι (ofAdd β)))),
        MulAut.conj (ι (ofAdd t)) j = j := by
    intro t ht j hj
    rw [hK] at hj
    obtain ⟨_, ⟨M, hM, rfl⟩, rfl⟩ := hj
    have hcomm := comm_classBlock_of_torus (hC := hC) (ε := ε) (c := c) (k := fun i => (t i).val)
      (fun i j hi hj => by rw [ht i j hi hj]) hM
    rw [MulAut.conj_apply, hιdef, frameHom_eq_ggFrame, ← map_inv, ← map_mul, ← map_mul, ← hcomm,
      mul_inv_cancel_right]
  have hconst : ∀ m, β m = c := by
    by_contra hm
    push Not at hm
    obtain ⟨m, hm⟩ := hm
    obtain ⟨i₀, hi₀⟩ := hS
    have hi₀' : β i₀ = c := mem_classSet.mp hi₀
    obtain ⟨z, hz⟩ := exists_zsmul_of_fix ε hι hconj hAT hcent (Pi.single m 1)
      (hfixK _ (fun i j hi hj => by
        have him : i ≠ m := fun h => hm (h ▸ hi)
        have hjm : j ≠ m := fun h => hm (h ▸ hj)
        rw [Pi.single_eq_of_ne him, Pi.single_eq_of_ne hjm]))
    have him₀ : i₀ ≠ m := fun h => hm (h ▸ hi₀')
    have h1 := congrFun hz i₀
    simp only [Pi.single_eq_of_ne him₀, Pi.smul_apply, zsmul_eq_mul, hi₀'] at h1
    have hz0 : (z : ZMod 3) = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact h
      · exact absurd h hc
    have h2 := congrFun hz m
    simp only [Pi.single_eq_same, Pi.smul_apply, zsmul_eq_mul, hz0, zero_mul] at h2
    exact one_ne_zero h2
  obtain ⟨i₁, i₂, h12, -, -⟩ := exists_two_ne hs (⟨0, by omega⟩ : Fin s)
  have hUK : ∀ x, rootHom ε φ h12 x ∈ LargeEvenLayer (ggFix (MulAut.conj (ι (ofAdd β)))) := by
    intro x
    rw [hK, rootHom_apply]
    exact ⟨_, ⟨_, SLRep.transvection_mem_coordBlockSL (mem_classSet.mpr (hconst i₁))
      (mem_classSet.mpr (hconst i₂)) h12 _, rfl⟩, rfl⟩
  set t₀ : Fin s → ZMod 3 := Pi.single i₁ 1 + Pi.single i₂ 2 with ht₀
  have hsum : ∑ i, t₀ i = 0 := by
    simp only [ht₀, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
    simp
    decide
  obtain ⟨D, hD, hθD⟩ := diag_mem_classBlock (ε := ε) (hC := hC) hζ (c := c) (t := t₀)
    (fun i hi => absurd (hconst i) hi) hsum
  have htK : ι (ofAdd t₀) ∈ LargeEvenLayer (ggFix (MulAut.conj (ι (ofAdd β)))) := by
    rw [hK, hιdef, frameHom_eq_ggFrame, ← hθD]
    exact ⟨theta g ε D, ⟨D, hD, rfl⟩, rfl⟩
  refine concl_of_root ε hψ hζ hAT h12 hUK t₀ htK ?_
  have h1 : t₀ i₁ = 1 := by simp [ht₀, Pi.single_eq_of_ne h12]
  have h2 : t₀ i₂ = 2 := by simp [ht₀, Pi.single_eq_of_ne (Ne.symm h12)]
  have h3 : (1 : ZMod 3).val = 1 := rfl
  have h4 : (2 : ZMod 3).val = 2 := rfl
  rw [h1, h2, h3, h4]
  intro h
  have h5 : AdjoinRoot.root g ^ 5 = 1 := by
    calc AdjoinRoot.root g ^ 5 = AdjoinRoot.root g ^ 1 * (AdjoinRoot.root g ^ 2) ^ 2 := by ring
      _ = 1 := h
  have := (hprim.pow_eq_one_iff_dvd 5).mp h5
  omega

end Concl

theorem fix_conj_eq_centralizer {R : Type*} [Group R] (t : R) :
    ggFix (MulAut.conj t) = Subgroup.centralizer ({t} : Set R) := by
  ext x
  rw [mem_ggFix, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * t = t * x * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  · intro h
    rw [← h]
    group

section Aligned

variable [Finite K] [CharP K 2] {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}
  {ψ : Matrix.SpecialLinearGroup (Fin n) K →* L'} {A₀ : Matrix.SpecialLinearGroup (Fin n) K}
  {hCp : rootMat g ^ 3 = 1}

theorem concl_of_aligned (hψb : Function.Bijective ψ) (hgd : g ∣ cyclotomic 3 K)
    (hpK : ¬ 3 ∣ Nat.card K - 1) (hs : 3 ≤ s)
    (hconj : ∀ x y : L', MulAut.conj x = MulAut.conj y → x = y)
    (hAT : ∀ a : MulAut L', a ∈ A ↔ ∃ t : Fin s → ZMod 3,
      a = MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd t)))
    {hζ : AdjoinRoot.root g ^ 3 = 1} {β : Fin s → ZMod 3} (hal : Aligned hζ β) (hβ : β ≠ 0)
    (hEcomp : IsComponentOf
      (LargeEvenLayer (ggFix (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β)))))
      (ggFix (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β)))))
    (hcent : ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer
      (ggFix (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β)))), a' j = j) ↔
      a' ∈ Subgroup.zpowers (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β))))) :
    GGStdSubTwoTorusConcl 3 A (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β))) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hpK' : ((3 : ℕ) : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp3 (by norm_num)
  have hprim := root_isPrimitiveRoot hp3 hpK' hgd
  have hζ' : AdjoinRoot.root g ^ 3 = 1 := hprim.pow_eq_one
  have hψ : Function.Injective ψ := hψb.1
  have hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [hψ (hx.trans (map_one ψ).symm)]
    exact Subgroup.one_mem _
  have hι : Function.Injective (frameHom ψ A₀ ε hC hCp) :=
    frameHom_injective ψ A₀ ε hC hCp hker (rootPB_dim_pos g)
      (isUnit_rootMat_pow_sub hp3 hpK hpK' hgd)
  have hb1 : frameHom ψ A₀ ε hC hCp (ofAdd β) ≠ 1 := by
    intro h1
    apply hβ
    have := hι (h1.trans (map_one _).symm)
    exact ofAdd.injective this
  have hrange : ψ.range = ⊤ := MonoidHom.range_eq_top.mpr hψb.2
  have hcomp : IsComponentOf
      (LargeEvenLayer (ggFix (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β)))))
      (ψ.range ⊓ Subgroup.centralizer {frameHom ψ A₀ ε hC hCp (ofAdd β)}) := by
    rw [hrange, top_inf_eq, ← fix_conj_eq_centralizer]
    exact hEcomp
  rcases comp_of_aligned_eq (hC := hC) (hCp := hCp) (A₀ := A₀) (by norm_num : 3 ≠ 2) hpK hker hgd
    hal hb1 hcomp with hK | ⟨c, hc, hS, hK⟩
  · exact concl_zero_case ε hψ hζ' hprim hs hι hconj hAT hβ hcent hK
  · exact concl_class_case ε hψ hζ' hprim hs hι hconj hAT hc hS hcent hK

theorem concl_of_frame (hψb : Function.Bijective ψ) (hgd : g ∣ cyclotomic 3 K)
    (hpK : ¬ 3 ∣ Nat.card K - 1) (hs : 3 ≤ s)
    (hconj : ∀ x y : L', MulAut.conj x = MulAut.conj y → x = y)
    (hAT : ∀ a : MulAut L', a ∈ A ↔ ∃ t : Fin s → ZMod 3,
      a = MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd t)))
    {β : Fin s → ZMod 3} (hβ : β ≠ 0)
    (hEcomp : IsComponentOf
      (LargeEvenLayer (ggFix (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β)))))
      (ggFix (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β)))))
    (hcent : ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer
      (ggFix (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β)))), a' j = j) ↔
      a' ∈ Subgroup.zpowers (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β))))) :
    GGStdSubTwoTorusConcl 3 A (MulAut.conj (frameHom ψ A₀ ε hC hCp (ofAdd β))) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hpK' : ((3 : ℕ) : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp3 (by norm_num)
  have hprim := root_isPrimitiveRoot hp3 hpK' hgd
  have hζ : AdjoinRoot.root g ^ 3 = 1 := hprim.pow_eq_one
  have hψ : Function.Injective ψ := hψb.1
  have hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [hψ (hx.trans (map_one ψ).symm)]
    exact Subgroup.one_mem _
  have hι : Function.Injective (frameHom ψ A₀ ε hC hCp) :=
    frameHom_injective ψ A₀ ε hC hCp hker (rootPB_dim_pos g)
      (isUnit_rootMat_pow_sub hp3 hpK hpK' hgd)
  obtain ⟨A₁, β₁, hal, hrange, hb⟩ := exists_aligned_frame (hC := hC) (hCp := hCp) (ψ := ψ)
    (A₀ := A₀) hζ β
  have hι₁ : Function.Injective (frameHom ψ A₁ ε hC hCp) :=
    frameHom_injective ψ A₁ ε hC hCp hker (rootPB_dim_pos g)
      (isUnit_rootMat_pow_sub hp3 hpK hpK' hgd)
  have hAT₁ : ∀ a : MulAut L', a ∈ A ↔ ∃ t : Fin s → ZMod 3,
      a = MulAut.conj (frameHom ψ A₁ ε hC hCp (ofAdd t)) := by
    intro a
    rw [hAT a]
    constructor
    · rintro ⟨t, rfl⟩
      have hx : frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ (frameHom ψ A₁ ε hC hCp).range := by
        rw [hrange]
        exact ⟨ofAdd t, rfl⟩
      obtain ⟨u, hu⟩ := hx
      exact ⟨toAdd u, by rw [ofAdd_toAdd, hu]⟩
    · rintro ⟨t, rfl⟩
      have hx : frameHom ψ A₁ ε hC hCp (ofAdd t) ∈ (frameHom ψ A₀ ε hC hCp).range := by
        rw [← hrange]
        exact ⟨ofAdd t, rfl⟩
      obtain ⟨u, hu⟩ := hx
      exact ⟨toAdd u, by rw [ofAdd_toAdd, hu]⟩
  have hβ₁ : β₁ ≠ 0 := by
    intro h0
    apply hβ
    have h1 : frameHom ψ A₀ ε hC hCp (ofAdd β) = 1 := by
      rw [← hb, h0, ofAdd_zero, map_one]
    exact ofAdd.injective (hι (h1.trans (map_one _).symm))
  rw [← hb] at hEcomp hcent ⊢
  exact concl_of_aligned ε hψb hgd hpK hs hconj hAT₁ hal hβ₁ hEcomp hcent

end Aligned

section Delta

variable {L' : Type} [Group L'] {A : Subgroup (MulAut L')}

theorem not_ggDeltaAdm_of_inner {p : ℕ} (hp : ¬ p ∣ 1)
    (hconj : ∀ x y : L', MulAut.conj x = MulAut.conj y → x = y)
    (hinner : ∀ a ∈ A, a ∈ (MulAut.conj : L' →* MulAut L').range) :
    ¬ GGDeltaAdm p L' A := by
  intro hδ
  rcases hδ.2 with ⟨⟨a, haA, hout⟩, -⟩ | ⟨hdvd, -, -⟩
  · exact hout (hinner a haA)
  · have hcen : Subgroup.center L' = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      apply hconj
      rw [map_one]
      ext y
      simp only [MulAut.conj_apply, MulAut.one_apply]
      have := Subgroup.mem_center_iff.mp hx y
      calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [this]
        _ = y := by group
    rw [hcen, Subgroup.card_bot] at hdvd
    exact hp hdvd

end Delta

end CFSG.StandardType.SmallL2

end

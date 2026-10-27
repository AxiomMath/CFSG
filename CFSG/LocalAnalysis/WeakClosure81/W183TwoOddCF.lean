module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoOddSub
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private theorem w183b5_finset_sup_subgroupOf {G : Type*} [Group G] (B : Subgroup G)
    [DecidableEq (Subgroup ↥B)] (s : Finset (Subgroup G)) (h : ∀ H ∈ s, H ≤ B) :
    (s.image (fun H => H.subgroupOf B)).sup id = (s.sup id).subgroupOf B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ha' : a ≤ B := h a (Finset.mem_insert_self a s)
    have hs : ∀ H ∈ s, H ≤ B := fun H hH => h H (Finset.mem_insert_of_mem hH)
    rw [Finset.image_insert, Finset.sup_insert, Finset.sup_insert, ih hs]
    exact (Subgroup.subgroupOf_sup (A := a) (A' := s.sup id) (B := B) ha'
      (Finset.sup_le hs)).symm

theorem isCompositionFactor_oddClassSub {Y : Type} [Group Y] [Finite Y] {a : Y}
    (hN2 : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ Subgroup.normalClosure ({a} : Set Y)) {T : Type}
    [Group T] (h : CFSG.Quasithin.E1.IsCompositionFactor Y T) (hnab : ∃ u v : T, u * v ≠ v * u) :
    CFSG.Quasithin.E1.IsCompositionFactor ↥(oddClassSub a) T := by
  classical
  letI := Fintype.ofFinite Y
  set N : Subgroup Y := Subgroup.normalClosure ({a} : Set Y) with hN
  haveI hNn : N.Normal := by rw [hN]; infer_instance
  have hN2' : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ N := by
    intro y
    obtain ⟨k, hk⟩ := hN2 y
    exact ⟨k, by rwa [hN]⟩
  rcases CFSG.LocalAnalysis.WeakClosure81.isCompositionFactor_of_normal N h with
    hNfac | hQfac
  ·
    let A : Y → Subgroup Y := fun y => (oddClassSub a).map (MulAut.conj y).toMonoidHom
    have hAle : ∀ y : Y, A y ≤ N := by
      intro y
      calc A y ≤ N.map (MulAut.conj y).toMonoidHom := by
            exact Subgroup.map_mono (by rw [hN]; exact oddClassSub_le_normalClosure a)
        _ = N := Subgroup.Normal.map_conj_eq N y
    have hAnorm : ∀ y : Y, ((A y).subgroupOf N).Normal := by
      intro y
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨z, hzX, hzx⟩ := Subgroup.mem_map.mp hx
      have hgN : y⁻¹ * (g : Y) * y ∈ N := by
        have h := hNn.conj_mem (g : Y) g.2 y⁻¹
        simpa [mul_assoc] using h
      refine Subgroup.mem_map.mpr
        ⟨(y⁻¹ * (g : Y) * y) * z * (y⁻¹ * (g : Y) * y)⁻¹,
          conj_mem_oddClassSub hgN hzX, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rw [← hzx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    let s : Finset (Subgroup Y) := Finset.univ.image A
    have hsle : ∀ H ∈ s, H ≤ N := by
      intro H hH
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hH
      exact hAle y
    have hsupY : s.sup id = N := by
      have h1 : s.sup id = Finset.univ.sup A := by simp [s]
      rw [h1, Finset.sup_eq_iSup]
      simpa [A] using iSup_conj_oddClassSub a
    let 𝒩 : Finset (Subgroup ↥N) := s.image (fun H => H.subgroupOf N)
    have h𝒩norm : ∀ K ∈ 𝒩, K.Normal := by
      intro K hK
      obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hK
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hH
      exact hAnorm y
    have h𝒩sup : 𝒩.sup id = ⊤ := by
      rw [show 𝒩.sup id = (s.sup id).subgroupOf N from
        w183b5_finset_sup_subgroupOf N s hsle]
      rw [hsupY, Subgroup.subgroupOf_self]
    obtain ⟨K, hK, hKfac⟩ :=
      CFSG.Quasithin.H13.L829N.isCompositionFactor_of_finset_sup 𝒩 h𝒩norm h𝒩sup hNfac
    obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hH
    refine (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      (Subgroup.equivMapOfInjective (oddClassSub a) (MulAut.conj y).toMonoidHom
        (MulAut.conj y).injective)).mpr ?_
    exact (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      (Subgroup.subgroupOfEquivOfLe (hAle y))).mp hKfac
  ·
    have hP : IsPGroup 2 (Y ⧸ N) := by
      intro g
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N g
      obtain ⟨k, hk⟩ := hN2' y
      refine ⟨k, ?_⟩
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hk
    haveI : Group.IsNilpotent (Y ⧸ N) := hP.isNilpotent
    haveI : Group.IsSolvable (Y ⧸ N) := IsNilpotent.to_isSolvable
    obtain ⟨u, v, huv⟩ := hnab
    exact absurd
      (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
        inferInstance hQfac u v) huv

end CFSG.LocalAnalysis.WeakClosure81

end

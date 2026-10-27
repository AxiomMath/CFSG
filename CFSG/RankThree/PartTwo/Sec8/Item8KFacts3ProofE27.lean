module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofA9
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofSp62
public import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofBMemY
import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofSp62
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62
import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofWreath

public section

namespace CFSG.RankThree.PartTwo.Sec8

open Subgroup

namespace Item8KFacts3

theorem mem_zpowers_of_map {M N : Type*} [Group M] [Group N] (f : M →* N)
    (hf : Function.Injective f) {E S H₁ H₂ : Subgroup M} {u v : M}
    (hN : ∀ {S' H₁' H₂' : Subgroup N} {u' v' : N}, S' ≤ E.map f → Nat.card S' = 9 →
      u' ∈ E.map f → v' ∈ E.map f → u' ∉ S' → v' ∉ S' → Group.IsPerfect H₁' →
      Group.IsPerfect H₂' → S' ≤ H₁' → S' ≤ H₂' → H₁' ≤ Subgroup.centralizer {u'} →
      H₂' ≤ Subgroup.centralizer {v'} → v' ∈ Subgroup.zpowers u')
    (hSE : S ≤ E) (hS9 : Nat.card S = 9) (huE : u ∈ E) (hvE : v ∈ E) (huS : u ∉ S)
    (hvS : v ∉ S) (hP₁ : Group.IsPerfect H₁) (hP₂ : Group.IsPerfect H₂) (hSH₁ : S ≤ H₁)
    (hSH₂ : S ≤ H₂) (hH₁ : H₁ ≤ Subgroup.centralizer {u}) (hH₂ : H₂ ≤ Subgroup.centralizer {v}) :
    v ∈ Subgroup.zpowers u := by
  have hmapc : ∀ {w : M} {H : Subgroup M}, H ≤ Subgroup.centralizer {w} →
      H.map f ≤ Subgroup.centralizer {f w} := by
    intro w H hH
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hH hy
    rw [mem_centralizer_singleton_iff] at h1 ⊢
    rw [← map_mul, ← map_mul, h1]
  have hmemf : ∀ {x : M} {K : Subgroup M}, f x ∈ K.map f ↔ x ∈ K := fun {x K} =>
    ⟨fun ⟨y, hy, hyx⟩ => hf hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hP₁' : Group.IsPerfect (H₁.map f) := @Group.IsPerfect.map _ _ _ _ _ f hP₁
  have hP₂' : Group.IsPerfect (H₂.map f) := @Group.IsPerfect.map _ _ _ _ _ f hP₂
  have h := hN (Subgroup.map_mono hSE) (by rw [Subgroup.card_map_of_injective hf, hS9])
    (hmemf.2 huE) (hmemf.2 hvE) (fun h => huS (hmemf.1 h)) (fun h => hvS (hmemf.1 h)) hP₁' hP₂'
    (Subgroup.map_mono hSH₁) (Subgroup.map_mono hSH₂) (hmapc hH₁) (hmapc hH₂)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, hf (by rw [map_zpow, hk])⟩

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
  CFSG.RankThree.PartTwo.Sec4.Item434Kit


theorem mem_zpowers_of_H6 {E : Subgroup H6} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) {S H₁ H₂ : Subgroup H6} {u v : H6} (hSE : S ≤ E)
    (hS9 : Nat.card S = 9) (huE : u ∈ E) (hvE : v ∈ E) (huS : u ∉ S) (hvS : v ∉ S)
    (hP₁ : Group.IsPerfect H₁) (hP₂ : Group.IsPerfect H₂) (hSH₁ : S ≤ H₁) (hSH₂ : S ≤ H₂)
    (hH₁ : H₁ ≤ Subgroup.centralizer {u}) (hH₂ : H₂ ≤ Subgroup.centralizer {v}) :
    v ∈ Subgroup.zpowers u := by
  obtain ⟨g, rfl⟩ := Item812Res5.exists_eq_map_conj_baseA wreathFacts_zH
    Item812Res5.card_wreathW_zH_eq_pow card_wreathW_zH hE hE27
  refine mem_zpowers_of_map (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective ?_ hSE
    hS9 huE hvE huS hvS hP₁ hP₂ hSH₁ hSH₂ hH₁ hH₂
  have hE' : ((baseA zH).map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom =
      baseA zH := by
    have h1 := Sec4.Item434AltPerm.map_conj_map_conj_inv (baseA zH) g⁻¹
    rwa [inv_inv] at h1
  rw [hE']
  intro S' H₁' H₂' u' v' hS'A hS'9 hu'A hv'A hu'S hv'S hP₁' hP₂' hS'H₁ hS'H₂ hH₁' hH₂'
  exact mem_zpowers_of_baseA_zH hS'A hS'9 hu'A hv'A hu'S hv'S hP₁' hP₂' hS'H₁ hS'H₂ hH₁' hH₂'

end Item8KFacts3

open Item8KFacts3

theorem kF812E27PerfCent_holds : KF812E27PerfCent := by
  intro M _ _ hM E S H₁ H₂ u v hE hE27 hSE hS9 huE hvE huS hvS hP₁ hP₂ hSH₁ hSH₂ hH₁ hH₂
  rcases hM with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · set f : M →* Equiv.Perm (Fin 9) :=
      (alternatingGroup (Fin 9)).subtype.comp e.toMonoidHom with hfdef
    have hf : Function.Injective f :=
      (alternatingGroup (Fin 9)).subtype_injective.comp e.injective
    refine mem_zpowers_of_map f hf ?_ hSE hS9 huE hvE huS hvS hP₁ hP₂ hSH₁ hSH₂ hH₁ hH₂
    intro S' H₁' H₂' u' v' _ hS'9 hu'E hv'E hu'S hv'S hP₁' hP₂' hS'H₁ hS'H₂ hH₁' hH₂'
    exact mem_zpowers_of_perm9 (Item812Res5.isElemAbelian_map_hom f hE)
      (by rw [Subgroup.card_map_of_injective hf, hE27]) hS'9 hu'E hv'E hu'S hv'S hP₁' hP₂' hS'H₁
      hS'H₂ hH₁' hH₂'
  · set e' : M ≃* CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.H6 :=
      e.trans Sec4.Item434SmallTwoIII.sp62Equiv with he'
    refine mem_zpowers_of_map e'.toMonoidHom e'.injective ?_ hSE hS9 huE hvE huS hvS hP₁ hP₂ hSH₁
      hSH₂ hH₁ hH₂
    intro S' H₁' H₂' u' v' hS'E hS'9 hu'E hv'E hu'S hv'S hP₁' hP₂' hS'H₁ hS'H₂ hH₁' hH₂'
    exact mem_zpowers_of_H6 (Item812Res5.isElemAbelian_map_hom e'.toMonoidHom hE)
      (by rw [Subgroup.card_map_of_injective e'.injective, hE27]) hS'E hS'9 hu'E hv'E hu'S hv'S
      hP₁' hP₂' hS'H₁ hS'H₂ hH₁' hH₂'

end CFSG.RankThree.PartTwo.Sec8

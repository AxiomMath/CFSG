module

public import CFSG.Permutation.FiveTransitive.SylowNormalizerSandwich

public section

namespace CFSG

namespace FiveTransitive.SylowNormalizerExtension

theorem exists_sylow_extension
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (F Q : Subgroup G) (hQF : Q≤F) (hQ : IsPGroup p Q)
    (hQcard : Nat.card Q < p ^ (Nat.card F).factorization p)
    (R : Sylow p ↥(Subgroup.normalizer (Q : Set G) ⊓ F)) :
    ∃ S : Sylow p F,
      Q < (R : Subgroup ↥(Subgroup.normalizer (Q : Set G) ⊓ F)).map
        (Subgroup.normalizer (Q : Set G) ⊓ F).subtype ∧
      (R : Subgroup ↥(Subgroup.normalizer (Q : Set G) ⊓ F)).map
        (Subgroup.normalizer (Q : Set G) ⊓ F).subtype =
      (S : Subgroup F).map F.subtype ⊓ Subgroup.normalizer (Q : Set G) := by
  let K := Subgroup.normalizer (Q : Set G) ⊓ F
  let A : Subgroup G := (R : Subgroup K).map K.subtype
  have hQK : Q≤K := le_inf Q.le_normalizer hQF
  have hKN : K≤Subgroup.normalizer (Q : Set G) := inf_le_left
  have : (Q.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKN
  have hQsub : IsPGroup p (Q.subgroupOf K) := hQ.comap_subtype
  have hQR : Q≤A := by
    intro q hq
    let qK : K := ⟨q,hQK hq⟩
    have hqR : qK∈R := hQsub.le_sylow_of_normal R hq
    exact ⟨qK,hqR,rfl⟩
  have hAN : A≤Subgroup.normalizer (Q:Set G) := by
    intro x hx
    obtain ⟨r,_,rfl⟩ := Subgroup.mem_map.mp hx
    exact r.property.1
  have hAF : A≤F := by
    intro x hx
    obtain ⟨r,_,rfl⟩ := Subgroup.mem_map.mp hx
    exact r.property.2
  have hA : IsPGroup p A := R.isPGroup'.map K.subtype
  have hAFp : IsPGroup p (A.subgroupOf F) := hA.comap_subtype
  obtain ⟨S,hAS⟩ := hAFp.exists_le_sylow
  let H : Subgroup G := (S : Subgroup F).map F.subtype
  have hAH : A≤H := by
    intro x hx
    let xF : F := ⟨x,hAF hx⟩
    have hxS : xF∈S := hAS hx
    exact ⟨xF,hxS,rfl⟩
  have hHF : H≤F := by
    intro x hx
    obtain ⟨s,_,rfl⟩ := Subgroup.mem_map.mp hx
    exact s.property
  have hH : IsPGroup p H := S.isPGroup'.map F.subtype
  have hHcard : Nat.card H=p^(Nat.card F).factorization p := by
    have he := Nat.card_congr ((S : Subgroup F).equivMapOfInjective F.subtype Subtype.val_injective).toEquiv
    exact he.symm.trans S.card_eq_multiplicity
  have hQH : Q<H := by
    apply lt_of_le_of_ne (hQR.trans hAH)
    intro he
    have h := hQcard
    rw [he,hHcard] at h
    exact Nat.lt_irrefl _ h
  have hHK : H ⊓ Subgroup.normalizer (Q:Set G) ≤ K := by
    intro x hx
    exact ⟨hx.2,hHF hx.1⟩
  exact ⟨S,SylowNormalizerSandwich.lt_sylow_image_of_normalizer_sandwich K H Q R hH hQH hAH hAN hHK,
    SylowNormalizerSandwich.sylow_image_eq_inf_normalizer K H Q R hH hAH hAN hHK⟩

end FiveTransitive.SylowNormalizerExtension

end CFSG

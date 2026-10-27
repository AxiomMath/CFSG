module

public import CFSG.Monster.B.TwoA.Fischer.SliceOrderPSU
public import CFSG.Monster.B.Classical.UnitarySixClass
public import CFSG.Monster.B.E6.StdF4Points

public noncomputable section

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar betaGroup card_betaGroup)
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.Monster.B.Classical.UnitarySix (IsoPt ProjSU tPt projAct)

theorem card_le_of_commute_rootClass
    {T : Type*} [Group T] [Finite T] (ψ : T →* GStar)
    (hψ : Function.Injective ψ)
    (hG : ∀ t, ψ t ∈ (SemidirectProduct.inl : stdGroup →* GStar).range)
    {x : stdGroup} (hx : x ∈ rootClass)
    (hc : ∀ t, ψ t * SemidirectProduct.inl x = SemidirectProduct.inl x * ψ t)
    (h2 : ∀ N : Subgroup T, N.Normal → IsPGroup 2 N → Nat.card N ≤ 2) :
    Nat.card T ≤ 2 * 9196830720 := by
  obtain ⟨g, rfl⟩ := (mem_rootClass_iff x).1 hx
  have hinl : Function.Injective (SemidirectProduct.inl : stdGroup →* GStar) :=
    SemidirectProduct.inl_injective
  let α : T →* stdGroup :=
    (MonoidHom.ofInjective hinl).symm.toMonoidHom.comp (ψ.codRestrict _ hG)
  have hα : ∀ t, (SemidirectProduct.inl (α t) : GStar) = ψ t := fun t =>
    MonoidHom.apply_ofInjective_symm hinl ⟨ψ t, hG t⟩
  have hαinj : Function.Injective α := fun a b h => hψ (by rw [← hα, ← hα, h])
  have hαc : ∀ t, α t * rootMap g = rootMap g * α t := by
    intro t
    apply hinl
    rw [map_mul, map_mul, hα]
    exact hc t
  let β : T →* stdGroup := (MulAut.conj g⁻¹).toMonoidHom.comp α
  have hβ : ∀ t, β t = g⁻¹ * α t * g := fun t => by
    show g⁻¹ * α t * g⁻¹⁻¹ = _
    rw [inv_inv]
  have hβmem : ∀ t, ((β t : stdGroup) : ModGL Tag.E6 K) ∈ nativeParabolic firstJ := by
    intro t
    rw [← mem_centralizer_rootInv_iff, hβ]
    have h := hαc t
    rw [rootMap] at h
    calc g⁻¹ * α t * g * rootInv * (g⁻¹ * α t * g)⁻¹
        = g⁻¹ * (α t * (g * rootInv * g⁻¹)) * (α t)⁻¹ * g := by group
      _ = g⁻¹ * (g * rootInv * g⁻¹ * α t) * (α t)⁻¹ * g := by rw [h]
      _ = rootInv := by group
  let γ : T →* nativeParabolic firstJ := (stdGroup.subtype.comp β).codRestrict _ hβmem
  have hγinj : Function.Injective γ := by
    intro a b h
    have h1 : β a = β b :=
      Subtype.ext (congrArg (fun z : nativeParabolic firstJ => (z : ModGL Tag.E6 K)) h)
    rw [hβ, hβ] at h1
    exact hαinj (mul_right_cancel (mul_left_cancel h1))
  let δ : T →* stdLevi firstJ := (leviProj two_mem_firstJ).comp γ
  have hK2 : IsPGroup 2 δ.ker := by
    let f : δ.ker →* stdUnipotent0 :=
      ((nativeParabolic firstJ).subtype.comp (γ.comp δ.ker.subtype)).codRestrict _ fun k =>
        stdRadical_le_stdUnipotent0 firstJ ((leviProj_eq_one_iff two_mem_firstJ _).1 k.2)
    have hf : Function.Injective f := by
      intro a b h
      exact Subtype.ext (hγinj (Subtype.ext
        (congrArg (fun z : stdUnipotent0 => (z : ModGL Tag.E6 K)) h)))
    exact (IsPGroup.of_card card_stdUnipotent0).of_injective f hf
  have hK := h2 δ.ker inferInstance hK2
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv] at hcard
  have hr : Nat.card δ.range ≤ 9196830720 := by
    rw [← card_stdLevi_firstJ]
    exact Subgroup.card_le_card_group _
  rw [hcard]
  calc Nat.card δ.range * Nat.card δ.ker ≤ 9196830720 * 2 := Nat.mul_le_mul hr hK
    _ = 2 * 9196830720 := by norm_num

theorem card_ker_rightHom_mul_two
    {T : Type*} [Group T] [Finite T] (ψ : T →* GStar)
    (h : ∃ t, ψ t ∉ (SemidirectProduct.inl : stdGroup →* GStar).range) :
    Nat.card (SemidirectProduct.rightHom.comp ψ).ker * 2 = Nat.card T := by
  set ε := (SemidirectProduct.rightHom : GStar →* betaGroup).comp ψ
  obtain ⟨t₀, ht₀⟩ := h
  have hne : ε t₀ ≠ 1 := fun h1 => ht₀ (by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact h1)
  have hdvd : Nat.card ε.range ∣ 2 := card_betaGroup ▸ Subgroup.card_subgroup_dvd_card _
  have hne1 : Nat.card ε.range ≠ 1 := fun h1 => hne (by
    have := (Subgroup.card_eq_one.1 h1)
    have hm : ε t₀ ∈ ε.range := ⟨t₀, rfl⟩
    rw [this] at hm
    exact hm)
  have h2 : Nat.card ε.range = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
    · exact absurd h1 hne1
    · exact h1
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ε.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ε).toEquiv, h2] at hcard
  rw [hcard, mul_comm]

theorem closure_range_tPt : Subgroup.closure (Set.range tPt) = ⊤ := by
  have hN : (Subgroup.closure (Set.range tPt)).Normal := by
    refine ⟨fun n hn x => ?_⟩
    have hle : (Subgroup.closure (Set.range tPt)).map (MulAut.conj x).toMonoidHom ≤
        Subgroup.closure (Set.range tPt) := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨projAct x p, by
        rw [CFSG.Monster.B.Classical.UnitarySix.tPt_projAct]
        rfl⟩
    exact hle ⟨n, hn, rfl⟩
  have := CFSG.Monster.B.TwoA.Fischer.isSimpleGroup_projSU
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure (Set.range tPt)) with h | h
  · exfalso
    let p : IsoPt := CFSG.Monster.B.Classical.UnitarySix.stdPt 0
    have hp : tPt p ∈ Subgroup.closure (Set.range tPt) := Subgroup.subset_closure ⟨p, rfl⟩
    rw [h, Subgroup.mem_bot] at hp
    exact CFSG.Monster.B.Classical.UnitarySix.tPt_ne_one p hp
  · exact h

end CFSG.Monster.B.TwoA.Amalgam

module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bWittBasis
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bModelC
public import CFSG.Quasithin.Recognition.GoldschmidtF112RTransport
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIFacts

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Quasithin CFSG.Open

section Conj

@[expose] def conjEW {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (e : W ≃ₗ[ZMod 2] Model.VM) : (W ≃ₗ[ZMod 2] W) ≃* (Model.VM ≃ₗ[ZMod 2] Model.VM) where
  toFun γ := (e.symm.trans γ).trans e
  invFun δ := (e.trans δ).trans e.symm
  left_inv γ := by
    ext w
    simp
  right_inv δ := by
    ext v
    simp
  map_mul' γ1 γ2 := by
    ext v
    simp

theorem conjE_apply {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (e : W ≃ₗ[ZMod 2] Model.VM) (γ : W ≃ₗ[ZMod 2] W) (v : Model.VM) :
    conjEW e γ v = e (γ (e.symm v)) := rfl

theorem conjEW_mem_iff {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (q : W → ZMod 2) (e : W ≃ₗ[ZMod 2] Model.VM) (he : ∀ v, Model.qM (e v) = q v)
    (γ : W ≃ₗ[ZMod 2] W) : γ ∈ orthogonalSubgroupOf q ↔ conjEW e γ ∈ Model.GM := by
  constructor
  · intro hγ v
    rw [conjE_apply, he, hγ, ← he (e.symm v), e.apply_symm_apply]
  · intro hγ w
    have h := hγ (e w)
    rw [conjE_apply, he, e.symm_apply_apply, he] at h
    exact h

theorem stabS_conj_iff {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (S : Submodule (ZMod 2) W) (e : W ≃ₗ[ZMod 2] Model.VM)
    (hSe : ∀ v, v ∈ S ↔ e v ∈ Model.Sm) (γ : W ≃ₗ[ZMod 2] W) :
    γ ∈ stabS S ↔ conjEW e γ ∈ Model.stabM Model.Sm := by
  show (∀ v, v ∈ S ↔ γ v ∈ S) ↔ (∀ x, x ∈ Model.Sm ↔ conjEW e γ x ∈ Model.Sm)
  constructor
  · intro h x
    have h1 := hSe (e.symm x)
    rw [e.apply_symm_apply] at h1
    have h2 := hSe (γ (e.symm x))
    rw [conjE_apply, ← h1, ← h2]
    exact h (e.symm x)
  · intro h v
    rw [hSe v, hSe (γ v)]
    have := h (e v)
    rw [conjE_apply, e.symm_apply_apply] at this
    exact this

theorem GM_map_eq {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (q : W → ZMod 2) (e : W ≃ₗ[ZMod 2] Model.VM) (he : ∀ v, Model.qM (e v) = q v) :
    (orthogonalSubgroupOf q).map (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM)) = Model.GM := by
  ext δ
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact (conjEW_mem_iff q e he γ).1 hγ
  · intro hδ
    exact ⟨(conjEW e).symm δ, (conjEW_mem_iff q e he _).2 (by rw [MulEquiv.apply_symm_apply]; exact hδ),
      MulEquiv.apply_symm_apply _ _⟩

theorem stabS_map_eq {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (S : Submodule (ZMod 2) W) (e : W ≃ₗ[ZMod 2] Model.VM)
    (hSe : ∀ v, v ∈ S ↔ e v ∈ Model.Sm) :
    (stabS S).map (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM)) = Model.stabM Model.Sm := by
  ext δ
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact (stabS_conj_iff S e hSe γ).1 hγ
  · intro hδ
    exact ⟨(conjEW e).symm δ, (stabS_conj_iff S e hSe _).2 (by rw [MulEquiv.apply_symm_apply]; exact hδ),
      MulEquiv.apply_symm_apply _ _⟩

end Conj

section Main

theorem part_c_of_MTS {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w) (hB : ∀ v : W, (∀ w, B v w = 0) → v = 0)
    (hdim : Module.finrank (ZMod 2) W = 6)
    (hGcard : Nat.card (orthogonalSubgroupOf q) = 40320)
    (S : Submodule (ZMod 2) W) (hS3 : Module.finrank (ZMod 2) S = 3) (hSs : ∀ s ∈ S, q s = 0)
    (Ω : Subgroup (W ≃ₗ[ZMod 2] W)) (hΩ : Ω ≤ orthogonalSubgroupOf q)
    (hrel : Ω.relIndex (orthogonalSubgroupOf q) = 2) :
    (∀ γ ∈ orthogonalSubgroupOf q, (∀ v, v ∈ S ↔ γ v ∈ S) → γ ∈ Ω) ∧
    (stabS S).relIndex Ω = 15 ∧
    Nat.card (pCoreOf 2 (stabS S ⊓ Ω)) = 8 ∧
    ∀ γ ∈ stabS S ⊓ Ω, (∀ s ∈ S, γ s = s) ↔ γ ∈ pCoreOf 2 (stabS S ⊓ Ω) := by
  haveI : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  obtain ⟨b, _hb1, _hb2, _hb3, hb5, hbS⟩ := exists_witt_basis_of_MTS q B hq hB hdim S hS3 hSs
  let e : W ≃ₗ[ZMod 2] Model.VM := b.equivFun
  have he : ∀ v, Model.qM (e v) = q v := by
    intro v
    have hv : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
    rw [Fintype.sum_sum_type] at hv
    have key : q v = ∑ i, b.repr v (.inl i) * b.repr v (.inr i) := by
      conv_lhs => rw [hv]
      exact hb5 (fun i => b.repr v (.inl i)) (fun i => b.repr v (.inr i))
    rw [key]
    simp only [Model.qM, Model.xp, Model.yp, dotProduct, e, Module.Basis.equivFun_apply]
  have hSe : ∀ v, v ∈ S ↔ e v ∈ Model.Sm := by
    intro v
    rw [hbS v, Model.mem_Sm_iff]
    simp only [e, Module.Basis.equivFun_apply]
  have hGM := GM_map_eq q e he
  have hstabM := stabS_map_eq S e hSe
  have hΩM : Ω.map (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM)) ≤ Model.GM := by
    rw [← hGM]
    exact Subgroup.map_mono hΩ
  have hrelM : (Ω.map (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM))).relIndex Model.GM = 2 := by
    rw [← hGM, Subgroup.relIndex_map_map_of_injective (f := (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM))) _ _
      (conjEW e).injective, hrel]
  have hGMcard : Nat.card Model.GM = 40320 := by
    rw [← hGM, ← hGcard]
    exact (Nat.card_congr ((orthogonalSubgroupOf q).equivMapOfInjective _
      (conjEW e).injective).toEquiv).symm
  obtain ⟨M1, M2, M3, M4⟩ := Model.model_claims hΩM hrelM hGMcard
  have C1 : ∀ γ ∈ orthogonalSubgroupOf q, (∀ v, v ∈ S ↔ γ v ∈ S) → γ ∈ Ω := by
    intro γ hγ hS'
    have hfγ : conjEW e γ ∈ Model.GM := (conjEW_mem_iff q e he γ).1 hγ
    have hst : conjEW e γ ∈ Model.stabM Model.Sm := (stabS_conj_iff S e hSe γ).1 hS'
    have hmem := M1 (conjEW e γ) hfγ ((Model.mem_stabM_iff _ _).1 hst)
    obtain ⟨ω, hω, hωγ⟩ := Subgroup.mem_map.1 hmem
    have hωγ' : ω = γ := (conjEW e).injective hωγ
    rw [← hωγ']
    exact hω
  have C2 : (stabS S).relIndex Ω = 15 := by
    have h := M2
    rw [← hstabM, Subgroup.relIndex_map_map_of_injective (f := (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM))) _ _
      (conjEW e).injective] at h
    exact h
  have hmapA : (stabS S ⊓ Ω).map (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM)) =
      Model.stabM Model.Sm ⊓ Ω.map (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM)) := by
    rw [Subgroup.map_inf _ _ (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM)) (conjEW e).injective, hstabM]
  have C3 : Nat.card (pCoreOf 2 (stabS S ⊓ Ω)) = 8 := by
    have hcard := CFSG.Quasithin.F112R.card_pCoreOf_of_mulEquiv (MulEquiv.subgroupMap (conjEW e) (stabS S ⊓ Ω)) 2
    rw [hmapA] at hcard
    rw [hcard, M3]
  have C4 : ∀ γ ∈ stabS S ⊓ Ω, (∀ s ∈ S, γ s = s) ↔ γ ∈ pCoreOf 2 (stabS S ⊓ Ω) := by
    intro γ hγ
    have hmem := CFSG.Quasithin.F112R.mem_pCoreOf_iff_of_mulEquiv (MulEquiv.subgroupMap (conjEW e) (stabS S ⊓ Ω)) 2
      ⟨γ, hγ⟩
    have hmem' : γ ∈ pCoreOf 2 (stabS S ⊓ Ω) ↔
        conjEW e γ ∈ pCoreOf 2 (Model.stabM Model.Sm ⊓ Ω.map (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM))) := by
      rw [← hmapA]
      exact hmem
    rw [hmem']
    have hfγ : conjEW e γ ∈ Model.stabM Model.Sm ⊓ Ω.map (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM)) :=
      Subgroup.mem_inf.2 ⟨(stabS_conj_iff S e hSe γ).1 (Subgroup.mem_inf.1 hγ).1,
        Subgroup.mem_map.2 ⟨γ, (Subgroup.mem_inf.1 hγ).2, rfl⟩⟩
    rw [← M4 (conjEW e γ) hfγ]
    constructor
    · intro h s hs
      have hes : e.symm s ∈ S := (hSe _).2 (by rw [e.apply_symm_apply]; exact hs)
      rw [conjE_apply, h _ hes, e.apply_symm_apply]
    · intro h s hs
      have h' := h (e s) ((hSe s).1 hs)
      rw [conjE_apply, e.symm_apply_apply] at h'
      exact e.injective h'
  exact ⟨C1, C2, C3, C4⟩

end Main

end CFSG.Quasithin.H13.C1294

end

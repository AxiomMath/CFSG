module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Sec45Shape
import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelScalar

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 RootHyp
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

theorem subW_iSup {ι : Type*}
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (f : ι → Subgroup G) (hf : ∀ i, f i ≤ Tim79a.xOf V H) :
    subW hW (⨆ i, f i) = ⨆ i, subW hW (f i) := by
  apply le_antisymm
  · have hle : (⨆ i, f i) ≤ subgroupOfSubW hW (⨆ i, subW hW (f i)) := by
      refine iSup_le fun i => ?_
      intro x hx
      exact ⟨hf i hx, Submodule.mem_iSup_of_mem i ((mem_subW_iff hW).mpr hx)⟩
    calc subW hW (⨆ i, f i) ≤ subW hW (subgroupOfSubW hW (⨆ i, subW hW (f i))) :=
          subW_mono hle
      _ = ⨆ i, subW hW (f i) := subW_subgroupOfSubW hW _
  · exact iSup_le fun i => subW_mono (le_iSup f i)

namespace Sec45Shape

variable {h₀ : G}

private theorem exists_sylow_conj (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l)) {ψ : HBar V H ≃* SL(2, F)}
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {y : G} (hy : y ∈ H) :
    ∃ S : Subgroup SL(2, F), (∀ a ∈ S, a * a = 1) ∧
      Nat.card S = 2 ^ (2 * l) ∧
        fixedSub (repW (hW := hW) ψ) S = subW hW (conjSubgroup y V) := by
  have hA := RootHyp.imgK_map_sl2 h hS.Pc_le hS.le_pCore hS.hH hS.not_le ψ
  have hconj : (imgK V H (conjSubgroup y (Pc M V))).map (ψ : HBar V H →* SL(2, F)) =
      conjSubgroup (ψ (piK V H ⟨y, hy⟩))
        ((imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F))) := by
    rw [imgK_conjSubgroup hy hS.Pc_le]
    exact map_conjSubgroup_mulEquiv ψ (piK V H ⟨y, hy⟩) (imgK V H (Pc M V))
  refine ⟨(imgK V H (conjSubgroup y (Pc M V))).map (ψ : HBar V H →* SL(2, F)),
    ?_, ?_, ?_⟩
  · intro a ha
    set c : SL(2, F) := ψ (piK V H ⟨y, hy⟩) with hc
    rw [hconj, mem_conjSubgroup] at ha
    calc a * a = c * (c⁻¹ * a * c) * (c⁻¹ * a * c) * c⁻¹ := by group
      _ = c * ((c⁻¹ * a * c) * (c⁻¹ * a * c)) * c⁻¹ := by group
      _ = 1 := by rw [hA.1 _ ha]; group
  · rw [hconj, card_conjSubgroup]
    exact hA.2.1.trans hl
  · rw [fixedSub_repW hW ψ (conjSubgroup_le_of_le_of_mem hS.Pc_le hy),
      h.xOf_inf_centralizer_conj_Pc hy]


private theorem maps_subW_of_commute {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (hl : Fintype.card F = 2 ^ (2 * l)) {ψ : HBar V H ≃* SL(2, F)}
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {s : Additive (IntMod (Tim79a.xOf V H) hW) →+
      Additive (IntMod (Tim79a.xOf V H) hW)}
    (hs : ∀ (g : SL(2, F)) (x : Additive (IntMod (Tim79a.xOf V H) hW)),
      s (repW (hW := hW) ψ g x) = repW (hW := hW) ψ g (s x))
    {A : Subgroup G} (hA : A ∈ Tim79a.omegaOf V H) :
    ∀ x ∈ subW hW A, s x ∈ subW hW A := by
  obtain ⟨y, hy, hAy⟩ := Tim79a.mem_omegaOf.mp hA
  obtain ⟨S, -, -, hSfix⟩ := exists_sylow_conj h hS hl hW hy
  have hfix : fixedSub (repW (hW := hW) ψ) S = subW hW A := by
    rw [hSfix, hAy]
  intro x hx
  have hx' : x ∈ fixedSub (repW (hW := hW) ψ) S := hfix ▸ hx
  have hmem : s x ∈ fixedSub (repW (hW := hW) ψ) S := by
    rw [mem_fixedSub] at hx' ⊢
    intro g hg
    rw [← hs g x, hx' g hg]
  rwa [hfix] at hmem

private theorem maps_iSup_subW_of_commute {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] [Fintype F] [CharP F 2] {l : ℕ}
    (hl : Fintype.card F = 2 ^ (2 * l)) {ψ : HBar V H ≃* SL(2, F)}
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {s : Additive (IntMod (Tim79a.xOf V H) hW) →+
      Additive (IntMod (Tim79a.xOf V H) hW)}
    (hs : ∀ (g : SL(2, F)) (x : Additive (IntMod (Tim79a.xOf V H) hW)),
      s (repW (hW := hW) ψ g x) = repW (hW := hW) ψ g (s x))
    {𝒯 : Set (Subgroup G)} (h𝒯 : 𝒯 ⊆ Tim79a.omegaOf V H) :
    ∀ x ∈ ⨆ A : {A : Subgroup G // A ∈ 𝒯}, subW hW A.1,
      s x ∈ ⨆ A : {A : Subgroup G // A ∈ 𝒯}, subW hW A.1 := by
  intro x hx
  refine Submodule.iSup_induction (p := fun A : {A : Subgroup G // A ∈ 𝒯} => subW hW A.1)
    (motive := fun x => s x ∈ ⨆ A : {A : Subgroup G // A ∈ 𝒯}, subW hW A.1) hx ?_ ?_ ?_
  · intro A x hxA
    exact Submodule.mem_iSup_of_mem A
      (maps_subW_of_commute (hW := hW) (hl := hl) (ψ := ψ) (h := h) (hS := hS)
        (hs := hs) (hA := h𝒯 A.2) x hxA)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx' hy'
    rw [map_add]
    exact Submodule.add_mem _ hx' hy'

theorem le_of_inf_ne_bot (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {𝒯 : Set (Subgroup G)} (h𝒯 : 𝒯 ⊆ Tim79a.omegaOf V H) {C : Subgroup G}
    (hC : C ∈ Tim79a.omegaOf V H)
    (hne : C ⊓ (⨆ A ∈ 𝒯, A) ≠ ⊥) : C ≤ ⨆ A ∈ 𝒯, A := by
  classical
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hW := hS.isElemAbelian h
  haveI hmod : Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    moduleOfElemAbelian hW
  have horth : Sec2.IsOrthModule hl (repW (hW := hW) ψ) :=
    IsOrthModule.repW_of_subRepW hW ψ hl (hw.orth_subRepW hW)
  obtain ⟨𝔰, hcomm, htrans⟩ := horth.exists_scalars
  let Y : Subgroup G := ⨆ A ∈ 𝒯, A
  have hYle : Y ≤ Tim79a.xOf V H := iSup₂_le fun A hA => Tim79a.le_xOf (h𝒯 hA)
  have hCle : C ≤ Tim79a.xOf V H := Tim79a.le_xOf hC
  let U : Submodule (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    ⨆ A : {A : Subgroup G // A ∈ 𝒯}, subW hW A.1
  have hYeq : Y = ⨆ A : {A : Subgroup G // A ∈ 𝒯}, A.1 := by
    rw [show Y = ⨆ A : Subgroup G, ⨆ (_ : A ∈ 𝒯), A from rfl]
    exact iSup_subtype' (p := fun A : Subgroup G => A ∈ 𝒯) (f := fun A _ => A)
  have hUY : U = subW hW Y := by
    rw [hYeq, subW_iSup (hW := hW)
      (f := fun A : {A : Subgroup G // A ∈ 𝒯} => A.1) (fun A => Tim79a.le_xOf (h𝒯 A.2))]
  have hpres : ∀ s ∈ 𝔰, ∀ x ∈ U, s x ∈ U := fun s hs =>
    maps_iSup_subW_of_commute (hW := hW) (hl := hl) (ψ := ψ) (h := h) (hS := hS)
      (hs := fun g x => hcomm s hs g x) (h𝒯 := h𝒯)
  have hbot : subW hW (C ⊓ Y) ≠ ⊥ := by
    intro hbot
    apply hne
    refine (subW_inj (hW := hW) (E := C ⊓ Y) (F := ⊥)
      (le_trans inf_le_left hCle) bot_le).mp ?_
    rw [hbot, subW_bot]
  have hbotU : subW hW C ⊓ U ≠ ⊥ := by
    rw [hUY, ← subW_inf]
    exact hbot
  obtain ⟨v₀, hv₀, hv₀ne⟩ := (Submodule.ne_bot_iff (subW hW C ⊓ U)).mp hbotU
  obtain ⟨yC, hyC, hCy⟩ := Tim79a.mem_omegaOf.mp hC
  obtain ⟨S, hS2, hScard, hSfix⟩ := exists_sylow_conj h hS hl hW hyC
  have hCfix : fixedSub (repW (hW := hW) ψ) S = subW hW C := by
    rw [hSfix, hCy]
  have hleU : subW hW C ≤ U := by
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0]
      exact U.zero_mem
    · have hmem₀ : v₀ ∈ fixedSub (repW (hW := hW) ψ) S := by
        rw [hCfix]
        exact hv₀.1
      have hmem : v ∈ fixedSub (repW (hW := hW) ψ) S := by
        rw [hCfix]
        exact hv
      obtain ⟨s, hs, hsv⟩ := htrans S hS2 hScard v₀ hmem₀ v hmem hv₀ne hv0
      rw [← hsv]
      exact hpres s hs v₀ hv₀.2
  have hsub : subW hW C ≤ subW hW Y := by
    rw [← hUY]
    exact hleU
  exact (subW_le_subW_iff hCle).mp hsub

end Sec45Shape

end CFSG.RankThree.GF2n.Tim81

module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenModChief
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.IrrSec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits Equiv
open CFSG.Quasithin.F53.Stellmacher.S43.Even
open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs (secData_secModule)
open scoped commutatorElement

namespace F53.Stellmacher.S35.G7

variable {G : Type} [Group G] [Finite G]

structure WBase (X E K W : Subgroup G) (θ : ↥X →* Perm (Fin 5)) where
  mod : Model 5
  proj : ↥W →* mod.W
  proj_surj : Function.Surjective proj
  proj_eq_one : ∀ w : ↥W, proj w = 1 ↔ (w : G) ∈ K
  proj_conj : ∀ (g : ↥X) (w : ↥W) (h : (g : G) * (w : G) * (g : G)⁻¹ ∈ W),
    mod.act (θ g) (proj w) = proj ⟨(g : G) * (w : G) * (g : G)⁻¹, h⟩
  faithful : mod.Faithful
  t : Perm (Fin 5)
  idx_t : idx mod t = 2
  π : mod.W →* orth.W
  π_surj : Function.Surjective π
  π_act : ∀ (σ : Perm (Fin 5)) (m : mod.W), π (mod.act σ m) = orth.act σ (π m)
  π_proj : ∀ w : ↥W, π (proj w) = 1 ↔ (w : G) ∈ E

namespace WM

variable {X V K E W : Subgroup G}

omit [Finite G] in
theorem isNormalIn_of_normalizer (hEW : E ≤ W) (h : X ≤ Subgroup.normalizer (E : Set G)) :
    IsNormalIn X W E :=
  ⟨hEW, fun _ hg x hx => (Subgroup.mem_normalizer_iff.mp (h hg) x).mp hx⟩

omit [Finite G] in
theorem mem_cSecIn_of_le {F : Subgroup G} (hKE : K ≤ E) {x : G}
    (hx : x ∈ cSecIn F K W) : x ∈ cSecIn F E W := by
  have hsub : {f | f ∈ F ∧ ∀ y ∈ W, f * y * f⁻¹ * y⁻¹ ∈ K} ⊆
      {f | f ∈ F ∧ ∀ y ∈ W, f * y * f⁻¹ * y⁻¹ ∈ E} :=
    fun f hf => ⟨hf.1, fun w hw => hKE (hf.2 w hw)⟩
  exact Subgroup.closure_mono hsub hx

omit [Finite G] in
theorem ker_le_cSecIn {θ : ↥X →* Perm (Fin 5)} {P : Subgroup G}
    (hker : θ.ker = P.subgroupOf X) (hP : ∀ w ∈ W, ∀ q ∈ P, ⁅w, q⁆ ∈ K) :
    θ.ker ≤ (cSecIn X K W).subgroupOf X := by
  intro x hx
  rw [hker, Subgroup.mem_subgroupOf] at hx
  rw [Subgroup.mem_subgroupOf]
  refine Subgroup.subset_closure ⟨x.2, fun w hw => ?_⟩
  have h1 := hP w hw x hx
  have : (x : G) * w * (x : G)⁻¹ * w⁻¹ = ⁅w, (x : G)⁆⁻¹ := by
    rw [commutatorElement_def]; group
  rw [this]
  exact K.inv_mem h1


theorem exists_wbase (hsec : IsSec X V W) (hWX : W ≤ X) (hVK : V ≤ K) (hKE : K ≤ E)
    (hEW : E ≤ W) (hnK : X ≤ Subgroup.normalizer (K : Set G))
    (hnE : X ≤ Subgroup.normalizer (E : Set G)) (horth : IsOrthSec X E W)
    (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5))) {θ : ↥X →* Perm (Fin 5)}
    (hθ : Function.Surjective θ) (hker : θ.ker = (pCoreOf 2 X).subgroupOf X)
    (hP : ∀ w ∈ W, ∀ q ∈ pCoreOf 2 X, ⁅w, q⁆ ∈ K) {y : G} (hy : y ∈ X)
    (hyQ : y ∉ pCoreOf 2 X) (hV2 : secIdx (Subgroup.zpowers y) V W = 2)
    (hE2 : secIdx (Subgroup.zpowers y) E W = 2) : Nonempty (WBase X E K W θ) := by
  have hsK : IsSec X K W := EvenMod.isSec_of_ge hsec hVK (hKE.trans hEW) hnK
  have hsE : IsSec X E W := EvenMod.isSec_of_ge hsec (hVK.trans hKE) hEW hnE
  have hkK : θ.ker ≤ (cSecIn X K W).subgroupOf X := WM.ker_le_cSecIn hker hP
  have hkE : θ.ker ≤ (cSecIn X E W).subgroupOf X :=
    WM.ker_le_cSecIn hker fun w hw q hq => hKE (hP w hw q hq)
  have hnK' : (K.subgroupOf W).Normal := hsK.normal_subgroupOf
  have hnE' : (E.subgroupOf W).Normal := hsE.normal_subgroupOf
  have hirr : (secModule hsE θ hθ hkE).IsIrred := by
    refine (secModule_isIrred_iff hsE θ hθ hkE (WM.isNormalIn_of_normalizer le_rfl hsec.normN)
      (WM.isNormalIn_of_normalizer hEW hnE)).mpr ⟨WM.isNormalIn_of_normalizer le_rfl hsec.normN,
      WM.isNormalIn_of_normalizer hEW hnE, lt_of_le_of_ne hEW fun h => ?_, fun K' hK' hEK' hK'W =>
      horth.irred K' hEK' hK'W (EvenMod.le_normalizer_of_isNormalIn hK')⟩
    have h16 := horth.relIndex_eq
    rw [h, Subgroup.relIndex_self] at h16
    omega
  have hidxE : idx (secModule hsE θ hθ hkE) (θ ⟨y, hy⟩) = 2 := by
    rw [← (secData_secModule hsE θ hθ hkE).secIdx_eq_idx hEW hy]
    exact hE2
  have ht1 : θ ⟨y, hy⟩ ≠ 1 := fun h => hyQ (by
    have h1 : (⟨y, hy⟩ : ↥X) ∈ θ.ker := h
    rw [hker, Subgroup.mem_subgroupOf] at h1
    exact h1)
  have hnt : ∃ σ w, (secModule hsE θ hθ hkE).act σ w ≠ w := by
    by_contra hcon
    push Not at hcon
    have h1 : fixW (secModule hsE θ hθ hkE) (Subgroup.zpowers (θ ⟨y, hy⟩)) = ⊤ := by
      refine eq_top_iff.mpr fun w _ => ?_
      rw [mem_fixW]
      intro b _
      exact hcon b w
    have h2 : idx (secModule hsE θ hθ hkE) (θ ⟨y, hy⟩) = 1 := by
      unfold idx
      rw [h1, Subgroup.index_top]
    omega
  obtain ⟨e⟩ : Nonempty ((secModule hsE θ hθ hkE).Iso orth) := by
    rcases model5_irred_classification _ hirr hnt with h | h
    · exact h
    · exfalso
      obtain ⟨e⟩ := h
      have h4 := (transvections _ ht1).1
      rw [e.idx_eq, hidxE] at h4
      omega
  let f : (secModule hsK θ hθ hkK).W →* orth.W :=
    QuotientGroup.lift (K.subgroupOf W) (e.toMulEquiv.toMonoidHom.comp hsE.proj) (by
      intro x hx
      rw [MonoidHom.mem_ker]
      show e.toMulEquiv (hsE.proj x) = 1
      rw [(hsE.proj_eq_one_iff x).mpr (hKE (Subgroup.mem_subgroupOf.mp hx))]
      exact map_one e.toMulEquiv)
  have hf : ∀ w : ↥W, f (hsK.proj w) = e.toMulEquiv (hsE.proj w) := fun w => rfl
  have hidxK : secIdx (Subgroup.zpowers y) K W = 2 := by
    refine le_antisymm ?_ ?_
    · exact hV2 ▸ EvenMod.secIdx_le_secIdx hWX hsec.normL hnK hsec.normN hVK (hKE.trans hEW)
        le_rfl hy
    · exact hE2 ▸ EvenMod.secIdx_le_secIdx hWX hnK hnE hsec.normN hKE hEW le_rfl hy
  refine ⟨⟨secModule hsK θ hθ hkK, hsK.proj, hsK.proj_surjective, hsK.proj_eq_one_iff,
    fun g w _ => secModule_act_proj hsK θ hθ hkK g w, ?_, θ ⟨y, hy⟩, ?_, f, ?_, ?_, ?_⟩⟩
  · refine (secModule_faithful_iff hsK θ hθ hkK).mpr fun x hx => ?_
    have h1 := WM.mem_cSecIn_of_le hKE (Subgroup.mem_subgroupOf.mp hx)
    rw [IsModelSec.cSecIn_eq_pCoreOf horth hq] at h1
    rw [hker]
    exact Subgroup.mem_subgroupOf.mpr h1
  · rw [← (secData_secModule hsK θ hθ hkK).secIdx_eq_idx hsK.le hy]
    exact hidxK
  · intro o
    obtain ⟨w, hw⟩ := hsE.proj_surjective (e.toMulEquiv.symm o)
    exact ⟨hsK.proj w, by rw [hf, hw]; exact e.toMulEquiv.apply_symm_apply o⟩
  · intro σ m
    obtain ⟨g, rfl⟩ := hθ σ
    obtain ⟨w, rfl⟩ := hsK.proj_surjective m
    rw [secModule_act_proj hsK θ hθ hkK g w, hf, hf]
    change e.toMulEquiv (hsE.proj (hsE.conjN g w)) = _
    rw [← secModule_act_proj hsE θ hθ hkE g w]
    exact e.map_act _ _
  · intro w
    show e.toMulEquiv (hsE.proj w) = 1 ↔ _
    exact e.toMulEquiv.map_eq_one_iff.trans (hsE.proj_eq_one_iff w)

end WM

end F53.Stellmacher.S35.G7

end CFSG.Quasithin

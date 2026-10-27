module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupRoots
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
import TauCeti.GroupTheory.Coxeter.Geometric

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem ggDMemberRoots_subsys {G : Type} [Group G] {L Bs : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {k : ℕ} (hk : 2 ≤ k)
    (φ : M.Group ≃* ggWeylD k) (X : Subgroup G) :
    GGDSubsys k (ggDMemberRoots e φ X) := by
  refine ⟨?_, ?_⟩
  · rintro γ ⟨t, ht, -⟩
    exact ht.mem (by omega)
  · rintro γ ⟨t, ht, htX⟩ δ ⟨t', ht', ht'X⟩
    refine ⟨t * t' * t⁻¹, ?_, ?_⟩
    · rw [map_mul, map_mul, map_inv]
      exact ht'.conj (ht.action hk)
    · have h := mul_mem (mul_mem htX ht'X) (inv_mem htX)
      simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h

theorem ggDk_memberRoots_subsys
    (hpos : GGSecFiveKGPosInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι}
    (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a) :
    (∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → GGDSubsys k (ggDMemberRoots e φ X)) ∧
    GGDIrred (ggDMemberRoots e φ L) ∧
    ∀ v : Fin k → ℤ,
      (∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ∀ η ∈ ggDMemberRoots e φ X, ggDDot v η = 0) →
        v = 0 := by
  have hk2 : 2 ≤ k := by omega
  obtain ⟨τ, n, q, _ψ, hadm, -, -, -, hτ, -, ε, hεr, -⟩ :=
    hpos G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 L (Or.inl rfl) hsplit
  let M' : CoxeterMatrix (Fin (ggU τ n q).D.rank) := coxeterMatrix (ggU τ n q).D.isFiniteType
  have hLA : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)
  let j : M'.Group →* M.Group :=
    e.symm.toMonoidHom.comp ((Subgroup.inclusion hLA).comp ε.toMonoidHom)
  have hj : ∀ w, ((e (j w) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
      ((ε w : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := fun w =>
    congrArg Subtype.val (e.apply_symm_apply (Subgroup.inclusion hLA (ε w)))
  have hjinj : ∀ w w', j w = j w' → w = w' := fun w w' h =>
    ε.injective (Subtype.val_injective ((hj w).symm.trans
      ((congrArg (fun z => ((e z : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) h).trans (hj w'))))
  have hroot : ∀ a, ∃ η, GGDReflRoot k (φ (j (M'.simple a))) η := by
    intro a
    obtain ⟨w, i, hwi⟩ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3
      (hLA (ε (M'.simple a)).2) (hεr a)
    have hji : j (M'.simple a) = w * M.simple i * w⁻¹ :=
      e.injective (Subtype.val_injective ((hj _).trans hwi))
    rw [hji]
    exact exists_ggDReflRoot_of_conj φ hφ w i
  choose η hη using hroot
  have hηL : ∀ a, η a ∈ ggDMemberRoots e φ L := fun a =>
    ⟨_, hη a, by rw [hj]; exact (ε _).2⟩
  have hfixL : ∀ v : Fin k → ℤ, (∀ a, ggDDot v (η a) = 0) → ∀ w, φ (j w) ∈ ggDFix k v := by
    intro v hv w
    refine M'.toCoxeterSystem.simple_induction (p := fun w => φ (j w) ∈ ggDFix k v) w
      (fun a => (hη a).mem_ggDFix hk2 (hv a)) ?_ fun w w' hw hw' => ?_
    · simp only [map_one]
      exact one_mem _
    · simp only [map_mul]
      exact mul_mem hw hw'
  refine ⟨fun X _ => ggDMemberRoots_subsys hk2 φ X, ?_, fun v hv => ?_⟩
  ·
    obtain ⟨hW, h3'⟩ := ggTag_weylMatrix hτ hadm
    refine ggDIrred_of_connected η hηL (ggSimplyLacedConnected_of_weyl hW h3').2
      (fun a b hab h0 => ?_) fun γ hγ => ?_
    ·
      have hab' : M'.M a b = 3 := hab
      have hc := (hη a).commute_of_dot_eq_zero hk2 (hη b) h0
      have hc' : M'.simple a * M'.simple b = M'.simple b * M'.simple a :=
        hjinj _ _ (φ.injective (by simp only [map_mul]; exact hc))
      have ha2 : M'.simple a ^ 2 = 1 := M'.toCoxeterSystem.simple_sq a
      have hb2 : M'.simple b ^ 2 = 1 := M'.toCoxeterSystem.simple_sq b
      have hsq : (M'.simple a * M'.simple b) ^ 2 = 1 := by
        rw [(show Commute (M'.simple a) (M'.simple b) from hc').mul_pow, ha2, hb2, one_mul]
      have hord : orderOf (M'.simple a * M'.simple b) = M'.M a b :=
        M'.toCoxeterSystem.orderOf_simple_mul_simple a b
      have h32 := orderOf_dvd_of_pow_eq_one hsq
      rw [hord, hab'] at h32
      omega
    ·
      obtain ⟨t₀, ht₀, ht₀L⟩ := hγ
      by_contra hno
      have hjt : j (ε.symm ⟨_, ht₀L⟩) = t₀ := e.injective (Subtype.val_injective
        ((hj _).trans (by rw [MulEquiv.apply_symm_apply])))
      have h1 : φ t₀ ∈ ggDFix k γ := by
        rw [← hjt]
        refine hfixL γ (fun a => ?_) _
        by_contra h
        exact hno ⟨a, by rwa [ggDDot_comm]⟩
      have h0 := ht₀.dot_eq_zero_of_mem_ggDFix hk2 h1
      rw [ggDDot_self_of_mem (ht₀.mem (by omega))] at h0
      omega
  ·
    let F : M.Group →* MulAut ↥Bs := (ggAutomizerJoin L Bs 𝒦).subtype.comp e.toMonoidHom
    have hF : Function.Injective F := Subtype.val_injective.comp e.injective
    let H : Subgroup M.Group := (ggDFix k v).comap φ.toMonoidHom
    have hAL : ggAutomizer L Bs ≤ H.map F := fun r hr => by
      obtain ⟨w, rfl⟩ : ∃ w, ((ε w : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) = r :=
        ⟨ε.symm ⟨r, hr⟩, by rw [MulEquiv.apply_symm_apply]⟩
      exact Subgroup.mem_map.2 ⟨j w, Subgroup.mem_comap.2
        (hfixL v (fun a => hv L (Or.inl rfl) (η a) (hηL a)) w), hj w⟩
    have hAK : ∀ K ∈ 𝒦, ggAutomizer K Bs ≤ H.map F := by
      intro K hK
      obtain ⟨y, hy⟩ := hcfg.2.2.2.1.2 K hK
      refine (hcfg.2.1 y K hy).le.trans ((Subgroup.closure_le _).2 fun r hr => ?_)
      obtain ⟨hrK, hrr⟩ := hr
      obtain ⟨w, i, rfl⟩ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3
        (ggAutomizer_le_ggAutomizerJoin (Or.inr hK) hrK) hrr
      obtain ⟨η', hη'⟩ := exists_ggDReflRoot_of_conj φ hφ w i
      exact Subgroup.mem_map.2 ⟨w * M.simple i * w⁻¹,
        Subgroup.mem_comap.2 (hη'.mem_ggDFix hk2 (hv K (Or.inr hK) η' ⟨_, hη', hrK⟩)), rfl⟩
    have hAll : ggAutomizerJoin L Bs 𝒦 ≤ H.map F := sup_le hAL (iSup₂_le hAK)
    refine eq_zero_of_top_le_ggDFix hk2 fun u _ => ?_
    obtain ⟨t', ht', hFt'⟩ := Subgroup.mem_map.1 (hAll (e (φ.symm u)).2)
    have h1 : t' = φ.symm u := hF hFt'
    rw [h1] at ht'
    simpa using Subgroup.mem_comap.1 ht'

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupMemberRoots
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupRoots
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpCount
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpSignedA
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpSignedTop
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpFix
import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedTits
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsPairs
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsWeyl
import TauCeti.GroupTheory.Coxeter.Geometric

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

private theorem dot_of_comm {k : ℕ} (hk : 2 ≤ k) {t t' : ggWeylD k} {γ γ' : Fin k → ℤ}
    (h : GGDReflRoot k t γ) (h' : GGDReflRoot k t' γ') (hc : t * t' = t' * t) :
    ggDDot γ γ' = 0 ∨ γ' = γ ∨ γ' = -γ := by
  obtain ⟨w, i, -, hw⟩ := id h
  have key := congrArg (fun g => toStdD k (weylAction (isFiniteType_cartanD k) g
    (weylAction (isFiniteType_cartanD k) w (Pi.single i 1)))) hc
  simp only [weylAction_mul_apply, h.action hk, h'.action hk, hw] at key
  exact ggDReflect_comm_dot (ggDDot_self_of_mem (h.mem (by omega)))
    (ggDDot_self_of_mem (h'.mem (by omega))) key

private theorem eq_signedA {k : ℕ} {ε : Fin k → ℤ} (hε : ∀ a, ε a = 1 ∨ ε a = -1)
    {γ : Fin k → ℤ} (hγ : γ ∈ ggDRootSet k) (h0 : ggDDot ε γ = 0) :
    ∃ a b : Fin k, a ≠ b ∧ γ = Pi.single a (ε a) - Pi.single b (ε b) := by
  obtain ⟨a, b, s, u, hab, hs, hu, rfl⟩ := hγ
  rw [ggDDot_comm, ggDDot_single_add_single] at h0
  rcases hε a with ha | ha <;> rcases hε b with hb | hb <;> rcases hs with rfl | rfl <;>
    rcases hu with rfl | rfl <;> rw [ha, hb] at h0 <;> norm_num at h0 <;>
    first
    | (refine ⟨a, b, hab, ?_⟩; simp only [ha, hb, sub_eq_add_neg, Pi.single_neg, neg_neg]; done)
    | (refine ⟨b, a, hab.symm, ?_⟩; simp only [ha, hb, sub_eq_add_neg, Pi.single_neg]; abel)

theorem ggDk_memberRoots_L
    (hKG : GGSecFiveKGPosInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι}
    (hM : M = (ggCoxeterMatrixD k).reindex σ) (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    (hss : GGDNoSameSupp e φ) :
    Nat.card Bs = p ^ k ∧ ∃ ε : Fin k → ℤ, (∀ a, ε a = 1 ∨ ε a = -1) ∧
      ggDMemberRoots e φ L =
        {η | ∃ a b : Fin k, a ≠ b ∧ η = Pi.single a (ε a) - Pi.single b (ε b)} ∧
      ∃ xb : ↥Bs, (xb : G) = x ∧ ∀ (u : M.Group) (η : Fin k → ℤ), GGDReflRoot k (φ u) η →
        ((((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) xb = xb) ↔ ggDDot ε η = 0) := by
  have hk2 : 2 ≤ k := by omega
  have hW : GGWeylOfType p (ggCoxeterMatrixD k) (ggAutomizerJoin L Bs 𝒦) := by
    subst hM
    exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
  have hΦ := (ggDk_memberRoots_subsys hKG hcfg hsplit hpres hle3 hk φ hφ).1 L (Or.inl rfl)
  obtain ⟨tg, n, f, _ψ, hadm, -, -, -, htag, -, hTB⟩ :=
    hKG G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 L (Or.inl rfl) hsplit
  obtain ⟨hlow, hup, hkℓ⟩ := ggDk_card_bstar_bounds hcfg hpres hk hM hTB
  obtain ⟨ε', hεr, -, -⟩ := hTB
  let M' : CoxeterMatrix (Fin (ggU tg n f).D.rank) := coxeterMatrix (ggU tg n f).D.isFiniteType
  have hLA : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)
  let j : M'.Group →* M.Group :=
    e.symm.toMonoidHom.comp ((Subgroup.inclusion hLA).comp ε'.toMonoidHom)
  have hj : ∀ w, ((e (j w) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
      ((ε' w : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := fun w =>
    congrArg Subtype.val (e.apply_symm_apply (Subgroup.inclusion hLA (ε' w)))
  have hjinj : Function.Injective j := fun w w' h => ε'.injective (Subtype.val_injective
    ((hj w).symm.trans ((congrArg (fun z => ((e z : ↥(ggAutomizerJoin L Bs 𝒦)) :
      MulAut ↥Bs)) h).trans (hj w'))))
  have hroot : ∀ a, ∃ η, GGDReflRoot k (φ (j (M'.simple a))) η := fun a => by
    obtain ⟨w, i, hwi⟩ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3
      (hLA (ε' (M'.simple a)).2) (hεr a)
    rw [show j (M'.simple a) = w * M.simple i * w⁻¹ from
      e.injective (Subtype.val_injective ((hj _).trans hwi))]
    exact exists_ggDReflRoot_of_conj φ hφ w i
  choose η hη using hroot
  have hηL : ∀ a, η a ∈ ggDMemberRoots e φ L := fun a =>
    ⟨_, hη a, by rw [hj]; exact (ε' _).2⟩
  have hfixL : ∀ v : Fin k → ℤ, (∀ a, ggDDot v (η a) = 0) → ∀ w, φ (j w) ∈ ggDFix k v := by
    intro v hv w
    refine M'.toCoxeterSystem.simple_induction (p := fun w => φ (j w) ∈ ggDFix k v) w
      (fun a => (hη a).mem_ggDFix hk2 (hv a)) ?_ fun w w' hw hw' => ?_
    · simp only [map_one]
      exact one_mem _
    · simp only [map_mul]
      exact mul_mem hw hw'
  obtain ⟨hW', h3'⟩ := ggTag_weylMatrix htag hadm
  have hsi : Function.Injective M'.simple := by
    rw [← CoxeterMatrix.toCoxeterSystem_simple]
    exact CoxeterSystem.simple_injective _
  have hne : ∀ a b, a ≠ b → η b ≠ η a ∧ η b ≠ -η a := fun a b hab => by
    have h : φ (j (M'.simple a)) ≠ φ (j (M'.simple b)) := fun h =>
      hab (hsi (hjinj (φ.injective h)))
    exact ⟨fun h' => h ((hη a).unique hk2 (hη b) (Or.inl h')),
      fun h' => h ((hη a).unique hk2 (hη b) (Or.inr h'))⟩
  have hdot2 : ∀ a b, a ≠ b → M'.M a b = 2 → ggDDot (η a) (η b) = 0 := fun a b hab h2 => by
    have hc := congrArg (fun w => φ (j w)) (ggSimplyLaced_simple_comm h2)
    simp only [map_mul] at hc
    rcases dot_of_comm hk2 (hη a) (hη b) hc with h | h | h
    · exact h
    · exact absurd h (hne a b hab).1
    · exact absurd h (hne a b hab).2
  have hdot3 : ∀ a b, M'.M a b = 3 → ggDDot (η a) (η b) ≠ 0 := fun a b hab h0 => by
    have hc := (hη a).commute_of_dot_eq_zero hk2 (hη b) h0
    have hc' : M'.simple a * M'.simple b = M'.simple b * M'.simple a :=
      hjinj (φ.injective (by simp only [map_mul]; exact hc))
    have ha2 : M'.simple a ^ 2 = 1 := M'.toCoxeterSystem.simple_sq a
    have hb2 : M'.simple b ^ 2 = 1 := M'.toCoxeterSystem.simple_sq b
    have hsq : (M'.simple a * M'.simple b) ^ 2 = 1 := by
      rw [(show Commute (M'.simple a) (M'.simple b) from hc').mul_pow, ha2, hb2, one_mul]
    have hord : orderOf (M'.simple a * M'.simple b) = M'.M a b :=
      M'.toCoxeterSystem.orderOf_simple_mul_simple a b
    have h32 := orderOf_dvd_of_pow_eq_one hsq
    rw [hord, hab] at h32
    omega
  obtain ⟨hℓk, ε, hε, hεη, hP⟩ :=
    ggDk_signedA_of_weyl hΦ (hss L (Or.inl rfl)) hW' h3' η hηL hne hdot2 hdot3 hkℓ
  have hcard : Nat.card Bs = p ^ k := le_antisymm (by rw [← hℓk]; exact hup) hlow
  have hset : ggDMemberRoots e φ L =
      {η | ∃ a b : Fin k, a ≠ b ∧ η = Pi.single a (ε a) - Pi.single b (ε b)} := by
    ext γ
    refine ⟨fun hγ => eq_signedA hε (hΦ.1 hγ) ?_, ?_⟩
    · obtain ⟨t, ht, htL⟩ := hγ
      have hjt : j (ε'.symm ⟨_, htL⟩) = t := e.injective (Subtype.val_injective
        ((hj _).trans (by rw [MulEquiv.apply_symm_apply])))
      have h1 : φ t ∈ ggDFix k ε := by
        rw [← hjt]
        exact hfixL ε hεη _
      exact ht.dot_eq_zero_of_mem_ggDFix hk2 h1
    · rintro ⟨a, b, hab, rfl⟩
      exact hP a b hab
  obtain ⟨-, hxB, hx1, hLcomp, -⟩ := hcfg.1.1.1.2.2.2.2.2.2.1
  let xb : ↥Bs := ⟨x, hcfg.1.1.2.1.1 hxB⟩
  have hfix : ∀ (u : M.Group) (γ : Fin k → ℤ), GGDReflRoot k (φ u) γ → ggDDot ε γ = 0 →
      ((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) xb = xb := by
    intro u γ hu h0
    obtain ⟨a, b, hab, rfl⟩ := eq_signedA hε (hu.mem (by omega)) h0
    obtain ⟨t, ht, htL⟩ := hP a b hab
    rw [φ.injective (hu.unique hk2 ht (Or.inl rfl))]
    exact ggAutomizer_apply_eq_of_le_centralizer (x := xb) hLcomp.1 htL
  refine ⟨hcard, ε, hε, hset, xb, rfl, fun u γ hu => ⟨fun hx => ?_, hfix u γ hu⟩⟩
  by_contra h0
  let H : Subgroup (ggWeylD k) := (MulAction.stabilizer (MulAut ↥Bs) xb).comap
    ((ggAutomizerJoin L Bs 𝒦).subtype.comp (e.toMonoidHom.comp φ.symm.toMonoidHom))
  have hH : ∀ w, w ∈ H ↔ ((e (φ.symm w) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) xb = xb :=
    fun w => Iff.rfl
  have htop := ggDk_eq_top_of_signedA hk hε (H := H) (fun t γ ht hγ => (hH t).2
    (hfix (φ.symm t) γ (by rwa [MulEquiv.apply_symm_apply]) hγ)) hu h0
    ((hH (φ u)).2 (by rwa [MulEquiv.symm_apply_apply]))
  have hb : ∀ ψ ∈ ggAutomizerJoin L Bs 𝒦, ψ xb = xb := fun ψ hψ => by
    have h := (hH (φ (e.symm ⟨ψ, hψ⟩))).1 (by rw [htop]; exact Subgroup.mem_top _)
    rwa [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply] at h
  exact hx1 (congrArg Subtype.val (ggWeylD_eq_one_of_fixed hcfg.1.1.1.2.2.2.2.2.1.1
    hcfg.1.1.1.2.2.2.2.2.1.2.1 (ggRouteCfg_isElemAbelian hcfg) (ggRouteCfg_noTransvection hcfg)
    hk hW (fun ψ hψ => mem_ggInduced_top_of_mem_ggAutomizer (ggAutomizerJoin_le_top L Bs 𝒦 hψ))
    hcard hb))

end CFSG.StandardType

end

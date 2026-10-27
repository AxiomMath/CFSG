module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupMemberRoots
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupRoots
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpCount
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpSignedA
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJTagBranch
import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedTits
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsPairs
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsWeyl
import TauCeti.GroupTheory.Coxeter.Geometric

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Spin

private theorem jtag_dot_of_comm {k : ℕ} (hk : 2 ≤ k) {t t' : ggWeylD k} {γ γ' : Fin k → ℤ}
    (h : GGDReflRoot k t γ) (h' : GGDReflRoot k t' γ') (hc : t * t' = t' * t) :
    ggDDot γ γ' = 0 ∨ γ' = γ ∨ γ' = -γ := by
  obtain ⟨w, i, -, hw⟩ := id h
  have key := congrArg (fun g => toStdD k (weylAction (isFiniteType_cartanD k) g
    (weylAction (isFiniteType_cartanD k) w (Pi.single i 1)))) hc
  simp only [weylAction_mul_apply, h.action hk, h'.action hk, hw] at key
  exact ggDReflect_comm_dot (ggDDot_self_of_mem (h.mem (by omega)))
    (ggDDot_self_of_mem (h'.mem (by omega))) key

private theorem jtag_roots
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {k : ℕ} (hk : 2 ≤ k) {σ : Fin k ≃ ι}
    (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G} (hTB : GGTableBPos p Bs L t n f ψ) :
    ∃ η : Fin (ggU t n f).D.rank → Fin k → ℤ, (∀ i, η i ∈ ggDMemberRoots e φ L) ∧
      (∀ i j, i ≠ j → η j ≠ η i ∧ η j ≠ -η i) ∧
      (∀ i j, i ≠ j → (coxeterMatrix (ggU t n f).D.isFiniteType).M i j = 2 →
        ggDDot (η i) (η j) = 0) ∧
      ∀ i j, (coxeterMatrix (ggU t n f).D.isFiniteType).M i j = 3 → ggDDot (η i) (η j) ≠ 0 := by
  obtain ⟨ε', hεr, -, -⟩ := hTB
  let M' : CoxeterMatrix (Fin (ggU t n f).D.rank) := coxeterMatrix (ggU t n f).D.isFiniteType
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
  have hsi : Function.Injective M'.simple := by
    rw [← CoxeterMatrix.toCoxeterSystem_simple]
    exact CoxeterSystem.simple_injective _
  have hne : ∀ a b, a ≠ b → η b ≠ η a ∧ η b ≠ -η a := fun a b hab => by
    have h : φ (j (M'.simple a)) ≠ φ (j (M'.simple b)) := fun h =>
      hab (hsi (hjinj (φ.injective h)))
    exact ⟨fun h' => h ((hη a).unique hk (hη b) (Or.inl h')),
      fun h' => h ((hη a).unique hk (hη b) (Or.inr h'))⟩
  refine ⟨η, fun a => ⟨_, hη a, by rw [hj]; exact (ε' _).2⟩, hne, fun a b hab h2 => ?_,
    fun a b hab h0 => ?_⟩
  ·
    have hc := congrArg (fun w => φ (j w)) (ggSimplyLaced_simple_comm h2)
    simp only [map_mul] at hc
    rcases jtag_dot_of_comm hk (hη a) (hη b) hc with h | h | h
    · exact h
    · exact absurd h (hne a b hab).1
    · exact absurd h (hne a b hab).2
  ·
    have hc := (hη a).commute_of_dot_eq_zero hk (hη b) h0
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

theorem ggDk_tablePos_tag
    (hKG : GGSecFiveKGPosInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι}
    (hM : M = (ggCoxeterMatrixD k).reindex σ) (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    (hss : GGDNoSameSupp e φ) {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hadm : StatedLieAdmissible t n 2 f)
    (htag : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hTB : GGTableBPos p Bs L t n f ψ) :
    t = .PSL ∧ n = k ∧ Nat.card Bs = p ^ k := by
  have hΦ := (ggDk_memberRoots_subsys hKG hcfg hsplit hpres hle3 hk φ hφ).1 L (Or.inl rfl)
  obtain ⟨η, hηL, hne, hdot2, hdot3⟩ := jtag_roots hcfg hpres hle3 (by omega) φ hφ hTB
  have hPSL := ggDk_tag_eq_psl_of_roots hΦ (hss L (Or.inl rfl)) htag hadm η hηL hdot2 hdot3
  obtain ⟨hW', h3'⟩ := ggTag_weylMatrix htag hadm
  obtain ⟨hlow, hup, hkℓ⟩ := ggDk_card_bstar_bounds hcfg hpres hk hM hTB
  obtain ⟨hℓk, -⟩ :=
    ggDk_signedA_of_weyl hΦ (hss L (Or.inl rfl)) hW' h3' η hηL hne hdot2 hdot3 hkℓ
  refine ⟨hPSL, ?_, le_antisymm (by rw [← hℓk]; exact hup) hlow⟩
  subst hPSL
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  exact hℓk

end CFSG.StandardType

end

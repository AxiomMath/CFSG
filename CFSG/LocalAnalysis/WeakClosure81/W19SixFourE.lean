module

public import CFSG.LocalAnalysis.WeakClosure81.W19SixFourK
public import CFSG.LocalAnalysis.WeakClosure81.W19SixFourTie
public import CFSG.LocalAnalysis.WeakClosure81.W19Quad
public import CFSG.LocalAnalysis.WeakClosure81.W19EightOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Conf196

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G} {g : G} {K : Subgroup G}

theorem isElemAbelian_E193 : IsElemAbelian 2 (E193 D V X (conjSubgroup V g) K) :=
  CFSG.Quasithin.B2F.isElemAbelian_omegaOneCenterOf _

theorem J193_le_normalizer_E193 :
    J193 D X (conjSubgroup V g) K ≤ normalizer (E193 D V X (conjSubgroup V g) K : Set G) :=
  inf_le_right.trans <|
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _).trans <|
      (E3.normalizer_le_normalizer_wClos _).trans
        (CFSG.Quasithin.normalizer_le_normalizer_omegaOneCenterOf _)

theorem E193_le_centerOf :
    E193 D V X (conjSubgroup V g) K ≤
      centerOf (E3.wClos V 1 (pCoreOf 2 (K0193 D X (conjSubgroup V g) K))) :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem mem_E193 {z : G}
    (hz : z ∈ centerOf (E3.wClos V 1 (pCoreOf 2 (K0193 D X (conjSubgroup V g) K))))
    (hz2 : z ^ 2 = 1) : z ∈ E193 D V X (conjSubgroup V g) K :=
  Subgroup.subset_closure ⟨hz, hz2⟩

theorem inf_pCoreOf_le_wClos (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    conjSubgroup V g ⊓ pCoreOf 2 K ≤
      E3.wClos V 1 (pCoreOf 2 (K0193 D X (conjSubgroup V g) K)) := by
  have hVg := hc.isElemAbelian_A c
  have hSyl : IsSylowIn 2 (D.T ⊓ K) K := hc.isE.2.2.1
  have hAS : conjSubgroup V g ≤ D.T ⊓ K := le_inf hc.le_T (hc.A_le_K c)
  have hm : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ pCoreOf 2 K) ≤ 1 := by
    have h := E3.e3_17_mQuot (V := conjSubgroup V g) (H := K) (S := D.T ⊓ K) hVg hSyl
      (i := 0) (j := 1) hAS le_rfl (by rw [E3.mQuot_self]) (hc.isE_self c)
    simpa using h
  have hrk : 1 < rk ↥(conjSubgroup V g) := by
    rw [E3.rk_conjSubgroup]
    have := c.three_le_rk
    omega
  have h1 := E3.le_wClos_of_mQuot_le_self hVg (hc.inf_pCoreOf_le_pCoreOf_K0193 c)
    inf_le_left hm hrk
  rwa [E3.wClos_conjV] at h1

theorem inf_pCoreOf_le_centralizer_E193 (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    conjSubgroup V g ⊓ pCoreOf 2 K ≤
      centralizer (E193 D V X (conjSubgroup V g) K : Set G) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have heW := (E193_le_centerOf (D := D) (V := V) (X := X) (g := g) (K := K)) he
  exact (Subgroup.mem_centralizer_iff.1 heW.2 b (hc.inf_pCoreOf_le_wClos c hb)).symm

theorem comm_cClos_le_E193 (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K)
    (h162 : W3Thm162Gt2 G) :
    ⁅conjSubgroup V g, E3.cClos V 1 (pCoreOf 2 K)⁆ ≤ E193 D V X (conjSubgroup V g) K := by
  obtain ⟨-, -, hle⟩ := hc.cClos_comm c h162
  have hVg := hc.isElemAbelian_A c
  have hV₀A : conjSubgroup V₀ g ≤ conjSubgroup V g := E3.conjSubgroup_mono_left g c.V₀_le_V
  have hKC : K ≤ normalizer (E3.cClos V 1 (pCoreOf 2 K) : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K).trans
      (E3.normalizer_le_normalizer_cClos _)
  refine Subgroup.commutator_le.2 fun a ha z hz => ?_
  have hzmem : ⁅a, z⁆ ∈ ⁅conjSubgroup V g, E3.cClos V 1 (pCoreOf 2 K)⁆ :=
    Subgroup.commutator_mem_commutator ha hz
  have hA : ⁅a, z⁆ ∈ conjSubgroup V g := hV₀A (hle hzmem)
  have hC : ⁅a, z⁆ ∈ E3.cClos V 1 (pCoreOf 2 K) := by
    have h1 : a * z * a⁻¹ ∈ E3.cClos V 1 (pCoreOf 2 K) :=
      (Subgroup.mem_normalizer_iff.1 (hKC (hc.A_le_K c ha)) z).1 hz
    have e : ⁅a, z⁆ = (a * z * a⁻¹) * z⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hz)
  have hQ : ⁅a, z⁆ ∈ pCoreOf 2 K := hC.1
  have hW : ⁅a, z⁆ ∈ E3.wClos V 1 (pCoreOf 2 (K0193 D X (conjSubgroup V g) K)) :=
    hc.inf_pCoreOf_le_wClos c ⟨hA, hQ⟩
  have hcent : ⁅a, z⁆ ∈ centralizer
      ((E3.wClos V 1 (pCoreOf 2 (K0193 D X (conjSubgroup V g) K)) : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (E3.wClos_mono (hc.pCoreOf_K0193_le c)) hC.2
  refine mem_E193 ⟨hW, hcent⟩ ?_
  exact hVg.2 _ hA

theorem inf_E193_ne_bot (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K)
    (h162 : W3Thm162Gt2 G) :
    E193 D V X (conjSubgroup V g) K ⊓ conjSubgroup V₀ g ≠ ⊥ := by
  obtain ⟨-, hne, hle⟩ := hc.cClos_comm c h162
  intro hbot
  apply hne
  rw [eq_bot_iff]
  intro x hx
  have hmem : x ∈ E193 D V X (conjSubgroup V g) K ⊓ conjSubgroup V₀ g :=
    ⟨hc.comm_cClos_le_E193 c h162 hx, hle hx⟩
  rwa [hbot] at hmem

theorem isPGroup_inf_centralizer_E193 (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K)
    (h162 : W3Thm162Gt2 G) :
    IsPGroup 2 ↥(J193 D X (conjSubgroup V g) K ⊓
      centralizer (E193 D V X (conjSubgroup V g) K : Set G)) := by
  obtain ⟨w, hw⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (hc.inf_E193_ne_bot c h162)
  have hwE : (w : G) ∈ E193 D V X (conjSubgroup V g) K := (Subgroup.mem_inf.1 w.2).1
  have hwV : (w : G) ∈ conjSubgroup V₀ g := (Subgroup.mem_inf.1 w.2).2
  have hw1 : (w : G) ≠ 1 := fun h => hw (Subtype.ext h)
  have hVM := (hc.V_le_conj_M c h162).1
  refine (Hyp193.isPGroup_two_inf_centralizer c.hyp c.setting c.ne_bot (hc.g_not_mem_M c)
    (c.V₀_le_V.trans hVM) hwV hw1).to_le ?_
  intro x hx
  refine Subgroup.mem_inf.2 ⟨hx.1.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact Subgroup.mem_centralizer_iff.1 hx.2 _ hwE

theorem relIndex_centralizer_E193 (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K)
    (h162 : W3Thm162Gt2 G) :
    (centralizer (E193 D V X (conjSubgroup V g) K : Set G)).relIndex (conjSubgroup V g) = 2 := by
  have h1 : conjSubgroup V g ⊓ pCoreOf 2 K ≤
      conjSubgroup V g ⊓ centralizer (E193 D V X (conjSubgroup V g) K : Set G) :=
    le_inf inf_le_left (hc.inf_pCoreOf_le_centralizer_E193 c)
  have hdvd := Subgroup.relIndex_dvd_of_le_left (conjSubgroup V g) h1
  rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left, hc.relIndex_A c] at hdvd
  have hne1 : (centralizer (E193 D V X (conjSubgroup V g) K : Set G)).relIndex
      (conjSubgroup V g) ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    apply hc.not_A_le_pCoreOf_J193 c
    intro x hx
    exact inf_centralizer_le_pCoreOf J193_le_normalizer_E193
      (hc.isPGroup_inf_centralizer_E193 c h162) ⟨hc.A_le_J193 c hx, h hx⟩
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact absurd h hne1
  · exact h

theorem comm_E193_le_V₀ (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K)
    (h162 : W3Thm162Gt2 G) :
    ⁅conjSubgroup V g, E193 D V X (conjSubgroup V g) K⁆ ≤ conjSubgroup V₀ g := by
  set A := conjSubgroup V g with hA
  set E := E193 D V X A K with hE
  have hEel : IsElemAbelian 2 E := isElemAbelian_E193
  have hAE : A ≤ normalizer (E : Set G) := (hc.A_le_J193 c).trans J193_le_normalizer_E193
  have hB : A ⊓ centralizer (E : Set G) ∈ E3.gammaSet V 1 A := by
    refine (c.mem_gammaSet_one_iff).2 ⟨inf_le_left, ?_⟩
    unfold E3.mQuot
    rw [Subgroup.inf_relIndex_left, hc.relIndex_centralizer_E193 c h162]
    exact padicValNat.self (by norm_num)
  have hcentB : ∀ e ∈ E, ∀ b ∈ A ⊓ centralizer (E : Set G), ⁅e, b⁆ ∈ (⊥ : Subgroup G) := by
    intro e he b hb
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hb.2 e he)
  have heB : eB E ⊥ (A ⊓ centralizer (E : Set G)) = E := eB_eq_of_forall hcentB
  have hcomm : Nat.card ↥(commEB E ⊥ (A ⊓ centralizer (E : Set G))) ≤ 2 := by
    have hbot : commEB E ⊥ (A ⊓ centralizer (E : Set G)) = ⊥ := by
      unfold commEB
      rw [heB, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (Subgroup.mem_centralizer_iff.1 hb.2 e he).symm
    rw [hbot, Subgroup.card_bot]
    norm_num
  have h := c.comm_le_V₀_of_card_le_two h162 hEel hAE hB hcomm
  rwa [heB] at h

theorem isPGroup_J193_inf_normalizer (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K)
    (h162 : W3Thm162Gt2 G) :
    IsPGroup 2 ↥(J193 D X (conjSubgroup V g) K ⊓ normalizer (conjSubgroup V g : Set G)) := by
  have hVM := (hc.V_le_conj_M c h162).1
  refine (Hyp193.isPGroup_two_inf_conj_M c.hyp (c.setting.normalizer₀ c.ne_bot).ge
    (hc.g_not_mem_M c) (c.V₀_le_V.trans hVM)).to_le ?_
  intro x hx
  refine Subgroup.mem_inf.2 ⟨hx.1.1, ?_⟩
  rw [c.conjSubgroup_M_eq g]
  exact hx.2

theorem ti_J193 (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) (h162 : W3Thm162Gt2 G)
    {j : G} (hj : j ∈ J193 D X (conjSubgroup V g) K)
    (hmeet : ⁅E193 D V X (conjSubgroup V g) K, conjSubgroup V g⁆ ⊓
      ⁅E193 D V X (conjSubgroup V g) K, conjSubgroup (conjSubgroup V g) j⁻¹⁆ ≠ ⊥) :
    j ∈ normalizer (conjSubgroup V g : Set G) := by
  set A := conjSubgroup V g with hA
  set E := E193 D V X A K with hE
  have hjE : j⁻¹ ∈ normalizer (E : Set G) :=
    J193_le_normalizer_E193 ((J193 D X A K).inv_mem hj)
  have hcomm : ⁅E, A⁆ ≤ conjSubgroup V₀ g := by
    rw [Subgroup.commutator_comm]
    exact hc.comm_E193_le_V₀ c h162
  have h2 : ⁅E, conjSubgroup A j⁻¹⁆ ≤ conjSubgroup (conjSubgroup V₀ g) j⁻¹ := by
    rw [commutator_conjSubgroup hjE A]
    exact E3.conjSubgroup_mono_left _ hcomm
  have hmeet' : conjSubgroup V₀ g ⊓ conjSubgroup (conjSubgroup V₀ g) j⁻¹ ≠ ⊥ := fun h =>
    hmeet (le_bot_iff.1 ((inf_le_inf hcomm h2).trans h.le))
  rcases inf_conj_eq_bot_or_eq_conj (c.setting.ti₀ c.ne_bot).1 g j⁻¹ with hbot | heq
  · exact absurd hbot hmeet'
  · have hjn : j⁻¹ ∈ normalizer (conjSubgroup V₀ g : Set G) :=
      conjSubgroup_eq_iff_mem_normalizer.1 heq
    rw [← E3.conjSubgroup_normalizer, c.setting.normalizer₀ c.ne_bot,
      c.conjSubgroup_M_eq g] at hjn
    simpa using Subgroup.inv_mem _ hjn

theorem tieData (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) (h162 : W3Thm162Gt2 G) :
    TieData (J193 D X (conjSubgroup V g) K) (E193 D V X (conjSubgroup V g) K)
      (conjSubgroup V g) where
  elemAb := isElemAbelian_E193
  le_normalizer := J193_le_normalizer_E193
  isPGroup_cent := hc.isPGroup_inf_centralizer_E193 c h162
  A_le := hc.A_le_J193 c
  relIndex := hc.relIndex_centralizer_E193 c h162
  inf_pCore := fun x hx =>
    hc.inf_pCoreOf_le_centralizer_E193 c (hc.inf_pCoreOf_J193_le c hx)
  isPGroup_norm := hc.isPGroup_J193_inf_normalizer c h162
  ti := fun _ hj hmeet => hc.ti_J193 c h162 hj hmeet

end Conf196

end CFSG.LocalAnalysis.WeakClosure81

end

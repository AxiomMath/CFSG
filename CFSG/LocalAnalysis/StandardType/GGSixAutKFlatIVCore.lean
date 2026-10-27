module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVStruct
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVPComp
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVQuot
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Cores

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem ggCore_centralizer_closure_pair (b e : G) :
    Subgroup.centralizer ↑(Subgroup.closure ({b, e} : Set G)) =
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({e} : Set G) := by
  rw [ggCentralizer_closure_pair_set b e]
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact h b (by simp)
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact h e (by simp)
  · rintro ⟨h1, h2⟩ y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy]; exact h1 b (by simp)
    · rw [hy]; exact h2 e (by simp)

theorem ggItem2_core (hS1 : GGStructSOne) (hp : p.Prime) (hp2 : p ≠ 2) {G₀ K : Subgroup G}
    {b e : G} (hsimple : IsSimpleGroup ↥G₀)
    (hA : IsElemAbelian p (Subgroup.closure ({b, e} : Set G)))
    (hAN : Subgroup.closure ({b, e} : Set G) ≤ Subgroup.normalizer (G₀ : Set G))
    (hmark : LargeEvenMarking ↥G₀ fun _ _ _ I _ θ => ∀ a ∈ Subgroup.closure ({b, e} : Set G),
      ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ)
    (hperf : ∀ P : Subgroup G, P ≤ Subgroup.centralizer {e} → ⁅P, P⁆ = P → P ≤ G₀)
    (hK : IsSubnormal K (Subgroup.centralizer {b})) {C₀ : Subgroup G}
    (hC₀le : C₀ ≤ K ⊓ Subgroup.centralizer {e})
    (hC₀ : CFSG.IsPComponent p (C₀.subgroupOf (K ⊓ Subgroup.centralizer {e}))) :
    CFSG.Assembly.IsQuasisimple ↥C₀ ∧
      LargeEvenMarking ↥C₀ (fun _ _ _ _ _ _ => True) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hperfC : ⁅C₀, C₀⁆ = C₀ := ggPComponent_commutator_eq p hC₀le hC₀
  have hC₀G₀ : C₀ ≤ G₀ := hperf C₀ (hC₀le.trans inf_le_right) hperfC
  have hC₀W : C₀ ≤ Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G) :=
    le_inf (hC₀le.trans (le_trans inf_le_left hK.le)) (hC₀le.trans inf_le_right)
  have hsub : IsSubnormal (K ⊓ Subgroup.centralizer ({e} : Set G))
      (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({e} : Set G)) :=
    hK.inf (Subgroup.centralizer ({e} : Set G))
  have h1 : CFSG.IsPComponent p
      (C₀.subgroupOf (Subgroup.centralizer ({b} : Set G) ⊓
        Subgroup.centralizer ({e} : Set G))) :=
    ggPComponent_subgroupOf_of_subnormal p hC₀le hsub hC₀
  have hC₀cl : C₀ ≤ Subgroup.centralizer ↑(Subgroup.closure ({b, e} : Set G)) := by
    rw [ggCore_centralizer_closure_pair b e]
    exact hC₀W
  have h2 : CFSG.IsPComponent p
      (C₀.subgroupOf (Subgroup.centralizer ↑(Subgroup.closure ({b, e} : Set G)) ⊓ G₀)) := by
    rw [ggCore_centralizer_closure_pair b e]
    exact ggPComponent_subgroupOf_of_le p (le_inf hC₀W hC₀G₀) inf_le_left h1
  have hLE : LargeEvenPComponent p
      (Subgroup.centralizer ↑(Subgroup.closure ({b, e} : Set G)) ⊓ G₀) C₀ :=
    (ggLargeEvenPComponent_iff p _ _).2 ⟨le_inf hC₀cl hC₀G₀, h2⟩
  exact hS1 G p G₀ (Subgroup.closure ({b, e} : Set G)) hp hp2 hsimple hA hAN hmark C₀ hLE

end Cores

section ItemFive

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem ggItem5_core (hS1' : GGStructSOnePrimeRoot) (hp : p.Prime) (hp2 : p ≠ 2)
    {G₀ : Subgroup G} {r e : G} (hsimple : IsSimpleGroup ↥G₀)
    (heN : e ∈ Subgroup.normalizer (G₀ : Set G))
    (hmark : LargeEvenMarking ↥G₀ fun _ _ _ I _ θ =>
      ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = e⁻¹ * l * e) φ)
    (hr : r ∈ G₀) (hr2 : orderOf r = 2) (hep : orderOf e = p) (hcomm : Commute r e)
    (hroot : GGIsRootInvolution G₀ r)
    (hperf : ∀ P : Subgroup G, P ≤ Subgroup.centralizer {r, e} → ⁅P, P⁆ = P → P ≤ G₀)
    {S₀ : Subgroup G} (hS₀ : S₀ ≤ Subgroup.centralizer {r, e})
    (hS₀pc : CFSG.IsPComponent p (S₀.subgroupOf (Subgroup.centralizer {r, e})))
    {D : Type*} [Group D] (hD : CFSG.Assembly.IsQuasisimple D)
    (Θ : ↥S₀ →* D) (hΘ : Function.Surjective Θ) :
    LargeEvenMarking D (fun _ _ _ _ _ _ => True) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hS₀perf : ⁅S₀, S₀⁆ = S₀ := ggPComponent_commutator_eq p hS₀ hS₀pc
  have hS₀G₀ : S₀ ≤ G₀ := hperf S₀ hS₀ hS₀perf
  let Y : Subgroup G := Subgroup.centralizer ({r, e} : Set G) ⊓ G₀
  have hS₀Y : S₀ ≤ Y := le_inf hS₀ hS₀G₀
  have hpcY : CFSG.IsPComponent p (S₀.subgroupOf Y) :=
    ggPComponent_subgroupOf_of_le p hS₀Y inf_le_left hS₀pc
  have hsub : IsSubnormal S₀ Y := ((ggPComponent_iff_data p hS₀Y).1 hpcY).1
  have hperfS : commutator ↥S₀ = ⊤ := ggCommutator_eq_top_of_perfect hS₀perf
  let κ : ↥S₀ →* D ⧸ Subgroup.center D :=
    (QuotientGroup.mk' (Subgroup.center D)).comp Θ
  have hκ : Function.Surjective κ :=
    (QuotientGroup.mk'_surjective (Subgroup.center D)).comp hΘ
  obtain ⟨hDs, hDnc⟩ := ggQuasisimple_centerQuot hD
  haveI : IsSimpleGroup (D ⧸ Subgroup.center D) := hDs
  let ε : ↥S₀ ⧸ κ.ker ≃* D ⧸ Subgroup.center D :=
    QuotientGroup.quotientKerEquivOfSurjective κ hκ
  have hsimpleQ : IsSimpleGroup (↥S₀ ⧸ κ.ker) := ε.isSimpleGroup
  have hncQ : ∃ a b : ↥S₀ ⧸ κ.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hDnc
    exact ⟨ε.symm a, ε.symm b, fun h => hab (by simpa using congrArg ε h)⟩
  haveI : Finite (D ⧸ Subgroup.center D) := Finite.of_surjective κ hκ
  have hY : (Subgroup.map Y.subtype (CFSG.pCore 2 ↥Y)).subgroupOf Y = CFSG.pCore 2 ↥Y :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective (CFSG.pCore 2 ↥Y)
  have hTeq : ((CFSG.pCore 2 ↥Y).map Y.subtype).subgroupOf S₀ =
      (CFSG.pCore 2 ↥Y).comap (Subgroup.inclusion hS₀Y) := by
    rw [← Subgroup.comap_inclusion_subgroupOf hS₀Y ((CFSG.pCore 2 ↥Y).map Y.subtype), hY]
  have hTnormal : (((CFSG.pCore 2 ↥Y).map Y.subtype).subgroupOf S₀).Normal := by
    rw [hTeq]
    infer_instance
  have hTp : IsPGroup 2 (((CFSG.pCore 2 ↥Y).map Y.subtype).subgroupOf S₀) := by
    rw [hTeq]
    exact IsPGroup.comap_of_injective (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
      (Subgroup.inclusion hS₀Y) (Subgroup.inclusion_injective hS₀Y)
  have hT : ((CFSG.pCore 2 ↥Y).map Y.subtype).subgroupOf S₀ ≤ κ.ker := by
    haveI := hTnormal
    exact ggNormalPGroup_le_ker κ hκ hDs hDnc _ hTp
  have hmarkQ : LargeEvenMarking (↥S₀ ⧸ κ.ker) (fun _ _ _ _ _ _ => True) :=
    hS1' G p G₀ r e hp hp2 hsimple heN hmark hr hr2 hep hcomm hroot S₀ hS₀Y hsub hperfS
      κ.ker hT hsimpleQ hncQ
  exact ggLargeEvenMarking_of_simple_quotient hD κ hκ hmarkQ

end ItemFive

end CFSG.StandardType

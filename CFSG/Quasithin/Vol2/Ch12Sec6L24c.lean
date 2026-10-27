module

public import CFSG.Quasithin.Vol2.Ch12Sec6L24b
public import CFSG.Quasithin.Vol2.Ch12Sec6L20d
public import CFSG.Quasithin.Vol2.Ch12Sec6Amalgam
public import CFSG.Quasithin.H13.A6F91General
public import CFSG.Quasithin.Background.BlueprintB2Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126FE S126L19 S126L19a S126L20a Equiv
open CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise

namespace S126L24

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem tf_fix_four : ∀ u : Fin 4, tf u 0 4 = 4 := by
  decide

theorem weak_e (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    {H : Subgroup G} (hHz : InHz T L F.V1 H) :
    ∀ g ∈ H, ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V → ⁅F.V5, conjSub g⁻¹ V⁆ ≤ F.V1 →
      ⁅conjSub g⁻¹ F.V5, V⁆ ≤ F.V1 → ⁅F.V5, conjSub g⁻¹ V⁆ = ⊥ ∧ ⁅conjSub g⁻¹ F.V5, V⁆ = ⊥ := by
  intro g hg hVV h5 _
  have hV5V : F.V5 ≤ V := preV_le F W5
  by_cases hc : ⁅V, conjSub g⁻¹ V⁆ = ⊥
  · refine ⟨eq_bot_iff.2 ?_, eq_bot_iff.2 ?_⟩
    · rw [← hc]
      exact Subgroup.commutator_mono hV5V le_rfl
    · rw [← hc, Subgroup.commutator_comm]
      exact Subgroup.commutator_mono le_rfl (Subgroup.map_mono hV5V)
  exfalso
  have hA : conjSub g⁻¹ V = conjSubgroup V g := rfl
  have hnotN : g ∉ Subgroup.normalizer (V : Set G) := by
    intro hgN
    apply hc
    rw [hA, conjSubgroup_eq_iff_mem_normalizer.2 hgN, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact S126L1b.comm_of_mem hw hv
  have hg4 : S126L20c.Hyp4 V g := ⟨hnotN, hc, hVV⟩
  have hcard := (S126L20d.card_permGrp h331 h1222 h1262 F hH hfus hg4).1
  obtain ⟨hVT, -, -, -⟩ := S126L20.facts h1222 hH
  have hTH : T ≤ H := le_sup_right.trans hHz.1.1
  have hBE : S126L20d.permGrp h331 h1222 F hH hg4 ≤ E16 := by
    intro σ hσ
    obtain ⟨y, hy, hyσ⟩ := (S126L20d.mem_permGrp h331 h1222 F hH hg4).1 hσ
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := hg4.le_normalizer hy
    have hyH : y ∈ H := by
      obtain ⟨v, hv, rfl⟩ := hy
      exact H.mul_mem (H.mul_mem (H.inv_mem hg) (hTH (hVT hv))) (H.inv_mem (H.inv_mem hg))
    have hy1 : y ∈ Subgroup.normalizer (F.V1 : Set G) :=
      Subgroup.centralizer_le_normalizer _ (hHz.2.2 hyH)
    have hyC : y ∈ centralizerMod F.V1 ⊤ F.V5 := by
      refine ⟨Subgroup.mem_top _, hy1, fun u hu => ?_⟩
      have h1 := F.V1.inv_mem (h5 (Subgroup.commutator_mem_commutator hu (hA ▸ hy)))
      rwa [commutatorElement_def, show (u * y * u⁻¹ * y⁻¹)⁻¹ = y * u * y⁻¹ * u⁻¹ by group]
        at h1
    exact mem_E16_of_cent (cent_of_mem_centralizerMod hyN hyσ hyC)
  obtain ⟨u, hu, huB⟩ := exists_K1 _ hBE (by rw [hcard]; norm_num)
  have hu1 : tau u 0 ≠ 1 := fun h => hu (tau_eq_one_iff.1 h).1
  exact S126L20d.permGrp_fpf h331 h1222 h1262 F hH hfus hg4 _ huB hu1 4
    (by rw [tau_apply, tf_fix_four])

theorem hypF91 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight)
    (h1262 : Theorem12_6_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : InHz T L F.V1 H) : HypF91 T V L F.V1 F.V5 H := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, hfsu⟩, -, -, -⟩ := hall V hyp.irrPlus
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hred' : IsTwoReducedIn (L ⊔ T) V :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVT.trans le_sup_right, hred⟩
  have hQ : pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (V : Set G) := by
    obtain ⟨-, -, hO⟩ := h3228 G T L V hfsu
    have hVc : conjClosure V T = V := le_antisymm
      (conjClosure_le fun _ ht v hv => (Subgroup.mem_normalizer_iff.1 (hTV ht) v).1 hv)
      (le_conjClosure V T)
    rwa [hyp.conjClosure_eq, hVc] at hO
  have huniq : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G)) := by
    obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
    obtain ⟨⟨hmax, -, huniq⟩, -, -, -, -⟩ := h331B L hyp.maximal hyp.quasisimple
    rw [hyp.conjClosure_eq] at hmax huniq
    exact ⟨⟨hmax, sup_le Subgroup.le_normalizer hyp.normalizes⟩,
      fun M' hM' => huniq M' hM'.1 hM'.2⟩
  have hcard : Nat.card F.V1 = 2 := (S126L23d.part2 h1222 F hH hZ).2
  have hinj := beta_injective F hZ
  have hV15 : F.V1 < F.V5 := by
    refine lt_of_le_of_ne (Subgroup.map_mono (Subgroup.comap_mono W1_le_W5)) fun h => ?_
    have h1 := card_V5 (F := F) hinj
    rw [← h, hcard] at h1
    omega
  obtain ⟨-, -, -, hXV5⟩ := sup_le_normalizers h1222 F hH
  have h6 := part6 h331 h1222 h1262 F hH hfus hZ
  have h4 := part4 h331 h1222 h1262 F hH hfus hZ
  have hTH : T ≤ H := le_sup_right.trans hHz.1.1
  have hHchar : CharTwo H := by
    obtain ⟨P, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
    exact CFSG.Quasithin.charTwo_of_inH hyp.qtke.2.1 P ⟨hTH, hHz.1.2⟩
  have hO2L : pCoreOf 2 L ≤ T :=
    (A6.pCoreOf_le_pCoreOf_sup hyp.normalizes).trans (A6.pCoreOf_le_of_sylow hyp.sylow le_sup_right)
  have hCLV : L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (A1a.le_normalizer_inf Subgroup.le_normalizer
        (hLV.trans (F7.normalizer_le_normalizer_centralizer V))) ?_
    rintro ⟨y, hyL, hyC⟩
    obtain ⟨k, hk⟩ := S126L19a.isPGroup_ker h1222 hH ⟨⟨y, hyL⟩, hyC⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 := congrArg
      (fun z : ↥((Subgroup.centralizer (V : Set G)).subgroupOf L) => ((z : ↥L) : G)) hk
    simpa using h1
  have hCL : ∀ y ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G),
      ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
    rintro y ⟨hyL, hyC⟩ l hl
    refine hCLV ⟨?_, ?_⟩
    · rw [show l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) by group]
      exact L.mul_mem hl ((Subgroup.mem_normalizer_iff.1 hyL _).1 (L.inv_mem hl))
    · refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ hyC)
      exact (Subgroup.mem_normalizer_iff.1
        (F7.normalizer_le_normalizer_centralizer V (hLV hl)) y).1 hyC
  have hCVL : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    rw [h6.2.2.2]
    exact inf_le_left
  have hVe : IsElemAbelian 2 V := hred'.2.2.1
  have hker := A6.coreIn_le_pCoreOf_of huniq hTH hHz.2.1 hHchar hHz.2.2
    (F7.isElemAbelian_mono hVe (preV_le F W5)) hV15.le hCVL hO2L hCL
    (fun y _ hy _ => h6.2.2.1 ▸ hy)
  exact A6.hypF91_of hyp.sylow hyp.faithful hyp.qtke.2.1 hyp.normalizes hred' hQ.symm huniq
    hcard hV15 (preV_le F W5) (S126L19b.T_le_normalizer_V1 h1222 hH) hHz.1 hHz.2.2 hHz.2.1 hker
    hXV5 (part1 h1222 F hH hZ) (inf_le_right.trans h4)
    (weak_e h331 h1222 h1262 F hH hfus hHz)

end S126L24

end CFSG.Quasithin.H13

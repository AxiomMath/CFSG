module

public import CFSG.Quasithin.Background.RonanE211Pair
public import CFSG.Quasithin.Vol2.E2Eleven
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.Quasithin.RonanE211

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.E2 B6 CFSG.Quasithin.Ch3E213M
  CFSG.QuasithinUnique.Borel252.A6 CFSG.Quasithin.RonanE27
open scoped commutatorElement

theorem oddCoverExact_perm_six :
    OddCoverExact P6 := by
  obtain ⟨σ⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm
    (k := ZMod 2) (ZMod.card 2)
  exact oddCoverExact_of_mulEquiv_statedSp 2 σ.symm

section

variable {G : Type} [Group G] [Finite G] {H T M V I : Subgroup G} {g : G}

theorem e2_11_four_of_center (h : Hyp28 H T M V)
    {N : ℕ∞} (hI : ASInputs.IsInIHTVNoRootAt H T M V I N)
    (hcen0 : Subgroup.center (StarQuot (M ⊓ I) I) = ⊥) (hg : g ∈ I)
    (hgen : I = V ⊔ B6.conjSub g V) (hJ : pCoreOf 2 I = kerIn (M ⊓ I) I) :
    B6.conjSub g V ⊓ pCoreOf 2 I = B6.conjSub g V ⊓ Subgroup.normalizer (V : Set G) := by
  have hp := h.pair_of_member hI hg hgen
  have hsyl := hI.2.2.1
  have hWI : B6.conjSub g V ≤ I := hp.conj_le
  have hVI : V ≤ I := hp.V_le
  apply le_antisymm
  · exact inf_le_inf_left _ ((B6.pCoreOf_two_le_of_isSylowTwoOf hsyl).trans
      (inf_le_left.trans h.normal_T))
  rintro u ⟨huW, huN⟩
  refine ⟨huW, ?_⟩
  have huI : u ∈ I := hWI huW
  have huM : u ∈ M ⊓ I := hp.normalizer_le ⟨huI, huN⟩
  set φ := QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) with hφ
  have := E2P.finite_starQuot (M ⊓ I) I
  have hS := isSylowTwoOf_star_inf (M := M) hsyl
  have hu2 : φ ⟨u, huI⟩ * φ ⟨u, huI⟩ = 1 := by
    rw [← map_mul]
    have : (⟨u, huI⟩ : I) * ⟨u, huI⟩ = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      have huW' : u ∈ B6.conjSub g V := huW
      rw [B6.mem_conjSub] at huW'
      have hv2 := h.elem.2 _ huW'
      rw [pow_two] at hv2
      have e1 : u * u = g * ((g⁻¹ * u * g) * (g⁻¹ * u * g)) * g⁻¹ := by group
      rw [e1, hv2]
      group)
    rw [this, map_one]
  have huT : φ ⟨u, huI⟩ ∈ star (M ⊓ I) I (T ⊓ I) := by
    have hzM := mem_star (M := M) huI huM
    have hTM : star (M ⊓ I) I (T ⊓ I) ≤ star (M ⊓ I) I (M ⊓ I) :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono I (inf_le_inf_right I h.minParabolic.le))
    have hu2' : (φ ⟨u, huI⟩) ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two]
      exact hu2
    have hle : Subgroup.zpowers (φ ⟨u, huI⟩) ≤ star (M ⊓ I) I (T ⊓ I) :=
      le_of_normal_sylow' (B6.isSylowTwoOf_mono hS hTM le_top) (le_normalizer_star h hI)
        (Subgroup.zpowers_le.2 hzM) (isPGroup_zpowers_of_pow hu2')
    exact hle (Subgroup.mem_zpowers _)
  have h2 := E2.e2_11_two h hI hVI
  have hcV : star (M ⊓ I) I V ≤
      Subgroup.centralizer ({φ ⟨u, huI⟩} : Set (StarQuot (M ⊓ I) I)) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (Subgroup.mem_centralizer_iff.1 (h2 hv) _ huT)
  have hcW : star (M ⊓ I) I (B6.conjSub g V) ≤
      Subgroup.centralizer ({φ ⟨u, huI⟩} : Set (StarQuot (M ⊓ I) I)) := by
    rintro _ ⟨⟨w, hwI⟩, hw, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hp.comm_conj huW (Subgroup.mem_subgroupOf.1 hw))
  have htop : star (M ⊓ I) I V ⊔ star (M ⊓ I) I (B6.conjSub g V) = ⊤ := by
    rw [← E2P.star_top (M ⊓ I) I]
    simp only [E2.star]
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hVI hWI, ← hgen]
  have hcen : φ ⟨u, huI⟩ ∈ Subgroup.center (StarQuot (M ⊓ I) I) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz : z ∈ Subgroup.centralizer ({φ ⟨u, huI⟩} : Set (StarQuot (M ⊓ I) I)) :=
      (htop ▸ sup_le hcV hcW) (Subgroup.mem_top z)
    exact (Subgroup.mem_centralizer_iff.1 hz _ rfl).symm
  rw [hcen0, Subgroup.mem_bot, hφ, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hcen
  rw [hJ]
  exact hcen


theorem twoPrimeResidual_eq_of_normal_sylow {Y T : Subgroup G} (hT : IsSylowTwoOf T Y)
    (hn : Y ≤ Subgroup.normalizer (T : Set G)) : T = twoPrimeResidual Y := by
  obtain ⟨hTY, hT2, hTodd⟩ := hT
  apply le_antisymm
  · exact le_iInf fun N => le_iInf fun hN =>
      B6.le_of_isPGroup_of_odd_relIndex hTY hT2 hN.1 hN.2.1 hN.2.2
  · exact iInf₂_le T ⟨hTY, hn, hTodd⟩

omit [Finite G] in
theorem isTwoClosed_of_closed {J : Subgroup G} (h : IsSylowTwoOf (pCoreOf 2 J) J) :
    E1.IsTwoClosed J := by
  refine ⟨pCoreOf 2 J, h, ?_⟩
  have : (pCoreOf 2 J).subgroupOf J = CFSG.pCore 2 ↥J :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  rw [this]
  infer_instance

theorem e2_11C_all
    (hKG1 : KGSz8CoverInvolutions) (hKG3 : KGI22One)
    (h : Hyp28 H T M V) {N : ℕ∞} (hI : ASInputs.IsInIHTVNoRootAt H T M V I N) (hg : g ∈ I)
    (hgen : I = V ⊔ B6.conjSub g V) :
    E2.Pair I (T ⊓ I) (M ⊓ I) V g ∧
      E2.star (M ⊓ I) I V ≤
        Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)) ∧
      T ⊓ I = pCoreOf 2 (M ⊓ I) ∧
      B6.conjSub g V ⊓ pCoreOf 2 I = B6.conjSub g V ⊓ Subgroup.normalizer (V : Set G) ∧
      pCoreOf 2 I = kerIn (M ⊓ I) I ∧
      (pCoreOf 2 I ⊓ V) ⊔ (pCoreOf 2 I ⊓ B6.conjSub g V) ≤ pCoreOf 2 I ∧
      (∀ x ∈ I, (∀ y ∈ I, x * y * x⁻¹ * y⁻¹ ∈ (pCoreOf 2 I ⊓ V) ⊔ (pCoreOf 2 I ⊓ B6.conjSub g V)) ↔
        x ∈ pCoreOf 2 I) ∧
      ∀ x ∈ pCoreOf 2 I, x ^ 2 ∈ (pCoreOf 2 I ⊓ V) ⊔ (pCoreOf 2 I ⊓ B6.conjSub g V) := by
  by_cases hS6 : Nonempty (StarQuot (M ⊓ I) I ≃* P6)
  swap
  · exact ASInputs.e2_11C_of_not_S6 hKG1 hKG3 h hI ⟨fun e => hS6 ⟨e⟩⟩ hg hgen
  obtain ⟨e⟩ := hS6
  have hp := h.pair_of_member hI hg hgen
  have hVI : V ≤ I := hp.V_le
  have := hp.normal_P
  have := E2P.finite_starQuot (M ⊓ I) I
  have hsyl := hI.2.2.1
  have hcenter : Subgroup.center (StarQuot (M ⊓ I) I) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : e z ∈ Subgroup.center P6 := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨u, rfl⟩ := e.surjective w
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz u]
    have h1 : e z = 1 :=
      CFSG.perm_eq_one_of_forall_commute (by simp) fun y =>
        (Subgroup.mem_center_iff.1 hz' y).symm
    exact e.injective (by rw [h1, map_one])
  obtain ⟨hZ, hsq, hJ⟩ := center_six_of_pair hp hKG3 oddCoverExact_perm_six e
    (E2.isSylowTwoOf_star_inf hsyl) (E2.e2_11_two h hI hVI)
  obtain ⟨hJ, h5b, h5c, h5d⟩ := hp.five_of_center hZ hsq hJ
  exact ⟨hp, E2.e2_11_two h hI hVI, E2.e2_11_three h hI hJ,
    e2_11_four_of_center h hI hcenter hg hgen hJ, hJ, h5b, h5c, h5d⟩

end

end CFSG.Quasithin.RonanE211

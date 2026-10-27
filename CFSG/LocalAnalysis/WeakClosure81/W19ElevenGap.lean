module

public import CFSG.LocalAnalysis.WeakClosure81.W19ElevenEnd
import CFSG.GroupTheory.SwappedFactorsOffenders
import CFSG.Quasithin.MS93.S38OffV

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_eq_singleton_of_relIndex_two {B Y : Subgroup G} {b : G}
    (hbB : b ∈ B) (hbC : b ∉ Subgroup.centralizer (Y : Set G))
    (hrel : (B ⊓ Subgroup.centralizer (Y : Set G)).relIndex B = 2) :
    Y ⊓ Subgroup.centralizer (B : Set G) =
      Y ⊓ Subgroup.centralizer ({b} : Set G) := by
  refine le_antisymm (inf_le_inf_left Y (Subgroup.centralizer_le
    (Set.singleton_subset_iff.2 hbB))) ?_
  rintro y ⟨hyY, hyb⟩
  refine Subgroup.mem_inf.2 ⟨hyY, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro c hcB
  have hyb' : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.1 hyb
  have hbH : b ∉ B ⊓ Subgroup.centralizer (Y : Set G) := fun h => hbC h.2
  rcases CFSG.Quasithin.MS93.OffV.mem_or_mul_inv_mem hrel hbB hbH hcB with hcH | hcb
  · exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hcH).2 y hyY).symm
  · have h1 : y * (c * b⁻¹) = (c * b⁻¹) * y :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hcb).2 y hyY
    calc c * y = ((c * b⁻¹) * b) * y := by group
      _ = (c * b⁻¹) * (b * y) := by group
      _ = (c * b⁻¹) * (y * b) := by rw [hyb'.symm]
      _ = ((c * b⁻¹) * y) * b := by group
      _ = (y * (c * b⁻¹)) * b := by rw [h1]
      _ = y * c := by group

theorem card_le_two_mul_card_inf_centralizer_of_commutator_le {B Y U : Subgroup G}
    (hU : Nat.card ↥U ≤ 2) (hcomm : ⁅B, Y⁆ ≤ U)
    (hB : Nat.card ↥B ≤
      2 * Nat.card ↥(B ⊓ Subgroup.centralizer (Y : Set G))) :
    Nat.card ↥Y ≤ 2 * Nat.card ↥(Y ⊓ Subgroup.centralizer (B : Set G)) := by
  classical
  by_cases hBC : B ≤ Subgroup.centralizer (Y : Set G)
  · have hYB : Y ≤ Subgroup.centralizer (B : Set G) := (Subgroup.le_centralizer_iff).1 hBC
    rw [inf_eq_left.2 hYB]
    omega
  · obtain ⟨b, hbB, hbC⟩ := SetLike.not_le_iff_exists.1 hBC
    have hHle : B ⊓ Subgroup.centralizer (Y : Set G) ≤ B := inf_le_left
    have hcard : Nat.card ↥B =
        (B ⊓ Subgroup.centralizer (Y : Set G)).relIndex B *
          Nat.card ↥(B ⊓ Subgroup.centralizer (Y : Set G)) := by
      have h := Subgroup.relIndex_mul_card
        (H := B ⊓ Subgroup.centralizer (Y : Set G)) (K := B)
      rw [inf_eq_left.2 hHle] at h
      exact h.symm
    have hrel2 : (B ⊓ Subgroup.centralizer (Y : Set G)).relIndex B = 2 := by
      have hle2 : (B ⊓ Subgroup.centralizer (Y : Set G)).relIndex B ≤ 2 := by
        rw [hcard] at hB
        exact Nat.le_of_mul_le_mul_right hB Nat.card_pos
      have hne1 : (B ⊓ Subgroup.centralizer (Y : Set G)).relIndex B ≠ 1 := by
        intro h
        exact hbC (Subgroup.mem_inf.1 ((Subgroup.relIndex_eq_one.1 h) hbB)).2
      have hpos : 0 < (B ⊓ Subgroup.centralizer (Y : Set G)).relIndex B :=
        Nat.pos_of_ne_zero (E3.relIndex_ne_zero' B (B ⊓ Subgroup.centralizer (Y : Set G)))
      omega
    have hidx : (Subgroup.centralizer ({b} : Set G)).relIndex Y ≤ 2 :=
      (relIndex_centralizer_le_card (B := Y) (R := U) (e := b)
        (fun y hy => hcomm (Subgroup.commutator_mem_commutator hbB hy))).trans hU
    have hcardY : Nat.card ↥Y ≤
        2 * Nat.card ↥(Y ⊓ Subgroup.centralizer ({b} : Set G)) := by
      have h := Subgroup.relIndex_mul_card
        (H := Subgroup.centralizer ({b} : Set G)) (K := Y)
      rw [inf_comm] at h
      calc Nat.card ↥Y = (Subgroup.centralizer ({b} : Set G)).relIndex Y *
            Nat.card ↥(Y ⊓ Subgroup.centralizer ({b} : Set G)) := h.symm
        _ ≤ 2 * Nat.card ↥(Y ⊓ Subgroup.centralizer ({b} : Set G)) :=
            Nat.mul_le_mul_right _ hidx
    rw [inf_centralizer_eq_singleton_of_relIndex_two hbB hbC hrel2]
    exact hcardY

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}
variable {g : G} {K : Subgroup G}

theorem conjSubgroup_le_wClos (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    conjSubgroup V g ≤ E3.wClos V 1 D.T := by
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := hc.isElemAbelian_A c
  have hkV : 1 < rk ↥(conjSubgroup V g) := by
    rw [E3.rk_conjSubgroup]
    have := c.three_le_rk
    omega
  have h := E3.le_wClos_of_mQuot_le_self hVg hc.le_T le_rfl
    (by rw [E3.mQuot_self]; exact Nat.zero_le _) hkV
  rwa [E3.wClos_conjV] at h

theorem Z193_le_centralizer_conjSubgroup (c : MinCex193 D V₀ V p X)
    (hc : Conf196 D V X g K) :
    Z193 D V ≤ Subgroup.centralizer (conjSubgroup V g : Set G) :=
  (CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf _).trans
    ((CFSG.Quasithin.A4.centerOf_le_centralizer _).trans
      (Subgroup.centralizer_le (conjSubgroup_le_wClos c hc)))

theorem inf_pCoreOf_le_centralizer_cClos (c : MinCex193 D V₀ V p X)
    (hc : Conf196 D V X g K) :
    conjSubgroup V g ⊓ pCoreOf 2 K ≤
      Subgroup.centralizer (E3.cClos V 1 (pCoreOf 2 K) : Set G) := by
  have hW : conjSubgroup V g ⊓ pCoreOf 2 K ≤ E3.wClos V 1 (pCoreOf 2 K) :=
    (hc.inf_pCoreOf_le_wClos c).trans (E3.wClos_mono (hc.pCoreOf_K0193_le c))
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.1 hz.2 b (hW hb)).symm

theorem conj_inf_pCoreOf_le_centralizer_cClos (c : MinCex193 D V₀ V p X)
    (hc : Conf196 D V X g K) {k : G} (hk : k ∈ K) :
    conjSubgroup (conjSubgroup V g) k ⊓ pCoreOf 2 K ≤
      Subgroup.centralizer (E3.cClos V 1 (pCoreOf 2 K) : Set G) := by
  have hbase := inf_pCoreOf_le_centralizer_cClos c hc
  have hKC : K ≤ Subgroup.normalizer (E3.cClos V 1 (pCoreOf 2 K) : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K).trans
      (E3.normalizer_le_normalizer_cClos _)
  have hkQ : k ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk
  intro x hx
  have hxA : k * x * k⁻¹ ∈ conjSubgroup V g :=
    CFSG.Quasithin.mem_conjSubgroup_iff.1 hx.1
  have hxQ : k * x * k⁻¹ ∈ pCoreOf 2 K := (Subgroup.mem_normalizer_iff.1 hkQ x).1 hx.2
  have ha : k * x * k⁻¹ ∈
      Subgroup.centralizer (E3.cClos V 1 (pCoreOf 2 K) : Set G) := hbase ⟨hxA, hxQ⟩
  have ha' := Subgroup.mem_centralizer_iff.1 ha
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzk : k * z * k⁻¹ ∈ E3.cClos V 1 (pCoreOf 2 K) :=
    (Subgroup.mem_normalizer_iff.1 (hKC hk) z).1 hz
  have hcomm := ha' (k * z * k⁻¹) hzk
  have hxeq : x = k⁻¹ * (k * x * k⁻¹) * k := by group
  calc z * x = k⁻¹ * ((k * z * k⁻¹) * (k * x * k⁻¹)) * k := by rw [hxeq]; group
    _ = k⁻¹ * ((k * x * k⁻¹) * (k * z * k⁻¹)) * k := by rw [hcomm]
    _ = x * z := by rw [hxeq]; group

theorem card_commutator_conj_cClos_le_two (c : MinCex193 D V₀ V p X)
    (h162 : W3Thm162Gt2 G) (hc : Conf196 D V X g K) {k : G} (hk : k ∈ K)
    (h2 : Nat.card ↥V₀ = 2) :
    Nat.card ↥⁅conjSubgroup (conjSubgroup V g) k, E3.cClos V 1 (pCoreOf 2 K)⁆ ≤ 2 := by
  have hKC : K ≤ Subgroup.normalizer (E3.cClos V 1 (pCoreOf 2 K) : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K).trans
      (E3.normalizer_le_normalizer_cClos _)
  have hCk : conjSubgroup (E3.cClos V 1 (pCoreOf 2 K)) k =
      E3.cClos V 1 (pCoreOf 2 K) :=
    CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.2 (hKC hk)
  have hUC : ⁅conjSubgroup (conjSubgroup V g) k, E3.cClos V 1 (pCoreOf 2 K)⁆ ≤
      conjSubgroup (conjSubgroup V₀ g) k := by
    have hcommBC : ⁅conjSubgroup (conjSubgroup V g) k, E3.cClos V 1 (pCoreOf 2 K)⁆ =
        ⁅conjSubgroup (conjSubgroup V g) k,
          conjSubgroup (E3.cClos V 1 (pCoreOf 2 K)) k⁆ := by
      rw [hCk]
    have hconjEq : ⁅conjSubgroup (conjSubgroup V g) k,
          conjSubgroup (E3.cClos V 1 (pCoreOf 2 K)) k⁆ =
        conjSubgroup ⁅conjSubgroup V g, E3.cClos V 1 (pCoreOf 2 K)⁆ k :=
      (E3.conjSubgroup_commutator (conjSubgroup V g) (E3.cClos V 1 (pCoreOf 2 K)) k).symm
    have hle : ⁅conjSubgroup V g, E3.cClos V 1 (pCoreOf 2 K)⁆ ≤ conjSubgroup V₀ g :=
      (hc.cClos_comm c h162).2.2
    rw [hcommBC, hconjEq]
    exact E3.conjSubgroup_mono_left k hle
  have hcard : Nat.card ↥(conjSubgroup (conjSubgroup V₀ g) k) = 2 := by
    rw [E3.card_conjSubgroup, E3.card_conjSubgroup, h2]
  exact (Subgroup.card_le_of_le hUC).trans (le_of_eq hcard)

theorem card_conj_le_two_mul_card_inf_centralizer (c : MinCex193 D V₀ V p X)
    (hc : Conf196 D V X g K) {k : G} (hk : k ∈ K) {Y : Subgroup G}
    (hY : Y ≤ E3.cClos V 1 (pCoreOf 2 K)) :
    Nat.card ↥(conjSubgroup (conjSubgroup V g) k) ≤
      2 * Nat.card ↥(conjSubgroup (conjSubgroup V g) k ⊓
        Subgroup.centralizer (Y : Set G)) := by
  have hQk : conjSubgroup (pCoreOf 2 K) k = pCoreOf 2 K :=
    CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.2
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk)
  have hrelB : (pCoreOf 2 K).relIndex (conjSubgroup (conjSubgroup V g) k) = 2 := by
    have h := E3.relIndex_conjSubgroup (pCoreOf 2 K) (conjSubgroup V g) k
    rw [hQk] at h
    rw [h]
    exact hc.relIndex_A c
  have hcardB : Nat.card ↥(conjSubgroup (conjSubgroup V g) k) =
      2 * Nat.card ↥(conjSubgroup (conjSubgroup V g) k ⊓ pCoreOf 2 K) := by
    have h := Subgroup.relIndex_mul_card (H := pCoreOf 2 K)
      (K := conjSubgroup (conjSubgroup V g) k)
    rw [hrelB, inf_comm] at h
    exact h.symm
  have hBQY : conjSubgroup (conjSubgroup V g) k ⊓ pCoreOf 2 K ≤
      Subgroup.centralizer (Y : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.1
      (conj_inf_pCoreOf_le_centralizer_cClos c hc hk hx) y (hY hy)
  calc Nat.card ↥(conjSubgroup (conjSubgroup V g) k) =
        2 * Nat.card ↥(conjSubgroup (conjSubgroup V g) k ⊓ pCoreOf 2 K) := hcardB
    _ ≤ 2 * Nat.card ↥(conjSubgroup (conjSubgroup V g) k ⊓
          Subgroup.centralizer (Y : Set G)) :=
        Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le (le_inf inf_le_left hBQY))

theorem card_le_two_mul_card_inf_centralizer_pairSub (c : MinCex193 D V₀ V p X)
    (h162 : W3Thm162Gt2 G) (hc : Conf196 D V X g K) {k : G} (hk : k ∈ K)
    (h2 : Nat.card ↥V₀ = 2) {Y : Subgroup G} (hY : Y ≤ Z193 D V) :
    Nat.card ↥Y ≤
      2 * Nat.card ↥(Y ⊓ centralizer (pairSub (conjSubgroup V g) k : Set G)) := by
  classical
  have hYC : Y ≤ E3.cClos V 1 (pCoreOf 2 K) :=
    hY.trans (hc.cClos_comm c h162).1
  have hYCA : Y ≤ Subgroup.centralizer (conjSubgroup V g : Set G) :=
    hY.trans (Z193_le_centralizer_conjSubgroup c hc)
  have hUcard := card_commutator_conj_cClos_le_two c h162 hc hk h2
  have hcommBY : ⁅conjSubgroup (conjSubgroup V g) k, Y⁆ ≤
      ⁅conjSubgroup (conjSubgroup V g) k, E3.cClos V 1 (pCoreOf 2 K)⁆ :=
    Subgroup.commutator_mono le_rfl hYC
  have hcardIndex := card_conj_le_two_mul_card_inf_centralizer c hc hk hYC
  have hstep := card_le_two_mul_card_inf_centralizer_of_commutator_le hUcard hcommBY hcardIndex
  have hcentPair : Y ⊓ centralizer (pairSub (conjSubgroup V g) k : Set G) =
      Y ⊓ centralizer (conjSubgroup (conjSubgroup V g) k : Set G) := by
    unfold pairSub
    rw [CFSG.GroupTheory.centralizer_sup_eq_inf_centralizer]
    rw [← inf_assoc, inf_eq_left.2 hYCA]
  calc Nat.card ↥Y ≤
        2 * Nat.card ↥(Y ⊓ centralizer (conjSubgroup (conjSubgroup V g) k : Set G)) :=
      hstep
    _ = 2 * Nat.card ↥(Y ⊓ centralizer (pairSub (conjSubgroup V g) k : Set G)) := by
        rw [hcentPair]

theorem gap1911e_holds (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h763 : ∀ (G' : Type) [Group G'] [Finite G'] (V' : Subgroup G'), SevenSixThreeAbelian V')
    (h2 : Nat.card ↥V₀ = 2) : Gap1911e D V X := by
  obtain ⟨g₁, g₂, K₁, K₂, k₁, k₂, hp⟩ := c.exists_pair1911 h162 h763
  exact ⟨g₁, g₂, K₁, K₂, k₁, k₂, hp,
    card_le_two_mul_card_inf_centralizer_pairSub c h162 hp.conf₁ hp.mem₁ h2 le_rfl,
    card_le_two_mul_card_inf_centralizer_pairSub c h162 hp.conf₂ hp.mem₂ h2 inf_le_left⟩

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end

module

public import CFSG.RankThree.GF2n.Stroth80.Sec94FreeStmt
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9ROneOm
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec97FiveTrans

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement


namespace S94F

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem not_mem_Q_of_conjMod (hc : Ctx M Q Z B) {t s x : G} (ht : t ∈ LB M Q B)
    (hxN : x ∉ hc.CN t) (hconj : ConjMod M Q s x) : s ∉ Q := by
  intro hsQ
  obtain ⟨-, g, hg, hq⟩ := hconj
  apply hxN
  apply hc.Q_le_CN ht
  have h1 : g * s * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) s).mp hsQ
  have e : x = x * (g * s * g⁻¹)⁻¹ * (g * s * g⁻¹) := by group
  rw [e]
  exact Q.mul_mem hq h1

theorem Vt_eq_of_mem_Z0 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement)
    (hP : Step94PointStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {s : G} (hs0 : s ∈ Z0)
    (hsQ : s ∉ Q) : Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  obtain ⟨r, hr⟩ := sec9AExists_of h34 h311a hNC G M Q Z B hc n t hs
  have hRs : Rt M (LB M Q B) s = Rt M (LB M Q B) t :=
    HS9.Rt_eq_of_mem_Z091 h34 h311a h311bComm h312b hs hr hZ0 hs0 hsQ
  obtain ⟨hprod, hcomm, -⟩ := sec9_N51 h34 h311a hNC hs hr
  have hZ0L : Z0 ≤ LB M Q B := by
    rw [HS9.isCentrePre_eq_inf91 hs hr hprod hcomm hZ0]
    exact inf_le_left
  have hQn : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have h35 : ∀ m ∈ M, CQt Q Z (LB M Q (conjSubgroup m B)) =
      ((conjSubgroup m B ⊔ Z : Subgroup G) : Set G) := fun m hm =>
    (stroth_3_5 h34 (hc.conj_of_mem hm) hs5.width hs5.n_gt (hc.noA2_conj hs5.noA2 hm)
      (hs5.gen.conj_of_mem hm)).2.1
  have hpt : ∀ m ∈ M, conjSubgroup m (LB M Q B) ≤ Rt M (LB M Q B) t →
      ∃ ρ ∈ Rt M (LB M Q B) t, conjSubgroup m (LB M Q B) = conjSubgroup ρ (LB M Q B) :=
    fun m hm hle => hP G M Q Z B hc n t hs m hm (by rw [hc.LB_conj hm]; exact hle)
  have hBV : ∀ m ∈ M, conjSubgroup m (LB M Q B) ≤ Rt M (LB M Q B) t →
      conjSubgroup m B ≤ Vt M (LB M Q B) B Z t := by
    intro m hm hle
    obtain ⟨ρ, hρ, hmρ⟩ := hpt m hm hle
    have hρM : ρ ∈ M := hc.Rt_le_M t hρ
    have e1 : ((conjSubgroup m B ⊔ Z : Subgroup G) : Set G) =
        ((conjSubgroup ρ B ⊔ Z : Subgroup G) : Set G) := by
      rw [← h35 m hm, ← h35 ρ hρM, hc.LB_conj hm, hc.LB_conj hρM, hmρ]
    have hle1 : conjSubgroup m B ≤ conjSubgroup ρ B ⊔ Z := by
      intro b hb
      have hb' : b ∈ ((conjSubgroup m B ⊔ Z : Subgroup G) : Set G) := Subgroup.mem_sup_left hb
      rw [e1] at hb'
      exact hb'
    have hVn : conjSubgroup ρ (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
      conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hρ)
    refine hle1.trans (sup_le ?_ sec39_Z_le_Vt)
    calc conjSubgroup ρ B ≤ conjSubgroup ρ (Vt M (LB M Q B) B Z t) :=
          Subgroup.map_mono (hc.B_le_Vt ht)
      _ = Vt M (LB M Q B) B Z t := hVn
  refine le_antisymm ?_ ?_
  · show Z ⊔ ⨆ (m : G) (_ : m ∈ M) (_ : s ∈ conjSubgroup m (LB M Q B)), conjSubgroup m B ≤ _
    refine sup_le sec39_Z_le_Vt (iSup₂_le fun m hm => iSup_le fun hsm => hBV m hm ?_)
    rw [← hRs]
    unfold Rt
    exact le_iSup₂_of_le m hm (le_iSup_of_le hsm le_rfl)
  · show Z ⊔ ⨆ (m : G) (_ : m ∈ M) (_ : t ∈ conjSubgroup m (LB M Q B)), conjSubgroup m B ≤ _
    refine sup_le sec39_Z_le_Vt (iSup₂_le fun m hm => iSup_le fun htm => ?_)
    have hle : conjSubgroup m (LB M Q B) ≤ Rt M (LB M Q B) t := by
      unfold Rt
      exact le_iSup₂_of_le m hm (le_iSup_of_le htm le_rfl)
    obtain ⟨ρ, hρ, hmρ⟩ := hpt m hm hle
    have hsm : s ∈ conjSubgroup m (LB M Q B) := by
      rw [hmρ, mem_conjSubgroup]
      have hnz := hZ0.mem_normalizer hQn ((Rt M (LB M Q B) t).inv_mem hρ)
      have h1 := (Subgroup.mem_normalizer_iff.mp hnz s).mp hs0
      rw [inv_inv] at h1
      exact hZ0L h1
    show conjSubgroup m B ≤ Z ⊔ ⨆ (m : G) (_ : m ∈ M) (_ : s ∈ conjSubgroup m (LB M Q B)),
      conjSubgroup m B
    exact le_sup_of_le_right (le_iSup₂_of_le m hm (le_iSup_of_le hsm le_rfl))

theorem omegaPlusNat_conj_of_mem_Z0 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement)
    (hP : Step94PointStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {s : G} (hs0 : s ∈ Z0)
    (hsQ : s ∉ Q) {z : G} (hz : z ∈ M) : OmegaPlusNat hc (z * s * z⁻¹) 2 := by
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  obtain ⟨r, hr⟩ := sec9AExists_of h34 h311a hNC G M Q Z B hc n t hs
  have hRs : Rt M (LB M Q B) s = Rt M (LB M Q B) t :=
    HS9.Rt_eq_of_mem_Z091 h34 h311a h311bComm h312b hs hr hZ0 hs0 hsQ
  have hVs := Vt_eq_of_mem_Z0 h34 h311a h311bComm h312b hP hs hZ0 hs0 hsQ
  have hCN : hc.CN s = hc.CN t := by
    ext y
    rw [Ctx.mem_CN, Ctx.mem_CN, hRs, hVs]
  obtain ⟨K, hK, hKf, hcard, hrep⟩ := hs.plus4
  refine ⟨K, hK, hKf, hcard, ?_⟩
  have h1 := hrep.conjG z
  rw [← hRs, ← hVs, ← hCN, conjSubgroup_Rt_eq hz s, conjSubgroup_Vt_eq hz (hc.conj_Z_eq hz) s,
    hc.conj_Z_eq hz, ← Ctx.CN_conjM hc hz s] at h1
  exact h1

end S94F

theorem step94YConj_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    (h312b : Stroth312bStatement) (h92 : Stroth92Statement) (hB : Step94ConjVStatement)
    (hP : Step94PointStatement) (hR0 : Step94ZInR0Statement) : Step94YConjStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 s hs0 x hxL hxN hconj Y hdp hYsl z hz hZ'
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hn5 := sec9NGeFive_of h34 h311a h311bComm h311bCard G M Q Z B hc n t hs
  have hsplit := split95_of_step94 h92 hB hc hs hZ0 hs0 hxL hxN hconj hdp hYsl
  have h4 := sec4_of h34 h311a G M Q Z B hc n t hs _ Y hsplit
  have hsQ : s ∉ Q := S94F.not_mem_Q_of_conjMod hc ht hxN hconj
  have heZ : z * s * z⁻¹ ∈ conjSubgroup z Z0 := by
    rw [mem_conjSubgroup, show z⁻¹ * (z * s * z⁻¹) * z = s by group]
    exact hs0
  have heL : z * s * z⁻¹ ∈ LB M Q B := hZ' heZ
  have heQ : z * s * z⁻¹ ∉ Q := by
    intro h
    apply hsQ
    have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hz))
      (z * s * z⁻¹)).mp h
    rwa [show z⁻¹ * (z * s * z⁻¹) * z⁻¹⁻¹ = s by group] at h1
  have heX : z * s * z⁻¹ ∈ Sec9R0 hc t x :=
    hR0 G M Q Z B hc n t hs Z0 hZ0 s hs0 x hxL hxN hconj Y hdp hYsl hn5 z hz hZ' heZ
  have hOm := S94F.omegaPlusNat_conj_of_mem_Z0 h34 h311a h311bComm h312b hP hs hZ0 hs0 hsQ hz
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  obtain ⟨r, hr⟩ := sec9AExists_of h34 h311a hNC G M Q Z B hc n t hs
  have hRs : Rt M (LB M Q B) s = Rt M (LB M Q B) t :=
    HS9.Rt_eq_of_mem_Z091 h34 h311a h311bComm h312b hs hr hZ0 hs0 hsQ
  have hRe : Rt M (LB M Q B) (z * s * z⁻¹) = conjSubgroup z (Rt M (LB M Q B) t) := by
    rw [← conjSubgroup_Rt_eq hz s, hRs]
  have hYn := hsplit.conjSubgroup_eq_self_of_mem_Rt
  have hsplit0 := hsplit
  obtain ⟨⟨-, -, hQY, hYR, -, -, -⟩, -, -⟩ := hsplit0
  refine HS9.normal_eq_Y h34 h311a h311bCard h311bComm hc hs hsplit h4 ⟨heL, heX⟩ heQ hOm
    ?_ ?_ ?_ ?_
  · rw [← hc.conj_Q_eq hz]
    exact Subgroup.map_mono hQY
  · rw [hRe]
    exact Subgroup.map_mono hYR
  · intro ρ hρ
    have hρ' : z⁻¹ * ρ * z ∈ Rt M (LB M Q B) t := by
      rw [hRe] at hρ
      exact mem_conjSubgroup.mp hρ
    calc conjSubgroup ρ (conjSubgroup z Y)
        = conjSubgroup z (conjSubgroup (z⁻¹ * ρ * z) Y) := by
          rw [← conjSubgroup_mul, ← conjSubgroup_mul]
          congr 1
          group
      _ = conjSubgroup z Y := by rw [hYn _ hρ']
  · exact hc.conj_Q_eq hz ▸ QuotSat.conj (fun X Y _ _ e h => IsSLModel.congr e h) hYsl z

end CFSG.RankThree.GF2n.Stroth80

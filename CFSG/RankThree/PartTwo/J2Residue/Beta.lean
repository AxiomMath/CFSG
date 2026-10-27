module

public import CFSG.RankThree.PartTwo.J2Residue.KFacts
public import CFSG.RankThree.PartTwo.J2Residue.Config
import CFSG.RankThree.PartTwo.J2Residue.Endgame
import CFSG.RankThree.PartTwo.J2Residue.Lemma17
import CFSG.RankThree.PartTwo.J2Residue.ChiefFactor
import CFSG.RankThree.PartTwo.J2Residue.G1Lift
import CFSG.RankThree.PartTwo.J2Residue.ChiefRep
import CFSG.RankThree.PartTwo.J2Residue.Dim8
import CFSG.RankThree.PartTwo.J2Residue.CentralInvolution
import CFSG.RankThree.PartTwo.J2Residue.Involution
import CFSG.RankThree.PartTwo.Sec16.Kcd166.FixRank

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem eight_le_of_beta (hG1 : KG1) {L LB : Subgroup G} {d : G}
    (hJ : J2Config L d LB) {Y : Subgroup G}
    (hY : L ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤ Y) {r : ℕ} [Fact r.Prime]
    (hr5 : 5 ≤ r) {V : Type} [AddCommGroup V] [Module (ZMod r) V] [Module.Finite (ZMod r) V]
    (ρ : Representation (ZMod r) ↥Y V) (hdY : d ∈ Y) (hρd : ρ ⟨d, hdY⟩ = 1) {l : G}
    (hlLB : l ∈ LB) (hlY : l ∈ Y) (hρl : ρ ⟨l, hlY⟩ ≠ 1) : 8 ≤ Module.finrank (ZMod r) V := by
  have hLBY : LB ≤ Y :=
    (hJ.lB_le.trans (inf_le_inf_left L (centralizer_le_normalizer_zpowers d))).trans hY
  obtain ⟨S, hSLB, hS27, hdS, hexp⟩ := hJ.exists_sylow
  obtain ⟨htrans, n, hnY', hnS, hinv⟩ := hJ.g1 hG1 hSLB hS27 hdS
  have hnY : n ∈ Y := hY hnY'
  have hSY : S ≤ Y := hSLB.trans hLBY
  have h3 : (3 : ZMod r) ≠ 0 := by
    have := natCast_ne_zero_of_lt (r := r) (n := 3) (by norm_num) (by omega)
    exact_mod_cast this
  refine eight_le_finrank h3 ρ (S := S.subgroupOf Y) (d := ⟨d, hdY⟩) hdS
    ((Subgroup.orderOf_mk d hdY).trans hJ.orderOf_d) hρd
    ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv).trans hS27) ?_ ?_ ?_ ?_
    ⟨⟨n, hnY⟩, mem_normalizer_subgroupOf hnY hnS, ?_⟩
  ·
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    apply Subtype.ext
    simpa using Subgroup.mem_centralizer_iff.mp (hJ.lB_le (hSLB hs)).2 d (Set.mem_singleton d)
  ·
    intro s hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hexp s hs)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  ·
    by_contra hcon
    push Not at hcon
    set N : Subgroup G := LB ⊓ (MonoidHom.ker ρ).map Y.subtype with hN
    have hker :
        Y ≤ Subgroup.normalizer (((MonoidHom.ker ρ).map Y.subtype : Subgroup G) : Set G) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨⟨y, hy⟩ * w * ⟨y, hy⟩⁻¹, (MonoidHom.normal_ker ρ).conj_mem w hw _, by simp⟩
      · rintro ⟨w, hw, hwx⟩
        refine ⟨⟨y, hy⟩⁻¹ * w * ⟨y, hy⟩, ?_, ?_⟩
        · simpa using (MonoidHom.normal_ker ρ).conj_mem w hw (⟨y, hy⟩⁻¹)
        · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hwx ⊢
          rw [hwx]
          group
    have hNn : LB ≤ Subgroup.normalizer (N : Set G) :=
      (le_inf Subgroup.le_normalizer (hLBY.trans hker)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have h27 : 27 ∣ Nat.card N := by
      rw [← hS27]
      exact Subgroup.card_dvd_of_le
        (le_inf hSLB fun s hs => ⟨⟨s, hSY hs⟩, (MonoidHom.mem_ker).mpr (hcon _ hs), rfl⟩)
    have hNeq : N = LB := hJ.eq_lB_of_dvd inf_le_left hNn (Or.inl h27)
    have hl : l ∈ N := by rw [hNeq]; exact hlLB
    obtain ⟨-, w, hw, hwl⟩ := hl
    apply hρl
    have hwl' : w = ⟨l, hlY⟩ := Subtype.ext hwl
    rw [← hwl']
    exact MonoidHom.mem_ker.mp hw
  ·
    intro T₁ T₂ h₁ h₁' h₂ h₂'
    have hmap : ∀ T : Subgroup ↥Y, Subgroup.zpowers ⟨d, hdY⟩ < T → T < S.subgroupOf Y →
        Subgroup.zpowers d < T.map Y.subtype ∧ T.map Y.subtype < S := by
      intro T hT hT'
      refine ⟨?_, ?_⟩
      · have := (Subgroup.map_lt_map_iff_of_injective Y.subtype_injective).mpr hT
        simpa [MonoidHom.map_zpowers] using this
      · have := (Subgroup.map_lt_map_iff_of_injective Y.subtype_injective).mpr hT'
        rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hSY] at this
    obtain ⟨a₁, b₁⟩ := hmap T₁ h₁ h₁'
    obtain ⟨a₂, b₂⟩ := hmap T₂ h₂ h₂'
    obtain ⟨m, hmY', hmS, hm⟩ := htrans _ _ a₁ b₁ a₂ b₂
    have hmY : m ∈ Y := hY hmY'
    refine ⟨⟨m, hmY⟩, mem_normalizer_subgroupOf hmY hmS, ?_⟩
    apply Subgroup.map_injective Y.subtype_injective
    rw [← hm, Subgroup.map_map, Subgroup.map_map]
    congr 1
  ·
    intro s hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hinv s hs)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩

theorem false_of_beta (hG1 : KG1) (hfix : KJFix) (hsplit : KJSplit) (hcover : KJCover)
    (hrk : ∀ q : ℕ, q.Prime → 3 < q → CFSG.Assembly.RankThreeEven.localRank q G < 3)
    {L LB Θ : Subgroup G} {d : G} (hJ : J2Config L d LB) (hU : CFSG.Open.pCoreOf 2 LB ≠ ⊥)
    (hΘs : Group.IsSolvable Θ) (hΘ3 : ¬ 3 ∣ Nat.card Θ) (hΘ2 : CFSG.Open.pCoreOf 2 Θ = ⊥)
    (hUΘ : CFSG.Open.pCoreOf 2 LB ≤ Θ) (hΘd : Θ ≤ Subgroup.centralizer ({d} : Set G))
    (hYΘ : L ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤
      Subgroup.normalizer (Θ : Set G)) : False := by
  set Y : Subgroup G := L ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G) with hY
  have hCY : L ⊓ Subgroup.centralizer ({d} : Set G) ≤ Y :=
    inf_le_inf_left L (centralizer_le_normalizer_zpowers d)
  have hLBY : LB ≤ Y := hJ.lB_le.trans hCY
  obtain ⟨hZ1, hZ2, hZU, hZY, hYZ⟩ := omegaZOf_pCoreOf_facts hU hLBY hJ.normalizer_le
  set Z₀ := Sec3.omegaZOf (CFSG.Open.pCoreOf 2 LB) with hZ₀
  obtain ⟨r, hr, hr5, F₁, F₂, hF₁Θ, hch, u, huZ, f, hfF, hfu⟩ :=
    exists_chiefFactor hΘs hΘ3 hΘ2 hZ2 hZ1 (hZU.trans hUΘ) hZY hYΘ
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨V, hV1, hV2, hV3, ρ, q, hρ, hq⟩ := exists_chiefRep_of_isChiefFactorUnder hch
  letI := hV1
  letI := hV2
  haveI := hV3
  have hF₁ : IsPGroup r F₁ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup r Θ).to_le hF₁Θ
  have hloc := Sec16.Kcd166.card_le_sq_of_localRank_lt hr (hrk r hr (by omega))
  have hR3 : ∀ t : ↥Y, t * t = 1 → t ≠ 1 →
      Module.finrank (ZMod r) (LinearMap.ker (ρ t - 1)) ≤ 3 := fun t ht ht1 =>
    hq.finrank_ker_le_three hr5 hloc hch hF₁ (isPGroup_zpowers_of_mul_self ht) ht1
  have h2 : (2 : ZMod r) ≠ 0 := by
    have := natCast_ne_zero_of_lt (r := r) (n := 2) (by norm_num) (by omega)
    exact_mod_cast this
  have hdY : d ∈ Y := ⟨hJ.mem_d, Subgroup.le_normalizer (Subgroup.mem_zpowers d)⟩
  have hρd : ρ ⟨d, hdY⟩ = 1 := by
    rw [hq.rho_eq_one_iff hch]
    intro m hm
    have hmd : d * m = m * d := Subgroup.mem_centralizer_iff.mp
      (hΘd (CFSG.LieType.BorelTits.pCoreOf_le r Θ (hF₁Θ hm))) d (Set.mem_singleton d)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hmd.symm]
    exact F₂.one_mem
  have huLB : u ∈ LB := (hZU.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 LB)) huZ
  have hρu : ρ ⟨u, hZY huZ⟩ ≠ 1 := by
    rw [Ne, hq.rho_eq_one_iff hch]
    exact fun h => hfu (h f hfF)
  have h8 := eight_le_of_beta hG1 hJ le_rfl hr5 ρ hdY hρd huLB (hZY huZ) hρu
  have hEn : (Z₀.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZY).mpr hYZ
  have hE2 : ∀ s ∈ Z₀.subgroupOf Y, s * s = 1 := fun s hs =>
    Subtype.ext (by simpa using ((mem_omegaZOf_iff _).mp hs).2.2)
  have hEΛ : Z₀.subgroupOf Y ≤ LB.subgroupOf Y := fun s hs =>
    (hZU.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 LB)) hs
  obtain ⟨z, hzE, hz1, hρz, -⟩ := exists_neg_one_of_eight_le h2 hρ hEn hE2
    (subgroupOf_ne_bot hZ1 hZY) (isPerfect_subgroupOf hJ.isPerfect_lB hLBY) hEΛ
    (fun s hs hs1 => hR3 s (hE2 s hs) hs1) h8
  obtain ⟨x, hxW, hx2, hx1, hxz, hxzc⟩ := exists_involution hJ
    (J2Config.four_le_card hfix hsplit hcover hJ hU) (z := (z : G)) hzE
    (fun h => hz1 (Subtype.ext h))
  have hxY : x ∈ Y := (sup_le hLBY
    ((inf_le_inf_right _ (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).trans hCY)) hxW
  have h6 := finrank_le_two_mul_of_neg_one h2 ρ hR3 (x := ⟨x, hxY⟩) hρz (hE2 z hzE)
    (Subtype.ext hx2) (fun h => hx1 (congrArg Subtype.val h))
    (fun h => hxz (congrArg Subtype.val h)) (Subtype.ext hxzc)
  omega

end CFSG.RankThree.PartTwo.J2Residue

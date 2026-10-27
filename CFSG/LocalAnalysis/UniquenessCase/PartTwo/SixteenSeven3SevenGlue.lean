module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SevenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c167_commute_lbar (D : Data G) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h151 : Hyp151 D ⊥ V L) {φ : MulAut (Vtil ⊥ V hV)} (hφ : φ ∈ Mbar D.M ⊥ V hV)
    (hne : φ ∉ normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV)))) :
    commSub (commSub ⊤ (lBar ⊥ V hV L))
      ((lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom) = ⊥ := by
  obtain ⟨m, hmM, rfl⟩ := (mem_barSub ⊥ V hV D.M φ).1 hφ
  have hmM' : ((m⁻¹ : ↥(stabTil ⊥ V)) : G) ∈ D.M := by
    rw [Subgroup.coe_inv]
    exact D.M.inv_mem hmM
  have h2 : barSub ⊥ V hV (conjSubgroup L ((m⁻¹ : ↥(stabTil ⊥ V)) : G)) =
      (lBar ⊥ V hV L).map (MulAut.conj (actTil ⊥ V hV m)).toMonoidHom := by
    rw [s15_Infra_barSub_conjSubgroup ⊥ V hV (m⁻¹).2 L]
    have h3 : (actTil ⊥ V hV ⟨((m⁻¹ : ↥(stabTil ⊥ V)) : G), (m⁻¹).2⟩)⁻¹ = actTil ⊥ V hV m := by
      rw [show (⟨((m⁻¹ : ↥(stabTil ⊥ V)) : G), (m⁻¹).2⟩ : ↥(stabTil ⊥ V)) = m⁻¹ from rfl,
        map_inv, inv_inv]
    rw [h3]
    rfl
  have hne' : ((m⁻¹ : ↥(stabTil ⊥ V)) : G) * (1 : G)⁻¹ ∉ nBar D.M ⊥ V hV L := by
    rw [inv_one, mul_one]
    intro hmem
    rw [s15_Infra_mem_nBar_iff h151.hyp125 hV hmM', h2] at hmem
    exact hne (Subgroup.mem_normalizer_iff_map_conj_eq.2 hmem)
  have h := (s15_Kbar_commute_conj h151 (m := (1 : G)) (m' := ((m⁻¹ : ↥(stabTil ⊥ V)) : G))
    D.M.one_mem hmM' hne').2
  rw [conjSubgroup_one, h2] at h
  exact h

theorem s16c167_sevenCfg_of_case168_4 (D : Data G) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D ⊥ V L hV) (h4 : Case168_4At D ⊥ V hV L 7 3) :
    ∃ Z : Subgroup (Vtil ⊥ V hV), SevenCfg (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) Z := by
  have h151 : Hyp151 D ⊥ V L := hc.setting.hyp151
  have hWsq : ∀ x : Vtil ⊥ V hV, x * x = 1 := fun x => by
    have := s15_Infra_vtil_sq_eq_one ⊥ V hV x
    rwa [pow_two] at this
  obtain ⟨hLab, hsym, -⟩ := h4
  obtain ⟨Z, hZ, -, hsup, hncard, hperm⟩ := hsym
  have hd : dParam 7 = 3 := by
    unfold dParam
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime (p := 3) (by decide) (by decide)
  rw [hd] at hZ
  have hp : IsPGroup 2 ↥Z := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    simpa [pow_two] using hWsq (x : Vtil ⊥ V hV)
  have hZcard : Nat.card ↥Z = 8 := by
    rw [card_eq_two_pow_of_isPGroup hp, hZ]
    norm_num
  exact ⟨Z, { sq := hWsq
              hZ := hZcard
              sup := hsup
              ncard := hncard
              perm := hperm
              le := barSub_mono ⊥ V hV h151.le
              lrank := hLab
              commute := fun g hg hgn => s16c167_commute_lbar D hV h151 hg hgn }⟩

theorem s16c167_rk_le_two_of_case168_4_seven (D : Data G) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) (h4 : Case168_4At D ⊥ V hV L 7 3)
    {X : Subgroup (MulAut (Vtil ⊥ V hV))} (hXM : X ≤ Mbar D.M ⊥ V hV)
    (hX : IsElemAbelian2 X) : rk ↥X ≤ 2 := by
  obtain ⟨Z, hZ⟩ := s16c167_sevenCfg_of_case168_4 D hV hc h4
  have hle := s16c167_card_le_four_of_sevenCfg hZ hXM hX
  have hp : IsPGroup 2 ↥X := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    simpa using hX.2 (x : MulAut (Vtil ⊥ V hV)) x.2
  rw [card_eq_two_pow_of_isPGroup hp] at hle
  by_contra hlt
  have h8 : 2 ^ 3 ≤ 2 ^ rk ↥X := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1Odd361
import CFSG.RankThree.PartTwo.Sec11.SimsR1L2CubeSolvableA
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec11.TwoStarProofLF

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1

private theorem five_le_of_prime_of_three_lt {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : 5 ≤ p := by
  by_contra hlt
  have : p = 4 := by omega
  subst this
  exact absurd hp (by norm_num)

private theorem exists_two_element_fixed_of_L2Cube {X : Type} [Group X] [Finite X]
    {N : Subgroup X} [N.Normal] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} [Fact r.Prime]
    (hr5 : 5 ≤ r) (hFF : SimsR1L2CubeFaithfulFix)
    (e : X ⧸ N ≃* projSL 2 (GaloisField p (3 * 1))) {V : Type} [AddCommGroup V]
    [Module (ZMod r) V] [Module.Finite (ZMod r) V] (ρ : X →* (V →ₗ[ZMod r] V))
    (hN : N ≤ ρ.ker) (hρ : ∃ x, ρ x ≠ 1) :
    ∃ t : X, ρ t ≠ 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
      3 ≤ Module.finrank (ZMod r) (LinearMap.ker (ρ t - 1)) := by
  have hF : Nat.card (GaloisField p (3 * 1)) = p ^ 3 := by
    simpa using GaloisField.card p (3 * 1) (by norm_num)
  have : IsSimpleGroup (projSL 2 (GaloisField p (3 * 1))) :=
    L2CubeSolvable.isSimpleGroup_projSL_two hp5 hF
  have hsimple : IsSimpleGroup (X ⧸ N) := MulEquiv.isSimpleGroup e
  set ρbar := QuotientGroup.lift N ρ hN with hρbar
  have hinj : Function.Injective ρbar := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρbar.ker with hb | ht
    · exact hb
    · exfalso
      obtain ⟨x, hx⟩ := hρ
      apply hx
      have hmem : (x : X ⧸ N) ∈ ρbar.ker := ht ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hρbar, QuotientGroup.lift_mk] at hmem
      exact hmem
  set ρ' := ρbar.comp e.symm.toMonoidHom with hρ'
  have hρ'inj : Function.Injective ρ' := hinj.comp e.symm.injective
  obtain ⟨s, hord, hdim⟩ := hFF p hp5 r hr5 V ρ' hρ'inj
  have hss : s * s = 1 := by
    have h2 : s ^ orderOf s = 1 := pow_orderOf_eq_one s
    rw [hord] at h2
    rw [← sq]
    exact h2
  have hs1 : s ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  obtain ⟨t, htu, k, htk⟩ := TwoStarProof.exists_two_element_lift (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (y := e.symm s) (by rw [← map_mul, hss, map_one])
  have hρt : ρ t = ρ' s := by
    rw [hρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← htu, QuotientGroup.mk'_apply,
      hρbar, QuotientGroup.lift_mk]
  refine ⟨t, ?_, ⟨k, htk⟩, ?_⟩
  · rw [hρt]
    intro h1
    exact hs1 (hρ'inj (h1.trans (map_one ρ').symm))
  · rw [hρt]
    exact hdim

private theorem commutator_eq_bot_of_centralizes_selfCentralizing {G : Type*} [Group G]
    {L T F : Subgroup G} (hperf : Group.IsPerfect L)
    (hLT : L ≤ Subgroup.normalizer (T : Set G)) (hTF : T ≤ Subgroup.normalizer (F : Set G))
    (hLF : ⁅L, F⁆ = ⊥) (hself : ∀ x ∈ T, (∀ v ∈ F, x * v * x⁻¹ * v⁻¹ = 1) → x ∈ F) :
    ⁅L, T⁆ = ⊥ := by
  have hFL : ⁅F, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hLF
  have h3 : ⁅⁅T, L⁆, F⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [hLF]
      exact Subgroup.commutator_bot_left T
    · refine eq_bot_iff.mpr ?_
      calc ⁅⁅F, T⁆, L⁆ ≤ ⁅F, L⁆ :=
            Subgroup.commutator_mono (Subgroup.le_normalizer_iff_commutator_le_left.mp hTF) le_rfl
        _ = ⊥ := hFL
  have hTL : ⁅T, L⁆ ≤ F := by
    intro x hx
    refine hself x (Subgroup.le_normalizer_iff_commutator_le_left.mp hLT hx) fun v hv => ?_
    have h4 : ⁅x, v⁆ ∈ ⁅⁅T, L⁆, F⁆ := Subgroup.commutator_mem_commutator hx hv
    rw [h3, Subgroup.mem_bot, commutatorElement_def] at h4
    exact h4
  have h5 : ⁅⁅T, L⁆, L⁆ = ⊥ := by
    refine eq_bot_iff.mpr ?_
    calc ⁅⁅T, L⁆, L⁆ ≤ ⁅F, L⁆ := Subgroup.commutator_mono hTL le_rfl
      _ = ⊥ := hFL
  have h6 : ⁅⁅L, L⁆, T⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [Subgroup.commutator_comm L T]
      exact h5
    · exact h5
  rwa [Sec6.commutator_self_eq_of_isPerfect hperf] at h6

section Residue


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

open TwoStarProof in
theorem lfAt_c_odd (hB : KFacts.BlackburnRankTwo) (hDk : SimsR1L2CubeTwoLocal)
    (hFF : SimsR1L2CubeFaithfulFix) (hSF : SimsR1L2CubeSolvableFix) (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) (hodd : IsL2OddCharOne L) :
    LFAt L c := by
  have hθodd := odd_card_theta_L_odd hB hDk h45 h hT hodd
  obtain ⟨p, hp, hp3, ⟨e⟩⟩ := hodd
  haveI := hp
  have hp5 := five_le_of_prime_of_three_lt hp.out hp3
  have hLC := le_centralizer_of_config h
  have hCH : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) : Set G) :=
    Subgroup.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta _)
  have hLH := hLC.trans hCH
  have : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have := Sec4.aschbacherSolvableCore_characteristic L
  have hfix : ∀ (r : ℕ) [Fact r.Prime], 5 ≤ r → ∀ (V : Type) [AddCommGroup V]
      [Module (ZMod r) V] [Module.Finite (ZMod r) V] (ρ : L →* (V →ₗ[ZMod r] V)),
        (∃ x, ρ x ≠ 1) → ∃ t : L, ρ t ≠ 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
          3 ≤ Module.finrank (ZMod r) (LinearMap.ker (ρ t - 1)) := by
    intro r _ hr5 V _ _ _ ρ hρ
    by_cases hθ : aschbacherSolvableCore 3 L ≤ ρ.ker
    · exact exists_two_element_fixed_of_L2Cube hp5 hr5 hFF e ρ hθ hρ
    · have hθs : Group.IsSolvable (aschbacherSolvableCore 3 L) :=
        (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).1
      have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
        (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
      exact hSF p hp5 r hr5 L inferInstance (aschbacherSolvableCore 3 L) hθs hθodd hθ3 ⟨e⟩ V ρ hθ
  by_contra hnot
  obtain ⟨q, _, hq5, t, ht1, ⟨k, htk⟩, EΘ, n, hn, hEcard, hEcomm, hEexp, hEfix⟩ :=
    exists_fixed_elemAbelian hLH (not_three_dvd_card_inSubgroup_theta _) hnot hfix
  obtain ⟨X₂, hX₂, R', hR'X₂, hR'e, hR'card⟩ := exists_twoLocal_elemAbelian (Sec6.theta_le _)
    (pCore_theta_le_pCore _) hLH (by omega) ht1 htk hEcard hEcomm hEexp hEfix
  have h1 := Sec5.le_pRank_of_elemAbelian (Fact.out : q.Prime) hR'X₂ hR'e hR'card
  have h2 := CFSG.RankThree.Classical.pRank_le_localRank (Fact.out : q.Prime).one_lt hX₂
  have h3 := h.localRank_lt q Fact.out (by omega)
  omega

theorem commutator_L_thetaCent_c_eq_bot_odd (hB : KFacts.BlackburnRankTwo)
    (hDk : SimsR1L2CubeTwoLocal) (hFF : SimsR1L2CubeFaithfulFix)
    (hSF : SimsR1L2CubeSolvableFix) (h45 : Sec4.Item4_5) (h : ResidueConfig G A c L a R Y d)
    (hT : A ∉ partTwoT G) (hodd : IsL2OddCharOne L) :
    ⁅L, thetaCent c⁆ = ⊥ ∧ aschbacherSolvableCore 3 L = ⊥ := by
  have hLF := lfAt_c_odd hB hDk hFF hSF h45 h hT hodd
  have hθodd := odd_card_theta_L_odd hB hDk h45 h hT hodd
  have hperf : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hLC := TwoStarProof.le_centralizer_of_config h
  have hO2 : inSubgroup (CFSG.pCore 2) (thetaCent c) = ⊥ :=
    le_bot_iff.mp ((TwoStarProof.pCore_theta_le_pCore (Subgroup.centralizer ({c} : Set G))).trans
      (pCore_two_centralizer_c_eq_bot_odd hB h45 h hT hodd).le)
  have hLF₂ : ⁅L, inSubgroup twoFitting (thetaCent c)⁆ = ⊥ := by
    have h1 : ⁅L, inSubgroup twoFitting (thetaCent c)⁆ ≤ inSubgroup (CFSG.pCore 2) (thetaCent c) :=
      hLF
    rw [hO2] at h1
    exact le_bot_iff.mp h1
  have hLθ : L ≤ Subgroup.normalizer (thetaCent c : Set G) :=
    hLC.trans (Subgroup.le_normalizer.trans
      (Sec6.normalizer_le_normalizer_theta (Subgroup.centralizer ({c} : Set G))))
  have hθF : thetaCent c ≤ Subgroup.normalizer (inSubgroup twoFitting (thetaCent c) : Set G) :=
    Subgroup.le_normalizer.trans (KFTools.normalizer_le_normalizer_twoFitting _)
  have hcomm : ⁅L, thetaCent c⁆ = ⊥ :=
    commutator_eq_bot_of_centralizes_selfCentralizing hperf hLθ hθF hLF₂ fun x hx hv =>
      KFTools.mem_inSubgroup_twoFitting_of_commutator_mem
        (Sec6.theta_solvable_and_not_dvd (Subgroup.centralizer ({c} : Set G))).1 hx
        fun v hv' => by rw [hv v hv']; exact Subgroup.one_mem _
  refine ⟨hcomm, ?_⟩
  have hθT : inSubgroup (aschbacherSolvableCore 3) L ≤ thetaCent c :=
    TwoStarProof.theta_L_le h45 h hT
  have hcent : aschbacherSolvableCore 3 L ≤ Subgroup.center L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h7 : ⁅(g : G), (x : G)⁆ ∈ ⁅L, thetaCent c⁆ :=
      Subgroup.commutator_mem_commutator g.2 (hθT ⟨x, hx, rfl⟩)
    rw [hcomm, Subgroup.mem_bot] at h7
    exact commutatorElement_eq_one_iff_mul_comm.mp h7
  obtain ⟨p, hp, hp3, ⟨e⟩⟩ := hodd
  haveI := hp
  have hp5 := five_le_of_prime_of_three_lt hp.out hp3
  have hF : Nat.card (GaloisField p (3 * 1)) = p ^ 3 := by
    simpa using GaloisField.card p (3 * 1) (by norm_num)
  haveI : Group.IsPerfect L := hperf
  set π : L →* projSL 2 (GaloisField p (3 * 1)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) with hπ
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = aschbacherSolvableCore 3 L := by
    ext x
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hbot := L2CubeSolvable.kernel_eq_bot_of_central_odd hp.out hp5 hF π hπs
    (by rw [hker]; exact hcent) (by rw [hker]; exact hθodd)
  rwa [hker] at hbot

end Residue

end CFSG.RankThree.PartTwo.Sec11.SimsR1

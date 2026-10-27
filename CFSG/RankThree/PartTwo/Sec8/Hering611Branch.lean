module

public import CFSG.RankThree.PartTwo.Sec8.Hering611K
import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofTools
import CFSG.RankThree.PartTwo.Sec12.Item125Act

public section

namespace CFSG.RankThree.PartTwo.Sec6.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL)

open CFSG.RankThree.PartTwo.Sec8.Hering611
open CFSG.GorensteinWalter (PSL2)

open Res611Res4 Res611Res7
open scoped commutatorElement

section Certs

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}

theorem odd_card_theta_K (h45 : Sec4.Item4_5) {S K : Subgroup G} (C : Cfg611 G A c L E T d S K) :
    Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) := by
  obtain ⟨B, hBe, hB81, hBN⟩ := exists_big_elemAbelian h45 C
  exact Res611Res3.odd_card_theta C.standing.evenRank_eq hBe hB81 hBN

theorem false_of_L2 (h45 : Sec4.Item4_5)
    {S K : Subgroup G} (C : Cfg611 G A c L E T d S K) {n : ℕ} (hn : 1 ≤ n)
    (φK : K ⧸ aschbacherSolvableCore 3 K ≃* projSL 2 (GaloisField 3 (3 * n))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := C.standing
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := C.mem_S.1.1
  have hcA := C.c_mem
  have hc1 := C.c_ne_one
  have hcE := C.c_mem_E
  have hdE : d ∈ E := C.d_mem.1
  have hdA : d ∈ A := C.mem_E.2 hdE
  have hd1 : d ≠ 1 := fun h => C.d_not_mem (h ▸ Subgroup.one_mem _)
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c C.mem_L
  have hKd : K ∈ thetaComponentsAt 3 d := lZeroStarAt_subset A d C.mem_K
  obtain ⟨φ⟩ := C.iso_L
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hAe hcA hc1 L hLc
  have hθodd := Res611Res3.odd_card_theta hst.evenRank_eq hAe
    (by rw [C.card_A]) hAL
  obtain ⟨hdN, hQ, -⟩ := fieldCent_facts_two φ C.d_field hd3
  have hTd : T ≤ L ⊓ Subgroup.centralizer ({d} : Set G) := le_inf C.T_le_L fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp C.d_mem.2 t ht)
  obtain ⟨hET, hTab, hT4⟩ := mem_fourGroups_iff.mp C.mem_T.1
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4]; norm_num)
  have hTK : T ≤ K := (le_sec11K_of_isPGroup_two hθodd hdN hd3 hQ.1 hTd hT2).trans C.perf_le
  have hTθK : T ⊓ inSubgroup (aschbacherSolvableCore 3) K = ⊥ := by
    have hodd := odd_card_theta_K h45 C
    have h1 : Nat.card (T ⊓ inSubgroup (aschbacherSolvableCore 3) K : Subgroup G) ∣ 4 := by
      rw [← hT4]; exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (T ⊓ inSubgroup (aschbacherSolvableCore 3) K : Subgroup G) ∣
        Nat.card (inSubgroup (aschbacherSolvableCore 3) K) :=
      Subgroup.card_dvd_of_le inf_le_right
    have hcop : Nat.Coprime 4 (Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) := by
      have : Nat.Coprime 2 (Nat.card (inSubgroup (aschbacherSolvableCore 3) K)) :=
        (Nat.coprime_two_left).mpr hodd
      simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using this.pow_left 2
    exact (Subgroup.card_eq_one).mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  set F := GaloisField 3 (3 * n) with hF
  set ψK := φK.trans (Sec4.projSLEquivPSL F) with hψK
  set θK := aschbacherSolvableCore 3 K with hθK
  set f : T →* PSL2 F := ψK.toMonoidHom.comp
    ((QuotientGroup.mk' θK).comp (Subgroup.inclusion hTK)) with hf
  have hfapp : ∀ t : T, f t = ψK (((Subgroup.inclusion hTK t : K)) : K ⧸ θK) := fun t => rfl
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro t ht
    rw [hfapp, map_eq_one_iff _ ψK.injective, QuotientGroup.eq_one_iff] at ht
    have h1 : (t : G) ∈ T ⊓ inSubgroup (aschbacherSolvableCore 3) K := ⟨t.2, ⟨_, ht, rfl⟩⟩
    rw [hTθK, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  set V := f.range with hV
  have hVe : CFSG.Assembly.IsElemAbelian 2 V := by
    rw [hV, MonoidHom.range_eq_map]
    refine CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 2 f ⊤ ?_
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x _ => Subtype.ext ?_⟩
    · exact congrArg Subtype.val (hTab.1.is_comm.comm (a : T) (b : T))
    · exact hTab.2 x x.2
  have hV4 : Nat.card V = 4 := by
    rw [hV, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hfinj, Subgroup.card_top,
      hT4]
  have hFodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨3, 3 * n, Nat.prime_three, by decide, by omega, GaloisField.card 3 (3 * n) (by omega)⟩
  have hfix : ∀ g (hg : g ∈ Subgroup.normalizer (K : Set G)),
      g ∈ Subgroup.centralizer (T : Set G) →
        ∀ v ∈ V, MulAut.congr ψK (thetaAct K ⟨g, hg⟩) v = v := by
    rintro g hg hgT _ ⟨t, rfl⟩
    rw [hfapp]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 1
    rw [thetaAct_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_coe]
    have h1 := Subgroup.mem_centralizer_iff.mp hgT (t : G) t.2
    change g * (t : G) * g⁻¹ = (t : G)
    rw [← h1, mul_inv_cancel_right]
  have hcT : c ∈ Subgroup.centralizer (T : Set G) := Subgroup.mem_centralizer_iff.mpr fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (le_centralizer_of_mem_thetaComponentsAt hLc (C.T_le_L ht))
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hAe hdA hd1 K hKd
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hAK hcA
  have hS := C.mem_Sub
  rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two] at hS
  obtain ⟨hSle, -, -⟩ := hS
  have hcomm : ∀ s ∈ S, ∀ hs : s ∈ Subgroup.normalizer (K : Set G),
      thetaAct K ⟨s, hs⟩ * thetaAct K ⟨c, hcN⟩ = thetaAct K ⟨c, hcN⟩ * thetaAct K ⟨s, hs⟩ := by
    intro s hsS hs
    have hsT : s ∈ Subgroup.centralizer (T : Set G) := (hSle hsS).2
    have h1 := commute_of_fix_kleinFour hFodd hVe hV4 (hfix s hs hsT) (hfix c hcN hcT)
    rw [← map_mul (MulAut.congr ψK), ← map_mul (MulAut.congr ψK)] at h1
    exact (MulAut.congr ψK).injective h1
  apply C.S_not_theta
  rw [Subgroup.commutator_comm, commutator_le_theta_iff C.S_norm, ← C.S_comm,
    Subgroup.commutator_le]
  intro s hsS y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hs := C.S_norm hsS
  have hck : c ^ k ∈ Subgroup.normalizer (K : Set G) := zpow_mem hcN k
  have hmem : ⁅s, c ^ k⁆ ∈ Subgroup.normalizer (K : Set G) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hs hck) (inv_mem hs)) (inv_mem hck)
  refine (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct hmem).mpr ?_
  have he1 : (⟨⁅s, c ^ k⁆, hmem⟩ : Subgroup.normalizer (K : Set G)) =
      ⁅(⟨s, hs⟩ : Subgroup.normalizer (K : Set G)), ⟨c, hcN⟩ ^ k⁆ := by
    apply Subtype.ext
    simp [commutatorElement_def]
  change thetaAct K ⟨⁅s, c ^ k⁆, hmem⟩ = 1
  rw [he1, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, map_zpow]
  have hc' : Commute (thetaAct K ⟨s, hs⟩) (thetaAct K ⟨c, hcN⟩ ^ k) :=
    (Commute.zpow_right (hcomm s hsS hs) k)
  rw [hc'.eq]
  group

end Certs

end CFSG.RankThree.PartTwo.Sec6.Hering611

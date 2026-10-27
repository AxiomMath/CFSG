module

public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.RankThree.PartTwo.Sec4.Steps439
import CFSG.RankThree.PartTwo.Sec4.Steps444
import CFSG.RankThree.PartTwo.Sec4.StepsBender
import CFSG.RankThree.PartTwo.Sec4.T444.Basic
import CFSG.RankThree.Coprime.ThetaPlaneNormalizesComponent
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.LocalRank.ThetaCoreQuotients
import CFSG.RankThree.PerfectCover.CentralQuotientPrimeSupport
import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item447

open Subgroup CFSG.RankThree.Coprime CFSG.RankThreeEvenClassification.Helpers

section Component

variable {X : Type*} [Group X] [Finite X]

theorem center_component_le_pCore_three (hθ : aschbacherSolvableCore 3 X = ⊥) {K : Subgroup X}
    (hK : IsComponent K) : (center K).map K.subtype ≤ CFSG.pCore 3 X := by
  have hZKE : (center K).map K.subtype ≤ layer X := (map_subtype_le _).trans (le_sSup hK)
  have hZKC : (center K).map K.subtype ≤ centralizer (layer X : Set X) := by
    rw [le_centralizer_iff]
    refine sSup_le fun K' hK' => ?_
    rw [← le_centralizer_iff]
    rcases LocalCores.distinct_components_commute hK hK' with rfl | hcomm
    · rintro _ ⟨z, hz, rfl⟩
      rw [mem_centralizer_iff]
      intro k hk
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨k, hk⟩)
    · exact (map_subtype_le _).trans (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have : (layer X).Characteristic := LocalCores.layer_characteristic
  have hWn : (layer X ⊓ centralizer (layer X : Set X)).Normal := normal_inf_normal _ _
  have hWcomm : IsMulCommutative (layer X ⊓ centralizer (layer X : Set X) : Subgroup X) :=
    ⟨⟨fun x y => Subtype.ext (mem_centralizer_iff.mp x.2.2 y y.2.1).symm⟩⟩
  have hWF : layer X ⊓ centralizer (layer X : Set X) ≤ fittingSubgroup X :=
    LocalCores.fitting_characteristic.2.2 _ hWn inferInstance
  exact (le_inf hZKE hZKC).trans (hWF.trans (fittingSubgroup_le_pCore_three hθ))

theorem inSubgroup_pPrimeCore_centralizer_le_normalizer {p : ℕ} [hp : Fact p.Prime]
    {K B : Subgroup X} (hK : IsComponent K) (hZp : IsPGroup p ((center K).map K.subtype))
    (hpK : p ∣ Nat.card (K ⧸ center K)) (hBp : IsPGroup p B)
    (hBK : B ≤ normalizer (K : Set X)) :
    inSubgroup (pPrimeCore p)
        (centralizer (((center K).map K.subtype ⊔ B : Subgroup X) : Set X)) ≤
      normalizer (K : Set X) := by
  set Z : Subgroup X := (center K).map K.subtype with hZdef
  set W := Z ⊔ B with hWdef
  set D := inSubgroup (pPrimeCore p) (centralizer (W : Set X)) with hDdef
  have hZK : Z ≤ K := map_subtype_le _
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp hZp
  have hpc : p ^ (c + 1) ∣ Nat.card K := by
    rw [card_eq_card_quotient_mul_card_subgroup (center K), pow_succ, mul_comm]
    have hcard : Nat.card (center K) = p ^ c := by
      rw [← hc, hZdef, card_map_of_injective (subtype_injective _)]
    rw [hcard]
    exact mul_dvd_mul_right hpK _
  obtain ⟨Q, hQK, hQp, hQcard, hBQ, hQnormal⟩ := exists_sylow_normalized K B hBp hBK
  have hZQ : Z ≤ Q := hQnormal Z hZK (by
    rw [hZdef, subgroupOf, comap_map_eq_self_of_injective (subtype_injective _)]
    infer_instance) hZp
  have hQZ : ¬ Q ≤ Z := by
    intro h
    have heq := le_antisymm h hZQ
    have h1 := hQcard _ hpc
    rw [heq, hc] at h1
    have h2 := Nat.le_of_dvd (pow_pos hp.out.pos c) h1
    have h3 : p ^ c < p ^ (c + 1) := Nat.pow_lt_pow_right hp.out.one_lt (Nat.lt_succ_self c)
    omega
  obtain ⟨P, hPK, hPp, hPW, hPZ⟩ := exists_pgroup_le_normalizer hQK hQp hBp hBQ hZQ hQZ
  have hPD : P ≤ normalizer (D : Set X) :=
    (normalizes_centralizer_of_normalizes P W hPW).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (pPrimeCore p (centralizer (W : Set X))))
  have hDp : ¬ p ∣ Nat.card D := by
    rw [hDdef, inSubgroup, card_map_of_injective (subtype_injective _)]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp pPrimeCore_coprime_card
  rw [coprime_commutator_centralizer_factorization p hp.out P D hPp hDp hPD]
  refine sup_le ?_ ?_
  · refine commutator_le.mpr fun d _ x hx => ?_
    exact commutator_mem_normalizer_of_mem_component hK (hPK hx) d
  · exact fun d hd => mem_normalizer_of_le_centralizer hK hPK hPZ hd.2

end Component

section Ctx

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G}

theorem three_dvd_card_map_quotient_center {L : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (h3 : 3 ∣ Nat.card L) :
    3 ∣ Nat.card (L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ⧸
      center (L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 G with hNdef
  set ρ := QuotientGroup.mk' N with hρdef
  set K := L.map ρ with hKdef
  have hN3 : ¬ 3 ∣ Nat.card N :=
    (solvable_prime_complement_core_characterization (H := G) Nat.prime_three).2.2.1
  have hK : IsComponent K := isComponent_map_of_mem_thetaComponents Nat.prime_three hL
  have h3K : 3 ∣ Nat.card K := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 3 h3
    have hx3 : (x : G) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]
    have hρx : ρ x ≠ 1 := by
      intro h1
      have hxN : (x : G) ∈ N := by
        rw [← QuotientGroup.ker_mk' N]
        exact h1
      have hdvd := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx] at hdvd
      exact hN3 hdvd
    have hord : orderOf (⟨ρ x, Subgroup.mem_map_of_mem ρ x.2⟩ : K) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [← map_pow, hx3, map_one]) hρx
    have hdvd := orderOf_dvd_natCard (⟨ρ x, Subgroup.mem_map_of_mem ρ x.2⟩ : K)
    rwa [hord] at hdvd
  have : Group.IsPerfect K := hK.1.1
  by_contra hnd
  exact CFSG.RankThree.PerfectCover.perfect_central_quotient_prime_support Nat.prime_three hnd h3K

theorem inf_centralizer_le_normalizer (h45 : Item4_5) (h : Ctx444 G A M) {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (hLM : ¬ L ≤ M) :
    inSubgroup (CFSG.pPrimeCore 3) M ⊓ centralizer (A : Set G) ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := inSubgroup (CFSG.pPrimeCore 3) M with hQdef
  set N := aschbacherSolvableCore 3 G with hNdef
  set ρ := QuotientGroup.mk' N with hρdef
  set K := L.map ρ with hKdef
  set Z : Subgroup (G ⧸ N) := (center K).map K.subtype with hZdef
  set W := Z ⊔ A.map ρ with hWdef
  have hA3 : IsPGroup 3 A := h.isE27.isPGroup
  have hQ3 : ¬ 3 ∣ Nat.card Q := not_three_dvd_card_inSubgroup_pPrimeCore M
  have hAQ : A ≤ normalizer (Q : Set G) := h.le_normalizer_inSubgroup
  have hAL : A ≤ normalizer (L : Set G) :=
    h45 G h.sectionFourHyp A hA3 (Or.inr ⟨h.isE27.1, 3, le_rfl, by rw [h.isE27.2]; norm_num⟩) L hL
  obtain ⟨hNs, -, hN3, -⟩ := solvable_prime_complement_core_characterization (H := G)
    Nat.prime_three
  have hK : IsComponent K := isComponent_map_of_mem_thetaComponents Nat.prime_three hL
  have hθ : aschbacherSolvableCore 3 (G ⧸ N) = ⊥ :=
    (solvable_prime_complement_core_quotient_centralizers Nat.prime_three N hNs hN3).2.2.1
  have hZO : Z ≤ CFSG.pCore 3 (G ⧸ N) := center_component_le_pCore_three hθ hK
  have hZp : IsPGroup 3 Z := CFSG.pCore_isPGroup.to_le hZO
  have h3L : 3 ∣ Nat.card L := by
    by_contra h3
    exact hLM (h.le_of_le_normalizer hAL h3)
  have h3K : 3 ∣ Nat.card (K ⧸ center K) := three_dvd_card_map_quotient_center hL h3L
  have hAK : A.map ρ ≤ normalizer (K : Set (G ⧸ N)) :=
    (map_mono hAL).trans (le_normalizer_map ρ)
  have hcore := inSubgroup_pPrimeCore_centralizer_le_normalizer hK hZp h3K (hA3.map ρ) hAK
  have hS3 : ¬ 3 ∣ Nat.card (Q.map ρ) := fun h' => hQ3 (h'.trans (card_map_dvd Q ρ))
  have hAS : A.map ρ ≤ normalizer ((Q.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
    (map_mono hAQ).trans (le_normalizer_map ρ)
  have hPtop : normalizer ((CFSG.pCore 3 (G ⧸ N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) = ⊤ :=
    normalizer_eq_top_iff.mpr CFSG.pCore_normal
  have hbender : ⁅CFSG.pCore 3 (G ⧸ N), Q.map ρ⁆ = ⊥ :=
    commutator_eq_bot_of_bender_quotient h.isE27.1 (fun y hy hy3 => h.rank3II_4_45 hy hy3) hN3
      hS3 hAS CFSG.pCore_isPGroup (by rw [hPtop]; exact le_top) (by rw [hPtop]; exact le_top)
  have hQZ : Q.map ρ ≤ centralizer (Z : Set (G ⧸ N)) := by
    have hQO : Q.map ρ ≤ centralizer (CFSG.pCore 3 (G ⧸ N) : Set (G ⧸ N)) := by
      rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm, hbender]
    exact hQO.trans (centralizer_le hZO)
  have hCAM : centralizer (A : Set G) ≤ M :=
    (centralizer_le_normalizer _).trans
      ((normalizer_le_gamma le_rfl (by rw [h.isE27.pRank_eq]; norm_num)).trans h.gamma_le)
  have hCWQ : centralizer (W : Set (G ⧸ N)) ≤
      normalizer ((Q.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    intro c hc
    have hcA : c ∈ centralizer ((A.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
      centralizer_le (le_sup_right : A.map ρ ≤ W) hc
    obtain ⟨m, hmC, rfl⟩ := exists_centralizer_preimage_of_pGroup_prime_complement_kernel 3
      Nat.prime_three ρ (QuotientGroup.mk'_surjective N) (by rwa [QuotientGroup.ker_mk']) A hA3
      c hcA
    exact le_normalizer_map ρ ⟨m, le_normalizer_inSubgroup_pPrimeCore M (hCAM hmC), rfl⟩
  have hSW : (Q ⊓ centralizer (A : Set G)).map ρ ≤ centralizer (W : Set (G ⧸ N)) := by
    rw [le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [← le_centralizer_iff]
      exact (map_mono inf_le_left).trans hQZ
    · rw [← le_centralizer_iff]
      rintro _ ⟨g, ⟨-, hgA⟩, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hgA a ha]
  have hle : Q.map ρ ⊓ centralizer (W : Set (G ⧸ N)) ≤
      inSubgroup (CFSG.pPrimeCore 3) (centralizer (W : Set (G ⧸ N))) :=
    le_inSubgroup_pPrimeCore inf_le_right
      (fun c hc => inf_normalizer_le_normalizer_inf ⟨hCWQ hc, le_normalizer hc⟩)
      (fun h' => hS3 (h'.trans (card_dvd_of_le inf_le_left)))
  intro g hg
  rw [mem_normalizer_iff_mk_mem_normalizer Nat.prime_three hL]
  exact hcore (hle ⟨mem_map_of_mem ρ hg.1, hSW (mem_map_of_mem ρ hg)⟩)

end Ctx

end Item447

theorem rank3II_4_47_of (h45 : Item4_5) : Item4_47 := by
  intro G _ _ A M h L hL hLM
  rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
    Nat.prime_three A _ h.isE27.isPGroup (not_three_dvd_card_inSubgroup_pPrimeCore M)
    h.le_normalizer_inSubgroup]
  exact sup_le (h.commutator_le_normalizer h45 _ hL)
    (Item447.inf_centralizer_le_normalizer h45 h hL hLM)

end CFSG.RankThree.PartTwo.Sec4

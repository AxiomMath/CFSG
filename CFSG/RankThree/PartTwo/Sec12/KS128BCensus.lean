module

public import CFSG.RankThree.PartTwo.Sec12.KS128BCensusTools
public import CFSG.RankThree.PartTwo.Sec12.KS128BCensusM12
import CFSG.RankThree.PartTwo.Sec12.Item127
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.Sporadic.J2
public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofCases
public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofStatements

public section

namespace CFSG.RankThree.PartTwo.Sec12.BCensus

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13 (omegaA lBarA)

variable {G : Type} [Group G] [Finite G]

section Steps

omit [Finite G] in
theorem card_center_eq_three {L : Subgroup G}
    (hty : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22) :
    Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := by
  rcases hty with hSL | hA6 | hA7 | hM22
  · exact card_center_eq_three_of_isSLThreePi hSL
  · exact hA6.1
  · exact hA7.1
  · exact hM22.1

theorem c_not_mem_zpowers (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) {A L : Subgroup G}
    {c : G} (h : Sec12StdBar G A c L) (hAE : A ∈ partTwoE G)
    (hAL9 : Nat.card (A ⊓ L : Subgroup G) = 9) {b : G} (hb : Subgroup.zpowers b ∈ omegaA A) :
    c ∉ Subgroup.zpowers b := by
  intro hcb
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ hAE
  obtain ⟨-, hb3, -⟩ := Sec13.zpowers_mem_omegaA_iff.mp hb
  have hc3 : Nat.card (Subgroup.zpowers c) = 3 :=
    Sec13.card_zpowers_of_pow_three (hAF.1.2 c h.mem_A) h.ne_one
  have heq : Subgroup.zpowers c = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcb) (by rw [hb3, hc3])
  have hc : Subgroup.zpowers c ∈ omegaA A := by rw [heq]; exact hb
  obtain ⟨K, hK⟩ := exists_mem_lA422 h422 h45 h.toPartTwoStanding hAF hAE.2.1 hc
  have hsc : A ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers c := by
    have h1 := hK.2.2.1
    rw [Sec13.sectionCentralizer_eq_inf hK.2.1] at h1
    exact SetLike.coe_injective h1
  have hne : L ≠ K := by
    rintro rfl
    have h1 := h.card_B
    rw [hsc, hc3] at h1
    norm_num at h1
  have hle : A ⊓ L ≤ Subgroup.zpowers c := by
    intro x hx
    rw [← hsc]
    exact ⟨hx.1, mem_thetaQuotCentralizer_of_ne h.mem_thetaComponentsAt hK.1 hne hx.2
      (hK.2.1 hx.1)⟩
  have h1 := Subgroup.card_le_of_le hle
  rw [hAL9, hc3] at h1
  norm_num at h1

theorem inf_le_residual {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L) {b : G}
    (hbA : b ∈ A) (hbB : b ∈ Sec4.thetaQuotCentralizer L) :
    A ⊓ L ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.isE27.1
  have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  intro x hx
  have hxb : x * b = b * x := congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx.1⟩ ⟨b, hbA⟩)
  exact mem_residual_of_pow_three hLq.1 (k := 1) (by simpa using hAe.2 b hbA) hbB
    ⟨hx.2, Subgroup.mem_centralizer_singleton_iff.mpr hxb⟩ (j := 1)
    (by simpa using hAe.2 x hx.1)

theorem residual_le (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hAE : A ∈ partTwoE G) (hAL9 : Nat.card (A ⊓ L : Subgroup G) = 9) {b : G} (hbA : b ∈ A)
    (hb1 : b ≠ 1) (hbB : b ∈ Sec4.thetaQuotCentralizer L) {K : Subgroup G}
    (hK : K ∈ lA422 A b) :
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ K := by
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ hAE
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hJdef
  have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hLeq := Proof128.eq_residual_sup_theta hLq.1 (k := 1)
    (by simpa using h.isE27.1.2 b hbA) hbB
  have hJL : J ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  obtain ⟨eJ⟩ := Sec13.nonempty_quotTheta_equiv_of_eq_sup hJL hLeq
  have hJq : IsQuasisimple (J ⧸ aschbacherSolvableCore 3 J) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ.symm hLq
  have hG4b : SectionFourHyp (Subgroup.centralizer ({b} : Set G)) :=
    (Proof128.centralizer_setup h.toPartTwoStanding hAF hAE.2.1 hbA hb1).1
  obtain ⟨X, hX, hJX⟩ := Sec14.exists_mem_thetaComponentsAt_le_residual h48 hG4b h.isE27
    h.mem_A hbA h.ne_one h.mem_thetaComponentsAt hJq
  have hALJ := inf_le_residual h hbA hbB
  by_contra hJK
  have hXK : X ≠ K := fun hXK => hJK (hXK ▸ hJX)
  have hsc := hK.2.2.1
  rw [Sec13.sectionCentralizer_eq_inf hK.2.1] at hsc
  have hle : A ⊓ L ≤ Subgroup.zpowers b := by
    intro x hx
    have hmem : x ∈ ((A ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) :=
      ⟨hx.1, mem_thetaQuotCentralizer_of_ne hX hK.1 hXK (hJX (hALJ hx)) (hK.2.1 hx.1)⟩
    rw [hsc] at hmem
    exact hmem
  have h1 := Subgroup.card_le_of_le hle
  rw [hAL9, Sec13.card_zpowers_of_pow_three (h.isE27.1.2 b hbA) hb1] at h1
  norm_num at h1

theorem isTripleCover_of_hj (h415 : Sec4.Item4_15)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (hK2 : KFacts.KS12NormalizerMoves)
    {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L) (hAE : A ∈ partTwoE G)
    (hty : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1) (hbB : b ∈ Sec4.thetaQuotCentralizer L)
    {K : Subgroup G} (hK : K ∈ lA422 A b)
    (hJK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ K)
    (hcJ : c ∈ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)))
    (hφ : Nonempty (lBarA b K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2))
    (hS3 : Nonempty (Sec4.autIn K A ≃* Equiv.Perm (Fin 3))) :
    Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) := by
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ hAE
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have h27 : Nat.card A = 27 := hAE.2.1
  have hcA := h.mem_A
  have hc1 := h.ne_one
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK.1
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hJdef
  have hcK : c ∈ K := hJK hcJ
  obtain ⟨hJ2p, -⟩ := Sec13.isPerfect_center_of_isSimpleGroup
    CFSG.Sporadic.J2.isSimpleGroup_J2 (by rw [KFacts.KS14.card_nativeJ2]; norm_num)
  obtain ⟨φ⟩ := hφ
  have hAH := Proof128.le_normalizer_zpowers_of_isElemAbelian hAe hbA
  have hKθ := Proof128.nonempty_thetaQuot_equiv hAe hK.1 hK.2.1 hAH hJ2p φ
  have h9 := Proof128.card_inf_eq_nine hAe h27 hK.1 hK.2.1 hAH hJ2p φ
  obtain ⟨n, hnK, hnA, ⟨k, hn3⟩, hnc, hnmove⟩ := exists_threeElement_of_perm3 h45 hK2 h hty hS3
  have hSyl := Proof128.exists_sylow_le_centralizer hAe hKθ h9 hcA hcK hnK hnA hn3 hnc hnmove
  obtain ⟨hq, htc, -, -⟩ := Sec13.residual_facts h415 hKθ hcK hc1 hSyl
  set I := inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G)) with hIdef
  have hG4c : SectionFourHyp (Subgroup.centralizer ({c} : Set G)) :=
    (Proof128.centralizer_setup h.toPartTwoStanding hAF h27 hcA hc1).1
  obtain ⟨L₀, hL₀, hIL₀⟩ :=
    Sec14.exists_mem_thetaComponentsAt_le_residual h48 hG4c h.isE27 hbA hcA hb1 hK.1 hq
  have hJp := Sec6.isPerfect_inSubgroup_perfectResidual
    (L ⊓ Subgroup.centralizer ({b} : Set G))
  have hIp := Sec6.isPerfect_inSubgroup_perfectResidual
    (K ⊓ Subgroup.centralizer ({c} : Set G))
  have hJL : J ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hJI : J ≤ I :=
    Sec6.le_inSubgroup_perfectResidual_of_isPerfect hJp (le_inf hJK (hJL.trans hLc))
  have hJ1 : J ≠ ⊥ := fun h0 => hc1 (by rw [h0] at hcJ; exact (Subgroup.mem_bot).mp hcJ)
  have hL₀L : L₀ = L :=
    PartOne.EmbeddingFixedResidual.eq_of_perfect_le_of_mem_thetaComponentsAt Nat.prime_three
      hL₀ h.mem_thetaComponentsAt hJ1 hJp (hJI.trans hIL₀) hJL
  have hIJ : I ≤ J := Sec6.le_inSubgroup_perfectResidual_of_isPerfect hIp
    (le_inf (hL₀L ▸ hIL₀) ((Subgroup.map_subtype_le _).trans (inf_le_left.trans hKb)))
  have hIJeq : I = J := le_antisymm hIJ hJI
  have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hLeq := Proof128.eq_residual_sup_theta hLq.1 (k := 1) (by simpa using hAe.2 b hbA) hbB
  obtain ⟨eJ⟩ := Sec13.nonempty_quotTheta_equiv_of_eq_sup hJL hLeq
  exact Sec13.isTripleCover_of_mulEquiv
    ((Sec14.quotThetaEquiv (MulEquiv.subgroupCongr hIJeq)).trans eJ) htc

theorem false_of_m12
    (h45 : Sec4.Item4_5)
    (hK2 : KFacts.KS12NormalizerMoves) {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hAE : A ∈ partTwoE G)
    (hty : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {b : G} (hbA : b ∈ A) {K : Subgroup G} (hK : K ∈ lA422 A b)
    (hJK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ K)
    (hcJ : c ∈ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)))
    (hφ : Nonempty (lBarA b K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12))
    (hS3 : Nonempty (Sec4.autIn K A ≃* Equiv.Perm (Fin 3))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ hAE
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have h27 : Nat.card A = 27 := hAE.2.1
  have hcA := h.mem_A
  have hc1 := h.ne_one
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hJdef
  have hcK : c ∈ K := hJK hcJ
  obtain ⟨φ⟩ := hφ
  have hM12p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.M12 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num)).1
  have hAH := Proof128.le_normalizer_zpowers_of_isElemAbelian hAe hbA
  obtain ⟨ψ⟩ := Proof128.nonempty_thetaQuot_equiv hAe hK.1 hK.2.1 hAH hM12p φ
  have h9 := Proof128.card_inf_eq_nine hAe h27 hK.1 hK.2.1 hAH hM12p φ
  obtain ⟨n, hnK, hnA, ⟨k, hn3⟩, hnc, hnmove⟩ := exists_threeElement_of_perm3 h45 hK2 h hty hS3
  have h81 : ¬ 81 ∣ Nat.card (K ⧸ aschbacherSolvableCore 3 K) := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.Sporadic.Mathieu.card_M12]
    norm_num
  have hSyl := exists_sylow_le_centralizer_of_not_dvd hAe h81 h9 hcA hcK hnK hnA hn3 hnc hnmove
  obtain ⟨hz1, P, hzP, hPz⟩ := Sec13.bar_facts_of_central (Λ := K) (z := ⟨c, hcK⟩)
    (fun h1 => hc1 (congrArg Subtype.val h1)) hSyl
  set f := ψ.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) with hf
  have hw1 : f ⟨c, hcK⟩ ≠ 1 := fun h1 => hz1 ((MulEquiv.map_eq_one_iff ψ).mp h1)
  have hψs : Function.Surjective ψ.toMonoidHom := ψ.surjective
  let P' := P.mapSurjective hψs
  have hP'eq : (P' : Subgroup _) = (P : Subgroup _).map ψ.toMonoidHom := rfl
  have hwP : f ⟨c, hcK⟩ ∈ (P' : Subgroup _) := by
    rw [hP'eq]
    exact Subgroup.mem_map_of_mem _ hzP
  have hPw : (P' : Subgroup _) ≤ Subgroup.centralizer ({f ⟨c, hcK⟩} : Set _) := by
    rw [hP'eq]
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hPz hq)
    change ψ q * ψ (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩) =
      ψ (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩) * ψ q
    rw [← map_mul, ← map_mul, h1]
  have hJp := Sec6.isPerfect_inSubgroup_perfectResidual
    (L ⊓ Subgroup.centralizer ({b} : Set G))
  have hJsub : Group.IsPerfect (J.subgroupOf K) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJK).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hHp : Group.IsPerfect ((J.subgroupOf K).map f) := Group.IsPerfect.map f
  have hHw : (J.subgroupOf K).map f ≤ Subgroup.centralizer ({f ⟨c, hcK⟩} : Set _) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have huL : (u : G) ∈ L :=
      ((Subgroup.map_subtype_le _ : J ≤ L ⊓ _) (Subgroup.mem_subgroupOf.mp hu)).1
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLc huL)
  have hH := eq_bot_of_isPerfect_le_centralizer hw1 P' hwP hPw hHp hHw
  have hmem : f ⟨c, hcK⟩ ∈ (J.subgroupOf K).map f :=
    Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr hcJ)
  rw [hH, Subgroup.mem_bot] at hmem
  exact hw1 hmem

end Steps

section Cases

theorem hj_of_mem_lA422_of_mem
    (h422 : Sec4.Item4_22)
    (h423 : Sec4.Item4_23) (h1134 : Sec11.Item1134E27N) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (hK2 : KFacts.KS12NormalizerMoves) {A L : Subgroup G} {c : G}
    (h : Sec12StdBar G A c L) (hAE : A ∈ partTwoE G) (hAT : A ∉ partTwoT G)
    (hty : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {b : G} (hb : Subgroup.zpowers b ∈ omegaA A) (hbB : b ∈ Sec4.thetaQuotCentralizer L)
    {K : Subgroup G} (hK : K ∈ lA422 A b) :
    Nonempty (lBarA b K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2) ∧
      Nonempty (Sec4.autIn K A ≃* Equiv.Perm (Fin 3)) := by
  have hFE := h.partTwoF_eq
  have hAF : A ∈ partTwoF G := hFE ▸ hAE
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have h27 : Nat.card A = 27 := hAE.2.1
  obtain ⟨hbA, hb3, -⟩ := Sec13.zpowers_mem_omegaA_iff.mp hb
  have hb1 : b ≠ 1 := ne_one_of_card_zpowers_eq_three hb3
  have hcA := h.mem_A
  have hc1 := h.ne_one
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcB : c ∈ Sec4.thetaQuotCentralizer L := mem_thetaQuotCentralizer_of_central h.mem_L hLc
  have hAL9 := card_inf_eq_nine_bar h.isE27 hcA hc1 h.mem_L hLc (card_center_eq_three hty)
    h.card_B h.sup_eq
  have hcb := c_not_mem_zpowers h422 h45 h hAE hAL9 hb
  have hW := normalizer_le_of_sec12StdBar_of_list h45 hK2 h hty
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK.1
  have hALJ := inf_le_residual h hbA hbB
  have hJK := residual_le h48 h hAE hAL9 hbA hb1 hbB hK
  have hcJ := hALJ ⟨hcA, h.mem_L⟩
  have hcK : c ∈ K := hJK hcJ
  have hT : ∀ σ ∈ Sec4.autIn K A, σ ^ 3 = 1 → σ ∈ transvectionGroup A ⟨c, hcA⟩ :=
    fun σ hσ h3 => Proof128.mem_transvectionGroup_of_mem_wStar h45 hK2 h hty
      (Sec13.Holds134.autIn_le_wStar K hσ) (k := 1) (by simpa using h3)
  rcases Proof128.cases423 h423 h.toPartTwoStanding hAF h27 hbA hb1 hK with
    ⟨σ, hσ4⟩ | ⟨-, -, x, hxA, -, hx3⟩ | ⟨h3, h9⟩ | ⟨hSL2, -⟩ | ⟨hMJ, hS3⟩ |
      ⟨x, hxA, hx1, hk⟩
  ·
    exact absurd hσ4 (Proof128.not_orderOf_eq_four hAe h27 hbA hcA hb1 hc1 hcb hKb hW σ)
  ·
    exfalso
    have hBeq : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c ⊔ Subgroup.zpowers b :=
      (Subgroup.eq_of_le_of_card_ge
        (sup_le (Subgroup.zpowers_le.mpr (⟨hcA, hcB⟩ : c ∈ A ⊓ Sec4.thetaQuotCentralizer L))
          (Subgroup.zpowers_le.mpr (⟨hbA, hbB⟩ : b ∈ A ⊓ Sec4.thetaQuotCentralizer L)))
        (by rw [h.card_B, Proof128.card_zpowers_sup_eq_nine hAe hbA hcA hb1 hc1 hcb])).symm
    have hAeq : A = Subgroup.zpowers b ⊔ (A ⊓ L) := by
      refine le_antisymm (fun y hy => ?_) (sup_le (Subgroup.zpowers_le.mpr hbA) inf_le_left)
      rw [← h.sup_eq, hBeq] at hy
      exact (sup_le (sup_le ((Subgroup.zpowers_le.mpr (⟨hcA, h.mem_L⟩ : c ∈ A ⊓ L)).trans
        le_sup_right) le_sup_left) le_sup_right) hy
    exact false_of_inducesTypeOn hAe hbA hK.1 hK.2.1 inf_le_left (hALJ.trans hJK) hAeq hxA hx3
  ·
    exfalso
    have hle : Sec4.autIn K A ≤ transvectionGroup A ⟨c, hcA⟩ := fun σ hσ => hT σ hσ (h3 σ hσ)
    have hfix : ∀ σ ∈ Sec4.autIn K A, σ ⟨b, hbA⟩ = ⟨b, hbA⟩ := by
      intro σ hσ
      obtain ⟨g, hgN, hgK, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe]
      have hgb : g * b = b * g := Subgroup.mem_centralizer_singleton_iff.mp (hKb hgK)
      rw [hgb, mul_inv_cancel_right]
    have := Proof128.card_le_three_of_le_transvectionGroup hAe h27 hbA hcA hb1 hc1 hcb hle hfix
    omega
  ·
    exact (Proof128.false_of_isSLThreePiTwo hAe h27 hbA hcA hb1 hc1 hcb hK.1 hK.2.1 hcK
      hSL2).elim
  ·
    rcases hMJ with hM | hJ
    · exact (false_of_m12 h45 hK2 h hAE hty hbA hK hJK hcJ hM hS3).elim
    · exact ⟨hJ, hS3⟩
  ·
    exact absurd hk
      (Proof128.not_inducesStdKind h1134 h.toPartTwoStanding hAF hAT hFE h27 hbA hb1 hK hxA hx1)

end Cases

end CFSG.RankThree.PartTwo.Sec12.BCensus

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem ks128BCensus_of
    (h422 : Sec4.Item4_22) (h423 : Sec4.Item4_23) (h1134 : Sec11.Item1134E27N)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hK2 : KFacts.KS12NormalizerMoves) : KS128BCensus := by
  intro G _ _ A c L h hAE hAT hty b hb hbB
  have hAF : A ∈ partTwoF G := h.partTwoF_eq ▸ hAE
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  obtain ⟨hbA, hb3, -⟩ := Sec13.zpowers_mem_omegaA_iff.mp hb
  have hb1 : b ≠ 1 := ne_one_of_card_zpowers_eq_three hb3
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hAL9 := card_inf_eq_nine_bar h.isE27 h.mem_A h.ne_one h.mem_L hLc
    (BCensus.card_center_eq_three hty) h.card_B h.sup_eq
  have hcJ := BCensus.inf_le_residual h hbA hbB ⟨h.mem_A, h.mem_L⟩
  have hAH := Proof128.le_normalizer_zpowers_of_isElemAbelian hAe hbA
  obtain ⟨hJ2p, -⟩ := Sec13.isPerfect_center_of_isSimpleGroup
    CFSG.Sporadic.J2.isSimpleGroup_J2 (by rw [KFacts.KS14.card_nativeJ2]; norm_num)
  refine ⟨?_, fun K hK => ?_⟩
  · obtain ⟨K, hK⟩ := exists_mem_lA422 h422 h45 h.toPartTwoStanding hAF hAE.2.1 hb
    obtain ⟨hφ, hS3⟩ :=
      BCensus.hj_of_mem_lA422_of_mem h422 h423 h1134 h45 h48 hK2 h hAE hAT hty hb hbB hK
    exact BCensus.isTripleCover_of_hj h415 h45 h48 hK2 h hAE hty hbA hb1 hbB hK
      (BCensus.residual_le h48 h hAE hAL9 hbA hb1 hbB hK) hcJ hφ hS3
  · obtain ⟨⟨φ⟩, -⟩ :=
      BCensus.hj_of_mem_lA422_of_mem h422 h423 h1134 h45 h48 hK2 h hAE hAT hty hb hbB hK
    exact Proof128.nonempty_thetaQuot_equiv hAe hK.1 hK.2.1 hAH hJ2p φ

end CFSG.RankThree.PartTwo.Sec12

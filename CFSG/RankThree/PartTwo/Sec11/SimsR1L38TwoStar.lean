module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1L38TwoStarA

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.L38TwoStar

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory
open scoped commutatorElement

section Certified


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem pCore_d_inf_thetaQuotCentralizer_le (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) :
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer ({d} : Set G)) ⊓ Sec4.thetaQuotCentralizer L ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set P := inSubgroup (CFSG.pCore 2) (C ⊓ Subgroup.centralizer ({d} : Set G)) with hP
  have hLC : L ≤ C := TwoStarProof.le_centralizer_of_config h
  have hCL : C ≤ Subgroup.normalizer (L : Set G) :=
    TwoStarProof.centralizer_le_normalizer_of_config h45 h hT
  have hdL := TwoStarProof.d_mem_L h
  have hd3 : d ^ 3 = 1 := h.mem_partTwoF.1.2 d h.d_mem
  have hP2 : IsPGroup 2 P := SteinbergBY.isPGroup_inSubgroup_pCore 2 _
  have hPC : P ≤ C ⊓ Subgroup.centralizer ({d} : Set G) := SteinbergBY.inSubgroup_pCore_le 2 _
  refine TwoStarProof.le_theta_of_commutator_mem hLC hCL hdL hd3 (hP2.to_le inf_le_left)
    (inf_le_left.trans hPC) (fun x hx => SteinbergBY.mem_normalizer_inf
      (SteinbergBY.le_normalizer_inSubgroup_pCore 2 _ hx)
      (mem_normalizer_thetaQuotCentralizer (hCL hx.1))) ?_
  intro q hq l hl
  have hqN : q ∈ Subgroup.normalizer (L : Set G) := hCL (hPC hq.1).1
  exact TwoStarProof.theta_L_le h45 h hT (TwoStarProof.commutator_mem_theta_of_autHom_eq_one hqN
    (autHom_eq_one_of_mem_thetaQuotCentralizer hqN hq.2) hl)

theorem commutator_pCore_d_le_theta (hAut : SimsR1L38AutFacts) (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) (hL : IsL3Eight L) :
    ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer ({d} : Set G)), A⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
  have hAe := h.mem_partTwoF.1
  have hAc := comm_of_mem_A h
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set N := Subgroup.normalizer (L : Set G) with hN
  set P := inSubgroup (CFSG.pCore 2) (C ⊓ Subgroup.centralizer ({d} : Set G)) with hP
  set ψ := TwoStarProof.autHom L with hψ
  have hCL : C ≤ N := TwoStarProof.centralizer_le_normalizer_of_config h45 h hT
  have hdL := TwoStarProof.d_mem_L h
  have hd3 : d ^ 3 = 1 := hAe.2 d h.d_mem
  have hAC : A ≤ C := fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c h.mem_A)
  have hP2 : IsPGroup 2 P := SteinbergBY.isPGroup_inSubgroup_pCore 2 _
  have hPC : P ≤ C ⊓ Subgroup.centralizer ({d} : Set G) := SteinbergBY.inSubgroup_pCore_le 2 _
  have hPN : P ≤ N := (hPC.trans inf_le_left).trans hCL
  have hAN : A ≤ Subgroup.normalizer (P : Set G) := fun u hu =>
    SteinbergBY.le_normalizer_inSubgroup_pCore 2 _
      ⟨hAC hu, Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu d h.d_mem)⟩
  set Qh : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)) := (P.subgroupOf N).map ψ with hQh
  have hQh2 : IsPGroup 2 Qh :=
    (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm).map ψ
  have hx3 : ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ^ 3 = 1 := by
    have : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  have hx1 : ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ≠ 1 := by
    intro h1
    have h2 : (⟨d, hdL⟩ : L) ∈ aschbacherSolvableCore 3 L := (QuotientGroup.eq_one_iff _).mp h1
    have hd1 : d = 1 := eq_one_of_mem_inSubgroup_theta ⟨_, h2, rfl⟩ hd3
    exact h.not_mem_zpowers (hd1 ▸ Subgroup.one_mem _)
  have hord : orderOf ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = 3 :=
    orderOf_eq_prime hx3 hx1
  have hfix : ∀ τ ∈ Qh, τ ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
      ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := by
    rintro _ ⟨q', hq', rfl⟩
    have hq'P : (q' : G) ∈ P := Subgroup.mem_subgroupOf.mp hq'
    have hqd : (q' : G) * d = d * q' := Subgroup.mem_centralizer_singleton_iff.mp (hPC hq'P).2
    show Sec4.thetaQuotMulAut L (Sec4.compAction L q')
      ((⟨d, hdL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = _
    rw [Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    change (q' : G) * d * (q' : G)⁻¹ = d
    rw [hqd]
    group
  have hcyc : IsCyclic Qh :=
    (hAut (L ⧸ aschbacherSolvableCore 3 L) hL).1 _ hord Qh hQh2 hfix
  rw [Subgroup.commutator_le]
  intro q hq α hα
  have hqN : q ∈ N := hPN hq
  have hαN : α ∈ N := hCL (hAC hα)
  have hα3 : α ^ 3 = 1 := hAe.2 α hα
  have hrP : ⁅q, α⁆ ∈ P := by
    have h1 : α * q⁻¹ * α⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hAN hα) q⁻¹).mp (Subgroup.inv_mem _ hq)
    have e : ⁅q, α⁆ = q * (α * q⁻¹ * α⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hq h1
  have hrN : ⁅q, α⁆ ∈ N := hPN hrP
  have hαnorm : (⟨α, hαN⟩ : N) ∈ Subgroup.normalizer ((P.subgroupOf N : Subgroup N) : Set N) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp (hAN hα) (x : G))
  have hgnorm : ψ ⟨α, hαN⟩ ∈
      Subgroup.normalizer (Qh : Set (MulAut (L ⧸ aschbacherSolvableCore 3 L))) :=
    Subgroup.le_normalizer_map ψ ⟨⟨α, hαN⟩, hαnorm, rfl⟩
  have hg3 : ψ ⟨α, hαN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨α, hαN⟩ : N) ^ 3 = 1 := Subtype.ext (by simpa using hα3)
    rw [this, map_one]
  have hgcent := mem_centralizer_of_pow_three_of_isCyclic hcyc hQh2 hgnorm hg3
  have hψq : ψ ⟨q, hqN⟩ ∈ Qh := ⟨⟨q, hqN⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
  have hrK : ⁅q, α⁆ ∈ Sec4.thetaQuotCentralizer L := by
    refine mem_thetaQuotCentralizer_of_autHom_eq_one hrN ?_
    have hcomm : (⟨⁅q, α⁆, hrN⟩ : N) = ⁅(⟨q, hqN⟩ : N), (⟨α, hαN⟩ : N)⁆ := rfl
    rw [hcomm, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp hgcent _ hψq
  exact pCore_d_inf_thetaQuotCentralizer_le h45 h hT ⟨hrP, hrK⟩

theorem mem_theta_of_mem_pCore_all (hAut : SimsR1L38AutFacts) (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) (hL : IsL3Eight L) {u : G}
    (hu : ∀ y ∈ A, y ∉ Subgroup.zpowers c →
      u ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G))) :
    u ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
  have hAe := h.mem_partTwoF.1
  have hAc := comm_of_mem_A h
  have : IsElementaryAbelian 3 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hAe
  have h27 : Nat.card A = 3 ^ 3 := by rw [h.card_eq]; norm_num
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set N := Subgroup.normalizer (L : Set G) with hN
  set ψ := TwoStarProof.autHom L with hψ
  have hCL : C ≤ N := TwoStarProof.centralizer_le_normalizer_of_config h45 h hT
  have hLC : L ≤ C := TwoStarProof.le_centralizer_of_config h
  have hdA := h.d_mem
  have hdL := TwoStarProof.d_mem_L h
  have hAC : A ≤ C := fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c h.mem_A)
  have hcd9 := SteinbergBY.card_zpowers_sup_zpowers Nat.prime_three h27 h.mem_A h.ne_one hdA
    h.not_mem_zpowers
  have haV : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    intro ha
    have hle : A ≤ Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
      rw [← h.closure_eq, Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · exact ha
    have := Subgroup.card_le_of_le hle
    rw [h.card_eq, hcd9] at this
    norm_num at this
  have hud := hu d hdA h.not_mem_zpowers
  have hua := hu a h.a_mem fun hac => haV (Subgroup.mem_sup_left hac)
  have huC : u ∈ C ⊓ Subgroup.centralizer ({d} : Set G) :=
    SteinbergBY.inSubgroup_pCore_le 2 _ hud
  have huN : u ∈ N := hCL huC.1
  have haN : a ∈ N := hCL (hAC h.a_mem)
  have ha3 : a ^ 3 = 1 := hAe.2 a h.a_mem
  set σ := ψ ⟨a, haN⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨a, haN⟩ : N) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
    rw [this, map_one]
  have hnot : σ ∉ (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range :=
    TwoStarProof.autHom_not_inner_of_not_mem h45 h hT h.a_mem haV haN
  have hne : σ ≠ 1 := fun h1 => hnot (by rw [h1]; exact Subgroup.one_mem _)
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hne
  have hτ2 : ∃ k : ℕ, ψ ⟨u, huN⟩ ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := SteinbergBY.isPGroup_inSubgroup_pCore 2
      (C ⊓ Subgroup.centralizer ({d} : Set G)) ⟨u, hud⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨u, huN⟩ : N) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hτfix : ∀ x ∈ Sec11.fixedSub σ, ψ ⟨u, huN⟩ x = x := by
    intro x hx
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨z, hzw, hza⟩ := exists_lift_of_fixed haN ha3 w hx
    have hzC : (z : G) ∈ C ⊓ Subgroup.centralizer ({a} : Set G) :=
      ⟨hLC z.2, Subgroup.mem_centralizer_singleton_iff.mpr hza.symm⟩
    have hrP : u * (z : G) * u⁻¹ * (z : G)⁻¹ ∈
        inSubgroup (CFSG.pCore 2) (C ⊓ Subgroup.centralizer ({a} : Set G)) := by
      have h1 := (Subgroup.mem_normalizer_iff.mp
        (SteinbergBY.le_normalizer_inSubgroup_pCore 2 _ hzC) u⁻¹).mp (Subgroup.inv_mem _ hua)
      have e : u * (z : G) * u⁻¹ * (z : G)⁻¹ = u * ((z : G) * u⁻¹ * (z : G)⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hua h1
    have hrL : u * (z : G) * u⁻¹ * (z : G)⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp huN z).mp z.2) (L.inv_mem z.2)
    obtain ⟨s, hs, hse⟩ := mem_theta_of_mem_pCore_inf hAut h45 h hT hL h.a_mem haV hrP hrL
    rw [← hzw]
    show Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨u, huN⟩) (z : L ⧸ aschbacherSolvableCore 3 L) =
      (z : L ⧸ aschbacherSolvableCore 3 L)
    rw [Sec4.thetaQuotMulAut_mk]
    have hsz : (Sec4.compAction L ⟨u, huN⟩ z : L) = s * z := by
      apply Subtype.ext
      change u * (z : G) * u⁻¹ = (s : G) * z
      have hse' : (s : G) = u * (z : G) * u⁻¹ * (z : G)⁻¹ := hse
      rw [hse']
      group
    rw [hsz, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff s).mpr hs, one_mul]
  have hψu : ψ ⟨u, huN⟩ = 1 :=
    (hAut (L ⧸ aschbacherSolvableCore 3 L) hL).2.2 σ _ hord hnot hτ2 hτfix
  exact pCore_d_inf_thetaQuotCentralizer_le h45 h hT
    ⟨hud, mem_thetaQuotCentralizer_of_autHom_eq_one huN hψu⟩

end Certified

end CFSG.RankThree.PartTwo.Sec11.SimsR1.L38TwoStar

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta
open CFSG.RankThree.GroupTheory
open scoped commutatorElement

section Certified


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem twoStarConditionAt_c_L38_of_lf (hAut : SimsR1L38AutFacts) (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) (hR1 : ResidueR1 G A c a d)
    (hL : IsL3Eight L) (hLF : LFAt L c) : TwoStarConditionAt A c := by
  have _ := hR1
  have hAe := h.mem_partTwoF.1
  have : IsElementaryAbelian 3 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hAe
  have h27 : Nat.card A = 3 ^ 3 := by rw [h.card_eq]; norm_num
  have hdA := h.d_mem
  have hdL := TwoStarProof.d_mem_L h
  have hclle : ∀ H : Subgroup G, c ∈ H → d ∈ H → a ∈ H → A ≤ H := by
    intro H hc hd ha
    rw [← h.closure_eq, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hc
    · exact hd
    · exact ha
  have hd1 : d ≠ 1 := fun h1 => h.not_mem_zpowers (h1 ▸ Subgroup.one_mem _)
  have hcd9 := SteinbergBY.card_zpowers_sup_zpowers Nat.prime_three h27 h.mem_A h.ne_one hdA
    h.not_mem_zpowers
  have had : a ∉ Subgroup.zpowers d := by
    intro had
    have hle := hclle (Subgroup.zpowers c ⊔ Subgroup.zpowers d) (Subgroup.mem_sup_left
      (Subgroup.mem_zpowers c)) (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
      (Subgroup.mem_sup_right had)
    have := Subgroup.card_le_of_le hle
    rw [h.card_eq, hcd9] at this
    norm_num at this
  have hV9 := SteinbergBY.card_zpowers_sup_zpowers Nat.prime_three h27 hdA hd1 h.a_mem had
  have hVA : Subgroup.zpowers d ⊔ Subgroup.zpowers a ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hdA) (Subgroup.zpowers_le.mpr h.a_mem)
  have hcV : c ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers a := by
    intro hc
    have hle := hclle _ hc (Subgroup.mem_sup_left (Subgroup.mem_zpowers d))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    have := Subgroup.card_le_of_le hle
    rw [h.card_eq, hV9] at this
    norm_num at this
  refine TwoStarProof.twoStarConditionAt_of_theta hAe h.card_eq h.mem_A h.ne_one
    (by rw [hV9]; norm_num) hVA hcV hdA h.not_mem_zpowers ?_ ?_ ?_
  ·
    intro v hv
    have := hLF (Subgroup.commutator_mem_commutator hdL hv)
    rwa [commutatorElement_def] at this
  ·
    intro y hyA hyc
    by_cases hyB : y ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d
    · have hplane := TwoStarProof.zpowers_sup_eq_of_mem h.card_eq h.mem_A h.ne_one hdA
        h.not_mem_zpowers hyA hyc hyB
      have hCy : Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) =
          Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) := by
        rw [← CFSG.RankThreeEvenClassification.Helpers.centralizer_join_zpowers,
          ← CFSG.RankThreeEvenClassification.Helpers.centralizer_join_zpowers, hplane]
      rw [hCy]
      exact L38TwoStar.commutator_pCore_d_le_theta hAut h45 h hT hL
    · exact L38TwoStar.commutator_pCore_le_theta_of_outer hAut h45 h hT hL hyA hyB
  ·
    intro u hu
    exact L38TwoStar.mem_theta_of_mem_pCore_all hAut h45 h hT hL hu

end Certified

end CFSG.RankThree.PartTwo.Sec11.SimsR1

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta

section Certified


theorem residueR1TwoStarCL38_of_lf (hAut : SimsR1L38AutFacts) (h45 : Sec4.Item4_5)
    (hLF : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
      (R Y : Subgroup G) (d : G), ResidueConfig G A c L a R Y d → A ∉ partTwoT G →
        IsL3Eight L → LFAt L c) : ResidueR1TwoStarCL38 := by
  intro G _ _ A c L a R Y d h hT hR1 hL
  exact SimsR1.twoStarConditionAt_c_L38_of_lf hAut h45 h hT hR1 hL (hLF G A c L a R Y d h hT hL)

end Certified

end CFSG.RankThree.PartTwo.Sec11

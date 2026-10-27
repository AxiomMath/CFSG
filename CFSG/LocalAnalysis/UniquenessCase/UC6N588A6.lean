module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588A5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.ABGLocalTools
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

namespace N588A

theorem isSimpleGroup_of_center_eq_bot {Q : Type} [Group Q] (hQ : IsSimpleGroup (Q ⧸ center Q))
    (hc : center Q = ⊥) : IsSimpleGroup Q :=
  ((QuotientGroup.quotientBot (G := Q)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hc.symm)).isSimpleGroup

theorem mul_comm_of_isCyclic {X : Type} [Group X] {T : Subgroup X} (hT : IsCyclic T) {x y : X}
    (hx : x ∈ T) (hy : y ∈ T) : x * y = y * x := by
  obtain ⟨g, hg⟩ := hT.exists_generator
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  have e := (Commute.zpow_zpow_self g i k).eq
  rw [hi, hk] at e
  exact congrArg Subtype.val e

namespace Hyp

variable {G : Type} [Group G] [Finite G] {p : ℕ} {S Z : Subgroup G}

theorem inf_centralizer_eq_bot {J : Subgroup G} (hc : center J = ⊥) :
    J ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxJ, hxC⟩
  have hmem : (⟨x, hxJ⟩ : J) ∈ center J := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
  rw [hc, Subgroup.mem_bot] at hmem
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hmem)

theorem pRank_top_le_three (h : Hyp G p S Z) (J : Subgroup G) :
    CFSG.Open.pRank p (⊤ : Subgroup J) ≤ 3 := by
  rw [← pRank_map_subtype h.prime.one_lt J, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact h.pRank_le_three J

theorem center_eq_bot (hMult : UCK.KMult) (h : Hyp G p S Z) (hcore : CFSG.pPrimeCore p G = ⊥)
    {J : Subgroup G} (hJ : CFSG.IsComponent J) [J.Normal] : center J = ⊥ := by
  haveI := h.fact
  let e := (center J).equivMapOfInjective J.subtype J.subtype_injective
  have hCn : ((center J).map J.subtype).Normal := inferInstance
  have hCnil : Group.IsNilpotent ((center J).map J.subtype) :=
    (Group.isNilpotent_congr e).mp inferInstance
  have hCp : IsPGroup p ((center J).map J.subtype) :=
    CFSG.isPGroup_of_nilpotent_normal _ hCn hCnil hcore
  exact hMult J ⟨hJ.1.1.commutator_eq_top, hJ.1.2.1⟩
    ((h.isKGroup.subgroup J).quotient (center J)) p h.prime h.five_le (hCp.of_equiv e.symm)
    (h.pRank_top_le_three J)

theorem concl_of_isSimpleGroup (hQS : UCK.KQS) (h : Hyp G p S Z) (hs : IsSimpleGroup G) :
    CFSG.Open.pRank p (normalClosure (Z : Set G)) = 1 := by
  have hcyc := hQS G hs h.isKGroup p h.prime h.five_le S h.sylow h.omega h.rank Z h.le h.card h.wc
  exact h.concl_of_le ((pRank_le_of_isSylowOf h.prime h.sylow _).trans
    (pRank_le_one_of_isCyclic h.prime.one_lt hcyc))

theorem false_of_not_le (hOutP : UCK.KOutP) (hQS : UCK.KQS) (h : Hyp G p S Z)
    (hcore : CFSG.pPrimeCore p G = ⊥) {J : Subgroup G} (hJ : CFSG.IsComponent J) [J.Normal]
    (hc : center J = ⊥) (hs : IsSimpleGroup J) (hZJ : ¬ Z ≤ Subgroup.centralizer (J : Set G))
    (hY : Z ⊔ J = ⊤) (hZnJ : ¬ Z ≤ J) : False := by
  haveI := h.fact
  have hJC := inf_centralizer_eq_bot hc
  obtain ⟨z, hzZ, hz1⟩ := (Subgroup.bot_or_exists_ne_one Z).resolve_left h.ne_bot
  have hZz := h.eq_zpowers hzZ hz1
  set α : MulAut J := MulAut.conjNormal z with hα
  have hαp : α ^ p = 1 := by rw [hα, ← map_pow, h.pow_eq_one hzZ, map_one]
  have hα1 : α ≠ 1 := by
    intro hα1
    apply hZJ
    rw [hZz, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    have e := congrArg (fun f : MulAut J => ((f ⟨x, hx⟩ : J) : G)) hα1
    simp only [hα, MulAut.conjNormal_apply, MulAut.one_apply] at e
    calc x * z = z * x * z⁻¹ * z := by rw [e]
      _ = z * x := by group
  have hαo : orderOf α = p := orderOf_eq_prime hαp hα1
  set T : Subgroup J := S.subgroupOf J with hT
  have hTmap : T.map J.subtype = S ⊓ J := Subgroup.subgroupOf_map_subtype S J
  have hJtop : (⊤ : Subgroup J).map J.subtype = J := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hTsyl : IsSylowOf p T ⊤ := by
    have hs' := isSylowOf_inf_of_isSubnormal h.sylow hJ.2
    rw [← hTmap] at hs'
    conv at hs' => rhs; rw [← hJtop]
    exact (isSylowOf_map_subtype_iff J).mp hs'
  have hαT : ∀ x ∈ T, α x = x := by
    intro x hx
    apply Subtype.ext
    rw [hα, MulAut.conjNormal_apply, h.comm hzZ (Subgroup.mem_subgroupOf.mp hx),
      mul_inv_cancel_right]
  have hdvdJ := h.dvd_card_of_isComponent hcore hJ
  obtain ⟨j, hj⟩ := hOutP J hs (h.isKGroup.subgroup J) p h.prime h.five_le hdvdJ
    (h.pRank_top_le_three J) T hTsyl α hαo hαT
  have hjx : ∀ x ∈ J, (j : G) * x * (j : G)⁻¹ = z * x * z⁻¹ := by
    intro x hx
    have e := congrArg (fun f : MulAut J => ((f ⟨x, hx⟩ : J) : G)) hj
    simpa [hα, MulAut.conj_apply, MulAut.conjNormal_apply] using e
  obtain ⟨c, hzeq, hcC, hcJ, hcS, htS, hco, hto⟩ :=
    h.exists_decomp hJC hY hZJ hZnJ hZz j.2 hjx
  have hkey : ∀ k : J, ((k : G))⁻¹ * j * k ∈ S → (j : G) * k = k * j := by
    intro k hk
    have e := h.conj_eq_of_conj_mem hJC hZz hzeq j.2 hcC hcJ hcS hco hto k.2 hk
    calc (j : G) * k = k * ((k : G)⁻¹ * j * k) := by group
      _ = k * j := by rw [e]
  have hjT : j ∈ T := Subgroup.mem_subgroupOf.mpr htS
  have hjo : orderOf j = p := by rw [← Subgroup.orderOf_coe, hto]
  have hTc : IsCyclic T := by
    refine hQS J hs (h.isKGroup.subgroup J) p h.prime h.five_le T hTsyl ?_ ?_ (zpowers j)
      ((Subgroup.zpowers_le).mpr hjT) (by rw [Nat.card_zpowers, hjo]) ?_
    · intro x hx hxp y hy
      apply Subtype.ext
      exact h.omega _ (Subgroup.mem_subgroupOf.mp hx) (by simpa using congrArg Subtype.val hxp) _
        (Subgroup.mem_subgroupOf.mp hy)
    · rw [← pRank_map_subtype h.prime.one_lt J, hTmap]
      exact h.pRank_le_three _
    · intro k hk
      have hkj : ((k : G))⁻¹ * j * k ∈ S := by
        have hmem : k⁻¹ * j * k ∈ CFSG.conjugate (zpowers j) k := by
          rw [mem_conjugate_iff]
          simpa [mul_assoc] using Subgroup.mem_zpowers j
        simpa using Subgroup.mem_subgroupOf.mp (hk hmem)
      have hcomm : Commute k j := Subtype.ext (hkey k hkj).symm
      have hcw : ∀ w ∈ zpowers j, k * w * k⁻¹ = w := by
        intro w hw
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        rw [(hcomm.zpow_right i).eq, mul_inv_cancel_right]
      ext x
      rw [mem_conjugate_iff]
      constructor
      · intro hx
        have e : x = k * x * k⁻¹ := by
          calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
            _ = k⁻¹ * (k * (k * x * k⁻¹) * k⁻¹) * k := by rw [hcw _ hx]
            _ = k * x * k⁻¹ := by group
        rw [e]
        exact hx
      · intro hx
        rw [hcw x hx]
        exact hx
  have hNC : Subgroup.normalizer (T : Set J) ≤ Subgroup.centralizer (T : Set J) := by
    intro n hn
    have hTC : T ≤ Subgroup.centralizer (T : Set J) := fun x hx => by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact mul_comm_of_isCyclic hTc hy hx
    have hCN : Subgroup.centralizer (T : Set J) ≤ Subgroup.normalizer (T : Set J) :=
      Subgroup.centralizer_le_normalizer _
    have hCnormal : ((Subgroup.centralizer (T : Set J)).subgroupOf
        (Subgroup.normalizer (T : Set J))).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      have hgy : ((g : J))⁻¹ * y * g ∈ T := (Subgroup.mem_normalizer_iff''.mp g.2 y).mp hy
      have hxy := hx _ hgy
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc y * (g * x * (g : J)⁻¹) = g * ((((g : J))⁻¹ * y * g) * x) * (g : J)⁻¹ := by group
        _ = g * (x * (((g : J))⁻¹ * y * g)) * (g : J)⁻¹ := by rw [hxy]
        _ = g * x * (g : J)⁻¹ * y := by group
    have hnm : n ^ ((Subgroup.centralizer (T : Set J)).subgroupOf
        (Subgroup.normalizer (T : Set J))).index ∈ Subgroup.centralizer (T : Set J) := by
      have hpow := Subgroup.pow_index_mem ((Subgroup.centralizer (T : Set J)).subgroupOf
        (Subgroup.normalizer (T : Set J))) (⟨n, hn⟩ : Subgroup.normalizer (T : Set J))
      simpa using Subgroup.mem_subgroupOf.mp hpow
    have hm : ¬ p ∣ ((Subgroup.centralizer (T : Set J)).subgroupOf
        (Subgroup.normalizer (T : Set J))).index := by
      have hsylN : IsSylowOf p T (Subgroup.normalizer (T : Set J)) :=
        hTsyl.of_le (hTC.trans hCN) le_top
      have hidx := (isSylowOf_iff.mp hsylN).2.2
      rw [← Subgroup.relIndex_mul_relIndex T _ _ hTC hCN] at hidx
      exact fun hdvd => hidx (dvd_mul_of_dvd_right hdvd _)
    have hnt : n * j = j * n := by
      have hnj : ((n : G))⁻¹ * j * n ∈ S := by
        have hmem := (Subgroup.mem_normalizer_iff''.mp hn j).mp hjT
        simpa using Subgroup.mem_subgroupOf.mp hmem
      exact Subtype.ext (hkey n hnj).symm
    exact mem_centralizer_of_isCyclic h.prime (h.prime.odd_of_ne_two (by have := h.five_le; omega))
      hTc hTsyl.isPGroup hn hm hnm hjT hjo hnt
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowOf_top hTsyl
  have hPT : (P : Set J) = (T : Set J) := congrArg (fun H : Subgroup J => (H : Set J)) hP
  have hNC' : Subgroup.normalizer (P : Set J) ≤ Subgroup.centralizer (P : Set J) := by
    rw [hPT]
    exact hNC
  exact not_dvd_card_of_normalizer_le_centralizer hJ.1.1 P hNC' hdvdJ

theorem concl_of_sup_eq_top (hMult : UCK.KMult) (hOutP : UCK.KOutP) (hQS : UCK.KQS)
    (h : Hyp G p S Z) (hcore : CFSG.pPrimeCore p G = ⊥) {J : Subgroup G}
    (hJ : CFSG.IsComponent J) (hZJ : ¬ Z ≤ Subgroup.centralizer (J : Set G))
    (hNJ : Z ≤ Subgroup.normalizer (J : Set G)) (hY : Z ⊔ J = ⊤) :
    CFSG.Open.pRank p (normalClosure (Z : Set G)) = 1 := by
  haveI hJn : J.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hY]
    exact sup_le hNJ Subgroup.le_normalizer
  have hc := center_eq_bot hMult h hcore hJ
  have hs := isSimpleGroup_of_center_eq_bot hJ.1.2.1 hc
  by_cases hZleJ : Z ≤ J
  · have hJtop : J = ⊤ := by rw [← hY, sup_eq_right.mpr hZleJ]
    haveI hs' : IsSimpleGroup (⊤ : Subgroup G) := hJtop ▸ hs
    exact h.concl_of_isSimpleGroup hQS (Subgroup.topEquiv (G := G)).symm.isSimpleGroup
  · exact (false_of_not_le hOutP hQS h hcore hJ hc hs hZJ hY hZleJ).elim

theorem concl (hMult : UCK.KMult) (hOutP : UCK.KOutP) (hQS : UCK.KQS)
    (ih : IHBelow (Nat.card G)) (h : Hyp G p S Z) :
    CFSG.Open.pRank p (normalClosure (Z : Set G)) = 1 := by
  by_cases hcore : CFSG.pPrimeCore p G = ⊥
  · by_cases hZn : Z.Normal
    · exact h.concl_of_normal hZn
    · obtain ⟨J, hJ, hZJ⟩ := h.exists_component hcore hZn
      have hNJ := h.le_normalizer_of_isComponent hcore hJ
      by_cases hY : Z ⊔ J = ⊤
      · exact h.concl_of_sup_eq_top hMult hOutP hQS hcore hJ hZJ hNJ hY
      · exact h.concl_of_sup_ne_top ih hcore hJ hZJ hNJ hY
  · exact h.concl_of_pPrimeCore_ne_bot ih hcore

end Hyp

end N588A

theorem K332'_of_inputs (hMult : UCK.KMult) (hOutP : UCK.KOutP) (hQS : UCK.KQS) : UCK.K332' := by
  have key : ∀ n : ℕ, N588A.IHBelow n := by
    intro n
    induction n with
    | zero =>
      intro G _ _ hG
      exact absurd hG (Nat.not_lt_zero _)
    | succ n ih =>
      intro G _ _ hG p S Z h
      refine h.concl hMult hOutP hQS ?_
      intro G' _ _ hG'
      exact ih G' (by omega)
  intro G _ _ hK p hp h5 S hS hΩ hrank Z hZS hZcard hwc
  exact key (Nat.card G + 1) G (Nat.lt_succ_self _) p S Z
    ⟨hK, hp, h5, hS, hΩ, hrank, hZS, hZcard, hwc⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK

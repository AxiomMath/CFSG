module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FM
public import CFSG.LieType.SteinbergBROddSylowNormalizers

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Generic

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem mem_of_odd_of_inner_ch615 {J F : Subgroup Γ} (hFJ : F ≤ J)
    (hJF : J ≤ Subgroup.normalizer (F : Set Γ))
    (hB : J ⊓ Subgroup.centralizer (F : Set Γ) ≤ F)
    (hout : ∀ α : MulAut ↥F, Odd (orderOf α) → ∃ g : ↥F, α = MulAut.conj g) {x : Γ}
    (hx : x ∈ J) (hodd : Odd (orderOf x)) : x ∈ F := by
  set α := F.normalizerMonoidHom ⟨x, hJF hx⟩ with hα
  have hαo : orderOf α ∣ orderOf x := by
    have := orderOf_map_dvd F.normalizerMonoidHom ⟨x, hJF hx⟩
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨g, hg⟩ := hout α (Odd.of_dvd_nat hodd hαo)
  have hxg : ∀ y ∈ F, x * y * x⁻¹ = (g : Γ) * y * (g : Γ)⁻¹ := fun y hy => by
    have := congrArg (fun β : MulAut ↥F => ((β ⟨y, hy⟩ : ↥F) : Γ)) hg
    simpa [hα, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using this
  have hc : (g : Γ)⁻¹ * x ∈ J ⊓ Subgroup.centralizer (F : Set Γ) := by
    refine ⟨J.mul_mem (J.inv_mem (hFJ g.2)) hx, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have h1 := hxg y hy
    calc y * ((g : Γ)⁻¹ * x) = (g : Γ)⁻¹ * ((g : Γ) * y * (g : Γ)⁻¹) * x := by group
      _ = (g : Γ)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
      _ = (g : Γ)⁻¹ * x * y := by group
  have := hB hc
  have e : x = (g : Γ) * ((g : Γ)⁻¹ * x) := by group
  rw [e]
  exact F.mul_mem g.2 this

end Generic

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem autI_oTwoUpper_le_of_odd_ch615 (hU : IsElemAbelian 2 (UX615 T L H))
    {C : Subgroup (MulAut (IntMod (UX615 T L H) hU))}
    (hC : ∀ y ∈ autI hU (oTwoUpper H), Odd (orderOf y) → y ∈ C) :
    autI hU (oTwoUpper H) ≤ C := by
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hHN : H ≤ Subgroup.normalizer (UX615 T L H : Set G) := le_sup_right.trans hXN
  refine autI_le_of_le_preI615 ((Subgroup.closure_le _).mpr ?_)
  rintro x ⟨hxH, hxo⟩
  have h1 := convI_mem_autI hU (mem_oTwoUpper_of_odd hxH hxo) (hHN hxH)
  have h2 : Odd (orderOf (convI hU ⟨x, hHN hxH⟩)) := Odd.of_dvd_nat hxo (by
    have := orderOf_map_dvd (convI hU) ⟨x, hHN hxH⟩
    rwa [Subgroup.orderOf_mk] at this)
  exact mem_preI615 (hHN hxH) (hC _ h1 h2)

namespace Cx615C

theorem false_of_le_dLemma_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    {F : Subgroup (MulAut (IntMod (UX615 T L H) hU))} (hdl : DLemmaFacts_ch615 F)
    (hZ : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1)
    (hTF : autI hU T ≤ Subgroup.normalizer (F : Set (MulAut _)))
    (hDF : autI hU D ≤ Subgroup.normalizer (F : Set (MulAut _)))
    (hKF : autI hU (oTwoUpper H) ≤ F) (hS : IsSylowTwoOf (autI hU T ⊓ F) F)
    (hfix : fixV F ≠ ⊥) : False := by
  classical
  obtain ⟨-, hout, hNS, hself⟩ := hdl
  by_cases hDc : autI hU D ≤ Subgroup.centralizer (F : Set (MulAut _))
  · apply c.not_hall_normalizes_ch615 hU hD hN
    intro y hy k hk
    rw [← Subgroup.mem_centralizer_iff.mp (hDc hy) k (hKF hk), mul_inv_cancel_right]
    exact hk
  have hDsodd : ∀ d ∈ autI hU D, Odd (orderOf d) := by
    have hodd : Odd (Nat.card (autI hU D)) := by
      rw [(c.autI_hall_ch615 hU hD).2, ← (c.hall_ch615 hD).2]
      exact hD.2.1
    exact fun d hd => Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hd)
  obtain ⟨d, hdD, hdF, hd1, -⟩ := exists_mem_of_not_le_centralizer_ch615 hout hZ
    hS.isPGroup hS.le (hNS _ hS) (hself _ hS) (inf_le_left.trans (autI_mono hU le_sup_right))
    (autI_mono hU (hD.1.trans le_sup_left)) (c.isSolvable_autI_ch615 hU) hDF hDsodd
    (fun y hy ho => c.mem_autI_borelL_of_odd_ch615 hU hy ho)
    (fun p hp hp2 x hx y hy hxp hyp hxy hx1 =>
      c.mem_zpowers_of_autI_borelL_prime_ch615 hU hp hp2 hx hy hxp hyp hxy hx1) hDc
  obtain ⟨w, hwF, hw1, hwT⟩ := exists_fix_ch615 IntMod.sq_eq_one (c.isPGroup_autI_ch615 hU)
    hfix fun t ht w hw => mem_fixV_of_conj_ch615 (hTF ht) hw
  exact c.false_of_fix_ch615 h432 hU hD hw1 hwT (fun k hk => hwF k (hKF hk)) hdD hd1
    (hwF d hdF)

theorem false_of_le_borel_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    {F : Subgroup (MulAut (IntMod (UX615 T L H) hU))}
    (hBor : ∀ S : Subgroup (MulAut (IntMod (UX615 T L H) hU)), IsSylowTwoOf S F →
      ∀ R : Subgroup (MulAut (IntMod (UX615 T L H) hU)), S ≤ R → R ≤ F → Group.IsSolvable ↥R →
        ∀ r ∈ R, ∀ s ∈ S, r * s * r⁻¹ ∈ S)
    (hKF : autI hU (oTwoUpper H) ≤ F) (hS : IsSylowTwoOf (autI hU T ⊓ F) F)
    (hKJ : autI hU (oTwoUpper H) ≤ ⁅autI hU (oTwoUpper H), autI hU T ⊓ F⁆) : False := by
  classical
  have hKne := c.autI_oTwoUpper_ne_bot_ch615 hU
  have hTK : autI hU T ⊓ F ≤ Subgroup.normalizer (autI hU (oTwoUpper H) : Set (MulAut _)) := by
    have hTK' : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
      c.hH.1.1.trans (le_normalizer_oTwoUpper H)
    intro y hy
    refine Subgroup.mem_normalizer_iff.mpr fun a =>
      ⟨fun ha => C124.autI_conj_mem hU hTK' y hy.1 a ha, fun ha => ?_⟩
    have := C124.autI_conj_mem hU hTK' y⁻¹ ((autI hU T).inv_mem hy.1) _ ha
    simpa [mul_assoc] using this
  have hKs := c.isSolvable_autI_oTwoUpper_ch615 hU
  have hT2s : Group.IsSolvable ↥(autI hU T ⊓ F) := by
    have := hS.isPGroup.isNilpotent
    infer_instance
  have hRs : Group.IsSolvable ↥(autI hU (oTwoUpper H) ⊔ (autI hU T ⊓ F)) :=
    A3.isSolvable_sup_of_le_normalizer hTK
  have hnorm := hBor _ hS _ le_sup_right (sup_le hKF inf_le_right) hRs
  have hKT : autI hU (oTwoUpper H) ≤ autI hU T ⊓ F := by
    refine hKJ.trans (Subgroup.commutator_le.mpr fun k hk s hs => ?_)
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (hnorm k (Subgroup.mem_sup_left hk) s hs)
      (Subgroup.inv_mem _ hs)
  apply hKne
  rw [eq_bot_iff]
  refine autI_oTwoUpper_le_of_odd_ch615 hU fun y hy hyo => ?_
  exact Subgroup.mem_bot.mpr (eq_one_of_odd_of_mem_l32_ch615 hS.isPGroup (hKT hy) hyo)

omit [Finite G] in
theorem le_normalizer_genFitting_ch615 (hU : IsElemAbelian 2 (UX615 T L H)) :
    autI hU (borelL T L ⊔ H) ≤ Subgroup.normalizer
      (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) : Set (MulAut _)) := fun _ hx =>
  normalizer_le_normalizer_quasithinGenFitting _ (B6.le_normalizer_ffJ _ hx)

theorem isSylowTwoOf_genFitting_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H)) :
    IsSylowTwoOf (autI hU T ⊓ quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))))
      (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := by
  have hLX : quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) ≤ autI hU (borelL T L ⊔ H) :=
    (quasithinGenFitting_le _).trans (B6.ffJ_le _)
  have hn := (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mpr
    (le_normalizer_genFitting_ch615 hU)
  exact RankOneRecog.isSylowTwoOf_inf_of_subnormal (c.isSylowTwoOf_autI_ch615 hU) hLX
    hn.isSubnormal

theorem autI_oTwoUpper_le_genFitting_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hout : ∀ α : MulAut ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))),
      Odd (orderOf α) → ∃ g, α = MulAut.conj g) :
    autI hU (oTwoUpper H) ≤ quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) :=
  autI_oTwoUpper_le_of_odd_ch615 hU fun _ hy hyo =>
    mem_of_odd_of_inner_ch615 (quasithinGenFitting_le _)
      (le_normalizer_quasithinGenFitting _) (centralizer_quasithinGenFitting_le _) hout
      ((c.le_ffJ_ch615 hU).2 hy) hyo

theorem false_of_case1_dLemma_fix_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (hdl : DLemmaFacts_ch615 (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))))
    (hZ : ∀ g ∈ quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))),
      (∀ x ∈ quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))), g * x = x * g) → g = 1)
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≠ ⊥) : False := by
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hK := c.autI_oTwoUpper_le_genFitting_ch615 hU hdl.2.1
  exact c.false_of_le_dLemma_ch615 h432 hU hN hD hdl hZ
    (fun x hx => le_normalizer_genFitting_ch615 hU (autI_mono hU (c.hH.1.1.trans le_sup_right) hx))
    (fun x hx => le_normalizer_genFitting_ch615 hU (autI_mono hU (hD.1.trans le_sup_left) hx))
    hK (c.isSylowTwoOf_genFitting_ch615 hU) hfix

theorem false_of_case1_borel_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hJ : quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) = ffJ (autI hU (borelL T L ⊔ H)))
    (hBor : ∀ S : Subgroup (MulAut (IntMod (UX615 T L H) hU)),
      IsSylowTwoOf S (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) →
      ∀ R : Subgroup (MulAut (IntMod (UX615 T L H) hU)), S ≤ R →
        R ≤ quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) → Group.IsSolvable ↥R →
        ∀ r ∈ R, ∀ s ∈ S, r * s * r⁻¹ ∈ S) : False := by
  have hKF : autI hU (oTwoUpper H) ≤ quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) := by
    rw [hJ]
    exact (c.le_ffJ_ch615 hU).2
  have hJT : autI hU (thompsonJ T) ≤
      autI hU T ⊓ quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) := by
    rw [hJ]
    exact le_inf (autI_mono hU (thompsonJ_le_self T)) (c.le_ffJ_ch615 hU).1
  exact c.false_of_le_borel_ch615 hU hBor hKF (c.isSylowTwoOf_genFitting_ch615 hU)
    ((c.le_commutator_ch615 hU).trans (Subgroup.commutator_mono le_rfl hJT))

end Cx615C

theorem dLemmaFacts_l32_ch615 {Γ : Type*} [Group Γ] [Finite Γ] {F : Subgroup Γ}
    (e : ↥F ≃* CFSG.QuasithinUnique.Setup.Family.GL32) : DLemmaFacts_ch615 F :=
  ⟨not_isSolvable_l32_ch615 e, exists_eq_conj_l32_ch615 e,
    fun _ hS _ hg hgS => mem_of_conj_mem_l32_ch615 e hS hg hgS,
    fun _ hS _ hSR hRF hRS hR _ hg hgR =>
      mem_of_conj_mem_overgroup_l32_ch615 e hS hSR hRF hRS hR hg hgR⟩

namespace Cx615C

theorem false_of_case1_alt_six_fix_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃* ↥(alternatingGroup (Fin 6)))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≠ ⊥) : False := by
  have hs : IsSimpleGroup ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := by
    have := isSimpleGroup_alt_six_ch615
    exact e.isSimpleGroup
  have hdl := dLemmaFacts_alt_six_ch615 e
  exact c.false_of_case1_dLemma_fix_ch615 h432 hU hN hdl (center_of_isSimpleGroup_ch615 hs hdl.1)
    hfix

theorem false_of_case1_l32_fix_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≠ ⊥) : False := by
  obtain ⟨e'⟩ := nonempty_l32_ch615 hK e
  exact c.false_of_case1_dLemma_fix_ch615 h432 hU hN (dLemmaFacts_l32_ch615 e')
    (fun _ hg h => eq_one_of_commute_l32_ch615 e' hg h) hfix

end Cx615C

section Frattini

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem mem_of_normalizes_overgroup_ch615 {F S R : Subgroup Γ} (hS : IsSylowTwoOf S F)
    (hN : ∀ g ∈ F, (∀ s ∈ S, g * s * g⁻¹ ∈ S) → g ∈ S) (hSR : S ≤ R) (hRF : R ≤ F) {g : Γ}
    (hg : g ∈ F) (hgR : ∀ r ∈ R, g * r * g⁻¹ ∈ R) : g ∈ R := by
  have hSRs : IsSylowTwoOf S R := by
    refine isSylowTwoOf_of_card_eq hSR hS.isPGroup (le_antisymm (card_le_twoPart hSR hS.isPGroup)
      ?_)
    rw [hS.card_eq]
    exact twoPart_mono hRF
  set S' := S.map (MulAut.conj g).toMonoidHom with hS'
  have hS'R : S' ≤ R := by
    rintro _ ⟨s, hs, rfl⟩
    exact hgR s (hSR hs)
  have hS's : IsSylowTwoOf S' R := by
    refine isSylowTwoOf_of_card_eq hS'R (hS.isPGroup.map _) ?_
    rw [hS', Subgroup.card_map_of_injective (MulAut.conj g).injective, hSRs.card_eq]
  obtain ⟨r, hrR, hr⟩ := hSRs.exists_conj hS's
  have hrg : r⁻¹ * g ∈ S := by
    refine hN _ (F.mul_mem (F.inv_mem (hRF hrR)) hg) fun s hs => ?_
    have h1 : g * s * g⁻¹ ∈ S' := ⟨s, hs, rfl⟩
    rw [hr] at h1
    obtain ⟨t, ht, he⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
    have : r⁻¹ * g * s * (r⁻¹ * g)⁻¹ = t := by
      calc r⁻¹ * g * s * (r⁻¹ * g)⁻¹ = r⁻¹ * (g * s * g⁻¹) * r := by group
        _ = r⁻¹ * (r * t * r⁻¹) * r := by rw [he]
        _ = t := by group
    rw [this]
    exact ht
  have e : g = r * (r⁻¹ * g) := by group
  rw [e]
  exact R.mul_mem hrR (hSR hrg)

end Frattini

section Small

theorem exists_eq_conj_of_outer_ch615 {X : Type*} [Group X] (hO : IsPGroup 2 (Outer X))
    (α : MulAut X) (hα : Odd (orderOf α)) : ∃ g, α = MulAut.conj g := by
  have hinn : α ∈ inner X := by
    obtain ⟨k, hk⟩ := hO (QuotientGroup.mk' (inner X) α)
    have hdvd := orderOf_map_dvd (QuotientGroup.mk' (inner X)) α
    have h1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.pow_right k (hα.of_dvd_nat hdvd).coprime_two_right)
      (orderOf_dvd_of_pow_eq_one hk)
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  obtain ⟨g, hg⟩ := hinn
  exact ⟨g, hg.symm⟩

theorem dLemmaFacts_of_smallAlt_ch615 {Γ : Type*} [Group Γ] [Finite Γ] {F : Subgroup Γ}
    (hsimp : IsSimpleGroup ↥F) (hnab : ∃ a b : ↥F, a * b ≠ b * a)
    (hcase : (∃ n : ℕ, (n = 6 ∨ n = 7 ∨ n = 8) ∧ Nonempty (↥F ≃* alternatingGroup (Fin n))) ∨
      ∃ (n : ℕ) (k : Type) (_ : Field k) (_ : Finite k), 3 ≤ n ∧ Nat.card k = 2 ∧
        Nonempty (↥F ≃* projectiveSL n k)) :
    DLemmaFacts_ch615 F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key := fun U : Sylow 2 ↥F =>
    CFSG.LieType.small_alternating_and_binary_linear_odd_Sylow_normalizers_are_trivial ↥F hsimp
      hnab U 1 (by rw [orderOf_one]; exact odd_one) (by
        ext x
        simp) hcase
  obtain ⟨U₀⟩ : Nonempty (Sylow 2 ↥F) := inferInstance
  have hO := (key U₀).2.1
  have hns : ¬ Group.IsSolvable ↥F := fun h => by
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr h a b)
  have hNX : ∀ S₀ : Subgroup ↥F, IsSylowTwoOf S₀ ⊤ → ∀ g : ↥F,
      (∀ s ∈ S₀, g * s * g⁻¹ ∈ S₀) → g ∈ S₀ := by
    intro S₀ hS₀ g hg
    have hidx : ¬ 2 ∣ S₀.index := by
      have := hS₀.2.2
      change ¬ 2 ∣ S₀.relIndex ⊤ at this
      rwa [Subgroup.relIndex_top_right] at this
    set U := hS₀.isPGroup.toSylow hidx with hUdef
    have hU : (U : Subgroup ↥F) = S₀ := rfl
    have hNU' : Subgroup.normalizer (((U : Subgroup ↥F) : Set ↥F)) = (U : Subgroup ↥F) :=
      (key U).1
    have hgN := mem_normalizer_of_conj_mem_l32_ch615 hg
    rw [← hU, hNU'] at hgN
    exact hgN
  exact dLemmaFacts_of_mulEquiv_ch615 (MulEquiv.refl ↥F) hns (exists_eq_conj_of_outer_ch615 hO)
    hNX fun S₀ hS₀ _ hSR _ _ g hg =>
      mem_of_normalizes_overgroup_ch615 hS₀ (fun g' _ h => hNX S₀ hS₀ g' h) hSR le_top
        (Subgroup.mem_top g) fun r hr => hg r hr

end Small

namespace Cx615C

theorem false_of_case1_small_fix_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (hs : IsSimpleGroup ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))))
    (hnab : ∃ a b : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))), a * b ≠ b * a)
    (hcase : (∃ k : ℕ, (k = 6 ∨ k = 7 ∨ k = 8) ∧
        Nonempty (↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
          alternatingGroup (Fin k))) ∨
      ∃ (k : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 3 ≤ k ∧ Nat.card F = 2 ∧
        Nonempty (↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃* projectiveSL k F))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≠ ⊥) : False := by
  have hdl := dLemmaFacts_of_smallAlt_ch615 hs hnab hcase
  exact c.false_of_case1_dLemma_fix_ch615 h432 hU hN hdl (center_of_isSimpleGroup_ch615 hs hdl.1)
    hfix

theorem false_of_case1_alt_seven_fix_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (hq : CFSG.IsQuasisimple ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))))
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃* ↥(alternatingGroup (Fin 7)))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≠ ⊥) : False := by
  have hs : IsSimpleGroup ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  exact c.false_of_case1_small_fix_ch615 h432 hU hN hs
    (CFSG.Quasithin.InternalSec.exists_noncomm_of_isQuasisimple hq)
    (Or.inl ⟨7, by norm_num, ⟨e⟩⟩) hfix

theorem false_of_case1_binary_linear_fix_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (hq : CFSG.IsQuasisimple ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))))
    {k : ℕ} (hk : 3 ≤ k)
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL k (ZMod 2)))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≠ ⊥) : False := by
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hs : IsSimpleGroup ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := by
    have := CFSG.Quasithin.B69.isSimpleGroup_statedSL_two h2 hk
    exact e.isSimpleGroup
  exact c.false_of_case1_small_fix_ch615 h432 hU hN hs
    (CFSG.Quasithin.InternalSec.exists_noncomm_of_isQuasisimple hq)
    (Or.inr ⟨k, ZMod 2, inferInstance, inferInstance, hk, h2,
      ⟨e.trans ((CFSG.Quasithin.B69.statedSLEquivStatedProj h2 k).trans
        (CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL k (ZMod 2)))⟩⟩) hfix

end Cx615C

end CFSG.Quasithin.H13

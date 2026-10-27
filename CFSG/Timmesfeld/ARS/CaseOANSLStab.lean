module

public import CFSG.Timmesfeld.ARS.CaseOANSLLocal
public import CFSG.Timmesfeld.ARS.ExclNSStab
public import CFSG.Timmesfeld.ARS.CaseOACells

public section

open scoped commutatorElement Pointwise

namespace CFSG.Timmesfeld.ARS

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace CaseOANSL

abbrev CompBar (Δ₁ : Set (Subgroup G)) : Type :=
  ↥(gen Δ₁) ⧸ Subgroup.center ↥(gen Δ₁)

@[expose] def stabBar₁ (Δ₁ : Set (Subgroup G)) (B : Subgroup G) : Subgroup (CompBar Δ₁) :=
  ((Subgroup.normalizer (B : Set G)).subgroupOf (gen Δ₁)).map
    (QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)))

theorem conjSub_conjSub_inv (X : Subgroup G) (g : G) : conjSub (conjSub X g) g⁻¹ = X := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem commuting_of_le_normalizer (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    {B X : Subgroup G} (hB : B ∈ lambdaStar R A A₀) (hX : X ∈ leviSet R A A₀)
    (hXB : X ≤ Subgroup.normalizer (B : Set G)) : Commuting X B := by
  have := h.finite
  have hR := h.root
  by_contra hc
  have hs : Special R B X :=
    special_of_not_commuting_of_mem_leviSet h hA hB hX fun h => hc h.symm
  have hle : ⁅B, X⁆ ≤ B := Linear.commutator_le_of_le_normalizer' le_rfl hXB
  exact hs.ne_commutator hR (Subgroup.eq_of_le_of_card_ge hle
    (hR.card_eq hB.1.1.1 hs.1).le).symm

section Stab

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
  (h2 : Nat.card (leviComps R A A₀) = 2) {Δ₁ Δ₂ : Set (Subgroup G)}
  (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
include h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne

omit hmax h2 hΔ₂ hne in
theorem gen_le_levi : gen Δ₁ ≤ levi R A A₀ :=
  Sec9.gen_le_levi fun _ hX => Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX

theorem conjSub_eq_of_mem_center {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    {z : ↥(gen Δ₁)} (hz : z ∈ Subgroup.center ↥(gen Δ₁)) : conjSub B (z : G) = B :=
  conjSub_eq_of_forall_commute h hA hAne hmax hA₀ hΔ₁ hΔ₂ hne hB
    (gen_le_levi h hA hAne hA₀ hΔ₁ z.2) fun _ hX _ hx =>
      commute_of_mem_center h hA hAne hA₀ hΔ₁ hΔ₂ hne h2 hz hX hx

theorem mk_mem_stabBar₁_iff {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) (v : ↥(gen Δ₁)) :
    QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) v ∈ stabBar₁ Δ₁ B ↔
      (v : G) ∈ Subgroup.normalizer (B : Set G) := by
  constructor
  · intro hv
    obtain ⟨w, hw, he⟩ := Subgroup.mem_map.1 hv
    have hz : w⁻¹ * v ∈ Subgroup.center ↥(gen Δ₁) := QuotientGroup.eq.1 he
    have e : (v : G) = (w : G) * ((w⁻¹ * v : ↥(gen Δ₁)) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_subgroupOf.1 hw)
      (conjSub_eq_self_iff.1 (conjSub_eq_of_mem_center h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB hz))
  · intro hv
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hv)

theorem commuting_iff_quotMap_le_stabBar₁ {B X : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hX : X ∈ Δ₁) : Commuting X B ↔ quotMap (gen Δ₁) X ≤ stabBar₁ Δ₁ B := by
  constructor
  · intro hc
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono _
      (ExclNS.le_normalizer_of_commuting' hc.symm))
  · intro hle
    refine commuting_of_le_normalizer h hA hB
      (Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX) fun x hx => ?_
    exact (mk_mem_stabBar₁_iff h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB ⟨x, le_gen hX hx⟩).1
      (hle (LeviQuot.mk_mem_quotMap hx))

theorem stabBar₁_conjSub {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) (v : ↥(gen Δ₁)) :
    stabBar₁ Δ₁ (conjSub B (v : G)) =
      conjSub (stabBar₁ Δ₁ B) (QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) v) := by
  have hR := h.root
  have hBv := conjSub_mem_lambdaStar_of_mem_levi hR hB (gen_le_levi h hA hAne hA₀ hΔ₁ v.2)
  ext a
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(gen Δ₁)) a
  rw [mk_mem_stabBar₁_iff h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hBv, mem_conjSub, ← map_inv,
    ← map_mul, ← map_mul, mk_mem_stabBar₁_iff h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB,
    ← conjSub_eq_self_iff, ← conjSub_eq_self_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  constructor
  · intro hw
    rw [conjSub_mul, conjSub_mul, hw, conjSub_conjSub_inv]
  · intro hw
    calc conjSub (conjSub B v) w = conjSub B ((v : G) * ((v : G)⁻¹ * w * v)) := by
          rw [← conjSub_mul]
          group
      _ = conjSub B v := by rw [conjSub_mul, hw]

omit hmax h2 hΔ₂ hne in
theorem conjSub_eq_of_mem_comp₂ (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
    {X : Subgroup G} (hX : X ∈ Δ₂) {v : G} (hv : v ∈ gen Δ₁) : conjSub X v = X :=
  conjSub_of_forall_commute fun x hx =>
    Sec9.commuting_gen_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne v hv x (le_gen hX hx)

theorem eq_of_forall_quotMap_le_stabBar₁ {B C : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hC : C ∈ lambdaStar R A A₀)
    (h₁ : ∀ X ∈ Δ₁, X ∈ deltaSet R A A₀ C → quotMap (gen Δ₁) X ≤ stabBar₁ Δ₁ B)
    (h₂ : ∀ X ∈ Δ₂, X ∈ deltaSet R A A₀ C → Commuting X B) : C = B := by
  have := h.finite
  refine eq_of_forall_commuting' h hA hAne hA₀ (fun _ hB' _ hC' hBC =>
    CaseOA.lambdaStar_inter_nonempty h hA hAne hmax hA₀ hΔ₁ hΔ₂ hne hB' hC' hBC) hmax hB hC
    fun X hX => ?_
  have hXc : Levi.comp R A A₀ X ∈ leviComps R A A₀ := ⟨X, hX.1, rfl⟩
  rcases CaseOA.eq_or_eq_of_card_two h2 hΔ₁ hΔ₂ hne hXc with e | e
  · exact (commuting_iff_quotMap_le_stabBar₁ h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB
      (e ▸ Sec9.self_mem_comp A A₀ X)).2 (h₁ X (e ▸ Sec9.self_mem_comp A A₀ X) hX)
  · exact h₂ X (e ▸ Sec9.self_mem_comp A A₀ X) hX

theorem conjSub_eq_of_forall_quotMap_le_stabBar₁ {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    {v : G} (hv : v ∈ gen Δ₁)
    (h₁ : ∀ X ∈ Δ₁, X ∈ deltaSet R A A₀ (conjSub B v) → quotMap (gen Δ₁) X ≤ stabBar₁ Δ₁ B) :
    conjSub B v = B := by
  have hR := h.root
  have hvV := gen_le_levi h hA hAne hA₀ hΔ₁ hv
  refine eq_of_forall_quotMap_le_stabBar₁ h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB
    (conjSub_mem_lambdaStar_of_mem_levi hR hB hvV) h₁ fun X hX hXB => ?_
  rw [← conjSet_deltaSet hR hvV] at hXB
  obtain ⟨Y, hY, hYX⟩ := hXB
  have hYc : Levi.comp R A A₀ Y ∈ leviComps R A A₀ := ⟨Y, hY.1, rfl⟩
  have hYX' : Y = X := by
    have hX' : conjSub X v⁻¹ = X :=
      conjSub_eq_of_mem_comp₂ h hA hAne hA₀ hΔ₁ hΔ₂ hne hX (inv_mem hv)
    rw [← hX', ← hYX, conjSub_conjSub_inv]
  subst hYX'
  exact hY.2.1.2.2.symm

theorem stabBar₁_ne_top {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) :
    stabBar₁ Δ₁ B ≠ ⊤ := by
  intro htop
  exact Sec9.not_forall_commuting h hA hAne hA₀ hmax hΔ₁ hB fun Y hY =>
    (commuting_iff_quotMap_le_stabBar₁ h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB hY).2
      (htop ▸ le_top)

theorem iSup_quotMap_le_stabBar₁ {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) :
    ⨆ X ∈ Δ₁ ∩ deltaSet R A A₀ B, quotMap (gen Δ₁) X ≤ stabBar₁ Δ₁ B :=
  iSup₂_le fun _ hX =>
    (commuting_iff_quotMap_le_stabBar₁ h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB hX.1).1
      hX.2.2.1.2.2.symm

omit hAne hmax h2 hΔ₁ hΔ₂ hne in
theorem isPGroup_iSup_quotMap {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) :
    IsPGroup 2 ↥(⨆ X ∈ Δ₁ ∩ deltaSet R A A₀ B, quotMap (gen Δ₁) X) := by
  have hR := h.root
  set T := ⨆ X ∈ Δ₁ ∩ deltaSet R A A₀ B, quotMap (gen Δ₁) X with hT
  have hgen : ∀ X ∈ Δ₁ ∩ deltaSet R A A₀ B, quotMap (gen Δ₁) X ≤ T := fun X hX =>
    le_iSup₂_of_le (f := fun X (_ : X ∈ Δ₁ ∩ deltaSet R A A₀ B) => quotMap (gen Δ₁) X) X hX
      le_rfl
  have hcomm : Commuting T T := by
    rw [commuting_iff_le_centralizer]
    refine iSup₂_le fun X hX => ?_
    rw [← commuting_iff_le_centralizer]
    refine Commuting.symm ?_
    rw [commuting_iff_le_centralizer]
    refine iSup₂_le fun Y hY => ?_
    rw [← commuting_iff_le_centralizer]
    exact LeviQuot.commuting_quotMap (commuting_of_mem_deltaSet h hA hA₀ hB hX.2 hY.2)
  have hsq : ∀ x ∈ T, x * x = 1 := by
    intro x hx
    have hx' := hx
    rw [hT, iSup_subtype'] at hx'
    refine (Subgroup.iSup_induction' (C := fun x _ => x ∈ T ∧ x * x = 1) _
      (fun i y hy => ⟨hgen i.1 i.2 hy, LeviQuot.mul_self_of_mem_quotMap hR i.2.2.1.1.1 hy⟩)
      ⟨T.one_mem, mul_one 1⟩ (fun y z _ _ hy hz => ⟨T.mul_mem hy.1 hz.1, ?_⟩) hx').2
    calc y * z * (y * z) = y * (z * y) * z := by group
      _ = y * (y * z) * z := by rw [(hcomm z hz.1 y hy.1).eq]
      _ = (y * y) * (z * z) := by group
      _ = 1 := by rw [hy.2, hz.2, one_mul]
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, SubgroupClass.coe_pow, pow_two]
  exact hsq x x.2

theorem exists_le_stabBar₁_of_isPGroup {U : Subgroup (CompBar Δ₁)} (hU : IsPGroup 2 U) :
    ∃ B ∈ lambdaStar R A A₀, U ≤ stabBar₁ Δ₁ B := by
  have := h.finite
  have hR := h.root
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B₁, hB₁⟩ := CaseD4.lambdaStar_nonempty h hA hA₀
  set P := stabBar₁ Δ₁ B₁ with hP
  set T := ⨆ X ∈ Δ₁ ∩ deltaSet R A A₀ B₁, quotMap (gen Δ₁) X with hT
  obtain ⟨S, hTS⟩ := (isPGroup_iSup_quotMap (Δ₁ := Δ₁) h hA hA₀ hB₁).exists_le_sylow
  have hTP : T ≤ P := iSup_quotMap_le_stabBar₁ h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB₁
  have hSP : (S : Subgroup _) ≤ P := by
    by_contra hSP
    set Q := (S : Subgroup _) ⊓ P with hQ
    have hQlt : Q.subgroupOf S < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => hSP fun x hx => ?_
      have hx' : (⟨x, hx⟩ : ↥(S : Subgroup _)) ∈ Q.subgroupOf S := htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hx').2
    have hnil := S.isPGroup'.isNilpotent
    obtain ⟨s, hsN, hsQ⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (h := hnil) _ hQlt)
    obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(gen Δ₁)) (s : _)
    have hsT : ∀ x ∈ T, (s : _) * x * (s : _)⁻¹ ∈ P := by
      intro x hx
      have hxQ : (⟨x, hTS hx⟩ : ↥(S : Subgroup _)) ∈ Q.subgroupOf S :=
        Subgroup.mem_subgroupOf.2 ⟨hTS hx, hTP hx⟩
      have := (Subgroup.mem_normalizer_iff.1 hsN _).1 hxQ
      exact (Subgroup.mem_subgroupOf.1 this).2
    have hvV := gen_le_levi h hA hAne hA₀ hΔ₁ v.2
    have hC : conjSub B₁ (v : G) = B₁ := by
      refine conjSub_eq_of_forall_quotMap_le_stabBar₁ h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB₁ v.2
        fun X hX₁ hX => ?_
      rw [← conjSet_deltaSet hR hvV] at hX
      obtain ⟨Y, hY, rfl⟩ := hX
      have hY₁ : Y ∈ Δ₁ := by
        have := Sec9.conjSub_mem h hA hAne hA₀ hΔ₁ hX₁ (inv_mem hvV)
        rwa [conjSub_conjSub_inv] at this
      rw [LeviQuot.quotMap_conjSub Y v.2]
      rintro _ ⟨y, hy, rfl⟩
      have hyT : y ∈ T := le_iSup₂_of_le
        (f := fun X (_ : X ∈ Δ₁ ∩ deltaSet R A A₀ B₁) => quotMap (gen Δ₁) X) Y ⟨hY₁, hY⟩
        le_rfl hy
      have e : (QuotientGroup.mk' (Subgroup.center ↥(gen Δ₁)) ⟨(v : G), v.2⟩) = s := hv
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e]
      exact hsT y hyT
    apply hsQ
    refine Subgroup.mem_subgroupOf.2 ⟨s.2, ?_⟩
    rw [← hv]
    exact (mk_mem_stabBar₁_iff h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB₁ v).2
      (conjSub_eq_self_iff.1 hC)
  obtain ⟨S', hUS'⟩ := hU.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (CompBar Δ₁) S S'
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(gen Δ₁)) g
  refine ⟨conjSub B₁ (v : G), conjSub_mem_lambdaStar_of_mem_levi hR hB₁
    (gen_le_levi h hA hAne hA₀ hΔ₁ v.2), ?_⟩
  rw [stabBar₁_conjSub h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hB₁ v, ← hP]
  refine hUS'.trans ?_
  rw [← hg, Sylow.coe_subgroup_smul, ExclNS.conj_smul_eq_conjSub]
  exact Subgroup.map_mono hSP

end Stab

end CaseOANSL

end CFSG.Timmesfeld.ARS

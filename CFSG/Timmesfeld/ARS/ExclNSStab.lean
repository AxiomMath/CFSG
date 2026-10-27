module

public import CFSG.Timmesfeld.ARS.CaseEExtremal
public import CFSG.Timmesfeld.ARS.Sec13Closed

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace ExclNS

variable {A A₀ : Subgroup G}

theorem conjSub_conjSub_inv (X : Subgroup G) (g : G) : conjSub (conjSub X g) g⁻¹ = X := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_inv_conjSub (X : Subgroup G) (g : G) : conjSub (conjSub X g⁻¹) g = X := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem le_normalizer_of_commuting' {E U : Subgroup G} (h : Commuting E U) :
    U ≤ Subgroup.normalizer (E : Set G) := fun u hu =>
  conjSub_eq_self_iff.1 (conjSub_of_forall_commute fun e he => (h e he u hu).symm)

@[expose] def stabBar (R : Set (Subgroup G)) (A A₀ B : Subgroup G) :
    Subgroup (↥(levi R A A₀) ⧸ Subgroup.center ↥(levi R A A₀)) :=
  ((Subgroup.normalizer (B : Set G)).subgroupOf (levi R A A₀)).map
    (QuotientGroup.mk' (Subgroup.center ↥(levi R A A₀)))

theorem conjSub_eq_of_mem_center (hS : Sec13 R A A₀) {B : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) {z : ↥(levi R A A₀)}
    (hz : z ∈ Subgroup.center ↥(levi R A A₀)) : conjSub B (z : G) = B := by
  have hR := hS.hyp.root
  have hfix : ∀ X ∈ leviSet R A A₀, conjSub X (z : G) = X := fun X hX =>
    conjSub_of_forall_commute fun x hx =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨x, le_gen hX hx⟩)).symm
  refine hS.eq_of_deltaSet_eq (conjSub_mem_lambdaStar_of_mem_levi hR hB z.2) hB ?_
  rw [← conjSet_deltaSet hR z.2]
  ext X
  constructor
  · rintro ⟨Y, hY, rfl⟩
    show conjSub Y (z : G) ∈ _
    rw [hfix Y hY.1]
    exact hY
  · intro hX
    exact ⟨X, hX, hfix X hX.1⟩

theorem mem_normalizer_of_mem_center (hS : Sec13 R A A₀) {B : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) {z : ↥(levi R A A₀)}
    (hz : z ∈ Subgroup.center ↥(levi R A A₀)) : (z : G) ∈ Subgroup.normalizer (B : Set G) :=
  conjSub_eq_self_iff.1 (conjSub_eq_of_mem_center hS hB hz)

theorem mk_mem_stabBar_iff (hS : Sec13 R A A₀) {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (v : ↥(levi R A A₀)) :
    QuotientGroup.mk' (Subgroup.center ↥(levi R A A₀)) v ∈ stabBar R A A₀ B ↔
      (v : G) ∈ Subgroup.normalizer (B : Set G) := by
  constructor
  · intro h
    obtain ⟨w, hw, he⟩ := Subgroup.mem_map.1 h
    have hz : w⁻¹ * v ∈ Subgroup.center ↥(levi R A A₀) := QuotientGroup.eq.1 he
    have e : (v : G) = (w : G) * ((w⁻¹ * v : ↥(levi R A A₀)) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_subgroupOf.1 hw)
      (mem_normalizer_of_mem_center hS hB hz)
  · intro h
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 h)

theorem commuting_of_le_normalizer (hS : Sec13 R A A₀) {B X : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hX : X ∈ leviSet R A A₀)
    (hXB : X ≤ Subgroup.normalizer (B : Set G)) : Commuting X B := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  by_contra hc
  have hs : Special R B X :=
    special_of_not_commuting_of_mem_leviSet hS.hyp hS.mem hB hX fun h => hc h.symm
  have hle : ⁅B, X⁆ ≤ B := Linear.commutator_le_of_le_normalizer' le_rfl hXB
  exact hs.ne_commutator hR (Subgroup.eq_of_le_of_card_ge hle
    (hR.card_eq hB.1.1.1 hs.1).le).symm

theorem commuting_iff_quotMap_le_stabBar (hS : Sec13 R A A₀) {B X : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hX : X ∈ leviSet R A A₀) :
    Commuting X B ↔ quotMap (levi R A A₀) X ≤ stabBar R A A₀ B := by
  constructor
  · intro h
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ (le_normalizer_of_commuting' h.symm))
  · intro h
    refine commuting_of_le_normalizer hS hB hX fun x hx => ?_
    exact (mk_mem_stabBar_iff hS hB ⟨x, le_gen hX hx⟩).1 (h (LeviQuot.mk_mem_quotMap hx))

theorem stabBar_conjSub (hS : Sec13 R A A₀) {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (v : ↥(levi R A A₀)) :
    stabBar R A A₀ (conjSub B (v : G)) =
      conjSub (stabBar R A A₀ B) (QuotientGroup.mk' (Subgroup.center ↥(levi R A A₀)) v) := by
  have hR := hS.hyp.root
  have hBv := conjSub_mem_lambdaStar_of_mem_levi hR hB v.2
  ext a
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(levi R A A₀)) a
  rw [mk_mem_stabBar_iff hS hBv, mem_conjSub, ← map_inv, ← map_mul, ← map_mul,
    mk_mem_stabBar_iff hS hB, ← conjSub_eq_self_iff, ← conjSub_eq_self_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  constructor
  · intro h
    rw [conjSub_mul, conjSub_mul, h, conjSub_conjSub_inv]
  · intro h
    calc conjSub (conjSub B v) w = conjSub B ((v : G) * ((v : G)⁻¹ * w * v)) := by
          rw [← conjSub_mul]
          group
      _ = conjSub B v := by rw [conjSub_mul, h]

theorem eq_of_forall_quotMap_le_stabBar (hS : Sec13 R A A₀) {B C : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀)
    (h : ∀ X ∈ deltaSet R A A₀ C, quotMap (levi R A A₀) X ≤ stabBar R A A₀ B) : C = B :=
  hS.eq_of_forall_commuting hS.leviClosed hB hC fun X hX =>
    (commuting_iff_quotMap_le_stabBar hS hB hX.1).2 (h X hX)

theorem stabBar_ne_top (hS : Sec13 R A A₀) {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) :
    stabBar R A A₀ B ≠ ⊤ := by
  intro htop
  obtain ⟨X, hX, hBX⟩ := exists_mem_leviSet_special hS.hyp hS.mem hS.sec8.2 hS.opp hB
  exact hBX.not_commuting hS.hyp.root
    ((commuting_iff_quotMap_le_stabBar hS hB hX).2 (htop ▸ le_top)).symm

theorem iSup_quotMap_deltaSet_le_stabBar (hS : Sec13 R A A₀) {B : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) :
    ⨆ X ∈ deltaSet R A A₀ B, quotMap (levi R A A₀) X ≤ stabBar R A A₀ B :=
  iSup₂_le fun _ hX =>
    (commuting_iff_quotMap_le_stabBar hS hB hX.1).1 hX.2.1.2.2.symm

theorem isPGroup_iSup_quotMap_deltaSet (hS : Sec13 R A A₀) {B : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) :
    IsPGroup 2 ↥(⨆ X ∈ deltaSet R A A₀ B, quotMap (levi R A A₀) X) := by
  have hR := hS.hyp.root
  set T := ⨆ X ∈ deltaSet R A A₀ B, quotMap (levi R A A₀) X with hT
  have hgen : ∀ X ∈ deltaSet R A A₀ B, quotMap (levi R A A₀) X ≤ T := fun X hX =>
    le_iSup₂_of_le (f := fun X (_ : X ∈ deltaSet R A A₀ B) => quotMap (levi R A A₀) X) X hX
      le_rfl
  have hcomm : Commuting T T := by
    rw [commuting_iff_le_centralizer]
    refine iSup₂_le fun X hX => ?_
    rw [← commuting_iff_le_centralizer]
    refine Commuting.symm ?_
    rw [commuting_iff_le_centralizer]
    refine iSup₂_le fun Y hY => ?_
    rw [← commuting_iff_le_centralizer]
    exact LeviQuot.commuting_quotMap
      (commuting_of_mem_deltaSet hS.hyp hS.mem hS.opp hB hX hY)
  have hsq : ∀ x ∈ T, x * x = 1 := by
    intro x hx
    have hx' := hx
    rw [hT, iSup_subtype'] at hx'
    refine (Subgroup.iSup_induction' (C := fun x _ => x ∈ T ∧ x * x = 1) _
      (fun i y hy => ⟨hgen i.1 i.2 hy, LeviQuot.mul_self_of_mem_quotMap hR i.2.1.1.1 hy⟩)
      ⟨T.one_mem, mul_one 1⟩ (fun y z _ _ hy hz => ⟨T.mul_mem hy.1 hz.1, ?_⟩) hx').2
    calc y * z * (y * z) = y * (z * y) * z := by group
      _ = y * (y * z) * z := by rw [(hcomm z hz.1 y hy.1).eq]
      _ = (y * y) * (z * z) := by group
      _ = 1 := by rw [hy.2, hz.2, one_mul]
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, SubgroupClass.coe_pow, pow_two]
  exact hsq x x.2

theorem conj_smul_eq_conjSub {H : Type*} [Group H] (P : Subgroup H) (g : H) :
    MulAut.conj g • P = conjSub P g := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_conjSub]
  simp [MulAut.smul_def, mul_assoc]

theorem exists_le_stabBar_of_isPGroup (hS : Sec13 R A A₀)
    {U : Subgroup (↥(levi R A A₀) ⧸ Subgroup.center ↥(levi R A A₀))} (hU : IsPGroup 2 U) :
    ∃ B ∈ lambdaStar R A A₀, U ≤ stabBar R A A₀ B := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B₁, hB₁⟩ := CaseD4.lambdaStar_nonempty hS.hyp hS.mem hS.opp
  set P := stabBar R A A₀ B₁ with hP
  set T := ⨆ X ∈ deltaSet R A A₀ B₁, quotMap (levi R A A₀) X with hT
  obtain ⟨S, hTS⟩ := (isPGroup_iSup_quotMap_deltaSet hS hB₁).exists_le_sylow
  have hTP : T ≤ P := iSup_quotMap_deltaSet_le_stabBar hS hB₁
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
    obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(levi R A A₀)) (s : _)
    have hsT : ∀ x ∈ T, (s : _) * x * (s : _)⁻¹ ∈ P := by
      intro x hx
      have hxQ : (⟨x, hTS hx⟩ : ↥(S : Subgroup _)) ∈ Q.subgroupOf S :=
        Subgroup.mem_subgroupOf.2 ⟨hTS hx, hTP hx⟩
      have := (Subgroup.mem_normalizer_iff.1 hsN _).1 hxQ
      exact (Subgroup.mem_subgroupOf.1 this).2
    have hC : conjSub B₁ (v : G) = B₁ := by
      refine eq_of_forall_quotMap_le_stabBar hS hB₁
        (conjSub_mem_lambdaStar_of_mem_levi hR hB₁ v.2) fun X hX => ?_
      rw [← conjSet_deltaSet hR v.2] at hX
      obtain ⟨Y, hY, rfl⟩ := hX
      rw [LeviQuot.quotMap_conjSub Y v.2]
      rintro _ ⟨y, hy, rfl⟩
      have hyT : y ∈ T := le_iSup₂_of_le
        (f := fun X (_ : X ∈ deltaSet R A A₀ B₁) => quotMap (levi R A A₀) X) Y hY le_rfl hy
      have e : (QuotientGroup.mk' (Subgroup.center ↥(levi R A A₀)) ⟨(v : G), v.2⟩) = s := hv
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e]
      exact hsT y hyT
    apply hsQ
    refine Subgroup.mem_subgroupOf.2 ⟨s.2, ?_⟩
    rw [← hv]
    exact (mk_mem_stabBar_iff hS hB₁ v).2 (conjSub_eq_self_iff.1 hC)
  obtain ⟨S', hUS'⟩ := hU.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    (↥(levi R A A₀) ⧸ Subgroup.center ↥(levi R A A₀)) S S'
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(levi R A A₀)) g
  refine ⟨conjSub B₁ (v : G), conjSub_mem_lambdaStar_of_mem_levi hR hB₁ v.2, ?_⟩
  rw [stabBar_conjSub hS hB₁ v, ← hP]
  refine hUS'.trans ?_
  rw [← hg, Sylow.coe_subgroup_smul, conj_smul_eq_conjSub]
  exact Subgroup.map_mono hSP

end ExclNS

end CFSG.Timmesfeld.ARS

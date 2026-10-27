module

public import CFSG.Quasithin.EmptyFaithful.E111RMemB
public import CFSG.Quasithin.EmptyFaithful.E111RSub

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB
open scoped commutatorElement

@[expose] def AutRankLe (n : ℕ) : GrpPred := fun J _ =>
  (∃ x : J, x ≠ 1 ∧ x ^ 2 = 1) ∧
    ∀ B : Subgroup (MulAut J), IsElemAbelian 2 B → Nat.card ↥B ≤ 2 ^ n

theorem autRank_bound_of_mulEquiv {n : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hr : ∀ B' : Subgroup (MulAut B), IsElemAbelian 2 B' → Nat.card ↥B' ≤ 2 ^ n) :
    ∀ B' : Subgroup (MulAut A), IsElemAbelian 2 B' → Nat.card ↥B' ≤ 2 ^ n := by
  intro B' hB'
  set f := (MulAut.congr e).toMonoidHom
  have hinj : Function.Injective f := (MulAut.congr e).injective
  rw [← Subgroup.card_map_of_injective hinj]
  refine hr _ ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha, hax⟩ := x.2
    obtain ⟨b, hb, hby⟩ := y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← hax, ← hby, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hB'.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hB'.2 a ha, map_one]

theorem autRankLe_isoInv (n : ℕ) : IsoInv (AutRankLe n) := by
  intro A B _ _ e ⟨⟨x, hx1, hx2⟩, hr⟩
  exact ⟨⟨e.symm x, fun h => hx1 (by simpa using congrArg e h), by
    rw [← map_pow, hx2, map_one]⟩, autRank_bound_of_mulEquiv e hr⟩

namespace E111R

variable {G : Type} [Group G] [Finite G]

namespace DiagSetting

variable {X T A S C : Subgroup G} (h : DiagSetting X T A S C) [Fintype ↥C]
include h

omit [Finite G] in
theorem commute_conj_diag_of_not_mem {z : G} (hzA : z ∈ A)
    (hz : z ∉ C ⊔ (A ⊓ Subgroup.normalizer (S : Set G))) (x y : ↥S) :
    Commute (z * diagHom S C h.diagComm x * z⁻¹) (diagHom S C h.diagComm y) := by
  refine commute_conj_diagHom h.diagComm (h.commute_of_ne fun c hc c' hc' heq => hz ?_) x y
  have hn : c'⁻¹ * (z * c) ∈ A ⊓ Subgroup.normalizer (S : Set G) := by
    refine ⟨A.mul_mem (A.inv_mem (h.CA hc')) (A.mul_mem hzA (h.CA hc)), ?_⟩
    apply mem_normalizer_of_conjSub_eq
    rw [A1b.conjSub_mul, heq, ← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]
  have hz' : z = c' * (c'⁻¹ * (z * c)) * c⁻¹ := by group
  rw [hz']
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hc')
    (Subgroup.mem_sup_right hn)) (Subgroup.mem_sup_left (C.inv_mem hc))

omit [Finite G] in
theorem not_mem_normalizer_diag {z : G} (hzA : z ∈ A)
    (hz : z ∉ C ⊔ (A ⊓ Subgroup.normalizer (S : Set G))) :
    z ∉ Subgroup.normalizer (diagSub S C h.diagComm : Set G) := by
  intro hzN
  obtain ⟨a, b, hab⟩ := h.diag_nonabelian
  apply hab
  obtain ⟨x, hx⟩ := a.2
  obtain ⟨y, hy⟩ := b.2
  have hza : z⁻¹ * (a : G) * z ∈ diagSub S C h.diagComm := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hzN) a).mp a.2
    simpa using this
  obtain ⟨w, hw⟩ := hza
  have h1 := h.commute_conj_diag_of_not_mem hzA hz w y
  rw [hw, hy] at h1
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  have e1 : z * (z⁻¹ * (a : G) * z) * z⁻¹ = a := by group
  rw [e1] at h1
  exact h1

omit [Finite G] in
theorem le_centralizer_diag_of_le {v : G} (hv : v ∈ A ⊓ Subgroup.normalizer (S : Set G))
    (hvc : v ∈ Subgroup.centralizer (S : Set G)) :
    v ∈ Subgroup.centralizer (diagSub S C h.diagComm : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨x, rfl⟩
  have h1 := conj_diagHom_of_comm h.diagComm x hv.2 fun c hc => h.comm hv.1 (h.CA hc)
  have h2 : (⟨v * x * v⁻¹, (Subgroup.mem_normalizer_iff.mp hv.2 x).mp x.2⟩ : ↥S) = x := by
    apply Subtype.ext
    simp only
    rw [(Subgroup.mem_centralizer_iff.mp hvc x x.2).symm, mul_inv_cancel_right]
  rw [h2] at h1
  calc diagHom S C h.diagComm x * v = v * diagHom S C h.diagComm x * v⁻¹ * v := by rw [h1]
    _ = v * diagHom S C h.diagComm x := by group

theorem eTwo_diagK
    (hcase : diagSub S C h.diagComm = ⁅diagSub S C h.diagComm, A⁆ ∨
      (¬ A ≤ Subgroup.normalizer (diagSub S C h.diagComm : Set G) ∧
        Nat.card ↥(E1.barRad ↥(diagK T A S C h.diagComm)
          (A.subgroupOf (diagK T A S C h.diagComm))) = 2)) :
    E1.ETwo ↥(diagK T A S C h.diagComm)
      ((T ⊓ diagK T A S C h.diagComm).subgroupOf (diagK T A S C h.diagComm))
      (A.subgroupOf (diagK T A S C h.diagComm)) := by
  set K := diagK T A S C h.diagComm with hK
  set E := diagE T A S C h.diagComm with hE
  set B₀ := T ⊓ Subgroup.centralizer (A : Set G) with hB₀
  have hDK : ∀ D ∈ diagFam T A S C h.diagComm, D ≤ K := fun D hD =>
    (le_sSup hD).trans h.diagE_le_diagK
  have hdK : diagSub S C h.diagComm ≤ K := h.diag_le_diagE.trans h.diagE_le_diagK
  set 𝒟' : Set (Subgroup ↥K) :=
    (fun D : Subgroup G => D.subgroupOf K) '' diagFam T A S C h.diagComm with h𝒟'
  have hsf : SemiFam 𝒟' := h.semiFam.subgroupOf hDK
  have hE' : sSup 𝒟' = E.subgroupOf K := sSup_image_subgroupOf hDK
  have hEn' : (sSup 𝒟').Normal := by
    rw [hE']
    exact h.normal_diagE
  have hC' : IsPGroup 2 ↥(Subgroup.centralizer ((sSup 𝒟' : Subgroup ↥K) : Set ↥K)) := by
    intro x
    have hx : (x : ↥K) ∈ Subgroup.centralizer ((E.subgroupOf K : Subgroup ↥K) : Set ↥K) :=
      hE' ▸ x.2
    rw [mem_centralizer_subgroupOf_iff h.diagE_le_diagK] at hx
    obtain ⟨m, hm⟩ := h.isPGroup_inf_centralizer ⟨((x : ↥K) : G), (x : ↥K).2, hx⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hm
  have hEB' : sSup 𝒟' ⊔ B₀.subgroupOf K = ⊤ := by
    rw [hE']
    exact h.sup_subgroupOf_eq_top
  have hB₀' : IsPGroup 2 ↥(B₀.subgroupOf K) :=
    (h.isPGroup_T.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe h.le_diagK).symm
  have hD₀' : (diagSub S C h.diagComm).subgroupOf K ∈ 𝒟' := ⟨_, h.diag_mem_diagFam, rfl⟩
  have hΓ : B₀.subgroupOf K ≤ E1.tauOf ⊤ ((T ⊓ K).subgroupOf K) (A.subgroupOf K) := by
    intro t ht
    rw [Subgroup.mem_subgroupOf] at ht
    rw [E1.mem_tauOf]
    refine ⟨Subgroup.mem_subgroupOf.mpr ⟨ht.1, t.2⟩, ?_, fun a ha => ?_⟩
    · have := pCoreOf_top_normal (G := ↥K)
      rw [Subgroup.normalizer_eq_top_iff.mpr this]
      exact Subgroup.mem_top t
    · have hc : (t : G) * a = a * t :=
        (Subgroup.mem_centralizer_iff.mp ht.2 a (Subgroup.mem_subgroupOf.mp ha)).symm
      have h1 : ⁅t, a⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact Subtype.ext hc
      rw [h1]
      exact Subgroup.one_mem _
  have htr : ⨆ (t : ↥K) (_ : t ∈ B₀.subgroupOf K),
      A1b.conjSub t ((diagSub S C h.diagComm).subgroupOf K) = sSup 𝒟' := by
    rw [hE']
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le h.diagE_le_diagK, h.diagE_eq, Subgroup.map_iSup]
    apply le_antisymm
    · refine iSup_le fun t => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun ht => ?_
      rw [conjSub_subgroupOf t hdK, Subgroup.map_subgroupOf_eq_of_le (conjSub_le_of_mem t.2 hdK)]
      exact le_iSup_of_le ⟨t, Subgroup.mem_subgroupOf.mp ht⟩ le_rfl
    · refine iSup_le fun g => ?_
      refine le_iSup_of_le ⟨g, h.le_diagK g.2⟩ ?_
      rw [Subgroup.map_iSup]
      refine le_iSup_of_le (Subgroup.mem_subgroupOf.mpr g.2) ?_
      rw [conjSub_subgroupOf _ hdK,
        Subgroup.map_subgroupOf_eq_of_le (conjSub_le_of_mem (h.le_diagK g.2) hdK)]
  have hcase' : (diagSub S C h.diagComm).subgroupOf K =
      ⁅(diagSub S C h.diagComm).subgroupOf K, A.subgroupOf K⁆ ∨
      (¬ A.subgroupOf K ≤ Subgroup.normalizer
        (((diagSub S C h.diagComm).subgroupOf K : Subgroup ↥K) : Set ↥K) ∧
        Nat.card ↥(E1.barRad ↥K (A.subgroupOf K)) = 2) := by
    rcases hcase with h1 | ⟨h1, h2⟩
    · left
      rw [commutator_subgroupOf hdK h.A_le_diagK, ← h1]
    · right
      refine ⟨fun hle => h1 fun a ha => ?_, h2⟩
      have h3 := hle (Subgroup.mem_subgroupOf.mpr ha : (⟨a, h.A_le_diagK ha⟩ : ↥K) ∈ A.subgroupOf K)
      rw [mem_normalizer_subgroupOf_iff, inf_eq_left.mpr hdK] at h3
      exact h3
  exact eTwo_of_semiFam hsf hEn' hC' hEB' hB₀' hD₀' hΓ htr hcase'

theorem le_normalizer_diag (hA : C ⊔ (A ⊓ Subgroup.normalizer (S : Set G)) = A) :
    A ≤ Subgroup.normalizer (diagSub S C h.diagComm : Set G) := by
  refine le_trans (le_of_eq hA.symm) (sup_le (fun c hc =>
    Subgroup.centralizer_le_normalizer _ (h.le_centralizer_diag hc)) fun v hv => ?_)
  exact mem_normalizer_of_conjSub_eq
    (h.conjSub_diag_of_comm hv.2 fun c hc => h.comm hv.1 (h.CA hc))

theorem diag_eq_commutator (hA : C ⊔ (A ⊓ Subgroup.normalizer (S : Set G)) = A)
    (hV : ¬ A ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G)) :
    diagSub S C h.diagComm = ⁅diagSub S C h.diagComm, A⁆ := by
  set D := diagSub S C h.diagComm with hD
  have hAN := h.le_normalizer_diag hA
  have hle : ⁅D, A⁆ ≤ D := Subgroup.commutator_le.mpr fun d hd a ha => by
    rw [commutatorElement_def]
    have := (Subgroup.mem_normalizer_iff.mp (hAN ha) d⁻¹).mp (D.inv_mem hd)
    have h2 := D.mul_mem hd this
    simpa [mul_assoc] using h2
  have := h.diag_simple
  have hn : ((⁅D, A⁆ : Subgroup G).subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (Subgroup.normalizer_commutator_ge_left D A)
  obtain ⟨v, hvV, hvS⟩ : ∃ v ∈ A ⊓ Subgroup.normalizer (S : Set G),
      v ∉ Subgroup.centralizer (S : Set G) := by
    by_contra hc
    push Not at hc
    exact hV hc
  have hvD : v ∉ Subgroup.centralizer (D : Set G) := by
    intro hvD
    apply hvS
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := conj_diagHom_of_comm h.diagComm ⟨x, hx⟩ hvV.2 fun c hc => h.comm hvV.1 (h.CA hc)
    have h2 : v * diagHom S C h.diagComm ⟨x, hx⟩ * v⁻¹ = diagHom S C h.diagComm ⟨x, hx⟩ := by
      rw [(Subgroup.mem_centralizer_iff.mp hvD _ ⟨_, rfl⟩).symm, mul_inv_cancel_right]
    rw [h2] at h1
    have h3 := congrArg Subtype.val (diagHom_injective h.diagComm h.center_trivial h1)
    simp only at h3
    calc x * v = v * x * v⁻¹ * v := by rw [← h3]
      _ = v * x := by group
  rw [Subgroup.mem_centralizer_iff] at hvD
  push Not at hvD
  obtain ⟨d, hd, hdv⟩ := hvD
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((⁅D, A⁆ : Subgroup G).subgroupOf D) with h1 | h1
  · exfalso
    rw [Subgroup.subgroupOf_eq_bot] at h1
    have hc : ⁅d, v⁆ ∈ ⁅D, A⁆ := Subgroup.commutator_mem_commutator hd hvV.1
    have h0 := (Subgroup.disjoint_def.mp h1) hc (hle hc)
    rw [commutatorElement_eq_one_iff_mul_comm] at h0
    exact hdv h0
  · exact le_antisymm (Subgroup.subgroupOf_eq_top.mp h1) hle

omit h [Finite G] [Fintype ↥C] in
theorem exists_not_mem (hidx : (C ⊔ (A ⊓ Subgroup.normalizer (S : Set G))).relIndex A = 2) :
    ∃ z ∈ A, z ∉ C ⊔ (A ⊓ Subgroup.normalizer (S : Set G)) := by
  by_contra hc
  push Not at hc
  rw [Subgroup.relIndex_eq_one.mpr hc] at hidx
  omega

omit [Finite G] in
theorem not_le_normalizer_diag
    (hidx : (C ⊔ (A ⊓ Subgroup.normalizer (S : Set G))).relIndex A = 2) :
    ¬ A ≤ Subgroup.normalizer (diagSub S C h.diagComm : Set G) := by
  intro hle
  obtain ⟨z, hzA, hz⟩ := exists_not_mem hidx
  exact h.not_mem_normalizer_diag hzA hz (hle hzA)

omit [Finite G] in
theorem centralizer_diagE_inf (hV : A ⊓ Subgroup.normalizer (S : Set G) ≤
      Subgroup.centralizer (S : Set G)) :
    Subgroup.centralizer (diagE T A S C h.diagComm : Set G) ⊓ A =
      C ⊔ (A ⊓ Subgroup.normalizer (S : Set G)) := by
  refine le_antisymm (fun a ha => ?_) (le_inf ?_ (sup_le h.CA inf_le_left))
  · by_contra hz
    have haD : a ∈ Subgroup.centralizer (diagSub S C h.diagComm : Set G) :=
      Subgroup.centralizer_le (fun x hx => h.diag_le_diagE hx) ha.1
    exact h.not_mem_normalizer_diag ha.2 hz (Subgroup.centralizer_le_normalizer _ haD)
  · refine sup_le (fun c hc => h.inf_centralizer_le ⟨h.CA hc, h.le_centralizer_diag hc⟩)
      fun v hv => h.inf_centralizer_le ⟨hv.1, h.le_centralizer_diag_of_le hv (hV hv)⟩

theorem solvableRadical_diagK :
    CFSG.solvableRadical ↥(diagK T A S C h.diagComm) =
      Subgroup.centralizer (((diagE T A S C h.diagComm).subgroupOf (diagK T A S C h.diagComm) :
        Subgroup ↥(diagK T A S C h.diagComm)) : Set ↥(diagK T A S C h.diagComm)) := by
  set K := diagK T A S C h.diagComm
  have hDK : ∀ D ∈ diagFam T A S C h.diagComm, D ≤ K := fun D hD =>
    (le_sSup hD).trans h.diagE_le_diagK
  have hsf := h.semiFam.subgroupOf hDK
  have hE' := sSup_image_subgroupOf hDK
  have hEn' :
      (sSup ((fun D : Subgroup G => D.subgroupOf K) '' diagFam T A S C h.diagComm)).Normal := by
    rw [hE']
    exact h.normal_diagE
  have hC' : IsPGroup 2 ↥(Subgroup.centralizer ((sSup ((fun D : Subgroup G => D.subgroupOf K) ''
      diagFam T A S C h.diagComm) : Subgroup ↥K) : Set ↥K)) := by
    intro x
    have hx : (x : ↥K) ∈ Subgroup.centralizer
        (((diagE T A S C h.diagComm).subgroupOf K : Subgroup ↥K) : Set ↥K) := hE' ▸ x.2
    rw [mem_centralizer_subgroupOf_iff h.diagE_le_diagK] at hx
    obtain ⟨m, hm⟩ := h.isPGroup_inf_centralizer ⟨((x : ↥K) : G), (x : ↥K).2, hx⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hm
  have := solvableRadical_eq hsf hEn' hC'
  rw [this, hE']
  rfl

theorem card_barRad_le_diagK {n : ℕ} (hA : C ⊔ (A ⊓ Subgroup.normalizer (S : Set G)) = A)
    (hrank : ∀ B' : Subgroup (MulAut ↥S), IsElemAbelian 2 B' → Nat.card ↥B' ≤ 2 ^ n) :
    Nat.card ↥(E1.barRad ↥(diagK T A S C h.diagComm)
      (A.subgroupOf (diagK T A S C h.diagComm))) ≤ 2 ^ n := by
  set K := diagK T A S C h.diagComm
  have hdK : diagSub S C h.diagComm ≤ K := h.diag_le_diagE.trans h.diagE_le_diagK
  have hAN := h.le_normalizer_diag hA
  have hBN : A.subgroupOf K ≤ Subgroup.normalizer
      (((diagSub S C h.diagComm).subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    intro a ha
    rw [mem_normalizer_subgroupOf_iff, inf_eq_left.mpr hdK]
    exact hAN (Subgroup.mem_subgroupOf.mp ha)
  have hB : IsElemAbelian 2 (A.subgroupOf K) := by
    refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · exact h.comm (Subgroup.mem_subgroupOf.mp x.2) (Subgroup.mem_subgroupOf.mp y.2)
    · have := h.elem.2 _ (Subgroup.mem_subgroupOf.mp hx)
      simpa using this
  have hBC : A.subgroupOf K ⊓ Subgroup.centralizer
      (((diagSub S C h.diagComm).subgroupOf K : Subgroup ↥K) : Set ↥K) ≤
      CFSG.solvableRadical ↥K := by
    rw [h.solvableRadical_diagK]
    intro x hx
    have hx1 : x ∈ A.subgroupOf K := hx.1
    have hx2 : x ∈ Subgroup.centralizer
        (((diagSub S C h.diagComm).subgroupOf K : Subgroup ↥K) : Set ↥K) := hx.2
    rw [mem_centralizer_subgroupOf_iff hdK] at hx2
    rw [mem_centralizer_subgroupOf_iff h.diagE_le_diagK]
    exact h.inf_centralizer_le ⟨Subgroup.mem_subgroupOf.mp hx1, hx2⟩
  have e : ↥((diagSub S C h.diagComm).subgroupOf K) ≃* ↥S :=
    (Subgroup.subgroupOfEquivOfLe hdK).trans h.diagEquiv.symm
  exact card_barRad_le hBN hB hBC (autRank_bound_of_mulEquiv e hrank)

theorem card_barRad_diagK_eq (hV : A ⊓ Subgroup.normalizer (S : Set G) ≤
      Subgroup.centralizer (S : Set G))
    (hidx : (C ⊔ (A ⊓ Subgroup.normalizer (S : Set G))).relIndex A = 2) :
    Nat.card ↥(E1.barRad ↥(diagK T A S C h.diagComm)
      (A.subgroupOf (diagK T A S C h.diagComm))) = 2 := by
  set K := diagK T A S C h.diagComm
  have hc : Subgroup.centralizer (((diagE T A S C h.diagComm).subgroupOf K : Subgroup ↥K) :
      Set ↥K) = (Subgroup.centralizer (diagE T A S C h.diagComm : Set G)).subgroupOf K := by
    ext x
    rw [mem_centralizer_subgroupOf_iff h.diagE_le_diagK, Subgroup.mem_subgroupOf]
  unfold E1.barRad
  rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', h.solvableRadical_diagK, hc,
    Subgroup.relIndex_subgroupOf h.A_le_diagK, ← Subgroup.inf_relIndex_right,
    h.centralizer_diagE_inf hV, hidx]

theorem isE_diagK {n : ℕ} (hn : 1 ≤ n)
    (hcase : (C ⊔ (A ⊓ Subgroup.normalizer (S : Set G)) = A ∧
        ¬ A ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G) ∧
        ∀ B' : Subgroup (MulAut ↥S), IsElemAbelian 2 B' → Nat.card ↥B' ≤ 2 ^ n) ∨
      (A ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G) ∧
        (C ⊔ (A ⊓ Subgroup.normalizer (S : Set G))).relIndex A = 2)) :
    E1.IsE n ⊤ T A (diagK T A S C h.diagComm) := by
  have hτ : E1.tauOf ⊤ T A ≤ T ⊓ diagK T A S C h.diagComm :=
    (tauOf_le (pCoreOf_two_eq_bot h.red) T A).trans (le_inf inf_le_left h.le_diagK)
  refine ⟨le_top, hτ, h.isSylowIn_diagK, Or.inr ?_⟩
  rcases hcase with ⟨hA, hV, hrank⟩ | ⟨hV, hidx⟩
  · exact ⟨h.eTwo_diagK (Or.inl (h.diag_eq_commutator hA hV)), h.card_barRad_le_diagK hA hrank⟩
  · have h2 := h.card_barRad_diagK_eq hV hidx
    refine ⟨h.eTwo_diagK (Or.inr ⟨h.not_le_normalizer_diag hidx, h2⟩), ?_⟩
    rw [h2]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

end DiagSetting

end E111R

end CFSG.Quasithin.E2.E22N

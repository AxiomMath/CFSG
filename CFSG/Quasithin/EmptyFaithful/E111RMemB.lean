module

public import CFSG.Quasithin.EmptyFaithful.E111RMemA
public import CFSG.Quasithin.Background.E1Sec6
public import CFSG.Quasithin.EmptyFaithful.E111RSemi

public section

namespace CFSG.Quasithin.E2.E22N.E111R

open CFSG.Open CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB

variable {G : Type} [Group G]

theorem conjSub_iSup {ι : Sort*} (g : G) (f : ι → Subgroup G) :
    A1b.conjSub g (⨆ i, f i) = ⨆ i, A1b.conjSub g (f i) := by
  unfold A1b.conjSub
  rw [Subgroup.map_iSup]

@[expose] noncomputable def diagE (T A S C : Subgroup G) [Fintype ↥C] (hC : DiagComm S C) :
    Subgroup G :=
  sSup (diagFam T A S C hC)

@[expose] noncomputable def diagK (T A S C : Subgroup G) [Fintype ↥C] (hC : DiagComm S C) :
    Subgroup G :=
  diagE T A S C hC ⊔ (T ⊓ Subgroup.centralizer (A : Set G))

theorem isSylowIn_inf_sup [Finite G] {T L₀ τ : Subgroup G} (hT2 : IsPGroup 2 T) (hτT : τ ≤ T)
    (hτN : τ ≤ Subgroup.normalizer (L₀ : Set G)) (hL : IsSylowIn 2 (T ⊓ L₀) L₀) :
    IsSylowIn 2 (T ⊓ (L₀ ⊔ τ)) (L₀ ⊔ τ) := by
  have hS₀T : T ⊓ L₀ ⊔ τ ≤ T := sup_le inf_le_left hτT
  have hS₀N : T ⊓ L₀ ⊔ τ ≤ Subgroup.normalizer (L₀ : Set G) :=
    sup_le (inf_le_right.trans Subgroup.le_normalizer) hτN
  have hS₀2 : IsPGroup 2 ↥(T ⊓ L₀ ⊔ τ) := hT2.to_le hS₀T
  have h1 : IsSylowIn 2 ((T ⊓ L₀ ⊔ τ) ⊓ L₀) L₀ :=
    E1.isSylowIn_two_of_le hL (le_inf le_sup_left inf_le_right) inf_le_right
      (hS₀2.to_le inf_le_left)
  have h2 := E1.isSylowIn_two_of_sup_inf hS₀N hS₀2 h1
  have heq : L₀ ⊔ (T ⊓ L₀ ⊔ τ) = L₀ ⊔ τ :=
    le_antisymm (sup_le le_sup_left (sup_le (inf_le_right.trans le_sup_left) le_sup_right))
      (sup_le_sup_left le_sup_right _)
  rw [heq] at h2
  exact E1.isSylowIn_two_of_le h2 (le_inf hS₀T h2.1) inf_le_right (hT2.to_le inf_le_left)

theorem inf_conjSub_of_eq {g : G} {H L : Subgroup G} (hH : A1b.conjSub g H = H) :
    H ⊓ A1b.conjSub g L = A1b.conjSub g (H ⊓ L) := by
  conv_lhs => rw [← hH]
  unfold A1b.conjSub
  rw [← Subgroup.map_inf _ _ _ (MulAut.conj g).injective]

namespace DiagSetting

variable {X T A S C : Subgroup G} (h : DiagSetting X T A S C) [Fintype ↥C]
include h

omit [Fintype ↥C] in
theorem isPGroup_T : IsPGroup 2 T := h.red.2.2.2.2.2.1.2.1

theorem diag_mem_diagFam : diagSub S C h.diagComm ∈ diagFam T A S C h.diagComm :=
  ⟨1, A1b.conjSub_one _⟩

theorem diagE_eq : diagE T A S C h.diagComm =
    ⨆ g : ↥(T ⊓ Subgroup.centralizer (A : Set G)), A1b.conjSub (g : G) (diagSub S C h.diagComm) :=
  sSup_range

theorem diag_le_diagE : diagSub S C h.diagComm ≤ diagE T A S C h.diagComm :=
  le_sSup h.diag_mem_diagFam

theorem diagE_le_diagK : diagE T A S C h.diagComm ≤ diagK T A S C h.diagComm := le_sup_left

theorem le_diagK : T ⊓ Subgroup.centralizer (A : Set G) ≤ diagK T A S C h.diagComm :=
  le_sup_right

theorem A_le_diagK : A ≤ diagK T A S C h.diagComm := by
  intro a ha
  refine h.le_diagK ⟨h.AT ha, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro b hb
  exact h.comm hb ha

theorem le_normalizer_diagE : T ⊓ Subgroup.centralizer (A : Set G) ≤
    Subgroup.normalizer (diagE T A S C h.diagComm : Set G) := by
  have key : ∀ t ∈ T ⊓ Subgroup.centralizer (A : Set G),
      A1b.conjSub t (diagE T A S C h.diagComm) ≤ diagE T A S C h.diagComm := by
    intro t ht
    rw [h.diagE_eq, conjSub_iSup]
    refine iSup_le fun g => ?_
    rw [← A1b.conjSub_mul]
    exact le_iSup_of_le ⟨t * g, Subgroup.mul_mem _ ht g.2⟩ le_rfl
  exact fun t ht => mem_normalizer_of_conjSub_le (key t ht) (key _ (Subgroup.inv_mem _ ht))

theorem diagK_le_normalizer :
    diagK T A S C h.diagComm ≤ Subgroup.normalizer (diagE T A S C h.diagComm : Set G) :=
  sup_le Subgroup.le_normalizer h.le_normalizer_diagE

theorem isSylowIn_diag [Finite G] :
    IsSylowIn 2 (T ⊓ diagSub S C h.diagComm) (diagSub S C h.diagComm) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := diagHom_injective h.diagComm h.center_trivial
  have hTS := isSylowIn_inf h.red h.comp
  set P := ((T ⊓ S).subgroupOf S).map (diagHom S C h.diagComm) with hP
  have hPD : P ≤ diagSub S C h.diagComm := Subgroup.map_le_range _ _
  have hPT : P ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    refine diagHom_mem_of h.diagComm x fun c hc => ?_
    have hxT : (x : G) ∈ T := (Subgroup.mem_subgroupOf.mp hx).1
    exact T.mul_mem (T.mul_mem (h.AT (h.CA hc)) hxT) (T.inv_mem (h.AT (h.CA hc)))
  have hcardP : Nat.card P = Nat.card ↥(T ⊓ S) := by
    rw [hP, Subgroup.card_map_of_injective hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hcardD : Nat.card ↥(diagSub S C h.diagComm) = Nat.card S :=
    (Nat.card_congr h.diagEquiv.toEquiv).symm
  have hPsyl : IsSylowIn 2 P (diagSub S C h.diagComm) := by
    refine isSylowIn_of_card_eq hPD ?_
    rw [hcardP, hcardD]
    exact hTS.card_eq
  exact E1.isSylowIn_two_of_le hPsyl (le_inf hPT hPD) inf_le_right
    (h.isPGroup_T.to_le inf_le_left)

theorem isSylowIn_conj_diag [Finite G] {g : G} (hg : g ∈ T) :
    IsSylowIn 2 (T ⊓ A1b.conjSub g (diagSub S C h.diagComm))
      (A1b.conjSub g (diagSub S C h.diagComm)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heq : T ⊓ A1b.conjSub g (diagSub S C h.diagComm) =
      A1b.conjSub g (T ⊓ diagSub S C h.diagComm) :=
    inf_conjSub_of_eq (conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hg))
  refine isSylowIn_of_card_eq inf_le_right ?_
  rw [heq, card_conjSub, card_conjSub, h.isSylowIn_diag.card_eq]

theorem isSylowIn_diagE [Finite G] :
    IsSylowIn 2 (T ⊓ diagE T A S C h.diagComm) (diagE T A S C h.diagComm) :=
  h.semiFam.isSylowIn h.isPGroup_T fun D' hD' => by
    obtain ⟨g, rfl⟩ := hD'
    exact h.isSylowIn_conj_diag g.2.1

theorem isSylowIn_diagK [Finite G] :
    IsSylowIn 2 (T ⊓ diagK T A S C h.diagComm) (diagK T A S C h.diagComm) :=
  isSylowIn_inf_sup h.isPGroup_T inf_le_left h.le_normalizer_diagE h.isSylowIn_diagE

theorem inf_centralizer_le : A ⊓ Subgroup.centralizer (diagSub S C h.diagComm : Set G) ≤
    Subgroup.centralizer (diagE T A S C h.diagComm : Set G) := by
  intro a ha
  have hle : diagE T A S C h.diagComm ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [h.diagE_eq]
    refine iSup_le fun g => ?_
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    rw [hb]
    have hag : Commute a (g : G) := Subgroup.mem_centralizer_iff.mp g.2.2 a ha.1
    have had : Commute a d := (Subgroup.mem_centralizer_iff.mp ha.2 d hd).symm
    exact (hag.mul_right had).mul_right hag.inv_right
  exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
    (Subgroup.mem_centralizer_iff.mp (hle hy) a (Set.mem_singleton a)).symm

theorem normal_diagE :
    ((diagE T A S C h.diagComm).subgroupOf (diagK T A S C h.diagComm)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.diagE_le_diagK).mpr h.diagK_le_normalizer

theorem sup_subgroupOf_eq_top :
    (diagE T A S C h.diagComm).subgroupOf (diagK T A S C h.diagComm) ⊔
      (T ⊓ Subgroup.centralizer (A : Set G)).subgroupOf (diagK T A S C h.diagComm) = ⊤ := by
  rw [← Subgroup.subgroupOf_sup h.diagE_le_diagK h.le_diagK]
  exact Subgroup.subgroupOf_self _

theorem isPGroup_inf_centralizer [Finite G] :
    IsPGroup 2 ↥(diagK T A S C h.diagComm ⊓
      Subgroup.centralizer (diagE T A S C h.diagComm : Set G)) := by
  intro x
  have hB : IsPGroup 2 ↥((T ⊓ Subgroup.centralizer (A : Set G)).subgroupOf
      (diagK T A S C h.diagComm)) :=
    (h.isPGroup_T.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe h.le_diagK).symm
  obtain ⟨m, hm⟩ := pow_mem_of_sup h.normal_diagE h.sup_subgroupOf_eq_top hB ⟨x, x.2.1⟩
  refine ⟨m, Subtype.ext ?_⟩
  have h1 : (x : G) ^ 2 ^ m ∈ sSup (diagFam T A S C h.diagComm) ⊓
      Subgroup.centralizer ((sSup (diagFam T A S C h.diagComm) : Subgroup G) : Set G) :=
    ⟨Subgroup.mem_subgroupOf.mp hm, Subgroup.pow_mem _ x.2.2 _⟩
  rw [inf_centralizer_eq_bot h.semiFam, Subgroup.mem_bot] at h1
  simpa using h1

end DiagSetting

end CFSG.Quasithin.E2.E22N.E111R

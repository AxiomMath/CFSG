module

public import CFSG.Quasithin.Background.F7Geometry
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

variable {G : Type*} [Group G]

namespace F7

theorem isPGroup_of_isElemAbelian {X : Subgroup G} (h : IsElemAbelian 2 X) : IsPGroup 2 X :=
  CFSG.Open.IsElemAbelian.isPGroup h

theorem normalizer_le_normalizer_centralizer (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ c ∈ Subgroup.centralizer (S : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := by
      have := (Subgroup.mem_normalizer_iff''.mp hg s).mp hs
      exact this
    have h2 := hc _ hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h2]
      _ = g * c * g⁻¹ * s := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key g hg c hc, fun hc => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hc

theorem conjSub_eq_of_mem {x : G} {H : Subgroup G} (hx : x ∈ H) : conjSub x H = H := by
  ext y
  rw [mem_conjSub]
  constructor
  · intro h
    have := H.mul_mem (H.mul_mem hx h) (H.inv_mem hx)
    simpa [mul_assoc] using this
  · intro h
    exact H.mul_mem (H.mul_mem (H.inv_mem hx) h) hx

theorem isElemAbelian_closure (S : Set G) (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (h2 : ∀ x ∈ S, x ^ 2 = 1) : IsElemAbelian 2 (Subgroup.closure S) := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S :=
    (Subgroup.closure_le _).mpr fun x hx => by
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      exact fun y hy => hc y hy x hx
  have hcomm : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    have hx' := (Subgroup.mem_centralizer_iff.mp (h1 hx))
    have : Subgroup.closure S ≤ Subgroup.centralizer {x} :=
      (Subgroup.closure_le _).mpr fun s hs => by
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (hx' s hs).symm
    exact (Subgroup.mem_centralizer_iff.mp (this hy)) x rfl
  refine isElemAbelian_iff.mpr ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h2 x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [Commute.mul_pow (hcomm x hx y hy), ihx, ihy, mul_one]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem commutator_self_eq_bot {X : Subgroup G} (h : IsElemAbelian 2 X) : ⁅X, X⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.mem_bot, commutatorElement_def]
  have := isElemAbelian_comm h hx hy
  rw [this]; group

theorem conjSub_eq_of_mem_normalizer {k : G} {V : Subgroup G}
    (hk : k ∈ Subgroup.normalizer (V : Set G)) : conjSub k V = V := by
  ext y
  rw [mem_conjSub]
  have := Subgroup.mem_normalizer_iff.mp (inv_mem hk) y
  simpa using this.symm

end F7

namespace CosetGeom

variable {G₀ G₁ G₂ T V : Subgroup G}

theorem dist_triangle (hG : G₀ = G₁ ⊔ G₂) (u v w : CosetGeom G₀ G₁ G₂) :
    dist u w ≤ dist u v + dist v w := (connected hG).dist_triangle

@[expose] noncomputable def Vv0 {G₀ G₁ : Subgroup G} (V : Subgroup G)
    (x : G₀ ⧸ G₁.subgroupOf G₀) : Subgroup G :=
  ⨆ (g : G₀) (_ : (g : G₀ ⧸ G₁.subgroupOf G₀) = x), conjSub (g : G) V

@[expose] noncomputable def Vv {G₀ G₁ G₂ : Subgroup G} (V : Subgroup G) :
    CosetGeom G₀ G₁ G₂ → Subgroup G
  | Sum.inl x => Vv0 V x
  | Sum.inr y => ⨆ (x : G₀ ⧸ G₁.subgroupOf G₀)
      (_ : (graph G₀ G₁ G₂).Adj (Sum.inr y) (Sum.inl x)), Vv0 V x

theorem Vv_inl (x : G₀ ⧸ G₁.subgroupOf G₀) :
    Vv V (Sum.inl x : CosetGeom G₀ G₁ G₂) = Vv0 V x := rfl

theorem Vv_inr (y : G₀ ⧸ G₂.subgroupOf G₀) :
    Vv V (Sum.inr y : CosetGeom G₀ G₁ G₂) = ⨆ (x : G₀ ⧸ G₁.subgroupOf G₀)
      (_ : (graph G₀ G₁ G₂).Adj (Sum.inr y) (Sum.inl x)), Vv0 V x := rfl

theorem Vv0_mk (hN : G₁ ≤ Subgroup.normalizer (V : Set G)) (g : G₀) :
    Vv0 V (g : G₀ ⧸ G₁.subgroupOf G₀) = conjSub (g : G) V := by
  refine le_antisymm (iSup₂_le fun g' hg' => ?_) (le_iSup₂_of_le g rfl le_rfl)
  have h1 : (g' : G₀)⁻¹ * g ∈ G₁.subgroupOf G₀ := QuotientGroup.eq.mp hg'
  rw [Subgroup.mem_subgroupOf] at h1
  have h2 : (g : G)⁻¹ * g' ∈ G₁ := by simpa [mul_assoc] using G₁.inv_mem h1
  have e : (g' : G) = g * ((g : G)⁻¹ * g') := by group
  rw [e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hN h2)]

theorem Vv0_smul (hN : G₁ ≤ Subgroup.normalizer (V : Set G)) (g : G₀)
    (x : G₀ ⧸ G₁.subgroupOf G₀) : Vv0 V (g • x) = conjSub (g : G) (Vv0 V x) := by
  induction x using QuotientGroup.induction_on with
  | H h =>
    rw [smul_coe_quot, Vv0_mk hN, Vv0_mk hN, Subgroup.coe_mul, conjSub_mul]

theorem Vv_smul (hN : G₁ ≤ Subgroup.normalizer (V : Set G)) (g : G₀)
    (γ : CosetGeom G₀ G₁ G₂) : Vv V (g • γ) = conjSub (g : G) (Vv V γ) := by
  cases γ with
  | inl x => exact Vv0_smul hN g x
  | inr y =>
    rw [smul_inr, Vv_inr, Vv_inr]
    apply le_antisymm
    · refine iSup₂_le fun x' hx' => ?_
      obtain ⟨x, rfl⟩ : ∃ x, x' = g • x := ⟨g⁻¹ • x', by simp⟩
      have hx : (graph G₀ G₁ G₂).Adj (Sum.inr y) (Sum.inl x) := (smul_adj g).mp hx'
      rw [Vv0_smul hN]
      exact conjSub_mono _ (le_iSup₂_of_le x hx le_rfl)
    · rw [conjSub_le_iff]
      refine iSup₂_le fun x hx => ?_
      rw [← conjSub_le_iff, ← Vv0_smul hN]
      exact le_iSup₂_of_le (g • x) ((smul_adj g).mpr hx) le_rfl

theorem Vv_smul_γ₀ (hN : G₁ ≤ Subgroup.normalizer (V : Set G)) (g : G₀) :
    Vv V (g • γ₀ G₀ G₁ G₂) = conjSub (g : G) V := by
  rw [smul_γ₀, Vv_inl]
  exact Vv0_mk hN g

theorem Vv_γ₀ (hN : G₁ ≤ Subgroup.normalizer (V : Set G)) :
    Vv V (γ₀ G₀ G₁ G₂) = V := by
  have := Vv_smul_γ₀ (G₂ := G₂) (G₀ := G₀) hN 1
  rwa [one_smul, Subgroup.coe_one, conjSub_one] at this

theorem stab_le_normalizer_Vv (hN : G₁ ≤ Subgroup.normalizer (V : Set G))
    (γ : CosetGeom G₀ G₁ G₂) : stab γ ≤ Subgroup.normalizer (Vv V γ : Set G) := by
  intro x hx
  obtain ⟨h, hxγ⟩ := mem_stab.mp hx
  apply mem_normalizer_of_conjSub_eq
  have := Vv_smul hN (⟨x, h⟩ : ↥G₀) γ
  rw [hxγ] at this
  exact this.symm

theorem mem_Γ0_iff_exists {δ : CosetGeom G₀ G₁ G₂} :
    δ ∈ Γ0 G₀ G₁ G₂ ↔ ∃ g : G₀, δ = g • γ₀ G₀ G₁ G₂ := by
  rw [← orbit_γ₀_eq_Γ0, MulAction.mem_orbit_iff]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, hg.symm⟩, fun ⟨g, hg⟩ => ⟨g, hg.symm⟩⟩

theorem Vv_γ₁ (h₂ : G₂ ≤ G₀) (hN : G₁ ≤ Subgroup.normalizer (V : Set G)) :
    Vv V (γ₁ G₀ G₁ G₂) = conjClosure V G₂ := by
  apply le_antisymm
  · refine iSup₂_le fun x hx => ?_
    obtain ⟨k, hk1, hk2⟩ := adj_inr_inl.mp hx
    have hkG₂ : (k : G) ∈ G₂ := by
      have := QuotientGroup.eq.mp hk2
      rw [mul_one, inv_mem_iff, Subgroup.mem_subgroupOf] at this
      exact this
    subst hk1
    rw [Vv0_mk hN]
    rintro _ ⟨z, hz, rfl⟩
    exact mem_conjClosure hkG₂ hz
  · refine conjClosure_le fun h hh z hz => ?_
    have hadj : (graph G₀ G₁ G₂).Adj (Sum.inr (1 : ↥G₀)) (Sum.inl ((⟨h, h₂ hh⟩ : ↥G₀) :
        G₀ ⧸ G₁.subgroupOf G₀)) := by
      refine adj_inr_inl.mpr ⟨⟨h, h₂ hh⟩, rfl, ?_⟩
      rw [QuotientGroup.eq, mul_one, inv_mem_iff, Subgroup.mem_subgroupOf]
      exact hh
    have : conjSub h V ≤ Vv V (γ₁ G₀ G₁ G₂) := by
      have := le_iSup₂_of_le (f := fun (x : G₀ ⧸ G₁.subgroupOf G₀)
        (_ : (graph G₀ G₁ G₂).Adj (Sum.inr (1 : ↥G₀)) (Sum.inl x)) => Vv0 V x) _ hadj le_rfl
      rw [Vv0_mk hN] at this
      exact this
    exact this (mul_mem_conjSub hz)

section Fin

variable [Finite G]

theorem pCoreOf_stab_inf_ballStab_le {β γ : CosetGeom G₀ G₁ G₂} (h : γ ∈ nbrs β) :
    pCoreOf 2 (stab β) ⊓ ballStab 1 γ ≤ pCoreOf 2 (stab β ⊓ stab γ) ⊓ ballStab 1 γ ∧
      pCoreOf 2 (stab β ⊓ stab γ) ⊓ ballStab 1 γ ≤ pCoreOf 2 (ballStab 1 γ) := by
  have hadj : (graph G₀ G₁ G₂).Adj β γ := h
  have hβ : ballStab 1 γ ≤ stab β :=
    ballStab_le_stab_of_dist_le (by rw [dist_comm]; exact (dist_eq_one_iff_adj.mpr hadj).le)
  have hγ : ballStab 1 γ ≤ stab γ := ballStab_le_stab 1 γ
  refine ⟨fun x hx => ⟨pCoreOf_inf_le (inf_le_left : stab β ⊓ stab γ ≤ stab β)
    ⟨hx.1, hβ hx.2, hγ hx.2⟩, hx.2⟩, ?_⟩
  refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
  refine le_normalizer_inf ?_ Subgroup.le_normalizer
  exact (le_inf hβ hγ).trans (le_normalizer_pCoreOf 2 _)

theorem pCoreOf_ballStab_le (hG : G₀ = G₁ ⊔ G₂) {n : ℕ} (hn : 0 < n)
    {α γ δ : CosetGeom G₀ G₁ G₂} (hγ : γ ∈ ballLT n α) (hδ : δ ∈ nbrs γ) :
    pCoreOf 2 (ballStab n α) ≤ pCoreOf 2 (ballStab 1 γ) ∧
      pCoreOf 2 (ballStab n α) ≤ pCoreOf 2 (stab γ ⊓ stab δ) := by
  have key : ∀ d : ℕ, ∀ γ : CosetGeom G₀ G₁ G₂, dist α γ = d → d < n →
      pCoreOf 2 (ballStab n α) ≤ pCoreOf 2 (ballStab 1 γ) := by
    intro d
    induction d with
    | zero =>
      intro γ hd _
      obtain rfl : α = γ := (dist_eq_zero_iff hG).mp hd
      exact pCoreOf_mono_of_le_normalizer (ballStab_antitone α (Nat.succ_le_of_lt hn))
        ((ballStab_le_stab 1 α).trans (le_normalizer_ballStab n α))
    | succ d ih =>
      intro γ hd hdn
      obtain ⟨β, hβ, hdβ⟩ := exists_adj_dist_eq hG hd
      have h1 : pCoreOf 2 (ballStab n α) ≤ pCoreOf 2 (ballStab 1 β) := ih β hdβ (by omega)
      have h2 : pCoreOf 2 (ballStab 1 β) ≤ pCoreOf 2 (stab β) :=
        pCoreOf_mono_of_le_normalizer (ballStab_le_stab 1 β) (le_normalizer_ballStab 1 β)
      have h3 : pCoreOf 2 (ballStab n α) ≤ ballStab 1 γ := by
        refine (pCoreOf_le 2 _).trans ?_
        intro x hx
        refine mem_ballStab.mpr fun δ hδ => mem_ballStab.mp hx δ ?_
        have := dist_triangle hG α γ δ
        omega
      have h4 := pCoreOf_stab_inf_ballStab_le (β := β) (γ := γ) hβ.symm
      intro x hx
      exact h4.2 (h4.1 ⟨h2 (h1 hx), h3 hx⟩)
  have h1 := key (dist α γ) γ rfl hγ
  refine ⟨h1, h1.trans ?_⟩
  have hadj : (graph G₀ G₁ G₂).Adj γ δ := hδ
  have hle : ballStab 1 γ ≤ stab γ ⊓ stab δ :=
    le_inf (ballStab_le_stab 1 γ) (ballStab_le_stab_of_dist_le (dist_eq_one_iff_adj.mpr hadj).le)
  exact pCoreOf_mono_of_le_normalizer hle (inf_le_left.trans (le_normalizer_ballStab 1 γ))

structure _root_.CFSG.Quasithin.AmalgamHypV (G₀ G₁ G₂ T V : Subgroup G) : Prop
    extends AmalgamHyp G₀ G₁ G₂ T where
  reduced : IsTwoReducedIn G₁ V
  cT : T ⊓ Subgroup.centralizer (V : Set G) =
    pCoreOf 2 (G₁ ⊓ Subgroup.centralizer (V : Set G))

omit [Finite G] in
theorem _root_.CFSG.Quasithin.AmalgamHypV.V_le (h : AmalgamHypV G₀ G₁ G₂ T V) : V ≤ G₁ :=
  h.reduced.1

omit [Finite G] in
theorem _root_.CFSG.Quasithin.AmalgamHypV.normalizes (h : AmalgamHypV G₀ G₁ G₂ T V) :
    G₁ ≤ Subgroup.normalizer (V : Set G) := h.reduced.2.1

omit [Finite G] in
theorem _root_.CFSG.Quasithin.AmalgamHypV.elemAbelian (h : AmalgamHypV G₀ G₁ G₂ T V) :
    IsElemAbelian 2 V := h.reduced.2.2.1

omit [Finite G] in
theorem _root_.CFSG.Quasithin.AmalgamHypV.isPGroup (h : AmalgamHypV G₀ G₁ G₂ T V) :
    IsPGroup 2 V := isPGroup_of_isElemAbelian h.elemAbelian

omit [Finite G] in
theorem exists_isSylowTwoOf_stab_inf (hyp : AmalgamHyp G₀ G₁ G₂ T) {α β : CosetGeom G₀ G₁ G₂}
    (h : (graph G₀ G₁ G₂).Adj α β) :
    ∃ S : Subgroup G, IsSylowTwoOf S (stab α) ∧ S ≤ stab α ⊓ stab β := by
  have h₁ := hyp.le₁
  have h₂ := hyp.le₂
  obtain ⟨g, ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩⟩ := exists_smul_edge h
  · refine ⟨conjSub (g : G) T, ?_, ?_⟩
    · rw [← hg1, stab_smul, stab_γ₀ h₁]
      exact isSylowTwoOf_conj hyp.sylow₁ _
    · rw [← hg1, ← hg2, stab_smul, stab_smul, stab_γ₀ h₁, stab_γ₁ h₂, ← conjSub_inf]
      exact conjSub_mono _ hyp.T_le
  · refine ⟨conjSub (g : G) T, ?_, ?_⟩
    · rw [← hg2, stab_smul, stab_γ₁ h₂]
      exact isSylowTwoOf_conj hyp.sylow₂ _
    · rw [← hg2, ← hg1, stab_smul, stab_smul, stab_γ₀ h₁, stab_γ₁ h₂, inf_comm, ← conjSub_inf]
      exact conjSub_mono _ hyp.T_le

theorem pCoreOf_stab_eq (hyp : AmalgamHyp G₀ G₁ G₂ T) {α β : CosetGeom G₀ G₁ G₂}
    (h : β ∈ nbrs α) :
    pCoreOf 2 (stab α) = pCoreOf 2 (stab α ⊓ stab β) ⊓ ballStab 1 α := by
  have hadj : (graph G₀ G₁ G₂).Adj α β := h
  obtain ⟨S, hS, hSle⟩ := exists_isSylowTwoOf_stab_inf hyp hadj
  have hle : pCoreOf 2 (stab α) ≤ pCoreOf 2 (stab α ⊓ stab β) :=
    pCoreOf_le_pCoreOf_of_isSylowTwoOf hS hSle inf_le_left
  have hle2 : pCoreOf 2 (stab α) ≤ ballStab 1 α := by
    rw [ballStab_one_eq_coreIn hyp.gen hadj]
    exact le_coreIn (pCoreOf_le 2 _) (le_normalizer_pCoreOf 2 _) (hle.trans (pCoreOf_le 2 _))
  refine le_antisymm (le_inf hle hle2) ?_
  have h4 := (pCoreOf_stab_inf_ballStab_le (β := β) (γ := α) hadj.symm).2
  rw [inf_comm (stab β) (stab α)] at h4
  exact h4.trans (pCoreOf_mono_of_le_normalizer (ballStab_le_stab 1 α) (le_normalizer_ballStab 1 α))

theorem pCoreOf_stab_le_ballStab_one (hyp : AmalgamHyp G₀ G₁ G₂ T) (α : CosetGeom G₀ G₁ G₂) :
    pCoreOf 2 (stab α) ≤ ballStab 1 α := by
  obtain ⟨β, hβ⟩ := exists_adj α
  rw [pCoreOf_stab_eq hyp hβ]
  exact inf_le_right

omit [Finite G] in
theorem le_normalizer_inf_centralizer (hyp : AmalgamHypV G₀ G₁ G₂ T V) :
    G₁ ≤ Subgroup.normalizer ((G₁ ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
  le_normalizer_inf Subgroup.le_normalizer
    (hyp.normalizes.trans (normalizer_le_normalizer_centralizer V))

theorem pCoreOf_eq_inf_centralizer (hyp : AmalgamHypV G₀ G₁ G₂ T V) :
    pCoreOf 2 G₁ = T ⊓ Subgroup.centralizer (V : Set G) := by
  rw [hyp.cT]
  apply le_antisymm
  · have hD : pCoreOf 2 G₁ ≤ Subgroup.centralizer (V : Set G) := by
      refine hyp.reduced.2.2.2 (pCoreOf 2 G₁) (pCoreOf_le 2 G₁) (le_normalizer_pCoreOf 2 G₁) ?_
      intro d hd
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 G₁ ⟨d, hd⟩
      have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      exact ⟨k, by rw [this]; exact Subgroup.one_mem _⟩
    exact le_pCoreOf_of_le_normalizer 2 (le_inf (pCoreOf_le 2 G₁) hD)
      (inf_le_left.trans (le_normalizer_pCoreOf 2 G₁)) (pCoreOf_isPGroup 2 G₁)
  · exact pCoreOf_mono_of_le_normalizer inf_le_left (le_normalizer_inf_centralizer hyp)

omit [Finite G] in
theorem ballStab_one_γ₀_le (hyp : AmalgamHyp G₀ G₁ G₂ T) :
    ballStab 1 (γ₀ G₀ G₁ G₂) ≤ G₁ := by
  have := ballStab_le_stab 1 (γ₀ G₀ G₁ G₂)
  rwa [stab_γ₀ hyp.le₁] at this

omit [Finite G] in
theorem le_normalizer_ballStab_γ₀ (hyp : AmalgamHyp G₀ G₁ G₂ T) (n : ℕ) :
    G₁ ≤ Subgroup.normalizer (ballStab n (γ₀ G₀ G₁ G₂) : Set G) := by
  have := le_normalizer_ballStab n (γ₀ G₀ G₁ G₂)
  rwa [stab_γ₀ hyp.le₁] at this

theorem oTwoPrime_centralizer_eq_pCoreOf (hyp : AmalgamHypV G₀ G₁ G₂ T V) :
    oTwoPrime (G₁ ⊓ Subgroup.centralizer (V : Set G)) = pCoreOf 2 (ballStab 1 (γ₀ G₀ G₁ G₂)) ∧
      pCoreOf 2 (ballStab 1 (γ₀ G₀ G₁ G₂)) = pCoreOf 2 G₁ := by
  have hQ := pCoreOf_eq_inf_centralizer hyp
  have hQ₂ : pCoreOf 2 G₁ ≤ G₁ ⊓ G₂ :=
    le_inf (pCoreOf_le 2 G₁) (by rw [hQ]; exact inf_le_left.trans hyp.sylow₂.1)
  have hQball : pCoreOf 2 G₁ ≤ ballStab 1 (γ₀ G₀ G₁ G₂) :=
    ((ballStab_one_γ₀ hyp.gen).2.2) ⟨hQ₂, le_normalizer_pCoreOf 2 G₁⟩
  have hbG := ballStab_one_γ₀_le hyp.toAmalgamHyp
  have hball : pCoreOf 2 (ballStab 1 (γ₀ G₀ G₁ G₂)) = pCoreOf 2 G₁ := by
    apply le_antisymm
    · exact pCoreOf_mono_of_le_normalizer hbG (le_normalizer_ballStab_γ₀ hyp.toAmalgamHyp 1)
    · exact le_pCoreOf_of_le_normalizer 2 hQball (hbG.trans (le_normalizer_pCoreOf 2 G₁))
        (pCoreOf_isPGroup 2 G₁)
  refine ⟨?_, hball⟩
  have hsyl : IsSylowTwoOf (pCoreOf 2 G₁) (G₁ ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [hQ]
    have := isSylowTwoOf_inf_normal hyp.sylow₁
      (N := G₁ ⊓ Subgroup.centralizer (V : Set G)) inf_le_left
      (hyp.sylow₁.1.trans (le_normalizer_inf_centralizer hyp))
    rwa [← inf_assoc, inf_eq_left.mpr hyp.sylow₁.1] at this
  rw [oTwoPrime_eq_of_normal_sylow hsyl (inf_le_left.trans (le_normalizer_pCoreOf 2 G₁)), hball]

@[expose] noncomputable def critDist (G₀ G₁ G₂ V : Subgroup G) : ℕ :=
  sSup {n : ℕ | 0 < n ∧ V ≤ ballStab n (γ₀ G₀ G₁ G₂)}

omit [Finite G] in
theorem V_le_pCoreOf (hyp : AmalgamHypV G₀ G₁ G₂ T V) : V ≤ pCoreOf 2 G₁ :=
  le_pCoreOf_of_le_normalizer 2 hyp.V_le hyp.normalizes hyp.isPGroup

theorem V_le_ballStab_one (hyp : AmalgamHypV G₀ G₁ G₂ T V) :
    V ≤ ballStab 1 (γ₀ G₀ G₁ G₂) :=
  (V_le_pCoreOf hyp).trans (((oTwoPrime_centralizer_eq_pCoreOf hyp).2.symm ▸ le_rfl :
    pCoreOf 2 G₁ ≤ pCoreOf 2 (ballStab 1 (γ₀ G₀ G₁ G₂))).trans (pCoreOf_le 2 _))

theorem critDist_spec (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) :
    0 < critDist G₀ G₁ G₂ V ∧ V ≤ ballStab (critDist G₀ G₁ G₂ V) (γ₀ G₀ G₁ G₂) ∧
      ¬ V ≤ ballStab (critDist G₀ G₁ G₂ V + 1) (γ₀ G₀ G₁ G₂) := by
  set S := {n : ℕ | 0 < n ∧ V ≤ ballStab n (γ₀ G₀ G₁ G₂)} with hS
  have hne : S.Nonempty := ⟨1, Nat.one_pos, V_le_ballStab_one hyp⟩
  obtain ⟨n, -, hbot⟩ := exists_ballStab_eq_bot hyp.toAmalgamHyp
  have hbdd : BddAbove S := by
    refine ⟨n, fun m hm => ?_⟩
    by_contra hlt
    push Not at hlt
    have : V ≤ ballStab n (γ₀ G₀ G₁ G₂) := hm.2.trans (ballStab_antitone _ hlt.le)
    rw [hbot] at this
    exact hV (le_bot_iff.mp this)
  have hmem : sSup S ∈ S := Nat.sSup_mem hne hbdd
  refine ⟨hmem.1, hmem.2, fun h => ?_⟩
  have hb : critDist G₀ G₁ G₂ V = sSup S := rfl
  have : critDist G₀ G₁ G₂ V + 1 ∈ S := ⟨Nat.succ_pos _, h⟩
  have := le_csSup hbdd this
  omega

theorem le_critDist (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) {m : ℕ} (hm : 0 < m)
    (h : V ≤ ballStab m (γ₀ G₀ G₁ G₂)) : m ≤ critDist G₀ G₁ G₂ V := by
  obtain ⟨n, -, hbot⟩ := exists_ballStab_eq_bot hyp.toAmalgamHyp
  have hbdd : BddAbove {n : ℕ | 0 < n ∧ V ≤ ballStab n (γ₀ G₀ G₁ G₂)} := by
    refine ⟨n, fun m hm => ?_⟩
    by_contra hlt
    push Not at hlt
    have : V ≤ ballStab n (γ₀ G₀ G₁ G₂) := hm.2.trans (ballStab_antitone _ hlt.le)
    rw [hbot] at this
    exact hV (le_bot_iff.mp this)
  exact le_csSup hbdd ⟨hm, h⟩

theorem V_le_stab_of_dist_le (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    {δ : CosetGeom G₀ G₁ G₂} (h : dist (γ₀ G₀ G₁ G₂) δ ≤ critDist G₀ G₁ G₂ V) : V ≤ stab δ :=
  (critDist_spec hyp hV).2.1.trans (ballStab_le_stab_of_dist_le h)

theorem V_le_pCoreOf_of_dist_lt (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    {γ δ : CosetGeom G₀ G₁ G₂} (hγ : γ ∈ ballLT (critDist G₀ G₁ G₂ V) (γ₀ G₀ G₁ G₂))
    (hδ : δ ∈ nbrs γ) :
    V ≤ pCoreOf 2 (ballStab 1 γ) ∧ V ≤ pCoreOf 2 (stab γ ⊓ stab δ) := by
  obtain ⟨hb0, hVb, -⟩ := critDist_spec hyp hV
  have hV2 : V ≤ pCoreOf 2 (ballStab (critDist G₀ G₁ G₂ V) (γ₀ G₀ G₁ G₂)) :=
    le_pCoreOf_of_le_normalizer 2 hVb
      ((ballStab_le_stab _ _).trans ((stab_γ₀ hyp.le₁).le.trans hyp.normalizes)) hyp.isPGroup
  have := pCoreOf_ballStab_le hyp.gen hb0 hγ hδ
  exact ⟨hV2.trans this.1, hV2.trans this.2⟩

theorem exists_dist_eq_critDist_not_le (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) :
    ∃ α : CosetGeom G₀ G₁ G₂, dist (γ₀ G₀ G₁ G₂) α = critDist G₀ G₁ G₂ V ∧
      ¬ V ≤ ballStab 1 α := by
  obtain ⟨hb0, hVb, hVb1⟩ := critDist_spec hyp hV
  have : ∃ β : CosetGeom G₀ G₁ G₂, dist (γ₀ G₀ G₁ G₂) β ≤ critDist G₀ G₁ G₂ V + 1 ∧
      ¬ V ≤ stab β := by
    by_contra hcon
    push Not at hcon
    exact hVb1 (fun x hx => mem_ballStab.mpr fun β hβ => hcon β hβ hx)
  obtain ⟨β, hβ1, hβ2⟩ := this
  have hβ : dist (γ₀ G₀ G₁ G₂) β = critDist G₀ G₁ G₂ V + 1 := by
    by_contra hne
    exact hβ2 (V_le_stab_of_dist_le hyp hV (by omega))
  obtain ⟨α, hαβ, hα⟩ := exists_adj_dist_eq hyp.gen hβ
  refine ⟨α, hα, fun hle => hβ2 ?_⟩
  have hadj : (graph G₀ G₁ G₂).Adj α β := hαβ.symm
  exact hle.trans (ballStab_le_stab_of_dist_le (dist_eq_one_iff_adj.mpr hadj).le)

theorem isLeast_critDist (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) :
    IsLeast {n : ℕ | ∃ γ ∈ sphere n (γ₀ G₀ G₁ G₂), ¬ V ≤ ballStab 1 γ} (critDist G₀ G₁ G₂ V) := by
  refine ⟨?_, fun n ⟨γ, hγ, hVγ⟩ => ?_⟩
  · obtain ⟨α, hα, hVα⟩ := exists_dist_eq_critDist_not_le hyp hV
    exact ⟨α, hα, hVα⟩
  · by_contra hlt
    push Not at hlt
    obtain ⟨δ, hδ⟩ := exists_adj γ
    have hγ' : γ ∈ ballLT (critDist G₀ G₁ G₂ V) (γ₀ G₀ G₁ G₂) := by
      show dist (γ₀ G₀ G₁ G₂) γ < _
      have : dist (γ₀ G₀ G₁ G₂) γ = n := hγ
      omega
    exact hVγ ((V_le_pCoreOf_of_dist_lt hyp hV hγ' hδ).1.trans
      ((pCoreOf_le 2 _)))

theorem V_le_ballStab_one_of_W0 (hyp : AmalgamHyp G₀ G₁ G₂ T) (hV2 : IsPGroup 2 V)
    {γ' : CosetGeom G₀ G₁ G₂} (hT : IsSylowTwoOf T (stab γ')) (g : G₀)
    (hW : weakClosureW0 T V ≤ pCoreOf 2 (stab γ')) (hVγ : V ≤ stab (g • γ')) :
    V ≤ ballStab 1 (g • γ') := by
  rw [stab_smul] at hVγ
  have hP : conjSub (g : G)⁻¹ V ≤ stab γ' := (conjSub_le_iff _).mpr (by rwa [inv_inv])
  obtain ⟨x, hx, hle⟩ := isSylowTwoOf_exists_conj_le hT hP (isPGroup_conjSub hV2)
  have h1 : V ≤ conjSub ((g : G) * x) T := by
    have := conjSub_mono (g : G) hle
    rwa [conjSub_inv_conjSub, ← conjSub_mul] at this
  have h2 : conjSub ((g : G) * x)⁻¹ V ≤ weakClosureW0 T V :=
    conjSub_le_weakClosureW0 ((conjSub_le_iff _).mpr (by simpa using h1))
  have h3 : V ≤ conjSub ((g : G) * x) (pCoreOf 2 (stab γ')) := by
    rw [le_conjSub_iff]
    exact h2.trans hW
  have h4 : conjSub ((g : G) * x) (stab γ') = stab (g • γ') := by
    rw [conjSub_mul, F7.conjSub_eq_of_mem hx, stab_smul]
  rw [← pCoreOf_conjSub, h4] at h3
  exact h3.trans (pCoreOf_stab_le_ballStab_one hyp _)

omit [Finite G] in
theorem walk_parity {u v : CosetGeom G₀ G₁ G₂} (p : (graph G₀ G₁ G₂).Walk u v) :
    (vtype u = vtype v ↔ Even p.length) := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    have hab := vtype_ne_of_adj h
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ← ih]
    revert hab
    cases vtype a <;> cases vtype b <;> cases vtype c <;> simp

omit [Finite G] in
theorem vtype_eq_iff_even_dist (hG : G₀ = G₁ ⊔ G₂) (u v : CosetGeom G₀ G₁ G₂) :
    vtype u = vtype v ↔ Even (dist u v) := by
  obtain ⟨p, hp⟩ := (connected hG).exists_walk_length_eq_dist u v
  have : dist u v = p.length := hp.symm
  rw [this]
  exact walk_parity p

omit [Finite G] in
theorem vtype_eq_false_of_even (hG : G₀ = G₁ ⊔ G₂) {γ : CosetGeom G₀ G₁ G₂}
    (h : Even (dist (γ₀ G₀ G₁ G₂) γ)) : vtype γ = false := by
  have := (vtype_eq_iff_even_dist hG (γ₀ G₀ G₁ G₂) γ).mpr h
  rw [vtype_γ₀] at this
  exact this.symm

omit [Finite G] in
theorem vtype_eq_true_of_odd (hG : G₀ = G₁ ⊔ G₂) {γ : CosetGeom G₀ G₁ G₂}
    (h : Odd (dist (γ₀ G₀ G₁ G₂) γ)) : vtype γ = true := by
  have h' : ¬ Even (dist (γ₀ G₀ G₁ G₂) γ) := Nat.not_even_iff_odd.mpr h
  have := (vtype_eq_iff_even_dist hG (γ₀ G₀ G₁ G₂) γ).not.mpr h'
  rw [vtype_γ₀] at this
  cases hv : vtype γ
  · exact absurd hv.symm this
  · rfl

theorem even_critDist_of_weakClosureW0_le_G₂ (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    (hW : weakClosureW0 T V ≤ pCoreOf 2 G₂) : Even (critDist G₀ G₁ G₂ V) := by
  obtain ⟨γ, hγ, hVγ⟩ := exists_dist_eq_critDist_not_le hyp hV
  by_contra hodd
  have hvt : vtype γ = true :=
    vtype_eq_true_of_odd hyp.gen (by rw [hγ]; exact Nat.not_even_iff_odd.mp hodd)
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hvt
  apply hVγ
  rw [hg]
  refine V_le_ballStab_one_of_W0 hyp.toAmalgamHyp hyp.isPGroup (γ' := γ₁ G₀ G₁ G₂) ?_ g ?_ ?_
  · rw [stab_γ₁ hyp.le₂]; exact hyp.sylow₂
  · rw [stab_γ₁ hyp.le₂]; exact hW
  · rw [← hg]; exact V_le_stab_of_dist_le hyp hV hγ.le

theorem odd_critDist_of_weakClosureW0_le_G₁ (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    (hW : weakClosureW0 T V ≤ pCoreOf 2 G₁) : Odd (critDist G₀ G₁ G₂ V) := by
  obtain ⟨γ, hγ, hVγ⟩ := exists_dist_eq_critDist_not_le hyp hV
  by_contra hodd
  have hvt : vtype γ = false :=
    vtype_eq_false_of_even hyp.gen (by rw [hγ]; exact Nat.not_odd_iff_even.mp hodd)
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hvt
  apply hVγ
  rw [hg]
  refine V_le_ballStab_one_of_W0 hyp.toAmalgamHyp hyp.isPGroup (γ' := γ₀ G₀ G₁ G₂) ?_ g ?_ ?_
  · rw [stab_γ₀ hyp.le₁]; exact hyp.sylow₁
  · rw [stab_γ₀ hyp.le₁]; exact hW
  · rw [← hg]; exact V_le_stab_of_dist_le hyp hV hγ.le

theorem critDist_mod_two_of_weakClosureW0_le (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    (i : Fin 2)
    (hW : weakClosureW0 T V ≤
      pCoreOf 2 (stab (if i = 0 then γ₀ G₀ G₁ G₂ else γ₁ G₀ G₁ G₂))) :
    critDist G₀ G₁ G₂ V % 2 = (i.val + 1) % 2 := by
  fin_cases i
  · simp only [Fin.zero_eta, ite_true, stab_γ₀ hyp.le₁] at hW
    have := odd_critDist_of_weakClosureW0_le_G₁ hyp hV hW
    simpa using Nat.odd_iff.mp this
  · simp only [Fin.mk_one, one_ne_zero, ite_false, stab_γ₁ hyp.le₂] at hW
    have := even_critDist_of_weakClosureW0_le_G₂ hyp hV hW
    simpa using Nat.even_iff.mp this

theorem V_le_stab_of_mem_walk_support (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    {δ : CosetGeom G₀ G₁ G₂} (p : (graph G₀ G₁ G₂).Walk (γ₀ G₀ G₁ G₂) δ)
    (hp : p.length ≤ critDist G₀ G₁ G₂ V) {v : CosetGeom G₀ G₁ G₂} (hv : v ∈ p.support) :
    V ≤ stab v := by
  classical
  refine V_le_stab_of_dist_le hyp hV ?_
  have h1 : dist (γ₀ G₀ G₁ G₂) v ≤ (p.takeUntil v hv).length := SimpleGraph.dist_le _
  have h2 := SimpleGraph.Walk.length_takeUntil_le_length p hv
  omega

theorem conjSub_V_le_pCoreOf (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) (g : G₀)
    {γ δ : CosetGeom G₀ G₁ G₂} (hγ : dist (g • γ₀ G₀ G₁ G₂) γ < critDist G₀ G₁ G₂ V)
    (hδ : δ ∈ nbrs γ) :
    conjSub (g : G) V ≤ pCoreOf 2 (ballStab 1 γ) ∧
      conjSub (g : G) V ≤ pCoreOf 2 (stab γ ⊓ stab δ) := by
  have hγ' : g⁻¹ • γ ∈ ballLT (critDist G₀ G₁ G₂ V) (γ₀ G₀ G₁ G₂) := by
    show dist (γ₀ G₀ G₁ G₂) (g⁻¹ • γ) < _
    have := dist_smul g (γ₀ G₀ G₁ G₂) (g⁻¹ • γ)
    rw [smul_inv_smul] at this
    rw [← this]; exact hγ
  have hδ' : g⁻¹ • δ ∈ nbrs (g⁻¹ • γ) := (smul_adj g⁻¹).mpr hδ
  obtain ⟨h1, h2⟩ := V_le_pCoreOf_of_dist_lt hyp hV hγ' hδ'
  constructor
  · have := conjSub_mono (g : G) h1
    rwa [← pCoreOf_conjSub, ← ballStab_smul, smul_inv_smul] at this
  · have := conjSub_mono (g : G) h2
    rwa [← pCoreOf_conjSub, conjSub_inf, ← stab_smul, ← stab_smul, smul_inv_smul,
      smul_inv_smul] at this

theorem pCoreOf_le_centralizer (hyp : AmalgamHypV G₀ G₁ G₂ T V) :
    pCoreOf 2 G₁ ≤ Subgroup.centralizer (V : Set G) := by
  rw [pCoreOf_eq_inf_centralizer hyp]
  exact inf_le_right

theorem commutator_V_Vv_eq_bot (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    {δ : CosetGeom G₀ G₁ G₂} (hδ : δ ∈ Γ0 G₀ G₁ G₂)
    (hd : dist (γ₀ G₀ G₁ G₂) δ < critDist G₀ G₁ G₂ V) : ⁅V, Vv V δ⁆ = ⊥ := by
  obtain ⟨g, rfl⟩ := mem_Γ0_iff_exists.mp hδ
  rw [Vv_smul_γ₀ hyp.normalizes]
  obtain ⟨nb, hnb⟩ := exists_adj (γ₀ G₀ G₁ G₂)
  have h1 := (conjSub_V_le_pCoreOf hyp hV g (γ := γ₀ G₀ G₁ G₂) (δ := nb)
    (by rw [dist_comm]; exact hd) hnb).1
  have h2 := ((oTwoPrime_centralizer_eq_pCoreOf hyp).2)
  have h3 : conjSub (g : G) V ≤ Subgroup.centralizer (V : Set G) :=
    h1.trans ((h2.le).trans (pCoreOf_le_centralizer hyp))
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h3

theorem commutator_Vv_Vv_eq_bot (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    {ν μ : CosetGeom G₀ G₁ G₂} (hν : ν ∈ Γ0 G₀ G₁ G₂) (hμ : μ ∈ Γ0 G₀ G₁ G₂)
    (hd : dist ν μ < critDist G₀ G₁ G₂ V) : ⁅Vv V ν, Vv V μ⁆ = ⊥ := by
  obtain ⟨g, rfl⟩ := mem_Γ0_iff_exists.mp hν
  have hμ' : g⁻¹ • μ ∈ Γ0 G₀ G₁ G₂ := by
    obtain ⟨h, rfl⟩ := mem_Γ0_iff_exists.mp hμ
    exact mem_Γ0_iff_exists.mpr ⟨g⁻¹ * h, by rw [mul_smul]⟩
  have hd' : dist (γ₀ G₀ G₁ G₂) (g⁻¹ • μ) < critDist G₀ G₁ G₂ V := by
    have := dist_smul g (γ₀ G₀ G₁ G₂) (g⁻¹ • μ)
    rw [smul_inv_smul] at this
    rw [← this]; exact hd
  have h := commutator_V_Vv_eq_bot hyp hV hμ' hd'
  have h' := congrArg (conjSub (g : G)) h
  rw [conjSub_bot, ← conjSub_commutator, ← Vv_smul hyp.normalizes, smul_inv_smul] at h'
  rw [Vv_smul_γ₀ hyp.normalizes]
  exact h'

omit [Finite G] in
theorem isElemAbelian_Vv_of_mem_Γ0 (hN : G₁ ≤ Subgroup.normalizer (V : Set G))
    (hV : IsElemAbelian 2 V) {ν : CosetGeom G₀ G₁ G₂} (hν : ν ∈ Γ0 G₀ G₁ G₂) :
    IsElemAbelian 2 (Vv V ν) := by
  obtain ⟨g, rfl⟩ := mem_Γ0_iff_exists.mp hν
  rw [Vv_smul_γ₀ hN]
  exact isElemAbelian_conjSub hV

omit [Finite G] in
theorem isElemAbelian_iSup {ι : Sort*} (W : ι → Subgroup G) (hW : ∀ i, IsElemAbelian 2 (W i))
    (hc : ∀ i j, ∀ x ∈ W i, ∀ y ∈ W j, x * y = y * x) : IsElemAbelian 2 (⨆ i, W i) := by
  rw [Subgroup.iSup_eq_closure]
  refine isElemAbelian_closure _ ?_ ?_
  · intro x hx y hy
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hx hy
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    exact hc i j x hi y hj
  · intro x hx
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
    obtain ⟨i, hi⟩ := hx
    exact isElemAbelian_pow_eq_one (hW i) hi

theorem isElemAbelian_Vv_γ₁ (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    (hb : 2 < critDist G₀ G₁ G₂ V) : IsElemAbelian 2 (Vv V (γ₁ G₀ G₁ G₂)) := by
  have hN := hyp.normalizes
  have e : Vv V (γ₁ G₀ G₁ G₂) = ⨆ x : {x : G₀ ⧸ G₁.subgroupOf G₀ //
      (graph G₀ G₁ G₂).Adj (γ₁ G₀ G₁ G₂) (Sum.inl x)}, Vv0 V x.1 := by
    rw [show Vv V (γ₁ G₀ G₁ G₂) = ⨆ (x : G₀ ⧸ G₁.subgroupOf G₀)
      (_ : (graph G₀ G₁ G₂).Adj (γ₁ G₀ G₁ G₂) (Sum.inl x)), Vv0 V x from Vv_inr _]
    exact iSup_subtype'
  rw [e]
  refine isElemAbelian_iSup _ (fun x => ?_) (fun i j x hx y hy => ?_)
  · exact isElemAbelian_Vv_of_mem_Γ0 (G₀ := G₀) (G₁ := G₁) (G₂ := G₂) hN hyp.elemAbelian
      (ν := Sum.inl x.1) ⟨x.1, rfl⟩
  · have hν : (Sum.inl i.1 : CosetGeom G₀ G₁ G₂) ∈ Γ0 G₀ G₁ G₂ := ⟨i.1, rfl⟩
    have hμ : (Sum.inl j.1 : CosetGeom G₀ G₁ G₂) ∈ Γ0 G₀ G₁ G₂ := ⟨j.1, rfl⟩
    have hd : dist (Sum.inl i.1 : CosetGeom G₀ G₁ G₂) (Sum.inl j.1) < critDist G₀ G₁ G₂ V := by
      have h1 := dist_triangle hyp.gen (Sum.inl i.1 : CosetGeom G₀ G₁ G₂) (γ₁ G₀ G₁ G₂)
        (Sum.inl j.1)
      have h2 : dist (Sum.inl i.1 : CosetGeom G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) = 1 := by
        rw [dist_comm]; exact dist_eq_one_iff_adj.mpr i.2
      have h3 : dist (γ₁ G₀ G₁ G₂) (Sum.inl j.1 : CosetGeom G₀ G₁ G₂) = 1 :=
        dist_eq_one_iff_adj.mpr j.2
      omega
    have hcomm := commutator_Vv_Vv_eq_bot hyp hV hν hμ hd
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
    exact ((Subgroup.mem_centralizer_iff.mp this) y hy).symm

omit [Finite G] in
theorem isElementaryAbelian_of_isElemAbelian {X : Subgroup G} (h : IsElemAbelian 2 X) :
    CFSG.IsElementaryAbelian 2 X :=
  CFSG.Open.IsElemAbelian.isElementaryAbelian h

theorem frattini_Vv_γ₁ (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    (hb : 2 < critDist G₀ G₁ G₂ V) : frattini (Vv V (γ₁ G₀ G₁ G₂)) = ⊥ := by
  have h := isElemAbelian_Vv_γ₁ hyp hV hb
  have : Fact (IsPGroup 2 (Vv V (γ₁ G₀ G₁ G₂))) := ⟨isPGroup_of_isElemAbelian h⟩
  exact (CFSG.frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mpr
    (isElementaryAbelian_of_isElemAbelian h)

omit [Finite G] in
theorem mem_nbrs_symm {γ δ : CosetGeom G₀ G₁ G₂} (h : δ ∈ nbrs γ) : γ ∈ nbrs δ :=
  SimpleGraph.Adj.symm (show (graph G₀ G₁ G₂).Adj γ δ from h)

theorem Vv_γ₁_le_pCoreOf_stab_inf (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    {γ γ' : CosetGeom G₀ G₁ G₂} (hγ' : γ ∈ nbrs γ')
    (hd : dist (γ₁ G₀ G₁ G₂) γ' + 2 = critDist G₀ G₁ G₂ V) :
    Vv V (γ₁ G₀ G₁ G₂) ≤ pCoreOf 2 (stab γ' ⊓ stab γ) := by
  rw [show Vv V (γ₁ G₀ G₁ G₂) = ⨆ (x : G₀ ⧸ G₁.subgroupOf G₀)
    (_ : (graph G₀ G₁ G₂).Adj (γ₁ G₀ G₁ G₂) (Sum.inl x)), Vv0 V x from Vv_inr _]
  refine iSup₂_le fun x hx => ?_
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [Vv0_mk hyp.normalizes]
    refine (conjSub_V_le_pCoreOf hyp hV g (γ := γ') (δ := γ) ?_ hγ').2
    have h1 : dist (g • γ₀ G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) = 1 := by
      rw [smul_γ₀]; exact dist_eq_one_iff_adj.mpr hx.symm
    have := dist_triangle hyp.gen (g • γ₀ G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) γ'
    omega

theorem Vv_le_pCoreOf_stab_inf (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    {γ γ₂ : CosetGeom G₀ G₁ G₂} (hγ₂ : γ₂ ∈ nbrs (γ₁ G₀ G₁ G₂))
    (hd : dist γ γ₂ + 2 = critDist G₀ G₁ G₂ V) :
    Vv V γ ≤ pCoreOf 2 (stab (γ₁ G₀ G₁ G₂) ⊓ stab γ₂) := by
  have hγ₂' : (γ₁ G₀ G₁ G₂) ∈ nbrs γ₂ := mem_nbrs_symm hγ₂
  rw [inf_comm]
  cases γ with
  | inl x =>
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [Vv_inl, Vv0_mk hyp.normalizes]
      refine (conjSub_V_le_pCoreOf hyp hV g (γ := γ₂) (δ := γ₁ G₀ G₁ G₂) ?_ hγ₂').2
      rw [smul_γ₀]
      omega
  | inr y =>
    rw [Vv_inr]
    refine iSup₂_le fun x hx => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [Vv0_mk hyp.normalizes]
      refine (conjSub_V_le_pCoreOf hyp hV g (γ := γ₂) (δ := γ₁ G₀ G₁ G₂) ?_ hγ₂').2
      have h1 : dist (g • γ₀ G₀ G₁ G₂) (Sum.inr y : CosetGeom G₀ G₁ G₂) = 1 := by
        rw [smul_γ₀]; exact dist_eq_one_iff_adj.mpr hx.symm
      have := dist_triangle hyp.gen (g • γ₀ G₀ G₁ G₂) (Sum.inr y : CosetGeom G₀ G₁ G₂) γ₂
      omega

omit [Finite G] in
theorem exists_nbrs_of_geodesic (hG : G₀ = G₁ ⊔ G₂) {γ : CosetGeom G₀ G₁ G₂} {b : ℕ}
    (hgeo : dist (γ₁ G₀ G₁ G₂) γ + 1 = b) (hb : 2 ≤ b) :
    (∃ γ', γ ∈ nbrs γ' ∧ dist (γ₁ G₀ G₁ G₂) γ' + 2 = b) ∧
      (∃ γ₂, γ₂ ∈ nbrs (γ₁ G₀ G₁ G₂) ∧ dist γ γ₂ + 2 = b) := by
  constructor
  · obtain ⟨β, hβ, hdβ⟩ := exists_adj_dist_eq hG (α := γ₁ G₀ G₁ G₂) (δ := γ) (d := b - 2)
      (by omega)
    exact ⟨β, mem_nbrs_symm hβ, by omega⟩
  · obtain ⟨β, hβ, hdβ⟩ := exists_adj_dist_eq hG (α := γ) (δ := γ₁ G₀ G₁ G₂) (d := b - 2)
      (by rw [dist_comm]; omega)
    exact ⟨β, hβ, by omega⟩

theorem commutator_Vv_γ₁_Vv_le (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    {γ : CosetGeom G₀ G₁ G₂} (hgeo : dist (γ₁ G₀ G₁ G₂) γ + 1 = critDist G₀ G₁ G₂ V)
    (hb : 2 ≤ critDist G₀ G₁ G₂ V) :
    ⁅Vv V (γ₁ G₀ G₁ G₂), Vv V γ⁆ ≤ Vv V (γ₁ G₀ G₁ G₂) ⊓ Vv V γ := by
  obtain ⟨⟨γ', hγ', hd'⟩, ⟨γ₂, hγ₂, hd₂⟩⟩ := exists_nbrs_of_geodesic hyp.gen hgeo hb
  apply commutator_le_inf_of_normalizes
  · refine ((Vv_γ₁_le_pCoreOf_stab_inf hyp hV hγ' hd').trans (pCoreOf_le 2 _)).trans ?_
    exact inf_le_right.trans (stab_le_normalizer_Vv hyp.normalizes γ)
  · refine ((Vv_le_pCoreOf_stab_inf hyp hV hγ₂ hd₂).trans (pCoreOf_le 2 _)).trans ?_
    exact inf_le_left.trans (stab_le_normalizer_Vv hyp.normalizes (γ₁ G₀ G₁ G₂))

theorem quadratic_Vv_γ₁_Vv (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    {γ : CosetGeom G₀ G₁ G₂} (hgeo : dist (γ₁ G₀ G₁ G₂) γ + 1 = critDist G₀ G₁ G₂ V)
    (hb : 3 ≤ critDist G₀ G₁ G₂ V) (hodd : Odd (critDist G₀ G₁ G₂ V)) :
    IsElemAbelian 2 (Vv V (γ₁ G₀ G₁ G₂)) ∧ IsElemAbelian 2 (Vv V γ) ∧
      ⁅⁅Vv V (γ₁ G₀ G₁ G₂), Vv V γ⁆, Vv V γ⁆ = ⊥ ∧
      ⁅⁅Vv V γ, Vv V (γ₁ G₀ G₁ G₂)⁆, Vv V (γ₁ G₀ G₁ G₂)⁆ = ⊥ := by
  have hA := isElemAbelian_Vv_γ₁ hyp hV (by omega)
  have hvt : vtype γ = true := by
    have h1 := (vtype_eq_iff_even_dist hyp.gen (γ₁ G₀ G₁ G₂) γ).mpr
      (by obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩)
    rw [vtype_γ₁] at h1
    exact h1.symm
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hvt
  have hB : IsElemAbelian 2 (Vv V γ) := by
    rw [hg, Vv_smul hyp.normalizes]
    exact isElemAbelian_conjSub hA
  have hc := commutator_Vv_γ₁_Vv_le hyp hV hgeo (by omega)
  refine ⟨hA, hB, ?_, ?_⟩
  · refine le_bot_iff.mp ((Subgroup.commutator_mono (hc.trans inf_le_right) le_rfl).trans ?_)
    rw [commutator_self_eq_bot hB]
  · have hc' : ⁅Vv V γ, Vv V (γ₁ G₀ G₁ G₂)⁆ ≤ Vv V (γ₁ G₀ G₁ G₂) := by
      rw [Subgroup.commutator_comm]; exact hc.trans inf_le_left
    refine le_bot_iff.mp ((Subgroup.commutator_mono hc' le_rfl).trans ?_)
    rw [commutator_self_eq_bot hA]

theorem commutator_V_Vv_of_even (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    (hb : Even (critDist G₀ G₁ G₂ V)) {γ : CosetGeom G₀ G₁ G₂}
    (hγ : dist (γ₀ G₀ G₁ G₂) γ = critDist G₀ G₁ G₂ V) (hVγ : ¬ V ≤ ballStab 1 γ) :
    ⁅V, Vv V γ⁆ ≠ ⊥ ∧ ⁅V, Vv V γ⁆ ≤ V ⊓ Vv V γ ∧ Vv V γ ≤ G₁ ∧
      ⁅⁅V, Vv V γ⁆, Vv V γ⁆ = ⊥ := by
  have hN := hyp.normalizes
  have hvt : vtype γ = false := vtype_eq_false_of_even hyp.gen (by rw [hγ]; exact hb)
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hvt
  subst hg
  rw [Vv_smul_γ₀ hN]
  have hVstab0 : V ≤ stab (g • γ₀ G₀ G₁ G₂) := V_le_stab_of_dist_le hyp hV hγ.le
  have hVstab : V ≤ conjSub (g : G) G₁ := by
    rw [stab_smul, stab_γ₀ hyp.le₁] at hVstab0
    exact hVstab0
  have hVγG₁ : conjSub (g : G) V ≤ G₁ := by
    have h1 : dist (γ₀ G₀ G₁ G₂) (g⁻¹ • γ₀ G₀ G₁ G₂) ≤ critDist G₀ G₁ G₂ V := by
      have := dist_smul g⁻¹ (γ₀ G₀ G₁ G₂) (g • γ₀ G₀ G₁ G₂)
      rw [inv_smul_smul] at this
      rw [dist_comm, this, hγ]
    have h2 := V_le_stab_of_dist_le hyp hV h1
    rw [stab_smul, stab_γ₀ hyp.le₁, Subgroup.coe_inv] at h2
    exact (conjSub_le_iff _).mpr (by simpa using h2)
  have hnormV : conjSub (g : G) V ≤ Subgroup.normalizer (V : Set G) := hVγG₁.trans hN
  have hnormW : V ≤ Subgroup.normalizer (conjSub (g : G) V : Set G) :=
    hVstab.trans (conjSub_le_normalizer hN)
  have hcl : ⁅V, conjSub (g : G) V⁆ ≤ V ⊓ conjSub (g : G) V :=
    commutator_le_inf_of_normalizes hnormW hnormV
  have hWabel : IsElemAbelian 2 (conjSub (g : G) V) := isElemAbelian_conjSub hyp.elemAbelian
  refine ⟨fun hbot => ?_, hcl, hVγG₁, ?_⟩
  · have hcent : V ≤ Subgroup.centralizer (conjSub (g : G) V : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have h1 : V ≤ oTwoPrime (stab (g • γ₀ G₀ G₁ G₂) ⊓
        Subgroup.centralizer (conjSub (g : G) V : Set G)) :=
      le_oTwoPrime_of_isPGroup hyp.isPGroup (le_inf hVstab0 hcent)
    have h2 : oTwoPrime (stab (g • γ₀ G₀ G₁ G₂) ⊓
        Subgroup.centralizer (conjSub (g : G) V : Set G)) =
        pCoreOf 2 (ballStab 1 (g • γ₀ G₀ G₁ G₂)) := by
      rw [stab_smul, stab_γ₀ hyp.le₁, conjSub_centralizer, ← conjSub_inf, ← conjSub_oTwoPrime,
        (oTwoPrime_centralizer_eq_pCoreOf hyp).1, ← pCoreOf_conjSub, ← ballStab_smul]
    exact hVγ (h1.trans (h2.le.trans (pCoreOf_le 2 _)))
  · refine le_bot_iff.mp ((Subgroup.commutator_mono (hcl.trans inf_le_right) le_rfl).trans ?_)
    rw [commutator_self_eq_bot hWabel]

omit [Finite G] in
theorem card_conjSub (g : G) (X : Subgroup G) : Nat.card (conjSub g X) = Nat.card X :=
  Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g))

omit [Finite G] in
theorem isFFModule_of_card_le {X W : Subgroup G} (hV : IsElemAbelian 2 V) (hWX : W ≤ X)
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hW : IsElemAbelian 2 W) (hnt : ⁅V, W⁆ ≠ ⊥)
    (hcard : Nat.card V = Nat.card W)
    (hle : Nat.card (W ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) ≤
      Nat.card (V ⊓ Subgroup.centralizer (W : Set G) : Subgroup G)) :
    @IsFFModule V (commGroupOfElemAbelian hV) (autOn X V) := by
  have hWN : W ≤ Subgroup.normalizer (V : Set G) := hWX.trans hXN
  have hnc : ¬ W ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    apply hnt
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h
  refine ⟨autOn W V, autOn_le_autOn V hWX, autOn_ne_bot_of_not_le_centralizer hWN hnc,
    isElemAbelian2_autOn hV hW hWN, ?_⟩
  rw [card_autOn_eq_relIndex hWN, card_fixV_autOn_eq hV hWN, hcard]
  have h1 := Subgroup.relIndex_mul_card (H := W ⊓ Subgroup.centralizer (V : Set G)) (K := W)
  rw [inf_assoc, inf_comm (Subgroup.centralizer (V : Set G)) W, ← inf_assoc, inf_idem] at h1
  rw [← h1]
  exact Nat.mul_le_mul_left _ hle

theorem odd_critDist_of_not_isFFModule (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    (hFF : ¬ @IsFFModule V (commGroupOfElemAbelian hyp.elemAbelian) (autOn G₁ V)) :
    Odd (critDist G₀ G₁ G₂ V) := by
  by_contra hodd
  have hb : Even (critDist G₀ G₁ G₂ V) := Nat.not_odd_iff_even.mp hodd
  obtain ⟨γ, hγ, hVγ⟩ := exists_dist_eq_critDist_not_le hyp hV
  obtain ⟨hnt, -, hG1, -⟩ := commutator_V_Vv_of_even hyp hV hb hγ hVγ
  have hN := hyp.normalizes
  have hvt : vtype γ = false := vtype_eq_false_of_even hyp.gen (by rw [hγ]; exact hb)
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hvt
  subst hg
  rw [Vv_smul_γ₀ hN] at hnt hG1
  have hVstab : V ≤ conjSub (g : G) G₁ := by
    have := V_le_stab_of_dist_le hyp hV hγ.le
    rwa [stab_smul, stab_γ₀ hyp.le₁] at this
  apply hFF
  by_cases hle : Nat.card (conjSub (g : G) V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) ≤
      Nat.card (V ⊓ Subgroup.centralizer (conjSub (g : G) V : Set G) : Subgroup G)
  · exact isFFModule_of_card_le hyp.elemAbelian hG1 hN (isElemAbelian_conjSub hyp.elemAbelian)
      hnt (card_conjSub _ _).symm hle
  · push Not at hle
    have hW'G : conjSub (g : G)⁻¹ V ≤ G₁ := by
      rw [conjSub_le_iff, inv_inv]; exact hVstab
    have hnt' : ⁅V, conjSub (g : G)⁻¹ V⁆ ≠ ⊥ := by
      intro h
      apply hnt
      have h' := congrArg (conjSub (g : G)) h
      rw [conjSub_bot, ← conjSub_commutator, conjSub_inv_conjSub] at h'
      rwa [Subgroup.commutator_comm]
    have e1 : Nat.card (conjSub (g : G)⁻¹ V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) =
        Nat.card (V ⊓ Subgroup.centralizer (conjSub (g : G) V : Set G) : Subgroup G) := by
      rw [← card_conjSub (g : G), conjSub_inf, conjSub_inv_conjSub, conjSub_centralizer]
    have e2 : Nat.card (V ⊓ Subgroup.centralizer (conjSub (g : G)⁻¹ V : Set G) : Subgroup G) =
        Nat.card (conjSub (g : G) V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
      rw [← card_conjSub (g : G)⁻¹ (conjSub (g : G) V ⊓ Subgroup.centralizer (V : Set G)),
        conjSub_inf, conjSub_conjSub_inv, ← conjSub_centralizer]
    exact isFFModule_of_card_le hyp.elemAbelian hW'G hN (isElemAbelian_conjSub hyp.elemAbelian)
      hnt' (card_conjSub _ _).symm (by rw [e1, e2]; exact hle.le)

theorem two_le_critDist_of_le_pCoreOf (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    (hVG₂ : V ≤ pCoreOf 2 G₂) : 2 ≤ critDist G₀ G₁ G₂ V := by
  have hN := hyp.normalizes
  obtain ⟨hb0, -, -⟩ := critDist_spec hyp hV
  have hb1 : critDist G₀ G₁ G₂ V ≠ 1 := by
    intro hb1
    obtain ⟨α, hα, hVα⟩ := exists_dist_eq_critDist_not_le hyp hV
    rw [hb1] at hα
    have hαn : α ∈ nbrs (γ₀ G₀ G₁ G₂) := (dist_eq_one_iff_adj.mp hα)
    have hγ₁n : γ₁ G₀ G₁ G₂ ∈ nbrs (γ₀ G₀ G₁ G₂) := adj_γ₀_γ₁
    obtain ⟨x, hx, hxγ⟩ := stab_transitive_on_nbrs hγ₁n hαn
    apply hVα
    rw [← hxγ, ballStab_smul, le_conjSub_iff]
    have hxG₁ : (x : G) ∈ G₁ := by rwa [stab_γ₀ hyp.le₁] at hx
    have hV' : conjSub (x : G)⁻¹ V = V := F7.conjSub_eq_of_mem_normalizer (inv_mem (hN hxG₁))
    rw [hV']
    refine hVG₂.trans ?_
    have := pCoreOf_stab_le_ballStab_one hyp.toAmalgamHyp (γ₁ G₀ G₁ G₂)
    rwa [stab_γ₁ hyp.le₂] at this
  omega

theorem isElemAbelian_conjClosure_of_not_isFFModule (hyp : AmalgamHypV G₀ G₁ G₂ T V)
    (hV : V ≠ ⊥) (hVG₂ : V ≤ pCoreOf 2 G₂)
    (hFF : ¬ @IsFFModule V (commGroupOfElemAbelian hyp.elemAbelian) (autOn G₁ V)) :
    IsElemAbelian 2 (conjClosure V G₂) := by
  have hodd := odd_critDist_of_not_isFFModule hyp hV hFF
  have hb2 := two_le_critDist_of_le_pCoreOf hyp hV hVG₂
  have hb3 : 2 < critDist G₀ G₁ G₂ V := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have h := isElemAbelian_Vv_γ₁ hyp hV hb3
  rwa [Vv_γ₁ hyp.le₂ hyp.normalizes] at h

theorem critDist_eq_one_of_not_le_pCoreOf (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    (h : ¬ V ≤ pCoreOf 2 G₂) : critDist G₀ G₁ G₂ V = 1 := by
  have hb0 := (critDist_spec hyp hV).1
  have hle : critDist G₀ G₁ G₂ V ≤ 1 := by
    refine (isLeast_critDist hyp hV).2 ⟨γ₁ G₀ G₁ G₂, ?_, ?_⟩
    · exact dist_eq_one_iff_adj.mpr adj_γ₀_γ₁
    · intro hV'
      apply h
      have hle1 : ballStab 1 (γ₁ G₀ G₁ G₂) ≤ G₂ := by
        have := ballStab_le_stab 1 (γ₁ G₀ G₁ G₂)
        rwa [stab_γ₁ hyp.le₂] at this
      have hN2 : G₂ ≤ Subgroup.normalizer (ballStab 1 (γ₁ G₀ G₁ G₂) : Set G) := by
        have := le_normalizer_ballStab 1 (γ₁ G₀ G₁ G₂)
        rwa [stab_γ₁ hyp.le₂] at this
      have hbG₁ : ballStab 1 (γ₁ G₀ G₁ G₂) ≤ G₁ :=
        (((ballStab_one_γ₁ hyp.gen).1).le.trans (coreIn_le_right _ _)).trans inf_le_left
      have hV2 : V ≤ pCoreOf 2 (ballStab 1 (γ₁ G₀ G₁ G₂)) :=
        le_pCoreOf_of_le_normalizer 2 hV' (hbG₁.trans hyp.normalizes) hyp.isPGroup
      exact hV2.trans (pCoreOf_mono_of_le_normalizer hle1 hN2)
  omega

theorem critDist_eq_two_of_nonabelian (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    (hVG₂ : V ≤ pCoreOf 2 G₂)
    (hna : ¬ ∀ x ∈ Vv V (γ₁ G₀ G₁ G₂), ∀ y ∈ Vv V (γ₁ G₀ G₁ G₂), x * y = y * x) :
    critDist G₀ G₁ G₂ V = 2 := by
  have hb2 := two_le_critDist_of_le_pCoreOf hyp hV hVG₂
  by_contra hne
  have hb3 : 2 < critDist G₀ G₁ G₂ V := by omega
  exact hna fun x hx y hy => isElemAbelian_comm (isElemAbelian_Vv_γ₁ hyp hV hb3) hx hy

structure IsCriticalVertex (G₀ G₁ G₂ V : Subgroup G) (γ : CosetGeom G₀ G₁ G₂) : Prop where
  dist_eq : dist (γ₀ G₀ G₁ G₂) γ = critDist G₀ G₁ G₂ V
  not_le : ¬ V ≤ ballStab 1 γ
  geodesic : dist (γ₁ G₀ G₁ G₂) γ + 1 = critDist G₀ G₁ G₂ V

theorem exists_isCriticalVertex (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) :
    ∃ γ : CosetGeom G₀ G₁ G₂, IsCriticalVertex G₀ G₁ G₂ V γ := by
  obtain ⟨hb0, -, -⟩ := critDist_spec hyp hV
  obtain ⟨α, hα, hVα⟩ := exists_dist_eq_critDist_not_le hyp hV
  obtain ⟨β, hβ, hdβ⟩ := exists_adj_dist_eq hyp.gen (α := α) (δ := γ₀ G₀ G₁ G₂)
    (d := critDist G₀ G₁ G₂ V - 1) (by rw [dist_comm, hα]; omega)
  have hγ₁n : γ₁ G₀ G₁ G₂ ∈ nbrs (γ₀ G₀ G₁ G₂) := adj_γ₀_γ₁
  obtain ⟨x, hx, hxγ⟩ := stab_transitive_on_nbrs hγ₁n hβ
  have hxG₁ : (x : G) ∈ G₁ := by rwa [stab_γ₀ hyp.le₁] at hx
  have hxγ₀ : x • γ₀ G₀ G₁ G₂ = γ₀ G₀ G₁ G₂ := smul_eq_of_mem_stab hx
  refine ⟨x⁻¹ • α, ⟨?_, ?_, ?_⟩⟩
  · have := dist_smul x (γ₀ G₀ G₁ G₂) (x⁻¹ • α)
    rw [smul_inv_smul, hxγ₀] at this
    rw [← this]; exact hα
  · intro hle
    apply hVα
    rw [ballStab_smul, le_conjSub_iff] at hle
    have hV' : conjSub (x : G)⁻¹⁻¹ V = V := by
      rw [inv_inv]; exact F7.conjSub_eq_of_mem_normalizer (hyp.normalizes hxG₁)
    simpa [inv_inv, F7.conjSub_eq_of_mem_normalizer (hyp.normalizes hxG₁)] using hle
  · have := dist_smul x (γ₁ G₀ G₁ G₂) (x⁻¹ • α)
    rw [smul_inv_smul, hxγ] at this
    rw [← this, dist_comm]
    omega

end Fin

end CosetGeom

end CFSG.Quasithin

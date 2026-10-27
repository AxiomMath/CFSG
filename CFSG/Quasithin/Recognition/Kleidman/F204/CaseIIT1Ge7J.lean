module

public import CFSG.Quasithin.Recognition.Kleidman.F204.EqZ
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIOffNatA

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

section Local

variable (F : Frame L1 L2 S D X)
include F

theorem not_Qv_le_Qv_of_nbr {x d : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    (hd : d ∈ nbrs x) : ¬ Qv x ≤ Qv d := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  have hQ0 : Qv (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q1 L1 L2 S := by
    unfold Qv; rw [stab_γ₀ h₁]
  have hQ1 : Qv (γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q2 L1 L2 S := by
    unfold Qv; rw [stab_γ₁ h₂]
  obtain ⟨g, ⟨hg0, hg1⟩ | ⟨hg0, hg1⟩⟩ := exists_smul_edge (show (graph _ _ _).Adj x d from hd)
  · exfalso
    have := vtype_smul g (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S))
    rw [hg0, hx, vtype_γ₀] at this
    exact Bool.noConfusion this
  · intro hle
    rw [← hg0, ← hg1, Qv_smul, Qv_smul, hQ0, hQ1] at hle
    apply not_Q2_le_Q1 F
    have := conjSub_mono ((g : G)⁻¹) hle
    rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this

variable (hT1 : ConfigT1 L1 L2 S)
include hT1

theorem five_centralizes_Zv_T1 {d : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hd : vtype d = false) :
    ∀ c ∈ stab d, c ^ 5 = 1 → c ∈ Subgroup.centralizer (Zv d : Set G) := by
  have hA := Amal.of_frame F
  obtain ⟨x, hx⟩ : ∃ x, x ∈ nbrs d := by
    by_contra hcon
    push Not at hcon
    have hcard := hA.card_nbrs d
    have : nbrs d = ∅ := Set.eq_empty_iff_forall_notMem.mpr hcon
    rw [this] at hcard
    simp at hcard
  have hxd : d ∈ nbrs x := mem_nbrs_symm hx
  have hxt : vtype x = true := by
    have := vtype_ne_of_adj (show (graph _ _ _).Adj d x from hx)
    rw [hd] at this
    cases h : vtype x <;> simp_all
  obtain ⟨hT, -, -⟩ := sylow_sup_Qv F hxt hxd
  have hZT : Zv d = quasithinOmegaOneCenter (Qv x ⊔ Qv d) := (hT1 d).mpr hd _ hT
  obtain ⟨t, htx, htd⟩ : ∃ t ∈ Qv x, t ∉ Qv d := by
    by_contra h; push Not at h; exact not_Qv_le_Qv_of_nbr F hxt hxd fun t ht => h t ht
  have htT : t ∈ Qv x ⊔ Qv d := le_sup_left (a := Qv x) htx
  have htC : t ∈ Subgroup.centralizer (Zv d : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [hZT] at hz
    have hle : quasithinOmegaOneCenter (Qv x ⊔ Qv d) ≤
        (Qv x ⊔ Qv d) ⊓ Subgroup.centralizer ((Qv x ⊔ Qv d : Subgroup G) : Set G) :=
      (Subgroup.closure_le _).mpr fun _ hx => hx.1
    exact (Subgroup.mem_centralizer_iff.mp (hle hz).2 t htT).symm
  have htd' : t ∈ stab d := hA.Qv_le_stab_of_mem_nbrs hxd htx
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (stab x)) ⟨t, htx⟩
  have htn : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  exact five_centralizes_Zv_of_two F hd htd' htn htC htd

theorem inf_centralizer_stab_eq_bot {x : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true) :
    Zv x ⊓ Subgroup.centralizer (stab x : Set G) = ⊥ := by
  have hA := Amal.of_frame F
  set C := Zv x ⊓ Subgroup.centralizer (stab x : Set G) with hCdef
  obtain ⟨d, hd⟩ : ∃ d, d ∈ nbrs x := by
    by_contra hcon
    push Not at hcon
    have hcard := hA.card_nbrs x
    have : nbrs x = ∅ := Set.eq_empty_iff_forall_notMem.mpr hcon
    rw [this] at hcard
    simp at hcard
  have hxd : x ∈ nbrs d := mem_nbrs_symm hd
  have hdf : vtype d = false := by
    have := vtype_ne_of_adj (show (graph _ _ _).Adj x d from hd)
    rw [hx] at this
    cases h : vtype d <;> simp_all
  have hCd : C ≤ Zv d := by
    rw [Zv_eq_inf_centralizer F hT1 hx hd]
    refine le_inf inf_le_left fun z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 q
      (hA.Qv_le_stab_of_mem_nbrs hxd hq))
  obtain ⟨c, hc, hcQ, hc5⟩ := exists_five_stab F hdf
  have hc5' : c ^ 5 ∈ Qv d := by rw [hc5]; exact one_mem _
  have hcC : c ∈ Subgroup.centralizer (Zv d : Set G) := five_centralizes_Zv_T1 F hT1 hdf c hc hc5
  have hdC : stab d ≤ Subgroup.centralizer (C : Set G) := by
    intro g hg
    obtain ⟨hG0, hfix⟩ := mem_stab.mp hg
    have hgx : (⟨g, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) • x ∈ nbrs d := by
      have := (smul_adj (⟨g, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S))).mpr
        (show (graph _ _ _).Adj d x from hxd)
      rwa [hfix] at this
    obtain ⟨e, he, hex⟩ := exists_zpow_smul_nbr F hdf hc hcQ hc5' hxd hgx
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp he
    have heC : (e : G) ∈ Subgroup.centralizer (C : Set G) := by
      rw [← hi]
      refine Subgroup.zpow_mem _ ?_ i
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact Subgroup.mem_centralizer_iff.mp hcC z (hCd hz)
    have hk : ((e⁻¹ * ⟨g, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) : G) ∈ stab x := by
      apply mem_stab_of_smul_eq
      rw [mul_smul, ← hex, inv_smul_smul]
    have hkC : ((e⁻¹ * ⟨g, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) : G) ∈
        Subgroup.centralizer (C : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 _ hk).symm
    have e' : g = (e : G) * ((e⁻¹ * ⟨g, hG0⟩ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) : G) := by simp
    rw [e']
    exact (Subgroup.centralizer _).mul_mem heC hkC
  have hxC : stab x ≤ Subgroup.centralizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 g hg).symm
  have hCQ : C ≤ Qv x := inf_le_left.trans (hA.Zv_le_Qv x)
  have hU : C ≤ stab x ⊓ stab d :=
    le_inf (hCQ.trans (pCoreOf_le 2 _)) (hCQ.trans (hA.Qv_le_stab_of_mem_nbrs hd))
  exact hA.eq_bot_of_normalizes_both (show (graph _ _ _).Adj x d from hd) hU
    (hxC.trans (Subgroup.centralizer_le_normalizer _)) (hdC.trans (Subgroup.centralizer_le_normalizer _))

theorem Zv_inf_Zv_eq_bot_T1 {x : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    {d d' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hd : d ∈ nbrs x) (hd' : d' ∈ nbrs x) (hne : d ≠ d') :
    Zv d ⊓ Zv d' = ⊥ := by
  have hA := Amal.of_frame F
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_stab F hx
  have hker : ∀ l : ↥(stab x), φ l = 1 → (l : G) ∈ Subgroup.centralizer (Zv x : Set G) := by
    intro l hl
    have hlQ : (l : G) ∈ Qv x := by
      have := MonoidHom.mem_ker.mpr hl
      rw [hφk, Subgroup.mem_subgroupOf] at this
      exact this
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv x hz).2 _ hlQ).symm
  have hCL : ∀ v ∈ Zv x, (∀ l : ↥(stab x), v * (l : G) = (l : G) * v) → v = 1 := by
    intro v hv hl
    have : v ∈ Zv x ⊓ Subgroup.centralizer (stab x : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hv, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
      exact (hl ⟨g, hg⟩).symm
    rw [inf_centralizer_stab_eq_bot F hT1 hx, Subgroup.mem_bot] at this
    exact this
  have h₁ := card_map_Qv_nbr F hx hd hφs hφk
  have h₂ := card_map_Qv_nbr F hx hd' hφs hφk
  have hne' := map_Qv_ne F hx hd hd' hne hφk
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvd, hvd'⟩ := Subgroup.mem_inf.mp hv
  have hvx : v ∈ Zv x := by
    rw [Zv_eq_inf_centralizer F hT1 hx hd] at hvd; exact (Subgroup.mem_inf.mp hvd).1
  rw [Subgroup.mem_bot]
  refine klein_fixed_inf_eq_bot φ hker hCL h₁ h₂ hne' v hvx (fun a ha => ?_) (fun a ha => ?_)
  · exact (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv d hvd).2 _
      (Subgroup.mem_subgroupOf.mp ha)).symm
  · exact (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv d' hvd').2 _
      (Subgroup.mem_subgroupOf.mp ha)).symm

end Local

end CFSG.Quasithin.Kleidman.F204

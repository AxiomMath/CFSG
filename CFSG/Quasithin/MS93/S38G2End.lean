module

public import CFSG.Quasithin.MS93.S38G2Rigid

public section

namespace CFSG.Quasithin.MS93.S38G

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 SimpleGraph
open scoped commutatorElement

section ClassTwo

variable {Γ : Type*} [Group Γ] {V G₀ : Subgroup Γ}

theorem commutatorElement_mul_left_of {a b c : Γ} (h : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆) :
    ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
  have e : ⁅a * b, c⁆ = (a * ⁅b, c⁆ * a⁻¹) * ⁅a, c⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, h]

theorem commutatorElement_mul_right_of {a b c : Γ} (h : b * ⁅a, c⁆ * b⁻¹ = ⁅a, c⁆) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have e : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, h]

theorem commutatorElement_conj_left (g a b : Γ) :
    ⁅g * a * g⁻¹, b⁆ = g * ⁅a, g⁻¹ * b * g⁆ * g⁻¹ := by
  simp only [commutatorElement_def]
  group

@[expose, instance_reducible] def quotCommGroup {V B : Subgroup Γ} [(B.subgroupOf V).Normal]
    (h : ∀ a ∈ V, ∀ b ∈ V, ⁅a, b⁆ ∈ B) : CommGroup (↥V ⧸ B.subgroupOf V) :=
  { (QuotientGroup.Quotient.group (B.subgroupOf V)) with
    mul_comm := fun x y => by
      induction x using QuotientGroup.induction_on with
      | H a =>
        induction y using QuotientGroup.induction_on with
        | H b =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
            Subgroup.mem_subgroupOf]
          have e : (((a * b)⁻¹ * (b * a) : ↥V) : Γ) = ⁅(b : Γ)⁻¹, (a : Γ)⁻¹⁆ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
            group
          rw [e]
          exact h _ (V.inv_mem b.2) _ (V.inv_mem a.2) }

end ClassTwo

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}
  {Lt Ut Wt : Vtx X → Subgroup X.Universal}

namespace G2Hyp

variable (hG : G2Hyp X Lt Ut Wt)
include hG

theorem nA_le_centralizer_stab {α : Vtx X} :
    S38E.nA X α ≤ Subgroup.centralizer (stab X α : Set X.Universal) := by
  refine iSup_le fun δ => iSup_le fun δ' => iSup_le fun hδ => ?_
  obtain ⟨hcδ, hδα⟩ := hδ
  rw [Subgroup.le_centralizer_iff, ← hδα, hG.xm_eq δ hcδ.1, hG.xm_eq δ' (hcδ.isMVtx_right X hG.h20)]
  exact hG.stab_le_centralizer_r hcδ

theorem vv_eq_closure (α : Vtx X) :
    Vv X α = Subgroup.closure {v | v ∈ Vv X α ∧ v ^ 2 = 1} := by
  refine le_antisymm (iSup₂_le fun ρ hρ => ?_) (Subgroup.closure_le _ |>.mpr fun v hv => hv.1)
  intro z hz
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx X | X.treeGraph.dist α ρ ≤ 2}) =>
      Zv X ρ) ρ hρ le_rfl hz
  · by_cases hρM : IsMVtx X ρ
    · rw [zv_of_isMVtx X hρM] at hz
      exact (isElemAbelian_xm X ρ).2 z (zm_le_xm X hG.h20 hG.critDist_pos hρM hz)
    · rw [zv_of_not_isMVtx X hρM] at hz
      exact (isElemAbelian_xm X ρ).2 z hz

theorem false_of_isCritical {α α' : Vtx X} (hc : IsCritical X α α') : False := by
  classical
  set β := geo X α α' 1 with hβdef
  set μ := geo X α α' 2 with hμdef
  set V := Vv X α with hVdef
  set G₀ := stab X α with hG₀def
  set L := Lt α with hLdef
  set Q := Qv X α with hQdef
  have hαβ : X.treeGraph.Adj α β := hG.adj_one hc
  have hβ : ¬ IsMVtx X β := hG.not_isMVtx_one hc
  have hVs : G₀ ≤ Subgroup.normalizer (V : Set X.Universal) := stab_le_normalizer_vi α 2
  have hVQ : V ≤ Q := S38E.vv_le_qv X (by rw [hG.b4]; norm_num) hc.1
  have hVG : V ≤ G₀ := hVQ.trans (qv_le_stab X α)
  have hLG : L ≤ G₀ := hG.lt_le α hc.1
  have hLn : G₀ ≤ Subgroup.normalizer (L : Set X.Universal) := hG.lt_nor α hc.1
  have hQn : G₀ ≤ Subgroup.normalizer (Q : Set X.Universal) := stab_le_normalizer_qv X α
  have hfV : Finite ↥V := by
    have := hG.qv_finite hc.1
    exact Finite.of_injective _ (Subgroup.inclusion_injective hVQ)
  have hV'c : ⁅V, V⁆ ≤ Subgroup.centralizer (G₀ : Set X.Universal) :=
    (S38E.commutator_vv_le_nA X hG.h20 hG.b4 hG.starNorm hc.1).trans hG.nA_le_centralizer_stab
  have hcen : ∀ a ∈ V, ∀ b ∈ V, ∀ g ∈ G₀, g * ⁅a, b⁆ * g⁻¹ = ⁅a, b⁆ := by
    intro a ha b hb g hg
    have := Subgroup.mem_centralizer_iff.mp (hV'c (Subgroup.commutator_mem_commutator ha hb)) g hg
    rw [this, mul_inv_cancel_right]
  set Zc := V ⊓ Subgroup.centralizer (V : Set X.Universal) with hZcdef
  have hZcn : G₀ ≤ Subgroup.normalizer (Zc : Set X.Universal) :=
    le_normalizer_inf' hVs (le_normalizer_centralizer' hVs)
  have hcommZc : ∀ a ∈ V, ∀ b ∈ V, ⁅a, b⁆ ∈ Zc := by
    intro a ha b hb
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact V.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hVs (hVG hb)) _).mp (V.inv_mem ha))
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := hcen a ha b hb g (hVG hg)
      calc g * ⁅a, b⁆ = g * ⁅a, b⁆ * g⁻¹ * g := by group
        _ = ⁅a, b⁆ * g := by rw [this]
  have hZV : ZM X α ≤ Zc := by
    refine le_inf (S38E.zm_le_vv X hc.1 (by simp)) ?_
    rw [Subgroup.le_centralizer_iff]
    exact hVQ.trans (by
      rw [← Subgroup.le_centralizer_iff]
      exact zm_le_centralizer_qv X hG.h20 hc.1)
  have h7 := (hG.commutator_vv_qv hc).1
  have hVQZ : ∀ v ∈ V, ∀ q ∈ Q, ⁅v, q⁆ ∈ Zc := by
    intro v hv q hq
    have hm := Subgroup.commutator_mem_commutator hv hq
    refine Subgroup.mem_inf.mpr ⟨commutator_le_self_of ((qv_le_stab X α).trans hVs) hm, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := Subgroup.commutator_mem_commutator hm hw
    rw [h7, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  set Bs := cRel L Zc ⊓ V with hBsdef
  have hBn : G₀ ≤ Subgroup.normalizer (Bs : Set X.Universal) :=
    le_normalizer_inf' (le_normalizer_cRel hLn hZcn) hVs
  have hZcB : Zc ≤ Bs := by
    intro z hz
    refine ⟨⟨hZcn (hVG hz.1), fun l hl => ?_⟩, hz.1⟩
    have e : ⁅z, l⁆ = z * (l * z⁻¹ * l⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Zc.mul_mem hz ((Subgroup.mem_normalizer_iff.mp (hZcn (hLG hl)) _).mp (Zc.inv_mem hz))
  have hBV : Bs ≤ V := inf_le_right
  have h64 : Bs.relIndex V ≤ 2 ^ 6 := by
    obtain ⟨g₁, hg₁, g₂, hg₂, hgen⟩ := hG.two_gen α α' hc
    have hZs : ZM X α' ≤ G₀ := zm_le_stab_of_isCritical X hG.h20 hG.critDist_pos hc
    have hA : ∀ g ∈ G₀, (ZM X α').map (MulAut.conj g).toMonoidHom ≤ G₀ := by
      rintro g hg _ ⟨z, hz, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hZs hz)) (Subgroup.inv_mem _ hg)
    have hle : cRel ((ZM X α').map (MulAut.conj g₁).toMonoidHom) Zc ⊓
        cRel ((ZM X α').map (MulAut.conj g₂).toMonoidHom) Zc ⊓ V ≤ Bs := by
      rintro d ⟨⟨hd₁, hd₂⟩, hdV⟩
      refine ⟨⟨hd₁.1, fun l hl => ?_⟩, hdV⟩
      have hS : (ZM X α').map (MulAut.conj g₁).toMonoidHom ⊔
          (ZM X α').map (MulAut.conj g₂).toMonoidHom ⊔ Q ≤ cOf d Zc := by
        refine sup_le (sup_le (fun a ha => ⟨hZcn (hA g₁ hg₁ ha), hd₁.2 a ha⟩)
          (fun a ha => ⟨hZcn (hA g₂ hg₂ ha), hd₂.2 a ha⟩))
          (fun q hq => ⟨hZcn (qv_le_stab X α hq), hVQZ d hdV q hq⟩)
      exact (hS (hgen hl)).2
    have h8 : ∀ g ∈ G₀, (cRel ((ZM X α').map (MulAut.conj g).toMonoidHom) Zc).relIndex V ≤ 8 := by
      intro g hg
      rw [relIndex_cRel_map_conj (hZcn hg) (hVs hg)]
      have hle' : cRel (ZM X α') (ZM X α) ⊓ V ≤ cRel (ZM X α') Zc := by
        rintro v ⟨⟨_, hv⟩, hvV⟩
        exact ⟨hZcn (hVG hvV), fun z hz => hZV (hv z hz)⟩
      have h0 : (cRel (ZM X α') (ZM X α) ⊓ V).relIndex V ≠ 0 := by
        unfold Subgroup.relIndex
        exact Subgroup.index_ne_zero_of_finite
      calc (cRel (ZM X α') Zc).relIndex V ≤ (cRel (ZM X α') (ZM X α) ⊓ V).relIndex V :=
            Subgroup.relIndex_le_of_le_left hle' h0
        _ = (cRel (ZM X α') (ZM X α)).relIndex V := Subgroup.inf_relIndex_right _ _
        _ ≤ 8 := hG.relIndex_cRel_vv_le hc
    have h0 : (cRel ((ZM X α').map (MulAut.conj g₁).toMonoidHom) Zc ⊓
        cRel ((ZM X α').map (MulAut.conj g₂).toMonoidHom) Zc ⊓ V).relIndex V ≠ 0 := by
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite
    calc Bs.relIndex V ≤ (cRel ((ZM X α').map (MulAut.conj g₁).toMonoidHom) Zc ⊓
          cRel ((ZM X α').map (MulAut.conj g₂).toMonoidHom) Zc ⊓ V).relIndex V :=
          Subgroup.relIndex_le_of_le_left hle h0
      _ = (cRel ((ZM X α').map (MulAut.conj g₁).toMonoidHom) Zc ⊓
          cRel ((ZM X α').map (MulAut.conj g₂).toMonoidHom) Zc).relIndex V :=
          Subgroup.inf_relIndex_right _ _
      _ ≤ (cRel ((ZM X α').map (MulAut.conj g₁).toMonoidHom) Zc).relIndex V *
          (cRel ((ZM X α').map (MulAut.conj g₂).toMonoidHom) Zc).relIndex V :=
          Subgroup.relIndex_inf_le
      _ ≤ 8 * 8 := Nat.mul_le_mul (h8 g₁ hg₁) (h8 g₂ hg₂)
      _ = 2 ^ 6 := rfl
  have hBnV : (Bs.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBV).mpr (hVG.trans hBn)
  have hcommB : ∀ a ∈ V, ∀ b ∈ V, ⁅a, b⁆ ∈ Bs := fun a ha b hb => hZcB (hcommZc a ha b hb)
  let _ : CommGroup (↥V ⧸ Bs.subgroupOf V) := quotCommGroup hcommB
  set ρ : ↥G₀ →* MulAut (↥V ⧸ Bs.subgroupOf V) := quotAct (K := V) (E := Bs) hVs hBn
    with hρdef
  have hρmk : ∀ (g : ↥G₀) (v : ↥V),
      ρ g (QuotientGroup.mk v) = QuotientGroup.mk (conjK hVs g v) := fun g v => rfl
  have hcardY : Nat.card (↥V ⧸ Bs.subgroupOf V) ≤ 2 ^ 6 := by
    rw [← Subgroup.index, ← Subgroup.relIndex]
    exact h64
  have hVcl : V = Subgroup.closure {v | v ∈ V ∧ v ^ 2 = 1} := hG.vv_eq_closure α
  have hsqY : ∀ y : ↥V ⧸ Bs.subgroupOf V, y ^ 2 = 1 := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H v =>
      have key : ∀ x (hx : x ∈ Subgroup.closure {v | v ∈ V ∧ v ^ 2 = 1}), ∀ hxV : x ∈ V,
          (QuotientGroup.mk (⟨x, hxV⟩ : ↥V) : ↥V ⧸ Bs.subgroupOf V) ^ 2 = 1 := by
        intro x hx
        induction hx using Subgroup.closure_induction with
        | mem y hy =>
          intro hyV
          rw [← QuotientGroup.mk_pow]
          have : (⟨y, hyV⟩ : ↥V) ^ 2 = 1 := Subtype.ext (by simpa using hy.2)
          rw [this, QuotientGroup.mk_one]
        | one =>
          intro h1
          have : (⟨1, h1⟩ : ↥V) = 1 := rfl
          rw [this, QuotientGroup.mk_one, one_pow]
        | mul a b ha hb iha ihb =>
          intro hab
          have haV : a ∈ V := by rw [hVcl]; exact ha
          have hbV : b ∈ V := by rw [hVcl]; exact hb
          have e : (⟨a * b, hab⟩ : ↥V) = ⟨a, haV⟩ * ⟨b, hbV⟩ := rfl
          rw [e, QuotientGroup.mk_mul, mul_pow, iha haV, ihb hbV, one_mul]
        | inv a ha iha =>
          intro hai
          have haV : a ∈ V := by rw [hVcl]; exact ha
          have e : (⟨a⁻¹, hai⟩ : ↥V) = (⟨a, haV⟩ : ↥V)⁻¹ := rfl
          rw [e, QuotientGroup.mk_inv, inv_pow, iha haV, inv_one]
      exact key v (by rw [← hVcl]; exact v.2) v.2
  have hρQ : ∀ q : ↥G₀, (q : X.Universal) ∈ Q → ρ q = 1 := by
    intro q hq
    ext y
    induction y using QuotientGroup.induction_on with
    | H v =>
      rw [hρmk, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have e : (((conjK hVs q v)⁻¹ * v : ↥V) : X.Universal) =
          ⁅(v : X.Universal)⁻¹, ((q : ↥G₀) : X.Universal)⁆⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjK_apply_coe, commutatorElement_def]
        group
      rw [e]
      exact hZcB (Zc.inv_mem (hVQZ _ (V.inv_mem v.2) _ hq))
  have hne : ⁅V, V⁆ ≠ ⊥ := S38E.commutator_vv_ne_bot X hG.h20 hG.b4 hG.cent hc (by
    have := hG.hV α α' hc
    rwa [hG.geo_rev hc (by norm_num)] at this)
  have hLC' : L ≤ Subgroup.centralizer ((⁅V, V⁆ : Subgroup X.Universal) : Set X.Universal) :=
    hLG.trans (Subgroup.le_centralizer_iff.mp hV'c)
  have hfalse_of : ⁅V, L⁆ ≤ Bs → False := by
    intro hVL
    have hVLZ : ⁅V, L⁆ ≤ Zc := two_step hZcB (hBV.trans (hVG.trans hZcn))
      (fun a ha b hb => hcommZc a (hBV ha) b (hBV hb)) hVL
      (Subgroup.commutator_le.mpr fun b hb l hl => hb.1.2 l hl) (hG.lt_perf α hc.1)
    apply hne
    refine S38E.commutator_vv_eq_bot_of_le X hG.h20 hG.b4 hG.cent hG.starNorm hc.1 hαβ
      (hG.lt_sup α β hc.1 hαβ) hLC' ?_
    have : ⁅⁅V, L⁆, V⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hVLZ.trans inf_le_right |>.trans (by
        rw [Subgroup.le_centralizer_iff, Subgroup.le_centralizer_iff])
    rw [this]
    exact bot_le
  have hρL : ∃ l : ↥G₀, (l : X.Universal) ∈ L ∧ ρ l ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hfalse_of
    rw [Subgroup.commutator_le]
    intro v hv l hl
    have h1 := congrArg (fun f : MulAut (↥V ⧸ Bs.subgroupOf V) =>
      f (QuotientGroup.mk (⟨v⁻¹, V.inv_mem hv⟩ : ↥V))) (hcon ⟨l, hLG hl⟩ hl)
    simp only [MulAut.one_apply] at h1
    rw [hρmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    have e : ⁅v, l⁆ = (((conjK hVs ⟨l, hLG hl⟩ ⟨v⁻¹, V.inv_mem hv⟩)⁻¹ *
        ⟨v⁻¹, V.inv_mem hv⟩ : ↥V) : X.Universal)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjK_apply_coe, commutatorElement_def]
      group
    rw [e]
    exact Bs.inv_mem h1
  obtain ⟨hirr, y₀, hy₀, hidx⟩ :=
    hG.nat α hc.1 (↥V ⧸ Bs.subgroupOf V) hsqY hcardY ρ hρQ hρL
  set Vo := ⁅V, L⁆ with hVodef
  have hVoV : Vo ≤ V := commutator_le_self_of (hLG.trans hVs)
  have hVon : G₀ ≤ Subgroup.normalizer (Vo : Set X.Universal) :=
    S38E.le_normalizer_commutator' hVs hLn
  have hVoconj : ∀ g ∈ G₀, ∀ v ∈ Vo, g * v * g⁻¹ ∈ Vo := fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hVon hg) v).mp hv
  have hVoB : Vo ≤ Subgroup.centralizer (Bs : Set X.Universal) := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbV := hBV hb
    have hl' : l ∈ G₀ := hLG hl
    have hv' : l * v * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hVs hl') v).mp hv
    have hlb : l⁻¹ * b * l ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hVs (G₀.inv_mem hl')) b).mp hbV
      rwa [inv_inv] at this
    set c := b⁻¹ * (l⁻¹ * b * l) with hcdef
    have hcZ : c ∈ Zc := by
      have := hb.1.2 _ (L.inv_mem hl)
      have hb' : b⁻¹ ∈ Bs := Bs.inv_mem hb
      have h1 := hb'.1.2 _ (L.inv_mem hl)
      have e : c = ⁅b⁻¹, l⁻¹⁆ := by
        rw [hcdef]
        simp only [commutatorElement_def]
        group
      rw [e]
      exact h1
    have hcV : c ∈ V := hcZ.1
    have h1 : ⁅v, l⁻¹ * b * l⁆ = ⁅v, b⁆ := by
      have e : l⁻¹ * b * l = b * c := by
        rw [hcdef]
        group
      rw [e, commutatorElement_mul_right_of (hcen v hv c hcV b (hVG hbV))]
      have : ⁅v, c⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_iff.mp hcZ.2 v hv)
      rw [this, mul_one]
    have h2 : ⁅l * v * l⁻¹, b⁆ = ⁅v, b⁆ := by
      rw [commutatorElement_conj_left, hcen v hv _ hlb l hl', h1]
    have e : ⁅v, l⁆ = v * (l * v * l⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    have h3 : ⁅v, l⁆ * b * ⁅v, l⁆⁻¹ = b := by
      have h4 : ⁅⁅v, l⁆, b⁆ = 1 := by
        rw [e, commutatorElement_mul_left_of (hcen _ (V.inv_mem hv') b hbV v (hVG hv))]
        have h5 : ⁅(l * v * l⁻¹)⁻¹, b⁆ = ⁅l * v * l⁻¹, b⁆⁻¹ := by
          have e2 : ⁅(l * v * l⁻¹)⁻¹, b⁆ =
              (l * v * l⁻¹)⁻¹ * ⁅l * v * l⁻¹, b⁆⁻¹ * (l * v * l⁻¹)⁻¹⁻¹ := by
            simp only [commutatorElement_def]
            group
          rw [e2]
          have := hcen _ hv' b hbV _ (hVG (V.inv_mem hv'))
          rw [show (l * v * l⁻¹)⁻¹ * ⁅l * v * l⁻¹, b⁆⁻¹ * (l * v * l⁻¹)⁻¹⁻¹ =
            ((l * v * l⁻¹)⁻¹ * ⁅l * v * l⁻¹, b⁆ * (l * v * l⁻¹)⁻¹⁻¹)⁻¹ by group, this]
        rw [h5, h2, inv_mul_cancel]
      rw [commutatorElement_eq_one_iff_mul_comm] at h4
      rw [h4, mul_inv_cancel_right]
    calc b * ⁅v, l⁆ = ⁅v, l⁆ * b * ⁅v, l⁆⁻¹ * ⁅v, l⁆ := by rw [h3]
      _ = ⁅v, l⁆ * b := by group
  have hVVoB : V ≤ Vo ⊔ Bs := by
    set W : Subgroup (↥V ⧸ Bs.subgroupOf V) := (Vo.subgroupOf V).map (QuotientGroup.mk' _)
    have hW : W = ⊤ := by
      refine (hirr W ?_).resolve_left ?_
      · rintro ⟨l, hl0⟩ hl _ ⟨v, hv, rfl⟩
        refine ⟨conjK hVs ⟨l, hl0⟩ v, ?_, rfl⟩
        rw [SetLike.mem_coe] at hv ⊢
        rw [Subgroup.mem_subgroupOf, conjK_apply_coe]
        exact hVoconj l hl0 v (Subgroup.mem_subgroupOf.mp hv)
      · intro hWb
        obtain ⟨l, hl, hne1⟩ := hρL
        apply hne1
        ext y
        induction y using QuotientGroup.induction_on with
        | H v =>
          rw [MulAut.one_apply, hρmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
          have hc' : ((conjK hVs l v)⁻¹ * v : ↥V) ∈ Vo.subgroupOf V := by
            rw [Subgroup.mem_subgroupOf]
            have e : (((conjK hVs l v)⁻¹ * v : ↥V) : X.Universal) =
                ⁅(l : X.Universal), (v : X.Universal)⁻¹⁆ := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjK_apply_coe,
                commutatorElement_def]
              group
            rw [e, ← commutatorElement_inv]
            exact Vo.inv_mem (Subgroup.commutator_mem_commutator (V.inv_mem v.2) hl)
          have : (QuotientGroup.mk' (Bs.subgroupOf V) ((conjK hVs l v)⁻¹ * v)) ∈ W :=
            ⟨_, hc', rfl⟩
          rw [hWb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
            Subgroup.mem_subgroupOf] at this
          exact this
    intro v hv
    have hmem : (QuotientGroup.mk' (Bs.subgroupOf V) ⟨v, hv⟩) ∈ W := by
      rw [hW]
      exact Subgroup.mem_top _
    obtain ⟨a, ha, hae⟩ := hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hae
    have e : v = (a : X.Universal) * ((a⁻¹ * ⟨v, hv⟩ : ↥V) : X.Universal) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha))
      (Subgroup.mem_sup_right hae)
  have hVoBZ : Vo ⊓ Bs ≤ Zc := by
    rintro x ⟨hxVo, hxB⟩
    refine Subgroup.mem_inf.mpr ⟨hVoV hxVo, ?_⟩
    have hle : Vo ⊔ Bs ≤ Subgroup.centralizer ({x} : Set X.Universal) := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (Subgroup.mem_centralizer_iff.mp (hVoB ha) x hxB)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (Subgroup.mem_centralizer_iff.mp (hVoB hxVo) b hb).symm
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hle (hVVoB hw)) x (Set.mem_singleton x)).symm
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective y₀
  have hVoBn : Vo ≤ Subgroup.normalizer (Bs : Set X.Universal) := (hVoV.trans hVG).trans hBn
  obtain ⟨x₀, hx₀, b₀, hb₀, hxb⟩ := exists_mul_of_mem_sup hVoBn (hVVoB w₀.2)
  have hx₀V : x₀ ∈ V := hVoV hx₀
  have hy₀eq : (QuotientGroup.mk w₀ : ↥V ⧸ Bs.subgroupOf V) = QuotientGroup.mk ⟨x₀, hx₀V⟩ := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : ((w₀⁻¹ * ⟨x₀, hx₀V⟩ : ↥V) : X.Universal) = b₀⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hxb]
      group
    rw [e]
    exact Bs.inv_mem hb₀
  have hφmul : ∀ v w : ↥V, ⁅x₀, ((v * w : ↥V) : X.Universal)⁆ =
      ⁅x₀, (v : X.Universal)⁆ * ⁅x₀, (w : X.Universal)⁆ := fun v w =>
    commutatorElement_mul_right_of (hcen x₀ hx₀V w w.2 v (hVG v.2))
  let φ : ↥V →* X.Universal :=
    { toFun := fun v => ⁅x₀, (v : X.Universal)⁆
      map_one' := by simp
      map_mul' := hφmul }
  have hφB : ∀ b ∈ Bs.subgroupOf V, φ b = 1 := by
    intro b hb
    change ⁅x₀, (b : X.Universal)⁆ = 1
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hVoB hx₀) b (Subgroup.mem_subgroupOf.mp hb)).symm
  let φb : ↥V ⧸ Bs.subgroupOf V →* X.Universal := QuotientGroup.lift _ φ hφB
  have hφb : ∀ v : ↥V, φb (QuotientGroup.mk v) = ⁅x₀, (v : X.Universal)⁆ := fun v => rfl
  have hker : Subgroup.closure {x | ∃ l : ↥G₀, (l : X.Universal) ∈ L ∧
      ρ l (QuotientGroup.mk w₀) = QuotientGroup.mk w₀ ∧ ∃ y, x = ρ l y * y⁻¹} ≤ φb.ker := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, hly, y, rfl⟩
    induction y using QuotientGroup.induction_on with
    | H w =>
      rw [SetLike.mem_coe, MonoidHom.mem_ker, hρmk, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul, hφb]
      rw [hy₀eq, hρmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hly
      have hl0 : (l : X.Universal) ∈ G₀ := l.2
      have hc₁ : (l : X.Universal) * x₀⁻¹ * (l : X.Universal)⁻¹ * x₀ ∈ Zc := by
        refine hVoBZ ⟨?_, ?_⟩
        · have e : (l : X.Universal) * x₀⁻¹ * (l : X.Universal)⁻¹ * x₀ =
              ⁅(l : X.Universal), x₀⁻¹⁆ := by
            simp only [commutatorElement_def]
            group
          rw [e, ← commutatorElement_inv]
          exact Vo.inv_mem (Subgroup.commutator_mem_commutator (V.inv_mem hx₀V) hl)
        · have e : (((conjK hVs l ⟨x₀, hx₀V⟩)⁻¹ * ⟨x₀, hx₀V⟩ : ↥V) : X.Universal) =
              (l : X.Universal) * x₀⁻¹ * (l : X.Universal)⁻¹ * x₀ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjK_apply_coe]
            group
          rw [← e]
          exact hly
      have hc₂ : x₀⁻¹ * ((l : X.Universal)⁻¹ * x₀ * (l : X.Universal)) ∈ Zc := by
        have := (Subgroup.mem_normalizer_iff.mp (hZcn (G₀.inv_mem hl0)) _).mp hc₁
        have e : (l : X.Universal)⁻¹ * ((l : X.Universal) * x₀⁻¹ * (l : X.Universal)⁻¹ * x₀) *
            (l : X.Universal)⁻¹⁻¹ = x₀⁻¹ * ((l : X.Universal)⁻¹ * x₀ * (l : X.Universal)) := by
          group
        rwa [e] at this
      have hwV := w.2
      have hlw : (l : X.Universal)⁻¹ * w * (l : X.Universal) ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (hVs (G₀.inv_mem hl0)) w).mp hwV
        rwa [inv_inv] at this
      have hlwl : (l : X.Universal) * w * (l : X.Universal)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hVs hl0) w).mp hwV
      have hlx : (l : X.Universal)⁻¹ * x₀ * (l : X.Universal) ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (hVs (G₀.inv_mem hl0)) x₀).mp hx₀V
        rwa [inv_inv] at this
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjK_apply_coe]
      rw [commutatorElement_mul_right_of (hcen x₀ hx₀V _ (V.inv_mem hwV) _ (hVG hlwl))]
      have h1 : ⁅x₀, (l : X.Universal) * w * (l : X.Universal)⁻¹⁆ = ⁅x₀, (w : X.Universal)⁆ := by
        have e : ⁅x₀, (l : X.Universal) * w * (l : X.Universal)⁻¹⁆ =
            (l : X.Universal) * ⁅(l : X.Universal)⁻¹ * x₀ * (l : X.Universal), (w : X.Universal)⁆ *
              (l : X.Universal)⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e, hcen _ hlx _ hwV _ hl0]
        set c := x₀⁻¹ * ((l : X.Universal)⁻¹ * x₀ * (l : X.Universal)) with hcdef
        have e2 : (l : X.Universal)⁻¹ * x₀ * (l : X.Universal) = x₀ * c := by
          rw [hcdef]
          group
        rw [e2, commutatorElement_mul_left_of (hcen c hc₂.1 _ hwV x₀ (hVG hx₀V))]
        have : ⁅c, (w : X.Universal)⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact (Subgroup.mem_centralizer_iff.mp hc₂.2 w hwV).symm
        rw [this, one_mul]
      have h2 : ⁅x₀, (w : X.Universal)⁻¹⁆ = ⁅x₀, (w : X.Universal)⁆⁻¹ := by
        have h3 := commutatorElement_mul_right_of (a := x₀) (b := (w : X.Universal))
          (c := (w : X.Universal)⁻¹) (hcen x₀ hx₀V _ (V.inv_mem hwV) _ (hVG hwV))
        rw [mul_inv_cancel, commutatorElement_one_right] at h3
        exact eq_inv_of_mul_eq_one_right h3.symm
      rw [h1, h2, mul_inv_cancel]
  have hrange : Nat.card φb.range ≤ 2 := by
    rw [← Subgroup.index_ker]
    have h0 : (Subgroup.closure {x | ∃ l : ↥G₀, (l : X.Universal) ∈ L ∧
        ρ l (QuotientGroup.mk w₀) = QuotientGroup.mk w₀ ∧ ∃ y, x = ρ l y * y⁻¹}).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (Subgroup.index_dvd_of_le hker)).trans hidx
  set S₀ := φb.range with hS₀def
  have hx₀S : ∀ w ∈ V, ⁅x₀, w⁆ ∈ S₀ := fun w hw => ⟨QuotientGroup.mk ⟨w, hw⟩, rfl⟩
  let U₀ : Subgroup X.Universal :=
    { carrier := {u | u ∈ V ∧ ∀ w ∈ V, ⁅u, w⁆ ∈ S₀}
      one_mem' := ⟨V.one_mem, fun w _ => by rw [commutatorElement_one_left]; exact S₀.one_mem⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨V.mul_mem ha hb, fun w hw => ?_⟩
        rw [commutatorElement_mul_left_of (hcen b hb w hw a (hVG ha))]
        exact S₀.mul_mem (hb' w hw) (ha' w hw)
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨V.inv_mem ha, fun w hw => ?_⟩
        have e : ⁅a⁻¹, w⁆ = a⁻¹ * ⁅a, w⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e, show a⁻¹ * ⁅a, w⁆⁻¹ * a⁻¹⁻¹ = (a⁻¹ * ⁅a, w⁆ * a⁻¹⁻¹)⁻¹ by group,
          hcen a ha w hw _ (hVG (V.inv_mem ha))]
        exact S₀.inv_mem (ha' w hw) }
  have hZcU : Zc ≤ U₀ := by
    intro z hz
    refine ⟨hz.1, fun w hw => ?_⟩
    have : ⁅z, w⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hz.2 w hw).symm
    rw [this]
    exact S₀.one_mem
  set Xc := Subgroup.closure {y | ∃ l ∈ L, l * x₀ * l⁻¹ = y} with hXcdef
  have hXcU : Xc ≤ U₀ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl0 := hLG hl
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hVs hl0) x₀).mp hx₀V, fun w hw => ?_⟩
    rw [commutatorElement_conj_left, hcen x₀ hx₀V _ ?_ l hl0]
    · have hlw : l⁻¹ * w * l ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (hVs (G₀.inv_mem hl0)) w).mp hw
        rwa [inv_inv] at this
      exact hx₀S _ hlw
    · have := (Subgroup.mem_normalizer_iff.mp (hVs (G₀.inv_mem hl0)) w).mp hw
      rwa [inv_inv] at this
  have hXcVo : Xc ≤ Vo := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact hVoconj l (hLG hl) x₀ hx₀
  have hXcV : Xc ≤ V := hXcVo.trans hVoV
  have hVoU : Vo ≤ U₀ := by
    set W : Subgroup (↥V ⧸ Bs.subgroupOf V) := (Xc.subgroupOf V).map (QuotientGroup.mk' _)
    have hXcconj : ∀ l ∈ L, ∀ x ∈ Xc, l * x * l⁻¹ ∈ Xc := by
      intro l hl x hx
      have hle : Xc ≤ Xc.comap (MulAut.conj l).toMonoidHom := by
        rw [Subgroup.closure_le]
        rintro _ ⟨l', hl', rfl⟩
        show (MulAut.conj l) (l' * x₀ * l'⁻¹) ∈ Xc
        refine Subgroup.subset_closure ⟨l * l', L.mul_mem hl hl', ?_⟩
        simp only [MulAut.conj_apply]
        group
      exact hle hx
    have hW : W = ⊤ := by
      refine (hirr W ?_).resolve_left ?_
      · rintro ⟨l, hl0⟩ hl _ ⟨v, hv, rfl⟩
        refine ⟨conjK hVs ⟨l, hl0⟩ v, ?_, rfl⟩
        rw [SetLike.mem_coe] at hv ⊢
        rw [Subgroup.mem_subgroupOf, conjK_apply_coe]
        exact hXcconj l hl v (Subgroup.mem_subgroupOf.mp hv)
      · intro hWb
        apply hy₀
        rw [hy₀eq]
        have hx₀Xc : x₀ ∈ Xc := Subgroup.subset_closure ⟨1, L.one_mem, by group⟩
        have : QuotientGroup.mk' (Bs.subgroupOf V) ⟨x₀, hx₀V⟩ ∈ W :=
          ⟨⟨x₀, hx₀V⟩, Subgroup.mem_subgroupOf.mpr hx₀Xc, rfl⟩
        rw [hWb, Subgroup.mem_bot] at this
        exact this
    intro a ha
    have hmem : (QuotientGroup.mk' (Bs.subgroupOf V) ⟨a, hVoV ha⟩) ∈ W := by
      rw [hW]
      exact Subgroup.mem_top _
    obtain ⟨c, hcX, hce⟩ := hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hce
    have hcXc : (c : X.Universal) ∈ Xc := Subgroup.mem_subgroupOf.mp hcX
    have hbVo : ((c⁻¹ * ⟨a, hVoV ha⟩ : ↥V) : X.Universal) ∈ Vo := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Vo.mul_mem (Vo.inv_mem (hXcVo hcXc)) ha
    have e : a = (c : X.Universal) * ((c⁻¹ * ⟨a, hVoV ha⟩ : ↥V) : X.Universal) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact U₀.mul_mem (hXcU hcXc) (hZcU (hVoBZ ⟨hbVo, hce⟩))
  obtain ⟨δ, hcδ, hδ1, -, hdδ⟩ := hG.exists_crit_back hc
  set Vβ := Vi X β 1 with hVβdef
  have hVβV : Vβ ≤ V := S38E.vi_one_le_vv X hαβ
  have hVβab := S38E.commutator_vi_one_eq_bot X hG.h20 (by rw [hG.b4]; norm_num) β
  have hTs : Qv X β ≤ G₀ := qv_le_stab_of_isMVtx X hG.h20 hc.1 hαβ
  have hTVβ : Qv X β ≤ Subgroup.normalizer (Vβ : Set X.Universal) :=
    (qv_le_stab X β).trans (stab_le_normalizer_vi β 1)
  have hVoVβ : V ≤ Vo ⊔ Vβ := by
    have hKn : G₀ ≤ Subgroup.normalizer ((Vo ⊔ Vβ : Subgroup X.Universal) :
        Set X.Universal) := by
      rw [hG₀def, hG.lt_sup α β hc.1 hαβ]
      refine sup_le ?_ (le_normalizer_sup (hTs.trans hVon) hTVβ)
      exact le_normalizer_of_conj fun l hl x hx => conj_mem_of_commutator_mem hx
        (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator
          (sup_le hVoV hVβV hx) hl))
    exact S38E.vv_le_of_vi_le X hαβ hKn le_sup_right
  have hZμ : ZM X μ ≤ Vβ := by
    rw [← zv_of_isMVtx X (hG.isMVtx_two hc)]
    refine zv_le_vi' ?_
    rw [dist_eq_one_of_adj X (hG.adj_one_two hc)]
  have hZδ : ZM X δ ≤ V := S38E.zm_le_vv X (hcδ.isMVtx_right X hG.h20) (by omega)
  have hVoVβn : Vo ≤ Subgroup.normalizer (Vβ : Set X.Universal) :=
    ((hVoV.trans hVQ).trans (qv_le_qv X hG.h20 hc.1 hαβ)).trans hTVβ
  have hRle : ⁅ZM X δ, ZM X μ⁆ ≤ S₀ := by
    rw [Subgroup.commutator_le]
    intro z hz z' hz'
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hVoVβn (hVoVβ (hZδ hz))
    rw [commutatorElement_mul_left_of (hcen b (hVβV hb) z' (hVβV (hZμ hz')) a
      (hVG (hVoV ha)))]
    have : ⁅b, z'⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hb (hZμ hz')
      rwa [hVβab, Subgroup.mem_bot] at this
    rw [this, one_mul]
    exact (hVoU ha).2 z' (hVβV (hZμ hz'))
  have hcard : 2 < Nat.card ↥⁅ZM X δ, ZM X μ⁆ := by
    have := hG.r_card _ δ hcδ
    rw [Subgroup.commutator_comm] at this
    exact this
  have : Finite ↥S₀ := Finite.of_surjective _ φb.rangeRestrict_surjective
  have := Subgroup.card_le_of_le hRle
  omega

theorem false : False := by
  obtain ⟨α, α', hc⟩ := exists_isCritical X hG.h20
  exact hG.false_of_isCritical hc

end G2Hyp

end CFSG.Quasithin.MS93.S38G

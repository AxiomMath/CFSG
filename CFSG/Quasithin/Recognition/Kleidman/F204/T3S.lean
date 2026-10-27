module

public import CFSG.Quasithin.Recognition.Kleidman.F204.T3Edge
public import CFSG.Quasithin.Recognition.Kleidman.F204.T3Core
public import CFSG.Quasithin.Recognition.Kleidman.F204.T3M
public import CFSG.Quasithin.Recognition.Kleidman.F204.T3Vertex

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

section Cent

variable (F : Frame L1 L2 S D X)
include F

theorem Zv_inf_centralizer_le {α β : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hβ : β ∈ nbrs α)
    {z : G} (hz : z ∈ Zv α) (hzc : z ∈ Subgroup.centralizer (stab α : Set G)) : z ∈ Zv β := by
  have hA := Amal.of_frame F
  obtain ⟨T, h1, h2, -⟩ := hA.exists_common_sylow hβ
  have hzs : z ∈ stab α := pCoreOf_le 2 (stab α) (hA.Zv_le_Qv α hz)
  have hz2 : z ^ 2 = 1 := (hA.isElemAbelian_Zv α).2 z hz
  have hmem : z ∈ quasithinOmegaOneCenter (stab α) :=
    Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hzs, hzc⟩, hz2⟩
  exact (hA.omegaOneCenter_le_Zv h1 h2).2.2 ((hA.omegaOneCenter_le_Zv h1 h2).1 hmem)

end Cent

omit [Finite G] in
theorem vtype_nbr_false {H M : Subgroup G} {α β : Geo H M} (hα : vtype α = true)
    (hβ : β ∈ nbrs α) : vtype β = false := by
  have := vtype_ne_of_adj (show (graph _ _ _).Adj α β from hβ)
  rw [hα] at this
  simpa using this.symm

section Hyp

variable (F : Frame L1 L2 S D X)

structure T3Hyp (α : Geo (P1 L1 L2 S) (P2 L1 L2 S)) (N A : Subgroup G) : Prop where
  vt : vtype α = true
  Ns : N ≤ stab α
  Nn : ∀ n ∈ N, ∀ g ∈ stab α, g * n * g⁻¹ ∈ N
  big : ∀ g ∈ stab α, ∃ n ∈ N, n⁻¹ * g ∈ Qv α
  comm : ∀ δ ∈ nbrs α, ∀ z ∈ Zv δ, ∀ n ∈ N, ⁅z, n⁆ ∈ Zv α
  Ax : A ≤ stab α
  A2 : IsPGroup 2 (A.subgroupOf (stab α))
  Ant : ∃ a ∈ A, ∃ v ∈ Zv α, a * v ≠ v * a
  idx : (Zv α ⊓ Subgroup.centralizer (A : Set G)).relIndex (Zv α) ≤ (A ⊓ Qv α).relIndex A

variable {α : Geo (P1 L1 L2 S) (P2 L1 L2 S)} {N A : Subgroup G} (h : T3Hyp α N A)
include F h

theorem T3Hyp.fix {β : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hβ : β ∈ nbrs α) {r : G}
    (hrα : r ∈ stab α) (hrβ : r ∈ stab β) (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1) :
    ∀ v ∈ Zv α, v * r = r * v → v ∈ Subgroup.centralizer (stab α : Set G) := by
  intro v hv hvr
  refine fix_three_vertex F h.vt hβ h.Ax h.A2 h.Ant h.idx hrα hrβ hr3 ?_ v hv hvr.symm
  intro hq
  exact hr1 (eq_one_of_mem_Qv_of_pow_three hq hr3)

theorem T3Hyp.Mc_le {β β' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hβ : β ∈ nbrs α) {r : G}
    (hrα : r ∈ stab α) (hrβ : r ∈ stab β) (hrβ' : r ∈ stab β') (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1)
    (e : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) (heN : (e : G) ∈ N) (he : e • β = β') :
    Mc β' r ≤ Mc β r := by
  have hA := Amal.of_frame F
  have hβf : vtype β = false := vtype_nbr_false h.vt hβ
  have heα : (e : G) ∈ stab α := h.Ns heN
  intro x hx
  set r' : G := (e : G)⁻¹ * r * (e : G) with hr'
  have hrr' : (e : G) * r' * (e : G)⁻¹ = r := by rw [hr']; group
  have hr'β : r' ∈ stab β := by
    have : r ∈ stab (e • β) := by rw [he]; exact hrβ'
    rw [stab_smul, mem_conjSub] at this
    exact this
  have hr'3 : r' ^ 3 = 1 := by
    have := conj_pow (a := (e : G)⁻¹) (b := r) (i := 3)
    rw [inv_inv, hr3] at this
    rw [hr', this]; group
  have hr'1 : r' ≠ 1 := by
    intro h1
    apply hr1
    rw [← hrr', h1]; group
  have hMeq : Mc β r' = Mc β r := Mc_eq_of_three F hβf hr'β hr'3 hr'1 hrβ hr3 hr1
  have hx' : x ∈ Mc (e • β) ((e : G) * r' * (e : G)⁻¹) := by rw [hrr', he]; exact hx
  have hm : (e : G)⁻¹ * x * (e : G) ∈ Mc β r := by
    rw [← hMeq]; exact (mem_Mc_conj e β r' x).mp hx'
  set m : G := (e : G)⁻¹ * x * (e : G) with hmdef
  obtain ⟨hmZ, hmr⟩ := mem_Mc.mp hm
  obtain ⟨hxZ, hxr⟩ := mem_Mc.mp hx
  have hxe : x = (e : G) * m * (e : G)⁻¹ := by rw [hmdef]; group
  have hz : x * m⁻¹ ∈ Zv α := by
    have h1 := h.comm β hβ m hmZ ((e : G)⁻¹) (N.inv_mem heN)
    have h2 := (Subgroup.mem_normalizer_iff.mp (hA.stab_le_normalizer_Zv α heα) _).mp h1
    have : (e : G) * ⁅m, (e : G)⁻¹⁆ * (e : G)⁻¹ = x * m⁻¹ := by
      rw [hxe]; simp only [commutatorElement_def]; group
    rw [← this]; exact h2
  have hzr : (x * m⁻¹) * r = r * (x * m⁻¹) := by
    have hmr' : m⁻¹ * r = r * m⁻¹ := by
      calc m⁻¹ * r = m⁻¹ * (r * m) * m⁻¹ := by group
        _ = m⁻¹ * (m * r) * m⁻¹ := by rw [hmr]
        _ = r * m⁻¹ := by group
    calc x * m⁻¹ * r = x * (m⁻¹ * r) := by group
      _ = x * (r * m⁻¹) := by rw [hmr']
      _ = (x * r) * m⁻¹ := by group
      _ = (r * x) * m⁻¹ := by rw [hxr]
      _ = r * (x * m⁻¹) := by group
  have hzc := h.fix F hβ hrα hrβ hr3 hr1 _ hz hzr
  have hzβ : x * m⁻¹ ∈ Zv β := Zv_inf_centralizer_le F hβ hz hzc
  have hxβ : x ∈ Zv β := by
    have := (Zv β).mul_mem hzβ hmZ
    simpa using this
  exact mem_Mc.mpr ⟨hxβ, hxr⟩

theorem T3Hyp.Mc_indep {β β' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hβ : β ∈ nbrs α)
    (hβ' : β' ∈ nbrs α) {r r' : G} (hr : r ∈ stab β) (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1)
    (hr'β : r' ∈ stab β') (hr'3 : r' ^ 3 = 1) (hr'1 : r' ≠ 1) : Mc β r = Mc β' r' := by
  have hA := Amal.of_frame F
  obtain ⟨r₀, h0α, h0β, h0β', h03, h01⟩ := exists_three_two F h.vt hβ hβ'
  have hcore : Mc β' r₀ = Mc β r₀ := by
    refine le_antisymm ?_ ?_
    · obtain ⟨e, heN, he⟩ := trans_of_big h.Ns h.big hA hβ hβ'
      exact h.Mc_le F hβ h0α h0β h0β' h03 h01 e heN he
    · obtain ⟨e, heN, he⟩ := trans_of_big h.Ns h.big hA hβ' hβ
      exact h.Mc_le F hβ' h0α h0β' h0β h03 h01 e heN he
  calc Mc β r = Mc β r₀ :=
        Mc_eq_of_three F (vtype_nbr_false h.vt hβ) hr hr3 hr1 h0β h03 h01
    _ = Mc β' r₀ := hcore.symm
    _ = Mc β' r' :=
        Mc_eq_of_three F (vtype_nbr_false h.vt hβ') h0β' h03 h01 hr'β hr'3 hr'1

theorem T3Hyp.Mc_bot {β : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hβ : β ∈ nbrs α) {r : G}
    (hrβ : r ∈ stab β) (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1) : Mc β r = ⊥ := by
  have hA := Amal.of_frame F
  have hβα : α ∈ nbrs β := mem_nbrs_symm hβ
  have hle : Mc β r ≤ stab α ⊓ stab β := by
    intro x hx
    have hxZ := (mem_Mc.mp hx).1
    have hxQ := hA.Zv_le_Qv β hxZ
    exact ⟨hA.Qv_le_stab_of_mem_nbrs hβα hxQ, pCoreOf_le 2 (stab β) hxQ⟩
  have tonorm : ∀ (K : Subgroup G), (∀ g ∈ K, ∀ x ∈ Mc β r, g * x * g⁻¹ ∈ Mc β r) →
      K ≤ Subgroup.normalizer ((Mc β r : Subgroup G) : Set G) := by
    intro K key g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact key g hg x
    · intro hx
      have := key g⁻¹ (K.inv_mem hg) _ hx
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [e] at this
  refine hA.eq_bot_of_normalizes_both (show (graph _ _ _).Adj α β from hβ) hle ?_ ?_
  ·
    refine tonorm _ ?_
    intro g hg x hx
    set g' : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨g, (mem_stab.mp hg).1⟩ with hg'
    have hgα : g' • α = α := smul_eq_of_mem_stab hg
    have hβ'' : g' • β ∈ nbrs α := by
      have := (smul_adj g').mpr (show (graph _ _ _).Adj α β from hβ)
      rwa [hgα] at this
    have hr'' : g * r * g⁻¹ ∈ stab (g' • β) := by
      rw [stab_smul, mem_conjSub]
      have e : (g' : G)⁻¹ * (g * r * g⁻¹) * (g' : G) = r := by
        show g⁻¹ * (g * r * g⁻¹) * g = r
        group
      rw [e]; exact hrβ
    have hr''3 : (g * r * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hr3]; group
    have hr''1 : g * r * g⁻¹ ≠ 1 := by
      intro h1
      apply hr1
      have : r = g⁻¹ * (g * r * g⁻¹) * g := by group
      rw [this, h1]; group
    have hM := h.Mc_indep F hβ'' hβ hr'' hr''3 hr''1 hrβ hr3 hr1
    have hxx : (g' : G)⁻¹ * (g * x * g⁻¹) * (g' : G) ∈ Mc β r := by
      have e : (g' : G)⁻¹ * (g * x * g⁻¹) * (g' : G) = x := by
        show g⁻¹ * (g * x * g⁻¹) * g = x
        group
      rw [e]; exact hx
    have := (mem_Mc_conj g' β r (g * x * g⁻¹)).mpr hxx
    have e2 : (g' : G) * r * (g' : G)⁻¹ = g * r * g⁻¹ := rfl
    rw [e2, hM] at this
    exact this
  ·
    refine tonorm _ ?_
    intro g hg x hx
    set g' : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨g, (mem_stab.mp hg).1⟩ with hg'
    have hgβ : g' • β = β := smul_eq_of_mem_stab hg
    have hr'' : g * r * g⁻¹ ∈ stab β := by
      have := (stab β).mul_mem ((stab β).mul_mem hg hrβ) ((stab β).inv_mem hg)
      exact this
    have hr''3 : (g * r * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hr3]; group
    have hr''1 : g * r * g⁻¹ ≠ 1 := by
      intro h1
      apply hr1
      have : r = g⁻¹ * (g * r * g⁻¹) * g := by group
      rw [this, h1]; group
    have hM := Mc_eq_of_three F (vtype_nbr_false h.vt hβ) hr'' hr''3 hr''1 hrβ hr3 hr1
    have hxx : (g' : G)⁻¹ * (g * x * g⁻¹) * (g' : G) ∈ Mc β r := by
      have e : (g' : G)⁻¹ * (g * x * g⁻¹) * (g' : G) = x := by
        show g⁻¹ * (g * x * g⁻¹) * g = x
        group
      rw [e]; exact hx
    have := (mem_Mc_conj g' β r (g * x * g⁻¹)).mpr hxx
    have e2 : (g' : G) * r * (g' : G)⁻¹ = g * r * g⁻¹ := rfl
    rw [e2, hgβ, hM] at this
    exact this

theorem T3Hyp.Zv_le {β : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hβ : β ∈ nbrs α) : Zv β ≤ Zv α := by
  have hA := Amal.of_frame F
  obtain ⟨r, hrα, hrβ, -, hr3, hr1⟩ := exists_three_two F h.vt hβ hβ
  have hrN : r ∈ N := three_mem_of_big h.Ns h.Nn h.big hrα hr3
  have hbot := h.Mc_bot F hβ hrβ hr3 hr1
  have hnorm : ∀ z ∈ Zv β, ⁅z, r⁆ ∈ Zv β := by
    intro z hz
    have e : ⁅z, r⁆ = z * (r * z⁻¹ * r⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Zv β).mul_mem hz
      ((Subgroup.mem_normalizer_iff.mp (hA.stab_le_normalizer_Zv β hrβ) _).mp ((Zv β).inv_mem hz))
  let f : ↥(Zv β) → ↥(Zv β) := fun z => ⟨⁅(z : G), r⁆, hnorm z z.2⟩
  have hinj : Function.Injective f := by
    intro z z' hzz
    have h1 : ⁅(z : G), r⁆ = ⁅(z' : G), r⁆ := congrArg Subtype.val hzz
    have hw : (z' : G)⁻¹ * z ∈ Mc β r := by
      refine mem_Mc.mpr ⟨(Zv β).mul_mem ((Zv β).inv_mem z'.2) z.2, ?_⟩
      simp only [commutatorElement_def] at h1
      have h2 : (z : G) * r * (z : G)⁻¹ = (z' : G) * r * (z' : G)⁻¹ := by
        have := congrArg (fun y => y * r) h1
        simpa using this
      calc (z' : G)⁻¹ * z * r = (z' : G)⁻¹ * ((z : G) * r * (z : G)⁻¹) * z := by group
        _ = (z' : G)⁻¹ * ((z' : G) * r * (z' : G)⁻¹) * z := by rw [h2]
        _ = r * ((z' : G)⁻¹ * z) := by group
    rw [hbot, Subgroup.mem_bot] at hw
    exact Subtype.ext (by simpa using (inv_mul_eq_one.mp hw).symm)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  intro z hz
  obtain ⟨z₀, hz₀⟩ := hsurj ⟨z, hz⟩
  have : ⁅(z₀ : G), r⁆ = z := congrArg Subtype.val hz₀
  rw [← this]
  exact h.comm β hβ z₀ z₀.2 r hrN

end Hyp

section Final

variable (F : Frame L1 L2 S D X)
include F

theorem false_of_Zv_le {α β : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hα : vtype α = true)
    (hβ : β ∈ nbrs α) (hZf : ZFaithful β) (hle : Zv β ≤ Zv α) : False := by
  have hA := Amal.of_frame F
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  obtain ⟨hsyl, -, -⟩ := sylow_sup_Qv F hα hβ
  have hfaith := hZf _ hsyl
  have hQαβ : Qv α ≤ Qv β := by
    intro q hq
    have hqc : q ∈ Subgroup.centralizer (Zv β : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have := (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv α (hle hz)).2) q hq
      exact this.symm
    rw [← hfaith]
    exact ⟨Subgroup.mem_sup_left hq, hqc⟩
  obtain ⟨g, hg1, hg0⟩ := exists_edge_conj_true hα hβ
  have hQx : Qv α = conjSub (g : G) (Q2 L1 L2 S) := by
    rw [← hg1, Qv_smul]; unfold Qv; rw [stab_γ₁ h₂]
  have hQδ : Qv β = conjSub (g : G) (Q1 L1 L2 S) := by
    rw [← hg0, Qv_smul]; unfold Qv; rw [stab_γ₀ h₁]
  have := conjSub_mono (g : G)⁻¹ hQαβ
  rw [hQx, hQδ, conjSub_conjSub_inv, conjSub_conjSub_inv] at this
  exact not_Q2_le_Q1 F this

end Final

end CFSG.Quasithin.Kleidman.F204

module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3D
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3N1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem le_normalizer_sup_of_comm {Y A B : Subgroup G} (hA : ⁅Y, A⁆ ≤ A ⊔ B)
    (hB : ⁅Y, B⁆ ≤ A ⊔ B) : Y ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ y ∈ Y, ∀ a ∈ A ⊔ B, y * a * y⁻¹ ∈ A ⊔ B := by
    intro y hy
    have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj y).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · have h1 : ⁅y, a⁆ ∈ A ⊔ B := hA (Subgroup.commutator_mem_commutator hy ha)
        have h2 : a ∈ A ⊔ B := Subgroup.mem_sup_left ha
        have := (A ⊔ B).mul_mem h1 h2
        simpa [commutatorElement_def, MulAut.conj_apply, mul_assoc] using this
      · have h1 : ⁅y, b⁆ ∈ A ⊔ B := hB (Subgroup.commutator_mem_commutator hy hb)
        have h2 : b ∈ A ⊔ B := Subgroup.mem_sup_right hb
        have := (A ⊔ B).mul_mem h1 h2
        simpa [commutatorElement_def, MulAut.conj_apply, mul_assoc] using this
    intro a ha
    simpa [MulAut.conj_apply] using hle ha
  exact le_normalizer_of_conj_mem key

theorem commutator_sup_le_of_normalizer {A A' B K : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (K : Set G)) (hA' : A' ≤ Subgroup.normalizer (K : Set G))
    (h1 : ⁅A, B⁆ ≤ K) (h2 : ⁅A', B⁆ ≤ K) : ⁅A ⊔ A', B⁆ ≤ K := by
  have e : A ⊔ A' = ⨆ i : Bool, (if i then A else A') := by
    rw [iSup_bool_eq]; rfl
  rw [e]
  refine commutator_iSup_le (by rw [← e]; exact sup_le hA hA') fun i => ?_
  cases i <;> simpa

namespace Step3Ctx

variable {α β α' : Geo H M} (C : Step3Ctx H M S α β α')

include C

theorem stab_eq_sup (P : CritPath α β α') {l : Geo H M} (hl : l ∈ nbrs α') (hlγ : l ≠ P.γ) :
    stab α' = (Qv l ⊔ Zv α) ⊔ Qv α' := by
  have hb := C.hb6
  have hγ : P.γ ∈ nbrs α' := mem_nbrs_comm (P.γ_adj (by omega))
  have hZ : Zv α ≤ stab α' ⊓ stab P.γ :=
    le_inf (Zv_le_stab_pair C.hA C.hc C.hcomm).2
      (Zv_le_stab_of_dist_le_bMin C.hA (by rw [P.dist_start_γ (by omega)]; omega))
  have h1 := sup_edge_eq_stab C.hA C.vtype_alpha' hγ hl (Ne.symm hlγ) hZ C.hc.not_le
  have h2 : Qv α' ⊔ Qv l = stab α' ⊓ stab l :=
    C.h28 (by omega) α' l hl (C.bAt_eq_of_true C.vtype_alpha')
  rw [← h2] at h1
  calc stab α' = Zv α ⊔ (Qv α' ⊔ Qv l) := h1.symm
    _ = (Qv l ⊔ Zv α) ⊔ Qv α' := by ac_rfl

theorem Qv_sup_Zv_le_stab {l : Geo H M} (hl : l ∈ nbrs α') :
    Qv l ⊔ Zv α ≤ stab α' :=
  sup_le (Qv_le_stab_of_mem_nbrs C.hA (mem_nbrs_comm hl))
    (Zv_le_stab_pair C.hA C.hc C.hcomm).2

theorem exists_mem_sup_smul (P : CritPath α β α') {l : Geo H M} (hl : l ∈ nbrs α')
    (hlγ : l ≠ P.γ) {x : Geo H M} (hx : x ∈ nbrs α') :
    ∃ y : ↥(H ⊔ M), (y : G) ∈ Qv l ⊔ Zv α ∧ y • l = x := by
  obtain ⟨g, hg, hgl⟩ := stab_transitive_on_nbrs hl hx
  have hgm : (g : G) ∈ (Qv l ⊔ Zv α) ⊔ Qv α' := by rw [← C.stab_eq_sup P hl hlγ]; exact hg
  obtain ⟨y, hy, q, hq, hyq⟩ := exists_mul_of_mem_sup_of_le_normalizer
    ((C.Qv_sup_Zv_le_stab hl).trans (le_normalizer_pCoreOf 2 (stab α'))) _ hgm
  have hqs : (q : G) ∈ stab l := Qv_le_stab_of_mem_nbrs C.hA hl hq
  have hys : y ∈ stab α' := C.Qv_sup_Zv_le_stab hl hy
  have hqα : q ∈ stab α' := pCoreOf_le 2 _ hq
  have e : g = ⟨y, stab_le _ hys⟩ * ⟨q, stab_le _ hqα⟩ := Subtype.ext hyq
  refine ⟨⟨y, stab_le _ hys⟩, hy, ?_⟩
  have h3 : (⟨q, stab_le _ hqα⟩ : ↥(H ⊔ M)) • l = l := smul_eq_of_mem_stab hqs
  rw [← hgl, e, mul_smul, h3]

theorem le_Vn_of_normalized (P : CritPath α β α') {l : Geo H M} (hl : l ∈ nbrs α')
    (hlγ : l ≠ P.γ) {K : Subgroup G} (hK : K ≤ Vn l)
    (hN : Qv l ⊔ Zv α ≤ Subgroup.normalizer (K : Set G)) {x : Geo H M} (hx : x ∈ nbrs α') :
    K ≤ Vn x := by
  obtain ⟨y, hy, hyl⟩ := C.exists_mem_sup_smul P hl hlγ hx
  rw [← hyl, Vn_smul]
  calc K = conjSub (y : G) K := (conjSub_eq_of_mem_normalizer (hN hy)).symm
    _ ≤ conjSub (y : G) (Vn l) := conjSub_mono _ hK

theorem comm_inter_le_Vn_γ (P : CritPath α β α') {l : Geo H M} (hl : l ∈ nbrs α')
    (hlγ : l ≠ P.γ) : ⁅Vn β ⊓ Qv α', Vn l⁆ ≤ Vn P.γ := by
  have hb := C.hb6
  have hγ : P.γ ∈ nbrs α' := mem_nbrs_comm (P.γ_adj (by omega))
  have hvl : vtype l = false := vtype_false_of_mem_nbrs_true hl C.vtype_alpha'
  have hHVl : ⁅Vn β ⊓ Qv α', Vn l⁆ ≤ Vn l :=
    (C.comm_inter_le P hl hlγ).trans (inf_le_left.trans inf_le_right)
  have hZ'l : Zv α' ≤ Vn l := Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm hl)
  have hZγα' : Zv P.γ ≤ Zv α' := C.Zv_le_Zv_of_mem_nbrs C.vtype_alpha' hγ
  have hcc := C.comm_comm_inter_Qv_le P hl hlγ
  have hN : Qv l ⊔ Zv α ≤ Subgroup.normalizer ((⁅Vn β ⊓ Qv α', Vn l⁆ ⊔ Zv α' : Subgroup G) : Set G) := by
    refine sup_le (le_normalizer_sup_of_comm ?_ ?_) (le_normalizer_sup_of_comm ?_ ?_)
    · rw [Subgroup.commutator_comm]
      exact (hcc.1.trans hcc.2).trans le_sup_right
    · rw [Subgroup.commutator_comm]
      refine le_trans ?_ (hcc.2.trans le_sup_right)
      rw [← C.comm_Vn_Qv_eq hvl]
      exact Subgroup.commutator_mono hZ'l le_rfl
    · rw [C.comm_Zv_alpha_comm_inter P hl hlγ]
      exact bot_le
    · rw [C.comm_eq_Zv_beta, C.Zv_beta_eq_Zv_γ P]
      exact hZγα'.trans le_sup_right
  exact le_sup_left.trans (C.le_Vn_of_normalized P hl hlγ (sup_le hHVl hZ'l) hN hγ)

theorem comm_inter_le_Ctilde (P : CritPath α β α') {l : Geo H M} (hl : l ∈ nbrs α')
    (hlγ : l ≠ P.γ) : ⁅Vn β ⊓ Qv α', Vn l⁆ ≤ Ctilde P.γ := by
  have hb := C.hb6
  have hVγ := C.comm_inter_le_Vn_γ P hl hlγ
  have hHVl : ⁅Vn β ⊓ Qv α', Vn l⁆ ≤ Vn l :=
    (C.comm_inter_le P hl hlγ).trans (inf_le_left.trans inf_le_right)
  have hHVβ : ⁅Vn β ⊓ Qv α', Vn l⁆ ≤ Vn β :=
    (C.comm_inter_le P hl hlγ).trans (inf_le_left.trans inf_le_left)
  obtain ⟨g, hgγ, hgδ, hgε⟩ := C.exists_smul_γ_δ_ε P hl hlγ
  have hP13 := C.oTwoRes_le_sup P (C.vhatData P) hgγ hgδ
  have hNZ : stab P.γ ≤ Subgroup.normalizer (Zv P.γ : Set G) := stab_le_normalizer_Zv C.hA P.γ
  have hWγ := C.Wv_le_stab_γ P
  have hWgγ : conjSub (g : G) (Wv α) ≤ stab P.γ := (C.conj_Wv_le P hgγ hgδ).trans inf_le_right
  have hQγ : Qv P.γ ≤ stab P.γ := pCoreOf_le 2 _
  have hWH : ⁅Wv α, ⁅Vn β ⊓ Qv α', Vn l⁆⁆ ≤ Zv P.γ := by
    have : ⁅Wv α, ⁅Vn β ⊓ Qv α', Vn l⁆⁆ ≤ ⁅Wv α, Wv α⁆ :=
      Subgroup.commutator_mono le_rfl (hHVβ.trans (C.Vn_le_Wv_of_mem_nbrs C.hv C.hc.adj))
    rw [commutator_self_eq_bot (C.isElemAbelian_Wv α)] at this
    exact (le_bot_iff.mp this) ▸ bot_le
  have hWgH : ⁅conjSub (g : G) (Wv α), ⁅Vn β ⊓ Qv α', Vn l⁆⁆ ≤ Zv P.γ := by
    have h1 := C.comm_conj_Wv_Vn P g
    rw [hgε] at h1
    have : ⁅conjSub (g : G) (Wv α), ⁅Vn β ⊓ Qv α', Vn l⁆⁆ ≤ ⁅conjSub (g : G) (Wv α), Vn l⁆ :=
      Subgroup.commutator_mono le_rfl hHVl
    rw [h1] at this
    exact (le_bot_iff.mp this) ▸ bot_le
  have hQH : ⁅Qv P.γ, ⁅Vn β ⊓ Qv α', Vn l⁆⁆ ≤ Zv P.γ := by
    rw [Subgroup.commutator_comm, ← C.comm_Vn_Qv_eq (C.vtype_γ P)]
    exact Subgroup.commutator_mono hVγ le_rfl
  have hS : ⁅(Wv α ⊔ conjSub (g : G) (Wv α)) ⊔ Qv P.γ, ⁅Vn β ⊓ Qv α', Vn l⁆⁆ ≤ Zv P.γ :=
    commutator_sup_le_of_normalizer (sup_le hWγ hWgγ |>.trans hNZ) (hQγ.trans hNZ)
      (commutator_sup_le_of_normalizer (hWγ.trans hNZ) (hWgγ.trans hNZ) hWH hWgH) hQH
  intro h hh
  refine Subgroup.subset_closure ⟨hVγ hh, fun a ha => ?_⟩
  exact hS (Subgroup.commutator_mem_commutator (hP13 ha) hh)

theorem exists_oTwoRes_smul {γ : Geo H M} (hγ : vtype γ = false) {ν ν' : Geo H M}
    (hν : ν ∈ nbrs γ) (hν' : ν' ∈ nbrs γ) :
    ∃ x : ↥(H ⊔ M), (x : G) ∈ oTwoRes (stab γ) ∧ x • ν = ν' := by
  let V : VhatData γ := (C.nonempty_vhatData hγ).some
  obtain ⟨g, hg, hgν⟩ := stab_transitive_on_nbrs hν hν'
  have hT : Nat.card (V.img (stab γ ⊓ stab ν)) = 8 := by
    rw [V.card_img inf_le_left]; exact relIndex_Qv_inf_false C.hA hν hγ
  have hodd : ∃ t : ↥(stab γ), (t : G) ∈ stab ν ∧ V.ψ t ∉ alternatingGroup (Fin 5) := by
    by_contra hcon
    push Not at hcon
    have hle : V.img (stab γ ⊓ stab ν) ≤ alternatingGroup (Fin 5) := by
      rintro _ ⟨z, hz, rfl⟩
      exact hcon z (Subgroup.mem_subgroupOf.mp hz).2
    have h1 := Subgroup.card_dvd_of_le hle
    rw [hT] at h1
    have h2 := two_mul_nat_card_alternatingGroup (α := Fin 5)
    have h3 : Nat.card (Perm (Fin 5)) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]; simp [Nat.factorial]
    omega
  have hqν : ∀ q : ↥(stab γ), (q : G) ∈ Qv γ → (q : G) ∈ stab ν :=
    fun q hq => Qv_le_stab_of_mem_nbrs C.hA hν hq
  have key : ∃ g'' : ↥(stab γ), V.ψ g'' ∈ alternatingGroup (Fin 5) ∧
      (⟨(g'' : G), stab_le _ g''.2⟩ : ↥(H ⊔ M)) • ν = ν' := by
    by_cases hA : V.ψ ⟨g, hg⟩ ∈ alternatingGroup (Fin 5)
    · exact ⟨⟨g, hg⟩, hA, hgν⟩
    · obtain ⟨t, htν, htA⟩ := hodd
      refine ⟨⟨g, hg⟩ * t⁻¹, ?_, ?_⟩
      · rw [Equiv.Perm.mem_alternatingGroup] at hA htA ⊢
        rw [map_mul, map_inv, map_mul, map_inv]
        rcases Int.units_eq_one_or (Equiv.Perm.sign (V.ψ ⟨g, hg⟩)) with h | h <;>
        rcases Int.units_eq_one_or (Equiv.Perm.sign (V.ψ t)) with h' | h' <;>
        simp_all
      · have e : (⟨(((⟨g, hg⟩ * t⁻¹ : ↥(stab γ))) : G), stab_le _ (⟨g, hg⟩ * t⁻¹).2⟩ : ↥(H ⊔ M)) =
            g * (⟨(t : G), stab_le _ t.2⟩ : ↥(H ⊔ M))⁻¹ := Subtype.ext (by simp)
        have ht : (⟨(t : G), stab_le _ t.2⟩ : ↥(H ⊔ M)) • ν = ν := smul_eq_of_mem_stab htν
        rw [e, mul_smul, inv_smul_eq_iff.mpr ht.symm, hgν]
  obtain ⟨g'', hA, hg''⟩ := key
  have hmem : V.ψ g'' ∈ V.img (oTwoRes (stab γ)) := by rw [V.img_oTwoRes]; exact hA
  obtain ⟨z, hz, hzg⟩ := hmem
  have hzO : (z : G) ∈ oTwoRes (stab γ) := Subgroup.mem_subgroupOf.mp hz
  have hq : ((g''⁻¹ * z : ↥(stab γ)) : G) ∈ Qv γ :=
    (V.ker _).mp (by rw [map_mul, map_inv, hzg]; simp)
  have hqs := hqν _ hq
  have e : (⟨(z : G), stab_le _ z.2⟩ : ↥(H ⊔ M)) =
      (⟨(g'' : G), stab_le _ g''.2⟩ : ↥(H ⊔ M)) *
        (⟨((g''⁻¹ * z : ↥(stab γ)) : G), stab_le _ (g''⁻¹ * z).2⟩ : ↥(H ⊔ M)) :=
    Subtype.ext (by simp)
  have hq' : (⟨((g''⁻¹ * z : ↥(stab γ)) : G), stab_le _ (g''⁻¹ * z).2⟩ : ↥(H ⊔ M)) • ν = ν :=
    smul_eq_of_mem_stab hqs
  exact ⟨⟨(z : G), stab_le _ z.2⟩, hzO, by rw [e, mul_smul, hq', hg'']⟩

theorem comm_Ctilde_Qv (P : CritPath α β α') : ⁅Ctilde P.γ, Qv α'⁆ = ⊥ := by
  have hb := C.hb6
  have hγ : P.γ ∈ nbrs α' := mem_nbrs_comm (P.γ_adj (by omega))
  have hγv := C.vtype_γ P
  obtain ⟨l, hl, hlγ⟩ := exists_nbr_ne C.hA α' hγ
  have hvl : vtype l = false := vtype_false_of_mem_nbrs_true hl C.vtype_alpha'
  have hCVγ : Ctilde P.γ ≤ Vn P.γ := (C.Ctilde_le_Vn_inf P hl hlγ).trans inf_le_left
  have hCVl : Ctilde P.γ ≤ Vn l := (C.Ctilde_le_Vn_inf P hl hlγ).trans inf_le_right
  have hCQ : Ctilde P.γ ≤ Qv α' := hCVl.trans (C.Vn_le_Qv_alpha' hl)
  have hVγs : Vn P.γ ≤ stab P.γ := (Vn_le_Qv' C.hb2 P.γ).trans (pCoreOf_le 2 _)
  have hQα's : Qv α' ≤ stab α' := pCoreOf_le 2 _
  have hQγ : Qv α' ≤ stab P.γ := Qv_le_stab_of_mem_nbrs C.hA hγ
  set U : Subgroup G := ⁅Ctilde P.γ, Qv α'⁆ with hUdef
  have hUC : U ≤ Ctilde P.γ := by
    rw [hUdef, Subgroup.commutator_le]
    intro c hc q hq
    have h1 := (Subgroup.mem_normalizer_iff.mp (C.Ctilde_normal P.γ (hQγ hq)) c⁻¹).mp
      ((Ctilde P.γ).inv_mem hc)
    have e : ⁅c, q⁆ = c * (q * c⁻¹ * q⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (Ctilde P.γ).mul_mem hc h1
  have hUQ : U ≤ Qv α' := by
    rw [hUdef, Subgroup.commutator_le]
    intro c hc q hq
    exact (Qv α').mul_mem ((Qv α').mul_mem ((Qv α').mul_mem (hCQ hc) hq) ((Qv α').inv_mem (hCQ hc)))
      ((Qv α').inv_mem hq)
  have hUV : U ≤ Vn P.γ := hUC.trans hCVγ
  have hU : U ≤ stab P.γ ⊓ stab α' := le_inf (hUV.trans hVγs) (hUQ.trans hQα's)
  have hVn : ∀ K : Subgroup G, K ≤ Vn P.γ → Vn P.γ ≤ Subgroup.normalizer (K : Set G) := by
    intro K hK
    refine le_normalizer_of_conj_mem fun x hx w hw => ?_
    have := isMulCommutative_subgroup_iff.mp (C.isElemAbelian_Vn' P.γ).1 x hx w (hK hw)
    rw [this, mul_inv_cancel_right]
    exact hw
  have hZ'γ : Zv α' ≤ Vn P.γ := C.Zv_α'_le_Vn_γ P
  have hZl : Zv l ≤ Zv α' := C.Zv_le_Zv_of_mem_nbrs C.vtype_alpha' hl
  have hZγα' : Zv P.γ ≤ Zv α' := C.Zv_le_Zv_of_mem_nbrs C.vtype_alpha' hγ
  have hZαβ : Zv α ≤ Vn β := Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm C.hc.adj)
  have hXN : Qv l ⊔ Zv α ≤ Subgroup.normalizer ((Ctilde P.γ ⊔ Zv α' : Subgroup G) : Set G) := by
    refine sup_le (le_normalizer_sup_of_comm ?_ ?_) (le_normalizer_sup_of_comm ?_ ?_)
    · rw [Subgroup.commutator_comm]
      refine le_trans ?_ (hZl.trans le_sup_right)
      rw [← C.comm_Vn_Qv_eq hvl]
      exact Subgroup.commutator_mono hCVl le_rfl
    · rw [Subgroup.commutator_comm]
      refine le_trans ?_ (hZl.trans le_sup_right)
      rw [← C.comm_Vn_Qv_eq hvl]
      exact Subgroup.commutator_mono ((Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm hl))) le_rfl
    · have h1 : ⁅Zv α, Ctilde P.γ⁆ ≤ Zv P.γ :=
        (Subgroup.commutator_mono hZαβ hCVγ).trans
          (by rw [← C.Zv_beta_eq_Zv_γ P]; exact C.comm_Vn_Vn_beta_γ P)
      exact h1.trans ((C.Zv_le_Ctilde P.γ).trans le_sup_left)
    · rw [C.comm_eq_Zv_beta, C.Zv_beta_eq_Zv_γ P]
      exact hZγα'.trans le_sup_right
  have hCN : Ctilde P.γ ≤ Subgroup.normalizer (U : Set G) := hCVγ.trans (hVn U hUV)
  have hZN : Zv α' ≤ Subgroup.normalizer (U : Set G) := hZ'γ.trans (hVn U hUV)
  have hXU : Ctilde P.γ ⊔ Zv α' ≤ Subgroup.normalizer (U : Set G) := sup_le hCN hZN
  have hXCQ : ⁅Ctilde P.γ ⊔ Zv α', Qv α'⁆ ≤ U := by
    refine commutator_sup_le_of_normalizer hCN hZN le_rfl ?_
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (fun z hz => ?_)]
    · exact bot_le
    · exact (Subgroup.mem_centralizer_iff.mpr fun q hq =>
        (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv C.hA α' hz).2 q hq))
  have hXNU : Qv l ⊔ Zv α ≤ Subgroup.normalizer (U : Set G) := by
    refine le_normalizer_of_conj_mem fun y hy u hu => ?_
    have hys : y ∈ stab α' := C.Qv_sup_Zv_le_stab hl hy
    have hQy : conjSub y (Qv α') = Qv α' :=
      conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 (stab α') hys)
    have hXy : conjSub y (Ctilde P.γ) ≤ Ctilde P.γ ⊔ Zv α' := by
      calc conjSub y (Ctilde P.γ) ≤ conjSub y (Ctilde P.γ ⊔ Zv α') :=
            conjSub_mono _ le_sup_left
        _ = Ctilde P.γ ⊔ Zv α' := conjSub_eq_of_mem_normalizer (hXN hy)
    have h1 : conjSub y U ≤ U := by
      calc conjSub y U = ⁅conjSub y (Ctilde P.γ), conjSub y (Qv α')⁆ := Subgroup.map_commutator _ _ _
        _ = ⁅conjSub y (Ctilde P.γ), Qv α'⁆ := by rw [hQy]
        _ ≤ ⁅Ctilde P.γ ⊔ Zv α', Qv α'⁆ := Subgroup.commutator_mono hXy le_rfl
        _ ≤ U := hXCQ
    exact h1 (mul_mem_conjSub hu)
  have hLN : oTwoRes (stab P.γ) ≤ Subgroup.normalizer (U : Set G) := by
    have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (C.comm_Ctilde_oTwoRes hγv)
    refine le_normalizer_of_conj_mem fun x hx u hu => ?_
    have := Subgroup.mem_centralizer_iff.mp (hcen (hUC hu)) x hx
    rw [this, mul_inv_cancel_right]
    exact hu
  have hadj : (graph (H ⊔ M) H M).Adj P.γ α' := P.γ_adj (by omega)
  refine eq_bot_of_normalizer_transitive_vertex C.hA hadj hU ?_ ?_
  · intro ε hε ε' hε'
    obtain ⟨x, hxO, hx⟩ := C.exists_oTwoRes_smul hγv hε hε'
    refine ⟨x, hLN hxO, smul_eq_of_mem_stab (oTwoRes_le _ hxO), hx⟩
  · intro ε hε ε' hε'
    obtain ⟨y₁, hy₁, h₁⟩ := C.exists_mem_sup_smul P hl hlγ hε
    obtain ⟨y₂, hy₂, h₂⟩ := C.exists_mem_sup_smul P hl hlγ hε'
    refine ⟨y₂ * y₁⁻¹, ?_, ?_, ?_⟩
    · exact (Subgroup.normalizer (U : Set G)).mul_mem (hXNU hy₂)
        ((Subgroup.normalizer (U : Set G)).inv_mem (hXNU hy₁))
    · have h1 : (y₂ : G) ∈ stab α' := C.Qv_sup_Zv_le_stab hl hy₂
      have h2 : (y₁ : G) ∈ stab α' := C.Qv_sup_Zv_le_stab hl hy₁
      exact smul_eq_of_mem_stab ((stab α').mul_mem h1 ((stab α').inv_mem h2))
    · rw [mul_smul, inv_smul_eq_iff.mpr h₁.symm, h₂]

theorem conjSub_Ctilde (g : ↥(H ⊔ M)) {γ : Geo H M} (hγ : vtype γ = false) :
    conjSub (g : G) (Ctilde γ) = Ctilde (g • γ) := by
  have hγ' : vtype (g • γ) = false := by rw [vtype_smul]; exact hγ
  rw [C.Ctilde_eq_centralizer hγ, C.Ctilde_eq_centralizer hγ', conjSub_inf, ← Vn_smul, stab_smul,
    ← conjSub_oTwoRes, conjSub_centralizer]

theorem comm_Ctilde_Qv_all (P : CritPath α β α') {ν ξ : Geo H M} (hν : vtype ν = false)
    (hξ : ξ ∈ nbrs ν) : ⁅Ctilde ν, Qv ξ⁆ = ⊥ := by
  have hb := C.hb6
  have hγv := C.vtype_γ P
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (hγv.trans hν.symm)
  have hξ' : g⁻¹ • ξ ∈ nbrs P.γ := by
    have := (smul_adj g⁻¹).mpr hξ
    rwa [inv_smul_smul] at this
  have hα' : α' ∈ nbrs P.γ := P.γ_adj (by omega)
  obtain ⟨h, hh, hhξ⟩ := stab_transitive_on_nbrs hξ' hα'
  have hξ'' : ξ = (g * h⁻¹) • α' := by
    rw [mul_smul, ← hhξ, inv_smul_smul, smul_inv_smul]
  have hγ'' : g • P.γ = (g * h⁻¹) • P.γ := by
    rw [mul_smul, inv_smul_eq_iff.mpr (smul_eq_of_mem_stab hh).symm]
  rw [hξ'', hγ'', Qv_smul, ← C.conjSub_Ctilde (g * h⁻¹) hγv, conjSub_commutator,
    C.comm_Ctilde_Qv P, conjSub_bot]

end Step3Ctx

end F53.Stellmacher

end CFSG.Quasithin

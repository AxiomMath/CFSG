module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.S7Fin
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.LemmaTV
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Claim1
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.VecStab

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem map_stab_smul {β : Geo H M} (θ : ↥(stab β) →* Equiv.Perm (Fin 5)) (k : ↥(H ⊔ M))
    (hk : (k : G) ∈ stab β) (μ : Geo H M) :
    ((stab β ⊓ stab (k • μ)).subgroupOf (stab β)).map θ =
      (((stab β ⊓ stab μ).subgroupOf (stab β)).map θ).map
        (MulAut.conj (θ ⟨k, hk⟩)).toMonoidHom := by
  set ky : ↥(stab β) := ⟨k, hk⟩ with hky
  have hP : (stab β ⊓ stab (k • μ)).subgroupOf (stab β) =
      ((stab β ⊓ stab μ).subgroupOf (stab β)).map (MulAut.conj ky).toMonoidHom := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, stab_smul, mem_conjSub] at hx
      refine ⟨ky⁻¹ * x * ky, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        refine ⟨mul_mem (mul_mem (inv_mem hk) x.2) hk, ?_⟩
        simpa using hx.2
      · simp [MulAut.conj_apply, mul_assoc]
    · rintro ⟨p, hp, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hp
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, stab_smul, mem_conjSub]
      refine ⟨(mul_mem (mul_mem hk p.2) (inv_mem hk)), ?_⟩
      have : (k : G)⁻¹ * (((MulAut.conj ky).toMonoidHom p : ↥(stab β)) : G) * k = p := by
        simp [MulAut.conj_apply, mul_assoc, hky]
      rw [this]; exact hp.2
  rw [hP, Subgroup.map_map]
  have hcomp : θ.comp (MulAut.conj ky).toMonoidHom =
      (MulAut.conj (θ ky)).toMonoidHom.comp θ := by
    ext x
    simp [MulAut.conj_apply]
  rw [hcomp, ← Subgroup.map_map]

theorem comm_le_of_le_normalizer {X A : Subgroup G} (hA : A ≤ Subgroup.normalizer (X : Set G)) :
    ⁅X, A⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro x hx g hg
  have h1 : g * x⁻¹ * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hA hg) x⁻¹).mp (inv_mem hx)
  have : ⁅x, g⁆ = x * (g * x⁻¹ * g⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact mul_mem hx h1

theorem comm_sup_le_of_normalizes {X Y A N : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (A : Set G)) (hY : Y ≤ Subgroup.normalizer (A : Set G))
    (hXA : ⁅X, A⁆ ≤ N) (hYA : ⁅Y, A⁆ ≤ N) : ⁅X ⊔ Y, A⁆ ≤ N := by
  have hmemA : ∀ g ∈ (X ⊔ Y), ∀ y ∈ A, g * y * g⁻¹ ∈ A := fun g hg y hy => by
    have : g ∈ Subgroup.normalizer (A : Set G) := (sup_le hX hY) hg
    exact (Subgroup.mem_normalizer_iff.mp this y).mp hy
  let P : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (A : Set G) ∧ ∀ y ∈ A, ⁅g, y⁆ ∈ N}
      mul_mem' := by
        rintro g g' ⟨hg, hg1⟩ ⟨hg', hg1'⟩
        refine ⟨mul_mem hg hg', fun y hy => ?_⟩
        have hy' : g' * y * g'⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hg' y).mp hy
        have : ⁅g * g', y⁆ = ⁅g, g' * y * g'⁻¹⁆ * ⁅g', y⁆ := by
          simp [commutatorElement_def, mul_assoc]
        rw [this]
        exact mul_mem (hg1 _ hy') (hg1' y hy)
      one_mem' := ⟨one_mem _, fun y hy => by simp⟩
      inv_mem' := by
        rintro g ⟨hg, hg1⟩
        refine ⟨inv_mem hg, fun y hy => ?_⟩
        have hy' : g⁻¹ * y * g ∈ A := by
          have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) y).mp hy
          simpa using this
        have : ⁅g⁻¹, y⁆ = (⁅g, g⁻¹ * y * g⁆)⁻¹ := by
          simp [commutatorElement_def, mul_assoc]
        rw [this]
        exact inv_mem (hg1 _ hy') }
  have hXP : X ≤ P := fun x hx =>
    ⟨hX hx, fun y hy => hXA (Subgroup.commutator_mem_commutator hx hy)⟩
  have hYP : Y ≤ P := fun x hx =>
    ⟨hY hx, fun y hy => hYA (Subgroup.commutator_mem_commutator hx hy)⟩
  rw [Subgroup.commutator_le]
  intro g hg y hy
  exact (sup_le hXP hYP hg).2 y hy

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem exists_nbr_sup_eq_top {β' : Geo H M} (hβ' : vtype β' = false) {y : G} (hy : y ∈ stab β')
    (hyQ : y ∉ Qv β') : ∃ δ ∈ nbrs β', stab β' ≤ (stab β' ⊓ stab δ) ⊔ Subgroup.zpowers y := by
  obtain ⟨hN, θ, βm, hθs, hθk, hsd⟩ := C.exists_secData hβ'
  obtain ⟨μ0, hμ0⟩ := exists_adj β'
  have hμ0' : μ0 ∈ nbrs β' := hμ0
  have hS := CFSG.Quasithin.F53.sylow_stab_inf_left C.hA hμ0'
  have hT := CFSG.QuasithinUnique.Setup.Wreath.isSylowTwoOf_map_hom hS θ
  rw [MonoidHom.range_eq_top.mpr hθs] at hT
  obtain ⟨g0, hg0⟩ := exists_conj_S5Syl (card_of_isSylowTwoOf_top hT)
  have hθy : θ ⟨y, hy⟩ ≠ 1 := by
    intro h1
    have : (⟨y, hy⟩ : ↥(stab β')) ∈ θ.ker := h1
    rw [hθk, Subgroup.mem_subgroupOf] at this
    exact hyQ this
  obtain ⟨τ, hτ⟩ := exists_syl_sup_zpowers_eq_top hθy
  obtain ⟨ky, hky⟩ := hθs (τ * g0⁻¹)
  have hkyH : (ky : G) ∈ H ⊔ M := stab_le β' ky.2
  set k : ↥(H ⊔ M) := ⟨ky, hkyH⟩ with hk
  have hkβ : (k : G) ∈ stab β' := ky.2
  have hδ : k • μ0 ∈ nbrs β' := by
    have h := (smul_adj k).mpr (show (graph (H ⊔ M) H M).Adj β' μ0 from hμ0')
    rwa [smul_eq_of_mem_stab hkβ] at h
  refine ⟨k • μ0, hδ, ?_⟩
  have himg := map_stab_smul θ k hkβ μ0
  rw [hg0, Subgroup.map_map] at himg
  have hθk' : θ ⟨k, hkβ⟩ = τ * g0⁻¹ := hky
  have hcomp : (MulAut.conj (θ ⟨k, hkβ⟩)).toMonoidHom.comp (MulAut.conj g0).toMonoidHom =
      (MulAut.conj τ).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
      hθk']
    group
  have hD : ((stab β' ⊓ stab (k • μ0)).subgroupOf (stab β')).map θ =
      S5Syl.map (MulAut.conj τ).toMonoidHom := by
    rw [himg, hcomp]
  intro g hg
  have hmem : θ ⟨g, hg⟩ ∈ (⊤ : Subgroup (Equiv.Perm (Fin 5))) := trivial
  rw [← hτ, ← hD, ← MonoidHom.map_zpowers θ ⟨y, hy⟩, ← Subgroup.map_sup] at hmem
  obtain ⟨q, hq, hqg⟩ := hmem
  set X' := (stab β' ⊓ stab (k • μ0)) ⊔ Subgroup.zpowers y with hX'
  have hQle : (stab β' ⊓ stab (k • μ0)).subgroupOf (stab β') ⊔
      Subgroup.zpowers (⟨y, hy⟩ : ↥(stab β')) ≤ X'.subgroupOf (stab β') := by
    refine sup_le (fun z hz => ?_) ((Subgroup.zpowers_le).mpr ?_)
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hz))
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hker : q⁻¹ * ⟨g, hg⟩ ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqg]; simp
  rw [hθk, Subgroup.mem_subgroupOf] at hker
  have hQδ : Qv β' ≤ stab (k • μ0) := Qv_le_stab_of_mem_nbrs C.hA hδ
  have hker' : q⁻¹ * ⟨g, hg⟩ ∈ X'.subgroupOf (stab β') := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_left ⟨(CFSG.Quasithin.F53B3.N37.Qv_le_stab_self β') hker, hQδ hker⟩
  have hgX : (⟨g, hg⟩ : ↥(stab β')) ∈ X'.subgroupOf (stab β') := by
    have := mul_mem (hQle hq) hker'
    simpa using this
  exact Subgroup.mem_subgroupOf.mp hgX

theorem false_of_comm_Wnn_le (hI : ⁅Wnn β, Vn α'⁆ ≤ Vn β) : False := by
  obtain ⟨y, hyV, hyQ⟩ := Set.not_subset.mp C.not_Vn_alpha'_le_Qv_beta
  have hys : y ∈ stab β := C.Vn_alpha'_le_stab hyV
  obtain ⟨δ, hδ, hX⟩ := C.exists_nbr_sup_eq_top C.vtype_beta hys hyQ
  have hvδ : vtype δ = true := vtype_true_of_mem_nbrs_false hδ C.vtype_beta
  have hβδ : β ∈ nbrs δ := mem_nbrs_comm hδ
  have key : ∀ g ∈ Vn α', ∀ w ∈ Wn δ, g * w * g⁻¹ ∈ Wn δ := by
    intro g hg w hw
    have hw' : w ∈ Wnn β := Wn_le_Wnn hδ hw
    have h1 : ⁅w, g⁆ ∈ Vn β := hI (Subgroup.commutator_mem_commutator hw' hg)
    have h2 : ⁅g, w⁆ ∈ Vn β := by
      rw [← commutatorElement_inv]; exact inv_mem h1
    have h3 : g * w * g⁻¹ = ⁅g, w⁆ * w := by simp [commutatorElement_def, mul_assoc]
    rw [h3]
    exact mul_mem (Vn_le_Wn hβδ h2) hw
  have hVnorm : Vn α' ≤ Subgroup.normalizer (Wn δ : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact key g hg h
    · intro hh
      have := key g⁻¹ (inv_mem hg) _ hh
      simpa [mul_assoc] using this
  have hstabN : stab β ≤ Subgroup.normalizer (Wn δ : Set G) := fun g hg =>
    (sup_le (inf_le_right.trans (stab_le_normalizer_Wn δ))
      ((Subgroup.zpowers_le).mpr (hVnorm hyV))) (hX hg)
  have hbot : Wn δ = ⊥ := by
    refine eq_bot_of_normalizer_transitive_vertex C.hA (α := δ) (β := β)
      (show (graph (H ⊔ M) H M).Adj δ β from hβδ) (U := Wn δ) ?_ ?_ ?_
    · have hQ : Wn δ ≤ Qv δ := C.Wn_le_Qv hvδ
      exact le_inf (hQ.trans (CFSG.Quasithin.F53B3.N37.Qv_le_stab_self δ))
        (hQ.trans (Qv_le_stab_of_mem_nbrs C.hA hβδ))
    · intro ε hε ε' hε'
      obtain ⟨g, hg, hgε⟩ := stab_transitive_on_nbrs hε hε'
      exact ⟨g, stab_le_normalizer_Wn δ hg, smul_eq_of_mem_stab hg, hgε⟩
    · intro ε hε ε' hε'
      obtain ⟨g, hg, hgε⟩ := stab_transitive_on_nbrs hε hε'
      exact ⟨g, hstabN hg, smul_eq_of_mem_stab hg, hgε⟩
  have hZ : Zv δ ≤ Vn β :=
    CFSG.Quasithin.F53B3.N37.Zv_le_Vn_of_adj (show (graph (H ⊔ M) H M).Adj β δ from hδ)
  exact Zv_ne_bot C.hA δ (le_bot_iff.mp (hZ.trans ((Vn_le_Wn hβδ).trans hbot.le)))

theorem comm_Wnn_Vn_le (hW : Wnn β ≤ Vn β ⊔ Qv α') :
    ⁅Wnn β, Vn α'⁆ ≤ ⁅Vn β, Vn α'⁆ ⊔ Zv α' := by
  refine (Subgroup.commutator_mono hW le_rfl).trans ?_
  refine comm_sup_le_of_normalizes (N := ⁅Vn β, Vn α'⁆ ⊔ Zv α') ?_ ?_ le_sup_left ?_
  · exact C.Vn_beta_le_stab.trans (stab_le_normalizer_Vn α')
  · exact (CFSG.Quasithin.F53B3.N37.Qv_le_stab_self α').trans (stab_le_normalizer_Vn α')
  · calc ⁅Qv α', Vn α'⁆ = ⁅Vn α', Qv α'⁆ := Subgroup.commutator_comm _ _
      _ = Zv α' := C.comm_Vn_Qv_eq C.vtype_alpha'
      _ ≤ _ := le_sup_right

theorem comm_Vn_Vn_le : ⁅Vn β, Vn α'⁆ ≤ Vn β :=
  comm_le_of_le_normalizer (C.Vn_alpha'_le_stab.trans (stab_le_normalizer_Vn β))

theorem relIndex_ne_two_of_comm_eq_bot (hK : ⁅Vn β ⊓ Qv α', Vn α'⁆ = ⊥) :
    (Qv α').relIndex (Vn β) ≠ 2 := by
  intro h2
  obtain ⟨y, hyV, hyQ⟩ := Set.not_subset.mp C.not_Vn_alpha'_le_Qv_beta
  have hys : y ∈ stab β := C.Vn_alpha'_le_stab hyV
  have h4 := C.four_le_relIndex_commSec C.vtype_beta hys hyQ
  obtain ⟨v0, hv0V, hv0Q⟩ := Set.not_subset.mp C.not_Vn_beta_le_Qv_alpha'
  have hRle := C.comm_Vn_Vn_le
  have hVab : IsElemAbelian 2 (Vn β) := isElemAbelian_Vn C.hA C.hb3 β
  have hy2 : y ^ 2 = 1 := (isElemAbelian_Vn C.hA C.hb3 α').2 y hyV
  set c : G := ⁅v0, y⁆ with hc
  have hcV : c ∈ Vn β := hRle (Subgroup.commutator_mem_commutator hv0V hyV)
  have hcomm_y : ∀ v ∈ Vn β ⊓ Qv α', ⁅v, y⁆ = 1 := fun v hv => by
    have := hK ▸ Subgroup.commutator_mem_commutator hv hyV
    simpa using this
  have hgen : ∀ v ∈ Vn β, ∀ g ∈ Subgroup.zpowers y, ⁅v, g⁆ ∈ Subgroup.zpowers c := by
    intro v hv g hg
    obtain ⟨k, hk, rfl⟩ := (mem_zpowers_iff_of_pow_eq_one hy2 (by norm_num)).mp hg
    interval_cases k
    · simp
    · simp only [pow_one]
      by_cases hvQ : v ∈ Qv α'
      · rw [hcomm_y v ⟨hv, hvQ⟩]; exact one_mem _
      · have hk' : v0 * v⁻¹ ∈ Qv α' :=
          mul_inv_mem_of_relIndex_two' h2 hv0V hv hv0Q hvQ
        have hkK : v0 * v⁻¹ ∈ Vn β ⊓ Qv α' := ⟨Subgroup.mul_mem _ hv0V (Subgroup.inv_mem _ hv), hk'⟩
        set k : G := v0 * v⁻¹ with hkdef
        have h1 := hcomm_y _ hkK
        have hky : k * y = y * k := commutatorElement_eq_one_iff_mul_comm.mp h1
        have e1 : v = k⁻¹ * v0 := by simp [hkdef, mul_assoc]
        have hkV : k ∈ Vn β := hkK.1
        have hcomm : k⁻¹ * c * k = c := by
          have := CFSG.Quasithin.F53B3.N37.elemAbelian_comm hVab (Subgroup.inv_mem _ hkV) hcV
          rw [this, mul_assoc]; simp
        have e2 : ⁅v, y⁆ = k⁻¹ * c * k := by
          have hyk : y * k * y⁻¹ = k := by rw [← hky]; simp [mul_assoc]
          calc ⁅v, y⁆ = k⁻¹ * (v0 * y * v0⁻¹ * y⁻¹) * (y * k * y⁻¹) := by
                rw [e1]; simp [commutatorElement_def, mul_assoc]
            _ = k⁻¹ * c * k := by rw [hyk, hc]; simp [commutatorElement_def]
        rw [e2, hcomm]
        exact Subgroup.mem_zpowers c
  have hle : ⁅Vn β, Subgroup.zpowers y⁆ ≤ Subgroup.zpowers c := by
    rw [Subgroup.commutator_le]; exact hgen
  have hcard : Nat.card ↥⁅Vn β, Subgroup.zpowers y⁆ ≤ 2 := by
    refine (Subgroup.card_le_of_le hle).trans ?_
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hVab.2 c hcV))
  have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (Vn β : Set G) :=
    (Subgroup.zpowers_le).mpr (stab_le_normalizer_Vn β hys)
  have hnorm : ⁅Vn β, Subgroup.zpowers y⁆ ≤ Subgroup.normalizer (F53B3.Cv β : Set G) :=
    (comm_le_of_le_normalizer hyN).trans
      (((C.Vn_le_Qv_self C.vtype_beta).trans (CFSG.Quasithin.F53B3.N37.Qv_le_stab_self β)).trans
        (CFSG.Quasithin.F53B3.N37.stab_le_normalizer_Cv β))
  have h5 := relIndex_sup_le_natCard hnorm
  have h6 : (F53B3.Cv β).relIndex (commSec (Subgroup.zpowers y) (F53B3.Cv β) (Vn β)) ≤ 2 :=
    h5.trans hcard
  omega

theorem mem_oTwoRes_sup_of_relIndex_four {δ δ' : Geo H M} (hδ : vtype δ = false)
    (hd : CosetGeom.dist δ δ' + 1 = bMin H M) (h4 : (Qv δ).relIndex (Vn δ') = 4) {y : G}
    (hy : y ∈ Vn δ') : y ∈ oTwoRes (stab δ) ⊔ Qv δ := by
  obtain ⟨hN, θ, βm, hθs, hθk, hsd⟩ := C.exists_secData hδ
  obtain ⟨-, hAK, -, hq0⟩ := hss114_d C.hA C.hb3 hd
  have hVδs : Vn δ ≤ stab δ :=
    (C.Vn_le_Qv_self hδ).trans (CFSG.Quasithin.F53B3.N37.Qv_le_stab_self δ)
  have hLX : F53B3.Cv δ ≤ Vn δ := inf_le_left
  have hstabN := CFSG.Quasithin.F53B3.N37.stab_le_normalizer_Cv (H := H) (M := M) δ
  have hXN : ⁅Vn δ, Vn δ'⁆ ≤ Subgroup.normalizer (F53B3.Cv δ : Set G) :=
    (commutator_le_of_le' hVδs hAK).trans hstabN
  have hAN : Vn δ' ≤ Subgroup.normalizer (F53B3.Cv δ : Set G) := hAK.trans hstabN
  have hquadC : ⁅commSec (Vn δ') (F53B3.Cv δ) (Vn δ), Vn δ'⁆ ≤ F53B3.Cv δ :=
    commutator_sup_le_of hXN hAN (by rw [hq0]; exact bot_le)
  have hq := (hsd.quadratic_iff hLX hAK).mp hquadC
  have hcard : Nat.card (((Vn δ').subgroupOf (stab δ)).map θ) = 4 := by
    rw [C.card_map_theta hθk hAK]; exact h4
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ ((Vn δ').subgroupOf (stab δ)).map θ, a ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : ((Vn δ').subgroupOf (stab δ)).map θ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hno
    rw [hbot] at hcard
    simp at hcard
  have hAalt := (quadratic_four_nat hcard hq haA ha1).1
  have hys : y ∈ stab δ := hAK hy
  have hθy : θ ⟨y, hys⟩ ∈ alternatingGroup (Fin 5) :=
    hAalt ⟨⟨y, hys⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  refine CFSG.Quasithin.F53.Stellmacher.mem_oTwoRes_sup_of_alt (F := stab δ) (Q := Qv δ) hθs
    (fun x => ?_) hys hθy
  rw [← Subgroup.mem_subgroupOf (H := Qv δ) (K := stab δ) (h := x), ← hθk, MonoidHom.mem_ker]

theorem claim3 : ¬ Wnn β ≤ Vn β ⊔ Qv α' := by
  intro hW
  by_cases hI : ⁅Wnn β, Vn α'⁆ ≤ Vn β
  · exact C.false_of_comm_Wnn_le hI
  have h3a := C.comm_Wnn_Vn_le hW
  have hR := C.comm_Vn_Vn_le
  have hcommle : ⁅Wnn β, Vn α'⁆ ≤ Vn β ⊔ Zv α' := h3a.trans (sup_le_sup_right hR _)
  have hZnle : ¬ Zv α' ≤ Vn β := fun hZ => hI (hcommle.trans (sup_le le_rfl hZ))
  obtain ⟨hzmem, hz1, hzonly⟩ := C.zgen_spec' C.vtype_alpha'
  have hZinf : Zv α' ⊓ Vn β = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rcases hzonly x hx1 with h | h
    · rw [h]; exact one_mem _
    · exfalso
      apply hZnle
      intro z hz
      rcases hzonly z hz with h' | h'
      · rw [h']; exact one_mem _
      · rw [h', ← h]; exact hx2
  have hK1 : ⁅Vn β ⊓ Qv α', Vn α'⁆ = ⊥ := by
    rw [eq_bot_iff]
    have a1 : ⁅Vn β ⊓ Qv α', Vn α'⁆ ≤ Zv α' := by
      calc ⁅Vn β ⊓ Qv α', Vn α'⁆ ≤ ⁅Qv α', Vn α'⁆ := Subgroup.commutator_mono inf_le_right le_rfl
        _ = ⁅Vn α', Qv α'⁆ := Subgroup.commutator_comm _ _
        _ = Zv α' := C.comm_Vn_Qv_eq C.vtype_alpha'
    have a2 : ⁅Vn β ⊓ Qv α', Vn α'⁆ ≤ Vn β :=
      (Subgroup.commutator_mono inf_le_left le_rfl).trans hR
    exact (le_inf a1 a2).trans hZinf.le
  have hne2 := C.relIndex_ne_two_of_comm_eq_bot hK1
  have hrel := C.relIndex_Qv_Vn_eq
  have h4 : (Qv β).relIndex (Vn α') = 4 := by omega
  have hd : CosetGeom.dist β α' + 1 = bMin H M := C.hc.dist_eq'
  obtain ⟨y, hyV, hyQ⟩ := Set.not_subset.mp C.not_Vn_alpha'_le_Qv_beta
  have hys : y ∈ stab β := C.Vn_alpha'_le_stab hyV
  have hyL := C.mem_oTwoRes_sup_of_relIndex_four C.vtype_beta hd h4 hyV
  have hZstab : Zv α' ≤ stab β := C.Zv_le_stab_of_dist_le C.vtype_alpha'
    (by rw [CosetGeom.dist_comm]; omega)
  have hZnorm : Zv α' ≤ Subgroup.normalizer (Vn β : Set G) :=
    hZstab.trans (stab_le_normalizer_Vn β)
  refine C.false_of_small_action C.vtype_beta hys hyQ hyL (U := Wnn β)
    (D := (Vn β ⊔ Zv α') ⊓ Wnn β) le_rfl (le_inf le_sup_left (Vn_le_Wnn_self β)) inf_le_right
    ?_ ?_
  · rw [sup_eq_left.mpr (Vn_le_Wnn_self β), Subgroup.relIndex_self, one_mul]
    have hDle : (Vn β ⊔ Zv α') ⊓ Wnn β ≤ Zv α' ⊔ Vn β := inf_le_left.trans (le_of_eq (sup_comm _ _))
    have h5 := Subgroup.relIndex_le_of_le_right hDle (relIndex_ne_zero' (Vn β) (Zv α' ⊔ Vn β))
    have h6 := relIndex_sup_le_natCard hZnorm
    have h7 : Nat.card (Zv α') = 2 := C.card_Zv_false C.vtype_alpha'
    omega
  · intro u hu
    have hc : ⁅u, y⁆ ∈ ⁅Wnn β, Vn α'⁆ := Subgroup.commutator_mem_commutator hu hyV
    refine ⟨hcommle hc, ?_⟩
    have hyN := stab_le_normalizer_Wnn β hys
    have h1 : y * u⁻¹ * y⁻¹ ∈ Wnn β := (Subgroup.mem_normalizer_iff.mp hyN u⁻¹).mp (inv_mem hu)
    have : ⁅u, y⁆ = u * (y * u⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
    show ⁅u, y⁆ ∈ Wnn β
    rw [this]
    exact mul_mem hu h1

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36

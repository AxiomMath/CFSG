module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.SevenB
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.LemmaI

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher Equiv
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def FactH7 : Prop :=
  ∀ Y : Subgroup nat.W, (∀ σ ∈ alternatingGroup (Fin 5), ∀ y ∈ Y, nat.act σ y ∈ Y) →
    Y = ⊥ ∨ Y = ⊤

@[expose] def IvBoundSpec (H M S : Subgroup G) : Prop :=
  ∀ {α β α' : Geo H M}, Ctx H M S α β α' → ∀ {ν : Geo H M}, vtype ν = true →
    Nat.card (Iv ν) ≤ 8

omit [Finite G] in
theorem le_normalizer_commutator {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  refine X1512.le_normalizer_of_forall fun g hg x hx => ?_
  have hle : (⁅A, B⁆).map (MulAut.conj g).toMonoidHom ≤ ⁅A, B⁆ := by
    rw [Subgroup.map_commutator]
    refine Subgroup.commutator_mono ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hA hg) a).mp ha
    · rintro _ ⟨a, ha, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hB hg) a).mp ha
  exact hle ⟨x, hx, rfl⟩

omit [Finite G] in
theorem conj_comm_mul {U : Subgroup G} (hU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) {g v r : G}
    (hv : v ∈ U) (hr : r ∈ U) (hgr : g * r * g⁻¹ ∈ U) :
    g * (v * r) * g⁻¹ * (v * r)⁻¹ = (g * v * g⁻¹ * v⁻¹) * (g * r * g⁻¹ * r⁻¹) := by
  have h1 : (g * r * g⁻¹) * r⁻¹ ∈ U := U.mul_mem hgr (U.inv_mem hr)
  have h2 := hU _ (U.inv_mem hv) _ h1
  calc g * (v * r) * g⁻¹ * (v * r)⁻¹ = g * v * g⁻¹ * ((g * r * g⁻¹ * r⁻¹) * v⁻¹) := by group
    _ = g * v * g⁻¹ * (v⁻¹ * (g * r * g⁻¹ * r⁻¹)) := by rw [h2]
    _ = (g * v * g⁻¹ * v⁻¹) * (g * r * g⁻¹ * r⁻¹) := by group

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem stab_le_normalizer_Qstar (δ : Geo H M) :
    stab δ ≤ Subgroup.normalizer ((⁅Qv δ, oTwoRes (stab δ)⁆ : Subgroup G) : Set G) :=
  le_normalizer_commutator (le_normalizer_pCoreOf 2 _) (le_normalizer_oTwoRes _)

theorem Qstar_le (δ : Geo H M) : ⁅Qv δ, oTwoRes (stab δ)⁆ ≤ Qv δ ⊓ oTwoRes (stab δ) :=
  commutator_le_inf_of_normalizes ((pCoreOf_le 2 _).trans (le_normalizer_oTwoRes _))
    ((oTwoRes_le _).trans (le_normalizer_pCoreOf 2 _))

theorem Iv_P_γ_eq (P : CritPath α β α') : Vn P.δ ⊓ Vn α' = Iv P.γ := by
  have hb := C.hb5
  have hγ : α' ∈ nbrs P.γ := P.γ_adj (by omega)
  have hδ : P.δ ∈ nbrs P.γ := mem_nbrs_comm (P.δ_adj (by omega))
  have hne : P.δ ≠ α' := by
    intro h
    have := P.dist_of_le (i := bMin H M - 2) (j := bMin H M) (by omega) le_rfl
    rw [P.p_b] at this
    have h' : dist P.δ α' = 0 := by rw [h, CosetGeom.dist_self]
    have : dist (P.p (bMin H M - 2)) α' = 2 := by omega
    exact absurd (h'.symm.trans this) (by decide)
  exact C.Vn_inf_Vn_eq_Iv (C.vtype_P_γ P) hδ hγ hne

theorem comm_Qstar_R_mem_Cv (h4 : Claim4Spec H M S) (hH8 : FactH8) (h6 : Claim6Spec H M S)
    (hI8 : IvBoundSpec H M S) (hH7 : FactH7) (P : CritPath α β α') (hW : ¬ Wnn β ≤ stab P.γ) :
    ∀ q ∈ ⁅Qv P.δ, oTwoRes (stab P.δ)⁆, ∀ r ∈ ⁅Vn β, Vn α'⁆,
      q * r * q⁻¹ * r⁻¹ ∈ F53B3.Cv P.δ := by
  have hb := C.hb5
  have hvδ := C.vtype_P_δ P
  have hvγ := C.vtype_P_γ P
  have hγ : P.γ ∈ nbrs P.δ := P.δ_adj (by omega)
  have hα' : α' ∈ nbrs P.γ := P.γ_adj (by omega)
  set δ := P.δ with hδdef
  set L := oTwoRes (stab δ) with hL
  set Qs := ⁅Qv δ, L⁆ with hQs
  set R := ⁅Vn β, Vn α'⁆ with hR
  have hcommL := C.comm_oTwoRes_R h4 hH8 h6 P hW
  have hQsle := C.Qstar_le δ
  have hXV : stab δ ≤ Subgroup.normalizer (Vn δ : Set G) := stab_le_normalizer_Vn _
  have hUab := C.isElemAbelian_RV P
  have hUn := C.stab_le_normalizer_RV h4 hH8 h6 P hW
  obtain ⟨hN, θ, βm, hθs, hθk, hsd⟩ := C.exists_secData hvδ
  have hCV : F53B3.Cv δ ≤ Vn δ := inf_le_left
  have hZC : Zv δ ≤ F53B3.Cv δ := C.Zv_le_Cv hvδ
  have hQs_s : ∀ q ∈ Qs, q ∈ stab δ := fun q hq => pCoreOf_le 2 _ (hQsle hq).1
  intro q₀ hq₀ r hr
  have hmemV : ∀ q ∈ Qs, q * r * q⁻¹ * r⁻¹ ∈ Vn δ := fun q hq =>
    hcommL q (hQsle hq).2 r hr
  have hmodQ : ∀ q ∈ Qv δ, ∀ c : ↥(Vn δ), ∀ h : q * (c : G) * q⁻¹ ∈ Vn δ,
      (QuotientGroup.mk (⟨q * (c : G) * q⁻¹, h⟩ : ↥(Vn δ)) :
        ↥(Vn δ) ⧸ (F53B3.Cv δ).subgroupOf (Vn δ)) = QuotientGroup.mk c := by
    intro q hq c h
    rw [X1512.mk_eq_iff hCV]
    refine hZC ?_
    rw [← C.comm_Vn_Qv_eq hvδ]
    have e : (c : G) * (q * (c : G) * q⁻¹)⁻¹ = ⁅(c : G), q⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator c.2 hq
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥Qs →* ↥(Vn δ) ⧸ (F53B3.Cv δ).subgroupOf (Vn δ),
      ∀ q : ↥Qs, φ q = QuotientGroup.mk ⟨q * r * q⁻¹ * r⁻¹, hmemV q q.2⟩ := ⟨
    { toFun := fun q => QuotientGroup.mk ⟨q * r * q⁻¹ * r⁻¹, hmemV q q.2⟩
      map_one' := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simp
      map_mul' := fun q₁ q₂ => by
        obtain ⟨a, ha⟩ := q₁
        obtain ⟨b, hb'⟩ := q₂
        have hc2 := hmemV b hb'
        have hc1 := hmemV a ha
        have hconj : a * (b * r * b⁻¹ * r⁻¹) * a⁻¹ ∈ Vn δ :=
          (Subgroup.mem_normalizer_iff.mp (hXV (hQs_s a ha)) _).mp hc2
        have e : (⟨(a * b) * r * (a * b)⁻¹ * r⁻¹, hmemV _ (Qs.mul_mem ha hb')⟩ : ↥(Vn δ)) =
            ⟨a * (b * r * b⁻¹ * r⁻¹) * a⁻¹, hconj⟩ * ⟨a * r * a⁻¹ * r⁻¹, hc1⟩ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          group
        show QuotientGroup.mk (⟨(a * b) * r * (a * b)⁻¹ * r⁻¹, _⟩ : ↥(Vn δ)) =
          QuotientGroup.mk (⟨a * r * a⁻¹ * r⁻¹, hc1⟩ : ↥(Vn δ)) *
            QuotientGroup.mk (⟨b * r * b⁻¹ * r⁻¹, hc2⟩ : ↥(Vn δ))
        rw [e, QuotientGroup.mk_mul, hmodQ a (hQsle ha).1 ⟨_, hc2⟩ hconj, ← QuotientGroup.mk_mul,
          ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        exact isElemAbelian_comm (isElemAbelian_Vn C.hA C.hb3 δ) hc2 hc1 }, fun _ => rfl⟩
  have hrα : r ∈ Vn α' := C.R_le_Vn_alpha' hr
  obtain ⟨K', hK'⟩ : ∃ K' : Subgroup ↥Qs, K' = (Qv P.γ).subgroupOf Qs := ⟨_, rfl⟩
  have hK'img : K'.map φ ≤ ((Iv P.γ).subgroupOf (Vn δ)).map
      (QuotientGroup.mk' ((F53B3.Cv δ).subgroupOf (Vn δ))) := by
    rintro _ ⟨q, hq, rfl⟩
    have hqγ : (q : G) ∈ Qv P.γ := by rw [hK'] at hq; exact Subgroup.mem_subgroupOf.mp hq
    have hqα : (q : G) ∈ stab α' ⊓ stab P.γ :=
      ⟨Qv_le_stab_of_mem_nbrs C.hA hα' hqγ, pCoreOf_le 2 _ hqγ⟩
    have hn := h6 C (mem_nbrs_comm hα') (C.Vn_beta_le_Qv_P_γ P) hqα
    have h1 : (q : G) * r * (q : G)⁻¹ ∈ ⁅Vn β, Vn α'⁆ ⊔ Zv α' :=
      (Subgroup.mem_normalizer_iff.mp hn r).mp (Subgroup.mem_sup_left hr)
    have hZα' : Zv α' ≤ Vn α' := Zv_le_Vn_self C.hA α'
    have h2 : (q : G) * r * (q : G)⁻¹ ∈ Vn α' := sup_le C.R_le_Vn_alpha' hZα' h1
    have h3 : (q : G) * r * (q : G)⁻¹ * r⁻¹ ∈ Iv P.γ := by
      rw [← C.Iv_P_γ_eq P]
      exact ⟨hmemV q q.2, (Vn α').mul_mem h2 ((Vn α').inv_mem hrα)⟩
    exact ⟨⟨_, hmemV q q.2⟩, Subgroup.mem_subgroupOf.mpr h3, (hφ q).symm⟩
  have hIV : Iv P.γ ≤ Vn δ := Iv_le_Vn (mem_nbrs_comm hγ)
  have hcardI : Nat.card (((Iv P.γ).subgroupOf (Vn δ)).map
      (QuotientGroup.mk' ((F53B3.Cv δ).subgroupOf (Vn δ)))) ≤ 4 := by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hIV]
    have h1 := Subgroup.relIndex_mul_card (H := F53B3.Cv δ) (K := Iv P.γ)
    have h2 : F53B3.Cv δ ⊓ Iv P.γ = Zv δ := by
      rw [inf_comm]; exact C.Iv_inf_Cv_eq hvγ (mem_nbrs_comm hγ)
    rw [h2, C.card_Zv_false hvδ] at h1
    have h3 := hI8 C hvγ
    omega
  have hK'idx : K'.index ≤ 2 := by
    have h1 : K'.index = (Qv P.γ).relIndex Qs := by rw [hK']; rfl
    rw [h1]
    have h2 := Subgroup.relIndex_le_of_le_right (H := Qv P.γ) (fun q hq => (hQsle hq).1)
      (relIndex_ne_zero_of_finite (Qv P.γ) (Qv δ))
    rw [C.relIndex_Qv_Qv_eq_two hvδ hγ] at h2
    exact h2
  have hcard : Nat.card φ.range ≤ 8 := by
    rw [← Subgroup.index_ker]
    have h1 : φ.ker.index ≤ (φ.ker ⊓ K').index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le inf_le_left)
    have h2 : (φ.ker ⊓ K').index = φ.ker.relIndex K' * K'.index := by
      rw [← Subgroup.relIndex_mul_index (inf_le_right : φ.ker ⊓ K' ≤ K'),
        Subgroup.inf_relIndex_right]
    have h3 : φ.ker.relIndex K' = Nat.card (K'.map φ) := Subgroup.relIndex_ker K' φ
    have h4 : Nat.card (K'.map φ) ≤ 4 := (Subgroup.card_le_of_le hK'img).trans hcardI
    rw [h2, h3] at h1
    nlinarith
  set Y : Subgroup nat.W := φ.range.comap βm with hY
  have hYmap : Y.map βm = φ.range := Subgroup.map_comap_eq_self_of_surjective hsd.surj _
  have hYcard : Nat.card Y = Nat.card φ.range := by
    rw [← hYmap, Subgroup.card_map_of_injective hsd.inj]
  have hLmap : ∀ σ ∈ alternatingGroup (Fin 5), ∃ (l : G) (hl : l ∈ stab δ), l ∈ L ∧
      θ ⟨l, hl⟩ = σ := by
    intro σ hσ
    obtain ⟨g, rfl⟩ := hθs σ
    have hg := (S34.mem_sup_iff_alt hθs hθk g.2).mpr hσ
    have hg' : (g : G) ∈ ((L ⊔ Qv δ : Subgroup G) : Set G) := hg
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L (Qv δ)
      ((oTwoRes_le _).trans (le_normalizer_pCoreOf 2 _))] at hg'
    obtain ⟨l, hl, q, hq, hlq⟩ := hg'
    have hls : l ∈ stab δ := oTwoRes_le _ hl
    have hqs : q ∈ stab δ := pCoreOf_le 2 _ hq
    refine ⟨l, hls, hl, ?_⟩
    have hq1 : θ ⟨q, hqs⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hθk, Subgroup.mem_subgroupOf]; exact hq
    have e : g = ⟨l, hls⟩ * ⟨q, hqs⟩ := Subtype.ext hlq.symm
    rw [e, map_mul, hq1, mul_one]
  have hYinv : ∀ σ ∈ alternatingGroup (Fin 5), ∀ y ∈ Y, nat.act σ y ∈ Y := by
    intro σ hσ y hy
    obtain ⟨l, hls, hlL, rfl⟩ := hLmap σ hσ
    obtain ⟨q, hq⟩ := (show βm y ∈ φ.range from hy)
    have hβy : βm y = QuotientGroup.mk (⟨q * r * q⁻¹ * r⁻¹, hmemV q q.2⟩ : ↥(Vn δ)) :=
      hq.symm.trans (hφ q)
    obtain ⟨hlx, hact⟩ := hsd.equiv ⟨l, hls⟩ y _ hβy
    show βm (nat.act (θ ⟨l, hls⟩) y) ∈ φ.range
    rw [hact]
    have hq'mem : l * (q : G) * l⁻¹ ∈ Qs :=
      (Subgroup.mem_normalizer_iff.mp (C.stab_le_normalizer_Qstar δ hls) _).mp q.2
    refine ⟨⟨_, hq'mem⟩, ?_⟩
    rw [hφ]
    refine (X1512.mk_eq_iff hCV).mpr ?_
    set q' := l * (q : G) * l⁻¹ with hq'
    set v := l * r * l⁻¹ * r⁻¹ with hv
    have hvV : v ∈ Vn δ := hcommL l hlL r hr
    have hq's : q' ∈ stab δ := hQs_s _ hq'mem
    have hUc : ∀ x ∈ ⁅Vn β, Vn α'⁆ ⊔ Vn δ, ∀ y ∈ ⁅Vn β, Vn α'⁆ ⊔ Vn δ, x * y = y * x :=
      fun x hx y hy => isElemAbelian_comm hUab hx hy
    have hq'r : q' * r * q'⁻¹ ∈ ⁅Vn β, Vn α'⁆ ⊔ Vn δ :=
      (Subgroup.mem_normalizer_iff.mp (hUn hq's) r).mp (Subgroup.mem_sup_left hr)
    have hkey := conj_comm_mul hUc (Subgroup.mem_sup_right hvV) (Subgroup.mem_sup_left hr) hq'r
    have hvr : v * r = l * r * l⁻¹ := by rw [hv]; group
    have e1 : l * ((q : G) * r * (q : G)⁻¹ * r⁻¹) * l⁻¹ =
        q' * (v * r) * q'⁻¹ * (v * r)⁻¹ := by rw [hvr, hq']; group
    rw [show ((⟨l * (q * r * q⁻¹ * r⁻¹) * l⁻¹, hlx⟩ : ↥(Vn δ)) : G) =
        l * ((q : G) * r * (q : G)⁻¹ * r⁻¹) * l⁻¹ from rfl, e1, hkey]
    have hz : q' * v * q'⁻¹ * v⁻¹ ∈ Zv δ := by
      rw [← C.comm_Vn_Qv_eq hvδ, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (hQsle hq'mem).1 hvV
    have e3 : ((⟨((⟨l * (q : G) * l⁻¹, hq'mem⟩ : ↥Qs) : G) * r *
        ((⟨l * (q : G) * l⁻¹, hq'mem⟩ : ↥Qs)⁻¹ : ↥Qs) * r⁻¹, hmemV _ hq'mem⟩ : ↥(Vn δ)) : G) =
        q' * r * q'⁻¹ * r⁻¹ := rfl
    rw [e3, mul_inv_cancel_right]
    exact hZC hz
  rcases hH7 Y hYinv with hbot | htop
  · have hrange : φ.range = ⊥ := by rw [← hYmap, hbot, Subgroup.map_bot]
    have h1 : φ ⟨q₀, hq₀⟩ = 1 := by
      have : φ ⟨q₀, hq₀⟩ ∈ φ.range := ⟨_, rfl⟩
      rw [hrange, Subgroup.mem_bot] at this
      exact this
    rw [hφ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  · exfalso
    rw [htop, Subgroup.card_top, card_nat] at hYcard
    omega

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36

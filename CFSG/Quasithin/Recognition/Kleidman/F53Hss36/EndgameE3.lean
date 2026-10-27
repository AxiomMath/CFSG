module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.EndgameKey

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher Equiv
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] noncomputable def mirrorPath {α β α' : Geo H M} (P : CritPath α β α') {μ : Geo H M}
    (hμ : μ ∈ nbrs α') (hd : dist μ β = bMin H M) (hb : 1 ≤ bMin H M) : CritPath μ α' β where
  p := fun i => if i = 0 then μ else P.p (bMin H M - (i - 1))
  p_zero := by simp
  p_one := by simp [P.p_b]
  p_b := by
    have : bMin H M ≠ 0 := by omega
    simp only [this, ite_false]
    rw [show bMin H M - (bMin H M - 1) = 1 by omega, P.p_one]
  isGeodesic := by
    have h1 := (P.isGeodesic.reverse).mono (m := bMin H M - 1) (by omega)
    have h2 := h1.cons (a := μ) (by simpa [P.p_b] using mem_nbrs_comm hμ) (by
      show dist μ (P.p (bMin H M - (bMin H M - 1))) = _
      rw [show bMin H M - (bMin H M - 1) = 1 by omega, P.p_one, hd]
      omega)
    rw [show bMin H M - 1 + 1 = bMin H M by omega] at h2
    exact h2

theorem mirrorPath_p {α β α' : Geo H M} (P : CritPath α β α') {μ : Geo H M}
    (hμ : μ ∈ nbrs α') (hd : dist μ β = bMin H M) (hb : 1 ≤ bMin H M) {i : ℕ} (hi : 1 ≤ i) :
    (mirrorPath P hμ hd hb).p i = P.p (bMin H M + 1 - i) := by
  show (if i = 0 then μ else P.p (bMin H M - (i - 1))) = _
  rw [if_neg (by omega)]
  congr 1
  omega

theorem exists_kleinAt_move : ∀ q q' : Fin 5, q ≠ q' →
    ∃ y : Perm (Fin 5), Perm.sign y = 1 ∧ y * y = 1 ∧ y q' = q' ∧ y q ≠ q := by
  decide +kernel

theorem exists_kleinAt_ne_one : ∀ q : Fin 5,
    ∃ y : Perm (Fin 5), Perm.sign y = 1 ∧ y * y = 1 ∧ y q = q ∧ y ≠ 1 := by
  decide +kernel

theorem card_fixW_kleinAt_le {P : Subgroup (Perm (Fin 5))} (hH8 : FactH8) (hP : Nat.card P = 8)
    {q : Fin 5} (hq : ∀ σ ∈ P, σ q = q) :
    Nat.card (fixW nat (P ⊓ alternatingGroup (Fin 5))) ≤ 4 := by
  obtain ⟨t, hs, hsq, htq, ht1⟩ := exists_kleinAt_ne_one q
  have htP : t ∈ P ⊓ alternatingGroup (Fin 5) := (hH8 P hP q hq t).mpr ⟨hs, hsq, htq⟩
  have hle : fixW nat (P ⊓ alternatingGroup (Fin 5)) ≤ fixW nat (Subgroup.zpowers t) :=
    fun w hw => (mem_fixW_zpowers nat).mpr (hw t htP)
  have hidx : idx nat t = 4 := by
    rw [idx_nat]
    have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact hsq
    simp [ht1, ht2]
  have h2 := Subgroup.index_mul_card (fixW nat (Subgroup.zpowers t))
  have hidx' : (fixW nat (Subgroup.zpowers t)).index = 4 := hidx
  rw [hidx', card_nat] at h2
  have h3 := Subgroup.card_le_of_le hle
  omega

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem Cv_eq_Zv_of {δ : Geo H M} (hδ : vtype δ = false) (hkey : F53B3.Cv α' = Zv α') :
    F53B3.Cv δ = Zv δ := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (δ := α') (δ' := δ) (by rw [hδ, C.vtype_alpha'])
  rw [F53B3.Cv_smul, Zv_smul, hkey]

theorem false_of_five (h4 : Claim4Spec H M S) (h5 : Claim5Spec H M S) (h6 : Claim6Spec H M S)
    (hI8 : IvBoundSpec H M S) (hH8 : FactH8) (hH11 : FactH11) (hH12 : FactH12)
    (hb : bMin H M = 5) (P : CritPath α β α') (h7 : Wnn β ≤ stab P.γ)
    {μ : Geo H M} (C' : Ctx H M S μ α' β) (P' : CritPath μ α' β) (h7' : Wnn α' ≤ stab P'.γ)
    (hP'γ : P'.γ = P.p 2) (hP'δ : P'.δ = P.p 3) : False := by
  have hpγ : P.γ = P.p 4 := by show P.p (bMin H M - 1) = P.p 4; rw [hb]
  have hpδ : P.δ = P.p 3 := by show P.p (bMin H M - 2) = P.p 3; rw [hb]
  have hvγ := C.vtype_P_δ P
  rw [hpδ] at hvγ
  have hv2 : vtype (P.p 2) = true := by rw [← hP'γ]; exact C'.vtype_P_γ P'
  have hv4 : vtype (P.p 4) = true := by rw [← hpγ]; exact C.vtype_P_γ P
  have h32 : P.p 3 ∈ nbrs (P.p 2) := P.isGeodesic.mem_nbrs_succ (i := 2) (by omega)
  have h34 : P.p 3 ∈ nbrs (P.p 4) := by
    have := P.isGeodesic.mem_nbrs_succ (i := 3) (by omega)
    exact mem_nbrs_comm this
  have h12 : P.p 1 ∈ nbrs (P.p 2) := by
    have := P.isGeodesic.mem_nbrs_succ (i := 1) (by omega)
    exact mem_nbrs_comm this
  have h54 : P.p 5 ∈ nbrs (P.p 4) := P.isGeodesic.mem_nbrs_succ (i := 4) (by omega)
  rw [P.p_one] at h12
  have hα'5 : P.p 5 = α' := by rw [← hb]; exact P.p_b
  rw [hα'5] at h54
  obtain ⟨hI4, hR4, h84⟩ := C.lemmaK h4 h5 h6 hI8 P h7
  obtain ⟨hI2, -, h82⟩ := C'.lemmaK h4 h5 h6 hI8 P' h7'
  rw [hpγ] at hI4 h84
  rw [hP'γ] at hI2 h82
  rw [Subgroup.commutator_comm] at hI2
  have hkey := C.Cv_eq_Zv_of hvγ (C.key h4 h5 h6 hI8 P h7)
  set γ := P.p 3 with hγdef
  set R := ⁅Vn β, Vn α'⁆ with hR
  have hRI4 : R ≤ Iv (P.p 4) := hI4 ▸ le_sup_left
  have hRI2 : R ≤ Iv (P.p 2) := hI2 ▸ le_sup_left
  obtain ⟨r, hr, hrC⟩ : ∃ r ∈ R, r ∉ F53B3.Cv γ := by
    by_contra hall
    push Not at hall
    have hRZ : R ≤ Zv γ := by
      rw [← C.Iv_inf_Cv_eq hv4 h34]
      exact le_inf hRI4 hall
    have h1 := Subgroup.card_le_of_le hRZ
    rw [C.card_Zv_false hvγ, hR4] at h1
    omega
  obtain ⟨hN, θ, βm, hθs, hθk, hsd⟩ := C.exists_secData hvγ
  have hCV : F53B3.Cv γ ≤ Vn γ := inf_le_left
  have hD2 := C.card_map_edge hvγ (mem_nbrs_comm h32) hθk
  have hD4 := C.card_map_edge hvγ (mem_nbrs_comm h34) hθk
  obtain ⟨q₂, hq₂, -⟩ := exists_fix_trans_of_card_eight _ hD2
  obtain ⟨q₄, hq₄, -⟩ := exists_fix_trans_of_card_eight _ hD4
  have himg : ∀ ν : Geo H M, γ ∈ nbrs ν → vtype ν = true → Nat.card (Iv ν) = 8 →
      ∀ q : Fin 5, (∀ σ ∈ ((stab γ ⊓ stab ν).subgroupOf (stab γ)).map θ, σ q = q) →
      ((((Iv ν).subgroupOf (Vn γ)).map
        (QuotientGroup.mk' ((F53B3.Cv γ).subgroupOf (Vn γ)))).comap βm =
          fixW nat (((stab γ ⊓ stab ν).subgroupOf (stab γ)).map θ ⊓ alternatingGroup (Fin 5))) := by
    intro ν hγν hvν h8 q hq
    have hIV : Iv ν ≤ Vn γ := Iv_le_Vn hγν
    set Ibar := ((Iv ν).subgroupOf (Vn γ)).map (QuotientGroup.mk' ((F53B3.Cv γ).subgroupOf (Vn γ)))
    set Y := Ibar.comap βm
    have hDν := C.card_map_edge hvγ (mem_nbrs_comm hγν) hθk
    have hYcard : Nat.card Y = 4 := by
      have hYmap : Y.map βm = Ibar := Subgroup.map_comap_eq_self_of_surjective hsd.surj _
      have h1 : Nat.card Y = Nat.card Ibar := by
        rw [← hYmap, Subgroup.card_map_of_injective hsd.inj]
      rw [h1, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hIV]
      have h2 := Subgroup.relIndex_mul_card (H := F53B3.Cv γ) (K := Iv ν)
      have h3 : F53B3.Cv γ ⊓ Iv ν = Zv γ := by rw [inf_comm]; exact C.Iv_inf_Cv_eq hvν hγν
      rw [h3, C.card_Zv_false hvγ, h8] at h2
      omega
    have hYinv : ∀ σ ∈ ((stab γ ⊓ stab ν).subgroupOf (stab γ)).map θ, ∀ y ∈ Y,
        nat.act σ y ∈ Y := by
      rintro _ ⟨g, hg, rfl⟩ y hy
      obtain ⟨x, hx, hxy⟩ := (show βm y ∈ Ibar from hy)
      have hxI : (x : G) ∈ Iv ν := Subgroup.mem_subgroupOf.mp hx
      obtain ⟨hgx, hact⟩ := hsd.equiv g y x hxy.symm
      show βm (nat.act (θ g) y) ∈ Ibar
      rw [hact]
      have hgν : (g : G) ∈ stab ν := (Subgroup.mem_subgroupOf.mp hg).2
      refine ⟨⟨_, hgx⟩, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Iv ν hgν) _).mp hxI
    have hYle := hH12 hDν hYinv (by omega)
    exact Subgroup.eq_of_le_of_card_ge hYle (by
      rw [hYcard]; exact card_fixW_kleinAt_le hH8 hDν hq)
  have hY2 := himg (P.p 2) h32 hv2 h82 q₂ hq₂
  have hY4 := himg (P.p 4) h34 hv4 h84 q₄ hq₄
  have hrV : r ∈ Vn γ := Iv_le_Vn h34 (hRI4 hr)
  obtain ⟨u, hu⟩ := hsd.surj (QuotientGroup.mk (⟨r, hrV⟩ : ↥(Vn γ)))
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [map_one] at hu
    exact hrC (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hu.symm))
  have huY : ∀ ν : Geo H M, R ≤ Iv ν → u ∈ (((Iv ν).subgroupOf (Vn γ)).map
      (QuotientGroup.mk' ((F53B3.Cv γ).subgroupOf (Vn γ)))).comap βm := by
    intro ν hRν
    rw [Subgroup.mem_comap, hu]
    exact ⟨⟨r, hrV⟩, Subgroup.mem_subgroupOf.mpr (hRν hr), rfl⟩
  have hu2 := huY _ hRI2
  have hu4 := huY _ hRI4
  rw [hY2] at hu2
  rw [hY4] at hu4
  set c : Fin 4 → ZMod 2 := Multiplicative.toAdd u with hc
  have hc0 : c ≠ 0 := by
    intro h
    apply hu1
    have : u = Multiplicative.ofAdd c := rfl
    rw [this, h]; rfl
  have hcT : ∀ (q : Fin 5) (D : Subgroup (Perm (Fin 5))), Nat.card D = 8 → (∀ σ ∈ D, σ q = q) →
      u ∈ fixW nat (D ⊓ alternatingGroup (Fin 5)) →
      ∀ y : Perm (Fin 5), Perm.sign y = 1 → y * y = 1 → y q = q → CFSG.Quasithin.F53Mod.natAct y c = c := by
    intro q D hD hDq huD y hs hsq hyq
    exact congrArg Multiplicative.toAdd (huD y ((hH8 D hD q hDq y).mpr ⟨hs, hsq, hyq⟩))
  have hq : q₂ = q₄ := by
    by_contra hne
    obtain ⟨y, hs, hsq, hy4, hy2⟩ := exists_kleinAt_move q₂ q₄ hne
    exact hy2 (hH11 hc0 (hcT q₂ _ hD2 hq₂ hu2) (hcT q₄ _ hD4 hq₄ hu4 y hs hsq hy4))
  have hfixeq : fixW nat (((stab γ ⊓ stab (P.p 2)).subgroupOf (stab γ)).map θ ⊓
      alternatingGroup (Fin 5)) = fixW nat (((stab γ ⊓ stab (P.p 4)).subgroupOf (stab γ)).map θ ⊓
      alternatingGroup (Fin 5)) := by
    have : ((stab γ ⊓ stab (P.p 2)).subgroupOf (stab γ)).map θ ⊓ alternatingGroup (Fin 5) =
        ((stab γ ⊓ stab (P.p 4)).subgroupOf (stab γ)).map θ ⊓ alternatingGroup (Fin 5) := by
      ext y
      rw [hH8 _ hD2 q₂ hq₂ y, hH8 _ hD4 q₄ hq₄ y, hq]
    rw [this]
  have hII : Iv (P.p 2) ≤ Iv (P.p 4) := by
    intro x hx
    have hxV : x ∈ Vn γ := Iv_le_Vn h32 hx
    obtain ⟨v, hv⟩ := hsd.surj (QuotientGroup.mk (⟨x, hxV⟩ : ↥(Vn γ)))
    have hv2 : v ∈ (((Iv (P.p 2)).subgroupOf (Vn γ)).map
        (QuotientGroup.mk' ((F53B3.Cv γ).subgroupOf (Vn γ)))).comap βm := by
      rw [Subgroup.mem_comap, hv]
      exact ⟨⟨x, hxV⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hY2, hfixeq, ← hY4] at hv2
    obtain ⟨x', hx', hx'v⟩ := Subgroup.mem_comap.mp hv2
    rw [hv] at hx'v
    have h1 := (X1512.mk_eq_iff hCV).mp hx'v
    rw [hkey] at h1
    have hZI : Zv γ ≤ Iv (P.p 4) :=
      (C.Zv_le_Zv_of_mem_nbrs hv4 h34).trans
        (le_iInf₂ fun _ hε => Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm hε))
    have hx'I : (x' : G) ∈ Iv (P.p 4) := Subgroup.mem_subgroupOf.mp hx'
    have e : x = (x * (x' : G)⁻¹) * x' := by group
    rw [e]
    exact (Iv (P.p 4)).mul_mem (hZI h1) hx'I
  apply (h5 C).2.2
  have hZβ2 : Zv β ≤ Iv (P.p 2) :=
    (C.Zv_le_Zv_of_mem_nbrs hv2 h12).trans
      (le_iInf₂ fun _ hε => Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm hε))
  exact (hZβ2.trans hII).trans (Iv_le_Vn h54)

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36

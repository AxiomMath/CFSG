module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.EndgameK
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.KeySplit
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.LemmaJ
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.KleinA5

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher Equiv
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem natAct_fix_three : ∀ σ : Perm (Fin 5), σ ^ 3 = 1 → σ ≠ 1 →
    ∀ c : Fin 4 → ZMod 2, CFSG.Quasithin.F53Mod.natAct σ c = c → c = 0 := by
  decide +kernel

theorem oTwoRes_le_centralizer_of_comm {X Z : Subgroup G} {x : G}
    (hZc : ∀ z ∈ Z, ∀ g ∈ X, z * g = g * z) (hZ2 : ∀ z ∈ Z, z * z = 1)
    (hc : ∀ l ∈ X, (∃ m : ℕ, Odd m ∧ l ^ m = 1) → l * x * l⁻¹ * x⁻¹ ∈ Z) :
    oTwoRes X ≤ Subgroup.centralizer ({x} : Set G) := by
  rw [oTwoRes, Subgroup.closure_le]
  rintro l ⟨hlX, m, hm, hlm⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨z, hz⟩ : ∃ z, z = l * x * l⁻¹ * x⁻¹ := ⟨_, rfl⟩
  have hzZ : z ∈ Z := hz ▸ hc l hlX ⟨m, hm, hlm⟩
  have hlx : l * x * l⁻¹ = z * x := by rw [hz]; group
  have hpow : ∀ k : ℕ, l ^ k * x * (l ^ k)⁻¹ = z ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc l ^ (k + 1) * x * (l ^ (k + 1))⁻¹ = l * (l ^ k * x * (l ^ k)⁻¹) * l⁻¹ := by
            rw [pow_succ']; group
        _ = l * (z ^ k * x) * l⁻¹ := by rw [ih]
        _ = z ^ k * (l * x * l⁻¹) := by
            have := hZc _ (Z.pow_mem hzZ k) l hlX
            calc l * (z ^ k * x) * l⁻¹ = (l * z ^ k) * x * l⁻¹ := by group
              _ = (z ^ k * l) * x * l⁻¹ := by rw [this]
              _ = z ^ k * (l * x * l⁻¹) := by group
        _ = z ^ (k + 1) * x := by rw [hlx, pow_succ, mul_assoc]
  have h1 := hpow m
  rw [hlm, one_mul, inv_one, mul_one] at h1
  have hzm : z ^ m = 1 := by
    have := congrArg (· * x⁻¹) h1
    simpa using this.symm
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hZ2 z hzZ
  obtain ⟨k, rfl⟩ := hm
  have hz1 : z = 1 := by
    have e : z = z ^ (2 * k + 1) * ((z ^ 2) ^ k)⁻¹ := by
      rw [← pow_mul, pow_succ]; group
    rw [e, hzm, hz2, one_pow, inv_one, one_mul]
  have : l * x * l⁻¹ = x := by rw [hlx, hz1, one_mul]
  calc l * x = l * x * l⁻¹ * l := by group
    _ = x * l := by rw [this]

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem isSec_Vn_Zv (δ : Geo H M) : IsSec (stab δ) (Zv δ) (Vn δ) where
  le := Zv_le_Vn_self C.hA δ
  normN := stab_le_normalizer_Vn δ
  normL := stab_le_normalizer_Zv C.hA δ
  comm := fun x hx y hy => by
    rw [isElemAbelian_comm (isElemAbelian_Vn C.hA C.hb3 δ) hx hy, mul_inv_cancel_right,
      mul_inv_cancel]
    exact one_mem _
  sq := fun x hx => by
    rw [isElemAbelian_pow_eq_one (isElemAbelian_Vn C.hA C.hb3 δ) hx]
    exact one_mem _

theorem Qv_le_cSecIn_Zv {δ : Geo H M} (hδ : vtype δ = false) :
    Qv δ ≤ cSecIn (stab δ) (Zv δ) (Vn δ) := by
  intro q hq
  refine Subgroup.subset_closure ⟨pCoreOf_le 2 _ hq, fun v hv => ?_⟩
  have h1 := Subgroup.commutator_mem_commutator hq hv
  rw [Subgroup.commutator_comm, C.comm_Vn_Qv_eq hδ] at h1
  simpa [commutatorElement_def] using h1

theorem mem_Cv_of_comm {δ : Geo H M} (hδ : vtype δ = false) {x : G} (hx : x ∈ Vn δ)
    (hc : ∀ l ∈ oTwoRes (stab δ), l * x * l⁻¹ * x⁻¹ ∈ Zv δ) : x ∈ F53B3.Cv δ := by
  have hZc : ∀ z ∈ Zv δ, ∀ g ∈ stab δ, z * g = g * z := fun z hz g hg =>
    ((Subgroup.mem_centralizer_iff.mp (C.Zv_le_center hδ hz).2) g hg).symm
  have hZ2 : ∀ z ∈ Zv δ, z * z = 1 := fun z hz => by
    rw [← pow_two]; exact isElemAbelian_pow_eq_one (isElemAbelian_Zv C.hA δ) hz
  have h := oTwoRes_le_centralizer_of_comm hZc hZ2
    (fun l hl _ => hc l (Subgroup.subset_closure ⟨hl, ‹∃ m : ℕ, Odd m ∧ l ^ m = 1›⟩))
  refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
  exact (Subgroup.mem_centralizer_singleton_iff.mp (h hl))

theorem Vn_le_comm_stab (hI : ∀ ν : Geo H M, vtype ν = true → Nat.card (Iv ν) = 8)
    {δ : Geo H M} (hδ : vtype δ = false) : Vn δ ≤ ⁅Vn δ, stab δ⁆ := by
  refine iSup₂_le fun ν hν => ?_
  have hvν := vtype_true_of_mem_nbrs_false hν hδ
  rw [← C.comm_Iv_Qv_eq hvν (hI ν hvν)]
  exact Subgroup.commutator_mono (Iv_le_Vn (mem_nbrs_comm hν))
    (Qv_le_stab_of_mem_nbrs C.hA (mem_nbrs_comm hν))

theorem key (h4 : Claim4Spec H M S) (h5 : Claim5Spec H M S) (h6 : Claim6Spec H M S)
    (hI8 : IvBoundSpec H M S) (P : CritPath α β α') (h7 : Wnn β ≤ stab P.γ) :
    F53B3.Cv α' = Zv α' := by
  have hb := C.hb5
  have hvα := C.vtype_alpha'
  have hvγ := C.vtype_P_γ P
  have hα' : α' ∈ nbrs P.γ := P.γ_adj (by omega)
  obtain ⟨hIeq, hR4, hI8γ⟩ := C.lemmaK h4 h5 h6 hI8 P h7
  have hIall : ∀ ν : Geo H M, vtype ν = true → Nat.card (Iv ν) = 8 := fun ν hν =>
    (C.card_Iv_eq hvγ hν).trans hI8γ
  have hVG := C.Vn_le_comm_stab hIall hvα
  obtain ⟨hN, θ, βm, hθs, hθk, hsd⟩ := C.exists_secData hvα
  have hVs : Vn β ≤ stab α' := C.Vn_beta_le_stab
  set A := alternatingGroup (Fin 5) with hA
  set T₀ := ((Vn β).subgroupOf (stab α')).map θ with hT₀
  have hT₀4 : Nat.card T₀ = 4 := by
    rw [hT₀, ← relIndex_inf_eq_card_map hθk hVs, Subgroup.inf_relIndex_left]
    exact (h5 C).2.1
  have hT₀A : T₀ ≤ A := by
    rintro _ ⟨v, hv, rfl⟩
    exact (S34.mem_sup_iff_alt hθs hθk v.2).mp (h4 C (Subgroup.mem_subgroupOf.mp hv))
  obtain ⟨g, hgA, hgT⟩ := OrdinaryProofs.alt5_klein_conj (kleinAt 4) T₀
    (kleinAt_le_alt 4) hT₀A (card_kleinAt 4) hT₀4
  set θ' : ↥(stab α') →* Perm (Fin 5) := (MulAut.conj g⁻¹).toMonoidHom.comp θ with hθ'
  have hθ'apply : ∀ h, θ' h = g⁻¹ * θ h * g := fun h => by simp [hθ']
  have hθ's : Function.Surjective θ' := by
    intro σ
    obtain ⟨h, hh⟩ := hθs (g * σ * g⁻¹)
    exact ⟨h, by rw [hθ'apply, hh]; group⟩
  have hθ'1 : ∀ h, θ' h = 1 ↔ θ h = 1 := fun h => by
    rw [hθ'apply]
    constructor
    · intro h1
      have : θ h = g * (g⁻¹ * θ h * g) * g⁻¹ := by group
      rw [this, h1]; group
    · intro h1; rw [h1]; group
  have hθ'k : θ'.ker = (Qv α').subgroupOf (stab α') := by
    ext h
    rw [MonoidHom.mem_ker, hθ'1, ← MonoidHom.mem_ker, hθk]
  have hθ'V : ((Vn β).subgroupOf (stab α')).map θ' = kleinAt 4 := by
    ext σ
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hmem : θ v ∈ T₀ := ⟨v, hv, rfl⟩
      rw [hgT] at hmem
      obtain ⟨y, hy, hyv⟩ := hmem
      rw [hθ'apply, ← hyv]
      simpa [MulAut.conj_apply, mul_assoc] using hy
    · intro hσ
      have hmem : g * σ * g⁻¹ ∈ T₀ := by
        rw [hgT]; exact ⟨σ, hσ, by simp [MulAut.conj_apply]⟩
      obtain ⟨v, hv, hvσ⟩ := hmem
      exact ⟨v, hv, by rw [hθ'apply, hvσ]; group⟩
  have hLmap : ∀ σ ∈ A, ∃ (l : G) (hl : l ∈ stab α'), l ∈ oTwoRes (stab α') ∧
      θ' ⟨l, hl⟩ = σ := by
    intro σ hσ
    obtain ⟨h, hh⟩ := hθs (g * σ * g⁻¹)
    have hσ' : θ h ∈ A := by
      rw [hh]
      exact (alternatingGroup.normal (α := Fin 5)).conj_mem σ hσ g
    have hg' := (S34.mem_sup_iff_alt hθs hθk h.2).mpr hσ'
    have hg'' : (h : G) ∈ ((oTwoRes (stab α') ⊔ Qv α' : Subgroup G) : Set G) := hg'
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (oTwoRes (stab α')) (Qv α')
      ((oTwoRes_le _).trans (le_normalizer_pCoreOf 2 _))] at hg''
    obtain ⟨l, hl, q, hq, hlq⟩ := hg''
    have hls : l ∈ stab α' := oTwoRes_le _ hl
    have hqs : q ∈ stab α' := pCoreOf_le 2 _ hq
    refine ⟨l, hls, hl, ?_⟩
    have hq1 : θ' ⟨q, hqs⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hθ'k, Subgroup.mem_subgroupOf]; exact hq
    have e : h = ⟨l, hls⟩ * ⟨q, hqs⟩ := Subtype.ext hlq.symm
    have : θ' h = σ := by rw [hθ'apply, hh]; group
    rw [e, map_mul, hq1, mul_one] at this
    exact this
  have hsec := C.isSec_Vn_Zv α'
  have hk : θ'.ker ≤ (cSecIn (stab α') (Zv α') (Vn α')).subgroupOf (stab α') := by
    rw [hθ'k]; exact Subgroup.subgroupOf_mono _ (C.Qv_le_cSecIn_Zv hvα)
  set Mo := secModule hsec θ' hθ's hk with hMo
  set pr : ↥(Vn α') →* Mo.W := hsec.proj with hpr
  have hact : ∀ (h : ↥(stab α')) (x : ↥(Vn α')),
      Mo.act (θ' h) (pr x) = pr (hsec.conjN h x) :=
    fun h x => secModule_act_proj hsec θ' hθ's hk h x
  have hpr_surj : Function.Surjective pr := hsec.proj_surjective
  have hpr_eq : ∀ x y : ↥(Vn α'), pr x = pr y ↔ (x : G)⁻¹ * (y : G) ∈ Zv α' :=
    fun x y => hsec.proj_eq_proj_iff x y
  have hpr_one : ∀ x : ↥(Vn α'), pr x = 1 ↔ (x : G) ∈ Zv α' :=
    fun x => hsec.proj_eq_one_iff x
  have hCV : F53B3.Cv α' ≤ Vn α' := inf_le_left
  have hZn : stab α' ≤ Subgroup.normalizer (Zv α' : Set G) := stab_le_normalizer_Zv C.hA α'
  have hfix_iff : ∀ (h : ↥(stab α')) (x : ↥(Vn α')),
      Mo.act (θ' h) (pr x) = pr x ↔ (h : G) * x * (h : G)⁻¹ * (x : G)⁻¹ ∈ Zv α' := by
    intro h x
    rw [hact]
    refine (hpr_eq _ _).trans ?_
    show ((h : G) * x * (h : G)⁻¹)⁻¹ * x ∈ Zv α' ↔ _
    have e : ((h : G) * x * (h : G)⁻¹)⁻¹ * x =
        (x : G)⁻¹ * ((h : G) * x * (h : G)⁻¹ * (x : G)⁻¹)⁻¹ * x := by group
    rw [e]
    constructor
    · intro hm
      have h1 := (Subgroup.mem_normalizer_iff.mp (hZn (C.Vn_le_stab_of_dist hvα
        (by rw [CosetGeom.dist_self]; omega) x.2)) _).mp hm
      have h2 : (x : G) * ((x : G)⁻¹ * ((h : G) * x * (h : G)⁻¹ * (x : G)⁻¹)⁻¹ * x) * (x : G)⁻¹ =
          ((h : G) * x * (h : G)⁻¹ * (x : G)⁻¹)⁻¹ := by group
      rw [h2] at h1
      simpa using (Zv α').inv_mem h1
    · intro hm
      have h1 := (Subgroup.mem_normalizer_iff.mp (hZn (Subgroup.inv_mem _ (C.Vn_le_stab_of_dist
        hvα (by rw [CosetGeom.dist_self]; omega) x.2))) _).mp ((Zv α').inv_mem hm)
      simpa [mul_assoc] using h1
  have hVst : Vn α' ≤ stab α' := C.Vn_le_stab_of_dist hvα (by rw [CosetGeom.dist_self]; omega)
  have hA1 : ∀ x : ↥(Vn α'), pr x ∈ fixW Mo A → (x : G) ∈ F53B3.Cv α' := by
    intro x hx
    refine C.mem_Cv_of_comm hvα x.2 fun l hl => ?_
    obtain ⟨hls, hlA⟩ := psi_mem_alt_of_mem_oTwoRes θ' hl
    exact (hfix_iff ⟨l, hls⟩ x).mp (hx _ hlA)
  have hA2 : ∀ x : ↥(Vn α'), (x : G) ∈ F53B3.Cv α' → pr x ∈ fixW Mo A := by
    intro x hx σ hσ
    obtain ⟨l, hls, hlL, rfl⟩ := hLmap σ hσ
    refine (hfix_iff ⟨l, hls⟩ x).mpr ?_
    have hc := (Subgroup.mem_centralizer_iff.mp hx.2) l hlL
    show l * x * l⁻¹ * (x : G)⁻¹ ∈ Zv α'
    rw [hc]; simp
  have hd : fixW Mo (Subgroup.zpowers d0) ≤ fixW Mo A := by
    intro w hw
    obtain ⟨x, rfl⟩ := hpr_surj w
    apply hA2
    obtain ⟨l, hls, hlL, hld⟩ := hLmap d0 d0_mem_alt
    have h1 : l * x * l⁻¹ * (x : G)⁻¹ ∈ Zv α' :=
      (hfix_iff ⟨l, hls⟩ x).mp (by rw [hld]; exact hw d0 (Subgroup.mem_zpowers d0))
    obtain ⟨u, hu⟩ := hsd.surj (QuotientGroup.mk x)
    obtain ⟨hlx, hu'⟩ := hsd.equiv ⟨l, hls⟩ u x hu
    have hfixu : nat.act (θ ⟨l, hls⟩) u = u := by
      apply hsd.inj
      rw [hu', hu]
      refine (X1512.mk_eq_iff hCV).mpr ?_
      show (x : G) * (l * x * l⁻¹)⁻¹ ∈ F53B3.Cv α'
      have e : (x : G) * (l * x * l⁻¹)⁻¹ = (l * x * l⁻¹ * (x : G)⁻¹)⁻¹ := by group
      rw [e]
      exact C.Zv_le_Cv hvα ((Zv α').inv_mem h1)
    have hθl : θ ⟨l, hls⟩ = g * d0 * g⁻¹ := by
      have := hθ'apply ⟨l, hls⟩
      rw [hld] at this
      rw [this]; group
    have h3 : (θ ⟨l, hls⟩) ^ 3 = 1 := by
      rw [hθl, conj_pow, show d0 ^ 3 = 1 from by rw [← orderOf_d0]; exact pow_orderOf_eq_one d0]
      group
    have h31 : θ ⟨l, hls⟩ ≠ 1 := by
      rw [hθl]
      intro h
      have : d0 = 1 := by
        have := congrArg (fun y => g⁻¹ * y * g) h
        simpa [mul_assoc] using this
      exact absurd this (by decide)
    have hu1 : u = 1 := by
      have := natAct_fix_three _ h3 h31 (Multiplicative.toAdd u)
        (congrArg Multiplicative.toAdd hfixu)
      exact Multiplicative.toAdd.injective this
    rw [hu1, map_one] at hu
    have := (QuotientGroup.eq_one_iff _).mp hu.symm
    exact Subgroup.mem_subgroupOf.mp this
  have hT : commW Mo (kleinAt 4) ⊤ ⊓ fixW Mo A = ⊥ := by
    have hle : commW Mo (kleinAt 4) ⊤ ≤
        (((⁅Vn β, Vn α'⁆ ⊔ Zv α' : Subgroup G)).subgroupOf (Vn α')).map pr := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨t, ht, w, -, rfl⟩
      obtain ⟨x, rfl⟩ := hpr_surj w
      rw [← hθ'V] at ht
      obtain ⟨v, hv, rfl⟩ := ht
      rw [hact]
      have hmem : (v : G) * x * (v : G)⁻¹ * (x : G)⁻¹ ∈ ⁅Vn β, Vn α'⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hv) x.2
      have hvx : (v : G) * x * (v : G)⁻¹ ∈ Vn α' := hsec.conj_mem_N v x
      refine ⟨⟨_, (Vn α').mul_mem hvx ((Vn α').inv_mem x.2)⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hmem), ?_⟩
      rw [← map_inv, ← map_mul]
      rfl
    rw [eq_bot_iff]
    rintro w ⟨hw1, hw2⟩
    obtain ⟨y, hy, rfl⟩ := hle hw1
    have hyC : (y : G) ∈ F53B3.Cv α' := hA1 y hw2
    have hyZ : (y : G) ∈ Zv α' := by
      rw [← C.Iv_inf_Cv_eq hvγ hα']
      exact ⟨hIeq ▸ Subgroup.mem_subgroupOf.mp hy, hyC⟩
    exact (Subgroup.mem_bot).mpr ((hpr_one y).mpr hyZ)
  have hG : commW Mo ⊤ ⊤ = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨x, rfl⟩ := hpr_surj w
    have hle : ⁅Vn α', stab α'⁆ ≤ ((commW Mo ⊤ ⊤).comap pr).map (Vn α').subtype := by
      rw [Subgroup.commutator_le]
      intro v hv h hh
      have hcV : ⁅v, h⁆ ∈ Vn α' := by
        have e : ⁅v, h⁆ = v * (h * v⁻¹ * h⁻¹) := by simp only [commutatorElement_def]; group
        rw [e]
        exact (Vn α').mul_mem hv (hsec.conj_mem_N ⟨h, hh⟩ ⟨v⁻¹, (Vn α').inv_mem hv⟩)
      refine ⟨⟨_, hcV⟩, ?_, rfl⟩
      show pr ⟨_, hcV⟩ ∈ commW Mo ⊤ ⊤
      have e : pr ⟨_, hcV⟩ = (Mo.act (θ' ⟨h, hh⟩) (pr ⟨v, hv⟩) * (pr ⟨v, hv⟩)⁻¹)⁻¹ := by
        rw [hact, mul_inv_rev, inv_inv, ← map_inv, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [IsSec.conjN, Subgroup.coe_mul, MonoidHom.coe_mk, OneHom.coe_mk,
          Subgroup.coe_inv, commutatorElement_def]
        group
      rw [e]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨θ' ⟨h, hh⟩, Subgroup.mem_top _,
        pr ⟨v, hv⟩, Subgroup.mem_top _, rfl⟩)
    obtain ⟨y, hy, hyx⟩ := hle (hVG x.2)
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hbot := fixW_alt_eq_bot_of_split Mo hd hT hG
  apply le_antisymm _ (C.Zv_le_Cv hvα)
  intro c hc
  have h1 := hA2 ⟨c, hc.1⟩ hc
  rw [hbot] at h1
  exact (hpr_one _).mp (Subgroup.mem_bot.mp h1)

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36

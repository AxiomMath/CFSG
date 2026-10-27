module

public import CFSG.RankThree.GF2n.Smith81.S81TModelDef
public import CFSG.RankThree.GF2n.Smith81.S81TP2
public import CFSG.RankThree.GF2n.Smith81.S81TQf
public import CFSG.RankThree.GF2n.Smith81.S81TClass4
public import CFSG.RankThree.GF2n.Smith81.S81D6Ops
public import CFSG.RankThree.GF2n.Smith81.S81D6Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


section E4

variable {K : Type} [Field K] [CharP K 2]

theorem closedL4 : ClosedL okD4 inL4 := by
  intro γ hγ hok b hb
  have hP : γ ∈ Perp := perp_iff.2 ⟨hγ, hok⟩
  have hPn : -γ ∈ Perp := neg_mem_Perp hP
  have h1 : pr b (-γ) = -1 := by rw [pr_neg, hb]
  show shift (-γ) b ∈ idx0 ↔ b ∈ idx0
  rw [mem_idx0, mem_idx0, pr_theta_shift_perp hPn h1]

theorem mem_Perp_of_okD4 {β : Rt} (hβ : IsRoot .E7 β) (h : okD4 β) : β ∈ Perp :=
  perp_iff.2 ⟨hβ, h⟩

theorem grpR4_le : GrpR K okD4 ≤ Lam K := by
  rw [GrpR, Subgroup.closure_le]
  rintro g ⟨β, hβ, hok, c, rfl⟩
  exact xu_mem_Lam (mem_Perp_of_okD4 hβ hok) c

theorem emb_supported (w : W K) :
    emb K w ∈ Finsupp.supported K K {a : Fin e7Data.d | inL4 a} := by
  rw [Finsupp.mem_supported']
  intro x hx
  exact emb_apply_of_not_mem w hx

theorem exists_emb_of_supported {v : V K}
    (hv : v ∈ Finsupp.supported K K {a : Fin e7Data.d | inL4 a}) : ∃ w : W K, emb K w = v :=
  exists_emb_eq (mem_V0.2 fun b hb => (Finsupp.mem_supported' K v).1 hv b hb)

theorem NOp_emb {S : List Rt} {t : W K ≃ₗ[K] W K} (ht : ∀ w, emb K (t w) = tOp K S (emb K w))
    (w : W K) : NOp K S (emb K w) = emb K (t w - w) := by
  rw [NOp_eq, LinearMap.sub_apply, Module.End.one_apply, map_sub, ht]

theorem Cw_iff_E4 {S : List Rt} {t : W K ≃ₗ[K] W K} (ht : ∀ w, emb K (t w) = tOp K S (emb K w))
    {c : W K} : c ∈ CwE t ↔ NOp K S (emb K c) = 0 := by
  show t c = c ↔ _
  rw [NOp_emb ht, map_eq_zero_iff _ emb_injective, sub_eq_zero]

theorem RangeL_iff_Rw {S : List Rt} {t : W K ≃ₗ[K] W K}
    (ht : ∀ w, emb K (t w) = tOp K S (emb K w)) {r : W K} :
    emb K r ∈ RangeL K S inL4 ↔ r ∈ RwE t := by
  constructor
  · rintro ⟨v, hv, hNv⟩
    obtain ⟨w, rfl⟩ := exists_emb_of_supported hv
    rw [NOp_emb ht] at hNv
    exact ⟨w, (emb_injective hNv).symm⟩
  · rintro ⟨w, rfl⟩
    exact ⟨emb K w, emb_supported w, NOp_emb ht w⟩

theorem mem_closure_of_emb {G : Set (W K)} {x : W K}
    (h : emb K x ∈ AddSubgroup.closure (emb K '' G)) : x ∈ AddSubgroup.closure G := by
  let f : W K →+ V K := (emb K).toAddMonoidHom
  have hf : (emb K) '' G = f '' G := rfl
  rw [hf, ← AddMonoidHom.map_closure] at h
  obtain ⟨y, hy, hyx⟩ := h
  have : y = x := emb_injective hyx
  subst this
  exact hy

theorem vAut0_mem_EAut0 {g : (Module.End K (W K))ˣ} (hg : g ∈ LamW K) : vAut0 K g ∈ EAut0 K :=
  Subgroup.mem_map_of_mem _ hg

set_option maxRecDepth 20000 in
theorem vAut0_xu_comm {S : List Rt} (hS : ∀ β ∈ S, IsRoot .E7 β) {t : W K ≃ₗ[K] W K}
    (ht : ∀ w, emb K (t w) = tOp K S (emb K w)) {α : Rt} (hα : α ∈ Perp)
    (hnn : ∀ β ∈ S, 0 ≤ ipR α β) (c : K) :
    vAut0 K (xuWUnit hα c) * t = t * vAut0 K (xuWUnit hα c) := by
  apply LinearEquiv.ext
  intro w
  apply emb_injective
  have h1 : (e7Data_valid.xu K α c : Module.End K (V K)) (tOp K S (emb K w)) =
      tOp K S ((e7Data_valid.xu K α c : Module.End K (V K)) (emb K w)) :=
    LinearMap.congr_fun (xu_commute_tOp hα.1 hS hnn c).eq (emb K w)
  have e1 : emb K ((vAut0 K (xuWUnit hα c)) (t w)) =
      (e7Data_valid.xu K α c : Module.End K (V K)) (tOp K S (emb K w)) := by
    rw [vAut0_apply, xuWUnit_induces hα c (t w), ht]
  have e2 : emb K (t ((vAut0 K (xuWUnit hα c)) w)) =
      tOp K S ((e7Data_valid.xu K α c : Module.End K (V K)) (emb K w)) := by
    rw [ht, vAut0_apply, xuWUnit_induces hα c w]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e1, e2, h1]

end E4

section E4inst

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem okD4_neg : ∀ γ : Rt, okD4 γ → okD4 (-γ) := by
  intro γ h
  show (-γ) node1 = 0
  have h' : γ node1 = 0 := h
  simp [h']

set_option maxRecDepth 20000 in
theorem involK12_E4 (hK4 : 4 ≤ Nat.card K) {S : List Rt} (hS : K12Cond okD4 inL4 S)
    {t : W K ≃ₗ[K] W K} (ht : ∀ w, emb K (t w) = tOp K S (emb K w)) :
    InvolK12 (EAut0 K) (p0 K) betaW t := by
  have hSo : SOrth S := sOrth_of_K12 hS
  have hSok : ∀ β ∈ S, okD4 β := hS.2.2.2.1
  obtain ⟨-, -, -, -, hStar, hStar2, hTwo, hNM, hCl, hpar⟩ := hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w
    show beta (emb K (t w)) (emb K w) = 0
    rw [ht]
    exact beta_tOp_eq_zero_of_even hSo hpar
      (fun a ha => by by_contra hn; exact ha (emb_apply_of_not_mem w hn))
  · intro c hc
    have hC := (Cw_iff_E4 ht).1 hc
    obtain ⟨r, hr, hcl⟩ := cov_of_star2 hSo (okD := okD4) (inL := inL4) hSok closedL4 hStar2
      (emb_supported c) hC
    obtain ⟨rW, hrW⟩ : ∃ rW : W K, emb K rW = r := by
      obtain ⟨v, hv, rfl⟩ := hr
      obtain ⟨w, rfl⟩ := exists_emb_of_supported hv
      exact ⟨t w - w, (NOp_emb ht w).symm⟩
    subst hrW
    refine ⟨rW, (RangeL_iff_Rw ht).1 hr, ?_⟩
    apply mem_closure_of_emb
    rw [map_sub]
    refine AddSubgroup.closure_mono ?_ hcl
    rintro v ⟨α, hα, hok, hperp, c', hc'sup, hc'N, rfl⟩
    have hP : α ∈ Perp := mem_Perp_of_okD4 hα hok
    obtain ⟨cW, rfl⟩ := exists_emb_of_supported hc'sup
    refine ⟨vAut0 K (xuWUnit hP 1) cW - cW,
      ⟨vAut0 K (xuWUnit hP 1),
        ⟨vAut0_mem_EAut0 (xuWUnit_mem_LamW hP 1),
          vAut0_xu_comm hSo.1 ht hP (fun β hβ => by rw [hperp β hβ]) 1⟩,
        cW, (Cw_iff_E4 ht).2 hc'N, rfl⟩, ?_⟩
    rw [map_sub, vAut0_apply, xuWUnit_induces hP 1 cW, e7Data_valid.xu_apply, one_smul]
    abel
  · refine ⟨{g | ∃ α : Rt, ∃ hP : α ∈ Perp, inAplus S α ∧ ∃ c₀ : K,
      g = vAut0 K (xuWUnit hP c₀)}, ?_, ?_, ?_⟩
    · rintro u ⟨α, hP, hA, c₀, rfl⟩
      exact ⟨vAut0_mem_EAut0 (xuWUnit_mem_LamW hP c₀),
        vAut0_xu_comm hSo.1 ht hP
          (fun β hβ => by rcases hA.1 β hβ with h | h <;> omega) c₀⟩
    · rintro u ⟨α, hP, hA, c₀, rfl⟩ c hc
      have hC := (Cw_iff_E4 ht).1 hc
      have h1 := heis_sub_mem hSo (okD := okD4) (inL := inL4) hSok closedL4 hP.1 (perp_iff.1 hP).2
        hA (emb_supported c) hC
      have h2 : c₀ • e7Data.rootOp K α (emb K c) ∈ RangeL K S inL4 := Submodule.smul_mem _ c₀ h1
      have e : emb K ((vAut0 K (xuWUnit hP c₀)) c - c) = c₀ • e7Data.rootOp K α (emb K c) := by
        rw [map_sub, vAut0_apply, xuWUnit_induces hP c₀ c, e7Data_valid.xu_apply]
        abel
      rw [← e] at h2
      exact (RangeL_iff_Rw ht).1 h2
    · intro c hc hfix
      have hC := (Cw_iff_E4 ht).1 hc
      have hfix' : ∀ α : Rt, IsRoot .E7 α → okD4 α → inAplus S α →
          e7Data.rootOp K α (emb K c) = 0 := by
        intro α hα hok hA
        have hP := mem_Perp_of_okD4 hα hok
        have h := hfix (vAut0 K (xuWUnit hP 1)) ⟨α, hP, hA, 1, rfl⟩
        have h' := congrArg (emb K) h
        rw [vAut0_apply, xuWUnit_induces hP 1 c, e7Data_valid.xu_apply, one_smul] at h'
        simpa using h'
      have h := fix_heis_le hSo (okD := okD4) (inL := inL4) hSok closedL4 hStar (emb_supported c)
        hC hfix'
      exact (RangeL_iff_Rw ht).1 h
  · intro S' hne hR hstab
    let f : W K →+ V K := (emb K).toAddMonoidHom
    have hne' : S'.map f ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro w hw
      have h1 : f w ∈ S'.map f := ⟨w, hw, rfl⟩
      rw [h, AddSubgroup.mem_bot] at h1
      have h2 : emb K w = 0 := h1
      have h3 : w = 0 := emb_injective (h2.trans (map_zero (emb K)).symm)
      simp [h3]
    have hsupp : ∀ s ∈ S'.map f, s ∈ Finsupp.supported K K {a : Fin e7Data.d | inL4 a} := by
      rintro _ ⟨w, -, rfl⟩
      exact emb_supported w
    have hR' : ∀ s ∈ S'.map f, s ∈ LinearMap.range (NOp K S) := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨w', hw'⟩ := hR w hw
      refine ⟨emb K w', ?_⟩
      show NOp K S (emb K w') = emb K w
      rw [NOp_emb ht, ← hw']
    have hstab' : ∀ a b : (Module.End K (V K))ˣ, a ∈ GrpR K okD4 → b ∈ GrpR K okD4 →
        Commute (a : Module.End K (V K)) (tOp K S) → Commute (b : Module.End K (V K)) (tOp K S) →
        ∀ s ∈ S'.map f,
          ((a * b * a⁻¹ * b⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) s ∈ S'.map f := by
      intro a b ha hb hac hbc s hs
      obtain ⟨w, hwS, rfl⟩ := hs
      obtain ⟨aW, haW⟩ := exists_induces (grpR4_le ha)
      obtain ⟨bW, hbW⟩ := exists_induces (grpR4_le hb)
      have haL : aW ∈ LamW K := ⟨a, grpR4_le ha, haW⟩
      have hbL : bW ∈ LamW K := ⟨b, grpR4_le hb, hbW⟩
      have hcomm : ∀ {u : (Module.End K (V K))ˣ} {uW : (Module.End K (W K))ˣ}, Induces uW u →
          Commute (u : Module.End K (V K)) (tOp K S) →
          vAut0 K uW * t = t * vAut0 K uW := by
        intro u uW huW huc
        apply LinearEquiv.ext
        intro w'
        apply emb_injective
        have h1 : (u : Module.End K (V K)) (tOp K S (emb K w')) =
            tOp K S ((u : Module.End K (V K)) (emb K w')) :=
          LinearMap.congr_fun huc.eq (emb K w')
        have e1 : emb K ((vAut0 K uW) (t w')) = (u : Module.End K (V K)) (tOp K S (emb K w')) := by
          rw [vAut0_apply, huW (t w'), ht]
        have e2 : emb K (t ((vAut0 K uW) w')) =
            tOp K S ((u : Module.End K (V K)) (emb K w')) := by
          rw [ht, vAut0_apply, huW w']
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e1, e2, h1]
      have hmem := hstab (vAut0 K aW) ⟨vAut0_mem_EAut0 haL, hcomm haW hac⟩ (vAut0 K bW)
        ⟨vAut0_mem_EAut0 hbL, hcomm hbW hbc⟩ w hwS
      have hind : Induces (aW * bW * aW⁻¹ * bW⁻¹) (a * b * a⁻¹ * b⁻¹) :=
        ((haW.mul hbW).mul haW.inv).mul hbW.inv
      have e : vAut0 K aW * vAut0 K bW * (vAut0 K aW)⁻¹ * (vAut0 K bW)⁻¹ =
          vAut0 K (aW * bW * aW⁻¹ * bW⁻¹) := by
        simp only [map_mul, map_inv]
      rw [e, vAut0_apply] at hmem
      refine ⟨_, hmem, ?_⟩
      exact hind w
    obtain ⟨p, hpS'', hp0, hpH⟩ := P2_of_clique hSo (okD := okD4) (inL := inL4) hSok okD4_neg
      closedL4 hTwo hNM hCl hK4 hne' hsupp hR' hstab'
    obtain ⟨pW, hpW, rfl⟩ := hpS''
    refine ⟨pW, hpW, fun h => hp0 (by rw [h]; exact map_zero f), ?_⟩
    have hℓ₀ : IsHWLine K (Submodule.span K {emb K (p0 K)}) := by
      have h := isHWLine_weight (K := K) (a0 : Fin e7Data.d)
      have e : emb K (p0 K) = Finsupp.single (a0 : Fin e7Data.d) 1 := emb_single a0 1
      rw [e]
      exact h
    have hle₀ : Submodule.span K {emb K (p0 K)} ≤ V0 K :=
      (Submodule.span_singleton_le_iff_mem _ _).2 (emb_mem_V0 _)
    have hleℓ : Submodule.span K {emb K pW} ≤ V0 K :=
      (Submodule.span_singleton_le_iff_mem _ _).2 (emb_mem_V0 _)
    obtain ⟨l, hl, hmap⟩ := Lam_transitive_hwLines hℓ₀ hle₀ hpH hleℓ
    have hmem : emb K pW ∈ (Submodule.span K {emb K (p0 K)}).map (l : Module.End K (V K)) := by
      rw [hmap]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨y, hy, hly⟩ := Submodule.mem_map.1 hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    obtain ⟨lW, hlW⟩ := exists_induces hl
    have hlWL : lW ∈ LamW K := ⟨l, hl, hlW⟩
    refine ⟨vAut0 K lW, vAut0_mem_EAut0 hlWL, c, ?_⟩
    apply emb_injective
    rw [map_smul, vAut0_apply, hlW (p0 K), ← map_smul (l : Module.End K (V K)), hly]

theorem involK3_E4 {S : List Rt} (hS : K3Cond okD4 inL4 S) {t : W K ≃ₗ[K] W K}
    (ht : ∀ w, emb K (t w) = tOp K S (emb K w)) : InvolK3 (EAut0 K) betaW t := by
  have hSo : SOrth S := sOrth_of_K3 hS
  have hSok : ∀ β ∈ S, okD4 β := hS.2.2.2.1
  obtain ⟨-, -, -, -, hperp, b, hbL, hb⟩ := hS
  refine ⟨?_, ?_⟩
  · intro c hc
    have hC := (Cw_iff_E4 ht).1 hc
    obtain ⟨w, hw, u, hu, hcu⟩ := ker_NOp_le_L hSo hSok closedL4 (emb_supported c) hC
    have hu0 : u = 0 := by
      ext x
      rw [Finsupp.zero_apply]
      refine (Finsupp.mem_supported' K u).1 hu x (fun hx => ?_)
      obtain ⟨β, hβ, hne⟩ := hperp x hx.1
      exact hne (hx.2 β hβ)
    rw [hu0, add_zero] at hcu
    have hmem : emb K c ∈ RangeL K S inL4 := ⟨w, hw, hcu.symm⟩
    exact (RangeL_iff_Rw ht).1 hmem
  · refine ⟨Finsupp.single ⟨b, hbL⟩ 1, ?_⟩
    show beta (emb K (t (Finsupp.single ⟨b, hbL⟩ 1))) (emb K (Finsupp.single ⟨b, hbL⟩ 1)) ≠ 0
    rw [ht, emb_single, beta_tOp_single_eq_one hSo hb]
    exact one_ne_zero

theorem involModel_E4 (hK4 : 4 ≤ Nat.card K) {S : List Rt} (hS : S ∈ e4Reps)
    {t : W K ≃ₗ[K] W K} (ht : ∀ w, emb K (t w) = tOp K S (emb K w)) :
    InvolK12 (EAut0 K) (p0 K) betaW t ∨ InvolK3 (EAut0 K) betaW t :=
  (e4Reps_cond S hS).elim (fun h => Or.inl (involK12_E4 hK4 h ht))
    (fun h => Or.inr (involK3_E4 h ht))

end E4inst

end CFSG.RankThree.GF2n.Smith81.MinuscT

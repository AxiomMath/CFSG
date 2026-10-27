module

public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneFour
public import CFSG.LocalAnalysis.StandardType.ZS.SubgroupSpaces
public import CFSG.LocalAnalysis.StandardType.ZS.Subquotient
public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem le_closure_insert {H : Subgroup (U ≃ₗ[ZMod p] U)} {b : U ≃ₗ[ZMod p] U} :
    H ≤ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))) :=
  fun _ hh => Subgroup.subset_closure (Set.mem_insert_of_mem b hh)

private theorem closure_insert_le {G H : Subgroup (U ≃ₗ[ZMod p] U)} {b : U ≃ₗ[ZMod p] U}
    (hb : b ∈ G) (hHG : H ≤ G) :
    Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))) ≤ G := by
  refine (Subgroup.closure_le G).mpr ?_
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact hb
  · exact hHG hx

private theorem closure_insert_mapsTo {W : Submodule (ZMod p) U}
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {b : U ≃ₗ[ZMod p] U} (hb2 : b * b = 1)
    (hb : ∀ w ∈ W, b w ∈ W) (hH : ∀ h ∈ H, ∀ w ∈ W, h w ∈ W) :
    ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))), ∀ w ∈ W, g w ∈ W := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have key : ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))),
      (∀ w ∈ W, g w ∈ W) ∧ (∀ w ∈ W, g⁻¹ w ∈ W) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact ⟨hb, fun w hw => by rw [hbinv]; exact hb w hw⟩
      · exact ⟨hH x hx, fun w hw => hH x⁻¹ (H.inv_mem hx) w hw⟩
    | one => exact ⟨fun w hw => by simpa using hw, fun w hw => by simpa using hw⟩
    | mul a c ha hc iha ihc =>
      refine ⟨fun w hw => iha.1 (c w) (ihc.1 w hw), fun w hw => ?_⟩
      have h1 : (a * c)⁻¹ = c⁻¹ * a⁻¹ := mul_inv_rev a c
      rw [h1]
      exact ihc.2 (a⁻¹ w) (iha.2 w hw)
    | inv a ha iha => exact ⟨iha.2, fun w hw => by simpa using iha.1 w hw⟩
  exact fun g hg => (key g hg).1

private theorem closure_insert_fixes {W : Submodule (ZMod p) U}
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {b : U ≃ₗ[ZMod p] U}
    (hb : ∀ w ∈ W, b w = w) (hH : ∀ h ∈ H, ∀ w ∈ W, h w = w) :
    ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))), ∀ w ∈ W, g w = w := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hb
    · exact hH x hx
  | one => intro w hw; rfl
  | mul a c ha hc iha ihc =>
    intro w hw
    rw [LinearEquiv.mul_apply, ihc w hw, iha w hw]
  | inv a ha iha =>
    intro w hw
    have h1 : a (a⁻¹ w) = a w := by
      rw [show a (a⁻¹ w) = w from LinearEquiv.apply_symm_apply a w, iha w hw]
    exact a.injective h1

theorem neg_mem_or_exists_closure_eq_of_tfNegOrGen (hp : p ≠ 2) {m : ℕ}
    (htab : TFNegOrGen p m) {U' : Type} [AddCommGroup U'] [Module (ZMod p) U']
    [Module.Finite (ZMod p) U'] (hU' : Module.finrank (ZMod p) U' = m)
    {J : Subgroup (U' ≃ₗ[ZMod p] U')} (hJ : ReflGen p J)
    (hirr : ∀ W : Submodule (ZMod p) U', (∀ g ∈ J, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hd : ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    (LinearEquiv.neg (ZMod p) : U' ≃ₗ[ZMod p] U') ∈ J ∨
      ∃ s : Finset (U' ≃ₗ[ZMod p] U'), s.card ≤ m ∧ (∀ x ∈ s, x ∈ J ∧ IsRefl p x) ∧
        J = Subgroup.closure (s : Set (U' ≃ₗ[ZMod p] U')) := by
  by_cases htv : ∃ t ∈ J, QTwoLin.IsTransvectionLin t
  · exact Or.inl (neg_mem_of_transvection_mem hp hJ hirr htv)
  · push Not at htv
    exact htab U' J hU' hJ htv hirr hd

private theorem commutatorSpace_closure_insert_eq [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {b : U ≃ₗ[ZMod p] U}
    (hbH : HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H) :
    HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))) =
      HardMathSupport.Kantor79.commutatorSpace H := by
  have hHF : H ≤ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))) := le_closure_insert
  have hrange : Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))) =
      Subgroup.closure (Set.range (fun i : {x // x ∈ insert b (H : Set (U ≃ₗ[ZMod p] U))} =>
        (i : U ≃ₗ[ZMod p] U))) := by rw [Subtype.range_coe]
  have hEq : HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))) =
      ⨆ i : {x // x ∈ insert b (H : Set (U ≃ₗ[ZMod p] U))},
        HardMathSupport.Kantor79.movedSpace (i : U ≃ₗ[ZMod p] U) := by
    rw [hrange]
    exact HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace
      (fun i : {x // x ∈ insert b (H : Set (U ≃ₗ[ZMod p] U))} => (i : U ≃ₗ[ZMod p] U))
  rw [hEq]
  refine le_antisymm (iSup_le fun i => ?_) ?_
  · rcases Set.mem_insert_iff.mp i.2 with h | h
    · rw [h]; exact hbH
    · exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace h
  · rw [← hEq]
    exact HardMathSupport.Kantor79.commutatorSpace_mono hHF

private theorem conj_fixes_and_sub_mem {V : Submodule (ZMod p) U}
    {b g : U ≃ₗ[ZMod p] U} (hb2 : b * b = 1) (hbV : ∀ w ∈ V, b w = w)
    (hinv : ∀ w ∈ V, b w ∈ V) (hgV : ∀ v : U, g v - v ∈ V)
    (hginvV : ∀ v : U, g⁻¹ v - v ∈ V) (hginv : ∀ w ∈ V, g⁻¹ w ∈ V) :
    (∀ w ∈ V, (b * g * b⁻¹ * g⁻¹) w = w) ∧
      (∀ u : U, (b * g * b⁻¹ * g⁻¹) u - u ∈ V) := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  constructor
  · intro w hw
    have h1 : g⁻¹ w ∈ V := hginv w hw
    have h2 : b⁻¹ (g⁻¹ w) = g⁻¹ w := by rw [hbinv]; exact hbV _ h1
    have h3 : g (g⁻¹ w) = w := LinearEquiv.apply_symm_apply g w
    simp only [LinearEquiv.mul_apply]
    rw [h2, h3]
    exact hbV w hw
  · intro u
    have h3 : b (b⁻¹ (g⁻¹ u)) = g⁻¹ u := LinearEquiv.apply_symm_apply b (g⁻¹ u)
    have h1 : (b * g * b⁻¹ * g⁻¹) u - u =
        (b (g (b⁻¹ (g⁻¹ u))) - b (b⁻¹ (g⁻¹ u))) + (g⁻¹ u - u) := by
      simp only [LinearEquiv.mul_apply]
      rw [h3]
      abel
    rw [h1]
    have h4 : b (g (b⁻¹ (g⁻¹ u))) - b (b⁻¹ (g⁻¹ u)) ∈ V := by
      rw [← map_sub]
      exact hinv _ (hgV (b⁻¹ (g⁻¹ u)))
    exact V.add_mem h4 (hginvV u)

private theorem eq_one_of_fixes_and_sub_mem [Module.Finite (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : QTwoLin.TransvectionFree A)
    {V : Submodule (ZMod p) U} {k : U ≃ₗ[ZMod p] U} (hk : k ∈ A)
    (hfix : ∀ w ∈ V, k w = w) (hquot : ∀ u : U, k u - u ∈ V)
    (hdim : Module.finrank (ZMod p) V = Module.finrank (ZMod p) U - 1)
    (hpos : 1 ≤ Module.finrank (ZMod p) U) : k = 1 := by
  set W := LinearMap.range ((k : U →ₗ[ZMod p] U) - 1) with hW
  have hle_ker : V ≤ LinearMap.ker ((k : U →ₗ[ZMod p] U) - 1) := by
    intro v hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact hfix v hv
  have hWle : W ≤ V := by
    rintro w ⟨v, rfl⟩
    rw [LinearMap.sub_apply, Module.End.one_apply]
    exact hquot v
  have hWfin : Module.finrank (ZMod p) W ≤ 1 := by
    have hfr : Module.finrank (ZMod p) W + Module.finrank (ZMod p)
        (LinearMap.ker ((k : U →ₗ[ZMod p] U) - 1)) = Module.finrank (ZMod p) U :=
      LinearMap.finrank_range_add_finrank_ker ((k : U →ₗ[ZMod p] U) - 1)
    have hle := Submodule.finrank_mono hle_ker
    omega
  by_cases hWbot : W = ⊥
  · have hzero : ((k : U →ₗ[ZMod p] U) - 1) = 0 := LinearMap.range_eq_bot.mp hWbot
    refine LinearEquiv.ext fun v => ?_
    have h := LinearMap.congr_fun hzero v
    simp only [LinearMap.sub_apply, Module.End.one_apply] at h
    exact sub_eq_zero.mp h
  · have hW1 : Module.finrank (ZMod p) W = 1 := by
      have hpos' : 0 < Module.finrank (ZMod p) W := by
        rcases Nat.eq_zero_or_pos (Module.finrank (ZMod p) W) with h0 | h0
        · exact absurd (Submodule.finrank_eq_zero.mp h0) hWbot
        · exact h0
      omega
    exact eq_one_of_forall_sub_mem_of_finrank_eq_one hA hW1 hk
      (fun w hw => hfix w (hWle hw)) (fun v => by
        change ((k : U →ₗ[ZMod p] U) - 1) v ∈ W
        exact ⟨v, rfl⟩)

private theorem conj_mul_eq_one_of_mapsTo [Module.Finite (ZMod p) U]
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1)) {b : U ≃ₗ[ZMod p] U} (hb : b ∈ G)
    (hb' : IsRefl p b)
    (hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hinv : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace H,
      b w ∈ HardMathSupport.Kantor79.commutatorSpace H) {g : U ≃ₗ[ZMod p] U} (hg : g ∈ H) :
    b * g * b⁻¹ * g⁻¹ = 1 := by
  have hbVH : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace H, b w = w :=
    fun w hw => apply_eq_self_of_not_movedSpace_le hb'.2 hinv hbH hw
  have hgVH : ∀ v : U, g v - v ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    (commutatorSpace_le_iff.mp le_rfl) g hg
  have hginvVH : ∀ v : U, g⁻¹ v - v ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    (commutatorSpace_le_iff.mp le_rfl) g⁻¹ (H.inv_mem hg)
  have hkey := conj_fixes_and_sub_mem hb'.1 hbVH hinv hgVH hginvVH
    (fun w hw => apply_mem_commutatorSpace (H.inv_mem hg) hw)
  have hkG : b * g * b⁻¹ * g⁻¹ ∈ G :=
    G.mul_mem (G.mul_mem (G.mul_mem hb (hHG hg)) (G.inv_mem hb)) (G.inv_mem (hHG hg))
  have hb_le : 1 ≤ Module.finrank (ZMod p) U := by
    rw [← hb'.2]
    exact Submodule.finrank_le _
  exact eq_one_of_fixes_and_sub_mem hG hkG hkey.1 hkey.2 hs.2.1 hb_le

private theorem mem_normalizer_of_commute {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {b : U ≃ₗ[ZMod p] U} (hcomm : ∀ g ∈ H, b * g = g * b) :
    b ∈ Subgroup.normalizer (H : Set (U ≃ₗ[ZMod p] U)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro x ⟨h, hh, rfl⟩
    show b * h * b⁻¹ ∈ H
    rw [show b * h * b⁻¹ = h from by rw [hcomm h hh]; group]
    exact hh
  · intro h hh
    refine ⟨h, hh, ?_⟩
    have hch : b * h * b⁻¹ = h := by rw [hcomm h hh]; group
    change b * h * b⁻¹ = h
    exact hch

private theorem exists_smul_of_mem_centralizer [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    {b : U ≃ₗ[ZMod p] U} (hb' : IsRefl p b)
    (hcomm : ∀ g ∈ H, b * g = g * b) :
    ∃ (f : U) (c : ZMod p), f ∈ centralizerSpace H ∧ f ≠ 0 ∧ b f = c • f ∧ c ^ 2 = 1 := by
  have hdimCH : Module.finrank (ZMod p) (centralizerSpace H) = 1 :=
    (by
      have h := hs.finrank_centralizerSpace
      have hn : 1 ≤ Module.finrank (ZMod p) U :=
        hb'.2 ▸ Submodule.finrank_le (HardMathSupport.Kantor79.movedSpace b)
      omega)
  have hmapCH : (centralizerSpace H).map (b : U →ₗ[ZMod p] U) = centralizerSpace H :=
    map_centralizerSpace_of_mem_normalizer (mem_normalizer_of_commute hcomm)
  have hCHbot : centralizerSpace H ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdimCH
    exact Nat.zero_ne_one hdimCH
  obtain ⟨f, hfCH, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCHbot
  have hCHspan : centralizerSpace H = Submodule.span (ZMod p) {f} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdimCH hfCH hf0
  have hbfCH : b f ∈ centralizerSpace H := by
    have h : b f ∈ (centralizerSpace H).map (b : U →ₗ[ZMod p] U) := Submodule.mem_map_of_mem hfCH
    rwa [hmapCH] at h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hCHspan ▸ hbfCH)
  refine ⟨f, c, hfCH, hf0, hc.symm, ?_⟩
  have h1 : b (b f) = f := by
    have := congrArg (fun e : U ≃ₗ[ZMod p] U => e f) hb'.1
    simpa [LinearEquiv.mul_apply] using this
  have h2 : c ^ 2 • f = f := by
    calc c ^ 2 • f = c • (c • f) := by rw [pow_two, smul_smul]
      _ = c • (b f) := by rw [hc]
      _ = b (c • f) := by rw [map_smul]
      _ = b (b f) := by rw [hc]
      _ = f := h1
  have h3 : (c ^ 2 - 1) • f = 0 := by rw [sub_smul, one_smul, h2, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hf0)

private theorem eq_one_of_fixes_of_compl {V W : Submodule (ZMod p) U} (h : IsCompl V W)
    {b : U ≃ₗ[ZMod p] U} (hV : ∀ v ∈ V, b v = v) (hW : ∀ w ∈ W, b w = w) :
    b = 1 := by
  have hker : V ⊔ W ≤ LinearMap.ker ((b : U →ₗ[ZMod p] U) - 1) := by
    refine sup_le ?_ ?_
    · intro v hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact hV v hv
    · intro w hw
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact hW w hw
  have hzero : ((b : U →ₗ[ZMod p] U) - 1) = 0 :=
    LinearMap.ker_eq_top.mp (top_unique (h.sup_eq_top ▸ hker))
  refine LinearEquiv.ext fun v => ?_
  have hh := LinearMap.congr_fun hzero v
  simp only [LinearMap.sub_apply, Module.End.one_apply] at hh
  exact sub_eq_zero.mp hh

private theorem movedSpace_le_centralizer_of_apply_eq_neg (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {b : U ≃ₗ[ZMod p] U} (hb' : IsRefl p b) {f : U} (hf0 : f ≠ 0)
    (hCHspan : centralizerSpace H = Submodule.span (ZMod p) {f}) (hbf : b f = -f) :
    HardMathSupport.Kantor79.movedSpace b ≤ centralizerSpace H := by
  have hne : (-(2 : ZMod p)) ≠ 0 := by
    intro h
    have h2 : (2 : ZMod p) = 0 := neg_eq_zero.mp h
    exact ZMod.prime_ne_zero p 2 hp h2
  have h2f : -f - f = (-(2 : ZMod p)) • f := by
    calc -f - f = -(f + f) := by abel
      _ = -((2 : ZMod p) • f) := by rw [two_smul]
      _ = (-(2 : ZMod p)) • f := (neg_smul (2 : ZMod p) f).symm
  have hfVb : f ∈ HardMathSupport.Kantor79.movedSpace b := by
    refine ⟨(-(2 : ZMod p))⁻¹ • f, ?_⟩
    change b ((-(2 : ZMod p))⁻¹ • f) - (-(2 : ZMod p))⁻¹ • f = f
    calc b ((-(2 : ZMod p))⁻¹ • f) - (-(2 : ZMod p))⁻¹ • f
        = (-(2 : ZMod p))⁻¹ • (b f) - (-(2 : ZMod p))⁻¹ • f := by rw [map_smul]
      _ = (-(2 : ZMod p))⁻¹ • (-f) - (-(2 : ZMod p))⁻¹ • f := by rw [hbf]
      _ = (-(2 : ZMod p))⁻¹ • (-f - f) := by rw [smul_sub]
      _ = (-(2 : ZMod p))⁻¹ • ((-(2 : ZMod p)) • f) := by rw [h2f]
      _ = ((-(2 : ZMod p))⁻¹ * (-(2 : ZMod p))) • f := by rw [smul_smul]
      _ = f := by rw [inv_mul_cancel₀ hne, one_smul]
  have hVbspan : HardMathSupport.Kantor79.movedSpace b = Submodule.span (ZMod p) {f} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hb'.2 hfVb hf0
  rw [hVbspan, hCHspan]

theorem movedSpace_le_centralizerSpace_of_mapsTo (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1)) {b : U ≃ₗ[ZMod p] U} (hb : b ∈ G)
    (hb' : IsRefl p b)
    (hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hinv : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace H,
      b w ∈ HardMathSupport.Kantor79.commutatorSpace H) :
    HardMathSupport.Kantor79.movedSpace b ≤ centralizerSpace H := by
  have hb2 : b * b = 1 := hb'.1
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hdimCH : Module.finrank (ZMod p) (centralizerSpace H) = 1 :=
    (by
      have h := hs.finrank_centralizerSpace
      have hn : 1 ≤ Module.finrank (ZMod p) U :=
        hb'.2 ▸ Submodule.finrank_le (HardMathSupport.Kantor79.movedSpace b)
      omega)
  have hk_one : ∀ g ∈ H, b * g * b⁻¹ * g⁻¹ = 1 :=
    fun g hg => conj_mul_eq_one_of_mapsTo hG hHG hs hb hb' hbH hinv hg
  have hcomm : ∀ g ∈ H, b * g = g * b := by
    intro g hg
    have h1 : b * g * b⁻¹ * g⁻¹ = 1 := hk_one g hg
    have h2 : b * g * b⁻¹ = g := by
      have := congrArg (fun x => x * g) h1
      simpa [mul_assoc] using this
    have := congrArg (fun x => x * b) h2
    simpa [mul_assoc, hbinv, hb2] using this
  obtain ⟨f, c, hfCH, hf0, hbf, hc2⟩ := exists_smul_of_mem_centralizer hs hb' hcomm
  have hCHspan : centralizerSpace H = Submodule.span (ZMod p) {f} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdimCH hfCH hf0
  rcases sq_eq_one_iff.mp hc2 with hc1 | hcm1
  · exfalso
    have hbVH : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace H, b w = w :=
      fun w hw => apply_eq_self_of_not_movedSpace_le hb'.2 hinv hbH hw
    have hCHfix : ∀ w ∈ centralizerSpace H, b w = w := by
      intro w hw
      obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (hCHspan ▸ hw)
      rw [← hd, map_smul, hbf, hc1, one_smul]
    have hb1 : b = 1 := eq_one_of_fixes_of_compl hs.1 hbVH hCHfix
    have hbne : b ≠ 1 := by
      intro hbeq
      have hmv : HardMathSupport.Kantor79.movedSpace b = ⊥ := by
        rw [hbeq, HardMathSupport.Kantor79.movedSpace, LinearMap.range_eq_bot]
        ext v
        simp
      have h2 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace b) = 1 := hb'.2
      rw [hmv, finrank_bot] at h2
      exact Nat.zero_ne_one h2
    exact hbne hb1
  · exact movedSpace_le_centralizer_of_apply_eq_neg hp hb' hf0 hCHspan
      (by rw [hbf, hcm1, neg_one_smul])

theorem splitSupport_closure_insert_of_le (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (htab : TFNegOrGen p (Module.finrank (ZMod p) U - 1)) {G H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G) (hH : ReflGen p H)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    {b : U ≃ₗ[ZMod p] U} (hb : b ∈ G) (hb' : IsRefl p b)
    (hbH : HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H) :
    SplitSupport (Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))))
      (Module.finrank (ZMod p) U - 1) := by
  set F := Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))) with hF
  have _h4 : 4 ≤ Module.finrank (ZMod p) U := h4
  have hHF : H ≤ F := le_closure_insert
  have hFG : F ≤ G := closure_insert_le hb hHG
  have hFgen : ReflGen p F := by rw [hF]; exact ReflGen.closure_insert hH hb'
  have hVF : HardMathSupport.Kantor79.commutatorSpace F =
      HardMathSupport.Kantor79.commutatorSpace H := by
    rw [hF]; exact commutatorSpace_closure_insert_eq hbH
  have hirrF : IrredOnSection F ⊥ (HardMathSupport.Kantor79.commutatorSpace F) := by
    intro X hbot hXle hXinv
    have hXle' : X ≤ HardMathSupport.Kantor79.commutatorSpace H := by rwa [hVF] at hXle
    rcases hs.2.2 X hbot hXle' (fun h hh x hx => hXinv h (hHF hh) x hx) with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hVF]; exact h)
  have hF : IsRGroup p F := ⟨hFgen, fun t ht htt => hG t (hFG ht) htt⟩
  have hdimF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) =
      Module.finrank (ZMod p) U - 1 := by rw [hVF]; exact hs.2.1
  have hdF : ∃ x ∈ F, ∃ y ∈ F, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact ⟨x, hHF hx, y, hHF hy, hxr, hyr, hxy⟩
  exact splitSupport_of_irredOnSection hp (l := Module.finrank (ZMod p) U - 1)
    (fun _ => htab) hF hirrF hdimF hdF

private theorem fixes_centralizerSpace_of_closure [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {b : U ≃ₗ[ZMod p] U}
    (hbe : ∀ v ∈ centralizerSpace H, b v = v) :
    ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))),
      ∀ w ∈ centralizerSpace H, g w = w :=
  closure_insert_fixes hbe (fun h hh _ hw => (mem_centralizerSpace.mp hw) h hh)

private theorem map_centralizerSpace_eq_self_of_closure [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {b : U ≃ₗ[ZMod p] U}
    (hbe : ∀ v ∈ centralizerSpace H, b v = v) :
    ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))),
      (centralizerSpace H).map (g : U →ₗ[ZMod p] U) = centralizerSpace H := by
  intro g hg
  have hfix := fixes_centralizerSpace_of_closure hbe g hg
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := hx
    have hgw : (g : U ≃ₗ[ZMod p] U) w = w := hfix w hw
    change (g : U ≃ₗ[ZMod p] U) w ∈ centralizerSpace H
    rw [hgw]
    exact hw
  · intro x hx
    exact ⟨x, hx, by
      have hgx : (g : U ≃ₗ[ZMod p] U) x = x := hfix x hx
      change (g : U ≃ₗ[ZMod p] U) x = x
      exact hgx⟩

private theorem finrank_subquot_top [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    {b : U ≃ₗ[ZMod p] U} (hb' : IsRefl p b) :
    Module.finrank (ZMod p) (Subquot (centralizerSpace H) ⊤) =
      Module.finrank (ZMod p) U - 1 := by
  have hCH : Module.finrank (ZMod p) (centralizerSpace H) = 1 :=
    (by
      have h := hs.finrank_centralizerSpace
      have hn : 1 ≤ Module.finrank (ZMod p) U :=
        hb'.2 ▸ Submodule.finrank_le (HardMathSupport.Kantor79.movedSpace b)
      omega)
  have hq : Module.finrank (ZMod p) (↥(⊤ : Submodule (ZMod p) U) ⧸
      (centralizerSpace H).comap ((⊤ : Submodule (ZMod p) U).subtype :
        ↥(⊤ : Submodule (ZMod p) U) →ₗ[ZMod p] U)) +
      Module.finrank (ZMod p) ((centralizerSpace H).comap
        ((⊤ : Submodule (ZMod p) U).subtype : ↥(⊤ : Submodule (ZMod p) U) →ₗ[ZMod p] U)) =
      Module.finrank (ZMod p) ↥(⊤ : Submodule (ZMod p) U) :=
    Submodule.finrank_quotient_add_finrank _
  have htop : Module.finrank (ZMod p) ↥(⊤ : Submodule (ZMod p) U) =
      Module.finrank (ZMod p) U := finrank_top (ZMod p) U
  have hD : Module.finrank (ZMod p) ((centralizerSpace H).comap
      ((⊤ : Submodule (ZMod p) U).subtype : ↥(⊤ : Submodule (ZMod p) U) →ₗ[ZMod p] U)) =
      Module.finrank (ZMod p) (centralizerSpace H) := by
    exact (LinearEquiv.ofSubmodule' (Submodule.topEquiv) (centralizerSpace H)).finrank_eq
  change Module.finrank (ZMod p) (↥(⊤ : Submodule (ZMod p) U) ⧸
      (centralizerSpace H).comap ((⊤ : Submodule (ZMod p) U).subtype :
        ↥(⊤ : Submodule (ZMod p) U) →ₗ[ZMod p] U)) = Module.finrank (ZMod p) U - 1
  omega

private theorem subquotHom_injective_of_fixes [Module.Finite (ZMod p) U]
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1)) {b : U ≃ₗ[ZMod p] U} (hb : b ∈ G)
    (hb' : IsRefl p b) (hbe : ∀ v ∈ centralizerSpace H, b v = v)
    (h₁ : ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))),
      (centralizerSpace H).map (g : U →ₗ[ZMod p] U) = centralizerSpace H)
    (h₂ : ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))),
      (⊤ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊤) :
    Function.Injective (subquotHom
      (Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))) (centralizerSpace H) ⊤ h₁ h₂) := by
  intro x y hxy
  have hz : subquotHom (Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))))
      (centralizerSpace H) ⊤ h₁ h₂ (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hdimCH : Module.finrank (ZMod p) (centralizerSpace H) = 1 :=
    (by
      have h := hs.finrank_centralizerSpace
      have hn : 1 ≤ Module.finrank (ZMod p) U :=
        hb'.2 ▸ Submodule.finrank_le (HardMathSupport.Kantor79.movedSpace b)
      omega)
  have hFG : Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))) ≤ G :=
    closure_insert_le hb hHG
  have hz1 : ((x * y⁻¹ : Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))) :
      U ≃ₗ[ZMod p] U) = 1 := by
    refine eq_one_of_forall_sub_mem_of_finrank_eq_one hG hdimCH (hFG (x * y⁻¹).2) ?_ ?_
    · exact fixes_centralizerSpace_of_closure hbe _ (x * y⁻¹).2
    · intro v
      exact (subquotEquiv_eq_one_iff (h₁ _ (x * y⁻¹).2) (h₂ _ (x * y⁻¹).2)).mp hz
        v Submodule.mem_top
  exact mul_inv_eq_one.mp (Subtype.ext hz1)

private theorem reflGen_range_subquotHom (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F : Subgroup (U ≃ₗ[ZMod p] U)} {W : Submodule (ZMod p) U} (hF : ReflGen p F)
    (h₁ : ∀ g ∈ F, W.map (g : U →ₗ[ZMod p] U) = W)
    (h₂ : ∀ g ∈ F, (⊤ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊤)
    (hfix : ∀ g ∈ F, ∀ w ∈ W, g w = w) :
    ReflGen p (subquotHom F W ⊤ h₁ h₂).range := by
  let φ := subquotHom F W ⊤ h₁ h₂
  let S : Set (Subquot W ⊤ ≃ₗ[ZMod p] Subquot W ⊤) := {t | t ∈ φ.range ∧ IsRefl p t}
  have htop : (⊤ : Subgroup F) =
      Subgroup.closure {t : F | IsRefl p (t : U ≃ₗ[ZMod p] U)} := by
    apply Subgroup.map_injective F.subtype_injective
    rw [MonoidHom.map_closure]
    have hmap : (⊤ : Subgroup F).map F.subtype = (F : Subgroup (U ≃ₗ[ZMod p] U)) := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hmap]
    have hset : F.subtype '' {t : F | IsRefl p (t : U ≃ₗ[ZMod p] U)} =
        {t : U ≃ₗ[ZMod p] U | t ∈ F ∧ IsRefl p t} := by
      ext y
      exact ⟨fun ⟨t, ht, hty⟩ => hty ▸ ⟨t.2, ht⟩, fun ⟨hy, hr⟩ => ⟨⟨y, hy⟩, hr, rfl⟩⟩
    rw [hset]
    exact hF
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr fun t ht => ht.1)
  calc φ.range = Subgroup.map φ ⊤ := MonoidHom.range_eq_map φ
    _ = Subgroup.map φ (Subgroup.closure {t : F | IsRefl p (t : U ≃ₗ[ZMod p] U)}) := by rw [htop]
    _ = Subgroup.closure (φ '' {t : F | IsRefl p (t : U ≃ₗ[ZMod p] U)}) := MonoidHom.map_closure φ _
    _ ≤ Subgroup.closure S := by
      refine Subgroup.closure_mono ?_
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨⟨t, rfl⟩, isRefl_subquotHom hp h₁ h₂ hfix (fun g hg v => Submodule.mem_top) ht⟩

private theorem eq_sup_inf_of_isCompl {V W X : Submodule (ZMod p) U} (h : IsCompl V W)
    (hWX : W ≤ X) : X = W ⊔ (X ⊓ V) := by
  refine le_antisymm ?_ (sup_le hWX inf_le_left)
  intro x hx
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩, hvw⟩ :=
    Submodule.mem_sup'.mp (h.sup_eq_top ▸ (Submodule.mem_top : x ∈ ⊤))
  have hwX : w ∈ X := hWX hw
  have hvX : v ∈ X := by
    have hsub : x - w ∈ X := X.sub_mem hx hwX
    rwa [show x - w = v by rw [← hvw]; abel] at hsub
  exact Submodule.mem_sup'.mpr ⟨⟨w, hw⟩, ⟨v, ⟨hvX, hv⟩⟩, by rw [add_comm]; exact hvw⟩

private theorem exists_invariant_subspace_of_subquot [Module.Finite (ZMod p) U]
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} (hHF : H ≤ F) {V W : Submodule (ZMod p) U}
    (hcompl : IsCompl V W)
    (h₁ : ∀ g ∈ F, W.map (g : U →ₗ[ZMod p] U) = W)
    (h₂ : ∀ g ∈ F, (⊤ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊤)
    {X : Submodule (ZMod p) (Subquot W ⊤)}
    (hXinv : ∀ g ∈ (subquotHom F W ⊤ h₁ h₂).range, ∀ x ∈ X, g x ∈ X) :
    ∃ X'' : Submodule (ZMod p) U, W ≤ X'' ∧ (∀ h ∈ H, ∀ x ∈ X'', h x ∈ X'') ∧
      X'' = W ⊔ (X'' ⊓ V) ∧
      X = (X''.comap ((⊤ : Submodule (ZMod p) U).subtype)).map
        (Submodule.mkQ (W.comap ((⊤ : Submodule (ZMod p) U).subtype))) := by
  let q : ↥(⊤ : Submodule (ZMod p) U) →ₗ[ZMod p] Subquot W ⊤ :=
    Submodule.mkQ (W.comap ((⊤ : Submodule (ZMod p) U).subtype))
  let X' : Submodule (ZMod p) ↥(⊤ : Submodule (ZMod p) U) := X.comap q
  let X'' : Submodule (ZMod p) U := X'.map ((⊤ : Submodule (ZMod p) U).subtype)
  have hWX'' : W ≤ X'' := by
    intro w hw
    refine Submodule.mem_map.mpr ⟨⟨w, Submodule.mem_top⟩, ?_, rfl⟩
    rw [Submodule.mem_comap]
    have hq0 : q ⟨w, Submodule.mem_top⟩ = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hw
    rw [hq0]; exact X.zero_mem
  have hX''inv : ∀ h ∈ H, ∀ x ∈ X'', h x ∈ X'' := by
    intro h hh x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine Submodule.mem_map.mpr ⟨⟨h y.1, Submodule.mem_top⟩, ?_, rfl⟩
    rw [Submodule.mem_comap]
    have hqy : q y ∈ X := Submodule.mem_comap.mp hy
    have hFmem : h ∈ F := hHF hh
    let hF' : F := ⟨h, hFmem⟩
    have hmem : subquotHom F W ⊤ h₁ h₂ hF' (q y) ∈ X :=
      hXinv (subquotHom F W ⊤ h₁ h₂ hF') ⟨hF', rfl⟩ (q y) hqy
    have hkey : q ⟨h y.1, Submodule.mem_top⟩ =
        subquotHom F W ⊤ h₁ h₂ hF' (q y) := by
      change Submodule.Quotient.mk (⟨h y.1, Submodule.mem_top⟩ : ↥(⊤ : Submodule (ZMod p) U)) =
        subquotEquiv W ⊤ h (h₁ h hFmem) (h₂ h hFmem) (q y)
      rw [show q y = Submodule.Quotient.mk y from rfl, subquotEquiv_mk]; rfl
    rw [hkey]; exact hmem
  have hXeq : X = (X''.comap ((⊤ : Submodule (ZMod p) U).subtype)).map q := by
    have hX' : X' = X''.comap ((⊤ : Submodule (ZMod p) U).subtype) := by
      apply Submodule.map_injective_of_injective
        (Submodule.subtype_injective (⊤ : Submodule (ZMod p) U))
      rw [show X'.map ((⊤ : Submodule (ZMod p) U).subtype) = X'' from rfl,
        Submodule.map_comap_subtype]
      simp
    have hXmap : X'.map q = X := by
      have h := Submodule.map_comap_eq q X
      rwa [Submodule.range_mkQ, top_inf_eq] at h
    rw [← hXmap, hX']
  exact ⟨X'', hWX'', hX''inv, eq_sup_inf_of_isCompl hcompl hWX'', hXeq⟩

private theorem irred_range_subquotHom [Module.Finite (ZMod p) U]
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} (hHF : H ≤ F) {V W : Submodule (ZMod p) U}
    (hcompl : IsCompl V W) (hVinv : ∀ h ∈ H, ∀ x ∈ V, h x ∈ V)
    (hirr : IrredOnSection H ⊥ V)
    (h₁ : ∀ g ∈ F, W.map (g : U →ₗ[ZMod p] U) = W)
    (h₂ : ∀ g ∈ F, (⊤ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊤) :
    ∀ X : Submodule (ZMod p) (Subquot W ⊤),
      (∀ g ∈ (subquotHom F W ⊤ h₁ h₂).range, ∀ x ∈ X, g x ∈ X) → X = ⊥ ∨ X = ⊤ := by
  intro X hXinv
  obtain ⟨X'', hWX'', hinv'', hdecomp, hXeq⟩ :=
    exists_invariant_subspace_of_subquot hHF hcompl h₁ h₂ hXinv
  have hY := hirr (X'' ⊓ V) bot_le inf_le_right
    (fun h hh x hx => ⟨hinv'' h hh x hx.1, hVinv h hh x hx.2⟩)
  rcases hY with hYbot | hYtop
  · left
    have hX''W : X'' = W := by rw [hdecomp, hYbot, sup_bot_eq]
    rw [hXeq, hX''W, Submodule.mkQ_map_self]
  · right
    have hX''top : X'' = ⊤ := by rw [hdecomp, hYtop, sup_comm, hcompl.sup_eq_top]
    rw [hXeq, hX''top, Submodule.comap_top, Submodule.map_top, Submodule.range_mkQ]

private theorem dLarge_range_subquotHom (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F : Subgroup (U ≃ₗ[ZMod p] U)} {W : Submodule (ZMod p) U}
    (h₁ : ∀ g ∈ F, W.map (g : U →ₗ[ZMod p] U) = W)
    (h₂ : ∀ g ∈ F, (⊤ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊤)
    (hfix : ∀ g ∈ F, ∀ w ∈ W, g w = w)
    (hinj : Function.Injective (subquotHom F W ⊤ h₁ h₂))
    (hd : ∃ x ∈ F, ∃ y ∈ F, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    ∃ x ∈ (subquotHom F W ⊤ h₁ h₂).range, ∃ y ∈ (subquotHom F W ⊤ h₁ h₂).range,
      IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
  let ρ := subquotHom F W ⊤ h₁ h₂
  obtain ⟨x, hxF, y, hyF, hxr, hyr, hxy⟩ := hd
  refine ⟨ρ ⟨x, hxF⟩, ⟨⟨x, hxF⟩, rfl⟩, ρ ⟨y, hyF⟩, ⟨⟨y, hyF⟩, rfl⟩, ?_, ?_, ?_⟩
  · exact isRefl_subquotHom hp h₁ h₂ hfix (fun g hg v => Submodule.mem_top) hxr
  · exact isRefl_subquotHom hp h₁ h₂ hfix (fun g hg v => Submodule.mem_top) hyr
  · rw [← map_mul, orderOf_injective ρ hinj (⟨x, hxF⟩ * ⟨y, hyF⟩)]
    simpa using hxy

private theorem neg_data [Module.Finite (ZMod p) U]
    {F : Subgroup (U ≃ₗ[ZMod p] U)} {CH : Submodule (ZMod p) U}
    {h₁ : ∀ g ∈ F, CH.map (g : U →ₗ[ZMod p] U) = CH}
    {h₂ : ∀ g ∈ F, (⊤ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊤}
    (hinj : Function.Injective (subquotHom F CH ⊤ h₁ h₂)) {z : F}
    (hz : subquotHom F CH ⊤ h₁ h₂ z =
      (LinearEquiv.neg (ZMod p) : Subquot CH ⊤ ≃ₗ[ZMod p] Subquot CH ⊤)) :
    (((z : F) : U ≃ₗ[ZMod p] U) * ((z : F) : U ≃ₗ[ZMod p] U) = 1) ∧
      ∀ v : U, ((z : F) : U ≃ₗ[ZMod p] U) v + v ∈ CH := by
  have hz2 : ((z : F) : U ≃ₗ[ZMod p] U) * ((z : F) : U ≃ₗ[ZMod p] U) = 1 := by
    have h1 : subquotHom F CH ⊤ h₁ h₂ (z * z) = subquotHom F CH ⊤ h₁ h₂ 1 := by
      rw [map_mul, hz, map_one]
      ext x
      simp [LinearEquiv.mul_apply]
    have h2 : z * z = 1 := hinj h1
    have := congrArg (fun t : F => (t : U ≃ₗ[ZMod p] U)) h2
    simpa [map_mul] using this
  refine ⟨hz2, fun v => ?_⟩
  have h := LinearEquiv.congr_fun hz
    (Submodule.Quotient.mk (⟨v, Submodule.mem_top⟩ : ↥(⊤ : Submodule (ZMod p) U)))
  change subquotEquiv CH ⊤ ((z : F) : U ≃ₗ[ZMod p] U) (h₁ z z.2) (h₂ z z.2)
      (Submodule.Quotient.mk (⟨v, Submodule.mem_top⟩ : ↥(⊤ : Submodule (ZMod p) U))) =
    (LinearEquiv.neg (ZMod p))
      (Submodule.Quotient.mk (⟨v, Submodule.mem_top⟩ : ↥(⊤ : Submodule (ZMod p) U))) at h
  rw [subquotEquiv_mk, LinearEquiv.neg_apply] at h
  have h2 := (Submodule.Quotient.eq (p := CH.comap
    ((⊤ : Submodule (ZMod p) U).subtype))).mp h
  simpa [LinearEquiv.ofSubmodules_apply, sub_neg_eq_add] using h2

private theorem isCompl_ker_add_one [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {CH : Submodule (ZMod p) U} (hCH : Module.finrank (ZMod p) CH = 1)
    {z : U ≃ₗ[ZMod p] U} (hzCH : ∀ w ∈ CH, z w = w) (hzq : ∀ v : U, z v + v ∈ CH) :
    IsCompl (LinearMap.ker ((z : U →ₗ[ZMod p] U) + 1)) CH := by
  have hdisj : Disjoint (LinearMap.ker ((z : U →ₗ[ZMod p] U) + 1)) CH := by
    rw [disjoint_iff_inf_le]
    intro x hx
    have hzx : z x = -x := by
      have h := LinearMap.mem_ker.mp hx.1
      simp only [LinearMap.add_apply, Module.End.one_apply] at h
      exact eq_neg_of_add_eq_zero_right (by rw [add_comm]; exact h)
    have hx0 : x = -x := (hzCH x hx.2).symm.trans hzx
    have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
    have hx2 : (2 : ZMod p) • x = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hx0]
      rw [add_neg_cancel]
    exact (smul_eq_zero.mp hx2).resolve_left h2
  have hdim : Module.finrank (ZMod p) U ≤
      Module.finrank (ZMod p) (LinearMap.ker ((z : U →ₗ[ZMod p] U) + 1)) +
      Module.finrank (ZMod p) CH := by
    have hle : Module.finrank (ZMod p) (LinearMap.range ((z : U →ₗ[ZMod p] U) + 1)) ≤
        Module.finrank (ZMod p) CH := by
      apply Submodule.finrank_mono
      rintro x ⟨v, rfl⟩
      rw [LinearMap.add_apply, Module.End.one_apply]
      exact hzq v
    have hfr := LinearMap.finrank_range_add_finrank_ker ((z : U →ₗ[ZMod p] U) + 1)
    omega
  exact (Submodule.isCompl_iff_disjoint _ _ hdim).mpr hdisj

private theorem mapsTo_ker_add_one_of_centralizes {z g : U ≃ₗ[ZMod p] U}
    (hcomm : z * g = g * z) :
    ∀ w ∈ LinearMap.ker ((z : U →ₗ[ZMod p] U) + 1),
      g w ∈ LinearMap.ker ((z : U →ₗ[ZMod p] U) + 1) := by
  intro w hw
  have hzw : z w = -w := by
    have h := LinearMap.mem_ker.mp hw
    simp only [LinearMap.add_apply, Module.End.one_apply] at h
    exact eq_neg_of_add_eq_zero_right (by rw [add_comm]; exact h)
  rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg]
  calc z (g w) = (z * g) w := rfl
    _ = (g * z) w := by rw [hcomm]
    _ = g (z w) := rfl
    _ = g (-w) := by rw [hzw]
    _ = -g w := map_neg g w

private theorem mul_eq_of_conj_mul_inv_mul_eq_one {G : Type*} [Group G] {z g : G}
    (hz2 : z * z = 1) (h2 : g * z * g⁻¹ * z⁻¹ = 1) : z * g = g * z := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have h4 : g * z * g⁻¹ = z := by
    have := congrArg (fun t : G => t * z) h2
    simpa [mul_assoc, hzinv, hz2] using this
  calc z * g = (g * z * g⁻¹) * g := by rw [h4]
    _ = g * z := by group

private theorem exists_isCompl_of_neg_mem_range (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1)) {b : U ≃ₗ[ZMod p] U} (hb' : IsRefl p b)
    (hfix : ∀ g ∈ F, ∀ w ∈ centralizerSpace H, g w = w)
    (h₁ : ∀ g ∈ F, (centralizerSpace H).map (g : U →ₗ[ZMod p] U) = centralizerSpace H)
    (h₂ : ∀ g ∈ F, (⊤ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊤)
    (hinj : Function.Injective (subquotHom F (centralizerSpace H) ⊤ h₁ h₂))
    (hneg : (LinearEquiv.neg (ZMod p) : Subquot (centralizerSpace H) ⊤ ≃ₗ[ZMod p]
      Subquot (centralizerSpace H) ⊤) ∈ (subquotHom F (centralizerSpace H) ⊤ h₁ h₂).range) :
    ∃ W : Submodule (ZMod p) U, IsCompl W (centralizerSpace H) ∧
      ∀ g ∈ F, ∀ w ∈ W, g w ∈ W := by
  obtain ⟨z, hz⟩ := hneg
  obtain ⟨hz2, hzq⟩ := neg_data hinj hz
  have hdimCH : Module.finrank (ZMod p) (centralizerSpace H) = 1 := by
    rw [hs.finrank_centralizerSpace, Nat.sub_sub_self
      (hb'.2 ▸ Submodule.finrank_le (HardMathSupport.Kantor79.movedSpace b))]
  have hzCH : ∀ w ∈ centralizerSpace H, ((z : F) : U ≃ₗ[ZMod p] U) w = w :=
    fun w hw => hfix z z.2 w hw
  refine ⟨LinearMap.ker ((((z : F) : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) + 1),
    isCompl_ker_add_one hp hdimCH hzCH hzq, ?_⟩
  intro g hg w hw
  let gF : F := ⟨g, hg⟩
  have hneg_comm : ∀ y : Subquot (centralizerSpace H) ⊤ ≃ₗ[ZMod p]
      Subquot (centralizerSpace H) ⊤,
      y * LinearEquiv.neg (ZMod p) = LinearEquiv.neg (ZMod p) * y := by
    intro y
    ext x
    simp [LinearEquiv.neg_apply]
  have hcomm_phi : subquotHom F (centralizerSpace H) ⊤ h₁ h₂ gF *
      subquotHom F (centralizerSpace H) ⊤ h₁ h₂ z =
      subquotHom F (centralizerSpace H) ⊤ h₁ h₂ z *
        subquotHom F (centralizerSpace H) ⊤ h₁ h₂ gF := by
    rw [hz]
    exact hneg_comm (subquotHom F (centralizerSpace H) ⊤ h₁ h₂ gF)
  have h1 : subquotHom F (centralizerSpace H) ⊤ h₁ h₂ (gF * z * gF⁻¹ * z⁻¹) =
      subquotHom F (centralizerSpace H) ⊤ h₁ h₂ 1 := by
    simp only [map_mul, map_inv, map_one]
    rw [hcomm_phi]
    group
  have h2 : gF * z * gF⁻¹ * z⁻¹ = 1 := hinj h1
  have hz2' : z * z = 1 := Subtype.ext hz2
  have h3 : ((z : F) : U ≃ₗ[ZMod p] U) * ((gF : F) : U ≃ₗ[ZMod p] U) =
      ((gF : F) : U ≃ₗ[ZMod p] U) * ((z : F) : U ≃ₗ[ZMod p] U) := by
    have h4 := mul_eq_of_conj_mul_inv_mul_eq_one hz2' h2
    have := congrArg (fun t : F => (t : U ≃ₗ[ZMod p] U)) h4
    simpa [Subgroup.coe_mul] using this
  exact mapsTo_ker_add_one_of_centralizes h3 w hw

private theorem finrank_sup_commutatorSpace_movedSpace [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    {b : U ≃ₗ[ZMod p] U} (hb' : IsRefl p b)
    (hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace H) :
    Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.commutatorSpace H ⊔
      HardMathSupport.Kantor79.movedSpace b) = Module.finrank (ZMod p) U := by
  have hinf : HardMathSupport.Kantor79.commutatorSpace H ⊓
      HardMathSupport.Kantor79.movedSpace b = ⊥ := by
    refine (Submodule.eq_bot_iff (HardMathSupport.Kantor79.commutatorSpace H ⊓
      HardMathSupport.Kantor79.movedSpace b)).mpr fun v hv => ?_
    by_contra hv0
    exact hbH (by
      have hspan : HardMathSupport.Kantor79.movedSpace b = Submodule.span (ZMod p) {v} :=
        eq_span_singleton_of_mem_of_finrank_eq_one hb'.2 hv.2 hv0
      rw [hspan]
      exact Submodule.span_le.mpr (by rintro w rfl; exact hv.1))
  have hdim_b : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace b) = 1 := hb'.2
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (HardMathSupport.Kantor79.commutatorSpace H) (HardMathSupport.Kantor79.movedSpace b)
  rw [hinf, finrank_bot, add_zero, hs.2.1, hdim_b] at hsum
  have hb_le : 1 ≤ Module.finrank (ZMod p) U := by
    rw [← hdim_b]
    exact Submodule.finrank_le _
  omega

private theorem false_of_gen_range_subquot (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} (hHF : H ≤ F)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    {b : U ≃ₗ[ZMod p] U} (hbF : b ∈ F) (hb' : IsRefl p b)
    (hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace H)
    {CH : Submodule (ZMod p) U}
    {h₁ : ∀ g ∈ F, CH.map (g : U →ₗ[ZMod p] U) = CH}
    {h₂ : ∀ g ∈ F, (⊤ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊤}
    (hfix : ∀ g ∈ F, ∀ w ∈ CH, g w = w)
    (hinj : Function.Injective (subquotHom F CH ⊤ h₁ h₂))
    {s : Finset (Subquot CH ⊤ ≃ₗ[ZMod p] Subquot CH ⊤)}
    (hscard : s.card ≤ Module.finrank (ZMod p) U - 1)
    (hsrefl : ∀ x ∈ s, x ∈ (subquotHom F CH ⊤ h₁ h₂).range ∧ IsRefl p x)
    (hgen : (subquotHom F CH ⊤ h₁ h₂).range = Subgroup.closure (s : Set _)) : False := by
  obtain ⟨y, hy, hFgen⟩ := exists_isRefl_closure_eq_of_injective hp h₁ h₂
    (fun g hg w hw => hfix g hg w hw) (fun g hg v => Submodule.mem_top) hinj
    (fun i : s => (i : Subquot CH ⊤ ≃ₗ[ZMod p] Subquot CH ⊤)) (fun i => (hsrefl i i.2).2)
    (by rw [hgen]; congr 1; exact Subtype.range_coe.symm)
  have hFfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) ≤
      s.card := by
    have hle := HardMathSupport.Kantor79.finrank_commutatorSpace_le
      (fun i : s => (y i : U ≃ₗ[ZMod p] U)) (r := 1) (fun i => le_of_eq (hy i).1.2)
    rw [← hFgen] at hle
    simpa using hle
  have hsup_le : HardMathSupport.Kantor79.commutatorSpace H ⊔
      HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace F :=
    sup_le (HardMathSupport.Kantor79.commutatorSpace_mono hHF)
      (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hbF)
  have hdim := finrank_sup_commutatorSpace_movedSpace hs hb' hbH
  have hmono := Submodule.finrank_mono hsup_le
  rw [hdim] at hmono
  have hb_le : 1 ≤ Module.finrank (ZMod p) U := by
    have hdim_b : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace b) = 1 := hb'.2
    rw [← hdim_b]
    exact Submodule.finrank_le _
  have hle : Module.finrank (ZMod p) U ≤ s.card := hmono.trans hFfin
  have hle' : s.card ≤ Module.finrank (ZMod p) U - 1 := hscard
  omega

private theorem exists_isCompl_of_le {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1)) {b : U ≃ₗ[ZMod p] U}
    (hb' : IsRefl p b)
    (hbH : HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace H) :
    ∃ W : Submodule (ZMod p) U, IsCompl W (centralizerSpace H) ∧
      ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))), ∀ w ∈ W, g w ∈ W := by
  refine ⟨HardMathSupport.Kantor79.commutatorSpace H, hs.1, ?_⟩
  have hinv : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace H,
      b w ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    intro w hw
    have hdiff : b w - w ∈ HardMathSupport.Kantor79.commutatorSpace H := hbH ⟨w, rfl⟩
    have hsum := (HardMathSupport.Kantor79.commutatorSpace H).add_mem hw hdiff
    rwa [add_sub_cancel] at hsum
  refine closure_insert_mapsTo hb'.1 hinv ?_
  intro h hh w hw
  exact apply_mem_commutatorSpace hh hw

private theorem exists_isCompl_of_not_le (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (htab : TFNegOrGen p (Module.finrank (ZMod p) U - 1)) {G H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G) (hH : ReflGen p H)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    {b : U ≃ₗ[ZMod p] U} (hb : b ∈ G) (hb' : IsRefl p b)
    (hbe : ∀ v ∈ centralizerSpace H, b v = v)
    (hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace H) :
    ∃ W : Submodule (ZMod p) U, IsCompl W (centralizerSpace H) ∧
      ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))), ∀ w ∈ W, g w ∈ W := by
  set F := Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))
  have hHF : H ≤ F := le_closure_insert
  have hfix : ∀ g ∈ F, ∀ w ∈ centralizerSpace H, g w = w :=
    fixes_centralizerSpace_of_closure hbe
  have h₁ : ∀ g ∈ F, (centralizerSpace H).map (g : U →ₗ[ZMod p] U) = centralizerSpace H :=
    map_centralizerSpace_eq_self_of_closure hbe
  have h₂ : ∀ g ∈ F, (⊤ : Submodule (ZMod p) U).map (g : U →ₗ[ZMod p] U) = ⊤ := by
    intro g hg
    simp
  have hinj := subquotHom_injective_of_fixes hG hHG hs hb hb' hbe h₁ h₂
  have hJrefl : ReflGen p (subquotHom F (centralizerSpace H) ⊤ h₁ h₂).range :=
    reflGen_range_subquotHom hp (ReflGen.closure_insert hH hb') h₁ h₂ hfix
  have hirr := irred_range_subquotHom hHF hs.1
    (fun h hh x hx => apply_mem_commutatorSpace hh hx) hs.2.2 h₁ h₂
  have hfin := finrank_subquot_top hs hb'
  have hdJ := dLarge_range_subquotHom hp h₁ h₂ hfix hinj
    (by obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
        exact ⟨x, hHF hx, y, hHF hy, hxr, hyr, hxy⟩)
  have hbF : b ∈ F := Subgroup.subset_closure (Set.mem_insert b (H : Set (U ≃ₗ[ZMod p] U)))
  rcases neg_mem_or_exists_closure_eq_of_tfNegOrGen hp htab hfin hJrefl hirr hdJ with
    hneg | ⟨s, hscard, hsrefl, hgen⟩
  · exact exists_isCompl_of_neg_mem_range hp hs hb' hfix h₁ h₂ hinj hneg
  · exact (false_of_gen_range_subquot hp hHF hs hbF hb' hbH hfix hinj hscard hsrefl hgen).elim

theorem exists_isCompl_of_forall_apply_eq (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (htab : TFNegOrGen p (Module.finrank (ZMod p) U - 1)) {G H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G) (hH : ReflGen p H)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    {b : U ≃ₗ[ZMod p] U} (hb : b ∈ G) (hb' : IsRefl p b)
    (hbe : ∀ v ∈ centralizerSpace H, b v = v) :
    ∃ W : Submodule (ZMod p) U, IsCompl W (centralizerSpace H) ∧
      ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))), ∀ w ∈ W, g w ∈ W := by
  have _h4 : 4 ≤ Module.finrank (ZMod p) U := h4
  by_cases hbH : HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace H
  · exact exists_isCompl_of_le hs hb' hbH
  · exact exists_isCompl_of_not_le hp htab hG hHG hH hs hd hb hb' hbe hbH

private theorem exists_smul_of_invariant_line [Module.Finite (ZMod p) U]
    {CH : Submodule (ZMod p) U} (hdimCH : Module.finrank (ZMod p) CH = 1)
    {b : U ≃ₗ[ZMod p] U} (hb2 : b * b = 1) (hmap : CH.map (b : U →ₗ[ZMod p] U) = CH) :
    ∃ (f : U) (c : ZMod p), f ∈ CH ∧ f ≠ 0 ∧ b f = c • f ∧ c ^ 2 = 1 := by
  have hCHbot : CH ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdimCH
    exact Nat.zero_ne_one hdimCH
  obtain ⟨f, hfCH, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCHbot
  have hCHspan : CH = Submodule.span (ZMod p) {f} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdimCH hfCH hf0
  have hbfCH : b f ∈ CH := by
    have h : b f ∈ CH.map (b : U →ₗ[ZMod p] U) := Submodule.mem_map_of_mem hfCH
    rwa [hmap] at h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hCHspan ▸ hbfCH)
  refine ⟨f, c, hfCH, hf0, hc.symm, ?_⟩
  have h1 : b (b f) = f := by
    have := congrArg (fun e : U ≃ₗ[ZMod p] U => e f) hb2
    simpa [LinearEquiv.mul_apply] using this
  have h2 : c ^ 2 • f = f := by
    calc c ^ 2 • f = c • (c • f) := by rw [pow_two, smul_smul]
      _ = c • (b f) := by rw [hc]
      _ = b (c • f) := by rw [map_smul]
      _ = b (b f) := by rw [hc]
      _ = f := h1
  have h3 : (c ^ 2 - 1) • f = 0 := by rw [sub_smul, one_smul, h2, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hf0)

private theorem eq_centralizerSpace_of_le_of_ne_bot [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    {b : U ≃ₗ[ZMod p] U} (hb' : IsRefl p b) {X : Submodule (ZMod p) U}
    (hX : X ≤ centralizerSpace H) (hne : X ≠ ⊥) : X = centralizerSpace H := by
  have hdimCH : Module.finrank (ZMod p) (centralizerSpace H) = 1 :=
    (by
      have h := hs.finrank_centralizerSpace
      have hn : 1 ≤ Module.finrank (ZMod p) U :=
        hb'.2 ▸ Submodule.finrank_le (HardMathSupport.Kantor79.movedSpace b)
      omega)
  have hpos : 0 < Module.finrank (ZMod p) X := by
    rcases Nat.eq_zero_or_pos (Module.finrank (ZMod p) X) with h0 | h0
    · exact absurd (Submodule.finrank_eq_zero.mp h0) hne
    · exact h0
  exact Submodule.eq_of_le_of_finrank_eq hX (by
    have := Submodule.finrank_mono hX
    omega)

private theorem eq_commutatorSpace_of_le_of_ne_top [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    {X : Submodule (ZMod p) U} (hX : HardMathSupport.Kantor79.commutatorSpace H ≤ X)
    (hne : X ≠ ⊤) : X = HardMathSupport.Kantor79.commutatorSpace H := by
  have hlt : Module.finrank (ZMod p) X < Module.finrank (ZMod p) U := Submodule.finrank_lt hne
  have hmono : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) ≤
      Module.finrank (ZMod p) X := Submodule.finrank_mono hX
  have hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) =
      Module.finrank (ZMod p) U - 1 := hs.2.1
  exact (Submodule.eq_of_le_of_finrank_eq hX (by omega)).symm

private theorem fixes_centralizer_of_invariant_le (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    {b : U ≃ₗ[ZMod p] U} (hb' : IsRefl p b)
    (hbH' : ¬ HardMathSupport.Kantor79.movedSpace b ≤ centralizerSpace H)
    (hbF : b ∈ F) {X : Submodule (ZMod p) U}
    (hXinv : ∀ g ∈ F, ∀ x ∈ X, g x ∈ X) (hX : X ≤ centralizerSpace H) (hne : X ≠ ⊥) :
    ∀ v ∈ centralizerSpace H, b v = v := by
  have hXeq : X = centralizerSpace H := eq_centralizerSpace_of_le_of_ne_bot hs hb' hX hne
  have hbb : ∀ x : U, b (b x) = x := by
    intro x
    have := congrArg (fun e : U ≃ₗ[ZMod p] U => e x) hb'.1
    simpa [LinearEquiv.mul_apply] using this
  have hbCH : ∀ w ∈ centralizerSpace H, b w ∈ centralizerSpace H := by
    intro w hw
    exact hXeq ▸ hXinv b hbF w (hXeq ▸ hw)
  have hmap : (centralizerSpace H).map (b : U →ₗ[ZMod p] U) = centralizerSpace H := by
    refine le_antisymm (fun x hx => ?_) (fun w hw => ⟨b w, hbCH w hw, hbb w⟩)
    obtain ⟨y, hy, rfl⟩ := hx
    exact hbCH y hy
  obtain ⟨f, c, hfCH, hf0, hbf, hc2⟩ := exists_smul_of_invariant_line
    ((by
      have h := hs.finrank_centralizerSpace
      have hn : 1 ≤ Module.finrank (ZMod p) U :=
        hb'.2 ▸ Submodule.finrank_le (HardMathSupport.Kantor79.movedSpace b)
      omega)) hb'.1 hmap
  have hCHspan : centralizerSpace H = Submodule.span (ZMod p) {f} :=
    eq_span_singleton_of_mem_of_finrank_eq_one ((by
      have h := hs.finrank_centralizerSpace
      have hn : 1 ≤ Module.finrank (ZMod p) U :=
        hb'.2 ▸ Submodule.finrank_le (HardMathSupport.Kantor79.movedSpace b)
      omega))
      hfCH hf0
  rcases sq_eq_one_iff.mp hc2 with hc1 | hcm1
  · intro v hv
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (hCHspan ▸ hv)
    rw [← hd, map_smul, hbf, hc1, one_smul]
  · exact absurd (movedSpace_le_centralizer_of_apply_eq_neg hp hb' hf0 hCHspan
      (by rw [hbf, hcm1, neg_one_smul])) hbH'

private theorem false_of_compl_centralizer (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (htab : TFNegOrGen p (Module.finrank (ZMod p) U - 1)) {G H : Subgroup (U ≃ₗ[ZMod p] U)}
    {b : U ≃ₗ[ZMod p] U}
    (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G) (hH : ReflGen p H)
    (hHF : H ≤ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))))
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hb : b ∈ G) (hb' : IsRefl p b)
    (hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hbH' : ¬ HardMathSupport.Kantor79.movedSpace b ≤ centralizerSpace H)
    (hbF : b ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))))
    (hbe : ∀ v ∈ centralizerSpace H, b v = v) : False := by
  obtain ⟨W, hWcompl, hWinv⟩ :=
    exists_isCompl_of_forall_apply_eq hp h4 htab hG hHG hH hs hd hb hb' hbe
  have hirrH : IrredOnSection H
      (HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H)
      (HardMathSupport.Kantor79.commutatorSpace H) := by
    rw [hs.1.inf_eq_bot]
    exact hs.2.2
  have hWH : ∀ h ∈ H, ∀ w ∈ W, h w ∈ W := fun h hh w hw => hWinv h (hHF hh) w hw
  have hCH : Module.finrank (ZMod p) (centralizerSpace H) = 1 :=
    (by
      have h := hs.finrank_centralizerSpace
      have hn : 1 ≤ Module.finrank (ZMod p) U :=
        hb'.2 ▸ Submodule.finrank_le (HardMathSupport.Kantor79.movedSpace b)
      omega)
  rcases commutatorSpace_le_or_le_centralizerSpace hp hH hirrH hWH with hVHW | hWCH
  · have hsum := Submodule.finrank_add_eq_of_isCompl hWcompl
    have hVH : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) =
        Module.finrank (ZMod p) U - 1 := hs.2.1
    have hdimW : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) =
        Module.finrank (ZMod p) W := by omega
    have hWeq : W = HardMathSupport.Kantor79.commutatorSpace H :=
      (Submodule.eq_of_le_of_finrank_eq hVHW hdimW).symm
    have hinv : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace H,
        b w ∈ HardMathSupport.Kantor79.commutatorSpace H := by
      intro w hw
      have h := hWinv b hbF w (by rwa [hWeq])
      rwa [hWeq] at h
    exact hbH' (movedSpace_le_centralizerSpace_of_mapsTo hp hG hHG hs hb hb' hbH hinv)
  · have hbot : W = ⊥ := by
      have hle : W ≤ W ⊓ centralizerSpace H := le_inf le_rfl hWCH
      rw [hWcompl.inf_eq_bot] at hle
      exact le_bot_iff.mp hle
    have hsum := Submodule.finrank_add_eq_of_isCompl hWcompl
    rw [hbot, finrank_bot, zero_add, hCH] at hsum
    omega

theorem irredOnSection_closure_insert_of_not_le (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (htab : TFNegOrGen p (Module.finrank (ZMod p) U - 1)) {G H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G) (hH : ReflGen p H)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    {b : U ≃ₗ[ZMod p] U} (hb : b ∈ G) (hb' : IsRefl p b)
    (hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hbH' : ¬ HardMathSupport.Kantor79.movedSpace b ≤ centralizerSpace H) :
    IrredOnSection (Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))) ⊥ ⊤ := by
  set F := Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))
  intro X hbot htop hXinv
  have hHF : H ≤ F := le_closure_insert
  have hXH : ∀ h ∈ H, ∀ x ∈ X, h x ∈ X := fun h hh x hx => hXinv h (hHF hh) x hx
  by_cases hXbot : X = ⊥
  · exact Or.inl hXbot
  by_cases hXtop : X = ⊤
  · exact Or.inr hXtop
  exfalso
  have hirrH : IrredOnSection H
      (HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H)
      (HardMathSupport.Kantor79.commutatorSpace H) := by
    rw [hs.1.inf_eq_bot]
    exact hs.2.2
  rcases commutatorSpace_le_or_le_centralizerSpace hp hH hirrH hXH with hVHX | hXCH
  · have hXeq : X = HardMathSupport.Kantor79.commutatorSpace H :=
      eq_commutatorSpace_of_le_of_ne_top hs hVHX hXtop
    have hbF : b ∈ F := Subgroup.subset_closure (Set.mem_insert b (H : Set (U ≃ₗ[ZMod p] U)))
    have hinv : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace H,
        b w ∈ HardMathSupport.Kantor79.commutatorSpace H := by
      intro w hw
      have h := hXinv b hbF w (hXeq ▸ hw)
      rwa [hXeq] at h
    exact hbH' (movedSpace_le_centralizerSpace_of_mapsTo hp hG hHG hs hb hb' hbH hinv)
  · have hbF : b ∈ F := Subgroup.subset_closure (Set.mem_insert b (H : Set (U ≃ₗ[ZMod p] U)))
    have hbe := fixes_centralizer_of_invariant_le hp hs hb' hbH' hbF hXinv hXCH hXbot
    exact false_of_compl_centralizer hp h4 htab hG hHG hH (b := b) le_closure_insert hs hd
      hb hb' hbH hbH' (by exact hbF) hbe

theorem mem_of_movedSpace_le_of_maximal (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : 4 ≤ Module.finrank (ZMod p) U)
    (htab : TFNegOrGen p (Module.finrank (ZMod p) U - 1)) {G H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G) (hH : ReflGen p H)
    (hs : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hmax : ∀ K : Subgroup (U ≃ₗ[ZMod p] U), K ≤ G → H ≤ K → ReflGen p K →
      SplitSupport K (Module.finrank (ZMod p) U - 1) → K = H)
    {b : U ≃ₗ[ZMod p] U} (hb : b ∈ G) (hb' : IsRefl p b)
    (hbH : HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H) :
    b ∈ H := by
  set F := Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))) with hF
  have hHF : H ≤ F := le_closure_insert
  have hFG : F ≤ G := closure_insert_le hb hHG
  have hFgen : ReflGen p F := by rw [hF]; exact ReflGen.closure_insert hH hb'
  have hFs : SplitSupport F (Module.finrank (ZMod p) U - 1) :=
    splitSupport_closure_insert_of_le hp h4 htab hG hHG hH hs hd hb hb' hbH
  have hEq : F = H := hmax F hFG hHF hFgen hFs
  have hbF : b ∈ F := Subgroup.subset_closure (Set.mem_insert b (H : Set (U ≃ₗ[ZMod p] U)))
  rwa [hEq] at hbF

end CFSG.StandardType.ZS

end

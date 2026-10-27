module

public import CFSG.LocalAnalysis.StandardType.ZS.TableDefs
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneFiveNeg
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneFiveConj
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneFour
import CFSG.LocalAnalysis.StandardType.ZS.Subquotient

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem apply_eq_neg_of_mem_movedSpace {x : U ≃ₗ[ZMod p] U} (hx : x * x = 1) {v : U}
    (hv : v ∈ HardMathSupport.Kantor79.movedSpace x) : x v = -v := by
  obtain ⟨u, rfl⟩ := hv
  change x (x u - u) = -(x u - u)
  rw [map_sub]
  have h1 : x (x u) = u := by
    have := congrArg (fun e : U ≃ₗ[ZMod p] U => e u) hx
    simpa [LinearEquiv.mul_apply] using this
  rw [h1]
  abel

private theorem subquotEquiv_apply_mk (W VF : Submodule (ZMod p) U) (f : U ≃ₗ[ZMod p] U)
    (h₁ : W.map (f : U →ₗ[ZMod p] U) = W) (h₂ : VF.map (f : U →ₗ[ZMod p] U) = VF)
    (w : ↥VF) :
    subquotEquiv W VF f h₁ h₂ (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (f.ofSubmodules VF VF h₂ w) := by
  simp only [subquotEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  rfl

private theorem subquot_neg_mk {W VF : Submodule (ZMod p) U} (w : ↥VF) :
    -(Submodule.Quotient.mk w : Subquot W VF) = Submodule.Quotient.mk (-w) :=
  (map_neg (Submodule.mkQ (W.comap VF.subtype)) w).symm

private theorem subquotEquiv_eq_neg_iff {W VF : Submodule (ZMod p) U} {f : U ≃ₗ[ZMod p] U}
    (h₁ : W.map (f : U →ₗ[ZMod p] U) = W) (h₂ : VF.map (f : U →ₗ[ZMod p] U) = VF) :
    subquotEquiv W VF f h₁ h₂ = LinearEquiv.neg (ZMod p) ↔
      ∀ v ∈ VF, f v + v ∈ W := by
  constructor
  · intro h v hv
    let w : ↥VF := ⟨v, hv⟩
    have happ := congrArg (fun e : Subquot W VF ≃ₗ[ZMod p] Subquot W VF =>
      e (Submodule.Quotient.mk w)) h
    rw [subquotEquiv_apply_mk, LinearEquiv.neg_apply, subquot_neg_mk] at happ
    rw [Submodule.Quotient.eq, Submodule.mem_comap] at happ
    have hcoe : VF.subtype ((f.ofSubmodules VF VF h₂) w) = f v := rfl
    have hneg : VF.subtype (-w : ↥VF) = -v := rfl
    have hval : VF.subtype ((f.ofSubmodules VF VF h₂) w - -w) = f v + v := by
      rw [map_sub, hcoe, hneg, sub_neg_eq_add]
    rwa [hval] at happ
  · intro h
    ext x
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [subquotEquiv_apply_mk, LinearEquiv.neg_apply, subquot_neg_mk]
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    have hcoe : VF.subtype ((f.ofSubmodules VF VF h₂) w) = f (w : U) := rfl
    have hneg : VF.subtype (-w : ↥VF) = -(w : U) := rfl
    have hval : VF.subtype ((f.ofSubmodules VF VF h₂) w - -w) = f (w : U) + (w : U) := by
      rw [map_sub, hcoe, hneg, sub_neg_eq_add]
    rw [hval]
    exact h (w : U) w.2

private theorem subquotHom_eq_one_iff {F : Subgroup (U ≃ₗ[ZMod p] U)} {W VF : Submodule (ZMod p) U}
    (h₁ : ∀ g ∈ F, W.map (g : U →ₗ[ZMod p] U) = W)
    (h₂ : ∀ g ∈ F, VF.map (g : U →ₗ[ZMod p] U) = VF) (k : F) :
    subquotHom F W VF h₁ h₂ k = 1 ↔ ∀ v ∈ VF, (k : U ≃ₗ[ZMod p] U) v - v ∈ W := by
  change subquotEquiv W VF (k : U ≃ₗ[ZMod p] U) (h₁ k k.2) (h₂ k k.2) = 1 ↔ _
  exact subquotEquiv_eq_one_iff _ _

private theorem subquotHom_eq_iff {F : Subgroup (U ≃ₗ[ZMod p] U)} {W VF : Submodule (ZMod p) U}
    (hWleVc : W ≤ centralizerSpace F)
    (hWeq : ∀ v ∈ VF, v ∈ W ↔ v ∈ centralizerSpace F)
    (hWinv : ∀ g ∈ F, ∀ w ∈ W, g w ∈ W)
    (hVFinv : ∀ g ∈ F, ∀ v ∈ VF, g v ∈ VF)
    (h₁ : ∀ g ∈ F, W.map (g : U →ₗ[ZMod p] U) = W)
    (h₂ : ∀ g ∈ F, VF.map (g : U →ₗ[ZMod p] U) = VF)
    {f g : U ≃ₗ[ZMod p] U} (hf : f ∈ F) (hg : g ∈ F) :
    subquotHom F W VF h₁ h₂ ⟨f, hf⟩ = subquotHom F W VF h₁ h₂ ⟨g, hg⟩ ↔
      ∀ v ∈ VF, f v - g v ∈ centralizerSpace F := by
  constructor
  · intro hfg
    have hker : subquotHom F W VF h₁ h₂ (⟨g, hg⟩⁻¹ * ⟨f, hf⟩) = 1 := by
      rw [map_mul, map_inv, hfg, inv_mul_cancel]
    have hmem := (subquotHom_eq_one_iff h₁ h₂ _).mp hker
    intro v hv
    refine hWleVc ?_
    have hfix : g ((g⁻¹ * f) v - v) = (g⁻¹ * f) v - v :=
      (mem_centralizerSpace.mp (hWleVc (hmem v hv))) g hg
    have hcalc : g ((g⁻¹ * f) v - v) = f v - g v := by
      simp [LinearEquiv.mul_apply]
    have heq : f v - g v = (g⁻¹ * f) v - v := hcalc.symm.trans hfix
    rw [heq]
    exact hmem v hv
  · intro hpt
    let gF : F := ⟨g, hg⟩
    let fF : F := ⟨f, hf⟩
    have hker : subquotHom F W VF h₁ h₂ (gF⁻¹ * fF) = 1 := by
      rw [subquotHom_eq_one_iff h₁ h₂ (gF⁻¹ * fF)]
      intro v hv
      have hfgv : f v - g v ∈ centralizerSpace F := hpt v hv
      have hfgVF : f v - g v ∈ VF :=
        VF.sub_mem (hVFinv f hf v hv) (hVFinv g hg v hv)
      have hWmem : f v - g v ∈ W := (hWeq _ hfgVF).mpr hfgv
      have := hWinv g⁻¹ (F.inv_mem hg) (f v - g v) hWmem
      have heq : (↑(gF⁻¹ * fF) : U ≃ₗ[ZMod p] U) v - v = g⁻¹ (f v - g v) := by
        rw [show (↑(gF⁻¹ * fF) : U ≃ₗ[ZMod p] U) = g⁻¹ * f from rfl]
        simp [LinearEquiv.mul_apply]
      rwa [heq]
    have : subquotHom F W VF h₁ h₂ fF = subquotHom F W VF h₁ h₂ gF := by
      nth_rewrite 1 [show fF = gF * (gF⁻¹ * fF) by group]
      rw [map_mul, hker, mul_one]
    exact this

private theorem two_le_of_splitSupport_dLarge [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hHs : SplitSupport H l)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    2 ≤ l := by
  by_contra h
  push Not at h
  obtain ⟨x, hxH, y, hyH, hxr, hyr, hxy⟩ := hd
  have hfinx : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace x) = 1 := hxr.2
  have hmvx : HardMathSupport.Kantor79.movedSpace x ≤
      HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hxH
  have hlx : l = 1 := by
    have hmono := Submodule.finrank_mono hmvx
    rw [hfinx, hHs.2.1] at hmono
    omega
  have heqx : HardMathSupport.Kantor79.movedSpace x =
      HardMathSupport.Kantor79.commutatorSpace H :=
    Submodule.eq_of_le_of_finrank_eq hmvx (by rw [hfinx, hHs.2.1, hlx])
  have hfiny : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace y) = 1 := hyr.2
  have hmvy : HardMathSupport.Kantor79.movedSpace y ≤
      HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hyH
  have hly : l = 1 := by
    have hmono := Submodule.finrank_mono hmvy
    rw [hfiny, hHs.2.1] at hmono
    omega
  have heqy : HardMathSupport.Kantor79.movedSpace y =
      HardMathSupport.Kantor79.commutatorSpace H :=
    Submodule.eq_of_le_of_finrank_eq hmvy (by rw [hfiny, hHs.2.1, hly])
  have hxy_eq : x = y := by
    ext v
    have hv : v ∈ HardMathSupport.Kantor79.commutatorSpace H ⊔ centralizerSpace H := by
      rw [hHs.1.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    have hxa : x a = -a := apply_eq_neg_of_mem_movedSpace hxr.1 (by rw [heqx]; exact ha)
    have hya : y a = -a := apply_eq_neg_of_mem_movedSpace hyr.1 (by rw [heqy]; exact ha)
    have hxb : x b = b := (mem_centralizerSpace.mp hb) x hxH
    have hyb : y b = b := (mem_centralizerSpace.mp hb) y hyH
    simp only [map_add, hxa, hya, hxb, hyb]
  have h1 : x * y = 1 := by rw [← hxy_eq, hxr.1]
  rw [h1, orderOf_one] at hxy
  omega

private theorem commutatorSpace_closure_le_span {ι : Type} (s : Finset ι) (y : s → U ≃ₗ[ZMod p] U)
    (ρ : s → U)
    (hspan : ∀ i : s, HardMathSupport.Kantor79.movedSpace (y i) =
      Submodule.span (ZMod p) {ρ i}) :
    HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure (Set.range fun i : s => (y i : U ≃ₗ[ZMod p] U))) ≤
      Submodule.span (ZMod p) (Set.range ρ) := by
  rw [commutatorSpace_le_iff]
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem t ht =>
      obtain ⟨i, rfl⟩ := ht
      intro v
      have hmv : (y i) v - v ∈ HardMathSupport.Kantor79.movedSpace (y i) := ⟨v, rfl⟩
      rw [hspan i] at hmv
      exact Submodule.span_le.mpr
        (Set.singleton_subset_iff.mpr
          (Submodule.subset_span (Set.mem_range_self (f := ρ) i))) hmv
  | one => intro v; simp
  | mul a b ha hb iha ihb =>
      intro v
      rw [LinearEquiv.mul_apply,
        show a (b v) - v = (a (b v) - b v) + (b v - v) by abel]
      exact Submodule.add_mem _ (iha (b v)) (ihb v)
  | inv a ha iha =>
      intro v
      have h : a (a⁻¹ v) = v := LinearEquiv.apply_symm_apply a v
      have hneg : a⁻¹ v - v = -(a (a⁻¹ v) - a⁻¹ v) := by rw [h]; abel
      rw [hneg]
      exact Submodule.neg_mem _ (iha (a⁻¹ v))

private theorem finrank_commutatorSpace_closure_le_card [Module.Finite (ZMod p) U]
    {ι : Type} (s : Finset ι) (y : s → U ≃ₗ[ZMod p] U) (hy : ∀ i : s, IsRefl p (y i)) :
    Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure (Set.range fun i : s => (y i : U ≃ₗ[ZMod p] U)))) ≤ s.card := by
  classical
  have hne : ∀ i : s, HardMathSupport.Kantor79.movedSpace (y i) ≠ ⊥ := by
    intro i hbot
    have h1 := (hy i).2
    change Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace (y i)) = 1 at h1
    rw [hbot, finrank_bot] at h1
    exact Nat.zero_ne_one h1
  choose ρ hρ using fun i : s => Submodule.exists_mem_ne_zero_of_ne_bot (hne i)
  have hspan : ∀ i : s, HardMathSupport.Kantor79.movedSpace (y i) =
      Submodule.span (ZMod p) {ρ i} := fun i =>
    eq_span_singleton_of_mem_of_finrank_eq_one (hy i).2 (hρ i).1 (hρ i).2
  have hle := commutatorSpace_closure_le_span s y ρ hspan
  refine (Submodule.finrank_mono hle).trans ?_
  have h := finrank_range_le_card (R := ZMod p) ρ
  rwa [Fintype.card_coe] at h

private abbrev VFof (F : Subgroup (U ≃ₗ[ZMod p] U)) : Submodule (ZMod p) U :=
  HardMathSupport.Kantor79.commutatorSpace F

private abbrev Wof (F : Subgroup (U ≃ₗ[ZMod p] U)) : Submodule (ZMod p) U :=
  VFof F ⊓ centralizerSpace F

private theorem subquotHomF_inv₁ (F : Subgroup (U ≃ₗ[ZMod p] U)) :
    ∀ g ∈ F, (Wof F).map (g : U →ₗ[ZMod p] U) = Wof F := by
  intro g hg
  refine map_eq_self_of_invariant (fun k hk w hw => ?_) hg
  refine ⟨apply_mem_commutatorSpace hk hw.1, ?_⟩
  refine (mem_centralizerSpace).mpr fun j hj => ?_
  rw [(mem_centralizerSpace.mp hw.2) k hk]
  exact (mem_centralizerSpace.mp hw.2) j hj

private theorem subquotHomF_inv₂ (F : Subgroup (U ≃ₗ[ZMod p] U)) :
    ∀ g ∈ F, (VFof F).map (g : U →ₗ[ZMod p] U) = VFof F := by
  intro g hg
  exact map_eq_self_of_invariant (fun k hk w hw => apply_mem_commutatorSpace hk hw) hg

private theorem subquotHomF_triv (F : Subgroup (U ≃ₗ[ZMod p] U)) :
    ∀ g ∈ F, ∀ w ∈ Wof F, g w = w := by
  intro g hg w hw
  exact (mem_centralizerSpace.mp hw.2) g hg

private theorem subquotHomF_sub (F : Subgroup (U ≃ₗ[ZMod p] U)) :
    ∀ g ∈ F, ∀ v : U, g v - v ∈ VFof F := by
  intro g hg v
  exact Submodule.subset_span ⟨g, hg, v, rfl⟩

private theorem subquotHomF_W_le_centralizer (F : Subgroup (U ≃ₗ[ZMod p] U)) :
    Wof F ≤ centralizerSpace F :=
  inf_le_right

private theorem subquotHomF_W_mem (F : Subgroup (U ≃ₗ[ZMod p] U)) (v : U) (hv : v ∈ VFof F) :
    v ∈ Wof F ↔ v ∈ centralizerSpace F :=
  ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩

private theorem subquotHomF_W_inv (F : Subgroup (U ≃ₗ[ZMod p] U)) :
    ∀ g ∈ F, ∀ w ∈ Wof F, g w ∈ Wof F := by
  intro g hg w hw
  refine ⟨apply_mem_commutatorSpace hg hw.1, ?_⟩
  refine (mem_centralizerSpace).mpr fun k hk => ?_
  rw [(mem_centralizerSpace.mp hw.2) g hg]
  exact (mem_centralizerSpace.mp hw.2) k hk

private theorem subquotHomF_VF_inv (F : Subgroup (U ≃ₗ[ZMod p] U)) :
    ∀ g ∈ F, ∀ v ∈ VFof F, g v ∈ VFof F :=
  fun _ hg _ hv => apply_mem_commutatorSpace hg hv

private theorem subquotHomF_Vc_inv (F : Subgroup (U ≃ₗ[ZMod p] U)) :
    ∀ g ∈ F, ∀ w ∈ centralizerSpace F, g w ∈ centralizerSpace F := by
  intro g hg w hw
  refine (mem_centralizerSpace).mpr fun k hk => ?_
  rw [(mem_centralizerSpace.mp hw) g hg]
  exact (mem_centralizerSpace.mp hw) k hk

private noncomputable def subquotHomF (F : Subgroup (U ≃ₗ[ZMod p] U)) :
    F →* (Subquot (Wof F) (VFof F) ≃ₗ[ZMod p] Subquot (Wof F) (VFof F)) :=
  subquotHom F _ _ (subquotHomF_inv₁ F) (subquotHomF_inv₂ F)

private theorem subquot_range_reflGen (hp : p ≠ 2) {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (hF : ReflGen p F) : ReflGen p (subquotHomF F).range := by
  unfold ReflGen
  let R' : Set F := {t | IsRefl p (t : U ≃ₗ[ZMod p] U)}
  have hFclo : Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ F ∧ IsRefl p t} = F :=
    (show F = Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ F ∧ IsRefl p t} from hF).symm
  have himg : Subgroup.subtype F '' R' = {t : U ≃ₗ[ZMod p] U | t ∈ F ∧ IsRefl p t} := by
    ext t; constructor
    · rintro ⟨g, hg, rfl⟩; exact ⟨g.2, hg⟩
    · rintro ⟨htF, htr⟩; exact ⟨⟨t, htF⟩, htr, rfl⟩
  have htop : (⊤ : Subgroup F) = Subgroup.closure R' := by
    apply Subgroup.map_injective (f := Subgroup.subtype F) (fun a b h => Subtype.ext h)
    rw [MonoidHom.map_closure, himg, hFclo]
    exact (MonoidHom.range_eq_map (Subgroup.subtype F)).symm.trans (Subgroup.range_subtype F)
  have hgen : (subquotHomF F).range = Subgroup.closure (subquotHomF F '' R') := by
    rw [MonoidHom.range_eq_map, htop, MonoidHom.map_closure]
  nth_rewrite 1 [hgen]
  refine le_antisymm ?_ ?_
  · refine (Subgroup.closure_le _).mpr ?_
    rintro t ⟨g, hg, hgt⟩
    rw [← hgt]
    have hrefl := isRefl_subquotHom hp (subquotHomF_inv₁ F) (subquotHomF_inv₂ F)
      (subquotHomF_triv F) (subquotHomF_sub F) (t := g) hg
    exact Subgroup.subset_closure ⟨⟨g, rfl⟩, hrefl⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro t ⟨htJ, _⟩
    rw [← hgen]; exact htJ

private theorem subquot_finrank [Module.Finite (ZMod p) U] {l : ℕ}
    {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (hVF : Module.finrank (ZMod p) (VFof F) = l + 1)
    (hW : Module.finrank (ZMod p) ↥(Wof F) = 1) :
    Module.finrank (ZMod p) (Subquot (Wof F) (VFof F)) = l := by
  have hpre : Module.finrank (ZMod p) ↥((Wof F).comap (VFof F).subtype) = 1 := by
    rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_left), hW]
  have hq := Submodule.finrank_quotient_add_finrank (R := ZMod p) ((Wof F).comap (VFof F).subtype)
  rw [hpre, hVF] at hq
  change Module.finrank (ZMod p) (↥(VFof F) ⧸ (Wof F).comap (VFof F).subtype) = l
  omega

private theorem subquot_comap_map_eq_bot {VF W : Submodule (ZMod p) U} (hWVF : W ≤ VF)
    (X : Submodule (ZMod p) (Subquot W VF)) :
    ((X.comap (Submodule.mkQ (W.comap VF.subtype))).map VF.subtype = W) ↔ X = ⊥ := by
  constructor
  · intro hXt
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (W.comap VF.subtype) x
    have hvXt : (v : U) ∈ (X.comap (Submodule.mkQ (W.comap VF.subtype))).map VF.subtype :=
      Submodule.mem_map.mpr ⟨v, hx, rfl⟩
    rw [hXt] at hvXt
    have hq0 : (Submodule.mkQ (W.comap VF.subtype)) v = 0 := by
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr hvXt)
    rw [hq0]
    exact Submodule.zero_mem ⊥
  · intro hX
    rw [hX, Submodule.comap_bot, Submodule.ker_mkQ, Submodule.map_comap_subtype,
      inf_eq_right.mpr hWVF]

private theorem subquot_comap_map_eq_top {VF W : Submodule (ZMod p) U}
    (X : Submodule (ZMod p) (Subquot W VF)) :
    ((X.comap (Submodule.mkQ (W.comap VF.subtype))).map VF.subtype = VF) ↔ X = ⊤ := by
  constructor
  · intro hXt
    rw [eq_top_iff]
    intro x _
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (W.comap VF.subtype) x
    have hvXt : (v : U) ∈ (X.comap (Submodule.mkQ (W.comap VF.subtype))).map VF.subtype := by
      rw [hXt]; exact v.2
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hvXt
    have hwv' : w = v := Subtype.ext hwv
    rwa [hwv'] at hw
  · intro hX
    rw [hX, Submodule.comap_top, Submodule.map_subtype_top]

private theorem subquot_preimage_sup {VF VH W : Submodule (ZMod p) U} (hWVF : W ≤ VF)
    (hVF : VF = VH ⊔ W) (X : Submodule (ZMod p) (Subquot W VF)) :
    (X.comap (Submodule.mkQ (W.comap VF.subtype))).map VF.subtype =
      ((X.comap (Submodule.mkQ (W.comap VF.subtype))).map VF.subtype ⊓ VH) ⊔ W := by
  set Xt : Submodule (ZMod p) U := (X.comap (Submodule.mkQ (W.comap VF.subtype))).map VF.subtype
    with hXtdef
  have hWq : W.comap VF.subtype ≤ X.comap (Submodule.mkQ (W.comap VF.subtype)) := by
    intro v hv
    rw [Submodule.mem_comap]
    have hq0 : (Submodule.mkQ (W.comap VF.subtype)) v = 0 := by
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hv
    rw [hq0]
    exact Submodule.zero_mem X
  have hWXt : W ≤ Xt := by
    have hm : (W.comap VF.subtype).map VF.subtype = W := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hWVF]
    rw [hXtdef]
    exact (le_of_eq hm.symm).trans (Submodule.map_mono hWq)
  have hXtVF : Xt ≤ VF := by
    rw [hXtdef]; exact Submodule.map_subtype_le VF _
  refine le_antisymm ?_ (sup_le inf_le_left hWXt)
  intro x hx
  have hxVF : x ∈ VF := hXtVF hx
  rw [hVF] at hxVF
  obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp hxVF
  have hwXt : w ∈ Xt := hWXt hw
  have hvXt : v ∈ Xt := by
    have : v = x - w := by rw [← hvw]; abel
    rw [this]; exact Xt.sub_mem hx hwXt
  rw [← hvw]
  exact Submodule.add_mem_sup ⟨hvXt, hv⟩ hw

private theorem subquot_preimage_invariant {F : Subgroup (U ≃ₗ[ZMod p] U)}
    (X : Submodule (ZMod p) (Subquot (Wof F) (VFof F)))
    (hXinv : ∀ g ∈ (subquotHomF F).range, ∀ x ∈ X, g x ∈ X) :
    ∀ f ∈ F, ∀ x ∈ (X.comap (Submodule.mkQ ((Wof F).comap (VFof F).subtype))).map
        (VFof F).subtype,
      f x ∈ (X.comap (Submodule.mkQ ((Wof F).comap (VFof F).subtype))).map (VFof F).subtype := by
  intro f hf x hx
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
  refine Submodule.mem_map.mpr ⟨f.ofSubmodules (VFof F) (VFof F) (subquotHomF_inv₂ F f hf) v,
    ?_, rfl⟩
  rw [Submodule.mem_comap]
  have hact : (Submodule.mkQ ((Wof F).comap (VFof F).subtype))
      (f.ofSubmodules (VFof F) (VFof F) (subquotHomF_inv₂ F f hf) v) =
      (subquotHomF F ⟨f, hf⟩) ((Submodule.mkQ ((Wof F).comap (VFof F).subtype)) v) := by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
    rw [show (subquotHomF F ⟨f, hf⟩) (Submodule.Quotient.mk v) =
        subquotEquiv (Wof F) (VFof F) f (subquotHomF_inv₁ F f hf) (subquotHomF_inv₂ F f hf)
          (Submodule.Quotient.mk v) from rfl,
      subquotEquiv_apply_mk]
  rw [hact]
  exact hXinv (subquotHomF F ⟨f, hf⟩) ⟨⟨f, hf⟩, rfl⟩ _ hv

private theorem subquot_irreducible [Module.Finite (ZMod p) U] {l : ℕ}
    {F H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hHF : H ≤ F) (hHs : SplitSupport H l)
    (hVF : Module.finrank (ZMod p) (VFof F) = l + 1)
    (hW : Module.finrank (ZMod p) ↥(Wof F) = 1) :
    ∀ X : Submodule (ZMod p) (Subquot (Wof F) (VFof F)),
      (∀ g ∈ (subquotHomF F).range, ∀ x ∈ X, g x ∈ X) → X = ⊥ ∨ X = ⊤ := by
  intro X hXinv
  let VH : Submodule (ZMod p) U := HardMathSupport.Kantor79.commutatorSpace H
  let Xt : Submodule (ZMod p) U := (X.comap (Submodule.mkQ ((Wof F).comap (VFof F).subtype))).map
    (VFof F).subtype
  have hVF_eq : VFof F = VH ⊔ Wof F := by
    have h := (commutatorSpace_eq_sup_of_splitSupport hHF hHs hVF hW).1
    simpa only [VH, Wof] using h
  have hXt_sup : Xt = (Xt ⊓ VH) ⊔ Wof F := subquot_preimage_sup inf_le_left hVF_eq X
  have hXtF : ∀ f ∈ F, ∀ x ∈ Xt, f x ∈ Xt := subquot_preimage_invariant X hXinv
  have hHinv : ∀ h ∈ H, ∀ x ∈ Xt ⊓ VH, h x ∈ Xt ⊓ VH := by
    intro h hh x hx
    exact ⟨hXtF h (hHF hh) x hx.1, apply_mem_commutatorSpace hh hx.2⟩
  rcases hHs.2.2 (Xt ⊓ VH) bot_le inf_le_right hHinv with hXH | hXH
  · left
    have hXt_eq_bot : Xt = Wof F := by rw [hXt_sup, hXH, bot_sup_eq]
    exact (subquot_comap_map_eq_bot inf_le_left X).mp hXt_eq_bot
  · right
    have hXt_eq_top : Xt = VFof F := by
      rw [hXt_sup, hXH]
      exact hVF_eq.symm
    exact (subquot_comap_map_eq_top X).mp hXt_eq_top

private theorem subquotHom_injective_on {l : ℕ} {F H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hHF : H ≤ F) (hHs : SplitSupport H l) :
    Function.Injective ((subquotHomF F).comp (Subgroup.inclusion hHF)) := by
  intro a b hab
  have hpt : ∀ v ∈ VFof F, (a : U ≃ₗ[ZMod p] U) v - (b : U ≃ₗ[ZMod p] U) v ∈
      centralizerSpace F :=
    (subquotHom_eq_iff (subquotHomF_W_le_centralizer F) (subquotHomF_W_mem F)
      (subquotHomF_W_inv F) (subquotHomF_VF_inv F) (subquotHomF_inv₁ F) (subquotHomF_inv₂ F)
      (hHF a.2) (hHF b.2)).mp hab
  have h1 : (a : U ≃ₗ[ZMod p] U)⁻¹ * (b : U ≃ₗ[ZMod p] U) = 1 := by
    refine eq_one_of_sub_mem_centralizerSpace hHF hHs (H.mul_mem (H.inv_mem a.2) b.2) ?_
    intro v hv
    have hbva : (b : U ≃ₗ[ZMod p] U) v - (a : U ≃ₗ[ZMod p] U) v ∈ centralizerSpace F := by
      simpa only [neg_sub] using (centralizerSpace F).neg_mem (hpt v hv)
    have hmem : (a : U ≃ₗ[ZMod p] U)⁻¹
        ((b : U ≃ₗ[ZMod p] U) v - (a : U ≃ₗ[ZMod p] U) v) ∈ centralizerSpace F :=
      subquotHomF_Vc_inv F (a : U ≃ₗ[ZMod p] U)⁻¹ (F.inv_mem (hHF a.2)) _ hbva
    have heq : ((a : U ≃ₗ[ZMod p] U)⁻¹ * (b : U ≃ₗ[ZMod p] U)) v - v =
        (a : U ≃ₗ[ZMod p] U)⁻¹
          ((b : U ≃ₗ[ZMod p] U) v - (a : U ≃ₗ[ZMod p] U) v) := by
      simp [LinearEquiv.mul_apply]
    rw [heq]; exact hmem
  exact Subtype.ext (inv_mul_eq_one.mp h1)

private theorem subquot_dLarge (hp : p ≠ 2) {l : ℕ} {F H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hHF : H ≤ F) (hHs : SplitSupport H l)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    ∃ x ∈ (subquotHomF F).range, ∃ y ∈ (subquotHomF F).range,
      IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
  obtain ⟨x, hxH, y, hyH, hxr, hyr, hxy⟩ := hd
  let xH : H := ⟨x, hxH⟩
  let yH : H := ⟨y, hyH⟩
  let xF : F := Subgroup.inclusion hHF xH
  let yF : F := Subgroup.inclusion hHF yH
  have hψinj := subquotHom_injective_on (l := l) hHF hHs
  refine ⟨(subquotHomF F) xF, ⟨xF, rfl⟩, (subquotHomF F) yF, ⟨yF, rfl⟩, ?_, ?_, ?_⟩
  · exact isRefl_subquotHom hp (subquotHomF_inv₁ F) (subquotHomF_inv₂ F)
      (subquotHomF_triv F) (subquotHomF_sub F) (t := xF) (by simpa [xF, xH] using hxr)
  · exact isRefl_subquotHom hp (subquotHomF_inv₁ F) (subquotHomF_inv₂ F)
      (subquotHomF_triv F) (subquotHomF_sub F) (t := yF) (by simpa [yF, yH] using hyr)
  · have hcomp : ((subquotHomF F).comp (Subgroup.inclusion hHF)) (xH * yH) =
        (subquotHomF F) (xF * yF) := rfl
    rw [show (subquotHomF F) xF * (subquotHomF F) yF = (subquotHomF F) (xF * yF) from
          (map_mul (subquotHomF F) xF yF).symm,
        ← hcomp, orderOf_injective ((subquotHomF F).comp (Subgroup.inclusion hHF)) hψinj]
    rwa [← orderOf_injective H.subtype Subtype.coe_injective (xH * yH)]

private theorem subquot_finrank_eq [Module.Finite (ZMod p) U] {l : ℕ}
    {F H F₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hl : 2 ≤ l) (hHF : H ≤ F) (hHs : SplitSupport H l)
    (hVF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1)
    (hF₁F : F₁ ≤ F)
    (hlift : ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F)
    (hle : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F₁) ≤ l) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F₁) = l := by
  have hle' : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) ≤
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F₁) + 1 := by
    refine (Submodule.finrank_mono
      (commutatorSpace_le_sup_of_lift hl hHF hHs hVF hW hF₁F hlift)).trans ?_
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (HardMathSupport.Kantor79.commutatorSpace F₁)
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
    rw [hW] at h
    omega
  have hb : l + 1 ≤ Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace F₁) + 1 := by
    rw [← hVF]; exact hle'
  omega

private theorem subquot_lift_of_neg [Module.Finite (ZMod p) U] {l : ℕ}
    (hp : p ≠ 2) {F H : Subgroup (U ≃ₗ[ZMod p] U)} (hl : 2 ≤ l) (hF : ReflGen p F) (hHF : H ≤ F)
    (hHs : SplitSupport H l)
    (hVF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1)
    (hnegJ : (LinearEquiv.neg (ZMod p) : Subquot (Wof F) (VFof F) ≃ₗ[ZMod p]
      Subquot (Wof F) (VFof F)) ∈ (subquotHomF F).range) :
    ∃ F₁ : Subgroup (U ≃ₗ[ZMod p] U), F₁ ≤ F ∧ ReflGen p F₁ ∧
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F₁) = l ∧
      ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
        f v - f₁ v ∈ centralizerSpace F := by
  obtain ⟨t, ht⟩ := hnegJ
  have hneg : ∃ z ∈ F, ∀ v ∈ VFof F, z v + v ∈ centralizerSpace F := by
    refine ⟨(t : U ≃ₗ[ZMod p] U), t.2, ?_⟩
    intro v hv
    exact subquotHomF_W_le_centralizer F
      ((subquotEquiv_eq_neg_iff (subquotHomF_inv₁ F t t.2) (subquotHomF_inv₂ F t t.2)).mp ht v hv)
  obtain ⟨F₁, hF₁F, hF₁gen, hF₁le, hlift⟩ := exists_reflGen_lift_of_neg hp hF hVF hW hneg
  exact ⟨F₁, hF₁F, hF₁gen, subquot_finrank_eq hl hHF hHs hVF hW hF₁F hlift hF₁le, hlift⟩

private theorem subquot_closure_reflGen {ι : Type} (y : ι → U ≃ₗ[ZMod p] U)
    (hy : ∀ i, IsRefl p (y i)) : ReflGen p (Subgroup.closure (Set.range y)) := by
  unfold ReflGen
  refine le_antisymm ?_ ?_
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨i, rfl⟩, hy i⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro t ⟨ht, _⟩
    exact ht

private theorem subquot_finset_hlift {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {s : Finset (Subquot (Wof F) (VFof F) ≃ₗ[ZMod p] Subquot (Wof F) (VFof F))}
    (hJclos : (subquotHomF F).range = Subgroup.closure
      (s : Set (Subquot (Wof F) (VFof F) ≃ₗ[ZMod p] Subquot (Wof F) (VFof F))))
    (y : s → F) (hy : ∀ x : s, IsRefl p (y x : U ≃ₗ[ZMod p] U) ∧
      (subquotHomF F) (y x) = (x : Subquot (Wof F) (VFof F) ≃ₗ[ZMod p] Subquot (Wof F) (VFof F)))
    (F₁ : Subgroup (U ≃ₗ[ZMod p] U)) (hF₁F : F₁ ≤ F)
    (hF₁eq : F₁ = Subgroup.closure (Set.range fun x : s => (y x : U ≃ₗ[ZMod p] U)))
    (hiff : ∀ {f g : U ≃ₗ[ZMod p] U} (hf : f ∈ F) (hg : g ∈ F),
      (subquotHomF F) ⟨f, hf⟩ = (subquotHomF F) ⟨g, hg⟩ ↔
        ∀ v ∈ VFof F, f v - g v ∈ centralizerSpace F) :
    ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
      f v - f₁ v ∈ centralizerSpace F := by
  intro f hf
  have hJ₁ : ((subquotHomF F).comp (Subgroup.inclusion hF₁F)).range = (subquotHomF F).range := by
    apply le_antisymm
    · rintro z ⟨g, rfl⟩
      exact ⟨Subgroup.inclusion hF₁F g, rfl⟩
    · rw [hJclos]
      refine (Subgroup.closure_le _).mpr ?_
      rintro x hx
      have hyF₁ : (y ⟨x, hx⟩ : U ≃ₗ[ZMod p] U) ∈ F₁ := by
        rw [hF₁eq]
        exact Subgroup.subset_closure (show (y ⟨x, hx⟩ : U ≃ₗ[ZMod p] U) ∈
          Set.range (fun i : s => (y i : U ≃ₗ[ZMod p] U)) from ⟨⟨x, hx⟩, rfl⟩)
      exact ⟨⟨y ⟨x, hx⟩, hyF₁⟩, (hy ⟨x, hx⟩).2⟩
  obtain ⟨g₁, hg₁⟩ := show (subquotHomF F) ⟨f, hf⟩ ∈
      ((subquotHomF F).comp (Subgroup.inclusion hF₁F)).range by
    rw [hJ₁]; exact ⟨⟨f, hf⟩, rfl⟩
  refine ⟨(g₁ : U ≃ₗ[ZMod p] U), g₁.2, ?_⟩
  intro v hv
  have hpt : (g₁ : U ≃ₗ[ZMod p] U) v - f v ∈ centralizerSpace F :=
    (hiff (f := (g₁ : U ≃ₗ[ZMod p] U)) (g := f) (hF₁F g₁.2) hf).mp hg₁ v hv
  simpa only [neg_sub] using (centralizerSpace F).neg_mem hpt

private theorem subquot_finset_exists {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {s : Finset (Subquot (Wof F) (VFof F) ≃ₗ[ZMod p] Subquot (Wof F) (VFof F))}
    (hp : p ≠ 2) (hsrefl : ∀ x ∈ s, x ∈ (subquotHomF F).range ∧ IsRefl p x) :
    ∀ x : s, ∃ t : F, IsRefl p (t : U ≃ₗ[ZMod p] U) ∧
      (subquotHomF F) t = (x : Subquot (Wof F) (VFof F) ≃ₗ[ZMod p] Subquot (Wof F) (VFof F)) := by
  intro x
  obtain ⟨hxJ, hxr⟩ := hsrefl x x.2
  obtain ⟨g, hg⟩ := hxJ
  obtain ⟨t, htr, htφ⟩ := exists_isRefl_subquotHom_eq hp (subquotHomF_inv₁ F) (subquotHomF_inv₂ F)
    (subquotHomF_triv F) (subquotHomF_sub F) (g := g)
    (by show IsRefl p ((subquotHomF F) g); rw [hg]; exact hxr)
  exact ⟨t, htr, htφ.trans hg⟩

private theorem subquot_lift_of_finset [Module.Finite (ZMod p) U] {l : ℕ}
    (hp : p ≠ 2) {F H : Subgroup (U ≃ₗ[ZMod p] U)} (hl : 2 ≤ l) (hHF : H ≤ F)
    (hHs : SplitSupport H l)
    (hVF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1)
    {s : Finset (Subquot (Wof F) (VFof F) ≃ₗ[ZMod p] Subquot (Wof F) (VFof F))}
    (hscard : s.card ≤ l)
    (hJclos : (subquotHomF F).range = Subgroup.closure
      (s : Set (Subquot (Wof F) (VFof F) ≃ₗ[ZMod p] Subquot (Wof F) (VFof F))))
    (hsrefl : ∀ x ∈ s, x ∈ (subquotHomF F).range ∧ IsRefl p x)
    (hiff : ∀ {f g : U ≃ₗ[ZMod p] U} (hf : f ∈ F) (hg : g ∈ F),
      (subquotHomF F) ⟨f, hf⟩ = (subquotHomF F) ⟨g, hg⟩ ↔
        ∀ v ∈ VFof F, f v - g v ∈ centralizerSpace F) :
    ∃ F₁ : Subgroup (U ≃ₗ[ZMod p] U), F₁ ≤ F ∧ ReflGen p F₁ ∧
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F₁) = l ∧
      ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
        f v - f₁ v ∈ centralizerSpace F := by
  choose y hy using subquot_finset_exists (F := F) hp hsrefl
  let F₁ : Subgroup (U ≃ₗ[ZMod p] U) :=
    Subgroup.closure (Set.range fun x : s => (y x : U ≃ₗ[ZMod p] U))
  have hF₁eq : F₁ = Subgroup.closure (Set.range fun x : s => (y x : U ≃ₗ[ZMod p] U)) := rfl
  have hF₁F : F₁ ≤ F := by
    rw [hF₁eq]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, rfl⟩
    exact (y x).2
  have hF₁gen : ReflGen p F₁ := by
    rw [hF₁eq]; exact subquot_closure_reflGen _ (fun x => (hy x).1)
  have hF₁fin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F₁) ≤ l := by
    rw [hF₁eq]
    exact (finrank_commutatorSpace_closure_le_card _ _ (fun x => (hy x).1)).trans hscard
  have hlift := subquot_finset_hlift hJclos y hy F₁ hF₁F hF₁eq hiff
  exact ⟨F₁, hF₁F, hF₁gen, subquot_finrank_eq hl hHF hHs hVF hW hF₁F hlift hF₁fin, hlift⟩

theorem exists_reflGen_lift (hp : p ≠ 2) [Module.Finite (ZMod p) U] {l : ℕ}
    (htab : TFNegOrGen p l) {F H : Subgroup (U ≃ₗ[ZMod p] U)} (hF : ReflGen p F) (hHF : H ≤ F)
    (hHs : SplitSupport H l)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hVF : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1)
    (hW : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1) :
    ∃ F₁ : Subgroup (U ≃ₗ[ZMod p] U), F₁ ≤ F ∧ ReflGen p F₁ ∧
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F₁) = l ∧
      ∀ f ∈ F, ∃ f₁ ∈ F₁, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
        f v - f₁ v ∈ centralizerSpace F := by
  have hl : 2 ≤ l := two_le_of_splitSupport_dLarge hHs hd
  have hiff : ∀ {f g : U ≃ₗ[ZMod p] U} (hf : f ∈ F) (hg : g ∈ F),
      (subquotHomF F) ⟨f, hf⟩ = (subquotHomF F) ⟨g, hg⟩ ↔
        ∀ v ∈ VFof F, f v - g v ∈ centralizerSpace F :=
    fun hf hg => subquotHom_eq_iff (subquotHomF_W_le_centralizer F) (subquotHomF_W_mem F)
      (subquotHomF_W_inv F) (subquotHomF_VF_inv F) (subquotHomF_inv₁ F) (subquotHomF_inv₂ F) hf hg
  have hJrefl : ReflGen p (subquotHomF F).range := subquot_range_reflGen hp hF
  have hfinJ : Module.finrank (ZMod p) (Subquot (Wof F) (VFof F)) = l := subquot_finrank hVF hW
  have hirrJ := subquot_irreducible hHF hHs hVF hW
  have hdJ := subquot_dLarge hp hHF hHs hd
  by_cases ht : ∃ t ∈ (subquotHomF F).range, QTwoLin.IsTransvectionLin t
  · exact subquot_lift_of_neg hp hl hF hHF hHs hVF hW
      (neg_mem_of_transvection_mem hp hJrefl hirrJ ht)
  · push Not at ht
    rcases htab (Subquot (Wof F) (VFof F)) (subquotHomF F).range hfinJ hJrefl ht hirrJ hdJ with
      hnegJ | ⟨s, hscard, hsrefl, hJclos⟩
    · exact subquot_lift_of_neg hp hl hF hHF hHs hVF hW hnegJ
    · exact subquot_lift_of_finset hp hl hHF hHs hVF hW hscard hJclos hsrefl hiff

end CFSG.StandardType.ZS


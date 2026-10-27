module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepRank
public import CFSG.LocalAnalysis.StandardType.GGDepEDim6
public import CFSG.Monster.B.Geometry.InitialIsometryParabolic
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
public import CFSG.LocalAnalysis.StandardType.GGResE6DepRecognition
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLKnown
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLData
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLPhiAct
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLNormalizes
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepNine
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge
public import CFSG.LocalAnalysis.StandardType.GGDepED4LowModel
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepFrame
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl
public import CFSG.LocalAnalysis.StandardType.GGE6DepFrameCentral
public import CFSG.LocalAnalysis.StandardType.GGTPJLabel
public import CFSG.LocalAnalysis.StandardType.GGTPJLayerHolds
public import CFSG.LocalAnalysis.StandardType.GGSpFrameConfig

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGReflCentre.of_span_ggLinMove
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {r : MulAut Bs} {c : Bs}
    (h : ggLinMove (ggLin (p := p) ι r) ≤ Submodule.span (ZMod p) {ι (Additive.ofMul c)}) :
    GGReflCentre r c := by
  intro b
  have hb : ((r b * b⁻¹ : Bs) : G) ∈ Subgroup.zpowers (c : G) := by
    apply (ofMul_mem_ggLinImage (p := p) ι (Subgroup.zpowers (c : G)) (r b * b⁻¹)).mp
    rw [← ggLin_apply_ofMul_sub (p := p), ← span_singleton_eq_ggLinImage (p := p) ι c.2]
    exact h ⟨ι (Additive.ofMul b), rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩

theorem GGReflCentre.ggLinMove_le_span
    {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {r : MulAut Bs} {c : Bs} (h : GGReflCentre r c) :
    ggLinMove (ggLin (p := p) ι r) ≤ Submodule.span (ZMod p) {ι (Additive.ofMul c)} := by
  rintro z ⟨v, rfl⟩
  obtain ⟨b, rfl⟩ := (Additive.ofMul.trans ι.toEquiv).surjective v
  change ggLin (p := p) ι r (ι (Additive.ofMul b)) - ι (Additive.ofMul b) ∈ _
  rw [ggLin_apply_ofMul_sub, span_singleton_eq_ggLinImage (p := p) ι c.2,
    ofMul_mem_ggLinImage]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h b)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg (fun d : Bs => (d : G)) hk⟩

theorem GGReflCentre.conj
    {G : Type} [Group G] {Bs : Subgroup G} {r : MulAut Bs} {c : Bs}
    (h : GGReflCentre r c) (ψ : MulAut Bs) : GGReflCentre (ψ * r * ψ⁻¹) (ψ c) := by
  intro b
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h (ψ⁻¹ b))
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg ψ hk⟩

private theorem depEL_deleted_one_kernel (v : GGDepAE 3 6) (hv : v 5 = 0)
    (h : ∀ i : Fin 6, i ≠ 1 → ggDepAdot (ggDepELα i) v = 0) :
    v = v 0 • (![1, 1, 2, 0, 0, 0] : GGDepAE 3 6) := by
  revert v
  decide +kernel

private def depEL_highest_word : List (Fin 6) := [1, 3, 4, 5, 2, 3, 4, 0, 2, 3, 1]

private theorem depEL_highest_word_apply :
    ((depEL_highest_word.map fun i => ggDepARefl (ggDepELh i) (ggDepELα i)).prod)
      (ggDepELh 1) = (![1, 1, 2, 0, 0, 0] : GGDepAE 3 6) := by
  ext i
  fin_cases i <;> decide +kernel

theorem GGDepEFrame.corootPt_of_deleted_one
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) {r : Fin 6 → MulAut Bs} {h : Fin 6 → V}
    {α : Fin 6 → Module.Dual (ZMod 3) V} {x : V}
    (F : GGDepEFrame 3 h α x) (hdim : Module.finrank (ZMod 3) V = 6)
    (hlin : ∀ i v, ggLin (p := 3) ι (r i) v = v - α i v • h i)
    (hr : ∀ i, r i ∈ ggAutomizer L Bs) (hrefl : GGIsReflection 3 (r 1))
    (hhL : ∀ i, h i ∈ ggLinImage (p := 3) ι L) (hxL : x ∉ ggLinImage (p := 3) ι L)
    {c : Bs} (hcL : (c : G) ∈ L) (hc1 : c ≠ 1)
    (hcfix : ∀ i : Fin 6, i ≠ 1 → α i (ι (Additive.ofMul c)) = 0) :
    GGCorootPt 3 (ggAutomizer L Bs) c := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨θ, hθh, hθα, hθx⟩ := ggDepELModel_iso F hdim
  let H := Submodule.span (ZMod 3) (Set.range h)
  have hHL : H ≤ ggLinImage (p := 3) ι L :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hhL i)
  have hLtop : ggLinImage (p := 3) ι L ≠ ⊤ := by
    intro heq
    exact hxL (heq ▸ Submodule.mem_top)
  have hfrL : Module.finrank (ZMod 3) (ggLinImage (p := 3) ι L) < 6 := by
    simpa only [hdim] using Submodule.finrank_lt hLtop
  have hHeq : H = ggLinImage (p := 3) ι L :=
    Submodule.eq_of_le_of_finrank_le hHL (by
      have hfrH := (ggDepE_relation F).2.2
      change Module.finrank (ZMod 3) H = 5 at hfrH
      omega)
  have hcH : ι (Additive.ofMul c) ∈ H := by
    rw [hHeq]
    exact (ofMul_mem_ggLinImage (p := 3) ι L c).mpr hcL
  have hHfive : H ≤ ((LinearMap.proj (5 : Fin 6)).comp θ.toLinearMap).ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    change θ (h i) 5 = 0
    rw [hθh]
    fin_cases i <;> rfl
  have hc5 : θ (ι (Additive.ofMul c)) 5 = 0 := hHfive hcH
  have hcmodel := depEL_deleted_one_kernel (θ (ι (Additive.ofMul c))) hc5
    (fun i hi => (hθα i _).symm.trans (hcfix i hi))
  have hscalar : θ (ι (Additive.ofMul c)) 0 ≠ 0 := by
    intro hzero
    rw [hzero, zero_smul] at hcmodel
    have hc0 := θ.injective (hcmodel.trans (map_zero θ).symm)
    exact hc1 (Additive.ofMul.injective (ι.injective (hc0.trans (map_zero ι).symm)))
  let w : MulAut Bs := (depEL_highest_word.map r).prod
  have hw : w ∈ ggAutomizer L Bs := by
    apply Subgroup.list_prod_mem
    intro t ht
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
    exact hr i
  have hθr : ∀ i v, θ (ggLin (p := 3) ι (r i) v) =
      ggDepARefl (ggDepELh i) (ggDepELα i) (θ v) := by
    intro i v
    rw [hlin, map_sub, map_smul, hθh, hθα]
    rfl
  have hθword : ∀ (l : List (Fin 6)) v,
      θ (ggLin (p := 3) ι ((l.map r).prod) v) =
      ((l.map fun i => ggDepARefl (ggDepELh i) (ggDepELα i)).prod) (θ v) := by
    intro l
    induction l with
    | nil => intro v; simp
    | cons i l ih =>
        intro v
        simp only [List.map_cons, List.prod_cons, map_mul, LinearEquiv.mul_apply,
          Module.End.mul_apply]
        rw [hθr, ih]
  let c₀ : Bs := Additive.toMul (ι.symm (h 1))
  have hc₀ : ι (Additive.ofMul c₀) = h 1 := by simp [c₀]
  have hc₀centre : GGReflCentre (r 1) c₀ := by
    apply GGReflCentre.of_span_ggLinMove (p := 3) ι
    rw [hc₀]
    rintro z ⟨v, rfl⟩
    change ggLin (p := 3) ι (r 1) v - v ∈ _
    rw [hlin]
    have heq : v - α 1 v • h 1 - v = -(α 1 v • h 1) := by abel
    rw [heq]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self (h 1)))
  have hwc₀ : θ (ι (Additive.ofMul (w c₀))) = (![1, 1, 2, 0, 0, 0] : GGDepAE 3 6) := by
    rw [← ggLin_apply_ofMul (p := 3), hc₀, hθword, hθh]
    exact depEL_highest_word_apply
  have hcv : ι (Additive.ofMul c) =
      θ (ι (Additive.ofMul c)) 0 • ι (Additive.ofMul (w c₀)) := by
    apply θ.injective
    rw [map_smul, hwc₀]
    exact hcmodel
  have hspan : Submodule.span (ZMod 3) {ι (Additive.ofMul (w c₀))} =
      Submodule.span (ZMod 3) {ι (Additive.ofMul c)} := by
    rw [hcv]
    exact (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hscalar) _).symm
  refine ⟨hc1, w * r 1 * w⁻¹,
    (ggAutomizer L Bs).mul_mem ((ggAutomizer L Bs).mul_mem hw (hr 1))
      ((ggAutomizer L Bs).inv_mem hw), hrefl.conj w, ?_⟩
  apply GGReflCentre.of_span_ggLinMove (p := 3) ι
  rw [← hspan]
  exact (hc₀centre.conj w).ggLinMove_le_span ι

theorem GGResE6DepShape.deleted_one
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hS : GGResE6DepShape p Bs L J K) :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b : Λ) (ML : CoxeterMatrix Λ)
      (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
      (e : Fin 6 ≃ Λ),
      e 1 = b ∧ ML = CoxeterMatrix.E₆.reindex e ∧
      (∀ i j, α (e i) (h (e j)) = (CartanMatrix.E 6 i j : ZMod p)) ∧
      (∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∃ fL : ML.Group ≃* ↥(ggAutomizer L Bs), ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range φ) ∧
      ggAutomizer J Bs = Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ j) ∧
      ∃ hx : x ∈ Bs, GGDepEFrame p (fun i => h (e i)) (fun i => α (e i))
        (ι (Additive.ofMul (⟨x, hx⟩ : Bs))) := by
  have hp3 : p = 3 := hS.1
  subst hp3
  obtain ⟨Λ, _, _, b, ML, CL, MK, CK, V, _, _, ι, φ, h, α,
    hWL, hCL, hWK, hCK, htyp, hlin, hrefl, hPairL, hPairK, hsel, hFL, hFK,
    hAL, hAK, hdel, hAJ⟩ := hS.2.2
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hcardV : Nat.card V = 3 ^ 6 := (card_eq_of_ggLin ι).symm.trans hS.2.1
  have hdim : Module.finrank (ZMod 3) V = 6 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod, hcardV] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  obtain ⟨e, hbe, hML, hCartan, F⟩ := ggDepE_frame_of_config_of_dim_six rfl hH hx hdim
    hCL htyp.1 hdel hlin hPairL hsel hAL
  have hαL : ∀ c : Λ, α (some c) (h (some c)) = 2 := by
    intro c
    rw [hPairL c c, hCL.1 c]
    norm_num
  obtain ⟨y', hyx, hyα⟩ := ggDepA_y_fixed (by norm_num : (3 : ℕ) ≠ 2) hH hx hlin hαL hAJ
  have hb : e.symm b = 1 := ggDepE_dim6_pos F hdim _ hbe
    ⟨y', hyx, fun c hc => hyα (e c) (fun hec => hc (by rw [← hec, Equiv.symm_apply_apply]))⟩
  exact ⟨Λ, inferInstance, inferInstance, b, ML, V, inferInstance, inferInstance, ι,
    (fun i => φ (some i)), (fun i => h (some i)), (fun i => α (some i)), e,
    (by rw [← hb, Equiv.apply_symm_apply]), hML,
    (fun i j => (hPairL _ _).trans (congrArg (fun z : ℤ => (z : ZMod 3)) (hCartan i j))),
    (fun i => hlin (some i)), (fun i => hrefl (some i)), hFL, hAL, hAJ, hx, F⟩

section Certs

theorem GGResE6DepShape.x_not_mem_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hS : GGResE6DepShape p Bs L J K) : x ∉ L := by
  have hp3 : p = 3 := hS.1
  subst hp3
  intro hxL
  have hMark := hS.e6_marking hH (Or.inl rfl)
  have hMarkL : LargeEvenMarking L (fun lab _ _ _ _ _ => GGE6DepLabel lab) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hMark
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  obtain ⟨hN, R, _, I, ψ, Φ, T, w, hTB, hcard, hZ, hmodel, hcob⟩ :=
    ggE6Dep_known_data_zl_of_marking hRig ggE6DepZLKnown_holds hH.1 hH.2.2.1.1
      rfl hS.2.1 hMarkL
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hxc : (⟨x, hxL⟩ : L) ∈ ψ.ker := hZ (by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (hH.1.data_L.1 l l.2))
  have hxord : orderOf (⟨x, hxL⟩ : L) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hH.1.orderOf_x
  have hwN := E6Dep.ZL.ggE6Dep_zl_weyl_normalizes hH.1 hN hmodel
  have hxCob := E6Dep.ZL.phiB_cobdry hN hwN hx hxL (hcob ⟨x, hxL⟩ hxc hxord)
  obtain ⟨Λ, _, _, b, ML, CL, MK, CK, V, _, _, ι, φ, h, α,
    hWL, hCL, hWK, hCK, htyp, hlin, hrefl, hPairL, hPairK, hsel, hFL, hFK,
    hAL, hAK, hdel, hAJ⟩ := hS.2.2
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hcardV : Nat.card V = 3 ^ 6 := (card_eq_of_ggLin ι).symm.trans hS.2.1
  have hdim : Module.finrank (ZMod 3) V = 6 := by
    have h' := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod, hcardV] at h'
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h').symm
  obtain ⟨e, _, _, _, F⟩ := ggDepE_frame_of_config_of_dim_six rfl hH hx hdim
    hCL htyp.1 hdel hlin hPairL hsel hAL
  have hxnot := (ggDepE_relation F).2.1
  let H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range fun i : Λ => h (some i))
  have hsub : AddSubgroup.closure
      {u | ∃ (i : Fin 6) (v : Additive ↥Bs),
        u = Additive.ofMul (ggConjAut Bs (hwN i) (Additive.toMul v)) - v} ≤
      H.toAddSubgroup.comap ι.toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).mpr ?_
    rintro u ⟨i, v, rfl⟩
    change ι (Additive.ofMul (ggConjAut Bs (hwN i) (Additive.toMul v)) - v) ∈ H
    rw [map_sub]
    have hi := ggAutomizer_sub_mem_span (fun i => hlin (some i)) hAL
      (ggConjAut_mem_ggAutomizer (w i).2 (hwN i)) (ι v)
    rw [ggLin_apply, AddEquiv.symm_apply_apply] at hi
    exact hi
  have hxH : ι (Additive.ofMul (⟨x, hx⟩ : Bs)) ∈ H := hsub hxCob
  have hRange : Set.range (fun i : Fin 6 => h (some (e i))) =
      Set.range (fun i : Λ => h (some i)) := e.surjective.range_comp (fun i : Λ => h (some i))
  rw [hRange] at hxnot
  exact hxnot hxH

theorem GGResE6DepShape.exists_coroot_fixed_component
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hS : GGResE6DepShape p Bs L J K) :
    ∃ c : Bs, (c : G) ∈ L ∧ GGCorootPt p (ggAutomizer L Bs) c ∧
      IsComponentOf J (L ⊓ Subgroup.centralizer ({(c : G)} : Set G)) := by
  have hp3 : p = 3 := hS.1
  subst hp3
  have hMark := hS.e6_marking hH (Or.inl rfl)
  have hMarkL : LargeEvenMarking L (fun lab _ _ _ _ _ => GGE6DepLabel lab) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hMark
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  obtain ⟨hN, R, _, I, ψ, Φ, T, w, hTB, hcard, _, hmodel, _⟩ :=
    ggE6Dep_known_data_zl_of_marking hRig ggE6DepZLKnown_holds hH.1 hH.2.2.1.1
      rfl hS.2.1 hMarkL
  have hBsL := ggE6Dep_hBsL hH.1 rfl hN hcard ⟨Φ, T, w, hmodel⟩
  obtain ⟨hy, _, hyD, hyx, _⟩ := GGNbr.facts hH.1 hH.2.2.2.2.1
  obtain ⟨l, hlL, k, hyEq⟩ := hBsL y hy
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  let c : Bs := ⟨y * (x ^ k)⁻¹, Bs.mul_mem hy (Bs.inv_mem (Bs.pow_mem hx k))⟩
  have hcL : (c : G) ∈ L := by
    change y * (x ^ k)⁻¹ ∈ L
    rw [hyEq, mul_inv_cancel_right]
    exact hlL
  have hc1 : c ≠ 1 := by
    intro heq
    have hyPow : y = x ^ k := mul_inv_eq_one.mp (congrArg (fun b : Bs => (b : G)) heq)
    exact hyx (hyPow ▸ Subgroup.npow_mem_zpowers x k)
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  have hcent : L ⊓ Subgroup.centralizer ({(c : G)} : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hg, hgc⟩
      have hgx : Commute g (x ^ k) :=
        (show Commute g x from Subgroup.mem_centralizer_singleton_iff.mp (hLx hg)).pow_right k
      have hyc : y = (c : G) * x ^ k := by dsimp [c]; group
      refine ⟨hg, ?_⟩
      rw [hyc]
      exact (show Commute g (c : G) from hgc).mul_right hgx
    · rintro ⟨hg, hgy⟩
      have hgx : Commute g (x ^ k) :=
        (show Commute g x from Subgroup.mem_centralizer_singleton_iff.mp (hLx hg)).pow_right k
      exact ⟨hg, (show Commute g y from hgy).mul_right hgx.inv_right⟩
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hH.1.2.2.1.2.2.2.2.2.1
  have hD : D = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [hH.2.2.2.2.1.2.1, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, Set.singleton_union]
  rw [hD, inf_centralizer_sup_zpowers hLx, ← hcent] at hJcomp
  obtain ⟨Λ, _, _, b, ML, V, _, _, ι, φ, h, α, e, hb, _, hPair, hLin, hRefl,
    _, hAL, hAJ, hx', F⟩ := hS.deleted_one hH
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 3) V = 6 := by
    have hcardV : Nat.card V = 3 ^ 6 := (card_eq_of_ggLin ι).symm.trans hS.2.1
    have hpow := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod, hcardV] at hpow
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow).symm
  have hgen : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Fin 6 => φ (e i)) := by
    have hRange : Set.range (fun i : Fin 6 => φ (e i)) = Set.range φ :=
      e.surjective.range_comp φ
    rw [hRange, hAL]
  have hr : ∀ i : Fin 6, φ (e i) ∈ ggAutomizer L Bs := by
    intro i
    rw [hAL]
    exact Subgroup.subset_closure (Set.mem_range_self (e i))
  have hhL : ∀ i : Fin 6, h (e i) ∈ ggLinImage (p := 3) ι L := by
    intro i
    exact (mem_ggLinImage (p := 3) ι L _).mpr
      (l05nTC_h_mem_L (by norm_num) hH ggIntCartan_E₆
        (fun i => hLin (e i)) F.pair hgen i)
  have hxnot : ι (Additive.ofMul (⟨x, hx'⟩ : Bs)) ∉ ggLinImage (p := 3) ι L := by
    rw [ofMul_mem_ggLinImage]
    exact hS.x_not_mem_L hH
  have hcfix : ∀ i : Fin 6, i ≠ 1 → α (e i) (ι (Additive.ofMul c)) = 0 := by
    intro i hi
    have hie : e i ≠ b := by rw [← hb]; exact fun heq => hi (e.injective heq)
    have hriJ : φ (e i) ∈ ggAutomizer J Bs := by
      rw [hAJ]
      exact Subgroup.subset_closure
        (Set.mem_range_self (f := fun j : {j : Λ // j ≠ b} => φ j) ⟨e i, hie⟩)
    have hfix := ggAutomizer_apply_eq_of_le_centralizer
      (hJcomp.1.trans inf_le_right) hriJ
    have heq := hLin (e i) (ι (Additive.ofMul c))
    rw [ggLin_apply_ofMul, hfix] at heq
    have hhne : h (e i) ≠ 0 := by
      intro hzero
      have hii := F.pair i i
      rw [hzero, map_zero] at hii
      have hdiag : CartanMatrix.E 6 i i = 2 := by fin_cases i <;> rfl
      rw [hdiag] at hii
      exact (zmod_two_ne_zero (by norm_num : (3 : ℕ) ≠ 2)) hii.symm
    exact (smul_eq_zero.mp (sub_eq_self.mp heq.symm)).resolve_right hhne
  exact ⟨c, hcL, F.corootPt_of_deleted_one ι hdim (fun i => hLin (e i)) hr
    (hRefl (e 1)) hhL hxnot hcL hc1 hcfix, hJcomp⟩

theorem GGResE6DepShape.j_label
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hS : GGResE6DepShape p Bs L J K)
    {labL : LargeEvenLabel} (hL : GGE6DepLabel labL)
    (hmL : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL)) :
    GGHasLabel (ggTPJLabel labL) (J ⧸ Subgroup.center J) ∧
      ¬ 3 ∣ Nat.card (Subgroup.center J) ∧ 3 ∣ Nat.card J := by
  have hp3 : p = 3 := hS.1
  subst hp3
  obtain ⟨c, hcL, hc, hJ⟩ := hS.exists_coroot_fixed_component hH
  exact ggTPJLabel_of_coroot ggLabelRigidInput_holds ggTPJLayerInput_holds hH.1
    hH.2.2.1.1 hS.2.1 (ggE6Dep_hZ hH.1 (hS.x_not_mem_L hH)) hcL hc hJ hL hmL

end Certs

end CFSG.StandardType

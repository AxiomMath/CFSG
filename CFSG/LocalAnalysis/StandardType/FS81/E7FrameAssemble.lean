module

public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameNativeRoots
public import CFSG.LocalAnalysis.StandardType.FS81.ConstructYE7
public import CFSG.ClassicalInvolution.Models.LinearPairs.Pairs
public import CFSG.LieType.Chevalley.LangRootRankOneTorus
public import CFSG.Sporadic.Th.Max3.Core

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.WeakCT
open CFSG.Timmesfeld

variable {G : Type} [Group G] {K : Subgroup G}

abbrev tr (ψ : ↥L7 ≃* ↥K) (X : Subgroup (ModGL .E7 (ZMod 2))) : Subgroup G :=
  (X.subgroupOf L7).map (K.subtype.comp ψ.toMonoidHom)

abbrev pull (ψ : ↥L7 ≃* ↥K) (H : Subgroup G) : Subgroup (ModGL .E7 (ZMod 2)) :=
  (H.comap (K.subtype.comp ψ.toMonoidHom)).map L7.subtype

theorem mem_tr {ψ : ↥L7 ≃* ↥K} {X : Subgroup (ModGL .E7 (ZMod 2))} {x : G} :
    x ∈ tr ψ X ↔ ∃ y : ↥L7, (y : ModGL .E7 (ZMod 2)) ∈ X ∧ ((ψ y : ↥K) : G) = x := by
  simp only [tr, Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_comp,
    Subgroup.coe_subtype, Function.comp_apply, MulEquiv.coe_toMonoidHom]

theorem tr_le_K (ψ : ↥L7 ≃* ↥K) (X : Subgroup (ModGL .E7 (ZMod 2))) : tr ψ X ≤ K := by
  rintro _ ⟨y, -, rfl⟩
  exact (ψ y).2

theorem tr_L7 (ψ : ↥L7 ≃* ↥K) : tr ψ L7 = K := by
  apply le_antisymm (tr_le_K ψ L7)
  intro x hx
  refine mem_tr.mpr ⟨ψ.symm ⟨x, hx⟩, (ψ.symm ⟨x, hx⟩).2, ?_⟩
  rw [MulEquiv.apply_symm_apply]

theorem le_pull_iff (ψ : ↥L7 ≃* ↥K) {X : Subgroup (ModGL .E7 (ZMod 2))} (hX : X ≤ L7)
    (H : Subgroup G) : X ≤ pull ψ H ↔ tr ψ X ≤ H := by
  constructor
  · intro h x hx
    obtain ⟨y, hyX, rfl⟩ := mem_tr.mp hx
    obtain ⟨z, hz, hzy⟩ := h hyX
    have : z = y := Subtype.ext hzy
    subst this
    exact hz
  · intro h y hy
    exact ⟨⟨y, hX hy⟩, h (mem_tr.mpr ⟨⟨y, hX hy⟩, hy, rfl⟩), rfl⟩

theorem tr_commute (ψ : ↥L7 ≃* ↥K) {X Y : Subgroup (ModGL .E7 (ZMod 2))}
    (h : ∀ a ∈ X, ∀ c ∈ Y, a * c = c * a) :
    ∀ a ∈ tr ψ X, ∀ c ∈ tr ψ Y, a * c = c * a := by
  intro a ha c hc
  obtain ⟨y, hyX, rfl⟩ := mem_tr.mp ha
  obtain ⟨z, hzY, rfl⟩ := mem_tr.mp hc
  have hyz : y * z = z * y := Subtype.ext (h _ hyX _ hzY)
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hyz]

theorem tr_pair (ψ : ↥L7 ≃* ↥K) {W X Y : Subgroup (ModGL .E7 (ZMod 2))} (hX : X ≤ L7)
    (hY : Y ≤ L7) (h : LinearBlockStandardPair (ZMod 2) W X Y) :
    ∃ W' : Subgroup G, LinearBlockStandardPair (ZMod 2) W' (tr ψ X) (tr ψ Y) :=
  ⟨_, CFSG.ClassicalInvolution.Models.linearBlockStandardPair_map
    (linearBlockStandardPair_subgroupOf hX hY h) (K.subtype.comp ψ.toMonoidHom)
    (Subtype.val_injective.comp ψ.injective)⟩

theorem pair_conj {W U V : Subgroup G} (h : LinearBlockStandardPair (ZMod 2) W U V) (g : G) :
    LinearBlockStandardPair (ZMod 2) (W.map (MulAut.conj g).toMonoidHom)
      (U.map (MulAut.conj g).toMonoidHom) (V.map (MulAut.conj g).toMonoidHom) :=
  CFSG.ClassicalInvolution.Models.linearBlockStandardPair_map h _ (MulAut.conj g).injective

theorem commute_conj {U V : Subgroup G} (h : ∀ a ∈ U, ∀ c ∈ V, a * c = c * a) (g : G) :
    ∀ a ∈ U.map (MulAut.conj g).toMonoidHom, ∀ c ∈ V.map (MulAut.conj g).toMonoidHom,
      a * c = c * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * a * g⁻¹ * (g * c * g⁻¹) = g * (a * c) * g⁻¹ := by group
    _ = g * (c * a) * g⁻¹ := by rw [h a ha c hc]
    _ = g * c * g⁻¹ * (g * a * g⁻¹) := by group

theorem map_conj_inv_map_conj (X : Subgroup G) (g : G) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = X := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id X
  ext x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, MonoidHom.id_apply]
  group

theorem map_conj_map_conj_inv (X : Subgroup G) (g : G) :
    (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X := by
  simpa using map_conj_inv_map_conj X g⁻¹

section Frame

theorem e7Frame_inv_of_sigma {b₀ : G}
    (ψ : ↥L7 ≃* ↥K) (σ : G) {K₀ : Subgroup G} (hK₀ : K₀ ≤ Subgroup.centralizer (K : Set G))
    (hb₀ : b₀ ∈ K₀)
    (h0 : (tr ψ (Jn 0)).map (MulAut.conj σ).toMonoidHom = K₀)
    (h0' : K₀.map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 0))
    (hM : (tr ψ M0).map (MulAut.conj σ).toMonoidHom = tr ψ M0)
    (h1 : (tr ψ (Jn 1)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 6))
    (h3 : (tr ψ (Jn 3)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 5))
    (h4 : (tr ψ (Jn 4)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 4))
    (h5 : (tr ψ (Jn 5)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 3))
    (h6 : (tr ψ (Jn 6)).map (MulAut.conj σ).toMonoidHom = tr ψ (J mu))
    (h77 : ∀ a ∈ (tr ψ (J theta)).map (MulAut.conj σ⁻¹).toMonoidHom, ∀ c ∈ tr ψ (Jn 2),
      a * c = c * a) :
    ∃ U : Fin 8 → Subgroup G,
      (∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
        ∀ a ∈ U i, ∀ c ∈ U j, a * c = c * a) ∧
      (∀ i j : Fin 8, edgeE 8 i j → ∃ W, LinearBlockStandardPair (ZMod 2) W (U i) (U j)) ∧
      K ≤ ⨆ k, U k ∧ b₀ ∈ ⨆ k, U k ∧ σ⁻¹ * b₀ * σ⁻¹⁻¹ ∈ K ∧
      (∃ (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K) (r : ↥(adjointGroup .E7 (ZMod 2))),
        (r : ModGL .E7 (ZMod 2)) ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) ∧
          ((ψ r : ↥K) : G) = σ⁻¹⁻¹ * b₀ * σ⁻¹) ∧
      ∀ k, U k ≤ K ∨ U k ≤ K.map (MulAut.conj σ⁻¹).toMonoidHom := by
  have hF := e7NatFrame_holds
  have hH := e7NatHigh_holds
  have hW := e7NatWeyl_holds
  obtain ⟨hJL, hcomm, hpair, hgen⟩ := hF
  obtain ⟨hθc, ⟨Wμ, hμθ⟩, hθgen, hθL, -, hμM, -⟩ := hH
  have back : ∀ {X Y : Subgroup G}, X.map (MulAut.conj σ).toMonoidHom = Y →
      X = Y.map (MulAut.conj σ⁻¹).toMonoidHom := fun {X Y} h => by
    rw [← h, map_conj_inv_map_conj]
  obtain ⟨U, hU7, hUi⟩ : ∃ U : Fin 8 → Subgroup G,
      U (Fin.last 7) = (tr ψ (J theta)).map (MulAut.conj σ⁻¹).toMonoidHom ∧
        ∀ i : Fin 7, U i.castSucc = tr ψ (Jn i) :=
    ⟨Fin.lastCases _ fun i : Fin 7 => tr ψ (Jn i), Fin.lastCases_last, Fin.lastCases_castSucc⟩
  have h7comm : ∀ j : Fin 7, j ≠ 6 → ∀ a ∈ U (Fin.last 7), ∀ c ∈ U j.castSucc,
      a * c = c * a := by
    intro j hj
    rw [hU7, hUi]
    have hθK : ∀ {Y : Subgroup G}, (∀ a ∈ tr ψ (J theta), ∀ c ∈ Y, a * c = c * a) →
        tr ψ (Jn j) = Y.map (MulAut.conj σ⁻¹).toMonoidHom →
        ∀ a ∈ (tr ψ (J theta)).map (MulAut.conj σ⁻¹).toMonoidHom, ∀ c ∈ tr ψ (Jn j),
          a * c = c * a := fun {Y} hY he => by
      rw [he]
      exact commute_conj hY σ⁻¹
    fin_cases j
    · exact hθK (fun a ha c hc => Subgroup.mem_centralizer_iff.mp (hK₀ hc) a (tr_le_K ψ _ ha))
        (back h0)
    · exact hθK (tr_commute ψ (hθc 6 (by decide))) (back h1)
    · exact h77
    · exact hθK (tr_commute ψ (hθc 5 (by decide))) (back h3)
    · exact hθK (tr_commute ψ (hθc 4 (by decide))) (back h4)
    · exact hθK (tr_commute ψ (hθc 3 (by decide))) (back h5)
    · exact absurd rfl hj
  have hcomm8 : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
      ∀ a ∈ U i, ∀ c ∈ U j, a * c = c * a := by
    intro i j hij hij' hji'
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j =>
        have hj : j ≠ 6 := by
          rintro rfl
          exact hji' (by decide)
        exact h7comm j hj
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        have hi : i ≠ 6 := by
          rintro rfl
          exact hij' (by decide)
        intro a ha c hc
        exact (h7comm i hi c hc a ha).symm
      | cast j =>
        rw [hUi, hUi]
        exact tr_commute ψ (hcomm i j (fun h => hij (congrArg _ h)) hij' hji')
  have hpair8 : ∀ i j : Fin 8, edgeE 8 i j →
      ∃ W, LinearBlockStandardPair (ZMod 2) W (U i) (U j) := by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      have := j.isLt
      simp only [edgeE, Fin.val_last] at hij
      omega
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        have hi : i = 6 := Fin.ext (by
          simp only [edgeE, Fin.coe_castSucc, Fin.val_last] at hij
          show (i : ℕ) = 6
          omega)
        subst hi
        rw [hUi, hU7, back h6]
        obtain ⟨W, hW⟩ := tr_pair ψ (hμM.trans inf_le_left) hθL hμθ
        exact ⟨_, pair_conj hW σ⁻¹⟩
      | cast j =>
        rw [hUi, hUi]
        obtain ⟨W, hW⟩ := hpair i j hij
        exact tr_pair ψ (hJL i) (hJL j) hW
  have hKU : K ≤ ⨆ k, U k := by
    rw [← tr_L7 ψ, ← le_pull_iff ψ le_rfl]
    apply hgen
    intro i
    rw [le_pull_iff ψ (hJL i), ← hUi i]
    exact le_iSup U i.castSucc
  have hbU : b₀ ∈ ⨆ k, U k := by
    have hMV : tr ψ M0 ≤ (⨆ k, U k).map (MulAut.conj σ).toMonoidHom := by
      rw [← hM]
      exact Subgroup.map_mono ((tr_le_K ψ _).trans hKU)
    have hθV : tr ψ (J theta) ≤ (⨆ k, U k).map (MulAut.conj σ).toMonoidHom := by
      rw [← map_conj_map_conj_inv (tr ψ (J theta)) σ, ← hU7]
      exact Subgroup.map_mono (le_iSup U _)
    have h0V : tr ψ (Jn 0) ≤ (⨆ k, U k).map (MulAut.conj σ).toMonoidHom := by
      rw [← le_pull_iff ψ (hJL 0)]
      apply hθgen
      intro m hm x hx
      have hmL : m ∈ L7 := (Subgroup.mem_inf.mp hm).1
      have hxL : x ∈ L7 := hθL hx
      have hmx : m * x * m⁻¹ ∈ L7 := mul_mem (mul_mem hmL hxL) (inv_mem hmL)
      refine ⟨⟨m * x * m⁻¹, hmx⟩, ?_, rfl⟩
      have e : (⟨m * x * m⁻¹, hmx⟩ : ↥L7) = ⟨m, hmL⟩ * ⟨x, hxL⟩ * (⟨m, hmL⟩ : ↥L7)⁻¹ := rfl
      have hm' := hMV (mem_tr.mpr ⟨⟨m, hmL⟩, hm, rfl⟩)
      have hx' := hθV (mem_tr.mpr ⟨⟨x, hxL⟩, hx, rfl⟩)
      rw [SetLike.mem_coe, Subgroup.mem_comap, e, map_mul, map_mul, map_inv]
      exact mul_mem (mul_mem hm' hx') (inv_mem hm')
    have := Subgroup.map_mono (f := (MulAut.conj σ⁻¹).toMonoidHom) h0V
    rw [map_conj_inv_map_conj, ← back h0'] at this
    exact this hb₀
  have hg : σ⁻¹ * b₀ * σ⁻¹⁻¹ ∈ K := by
    have : K₀.map (MulAut.conj σ⁻¹).toMonoidHom = tr ψ (Jn 0) := by
      rw [← h0, map_conj_inv_map_conj]
    apply tr_le_K ψ (Jn 0)
    rw [← this]
    exact ⟨b₀, hb₀, rfl⟩
  have hroot : ∃ (ψ' : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥K) (r : ↥(adjointGroup .E7 (ZMod 2))),
      (r : ModGL .E7 (ZMod 2)) ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) ∧
        ((ψ' r : ↥K) : G) = σ⁻¹⁻¹ * b₀ * σ⁻¹ := by
    have hJθ : J theta = CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) :=
      (exceptional_Lang_root_rank_one_torus_transport .E7 (ZMod 2)
        (CFSG.SeitzReduction.isRoot_highRoot .E7)).1
    have hb : σ⁻¹⁻¹ * b₀ * σ⁻¹ ∈ tr ψ (Jn 0) := by
      rw [inv_inv, ← h0']
      exact ⟨b₀, hb₀, rfl⟩
    obtain ⟨y, hy, hψy⟩ := mem_tr.mp hb
    obtain ⟨⟨w, hwL, hw⟩, -⟩ := hW
    rw [← hw] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    have hxy' : MulAut.conj (⟨w, hwL⟩ : ↥L7) ⟨x, hθL hx⟩ = y := Subtype.ext hxy
    refine ⟨(MulAut.conj (⟨w, hwL⟩ : ↥L7)).trans ψ, ⟨x, hθL hx⟩, hJθ ▸ hx, ?_⟩
    rw [MulEquiv.trans_apply, hxy', hψy]
  have hcover : ∀ k, U k ≤ K ∨ U k ≤ K.map (MulAut.conj σ⁻¹).toMonoidHom := by
    intro k
    induction k using Fin.lastCases with
    | last =>
      rw [hU7]
      exact Or.inr (Subgroup.map_mono (tr_le_K ψ _))
    | cast i =>
      rw [hUi]
      exact Or.inl (tr_le_K ψ _)
  exact ⟨U, hcomm8, hpair8, hKU, hbU, hg, hroot, hcover⟩

end Frame

end CFSG.StandardType.FrameRoute.FS81.E7Frame

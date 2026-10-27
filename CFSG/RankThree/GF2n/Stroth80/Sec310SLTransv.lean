module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Main
public import CFSG.RankThree.GF2n.Stroth80.Sec310Nat
public import CFSG.RankThree.GF2n.Stroth80.Sec310FC
public import CFSG.RankThree.GF2n.Stroth80.Sec310Count
public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.two_le_finrank_Vt (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) {t : G} (ht : t ∈ LB M Q B)
    (hR : Rt M (LB M Q B) t ≠ LB M Q B) {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    (hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t)) :
    2 ≤ Module.finrank K (imgSub M₀ (Vt M (LB M Q B) B Z t) hS) := by
  classical
  by_contra hlt
  push Not at hlt
  apply hc.not_Rt_le_CN h35 ht hR
  set V := Vt M (LB M Q B) B Z t with hVdef
  obtain ⟨φ₀, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp h
  obtain ⟨b, hb0, -, hB, -, -⟩ := hc.dictB h
  have hbV : b ∈ imgSub M₀ V hS :=
    mem_imgSub.mpr (M₀.img_mono (hc.B_le_Vt ht) ((hB b).mpr ⟨1, (one_smul K b).symm⟩))
  have hone : ∀ w ∈ imgSub M₀ V hS, ∃ s : K, w = s • b := by
    have hbne : (⟨b, hbV⟩ : imgSub M₀ V hS) ≠ 0 := fun h0 => hb0 (congrArg Subtype.val h0)
    have hpos : 0 < Module.finrank K (imgSub M₀ V hS) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hbne⟩
    have hlt' : Module.finrank K (imgSub M₀ V hS) < 2 := hlt
    have h1 : Module.finrank K (imgSub M₀ V hS) = 1 := by omega
    intro w hw
    obtain ⟨s, hs⟩ := (finrank_eq_one_iff_of_nonzero' _ hbne).mp h1 ⟨w, hw⟩
    exact ⟨s, (congrArg Subtype.val hs).symm⟩
  refine iSup₂_le fun m hm => iSup_le fun htm => ?_
  intro l hl
  have hlR : l ∈ Rt M (LB M Q B) t := conjSubgroup_le_Rt hm htm hl
  refine ⟨hlR, fun v hv => ?_⟩
  have hcC : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  have hlLC : l ∈ LB M Q (conjSubgroup m B) := by rw [hc.LB_conj hm]; exact hl
  have hl2 : l ^ 2 ∈ Q := hcC.sq_mem_Q_of_mem_LB hlLC
  have hlH : l ∈ H0 M Z := hc.Rt_le_H0 t hlR
  have hvQ : v ∈ Q := hc.Vt_le_Q t hv
  have hlvQ : l * v * l⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hlH.1).1 v hvQ
  set T := φ₀ ⟨l, hlH⟩ with hTdef
  have hTπ : ∀ x ∈ Q, M₀.π (l * x * l⁻¹) = T (M₀.π x) := fun x hx => hφπ ⟨l, hlH⟩ x hx
  have hlV : l * v * l⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hlR) v).mp hv
  have hTb : T b ∈ imgSub M₀ V hS := by
    obtain ⟨u, huB, huQ, hu⟩ := (hB b).mpr ⟨1, (one_smul K b).symm⟩
    rw [← hu, ← hTπ u huQ]
    refine mem_imgSub.mpr (M₀.pi_mem_img ?_ ((hc.conj_mem_Q_of_mem_M hlH.1).1 u huQ))
    exact (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hlR) u).mp
      (hc.B_le_Vt ht huB)
  have hT2 : ∀ e, T (T e) = e := by
    intro e
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    rw [← hTπ x hxQ, ← hTπ _ ((hc.conj_mem_Q_of_mem_M hlH.1).1 x hxQ)]
    have e1 : l * (l * x * l⁻¹) * l⁻¹ = l ^ 2 * x * (l ^ 2)⁻¹ := by
      rw [pow_two, mul_inv_rev]
      simp only [mul_assoc]
    rw [e1]
    exact Tim79.QuadModel.pi_conj_self (M₀ := M₀) hl2 hxQ
  obtain ⟨s₀, hs₀⟩ := hone _ hTb
  have hs₀sq : s₀ = 1 := by
    have h1 : T (T b) = b := hT2 b
    rw [hs₀, map_smul, hs₀, smul_smul] at h1
    have h2 : (s₀ * s₀ - 1) • b = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    have h3 : s₀ * s₀ - 1 = 0 := by
      rcases smul_eq_zero.mp h2 with h4 | h4
      · exact h4
      · exact absurd h4 hb0
    have h5 : (s₀ - 1) * (s₀ - 1) = 0 := by
      have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h3 + (1 - s₀) * h2K
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h5)
  have hTb' : T b = b := by rw [hs₀, hs₀sq, one_smul]
  obtain ⟨s, hs⟩ := hone _ (mem_imgSub.mpr (M₀.pi_mem_img hv hvQ))
  refine (M₀.comm_mem_iff hvQ hlvQ).mpr ?_
  rw [hTπ v hvQ, hs, map_smul, hTb']


theorem Ctx.natIrred_of_data (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) {t : G} (ht : t ∈ LB M Q B)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (h : GlobalModelData M Q Z γ M₀)
    (hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t))
    {m : ℕ} (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m) K)
    (c : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) ≃ₗ[K] (Fin m → K))
    (hSeq : ∀ (r : ↥(Rt M (LB M Q B) t)) (S : M₀.E ≃ₗ[K] M₀.E),
      (∀ x ∈ Q, M₀.π ((r : G) * x * (r : G)⁻¹) = S (M₀.π x)) →
      ∀ (w : ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS))
        (hw : S (w : M₀.E) ∈ imgSub M₀ (Vt M (LB M Q B) B Z t) hS),
        c ⟨S (w : M₀.E), hw⟩ = (φ r : Matrix (Fin m) (Fin m) K) *ᵥ c w) :
    NatIrred φ.range := by
  classical
  intro S' hS'
  by_cases hbot : S' = ⊥
  · exact Or.inl hbot
  right
  rw [eq_top_iff]
  set V := Vt M (LB M Q B) B Z t with hVdef
  let W' : Submodule K M₀.E := imgSub M₀ V hS
  let ι : (Fin m → K) →ₗ[K] M₀.E := W'.subtype.comp c.symm.toLinearMap
  have hι : Function.Injective ι := fun x y hxy =>
    c.symm.injective (Subtype.ext hxy)
  let Sp : Submodule K M₀.E := S'.map ι
  have hSp0 : Sp ≠ ⊥ := by
    intro h0
    apply hbot
    rw [eq_bot_iff]
    intro x hx
    have : ι x ∈ Sp := ⟨x, hx, rfl⟩
    rw [h0] at this
    have h1 : ι x = 0 := by simpa using this
    have h2 : x = 0 := hι (by rw [h1, map_zero])
    rw [h2]
    exact Submodule.zero_mem _
  have hSp : ∀ l ∈ Rt M (LB M Q B) t, ∀ S : M₀.E ≃ₗ[K] M₀.E,
      (∀ x ∈ Q, M₀.π (l * x * l⁻¹) = S (M₀.π x)) → (∀ e, M₀.Qf (S e) = M₀.Qf e) →
        ∀ v ∈ Sp, S v ∈ Sp := by
    intro l hl S hS0 _ v hv
    obtain ⟨x, hxS, rfl⟩ := hv
    have hlH : l ∈ H0 M Z := hc.Rt_le_H0 t hl
    have hmem : S ((c.symm x : W') : M₀.E) ∈ W' := by
      obtain ⟨u, huV, huQ, hu⟩ := mem_imgSub.mp (c.symm x).2
      rw [← hu, ← hS0 u huQ]
      exact mem_imgSub.mpr (M₀.pi_mem_img
        ((Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hl) u).mp huV)
        ((hc.conj_mem_Q_of_mem_M hlH.1).1 u huQ))
    have h1 := hSeq ⟨l, hl⟩ S hS0 (c.symm x) hmem
    rw [LinearEquiv.apply_symm_apply] at h1
    refine ⟨(φ ⟨l, hl⟩ : Matrix (Fin m) (Fin m) K) *ᵥ x,
      hS' _ ⟨⟨l, hl⟩, rfl⟩ x hxS, ?_⟩
    show ((c.symm ((φ ⟨l, hl⟩ : Matrix (Fin m) (Fin m) K) *ᵥ x) : W') : M₀.E) = _
    rw [← h1, LinearEquiv.symm_apply_apply]
    rfl
  have hall := hc.img_Vt_le_of_invariant h35 h t Sp hSp0 hSp
  intro x _
  have hx : ((c.symm x : W') : M₀.E) ∈ M₀.img V := mem_imgSub.mp (c.symm x).2
  obtain ⟨x', hx'S, hx'⟩ := hall _ hx
  have : x' = x := hι hx'
  rw [← this]
  exact hx'S


theorem Ctx.matrix_elation_data (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B))
    (hcardLB : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1))
    (hcardL : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1))
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (h : GlobalModelData M Q Z γ M₀) {V R : Subgroup G} (hBV : B ≤ V) (hVL : V ≤ Q ⊓ QB B)
    (hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V) (hRH : R ≤ H0 M Z)
    (hRV : R ≤ Subgroup.normalizer (V : Set G)) (hLR : LB M Q B ≤ R) {m : ℕ}
    (φ : ↥R →* GL (Fin m) K) (c : ↥(imgSub M₀ V hS) ≃ₗ[K] (Fin m → K))
    (hSeq : ∀ (r : ↥R) (S : M₀.E ≃ₗ[K] M₀.E),
      (∀ x ∈ Q, M₀.π ((r : G) * x * (r : G)⁻¹) = S (M₀.π x)) →
      ∀ (w : ↥(imgSub M₀ V hS)) (hw : S (w : M₀.E) ∈ imgSub M₀ V hS),
        c ⟨S (w : M₀.E), hw⟩ = (φ r : Matrix (Fin m) (Fin m) K) *ᵥ c w) :
    ∃ (b : M₀.E) (hbV : b ∈ imgSub M₀ V hS), b ≠ 0 ∧ c ⟨b, hbV⟩ ≠ 0 ∧
      (∀ v, v ∈ M₀.img B ↔ ∃ s : K, v = s • b) ∧
      (∀ (l : G) (hl : l ∈ LB M Q B), ∃ f : Fin m → K, f ⬝ᵥ c ⟨b, hbV⟩ = 0 ∧
        (φ ⟨l, hLR hl⟩ : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec (c ⟨b, hbV⟩) f) ∧
      (∀ f : Fin m → K, f ⬝ᵥ c ⟨b, hbV⟩ = 0 → ∃ (l : G) (hl : l ∈ LB M Q B),
        (φ ⟨l, hLR hl⟩ : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec (c ⟨b, hbV⟩) f) ∧
      (∀ T : Subgroup G, (∀ x, x ∈ T ↔ x ∈ LB M Q B ∧ ∀ y ∈ V, ⁅x, y⁆ ∈ Z) →
        Nat.card (LB M Q B) = Nat.card T * Nat.card K ^ (m - 1)) := by
  classical
  obtain ⟨b, hbV, hb0, hBb, hE1, hE2, hE3⟩ :=
    hc.elation_package hw hn hno hcardLB hcardL h hBV hVL hS
  obtain ⟨φ₀, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp h
  let u : Fin m → K := c ⟨b, hbV⟩
  have hu0 : u ≠ 0 := fun h0 => hb0 (congrArg Subtype.val (c.injective (h0.trans c.map_zero.symm)))
  have hSl : ∀ (l : G) (hl : l ∈ LB M Q B), ∀ x ∈ Q,
      M₀.π (l * x * l⁻¹) = φ₀ ⟨l, hc.LB_le_H0 hl⟩ (M₀.π x) := fun l hl x hx =>
    hφπ ⟨l, hc.LB_le_H0 hl⟩ x hx
  have hWV : ∀ (l : G) (hl : l ∈ LB M Q B) (w : M₀.E), w ∈ imgSub M₀ V hS →
      φ₀ ⟨l, hc.LB_le_H0 hl⟩ w ∈ imgSub M₀ V hS := by
    intro l hl w hw
    obtain ⟨v, hvV, hvQ, rfl⟩ := mem_imgSub.mp hw
    rw [← hSl l hl v hvQ]
    refine mem_imgSub.mpr (M₀.pi_mem_img ?_ ((hc.conj_mem_Q_of_mem_M (hc.LB_le_M hl)).1 v hvQ))
    exact (Subgroup.mem_normalizer_iff.mp (hRV (hLR hl)) v).mp hvV
  have hact : ∀ (l : G) (hl : l ∈ LB M Q B) (w : ↥(imgSub M₀ V hS)),
      (φ ⟨l, hLR hl⟩ : Matrix (Fin m) (Fin m) K) *ᵥ c w =
        c ⟨φ₀ ⟨l, hc.LB_le_H0 hl⟩ (w : M₀.E), hWV l hl _ w.2⟩ := fun l hl w =>
    (hSeq ⟨l, hLR hl⟩ (φ₀ ⟨l, hc.LB_le_H0 hl⟩) (hSl l hl) w (hWV l hl _ w.2)).symm
  have hpart1 : ∀ (l : G) (hl : l ∈ LB M Q B), ∃ f : Fin m → K, f ⬝ᵥ u = 0 ∧
      (φ ⟨l, hLR hl⟩ : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec u f := by
    intro l hl
    obtain ⟨hSb, hSe⟩ := hE1 l hl (φ₀ ⟨l, hc.LB_le_H0 hl⟩) (hSl l hl)
    have hA : ∀ x, ∃ s : K, (φ ⟨l, hLR hl⟩ : Matrix (Fin m) (Fin m) K) *ᵥ x - x = s • u := by
      intro x
      obtain ⟨s, hs⟩ := hSe (c.symm x : M₀.E) (c.symm x).2
      refine ⟨s, ?_⟩
      have h1 := hact l hl (c.symm x)
      rw [LinearEquiv.apply_symm_apply] at h1
      rw [h1]
      have h2 : (⟨φ₀ ⟨l, hc.LB_le_H0 hl⟩ ((c.symm x : _) : M₀.E), hWV l hl _ (c.symm x).2⟩ :
          ↥(imgSub M₀ V hS)) - c.symm x = s • (⟨b, hbV⟩ : ↥(imgSub M₀ V hS)) :=
        Subtype.ext hs
      have h3 : c ⟨φ₀ ⟨l, hc.LB_le_H0 hl⟩ ((c.symm x : _) : M₀.E), hWV l hl _ (c.symm x).2⟩ -
          c (c.symm x) = s • u := by
        rw [← map_sub, h2, map_smul]
      rw [LinearEquiv.apply_symm_apply] at h3
      exact h3
    obtain ⟨f, hf⟩ := exists_vecMulVec_of_sub_smul hA
    refine ⟨f, ?_, hf⟩
    have h3 := hact l hl ⟨b, hbV⟩
    have h4 : (⟨φ₀ ⟨l, hc.LB_le_H0 hl⟩ ((⟨b, hbV⟩ : ↥(imgSub M₀ V hS)) : M₀.E),
        hWV l hl _ hbV⟩ : ↥(imgSub M₀ V hS)) = ⟨b, hbV⟩ := Subtype.ext hSb
    rw [h4] at h3
    have h5 : (1 + Matrix.vecMulVec u f) *ᵥ u = u := by rw [← hf]; exact h3
    rw [mulVec_one_add_vecMulVec] at h5
    have h6 : (f ⬝ᵥ u) • u = 0 := by
      have := congrArg (fun z => z - u) h5
      simpa using this
    rcases smul_eq_zero.mp h6 with h7 | h7
    · exact h7
    · exact absurd h7 hu0
  refine ⟨b, hbV, hb0, hu0, hBb, hpart1, ?_, ?_⟩
  ·
    intro f hf
    let f' : Module.Dual K ↥(imgSub M₀ V hS) :=
      { toFun := fun w => f ⬝ᵥ c w
        map_add' := fun x y => by rw [map_add, dotProduct_add]
        map_smul' := fun r x => by
          rw [map_smul, dotProduct_smul, RingHom.id_apply, smul_eq_mul] }
    have hf' : f' ⟨b, hbV⟩ = 0 := hf
    obtain ⟨l, hl, hlS⟩ := hE2 f' hf'
    refine ⟨l, hl, matrix_eq_of_forall_mulVec fun x => ?_⟩
    rw [mulVec_one_add_vecMulVec]
    rw [← c.apply_symm_apply x, hact l hl (c.symm x)]
    have h1 := hlS (φ₀ ⟨l, hc.LB_le_H0 hl⟩) (hSl l hl) (c.symm x)
    have h2 : (⟨φ₀ ⟨l, hc.LB_le_H0 hl⟩ ((c.symm x : _) : M₀.E), hWV l hl _ (c.symm x).2⟩ :
        ↥(imgSub M₀ V hS)) = c.symm x + f' (c.symm x) • (⟨b, hbV⟩ : ↥(imgSub M₀ V hS)) :=
      Subtype.ext h1
    rw [h2, map_add, map_smul]
    simp [f']
  · intro T hT
    rw [hE3 T hT, c.finrank_eq, Module.finrank_fin_fun]

omit [Finite G] in
theorem card_dotProduct_ker {m : ℕ} {K : Type} [Field K] [Finite K] {u : Fin m → K}
    (hu : u ≠ 0) :
    Nat.card {f : Fin m → K // f ⬝ᵥ u = 0} = Nat.card K ^ (m - 1) := by
  classical
  let ev : (Fin m → K) →ₗ[K] K :=
    { toFun := fun f => f ⬝ᵥ u
      map_add' := fun x y => by rw [add_dotProduct]
      map_smul' := fun r x => by rw [smul_dotProduct, RingHom.id_apply] }
  have hrange : LinearMap.range ev = ⊤ := by
    rw [eq_top_iff]
    obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu (funext hcon)
    intro a _
    refine ⟨Pi.single j (a / u j), ?_⟩
    show Pi.single j (a / u j) ⬝ᵥ u = a
    rw [single_dotProduct, div_mul_cancel₀ _ hj]
  have h1 := LinearMap.finrank_range_add_finrank_ker ev
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
  have h2 : Module.finrank K (LinearMap.ker ev) = m - 1 := by omega
  have h3 := Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker ev)
  rw [h2] at h3
  rw [← h3]
  exact Nat.card_congr (Equiv.refl _)

theorem stroth310SLTransv_of_34 (h34 : Stroth34Statement) : Stroth310SLTransvStatement := by
  classical
  intro G _ _ M Q Z B hc n t hs hR hV
  have h35all := stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen
  have h35 := h35all.2.1
  obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  set V := Vt M (LB M Q B) B Z t with hVdef
  set R := Rt M (LB M Q B) t with hRdef
  have hS : ∀ (c : GaloisField 2 n') (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V :=
    fun c e he => hc.smul_mem_img_Vt h t c he
  obtain ⟨m, φ, hnorm, ψ, c, hker, hequiv, -, -, hSeq⟩ :=
    exists_natural_data_of_subspace hc.hyp (hc.Vt_le_Q t) sec39_Z_le_Vt (hc.Rt_le_H0 t)
      (hc.Rt_normalizes_Vt hs.mem) (fun _ => Ctx.mem_CN (hc := hc)) h hS
  have hm2 : 2 ≤ m := by
    have := hc.two_le_finrank_Vt h35 hs.mem hR h hS
    rwa [c.finrank_eq, Module.finrank_fin_fun] at this
  have hLRB : LB M Q B ≤ R := le_Rt (M := M) (LB M Q B) hs.mem
  obtain ⟨bB, hbBV, -, huB0, -, hB1, hB2, -⟩ := hc.matrix_elation_data hs.width hs.n_gt hs.noA2
    h35all.2.2.1 h35all.2.2.2 h (hc.B_le_Vt hs.mem) (le_inf (hc.Vt_le_Q t) hV) hS
    (hc.Rt_le_H0 t) (hc.Rt_normalizes_Vt hs.mem) hLRB φ c hSeq
  set uB : Fin m → GaloisField 2 n' := c ⟨bB, hbBV⟩ with huBdef
  have hconj : ∀ m' ∈ M, t ∈ conjSubgroup m' (LB M Q B) → ∃ u : Fin m → GaloisField 2 n',
      u ≠ 0 ∧
      (∀ (l : G) (hl : l ∈ LB M Q (conjSubgroup m' B)), ∃ f : Fin m → GaloisField 2 n',
        f ⬝ᵥ u = 0 ∧ ∀ hlR : l ∈ R, (φ ⟨l, hlR⟩ : Matrix (Fin m) (Fin m) (GaloisField 2 n')) =
          1 + Matrix.vecMulVec u f) ∧
      (∀ f : Fin m → GaloisField 2 n', f ⬝ᵥ u = 0 → ∃ (l : G)
        (hl : l ∈ LB M Q (conjSubgroup m' B)) (hlR : l ∈ R),
          (φ ⟨l, hlR⟩ : Matrix (Fin m) (Fin m) (GaloisField 2 n')) =
            1 + Matrix.vecMulVec u f) := by
    intro m' hm' htm'
    have hC : Ctx M Q Z (conjSubgroup m' B) := hc.conj_of_mem hm'
    have hnoC : NoA2 Q Z (LB M Q (conjSubgroup m' B)) := hc.noA2_conj hs.noA2 hm'
    have h35C := stroth_3_5 h34 hC hs.width hs.n_gt hnoC (hs.gen.conj_of_mem hm')
    have hVC : V ≤ QB (conjSubgroup m' B) :=
      hc.Vt_le_QB_conj hs.width hs.n_gt hs.noA2 h35 hs.mem hV hm' htm'
    have hCV : conjSubgroup m' B ≤ V := sec39_conjB_le_Vt hm' htm'
    have hLR : LB M Q (conjSubgroup m' B) ≤ R := by
      rw [hc.LB_conj hm']
      exact conjSubgroup_le_Rt hm' htm'
    obtain ⟨b, hbV', -, hu0, -, hP1, hP2, -⟩ := hC.matrix_elation_data hs.width hs.n_gt hnoC
      h35C.2.2.1 h35C.2.2.2 h hCV (le_inf (hc.Vt_le_Q t) hVC) hS (hc.Rt_le_H0 t)
      (hc.Rt_normalizes_Vt hs.mem) hLR φ c hSeq
    refine ⟨c ⟨b, hbV'⟩, hu0, fun l hl => ?_, fun f hf => ?_⟩
    · obtain ⟨f, hf0, hfm⟩ := hP1 l hl
      exact ⟨f, hf0, fun _ => hfm⟩
    · obtain ⟨l, hl, hfm⟩ := hP2 f hf
      exact ⟨l, hl, hLR hl, hfm⟩
  have hirr : NatIrred φ.range := hc.natIrred_of_data h35 hs.mem h hS φ c hSeq
  have hgen : GenByTransvLines φ.range := by
    apply le_antisymm
    · let Sset : Set (GL (Fin m) (GaloisField 2 n')) := {g | ∃ v f : Fin m → GaloisField 2 n',
        v ≠ 0 ∧ f ≠ 0 ∧ f ⬝ᵥ v = 0 ∧ (g : Matrix (Fin m) (Fin m) (GaloisField 2 n')) =
          1 + Matrix.vecMulVec v f ∧ ∀ c : GaloisField 2 n', ∃ h ∈ φ.range,
            (h : Matrix (Fin m) (Fin m) (GaloisField 2 n')) = 1 + c • Matrix.vecMulVec v f}
      let Γ : Subgroup G := ((Subgroup.closure Sset).comap φ).map R.subtype
      have hRΓ : R ≤ Γ := by
        refine iSup₂_le fun m' hm' => iSup_le fun htm' => ?_
        intro l hl
        have hlR : l ∈ R := conjSubgroup_le_Rt hm' htm' hl
        have hlC : l ∈ LB M Q (conjSubgroup m' B) := by rw [hc.LB_conj hm']; exact hl
        refine ⟨⟨l, hlR⟩, ?_, rfl⟩
        obtain ⟨u, hu0, hP1, hP2⟩ := hconj m' hm' htm'
        obtain ⟨f, hf0, hfm⟩ := hP1 l hlC
        show φ ⟨l, hlR⟩ ∈ Subgroup.closure Sset
        by_cases hf : f = 0
        · have : φ ⟨l, hlR⟩ = 1 := by
            apply Units.ext
            rw [hfm hlR, hf]
            simp
          rw [this]
          exact Subgroup.one_mem _
        · refine Subgroup.subset_closure ⟨u, f, hu0, hf, hf0, hfm hlR, fun a => ?_⟩
          have ha : (a • f) ⬝ᵥ u = 0 := by rw [smul_dotProduct, hf0, smul_zero]
          obtain ⟨l', hl', hl'R, hmat⟩ := hP2 (a • f) ha
          refine ⟨φ ⟨l', hl'R⟩, ⟨_, rfl⟩, ?_⟩
          rw [hmat]
          congr 1
          ext i j
          simp [Matrix.vecMulVec_apply, mul_left_comm]
      rintro _ ⟨r, rfl⟩
      obtain ⟨r', hr', hrr⟩ := hRΓ r.2
      have : r' = r := Subtype.ext hrr
      rw [← this]
      exact hr'
    · refine (Subgroup.closure_le φ.range).mpr ?_
      rintro g ⟨v, f, -, -, -, hg, hK⟩
      obtain ⟨h', hh', hh'g⟩ := hK 1
      rw [one_smul] at hh'g
      have : h' = g := Units.ext (hh'g.trans hg.symm)
      exact this ▸ hh'
  have hcount : Nat.card (GaloisField 2 n') ^ (m - 1) ≤
      Nat.card ↥(((LB M Q B).subgroupOf R).map φ) := by
    rw [← card_dotProduct_ker huB0]
    let F : {f : Fin m → GaloisField 2 n' // f ⬝ᵥ uB = 0} → ↥(((LB M Q B).subgroupOf R).map φ) :=
      fun f => ⟨φ ⟨(hB2 f.1 f.2).choose, hLRB (hB2 f.1 f.2).choose_spec.choose⟩,
        ⟨⟨(hB2 f.1 f.2).choose, hLRB (hB2 f.1 f.2).choose_spec.choose⟩,
          (hB2 f.1 f.2).choose_spec.choose, rfl⟩⟩
    refine Nat.card_le_card_of_injective F ?_
    intro f f' hff
    have h1 := congrArg (fun x : ↥(((LB M Q B).subgroupOf R).map φ) =>
      ((x : GL (Fin m) (GaloisField 2 n')) : Matrix (Fin m) (Fin m) (GaloisField 2 n'))) hff
    simp only [F] at h1
    rw [(hB2 f.1 f.2).choose_spec.choose_spec, (hB2 f'.1 f'.2).choose_spec.choose_spec] at h1
    obtain ⟨i, hi⟩ : ∃ i, uB i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact huB0 (funext hcon)
    refine Subtype.ext (funext fun j => ?_)
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply] at h2
    exact mul_left_cancel₀ hi (add_left_cancel h2)
  refine ⟨GaloisField 2 n', inferInstance, inferInstance, inferInstance, h.card, m, hm2, φ, hker,
    ⟨hc.Rt_normalizes_Vt hs.mem, hnorm, ψ, hequiv⟩, hirr, hgen, ⟨uB, huB0, ?_⟩, hcount⟩
  intro l hl x
  obtain ⟨f, -, hf⟩ := hB1 (l : G) hl
  refine ⟨f ⬝ᵥ x, ?_⟩
  have h1 : (φ l : Matrix (Fin m) (Fin m) (GaloisField 2 n')) *ᵥ x =
      x + (f ⬝ᵥ x) • uB := by
    rw [show φ l = φ ⟨(l : G), hLRB hl⟩ from rfl, hf, mulVec_one_add_vecMulVec]
  rw [h1]
  abel

end CFSG.RankThree.GF2n.Stroth80

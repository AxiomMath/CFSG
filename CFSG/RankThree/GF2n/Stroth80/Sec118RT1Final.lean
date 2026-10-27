module

public import CFSG.RankThree.GF2n.Stroth80.Sec118RT1Radical
public import CFSG.RankThree.GF2n.Stroth80.Sec118RT1TensorHom
public import CFSG.RankThree.GF2n.Stroth80.Sec118RT1Fix
public import CFSG.RankThree.GF2n.Stroth80.Sec118RT1Core
public import CFSG.RankThree.GF2n.Stroth80.Sec118RT1Struct

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix
open CFSG.ClassicalGroups.Symplectic

theorem stroth118_RT1_refutation (G : Type) [Group G] [Finite G]
    (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n m x : ℕ) (hw : Width Q Z n) (hn : 2 < n)
    (hLie : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    (_hq : 2 ^ x = Nat.card Z)
    (a : ↥M) (h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G))
    (_hspt : CMSpTransvAt M Q Z B m x a h)
    (hcard : Nat.card ↥(Z ⊔ ⁅Q, XbarPre M Q Z B⁆) = Nat.card Z ^ (4 * m + 1))
    (K : Type) [Field K] [Finite K] [CharP K 2] (γ : G → K)
    (M₀ : Tim79.QuadModel Q Z K γ) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (W₁ W₂ : Submodule K M₀.E) (h12 : W₁ ⊓ W₂ = ⊥)
    (hsup : W₁ ⊔ W₂ = cmComm M Q Z B K γ M₀ φ)
    (hW₁ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₁, φ s w ∈ W₁)
    (hW₂ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₂, φ s w ∈ W₂)
    (hs₁ : ∀ w ∈ W₁, M₀.Qf w = 0) (hs₂ : ∀ w ∈ W₂, M₀.Qf w = 0)
    (b : Module.Basis (Fin m ⊕ Fin m) K ↥W₁)
    (ρ : ↥(XbarH M Q Z B) →* GL (Fin m ⊕ Fin m) K) (hρr : ρ.range = StatedSp m K)
    (hρk : ∀ s : ↥(XbarH M Q Z B), ρ s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q)
    (hbas : ∀ (s : ↥(XbarH M Q Z B)) (i : Fin m ⊕ Fin m),
      φ s ((b i : ↥W₁) : M₀.E) =
        ∑ j, (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) j i • ((b j : ↥W₁) : M₀.E)) :
    False := by
  classical
  obtain ⟨-, -, hm2, -⟩ := hLie.admissible
  have hm1 : 1 ≤ m := by omega
  have hn2m : 2 * m ≤ n := hc.two_mul_le_of_card_commXbarPre hw hcard
  have hKq : Nat.card K = Nat.card Z := hD.card
  have hq2 : 2 < Nat.card K := by
    have := hc.hyp.q4
    rw [hKq]
    omega
  have hρe : ∀ (s : ↥(XbarH M Q Z B)) (w : ↥W₁),
      b.equivFun ⟨φ s (w : M₀.E), hW₁ s (w : M₀.E) w.2⟩ =
        (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ b.equivFun w := fun s w =>
    equivFun_map_of_basis_action b ((φ s : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
      (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (hbas s) (hW₁ s) w
  obtain ⟨e₁, e₂, he₁, he₂⟩ :=
    hc.exists_coords_of_global hD φ hφπ hsup hW₁ hW₂ hs₁ hs₂ b ρ hρr hρe
  have haL : (a : G) ∈ LB M Q B := h.1
  have hA : IsA2 Q Z (a : G) := h.2
  have ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a := ⟨a, haL, hA⟩
  have haM : (a : G) ∈ M := a.2
  have haX : (a : G) ∈ XbarPre M Q Z B :=
    (mem_XbarPre_iff hc haM).mpr (Subgroup.subset_closure (hc.mk_mem_Ebar haL hA))
  have hrank := hc.rank_sub_one_eq_one hD φ hφπ ha2 (disjoint_iff.mpr h12) hsup hW₁ hW₂ ρ e₁ e₂
    he₁ he₂ haL hA haX
  obtain ⟨u, hu0, hrange⟩ : ∃ u : Fin m ⊕ Fin m → K, u ≠ 0 ∧
      LinearMap.range (Matrix.mulVecLin
        (((ρ ⟨⟨a, XbarPre_le_H0 hc haX⟩, (mem_XbarH_iff hc _).mpr haX⟩ : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1)) = Submodule.span K {u} := by
    obtain ⟨⟨v, hv⟩, hv0, hvall⟩ := finrank_eq_one_iff'.mp hrank
    refine ⟨v, fun h0 => hv0 (Subtype.ext h0), ?_⟩
    ext y
    constructor
    · intro hy
      obtain ⟨c, hc'⟩ := hvall ⟨y, hy⟩
      exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc'⟩
    · intro hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      exact Submodule.smul_mem _ c hv
  obtain ⟨b₀, hb00, -, hB, hperp, -⟩ := hc.dictB hD
  obtain ⟨c₁, c₂, hdec⟩ :=
    hc.exists_decomp_of_dictB hD φ hφπ ha2 hsup hW₁ hW₂ ρ e₁ e₂ he₁ he₂ haL hA haX hrange hB
  let ι₁ : (Fin m ⊕ Fin m → K) →ₗ[K] M₀.E := W₁.subtype ∘ₗ e₁.symm.toLinearMap
  let ι₂ : (Fin m ⊕ Fin m → K) →ₗ[K] M₀.E := W₂.subtype ∘ₗ e₂.symm.toLinearMap
  have hind : ∀ a a' : Fin m ⊕ Fin m → K, ι₁ a + ι₂ a' = 0 → a = 0 ∧ a' = 0 := by
    intro a a' hsum
    have h1 : ι₁ a = -(ι₂ a') := eq_neg_of_add_eq_zero_left hsum
    have hmem : ι₁ a ∈ W₁ ⊓ W₂ := ⟨(e₁.symm a).2, by
      rw [h1]; exact W₂.neg_mem (e₂.symm a').2⟩
    rw [h12, Submodule.mem_bot] at hmem
    refine ⟨?_, ?_⟩
    · have : e₁.symm a = 0 := Subtype.ext hmem
      simpa using this
    · rw [hmem] at h1
      have : e₂.symm a' = 0 := Subtype.ext (neg_eq_zero.mp h1.symm)
      simpa using this
  let k₀ : Fin 2 → K := ![c₁, c₂]
  have hb₀ : b₀ = tensorK2 ι₁ ι₂ u k₀ := by
    rw [hdec, tensorK2_apply]
    rfl
  have hk₀ne : k₀ ≠ 0 := by
    intro h0
    apply hb00
    rw [hb₀, h0]
    simp
  obtain ⟨k₁, hk⟩ := exists_detFin2_eq_one hk₀ne
  obtain ⟨σ, η, hσ, hση, hT⟩ :=
    hc.exists_tensorHom hD φ hφπ hm1 h12 hsup hW₁ hW₂ ρ hρr e₁ e₂ he₁ he₂
  have hLBH : LB M Q B ≤ H0 M Z := hc.LB_le_H0
  let inc : ↥(LB M Q B) →* ↥(H0 M Z) := Subgroup.inclusion hLBH
  let T : ↥(LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E) := φ.comp inc
  let S : ↥(LB M Q B) →* GL (Fin m ⊕ Fin m) K := σ.comp inc
  let H : ↥(LB M Q B) →* GL (Fin 2) K := (η.toHomUnits).comp inc
  have hHval : ∀ d : ↥(LB M Q B), ((H d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = η (inc d) :=
    fun d => rfl
  have hTcore : ∀ (d : ↥(LB M Q B)) (x : Fin m ⊕ Fin m → K) (k : Fin 2 → K),
      T d (tensorK2 ι₁ ι₂ x k) =
        tensorK2 ι₁ ι₂ ((S d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)
          ((H d : Matrix (Fin 2) (Fin 2) K) *ᵥ k) := by
    intro d x k
    exact tensorK2_map ι₁ ι₂ ((φ (inc d) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
      (Matrix.mulVecLin (σ (inc d) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) (η (inc d))
      (fun x => (hT (inc d) x).1) (fun x => (hT (inc d) x).2) x k
  have hfixd : ∀ d : ↥(LB M Q B), T d (tensorK2 ι₁ ι₂ u k₀) = tensorK2 ι₁ ι₂ u k₀ := by
    intro d
    rw [← hb₀]
    exact (hc.LB_act_fix_line hD hB d.2
      (T := ((φ (inc d) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E))
      (fun y hy => hφπ (inc d) y hy)).1
  have hsq : ∀ d : ↥(LB M Q B), S d * S d = 1 ∧ η (inc d) * η (inc d) = 1 := by
    intro d
    have hdd : ((inc d * inc d : ↥(H0 M Z)) : G) ∈ Q := by
      have h2 := hc.sq_mem_Q_of_mem_LB d.2
      rw [pow_two] at h2
      exact h2
    obtain ⟨h1, h2⟩ := tensorHom_eq_one_of_mem_Q φ hm1 h12 e₁ e₂ σ η hσ hT (inc d * inc d)
      (action_eq_id_of_mem_Q φ hφπ (inc d * inc d) hdd)
    rw [map_mul] at h1 h2
    exact ⟨h1, h2⟩
  have hunip : ∀ d : ↥(LB M Q B),
      (S d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = u ∧
        (H d : Matrix (Fin 2) (Fin 2) K) *ᵥ k₀ = k₀ ∧
          ∃ t : K, (H d : Matrix (Fin 2) (Fin 2) K) *ᵥ k₁ = k₁ + t • k₀ := by
    intro d
    obtain ⟨hs1, hη1⟩ := hsq d
    have hs2 : ∀ y : Fin m ⊕ Fin m → K,
        (Matrix.mulVecLin (σ (inc d) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K))
          ((Matrix.mulVecLin (σ (inc d) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) y) = y := by
      intro y
      have h3 : ((S d * S d : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
          = 1 := by rw [hs1]; rfl
      rw [Units.val_mul] at h3
      show (σ (inc d) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        ((σ (inc d) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) = y
      rw [Matrix.mulVec_mulVec]
      exact (congrArg (fun A => A *ᵥ y) h3).trans (Matrix.one_mulVec y)
    exact unip_of_tensor_fix ι₁ ι₂ hind hu0 hk ((φ (inc d) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
      (Matrix.mulVecLin (σ (inc d) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) (η (inc d))
      (fun x k => hTcore d x k) (hfixd d) hs2 hη1
  have hDq : ∀ d : ↥(LB M Q B), d ∈ Q.subgroupOf (LB M Q B) ↔ (S d = 1 ∧ H d = 1) := by
    intro d
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hdQ
      obtain ⟨h1, h2⟩ := tensorHom_eq_one_of_mem_Q φ hm1 h12 e₁ e₂ σ η hσ hT (inc d)
        (action_eq_id_of_mem_Q φ hφπ (inc d) hdQ)
      exact ⟨h1, Units.ext h2⟩
    · rintro ⟨h1, h2⟩
      refine hc.mem_Q_of_tensor_eq_one hD φ hφπ hsup e₁ e₂ σ η hT (inc d)
        (fun z hz => hc.action_fixes_orthogonal hD φ hφπ ha2 d.2 (hLBH d.2) hz) h1 ?_
      exact congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h2
  obtain ⟨-, hLuW, hdichW⟩ := hc.rho_LB_le_LspGL_or_eq hD φ hφπ ha2 h12 hsup hW₁ hW₂ hs₁ hs₂ b ρ
    hρr hρk hρe haL hA haX hu0 hrange
  have hηeq : ∀ d : ↥(LB M Q B), H d = 1 → η (inc d) = 1 := fun d hd =>
    congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hd
  have hXd : ∀ d : ↥(LB M Q B), H d = 1 →
      ∃ y : ↥(XbarH M Q Z B), ((y : ↥(H0 M Z)) : G) = (d : G) ∧ ρ y = S d := by
    intro d hd
    have hX : (d : G) ∈ XbarPre M Q Z B :=
      hc.mem_XbarPre_of_eta_eq_one hD φ hφπ ha2 hsup e₁ e₂ σ η hT hσ ρ hρr hση (inc d) d.2
        (hηeq d hd)
    refine ⟨⟨inc d, (mem_XbarH_iff hc _).mpr hX⟩, rfl, ?_⟩
    exact ((hση ⟨inc d, (mem_XbarH_iff hc _).mpr hX⟩).1).symm
  have hLu : ∀ d : ↥(LB M Q B), H d = 1 → S d ∈ LspGL m K u := by
    intro d hd
    obtain ⟨y, hyd, hρy⟩ := hXd d hd
    have := hLuW y (by rw [hyd]; exact d.2)
    rw [← hρy]
    exact this
  have hdich : (∀ d : ↥(LB M Q B), H d = 1 → ∃ c : K, ∀ v : Fin m ⊕ Fin m → K,
        (S d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v = v + (c * spForm m K v u) • u) ∨
      (∀ g ∈ LspGL m K u, ∃ d : ↥(LB M Q B), H d = 1 ∧ S d = g) := by
    rcases hdichW with h1 | h2
    · left
      intro d hd
      obtain ⟨y, hyd, hρy⟩ := hXd d hd
      obtain ⟨c, hc'⟩ := h1 y (by rw [hyd]; exact d.2)
      exact ⟨c, fun v => by rw [← hρy]; exact hc' v⟩
    · right
      intro g hg
      obtain ⟨y, hyLB, hyg⟩ := h2 g hg
      refine ⟨⟨((y : ↥(H0 M Z)) : G), hyLB⟩, ?_, ?_⟩
      · exact Units.ext (hση y).2
      · rw [← hyg]
        exact (hση y).1
  have : Finite M₀.E := Module.finite_of_finite K
  have hcompl := hc.isCompl_cmComm_orthogonal hD φ hφπ
  let Yp : AddSubgroup M₀.E := (M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ)).toAddSubgroup
  let V : AddSubgroup M₀.E := M₀.img (Q ⊓ QB B)
  have htv : ∀ (y : Fin m ⊕ Fin m → K) (k : Fin 2 → K),
      tensorK2 ι₁ ι₂ y k ∈ cmComm M Q Z B K γ M₀ φ := by
    intro y k
    rw [tensorK2_apply, ← hsup]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (W₁.smul_mem _ (e₁.symm y).2))
      (Submodule.mem_sup_right (W₂.smul_mem _ (e₂.symm y).2))
  have hdec' : ∀ v : M₀.E, ∃ (x₀ x₁ : Fin m ⊕ Fin m → K) (z : M₀.E), z ∈ Yp ∧
      v = tensorK2 ι₁ ι₂ x₀ k₀ + tensorK2 ι₁ ι₂ x₁ k₁ + z := by
    intro v
    have hv : v ∈ cmComm M Q Z B K γ M₀ φ ⊔ M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ) := by
      rw [hcompl.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    rw [← hsup] at hy
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨x₀, x₁, hx⟩ := exists_tensorK2_eq_add ι₁ ι₂ hk (e₁ ⟨w₁, hw₁⟩) (e₂ ⟨w₂, hw₂⟩)
    refine ⟨x₀, x₁, z, hz, ?_⟩
    rw [← hx]
    simp [ι₁, ι₂]
  have hYp' : ∀ (x₀ x₁ : Fin m ⊕ Fin m → K) (z : M₀.E), z ∈ Yp →
      tensorK2 ι₁ ι₂ x₀ k₀ + tensorK2 ι₁ ι₂ x₁ k₁ + z = 0 → x₀ = 0 ∧ x₁ = 0 := by
    intro x₀ x₁ z hz hsum
    have hy : tensorK2 ι₁ ι₂ x₀ k₀ + tensorK2 ι₁ ι₂ x₁ k₁ ∈ cmComm M Q Z B K γ M₀ φ :=
      Submodule.add_mem _ (htv _ _) (htv _ _)
    have hneg : tensorK2 ι₁ ι₂ x₀ k₀ + tensorK2 ι₁ ι₂ x₁ k₁ = -z := eq_neg_of_add_eq_zero_left hsum
    have hy' : tensorK2 ι₁ ι₂ x₀ k₀ + tensorK2 ι₁ ι₂ x₁ k₁ ∈
        M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ) := by
      rw [hneg]; exact Submodule.neg_mem _ hz
    have h0 := Submodule.disjoint_def.mp hcompl.disjoint _ hy hy'
    exact tensorK2_eq_zero_pair ι₁ ι₂ hind hk h0
  have hTYp : ∀ d : ↥(LB M Q B), ∀ z ∈ Yp, T d z = z := fun d z hz =>
    hc.action_fixes_orthogonal hD φ hφπ ha2 d.2 (hLBH d.2) hz
  have hV1 : ∀ d : ↥(LB M Q B), ∀ v ∈ V, ∃ s : K, T d v - v = s • tensorK2 ι₁ ι₂ u k₀ := by
    intro d v hv
    obtain ⟨c, hc'⟩ := (hc.LB_act_fix_line hD hB d.2
      (T := ((φ (inc d) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E))
      (fun y hy => hφπ (inc d) y hy)).2 v hv
    exact ⟨c, by rw [← hb₀]; exact hc'⟩
  obtain ⟨cf, -, hcf⟩ :=
    hc.exists_form_const hD φ hφπ hm1 hsup hW₁ hW₂ hs₁ ρ hρr e₁ e₂ he₁ he₂
  have hsymm : ∀ e f : M₀.E, M₀.B e f = M₀.B f e := fun e f => by
    rw [Tim79.QuadModel.B_comm, CharTwo.neg_eq]
  have hV2 : ∀ (d : ↥(LB M Q B)) (y : Fin m ⊕ Fin m → K) (k : Fin 2 → K),
      spForm m K y u = 0 → T d (tensorK2 ι₁ ι₂ y k) - tensorK2 ι₁ ι₂ y k ∈ V := by
    intro d y k hyu
    have hy : M₀.B (tensorK2 ι₁ ι₂ y k) b₀ = 0 := by
      rw [hb₀, tensorK2_form M₀.B ι₁ ι₂ cf hsymm
        (fun x y => polar_eq_zero_of_Qf_eq_zero hs₁ (e₁.symm x).2 (e₁.symm y).2)
        (fun x y => polar_eq_zero_of_Qf_eq_zero hs₂ (e₂.symm x).2 (e₂.symm y).2) hcf y u k k₀,
        hyu, mul_zero]
    exact hc.map_sub_one_mem_img_inf_QB φ hφπ hperp d.2 (hLBH d.2) hy
  have hV3 : ∀ v ∈ V, (∀ d : ↥(LB M Q B), T d v = v) → ∃ s : K, v = s • tensorK2 ι₁ ι₂ u k₀ := by
    intro v hv hfix
    obtain ⟨s, hs⟩ := hc.eq_smul_of_fixed_mem_img_inf_QB φ hφπ hB hv
      (fun l hl hlH => hfix ⟨l, hl⟩)
    exact ⟨s, by rw [← hb₀]; exact hs⟩
  have hQLB : Q ≤ LB M Q B := le_sup_left
  have hDqcard : Nat.card (Q.subgroupOf (LB M Q B)) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQLB).toEquiv
  have hZS : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have hcardV : Nat.card ↥(Q ⊓ QB B) = Nat.card Z * Nat.card V := M₀.card_eq inf_le_left hZS
  have hmul := hc.card_LB_mul hw
  have hcnt : Nat.card ↥(LB M Q B) * (Nat.card K * Nat.card V) =
      Nat.card (Q.subgroupOf (LB M Q B)) * Nat.card K ^ (2 * n) := by
    rw [hDqcard, hKq, ← hcardV]
    exact hmul
  have hge : Nat.card (Q.subgroupOf (LB M Q B)) * Nat.card K ^ (n - 1) ≤
      Nat.card ↥(LB M Q B) := by
    rw [hDqcard, hKq]
    exact hc.card_LB_ge hw (by omega)
  exact rt1_core (n := n) hm2 hq2 hn2m ι₁ ι₂ hu0 hk T S H hTcore (fun d => (hunip d).1)
    (fun d => (hunip d).2.1) (fun d => (hunip d).2.2) (Q.subgroupOf (LB M Q B)) hDq hLu hdich
    Yp V hdec' hYp' hTYp hV1 hV2 hV3 hcnt hge

end CFSG.RankThree.GF2n.Stroth80

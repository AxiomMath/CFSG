module

public import CFSG.RankThree.GF2n.Stroth80.Sec34RootPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec34Trilinear
public import CFSG.RankThree.GF2n.Stroth80.Sec34Main

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B X : Subgroup G}

structure Stroth34CaseBHyp (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) : Prop where
  hw : Width Q Z n
  hn : 2 < n
  hno : NoA2 Q Z (LB M Q B)
  hgen : GenByB M Q B
  hO : ¬ OrthLe M B
  hS : ¬ hc.Spure ≤ Q

theorem Stroth34CaseBHyp.conj {hc : Ctx M Q Z B} {n : ℕ} (hB : Stroth34CaseBHyp M Q Z B hc n)
    {m : G} (hm : m ∈ M) :
    Stroth34CaseBHyp M Q Z (conjSubgroup m B) (hc.conj_of_mem hm) n where
  hw := hB.hw
  hn := hB.hn
  hno := hc.noA2_conj hB.hno hm
  hgen := hB.hgen.conj_of_mem hm
  hO := fun hO' => hB.hO (by
    have := hO'.conj (M.inv_mem hm)
    rwa [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one] at this)
  hS := fun hS' => hB.hS (by
    rw [hc.Spure_conj hm] at hS'
    have h1 := Subgroup.map_mono (f := (MulAut.conj m⁻¹).toMonoidHom) hS'
    have e1 : conjSubgroup m⁻¹ (conjSubgroup m hc.Spure) = hc.Spure := by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    have e2 : conjSubgroup m⁻¹ Q = Q := hc.conj_Q_eq (M.inv_mem hm)
    rw [show Subgroup.map (MulAut.conj m⁻¹).toMonoidHom (conjSubgroup m hc.Spure) = hc.Spure
      from e1, show Subgroup.map (MulAut.conj m⁻¹).toMonoidHom Q = Q from e2] at h1
    exact h1)

section Local

variable {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

@[expose] def IsLineGen (M₀ : Tim79.QuadModel Q Z K γ) (X : Subgroup G) (x : M₀.E) : Prop :=
  ∀ v : M₀.E, v ∈ M₀.img X ↔ ∃ s : K, v = s • x

theorem Ctx.dictB_gen (hc : Ctx M Q Z X) (h : GlobalModelData M Q Z γ M₀) {x : M₀.E}
    (hx0 : x ≠ 0) (hx : IsLineGen M₀ X x) :
    M₀.Qf x = 0 ∧ ∀ y ∈ Q, (y ∈ Subgroup.centralizer (X : Set G) ↔ M₀.B (M₀.π y) x = 0) := by
  obtain ⟨b, hb0, hbs, hB, hcent, -⟩ := hc.dictB h
  obtain ⟨t, ht⟩ := (hB x).mp ((hx x).mpr ⟨1, (one_smul K x).symm⟩)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [ht, zero_smul])
  refine ⟨by rw [ht, M₀.Qf_smul, hbs, mul_zero], fun y hy => ?_⟩
  rw [hcent y hy, ht, map_smul, smul_eq_mul]
  exact ⟨fun h0 => by rw [h0, mul_zero], fun h0 => (mul_eq_zero.mp h0).resolve_left ht0⟩

theorem Ctx.lagr (hc : Ctx M Q Z X) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q X)) (h : GlobalModelData M Q Z γ M₀) :
    ∃ W : Submodule K M₀.E, (∀ e, e ∈ M₀.img (Q ⊓ QB X) ↔ e ∈ W) ∧ Module.finrank K W = n ∧
      (∀ v, (∀ u ∈ W, M₀.B v u = 0) → v ∈ W) ∧ ∀ w ∈ W, M₀.Qf w = 0 := by
  have hK2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1n : 1 ≤ n := by omega
  have hDQ : Q ⊓ QB X ≤ Q := inf_le_left
  have hVD : Z ≤ Q ⊓ QB X := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have hDc : ∀ x ∈ Q ⊓ QB X, ∀ y ∈ Q ⊓ QB X, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((Ctx.inf_QB_elemAbelian hc).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hD := (hc.card_of_3_3 hw h1n hno (stroth_3_3 hc hw h1n)).2
  have hDcard : Nat.card ↥(Q ⊓ QB X) = Nat.card K ^ (n + 1) := by
    rw [hD, h.card]
  have hE : Module.finrank K M₀.E = 2 * n :=
    Stroth57D.finrank_of_card (n := n) M₀ h.reg h.card hw
  obtain ⟨W, hmem, hWn, hWo⟩ :=
    Stroth57D.lagrangian_img M₀ h.reg hK2 h.card hE hDQ hVD hDc hDcard
  refine ⟨W, hmem, hWn, fun v hv => ?_, fun w hw' => ?_⟩
  · have hvO : v ∈ M₀.B.orthogonal W := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      rw [Tim79.QuadModel.B_comm, hv u hu, neg_zero]
    rwa [hWo] at hvO
  · exact (M₀.isElemAbelian_iff h.reg hDQ).mp hc.inf_QB_elemAbelian w ((hmem w).mpr hw')

@[expose] def imgQInfQB (M₀ : Tim79.QuadModel Q Z K γ) (X : Subgroup G) : Submodule K M₀.E :=
  Submodule.span K (M₀.img (Q ⊓ QB X) : Set M₀.E)

theorem Ctx.mem_imgQInfQB_iff (hc : Ctx M Q Z X) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q X)) (h : GlobalModelData M Q Z γ M₀) (e : M₀.E) :
    e ∈ imgQInfQB M₀ X ↔ e ∈ M₀.img (Q ⊓ QB X) := by
  obtain ⟨W, hW, -, -, -⟩ := hc.lagr hw hn hno h
  constructor
  · intro he
    have hle : imgQInfQB M₀ X ≤ W := Submodule.span_le.mpr fun v hv => (hW v).mp hv
    exact (hW e).mpr (hle he)
  · exact fun he => Submodule.subset_span he

theorem Ctx.imgQInfQB_lagr (hc : Ctx M Q Z X) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q X)) (h : GlobalModelData M Q Z γ M₀) :
    Module.finrank K (imgQInfQB M₀ X) = n ∧
      (∀ v, (∀ u ∈ imgQInfQB M₀ X, M₀.B v u = 0) → v ∈ imgQInfQB M₀ X) ∧
      ∀ w ∈ imgQInfQB M₀ X, M₀.Qf w = 0 := by
  obtain ⟨W, hW, hWn, hWp, hWs⟩ := hc.lagr hw hn hno h
  have hDW : imgQInfQB M₀ X = W := by
    ext e
    rw [hc.mem_imgQInfQB_iff hw hn hno h, hW]
  rw [hDW]
  exact ⟨hWn, hWp, hWs⟩

theorem Ctx.le_QB_iff_mem_imgQInfQB (hc : Ctx M Q Z X) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q X)) (h : GlobalModelData M Q Z γ M₀) {Y : Subgroup G}
    (hcY : Ctx M Q Z Y) {y : M₀.E} (hy : IsLineGen M₀ Y y) :
    Y ≤ QB X ↔ y ∈ imgQInfQB M₀ X := by
  rw [hc.mem_imgQInfQB_iff hw hn hno h]
  constructor
  · intro hYX
    have hYD : Y ≤ Q ⊓ QB X := le_inf hcY.le hYX
    exact M₀.img_mono hYD ((hy y).mpr ⟨1, (one_smul K y).symm⟩)
  · intro hyD u hu
    have hZD : Z ≤ Q ⊓ QB X := le_inf hc.Z_le_Q hc.Z_le_QB.1
    obtain ⟨s, hs⟩ := (hy _).mp (M₀.pi_mem_img hu (hcY.le hu))
    have hsy : s • y ∈ M₀.img (Q ⊓ QB X) := by
      have h1 : s • y ∈ imgQInfQB M₀ X :=
        (imgQInfQB M₀ X).smul_mem s ((hc.mem_imgQInfQB_iff hw hn hno h y).mpr hyD)
      exact (hc.mem_imgQInfQB_iff hw hn hno h _).mp h1
    rw [← hs] at hsy
    exact ((M₀.mem_img_iff hZD (hcY.le hu)).mp hsy).2

structure GlobalModelAction (M Q Z : Subgroup G) (K : Type) [Field K] [Finite K] (γ : G → K)
    (M₀ : Tim79.QuadModel Q Z K γ) where
  h : GlobalModelData M Q Z γ M₀
  φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)
  hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)
  hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q
  hφiso : ∀ (m : H0 M Z) e, M₀.Qf (φ m e) = M₀.Qf e

theorem Ctx.spure_data (hc : Ctx M Q Z X) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q X)) (Pk : GlobalModelAction M Q Z K γ M₀) (hLH0 : LB M Q X ≤ H0 M Z)
    {x : M₀.E} (hx0 : x ≠ 0) (hx : IsLineGen M₀ X x) :
    ∃ d : ℕ, Nat.card hc.Spure = Nat.card Q * Nat.card K ^ d ∧
      (d ≤ 1 → ∃ f : M₀.E, ∀ y, M₀.B y x = 0 →
        (∀ r : ↥(LB M Q X), Pk.φ (Subgroup.inclusion hLH0 r) y - y ∈ Submodule.span K {x}) →
          y ∈ imgQInfQB M₀ X ⊔ Submodule.span K {f}) := by
  obtain ⟨-, hcent⟩ := hc.dictB_gen Pk.h hx0 hx
  obtain ⟨hWn, hWp, hWs⟩ := hc.imgQInfQB_lagr hw hn hno Pk.h
  have hWmem := hc.mem_imgQInfQB_iff hw hn hno Pk.h
  have hbW : x ∈ imgQInfQB M₀ X := (hWmem x).mpr
    (M₀.img_mono (le_inf hc.le hc.B_le_QB : X ≤ Q ⊓ QB X) ((hx x).mpr ⟨1, (one_smul K x).symm⟩))
  have hxW : (⟨x, hbW⟩ : imgQInfQB M₀ X) ≠ 0 := fun h0 => hx0 (congrArg Subtype.val h0)
  have hHom0 := card_dual_ker_eval hWn ⟨x, hbW⟩ hxW
  have hrep := exists_perp_rep M₀ (imgQInfQB M₀ X) hbW
  exact hc.card_Spure_eq_pow hw hn hno Pk.h hLH0 Pk.φ Pk.hφπ Pk.hφker Pk.hφiso hx0 hx hcent
    (imgQInfQB M₀ X) (fun e => (hWmem e).symm) hWn hWp hbW hHom0 hrep

theorem near_line_local {hc0 : Ctx M Q Z B} {n : ℕ} (hB : Stroth34CaseBHyp M Q Z B hc0 n)
    (Pk : GlobalModelAction M Q Z K γ M₀) {mx my : G} (hmx : mx ∈ M) (hmy : my ∈ M) {x y : M₀.E}
    (hx : IsLineGen M₀ (conjSubgroup mx B) x) (hy : IsLineGen M₀ (conjSubgroup my B) y)
    (hyD : y ∈ imgQInfQB M₀ (conjSubgroup mx B)) (hyx : ∀ c : K, y ≠ c • x) (κ : K) :
    ∃ m' ∈ M, y + κ • x ∈ M₀.img (conjSubgroup m' B) := by
  classical
  have hcX := hc0.conj_of_mem hmx
  have hcY := hc0.conj_of_mem hmy
  have hXc := hB.conj hmx
  have hYle : conjSubgroup my B ≤ QB (conjSubgroup mx B) :=
    (hcX.le_QB_iff_mem_imgQInfQB hB.hw hB.hn hXc.hno Pk.h hcY hy).mpr hyD
  obtain ⟨y', hy'Y, hy'Q, hπy'⟩ := (hy y).mpr ⟨1, (one_smul K y).symm⟩
  obtain ⟨x', hx'X, hx'Q, hπx'⟩ := (hx (κ • x)).mpr ⟨κ, rfl⟩
  have hle : (Z ⊔ conjSubgroup mx B : Subgroup G) ≤ M₀.lift (M₀.img (conjSubgroup mx B)) := by
    refine sup_le (fun z hz => ⟨Pk.h.reg.V_le hz, ?_⟩)
      (fun u hu => ⟨hcX.le hu, M₀.pi_mem_img hu (hcX.le hu)⟩)
    rw [(M₀.π_ker z (Pk.h.reg.V_le hz)).mpr hz]
    exact AddSubgroup.zero_mem _
  have hy'ZX : y' ∉ Z ⊔ conjSubgroup mx B := by
    intro hmem
    have h1 := (hle hmem).2
    rw [hπy'] at h1
    obtain ⟨c, hc⟩ := (hx y).mp h1
    exact hyx c hc
  obtain ⟨s, hs, hsb⟩ := hcX.exists_mem_QB_M_comm_eq (hYle hy'Y) hy'ZX hx'X
  have hsM : s ∈ M := hs.2
  have hconj : s * y' * s⁻¹ = x' * y' := by
    rw [← hsb, commutatorElement_def]
    group
  refine ⟨s * my, M.mul_mem hsM hmy, ?_⟩
  have hxyQ : x' * y' ∈ Q := Q.mul_mem hx'Q hy'Q
  refine ⟨s * y' * s⁻¹, ?_, by rw [hconj]; exact hxyQ, ?_⟩
  · rw [mem_conjSubgroup]
    have e : (s * my)⁻¹ * (s * y' * s⁻¹) * (s * my) = my⁻¹ * y' * my := by group
    rw [e]
    exact mem_conjSubgroup.mp hy'Y
  · rw [hconj, M₀.π_mul _ hx'Q _ hy'Q, hπx', hπy', add_comm]

theorem far_exists_local {hc0 : Ctx M Q Z B} {n : ℕ} (hB : Stroth34CaseBHyp M Q Z B hc0 n)
    (Pk : GlobalModelAction M Q Z K γ M₀) {mx : G} (hmx : mx ∈ M) {x : M₀.E}
    (hx : IsLineGen M₀ (conjSubgroup mx B) x) :
    ∃ m' ∈ M, ∃ y : M₀.E, IsLineGen M₀ (conjSubgroup m' B) y ∧ y ≠ 0 ∧ M₀.B x y = 0 ∧
      y ∉ imgQInfQB M₀ (conjSubgroup mx B) := by
  classical
  have hcX := hc0.conj_of_mem hmx
  have hXc := hB.conj hmx
  have hO := hXc.hO
  unfold OrthLe at hO
  push Not at hO
  obtain ⟨m, hm, hcomm, hnle⟩ := hO
  have hcY := hcX.conj_of_mem hm
  obtain ⟨y, hy0, -, hY, -, -⟩ := hcY.dictB Pk.h
  have hYle : conjSubgroup m (conjSubgroup mx B) ≤ Q := hcY.le
  have hXle : conjSubgroup mx B ≤ Q := hcX.le
  have hBy := (M₀.commute_iff Pk.h.reg hYle hXle).mp hcomm y
    ((hY y).mpr ⟨1, (one_smul K y).symm⟩) x ((hx x).mpr ⟨1, (one_smul K x).symm⟩)
  refine ⟨m * mx, M.mul_mem hm hmx, y, ?_, hy0, ?_, ?_⟩
  · rw [conjSubgroup_mul]
    exact hY
  · rw [Tim79.QuadModel.B_comm, hBy, neg_zero]
  · exact fun hyD => hnle ((hcX.le_QB_iff_mem_imgQInfQB hB.hw hB.hn hXc.hno Pk.h hcY hY).mpr hyD)

theorem lemmaN_local {hc0 : Ctx M Q Z B} {n : ℕ} (hB : Stroth34CaseBHyp M Q Z B hc0 n)
    (Pk : GlobalModelAction M Q Z K γ M₀) {mx my : G} (hmx : mx ∈ M) (hmy : my ∈ M) {x y : M₀.E}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : IsLineGen M₀ (conjSubgroup mx B) x)
    (hy : IsLineGen M₀ (conjSubgroup my B) y) (hxy : M₀.B x y = 0)
    {t : G} (htS : t ∈ (hc0.conj_of_mem hmx).Spure) (htQ : t ∉ Q)
    {T : M₀.E → M₀.E} (hT : ∀ z ∈ Q, M₀.π (t * z * t⁻¹) = T (M₀.π z)) (hTy : T y = y) :
    y ∈ imgQInfQB M₀ (conjSubgroup mx B) := by
  classical
  have hcX := hc0.conj_of_mem hmx
  have hcY := hc0.conj_of_mem hmy
  have hXc := hB.conj hmx
  obtain ⟨-, hcent⟩ := hcX.dictB_gen Pk.h hx0 hx
  obtain ⟨y', hy'Y, hy'Q, hπy'⟩ := (hy y).mpr ⟨1, (one_smul K y).symm⟩
  have hy'1 : y' ≠ 1 := by
    rintro rfl
    exact hy0 (by rw [← hπy', M₀.pi_one])
  have hy'C : y' ∈ Subgroup.centralizer ((conjSubgroup mx B : Subgroup G) : Set G) := by
    rw [hcent y' hy'Q, hπy', Tim79.QuadModel.B_comm, hxy, neg_zero]
  have htM : t ∈ M := hcX.LB_le_M htS.1
  have hty : t * y' * t⁻¹ ∈ Q := (hcX.conj_mem_Q_of_mem_M htM).1 y' hy'Q
  have hZ : ⁅t, y'⁆ ∈ Z := (M₀.comm_mem_iff hy'Q hty).mpr (by rw [hT y' hy'Q, hπy', hTy])
  have hconj : conjSubgroup (my * mx⁻¹) (conjSubgroup mx B) = conjSubgroup my B := by
    rw [← conjSubgroup_mul, mul_assoc, inv_mul_cancel, mul_one]
  have hmem : y' ∈ conjSubgroup (my * mx⁻¹) (conjSubgroup mx B) := by
    rw [hconj]
    exact hy'Y
  have hN := hcX.conj_le_QB_of_exists_comm hB.hw hB.hn hXc.hno (m := my * mx⁻¹)
    (M.mul_mem hmy (M.inv_mem hmx)) hmem hy'1 hy'C ⟨t, htS, htQ, hZ⟩
  rw [hconj] at hN
  exact (hcX.le_QB_iff_mem_imgQInfQB hB.hw hB.hn hXc.hno Pk.h hcY hy).mp hN

theorem Ctx.card_Spure_caseB {hc : Ctx M Q Z X} {n : ℕ} (hX : Stroth34CaseBHyp M Q Z X hc n)
    (Pk : GlobalModelAction M Q Z K γ M₀) (hLH0 : LB M Q X ≤ H0 M Z) {x : M₀.E} (hx0 : x ≠ 0)
    (hx : IsLineGen M₀ X x) : Nat.card hc.Spure = Nat.card Q * Nat.card K := by
  obtain ⟨d, hdS, -⟩ := hc.spure_data hX.hw hX.hn hX.hno Pk hLH0 hx0 hx
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hKq : Nat.card K = Nat.card Z := Pk.h.card
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hle : Nat.card hc.Spure ≤ Nat.card Q * Nat.card Z := by
    by_contra hlt
    push Not at hlt
    exact hX.hO (hc.orthLe_of_card_Spure hX.hw hX.hn hX.hno hlt)
  have hgt : Nat.card Q < Nat.card hc.Spure := by
    by_contra hge
    push Not at hge
    exact hX.hS (Subgroup.eq_of_le_of_card_ge hc.Q_le_Spure hge).ge
  rw [hdS] at hle hgt
  rw [hKq] at hdS ⊢
  have h1 : Nat.card Z ^ d ≤ Nat.card Z := Nat.le_of_mul_le_mul_left (by rwa [hKq] at hle) hQpos
  have h2 : 1 < Nat.card Z ^ d := by
    have := hgt
    rw [hKq] at this
    nlinarith
  have hd1 : d = 1 := by
    rcases d with _ | _ | d
    · simp at h2
    · rfl
    · exfalso
      have : Nat.card Z ^ 2 ≤ Nat.card Z ^ (d + 2) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith
  rw [hdS, hd1, pow_one]

theorem far_line_local {hc0 : Ctx M Q Z B} {n : ℕ} (hB : Stroth34CaseBHyp M Q Z B hc0 n)
    (Pk : GlobalModelAction M Q Z K γ M₀) {mx my : G} (hmx : mx ∈ M) (hmy : my ∈ M) {x y : M₀.E}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : IsLineGen M₀ (conjSubgroup mx B) x)
    (hy : IsLineGen M₀ (conjSubgroup my B) y) (hxy : M₀.B x y = 0)
    (hyD : y ∉ imgQInfQB M₀ (conjSubgroup mx B)) (κ : K) :
    ∃ m' ∈ M, y + κ • x ∈ M₀.img (conjSubgroup m' B) := by
  classical
  have hcX := hc0.conj_of_mem hmx
  have hXc := hB.conj hmx
  have hLH0 : LB M Q (conjSubgroup mx B) ≤ H0 M Z := hcX.LB_le_H0_cb
  have hSH0 : hcX.Spure ≤ H0 M Z := hcX.Spure_le_H0
  obtain ⟨-, hcent⟩ := hcX.dictB_gen Pk.h hx0 hx
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hSq : Nat.card hcX.Spure = Nat.card Q * Nat.card K :=
    hcX.card_Spure_caseB hXc Pk hLH0 hx0 hx
  obtain ⟨f₁, hf₁⟩ := Tim79.QuadModel.exists_B_ne_zero hx0
  have hf₂x : M₀.B ((M₀.B f₁ x)⁻¹ • f₁) x = 1 := by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₁]
  obtain ⟨f₂, hf₂⟩ : ∃ f₂ : M₀.E, M₀.B f₂ x = 1 := ⟨_, hf₂x⟩
  let ΦS : ↥hcX.Spure →* (M₀.E ≃ₗ[K] M₀.E) := Pk.φ.comp (Subgroup.inclusion hSH0)
  have hΦπ : ∀ (s : ↥hcX.Spure) (z : G), z ∈ Q →
      M₀.π ((s : G) * z * (s : G)⁻¹) = ΦS s (M₀.π z) := fun s z hz =>
    Pk.hφπ (Subgroup.inclusion hSH0 s) z hz
  have hΦker : ∀ s : ↥hcX.Spure, ΦS s = 1 ↔ (s : G) ∈ Q := fun s =>
    Pk.hφker (Subgroup.inclusion hSH0 s)
  have hact : ∀ s : ↥hcX.Spure, ΦS s x = x ∧ ∃ c : K, ΦS s y = y + c • x := by
    intro s
    obtain ⟨hTx, hr⟩ := hcX.Spure_act Pk.h hx hcent s.2 (T := (ΦS s : M₀.E → M₀.E))
      (fun z hz => hΦπ s z hz)
    exact ⟨hTx, hr y (by rw [Tim79.QuadModel.B_comm, hxy, neg_zero])⟩
  have hcoef : ∀ (s : ↥hcX.Spure) (c : K), ΦS s y = y + c • x →
      M₀.B f₂ (ΦS s y - y) = c := by
    intro s c hc
    rw [hc, add_sub_cancel_left, map_smul, hf₂, smul_eq_mul, mul_one]
  let χ : ↥hcX.Spure →* Multiplicative K :=
    { toFun := fun s => Multiplicative.ofAdd (M₀.B f₂ (ΦS s y - y))
      map_one' := by simp
      map_mul' := by
        intro s s'
        obtain ⟨hTx, c, hc⟩ := hact s
        obtain ⟨-, c', hc'⟩ := hact s'
        have h3 : ΦS (s * s') y = y + (c + c') • x := by
          rw [map_mul, LinearEquiv.mul_apply, hc', map_add, map_smul, hTx, hc, add_smul]
          abel
        show Multiplicative.ofAdd (M₀.B f₂ (ΦS (s * s') y - y)) =
          Multiplicative.ofAdd (M₀.B f₂ (ΦS s y - y)) * Multiplicative.ofAdd (M₀.B f₂ (ΦS s' y - y))
        rw [hcoef _ _ h3, hcoef _ _ hc, hcoef _ _ hc', ofAdd_add] }
  have hχker : ∀ s : ↥hcX.Spure, χ s = 1 ↔ (s : G) ∈ Q := by
    intro s
    constructor
    · intro h1
      by_contra hsQ
      obtain ⟨-, c, hc⟩ := hact s
      have hc0 : c = 0 := by
        have h2 : M₀.B f₂ (ΦS s y - y) = 0 := ofAdd_eq_one.mp h1 
        rw [hcoef s c hc] at h2
        exact h2
      have hTy : ΦS s y = y := by rw [hc, hc0, zero_smul, add_zero]
      exact hyD (lemmaN_local hB Pk hmx hmy hx0 hy0 hx hy hxy s.2 hsQ (T := (ΦS s : M₀.E → M₀.E))
        (fun z hz => hΦπ s z hz) hTy)
    · intro hsQ
      have h1 : ΦS s = 1 := (hΦker s).mpr hsQ
      show Multiplicative.ofAdd (M₀.B f₂ (ΦS s y - y)) = 1
      rw [h1]
      simp
  have hcardχ : Nat.card hcX.Spure = Nat.card Q * Nat.card χ.range := by
    have hker : χ.ker = Q.subgroupOf hcX.Spure := by
      ext s
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hχker s
    have h1 : Nat.card χ.ker = Nat.card Q := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcX.Q_le_Spure).toEquiv
    rw [← h1, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hrange : Nat.card χ.range = Nat.card (Multiplicative K) := by
    have : Nat.card (Multiplicative K) = Nat.card K := Nat.card_congr Multiplicative.toAdd
    rw [this]
    rw [hSq] at hcardχ
    exact (Nat.eq_of_mul_eq_mul_left hQpos hcardχ).symm
  have htop : χ.range = ⊤ := Subgroup.eq_top_of_card_eq _ hrange
  obtain ⟨s, hs⟩ : Multiplicative.ofAdd κ ∈ χ.range := by rw [htop]; trivial
  obtain ⟨-, c, hc⟩ := hact s
  have hcκ : c = κ := by
    have h1 : M₀.B f₂ (ΦS s y - y) = κ := congrArg Multiplicative.toAdd hs
    rw [hcoef s c hc] at h1
    exact h1
  obtain ⟨y', hy'Y, hy'Q, hπy'⟩ := (hy y).mpr ⟨1, (one_smul K y).symm⟩
  have htM : (s : G) ∈ M := hcX.LB_le_M s.2.1
  have hty : (s : G) * y' * (s : G)⁻¹ ∈ Q := (hcX.conj_mem_Q_of_mem_M htM).1 y' hy'Q
  refine ⟨(s : G) * my, M.mul_mem htM hmy, (s : G) * y' * (s : G)⁻¹, ?_, hty, ?_⟩
  · rw [mem_conjSubgroup]
    have e : ((s : G) * my)⁻¹ * ((s : G) * y' * (s : G)⁻¹) * ((s : G) * my) = my⁻¹ * y' * my := by
      group
    rw [e]
    exact mem_conjSubgroup.mp hy'Y
  · rw [hΦπ s y' hy'Q, hπy', hc, hcκ]

theorem eich_local {hc0 : Ctx M Q Z B} {n : ℕ} (hB : Stroth34CaseBHyp M Q Z B hc0 n)
    (Pk : GlobalModelAction M Q Z K γ M₀) {mx : G} (hmx : mx ∈ M) {x : M₀.E} (hx0 : x ≠ 0)
    (hx : IsLineGen M₀ (conjSubgroup mx B) x) :
    ∃ f : Module.Dual K M₀.E, f x = 0 ∧ ∀ (my : G), my ∈ M → ∀ y : M₀.E, y ≠ 0 →
      IsLineGen M₀ (conjSubgroup my B) y → M₀.B x y = 0 → f y = 0 →
        y ∈ imgQInfQB M₀ (conjSubgroup mx B) := by
  classical
  have hcX := hc0.conj_of_mem hmx
  have hXc := hB.conj hmx
  have hSH0 : hcX.Spure ≤ H0 M Z := hcX.Spure_le_H0
  obtain ⟨-, hcent⟩ := hcX.dictB_gen Pk.h hx0 hx
  obtain ⟨t, htS, htQ⟩ := Set.not_subset.mp hXc.hS
  let T : M₀.E ≃ₗ[K] M₀.E := Pk.φ ⟨t, hSH0 htS⟩
  have hT : ∀ z ∈ Q, M₀.π (t * z * t⁻¹) = T (M₀.π z) := fun z hz =>
    Pk.hφπ ⟨t, hSH0 htS⟩ z hz
  obtain ⟨hTx, hr⟩ := hcX.Spure_act Pk.h hx hcent htS (T := (T : M₀.E → M₀.E)) hT
  obtain ⟨f₁, hf₁⟩ := Tim79.QuadModel.exists_B_ne_zero hx0
  obtain ⟨f₂, hf₂⟩ : ∃ f₂ : M₀.E, M₀.B f₂ x = 1 :=
    ⟨(M₀.B f₁ x)⁻¹ • f₁, by rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₁]⟩
  refine ⟨(M₀.B f₂).comp ((T : M₀.E →ₗ[K] M₀.E) - LinearMap.id), ?_, ?_⟩
  · simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_coe,
      id_eq]
    rw [show T x = x from hTx, sub_self, map_zero]
  · intro my hmy y hy0 hy hxy hfy
    obtain ⟨c, hc⟩ := hr y (by rw [Tim79.QuadModel.B_comm, hxy, neg_zero])
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_coe,
      id_eq] at hfy
    have hc0 : c = 0 := by
      have h1 : M₀.B f₂ (T y - y) = c := by
        rw [show T y = y + c • x from hc, add_sub_cancel_left, map_smul, hf₂, smul_eq_mul,
          mul_one]
      rw [← h1]
      exact hfy
    have hTy : T y = y := by
      rw [show T y = y + c • x from hc, hc0, zero_smul, add_zero]
    exact lemmaN_local hB Pk hmx hmy hx0 hy0 hx hy hxy htS htQ hT hTy

@[expose] def rootVecs (M₀ : Tim79.QuadModel Q Z K γ) (M B : Subgroup G) : Set M₀.E :=
  {e | e ≠ 0 ∧ ∃ m ∈ M, e ∈ M₀.img (conjSubgroup m B)}

theorem rootVecs_line {hc0 : Ctx M Q Z B} (Pk : GlobalModelAction M Q Z K γ M₀) {x : M₀.E}
    (hx : x ∈ rootVecs M₀ M B) : ∃ m ∈ M, IsLineGen M₀ (conjSubgroup m B) x := by
  obtain ⟨hx0, m, hm, hxm⟩ := hx
  obtain ⟨b, hb0, -, hB, -, -⟩ := (hc0.conj_of_mem hm).dictB Pk.h
  obtain ⟨t, ht⟩ := (hB x).mp hxm
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [ht, zero_smul])
  refine ⟨m, hm, fun v => ⟨fun hv => ?_, fun ⟨s, hs⟩ => ?_⟩⟩
  · obtain ⟨u, hu⟩ := (hB v).mp hv
    exact ⟨u * t⁻¹, by rw [hu, ht, smul_smul, mul_assoc, inv_mul_cancel₀ ht0, mul_one]⟩
  · exact (hB v).mpr ⟨s * t, by rw [hs, ht, smul_smul]⟩

theorem mem_rootVecs_of_line {m : G} (hm : m ∈ M) {x : M₀.E} (hx0 : x ≠ 0)
    (hx : IsLineGen M₀ (conjSubgroup m B) x) : x ∈ rootVecs M₀ M B :=
  ⟨hx0, m, hm, (hx x).mpr ⟨1, (one_smul K x).symm⟩⟩

theorem rootVecs_span {hc0 : Ctx M Q Z B} (hgen : GenByB M Q B)
    (Pk : GlobalModelAction M Q Z K γ M₀) :
    Submodule.span K (rootVecs M₀ M B) = ⊤ := by
  have hle : (⨆ (m : G) (_ : m ∈ M), conjSubgroup m B) ≤
      M₀.lift (Submodule.span K (rootVecs M₀ M B)).toAddSubgroup := by
    refine iSup₂_le fun m hm u hu => ?_
    have hcm := hc0.conj_of_mem hm
    refine ⟨hcm.le hu, ?_⟩
    by_cases h0 : M₀.π u = 0
    · rw [h0]
      exact zero_mem _
    · exact Submodule.subset_span ⟨h0, m, hm, M₀.pi_mem_img hu (hcm.le hu)⟩
  rw [eq_top_iff]
  intro e _
  obtain ⟨u, huQ, rfl⟩ := M₀.π_surj e
  have hu : u ∈ ⨆ (m : G) (_ : m ∈ M), conjSubgroup m B := by
    rw [← hgen]
    exact huQ
  exact (hle hu).2

@[expose] def lbActSet (Pk : GlobalModelAction M Q Z K γ M₀) (X : Subgroup G) :
    Set (M₀.E →ₗ[K] M₀.E) :=
  {T | ∃ r : G, ∃ _ : r ∈ LB M Q X, ∃ hH : r ∈ H0 M Z,
    T = ((Pk.φ ⟨r, hH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)}

theorem lbActSet_fix (Pk : GlobalModelAction M Q Z K γ M₀) {X : Subgroup G}
    (hcX : Ctx M Q Z X) {x : M₀.E}
    (hx : IsLineGen M₀ X x) {T : M₀.E →ₗ[K] M₀.E} (hT : T ∈ lbActSet Pk X) : T x = x := by
  obtain ⟨r, hr, hH, rfl⟩ := hT
  obtain ⟨u, huX, huQ, hu⟩ := (hx x).mpr ⟨1, (one_smul K x).symm⟩
  have hrQ := (hcX.conj_mem_Q_of_mem_M hH.1).1 u huQ
  rw [← hu]
  have h1 := Pk.hφπ ⟨r, hH⟩ u huQ
  have h2 : M₀.π (r * u * r⁻¹) = M₀.π u :=
    (M₀.comm_mem_iff huQ hrQ).mp (hcX.comm_B_mem_Z hr huX)
  rw [h2] at h1
  exact h1.symm

theorem lbActSet_iso (Pk : GlobalModelAction M Q Z K γ M₀) {X : Subgroup G} {T : M₀.E →ₗ[K] M₀.E}
    (hT : T ∈ lbActSet Pk X) (e : M₀.E) : M₀.Qf (T e) = M₀.Qf e := by
  obtain ⟨r, hr, hH, rfl⟩ := hT
  exact Pk.hφiso ⟨r, hH⟩ e

theorem lbActSet_R {hc0 : Ctx M Q Z B} (Pk : GlobalModelAction M Q Z K γ M₀) {X : Subgroup G}
    (hcX : Ctx M Q Z X) {T : M₀.E →ₗ[K] M₀.E} (hT : T ∈ lbActSet Pk X) {y : M₀.E}
    (hy : y ∈ rootVecs M₀ M B) : T y ∈ rootVecs M₀ M B := by
  obtain ⟨r, hr, hH, rfl⟩ := hT
  obtain ⟨hy0, m, hm, u, huB, huQ, rfl⟩ := hy
  have hrM : r ∈ M := hH.1
  have hrQ := (hcX.conj_mem_Q_of_mem_M hrM).1 u huQ
  have hTπ : ((Pk.φ ⟨r, hH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) (M₀.π u) =
      M₀.π (r * u * r⁻¹) := (Pk.hφπ ⟨r, hH⟩ u huQ).symm
  refine ⟨?_, r * m, M.mul_mem hrM hm, ⟨r * u * r⁻¹, ?_, hrQ, hTπ.symm⟩⟩
  · rw [hTπ]
    intro h0
    have h1 : M₀.π u = 0 := by
      have := (Pk.φ ⟨r, hH⟩).map_eq_zero_iff.mp
        (show (Pk.φ ⟨r, hH⟩) (M₀.π u) = 0 from by rw [← hTπ] at h0; simpa using h0)
      exact this
    exact hy0 h1
  · rw [mem_conjSubgroup]
    have e : (r * m)⁻¹ * (r * u * r⁻¹) * (r * m) = m⁻¹ * u * m := by group
    rw [e]
    exact mem_conjSubgroup.mp huB

theorem lbActSet_D {hc0 : Ctx M Q Z B} {n : ℕ} (hB : Stroth34CaseBHyp M Q Z B hc0 n)
    (Pk : GlobalModelAction M Q Z K γ M₀) {mx : G} (hmx : mx ∈ M) {x : M₀.E}
    (hx : IsLineGen M₀ (conjSubgroup mx B) x) {T : M₀.E →ₗ[K] M₀.E}
    (hT : T ∈ lbActSet Pk (conjSubgroup mx B)) {y : M₀.E} (hy : M₀.B y x = 0) :
    T y - y ∈ imgQInfQB M₀ (conjSubgroup mx B) := by
  have hcX := hc0.conj_of_mem hmx
  have hXc := hB.conj hmx
  obtain ⟨r, hr, hH, rfl⟩ := hT
  have hflag := hcX.LB_act_flag hB.hw hB.hn hXc.hno Pk.h hx hr
    (T := ((Pk.φ ⟨r, hH⟩ : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)) (fun z hz => Pk.hφπ ⟨r, hH⟩ z hz)
  exact (hcX.mem_imgQInfQB_iff hB.hw hB.hn hXc.hno Pk.h _).mpr (hflag.2.2 y hy)

open _root_.Classical in
@[expose] noncomputable def lineElt (M₀ : Tim79.QuadModel Q Z K γ) (M B : Subgroup G)
    (ℓ : Submodule K M₀.E) : G :=
  if h : ∃ m ∈ M, ∀ v, v ∈ M₀.img (conjSubgroup m B) ↔ v ∈ ℓ then h.choose else 1

theorem lineElt_spec {M B : Subgroup G} {ℓ : Submodule K M₀.E}
    (hex : ∃ m ∈ M, ∀ v, v ∈ M₀.img (conjSubgroup m B) ↔ v ∈ ℓ) :
    lineElt M₀ M B ℓ ∈ M ∧ ∀ v, v ∈ M₀.img (conjSubgroup (lineElt M₀ M B ℓ) B) ↔ v ∈ ℓ := by
  unfold lineElt
  rw [dif_pos hex]
  exact hex.choose_spec

theorem exists_line_elt {hc0 : Ctx M Q Z B} (Pk : GlobalModelAction M Q Z K γ M₀) {x : M₀.E}
    (hx : x ∈ rootVecs M₀ M B) :
    ∃ m ∈ M, ∀ v, v ∈ M₀.img (conjSubgroup m B) ↔ v ∈ Submodule.span K {x} := by
  obtain ⟨m, hm, hl⟩ := rootVecs_line (hc0 := hc0) Pk hx
  refine ⟨m, hm, fun v => ?_⟩
  rw [hl v, Submodule.mem_span_singleton]
  exact ⟨fun ⟨s, hs⟩ => ⟨s, hs.symm⟩, fun ⟨s, hs⟩ => ⟨s, hs.symm⟩⟩

theorem exists_rootGeom {hc0 : Ctx M Q Z B} {n : ℕ} (hB : Stroth34CaseBHyp M Q Z B hc0 n)
    (Pk : GlobalModelAction M Q Z K γ M₀) : Nonempty (RootGeom M₀) := by
  classical
  obtain ⟨mx, hmxdef⟩ : ∃ mx : M₀.E → G, ∀ x, mx x = lineElt M₀ M B (Submodule.span K {x}) :=
    ⟨_, fun _ => rfl⟩
  have hmx : ∀ x ∈ rootVecs M₀ M B, mx x ∈ M ∧ IsLineGen M₀ (conjSubgroup (mx x) B) x := by
    intro x hx
    obtain ⟨hm, hl⟩ := lineElt_spec (exists_line_elt (hc0 := hc0) Pk hx)
    rw [← hmxdef] at hm hl
    refine ⟨hm, fun v => ?_⟩
    rw [hl v, Submodule.mem_span_singleton]
    exact ⟨fun ⟨s, hs⟩ => ⟨s, hs.symm⟩, fun ⟨s, hs⟩ => ⟨s, hs.symm⟩⟩
  have hDx : ∀ x ∈ rootVecs M₀ M B, x ∈ imgQInfQB M₀ (conjSubgroup (mx x) B) := by
    intro x hx
    obtain ⟨hm, hl⟩ := hmx x hx
    have hcX := hc0.conj_of_mem hm
    have hXc := hB.conj hm
    exact (hcX.mem_imgQInfQB_iff hB.hw hB.hn hXc.hno Pk.h x).mpr
      (M₀.img_mono (le_inf hcX.le hcX.B_le_QB : conjSubgroup (mx x) B ≤ Q ⊓ QB _)
        ((hl x).mpr ⟨1, (one_smul K x).symm⟩))
  refine ⟨{ R := rootVecs M₀ M B
            D := fun x => imgQInfQB M₀ (conjSubgroup (mx x) B)
            Λ := fun x => lbActSet Pk (conjSubgroup (mx x) B)
            R_ne := fun x hx => hx.1
            R_smul := ?_
            R_sing := ?_
            R_span := rootVecs_span (hc0 := hc0) hB.hgen Pk
            D_sing := ?_
            mem_D := hDx
            D_smul := ?_
            D_symm := ?_
            far_exists := ?_
            near_line := ?_
            far_line := ?_
            eich := ?_
            Λ_fix := ?_
            Λ_iso := ?_
            Λ_R := ?_
            Λ_D := ?_
            Fdim := ?_ }⟩
  ·
    intro x hx c hc
    obtain ⟨hm, hl⟩ := hmx x hx
    exact ⟨smul_ne_zero hc hx.1, mx x, hm, (hl _).mpr ⟨c, rfl⟩⟩
  ·
    intro x hx
    obtain ⟨hm, hl⟩ := hmx x hx
    exact ((hc0.conj_of_mem hm).dictB_gen Pk.h hx.1 hl).1
  ·
    intro x hx d hd
    obtain ⟨hm, hl⟩ := hmx x hx
    exact ((hc0.conj_of_mem hm).imgQInfQB_lagr hB.hw hB.hn (hB.conj hm).hno Pk.h).2.2 d hd
  ·
    intro x hx c hc
    show imgQInfQB M₀ (conjSubgroup (mx (c • x)) B) = imgQInfQB M₀ (conjSubgroup (mx x) B)
    rw [hmxdef, hmxdef, Submodule.span_singleton_smul_eq (Ne.isUnit hc)]
  ·
    intro x hx y hy hxy hyD
    obtain ⟨hmxM, hxl⟩ := hmx x hx
    obtain ⟨hmyM, hyl⟩ := hmx y hy
    have hcX := hc0.conj_of_mem hmxM
    have hcY := hc0.conj_of_mem hmyM
    have hXc := hB.conj hmxM
    have hYc := hB.conj hmyM
    have hYle : conjSubgroup (mx y) B ≤ QB (conjSubgroup (mx x) B) :=
      (hcX.le_QB_iff_mem_imgQInfQB hB.hw hB.hn hXc.hno Pk.h hcY hyl).mpr hyD
    have hXle : conjSubgroup (mx x) B ≤ QB (conjSubgroup (mx y) B) := by
      by_cases hXY : conjSubgroup (mx y) B = conjSubgroup (mx x) B
      · rw [hXY]
        exact hcX.B_le_QB
      · exact (hc0.hyp.le_QB_iff_le_QB hcY.conj hcX.conj hXY).mp hYle
    exact (hcY.le_QB_iff_mem_imgQInfQB hB.hw hB.hn hYc.hno Pk.h hcX hxl).mp hXle
  ·
    intro x hx
    obtain ⟨hm, hl⟩ := hmx x hx
    obtain ⟨m', hm', y, hy, hy0, hxy, hyD⟩ := far_exists_local hB Pk hm hl
    exact ⟨y, mem_rootVecs_of_line hm' hy0 hy, hxy, hyD⟩
  ·
    intro x hx y hy hxy hyD κ hne
    obtain ⟨hmxM, hxl⟩ := hmx x hx
    obtain ⟨hmyM, hyl⟩ := hmx y hy
    by_cases hyx : ∃ c : K, y = c • x
    · obtain ⟨c, rfl⟩ := hyx
      have hc : c + κ ≠ 0 := by
        intro h0
        apply hne
        rw [← add_smul, h0, zero_smul]
      rw [← add_smul]
      exact ⟨smul_ne_zero hc hx.1, mx x, hmxM, (hxl _).mpr ⟨c + κ, rfl⟩⟩
    · push Not at hyx
      obtain ⟨m', hm', hmem⟩ := near_line_local hB Pk hmxM hmyM hxl hyl hyD hyx κ
      exact ⟨hne, m', hm', hmem⟩
  ·
    intro x hx y hy hxy hyD κ
    obtain ⟨hmxM, hxl⟩ := hmx x hx
    obtain ⟨hmyM, hyl⟩ := hmx y hy
    obtain ⟨m', hm', hmem⟩ := far_line_local hB Pk hmxM hmyM hx.1 hy.1 hxl hyl hxy hyD κ
    refine ⟨?_, m', hm', hmem⟩
    intro h0
    apply hyD
    have hκ : y = (-κ) • x := by
      rw [neg_smul, eq_neg_iff_add_eq_zero]
      exact h0
    rw [hκ]
    exact (imgQInfQB M₀ (conjSubgroup (mx x) B)).smul_mem _ (hDx x hx)
  ·
    intro x hx
    obtain ⟨hmxM, hxl⟩ := hmx x hx
    obtain ⟨f, hfx, hf⟩ := eich_local hB Pk hmxM hx.1 hxl
    refine ⟨f, hfx, fun y hy hxy hfy => ?_⟩
    obtain ⟨hmyM, hyl⟩ := hmx y hy
    exact hf (mx y) hmyM y hy.1 hyl hxy hfy
  ·
    intro x hx T hT
    obtain ⟨hmxM, hxl⟩ := hmx x hx
    exact lbActSet_fix Pk (hc0.conj_of_mem hmxM) hxl hT
  ·
    intro x hx T hT e
    exact lbActSet_iso Pk hT e
  ·
    intro x hx T hT y hy
    obtain ⟨hmxM, hxl⟩ := hmx x hx
    exact lbActSet_R (hc0 := hc0) Pk (hc0.conj_of_mem hmxM) hT hy
  ·
    intro x hx T hT y hxy
    obtain ⟨hmxM, hxl⟩ := hmx x hx
    exact lbActSet_D hB Pk hmxM hxl hT (by rw [Tim79.QuadModel.B_comm, hxy, neg_zero])
  ·
    intro x hx
    obtain ⟨hmxM, hxl⟩ := hmx x hx
    have hcX := hc0.conj_of_mem hmxM
    have hXc := hB.conj hmxM
    obtain ⟨d, hdS, hfd⟩ := hcX.spure_data hB.hw hB.hn hXc.hno Pk hcX.LB_le_H0_cb hx.1 hxl
    have hSq := hcX.card_Spure_caseB hXc Pk hcX.LB_le_H0_cb hx.1 hxl
    have hq4 : 4 ≤ Nat.card Z := hcX.hyp.q4
    have hKq : Nat.card K = Nat.card Z := Pk.h.card
    have hd1 : d ≤ 1 := by
      have hQpos : 0 < Nat.card Q := Nat.card_pos
      rw [hdS] at hSq
      have h1 : Nat.card K ^ d = Nat.card K ^ 1 := by
        rw [pow_one]
        exact Nat.eq_of_mul_eq_mul_left hQpos hSq
      exact (Nat.pow_right_injective (by omega) h1).le
    obtain ⟨f, hf⟩ := hfd hd1
    refine ⟨f, fun y hxy hy => hf y (by rw [Tim79.QuadModel.B_comm, hxy, neg_zero])
      fun r => hy _ ⟨r, r.2, hcX.LB_le_H0_cb r.2, rfl⟩⟩

end Local

theorem stroth34CaseB : Stroth34CaseBStatement := by
  intro G _ _ M Q Z B hc n hw hn hno hgen hO
  by_contra hS
  have hB : Stroth34CaseBHyp M Q Z B hc n := ⟨hw, hn, hno, hgen, hO, hS⟩
  obtain ⟨m, γ, M₀, hm, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  obtain ⟨P⟩ := exists_rootGeom hB (⟨h, φ, hφπ, hφker, hφiso⟩ : GlobalModelAction M Q Z _ γ M₀)
  have hK : 1 < Nat.card (GaloisField 2 m) := by
    rw [h.card]
    have := hc.hyp.q4
    omega
  have hdim := h.finrank_E hw hK
  exact RootGeom.false_of_dim P (by omega)

end CFSG.RankThree.GF2n.Stroth80

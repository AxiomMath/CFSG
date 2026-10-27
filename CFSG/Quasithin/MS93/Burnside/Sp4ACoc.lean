module

public import CFSG.Quasithin.MS93.S512NCoc
public import CFSG.Quasithin.MS93.S33Faith
public import CFSG.Quasithin.MS93.S4A42Coc
public import CFSG.Quasithin.MS93.S34FFlat

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Abstract

variable {F : Type} [Field F]

theorem burnsideSp4A_odd_nsmul_eq [CharP F 2] {n : ℕ} (hn : Odd n) (v : MSP.V4 F) :
    n • v = v := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, one_nsmul, mul_nsmul, two_nsmul, CharTwo.add_self_eq_zero, nsmul_zero,
    zero_add]

theorem burnsideSp4A_eq_top_of_forall_mulVec_mem {W : Submodule F (MSP.V4 F)} {v : MSP.V4 F}
    (hv : v ≠ 0) (hW : ∀ g : MSP.Sp4 F, MSP.mat g *ᵥ v ∈ W) : W = ⊤ := by
  rw [eq_top_iff]
  intro u _
  by_cases hu : u = 0
  · rw [hu]
    exact W.zero_mem
  obtain ⟨g₁, hg₁⟩ := MSP.exists_map_pt₀_eq (MSP.isPoint_span hv)
  obtain ⟨g₂, hg₂⟩ := MSP.exists_map_pt₀_eq (MSP.isPoint_span hu)
  have hu' : u ∈ (MSP.pt₀ F).map (Matrix.mulVecLin (MSP.mat g₂)) := by
    rw [hg₂]
    exact Submodule.mem_span_singleton_self u
  rw [MSP.mem_map_mulVecLin] at hu'
  have h1 : MSP.mat g₁ *ᵥ (MSP.mat g₂⁻¹ *ᵥ u) ∈ F ∙ v := by
    rw [← hg₁]
    exact MSP.mulVec_mem_map g₁ hu'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
  have h2 : u = c • (MSP.mat (g₂ * g₁⁻¹) *ᵥ v) := by
    rw [← Matrix.mulVec_smul, hc, MSP.mat_mul_mulVec, MSP.mat_inv_mulVec, MSP.mat_mulVec_inv]
  rw [h2]
  exact W.smul_mem c (hW _)

theorem burnsideSp4A_cform_one [Fintype F] [CharP F 2] (B : F) (m : MSP.V4 F) :
    S5.cform B m 1 = 0 := by
  have h := S512N.cform_mul B m 1 1
  rw [mul_one, MSP.mat_one, Matrix.one_mulVec] at h
  exact add_eq_left.mp h.symm

theorem burnsideSp4A_ne_bot_of_rigid [Fintype F] [CharP F 2] {A : Subgroup (MSP.Sp4 F)}
    (hA : S512N.Rigid A) : A ≠ ⊥ := by
  rintro rfl
  refine one_ne_zero (hA 1 0 fun x hx => ?_)
  rw [Subgroup.mem_bot] at hx
  rw [hx]
  exact burnsideSp4A_cform_one 1 0

variable {S : Type*} [Group S] {ρ : S →* MSP.Sp4 F} {H Y P : Subgroup S} {f : S → MSP.V4 F}

theorem burnsideSp4A_cocycle_one
    (hf : ∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + MSP.mat (ρ a) *ᵥ f b) : f 1 = 0 := by
  have := hf 1 H.one_mem 1 H.one_mem
  rw [mul_one, map_one, MSP.mat_one, Matrix.one_mulVec] at this
  exact add_eq_left.mp this.symm

theorem burnsideSp4A_cocycle_conj_ker
    (hf : ∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + MSP.mat (ρ a) *ᵥ f b)
    {a k : S} (ha : a ∈ H) (hk : k ∈ H) (hk1 : ρ k = 1) :
    f (a * k * a⁻¹) = MSP.mat (ρ a) *ᵥ f k := by
  have hai : a⁻¹ ∈ H := H.inv_mem ha
  have h1 := hf a ha (k * a⁻¹) (H.mul_mem hk hai)
  have h2 := hf k hk a⁻¹ hai
  have h3 := hf a ha a⁻¹ hai
  rw [mul_inv_cancel, burnsideSp4A_cocycle_one hf] at h3
  rw [mul_assoc, h1, h2, hk1, MSP.mat_one, Matrix.one_mulVec, Matrix.mulVec_add,
    add_comm (MSP.mat (ρ a) *ᵥ f k), ← add_assoc, ← h3, zero_add]

theorem burnsideSp4A_cocycle_pow_ker
    (hf : ∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + MSP.mat (ρ a) *ᵥ f b)
    {k : S} (hk : k ∈ H) (hk1 : ρ k = 1) (n : ℕ) : f (k ^ n) = n • f k := by
  induction n with
  | zero => rw [pow_zero, burnsideSp4A_cocycle_one hf, zero_nsmul]
  | succ n ih =>
    rw [pow_succ, hf _ (H.pow_mem hk n) k hk, ih, add_nsmul, one_nsmul, map_pow, hk1, one_pow,
      MSP.mat_one, Matrix.one_mulVec]

theorem burnsideSp4A_cocycle_eq_zero_of_ker [CharP F 2]
    (hf : ∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + MSP.mat (ρ a) *ᵥ f b)
    (hYH : Y ≤ H) (hfY : ∀ y ∈ Y, f y = 0) (hρH : ∀ g : MSP.Sp4 F, ∃ a ∈ H, ρ a = g)
    (hP : ∀ k ∈ H, ρ k = 1 → ∃ b : ℕ, Odd b ∧ k ^ b ∈ P)
    (hPY : P ≤ Subgroup.normalizer (Y : Set S)) (hYρ : Y.map ρ ≠ ⊥) {k : S} (hk : k ∈ H)
    (hk1 : ρ k = 1) : f k = 0 := by
  have hfixP : ∀ k ∈ H, ρ k = 1 → k ∈ P → f k ∈ MSP.fixSp (Y.map ρ) := by
    intro k hk hk1 hkP
    rw [MSP.mem_fixSp]
    rintro _ ⟨y, hyY, rfl⟩
    have hc : y * k * y⁻¹ * k⁻¹ ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (hPY hkP) _).mp (Y.inv_mem hyY)
      have hmul := Y.mul_mem hyY this
      simpa [mul_assoc] using hmul
    have hck : y * k * y⁻¹ = (y * k * y⁻¹ * k⁻¹) * k := by group
    have key := burnsideSp4A_cocycle_conj_ker hf (hYH hyY) hk hk1
    rw [hck, hf _ (hYH hc) k hk, hfY _ hc, zero_add] at key
    have hρc : ρ (y * k * y⁻¹ * k⁻¹) = 1 := by
      simp only [map_mul, map_inv, hk1, mul_one, inv_one, mul_inv_cancel]
    rw [hρc, MSP.mat_one, Matrix.one_mulVec] at key
    exact key.symm
  have hfix : ∀ k ∈ H, ρ k = 1 → f k ∈ MSP.fixSp (Y.map ρ) := by
    intro k hk hk1
    obtain ⟨b, hb, hkb⟩ := hP k hk hk1
    have h := hfixP (k ^ b) (H.pow_mem hk b) (by rw [map_pow, hk1, one_pow]) hkb
    rwa [burnsideSp4A_cocycle_pow_ker hf hk hk1 b, burnsideSp4A_odd_nsmul_eq hb] at h
  by_contra hne
  apply hYρ
  have htop : MSP.fixSp (Y.map ρ) = ⊤ := by
    refine burnsideSp4A_eq_top_of_forall_mulVec_mem hne fun g => ?_
    obtain ⟨a, ha, rfl⟩ := hρH g
    rw [← burnsideSp4A_cocycle_conj_ker hf ha hk hk1]
    refine hfix _ (H.mul_mem (H.mul_mem ha hk) (H.inv_mem ha)) ?_
    simp only [map_mul, map_inv, hk1, mul_one, mul_inv_cancel]
  rw [eq_bot_iff]
  rintro _ ⟨y, hyY, rfl⟩
  rw [Subgroup.mem_bot]
  refine MSP.ext_mulVec fun x => ?_
  have hx : x ∈ MSP.fixSp (Y.map ρ) := htop ▸ Submodule.mem_top
  rw [MSP.mat_one, Matrix.one_mulVec]
  exact (MSP.mem_fixSp.mp hx) _ ⟨y, hyY, rfl⟩

theorem burnsideSp4A_exists_coboundary [Fintype F] [CharP F 2] {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hn : 1 ≤ n)
    (hf : ∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + MSP.mat (ρ a) *ᵥ f b)
    (hYH : Y ≤ H) (hfY : ∀ y ∈ Y, f y = 0) (hρH : ∀ g : MSP.Sp4 F, ∃ a ∈ H, ρ a = g)
    (hP : ∀ k ∈ H, ρ k = 1 → ∃ b : ℕ, Odd b ∧ k ^ b ∈ P)
    (hPY : P ≤ Subgroup.normalizer (Y : Set S)) (hYR : S512N.Rigid (Y.map ρ)) :
    ∃ m : MSP.V4 F, ∀ a ∈ H, f a = MSP.mat (ρ a) *ᵥ m - m := by
  have hYρ := burnsideSp4A_ne_bot_of_rigid hYR
  have hker : ∀ k ∈ H, ρ k = 1 → f k = 0 := fun k hk hk1 =>
    burnsideSp4A_cocycle_eq_zero_of_ker hf hYH hfY hρH hP hPY hYρ hk hk1
  choose pre hpreH hpre using hρH
  have hfib : ∀ a ∈ H, f (pre (ρ a)) = f a := by
    intro a ha
    have hk : a⁻¹ * pre (ρ a) ∈ H := H.mul_mem (H.inv_mem ha) (hpreH _)
    have hk1 : ρ (a⁻¹ * pre (ρ a)) = 1 := by rw [map_mul, map_inv, hpre, inv_mul_cancel]
    have := hf a ha _ hk
    rw [mul_inv_cancel_left, hker _ hk hk1, Matrix.mulVec_zero, add_zero] at this
    exact this
  have hcoc : ∀ g₁ g₂ : MSP.Sp4 F,
      f (pre (g₁ * g₂)) = f (pre g₁) + MSP.mat g₁ *ᵥ f (pre g₂) := by
    intro g₁ g₂
    have h12 : pre g₁ * pre g₂ ∈ H := H.mul_mem (hpreH g₁) (hpreH g₂)
    have := hfib _ h12
    rw [map_mul, hpre, hpre] at this
    rw [this, hf _ (hpreH g₁) _ (hpreH g₂), hpre]
  obtain ⟨B, m, hBm⟩ := S5.exists_eq_sqf (φ := fun g => f (pre g)) hcard hn hcoc
  have hB : B = 0 := hYR B m (by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : f (pre (ρ y)) = B • S5.sqf (MSP.mat (ρ y)) + (MSP.mat (ρ y) *ᵥ m - m) :=
      hBm (ρ y)
    rw [hfib y (hYH hy), hfY y hy] at h1
    exact h1.symm)
  refine ⟨m, fun a ha => ?_⟩
  have h1 : f (pre (ρ a)) = B • S5.sqf (MSP.mat (ρ a)) + (MSP.mat (ρ a) *ᵥ m - m) := hBm (ρ a)
  rw [hfib a ha, hB, zero_smul, zero_add] at h1
  exact h1

end Abstract

section Coord

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {A : Subgroup G} {F : Type}
  [Field F] {α : ↥A →* MSP.Sp4 F}

noncomputable def burnsideSp4A_crd
    (c : MSP.NatCoord A (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α) (x : G) :
    MSP.V4 F :=
  c.vec (Classical.epsilon fun u : ↥(Uq M T L) => (u : G)⁻¹ * x ∈ Dq M L)

theorem burnsideSp4A_crd_eq
    (c : MSP.NatCoord A (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α) {x : G}
    (u : ↥(Uq M T L)) (hu : (u : G)⁻¹ * x ∈ Dq M L) : burnsideSp4A_crd c x = c.vec u := by
  set u' : ↥(Uq M T L) := Classical.epsilon fun u : ↥(Uq M T L) => (u : G)⁻¹ * x ∈ Dq M L
  have hu' : (u' : G)⁻¹ * x ∈ Dq M L :=
    Classical.epsilon_spec (p := fun u : ↥(Uq M T L) => (u : G)⁻¹ * x ∈ Dq M L) ⟨u, hu⟩
  show c.vec u' = c.vec u
  have hmem : ((u'⁻¹ * u : ↥(Uq M T L)) : G) ∈
      Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨(u'⁻¹ * u).2, ?_⟩
    have e : ((u'⁻¹ * u : ↥(Uq M T L)) : G) = ((u' : G)⁻¹ * x) * ((u : G)⁻¹ * x)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact (Subgroup.mem_inf.mp ((Dq M L).mul_mem hu' ((Dq M L).inv_mem hu))).2
  have h0 := (c.vec_eq_zero_iff _).2 hmem
  rw [c.vec_mul, c.vec_inv] at h0
  exact neg_add_eq_zero.mp h0

theorem burnsideSp4A_crd_coe
    (c : MSP.NatCoord A (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α)
    (u : ↥(Uq M T L)) : burnsideSp4A_crd c (u : G) = c.vec u :=
  burnsideSp4A_crd_eq c u (by rw [inv_mul_cancel]; exact one_mem _)

theorem burnsideSp4A_crd_one
    (c : MSP.NatCoord A (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α) :
    burnsideSp4A_crd c (1 : G) = 0 := by
  have h1 : burnsideSp4A_crd c (1 : G) = c.vec 1 := burnsideSp4A_crd_coe c 1
  have h2 := c.vec_mul 1 1
  rw [mul_one] at h2
  rw [h1]
  exact add_eq_left.mp h2.symm

theorem burnsideSp4A_exists_of_mem (h : PUHyp M T L) {x : G} (hx : x ∈ Uq M T L ⊔ Dq M L) :
    ∃ u : ↥(Uq M T L), (u : G)⁻¹ * x ∈ Dq M L := by
  have hUD : Uq M T L ≤ Subgroup.normalizer (Dq M L : Set G) :=
    (Uq_le h.L_le).trans (le_normalizer_Dq h.le_normalizer)
  have hx' : x ∈ ((Uq M T L ⊔ Dq M L : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUD] at hx'
  obtain ⟨u, hu, d, hd, rfl⟩ := hx'
  exact ⟨⟨u, hu⟩, by simpa using hd⟩

theorem burnsideSp4A_crd_mul (h : PUHyp M T L)
    (c : MSP.NatCoord A (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α) {x y : G}
    (hx : x ∈ Uq M T L ⊔ Dq M L) (hy : y ∈ Uq M T L ⊔ Dq M L) :
    burnsideSp4A_crd c (x * y) = burnsideSp4A_crd c x + burnsideSp4A_crd c y := by
  obtain ⟨u, hu⟩ := burnsideSp4A_exists_of_mem h hx
  obtain ⟨u', hu'⟩ := burnsideSp4A_exists_of_mem h hy
  have hcomm : (u : G)⁻¹ * x * u' = u' * ((u : G)⁻¹ * x) :=
    (Subgroup.mem_centralizer_iff.mp
      (S34F.pCoreOf_le_centralizer_Uq h (Subgroup.mem_inf.mp hu).1) _ u'.2).symm
  have hmem : ((u * u' : ↥(Uq M T L)) : G)⁻¹ * (x * y) ∈ Dq M L := by
    have e : ((u * u' : ↥(Uq M T L)) : G)⁻¹ * (x * y) =
        (u' : G)⁻¹ * ((u : G)⁻¹ * x * u') * ((u' : G)⁻¹ * y) := by
      simp only [Subgroup.coe_mul]
      group
    rw [e, hcomm, inv_mul_cancel_left]
    exact (Dq M L).mul_mem hu hu'
  rw [burnsideSp4A_crd_eq c (u * u') hmem, burnsideSp4A_crd_eq c u hu,
    burnsideSp4A_crd_eq c u' hu', c.vec_mul]

theorem burnsideSp4A_crd_conj (h : PUHyp M T L) (hAM : A ≤ M)
    (c : MSP.NatCoord A (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α) (a : ↥A)
    {x : G} (hx : x ∈ Uq M T L ⊔ Dq M L) :
    burnsideSp4A_crd c ((a : G) * x * (a : G)⁻¹) = MSP.mat (α a) *ᵥ burnsideSp4A_crd c x := by
  obtain ⟨u, hu⟩ := burnsideSp4A_exists_of_mem h hx
  have haU : (a : G) * u * (a : G)⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_Uq (T := T) h.le_normalizer (hAM a.2)) _).mp
      u.2
  have hmem : (((⟨_, haU⟩ : ↥(Uq M T L)) : G))⁻¹ * ((a : G) * x * (a : G)⁻¹) ∈ Dq M L := by
    have e : (((⟨_, haU⟩ : ↥(Uq M T L)) : G))⁻¹ * ((a : G) * x * (a : G)⁻¹) =
        (a : G) * ((u : G)⁻¹ * x) * (a : G)⁻¹ := by
      show ((a : G) * u * (a : G)⁻¹)⁻¹ * ((a : G) * x * (a : G)⁻¹) = _
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_Dq h.le_normalizer (hAM a.2)) _).mp hu
  rw [burnsideSp4A_crd_eq c _ hmem, burnsideSp4A_crd_eq c u hu, c.vec_conj a u haU]

theorem burnsideSp4A_inv_mul_mem_dq (h : PUHyp M T L)
    (c : MSP.NatCoord A (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α) {x : G}
    (hx : x ∈ Uq M T L ⊔ Dq M L) (v : ↥(Uq M T L)) (hv : burnsideSp4A_crd c x = c.vec v) :
    (v : G)⁻¹ * x ∈ Dq M L := by
  obtain ⟨u, hu⟩ := burnsideSp4A_exists_of_mem h hx
  rw [burnsideSp4A_crd_eq c u hu] at hv
  have h0 : c.vec (v⁻¹ * u) = 0 := by rw [c.vec_mul, c.vec_inv, hv, neg_add_cancel]
  rw [c.vec_eq_zero_iff] at h0
  have hvuD : ((v⁻¹ * u : ↥(Uq M T L)) : G) ∈ Dq M L :=
    Subgroup.mem_inf.mpr ⟨h.Uq_le_Xq.trans (Xq_le_pCoreOf M) (v⁻¹ * u).2,
      (Subgroup.mem_inf.mp h0).2⟩
  have e : ((v⁻¹ * u : ↥(Uq M T L)) : G) * ((u : G)⁻¹ * x) = (v : G)⁻¹ * x := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [← e]
  exact (Dq M L).mul_mem hvuD hu

theorem burnsideSp4A_crd_comm_mul (h : PUHyp M T L) (hAM : A ≤ M)
    (c : MSP.NatCoord A (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α) {w : G}
    (a b : ↥A) (ha : ⁅(a : G), w⁆ ∈ Uq M T L ⊔ Dq M L) (hb : ⁅(b : G), w⁆ ∈ Uq M T L ⊔ Dq M L) :
    burnsideSp4A_crd c ⁅((a * b : ↥A) : G), w⁆ =
      burnsideSp4A_crd c ⁅(a : G), w⁆ + MSP.mat (α a) *ᵥ burnsideSp4A_crd c ⁅(b : G), w⁆ := by
  have hMN : M ≤ Subgroup.normalizer ((Uq M T L ⊔ Dq M L : Subgroup G) : Set G) :=
    CFSG.Quasithin.MS93.le_normalizer_sup (le_normalizer_Uq h.le_normalizer)
      (le_normalizer_Dq h.le_normalizer)
  have hrw : ⁅((a * b : ↥A) : G), w⁆ = (a : G) * ⁅(b : G), w⁆ * (a : G)⁻¹ * ⁅(a : G), w⁆ := by
    simp only [Subgroup.coe_mul, commutatorElement_def]
    group
  have hconj : (a : G) * ⁅(b : G), w⁆ * (a : G)⁻¹ ∈ Uq M T L ⊔ Dq M L :=
    (Subgroup.mem_normalizer_iff.mp (hMN (hAM a.2)) _).mp hb
  rw [hrw, burnsideSp4A_crd_mul h c hconj ha, burnsideSp4A_crd_conj h hAM c a hb, add_comm]

theorem burnsideSp4A_eq_one_of_mem_centralizer
    (c : MSP.NatCoord A (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α) (a : ↥A)
    (ha : (a : G) ∈ Subgroup.centralizer (Uq M T L : Set G)) : α a = 1 := by
  refine MSP.ext_mulVec fun v => ?_
  obtain ⟨u, rfl⟩ := c.exists_vec_eq v
  have hu : (u : G) = (a : G) * u * (a : G)⁻¹ := by
    rw [← Subgroup.mem_centralizer_iff.mp ha u u.2, mul_inv_cancel_right]
  have h1 : c.vec u = MSP.mat (α a) *ᵥ c.vec u := c.equiv a u u hu
  rw [MSP.mat_one, Matrix.one_mulVec]
  exact h1.symm

theorem burnsideSp4A_mem_actTriv_of_eq_one (h : PUHyp M T L) (hAM : A ≤ M)
    (c : MSP.NatCoord A (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α) (a : ↥A)
    (ha : α a = 1) : (a : G) ∈ S33.actTriv h := by
  refine (S33.mem_actTriv h).mpr ⟨hAM a.2, fun u hu => ?_⟩
  have hconj : (a : G) * u * (a : G)⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_Uq (T := T) h.le_normalizer (hAM a.2)) u).mp
      hu
  have hcomm := c.vec_commutator a ⟨u, hu⟩ hconj
  rw [ha, MSP.mat_one, Matrix.one_mulVec, sub_self, c.vec_eq_zero_iff] at hcomm
  have e : ⁅u, (a : G)⁆ = ((a : G) * u * (a : G)⁻¹ * u⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.inv_mem _ (Subgroup.mem_inf.mp hcomm).2

theorem burnsideSp4A_mem_centralizer_of_eq_one (h : PUHyp M T L) (hAM : A ≤ M)
    (c : MSP.NatCoord A (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α) (a : ↥A)
    (ha : α a = 1) : (a : G) ∈ Subgroup.centralizer (Uq M T L : Set G) :=
  S33.centralizer_of_actTriv h (burnsideSp4A_mem_actTriv_of_eq_one h hAM c a ha)

end Coord

section CommSub

variable {G : Type} [Group G]

def burnsideSp4A_commSub {K N : Subgroup G} (hKN : K ≤ Subgroup.normalizer (N : Set G))
    (w : G) : Subgroup ↥K where
  carrier := {a | ⁅(a : G), w⁆ ∈ N}
  mul_mem' := by
    intro a b ha hb
    have e : ⁅((a * b : ↥K) : G), w⁆ = (a : G) * ⁅(b : G), w⁆ * (a : G)⁻¹ * ⁅(a : G), w⁆ := by
      simp only [Subgroup.coe_mul, commutatorElement_def]
      group
    show ⁅((a * b : ↥K) : G), w⁆ ∈ N
    rw [e]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKN a.2) _).mp hb) ha
  one_mem' := by
    show ⁅(1 : G), w⁆ ∈ N
    rw [commutatorElement_one_left]
    exact N.one_mem
  inv_mem' := by
    intro a ha
    have e : ⁅((a⁻¹ : ↥K) : G), w⁆ = (a : G)⁻¹ * ⁅(a : G), w⁆⁻¹ * ((a : G)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_inv, commutatorElement_def]
      group
    show ⁅((a⁻¹ : ↥K) : G), w⁆ ∈ N
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem a.2)) _).mp (N.inv_mem ha)

end CommSub

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideSp4A_mem_dq_of_commutator (h : PUHyp M T L) {x : G} (hxQ : x ∈ pCoreOf 2 M)
    (hxL : ∀ l ∈ L, ⁅l, x⁆ ∈ Dq M L) : x ∈ Dq M L := by
  refine Subgroup.mem_inf.mpr ⟨hxQ, ?_⟩
  have hxM : x ∈ M := pCoreOf_le' M hxQ
  have hcl : ⁅Subgroup.closure ({x} : Set G), L⁆ ≤ Dq M L := by
    refine S4A.commutator_closure_le_of (fun s hs l hl => ?_) ?_
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (hxL l hl)
    · rw [Subgroup.closure_le]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst hs
      exact le_normalizer_Dq h.le_normalizer hxM
  have h1 : ⁅⁅Subgroup.closure ({x} : Set G), L⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hcl.trans inf_le_right
  have h2 : ⁅⁅L, Subgroup.closure ({x} : Set G)⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm L]
    exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  rw [h.perfect, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
  exact Subgroup.le_centralizer_iff.mp h3 (Subgroup.subset_closure rfl)

theorem burnsideSp4A_mem_uq_sup_dq (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    [CharP F 2] (hcard : Fintype.card F = 2 ^ k) (hk : 1 ≤ k)
    {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSp 2 F)} (hφs : Function.Surjective φ)
    (hφ : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L)
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) φ false 1)
    {w : G} (hwQ : w ∈ pCoreOf 2 M) (hwL : ∀ l ∈ L, ⁅l, w⁆ ∈ Uq M T L ⊔ Dq M L)
    {Y : Subgroup G} (hYK : Y ≤ L ⊔ pCoreOf 2 M)
    (hQY : pCoreOf 2 M ≤ Subgroup.normalizer (Y : Set G))
    (hYw : ∀ y ∈ Y, y * w = w * y)
    (hYR : S512N.Rigid ((Y.subgroupOf (L ⊔ pCoreOf 2 M)).map φ)) :
    w ∈ Uq M T L ⊔ Dq M L := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hφ
  have hKM : L ⊔ pCoreOf 2 M ≤ M := sup_le h.L_le (pCoreOf_le' M)
  have hMN : M ≤ Subgroup.normalizer ((Uq M T L ⊔ Dq M L : Subgroup G) : Set G) :=
    CFSG.Quasithin.MS93.le_normalizer_sup (le_normalizer_Uq h.le_normalizer)
      (le_normalizer_Dq h.le_normalizer)
  set H : Subgroup ↥(L ⊔ pCoreOf 2 M) := burnsideSp4A_commSub (hKM.trans hMN) w
  set f : ↥(L ⊔ pCoreOf 2 M) → MSP.V4 F := fun a => burnsideSp4A_crd c ⁅(a : G), w⁆
  have hf : ∀ a ∈ H, ∀ b ∈ H, f (a * b) = f a + MSP.mat (φ a) *ᵥ f b :=
    fun a ha b hb => burnsideSp4A_crd_comm_mul h hKM c a b ha hb
  have hρH : ∀ g : MSP.Sp4 F, ∃ a ∈ H, φ a = g := by
    intro g
    obtain ⟨s, rfl⟩ := hφs g
    have hs : (s : G) ∈ ((L ⊔ pCoreOf 2 M : Subgroup G) : Set G) := s.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (h.L_le.trans (le_normalizer_pCoreOf M))] at hs
    obtain ⟨l, hl, q, hq, hlq⟩ := hs
    have hlK : l ∈ L ⊔ pCoreOf 2 M := Subgroup.mem_sup_left hl
    have hqK : q ∈ L ⊔ pCoreOf 2 M := Subgroup.mem_sup_right hq
    refine ⟨⟨l, hlK⟩, hwL l hl, ?_⟩
    have hq1 : φ ⟨q, hqK⟩ = 1 :=
      burnsideSp4A_eq_one_of_mem_centralizer c ⟨q, hqK⟩ (S34F.pCoreOf_le_centralizer_Uq h hq)
    have hs' : s = ⟨l, hlK⟩ * ⟨q, hqK⟩ := Subtype.ext hlq.symm
    rw [hs', map_mul, hq1, mul_one]
  have hYw' : ∀ y ∈ Y, ⁅y, w⁆ = 1 := fun y hy => by
    rw [commutatorElement_def, hYw y hy, mul_inv_cancel_right, mul_inv_cancel]
  have hYH : Y.subgroupOf (L ⊔ pCoreOf 2 M) ≤ H := fun y hy => by
    show ⁅((y : ↥(L ⊔ pCoreOf 2 M)) : G), w⁆ ∈ Uq M T L ⊔ Dq M L
    rw [hYw' _ (Subgroup.mem_subgroupOf.mp hy)]
    exact Subgroup.one_mem _
  have hfY : ∀ y ∈ Y.subgroupOf (L ⊔ pCoreOf 2 M), f y = 0 := fun y hy => by
    show burnsideSp4A_crd c ⁅((y : ↥(L ⊔ pCoreOf 2 M)) : G), w⁆ = 0
    rw [hYw' _ (Subgroup.mem_subgroupOf.mp hy)]
    exact burnsideSp4A_crd_one c
  have hP : ∀ x ∈ H, φ x = 1 →
      ∃ b : ℕ, Odd b ∧ x ^ b ∈ (pCoreOf 2 M).subgroupOf (L ⊔ pCoreOf 2 M) := by
    intro x _ hx1
    obtain ⟨e, b, hb, heb⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x : G)).ne'
    refine ⟨b, hb, ?_⟩
    have hxb : ((x ^ b : ↥(L ⊔ pCoreOf 2 M)) : G) = (x : G) ^ b := by simp
    rw [Subgroup.mem_subgroupOf, hxb]
    have hxC := burnsideSp4A_mem_centralizer_of_eq_one h hKM c x hx1
    refine S4A.mem_pCoreOf_of_centralizer_Uq h (pow_mem (hKM x.2) b) (pow_mem hxC b) ⟨e, ?_⟩
    rw [← pow_mul, mul_comm, ← heb, pow_orderOf_eq_one]
  have hPY : (pCoreOf 2 M).subgroupOf (L ⊔ pCoreOf 2 M) ≤
      Subgroup.normalizer ((Y.subgroupOf (L ⊔ pCoreOf 2 M) : Subgroup _) :
        Set ↥(L ⊔ pCoreOf 2 M)) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hQY (Subgroup.mem_subgroupOf.mp hq)) _
  obtain ⟨m, hm⟩ := burnsideSp4A_exists_coboundary hcard hk hf hYH hfY hρH hP hPY hYR
  obtain ⟨u₀, hu₀⟩ := c.exists_vec_eq m
  have hcomm_l : ∀ l ∈ L, ⁅l, (u₀ : G)⁻¹ * w⁆ ∈ Dq M L := by
    intro l hl
    have hlK : l ∈ L ⊔ pCoreOf 2 M := Subgroup.mem_sup_left hl
    have hlu : l * (u₀ : G) * l⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_Uq (T := T) h.le_normalizer (h.L_le hl)) _).mp u₀.2
    let v : ↥(Uq M T L) := ⟨l * u₀ * l⁻¹ * (u₀ : G)⁻¹, mul_mem hlu (inv_mem u₀.2)⟩
    have hvG : (v : G) = l * u₀ * l⁻¹ * (u₀ : G)⁻¹ := rfl
    have hvv : c.vec v = MSP.mat (φ ⟨l, hlK⟩) *ᵥ c.vec u₀ - c.vec u₀ :=
      c.vec_commutator ⟨l, hlK⟩ u₀ hlu
    have hfl : burnsideSp4A_crd c ⁅l, w⁆ = MSP.mat (φ ⟨l, hlK⟩) *ᵥ m - m :=
      hm ⟨l, hlK⟩ (hwL l hl)
    have hvx : (v : G)⁻¹ * ⁅l, w⁆ ∈ Dq M L :=
      burnsideSp4A_inv_mul_mem_dq h c (hwL l hl) v (by rw [hfl, hvv, hu₀])
    have hrw : ⁅l, (u₀ : G)⁻¹ * w⁆ = (u₀ : G)⁻¹ * ((v : G)⁻¹ * ⁅l, w⁆) * ((u₀ : G)⁻¹)⁻¹ := by
      rw [hvG]
      simp only [commutatorElement_def]
      group
    rw [hrw]
    exact (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_Dq h.le_normalizer (inv_mem (Uq_le h.L_le u₀.2))) _).mp hvx
  have hw'Q : (u₀ : G)⁻¹ * w ∈ pCoreOf 2 M :=
    mul_mem (inv_mem (h.Uq_le_Xq.trans (Xq_le_pCoreOf M) u₀.2)) hwQ
  have hw'D := burnsideSp4A_mem_dq_of_commutator h hw'Q hcomm_l
  have hmem : (u₀ : G) * ((u₀ : G)⁻¹ * w) ∈ Uq M T L ⊔ Dq M L :=
    mul_mem (Subgroup.mem_sup_left u₀.2) (Subgroup.mem_sup_right hw'D)
  rwa [mul_inv_cancel_left] at hmem

end Main

end CFSG.Quasithin.MS93.S4L

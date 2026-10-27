module

public import CFSG.Quasithin.Background.G12Final
public import CFSG.Foundations.HigherElementaryThompson

public section

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open

section Vocab

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def Qv (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (v : V) :
    Subgroup (GLV V) :=
  QSub G v (perp B v)

@[expose] def QFaithfulOnW (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (v : V) :
    Prop :=
  ∀ x ∈ Qv B G v, (∀ w ∈ perp B v, x w = w) → x = 1

@[expose] def TransOnNonzero (G : Subgroup (GLV V)) : Prop :=
  ∀ x y : V, x ≠ 0 → y ≠ 0 → ∃ g ∈ G, g x = y

@[expose] def IsRegularAt (Y : Subgroup (GLV V)) (x : V) : Prop :=
  ∀ g ∈ Y, g x = x → g = 1

@[expose] def FullAxisTransvOnQuot (B : LinearMap.BilinForm (ZMod 2) V) (v : V)
    (Y : Subgroup (GLV V)) : Prop :=
  (∀ y ∈ Y, ∃ c ∈ perp B v, ∀ x : V, y x - x - B x v • c ∈ Submodule.span (ZMod 2) {v}) ∧
  ∀ c ∈ perp B v, ∃ y ∈ Y, ∀ x : V, y x - x - B x v • c ∈ Submodule.span (ZMod 2) {v}

@[expose] def spStab (B : LinearMap.BilinForm (ZMod 2) V) (v : V) : Subgroup (GLV V) :=
  spSub B ⊓ MulAction.stabilizer (GLV V) v

@[expose] def IsQuadFormFor (B : LinearMap.BilinForm (ZMod 2) V) (q : V → ZMod 2) : Prop :=
  ∀ x y : V, q (x + y) = q x + q y + B x y

@[expose] def Concl121 (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (v : V) : Prop :=
  G = spSub B ∨
  (∃ q : V → ZMod 2, IsQuadFormFor B q ∧ (G = orthSub q ∨ G = omegaSub B q) ∧
    ∀ w : V, (∃ g ∈ G, w = g v) ↔ (w ≠ 0 ∧ q w = 0)) ∨
  (Module.finrank (ZMod 2) V = 4 ∧
    (G = ⁅spSub B, spSub B⁆ ∨
      (Nonempty (↥G ≃* Equiv.Perm (Fin 5)) ∧
        ∃ A : Subgroup (GLV V), A ≤ G ∧ IsL24ModuleFor A)))

structure HypG121 (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V) :
    Prop where
  symp : IsSymplectic B
  le_sp : G ≤ spSub B
  u_mem : IsStarVec B G u
  v_mem : IsStarVec B G v
  uv : B u v ≠ 0
  dim : 4 ≤ Module.finrank (ZMod 2) V

structure MinCx (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V) : Prop where
  hyp : HypG121 B G u v
  u_mem : u ∈ orbitSet G v
  not_concl : ¬ Concl121 B G v
  minimal : ∀ (V' : Type) [AddCommGroup V'] [Module (ZMod 2) V'] [Finite V']
    (B' : LinearMap.BilinForm (ZMod 2) V') (G' : Subgroup (GLV V')) (u' v' : V'),
    HypG121 B' G' u' v' → Module.finrank (ZMod 2) V' < Module.finrank (ZMod 2) V →
      Concl121 B' G' v'

open Classical in
@[expose] noncomputable def qOrb (G : Subgroup (GLV V)) (v : V) : V → ZMod 2 :=
  fun z => if z = 0 ∨ z ∈ orbitSet G v then 0 else 1

@[expose] def IsNonsingPair (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (v : V)
    (e : ZMod 2) (x y : V) : Prop :=
  qOrb G v x = 1 ∧ qOrb G v y = 1 ∧ x ≠ y ∧ B x y = e

end Vocab

section Hat

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {Û : Type} [AddCommGroup Û] [Module (ZMod 2) Û]

structure HatModel (B : LinearMap.BilinForm (ZMod 2) V) (w : V) (π : ↥(perp B w) →ₗ[ZMod 2] Û) :
    Prop where
  surj : Function.Surjective π
  ker : ∀ x : ↥(perp B w), π x = 0 ↔ ((x : V) = 0 ∨ (x : V) = w)

open Classical in
@[expose] noncomputable def hatOf (B : LinearMap.BilinForm (ZMod 2) V) (w : V)
    (π : ↥(perp B w) →ₗ[ZMod 2] Û) (x : V) : Û :=
  if h : x ∈ perp B w then π ⟨x, h⟩ else 0

@[expose] def HatForm (B : LinearMap.BilinForm (ZMod 2) V) (w : V) (π : ↥(perp B w) →ₗ[ZMod 2] Û)
    (B' : LinearMap.BilinForm (ZMod 2) Û) : Prop :=
  ∀ x y : ↥(perp B w), B' (π x) (π y) = B (x : V) (y : V)

@[expose] def Gstar (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (w : V)
    (π : ↥(perp B w) →ₗ[ZMod 2] Û) : Subgroup (GLV Û) :=
  Subgroup.closure {φ : GLV Û | ∃ g ∈ G, g w = w ∧
    ∀ x y : ↥(perp B w), g (x : V) = (y : V) → φ (π x) = π y}

@[expose] def HatQuadProp (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (v w : V)
    (π : ↥(perp B w) →ₗ[ZMod 2] Û) (B' : LinearMap.BilinForm (ZMod 2) Û) (qw : Û → ZMod 2) : Prop :=
  IsQuadFormFor B' qw ∧
  (Gstar B G w π = orthSub qw ∨ Gstar B G w π = omegaSub B' qw) ∧
  {z : Û | z ≠ 0 ∧ qw z = 0} = {z : Û | ∃ g ∈ G, g w = w ∧ z = hatOf B w π (g v)}

end Hat

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.ASVolI.ChG

@[expose] def G_12_1 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    HypG121 B G u v → Concl121 B G v

theorem as_G_12_1 : G_12_1 :=
  fun V _ _ _ B G u v h => g12_1 V B G u v h.symp h.le_sp h.u_mem h.v_mem h.uv h.dim

private theorem g12h_qv_rep {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {G : Subgroup (GLV V)} {v : V}
    (h : IsSymplectic B) (hG : G ≤ spSub B) (hv : IsStarVec B G v)
    {g : GLV V} (hg : g ∈ Qv B G v) : ∃ (a : V) (c : ZMod 2), B v a = 0 ∧ g = radE B v a c := by
  obtain ⟨_, hvp, hFT⟩ := hv
  obtain ⟨f, hf0, hfu⟩ := hFT.1 g hg
  obtain ⟨a, hva, ha⟩ := h.exists_rep_perp hvp f hf0
  obtain ⟨c, hc⟩ := eq_radE_of_fix h hva (hG hg.1) (fun u hu => by
    have h1 := hfu ⟨u, hu⟩
    have h2 := ha ⟨u, hu⟩
    simp only at h1 h2
    rw [h1, h2])
  exact ⟨a, c, hva, hc⟩

private theorem g12h_exists_pair {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} (h : IsSymplectic B) {w b : V}
    (hbn : b ∉ Submodule.span (ZMod 2) {w}) : ∃ a, B w a = 0 ∧ B b a = 1 := by
  by_contra hcon
  push_neg at hcon
  apply hbn
  have hmem : b ∈ B.orthogonal (perp B w) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [h.symm' n b]
    exact (g12_eq_zero_or_one (B b n)).resolve_right (hcon n (mem_perp_iff.1 hn))
  rw [IsSymplectic.orthogonal_perp h w] at hmem
  exact hmem

private theorem g12h_perp_exists {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} (h : IsSymplectic B) {w : V} (hw : w ≠ 0)
    (hd : 4 ≤ Module.finrank (ZMod 2) V) :
    ∃ b, B w b = 0 ∧ b ∉ Submodule.span (ZMod 2) {w} := by
  by_contra hcon
  push_neg at hcon
  have hle : perp B w ≤ Submodule.span (ZMod 2) {w} :=
    fun b hb => hcon b (mem_perp_iff.1 hb)
  have h1 := Submodule.finrank_mono hle
  rw [finrank_span_singleton hw] at h1
  have h2 := h.finrank_perp hw
  omega

private theorem g12h_span_apply {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {B : LinearMap.BilinForm (ZMod 2) V} (h : IsSymplectic B) {v : V} (t c : ZMod 2) (y : V) :
    radE B v (t • v) c y = y + (c * B y v) • v := by
  have hva : B v (t • v) = 0 := by rw [map_smul, h.1 v, smul_zero]
  have key : ∀ p q r : ZMod 2, p * q + (q * p + r * p) = r * p := by decide
  rw [radE_apply h hva]
  simp only [map_smul, smul_eq_mul, smul_smul]
  rw [add_assoc, ← add_smul, key]

private theorem g12h_fixW {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {B : LinearMap.BilinForm (ZMod 2) V} (h : IsSymplectic B) {v a y : V} {c t : ZMod 2}
    (hva : B v a = 0) (hyv : B y v = 1) (hz : radE B v a c y = y + t • v) :
    ∀ w ∈ perp B v, B w a = 0 := by
  intro w hw
  have hwv : B w v = 0 := by rw [h.symm' w v]; exact mem_perp_iff.1 hw
  rw [radE_apply h hva, hyv, one_smul, mul_one, add_assoc] at hz
  have hz' := add_left_cancel hz
  have := congrArg (B w) hz'
  simpa [map_add, map_smul, hwv] using this

private theorem g12h_fix_perp {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {B : LinearMap.BilinForm (ZMod 2) V} (h : IsSymplectic B) {v a : V} (c : ZMod 2)
    (hva : B v a = 0) (hBa : ∀ w ∈ perp B v, B w a = 0) :
    ∀ w ∈ perp B v, radE B v a c w = w := by
  intro w hw
  have hwv : B w v = 0 := by rw [h.symm' w v]; exact mem_perp_iff.1 hw
  rw [radE_apply h hva, hwv, hBa w hw]
  simp

private theorem g12h_perp_sub {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {G : Subgroup (GLV V)} {w : V}
    (h : IsSymplectic B) (hG : G ≤ spSub B) (hd : 4 ≤ Module.finrank (ZMod 2) V)
    (hw : IsStarVec B G w) {J : Submodule (ZMod 2) V}
    (hJ : ∀ k ∈ Qv B G w, ∀ y ∈ J, k y ∈ J) {x : V} (hx : x ∈ J) (hxw : B x w = 1) :
    ∀ z, B w z = 0 → z ∈ J := by
  have hex : ∀ a : V, B w a = 0 → ∃ c : ZMod 2, radE B w a c ∈ G :=
    fun a ha => ((isStarVec_iff_rad h hG).1 hw).2 a ha
  choose! cc hcc using hex
  have hQ : ∀ a, B w a = 0 → radE B w a (cc a) ∈ Qv B G w :=
    fun a ha => radE_mem_QSub h ha (hcc a ha)
  have hφ : ∀ a, B w a = 0 → a + (B x a + cc a) • w ∈ J := by
    intro a ha
    have h1 := hJ _ (hQ a ha) x hx
    have h2 : radE B w a (cc a) x = x + (a + (B x a + cc a) • w) := by
      rw [radE_apply h ha, hxw, one_smul, mul_one]
      abel
    rw [h2] at h1
    simpa using J.sub_mem h1 hx
  obtain ⟨b, hbw, hbn⟩ := g12h_perp_exists h hw.1 hd
  obtain ⟨a, ha, hba⟩ := g12h_exists_pair h hbn
  have hzJ := hφ b hbw
  have hwJ : w ∈ J := by
    have h3 := hJ _ (hQ a ha) _ hzJ
    have hzw : B (b + (B x b + cc b) • w) w = 0 := by
      simp [map_add, map_smul, h.1 w, h.symm' b w, hbw]
    have hza : B (b + (B x b + cc b) • w) a = 1 := by
      simp [map_add, map_smul, ha, hba]
    have h4 : radE B w a (cc a) (b + (B x b + cc b) • w) = (b + (B x b + cc b) • w) + w := by
      rw [radE_apply h ha, hzw, hza]
      simp
    rw [h4] at h3
    simpa using J.sub_mem h3 hzJ
  intro z hz
  have h5 := hφ z hz
  have h6 := J.sub_mem h5 (J.smul_mem (B x z + cc z) hwJ)
  simpa using h6

private theorem g12h_top {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {G : Subgroup (GLV V)} {w : V}
    (h : IsSymplectic B) (hG : G ≤ spSub B) (hd : 4 ≤ Module.finrank (ZMod 2) V)
    (hw : IsStarVec B G w) {J : Submodule (ZMod 2) V}
    (hJ : ∀ k ∈ Qv B G w, ∀ y ∈ J, k y ∈ J) {x : V} (hx : x ∈ J) (hxw : B x w = 1) (y : V) :
    y ∈ J := by
  have hp := g12h_perp_sub h hG hd hw hJ hx hxw
  have h1 := hp (y - B y w • x) (by
    rw [map_sub, map_smul, h.symm' w y, h.symm' w x, hxw, smul_eq_mul, mul_one]
    exact sub_self _)
  have h2 := J.add_mem h1 (J.smul_mem (B y w) hx)
  simpa using h2

private theorem g12h_trans_of_all {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {G : Subgroup (GLV V)} {v : V}
    (h : IsSymplectic B) (hG : G ≤ spSub B) (hv0 : v ≠ 0)
    (hall : ∀ x : V, x ∉ perp B v → x ∈ orbitSet G v) : TransOnNonzero G := by
  have hfar : ∀ y, B y v = 1 → y ∈ orbitSet G v := by
    intro y hy
    apply hall
    intro hm
    have h0 := mem_perp_iff.1 hm
    rw [h.symm' v y, hy] at h0
    exact one_ne_zero h0
  have hO := orbit_eq_of_far h hG hv0 hfar
  intro x y hx hy
  obtain ⟨g1, hg1, hg1x⟩ := hO x hx
  obtain ⟨g2, hg2, hg2y⟩ := hO y hy
  refine ⟨g2 * g1⁻¹, G.mul_mem hg2 (G.inv_mem hg1), ?_⟩
  rw [hg1x]
  simp [hg2y]

private theorem g12h_orb_mem {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {G : Subgroup (GLV V)} {v : V} {k : GLV V} (hk : k ∈ G) {w : V}
    (hw : w ∈ orbitSet G v) : k w ∈ orbitSet G v := by
  obtain ⟨g, hg, rfl⟩ := hw
  exact ⟨k * g, G.mul_mem hk hg, rfl⟩

@[expose] def G_12_2 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    HypG121 B G u v →
      (∀ x ∈ Qv B G v, x ≠ 1 → ∀ y : V, x y = y → y ∈ perp B v) ∧
      ((QFaithfulOnW B G v ∧ pRank 2 (Qv B G v) = Module.finrank (ZMod 2) V - 2) ∨
        (Qv B G v = pCoreOf 2 (spStab B v) ∧
          pRank 2 (Qv B G v) = Module.finrank (ZMod 2) V - 1 ∧
          ∃ t ∈ Qv B G v, ∀ x : V, t x = x + B x v • v)) ∧
      FullAxisTransvOnQuot B v (Qv B G v)

private instance g12h2_finite_glv {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Finite (GLV V) :=
  Finite.of_injective _ DFunLike.coe_injective

private theorem g12h2_stab_perp {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {B : LinearMap.BilinForm (ZMod 2) V} {v : V} {g : GLV V} (hg : g ∈ spStab B v)
    {x : V} (hx : x ∈ perp B v) : g x ∈ perp B v := by
  have hgB : ∀ x y : V, B (g x) (g y) = B x y := hg.1
  have hgv : g v = v := MulAction.mem_stabilizer_iff.1 hg.2
  rw [mem_perp_iff] at hx ⊢
  have h1 := hgB v x
  rw [hgv, hx] at h1
  exact h1

private theorem g12h2_mapQ_le {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {v : V}
    {g : GLV V} (hgv : g v = v) :
    Submodule.span (ZMod 2) {v} ≤
      (Submodule.span (ZMod 2) {v}).comap ((g : GLV V) : V →ₗ[ZMod 2] V) := by
  rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap]
  show g v ∈ Submodule.span (ZMod 2) {v}
  rw [hgv]
  exact Submodule.mem_span_singleton_self v

private theorem g12h2_W_irr {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {v : V} (h : IsSymplectic B)
    {U : Submodule (ZMod 2) V} {x : V} (hxU : x ∈ U)
    (hxS : x ∉ Submodule.span (ZMod 2) {v})
    (hcl : ∀ p ∈ perp B v, x + B x p • p ∈ U) : perp B v ≤ U := by
  obtain ⟨a, hva, hxa⟩ := g12h_exists_pair h hxS
  have haW : a ∈ perp B v := mem_perp_iff.2 hva
  have step1 : ∀ p ∈ perp B v, B x p = 1 → p ∈ U := by
    intro p hp hxp
    have h1 := hcl p hp
    rw [hxp, one_smul] at h1
    simpa using U.sub_mem h1 hxU
  intro w hw
  rcases g12_eq_zero_or_one (B x w) with h0 | h1
  · have hwa : w + a ∈ perp B v := (perp B v).add_mem hw haW
    have hxwa : B x (w + a) = 1 := by simp [h0, hxa]
    simpa using U.sub_mem (step1 (w + a) hwa hxwa) (step1 a haW hxa)
  · exact step1 w hw h1

private theorem g12h2_fixed_coset {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {v : V} (hv : v ≠ 0) (hd : 2 ≤ Module.finrank (ZMod 2) V)
    (N : Subgroup (GLV V)) (hN : ∀ n ∈ N, ∃ k : ℕ, n ^ 2 ^ k = 1) (hNv : ∀ n ∈ N, n v = v) :
    ∃ a : V, a ∉ Submodule.span (ZMod 2) {v} ∧
      ∀ n ∈ N, n a - a ∈ Submodule.span (ZMod 2) {v} := by
  classical
  haveI : Module.Finite (ZMod 2) V := (Module.finite_iff_finite (R := ZMod 2)).2 inferInstance
  haveI : Finite (V ⧸ Submodule.span (ZMod 2) {v}) :=
    Finite.of_surjective (Submodule.Quotient.mk : V → V ⧸ Submodule.span (ZMod 2) {v})
      (Submodule.Quotient.mk_surjective _)
  letI : MulAction ↥N (V ⧸ Submodule.span (ZMod 2) {v}) :=
    { smul := fun n x => Submodule.mapQ _ _ ((n : GLV V) : V →ₗ[ZMod 2] V)
        (g12h2_mapQ_le (hNv n n.2)) x
      one_smul := fun x => by
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rfl
      mul_smul := fun n m x => by
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rfl }
  have hpg : IsPGroup 2 ↥N := fun g => by
    obtain ⟨k, hk⟩ := hN g.1 g.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hmod := hpg.card_modEq_card_fixedPoints (V ⧸ Submodule.span (ZMod 2) {v})
  unfold Nat.ModEq at hmod
  have hfin : Nat.card (V ⧸ Submodule.span (ZMod 2) {v}) % 2 = 0 := by
    have h1 := Submodule.finrank_quotient_add_finrank (Submodule.span (ZMod 2) {v})
    rw [finrank_span_singleton hv] at h1
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
  have h0F : (0 : V ⧸ Submodule.span (ZMod 2) {v}) ∈
      MulAction.fixedPoints ↥N (V ⧸ Submodule.span (ZMod 2) {v}) :=
    MulAction.mem_fixedPoints.2 fun m => by
      show Submodule.mapQ _ _ _ _ 0 = 0
      exact map_zero _
  set F := MulAction.fixedPoints ↥N (V ⧸ Submodule.span (ZMod 2) {v}) with hF
  haveI : Nonempty F := ⟨⟨0, h0F⟩⟩
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hFeven : Nat.card F % 2 = 0 := by omega
  have hgt : 1 < Nat.card F := by omega
  haveI hnt : Nontrivial F := (Finite.one_lt_card_iff_nontrivial).1 hgt
  obtain ⟨x, y, hxy⟩ := exists_pair_ne F
  obtain ⟨z, hzF, hz0⟩ : ∃ z ∈ F, z ≠ 0 := by
    by_cases hx0 : (x : V ⧸ Submodule.span (ZMod 2) {v}) = 0
    · exact ⟨y, y.2, fun hy0 => hxy (Subtype.ext (hx0.trans hy0.symm))⟩
    · exact ⟨x, x.2, hx0⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  refine ⟨a, fun ha => hz0 ((Submodule.Quotient.mk_eq_zero _).2 ha), fun n hn => ?_⟩
  have hfix := MulAction.mem_fixedPoints.1 hzF ⟨n, hn⟩
  have hfix' : (Submodule.Quotient.mk (n a) : V ⧸ Submodule.span (ZMod 2) {v}) =
      Submodule.Quotient.mk a := hfix
  exact (Submodule.Quotient.eq _).1 hfix'

private theorem g12h2_radical {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {v : V} (h : IsSymplectic B) (hv : v ≠ 0)
    (hd : 2 ≤ Module.finrank (ZMod 2) V)
    (N : Subgroup (GLV V)) (hN : ∀ n ∈ N, ∃ k : ℕ, n ^ 2 ^ k = 1)
    (hNS : N ≤ spStab B v) (hNn : ∀ g ∈ spStab B v, ∀ n ∈ N, g * n * g⁻¹ ∈ N) :
    N ≤ Qv B (spSub B) v := by
  classical
  set T : Set V := {y | ∃ m ∈ N, ∃ x ∈ perp B v, y = m x - x} with hT
  set D : Submodule (ZMod 2) V := Submodule.span (ZMod 2) T with hD
  have hDW : D ≤ perp B v := by
    rw [hD, Submodule.span_le]
    rintro y ⟨m, hm, x, hx, rfl⟩
    exact (perp B v).sub_mem (g12h2_stab_perp (hNS hm) hx) hx
  have hcl : ∀ p ∈ perp B v, ∀ y ∈ D, y + B y p • p ∈ D := by
    intro p hp
    have hpv : B v p = 0 := mem_perp_iff.1 hp
    set t : GLV V := radE B p 0 1 with ht
    have hty : ∀ y, t y = y + B y p • p := fun y => radE_one_apply h y
    have htv : t v = v := by rw [hty, hpv, zero_smul, add_zero]
    have htS : t ∈ spStab B v :=
      ⟨radE_mem_spSub h (map_zero (B p)), MulAction.mem_stabilizer_iff.2 htv⟩
    let φ : V →ₗ[ZMod 2] V := LinearMap.id + LinearMap.smulRight (LinearMap.flip B p) p
    have hφ : ∀ y, φ y = y + B y p • p := fun y => by simp [φ, LinearMap.flip_apply]
    have hφt : ∀ y, φ y = t y := fun y => by rw [hφ, hty]
    have hsub : D ≤ D.comap φ := by
      rw [hD, Submodule.span_le]
      rintro y ⟨m, hm, x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, hφt, map_sub]
      have hm' : t * m * t⁻¹ ∈ N := hNn t htS m hm
      have e2 : (t * m * t⁻¹) (t x) = t (m x) := by
        show t (m (t.symm (t x))) = t (m x)
        rw [LinearEquiv.symm_apply_apply]
      have hgen : (t * m * t⁻¹) (t x) - t x ∈ T :=
        ⟨t * m * t⁻¹, hm', t x, g12h2_stab_perp htS hx, rfl⟩
      rw [← e2]
      exact Submodule.subset_span hgen
    intro y hy
    have := Submodule.mem_comap.1 (hsub hy)
    rwa [hφ] at this
  have hDS : D ≤ Submodule.span (ZMod 2) {v} := by
    by_contra hcon
    rw [SetLike.not_le_iff_exists] at hcon
    obtain ⟨d, hdD, hdS⟩ := hcon
    have hWD : perp B v ≤ D := g12h2_W_irr h hdD hdS (fun p hp => hcl p hp d hdD)
    obtain ⟨a, haS, hfix⟩ := g12h2_fixed_coset hv hd N hN
      (fun m hm => MulAction.mem_stabilizer_iff.1 (hNS hm).2)
    have hkillD : D ≤ LinearMap.ker (B a) := by
      rw [hD, Submodule.span_le]
      rintro y ⟨m, hm, x, hx, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hfix m⁻¹ (N.inv_mem hm))
      have e2 : m⁻¹ a = a + c • v := by rw [hc]; abel
      have hmB : ∀ x y : V, B (m x) (m y) = B x y := (hNS hm).1
      have e3 : B a (m x) = B (m⁻¹ a) x := by
        have h4 := hmB (m⁻¹ a) x
        have e4 : m (m⁻¹ a) = a := by simp
        rw [e4] at h4
        exact h4
      have hvx : B v x = 0 := mem_perp_iff.1 hx
      have e5 : B (a + c • v) x = B a x := by
        rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hvx, smul_zero,
          add_zero]
      rw [map_sub, e3, e2, e5]
      exact sub_self _
    have hWker : ∀ w ∈ perp B v, B a w = 0 := fun w hw => LinearMap.mem_ker.1 (hkillD (hWD hw))
    have haO : a ∈ B.orthogonal (perp B v) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      rw [h.symm' w a]
      exact hWker w hw
    rw [IsSymplectic.orthogonal_perp h v] at haO
    exact haS haO
  intro n hn
  have hnS : n ∈ spStab B v := hNS hn
  have hnv : n v = v := MulAction.mem_stabilizer_iff.1 hnS.2
  have hmem : ∀ x ∈ perp B v, n x - x ∈ Submodule.span (ZMod 2) {v} := by
    intro x hx
    have hmemT : n x - x ∈ T := ⟨n, hn, x, hx, rfl⟩
    exact hDS (Submodule.subset_span hmemT)
  exact ⟨hnS.1, hnv, fun x hx => ⟨g12h2_stab_perp hnS hx, hmem x hx⟩⟩

private theorem g12h2_Q_normal {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {v : V} {g r : GLV V}
    (hg : g ∈ spStab B v) (hr : r ∈ Qv B (spSub B) v) :
    g * r * g⁻¹ ∈ Qv B (spSub B) v := by
  obtain ⟨hr1, hrv, hrW⟩ := hr
  have hginv : g⁻¹ ∈ spStab B v := (spStab B v).inv_mem hg
  have hgv : g v = v := MulAction.mem_stabilizer_iff.1 hg.2
  have hginvv : g⁻¹ v = v := MulAction.mem_stabilizer_iff.1 hginv.2
  refine ⟨(spSub B).mul_mem ((spSub B).mul_mem hg.1 hr1) ((spSub B).inv_mem hg.1), ?_, ?_⟩
  · show g (r (g⁻¹ v)) = v
    rw [hginvv, hrv, hgv]
  · intro x hx
    have hy : g⁻¹ x ∈ perp B v := g12h2_stab_perp hginv hx
    obtain ⟨hry, hrys⟩ := hrW (g⁻¹ x) hy
    have hgx : g (g⁻¹ x) = x := by simp
    refine ⟨g12h2_stab_perp hg hry, ?_⟩
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hrys
    have key : g (r (g⁻¹ x)) - x = t • v := by
      calc g (r (g⁻¹ x)) - x = g (r (g⁻¹ x)) - g (g⁻¹ x) := by rw [hgx]
        _ = g (r (g⁻¹ x) - g⁻¹ x) := (map_sub g _ _).symm
        _ = g (t • v) := by rw [ht]
        _ = t • v := by rw [map_smul, hgv]
    show g (r (g⁻¹ x)) - x ∈ Submodule.span (ZMod 2) {v}
    rw [key]
    exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self v)

private theorem g12h2_elemAb {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {G : Subgroup (GLV V)} {v : V}
    (h : IsSymplectic B) (hG : G ≤ spSub B) (hv : IsStarVec B G v) :
    CFSG.Open.IsElemAbelian 2 (Qv B G v) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', c, ha, hac⟩ := g12h_qv_rep h hG hv a.2
    obtain ⟨b', c', hb, hbc⟩ := g12h_qv_rep h hG hv b.2
    apply Subtype.ext
    show (a : GLV V) * b = b * a
    rw [hac, hbc, radE_mul h ha hb, radE_mul h hb ha, add_comm b' a', h.symm' b' a']
    congr 1
    abel
  · obtain ⟨a, c, ha, hxe⟩ := g12h_qv_rep h hG hv hx
    rw [pow_two, hxe, radE_mul_self h ha]

private theorem g12h2_isEA {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Q : Subgroup (GLV V)) (hQ : CFSG.Open.IsElemAbelian 2 Q) :
    CFSG.IsElementaryAbelian 2 ↥Q :=
  { toIsMulCommutative := hQ.1
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by simpa using hQ.2 x.1 x.2) }

private theorem g12h2_pRank {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Q : Subgroup (GLV V)) (k : ℕ) (hQ : CFSG.Open.IsElemAbelian 2 Q)
    (hc : Nat.card Q = 2 ^ k) : CFSG.pRank 2 ↥Q = k := by
  haveI := g12h2_isEA Q hQ
  exact CFSG.pRank_eq_of_card_eq_pow (by norm_num) hc

private theorem g12h2_pCore {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {v : V} (h : IsSymplectic B) (hv : v ≠ 0)
    (hd : 2 ≤ Module.finrank (ZMod 2) V)
    (hQ : CFSG.Open.IsElemAbelian 2 (Qv B (spSub B) v)) :
    pCoreOf 2 (spStab B v) = Qv B (spSub B) v := by
  apply le_antisymm
  · intro g hg
    unfold pCoreOf at hg
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hg
    have hKn : (CFSG.pCore 2 ↥(spStab B v)).Normal := CFSG.pCore_normal
    have hKp : IsPGroup 2 (CFSG.pCore 2 ↥(spStab B v)) := CFSG.pCore_isPGroup
    have hradN : (CFSG.pCore 2 ↥(spStab B v)).map (spStab B v).subtype ≤
        Qv B (spSub B) v := by
      apply g12h2_radical h hv hd
      · intro n hn
        obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.1 hn
        obtain ⟨j, hj⟩ := hKp ⟨k', hk'⟩
        refine ⟨j, ?_⟩
        have h1 := congrArg (fun z : ↥(spStab B v) => (z : GLV V)) (congrArg Subtype.val hj)
        simpa using h1
      · exact Subgroup.map_subtype_le _
      · intro g hg n hn
        obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.1 hn
        refine Subgroup.mem_map.2 ⟨⟨g, hg⟩ * k' * (⟨g, hg⟩)⁻¹, hKn.conj_mem k' hk' ⟨g, hg⟩, ?_⟩
        simp
    exact hradN (Subgroup.mem_map_of_mem _ hk)
  · intro g hg
    have hgS : g ∈ spStab B v := ⟨hg.1, MulAction.mem_stabilizer_iff.2 hg.2.1⟩
    let H : Subgroup ↥(spStab B v) := (Qv B (spSub B) v).subgroupOf (spStab B v)
    have hHn : H.Normal := by
      refine ⟨fun k hk x => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      have := g12h2_Q_normal x.2 hk
      simpa using this
    have hHp : IsPGroup 2 H := by
      intro k
      refine ⟨1, ?_⟩
      have hk2 : ((k : ↥(spStab B v)) : GLV V) ^ 2 = 1 :=
        hQ.2 _ (Subgroup.mem_subgroupOf.1 k.2)
      apply Subtype.ext
      apply Subtype.ext
      simpa [pow_two] using hk2
    have hHle : H ≤ CFSG.pCore 2 ↥(spStab B v) := le_sSup ⟨hHn, hHp⟩
    show g ∈ (CFSG.pCore 2 ↥(spStab B v)).map (spStab B v).subtype
    exact Subgroup.mem_map.2 ⟨⟨g, hgS⟩, hHle (Subgroup.mem_subgroupOf.2 hg), rfl⟩

private theorem g12h2_card {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {G : Subgroup (GLV V)} {v : V}
    (h : IsSymplectic B) (hG : G ≤ spSub B) (hv : IsStarVec B G v)
    (hd : 2 ≤ Module.finrank (ZMod 2) V) :
    (QFaithfulOnW B G v → Nat.card (Qv B G v) = 2 ^ (Module.finrank (ZMod 2) V - 2)) ∧
    (¬ QFaithfulOnW B G v → Nat.card (Qv B G v) = 2 ^ (Module.finrank (ZMod 2) V - 1)) := by
  classical
  haveI : Module.Finite (ZMod 2) V := (Module.finite_iff_finite (R := ZMod 2)).2 inferInstance
  have hv0 : v ≠ 0 := hv.1
  obtain ⟨x0, hx0⟩ := h.exists_B_eq_one hv0
  have hvW : v ∈ perp B v := mem_perp_iff.2 (h.1 v)
  let S0 : Submodule (ZMod 2) (perp B v) := Submodule.span (ZMod 2) {(⟨v, hvW⟩ : perp B v)}
  let pr : V → perp B v := fun y => if hy : y ∈ perp B v then ⟨y, hy⟩ else 0
  have pr_mem : ∀ y (hy : y ∈ perp B v), pr y = ⟨y, hy⟩ := fun y hy => dif_pos hy
  have hgB : ∀ g ∈ Qv B G v, ∀ x y : V, B (g x) (g y) = B x y := fun g hg => hG hg.1
  have hWmem : ∀ g ∈ Qv B G v, g x0 - x0 ∈ perp B v := by
    intro g hg
    rw [mem_perp_iff, map_sub]
    have h1 := hgB g hg v x0
    rw [hg.2.1] at h1
    rw [h1]
    exact sub_self _
  have hmulS : ∀ g ∈ Qv B G v, ∀ g' ∈ Qv B G v,
      pr ((g * g' : GLV V) x0 - x0) - (pr (g x0 - x0) + pr (g' x0 - x0)) ∈ S0 := by
    intro g hg g' hg'
    have hy := hWmem g' hg'
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 (hg.2.2 _ hy).2
    have hval : ((g * g' : GLV V) x0 - x0) - ((g x0 - x0) + (g' x0 - x0)) = s • v := by
      rw [hs]
      show g (g' x0) - x0 - ((g x0 - x0) + (g' x0 - x0)) = g (g' x0 - x0) - (g' x0 - x0)
      rw [map_sub]
      abel
    rw [pr_mem _ (hWmem _ (Subgroup.mul_mem _ hg hg')), pr_mem _ (hWmem g hg), pr_mem _ hy]
    have e : (⟨((g * g' : GLV V) x0 - x0), hWmem _ (Subgroup.mul_mem _ hg hg')⟩ -
        (⟨g x0 - x0, hWmem g hg⟩ + ⟨g' x0 - x0, hy⟩) : perp B v) = s • (⟨v, hvW⟩ : perp B v) :=
      Subtype.ext hval
    rw [e]
    exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)
  let ψ : Qv B G v →* Multiplicative (perp B v ⧸ S0) :=
    { toFun := fun g => Multiplicative.ofAdd (Submodule.Quotient.mk (pr ((g : GLV V) x0 - x0)))
      map_one' := by
        show Multiplicative.ofAdd (Submodule.Quotient.mk (pr (x0 - x0))) = 1
        rw [sub_self, pr_mem 0 (Submodule.zero_mem _)]
        rfl
      map_mul' := fun g g' => by
        show Multiplicative.ofAdd (Submodule.Quotient.mk
            (pr (((g * g' : Qv B G v) : GLV V) x0 - x0))) =
          Multiplicative.ofAdd (Submodule.Quotient.mk (pr ((g : GLV V) x0 - x0))) *
            Multiplicative.ofAdd (Submodule.Quotient.mk (pr ((g' : GLV V) x0 - x0)))
        rw [← ofAdd_add, ← Submodule.Quotient.mk_add]
        congr 1
        exact (Submodule.Quotient.eq _).2 (hmulS (g : GLV V) g.2 (g' : GLV V) g'.2) }
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective S0 (Multiplicative.toAdd z)
    obtain ⟨c, hc⟩ := ((isStarVec_iff_rad h hG).1 hv).2 (w : V) (mem_perp_iff.1 w.2)
    have hgQ : radE B v (w : V) c ∈ Qv B G v := radE_mem_QSub h (mem_perp_iff.1 w.2) hc
    refine ⟨⟨radE B v (w : V) c, hgQ⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    show Submodule.Quotient.mk (pr (radE B v (w : V) c x0 - x0)) = Multiplicative.toAdd z
    rw [← hw]
    apply (Submodule.Quotient.eq _).2
    have hgx : radE B v (w : V) c x0 - x0 = (w : V) + (B x0 w + c) • v := by
      rw [radE_apply h (mem_perp_iff.1 w.2), hx0, one_smul, mul_one]
      abel
    have hmem : radE B v (w : V) c x0 - x0 ∈ perp B v := hWmem _ hgQ
    rw [pr_mem _ hmem]
    have e : (⟨radE B v (w : V) c x0 - x0, hmem⟩ - w : perp B v) =
        (B x0 w + c) • (⟨v, hvW⟩ : perp B v) := by
      apply Subtype.ext
      show radE B v (w : V) c x0 - x0 - (w : V) = (B x0 w + c) • v
      rw [hgx]
      abel
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hker : ∀ g : Qv B G v, g ∈ ψ.ker ↔ (g : GLV V) x0 - x0 ∈ Submodule.span (ZMod 2) {v} := by
    intro g
    have hy := hWmem g g.2
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (Submodule.Quotient.mk (pr ((g : GLV V) x0 - x0))) = 1 ↔ _
    rw [ofAdd_eq_one, Submodule.Quotient.mk_eq_zero, pr_mem _ hy]
    constructor
    · intro hmem
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hmem
      exact Submodule.mem_span_singleton.2 ⟨s, congrArg Subtype.val hs⟩
    · intro hmem
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hmem
      exact Submodule.mem_span_singleton.2 ⟨s, Subtype.ext hs⟩
  have hfixW : ∀ g ∈ Qv B G v, g x0 - x0 ∈ Submodule.span (ZMod 2) {v} →
      ∀ w ∈ perp B v, g w = w := by
    intro g hg hgs w hw
    obtain ⟨a, c, ha, hge⟩ := g12h_qv_rep h hG hv hg
    rw [hge] at hgs ⊢
    rw [radE_apply h ha, hx0, one_smul, mul_one] at hgs
    have hsa : (B x0 a + c) • v ∈ Submodule.span (ZMod 2) {v} :=
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    have hkey : (x0 + a + (B x0 a + c) • v - x0) - (B x0 a + c) • v = a := by abel
    have has : a ∈ Submodule.span (ZMod 2) {v} := by
      have := Submodule.sub_mem _ hgs hsa
      rwa [hkey] at this
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 has
    have hwv : B w v = 0 := by rw [h.symm' w v]; exact mem_perp_iff.1 hw
    rw [← hs, g12h_span_apply h s c w, hwv, mul_zero, zero_smul, add_zero]
  have hsmall : ∀ g ∈ Qv B G v, (∀ w ∈ perp B v, g w = w) → g = 1 ∨ g = radE B v 0 1 := by
    intro g hg hfix
    obtain ⟨a, c, ha, hge⟩ := g12h_qv_rep h hG hv hg
    rw [hge] at hfix ⊢
    have hBa : ∀ w ∈ perp B v, B w a = 0 := by
      intro w hw
      have hwv : B w v = 0 := by rw [h.symm' w v]; exact mem_perp_iff.1 hw
      have e := hfix w hw
      rw [radE_apply h ha, hwv] at e
      simpa [hv0] using e
    have haO : a ∈ B.orthogonal (perp B v) := LinearMap.BilinForm.mem_orthogonal_iff.2 hBa
    rw [IsSymplectic.orthogonal_perp h v] at haO
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 haO
    have hae : radE B v a c = radE B v 0 c := by
      rw [← hs]
      exact LinearEquiv.ext fun y => by rw [g12h_span_apply h s c y, radE_zero_apply h y]
    rcases g12_eq_zero_or_one c with rfl | rfl
    · left
      rw [hae, radE_zero_zero h]
    · right
      exact hae
  have ht1 : radE B v 0 1 ≠ 1 := by
    intro h1
    have h2 : radE B v 0 1 x0 = (1 : GLV V) x0 := by rw [h1]
    rw [radE_one_apply h, hx0, one_smul] at h2
    have h3 : x0 + v = x0 := h2
    exact hv0 (by simpa using h3)
  have hkerF : QFaithfulOnW B G v → ψ.ker = ⊥ := by
    intro hf
    rw [eq_bot_iff]
    intro g hg
    rw [hker] at hg
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rcases hsmall g.1 g.2 (hfixW g.1 g.2 hg) with h1 | h1
    · exact h1
    · exfalso
      have hmemT : radE B v 0 1 ∈ Qv B G v := h1 ▸ g.2
      have hfix1 : ∀ w ∈ perp B v, radE B v 0 1 w = w := fun w hw => by
        rw [← h1]
        exact hfixW _ g.2 hg w hw
      exact ht1 (hf _ hmemT hfix1)
  have hnonf : ¬ QFaithfulOnW B G v → radE B v 0 1 ∈ Qv B G v := by
    intro hnf
    unfold QFaithfulOnW at hnf
    push_neg at hnf
    obtain ⟨x, hx, hfix, hx1⟩ := hnf
    rcases hsmall x hx hfix with h1 | h1
    · exact absurd h1 hx1
    · rw [← h1]
      exact hx
  have hkerN : ¬ QFaithfulOnW B G v → Nat.card ↥ψ.ker = 2 := by
    intro hnf
    have htQ : radE B v 0 1 ∈ Qv B G v := hnonf hnf
    let t : Qv B G v := ⟨radE B v 0 1, htQ⟩
    have htK : t ∈ ψ.ker := by
      rw [hker]
      show radE B v 0 1 x0 - x0 ∈ _
      rw [radE_one_apply h, hx0, one_smul, add_sub_cancel_left]
      exact Submodule.mem_span_singleton_self v
    have hK : ψ.ker = Subgroup.zpowers t := by
      apply le_antisymm
      · intro g hg
        rw [hker] at hg
        rcases hsmall g.1 g.2 (hfixW g.1 g.2 hg) with h1 | h1
        · have hg1 : g = 1 := Subtype.ext h1
          rw [hg1]
          exact Subgroup.one_mem _
        · have hgt : g = t := Subtype.ext h1
          rw [hgt]
          exact Subgroup.mem_zpowers t
      · exact Subgroup.zpowers_le.2 htK
    have ht2 : t ^ 2 = 1 := by
      apply Subtype.ext
      show radE B v 0 1 ^ 2 = 1
      rw [pow_two]
      exact radE_mul_self h (map_zero (B v))
    have ht_ne : t ≠ 1 := fun h1 => ht1 (congrArg Subtype.val h1)
    rw [hK, Nat.card_zpowers, orderOf_eq_prime ht2 ht_ne]
  have hWfin : Module.finrank (ZMod 2) (perp B v) + 1 = Module.finrank (ZMod 2) V :=
    h.finrank_perp hv0
  have hS0fin : Module.finrank (ZMod 2) S0 = 1 := by
    have hne : (⟨v, hvW⟩ : perp B v) ≠ 0 := fun h0 => hv0 (congrArg Subtype.val h0)
    exact finrank_span_singleton hne
  have hTcard : Nat.card (perp B v ⧸ S0) = 2 ^ (Module.finrank (ZMod 2) V - 2) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have hq := Submodule.finrank_quotient_add_finrank S0
    congr 1
    omega
  have hidx : ψ.ker.index = Nat.card (perp B v ⧸ S0) := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top]
    rfl
  have hPcard : Nat.card (Qv B G v) = Nat.card ψ.ker * Nat.card (perp B v ⧸ S0) := by
    rw [← hidx]
    exact (Subgroup.card_mul_index ψ.ker).symm
  refine ⟨fun hf => ?_, fun hnf => ?_⟩
  · rw [hPcard, hkerF hf, Subgroup.card_bot, one_mul, hTcard]
  · rw [hPcard, hkerN hnf, hTcard]
    have e : Module.finrank (ZMod 2) V - 1 = (Module.finrank (ZMod 2) V - 2) + 1 := by omega
    rw [e, pow_succ, mul_comm]

private theorem g12h2_part1 {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {G : Subgroup (GLV V)} {v : V}
    (h : IsSymplectic B) (hG : G ≤ spSub B) (hv : IsStarVec B G v) :
    ∀ x ∈ Qv B G v, x ≠ 1 → ∀ y : V, x y = y → y ∈ perp B v := by
  intro x hx hx1 y hy
  obtain ⟨a, c, ha, hxe⟩ := g12h_qv_rep h hG hv hx
  rw [hxe, radE_apply h ha] at hy
  rw [mem_perp_iff]
  by_contra hyv
  have hyv' : B y v ≠ 0 := by rw [h.symm' y v]; exact hyv
  have hyv1 : B y v = 1 := g12_eq_one_of_ne_zero _ hyv'
  have h3 : B y v • a + (B y a + c * B y v) • v = 0 := by
    have h3a := hy
    rw [add_assoc] at h3a
    exact add_eq_left.1 h3a
  rw [hyv1, one_smul, mul_one] at h3
  have h4 : B y (a + (B y a + c) • v) = 0 := by rw [h3, map_zero]
  rw [map_add, map_smul, smul_eq_mul, hyv1, mul_one] at h4
  have hc0 : c = 0 := by linear_combination h4 - g12_add_self (B y a)
  have ha_eq : a = (B y a + c) • v := by
    calc a = (a + (B y a + c) • v) + (B y a + c) • v := by
          rw [add_assoc, g12_vadd_self, add_zero]
      _ = (B y a + c) • v := by rw [h3, zero_add]
  have has : a ∈ Submodule.span (ZMod 2) {v} := by
    rw [ha_eq]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 has
  apply hx1
  rw [hxe, ← hs, hc0]
  have e : radE B v (s • v) 0 = radE B v 0 0 :=
    LinearEquiv.ext fun z => by rw [g12h_span_apply h s 0 z, radE_zero_apply h z]
  rw [e, radE_zero_zero h]

private theorem g12h2_part3 {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {G : Subgroup (GLV V)} {v : V}
    (h : IsSymplectic B) (hG : G ≤ spSub B) (hv : IsStarVec B G v) :
    FullAxisTransvOnQuot B v (Qv B G v) := by
  refine ⟨fun y hy => ?_, fun c hc => ?_⟩
  · obtain ⟨a, c', ha, hye⟩ := g12h_qv_rep h hG hv hy
    refine ⟨a, mem_perp_iff.2 ha, fun x => ?_⟩
    rw [hye, radE_apply h ha]
    have e : x + B x v • a + (B x a + c' * B x v) • v - x - B x v • a =
        (B x a + c' * B x v) • v := by abel
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  · obtain ⟨c', hc'⟩ := ((isStarVec_iff_rad h hG).1 hv).2 c (mem_perp_iff.1 hc)
    refine ⟨radE B v c c', radE_mem_QSub h (mem_perp_iff.1 hc) hc', fun x => ?_⟩
    rw [radE_apply h (mem_perp_iff.1 hc)]
    have e : x + B x v • c + (B x c + c' * B x v) • v - x - B x v • c =
        (B x c + c' * B x v) • v := by abel
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)


@[expose] def G_12_3 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    HypG121 B G u v →
      IsIrr (Qv B G v ⊔ Qv B G u) ⊤ ∧
      ∃ g ∈ Qv B G v ⊔ Qv B G u, g v ∉ perp B v

theorem as_G_12_3 : G_12_3 := by
  intro V _ _ _ B G u v h
  have huv : B u v = 1 := (g12_eq_zero_or_one (B u v)).resolve_left h.uv
  have hv0 : v ≠ 0 := h.v_mem.1
  have hvu : B v u = 1 := by rw [h.symp.symm' v u]; exact huv
  refine ⟨?_, ?_⟩
  · have hlt : (⊥ : Submodule (ZMod 2) V) < ⊤ := by
      refine lt_of_le_of_ne bot_le (fun heq => hv0 ?_)
      have hvtop : v ∈ (⊤ : Submodule (ZMod 2) V) := Submodule.mem_top
      rw [← heq] at hvtop
      exact (Submodule.mem_bot _).1 hvtop
    refine ⟨fun k _ x _ => Submodule.mem_top, hlt, ?_⟩
    intro J hJ _ _
    by_cases hJ0 : J = ⊥
    · exact Or.inl hJ0
    · right
      obtain ⟨x0, hx0J, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ0
      have hJv : ∀ k ∈ Qv B G v, ∀ y ∈ J, k y ∈ J :=
        fun k hk y hy => hJ k (Subgroup.mem_sup_left hk) y hy
      have hJu : ∀ k ∈ Qv B G u, ∀ y ∈ J, k y ∈ J :=
        fun k hk y hy => hJ k (Subgroup.mem_sup_right hk) y hy
      apply eq_top_iff.2
      intro y _
      by_cases hxv : B x0 v = 1
      · exact g12h_top h.symp h.le_sp h.dim h.v_mem hJv hx0J hxv y
      · have hxv0 : B x0 v = 0 := (g12_eq_zero_or_one (B x0 v)).resolve_right hxv
        have hvJ : v ∈ J := by
          by_cases hxs : x0 ∈ Submodule.span (ZMod 2) {v}
          · obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hxs
            rcases g12_eq_zero_or_one t with rfl | rfl
            · exact absurd (zero_smul (ZMod 2) v) hx00
            · simpa using hx0J
          · obtain ⟨a, ha, hxa⟩ := g12h_exists_pair h.symp hxs
            obtain ⟨c, hc⟩ := ((isStarVec_iff_rad h.symp h.le_sp).1 h.v_mem).2 a ha
            have hg : radE B v a c ∈ Qv B G v := radE_mem_QSub h.symp ha hc
            have h1 := hJv _ hg x0 hx0J
            have h2 : radE B v a c x0 = x0 + v := by
              rw [radE_apply h.symp ha, hxv0, hxa]; simp
            rw [h2] at h1
            simpa using J.sub_mem h1 hx0J
        exact g12h_top h.symp h.le_sp h.dim h.u_mem hJu hvJ hvu y
  · have key : ∃ a, B u a = 0 ∧ radE B u a 1 ∈ G := by
      by_contra hcon
      push_neg at hcon
      have h0 : ∀ a, B u a = 0 → radE B u a 0 ∈ G := by
        intro a ha
        obtain ⟨c, hc⟩ := ((isStarVec_iff_rad h.symp h.le_sp).1 h.u_mem).2 a ha
        rcases g12_eq_zero_or_one c with rfl | rfl
        · exact hc
        · exact absurd hc (hcon a ha)
      obtain ⟨b, hbu, hbn⟩ := g12h_perp_exists h.symp h.u_mem.1 h.dim
      obtain ⟨a, hau, hba⟩ := g12h_exists_pair h.symp hbn
      have hm : radE B u b 0 * radE B u a 0 = radE B u (b + a) (0 + 0 + B b a) :=
        radE_mul h.symp hbu hau
      have hmem : radE B u (b + a) 1 ∈ G := by
        have := G.mul_mem (h0 b hbu) (h0 a hau)
        rw [hm, hba] at this
        simpa using this
      exact hcon (b + a) (by rw [map_add, hbu, hau, add_zero]) hmem
    obtain ⟨a0, ha0, hg0⟩ := key
    refine ⟨radE B u a0 1, Subgroup.mem_sup_right (radE_mem_QSub h.symp ha0 hg0), ?_⟩
    intro hmem
    rw [mem_perp_iff, radE_apply h.symp ha0 v] at hmem
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      h.symp.1 v, hvu] at hmem
    generalize B v a0 = p at hmem
    revert p
    decide

@[expose] def G_12_4 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    HypG121 B G u v →
      ((∀ x : V, x ∉ perp B v → x ∈ orbitSet G v) → TransOnNonzero G) ∧
      ((∀ x : V, x ∈ perp B v → x ≠ 0 → x ∈ orbitSet G v) → TransOnNonzero G)

theorem as_G_12_4 : G_12_4 := by
  intro V _ _ _ B G u v h
  have huv : B u v = 1 := (g12_eq_zero_or_one (B u v)).resolve_left h.uv
  have hv0 : v ≠ 0 := h.v_mem.1
  refine ⟨fun hall => g12h_trans_of_all h.symp h.le_sp hv0 hall, ?_⟩
  intro hW
  by_contra hnt
  have hnt' : ∃ x, x ≠ 0 ∧ x ∉ orbitSet G v := by
    by_contra hcon
    push_neg at hcon
    apply hnt
    intro x y hx hy
    obtain ⟨g1, hg1, hg1x⟩ := hcon x hx
    obtain ⟨g2, hg2, hg2y⟩ := hcon y hy
    refine ⟨g2 * g1⁻¹, G.mul_mem hg2 (G.inv_mem hg1), ?_⟩
    simp [hg1x, hg2y]
  obtain ⟨q, hq_add, -, -, hq_orb⟩ :=
    exists_quadratic_of_nontransitive h.symp h.le_sp h.v_mem h.u_mem huv h.dim hnt'
  have hWB : ∀ w ∈ perp B v, ∀ w' ∈ perp B v, B w w' = 0 := by
    intro w hw w' hw'
    by_cases hw0 : w = 0
    · simp [hw0]
    by_cases hw'0 : w' = 0
    · simp [hw'0]
    by_cases hww : w + w' = 0
    · have hweq : w' = w + (w + w') := by rw [← add_assoc, g12_vadd_self, zero_add]
      rw [hweq]
      simp [map_add, h.symp.1 w, hww]
    · have hq1 : q w = 0 := ((hq_orb w).1 (hW w hw hw0)).2
      have hq2 : q w' = 0 := ((hq_orb w').1 (hW w' hw' hw'0)).2
      have hq3 : q (w + w') = 0 :=
        ((hq_orb (w + w')).1 (hW (w + w') ((perp B v).add_mem hw hw') hww)).2
      have e := hq_add w w'
      rw [hq1, hq2, hq3] at e
      simpa using e.symm
  have hWsub : perp B v ≤ B.orthogonal (perp B v) := fun w hw =>
    LinearMap.BilinForm.mem_orthogonal_iff.2 (fun n hn => hWB n hn w hw)
  rw [IsSymplectic.orthogonal_perp h.symp v] at hWsub
  have h1 := Submodule.finrank_mono hWsub
  rw [finrank_span_singleton hv0] at h1
  have h2 := h.symp.finrank_perp hv0
  have h3 := h.dim
  omega

@[expose] def G_12_5 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    HypG121 B G u v → ¬ QFaithfulOnW B G v → G = spSub B

theorem as_G_12_5 : G_12_5 := by
  intro V _ _ _ B G u v h hnf
  have huv : B u v = 1 := (g12_eq_zero_or_one (B u v)).resolve_left h.uv
  have hv0 : v ≠ 0 := h.v_mem.1
  unfold QFaithfulOnW at hnf
  push_neg at hnf
  obtain ⟨x, hx, hfix, hne⟩ := hnf
  obtain ⟨a, c, hva, rfl⟩ := g12h_qv_rep h.symp h.le_sp h.v_mem hx
  have hBa : ∀ w ∈ perp B v, B w a = 0 := by
    intro w hw
    have hwv : B w v = 0 := by rw [h.symp.symm' w v]; exact mem_perp_iff.1 hw
    have := hfix w hw
    rw [radE_apply h.symp hva, hwv] at this
    simpa [hv0] using this
  have hamem : a ∈ B.orthogonal (perp B v) := LinearMap.BilinForm.mem_orthogonal_iff.2 hBa
  rw [IsSymplectic.orthogonal_perp h.symp v] at hamem
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hamem
  have hc1 : c = 1 := by
    rcases g12_eq_zero_or_one c with rfl | rfl
    · exfalso
      apply hne
      exact LinearEquiv.ext fun y => by rw [g12h_span_apply h.symp]; simp
    · rfl
  subst hc1
  have htv : radE B v 0 1 ∈ G := by
    have e : radE B v (t • v) 1 = radE B v 0 1 := LinearEquiv.ext fun y => by
      rw [g12h_span_apply h.symp, radE_one_apply h.symp, one_mul]
    rw [← e]
    exact hx.1
  exact eq_spSub_of_tv_mem h.symp h.le_sp h.v_mem h.u_mem huv h.dim htv

theorem as_G_12_2 : G_12_2 := by
  intro V _ _ _ B G u v h
  have hv0 : v ≠ 0 := h.v_mem.1
  have hd : 2 ≤ Module.finrank (ZMod 2) V := by have := h.dim; omega
  refine ⟨g12h2_part1 h.symp h.le_sp h.v_mem, ?_, g12h2_part3 h.symp h.le_sp h.v_mem⟩
  have hcard := g12h2_card h.symp h.le_sp h.v_mem hd
  by_cases hf : QFaithfulOnW B G v
  · left
    exact ⟨hf, g12h2_pRank _ _ (g12h2_elemAb h.symp h.le_sp h.v_mem) (hcard.1 hf)⟩
  · right
    have hG : G = spSub B := as_G_12_5 V B G u v h hf
    have hcard' := hcard.2 hf
    subst hG
    have hQ := g12h2_elemAb h.symp (le_refl _) h.v_mem
    refine ⟨(g12h2_pCore h.symp hv0 hd hQ).symm, g12h2_pRank _ _ hQ hcard', radE B v 0 1,
      radE_mem_QSub h.symp (map_zero (B v)) (radE_mem_spSub h.symp (map_zero (B v))), ?_⟩
    intro x
    exact radE_one_apply h.symp x

@[expose] def G_12_6 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    HypG121 B G u v → QFaithfulOnW B G v →
      ((∀ x : V, x ∉ perp B v →
          x ∈ orbitSet (Qv B G v) u ∨ x ∈ orbitSet (Qv B G v) (u + v)) ∧
        u + v ∉ orbitSet (Qv B G v) u ∧
        IsRegularAt (Qv B G v) u ∧ IsRegularAt (Qv B G v) (u + v)) ∧
      (∀ w : V, w ∈ perp B v → w ≠ 0 → w ≠ v →
        w ∈ orbitSet (Qv B G v) (v + w) ∧ (w ∈ orbitSet G v ↔ w + v ∈ orbitSet G v)) ∧
      (TransOnNonzero G ∨ Xor (u ∈ orbitSet G v) (u + v ∈ orbitSet G v))

theorem as_G_12_6 : G_12_6 := by
  intro V _ _ _ B G u v h hfaith
  have huv : B u v = 1 := (g12_eq_zero_or_one (B u v)).resolve_left h.uv
  have hv0 : v ≠ 0 := h.v_mem.1
  have hvu : B v u = 1 := by rw [h.symp.symm' v u]; exact huv
  have huv' : B (u + v) v = 1 := by simp [map_add, h.symp.1 v, huv]
  have hcover : ∀ x : V, x ∉ perp B v →
      x ∈ orbitSet (Qv B G v) u ∨ x ∈ orbitSet (Qv B G v) (u + v) := by
    intro x hx
    have hxv : B v x = 1 :=
      (g12_eq_zero_or_one (B v x)).resolve_left (fun h0 => hx (mem_perp_iff.2 h0))
    have hux : u + (x + u) = x := by rw [add_comm x u, ← add_assoc, g12_vadd_self, zero_add]
    have ha : B v (x + u) = 0 := by rw [map_add, hxv, hvu]; exact g12_add_self 1
    obtain ⟨c, hc⟩ := ((isStarVec_iff_rad h.symp h.le_sp).1 h.v_mem).2 (x + u) ha
    have hg : radE B v (x + u) c ∈ Qv B G v := radE_mem_QSub h.symp ha hc
    have hgu : radE B v (x + u) c u = x + (B u (x + u) + c) • v := by
      rw [radE_apply h.symp ha, huv, one_smul, mul_one, hux]
    rcases g12_eq_zero_or_one (B u (x + u) + c) with h0 | h1
    · left
      refine ⟨radE B v (x + u) c, hg, ?_⟩
      rw [hgu, h0, zero_smul, add_zero]
    · right
      refine ⟨radE B v (x + u) c, hg, ?_⟩
      rw [map_add, hgu, radE_apply_v h.symp ha, h1, one_smul, add_assoc, g12_vadd_self,
        add_zero]
  have hnot : u + v ∉ orbitSet (Qv B G v) u := by
    rintro ⟨g, hg, hgu⟩
    obtain ⟨a, c, ha, rfl⟩ := g12h_qv_rep h.symp h.le_sp h.v_mem hg
    have hz : radE B v a c u = u + (1 : ZMod 2) • v := by rw [one_smul]; exact hgu.symm
    have hfix := g12h_fix_perp h.symp c ha (g12h_fixW h.symp ha huv hz)
    have hid : radE B v a c = 1 := hfaith _ hg hfix
    rw [hid] at hgu
    have hgu' : u + v = u := hgu
    exact hv0 (by simpa using hgu')
  have hreg : ∀ y : V, B y v = 1 → ∀ g ∈ Qv B G v, g y = y → g = 1 := by
    intro y hyv g hg hgy
    obtain ⟨a, c, ha, rfl⟩ := g12h_qv_rep h.symp h.le_sp h.v_mem hg
    have hz : radE B v a c y = y + (0 : ZMod 2) • v := by rw [zero_smul, add_zero]; exact hgy
    exact hfaith _ hg (g12h_fix_perp h.symp c ha (g12h_fixW h.symp ha hyv hz))
  have part2 : ∀ w : V, w ∈ perp B v → w ≠ 0 → w ≠ v →
      w ∈ orbitSet (Qv B G v) (v + w) ∧ (w ∈ orbitSet G v ↔ w + v ∈ orbitSet G v) := by
    intro w hw hw0 hwv
    have hvw : B v w = 0 := mem_perp_iff.1 hw
    have hwv0 : B w v = 0 := by rw [h.symp.symm' w v]; exact hvw
    have hwS : w ∉ Submodule.span (ZMod 2) {v} := by
      intro hs
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hs
      rcases g12_eq_zero_or_one t with rfl | rfl
      · exact hw0 (by simp)
      · exact hwv (by simp)
    obtain ⟨a, ha, hwa⟩ := g12h_exists_pair h.symp hwS
    obtain ⟨c, hc⟩ := ((isStarVec_iff_rad h.symp h.le_sp).1 h.v_mem).2 a ha
    have hg : radE B v a c ∈ Qv B G v := radE_mem_QSub h.symp ha hc
    have e1 : B (v + w) v = 0 := by rw [map_add, LinearMap.add_apply, h.symp.1 v, hwv0, add_zero]
    have e2 : B (v + w) a = 1 := by rw [map_add, LinearMap.add_apply, ha, hwa, zero_add]
    have hgvw : radE B v a c (v + w) = w := by
      rw [radE_apply h.symp ha, e1, e2, zero_smul, mul_zero, add_zero, add_zero, one_smul,
        add_right_comm, g12_vadd_self, zero_add]
    have hgG : radE B v a c ∈ G := hg.1
    refine ⟨⟨radE B v a c, hg, hgvw.symm⟩, ?_⟩
    constructor
    · rintro ⟨k, hk, hkw⟩
      refine ⟨(radE B v a c)⁻¹ * k, G.mul_mem (G.inv_mem hgG) hk, ?_⟩
      have hinv : (radE B v a c)⁻¹ w = v + w := by
        conv_lhs => rw [← hgvw]
        simp
      show w + v = (radE B v a c)⁻¹ (k v)
      rw [← hkw, hinv, add_comm]
    · rintro ⟨k, hk, hkw⟩
      refine ⟨radE B v a c * k, G.mul_mem hgG hk, ?_⟩
      show w = radE B v a c (k v)
      rw [← hkw, add_comm, hgvw]
  have part3 : TransOnNonzero G ∨ Xor (u ∈ orbitSet G v) (u + v ∈ orbitSet G v) := by
    by_cases hall : ∀ x : V, x ∉ perp B v → x ∈ orbitSet G v
    · exact Or.inl (g12h_trans_of_all h.symp h.le_sp hv0 hall)
    · right
      obtain ⟨g, hg, hgv⟩ := exists_B_ne h.symp h.le_sp h.u_mem huv h.dim
      have hzW : g v ∉ perp B v := by
        intro hm
        have h0 := mem_perp_iff.1 hm
        rw [h.symp.symm' v (g v), hgv] at h0
        exact one_ne_zero h0
      have hU : u ∈ orbitSet G v ∨ u + v ∈ orbitSet G v := by
        rcases hcover (g v) hzW with ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩
        · left
          refine ⟨k⁻¹ * g, G.mul_mem (G.inv_mem hk.1) hg, ?_⟩
          show u = k⁻¹ (g v)
          simp [hkz]
        · right
          refine ⟨k⁻¹ * g, G.mul_mem (G.inv_mem hk.1) hg, ?_⟩
          show u + v = k⁻¹ (g v)
          simp [hkz]
      by_cases hP : u ∈ orbitSet G v
      · by_cases hQ : u + v ∈ orbitSet G v
        · exact absurd (fun x hx => by
            rcases hcover x hx with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
            · exact g12h_orb_mem hk.1 hP
            · exact g12h_orb_mem hk.1 hQ) hall
        · exact Or.inl ⟨hP, hQ⟩
      · rcases hU with hU | hU
        · exact absurd hU hP
        · exact Or.inr ⟨hU, hP⟩
  exact ⟨⟨hcover, hnot, fun g hg hgu => hreg u huv g hg hgu,
    fun g hg hgu => hreg (u + v) huv' g hg hgu⟩, part2, part3⟩

theorem ChG.MinCx.false_of_g12_1 {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {G : Subgroup (GLV V)} {u v : V} (h : MinCx B G u v) :
    False :=
  h.not_concl (g12_1 V B G u v h.hyp.symp h.hyp.le_sp h.hyp.u_mem h.hyp.v_mem h.hyp.uv h.hyp.dim)

@[expose] def G_12_7 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    MinCx B G u v → Module.finrank (ZMod 2) V = 4 → ¬ TransOnNonzero G

theorem as_G_12_7 : G_12_7 := fun _ _ _ _ _ _ _ _ h => h.false_of_g12_1.elim

@[expose] def G_12_8 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    MinCx B G u v →
    ∀ w : V, w ∈ perp B v → w ∈ orbitSet G v → w ≠ v →
    ∀ (Û : Type) [AddCommGroup Û] [Module (ZMod 2) Û] (π : ↥(perp B w) →ₗ[ZMod 2] Û),
      HatModel B w π →
      ∃ B' : LinearMap.BilinForm (ZMod 2) Û, HatForm B w π B' ∧
        (IsSymplectic B' ∧ Gstar B G w π ≤ spSub B') ∧
        (∃ u' : V, u' ∈ orbitSet G v ∧ u' ∈ perp B w ∧ u' ∉ perp B v) ∧
        (∀ u' : V, u' ∈ orbitSet G v → u' ∈ perp B w → u' ∉ perp B v →
          IsStarVec B' (Gstar B G w π) (hatOf B w π v) ∧
            IsStarVec B' (Gstar B G w π) (hatOf B w π u')) ∧
        (4 < Module.finrank (ZMod 2) V →
          ∃ qw : Û → ZMod 2, HatQuadProp B G v w π B' qw) ∧
        (4 < Module.finrank (ZMod 2) V → ∀ qw : Û → ZMod 2, HatQuadProp B G v w π B' qw →
          ∀ z : V, z ∈ perp B w → z ≠ 0 → z ≠ w →
            (z ∈ orbitSet G v ↔ qw (hatOf B w π z) = 0))

theorem as_G_12_8 : G_12_8 := fun _ _ _ _ _ _ _ _ h => h.false_of_g12_1.elim

@[expose] def G_12_9 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    MinCx B G u v → ¬ TransOnNonzero G

theorem as_G_12_9 : G_12_9 := fun _ _ _ _ _ _ _ _ h => h.false_of_g12_1.elim

@[expose] def G_12_10 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    MinCx B G u v →
    (∀ x y : V, qOrb G v (x + y) = qOrb G v x + qOrb G v y + B x y) →
      (∃ Q : QuadraticMap (ZMod 2) V (ZMod 2), (∀ x, Q x = qOrb G v x) ∧
        ∀ x y, QuadraticMap.polar Q x y = B x y) ∧
      (G = orthSub (qOrb G v) ∨ G = omegaSub B (qOrb G v))

theorem as_G_12_10 : G_12_10 := fun _ _ _ _ _ _ _ _ h _ => h.false_of_g12_1.elim

@[expose] def G_12_11 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (G : Subgroup (GLV V)) (u v : V),
    MinCx B G u v →
      (∀ x y : V, qOrb G v x = 1 → qOrb G v y = 1 → ∃ g ∈ G, g x = y) ∧
      4 < Module.finrank (ZMod 2) V ∧
      ∀ e : ZMod 2,
        (∀ x y x' y' : V, IsNonsingPair B G v e x y → IsNonsingPair B G v e x' y' →
          ∃ g ∈ G, Submodule.map (g : V →ₗ[ZMod 2] V) (Submodule.span (ZMod 2) {x, y}) =
            Submodule.span (ZMod 2) {x', y'}) ∧
        (∀ x y : V, IsNonsingPair B G v e x y → qOrb G v (x + y) = e)

theorem as_G_12_11 : G_12_11 := fun _ _ _ _ _ _ _ _ h => h.false_of_g12_1.elim

@[expose] def G_12_12 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (H K Q : Subgroup (GLV V)) (W : Submodule (ZMod 2) V) (v : V),
    2 < Module.finrank (ZMod 2) V →
    K ≤ H → (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) → IsIrr K ⊤ → SelfDual K ⊤ →
    Q ≤ H → (∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) → (∀ a ∈ Q, a * a = 1) →
    Module.finrank (ZMod 2) W + 1 = Module.finrank (ZMod 2) V →
    ∀ (hv : v ∈ W), v ≠ 0 → FullTransvections Q W v hv →
      ∃ f : LinearMap.BilinForm (ZMod 2) V,
        (IsSymplectic f ∧ K ⊔ Q ≤ spSub f) ∧
        W = perp f v ∧
        ((∀ k ∈ K, IsStarVec f (K ⊔ Q) (k v)) ∧ ∃ h ∈ H, h v ∉ W) ∧
        (H ≤ spSub f ∨ ∃ ω : GLV V, (∀ x, ω (ω x) + ω x + x = 0) ∧
          H = Subgroup.normalizer (Subgroup.zpowers ω : Set (GLV V))) ∧
        (Concl121 f (K ⊔ Q) v ∧ (H ≤ spSub f → Concl121 f H v))

theorem as_G_12_12 : G_12_12 := by
  intro V _ _ _ H K Q W v hd hKH hnorm hirr hsd hQH hcomm hsq hhyp hv hv0 htr
  obtain ⟨f, h1, h2, h3, h4, h5, h6, h7, h8⟩ := g12_12_all V H K Q W v
    ⟨hd, hKH, hnorm, hirr, hsd, hQH, hcomm, hsq, hhyp, hv, hv0, htr⟩
  exact ⟨f, ⟨h1, h2⟩, h3, ⟨h4, h5⟩, h6, h7, h8⟩

end CFSG.ASVolI

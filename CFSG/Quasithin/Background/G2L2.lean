module

public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.G2SL2
public import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model
open scoped MatrixGroups Pointwise

variable {G : Type*} [Group G]

theorem conjAct_coe_apply (V : Subgroup G) (x : Subgroup.normalizer (V : Set G)) (v : V) :
    ((conjAct V x v : V) : G) = (x : G) * v * (x : G)⁻¹ := by
  unfold conjAct
  simp [Subgroup.normalizerMonoidHom_apply_apply_coe]

@[expose] def IsNaturalSL2Module (n : ℕ) (A K V V₁ : Subgroup G) : Prop :=
  ∃ (hnorm : A ≤ Subgroup.normalizer (V : Set G))
    (θ : A →* SL(2, GaloisField 2 n)) (ψ : V ≃* Wm (GaloisField 2 n)),
    θ.ker = K.subgroupOf A ∧ θ.range = commutator SL(2, GaloisField 2 n) ∧
    (∀ (a : A) (v : V), ψ (conjAct V ⟨a, hnorm a.2⟩ v) = natAct (θ a) (ψ v)) ∧
    ∃ w : Fin 2 → GaloisField 2 n, w ≠ 0 ∧
      ∀ v : V, (v : G) ∈ V₁ ↔ ∃ c : GaloisField 2 n, Multiplicative.toAdd (ψ v) = c • w

structure NatData (n : ℕ) (A K V V₁ : Subgroup G) where
  hnorm : A ≤ Subgroup.normalizer (V : Set G)
  θ : A →* SL(2, GaloisField 2 n)
  ψ : V ≃* Wm (GaloisField 2 n)
  ker_eq : θ.ker = K.subgroupOf A
  range_eq : θ.range = commutator SL(2, GaloisField 2 n)
  equiv : ∀ (a : A) (v : V), ψ (conjAct V ⟨a, hnorm a.2⟩ v) = natAct (θ a) (ψ v)
  line : ∀ v : V, (v : G) ∈ V₁ ↔ ∃ c : GaloisField 2 n, Multiplicative.toAdd (ψ v) = c • e0 (GaloisField 2 n)

theorem IsNaturalSL2Module.nonempty_data {n : ℕ} {A K V V₁ : Subgroup G}
    (h : IsNaturalSL2Module n A K V V₁) : Nonempty (NatData n A K V V₁) := by
  obtain ⟨hnorm, θ, ψ, hker, hrange, hequiv, w, hw0, hw⟩ := h
  obtain ⟨g, hg0⟩ := exists_smul_eq_e0 w hw0
  have hg : g • w = e0 (GaloisField 2 n) := hg0
  refine ⟨{ hnorm := hnorm, θ := (MulAut.conj g).toMonoidHom.comp θ, ψ := ψ.trans (natAct g),
            ker_eq := ?_, range_eq := ?_, equiv := ?_, line := ?_ }⟩
  · rw [← hker]
    ext a
    simp [MonoidHom.mem_ker]
  · rw [MonoidHom.range_comp, hrange]
    have hN : (commutator SL(2, GaloisField 2 n)).Normal := inferInstance
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hN.conj_mem y hy g
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by group⟩
      simpa using hN.conj_mem x hx g⁻¹
  · intro a v
    have h1 := hequiv a v
    show natAct g (ψ (conjAct V ⟨a, hnorm a.2⟩ v)) =
      natAct (g * θ a * g⁻¹) (natAct g (ψ v))
    rw [h1, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]
  · intro v
    rw [hw v]
    have hg' : g⁻¹ • e0 (GaloisField 2 n) = w := by rw [← hg, inv_smul_smul]
    show (∃ c, _ = c • w) ↔ ∃ c, Multiplicative.toAdd (natAct g (ψ v)) = c • e0 _
    rw [natAct_apply, toAdd_ofAdd]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [hc, smul_comm, ← hg]
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have : Multiplicative.toAdd (ψ v) = g⁻¹ • (c • e0 (GaloisField 2 n)) := by
        rw [← hc, inv_smul_smul]
      rw [this, smul_comm, hg']

namespace NatData

variable {n : ℕ} {A K V V₁ : Subgroup G} (D : NatData n A K V V₁)

@[expose] noncomputable def alpha : Subgroup.normalizer (V : Set G) →* MulAut (Wm (GaloisField 2 n)) :=
  (MulAut.congr D.ψ).toMonoidHom.comp (conjAct V)

theorem alpha_psi (x : Subgroup.normalizer (V : Set G)) (v : V) :
    D.alpha x (D.ψ v) = D.ψ (conjAct V x v) := by
  simp [alpha, MulAut.congr_apply]

theorem alpha_of_mem (a : A) : D.alpha ⟨a, D.hnorm a.2⟩ = natAct (D.θ a) := by
  ext w
  obtain ⟨v, rfl⟩ := D.ψ.surjective w
  rw [alpha_psi, D.equiv]

theorem alpha_eq_one_iff (x : Subgroup.normalizer (V : Set G)) :
    D.alpha x = 1 ↔ ∀ v : V, (x : G) * v * (x : G)⁻¹ = v := by
  constructor
  · intro h v
    have h1 := alpha_psi D x v
    rw [h, MulAut.one_apply] at h1
    have h2 := D.ψ.injective h1
    have h3 := congrArg (fun v : V => (v : G)) h2
    simpa [conjAct_coe_apply] using h3.symm
  · intro h
    refine MulEquiv.ext fun w => ?_
    obtain ⟨v, rfl⟩ := D.ψ.surjective w
    rw [alpha_psi, MulAut.one_apply]
    have : conjAct V x v = v := Subtype.ext (by rw [conjAct_coe_apply]; exact h v)
    rw [this]

end NatData

structure AlmostSpecialL2Hyp (n : ℕ) (V V₁ L T H : Subgroup G) : Prop where
  base : AlmostSpecialHyp V V₁ L T H
  n_pos : 0 < n
  V_eq : V = conjClosure V₁ L
  natural : IsNaturalSL2Module n L (pCoreOf 2 (L ⊔ T)) V V₁
  U_ne : ¬ conjClosure V H ≤ pCoreOf 2 (L ⊔ T)

structure L2Setting (n : ℕ) (V V₁ L T H : Subgroup G) where
  hyp : AlmostSpecialL2Hyp n V V₁ L T H
  D : NatData n L (pCoreOf 2 (L ⊔ T)) V V₁

theorem normalizer_le_normalizer_centralizer'' (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ c ∈ Subgroup.centralizer (S : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.1 hg s).1 hs
    have h1 := hc _ hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * s := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  exact ⟨fun hc => key g hg c hc, fun hc => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hc⟩

theorem exists_ne_one_mem_centralizer [Finite G] {T V : Subgroup G} (hT : IsPGroup 2 T)
    (hVT : V ≤ T) (hnorm : T ≤ Subgroup.normalizer (V : Set G)) (hV : V ≠ ⊥) :
    ∃ z ∈ V, z ≠ 1 ∧ ∀ t ∈ T, t * z = z * t := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have : (V.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hne : V.subgroupOf T ≠ ⊥ := by
    intro h
    apply hV
    rw [eq_bot_iff]
    intro v hv
    have : (⟨v, hVT hv⟩ : T) ∈ V.subgroupOf T := hv
    rw [h, Subgroup.mem_bot] at this
    have := congrArg Subtype.val this
    simpa using this
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨(w.1 : T), w.2.1, fun h => hw ?_, fun t ht => ?_⟩
  · exact Subtype.ext (Subtype.ext h)
  · have := Subgroup.mem_center_iff.1 w.2.2 ⟨t, ht⟩
    exact congrArg Subtype.val this

theorem exists_pow_two_pow_mem_of_le_normalizer [Finite G] {L T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (L : Set G)) (hT2 : IsPGroup 2 T) {c : G} (hc : c ∈ L ⊔ T) :
    ∃ k : ℕ, c ^ 2 ^ k ∈ L := by
  have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L T hT
  rw [SetLike.mem_coe.symm, hmul] at hc
  obtain ⟨l, hl, t, ht, rfl⟩ := hc
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem hT2 ht
  refine ⟨k, ?_⟩
  have key : ∀ m : ℕ, ∃ l' ∈ L, (l * t) ^ m = l' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, L.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨l', hl', h⟩ := ih
      refine ⟨l' * (t ^ m * l * (t ^ m)⁻¹), L.mul_mem hl' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hT (T.pow_mem ht m)) l).1 hl
      · rw [pow_succ, h]
        group
  obtain ⟨l', hl', h⟩ := key (2 ^ k)
  rw [h, hk, mul_one]
  exact hl'

namespace L2Setting

section NoFinite

variable {n : ℕ} {V V₁ L T H : Subgroup G} (S : L2Setting n V V₁ L T H)

include S

theorem LT_le_normV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
  sup_le S.D.hnorm S.hyp.base.T_le_normV

theorem isPGroup_V : IsPGroup 2 V := S.hyp.base.isPGroup_T.to_le S.hyp.base.V_le_T

theorem V_le_LT : V ≤ L ⊔ T := S.hyp.base.V_le_T.trans le_sup_right

theorem V_ne_bot : V ≠ ⊥ := fun h =>
  S.hyp.base.ne_bot (le_bot_iff.1 (h ▸ S.hyp.base.le_V))

theorem V_le_O : V ≤ pCoreOf 2 (L ⊔ T) :=
  le_pCoreOf_of_le_normalizer 2 S.V_le_LT S.LT_le_normV S.isPGroup_V

end NoFinite

section WithFinite

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L2Setting n V V₁ L T H)

include S

theorem O_le_T : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf S.hyp.base.sylow_LT

omit [Finite G] in
theorem irreducible_L {Y : Subgroup G} (hYV : Y ≤ V)
    (hY : L ≤ Subgroup.normalizer (Y : Set G)) : Y = ⊥ ∨ Y = V := by
  set D := S.D
  let Yw : Subgroup (Wm (GaloisField 2 n)) := (Y.subgroupOf V).map D.ψ.toMonoidHom
  have hinv : ∀ A ∈ commutator SL(2, GaloisField 2 n), ∀ x ∈ Yw, natAct A x ∈ Yw := by
    intro A hA x hx
    rw [← D.range_eq] at hA
    obtain ⟨a, rfl⟩ := hA
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨conjAct V ⟨a, D.hnorm a.2⟩ y, ?_, D.equiv a y⟩
    show (conjAct V ⟨a, D.hnorm a.2⟩ y : V) ∈ Y.subgroupOf V
    rw [Subgroup.mem_subgroupOf, conjAct_coe_apply]
    exact (Subgroup.mem_normalizer_iff.1 (hY a.2) y).1 hy
  rcases natAct_irreducible_comm Yw hinv with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    have hyV : y ∈ V := hYV hy
    have h1 : D.ψ ⟨y, hyV⟩ ∈ Yw := ⟨⟨y, hyV⟩, hy, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2 : (⟨y, hyV⟩ : V) = 1 := D.ψ.injective (h1.trans (map_one D.ψ).symm)
    have := congrArg Subtype.val h2
    simpa using this
  · right
    apply le_antisymm hYV
    intro v hv
    have h1 : D.ψ ⟨v, hv⟩ ∈ Yw := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyv⟩ := h1
    have h2 : y = ⟨v, hv⟩ := D.ψ.injective hyv
    have h3 : (y : G) ∈ Y := hy
    rwa [h2] at h3

theorem O_centralizes_V : ∀ x ∈ pCoreOf 2 (L ⊔ T), ∀ v ∈ V, x * v * x⁻¹ = v := by
  let Z : Subgroup G := V ⊓ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G)
  have hZne : Z ≠ ⊥ := by
    obtain ⟨z, hzV, hz1, hz⟩ := exists_ne_one_mem_centralizer S.hyp.base.isPGroup_T
      S.hyp.base.V_le_T S.hyp.base.T_le_normV S.V_ne_bot
    intro h
    have : z ∈ Z := ⟨hzV, Subgroup.mem_centralizer_iff.2 fun o ho => hz o (S.O_le_T ho)⟩
    rw [h, Subgroup.mem_bot] at this
    exact hz1 this
  have hZV : Z ≤ V := inf_le_left
  have hZL : L ≤ Subgroup.normalizer (Z : Set G) := by
    intro l hl
    have h1 : l ∈ Subgroup.normalizer (V : Set G) := S.D.hnorm hl
    have h2 : l ∈ Subgroup.normalizer (Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) : Set G) :=
      normalizer_le_normalizer_centralizer'' _
        (le_normalizer_pCoreOf 2 (L ⊔ T) ((le_sup_left : L ≤ L ⊔ T) hl))
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩
  rcases S.irreducible_L hZV hZL with h | h
  · exact absurd h hZne
  · intro x hx v hv
    have hvZ : v ∈ Z := by rw [h]; exact hv
    have h1 := Subgroup.mem_centralizer_iff.1 hvZ.2 x hx
    calc x * v * x⁻¹ = v * x * x⁻¹ := by rw [h1]
      _ = v := by group


theorem alpha_eq_one_iff_mem_O {x : G} (hx : x ∈ L ⊔ T) :
    S.D.alpha ⟨x, S.LT_le_normV hx⟩ = 1 ↔ x ∈ pCoreOf 2 (L ⊔ T) := by
  rw [NatData.alpha_eq_one_iff]
  constructor
  · intro h
    let C : Subgroup G := (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)
    have hxC : x ∈ C := by
      refine ⟨hx, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
      have := h ⟨v, hv⟩
      calc v * x = (x * v * x⁻¹) * x := by rw [this]
        _ = x * v := by group
    have hCnorm : L ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
      fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hy,
          normalizer_le_normalizer_centralizer'' _ (S.LT_le_normV hy)⟩
    have hCle : C ≤ L ⊔ T := inf_le_left
    have hLC : ∀ l ∈ L, l ∈ C → l ∈ pCoreOf 2 (L ⊔ T) := by
      intro l hl hlC
      have h1 : S.D.alpha ⟨l, S.LT_le_normV ((le_sup_left : L ≤ L ⊔ T) hl)⟩ = 1 := by
        rw [NatData.alpha_eq_one_iff]
        intro v
        have := Subgroup.mem_centralizer_iff.1 hlC.2 v v.2
        calc l * v * l⁻¹ = v * l * l⁻¹ := by rw [← this]
          _ = v := by group
      have h2 := S.D.alpha_of_mem ⟨l, hl⟩
      have h3 : natAct (S.D.θ ⟨l, hl⟩) = 1 := by rw [← h2]; exact h1
      have h4 : S.D.θ ⟨l, hl⟩ = 1 := natAct_injective (h3.trans (map_one natAct).symm)
      have h5 : (⟨l, hl⟩ : L) ∈ S.D.θ.ker := h4
      rw [S.D.ker_eq] at h5
      exact h5
    have hpg : IsPGroup 2 C := by
      refine isPGroup_two_of_forall fun c hc => ?_
      obtain ⟨k, hk⟩ := exists_pow_two_pow_mem_of_le_normalizer S.hyp.base.T_le_normL
        S.hyp.base.isPGroup_T (hCle hc)
      have hkC : c ^ 2 ^ k ∈ C := C.pow_mem hc _
      have hkO := hLC _ hk hkC
      obtain ⟨j, hj⟩ := exists_pow_two_pow_eq_one_of_mem (pCoreOf_isPGroup 2 (L ⊔ T)) hkO
      exact ⟨j + k, by rw [pow_add, mul_comm, pow_mul, hj]⟩
    exact le_pCoreOf_of_le_normalizer 2 hCle hCnorm hpg hxC
  · intro hxO v
    exact S.O_centralizes_V x hxO v v.2

end WithFinite

end L2Setting

namespace AlmostSpecialHyp

variable [Finite G] {V V₁ L T H : Subgroup G} (h : AlmostSpecialHyp V V₁ L T H)

include h

theorem G22_commutator_mem {x y : G} (hx : x ∈ conjClosure V H) (hy : y ∈ conjClosure V H) :
    x * y * x⁻¹ * y⁻¹ ∈ V₁ := by
  have hU := h.G22_one.2
  have hcc := h.conjClosure_le_N
  have hmemY : ∀ u (hu : u ∈ conjClosure V H),
      tmk V₁ ⟨u, hcc hu⟩ ∈ omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H)) :=
    fun u hu => (secImg_le_iff.1 hU) ⟨u, hcc hu⟩ hu
  have hyQ : tmk V₁ ⟨y, hcc hy⟩ ∈ tildeOf V₁ (pCoreOf 2 H) :=
    omegaOneCenterOf_le _ (hmemY y hy)
  have hxy : tmk V₁ ⟨x, hcc hx⟩ * tmk V₁ ⟨y, hcc hy⟩ =
      tmk V₁ ⟨y, hcc hy⟩ * tmk V₁ ⟨x, hcc hx⟩ :=
    (mem_centralizer_of_mem_omegaOneCenterOf (hmemY x hx) hyQ).symm
  exact commutator_mem_of_secMk_commute hxy

theorem G22_sq_mem {x : G} (hx : x ∈ conjClosure V H) : x ^ 2 ∈ V₁ := by
  have hU := h.G22_one.2
  have hcc := h.conjClosure_le_N
  have h1 := sq_eq_one_of_mem_omegaOneCenterOf ((secImg_le_iff.1 hU) ⟨x, hcc hx⟩ hx)
  rw [← map_pow] at h1
  simpa using secMk_eq_one_iff.1 h1

end AlmostSpecialHyp

namespace L2Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L2Setting n V V₁ L T H)

include S

theorem U_le_T : conjClosure V H ≤ T := S.hyp.base.G22_three.1

theorem U_le_normV {u : G} (hu : u ∈ conjClosure V H) : u ∈ Subgroup.normalizer (V : Set G) :=
  S.hyp.base.T_le_normV (S.U_le_T hu)

theorem U_le_normL {u : G} (hu : u ∈ conjClosure V H) : u ∈ Subgroup.normalizer (L : Set G) :=
  S.hyp.base.T_le_normL (S.U_le_T hu)

theorem alpha_U_eq_e12 {u : G} (hu : u ∈ conjClosure V H) :
    ∃ b : GaloisField 2 n, S.D.alpha ⟨u, S.U_le_normV hu⟩ = natAct (e12 b) := by
  set D := S.D
  have hF := S.hyp.n_pos
  have ha : ∀ w : Wm (GaloisField 2 n),
      Multiplicative.toAdd (D.alpha ⟨u, S.U_le_normV hu⟩ w) 1 = Multiplicative.toAdd w 1 := by
    intro w
    obtain ⟨v, rfl⟩ := D.ψ.surjective w
    rw [NatData.alpha_psi]
    have hvU : (v : G) ∈ conjClosure V H := le_conjClosure V H v.2
    have hc : u * v * u⁻¹ * (v : G)⁻¹ ∈ V₁ := S.hyp.base.G22_commutator_mem hu hvU
    have hcV : u * v * u⁻¹ * (v : G)⁻¹ ∈ V := S.hyp.base.le_V hc
    have hconj : conjAct V ⟨u, S.U_le_normV hu⟩ v = ⟨u * v * u⁻¹ * (v : G)⁻¹, hcV⟩ * v := by
      apply Subtype.ext
      rw [conjAct_coe_apply]
      simp
    rw [hconj, map_mul, toAdd_mul]
    have hline := (D.line ⟨u * v * u⁻¹ * (v : G)⁻¹, hcV⟩).1 hc
    obtain ⟨c', hc'⟩ := hline
    simp [hc']
  have hc2 : ∃ k : ℕ, D.alpha ⟨u, S.U_le_normV hu⟩ ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem S.hyp.base.isPGroup_T (S.U_le_T hu)
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨u, S.U_le_normV hu⟩ : Subgroup.normalizer (V : Set G)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hk)
    rw [this, map_one]
  rcases card_two_or_exists_sq_ne_one (F := GaloisField 2 n) with h2 | ⟨a, ha0, ha1⟩
  · obtain ⟨b, hb⟩ := normalizing_lemma_two h2 _ ha
    exact ⟨b, MulEquiv.ext hb⟩
  ·
    have hrange : D.θ.range = ⊤ := by rw [D.range_eq]; exact Matrix.SL2.commutator_eq_top ha0 ha1
    have hb : ∀ A : SL(2, GaloisField 2 n), ∃ A' : SL(2, GaloisField 2 n), ∀ w : Wm (GaloisField 2 n),
        D.alpha ⟨u, S.U_le_normV hu⟩ (natAct A w) = natAct A' (D.alpha ⟨u, S.U_le_normV hu⟩ w) := by
      intro A
      have hA : A ∈ D.θ.range := by rw [hrange]; exact Subgroup.mem_top A
      obtain ⟨a, rfl⟩ := hA
      have huL : u * a * u⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 (S.U_le_normL hu) a).1 a.2
      refine ⟨D.θ ⟨u * a * u⁻¹, huL⟩, fun w => ?_⟩
      have h1 : D.alpha ⟨u, S.U_le_normV hu⟩ * D.alpha ⟨a, D.hnorm a.2⟩ =
          D.alpha ⟨u * a * u⁻¹, D.hnorm huL⟩ * D.alpha ⟨u, S.U_le_normV hu⟩ := by
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        simp
      rw [D.alpha_of_mem a, D.alpha_of_mem ⟨u * a * u⁻¹, huL⟩] at h1
      have := congrArg (fun ρ : MulAut (Wm (GaloisField 2 n)) => ρ w) h1
      simpa using this
    obtain ⟨b, hb⟩ := normalizing_lemma _ ha hb hc2
    exact ⟨b, MulEquiv.ext hb⟩

end L2Setting

namespace NatData

variable {n : ℕ} {A K V V₁ : Subgroup G} (D : NatData n A K V V₁)

@[expose] noncomputable def actSL (X : Subgroup G) (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hr : ∀ x : X, D.alpha ⟨x, hX x.2⟩ ∈ (natAct : SL(2, GaloisField 2 n) →* MulAut (Wm (GaloisField 2 n))).range) :
    X →* SL(2, GaloisField 2 n) :=
  (MonoidHom.ofInjective natAct_injective).symm.toMonoidHom.comp
    ((D.alpha.comp (Subgroup.inclusion hX)).codRestrict _ hr)

theorem natAct_actSL (X : Subgroup G) (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hr : ∀ x : X, D.alpha ⟨x, hX x.2⟩ ∈ (natAct : SL(2, GaloisField 2 n) →* MulAut (Wm (GaloisField 2 n))).range)
    (x : X) : natAct (D.actSL X hX hr x) = D.alpha ⟨x, hX x.2⟩ := by
  have h1 := (MonoidHom.ofInjective (natAct_injective (F := GaloisField 2 n))).apply_symm_apply
    ⟨D.alpha ⟨x, hX x.2⟩, hr x⟩
  have h2 := congrArg Subtype.val h1
  exact h2

end NatData

namespace L2Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L2Setting n V V₁ L T H)

include S

theorem LU_le_normV : L ⊔ conjClosure V H ≤ Subgroup.normalizer (V : Set G) :=
  sup_le S.D.hnorm fun _ hu => S.U_le_normV hu

theorem LU_le_LT : L ⊔ conjClosure V H ≤ L ⊔ T := sup_le_sup_left S.U_le_T L

theorem alpha_mem_range (x : ↥(L ⊔ conjClosure V H)) :
    S.D.alpha ⟨x, S.LU_le_normV x.2⟩ ∈
      (natAct : SL(2, GaloisField 2 n) →* MulAut (Wm (GaloisField 2 n))).range := by
  let Zs : Subgroup G :=
    ((natAct : SL(2, GaloisField 2 n) →* MulAut (Wm (GaloisField 2 n))).range.comap
      S.D.alpha).map (Subgroup.normalizer (V : Set G)).subtype
  have hL : L ≤ Zs := fun l hl =>
    ⟨⟨l, S.D.hnorm hl⟩, Subgroup.mem_comap.2 (by
      rw [S.D.alpha_of_mem ⟨l, hl⟩]
      exact ⟨_, rfl⟩), rfl⟩
  have hU : conjClosure V H ≤ Zs := fun u hu =>
    ⟨⟨u, S.U_le_normV hu⟩, Subgroup.mem_comap.2 (by
      obtain ⟨b, hb⟩ := S.alpha_U_eq_e12 hu
      rw [hb]
      exact ⟨_, rfl⟩), rfl⟩
  obtain ⟨y, hy, hyx⟩ := (sup_le hL hU) x.2
  have : y = ⟨x, S.LU_le_normV x.2⟩ := Subtype.ext hyx
  rw [← this]
  exact Subgroup.mem_comap.1 hy

@[expose] noncomputable def Phi : ↥(L ⊔ conjClosure V H) →* SL(2, GaloisField 2 n) :=
  S.D.actSL _ S.LU_le_normV S.alpha_mem_range

theorem natAct_Phi (x : ↥(L ⊔ conjClosure V H)) :
    natAct (S.Phi x) = S.D.alpha ⟨x, S.LU_le_normV x.2⟩ :=
  S.D.natAct_actSL _ S.LU_le_normV S.alpha_mem_range x

theorem Phi_of_L (a : L) :
    S.Phi ⟨a, (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2⟩ = S.D.θ a := by
  apply natAct_injective
  rw [S.natAct_Phi]
  exact S.D.alpha_of_mem a

theorem Phi_eq_one_iff (x : ↥(L ⊔ conjClosure V H)) :
    S.Phi x = 1 ↔ (x : G) ∈ pCoreOf 2 (L ⊔ T) := by
  have h1 : S.Phi x = 1 ↔ S.D.alpha ⟨x, S.LU_le_normV x.2⟩ = 1 := by
    rw [← S.natAct_Phi]
    constructor
    · intro h
      rw [h, map_one]
    · intro h
      apply natAct_injective
      rw [h, map_one]
  rw [h1]
  exact S.alpha_eq_one_iff_mem_O (S.LU_le_LT x.2)

theorem Phi_of_U {u : G} (hu : u ∈ conjClosure V H) :
    ∃ b : GaloisField 2 n,
      S.Phi ⟨u, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hu⟩ = e12 b := by
  obtain ⟨b, hb⟩ := S.alpha_U_eq_e12 hu
  refine ⟨b, natAct_injective ?_⟩
  rw [S.natAct_Phi]
  exact hb

end L2Setting

namespace L2Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L2Setting n V V₁ L T H)

include S

omit [Finite G] in
theorem conj_mem_V₁_of_stab (a : L) (ha : (S.D.θ a).1 1 0 = 0) (v : V) (hv : (v : G) ∈ V₁) :
    (a : G) * v * (a : G)⁻¹ ∈ V₁ := by
  obtain ⟨c, hc⟩ := (S.D.line v).1 hv
  have h1 := (S.D.line (conjAct V ⟨a, S.D.hnorm a.2⟩ v)).2 ⟨c * (S.D.θ a).1 0 0, ?_⟩
  · simpa [conjAct_coe_apply] using h1
  · rw [S.D.equiv, natAct_apply, toAdd_ofAdd, hc, smul_comm, smul_e0, ha]
    ext i
    fin_cases i <;> simp

omit [Finite G] in
theorem mem_normalizer_V₁_of_stab (a : L) (ha : (S.D.θ a).1 1 0 = 0) :
    (a : G) ∈ Subgroup.normalizer (V₁ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact S.conj_mem_V₁_of_stab a ha ⟨h, S.hyp.base.le_V hh⟩ hh
  · intro hh
    have hV : (a : G) * h * (a : G)⁻¹ ∈ V := S.hyp.base.le_V hh
    have hhV : h ∈ V := (Subgroup.mem_normalizer_iff.1 (S.D.hnorm a.2) h).2 hV
    have ha' : (S.D.θ a⁻¹).1 1 0 = 0 := by rw [map_inv, inv_lower_left, ha, neg_zero]
    have := S.conj_mem_V₁_of_stab a⁻¹ ha' ⟨(a : G) * h * (a : G)⁻¹, hV⟩ hh
    simpa [mul_assoc] using this

theorem exists_l1 (d : (GaloisField 2 n)ˣ) :
    ∃ a : L, (a : G) ∈ lOne L V₁ ∧ S.D.θ a = dgm d := by
  rcases card_two_or_exists_sq_ne_one (F := GaloisField 2 n) with h2 | ⟨a, ha0, ha1⟩
  · refine ⟨1, one_mem _, ?_⟩
    have hd : d = 1 := by
      ext
      rcases eq_zero_or_one_of_card_two h2 (d : GaloisField 2 n) with h | h
      · exact absurd h d.ne_zero
      · simpa using h
    rw [hd, dgm_one, map_one]
  · have hrange : S.D.θ.range = ⊤ := by rw [S.D.range_eq]; exact Matrix.SL2.commutator_eq_top ha0 ha1
    obtain ⟨a₀, ha₀⟩ : dgm d ∈ S.D.θ.range := by rw [hrange]; exact Subgroup.mem_top _
    have hstab : (S.D.θ a₀).1 1 0 = 0 := by rw [ha₀]; simp
    have hnorm := S.mem_normalizer_V₁_of_stab a₀ hstab
    set N₀ : Subgroup L := (L ⊓ Subgroup.normalizer (V₁ : Set G)).subgroupOf L with hN₀
    have ha₀N : a₀ ∈ N₀ := Subgroup.mem_subgroupOf.2 ⟨a₀.2, hnorm⟩
    have hmem : dgm d ∈ oTwoUpper (N₀.map S.D.θ) :=
      mem_oTwoUpper_of_odd ⟨a₀, ha₀N, ha₀⟩ (odd_orderOf_dgm d)
    rw [oTwoUpper_map S.D.θ N₀] at hmem
    obtain ⟨a₁, ha₁, ha₁θ⟩ := hmem
    refine ⟨a₁, ?_, ha₁θ⟩
    have h3 := oTwoUpper_map L.subtype N₀
    have h4 : N₀.map L.subtype = L ⊓ Subgroup.normalizer (V₁ : Set G) := by
      rw [hN₀, Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.2 inf_le_left
    rw [h4] at h3
    have h5 : (a₁ : G) ∈ (oTwoUpper N₀).map L.subtype := ⟨a₁, ha₁, rfl⟩
    rw [← h3] at h5
    exact h5

end L2Setting

namespace L2Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L2Setting n V V₁ L T H)

include S

@[expose] noncomputable def betaU : ↥(conjClosure V H) →* SL(2, GaloisField 2 n) :=
  S.Phi.comp (Subgroup.inclusion (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H))

theorem betaU_apply (u : ↥(conjClosure V H)) :
    S.betaU u = S.Phi ⟨u, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u.2⟩ := rfl

theorem betaU_mem_Rg (u : ↥(conjClosure V H)) : S.betaU u ∈ Rg (GaloisField 2 n) := by
  obtain ⟨b, hb⟩ := S.Phi_of_U u.2
  rw [betaU_apply, hb]
  exact e12_mem_Rg b

theorem betaU_eq_one_iff (u : ↥(conjClosure V H)) :
    S.betaU u = 1 ↔ (u : G) ∈ pCoreOf 2 (L ⊔ T) :=
  S.Phi_eq_one_iff _

@[expose] noncomputable def Ubar : Subgroup SL(2, GaloisField 2 n) := S.betaU.range

theorem Ubar_le_Rg : S.Ubar ≤ Rg (GaloisField 2 n) := by
  rintro _ ⟨u, rfl⟩
  exact S.betaU_mem_Rg u

theorem Ubar_ne_bot : S.Ubar ≠ ⊥ := by
  intro h
  apply S.hyp.U_ne
  intro u hu
  have h1 : S.betaU ⟨u, hu⟩ ∈ S.Ubar := ⟨⟨u, hu⟩, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  exact (S.betaU_eq_one_iff ⟨u, hu⟩).1 h1

theorem Ubar_torus (d : (GaloisField 2 n)ˣ) (x : SL(2, GaloisField 2 n)) (hx : x ∈ S.Ubar) :
    dgm d * x * (dgm d)⁻¹ ∈ S.Ubar := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨a, ha1, haθ⟩ := S.exists_l1 d
  have haH : (a : G) ∈ H := S.hyp.base.lOne_sup_le ((le_sup_left : lOne L V₁ ≤ lOne L V₁ ⊔ T) ha1)
  have hU : (a : G) * u * (a : G)⁻¹ ∈ conjClosure V H :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure V H haH) u).1 u.2
  refine ⟨⟨(a : G) * u * (a : G)⁻¹, hU⟩, ?_⟩
  have hL : (a : G) ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2
  have hu' : (u : G) ∈ L ⊔ conjClosure V H := (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u.2
  have h1 : (⟨(a : G) * u * (a : G)⁻¹, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hU⟩ :
      ↥(L ⊔ conjClosure V H)) = ⟨a, hL⟩ * ⟨u, hu'⟩ * ⟨a, hL⟩⁻¹ := Subtype.ext (by simp)
  rw [betaU_apply, betaU_apply, h1, map_mul, map_mul, map_inv]
  have h2 : S.Phi ⟨a, hL⟩ = dgm d := by rw [S.Phi_of_L a, haθ]
  rw [h2]

theorem Ubar_eq_Rg : S.Ubar = Rg (GaloisField 2 n) := by
  rcases Rg_torus_irreducible S.Ubar S.Ubar_le_Rg (fun d x hx => S.Ubar_torus d x hx) with h | h
  · exact absurd h S.Ubar_ne_bot
  · exact h

theorem Phi_surjective : Function.Surjective S.Phi := by
  have hrange : S.Phi.range = ⊤ := by
    rw [eq_top_iff, ← commutator_sup_Rg (F := GaloisField 2 n)]
    refine sup_le ?_ ?_
    · rw [← S.D.range_eq]
      rintro _ ⟨a, rfl⟩
      exact ⟨⟨a, (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2⟩, S.Phi_of_L a⟩
    · rw [← S.Ubar_eq_Rg]
      rintro _ ⟨u, rfl⟩
      exact ⟨⟨u, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u.2⟩, rfl⟩
  exact MonoidHom.range_eq_top.1 hrange

end L2Setting

theorem secImg_equiv_of_hom {A B X : Subgroup G} [(B.subgroupOf A).Normal] (hXA : X ≤ A)
    {M : Type*} [Group M] (Φ : ↥X →* M) (hΦ : Function.Surjective Φ)
    (hker : ∀ x : X, Φ x = 1 ↔ (x : G) ∈ B) :
    ∃ e : ↥(secImg A B X) ≃* M,
      ∀ x : X, e ⟨secMk A B ⟨x, hXA x.2⟩, secMk_mem_secImg x.2⟩ = Φ x := by
  let f : ↥X →* ↥(secImg A B X) :=
    { toFun := fun x => ⟨secMk A B ⟨x, hXA x.2⟩, secMk_mem_secImg x.2⟩
      map_one' := Subtype.ext (map_one (secMk A B))
      map_mul' := fun x y => Subtype.ext (map_mul (secMk A B) ⟨x, hXA x.2⟩ ⟨y, hXA y.2⟩) }
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := mem_secImg.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hle : f.ker ≤ Φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have : secMk A B ⟨x, hXA x.2⟩ = 1 := congrArg Subtype.val hx
    exact (hker x).2 ((secMk_eq_one_iff (A := A) (B := B) (x := ⟨x, hXA x.2⟩)).1 this)
  let Φ' := f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf) ⟨Φ, hle⟩
  have hΦ' : ∀ x, Φ' (f x) = Φ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply f _ _ ⟨Φ, hle⟩ x
  have hinj : Function.Injective Φ' := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨x, rfl⟩ := hf y
    rw [hΦ'] at hy
    have hxB : (x : G) ∈ B := (hker x).1 hy
    apply Subtype.ext
    show secMk A B ⟨x, hXA x.2⟩ = 1
    rw [secMk_eq_one_iff]
    exact hxB
  have hsurj : Function.Surjective Φ' := by
    intro m
    obtain ⟨x, rfl⟩ := hΦ m
    exact ⟨f x, hΦ' x⟩
  exact ⟨MulEquiv.ofBijective Φ' ⟨hinj, hsurj⟩, fun x => hΦ' x⟩

@[expose] def rconj (X : Subgroup G) (g : G) : Subgroup G := X.map (MulAut.conj g⁻¹).toMonoidHom

theorem mem_rconj {X : Subgroup G} {g y : G} : y ∈ rconj X g ↔ g * y * g⁻¹ ∈ X := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro h
    exact ⟨g * y * g⁻¹, h, by simp [mul_assoc]⟩

theorem inv_mul_mul_mem_rconj {X : Subgroup G} {g x : G} (hx : x ∈ X) : g⁻¹ * x * g ∈ rconj X g := by
  rw [mem_rconj]
  simpa [mul_assoc] using hx

theorem eq_sup_of_normal_closure [Finite G] {L U I T₀ : Subgroup G} {g : G}
    (hL : L = oTwoUpper L) (hgL : g ∈ L) (hI : I = U ⊔ rconj U g)
    (hT₀U : T₀ ≤ Subgroup.normalizer (U : Set G)) (hT₀p : IsPGroup 2 T₀) (hT₀X : T₀ ≤ L ⊔ U)
    (hdec : ∀ x ∈ L ⊔ U, ∃ o ∈ T₀, ∃ i ∈ I, x = o * i) : I = L ⊔ U := by
  have hUI : U ≤ I := hI ▸ le_sup_left
  have hIX : I ≤ L ⊔ U := by
    rw [hI]
    refine sup_le le_sup_right ?_
    intro y hy
    rw [mem_rconj] at hy
    have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (inv_mem ((le_sup_left : L ≤ L ⊔ U) hgL))
      ((le_sup_right : U ≤ L ⊔ U) hy)) ((le_sup_left : L ≤ L ⊔ U) hgL)
  have hnormU : ∀ x ∈ L ⊔ U, ∀ y ∈ U, x⁻¹ * y * x ∈ I := by
    intro x hx y hy
    obtain ⟨o, ho, i, hi, rfl⟩ := hdec x hx
    have hy' : o⁻¹ * y * o ∈ U := by
      have := (Subgroup.mem_normalizer_iff''.1 (hT₀U ho) y).1 hy
      simpa using this
    have : (o * i)⁻¹ * y * (o * i) = i⁻¹ * (o⁻¹ * y * o) * i := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (inv_mem hi) (hUI hy')) hi
  have hnormI : ∀ x ∈ L ⊔ U, ∀ y ∈ I, x⁻¹ * y * x ∈ I := by
    intro x hx y hy
    rw [hI, Subgroup.sup_eq_closure] at hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact hnormU x hx y hy
      · have hy' : g * y * g⁻¹ ∈ U := mem_rconj.1 hy
        have h1 := hnormU (g * x) (Subgroup.mul_mem _ ((le_sup_left : L ≤ L ⊔ U) hgL) hx) _ hy'
        have : (g * x)⁻¹ * (g * y * g⁻¹) * (g * x) = x⁻¹ * y * x := by group
        rwa [this] at h1
    | one => simp
    | mul y z _ _ ihy ihz =>
      have : x⁻¹ * (y * z) * x = (x⁻¹ * y * x) * (x⁻¹ * z * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ ihy ihz
    | inv y _ ih =>
      have : x⁻¹ * y⁻¹ * x = (x⁻¹ * y * x)⁻¹ := by group
      rw [this]
      exact inv_mem ih
  have hXnorm : L ⊔ U ≤ Subgroup.normalizer (I : Set G) := by
    refine le_normalizer_of_conj_mem fun x hx y hy => ?_
    have := hnormI x⁻¹ (inv_mem hx) y hy
    simpa using this
  have h2 : ∀ x ∈ L ⊔ U, ∃ k : ℕ, x ^ 2 ^ k ∈ I := by
    intro x hx
    obtain ⟨o, ho, i, hi, rfl⟩ := hdec x hx
    exact exists_pow_two_pow_mem_of_le_normalizer (L := I) (T := T₀)
      (fun t ht => hXnorm (hT₀X ht)) hT₀p
      (Subgroup.mul_mem _ ((le_sup_right : T₀ ≤ I ⊔ T₀) ho) ((le_sup_left : I ≤ I ⊔ T₀) hi))
  have h3 : oTwoUpper (L ⊔ U) ≤ I := oTwoUpper_le_of_pow_mem h2
  have h4 : L ≤ I := calc
    L = oTwoUpper L := hL
    _ ≤ oTwoUpper (L ⊔ U) := oTwoUpper_mono le_sup_left
    _ ≤ I := h3
  exact le_antisymm hIX (sup_le h4 hUI)

abbrev starImg (L T X : Subgroup G) : Subgroup (SecQuot (L ⊔ T) (pCoreOf 2 (L ⊔ T))) :=
  secImg (L ⊔ T) (pCoreOf 2 (L ⊔ T)) X

namespace L2Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L2Setting n V V₁ L T H)

include S

theorem star_iso : ∃ e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* SL(2, GaloisField 2 n),
    ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x :=
  secImg_equiv_of_hom S.LU_le_LT S.Phi S.Phi_surjective S.Phi_eq_one_iff

theorem U_le_LT : conjClosure V H ≤ L ⊔ T := (S.U_le_T).trans le_sup_right

theorem isPGroup_U : IsPGroup 2 (conjClosure V H) := S.hyp.base.isPGroup_T.to_le S.U_le_T

theorem star_sylow :
    IsSylowTwoOf (starImg L T (conjClosure V H)) (starImg L T (L ⊔ conjClosure V H)) := by
  obtain ⟨e, he⟩ := S.star_iso
  refine ⟨secImg_mono le_sup_right, isPGroup_secImg S.U_le_LT S.isPGroup_U, ?_⟩
  set P' : Subgroup ↥(starImg L T (L ⊔ conjClosure V H)) :=
    (starImg L T (conjClosure V H)).subgroupOf (starImg L T (L ⊔ conjClosure V H)) with hP'
  have hmap : P'.map e.toMonoidHom = Rg (GaloisField 2 n) := by
    rw [← S.Ubar_eq_Rg]
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hxU, hxy⟩ := mem_secImg.1 (Subgroup.mem_subgroupOf.1 hy)
      have hxLU : (x : G) ∈ L ⊔ conjClosure V H :=
        (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hxU
      have hyx : y = ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT hxLU⟩,
          secMk_mem_secImg hxLU⟩ := Subtype.ext hxy.symm
      refine ⟨⟨x, hxU⟩, ?_⟩
      rw [hyx]
      exact (he ⟨x, hxLU⟩).symm
    · rintro ⟨u, rfl⟩
      have huLU : (u : G) ∈ L ⊔ conjClosure V H :=
        (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u.2
      refine ⟨⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨u, S.LU_le_LT huLU⟩, secMk_mem_secImg huLU⟩,
        Subgroup.mem_subgroupOf.2 (secMk_mem_secImg u.2), ?_⟩
      exact he ⟨u, huLU⟩
  have h1 : (P'.map e.toMonoidHom).index = P'.index := Subgroup.index_map_equiv P' e
  rw [hmap] at h1
  change ¬ 2 ∣ P'.index
  rw [← h1]
  exact Rg_index_odd

end L2Setting

namespace L2Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L2Setting n V V₁ L T H)

include S

omit [Finite G] in
theorem lower_left_ne_zero {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    (S.D.θ ⟨g, hg⟩).1 1 0 ≠ 0 := fun h =>
  hgN (S.mem_normalizer_V₁_of_stab ⟨g, hg⟩ h)

theorem Phi_I_surjective {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    ∀ A : SL(2, GaloisField 2 n), ∃ i : ↥(L ⊔ conjClosure V H),
      (i : G) ∈ conjClosure V H ⊔ rconj (conjClosure V H) g ∧ S.Phi i = A := by
  set U := conjClosure V H with hU
  have hθ := S.lower_left_ne_zero hg hgN
  have htop := Rg_sup_conj_eq_top (S.D.θ ⟨g, hg⟩) hθ
  let J : Subgroup SL(2, GaloisField 2 n) :=
    ((U ⊔ rconj U g).subgroupOf (L ⊔ U)).map S.Phi
  have hgLU : g ∈ L ⊔ U := (le_sup_left : L ≤ L ⊔ U) hg
  have hRg : Rg (GaloisField 2 n) ≤ J := by
    rw [← S.Ubar_eq_Rg]
    rintro _ ⟨u, rfl⟩
    exact ⟨⟨u, (le_sup_right : U ≤ L ⊔ U) u.2⟩,
      Subgroup.mem_subgroupOf.2 ((le_sup_left : U ≤ U ⊔ rconj U g) u.2), rfl⟩
  have hconj : (Rg (GaloisField 2 n)).map (MulAut.conj (S.D.θ ⟨g, hg⟩)⁻¹).toMonoidHom ≤ J := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← S.Ubar_eq_Rg] at hr
    obtain ⟨u, rfl⟩ := hr
    have hu : (u : G) ∈ L ⊔ U := (le_sup_right : U ≤ L ⊔ U) u.2
    have hgu : g⁻¹ * u * g ∈ U ⊔ rconj U g :=
      (le_sup_right : rconj U g ≤ U ⊔ rconj U g) (inv_mul_mul_mem_rconj u.2)
    have hguLU : g⁻¹ * u * g ∈ L ⊔ U :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (inv_mem hgLU) hu) hgLU
    refine ⟨⟨g⁻¹ * u * g, hguLU⟩, Subgroup.mem_subgroupOf.2 hgu, ?_⟩
    have h1 : (⟨g⁻¹ * u * g, hguLU⟩ : ↥(L ⊔ U)) = ⟨g, hgLU⟩⁻¹ * ⟨u, hu⟩ * ⟨g, hgLU⟩ :=
      Subtype.ext (by simp)
    rw [h1, map_mul, map_mul, map_inv, S.Phi_of_L ⟨g, hg⟩]
    simp [betaU_apply]
  intro A
  have hA : A ∈ J := by
    have : A ∈ Rg (GaloisField 2 n) ⊔ (Rg (GaloisField 2 n)).map
        (MulAut.conj (S.D.θ ⟨g, hg⟩)⁻¹).toMonoidHom := by rw [htop]; exact Subgroup.mem_top A
    exact (sup_le hRg hconj) this
  obtain ⟨i, hi, rfl⟩ := hA
  exact ⟨i, Subgroup.mem_subgroupOf.1 hi, rfl⟩

theorem G23_two {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    conjClosure V H ⊔ rconj (conjClosure V H) g = L ⊔ conjClosure V H := by
  set U := conjClosure V H with hU
  have hdec : ∀ x ∈ L ⊔ U, ∃ o ∈ pCoreOf 2 (L ⊔ T) ⊓ (L ⊔ U), ∃ i ∈ U ⊔ rconj U g, x = o * i := by
    intro x hx
    obtain ⟨i, hiI, hi⟩ := S.Phi_I_surjective hg hgN (S.Phi ⟨x, hx⟩)
    refine ⟨x * (i : G)⁻¹, ⟨?_, ?_⟩, i, hiI, by group⟩
    · have h1 : S.Phi (⟨x, hx⟩ * i⁻¹) = 1 := by
        rw [map_mul, map_inv, ← hi, mul_inv_cancel]
      exact (S.Phi_eq_one_iff _).1 h1
    · exact Subgroup.mul_mem _ hx (inv_mem i.2)
  exact eq_sup_of_normal_closure (T₀ := pCoreOf 2 (L ⊔ T) ⊓ (L ⊔ U)) S.hyp.base.oTwo_eq hg rfl
    (fun x hx => S.hyp.base.G22_three.2 (S.O_le_T hx.1))
    ((pCoreOf_isPGroup 2 (L ⊔ T)).to_le inf_le_left) inf_le_right hdec

end L2Setting

namespace L2Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L2Setting n V V₁ L T H)

include S

omit [Finite G] in
theorem V_le_rconj_U {g : G} (hg : g ∈ L) : V ≤ rconj (conjClosure V H) g := by
  intro v hv
  rw [mem_rconj]
  exact (le_conjClosure V H) ((Subgroup.mem_normalizer_iff.1 (S.D.hnorm hg) v).1 hv)

omit [Finite G] in
theorem V₁_le_rconj_V {g : G} (hg : g ∈ L) : rconj V₁ g ≤ V := by
  intro y hy
  rw [mem_rconj] at hy
  have h1 : g * y * g⁻¹ ∈ V := S.hyp.base.le_V hy
  exact (Subgroup.mem_normalizer_iff.1 (S.D.hnorm hg) y).2 h1

omit [Finite G] in
theorem V₁_inf_rconj {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    V₁ ⊓ rconj V₁ g = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
  rw [mem_rconj] at hy2
  have hyV : y ∈ V := S.hyp.base.le_V hy1
  have hθ := S.lower_left_ne_zero hg hgN
  obtain ⟨c, hc⟩ := (S.D.line ⟨y, hyV⟩).1 hy1
  have hgyV : g * y * g⁻¹ ∈ V := S.hyp.base.le_V hy2
  have h1 : conjAct V ⟨g, S.D.hnorm hg⟩ ⟨y, hyV⟩ = ⟨g * y * g⁻¹, hgyV⟩ :=
    Subtype.ext (by rw [conjAct_coe_apply])
  obtain ⟨c', hc'⟩ := (S.D.line ⟨g * y * g⁻¹, hgyV⟩).1 hy2
  have h2 := S.D.equiv ⟨g, hg⟩ ⟨y, hyV⟩
  rw [h1, natAct_apply] at h2
  have h3 := congrArg Multiplicative.toAdd h2
  rw [toAdd_ofAdd, hc', hc, smul_comm, smul_e0] at h3
  have h4 := congrFun h3 1
  simp at h4
  rcases h4 with h4 | h4
  · have : Multiplicative.toAdd (S.D.ψ ⟨y, hyV⟩) = 0 := by rw [hc, h4, zero_smul]
    have h5 : S.D.ψ ⟨y, hyV⟩ = 1 := Multiplicative.toAdd.injective (by simpa using this)
    have h6 : (⟨y, hyV⟩ : V) = 1 := S.D.ψ.injective (h5.trans (map_one S.D.ψ).symm)
    have := congrArg Subtype.val h6
    simpa using this
  · exact absurd h4 hθ

theorem rconj_commutator_mem {g x y : G} (hx : x ∈ rconj (conjClosure V H) g)
    (hy : y ∈ rconj (conjClosure V H) g) : x * y * x⁻¹ * y⁻¹ ∈ rconj V₁ g := by
  rw [mem_rconj] at hx hy ⊢
  have h := S.hyp.base.G22_commutator_mem hx hy
  have : g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ =
      (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ := by group
  rwa [this]

theorem rconj_sq_mem {g x : G} (hx : x ∈ rconj (conjClosure V H) g) : x ^ 2 ∈ rconj V₁ g := by
  rw [mem_rconj] at hx ⊢
  have h := S.hyp.base.G22_sq_mem hx
  have : g * x ^ 2 * g⁻¹ = (g * x * g⁻¹) ^ 2 := (conj_pow).symm
  rwa [this]

theorem isElemAbelian_inter {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    IsElemAbelian 2 (conjClosure V H ⊓ rconj (conjClosure V H) g) := by
  have hTI := S.V₁_inf_rconj hg hgN
  have hcomm : ∀ x ∈ conjClosure V H ⊓ rconj (conjClosure V H) g,
      ∀ y ∈ conjClosure V H ⊓ rconj (conjClosure V H) g, x * y = y * x := by
    intro x hx y hy
    have h1 := S.hyp.base.G22_commutator_mem hx.1 hy.1
    have h2 := S.rconj_commutator_mem hx.2 hy.2
    have h3 : x * y * x⁻¹ * y⁻¹ ∈ V₁ ⊓ rconj V₁ g := ⟨h1, h2⟩
    rw [hTI, Subgroup.mem_bot] at h3
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h3, one_mul]
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  have h1 := S.hyp.base.G22_sq_mem hx.1
  have h2 := S.rconj_sq_mem hx.2
  have h3 : x ^ 2 ∈ V₁ ⊓ rconj V₁ g := ⟨h1, h2⟩
  rw [hTI, Subgroup.mem_bot] at h3
  exact h3

end L2Setting

namespace L2Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L2Setting n V V₁ L T H)

include S

theorem I_le_normV {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    conjClosure V H ⊔ rconj (conjClosure V H) g ≤ Subgroup.normalizer (V : Set G) := by
  rw [S.G23_two hg hgN]
  exact S.LU_le_normV

theorem commutator_inter_le {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    ⁅conjClosure V H ⊓ rconj (conjClosure V H) g,
      conjClosure V H ⊔ rconj (conjClosure V H) g⁆ ≤ V := by
  set U := conjClosure V H with hU
  have hIV := S.I_le_normV hg hgN
  rw [Subgroup.commutator_le]
  intro x hx y hy
  show x * y * x⁻¹ * y⁻¹ ∈ V
  rw [Subgroup.sup_eq_closure] at hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact S.hyp.base.le_V (S.hyp.base.G22_commutator_mem hx.1 hy)
    · exact S.V₁_le_rconj_V hg (S.rconj_commutator_mem hx.2 hy)
  | one => simp
  | mul y z hy hz ihy ihz =>
    have hyI : y ∈ U ⊔ rconj U g := by rw [Subgroup.sup_eq_closure]; exact hy
    have h1 : y * (x * z * x⁻¹ * z⁻¹) * y⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hIV hyI) _).1 ihz
    have : x * (y * z) * x⁻¹ * (y * z)⁻¹ =
        (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
    rw [this]
    exact V.mul_mem ihy h1
  | inv y hy ih =>
    have hyI : y ∈ U ⊔ rconj U g := by rw [Subgroup.sup_eq_closure]; exact hy
    have h1 : y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 (hIV (inv_mem hyI)) _).1 (V.inv_mem ih)
      simpa [mul_assoc] using this
    have : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y := by group
    rw [this]
    exact h1

theorem inter_le_normalizer {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    conjClosure V H ⊔ rconj (conjClosure V H) g ≤
      Subgroup.normalizer ((conjClosure V H ⊓ rconj (conjClosure V H) g : Subgroup G) : Set G) := by
  set U := conjClosure V H with hU
  have hc := S.commutator_inter_le hg hgN
  have hVS : V ≤ U ⊓ rconj U g := le_inf (le_conjClosure V H) (S.V_le_rconj_U hg)
  refine le_normalizer_of_conj_mem fun y hy x hx => ?_
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ V := hc (Subgroup.commutator_mem_commutator hx hy)
  have h2 : y * x * y⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ * x := by group
  rw [h2]
  exact Subgroup.mul_mem _ (hVS (V.inv_mem h1)) hx

theorem pCoreOf_I_le_O {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    pCoreOf 2 (conjClosure V H ⊔ rconj (conjClosure V H) g) ≤ pCoreOf 2 (L ⊔ T) := by
  set U := conjClosure V H with hU
  have hI := S.G23_two hg hgN
  have hLT : L ⊔ T ≤ Subgroup.normalizer ((U ⊔ rconj U g : Subgroup G) : Set G) := by
    rw [hI]
    refine sup_le ((le_sup_left : L ≤ L ⊔ U).trans Subgroup.le_normalizer) ?_
    intro t ht
    exact Subgroup.inf_normalizer_le_normalizer_sup L U
      (Subgroup.mem_inf.2 ⟨S.hyp.base.T_le_normL ht, S.hyp.base.G22_three.2 ht⟩)
  have hIle : U ⊔ rconj U g ≤ L ⊔ T := by rw [hI]; exact S.LU_le_LT
  refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hIle) ?_
    (pCoreOf_isPGroup 2 _)
  exact hLT.trans (normalizer_le_normalizer_pCoreOf 2 _)

theorem G23_four {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    V ≤ conjClosure V H ⊓ rconj (conjClosure V H) g ∧
      conjClosure V H ⊓ rconj (conjClosure V H) g ≤
        pCoreOf 2 (conjClosure V H ⊔ rconj (conjClosure V H) g) ∧
      V ≤ centerOf (pCoreOf 2 (conjClosure V H ⊔ rconj (conjClosure V H) g)) ∧
      conjClosure V H ⊔ rconj (conjClosure V H) g ≤ Subgroup.normalizer (V : Set G) ∧
      conjClosure V H ⊔ rconj (conjClosure V H) g ≤
        Subgroup.normalizer ((conjClosure V H ⊓ rconj (conjClosure V H) g : Subgroup G) : Set G) ∧
      conjClosure V H ⊔ rconj (conjClosure V H) g ≤
        Subgroup.normalizer
          (pCoreOf 2 (conjClosure V H ⊔ rconj (conjClosure V H) g) : Set G) := by
  set U := conjClosure V H with hU
  have hVS : V ≤ U ⊓ rconj U g := le_inf (le_conjClosure V H) (S.V_le_rconj_U hg)
  have hIV := S.I_le_normV hg hgN
  have hVI : V ≤ U ⊔ rconj U g := (le_conjClosure V H).trans le_sup_left
  have hS₂N := S.inter_le_normalizer hg hgN
  refine ⟨hVS, ?_, ?_, hIV, hS₂N, le_normalizer_pCoreOf 2 _⟩
  · exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_left) hS₂N
      (S.isPGroup_U.to_le inf_le_left)
  · have hVS' : V ≤ pCoreOf 2 (U ⊔ rconj U g) :=
      le_pCoreOf_of_le_normalizer 2 hVI hIV S.isPGroup_V
    intro v hv
    refine ⟨hVS' hv, Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
    have h1 := S.O_centralizes_V s (S.pCoreOf_I_le_O hg hgN hs) v hv
    calc s * v = (s * v * s⁻¹) * s := by group
      _ = v * s := by rw [h1]

end L2Setting

namespace AlmostSpecialL2Hyp

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialL2Hyp n V V₁ L T H)

include hyp

theorem G23_one :
    Nonempty (↥(starImg L T (L ⊔ conjClosure V H)) ≃* SL(2, GaloisField 2 n)) ∧
      IsSylowTwoOf (starImg L T (conjClosure V H)) (starImg L T (L ⊔ conjClosure V H)) := by
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let S : L2Setting n V V₁ L T H := ⟨hyp, D⟩
  exact ⟨⟨S.star_iso.choose⟩, S.star_sylow⟩

theorem G23_two {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    conjClosure V H ⊔ rconj (conjClosure V H) g = L ⊔ conjClosure V H := by
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let S : L2Setting n V V₁ L T H := ⟨hyp, D⟩
  exact S.G23_two hg hgN

theorem G23_four {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    V ≤ conjClosure V H ⊓ rconj (conjClosure V H) g ∧
      conjClosure V H ⊓ rconj (conjClosure V H) g ≤
        pCoreOf 2 (conjClosure V H ⊔ rconj (conjClosure V H) g) ∧
      V ≤ centerOf (pCoreOf 2 (conjClosure V H ⊔ rconj (conjClosure V H) g)) ∧
      conjClosure V H ⊔ rconj (conjClosure V H) g ≤ Subgroup.normalizer (V : Set G) ∧
      conjClosure V H ⊔ rconj (conjClosure V H) g ≤
        Subgroup.normalizer ((conjClosure V H ⊓ rconj (conjClosure V H) g : Subgroup G) : Set G) ∧
      conjClosure V H ⊔ rconj (conjClosure V H) g ≤
        Subgroup.normalizer
          (pCoreOf 2 (conjClosure V H ⊔ rconj (conjClosure V H) g) : Set G) := by
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let S : L2Setting n V V₁ L T H := ⟨hyp, D⟩
  exact S.G23_four hg hgN

theorem G23_five {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    ⁅conjClosure V H ⊓ rconj (conjClosure V H) g,
        conjClosure V H ⊔ rconj (conjClosure V H) g⁆ ≤ V ∧
      IsElemAbelian 2 (conjClosure V H ⊓ rconj (conjClosure V H) g) := by
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let S : L2Setting n V V₁ L T H := ⟨hyp, D⟩
  exact ⟨S.commutator_inter_le hg hgN, S.isElemAbelian_inter hg hgN⟩

end AlmostSpecialL2Hyp

end CFSG.Quasithin

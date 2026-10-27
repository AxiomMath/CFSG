module

public import CFSG.Quasithin.Background.G2SL3
public import CFSG.Quasithin.Background.G2L2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type*} [Group G]

@[expose] def IsNaturalSL3Module (n : ℕ) (A K V V₁ : Subgroup G) : Prop :=
  ∃ (hnorm : A ≤ Subgroup.normalizer (V : Set G))
    (θ : A →* SL(3, GaloisField 2 n)) (ψ : V ≃* W3 (GaloisField 2 n)),
    Function.Surjective θ ∧ θ.ker = K.subgroupOf A ∧
    (∀ (a : A) (v : V), ψ (conjAct V ⟨a, hnorm a.2⟩ v) = natAct3 (θ a) (ψ v)) ∧
    ∃ w : Fin 3 → GaloisField 2 n, w ≠ 0 ∧
      ∀ v : V, (v : G) ∈ V₁ ↔ ∃ c : GaloisField 2 n, Multiplicative.toAdd (ψ v) = c • w

structure NatData3 (n : ℕ) (A K V V₁ : Subgroup G) where
  hnorm : A ≤ Subgroup.normalizer (V : Set G)
  θ : A →* SL(3, GaloisField 2 n)
  ψ : V ≃* W3 (GaloisField 2 n)
  surj : Function.Surjective θ
  ker_eq : θ.ker = K.subgroupOf A
  equiv : ∀ (a : A) (v : V), ψ (conjAct V ⟨a, hnorm a.2⟩ v) = natAct3 (θ a) (ψ v)
  line : ∀ v : V, (v : G) ∈ V₁ ↔
    ∃ c : GaloisField 2 n, Multiplicative.toAdd (ψ v) = c • vE (GaloisField 2 n) 0

theorem IsNaturalSL3Module.nonempty_data {n : ℕ} {A K V V₁ : Subgroup G}
    (h : IsNaturalSL3Module n A K V V₁) : Nonempty (NatData3 n A K V V₁) := by
  obtain ⟨hnorm, θ, ψ, hsurj, hker, hequiv, w, hw0, hw⟩ := h
  obtain ⟨g, hg0⟩ := exists_smul_eq_e0_3 w hw0
  have hg : g • w = vE (GaloisField 2 n) 0 := hg0
  refine ⟨{ hnorm := hnorm, θ := (MulAut.conj g).toMonoidHom.comp θ, ψ := ψ.trans (natAct3 g),
            surj := ?_, ker_eq := ?_, equiv := ?_, line := ?_ }⟩
  · intro y
    obtain ⟨a, ha⟩ := hsurj (g⁻¹ * y * g)
    exact ⟨a, by simp [ha]; group⟩
  · rw [← hker]
    ext a
    simp [MonoidHom.mem_ker]
  · intro a v
    have h1 := hequiv a v
    show natAct3 g (ψ (conjAct V ⟨a, hnorm a.2⟩ v)) =
      natAct3 (g * θ a * g⁻¹) (natAct3 g (ψ v))
    rw [h1, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]
  · intro v
    rw [hw v]
    have hg' : g⁻¹ • vE (GaloisField 2 n) 0 = w := by rw [← hg, inv_smul_smul]
    show (∃ c, _ = c • w) ↔ ∃ c, Multiplicative.toAdd (natAct3 g (ψ v)) = c • vE _ 0
    rw [natAct3_apply, toAdd_ofAdd]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [hc, smul_comm, ← hg]
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have : Multiplicative.toAdd (ψ v) = g⁻¹ • (c • vE (GaloisField 2 n) 0) := by
        rw [← hc, inv_smul_smul]
      rw [this, smul_comm, hg']

namespace NatData3

variable {n : ℕ} {A K V V₁ : Subgroup G} (D : NatData3 n A K V V₁)

@[expose] noncomputable def alpha :
    Subgroup.normalizer (V : Set G) →* MulAut (W3 (GaloisField 2 n)) :=
  (MulAut.congr D.ψ).toMonoidHom.comp (conjAct V)

theorem alpha_psi (x : Subgroup.normalizer (V : Set G)) (v : V) :
    D.alpha x (D.ψ v) = D.ψ (conjAct V x v) := by
  simp [alpha, MulAut.congr_apply]

theorem alpha_of_mem (a : A) : D.alpha ⟨a, D.hnorm a.2⟩ = natAct3 (D.θ a) := by
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

end NatData3

structure AlmostSpecialL3Hyp (n : ℕ) (V V₁ L T H : Subgroup G) : Prop where
  base : AlmostSpecialHyp V V₁ L T H
  n_pos : 0 < n
  V_eq : V = conjClosure V₁ L
  natural : IsNaturalSL3Module n L (pCoreOf 2 (L ⊔ T)) V V₁
  U_ne : ¬ conjClosure V H ≤ pCoreOf 2 (L ⊔ T)

structure L3Setting (n : ℕ) (V V₁ L T H : Subgroup G) where
  hyp : AlmostSpecialL3Hyp n V V₁ L T H
  D : NatData3 n L (pCoreOf 2 (L ⊔ T)) V V₁

namespace L3Setting

section NoFinite

variable {n : ℕ} {V V₁ L T H : Subgroup G} (S : L3Setting n V V₁ L T H)

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

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L3Setting n V V₁ L T H)

include S

theorem O_le_T : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf S.hyp.base.sylow_LT

omit [Finite G] in
theorem irreducible_L {Y : Subgroup G} (hYV : Y ≤ V)
    (hY : L ≤ Subgroup.normalizer (Y : Set G)) : Y = ⊥ ∨ Y = V := by
  set D := S.D
  let Yw : Subgroup (W3 (GaloisField 2 n)) := (Y.subgroupOf V).map D.ψ.toMonoidHom
  have hinv : ∀ A : SL(3, GaloisField 2 n), ∀ x ∈ Yw, natAct3 A x ∈ Yw := by
    intro A x hx
    obtain ⟨a, rfl⟩ := D.surj A
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨conjAct V ⟨a, D.hnorm a.2⟩ y, ?_, D.equiv a y⟩
    show (conjAct V ⟨a, D.hnorm a.2⟩ y : V) ∈ Y.subgroupOf V
    rw [Subgroup.mem_subgroupOf, conjAct_coe_apply]
    exact (Subgroup.mem_normalizer_iff.1 (hY a.2) y).1 hy
  rcases natAct3_irreducible Yw hinv with h | h
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
  rw [NatData3.alpha_eq_one_iff]
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
        rw [NatData3.alpha_eq_one_iff]
        intro v
        have := Subgroup.mem_centralizer_iff.1 hlC.2 v v.2
        calc l * v * l⁻¹ = v * l * l⁻¹ := by rw [← this]
          _ = v := by group
      have h2 := S.D.alpha_of_mem ⟨l, hl⟩
      have h3 : natAct3 (S.D.θ ⟨l, hl⟩) = 1 := by rw [← h2]; exact h1
      have h4 : S.D.θ ⟨l, hl⟩ = 1 := natAct3_injective (h3.trans (map_one natAct3).symm)
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

end L3Setting

namespace L3Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L3Setting n V V₁ L T H)

include S

theorem U_le_T : conjClosure V H ≤ T := S.hyp.base.G22_three.1

theorem U_le_normV {u : G} (hu : u ∈ conjClosure V H) : u ∈ Subgroup.normalizer (V : Set G) :=
  S.hyp.base.T_le_normV (S.U_le_T hu)

theorem U_le_normL {u : G} (hu : u ∈ conjClosure V H) : u ∈ Subgroup.normalizer (L : Set G) :=
  S.hyp.base.T_le_normL (S.U_le_T hu)

theorem alpha_U_eq_tq {u : G} (hu : u ∈ conjClosure V H) :
    ∃ b c : GaloisField 2 n, S.D.alpha ⟨u, S.U_le_normV hu⟩ = natAct3 (tq b c) := by
  set D := S.D
  have hT : Triv (D.alpha ⟨u, S.U_le_normV hu⟩) := by
    intro w
    obtain ⟨v, rfl⟩ := D.ψ.surjective w
    rw [NatData3.alpha_psi]
    have hvU : (v : G) ∈ conjClosure V H := le_conjClosure V H v.2
    have hc : u * v * u⁻¹ * (v : G)⁻¹ ∈ V₁ := S.hyp.base.G22_commutator_mem hu hvU
    have hcV : u * v * u⁻¹ * (v : G)⁻¹ ∈ V := S.hyp.base.le_V hc
    have hconj : conjAct V ⟨u, S.U_le_normV hu⟩ v = ⟨u * v * u⁻¹ * (v : G)⁻¹, hcV⟩ * v := by
      apply Subtype.ext
      rw [conjAct_coe_apply]
      simp
    rw [hconj, map_mul, toAdd_mul]
    obtain ⟨c', hc'⟩ := (D.line ⟨u * v * u⁻¹ * (v : G)⁻¹, hcV⟩).1 hc
    simp [hc']
  have hb : ∀ A : SL(3, GaloisField 2 n), ∃ A' : SL(3, GaloisField 2 n),
      ∀ w : W3 (GaloisField 2 n),
        D.alpha ⟨u, S.U_le_normV hu⟩ (natAct3 A w) = natAct3 A' (D.alpha ⟨u, S.U_le_normV hu⟩ w) := by
    intro A
    obtain ⟨a, rfl⟩ := D.surj A
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
    have := congrArg (fun ρ : MulAut (W3 (GaloisField 2 n)) => ρ w) h1
    simpa using this
  have hc2 : ∃ k : ℕ, D.alpha ⟨u, S.U_le_normV hu⟩ ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem S.hyp.base.isPGroup_T (S.U_le_T hu)
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨u, S.U_le_normV hu⟩ : Subgroup.normalizer (V : Set G)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hk)
    rw [this, map_one]
  obtain ⟨b, c, hbc⟩ := normalizing_lemma3 _ hT hb hc2
  exact ⟨b, c, MulEquiv.ext hbc⟩

end L3Setting

namespace NatData3

variable {n : ℕ} {A K V V₁ : Subgroup G} (D : NatData3 n A K V V₁)

@[expose] noncomputable def actSL3 (X : Subgroup G) (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hr : ∀ x : X, D.alpha ⟨x, hX x.2⟩ ∈
      (natAct3 : SL(3, GaloisField 2 n) →* MulAut (W3 (GaloisField 2 n))).range) :
    X →* SL(3, GaloisField 2 n) :=
  (MonoidHom.ofInjective natAct3_injective).symm.toMonoidHom.comp
    ((D.alpha.comp (Subgroup.inclusion hX)).codRestrict _ hr)

theorem natAct3_actSL3 (X : Subgroup G) (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hr : ∀ x : X, D.alpha ⟨x, hX x.2⟩ ∈
      (natAct3 : SL(3, GaloisField 2 n) →* MulAut (W3 (GaloisField 2 n))).range)
    (x : X) : natAct3 (D.actSL3 X hX hr x) = D.alpha ⟨x, hX x.2⟩ := by
  have h1 := (MonoidHom.ofInjective (natAct3_injective (F := GaloisField 2 n))).apply_symm_apply
    ⟨D.alpha ⟨x, hX x.2⟩, hr x⟩
  have h2 := congrArg Subtype.val h1
  exact h2

end NatData3

namespace L3Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L3Setting n V V₁ L T H)

include S

theorem LU_le_normV : L ⊔ conjClosure V H ≤ Subgroup.normalizer (V : Set G) :=
  sup_le S.D.hnorm fun _ hu => S.U_le_normV hu

theorem LU_le_LT : L ⊔ conjClosure V H ≤ L ⊔ T := sup_le_sup_left S.U_le_T L

theorem alpha_mem_range (x : ↥(L ⊔ conjClosure V H)) :
    S.D.alpha ⟨x, S.LU_le_normV x.2⟩ ∈
      (natAct3 : SL(3, GaloisField 2 n) →* MulAut (W3 (GaloisField 2 n))).range := by
  let Zs : Subgroup G :=
    ((natAct3 : SL(3, GaloisField 2 n) →* MulAut (W3 (GaloisField 2 n))).range.comap
      S.D.alpha).map (Subgroup.normalizer (V : Set G)).subtype
  have hL : L ≤ Zs := fun l hl =>
    ⟨⟨l, S.D.hnorm hl⟩, Subgroup.mem_comap.2 (by
      rw [S.D.alpha_of_mem ⟨l, hl⟩]
      exact ⟨_, rfl⟩), rfl⟩
  have hU : conjClosure V H ≤ Zs := fun u hu =>
    ⟨⟨u, S.U_le_normV hu⟩, Subgroup.mem_comap.2 (by
      obtain ⟨b, c, hb⟩ := S.alpha_U_eq_tq hu
      rw [hb]
      exact ⟨_, rfl⟩), rfl⟩
  obtain ⟨y, hy, hyx⟩ := (sup_le hL hU) x.2
  have : y = ⟨x, S.LU_le_normV x.2⟩ := Subtype.ext hyx
  rw [← this]
  exact Subgroup.mem_comap.1 hy

@[expose] noncomputable def Phi : ↥(L ⊔ conjClosure V H) →* SL(3, GaloisField 2 n) :=
  S.D.actSL3 _ S.LU_le_normV S.alpha_mem_range

theorem natAct3_Phi (x : ↥(L ⊔ conjClosure V H)) :
    natAct3 (S.Phi x) = S.D.alpha ⟨x, S.LU_le_normV x.2⟩ :=
  S.D.natAct3_actSL3 _ S.LU_le_normV S.alpha_mem_range x

theorem Phi_of_L (a : L) :
    S.Phi ⟨a, (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2⟩ = S.D.θ a := by
  apply natAct3_injective
  rw [S.natAct3_Phi]
  exact S.D.alpha_of_mem a

theorem Phi_eq_one_iff (x : ↥(L ⊔ conjClosure V H)) :
    S.Phi x = 1 ↔ (x : G) ∈ pCoreOf 2 (L ⊔ T) := by
  have h1 : S.Phi x = 1 ↔ S.D.alpha ⟨x, S.LU_le_normV x.2⟩ = 1 := by
    rw [← S.natAct3_Phi]
    constructor
    · intro h
      rw [h, map_one]
    · intro h
      apply natAct3_injective
      rw [h, map_one]
  rw [h1]
  exact S.alpha_eq_one_iff_mem_O (S.LU_le_LT x.2)

theorem Phi_of_U {u : G} (hu : u ∈ conjClosure V H) :
    ∃ b c : GaloisField 2 n,
      S.Phi ⟨u, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hu⟩ = tq b c := by
  obtain ⟨b, c, hb⟩ := S.alpha_U_eq_tq hu
  refine ⟨b, c, natAct3_injective ?_⟩
  rw [S.natAct3_Phi]
  exact hb

theorem Phi_surjective : Function.Surjective S.Phi := by
  intro A
  obtain ⟨a, rfl⟩ := S.D.surj A
  exact ⟨⟨a, (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2⟩, S.Phi_of_L a⟩

end L3Setting

section LeviO2

variable {F : Type*} [Field F]

theorem blk_injective : Function.Injective (blk : SL(2, F) →* SL(3, F)) := by
  intro M N h
  apply Subtype.ext
  ext i j
  have := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F) (i.succ) (j.succ)) h
  fin_cases i <;> fin_cases j <;> simpa [blk_coe] using this

theorem e12_inv (b : F) : (e12 b)⁻¹ = e12 (-b) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← e12_add, add_neg_cancel, e12_zero]

@[expose] def wSL (F : Type*) [Field F] [CharP F 2] : SL(2, F) :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

theorem wSL_conj_e12 [CharP F 2] (c : F) : wSL F * e12 c * (wSL F)⁻¹ = e21 c := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wSL, e12, e21, Matrix.mul_apply, Fin.sum_univ_two]

theorem blk_mem_oTwoUpper [Finite F] [CharP F 2] {M : SL(2, F)} (hM : M ∈ commutator SL(2, F)) :
    blk M ∈ oTwoUpper (Pt (vE F 0)) := by
  let X : Subgroup SL(2, F) := (oTwoUpper (Pt (vE F 0))).comap blk
  have hXnorm : ∀ g x, x ∈ X → g * x * g⁻¹ ∈ X := by
    intro g x hx
    show blk (g * x * g⁻¹) ∈ oTwoUpper _
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_oTwoUpper (Subgroup.le_normalizer (blk_mem_Pt g)) hx
  rcases card_two_or_exists_sq_ne_one (F := F) with h2 | ⟨a, ha0, ha1⟩
  · have hc3 : c3 F ∈ X := by
      refine mem_oTwoUpper_of_odd (blk_mem_Pt _) ?_
      rw [orderOf_injective blk blk_injective, orderOf_c3]
      exact ⟨1, rfl⟩
    rw [commutator_eq_zpowers_c3 h2] at hM
    exact (Subgroup.zpowers_le.2 hc3) hM
  · let d : Fˣ := Units.mk0 a ha0
    have hd : dgm d ∈ X := by
      refine mem_oTwoUpper_of_odd (blk_mem_Pt _) ?_
      rw [orderOf_injective blk blk_injective]
      exact odd_orderOf_dgm d
    have hsq : (d : F) ^ 2 - 1 ≠ 0 := sub_ne_zero.2 ha1
    have he12 : ∀ c : F, e12 c ∈ X := by
      intro c
      have h1 := hXnorm (e12 (c / ((d : F) ^ 2 - 1))) (dgm d)⁻¹ (X.inv_mem hd)
      have h2 := X.mul_mem hd h1
      have : dgm d * (e12 (c / ((d : F) ^ 2 - 1)) * (dgm d)⁻¹ * (e12 (c / ((d : F) ^ 2 - 1)))⁻¹) =
          e12 c := by
        rw [e12_inv]
        calc dgm d * (e12 (c / ((d : F) ^ 2 - 1)) * (dgm d)⁻¹ * e12 (-(c / ((d : F) ^ 2 - 1))))
            = (dgm d * e12 (c / ((d : F) ^ 2 - 1)) * (dgm d)⁻¹) *
                e12 (-(c / ((d : F) ^ 2 - 1))) := by group
          _ = e12 ((d : F) ^ 2 * (c / ((d : F) ^ 2 - 1))) *
                e12 (-(c / ((d : F) ^ 2 - 1))) := by rw [dgm_conj_e12]
          _ = e12 ((d : F) ^ 2 * (c / ((d : F) ^ 2 - 1)) + -(c / ((d : F) ^ 2 - 1))) := by
              rw [e12_add]
          _ = e12 c := by
              congr 1
              field_simp
              ring
      rwa [this] at h2
    have he21 : ∀ c : F, e21 c ∈ X := fun c => by
      have := hXnorm (wSL F) _ (he12 c)
      rwa [wSL_conj_e12] at this
    have hXtop : ∀ A : SL(2, F), A ∈ X := by
      intro A
      refine Matrix.SL2.transvection_induction (fun A => A ∈ X) ?_ (fun A B hA hB => X.mul_mem hA hB) A
      intro i j hij c
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · rw [transvection_zero_one]
        exact he12 c
      · rw [transvection_one_zero]
        exact he21 c
      · exact absurd rfl hij
    exact hXtop M

end LeviO2

namespace L3Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L3Setting n V V₁ L T H)

include S

omit [Finite G] in
theorem conj_mem_V₁_of_stab (a : L) (ha : S.D.θ a ∈ Pt (vE (GaloisField 2 n) 0)) (v : V)
    (hv : (v : G) ∈ V₁) : (a : G) * v * (a : G)⁻¹ ∈ V₁ := by
  obtain ⟨c, hc⟩ := (S.D.line v).1 hv
  obtain ⟨r, hr⟩ := ha
  have h1 := (S.D.line (conjAct V ⟨a, S.D.hnorm a.2⟩ v)).2 ⟨c * r, ?_⟩
  · simpa [conjAct_coe_apply] using h1
  · rw [S.D.equiv, natAct3_apply, toAdd_ofAdd, hc, smul_comm, hr, smul_smul]

omit [Finite G] in
theorem mem_normalizer_V₁_of_stab (a : L) (ha : S.D.θ a ∈ Pt (vE (GaloisField 2 n) 0)) :
    (a : G) ∈ Subgroup.normalizer (V₁ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact S.conj_mem_V₁_of_stab a ha ⟨h, S.hyp.base.le_V hh⟩ hh
  · intro hh
    have hV : (a : G) * h * (a : G)⁻¹ ∈ V := S.hyp.base.le_V hh
    have hhV : h ∈ V := (Subgroup.mem_normalizer_iff.1 (S.D.hnorm a.2) h).2 hV
    have ha' : S.D.θ a⁻¹ ∈ Pt (vE (GaloisField 2 n) 0) := by
      rw [map_inv]
      exact inv_mem ha
    have := S.conj_mem_V₁_of_stab a⁻¹ ha' ⟨(a : G) * h * (a : G)⁻¹, hV⟩ hh
    simpa [mul_assoc] using this

omit [Finite G] in
theorem theta_mem_Pt_of_normalizer (a : L) (ha : (a : G) ∈ Subgroup.normalizer (V₁ : Set G)) :
    S.D.θ a ∈ Pt (vE (GaloisField 2 n) 0) := by
  set v₀ : V := S.D.ψ.symm (Multiplicative.ofAdd (vE (GaloisField 2 n) 0)) with hv₀
  have hψ : S.D.ψ v₀ = Multiplicative.ofAdd (vE (GaloisField 2 n) 0) :=
    MulEquiv.apply_symm_apply _ _
  have hv₀1 : (v₀ : G) ∈ V₁ := (S.D.line v₀).2 ⟨1, by rw [hψ, toAdd_ofAdd, one_smul]⟩
  have h1 : (a : G) * v₀ * (a : G)⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.1 ha _).1 hv₀1
  have hV : (a : G) * v₀ * (a : G)⁻¹ ∈ V := S.hyp.base.le_V h1
  have h2 : conjAct V ⟨a, S.D.hnorm a.2⟩ v₀ = ⟨(a : G) * v₀ * (a : G)⁻¹, hV⟩ :=
    Subtype.ext (by rw [conjAct_coe_apply])
  obtain ⟨c, hc⟩ := (S.D.line ⟨(a : G) * v₀ * (a : G)⁻¹, hV⟩).1 h1
  have h3 := S.D.equiv a v₀
  rw [h2, hψ, natAct3_apply, toAdd_ofAdd] at h3
  have h4 := congrArg Multiplicative.toAdd h3
  rw [toAdd_ofAdd, hc] at h4
  exact ⟨c, h4.symm⟩

omit [Finite G] in
theorem map_theta_N :
    ((L ⊓ Subgroup.normalizer (V₁ : Set G)).subgroupOf L).map S.D.θ =
      Pt (vE (GaloisField 2 n) 0) := by
  ext A
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact S.theta_mem_Pt_of_normalizer a (Subgroup.mem_subgroupOf.1 ha).2
  · intro hA
    obtain ⟨a, rfl⟩ := S.D.surj A
    exact ⟨a, Subgroup.mem_subgroupOf.2 ⟨a.2, S.mem_normalizer_V₁_of_stab a hA⟩, rfl⟩

theorem exists_l1_blk (M : SL(2, GaloisField 2 n)) (hM : M ∈ commutator SL(2, GaloisField 2 n)) :
    ∃ a : L, (a : G) ∈ lOne L V₁ ∧ S.D.θ a = blk M := by
  set N₀ : Subgroup L := (L ⊓ Subgroup.normalizer (V₁ : Set G)).subgroupOf L with hN₀
  have hmem : blk M ∈ oTwoUpper (N₀.map S.D.θ) := by
    rw [S.map_theta_N]
    exact blk_mem_oTwoUpper hM
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

@[expose] noncomputable def betaU : ↥(conjClosure V H) →* SL(3, GaloisField 2 n) :=
  S.Phi.comp (Subgroup.inclusion (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H))

theorem betaU_apply (u : ↥(conjClosure V H)) :
    S.betaU u = S.Phi ⟨u, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u.2⟩ := rfl

theorem betaU_mem_Qv (u : ↥(conjClosure V H)) : S.betaU u ∈ Qv (vE (GaloisField 2 n) 0) := by
  obtain ⟨b, c, hb⟩ := S.Phi_of_U u.2
  rw [betaU_apply, hb]
  exact tq_mem_Qv b c

theorem betaU_eq_one_iff (u : ↥(conjClosure V H)) :
    S.betaU u = 1 ↔ (u : G) ∈ pCoreOf 2 (L ⊔ T) :=
  S.Phi_eq_one_iff _

@[expose] noncomputable def Ubar : Subgroup SL(3, GaloisField 2 n) := S.betaU.range

theorem Ubar_le_Qv : S.Ubar ≤ Qv (vE (GaloisField 2 n) 0) := by
  rintro _ ⟨u, rfl⟩
  exact S.betaU_mem_Qv u

theorem Ubar_ne_bot : S.Ubar ≠ ⊥ := by
  intro h
  apply S.hyp.U_ne
  intro u hu
  have h1 : S.betaU ⟨u, hu⟩ ∈ S.Ubar := ⟨⟨u, hu⟩, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  exact (S.betaU_eq_one_iff ⟨u, hu⟩).1 h1

theorem Ubar_conj (M : SL(2, GaloisField 2 n)) (hM : M ∈ commutator SL(2, GaloisField 2 n))
    (x : SL(3, GaloisField 2 n)) (hx : x ∈ S.Ubar) : blk M * x * (blk M)⁻¹ ∈ S.Ubar := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨a, ha1, haθ⟩ := S.exists_l1_blk M hM
  have haH : (a : G) ∈ H :=
    S.hyp.base.lOne_sup_le ((le_sup_left : lOne L V₁ ≤ lOne L V₁ ⊔ T) ha1)
  have hU : (a : G) * u * (a : G)⁻¹ ∈ conjClosure V H :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure V H haH) u).1 u.2
  refine ⟨⟨(a : G) * u * (a : G)⁻¹, hU⟩, ?_⟩
  have hL : (a : G) ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2
  have hu' : (u : G) ∈ L ⊔ conjClosure V H :=
    (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u.2
  have h1 : (⟨(a : G) * u * (a : G)⁻¹, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) hU⟩ :
      ↥(L ⊔ conjClosure V H)) = ⟨a, hL⟩ * ⟨u, hu'⟩ * ⟨a, hL⟩⁻¹ := Subtype.ext (by simp)
  rw [betaU_apply, betaU_apply, h1, map_mul, map_mul, map_inv]
  have h2 : S.Phi ⟨a, hL⟩ = blk M := by rw [S.Phi_of_L a, haθ]
  rw [h2]

theorem Ubar_eq_Qv : S.Ubar = Qv (vE (GaloisField 2 n) 0) := by
  rcases Qv_irreducible S.Ubar S.Ubar_le_Qv S.Ubar_conj with h | h
  · exact absurd h S.Ubar_ne_bot
  · exact h

end L3Setting

namespace L3Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L3Setting n V V₁ L T H)

include S

theorem Ubar_eq_map : S.Ubar =
    ((conjClosure V H).subgroupOf (L ⊔ conjClosure V H)).map S.Phi := by
  ext A
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨⟨u, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u.2⟩,
      Subgroup.mem_subgroupOf.2 u.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩

theorem star_iso : ∃ e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* SL(3, GaloisField 2 n),
    ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x :=
  secImg_equiv_of_hom S.LU_le_LT S.Phi S.Phi_surjective S.Phi_eq_one_iff

theorem star_map_eq {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* SL(3, GaloisField 2 n)}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x)
    {X : Subgroup G} (hX : X ≤ L ⊔ conjClosure V H) :
    ((starImg L T X).subgroupOf (starImg L T (L ⊔ conjClosure V H))).map e.toMonoidHom =
      (X.subgroupOf (L ⊔ conjClosure V H)).map S.Phi := by
  ext A
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hxX, hxy⟩ := mem_secImg.1 (Subgroup.mem_subgroupOf.1 hy)
    have hxLU : (x : G) ∈ L ⊔ conjClosure V H := hX hxX
    have hyx : y = ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT hxLU⟩,
        secMk_mem_secImg hxLU⟩ := Subtype.ext hxy.symm
    refine ⟨⟨x, hxLU⟩, Subgroup.mem_subgroupOf.2 hxX, ?_⟩
    rw [hyx]
    exact (he ⟨x, hxLU⟩).symm
  · rintro ⟨x, hx, rfl⟩
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.1 hx
    refine ⟨⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩,
      Subgroup.mem_subgroupOf.2 (secMk_mem_secImg hxX), ?_⟩
    exact he x

theorem star_map_U {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* SL(3, GaloisField 2 n)}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x) :
    ((starImg L T (conjClosure V H)).subgroupOf
      (starImg L T (L ⊔ conjClosure V H))).map e.toMonoidHom = Qv (vE (GaloisField 2 n) 0) := by
  rw [S.star_map_eq he le_sup_right, ← S.Ubar_eq_map, S.Ubar_eq_Qv]

theorem star_map_N {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* SL(3, GaloisField 2 n)}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x) :
    ((starImg L T (L ⊓ Subgroup.normalizer (V₁ : Set G))).subgroupOf
      (starImg L T (L ⊔ conjClosure V H))).map e.toMonoidHom = Pt (vE (GaloisField 2 n) 0) := by
  rw [S.star_map_eq he (inf_le_left.trans le_sup_left)]
  ext A
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)
    have := S.theta_mem_Pt_of_normalizer ⟨x, hxL⟩ hxN
    rwa [← S.Phi_of_L ⟨x, hxL⟩] at this
  · intro hA
    rw [← S.map_theta_N] at hA
    obtain ⟨a, ha, rfl⟩ := hA
    refine ⟨⟨a, (le_sup_left : L ≤ L ⊔ conjClosure V H) a.2⟩,
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 ha), S.Phi_of_L a⟩

theorem U_le_LT : conjClosure V H ≤ L ⊔ T := (S.U_le_T).trans le_sup_right

theorem isPGroup_U : IsPGroup 2 (conjClosure V H) := S.hyp.base.isPGroup_T.to_le S.U_le_T

theorem mem_star_U_iff {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* SL(3, GaloisField 2 n)}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x)
    (y : ↥(starImg L T (L ⊔ conjClosure V H))) :
    (y : SecQuot (L ⊔ T) (pCoreOf 2 (L ⊔ T))) ∈ starImg L T (conjClosure V H) ↔
      e y ∈ Qv (vE (GaloisField 2 n) 0) := by
  rw [← S.star_map_U he]
  constructor
  · intro hy
    exact ⟨y, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  · rintro ⟨y', hy', hyy⟩
    have : y' = y := e.injective hyy
    rw [← this]
    exact Subgroup.mem_subgroupOf.1 hy'

theorem mem_star_N_iff {e : ↥(starImg L T (L ⊔ conjClosure V H)) ≃* SL(3, GaloisField 2 n)}
    (he : ∀ x : ↥(L ⊔ conjClosure V H),
      e ⟨secMk (L ⊔ T) (pCoreOf 2 (L ⊔ T)) ⟨x, S.LU_le_LT x.2⟩, secMk_mem_secImg x.2⟩ = S.Phi x)
    (y : ↥(starImg L T (L ⊔ conjClosure V H))) :
    (y : SecQuot (L ⊔ T) (pCoreOf 2 (L ⊔ T))) ∈
        starImg L T (L ⊓ Subgroup.normalizer (V₁ : Set G)) ↔
      e y ∈ Pt (vE (GaloisField 2 n) 0) := by
  rw [← S.star_map_N he]
  constructor
  · intro hy
    exact ⟨y, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  · rintro ⟨y', hy', hyy⟩
    have : y' = y := e.injective hyy
    rw [← this]
    exact Subgroup.mem_subgroupOf.1 hy'

theorem star_U_eq : starImg L T (conjClosure V H) =
    pCoreOf 2 (starImg L T (L ⊓ Subgroup.normalizer (V₁ : Set G))) := by
  obtain ⟨e, he⟩ := S.star_iso
  have hv0 : vE (GaloisField 2 n) 0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hUY : starImg L T (conjClosure V H) ≤ starImg L T (L ⊔ conjClosure V H) :=
    secImg_mono le_sup_right
  have hNY : starImg L T (L ⊓ Subgroup.normalizer (V₁ : Set G)) ≤
      starImg L T (L ⊔ conjClosure V H) := secImg_mono (inf_le_left.trans le_sup_left)
  apply le_antisymm
  ·
    have hUN : starImg L T (conjClosure V H) ≤
        starImg L T (L ⊓ Subgroup.normalizer (V₁ : Set G)) := by
      intro z hz
      exact (S.mem_star_N_iff he ⟨z, hUY hz⟩).2
        (Qv_le_Pt _ ((S.mem_star_U_iff he ⟨z, hUY hz⟩).1 hz))
    have key : ∀ m ∈ starImg L T (L ⊓ Subgroup.normalizer (V₁ : Set G)),
        ∀ z ∈ starImg L T (conjClosure V H), m * z * m⁻¹ ∈ starImg L T (conjClosure V H) := by
      intro m hm z hz
      have hmY := hNY hm
      have hzY := hUY hz
      have hw : m * z * m⁻¹ ∈ starImg L T (L ⊔ conjClosure V H) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hmY hzY) (Subgroup.inv_mem _ hmY)
      have := (S.mem_star_U_iff he ⟨m * z * m⁻¹, hw⟩).2
      have h1 : e ⟨m * z * m⁻¹, hw⟩ = e ⟨m, hmY⟩ * e ⟨z, hzY⟩ * (e ⟨m, hmY⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      apply this
      rw [h1]
      exact Qv_conj_mem hv0 ((S.mem_star_N_iff he ⟨m, hmY⟩).1 hm)
        ((S.mem_star_U_iff he ⟨z, hzY⟩).1 hz)
    have hnorm : starImg L T (L ⊓ Subgroup.normalizer (V₁ : Set G)) ≤
        Subgroup.normalizer (starImg L T (conjClosure V H) :
          Set (SecQuot (L ⊔ T) (pCoreOf 2 (L ⊔ T)))) := by
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro z
      refine ⟨fun hz => key m hm z hz, fun hz => ?_⟩
      have := key m⁻¹ (Subgroup.inv_mem _ hm) _ hz
      simpa [mul_assoc] using this
    exact le_pCoreOf_of_le_normalizer 2 hUN hnorm (isPGroup_secImg S.U_le_LT S.isPGroup_U)
  ·
    set Z := pCoreOf 2 (starImg L T (L ⊓ Subgroup.normalizer (V₁ : Set G))) with hZ
    have hZN : Z ≤ starImg L T (L ⊓ Subgroup.normalizer (V₁ : Set G)) := pCoreOf_le 2 _
    have hZY : Z ≤ starImg L T (L ⊔ conjClosure V H) := hZN.trans hNY
    let Z' : Subgroup SL(3, GaloisField 2 n) :=
      (Z.subgroupOf (starImg L T (L ⊔ conjClosure V H))).map e.toMonoidHom
    have hZ'P : Z' ≤ Pt (vE (GaloisField 2 n) 0) := by
      rintro _ ⟨z, hz, rfl⟩
      exact (S.mem_star_N_iff he z).1 (hZN (Subgroup.mem_subgroupOf.1 hz))
    have hZ'norm : ∀ p ∈ Pt (vE (GaloisField 2 n) 0), ∀ x ∈ Z', p * x * p⁻¹ ∈ Z' := by
      rintro p hp _ ⟨z, hz, rfl⟩
      obtain ⟨m, rfl⟩ := e.surjective p
      have hm : (m : SecQuot (L ⊔ T) (pCoreOf 2 (L ⊔ T))) ∈
          starImg L T (L ⊓ Subgroup.normalizer (V₁ : Set G)) := (S.mem_star_N_iff he m).2 hp
      have hmn := le_normalizer_pCoreOf 2 _ hm
      have hzZ : (z : SecQuot (L ⊔ T) (pCoreOf 2 (L ⊔ T))) ∈ Z := Subgroup.mem_subgroupOf.1 hz
      refine ⟨m * z * m⁻¹, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 hmn _).1 hzZ
      · simp
    have hZ'p : IsPGroup 2 Z' :=
      ((pCoreOf_isPGroup 2 _).of_equiv (Subgroup.subgroupOfEquivOfLe hZY).symm).map e.toMonoidHom
    have hle := normal_two_le_Qv Z' hZ'P hZ'norm hZ'p
    intro z hz
    have hzY : z ∈ starImg L T (L ⊔ conjClosure V H) := hZY hz
    have : e ⟨z, hzY⟩ ∈ Z' := ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
    exact (S.mem_star_U_iff he ⟨z, hzY⟩).2 (hle this)

theorem star_U_isElemAbelian : IsElemAbelian 2 (starImg L T (conjClosure V H)) ∧
    Nat.card ↥(starImg L T (conjClosure V H)) = 2 ^ (2 * n) := by
  obtain ⟨e, he⟩ := S.star_iso
  have hUY : starImg L T (conjClosure V H) ≤ starImg L T (L ⊔ conjClosure V H) :=
    secImg_mono le_sup_right
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext
    have hab : (⟨a, hUY a.2⟩ : ↥(starImg L T (L ⊔ conjClosure V H))) *
        ⟨b, hUY b.2⟩ = ⟨b, hUY b.2⟩ * ⟨a, hUY a.2⟩ := by
      apply e.injective
      rw [map_mul, map_mul]
      exact Qv_comm _ _ ((S.mem_star_U_iff he _).1 a.2) ((S.mem_star_U_iff he _).1 b.2)
    show (a : SecQuot (L ⊔ T) (pCoreOf 2 (L ⊔ T))) * b = b * a
    exact congrArg Subtype.val hab
  · have hxY := hUY hx
    have h1 : (⟨x, hxY⟩ : ↥(starImg L T (L ⊔ conjClosure V H))) ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, map_one, pow_two]
      exact Qv_sq _ ((S.mem_star_U_iff he ⟨x, hxY⟩).1 hx)
    exact congrArg Subtype.val h1
  · have h1 : Nat.card ↥(starImg L T (conjClosure V H)) =
        Nat.card ↥((starImg L T (conjClosure V H)).subgroupOf
          (starImg L T (L ⊔ conjClosure V H))) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUY).symm.toEquiv
    have h2 : Nat.card ↥((starImg L T (conjClosure V H)).subgroupOf
          (starImg L T (L ⊔ conjClosure V H))) =
        Nat.card ↥(((starImg L T (conjClosure V H)).subgroupOf
          (starImg L T (L ⊔ conjClosure V H))).map e.toMonoidHom) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv
    rw [h1, h2, S.star_map_U he, card_Qv, GaloisField.card 2 n S.hyp.n_pos.ne', ← pow_mul,
      mul_comm]

theorem commutator_V_U_eq : ⁅V, conjClosure V H⁆ = V₁ := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv u hu
    have h := S.hyp.base.G22_commutator_mem hu (le_conjClosure V H hv)
    have : ⁅v, u⁆ = (u * v * u⁻¹ * v⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact V₁.inv_mem h
  · intro x hx
    have hxV : x ∈ V := S.hyp.base.le_V hx
    obtain ⟨c, hc⟩ := (S.D.line ⟨x, hxV⟩).1 hx
    have hq : tq (1 : GaloisField 2 n) 0 ∈ S.Ubar := by
      rw [S.Ubar_eq_Qv]
      exact tq_mem_Qv 1 0
    obtain ⟨u, hu⟩ := hq
    have huU : (u : G) ∈ conjClosure V H := u.2
    have huN : (u : G) ∈ Subgroup.normalizer (V : Set G) := S.U_le_normV huU
    obtain ⟨v, hv⟩ : ∃ v : V, S.D.ψ v =
        Multiplicative.ofAdd (c • vE (GaloisField 2 n) 1) :=
      ⟨S.D.ψ.symm _, MulEquiv.apply_symm_apply _ _⟩
    have hα : S.D.alpha ⟨u, huN⟩ = natAct3 (tq 1 0) := by
      have h1 := S.natAct3_Phi ⟨u, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) huU⟩
      have h2 : S.Phi ⟨u, (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) huU⟩ = tq 1 0 :=
        hu
      rw [h2] at h1
      exact h1.symm
    have hwV : (v : G) * ((u : G) * (v : G)⁻¹ * (u : G)⁻¹) ∈ V :=
      V.mul_mem v.2 ((Subgroup.mem_normalizer_iff.1 huN _).1 (V.inv_mem v.2))
    have hψw : S.D.ψ ⟨(v : G) * ((u : G) * (v : G)⁻¹ * (u : G)⁻¹), hwV⟩ =
        S.D.ψ v * (S.D.alpha ⟨u, huN⟩ (S.D.ψ v))⁻¹ := by
      have e1 : (⟨(v : G) * ((u : G) * (v : G)⁻¹ * (u : G)⁻¹), hwV⟩ : V) =
          v * conjAct V ⟨u, huN⟩ v⁻¹ :=
        Subtype.ext (by rw [Subgroup.coe_mul, conjAct_coe_apply]; simp)
      rw [e1, map_mul, ← NatData3.alpha_psi, map_inv, map_inv]
    have hψx : S.D.ψ ⟨(v : G) * ((u : G) * (v : G)⁻¹ * (u : G)⁻¹), hwV⟩ = S.D.ψ ⟨x, hxV⟩ := by
      apply Multiplicative.toAdd.injective
      rw [hψw, hα, toAdd_mul, toAdd_inv, natAct3_apply, toAdd_ofAdd, hv, toAdd_ofAdd, hc]
      ext i
      fin_cases i <;> simp [tq_smul, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
    have hxeq : (v : G) * ((u : G) * (v : G)⁻¹ * (u : G)⁻¹) = x :=
      congrArg Subtype.val (S.D.ψ.injective hψx)
    have hcomm : ⁅(v : G), (u : G)⁆ ∈ ⁅V, conjClosure V H⁆ :=
      Subgroup.commutator_mem_commutator v.2 huU
    have e2 : ⁅(v : G), (u : G)⁆ = (v : G) * ((u : G) * (v : G)⁻¹ * (u : G)⁻¹) := by
      rw [commutatorElement_def]
      group
    rwa [e2, hxeq] at hcomm

end L3Setting

namespace AlmostSpecialL3Hyp

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialL3Hyp n V V₁ L T H)

include hyp

theorem G25_one :
    starImg L T (conjClosure V H) =
        pCoreOf 2 (starImg L T (L ⊓ Subgroup.normalizer (V₁ : Set G))) ∧
      IsElemAbelian 2 (starImg L T (conjClosure V H)) ∧
      Nat.card ↥(starImg L T (conjClosure V H)) = 2 ^ (2 * n) ∧
      ⁅V, conjClosure V H⁆ = V₁ := by
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let S : L3Setting n V V₁ L T H := ⟨hyp, D⟩
  exact ⟨S.star_U_eq, S.star_U_isElemAbelian.1, S.star_U_isElemAbelian.2, S.commutator_V_U_eq⟩

end AlmostSpecialL3Hyp

end CFSG.Quasithin

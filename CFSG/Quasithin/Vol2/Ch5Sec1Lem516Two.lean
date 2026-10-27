module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516TwoCoord
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Mod
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Orth
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QJ

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Setup.Offender
open scoped IsMulCommutative MatrixGroups Matrix Pointwise
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL diagSL coe_diagSL diagSL_conj)

variable {G : Type} [Group G]

namespace Setting516

variable {T L D R : Subgroup G}

theorem decomp [Finite G] (hS : Setting516 T L D R) {x : G} (hx : x ∈ T ⊔ D) :
    ∃ t ∈ T, ∃ δ ∈ D, t * δ = x := by
  have hx' : x ∈ ((T ⊔ borelL T L : Subgroup G) : Set G) := sup_le_sup_left hS.hall.1 T hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T (borelL T L) hS.T_le_normalizer_borel] at hx'
  obtain ⟨t, ht, b, hb, rfl⟩ := hx'
  obtain ⟨δ, hδ, s, hs, rfl⟩ := hS.exists_mul_of_mem_borel hb
  have hδN : δ ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp (hS.hall.1 hδ)).2
  have hδs : δ * s * δ⁻¹ ∈ T ⊓ L := (Subgroup.mem_normalizer_iff.mp hδN s).mp hs
  exact ⟨t * (δ * s * δ⁻¹), T.mul_mem ht (Subgroup.mem_inf.mp hδs).1, δ, hδ, by group⟩

theorem mem_of_commute [Finite G] (hS : Setting516 T L D R) {F : Type} [Field F] [CharP F 2]
    [Finite F] (hF : 2 < Nat.card F) (ψ : ↥(autOn L R) ≃* SL(2, F)) {x : G} (hx : x ∈ L ⊔ T)
    (hc : ∀ a ∈ autOn L R, a * conjAct R ⟨x, hS.reduced.2.1 hx⟩ =
      conjAct R ⟨x, hS.reduced.2.1 hx⟩ * a) :
    x ∈ T ∧ x ∈ Subgroup.centralizer (R : Set G) := by
  have hLTR : L ⊔ T ≤ Subgroup.normalizer (R : Set G) := hS.reduced.2.1
  set H : Subgroup (MulAut ↥R) := autOn L R with hH
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup G, K = ((Subgroup.centralizer (H : Set (MulAut ↥R))).comap
      ((conjAct R).comp (Subgroup.inclusion hLTR))).map (L ⊔ T).subtype := ⟨_, rfl⟩
  have hmemK : ∀ (y : G) (hy : y ∈ L ⊔ T),
      (∀ a ∈ H, a * conjAct R ⟨y, hLTR hy⟩ = conjAct R ⟨y, hLTR hy⟩ * a) → y ∈ K := by
    intro y hy h1
    rw [hKdef]
    exact ⟨⟨y, hy⟩, Subgroup.mem_centralizer_iff.mpr h1, rfl⟩
  have hKmem : ∀ y ∈ K, ∃ hy : y ∈ L ⊔ T,
      ∀ a ∈ H, a * conjAct R ⟨y, hLTR hy⟩ = conjAct R ⟨y, hLTR hy⟩ * a := by
    intro y hy
    rw [hKdef] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z.2, Subgroup.mem_centralizer_iff.mp hz⟩
  have hKLT : K ≤ L ⊔ T := fun y hy => (hKmem y hy).1
  have hKn : L ⊔ T ≤ Subgroup.normalizer (K : Set G) := fun g hg =>
    mem_normalizer_of_conj_mem fun y hy => by
      obtain ⟨hyLT, hy1⟩ := hKmem y hy
      refine hmemK _ (mul_mem (mul_mem hg hyLT) (inv_mem hg)) fun a ha => ?_
      have hgL : g ∈ Subgroup.normalizer (L : Set G) :=
        sup_le Subgroup.le_normalizer hS.le_normalizer hg
      have hgH : conjAct R ⟨g, hLTR hg⟩ ∈ Subgroup.normalizer (H : Set (MulAut ↥R)) :=
        conjAct_mem_normalizer_autOn ⟨g, hLTR hg⟩ hgL
      have ha' : (conjAct R ⟨g, hLTR hg⟩)⁻¹ * a * conjAct R ⟨g, hLTR hg⟩ ∈ H := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hgH) a).mp ha
        simpa using this
      have e : conjAct R ⟨g * y * g⁻¹, hLTR (mul_mem (mul_mem hg hyLT) (inv_mem hg))⟩ =
          conjAct R ⟨g, hLTR hg⟩ * conjAct R ⟨y, hLTR hyLT⟩ * (conjAct R ⟨g, hLTR hg⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      have h2 := hy1 _ ha'
      calc a * (conjAct R ⟨g, hLTR hg⟩ * conjAct R ⟨y, hLTR hyLT⟩ *
            (conjAct R ⟨g, hLTR hg⟩)⁻¹)
          = conjAct R ⟨g, hLTR hg⟩ * (((conjAct R ⟨g, hLTR hg⟩)⁻¹ * a *
              conjAct R ⟨g, hLTR hg⟩) * conjAct R ⟨y, hLTR hyLT⟩) *
              (conjAct R ⟨g, hLTR hg⟩)⁻¹ := by group
        _ = conjAct R ⟨g, hLTR hg⟩ * (conjAct R ⟨y, hLTR hyLT⟩ *
              ((conjAct R ⟨g, hLTR hg⟩)⁻¹ * a * conjAct R ⟨g, hLTR hg⟩)) *
              (conjAct R ⟨g, hLTR hg⟩)⁻¹ := by rw [h2]
        _ = _ := by group
  have hKL : L ⊓ K ≤ pCoreOf 2 L := by
    have hnorm : L ≤ Subgroup.normalizer ((L ⊓ K : Subgroup G) : Set G) := fun l hl =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl,
        hKn (Subgroup.mem_sup_left hl)⟩
    rcases hS.simple _ inf_le_left hnorm with hle | heq
    · exact hle
    · exfalso
      obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one_of_two_lt_card hF
      obtain ⟨g, hgL, hg⟩ := mem_autOn_iff.mp (ψ.symm (diagSL hc0)).2
      obtain ⟨hgLT, hg1⟩ := hKmem _ (heq.symm.le hgL).2
      have hu := hg1 _ (ψ.symm (unipSL 1)).2
      have hg' : conjAct R ⟨(g : G), hLTR hgLT⟩ = ((ψ.symm (diagSL hc0) : ↥H) : MulAut ↥R) :=
        hg
      rw [hg'] at hu
      have hu' : ψ.symm (unipSL 1) * ψ.symm (diagSL hc0) =
          ψ.symm (diagSL hc0) * ψ.symm (unipSL 1) := Subtype.ext hu
      rw [← map_mul, ← map_mul] at hu'
      have h3 := ψ.symm.injective hu'
      have h4 : diagSL hc0 * unipSL 1 * (diagSL hc0)⁻¹ = unipSL 1 := by
        rw [← h3, mul_inv_cancel_right]
      rw [diagSL_conj, mul_one] at h4
      have h5 := congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F) 0 1) h4
      simp only [coe_unipSL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
        Matrix.cons_val_zero] at h5
      have h6 : (c - 1) ^ 2 = 0 := by
        have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
        linear_combination h5 + (1 - c) * h2
      exact hc1 (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h6))
  have hKO := hS.le_pCoreOf_of_inf_le hKLT hKn hKL
  have hxK : x ∈ K := hmemK x hx hc
  exact ⟨hKO.trans (F7.isSylowTwoOf_pCoreOf_le hS.sylow_sup) hxK,
    hKO.trans (A4.pCoreOf_le_centralizer_of_isTwoReducedIn hS.reduced) hxK⟩

end Setting516

theorem QCoord.beta_conj {L N T : Subgroup G} {F : Type} [Field F]
    {ψ : ↥(autOn L N) ≃* SL(2, F)} {Y : ↥N →* Multiplicative (Fin 2 → F)}
    (hc : QCoord L N (T ⊓ L) F ψ Y) (β : ↥(T ⊓ L) →* Multiplicative F)
    (hβ : ∀ s : ↥(T ⊓ L), ψ (autHom hc.le_normalizer ⟨s, (Subgroup.mem_inf.mp s.2).2⟩) =
      unipSL (Multiplicative.toAdd (β s)))
    {b : G} (hb : b ∈ borelL T L) (s : ↥(T ⊓ L)) (hbs : b * s * b⁻¹ ∈ T ⊓ L) :
    Multiplicative.toAdd (β ⟨b * s * b⁻¹, hbs⟩) =
      (ψ (autHom hc.le_normalizer ⟨b, (Subgroup.mem_inf.mp hb).1⟩) :
        Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * Multiplicative.toAdd (β s) := by
  have hinj : Function.Injective (unipSL : F → SL(2, F)) := by
    intro x y hxy
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) hxy
    simpa [coe_unipSL] using this
  have hbL : b ∈ L := (Subgroup.mem_inf.mp hb).1
  have hsL : (s : G) ∈ L := (Subgroup.mem_inf.mp s.2).2
  apply hinj
  rw [← hβ ⟨b * s * b⁻¹, hbs⟩,
    ← upper_conj_unipSL (hc.upper hbL (Subgroup.mem_inf.mp hb).2) (Multiplicative.toAdd (β s)),
    ← hβ s, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

structure TwoCtx (T L D R W₁ W₂ : Subgroup G) (n : ℕ) (F₁ F₂ : Type) [Field F₁] [Field F₂]
    (ψ₁ : ↥(autOn L W₁) ≃* SL(2, F₁)) (Y₁ : ↥W₁ ≃* Multiplicative (Fin 2 → F₁))
    (ψ₂ : ↥(autOn L W₂) ≃* SL(2, F₂)) (Y₂ : ↥W₂ ≃* Multiplicative (Fin 2 → F₂))
    (φ : F₁ ≃+* F₂) (r : ↥(autOn L R) ≃* ↥(autOn L W₁)) : Prop where
  setting : Setting516 T L D R
  two_le : 2 ≤ n
  card : Nat.card F₁ = 2 ^ n
  disj : W₁ ⊓ W₂ = ⊥
  sup : W₁ ⊔ W₂ = R
  nat₁ : IsNatModCh5 L W₁ n
  nat₂ : IsNatModCh5 L W₂ n
  coord₁ : QCoord L W₁ (T ⊓ L) F₁ ψ₁ Y₁.toMonoidHom
  coord₂ : QCoord L W₂ (T ⊓ L) F₂ ψ₂ Y₂.toMonoidHom
  chi : ∀ (b : G) (hb : b ∈ borelL T L),
    (ψ₂ (autHom nat₂.1 ⟨b, (Subgroup.mem_inf.mp hb).1⟩) : Matrix (Fin 2) (Fin 2) F₂) 0 0 =
      φ ((ψ₁ (autHom nat₁.1 ⟨b, (Subgroup.mem_inf.mp hb).1⟩) : Matrix (Fin 2) (Fin 2) F₁) 0 0)
  res : ∀ (a : ↥(autOn L R)) (w : ↥W₁), ((((r a : ↥(autOn L W₁)) : MulAut ↥W₁) w : ↥W₁) : G) =
    (((a : MulAut ↥R) ⟨w, (le_sup_left.trans sup.le) w.2⟩ : ↥R) : G)

theorem Setting516.exists_twoCtx [Finite G] {T L D R : Subgroup G} {n : ℕ}
    (hS : Setting516 T L D R) (hn : 2 ≤ n)
    (hsum : IsSumOfTwo L R (fun W => IsNatModCh5 L W n)) :
    ∃ (W₁ W₂ : Subgroup G) (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂) (_ : Finite F₁)
      (_ : Finite F₂) (_ : CharP F₁ 2) (_ : CharP F₂ 2)
      (ψ₁ : ↥(autOn L W₁) ≃* SL(2, F₁)) (Y₁ : ↥W₁ ≃* Multiplicative (Fin 2 → F₁))
      (ψ₂ : ↥(autOn L W₂) ≃* SL(2, F₂)) (Y₂ : ↥W₂ ≃* Multiplicative (Fin 2 → F₂))
      (φ : F₁ ≃+* F₂) (r : ↥(autOn L R) ≃* ↥(autOn L W₁)),
      TwoCtx T L D R W₁ W₂ n F₁ F₂ ψ₁ Y₁ ψ₂ Y₂ φ r := by
  obtain ⟨W₁, W₂, -, -, hdisj, hsup, hW₁, hW₂⟩ := hsum
  have hW₁R : W₁ ≤ R := le_sup_left.trans hsup.le
  have hW₂R : W₂ ≤ R := le_sup_right.trans hsup.le
  obtain ⟨F₁, _, _, _, hF₁, ψ₁, Y₁, hc₁⟩ := hW₁.exists_qcoord hS.sylow
  obtain ⟨F₂, _, _, _, hF₂, ψ₂, Y₂, hc₂⟩ := hW₂.exists_qcoord hS.sylow
  obtain ⟨r, hr⟩ := hS.exists_resIso hW₁R hW₁
  have hSL : T ⊓ L ≤ L := inf_le_right
  obtain ⟨β₁, hs₁, hβ₁, hk₁⟩ := hc₁.exists_beta hSL
  obtain ⟨β₂, -, hβ₂, hk₂⟩ := hc₂.exists_beta hSL
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans hS.reduced.2.1
  have hker : ∀ s, β₁ s = 1 ↔ β₂ s = 1 := by
    intro s
    rw [hk₁, hk₂]
    have hsL : (s : G) ∈ L := hSL s.2
    constructor
    · intro h1
      exact Subgroup.centralizer_le hW₂R
        (hS.inf_centralizer_le_of_nat hW₁ (Subgroup.mem_inf.mpr ⟨hsL, h1⟩))
    · intro h1
      exact Subgroup.centralizer_le hW₁R
        (hS.inf_centralizer_le_of_nat hW₂ (Subgroup.mem_inf.mpr ⟨hsL, h1⟩))
  let act : ↥(borelL T L) → ↥(T ⊓ L) → ↥(T ⊓ L) := fun b s =>
    ⟨b * s * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp b.2).2 s).mp s.2⟩
  let c₁ : ↥(borelL T L) → F₁ := fun b =>
    (ψ₁ (autHom hc₁.le_normalizer ⟨b, (Subgroup.mem_inf.mp b.2).1⟩) :
      Matrix (Fin 2) (Fin 2) F₁) 0 0
  let c₂ : ↥(borelL T L) → F₂ := fun b =>
    (ψ₂ (autHom hc₂.le_normalizer ⟨b, (Subgroup.mem_inf.mp b.2).1⟩) :
      Matrix (Fin 2) (Fin 2) F₂) 0 0
  have h₁ : ∀ b s, Multiplicative.toAdd (β₁ (act b s)) = c₁ b ^ 2 * Multiplicative.toAdd (β₁ s) :=
    fun b s => hc₁.beta_conj β₁ hβ₁ b.2 s _
  have h₂ : ∀ b s, Multiplicative.toAdd (β₂ (act b s)) = c₂ b ^ 2 * Multiplicative.toAdd (β₂ s) :=
    fun b s => hc₂.beta_conj β₂ hβ₂ b.2 s _
  have hP_R := hS.sylow_resIso hW₁R hW₁ hSL hr hc₁.sylow
  have hcs : ∀ c : F₁, c ≠ 0 → ∃ b, c₁ b = c := by
    intro c hc0
    obtain ⟨g, hg, hgc⟩ := exists_mem_borel_of_sylow hLR (r.trans ψ₁) hP_R hS.centralizer_le hc0
    refine ⟨⟨g, hg⟩, ?_⟩
    rw [MulEquiv.trans_apply, Setting516.resIso_autHom hW₁R hLR hW₁.1 hr] at hgc
    exact hgc
  obtain ⟨φ, hφ⟩ := exists_ringEquiv_of_beta (hF₁.trans hF₂.symm) β₁ β₂ hs₁ hker act c₁ c₂ h₁ h₂
    hcs
  exact ⟨W₁, W₂, F₁, F₂, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ψ₁, Y₁, ψ₂, Y₂, φ, r,
    ⟨hS, hn, hF₁, hdisj, hsup, hW₁, hW₂, hc₁, hc₂, fun b hb => hφ ⟨b, hb⟩, hr⟩⟩

namespace TwoCtx

variable {T L D R W₁ W₂ : Subgroup G} {n : ℕ} {F₁ F₂ : Type} [Field F₁] [Field F₂]
  {ψ₁ : ↥(autOn L W₁) ≃* SL(2, F₁)} {Y₁ : ↥W₁ ≃* Multiplicative (Fin 2 → F₁)}
  {ψ₂ : ↥(autOn L W₂) ≃* SL(2, F₂)} {Y₂ : ↥W₂ ≃* Multiplicative (Fin 2 → F₂)}
  {φ : F₁ ≃+* F₂} {r : ↥(autOn L R) ≃* ↥(autOn L W₁)}

abbrev W (_h : TwoCtx T L D R W₁ W₂ n F₁ F₂ ψ₁ Y₁ ψ₂ Y₂ φ r) : Subgroup G :=
  R ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)

variable (h : TwoCtx T L D R W₁ W₂ n F₁ F₂ ψ₁ Y₁ ψ₂ Y₂ φ r)
include h

theorem W₁_le : W₁ ≤ R := le_sup_left.trans h.sup.le

theorem W₂_le : W₂ ≤ R := le_sup_right.trans h.sup.le

theorem L_le_R : L ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans h.setting.reduced.2.1

theorem comm {a b : G} (ha : a ∈ R) (hb : b ∈ R) : a * b = b * a :=
  congrArg Subtype.val (h.setting.reduced.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

@[expose] noncomputable def prodHom (h : TwoCtx T L D R W₁ W₂ n F₁ F₂ ψ₁ Y₁ ψ₂ Y₂ φ r) :
    ↥W₁ × ↥W₂ →* ↥R where
  toFun p := ⟨p.1 * p.2, h.sup.le (Subgroup.mul_mem_sup p.1.2 p.2.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' p q := Subtype.ext (by
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    have e := h.comm (h.W₂_le p.2.2) (h.W₁_le q.1.2)
    calc (p.1 : G) * q.1 * (p.2 * q.2) = p.1 * (q.1 * p.2) * q.2 := by group
      _ = p.1 * (p.2 * q.1) * q.2 := by rw [e]
      _ = p.1 * p.2 * (q.1 * q.2) := by group)

theorem prodHom_bijective : Function.Bijective h.prodHom := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro p hp
    have h1 : (p.1 : G) * p.2 = 1 := congrArg Subtype.val hp
    have h2 := eq_of_mul_eq h.disj p.1.2 W₁.one_mem p.2.2 W₂.one_mem (h1.trans (mul_one 1).symm)
    exact Prod.ext (Subtype.ext h2.1) (Subtype.ext h2.2)
  · intro w
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup
      (fun a ha b hb => h.comm (h.W₁_le ha) (h.W₂_le hb)) (h.sup.ge w.2)
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

@[expose] noncomputable def prodR (h : TwoCtx T L D R W₁ W₂ n F₁ F₂ ψ₁ Y₁ ψ₂ Y₂ φ r) :
    ↥W₁ × ↥W₂ ≃* ↥R :=
  MulEquiv.ofBijective h.prodHom h.prodHom_bijective

theorem coe_prodR (p : ↥W₁ × ↥W₂) : (h.prodR p : G) = p.1 * p.2 := rfl

theorem mul_prodR_symm (w : ↥R) :
    ((h.prodR.symm w).1 : G) * (h.prodR.symm w).2 = w := by
  rw [← h.coe_prodR, MulEquiv.apply_symm_apply]

theorem prodR_symm_conj {g : G} (hgR : g ∈ Subgroup.normalizer (R : Set G))
    (hg₁ : g ∈ Subgroup.normalizer (W₁ : Set G)) (hg₂ : g ∈ Subgroup.normalizer (W₂ : Set G))
    (w : ↥R) :
    h.prodR.symm (conjAct R ⟨g, hgR⟩ w) =
      (conjAct W₁ ⟨g, hg₁⟩ (h.prodR.symm w).1, conjAct W₂ ⟨g, hg₂⟩ (h.prodR.symm w).2) := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [h.coe_prodR, conjAct_apply_coe, conjAct_apply_coe, conjAct_apply_coe,
    ← h.mul_prodR_symm w]
  group

theorem prodR_symm_mem {w : ↥R} (hw : (w : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) :
    Set G)) :
    ((h.prodR.symm w).1 : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) ∧
      ((h.prodR.symm w).2 : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := by
  constructor <;> rw [Subgroup.mem_centralizer_iff] <;> intro s hs <;>
  · have hsL : s ∈ L := (Subgroup.mem_inf.mp hs).2
    have h1 := conj_eq_of_conj_mul_eq h.disj (h.nat₁.1 hsL) (h.nat₂.1 hsL)
      (h.prodR.symm w).1.2 (h.prodR.symm w).2.2 (by
        rw [h.mul_prodR_symm w, Subgroup.mem_centralizer_iff.mp hw s hs,
          mul_inv_cancel_right])
    first
    | calc s * ((h.prodR.symm w).1 : G) = s * (h.prodR.symm w).1 * s⁻¹ * s := by group
        _ = (h.prodR.symm w).1 * s := by rw [h1.1]
    | calc s * ((h.prodR.symm w).2 : G) = s * (h.prodR.symm w).2 * s⁻¹ * s := by group
        _ = (h.prodR.symm w).2 * s := by rw [h1.2]

theorem bot₁ : W₁ ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  have h1 : Y₁ ⟨x, hx1⟩ = 1 := (h.coord₁.ker ⟨x, hx1⟩).mpr hx2
  have h2 : (⟨x, hx1⟩ : ↥W₁) = 1 := Y₁.injective (h1.trans (map_one Y₁).symm)
  exact congrArg Subtype.val h2

theorem bot₂ : W₂ ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  have h1 : Y₂ ⟨x, hx1⟩ = 1 := (h.coord₂.ker ⟨x, hx1⟩).mpr hx2
  have h2 : (⟨x, hx1⟩ : ↥W₂) = 1 := Y₂.injective (h1.trans (map_one Y₂).symm)
  exact congrArg Subtype.val h2

@[expose] noncomputable def coordHom (h : TwoCtx T L D R W₁ W₂ n F₁ F₂ ψ₁ Y₁ ψ₂ Y₂ φ r) :
    ↥h.W →* Multiplicative (Fin 2 → F₁) where
  toFun w := Multiplicative.ofAdd
    ![(Multiplicative.toAdd (Y₁ (h.prodR.symm (Subgroup.inclusion inf_le_left w)).1)) 0,
      φ.symm ((Multiplicative.toAdd (Y₂ (h.prodR.symm (Subgroup.inclusion inf_le_left w)).2)) 0)]
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp

theorem toAdd_coordHom (w : ↥h.W) : Multiplicative.toAdd (h.coordHom w) =
    ![(Multiplicative.toAdd (Y₁ (h.prodR.symm (Subgroup.inclusion inf_le_left w)).1)) 0,
      φ.symm ((Multiplicative.toAdd (Y₂ (h.prodR.symm (Subgroup.inclusion inf_le_left w)).2)) 0)] :=
  rfl

theorem coordHom_bijective : Function.Bijective h.coordHom := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro w hw
    have hw' := congrArg Multiplicative.toAdd hw
    rw [toAdd_coordHom, toAdd_one] at hw'
    have h0 := congrFun hw' 0
    have h1 := congrFun hw' 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
    set p := h.prodR.symm (Subgroup.inclusion inf_le_left w) with hp
    obtain ⟨hp₁, hp₂⟩ := h.prodR_symm_mem (w := Subgroup.inclusion inf_le_left w) w.2.2
    have l₁ := (h.coord₁.mem_centralizer_iff_of_nat inf_le_right h.bot₁ p.1).mp hp₁
    have l₂ := (h.coord₂.mem_centralizer_iff_of_nat inf_le_right h.bot₂ p.2).mp hp₂
    have hY₁ : Y₁ p.1 = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      fin_cases i
      · exact h0
      · exact l₁
    have hY₂ : Y₂ p.2 = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      fin_cases i
      · have := congrArg φ h1
        rwa [RingEquiv.apply_symm_apply, map_zero] at this
      · exact l₂
    have hp1 : p = 1 := Prod.ext (Y₁.injective (hY₁.trans (map_one Y₁).symm))
      (Y₂.injective (hY₂.trans (map_one Y₂).symm))
    have h2 : Subgroup.inclusion inf_le_left w = 1 := by
      have := congrArg h.prodR hp1
      rwa [hp, MulEquiv.apply_symm_apply, map_one] at this
    exact Subtype.ext (congrArg (Subtype.val : ↥R → G) h2)
  · intro v
    set q₁ := Y₁.symm (Multiplicative.ofAdd ![(Multiplicative.toAdd v) 0, 0]) with hq₁
    set q₂ := Y₂.symm (Multiplicative.ofAdd ![φ ((Multiplicative.toAdd v) 1), 0]) with hq₂
    have hq₁S : (q₁ : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := by
      rw [h.coord₁.mem_centralizer_iff_of_nat inf_le_right h.bot₁]
      show (Multiplicative.toAdd (Y₁ q₁)) 1 = 0
      rw [hq₁, MulEquiv.apply_symm_apply]
      simp
    have hq₂S : (q₂ : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := by
      rw [h.coord₂.mem_centralizer_iff_of_nat inf_le_right h.bot₂]
      show (Multiplicative.toAdd (Y₂ q₂)) 1 = 0
      rw [hq₂, MulEquiv.apply_symm_apply]
      simp
    have hmemS : ((h.prodR (q₁, q₂) : ↥R) : G) ∈
        Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := by
      rw [h.coe_prodR]
      exact mul_mem hq₁S hq₂S
    refine ⟨⟨h.prodR (q₁, q₂), (h.prodR (q₁, q₂)).2, hmemS⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_coordHom]
    have e : Subgroup.inclusion (inf_le_left : h.W ≤ R)
        ⟨((h.prodR (q₁, q₂) : ↥R) : G), (h.prodR (q₁, q₂)).2, hmemS⟩ = h.prodR (q₁, q₂) := rfl
    rw [e, MulEquiv.symm_apply_apply, hq₁, hq₂, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
    funext i
    fin_cases i <;> simp

@[expose] noncomputable def coord (h : TwoCtx T L D R W₁ W₂ n F₁ F₂ ψ₁ Y₁ ψ₂ Y₂ φ r) :
    ↥h.W ≃* Multiplicative (Fin 2 → F₁) :=
  MulEquiv.ofBijective h.coordHom h.coordHom_bijective

theorem toAdd_coord (w : ↥h.W) : Multiplicative.toAdd (h.coord w) =
    ![(Multiplicative.toAdd (Y₁ (h.prodR.symm (Subgroup.inclusion inf_le_left w)).1)) 0,
      φ.symm ((Multiplicative.toAdd (Y₂ (h.prodR.symm (Subgroup.inclusion inf_le_left w)).2)) 0)] :=
  rfl

theorem borel_le_normalizer_W :
    borelL T L ≤ Subgroup.normalizer (h.W : Set G) := fun _ hb =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨h.L_le_R (Subgroup.mem_inf.mp hb).1,
    F7.normalizer_le_normalizer_centralizer _ (Subgroup.mem_inf.mp hb).2⟩

theorem T_le_normalizer_W : T ≤ Subgroup.normalizer (h.W : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨h.setting.reduced.2.1 (Subgroup.mem_sup_right ht),
    F7.normalizer_le_normalizer_centralizer _ (h.setting.T_le_normalizer_inf ht)⟩

theorem act_eq_smul {b : G} (hb : b ∈ borelL T L) (x : Fin 2 → F₁) :
    Semi516.act h.coord b (h.borel_le_normalizer_W hb) x =
      (ψ₁ (autHom h.nat₁.1 ⟨b, (Subgroup.mem_inf.mp hb).1⟩) :
        Matrix (Fin 2) (Fin 2) F₁) 0 0 • x := by
  have hbL : b ∈ L := (Subgroup.mem_inf.mp hb).1
  have hbS : b ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hb).2
  rw [Semi516.act, Semi516.coordPerm_apply]
  obtain ⟨w, hw⟩ : ∃ w, w = h.coord.symm (Multiplicative.ofAdd x) := ⟨_, rfl⟩
  rw [← hw]
  have hx : Multiplicative.toAdd (h.coord w) = x := by
    rw [hw, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  obtain ⟨p, hp⟩ : ∃ p, p = h.prodR.symm (Subgroup.inclusion inf_le_left w) := ⟨_, rfl⟩
  obtain ⟨hp₁, hp₂⟩ := h.prodR_symm_mem (w := Subgroup.inclusion inf_le_left w) w.2.2
  rw [← hp] at hp₁ hp₂
  have l₁ := (h.coord₁.mem_centralizer_iff_of_nat inf_le_right h.bot₁ p.1).mp hp₁
  have l₂ := (h.coord₂.mem_centralizer_iff_of_nat inf_le_right h.bot₂ p.2).mp hp₂
  have hconj : Subgroup.inclusion (inf_le_left : h.W ≤ R)
      (conjAct h.W ⟨b, h.borel_le_normalizer_W hb⟩ w) =
        conjAct R ⟨b, h.L_le_R hbL⟩ (Subgroup.inclusion inf_le_left w) := by
    apply Subtype.ext
    rw [conjAct_apply_coe]
    exact conjAct_apply_coe _ _
  have hdec := h.prodR_symm_conj (h.L_le_R hbL) (h.nat₁.1 hbL) (h.nat₂.1 hbL)
    (Subgroup.inclusion inf_le_left w)
  rw [← hp] at hdec
  have e₁ : Multiplicative.toAdd (Y₁ (conjAct W₁ ⟨b, h.nat₁.1 hbL⟩ p.1)) =
      (ψ₁ (autHom h.nat₁.1 ⟨b, hbL⟩) : Matrix (Fin 2) (Fin 2) F₁) 0 0 •
        Multiplicative.toAdd (Y₁ p.1) := h.coord₁.toAdd_Y_line hbL hbS p.1 l₁
  have e₂ : Multiplicative.toAdd (Y₂ (conjAct W₂ ⟨b, h.nat₂.1 hbL⟩ p.2)) =
      (ψ₂ (autHom h.nat₂.1 ⟨b, hbL⟩) : Matrix (Fin 2) (Fin 2) F₂) 0 0 •
        Multiplicative.toAdd (Y₂ p.2) := h.coord₂.toAdd_Y_line hbL hbS p.2 l₂
  have hχ := h.chi b hb
  rw [toAdd_coord, hconj, hdec, ← hx, toAdd_coord, ← hp]
  funext i
  fin_cases i
  · simp only [Matrix.cons_val_zero, Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
    rw [e₁, Pi.smul_apply, smul_eq_mul]
  · simp only [Matrix.cons_val_one, Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
    rw [e₂, Pi.smul_apply, smul_eq_mul, hχ, map_mul, RingEquiv.symm_apply_apply]
    simp

theorem sylowR [Finite G] (a : ↥(autOn L R)) :
    (a : MulAut ↥R) ∈ autOn (T ⊓ L) R ↔ ∃ b : F₁, (r.trans ψ₁) a = unipSL b :=
  h.setting.sylow_resIso h.W₁_le h.nat₁ inf_le_right h.res h.coord₁.sylow a

theorem psiR_autHom {l : G} (hl : l ∈ L) :
    (r.trans ψ₁) (autHom h.L_le_R ⟨l, hl⟩) = ψ₁ (autHom h.nat₁.1 ⟨l, hl⟩) := by
  rw [MulEquiv.trans_apply, Setting516.resIso_autHom h.W₁_le h.L_le_R h.nat₁.1 h.res]

theorem chi_conj_of_linear {t : G} (ht : t ∈ T)
    (hlin : IsSemilinearWith (Semi516.act h.coord t (h.T_le_normalizer_W ht)) (1 : F₁ ≃+* F₁))
    {b : G} (hb : b ∈ borelL T L) (htb : t * b * t⁻¹ ∈ borelL T L) :
    (ψ₁ (autHom h.nat₁.1 ⟨t * b * t⁻¹, (Subgroup.mem_inf.mp htb).1⟩) :
        Matrix (Fin 2) (Fin 2) F₁) 0 0 =
      (ψ₁ (autHom h.nat₁.1 ⟨b, (Subgroup.mem_inf.mp hb).1⟩) : Matrix (Fin 2) (Fin 2) F₁) 0 0 := by
  have hT := h.T_le_normalizer_W ht
  have hB := h.borel_le_normalizer_W hb
  have hact := h.act_eq_smul htb ![1, 0]
  have hmul : Semi516.act h.coord (t * b * t⁻¹) (h.borel_le_normalizer_W htb) =
      Semi516.act h.coord t hT * Semi516.act h.coord b hB * (Semi516.act h.coord t hT)⁻¹ := by
    rw [← Semi516.act_inv h.coord hT, ← Semi516.act_mul h.coord hT hB,
      ← Semi516.act_mul h.coord (Subgroup.mul_mem _ hT hB) (Subgroup.inv_mem _ hT)]
  rw [hmul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h.act_eq_smul hb] at hact
  have h1 := hlin ((ψ₁ (autHom h.nat₁.1 ⟨b, (Subgroup.mem_inf.mp hb).1⟩) :
    Matrix (Fin 2) (Fin 2) F₁) 0 0) ((Semi516.act h.coord t hT)⁻¹ ![1, 0])
  rw [h1, Semi516.perm_apply_inv] at hact
  have h2 := congrFun hact 0
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at h2
  exact h2.symm

theorem hyp [Finite G] [Finite F₁] [CharP F₁ 2] : Semi516.Hyp h.coord T (borelL T L) D := by
  have hS := h.setting
  have hLR := h.L_le_R
  have hLTR : L ⊔ T ≤ Subgroup.normalizer (R : Set G) := hS.reduced.2.1
  have hP_R := h.sylowR
  have hn1 : 1 ≤ n := by have := h.two_le; omega
  have hF2 : 2 < Nat.card F₁ := by
    rw [h.card]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hsurjD : ∀ c : F₁, c ≠ 0 → ∃ (δ : G) (hδ : δ ∈ D),
      (ψ₁ (autHom h.nat₁.1 ⟨δ, (Subgroup.mem_inf.mp (hS.hall.1 hδ)).1⟩) :
        Matrix (Fin 2) (Fin 2) F₁) 0 0 = c := by
    intro c hc
    obtain ⟨δ, hδ, hδc⟩ := exists_mem_D_of_sylow hLR (r.trans ψ₁) hP_R hS.centralizer_le
      hS.sylow hS.hall hc
    refine ⟨δ, hδ, ?_⟩
    rw [h.psiR_autHom] at hδc
    exact hδc
  refine
    { one_le := by norm_num
      isPGroup := hS.isPGroup
      odd := hS.hall.2.1
      le_T := inf_le_left.trans hS.le_T
      T_le := h.T_le_normalizer_W
      B_le := h.borel_le_normalizer_W
      T_le_B := hS.T_le_normalizer_borel
      D_le := hS.hall.1
      decomp := fun _ hx => hS.decomp hx
      scalar := fun _ hb => ⟨_, h.act_eq_smul hb⟩
      surj := fun c hc => by
        obtain ⟨δ, hδ, hδc⟩ := hsurjD c hc
        exact ⟨δ, hδ, fun x => by rw [h.act_eq_smul (hS.hall.1 hδ), hδc]⟩
      linear := ?_
      faithful := ?_ }
  ·
    intro t ht hlin
    have htL : t ∈ Subgroup.normalizer (L : Set G) := hS.le_normalizer ht
    have htLT : t ∈ L ⊔ T := Subgroup.mem_sup_right ht
    have htR : t ∈ Subgroup.normalizer (R : Set G) := hLTR htLT
    have htS : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      hS.T_le_normalizer_inf ht
    set τ : Subgroup.normalizer ((autOn L R : Subgroup (MulAut ↥R)) : Set (MulAut ↥R)) :=
      ⟨conjAct R ⟨t, htR⟩, conjAct_mem_normalizer_autOn ⟨t, htR⟩ htL⟩ with hτ
    have hτP : (τ : MulAut ↥R) ∈
        Subgroup.normalizer ((autOn (T ⊓ L) R : Subgroup (MulAut ↥R)) : Set (MulAut ↥R)) :=
      conjAct_mem_normalizer_autOn ⟨t, htR⟩ htS
    obtain ⟨h₀, σ, hh₀, hασ, -⟩ :=
      exists_upper_of_normalizes hn1 h.card (r.trans ψ₁) hP_R τ hτP
    have hσ1 : σ = 1 := by
      refine RingEquiv.ext fun c => ?_
      by_cases hc : c = 0
      · rw [hc, map_zero, map_zero]
      obtain ⟨δ, hδ, hδc⟩ := hsurjD c hc
      have hδB := hS.hall.1 hδ
      have hδL : δ ∈ L := (Subgroup.mem_inf.mp hδB).1
      have htδ : t * δ * t⁻¹ ∈ borelL T L :=
        (Subgroup.mem_normalizer_iff.mp (hS.T_le_normalizer_borel ht) δ).mp hδB
      have htδL : t * δ * t⁻¹ ∈ L := (Subgroup.mem_inf.mp htδ).1
      have e1 : (autOn L R).normalizerMonoidHom τ (autHom hLR ⟨δ, hδL⟩) =
          autHom hLR ⟨t * δ * t⁻¹, htδL⟩ := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        show conjAct R ⟨t, htR⟩ * conjAct R ⟨δ, hLR hδL⟩ * (conjAct R ⟨t, htR⟩)⁻¹ =
          conjAct R ⟨t * δ * t⁻¹, hLR htδL⟩
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      have e2 := hασ (autHom hLR ⟨δ, hδL⟩)
      rw [e1] at e2
      have hupδ : ((r.trans ψ₁) (autHom hLR ⟨δ, hδL⟩) : Matrix (Fin 2) (Fin 2) F₁) 1 0 = 0 :=
        upper_of_mem_normalizer _ hP_R _
          (conjAct_mem_normalizer_autOn ⟨δ, hLR hδL⟩ (Subgroup.mem_inf.mp hδB).2)
      have e3 := (upper_conj_map σ hh₀ hupδ).2
      rw [← e2, h.psiR_autHom, h.psiR_autHom, hδc] at e3
      rw [← e3, h.chi_conj_of_linear ht hlin hδB htδ, hδc]
      rfl
    set e₀ := (r.trans ψ₁).symm h₀ with he₀
    have hconj : ∀ y : ↥(autOn L R), (autOn L R).normalizerMonoidHom τ y = e₀ * y * e₀⁻¹ := by
      intro y
      apply (r.trans ψ₁).injective
      rw [hασ, hσ1, map_mul, map_mul, map_inv, he₀, MulEquiv.apply_symm_apply]
      rfl
    obtain ⟨l, hlL, hle₀⟩ := mem_autOn_iff.mp e₀.2
    have hxLT : (l : G)⁻¹ * t ∈ L ⊔ T :=
      mul_mem (inv_mem (Subgroup.mem_sup_left hlL)) htLT
    have hxc : ∀ a ∈ autOn L R, a * conjAct R ⟨(l : G)⁻¹ * t, hLTR hxLT⟩ =
        conjAct R ⟨(l : G)⁻¹ * t, hLTR hxLT⟩ * a := by
      intro a ha
      have e1 : conjAct R ⟨(l : G)⁻¹ * t, hLTR hxLT⟩ =
          ((e₀ : ↥(autOn L R)) : MulAut ↥R)⁻¹ * (τ : MulAut ↥R) := by
        rw [← hle₀, hτ, ← map_inv, ← map_mul]
        rfl
      have e2 : (τ : MulAut ↥R) * a * (τ : MulAut ↥R)⁻¹ =
          ((e₀ : ↥(autOn L R)) : MulAut ↥R) * a * ((e₀ : ↥(autOn L R)) : MulAut ↥R)⁻¹ := by
        have := congrArg Subtype.val (hconj ⟨a, ha⟩)
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at this
        rw [this]
        rfl
      rw [e1]
      calc a * (((e₀ : ↥(autOn L R)) : MulAut ↥R)⁻¹ * (τ : MulAut ↥R))
          = ((e₀ : ↥(autOn L R)) : MulAut ↥R)⁻¹ * (((e₀ : ↥(autOn L R)) : MulAut ↥R) * a *
              ((e₀ : ↥(autOn L R)) : MulAut ↥R)⁻¹) * (τ : MulAut ↥R) := by group
        _ = ((e₀ : ↥(autOn L R)) : MulAut ↥R)⁻¹ * ((τ : MulAut ↥R) * a *
              (τ : MulAut ↥R)⁻¹) * (τ : MulAut ↥R) := by rw [e2]
        _ = ((e₀ : ↥(autOn L R)) : MulAut ↥R)⁻¹ * (τ : MulAut ↥R) * a := by group
    obtain ⟨hxT, hxC⟩ := hS.mem_of_commute hF2 (r.trans ψ₁) hxLT hxc
    have hlT : (l : G) ∈ T := by
      have e : (l : G) = t * ((l : G)⁻¹ * t)⁻¹ := by group
      rw [e]
      exact mul_mem ht (inv_mem hxT)
    have hlS : (l : G) ∈ T ⊓ L := Subgroup.mem_inf.mpr ⟨hlT, hlL⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨hwR, hwS⟩ := Subgroup.mem_inf.mp hw
    have h1 := Subgroup.mem_centralizer_iff.mp hwS l hlS
    have h2 := Subgroup.mem_centralizer_iff.mp hxC w hwR
    have ht' : t = (l : G) * ((l : G)⁻¹ * t) := by group
    rw [ht']
    calc w * ((l : G) * ((l : G)⁻¹ * t)) = (w * l) * ((l : G)⁻¹ * t) := by group
      _ = (l * w) * ((l : G)⁻¹ * t) := by rw [← h1]
      _ = l * (w * ((l : G)⁻¹ * t)) := by group
      _ = l * (((l : G)⁻¹ * t) * w) := by rw [h2]
      _ = (l : G) * ((l : G)⁻¹ * t) * w := by group
  ·
    rw [eq_bot_iff]
    intro δ hδ
    obtain ⟨hδD, hδC⟩ := Subgroup.mem_inf.mp hδ
    rw [Subgroup.mem_bot]
    have hδB := hS.hall.1 hδD
    have hδL : δ ∈ L := (Subgroup.mem_inf.mp hδB).1
    have hδS := (Subgroup.mem_inf.mp hδB).2
    have h1 : Semi516.act h.coord δ (h.borel_le_normalizer_W hδB) = 1 :=
      (Semi516.act_eq_one_iff _ _).mpr hδC
    have h2 := h.act_eq_smul hδB ![1, 0]
    rw [h1, Equiv.Perm.one_apply] at h2
    have h00 : (ψ₁ (autHom h.nat₁.1 ⟨δ, hδL⟩) : Matrix (Fin 2) (Fin 2) F₁) 0 0 = 1 := by
      have := congrFun h2 0
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at this
      exact this.symm
    have hupR : ((r.trans ψ₁) (autHom hLR ⟨δ, hδL⟩) : Matrix (Fin 2) (Fin 2) F₁) 1 0 = 0 :=
      upper_of_mem_normalizer (r.trans ψ₁) hP_R _
        (conjAct_mem_normalizer_autOn ⟨δ, hLR hδL⟩ hδS)
    have h00R : ((r.trans ψ₁) (autHom hLR ⟨δ, hδL⟩) : Matrix (Fin 2) (Fin 2) F₁) 0 0 = 1 := by
      rw [h.psiR_autHom]
      exact h00
    have hu := eq_unipSL_of_upper hupR h00R
    have hmem : ((autHom hLR ⟨δ, hδL⟩ : ↥(autOn L R)) : MulAut ↥R) ∈ autOn (T ⊓ L) R :=
      (hP_R _).mpr ⟨_, hu⟩
    have hδT : δ ∈ T := mem_of_conjAct_mem_autOn hS.centralizer_le ⟨δ, hLR hδL⟩
      (Subgroup.mem_sup_left hδL) hmem
    exact eq_one_of_mem_of_odd hS.hall.2.1 hS.isPGroup hδD hδT

theorem le_two [Finite G] [Finite F₁] [CharP F₁ 2] (hW : IsElemAbelian 2 h.W)
    (hq : qhatInt (T ⊔ D) h.W hW ≤ 2) : n ≤ 2 := by
  by_contra hn
  push Not at hn
  have hcard : Nat.card h.W = (2 ^ n) ^ 2 := by
    rw [Nat.card_congr h.coord.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
    simp [h.card]
  have h16 : 16 < Nat.card h.W := by
    rw [hcard]
    calc 16 < (2 ^ 3) ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hn) 2
  exact absurd hq (not_le.mpr (h.hyp.two_lt_qhatInt hW h16))

end TwoCtx

theorem fact516Two : Fact516Two := by
  intro G _ _ T L D R n hS hn hsum
  obtain ⟨W₁, W₂, F₁, F₂, _, _, _, _, _, _, ψ₁, Y₁, ψ₂, Y₂, φ, r, h⟩ :=
    hS.exists_twoCtx hn hsum
  exact ⟨h.W, inf_le_left, h.hyp.isTDMod, fun hW hq => h.le_two hW hq⟩

end CFSG.Quasithin.H13

module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec57
import CFSG.RankThree.GF2n.Stroth80.Sec10CQt
import CFSG.RankThree.GF2n.Stroth80.Sec10SevenRoots

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem Ctx.comm_of_mem_QB_of_mem_C {C : Subgroup G} (hC : Ctx M Q Z C) {x c : G}
    (hx : x ∈ QB C) (hc : c ∈ C) : x * c = c * x := by
  obtain ⟨g, hg⟩ := hC.conj
  have hQB : QB C = conjSubgroup g Q := (Ctx.QB_eq hC hg).2
  have hx' : g⁻¹ * x * g ∈ Q := by
    rw [hQB] at hx
    exact mem_conjSubgroup.mp hx
  have hc' : g⁻¹ * c * g ∈ Z := by
    rw [hg] at hc
    exact mem_conjSubgroup.mp hc
  have hcomm := hC.hyp.toHyp79.V_central hc' hx'
  calc x * c = g * ((g⁻¹ * x * g) * (g⁻¹ * c * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * c * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcomm]
    _ = c * x := by group

private theorem card_inf_QB_eq_mul (hc : Ctx M Q Z B) {t : G}
    (ht : Good101 M Q Z B t) {C : Subgroup G} (hC : Ctx M Q Z C)
    {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {τ : M₀.E ≃ₗ[K] M₀.E}
    (hτπ : ∀ y ∈ Q, M₀.π (t * y * t⁻¹) = τ (M₀.π y))
    {W : Submodule K M₀.E} (hWmem : ∀ e, e ∈ M₀.img (Q ⊓ QB C) ↔ e ∈ W) :
    Nat.card ↥(Q ⊓ QB C) = Nat.card Z * Nat.card ↥W ∧
      Nat.card ↥(Q ⊓ QB C ⊓ Q1 hc t) = Nat.card Z *
        Nat.card ↥(W ⊓ LinearMap.ker ((τ : M₀.E →ₗ[K] M₀.E) - 1)) := by
  have htM : t ∈ M := hc.LB_le_M ht.mem_LB
  obtain ⟨htQ, -⟩ := hc.conj_mem_Q_of_mem_M htM
  have hZQ1 : Z ≤ Q1 hc t := by
    intro z hz
    refine (hc.mem_Q1_iff htM).mpr ⟨hc.Z_le_Q hz, ?_⟩
    have hzt := hc.LB_centralizes_Z ht.mem_LB z hz
    rw [show ⁅t, z⁆ = t * z * t⁻¹ * z⁻¹ by rw [commutatorElement_def], hzt]
    simp
  have hZA : Z ≤ Q ⊓ QB C := le_inf hC.Z_le_Q hC.Z_le_QB.1
  have hcardA : Nat.card ↥(Q ⊓ QB C) = Nat.card Z * Nat.card ↥W := by
    rw [M₀.card_eq (inf_le_left : Q ⊓ QB C ≤ Q) hZA]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun e => hWmem e)
  have hWker : ∀ e, e ∈ M₀.img (Q ⊓ QB C ⊓ Q1 hc t) ↔
      e ∈ W ⊓ LinearMap.ker ((τ : M₀.E →ₗ[K] M₀.E) - 1) := by
    intro e
    constructor
    · rintro ⟨a, ha, haQ, rfl⟩
      obtain ⟨haA, haQ1⟩ := Subgroup.mem_inf.mp ha
      refine Submodule.mem_inf.mpr ⟨(hWmem _).mp (M₀.pi_mem_img haA haQ), ?_⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact (comm_mem_iff_fix htQ hτπ haQ).mp ((hc.mem_Q1_iff htM).mp haQ1).2
    · rintro ⟨heW, heF⟩
      obtain ⟨a, haA, haQ, rfl⟩ := (hWmem e).mpr heW
      have hker : (τ : M₀.E →ₗ[K] M₀.E) (M₀.π a) = M₀.π a := by
        have h := LinearMap.mem_ker.mp heF
        rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
        exact h
      have haQ1 : a ∈ Q1 hc t :=
        (hc.mem_Q1_iff htM).mpr ⟨haQ, (comm_mem_iff_fix htQ hτπ haQ).mpr hker⟩
      exact M₀.pi_mem_img ⟨haA, haQ1⟩ haQ
  have hcardA1 : Nat.card ↥(Q ⊓ QB C ⊓ Q1 hc t) = Nat.card Z *
      Nat.card ↥(W ⊓ LinearMap.ker ((τ : M₀.E →ₗ[K] M₀.E) - 1)) := by
    rw [M₀.card_eq (le_trans inf_le_left inf_le_left) (le_inf hZA hZQ1)]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun e => hWker e)
  exact ⟨hcardA, hcardA1⟩

private theorem card_img_le_mul_card_inf_ker (hc : Ctx M Q Z B) {t : G}
    (ht : Good101 M Q Z B t) {C : Subgroup G} (hC : Ctx M Q Z C) (htC : t ∈ QB C)
    {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {τ : M₀.E ≃ₗ[K] M₀.E}
    (hτπ : ∀ y ∈ Q, M₀.π (t * y * t⁻¹) = τ (M₀.π y))
    {W : Submodule K M₀.E} (hWmem : ∀ e, e ∈ M₀.img (Q ⊓ QB C) ↔ e ∈ W) :
    Nat.card ↥W ≤ Nat.card Z *
      Nat.card ↥(W ⊓ LinearMap.ker ((τ : M₀.E →ₗ[K] M₀.E) - 1)) := by
  obtain ⟨hcardA, hcardA1⟩ := card_inf_QB_eq_mul hc ht hC hτπ hWmem
  have htM : t ∈ M := hc.LB_le_M ht.mem_LB
  have hle : Q ⊓ QB C ⊓ Subgroup.centralizer ({t} : Set G) ≤ Q ⊓ QB C ⊓ Q1 hc t := by
    refine le_inf inf_le_left fun y hy => ?_
    obtain ⟨hyA, hyt⟩ := Subgroup.mem_inf.mp hy
    refine (hc.mem_Q1_iff htM).mpr ⟨hyA.1, ?_⟩
    have hcomm : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyt
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm]
    exact Z.one_mem
  have hcard_le : Nat.card ↥(Q ⊓ QB C) ≤
      Nat.card Z * Nat.card ↥(Q ⊓ QB C ⊓ Q1 hc t) := by
    refine (hC.card_inf_QB_le_mul_card_centralizer htC).trans ?_
    exact Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective
      (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle))
  refine Nat.le_of_mul_le_mul_left (c := Nat.card ↥Z) ?_ (Nat.card_pos (α := ↥Z))
  calc Nat.card Z * Nat.card ↥W = Nat.card ↥(Q ⊓ QB C) := hcardA.symm
    _ ≤ Nat.card Z * Nat.card ↥(Q ⊓ QB C ⊓ Q1 hc t) := hcard_le
    _ = Nat.card Z * (Nat.card Z * Nat.card ↥(W ⊓
          LinearMap.ker ((τ : M₀.E →ₗ[K] M₀.E) - 1))) := by rw [hcardA1]

private theorem eq_sup_span_of_card_le {K E : Type} [Field K] [Finite K] [AddCommGroup E]
    [Module K E] [Module.Finite K E] {W V : Submodule K E} {v : E}
    (hVW : V ≤ W) (hvW : v ∈ W) (hv : v ∉ V)
    (hcard : Nat.card ↥W ≤ Nat.card K * Nat.card ↥V) :
    W = V ⊔ Submodule.span K {v} := by
  have hHcard : Nat.card ↥(V ⊔ Submodule.span K {v}) = Nat.card K * Nat.card ↥V := by
    have hfr := Submodule.finrank_sup_span_singleton (K := K) (p := V) (v := v) hv
    calc Nat.card ↥(V ⊔ Submodule.span K {v})
        = Nat.card K ^ Module.finrank K ↥(V ⊔ Submodule.span K {v}) :=
          Module.natCard_eq_pow_finrank
      _ = Nat.card K ^ (Module.finrank K ↥V + 1) := by rw [hfr]
      _ = Nat.card K ^ Module.finrank K ↥V * Nat.card K := by rw [pow_succ]
      _ = Nat.card K * Nat.card K ^ Module.finrank K ↥V := by rw [mul_comm]
      _ = Nat.card K * Nat.card ↥V := by
          rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥V)]
  have hHle : V ⊔ Submodule.span K {v} ≤ W :=
    sup_le hVW (by rw [Submodule.span_le]; simpa using hvW)
  have hcardW : Nat.card ↥W ≤ Nat.card ↥(V ⊔ Submodule.span K {v}) := by
    rw [hHcard]
    exact hcard
  haveI : Finite E := Module.finite_of_finite K
  exact SetLike.coe_injective (Set.Finite.eq_of_subset_of_card_le
    (Set.toFinite (W : Set E)) hHle hcardW).symm

private theorem exists_isometry_fixing_ker (hc : Ctx M Q Z B) {t x : G}
    (ht : Good101 M Q Z B t) {C : Subgroup G} (hC : Ctx M Q Z C)
    {P : Subgroup G} (hP : P ≤ QB C ⊓ M)
    (hPQ1 : ∀ y ∈ P, ∀ e ∈ Q1 hc t, ⁅y, e⁆ ∈ Z) (hxP : x ∈ P)
    {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hM : GlobalModelData M Q Z γ M₀) {τ : M₀.E ≃ₗ[K] M₀.E}
    (hτπ : ∀ y ∈ Q, M₀.π (t * y * t⁻¹) = τ (M₀.π y)) :
    ∃ T : M₀.E ≃ₗ[K] M₀.E, (∀ y ∈ Q, M₀.π (x * y * x⁻¹) = T (M₀.π y)) ∧
      (∀ e f, M₀.B (T e) (T f) = M₀.B e f) ∧ ∀ f, τ f = f → T f = f := by
  have hxM : x ∈ M := (hP hxP).2
  obtain ⟨hxQ, -⟩ := hc.conj_mem_Q_of_mem_M hxM
  have hxcent : ∀ z ∈ Z, x * z * x⁻¹ = z := by
    have h : x ∈ QB C ⊓ Subgroup.centralizer (Z : Set G) := by
      have h := hP hxP
      rwa [hC.QB_inf_M_eq] at h
    intro z hz
    have hxz : z * x = x * z :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h).2 z hz
    rw [← hxz]
    group
  obtain ⟨T, hTπ, -, hTB⟩ := hM.linear_of_centralizes hxM hxcent
  refine ⟨T, hTπ, hTB, fun f hf => ?_⟩
  have htM : t ∈ M := hc.LB_le_M ht.mem_LB
  obtain ⟨htQ, -⟩ := hc.conj_mem_Q_of_mem_M htM
  obtain ⟨q, hqQ, rfl⟩ := M₀.π_surj f
  have hqQ1 : q ∈ Q1 hc t :=
    (hc.mem_Q1_iff htM).mpr ⟨hqQ, (comm_mem_iff_fix htQ hτπ hqQ).mpr hf⟩
  exact (comm_mem_iff_fix hxQ hTπ hqQ).mp (hPQ1 x hxP q hqQ1)

private theorem comm_inf_QB_mem_Z_of_ker (hc : Ctx M Q Z B) {n : ℕ} (H : Sec10Hyp hc n)
    (hspread : StrothNoA2SpreadStatement) {t : G} (ht : Good101 M Q Z B t)
    {C : Subgroup G} (hC : Ctx M Q Z C) (htC : t ∈ QB C)
    {P : Subgroup G} (hP : P ≤ QB C ⊓ M)
    (hPQ1 : ∀ x ∈ P, ∀ e ∈ Q1 hc t, ⁅x, e⁆ ∈ Z)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hM : GlobalModelData M Q Z γ M₀)
    {τ : M₀.E ≃ₗ[K] M₀.E}
    (hτπ : ∀ y ∈ Q, M₀.π (t * y * t⁻¹) = τ (M₀.π y))
    {r₀ : G} (hr₀A : r₀ ∈ Q ⊓ QB C) (hr₀Q1 : r₀ ∉ Q1 hc t)
    {x : G} (hxP : x ∈ P) (hx1 : ⁅x, r₀⁆ = 1) :
    ∀ r ∈ Q ⊓ QB C, ⁅x, r⁆ ∈ Z := by
  have hr₀Q : r₀ ∈ Q := (Subgroup.mem_inf.mp hr₀A).1
  have hxM : x ∈ M := (hP hxP).2
  obtain ⟨hxQ, -⟩ := hc.conj_mem_Q_of_mem_M hxM
  obtain ⟨T, hTπ, -, hFix⟩ :=
    exists_isometry_fixing_ker hc ht hC hP hPQ1 hxP hM hτπ
  have htM : t ∈ M := hc.LB_le_M ht.mem_LB
  obtain ⟨htQ, -⟩ := hc.conj_mem_Q_of_mem_M htM
  have hnoC : NoA2 Q Z (LB M Q C) :=
    hspread G M Q Z B hc n H.width H.n_gt H.noA2 H.gen C hC
  obtain ⟨W, hWmem, -, -, -⟩ := hC.lagr H.width H.n_gt hnoC hM
  have hπr₀W : M₀.π r₀ ∈ W := (hWmem _).mp (M₀.pi_mem_img hr₀A hr₀Q)
  have hπr₀ker : M₀.π r₀ ∉ LinearMap.ker ((τ : M₀.E →ₗ[K] M₀.E) - 1) := by
    intro hker
    apply hr₀Q1
    refine (hc.mem_Q1_iff htM).mpr ⟨hr₀Q, ?_⟩
    have h := LinearMap.mem_ker.mp hker
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
    exact (comm_mem_iff_fix htQ hτπ hr₀Q).mpr h
  have hπr₀not : M₀.π r₀ ∉ W ⊓ LinearMap.ker ((τ : M₀.E →ₗ[K] M₀.E) - 1) :=
    fun h => hπr₀ker (Submodule.mem_inf.mp h).2
  have hWle := card_img_le_mul_card_inf_ker hc ht hC htC hτπ hWmem
  have hWle' : Nat.card ↥W ≤ Nat.card K *
      Nat.card ↥(W ⊓ LinearMap.ker ((τ : M₀.E →ₗ[K] M₀.E) - 1)) := by
    rw [hM.card]
    exact hWle
  have hWH := eq_sup_span_of_card_le inf_le_left hπr₀W hπr₀not hWle'
  intro r hrA
  have hrQ : r ∈ Q := (Subgroup.mem_inf.mp hrA).1
  have hπrW : M₀.π r ∈ W := (hWmem _).mp (M₀.pi_mem_img hrA hrQ)
  rw [hWH] at hπrW
  obtain ⟨f, hf, c, hcspan, hfc⟩ := Submodule.mem_sup.mp hπrW
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hcspan
  have hτf : τ f = f := by
    have h := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hf).2
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
    exact h
  have hTv : T (M₀.π r₀) = M₀.π r₀ := by
    have h : ⁅x, r₀⁆ ∈ Z := by rw [hx1]; exact Z.one_mem
    exact (comm_mem_iff_fix hxQ hTπ hr₀Q).mp h
  have hTr : T (M₀.π r) = M₀.π r := by
    rw [← hfc, map_add, map_smul, hFix f hτf, hTv]
  exact (comm_mem_iff_fix hxQ hTπ hrQ).mpr hTr

private def commRightHom {C : Subgroup G} (hC : Ctx M Q Z C) {P : Subgroup G}
    (hP : P ≤ QB C ⊓ M) {r₀ : G} (hr₀ : r₀ ∈ QB C) : ↥P →* ↥C where
  toFun x := ⟨⁅(x : G), r₀⁆, hC.comm_QB_le_B ((hP x.2).1) hr₀⟩
  map_one' := Subtype.ext (by simp [commutatorElement_def])
  map_mul' x y := by
    apply Subtype.ext
    have hxQB : (x : G) ∈ QB C := (hP x.2).1
    have hyQB : (y : G) ∈ QB C := (hP y.2).1
    have hyC : ⁅(y : G), r₀⁆ ∈ C := hC.comm_QB_le_B hyQB hr₀
    have hxrC : ⁅(x : G), r₀⁆ ∈ C := hC.comm_QB_le_B hxQB hr₀
    have hcent : (x : G) * ⁅(y : G), r₀⁆ * (x : G)⁻¹ = ⁅(y : G), r₀⁆ := by
      rw [Ctx.comm_of_mem_QB_of_mem_C hC hxQB hyC]
      group
    have habel : ⁅(y : G), r₀⁆ * ⁅(x : G), r₀⁆ = ⁅(x : G), r₀⁆ * ⁅(y : G), r₀⁆ :=
      congrArg Subtype.val (hC.isElemAbelian_B.1.is_comm.comm ⟨_, hyC⟩ ⟨_, hxrC⟩)
    show ⁅(x : G) * (y : G), r₀⁆ = ⁅(x : G), r₀⁆ * ⁅(y : G), r₀⁆
    rw [show ⁅(x : G) * (y : G), r₀⁆ =
      (x : G) * ⁅(y : G), r₀⁆ * (x : G)⁻¹ * ⁅(x : G), r₀⁆ by
        simp only [commutatorElement_def]; group, hcent, habel]

theorem Good101.card_le_of_centralizes_Q1
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    {C : Subgroup G} (hC : Ctx M Q Z C) (hCY : C ≤ QB Y) {P : Subgroup G}
    (hP : P ≤ QB C ⊓ M) (hPQ1 : ∀ x ∈ P, ∀ e ∈ Q1 hc t, ⁅x, e⁆ ∈ Z) :
    Nat.card ↥P ≤ Nat.card Z * Nat.card ↥(P ⊓ Q) := by
  have htC : t ∈ QB C := Sit.mem_QB_of_le_QB hs hC hCY
  have hnoC : NoA2 Q Z (LB M Q C) :=
    hspread G M Q Z B hc n H.width H.n_gt H.noA2 H.gen C hC
  obtain ⟨m, γ, M₀, -, hM⟩ := stroth_globalModelDataGF hc.hyp
  have hmemQ : ∀ x ∈ P, (∀ r ∈ Q ⊓ QB C, ⁅x, r⁆ ∈ Z) → x ∈ Q := fun x hx hxr =>
    hC.centralizer_inf_QB_le H.width H.n_gt hnoC hM (hP hx).1 fun r hr => by
      have h1 : ⁅x, r⁆ ∈ Z ⊓ C := ⟨hxr r hr, hC.comm_QB_le_B (hP hx).1 hr.2⟩
      rw [hC.inf_eq_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
  by_cases hcase : Q ⊓ QB C ≤ Q1 hc t
  · have hPQ : P ≤ Q := fun x hx => hmemQ x hx fun r hr => hPQ1 x hx r (hcase hr)
    rw [inf_eq_left.mpr hPQ]
    exact Nat.le_mul_of_pos_left _ Nat.card_pos
  · obtain ⟨r₀, hr₀A, hr₀Q1⟩ := SetLike.not_le_iff_exists.mp hcase
    have htM : t ∈ M := hc.LB_le_M ht.mem_LB
    obtain ⟨τ, hτπ, -, -⟩ := hM.linear_of_centralizes htM (hc.LB_centralizes_Z ht.mem_LB)
    let φ : ↥P →* ↥C := commRightHom hC hP (Subgroup.mem_inf.mp hr₀A).2
    have hker : φ.ker ≤ (P ⊓ Q).subgroupOf P := by
      intro x hx
      have hxP : (x : G) ∈ P := x.2
      have hx1 : ⁅(x : G), r₀⁆ = 1 := by
        have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
        simpa [φ, commRightHom] using h
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hxP, hmemQ _ hxP
        (comm_inf_QB_mem_Z_of_ker hc H hspread ht hC htC hP hPQ1 hM hτπ hr₀A hr₀Q1 hxP hx1)⟩)
    have hker_le : Nat.card ↥φ.ker ≤ Nat.card ↥(P ⊓ Q) :=
      (Nat.card_le_card_of_injective (Subgroup.inclusion hker)
        (Subgroup.inclusion_injective hker)).trans_eq
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : P ⊓ Q ≤ P)).toEquiv)
    have hrange_le : Nat.card ↥φ.range ≤ Nat.card Z := by
      have h1 : Nat.card ↥φ.range ≤ Nat.card ↥C :=
        Nat.card_le_card_of_injective (fun x : ↥φ.range => (x.1 : ↥C))
          (fun a b h => Subtype.ext h)
      have h2 : Nat.card ↥C = Nat.card Z := by
        obtain ⟨g, hg⟩ := hC.conj
        rw [hg]
        exact card_conjSubgroup g Z
      exact h1.trans (le_of_eq h2)
    calc Nat.card ↥P = Nat.card ↥φ.ker * Nat.card ↥φ.range :=
          (Subgroup.card_ker_mul_card_range φ).symm
      _ ≤ Nat.card ↥(P ⊓ Q) * Nat.card Z := Nat.mul_le_mul hker_le hrange_le
      _ = Nat.card Z * Nat.card ↥(P ⊓ Q) := mul_comm _ _

end CFSG.RankThree.GF2n.Stroth80

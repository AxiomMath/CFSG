module

public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaCent
public import CFSG.RankThree.GF2n.Stroth80.Sec310Count
public import CFSG.RankThree.GF2n.Stroth80.Sec34TI
public import CFSG.RankThree.GF2n.Stroth80.Sec310RootFlag

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement Matrix

theorem mem_sup_iff_map_mem {G H : Type*} [Group G] [Group H] {R N L : Subgroup G}
    (φ : ↥R →* H) (hNφ : φ.ker = N.subgroupOf R) (hN : N ≤ R) (hL : L ≤ R)
    {S : Subgroup H} (h : (L.subgroupOf R).map φ = S) (r : ↥R) :
    (r : G) ∈ L ⊔ N ↔ φ r ∈ S := by
  have hNn : (N.subgroupOf R).Normal := by rw [← hNφ]; exact MonoidHom.normal_ker φ
  subst h
  constructor
  · intro hr
    have hr' : r ∈ L.subgroupOf R ⊔ N.subgroupOf R := by
      rw [← Subgroup.subgroupOf_sup hL hN]
      exact Subgroup.mem_subgroupOf.mpr hr
    obtain ⟨l, hl, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hr'
    refine ⟨l, hl, ?_⟩
    have hn1 : φ n = 1 := by rw [← MonoidHom.mem_ker, hNφ]; exact hn
    rw [map_mul, hn1, mul_one]
  · rintro ⟨l, hl, hlr⟩
    have hk : l⁻¹ * r ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hlr, inv_mul_cancel]
    rw [hNφ, Subgroup.mem_subgroupOf] at hk
    have e : (r : G) = (l : G) * ((l⁻¹ * r : ↥R) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hl) hk

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.exists_centSub (hc : Ctx M Q Z B) (S : Set G) :
    ∃ T : Subgroup G, ∀ x, x ∈ T ↔ x ∈ LB M Q B ∧ ∀ y ∈ S, ⁅x, y⁆ ∈ Z := by
  have hZn : ∀ a ∈ M, ∀ z ∈ Z, a * z * a⁻¹ ∈ Z := fun a ha z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 ha) z).mp hz
  refine ⟨{ carrier := {x | x ∈ LB M Q B ∧ ∀ y ∈ S, ⁅x, y⁆ ∈ Z}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro x x' ⟨hx, hx'⟩ ⟨hx2, hx2'⟩
    refine ⟨(LB M Q B).mul_mem hx hx2, fun y hy => ?_⟩
    have e : ⁅x * x', y⁆ = x * ⁅x', y⁆ * x⁻¹ * ⁅x, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Z.mul_mem (hZn x (hc.LB_le_M hx) _ (hx2' y hy)) (hx' y hy)
  · refine ⟨(LB M Q B).one_mem, fun y _ => ?_⟩
    rw [show ⁅(1 : G), y⁆ = 1 by simp [commutatorElement_def]]
    exact Z.one_mem
  · rintro x ⟨hx, hx'⟩
    refine ⟨(LB M Q B).inv_mem hx, fun y hy => ?_⟩
    have e : ⁅x⁻¹, y⁆ = (x⁻¹ * ⁅x, y⁆ * x)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    refine Z.inv_mem ?_
    have := hZn x⁻¹ (M.inv_mem (hc.LB_le_M hx)) _ (hx' y hy)
    simpa using this


theorem Ctx.card_map_LB_ge (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z)
    {ι : Type} [Fintype ι] [DecidableEq ι] (φ : ↥(Rt M (LB M Q B) t) →* GL ι K)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    {nn : ℕ} {γ : G → GaloisField 2 nn} {M₀ : Tim79.QuadModel Q Z (GaloisField 2 nn) γ}
    (h : GlobalModelData M Q Z γ M₀) (θ : GaloisField 2 nn ≃+* K)
    (hθ : ∀ (c : GaloisField 2 nn) (v w : ↥(Vt M (LB M Q B) B Z t)),
      M₀.π w = c • M₀.π v → secVec ψ w = θ c • secVec ψ v)
    (perp : Set (ι → K))
    (hW : ∀ x : ι → K, (∃ w : ↥(Vt M (LB M Q B) B Z t),
      (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧ secVec ψ w = x) ↔ x ∈ perp)
    (hsmul : ∀ (c : K) (x : ι → K), x ∈ perp → c • x ∈ perp)
    (hcard : Nat.card perp = Nat.card K ^ (Fintype.card ι - 1)) :
    Nat.card K ^ (Fintype.card ι - 2) ≤
      Nat.card (((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ) := by
  classical
  set V := Vt M (LB M Q B) B Z t with hV
  have ht : t ∈ LB M Q B := hs.mem
  have h35all := stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen
  set Y : Subgroup G := V ⊓ QB B with hY
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hZY : Z ≤ Y := le_inf hZV (hc.Z_le_QB).1
  have hBY : B ≤ Y := le_inf (hc.B_le_Vt ht) hc.B_le_QB
  have hYQ : Y ≤ Q ⊓ QB B := inf_le_inf_right _ (hc.Vt_le_Q t)
  have hYV : Y ≤ V := inf_le_left
  have hYsc : ∀ (c : GaloisField 2 nn) (e : M₀.E), e ∈ M₀.img Y → c • e ∈ M₀.img Y := by
    intro c e he
    obtain ⟨y, hyY, hyQ, rfl⟩ := he
    have hyV : y ∈ V := hYV hyY
    obtain ⟨v', hv'V, hv'Q, hv'⟩ := hc.smul_mem_img_Vt h t c (M₀.pi_mem_img hyV hyQ)
    have hsec := hθ c ⟨y, hyV⟩ ⟨v', hv'V⟩ hv'
    have hyp : secVec ψ ⟨y, hyV⟩ ∈ perp := (hW _).mp ⟨⟨y, hyV⟩, hyY, rfl⟩
    obtain ⟨w, hwY, hw⟩ := (hW _).mpr (hsmul (θ c) _ hyp)
    have hv'Y : v' ∈ Y := mem_of_secVec_eq hZY ψ (y := ⟨v', hv'V⟩) hwY (by rw [hw, hsec])
    exact ⟨v', hv'Y, hv'Q, hv'⟩
  obtain ⟨b, hbY, hb0, -, -, -, hcount⟩ := hc.elation_package hs.width hs.n_gt hs.noA2
    h35all.2.2.1 h35all.2.2.2 h hBY hYQ hYsc
  obtain ⟨T, hT⟩ := hc.exists_centSub (Y : Set G)
  have hcnt := hcount T hT
  have hKg : Nat.card (GaloisField 2 nn) = Nat.card K := h.card.trans hK.symm
  have hK1 : 2 ≤ Nat.card K := by
    have := hc.hyp.q4
    omega
  have himg : Nat.card (M₀.img Y) = Nat.card perp := by
    have e1 := M₀.card_eq (hYQ.trans inf_le_left) hZY
    have e2 := card_eq_of_secVec ψ hZY hYV perp hW
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (e1.symm.trans e2)
  have hdim : Module.finrank (GaloisField 2 nn) (imgSub M₀ Y hYsc) = Fintype.card ι - 1 := by
    have hc1 : Nat.card (imgSub M₀ Y hYsc) = Nat.card (M₀.img Y) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun e => mem_imgSub)
    rw [Module.natCard_eq_pow_finrank (K := GaloisField 2 nn), himg, hcard, hKg] at hc1
    exact Nat.pow_right_injective hK1 hc1
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (LB M Q B) ht
  have hcard' := card_inf_mul_card_map hLR φ hker
  have hLN : LB M Q B ⊓ hc.CN t ≤ T := fun x hx =>
    (hT x).mpr ⟨hx.1, fun y hy => (Ctx.mem_CN.mp hx.2).2 y (hYV hy)⟩
  have hle : Nat.card ↥(LB M Q B ⊓ hc.CN t) ≤ Nat.card T := Subgroup.card_le_of_le hLN
  rw [hcnt, hdim, hKg, show Fintype.card ι - 1 - 1 = Fintype.card ι - 2 by omega] at hcard'
  have hpos : 0 < Nat.card ↥(LB M Q B ⊓ hc.CN t) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card K ^ (Fintype.card ι - 2)
      ≤ Nat.card T * Nat.card K ^ (Fintype.card ι - 2) := Nat.mul_le_mul_right _ hle
    _ = _ := hcard'.symm


theorem Ctx.map_LB_normalized (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {X : Subgroup (GL ι K)}
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {u : ι → K}
    (hBiff : ∀ x : ι → K, (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
      ∃ c : K, x = c • u)
    {A : GL ι K} (hA : A ∈ X) (hAu : ∃ c : K, (A : Matrix ι ι K) *ᵥ u = c • u) :
    ∀ l ∈ ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ,
      A * l * A⁻¹ ∈ ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ := by
  classical
  intro l hl
  obtain ⟨c, hc'⟩ := hAu
  rw [← hφ] at hA
  obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hA
  have ht : t ∈ LB M Q B := hs.mem
  have hVR := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hle : conjSubgroup (r : G) B ≤ B ⊔ Z := by
    intro x hx
    have hb : (r : G)⁻¹ * x * r ∈ B := mem_conjSubgroup.mp hx
    have hbV : (r : G)⁻¹ * x * r ∈ Vt M (LB M Q B) B Z t := hBV hb
    have hxV : x ∈ Vt M (LB M Q B) B Z t := by
      have := (Subgroup.mem_normalizer_iff.mp (hVR r.2) _).mp hbV
      rwa [show (r : G) * ((r : G)⁻¹ * x * r) * (r : G)⁻¹ = x by group] at this
    have hrel : secVec ψ ⟨x, hxV⟩ = (φ r : Matrix ι ι K) *ᵥ secVec ψ ⟨_, hbV⟩ :=
      hψ r ⟨_, hbV⟩ ⟨x, hxV⟩ (by group)
    obtain ⟨a, ha⟩ := (hBiff _).mp ⟨⟨_, hbV⟩, hb, rfl⟩
    obtain ⟨b'', hb'', hb''e⟩ := (hBiff ((a * c) • u)).mpr ⟨a * c, rfl⟩
    refine mem_of_secVec_eq (S := B ⊔ Z) le_sup_right ψ (y := ⟨x, hxV⟩) (w := b'')
      (Subgroup.mem_sup_left hb'') ?_
    rw [hb''e, hrel, ha, Matrix.mulVec_smul, hc', smul_smul]
  have hLeq := hc.conj_LB_eq_of_le_sup_Z (hc.Rt_le_M t r.2) hle
  obtain ⟨x₀, hx₀, rfl⟩ := hl
  refine ⟨r * x₀ * r⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
  have hx₀L : (x₀ : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hx₀
  have hmem : (r : G) * (x₀ : G) * (r : G)⁻¹ ∈ conjSubgroup (r : G) (LB M Q B) := by
    rw [mem_conjSubgroup,
      show (r : G)⁻¹ * ((r : G) * (x₀ : G) * (r : G)⁻¹) * (r : G) = (x₀ : G) by group]
    exact hx₀L
  rw [hLeq] at hmem
  exact hmem


open CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Orthogonal QuadraticMap

theorem Ctx.sp_perp_data (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = Nat.card Z) {m : ℕ} (hm : 2 ≤ m)
    (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K)
    (hφ : φ.range = StatedSp m K)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    [hn : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin m ⊕ Fin m → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v))) :
    ∃ (nn : ℕ) (γ : G → GaloisField 2 nn) (M₀ : Tim79.QuadModel Q Z (GaloisField 2 nn) γ)
      (_ : GlobalModelData M Q Z γ M₀) (θ : GaloisField 2 nn ≃+* K)
      (_ : ∀ (c : GaloisField 2 nn) (v w : ↥(Vt M (LB M Q B) B Z t)),
        M₀.π w = c • M₀.π v → secVec ψ w = θ c • secVec ψ v)
      (u : Fin m ⊕ Fin m → K), u ≠ 0 ∧
      (∀ x : Fin m ⊕ Fin m → K,
        (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u) ∧
      (∀ x : Fin m ⊕ Fin m → K,
        (∃ w : ↥(Vt M (LB M Q B) B Z t),
          (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧ secVec ψ w = x) ↔ spForm m K x u = 0) := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hchi := hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB h35 ht hs.notQ hnotQB
  have hperp := stroth310Perp_of_34 h34 G M Q Z B hc n t hs hnotQB
  have hVR := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  let D := hc.natCommData ht hchi.1 hchi.2
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨nn, γ, M₀, h, θ, hθ⟩ :=
    hc.exists_globalRingEquiv ht hK addCommutantScalar_statedSp φ hφ ψ hψ
  obtain ⟨b₀, hb₀B, hu0, hBiff⟩ := hc.exists_point_of_le hBV ψ h θ hθ
  set u := secVec ψ b₀ with hu
  have C' : ∀ (b : ↥(Vt M (LB M Q B) B Z t)), secVec ψ b ≠ 0 → ∀ x : Fin m ⊕ Fin m → K,
      pairVec D ψ b x = 1 ↔ spForm m K (secVec ψ b) x = 0 :=
    fun b hb x => hc.pairVec_eq_one_iff_spForm ht D φ hφ ψ hψ h θ hθ hb x
  have hsym : ∀ x y : Fin m ⊕ Fin m → K, spForm m K x y = 0 ↔ spForm m K y x = 0 := by
    intro x y
    rw [← spForm_isAlt.neg_eq x y, neg_eq_zero]
  have hW : ∀ x : Fin m ⊕ Fin m → K,
      (∃ w : ↥(Vt M (LB M Q B) B Z t), (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧
        secVec ψ w = x) ↔ spForm m K x u = 0 := by
    intro x
    constructor
    · rintro ⟨w, ⟨-, hwQB⟩, rfl⟩
      have hw := (hperp (w : G) w.2).mp hwQB
      obtain ⟨y, hy⟩ := exists_kapVec D ψ (secVec ψ w)
      have h1 : ⁅(y : G), t⁆ * (w : G)⁻¹ ∈ Z :=
        (secVec_eq_iff ψ ⟨⁅(y : G), t⁆, D.comm_t_mem y y.2⟩ w).mp hy
      have h2 : ⁅(b₀ : G), (y : G)⁆ = 1 := hw b₀ hb₀B y y.2 h1
      have h3 : pairVec D ψ b₀ (secVec ψ w) = 1 := by rw [pairVec_eq D ψ b₀ y hy]; exact h2
      exact (hsym _ _).mp ((C' b₀ hu0 _).mp h3)
    · intro hx
      obtain ⟨w, hw⟩ := exists_secVec_eq ψ x
      refine ⟨w, ⟨w.2, (hperp (w : G) w.2).mpr fun b hb y hy hyt => ?_⟩, hw⟩
      have hk : kapVec D ψ ⟨y, hy⟩ = x := by
        rw [← hw]
        exact (secVec_eq_iff ψ ⟨⁅y, t⁆, D.comm_t_mem y hy⟩ w).mpr hyt
      rw [← pairVec_eq D ψ ⟨b, hBV hb⟩ ⟨y, hy⟩ hk]
      obtain ⟨c, hcc⟩ := (hBiff (secVec ψ ⟨b, hBV hb⟩)).mp ⟨⟨b, hBV hb⟩, hb, rfl⟩
      by_cases hc0 : c = 0
      · have hz : b ∈ Z :=
          (secVec_eq_zero_iff ψ ⟨b, hBV hb⟩).mp (by rw [hcc, hc0, zero_smul])
        have := D.comm_Z_left hz hy
        rw [pairVec_eq D ψ ⟨b, hBV hb⟩ ⟨y, hy⟩ hk]
        exact this
      · have hbu : secVec ψ ⟨b, hBV hb⟩ ≠ 0 := by
          rw [hcc]; exact smul_ne_zero hc0 hu0
        refine (C' ⟨b, hBV hb⟩ hbu x).mpr ?_
        rw [hcc, map_smul, LinearMap.smul_apply, smul_eq_mul, (hsym _ _).mp hx, mul_zero]
  exact ⟨nn, γ, M₀, h, θ, hθ, u, hu0, hBiff, hW⟩


theorem Ctx.omega_singular_flag (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {Q' : QuadraticForm K (ι → K)}
    {X : Subgroup (GL ι K)} (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X)
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v))) :
    ∀ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B → Q' (secVec ψ b) = 0 := by
  classical
  intro b hb
  have ht : t ∈ LB M Q B := hs.mem
  have hVR := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  obtain ⟨nn, γ, M₀, h, θ, hθ⟩ := hc.exists_globalRingEquiv ht hK hX φ hφ ψ hψ
  obtain ⟨b₀, hb₀B, hu0, hBiff⟩ := hc.exists_point_of_le hBV ψ h θ hθ
  set u := secVec ψ b₀ with hu
  suffices hQu : Q' u = 0 by
    obtain ⟨c, hcc⟩ := (hBiff (secVec ψ b)).mp ⟨b, hb, rfl⟩
    rw [hcc, map_smul_eq_sq, hQu, mul_zero]
  by_contra ha
  let S : Set (Matrix ι ι K) :=
    {A | ∃ (r : G) (hr : r ∈ LB M Q B),
      A = (φ ⟨r, le_Rt (M := M) (LB M Q B) ht hr⟩ : Matrix ι ι K)}
  let H : (ι → K) → Prop := fun x =>
    ∃ w : ↥(Vt M (LB M Q B) B Z t), (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧ secVec ψ w = x
  have hBZ : ∀ y ∈ B ⊔ Z, ∃ b ∈ B, ∃ z ∈ Z, y = b * z := fun y hy =>
    exists_mul_of_mem_sup (fun b hb z hz => by
      have := hc.conj_Z_of_mem_Q (hc.le hb) hz
      calc b * z = (b * z * b⁻¹) * b := by group
        _ = z * b := by rw [this]) hy
  have hflag : ∀ A ∈ S, ((A *ᵥ u = u) ∧ (∀ x, H x → ∃ c : K, A *ᵥ x - x = c • u) ∧
      ∀ x, H (A *ᵥ x - x)) := by
    rintro A ⟨r, hr, rfl⟩
    have hrR := le_Rt (M := M) (LB M Q B) ht hr
    have hf := hc.LB_flag h35 ht hs.notQ hr
    exact (commFlag_iff φ ψ hψ hVR hZV hBV inf_le_left (le_inf hZV (hc.Z_le_QB).1) hBZ hBiff
      (fun x => Iff.rfl) ⟨r, hrR⟩).mp hf
  have hSX : ∀ A ∈ S, ∃ g : GL ι K, g ∈ X ∧ A = (g : Matrix ι ι K) := by
    rintro A ⟨r, hr, rfl⟩
    exact ⟨_, hφ ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩, rfl⟩
  have hcent : ∀ x : ι → K, (∀ A ∈ S, A *ᵥ x = x) → ∃ c : K, x = c • u := by
    intro x hx
    obtain ⟨v, rfl⟩ := exists_secVec_eq ψ x
    have hv : (v : G) ∈ CQt Q Z (LB M Q B) := by
      refine ⟨hc.Vt_le_Q t v.2, fun l hl => ?_⟩
      have h0 := secVec_comm φ ψ hψ hVR ⟨l, le_Rt (M := M) (LB M Q B) ht hl⟩ v
      have h1 := hx _ ⟨l, hl, rfl⟩
      rw [h1, sub_self] at h0
      exact (secVec_eq_zero_iff ψ _).mp h0
    rw [h35] at hv
    obtain ⟨b', hb', z, hz, hbz⟩ := hBZ _ hv
    have hvv : v = ⟨b', hBV hb'⟩ * ⟨z, hZV hz⟩ := Subtype.ext hbz
    have : secVec ψ v = secVec ψ ⟨b', hBV hb'⟩ := by
      rw [hvv, secVec_mul, (secVec_eq_zero_iff ψ ⟨z, hZV hz⟩).mpr hz, add_zero]
    obtain ⟨c, hcc⟩ := (hBiff _).mp ⟨⟨b', hBV hb'⟩, hb', rfl⟩
    exact ⟨c, by rw [this]; exact hcc⟩
  exact false_of_nonsingular_flag Q' hQ h3 S hu0
    (fun h0 => ha (by simp [h0])) H
    (fun A hA x => by
      obtain ⟨g, hg, rfl⟩ := hSX A hA
      exact E.quad_mulVec hg x)
    (fun A hA x y => by
      obtain ⟨g, hg, rfl⟩ := hSX A hA
      exact E.polar_mulVec hg x y)
    (fun A hA => (hflag A hA).1) (fun A hA => (hflag A hA).2.1) (fun A hA => (hflag A hA).2.2)
    hcent


theorem Ctx.omega_perp_data (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)} (E : ElemMatrixIso Q' X)
    (hQ : (polarBilin Q').Nondegenerate) (h3 : 3 ≤ Module.finrank K (ι → K))
    (hX : AddCommutantScalar X) (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v))) :
    ∃ (nn : ℕ) (γ : G → GaloisField 2 nn) (M₀ : Tim79.QuadModel Q Z (GaloisField 2 nn) γ)
      (_ : GlobalModelData M Q Z γ M₀) (θ : GaloisField 2 nn ≃+* K)
      (_ : ∀ (c : GaloisField 2 nn) (v w : ↥(Vt M (LB M Q B) B Z t)),
        M₀.π w = c • M₀.π v → secVec ψ w = θ c • secVec ψ v)
      (u : ι → K), Q' u = 0 ∧ u ≠ 0 ∧
      (∀ x : ι → K,
        (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u) ∧
      (∀ x : ι → K, (∃ w : ↥(Vt M (LB M Q B) B Z t),
        (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧ secVec ψ w = x) ↔ polar Q' u x = 0) := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hchi := hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB h35 ht hs.notQ hnotQB
  have hperp := stroth310Perp_of_34 h34 G M Q Z B hc n t hs hnotQB
  have hVR := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hsing := hc.omega_singular_flag h34 hs hK E hQ h3 hX φ hφ ψ hψ
  let D := hc.natCommData ht hchi.1 hchi.2
  obtain ⟨nn, γ, M₀, h, θ, hθ⟩ := hc.exists_globalRingEquiv ht hK hX φ hφ ψ hψ
  obtain ⟨b₀, hb₀B, hu0, hBiff⟩ := hc.exists_point_of_le hBV ψ h θ hθ
  set u := secVec ψ b₀ with hu
  have hQu : Q' u = 0 := hsing b₀ hb₀B
  have C' : ∀ (b : ↥(Vt M (LB M Q B) B Z t)), (b : G) ∈ B → secVec ψ b ≠ 0 →
      ∀ x : ι → K, pairVec D ψ b x = 1 ↔ polar Q' (secVec ψ b) x = 0 := by
    intro b hb hb0 x
    refine hc.pairVec_eq_one_iff_of_forward ht D ψ h θ hθ hb0 (polarBilin Q' (secVec ψ b)) ?_ x
    intro y hy
    have hg0 := E.additive_eq_zero_of_range_polar hQ h3 φ hφ (pairHom D ψ b) (hsing b hb) hb0
      (fun r hr z => by
        show Additive.ofMul (pairVec D ψ _ _) = Additive.ofMul (pairVec D ψ _ _)
        rw [pairVec_conj D ψ hψ hVR _ r hr z]) (x := y) hy
    exact ofMul_eq_zero.mp hg0
  have hW : ∀ x : ι → K,
      (∃ w : ↥(Vt M (LB M Q B) B Z t), (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧
        secVec ψ w = x) ↔ polar Q' u x = 0 := by
    intro x
    constructor
    · rintro ⟨w, ⟨-, hwQB⟩, rfl⟩
      have hw := (hperp (w : G) w.2).mp hwQB
      obtain ⟨y, hy⟩ := exists_kapVec D ψ (secVec ψ w)
      have h1 : ⁅(y : G), t⁆ * (w : G)⁻¹ ∈ Z :=
        (secVec_eq_iff ψ ⟨⁅(y : G), t⁆, D.comm_t_mem y y.2⟩ w).mp hy
      have h2 : ⁅(b₀ : G), (y : G)⁆ = 1 := hw b₀ hb₀B y y.2 h1
      have h3' : pairVec D ψ b₀ (secVec ψ w) = 1 := by rw [pairVec_eq D ψ b₀ y hy]; exact h2
      exact (C' b₀ hb₀B hu0 _).mp h3'
    · intro hx
      obtain ⟨w, hw⟩ := exists_secVec_eq ψ x
      refine ⟨w, ⟨w.2, (hperp (w : G) w.2).mpr fun b hb y hy hyt => ?_⟩, hw⟩
      have hk : kapVec D ψ ⟨y, hy⟩ = x := by
        rw [← hw]
        exact (secVec_eq_iff ψ ⟨⁅y, t⁆, D.comm_t_mem y hy⟩ w).mpr hyt
      rw [← pairVec_eq D ψ ⟨b, hBV hb⟩ ⟨y, hy⟩ hk]
      obtain ⟨c, hcc⟩ := (hBiff (secVec ψ ⟨b, hBV hb⟩)).mp ⟨⟨b, hBV hb⟩, hb, rfl⟩
      by_cases hc0 : c = 0
      · have hz : b ∈ Z :=
          (secVec_eq_zero_iff ψ ⟨b, hBV hb⟩).mp (by rw [hcc, hc0, zero_smul])
        have := D.comm_Z_left hz hy
        rw [pairVec_eq D ψ ⟨b, hBV hb⟩ ⟨y, hy⟩ hk]
        exact this
      · have hbu : secVec ψ ⟨b, hBV hb⟩ ≠ 0 := by
          rw [hcc]; exact smul_ne_zero hc0 hu0
        refine (C' ⟨b, hBV hb⟩ hb hbu x).mpr ?_
        rw [hcc, polar_smul_left_eq, hx, mul_zero]
  exact ⟨nn, γ, M₀, h, θ, hθ, u, hQu, hu0, hBiff, hW⟩


theorem Ctx.omega_points_flag (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X)
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v))) :
    ∃ u : ι → K, Q' u = 0 ∧ u ≠ 0 ∧
      (∀ x : ι → K,
        (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u) ∧
      (∀ x : ι → K, (∃ w : ↥(Vt M (LB M Q B) B Z t),
        (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧ secVec ψ w = x) ↔ polar Q' u x = 0) ∧
      ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL u := by
  classical
  obtain ⟨nn, γ, M₀, h, θ, hθ, u, hQu, hu0, hBiff, hW⟩ :=
    hc.omega_perp_data h34 hs hnotQB hK E hQ h3 hX φ hφ ψ hψ
  have ht : t ∈ LB M Q B := hs.mem
  have hVR := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hBZ : ∀ y ∈ B ⊔ Z, ∃ b ∈ B, ∃ z ∈ Z, y = b * z := fun y hy =>
    exists_mul_of_mem_sup (fun b hb z hz => by
      have := hc.conj_Z_of_mem_Q (hc.le hb) hz
      calc b * z = (b * z * b⁻¹) * b := by group
        _ = z * b := by rw [this]) hy
  have hflag := fun s => commFlag_iff (V := Vt M (LB M Q B) B Z t) (B := B)
    (W := Vt M (LB M Q B) B Z t ⊓ QB B) φ ψ hψ hVR hZV hBV inf_le_left
    (le_inf hZV (hc.Z_le_QB).1) hBZ (u := u) (H := fun x => polar Q' u x = 0) hBiff hW s
  have hcnt := hc.card_map_LB_ge h34 hs hK φ hker ψ h θ hθ {x | polar Q' u x = 0} hW
    (fun c x hx => by
      show polar Q' u (c • x) = 0
      rw [polar_smul_right_eq, show polar Q' u x = 0 from hx, mul_zero])
    (card_polar_perp Q' hQ hu0)
  have hLsub : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ ≤ E.LomGL u := by
    rintro _ ⟨l, hl, rfl⟩
    have hlL : (l : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hl
    refine (E.mem_LomGL_iff_flag hQ hQu hu0).mpr ⟨hφ ▸ MonoidHom.mem_range.mpr ⟨l, rfl⟩, ?_⟩
    exact (hflag l).mp (hc.LB_flag h35 ht hs.notQ hlL)
  refine ⟨u, hQu, hu0, hBiff, hW, Subgroup.eq_of_le_of_card_ge hLsub ?_⟩
  rw [E.card_LomGL hQ hQu hu0, Module.finrank_fintype_fun_eq_card]
  exact hcnt

theorem Ctx.root_omega (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X)
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (r : ↥(Rt M (LB M Q B) t)) :
    (r : G) ∈ LB M Q B ⊔ hc.CN t ↔
      ((∀ b ∈ B, ⁅(r : G), b⁆ ∈ Z) ∧
        (∀ v ∈ Vt M (LB M Q B) B Z t ⊓ QB B, ⁅(r : G), v⁆ ∈ B ⊔ Z) ∧
        (∀ v ∈ Vt M (LB M Q B) B Z t, ⁅(r : G), v⁆ ∈ Vt M (LB M Q B) B Z t ⊓ QB B)) := by
  classical
  obtain ⟨u, hQu, hu0, hBiff, hW, hLeq⟩ :=
    hc.omega_points_flag h34 hs hnotQB hK E hQ h3 hX φ hφ hker ψ hψ
  have ht : t ∈ LB M Q B := hs.mem
  have hVR := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBZ : ∀ y ∈ B ⊔ Z, ∃ b ∈ B, ∃ z ∈ Z, y = b * z := fun y hy =>
    exists_mul_of_mem_sup (fun b hb z hz => by
      have := hc.conj_Z_of_mem_Q (hc.le hb) hz
      calc b * z = (b * z * b⁻¹) * b := by group
        _ = z * b := by rw [this]) hy
  have hflag := fun s => commFlag_iff (V := Vt M (LB M Q B) B Z t) (B := B)
    (W := Vt M (LB M Q B) B Z t ⊓ QB B) φ ψ hψ hVR hZV hBV inf_le_left
    (le_inf hZV (hc.Z_le_QB).1) hBZ (u := u) (H := fun x => polar Q' u x = 0) hBiff hW s
  rw [mem_sup_iff_map_mem φ hker (fun x hx => (Ctx.mem_CN.mp hx).1) (le_Rt (LB M Q B) ht) hLeq r,
    E.mem_LomGL_iff_flag hQ hQu hu0, ← hflag r]
  exact ⟨fun hh => hh.2, fun hh => ⟨hφ ▸ MonoidHom.mem_range.mpr ⟨r, rfl⟩, hh⟩⟩

end CFSG.RankThree.GF2n.Stroth80

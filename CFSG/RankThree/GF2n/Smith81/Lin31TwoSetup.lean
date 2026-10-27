module

public import CFSG.RankThree.GF2n.Smith81.Lin31TwoModel

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

private theorem exists_quotEquiv_of_img {G : Type} [Group G] {Q Z V : Subgroup G} {K : Type}
    [Field K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) (hVQ : V ≤ Q) {A : Type}
    [AddCommGroup A] (Ψ : ↥(M₀.img V) ≃+ A) :
    ∃ _ : (Z.subgroupOf V).Normal, ∃ ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative A,
      ∀ v : ↥V, Multiplicative.toAdd (ψ (QuotientGroup.mk v)) =
        Ψ ⟨M₀.π v, M₀.pi_mem_img v.2 (hVQ v.2)⟩ := by
  have hπV : ∀ v : ↥V, M₀.π v ∈ M₀.img V := fun v => M₀.pi_mem_img v.2 (hVQ v.2)
  let κ : ↥V →* Multiplicative A :=
    { toFun := fun v => Multiplicative.ofAdd (Ψ ⟨M₀.π v, hπV v⟩)
      map_one' := by
        show Multiplicative.ofAdd (Ψ ⟨M₀.π ((1 : ↥V) : G), hπV 1⟩) = 1
        rw [show (⟨M₀.π ((1 : ↥V) : G), hπV 1⟩ : ↥(M₀.img V)) = 0 from
          Subtype.ext (Tim79.QuadModel.pi_one M₀), map_zero, ofAdd_zero]
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (Ψ ⟨M₀.π ((x * y : ↥V) : G), hπV (x * y)⟩) =
          Multiplicative.ofAdd (Ψ ⟨M₀.π x, hπV x⟩) * Multiplicative.ofAdd (Ψ ⟨M₀.π y, hπV y⟩)
        rw [show (⟨M₀.π ((x * y : ↥V) : G), hπV (x * y)⟩ : ↥(M₀.img V)) =
            ⟨M₀.π x, hπV x⟩ + ⟨M₀.π y, hπV y⟩ from
          Subtype.ext (M₀.π_mul x (hVQ x.2) y (hVQ y.2)), map_add, ofAdd_add] }
  have hκ : ∀ v : ↥V, κ v = Multiplicative.ofAdd (Ψ ⟨M₀.π v, hπV v⟩) := fun v => rfl
  have hκsurj : Function.Surjective κ := by
    intro a
    obtain ⟨x, hxV, -, hx⟩ := (M₀.mem_img).mp (Ψ.symm (Multiplicative.toAdd a)).2
    refine ⟨⟨x, hxV⟩, ?_⟩
    rw [hκ, show (⟨M₀.π x, hπV ⟨x, hxV⟩⟩ : ↥(M₀.img V)) = Ψ.symm (Multiplicative.toAdd a) from
      Subtype.ext hx, AddEquiv.apply_symm_apply]
    rfl
  have hker : κ.ker = Z.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← M₀.π_ker _ (hVQ v.2), hκ, ofAdd_eq_one,
      AddEquiv.map_eq_zero_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  haveI hN : (Z.subgroupOf V).Normal := hker ▸ κ.normal_ker
  exact ⟨hN, (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective κ hκsurj), fun v => rfl⟩

private def dualCoord (F : Type) [Field F] : (Fin 2 → F) ≃+ (Fin 2 → F) where
  toFun n := ![n 1, -n 0]
  invFun n := ![-n 1, n 0]
  left_inv n := by
    funext i
    fin_cases i <;> simp
  right_inv n := by
    funext i
    fin_cases i <;> simp
  map_add' n n' := by
    funext i
    fin_cases i <;> simp <;> ring

private theorem dualCoord_apply {F : Type} [Field F] (n : Fin 2 → F) :
    dualCoord F n = ![n 1, -n 0] := rfl

private theorem dualCoord_mulVec {F : Type} [Field F] (g : GL (Fin 2) F)
    (hg : (g : Matrix (Fin 2) (Fin 2) F).det = 1) (n : Fin 2 → F) :
    dualCoord F ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ n) =
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ *ᵥ dualCoord F n := by
  have key : (g : Matrix (Fin 2) (Fin 2) F)ᵀ *ᵥ dualCoord F ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ n) =
      dualCoord F n := by
    rw [Matrix.det_fin_two] at hg
    funext i
    fin_cases i
    · simp [dualCoord_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination (n 1) * hg
    · simp [dualCoord_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination (-n 0) * hg
  rw [← key, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
    Matrix.one_mulVec]

section Setup

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace TensorModel

variable {TM : TensorModel M Q Z B}

private theorem exists_imgPlane_coord {u : Fin 2 → TM.F} (hu : u ≠ 0) :
    ∃ Ψ : ↥(TM.M₀.img (TM.plane u)) ≃+ (Fin 2 → TM.F),
      ∀ e, Matrix.vecMulVec (Ψ e) u = TM.Φ (e : TM.M₀.E) := by
  let Φu : ↥(TM.M₀.img (TM.plane u)) ≃+ ↥(planeAdd u) :=
    { toFun := fun e => ⟨TM.Φ (e : TM.M₀.E), img_plane.mp e.2⟩
      invFun := fun X => ⟨TM.Φ.symm (X : Matrix (Fin 2) (Fin 2) TM.F),
        img_plane.mpr (by rw [AddEquiv.apply_symm_apply]; exact X.2)⟩
      left_inv := fun e => Subtype.ext (TM.Φ.symm_apply_apply (e : TM.M₀.E))
      right_inv := fun X => Subtype.ext (TM.Φ.apply_symm_apply (X : Matrix (Fin 2) (Fin 2) TM.F))
      map_add' := fun e f => Subtype.ext (map_add TM.Φ (e : TM.M₀.E) (f : TM.M₀.E)) }
  refine ⟨Φu.trans (planeEquiv hu).symm, fun e => ?_⟩
  rw [← coe_planeEquiv hu, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rfl

private theorem exists_plane_quotEquiv {u : Fin 2 → TM.F} (hu : u ≠ 0)
    (J : (Fin 2 → TM.F) ≃+ (Fin 2 → TM.F)) :
    ∃ _ : (Z.subgroupOf (TM.plane u)).Normal,
      ∃ ψ : ↥(TM.plane u) ⧸ Z.subgroupOf (TM.plane u) ≃* Multiplicative (Fin 2 → TM.F),
        ∀ (v : ↥(TM.plane u)) (n : Fin 2 → TM.F), TM.Φ (TM.M₀.π v) = Matrix.vecMulVec n u →
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)) = J n := by
  obtain ⟨Ψ, hΨ⟩ := exists_imgPlane_coord (TM := TM) hu
  obtain ⟨hN, ψ, hψ⟩ := exists_quotEquiv_of_img TM.M₀ (plane_le_Q u) (Ψ.trans J)
  refine ⟨hN, ψ, fun v n hn => ?_⟩
  rw [hψ v, AddEquiv.trans_apply]
  congr 1
  apply (planeEquiv hu).injective
  apply Subtype.ext
  rw [coe_planeEquiv, coe_planeEquiv, hΨ]
  exact hn

private theorem sectionAct_plane {u : Fin 2 → TM.F} (hu : u ≠ 0)
    (J : (Fin 2 → TM.F) ≃+ (Fin 2 → TM.F)) (act : GL (Fin 2) TM.F → Matrix (Fin 2) (Fin 2) TM.F)
    (hJ : ∀ (s : ↥(Lgen M (LB M Q B))) (n : Fin 2 → TM.F),
      J ((TM.φ s : Matrix (Fin 2) (Fin 2) TM.F) *ᵥ n) = act (TM.φ s) *ᵥ J n) :
    SectionAct (ι := Fin 2) TM.F (Lgen M (LB M Q B)) (TM.plane u) Z TM.φ act := by
  obtain ⟨hN, ψ, hψ⟩ := exists_plane_quotEquiv hu J
  refine ⟨fun s hs => normalizes_plane u hs, hN, ψ, fun s v w hw => ?_⟩
  obtain ⟨hvQ, n, hn⟩ := mem_plane.mp v.2
  have hwn : TM.Φ (TM.M₀.π w) =
      Matrix.vecMulVec ((TM.φ s : Matrix (Fin 2) (Fin 2) TM.F) *ᵥ n) u := by
    rw [hw, TM.act s v hvQ, hn, Matrix.mul_vecMulVec]
  rw [hψ w _ hwn, hψ v n hn, hJ]

private theorem det_φ (s : ↥(Lgen M (LB M Q B))) :
    ((TM.φ s : GL (Fin 2) TM.F) : Matrix (Fin 2) (Fin 2) TM.F).det = 1 := by
  have h : TM.φ s ∈ TM.φ.range := ⟨s, rfl⟩
  rw [TM.φ_range] at h
  exact StatedAPI.mem_statedSL_iff.mp h

private theorem exists_conj_plane_eq (hc : Ctx M Q Z B) {u₁ u₂ : Fin 2 → TM.F} (hu₁ : u₁ ≠ 0)
    (hperm : ∀ m ∈ M, conjSubgroup m (TM.plane u₁) = TM.plane u₁ ∨
      conjSubgroup m (TM.plane u₁) = TM.plane u₂) :
    ∃ x ∈ M, conjSubgroup x (TM.plane u₁) = TM.plane u₂ := by
  by_contra hno
  have hMN : M ≤ Subgroup.normalizer (TM.plane u₁ : Set G) := fun m hm =>
    conjSubgroup_eq_self_iff.mp ((hperm m hm).resolve_right fun h => hno ⟨m, hm, h⟩)
  have hcomm : IsMulCommutative (TM.plane u₁) :=
    ⟨⟨fun a b => Subtype.ext (plane_comm a.2 b.2)⟩⟩
  have hle : TM.plane u₁ ≤ Z :=
    hc.hyp.maxAb.le_of_ge ⟨(plane_le_Q u₁).trans hc.hyp.Q_normal.1, hMN, hcomm⟩ (Z_le_plane u₁)
  have hcard : Nat.card (TM.plane u₁) ≤ Nat.card Z := Subgroup.card_le_of_le hle
  rw [card_plane hu₁] at hcard
  have h4 := hc.hyp.q4
  have h16 : 16 ≤ Nat.card Z * Nat.card Z := by nlinarith
  have h3 : Nat.card Z ^ 3 = Nat.card Z * (Nat.card Z * Nat.card Z) := by ring
  nlinarith

theorem linSetup_planes (hc : Ctx M Q Z B) (hCD : CentDvdN 2 M Q Z (Lgen M (LB M Q B)))
    {u₁ u₂ : Fin 2 → TM.F} (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hne : ∀ c : TM.F, u₂ ≠ c • u₁)
    (hperm : ∀ m ∈ M, conjSubgroup m (TM.plane u₁) = TM.plane u₁ ∨
      conjSubgroup m (TM.plane u₁) = TM.plane u₂) :
    LinSetup M Q Z B 2 (TM.plane u₁) (TM.plane u₂) := by
  exact ⟨TM.F, inferInstance, inferInstance, TM.card_F, TM.φ, TM.φ_range, TM.φ_ker,
    Z_le_plane u₁, plane_le_Q u₁, Z_le_plane u₂, plane_le_Q u₂, plane_inf_plane hu₁ hu₂ hne,
    plane_sup_plane hu₁ hu₂ hne,
    sectionAct_plane hu₁ (AddEquiv.refl _) (fun g => (g : Matrix (Fin 2) (Fin 2) TM.F))
      fun _ _ => rfl,
    sectionAct_plane hu₂ (dualCoord TM.F)
      (fun g => ((g⁻¹ : GL (Fin 2) TM.F) : Matrix (Fin 2) (Fin 2) TM.F)ᵀ)
      fun s n => dualCoord_mulVec _ (det_φ s) n,
    exists_conj_plane_eq hc hu₁ hperm, hCD⟩

end TensorModel

end Setup

end CFSG.RankThree.GF2n.Smith81

module

public import CFSG.Quasithin.H13.L32AL2k
public import CFSG.Quasithin.H13.L32AL2l

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V K W : Subgroup G} {t₀ : G}

namespace TopCtx

variable {X : TopCtx T L V K W t₀} [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]

section Data

variable {F : Type} [Field F] [Finite F] {π : TensorG2 F →* ↥(X.img (conjClosure K T))}
  {β : Hat V (A6.g1 T V) W ≃* TensorE2 F}

omit [Finite F] in
theorem IsModel.card_hat (Y : X.IsModel π β) : Nat.card (Hat V (A6.g1 T V) W) = 256 := by
  rw [Nat.card_congr β.toEquiv]
  show Nat.card (Multiplicative (Matrix (Fin 2) (Fin 2) F)) = 256
  rw [Nat.card_congr Multiplicative.toAdd]
  show Nat.card (Fin 2 → Fin 2 → F) = 256
  rw [Nat.card_fun, Nat.card_fun, Y.card, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

theorem IsModel.fpf (Y : X.IsModel π β) {P : Subgroup (MulAut (Hat V (A6.g1 T V) W))}
    (hP : P = leftImg π ∨ P = rightImg π) (hcard : Nat.card P = 60) :
    ∀ y ∈ P, y ≠ 1 → ∀ m : ℕ, Odd m → y ^ m = 1 → ∀ w, y w = w → w = 1 := by
  rcases hP with rfl | rfl
  · exact fun y hy hy1 m hm hym w hw => Y.fix_left hcard hy hy1 hm hym hw
  · exact fun y hy hy1 m hm hym w hw => Y.fix_right hcard hy hy1 hm hym hw

theorem IsModel.wrData (Y : X.IsModel π β) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (h76 : Lemma14_7_6) (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    WrData (X.img (A6.g1 T V)) (X.img K) (X.img (K.map (MulAut.conj t₀ : G →* G))) := by
  obtain ⟨φ⟩ := X.nonempty_equiv_img_K hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  obtain ⟨φ'⟩ := X.nonempty_equiv_img_Kt hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  have hc := (props_of_equiv φ).2.1
  have hc' := (props_of_equiv φ').2.1
  have hinj := X.actDot_injective hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  have hle : ∀ A : Subgroup G, X.img A ≤ X.img (A6.g1 T V) := fun A => by
    rintro _ ⟨k, -, rfl⟩
    exact ⟨k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  have hfac := Y.factors hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  have hP1 : X.img K = leftImg π ∨ X.img K = rightImg π := hfac.imp (fun h => h.1) (fun h => h.1)
  have hP2 : X.img (K.map (MulAut.conj t₀ : G →* G)) = leftImg π ∨
      X.img (K.map (MulAut.conj t₀ : G →* G)) = rightImg π :=
    hfac.symm.imp (fun h => h.2) (fun h => h.2)
  have hconj : ∀ (h : ↥(A6.g1 T V)) (A B : Subgroup G),
      (∀ a ∈ modO2Image (A6.g1 T V) A, QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) h * a *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) h)⁻¹ ∈ modO2Image (A6.g1 T V) B) →
      ∀ a ∈ X.img A, X.top.act h * a * (X.top.act h)⁻¹ ∈ X.img B := by
    intro h A B hAB a ha
    rw [img_eq_map] at ha ⊢
    obtain ⟨κ, hκ, rfl⟩ := ha
    exact ⟨_, hAB κ hκ, by rw [map_mul, map_mul, map_inv, actDot_mk]⟩
  refine
    { sq := X.top.sec_sq
      card := Y.card_hat
      iso₁ := ⟨φ⟩
      iso₂ := ⟨φ'⟩
      le₁ := hle K
      le₂ := hle _
      comm := fun a ha b hb => X.img_K_comm hA37 ha hb
      inf := X.img_K_inf hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
      fpf₁ := Y.fpf hP1 hc
      fpf₂ := Y.fpf hP2 hc'
      cases := ?_
      cent := ?_
      inner₁ := ?_
      inner₂ := ?_ }
  · rintro _ ⟨h, -, rfl⟩
    rcases L2.CtxL2.conj_cases X.C (QuotientGroup.mk' _ h) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hconj h _ _ h1, hconj h _ _ h2⟩
    · exact Or.inr ⟨hconj h _ _ h1, hconj h _ _ h2⟩
  · rintro _ ⟨b, -, rfl⟩ hc1 hc2
    have key : ∀ A : Subgroup G, (∀ a ∈ X.img A, X.top.act b * a = a * X.top.act b) →
        ∀ a ∈ modO2Image (A6.g1 T V) A, QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) b * a =
          a * QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)) b := by
      intro A hA a ha
      apply hinj
      rw [map_mul, map_mul, actDot_mk]
      exact hA _ (by rw [img_eq_map]; exact ⟨a, ha, rfl⟩)
    have h1 := eq_one_of_centralizes hA37 hA38 h76 h33 h36 hlist X.R X.C (key K hc1) (key _ hc2)
    rw [← X.actDot_mk b, h1, map_one]
  · intro f hf
    rcases hfac with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2] at hf
      rw [h1]
      exact Y.inner_left_of_right hf
    · rw [h2] at hf
      rw [h1]
      exact Y.inner_right_of_left hf
  · intro f hf
    rcases hfac with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hf
      rw [h2]
      exact Y.inner_right_of_left hf
    · rw [h1] at hf
      rw [h2]
      exact Y.inner_left_of_right hf

end Data

theorem card_img_lt_four (hD36 : D36) (hD37 : D37) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (h76 : Lemma14_7_6) (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (h29 : Thm14_7_29) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    {γ γ' : F8.Geom T L (A6.g1 T V)} {g : ↥((L ⊔ T) ⊔ A6.g1 T V)}
    (s : F8Setup T V L (A6.g1 T V) γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ V (A6.g1 T V) (g : G)) (F8.Dγ V (fsuV1 T V) (A6.g1 T V) (g : G)))
    (hle : mIdx (conjClosure V (A6.g1 T V)) (F8.DH V (fsuV1 T V) (A6.g1 T V) (g : G)) ≤
      mIdx (F8.Uγ V (A6.g1 T V) (g : G)) (F8.Dγ V (fsuV1 T V) (A6.g1 T V) (g : G))) :
    Nat.card (X.img (F8.Uγ V (A6.g1 T V) (g : G))) < 4 := by
  have hF := X.top.hF
  set U := conjClosure V (A6.g1 T V) with hU
  set Uγ := F8.Uγ V (A6.g1 T V) (g : G) with hUγ
  set A₁ := F8.A₁ (fsuV1 T V) (g : G) with hA₁
  set DH := F8.DH V (fsuV1 T V) (A6.g1 T V) (g : G) with hDH
  obtain ⟨F, _, _, π, β, Y⟩ :=
    X.exists_model hD36 hD37 hA37 hA38 h76 h33 h36 hlist h29 h1222 h1332 h1334
  have Wd := Y.wrData hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  have hB := (hF.F916_2_aux s hpos hle).1
  have hUγH : Uγ ≤ A6.g1 T V := hF.Uγ_le_H s
  have hA := X.isA2_img hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 hB
  obtain ⟨hAH, -, hAc, hA2⟩ := hA
  have hquad := X.quad_img hB
  rw [← isQuadratic_iff_commSeries_two] at hquad
  have hq : ∀ a ∈ X.img Uγ, ∀ b ∈ X.img Uγ, ∀ w : Hat V (A6.g1 T V) W,
      b (a w * w⁻¹) = a w * w⁻¹ := fun a ha b hb w =>
    hquad (Subgroup.subset_closure ⟨a, ha, w, rfl⟩) b hb
  by_contra h4
  push Not at h4
  set D : Subgroup (Hat V (A6.g1 T V) W) :=
    (DH.subgroupOf U).map (InternalSec.secMk (W.subgroupOf U)) with hD
  set Z : Subgroup (Hat V (A6.g1 T V) W) :=
    ((A₁ ⊓ U).subgroupOf U).map (InternalSec.secMk (W.subgroupOf U)) with hZ
  have hZ2 : Nat.card Z ≤ 2 := by
    have h1 : Nat.card Z ≤ Nat.card ((A₁ ⊓ U).subgroupOf U) :=
      Nat.card_le_card_of_surjective _
        (MonoidHom.subgroupMap_surjective (InternalSec.secMk (W.subgroupOf U)) _)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h1
    exact h1.trans ((Subgroup.card_le_of_le inf_le_left).trans hF.card_A₁.le)
  have hUp : IsPGroup 2 ↥U := F7.isPGroup_of_isElemAbelian hF.F911_3
  have hUγp : IsPGroup 2 ↥Uγ := F7.isPGroup_of_isElemAbelian hF.isElemAbelian_Uγ
  have hcard : Nat.card (X.img Uγ) =
      (F8.Dγ V (fsuV1 T V) (A6.g1 T V) (g : G)).relIndex Uγ := by
    rw [X.card_img hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 hUγH, hF.Dγ_eq_inf_pCoreOf s]
  have hDidx : D.index ≤ Nat.card (X.img Uγ) := by
    have h1 : D.index ≤ (DH.subgroupOf U).index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_map_dvd _ (InternalSec.secMk_surjective _))
    have h2 : (DH.subgroupOf U).index = 2 ^ mIdx U DH := HypF98.relIndex_eq_two_pow_mIdx hUp
    rw [hcard, HypF98.relIndex_eq_two_pow_mIdx hUγp]
    exact h1.trans (h2.trans_le (Nat.pow_le_pow_right (by norm_num) hle))
  have hDZ : ∀ d ∈ D, ∀ a ∈ X.img Uγ, a d * d⁻¹ ∈ Z := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨x, hx, rfl⟩
    have hu' : (u : G) ∈ DH := hu
    have hx' : (x : G) ∈ Uγ := hx
    have hc := (mem_centralizerMod.mp hu').2.2 (x : G) hx'
    refine ⟨Setup.rho U (A6.g1 T V) (le_normalizer_conjClosure V (A6.g1 T V)) x u * u⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.mpr ⟨?_, (Setup.rho U (A6.g1 T V)
        (le_normalizer_conjClosure V (A6.g1 T V)) x u * u⁻¹).2⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
      have := inv_mem hc
      rwa [show ((u : G) * x * (u : G)⁻¹ * (x : G)⁻¹)⁻¹ = (x : G) * u * (x : G)⁻¹ * (u : G)⁻¹ by
        group] at this
    · rw [map_mul, map_inv, X.top.act_secMk]
  exact Wd.false_of_offender hAH hAc (fun a ha => by rw [← pow_two]; exact hA2 a ha) hq h4 hZ2
    hDidx hDZ

end TopCtx

end CFSG.Quasithin.H13.L32A.L2

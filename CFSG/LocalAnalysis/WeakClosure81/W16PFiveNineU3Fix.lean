module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankU3
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUSUGen
public import CFSG.LocalAnalysis.WeakClosure81.ThirteenTwo
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveIb

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

theorem isPSUGp_quotient_center_of_surjective {X Q : Type} [Group X] [Group Q] {θ : X →* Q}
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center X) {n : ℕ}
    (hX : IsPSUGp (X ⧸ Subgroup.center X) 3 n) : IsPSUGp (Q ⧸ Subgroup.center Q) 3 n := by
  have hZquot : Subgroup.center (X ⧸ Subgroup.center X) = ⊥ := by
    obtain ⟨hsimple, hperfect⟩ := isSimpleGroup_isPerfect_of_isPSUGp_three hX
    haveI := hsimple
    haveI := hperfect
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (X ⧸ Subgroup.center X)) with h | h
    · exact h
    · exfalso
      haveI : IsMulCommutative (X ⧸ Subgroup.center X) := Subgroup.center_eq_top_iff.mp h
      exact Group.IsPerfect.not_isMulCommutative (X ⧸ Subgroup.center X) inferInstance
  have hZ : Subgroup.center Q = (Subgroup.center X).map θ := by
    refine le_antisymm ?_ (Subgroup.map_center_le_center hθ)
    intro q hq
    obtain ⟨x, rfl⟩ := hθ q
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    have hq' : ∀ g, g * θ x = θ x * g := Subgroup.mem_center_iff.mp hq
    have hxcent : (QuotientGroup.mk x : X ⧸ Subgroup.center X) ∈
        Subgroup.center (X ⧸ Subgroup.center X) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) z
      change ((y : X ⧸ Subgroup.center X) * (x : X ⧸ Subgroup.center X) =
        (x : X ⧸ Subgroup.center X) * (y : X ⧸ Subgroup.center X))
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
      apply hker
      rw [MonoidHom.mem_ker]
      simp only [map_div, map_mul]
      rw [hq' (θ y)]
      simp
    have hx1 : (QuotientGroup.mk x : X ⧸ Subgroup.center X) = 1 := by
      rw [hZquot] at hxcent
      exact Subgroup.mem_bot.mp hxcent
    exact (QuotientGroup.eq_one_iff x).mp hx1
  exact CFSG.Blueprint.LieModel.of_mulEquiv
    (CFSG.LieType.CurtisTits.centerQuotientEquivOfSurjective θ hθ hker hZ) hX

theorem Cex16.map_centralizer_iSub16_le_center (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hF : Fam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G))
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ) {n : ℕ}
    (hcase : commutator X = ⊤ ∧ IsPSUGp (X ⧸ Subgroup.center X) 3 n) :
    ∀ c : ↥(conjClosure V H), (c : G) ∈ centralizer (iSub16 V H : Set G) →
      φ c ∈ Subgroup.center X := by
  classical
  have hVH : V ≤ H := h.V_le_S.trans hF.1
  have hKH : conjClosure V H ≤ H :=
    conjClosure_le fun k hk z hz => H.mul_mem (H.mul_mem hk (hVH hz)) (H.inv_mem hk)
  have hHnorm : H ≤ Subgroup.normalizer (iSub16 V H : Set G) :=
    le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
  have hKI : conjClosure V H ≤ Subgroup.normalizer (iSub16 V H : Set G) :=
    hKH.trans hHnorm
  have hKcent : conjClosure V H ≤
      Subgroup.normalizer (Subgroup.centralizer (iSub16 V H : Set G)) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      refine Subgroup.mem_centralizer_iff.mpr fun i hi => ?_
      have hxi : (k⁻¹ * i * k) * x = x * (k⁻¹ * i * k) :=
        Subgroup.mem_centralizer_iff.mp hx _
          ((Subgroup.mem_normalizer_iff''.mp (hKI hk) i).mp hi)
      calc i * (k * x * k⁻¹) = k * ((k⁻¹ * i * k) * x) * k⁻¹ := by group
        _ = k * (x * (k⁻¹ * i * k)) * k⁻¹ := by rw [hxi]
        _ = (k * x * k⁻¹) * i := by group
    · intro hx
      refine Subgroup.mem_centralizer_iff.mpr fun i hi => ?_
      have hxi : (k * i * k⁻¹) * (k * x * k⁻¹) = (k * x * k⁻¹) * (k * i * k⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hx _
          ((Subgroup.mem_normalizer_iff.mp (hKI hk) i).mp hi)
      calc i * x = k⁻¹ * ((k * i * k⁻¹) * (k * x * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * x * k⁻¹) * (k * i * k⁻¹)) * k := by rw [hxi]
        _ = x * i := by group
  let N : Subgroup X :=
    ((Subgroup.centralizer (iSub16 V H : Set G)).subgroupOf (conjClosure V H)).map φ
  have hNnormal : N.Normal :=
    Subgroup.Normal.map
      (Subgroup.normal_subgroupOf_of_le_normalizer hKcent) φ hφ.surjective
  haveI : N.Normal := hNnormal
  have hXsimple : IsSimpleGroup (X ⧸ Subgroup.center X) :=
    (isSimpleGroup_isPerfect_of_isPSUGp_three hcase.2).1
  rcases CFSG.StandardType.GGOppRadSpU.le_center_or_eq_top_of_perfect hcase.1 hXsimple N with
    hNle | hNtop
  · intro c hc
    refine hNle (Subgroup.mem_map.mpr ⟨c, ?_, rfl⟩)
    exact hc
  · exfalso
    have hVleC : V ≤ Subgroup.centralizer (iSub16 V H : Set G) := by
      intro v hv
      have hvK : v ∈ conjClosure V H := le_conjClosure V H hv
      have hφv : φ ⟨v, hvK⟩ ∈ N := by rw [hNtop]; exact Subgroup.mem_top _
      obtain ⟨c, hc, hcc⟩ := Subgroup.mem_map.mp hφv
      have hker : c⁻¹ * ⟨v, hvK⟩ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hcc, inv_mul_cancel]
      have hO : ((c⁻¹ * ⟨v, hvK⟩ : ↥(conjClosure V H)) : G) ∈
          pCoreOf 2 (conjClosure V H) := (hφ.ker_iff _).mp hker
      have hc1 : (c : G) ∈ Subgroup.centralizer (iSub16 V H : Set G) := hc
      have hc2 : ((c⁻¹ * ⟨v, hvK⟩ : ↥(conjClosure V H)) : G) ∈
          Subgroup.centralizer (iSub16 V H : Set G) := hQ hO
      have heq : (c : G) * (((c⁻¹ * ⟨v, hvK⟩ : ↥(conjClosure V H))) : G) = v := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [← heq]
      exact Subgroup.mul_mem _ hc1 hc2
    have hVsub : V ≤ V ⊓ pCoreOf 2 H := by
      calc V ≤ V ⊓ Subgroup.centralizer (iSub16 V H : Set G) := le_inf le_rfl hVleC
        _ = U ⊔ V₀ := h.inf_centralizer_iSub16_eq h1 h5 hS hF hV
        _ = V ⊓ pCoreOf 2 H := (h.inf_pCoreOf_eq h1 h5 hS hF hV).symm
    exact hV (hVsub.trans inf_le_right)

theorem Cex16.isPSUGp_img_conjClosure (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hF : Fam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G))
    (D : ModDataE H (iSub16 V H)) {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ) {n : ℕ}
    (hcase : commutator X = ⊤ ∧ IsPSUGp (X ⧸ Subgroup.center X) 3 n) :
    IsPSUGp (↥(D.img (conjClosure V H)) ⧸ Subgroup.center ↥(D.img (conjClosure V H))) 3 n := by
  classical
  have hVH : V ≤ H := h.V_le_S.trans hF.1
  have hKH : conjClosure V H ≤ H :=
    conjClosure_le fun k hk z hz => H.mul_mem (H.mul_mem hk (hVH hz)) (H.inv_mem hk)
  let ρK : ↥(conjClosure V H) →* LGL 2 D.W := D.ρ.comp (Subgroup.inclusion hKH)
  have hmem_img : ∀ x : ↥(conjClosure V H), ρK x ∈ D.img (conjClosure V H) := by
    intro x
    rw [D.mem_img]
    exact ⟨⟨(x : G), hKH x.2⟩, x.2, rfl⟩
  let ρQ : ↥(conjClosure V H) →* ↥(D.img (conjClosure V H)) :=
    ρK.codRestrict (D.img (conjClosure V H)) hmem_img
  have hρQ_surj : Function.Surjective ρQ := by
    intro y
    obtain ⟨j, hj, hjρ⟩ := (D.mem_img (S := conjClosure V H)).mp y.2
    refine ⟨⟨j, hj⟩, ?_⟩
    apply Subtype.ext
    change D.ρ j = (y : LGL 2 D.W)
    exact hjρ
  have hker_le : φ.ker ≤ ρQ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    apply Subtype.ext
    change D.ρ ⟨(k : G), hKH k.2⟩ = 1
    exact (D.ρ_eq_one_iff ⟨(k : G), hKH k.2⟩).mpr (hQ ((hφ.ker_iff k).mp hk))
  let θ : X →* ↥(D.img (conjClosure V H)) :=
    (MonoidHom.liftOfSurjective φ hφ.surjective) ⟨ρQ, hker_le⟩
  have hθφ : θ.comp φ = ρQ := by
    simpa [θ, MonoidHom.liftOfSurjective] using
      MonoidHom.liftOfRightInverse_comp (f := φ) (f_inv := Function.surjInv hφ.surjective)
        (Function.rightInverse_surjInv hφ.surjective) ⟨ρQ, hker_le⟩
  have hθ_surj : Function.Surjective θ := by
    intro y
    obtain ⟨k, hk⟩ := hρQ_surj y
    refine ⟨φ k, ?_⟩
    change (θ.comp φ) k = y
    rw [hθφ]
    exact hk
  have hker_θ : θ.ker ≤ Subgroup.center X := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    obtain ⟨k, rfl⟩ := hφ.surjective y
    have hk : k ∈ ρQ.ker := by
      rw [MonoidHom.mem_ker]
      rw [← hθφ]
      exact hy
    rw [MonoidHom.mem_ker] at hk
    have hC : (k : G) ∈ centralizer (iSub16 V H : Set G) := by
      have hρ : D.ρ ⟨(k : G), hKH k.2⟩ = 1 := by
        have h1 := congrArg Subtype.val hk
        change ρK k = 1 at h1
        change D.ρ ⟨(k : G), hKH k.2⟩ = 1 at h1
        exact h1
      exact (D.ρ_eq_one_iff ⟨(k : G), hKH k.2⟩).mp hρ
    exact Cex16.map_centralizer_iSub16_le_center h1 h5 hS h hF hV hQ hφ hcase k hC
  exact isPSUGp_quotient_center_of_surjective hθ_surj hker_θ hcase.2

theorem Cex16.rk_barSub_UAOf_img (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G))
    (D : ModDataE H (iSub16 V H)) {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ) {n : ℕ}
    (hn : Nat.card ↥(SevenK.barSub (conjClosure V H) φ V) = 2 ^ n)
    {ψ : ↥(kSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
      (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)))
      →* ↥(D.img (conjClosure V H))}
    (hψ : ∀ k, ((ψ k : ↥(D.img (conjClosure V H))) : LGL 2 D.W) = projG (D.img H) k) :
    rk ↥(SevenK.barSub (kSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
      (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H))) ψ
      (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))) = n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hKH : conjClosure V H ≤ H :=
    conjClosure_le fun k hk z hz => H.mul_mem (H.mul_mem hk (hVH hz)) (H.inv_mem hk)
  have h131 := Cex16.assumption131_iSub16 h1 h5 hS h hH.1 hV D
  have hrank := Cex16.mRank_le_iSub16 h hH.1 D
  have hA : D.img V ∈ D.conjImgFam V := ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩
  have htrans : ∀ B ∈ D.conjImgFam V, ∀ C ∈ D.conjImgFam V,
      ∃ g ∈ D.img H, C = cj g B := by
    rintro B ⟨x, hxH, rfl⟩ C ⟨y, hyH, rfl⟩
    refine ⟨D.ρ ⟨y⁻¹ * x, H.mul_mem (H.inv_mem hyH) hxH⟩, ?_, ?_⟩
    · exact ⟨⟨y⁻¹ * x, H.mul_mem (H.inv_mem hyH) hxH⟩,
        H.mul_mem (H.inv_mem hyH) hxH, rfl⟩
    · have hconj : conjSubgroup V x ≤ H := by
        intro z hz
        have h1 : x * z * x⁻¹ ∈ H := hVH (mem_conjSubgroup_iff.mp hz)
        rw [show z = x⁻¹ * (x * z * x⁻¹) * x by group]
        exact H.mul_mem (H.mul_mem (H.inv_mem hxH) h1) hxH
      have hxj := D.img_conj (A := conjSubgroup V x) hconj
        (⟨y⁻¹ * x, H.mul_mem (H.inv_mem hyH) hxH⟩ : ↥H)
      have hexp : conjSubgroup (conjSubgroup V x) (y⁻¹ * x)⁻¹ = conjSubgroup V y := by
        rw [mul_inv_rev, inv_inv, conjSubgroup_conjSubgroup]
        congr 1
        group
      rw [hexp] at hxj
      exact hxj.symm
  have hΩ := (thirteen_two_three h131 hrank htrans hA).1
  have hU'Ω : UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V) ∈
      omegaSet (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
        (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)) := by
    rw [hΩ]
    exact ⟨D.img V, hA, rfl⟩
  have hU'K : UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V) ≤
      kSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
        (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)) := le_kSub hU'Ω
  have hmap : (SevenK.barSub
        (kSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
          (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H))) ψ
        (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))).map
      (Subgroup.subtype (D.img (conjClosure V H))) = D.img V := by
    unfold SevenK.barSub
    rw [Subgroup.map_map]
    have e : (Subgroup.subtype (D.img (conjClosure V H))).comp ψ =
        (projG (D.img H)).comp
          (Subgroup.subtype (kSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
            (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)))) :=
      MonoidHom.ext fun k => hψ k
    rw [e, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hU'K]
    exact map_projG_wHat_sup_aHat (D.img_mono hVH)
  have hIleO : iSub16 V H ≤ pCoreOf 2 (conjClosure V H) := by
    have hKI : conjClosure V H ≤ Subgroup.normalizer (iSub16 V H : Set G) :=
      hKH.trans (le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H)
    have hIK : iSub16 V H ≤ conjClosure V H := conjClosure_mono inf_le_left le_rfl
    have hInorm : ((iSub16 V H).subgroupOf (conjClosure V H)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hKI
    have hIpg : IsPGroup 2 (iSub16 V H) :=
      CFSG.Open.IsElemAbelian.isPGroup (Cex16.isElemAbelian_iSub16 h1 hS h hH.1)
    exact le_pCoreOf_of_isPGroup_of_normal hIK hInorm hIpg
  have hinf : V ⊓ pCoreOf 2 (conjClosure V H) = V ⊓ centralizer (iSub16 V H : Set G) := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, hQ hx.2⟩
    · calc V ⊓ centralizer (iSub16 V H : Set G) = U ⊔ V₀ :=
            h.inf_centralizer_iSub16_eq h1 h5 hS hH.1 hV
        _ = V ⊓ iSub16 V H := (h.inf_iSub16_eq h1 h5 hS hH.1 hV).symm
        _ ≤ V ⊓ pCoreOf 2 (conjClosure V H) := le_inf inf_le_left (inf_le_right.trans hIleO)
  have hcard : Nat.card ↥(D.img V) = 2 ^ n := by
    have hcard1 : Nat.card ↥(D.img V) = (centralizer (iSub16 V H : Set G)).relIndex V :=
      D.card_img hVH
    have hcard2 : Nat.card ↥(SevenK.barSub (conjClosure V H) φ V) =
        (pCoreOf 2 (conjClosure V H)).relIndex V :=
      card_barSub_eq_relIndex_of_isBarMap (le_conjClosure V H)
        (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hφ
    have hrel : (pCoreOf 2 (conjClosure V H)).relIndex V =
        (centralizer (iSub16 V H : Set G)).relIndex V := by
      rw [← Subgroup.inf_relIndex_right (pCoreOf 2 (conjClosure V H)) V,
        ← Subgroup.inf_relIndex_right (centralizer (iSub16 V H : Set G)) V,
        inf_comm (pCoreOf 2 (conjClosure V H)) V,
        inf_comm (centralizer (iSub16 V H : Set G)) V, hinf]
    calc Nat.card ↥(D.img V) = (centralizer (iSub16 V H : Set G)).relIndex V := hcard1
      _ = (pCoreOf 2 (conjClosure V H)).relIndex V := hrel.symm
      _ = Nat.card ↥(SevenK.barSub (conjClosure V H) φ V) := hcard2.symm
      _ = 2 ^ n := hn
  have hcard_bar : Nat.card ↥(SevenK.barSub
        (kSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
          (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H))) ψ
        (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))) = Nat.card ↥(D.img V) := by
    rw [← Subgroup.card_map_of_injective
      (Subgroup.subtype_injective (D.img (conjClosure V H))), hmap]
  rw [show rk ↥(SevenK.barSub
        (kSub (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))
          (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H))) ψ
        (UAOf (D.img H) (D.conjImgSpace V₀ V) (D.img V))) = rk ↥(D.img V) by
      unfold rk
      rw [hcard_bar]]
  unfold rk
  rw [hcard, padicValNat.prime_pow]

end CFSG.LocalAnalysis.WeakClosure81

end

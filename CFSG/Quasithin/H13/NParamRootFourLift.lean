module

public import CFSG.Quasithin.H13.NParamLiftS5
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.E1.LiftS5

open CFSG.Open Equiv CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

@[expose] def RootFourLift (H T : Subgroup G) (ψ : ↥H →* Perm (Fin 5)) : Prop :=
  ∃ A : Subgroup G, A ≤ T ∧ IsElemAbelian 2 A ∧
    (A.subgroupOf H).map ψ ≤ alternatingGroup (Fin 5) ∧ Nat.card ↥((A.subgroupOf H).map ψ) = 4

theorem one_lt_nParam_of_rootFourLift {H T : Subgroup G} {ψ : ↥H →* Perm (Fin 5)}
    (hA5 : alternatingGroup (Fin 5) ≤ ψ.range) (hT : IsSylowIn 2 T H)
    (h : RootFourLift H T ψ) : 1 < E1.nParam H := by
  obtain ⟨A, hAT, hA, hψA, hψA4⟩ := h
  exact one_lt_nParam_of_lift ψ hA5 hT hAT hA hψA hψA4

@[expose] noncomputable def autAltFive : Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num))

theorem autAltFive_apply (σ : Perm (Fin 5)) : autAltFive σ = MulAut.conjNormal σ := rfl

@[expose] noncomputable def quotAut (K : Subgroup G) :
    MulAut ↥K →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) where
  toFun α := QuotientGroup.congr _ _ α
    (Subgroup.characteristic_iff_map_eq.mp inferInstance α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

@[expose] noncomputable def quotConj (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
  (quotAut K).comp K.normalizerMonoidHom

omit [Finite G] in
theorem quotConj_of_mem (K : Subgroup G) (g : ↥(Subgroup.normalizer (K : Set G)))
    (hg : (g : G) ∈ K) :
    quotConj K g = MulAut.conj (QuotientGroup.mk ⟨g, hg⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    exact Subgroup.normalizerMonoidHom_apply_apply_coe K g k

@[expose] noncomputable def quotPerm {H K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) : ↥H →* Perm (Fin 5) :=
  autAltFive.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp ((quotConj K).comp (Subgroup.inclusion hHK)))

omit [Finite G] in
theorem quotPerm_of_mem {H K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) (h : ↥H) (hk : (h : G) ∈ K) :
    quotPerm hHK e h = ((e (QuotientGroup.mk ⟨h, hk⟩) : alternatingGroup (Fin 5)) :
      Perm (Fin 5)) := by
  have hk' : ((Subgroup.inclusion hHK h : ↥(Subgroup.normalizer (K : Set G))) : G) ∈ K := by
    simpa using hk
  have he : (⟨_, hk'⟩ : ↥K) = ⟨h, hk⟩ := Subtype.ext (by simp)
  apply autAltFive.injective
  have h1 : autAltFive (quotPerm hHK e h) =
      MulAut.congr e (quotConj K (Subgroup.inclusion hHK h)) := by
    simp only [quotPerm, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rw [h1, quotConj_of_mem K _ hk', he]
  refine MulEquiv.ext fun a => Subtype.ext ?_
  rw [autAltFive_apply, MulAut.conjNormal_apply]
  simp [MulAut.congr_apply, MulAut.conj_apply]

omit [Finite G] in
theorem alt_le_range_quotPerm {H K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hKH : K ≤ H) (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) :
    alternatingGroup (Fin 5) ≤ (quotPerm hHK e).range := by
  intro σ hσ
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm ⟨σ, hσ⟩)
  refine ⟨⟨k, hKH k.2⟩, ?_⟩
  rw [quotPerm_of_mem hHK e _ k.2]
  have : (QuotientGroup.mk ⟨(k : G), k.2⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) = e.symm ⟨σ, hσ⟩ := hk
  rw [this, MulEquiv.apply_symm_apply]

@[expose] def RootFourLiftQuot (T K : Subgroup G) : Prop :=
  ∃ A : Subgroup G, A ≤ T ∧ A ≤ K ∧ IsElemAbelian 2 A ∧
    Nat.card ↥((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) = 4

omit [Finite G] in
theorem rootFourLift_of_quot {H T K : Subgroup G} (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hKH : K ≤ H) (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))
    (h : RootFourLiftQuot T K) : RootFourLift H T (quotPerm hHK e) := by
  obtain ⟨A, hAT, hAK, hA, h4⟩ := h
  set j : (↥K ⧸ CFSG.pCore 2 ↥K) →* Perm (Fin 5) :=
    (alternatingGroup (Fin 5)).subtype.comp e.toMonoidHom with hj
  have hjinj : Function.Injective j := fun x y hxy =>
    e.injective (Subtype.ext (by simpa [hj] using hxy))
  have himg : (A.subgroupOf H).map (quotPerm hHK e) =
      ((A.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map j := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyK : (y : G) ∈ K := hAK hy
      refine ⟨QuotientGroup.mk ⟨y, hyK⟩, ⟨⟨y, hyK⟩, hy, rfl⟩, ?_⟩
      rw [quotPerm_of_mem hHK e y hyK]
      rfl
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨⟨y, hKH y.2⟩, hy, ?_⟩
      rw [quotPerm_of_mem hHK e _ y.2]
      rfl
  refine ⟨A, hAT, hA, ?_, ?_⟩
  · rw [himg]
    rintro _ ⟨x, -, rfl⟩
    exact (e x).2
  · rw [himg, Subgroup.card_map_of_injective hjinj, h4]

theorem one_lt_nParam_of_rootFourLiftQuot {H T K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hKH : K ≤ H)
    (hA5 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hT : IsSylowIn 2 T H) (h : RootFourLiftQuot T K) : 1 < E1.nParam H := by
  obtain ⟨e⟩ := hA5
  exact one_lt_nParam_of_rootFourLift (alt_le_range_quotPerm hHK hKH e) hT
    (rootFourLift_of_quot hHK hKH e h)

open E1 A1b

omit [Finite G] in
theorem le_of_isE {i : ℕ} {H T A K : Subgroup G} (hAT : A ≤ T) (hAH : A ≤ H)
    (hA : IsElemAbelian 2 A) (hK : IsE i H T A K) : A ≤ K := by
  intro a ha
  refine (hK.2.1 ⟨hAT ha, LieType.BorelTits.le_normalizer_pCoreOf 2 H (hAH ha),
    fun b hb => ?_⟩).2
  have hab : a * b = b * a := congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  rw [commutatorElement_def, hab]
  simp

theorem one_lt_nParam_of_le {H T Y : Subgroup G} {Ω : Set (Subgroup G)}
    (hT : IsSylowIn 2 T H) (hΩ : IsInvColl H Ω)
    (hE : ∀ A' ∈ Ω, A' ≤ T → ∀ K, IsE 1 H T A' K → K ≤ Y)
    (hN : H ⊓ Subgroup.normalizer (weakClosure T Ω : Set G) ≤ Y) (hHY : ¬ H ≤ Y) :
    1 < nParam H := by
  rw [← not_le]
  intro hle
  have hInE : InE 1 H := (nParam_le_iff (n := 1) one_pos).1 (by exact_mod_cast hle)
  apply hHY
  rw [← hInE T hT Ω hΩ]
  refine sup_le ?_ hN
  exact iSup₂_le fun A' hA' => iSup_le fun hA'T => iSup₂_le fun K hK => hE A' hA' hA'T K hK

theorem card_map_dvd_card_map_mk {K Q : Type*} [Group K] [Group Q] (φ : K →* Q) (N : Subgroup K)
    [N.Normal] (hN : N ≤ φ.ker) (B : Subgroup K) :
    Nat.card ↥(B.map φ) ∣ Nat.card ↥(B.map (QuotientGroup.mk' N)) := by
  have hcomp : (QuotientGroup.lift N φ hN).comp (QuotientGroup.mk' N) = φ := by
    ext x; simp
  have h1 : (B.map (QuotientGroup.mk' N)).map (QuotientGroup.lift N φ hN) = B.map φ := by
    rw [Subgroup.map_map, hcomp]
  rw [← h1]
  exact Subgroup.card_map_dvd (H := B.map (QuotientGroup.mk' N)) (QuotientGroup.lift N φ hN)

theorem card_map_le_two_of_isE {H T A K : Subgroup G} {Q : Type*} [Group Q] (φ : ↥K →* Q)
    (hφ : ∀ N : Subgroup ↥K, N.Normal → Group.IsSolvable ↥N → N ≤ φ.ker)
    (hK : IsE 1 H T A K) : Nat.card ↥((A.subgroupOf K).map φ) ≤ 2 := by
  rcases hK.2.2.2 with ⟨-, h2⟩ | ⟨-, h2⟩
  · have hnil : Group.IsNilpotent ↥(CFSG.Open.pCore 2 ↥K) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2).isNilpotent
    have hO : CFSG.Open.pCore 2 ↥K ≤ φ.ker :=
      hφ _ (CFSG.LieType.BorelTits.pCore_normal 2) inferInstance
    have h := card_map_dvd_card_map_mk φ _ hO (A.subgroupOf K)
    unfold barO2 at h2
    exact (Nat.le_of_dvd Nat.card_pos h).trans (h2.trans_eq (pow_one 2))
  · have hO : CFSG.solvableRadical ↥K ≤ φ.ker :=
      hφ _ ABGLocalTools.solvableRadical_normal ABGLocalTools.solvableRadical_isSolvable
    have : (CFSG.solvableRadical ↥K).Normal := ABGLocalTools.solvableRadical_normal
    have h := card_map_dvd_card_map_mk φ _ hO (A.subgroupOf K)
    unfold barRad at h2
    exact (Nat.le_of_dvd Nat.card_pos h).trans (h2.trans_eq (pow_one 2))

omit [Finite G] in
theorem map_subgroupOf_inclusion {H K A : Subgroup G} {Q : Type*} [Group Q] (φ : ↥H →* Q)
    (hKH : K ≤ H) (hAK : A ≤ K) :
    (A.subgroupOf K).map (φ.comp (Subgroup.inclusion hKH)) = (A.subgroupOf H).map φ := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.comp_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Subgroup.inclusion hKH y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨(y : G), hAK hy⟩, hy, rfl⟩

theorem one_lt_nParam_of_map {H T : Subgroup G} {Ω : Set (Subgroup G)} {Q : Type*} [Group Q]
    (φ : ↥H →* Q) (Y₀ : Subgroup Q) (hT : IsSylowIn 2 T H) (hΩ : IsInvColl H Ω)
    (hlift : ∀ A' ∈ Ω, A' ≤ T → 2 < Nat.card ↥((A'.subgroupOf H).map φ))
    (hkill : ∀ A' ∈ Ω, A' ≤ T → ∀ (K : Subgroup G) (hKH : K ≤ H), A' ≤ K →
      ¬ (K.subgroupOf H).map φ ≤ Y₀ → ∀ N : Subgroup ↥K, N.Normal → Group.IsSolvable ↥N →
        N ≤ (φ.comp (Subgroup.inclusion hKH)).ker)
    (hN : ((H ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)).subgroupOf H).map φ ≤ Y₀)
    (hH : ¬ φ.range ≤ Y₀) : 1 < nParam H := by
  refine one_lt_nParam_of_le (Y := (Y₀.comap φ).map H.subtype) hT hΩ ?_ ?_ ?_
  · intro A' hA' hA'T K hK
    have hKH : K ≤ H := hK.1
    have hA'K : A' ≤ K := le_of_isE hA'T (hΩ.le A' hA') (hΩ.isElemAbelian A' hA') hK
    by_contra hKY
    have hKY' : ¬ (K.subgroupOf H).map φ ≤ Y₀ := by
      intro h
      apply hKY
      intro x hx
      exact ⟨⟨x, hKH hx⟩, h ⟨⟨x, hKH hx⟩, hx, rfl⟩, rfl⟩
    have h2 := card_map_le_two_of_isE _ (hkill A' hA' hA'T K hKH hA'K hKY') hK
    rw [map_subgroupOf_inclusion φ hKH hA'K] at h2
    have := hlift A' hA' hA'T
    omega
  · rintro x ⟨hxH, hxN⟩
    exact ⟨⟨x, hxH⟩, hN ⟨⟨x, hxH⟩, ⟨hxH, hxN⟩, rfl⟩, rfl⟩
  · intro hHY
    apply hH
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hHY y.2
    have : z = y := Subtype.ext hzy
    rw [← this]
    exact hz

end CFSG.Quasithin.E1.LiftS5

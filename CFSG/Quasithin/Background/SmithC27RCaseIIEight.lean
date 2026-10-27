module

public import CFSG.Quasithin.Background.SmithC27RCaseIICover8
public import CFSG.Quasithin.Background.SmithC27RCaseIIStd8
public import CFSG.Quasithin.Background.SmithC27RCaseIITrans

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

theorem mem_normalizer_of_forall_conj_mem {Γ : Type*} [Group Γ] [Finite Γ] {Z : Subgroup Γ}
    {s : Γ} (h : ∀ z ∈ Z, s * z * s⁻¹ ∈ Z) : s ∈ Subgroup.normalizer (Z : Set Γ) := by
  have hle : Z.map (MulAut.conj s).toMonoidHom ≤ Z := by
    rintro _ ⟨z, hz, rfl⟩
    exact h z hz
  have heq : Z.map (MulAut.conj s).toMonoidHom = Z := Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (f := (MulAut.conj s).toMonoidHom)
      (MulAut.conj s).injective).symm.le
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨h g, fun hg => ?_⟩
  rw [← heq] at hg
  obtain ⟨g', hg', e⟩ := hg
  have e' : s * g' * s⁻¹ = s * g * s⁻¹ := e
  rwa [← mul_left_cancel (mul_right_cancel e')]

theorem sylow_eq_of_le_of_isPGroup {Γ : Type*} [Group Γ] [Finite Γ] {S X Y : Subgroup Γ}
    (hS : IsSylowTwoOf S Y) (hSX : S ≤ X) (hXY : X ≤ Y) (hX : IsPGroup 2 X) : X = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := Subgroup.relIndex_mul_relIndex S X Y hSX hXY
  obtain ⟨k, hk⟩ := hX.index (S.subgroupOf X)
  have hk' : S.relIndex X = 2 ^ k := hk
  have hodd : ¬ 2 ∣ S.relIndex Y := hS.2.2
  have hk0 : k = 0 := by
    by_contra hk0
    apply hodd
    rw [← e, hk']
    exact Dvd.dvd.mul_right (dvd_pow_self 2 hk0) _
  rw [hk0, pow_zero] at hk'
  exact le_antisymm (Subgroup.relIndex_eq_one.1 hk') hSX

theorem isPGroup_P8 : IsPGroup 2 Claim2526.P8 :=
  IsPGroup.of_card (n := 7) (by rw [Claim2526.card_P8]; norm_num)

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G}

theorem three_of_caseII_eight_sylow (h : Hyp27 H R M K) (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (C : CaseIICtx R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) 8)
    {T : Subgroup (Perm (Fin 8))} (hT : IsSylowTwoOf T ⊤)
    (hTN : T ≤ Subgroup.normalizer (C.bar R : Set (Perm (Fin 8)))) :
    C27Three H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) := by
  have hs := h.starHyp
  obtain ⟨T', hT', hT'R⟩ := C.exists_sylow_star_of_bar hT hTN
  obtain ⟨e⟩ := C.nonempty_equivK
  have hP := isParabolic2_MK_of_sylow h hs hT' hT'R (C.self_normalizing_K (Or.inr rfl))
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))
  have eSL : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) ≃* GL (Fin 4) (ZMod 2) :=
    (MulEquiv.subgroupCongr (CFSG.GH74.Exceptional.statedSL_eq_top_of_card_two
      (Nat.card_zmod 2) 4)).trans Subgroup.topEquiv
  exact ⟨Or.inl ⟨e.trans (CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.trans eSL.symm)⟩,
    hP, not_isBorelIn_MK h hs hnS⟩

section Act

variable {V : Subgroup G} {n : ℕ}

namespace CaseIICtx

variable (C : CaseIICtx R K V n)

@[expose] noncomputable def actI : Perm (Fin n) →* MulAut (IntMod V C.hV) :=
  (autOn (K ⊔ R) V).subtype.comp C.ι.symm.toMonoidHom

omit [Finite G] in
theorem actI_val {σ : Perm (Fin n)} {x : G} {hxN : x ∈ Subgroup.normalizer (V : Set G)}
    (hx : C.actI σ = convI C.hV ⟨x, hxN⟩) (u : IntMod V C.hV) :
    (C.actI σ u).val = x * u.val * x⁻¹ := by
  rw [hx, convI_apply_val]

omit [Finite G] in
theorem exists_of_mem_bar {Y : Subgroup G} {σ : Perm (Fin n)} (hσ : σ ∈ C.bar Y) :
    ∃ y ∈ Y, ∃ hyN : y ∈ Subgroup.normalizer (V : Set G), C.actI σ = convI C.hV ⟨y, hyN⟩ := by
  rw [mem_bar_iff] at hσ
  obtain ⟨⟨y, hyN⟩, hyY, hye⟩ := (mem_autI C.hV).1 hσ
  exact ⟨y, hyY, hyN, hye.symm⟩

omit [Finite G] in
theorem exists_mem_bar (hs : StarHyp R K V) {Y : Subgroup G} (hYX : Y ≤ K ⊔ R) {y : G}
    (hy : y ∈ Y) : ∃ σ ∈ C.bar Y, ∀ u : IntMod V C.hV, (C.actI σ u).val = y * u.val * y⁻¹ := by
  have hyN : y ∈ Subgroup.normalizer (V : Set G) := hs.le_normalizer_V (hYX hy)
  let x : ↥(autOn (K ⊔ R) V) := ⟨convI C.hV ⟨y, hyN⟩, convI_mem_autI C.hV (hYX hy) hyN⟩
  have hx : C.actI (C.ι x) = convI C.hV ⟨y, hyN⟩ := by
    show (((C.ι.symm (C.ι x) : ↥(autOn (K ⊔ R) V)) : MulAut ↥V) : MulAut (IntMod V C.hV)) = _
    rw [MulEquiv.symm_apply_apply]
  refine ⟨C.ι x, ?_, C.actI_val hx⟩
  rw [mem_bar_iff, MulEquiv.symm_apply_apply]
  exact convI_mem_autI C.hV hy hyN

end CaseIICtx

end Act

section Excl

variable {V : Subgroup G}

theorem false_of_d8v4 (h : Hyp27 H R M K) (hs : StarHyp R K V) (hVR : V ≤ R)
    (hZV : omegaOneCenterOf R ≤ V) (C : CaseIICtx R K V 8) (hR : C.bar R = d8v4) : False := by
  classical
  have hs0K : ((C.ι.symm s0 : ↥(autOn (K ⊔ R) V)) : MulAut ↥V) ∈ autOn K V := by
    rw [C.mem_K, MulEquiv.apply_symm_apply]
    exact s0_mem_alt
  obtain ⟨⟨s, hsN⟩, hsK, hse⟩ := (mem_autI C.hV).1 hs0K
  have hse' : C.actI s0 = convI C.hV ⟨s, hsN⟩ := hse.symm
  have hfix1 : ∀ u : IntMod V C.hV, (∀ σ ∈ d8v4, C.actI σ u = u) →
      ∀ r ∈ R, r * u.val * r⁻¹ = u.val := by
    intro u hu r hr
    obtain ⟨σ, hσ, hσu⟩ := C.exists_mem_bar hs le_sup_right hr
    rw [← hσu, hu σ (by rw [← hR]; exact hσ)]
  have hfix2 : ∀ u : IntMod V C.hV, (∀ r ∈ R, r * u.val * r⁻¹ = u.val) →
      ∀ σ ∈ d8v4, C.actI σ u = u := by
    intro u hu σ hσ
    obtain ⟨r, hr, hrN, hre⟩ := C.exists_of_mem_bar (by rw [hR]; exact hσ : σ ∈ C.bar R)
    exact IntMod.val_injective ((C.actI_val hre u).trans (hu r hr))
  have hconjV8 : ∀ g ∈ Claim2526.V8, s0⁻¹ * g * s0 ∈ Claim2526.V8 := by
    intro g hg
    have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ s0_mem_normalizer_V8) g).1 hg
    rwa [inv_inv] at h1
  have key : ∀ u : IntMod V C.hV, (∀ σ ∈ d8v4, C.actI σ u = u) →
      ∀ σ ∈ d8v4, C.actI σ (C.actI s0 u) = C.actI s0 u := by
    intro u hu
    have hV8 : ∀ g ∈ Claim2526.V8, C.actI g (C.actI s0 u) = C.actI s0 u := by
      intro g hg
      have e : g * s0 = s0 * (s0⁻¹ * g * s0) := by group
      rw [← MulAut.mul_apply, ← map_mul, e, map_mul, MulAut.mul_apply,
        hu _ (V8_le_d8v4 (hconjV8 g hg))]
    have hw : C.actI s0 u * u⁻¹ ∈ commV (autI C.hV K) :=
      Subgroup.subset_closure ⟨C.actI s0, hs0K, u, rfl⟩
    have hwfix : ∀ g ∈ Claim2526.V8, C.actI g (C.actI s0 u * u⁻¹) = C.actI s0 u * u⁻¹ := by
      intro g hg
      rw [map_mul, map_inv, hV8 g hg, hu g (V8_le_d8v4 hg)]
    have h01 : C.actI (swap 0 1) (C.actI s0 u * u⁻¹) = C.actI s0 u * u⁻¹ :=
      C.apply_swap01_eq_of_fix_V8 hs hw hwfix
    have hu' : C.actI s0 u = C.actI s0 u * u⁻¹ * u := by rw [inv_mul_cancel_right]
    intro σ hσ
    unfold d8v4 at hσ
    induction hσ using Subgroup.closure_induction with
    | mem g hg =>
      have hg' : g ∈ d8v4Gens := hg
      simp only [d8v4Gens, List.mem_cons, List.mem_nil_iff, or_false] at hg'
      rcases hg' with rfl | hg'
      · rw [hu', map_mul, h01, hu _ swap01_mem_d8v4]
      · refine hV8 g (Subgroup.subset_closure ?_)
        show g ∈ Claim2526.v8Gens
        simp only [Claim2526.v8Gens, List.mem_cons, List.mem_nil_iff, or_false]
        exact hg'
    | one => rw [map_one, MulAut.one_apply]
    | mul a b _ _ ha hb => rw [map_mul, MulAut.mul_apply, hb, ha]
    | inv a _ ha =>
      calc C.actI a⁻¹ (C.actI s0 u) = C.actI a⁻¹ (C.actI a (C.actI s0 u)) := by rw [ha]
        _ = C.actI s0 u := by
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  have hZC : ∀ z ∈ omegaOneCenterOf R, ∀ r ∈ R, r * z * r⁻¹ = z := by
    intro z hz r hr
    have hzC : z ∈ Subgroup.centralizer (R : Set G) :=
      (Subgroup.closure_le _).2 (fun x hx => hx.1.2) hz
    rw [Subgroup.mem_centralizer_iff.1 hzC r hr, mul_inv_cancel_right]
  have hsZ : s ∈ Subgroup.normalizer (omegaOneCenterOf R : Set G) := by
    refine mem_normalizer_of_forall_conj_mem fun z hz => ?_
    have hzV : z ∈ V := hZV hz
    have hu : ∀ σ ∈ d8v4, C.actI σ (IntMod.mk C.hV ⟨z, hzV⟩) = IntMod.mk C.hV ⟨z, hzV⟩ :=
      hfix2 _ fun r hr => hZC z hz r hr
    have h1 := hfix1 _ (key _ hu)
    rw [C.actI_val hse'] at h1
    have h1' : ∀ r ∈ R, r * (s * z * s⁻¹) * r⁻¹ = s * z * s⁻¹ := h1
    have hszV : s * z * s⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hsN z).1 hzV
    refine Subgroup.subset_closure ⟨⟨hVR hszV, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩,
      C.hV.2 _ hszV⟩
    calc r * (s * z * s⁻¹) = r * (s * z * s⁻¹) * r⁻¹ * r := by group
      _ = s * z * s⁻¹ * r := by rw [h1' r hr]
  have hZne : omegaOneCenterOf R ≠ ⊥ :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot h.isPGroup h.R_ne_bot
  have hsM : s ∈ M := h.hyp.cgs (inf_normalizer_le_cgsIn_of_char (A4.omegaOneCenterOf_le R) hZne
    (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf R) ⟨h.K_le hsK, hsZ⟩)
  have hsX : s ∈ K ⊔ R := Subgroup.mem_sup_left hsK
  have hLX : conjClosure R (M ⊓ (K ⊔ R)) ≤ K ⊔ R := conjClosure_le fun m hm r hr =>
    (K ⊔ R).mul_mem ((K ⊔ R).mul_mem hm.2 (Subgroup.mem_sup_right hr)) ((K ⊔ R).inv_mem hm.2)
  have hRL : R ≤ conjClosure R (M ⊓ (K ⊔ R)) := le_conjClosure R _
  have hSyl := CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn h.isSylowTwoOf_conjClosure
    (hLX.trans hs.le_normalizer_V)
  have hSylBar : IsSylowTwoOf (C.bar R) (C.bar (conjClosure R (M ⊓ (K ⊔ R)))) :=
    (isSylowTwoOf_trS_iff C.ι (autOn_mono' hRL) (autOn_mono' hLX)).1 hSyl
  rw [hR] at hSylBar
  have hconj : d8v4.map (MulAut.conj s0).toMonoidHom ≤
      C.bar (conjClosure R (M ⊓ (K ⊔ R))) := by
    rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨r, hr, hrN, hre⟩ := C.exists_of_mem_bar (by rw [hR]; exact hτ : τ ∈ C.bar R)
    rw [CaseIICtx.mem_bar_iff]
    show C.actI (s0 * τ * s0⁻¹) ∈ autI C.hV (conjClosure R (M ⊓ (K ⊔ R)))
    rw [map_mul, map_mul, map_inv, hse', hre, ← map_inv, ← map_mul, ← map_mul]
    refine (mem_autI C.hV).2 ⟨_, ?_, rfl⟩
    exact mem_conjClosure ⟨hsM, hsX⟩ hr
  have hQ : d8v4 ⊔ d8v4.map (MulAut.conj s0).toMonoidHom ≤
      C.bar (conjClosure R (M ⊓ (K ⊔ R))) := sup_le hSylBar.1 hconj
  have hQ2 : IsPGroup 2 ↥(d8v4 ⊔ d8v4.map (MulAut.conj s0).toMonoidHom) :=
    isPGroup_P8.to_le (sup_le d8v4_le_P8 map_s0_d8v4_le_P8)
  have heq := sylow_eq_of_le_of_isPGroup hSylBar le_sup_left hQ hQ2
  exact not_map_s0_d8v4_le (le_sup_right.trans heq.le)

theorem false_of_caseII_d8v4 (h : Hyp27 H R M K)
    (C : CaseIICtx R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) 8) (hR : C.bar R = d8v4) :
    False :=
  false_of_d8v4 h h.starHyp ((A4.omegaOneCenterOf_le _).trans h.pCoreOf_sup_le)
    h.omegaOneCenterOf_le C hR

end Excl

end CFSG.Quasithin.SmithC27

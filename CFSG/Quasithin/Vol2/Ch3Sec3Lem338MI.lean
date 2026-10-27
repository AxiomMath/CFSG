module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338MH

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

omit [Finite G] in
theorem commVPlus_eq_commV [IsMulCommutative ↥(vPlus L T)] {X : Subgroup G}
    (hXV : X ≤ Subgroup.normalizer (vPlus L T : Set G)) :
    commVPlus L T X = commV (autOn X (vPlus L T)) := by
  apply Subgroup.map_injective (vPlus L T).subtype_injective
  rw [map_commV_autOn hXV, Subgroup.map_subgroupOf_eq_of_le
    (commutator_le_left_of_le_normalizer hXV)]

omit [Finite G] in
theorem map_conj_eq_of_mul_self {X : Subgroup G} {u : G}
    (h : X.map (MulAut.conj (u * u)).toMonoidHom = X.map (MulAut.conj u).toMonoidHom) :
    X.map (MulAut.conj u).toMonoidHom = X := by
  have h1 := congrArg (Subgroup.map (MulAut.conj u⁻¹).toMonoidHom) h
  rw [Subgroup.map_map, Subgroup.map_map] at h1
  have e1 : (MulAut.conj u⁻¹).toMonoidHom.comp (MulAut.conj (u * u)).toMonoidHom =
      (MulAut.conj u).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have e2 : (MulAut.conj u⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [e1, e2, Subgroup.map_id] at h1
  exact h1

namespace Hyp331

theorem lemma_3_3_8_one
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat)
    (h39 : A39ForSQTKCat) (h56 : AsB56) (hSL3 : A38TypesSLThree)
    (hT : ¬ T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ _ : IsMulCommutative ↥(vPlus L T), Case3_3_8_one T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht, htn⟩ := IsConcreteLE.not_le_iff_exists.mp hT
  have hMp := h.mPlus_eq_sup_conjugate h38 hT ht htn
  have hcV := h.commutator_conjugate_le ht htn
  obtain ⟨hVc, hFF⟩ := h.isFFModule h38 h39
  have hred := vPlus_reduced h.toSetup331
  obtain ⟨hKX, hXK, h2X, -⟩ := h.autOn_data
  set V := vPlus L T with hVdef
  have hHV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hred.2.2.2.1
  have hO2 : pCoreOf 2 (autOn (L ⊔ T) V) = ⊥ :=
    CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred.2.2
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hHV
  have htV : t ∈ Subgroup.normalizer (V : Set G) := hHV (Subgroup.mem_sup_right ht)
  have hLtV : CFSG.conjugate L t ≤ Subgroup.normalizer (V : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).mul_mem (inv_mem htV) (hLV hx)) (inv_mem (inv_mem htV))
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hred.2.1.2 v v.2)
  set K₁ := autOn L V with hK₁
  set K₂ := autOn (CFSG.conjugate L t) V with hK₂
  set X := autOn (L ⊔ T) V with hXdef
  set K := autOn (mPlus L T) V with hKdef
  have hKsup : K = K₁ ⊔ K₂ := by
    rw [hKdef, hMp]
    exact autOn_sup hLV hLtV
  have hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := autOn_commute hcV
  set s := conjAct V ⟨t⁻¹, inv_mem htV⟩ with hs
  have hK₂eq : K₂ = K₁.map (MulAut.conj s).toMonoidHom := autOn_map_conj (X := L) (inv_mem htV)
  have hsX : s ∈ X := CFSG.QuasithinUnique.Setup.mem_autOn_iff.mpr
    ⟨⟨t⁻¹, inv_mem htV⟩, (L ⊔ T).inv_mem (Subgroup.mem_sup_right ht), rfl⟩
  have hK₂N : K₂ ≤ Subgroup.normalizer (K₁ : Set (MulAut ↥V)) := le_normalizer_of_commute hc
  have hK₁K : K₁ ≤ K := by rw [hKsup]; exact le_sup_left
  have hKN₁ : K ≤ Subgroup.normalizer (K₁ : Set (MulAut ↥V)) := by
    rw [hKsup]
    exact sup_le Subgroup.le_normalizer hK₂N
  have hOK : pCoreOf 2 K = ⊥ := le_bot_iff.mp (hO2 ▸
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K X hKX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK))
  have hOK₁ : pCoreOf 2 K₁ = ⊥ := le_bot_iff.mp (hOK ▸
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K₁ K hK₁K
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₁K).mpr hKN₁))
  have hnt : ¬ L ≤ Subgroup.centralizer (V : Set G) := h.not_L_le_centralizer h38 h39
  have hq₁ : CFSG.IsQuasisimple ↥K₁ := InternalSec.isQuasisimple_autOn hLV h.Lq hOK₁ hnt
  have hA38L : A38Types (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases lemma_1_2_1_three h.qtke h.simple h.nonabelian
        (a37ForSQTK_of_cat CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved)
        (a38ForSQTK_of_cat h38) h.toSetup331.pCoreOf_ne_bot h.toSetup331.mem_cComp with
      hL | ⟨-, hA⟩
    · exact absurd (le_sup_right.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hL)) hT
    · exact hA
  have hsL : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Vol2Native.L122A.isSimpleGroup_of_a38Types hA38L
  set ρ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥K₁ := QuotientGroup.lift (CFSG.pCore 2 ↥L)
    (InternalSec.autOnHom hLV) (InternalSec.pCore_le_ker_autOnHom hLV hOK₁) with hρ
  have hρs : Function.Surjective ρ := by
    intro y
    obtain ⟨l, rfl⟩ := InternalSec.autOnHom_surjective hLV y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hρi : Function.Injective ρ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with hk | hk
    · exact (MonoidHom.ker_eq_bot_iff ρ).mp hk
    · exfalso
      apply InternalSec.ker_autOnHom_ne_top hLV hnt
      rw [eq_top_iff]
      intro l _
      have hl : (QuotientGroup.mk l : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ ρ.ker := hk ▸ Subgroup.mem_top _
      exact (MonoidHom.mem_ker).mpr ((MonoidHom.mem_ker).mp hl)
  let eρ := MulEquiv.ofBijective ρ ⟨hρi, hρs⟩
  have hA38 : A38Types ↥K₁ := A38Types.of_mulEquiv eρ hA38L
  have hs₁ : IsSimpleGroup ↥K₁ := eρ.symm.isSimpleGroup
  let c : ↥K₁ ≃* ↥(K₁.map (MulAut.conj s).toMonoidHom) :=
    K₁.equivMapOfInjective _ (MulAut.conj s).injective
  have hq₂ : CFSG.IsQuasisimple ↥K₂ := by
    rw [hK₂eq]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv c hq₁
  have hs₂ : IsSimpleGroup ↥K₂ := by
    rw [hK₂eq]
    exact c.symm.isSimpleGroup
  have hA38₂ : A38Types ↥K₂ := by
    rw [hK₂eq]
    exact A38Types.of_mulEquiv c hA38
  have hZ : Subgroup.center ↥K₁ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K₁) with hz | hz
    · exact hz
    · exfalso
      obtain ⟨a, b, hab⟩ := InternalSec.exists_noncomm_of_isQuasisimple hq₁
      have hb : b ∈ Subgroup.center ↥K₁ := by rw [hz]; exact Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.mp hb a)
  have hinf : K₁ ⊓ K₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxz : (⟨x, hx.1⟩ : ↥K₁) ∈ Subgroup.center ↥K₁ :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2 x hx.2)
    rw [hZ, Subgroup.mem_bot] at hxz
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxz)
  set J := ffJ X with hJdef
  have hJX : J ≤ X := B6.ffJ_le X
  have hXJ : X ≤ Subgroup.normalizer (J : Set (MulAut ↥V)) := B6.le_normalizer_ffJ X
  obtain ⟨A, hA⟩ := ((B1_4_5 hV2 X).out 1 2).1 hFF
  have hAJ : A ≤ J := B6.le_ffJ hA
  have hperf₁ : ⁅K₁, K₁⁆ = K₁ := commutator_eq_self_of_isPerfect hq₁.1
  have hK₁J : K₁ ≤ J := by
    rcases le_or_commute_of_isSimpleGroup hs₁ hperf₁ ((hK₁K.trans hKX).trans hXJ)
        (((Subgroup.commutator_mono hK₁K hJX).trans
          (commutator_le_left_of_le_normalizer hXK)).trans hKN₁) with hle | hcomm
    · exact hle
    · exfalso
      have hsJ : ∀ j ∈ J, s⁻¹ * j * s⁻¹⁻¹ ∈ J := fun j hj =>
        (Subgroup.mem_normalizer_iff.mp (inv_mem (hXJ hsX)) j).mp hj
      have hcomm₂ : ∀ b ∈ K₂, ∀ j ∈ J, b * j = j * b := by
        intro b hb j hj
        rw [hK₂eq] at hb
        obtain ⟨a, ha, rfl⟩ := hb
        have h1 := hcomm a ha _ (hsJ j hj)
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1 ⊢
        calc s * a * s⁻¹ * j = s * (a * (s⁻¹ * j * s)) * s⁻¹ := by group
          _ = s * (s⁻¹ * j * s * a) * s⁻¹ := by rw [h1]
          _ = j * (s * a * s⁻¹) := by group
      have hJC : J ≤ Subgroup.centralizer (K : Set (MulAut ↥V)) := by
        rw [Subgroup.le_centralizer_iff, hKsup]
        exact sup_le
          (fun a ha => Subgroup.mem_centralizer_iff.mpr fun j hj => (hcomm a ha j hj).symm)
          (fun b hb => Subgroup.mem_centralizer_iff.mpr fun j hj => (hcomm₂ b hb j hj).symm)
      apply hA.2.1
      rw [eq_bot_iff]
      intro a ha
      refine Subgroup.mem_bot.mpr (eq_one_of_two_of_commute hXK h2X hO2 (hA.1 ha)
        (fun k hk => (Subgroup.mem_centralizer_iff.mp (hJC (hAJ ha)) k hk)) (e := 1) ?_)
      simpa using hA.2.2.1.2 a ha
  have hK₂J : K₂ ≤ J := by
    rw [hK₂eq]
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hXJ hsX) a).mp (hK₁J ha)
  have hJK : J ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) := by
    rw [← hKsup]
    exact hJX.trans hXK
  have hJne : J ≠ ⊥ := fun hb => hA.2.1 (le_bot_iff.mp (hb ▸ hAJ))
  have hSY : SQTKGroup ↥(L ⊔ T) :=
    sqtkGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian h.toSetup331.pCoreOf_ne_bot
  have hcases := h56 ↥V hV2 J hJne (InternalSec.b53Hyp_ffJ_autOn hHV hSY hO2)
  have hty : (∃ n : ℕ, LieModel ↥K₁ .PSL 2 2 n) ∨ IsPSL 3 2 1 ↥K₁ := by
    rcases type_of_b56Cases hq₁ hs₁ hq₂ hs₂ hc hinf hK₁J hK₂J hJK hcases with
      hL | ⟨m, F, _, _, hF, ⟨e⟩⟩
    · exact Or.inl hL
    · have hm : m = 1 := hSL3 ↥K₁ F m hF ⟨e⟩ hA38
      subst hm
      rw [pow_one] at hF
      exact Or.inr (Vol2Native.A312L.Seven.isPSL_three_two (e.trans (statedSLEquivZModTwo hF)))
  have htt : t⁻¹ * t⁻¹ ∈ L ⊔ T :=
    (L ⊔ T).mul_mem (Subgroup.mem_sup_right (inv_mem ht)) (Subgroup.mem_sup_right (inv_mem ht))
  have hL2 : L.map (MulAut.conj (t⁻¹ * t⁻¹)).toMonoidHom = L := by
    rcases h.map_conj_mem h38 hT ht htn htt with h1 | h1
    · exact h1
    · exfalso
      apply htn
      have h2 : t⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
        Ch3Sec3.mem_normalizer_of_map_conj_eq (map_conj_eq_of_mul_self h1)
      simpa using inv_mem h2
  have hu2 : t⁻¹ * t⁻¹ ∈ Subgroup.normalizer (V : Set G) := mul_mem (inv_mem htV) (inv_mem htV)
  have hs₁₂ : CFSG.Quasithin.conjSub s K₂ = K₁ := by
    have h2 := autOn_map_conj (X := L) hu2
    rw [hL2] at h2
    have e1 : conjAct V ⟨t⁻¹ * t⁻¹, hu2⟩ = s * s := by
      rw [hs, ← map_mul]
      rfl
    rw [e1] at h2
    have e2 : (MulAut.conj s).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
        (MulAut.conj (s * s)).toMonoidHom := by
      ext x v
      simp [MulAut.conj_apply, MulAut.mul_apply]
    calc CFSG.Quasithin.conjSub s K₂
        = (K₁.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s).toMonoidHom := by
          rw [hK₂eq]
          rfl
      _ = K₁.map (MulAut.conj (s * s)).toMonoidHom := by rw [Subgroup.map_map, e2]
      _ = K₁ := h2.symm
  have hMV : mPlus L T ≤ Subgroup.normalizer (V : Set G) := by
    rw [hMp]
    exact sup_le hLV hLtV
  have hZ' : cvPlus L T = fixV (K₁ ⊔ K₂) := by
    rw [← hKsup, hKdef, fixV_autOn hMV]
  have hcL : commVPlus L T L = commV K₁ := commVPlus_eq_commV hLV
  have hcLt : commVPlus L T (CFSG.conjugate L t) = commV K₂ := commVPlus_eq_commV hLtV
  have hcM : commVPlus L T (mPlus L T) = commV K₁ ⊔ commV K₂ := by
    rw [commVPlus_eq_commV hMV, ← hKdef, hKsup, M338.commV_sup]
  obtain ⟨hint, hmod⟩ := M338.module_of_b56 hq₁ hs₁ hq₂ hs₂ hc hinf hK₁J hK₂J hJK hV2 hA38
    hA38₂ hSL3 hs₁₂ hK₂eq.symm hcases
  refine ⟨hVc, t, ht, htn, hMp, hc, hinf, hty, ?_, ?_, ?_⟩
  · show commVPlus L T (mPlus L T) ⊔ cvPlus L T =
      (commVPlus L T L ⊔ cvPlus L T) ⊔ (commVPlus L T (CFSG.conjugate L t) ⊔ cvPlus L T)
    rw [hcM, hcL, hcLt, hZ', sup_sup_sup_comm, sup_idem]
  · show (commVPlus L T L ⊔ cvPlus L T) ⊓ (commVPlus L T (CFSG.conjugate L t) ⊔ cvPlus L T) =
      cvPlus L T
    rw [hcL, hcLt, hZ']
    exact hint
  · show M338.ModType K₁ (commVPlus L T L ⊔ cvPlus L T) (cvPlus L T)
    rw [hcL, hZ']
    exact hmod

end Hyp331

theorem stmt3_3_8One_of_b56
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h56 : AsB56)
    (hSL3 : A38TypesSLThree) : Stmt3_3_8One := by
  intro G _ _ T M L D h hT
  exact h.lemma_3_3_8_one h38 h39 h56 hSL3 hT

end CFSG.Quasithin.H13

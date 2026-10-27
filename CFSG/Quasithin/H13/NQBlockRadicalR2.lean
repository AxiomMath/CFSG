module

public import CFSG.Quasithin.H13.NQBlockA312Cases
public import CFSG.Quasithin.H13.A7Nat1233KXi
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native312

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_not_isQuasisimple
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hQ : QuasithinUnique.quasithinIsQTKECat G) {T L : Subgroup G} (hL : quasithinIsLocal T L)
    (hLq : ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) : T ≤ normalizer (L : Set G) := by
  have := hs
  have hloc : QuasithinUnique.LocalSQTK G := (QuasithinUnique.qtkeCore_of_cat hnab hQ).1
  have hO2 : pCoreOf 2 (L ⊔ T) ≠ ⊥ := hL.2.2.2
  have hLc : L ∈ cComp (L ⊔ T) := cComp_of_isLocal hL
  have hQs := QuasithinUnique.Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hloc hO2
  have := hQs.finite
  have hLb := modO2Image_mem_cComp hLc
  obtain ⟨e, -⟩ := exists_modO2_equiv hLc
  have hnq : ¬ CFSG.IsQuasisimple ↥(modO2Image (L ⊔ T) L) := fun h =>
    hLq (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm h)
  have hnorm : (modO2Image (L ⊔ T) L).Normal := by
    by_contra hn
    obtain ⟨t, ht⟩ := A38.exists_not_mem_normalizer hn
    have hcomm := QuasithinUnique.Vol2Native.a37ForSQTKCat_proved _ hQs _ hLb _
      (A38.cComp_conj hLb) (fun h => ht (A38.map_conj_eq_iff.mp h.symm))
    have hA := QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved _ hQs _ hLb
    exact hnq (QuasithinUnique.Vol2Native.isQuasisimple_of_commuting_conj_of_rank
      (fun q hq hq2 => hQs.rank_top hq hq2) hLb
      (hQs.pCore_two_of_subnormal (subnormal_of_mem_cComp hLb)) hA.1 hA.2.2 hcomm)
  have hLn : (L.subgroupOf (L ⊔ T)).Normal :=
    normal_of_normal_map_of_mem_cComp (CFSG.pCore 2 ↥(L ⊔ T))
      (isSolvable_pCore_two_group ↥(L ⊔ T)) (subgroupOf_mem_cComp hLc) hnorm
  exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer le_sup_left).mp hLn)

theorem le_centralizer_of_not_faithful (hQ : QuasithinUnique.quasithinIsQTKECat G)
    {T L : Subgroup G} (hT : quasithinIsSylowTwo T) (hL : quasithinIsLocal T L)
    (hLf : ¬ quasithinIsFaithfulLocal T L) :
    L ≤ centralizer (reducedAggregate (L ⊔ T) : Set G) := by
  have hX : IsXClass L := isXClass_of_isLocal_cat hQ hT hL
  have hVY : VY L = ⊥ := by
    by_contra h
    exact hLf (isFaithfulLocal_iff_isXf.mpr ⟨hL, hX, h⟩)
  have hc : ⁅CFSG.Quasithin.omegaOneCenterOf (pCoreOf 2 (L ⊔ T)), L⁆ = ⊥ := by
    by_contra h
    exact ((a4_9 hX (subnormal_of_mem_cComp (cComp_of_isLocal hL))).mp h) hVY
  rw [commutator_eq_bot_iff_le_centralizer] at hc
  intro x hx
  rw [mem_centralizer_iff]
  intro v hv
  have hv' : v ∈ CFSG.Quasithin.omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) :=
    reducedAggregate_le_omegaOneCenterOf (L ⊔ T) hv
  exact (mem_centralizer_iff.mp (hc hv') x hx).symm

omit [Finite G] in
theorem exists_modO2Image_surjection [Finite G] {H L : Subgroup G} (hLH : L ≤ H) :
    ∃ ψ : ↥L →* ↥(modO2Image H L), Function.Surjective ψ ∧ IsPGroup 2 ψ.ker ∧
      ∀ l : ↥L, ((ψ l : ↥(modO2Image H L)) : ↥H ⧸ CFSG.pCore 2 ↥H) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) (Subgroup.inclusion hLH l) := by
  set φ : ↥L →* ↥H ⧸ CFSG.pCore 2 ↥H :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hLH) with hφ
  have hr : φ.range = modO2Image H L := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  refine ⟨(MulEquiv.subgroupCongr hr).toMonoidHom.comp φ.rangeRestrict,
    (MulEquiv.subgroupCongr hr).surjective.comp φ.rangeRestrict_surjective, ?_, fun _ => rfl⟩
  rintro ⟨x, hx⟩
  have h1 : φ x = 1 := by
    have h2 : (MulEquiv.subgroupCongr hr) (φ.rangeRestrict x) = 1 := hx
    rw [MulEquiv.map_eq_one_iff] at h2
    exact congrArg Subtype.val h2
  have h3 : Subgroup.inclusion hLH x ∈ CFSG.pCore 2 ↥H := by
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, h3⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h4 : (Subgroup.inclusion hLH x) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  show x ^ 2 ^ k = 1
  apply Subgroup.inclusion_injective hLH
  rw [map_pow, map_one]
  exact h4

theorem isQuasisimple_of_modO2Image {H L : Subgroup G} (hLH : L ≤ H)
    (h : CFSG.IsQuasisimple (↥(modO2Image H L) ⧸ CFSG.pCore 2 ↥(modO2Image H L))) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨ψ, hψ, hker, -⟩ := exists_modO2Image_surjection hLH
  set χ : ↥L →* ↥(modO2Image H L) ⧸ CFSG.pCore 2 ↥(modO2Image H L) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(modO2Image H L))).comp ψ with hχ
  have hχs : Function.Surjective χ := (QuotientGroup.mk'_surjective _).comp hψ
  have hV : IsPGroup 2 χ.ker := by
    have h1 : χ.ker = (CFSG.pCore 2 ↥(modO2Image H L)).comap ψ := by
      rw [hχ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rw [h1]
    exact IsPGroup.comap_of_ker_isPGroup CFSG.pCore_isPGroup ψ hker
  exact isQuasisimple_quotient_pCore_of_ext hV
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective χ hχs).symm h)

omit [Finite G] in
theorem pCore_le_oddCore {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.pCore p X ≤ CFSG.oddCore X := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := p) (G := X)).exists_card_eq
  show CFSG.pCore p X ≤ sSup _
  exact le_sSup ⟨CFSG.pCore_normal, by rw [hn]; exact (hp.odd_of_ne_two hp2).pow⟩

omit [Finite G] in
theorem mem_oddCore_of_mem_solvableRadical {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}
    (hA : QuasithinUnique.Vol2Native.A36CoreCat L) (hq : ¬ CFSG.IsQuasisimple ↥L) {x : ↥L}
    (hx : x ∈ CFSG.solvableRadical ↥L) (hodd : Odd (orderOf x)) : x ∈ CFSG.oddCore ↥L := by
  refine mem_of_forall_prime_power fun y hy ⟨p, k, hp, hyk⟩ => ?_
  have hyR : y ∈ CFSG.solvableRadical ↥L := zpowers_le.mpr hx hy
  by_cases hk0 : k = 0
  · subst hk0
    rw [pow_zero, orderOf_eq_one_iff] at hyk
    rw [hyk]
    exact one_mem _
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : orderOf y ∣ orderOf x := orderOf_dvd_of_mem_zpowers hy
    rw [hyk] at h1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans h1))
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hyk
    exact (Nat.one_lt_pow hk0 hp.one_lt).ne hyk
  obtain ⟨-, hyP, -⟩ := a36_prime_element hA hq hp hp2 hyR hy1 hyk
  exact pCore_le_oddCore hp hp2 hyP

omit [Finite G] in
theorem sq_eq_one_of_mem_center_SL2 {F : Type} [Field F]
    {A : Matrix.SpecialLinearGroup (Fin 2) F}
    (hA : A ∈ center (Matrix.SpecialLinearGroup (Fin 2) F)) : A ^ 2 = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  ext i j
  simp only [Fintype.card_fin] at hr
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, ← hrA, ← map_mul, ← pow_two, hr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

omit [Finite G] in
theorem eq_one_of_isSL2 {X Q : Type} [Group X] [Group Q] [Finite X] (φ : X →* Q)
    (hφ : Function.Surjective φ) {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hQ : IsSL2 r Q) {y : X}
    (hy : y ∈ CFSG.solvableRadical X) (hodd : Odd (orderOf y)) : φ y = 1 := by
  have : Finite Q := Finite.of_surjective φ hφ
  have : Fact r.Prime := ⟨hr⟩
  have hqs := isQuasisimple_of_isSL2 hr hr3 hQ
  obtain ⟨e⟩ := hQ
  have hR : φ y ∈ CFSG.solvableRadical Q :=
    CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.map_solvableRadical_le hφ
      (mem_map_of_mem φ hy)
  have hZ : φ y ∈ center Q := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs
      (inferInstance : (CFSG.solvableRadical Q).Normal) with htop | hle
    · exfalso
      have hs : Group.IsSolvable ↥(CFSG.solvableRadical Q) := A3.solvableRadical_isSolvable
      let e' : ↥(CFSG.solvableRadical Q) ≃* Q :=
        (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
      have hsQ : Group.IsSolvable Q :=
        Group.isSolvable_of_isSolvable_injective (f := e'.symm.toMonoidHom) e'.symm.injective
      have : Group.IsPerfect Q := hqs.1
      have : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hqs
      exact Group.IsPerfect.not_isSolvable Q hsQ
    · exact hle hR
  have hZ' : e (φ y) ∈ center (Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) := by
    rw [mem_center_iff] at hZ ⊢
    intro g
    obtain ⟨h, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hZ h]
  have h2 : (φ y) ^ 2 = 1 := by
    have h3 := sq_eq_one_of_mem_center_SL2 hZ'
    rwa [← map_pow, MulEquiv.map_eq_one_iff] at h3
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left
    (orderOf_dvd_of_pow_eq_one h2) (Nat.coprime_two_left.mpr hodd)) (orderOf_map_dvd φ y))

omit [Finite G] in
theorem surjective_mk_oddCore_of_eq_sup {E : Type} [Group E] {B L : Subgroup E} (hBL : B ≤ L)
    (hL : L = B ⊔ (CFSG.oddCore ↥L).map L.subtype) :
    Function.Surjective ((QuotientGroup.mk' (CFSG.oddCore ↥L)).comp (Subgroup.inclusion hBL)) := by
  intro q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore ↥L) q
  have hl : (l : E) ∈ ((B ⊔ (CFSG.oddCore ↥L).map L.subtype : Subgroup E) : Set E) := by
    rw [← hL]
    exact l.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right B _
    (hBL.trans (A312.le_normalizer_oddCoreSub L))] at hl
  obtain ⟨b, hb, o, ⟨o', ho', rfl⟩, hbo⟩ := hl
  refine ⟨⟨b, hb⟩, ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have h1 : (Subgroup.inclusion hBL ⟨b, hb⟩)⁻¹ * l = o' := by
    apply Subtype.ext
    show (b : E)⁻¹ * (l : E) = (o' : E)
    rw [← hbo]
    simp
  rw [h1]
  exact ho'

omit [Finite G] in
theorem surjective_mk_sup_oddCore {E : Type} [Group E] {B L : Subgroup E} (hBL : B ≤ L)
    [(((CFSG.oddCore ↥L).map L.subtype).subgroupOf
      (B ⊔ (CFSG.oddCore ↥L).map L.subtype)).Normal] :
    Function.Surjective ((QuotientGroup.mk' (((CFSG.oddCore ↥L).map L.subtype).subgroupOf
      (B ⊔ (CFSG.oddCore ↥L).map L.subtype))).comp
      (Subgroup.inclusion (le_sup_left : B ≤ B ⊔ (CFSG.oddCore ↥L).map L.subtype))) := by
  intro q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hl : (l : E) ∈ ((B ⊔ (CFSG.oddCore ↥L).map L.subtype : Subgroup E) : Set E) := l.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right B _
    (hBL.trans (A312.le_normalizer_oddCoreSub L))] at hl
  obtain ⟨b, hb, o, ho, hbo⟩ := hl
  refine ⟨⟨b, hb⟩, ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    mem_subgroupOf]
  show (b : E)⁻¹ * (l : E) ∈ _
  rw [← hbo, inv_mul_cancel_left]
  exact ho

theorem mem_oddCore_of_nonquasi {E : Type} [Group E] [Finite E] {B L : Subgroup E} (hBL : B ≤ L)
    (h36 : A36Strong L) (hnq : ¬ CFSG.IsQuasisimple ↥L) (h : A312Nonquasi B L) {x : ↥B}
    (hx : x ∈ CFSG.solvableRadical ↥B) (hodd : Odd (orderOf x)) :
    (x : E) ∈ (CFSG.oddCore ↥L).map L.subtype := by
  unfold A312Nonquasi at h
  dsimp only at h
  rcases h with ⟨-, hLB, -⟩ | ⟨-, -, N, hN, rfl, hSL⟩
  · obtain ⟨p, hp, hp3, hSL⟩ := A312.exists_isSL2_oddCore h36 hnq
    have h1 := eq_one_of_isSL2 _ (surjective_mk_oddCore_of_eq_sup hBL hLB) hp hp3 hSL hx hodd
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, rfl⟩
  · have h1 := eq_one_of_isSL2 _ (surjective_mk_sup_oddCore hBL) Nat.prime_five (by norm_num)
      hSL hx hodd
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_subgroupOf] at h1
    exact h1

theorem oddPre_le_centralizer_of_radical (hQ : QuasithinUnique.quasithinIsQTKECat G)
    {T K : Subgroup G} (hT : quasithinIsSylowTwo T) (hloc : quasithinIsLocal T K)
    (hTK : T ≤ normalizer (K : Set G))
    (hR : (CFSG.solvableRadical ↥K).map K.subtype ≤
      centralizer (reducedAggregate (K ⊔ T) : Set G)) :
    A7.oddPre K T ≤
      centralizer (CFSG.Quasithin.omegaOneCenterOf (pCoreOf 2 (K ⊔ T)) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := A7.oddPre K T with hPdef
  set X := oTwoUpper P with hX
  have hO : pCoreOf 2 (K ⊔ T) ≠ ⊥ := hloc.2.2.2
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hchar : QuasithinUnique.CharTwo (K ⊔ T) :=
    charTwo_of_inH hQ.2.1 S ⟨hS ▸ le_sup_right, hO⟩
  have hPK : P ≤ K := A7.oddPre_le K T
  have hKP : K ≤ normalizer (P : Set G) := A7.le_normalizer_oddPre K T
  have hXP : X ≤ P := oTwoUpper_le P
  have hKM : K ≤ K ⊔ T := le_sup_left
  have hMK : K ⊔ T ≤ normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hXsub : IsSubnormal X (K ⊔ T) :=
    IsSubnormal.step hXP ((Subgroup.normal_subgroupOf_iff_le_normalizer hXP).mpr
      (le_normalizer_oTwoUpper P)) (IsSubnormal.step hPK
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hPK).mpr hKP)
        (A3.subnormal_of_normal hKM
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMK)))
  have hXR : ⁅twoReducedJoin (K ⊔ T), X⁆ = ⊥ := by
    rw [← primeReducedAggregate_map_subtype_eq_twoReducedJoin,
      Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    exact (hXP.trans (A7.oddPre_le_solvableRadical K T)).trans hR
  have htfae := a4_11 hchar (A4.oTwoUpper_oTwoUpper P).symm hXsub
    (A7.noncentral_oTwoUpper_oddPre K T)
  have h13 : IsXf X ↔ ⁅twoReducedJoin (K ⊔ T), X⁆ ≠ ⊥ := htfae.out 1 3
  have hnXf : ¬ IsXf X := fun hXf => h13.mp hXf hXR
  have hXC : X ≤ centralizer (CFSG.Quasithin.omegaOneCenterOf (pCoreOf 2 (K ⊔ T)) : Set G) := by
    by_cases hX1 : X = ⊥
    · rw [hX1]
      exact bot_le
    have hXc : IsXClass X :=
      ⟨hX1, (A4.oTwoUpper_oTwoUpper P).symm, A4.charTwo_of_subnormal hXsub hchar⟩
    have hVY : VY X = ⊥ := by
      by_contra hne
      exact hnXf ⟨hXc, hne⟩
    have hb : ¬ ⁅CFSG.Quasithin.omegaOneCenterOf (pCoreOf 2 (K ⊔ T)), X⁆ ≠ ⊥ := fun hne =>
      ((a4_9 hXc hXsub).mp hne) hVY
    rw [not_not, Subgroup.commutator_eq_bot_iff_le_centralizer] at hb
    exact Subgroup.le_centralizer_iff.mp hb
  intro y hy
  apply A7.mem_of_odd_two_pow (orderOf_pos y).ne'
  · intro m hm
    exact hXC (mem_oTwoUpper_of_odd (P.pow_mem hy m) hm)
  · intro m k hk
    have hmem := A7.mem_pCoreOf_of_mem_oddPre (P.pow_mem hy m) hk
    rw [mem_centralizer_iff]
    intro w hw
    exact (mem_centralizer_iff.1 (A4.centerOf_le_centralizer _
      (A4.omegaOneCenterOf_le_centerOf _ hw)) _ hmem).symm

omit [Finite G] in
theorem omegaOneCenter_pCoreOf_mono [Finite G] {T L K : Subgroup G} (hLK : L ≤ K)
    (hchar : QuasithinUnique.CharTwo (K ⊔ T)) (hPT : pCoreOf 2 (K ⊔ T) ≤ T) :
    CFSG.Quasithin.omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ≤
      CFSG.Quasithin.omegaOneCenterOf (pCoreOf 2 (K ⊔ T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPP : pCoreOf 2 (K ⊔ T) ≤ pCoreOf 2 (L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hPT.trans le_sup_right)
      ((sup_le_sup_right hLK T).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  refine (closure_le _).mpr ?_
  rintro x ⟨⟨hxP, hxC⟩, hx2⟩
  have hxP : x ∈ pCoreOf 2 (L ⊔ T) := hxP
  have hxC : x ∈ centralizer (pCoreOf 2 (L ⊔ T) : Set G) := hxC
  have hxC' : x ∈ centralizer (pCoreOf 2 (K ⊔ T) : Set G) := by
    rw [mem_centralizer_iff] at hxC ⊢
    exact fun y hy => hxC y (hPP hy)
  have hxKT : x ∈ K ⊔ T :=
    sup_le_sup_right hLK T (CFSG.LieType.BorelTits.pCoreOf_le 2 (L ⊔ T) hxP)
  exact subset_closure ⟨⟨hchar ⟨hxKT, hxC'⟩, hxC'⟩, hx2⟩

theorem radical_le_centralizer_of_faithful
    (ha : NoOddLinearThreeLStarF)
    (hb : Lemma3_2_13Consumed) (hc : Lemma3_2_14HomocyclicConsumed)
    (hList : QuasithinUnique.Vol2Native.A312ListFactsCat)
    {T L : Subgroup G} (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hQ : QuasithinUnique.quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hL : quasithinIsLocal T L) (hLf : quasithinIsFaithfulLocal T L)
    (hLq : ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    (CFSG.solvableRadical ↥L).map L.subtype ≤
      centralizer (reducedAggregate (L ⊔ T) : Set G) := by
  classical
  have := hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hloc : QuasithinUnique.LocalSQTK G := (QuasithinUnique.qtkeCore_of_cat hnab hQ).1
  have hTL := le_normalizer_of_not_isQuasisimple hs hnab hQ hL hLq
  obtain ⟨K, hKm, hLK⟩ := exists_maximalLocal_ge hL
  have hKf := local_faithfulness_upward LocDbl.local_double_embedding_exclusion hs hnab hQ hT
    hKm.1 hLK hLf
  have hO2 : pCoreOf 2 (K ⊔ T) ≠ ⊥ := hKm.1.2.2.2
  have hS : QuasithinUnique.IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKm.1.1, hKm.1.2.2.1⟩
  have hKc : K ∈ cComp (K ⊔ T) := cComp_of_isLocal hKm.1
  have hLH : L ≤ K ⊔ T := hLK.trans le_sup_left
  have hQs := QuasithinUnique.Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hloc hO2
  have hA := QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved _ hQs _
    (modO2Image_mem_cComp hKc)
  obtain ⟨eK, -⟩ := exists_modO2_equiv hKc
  obtain ⟨ψ, hψs, -, hψ⟩ := exists_modO2Image_surjection hLH
  have hLKb : modO2Image (K ⊔ T) L ≤ modO2Image (K ⊔ T) K :=
    Subgroup.map_mono fun x hx => hLK hx
  have h312 : QuasithinUnique.Vol2Native.A312ForSQTKCat :=
    QuasithinUnique.Vol2Native.a312ForSQTKCat_of_facts hList CFSG.Quasithin.a312SL2Fact
      QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved
      QuasithinUnique.Vol2Native.a37ForSQTKCat_proved
      QuasithinUnique.Vol2Native.a39ForSQTKCat_proved
  have hLbq : ¬ CFSG.IsQuasisimple
      (↥(modO2Image (K ⊔ T) L) ⧸ CFSG.pCore 2 ↥(modO2Image (K ⊔ T) L)) := fun h =>
    hLq (isQuasisimple_of_modO2Image hLH h)
  have hkey : ¬ CFSG.IsQuasisimple ↥(modO2Image (K ⊔ T) K) ∧
      ∀ z, z ∈ (CFSG.solvableRadical ↥(modO2Image (K ⊔ T) L)).map
        (modO2Image (K ⊔ T) L).subtype → Odd (orderOf z) → z ∈ A7.oddBar K T := by
    rcases QuasithinUnique.Vol2Native.lemma_1_2_4_list hloc h312 hO2 hS hLH
      (mem_lFamily_of_isLocal hL) hKc hLK with heq | hcase | hnq
    · rw [heq] at hLbq ⊢
      have hnq : ¬ CFSG.IsQuasisimple ↥(modO2Image (K ⊔ T) K) := fun h =>
        hLbq (isQuasisimple_quotient_pCore h)
      refine ⟨hnq, ?_⟩
      rintro _ ⟨y, hy, rfl⟩ hodd
      have hodd' : Odd (orderOf y) := by
        rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe] at hodd
      exact ⟨y, mem_oddCore_of_mem_solvableRadical hA hnq hy hodd', rfl⟩
    · exfalso
      have hLp : Group.IsPerfect ↥L :=
        Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp (cComp_of_isLocal hL))
      have : Group.IsPerfect ↥(modO2Image (K ⊔ T) L) := by
        rw [Group.isPerfect_def, eq_top_iff]
        intro y _
        obtain ⟨x, rfl⟩ := hψs y
        have hx : x ∈ commutator ↥L := hLp.commutator_eq_top ▸ mem_top x
        have h1 := mem_map_of_mem ψ hx
        rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
          MonoidHom.range_eq_top.mpr hψs, ← _root_.commutator_def] at h1
      rcases a312Case_quasisimple_or_linear hcase with hq | ⟨p, hp, hp3, hlin⟩
      · exact hLbq hq
      · obtain ⟨hPSL, hSL3⟩ := ha G T K hs hnab hQ hT hKm hKf p hp hp3
        rcases hlin with h | h
        · exact hPSL (IsPSL.of_mulEquiv eK.symm h)
        · exact hSL3 (IsSL3.of_mulEquiv eK.symm h)
    · have hnq' := A312.not_quasisimple_of_nonquasi hnq
      refine ⟨hnq', ?_⟩
      rintro _ ⟨y, hy, rfl⟩ hodd
      have hodd' : Odd (orderOf y) := by
        rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe] at hodd
      exact mem_oddCore_of_nonquasi hLKb (hA.toStrong hnq') hnq' hnq hy hodd'
  obtain ⟨hKbq, hkey⟩ := hkey
  have hKq : ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := fun h =>
    hKbq (CFSG.LocalCores.isQuasisimple_of_mulEquiv eK h)
  have hTK := le_normalizer_of_not_isQuasisimple hs hnab hQ hKm.1 hKq
  have hRK := radical_le_centralizer_of_maximalLocal hb hc hs hnab hQ hT hKm hKf hTK hKq
  have hP := oddPre_le_centralizer_of_radical hQ hT hKm.1 hTK hRK
  obtain ⟨S, hS'⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hchar : QuasithinUnique.CharTwo (K ⊔ T) :=
    charTwo_of_inH hQ.2.1 S ⟨hS' ▸ le_sup_right, hO2⟩
  have hΩ := omegaOneCenter_pCoreOf_mono hLK hchar
    (QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS)
  have hodd : ∀ x ∈ (CFSG.solvableRadical ↥L).map L.subtype, Odd (orderOf x) →
      x ∈ centralizer (reducedAggregate (L ⊔ T) : Set G) := by
    rintro _ ⟨r, hr, rfl⟩ ho
    have ho' : Odd (orderOf r) := by rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe] at ho
    have hz := hkey (ψ r : ↥(K ⊔ T) ⧸ CFSG.pCore 2 ↥(K ⊔ T))
      ⟨ψ r, CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.map_solvableRadical_le hψs
        (mem_map_of_mem ψ hr), rfl⟩
      (by
        rw [Subgroup.orderOf_coe]
        exact ho'.of_dvd_nat (orderOf_map_dvd ψ r))
    rw [hψ r] at hz
    have hmem : (r : G) ∈ A7.oddPre K T := A7.mem_oddPre.2 ⟨hLK r.2, hz⟩
    have hc := hP hmem
    rw [mem_centralizer_iff] at hc ⊢
    intro v hv
    exact hc v (hΩ (reducedAggregate_le_omegaOneCenterOf (L ⊔ T) hv))
  have hO : oTwoUpper ((CFSG.solvableRadical ↥L).map L.subtype) ≤
      centralizer (reducedAggregate (L ⊔ T) : Set G) :=
    (closure_le _).mpr fun x hx => hodd x hx.1 hx.2
  exact le_centralizer_of_oTwoUpper_le (isTwoReducedIn_reducedAggregate (L ⊔ T))
    ((map_subtype_le _).trans le_sup_left)
    ((sup_le le_normalizer hTL).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)) hO

theorem stmt3_2_14_of
    (ha : NoOddLinearThreeLStarF) (hb : Lemma3_2_13Consumed)
    (hc : Lemma3_2_14HomocyclicConsumed) (hList : QuasithinUnique.Vol2Native.A312ListFactsCat) :
    Stmt3_2_14 := by
  intro G _ _ T L hs hnab hQ hT hL hLq
  by_cases hLf : quasithinIsFaithfulLocal T L
  · exact radical_le_centralizer_of_faithful ha hb hc hList hs hnab hQ hT hL hLf hLq
  · exact (map_subtype_le _).trans (le_centralizer_of_not_faithful hQ hT hL hLf)

end CFSG.Quasithin.H13.NQBlock

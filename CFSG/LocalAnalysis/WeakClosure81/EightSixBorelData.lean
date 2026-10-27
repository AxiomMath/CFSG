module

public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelDefs
import CFSG.LocalAnalysis.WeakClosure81.EightFiveBars
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpAut
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpFix
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpTorus
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelUAut
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelUFix
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelUTorus
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2Sp
import CFSG.Quasithin.Background.HSecQuot
public import CFSG.LocalAnalysis.WeakClosure81.EightSixIn

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.Quasithin.H.SecQ
open CFSG.LocalAnalysis.WeakClosure81.SevenK

private theorem borel86_data_congr_apply_apply {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (γ : MulAut S) (x : S) :
    MulAut.congr e γ (e x) = e (γ x) := by
  simp [MulAut.congr_apply]

private theorem borel86_data_congr_conj {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext x
  conv_lhs => rw [← e.apply_symm_apply x]
  rw [borel86_data_congr_apply_apply]
  simp [MulAut.conj_apply]

private theorem borel86_data_congr_mem_range {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (γ : MulAut S) :
    MulAut.congr e γ ∈ (MulAut.conj : S' →* MulAut S').range ↔
      γ ∈ (MulAut.conj : S →* MulAut S).range := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    ext x
    apply e.injective
    have hx := congrArg (fun f : MulAut S' => f (e x)) hy
    rw [MulAut.conj_apply, borel86_data_congr_apply_apply] at hx
    rw [MulAut.conj_apply]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hx
  · rintro ⟨s, rfl⟩
    exact ⟨e s, (borel86_data_congr_conj e s).symm⟩

theorem BorelLieFacts.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {t : S}
    (h : BorelLieFacts S' (e t)) : BorelLieFacts S t where
  center := by
    apply le_antisymm _ bot_le
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : e z ∈ Subgroup.center S' := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
    rw [h.center, Subgroup.mem_bot] at hz'
    exact e.injective (by rw [hz', map_one])
  out α β hαt hβt hα hβ hαβ hαo hβo := by
    set α' := MulAut.congr e α with hα'
    set β' := MulAut.congr e β with hβ'
    have hαt' : α' (e t) = e t := by rw [hα', borel86_data_congr_apply_apply, hαt]
    have hβt' : β' (e t) = e t := by rw [hβ', borel86_data_congr_apply_apply, hβt]
    have hα2 : α' * α' = 1 := by rw [hα', ← map_mul, hα, map_one]
    have hβ2 : β' * β' = 1 := by rw [hβ', ← map_mul, hβ, map_one]
    have hαβ' : α' * β' = β' * α' := by rw [hα', hβ', ← map_mul, ← map_mul, hαβ]
    have hαo' : α' ∉ (MulAut.conj : S' →* MulAut S').range := fun hh =>
      hαo ((borel86_data_congr_mem_range e α).mp (by simpa only [hα'] using hh))
    have hβo' : β' ∉ (MulAut.conj : S' →* MulAut S').range := fun hh =>
      hβo ((borel86_data_congr_mem_range e β).mp (by simpa only [hβ'] using hh))
    have hres := h.out α' β' hαt' hβt' hα2 hβ2 hαβ' hαo' hβo'
    refine (borel86_data_congr_mem_range e (α * β)).mp ?_
    simpa only [hα', hβ', map_mul] using hres
  fix α g hα2 hg hαt hfix := by
    set α' := MulAut.congr e α with hα'
    have hαt' : α' (e t) = e t := by rw [hα', borel86_data_congr_apply_apply, hαt]
    have hα2' : α' * α' = 1 := by rw [hα', ← map_mul, hα2, map_one]
    have hg' : e g * e g = 1 := by rw [← map_mul, hg, map_one]
    have hfix' : ∀ s' : S', α' (s' * e t * s'⁻¹) = s' * e t * s'⁻¹ ↔
        e g * (s' * e t * s'⁻¹) = s' * e t * s'⁻¹ * e g := by
      intro s'
      set u := e.symm s' * t * (e.symm s')⁻¹ with hu
      have hw : s' * e t * s'⁻¹ = e u := by rw [hu]; simp [mul_assoc]
      rw [hα', hw, borel86_data_congr_apply_apply]
      have h1 := hfix (e.symm s')
      constructor
      · intro hh
        have hh' : α u = u := e.injective hh
        simpa only [map_mul, hu] using congrArg e (h1.mp hh')
      · intro hh
        have hh' : g * u = u * g := e.injective (by simpa only [map_mul] using hh)
        exact congrArg e (h1.mpr hh')
    have hres := h.fix α' (e g) hα2' hg' hαt' hfix'
    exact (borel86_data_congr_mem_range e α).mp (by simpa only [hα'] using hres)
  borel P hP := by
    let P' : Sylow 2 S' :=
      P.comapOfInjective e.symm.toMonoidHom e.symm.injective
        (by rw [MonoidHom.range_eq_top.mpr e.symm.surjective]; exact le_top)
    have hP' : ∀ p ∈ (P' : Subgroup S'), p * e t = e t * p := by
      intro p hp
      have hp' : e.symm p ∈ (P : Subgroup S) := hp
      simpa only [map_mul, MulEquiv.apply_symm_apply] using
        congrArg e (hP (e.symm p) hp')
    obtain ⟨d', hd', hd'ne⟩ := h.borel P' hP'
    refine ⟨e.symm d', ?_, ?_⟩
    · have hmap' : (P' : Subgroup S').map e.symm.toMonoidHom = (P : Subgroup S) :=
        Subgroup.map_comap_eq_self_of_surjective e.symm.surjective (P : Subgroup S)
      have h1 : e.symm d' ∈ (Subgroup.normalizer ((P' : Subgroup S') : Set S')).map
          e.symm.toMonoidHom := Subgroup.mem_map.mpr ⟨d', hd', rfl⟩
      rw [Subgroup.map_equiv_normalizer_eq, hmap'] at h1
      exact h1
    · intro hcon
      exact hd'ne (by
        have h2 := congrArg e hcon
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
        exact h2)

section Lie

variable {k m n : ℕ} {F : Type} [Field F] [Finite F]

theorem borelLieFacts_sp (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hk : 1 ≤ k)
    {t₀ : ↥(StatedSp k F)} (ht : IsSymplecticTransvectionIn k t₀) :
    BorelLieFacts ↥(StatedSp k F) t₀ where
  center := by
    haveI : NeZero k := ⟨by omega⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := Fintype.ofFinite F
    haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := n) (by rw [Fintype.card_eq_nat_card, hF])
    exact CFSG.SeitzReduction.F4Pilot.center_statedSp_eq_bot_of_charTwo
  out _ _ _ _ hα hβ hαβ hαo hβo := mul_mem_range_conj_statedSp hF hk hα hβ hαβ hαo hβo
  fix α g _ _ hα hfix := mem_range_conj_of_fix_conj_iff_commute_statedSp hF hn hk ht α g hα hfix
  borel P hP := exists_mem_normalizer_conj_ne_statedSp hF hn ht P hP

theorem borelLieFacts_psu (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 < n) (hm : 3 ≤ m)
    {t₀ : StatedProj (StatedSU m (2 ^ n) F)} (ht : IsUnitaryTransvectionIn m n t₀) :
    BorelLieFacts (StatedProj (StatedSU m (2 ^ n) F)) t₀ where
  center := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hq : (m, 2 ^ n) ≠ (3, 2) := fun h => by
      have h1 : 2 ^ n = 2 := congrArg Prod.snd h
      have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      rw [h1] at h4
      norm_num at h4
    haveI hsimple : IsSimpleGroup (StatedProj (StatedSU m (2 ^ n) F)) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 n hF m hm hq
    haveI : Group.IsPerfect (StatedSU m (2 ^ n) F) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF hm hq
    have hperf : Group.IsPerfect (StatedProj (StatedSU m (2 ^ n) F)) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective
        ((StatedScalars (Fin m) F).subgroupOf (StatedSU m (2 ^ n) F)))
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (1 : StatedProj (StatedSU m (2 ^ n) F))
      have hx' : x ∈ commutator (StatedProj (StatedSU m (2 ^ n) F)) := by
        rw [hperf.commutator_eq_top]
        exact Subgroup.mem_top x
      have hbot : commutator (StatedProj (StatedSU m (2 ^ n) F)) ≤ ⊥ := by
        rw [_root_.commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
      exact hx (Subgroup.mem_bot.mp (hbot hx'))
  out _ _ _ _ hα hβ hαβ hαo hβo := mul_mem_range_conj_statedProjSU hF hn hm hα hβ hαβ hαo hβo
  fix α g hα2 hg hα hfix :=
    mem_range_conj_of_fix_conj_iff_commute_statedProjSU hF hn hm ht α g hα2 hg hα hfix
  borel P hP := exists_mem_normalizer_conj_ne_statedProjSU hF hn hm ht P hP

end Lie

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}

private theorem borel86_data_comp_mk_center_eq_one_iff {K N : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} (hφ : IsBarMap K N φ) (k : ↥K) :
    ((QuotientGroup.mk' (Subgroup.center X)).comp φ) k = 1 ↔ (k : G) ∈ centerPre K N := by
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_center_iff]
  change (∀ g : X, g * φ k = φ k * g) ↔
    (k : G) ∈ K ∧ ∀ x ∈ K, (k : G) * x * (k : G)⁻¹ * x⁻¹ ∈ N
  constructor
  · intro hk
    refine ⟨k.2, fun x hx => ?_⟩
    have h1 : φ (k * (⟨x, hx⟩ : ↥K) * k⁻¹ * (⟨x, hx⟩ : ↥K)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hk (φ ⟨x, hx⟩)]
      group
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using (hφ.ker_iff _).mp h1
  · rintro ⟨-, hx⟩ g
    obtain ⟨y, rfl⟩ := hφ.surjective g
    have h1 : φ (k * y * k⁻¹ * y⁻¹) = 1 := by
      refine (hφ.ker_iff _).mpr ?_
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hx (y : G) y.2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm

theorem exists_borel86Data (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T)
    (hδ : Shape86DeltaT' V H T) :
    ∃ (S : Type) (_ : Group S) (ψ : ↥(kGenIn V H) →* S) (ρ : ↥H →* MulAut S) (t₀ : S),
      Borel86Data V H T S ψ ρ t₀ := by
  obtain ⟨m, n, hn, hrk, X, hX, φ, hφ, hroot⟩ := hδ
  letI := hX
  have hvnmem : ∃ v ∈ V, v ∉ eCentSet V H T := by
    by_contra hcon
    have hle : V ≤ Subgroup.centralizer (eSub V H T : Set G) := fun v hv => by
      by_contra hv'
      exact hcon ⟨v, hv, hv'⟩
    have h1 := hrk
    rw [rankBarV, inf_eq_left.mpr hle, E3.mQuot_self] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨v₀, hv₀V, hv₀E⟩ := hvnmem
  have hv₀K : v₀ ∈ kGenIn V H := le_kGenIn_self V H hv₀V
  let vh : ↥(kGenIn V H) := ⟨v₀, hv₀K⟩
  let ψ₀ : ↥(kGenIn V H) →* X ⧸ Subgroup.center X :=
    (QuotientGroup.mk' (Subgroup.center X)).comp φ
  have hψ₀surj : Function.Surjective ψ₀ :=
    (QuotientGroup.mk'_surjective (Subgroup.center X)).comp hφ.surjective
  have hψ₀ker : ∀ k : ↥(kGenIn V H), ψ₀ k = 1 ↔
      (k : G) ∈ centerPre (kGenIn V H) (eCentSet V H T) := by
    intro k
    dsimp only [ψ₀]
    rw [borel86_data_comp_mk_center_eq_one_iff hφ k, ← h.centerPre_eCentSet_eq hKT]
  let N₀ : Subgroup ↥(kGenIn V H) := ψ₀.ker
  haveI : N₀.Normal := MonoidHom.normal_ker ψ₀
  let I : Subgroup G := N₀.map (kGenIn V H).subtype
  have hIN₀ : I.subgroupOf (kGenIn V H) = N₀ := by
    change Subgroup.comap (kGenIn V H).subtype I = N₀
    rw [show I = N₀.map (kGenIn V H).subtype from rfl]
    exact Subgroup.comap_map_eq_self_of_injective (kGenIn V H).subtype_injective N₀
  haveI : (I.subgroupOf (kGenIn V H)).Normal := by
    rw [hIN₀]
    exact MonoidHom.normal_ker ψ₀
  have hmemI : ∀ x : G, x ∈ I ↔ x ∈ centerPre (kGenIn V H) (eCentSet V H T) := by
    intro x
    constructor
    · intro hx
      obtain ⟨k, hk, hk_eq⟩ := hx
      have hk1 : ψ₀ k = 1 := MonoidHom.mem_ker.mp hk
      rw [← hk_eq]
      exact (hψ₀ker k).mp hk1
    · intro hx
      have hxK : x ∈ kGenIn V H := hx.1
      refine Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, ?_, rfl⟩
      exact MonoidHom.mem_ker.mpr ((hψ₀ker ⟨x, hxK⟩).mpr hx)
  have hHnormI : H ≤ Subgroup.normalizer (I : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb i hi
    rw [hmemI i] at hi
    rw [hmemI (b * i * b⁻¹)]
    obtain ⟨hiK, hic⟩ := hi
    have hbK : b ∈ Subgroup.normalizer (kGenIn V H : Set G) :=
      h.le_normalizer_kGenIn_of_eq_sup hKT hb
    have hbiK : b * i * b⁻¹ ∈ kGenIn V H :=
      (Subgroup.mem_normalizer_iff.mp hbK i).mp hiK
    refine ⟨hbiK, fun x hx => ?_⟩
    have hxb : b⁻¹ * x * b ∈ kGenIn V H := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbK) x).mp hx
    have hcomm : i * (b⁻¹ * x * b) * i⁻¹ * (b⁻¹ * x * b)⁻¹ ∈
        Subgroup.centralizer (eSub V H T : Set G) := hic _ hxb
    have hconj := h.conj_mem_centralizer_eSub hb hcomm
    show (b * i * b⁻¹) * x * (b * i * b⁻¹)⁻¹ * x⁻¹ ∈
      Subgroup.centralizer (eSub V H T : Set G)
    convert hconj using 1
    group
  let S : Type := ↥(kGenIn V H) ⧸ I.subgroupOf (kGenIn V H)
  let ψ : ↥(kGenIn V H) →* S := QuotientGroup.mk' (I.subgroupOf (kGenIn V H))
  let ρ : ↥H →* MulAut S :=
    (conjHom (A := kGenIn V H) (B := I)).comp
      (Subgroup.inclusion (le_inf (h.le_normalizer_kGenIn_of_eq_sup hKT) hHnormI))
  let t₀ : S := ψ vh
  have hs₀v : φ vh ∈ barSub (kGenIn V H) φ V := mem_barSub.mpr ⟨vh, hv₀V, rfl⟩
  have hs₀ne : φ vh ≠ 1 := by
    intro h1
    exact hv₀E (h.pCoreOf_kGenIn_le_centralizer_eSub ((hφ.ker_iff vh).mp h1))
  have hcard : Nat.card (barSub (kGenIn V H) φ V) = 2 := by
    rw [h.card_barSub_eq_two_pow_rankBarV hKT hφ, hrk]
    norm_num
  refine ⟨S, inferInstance, ψ, ρ, t₀, h, hKT, hrk, QuotientGroup.mk'_surjective _, ?_, ?_, ?_,
    ?_⟩
  · intro k
    dsimp only [ψ]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hmemI]
  · intro y k x hyx
    dsimp only [ρ, ψ]
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, conjHom_mk]
    congr 1
    apply Subtype.ext
    rw [coe_conjA, Subgroup.coe_inclusion]
    exact hyx.symm
  · intro v hvV hvE
    have hsv : φ v ∈ barSub (kGenIn V H) φ V := mem_barSub.mpr ⟨v, hvV, rfl⟩
    have hsne : φ v ≠ 1 := by
      intro h1
      exact hvE (h.pCoreOf_kGenIn_le_centralizer_eSub ((hφ.ker_iff v).mp h1))
    obtain ⟨y, _, hyuniq⟩ :=
      (Nat.card_eq_two_iff' (1 : barSub (kGenIn V H) φ V)).mp hcard
    have hsv' : (⟨φ v, hsv⟩ : barSub (kGenIn V H) φ V) ≠ 1 := fun hh =>
      hsne (Subtype.ext_iff.mp hh)
    have hs₀v' : (⟨φ vh, hs₀v⟩ : barSub (kGenIn V H) φ V) ≠ 1 := fun hh =>
      hs₀ne (Subtype.ext_iff.mp hh)
    have heq : φ v = φ vh := congrArg Subtype.val
      ((hyuniq ⟨φ v, hsv⟩ hsv').trans ((hyuniq ⟨φ vh, hs₀v⟩ hs₀v').symm))
    have hψ₀eq : ψ₀ v = ψ₀ vh := by
      change (QuotientGroup.mk' (Subgroup.center X)) (φ v) =
        (QuotientGroup.mk' (Subgroup.center X)) (φ vh)
      rw [heq]
    have hmem : vh⁻¹ * v ∈ I.subgroupOf (kGenIn V H) := by
      rw [Subgroup.mem_subgroupOf, hmemI, ← hψ₀ker (vh⁻¹ * v), map_mul, map_inv, hψ₀eq,
        inv_mul_cancel]
    have hψmem : ψ (vh⁻¹ * v) = 1 := by
      dsimp only [ψ]
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hmem
    have hψv : ψ v = ψ vh := by
      conv_lhs => rw [← mul_inv_cancel_left vh v]
      rw [map_mul, hψmem, mul_one]
    exact hψv
  · rcases hroot with ⟨hm2, hsymp⟩ | ⟨hm3, hunit⟩
    · obtain ⟨k, hk, F, hField, hFinite, hF, e₀, ht⟩ := hsymp (φ vh) hs₀v hs₀ne
      have hk1 : 1 ≤ k := by omega
      let e : S ≃* ↥(StatedSp k F) :=
        (QuotientGroup.quotientMulEquivOfEq hIN₀).trans
          ((QuotientGroup.liftEquiv (N := N₀) (φ := ψ₀) hψ₀surj rfl).trans e₀)
      have hee : e t₀ = e₀ (QuotientGroup.mk (φ vh)) := by
        dsimp only [e, t₀, ψ]
        rw [MulEquiv.trans_apply, MulEquiv.trans_apply, QuotientGroup.mk'_apply,
          QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.liftEquiv_mk]
        rfl
      exact BorelLieFacts.of_mulEquiv e (hee.symm ▸ borelLieFacts_sp hF hn hk1 ht)
    · obtain ⟨F, hField, hFinite, hF, e₀, ht⟩ := hunit (φ vh) hs₀v hs₀ne
      let e : S ≃* StatedProj (StatedSU m (2 ^ n) F) :=
        (QuotientGroup.quotientMulEquivOfEq hIN₀).trans
          ((QuotientGroup.liftEquiv (N := N₀) (φ := ψ₀) hψ₀surj rfl).trans e₀)
      have hee : e t₀ = e₀ (QuotientGroup.mk (φ vh)) := by
        dsimp only [e, t₀, ψ]
        rw [MulEquiv.trans_apply, MulEquiv.trans_apply, QuotientGroup.mk'_apply,
          QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.liftEquiv_mk]
        rfl
      exact BorelLieFacts.of_mulEquiv e (hee.symm ▸ borelLieFacts_psu hF hn hm3 ht)

end CFSG.LocalAnalysis.WeakClosure81

end

module

public import CFSG.Quasithin.Background.F918Fine4PfHat6M
public import CFSG.Quasithin.Background.F918Fine4PfCore
public import CFSG.Quasithin.Background.F918Fine4Hat6
public import CFSG.Quasithin.Background.SmithB45HatA6
public import CFSG.Quasithin.Background.F918Fine4PfIrr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace F918Fine4Pf

section Module

private theorem sec_sq_eq_one_h6 {Y : Type} [CommGroup Y] (hY : ∀ y : Y, y ^ 2 = 1)
    (A C : Subgroup Y) : ∀ q : Sec A C, q ^ 2 = 1 := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow, show a ^ 2 = 1 from Subtype.ext (by simpa using hY a),
      QuotientGroup.mk_one]

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem hat6_card_and_model (hA21 : AsA21SQTKSection) {Q : Type} [Group Q]
    (hM : HatMod M Mp T L V Q) (hQ : IsHat Q ↥(alternatingGroup (Fin 6))) :
    Nat.card V = 2 ^ 6 ∧ TripleA6Six (autSub L V) ⊤ ⊥ := by
  obtain ⟨hD, hMp, hT, -, hfix, -, ⟨e⟩⟩ := hM
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD.hyp hT
  have hQS := lred3_qsec hD.hyp hMp hO2
  have hb4 := lred3_b4Hyp hA21 hD.hyp hMp hO2
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
  have hsv : ∀ v : Sec (⊤ : Subgroup ↥V) ((V ⊓ fixV Mp).subgroupOf V), v ^ 2 = 1 :=
    sec_sq_eq_one_h6 hexp ⊤ _
  let e₃ := B5.secEquiv (autSub L V) (InternalSec.le_stabSub_top _) hQS.stabKC hQS.faithful
  have hP : IsHat ↥(autSec (autSub L V) ⊤ ((V ⊓ fixV Mp).subgroupOf V))
      ↥(alternatingGroup (Fin 6)) := IsHat.of_mulEquiv (e.symm.trans e₃) hQ
  have hqh := lred3_qhatOf_autSec hD hMp hT
  have hq1 := asB45HatA6_holds _ hsv _ _ hb4 hP hqh
  obtain ⟨A, hA, -, hr⟩ := kq_le_iff.mp hq1
  obtain ⟨B, -, hB, -⟩ := B1_4_4_le hsv hA hr
  have hcard := HatA6.card_V hsv hb4 hP hB
  have hC : (V ⊓ fixV Mp).subgroupOf V = ⊥ := by
    rw [hMp, hfix, Subgroup.bot_subgroupOf]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (((V ⊓ fixV Mp).subgroupOf V).subgroupOf (⊤ : Subgroup ↥V))
  have h2 : Nat.card ↥(((V ⊓ fixV Mp).subgroupOf V).subgroupOf (⊤ : Subgroup ↥V)) = 1 := by
    rw [hC, Subgroup.bot_subgroupOf, Subgroup.card_bot]
  rw [h2, mul_one, Subgroup.card_top] at h1
  have hcV : Nat.card V = 2 ^ 6 := h1.trans hcard
  obtain ⟨hq, hZ, ⟨eA⟩⟩ := IsHat.of_mulEquiv e.symm hQ
  exact ⟨hcV, HatA6.hatA6SixModel ↥V hexp hcV (autSub L V) hq.1 hZ ⟨eA⟩⟩

end Module

section Group

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem card_of_isHat_alt6 {Q : Type} [Group Q] [Finite Q]
    (hQ : IsHat Q ↥(alternatingGroup (Fin 6))) : Nat.card Q = 1080 := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := hQ
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q), hZ,
    Nat.card_congr e.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
  norm_num [Nat.factorial]

theorem mem_center_iff_of_surjective {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (a : A) :
    f a ∈ Subgroup.center B ↔ ∀ w : A, a * w * a⁻¹ * w⁻¹ ∈ f.ker := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hc w
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hc (f w)]
    group
  · intro hc b
    obtain ⟨w, rfl⟩ := hf b
    have h1 := hc w
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 : f a * f w = f w * f a := by
      have := congrArg (· * (f w * f a)) h1
      simpa [mul_assoc] using this
    exact h2.symm

theorem ker_toAutI_eq_pCore (h : HypF918 T V L V₁ Vp H K) :
    (toAutI h Vp).ker = CFSG.pCore 2 ↥K := by
  have hF := factElem h (le_conjClosure Vp H)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  apply le_antisymm
  · have hle : (toAutI h Vp).ker ≤ (pCoreOf 2 H).subgroupOf K := by
      intro x hx
      rw [MonoidHom.mem_ker, toAutI_eq_one_iff] at hx
      exact Subgroup.mem_subgroupOf.mpr (mem_pCoreOf_of_actH_eq_one h hx)
    have h2 : IsPGroup 2 ↥(toAutI h Vp).ker :=
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).comap_subtype (K := K)).to_le hle
    exact le_sSup ⟨inferInstance, h2⟩
  · intro x hx
    rw [MonoidHom.mem_ker, toAutI_eq_one_iff]
    apply h.actH_eq_one_of_mem_pCoreOf (le_conjClosure Vp H)
    have hx' : x ∈ CFSG.Open.pCore 2 ↥K := by
      assumption
    have hx1 : (x : G) ∈ pCoreOf 2 K := ⟨x, hx', rfl⟩
    exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp h.K_cComp) hx1

omit [Finite G] in
theorem mem_oTwoZIn_iff_pCore {y : ↥K} :
    (y : G) ∈ oTwoZIn K ↔ ∀ w : ↥K, y * w * y⁻¹ * w⁻¹ ∈ CFSG.pCore 2 ↥K := by
  unfold oTwoZIn preimageModTwoCore
  rw [show (y : G) = K.subtype y from rfl, Subgroup.mem_map_iff_mem K.subtype_injective,
    Subgroup.mem_comap, mem_center_iff_of_surjective _ (QuotientGroup.mk'_surjective _),
    QuotientGroup.ker_mk']

theorem f918Fine4Hat6_of (h310 : D310) (h391 : D391) (hA21 : AsA21SQTKSection) :
    F918Fine4Hat6 := by
  intro G _ _ T V L V₁ Vp H K h hH hK hHat t ht hfuse
  obtain ⟨x, hxK, hx3, hx1, hall⟩ := hfuse
  have hFU := factElem h (le_conjClosure Vp H)
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hTH : T ≤ H := h.T_le_H
  have hHN : H ≤ Subgroup.normalizer (K : Set G) := hK ▸ h.K₀_normal
  have hcard := card_of_isHat_alt6 hHat
  have hZ : Subgroup.center ↥(autIH V₁ Vp H K) ≠ ⊥ := by
    intro hb
    have hZ3 := hHat.2.1
    rw [hb, Subgroup.card_bot] at hZ3
    omega
  obtain ⟨I, hV₁I, hIU, ⟨W, hW, hirr⟩, hfpf⟩ := exists_irrPlus_fixFree h hK hZ
  obtain ⟨-, hcore⟩ :=
    hatCore_of h hH hK h310 h391 hV₁I hIU W hW hirr hfpf hHat.1 hHat.2.1 (Or.inr hcard)
  have hFI := factElem h hIU
  obtain ⟨hM, hker⟩ := hcore
  obtain ⟨hcardV, -⟩ := hat6_card_and_model hA21 hM hHat
  obtain ⟨hD, hMp, hTst, -, hfix, hfaith, ⟨e⟩⟩ := hM
  have hV₁N := h.H_le_normalizer_V₁
  have hIH : H ≤ Subgroup.normalizer (conjClosure I H : Set G) := le_normalizer_conjClosure I H
  have hLs : autIH V₁ I H K ≤ stabSub (subM V₁ (conjClosure I H) I) := insp5a_le_stabSub hD.hyp
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD.hyp hTst
  have hQS := lred3_qsec hD.hyp hMp hO2
  set f : ↥(autIH V₁ I H K) →* ↥(autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) :=
    (MulEquiv.subgroupCongr (autSub_eq_range_resHomOn hLs)).symm.toMonoidHom.comp
      (resHomOn (subM V₁ (conjClosure I H) I) hLs).rangeRestrict with hfdef
  set θ := f.comp (toAutI h I) with hθdef
  have hθs : Function.Surjective θ := by
    intro y
    obtain ⟨r, hr⟩ := (MulEquiv.subgroupCongr (autSub_eq_range_resHomOn hLs)).symm.surjective y
    obtain ⟨l, hl⟩ := MonoidHom.rangeRestrict_surjective
      (resHomOn (subM V₁ (conjClosure I H) I) hLs) r
    obtain ⟨k, hk⟩ := toAutI_surjective h I l
    refine ⟨k, ?_⟩
    simp only [hθdef, hfdef, MonoidHom.comp_apply, hk, hl, MulEquiv.coe_toMonoidHom, hr]
  have hρinj : Function.Injective (resHomOn (subM V₁ (conjClosure I H) I) hLs) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro l hl
    have hlc : (l : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈
        centSub (subM V₁ (conjClosure I H) I) := by
      intro v hv
      exact congrArg (fun φ : MulAut ↥(subM V₁ (conjClosure I H) I) =>
        ((φ ⟨v, hv⟩ : ↥(subM V₁ (conjClosure I H) I)) : ↥(tildeOf V₁ (conjClosure I H))))
        (MonoidHom.mem_ker.mp hl)
    have h1 : (l : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈
        autIH V₁ I H K ⊓ centSub (subM V₁ (conjClosure I H) I) := ⟨l.2, hlc⟩
    rw [hfaith, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have hfinj : Function.Injective f := by
    intro a b hab
    simp only [hfdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hab
    exact hρinj (congrArg Subtype.val ((MulEquiv.injective _) hab))
  have hθker : θ.ker = CFSG.pCore 2 ↥K := by
    rw [← ker_toAutI_eq_pCore h, ← hker]
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hθdef, MonoidHom.comp_apply, map_eq_one_iff _ hfinj]
  have hθZ : ∀ y : ↥K, θ y ∈ Subgroup.center ↥(autSub (autIH V₁ I H K)
      (subM V₁ (conjClosure I H) I)) ↔ (y : G) ∈ oTwoZIn K := by
    intro y
    rw [mem_center_iff_of_surjective θ hθs, hθker, mem_oTwoZIn_iff_pCore]
  set x₀ : ↥K := ⟨x, hxK⟩ with hx₀
  have hx3' : θ x₀ ^ 3 ∈ Subgroup.center ↥(autSub (autIH V₁ I H K)
      (subM V₁ (conjClosure I H) I)) := by
    rw [← map_pow]
    exact (hθZ (x₀ ^ 3)).mpr hx3
  have hx1' : θ x₀ ∉ Subgroup.center ↥(autSub (autIH V₁ I H K)
      (subM V₁ (conjClosure I H) I)) := fun h1 => hx1 ((hθZ x₀).mp h1)
  have htH : t ∈ H := hTH ht
  have hat : actH hV₁N hIH ⟨t, htH⟩ ∈ autIH V₁ I H T := by
    rw [autIH_eq_map h hTH]
    exact ⟨⟨t, htH⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  set at' : ↥(stabSub (subM V₁ (conjClosure I H) I)) :=
    ⟨actH hV₁N hIH ⟨t, htH⟩, hTst hat⟩ with hat'
  set g : MulAut ↥(subM V₁ (conjClosure I H) I) := resHom _ at' with hg
  have hgX : g ∈ autSub (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
      (subM V₁ (conjClosure I H) I) :=
    mem_autSub.mpr ⟨at', (le_sup_right : autIH V₁ I H T ≤ _ ⊔ autIH V₁ I H T) hat, rfl⟩
  have hgN : ∀ l, l ∈ autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I) ↔
      g * l * g⁻¹ ∈ autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I) := by
    intro l
    constructor
    · intro hl
      exact hQS.normal g hgX l hl
    · intro hl
      have h1 := hQS.normal g⁻¹ (inv_mem hgX) _ hl
      have e1 : g⁻¹ * (g * l * g⁻¹) * g⁻¹⁻¹ = l := by group
      rwa [e1] at h1
  have hexp : ∀ w : ↥(subM V₁ (conjClosure I H) I), w ^ 2 = 1 :=
    fun w => Subtype.ext (by simp [hD.hyp.exp])
  obtain ⟨hqK, hZK, ⟨eK⟩⟩ := IsHat.of_mulEquiv e.symm hHat
  have hC : ((subM V₁ (conjClosure I H) I) ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
      (subM V₁ (conjClosure I H) I) = ⊥ := by
    rw [hMp, hfix, Subgroup.bot_subgroupOf]
  have hirrV : ∀ J : Subgroup ↥(subM V₁ (conjClosure I H) I),
      (∀ l ∈ autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I), ∀ v ∈ J, l v ∈ J) →
        J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    have h1 := hQS.irr J (hC ▸ bot_le) hJ
    rwa [hC] at h1
  obtain ⟨l, hl⟩ := exists_conj_mod_center hexp hcardV hqK.1 hZK eK hirrV hgN hx3' hx1'
  obtain ⟨k, rfl⟩ := hθs l
  have htx : t * x * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hHN htH) x).mp hxK
  have hθc : ∀ y : ↥K, (θ y : MulAut ↥(subM V₁ (conjClosure I H) I)) =
      resHom _ ⟨actH hV₁N hIH (Subgroup.inclusion hKH y), hLs (toAutI h I y).2⟩ := fun y => rfl
  have hcompat : (⟨g * (θ x₀ : MulAut ↥(subM V₁ (conjClosure I H) I)) * g⁻¹,
      (hgN _).1 (θ x₀).2⟩ : ↥(autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I))) =
      θ ⟨t * x * t⁻¹, htx⟩ := by
    apply Subtype.ext
    show g * (θ x₀ : MulAut ↥(subM V₁ (conjClosure I H) I)) * g⁻¹ =
      (θ ⟨t * x * t⁻¹, htx⟩ : MulAut ↥(subM V₁ (conjClosure I H) I))
    rw [hθc, hθc, hg]
    have e3 : at' * ⟨actH hV₁N hIH (Subgroup.inclusion hKH x₀), hLs (toAutI h I x₀).2⟩ *
        at'⁻¹ = ⟨actH hV₁N hIH (Subgroup.inclusion hKH ⟨t * x * t⁻¹, htx⟩),
          hLs (toAutI h I ⟨t * x * t⁻¹, htx⟩).2⟩ := by
      apply Subtype.ext
      simp only [hat', Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    rw [← e3, map_mul, map_mul, map_inv]
  rw [hcompat] at hl
  have e4 : θ ((k * x₀ * k⁻¹)⁻¹ * ⟨t * x * t⁻¹, htx⟩) =
      (θ k * θ x₀ * (θ k)⁻¹)⁻¹ * θ ⟨t * x * t⁻¹, htx⟩ := by
    simp only [map_mul, map_inv]
  have h2 : θ ((k * x₀ * k⁻¹)⁻¹ * ⟨t * x * t⁻¹, htx⟩) ∈ Subgroup.center ↥(autSub
      (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) := by
    rw [e4]
    exact hl
  have h3 := (hθZ _).mp h2
  have e5 : (((k * x₀ * k⁻¹)⁻¹ * ⟨t * x * t⁻¹, htx⟩ : ↥K) : G) =
      ((k : G) * x * (k : G)⁻¹)⁻¹ * (t * x * t⁻¹) := by
    rw [hx₀]
    rfl
  rw [e5] at h3
  exact hall (k : G) k.2 h3

end Group

end F918Fine4Pf

end CFSG.Quasithin

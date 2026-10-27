module

public import CFSG.Quasithin.MS93.M15WeylQ
public import CFSG.Quasithin.Background.SmithB42G2Nat
public import CFSG.Quasithin.Background.SmithB51Sp4Sec
public import CFSG.Quasithin.Vol2.Ch12Sec4G2NormZorn

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.Ch11.G2Q8

section Act

variable {F : Type} [Field F] [CharP F 2] {Z : Subgroup (Multiplicative (quasithinZorn F))}

omit [CharP F 2] in
theorem zornAct_R (γ : ↥(quasithinG2 F)) {m : Multiplicative (quasithinZorn F)}
    (hm : m ∈ zornR F) : zornAct (quasithinG2 F) γ m = m := by
  obtain ⟨c, hc⟩ := hm
  show Multiplicative.ofAdd ((γ : quasithinZorn F ≃ₗ[F] quasithinZorn F)
    (Multiplicative.toAdd m)) = m
  rw [hc, (mem_quasithinG2_isZornAuto γ.2).map_smul_one c, ← hc]
  rfl

theorem zornWeylQuot_isActionModel (hZ : Z ≤ zornR F) :
    (zornWeylQuot (quasithinG2 F) Z).IsActionModel where
  act_mul := zornAct_mul (quasithinG2 F)
  act_one := zornAct_one (quasithinG2 F)
  act_mul_act := zornAct_mul_act (quasithinG2 F)
  sec_inv := fun γ _ hm => zornAct_mem_O0 (quasithinG2 F) le_rfl γ hm
  ker_inv := fun γ m hm => by
    show zornAct (quasithinG2 F) γ m ∈ Z
    rw [zornAct_R γ (hZ hm)]
    exact hm
  ker_le := hZ.trans CFSG.Quasithin.zornR_le_zornO0

@[expose] noncomputable def weylAct (hZ : Z ≤ zornR F) :
    ↥(cayleyGroup F) →* MulAut (WeylQ F Z) :=
  (zornWeylQuot_isActionModel hZ).modAct.comp
    (MulEquiv.subgroupCongr G11.P3G2.quasithinG2_eq_cayleyGroup.symm).toMonoidHom

theorem isWeylAct_weylAct (hZ : Z ≤ zornR F) : IsWeylAct Z (weylAct hZ) := fun _ _ _ => rfl

theorem realizeEquiv_weyl {W : Type} [CommGroup W] (hZ : Z ≤ zornR F) {L₀ : Subgroup (MulAut W)}
    {π : ↥(quasithinG2 F) →* ↥L₀} {β : ↥(⊤ : Subgroup W) →* WeylQ F Z}
    (h : H.Mathieu.RealizesBy (zornWeylQuot (quasithinG2 F) Z) L₀ ⊤ ⊥ π β)
    (γ : ↥(quasithinG2 F)) (w : W) :
    H13.realizeEquiv h ((π γ : MulAut W) w) =
      (zornWeylQuot_isActionModel hZ).modAct γ (H13.realizeEquiv h w) := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨w, trivial⟩)
  have hm' : (zornWeylQuot (quasithinG2 F) Z).act γ (m : Multiplicative (quasithinZorn F)) ∈
      (zornWeylQuot (quasithinG2 F) Z).sec :=
    zornAct_mem_O0 (quasithinG2 F) le_rfl γ m.2
  have h1 := h.2.2.2.2.2.2.2.2.2 γ ⟨w, trivial⟩ m trivial hm' hm.symm
  change β ⟨(π γ : MulAut W) w, trivial⟩ =
    (zornWeylQuot_isActionModel hZ).modAct γ (β ⟨w, trivial⟩)
  rw [← hm]
  exact h1

end Act

section Cases

variable {V : Type} [CommGroup V] [Finite V] {X K : Subgroup (MulAut V)}

theorem MS15Hyp.offender_quot (hV : ∀ v : V, v ^ 2 = 1) (h : MS15Hyp X K)
    {A : Subgroup (MulAut V)} (hAX : A ≤ X) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A)
    (hcard : Nat.card V ≤ Nat.card A * Nat.card ↥(fixQuot A (fixV K))) :
    autSec A ⊤ (fixV K) ≠ ⊥ ∧ IsElemAbelian2 (autSec A ⊤ (fixV K)) ∧
      Nat.card (Sec (⊤ : Subgroup V) (fixV K)) ≤
        Nat.card (autSec A ⊤ (fixV K)) * Nat.card (fixV (autSec A ⊤ (fixV K))) := by
  have hAW : A ≤ stabSub (⊤ : Subgroup V) := MS15Hyp.le_stabSub_top A
  have hAC : A ≤ stabSub (fixV K) := hAX.trans h.le_stabSub
  have hfA := h.faithful_le hV hAX
  have hcA : Nat.card (autSec A ⊤ (fixV K)) = Nat.card A := by
    have := card_autSec_mul hAW hAC
    rwa [hfA, Subgroup.card_bot, mul_one] at this
  have hfix : Nat.card (fixV (autSec A ⊤ (fixV K))) * Nat.card (fixV K) =
      Nat.card (fixQuot A (fixV K)) := by
    have e : B5.fixSec A ⊤ (fixV K) = fixQuot A (fixV K) := by
      ext v
      exact ⟨fun hv => hv.2, fun hv => ⟨Subgroup.mem_top v, hv⟩⟩
    rw [B5.card_fixV_autSec_mul le_top hAW hAC, e]
  have hsec : Nat.card V = Nat.card (Sec (⊤ : Subgroup V) (fixV K)) * Nat.card (fixV K) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_top : fixV K ≤ ⊤)).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup, Subgroup.card_top]
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro hbot
    apply hA1
    have h1 : Nat.card A = 1 := by rw [← hcA, hbot, Subgroup.card_bot]
    exact Subgroup.eq_bot_of_card_eq A h1
  · intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := (h.mem_autSec_iff hAX).1 ha
    obtain ⟨y, hy, rfl⟩ := (h.mem_autSec_iff hAX).1 hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAe.1 _ hx _ hy)
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := (h.mem_autSec_iff hAX).1 ha
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (by simpa using hAe.2 _ hx)
    rw [this, map_one]
  · have hpos : 0 < Nat.card (fixV K) := Nat.card_pos
    rw [hcA]
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [mul_assoc, hfix, ← hsec]
    exact hcard

theorem MS15Hyp.offender_le_g2 (hV : ∀ v : V, v ^ 2 = 1) (h : MS15Hyp X K) {n : ℕ} (hn : 2 ≤ n)
    (hG : G2Natural K ⊤ (fixV K) n) {A : Subgroup (MulAut V)} (hAX : A ≤ X) (hA1 : A ≠ ⊥)
    (hAe : IsElemAbelian2 A)
    (hcard : Nat.card V ≤ Nat.card A * Nat.card ↥(fixQuot A (fixV K))) : A ≤ K := by
  obtain ⟨F₁, iF₁, fF₁, hF₁, π₁, hπ₁⟩ := hG
  have : Fintype F₁ := Fintype.ofFinite F₁
  have hFc : Fintype.card F₁ = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hF₁]
  have : CharP F₁ 2 := charP_of_card_eq_prime_pow hFc
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hF₁
  have heq : ⁅quasithinG2 F₁, quasithinG2 F₁⁆ = quasithinG2 F₁ :=
    (g2Derived_eq hc0 hc1).trans
      CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup.symm
  have hR : (FFModel.zornQ (quasithinG2 F₁)).Realizes (autSec K ⊤ (fixV K)) ⊤ ⊥ :=
    ⟨_, FFC.Sp4Off.realizesVia_autSec (MS15Hyp.le_stabSub_top K) (h.le.trans h.le_stabSub)
      (h.faithful_le hV h.le) hπ₁⟩
  have hR' : (FFModel.zornQ ⁅quasithinG2 F₁, quasithinG2 F₁⁆).Realizes
      (autSec K ⊤ (fixV K)) ⊤ ⊥ := by
    rw [heq]
    exact hR
  obtain ⟨π', hπ'⟩ := hR'
  obtain ⟨fc, hfc⟩ := Vol2.KGNat.exists_isCoord (lmG F₁) hπ'
  obtain ⟨hĀ1, hĀe, hĀcard⟩ := h.offender_quot hV hAX hA1 hAe hcard
  have hĀN : autSec A ⊤ (fixV K) ≤ Subgroup.normalizer (autSec K ⊤ (fixV K) : Set _) :=
    (autSec_mono hAX ⊤ (fixV K)).trans (h.ffHyp hV).le_normalizer
  obtain ⟨hĀK, -, -⟩ := (B42G2.offender_facts hF₁ hn hfc hĀN hĀe).2 hĀ1 hĀcard
  intro a ha
  have h1 : B5.secHom X (MS15Hyp.le_stabSub_top X) h.le_stabSub ⟨a, hAX ha⟩ ∈
      autSec K ⊤ (fixV K) := hĀK ((h.mem_autSec_iff hAX).2 ⟨⟨a, hAX ha⟩, ha, rfl⟩)
  obtain ⟨k, hk, hka⟩ := (h.mem_autSec_iff h.le).1 h1
  have hk' := h.secHom_injective hV hka
  rw [hk'] at hk
  exact hk

theorem g2Comm_large (hV : ∀ v : V, v ^ 2 = 1) (h : MS15Hyp X K) {n : ℕ} (hn : 2 ≤ n)
    (hG : G2Natural K ⊤ (fixV K) n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n)
    {Z : Subgroup (Multiplicative (quasithinZorn F))} (hZ : Z ≤ zornR F)
    (hR : (zornWeylQuot (quasithinG2 F) Z).Realizes K ⊤ ⊥) {A : Subgroup (MulAut V)}
    (hAX : A ≤ X) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A)
    (hcard : Nat.card V ≤ Nat.card A * Nat.card ↥(fixQuot A (fixV K))) (v : V) :
    (v ∈ fixV K ∧ v ≠ 1) ↔ (v ∈ commV A ∧ ∀ a ∈ A, ∀ w : V, a w * w⁻¹ ≠ v) := by
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := charP_of_card_eq_prime_pow hFc
  have hAK := h.offender_le_g2 hV hn hG hAX hA1 hAe hcard
  obtain ⟨π, β, hβ⟩ := (H.Mathieu.realizes_iff _ K ⊤ ⊥).1 hR
  set e : V ≃* WeylQ F Z := H13.realizeEquiv (D := zornWeylQuot (quasithinG2 F) Z) hβ with he
  set ι : ↥(cayleyGroup F) ≃* ↥(quasithinG2 F) :=
    MulEquiv.subgroupCongr G11.P3G2.quasithinG2_eq_cayleyGroup.symm with hι
  have hρ := isWeylAct_weylAct (F := F) hZ
  have heq : ∀ (g : ↥(quasithinG2 F)) (w : V),
      e ((π g : MulAut V) w) = weylAct hZ (ι.symm g) (e w) := by
    intro g w
    have h2 : weylAct hZ (ι.symm g) = (zornWeylQuot_isActionModel hZ).modAct g := by
      show (zornWeylQuot_isActionModel hZ).modAct (ι (ι.symm g)) = _
      rw [MulEquiv.apply_symm_apply]
    rw [h2]
    exact realizeEquiv_weyl hZ hβ g w
  have hcongr : ∀ g : ↥(quasithinG2 F),
      MulAut.congr e (π g : MulAut V) = weylAct hZ (ι.symm g) := by
    intro g
    ext q
    obtain ⟨w, rfl⟩ := e.surjective q
    rw [H13.congr_apply_eq, heq]
  have hAρ : A.map (MulAut.congr e).toMonoidHom ≤ (weylAct hZ).range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨g, hg⟩ := hβ.1 ⟨a, hAK ha⟩
    refine ⟨ι.symm g, ?_⟩
    rw [← hcongr g, hg]
    rfl
  have hC : ∀ v, v ∈ fixV K ↔ e v ∈ rbar Z := by
    intro v
    constructor
    · intro hv
      refine hρ.mem_rbar_of_fixed hZ fun γ => ?_
      have h1 := heq (ι γ) v
      rw [MulEquiv.symm_apply_apply, (mem_fixV.1 hv) _ (π (ι γ)).2] at h1
      exact h1.symm
    · intro hv
      rw [mem_fixV]
      intro k hk
      obtain ⟨g, hg⟩ := hβ.1 ⟨k, hk⟩
      apply e.injective
      have h1 : e (k v) = weylAct hZ (ι.symm g) (e v) := by
        have h2 := heq g v
        rwa [hg] at h2
      rw [h1, hρ.fix_rbar _ hv]
  exact comm_char_of_equiv hF (by omega) hZ hρ e hAρ hA1 hAe hC hcard v

theorem g2Comm_two
    (h : MS15Hyp X K) (hC2 : Nat.card (fixV K) = 2)
    (hV7 : Nat.card V = 2 ^ 7) (hW : H13.G2WeylDerived K) {A : Subgroup (MulAut V)}
    (hAX : A ≤ X) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A)
    (hcard : Nat.card V ≤ Nat.card A * Nat.card ↥(fixQuot A (fixV K))) (v : V) :
    (v ∈ fixV K ∧ v ≠ 1) ↔ (v ∈ commV A ∧ ∀ a ∈ A, ∀ w : V, a w * w⁻¹ ≠ v) := by
  obtain ⟨F, iF, fF, hF2, hR⟩ := hW
  have := H13.charP_two_of_natCard_two hF2
  obtain ⟨π, β, hβ⟩ := (H.Mathieu.realizes_iff _ K ⊤ ⊥).1 hR
  set e : V ≃* (H13.zornO0Model (quasithinG2 F)).Mod :=
    H13.realizeEquiv (D := H13.zornO0Model ⁅quasithinG2 F, quasithinG2 F⁆) hβ with he
  set ι : ↥(cayleyGroup F) ≃* ↥(quasithinG2 F) :=
    MulEquiv.subgroupCongr G11.P3G2.quasithinG2_eq_cayleyGroup.symm with hι
  have hLe : K.map (MulAut.congr e).toMonoidHom = (H13.g2Derived F).map (H13.g2OAct F) :=
    H13.map_congr_eq_of_equivariant e π hβ.1 (H13.g2OAct F)
      (fun γ => ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩) (H13.realizeEquiv_zornO0 hβ) _
      (H13.mem_map_g2Derived_iff (H13.g2OAct F))
  have hN := (H13.g2DerivedNormalizerZorn F hF2).2
  have hle' : A.map (MulAut.congr e).toMonoidHom ≤ (H13.g2OAct F).range := by
    rintro _ ⟨a, ha, rfl⟩
    apply hN
    intro x
    have hx := Subgroup.mem_set_normalizer_iff.1 (h.le_normalizer (hAX ha))
    rw [← hLe]
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨a * l * a⁻¹, (hx l).1 hl, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · rintro ⟨l, hl, hl'⟩
      refine ⟨a⁻¹ * l * a, ?_, ?_⟩
      · have e1 : a * (a⁻¹ * l * a) * a⁻¹ = l := by group
        exact (hx _).2 (by rw [e1]; exact hl)
      · rw [map_mul, map_mul, map_inv, hl']
        group
  have hK' : ∀ k ∈ K, ∃ g : ↥(quasithinG2 F), ∀ w, e (k w) = H13.g2OAct F g (e w) := by
    intro k hk
    obtain ⟨g, -, hg⟩ : MulAut.congr e k ∈ (H13.g2Derived F).map (H13.g2OAct F) := by
      rw [← hLe]
      exact ⟨k, hk, rfl⟩
    refine ⟨g, fun w => ?_⟩
    have hg' : MulAut.congr e k = H13.g2OAct F g := hg.symm
    rw [← hg', H13.congr_apply_eq]
  set e₂ : V ≃* WeylQ F ⊥ := e with he₂
  set ρ : ↥(cayleyGroup F) →* MulAut (WeylQ F ⊥) := (H13.g2OAct F).comp ι.toMonoidHom
    with hρdef
  have hρ : IsWeylAct ⊥ ρ := fun _ _ _ => rfl
  have hle : A.map (MulAut.congr e₂).toMonoidHom ≤ ρ.range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨g, hg⟩ := hle' ⟨a, ha, rfl⟩
    refine ⟨ι.symm g, ?_⟩
    show H13.g2OAct F (ι (ι.symm g)) = (MulAut.congr e).toMonoidHom a
    rw [MulEquiv.apply_symm_apply]
    exact hg
  have hK₂ : ∀ k ∈ K, ∃ γ : ↥(cayleyGroup F), ∀ w, e₂ (k w) = ρ γ (e₂ w) := by
    intro k hk
    obtain ⟨g, hg⟩ := hK' k hk
    refine ⟨ι.symm g, fun w => ?_⟩
    show e (k w) = H13.g2OAct F (ι (ι.symm g)) (e w)
    rw [MulEquiv.apply_symm_apply]
    exact hg w
  have hfixR : ∀ v, e₂ v ∈ rbar ⊥ → v ∈ fixV K := by
    intro v hv
    rw [mem_fixV]
    intro k hk
    obtain ⟨γ, hγ⟩ := hK₂ k hk
    apply e₂.injective
    rw [hγ, hρ.fix_rbar γ hv]
  have hcR : Nat.card (rbar (⊥ : Subgroup (Multiplicative (quasithinZorn F)))) = 2 := by
    have h1 := card_weylQ (F := F) (Z := ⊥) bot_le
    have h2 : Nat.card V = Nat.card (WeylQ F ⊥) := Nat.card_congr e₂.toEquiv
    rw [← h2, hV7, hF2] at h1
    norm_num at h1
    omega
  have hS : (rbar ⊥).comap e₂.toMonoidHom = fixV K := by
    refine Subgroup.eq_of_le_of_card_ge (fun v hv => hfixR v hv) ?_
    have h1 := card_comap_eq_mul (f := e₂.toMonoidHom) e₂.surjective (rbar ⊥)
    rw [(MonoidHom.ker_eq_bot_iff _).2 e₂.injective, Subgroup.card_bot, mul_one, hcR] at h1
    rw [h1, hC2]
  have hC : ∀ v, v ∈ fixV K ↔ e₂ v ∈ rbar ⊥ := by
    intro v
    rw [← hS]
    rfl
  exact comm_char_of_equiv (hF2.trans (pow_one 2).symm) le_rfl bot_le hρ e₂ hle hA1 hAe hC hcard v

end Cases

theorem ms15G2Comm_holds :
    MS15G2Comm := by
  intro V _ _ hV X K h hcase A hAX hA1 hAe hcard v
  rcases hcase with ⟨n, hn, hG, -, F, iF, fF, hF, Z, hZ, hR⟩ | ⟨-, -, -, hC2, hV7, hW⟩
  · exact g2Comm_large hV h hn hG hF hZ hR hAX hA1 hAe hcard v
  · exact g2Comm_two h hC2 hV7 hW hAX hA1 hAe hcard v

end CFSG.Quasithin.MS93

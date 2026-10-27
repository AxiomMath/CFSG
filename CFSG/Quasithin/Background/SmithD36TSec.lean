module

public import CFSG.Quasithin.Background.SmithD36TUeqV
public import CFSG.Quasithin.Background.SmithD36TB42
public import CFSG.Quasithin.Background.SmithD36TA5
public import CFSG.Quasithin.Background.F918J2
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Background.F918D2
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.Background.InternalSecReal

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

section Data

theorem d36t_hN (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    (Mp ⊔ T) ⊓ stabSub V ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  rintro z ⟨hzX, hzV⟩
  rcases d36t_conj_cases hL38 n hzX with h | h
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  · exfalso
    have h1 := commSub_conjBy z V L
    rw [d36t_commSub_V hL38 n, mem_stabSub_iff_map_eq.mp hzV] at h1
    have h2 : conjBy z L = conjAutSub t L := h
    rw [h2] at h1
    have h3 : commSub V (conjAutSub t L) = ⊥ :=
      commSub_eq_bot_iff.mpr fun v hv g hg => n.triv v hv g hg
    rw [h3] at h1
    exact d36t_V_not_le_fixV n (by rw [← h1]; exact bot_le)

theorem d36t_faithful_V [IsSimpleGroup ↥L] (n : D36Norm M Mp T L V t) : L ⊓ centSub V = ⊥ :=
  inf_centSub_eq_bot_of_simple (insp5a_le_stabSub n.std.hyp) (d36t_exists_ne n)

theorem d36t_qsec [IsSimpleGroup ↥L] (hL38 : D3L38) (n : D36Norm M Mp T L V t) :
    InternalSec.QSec (autSub (Mp ⊔ T) V) (autSub L V) ((V ⊓ fixV Mp).subgroupOf V) := by
  have hD := n.std.hyp
  have hN := d36t_hN hL38 n
  have hLs : L ≤ stabSub V := insp5a_le_stabSub hD
  have hact := insp5a_sec_act hD n.Mp_eq n.triv hN
  have hns : ¬ Group.IsSolvable ↥L := not_isSolvable_of_mem_cComp hD.comp
  have hne : autSub L V ≠ ⊥ := autSub_ne_bot_of_exists hLs le_rfl (d36t_exists_ne n)
  have hle : autSub L V ≤ autSub (Mp ⊔ T) V :=
    autSub_mono ((insp5a_sec_L_le_Mp hD).trans le_sup_left) V
  have hstab := insp5a_sec_stab hD
  have hfix := insp5a_sec_fix hD
  have hO2 : pCoreOf 2 (autSub L V) = ⊥ := pCoreOf_autSub_eq_bot_of_isSimple hLs hns hne
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.exp])
  exact
    { le := hle
      normal := insp5a_sec_normal hN
      two := insp5a_sec_two hD hact hN
      stab := hstab
      fix := hfix
      comm := insp5a_sec_comm hLs (d36t_commSub_V hL38 n)
      lt := insp5a_sec_lt hD
      irr := insp5a_sec_irr hD hact
      faithful := InternalSec.inf_centSec_eq_bot_of_pCoreOf hexp (hle.trans hstab) hfix hO2
      quasi := CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (autSubEquivOfFaithful hLs (d36t_faithful_V n)) hD.quasi }

theorem d36t_sqtk [IsSimpleGroup ↥L] (hA21 : AsA21SQTKSection) (n : D36Norm M Mp T L V t) :
    SQTKGroup ↥(autSub L V) := by
  have hD := n.std.hyp
  have hLs : L ≤ stabSub V := insp5a_le_stabSub hD
  have hq : CFSG.IsQuasisimple ↥(autSub L V) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (autSubEquivOfFaithful hLs (d36t_faithful_V n))
      hD.quasi
  obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := hD.qsqtk
  have hS : SQTKGroup S := ⟨fun p hp hp2 => hSQT p hp hp2, hK⟩
  have hSL : SQTKGroup ↥L := B69.sqtk_subgroup hA21 hS φ hφ (le_of_mem_cComp hD.comp) hD.quasi
  exact B69.sqtk_autSub hA21 hLs hSL hq

theorem d36t_C_eq (n : D36Norm M Mp T L V t) :
    (V ⊓ fixV Mp).subgroupOf V = (⊤ : Subgroup ↥V) ⊓ fixV (autSub L V) := by
  rw [top_inf_eq]
  refine le_antisymm (insp5a_sec_fix n.std.hyp) fun v hv => ?_
  have hLs : L ≤ stabSub V := insp5a_le_stabSub n.std.hyp
  have hvL : (v : W) ∈ fixV L := fun l hl => by
    have h := hv _ (mem_autSub.mpr ⟨⟨l, hLs hl⟩, hl, rfl⟩)
    exact congrArg Subtype.val h
  rw [Subgroup.mem_subgroupOf, d36t_fixV_Mp n]
  exact ⟨v.2, hvL⟩

end Data

section Main

omit [Finite W] in
theorem sec_sq_eq_one_d36t {Y : Type} [CommGroup Y] (hY : ∀ y : Y, y ^ 2 = 1) (A C : Subgroup Y) :
    ∀ q : Sec A C, q ^ 2 = 1 := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow, show a ^ 2 = 1 from Subtype.ext (by simpa using hY a),
      QuotientGroup.mk_one]

theorem d36t_card_fixV_le_two
    [IsSimpleGroup ↥L] (hB42 : AsB42)
    (hA21 : AsA21SQTKSection) (hL38 : D3L38) (n : D36Norm M Mp T L V t) {x : MulAut W}
    (hxX : x ∈ Mp ⊔ T) (hxV : x ∈ stabSub V)
    (hF5 : ∀ u ∈ V, ∀ u' ∈ V, x u * u⁻¹ ∈ fixV L ∨ x u' * u'⁻¹ ∈ fixV L ∨
      x (u * u') * (u * u')⁻¹ ∈ fixV L)
    {v₀ : W} (hv₀ : v₀ ∈ V) (hv₀x : x v₀ * v₀⁻¹ ∉ fixV L) :
    Nat.card ↥(V ⊓ fixV Mp) ≤ 2 := by
  have hD := n.std.hyp
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.exp])
  have hQ := d36t_qsec hL38 n
  have hS := d36t_sqtk hA21 n
  have hb4 := hQ.b4Hyp hexp hS
  have hsv := sec_sq_eq_one_d36t hexp (⊤ : Subgroup ↥V) ((V ⊓ fixV Mp).subgroupOf V)
  have hLs : L ≤ stabSub V := insp5a_le_stabSub hD
  set X := autSub (Mp ⊔ T) V with hX
  set C := (V ⊓ fixV Mp).subgroupOf V with hC
  have hxX' : resHom V ⟨x, hxV⟩ ∈ X := mem_autSub.mpr ⟨⟨x, hxV⟩, hxX, rfl⟩
  set ξ := B5.secHom X (InternalSec.le_stabSub_top X) hQ.stab ⟨_, hxX'⟩ with hξ
  have hξG : ξ ∈ autSec X ⊤ C := by
    rw [← B5.range_secHom X (InternalSec.le_stabSub_top X) hQ.stab]
    exact ⟨_, rfl⟩
  let mk : ↥V → Sec (⊤ : Subgroup ↥V) C := fun v => QuotientGroup.mk ⟨v, Subgroup.mem_top v⟩
  have hmk_mul : ∀ a b : ↥V, mk (a * b) = mk a * mk b := fun a b => rfl
  have hmk_one : ∀ a : ↥V, mk a = 1 ↔ (a : W) ∈ V ⊓ fixV L := by
    intro a
    rw [← d36t_fixV_Mp n]
    exact (QuotientGroup.eq_one_iff _).trans Iff.rfl
  have hmk_surj : ∀ q : Sec (⊤ : Subgroup ↥V) C, ∃ a, mk a = q := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨w.1, rfl⟩
  have hδV : ∀ a : ↥V, x a * (a : W)⁻¹ ∈ V := fun a =>
    V.mul_mem ((hxV a).mpr a.2) (V.inv_mem a.2)
  let δ : ↥V → ↥V := fun a => ⟨x a * (a : W)⁻¹, hδV a⟩
  have hξmk : ∀ a : ↥V, ξ (mk a) = mk a * mk (δ a) := by
    intro a
    rw [← hmk_mul]
    show QuotientGroup.mk _ = QuotientGroup.mk _
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    show x a = (a : W) * (x a * (a : W)⁻¹)
    rw [mul_comm (x a), mul_inv_cancel_left]
  set c := mk (δ ⟨v₀, hv₀⟩) with hc
  have hc1 : c ≠ 1 := fun h => hv₀x ((hmk_one _).mp h).2
  have hcc : c * c = 1 := by simpa [pow_two] using hsv c
  have htw : IsTransvectionWith ξ c := by
    refine ⟨hc1, fun q => ?_⟩
    obtain ⟨a, rfl⟩ := hmk_surj q
    rw [hξmk]
    by_cases ha : x a * (a : W)⁻¹ ∈ fixV L
    · left
      rw [(hmk_one (δ a)).mpr ⟨hδV a, ha⟩, mul_one]
    · right
      rcases hF5 a a.2 v₀ hv₀ with h | h | h
      · exact absurd h ha
      · exact absurd h hv₀x
      · rw [comm_mul_d36t] at h
        have h1 : mk (δ a) * c = 1 := by
          rw [hc, ← hmk_mul]
          exact (hmk_one _).mpr ⟨(δ a * δ ⟨v₀, hv₀⟩).2, h⟩
        have h2 : mk (δ a) = c := by
          have := congrArg (· * c) h1
          simpa [mul_assoc, hcc] using this
        rw [h2]
  have hξ1 : ξ ≠ 1 := by
    intro h
    have h1 := hξmk ⟨v₀, hv₀⟩
    rw [h, MulAut.one_apply] at h1
    have h2 : mk (δ ⟨v₀, hv₀⟩) = 1 := by
      have := congrArg (fun z => (mk ⟨v₀, hv₀⟩)⁻¹ * z) h1
      simp only [inv_mul_cancel, inv_mul_cancel_left] at this
      exact this.symm
    exact hc1 h2
  have hord : orderOf ξ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact B1.tv_sq hsv htw hξ1) hξ1
  have hcardA : Nat.card ↥(Subgroup.zpowers ξ) = 2 := by rw [Nat.card_zpowers, hord]
  have hcardV := B1.card_eq_two_mul_fixV_of_tv hsv hξ1 htw
  have hA' : IsFFStarOffender (autSec X ⊤ C) (Subgroup.zpowers ξ) := by
    refine ⟨Subgroup.zpowers_le.mpr hξG, fun h => hξ1 (Subgroup.zpowers_eq_bot.mp h),
      B1.isElemAbelian2_zpowers_tv hsv hξ1 htw, fun B hB => ?_⟩
    have hBd : Nat.card ↥B ∣ 2 := hcardA ▸ Subgroup.card_dvd_of_le hB
    rcases (Nat.dvd_prime Nat.prime_two).mp hBd with h1 | h2
    · have hBbot : B = ⊥ := Subgroup.card_eq_one.mp h1
      subst hBbot
      have hfix : fixV (⊥ : Subgroup (MulAut (Sec (⊤ : Subgroup ↥V) C))) = ⊤ := by
        ext v
        simp [mem_fixV]
      rw [h1, one_mul, hcardA, hfix, Subgroup.card_top, hcardV]
    · have hBe : B = Subgroup.zpowers ξ :=
        Subgroup.eq_of_le_of_card_ge hB (by rw [h2, hcardA])
      rw [hBe]
  have hc42 := hB42 _ hsv _ _ hb4 _ hA'
  have hA38 : A38Types ↥L := (hL38 W M Mp T L V n.std t n.tT n.tn n.Mp_eq).1
  let e₁ : ↥L ≃* ↥(autSub L V) := autSubEquivOfFaithful hLs (d36t_faithful_V n)
  let e₂ : ↥(autSub L V) ≃* ↥(autSec (autSub L V) ⊤ C) :=
    B5.secEquiv (autSub L V) (InternalSec.le_stabSub_top _) hQ.stabKC hQ.faithful
  have : IsSimpleGroup ↥(autSec (autSub L V) ⊤ C) := (e₁.trans e₂).symm.isSimpleGroup
  have hA38' : A38Types ↥(autSec (autSub L V) ⊤ C) := a38Types_congr (e₁.trans e₂) hA38
  have hcommK : XMod.commOf ↥(autSub L V) (⊤ : Subgroup ↥V) = ⊤ := by
    rw [commOf_eq_commSub, ← commV_eq_commSub]
    exact hQ.comm
  have hCeq := d36t_C_eq n
  have hcardC : Nat.card ↥(V ⊓ fixV Mp) = Nat.card ↥((⊤ : Subgroup ↥V) ⊓ fixV (autSub L V)) := by
    rw [← hCeq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  rw [hcardC]
  rcases b42_card_two_of_a38Types hsv hb4 hA' hcardA hc42 hA38' with h3 | h5
  · have hnat := InternalSec.binaryNaturalSL_of_autSec hQ.stabKC hQ.faithful h3
    rw [hC, hCeq] at hnat
    exact card_fixV_le_two_of_natural3 hexp _ ⊤ (fun _ _ _ _ => trivial) hcommK hnat
  · have halt := InternalSec.alternatingNatural_of_autSec hQ.stabKC hQ.faithful h5
    rw [hC, hCeq] at halt
    exact (card_fixV_le_one_of_altD5 hexp _ ⊤ (fun _ _ _ _ => trivial) hcommK halt).trans
      (by norm_num)

end Main

end CFSG.Quasithin

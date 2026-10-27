module

public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCorePre
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]


private theorem seven_eight_core_reps_phi_mul {H : Subgroup G} {Q : Type} [Group Q]
    {φ : ↥H →* Q} {a b : G} (ha : a ∈ H) (hb : b ∈ H) (hab : a * b ∈ H) :
    φ ⟨a * b, hab⟩ = φ ⟨a, ha⟩ * φ ⟨b, hb⟩ := by
  rw [← map_mul]
  congr 1

private theorem seven_eight_core_reps_phi_inv {H : Subgroup G} {Q : Type} [Group Q]
    {φ : ↥H →* Q} {a : G} (ha : a ∈ H) (hia : a⁻¹ ∈ H) :
    φ ⟨a⁻¹, hia⟩ = (φ ⟨a, ha⟩)⁻¹ := by
  rw [← map_inv]
  congr 1

theorem Hyp78.exists_normalizing_rep_of_mem_omegaSet {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) (hV2 : J.relIndex V = 2) {Q : Type} [Group Q] [Finite Q]
    {φ : ↥H →* Q} (hφ : IsBarMap H J φ) {Xb : Subgroup Q}
    (hXL : barSub H φ L ≤ Subgroup.normalizer (Xb : Set Q)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hexp : ∀ x ∈ Xb, x ^ p = 1) {Y : Subgroup G}
    (hY : IsHallCompl V H E J (barPre H φ Xb) Y) {U : Subgroup G} (hU : U ∈ omegaSet V H E)
    (hUL : U ≤ L) {u : G} (hu : u ∈ U) (huJ : u ∉ J)
    (hne : ⁅Xb, Subgroup.zpowers (φ ⟨u, h.omega_le U hU hu⟩)⁆ ≠ ⊥) :
    ∃ U' ∈ omegaSet V H E, U' ≤ U ⊔ J ∧
      ∃ u₁ ∈ U', u₁ ∉ J ∧ u₁ ∈ Subgroup.normalizer (Y : Set G) ∧ u⁻¹ * u₁ ∈ J := by
  have hJH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hLH : L ≤ H := h.le_kSub.trans (kSub_le_of_forall_le h.omega_le)
  have hXH : barPre H φ Xb ≤ H := barPre_le H φ Xb
  have hJX : J ≤ barPre H φ Xb := le_barPre hJH hφ Xb
  have hJnormH : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJH h.jnormal
  haveI hJn : (J.subgroupOf (barPre H φ Xb)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hXH.trans hJnormH)
  have hUX : U ≤ Subgroup.normalizer ((barPre H φ Xb : Subgroup G) : Set G) :=
    hUL.trans (le_normalizer_barPre hφ hLH hXL)
  have hexpG : ∀ g ∈ barPre H φ Xb, g ^ p ∈ J := by
    intro g hg
    obtain ⟨hgH, hgX⟩ := mem_barPre.mp hg
    have hpow : φ ⟨g ^ p, H.pow_mem hgH p⟩ = (1 : Q) := by
      rw [show (⟨g ^ p, H.pow_mem hgH p⟩ : ↥H) = ⟨g, hgH⟩ ^ p from Subtype.ext rfl,
        map_pow]
      exact hexp (φ ⟨g, hgH⟩) hgX
    exact (hφ.ker_iff ⟨g ^ p, H.pow_mem hgH p⟩).mp hpow
  have h76 : Hyp76 V H E J U (barPre H φ Xb) :=
    hyp76_of_member h.elemAbelian h.ti hp hp2 h.abelian h.le h.normal h.omega_le
      h.pcore_le h.jnormal h.iSub_le hU (le_barPre hJH hφ Xb) (barPre_le H φ Xb) hUX
      (Hyp78.faithful_of_mem_omegaSet h hV2 hφ hU hu huJ hne) hexpG
  exact h76.exists_normalizing_rep hY ⟨U, hU, le_sup_left, hu, huJ⟩

theorem Hyp78.exists_normalizing_reps {V H E J L : Subgroup G} (h : Hyp78 V H E J L)
    (hV2 : J.relIndex V = 2) {Q : Type} [Group Q] [Finite Q] {φ : ↥H →* Q}
    (hφ : IsBarMap H J φ) {v : G} (hv : v ∈ V) (hvJ : v ∉ J) {Xb : Subgroup Q}
    (hXL : barSub H φ L ≤ Subgroup.normalizer (Xb : Set Q)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hXp : IsPGroup p Xb) (hexp : ∀ x ∈ Xb, x ^ p = 1)
    (hne : ∀ a ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩),
      ⁅Xb, Subgroup.zpowers a⁆ ≠ ⊥)
    {Y : Subgroup G} (hY : IsHallCompl V H E J (barPre H φ Xb) Y) :
    ∃ w : ↥(deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩)) → G,
      ∃ hwH : ∀ a, w a ∈ H,
        (∀ a, φ ⟨w a, hwH a⟩ = (a : Q)) ∧ (∀ a, w a * w a = 1) ∧
        (∀ a, w a ∈ Subgroup.normalizer (Y : Set G)) ∧
        ∀ a b, a ≠ b → ∀ y ∈ ⁅Y, Subgroup.zpowers (w b)⁆,
          ∀ z ∈ ⁅iSub V H E, Subgroup.zpowers (w a)⁆, y * z = z * y := by
  have hVH : v ∈ H := h.omega_le V h.mem hv
  have hJH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hLH : L ≤ H := h.le_kSub.trans (kSub_le_of_forall_le h.omega_le)
  have hJnormH : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJH h.jnormal
  have hXH : barPre H φ Xb ≤ H := barPre_le H φ Xb
  have hJX : J ≤ barPre H φ Xb := le_barPre hJH hφ Xb
  haveI hJn : (J.subgroupOf (barPre H φ Xb)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hXH.trans hJnormH)
  have h_exists : ∀ a : ↥(deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, hVH⟩)),
      ∃ x ∈ pCoreOf 2 L, ∃ hw : x * v * x⁻¹ ∈ H,
        (a : Q) = φ ⟨x * v * x⁻¹, hw⟩ :=
    fun a => Hyp78.exists_mem_pCoreOf_of_mem_deltaSet h hv a.2
  choose x hxcore hxH hxeq using h_exists
  have hUΩ : ∀ a, conjSubgroup V (x a)⁻¹ ∈ omegaSet V H E :=
    fun a => (Hyp78.conjSubgroup_inv_mem_omegaSet h (hxcore a)).1
  have hUL : ∀ a, conjSubgroup V (x a)⁻¹ ≤ L :=
    fun a => (Hyp78.conjSubgroup_inv_mem_omegaSet h (hxcore a)).2
  have huU : ∀ a, x a * v * (x a)⁻¹ ∈ conjSubgroup V (x a)⁻¹ := by
    intro a
    rw [mem_conjSubgroup_iff]
    rw [show (x a)⁻¹ * (x a * v * (x a)⁻¹) * ((x a)⁻¹)⁻¹ = v by group]
    exact hv
  have huH : ∀ a, x a * v * (x a)⁻¹ ∈ H :=
    fun a => h.omega_le (conjSubgroup V (x a)⁻¹) (hUΩ a) (huU a)
  have hphi_u : ∀ a, φ ⟨x a * v * (x a)⁻¹, huH a⟩ = (a : Q) := by
    intro a
    rw [show (⟨x a * v * (x a)⁻¹, huH a⟩ : ↥H) =
        ⟨x a * v * (x a)⁻¹, hxH a⟩ from Subtype.ext rfl]
    exact (hxeq a).symm
  have huJ : ∀ a, x a * v * (x a)⁻¹ ∉ J := by
    intro a hmem
    have h1 : (a : Q) = 1 := by
      rw [hxeq a, (hφ.ker_iff ⟨x a * v * (x a)⁻¹, hxH a⟩).mpr hmem]
    have hbot : ⁅Xb, Subgroup.zpowers (a : Q)⁆ = ⊥ := by
      rw [h1, Subgroup.zpowers_eq_bot.mpr rfl, Subgroup.commutator_bot_right]
    exact hne a a.2 hbot
  have h_exists' : ∀ a : ↥(deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, hVH⟩)),
      ∃ U' ∈ omegaSet V H E, U' ≤ conjSubgroup V (x a)⁻¹ ⊔ J ∧
        ∃ u₁ ∈ U', u₁ ∉ J ∧ u₁ ∈ Subgroup.normalizer (Y : Set G) ∧
          (x a * v * (x a)⁻¹)⁻¹ * u₁ ∈ J := by
    intro a
    refine Hyp78.exists_normalizing_rep_of_mem_omegaSet h hV2 hφ hXL hp hp2 hexp hY
      (hUΩ a) (hUL a) (huU a) (huJ a) ?_
    rw [hphi_u a]
    exact hne a a.2
  choose U' hU'Ω hU'U u₁ hu₁U hu₁J hu₁N hu₁Ju using h_exists'
  have hwH : ∀ a, u₁ a ∈ H := fun a => h.omega_le (U' a) (hU'Ω a) (hu₁U a)
  have hphiw : ∀ a, φ ⟨u₁ a, hwH a⟩ = (a : Q) := by
    intro a
    have hmemH : (x a * v * (x a)⁻¹)⁻¹ * u₁ a ∈ H :=
      H.mul_mem (H.inv_mem (huH a)) (hwH a)
    have hone : φ ⟨(x a * v * (x a)⁻¹)⁻¹ * u₁ a, hmemH⟩ = 1 :=
      (hφ.ker_iff _).mpr (hu₁Ju a)
    have hprod : φ ⟨(x a * v * (x a)⁻¹)⁻¹ * u₁ a, hmemH⟩ =
        (a : Q)⁻¹ * φ ⟨u₁ a, hwH a⟩ := by
      rw [seven_eight_core_reps_phi_mul (H.inv_mem (huH a)) (hwH a) hmemH,
        seven_eight_core_reps_phi_inv (huH a) (H.inv_mem (huH a)), hphi_u a]
    have h2 : (a : Q)⁻¹ * φ ⟨u₁ a, hwH a⟩ = 1 := by rw [← hprod, hone]
    exact (inv_mul_eq_one.mp h2).symm
  have hww : ∀ a, u₁ a * u₁ a = 1 := fun a =>
    elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet h.elemAbelian (hU'Ω a)) (hu₁U a)
  have hwcomm : ∀ a b, a ≠ b → ∀ y ∈ ⁅Y, Subgroup.zpowers (u₁ b)⁆,
      ∀ z ∈ ⁅iSub V H E, Subgroup.zpowers (u₁ a)⁆, y * z = z * y := by
    intro a b hab y hy z hz
    have habQ : (a : Q) ≠ (b : Q) := fun h => hab (Subtype.ext h)
    have hxy : (x a * v * (x a)⁻¹)⁻¹ * (x b * v * (x b)⁻¹) ∉ J := by
      intro hmem
      have hmemH : (x a * v * (x a)⁻¹)⁻¹ * (x b * v * (x b)⁻¹) ∈ H :=
        H.mul_mem (H.inv_mem (huH a)) (huH b)
      have hone : φ ⟨(x a * v * (x a)⁻¹)⁻¹ * (x b * v * (x b)⁻¹), hmemH⟩ = 1 :=
        (hφ.ker_iff _).mpr hmem
      have hprod : φ ⟨(x a * v * (x a)⁻¹)⁻¹ * (x b * v * (x b)⁻¹), hmemH⟩ =
          (a : Q)⁻¹ * (b : Q) := by
        rw [seven_eight_core_reps_phi_mul (H.inv_mem (huH a)) (huH b) hmemH,
          seven_eight_core_reps_phi_inv (huH a) (H.inv_mem (huH a)), hphi_u a, hphi_u b]
      rw [hprod] at hone
      exact habQ (inv_mul_eq_one.mp hone)
    have h76 : Hyp76 V H E J (conjSubgroup V (x a)⁻¹ ⊔ conjSubgroup V (x b)⁻¹)
        (barPre H φ Xb) :=
      Hyp78.hyp76_sup h hV2 hφ hv hvJ hXL hp hp2 hXp hexp hne (hxcore a) (hxcore b) hxy
    have hD : u₁ b ∈ dSetIn V H E J (conjSubgroup V (x a)⁻¹ ⊔ conjSubgroup V (x b)⁻¹) :=
      ⟨U' b, hU'Ω b, (hU'U b).trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right),
        hu₁U b, hu₁J b⟩
    have hne' : (u₁ a)⁻¹ * u₁ b ∉ J := by
      intro hmem
      have hmemH : (u₁ a)⁻¹ * u₁ b ∈ H := H.mul_mem (H.inv_mem (hwH a)) (hwH b)
      have hone : φ ⟨(u₁ a)⁻¹ * u₁ b, hmemH⟩ = 1 := (hφ.ker_iff _).mpr hmem
      have hprod : φ ⟨(u₁ a)⁻¹ * u₁ b, hmemH⟩ = (a : Q)⁻¹ * (b : Q) := by
        rw [seven_eight_core_reps_phi_mul (H.inv_mem (hwH a)) (hwH b) hmemH,
          seven_eight_core_reps_phi_inv (hwH a) (H.inv_mem (hwH a)), hphiw a, hphiw b]
      rw [hprod] at hone
      exact habQ (inv_mul_eq_one.mp hone)
    have hle : ⁅Y, Subgroup.zpowers (u₁ b)⁆ ≤
        commOthers V H E J (conjSubgroup V (x a)⁻¹ ⊔ conjSubgroup V (x b)⁻¹) Y (u₁ a) := by
      unfold commOthers
      exact le_iSup₂_of_le (u₁ b) hD
        (le_iSup_of_le (hu₁N b) (le_iSup_of_le hne' le_rfl))
    have hy' : y ∈ commOthers V H E J
        (conjSubgroup V (x a)⁻¹ ⊔ conjSubgroup V (x b)⁻¹) Y (u₁ a) := hle hy
    have hcent := h76.commOthers_sup_iSub_centralizes hY.le_X (hU'Ω a)
      ((hU'U a).trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
      (hu₁U a) (hu₁J a)
    exact hcent y (Subgroup.mem_sup_left hy') z hz
  exact ⟨u₁, hwH, hphiw, hww, hu₁N, hwcomm⟩

end CFSG.LocalAnalysis.WeakClosure81

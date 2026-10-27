module

public import CFSG.RankThree.GF2n.Parrott.Lemma13Structure
import CFSG.RankThree.GF2n.Parrott.Section4HPrimeIndex
public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma13Q

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43 A1Section2Local
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_conj_mem_mul_of_free (h : Tim79a.ParrottHyp z) {B R : Subgroup G} {g : G}
    (hRJ : R ≤ J z) (hZB : centerIn (J z) ≤ B)
    (hJBR : ∀ j ∈ J z, ∃ b ∈ B, ∃ r ∈ R, j = b * r)
    (hBR : ∀ b ∈ B, ∀ r ∈ R, b * r = r * b)
    (hBRZ : ∀ a ∈ B, a ∈ R → a ∈ centerIn (J z))
    (hgB : ∀ a : G, a ∈ B ↔ g * a * g⁻¹ ∈ B) (hgR : ∀ a : G, a ∈ R ↔ g * a * g⁻¹ ∈ R)
    (hg2 : g * g ∈ B)
    (hfree : ∀ r ∈ R, g * r * g⁻¹ * r ∈ centerIn (J z) →
      ∃ v ∈ R, r⁻¹ * (g * v * g⁻¹ * v) ∈ centerIn (J z))
    {x : G} (hx : ∃ j ∈ J z, x = g * j) (hx2 : x * x = 1) :
    ∃ w ∈ R, ∃ c ∈ B, w * x * w⁻¹ = g * c := by
  obtain ⟨j, hj, rfl⟩ := hx
  obtain ⟨b, hb, r, hr, rfl⟩ := hJBR j hj
  have hr'R : g * r * g⁻¹ ∈ R := (hgR r).mp hr
  have hb'B : g * b * g⁻¹ ∈ B := (hgB b).mp hb
  have hxx : g * (b * r) * (g * (b * r)) =
      (g * b * g⁻¹ * (g * g) * b) * (g * r * g⁻¹ * r) := by
    have hc := hBR _ (B.mul_mem hg2 hb) _ hr'R
    calc g * (b * r) * (g * (b * r)) = g * b * g⁻¹ * ((g * r * g⁻¹) * ((g * g) * b)) * r := by
          group
      _ = g * b * g⁻¹ * (((g * g) * b) * (g * r * g⁻¹)) * r := by rw [hc]
      _ = (g * b * g⁻¹ * (g * g) * b) * (g * r * g⁻¹ * r) := by group
  have hrr : g * r * g⁻¹ * r ∈ centerIn (J z) := by
    have h1 : (g * b * g⁻¹ * (g * g) * b) * (g * r * g⁻¹ * r) = 1 := hxx ▸ hx2
    have e : g * r * g⁻¹ * r = (g * b * g⁻¹ * (g * g) * b)⁻¹ := eq_inv_of_mul_eq_one_right h1
    refine hBRZ _ ?_ (R.mul_mem hr'R hr)
    rw [e]
    exact B.inv_mem (B.mul_mem (B.mul_mem hb'B hg2) hb)
  obtain ⟨v, hvR, hv⟩ := hfree r hr hrr
  have hwR : g * v * g⁻¹ ∈ R := (hgR v).mp hvR
  have hvJ : v ∈ J z := hRJ hvR
  have hwJ : g * v * g⁻¹ ∈ J z := hRJ hwR
  refine ⟨g * v * g⁻¹, hwR, b * (v * r * (g * v * g⁻¹)⁻¹), B.mul_mem hb (hZB ?_), ?_⟩
  ·
    set w := g * v * g⁻¹ with hw
    set ζ := r⁻¹ * (w * v) with hζ
    have hc : v * w * v⁻¹ * w⁻¹ ∈ centerIn (J z) := by
      have := commutator_mem_centerIn h ⟨v, hvJ⟩ ⟨w, hwJ⟩
      simpa [commutatorElement_def] using this
    have hvv : v * v ∈ centerIn (J z) := sq_mem_centerIn_J h hvJ
    have hvvw : w * (v * v) * w⁻¹ = v * v := by
      rw [(Subgroup.mem_centralizer_iff.mp hvv.2 w hwJ)]
      group
    have hζw : ζ⁻¹ * w⁻¹ = w⁻¹ * ζ⁻¹ :=
      (Subgroup.mem_centralizer_iff.mp ((centerIn (J z)).inv_mem hv).2 _ ((J z).inv_mem hwJ)).symm
    have hr_eq : r = w * v * ζ⁻¹ := by rw [hζ]; group
    have e : v * r * w⁻¹ = (v * w * v⁻¹ * w⁻¹) * (v * v) * ζ⁻¹ := by
      rw [hr_eq]
      calc v * (w * v * ζ⁻¹) * w⁻¹ = v * w * v * (ζ⁻¹ * w⁻¹) := by group
        _ = v * w * v * (w⁻¹ * ζ⁻¹) := by rw [hζw]
        _ = (v * w * v⁻¹ * w⁻¹) * (w * (v * v) * w⁻¹) * ζ⁻¹ := by group
        _ = (v * w * v⁻¹ * w⁻¹) * (v * v) * ζ⁻¹ := by rw [hvvw]
    rw [e]
    exact (centerIn (J z)).mul_mem ((centerIn (J z)).mul_mem hc hvv)
      ((centerIn (J z)).inv_mem hv)
  ·
    have hvb : v * b = b * v := (hBR b hb v hvR).symm
    calc g * v * g⁻¹ * (g * (b * r)) * (g * v * g⁻¹)⁻¹ = g * (v * b) * r * (g * v * g⁻¹)⁻¹ := by
          group
      _ = g * (b * v) * r * (g * v * g⁻¹)⁻¹ := by rw [hvb]
      _ = g * (b * (v * r * (g * v * g⁻¹)⁻¹)) := by group

variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem free_commutator_of_qH_eq_t (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {g : ↥(H z)}
    (hg : qH D g = (⟨t, t_mem_A⟩ : QA45.originalSubgroup))
    (hgσ : g * (sigma1Nine (z := z) D * σ₂⁻¹) = (sigma1Nine (z := z) D * σ₂⁻¹) * g) :
    ∀ r ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D * σ₂⁻¹)).map (H z).subtype, J z⁆,
      (g : G) * r * (g : G)⁻¹ * r ∈ centerIn (J z) →
      ∃ v ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D * σ₂⁻¹)).map (H z).subtype, J z⁆,
        r⁻¹ * ((g : G) * v * (g : G)⁻¹ * v) ∈ centerIn (J z) := by
  set σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹ with hσdef
  set R : Subgroup G := ⁅(Subgroup.zpowers σ).map (H z).subtype, J z⁆ with hRdef
  have hRJ : R ≤ J z := commutator_le_J_of (z := z)
  have hσ3 : orderOf σ = 3 :=
    orderOf_mul_inv_of_commute_of_hom (qH D) (sigma1Nine_order D) hσ₂ (qH_sigma1Nine D) hq₂ hcomm
  have hZσ : conjZ z σ = 1 := conjZ_sigma1Nine_mul_inv D h hq₂
  have hRσ : R = ⁅Subgroup.zpowers (σ : G), J z⁆ := by rw [hRdef, map_zpowers_sigma_eq]
  have hgσ' : (g : G) * (σ : G) = (σ : G) * (g : G) := congrArg Subtype.val hgσ
  have hgR : ∀ a : G, a ∈ R ↔ (g : G) * a * (g : G)⁻¹ ∈ R := by
    intro a
    rw [hRσ]
    exact mem_commutator_conj_iff g.2 hgσ' a
  have hσR : ∀ a : G, a ∈ R ↔ (σ : G) * a * (σ : G)⁻¹ ∈ R := by
    intro a
    rw [hRσ]
    exact mem_commutator_conj_iff σ.2 rfl a
  set W : Subgroup (QuotientV.V z) := (R.subgroupOf (J z)).map (QuotientV.pi z) with hWdef
  have hWV : W = commutatorV h σ := rfl
  set τ := conjV h g with hτdef
  set β := conjV h σ with hβdef
  have hτW : ∀ v, τ v ∈ W ↔ v ∈ W := conjV_mem_map_pi_iff h g hgR
  have hβW : ∀ v, β v ∈ W ↔ v ∈ W := conjV_mem_map_pi_iff h σ hσR
  have hg2 : ((g * g : ↥(H z)) : G) ∈ J z := by
    have hq1 : qH D (g * g) = 1 := by
      rw [map_mul, hg]
      apply Subtype.ext
      simp [t_sq]
    exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr hq1)
  have hτ2 : ∀ v ∈ W, τ (τ v) = v := by
    intro v _
    have h1 : conjV h (g * g) = 1 :=
      MonoidHom.mem_ker.mp (J_le_ker_conjV (z := z) h (Subgroup.mem_subgroupOf.mpr hg2))
    rw [hτdef, ← MulAut.mul_apply, ← map_mul, h1]
    rfl
  have hVcomm : ∀ a b : QuotientV.V z, a * b = b * a := (QuotientV.isMulCommutative_V h).is_comm.comm
  have hV2 : ∀ v : QuotientV.V z, v * v = 1 := fun v => by
    have := QuotientV.pow_two_eq_one_V h v
    rwa [pow_two] at this
  have hβτ : ∀ v, β (τ v) = τ (β v) := by
    intro v
    rw [hβdef, hτdef, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, hgσ]
  have hσ3' : σ ^ 3 = 1 := by rw [← hσ3]; exact pow_orderOf_eq_one σ
  set F := fixIn W τ with hFdef
  have hβF : ∀ v, β v ∈ F ↔ v ∈ F := by
    intro v
    constructor
    · rintro ⟨hv1, hv2⟩
      refine ⟨(hβW v).mp hv1, ?_⟩
      apply β.injective
      rw [hβτ, hv2]
    · rintro ⟨hv1, hv2⟩
      exact ⟨(hβW v).mpr hv1, by rw [← hβτ, hv2]⟩
  have hβ3 : ∀ v ∈ F, (β ^ 3) v = v := by
    intro v _
    rw [hβdef, ← map_pow, hσ3', map_one]
    rfl
  have hβfixW : ∀ v ∈ W, β v = v → v = 1 := by
    intro v hv hfix
    have hker : v ∈ (VComplementHom h σ).ker := by
      rw [ker_VComplementHom_eq_autFixedSubgroup (z := z) h hσ3, mem_autFixedSubgroup]
      exact hfix
    have hrange : v ∈ (VComplementHom h σ).range := by
      rw [← commutatorV_eq_range (z := z) h hσ3]
      exact hv
    have hmem : v ∈ (VComplementHom h σ).ker ⊓ (VComplementHom h σ).range := ⟨hker, hrange⟩
    rw [disjoint_ker_range_VComplementHom (z := z) h hσ3] at hmem
    exact hmem
  have hmodF := card_modEq_one_of_cube F β hβF hβ3 (fun v hv => hβfixW v hv.1)
  have hWcard : Nat.card W = 16 := card_commutatorV_mul_inv_of_equalityBranch D h hσ₂ hq₂ hcomm hEq
  have hdvd : Nat.card F ∣ 16 := hWcard ▸ Subgroup.card_dvd_of_le (fixIn_le W τ)
  have hne : Nat.card F ≠ 16 := by
    intro h16
    have hFW : F = W := Subgroup.eq_of_le_of_card_ge (fixIn_le W τ) (by rw [h16, hWcard])
    have hall : conjV h g = 1 := by
      ext v
      obtain ⟨j, rfl⟩ := QuotientV.pi_surjective z v
      obtain ⟨b, hb, r, hr, hjbr⟩ := exists_mul_of_mem_J_of_orderOf_eq_three h hσ3 j.2
      have hbJ : b ∈ J z := (mem_CJ.mp hb).2
      have hrJ : r ∈ J z := hRJ hr
      have hj : j = ⟨b, hbJ⟩ * ⟨r, hrJ⟩ := Subtype.ext hjbr
      have hτb : τ (QuotientV.pi z ⟨b, hbJ⟩) = QuotientV.pi z ⟨b, hbJ⟩ := by
        have hZ := conj_mul_inv_mem_centerIn_of_mem_CJ_mul_inv_of_qH_eq_t D h hσ₂ hq₂ hcomm hEq hg hgσ hb
        rw [hτdef, conjV_pi_conj h g hbJ]
        have hgbJ : (g : G) * b * (g : G)⁻¹ ∈ J z := H_conj_mem_J (z := z) g hbJ
        have hone : QuotientV.pi z ⟨(g : G) * b * (g : G)⁻¹ * b⁻¹,
            (J z).mul_mem hgbJ ((J z).inv_mem hbJ)⟩ = 1 :=
          (pi_eq_one_iff_mem_centerIn _).mpr hZ
        have e : (⟨(g : G) * b * (g : G)⁻¹ * b⁻¹, (J z).mul_mem hgbJ ((J z).inv_mem hbJ)⟩ : J z) =
            ⟨(g : G) * b * (g : G)⁻¹, hgbJ⟩ * (⟨b, hbJ⟩ : J z)⁻¹ := rfl
        rw [e, map_mul, map_inv, mul_inv_eq_one] at hone
        exact hone
      have hτr : τ (QuotientV.pi z ⟨r, hrJ⟩) = QuotientV.pi z ⟨r, hrJ⟩ := by
        have hmem : QuotientV.pi z ⟨r, hrJ⟩ ∈ F := by
          rw [hFW]
          exact ⟨⟨r, hrJ⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
        exact hmem.2
      rw [hj, map_mul, map_mul, hτb, hτr]
      rfl
    have hZg : conjZ z g = 1 := by
      apply conjZ_eq_one_of_mem_Q (z := z) D h g
      rw [hg]
      exact t_mem_Q
    have hgJ := mem_J_of_conjZ_eq_one_of_conjV_eq_one h hZg hall
    have hq1 : qH D g = 1 := (J_mem_iff D g).mp (Subgroup.mem_subgroupOf.mpr hgJ)
    rw [hg] at hq1
    exact t_ne_one (congrArg Subtype.val hq1)
  have hcard : Nat.card F ^ 2 ≤ Nat.card W := by
    rw [hWcard]
    have hdvd' : Nat.card F ∣ 2 ^ 4 := by norm_num; exact hdvd
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    have hm : Nat.card F % 3 = 1 := by simpa [Nat.ModEq] using hmodF
    rw [hkeq] at hm hne ⊢
    have arith : ∀ k : ℕ, k ≤ 4 → 2 ^ k % 3 = 1 → 2 ^ k ≠ 16 → (2 ^ k) ^ 2 ≤ 16 := by decide
    exact arith k hk hm hne
  have hfreeW := exists_eq_mul_of_card_fix_sq_le hVcomm W τ hτW hτ2 (fun v _ => hV2 v) hcard
  intro r hr hrfix
  have hrJ : r ∈ J z := hRJ hr
  have hgrJ : (g : G) * r * (g : G)⁻¹ ∈ J z := H_conj_mem_J (z := z) g hrJ
  have hrW : QuotientV.pi z ⟨r, hrJ⟩ ∈ W := ⟨⟨r, hrJ⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  have hτr : τ (QuotientV.pi z ⟨r, hrJ⟩) = QuotientV.pi z ⟨r, hrJ⟩ := by
    rw [hτdef, conjV_pi_conj h g hrJ]
    have hone : QuotientV.pi z ⟨(g : G) * r * (g : G)⁻¹ * r, (J z).mul_mem hgrJ hrJ⟩ = 1 :=
      (pi_eq_one_iff_mem_centerIn _).mpr hrfix
    have e : (⟨(g : G) * r * (g : G)⁻¹ * r, (J z).mul_mem hgrJ hrJ⟩ : J z) =
        ⟨(g : G) * r * (g : G)⁻¹, hgrJ⟩ * ⟨r, hrJ⟩ := rfl
    rw [e, map_mul] at hone
    calc QuotientV.pi z ⟨(g : G) * r * (g : G)⁻¹, hgrJ⟩
        = QuotientV.pi z ⟨(g : G) * r * (g : G)⁻¹, hgrJ⟩ * (QuotientV.pi z ⟨r, hrJ⟩ *
            QuotientV.pi z ⟨r, hrJ⟩) := by rw [hV2, mul_one]
      _ = 1 * QuotientV.pi z ⟨r, hrJ⟩ := by rw [← mul_assoc, hone]
      _ = QuotientV.pi z ⟨r, hrJ⟩ := one_mul _
  obtain ⟨c, hcW, hc⟩ := hfreeW _ hrW hτr
  obtain ⟨v, hv, rfl⟩ := hcW
  have hvR : (v : G) ∈ R := Subgroup.mem_subgroupOf.mp hv
  refine ⟨v, hvR, ?_⟩
  have hgvJ : (g : G) * v * (g : G)⁻¹ ∈ J z := H_conj_mem_J (z := z) g v.2
  rw [hτdef, conjV_pi_conj h g v.2] at hc
  have hmemJ : r⁻¹ * ((g : G) * v * (g : G)⁻¹ * v) ∈ J z :=
    (J z).mul_mem ((J z).inv_mem hrJ) ((J z).mul_mem hgvJ v.2)
  apply (pi_eq_one_iff_mem_centerIn hmemJ).mp
  have e : (⟨r⁻¹ * ((g : G) * v * (g : G)⁻¹ * v), hmemJ⟩ : J z) =
      (⟨r, hrJ⟩ : J z)⁻¹ * (⟨(g : G) * v * (g : G)⁻¹, hgvJ⟩ * v) := rfl
  rw [e, map_mul, map_inv, map_mul, ← hc, inv_mul_cancel]

theorem reduce_tJ_tCJ_of_equalityBranch (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {σ : ↥(H z)} (hσ : σ = sigma1Nine (z := z) D * σ₂⁻¹)
    {t : ↥(H z)} (ht : (tH D)⁻¹ * t ∈ (J z).subgroupOf (H z)) (htσ : t * σ = σ * t) :
    ∀ ⦃x : G⦄, (∃ j ∈ J z, x = (t : G) * j) → orderOf x = 2 →
      ∃ h' ∈ H z, ∃ c ∈ CJ z (σ : G), h' * x * h'⁻¹ = (t : G) * c := by
  intro x hx hx2
  subst hσ
  have hσ3 : orderOf (sigma1Nine (z := z) D * σ₂⁻¹) = 3 :=
    orderOf_mul_inv_of_commute_of_hom (qH D) (sigma1Nine_order D) hσ₂ (qH_sigma1Nine D) hq₂ hcomm
  have hZσ := conjZ_sigma1Nine_mul_inv D h hq₂
  have hqt : qH D t =
      (⟨_root_.CFSG.RankThree.GF2n.Parrott.t, t_mem_A⟩ : QA45.originalSubgroup) := by
    have h1 := (J_mem_iff D _).mp ht
    rw [map_mul, map_inv, qH_tH, inv_mul_eq_one] at h1
    exact h1.symm
  have htσ' : (t : G) * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) =
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * (t : G) := congrArg Subtype.val htσ
  have hRσ : ⁅(Subgroup.zpowers (sigma1Nine (z := z) D * σ₂⁻¹)).map (H z).subtype, J z⁆ =
      ⁅Subgroup.zpowers ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G), J z⁆ := by
    rw [map_zpowers_sigma_eq]
  have ht2 : (t : G) * (t : G) ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) := by
    have hq1 : qH D (t * t) = 1 := by
      rw [map_mul, hqt]
      apply Subtype.ext
      simp [t_sq]
    have htt : ((t * t : ↥(H z)) : G) ∈ J z := Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr hq1)
    refine mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, by simpa using htt⟩
    calc (t : G) * (t : G) * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
        = (t : G) * ((t : G) * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) := by group
      _ = ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * ((t : G) * (t : G)) := by
          rw [htσ', ← mul_assoc, htσ', mul_assoc]
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at this
  obtain ⟨w, hwR, c, hc, hwx⟩ := exists_conj_mem_mul_of_free h (commutator_le_J_of (z := z))
    (centerIn_le_CJ_of_conjZ_eq_one hZσ) (fun j hj => exists_mul_of_mem_J_of_orderOf_eq_three h hσ3 hj)
    (fun b hb r hr => commute_of_mem_CJ_of_mem_commutator h _ hb hr)
    (fun a haB haR => Subgroup.zpowers_le.mpr (show z ∈ centerIn (J z) from
      ⟨z_mem_J h, z_centralizes_J h⟩) (mem_zpowers_of_mem_CJ_of_mem_commutator h hσ3 hZσ haB haR))
    (mem_CJ_conj_iff t.2 htσ') (by rw [hRσ]; exact mem_commutator_conj_iff t.2 htσ') ht2
    (free_commutator_of_qH_eq_t D h hσ₂ hq₂ hcomm hEq hqt htσ) hx hxx
  exact ⟨w, J_le_H (commutator_le_J_of (z := z) hwR), c, hc, hwx⟩

end CFSG.RankThree.GF2n.Parrott

module

public import CFSG.RankThree.Co2.Exclude
public import CFSG.RankThree.Co2.Sqrt
public import CFSG.RankThree.Co2.CrMat
public import CFSG.RankThree.Co2.X9Cert
public import Certificates.Certificate3054
public import Certificates.Certificate8101
public import Certificates.Certificate8102
public import Certificates.Certificate8108
public import Certificates.Certificate8111
public import Certificates.Certificate8113
public import Certificates.Certificate16022
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate16000
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3138

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

theorem x9_letters : (∀ k < xWords9.size, ∀ l ∈ xWords9[k]!, l < 42) ∧ ∀ l ∈ dWord, l < 42 := by
  decide +kernel

theorem crMat_gensW9 {k : ℕ} (hk : k < xWords9.size) :
    crMat (gensW xWords9 k) = wordMat xWords9[(⟨k, hk⟩ : Fin xWords9.size)] := by
  unfold gensW
  rw [crMat_wordCr (x9_letters.1 k hk), getElem!_pos xWords9 k hk]
  rfl

theorem le_C9 : subW xWords9 ≤ Subgroup.centralizer ({rep 9} : Set Cr) := by
  rw [subW, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  apply crMat_injective
  simp only [map_mul]
  rw [crMat_gensW9 hk, crMat_rep (by norm_num)]
  exact x9Facts_cert.comm9 ⟨k, hk⟩

theorem card_C9 : Nat.card (Subgroup.centralizer ({rep 9} : Set Cr)) = 6144 :=
  card_C 9 (by norm_num) (by decide) (classSizes_pos (by norm_num))

theorem card_subW9 : Nat.card (subW xWords9) = 6144 := by
  apply le_antisymm
  · rw [← card_C9]
    exact Subgroup.card_le_of_le le_C9
  · exact x9Facts_cert.card.trans (card_matGrp_le x9_letters.1)

theorem subW_eq_C9 : subW xWords9 = Subgroup.centralizer ({rep 9} : Set Cr) :=
  Subgroup.eq_of_le_of_card_ge le_C9 (by rw [card_C9, card_subW9])

theorem matGrp9_eq : matGrp xWords9 = (subW xWords9).toSubmonoid.map crMat :=
  matGrp_eq_map x9_letters.1 (by rw [card_subW9]; exact x9Facts_cert.card)

theorem mem_subW9_iff {y : Cr} : y ∈ subW xWords9 ↔ crMat y ∈ matGrp xWords9 := by
  rw [matGrp9_eq]
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y', hy', e⟩
    rwa [← crMat_injective e]

@[expose] def d9 : Cr := wordCr dWord

theorem crMat_d9 : crMat d9 = wordMat dWord :=
  crMat_wordCr x9_letters.2

theorem d9_mem : d9 ∈ subW xWords9 := by
  obtain ⟨y, hy, hyy⟩ := x9Facts_cert.sq
  rw [mem_subW9_iff, crMat_d9, ← hyy]
  exact Submonoid.mul_mem _ hy hy

theorem d9_ne_one : d9 ≠ 1 := by
  intro e
  apply x9Facts_cert.ne
  rw [← crMat_d9, e, map_one]

theorem d9_central : ∀ y ∈ subW xWords9, y * d9 = d9 * y := by
  have hle : subW xWords9 ≤ Subgroup.centralizer ({d9} : Set Cr) := by
    rw [subW, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply crMat_injective
    simp only [map_mul]
    rw [crMat_gensW9 hk, crMat_d9]
    exact x9Facts_cert.commD ⟨k, hk⟩
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

theorem exists_sq_d9 : ∃ y ∈ subW xWords9, y * y = d9 := by
  obtain ⟨y, hy, hyy⟩ := x9Facts_cert.sq
  rw [matGrp9_eq] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨y', hy', crMat_injective ?_⟩
  rw [map_mul, crMat_d9]
  exact hyy

theorem sq_central_C9 {y : Cr} (hy : y ∈ subW xWords9)
    (hc : ∀ x ∈ subW xWords9, x * (y * y) = (y * y) * x) : y * y = 1 ∨ y * y = d9 := by
  have hcard : Nat.card (matGrp xWords9) ≤ 6144 := by
    rw [matGrp9_eq, card_map_subW, card_subW9]
  have hc' : ∀ x ∈ matGrp xWords9, x * (crMat y * crMat y) = crMat y * crMat y * x := by
    intro x hx
    rw [matGrp9_eq] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    simpa only [map_mul] using congrArg crMat (hc x' hx')
  rcases x9Facts_cert.cen hcard (crMat y) (mem_subW9_iff.1 hy) hc' with e | e
  · left
    apply crMat_injective
    rw [map_mul, e, map_one]
  · right
    apply crMat_injective
    rw [map_mul, e, crMat_d9]

theorem isConj_rep9_mul_d9 : IsConj (rep 9) (rep 9 * d9) := by
  obtain ⟨g, hg, e⟩ := x9Facts_cert.conj9
  obtain ⟨g', rfl⟩ := MonoidHom.mem_mrange.1 (Cm_le_mrange hg)
  have e' : g' * rep 9 = rep 9 * d9 * g' := by
    apply crMat_injective
    simp only [map_mul]
    rw [crMat_rep (by norm_num), crMat_d9]
    exact e
  exact isConj_iff.2 ⟨g', by rw [e', mul_inv_cancel_right]⟩

theorem isConj_rep1_r_mul_d9 : IsConj (rep 1) (rCr * d9) := by
  obtain ⟨g, hg, e⟩ := x9Facts_cert.conj1
  obtain ⟨g', rfl⟩ := MonoidHom.mem_mrange.1 (Cm_le_mrange hg)
  have e' : g' * rep 1 = rep 0 * d9 * g' := by
    apply crMat_injective
    simp only [map_mul]
    rw [crMat_rep (by norm_num), crMat_rep (by norm_num), crMat_d9]
    exact e
  rw [← rep_zero]
  exact isConj_iff.2 ⟨g', by rw [e', mul_inv_cancel_right]⟩

theorem nine_facts {a : Cr} (ha : IsConj (rep 9) a) : ∃ d : Cr,
    d ∈ Subgroup.centralizer ({a} : Set Cr) ∧ d ≠ 1 ∧
    (∀ x ∈ Subgroup.centralizer ({a} : Set Cr), x * d = d * x) ∧
    (∃ y ∈ Subgroup.centralizer ({a} : Set Cr), y * y = d) ∧
    (∀ y ∈ Subgroup.centralizer ({a} : Set Cr),
      (∀ x ∈ Subgroup.centralizer ({a} : Set Cr), x * (y * y) = (y * y) * x) →
        y * y = 1 ∨ y * y = d) ∧
    IsConj a (a * d) ∧ IsConj (rep 1) (rCr * d) := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 ha
  have hC : ∀ x, x ∈ Subgroup.centralizer ({g * rep 9 * g⁻¹} : Set Cr) ↔
      g⁻¹ * x * g ∈ subW xWords9 := by
    intro x
    rw [subW_eq_C9, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      calc g⁻¹ * x * g * rep 9 = g⁻¹ * (x * (g * rep 9 * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * rep 9 * g⁻¹) * x) * g := by rw [hx]
        _ = rep 9 * (g⁻¹ * x * g) := by group
    · intro hx
      calc x * (g * rep 9 * g⁻¹) = g * ((g⁻¹ * x * g) * rep 9) * g⁻¹ := by group
        _ = g * (rep 9 * (g⁻¹ * x * g)) * g⁻¹ := by rw [hx]
        _ = g * rep 9 * g⁻¹ * x := by group
  refine ⟨g * d9 * g⁻¹, (hC _).2 (by simpa [mul_assoc] using d9_mem), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    apply d9_ne_one
    calc d9 = g⁻¹ * (g * d9 * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group
  · intro x hx
    have h1 := d9_central _ ((hC x).1 hx)
    calc x * (g * d9 * g⁻¹) = g * ((g⁻¹ * x * g) * d9) * g⁻¹ := by group
      _ = g * (d9 * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * d9 * g⁻¹ * x := by group
  · obtain ⟨y, hy, hyd⟩ := exists_sq_d9
    refine ⟨g * y * g⁻¹, (hC _).2 (by simpa [mul_assoc] using hy), ?_⟩
    rw [← hyd]
    group
  · intro y hy hc
    have hy' := (hC y).1 hy
    have hc' : ∀ x ∈ subW xWords9, x * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) =
        ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * x := by
      intro x hx
      have hx' : g * x * g⁻¹ ∈ Subgroup.centralizer ({g * rep 9 * g⁻¹} : Set Cr) :=
        (hC _).2 (by simpa [mul_assoc] using hx)
      have := hc _ hx'
      calc x * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) =
          g⁻¹ * ((g * x * g⁻¹) * (y * y)) * g := by group
        _ = g⁻¹ * ((y * y) * (g * x * g⁻¹)) * g := by rw [this]
        _ = ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * x := by group
    rcases sq_central_C9 hy' hc' with e | e
    · left
      calc y * y = g * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = 1 := by rw [e]; group
    · right
      calc y * y = g * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * d9 * g⁻¹ := by rw [e]
  · obtain ⟨f, hf⟩ := isConj_iff.1 isConj_rep9_mul_d9
    refine isConj_iff.2 ⟨g * f * g⁻¹, ?_⟩
    calc g * f * g⁻¹ * (g * rep 9 * g⁻¹) * (g * f * g⁻¹)⁻¹ = g * (f * rep 9 * f⁻¹) * g⁻¹ := by
          group
      _ = g * rep 9 * g⁻¹ * (g * d9 * g⁻¹) := by rw [hf]; group
  · obtain ⟨e, he⟩ := isConj_iff.1 isConj_rep1_r_mul_d9
    refine isConj_iff.2 ⟨g * e, ?_⟩
    calc g * e * rep 1 * (g * e)⁻¹ = g * (e * rep 1 * e⁻¹) * g⁻¹ := by group
      _ = g * (rCr * d9) * g⁻¹ := by rw [he]
      _ = (g * rCr * g⁻¹) * (g * d9 * g⁻¹) := by group
      _ = rCr * (g * d9 * g⁻¹) := by rw [conj_rCr]

namespace Co2CentHyp

variable {G : Type} [Group G] (h : Co2CentHyp G)

theorem not_isConj_rep_nine {t : h.H} (ht : IsConj h.z (t : G)) :
    ¬ IsConj (h.φ t) (rep 9) := by
  intro hti
  have htz : t ≠ h.zG := by
    rintro rfl
    rw [h.φ_zG] at hti
    exact not_isConj_rCr_rep (by norm_num) (by decide) hti
  obtain ⟨s, hs, -, Ψ, h1, h2, c, -, -, hΨ⟩ := h.exists_partner ht htz
  obtain ⟨hs2, hs1⟩ := h.φ_invol hs
  obtain ⟨j, hj, hsj⟩ := exists_isConj_rep (h.φ s) hs2 hs1
  have hp : PartnerPair 9 j := PartnerElts.of_conj ⟨Ψ, h1, h2⟩ hti hsj
  obtain rfl : j = 9 := by
    have := classSizes_eq_of_partnerPair (by norm_num) hj hp
    interval_cases j <;> first | rfl | (simp [classSizes] at this)
  obtain ⟨dt, hdt, hdt1, hdtc, ⟨y, hy, hyy⟩, -, hdtconj, -⟩ := nine_facts hti.symm
  obtain ⟨ds, -, -, -, -, hdsuniq, -, hdsr⟩ := nine_facts hsj.symm
  have hsq : Ψ ⟨y, hy⟩ * Ψ ⟨y, hy⟩ = Ψ ⟨dt, hdt⟩ :=
    (map_mul Ψ _ _).symm.trans (congrArg Ψ (Subtype.ext hyy))
  have hcen : ∀ x ∈ Subgroup.centralizer ({h.φ s} : Set Cr),
      x * (((Ψ ⟨y, hy⟩ : Subgroup.centralizer _) : Cr) * (Ψ ⟨y, hy⟩ : Cr)) =
        (((Ψ ⟨y, hy⟩ : Subgroup.centralizer _) : Cr) * (Ψ ⟨y, hy⟩ : Cr)) * x := by
    intro x hx
    obtain ⟨x', hx'⟩ := Ψ.surjective ⟨x, hx⟩
    have hc : Ψ x' * Ψ ⟨dt, hdt⟩ = Ψ ⟨dt, hdt⟩ * Ψ x' :=
      (map_mul Ψ _ _).symm.trans ((congrArg Ψ (Subtype.ext (hdtc _ x'.2))).trans
        (map_mul Ψ _ _))
    have hc2 : (⟨x, hx⟩ : Subgroup.centralizer ({h.φ s} : Set Cr)) *
        (Ψ ⟨y, hy⟩ * Ψ ⟨y, hy⟩) = (Ψ ⟨y, hy⟩ * Ψ ⟨y, hy⟩) * ⟨x, hx⟩ := by
      calc (⟨x, hx⟩ : Subgroup.centralizer ({h.φ s} : Set Cr)) * (Ψ ⟨y, hy⟩ * Ψ ⟨y, hy⟩)
          = Ψ x' * Ψ ⟨dt, hdt⟩ := congrArg₂ (· * ·) hx'.symm hsq
        _ = Ψ ⟨dt, hdt⟩ * Ψ x' := hc
        _ = (Ψ ⟨y, hy⟩ * Ψ ⟨y, hy⟩) * ⟨x, hx⟩ := congrArg₂ (· * ·) hsq.symm hx'
    exact congrArg Subtype.val hc2
  have hΨd : ((Ψ ⟨dt, hdt⟩ : Subgroup.centralizer _) : Cr) = ds := by
    rcases hdsuniq _ (Ψ ⟨y, hy⟩).2 hcen with e | e
    · exfalso
      have h1' : Ψ ⟨dt, hdt⟩ = 1 := by rw [← hsq]; exact Subtype.ext e
      exact hdt1 (congrArg Subtype.val (Ψ.injective (h1'.trans (map_one Ψ).symm)))
    · rw [← hsq]
      exact e
  have e1 : ((Ψ (selfC (h.φ t) * ⟨dt, hdt⟩) : Subgroup.centralizer ({h.φ s} : Set Cr)) : Cr) =
      rCr * ds :=
    (congrArg Subtype.val (map_mul Ψ _ _)).trans
      (congrArg₂ (· * ·) (congrArg Subtype.val h1) hΨd)
  have hG : ((h.φ.symm (rCr * ds) : h.H) : G) =
      c⁻¹ * ((h.φ.symm (h.φ t * dt) : h.H) : G) * c :=
    (congrArg (fun x => ((h.φ.symm x : h.H) : G)) e1).symm.trans
      (hΨ (selfC (h.φ t) * ⟨dt, hdt⟩))
  have hz : IsConj h.z ((h.φ.symm (rCr * ds) : h.H) : G) := by
    have h3 := h.isConj_φ_symm hdtconj
    rw [MulEquiv.symm_apply_apply] at h3
    refine (ht.trans h3).trans (isConj_iff.2 ⟨c⁻¹, ?_⟩)
    rw [inv_inv]
    exact hG.symm
  apply h.not_isConj_rep_of_bad hz (i := 1) (Or.inl rfl)
  rw [MulEquiv.apply_symm_apply]
  exact hdsr.symm

end Co2CentHyp

end CFSG.RankThree.Co2

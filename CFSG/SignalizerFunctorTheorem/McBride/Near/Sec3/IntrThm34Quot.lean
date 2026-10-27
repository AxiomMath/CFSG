module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Step3
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm34Core

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm34

variable {Γ : Type u} [Group Γ]

theorem fittingPre_eq_inf_qpre {R D D₂ : Subgroup Γ} (hD : D ≤ AChief.nrm R) (hD₂ : D ⊓ R = D₂)
    [(D₂.subgroupOf D).Normal] :
    fittingPre D D₂ =
      D ⊓ SolQuot.qpre R (CFSG.fittingSubgroupOf (AChief.qimg R D)) := by
  subst hD₂
  set φ := SolQuot.qres R D hD with hφ
  have hker : (D ⊓ R).subgroupOf D = φ.ker := by
    rw [SolQuot.ker_qres hD]
    exact Subgroup.inf_subgroupOf_left R D
  let e : ↥D ⧸ (D ⊓ R).subgroupOf D ≃* ↥(AChief.qimg R D) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ (SolQuot.qres_surjective hD))
  have he : ∀ y : ↥D, e (QuotientGroup.mk y) = φ y := fun y => rfl
  have hF : ∀ z, z ∈ CFSG.fittingSubgroup (↥D ⧸ (D ⊓ R).subgroupOf D) ↔
      e z ∈ CFSG.fittingSubgroup ↥(AChief.qimg R D) := by
    intro z
    rw [← fittingSubgroup_map_equiv e]
    constructor
    · intro hz
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z', hz', hzz⟩
      exact (e.injective hzz) ▸ hz'
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨y.2, SolQuot.mem_qpre_iff.mpr ⟨hD y.2, ?_⟩⟩
    exact ⟨φ y, (hF _).mp hy, rfl⟩
  · intro hx
    obtain ⟨hxD, hxq⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxN, z, hz, hzx⟩ := SolQuot.mem_qpre_iff.mp hxq
    have hzφ : z = φ ⟨x, hxD⟩ := Subtype.ext hzx
    refine ⟨⟨x, hxD⟩, ?_, rfl⟩
    have h1 : QuotientGroup.mk' ((D ⊓ R).subgroupOf D) ⟨x, hxD⟩ ∈
        CFSG.fittingSubgroup (↥D ⧸ (D ⊓ R).subgroupOf D) := (hF _).mpr (hzφ ▸ hz)
    exact h1

theorem isChiefFactorOf_qimg_inf {R D M : Subgroup Γ} (hD : D ≤ AChief.nrm R)
    (h : IsChiefFactorOf D M (D ⊓ R)) :
    IsChiefFactorOf (AChief.qimg R D) (AChief.qimg R M) ⊥ := by
  obtain ⟨-, hM, hlt, hmin⟩ := h
  have hMD : M ≤ D := hM.1
  have hMN : M ≤ AChief.nrm R := hMD.trans hD
  refine ⟨isNormalIn_bot _, ⟨SolQuot.qimg_mono hMD, AChief.qimg_le_normalizer hM.2⟩, ?_, ?_⟩
  · refine bot_lt_iff_ne_bot.mpr fun hb => ?_
    exact hlt.not_ge (le_inf hMD ((SolQuot.qimg_eq_bot_iff hMN).mp hb))
  · intro K' hK' _ hK'M
    have hqM' : AChief.qimg R (M ⊓ SolQuot.qpre R K') = K' := by
      rw [SolQuot.qimg_inf_of_le (SolQuot.qpre_le_nrm K') (SolQuot.le_qpre K'),
        SolQuot.qimg_qpre]
      exact inf_eq_right.mpr hK'M
    have hM'D : M ⊓ SolQuot.qpre R K' ≤ D := inf_le_left.trans hMD
    have hDRM' : D ⊓ R ≤ M ⊓ SolQuot.qpre R K' :=
      le_inf hlt.le (inf_le_right.trans (SolQuot.le_qpre K'))
    have hnor : D ≤ Subgroup.normalizer ((M ⊓ SolQuot.qpre R K' : Subgroup Γ) : Set Γ) := by
      refine (SolQuot.qimg_le_normalizer_iff hM'D hDRM' hD le_rfl).mp ?_
      rw [hqM']
      exact hK'.2
    rcases hmin (M ⊓ SolQuot.qpre R K') ⟨hM'D, hnor⟩ hDRM' inf_le_left with h | h
    · left
      rw [← hqM', h]
      exact (SolQuot.qimg_eq_bot_iff (inf_le_left.trans hD)).mpr inf_le_right
    · right
      rw [← hqM', h]

theorem isChiefFactorOf_inf_qpre {R D : Subgroup Γ} {M' : Subgroup (AChief.QG R)}
    (hD : D ≤ AChief.nrm R) (h : IsChiefFactorOf (AChief.qimg R D) M' ⊥) :
    IsChiefFactorOf D (D ⊓ SolQuot.qpre R M') (D ⊓ R) := by
  obtain ⟨-, hM', hlt, hmin⟩ := h
  have hMD : D ⊓ SolQuot.qpre R M' ≤ D := inf_le_left
  have hqM : AChief.qimg R (D ⊓ SolQuot.qpre R M') = M' := by
    rw [SolQuot.qimg_inf_of_le (SolQuot.qpre_le_nrm M') (SolQuot.le_qpre M'), SolQuot.qimg_qpre]
    exact inf_eq_right.mpr hM'.1
  have hDRM : D ⊓ R ≤ D ⊓ SolQuot.qpre R M' :=
    le_inf inf_le_left (inf_le_right.trans (SolQuot.le_qpre M'))
  refine ⟨⟨inf_le_left, Thm32.le_normalizer_inf Subgroup.le_normalizer hD⟩,
    ⟨hMD, (SolQuot.qimg_le_normalizer_iff hMD hDRM hD le_rfl).mp (by rw [hqM]; exact hM'.2)⟩,
    lt_of_le_of_ne hDRM fun heq => ?_, ?_⟩
  · have h1 : AChief.qimg R (D ⊓ SolQuot.qpre R M') = ⊥ := by
      rw [← heq]
      exact (SolQuot.qimg_eq_bot_iff (inf_le_left.trans hD)).mpr inf_le_right
    rw [hqM] at h1
    exact hlt.ne' h1
  · intro K₁ hK₁ hDRK₁ hK₁M
    have hK₁D : K₁ ≤ D := hK₁.1
    have hqK₁ : AChief.qimg R K₁ ≤ M' := hqM ▸ SolQuot.qimg_mono hK₁M
    rcases hmin (AChief.qimg R K₁) ⟨SolQuot.qimg_mono hK₁D, AChief.qimg_le_normalizer hK₁.2⟩
      bot_le hqK₁ with h0 | h0
    · left
      exact le_antisymm (le_inf hK₁D ((SolQuot.qimg_eq_bot_iff (hK₁D.trans hD)).mp h0)) hDRK₁
    · right
      have h1 : D ⊓ SolQuot.qpre R M' ≤ K₁ ⊔ R :=
        (SolQuot.qimg_le_qimg_iff (hMD.trans hD) (hK₁D.trans hD)).mp (by rw [hqM, h0])
      exact le_antisymm hK₁M (Thm32.le_of_le_sup_of_inf_le hK₁M (hK₁D.trans hD)
        ((inf_le_inf_right R hMD).trans hDRK₁) h1)

theorem eq_inf_qpre_qimg {R D M : Subgroup Γ} (hD : D ≤ AChief.nrm R) (hMD : M ≤ D)
    (hDRM : D ⊓ R ≤ M) : M = D ⊓ SolQuot.qpre R (AChief.qimg R M) := by
  rw [SolQuot.qpre_qimg (hMD.trans hD)]
  refine le_antisymm (le_inf hMD le_sup_left) ?_
  exact Thm32.le_of_le_sup_of_inf_le (L := M) (Z := D ⊓ (M ⊔ R)) (R := R)
    (le_inf hMD le_sup_left) (hMD.trans hD) ((inf_le_inf_right R inf_le_left).trans hDRM)
    inf_le_right

theorem thm34_of_quotient {R D X₁ : Subgroup Γ} (hD : D ≤ AChief.nrm R)
    (hX₁ : X₁ ≤ AChief.nrm R) (hRX₁ : R ≤ X₁) [((D ⊓ R).subgroupOf D).Normal]
    [((D ⊓ R).subgroupOf (D ⊓ X₁)).Normal]
    (ha : CFSG.fittingSubgroupOf (AChief.qimg R D) =
      CFSG.fittingSubgroupOf (AChief.qimg R D ⊓ AChief.qimg R X₁))
    (hb : IsChiefFactorOf (AChief.qimg R D) (CFSG.fittingSubgroupOf (AChief.qimg R D)) ⊥)
    (hc : ∀ M, IsChiefFactorOf (AChief.qimg R D) M ⊥ →
      M = CFSG.fittingSubgroupOf (AChief.qimg R D)) :
    fittingPre (D ⊓ X₁) (D ⊓ R) = fittingPre D (D ⊓ R) ∧
      IsChiefFactorOf D (fittingPre D (D ⊓ R)) (D ⊓ R) ∧
      ∀ M, IsChiefFactorOf D M (D ⊓ R) → M = fittingPre D (D ⊓ R) := by
  have e1 : fittingPre D (D ⊓ R) =
      D ⊓ SolQuot.qpre R (CFSG.fittingSubgroupOf (AChief.qimg R D)) :=
    fittingPre_eq_inf_qpre hD rfl
  refine ⟨?_, ?_, fun M hM => ?_⟩
  · have hD₁ : D ⊓ X₁ ≤ AChief.nrm R := inf_le_left.trans hD
    have e2 : fittingPre (D ⊓ X₁) (D ⊓ R) = (D ⊓ X₁) ⊓
        SolQuot.qpre R (CFSG.fittingSubgroupOf (AChief.qimg R (D ⊓ X₁))) :=
      fittingPre_eq_inf_qpre hD₁ (by
        rw [inf_assoc, inf_eq_right.mpr hRX₁])
    have hFK : CFSG.fittingSubgroupOf (AChief.qimg R D) ≤ AChief.qimg R X₁ := by
      rw [ha]
      exact (Subgroup.map_subtype_le _).trans inf_le_right
    have hQX : SolQuot.qpre R (CFSG.fittingSubgroupOf (AChief.qimg R D)) ≤ X₁ := by
      refine (SolQuot.qpre_mono hFK).trans ?_
      rw [SolQuot.qpre_qimg hX₁, sup_eq_left.mpr hRX₁]
    rw [e1, e2, SolQuot.qimg_inf_of_le hX₁ hRX₁, ← ha]
    exact le_antisymm (inf_le_inf_right _ inf_le_left)
      (le_inf (le_inf inf_le_left (inf_le_right.trans hQX)) inf_le_right)
  · rw [e1]
    exact isChiefFactorOf_inf_qpre hD hb
  · have hq := isChiefFactorOf_qimg_inf hD hM
    rw [e1, ← hc _ hq]
    exact eq_inf_qpre_qimg hD hM.2.1.1 hM.2.2.1.le

section Setting

variable {p : ℕ} {A X X₁ X₂ : Subgroup Γ}

theorem chiefSetting_qimg (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairs A X) :
    Thm32.ChiefSetting p (AChief.qimg X₂ A) (AChief.qimg X₂ (X₁ ⊔ cenIn X (A : Set Γ)))
      (AChief.qimg X₂ X₁) (AChief.qimg X₂ (cenIn X (A : Set Γ))) ∧
    cenIn (AChief.qimg X₂ (X₁ ⊔ cenIn X (A : Set Γ))) (AChief.qimg X₂ A : Set (AChief.QG X₂)) =
      AChief.qimg X₂ (cenIn X (A : Set Γ)) := by
  have hP' : (X₁, X₂) ∈ iPairsY A X (X₂ ⊓ cenIn X (A : Set Γ)) := ⟨hP, rfl⟩
  have hch := Thm32.chief_of_mem_iPairsY hP'
  have hsec := Thm32.secCen_of_mem_iPairsY hP'
  have hX₁ := Thm32.isDAIn_left_of_mem_iPairsY hP'
  set D := cenIn X (A : Set Γ) with hD
  have hDX : D ≤ X := inf_le_left
  have hDA : D ≤ Subgroup.centralizer (A : Set Γ) := inf_le_right
  have hGX : X₁ ⊔ D ≤ X := sup_le hX₁.1 hDX
  have hcop : Nat.Coprime p (Nat.card ↥(X₁ ⊔ D)) :=
    h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le hGX)
  have S0 : Thm32.BackSetting p A D X₁ X₂ A := ⟨h.prime, h.elemAbelian, hDA, hcop, hch, le_rfl⟩
  have hG : NearAsolvAction p A (X₁ ⊔ D) := Thm211.nearAsolvAction_of_le h hGX S0.A_le_nor_G
  have hq : NearAsolvAction p (AChief.qimg X₂ A) (AChief.qimg X₂ (X₁ ⊔ D)) :=
    Thm211.nearAsolvAction_qimg hG S0.G_le_nrm S0.A_le_nrm
  have hGX₁ : X₁ ⊔ D ≤ Subgroup.normalizer (X₁ : Set Γ) :=
    sup_le Subgroup.le_normalizer S0.D_le_nor_X₁
  refine ⟨⟨hq, SolQuot.qimg_mono le_sup_left, SolQuot.qimg_mono le_sup_right,
    Thm32.qimg_le_centralizer hDA, (SolQuot.qimg_sup S0.X₁_le_nrm S0.D_le_nrm).symm, ?_, ?_⟩, ?_⟩
  · have h1 := Thm32.isChiefFactorOf_qimg (R := X₂) S0.E_le_nor_X₂ hch
    rwa [SolQuot.qimg_sup S0.G_le_nrm S0.A_le_nrm] at h1
  · exact Thm32.qimg_inf_centralizer_eq_bot S0.G_le_nrm le_sup_left hGX₁ hsec.le
  · have hcen : (X₁ ⊔ D) ⊓ Subgroup.centralizer (A : Set Γ) = D :=
      le_antisymm (inf_le_inf_right _ hGX) (le_inf le_sup_right hDA)
    have := AChief.qimg_inf_centralizer h.prime h.elemAbelian S0.A_le_nor_G S0.A_le_nrm
      S0.G_le_nrm hcop
    rw [hcen] at this
    exact this.symm

end Setting

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm34

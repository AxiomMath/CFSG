module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.ThetaLInfAux2
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Step3
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux1
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.FixedPoint

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33h

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv Thm32 Thm33a

variable {Γ : Type u} [Group Γ] {p : ℕ} {A X Y X₁ X₂ W N : Subgroup Γ} {a : Γ}

theorem not_mem_of_coprime {B : Subgroup Γ} (hp : p.Prime) (ha : a ^ p = 1) (ha1 : a ≠ 1)
    (hcop : Nat.Coprime p (Nat.card ↥B)) : a ∉ B := by
  intro haB
  have := Fact.mk hp
  have hord : orderOf a = p := orderOf_eq_prime ha ha1
  have h1 : orderOf a ∣ Nat.card ↥B := Subgroup.orderOf_dvd_natCard B haB
  rw [hord] at h1
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop h1)

theorem qimg_cenIn_singleton (hp : p.Prime)
    (hE : IsElemAbelian p (Subgroup.zpowers a))
    (haY : Subgroup.zpowers a ≤ Subgroup.normalizer (Y : Set Γ)) (ha : a ∈ AChief.nrm N)
    (hYN : Y ≤ AChief.nrm N) (hcop : Nat.Coprime p (Nat.card ↥Y)) :
    AChief.qimg N (cenIn Y ({a} : Set Γ)) =
      cenIn (AChief.qimg N Y) ({AChief.qmap N ⟨a, ha⟩} : Set (AChief.QG N)) := by
  have h := AChief.qimg_inf_centralizer hp hE haY (Subgroup.zpowers_le.2 ha) hYN hcop
  rw [SolQuot.qimg_zpowers ha] at h
  unfold cenIn
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
  exact h

variable [Finite Γ]

theorem le_of_normalized
    (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairsY A X Y)
    (ha : a ∈ A) (ha1 : a ≠ 1) (hWX₁ : W ≤ X₁) (hWa : W ≤ Subgroup.centralizer ({a} : Set Γ))
    (hWA : Admits A W) (hWY : W ⊓ cenIn X (A : Set Γ) ≤ X₂)
    (hWc : cenIn X₁ ({a} : Set Γ) ≤ Subgroup.normalizer (W : Set Γ)) : W ≤ X₂ := by
  have hch := chief_of_mem_iPairsY hP
  have hX₁ := isDAIn_left_of_mem_iPairsY hP
  set D := cenIn X (A : Set Γ) with hD
  have hDX : D ≤ X := inf_le_left
  have hDA : D ≤ Subgroup.centralizer (A : Set Γ) := inf_le_right
  have hGX : X₁ ⊔ D ≤ X := sup_le hX₁.1 hDX
  have hcop : Nat.Coprime p (Nat.card ↥(X₁ ⊔ D)) :=
    h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le hGX)
  have S0 : BackSetting p A D X₁ X₂ A := ⟨h.prime, h.elemAbelian, hDA, hcop, hch, le_rfl⟩
  have hG : NearAsolvAction p A (X₁ ⊔ D) := Thm211.nearAsolvAction_of_le h hGX S0.A_le_nor_G
  have hq : NearAsolvAction p (AChief.qimg X₂ A) (AChief.qimg X₂ (X₁ ⊔ D)) :=
    Thm211.nearAsolvAction_qimg hG S0.G_le_nrm S0.A_le_nrm
  have hGX₁ : X₁ ⊔ D ≤ Subgroup.normalizer (X₁ : Set Γ) :=
    sup_le Subgroup.le_normalizer S0.D_le_nor_X₁
  have hCS : ChiefSetting p (AChief.qimg X₂ A) (AChief.qimg X₂ (X₁ ⊔ D)) (AChief.qimg X₂ X₁)
      (AChief.qimg X₂ D) := by
    refine ⟨hq, SolQuot.qimg_mono le_sup_left, SolQuot.qimg_mono le_sup_right,
      qimg_le_centralizer hDA,
      (SolQuot.qimg_sup S0.X₁_le_nrm S0.D_le_nrm).symm, ?_, ?_⟩
    · have h1 := isChiefFactorOf_qimg (R := X₂) S0.E_le_nor_X₂ hch
      rwa [SolQuot.qimg_sup S0.G_le_nrm S0.A_le_nrm] at h1
    · exact qimg_inf_centralizer_eq_bot S0.G_le_nrm le_sup_left hGX₁
        (secCen_of_mem_iPairsY hP).le
  have hHyp : Lemma212.Hyp p (AChief.qimg X₂ A) (AChief.qimg X₂ (X₁ ⊔ D)) :=
    ⟨hCS.near, hCS.sol_eq_bot, by rw [hCS.layerIn_eq]; exact hCS.chief, hCS.prod_eq⟩
  have hkK : kOf (AChief.qimg X₂ (X₁ ⊔ D)) = AChief.qimg X₂ X₁ :=
    hHyp.layerIn_eq.symm.trans hCS.layerIn_eq
  have hAn : A ≤ AChief.nrm X₂ := S0.A_le_nrm
  have han : a ∈ AChief.nrm X₂ := hAn ha
  have hX₁n : X₁ ≤ AChief.nrm X₂ := S0.X₁_le_nrm
  have hX₂X : X₂ ≤ X := (pair_le₂ hP).trans (pair_le hP)
  have hcopX₂ : Nat.Coprime p (Nat.card ↥X₂) :=
    h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le hX₂X)
  have hāA : AChief.qmap X₂ ⟨a, han⟩ ∈ AChief.qimg X₂ A :=
    (AChief.mem_qimg_iff X₂ A _).2 ⟨⟨a, han⟩, ha, rfl⟩
  have hā1 : AChief.qmap X₂ ⟨a, han⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨a, han⟩ : ↥(AChief.nrm X₂)) ∈ X₂.subgroupOf (AChief.nrm X₂) :=
      (QuotientGroup.eq_one_iff _).mp h1
    exact not_mem_of_coprime h.prime (h.elemAbelian.2 a ha) ha1 hcopX₂
      (Subgroup.mem_subgroupOf.mp h2)
  have hcen := qimg_cenIn_singleton (N := X₂) (Y := X₁) h.prime
    (isElemAbelian_of_le h.elemAbelian (Subgroup.zpowers_le.2 ha))
    ((Subgroup.zpowers_le.2 ha).trans S0.A_le_nor_X₁) han hX₁n S0.coprime_X₁
  have hWn : W ≤ AChief.nrm X₂ := hWX₁.trans hX₁n
  have hWX : W ≤ X := hWX₁.trans (pair_le hP)
  have hWnear : NearAsolvAction p A W := Thm211.nearAsolvAction_of_le h hWX hWA
  have hWbarnear := Thm211.nearAsolvAction_qimg hWnear hWn hAn
  have hWB : signalizerMcBrideHypothesisB p (AChief.qimg X₂ W) :=
    signalizerMcBrideHypothesisB_of_nearPSolvable h.prime hWbarnear.nearPSolvable
  have hWbarA : cenIn (AChief.qimg X₂ W)
      ((AChief.qimg X₂ A : Subgroup (AChief.QG X₂)) : Set (AChief.QG X₂)) = ⊥ := by
    have hcopW : Nat.Coprime p (Nat.card ↥W) :=
      h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le hWX)
    have key := AChief.qimg_inf_centralizer (N := X₂) h.prime h.elemAbelian hWA hAn hWn hcopW
    show AChief.qimg X₂ W ⊓ Subgroup.centralizer
      ((AChief.qimg X₂ A : Subgroup (AChief.QG X₂)) : Set (AChief.QG X₂)) = ⊥
    rw [← key]
    refine le_bot_iff.mp ?_
    have hle : W ⊓ Subgroup.centralizer (A : Set Γ) ≤ X₂ := fun x hx =>
      hWY (Subgroup.mem_inf.mpr ⟨hx.1, Subgroup.mem_inf.mpr ⟨hWX hx.1, hx.2⟩⟩)
    exact (SolQuot.qimg_mono hle).trans SolQuot.qimg_self.le
  have hWbarsol : Group.IsSolvable ↥(AChief.qimg X₂ W) :=
    isSolvable_of_inf_centralizer_eq_bot h.prime (AChief.isElemAbelian_qimg h.elemAbelian)
      (AChief.qimg_le_normalizer hWA) hWB hWbarA
  have hWK : AChief.qimg X₂ W ≤ cenIn (kOf (AChief.qimg X₂ (X₁ ⊔ D)))
      ({AChief.qmap X₂ ⟨a, han⟩} : Set (AChief.QG X₂)) := by
    rw [hkK, ← hcen]
    exact SolQuot.qimg_mono (le_inf hWX₁ hWa)
  have hWadm : Admits (AChief.qimg X₂ A ⊔ cenIn (kOf (AChief.qimg X₂ (X₁ ⊔ D)))
      ({AChief.qmap X₂ ⟨a, han⟩} : Set (AChief.QG X₂))) (AChief.qimg X₂ W) := by
    rw [hkK, ← hcen]
    exact sup_le (AChief.qimg_le_normalizer hWA) (AChief.qimg_le_normalizer hWc)
  have hbot := eq_bot_of_normalized hHyp hāA hā1 hWK hWadm hWbarsol hWbarA
  exact (SolQuot.qimg_eq_bot_iff hWn).1 hbot

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33h

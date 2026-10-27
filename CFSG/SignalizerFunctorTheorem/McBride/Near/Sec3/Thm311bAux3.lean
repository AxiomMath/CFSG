module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm311bAux2
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Step3
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Basic

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm311b

variable {Γ : Type u} [Group Γ] {p : ℕ} {A X Y X₁ X₂ : Subgroup Γ}

section Quotient

variable [Finite Γ]

omit [Finite Γ] in
theorem chiefSetting_of_mem_iPairsY (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairsY A X Y) :
    Thm32.ChiefSetting p (AChief.qimg X₂ A) (AChief.qimg X₂ (X₁ ⊔ cenIn X (A : Set Γ)))
      (AChief.qimg X₂ X₁) (AChief.qimg X₂ (cenIn X (A : Set Γ))) := by
  have hch := Thm32.chief_of_mem_iPairsY hP
  have hsec := Thm32.secCen_of_mem_iPairsY hP
  have hX₁ := Thm32.isDAIn_left_of_mem_iPairsY hP
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
  refine ⟨hq, SolQuot.qimg_mono le_sup_left, SolQuot.qimg_mono le_sup_right,
    Thm32.qimg_le_centralizer hDA,
    (SolQuot.qimg_sup S0.X₁_le_nrm S0.D_le_nrm).symm, ?_, ?_⟩
  · have h1 := Thm32.isChiefFactorOf_qimg (R := X₂) S0.E_le_nor_X₂ hch
    rwa [SolQuot.qimg_sup S0.G_le_nrm S0.A_le_nrm] at h1
  · exact Thm32.qimg_inf_centralizer_eq_bot S0.G_le_nrm le_sup_left hGX₁ hsec.le

theorem hyp_of_mem_iPairsY (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairsY A X Y) :
    Lemma212.Hyp p (AChief.qimg X₂ A) (AChief.qimg X₂ (X₁ ⊔ cenIn X (A : Set Γ))) := by
  have hCS := chiefSetting_of_mem_iPairsY h hP
  exact ⟨hCS.near, hCS.sol_eq_bot, by rw [hCS.layerIn_eq]; exact hCS.chief, hCS.prod_eq⟩

theorem kOf_qimg_eq (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairsY A X Y) :
    kOf (AChief.qimg X₂ (X₁ ⊔ cenIn X (A : Set Γ))) = AChief.qimg X₂ X₁ := by
  have hCS := chiefSetting_of_mem_iPairsY h hP
  have hyp := hyp_of_mem_iPairsY h hP
  rw [← hyp.layerIn_eq, hCS.layerIn_eq]

theorem card_qimg_eq {R B : Subgroup Γ} (hp : p.Prime) (hB : IsPGroup p B)
    (hR : Nat.Coprime p (Nat.card R)) (hBN : B ≤ AChief.nrm R) :
    Nat.card (AChief.qimg R B) = Nat.card B := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hB.exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card R) := by
    rw [hn]
    exact hR.pow_left n
  have hdisj : Disjoint B R := Subgroup.disjoint_of_coprime_natCard hcop
  have hker : (SolQuot.qres R B hBN).ker = ⊥ := by
    rw [SolQuot.ker_qres, eq_bot_iff]
    intro x hx
    have h1 : (x : Γ) ∈ B ⊓ R := ⟨x.2, Subgroup.mem_subgroupOf.mp hx⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have hbij : Function.Bijective (SolQuot.qres R B hBN) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).mp hker, SolQuot.qres_surjective hBN⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

omit [Finite Γ] in
theorem exists_preimage_le {R A : Subgroup Γ} {B' : Subgroup (AChief.QG R)}
    (hB' : B' ≤ AChief.qimg R A) :
    ∃ B : Subgroup Γ, B ≤ A ∧ AChief.qimg R B = B' := by
  refine ⟨A ⊓ SolQuot.qpre R B', inf_le_left, ?_⟩
  rw [SolQuot.qimg_inf_of_le (SolQuot.qpre_le_nrm B') (SolQuot.le_qpre B'), SolQuot.qimg_qpre]
  exact inf_eq_right.mpr hB'

local notation "q" => AChief.qimg X₂

theorem mem_iPairsY_cen (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairsY A X Y)
    {B : Subgroup Γ} (hBA : B ≤ A)
    (hns : ¬ Group.IsSolvable ↥(cenIn (q X₁) ((q B : Subgroup (AChief.QG X₂)) : Set _)))
    (hch : IsChiefFactorOf (q A ⊔ cenIn (q (X₁ ⊔ cenIn X (A : Set Γ)))
      ((q B : Subgroup (AChief.QG X₂)) : Set _)) (cenIn (q X₁) ((q B : Subgroup (AChief.QG X₂)) :
        Set _)) ⊥)
    (hsol : sol (cenIn (q (X₁ ⊔ cenIn X (A : Set Γ))) ((q B : Subgroup (AChief.QG X₂)) : Set _)) =
      ⊥) :
    (cenIn X₁ (B : Set Γ), cenIn X₂ (B : Set Γ)) ∈ iPairsY A X Y := by
  have hch0 := Thm32.chief_of_mem_iPairsY hP
  have hinf := Thm32.inf_eq_of_mem_iPairsY hP
  have hX₁ := Thm32.isDAIn_left_of_mem_iPairsY hP
  have hX₂ := Thm32.isDAIn_right_of_mem_iPairsY hP
  set D := cenIn X (A : Set Γ) with hD
  have hDX : D ≤ X := inf_le_left
  have hDA : D ≤ Subgroup.centralizer (A : Set Γ) := inf_le_right
  have hGX : X₁ ⊔ D ≤ X := sup_le hX₁.1 hDX
  have hcop : Nat.Coprime p (Nat.card ↥(X₁ ⊔ D)) :=
    h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le hGX)
  have S : Thm32.BackSetting p A D X₁ X₂ B := ⟨h.prime, h.elemAbelian, hDA, hcop, hch0, hBA⟩
  refine Thm32.mem_iPairsY_of ?_ ?_ ?_ ?_ ?_
  · exact ⟨inf_le_left.trans hX₁.1, Thm32.le_normalizer_inf hX₁.2
      ((sup_le S.D_le_cen_B S.A_le_cen_B).trans Subgroup.le_normalizer)⟩
  · exact ⟨inf_le_left.trans hX₂.1, Thm32.le_normalizer_inf hX₂.2
      ((sup_le S.D_le_cen_B S.A_le_cen_B).trans Subgroup.le_normalizer)⟩
  · exact S.isChiefFactorOf_cen hns hch
  · exact S.secCenIn_cen h.solvable_cen hns hch hsol
  · calc cenIn X₂ (B : Set Γ) ⊓ D = X₂ ⊓ D :=
        le_antisymm (inf_le_inf_right _ inf_le_left)
          (le_inf (le_inf inf_le_left (inf_le_right.trans S.D_le_cen_B)) inf_le_right)
      _ = Y := hinf

theorem exists_family
    (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairsY A X Y) :
    ∃ 𝒰 : Set (Subgroup Γ), 𝒰.Nonempty ∧
      (∀ B ∈ 𝒰, B ≤ A ∧ Nat.card A = p * Nat.card B ∧
        (cenIn X₁ (B : Set Γ), cenIn X₂ (B : Set Γ)) ∈ iPairsY A X Y ∧
        ∀ d ∈ B, d ≠ 1 →
          (cenIn X₁ ({d} : Set Γ), cenIn X₂ ({d} : Set Γ)) ∈ iPairsY A X Y) ∧
      X₁ ≤ X₂ ⊔ ⨆ B ∈ 𝒰, cenIn X₁ (B : Set Γ) := by
  set D := cenIn X (A : Set Γ) with hD
  have hyp := hyp_of_mem_iPairsY h hP
  have hK := kOf_qimg_eq h hP
  obtain ⟨𝒰', hne, hspec, hgen⟩ := exists_free_family hyp
  have hch0 := Thm32.chief_of_mem_iPairsY hP
  have hX₁ := Thm32.isDAIn_left_of_mem_iPairsY hP
  have hDX : D ≤ X := inf_le_left
  have hDA : D ≤ Subgroup.centralizer (A : Set Γ) := inf_le_right
  have hGX : X₁ ⊔ D ≤ X := sup_le hX₁.1 hDX
  have hcop : Nat.Coprime p (Nat.card ↥(X₁ ⊔ D)) :=
    h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le hGX)
  have S0 : Thm32.BackSetting p A D X₁ X₂ A := ⟨h.prime, h.elemAbelian, hDA, hcop, hch0, le_rfl⟩
  have hX₂cop : Nat.Coprime p (Nat.card X₂) :=
    S0.coprime_X₁.coprime_dvd_right (Subgroup.card_dvd_of_le S0.X₂_le)
  have hApG : IsPGroup p A :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A h.elemAbelian
  have hfreeq : ∀ B', B' ∈ 𝒰' → ∀ J ∈ lcal (q (X₁ ⊔ D)),
      B' ⊓ Subgroup.normalizer (J : Set (AChief.QG X₂)) ≤
        Subgroup.centralizer (J : Set (AChief.QG X₂)) := fun B' hB' => (hspec B' hB').2.2
  have hpair : ∀ B : Subgroup Γ, B ≤ A → (∀ J ∈ lcal (q (X₁ ⊔ D)),
      q B ⊓ Subgroup.normalizer (J : Set (AChief.QG X₂)) ≤
        Subgroup.centralizer (J : Set (AChief.QG X₂))) →
      (cenIn X₁ (B : Set Γ), cenIn X₂ (B : Set Γ)) ∈ iPairsY A X Y := by
    intro B hBA hfree
    have hBA' : q B ≤ q A := SolQuot.qimg_mono hBA
    have hns := not_isSolvable_cenIn hyp hBA' hfree
    have hch := isChiefFactorOf_cenIn hyp hBA' hfree
    have hsol := sol_cenIn_eq_bot hyp hBA' hfree
    rw [hK] at hns hch
    exact mem_iPairsY_cen h hP hBA hns hch hsol
  refine ⟨{B | B ≤ A ∧ q B ∈ 𝒰'}, ?_, ?_, ?_⟩
  · obtain ⟨B', hB'⟩ := hne
    obtain ⟨B, hBA, hqB⟩ := exists_preimage_le (hspec B' hB').1
    exact ⟨B, hBA, hqB ▸ hB'⟩
  · rintro B ⟨hBA, hB⟩
    obtain ⟨-, hcard, hfree⟩ := hspec _ hB
    refine ⟨hBA, ?_, hpair B hBA hfree, ?_⟩
    · have h1 := card_qimg_eq h.prime hApG hX₂cop S0.A_le_nrm
      have h2 := card_qimg_eq h.prime (hApG.to_le hBA) hX₂cop (hBA.trans S0.A_le_nrm)
      rw [h1, h2] at hcard
      exact hcard
    · intro d hd hd1
      have hzA : Subgroup.zpowers d ≤ A := Subgroup.zpowers_le.mpr (hBA hd)
      have hzB : Subgroup.zpowers d ≤ B := Subgroup.zpowers_le.mpr hd
      have := hpair (Subgroup.zpowers d) hzA fun J hJ =>
        (inf_le_inf_right _ (SolQuot.qimg_mono hzB)).trans (hfree J hJ)
      have hc : Subgroup.centralizer ((Subgroup.zpowers d : Subgroup Γ) : Set Γ) =
          Subgroup.centralizer ({d} : Set Γ) := centralizer_zpowers_eq_singleton d
      simpa only [cenIn, hc] using this
  ·
    set T : Subgroup Γ := ⨆ B ∈ {B | B ≤ A ∧ q B ∈ 𝒰'}, cenIn X₁ (B : Set Γ) with hT
    have hTX₁ : T ≤ X₁ := iSup₂_le fun B _ => inf_le_left
    have hqle : q X₁ ≤ q T := by
      rw [← hK]
      refine hgen.trans (iSup₂_le fun B' hB' => ?_)
      obtain ⟨B, hBA, hqB⟩ := exists_preimage_le (hspec B' hB').1
      have hBmem : B ∈ {B | B ≤ A ∧ q B ∈ 𝒰'} := ⟨hBA, hqB ▸ hB'⟩
      have S : Thm32.BackSetting p A D X₁ X₂ B := ⟨h.prime, h.elemAbelian, hDA, hcop, hch0, hBA⟩
      have h1 : q (cenIn X₁ (B : Set Γ)) = cenIn (q X₁) (q B) := S.qimg_cenIn_X₁
      rw [hK, ← hqB, ← h1]
      exact SolQuot.qimg_mono (le_iSup₂ (f := fun B (_ : B ∈ {B | B ≤ A ∧ q B ∈ 𝒰'}) =>
        cenIn X₁ (B : Set Γ)) B hBmem)
    have := (SolQuot.qimg_le_qimg_iff S0.X₁_le_nrm (hTX₁.trans S0.X₁_le_nrm)).mp hqle
    rwa [sup_comm] at this

end Quotient

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm311b

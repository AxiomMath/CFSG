module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm36Aux1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Quot

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm36

variable {Γ : Type u} [Group Γ]

theorem le_sectionCentralizer {X₁ X₂ : Subgroup Γ} (h : X₂ ≤ X₁)
    (hn : X₁ ≤ Subgroup.normalizer (X₂ : Set Γ)) : X₂ ≤ sectionCentralizer X₂ X₁ := by
  intro z hz
  refine mem_sectionCentralizer_iff.mpr ⟨Subgroup.le_normalizer hz,
    Subgroup.le_normalizer (h hz), fun y hy => ?_⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp (hn hy) z⁻¹).mp (inv_mem hz)
  have e : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem hz (by simpa using h1)

theorem secCenIn_sup_le {p : ℕ} {A D X₁ X₂ : Subgroup Γ} (hp : p.Prime) (hA : IsElemAbelian p A)
    (hDA : D ≤ Subgroup.centralizer (A : Set Γ))
    (hXD : X₁ ⊓ Subgroup.centralizer (A : Set Γ) ≤ D) (hcop : Nat.Coprime p (Nat.card ↥X₁))
    (hc : IsChiefFactorOf (X₁ ⊔ D ⊔ A) X₁ X₂) (hns : ¬ IsSolvableSection X₁ X₂) :
    secCenIn (X₁ ⊔ D) X₁ X₂ ≤ X₂ ⊔ secCenIn D X₁ X₂ := by
  have hH : X₁ ⊔ D ⊔ A ≤ AChief.nrm X₂ := hc.1.2
  have hX₁H : X₁ ≤ X₁ ⊔ D ⊔ A := le_sup_left.trans le_sup_left
  have hDH : D ≤ X₁ ⊔ D ⊔ A := le_sup_right.trans le_sup_left
  have hAH : A ≤ X₁ ⊔ D ⊔ A := le_sup_right
  have hX₁n : X₁ ≤ AChief.nrm X₂ := hX₁H.trans hH
  have hDn : D ≤ AChief.nrm X₂ := hDH.trans hH
  have hAn : A ≤ AChief.nrm X₂ := hAH.trans hH
  have hX₂X₁ : X₂ ≤ X₁ := hc.2.2.1.le
  have hDnX₁ : D ≤ Subgroup.normalizer (X₁ : Set Γ) := hDH.trans hc.2.1.2
  have hAnX₁ : A ≤ Subgroup.normalizer (X₁ : Set Γ) := hAH.trans hc.2.1.2
  have hDnX₂ : D ≤ Subgroup.normalizer (X₂ : Set Γ) := hDn
  have hq := Thm32.isChiefFactorOf_qimg hH hc
  have hTns : ¬ Group.IsSolvable ↥(AChief.qimg X₂ X₁) := fun hs =>
    hns ((isSolvableSection_iff hX₁n).mpr hs)
  have hcenter := Thm32.inf_centralizer_self_eq_bot hq hTns
  intro g hg
  obtain ⟨hgXD, hgsc⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨hgN₂, hgN₁, hgcomm⟩ := mem_sectionCentralizer_iff.mp hgsc
  obtain ⟨x, hx, d, hd, rfl⟩ := (Thm32.mem_sup_iff_mul hDnX₁).mp hgXD
  have hxN : x ∈ AChief.nrm X₂ := hX₁n hx
  have hdN : d ∈ AChief.nrm X₂ := hDn hd
  set T := AChief.qimg X₂ X₁ with hT
  set xb : AChief.QG X₂ := AChief.qmap X₂ ⟨x, hxN⟩ with hxb
  set db : AChief.QG X₂ := AChief.qmap X₂ ⟨d, hdN⟩ with hdb
  have hxbT : xb ∈ T := (AChief.mem_qimg_iff X₂ X₁ _).mpr ⟨⟨x, hxN⟩, hx, rfl⟩
  have hgbar : xb * db ∈ Subgroup.centralizer (T : Set (AChief.QG X₂)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z' hz'
    obtain ⟨y, hy, rfl⟩ := (AChief.mem_qimg_iff X₂ X₁ z').mp hz'
    have h2 : ⁅x * d, (y : Γ)⁆ ∈ X₂ := hgcomm _ hy
    have h1 : ((⟨x, hxN⟩ * ⟨d, hdN⟩ : ↥(AChief.nrm X₂)) * y * (⟨x, hxN⟩ * ⟨d, hdN⟩)⁻¹ * y⁻¹ :
        ↥(AChief.nrm X₂)) ∈ X₂.subgroupOf (AChief.nrm X₂) := by
      rw [Subgroup.mem_subgroupOf]
      simpa [commutatorElement_def] using h2
    have h3 := (QuotientGroup.eq_one_iff _).mpr h1
    change AChief.qmap X₂ _ = 1 at h3
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_mul] at h3
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h3)).symm
  have hxA : xb ∈ Subgroup.centralizer ((AChief.qimg X₂ A : Subgroup (AChief.QG X₂)) :
      Set (AChief.QG X₂)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨a, ha, rfl⟩ := (AChief.mem_qimg_iff X₂ A z).mp hz
    set ab : AChief.QG X₂ := AChief.qmap X₂ a with hab
    have habT : ab ∈ Subgroup.normalizer (T : Set (AChief.QG X₂)) :=
      AChief.qimg_le_normalizer hAnX₁ ((AChief.mem_qimg_iff X₂ A _).mpr ⟨a, ha, rfl⟩)
    have habC := Thm211.normalizer_le_normalizer_centralizer T habT
    have h1 : ab * (xb * db) * ab⁻¹ ∈ Subgroup.centralizer (T : Set (AChief.QG X₂)) :=
      (Subgroup.mem_normalizer_iff.mp habC _).mp hgbar
    have hda : ab * db = db * ab := by
      rw [hab, hdb, ← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (Subgroup.mem_centralizer_iff.mp (hDA hd) (a : Γ) ha))
    have h2 : ab * (xb * db) * ab⁻¹ = (ab * xb * ab⁻¹) * db := by
      calc ab * (xb * db) * ab⁻¹ = ab * xb * (db * ab⁻¹) := by group
        _ = ab * xb * (ab⁻¹ * (ab * db * ab⁻¹)) := by group
        _ = ab * xb * (ab⁻¹ * (db * ab * ab⁻¹)) := by rw [hda]
        _ = (ab * xb * ab⁻¹) * db := by group
    have h3 : (ab * xb * ab⁻¹) * xb⁻¹ ∈ Subgroup.centralizer (T : Set (AChief.QG X₂)) := by
      have := mul_mem h1 (inv_mem hgbar)
      rw [h2] at this
      simpa [mul_assoc] using this
    have h4 : (ab * xb * ab⁻¹) * xb⁻¹ ∈ T :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp habT xb).mp hxbT) (inv_mem hxbT)
    have h5 : (ab * xb * ab⁻¹) * xb⁻¹ ∈ T ⊓ Subgroup.centralizer (T : Set (AChief.QG X₂)) :=
      ⟨h4, h3⟩
    rw [hcenter, Subgroup.mem_bot, mul_inv_eq_one] at h5
    calc ab * xb = ab * xb * ab⁻¹ * ab := by group
      _ = xb * ab := by rw [h5]
  have himg := AChief.qimg_inf_centralizer (N := X₂) hp hA hAnX₁ hAn hX₁n hcop
  have hxbmem : xb ∈ AChief.qimg X₂ (X₁ ⊓ Subgroup.centralizer (A : Set Γ)) := by
    rw [himg]
    exact ⟨hxbT, hxA⟩
  obtain ⟨z, hz, hzx⟩ := (AChief.mem_qimg_iff X₂ _ _).mp hxbmem
  obtain ⟨r, hr, hxr⟩ := Thm211.exists_mem_of_qmap_eq hzx
  have hxr' : x = (z : Γ) * r := hxr
  have hzD : (z : Γ) ∈ D := hXD hz
  set e : Γ := (z : Γ) * d with he
  have heD : e ∈ D := mul_mem hzD hd
  have hen₂ : e ∈ Subgroup.normalizer (X₂ : Set Γ) := hDnX₂ heD
  set r'' : Γ := e * (d⁻¹ * r * d) * e⁻¹ with hr''
  have hr'₂ : d⁻¹ * r * d ∈ X₂ := (Subgroup.mem_normalizer_iff''.mp (hDnX₂ hd) r).mp hr
  have hr''₂ : r'' ∈ X₂ := (Subgroup.mem_normalizer_iff.mp hen₂ _).mp hr'₂
  have hgeq : x * d = r'' * e := by
    rw [hr'', he, hxr']
    group
  have hsec : sectionCentralizer X₂ X₁ ≥ X₂ := le_sectionCentralizer hX₂X₁ (hX₁H.trans hH)
  have heSec : e ∈ sectionCentralizer X₂ X₁ := by
    have h1 : r''⁻¹ * (x * d) ∈ sectionCentralizer X₂ X₁ :=
      mul_mem (inv_mem (hsec hr''₂)) hgsc
    rw [hgeq] at h1
    simpa using h1
  rw [hgeq]
  exact Subgroup.mul_mem_sup hr''₂ (Subgroup.mem_inf.mpr ⟨heD, heSec⟩)

theorem le_normalizer_sup_of_commutator {Q X₂ Y : Subgroup Γ}
    (hY : Y ≤ Subgroup.normalizer (X₂ : Set Γ)) (hQ : Q ≤ Subgroup.normalizer (X₂ : Set Γ))
    (hc : ∀ g ∈ Q, ∀ y ∈ Y, ⁅g, y⁆ ∈ X₂) :
    Q ≤ Subgroup.normalizer ((X₂ ⊔ Y : Subgroup Γ) : Set Γ) := by
  have key : ∀ g ∈ Q, ∀ x ∈ X₂ ⊔ Y, g * x * g⁻¹ ∈ X₂ ⊔ Y := by
    intro g hg x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (Thm32.mem_sup_iff_mul hY).mp hx
    have h1 : g * a * g⁻¹ ∈ X₂ := (Subgroup.mem_normalizer_iff.mp (hQ hg) a).mp ha
    have h2 : g * b * g⁻¹ = ⁅g, b⁆ * b := by
      simp only [commutatorElement_def]
      group
    have h3 : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [h3, h2]
    exact mul_mem (Subgroup.mem_sup_left h1)
      (mul_mem (Subgroup.mem_sup_left (hc g hg b hb)) (Subgroup.mem_sup_right hb))
  intro g hg
  exact Thm211.mem_normalizer_of_forall (key g hg)
    (fun x hx => by simpa using key g⁻¹ (inv_mem hg) x hx)

theorem pairs_of_secCen {p : ℕ} {A W Y X₁ X₂ : Subgroup Γ} (h : NearAsolvAction p A W)
    (hX₁ : IsDAIn A W X₁) (hX₂ : IsDAIn A W X₂)
    (hc : IsChiefFactorOf (X₁ ⊔ cenIn W (A : Set Γ) ⊔ A) X₁ X₂) (hns : ¬ IsSolvableSection X₁ X₂)
    (hX₂Y : X₂ ⊓ cenIn W (A : Set Γ) ≤ Y) (hYadm : Admits (cenIn W (A : Set Γ) ⊔ A) Y)
    (hYD : Y ≤ cenIn W (A : Set Γ))
    (hsec : secCenIn (cenIn W (A : Set Γ)) X₁ X₂ = Y) :
    (X₁ ⊔ Y, X₂ ⊔ Y) ∈ iPairsY A W Y := by
  set D : Subgroup Γ := cenIn W (A : Set Γ) with hDdef
  have hDW : D ≤ W := inf_le_left
  have hDA : D ≤ Subgroup.centralizer (A : Set Γ) := inf_le_right
  have hX₂X₁ : X₂ ≤ X₁ := hc.2.2.1.le
  have hX₁H : X₁ ≤ X₁ ⊔ D ⊔ A := le_sup_left.trans le_sup_left
  have hDH : D ≤ X₁ ⊔ D ⊔ A := le_sup_right.trans le_sup_left
  have hAH : A ≤ X₁ ⊔ D ⊔ A := le_sup_right
  have hX₁n₂ : X₁ ≤ Subgroup.normalizer (X₂ : Set Γ) := hX₁H.trans hc.1.2
  have hDn₂ : D ≤ Subgroup.normalizer (X₂ : Set Γ) := hDH.trans hc.1.2
  have hAn₂ : A ≤ Subgroup.normalizer (X₂ : Set Γ) := hAH.trans hc.1.2
  have hDn₁ : D ≤ Subgroup.normalizer (X₁ : Set Γ) := hDH.trans hc.2.1.2
  have hAn₁ : A ≤ Subgroup.normalizer (X₁ : Set Γ) := hAH.trans hc.2.1.2
  have hDAn₂ : D ⊔ A ≤ Subgroup.normalizer (X₂ : Set Γ) := sup_le hDn₂ hAn₂
  have hDAn₁ : D ⊔ A ≤ Subgroup.normalizer (X₁ : Set Γ) := sup_le hDn₁ hAn₁
  have hYn₂ : Y ≤ Subgroup.normalizer (X₂ : Set Γ) := hYD.trans hDn₂
  have hYn₁ : Y ≤ Subgroup.normalizer (X₁ : Set Γ) := hYD.trans hDn₁
  have hYDA : D ⊔ A ≤ Subgroup.normalizer (Y : Set Γ) := hYadm
  have hYc : ∀ y ∈ Y, ∀ x ∈ X₁, ⁅y, x⁆ ∈ X₂ := by
    intro y hy x hx
    have : y ∈ secCenIn D X₁ X₂ := by
      rw [hsec]
      exact hy
    exact (mem_sectionCentralizer_iff.mp (Subgroup.mem_inf.mp this).2).2.2 x hx
  have hYc' : ∀ g ∈ X₁, ∀ y ∈ Y, ⁅g, y⁆ ∈ X₂ := by
    intro g hg y hy
    rw [← commutatorElement_inv]
    exact inv_mem (hYc y hy g hg)
  have hX₁N₂ : X₁ ≤ Subgroup.normalizer ((X₂ ⊔ Y : Subgroup Γ) : Set Γ) :=
    le_normalizer_sup_of_commutator hYn₂ hX₁n₂ hYc'
  have hX₁N₁ : X₁ ≤ Subgroup.normalizer ((X₁ ⊔ Y : Subgroup Γ) : Set Γ) :=
    le_normalizer_sup_of_commutator hYn₁ Subgroup.le_normalizer
      (fun g hg y hy => hX₂X₁ (hYc' g hg y hy))
  have hDAN₂ : D ⊔ A ≤ Subgroup.normalizer ((X₂ ⊔ Y : Subgroup Γ) : Set Γ) :=
    Thm32.le_normalizer_sup hDAn₂ hYDA
  have hDAN₁ : D ⊔ A ≤ Subgroup.normalizer ((X₁ ⊔ Y : Subgroup Γ) : Set Γ) :=
    Thm32.le_normalizer_sup hDAn₁ hYDA
  have hH'N₂ : X₁ ⊔ Y ⊔ D ⊔ A ≤ Subgroup.normalizer ((X₂ ⊔ Y : Subgroup Γ) : Set Γ) :=
    sup_le (sup_le (sup_le hX₁N₂ (le_sup_right.trans Subgroup.le_normalizer))
      (le_sup_left.trans hDAN₂)) (le_sup_right.trans hDAN₂)
  have hH'N₁ : X₁ ⊔ Y ⊔ D ⊔ A ≤ Subgroup.normalizer ((X₁ ⊔ Y : Subgroup Γ) : Set Γ) :=
    sup_le (sup_le Subgroup.le_normalizer (le_sup_left.trans hDAN₁)) (le_sup_right.trans hDAN₁)
  have hX₁H' : X₁ ≤ X₁ ⊔ Y ⊔ D ⊔ A := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hYH' : Y ≤ X₁ ⊔ Y ⊔ D ⊔ A := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hXYH' : X₁ ⊔ Y ≤ X₁ ⊔ Y ⊔ D ⊔ A := le_sup_left.trans le_sup_left
  have hHH' : X₁ ⊔ D ⊔ A ≤ X₁ ⊔ Y ⊔ D ⊔ A :=
    sup_le (sup_le hX₁H' (le_sup_right.trans le_sup_left)) le_sup_right
  have hYsol : Group.IsSolvable ↥Y := Thm211.isSolvable_of_le hYD h.solvable_cen
  have hstrict : X₂ ⊔ Y < X₁ ⊔ Y := by
    refine lt_of_le_of_ne (sup_le_sup_right hX₂X₁ Y) fun heq => hns ?_
    have hX₁le : X₁ ≤ X₂ ⊔ Y := (le_sup_left : X₁ ≤ X₁ ⊔ Y).trans heq.symm.le
    have hn : X₁ ≤ AChief.nrm X₂ := hX₁n₂
    rw [isSolvableSection_iff hn]
    have hYnrm : Y ≤ AChief.nrm X₂ := hYn₂
    have hqle : AChief.qimg X₂ X₁ ≤ AChief.qimg X₂ Y := by
      have h1 : AChief.qimg X₂ X₁ ≤ AChief.qimg X₂ (X₂ ⊔ Y) := SolQuot.qimg_mono hX₁le
      rwa [SolQuot.qimg_sup Subgroup.le_normalizer hYnrm, SolQuot.qimg_self, bot_sup_eq] at h1
    have : Group.IsSolvable ↥(AChief.qimg X₂ Y) :=
      Group.isSolvable_of_surjective (SolQuot.qres_surjective hYnrm)
    exact Thm211.isSolvable_of_le hqle this
  have hchief : IsChiefFactorOf (X₁ ⊔ Y ⊔ D ⊔ A) (X₁ ⊔ Y) (X₂ ⊔ Y) := by
    refine ⟨⟨(sup_le (hX₂X₁.trans hX₁H') hYH'), hH'N₂⟩,
      ⟨sup_le hX₁H' hYH', hH'N₁⟩, hstrict, ?_⟩
    intro L hL hlow hup
    have hLH : X₁ ⊔ D ⊔ A ≤ Subgroup.normalizer (L : Set Γ) := hHH'.trans hL.2
    have hL₁ : IsNormalIn (L ⊓ X₁) (X₁ ⊔ D ⊔ A) :=
      ⟨inf_le_right.trans hX₁H, Thm32.le_normalizer_inf hLH hc.2.1.2⟩
    have hX₂L : X₂ ≤ L ⊓ X₁ := le_inf (le_sup_left.trans hlow) hX₂X₁
    have hYL : Y ≤ L := le_sup_right.trans hlow
    have hLeq : L = (L ⊓ X₁) ⊔ Y := by
      refine le_antisymm (fun l hl => ?_) (sup_le inf_le_left hYL)
      obtain ⟨x, hx, y, hy, rfl⟩ := (Thm32.mem_sup_iff_mul hYn₁).mp (hup hl)
      have hxL : x ∈ L := by
        have := mul_mem hl (inv_mem (hYL hy))
        simpa using this
      exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hxL, hx⟩) hy
    rcases hc.2.2.2 (L ⊓ X₁) hL₁ hX₂L inf_le_right with h0 | h0
    · left
      rw [hLeq, h0]
    · right
      rw [hLeq, h0]
  have hDAIn₁ : IsDAIn A W (X₁ ⊔ Y) := ⟨sup_le hX₁.1 (hYD.trans hDW), Admits.sup hX₁.2 hYadm⟩
  have hDAIn₂ : IsDAIn A W (X₂ ⊔ Y) := ⟨sup_le hX₂.1 (hYD.trans hDW), Admits.sup hX₂.2 hYadm⟩
  have hcop : Nat.Coprime p (Nat.card ↥X₁) :=
    h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le hX₁.1)
  have hXD : X₁ ⊓ Subgroup.centralizer (A : Set Γ) ≤ D := fun x hx =>
    Subgroup.mem_inf.mpr ⟨hX₁.1 hx.1, hx.2⟩
  have hsecCen : secCenIn (X₁ ⊔ Y ⊔ D) (X₁ ⊔ Y) (X₂ ⊔ Y) = X₂ ⊔ Y := by
    refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
    · obtain ⟨hgXD, hgsc⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨-, -, hgcomm⟩ := mem_sectionCentralizer_iff.mp hgsc
      have hgXD' : g ∈ X₁ ⊔ D :=
        (sup_le (sup_le le_sup_left (hYD.trans le_sup_right)) le_sup_right : X₁ ⊔ Y ⊔ D ≤ X₁ ⊔ D)
          hgXD
      have hgn₂ : g ∈ Subgroup.normalizer (X₂ : Set Γ) :=
        (le_sup_left.trans hc.1.2) hgXD'
      have hgn₁ : g ∈ Subgroup.normalizer (X₁ : Set Γ) :=
        (le_sup_left.trans hc.2.1.2) hgXD'
      have hgsec : g ∈ secCenIn (X₁ ⊔ D) X₁ X₂ := by
        refine Subgroup.mem_inf.mpr ⟨hgXD', mem_sectionCentralizer_iff.mpr
          ⟨hgn₂, hgn₁, fun x hx => ?_⟩⟩
        have h1 : ⁅g, x⁆ ∈ X₂ ⊔ Y := hgcomm x (Subgroup.mem_sup_left hx)
        have h2 : ⁅g, x⁆ ∈ X₁ := by
          have := (Subgroup.mem_normalizer_iff.mp hgn₁ x).mp hx
          exact mul_mem this (inv_mem hx)
        obtain ⟨r, hr, y, hy, hry⟩ := (Thm32.mem_sup_iff_mul hYn₂).mp h1
        have hy1 : y ∈ X₁ := by
          have : y = r⁻¹ * ⁅g, x⁆ := by rw [hry]; group
          rw [this]
          exact mul_mem (inv_mem (hX₂X₁ hr)) h2
        have hy2 : y ∈ X₂ := mem_of_forall_commutator_mem hc hns hy1 (hYc y hy)
        rw [hry]
        exact mul_mem hr hy2
      have := secCenIn_sup_le h.prime h.elemAbelian hDA hXD hcop hc hns hgsec
      rwa [hsec] at this
    · have hgX : g ∈ X₁ ⊔ Y := (sup_le_sup_right hX₂X₁ Y) hg
      refine Subgroup.mem_inf.mpr ⟨(le_sup_left : X₁ ⊔ Y ≤ X₁ ⊔ Y ⊔ D) hgX,
        mem_sectionCentralizer_iff.mpr ⟨Subgroup.le_normalizer hg,
          Subgroup.le_normalizer hgX, fun y' hy' => ?_⟩⟩
      have hy'H : y' ∈ Subgroup.normalizer ((X₂ ⊔ Y : Subgroup Γ) : Set Γ) :=
        hH'N₂ (hXYH' hy')
      have h1 := (Subgroup.mem_normalizer_iff.mp hy'H g⁻¹).mp (inv_mem hg)
      have e : ⁅g, y'⁆ = g * (y' * g⁻¹ * y'⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hg (by simpa using h1)
  have hinf : (X₂ ⊔ Y) ⊓ D = Y := by
    refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hYD)
    obtain ⟨hxS, hxD⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨r, hr, y, hy, rfl⟩ := (Thm32.mem_sup_iff_mul hYn₂).mp hxS
    have hrD : r ∈ D := by
      have := mul_mem hxD (inv_mem (hYD hy))
      simpa using this
    exact mul_mem (hX₂Y (Subgroup.mem_inf.mpr ⟨hr, hrD⟩)) hy
  exact ⟨⟨hDAIn₁, hDAIn₂, hchief, hsecCen⟩, hinf⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm36

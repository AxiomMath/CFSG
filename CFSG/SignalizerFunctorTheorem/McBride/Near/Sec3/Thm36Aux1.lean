module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Invariance

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm36

variable {Γ : Type u} [Group Γ]

theorem isSolvableSection_iff {X₁ X₂ : Subgroup Γ} (hX₁ : X₁ ≤ AChief.nrm X₂) :
    IsSolvableSection X₁ X₂ ↔ Group.IsSolvable ↥(AChief.qimg X₂ X₁) := by
  rw [Group.isSolvable_def]
  unfold IsSolvableSection
  refine exists_congr fun n => ?_
  rw [← map_derivedSeries_eq (SolQuot.qres_surjective hX₁) n, Subgroup.map_eq_bot_iff,
    SolQuot.ker_qres hX₁]

theorem exists_mul_of_mem_sup_cen {p : ℕ} {A M N : Subgroup Γ} (hp : p.Prime)
    (hA : IsElemAbelian p A) (hAM : A ≤ Subgroup.normalizer (M : Set Γ))
    (hAN : A ≤ AChief.nrm N) (hMN : M ≤ AChief.nrm N) (hcop : Nat.Coprime p (Nat.card ↥M))
    {x : Γ} (hx : x ∈ M ⊔ N) (hxA : x ∈ Subgroup.centralizer (A : Set Γ)) :
    ∃ m ∈ cenIn M (A : Set Γ), ∃ n ∈ cenIn N (A : Set Γ), x = m * n := by
  have hxN : x ∈ AChief.nrm N := (sup_le hMN Subgroup.le_normalizer) hx
  have hx1 : AChief.qmap N ⟨x, hxN⟩ ∈ AChief.qimg N (M ⊔ N) :=
    (AChief.mem_qimg_iff N _ _).mpr ⟨⟨x, hxN⟩, hx, rfl⟩
  rw [SolQuot.qimg_sup hMN Subgroup.le_normalizer, SolQuot.qimg_self, sup_bot_eq] at hx1
  have hx2 : AChief.qmap N ⟨x, hxN⟩ ∈ Subgroup.centralizer
      ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨a, ha, rfl⟩ := (AChief.mem_qimg_iff N A z).mp hz
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (Subgroup.mem_centralizer_iff.mp hxA _ ha))
  have himg := AChief.qimg_inf_centralizer (N := N) hp hA hAM hAN hMN hcop
  have hx3 : AChief.qmap N ⟨x, hxN⟩ ∈
      AChief.qimg N (M ⊓ Subgroup.centralizer (A : Set Γ)) := by
    rw [himg]
    exact ⟨hx1, hx2⟩
  obtain ⟨y, hy, hyx⟩ := (AChief.mem_qimg_iff N _ _).mp hx3
  obtain ⟨r, hr, hxr⟩ := Thm211.exists_mem_of_qmap_eq hyx
  have hxr' : x = (y : Γ) * r := hxr
  refine ⟨(y : Γ), hy, r, ⟨hr, ?_⟩, hxr'.symm ▸ rfl⟩
  have : r = (y : Γ)⁻¹ * x := by rw [hxr']; group
  rw [this]
  exact (Subgroup.centralizer (A : Set Γ)).mul_mem
    ((Subgroup.centralizer (A : Set Γ)).inv_mem (Subgroup.mem_inf.mp hy).2) hxA

theorem admits_sectionCentralizer {Q X Y : Subgroup Γ} (hX : Admits Q X) (hY : Admits Q Y) :
    Admits Q (sectionCentralizer X Y) := by
  have key : ∀ q ∈ Q, ∀ g ∈ sectionCentralizer X Y, q * g * q⁻¹ ∈ sectionCentralizer X Y := by
    intro q hq g hg
    obtain ⟨hgX, hgY, hgc⟩ := mem_sectionCentralizer_iff.mp hg
    refine mem_sectionCentralizer_iff.mpr ⟨mul_mem (mul_mem (hX hq) hgX) (inv_mem (hX hq)),
      mul_mem (mul_mem (hY hq) hgY) (inv_mem (hY hq)), fun y hy => ?_⟩
    have hy' : q⁻¹ * y * q ∈ Y := (Subgroup.mem_normalizer_iff''.mp (hY hq) y).mp hy
    have h1 := hgc _ hy'
    have h2 : q * ⁅g, q⁻¹ * y * q⁆ * q⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hX hq) _).mp h1
    have e : ⁅q * g * q⁻¹, y⁆ = q * ⁅g, q⁻¹ * y * q⁆ * q⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h2
  intro q hq
  exact Thm211.mem_normalizer_of_forall (fun g hg => key q hq g hg)
    (fun g hg => by simpa using key q⁻¹ (inv_mem hq) g hg)

theorem admits_secCenIn {Q D X₁ X₂ : Subgroup Γ} (hD : Admits Q D) (hX₁ : Admits Q X₁)
    (hX₂ : Admits Q X₂) : Admits Q (secCenIn D X₁ X₂) :=
  Admits.inf hD (admits_sectionCentralizer hX₂ hX₁)

theorem commutator_mem_mul_right {X₂ : Subgroup Γ} {g y x : Γ}
    (hg : g ∈ Subgroup.normalizer (X₂ : Set Γ)) (hy : y ∈ Subgroup.normalizer (X₂ : Set Γ))
    (hx : x ∈ X₂) (hgy : ⁅g, y⁆ ∈ X₂) : ⁅g, y * x⁆ ∈ X₂ := by
  have h1 : ⁅g, x⁆ ∈ X₂ := mul_mem ((Subgroup.mem_normalizer_iff.mp hg x).mp hx) (inv_mem hx)
  have h2 : y * ⁅g, x⁆ * y⁻¹ ∈ X₂ := (Subgroup.mem_normalizer_iff.mp hy _).mp h1
  have e : ⁅g, y * x⁆ = ⁅g, y⁆ * (y * ⁅g, x⁆ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem hgy h2

theorem isChiefFactorOf_subpair {D A X₁ X₂ X₁' : Subgroup Γ}
    (hc : IsChiefFactorOf (X₁ ⊔ D ⊔ A) X₁ X₂) (h1 : X₁' ≤ X₁) (hadm : Admits (D ⊔ A) X₁')
    (hsup : X₁' ⊔ X₂ = X₁) : IsChiefFactorOf (X₁' ⊔ D ⊔ A) X₁' (X₁' ⊓ X₂) := by
  have hH : X₁' ⊔ D ⊔ A ≤ X₁ ⊔ D ⊔ A := sup_le_sup_right (sup_le_sup_right h1 D) A
  have hn₂ : X₁' ⊔ D ⊔ A ≤ Subgroup.normalizer (X₂ : Set Γ) := hH.trans hc.1.2
  have hn₁ : X₁' ⊔ D ⊔ A ≤ Subgroup.normalizer (X₁' : Set Γ) :=
    sup_le (sup_le Subgroup.le_normalizer (le_sup_left.trans hadm)) (le_sup_right.trans hadm)
  have hDA : D ⊔ A ≤ X₁ ⊔ D ⊔ A := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hX₁'H : X₁' ≤ X₁' ⊔ D ⊔ A := le_sup_left.trans le_sup_left
  have hinf : X₁' ⊓ X₂ ≤ X₁' ⊔ D ⊔ A := inf_le_left.trans hX₁'H
  have hnor : X₁' ⊔ D ⊔ A ≤ Subgroup.normalizer ((X₁' ⊓ X₂ : Subgroup Γ) : Set Γ) :=
    Thm32.le_normalizer_inf hn₁ hn₂
  have hlt : X₁' ⊓ X₂ < X₁' := by
    refine lt_of_le_of_ne inf_le_left fun heq => hc.2.2.1.not_ge ?_
    rw [← hsup]
    exact sup_le (heq.ge.trans inf_le_right) le_rfl
  refine ⟨⟨hinf, hnor⟩, ⟨hX₁'H, hn₁⟩, hlt, ?_⟩
  intro L hL hlow hup
  have hLn₂ : L ≤ Subgroup.normalizer (X₂ : Set Γ) := hL.1.trans hn₂
  have hLH : X₁' ⊔ D ⊔ A ≤ Subgroup.normalizer (L : Set Γ) := hL.2
  have hX₁'nL : X₁' ≤ Subgroup.normalizer (L : Set Γ) := hX₁'H.trans hLH
  have hDAnL : D ⊔ A ≤ Subgroup.normalizer (L : Set Γ) :=
    (sup_le (le_sup_right.trans le_sup_left) le_sup_right).trans hLH
  have hX₁X₁H : X₁ ≤ X₁ ⊔ D ⊔ A := le_sup_left.trans le_sup_left
  have hX₁'n₂ : X₁' ≤ Subgroup.normalizer (X₂ : Set Γ) := h1.trans (hX₁X₁H.trans hc.1.2)
  have hDAn₂ : D ⊔ A ≤ Subgroup.normalizer (X₂ : Set Γ) := hDA.trans hc.1.2
  have hX₁M : X₁ ≤ Subgroup.normalizer ((L ⊔ X₂ : Subgroup Γ) : Set Γ) := by
    rw [← hsup]
    exact sup_le (Thm32.le_normalizer_sup hX₁'nL hX₁'n₂)
      (le_sup_right.trans Subgroup.le_normalizer)
  have hDAM : D ⊔ A ≤ Subgroup.normalizer ((L ⊔ X₂ : Subgroup Γ) : Set Γ) :=
    Thm32.le_normalizer_sup hDAnL hDAn₂
  have hX₂X₁ : X₂ ≤ X₁ := hc.2.2.1.le
  have hMle : L ⊔ X₂ ≤ X₁ ⊔ D ⊔ A :=
    sup_le ((hup.trans h1).trans hX₁X₁H) (hX₂X₁.trans hX₁X₁H)
  have hMX₁ : L ⊔ X₂ ≤ X₁ := sup_le (hup.trans h1) hX₂X₁
  have hMnor : X₁ ⊔ D ⊔ A ≤ Subgroup.normalizer ((L ⊔ X₂ : Subgroup Γ) : Set Γ) :=
    sup_le (sup_le hX₁M (le_sup_left.trans hDAM)) (le_sup_right.trans hDAM)
  rcases hc.2.2.2 (L ⊔ X₂) ⟨hMle, hMnor⟩ le_sup_right hMX₁ with h0 | h0
  · left
    have hLX₂ : L ≤ X₂ := le_sup_left.trans h0.le
    exact le_antisymm (le_inf hup hLX₂) hlow
  · right
    refine le_antisymm hup (Thm32.le_of_le_sup_of_inf_le hup hLn₂ hlow ?_)
    calc X₁' ≤ X₁ := h1
      _ = L ⊔ X₂ := h0.symm

theorem secCenIn_subpair {D X₁ X₂ X₁' : Subgroup Γ} (hD₁ : Admits D X₁) (hD₂ : Admits D X₂)
    (hD₁' : Admits D X₁') (hX₁₂ : Admits X₁ X₂) (h1 : X₁' ≤ X₁) (hsup : X₁' ⊔ X₂ = X₁) :
    secCenIn D X₁' (X₁' ⊓ X₂) = secCenIn D X₁ X₂ := by
  ext d
  simp only [secCenIn, Subgroup.mem_inf, mem_sectionCentralizer_iff]
  constructor
  · rintro ⟨hdD, -, -, hcomm⟩
    refine ⟨hdD, hD₂ hdD, hD₁ hdD, fun y hy => ?_⟩
    rw [← hsup] at hy
    obtain ⟨y', hy', x, hx, rfl⟩ := (Thm32.mem_sup_iff_mul' (h1.trans hX₁₂)).mp hy
    exact commutator_mem_mul_right (hD₂ hdD) (hX₁₂ (h1 hy')) hx (hcomm y' hy').2
  · rintro ⟨hdD, -, -, hcomm⟩
    refine ⟨hdD, Admits.inf hD₁' hD₂ hdD, hD₁' hdD, fun y hy => ⟨?_, hcomm y (h1 hy)⟩⟩
    have h2 : d * y * d⁻¹ ∈ X₁' := (Subgroup.mem_normalizer_iff.mp (hD₁' hdD) y).mp hy
    exact mul_mem h2 (inv_mem hy)

theorem isSolvableSection_of_subpair {X₁ X₂ X₁' : Subgroup Γ} (hX₁₂ : Admits X₁ X₂)
    (h1 : X₁' ≤ X₁) (hsup : X₁' ⊔ X₂ = X₁) (h : IsSolvableSection X₁' (X₁' ⊓ X₂)) :
    IsSolvableSection X₁ X₂ := by
  have hn₁' : X₁' ≤ AChief.nrm X₂ := h1.trans hX₁₂
  have hn₁ : X₁ ≤ AChief.nrm X₂ := hX₁₂
  rw [isSolvableSection_iff hn₁]
  have hq : AChief.qimg X₂ X₁ = AChief.qimg X₂ X₁' := by
    rw [← hsup, SolQuot.qimg_sup hn₁' Subgroup.le_normalizer, SolQuot.qimg_self, sup_bot_eq]
  rw [hq, ← isSolvableSection_iff hn₁']
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn.trans (Subgroup.subgroupOf_mono X₁' inf_le_right)⟩

theorem mem_of_forall_commutator_mem {D A X₁ X₂ : Subgroup Γ}
    (hc : IsChiefFactorOf (X₁ ⊔ D ⊔ A) X₁ X₂) (hns : ¬ IsSolvableSection X₁ X₂) {x : Γ}
    (hx : x ∈ X₁) (hcomm : ∀ y ∈ X₁, ⁅x, y⁆ ∈ X₂) : x ∈ X₂ := by
  set S : Subgroup Γ := X₁ ⊓ sectionCentralizer X₂ X₁ with hS
  have hn₂ : X₁ ⊔ D ⊔ A ≤ Subgroup.normalizer (X₂ : Set Γ) := hc.1.2
  have hn₁ : X₁ ⊔ D ⊔ A ≤ Subgroup.normalizer (X₁ : Set Γ) := hc.2.1.2
  have hX₁H : X₁ ≤ X₁ ⊔ D ⊔ A := le_sup_left.trans le_sup_left
  have hX₂X₁ : X₂ ≤ X₁ := hc.2.2.1.le
  have hSnor : X₁ ⊔ D ⊔ A ≤ Subgroup.normalizer (S : Set Γ) :=
    Thm32.le_normalizer_inf hn₁ (admits_sectionCentralizer hn₂ hn₁)
  have hX₂S : X₂ ≤ S := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hX₂X₁ hz, mem_sectionCentralizer_iff.mpr
      ⟨Subgroup.le_normalizer hz, Subgroup.le_normalizer (hX₂X₁ hz), fun y hy => ?_⟩⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hn₂ (hX₁H hy)) z⁻¹).mp (inv_mem hz)
    have e : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hz (by simpa using h1)
  have hSle : S ≤ X₁ ⊔ D ⊔ A := inf_le_left.trans hX₁H
  rcases hc.2.2.2 S ⟨hSle, hSnor⟩ hX₂S inf_le_left with h | h
  · have hxS : x ∈ S := Subgroup.mem_inf.mpr ⟨hx, mem_sectionCentralizer_iff.mpr
      ⟨hn₂ (hX₁H hx), hn₁ (hX₁H hx), hcomm⟩⟩
    rw [h] at hxS
    exact hxS
  · exfalso
    apply hns
    refine ⟨1, ?_⟩
    rw [derivedSeries_one]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [Subgroup.mem_subgroupOf]
    have ha : (a : Γ) ∈ S := by
      rw [h]
      exact a.2
    exact (mem_sectionCentralizer_iff.mp (Subgroup.mem_inf.mp ha).2).2.2 b b.2

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm36

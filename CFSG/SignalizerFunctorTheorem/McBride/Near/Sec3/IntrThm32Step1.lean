module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm211
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Aux

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm32

variable {Γ : Type*} [Group Γ] {p : ℕ} {A X Y X₁ X₂ : Subgroup Γ}

theorem commutator_mem_mul {g n z : Γ} (hg : g ∈ Subgroup.normalizer (X₂ : Set Γ)) (hn : n ∈ X₂)
    (hgz : ⁅g, z⁆ ∈ X₂) : ⁅g, n * z⁆ ∈ X₂ := by
  have h1 : g * n * g⁻¹ * n⁻¹ ∈ X₂ :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hg n).mp hn) (inv_mem hn)
  have h2 : n * ⁅g, z⁆ * n⁻¹ ∈ X₂ := mul_mem (mul_mem hn hgz) (inv_mem hn)
  have h3 := mul_mem h1 h2
  convert h3 using 1
  simp only [commutatorElement_def]
  group

theorem exists_solvable_of_pair
    [Finite Γ] (h : NearAsolvAction p A X)
    (hP : (X₁, X₂) ∈ iPairsY A X Y) :
    ∃ Z₁ Z₂ : Subgroup Γ, Z₁ ≤ X₁ ∧ Z₂ ≤ X₂ ∧ (Z₁, Z₂) ∈ iPairsY A X Y ∧
      Group.IsSolvable ↥Z₂ := by
  have hch := chief_of_mem_iPairsY hP
  have hsec := secCen_of_mem_iPairsY hP
  have hinf := inf_eq_of_mem_iPairsY hP
  have hX₁ := isDAIn_left_of_mem_iPairsY hP
  have hX₂ := isDAIn_right_of_mem_iPairsY hP
  set D := cenIn X (A : Set Γ) with hD
  have hDX : D ≤ X := inf_le_left
  have hDA : D ≤ Subgroup.centralizer (A : Set Γ) := inf_le_right
  have hDs : Group.IsSolvable ↥D := h.solvable_cen
  have hGX : X₁ ⊔ D ≤ X := sup_le hX₁.1 hDX
  have hX₂X₁ : X₂ ≤ X₁ := hch.2.2.1.le
  have hX₂X : X₂ ≤ X := hX₂.1
  have hAnorX₁ : A ≤ Subgroup.normalizer (X₁ : Set Γ) := le_sup_right.trans hX₁.2
  have hAcenD : A ≤ Subgroup.centralizer (D : Set Γ) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun d hd =>
      (Subgroup.mem_centralizer_iff.mp (hDA hd) a ha).symm
  have hAnorD : A ≤ Subgroup.normalizer (D : Set Γ) :=
    hAcenD.trans (Subgroup.centralizer_le_normalizer _)
  have hG : NearAsolvAction p A (X₁ ⊔ D) :=
    Thm211.nearAsolvAction_of_le h hGX (le_normalizer_sup hAnorX₁ hAnorD)
  have hcenG : cenIn (X₁ ⊔ D) (A : Set Γ) = D :=
    le_antisymm (inf_le_inf_right _ hGX) (le_inf le_sup_right hDA)
  have hX₂G : X₂ ≤ X₁ ⊔ D := hX₂X₁.trans le_sup_left
  have hX₂adm : Admits (cenIn (X₁ ⊔ D) (A : Set Γ) ⊔ A) X₂ := by
    rw [hcenG]
    exact hX₂.2
  have hb := thm211b hG hX₂G hX₂adm
  have hd := thm211d hG hX₂G hX₂adm
  have hc := thm211c_mul hG hX₂G hch.1
  rw [hcenG] at hb hd hc
  set T := scalJoin X₂ A D with hT
  have hTX₂ : T ≤ X₂ := Thm211.scalJoin_le_left X₂ A D
  have hTs : Group.IsSolvable ↥T := hb.2
  have hDAT : D ⊔ A ≤ Subgroup.normalizer (T : Set Γ) :=
    Thm211.sup_le_normalizer_scalJoin hDA (le_sup_left.trans hX₂.2) (le_sup_right.trans hX₂.2)
  have hYT : X₂ ⊓ D ≤ T := Thm211.inf_le_scalJoin hDA (Thm211.isSolvable_of_le inf_le_right hDs)
  have hTD : T ⊓ D = Y :=
    le_antisymm ((inf_le_inf_right D hTX₂).trans hinf.le)
      (le_inf (hinf.ge.trans hYT) (hinf.ge.trans inf_le_right))
  set Z₁ : Subgroup Γ := X₁ ⊓ Subgroup.normalizer (T : Set Γ) with hZ₁
  have hZ₁X₁ : Z₁ ≤ X₁ := inf_le_left
  have hTZ₁ : T ≤ Z₁ := le_inf (hTX₂.trans hX₂X₁) Subgroup.le_normalizer
  have hZ₁nor : Z₁ ≤ Subgroup.normalizer (T : Set Γ) := inf_le_right
  have hZ₁X₂ : Z₁ ⊓ X₂ = T := by
    refine le_antisymm (fun x hx => ?_) (le_inf hTZ₁ hTX₂)
    have h1 : x ∈ norIn X₂ (T : Set Γ) := Subgroup.mem_inf.mpr ⟨hx.2, hx.1.2⟩
    rwa [hd] at h1
  have hdec : ∀ x ∈ X₁, ∃ n ∈ X₂, ∃ z ∈ Z₁, x = n * z := by
    intro x hx
    have hxG : x ∈ ((X₁ ⊔ D : Subgroup Γ) : Set Γ) := (le_sup_left : X₁ ≤ X₁ ⊔ D) hx
    rw [← hc] at hxG
    obtain ⟨n, hn, g, hg, rfl⟩ := hxG
    refine ⟨n, hn, g, Subgroup.mem_inf.mpr ⟨?_, (Subgroup.mem_inf.mp hg).2⟩, rfl⟩
    have : g = n⁻¹ * (n * g) := by group
    rw [this]
    exact mul_mem (inv_mem (hX₂X₁ hn)) hx
  have hZ₁adm : Admits (D ⊔ A) Z₁ := le_normalizer_inf hX₁.2 (hDAT.trans Subgroup.le_normalizer)
  have hE₁ : Z₁ ⊔ D ⊔ A ≤ Subgroup.normalizer (T : Set Γ) :=
    sup_le (sup_le hZ₁nor (le_sup_left.trans hDAT)) (le_sup_right.trans hDAT)
  have hE₁' : Z₁ ⊔ D ⊔ A ≤ Subgroup.normalizer (Z₁ : Set Γ) :=
    sup_le (sup_le Subgroup.le_normalizer (le_sup_left.trans hZ₁adm)) (le_sup_right.trans hZ₁adm)
  have hE₁X : Z₁ ⊔ D ⊔ A ≤ X₁ ⊔ D ⊔ A := sup_le_sup_right (sup_le_sup_right hZ₁X₁ D) A
  have hlt : T < Z₁ := lt_of_le_of_ne hTZ₁ fun heq => by
    refine hch.2.2.1.not_ge fun x hx => ?_
    obtain ⟨n, hn, z, hz, rfl⟩ := hdec x hx
    have hzT : z ∈ T := by
      rw [heq]
      exact hz
    exact mul_mem hn (hTX₂ hzT)
  have hmin : ∀ L : Subgroup Γ, IsNormalIn L (Z₁ ⊔ D ⊔ A) → T ≤ L → L ≤ Z₁ →
      L = T ∨ L = Z₁ := by
    intro L hL hTL hLZ₁
    have hLn₂ : L ≤ Subgroup.normalizer (X₂ : Set Γ) :=
      hLZ₁.trans (hZ₁X₁.trans (le_sup_left.trans (le_sup_left.trans hch.1.2)))
    have hEn₂ : Z₁ ⊔ D ⊔ A ≤ Subgroup.normalizer (X₂ : Set Γ) := hE₁X.trans hch.1.2
    have hMn : Z₁ ⊔ D ⊔ A ≤ Subgroup.normalizer ((X₂ ⊔ L : Subgroup Γ) : Set Γ) :=
      le_normalizer_sup hEn₂ hL.2
    have hX₂M : X₂ ≤ Subgroup.normalizer ((X₂ ⊔ L : Subgroup Γ) : Set Γ) :=
      le_sup_left.trans Subgroup.le_normalizer
    have hX₁M : X₁ ≤ Subgroup.normalizer ((X₂ ⊔ L : Subgroup Γ) : Set Γ) := by
      intro x hx
      obtain ⟨n, hn, z, hz, rfl⟩ := hdec x hx
      exact mul_mem (hX₂M hn) ((le_sup_left.trans (le_sup_left.trans hMn)) hz)
    have hMnE : X₁ ⊔ D ⊔ A ≤ Subgroup.normalizer ((X₂ ⊔ L : Subgroup Γ) : Set Γ) :=
      sup_le (sup_le hX₁M ((le_sup_right.trans le_sup_left).trans hMn)) (le_sup_right.trans hMn)
    have hMle : X₂ ⊔ L ≤ X₁ ⊔ D ⊔ A :=
      sup_le (hX₂X₁.trans (le_sup_left.trans le_sup_left)) (hL.1.trans hE₁X)
    have hMX₁ : X₂ ⊔ L ≤ X₁ := sup_le hX₂X₁ (hLZ₁.trans hZ₁X₁)
    rcases hch.2.2.2 (X₂ ⊔ L) ⟨hMle, hMnE⟩ le_sup_left hMX₁ with h0 | h0
    · left
      have hLX₂ : L ≤ X₂ := le_sup_right.trans h0.le
      refine le_antisymm ?_ hTL
      rw [← hZ₁X₂]
      exact le_inf hLZ₁ hLX₂
    · right
      refine le_antisymm hLZ₁ (le_of_le_sup_of_inf_le hLZ₁ hLn₂ (hZ₁X₂.le.trans hTL) ?_)
      calc Z₁ ≤ X₁ := hZ₁X₁
        _ = X₂ ⊔ L := h0.symm
        _ = L ⊔ X₂ := sup_comm _ _
  have hsecZ : secCenIn (Z₁ ⊔ D) Z₁ T = T := by
    refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
    · obtain ⟨hgZD, hgsc⟩ := Subgroup.mem_inf.mp hg
      have hgcomm := (mem_sectionCentralizer_iff.mp hgsc).2.2
      have hgG : g ∈ X₁ ⊔ D := (sup_le_sup_right hZ₁X₁ D) hgZD
      have hgn₂ : g ∈ Subgroup.normalizer (X₂ : Set Γ) := (le_sup_left.trans hch.1.2) hgG
      have hgn₁ : g ∈ Subgroup.normalizer (X₁ : Set Γ) := (le_sup_left.trans hch.2.1.2) hgG
      have hgsec : g ∈ secCenIn (X₁ ⊔ D) X₁ X₂ := by
        refine Subgroup.mem_inf.mpr ⟨hgG, mem_sectionCentralizer_iff.mpr
          ⟨hgn₂, hgn₁, fun y hy => ?_⟩⟩
        obtain ⟨n, hn, z, hz, rfl⟩ := hdec y hy
        exact commutator_mem_mul hgn₂ hn (hTX₂ (hgcomm z hz))
      rw [hsec] at hgsec
      have hgnT : g ∈ Subgroup.normalizer (T : Set Γ) :=
        (sup_le hZ₁nor (le_sup_left.trans hDAT)) hgZD
      have h1 : g ∈ norIn X₂ (T : Set Γ) := Subgroup.mem_inf.mpr ⟨hgsec, hgnT⟩
      rwa [hd] at h1
    · refine Subgroup.mem_inf.mpr ⟨(hTZ₁.trans le_sup_left) hg, ?_⟩
      refine mem_sectionCentralizer_iff.mpr ⟨Subgroup.le_normalizer hg,
        Subgroup.le_normalizer (hTZ₁ hg), fun y hy => ?_⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (hZ₁nor hy) g⁻¹).mp (inv_mem hg)
      have h2 := mul_mem hg h1
      simpa [commutatorElement_def, mul_assoc] using h2
  exact ⟨Z₁, T, hZ₁X₁, hTX₂, mem_iPairsY_of ⟨hZ₁X₁.trans hX₁.1, hZ₁adm⟩
    ⟨hTX₂.trans hX₂X, hDAT⟩
    ⟨⟨hTZ₁.trans (le_sup_left.trans le_sup_left), hE₁⟩,
      ⟨le_sup_left.trans le_sup_left, hE₁'⟩, hlt, hmin⟩ hsecZ hTD, hTs⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm32

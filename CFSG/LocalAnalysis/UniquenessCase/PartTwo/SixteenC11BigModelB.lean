module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigModelA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigModelBA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigSym
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigCombB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MJoin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c11_big_le_of_mem_aSet {n : ℕ} {X L K L₀ : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (h : S16C11AltSetup n X L K L₀ J₀ J₁) {E : Subgroup (MulAut W)} (hE : E ∈ E3.aSet 2 X) :
    E ≤ L₀ := by
  classical
  obtain ⟨s⟩ := h.ksym
  set Y : Subgroup (MulAut W) :=
    ((alternatingGroup (Fin 3)).comap s.toMonoidHom).map K.subtype with hYdef
  have hYcard : Nat.card Y = 3 := by
    rw [hYdef]
    exact s16c11_big_modelb_three_card s
  have hYodd : ¬ 2 ∣ Nat.card Y := by
    rw [hYcard]
    norm_num
  have hYleK : Y ≤ K := by
    rw [hYdef]
    exact Subgroup.map_subtype_le _
  have hKnorm : K ≤ Subgroup.normalizer (Y : Set (MulAut W)) := by
    rw [hYdef]
    exact s16c11_big_modelb_map_subtype_normalizer K _
      (alternatingGroup.normal.comap s.toMonoidHom)
  have hLcent : L₀ ≤ Subgroup.centralizer (Y : Set (MulAut W)) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact s16c11_comm_of_isInternalDirect h.dir y (hYleK hy) l hl
  have hAY : E ≤ Subgroup.normalizer (Y : Set (MulAut W)) := by
    have hsup : K ⊔ L₀ ≤ Subgroup.normalizer (Y : Set (MulAut W)) :=
      sup_le hKnorm (hLcent.trans (Subgroup.centralizer_le_normalizer _))
    rw [h.dir.2.2] at hsup
    exact hE.1.trans hsup
  have hEcent : E ≤ Subgroup.centralizer (Y : Set (MulAut W)) :=
    s16c11_le_centralizer_of_mem_aSet_two h.cfg.sq hE hYodd hAY
  intro x hx
  have hxX : x ∈ K ⊔ L₀ := by
    rw [h.dir.2.2]
    exact hE.1 hx
  obtain ⟨κ, hκ, ℓ, hℓ, hκℓ⟩ :=
    s16c2m_exists_mul_of_mem_sup (s16c11_comm_of_isInternalDirect h.dir) hxX
  have hx2 : x ^ 2 = 1 := hE.2.2.1.2 x hx
  have hκℓcomm : κ * ℓ = ℓ * κ := s16c11_comm_of_isInternalDirect h.dir κ hκ ℓ hℓ
  have hκcent : κ ∈ Subgroup.centralizer (Y : Set (MulAut W)) := by
    have hx' : x ∈ Subgroup.centralizer (Y : Set (MulAut W)) := hEcent hx
    have hl' : ℓ⁻¹ ∈ Subgroup.centralizer (Y : Set (MulAut W)) :=
      (Subgroup.centralizer (Y : Set (MulAut W))).inv_mem (hLcent hℓ)
    have hprod : x * ℓ⁻¹ ∈ Subgroup.centralizer (Y : Set (MulAut W)) :=
      (Subgroup.centralizer (Y : Set (MulAut W))).mul_mem hx' hl'
    rwa [← hκℓ, mul_inv_cancel_right] at hprod
  have hκY : κ ∈ Y := by
    rw [hYdef] at hκcent ⊢
    exact s16c11_big_modelb_three_mem_of_centralizer s hκ hκcent
  have hκ3 : κ ^ 3 = 1 := by
    rw [hYdef] at hκY
    exact s16c11_big_modelb_three_pow_three s hκ hκY
  have hκ2 : κ ^ 2 = 1 := by
    have h1 : κ ^ 2 * ℓ ^ 2 = 1 := by
      rw [← (show Commute κ ℓ from hκℓcomm).mul_pow 2, hκℓ, hx2]
    have h2 : κ ^ 2 = (ℓ ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hmemL : κ ^ 2 ∈ L₀ := by
      rw [h2]
      exact L₀.inv_mem (L₀.pow_mem hℓ 2)
    have hmem : κ ^ 2 ∈ K ⊓ L₀ := ⟨K.pow_mem hκ 2, hmemL⟩
    rwa [h.dir.2.1, Subgroup.mem_bot] at hmem
  have hκ1 : κ = 1 := by
    calc κ = κ ^ 3 * (κ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hκ3, hκ2]; simp
  rw [← hκℓ, hκ1, one_mul]
  exact hℓ

theorem s16c11_big_transfer_aSet {n : ℕ} (h5 : 5 ≤ n) (h6 : n ≠ 6)
    {X L K L₀ : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (h : S16C11AltSetup n X L K L₀ J₀ J₁) {E : Subgroup (MulAut W)} (hE : E ∈ E3.aSet 2 X) :
    ∃ E' : Subgroup (Equiv.Perm (Fin n)), IsElemAbelian 2 E' ∧ E' ≠ ⊥ ∧
      (∀ B : Subgroup (Equiv.Perm (Fin n)), B ≤ E' → B.relIndex E' ≤ 2 →
        ∀ q : (FFModel.symDn n).Mod,
          (∀ σ ∈ B, (FFModel.symDn_isActionModel n).modAct σ q = q) →
            ∀ σ ∈ E', (FFModel.symDn_isActionModel n).modAct σ q = q) ∧
      Nat.card ↥(J₀ ⊓ fixV E) = Nat.card {q : (FFModel.symDn n).Mod //
        ∀ σ ∈ E', (FFModel.symDn_isActionModel n).modAct σ q = q} := by
  classical
  obtain ⟨ρ, β, hβ⟩ := s16c11_big_realizes_equiv (FFModel.symDn_isActionModel n)
    (FFC.symDn_faithful h5) (s16c11_big_symRealizes h5 h6 h)
  have hle : E ≤ L₀ := s16c11_big_le_of_mem_aSet h hE
  let f : Equiv.Perm (Fin n) →* MulAut W := L₀.subtype.comp ρ.toMonoidHom
  let E' : Subgroup (Equiv.Perm (Fin n)) := E.comap f
  have hf : Function.Injective f := fun a b hab => ρ.injective (Subgroup.subtype_injective L₀ hab)
  have hrange : f.range = L₀ := by
    ext y
    constructor
    · rintro ⟨σ, rfl⟩
      exact (ρ σ).2
    · intro hy
      refine ⟨ρ.symm ⟨y, hy⟩, ?_⟩
      show ((ρ (ρ.symm ⟨y, hy⟩) : ↥L₀) : MulAut W) = y
      rw [MulEquiv.apply_symm_apply]
  have hE'map : E'.map f = E :=
    Subgroup.map_comap_eq_self (f := f) (H := E) (by rw [hrange]; exact hle)
  have hEab : IsElemAbelian 2 E' := by
    refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, ?_⟩
    · apply hf
      change f (a.1 * b.1) = f (b.1 * a.1)
      rw [map_mul, map_mul]
      exact hE.2.2.1.1 (f a.1) (Subgroup.mem_comap.mp a.2) (f b.1)
        (Subgroup.mem_comap.mp b.2)
    · intro x hx
      apply hf
      rw [map_pow, map_one]
      exact hE.2.2.1.2 (f x) (Subgroup.mem_comap.mp hx)
  have hE'ne : E' ≠ ⊥ := by
    intro hbot
    apply hE.2.1
    rw [← hE'map, hbot, Subgroup.map_bot]
  have hprop : ∀ B : Subgroup (Equiv.Perm (Fin n)), B ≤ E' → B.relIndex E' ≤ 2 →
      ∀ q : (FFModel.symDn n).Mod,
        (∀ σ ∈ B, (FFModel.symDn_isActionModel n).modAct σ q = q) →
          ∀ σ ∈ E', (FFModel.symDn_isActionModel n).modAct σ q = q := by
    intro B hB hrel q hq σ hσ
    have hB₁le : B.map f ≤ E := by
      rw [← hE'map]
      exact Subgroup.map_mono hB
    have hrelB : (B.map f).relIndex E = B.relIndex E' := by
      rw [← hE'map]
      exact Subgroup.relIndex_map_map_of_injective (f := f) B E' hf
    have hmq : E3.mQuot E (B.map f) < 2 := by
      unfold E3.mQuot
      rw [hrelB]
      rcases eq_or_ne (B.relIndex E') 0 with h0 | h0
      · rw [h0]
        norm_num
      · by_contra hlt
        have hle2 : 2 ≤ padicValNat 2 (B.relIndex E') := not_lt.1 hlt
        have h4 : 4 ∣ B.relIndex E' :=
          (padicValNat_dvd_iff_le (p := 2) (a := B.relIndex E') (n := 2) h0).2 hle2
        obtain ⟨k, hk⟩ := h4
        omega
    have hfix := hE.2.2.2 (B.map f) hB₁le hmq
    set u : ↥J₀ := β.symm q with hu
    have hβuq : β u = q := β.apply_symm_apply q
    have hufix : ((u : ↥J₀) : W) ∈ fixV (B.map f) := by
      rw [mem_fixV]
      intro z hz
      obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hz
      have hqτ : (FFModel.symDn_isActionModel n).modAct τ q = q := hq τ hτ
      have hβτ := hβ τ u
      rw [hβuq, hqτ, ← hu] at hβτ
      change ((ρ τ : ↥L₀) : MulAut W) (u : W) = (u : W)
      exact hβτ.symm
    have hfixσ : f σ (u : W) = (u : W) := by
      have huE : ((u : ↥J₀) : W) ∈ fixV E := by rw [← hfix]; exact hufix
      exact (mem_fixV.mp huE) (f σ) (Subgroup.mem_comap.mp hσ)
    have hsu : ((β.symm ((FFModel.symDn_isActionModel n).modAct σ (β u)) : ↥J₀) : W) =
        (u : W) := by
      have h1 : ((β.symm ((FFModel.symDn_isActionModel n).modAct σ (β u)) : ↥J₀) : W) =
          ((ρ σ : ↥L₀) : MulAut W) (u : W) := hβ σ u
      rw [h1]
      exact hfixσ
    have hsu' : β.symm ((FFModel.symDn_isActionModel n).modAct σ (β u)) = u :=
      Subtype.ext hsu
    calc (FFModel.symDn_isActionModel n).modAct σ q
        = (FFModel.symDn_isActionModel n).modAct σ (β u) := by rw [hβuq]
      _ = β (β.symm ((FFModel.symDn_isActionModel n).modAct σ (β u))) :=
          (β.apply_symm_apply _).symm
      _ = β u := by rw [hsu']
      _ = q := hβuq
  have hcard : Nat.card ↥(J₀ ⊓ fixV E) = Nat.card {q : (FFModel.symDn n).Mod //
        ∀ σ ∈ E', (FFModel.symDn_isActionModel n).modAct σ q = q} := by
    let g : ↥(J₀ ⊓ fixV E) → {q : (FFModel.symDn n).Mod //
        ∀ σ ∈ E', (FFModel.symDn_isActionModel n).modAct σ q = q} :=
      fun w => ⟨β ⟨(w : W), (Subgroup.mem_inf.mp w.2).1⟩, by
        intro σ hσ
        have hσE : f σ ∈ E := Subgroup.mem_comap.mp hσ
        have hwfix : f σ (w : W) = (w : W) :=
          (mem_fixV.mp (Subgroup.mem_inf.mp w.2).2) (f σ) hσE
        have hβσ' : ((β.symm ((FFModel.symDn_isActionModel n).modAct σ
            (β ⟨(w : W), (Subgroup.mem_inf.mp w.2).1⟩)) : ↥J₀) : W) = (w : W) :=
          (hβ σ ⟨(w : W), (Subgroup.mem_inf.mp w.2).1⟩).trans hwfix
        have hEq : β.symm ((FFModel.symDn_isActionModel n).modAct σ
            (β ⟨(w : W), (Subgroup.mem_inf.mp w.2).1⟩)) =
            ⟨(w : W), (Subgroup.mem_inf.mp w.2).1⟩ := Subtype.ext hβσ'
        calc (FFModel.symDn_isActionModel n).modAct σ
              (β ⟨(w : W), (Subgroup.mem_inf.mp w.2).1⟩)
            = β (β.symm ((FFModel.symDn_isActionModel n).modAct σ
                (β ⟨(w : W), (Subgroup.mem_inf.mp w.2).1⟩))) := (β.apply_symm_apply _).symm
          _ = β ⟨(w : W), (Subgroup.mem_inf.mp w.2).1⟩ := by rw [hEq]⟩
    have hg : Function.Bijective g := by
      refine ⟨?_, ?_⟩
      · intro w₁ w₂ h
        have hval : β ⟨(w₁ : W), (Subgroup.mem_inf.mp w₁.2).1⟩ =
            β ⟨(w₂ : W), (Subgroup.mem_inf.mp w₂.2).1⟩ := congrArg Subtype.val h
        have hJ : (⟨(w₁ : W), (Subgroup.mem_inf.mp w₁.2).1⟩ : ↥J₀) =
            ⟨(w₂ : W), (Subgroup.mem_inf.mp w₂.2).1⟩ := β.injective hval
        apply Subtype.ext
        exact congrArg (fun z : ↥J₀ => (z : W)) hJ
      · intro q
        let u : ↥J₀ := β.symm q.1
        have huFix : (u : W) ∈ fixV E := by
          rw [mem_fixV]
          intro σ hσ
          have hσmap : σ ∈ E'.map f := by rw [hE'map]; exact hσ
          obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hσmap
          have hβu : β u = q.1 := β.apply_symm_apply q.1
          have hqτ : (FFModel.symDn_isActionModel n).modAct τ q.1 = q.1 := q.2 τ hτ
          have hβτ := hβ τ u
          rw [hβu, hqτ] at hβτ
          have hsym : β.symm q.1 = u := rfl
          rw [hsym] at hβτ
          change ((ρ τ : ↥L₀) : MulAut W) (u : W) = (u : W)
          exact hβτ.symm
        refine ⟨⟨(u : W), Subgroup.mem_inf.mpr ⟨u.2, huFix⟩⟩, ?_⟩
        apply Subtype.ext
        show (β ⟨(u : W),
          (Subgroup.mem_inf.mp (Subgroup.mem_inf.mpr ⟨u.2, huFix⟩)).1⟩ :
            (FFModel.symDn n).Mod) = q.1
        have hsub : (⟨(u : W),
            (Subgroup.mem_inf.mp (Subgroup.mem_inf.mpr ⟨u.2, huFix⟩)).1⟩ : ↥J₀) = u :=
          Subtype.ext rfl
        rw [hsub]
        exact β.apply_symm_apply q.1
    exact Nat.card_congr (Equiv.ofBijective g hg)
  exact ⟨E', hEab, hE'ne, hprop, hcard⟩

theorem s16c11_big_aSet_nine {X L K L₀ : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (h : S16C11AltSetup 9 X L K L₀ J₀ J₁) {E : Subgroup (MulAut W)} (hE : E ∈ E3.aSet 2 X) :
    False := by
  obtain ⟨E', hab, hne, hB, -⟩ := s16c11_big_transfer_aSet (by norm_num) (by norm_num) h hE
  exact s16c11_big_no_a2_odd (by norm_num) hab hne hB

theorem s16c11_big_rkIdx_ten {X L K L₀ : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (h : S16C11AltSetup 10 X L K L₀ J₀ J₁) {E : Subgroup (MulAut W)} (hE : E ∈ E3.aSet 2 X) :
    rkIdx (fixV E) = 8 := by
  obtain ⟨E', hab, hne, hB, hcard⟩ := s16c11_big_transfer_aSet (by norm_num) (by norm_num) h hE
  have h16 : Nat.card ↥(J₀ ⊓ fixV E) = 16 := hcard.trans (s16c11_big_a2_ten hab hne hB)
  have h1 : Nat.card ↥(fixV E) = 2 ^ 8 := by
    rw [s16c11_big_fixV_card h (s16c11_big_le_of_mem_aSet h hE), h16]
    norm_num
  have h2: Nat.card W = 2 ^ 16 := by
    rw [s16c11_big_card_eq h, s16c11_big_card_J (Or.inr rfl) h]
    norm_num
  have h3 : (fixV E).index = 2 ^ 8 := by
    have h4 := Subgroup.card_mul_index (fixV E)
    rw [h1, h2] at h4
    have h5 : (2 : ℕ) ^ 8 * (fixV E).index = 2 ^ 8 * 2 ^ 8 := by
      rw [h4]
      norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h5
  unfold rkIdx
  rw [h3]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact padicValNat.prime_pow 8

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

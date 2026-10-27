module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCfg10Comps
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {X Fs : Subgroup (MulAut W)} {I₁ I₂ : Subgroup W}

private theorem s16c167_disjoint_sup_of_inf_eq_bot {A B J J' : Subgroup W}
    (hAB : A ⊓ B = ⊥) (hs : A ⊔ B = J) (hJ : J ⊓ J' = ⊥) : Disjoint A (B ⊔ J') := by
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxA, hxBJ⟩ := hx
  rw [Subgroup.mem_sup] at hxBJ
  obtain ⟨y, hyB, z, hzJ', hyz⟩ := hxBJ
  have hAle : A ≤ J := by rw [← hs]; exact le_sup_left
  have hBle : B ≤ J := by rw [← hs]; exact le_sup_right
  have hz_eq : z = y⁻¹ * x := by rw [← hyz]; group
  have hzJ : z ∈ J := by
    rw [hz_eq]
    exact J.mul_mem (J.inv_mem (hBle hyB)) (hAle hxA)
  have hzbot : z = 1 := by
    have hmem : z ∈ J ⊓ J' := ⟨hzJ, hzJ'⟩
    rw [hJ] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hxy : x = y := by rw [← hyz, hzbot, mul_one]
  have hxbot : x = 1 := by
    have hmem : x ∈ A ⊓ B := ⟨hxA, by rw [hxy]; exact hyB⟩
    rw [hAB] at hmem
    exact Subgroup.mem_bot.mp hmem
  simpa using hxbot

private theorem s16c167_fixV_map_conj (x : MulAut W) (R : Subgroup (MulAut W)) :
    (fixV R).map x.toMonoidHom = fixV (R.map (MulAut.conj x).toMonoidHom) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_fixV]
    intro φ hφ
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hφ
    show (x * r * x⁻¹) (x w) = x w
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, mem_fixV.mp hw r hr]
  · intro hv
    refine Subgroup.mem_map.mpr ⟨x⁻¹ v, ?_, by simp⟩
    rw [mem_fixV]
    intro r hr
    have h := mem_fixV.mp hv (x * r * x⁻¹) (Subgroup.mem_map_of_mem _ hr)
    rw [MulAut.mul_apply, MulAut.mul_apply] at h
    refine x.injective ?_
    simpa using h

private theorem s16c167_map_inf_fixV (x : MulAut W) (I : Subgroup W)
    (R : Subgroup (MulAut W)) :
    (I ⊓ fixV R).map x.toMonoidHom =
      (I.map x.toMonoidHom) ⊓ fixV (R.map (MulAut.conj x).toMonoidHom) := by
  rw [Subgroup.map_inf I (fixV R) x.toMonoidHom x.injective, s16c167_fixV_map_conj]

private theorem s16c167_ne_of_inf_eq_bot {A B : Subgroup W} (h : A ⊓ B = ⊥)
    (hrk : rk ↥A = 2) : A ≠ B := by
  intro hAB
  have hbot : A = ⊥ := by rw [← h, ← hAB, inf_idem]
  have hzero : rk ↥A = 0 := by rw [hbot]; exact rk_bot
  omega

private theorem s16c167_ne_of_le_indep {A B I J : Subgroup W} (hA : A ≤ I) (hB : B ≤ J)
    (hIJ : I ⊓ J = ⊥) (hrk : rk ↥A = 2) : A ≠ B := by
  intro hAB
  have hle : A ≤ I ⊓ J := le_inf hA (by rw [hAB]; exact hB)
  have hle' : A ≤ ⊥ := by rw [← hIJ]; exact hle
  have hbot : A = ⊥ := le_bot_iff.mp hle'
  have hzero : rk ↥A = 0 := by rw [hbot]; exact rk_bot
  omega

theorem s16c167_indep_four {A₁ B₁ A₂ B₂ J₁ J₂ : Subgroup W} (hJ : J₁ ⊓ J₂ = ⊥)
    (hs : J₁ ⊔ J₂ = ⊤) (h₁ : A₁ ⊓ B₁ = ⊥) (hs₁ : A₁ ⊔ B₁ = J₁) (h₂ : A₂ ⊓ B₂ = ⊥)
    (hs₂ : A₂ ⊔ B₂ = J₂) :
    sSupIndep ({A₁, B₁, A₂, B₂} : Set (Subgroup W)) ∧
      sSup ({A₁, B₁, A₂, B₂} : Set (Subgroup W)) = ⊤ := by
  have hset : ({A₁, B₁, A₂, B₂} : Set (Subgroup W)) =
      ({A₁} ∪ {B₁}) ∪ ({A₂} ∪ {B₂}) := by
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hsup : sSup ({A₁, B₁, A₂, B₂} : Set (Subgroup W)) = ⊤ := by
    rw [hset, sSup_union, sSup_union, sSup_union, sSup_singleton, sSup_singleton,
      sSup_singleton, sSup_singleton, hs₁, hs₂, hs]
  refine ⟨?_, hsup⟩
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with h | h | h | h
  · rw [h]
    have hd : Disjoint A₁ (B₁ ⊔ (A₂ ⊔ B₂)) := by
      have h := s16c167_disjoint_sup_of_inf_eq_bot (A := A₁) (B := B₁) (J := J₁)
        (J' := J₂) h₁ hs₁ hJ
      rwa [← hs₂] at h
    refine hd.mono_right (sSup_le ?_)
    intro x hx
    rw [Set.mem_sdiff] at hx
    obtain ⟨hxS, hxne⟩ := hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxS hxne
    rcases hxS with h | h | h | h
    · exact absurd h hxne
    · rw [h]; exact le_sup_left
    · rw [h]; exact le_sup_of_le_right le_sup_left
    · rw [h]; exact le_sup_of_le_right le_sup_right
  · rw [h]
    have hd : Disjoint B₁ (A₁ ⊔ (A₂ ⊔ B₂)) := by
      have h := s16c167_disjoint_sup_of_inf_eq_bot (A := B₁) (B := A₁) (J := J₁)
        (J' := J₂) (by rw [inf_comm]; exact h₁) (by rw [sup_comm]; exact hs₁) hJ
      rwa [← hs₂] at h
    refine hd.mono_right (sSup_le ?_)
    intro x hx
    rw [Set.mem_sdiff] at hx
    obtain ⟨hxS, hxne⟩ := hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxS hxne
    rcases hxS with h | h | h | h
    · rw [h]; exact le_sup_left
    · exact absurd h hxne
    · rw [h]; exact le_sup_of_le_right le_sup_left
    · rw [h]; exact le_sup_of_le_right le_sup_right
  · rw [h]
    have hd : Disjoint A₂ (B₂ ⊔ (A₁ ⊔ B₁)) := by
      have h := s16c167_disjoint_sup_of_inf_eq_bot (A := A₂) (B := B₂) (J := J₂)
        (J' := J₁) h₂ hs₂ (by rw [inf_comm]; exact hJ)
      rwa [← hs₁] at h
    refine hd.mono_right (sSup_le ?_)
    intro x hx
    rw [Set.mem_sdiff] at hx
    obtain ⟨hxS, hxne⟩ := hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxS hxne
    rcases hxS with h | h | h | h
    · rw [h]; exact le_sup_of_le_right le_sup_left
    · rw [h]; exact le_sup_of_le_right le_sup_right
    · exact absurd h hxne
    · rw [h]; exact le_sup_left
  · rw [h]
    have hd : Disjoint B₂ (A₂ ⊔ (A₁ ⊔ B₁)) := by
      have h := s16c167_disjoint_sup_of_inf_eq_bot (A := B₂) (B := A₂) (J := J₂)
        (J' := J₁) (by rw [inf_comm]; exact h₂) (by rw [sup_comm]; exact hs₂)
        (by rw [inf_comm]; exact hJ)
      rwa [← hs₁] at h
    refine hd.mono_right (sSup_le ?_)
    intro x hx
    rw [Set.mem_sdiff] at hx
    obtain ⟨hxS, hxne⟩ := hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxS hxne
    rcases hxS with h | h | h | h
    · rw [h]; exact le_sup_of_le_right le_sup_left
    · rw [h]; exact le_sup_of_le_right le_sup_right
    · rw [h]; exact le_sup_left
    · exact absurd h hxne

theorem s16c167_cfg10_four (F : Cfg10Mod X Fs I₁ I₂) :
    ∃ 𝒰 : Set (Subgroup W), 𝒰.ncard = 4 ∧ (∀ Y ∈ 𝒰, rk ↥Y = 2) ∧ sSupIndep 𝒰 ∧
      sSup 𝒰 = ⊤ ∧ ∀ x ∈ X, ∀ Y ∈ 𝒰, Y.map x.toMonoidHom ∈ 𝒰 := by
  obtain ⟨A₁, B₁, hA₁I₁, hB₁I₁, hrkA₁, hrkB₁, hinf₁, hsup₁, hA₁fix, hB₁fix, hchar₁⟩ :=
    s16c167_cfg10_comps F (Or.inl rfl)
  obtain ⟨A₂, B₂, hA₂I₂, hB₂I₂, hrkA₂, hrkB₂, hinf₂, hsup₂, hA₂fix, hB₂fix, hchar₂⟩ :=
    s16c167_cfg10_comps F (Or.inr rfl)
  have hA₁B₁ : A₁ ≠ B₁ := s16c167_ne_of_inf_eq_bot hinf₁ hrkA₁
  have hA₂B₂ : A₂ ≠ B₂ := s16c167_ne_of_inf_eq_bot hinf₂ hrkA₂
  have hA₁A₂ : A₁ ≠ A₂ := s16c167_ne_of_le_indep hA₁I₁ hA₂I₂ F.inf hrkA₁
  have hA₁B₂ : A₁ ≠ B₂ := s16c167_ne_of_le_indep hA₁I₁ hB₂I₂ F.inf hrkA₁
  have hB₁A₂ : B₁ ≠ A₂ := s16c167_ne_of_le_indep hB₁I₁ hA₂I₂ F.inf hrkB₁
  have hB₁B₂ : B₁ ≠ B₂ := s16c167_ne_of_le_indep hB₁I₁ hB₂I₂ F.inf hrkB₁
  have hncard : ({A₁, B₁, A₂, B₂} : Set (Subgroup W)).ncard = 4 := by
    rw [Set.ncard_eq_four]
    exact ⟨A₁, B₁, A₂, B₂, hA₁B₁, hA₁A₂, hA₁B₂, hB₁A₂, hB₁B₂, hA₂B₂, rfl⟩
  have hind : sSupIndep ({A₁, B₁, A₂, B₂} : Set (Subgroup W)) :=
    (s16c167_indep_four F.inf F.sup hinf₁ hsup₁ hinf₂ hsup₂).1
  have htop : sSup ({A₁, B₁, A₂, B₂} : Set (Subgroup W)) = ⊤ :=
    (s16c167_indep_four F.inf F.sup hinf₁ hsup₁ hinf₂ hsup₂).2
  have hrk2 : ∀ Y ∈ ({A₁, B₁, A₂, B₂} : Set (Subgroup W)), rk ↥Y = 2 := by
    intro Y hY
    have hYmem := hY
    simp at hYmem
    rcases hYmem with h | h | h | h
    · rw [h]; exact hrkA₁
    · rw [h]; exact hrkB₁
    · rw [h]; exact hrkA₂
    · rw [h]; exact hrkB₂
  refine ⟨{A₁, B₁, A₂, B₂}, hncard, hrk2, hind, htop, ?_⟩
  · intro x hx Y hY
    have hrkY : rk ↥Y = 2 := hrk2 Y hY
    have hYrep := hY
    have hrep : ∃ (I : Subgroup W) (R : Subgroup (MulAut W)),
        (I = I₁ ∨ I = I₂) ∧ R ≤ Fs ∧ Y = I ⊓ fixV R := by
      simp at hYrep
      rcases hYrep with h | h | h | h
      · rw [h]
        exact ⟨I₁, hA₁fix.choose, Or.inl rfl, hA₁fix.choose_spec.1, hA₁fix.choose_spec.2⟩
      · rw [h]
        exact ⟨I₁, hB₁fix.choose, Or.inl rfl, hB₁fix.choose_spec.1, hB₁fix.choose_spec.2⟩
      · rw [h]
        exact ⟨I₂, hA₂fix.choose, Or.inr rfl, hA₂fix.choose_spec.1, hA₂fix.choose_spec.2⟩
      · rw [h]
        exact ⟨I₂, hB₂fix.choose, Or.inr rfl, hB₂fix.choose_spec.1, hB₂fix.choose_spec.2⟩
    obtain ⟨I, R, hI, hRFs, hYeq⟩ := hrep
    have hmap : Y.map x.toMonoidHom =
        (I.map x.toMonoidHom) ⊓ fixV (R.map (MulAut.conj x).toMonoidHom) := by
      rw [hYeq, s16c167_map_inf_fixV x I R]
    have hR'Fs : R.map (MulAut.conj x).toMonoidHom ≤ Fs := by
      rintro _ ⟨r, hr, rfl⟩
      simpa using F.norm x hx r (hRFs hr)
    have hrkmap : rk ↥(I.map x.toMonoidHom ⊓
        fixV (R.map (MulAut.conj x).toMonoidHom)) = 2 := by
      rw [← hmap, rk_map_aut_eq, hrkY]
    have hI' : I.map x.toMonoidHom = I₁ ∨ I.map x.toMonoidHom = I₂ := by
      have hmem : I.map x.toMonoidHom ∈ conjSubs X I₁ := by
        rcases hI with hI | hI
        · rw [hI]; exact ⟨x, hx, rfl⟩
        · rw [hI]
          exact s16c167_cfg4_map_mem hx (by rw [F.orb]; simp)
      rw [F.orb] at hmem
      simpa using hmem
    rcases hI' with hI' | hI'
    · have hrk' : rk ↥(I₁ ⊓ fixV (R.map (MulAut.conj x).toMonoidHom)) = 2 := by
        rw [← hI']; exact hrkmap
      have hchar := hchar₁ (R.map (MulAut.conj x).toMonoidHom) hR'Fs hrk'
      rw [hmap, hI']
      rcases hchar with h | h <;> rw [h] <;> simp
    · have hrk' : rk ↥(I₂ ⊓ fixV (R.map (MulAut.conj x).toMonoidHom)) = 2 := by
        rw [← hI']; exact hrkmap
      have hchar := hchar₂ (R.map (MulAut.conj x).toMonoidHom) hR'Fs hrk'
      rw [hmap, hI']
      rcases hchar with h | h <;> rw [h] <;> simp

theorem s16c167_cfg10_two19 (F : Cfg10Mod X Fs I₁ I₂) : Two19 X := by
  intro E hEX hE2 hEc hrk
  obtain ⟨𝒰, hn, hrk2, hind, hsup, hperm⟩ := s16c167_cfg10_four F
  exact s16c167_two_bad_four (𝒴 := 𝒰)
    ⟨F.sq, hE2, hEc, hn, hrk2, hind, hsup, fun e he Y hY => hperm e (hEX he) Y hY⟩ hrk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

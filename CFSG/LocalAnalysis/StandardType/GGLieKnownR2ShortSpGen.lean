module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSpDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieSpCent
public import CFSG.Timmesfeld.Transvection.ModelSpGen
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMLevi
public import CFSG.Timmesfeld.ARS.Sec12Center
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique.B113Lie.Sp
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Symplectic

private def AllTrans {n : ℕ} {F : Type} [Field F]
    (H : Subgroup (StatedSp n F)) (x : Fin n ⊕ Fin n → F) : Prop :=
  ∀ (c : F) (t : StatedSp n F),
    (∀ w, natRep (StatedSp n F) t w = w + (c * (spForm n F).β x w) • x) → t ∈ H

private def Visible {n : ℕ} {F : Type} [Field F]
    (a₁ a₂ x : Fin n ⊕ Fin n → F) : Prop :=
  (spForm n F).β a₁ x ≠ 0 ∨ (spForm n F).β a₂ x ≠ 0

private theorem spForm_β_smul_left {n : ℕ} {F : Type} [Field F]
    (c : F) (u v : Fin n ⊕ Fin n → F) :
    (spForm n F).β (c • u) v = c * (spForm n F).β u v := by
  rw [(spForm n F).smul_left]
  rfl

private theorem spForm_β_symm {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (x y : Fin n ⊕ Fin n → F) :
    (spForm n F).β x y = (spForm n F).β y x := by
  have h0 : (spForm n F).β x y + (spForm n F).β y x = 0 := by
    have h := spForm_self n F (x + y)
    simpa [(spForm n F).add_left, (spForm n F).add_right, spForm_self, add_assoc, add_comm,
      add_left_comm] using h
  have h1 : (spForm n F).β y x = -(spForm n F).β x y := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h0
  rw [h1, CharTwo.neg_eq]

private theorem add_self_eq_zero_vec {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (v : Fin n ⊕ Fin n → F) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private theorem cm_spForm_eq_β {n : ℕ} {F : Type} [Field F]
    (v w : Fin n ⊕ Fin n → F) :
    CFSG.Timmesfeld.ARS.CaseM.spForm v w = (spForm n F).β v w := rfl

private theorem mem_perp_of_β_eq_zero {n : ℕ} {F : Type} [Field F]
    {a₁ a₂ x : Fin n ⊕ Fin n → F}
    (h₁ : (spForm n F).β a₁ x = 0) (h₂ : (spForm n F).β a₂ x = 0) :
    x ∈ (spForm n F).perp (Submodule.span F {a₁, a₂}) := by
  rw [ReflForm.mem_perp]
  intro w hw
  obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hw
  simp only [(spForm n F).add_left, spForm_β_smul_left, h₁, h₂, mul_zero, add_zero]

private theorem sub_smul_b_mem_perp {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    (x : Fin n ⊕ Fin n → F) :
    x - ((spForm n F).β a₁ x • b₁ + (spForm n F).β a₂ x • b₂) ∈
      (spForm n F).perp (Submodule.span F {a₁, a₂}) := by
  have h11 : (spForm n F).β a₁ b₁ = 1 := hp.1
  have h22 : (spForm n F).β a₂ b₂ = 1 := hp.2.1
  have h12 : (spForm n F).β a₁ b₂ = 0 := hp.2.2.2.2.1
  have h21 : (spForm n F).β a₂ b₁ = 0 := hp.2.2.2.2.2
  rw [ReflForm.mem_perp]
  intro w hw
  obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hw
  simp only [(spForm n F).add_left, spForm_β_smul_left, (spForm n F).β_sub_right,
    (spForm n F).add_right, (spForm n F).smul_right, h11, h22, h12, h21, mul_one, mul_zero,
    add_zero, sub_zero]
  ring

private theorem β_a₁_add_inv_a₂_add {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    (x : Fin n ⊕ Fin n → F) :
    (spForm n F).β a₁ (((spForm n F).β a₁ x • b₁ + ((spForm n F).β a₂ x)⁻¹ • a₂) +
      (spForm n F).β a₂ x • b₂) = (spForm n F).β a₁ x := by
  have h11 : (spForm n F).β a₁ b₁ = 1 := hp.1
  have h12 : (spForm n F).β a₁ a₂ = 0 := hp.2.2.1
  have h12' : (spForm n F).β a₁ b₂ = 0 := hp.2.2.2.2.1
  simp only [(spForm n F).add_right, (spForm n F).smul_right, h11, h12, h12', mul_one, mul_zero,
    add_zero, zero_add]

private theorem β_a₂_add_inv_a₂_add {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    (x : Fin n ⊕ Fin n → F) :
    (spForm n F).β a₂ (((spForm n F).β a₁ x • b₁ + ((spForm n F).β a₂ x)⁻¹ • a₂) +
      (spForm n F).β a₂ x • b₂) = (spForm n F).β a₂ x := by
  have h21 : (spForm n F).β a₂ b₁ = 0 := hp.2.2.2.2.2
  have h22 : (spForm n F).β a₂ b₂ = 1 := hp.2.1
  simp only [(spForm n F).add_right, (spForm n F).smul_right, h21, spForm_self, h22, mul_zero,
    mul_one, add_zero, zero_add]

private theorem allTrans_zero {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {H : Subgroup (StatedSp n F)} : AllTrans H 0 := by
  intro c t ht
  have ht1 : t = 1 := by
    apply natRep_injective (StatedSp n F)
    refine LinearMap.ext fun w => ?_
    rw [ht w, (spForm n F).β_zero_left, mul_zero, zero_smul, add_zero, map_one,
      Module.End.one_apply]
  rw [ht1]
  exact H.one_mem

private theorem allTrans_smul {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {H : Subgroup (StatedSp n F)} {x : Fin n ⊕ Fin n → F} (hx : AllTrans H x) (l : F) :
    AllTrans H (l • x) := by
  intro c t ht
  refine hx (l * l * c) t fun w => ?_
  rw [ht w, spForm_β_smul_left, smul_smul]
  congr 1
  ring

private theorem allTrans_conj {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {H : Subgroup (StatedSp n F)} {q : StatedSp n F} (hq : q ∈ H)
    {x : Fin n ⊕ Fin n → F} (hx : AllTrans H x) :
    AllTrans H (natRep (StatedSp n F) q x) := by
  intro c t' ht'
  have ht : ∀ w, natRep (StatedSp n F) (q⁻¹ * t' * q) w =
      w + (c * (spForm n F).β x w) • x := by
    intro w
    have hh : ∀ v, natRep (StatedSp n F) t' v =
        v + (spForm n F).β (c • natRep (StatedSp n F) q x) v •
              natRep (StatedSp n F) q x +
          (spForm n F).β (natRep (StatedSp n F) q x) v • (0 : Fin n ⊕ Fin n → F) := by
      intro v
      rw [ht' v, smul_zero, add_zero, spForm_β_smul_left]
    have hxx : natRep (StatedSp n F) q⁻¹ (natRep (StatedSp n F) q x) = x := by
      simpa using rep_apply_inv_apply (ρ := natRep (StatedSp n F)) q⁻¹ x
    have hconj := rep_conj_apply (F := spForm n F) (ρ := natRep (StatedSp n F))
      (isIsometric_natRep_statedSp n F) hh q⁻¹ w
    simp only [inv_inv] at hconj
    rw [hconj, map_smul, hxx, map_zero, smul_zero, add_zero, spForm_β_smul_left]
  have htH : q⁻¹ * t' * q ∈ H := hx c (q⁻¹ * t' * q) ht
  have hq' : t' = q * (q⁻¹ * t' * q) * q⁻¹ := by group
  rw [hq']
  exact mul_mem (mul_mem hq htH) (inv_mem hq)

private theorem allTrans_of_mem_span {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ : Fin n ⊕ Fin n → F}
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})}
    {H : Subgroup (StatedSp n F)}
    (hrad : sprad (Submodule.span F {a₁, a₂}) hW ≤ H)
    {a : Fin n ⊕ Fin n → F} (ha : a ∈ Submodule.span F {a₁, a₂}) : AllTrans H a := by
  intro c t ht
  apply hrad
  change t ∈ rad (spForm n F) (natRep (StatedSp n F)) (Submodule.span F {a₁, a₂}) hW
  rw [mem_rad]
  refine ⟨fun w hw => ?_, fun v hv => ?_⟩
  · rw [ht w, (hW hw) a ha, mul_zero, zero_smul, add_zero]
  · rw [ht v, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ ha

private theorem exists_trans {n : ℕ} {F : Type} [Field F]
    (v : Fin n ⊕ Fin n → F) (c : F) :
    ∃ t : StatedSp n F, ∀ w, natRep (StatedSp n F) t w =
      w + (c * (spForm n F).β v w) • v := by
  obtain ⟨t, ht⟩ := CFSG.Timmesfeld.Transvection.ModelRank.exists_mat_eq_spTrans v c
  refine ⟨t, fun w => ?_⟩
  rw [natRep_apply, ← SpExtras.mat_apply t, ht,
    CFSG.Timmesfeld.Transvection.ModelRank.spTrans_mulVec, cm_spForm_eq_β]

private theorem allTrans_add_of_β_eq_one {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {H : Subgroup (StatedSp n F)} {x y : Fin n ⊕ Fin n → F}
    (hx : AllTrans H x) (hy : AllTrans H y)
    (hxy : (spForm n F).β x y = 1) : AllTrans H (x + y) := by
  obtain ⟨t, ht⟩ := exists_trans y 1
  have htH : t ∈ H := hy 1 t ht
  have htx : natRep (StatedSp n F) t x = x + y := by
    rw [ht x, one_mul, spForm_β_symm y x, hxy, one_smul]
  rw [← htx]
  exact allTrans_conj htH hx

private theorem allTrans_add_of_β_ne_zero {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ : Fin n ⊕ Fin n → F}
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})}
    {H : Subgroup (StatedSp n F)}
    (hrad : sprad (Submodule.span F {a₁, a₂}) hW ≤ H)
    {x d : Fin n ⊕ Fin n → F} (hx : AllTrans H x)
    (hd : d ∈ Submodule.span F {a₁, a₂})
    (hdx : (spForm n F).β d x ≠ 0) : AllTrans H (x + d) := by
  obtain ⟨t, ht⟩ := exists_trans d ((spForm n F).β d x)⁻¹
  have htH : t ∈ H := (allTrans_of_mem_span hrad hd) _ t ht
  have htx : natRep (StatedSp n F) t x = x + d := by
    rw [ht x, inv_mul_cancel₀ hdx, one_smul]
  rw [← htx]
  exact allTrans_conj htH hx

private theorem allTrans_add_of_mem_span_of_visible {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ : Fin n ⊕ Fin n → F}
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})}
    {H : Subgroup (StatedSp n F)}
    (hrad : sprad (Submodule.span F {a₁, a₂}) hW ≤ H)
    {x a : Fin n ⊕ Fin n → F} (hx : AllTrans H x) (hvis : Visible a₁ a₂ x)
    (ha : a ∈ Submodule.span F {a₁, a₂}) : AllTrans H (x + a) := by
  by_cases hax : (spForm n F).β a x = 0
  · rcases hvis with h1 | h2
    · have ha₁ : a₁ ∈ Submodule.span F {a₁, a₂} := Submodule.subset_span (by simp)
      have hxd : AllTrans H (x + a₁) := allTrans_add_of_β_ne_zero hrad hx ha₁ h1
      have hsum : a + a₁ ∈ Submodule.span F {a₁, a₂} := add_mem ha ha₁
      have had : (spForm n F).β (a + a₁) (x + a₁) ≠ 0 := by
        have h2' : (spForm n F).β a a₁ = 0 := (hW ha₁) a ha
        simpa [(spForm n F).add_left, (spForm n F).add_right, hax, h2', spForm_self] using h1
      have hres := allTrans_add_of_β_ne_zero hrad hxd hsum had
      have heq : (x + a₁) + (a + a₁) = x + a := by
        have h : (x + a₁) + (a + a₁) = x + a + (a₁ + a₁) := by abel
        rw [h, add_self_eq_zero_vec a₁, add_zero]
      rwa [heq] at hres
    · have ha₂ : a₂ ∈ Submodule.span F {a₁, a₂} := Submodule.subset_span (by simp)
      have hxd : AllTrans H (x + a₂) := allTrans_add_of_β_ne_zero hrad hx ha₂ h2
      have hsum : a + a₂ ∈ Submodule.span F {a₁, a₂} := add_mem ha ha₂
      have had : (spForm n F).β (a + a₂) (x + a₂) ≠ 0 := by
        have h2' : (spForm n F).β a a₂ = 0 := (hW ha₂) a ha
        simpa [(spForm n F).add_left, (spForm n F).add_right, hax, h2', spForm_self] using h2
      have hres := allTrans_add_of_β_ne_zero hrad hxd hsum had
      have heq : (x + a₂) + (a + a₂) = x + a := by
        have h : (x + a₂) + (a + a₂) = x + a + (a₂ + a₂) := by abel
        rw [h, add_self_eq_zero_vec a₂, add_zero]
      rwa [heq] at hres
  · exact allTrans_add_of_β_ne_zero hrad hx ha hax

private theorem allTrans_add_of_mem_perp {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ : Fin n ⊕ Fin n → F}
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})}
    {H : Subgroup (StatedSp n F)}
    (hrad : sprad (Submodule.span F {a₁, a₂}) hW ≤ H)
    {x z : Fin n ⊕ Fin n → F} (hx : AllTrans H x) (hvis : Visible a₁ a₂ x)
    (hz : z ∈ (spForm n F).perp (Submodule.span F {a₁, a₂})) : AllTrans H (x + z) := by
  have hax : ∃ a ∈ Submodule.span F {a₁, a₂}, (spForm n F).β a x = 1 := by
    rcases hvis with h1 | h2
    · refine ⟨((spForm n F).β a₁ x)⁻¹ • a₁,
        Submodule.smul_mem _ _ (Submodule.subset_span (by simp)), ?_⟩
      rw [spForm_β_smul_left]
      exact inv_mul_cancel₀ h1
    · refine ⟨((spForm n F).β a₂ x)⁻¹ • a₂,
        Submodule.smul_mem _ _ (Submodule.subset_span (by simp)), ?_⟩
      rw [spForm_β_smul_left]
      exact inv_mul_cancel₀ h2
  obtain ⟨a, ha, hax1⟩ := hax
  have haz : (spForm n F).β a z = 0 := hz a ha
  obtain ⟨σ, hσ⟩ := exists_siegel a z haz
  have hσrad : σ ∈ sprad (Submodule.span F {a₁, a₂}) hW := siegel_mem_rad ha hz hσ
  have hσH : σ ∈ H := hrad hσrad
  have hxz : AllTrans H (x + (spForm n F).β z x • a) :=
    allTrans_add_of_mem_span_of_visible hrad hx hvis (Submodule.smul_mem _ _ ha)
  have hσx : natRep (StatedSp n F) σ (x + (spForm n F).β z x • a) = x + z := by
    rw [hσ]
    have haa : (spForm n F).β a a = 0 := spForm_self n F a
    have hza : (spForm n F).β z a = 0 := by
      rw [spForm_β_symm]
      exact hz a ha
    have h1 : (spForm n F).β a (x + (spForm n F).β z x • a) = 1 := by
      rw [(spForm n F).add_right, (spForm n F).smul_right, hax1, haa, mul_zero, add_zero]
    have h2 : (spForm n F).β z (x + (spForm n F).β z x • a) = (spForm n F).β z x := by
      rw [(spForm n F).add_right, (spForm n F).smul_right, hza, mul_zero, add_zero]
    rw [h1, h2, one_smul]
    have hcomm : (x + (spForm n F).β z x • a) + z + (spForm n F).β z x • a =
        x + z + ((spForm n F).β z x • a + (spForm n F).β z x • a) := by abel
    rw [hcomm, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  rw [← hσx]
  exact allTrans_conj hσH hxz

private theorem allTrans_of_sub_mem_perp {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ : Fin n ⊕ Fin n → F}
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})}
    {H : Subgroup (StatedSp n F)}
    (hrad : sprad (Submodule.span F {a₁, a₂}) hW ≤ H)
    {x y : Fin n ⊕ Fin n → F} (hy : AllTrans H y) (hvis : Visible a₁ a₂ y)
    (hz : x - y ∈ (spForm n F).perp (Submodule.span F {a₁, a₂})) : AllTrans H x := by
  have hxy : x = y + (x - y) := by abel
  rw [hxy]
  exact allTrans_add_of_mem_perp hrad hy hvis hz

private theorem allTrans_of_visible {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})}
    {H : Subgroup (StatedSp n F)}
    (hrad : sprad (Submodule.span F {a₁, a₂}) hW ≤ H)
    (hb₁ : AllTrans H b₁) (hb₂ : AllTrans H b₂)
    {x : Fin n ⊕ Fin n → F} (hvis : Visible a₁ a₂ x) : AllTrans H x := by
  have h11 : (spForm n F).β a₁ b₁ = 1 := hp.1
  have h22 : (spForm n F).β a₂ b₂ = 1 := hp.2.1
  have h12 : (spForm n F).β a₁ a₂ = 0 := hp.2.2.1
  have hb12 : (spForm n F).β b₁ b₂ = 0 := hp.2.2.2.1
  have h12' : (spForm n F).β a₁ b₂ = 0 := hp.2.2.2.2.1
  have hbase : x - ((spForm n F).β a₁ x • b₁ + (spForm n F).β a₂ x • b₂) ∈
      (spForm n F).perp (Submodule.span F {a₁, a₂}) := sub_smul_b_mem_perp hp x
  by_cases hβ0 : (spForm n F).β a₂ x = 0
  · have hα0 : (spForm n F).β a₁ x ≠ 0 := by
      rcases hvis with h | h
      · exact h
      · exact (h hβ0).elim
    have hy : (spForm n F).β a₁ x • b₁ + (spForm n F).β a₂ x • b₂ =
        (spForm n F).β a₁ x • b₁ := by rw [hβ0, zero_smul, add_zero]
    have hz : x - (spForm n F).β a₁ x • b₁ ∈
        (spForm n F).perp (Submodule.span F {a₁, a₂}) := by
      simpa only [hy] using hbase
    refine allTrans_of_sub_mem_perp hrad (allTrans_smul hb₁ _) ?_ hz
    left
    rw [(spForm n F).smul_right, h11, mul_one]
    exact hα0
  · by_cases hα0 : (spForm n F).β a₁ x = 0
    · have hβ0' : (spForm n F).β a₂ x ≠ 0 := by
        rcases hvis with h | h
        · exact (h hα0).elim
        · exact h
      have hy : (spForm n F).β a₁ x • b₁ + (spForm n F).β a₂ x • b₂ =
          (spForm n F).β a₂ x • b₂ := by rw [hα0, zero_smul, zero_add]
      have hz : x - (spForm n F).β a₂ x • b₂ ∈
          (spForm n F).perp (Submodule.span F {a₁, a₂}) := by
        simpa only [hy] using hbase
      refine allTrans_of_sub_mem_perp hrad (allTrans_smul hb₂ _) ?_ hz
      right
      rw [(spForm n F).smul_right, h22, mul_one]
      exact hβ0'
    · have hβ0' : (spForm n F).β a₂ x ≠ 0 := hβ0
      have hu : AllTrans H ((spForm n F).β a₁ x • b₁ + ((spForm n F).β a₂ x)⁻¹ • a₂) := by
        refine allTrans_add_of_mem_perp hrad (allTrans_smul hb₁ _) ?_ ?_
        · left
          rw [(spForm n F).smul_right, h11, mul_one]
          exact hα0
        · exact hW (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      have hw : AllTrans H ((spForm n F).β a₂ x • b₂) := allTrans_smul hb₂ _
      have huv : (spForm n F).β ((spForm n F).β a₁ x • b₁ + ((spForm n F).β a₂ x)⁻¹ • a₂)
          ((spForm n F).β a₂ x • b₂) = 1 := by
        rw [(spForm n F).add_left, spForm_β_smul_left, spForm_β_smul_left,
          (spForm n F).smul_right, (spForm n F).smul_right, hb12, h22]
        simp only [mul_zero, mul_one, zero_add]
        exact inv_mul_cancel₀ hβ0'
      have hy := allTrans_add_of_β_eq_one hu hw huv
      refine allTrans_of_sub_mem_perp hrad hy ?_ ?_
      · left
        simpa only [(spForm n F).add_right, (spForm n F).smul_right, h11, h12, h12', mul_one,
          mul_zero, add_zero, zero_add] using hα0
      · apply mem_perp_of_β_eq_zero
        · rw [(spForm n F).β_sub_right, β_a₁_add_inv_a₂_add hp x, sub_self]
        · rw [(spForm n F).β_sub_right, β_a₂_add_inv_a₂_add hp x, sub_self]

private theorem allTrans_of_mem_perp_ne_zero {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})}
    {H : Subgroup (StatedSp n F)}
    (hrad : sprad (Submodule.span F {a₁, a₂}) hW ≤ H)
    (hb₁ : AllTrans H b₁) (hb₂ : AllTrans H b₂)
    {v : Fin n ⊕ Fin n → F} (hv : v ∈ (spForm n F).perp (Submodule.span F {a₁, a₂}))
    (hv0 : v ≠ 0) : AllTrans H v := by
  have h11 : (spForm n F).β a₁ b₁ = 1 := hp.1
  obtain ⟨w, hw⟩ := exists_β_eq_one (F := spForm n F) hv0
  have hwv : (spForm n F).β w v = 1 := by rw [spForm_β_symm]; exact hw
  have hvis_or : Visible a₁ a₂ w ∨ w ∈ (spForm n F).perp (Submodule.span F {a₁, a₂}) := by
    by_cases h : Visible a₁ a₂ w
    · exact Or.inl h
    · right
      simp only [Visible] at h
      push Not at h
      exact mem_perp_of_β_eq_zero h.1 h.2
  obtain ⟨u, hu_vis, huv⟩ : ∃ u, Visible a₁ a₂ u ∧ (spForm n F).β u v = 1 := by
    rcases hvis_or with hw_vis | hw_perp
    · exact ⟨w, hw_vis, hwv⟩
    · by_cases hb1v : (spForm n F).β b₁ v ≠ 0
      · refine ⟨((spForm n F).β b₁ v)⁻¹ • b₁, ?_, ?_⟩
        · left
          rw [(spForm n F).smul_right, h11, mul_one]
          exact inv_ne_zero hb1v
        · rw [spForm_β_smul_left, inv_mul_cancel₀ hb1v]
      · push Not at hb1v
        refine ⟨w + b₁, ?_, ?_⟩
        · left
          rw [(spForm n F).add_right, hw_perp a₁ (Submodule.subset_span (by simp)), h11,
            zero_add]
          exact one_ne_zero
        · rw [(spForm n F).add_left, hwv, hb1v, add_zero]
  have hu : AllTrans H u := allTrans_of_visible hp hrad hb₁ hb₂ hu_vis
  have huv_vis : Visible a₁ a₂ (u + v) := by
    rcases hu_vis with h | h
    · left
      rw [(spForm n F).add_right, hv a₁ (Submodule.subset_span (by simp)), add_zero]
      exact h
    · right
      rw [(spForm n F).add_right, hv a₂ (Submodule.subset_span (by simp)), add_zero]
      exact h
  have huvP : AllTrans H (u + v) := allTrans_of_visible hp hrad hb₁ hb₂ huv_vis
  have hsum : (spForm n F).β u (u + v) = 1 := by
    rw [(spForm n F).add_right, spForm_self, zero_add, huv]
  have hres := allTrans_add_of_β_eq_one hu huvP hsum
  have heq : u + (u + v) = v := by
    have h : u + (u + v) = v + (u + u) := by abel
    rw [h, add_self_eq_zero_vec u, add_zero]
  rwa [heq] at hres

private theorem allTrans_all {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})}
    {H : Subgroup (StatedSp n F)}
    (hrad : sprad (Submodule.span F {a₁, a₂}) hW ≤ H)
    (hb₁ : AllTrans H b₁) (hb₂ : AllTrans H b₂) : ∀ x, AllTrans H x := by
  intro x
  by_cases hx0 : x = 0
  · rw [hx0]
    exact allTrans_zero
  · by_cases hvis : Visible a₁ a₂ x
    · exact allTrans_of_visible hp hrad hb₁ hb₂ hvis
    · have hxperp : x ∈ (spForm n F).perp (Submodule.span F {a₁, a₂}) := by
        simp only [Visible] at hvis
        push Not at hvis
        exact mem_perp_of_β_eq_zero hvis.1 hvis.2
      exact allTrans_of_mem_perp_ne_zero hp hrad hb₁ hb₂ hxperp hx0

private theorem exists_alt_siegel {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ : Fin n ⊕ Fin n → F} (h : (spForm n F).β a₁ a₂ = 0) :
    ∃ g ∈ spAltSiegel n F a₁ a₂, ∀ v : Fin n ⊕ Fin n → F,
      natRep (StatedSp n F) g v = v + (spForm n F).β a₂ v • a₁ + (spForm n F).β a₁ v • a₂ := by
  obtain ⟨g, hg, hgv⟩ := exists_mem_spAltSiegel_mulVec (n := n) (F := F) h 1
  refine ⟨g, hg, fun v => ?_⟩
  rw [natRep_apply, hgv v]
  simp only [one_mul, spForm_β]

private theorem allTrans_b₁ {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})}
    {H : Subgroup (StatedSp n F)}
    (hrad : sprad (Submodule.span F {a₁, a₂}) hW ≤ H)
    (hS : spAltSiegel n F a₁ a₂ ≤ H) (hS' : spAltSiegel n F b₁ b₂ ≤ H) :
    AllTrans H b₁ := by
  obtain ⟨q₁, hq₁S, hq₁⟩ := exists_alt_siegel (a₁ := a₁) (a₂ := a₂) hp.2.2.1
  obtain ⟨s₁, hs₁S, hs₁⟩ := exists_alt_siegel (a₁ := b₁) (a₂ := b₂) hp.2.2.2.1
  have h11 : (spForm n F).β a₁ b₁ = 1 := hp.1
  have h12 : (spForm n F).β a₁ a₂ = 0 := hp.2.2.1
  have h21 : (spForm n F).β a₂ b₁ = 0 := hp.2.2.2.2.2
  have ha₂ : AllTrans H a₂ := allTrans_of_mem_span hrad (Submodule.subset_span (by simp))
  have h1 : AllTrans H (natRep (StatedSp n F) s₁ a₂) := allTrans_conj (hS' hs₁S) ha₂
  have h2 : natRep (StatedSp n F) s₁ a₂ = a₂ + b₁ := by
    rw [hs₁ a₂]
    have hb₂a₂ : (spForm n F).β b₂ a₂ = 1 := by rw [spForm_β_symm]; exact hp.2.1
    have hb₁a₂ : (spForm n F).β b₁ a₂ = 0 := by rw [spForm_β_symm]; exact h21
    rw [hb₂a₂, hb₁a₂, one_smul, zero_smul, add_zero]
  have h3 : AllTrans H (natRep (StatedSp n F) q₁ (a₂ + b₁)) :=
    allTrans_conj (hS hq₁S) (by rwa [h2] at h1)
  have h4 : natRep (StatedSp n F) q₁ (a₂ + b₁) = b₁ := by
    rw [hq₁ (a₂ + b₁)]
    have h1' : (spForm n F).β a₂ (a₂ + b₁) = 0 := by
      rw [(spForm n F).add_right, spForm_self, h21, add_zero]
    have h2' : (spForm n F).β a₁ (a₂ + b₁) = 1 := by
      rw [(spForm n F).add_right, h12, h11, zero_add]
    rw [h1', h2', zero_smul, one_smul, add_zero]
    have heq : a₂ + b₁ + a₂ = b₁ := by
      have h : a₂ + b₁ + a₂ = b₁ + (a₂ + a₂) := by abel
      rw [h, add_self_eq_zero_vec a₂, add_zero]
    rw [heq]
  rwa [h4] at h3

private theorem allTrans_b₂ {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})}
    {H : Subgroup (StatedSp n F)}
    (hrad : sprad (Submodule.span F {a₁, a₂}) hW ≤ H)
    (hS : spAltSiegel n F a₁ a₂ ≤ H) (hS' : spAltSiegel n F b₁ b₂ ≤ H) :
    AllTrans H b₂ := by
  obtain ⟨q₁, hq₁S, hq₁⟩ := exists_alt_siegel (a₁ := a₁) (a₂ := a₂) hp.2.2.1
  obtain ⟨s₁, hs₁S, hs₁⟩ := exists_alt_siegel (a₁ := b₁) (a₂ := b₂) hp.2.2.2.1
  have h11 : (spForm n F).β a₁ b₁ = 1 := hp.1
  have h12 : (spForm n F).β a₁ a₂ = 0 := hp.2.2.1
  have h12' : (spForm n F).β a₁ b₂ = 0 := hp.2.2.2.2.1
  have h22 : (spForm n F).β a₂ b₂ = 1 := hp.2.1
  have ha₁ : AllTrans H a₁ := allTrans_of_mem_span hrad (Submodule.subset_span (by simp))
  have h1 : AllTrans H (natRep (StatedSp n F) s₁ a₁) := allTrans_conj (hS' hs₁S) ha₁
  have h2 : natRep (StatedSp n F) s₁ a₁ = a₁ + b₂ := by
    rw [hs₁ a₁]
    have hb₂a₁ : (spForm n F).β b₂ a₁ = 0 := by rw [spForm_β_symm]; exact h12'
    have hb₁a₁ : (spForm n F).β b₁ a₁ = 1 := by rw [spForm_β_symm]; exact h11
    rw [hb₂a₁, hb₁a₁, zero_smul, one_smul, add_zero]
  have h3 : AllTrans H (natRep (StatedSp n F) q₁ (a₁ + b₂)) :=
    allTrans_conj (hS hq₁S) (by rwa [h2] at h1)
  have h4 : natRep (StatedSp n F) q₁ (a₁ + b₂) = b₂ := by
    rw [hq₁ (a₁ + b₂)]
    have h1' : (spForm n F).β a₂ (a₁ + b₂) = 1 := by
      rw [(spForm n F).add_right, spForm_β_symm a₂ a₁, h12, h22, zero_add]
    have h2' : (spForm n F).β a₁ (a₁ + b₂) = 0 := by
      rw [(spForm n F).add_right, spForm_self, h12', add_zero]
    rw [h1', h2', one_smul, zero_smul, add_zero]
    have heq : a₁ + b₂ + a₁ = b₂ := by
      have h : a₁ + b₂ + a₁ = b₂ + (a₁ + a₁) := by abel
      rw [h, add_self_eq_zero_vec a₁, add_zero]
    rw [heq]
  rwa [h4] at h3

theorem sprad_sup_spAltSiegel_eq_top {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})} :
    sprad (Submodule.span F {a₁, a₂}) hW ⊔ (spAltSiegel n F a₁ a₂ ⊔ spAltSiegel n F b₁ b₂) = ⊤ := by
  let H : Subgroup (StatedSp n F) :=
    sprad (Submodule.span F {a₁, a₂}) hW ⊔ (spAltSiegel n F a₁ a₂ ⊔ spAltSiegel n F b₁ b₂)
  change H = ⊤
  have hrad : sprad (Submodule.span F {a₁, a₂}) hW ≤ H := le_sup_left
  have hS : spAltSiegel n F a₁ a₂ ≤ H := le_sup_left.trans le_sup_right
  have hS' : spAltSiegel n F b₁ b₂ ≤ H := le_sup_right.trans le_sup_right
  have hb₁ : AllTrans H b₁ := allTrans_b₁ hp hrad hS hS'
  have hb₂ : AllTrans H b₂ := allTrans_b₂ hp hrad hS hS'
  have hall : ∀ x, AllTrans H x := allTrans_all hp hrad hb₁ hb₂
  rw [eq_top_iff, ← CFSG.Timmesfeld.Transvection.ModelRank.closure_spTrans_eq_top n F,
    Subgroup.closure_le]
  rintro x ⟨v, c, hx⟩
  exact hall v c x (by
    intro w
    rw [natRep_apply, ← SpExtras.mat_apply x, hx,
      CFSG.Timmesfeld.Transvection.ModelRank.spTrans_mulVec, cm_spForm_eq_β])

end CFSG.StandardType.LieKnownR2.Short

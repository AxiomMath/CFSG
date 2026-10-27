module

public import CFSG.Quasithin.Background.SmithB45HM22Sub
public import CFSG.Quasithin.Background.SmithB45HM22Cover
public import CFSG.Quasithin.Background.SmithB45MatM22Cls

public section

namespace CFSG.Quasithin.HM22

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
  CFSG.Quasithin.HatM22 CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Blueprint

@[expose] def liftW (r : List ℤ) (q : ℕ) : List ℤ :=
  invW (cosetW.getD q []) ++ r ++ cosetW.getD q []

theorem isLetters_cosetW : ∀ q : Fin 22, IsLetters (cosetW.getD q []) := by
  unfold IsLetters
  decide

theorem cosetW_zero_act : ∀ q : Fin 22,
    evalCodes [m22gA, m22gB] (cosetW.getD q []) 0 = q := by
  decide +kernel

theorem hatM22Act_cosetW (q : Fin 22) :
    hatM22Act (wordΓ (cosetW.getD q [])) 0 = q := by
  rw [hatM22Act_wordΓ (isLetters_cosetW q), cosetW_zero_act q]

theorem hatM22Act_liftW (r : List ℤ) (q : ℕ) :
    hatM22Act (wordΓ (liftW r q)) =
      (hatM22Act (wordΓ (cosetW.getD q [])))⁻¹ * hatM22Act (wordΓ r) *
        hatM22Act (wordΓ (cosetW.getD q [])) := by
  rw [liftW, wordΓ_append, wordΓ_append, wordΓ_invW, map_mul, map_mul, map_inv]

theorem exists_conj_liftW
    {h : ↥hatH} {c r : Equiv.Perm (Fin 22)} (hc : c ∈ NativeSporadic.M22)
    (hσ : hatM22Act (h : ↥hatM22Γ₀) = c * r * c⁻¹) {wr : List ℤ} (hwr : IsLetters wr)
    (hrw : evalCodes [m22gA, m22gB] wr = r) {q : Fin 22} (hq : c⁻¹ 0 = q)
    (hmem : wordΓ (liftW wr q) ∈ hatH) :
    ∃ e : ℕ, IsConj h (⟨wordΓ (liftW wr q), hmem⟩ * zH ^ e) := by
  set t := wordΓ (cosetW.getD q []) with ht
  have htq : hatM22Act t 0 = q := hatM22Act_cosetW q
  have hm : c * hatM22Act t ∈ NativeSporadic.M22 :=
    NativeSporadic.M22.mul_mem hc (hatM22Act_mem t)
  obtain ⟨mh, hmh⟩ := hatM22Q_surjective ⟨c * hatM22Act t, hm⟩
  have hmh' : hatM22Act mh = c * hatM22Act t := congrArg Subtype.val hmh
  have hmhH : mh ∈ hatH := by
    rw [mem_hatH, hmh', Equiv.Perm.mul_apply, htq, ← hq]
    exact Equiv.apply_symm_apply c 0
  set ρ : ↥hatM22Γ₀ := wordΓ (liftW wr q) with hρ
  have hρact : hatM22Act ρ = (hatM22Act t)⁻¹ * r * hatM22Act t := by
    rw [hρ, hatM22Act_liftW, hatM22Act_wordΓ hwr, hrw]
  have hk : mh⁻¹ * (h : ↥hatM22Γ₀) * mh * ρ⁻¹ ∈ hatM22Act.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hmh', hσ, hρact]
    group
  obtain ⟨e, he⟩ : ∃ e : ℕ, mh⁻¹ * (h : ↥hatM22Γ₀) * mh * ρ⁻¹ = hatM22Z ^ e := by
    rcases (mem_ker_hatM22Act_iff _).1 hk with h1 | h1 | h1
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h1, pow_one]⟩
    · exact ⟨2, h1⟩
  refine ⟨e, ?_⟩
  rw [isConj_iff]
  refine ⟨⟨mh, hmhH⟩⁻¹, ?_⟩
  apply Subtype.ext
  have hz : hatM22Z ^ e ∈ Subgroup.center ↥hatM22Γ₀ :=
    Subgroup.pow_mem _ hatM22Z_mem_center e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, Subgroup.coe_pow]
  change mh⁻¹ * (h : ↥hatM22Γ₀) * mh = ρ * hatM22Z ^ e
  rw [Subgroup.mem_center_iff.mp hz ρ, ← he]
  group

open CFSG.Quasithin.B45Mat.M22 in
theorem fix3 : ∀ q : Fin 22, evalCodes [m22gA, m22gB] word3 q = q →
    q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 11 := by decide +kernel

open CFSG.Quasithin.B45Mat.M22 in
theorem fix5 : ∀ q : Fin 22, evalCodes [m22gA, m22gB] word5 q = q → q = 4 ∨ q = 18 := by
  decide +kernel

open CFSG.Quasithin.B45Mat.M22 in
theorem fix7 : ∀ q : Fin 22, evalCodes [m22gA, m22gB] word7 q = q → q = 21 := by
  decide +kernel

open CFSG.Quasithin.B45Mat.M22 in
theorem fix7i : ∀ q : Fin 22, evalCodes [m22gA, m22gB] (invWord word7) q = q → q = 21 := by
  decide +kernel

open CFSG.Quasithin.B45Mat.M22 in
theorem fix11 : ∀ q : Fin 22, evalCodes [m22gA, m22gB] word11 q ≠ q := by decide +kernel

open CFSG.Quasithin.B45Mat.M22 in
theorem fix11i : ∀ q : Fin 22, evalCodes [m22gA, m22gB] (invWord word11) q ≠ q := by
  decide +kernel

open CFSG.Quasithin.B45Mat.M22 in
theorem liftW_mem_act : ∀ p ∈ [(word3, 5), (word3, 6), (word3, 7), (word3, 11), (word5, 4),
    (word5, 18), (word7, 21), (invWord word7, 21)],
    IsLetters (liftW p.1 p.2) ∧ evalCodes [m22gA, m22gB] (liftW p.1 p.2) 0 = 0 := by
  unfold IsLetters
  decide +kernel

theorem wordΓ_mem_hatH {w : List ℤ} (hw : IsLetters w) (h0 : evalCodes [m22gA, m22gB] w 0 = 0) :
    wordΓ w ∈ hatH := by
  rw [mem_hatH, hatM22Act_wordΓ hw, h0]

open CFSG.Quasithin.B45Mat.M22 in
theorem liftW_mem {r : List ℤ} {q : ℕ} (h : (r, q) ∈ [(word3, 5), (word3, 6), (word3, 7),
    (word3, 11), (word5, 4), (word5, 18), (word7, 21), (invWord word7, 21)]) :
    wordΓ (liftW r q) ∈ hatH :=
  wordΓ_mem_hatH (liftW_mem_act _ h).1 (liftW_mem_act _ h).2

open CFSG.Quasithin.B45Mat.M22 in
@[expose] noncomputable def hRep : Fin 5 → ↥hatH :=
  ![1, ⟨wordΓ (liftW word5 4), liftW_mem (by simp)⟩, ⟨wordΓ (liftW word5 18), liftW_mem (by simp)⟩,
    ⟨wordΓ (liftW word7 21), liftW_mem (by simp)⟩,
    ⟨wordΓ (liftW (invWord word7) 21), liftW_mem (by simp)⟩]

@[expose] def zW : List ℤ := (List.replicate 11 [1, 2]).flatten

@[expose] def fusionW : ℕ → List ℤ
  | 5 => [-1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2,
      -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -1,
      -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2]
  | 6 => [2, 1, 2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 1, -2, -2, -1, 2, -1, -2, -1, -2, -1, -2,
      -2, -2, -1, -2, -2, -2, -1, 2, -1, -2, -2, -1, 2, -1, -2, -2, -1, 2, -1, -2, -2, -1]
  | 7 => [-1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1,
      -2, 1, -2, 1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -2, -1, -2]
  | _ => [-2, -1, 2, -1, -2, -1, 2, -1, -2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2,
      1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1]

theorem gmat_wordΓ_zW : gmat (wordΓ zW) = ω • (1 : Matrix (Fin 6) (Fin 6) FieldFour) := by
  rw [gmat_wordΓ, ← PM.toMat_ofMat (ω • (1 : Matrix (Fin 6) (Fin 6) FieldFour))]
  exact PM.toMat_eq_of_eqm (by decide +kernel)

theorem wordΓ_zW : wordΓ zW = hatM22Z := by
  apply Subtype.ext
  apply Units.ext
  change gmat (wordΓ zW) = _
  rw [gmat_wordΓ_zW, hatM22Z_val]

open CFSG.Quasithin.B45Mat.M22 in
theorem fusion_act : ∀ q ∈ [5, 6, 7, 11], IsLetters (fusionW q) ∧
    evalCodes [m22gA, m22gB] (fusionW q) 0 = 0 ∧
      PM.eqm 6 (pWord (liftW word3 q ++ fusionW q)) (pWord (zW ++ fusionW q ++ liftW word3 q)) =
        true := by
  unfold IsLetters
  decide +kernel

theorem gmat_injective : Function.Injective gmat := fun _ _ h => Subtype.ext (Units.ext h)

open CFSG.Quasithin.B45Mat.M22 in
theorem fusion_liftW3 {q : ℕ} (hq : q ∈ [5, 6, 7, 11]) (hmem : wordΓ (liftW word3 q) ∈ hatH) :
    IsConj (⟨wordΓ (liftW word3 q), hmem⟩ : ↥hatH) (zH * ⟨wordΓ (liftW word3 q), hmem⟩) := by
  obtain ⟨hl, h0, heq⟩ := fusion_act q hq
  have hd : wordΓ (fusionW q) ∈ hatH := wordΓ_mem_hatH hl h0
  have hrel : wordΓ (liftW word3 q) * wordΓ (fusionW q) =
      hatM22Z * wordΓ (fusionW q) * wordΓ (liftW word3 q) := by
    apply gmat_injective
    rw [← wordΓ_append, ← wordΓ_zW, ← wordΓ_append, ← wordΓ_append, gmat_wordΓ, gmat_wordΓ]
    exact PM.toMat_eq_of_eqm heq
  rw [isConj_iff]
  refine ⟨⟨wordΓ (fusionW q), hd⟩⁻¹, ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  change (wordΓ (fusionW q))⁻¹ * wordΓ (liftW word3 q) * wordΓ (fusionW q) =
    hatM22Z * wordΓ (liftW word3 q)
  rw [mul_assoc, hrel, ← Subgroup.mem_center_iff.mp hatM22Z_mem_center (wordΓ (fusionW q))]
  group

theorem zH_mem_center : zH ∈ Subgroup.center ↥hatH := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp hatM22Z_mem_center (g : ↥hatM22Γ₀)

theorem isConj_mul_central {G : Type*} [Group G] {u v c : G} (hc : c ∈ Subgroup.center G)
    (h : IsConj u v) : IsConj (u * c) (v * c) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  rw [isConj_iff]
  refine ⟨g, ?_⟩
  have hgc : g * c * g⁻¹ = c := by
    rw [Subgroup.mem_center_iff.mp hc g]
    group
  calc g * (u * c) * g⁻¹ = (g * u * g⁻¹) * (g * c * g⁻¹) := by group
    _ = v * c := by rw [hg, hgc]

theorem isConj_central_mul {G : Type*} [Group G] {u v c : G} (hc : c ∈ Subgroup.center G)
    (h : IsConj u v) : IsConj (c * u) (c * v) := by
  rw [← Subgroup.mem_center_iff.mp hc u, ← Subgroup.mem_center_iff.mp hc v]
  exact isConj_mul_central hc h

open CFSG.Quasithin.B45Mat.M22 in
theorem hatH_cover
    (h : ↥hatH)
    (hreg : CFSG.IsPRegular 2 h) :
    (∃ j : Fin 5, ∃ e : ℕ, IsConj h (hRep j * zH ^ e)) ∨ IsConj h (zH * h) := by
  have hreg' : CFSG.IsPRegular 2 (hatM22Q (h : ↥hatM22Γ₀)) :=
    CFSG.IsPRegular.map 2 hatM22Q (CFSG.IsPRegular.map 2 hatH.subtype hreg)
  obtain ⟨r, hr, c, hc, hσ⟩ := exists_conj_of_isPRegular _ hreg'
  have hσ' : hatM22Act (h : ↥hatM22Γ₀) = c * r * c⁻¹ := hσ
  have h0 : hatM22Act (h : ↥hatM22Γ₀) 0 = 0 := h.2
  generalize hqdef : c⁻¹ 0 = q
  have hrq : r q = q := by
    have := congrArg (fun σ : Equiv.Perm (Fin 22) => σ 0) hσ'
    simp only [h0, Equiv.Perm.mul_apply] at this
    have h1 : c (r q) = c q := by
      rw [← hqdef, ← this]
      exact (Equiv.apply_symm_apply c 0).symm
    exact c.injective h1
  have key : ∀ (wr : List ℤ) (hwr : IsLetters wr), evalCodes [m22gA, m22gB] wr = r →
      ∀ (hmem : wordΓ (liftW wr q) ∈ hatH),
        ∃ e : ℕ, IsConj h (⟨wordΓ (liftW wr q), hmem⟩ * zH ^ e) :=
    fun wr hwr hrw hmem => exists_conj_liftW hc hσ' hwr hrw hqdef hmem
  have hlet : ∀ w ∈ [word3, word5, word7, invWord word7], IsLetters w := by
    unfold IsLetters
    decide
  simp only [oddReps, oddReps3, oddReps5, oddReps7, oddReps11, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    left
    refine ⟨0, ?_⟩
    have hk : (h : ↥hatM22Γ₀) ∈ hatM22Act.ker := by
      rw [MonoidHom.mem_ker, hσ']
      group
    obtain ⟨e, he⟩ : ∃ e : ℕ, (h : ↥hatM22Γ₀) = hatM22Z ^ e := by
      rcases (mem_ker_hatM22Act_iff _).1 hk with h1 | h1 | h1
      · exact ⟨0, by rw [h1, pow_zero]⟩
      · exact ⟨1, by rw [h1, pow_one]⟩
      · exact ⟨2, h1⟩
    refine ⟨e, ?_⟩
    have : h = hRep 0 * zH ^ e := by
      apply Subtype.ext
      simp only [hRep, Matrix.cons_val_zero, one_mul, Subgroup.coe_pow]
      exact he
    rw [this]
  ·
    right
    have hq3 := fix3 q hrq
    have hqm : q.val ∈ [5, 6, 7, 11] := by
      rcases hq3 with h1 | h1 | h1 | h1 <;> simp [h1]
    have hmem : wordΓ (liftW word3 q) ∈ hatH := liftW_mem (by
      rcases hq3 with h1 | h1 | h1 | h1 <;> simp [h1])
    obtain ⟨e, he⟩ := key word3 (hlet _ (by simp)) rfl hmem
    have hz := Subgroup.pow_mem _ zH_mem_center e
    have h2 : IsConj (⟨wordΓ (liftW word3 q), hmem⟩ * zH ^ e)
        (zH * (⟨wordΓ (liftW word3 q), hmem⟩ * zH ^ e)) := by
      rw [← mul_assoc]
      exact isConj_mul_central hz (fusion_liftW3 hqm hmem)
    exact he.trans (h2.trans (isConj_central_mul zH_mem_center he).symm)
  ·
    left
    rcases fix5 q hrq with h1 | h1 <;> subst h1
    · obtain ⟨e, he⟩ := key word5 (hlet _ (by simp)) rfl (liftW_mem (by simp))
      exact ⟨1, e, he⟩
    · obtain ⟨e, he⟩ := key word5 (hlet _ (by simp)) rfl (liftW_mem (by simp))
      exact ⟨2, e, he⟩
  ·
    left
    have h1 := fix7 q hrq
    subst h1
    obtain ⟨e, he⟩ := key word7 (hlet _ (by simp)) rfl (liftW_mem (by simp))
    exact ⟨3, e, he⟩
  ·
    left
    have h1 := fix7i q hrq
    subst h1
    obtain ⟨e, he⟩ := key (invWord word7) (hlet _ (by simp)) rfl (liftW_mem (by simp))
    exact ⟨4, e, he⟩
  · exact absurd hrq (fix11 q)
  · exact absurd hrq (fix11i q)

end CFSG.Quasithin.HM22

module

public import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockOrth
public import CFSG.OddTranspositions.PartFour.LinePolar
import CFSG.RankThree.OrthogonalInvolutions.Witt
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2

public noncomputable section

namespace CFSG.OddTranspositions.PartFour

open Matrix Module QuadraticMap CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Model

variable {X : Type} [Group X] {K : Type} [Field K] [CharP K 2] {m : ℕ}
  {Q : QuadraticForm K (Fin m → K)}

private theorem polar_self_eq_zero' {V : Type*} [AddCommGroup V] [Module K V]
    (R : QuadraticForm K V) (x : V) : polar R x x = 0 := by
  rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]

omit [CharP K 2] in
private theorem ne_zero_of_map_eq_one' {V : Type*} [AddCommGroup V] [Module K V]
    {R : QuadraticForm K V} {x : V} (hx : R x = 1) : x ≠ 0 := fun h => by
  rw [h, QuadraticMap.map_zero] at hx
  exact zero_ne_one hx

private theorem commute_symmetryGL_iff (hQ : Q.polarBilin.Nondegenerate) {x y : Fin m → K}
    (hx : Q x = 1) (hy : Q y = 1) :
    Commute (symmetryGL Q x) (symmetryGL Q y) ↔ polar Q x y = 0 := by
  have h1 : Commute (symmetryGL Q x) (symmetryGL Q y) ↔
      symmetryGL Q x ∈ Subgroup.centralizer {symmetryGL Q y} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Iff.rfl
  rw [h1, mem_centralizer_symmetryGL_iff hQ hy (symmetryGL_mem Q x),
    symmetryGL_mulVec_of_charTwo hx, add_eq_left, smul_eq_zero]
  simp [ne_zero_of_map_eq_one' hx]

theorem commute_iff_of_symmetryGL (hQ : Q.polarBilin.Nondegenerate)
    {ψ : X →* GL (Fin m) K} (hψ : Function.Injective ψ) {t t' : X} {x y : Fin m → K}
    (hx : Q x = 1) (hy : Q y = 1) (ht : ψ t = symmetryGL Q x) (ht' : ψ t' = symmetryGL Q y) :
    Commute t t' ↔ polar Q x y = 0 := by
  rw [← commute_symmetryGL_iff hQ hx hy, ← ht, ← ht']
  exact ⟨fun h => h.map ψ, fun h => hψ (by rw [map_mul, map_mul]; exact h.eq)⟩

omit [CharP K 2] in
theorem exists_vec_of_isConj {ψ : X →* GL (Fin m) K}
    (hrange : ψ.range = matrixIsometries Q) {s : X} {v : Fin m → K} (hv : Q v = 1)
    (hψs : ψ s = symmetryGL Q v) {t : X} (ht : IsConj s t) :
    ∃ x, Q x = 1 ∧ ψ t = symmetryGL Q x := by
  have hψmem : ∀ g, ψ g ∈ matrixIsometries Q := fun g => hrange ▸ ⟨g, rfl⟩
  obtain ⟨c, rfl⟩ := isConj_iff.mp ht
  refine ⟨(ψ c : Matrix (Fin m) (Fin m) K) *ᵥ v, ?_, ?_⟩
  · rw [← hv]
    exact (mem_matrixIsometries_iff Q _).mp (hψmem c) v
  · rw [map_mul, map_mul, map_inv, hψs, conj_symmetryGL (hψmem c)]

private theorem exists_eq_of_perp_pair [Finite K] (hQ : Q.polarBilin.Nondegenerate)
    {b c x : Fin m → K} (hb : Q b = 1) (hc : Q c = 1) (hbc : polar Q b c = 0) (hx : Q x = 1)
    (h : ∀ w, Q w = 1 → polar Q w b = 0 → polar Q w c = 0 → polar Q x w = 0) :
    ∃ α : K, x = α • b + (1 + α) • c := by
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb := polar_self_eq_zero' Q b
  have hall : ∀ w, polar Q w b = 0 → polar Q w c = 0 → polar Q x w = 0 := by
    intro w hwb hwc
    by_cases hw0 : Q w = 0
    · have h1 := h (w + b) (by rw [QuadraticMap.map_add Q w b, hw0, hb, hwb]; ring)
        (by rw [polar_add_left, hwb, hbb, add_zero])
        (by rw [polar_add_left, hwc, hbc, add_zero])
      have h2 := h b hb hbb (polar_comm Q c b ▸ hbc)
      rw [polar_add_right] at h1
      linear_combination h1 - h2
    · obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q w)
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        exact hw0 (by rw [hμ]; ring)
      have h1 := h (μ⁻¹ • w)
        (by rw [QuadraticMap.map_smul, smul_eq_mul, hμ]; field_simp)
        (by rw [polar_smul_left, hwb, smul_zero]) (by rw [polar_smul_left, hwc, smul_zero])
      rw [polar_smul_right, smul_eq_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_left (inv_ne_zero hμ0)
  obtain ⟨α, β, hαβ⟩ := exists_eq_smul_add_smul_of_forall_polar_eq_zero hQ hall
  have hQx : α * α + β * β = 1 := by
    rw [hαβ, QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul,
      polar_smul_left, polar_smul_right, hb, hc, hbc] at hx
    simpa [smul_eq_mul] using hx
  have hβ : β = 1 + α := by
    have h3 : (α + β + 1) * (α + β + 1) = 0 := by
      linear_combination hQx + (1 + α * β + α + β) * h22
    have h4 := mul_self_eq_zero.mp h3
    linear_combination h4 - (α + 1) * h22
  exact ⟨α, by rw [hαβ, hβ]⟩

end Model

theorem exists_lineMem_ncard_le_of_isOrthReflection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ}
    (hs : CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection X m f s) :
    ∃ v ∈ {x | IsConj s x}, ∃ w ∈ {x | IsConj s x}, Commute v w ∧
      perpMem {x | IsConj s x} v ≠ perpMem {x | IsConj s x} w ∧
      (perpMem {x | IsConj s x} '' lineMem {x | IsConj s x} v w).ncard ≤ 2 ^ f := by
  classical
  have hm := four_le_of_isOrthReflection hs
  obtain ⟨K, _, _, _, Q, ψ, b, hcard, hQ, hψ, hrange, hb, hψs, hrefl⟩ :=
    exists_symmetry_model_of_isOrthReflection hZ hs
  set E : Set X := {x | IsConj s x} with hE
  have hdim : 3 ≤ finrank K (Fin m → K) := by
    rw [Module.finrank_fin_fun]
    omega
  have hb0 := ne_zero_of_map_eq_one' hb
  obtain ⟨z, hbz⟩ : ∃ z, polar Q b z ≠ 0 := by
    by_contra! h0
    exact hb0 (hQ.1 b fun y => by rw [QuadraticMap.polarBilin_apply_apply]; exact h0 y)
  obtain ⟨c, hcb, hcz, hc⟩ := exists_polar_eq_map_eq_of_polar_ne_zero hQ hdim hbz 0
    (polar Q b z + 1) 1
  have hne : c ≠ b := by
    intro h
    rw [h] at hcz
    exact one_ne_zero (by linear_combination -hcz)
  have hbc : polar Q b c = 0 := by rw [polar_comm]; exact hcb
  have hind : LinearIndependent K ![b, c] :=
    linearIndependent_pair_of_map_eq_one hb hc (Ne.symm hne)
  obtain ⟨y, hyb, hyc, hy⟩ := exists_polar_eq_map_eq_of_polar_eq_zero hQ hind hbc
    (hb.trans hc.symm) zero_ne_one 1
  obtain ⟨w, hwconj, hψw⟩ := hrefl c hc
  obtain ⟨u, huconj, hψu⟩ := hrefl y hy
  have hcomm : ∀ {t t' : X} {x y : Fin m → K}, Q x = 1 → Q y = 1 → ψ t = symmetryGL Q x →
      ψ t' = symmetryGL Q y → (Commute t t' ↔ polar Q x y = 0) := fun hx hy ht ht' =>
    commute_iff_of_symmetryGL hQ hψ hx hy ht ht'
  refine ⟨s, IsConj.refl s, w, hwconj, (hcomm hb hc hψs hψw).mpr hbc, ?_, ?_⟩
  ·
    intro hEq
    have hus : u ∈ perpMem E s := ⟨huconj, (hcomm hy hb hψu hψs).mpr hyb⟩
    have huw : Commute u w := by
      have : u ∈ perpMem E w := hEq ▸ hus
      exact this.2
    have := (hcomm hy hc hψu hψw).mp huw
    rw [hyc] at this
    exact one_ne_zero this
  ·
    set ι : K → Fin m → K := fun α => α • b + (1 + α) • c with hι
    have hsub : ∀ t ∈ lineMem E s w, ∃ α, ψ t = symmetryGL Q (ι α) := by
      intro t ht
      obtain ⟨htE, hperp⟩ := ht
      obtain ⟨x, hx, hψt⟩ := exists_vec_of_isConj hrange hb hψs htE
      obtain ⟨α, hα⟩ := exists_eq_of_perp_pair hQ hb hc hbc hx fun w' hw'1 hw'b hw'c => by
        obtain ⟨u', hu'conj, hψu'⟩ := hrefl w' hw'1
        have hu's : u' ∈ perpMem E s := ⟨hu'conj, (hcomm hw'1 hb hψu' hψs).mpr hw'b⟩
        have hu'w : u' ∈ perpMem E w := ⟨hu'conj, (hcomm hw'1 hc hψu' hψw).mpr hw'c⟩
        have hu't : Commute u' t := (hperp ⟨hu's, hu'w⟩).2
        rw [polar_comm]
        exact (hcomm hw'1 hx hψu' hψt).mp hu't
      exact ⟨α, by rw [hψt, hα]⟩
    have hfin : (ψ '' lineMem E s w).Finite := by
      refine (Set.finite_range fun α : K => symmetryGL Q (ι α)).subset ?_
      rintro _ ⟨t, ht, rfl⟩
      obtain ⟨α, hα⟩ := hsub t ht
      exact ⟨α, hα.symm⟩
    have hfin' : (lineMem E s w).Finite := Set.Finite.of_finite_image hfin hψ.injOn
    calc (perpMem E '' lineMem E s w).ncard ≤ (lineMem E s w).ncard := Set.ncard_image_le hfin'
      _ ≤ (Set.range fun α : K => symmetryGL Q (ι α)).ncard :=
          Set.ncard_le_ncard_of_injOn ψ (fun t ht => by
            obtain ⟨α, hα⟩ := hsub t ht
            exact ⟨α, hα.symm⟩) hψ.injOn (Set.finite_range _)
      _ = ((fun α : K => symmetryGL Q (ι α)) '' Set.univ).ncard := by rw [Set.image_univ]
      _ ≤ (Set.univ : Set K).ncard := Set.ncard_image_le Set.finite_univ
      _ = 2 ^ f := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]

section Triple

variable {K : Type} [Field K] [CharP K 2] {m : ℕ} {Q : QuadraticForm K (Fin m → K)}

structure IsTriple (Q : QuadraticForm K (Fin m → K)) (v w₁ w₂ : Fin m → K) : Prop where
  q_v : Q v = 1
  q_w₁ : Q w₁ = 0
  q_w₂ : Q w₂ = 0
  v_w₁ : polar Q v w₁ = 0
  v_w₂ : polar Q v w₂ = 0
  w₁_w₂ : polar Q w₁ w₂ = 1

theorem exists_isTriple [Finite K] (hQ : Q.polarBilin.Nondegenerate) (hm : 4 ≤ m)
    {v : Fin m → K} (hv : Q v = 1) : ∃ w₁ w₂ : Fin m → K, IsTriple Q v w₁ w₂ := by
  have hdim : 3 ≤ finrank K (Fin m → K) := by
    rw [Module.finrank_fin_fun]
    omega
  have hv0 := ne_zero_of_map_eq_one' hv
  obtain ⟨z, hvz⟩ : ∃ z, polar Q v z ≠ 0 := by
    by_contra! h0
    exact hv0 (hQ.1 v fun y => by rw [QuadraticMap.polarBilin_apply_apply]; exact h0 y)
  obtain ⟨c, hcv, hcz, hc⟩ := exists_polar_eq_map_eq_of_polar_ne_zero hQ hdim hvz 0
    (polar Q v z + 1) 1
  have hne : c ≠ v := by
    intro h
    rw [h] at hcz
    exact one_ne_zero (by linear_combination -hcz)
  have hvc : polar Q v c = 0 := by rw [polar_comm]; exact hcv
  have hvv := polar_self_eq_zero' Q v
  have hQw₁ : Q (v + c) = 0 := by
    rw [QuadraticMap.map_add Q v c, hv, hc, hvc, ← two_mul,
      show (2 : K) = 0 from CharTwo.two_eq_zero, zero_mul, add_zero]
  have hvw₁ : polar Q v (v + c) = 0 := by rw [polar_add_right, hvv, hvc, add_zero]
  have hind : LinearIndependent K ![v, v + c] := by
    rw [LinearIndependent.pair_iff' hv0]
    intro a ha
    have h1 : Q (a • v) = 0 := by rw [ha]; exact hQw₁
    rw [QuadraticMap.map_smul, hv, smul_eq_mul, mul_one] at h1
    have ha0 : a = 0 := mul_self_eq_zero.mp h1
    rw [ha0, zero_smul] at ha
    have h2 : v + c = 0 := ha.symm
    have hvv2 : v + v = 0 := by
      rw [← two_smul K v, show (2 : K) = 0 from CharTwo.two_eq_zero, zero_smul]
    exact hne (by
      have h3 : c = -v := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact h2
      rw [h3]
      exact neg_eq_of_add_eq_zero_right hvv2)
  obtain ⟨z₂, hz₂v, hz₂w⟩ := exists_polar_eq_pair_of_linearIndependent hQ hind 0 1
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q z₂)
  refine ⟨v + c, z₂ + μ • v, ⟨hv, hQw₁, ?_, hvw₁, ?_, ?_⟩⟩
  · rw [QuadraticMap.map_add Q z₂ (μ • v), QuadraticMap.map_smul, hv, polar_smul_right, hz₂v,
      smul_eq_mul, smul_eq_mul, mul_zero, mul_one, ← hμ, ← two_mul,
      show (2 : K) = 0 from CharTwo.two_eq_zero, zero_mul, add_zero]
  · rw [polar_add_right, polar_smul_right, polar_comm Q v z₂, hz₂v, hvv, smul_eq_mul, mul_zero,
      add_zero]
  · rw [polar_add_right, polar_smul_right, polar_comm Q (v + c) z₂, hz₂w, polar_comm Q (v + c) v,
      hvw₁, smul_eq_mul, mul_zero, add_zero]

end Triple

section Coord

variable {K : Type} [Field K] [CharP K 2] {m : ℕ} {Q : QuadraticForm K (Fin m → K)}
  {v w₁ w₂ : Fin m → K}

private def theta (v w₁ w₂ : Fin m → K) (t : K × K × K) : Fin m → K :=
  t.1 • v + t.2.1 • w₁ + t.2.2 • w₂

private def bil (t t' : K × K × K) : K := t.2.1 * t'.2.2 + t.2.2 * t'.2.1

private def refl3 (t t' : K × K × K) : K × K × K :=
  (t'.1 + bil t t' * t.1, t'.2.1 + bil t t' * t.2.1, t'.2.2 + bil t t' * t.2.2)

private abbrev TT : Set (K × K × K) :=
  {t | t.1 * t.1 + t.2.1 * t.2.2 = 1 ∧ (t.2.1 ≠ 0 ∨ t.2.2 ≠ 0)}

omit [CharP K 2] in
private theorem theta_refl3 (t t' : K × K × K) :
    theta v w₁ w₂ (refl3 t t') = theta v w₁ w₂ t' + bil t t' • theta v w₁ w₂ t := by
  simp only [theta, refl3, add_smul, mul_smul, smul_add]
  abel

omit [CharP K 2] in
private theorem map_theta (hT : IsTriple Q v w₁ w₂) (t : K × K × K) :
    Q (theta v w₁ w₂ t) = t.1 * t.1 + t.2.1 * t.2.2 := by
  rw [theta, CFSG.RankThree.OrthogonalInvolutions.map_add_smul_add_smul, QuadraticMap.map_smul,
    polar_smul_left, polar_smul_left, hT.q_v, hT.q_w₁, hT.q_w₂, hT.v_w₁, hT.v_w₂, hT.w₁_w₂]
  simp only [smul_eq_mul]
  ring

private theorem polar_theta (hT : IsTriple Q v w₁ w₂) (t t' : K × K × K) :
    polar Q (theta v w₁ w₂ t) (theta v w₁ w₂ t') = bil t t' := by
  have h11 : polar Q w₁ w₁ = 0 := polar_self_eq_zero' Q w₁
  have h22 : polar Q w₂ w₂ = 0 := polar_self_eq_zero' Q w₂
  have hvv : polar Q v v = 0 := polar_self_eq_zero' Q v
  have h21 : polar Q w₂ w₁ = 1 := by rw [polar_comm]; exact hT.w₁_w₂
  have h1v : polar Q w₁ v = 0 := by rw [polar_comm]; exact hT.v_w₁
  have h2v : polar Q w₂ v = 0 := by rw [polar_comm]; exact hT.v_w₂
  simp only [theta, bil, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
    smul_eq_mul, hvv, h11, h22, h21, h1v, h2v, hT.v_w₁, hT.v_w₂, hT.w₁_w₂]
  ring

private theorem symmetryGL_mulVec_theta (hT : IsTriple Q v w₁ w₂) {t : K × K × K}
    (ht : t.1 * t.1 + t.2.1 * t.2.2 = 1) (t' : K × K × K) :
    (symmetryGL Q (theta v w₁ w₂ t) : Matrix (Fin m) (Fin m) K) *ᵥ theta v w₁ w₂ t' =
      theta v w₁ w₂ (refl3 t t') := by
  rw [symmetryGL_mulVec_of_charTwo (by rw [map_theta hT]; exact ht), polar_theta hT,
    theta_refl3]

end Coord

section Algebra

variable {K : Type} [Field K] [CharP K 2]

private theorem refl3_mem {t t' : K × K × K} (ht : t ∈ TT) (ht' : t' ∈ TT) : refl3 t t' ∈ TT := by
  obtain ⟨l, a, b⟩ := t
  obtain ⟨l', a', b'⟩ := t'
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨h1, -⟩ := ht
  obtain ⟨h1', h2'⟩ := ht'
  simp only [TT, refl3, bil, Set.mem_setOf_eq] at h1 h1' h2' ⊢
  refine ⟨?_, ?_⟩
  · linear_combination h1' + (a * b' + b * a') ^ 2 * h1 +
      ((a * b' + b * a') ^ 2 + (a * b' + b * a') * l * l') * h22
  · by_contra hcon
    push Not at hcon
    obtain ⟨hh1, hh2⟩ := hcon
    have hB : a * b' + b * a' = 0 := by
      linear_combination a * hh2 + b * hh1 - ((a * b' + b * a') * a * b) * h22
    rw [hB, zero_mul, add_zero] at hh1 hh2
    exact h2'.elim (fun h => h hh1) (fun h => h hh2)

private theorem eq_of_snd_eq {t t' : K × K × K} (ht : t ∈ TT) (ht' : t' ∈ TT) (h : t.2 = t'.2) :
    t = t' := by
  obtain ⟨l, a, b⟩ := t
  obtain ⟨l', a', b'⟩ := t'
  obtain ⟨h1, -⟩ := ht
  obtain ⟨h1', -⟩ := ht'
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have : l ^ 2 = l' ^ 2 := by
    simp only at h1 h1'
    linear_combination h1 - h1'
  have hl : l = l' := CharTwo.sq_inj.mp this
  rw [hl]

private theorem exists_refl3_eq [Finite K] {t t' : K × K × K} (ht : t ∈ TT) (ht' : t' ∈ TT)
    (hB : bil t t' ≠ 0) : ∃ c ∈ TT, refl3 c t = t' := by
  obtain ⟨l, a, b⟩ := t
  obtain ⟨l', a', b'⟩ := t'
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨h1, -⟩ := ht
  obtain ⟨h1', -⟩ := ht'
  simp only [bil] at h1 h1' hB
  obtain ⟨κ, hκ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (a * b' + b * a')⁻¹
  have hκB : κ * κ * (a * b' + b * a') = 1 := by
    rw [← hκ]
    exact inv_mul_cancel₀ hB
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_mul] at hκB
    exact zero_ne_one hκB
  refine ⟨(κ * (l + l'), κ * (a + a'), κ * (b + b')), ⟨?_, ?_⟩, ?_⟩
  · simp only
    linear_combination hκB + κ ^ 2 * h1 + κ ^ 2 * h1' + κ ^ 2 * (1 + l * l') * h22
  · simp only
    by_contra hcon
    push Not at hcon
    obtain ⟨hh1, hh2⟩ := hcon
    have ha : a + a' = 0 := (mul_eq_zero.mp hh1).resolve_left hκ0
    have hb : b + b' = 0 := (mul_eq_zero.mp hh2).resolve_left hκ0
    apply hB
    have ha' : a' = a := (CharTwo.add_eq_zero.mp ha).symm
    have hb' : b' = b := (CharTwo.add_eq_zero.mp hb).symm
    rw [ha', hb']
    linear_combination (a * b) * h22
  · simp only [refl3, bil]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only
      linear_combination (l + l') * hκB + (l + κ ^ 2 * a * b * (l + l')) * h22
    · simp only
      linear_combination (a + a') * hκB + (a + κ ^ 2 * a * b * (a + a')) * h22
    · simp only
      linear_combination (b + b') * hκB + (b + κ ^ 2 * a * b * (b + b')) * h22

private theorem exists_refl3_eq_or [Finite K] {t t' : K × K × K} (ht : t ∈ TT) (ht' : t' ∈ TT) :
    (∃ c ∈ TT, refl3 c t = t') ∨ ∃ c₁ ∈ TT, ∃ c₂ ∈ TT, refl3 c₂ (refl3 c₁ t) = t' := by
  by_cases hB : bil t t' = 0
  · right
    have hz₁ : ((1 : K), (1 : K), (0 : K)) ∈ TT := ⟨by simp, Or.inl one_ne_zero⟩
    have hz₂ : ((1 : K), (0 : K), (1 : K)) ∈ TT := ⟨by simp, Or.inr one_ne_zero⟩
    obtain ⟨l, a, b⟩ := t
    obtain ⟨l', a', b'⟩ := t'
    have hmain : (b ≠ 0 ∧ b' ≠ 0) ∨ (a ≠ 0 ∧ a' ≠ 0) := by
      have hB' : a * b' + b * a' = 0 := hB
      obtain ⟨-, h2⟩ := ht
      obtain ⟨-, h2'⟩ := ht'
      simp only at h2 h2'
      by_contra hnot
      push Not at hnot
      rcases h2 with ha | hb
      · have ha' : a' = 0 := hnot.2 ha
        rw [ha', mul_zero, add_zero] at hB'
        have hb' : b' = 0 := (mul_eq_zero.mp hB').resolve_left ha
        exact h2'.elim (fun h => h ha') (fun h => h hb')
      · by_cases ha0 : a = 0
        · have hb' : b' = 0 := hnot.1 hb
          rw [ha0, zero_mul, zero_add] at hB'
          have ha' : a' = 0 := (mul_eq_zero.mp hB').resolve_left hb
          exact h2'.elim (fun h => h ha') (fun h => h hb')
        · have ha' : a' = 0 := hnot.2 ha0
          rw [ha', mul_zero, add_zero] at hB'
          have hb' : b' = 0 := (mul_eq_zero.mp hB').resolve_left ha0
          exact h2'.elim (fun h => h ha') (fun h => h hb')
    rcases hmain with ⟨hb, hb'⟩ | ⟨ha, ha'⟩
    · obtain ⟨c₁, hc₁, h₁⟩ := exists_refl3_eq ht hz₁ (by simpa [bil] using hb)
      obtain ⟨c₂, hc₂, h₂⟩ := exists_refl3_eq hz₁ ht' (by simpa [bil] using hb')
      exact ⟨c₁, hc₁, c₂, hc₂, by rw [h₁, h₂]⟩
    · obtain ⟨c₁, hc₁, h₁⟩ := exists_refl3_eq ht hz₂ (by simpa [bil] using ha)
      obtain ⟨c₂, hc₂, h₂⟩ := exists_refl3_eq hz₂ ht' (by simpa [bil] using ha')
      exact ⟨c₁, hc₁, c₂, hc₂, by rw [h₁, h₂]⟩
  · left
    exact exists_refl3_eq ht ht' hB

end Algebra

section Reach

variable {K : Type} [Field K] [CharP K 2]

private def unu (t : K × K × K) (ν : K) : K × K × K := ((1 + ν) + ν * t.1, ν * t.2.1, ν * t.2.2)

private theorem unu_mem {a : K × K × K} (ha : a ∈ TT) {ν : K} (hν : ν ≠ 0) : unu a ν ∈ TT := by
  obtain ⟨l, α, β⟩ := a
  obtain ⟨h1, h2⟩ := ha
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [TT, unu, Set.mem_setOf_eq] at h1 h2 ⊢
  refine ⟨?_, ?_⟩
  · linear_combination ν ^ 2 * h1 + (ν + ν ^ 2 + (1 + ν) * ν * l) * h22
  · exact h2.imp (mul_ne_zero hν ·) (mul_ne_zero hν ·)

private theorem bil_unu_self (a : K × K × K) (ν : K) : bil (unu a ν) a = 0 := by
  obtain ⟨l, α, β⟩ := a
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [bil, unu]
  linear_combination (ν * α * β) * h22

private theorem mem_of_closed [Finite K] {a b : K × K × K} (ha : a ∈ TT) (hb : b ∈ TT)
    (hγ : bil a b ≠ 0) {D : Set (K × K × K)} (hD1 : ∀ ν : K, ν ≠ 0 → unu a ν ∈ D) (hD2 : b ∈ D)
    (hD3 : ∀ c ∈ D, ∀ c' ∈ D, refl3 c c' ∈ D) : ∀ u ∈ TT, u ∈ D := by
  intro u hu
  obtain ⟨la, p, q⟩ := a
  obtain ⟨lb, r, s⟩ := b
  obtain ⟨l, x, y⟩ := u
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hγ' : p * s + q * r ≠ 0 := hγ
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ * (p * s + q * r) = x * s + y * r :=
    ⟨(x * s + y * r) / (p * s + q * r), div_mul_cancel₀ _ hγ'⟩
  obtain ⟨η, hη⟩ : ∃ η, η * (p * s + q * r) = x * q + y * p :=
    ⟨(x * q + y * p) / (p * s + q * r), div_mul_cancel₀ _ hγ'⟩
  by_cases hη0 : η = 0
  ·
    have hA : x * q + y * p = 0 := by rw [← hη, hη0, zero_mul]
    have h₁ : ξ * p = x := by
      have h := (mul_eq_zero.mp (show (p * s + q * r) * (ξ * p - x) = 0 by
        linear_combination p * hξ + r * hA - (r * x * q) * h22)).resolve_left hγ'
      linear_combination h
    have h₂ : ξ * q = y := by
      have h := (mul_eq_zero.mp (show (p * s + q * r) * (ξ * q - y) = 0 by
        linear_combination q * hξ + s * hA - (s * y * p) * h22)).resolve_left hγ'
      linear_combination h
    have hξ0 : ξ ≠ 0 := by
      rintro rfl
      rw [zero_mul] at h₁ h₂
      exact hu.2.elim (fun h => h h₁.symm) (fun h => h h₂.symm)
    have hmem : unu (la, p, q) ξ ∈ TT := unu_mem ha hξ0
    have heq := eq_of_snd_eq hmem hu (by
      show (ξ * p, ξ * q) = (x, y)
      rw [h₁, h₂])
    rw [← heq]
    exact hD1 ξ hξ0
  ·
    obtain ⟨ν, hνγ⟩ : ∃ ν, ν * (p * s + q * r) = η :=
      ⟨η / (p * s + q * r), div_mul_cancel₀ _ hγ'⟩
    have hν0 : ν ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hνγ
      exact hη0 hνγ.symm
    obtain ⟨κ, hκ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (ξ / ν + 1)
    have hξν : ν * (κ * κ + 1) = ξ := by
      rw [← hκ]
      have h : ν * (ξ / ν) = ξ := by field_simp
      linear_combination h + ν * h22
    obtain ⟨ν', hν'γ⟩ : ∃ ν', ν' * (p * s + q * r) = κ :=
      ⟨κ / (p * s + q * r), div_mul_cancel₀ _ hγ'⟩
    have hu₁ : unu (la, p, q) ν ∈ D := hD1 ν hν0
    have hu₂ : refl3 (lb, r, s) (unu (la, p, q) ν) ∈ D := hD3 _ hD2 _ hu₁
    have hu₂TT : refl3 (lb, r, s) (unu (la, p, q) ν) ∈ TT := refl3_mem hb (unu_mem ha hν0)
    have hu₃ : refl3 (unu (la, p, q) ν') (refl3 (lb, r, s) (unu (la, p, q) ν)) ∈ D ∧
        refl3 (unu (la, p, q) ν') (refl3 (lb, r, s) (unu (la, p, q) ν)) ∈ TT := by
      by_cases hν'0 : ν' = 0
      · have h : refl3 (unu (la, p, q) ν') (refl3 (lb, r, s) (unu (la, p, q) ν)) =
            refl3 (lb, r, s) (unu (la, p, q) ν) := by
          simp [refl3, bil, unu, hν'0]
        rw [h]
        exact ⟨hu₂, hu₂TT⟩
      · exact ⟨hD3 _ (hD1 ν' hν'0) _ hu₂, refl3_mem (unu_mem ha hν'0) hu₂TT⟩
    have hx₃ : (refl3 (unu (la, p, q) ν') (refl3 (lb, r, s) (unu (la, p, q) ν))).2.1 = x := by
      have e1 : (refl3 (unu (la, p, q) ν') (refl3 (lb, r, s) (unu (la, p, q) ν))).2.1 =
          ξ * p + η * r := by
        simp only [refl3, bil, unu]
        linear_combination p * hξν + p * ν * (ν' * (p * s + q * r) + κ) * hν'γ + r * hνγ +
          (ν' ^ 2 * ν * p ^ 2 * q) * h22
      rw [e1]
      have h := (mul_eq_zero.mp (show (p * s + q * r) * (ξ * p + η * r - x) = 0 by
        linear_combination p * hξ + r * hη + (p * y * r) * h22)).resolve_left hγ'
      linear_combination h
    have hy₃ : (refl3 (unu (la, p, q) ν') (refl3 (lb, r, s) (unu (la, p, q) ν))).2.2 = y := by
      have e1 : (refl3 (unu (la, p, q) ν') (refl3 (lb, r, s) (unu (la, p, q) ν))).2.2 =
          ξ * q + η * s := by
        simp only [refl3, bil, unu]
        linear_combination q * hξν + q * ν * (ν' * (p * s + q * r) + κ) * hν'γ + s * hνγ +
          (ν' ^ 2 * ν * q ^ 2 * p) * h22
      rw [e1]
      have h := (mul_eq_zero.mp (show (p * s + q * r) * (ξ * q + η * s - y) = 0 by
        linear_combination q * hξ + s * hη + (q * x * s) * h22)).resolve_left hγ'
      linear_combination h
    have heq := eq_of_snd_eq hu hu₃.2 (Prod.ext hx₃.symm hy₃.symm)
    rw [heq]
    exact hu₃.1

end Reach

section TwoByTwo

variable {K : Type} [Field K]

private def powCoeff (τ : K) : ℕ → K × K
  | 0 => (0, 1)
  | n + 1 => (τ * (powCoeff τ n).1 + (powCoeff τ n).2, -(powCoeff τ n).1)

private theorem pow_eq_powCoeff {M : Matrix (Fin 2) (Fin 2) K} {τ : K}
    (hM : M ^ 2 = τ • M - 1) (n : ℕ) :
    M ^ n = (powCoeff τ n).1 • M + (powCoeff τ n).2 • (1 : Matrix (Fin 2) (Fin 2) K) := by
  induction n with
  | zero => simp [powCoeff]
  | succ n ih =>
    rw [pow_succ, ih]
    simp only [powCoeff, add_mul, smul_mul_assoc, one_mul]
    rw [← _root_.sq, hM]
    simp only [smul_sub, smul_smul, add_smul, neg_smul]
    rw [mul_comm (powCoeff τ n).1 τ]
    abel

private theorem pow_eq_one_iff_powCoeff {M : Matrix (Fin 2) (Fin 2) K} {τ : K}
    (hM : M ^ 2 = τ • M - 1) (hns : ∀ c : K, M ≠ c • 1) (n : ℕ) :
    M ^ n = 1 ↔ (powCoeff τ n).1 = 0 ∧ (powCoeff τ n).2 = 1 := by
  rw [pow_eq_powCoeff hM n]
  generalize (powCoeff τ n).1 = α
  generalize (powCoeff τ n).2 = β
  constructor
  · intro h
    by_cases hα : α = 0
    · subst hα
      refine ⟨rfl, ?_⟩
      have h00 := congrFun (congrFun h 0) 0
      simpa using h00
    · exfalso
      refine hns (α⁻¹ * (1 - β)) ?_
      have h' : α • M = (1 - β) • (1 : Matrix (Fin 2) (Fin 2) K) := by
        rw [sub_smul, one_smul, eq_sub_iff_add_eq]
        exact h
      calc M = α⁻¹ • (α • M) := by rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
        _ = α⁻¹ • ((1 - β) • (1 : Matrix (Fin 2) (Fin 2) K)) := by rw [h']
        _ = (α⁻¹ * (1 - β)) • 1 := by rw [smul_smul]
  · rintro ⟨rfl, rfl⟩
    simp

variable [CharP K 2]

def planeMat (γ : K) : Matrix (Fin 2) (Fin 2) K := !![1 + γ ^ 2, γ; γ, 1]

private theorem planeMat_sq (γ : K) : planeMat γ ^ 2 = γ ^ 2 • planeMat γ - 1 := by
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeMat, _root_.sq, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (1 + γ * γ) * h22
  · linear_combination γ * h22
  · linear_combination γ * h22
  · linear_combination h22

omit [CharP K 2] in
private theorem planeMat_ne_smul {γ : K} (hγ : γ ≠ 0) (c : K) : planeMat γ ≠ c • 1 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [planeMat] at h01
  exact hγ h01

theorem exists_planeMat_orderOf [Finite K] :
    ∃ γ : K, γ ≠ 0 ∧ orderOf (planeMat γ) = Nat.card K + 1 := by
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨A, hA⟩ := CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := K)
  obtain ⟨τ, hτ⟩ : ∃ τ : K, τ = Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) := ⟨_, rfl⟩
  have hMsq : (A : Matrix (Fin 2) (Fin 2) K) ^ 2 = τ • (A : Matrix (Fin 2) (Fin 2) K) - 1 := by
    have := CFSG.SeitzReduction.F4Pilot.sq_eq_trace_smul_sub_one A
    rw [Matrix.SpecialLinearGroup.coe_pow] at this
    rw [hτ]
    exact this
  have hτ0 : τ ≠ 0 := by
    intro h0
    have hA2 : A ^ 2 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hMsq, h0,
        zero_smul, zero_sub]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]
    have h2 := orderOf_dvd_of_pow_eq_one hA2
    rw [hA] at h2
    have h3 := CFSG.SeitzReduction.F4Pilot.three_le_natCard_add_one (K := K)
    have h4 := Nat.le_of_dvd two_pos h2
    omega
  obtain ⟨γ, hγ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) τ
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    apply hτ0
    rw [hγ]
    ring
  refine ⟨γ, hγ0, ?_⟩
  rw [← hA]
  refine orderOf_eq_orderOf_iff.2 fun n => ?_
  have hns : ∀ c : K, (A : Matrix (Fin 2) (Fin 2) K) ≠ c • 1 := by
    intro c hc
    apply hτ0
    rw [hτ, hc]
    simp
    exact Or.inr h22
  have hN : planeMat γ ^ 2 = τ • planeMat γ - 1 := by rw [planeMat_sq, hγ, _root_.sq]
  rw [pow_eq_one_iff_powCoeff hN (planeMat_ne_smul hγ0) n,
    ← pow_eq_one_iff_powCoeff hMsq hns n, ← Matrix.SpecialLinearGroup.coe_pow,
    ← Matrix.SpecialLinearGroup.coe_one]
  exact Subtype.coe_inj

end TwoByTwo

section Order

variable {K : Type} [Field K] [CharP K 2] {m : ℕ} {Q : QuadraticForm K (Fin m → K)}

private theorem mulVec_symmetryGL_mul {a b : Fin m → K} (ha : Q a = 1) (hb : Q b = 1) {γ : K}
    (hab : polar Q a b = γ) (z : Fin m → K) :
    ((symmetryGL Q a * symmetryGL Q b : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ z =
      z + polar Q b z • b + (polar Q a z + polar Q b z * γ) • a := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, symmetryGL_mulVec_of_charTwo hb,
    symmetryGL_mulVec_of_charTwo ha, polar_add_right, polar_smul_right, hab, smul_eq_mul]

theorem pow_symmetryGL_mul_eq_one_iff {a b : Fin m → K} (ha : Q a = 1) (hb : Q b = 1)
    {γ : K} (hγ : γ ≠ 0) (hab : polar Q a b = γ) (n : ℕ) :
    (symmetryGL Q a * symmetryGL Q b) ^ n = 1 ↔ planeMat γ ^ n = 1 := by
  have haa := polar_self_eq_zero' Q a
  have hbb := polar_self_eq_zero' Q b
  have hba : polar Q b a = γ := by rw [polar_comm]; exact hab
  have hTz := mulVec_symmetryGL_mul ha hb hab
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin m) (Fin m) K,
      T = ((symmetryGL Q a * symmetryGL Q b : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) :=
    ⟨_, rfl⟩
  rw [← hT] at hTz
  let lam : (Fin 2 → K) → Fin m → K := fun c => c 0 • a + c 1 • b
  let phi : (Fin m → K) → Fin 2 → K := fun z => ![γ⁻¹ * polar Q b z, γ⁻¹ * polar Q a z]
  have hphilam : ∀ c, phi (lam c) = c := by
    intro c
    ext i
    fin_cases i
    · simp only [phi, lam, polar_add_right, polar_smul_right, hba, hbb, smul_eq_mul]
      simp
      field_simp
    · simp only [phi, lam, polar_add_right, polar_smul_right, hab, haa, smul_eq_mul]
      simp
      field_simp
  have hTlam : ∀ c, T *ᵥ lam c = lam (planeMat γ *ᵥ c) := by
    intro c
    rw [hTz]
    simp only [lam, planeMat, polar_add_right, polar_smul_right, hba, hbb, hab, haa, smul_eq_mul]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    module
  have hphisub : ∀ z w, phi (z - w) = phi z - phi w := by
    intro z w
    ext i
    fin_cases i <;> simp [phi, polar_sub_right, mul_sub]
  have hfix : ∀ z, phi z = 0 → T *ᵥ z = z := by
    intro z hz
    have h0 : γ⁻¹ * polar Q b z = 0 := by simpa [phi] using congrFun hz 0
    have h1 : γ⁻¹ * polar Q a z = 0 := by simpa [phi] using congrFun hz 1
    have h0' : polar Q b z = 0 := (mul_eq_zero.mp h0).resolve_left (inv_ne_zero hγ)
    have h1' : polar Q a z = 0 := (mul_eq_zero.mp h1).resolve_left (inv_ne_zero hγ)
    rw [hTz, h0', h1']
    simp
  have hpow : ∀ (k : ℕ) (z : Fin m → K),
      (T ^ k) *ᵥ z = lam ((planeMat γ ^ k) *ᵥ phi z) + (z - lam (phi z)) := by
    intro k
    induction k with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      have hz : phi (z - lam (phi z)) = 0 := by rw [hphisub, hphilam, sub_self]
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih z, Matrix.mulVec_add, hTlam,
        hfix _ hz, pow_succ', ← Matrix.mulVec_mulVec]
  rw [← Units.val_eq_one, Units.val_pow_eq_pow_val, ← hT]
  constructor
  · intro h
    rw [Matrix.ext_iff_mulVec]
    intro c
    have h1 := hpow n (lam c)
    rw [h, Matrix.one_mulVec, hphilam, sub_self, add_zero] at h1
    have h2 := congrArg phi h1
    rw [hphilam, hphilam] at h2
    rw [Matrix.one_mulVec]
    exact h2.symm
  · intro h
    rw [Matrix.ext_iff_mulVec]
    intro z
    rw [hpow n z, h, Matrix.one_mulVec, Matrix.one_mulVec, add_sub_cancel]

end Order

section Assembly

variable {X : Type} [Group X] {K : Type} [Field K] [CharP K 2] [Finite K] {m : ℕ}
  {Q : QuadraticForm K (Fin m → K)} {ψ : X →* GL (Fin m) K} {v w₁ w₂ : Fin m → K}

omit [Finite K] [CharP K 2] in
private theorem map_theta_eq_one (hT : IsTriple Q v w₁ w₂) {t : K × K × K} (ht : t ∈ TT) :
    Q (theta v w₁ w₂ t) = 1 := by
  rw [map_theta hT]
  exact ht.1

omit [Finite K] in
private theorem map_conj_theta (hT : IsTriple Q v w₁ w₂) {z x : X} {c t : K × K × K}
    (hc : c ∈ TT) (hz : ψ z = symmetryGL Q (theta v w₁ w₂ c))
    (hx : ψ x = symmetryGL Q (theta v w₁ w₂ t)) :
    ψ (z * x * z⁻¹) = symmetryGL Q (theta v w₁ w₂ (refl3 c t)) := by
  rw [map_mul, map_mul, map_inv, hz, hx, conj_symmetryGL (symmetryGL_mem Q _),
    symmetryGL_mulVec_theta hT hc.1]

private theorem exists_class_of_model {s : X} (hQ : Q.polarBilin.Nondegenerate)
    (hψ : Function.Injective ψ) (hT : IsTriple Q v w₁ w₂)
    (hrefl : ∀ x : Fin m → K, Q x = 1 → ∃ t, IsConj s t ∧ ψ t = symmetryGL Q x) :
    ∃ S₀ ⊆ {x | IsConj s x},
      (∀ x ∈ S₀, ∀ y ∈ S₀, y * x * y⁻¹ ∈ S₀) ∧
      (∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y) ∧
      (∀ x ∈ S₀, ∀ y ∈ S₀, ¬ Commute x y →
        Subgroup.closure (insert y {z | z ∈ S₀ ∧ Commute z x}) = Subgroup.closure S₀) ∧
      ∀ t ∈ TT, ∃ x ∈ S₀, ψ x = symmetryGL Q (theta v w₁ w₂ t) := by
  classical
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Set X, ∀ x, x ∈ S₀ ↔
      IsConj s x ∧ ∃ t ∈ TT, ψ x = symmetryGL Q (theta v w₁ w₂ t) :=
    ⟨{x | IsConj s x ∧ ∃ t ∈ TT, ψ x = symmetryGL Q (theta v w₁ w₂ t)}, fun x => Iff.rfl⟩
  have hex : ∀ t ∈ TT, ∃ x ∈ S₀, ψ x = symmetryGL Q (theta v w₁ w₂ t) := fun t ht => by
    obtain ⟨x, hxc, hψx⟩ := hrefl _ (map_theta_eq_one hT ht)
    exact ⟨x, (hS₀ x).mpr ⟨hxc, t, ht, hψx⟩, hψx⟩
  have hconj : ∀ {z x : X} {c t : K × K × K}, c ∈ TT → t ∈ TT → IsConj s x →
      ψ z = symmetryGL Q (theta v w₁ w₂ c) → ψ x = symmetryGL Q (theta v w₁ w₂ t) →
      z * x * z⁻¹ ∈ S₀ := by
    intro z x c t hc ht hxc hz hx
    exact (hS₀ _).mpr ⟨hxc.trans (isConj_iff.mpr ⟨z, rfl⟩), refl3 c t, refl3_mem hc ht,
      map_conj_theta hT hc hz hx⟩
  refine ⟨S₀, fun x hx => ((hS₀ x).mp hx).1, ?_, ?_, ?_, hex⟩
  · intro x hx y hy
    obtain ⟨hxc, t, ht, hψx⟩ := (hS₀ x).mp hx
    obtain ⟨-, c, hc, hψy⟩ := (hS₀ y).mp hy
    exact hconj hc ht hxc hψy hψx
  · intro x hx y hy
    obtain ⟨-, t, ht, hψx⟩ := (hS₀ x).mp hx
    obtain ⟨-, t', ht', hψy⟩ := (hS₀ y).mp hy
    rcases exists_refl3_eq_or ht ht' with ⟨c, hc, hct⟩ | ⟨c₁, hc₁, c₂, hc₂, hct⟩
    · obtain ⟨z, hzS, hψz⟩ := hex c hc
      refine ⟨z, Subgroup.subset_closure hzS, hψ ?_⟩
      rw [map_conj_theta hT hc hψz hψx, hct, hψy]
    · obtain ⟨z₁, hz₁S, hψz₁⟩ := hex c₁ hc₁
      obtain ⟨z₂, hz₂S, hψz₂⟩ := hex c₂ hc₂
      refine ⟨z₂ * z₁, Subgroup.mul_mem _ (Subgroup.subset_closure hz₂S)
        (Subgroup.subset_closure hz₁S), hψ ?_⟩
      have h2 := map_conj_theta hT hc₂ hψz₂ (map_conj_theta hT hc₁ hψz₁ hψx)
      rw [hct, ← hψy] at h2
      rw [show z₂ * z₁ * x * (z₂ * z₁)⁻¹ = z₂ * (z₁ * x * z₁⁻¹) * z₂⁻¹ by group]
      exact h2
  · intro x hx y hy hxy
    obtain ⟨-, a, ha, hψx⟩ := (hS₀ x).mp hx
    obtain ⟨-, b, hb, hψy⟩ := (hS₀ y).mp hy
    have hγ : bil a b ≠ 0 := fun h0 => hxy
      ((commute_iff_of_symmetryGL hQ hψ (map_theta_eq_one hT ha) (map_theta_eq_one hT hb)
        hψx hψy).mpr (by rw [polar_theta hT]; exact h0))
    obtain ⟨H, hH⟩ : ∃ H : Subgroup X,
        H = Subgroup.closure (insert y {z | z ∈ S₀ ∧ Commute z x}) := ⟨_, rfl⟩
    rw [← hH]
    obtain ⟨D, hD⟩ : ∃ D : Set (K × K × K), ∀ u, u ∈ D ↔
        u ∈ TT ∧ ∃ z ∈ H, ψ z = symmetryGL Q (theta v w₁ w₂ u) :=
      ⟨{u | u ∈ TT ∧ ∃ z ∈ H, ψ z = symmetryGL Q (theta v w₁ w₂ u)}, fun u => Iff.rfl⟩
    have hD1 : ∀ ν : K, ν ≠ 0 → unu a ν ∈ D := by
      intro ν hν
      obtain ⟨z, hzS, hψz⟩ := hex _ (unu_mem ha hν)
      refine (hD _).mpr ⟨unu_mem ha hν, z, ?_, hψz⟩
      rw [hH]
      refine Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨hzS, ?_⟩)
      exact (commute_iff_of_symmetryGL hQ hψ (map_theta_eq_one hT (unu_mem ha hν))
        (map_theta_eq_one hT ha) hψz hψx).mpr
        (by rw [polar_theta hT]; exact bil_unu_self a ν)
    have hD2 : b ∈ D := (hD _).mpr ⟨hb, y, by
      rw [hH]
      exact Subgroup.subset_closure (Set.mem_insert _ _), hψy⟩
    have hD3 : ∀ c ∈ D, ∀ c' ∈ D, refl3 c c' ∈ D := by
      intro c hc c' hc'
      obtain ⟨hcT, z, hzH, hψz⟩ := (hD c).mp hc
      obtain ⟨hcT', z', hz'H, hψz'⟩ := (hD c').mp hc'
      exact (hD _).mpr ⟨refl3_mem hcT hcT', z * z' * z⁻¹,
        H.mul_mem (H.mul_mem hzH hz'H) (H.inv_mem hzH), map_conj_theta hT hcT hψz hψz'⟩
    have hall := mem_of_closed ha hb hγ hD1 hD2 hD3
    have hsub : S₀ ⊆ H := by
      intro z hz
      obtain ⟨-, u, hu, hψz⟩ := (hS₀ z).mp hz
      obtain ⟨-, z', hz'H, hψz'⟩ := (hD u).mp (hall u hu)
      have hzz : z = z' := hψ (hψz.trans hψz'.symm)
      rw [hzz]
      exact hz'H
    refine le_antisymm ?_ ((Subgroup.closure_le _).mpr hsub)
    rw [hH]
    refine (Subgroup.closure_le _).mpr ?_
    intro z hz
    rcases hz with hzy | ⟨hzS, -⟩
    · rw [hzy]
      exact Subgroup.subset_closure hy
    · exact Subgroup.subset_closure hzS

end Assembly

theorem exists_class_of_isOrthReflection {X : Type} [Group X] (hZ : Subgroup.center X = ⊥)
    {s : X} {m f : ℕ} (_hf : 2 ≤ f)
    (hs : CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection X m f s) :
    ∃ S₀ ⊆ {x | IsConj s x},
      (∀ x ∈ S₀, ∀ y ∈ S₀, y * x * y⁻¹ ∈ S₀) ∧
      (∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y) ∧
      (∀ x ∈ S₀, ∀ y ∈ S₀, ¬ Commute x y →
        Subgroup.closure (insert y {z | z ∈ S₀ ∧ Commute z x}) = Subgroup.closure S₀) ∧
      ∃ x ∈ S₀, ∃ y ∈ S₀, orderOf (x * y) = 2 ^ f + 1 := by
  classical
  have hm := four_le_of_isOrthReflection hs
  obtain ⟨K, _, _, _, Q, ψ, v, hcard, hQ, hψ, hrange, hv, hψs, hrefl⟩ :=
    exists_symmetry_model_of_isOrthReflection hZ hs
  obtain ⟨w₁, w₂, hT⟩ := exists_isTriple hQ hm hv
  obtain ⟨S₀, hS₀, h1, h2, h3, hcov⟩ := exists_class_of_model hQ hψ hT hrefl
  refine ⟨S₀, hS₀, h1, h2, h3, ?_⟩
  obtain ⟨γ, hγ0, hord⟩ := exists_planeMat_orderOf (K := K)
  have ha : ((0 : K), (1 : K), (1 : K)) ∈ TT := ⟨by simp, Or.inl one_ne_zero⟩
  have hb : ((1 : K), (0 : K), γ) ∈ TT := ⟨by simp, Or.inr hγ0⟩
  obtain ⟨x, hxS, hψx⟩ := hcov _ ha
  obtain ⟨y, hyS, hψy⟩ := hcov _ hb
  refine ⟨x, hxS, y, hyS, ?_⟩
  have hab : polar Q (theta v w₁ w₂ (0, 1, 1)) (theta v w₁ w₂ (1, 0, γ)) = γ := by
    rw [polar_theta hT]
    simp [bil]
  rw [← orderOf_injective ψ hψ (x * y), map_mul, hψx, hψy,
    orderOf_eq_orderOf_iff.2 (pow_symmetryGL_mul_eq_one_iff (map_theta_eq_one hT ha)
      (map_theta_eq_one hT hb) hγ0 hab), hord, Nat.card_eq_fintype_card, hcard]

end CFSG.OddTranspositions.PartFour

end

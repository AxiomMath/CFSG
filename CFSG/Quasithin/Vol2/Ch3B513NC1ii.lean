module

public import CFSG.Quasithin.Vol2.Ch3B513NC1

public section

namespace CFSG.Quasithin.B513N

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem card_sup_of_inf_eq_bot {A B : Subgroup W} (h : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hbij : Function.Bijective (fun p : ↥A × ↥B =>
      (⟨(p.1 : W) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(A ⊔ B))) := by
    refine ⟨fun p q hpq => ?_, fun x => ?_⟩
    · have h1 : (p.1 : W) * p.2 = q.1 * q.2 := congrArg Subtype.val hpq
      have h2 : (q.1 : W)⁻¹ * p.1 ∈ A ⊓ B := by
        refine ⟨A.mul_mem (A.inv_mem q.1.2) p.1.2, ?_⟩
        have : (q.1 : W)⁻¹ * p.1 = q.2 * (p.2 : W)⁻¹ :=
          calc (q.1 : W)⁻¹ * p.1 = (q.1 : W)⁻¹ * (p.1 * p.2) * (p.2 : W)⁻¹ := by group
            _ = (q.1 : W)⁻¹ * (q.1 * q.2) * (p.2 : W)⁻¹ := by rw [h1]
            _ = q.2 * (p.2 : W)⁻¹ := by group
        rw [this]
        exact B.mul_mem q.2.2 (B.inv_mem p.2.2)
      rw [h, Subgroup.mem_bot, inv_mul_eq_one] at h2
      have h3 : (p.2 : W) = q.2 := by
        rw [← h2] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext h2.symm) (Subtype.ext h3)
    · obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 x.2
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

omit [Finite W] in
theorem fixV_inf_sup_le {D : Subgroup (MulAut W)} {A B : Subgroup W} (h : A ⊓ B = ⊥)
    (hA : ∀ d ∈ D, ∀ a ∈ A, d a ∈ A) (hB : ∀ d ∈ D, ∀ b ∈ B, d b ∈ B) :
    fixV D ⊓ (A ⊔ B) ≤ (fixV D ⊓ A) ⊔ (fixV D ⊓ B) := by
  rintro u ⟨hu, huAB⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 huAB
  have key : ∀ d ∈ D, d a = a ∧ d b = b := by
    intro d hd
    have h1 : d a * d b = a * b := by rw [← map_mul]; exact hu d hd
    have h2 : (d a)⁻¹ * a ∈ A ⊓ B := by
      refine ⟨A.mul_mem (A.inv_mem (hA d hd a ha)) ha, ?_⟩
      have : (d a)⁻¹ * a = d b * b⁻¹ :=
        calc (d a)⁻¹ * a = (d a)⁻¹ * (a * b) * b⁻¹ := by group
          _ = (d a)⁻¹ * (d a * d b) * b⁻¹ := by rw [h1]
          _ = d b * b⁻¹ := by group
      rw [this]
      exact B.mul_mem (hB d hd b hb) (B.inv_mem hb)
    rw [h, Subgroup.mem_bot, inv_mul_eq_one] at h2
    refine ⟨h2, ?_⟩
    rw [h2] at h1
    exact mul_left_cancel h1
  exact Subgroup.mul_mem_sup ⟨fun d hd => (key d hd).1, ha⟩ ⟨fun d hd => (key d hd).2, hb⟩

omit [Finite W] in
theorem card_fixV_inf_le_of_nat {L D : Subgroup (MulAut W)} {d : ℕ} {K : Type} [Field K]
    [Finite K] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin d) K)} {I : Subgroup W}
    {π : (FFModel.nat Γ).Gam →* ↥L} (hr : (FFModel.nat Γ).RealizesVia L I ⊥ π) {γ : ↥Γ}
    (hγ : γ ≠ 1) (hγD : ((π γ : ↥L) : MulAut W) ∈ D) :
    Nat.card ↥(fixV D ⊓ I) ≤ Nat.card K ^ (d - 1) := by
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hr
  have hFI : fixV D ⊓ I ≤ I := inf_le_right
  let g : ↥(fixV D ⊓ I) →* Multiplicative (Fin d → K) := β.comp (Subgroup.inclusion hFI)
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have := (hβk _).1 hx
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  refine le_trans (Nat.card_le_card_of_injective
    (fun x => (⟨g x, ?_⟩ : {y : Multiplicative (Fin d → K) // natAct Γ γ y = y})) ?_)
    (card_fix_natAct_le Γ hγ)
  · have hfix : ((π γ : ↥L) : MulAut W) (x : W) = x := x.2.1 _ hγD
    have hu : ((π γ : ↥L) : MulAut W) ((x : W)) ∈ I := by rw [hfix]; exact hFI x.2
    have h1 := hβe γ ⟨x, hFI x.2⟩ hu
    have h2 : (⟨((π γ : ↥L) : MulAut W) (x : W), hu⟩ : ↥I) = ⟨x, hFI x.2⟩ :=
      Subtype.ext hfix
    rw [h2] at h1
    exact h1.symm
  · intro x y hxy
    have h1 : g x = g y :=
      congrArg (fun t : {y : Multiplicative (Fin d → K) // natAct Γ γ y = y} => t.1) hxy
    exact hinj h1

theorem relIndex_fixV_le_index (D : Subgroup (MulAut W)) (U : Subgroup W) :
    (fixV D).relIndex U ≤ (fixV D).index := by
  have := Subgroup.relIndex_le_of_le_right (H := fixV D) (le_top : U ≤ ⊤)
    (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
  rwa [Subgroup.relIndex_top_right] at this

theorem c1ii_holds : C1ii := by
  intro W _ _ hW G hne hB53 h1 hii
  generalize quasithinGenFitting G = L at hii
  obtain ⟨hGL, n, K, _, _, hK, I, π, hind, hsup, hreal, -, -⟩ := hii
  have hJ : G = ffJ G := hB53.2.1
  obtain ⟨D, hD⟩ := exists_isFFStarMin hne hJ
  have hDL : D ≤ L := hD.1.1.trans hGL.le
  obtain ⟨d₀, hd₀, hd₀1⟩ : ∃ x ∈ D, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hD.1.2.1 (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx))
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K), π γ = ⟨d₀, hDL hd₀⟩ :=
    (hreal 0).1 _
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    apply hd₀1
    have := congrArg Subtype.val hγ
    rw [map_one] at this
    exact this.symm
  have hγD : ((π γ : ↥L) : MulAut W) ∈ D := by rw [hγ]; exact hd₀
  have hU2 : I 0 ⊔ I 1 = commV L := by
    rw [← hsup]
    apply le_antisymm (sup_le (le_iSup I 0) (le_iSup I 1))
    refine iSup_le fun i => ?_
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hdisj : I 0 ⊓ I 1 = ⊥ := by
    have := hind.disjoint_biSup (x := 0) (y := {1}) (by simp)
    rw [iSup_singleton] at this
    exact disjoint_iff.1 this
  have hinv : ∀ i, ∀ x ∈ D, ∀ u ∈ I i, x u ∈ I i := fun i x hx u hu =>
    (hreal i).2.2.2.1 ⟨x, hDL hx⟩ u hu
  have hF : Nat.card ↥(fixV D ⊓ commV L) ≤ Nat.card K ^ 2 * Nat.card K ^ 2 := by
    rw [← hU2]
    calc Nat.card ↥(fixV D ⊓ (I 0 ⊔ I 1))
        ≤ Nat.card ↥((fixV D ⊓ I 0) ⊔ (fixV D ⊓ I 1)) :=
          Subgroup.card_le_of_le (fixV_inf_sup_le hdisj (hinv 0) (hinv 1))
      _ ≤ Nat.card ↥(fixV D ⊓ I 0) * Nat.card ↥(fixV D ⊓ I 1) := card_sup_le _ _
      _ ≤ Nat.card K ^ 2 * Nat.card K ^ 2 := by
          refine Nat.mul_le_mul ?_ ?_
          · exact card_fixV_inf_le_of_nat (hreal 0) hγ1 hγD
          · exact card_fixV_inf_le_of_nat (hreal 1) hγ1 hγD
  have hIcard : ∀ i, Nat.card (I i) = Nat.card K ^ 3 := fun i => by
    rw [card_commV_of_nat (hreal i), Subgroup.card_bot, one_mul]
  have hUcard : Nat.card (commV L) = Nat.card K ^ 3 * Nat.card K ^ 3 := by
    rw [← hU2, card_sup_of_inf_eq_bot hdisj, hIcard, hIcard]
  have hDK : Nat.card K ^ 2 ≤ Nat.card D := by
    have h1 := Subgroup.relIndex_mul_card (fixV D) (commV L)
    have h2 := (relIndex_fixV_le_index D (commV L)).trans (index_fixV_le_card hD.1)
    have hpos : 0 < Nat.card K ^ 2 * Nat.card K ^ 2 :=
      Nat.mul_pos (pow_pos Nat.card_pos _) (pow_pos Nat.card_pos _)
    have h4 : Nat.card K ^ 3 * Nat.card K ^ 3 ≤
        (fixV D).relIndex (commV L) * (Nat.card K ^ 2 * Nat.card K ^ 2) := by
      rw [← hUcard, ← h1]
      exact Nat.mul_le_mul_left _ hF
    have h5 : Nat.card K ^ 2 * (Nat.card K ^ 2 * Nat.card K ^ 2) ≤
        (fixV D).relIndex (commV L) * (Nat.card K ^ 2 * Nat.card K ^ 2) := by
      calc Nat.card K ^ 2 * (Nat.card K ^ 2 * Nat.card K ^ 2)
          = Nat.card K ^ 3 * Nat.card K ^ 3 := by ring
        _ ≤ _ := h4
    exact (Nat.le_of_mul_le_mul_right h5 hpos).trans h2
  refine hasGood_of_offender_le hW hD (commV_mono hDL) ?_
  calc Nat.card ↥(fixV D ⊓ commV L) ≤ Nat.card K ^ 2 * Nat.card K ^ 2 := hF
    _ = (Nat.card K ^ 2) ^ 2 := by ring
    _ ≤ Nat.card D ^ 2 := Nat.pow_le_pow_left hDK 2

end CFSG.Quasithin.B513N

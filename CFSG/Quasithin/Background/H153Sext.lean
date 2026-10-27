module

public import CFSG.Quasithin.Background.HZCoc24
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Milestones.ASVolI.H13

public section

open scoped Pointwise

namespace CFSG.Quasithin.H153

open CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Coc24

@[expose] def colF (j : Fin 6) : Finset (Fin 24) := Finset.univ.filter fun i => colOf i = j

theorem mem_colF {j : Fin 6} {i : Fin 24} : i ∈ colF j ↔ colOf i = j := by simp [colF]

theorem card_colF (j : Fin 6) : (colF j).card = 4 := by
  fin_cases j <;> decide

theorem colF_injective : Function.Injective colF := by
  intro a b h
  have h1 : (⟨4 * (a : ℕ), by omega⟩ : Fin 24) ∈ colF a :=
    mem_colF.2 (Fin.ext (by simp only [colOf]; omega))
  rw [h, mem_colF] at h1
  rw [← h1]
  exact Fin.ext (by simp only [colOf]; omega)

@[expose] def S0 : Finset (Finset (Fin 24)) := Finset.univ.image colF

theorem mem_S0 (j : Fin 6) : colF j ∈ S0 := Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩

theorem card_S0 : S0.card = 6 := by
  rw [S0, Finset.card_image_of_injective _ colF_injective]
  simp

@[expose] def maskAB (a b : ℕ) : ℕ := (15 <<< (4 * a)) ||| (15 <<< (4 * b))

theorem maskAB_bits : ∀ a < 6, ∀ b < 6, ∀ i < 24,
    ((i / 4 = a ∨ i / 4 = b) ↔ (maskAB a b).testBit i = true) := by
  decide +kernel

theorem maskAB_synd : ∀ a < 6, ∀ b < 6, a ≠ b → syndM (maskAB a b) = 0 := by
  decide +kernel

theorem toAdd_eY_apply (Y : Finset (Fin 24)) (i : Fin 24) :
    Multiplicative.toAdd (eY Y) i = if i ∈ Y then 1 else 0 := toAdd_eY Y i

theorem eY_colF_union_mem (a b : Fin 6) (hab : a ≠ b) : eY (colF a ∪ colF b) ∈ golayC := by
  have h : eY (colF a ∪ colF b) = Multiplicative.ofAdd (bvec 24 (maskAB a b)) := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_eY_apply, toAdd_ofAdd, bvec_apply]
    have hb := maskAB_bits a a.2 b b.2 i i.2
    have hi : i ∈ colF a ∪ colF b ↔ ((i : ℕ) / 4 = a ∨ (i : ℕ) / 4 = b) := by
      rw [Finset.mem_union, mem_colF, mem_colF]
      simp only [colOf, Fin.ext_iff]
    by_cases hc : i ∈ colF a ∪ colF b
    · have := hb.1 (hi.1 hc)
      simp [hc, this]
    · have : ¬ (maskAB a b).testBit i = true := fun h' => hc (hi.2 (hb.2 h'))
      simp [hc, this]
  rw [h, mem_golayC_iff']
  exact (bvec_mem_C_iff _).2 (maskAB_synd a a.2 b b.2 (fun e => hab (Fin.ext e)))

theorem disjoint_colF {a b : Fin 6} (hab : a ≠ b) : Disjoint (colF a) (colF b) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_colF] at hx hx'
  exact hab (hx.symm.trans hx')

theorem eY_smul {σ : S24} (Y : Finset (Fin 24)) : eY (σ • Y) = G6.permAct 24 σ (eY Y) := by
  rw [smul_finset_eq_map, permAct_eY]

theorem isOctad_smul {σ : S24} (hσ : σ ∈ AutPerm) {O : Finset (Fin 24)} (h : IsOctad O) :
    IsOctad (σ • O) :=
  ⟨by rw [Finset.card_smul_finset]; exact h.1, by
    rw [eY_smul]; exact (preserves_cocode hσ).2 _ h.2⟩

theorem isSextet_smul {σ : S24} (hσ : σ ∈ AutPerm) {S : Finset (Finset (Fin 24))}
    (h : IsSextet S) : IsSextet (σ • S) := by
  obtain ⟨hc, h4, hd, hu, ho⟩ := h
  refine ⟨by rw [Finset.card_smul_finset]; exact hc, ?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_smul_finset.1 hB
    rw [Finset.card_smul_finset]
    exact h4 B₁ hB₁
  · intro B hB B' hB' hne
    obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_smul_finset.1 hB
    obtain ⟨B₂, hB₂, rfl⟩ := Finset.mem_smul_finset.1 hB'
    have h12 : B₁ ≠ B₂ := fun e => hne (by rw [e])
    rw [smul_finset_eq_map, smul_finset_eq_map, Finset.disjoint_map]
    exact hd B₁ hB₁ B₂ hB₂ h12
  · ext x
    simp only [Finset.mem_biUnion, id, Finset.mem_univ, iff_true]
    have hx : σ⁻¹ x ∈ S.biUnion id := by rw [hu]; exact Finset.mem_univ _
    obtain ⟨B₁, hB₁, hxB⟩ := Finset.mem_biUnion.1 hx
    exact ⟨σ • B₁, Finset.mem_smul_finset.2 ⟨B₁, hB₁, rfl⟩,
      Finset.mem_smul_finset.2 ⟨σ⁻¹ x, hxB, by simp⟩⟩
  · intro B hB B' hB' hne
    obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_smul_finset.1 hB
    obtain ⟨B₂, hB₂, rfl⟩ := Finset.mem_smul_finset.1 hB'
    have h12 : B₁ ≠ B₂ := fun e => hne (by rw [e])
    rw [← Finset.smul_finset_union]
    exact isOctad_smul hσ (ho B₁ hB₁ B₂ hB₂ h12)

theorem eY_mul_eq (X Y : Finset (Fin 24)) : eY X * eY Y = eY (symmDiff X Y) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, Pi.add_apply, toAdd_eY, Finset.mem_symmDiff]
  by_cases hx : i ∈ X <;> by_cases hy : i ∈ Y <;> simp [hx, hy] <;> decide

theorem eq_of_inter_nonempty {X Y : Finset (Fin 24)} (hX : X.card = 4) (hY : Y.card = 4)
    (h : eY X * eY Y ∈ golayC) (hne : (X ∩ Y).Nonempty) : X = Y := by
  rw [eY_mul_eq] at h
  have h1 := Finset.card_sdiff_add_card_inter X Y
  have h2 := Finset.card_sdiff_add_card_inter Y X
  rw [Finset.inter_comm] at h2
  have hpos : 0 < (X ∩ Y).card := Finset.card_pos.2 hne
  have hcard : (symmDiff X Y).card < 8 := by
    have hu := Finset.card_union_le (X \ Y) (Y \ X)
    rw [Finset.symmDiff_def]
    omega
  have h0 := (eY_mem_golayC_iff _ hcard).1 h
  exact symmDiff_eq_bot.1 (by simpa using h0)

theorem tetrad_mem_S0 {B₁ : Finset (Fin 24)} (h4 : B₁.card = 4)
    (h : eY B₁ * eY (colF 0) ∈ golayC) : B₁ ∈ S0 := by
  by_cases hint : (B₁ ∩ colF 0).Nonempty
  · have : B₁ = colF 0 := eq_of_inter_nonempty h4 (card_colF 0) h hint
    rw [this]
    exact mem_S0 0
  · obtain ⟨x, hx⟩ : B₁.Nonempty := Finset.card_pos.1 (by omega)
    have hj0 : colOf x ≠ 0 := by
      intro hc
      exact hint ⟨x, Finset.mem_inter.2 ⟨hx, mem_colF.2 hc⟩⟩
    have hoct : eY (colF 0) * eY (colF (colOf x)) ∈ golayC := by
      rw [eY_mul_eq, (disjoint_colF (Ne.symm hj0)).symmDiff_eq_sup]
      exact eY_colF_union_mem _ _ (Ne.symm hj0)
    have h' : eY B₁ * eY (colF (colOf x)) ∈ golayC := by
      have e : eY B₁ * eY (colF (colOf x)) =
          (eY B₁ * eY (colF 0)) * (eY (colF 0) * eY (colF (colOf x))) := by
        rw [mul_assoc, ← mul_assoc (eY (colF 0)), sq24, one_mul]
      rw [e]
      exact golayC.mul_mem h hoct
    have : B₁ = colF (colOf x) :=
      eq_of_inter_nonempty h4 (card_colF _) h' ⟨x, Finset.mem_inter.2 ⟨hx, mem_colF.2 rfl⟩⟩
    rw [this]
    exact mem_S0 _

theorem sextet_eq_S0_of_mem {T : Finset (Finset (Fin 24))} (hT : IsSextet T)
    (h0 : colF 0 ∈ T) : T = S0 := by
  have hsub : T ⊆ S0 := by
    intro B hB
    by_cases hBe : B = colF 0
    · rw [hBe]
      exact mem_S0 0
    · have hoct := hT.2.2.2.2 B hB (colF 0) h0 hBe
      have hdisj := hT.2.2.1 B hB (colF 0) h0 hBe
      have : eY B * eY (colF 0) ∈ golayC := by
        rw [eY_mul_eq, hdisj.symmDiff_eq_sup]
        exact hoct.2
      exact tetrad_mem_S0 (hT.2.1 B hB) this
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hT.1, card_S0])

theorem colF_zero : colF 0 = {0, 1, 2, 3} := by decide

theorem sextet_normal_form {S : Finset (Finset (Fin 24))}
    (hS : IsSextet S) : ∃ h ∈ AutPerm, S = h • S0 := by
  obtain ⟨B, hB⟩ : S.Nonempty := Finset.card_pos.1 (by rw [hS.1]; norm_num)
  have h4 := hS.2.1 B hB
  obtain ⟨u, t, hut, rfl, ht⟩ := Finset.card_eq_succ.1 h4
  obtain ⟨v, w, z, hvw, hvz, hwz, rfl⟩ := Finset.card_eq_three.1 ht
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hut
  obtain ⟨p, hp, p0, p1, p2, p3⟩ := CFSG.Monster.B.TwoA.autPerm_maps_four u v w z
    hut.1 hut.2.1 hut.2.2 hvw hvz hwz
  have hpB : p⁻¹ • (insert u {v, w, z} : Finset (Fin 24)) = colF 0 := by
    rw [colF_zero, inv_smul_eq_iff]
    simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, Equiv.Perm.smul_def,
      p0, p1, p2, p3]
  have hT : IsSextet (p⁻¹ • S) := isSextet_smul (AutPerm.inv_mem hp) hS
  have h0 : colF 0 ∈ p⁻¹ • S := Finset.mem_smul_finset.2 ⟨_, hB, hpB⟩
  have hTS := sextet_eq_S0_of_mem hT h0
  exact ⟨p, hp, by rw [← hTS, smul_inv_smul]⟩

end CFSG.Quasithin.H153

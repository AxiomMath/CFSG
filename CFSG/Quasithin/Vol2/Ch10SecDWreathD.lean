module

public import CFSG.Quasithin.Vol2.Ch10SecDWreathC
public import CFSG.Quasithin.Vol2.Ch10SecDFacts33

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Quasithin Equiv

theorem wrBase_normal : wrBase.Normal := by
  rw [← oTwoUpper_top_eq, ← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  exact le_normalizer_oTwoUpper ⊤

@[expose] def wrT : SymFiveWrTwo := ⟨1, zs⟩

theorem wrT_conj (q : Multiplicative (ZMod 2)) (σ : Perm (Fin 5)) :
    wrT * wrIota q σ * wrT⁻¹ = wrIota (zs * q) σ := by
  refine RegularWreathProduct.ext ?_ ?_
  · funext x
    change (1 : Multiplicative (ZMod 2) → Perm (Fin 5)) x *
        (Pi.mulSingle q σ : Multiplicative (ZMod 2) → Perm (Fin 5)) (zs⁻¹ * x) *
        (wrT⁻¹).left ((zs * 1)⁻¹ * x) =
      (Pi.mulSingle (zs * q) σ : Multiplicative (ZMod 2) → Perm (Fin 5)) x
    have hinv : (wrT⁻¹).left = 1 := by
      funext y
      rw [RegularWreathProduct.inv_left]
      rfl
    rw [hinv, Pi.one_apply, Pi.one_apply, one_mul, mul_one, Pi.mulSingle_apply,
      Pi.mulSingle_apply]
    have hiff : ∀ x q : Multiplicative (ZMod 2), (zs⁻¹ * x = q ↔ x = zs * q) := by decide
    exact if_congr (hiff x q) rfl rfl
  · show zs * 1 * zs⁻¹ = 1
    decide

theorem commutator_wrIota (f : Multiplicative (ZMod 2) → Perm (Fin 5))
    (q : Multiplicative (ZMod 2)) (σ : Perm (Fin 5)) :
    wrBaseHom f * wrIota q σ * (wrBaseHom f)⁻¹ * (wrIota q σ)⁻¹ =
      wrIota q (f q * σ * (f q)⁻¹ * σ⁻¹) := by
  rw [wrIota_eq, wrIota_eq, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  funext x
  by_cases hx : x = q
  · subst hx
    simp
  · simp [Pi.mulSingle_eq_of_ne hx]

theorem wrBase_le_of_normal (N : Subgroup SymFiveWrTwo) (hN : N.Normal) (hN1 : N ≠ ⊥) :
    wrBase ≤ N := by
  have hNB : N ⊓ wrBase ≠ ⊥ := by
    intro hbot
    apply hN1
    rw [eq_bot_iff, ← centralizer_wrBase_eq_bot]
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : n * b * n⁻¹ * b⁻¹ ∈ N ⊓ wrBase := by
      refine ⟨?_, wrBase.mul_mem (wrBase_normal.conj_mem b hb n) (wrBase.inv_mem hb)⟩
      have := N.mul_mem hn (hN.conj_mem n⁻¹ (N.inv_mem hn) b)
      simpa [mul_assoc] using this
    rw [hbot, Subgroup.mem_bot] at h1
    calc b * n = (n * b * n⁻¹ * b⁻¹)⁻¹ * n * b := by group
      _ = n * b := by rw [h1]; group
  obtain ⟨⟨n, hnN, hnB⟩, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hNB
  have hn1' : n ≠ 1 := fun h1 => hn1 (Subtype.ext h1)
  have hn := eq_wrBaseHom hnB.1
  obtain ⟨q, hq⟩ : ∃ q, n.left q ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hn1'
    rw [hn, show n.left = 1 from funext hcon, map_one]
  have hcomm : ∀ σ : Perm (Fin 5), wrIota q (n.left q * σ * (n.left q)⁻¹ * σ⁻¹) ∈ N := by
    intro σ
    rw [← commutator_wrIota, ← hn]
    have := N.mul_mem hnN (hN.conj_mem n⁻¹ (N.inv_mem hnN) (wrIota q σ))
    simpa [mul_assoc] using this
  have hq5 : ∀ σ ∈ alternatingGroup (Fin 5), wrIota q σ ∈ N := by
    set K := (N.comap (wrIota q)).subgroupOf (alternatingGroup (Fin 5)) with hK
    have hKn : K.Normal := by
      refine ⟨fun k hk a => ?_⟩
      rw [hK, Subgroup.mem_subgroupOf, Subgroup.mem_comap] at hk ⊢
      have := hN.conj_mem _ hk (wrIota q a)
      simpa [map_mul, map_inv] using this
    have hK1 : K ≠ ⊥ := by
      intro hbot
      apply hq
      have hmem : ∀ σ ∈ alternatingGroup (Fin 5),
          n.left q * σ * (n.left q)⁻¹ * σ⁻¹ = 1 := by
        intro σ hσ
        have h1 : (⟨_, (alternatingGroup (Fin 5)).mul_mem ((alternatingGroup (Fin 5)).mul_mem
            ((alternatingGroup (Fin 5)).mul_mem (hnB.2 q) hσ)
            ((alternatingGroup (Fin 5)).inv_mem (hnB.2 q)))
            ((alternatingGroup (Fin 5)).inv_mem hσ)⟩ : ↥(alternatingGroup (Fin 5))) ∈ K :=
          Subgroup.mem_subgroupOf.mpr (hcomm σ)
        rw [hbot, Subgroup.mem_bot] at h1
        exact congrArg Subtype.val h1
      refine eq_one_of_comm_wc _ ?_ ?_
      · have := hmem wc1 wc1_mem
        calc n.left q * wc1 = n.left q * wc1 * (n.left q)⁻¹ * wc1⁻¹ * wc1 * n.left q := by group
          _ = wc1 * n.left q := by rw [this, one_mul]
      · have := hmem wc2 wc2_mem
        calc n.left q * wc2 = n.left q * wc2 * (n.left q)⁻¹ * wc2⁻¹ * wc2 * n.left q := by group
          _ = wc2 * n.left q := by rw [this, one_mul]
    have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin])
    have hKtop := (IsSimpleGroup.eq_bot_or_eq_top_of_normal K).resolve_left hK1
    intro σ hσ
    have h1 : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin 5))) ∈ K := hKtop ▸ Subgroup.mem_top _
    exact Subgroup.mem_comap.mp (Subgroup.mem_subgroupOf.mp h1)
  have hall : ∀ q' σ, σ ∈ alternatingGroup (Fin 5) → wrIota q' σ ∈ N := by
    intro q' σ hσ
    by_cases hq' : q' = q
    · rw [hq']
      exact hq5 σ hσ
    · have e : q' = zs * q := by
        rcases zmod2_cases q' with rfl | rfl <;> rcases zmod2_cases q with rfl | rfl <;>
          first | exact absurd rfl hq' | decide
      rw [e, ← wrT_conj]
      exact hN.conj_mem _ (hq5 σ hσ) wrT
  intro w hw
  rw [eq_mul_wrIota hw.1]
  exact N.mul_mem (hall 1 _ (hw.2 1)) (hall zs _ (hw.2 zs))

theorem factSymFiveWrTwo : FactSymFiveWrTwo := by
  refine ⟨fun N hN hN1 => ?_, ?_⟩
  · rw [oTwoUpper_top_eq]
    exact wrBase_le_of_normal N hN hN1
  · rw [oTwoUpper_top_eq]
    exact centralizer_wrBase_eq_bot

end CFSG.Quasithin.Vol2.Ch10.SecD

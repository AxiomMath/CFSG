module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NNabQ
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NNabL

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

open CFSG.Holt.General.AltRecPrim

variable {Γ : Type} [Group Γ] [Finite Γ] {Q L : Subgroup Γ} {b : Γ}

theorem index_le_of_orbit (hQ : Q.Normal) (F : SimpleFactors Q) (j : Fin F.r)
    (S : Finset (Fin F.r)) (hmem : ∀ l ∈ L, ∃ k ∈ S, Cj F l j k) :
    ((Subgroup.normalizer (F.S j : Set Γ)).subgroupOf L).index ≤ S.card := by
  classical
  set H : Subgroup L := (Subgroup.normalizer (F.S j : Set Γ)).subgroupOf L with hH
  let f : L → Fin F.r := fun l => (exists_Cj F hQ l j).choose
  have hf : ∀ l : L, Cj F l j (f l) := fun l => (exists_Cj F hQ l j).choose_spec
  have hfS : ∀ l : L, f l ∈ S := by
    intro l
    obtain ⟨k, hk, hlk⟩ := hmem l l.2
    exact (hf l).unique hlk ▸ hk
  have hinj : ∀ l l' : L, f l = f l' → l⁻¹ * l' ∈ H := by
    intro l l' hll
    have h1 : Cj F ((l⁻¹ * l' : L) : Γ) j j := by
      have hc : Cj F (((l : Γ))⁻¹ * (l' : Γ)) j j := by
        have h2 : Cj F (l' : Γ) j (f l) := hll ▸ hf l'
        exact h2.comp (hf l).inv
      simpa using hc
    rw [hH, Subgroup.mem_subgroupOf]
    exact (Cj_self_iff F _ j).mp h1
  let ψ : L ⧸ H → S := fun x => ⟨f x.out, hfS _⟩
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have := hinj x.out y.out (congrArg Subtype.val hxy)
    rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' y]
    exact QuotientGroup.eq.mpr this
  have := Nat.card_le_card_of_injective ψ hψ
  rw [Nat.card_eq_fintype_card (α := S), Fintype.card_coe] at this
  exact this

theorem moved_factor_false (h : NHyp Q L b) (hQ : Q.Normal) (F : SimpleFactors Q)
    (j : Fin F.r) (hb : ¬ Cj F b j j) : False := by
  classical
  obtain ⟨j1, hj1⟩ := exists_Cj F hQ b j
  obtain ⟨j2, hj2⟩ := exists_Cj F hQ b j1
  have hb3 : b * b * b = 1 := by
    have := pow_orderOf_eq_one b
    rw [h.order] at this
    simpa [pow_succ, mul_assoc] using this
  have hj1j : j1 ≠ j := fun e => hb (e ▸ hj1)
  have hj2j : j2 ≠ j := by
    intro e
    have h1 : Cj F (b * b) j j := hj1.comp (e ▸ hj2)
    have h2 : Cj F (b * (b * b)) j j1 := h1.comp hj1
    have h3 : b * (b * b) = 1 := by rw [← mul_assoc]; exact hb3
    rw [h3] at h2
    exact hj1j ((Cj.one F j).unique h2).symm
  have hj2j1 : j2 ≠ j1 := by
    intro e
    have h2 : Cj F (b⁻¹ * b) j j1 := (e ▸ hj2).inv |> hj1.comp
    rw [inv_mul_cancel] at h2
    exact hj1j ((Cj.one F j).unique h2).symm
  obtain ⟨x, hxS, hx1⟩ := exists_ne_one_mem F j
  set x1 : Γ := b * x * b⁻¹ with hx1def
  set x2 : Γ := b * x1 * b⁻¹ with hx2def
  have hx1S : x1 ∈ F.S j1 := (hj1 x).mp hxS
  have hx2S : x2 ∈ F.S j2 := (hj2 x1).mp hx1S
  have hbx2 : b * x2 * b⁻¹ = x := by
    have : b * x2 * b⁻¹ = (b * b * b) * x * (b * b * b)⁻¹ := by
      rw [hx2def, hx1def]; group
    rw [this, hb3]; group
  have hc1 : Commute x x1 := F.commute_of_ne hj1j.symm hxS hx1S
  have hc2 : Commute x x2 := F.commute_of_ne hj2j.symm hxS hx2S
  set d : Γ := x * x1 * x2 with hd
  have hdQ : d ∈ Q := mul_mem (mul_mem (F.le j hxS) (F.le j1 hx1S)) (F.le j2 hx2S)
  have hbd : b * d * b⁻¹ = d := by
    have : b * d * b⁻¹ = x1 * x2 * (b * x2 * b⁻¹) := by
      rw [hd, hx2def, hx1def]; group
    rw [this, hbx2]
    have h12 : Commute x (x1 * x2) := hc1.mul_right hc2
    calc x1 * x2 * x = (x1 * x2) * x := rfl
      _ = x * (x1 * x2) := h12.eq.symm
      _ = d := by rw [hd]; exact (mul_assoc x x1 x2).symm
  have hdC : d ∈ Subgroup.centralizer (L : Set Γ) := by
    refine h.cent (Subgroup.mem_inf.mpr ⟨hdQ, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    calc g * d = (g * d * g⁻¹) * g := by group
      _ = d * g := by rw [hbd]
  have horbit : ∀ l ∈ L, ∃ k ∈ ({j, j1, j2} : Finset (Fin F.r)), Cj F l j k := by
    intro l hl
    obtain ⟨k, hk⟩ := exists_Cj F hQ l j
    refine ⟨k, ?_, hk⟩
    by_contra hkS
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hkS
    obtain ⟨hkj, hkj1, hkj2⟩ := hkS
    have hld : l * d * l⁻¹ = d := by
      have := Subgroup.mem_centralizer_iff.mp hdC l hl
      calc l * d * l⁻¹ = (l * d) * l⁻¹ := rfl
        _ = (d * l) * l⁻¹ := by rw [this]
        _ = d := by group
    have hm : l * (⟨d, hdQ⟩ : Q) * l⁻¹ ∈ Q := by
      show l * d * l⁻¹ ∈ Q
      rw [hld]; exact hdQ
    have hpc := F.proj_conj hk.map_eq ⟨d, hdQ⟩ (by simpa using hm)
    have hsub : (⟨l * d * l⁻¹, by simpa using hm⟩ : Q) = ⟨d, hdQ⟩ := Subtype.ext hld
    rw [hsub] at hpc
    have hdsplit : (⟨d, hdQ⟩ : Q) = ⟨x, F.le j hxS⟩ * ⟨x1, F.le j1 hx1S⟩ * ⟨x2, F.le j2 hx2S⟩ :=
      rfl
    have hpj : (F.proj j ⟨d, hdQ⟩ : Γ) = x := by
      rw [hdsplit, map_mul, map_mul, F.proj_of_mem_of_ne hj1j.symm hx1S,
        F.proj_of_mem_of_ne hj2j.symm hx2S]
      simpa using F.proj_of_mem hxS
    have hpk : (F.proj k ⟨d, hdQ⟩ : Γ) = 1 := by
      rw [hdsplit, map_mul, map_mul, F.proj_of_mem_of_ne hkj hxS,
        F.proj_of_mem_of_ne hkj1 hx1S, F.proj_of_mem_of_ne hkj2 hx2S]
      simp
    rw [hpk, hpj] at hpc
    apply hx1
    calc x = l⁻¹ * (l * x * l⁻¹) * l := by group
      _ = 1 := by rw [← hpc]; group
  have hidx := index_le_of_orbit hQ F j {j, j1, j2} horbit
  have hcard : ({j, j1, j2} : Finset (Fin F.r)).card ≤ 3 := Finset.card_le_three
  have htop := h.eq_top_of_index_le_three _ (hidx.trans hcard)
  have hbmem : (⟨b, h.mem⟩ : L) ∈ (Subgroup.normalizer (F.S j : Set Γ)).subgroupOf L := by
    rw [htop]; exact Subgroup.mem_top _
  rw [Subgroup.mem_subgroupOf] at hbmem
  exact hb ((Cj_self_iff F b j).mpr hbmem)

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

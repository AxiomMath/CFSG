module

public import CFSG.Quasithin.Background.D2Z8

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem sup_mulEquiv_prod {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) (hinf : H ⊓ K = ⊥) :
    Nonempty (↥(H ⊔ K) ≃* (↥H × ↥K)) := by
  let f : ↥H × ↥K →* G := H.subtype.noncommCoprod K.subtype (fun x y => hcomm x x.2 y y.2)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ h
    have h1 : (x : G) * y = 1 := h
    have hx : (x : G) ∈ H ⊓ K := by
      refine ⟨x.2, ?_⟩
      have : (x : G) = (y : G)⁻¹ := mul_eq_one_iff_eq_inv.mp h1
      rw [this]
      exact K.inv_mem y.2
    rw [hinf, Subgroup.mem_bot] at hx
    have hy : (y : G) = 1 := by
      rw [hx, one_mul] at h1
      exact h1
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  have hrange : f.range = H ⊔ K := by
    apply le_antisymm
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      exact Subgroup.mul_mem_sup a.2 b.2
    · refine sup_le (fun a ha => ⟨(⟨a, ha⟩, 1), ?_⟩) (fun b hb => ⟨(1, ⟨b, hb⟩), ?_⟩)
      · show a * 1 = a
        exact mul_one a
      · show 1 * b = b
        exact one_mul b
  exact ⟨((MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)).symm⟩

omit [Finite V] in
theorem card_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hcomm : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) (hinf : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  obtain ⟨e⟩ := sup_mulEquiv_prod hcomm hinf
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]

omit [Finite V] in
structure PDecomp (X : Subgroup (MulAut V)) {s : ℕ} (Pi : Fin s → Subgroup (MulAut V)) : Prop where
  le_P : ∀ i, Pi i ≤ pCoreOf 3 X
  card_eq : ∀ i, Nat.card (Pi i) = 3
  indep : iSupIndep Pi
  sup_eq : ⨆ i, Pi i = pCoreOf 3 X
  card_P : Nat.card (pCoreOf 3 X) = 3 ^ s
  rk_eq : ∀ i, rk (commV (Pi i)) = 2
  vindep : iSupIndep fun i => commV (Pi i)
  vsup : ⨆ i, commV (Pi i) = commV (pCoreOf 3 X)
  triv : ∀ i j, i ≠ j → commV (Pi i) ≤ fixV (Pi j)

section Three

variable {X A : Subgroup (MulAut V)} {r : ℚ}

theorem pdecomp_three (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u w : MulAut V}
    (kt : KTriple A t u w) (h1 : centR X t ≠ ⊥) (h2 : centR X u ≠ ⊥) (h3 : centR X w ≠ ⊥) :
    PDecomp X ![centR X t, centR X u, centR X w] := by
  obtain ⟨-, r1, r2, r3, d_tu, d_tw, d_uw⟩ := caseThree hV h kt h1 h2 h3
  have c1 : Nat.card (centR X t) = 3 := (centR_data hV h kt.tu h1).1
  have c2 : Nat.card (centR X u) = 3 := (centR_data hV h kt.tu.symm h2).1
  have c3 : Nat.card (centR X w) = 3 := (centR_data hV h kt.tw.symm h3).1
  have i1 := centR_inf_sup_eq_bot hV h kt.tu.symm kt.tw.symm
  have i2 := centR_inf_sup_eq_bot hV h kt.uw.symm kt.tu
  have i3 := centR_inf_sup_eq_bot hV h kt.tw kt.uw
  have hcomm := pCoreOf_comm hV h
  have hPsup := pCoreOf_eq_sup_triple hV h kt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact centR_le_pCoreOf X t
    · exact centR_le_pCoreOf X u
    · exact centR_le_pCoreOf X w
  · intro i
    fin_cases i
    · exact c1
    · exact c2
    · exact c3
  · rw [iSupIndep_fin_three]
    refine ⟨?_, ?_, ?_⟩
    · exact disjoint_iff.mpr i1
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
      exact disjoint_iff.mpr i2
    · exact disjoint_iff.mpr i3
  · rw [iSup_fin_three, hPsup]
    simp
  · rw [hPsup]
    have hinf : (centR X t ⊔ centR X u) ⊓ centR X w = ⊥ := by rw [inf_comm]; exact i3
    have hcomm' : ∀ a ∈ centR X t ⊔ centR X u, ∀ b ∈ centR X w, a * b = b * a := fun a ha b hb =>
      hcomm a (sup_le (centR_le_pCoreOf X t) (centR_le_pCoreOf X u) ha) b (centR_le_pCoreOf X w hb)
    have e1 := card_sup_of_commute hcomm' hinf
    have e2 := card_sup_of_commute (centR_comm hV h t u) (centR_inf_eq_bot hV h kt.tu)
    rw [e1, e2, c1, c2, c3]
    norm_num
  · intro i
    fin_cases i
    · exact r1
    · exact r2
    · exact r3
  · rw [iSupIndep_fin_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    refine ⟨?_, ?_, ?_⟩
    · have := sup_inf_eq_bot_of_disjoint hV h (t := u) (u := w) (w := t)
        (by rw [inf_comm]; exact d_tu) (by rw [inf_comm]; exact d_tw) c1
      exact disjoint_iff.mpr (by rw [inf_comm]; exact this)
    · have := sup_inf_eq_bot_of_disjoint hV h (t := w) (u := t) (w := u)
        (by rw [inf_comm]; exact d_uw) d_tu c2
      exact disjoint_iff.mpr (by rw [inf_comm]; exact this)
    · have := sup_inf_eq_bot_of_disjoint hV h (t := t) (u := u) (w := w) d_tw d_uw c3
      exact disjoint_iff.mpr (by rw [inf_comm]; exact this)
  · rw [iSup_fin_three, hPsup, commV_sup, commV_sup]
    simp
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact Nt_le_fixV_of_disjoint hV h d_tu
    · exact Nt_le_fixV_of_disjoint hV h d_tw
    · exact Nt_le_fixV_of_disjoint hV h (by rw [inf_comm]; exact d_tu)
    · exact Nt_le_fixV_of_disjoint hV h d_uw
    · exact Nt_le_fixV_of_disjoint hV h (by rw [inf_comm]; exact d_tw)
    · exact Nt_le_fixV_of_disjoint hV h (by rw [inf_comm]; exact d_uw)

end Three

end CFSG.Quasithin

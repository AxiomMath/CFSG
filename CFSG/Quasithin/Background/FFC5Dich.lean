module

public import CFSG.Quasithin.Background.FFC5S5
public import CFSG.Quasithin.Background.FFC5Piece
public import CFSG.Quasithin.Background.B56Inputs

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.JonesParshall

section Dich

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem commV_hc (L : Subgroup (MulAut V)) : ∀ g ∈ L, ∀ v : V, g v * v⁻¹ ∈ commV L :=
  fun g hg v => Subgroup.subset_closure ⟨g, hg, v, rfl⟩

omit [Finite V] in
theorem commV_hLW (L : Subgroup (MulAut V)) : ∀ g ∈ L, ∀ w ∈ commV L, g w ∈ commV L :=
  fun _ hg _ hw => commV_invariant_self L _ hg _ hw

theorem dich_case1 (hV : ∀ v : V, v ^ 2 = 1) {A L : Subgroup (MulAut V)} (h : B59Case1 A L) :
    commV L ⊔ fixV L = ⊤ := by
  obtain ⟨-, ⟨-, -, hodd⟩, hS⟩ := h
  exact sup_fixV_eq_top_of_odd (commV_hLW L) (commV_hc L) hV (Nat.odd_iff.2 (by omega)) hS

omit [Finite V] in
theorem index_eq_two_of_three {S : Subgroup V} (hne : S ≠ ⊤)
    (h : ∀ v v' : V, v ∈ S ∨ v' ∈ S ∨ v * v'⁻¹ ∈ S) : S.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  obtain ⟨a, ha⟩ : ∃ a, a ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_top_iff.2 fun x _ => hcon x)
  refine ⟨a, fun b => ?_⟩
  by_cases hb : b ∈ S
  · refine Or.inr ⟨hb, fun hba => ha ?_⟩
    simpa using S.mul_mem (S.inv_mem hb) hba
  · refine Or.inl ⟨?_, hb⟩
    rcases h b a⁻¹ with h1 | h1 | h1
    · exact absurd h1 hb
    · exact absurd (by simpa using S.inv_mem h1) ha
    · simpa using h1

omit [Finite V] in
theorem dich_case5
    {A L : Subgroup (MulAut V)} (hA2 : IsElemAbelian2 A) (h : B59Case5 A L) :
    commV L ⊔ fixV L = ⊤ := by
  obtain ⟨-, hAL, hA4, ⟨-, hnat, -⟩, hS⟩ := h
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h] at hA4
    simp at hA4
  obtain ⟨D⟩ := exists_natQuot3 hnat
  exact sup_fixV_eq_top_of_R (commV_hLW L) (commV_hc L) hS
    (D.hR (fun z hz g hg => hz.1 g hg) hAL hAne hA2.2 (commV_hLW L))

omit [Finite V] in
theorem dich_case4 {A L : Subgroup (MulAut V)} (h : B59Case4 A L) :
    commV L ⊔ fixV L = ⊤ ∨
      (BinaryNaturalSL L (commV L) ⊥ 3 1 ∧ (commV L ⊔ fixV L).index = 2) := by
  obtain ⟨⟨m, hm, K, hK, hf, hcard, hreal⟩, -⟩ := h
  by_cases h1 : m = 1
  · subst h1
    obtain ⟨D⟩ := exists_natQuot3 ⟨K, hK, hf, hcard, hreal⟩
    by_cases htop : commV L ⊔ fixV L = ⊤
    · exact Or.inl htop
    · exact Or.inr ⟨⟨K, hK, hf, hcard, hreal⟩, index_eq_two_of_three htop
        (sup_fixV_natural3 (commV_hLW L) (commV_hc L) D)⟩
  · refine Or.inl (sup_fixV_eq_top_of_h1 (commV_hLW L) (commV_hc L) ?_)
    have hm' : 1 < m := by
      rcases hm with ⟨k, rfl⟩
      omega
    exact natural_h1_vanish hcard hm' (commV_hLW L) hreal

omit [Finite V] in
theorem dich_case3
    {A L : Subgroup (MulAut V)} (hA2 : IsElemAbelian2 A) (hAne : A ≠ ⊥)
    (h : B59Case3 A L) : commV L ⊔ fixV L = ⊤ := by
  obtain ⟨⟨m, K, hK, hf, hm, hcard, I, π, hZ, hind, hsup, hreal⟩, hAL, hS⟩ := h
  have hLI : ∀ i, ∀ g ∈ L, ∀ w ∈ I i, g w ∈ I i :=
    fun i g hg w hw => (hreal i).2.2.2.1 ⟨g, hg⟩ w hw
  have h12 : (⨆ j : Fin 2, ⨆ _ : j ≠ 0, I j) = I 1 := by
    refine le_antisymm (iSup₂_le fun j hj => ?_) (le_iSup₂ (f := fun j _ => I j) 1 (by decide))
    fin_cases j
    · exact absurd rfl hj
    · exact le_rfl
  have hsup2 : I 0 ⊔ I 1 = commV L := by
    rw [← hsup, bot_sup_eq]
    refine le_antisymm (sup_le (le_iSup I 0) (le_iSup I 1)) (iSup_le fun i => ?_)
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hinf2 : I 0 ⊓ I 1 = ⊥ := by
    have := hind 0
    rwa [h12, bot_sup_eq] at this
  have hRi : ∀ i, ∀ f ∈ Z1A (muW (hLI i)), (∃ m' : Additive ↥(I i), ∀ a : ↥L, (a : MulAut V) ∈ A →
      f a = muW (hLI i) a m' - m') → f ∈ B1A (muW (hLI i)) := by
    intro i
    by_cases h1 : m = 1
    · subst h1
      obtain ⟨D⟩ := exists_natQuot3 (H := L) (U := I i) (Z := ⊥)
        ⟨K, hK, hf, hcard, π, hreal i⟩
      exact D.hR (fun z hz g _ => by rw [Subgroup.mem_bot.1 hz, map_one]) hAL hAne hA2.2 (hLI i)
    · have hm' : 1 < m := by
        rcases hm with ⟨k, rfl⟩
        omega
      exact fun f hf _ => natural_h1_vanish hcard hm' (hLI i) ⟨π, hreal i⟩ f hf
  exact sup_fixV_eq_top_of_R (commV_hLW L) (commV_hc L) hS
    (hR_of_directSum hsup2 hinf2 (hLI 0) (hLI 1) (commV_hLW L) (hRi 0) (hRi 1))

omit [Finite V] in
theorem dich_case2 {A L : Subgroup (MulAut V)} (h : B59Case2 A L) :
    commV (L ⊔ A) = commV L ∧ commV (L ⊔ A) ⊔ fixV (L ⊔ A) = ⊤ ∧ commV L ⊓ fixV (L ⊔ A) = ⊥ := by
  obtain ⟨-, -, hsym, hS⟩ := h
  have hreal := hsym
  obtain ⟨π, hπ⟩ := hsym
  have hLA : ∀ g ∈ L ⊔ A, ∀ w ∈ commV L, g w ∈ commV L := fun g hg w hw => hπ.2.2.2.1 ⟨g, hg⟩ w hw
  have hAcomm : A ≤ B19.commLeSub (commV L) := by
    intro a ha v
    have hv : v ∈ commV L ⊔ fixV A := by rw [hS]; trivial
    obtain ⟨w, hw, z, hz, rfl⟩ := Subgroup.mem_sup.1 hv
    have h1 : (a : MulAut V) (w * z) * (w * z)⁻¹ = (a : MulAut V) w * w⁻¹ := by
      rw [map_mul, hz a ha, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
    show (a : MulAut V) (w * z) * (w * z)⁻¹ ∈ commV L
    rw [h1]
    exact (commV L).mul_mem (hLA a ((le_sup_right : A ≤ L ⊔ A) ha) w hw) ((commV L).inv_mem hw)
  have hLcomm : L ≤ B19.commLeSub (commV L) := B19.commV_le_iff.1 le_rfl
  have hle : L ⊔ A ≤ B19.commLeSub (commV L) := sup_le hLcomm hAcomm
  have hcomm : commV (L ⊔ A) = commV L :=
    le_antisymm (B19.commV_le_iff.2 hle) (B19.commV_mono le_sup_left)
  refine ⟨hcomm, ?_, fixV_inf_eq_bot_of_sym5 hπ ▸ inf_comm _ _⟩
  rw [hcomm]
  exact sup_fixV_eq_top_of_h1 hLA (fun g hg v => hle hg v) (sym5_h1_vanish hLA hreal)

end Dich

end FFC

end CFSG.Quasithin

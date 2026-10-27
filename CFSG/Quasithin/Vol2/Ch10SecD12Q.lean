module

public import CFSG.Quasithin.Vol2.Ch10SecDFacts12
public import CFSG.Quasithin.Vol2.Ch10SecD12I

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem autOn_le_normalizer (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) {E : Subgroup G}
    (hE : E ≤ fsuM T L ⊓ Subgroup.normalizer (fsuUL T L I : Set G)) (hEa : IsElemAbelian 2 E) :
    autOn E (fsuUL T L I) ≤
        Subgroup.normalizer (autOn L (fsuUL T L I) : Set (MulAut ↥(fsuUL T L I))) ∧
      IsElemAbelian 2 (autOn E (fsuUL T L I)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨⟨x, hxN⟩, hxE, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro σ
    exact conj_mem_autOn_iff (mem_normalizer_L h37 h38 h (hE (Subgroup.mem_subgroupOf.mp hxE)))
      hxN σ
  · have hcomm : ∀ a ∈ autOn E (fsuUL T L I), ∀ b ∈ autOn E (fsuUL T L I), a * b = b * a := by
      rintro _ ⟨⟨x, hxN⟩, hxE, rfl⟩ _ ⟨⟨y, hyN⟩, hyE, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (B2F.isElemAbelian_comm hEa (Subgroup.mem_subgroupOf.mp hxE)
        (Subgroup.mem_subgroupOf.mp hyE))
    refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, ?_⟩
    rintro _ ⟨⟨x, hxN⟩, hxE, rfl⟩
    rw [← map_pow]
    have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (fsuUL T L I : Set G))) ^ 2 = 1 :=
      Subtype.ext (by simpa using hEa.2 x (Subgroup.mem_subgroupOf.mp hxE))
    rw [this, map_one]

theorem rank_le_of_bound (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) {r0 : ℕ} (hb : RankBoundAut (autOn L (fsuUL T L I)) r0) (E : Subgroup G)
    (hE : E ≤ fsuM T L ⊓ Subgroup.normalizer (fsuUL T L I : Set G)) (hEa : IsElemAbelian 2 E) :
    mQuot E (E ⊓ Subgroup.centralizer (fsuUL T L I : Set G)) ≤ r0 := by
  obtain ⟨hsub, hel⟩ := autOn_le_normalizer h37 h38 h hE hEa
  have hcard : Nat.card (autOn E (fsuUL T L I)) =
      2 ^ mQuot E (E ⊓ Subgroup.centralizer (fsuUL T L I : Set G)) := by
    rw [card_autOn_eq_relIndex (hE.trans inf_le_right)]
    exact relIndex_eq_two_pow (B2F.isPGroup_of_isElemAbelian hEa) _
  have := hb _ hsub hel
  rw [hcard] at this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

omit [Finite G] in
theorem fixV_autOn_eq [IsMulCommutative ↥(fsuUL T L I)] {B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (fsuUL T L I : Set G)) :
    fixV (autOn B (fsuUL T L I)) = (Subgroup.centralizer (B : Set G)).subgroupOf (fsuUL T L I) := by
  ext v
  rw [Subgroup.mem_subgroupOf]
  exact (mem_centralizer_iff_autOn hB v).symm

theorem a_le_of_bound (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) [IsMulCommutative ↥(fsuUL T L I)] {a0 : ℕ}
    (ha : ∀ E : Subgroup (MulAut ↥(fsuUL T L I)),
      E ≤ Subgroup.normalizer (autOn L (fsuUL T L I) : Set (MulAut ↥(fsuUL T L I))) →
      IsElemAbelian 2 E → E ≠ ⊥ → ∀ q : ℕ,
        (∀ B : Subgroup (MulAut ↥(fsuUL T L I)), B ≤ E → mQuot E B < q → fixV B = fixV E) →
          q ≤ a0)
    (E : Subgroup G) (hE : E ≤ fsuM T L ⊓ Subgroup.normalizer (fsuUL T L I : Set G))
    (hEa : IsElemAbelian 2 E) (hEC : ¬ E ≤ Subgroup.centralizer (fsuUL T L I : Set G)) (q : ℕ)
    (hq : ∀ B : Subgroup G, B ≤ E → mQuot E B < q →
      fsuUL T L I ⊓ Subgroup.centralizer (B : Set G) =
        fsuUL T L I ⊓ Subgroup.centralizer (E : Set G)) : q ≤ a0 := by
  have hEN : E ≤ Subgroup.normalizer (fsuUL T L I : Set G) := hE.trans inf_le_right
  obtain ⟨hsub, hel⟩ := autOn_le_normalizer h37 h38 h hE hEa
  have hne : autOn E (fsuUL T L I) ≠ ⊥ := by
    intro hbot
    apply hEC
    intro x hx
    have h1 : conjAct (fsuUL T L I) ⟨x, hEN hx⟩ ∈ autOn E (fsuUL T L I) :=
      ⟨⟨x, hEN hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact A1b.conjAct_eq_one_iff.mp h1
  refine ha _ hsub hel hne q fun B' hB' hqB => ?_
  set B := E ⊓ (B'.comap (conjAct (fsuUL T L I))).map
    (Subgroup.normalizer (fsuUL T L I : Set G)).subtype with hBdef
  have hBE : B ≤ E := inf_le_left
  have hBN : B ≤ Subgroup.normalizer (fsuUL T L I : Set G) := hBE.trans hEN
  have hautB : autOn B (fsuUL T L I) = B' := by
    refine le_antisymm (fun σ hσ => ?_) (fun σ hσ => ?_)
    · obtain ⟨⟨x, hxN⟩, hxB, rfl⟩ := Subgroup.mem_map.mp hσ
      obtain ⟨-, ⟨y, hy, hyx⟩⟩ := Subgroup.mem_subgroupOf.mp hxB
      have : y = ⟨x, hxN⟩ := Subtype.ext hyx
      rw [← this]
      exact hy
    · obtain ⟨⟨x, hxN⟩, hxE, hxσ⟩ := Subgroup.mem_map.mp (hB' hσ)
      refine Subgroup.mem_map.mpr ⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.mpr
        ⟨Subgroup.mem_subgroupOf.mp hxE, ⟨⟨x, hxN⟩, ?_, rfl⟩⟩, hxσ⟩
      show conjAct (fsuUL T L I) ⟨x, hxN⟩ ∈ B'
      rw [hxσ]
      exact hσ
  have hEB : mQuot E B = mQuot (autOn E (fsuUL T L I)) B' := by
    have hE2 := B2F.isPGroup_of_isElemAbelian hEa
    have hKB : E ⊓ Subgroup.centralizer (fsuUL T L I : Set G) ≤ B := by
      intro x hx
      refine ⟨hx.1, ⟨x, hEN hx.1⟩, ?_, rfl⟩
      show conjAct (fsuUL T L I) ⟨x, hEN hx.1⟩ ∈ B'
      rw [A1b.conjAct_eq_one_iff.mpr hx.2]
      exact B'.one_mem
    have hBC : B ⊓ Subgroup.centralizer (fsuUL T L I : Set G) =
        E ⊓ Subgroup.centralizer (fsuUL T L I : Set G) :=
      le_antisymm (inf_le_inf_right _ hBE) (le_inf hKB inf_le_right)
    have h1 := card_eq_two_pow_mul hE2 hBE
    have h2 := card_eq_two_pow_mul (B2F.isPGroup_of_isElemAbelian hel) hB'
    have h3 := Subgroup.relIndex_mul_card (E ⊓ Subgroup.centralizer (fsuUL T L I : Set G)) E
    have h4 := Subgroup.relIndex_mul_card (B ⊓ Subgroup.centralizer (fsuUL T L I : Set G)) B
    rw [inf_eq_left.mpr inf_le_left, ← card_autOn_eq_relIndex hEN] at h3
    rw [inf_eq_left.mpr inf_le_left, ← card_autOn_eq_relIndex hBN, hautB, hBC] at h4
    have hc : 0 < Nat.card ↥(E ⊓ Subgroup.centralizer (fsuUL T L I : Set G)) := Nat.card_pos
    have hb : 0 < Nat.card B' := Nat.card_pos
    have h5 : 2 ^ mQuot E B * (Nat.card B' * Nat.card ↥(E ⊓ Subgroup.centralizer
        (fsuUL T L I : Set G))) = 2 ^ mQuot (autOn E (fsuUL T L I)) B' *
          (Nat.card B' * Nat.card ↥(E ⊓ Subgroup.centralizer (fsuUL T L I : Set G))) := by
      calc _ = 2 ^ mQuot E B * Nat.card B := by rw [← h4]
        _ = Nat.card E := h1.symm
        _ = _ := by rw [← h3, h2]; ring
    exact Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_right (by positivity) h5)
  have h6 := hq B hBE (hEB ▸ hqB)
  rw [← hautB, fixV_autOn_eq hBN, fixV_autOn_eq hEN]
  ext v
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  constructor
  · intro hv
    exact (h6.le ⟨v.2, hv⟩).2
  · intro hv
    exact (h6.ge ⟨v.2, hv⟩).2

end CFSG.Quasithin.Vol2.Ch10.SecD

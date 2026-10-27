module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312NE
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312E
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312ND

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L3312.NQ

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem le_centralizer_of_unique {B : Subgroup Q} {z : Q} (hzB : z ∈ B) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hzuniq : ∀ t ∈ B, t * t = 1 → t = 1 ∨ t = z) :
    B ≤ Subgroup.centralizer ({z} : Set Q) := by
  intro b hb
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hbz : b * z * b⁻¹ ∈ B := B.mul_mem (B.mul_mem hb hzB) (B.inv_mem hb)
  rcases hzuniq _ hbz (by
    calc b * z * b⁻¹ * (b * z * b⁻¹) = b * (z * z) * b⁻¹ := by group
      _ = 1 := by rw [hz2]; group) with h | h
  · exfalso
    apply hz1
    calc z = b⁻¹ * (b * z * b⁻¹) * b := by group
      _ = 1 := by rw [h]; group
  · calc b * z = (b * z * b⁻¹) * b := by group
      _ = z * b := by rw [h]

theorem map_eq_of_le_sup {B O : Subgroup Q} [O.Normal] (hOsolv : Group.IsSolvable ↥O)
    (hperf : ⁅B, B⁆ = B) {z : Q} (hBC : B ≤ Subgroup.centralizer ({z} : Set Q))
    (hCz : O ⊓ Subgroup.centralizer ({z} : Set Q) ≤ Subgroup.centralizer (B : Set Q))
    {d : MulAut Q} (hdz : d z = z) (hle : B.map d.toMonoidHom ≤ B ⊔ O) :
    B.map d.toMonoidHom = B := by
  have hdC : B.map d.toMonoidHom ≤ Subgroup.centralizer ({z} : Set Q) := by
    rintro _ ⟨b, hb, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hBC hb)
    rw [Subgroup.mem_centralizer_singleton_iff]
    show d b * z = z * d b
    rw [← hdz, ← map_mul, ← map_mul, h]
  have h1 : B.map d.toMonoidHom ≤ B ⊔ (Subgroup.centralizer ({z} : Set Q) ⊓ O) :=
    (le_inf hdC hle).trans (ChiefCount.inf_sup_le hBC (fun b _ =>
      (Subgroup.normalizer_eq_top (H := O)).symm ▸ Subgroup.mem_top b))
  have hY : B ⊔ (Subgroup.centralizer ({z} : Set Q) ⊓ O) ≤ Subgroup.normalizer (B : Set Q) :=
    sup_le Subgroup.le_normalizer
      ((inf_comm (Subgroup.centralizer ({z} : Set Q)) O ▸ hCz).trans
        (Subgroup.centralizer_le_normalizer _))
  have hcore : perfectCore (B ⊔ (Subgroup.centralizer ({z} : Set Q) ⊓ O)) ≤ B :=
    perfectCore_le_of_sup_solvable le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hY) rfl
      (Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (inf_le_right : Subgroup.centralizer ({z} : Set Q) ⊓ O ≤ O)))
  have hperf' : ⁅B.map d.toMonoidHom, B.map d.toMonoidHom⁆ = B.map d.toMonoidHom := by
    rw [← Subgroup.map_commutator, hperf]
  have h2 : B.map d.toMonoidHom ≤ B := (le_perfectCore_of_perfect h1 hperf').trans hcore
  exact Subgroup.eq_of_le_of_card_ge h2
    (le_of_eq (Subgroup.card_map_of_injective d.injective).symm)

theorem oddNorm_case22 (hNorm : FactL2pSylowNorm)
    (hFour : FactL2pSylowFour) (hOut : FactAutL2pOuter) {B : Subgroup Q}
    (hcomm : A36Common Q) (hcase : A36Case3 Q ∨ A36Case4 Q) (hext : A36Extra Q)
    (htype : Type3312R (ModO2 B)) (hO1 : CFSG.oddCore Q ≠ ⊥) {p : ℕ} (hp : p.Prime)
    (hp5 : p ^ 2 % 5 = 1) (hp8 : p % 8 = 3 ∨ p % 8 = 5) (hSL : IsSL2 p (Q ⧸ CFSG.oddCore Q))
    (hB5 : IsSL2 5 ↥B) : OddNorm Q B := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hp8
  have hp3 : 3 < p := by
    rcases (show p = 2 ∨ p = 3 ∨ 3 < p by have := hp.two_le; omega) with h | h | h
    · exact absurd h hp2
    · subst h
      norm_num at hp5
    · exact h
  have hp5' : 5 ≤ p := by
    rcases (show p = 4 ∨ 5 ≤ p by omega) with h | h
    · subst h
      exact absurd hp (by norm_num)
    · exact h
  have hOodd := odd_card_oddCore (Q := Q)
  have hBO : B ⊓ CFSG.oddCore Q = ⊥ := inf_oddCore_eq_bot htype
  obtain ⟨eB⟩ := hB5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hperf, z, hzB, hz2, hz1, hzuniq⟩ := sl2_data (p := 5) le_rfl eB
  have hzO : z ∉ CFSG.oddCore Q := fun h => hz1 (by
    have : z ∈ B ⊓ CFSG.oddCore Q := ⟨hzB, h⟩
    rwa [hBO, Subgroup.mem_bot] at this)
  have huniq := fun t t' (ht : t * t = 1) (ht' : t' * t' = 1) (htO : t ∉ CFSG.oddCore Q)
    (ht'O : t' ∉ CFSG.oddCore Q) => inv_mul_mem_of_isSL2 hp2 hSL ht ht' htO ht'O
  have hZodd := odd_card_center hcomm hext hO1 hz2 hzO huniq
  have : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hperf
  have hzF : z ∉ CFSG.fittingSubgroup Q := by rw [hcomm.1]; exact hzO
  have hCz := le_centralizer_of_fitting hcomm hcase hext hzB hz2 hzF
  rw [hcomm.1] at hCz
  have hOsolv : Group.IsSolvable ↥(CFSG.oddCore Q) := by
    have : Group.IsNilpotent ↥(CFSG.fittingSubgroup Q) := inferInstance
    rw [hcomm.1] at this
    infer_instance
  have hBC := le_centralizer_of_unique hzB hz2 hz1 hzuniq
  have hMc := characteristic_sup huniq hz2 hzO
  obtain ⟨eSL⟩ := hSL
  have hw2 : eSL (z : Q ⧸ CFSG.oddCore Q) * eSL (z : Q ⧸ CFSG.oddCore Q) = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul, hz2, QuotientGroup.mk_one, map_one]
  have hw1 : eSL (z : Q ⧸ CFSG.oddCore Q) ≠ 1 := fun h => hzO (by
    rwa [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h)
  have hMeq : CFSG.oddCore Q ⊔ Subgroup.zpowers z = (Subgroup.center _).comap
      (eSL.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore Q))) := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · intro o ho
        show eSL (o : Q ⧸ CFSG.oddCore Q) ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
        rw [(QuotientGroup.eq_one_iff o).mpr ho, map_one]
        exact Subgroup.one_mem _
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap, center_eq_zpowers hp2 hw2 hw1]
        exact Subgroup.mem_zpowers _
    · intro x hx
      rw [Subgroup.mem_comap, center_eq_zpowers hp2 hw2 hw1, mem_zpowers_iff_of_sq hw2] at hx
      rcases hx with h | h
      · have h' : eSL (x : Q ⧸ CFSG.oddCore Q) = 1 := h
        rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h'
        exact Subgroup.mem_sup_left h'
      · have h' : eSL (x : Q ⧸ CFSG.oddCore Q) = eSL (z : Q ⧸ CFSG.oddCore Q) := h
        rw [eSL.injective.eq_iff, QuotientGroup.eq] at h'
        have hx : x = z * (x⁻¹ * z)⁻¹ := by group
        rw [hx]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
          (Subgroup.mem_sup_left (Subgroup.inv_mem _ h'))
  have hQ : IsPSL 2 p 1 (Q ⧸ (CFSG.oddCore Q ⊔ Subgroup.zpowers z)) :=
    isPSL_of_surjective hp5' _ (eSL.surjective.comp (QuotientGroup.mk'_surjective _)) _ hMeq
  have hBM : ∀ x ∈ B, x ∈ CFSG.oddCore Q ⊔ Subgroup.zpowers z ↔ x = 1 ∨ x = z := by
    intro x hxB
    constructor
    · intro hx
      rw [hMeq, Subgroup.mem_comap, center_eq_zpowers hp2 hw2 hw1, mem_zpowers_iff_of_sq hw2]
        at hx
      rcases hx with h | h
      · left
        have h' : eSL (x : Q ⧸ CFSG.oddCore Q) = 1 := h
        rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h'
        have : x ∈ B ⊓ CFSG.oddCore Q := ⟨hxB, h'⟩
        rwa [hBO, Subgroup.mem_bot] at this
      · right
        have h' : eSL (x : Q ⧸ CFSG.oddCore Q) = eSL (z : Q ⧸ CFSG.oddCore Q) := h
        rw [eSL.injective.eq_iff, QuotientGroup.eq] at h'
        have : x⁻¹ * z ∈ B ⊓ CFSG.oddCore Q := ⟨B.mul_mem (B.inv_mem hxB) hzB, h'⟩
        rw [hBO, Subgroup.mem_bot] at this
        calc x = x * (x⁻¹ * z) := by rw [this, mul_one]
          _ = z := by group
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hN := oddNorm_psl2_alt5 hNorm hFour hOut hp hp3 hp8 hQ (isAlt_five_map eB hzB hz2 hz1 hBM)
  intro A S hInn hS hSB d hd hodd
  have hSz : ∀ s ∈ S, s z = z := by
    intro s hs
    have hsB := mem_stabilizer_subgroup_iff.mp (hSB hs)
    have hszB : s z ∈ B := hsB ▸ ⟨z, hzB, rfl⟩
    rcases hzuniq (s z) hszB (by rw [← map_mul, hz2, map_one]) with h | h
    · exfalso
      apply hz1
      apply s.injective
      rw [h, map_one]
    · exact h
  have hdz := fix_z hZodd hOodd huniq hS hz2 hzO (conj_mem_of_fix hInn hS hz2 hSz) hd.1
  have hle := map_le_sup_of_oddNorm_quot hN hInn hS hSB hd hodd
  have hle' : B.map d.toMonoidHom ≤ B ⊔ CFSG.oddCore Q := by
    refine hle.trans (sup_le le_sup_left (sup_le le_sup_right ?_))
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_sup_left hzB
  rw [mem_stabilizer_subgroup_iff]
  exact map_eq_of_le_sup hOsolv hperf hBC hCz hdz hle'

end CFSG.Quasithin.H13.L3312.NQ

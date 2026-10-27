module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Kbar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem ThreeNat.card_dvd_of_seven (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7) :
    Nat.card ↥A ∣ 336 * Nat.card ↥L := by
  obtain ⟨N, hNA, hLN, _hfix, hcomm, hdisj, hsup, hKbar⟩ :=
    ThreeNat.structure_of_seven h h7
  have hNinf : N ⊓ (L ⊔ s1t3KBar A L) = L := by
    have hKnorm : s1t3KBar A L ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
      rw [Subgroup.le_normalizer_iff]
      intro k hk l hl
      have h := hcomm l (hLN hl) k hk
      rw [← h, mul_assoc, mul_inv_cancel, mul_one]
      exact hl
    refine le_antisymm ?_ fun x hx => ⟨hLN hx, Subgroup.mem_sup_left hx⟩
    intro x hx
    obtain ⟨hxN, hxsup⟩ := Subgroup.mem_inf.mp hx
    have hxmul : x ∈ (↑(L ⊔ s1t3KBar A L) : Set (MulAut W)) := hxsup
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L (s1t3KBar A L) hKnorm,
      Set.mem_mul] at hxmul
    obtain ⟨l, hl, k, hk, hlk⟩ := hxmul
    have hk_eq : k = l⁻¹ * x := by
      rw [← hlk]
      exact (inv_mul_cancel_left l k).symm
    have hkN : k ∈ N := by
      rw [hk_eq]
      exact N.mul_mem (N.inv_mem (hLN hl)) hxN
    have hkbot : k ∈ (⊥ : Subgroup (MulAut W)) := by
      have : k ∈ N ⊓ s1t3KBar A L := ⟨hkN, hk⟩
      rwa [hdisj] at this
    rw [Subgroup.mem_bot.mp hkbot, mul_one] at hlk
    rwa [← hlk]
  have hthree : ∀ x y z : ↥N, x⁻¹ * y ∈ L.subgroupOf N ∨ x⁻¹ * z ∈ L.subgroupOf N ∨
      y⁻¹ * z ∈ L.subgroupOf N := by
    intro x y z
    have hmem := ThreeNat.index_kBar_le_two h h7 (hNA x.2) (hNA y.2) (hNA z.2)
    have key : ∀ w : ↥N, (w : MulAut W) ∈ L ⊔ s1t3KBar A L → w ∈ L.subgroupOf N := by
      intro w hw
      refine Subgroup.mem_subgroupOf.mpr ?_
      have : (w : MulAut W) ∈ N ⊓ (L ⊔ s1t3KBar A L) := ⟨w.2, hw⟩
      rwa [hNinf] at this
    rcases hmem with hmem | hmem | hmem
    · exact Or.inl (key _ (by simpa using hmem))
    · exact Or.inr (Or.inl (key _ (by simpa using hmem)))
    · exact Or.inr (Or.inr (key _ (by simpa using hmem)))
  have hLidx : (L.subgroupOf N).index ≤ 2 := by
    rcases s16t3_index_eq_two_of_thirds (L.subgroupOf N) hthree with htop | hidx
    · rw [htop, Subgroup.index_top]
      norm_num
    · rw [hidx]
  have hcardL : Nat.card ↥(L.subgroupOf N) = Nat.card ↥L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv
  have hNdvd : Nat.card ↥N ∣ 2 * Nat.card ↥L := by
    have hidx_ne : (L.subgroupOf N).index ≠ 0 := (L.subgroupOf N).index_ne_zero_of_finite
    have hidx : (L.subgroupOf N).index = 1 ∨ (L.subgroupOf N).index = 2 := by omega
    have hcard : Nat.card ↥N = Nat.card ↥(L.subgroupOf N) * (L.subgroupOf N).index :=
      (L.subgroupOf N).card_mul_index.symm
    rcases hidx with hidx | hidx
    · rw [hcard, hidx, mul_one, hcardL]
      exact dvd_mul_left _ _
    · rw [hcard, hidx, hcardL, mul_comm]
  have hKdvd : Nat.card ↥(s1t3KBar A L) ∣ 168 := by
    rcases hKbar with hK | hK | ⟨hK, _⟩
    · rw [hK]
      norm_num
    · rw [hK]
      norm_num
    · rw [hK]
  let φ : ↥N × ↥(s1t3KBar A L) →* ↥A :=
    { toFun := fun p => ⟨(p.1 : MulAut W) * (p.2 : MulAut W),
        A.mul_mem (hNA p.1.2) (Subgroup.mem_inf.mp p.2.2).1⟩
      map_one' := by ext; simp
      map_mul' := by
        intro p q
        apply Subtype.ext
        show ((p.1 : MulAut W) * (q.1 : MulAut W)) * ((p.2 : MulAut W) * (q.2 : MulAut W))
            = ((p.1 : MulAut W) * (p.2 : MulAut W)) * ((q.1 : MulAut W) * (q.2 : MulAut W))
        calc ((p.1 : MulAut W) * (q.1 : MulAut W)) * ((p.2 : MulAut W) * (q.2 : MulAut W))
            = (p.1 : MulAut W) * ((q.1 : MulAut W) * (p.2 : MulAut W)) * (q.2 : MulAut W) := by
              group
          _ = (p.1 : MulAut W) * ((p.2 : MulAut W) * (q.1 : MulAut W)) * (q.2 : MulAut W) := by
              rw [hcomm (q.1 : MulAut W) q.1.2 (p.2 : MulAut W) p.2.2]
          _ = ((p.1 : MulAut W) * (p.2 : MulAut W)) * ((q.1 : MulAut W) * (q.2 : MulAut W)) := by
              group }
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    refine le_antisymm le_top ?_
    have hNrange : N.subgroupOf A ≤ φ.range := by
      rintro x hx
      refine ⟨(⟨(x : MulAut W), Subgroup.mem_subgroupOf.mp hx⟩, 1), ?_⟩
      ext
      simp [φ]
    have hKrange : (s1t3KBar A L).subgroupOf A ≤ φ.range := by
      rintro x hx
      refine ⟨(1, ⟨(x : MulAut W), Subgroup.mem_subgroupOf.mp hx⟩), ?_⟩
      ext
      simp [φ]
    have hKA : s1t3KBar A L ≤ A := fun x hx => (Subgroup.mem_inf.mp hx).1
    have h := sup_le hNrange hKrange
    rw [← Subgroup.subgroupOf_sup hNA hKA, hsup, Subgroup.subgroupOf_self] at h
    exact h
  have hAdvd : Nat.card ↥A ∣ Nat.card ↥N * Nat.card ↥(s1t3KBar A L) := by
    have := Subgroup.card_dvd_of_surjective (f := φ) hsurj
    rwa [Nat.card_prod] at this
  refine hAdvd.trans ?_
  have h336 : (2 * Nat.card ↥L) * 168 = 336 * Nat.card ↥L := by ring
  exact h336 ▸ mul_dvd_mul hNdvd hKdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

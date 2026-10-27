module

public import CFSG.RankThree.PartTwo.KFacts.K426McL

public section

namespace CFSG.RankThree.PartTwo.KFacts.K426Rest

open Subgroup CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier

theorem centralizer_pow_eq {G : Type*} [Group G] {y : G} (hy : y ^ 3 = 1) {e : ℕ}
    (he : e = 1 ∨ e = 2) : centralizer {y ^ e} = centralizer {y} := by
  rcases he with rfl | rfl
  · rw [pow_one]
  · refine le_antisymm (centralizer_pow_two_le hy) fun z hz => ?_
    rw [mem_centralizer_singleton_iff] at hz ⊢
    exact (Commute.pow_right hz 2)

theorem card_centralizer_conj {G : Type*} [Group G] {P : Subgroup G} {y k : G} (hk : k ∈ P)
    (hy : y ^ 3 = 1) {e : ℕ} (he : e = 1 ∨ e = 2) :
    Nat.card (centralizer {k * y ^ e * k⁻¹} ⊓ P : Subgroup G) =
      Nat.card (centralizer {y} ⊓ P : Subgroup G) := by
  have hmap : (centralizer {y} ⊓ P).map (MulAut.conj k).toMonoidHom =
      centralizer {k * y ^ e * k⁻¹} ⊓ P := by
    rw [← centralizer_pow_eq hy he]
    ext w
    simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨z, ⟨hzc, hzP⟩, rfl⟩
      refine ⟨?_, P.mul_mem (P.mul_mem hk hzP) (P.inv_mem hk)⟩
      calc k * z * k⁻¹ * (k * y ^ e * k⁻¹) = k * (z * y ^ e) * k⁻¹ := by group
        _ = k * (y ^ e * z) * k⁻¹ := by rw [hzc]
        _ = k * y ^ e * k⁻¹ * (k * z * k⁻¹) := by group
    · rintro ⟨hwc, hwP⟩
      refine ⟨k⁻¹ * w * k, ⟨?_, P.mul_mem (P.mul_mem (P.inv_mem hk) hwP) hk⟩, by group⟩
      calc k⁻¹ * w * k * y ^ e = k⁻¹ * (w * (k * y ^ e * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * y ^ e * k⁻¹) * w) * k := by rw [hwc]
        _ = y ^ e * (k⁻¹ * w * k) := by group
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj k).injective]


theorem card_centralizer_mclP {x : Equiv.Perm (Fin 275)} (hx : x ∈ mclP) (hxo : orderOf x = 3) :
    Nat.card (centralizer {x} ⊓ mclP : Subgroup (Equiv.Perm (Fin 275))) = 29160 ∨
      Nat.card (centralizer {x} ⊓ mclP : Subgroup (Equiv.Perm (Fin 275))) = 972 := by
  obtain ⟨k, hk, j, hj, e, he, rfl⟩ := exists_conj_rep mcl3Q_le card_mcl3Q
    (fun j => permOfArr 275 mcl3Lines[j]!) (fun c => permOfArr 275 mcl3Lines[c]!)
    (fun j => permOfArr 275 mcl3Trans[j]!) (fun j => mcl3Rec.getD j 0) (r := 148)
    (fun g hg hg3 => mcl3_lines hg hg3) (fun j hj => mcl3_trans hj) hx hxo
  have hrec : mcl3Rec.getD j 0 < 2 := of_decide_eq_true (allLt_spec mcl3_lines_check.2.2.2 hj)
  have hcube := (linesOK3_line mcl3_lines_check.1 (lt_trans hrec (by norm_num : 2 < 148))).2
  rw [card_centralizer_conj hk hcube he]
  rcases (by omega : mcl3Rec.getD j 0 = 0 ∨ mcl3Rec.getD j 0 = 1) with h | h
  · left
    rw [h, ← mcl3_caseA.1]
    exact mcl3_caseA.2
  · right
    rw [h, ← mcl3_caseB.1]
    exact mcl3_caseB.2

theorem card_centralizer_of_mulEquiv {G G' : Type*} [Group G] [Group G'] {P : Subgroup G'}
    (e : G ≃* P) (x : G) :
    Nat.card (centralizer {x}) = Nat.card (centralizer {(e x : G')} ⊓ P : Subgroup G') := by
  have hι : Function.Injective (P.subtype.comp e.toMonoidHom) :=
    Subtype.val_injective.comp e.injective
  have hmap : (centralizer {x}).map (P.subtype.comp e.toMonoidHom) =
      centralizer {(e x : G')} ⊓ P := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z * x = x * z := mem_centralizer_singleton_iff.mp hz
      refine mem_inf.2 ⟨?_, (e z).2⟩
      rw [mem_centralizer_singleton_iff]
      change ((e z : P) : G') * (e x : P) = (e x : P) * (e z : P)
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hz']
    · intro hw
      obtain ⟨hwc, hwP⟩ := mem_inf.1 hw
      rw [mem_centralizer_singleton_iff] at hwc
      refine ⟨e.symm ⟨w, hwP⟩, mem_centralizer_singleton_iff.mpr ?_, ?_⟩
      · apply e.injective
        apply Subtype.ext
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul]
        exact hwc
      · change ((e (e.symm ⟨w, hwP⟩) : P) : G') = w
        rw [MulEquiv.apply_symm_apply]
  rw [← hmap, Subgroup.card_map_of_injective hι]

theorem card_centralizer_all_of_mulEquiv {G G' : Type*} [Group G] [Group G'] {P : Subgroup G'}
    (e : G ≃* P) (h : ∀ x ∈ P, orderOf x = 3 →
      Nat.card (centralizer {x} ⊓ P : Subgroup G') = 29160 ∨
        Nat.card (centralizer {x} ⊓ P : Subgroup G') = 972) :
    ∀ x : G, orderOf x = 3 →
      Nat.card (centralizer {x}) = 29160 ∨ Nat.card (centralizer {x}) = 972 := by
  intro x hx
  have hXo : orderOf ((e x : P) : G') = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hx
  rw [card_centralizer_of_mulEquiv e x]
  exact h _ (e x).2 hXo

theorem mclThreeCentralizerCard : ∀ x : Blueprint.NativeSporadic.McL, orderOf x = 3 →
    Nat.card (centralizer {x}) = 29160 ∨ Nat.card (centralizer {x}) = 972 :=
  card_centralizer_all_of_mulEquiv mclPermEquiv fun _ hx hxo => card_centralizer_mclP hx hxo

end CFSG.RankThree.PartTwo.KFacts.K426Rest

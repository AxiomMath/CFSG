module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.H13.L8211G

variable {X Y : Type} [Group X] [Group Y]

theorem comap_pCore_eq_of_surj {f : X →* Y}
    (hf : Function.Surjective f) (hk : f.ker ≤ CFSG.pCore 2 X)
    (hmap : (CFSG.pCore 2 X).map f = CFSG.pCore 2 Y) :
    (CFSG.pCore 2 Y).comap f = CFSG.pCore 2 X := by
  ext x
  constructor
  · intro hx
    have h1 : f x ∈ (CFSG.pCore 2 X).map f := by
      rw [hmap]
      exact hx
    obtain ⟨o, ho, hof⟩ := Subgroup.mem_map.mp h1
    have hxo : o⁻¹ * x ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hof, inv_mul_cancel]
    have h2 := (CFSG.pCore 2 X).mul_mem ho (hk hxo)
    simpa using h2
  · intro hx
    rw [Subgroup.mem_comap, ← hmap]
    exact Subgroup.mem_map_of_mem f hx

theorem card_quot_pCore_eq_of_surj [Finite X] [Finite Y] {f : X →* Y}
    (hf : Function.Surjective f) (hk : f.ker ≤ CFSG.pCore 2 X)
    (hmap : (CFSG.pCore 2 X).map f = CFSG.pCore 2 Y) :
    Nat.card (X ⧸ CFSG.pCore 2 X) = Nat.card (Y ⧸ CFSG.pCore 2 Y) := by
  have hcomap := comap_pCore_eq_of_surj hf hk hmap
  let g : X →* Y ⧸ CFSG.pCore 2 Y := (QuotientGroup.mk' (CFSG.pCore 2 Y)).comp f
  have hgs : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hker : g.ker = CFSG.pCore 2 X := by
    rw [← hcomap]
    ext x
    simp [g, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have e : X ⧸ g.ker ≃* Y ⧸ CFSG.pCore 2 Y := QuotientGroup.quotientKerEquivOfSurjective g hgs
  have e2 : X ⧸ CFSG.pCore 2 X ≃* Y ⧸ CFSG.pCore 2 Y :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans e
  exact Nat.card_congr e2.toEquiv

theorem card_quot_eq_two_pow {V : Type} [Group V] [Finite V] (W : Subgroup V) {a b : ℕ}
    (hV : Nat.card V = 2 ^ a) (hW : Nat.card W = 2 ^ b) (hab : b ≤ a) :
    Nat.card (V ⧸ W) = 2 ^ (a - b) := by
  have h := W.card_eq_card_quotient_mul_card_subgroup
  rw [hV, hW] at h
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : 0 < 2) b)
  rw [← h, pow_sub_mul_pow 2 hab]

theorem nonempty_mulEquiv_fin_of_card_two_pow {Q : Type} [CommGroup Q] [Finite Q]
    (hQ : ∀ q : Q, q ^ 2 = 1) {n : ℕ} (hcard : Nat.card Q = 2 ^ n) :
    Nonempty (Q ≃* Multiplicative (Fin n → ZMod 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := Q)
    (fun a b => mul_comm a b) hQ hcard

end CFSG.Quasithin.H13.L8211G

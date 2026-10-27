module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.C126A5PermBasic

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G]

structure FamData (H T V : Subgroup G) (hV : IsElemAbelian 2 V) where
  L : Subgroup (MulAut (IntMod V hV))
  θ : ↥L ≃* Perm (Fin 5)
  β : ↥(commV L) ≃* Multiplicative (evenWeight 5)
  hβ : ∀ (h : ↥L) (u : ↥(commV L)) (hu : (h : MulAut (IntMod V hV)) (u : IntMod V hV) ∈ commV L)
    (i : Fin 5),
    ((Multiplicative.toAdd (β ⟨(h : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩) :
        evenWeight 5) : Fin 5 → ZMod 2) i =
      ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) ((θ h)⁻¹ i)
  π : Perm (Fin 5)
  C : Subgroup (MulAut (IntMod V hV))
  C_card : Nat.card C = 3
  C_le : C ≤ L
  C_θ : ∀ φ ∈ C, ∃ hφ : φ ∈ L, θ ⟨φ, hφ⟩ ∈ Subgroup.closure {cyc3 π}
  L_J : L ≤ autI hV (thompsonJ H)
  J_N : autI hV (thompsonJ H) ≤ Subgroup.normalizer (L : Set (MulAut (IntMod V hV)))
  JT_C : autI hV (thompsonJ T) ≤ Subgroup.normalizer (C : Set (MulAut (IntMod V hV)))
  baum_C : autI hV (baum T) ≤ Subgroup.normalizer (C : Set (MulAut (IntMod V hV)))
  gen_L : ∀ X : Subgroup (MulAut (IntMod V hV)), autI hV T ≤ X → C ≤ X → L ≤ X
  gen_J : ∀ X : Subgroup (MulAut (IntMod V hV)), autI hV T ≤ X → L ≤ X →
    autI hV (thompsonJ H) ≤ X
  t_lift : ∃ φ ∈ autI hV (thompsonJ T), ∃ hφ : φ ∈ L, θ ⟨φ, hφ⟩ = swap (π 2) (π 3)

theorem autI_le_normalizer_autI {H K V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hK : H ≤ Subgroup.normalizer (K : Set G)) :
    autI hV H ≤ Subgroup.normalizer (autI hV K : Set (MulAut (IntMod V hV))) := by
  intro φ hφ
  obtain ⟨g, hgH, rfl⟩ := (mem_autI hV).1 hφ
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨k, hkK, rfl⟩ := (mem_autI hV).1 hn
  refine (mem_autI hV).2 ⟨g * k * g⁻¹, ?_, by simp [map_mul, map_inv]⟩
  have := (Subgroup.mem_normalizer_iff.1 (hK hgH) (k : G)).1 hkK
  simpa using this

theorem card_eq_eight_of_isSylowTwoOf {Y : Type*} [Group Y] [Finite Y] {P L : Subgroup Y}
    (hP : IsSylowTwoOf P L) (hL : Nat.card ↥L = 120) : Nat.card ↥P = 8 := by
  obtain ⟨hle, hp, hodd⟩ := hP
  change ¬ 2 ∣ P.relIndex L at hodd
  obtain ⟨a, ha⟩ := hp.exists_card_eq
  have h := Subgroup.relIndex_mul_card P L
  rw [inf_eq_left.2 hle, hL, ha] at h
  have hr : 1 ≤ P.relIndex L := Nat.pos_of_ne_zero fun h0 => by simp [h0] at h
  have ha7 : a < 7 := by
    by_contra hcon
    have : 2 ^ 7 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  have ha3 : a = 3 := by
    interval_cases a <;> (try simp at h) <;> omega
  rw [ha, ha3]
  norm_num

end CFSG.Quasithin.C126.A5

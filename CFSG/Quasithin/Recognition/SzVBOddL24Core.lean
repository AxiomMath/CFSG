module

public import CFSG.Quasithin.Recognition.SzVBOddL24Perm
public import CFSG.Quasithin.Recognition.SzVBOddL24Orbit

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem core_false_pair [Finite G] {P S V : Subgroup G} {z y t : G}
    (hK : KleinData P V z) (hW : IsElemAbelian 2 (conjClosure V P))
    (hS_le : S ≤ P) (hS : IsPGroup 2 S) (hSV : S ≤ Subgroup.normalizer (V : Set G))
    (hS_trans : ∀ U U' : ConjSet P V, U ≠ ConjSet.base P V → U' ≠ ConjSet.base P V →
      ∃ s : ↥P, (s : G) ∈ S ∧ s • U = U')
    (hcard : Nat.card (ConjSet P V) = 5)
    (hyP : y ∈ P) (hy2 : y * y = 1) (hy : (⟨y, hyP⟩ : ↥P) ∉ kerAct P V)
    (hyV : y ∈ Subgroup.normalizer (V : Set G))
    (htP : t ∈ P) (htV : t ∈ Subgroup.normalizer (V : Set G))
    (hτ1 : MulAction.toPermHom ↥P (ConjSet P V) ⟨t, htP⟩ ≠ 1)
    (hτ3 : (MulAction.toPermHom ↥P (ConjSet P V) ⟨t, htP⟩) ^ 3 = 1)
    (hcomm : ∀ w ∈ conjClosure V P, (t * y * t⁻¹) * (y * w * y⁻¹ * w⁻¹) * (t * y * t⁻¹)⁻¹ =
      y * w * y⁻¹ * w⁻¹) : False := by
  set ρ := MulAction.toPermHom ↥P (ConjSet P V) with hρ
  set ω : ConjSet P V := ConjSet.base P V with hω
  have hyP' : (⟨y, hyP⟩ : ↥P) * ⟨y, hyP⟩ = 1 := Subtype.ext hy2
  have hm2 : ρ ⟨y, hyP⟩ * ρ ⟨y, hyP⟩ = 1 := by rw [← map_mul, hyP', map_one]
  have hm1 : ρ ⟨y, hyP⟩ ≠ 1 := fun h => hy (MonoidHom.mem_ker.mpr h)
  have hfix : ∀ (x : G) (hx : x ∈ P), x ∈ Subgroup.normalizer (V : Set G) →
      ρ ⟨x, hx⟩ ω = ω := fun x hx hxV =>
    Subtype.ext (OddAux.conjSub_eq_of_mem_normalizer' hxV)
  have hmω : ρ ⟨y, hyP⟩ ω = ω := hfix y hyP hyV
  have hτω : ρ ⟨t, htP⟩ ω = ω := hfix t htP htV
  have hτ3' : ρ ⟨t, htP⟩ * ρ ⟨t, htP⟩ * ρ ⟨t, htP⟩ = 1 := by
    rw [← pow_three']
    exact hτ3
  obtain ⟨U, h1, h2, h3⟩ := perm_core hcard ω (ρ ⟨y, hyP⟩) (ρ ⟨t, htP⟩) hm2 hm1 hmω hτω hτ1 hτ3'
  have hy'P : t * y * t⁻¹ ∈ P := P.mul_mem (P.mul_mem htP hyP) (P.inv_mem htP)
  have hconj : (⟨t * y * t⁻¹, hy'P⟩ : ↥P) = ⟨t, htP⟩ * ⟨y, hyP⟩ * ⟨t, htP⟩⁻¹ := rfl
  have horb := orbit_of_comm hK hW hS_le hS hSV hS_trans (by rw [hcard]; decide)
    (by rw [hcard]) (e := ⟨y, hyP⟩) (e' := ⟨t * y * t⁻¹, hy'P⟩) hcomm U
  have hact : ∀ (e : ↥P) (U : ConjSet P V), e • U = ρ e U := fun _ _ => rfl
  simp only [hact] at horb
  rw [hconj] at horb
  simp only [map_mul, map_inv] at horb
  rcases horb with h | h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h

theorem core_false [Finite G] {P S V N : Subgroup G} {z y t : G}
    (hK : KleinData P V z) (hW : IsElemAbelian 2 (conjClosure V P))
    (hS_le : S ≤ P) (hS : IsPGroup 2 S) (hSV : S ≤ Subgroup.normalizer (V : Set G))
    (hS_trans : ∀ U U' : ConjSet P V, U ≠ ConjSet.base P V → U' ≠ ConjSet.base P V →
      ∃ s : ↥P, (s : G) ∈ S ∧ s • U = U')
    (hcard : Nat.card (ConjSet P V) = 5)
    (hNS : N ≤ S) (hquad : ⁅⁅conjClosure V P, N⁆, N⁆ = ⊥)
    (hyN : y ∈ N) (hy2 : y * y = 1) (hyP : y ∈ P) (hy : (⟨y, hyP⟩ : ↥P) ∉ kerAct P V)
    (htP : t ∈ P) (htN : conjSub t N = N) (htV : t ∈ Subgroup.normalizer (V : Set G))
    (hτ1 : MulAction.toPermHom ↥P (ConjSet P V) ⟨t, htP⟩ ≠ 1)
    (hτ3 : (MulAction.toPermHom ↥P (ConjSet P V) ⟨t, htP⟩) ^ 3 = 1) : False := by
  have hy'N : t * y * t⁻¹ ∈ N := by
    have := mul_mem_conjSub (g := t) hyN
    rwa [htN] at this
  refine core_false_pair hK hW hS_le hS hSV hS_trans hcard hyP hy2 hy (hSV (hNS hyN)) htP htV
    hτ1 hτ3 fun w hw => ?_
  have h1 : (y * w * y⁻¹ * w⁻¹) ∈ ⁅conjClosure V P, N⁆ := by
    rw [Subgroup.commutator_comm (conjClosure V P) N]
    exact Subgroup.commutator_mem_commutator hyN hw
  have h2 : ((t * y * t⁻¹) * (y * w * y⁻¹ * w⁻¹) * (t * y * t⁻¹)⁻¹ *
      (y * w * y⁻¹ * w⁻¹)⁻¹) ∈ (⊥ : Subgroup G) := by
    rw [← hquad, Subgroup.commutator_comm ⁅conjClosure V P, N⁆ N]
    exact Subgroup.commutator_mem_commutator hy'N h1
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp h2)

end CFSG.Quasithin.SzVB

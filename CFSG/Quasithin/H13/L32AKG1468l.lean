module

public import CFSG.Quasithin.H13.L32AKG1468k

public section

namespace CFSG.Quasithin.H13.KGBlk

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

omit [Group G] in
theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem autOn_mono {H H' V : Subgroup G} (h : H ≤ H') : autOn H V ≤ autOn H' V :=
  CFSG.Quasithin.AutOn.autOn_mono h

variable [Finite G] {Y R M I : Subgroup G}

theorem false_of_borel {V : Subgroup G} {X : Subgroup (MulAut ↥V)} (hX : X ≤ autOn (M ⊓ I) V)
    (θ : ↥X →* alternatingGroup (Fin 5)) (hθ : Function.Surjective θ)
    (hB : IsBorelIn (autOn I V) (autOn (M ⊓ I) V)) : False := by
  obtain ⟨S, hS, hEq⟩ := hB
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact false_of_le_normalizer_sylow hS (hX.trans (hEq.le.trans inf_le_left))
    (hX.trans (hEq.le.trans inf_le_right)) card_alt_five θ hθ

omit [Finite G] in
theorem false_of_partition {V : Subgroup G} {x : MulAut ↥V}
    (hx : x ∈ autOn (oTwoUpper (I ⊓ M)) V) (hx5 : orderOf x = 5)
    (e : ↥(autOn (I ⊔ R) V) ≃* Equiv.Perm (Fin 7)) {sizes : Multiset ℕ}
    (hs : ∀ n ∈ sizes, n ≤ 4) (hcard : Multiset.card sizes ≤ 4) {P : Finset (Finset (Fin 7))}
    (hP : IsPartitionOfType P sizes)
    (hmap : ((autOn (M ⊓ I) V).subgroupOf (autOn (I ⊔ R) V)).map e.toMonoidHom =
      MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7)) : False := by
  have ha1 : x ∈ autOn (M ⊓ I) V := autOn_mono oTwoUpper_le_inf hx
  have ha2 : x ∈ autOn (I ⊔ R) V :=
    autOn_mono ((oTwoUpper_le _).trans (inf_le_left.trans le_sup_left)) hx
  have hmem : (⟨x, ha2⟩ : ↥(autOn (I ⊔ R) V)) ∈
      (autOn (M ⊓ I) V).subgroupOf (autOn (I ⊔ R) V) := ha1
  have he : e ⟨x, ha2⟩ ∈ MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7) :=
    hmap ▸ Subgroup.mem_map_of_mem _ hmem
  have hord : orderOf (e ⟨x, ha2⟩) = 5 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx5]
  exact He17.not_stabilizes_partition hs hcard hP hord (Subgroup.mem_inf.mp he).1

omit [Finite G] in
theorem five_dvd_card_inf {a : G} (haB : a ∈ oTwoUpper (I ⊓ M)) (ha5 : orderOf a = 5) :
    5 ∣ Nat.card ↥(M ⊓ I) := by
  have := orderOf_dvd_natCard (⟨a, oTwoUpper_le_inf haB⟩ : ↥(M ⊓ I))
  rwa [Subgroup.orderOf_mk, ha5] at this

theorem false_of_hatA6 (hA : CFSG.Quasithin.IsHatA6Block I) (hidx : M.relIndex I = 15)
    (h5 : 5 ∣ Nat.card ↥(M ⊓ I)) : False := by
  obtain ⟨-, ⟨-, hZ3, ⟨e⟩⟩, -⟩ := hA
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥I))
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hq : Nat.card (↥I ⧸ CFSG.pCore 2 ↥I) = 1080 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥I ⧸ CFSG.pCore 2 ↥I))
    rw [hZ3, Nat.card_congr e.toEquiv, hA6] at h1
    exact h1
  have hI : Nat.card ↥I = 2 ^ a * 1080 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥I)
    rw [hq, ha] at h1
    rw [h1]
    ring
  have hmul := Subgroup.relIndex_mul_card (H := M) (K := I)
  rw [hidx, hI] at hmul
  exact He17.not_five_dvd_of_index (r := 216) (s := 3) (by norm_num) (by linarith) h5

theorem false_of_excA7 (hA : CFSG.Quasithin.IsExcA7Block I) (hidx : M.relIndex I = 35)
    (h5 : 5 ∣ Nat.card ↥(M ⊓ I)) : False := by
  obtain ⟨-, ⟨α, hα, hker⟩, -⟩ := hA
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥I))
  have hq : Nat.card (↥I ⧸ CFSG.pCore 2 ↥I) = 2520 := by
    let e : (↥I ⧸ CFSG.pCore 2 ↥I) ≃* alternatingGroup (Fin 7) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hI : Nat.card ↥I = 2 ^ a * 2520 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥I)
    rw [hq, ha] at h1
    rw [h1]
    ring
  have hmul := Subgroup.relIndex_mul_card (H := M) (K := I)
  rw [hidx, hI] at hmul
  exact He17.not_five_dvd_of_index (r := 504) (s := 7) (by norm_num) (by linarith) h5

omit [Finite G] in
theorem false_of_g2 {V : Subgroup G} {x : MulAut ↥V} (hx : x ∈ autOn (oTwoUpper (I ⊓ M)) V)
    (hx5 : orderOf x = 5) (hg2 : IsG2Two ↥(autOn (I ⊔ R) V)) : False := by
  have hx' : x ∈ autOn (I ⊔ R) V :=
    autOn_mono ((oTwoUpper_le _).trans (inf_le_left.trans le_sup_left)) hx
  have h2 := orderOf_dvd_natCard (⟨x, hx'⟩ : ↥(autOn (I ⊔ R) V))
  rw [Subgroup.orderOf_mk, hx5, hg2.1] at h2
  omega

end CFSG.Quasithin.H13.KGBlk

module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213HatS
public import CFSG.Sporadic.HeldB.InnerClass
public import Certificates.Certificate7167

public section

namespace CFSG.Quasithin.H13.Ch4.HatH

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Quasithin.H13.Ch4.HatChk

variable {n : ℕ}

theorem hatCoreAt_of_card {M : Subgroup (Equiv.Perm (Fin n))} {r : Equiv.Perm (Fin n)}
    {P₁ P₂ : Subgroup (Equiv.Perm (Fin n))} {a m : ℕ}
    (hC : Nat.card ↥(M ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin n)))) = 2 ^ a * m)
    (hm : ¬ 2 ∣ m) (hP₁ : P₁ ≤ M ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin n))))
    (hP₂ : P₂ ≤ M ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin n))))
    (hc₁ : Nat.card P₁ = 2 ^ a) (hc₂ : Nat.card P₂ = 2 ^ a)
    (hab : ∀ A : Subgroup (Equiv.Perm (Fin n)), A ≤ P₁ → A ≤ P₂ →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ 63) :
    HatCoreAt (Equiv.Perm (Fin n)) M r := by
  intro t U S _ _ _ hUc hU _ _ _ _ _ _ _ _ _ _ _ hle
  have hsyl₁ := HatS.isSylowTwoOf_of_card hP₁ hc₁ hC hm
  have hsyl₂ := HatS.isSylowTwoOf_of_card hP₂ hc₂ hC hm
  have h63 := hab U (hle.trans (HatS.pCoreOf_le_of_isSylowTwoOf hsyl₁))
    (hle.trans (HatS.pCoreOf_le_of_isSylowTwoOf hsyl₂)) hUc
  omega

theorem map_conj_le {X : Type} [Group X] {C P : Subgroup X} {d : X} (hd : d ∈ C) (hP : P ≤ C) :
    P.map (MulAut.conj d).toMonoidHom ≤ C := by
  rintro _ ⟨x, hx, rfl⟩
  exact C.mul_mem (C.mul_mem hd (hP hx)) (C.inv_mem hd)

theorem card_map_conj {X : Type} [Group X] (P : Subgroup X) (d : X) :
    Nat.card (P.map (MulAut.conj d).toMonoidHom) = Nat.card P :=
  Subgroup.card_map_of_injective (MulAut.conj d).injective

theorem p0Words_lt : ∀ w ∈ p0Words, ∀ k ∈ w, k < 9 := by decide

theorem p1Words_lt : ∀ w ∈ p1Words, ∀ k ∈ w, k < 9 := by decide

theorem d0Word_lt : ∀ k ∈ d0Word, k < 9 := by decide

theorem d1Word_lt : ∀ k ∈ d1Word, k < 9 := by decide

theorem prod_mem_grp0 {w : List ℕ} (hw : ∀ k ∈ w, k < 9) : (w.map heInnerCP0).prod ∈ heInnerGrp0 :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.subset_closure ⟨k, hw k hk, rfl⟩

theorem prod_mem_grp1 {w : List ℕ} (hw : ∀ k ∈ w, k < 9) : (w.map heInnerCP1).prod ∈ heInnerGrp1 :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.subset_closure ⟨k, hw k hk, rfl⟩

theorem grp0_le :
    heInnerGrp0 ≤ heP ⊓ Subgroup.centralizer ({heGenPerm 0} : Set (Equiv.Perm (Fin 8330))) := by
  have h := heInnerGrp0_le
  rwa [centralizerIn] at h

theorem grp1_le :
    heInnerGrp1 ≤ heP ⊓ Subgroup.centralizer ({heT1P} : Set (Equiv.Perm (Fin 8330))) := by
  have h := heInnerGrp1_le
  rwa [centralizerIn] at h

theorem heP0_le :
    heP0 ≤ heP ⊓ Subgroup.centralizer ({heGenPerm 0} : Set (Equiv.Perm (Fin 8330))) := by
  rw [heP0, Subgroup.closure_le]
  intro g hg
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (Set.mem_setOf_eq ▸ hg)
  exact grp0_le (prod_mem_grp0 (p0Words_lt w hw))

theorem heP1_le :
    heP1 ≤ heP ⊓ Subgroup.centralizer ({heT1P} : Set (Equiv.Perm (Fin 8330))) := by
  rw [heP1, Subgroup.closure_le]
  intro g hg
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (Set.mem_setOf_eq ▸ hg)
  exact grp1_le (prod_mem_grp1 (p1Words_lt w hw))

theorem heD0_mem :
    heD0 ∈ heP ⊓ Subgroup.centralizer ({heGenPerm 0} : Set (Equiv.Perm (Fin 8330))) :=
  grp0_le (prod_mem_grp0 d0Word_lt)

theorem heD1_mem :
    heD1 ∈ heP ⊓ Subgroup.centralizer ({heT1P} : Set (Equiv.Perm (Fin 8330))) :=
  grp1_le (prod_mem_grp1 d1Word_lt)

theorem card_cent0 :
    Nat.card ↥(heP ⊓ Subgroup.centralizer ({heGenPerm 0} : Set (Equiv.Perm (Fin 8330)))) =
      2 ^ 9 * 315 := by
  have h := card_heP_cent0
  rw [centralizerIn] at h
  exact h.trans (by norm_num)

theorem card_cent1 :
    Nat.card ↥(heP ⊓ Subgroup.centralizer ({heT1P} : Set (Equiv.Perm (Fin 8330)))) =
      2 ^ 10 * 21 := by
  have h := card_heP_cent1
  rw [centralizerIn] at h
  exact h.trans (by norm_num)

theorem hatCoreAt_t0 :
    HatCoreAt (Equiv.Perm (Fin 8330)) heP (heGenPerm 0) := by
  obtain ⟨hP, hA, -, -⟩ := Certificates.certificate7167
  exact hatCoreAt_of_card card_cent0 (by decide) heP0_le (map_conj_le heD0_mem heP0_le) hP
    ((card_map_conj _ _).trans hP) hA

theorem hatCoreAt_t1 :
    HatCoreAt (Equiv.Perm (Fin 8330)) heP heT1P := by
  obtain ⟨-, -, hP, hA⟩ := Certificates.certificate7167
  exact hatCoreAt_of_card card_cent1 (by decide) heP1_le (map_conj_le heD1_mem heP1_le) hP
    ((card_map_conj _ _).trans hP) hA

theorem hatCoreAmb_he :
    HatCoreAmb (Equiv.Perm (Fin 8330)) heP := by
  intro z t U S hUM hSM htM hUc hU hS2 hS hUS hzU hzS hz2 hz1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases involution_conj_cases (hUM hzU) (orderOf_eq_prime hz2 hz1) with
    ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · exact HatS.hatCoreAt_conj hc hatCoreAt_t0 t U S hUM hSM htM hUc hU hS2 hS hUS hzU hzS hz2 hz1
  · exact HatS.hatCoreAt_conj hc hatCoreAt_t1 t U S hUM hSM htM hUc hU hS2 hS hUS hzU hzS hz2 hz1

end CFSG.Quasithin.H13.Ch4.HatH

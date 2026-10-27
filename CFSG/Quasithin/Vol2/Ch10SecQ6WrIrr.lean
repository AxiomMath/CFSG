module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WrCl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

@[expose] def c4 : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3

theorem c4_mem : c4 ∈ D8 := by decide

theorem swap02_mem : swap 0 2 ∈ D8 := by decide

set_option maxRecDepth 10000 in
theorem fixO_D8 : ∀ u : Fin 5 → ZMod 2, IsO u → pv c4 u = u → pv (swap 0 2) u = u →
    u = 0 ∨ u = wv 4 := by
  decide +kernel

theorem wrIota_right' (q : Multiplicative (ZMod 2)) (σ : Perm (Fin 5)) : (wrIota q σ).right = 1 :=
  rfl

theorem wrIota_left_self (q : Multiplicative (ZMod 2)) (σ : Perm (Fin 5)) :
    (wrIota q σ).left q = σ := by
  change (Pi.mulSingle q σ : Multiplicative (ZMod 2) → Perm (Fin 5)) q = σ
  rw [Pi.mulSingle_eq_same]

theorem wrIota_left_ne {q q' : Multiplicative (ZMod 2)} (h : q' ≠ q) (σ : Perm (Fin 5)) :
    (wrIota q σ).left q' = 1 := by
  change (Pi.mulSingle q σ : Multiplicative (ZMod 2) → Perm (Fin 5)) q' = 1
  rw [Pi.mulSingle_eq_of_ne h]

theorem zs_ne_one' : (1 : Multiplicative (ZMod 2)) ≠ zs := fun h => zs_ne_one h.symm

theorem wrT_right : wrT.right = zs := rfl

theorem wrT_left (q : Multiplicative (ZMod 2)) : wrT.left q = 1 := rfl

theorem eq_of_fix_Mmod {m : PMod} (hm : m ∈ Mmod) (hfix : ∀ s ∈ S0, gP s m = m) :
    m = 0 ∨ m = m0 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hm
  have h1 : ∀ σ ∈ D8, pv σ a = a := fun σ hσ => by
    have h := hfix _ (wrIota_mem_wrSub hσ 1)
    rw [gP_sumv_base (wrIota_right' 1 σ), wrIota_left_self, wrIota_left_ne zs_ne_one, pv_one] at h
    exact (sumv_inj ((isO_pv _ _).mpr ha) ha h).1
  have ht := hfix wrT (wrT_mem_wrSub _)
  rw [gP_sumv_swap wrT_right, wrT_left, wrT_left, pv_one, pv_one] at ht
  have hab : b = a := (sumv_inj hb ha ht).1
  subst hab
  rcases fixO_D8 b hb (h1 _ c4_mem) (h1 _ swap02_mem) with h | h
  · left
    rw [h]
    funext i j
    simp [sumv]
  · right
    rw [h]
    rfl

theorem eq_of_fix_Nmod {n : PMod} (hn : n ∈ Nmod) (hfix : ∀ s ∈ S0, gP s n = n) :
    n = 0 ∨ n = n0 := by
  have hcol : ∀ j, (fun i => n i j) = 0 ∨ (fun i => n i j) = wv 4 := fun j => by
    have hσ : ∀ σ ∈ D8, pv σ (fun i => n i j) = fun i => n i j := fun σ hσ => by
      funext i
      have h := congrFun (congrFun (hfix _ (wrIota_mem_wrSub hσ 1)) i) j
      rw [gP_base (wrIota_right' 1 σ), wrIota_left_self, wrIota_left_ne zs_ne_one, inv_one,
        Perm.one_apply] at h
      exact h
    exact fixO_D8 _ (hn.2 j) (hσ _ c4_mem) (hσ _ swap02_mem)
  have hrow : ∀ i, n i = 0 ∨ n i = wv 4 := fun i => by
    have hσ : ∀ σ ∈ D8, pv σ (n i) = n i := fun σ hσ => by
      funext j
      have h := congrFun (congrFun (hfix _ (wrIota_mem_wrSub hσ zs)) i) j
      rw [gP_base (wrIota_right' zs σ), wrIota_left_self, wrIota_left_ne zs_ne_one', inv_one,
        Perm.one_apply] at h
      exact h
    exact fixO_D8 _ (hn.1 i) (hσ _ c4_mem) (hσ _ swap02_mem)
  rcases hrow 0 with h0 | h0
  · left
    funext i j
    rcases hcol j with hc | hc
    · exact congrFun hc i
    · exfalso
      have h1 : n 0 j = wv 4 0 := congrFun hc 0
      have h2 : n 0 j = 0 := congrFun h0 j
      rw [h2] at h1
      exact absurd h1 (by decide)
  · right
    funext i j
    change n i j = wv 4 i * wv 4 j
    rcases hcol j with hc | hc
    · have h1 : wv 4 j = 0 := by
        rw [← congrFun h0 j]
        exact congrFun hc 0
      rw [h1, mul_zero]
      exact congrFun hc i
    · have h1 : wv 4 j = 1 := by
        rw [← congrFun h0 j]
        exact (congrFun hc 0).trans (by decide)
      rw [h1, mul_one]
      exact congrFun hc i

theorem exists_fix_of_ne_bot {K : AddSubgroup PMod}
    (hK : ∀ g : SymFiveWrTwo, ∀ k ∈ K, gP g k ∈ K) (hne : K ≠ ⊥) :
    ∃ m ∈ K, m ≠ 0 ∧ ∀ s ∈ S0, gP s m = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction S0 K :=
    { smul := fun s k => ⟨gP s k, hK s k k.2⟩
      one_smul := fun k => Subtype.ext (gP_one k)
      mul_smul := fun s t k => Subtype.ext (gP_mul s t k) }
  have hmod := IsPGroup.card_modEq_card_fixedPoints isPGroup_S0 K
  obtain ⟨k, hk0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hne
  have hk2 : addOrderOf (k : PMod) = 2 := addOrderOf_eq_prime (by
    funext i j
    simp only [Pi.smul_apply, Pi.zero_apply, two_nsmul]
    exact zmod_two_add_self _) (fun h => hk0 (Subtype.ext h))
  have heven : 2 ∣ Nat.card K := by
    have h := AddSubgroup.card_dvd_of_le
      ((AddSubgroup.zmultiples_le (H := K)).mpr k.2)
    rwa [Nat.card_zmultiples, hk2] at h
  by_contra hno
  push Not at hno
  have hsub : MulAction.fixedPoints S0 K ⊆ {0} := fun x hx => by
    by_contra hx0
    obtain ⟨s, hs, hsx⟩ := hno x x.2 (fun h => hx0 (Subtype.ext h))
    exact hsx (congrArg Subtype.val (hx ⟨s, hs⟩))
  have h0 : (0 : K) ∈ MulAction.fixedPoints S0 K := fun s => Subtype.ext (gP_zero s)
  have hfix1 : Nat.card (MulAction.fixedPoints S0 K) = 1 := by
    have heq : MulAction.fixedPoints S0 K = {0} :=
      Set.eq_of_subset_of_subset hsub (Set.singleton_subset_iff.mpr h0)
    rw [heq, Nat.card_unique]
  rw [hfix1] at hmod
  have h3 : Nat.card K % 2 = 1 % 2 := hmod
  have h4 : Nat.card K % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp heven
  omega

theorem Mcl_le_of {K : AddSubgroup PMod} (hKM : K ≤ Mcl)
    (hK : ∀ g : SymFiveWrTwo, ∀ k ∈ K, gP g k ∈ K) (hne : K ≠ ⊥) : Mcl ≤ K := by
  obtain ⟨m, hmK, hm0, hfix⟩ := exists_fix_of_ne_bot hK hne
  rcases eq_of_fix_Mmod (Mcl_le_Mmod (hKM hmK)) hfix with h | h
  · exact absurd h hm0
  · rw [Mcl, AddSubgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    rw [Tv, ← h]
    exact hK _ _ hmK

theorem Ncl_le_of {K : AddSubgroup PMod} (hKN : K ≤ Ncl)
    (hK : ∀ g : SymFiveWrTwo, ∀ k ∈ K, gP g k ∈ K) (hne : K ≠ ⊥) : Ncl ≤ K := by
  obtain ⟨n, hnK, hn0, hfix⟩ := exists_fix_of_ne_bot hK hne
  rcases eq_of_fix_Nmod (Ncl_le_Nmod (hKN hnK)) hfix with h | h
  · exact absurd h hn0
  · rw [Ncl, AddSubgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    rw [Rv, ← h]
    exact hK _ _ hnK

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD

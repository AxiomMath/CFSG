module

public import CFSG.Quasithin.H13.NQCatT513Sym5
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Lift
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M3
public import CFSG.Quasithin.H13.KGFactT3J4Lat
public import CFSG.Quasithin.H13.NQCatT513HallS

public section

namespace CFSG.Quasithin.H13.NQCat.T513P

open CFSG.QuasithinUnique
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Rad
  CFSG.Quasithin.A312M24 CFSG.Quasithin.J4Fam

theorem isSolvable_subgroupOf {G : Type*} [Group G] {K L : Subgroup G} (h : Group.IsSolvable ↥K) :
    Group.IsSolvable ↥(K.subgroupOf L) := by
  let f : ↥(K.subgroupOf L) →* ↥K :=
    { toFun := fun x => ⟨(x : ↥L), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Group.isSolvable_of_isSolvable_injective (f := f) fun x y hxy => ?_
  have h1 : ((f x : ↥K) : G) = ((f y : ↥K) : G) := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext h1)

theorem isSolvable_of_le {G : Type*} [Group G] {K L : Subgroup G} (hKL : K ≤ L)
    (h : Group.IsSolvable ↥L) : Group.IsSolvable ↥K :=
  Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKL)

theorem isSolvable_map {G H : Type*} [Group G] [Group H] (f : G →* H) {K : Subgroup G}
    (h : Group.IsSolvable ↥K) : Group.IsSolvable ↥(K.map f) :=
  Group.isSolvable_of_surjective (f.subgroupMap_surjective K)

theorem index_of_le_M3
    {Z : Subgroup J}
    (hZM : Z ≤ M3) (hZs : Group.IsSolvable ↥Z) {m : ℕ} (hm : Nat.card ↥Z = m * 2 ^ 21) :
    m = 1 ∨ 3 ∣ m := by
  have hF := j4Facts
  have hM := hF.mat
  have hm315 : m ∣ 315 := by
    have h := Subgroup.card_dvd_of_le hZM
    rw [hm, card_M3 hF, show (660602880 : ℕ) = 315 * 2 ^ 21 by norm_num] at h
    exact Nat.dvd_of_mul_dvd_mul_right (by positivity) h
  by_contra hne
  have hcases : m = 5 ∨ m = 7 ∨ m = 35 := by
    have hmem : m ∈ Nat.divisors 315 := Nat.mem_divisors.mpr ⟨hm315, by norm_num⟩
    have hd : Nat.divisors 315 = {1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 315} := by decide
    rw [hd] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  set Z' : Subgroup ↥M3 := Z.subgroupOf M3 with hZ'
  have hZ'c : Nat.card ↥Z' = m * 2 ^ 21 := by
    rw [hZ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv, hm]
  set α : ↥M3 →* MulAut ↥V0 := V0.normalizerMonoidHom with hα
  have hker : α.ker = Dm := by
    ext x
    rw [MonoidHom.mem_ker, hα, normalizerMonoidHom_eq_one_iff', Subgroup.mem_subgroupOf]
  have hsplit := card_map_mul_card_ker_inf α Z'
  rw [hZ'c] at hsplit
  set x := Nat.card ↥(Z'.map α) with hx
  set k := Nat.card ↥(α.ker ⊓ Z') with hk
  have hkD : k ∣ 3932160 := by
    rw [hk, ← card_Dm hF, ← hker]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hkZ : k ∣ m * 2 ^ 21 := ⟨x, by rw [← hsplit]; ring⟩
  have hx168 : x ∣ 168 := by
    have := Subgroup.card_subgroup_dvd_card (Z'.map α)
    rwa [card_mulAut_V0 hM] at this
  have hxZ : x ∣ m * 2 ^ 21 := ⟨k, hsplit.symm⟩
  have hsimp : IsSimpleGroup (MulAut ↥V0) :=
    isSimpleGroup_mulAut_of_subgroup_eight V0 (V0_comm hM) (V0_sq hM) (card_V0 hM)
  have hfin : Finite (MulAut ↥V0) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut_V0 hM]; norm_num)
  have h56 : x ≠ 56 := by
    intro hx56
    have hXi : (Z'.map α).index = 3 := by
      have h := Subgroup.card_mul_index (Z'.map α)
      rw [← hx, hx56, card_mulAut_V0 hM] at h
      omega
    have h1 := index_eq_one_of_simple (Z'.map α)
      (by rw [hXi, card_mulAut_V0 hM]; decide)
    omega
  rcases hcases with rfl | rfl | rfl
  ·
    have hkg : k ∣ 5 * 2 ^ 18 := by
      have := Nat.dvd_gcd hkZ hkD
      rwa [show Nat.gcd (5 * 2 ^ 21) 3932160 = 5 * 2 ^ 18 by norm_num] at this
    have hxg : x ∣ 8 := by
      have := Nat.dvd_gcd hxZ hx168
      rwa [show Nat.gcd (5 * 2 ^ 21) 168 = 8 by norm_num] at this
    have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hkg (by norm_num)
    have hkle : k ≤ 5 * 2 ^ 18 := Nat.le_of_dvd (by norm_num) hkg
    have hxle : x ≤ 8 := Nat.le_of_dvd (by norm_num) hxg
    have hk5 : k = 5 * 2 ^ 18 := by nlinarith
    set W : Subgroup ↥Dm := (α.ker ⊓ Z').subgroupOf Dm with hW
    have hWle : α.ker ⊓ Z' ≤ Dm := hker ▸ inf_le_left
    have hWc : Nat.card ↥W = 5 * 2 ^ 18 := by
      rw [hW, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWle).toEquiv, ← hk, hk5]
    have hWi : W.index = 3 := by
      have h := Subgroup.card_mul_index W
      rw [hWc, card_Dm hF] at h
      omega
    have hWs : Group.IsSolvable ↥W :=
      isSolvable_subgroupOf (isSolvable_of_le inf_le_right (isSolvable_subgroupOf hZs))
    set ρ : ↥Dm →* Equiv.Perm (Fin 5) := (rho3 hF).comp Dm.subtype with hρ
    have h60 : 60 ∣ Nat.card ↥ρ.range := sixty_dvd_card_rho3 hF
    set U : Subgroup ↥ρ.range := W.map ρ.rangeRestrict with hU
    have hUi : U.index ≤ 3 := by
      have h := Subgroup.index_map_dvd W ρ.rangeRestrict_surjective
      rw [hWi] at h
      exact Nat.le_of_dvd (by norm_num) h
    have hUs : Group.IsSolvable ↥U := isSolvable_map ρ.rangeRestrict hWs
    exact false_of_sym5 h60 U hUi hUs
  ·
    have hkg : k ∣ 2 ^ 18 := by
      have := Nat.dvd_gcd hkZ hkD
      rwa [show Nat.gcd (7 * 2 ^ 21) 3932160 = 2 ^ 18 by norm_num] at this
    have hxg : x ∣ 56 := by
      have := Nat.dvd_gcd hxZ hx168
      rwa [show Nat.gcd (7 * 2 ^ 21) 168 = 56 by norm_num] at this
    have hkle : k ≤ 2 ^ 18 := Nat.le_of_dvd (by norm_num) hkg
    have hxle : x ≤ 56 := Nat.le_of_dvd (by norm_num) hxg
    exact h56 (by nlinarith)
  ·
    have hkg : k ∣ 5 * 2 ^ 18 := by
      have := Nat.dvd_gcd hkZ hkD
      rwa [show Nat.gcd (35 * 2 ^ 21) 3932160 = 5 * 2 ^ 18 by norm_num] at this
    have hxg : x ∣ 56 := by
      have := Nat.dvd_gcd hxZ hx168
      rwa [show Nat.gcd (35 * 2 ^ 21) 168 = 56 by norm_num] at this
    have hkle : k ≤ 5 * 2 ^ 18 := Nat.le_of_dvd (by norm_num) hkg
    have hxle : x ≤ 56 := Nat.le_of_dvd (by norm_num) hxg
    exact h56 (by nlinarith)

theorem index_of_solvable_J [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]
    {Z : Subgroup J}
    (hPZ : P0 ≤ Z) (hZs : Group.IsSolvable ↥Z) {m : ℕ} (hm : Nat.card ↥Z = m * Nat.card ↥P0) :
    m = 1 ∨ 3 ∣ m := by
  have hF := j4Facts
  rw [card_P0 hF.mat hF] at hm
  have hHj : Z ≤ Hj → m = 1 ∨ 3 ∣ m := fun hZH => by
    rcases KGT3J4.card_of_le_Hj hPZ hZH with h | ⟨j, hj, hc⟩
    · rw [h, card_Hj hF] at hm
      have : m = 239085 := by omega
      rw [this]
      norm_num
    · rw [hc] at hm
      have hmj : m = memIdx[j]! := (Nat.eq_of_mul_eq_mul_right (by positivity) hm).symm
      have hL : ∀ i < 13, memIdx[i]! = 1 ∨ 3 ∣ memIdx[i]! := by decide
      rw [hmj]
      exact hL j hj
  rcases overgroup_of_solvable hPZ hZs with h | h | h
  · exact hHj h
  · rcases CFSG.Quasithin.J4M2.J4M2Lattice hF hPZ h with h2 | h2 | h2
    · exact hHj h2
    · exact index_of_le_M3 h2 hZs hm
    · rw [h2, CFSG.Quasithin.J4M2.card_M2 hF] at hm
      have : m = 10395 := by omega
      rw [this]
      norm_num
  · exact index_of_le_M3 h hZs hm

theorem cycOddPerm_j4Grp [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    CycOddPerm ↥J fun _ => False :=
  cycOddPerm_of_solvable_overgroups isSylowTwoOf_P0 fun _ hPZ hZs _ hm =>
    index_of_solvable_J hPZ hZs hm

theorem cycOddPerm_j4 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    CycOddPerm (CFSG.Blueprint.NativeSporadic.Carrier .J4) fun _ => False := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .J4 ≃* ↥J := seedEquiv j4Facts.mat
  exact @CycOddPerm.of_equiv ↥J (CFSG.Blueprint.NativeSporadic.Carrier .J4) _ _ _ _ e.symm
    cycOddPerm_j4Grp

end CFSG.Quasithin.H13.NQCat.T513P

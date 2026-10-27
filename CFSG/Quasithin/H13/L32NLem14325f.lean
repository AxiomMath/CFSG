module

public import CFSG.Quasithin.H13.L32NLem14325e
public import CFSG.CharacterTheory.Burnside
public import CFSG.Quasithin.H13.L32NLem14325d

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14325

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem exists_eq_two_pow_mul_three_pow {n i j : ℕ} (h : n ∣ 2 ^ i * 3 ^ j) :
    ∃ a b : ℕ, n = 2 ^ a * 3 ^ b := by
  obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp h
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hz
  exact ⟨a, b, rfl⟩

theorem prime_dvd_of_perfect {X : Subgroup Γ} (hX1 : X ≠ ⊥) (hXp : ⁅X, X⁆ = X) {i j p : ℕ}
    (hp : p.Prime) (hdvd : Nat.card X ∣ 2 ^ i * 3 ^ j * p) :
    p ∣ Nat.card X := by
  by_contra h5
  have hcop : Nat.Coprime (Nat.card X) p := (Nat.Prime.coprime_iff_not_dvd hp).mpr h5 |>.symm
  obtain ⟨a, b, hab⟩ := exists_eq_two_pow_mul_three_pow (hcop.dvd_of_dvd_mul_right hdvd)
  have : Fintype ↥X := Fintype.ofFinite _
  have hsolv : Group.IsSolvable ↥X :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [Fintype.card_eq_nat_card, hab])
  have hcore := (isSolvable_iff_perfectCore_eq_bot X).mp hsolv
  rw [perfectCore_eq_self_of_perfect hXp] at hcore
  exact hX1 hcore

omit [Finite Γ] in
theorem mem_of_subnormal_of_dvd {X Y : Subgroup Γ} (hXY : IsSubnormal X Y) {p : ℕ}
    (hp : p.Prime) (hpX : p ∣ Nat.card X) (hpY : ¬ p ^ 2 ∣ Nat.card Y) {y : Γ} (hy : y ∈ Y)
    (hyp : y ^ p = 1) : y ∈ X := by
  refine mem_of_subnormal_of_pow_eq_one hXY hp ?_ hy (k := 1) (by rwa [pow_one])
  intro hd
  apply hpY
  have hmul := Subgroup.relIndex_mul_card (H := X) (K := Y)
  rw [inf_eq_left.mpr (le_of_isSubnormal hXY)] at hmul
  rw [← hmul, pow_two]
  exact Nat.mul_dvd_mul hd hpX

omit [Finite Γ] in
theorem commutator_top_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : ⁅(⊤ : Subgroup Y'), (⊤ : Subgroup Y')⁆ = ⊤) :
    ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ := by
  have ht : (⊤ : Subgroup Y').map e.symm.toMonoidHom = (⊤ : Subgroup Y) :=
    Subgroup.map_top_of_surjective _ e.symm.surjective
  rw [← ht, ← Subgroup.map_commutator, h]

theorem a6_facts {Y : Type*} [Group Y] [Finite Y]
    (h : Nonempty (Y ≃* ↥(alternatingGroup (Fin 6))) ∨ Nonempty (Y ≃* Equiv.Perm (Fin 6))) :
    Nat.card Y ∣ 2 ^ 4 * 3 ^ 2 * 5 ∧ (∀ N : Subgroup Y, N.Normal → N ≠ ⊥ → 360 ≤ Nat.card N) ∧
      ∃ P : Subgroup Y, P ≠ ⊥ ∧ ⁅P, P⁆ = P := by
  have h6 : 5 ≤ Nat.card (Fin 6) := by simp
  have h360 : Nat.factorial 6 / 2 = 360 := by decide
  rcases h with he | he
  · obtain ⟨e⟩ := he
    have hcard : Nat.card Y = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin, h360]
    refine ⟨by rw [hcard]; norm_num, fun N hN hN1 => ?_, ⊤, ?_, ?_⟩
    · have hNe : (N.map e.toMonoidHom).Normal := hN.map _ e.surjective
      rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top h6 (N := N.map e.toMonoidHom)
        with hb | ht
      · exact absurd ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hb) hN1
      · have h1 := Subgroup.card_map_of_injective (K := N) (f := e.toMonoidHom) e.injective
        rw [ht, Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin, h360] at h1
        omega
    · intro hb
      have h1 : Nat.card (⊤ : Subgroup Y) = 1 := by rw [hb, Subgroup.card_bot]
      rw [Subgroup.card_top, hcard] at h1
      omega
    · exact commutator_top_of_mulEquiv e (commutator_alternatingGroup_eq_top h6)
  · obtain ⟨e⟩ := he
    have hcard : Nat.card Y = 720 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      decide
    refine ⟨by rw [hcard]; norm_num, fun N hN hN1 => ?_,
      (alternatingGroup (Fin 6)).map e.symm.toMonoidHom, ?_, ?_⟩
    · have hNe : (N.map e.toMonoidHom).Normal := hN.map _ e.surjective
      have hnt : Nontrivial ↥(N.map e.toMonoidHom) := by
        rw [Subgroup.nontrivial_iff_ne_bot]
        exact fun hb => hN1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hb)
      have hA := Equiv.Perm.alternatingGroup_le_of_normal h6 hnt
      have h1 := Subgroup.card_map_of_injective (K := N) (f := e.toMonoidHom) e.injective
      have h2 := Subgroup.card_le_of_le hA
      rw [nat_card_alternatingGroup, Nat.card_fin, h360] at h2
      omega
    · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective]
      have := alternatingGroup.nontrivial_of_three_le_card (α := Fin 6) (by simp)
      exact (Subgroup.nontrivial_iff_ne_bot _).mp this
    · rw [← Subgroup.map_commutator, commutator_alternatingGroup_eq_self h6]

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

namespace Ctx14325

variable (C : Ctx14325 G T L V V₂ g D)
include C

theorem not_maps_of_five (hd : Module.finrank (ZMod 2) D.V = 4) {γ : D.V ≃ₗ[ZMod 2] D.V}
    {k : ℕ} (hγ : γ ^ (5 ^ k) = 1) (hγ1 : γ ≠ 1) : ¬ ∀ w ∈ D.hat V, γ w ∈ D.hat V := by
  intro hγS
  have hfix := fix_of_maps_card_four C.card_hatV (p := 5) (by norm_num) le_rfl hγ hγS
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ D.hat V, w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hb : D.hat V = ⊥ := (Submodule.eq_bot_iff _).mpr hcon
    have := C.card_hatV
    rw [hb] at this
    simp at this
  exact hγ1 (eq_one_of_fix_card_sixteen (card_V_of_dim hd) hγ hw0 (hfix w hw))

theorem not_case_iii (h1332 : Stmt13_3_2) (h1352 : A6.Stmt13_5_2) (h1381 : Stmt13_8_1)
    (h36 : A36ForSQTK) (h39 : A39ForSQTK) (hd : Module.finrank (ZMod 2) D.V = 4)
    (hiii : Case14323iii T V g D) : False := by
  have := L14332.finite_linearEquiv D
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set Hd := D.img (l32nH T V) with hHd
  have h6 : 5 ≤ Nat.card (Fin 6) := by simp
  obtain ⟨hcardH, hbig, P₀, hP₀1, hP₀p⟩ := a6_facts (Y := ↥Hd) hiii.iso
  set P := P₀.map Hd.subtype with hP
  have hPH : P ≤ Hd := Subgroup.map_le_iff_le_comap.mpr (fun x _ => x.2)
  have hP1 : P ≠ ⊥ := by
    rw [Ne, hP, Subgroup.map_eq_bot_iff_of_injective _ Hd.subtype_injective]
    exact hP₀1
  have hPp : ⁅P, P⁆ = P := by rw [hP, ← Subgroup.map_commutator, hP₀p]
  have h25 : ¬ 5 ^ 2 ∣ Nat.card Hd := fun h => by
    have := Nat.dvd_trans h hcardH
    norm_num at this
  have hfive : ∀ X : Subgroup (D.V ≃ₗ[ZMod 2] D.V), X ≤ Hd → X ≠ ⊥ → ⁅X, X⁆ = X →
      5 ∣ Nat.card X := fun X hXH hX1 hXp =>
    prime_dvd_of_perfect hX1 hXp (by norm_num) ((Subgroup.card_dvd_of_le hXH).trans hcardH)
  obtain ⟨X, hXsub, hX1, hXp, hX60⟩ := C.exists_comp_img h1332 h1352 h1381 h36 h39 hPH hP1 hPp
    (fun X hXsub hX1 hXp hmaps => by
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 5
        (hfive X (le_of_isSubnormal hXsub) hX1 hXp)
      have hy5 : (y : D.V ≃ₗ[ZMod 2] D.V) ^ (5 ^ 1) = 1 := by
        have := pow_orderOf_eq_one (y : D.V ≃ₗ[ZMod 2] D.V)
        rwa [Subgroup.orderOf_coe, hy, ← pow_one 5] at this
      have hy1 : (y : D.V ≃ₗ[ZMod 2] D.V) ≠ 1 := fun h => by
        rw [← Subgroup.orderOf_coe, h, orderOf_one] at hy
        omega
      exact C.not_maps_of_five hd hy5 hy1 fun w hw => hmaps _ y.2 w hw)
  have h5X := hfive X (le_of_isSubnormal hXsub) hX1 hXp
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 5 h5X
  have hyH : (y : D.V ≃ₗ[ZMod 2] D.V) ∈ Hd := le_of_isSubnormal hXsub y.2
  set N := Subgroup.normalClosure ({⟨y, hyH⟩} : Set ↥Hd) with hN
  have hNX : N.map Hd.subtype ≤ X := by
    rw [Subgroup.map_le_iff_le_comap, hN, Subgroup.normalClosure, Subgroup.closure_le]
    intro c hc
    obtain ⟨b, hb, hbc⟩ := Group.mem_conjugatesOfSet_iff.mp hc
    rw [Set.mem_singleton_iff] at hb
    subst hb
    have hb5 : orderOf (⟨y, hyH⟩ : ↥Hd) = 5 := by
      rw [← Subgroup.orderOf_coe (⟨(y : D.V ≃ₗ[ZMod 2] D.V), hyH⟩ : ↥Hd)]
      exact (Subgroup.orderOf_coe y).trans hy
    have hco : orderOf c = 5 := by rw [← hbc.orderOf_eq, hb5]
    have hc5 : (c : D.V ≃ₗ[ZMod 2] D.V) ^ 5 = 1 := by
      have := pow_orderOf_eq_one c
      rw [hco] at this
      exact congrArg Subtype.val this
    exact mem_of_subnormal_of_dvd hXsub (by norm_num) h5X h25 c.2 hc5
  have hN1 : N ≠ ⊥ := by
    intro hb
    have hmem : (⟨y, hyH⟩ : ↥Hd) ∈ N := Subgroup.subset_normalClosure (Set.mem_singleton _)
    rw [hb, Subgroup.mem_bot] at hmem
    have : (y : D.V ≃ₗ[ZMod 2] D.V) = 1 := congrArg Subtype.val hmem
    rw [← Subgroup.orderOf_coe, this, orderOf_one] at hy
    omega
  have h360 := hbig N (Subgroup.normalClosure_normal) hN1
  have hle := Subgroup.card_le_of_le hNX
  rw [Subgroup.card_map_of_injective Hd.subtype_injective] at hle
  rcases hX60 with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

end Ctx14325

end L14325

end CFSG.Quasithin.H13

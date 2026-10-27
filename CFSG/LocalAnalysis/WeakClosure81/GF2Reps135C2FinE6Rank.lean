module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinE6Module
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinE6Periodic
import CFSG.GroupTheory.E3Params

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint.Chevalley CFSG.Quasithin CFSG.Quasithin.SmithCurtis CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
open scoped Matrix

theorem six_le_mQuot_of_card_fixV_le {W : Type} [CommGroup W] [Finite W] {g : MulAut W}
    (hcard : Nat.card W = 2 ^ 27) (hfix : Nat.card ↥(fixV (Subgroup.zpowers g)) ≤ 2 ^ 21) :
    6 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers g)) := by
  rw [CFSG.GroupTheory.mQuot_top_eq_rkIdx]
  unfold rkIdx
  set S := fixV (Subgroup.zpowers g) with hS
  have h1 : S.index * Nat.card S = 2 ^ 27 := by rw [mul_comm, Subgroup.card_mul_index, hcard]
  have hdvd : S.index ∣ 2 ^ 27 := ⟨Nat.card S, h1.symm⟩
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj6 : 6 ≤ j := by
    by_contra h
    push Not at h
    have h5 : S.index ≤ 2 ^ 5 := by
      rw [hjeq]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : S.index * Nat.card S ≤ 2 ^ 5 * 2 ^ 21 := Nat.mul_le_mul h5 hfix
    rw [h1] at h3
    norm_num at h3
  rw [hjeq, padicValNat.prime_pow]
  exact hj6


theorem card_le_twentyOne_of_unmoved (X : Finset (Fin Tag.E6.rank → ℤ))
    (Y : Finset (Fin e6Data.d)) (hX : X.Nonempty) (hXP : ∀ γ ∈ X, IsRoot .E6 γ ∧ 0 < ht γ)
    (hXY : ∀ γ ∈ X, ∀ a ∈ Y, ¬ (e6Data.wt a ⬝ᵥ γ = -1)) : Y.card ≤ 21 := by
  classical
  obtain ⟨γ, hγ⟩ := hX
  have hmem : List.ofFn γ ∈ e6R := (posData_E6.mem γ).1 (hXP γ hγ)
  have hcheck : ∀ l ∈ e6R, (Finset.univ.filter fun a : Fin e6Data.d =>
      ¬ (e6Data.wt a ⬝ᵥ (fun i : Fin Tag.E6.rank => l.getD i 0) = -1)).card ≤ 21 := by
    decide +kernel
  have hγeq : (fun i : Fin Tag.E6.rank => (List.ofFn γ).getD i 0) = γ := by
    funext i
    simp [List.getD_eq_getElem?_getD]
  have h1 := hcheck _ hmem
  rw [hγeq] at h1
  calc Y.card ≤ (Finset.univ.filter fun a : Fin e6Data.d => ¬ (e6Data.wt a ⬝ᵥ γ = -1)).card :=
        Finset.card_le_card (fun a ha => by simpa using hXY γ hγ a ha)
    _ ≤ 21 := h1

theorem card_fixedSub_le_pow_twentyOne {K : Type} [Field K] [Finite K] [CharP K 2]
    (A : Subgroup ↥(e6Data_valid.minGroup K)) (hne : A ≠ ⊥) (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card ↥(fixedSub (hV := e6Data_valid) (k := K) A) ≤ Nat.card K ^ 21 := by
  classical
  have := finite_minGroup6 K
  obtain ⟨g, hg⟩ := e6_conj_into_posU6 K A (isPGroup_of_sq A hel)
  set A' := A.map (MulAut.conj g).toMonoidHom with hA'
  have hne' : A' ≠ ⊥ := fun h => hne (by
    rwa [Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective] at h)
  have hel' : ∀ b ∈ A', b ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hel a ha, map_one]
  have hAU : A' ≤ lvlU e6Data_valid K (fWt Tag.E6.rank) 1 := by
    rw [lvlU_one_eq e6Data_valid posData_E6 K, ← posU6_eq K]
    exact hg
  obtain ⟨X, Y, hXr, -, hXY, -, hCc, hXne⟩ := exists_leading_data (hV := e6Data_valid) (k := K)
    (MinData.det_cartan_pos posDef_cartan_E6) (fun γ δ hγ hδ h => posData_E6.inj γ δ hγ hδ h)
    hAU (comm_of_exp_two hel')
  have hX := hXne hne'
  have hXP : ∀ γ ∈ X, IsRoot .E6 γ ∧ 0 < ht γ := fun γ hγ =>
    ⟨(hXr γ hγ).1, (posData_E6.pos γ (hXr γ hγ).1).1 (hXr γ hγ).2⟩
  have hXY' : ∀ γ ∈ X, ∀ a ∈ Y, ¬ (e6Data.wt a ⬝ᵥ γ = -1) := fun γ hγ a ha h =>
    ((e6Data_valid.rootOp_single_ne_zero_iff (R := K) (cartan_symm posDef_cartan_E6)
      (hXP γ hγ).1 a).2 h) (hXY γ hγ a ha)
  have hY := card_le_twentyOne_of_unmoved X Y hX hXP hXY'
  rw [← natCard_fixedSub_map_conj e6Data_valid K A g]
  exact hCc.trans (Nat.pow_le_pow_right Nat.card_pos hY)

theorem finrank_fixSub_le_twentyOne {K : Type} [Field K] [Finite K] [CharP K 2]
    {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
    {ρ : Representation k ↥(e6Data_valid.minGroup K) (Fin m → k)} (hρ : IsSimpleRep ρ)
    (hty : IsE6TwentySevenType ρ) (A : Subgroup ↥(e6Data_valid.minGroup K)) (hne : A ≠ ⊥)
    (hel : ∀ a ∈ A, a ^ 2 = 1) : Module.finrank k ↥(fixSub ρ A) ≤ 21 := by
  have hK27 : ∀ B : Subgroup ↥(e6Data_valid.minGroup K), B ≠ ⊥ → (∀ a ∈ B, a ^ 2 = 1) →
      Module.finrank K ↥(fixSub (e6Rep27 K) B) ≤ 21 := by
    intro B hBne hBel
    have h := card_fixedSub_le_pow_twentyOne B hBne hBel
    have e : fixedSub (hV := e6Data_valid) (k := K) B = fixSub (e6Rep27 K) B :=
      Submodule.ext fun v => Iff.rfl
    rw [e, Module.natCard_eq_pow_finrank (K := K) (V := ↥(fixSub (e6Rep27 K) B))] at h
    exact (Nat.pow_le_pow_iff_right (Finite.one_lt_card (α := K))).1 h
  have hK27s : ∀ B : Subgroup ↥(e6Data_valid.minGroup K), B ≠ ⊥ → (∀ a ∈ B, a ^ 2 = 1) →
      Module.finrank K ↥(fixSub (Min.e6Rep27s K) B) ≤ 21 := by
    intro B hBne hBel
    have hinj : Function.Injective (Min.e6Graph K) :=
      Function.LeftInverse.injective (g := Min.e6Graph K) Min.e6Graph_involutive
    have hBne' : B.map (Min.e6Graph K) ≠ ⊥ := fun h =>
      hBne ((Subgroup.map_eq_bot_iff_of_injective B hinj).1 h)
    have hBel' : ∀ a ∈ B.map (Min.e6Graph K), a ^ 2 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hBel x hx, map_one]
    have h := hK27 (B.map (Min.e6Graph K)) hBne' hBel'
    have e : fixSub (Min.e6Rep27s K) B = fixSub (e6Rep27 K) (B.map (Min.e6Graph K)) := by
      ext v
      constructor
      · intro hv h hh
        obtain ⟨g, hg, rfl⟩ := hh
        exact hv g hg
      · intro hv g hg
        exact hv _ ⟨g, hg, rfl⟩
    rwa [e]
  obtain ⟨y, χ, s, hs, ht, hχ⟩ := hty
  rcases hs with rfl | rfl
  · have hkey : ∀ (i : N6) (u : Kˣ),
        (if i = Min.n0T then algebraMap K k (u : K) else 1) =
        algebraMap K k (e6Chi27 (e6Data_valid.hm K i u)) := by
      intro i u
      have hchi := Min.e6Chi27_hmT (K := K) i u
      rw [hchi]
      by_cases h : i = Min.n0T
      · rw [if_pos h, if_pos h, zpow_one]
      · rw [if_neg h, if_neg h, zpow_zero]
        simp
    have hχ' : ∀ i u, χ (e6Data_valid.hm K i u) =
        algebraMap K k (e6Chi27 (e6Data_valid.hm K i u)) :=
      fun i u => (hχ i u).trans (hkey i u)
    obtain ⟨β, hβ⟩ := e6_27_iso_bc hρ ht hχ'
    have h1 := finrank_fixSub_of_iso β hβ A
    have h2 := finrank_fixSub_bcRep_le (K := K) (k := k) (e6Rep27 K) A
    exact (h1.symm ▸ h2).trans (hK27 A hne hel)
  · have hkey : ∀ (i : N6) (u : Kˣ),
        (if i = Min.n5T then algebraMap K k (u : K) else 1) =
        algebraMap K k (Min.e6Chi27s (e6Data_valid.hm K i u)) := by
      intro i u
      have hchi := Min.e6Chi27s_hmT (K := K) i u
      rw [hchi]
      by_cases h : i = Min.n5T
      · rw [if_pos h, if_pos h, zpow_one]
      · rw [if_neg h, if_neg h, zpow_zero]
        simp
    have hχ' : ∀ i u, χ (e6Data_valid.hm K i u) =
        algebraMap K k (Min.e6Chi27s (e6Data_valid.hm K i u)) :=
      fun i u => (hχ i u).trans (hkey i u)
    obtain ⟨β, hβ⟩ := e6_27s_iso_bc hρ ht hχ'
    have h1 := finrank_fixSub_of_iso β hβ A
    have h2 := finrank_fixSub_bcRep_le (K := K) (k := k) (Min.e6Rep27s K) A
    exact (h1.symm ▸ h2).trans (hK27s A hne hel)

theorem natCard_fixV_zpowers_le
    {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    {K : Type} [Field K] [Finite K] [CharP K 2] (D : HatData K ↥L)
    {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
    (c : ModuleCoordinates W L k m) (hk : Nat.card k = 2) (hρ : IsSimpleRep c.rep)
    (hty : IsE6TwentySevenType (c.rep.comp D.π)) {g : MulAut W} (hgL : g ∈ L)
    (hg2 : orderOf g = 2) : Nat.card ↥(fixV (Subgroup.zpowers g)) ≤ 2 ^ 21 := by
  classical
  haveI : Finite ↥(e6Data_valid.minGroup K) := finite_minGroup6 K
  set s : ↥L := ⟨g, hgL⟩ with hs
  have hval : (s : MulAut W) = g := by rw [hs]
  have hs2 : s ^ 2 = 1 := by
    apply Subtype.ext
    change (s : MulAut W) ^ 2 = 1
    rw [hval]
    simpa [hg2] using pow_orderOf_eq_one g
  have hZ : ∀ x ∈ Subgroup.zpowers s, x ^ 2 = 1 := by
    rw [Subgroup.forall_mem_zpowers]
    intro n
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs2, one_zpow]
  obtain ⟨A, hA, hA2, -, hfix⟩ := lift_fix D.π D.hπs D.hodd c.rep (Subgroup.zpowers s) hZ
  have hs1 : s ≠ 1 := by
    intro h
    have hg1 : g = 1 := by
      have h1 : (s : MulAut W) = 1 := congrArg Subtype.val h
      rwa [hval] at h1
    rw [hg1, orderOf_one] at hg2
    omega
  have hne : A ≠ ⊥ := fun h => hs1 (Subgroup.zpowers_eq_bot.1 (hA.1 h))
  have hdim : Module.finrank k ↥(fixSub c.rep (Subgroup.zpowers s)) ≤ 21 := by
    have h := finrank_fixSub_le_twentyOne (simpleRep_comp D.π D.hπs hρ) hty A hne hA2
    rwa [hfix] at h
  have hmap : (Subgroup.zpowers s).map L.subtype = Subgroup.zpowers g := by
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hval
  rw [← hmap, natCard_fixV_map_subtype c (Subgroup.zpowers s), hk]
  exact Nat.pow_le_pow_right (by norm_num) hdim

end CFSG.LocalAnalysis.WeakClosure81

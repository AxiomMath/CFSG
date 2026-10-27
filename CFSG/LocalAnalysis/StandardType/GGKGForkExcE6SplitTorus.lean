module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreFrame

public section

namespace CFSG.StandardType

namespace ExcE6Split

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TwE6CorootCore CFSG.StandardType.TableBExcTwoFusion CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE

private def ggKGSt_ract {C : Type} [CommGroup C] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℤ) (t : Fin n → C) : Fin m → C :=
  fun k => ∏ j, t j ^ M k j

private theorem ggKGSt_prod_zpow_sum_ab {C : Type} [CommGroup C] {ι : Type*}
    (s : Finset ι) (a : C) (c : ι → ℤ) :
    ∏ j ∈ s, a ^ c j = a ^ ∑ j ∈ s, c j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, zpow_add, ih]

private theorem ggKGSt_ract_mul {C : Type} [CommGroup C] {m n p : ℕ}
    (M : Matrix (Fin m) (Fin n) ℤ) (N : Matrix (Fin n) (Fin p) ℤ) (t : Fin p → C) :
    ggKGSt_ract (M * N) t = ggKGSt_ract M (ggKGSt_ract N t) := by
  ext k
  simp only [ggKGSt_ract, Matrix.mul_apply, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← ggKGSt_prod_zpow_sum_ab]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_comm]

private theorem ggKGSt_ract_one_vec {C : Type} [CommGroup C] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℤ) :
    ggKGSt_ract M (1 : Fin n → C) = 1 := by
  ext k
  simp [ggKGSt_ract]

private theorem ggKGSt_ract_smul_one {C : Type} [CommGroup C] {r : ℕ}
    (c : ℤ) (t : Fin r → C) :
    ggKGSt_ract (c • (1 : Matrix (Fin r) (Fin r) ℤ)) t = t ^ c := by
  ext k
  simp [ggKGSt_ract, Matrix.smul_apply, Matrix.one_apply, Finset.prod_ite_eq]

private def ggKGSt_B : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  !![4, 3, 5, 6, 4, 2; 3, 6, 6, 9, 6, 3; 5, 6, 10, 12, 8, 4;
     6, 9, 12, 18, 12, 6; 4, 6, 8, 12, 10, 5; 2, 3, 4, 6, 5, 4]

private lemma ggKGSt_B_mul_cartanT :
    ggKGSt_B * Matrix.transpose (Tag.cartan .E6) =
      (3 : ℤ) • (1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) := by
  decide +kernel

private lemma ggKGSt_cartanChar_mul {K : Type} [Field K] (c d : Fin Tag.E6.rank → Kˣ) :
    cartanChar (τ := .E6) (c * d) = cartanChar (τ := .E6) c * cartanChar (τ := .E6) d := by
  funext l
  simp only [cartanChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

private lemma ggKGSt_map_cartanChar {K L : Type} [Field K] [Field L] (f : K →+* L)
    (c : Fin Tag.E6.rank → Kˣ) :
    (fun i => Units.map f.toMonoidHom (cartanChar (τ := .E6) c i)) =
      cartanChar (τ := .E6) (fun i => Units.map f.toMonoidHom (c i)) := by
  funext l
  simp only [cartanChar]
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_zpow]

private lemma ggKGSt_cartanChar_eq_one_imp {K : Type} [Field K] {p a : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (c : Fin Tag.E6.rank → Kˣ) (hc : ∀ i, c i ^ (p ^ a) = 1)
    (h : cartanChar (τ := .E6) c = 1) : c = 1 := by
  have hcart : cartanChar (τ := .E6) c =
      ggKGSt_ract (Matrix.transpose (Tag.cartan .E6)) c := rfl
  have hB : ggKGSt_ract ggKGSt_B (cartanChar (τ := .E6) c) = c ^ (3 : ℤ) := by
    rw [hcart, ← ggKGSt_ract_mul, ggKGSt_B_mul_cartanT, ggKGSt_ract_smul_one]
  have hB1 : ggKGSt_ract ggKGSt_B (cartanChar (τ := .E6) c) = 1 := by
    rw [h, ggKGSt_ract_one_vec]
  have hc3z : c ^ (3 : ℤ) = 1 := hB.symm.trans hB1
  have hp_ne_three : p ≠ 3 := by
    intro hp3; rw [hp3] at hp5; omega
  have hcop3p : Nat.Coprime 3 p :=
    (Nat.prime_three.coprime_iff_not_dvd).2 (by
      intro h3p
      exact hp_ne_three ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3p).symm)
  have hcop : Nat.Coprime 3 (p ^ a) := hcop3p.pow_right a
  funext i
  have hci3 : c i ^ 3 = 1 := by
    have h := congrFun hc3z i
    change (c i) ^ (3 : ℤ) = 1 at h
    simpa using h
  have hcipa : c i ^ (p ^ a) = 1 := hc i
  have hdvd1 : orderOf (c i) ∣ 1 := by
    have hdvd3 : orderOf (c i) ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 hci3
    have hdvdp : orderOf (c i) ∣ p ^ a := orderOf_dvd_iff_pow_eq_one.2 hcipa
    have hgcd : orderOf (c i) ∣ Nat.gcd 3 (p ^ a) := Nat.dvd_gcd hdvd3 hdvdp
    rwa [show Nat.gcd 3 (p ^ a) = 1 from hcop] at hgcd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)

theorem exists_pgroup_le_splitTorus
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    ∃ P : Subgroup (adjointGroup .E6 K),
      IsPGroup p P ∧ Nat.card P = p ^ (6 * padicValNat p (Nat.card K - 1)) ∧
      ∀ x ∈ P,
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) ∈
          twistedTorusOf (1 : ModGL .E6 (AlgebraicClosure K)) (Units.map (entrywiseHom Fr)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let L := AlgebraicClosure K
  set a := padicValNat p (Nat.card K - 1) with ha
  have hq_ne : Nat.card K - 1 ≠ 0 := by
    have := Finite.one_lt_card (α := K)
    omega
  have hpa_dvd : p ^ a ∣ Nat.card K - 1 := by
    rw [ha]; exact pow_padicValNat_dvd
  have hpa_ne : p ^ a ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : NeZero (p ^ a) := ⟨hpa_ne⟩
  let V := rootsOfUnity (p ^ a) K
  have hcardV : Nat.card V = p ^ a :=
    card_rootsOfUnity_of_dvd_card_sub_one hpa_dvd
  have hcartan_mem : ∀ c : Fin Tag.E6.rank → Kˣ,
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6
        (cartanChar (τ := .E6) c) ∈ adjointGroup .E6 K := by
    intro c
    rw [← list_prod_torusElt_eq_rootDiagUnit (τ := .E6) c]
    apply Subgroup.list_prod_mem
    intro x hx
    rcases List.mem_map.1 hx with ⟨j, -, rfl⟩
    exact torusElt_mem_adjointGroup j (c j)
  let φ : (Fin Tag.E6.rank → Kˣ) →* adjointGroup .E6 K :=
    { toFun := fun c => ⟨CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6
          (cartanChar (τ := .E6) c), hcartan_mem c⟩
      map_one' := by
        apply Subtype.ext
        have h1 : cartanChar (τ := .E6) (1 : Fin Tag.E6.rank → Kˣ) = 1 := by
          funext l; simp [cartanChar]
        change CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6
          (cartanChar (τ := .E6) (1 : Fin Tag.E6.rank → Kˣ)) = 1
        rw [h1, rootDiagUnit_one]
      map_mul' := by
        intro c d
        apply Subtype.ext
        rw [Subgroup.coe_mul]
        change CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6
          (cartanChar (τ := .E6) (c * d)) =
          CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6
            (cartanChar (τ := .E6) c) *
          CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6
            (cartanChar (τ := .E6) d)
        rw [ggKGSt_cartanChar_mul, rootDiagUnit_mul] }
  let inc : (Fin Tag.E6.rank → V) →* (Fin Tag.E6.rank → Kˣ) :=
    { toFun := fun t i => (t i : Kˣ)
      map_one' := rfl
      map_mul' := fun x y => rfl }
  let ι : (Fin Tag.E6.rank → V) →* adjointGroup .E6 K := φ.comp inc
  have hT1 : ∀ t : Fin Tag.E6.rank → V,
      baseChangeGL (algebraMap K L) (ι t : ModGL .E6 K) ∈ torusGroup .E6 L := by
    intro t
    change baseChangeGL (algebraMap K L)
      (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6
        (cartanChar (τ := .E6) fun i => (t i : Kˣ))) ∈ torusGroup .E6 L
    rw [baseChangeGL_rootDiagUnit, ggKGSt_map_cartanChar]
    rw [← list_prod_torusElt_eq_rootDiagUnit (τ := .E6)]
    apply Subgroup.list_prod_mem
    intro x hx
    rcases List.mem_map.1 hx with ⟨j, -, rfl⟩
    exact torusElt_mem_torusGroup j _
  have hT2 : ∀ t : Fin Tag.E6.rank → V,
      Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K L) (ι t : ModGL .E6 K)) =
        baseChangeGL (algebraMap K L) (ι t : ModGL .E6 K) :=
    fun t => units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr _
  have hker : ∀ t : Fin Tag.E6.rank → V, ι t = 1 → t = 1 := by
    intro t ht
    have h1 : (ι t : ModGL .E6 K) = 1 := by rw [ht]; rfl
    have h2 : cartanChar (τ := .E6) (fun i => (t i : Kˣ)) = 1 := by
      apply rootDiagUnit_injective
      rw [rootDiagUnit_one]
      show (ι t : ModGL .E6 K) = 1
      exact h1
    have hc_eq : (fun i => (t i : Kˣ)) = 1 :=
      ggKGSt_cartanChar_eq_one_imp (p := p) (a := a) hp hp5
        (fun i => (t i : Kˣ))
        (fun i => (mem_rootsOfUnity (p ^ a) ((t i : V) : Kˣ)).mp (t i).2) h2
    funext i
    exact Subtype.ext (congrFun hc_eq i)
  have hι_inj : Function.Injective ι := by
    intro s t hst
    have h1 : s⁻¹ * t = 1 := by
      apply hker (s⁻¹ * t)
      rw [map_mul, map_inv, hst, inv_mul_cancel]
    have h2 : s * (s⁻¹ * t) = s * 1 := by rw [h1]
    rw [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h2
    exact h2.symm
  let P : Subgroup (adjointGroup .E6 K) := ι.range
  have hcardP : Nat.card P = p ^ (6 * a) := by
    have h1 : Nat.card (Fin Tag.E6.rank → V) = (p ^ a) ^ 6 := by
      rw [Nat.card_fun, hcardV, Nat.card_fin]
      rfl
    have h2 : Nat.card (Fin Tag.E6.rank → V) = Nat.card P := by
      dsimp only [P]
      exact Nat.card_congr (Equiv.ofInjective ι hι_inj)
    calc Nat.card P = Nat.card (Fin Tag.E6.rank → V) := h2.symm
      _ = (p ^ a) ^ 6 := h1
      _ = p ^ (a * 6) := (pow_mul p a 6).symm
      _ = p ^ (6 * a) := by rw [Nat.mul_comm]
  have hPgroup : IsPGroup p P := IsPGroup.of_card (n := 6 * a) hcardP
  refine ⟨P, hPgroup, hcardP, ?_⟩
  · intro x hx
    rw [mem_twistedTorusOf]
    refine ⟨?_, ?_⟩
    · obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp (show x ∈ ι.range from hx)
      exact hT1 t
    · obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp (show x ∈ ι.range from hx)
      rw [one_mul, inv_one, mul_one]
      exact hT2 t

end ExcE6Split

end CFSG.StandardType

end

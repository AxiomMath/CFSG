module

public import CFSG.Quasithin.Vol2.KGFact12617c
public import CFSG.Quasithin.Vol2.KGFact12618f
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.Perm.Fin
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.T1531Cat
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
public import CFSG.Quasithin.Vol2.KGFact12614NoFF
public import CFSG.Quasithin.Vol2.KGFact12617b
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.Quasithin.H13.KG12618

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv CFSG.Assembly.LowTwoRank
open scoped Matrix commutatorElement

section GL5

abbrev V5 := Matrix (Fin 5) (Fin 1) (ZMod 2)

theorem card_V5 : Nat.card V5 = 32 := by
  rw [Nat.card_eq_fintype_card]
  simp [Matrix]

theorem add_self_V5 (v : V5) : v + v = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  generalize v i j = a
  revert a
  decide

theorem eq_one_of_smul_eq (g : GL (Fin 5) (ZMod 2)) (h : ∀ v : V5, g • v = v) : g = 1 := by
  ext i j
  set e : V5 := Matrix.of fun k (_ : Fin 1) => if k = j then (1 : ZMod 2) else 0 with he
  have h1 := congrFun (congrFun (h e) i) 0
  change ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * e) i 0 = _ at h1
  simp [he, Matrix.mul_apply] at h1
  simp only [Units.val_one, Matrix.one_apply]
  rw [h1]

theorem card_addSubgroup_V5 (W : AddSubgroup V5) : ∃ k ≤ 5, Nat.card W = 2 ^ k := by
  have h := W.card_addSubgroup_dvd_card
  rw [card_V5, show (32 : ℕ) = 2 ^ 5 by norm_num] at h
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  exact ⟨k, hk, hk'⟩

theorem eq_one_or_five_of_modEq {k : ℕ} (hk : k ≤ 5) (h : 32 % 5 = 2 ^ k % 5) :
    k = 1 ∨ k = 5 := by
  interval_cases k <;> simp_all

theorem eq_five_of_modEq {k : ℕ} (hk : k ≤ 5) (h1 : 2 ^ k % 5 = 2 % 5)
    (h2 : 32 ≤ 2 ^ k * 2 ^ k) : k = 5 := by
  interval_cases k <;> simp_all

theorem eq_one_of_commute_orderOf_five {g t : GL (Fin 5) (ZMod 2)} (hg : orderOf g = 5)
    (ht : t ^ 2 = 1) (hc : g * t = t * g) : t = 1 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set G := Subgroup.zpowers g with hGdef
  have hG5 : IsPGroup 5 ↥G := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hg, pow_one]
  have hGt : ∀ h ∈ G, h * t = t * h := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left hc k)
  set F := FixedPoints.addSubgroup ↥G V5 with hF
  have hmod := hG5.card_modEq_card_fixedPoints (α := V5)
  have hcF : Nat.card (MulAction.fixedPoints ↥G V5) = Nat.card ↥F := rfl
  rw [hcF, card_V5] at hmod
  have hF2 : Nat.card ↥F = 2 := by
    obtain ⟨k, hk, hk'⟩ := card_addSubgroup_V5 F
    rw [hk'] at hmod
    unfold Nat.ModEq at hmod
    rcases eq_one_or_five_of_modEq hk hmod with rfl | rfl
    · rw [hk', pow_one]
    exfalso
    have htop : F = ⊤ := AddSubgroup.eq_top_of_card_eq F (by rw [hk', card_V5]; norm_num)
    have hg1 : g = 1 := eq_one_of_smul_eq g fun v => by
      have hv : v ∈ F := htop ▸ AddSubgroup.mem_top v
      exact hv ⟨g, Subgroup.mem_zpowers g⟩
    rw [hg1, orderOf_one] at hg
    norm_num at hg
  have hF1 : ∀ v ∈ F, ∀ w ∈ F, v ≠ 0 → w ≠ 0 → v = w := by
    intro v hv w hw hv0 hw0
    by_contra hvw
    have h3 : (({⟨0, F.zero_mem⟩, ⟨v, hv⟩, ⟨w, hw⟩} : Finset ↥F)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · exact fun h => hvw (congrArg Subtype.val h)
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hv0 (congrArg Subtype.val h).symm,
          fun h => hw0 (congrArg Subtype.val h).symm⟩
    have := Finset.card_le_univ ({⟨0, F.zero_mem⟩, ⟨v, hv⟩, ⟨w, hw⟩} : Finset ↥F)
    rw [h3, ← Nat.card_eq_fintype_card, hF2] at this
    omega
  let ψ : V5 →+ V5 :=
    { toFun := fun v => v + t • v
      map_zero' := by simp
      map_add' := fun a b => by simp only [smul_add]; abel }
  have hψ : ∀ v, ψ v = v + t • v := fun v => rfl
  have hker : ∀ v, ψ v = 0 ↔ t • v = v := by
    intro v
    rw [hψ]
    constructor
    · intro h
      have h1 : t • v = -v := eq_neg_of_add_eq_zero_right h
      rw [h1]
      exact neg_eq_of_add_eq_zero_left (add_self_V5 v)
    · intro h
      rw [h, add_self_V5]
  have htt : ∀ v : V5, t • t • v = v := fun v => by rw [smul_smul, ← sq, ht, one_smul]
  have hrange : ψ.range ≤ ψ.ker := by
    rintro _ ⟨v, rfl⟩
    rw [AddMonoidHom.mem_ker, hker, hψ, smul_add, htt, add_comm]
  have hcard : Nat.card V5 = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [ψ.ker.card_eq_card_quotient_mul_card_addSubgroup,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv]
  have hW32 : 32 ≤ Nat.card ψ.ker * Nat.card ψ.ker := by
    rw [← card_V5, hcard]
    exact Nat.mul_le_mul_right _ (AddSubgroup.card_le_of_le hrange)
  have hFW : ∀ v ∈ F, v ∈ ψ.ker := by
    intro v hv
    rw [AddMonoidHom.mem_ker, hker]
    by_cases hv0 : v = 0
    · rw [hv0, smul_zero]
    have htv : t • v ∈ F := fun c => by
      show (c : GL (Fin 5) (ZMod 2)) • t • v = t • v
      rw [smul_smul, hGt c c.2, ← smul_smul, show (c : GL (Fin 5) (ZMod 2)) • v = v from hv c]
    refine hF1 _ htv _ hv ?_ hv0
    intro h0
    apply hv0
    rw [← htt v, h0, smul_zero]
  have hWinv : ∀ c : ↥G, ∀ w ∈ ψ.ker, c • w ∈ ψ.ker := by
    intro c w hw
    rw [AddMonoidHom.mem_ker, hker] at hw ⊢
    show t • (c : GL (Fin 5) (ZMod 2)) • w = (c : GL (Fin 5) (ZMod 2)) • w
    rw [smul_smul, ← hGt c c.2, ← smul_smul, hw]
  let Wg : SubMulAction ↥G V5 :=
    { carrier := ψ.ker
      smul_mem' := fun c w hw => hWinv c w hw }
  have hmodW := hG5.card_modEq_card_fixedPoints (α := ↥Wg)
  have hfixW : Nat.card (MulAction.fixedPoints ↥G ↥Wg) = 2 := by
    refine (Nat.card_congr ?_).trans hF2
    exact
      { toFun := fun w => ⟨w.1.1, fun c => congrArg Subtype.val (w.2 c)⟩
        invFun := fun v => ⟨⟨v.1, hFW v.1 v.2⟩, fun c => Subtype.ext (v.2 c)⟩
        left_inv := fun w => rfl
        right_inv := fun v => rfl }
  have hcWg : Nat.card ↥Wg = Nat.card ψ.ker := rfl
  rw [hfixW, hcWg] at hmodW
  obtain ⟨k, hk, hk'⟩ := card_addSubgroup_V5 ψ.ker
  rw [hk'] at hmodW hW32
  unfold Nat.ModEq at hmodW
  have hk5 : k = 5 := eq_five_of_modEq hk hmodW hW32
  have htop : ψ.ker = ⊤ := AddSubgroup.eq_top_of_card_eq _ (by rw [hk', hk5, card_V5]; norm_num)
  refine eq_one_of_smul_eq t fun v => (hker v).1 ?_
  have hv : v ∈ ψ.ker := htop ▸ AddSubgroup.mem_top v
  exact hv

end GL5

theorem card_perm6_pow_five :
    (Finset.univ.filter (fun σ : Perm (Fin 6) => σ ^ 5 = 1 ∧ σ ≠ 1)).card = 144 := by
  decide +kernel

local notation "SL52" => Assembly.LowTwoRank.StatedSL 5 (ZMod 2)

theorem factKv12618L52_holds : FactKv12618L52 := by
  intro B T₀ hBB hBiso hBc hT₀2 hT₀8 hT₀N
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨φ, hφs, hφk⟩ := hBiso
  have hP2 : IsPGroup 2 ↥φ.ker := by
    rw [hφk]
    exact CFSG.pCore_isPGroup
  have hcent : ∀ z ∈ φ.ker, ∀ b : ↥B, z * b = b * z := by
    intro z hz b
    rw [hφk] at hz
    have h1 : ⁅((z : ↥SL52) : ↥SL52), (b : ↥SL52)⁆ ∈ ⁅pCoreOf 2 B, B⁆ :=
      Subgroup.commutator_mem_commutator (by unfold pCoreOf; exact ⟨z, hz, rfl⟩) b.2
    rw [hBc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact Subtype.ext h1
  have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hB : Nat.card ↥B = 360 * Nat.card ↥φ.ker := by
    rw [φ.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv, hA6]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5
    (show 5 ∣ Nat.card ↥B by rw [hB]; exact dvd_mul_of_dvd_left (by norm_num) _)
  have h25 : ∀ z : ↥B, z ∈ φ.ker → z ^ 5 = 1 → z = 1 := by
    intro z hz hz5
    obtain ⟨k, hk⟩ := hP2 ⟨z, hz⟩
    have hk' : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hd5 := orderOf_dvd_of_pow_eq_one hz5
    have hd2 := orderOf_dvd_of_pow_eq_one hk'
    have : orderOf z ∣ Nat.gcd 5 (2 ^ k) := Nat.dvd_gcd hd5 hd2
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 5 2)),
      Nat.dvd_one, orderOf_eq_one_iff] at this
    exact this
  have hpow5 : ∀ y : ↥B, orderOf y = 5 → y ^ 5 = 1 := fun y hy =>
    orderOf_dvd_iff_pow_eq_one.1 (by rw [hy])
  set Ω := {y : ↥B // orderOf y = 5} with hΩ
  set Ω₆ := {σ : Perm (Fin 6) // σ ^ 5 = 1 ∧ σ ≠ 1} with hΩ₆
  have hΩ₆c : Nat.card Ω₆ = 144 := by
    rw [hΩ₆, Nat.card_eq_fintype_card, Fintype.card_subtype, card_perm6_pow_five]
  have hmapΩ : ∀ y : Ω, ((φ y.1 : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) ^ 5 = 1 ∧
      ((φ y.1 : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) ≠ 1 := by
    rintro ⟨y, hy⟩
    refine ⟨?_, fun h1 => ?_⟩
    · have h1 : y ^ 5 = 1 := hpow5 y hy
      have h2 := congrArg (fun w => ((φ w : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6))) h1
      simpa using h2
    · have hker : y ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        exact Subtype.ext h1
      have := h25 y hker (hpow5 y hy)
      rw [this, orderOf_one] at hy
      exact absurd hy (by norm_num)
  have hinjΩ : Function.Injective (fun y : Ω => (⟨_, hmapΩ y⟩ : Ω₆)) := by
    rintro ⟨y, hy⟩ ⟨y', hy'⟩ h
    have h1 : φ y = φ y' := Subtype.ext (congrArg (fun w : Ω₆ => (w.1 : Perm (Fin 6))) h)
    have hz : y⁻¹ * y' ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have hcomm : Commute y (y⁻¹ * y') := (hcent _ hz y).symm
    have h5 : (y⁻¹ * y') ^ 5 = 1 := by
      have e1 : y' = y * (y⁻¹ * y') := by group
      have hy5 : y ^ 5 = 1 := hpow5 y hy
      have hy'5 : y' ^ 5 = 1 := hpow5 y' hy'
      rw [e1, hcomm.mul_pow, hy5, one_mul] at hy'5
      exact hy'5
    have := h25 _ hz h5
    apply Subtype.ext
    calc y = y * (y⁻¹ * y') := by rw [this, mul_one]
      _ = y' := by group
  have hΩc : Nat.card Ω ≤ 144 := hΩ₆c ▸ Nat.card_le_card_of_injective _ hinjΩ
  have hxK : orderOf (x : ↥SL52) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
  have hfree : ∀ s : ↥SL52, s ∈ T₀ → s * x = x * s → s = 1 := by
    intro s hs hsx
    obtain ⟨j, hj⟩ := hT₀2 ⟨s, hs⟩
    have hj' : s ^ 2 ^ j = 1 := congrArg Subtype.val hj
    by_contra hs1
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hj')
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hi
      exact hs1 hi
    obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    set u := s ^ 2 ^ i' with hu
    have hu2 : u ^ 2 = 1 := by
      rw [hu, ← pow_mul, ← pow_succ, ← hi, pow_orderOf_eq_one]
    have hu1 : u ≠ 1 := by
      intro h
      have h1 := orderOf_dvd_of_pow_eq_one h
      rw [hi] at h1
      have := Nat.le_of_dvd (by positivity) h1
      have h2 : 2 ^ i' < 2 ^ (i' + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hux : u * x = x * u := (Commute.pow_left (show Commute s x from hsx) (2 ^ i')).eq
    apply hu1
    apply Subtype.ext
    refine eq_one_of_commute_orderOf_five (g := ((x : ↥SL52) : GL (Fin 5) (ZMod 2)))
      (by rw [Subgroup.orderOf_coe]; exact hxK) ?_ ?_
    · have h1 := congrArg (fun w : ↥SL52 => (w : GL (Fin 5) (ZMod 2))) hu2
      simpa using h1
    · have h1 := congrArg (fun w : ↥SL52 => (w : GL (Fin 5) (ZMod 2))) hux
      simpa using h1.symm
  have hconjB : ∀ t : ↥T₀, (t : ↥SL52) * x * (t : ↥SL52)⁻¹ ∈ B := fun t =>
    (Subgroup.mem_normalizer_iff.1 (hT₀N t.2) x).1 x.2
  have hord : ∀ t : ↥T₀, orderOf (⟨(t : ↥SL52) * x * (t : ↥SL52)⁻¹, hconjB t⟩ : ↥B) = 5 := by
    intro t
    rw [← Subgroup.orderOf_coe]
    show orderOf ((t : ↥SL52) * x * (t : ↥SL52)⁻¹) = 5
    rw [← SemiconjBy.orderOf_eq (t : ↥SL52) (show SemiconjBy (t : ↥SL52) x
      ((t : ↥SL52) * x * (t : ↥SL52)⁻¹) by unfold SemiconjBy; group)]
    exact hxK
  let f : ↥T₀ → Ω := fun t => ⟨⟨(t : ↥SL52) * x * (t : ↥SL52)⁻¹, hconjB t⟩, hord t⟩
  have hf : Function.Injective f := by
    intro t t' h
    have h1 : (t : ↥SL52) * x * (t : ↥SL52)⁻¹ = (t' : ↥SL52) * x * (t' : ↥SL52)⁻¹ :=
      congrArg (fun w : Ω => ((w.1 : ↥B) : ↥SL52)) h
    have hs : (t' : ↥SL52)⁻¹ * t ∈ T₀ := T₀.mul_mem (T₀.inv_mem t'.2) t.2
    have hsx : ((t' : ↥SL52)⁻¹ * t) * x = x * ((t' : ↥SL52)⁻¹ * t) := by
      calc ((t' : ↥SL52)⁻¹ * t) * x =
            (t' : ↥SL52)⁻¹ * ((t : ↥SL52) * x * (t : ↥SL52)⁻¹) * t := by group
        _ = (t' : ↥SL52)⁻¹ * ((t' : ↥SL52) * x * (t' : ↥SL52)⁻¹) * t := by rw [h1]
        _ = x * ((t' : ↥SL52)⁻¹ * t) := by group
    have h2 := hfree _ hs hsx
    apply Subtype.ext
    calc (t : ↥SL52) = t' * ((t' : ↥SL52)⁻¹ * t) := by group
      _ = t' := by rw [h2, mul_one]
  have hT₀c : Nat.card ↥T₀ ≤ Nat.card Ω := Nat.card_le_card_of_injective f hf
  have h256 : (2 : ℕ) ^ 8 = 256 := by norm_num
  omega

end CFSG.Quasithin.H13.KG12618

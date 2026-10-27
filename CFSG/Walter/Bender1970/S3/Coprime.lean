module

public import CFSG.Walter.Bender1970.S3.Abelian
import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Open.LocalVocabulary
public import CFSG.Walter.Bender1970.S2.OddCentralizerSubgroup
public import CFSG.Walter.Bender1970.S3.FStar

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_forall_inf_centralizer_eq_bot_of_elementary {E N : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hEcomm : IsMulCommutative E) (hEexp : ∀ x ∈ E, x ^ r = 1)
    (hEcard : r ^ 2 ≤ Nat.card E) (hEN : E ≤ Subgroup.normalizer (N : Set G))
    (hcop : ¬ r ∣ Nat.card N)
    (h : ∀ e ∈ E, e ≠ 1 → N ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) : N = ⊥ := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : IsElementaryAbelian r E :=
    { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hEexp x x.2) }
  let _ : MulDistribMulAction E N := Subgroup.conjMulDistribMulActionOfLeNormalizer E N hEN
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := r) (A := E) (H := N)
    hEcard hcop
  have hbot : ∀ a : E, a ≠ 1 → CFSG.fixedPointSubgroup (Subgroup.zpowers a) N = ⊥ := by
    intro a ha
    rw [eq_bot_iff]
    intro x hx
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hx
    have hxa : ((a : G) * x * (a : G)⁻¹) = x := congrArg Subtype.val hx
    have hmem : (x : G) ∈ N ⊓ Subgroup.centralizer ({(a : G)} : Set G) := by
      refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc (x : G) * a = (a : G) * x * (a : G)⁻¹ * a := by rw [hxa]
        _ = a * x := by group
    rw [h a a.2 (fun h1 => ha (Subtype.ext h1)), Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  have htop : (⊤ : Subgroup N) = ⊥ := by
    rw [← hgen]
    exact le_bot_iff.mp (iSup₂_le fun a ha => (hbot a ha).le)
  rw [eq_bot_iff]
  intro x hx
  have h1 : (⟨x, hx⟩ : N) ∈ (⊥ : Subgroup N) := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp h1))

theorem eq_bot_of_forall_inf_centralizer_eq_bot {U N : Subgroup G}
    (hUcomm : IsMulCommutative U) (hUcyc : ¬ IsCyclic U)
    (hUN : U ≤ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime (Nat.card U) (Nat.card N))
    (h : ∀ u ∈ U, u ≠ 1 → N ⊓ Subgroup.centralizer ({u} : Set G) = ⊥) : N = ⊥ := by
  obtain ⟨r, hr, E, hEU, hEcomm, hEexp, hEcard⟩ :=
    exists_elementary_of_not_isCyclic hUcomm hUcyc
  refine eq_bot_of_forall_inf_centralizer_eq_bot_of_elementary hr hEcomm hEexp hEcard
    (hEU.trans hUN) (fun hrN => ?_) fun e he he1 => h e (hEU he) he1
  have hrE : r ∣ Nat.card E :=
    (dvd_pow_self r two_ne_zero).trans (by
      have : Fact r.Prime := ⟨hr⟩
      obtain ⟨k, hk⟩ := (IsPGroup.of_exponent_dvd_pow (p := r) (n := 1)
        (by rw [pow_one]; exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
          Subtype.ext (hEexp x x.2)) : IsPGroup r E).exists_card_eq
      rw [hk] at hEcard ⊢
      exact Nat.pow_dvd_pow r ((Nat.pow_le_pow_iff_right hr.one_lt).mp hEcard))
  have hrU : r ∣ Nat.card U := hrE.trans (Subgroup.card_dvd_of_le hEU)
  exact hr.one_lt.ne' (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hrU hrN))

theorem le_oddCoreOf_of_odd {F S : Subgroup G} (hF : Group.IsNilpotent F) (hSF : S ≤ F)
    (hS : Odd (Nat.card S)) : S ≤ oddCoreOf F := by
  set S' : Subgroup F := S.subgroupOf F
  have hS'sn : S'.IsSubnormal := isSubnormal_of_isNilpotent hF S'
  have hS'odd : Odd (Nat.card S') := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSF).toEquiv]
    exact hS
  have htop : pPrimeCore 2 S' = ⊤ := by
    rw [eq_top_iff]
    refine le_sSup ⟨Subgroup.normal_top, ?_⟩
    rw [Subgroup.card_top]
    exact Nat.coprime_two_left.mpr hS'odd
  have hle := map_pPrimeCore_le_of_isSubnormal hS'sn
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hle
  intro x hx
  exact ⟨⟨x, hSF hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem le_oddCoreOf_fittingSubgroupOf {N X : Subgroup G} (hN : IsNormalIn N X)
    (hNnil : Group.IsNilpotent N) (hNodd : Odd (Nat.card N)) :
    N ≤ oddCoreOf (CFSG.fittingSubgroupOf X) :=
  le_oddCoreOf_of_odd (CFSG.fittingSubgroupOf_isNilpotent X)
    (le_fittingSubgroupOf_of_isNormalIn_nilpotent hN.1 hN hNnil) hNodd

omit [Finite G] in
theorem oddCoreOf_fittingSubgroupOf_isNormalIn (A : Subgroup G) :
    IsNormalIn (oddCoreOf (CFSG.fittingSubgroupOf A)) A :=
  map_characteristic_isNormalIn_of_isNormalIn _ inferInstance (fittingSubgroupOf_isNormalIn A)

theorem oddCoreOf_fitting_inf_le {H X : Subgroup G} {t : G}
    (hXH : X ⊓ Subgroup.centralizer ({t} : Set G) ≤ H) :
    oddCoreOf (CFSG.fittingSubgroupOf H) ⊓ (X ⊓ Subgroup.centralizer ({t} : Set G)) ≤
      oddCoreOf (CFSG.fittingSubgroupOf (X ⊓ Subgroup.centralizer ({t} : Set G))) := by
  set C := X ⊓ Subgroup.centralizer ({t} : Set G)
  set O := oddCoreOf (CFSG.fittingSubgroupOf H)
  have hOn := oddCoreOf_fittingSubgroupOf_isNormalIn H
  refine le_oddCoreOf_fittingSubgroupOf ⟨inf_le_right, fun c hc x hx => ?_⟩ ?_ ?_
  · exact ⟨hOn.2 c (hXH hc) x hx.1, C.mul_mem (C.mul_mem hc hx.2) (C.inv_mem hc)⟩
  · have hO : O ≤ CFSG.fittingSubgroupOf H := Subgroup.map_subtype_le _
    exact isNilpotent_of_le (CFSG.fittingSubgroupOf_isNilpotent H) (inf_le_left.trans hO)
  · exact Odd.of_dvd_nat (odd_card_oddCoreOf _) (Subgroup.card_dvd_of_le inf_le_left)

theorem exists_ne_one_mem_centralizer_of_isComponentOf
    {X : Subgroup G} (hX : IsAStar X)
    {t : G} (htX : t ∈ X) (ht : orderOf t = 2) {U : Subgroup G}
    (hU : U ≤ oddCoreOf (CFSG.fittingSubgroupOf (X ⊓ Subgroup.centralizer ({t} : Set G))))
    (hUcyc : ¬ IsCyclic U) {K : Subgroup G} (hK : IsComponentOf K X) :
    ∃ u ∈ U, u ≠ 1 ∧ K ≤ Subgroup.centralizer ({u} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htp : IsPGroup 2 (Subgroup.zpowers (⟨t, htX⟩ : X)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht, pow_one])
  obtain ⟨T, hT⟩ := htp.exists_le_sylow
  obtain ⟨-, -, hE⟩ := bender1970_2_5_subgroup hX htX ht T (hT (Subgroup.mem_zpowers _)) rfl
  obtain ⟨-, hn, hcyc, -⟩ := hE K hK
  set U' := oddCoreOf (CFSG.fittingSubgroupOf (X ⊓ Subgroup.centralizer ({t} : Set G)))
  set N := (Subgroup.centralizer (K : Set G)).subgroupOf U'
  have : IsCyclic (U' ⧸ N) := hcyc
  set φ : U →* U' ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hU)
  have hker : φ.ker ≠ ⊥ := by
    intro h
    exact hUcyc (isCyclic_of_injective φ ((MonoidHom.ker_eq_bot_iff φ).mp h))
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker
  refine ⟨(u : U), (u : U).2, fun h => hu1 (Subtype.ext (Subtype.ext h)), ?_⟩
  have hmem : Subgroup.inclusion hU (u : U) ∈ N := by
    have := (u : φ.ker).2
    rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at this
  have hmem' : ((u : U) : G) ∈ Subgroup.centralizer (K : Set G) := Subgroup.mem_subgroupOf.mp hmem
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hmem' k hk)

end CFSG.Walter

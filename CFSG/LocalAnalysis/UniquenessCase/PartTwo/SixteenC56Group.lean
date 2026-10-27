module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped Classical IsMulCommutative commutatorElement

private lemma int_pow_dvd_sub_one_of_pow_dvd_pow_sub_one {p : ℕ} (hp : p.Prime) {k : ℤ}
    {m n : ℕ} (hpm : ¬ (p : ℤ) ∣ (m : ℤ)) (hk1 : (p : ℤ) ∣ k - 1)
    (hkm : (p : ℤ) ^ n ∣ k ^ m - 1) : (p : ℤ) ^ n ∣ k - 1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hkp : ¬ (p : ℤ) ∣ k := by
    intro h
    have h1 : (p : ℤ) ∣ (1 : ℤ) := by
      have h2 := dvd_sub h hk1
      rwa [sub_sub_cancel] at h2
    exact hpZ.not_dvd_one h1
  have hLTE := emultiplicity_pow_sub_pow_of_prime (p := (p : ℤ)) (x := k) (y := 1) (n := m)
    hpZ hk1 hkp hpm
  simp only [one_pow] at hLTE
  have hle : n ≤ emultiplicity (p : ℤ) (k ^ m - 1) :=
    (pow_dvd_iff_le_emultiplicity).mp hkm
  rw [hLTE] at hle
  exact (pow_dvd_iff_le_emultiplicity).mpr hle

private theorem mulAut_eq_one_of_pow_eq_one_of_fixes {X : Type*} [Group X] [Finite X]
    [IsCyclic X] {p m : ℕ} [Fact p.Prime] (hXp : IsPGroup p X) (α : MulAut X)
    (hαm : α ^ m = 1) (hpm : ¬ p ∣ m) {t : X} (ht : orderOf t = p) (hfix : α t = t) :
    α = 1 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := X)
  have ha_top : Subgroup.zpowers a = ⊤ := eq_top_iff.mpr fun x _ => ha x
  obtain ⟨n, hn⟩ := hXp.exists_card_eq
  obtain ⟨k, hk⟩ := MonoidHom.map_cyclic α.toMonoidHom
  have hk' : ∀ g : X, α g = g ^ k := fun g => hk g
  have hpow : ∀ j : ℕ, (α ^ j) a = a ^ (k ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hmul : (α ^ (j + 1)) a = (α ^ j) (α a) := by rw [pow_succ]; rfl
      rw [hmul, hk' a, map_zpow, ih, ← zpow_mul]
      congr 1
      rw [pow_succ]
  have horda : orderOf a = Nat.card X := by
    rw [← Nat.card_zpowers, ha_top, Subgroup.card_top]
  have hka : a ^ (k ^ m) = a := by rw [← hpow m, hαm]; rfl
  have h1a : a ^ (k ^ m - 1) = 1 := by rw [zpow_sub_one, hka, mul_inv_cancel]
  have hdiv : (p : ℤ) ^ n ∣ k ^ m - 1 := by
    have h : ((orderOf a : ℕ) : ℤ) ∣ k ^ m - 1 := (orderOf_dvd_iff_zpow_eq_one).mpr h1a
    rw [horda, hn] at h
    rwa [Nat.cast_pow] at h
  have hk1 : (p : ℤ) ∣ k - 1 := by
    have h : t ^ k = t := by rw [← hk' t]; exact hfix
    have h1 : t ^ (k - 1) = 1 := by rw [zpow_sub_one, h, mul_inv_cancel]
    have h2 : ((orderOf t : ℕ) : ℤ) ∣ k - 1 := (orderOf_dvd_iff_zpow_eq_one).mpr h1
    rwa [ht] at h2
  have hpmZ : ¬ (p : ℤ) ∣ (m : ℤ) := by rwa [Int.natCast_dvd_natCast]
  have hk1' : (p : ℤ) ^ n ∣ k - 1 :=
    int_pow_dvd_sub_one_of_pow_dvd_pow_sub_one Fact.out hpmZ hk1 hdiv
  have hak : a ^ k = a := by
    have hdiv' : (orderOf a : ℤ) ∣ k - 1 := by
      rw [horda, hn]
      rwa [Nat.cast_pow]
    have h : a ^ (k - 1) = 1 := (orderOf_dvd_iff_zpow_eq_one).mp hdiv'
    calc a ^ k = a ^ ((k - 1) + 1) := by rw [sub_add_cancel]
      _ = a ^ (k - 1) * a := zpow_add_one a (k - 1)
      _ = 1 * a := by rw [h]
      _ = a := one_mul a
  have haa : α a = a := by rw [hk' a, hak]
  ext x
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (ha x)
  rw [← hj, map_zpow, haa]
  rfl

private theorem relIndex_sup_eq_relIndex_of_normal {G : Type*} [Group G] [Finite G]
    (N P : Subgroup G) [N.Normal] : P.relIndex (N ⊔ P) = P.relIndex N := by
  have h1 := Subgroup.relIndex_mul_card P (N ⊔ P)
  have h2 := Subgroup.relIndex_mul_card N (N ⊔ P)
  have h3 := Subgroup.relIndex_mul_card N P
  have h4 := Subgroup.relIndex_mul_card P N
  have h5 : N.relIndex (N ⊔ P) = N.relIndex P := Subgroup.relIndex_sup_left P N
  rw [inf_eq_left.mpr (le_sup_right : P ≤ N ⊔ P)] at h1
  rw [inf_eq_left.mpr (le_sup_left : N ≤ N ⊔ P), h5] at h2
  rw [inf_comm] at h4
  have hpos : 0 < N.relIndex P * Nat.card (N ⊓ P : Subgroup G) := by
    rw [h3]
    exact Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc P.relIndex (N ⊔ P) * (N.relIndex P * Nat.card (N ⊓ P : Subgroup G))
      = P.relIndex (N ⊔ P) * Nat.card P := by rw [h3]
    _ = N.relIndex P * Nat.card N := by rw [h1, h2]
    _ = P.relIndex N * (N.relIndex P * Nat.card (N ⊓ P : Subgroup G)) := by
        rw [← h4]
        ring

private theorem sylow_inf_normal {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (P : Sylow p G) :
    ∃ T : Sylow p N, (T : Subgroup N).map N.subtype = (P : Subgroup G) ⊓ N := by
  have hdvd : P.relIndex N ∣ P.index := by
    rw [← relIndex_sup_eq_relIndex_of_normal N P]
    exact Subgroup.relIndex_dvd_index_of_le le_sup_right
  have hpm : ¬ p ∣ (P.comap N.subtype).index := by
    rw [Subgroup.comap_subtype]
    exact fun h => P.not_dvd_index (h.trans hdvd)
  refine ⟨(P.2.comap_subtype (K := N)).toSylow hpm, ?_⟩
  rw [IsPGroup.toSylow_coe, Subgroup.comap_subtype, Subgroup.subgroupOf_map_subtype]

private theorem normalizer_le_centralizer_of_cyclic_sylow {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hcyc : IsCyclic (P : Subgroup G))
    {T : Subgroup G} (hTle : T ≤ P) (hTne : T ≠ ⊥) (hTz : T ≤ Subgroup.center G) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
  haveI : IsCyclic (P : Subgroup G) := hcyc
  haveI : IsMulCommutative (P : Subgroup G) := IsCyclic.isMulCommutative
  intro g hg
  set NC : Subgroup G := Subgroup.normalizer (P : Set G)
  set CC : Subgroup G := Subgroup.centralizer (P : Set G)
  haveI : (CC.subgroupOf NC).Normal := Subgroup.normal_subgroupOf_centralizer_normalizer (P : Set G)
  have hindex : ¬ p ∣ (CC.subgroupOf NC).index := by
    have h1 : CC.relIndex NC ∣ P.index :=
      (Subgroup.relIndex_dvd_of_le_left NC
        (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)).trans
        (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer)
    exact fun h => P.not_dvd_index (h.trans h1)
  have hpdvdT : p ∣ Nat.card T := by
    rcases (P.isPGroup'.to_le hTle).card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hTne
    · exact h1
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' p hpdvdT
  set α : MulAut ↥(P : Subgroup G) := (P : Subgroup G).normalizerMonoidHom ⟨g, hg⟩
  have hαm : α ^ (CC.subgroupOf NC).index = 1 := by
    have hker : (⟨g, hg⟩ : NC) ^ (CC.subgroupOf NC).index ∈
        (P : Subgroup G).normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact Subgroup.pow_index_mem (CC.subgroupOf NC) ⟨g, hg⟩
    rw [← map_pow, MonoidHom.mem_ker.mp hker]
  have ht' : orderOf (⟨t, hTle t.2⟩ : ↥(P : Subgroup G)) = p := by
    rw [← Subgroup.orderOf_coe (⟨t, hTle t.2⟩ : ↥(P : Subgroup G)), Subgroup.orderOf_coe t, ht]
  have hfix : α ⟨t, hTle t.2⟩ = ⟨t, hTle t.2⟩ := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hgt : (t : G) ∈ Subgroup.center G := hTz t.2
    rw [Subgroup.mem_center_iff] at hgt
    rw [hgt g, mul_assoc, mul_inv_cancel, mul_one]
  have hα1 : α = 1 :=
    mulAut_eq_one_of_pow_eq_one_of_fixes P.isPGroup' α hαm hindex ht' hfix
  have hmem : (⟨g, hg⟩ : NC) ∈ (P : Subgroup G).normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    exact hα1
  rwa [Subgroup.normalizerMonoidHom_ker] at hmem

theorem not_isCyclic_sylow_of_perfect_quotient {H K : Type*} [Group H] [Finite H] [Group K]
    [Group.IsPerfect K] (φ : H →* K) (hφ : Function.Surjective φ) {p : ℕ} [Fact p.Prime]
    (hpK : p ∣ Nat.card K) (hpker : p ∣ Nat.card φ.ker) (P : Sylow p H) :
    ¬ IsCyclic (P : Subgroup H) := by
  intro hcyc
  haveI : IsCyclic (P : Subgroup H) := hcyc
  haveI : IsMulCommutative (P : Subgroup H) := IsCyclic.isMulCommutative
  let N : Subgroup H := φ.ker
  have hNnormal : N.Normal := MonoidHom.normal_ker φ
  haveI : N.Normal := hNnormal
  obtain ⟨T, hT⟩ := sylow_inf_normal (p := p) (N := N) P
  let T' : Subgroup H := (P : Subgroup H) ⊓ N
  have hT' : (T : Subgroup N).map N.subtype = T' := hT
  have hTne : (T : Subgroup N) ≠ ⊥ := Sylow.ne_bot_of_dvd_card T hpker
  have hT'ne : T' ≠ ⊥ := by
    rw [← hT']
    intro h
    exact hTne ((Subgroup.map_eq_bot_iff_of_injective (T : Subgroup N)
      N.subtype_injective).mp h)
  haveI : Finite (Sylow p N) := Sylow.finite_of_finiteIndex (Classical.arbitrary (Sylow p N))
  have hFr : Subgroup.normalizer (T' : Set H) ⊔ N = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top (p := p) T
    rwa [hT'] at h
  have hmapN : N.map φ = ⊥ := Subgroup.map_ker_self φ
  have hmapNHT : (Subgroup.normalizer (T' : Set H)).map φ = ⊤ := by
    have h := congrArg (Subgroup.map φ) hFr
    rw [Subgroup.map_sup, hmapN, Subgroup.map_top_of_surjective φ hφ, sup_bot_eq] at h
    exact h
  have hcomm : ⁅Subgroup.normalizer (T' : Set H), Subgroup.normalizer (T' : Set H)⁆ ≤
      Subgroup.centralizer (T' : Set H) := by
    haveI hTcyc : IsCyclic T' := Subgroup.isCyclic_of_le inf_le_left
    haveI hTcomm : IsMulCommutative (MulAut T') := by
      have e := IsCyclic.mulAutMulEquiv T'
      exact Function.Surjective.isMulCommutative e.symm.surjective inferInstance
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hmem : ⁅x, y⁆ ∈ Subgroup.normalizer (T' : Set H) :=
      Subgroup.commutator_le_self (Subgroup.normalizer (T' : Set H))
        (Subgroup.commutator_mem_commutator hx hy)
    have hf : T'.normalizerMonoidHom ⟨⁅x, y⁆, hmem⟩ = 1 := by
      have h1 : (⟨⁅x, y⁆, hmem⟩ : Subgroup.normalizer (T' : Set H)) =
          ⁅(⟨x, hx⟩ : Subgroup.normalizer (T' : Set H)),
            (⟨y, hy⟩ : Subgroup.normalizer (T' : Set H))⁆ := rfl
      rw [h1, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
    have h2 : ⟨⁅x, y⁆, hmem⟩ ∈ T'.normalizerMonoidHom.ker := MonoidHom.mem_ker.mpr hf
    rwa [Subgroup.normalizerMonoidHom_ker] at h2
  have hmapC : (Subgroup.centralizer (T' : Set H)).map φ = ⊤ := by
    apply top_le_iff.mp
    calc (⊤ : Subgroup K) = _root_.commutator K := Group.IsPerfect.commutator_eq_top.symm
      _ = ⁅(⊤ : Subgroup K), ⊤⁆ := rfl
      _ = ⁅(Subgroup.normalizer (T' : Set H)).map φ,
            (Subgroup.normalizer (T' : Set H)).map φ⁆ := by rw [hmapNHT]
      _ = (⁅Subgroup.normalizer (T' : Set H),
            Subgroup.normalizer (T' : Set H)⁆).map φ :=
          (Subgroup.map_commutator _ _ φ).symm
      _ ≤ (Subgroup.centralizer (T' : Set H)).map φ := Subgroup.map_mono hcomm
  have hPC : (P : Subgroup H) ≤ Subgroup.centralizer (T' : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyP : y ∈ (P : Subgroup H) := (inf_le_left : (P : Subgroup H) ⊓ N ≤ P) hy
    exact congrArg Subtype.val (mul_comm' (⟨y, hyP⟩ : P) (⟨x, hx⟩ : P))
  let C : Subgroup H := Subgroup.centralizer (T' : Set H)
  have hPC' : (P : Subgroup H) ≤ C := hPC
  let PC : Sylow p C := P.subtype hPC'
  have hPCcyc : IsCyclic (PC : Subgroup C) := by
    rw [Sylow.coe_subtype]
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hPC').symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hPC').symm.surjective
  have hT'leC : T' ≤ C := inf_le_left.trans hPC'
  have hT''ne : T'.subgroupOf C ≠ ⊥ := by
    intro h
    apply hT'ne
    have h' := congrArg (Subgroup.map C.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hT'leC, Subgroup.map_bot] at h'
  have hT''z : T'.subgroupOf C ≤ Subgroup.center C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxC : (x : H) ∈ T' := hx
    exact (Subgroup.mem_centralizer_iff.mp y.2 (x : H) hxC).symm
  have hPCnorm : Subgroup.normalizer (PC : Set C) ≤ Subgroup.centralizer (PC : Set C) := by
    have hle : T'.subgroupOf C ≤ (PC : Subgroup C) := by
      rw [Sylow.coe_subtype]
      exact Subgroup.subgroupOf_mono C inf_le_left
    exact normalizer_le_centralizer_of_cyclic_sylow PC hPCcyc hle hT''ne hT''z
  let R : Subgroup C := (MonoidHom.transferSylow PC hPCnorm).ker
  have hcomp : Subgroup.IsComplement' R PC := MonoidHom.ker_transferSylow_isComplement' PC hPCnorm
  have hRp : ¬ p ∣ Nat.card R := MonoidHom.not_dvd_card_ker_transferSylow PC hPCnorm
  haveI : R.Normal := MonoidHom.normal_ker _
  have hCC : _root_.commutator ↥C ≤ R := by
    apply Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hcomp.sup_eq_top
    exact IsCyclic.isMulCommutative
  have hCC' : ⁅C, C⁆ ≤ R.map C.subtype := by
    rw [← Subgroup.map_subtype_commutator C]
    exact Subgroup.map_mono hCC
  have hmapR' : (R.map C.subtype).map φ = ⊤ := by
    apply top_le_iff.mp
    calc (⊤ : Subgroup K) = _root_.commutator K := Group.IsPerfect.commutator_eq_top.symm
      _ = ⁅(⊤ : Subgroup K), ⊤⁆ := rfl
      _ = ⁅C.map φ, C.map φ⁆ := by rw [hmapC]
      _ = (⁅C, C⁆).map φ := (Subgroup.map_commutator C C φ).symm
      _ ≤ (R.map C.subtype).map φ := Subgroup.map_mono hCC'
  have hcardR' : Nat.card (R.map C.subtype) = Nat.card R :=
    Subgroup.card_map_of_injective C.subtype_injective
  have hdvd : p ∣ Nat.card (R.map C.subtype) := by
    have h := Subgroup.card_map_dvd (R.map C.subtype) φ
    rw [hmapR', Subgroup.card_top] at h
    exact hpK.trans h
  exact hRp (hcardR' ▸ hdvd)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

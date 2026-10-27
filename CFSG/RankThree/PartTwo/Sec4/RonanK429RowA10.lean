module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgIso
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowCard
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating10

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open Equiv Equiv.Perm
open CFSG.RankThree.PartTwo.KFacts.KP2 (dThree embedSeven embedSeven_injective embedSeven_commute
  exists_eq_of_commute_dThree_of_mem sign_embedSeven embedSeven_apply_of_ge)
open CFSG.Quasithin.SteinbergCB (conjPerm conjPerm_apply conjPerm_surjective conjPerm_injective)
open scoped commutatorElement

theorem mem_autFix_conjPerm_iff {n : ℕ} {τ : Perm (Fin n)} {x : alternatingGroup (Fin n)} :
    x ∈ autFix (conjPerm n τ) ↔ (x : Perm (Fin n)) * τ = τ * x := by
  rw [mem_autFix]
  constructor
  · intro h
    have h' : τ * (x : Perm (Fin n)) * τ⁻¹ = x := by
      rw [← conjPerm_apply]
      exact congrArg Subtype.val h
    calc (x : Perm (Fin n)) * τ = τ * x * τ⁻¹ * τ := by rw [h']
      _ = τ * x := by group
  · intro h
    apply Subtype.ext
    rw [conjPerm_apply, ← h]
    group

theorem card_autFix_conjPerm_le {n : ℕ} (τ : Perm (Fin n)) :
    Nat.card (autFix (conjPerm n τ)) ≤
      Nat.card (Subgroup.centralizer ({τ} : Set (Perm (Fin n)))) := by
  refine Nat.card_le_card_of_injective
    (fun x => ⟨((x : alternatingGroup (Fin n)) : Perm (Fin n)), ?_⟩) ?_
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact mem_autFix_conjPerm_iff.mp x.2
  · intro x y hxy
    have h := congrArg
      (fun z : Subgroup.centralizer ({τ} : Set (Perm (Fin n))) => (z : Perm (Fin n))) hxy
    exact Subtype.ext (Subtype.ext h)

theorem congr_conjPerm {n : ℕ} (g τ : Perm (Fin n)) :
    MulAut.congr (conjPerm n g⁻¹) (conjPerm n τ) = conjPerm n (g⁻¹ * τ * g) := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  change ((conjPerm n g⁻¹ (conjPerm n τ ((conjPerm n g⁻¹).symm x)) :
      alternatingGroup (Fin n)) : Perm (Fin n)) = _
  have hs : (conjPerm n g⁻¹).symm x = conjPerm n g x := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [conjPerm_apply, conjPerm_apply]
    group
  rw [hs, conjPerm_apply, conjPerm_apply, conjPerm_apply, conjPerm_apply]
  group

theorem isThreeCycle_dThree : dThree.IsThreeCycle := by
  have h : dThree = swap (8 : Fin 10) 7 * swap 8 9 := by
    rw [swap_comm]
    rfl
  rw [h]
  exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem isThreeCycle_or_card_centralizer_le {τ : Perm (Fin 10)} (h3 : τ ^ 3 = 1) (h1 : τ ≠ 1) :
    τ.IsThreeCycle ∨ Nat.card (Subgroup.centralizer ({τ} : Set (Perm (Fin 10)))) ≤ 432 := by
  have hord : orderOf τ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hmem : ∀ m ∈ τ.cycleType, m = 3 := fun m hm => by
    have h2 := two_le_of_mem_cycleType hm
    have hd := (dvd_of_mem_cycleType hm).trans hord
    have : m ≤ 3 := Nat.le_of_dvd (by norm_num) hd
    interval_cases m
    · norm_num at hd
    · rfl
  set k := Multiset.card τ.cycleType with hk
  have hrep : τ.cycleType = Multiset.replicate k 3 := Multiset.eq_replicate.mpr ⟨rfl, hmem⟩
  have hsum : 3 * k ≤ 10 := by
    have := sum_cycleType_le τ
    rw [hrep, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at this
    omega
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    rw [hk0, Multiset.replicate_zero] at hrep
    exact h1 (cycleType_eq_zero.mp hrep)
  by_cases hk1' : k = 1
  · left
    rw [IsThreeCycle, hrep, hk1', Multiset.replicate_one]
  · right
    rw [nat_card_centralizer, hrep, Multiset.sum_replicate, Multiset.prod_replicate,
      Fintype.card_fin, smul_eq_mul, Multiset.toFinset_replicate, if_neg (by omega),
      Finset.prod_singleton, Multiset.count_replicate_self]
    have : k = 2 ∨ k = 3 := by omega
    rcases this with h | h <;> rw [h] <;> decide

@[expose] noncomputable def aSevenIn : Subgroup (alternatingGroup (Fin 10)) :=
  ((alternatingGroup (Fin 7)).map embedSeven).subgroupOf (alternatingGroup (Fin 10))

theorem map_embedSeven_le : (alternatingGroup (Fin 7)).map embedSeven ≤ alternatingGroup (Fin 10) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [Perm.mem_alternatingGroup, sign_embedSeven]
  exact hs

theorem mem_aSevenIn_iff {x : alternatingGroup (Fin 10)} :
    x ∈ aSevenIn ↔ ∃ s ∈ alternatingGroup (Fin 7), embedSeven s = x :=
  Iff.rfl

@[expose] noncomputable def aSevenInEquiv : aSevenIn ≃* alternatingGroup (Fin 7) :=
  (Subgroup.subgroupOfEquivOfLe map_embedSeven_le).trans
    ((alternatingGroup (Fin 7)).equivMapOfInjective embedSeven embedSeven_injective).symm

theorem card_aSevenIn : Nat.card aSevenIn = 2520 := by
  rw [Nat.card_congr aSevenInEquiv.toEquiv, KFacts.KS14.card_alternatingGroup_fin (by norm_num)]
  decide

theorem exists_of_mem_autFix_dThree {x : alternatingGroup (Fin 10)}
    (hx : x ∈ autFix (conjPerm 10 dThree)) :
    ∃ i : Fin 3, ∃ s ∈ alternatingGroup (Fin 7),
      (x : Perm (Fin 10)) = dThree ^ (i : ℕ) * embedSeven s :=
  exists_eq_of_commute_dThree_of_mem (mem_autFix_conjPerm_iff.mp hx) x.2

theorem commutator_mul_mul_of_commute {G : Type*} [Group G] {d₁ d₂ e₁ e₂ : G}
    (h₁₁ : Commute d₁ e₁) (h₁₂ : Commute d₁ e₂) (h₂₁ : Commute d₂ e₁) (h₂₂ : Commute d₂ e₂)
    (hd : Commute d₁ d₂) :
    ⁅d₁ * e₁, d₂ * e₂⁆ = ⁅e₁, e₂⁆ := by
  have hab : (d₁ * e₁) * (d₂ * e₂) = (d₁ * d₂) * (e₁ * e₂) := by
    rw [mul_assoc, ← mul_assoc e₁, h₂₁.symm.eq, mul_assoc, mul_assoc]
  have hba : (d₂ * e₂) * (d₁ * e₁) = (d₁ * d₂) * (e₂ * e₁) := by
    rw [mul_assoc, ← mul_assoc e₂, h₁₂.symm.eq, ← mul_assoc, ← mul_assoc, hd.eq, mul_assoc]
  have hc : Commute (d₁ * d₂) (e₁ * e₂ * (e₂ * e₁)⁻¹) :=
    ((h₁₁.mul_right h₁₂).mul_right (h₁₂.mul_right h₁₁).inv_right).mul_left
      ((h₂₁.mul_right h₂₂).mul_right (h₂₂.mul_right h₂₁).inv_right)
  rw [commutatorElement_def, commutatorElement_def,
    show (d₁ * e₁) * (d₂ * e₂) * (d₁ * e₁)⁻¹ * (d₂ * e₂)⁻¹ =
      ((d₁ * e₁) * (d₂ * e₂)) * ((d₂ * e₂) * (d₁ * e₁))⁻¹ by group, hab, hba]
  calc d₁ * d₂ * (e₁ * e₂) * (d₁ * d₂ * (e₂ * e₁))⁻¹
      = (d₁ * d₂) * (e₁ * e₂ * (e₂ * e₁)⁻¹) * (d₁ * d₂)⁻¹ := by group
    _ = e₁ * e₂ * (e₂ * e₁)⁻¹ := by rw [hc.eq, mul_inv_cancel_right]
    _ = e₁ * e₂ * e₁⁻¹ * e₂⁻¹ := by group

theorem commutator_mem_aSevenIn {x y : alternatingGroup (Fin 10)}
    (hx : x ∈ autFix (conjPerm 10 dThree)) (hy : y ∈ autFix (conjPerm 10 dThree)) :
    ⁅x, y⁆ ∈ aSevenIn := by
  obtain ⟨i, s, hs, hxs⟩ := exists_of_mem_autFix_dThree hx
  obtain ⟨j, t, ht, hyt⟩ := exists_of_mem_autFix_dThree hy
  rw [mem_aSevenIn_iff]
  have hst : ⁅s, t⁆ ∈ alternatingGroup (Fin 7) := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hs ht) (Subgroup.inv_mem _ hs))
      (Subgroup.inv_mem _ ht)
  refine ⟨⁅s, t⁆, hst, ?_⟩
  have hcomm : ∀ (m : ℕ) (u : Perm (Fin 7)), Commute (dThree ^ m) (embedSeven u) :=
    fun m u => (show Commute (embedSeven u) dThree from embedSeven_commute u).symm.pow_left m
  have hcoe : ((⁅x, y⁆ : alternatingGroup (Fin 10)) : Perm (Fin 10)) =
      ⁅(x : Perm (Fin 10)), (y : Perm (Fin 10))⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    rfl
  rw [hcoe, hxs, hyt, commutator_mul_mul_of_commute (hcomm _ s) (hcomm _ t) (hcomm _ s)
    (hcomm _ t) ((Commute.refl dThree).pow_pow _ _)]
  exact map_commutatorElement embedSeven s t

theorem le_aSevenIn_of_isPerfect {K : Subgroup (alternatingGroup (Fin 10))}
    (hK : K ≤ autFix (conjPerm 10 dThree)) [Group.IsPerfect K] : K ≤ aSevenIn := by
  rw [← Subgroup.commutator_eq_self (H := K), Subgroup.commutator_le]
  intro a ha b hb
  exact commutator_mem_aSevenIn (hK ha) (hK hb)

@[expose] noncomputable def iotaSeven :
    alternatingGroup (Fin 7) →* autFix (conjPerm 10 dThree) where
  toFun s := ⟨⟨embedSeven s, map_embedSeven_le ⟨s, s.2, rfl⟩⟩,
    mem_autFix_conjPerm_iff.mpr (embedSeven_commute s)⟩
  map_one' := Subtype.ext (Subtype.ext (map_one embedSeven))
  map_mul' s t := Subtype.ext (Subtype.ext (map_mul embedSeven (s : Perm (Fin 7)) t))

theorem iotaSeven_injective : Function.Injective iotaSeven := fun s t h =>
  Subtype.ext (embedSeven_injective
    (congrArg (fun x : autFix (conjPerm 10 dThree) => ((x : alternatingGroup (Fin 10)) :
      Perm (Fin 10))) h))

theorem three_dvd_of_dThree_pow_apply {m : ℕ} (h : (dThree ^ m) 7 = 7) : 3 ∣ m := by
  have h3 : dThree ^ 3 = 1 := by decide
  rw [← Nat.mod_add_div m 3, pow_add, pow_mul, h3, one_pow, mul_one] at h
  have hr : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · exact Nat.dvd_of_mod_eq_zero hr
  · rw [hr] at h
    exact absurd h (by decide)
  · rw [hr] at h
    exact absurd h (by decide)

theorem exists_iotaSeven_of_pow_two_pow {x : autFix (conjPerm 10 dThree)} {a : ℕ}
    (hx : x ^ 2 ^ a = 1) : ∃ s, iotaSeven s = x := by
  obtain ⟨i, s, hs, hxs⟩ := exists_of_mem_autFix_dThree x.2
  have hc : Commute (dThree ^ (i : ℕ)) (embedSeven s) :=
    (show Commute (embedSeven s) dThree from embedSeven_commute s).symm.pow_left _
  have h1 : (dThree ^ (i : ℕ)) ^ 2 ^ a * (embedSeven s) ^ 2 ^ a = 1 := by
    rw [← hc.mul_pow, ← hxs]
    have := congrArg (fun y : autFix (conjPerm 10 dThree) => ((y : alternatingGroup (Fin 10)) :
      Perm (Fin 10))) hx
    simpa using this
  have h2 : (dThree ^ (i : ℕ)) ^ 2 ^ a = embedSeven ((s ^ 2 ^ a)⁻¹) := by
    rw [map_inv, map_pow, eq_inv_iff_mul_eq_one]
    exact h1
  have h7 : (dThree ^ ((i : ℕ) * 2 ^ a)) 7 = 7 := by
    rw [pow_mul, h2]
    exact embedSeven_apply_of_ge _ (by decide)
  have h3 := three_dvd_of_dThree_pow_apply h7
  have hcop : Nat.Coprime 3 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
  have hi3 : 3 ∣ (i : ℕ) := hcop.dvd_of_dvd_mul_right h3
  have hi : (i : ℕ) = 0 := by
    have := i.isLt
    omega
  refine ⟨⟨s, hs⟩, Subtype.ext (Subtype.ext ?_)⟩
  change embedSeven s = ((x : alternatingGroup (Fin 10)) : Perm (Fin 10))
  rw [hxs, hi, pow_zero, one_mul]

theorem pCore_two_autFix_dThree : CFSG.pCore 2 (autFix (conjPerm 10 dThree)) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 (autFix (conjPerm 10 dThree)) with hP
  set P7 := P.comap iotaSeven with hP7
  haveI : P7.Normal := Subgroup.Normal.comap inferInstance _
  have hP7p : IsPGroup 2 P7 :=
    (CFSG.pCore_isPGroup : IsPGroup 2 P).comap_of_injective _ iotaSeven_injective
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hP7b : P7 = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P7 with h | h
    · exact h
    · exfalso
      rw [h] at hP7p
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP7p
      rw [Subgroup.card_top, KFacts.KS14.card_alternatingGroup_fin (by norm_num)] at hn
      have h3 : 3 ∣ 2 ^ n := hn ▸ (by decide : 3 ∣ Nat.factorial 7 / 2)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 P) ⟨x, hx⟩
  have hxa : x ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  obtain ⟨s, rfl⟩ := exists_iotaSeven_of_pow_two_pow hxa
  have hs : s ∈ P7 := hx
  rw [hP7b, Subgroup.mem_bot] at hs
  rw [hs, map_one]
  exact Subgroup.one_mem _

theorem conclS429_dThree
    {A : Subgroup (MulAut (alternatingGroup (Fin 10)))}
    {K : Subgroup (alternatingGroup (Fin 10))}
    (hc : CfgS429 (alternatingGroup (Fin 10)) A (conjPerm 10 dThree) K) :
    ConclS429 (alternatingGroup (Fin 10)) (conjPerm 10 dThree) K := by
  refine ⟨pCore_two_autFix_dThree, Or.inl (Or.inl ⟨?_, ⟨MulEquiv.refl _⟩⟩)⟩
  haveI := hc.isPerfect
  have hKE : K ≤ aSevenIn := le_aSevenIn_of_isPerfect hc.le_autFix
  have hcard : Nat.card aSevenIn ≤ Nat.card K := by
    rw [card_aSevenIn]
    have h1 := le_card_of_isType429 hc.isType
    have h2 : Nat.card (K ⧸ CFSG.pCore 2 K) ≤ Nat.card K :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    omega
  have hKeq : K = aSevenIn := Subgroup.eq_of_le_of_card_ge hKE hcard
  exact ⟨(MulEquiv.subgroupCongr hKeq).trans aSevenInEquiv⟩

theorem rowS429_alternatingGroup_ten :
    RowS429 (alternatingGroup (Fin 10)) := by
  intro A σ K hc
  obtain ⟨τ, rfl⟩ := conjPerm_surjective (by norm_num : 10 = 5 ∨ 7 ≤ 10) σ
  have hτ3 : τ ^ 3 = 1 := conjPerm_injective (by norm_num)
    (by rw [map_pow, hc.isE27.1.2 _ hc.mem, map_one])
  have hτ1 : τ ≠ 1 := fun h => hc.ne_one (by rw [h, map_one])
  rcases isThreeCycle_or_card_centralizer_le hτ3 hτ1 with h3c | hle
  · obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr
      (show dThree.cycleType = τ.cycleType by rw [isThreeCycle_dThree, h3c]))
    have hgτ : g⁻¹ * τ * g = dThree := by rw [← hg]; group
    have hψ : MulAut.congr (conjPerm 10 g⁻¹) (conjPerm 10 τ) = conjPerm 10 dThree := by
      rw [congr_conjPerm, hgτ]
    have hc' := hc.map (conjPerm 10 g⁻¹)
    rw [hψ] at hc'
    have hconc := conclS429_dThree hc'
    rw [← hψ] at hconc
    exact ConclS429.of_map (conjPerm 10 g⁻¹) hconc
  · exfalso
    haveI := hc.isPerfect
    have h1 := le_card_of_isType429 hc.isType
    have h2 : Nat.card (K ⧸ CFSG.pCore 2 K) ≤ Nat.card K :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    have h3 : Nat.card K ≤ Nat.card (autFix (conjPerm 10 τ)) :=
      Subgroup.card_le_of_le hc.le_autFix
    have h4 := card_autFix_conjPerm_le τ
    omega

theorem rowSOf429_alternatingGroup_ten :
    RowSOf429 (alternatingGroup (Fin 10)) :=
  rowSOf429_of_rowS429 rowS429_alternatingGroup_ten

end CFSG.RankThree.PartTwo.Sec4.RonanK429

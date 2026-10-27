module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.FactA
public import CFSG.HardMathSupport.RichardWeiss.Proving.PLType.SymCent
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.AltOn
import CFSG.LocalAnalysis.OddStandard.AltStdBalPermCenter
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Swap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Equiv Equiv.Perm

private abbrev AltEightPerm := Equiv.Perm (Fin 8)
private abbrev AltEightGroup := alternatingGroup (Fin 8)

private def a8c5 : AltEightGroup :=
  ⟨swap (0 : Fin 8) 1 * swap 1 2 * swap 2 3 * swap 3 4, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel⟩

private def a8c3 : AltEightGroup :=
  ⟨swap (5 : Fin 8) 6 * swap 6 7, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel⟩

private theorem a8c5_order : orderOf a8c5 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

private theorem a8c3_order : orderOf a8c3 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

private theorem a8c5_comm_a8c3 : a8c5 * a8c3 = a8c3 * a8c5 := by decide +kernel

private theorem no_fixed_coset_a8 {H : Subgroup AltEightGroup} {x : AltEightGroup}
    (hx : ¬ orderOf x ∣ Nat.card H) (c : AltEightGroup ⧸ H) :
    (MulAction.toPermHom AltEightGroup (AltEightGroup ⧸ H)) x c ≠ c := by
  intro hfix
  have hfix' : x • c = c := hfix
  let g : AltEightGroup := Quotient.out c
  have hc : c = ((g : AltEightGroup ⧸ H)) := (Quotient.out_eq c).symm
  have h1 : (g : AltEightGroup ⧸ H) = g • (((1 : AltEightGroup) : AltEightGroup ⧸ H)) := rfl
  have hconj : (MulAut.conj g⁻¹) x = g⁻¹ * x * g := by
    rw [MulAut.conj_apply]
    simp
  have h2 : (MulAut.conj g⁻¹) x •
      (((1 : AltEightGroup) : AltEightGroup ⧸ H)) =
      (((1 : AltEightGroup) : AltEightGroup ⧸ H)) := by
    rw [hconj]
    calc (g⁻¹ * x * g) • (((1 : AltEightGroup) : AltEightGroup ⧸ H))
        = g⁻¹ • (x • (g • (((1 : AltEightGroup) : AltEightGroup ⧸ H)))) := by
          rw [mul_smul, mul_smul]
      _ = g⁻¹ • (g • (((1 : AltEightGroup) : AltEightGroup ⧸ H))) := by rw [← h1, ← hc, hfix']
      _ = (((1 : AltEightGroup) : AltEightGroup ⧸ H)) := by
          rw [← mul_smul, inv_mul_cancel, one_smul]
  have hmem : (MulAut.conj g⁻¹) x ∈
      MulAction.stabilizer AltEightGroup (((1 : AltEightGroup) : AltEightGroup ⧸ H)) := by
    rw [MulAction.mem_stabilizer_iff]
    exact h2
  rw [MulAction.stabilizer_quotient] at hmem
  apply hx
  have hord : orderOf (g⁻¹ * x * g) = orderOf x := by
    simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x)
  rw [← hord]
  exact Subgroup.orderOf_dvd_natCard H hmem

private theorem AltEightGroup_card : Nat.card AltEightGroup = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem alt8_false_index_ten (H : Subgroup AltEightGroup)
    (hidx : H.index = 10) : False := by
  classical
  have : Fintype (AltEightGroup ⧸ H) := Fintype.ofFinite _
  have : IsSimpleGroup AltEightGroup := alternatingGroup.isSimpleGroup (by norm_num)
  have hproper : H ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at hidx
    omega
  have hcore : H.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with hb | ht
    · exact hb
    · exfalso
      exact hproper (le_antisymm le_top (ht ▸ H.normalCore_le))
  have hHcard : Nat.card H = 2016 := by
    have h := Subgroup.card_mul_index H
    rw [hidx, AltEightGroup_card] at h
    omega
  have hno5 : ¬ orderOf a8c5 ∣ Nat.card H := by
    rw [hHcard, a8c5_order]
    norm_num
  let φ : AltEightGroup →* Equiv.Perm (AltEightGroup ⧸ H) :=
    MulAction.toPermHom AltEightGroup (AltEightGroup ⧸ H)
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker H, hcore]
  have hfree5 : ∀ c : AltEightGroup ⧸ H, φ a8c5 c ≠ c := by
    intro c
    exact no_fixed_coset_a8 hno5 c
  have hcardQ : Fintype.card (AltEightGroup ⧸ H) = 10 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hidx]
  have hsupp5 : (φ a8c5).support = Finset.univ := by
    ext c
    simp [Equiv.Perm.mem_support, hfree5 c]
  have hsum5 : (φ a8c5).cycleType.sum = 10 := by
    rw [Equiv.Perm.sum_cycleType, hsupp5, Finset.card_univ, hcardQ]
  have hord5 : orderOf (φ a8c5) = 5 := by
    rw [orderOf_injective φ hφinj a8c5, a8c5_order]
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := φ a8c5) (by
    rw [hord5]; exact Nat.prime_five)
  have hk : n + 1 = 2 := by
    have h : 5 + n * 5 = 10 := by
      simpa [hn, Multiset.sum_replicate, hord5] using hsum5
    omega
  have hcen : Nat.card (Subgroup.centralizer {φ a8c5}) = 50 := by
    rw [Equiv.Perm.nat_card_centralizer, hn, hk]
    simp [hcardQ, hord5]
  have hord3 : orderOf (φ a8c3) = 3 := by
    rw [orderOf_injective φ hφinj a8c3, a8c3_order]
  have hcomm : φ a8c3 * φ a8c5 = φ a8c5 * φ a8c3 := by
    rw [← map_mul, ← map_mul, a8c5_comm_a8c3]
  have hmem : φ a8c3 ∈ Subgroup.centralizer {φ a8c5} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  have h3dvd : 3 ∣ Nat.card (Subgroup.centralizer {φ a8c5}) := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.centralizer {φ a8c5}) hmem
    rwa [hord3] at this
  rw [hcen] at h3dvd
  norm_num at h3dvd

private theorem alt8_false_index_nine (H : Subgroup AltEightGroup)
    (hidx : H.index = 9) : False := by
  classical
  have : Fintype (AltEightGroup ⧸ H) := Fintype.ofFinite _
  have : IsSimpleGroup AltEightGroup := alternatingGroup.isSimpleGroup (by norm_num)
  have hproper : H ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at hidx
    omega
  have hcore : H.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with hb | ht
    · exact hb
    · exfalso
      exact hproper (le_antisymm le_top (ht ▸ H.normalCore_le))
  have hHcard : Nat.card H = 2240 := by
    have h := Subgroup.card_mul_index H
    rw [hidx, AltEightGroup_card] at h
    omega
  have hno3 : ¬ orderOf a8c3 ∣ Nat.card H := by
    rw [hHcard, a8c3_order]
    norm_num
  let φ : AltEightGroup →* Equiv.Perm (AltEightGroup ⧸ H) :=
    MulAction.toPermHom AltEightGroup (AltEightGroup ⧸ H)
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker H, hcore]
  have hfree3 : ∀ c : AltEightGroup ⧸ H, φ a8c3 c ≠ c := by
    intro c
    exact no_fixed_coset_a8 hno3 c
  have hcardQ : Fintype.card (AltEightGroup ⧸ H) = 9 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hidx]
  have hsupp3 : (φ a8c3).support = Finset.univ := by
    ext c
    simp [Equiv.Perm.mem_support, hfree3 c]
  have hsum3 : (φ a8c3).cycleType.sum = 9 := by
    rw [Equiv.Perm.sum_cycleType, hsupp3, Finset.card_univ, hcardQ]
  have hord3 : orderOf (φ a8c3) = 3 := by
    rw [orderOf_injective φ hφinj a8c3, a8c3_order]
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := φ a8c3) (by
    rw [hord3]; exact Nat.prime_three)
  have hk : n + 1 = 3 := by
    have h : 3 + n * 3 = 9 := by
      simpa [hn, Multiset.sum_replicate, hord3] using hsum3
    omega
  have hcen : Nat.card (Subgroup.centralizer {φ a8c3}) = 162 := by
    rw [Equiv.Perm.nat_card_centralizer, hn, hk]
    simp [hcardQ, hord3]
    norm_num
  have hord5 : orderOf (φ a8c5) = 5 := by
    rw [orderOf_injective φ hφinj a8c5, a8c5_order]
  have hcomm : φ a8c5 * φ a8c3 = φ a8c3 * φ a8c5 := by
    rw [← map_mul, ← map_mul, a8c5_comm_a8c3]
  have hmem : φ a8c5 ∈ Subgroup.centralizer {φ a8c3} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  have h5dvd : 5 ∣ Nat.card (Subgroup.centralizer {φ a8c3}) := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.centralizer {φ a8c3}) hmem
    rwa [hord5] at this
  rw [hcen] at h5dvd
  norm_num at h5dvd

private theorem alt8_index_le_ten (H : Subgroup AltEightGroup) (h : H.index ≤ 10) :
    H.index = 1 ∨ H.index = 8 := by
  have hge : H.index = 1 ∨ 8 ≤ H.index := by
    by_cases htop : H = ⊤
    · exact Or.inl (by rw [htop, Subgroup.index_top])
    · right
      have : IsSimpleGroup AltEightGroup := alternatingGroup.isSimpleGroup (by norm_num)
      by_contra hlt
      have hcore : H.normalCore = ⊥ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with hb | ht
        · exact hb
        · exfalso
          exact htop (le_antisymm le_top (ht ▸ H.normalCore_le))
      have hfac : Nat.card AltEightGroup ≤ H.index.factorial := by
        have h2 := Subgroup.index_normalCore_le_factorial_index H
        rwa [hcore, Subgroup.index_bot] at h2
      have hlt8 : H.index < 8 := not_le.mp hlt
      have hle7 : H.index ≤ 7 := Nat.lt_succ_iff.mp hlt8
      have h7 : H.index.factorial ≤ Nat.factorial 7 := Nat.factorial_le hle7
      have h7fac : Nat.factorial 7 = 5040 := by decide
      have hle : Nat.card AltEightGroup ≤ Nat.factorial 7 := hfac.trans h7
      rw [AltEightGroup_card, h7fac] at hle
      norm_num at hle
  have hcases : H.index = 1 ∨ H.index = 8 ∨ H.index = 9 ∨ H.index = 10 := by
    rcases hge with h1 | h8
    · exact Or.inl h1
    · omega
  rcases hcases with h1 | h8 | h9 | h10
  · exact Or.inl h1
  · exact Or.inr h8
  · exact (alt8_false_index_nine H h9).elim
  · exact (alt8_false_index_ten H h10).elim

theorem eq_centralizer_swap_of_perm6_le_alt8
    (Y : Subgroup (alternatingGroup (Fin 8))) (e : ↥Y ≃* Equiv.Perm (Fin 6)) :
    ∃ a b : Fin 8, a ≠ b ∧ Y = (Subgroup.centralizer ({swap a b} : Set (Perm (Fin 8)))).comap
      (alternatingGroup (Fin 8)).subtype := by
  classical
  set W : Subgroup AltEightPerm := Y.map AltEightGroup.subtype with hW
  set eW : ↥W ≃* Equiv.Perm (Fin 6) :=
    (Subgroup.equivMapOfInjective Y AltEightGroup.subtype
      AltEightGroup.subtype_injective).symm.trans e with heW
  set Wbar : Subgroup ↥W := commutator ↥W with hWbar
  set W' : Subgroup AltEightPerm := Wbar.map W.subtype with hW'
  have hcommutator : Wbar.map eW.toMonoidHom = alternatingGroup (Fin 6) := by
    rw [hWbar, map_commutator_eq ↥W eW.toMonoidHom,
      MonoidHom.range_eq_top.mpr eW.surjective, ← commutator_def,
      alternatingGroup.commutator_perm_eq (by norm_num : 5 ≤ Nat.card (Fin 6))]
  set ebar : ↥Wbar ≃* alternatingGroup (Fin 6) :=
    (Subgroup.equivMapOfInjective Wbar eW.toMonoidHom eW.injective).trans
      (MulEquiv.subgroupCongr hcommutator) with hebar
  set e' : ↥W' ≃* alternatingGroup (Fin 6) :=
    (Subgroup.equivMapOfInjective Wbar W.subtype W.subtype_injective).symm.trans ebar with he'
  have hW'leW : W' ≤ W := by
    rw [hW', hWbar]
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hW'le : W' ≤ AltEightGroup := hW'leW.trans (by
    rw [hW]
    exact Subgroup.map_subtype_le Y)
  obtain ⟨p, q, hpq, hW'eq⟩ :=
    CFSG.EvenSporadicStandard.HNRecog.Section3.seg27_eq_altFix_of_A6 hW'le e'
  have hW'norm : W ≤ Subgroup.normalizer (W' : Set AltEightPerm) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [hW', Subgroup.map_map]
    have hcomp : (↑(MulAut.conj y) : AltEightPerm →* AltEightPerm).comp W.subtype =
        W.subtype.comp (↑(MulAut.conj (⟨y, hy⟩ : ↥W)) : ↥W →* ↥W) := by
      ext x
      simp [MulAut.conj_apply]
    rw [hcomp, ← Subgroup.map_map]
    have hchar : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (⟨y, hy⟩ : ↥W))) Wbar =
        Wbar := by
      rw [hWbar]
      exact Subgroup.characteristic_iff_map_eq.mp
        (inferInstance : (commutator ↥W).Characteristic) (MulAut.conj (⟨y, hy⟩ : ↥W))
    change Subgroup.map W.subtype
      (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (⟨y, hy⟩ : ↥W))) Wbar) =
      Subgroup.map W.subtype Wbar
    rw [hchar]
  have hcardW' : Nat.card W' = 360 := by
    calc Nat.card W' = Nat.card (alternatingGroup (Fin 6)) := Nat.card_congr e'.toEquiv
      _ = 360 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]
        norm_num
  have hfix : {r : Fin 8 | ∀ g ∈ W', g r = r} = ({p, q} : Set (Fin 8)) := by
    ext r
    constructor
    · intro hr
      by_contra hrpq
      have hrp : r ≠ p := by
        intro h
        exact hrpq (by rw [h]; simp)
      have hrq : r ≠ q := by
        intro h
        exact hrpq (by rw [h]; simp)
      have hle : W' ≤ CFSG.EvenSporadicStandard.HNRecog.Section3.seg27AltFix
          ({p, q, r} : Finset (Fin 8)) := by
        intro g hg
        rw [CFSG.EvenSporadicStandard.HNRecog.Section3.seg27_mem_altFix]
        refine ⟨hW'le hg, ?_⟩
        intro x hx
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx
        rcases hx with hxp | hxq | hxr
        · rw [hxp]
          rw [hW'eq] at hg
          exact (CFSG.EvenSporadicStandard.HNRecog.Section3.seg27_mem_altFix.mp hg).2 p
            (by simp)
        · rw [hxq]
          rw [hW'eq] at hg
          exact (CFSG.EvenSporadicStandard.HNRecog.Section3.seg27_mem_altFix.mp hg).2 q
            (by simp)
        · rw [hxr]
          exact hr g hg
      have h3 : ({p, q, r} : Finset (Fin 8)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · intro h
          have hqr : q = r := by simpa using h
          exact hrq hqr.symm
        · intro h
          simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with h | h
          · exact hpq h
          · exact hrp h.symm
      have hcard60 : Nat.card (CFSG.EvenSporadicStandard.HNRecog.Section3.seg27AltFix
          ({p, q, r} : Finset (Fin 8))) = 60 := by
        rw [CFSG.EvenSporadicStandard.HNRecog.Section3.seg27_card_altFix (F := {p, q, r})
          (by rw [h3]; norm_num), h3]
        norm_num
      have := Subgroup.card_le_of_le hle
      rw [hcardW', hcard60] at this
      norm_num at this
    · intro hr
      have hmem : r = p ∨ r = q := by simpa using hr
      rintro g hg
      rcases hmem with hp | hq
      · rw [hp]
        rw [hW'eq] at hg
        exact (CFSG.EvenSporadicStandard.HNRecog.Section3.seg27_mem_altFix.mp hg).2 p
          (by simp)
      · rw [hq]
        rw [hW'eq] at hg
        exact (CFSG.EvenSporadicStandard.HNRecog.Section3.seg27_mem_altFix.mp hg).2 q
          (by simp)
  have hpres : ∀ y ∈ W, y p ∈ ({p, q} : Set (Fin 8)) ∧ y q ∈ ({p, q} : Set (Fin 8)) := by
    intro y hy
    have hperm : ∀ r ∈ ({p, q} : Set (Fin 8)), y r ∈ ({p, q} : Set (Fin 8)) := by
      intro r hr
      have hrmem : r ∈ {r : Fin 8 | ∀ g ∈ W', g r = r} := by
        rw [hfix]
        exact hr
      have hyr : y r ∈ {r : Fin 8 | ∀ g ∈ W', g r = r} := by
        intro g hg
        have hconj : y⁻¹ * g * y ∈ W' := by
          have hyinv : y⁻¹ ∈ W := W.inv_mem hy
          have hmap := hW'norm hyinv
          rw [Subgroup.mem_normalizer_iff] at hmap
          exact (hmap g).mp hg
        have := hrmem (y⁻¹ * g * y) hconj
        calc g (y r) = y ((y⁻¹ * g * y) r) := by simp [Equiv.Perm.mul_apply]
          _ = y r := by rw [this]
      rw [hfix] at hyr
      exact hyr
    exact ⟨hperm p (by simp), hperm q (by simp)⟩
  refine ⟨p, q, hpq, ?_⟩
  have hcardW : Nat.card W = 720 := by
    rw [hW, Subgroup.card_map_of_injective AltEightGroup.subtype_injective]
    calc Nat.card Y = Nat.card (Equiv.Perm (Fin 6)) := Nat.card_congr e.toEquiv
      _ = 720 := by
        rw [Nat.card_perm, Nat.card_fin]
        norm_num
  have hcardC : Nat.card (Subgroup.centralizer ({swap p q} : Set AltEightPerm) ⊓ AltEightGroup :
      Subgroup AltEightPerm) = 720 := by
    have h := CFSG.HardMathSupport.RichardWeiss.Proving.PLType.card_altCent_swap
      (m := 8) (a := p) (b := q) hpq
    have h6 : Nat.factorial 6 = 720 := by decide
    simpa [AltEightGroup, h6] using h
  have hWleC : W ≤ (Subgroup.centralizer ({swap p q} : Set AltEightPerm) ⊓
      AltEightGroup : Subgroup AltEightPerm) := by
    intro y hy
    rw [Subgroup.mem_inf]
    constructor
    · obtain ⟨hp, hq⟩ := hpres y hy
      have hp' : y p = p ∨ y p = q := by simpa using hp
      have hq' : y q = p ∨ y q = q := by simpa using hq
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (CFSG.OddStandard.AltStdBal.permC_swap_comm
          (CFSG.QuasithinUnique.L246C127.AltBig.ftc7_perm_pair hpq hp' hq'))
    · rw [hW] at hy
      exact Subgroup.map_subtype_le Y hy
  have hWeq : W = (Subgroup.centralizer ({swap p q} : Set AltEightPerm) ⊓
      AltEightGroup : Subgroup AltEightPerm) :=
    Subgroup.eq_of_le_of_card_ge hWleC (by rw [hcardW, hcardC])
  apply Subgroup.map_injective AltEightGroup.subtype_injective
  change Subgroup.map AltEightGroup.subtype Y =
    Subgroup.map AltEightGroup.subtype
      ((Subgroup.centralizer ({swap p q} : Set AltEightPerm)).subgroupOf AltEightGroup)
  rw [← hW, Subgroup.subgroupOf_map_subtype]
  exact hWeq

private abbrev AltTenPerm := Equiv.Perm (Fin 10)
private abbrev AltTenGroup := alternatingGroup (Fin 10)

theorem eq_centralizer_swap_of_perm8_le_alt10
    (Y : Subgroup (alternatingGroup (Fin 10))) (e : ↥Y ≃* Equiv.Perm (Fin 8)) :
    ∃ a b : Fin 10, a ≠ b ∧ Y = (Subgroup.centralizer ({swap a b} : Set (Perm (Fin 10)))).comap
      (alternatingGroup (Fin 10)).subtype := by
  classical
  set W : Subgroup AltTenPerm := Y.map AltTenGroup.subtype with hW
  set eW : ↥W ≃* Equiv.Perm (Fin 8) :=
    (Subgroup.equivMapOfInjective Y AltTenGroup.subtype
      AltTenGroup.subtype_injective).symm.trans e with heW
  set Wbar : Subgroup ↥W := commutator ↥W with hWbar
  set S : Subgroup AltTenPerm := Wbar.map W.subtype with hS
  have hcommutator : Wbar.map eW.toMonoidHom = alternatingGroup (Fin 8) := by
    rw [hWbar, map_commutator_eq ↥W eW.toMonoidHom,
      MonoidHom.range_eq_top.mpr eW.surjective, ← commutator_def,
      alternatingGroup.commutator_perm_eq (by norm_num : 5 ≤ Nat.card (Fin 8))]
  set ebar : ↥Wbar ≃* alternatingGroup (Fin 8) :=
    (Subgroup.equivMapOfInjective Wbar eW.toMonoidHom eW.injective).trans
      (MulEquiv.subgroupCongr hcommutator) with hebar
  set eS : ↥S ≃* alternatingGroup (Fin 8) :=
    (Subgroup.equivMapOfInjective Wbar W.subtype W.subtype_injective).symm.trans ebar with heS
  have hSleW : S ≤ W := by
    rw [hS, hWbar]
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hSle : S ≤ AltTenGroup := hSleW.trans (by
    rw [hW]
    exact Subgroup.map_subtype_le Y)
  have hcardS : Nat.card S = 20160 := by
    calc Nat.card S = Nat.card (alternatingGroup (Fin 8)) := Nat.card_congr eS.toEquiv
      _ = 20160 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]
        norm_num
  have horbit : ∀ x : Fin 10,
      (MulAction.orbit S x).ncard = 1 ∨ (MulAction.orbit S x).ncard = 8 := by
    intro x
    set H : Subgroup S := MulAction.stabilizer S x with hH
    have hidx : H.index = (MulAction.orbit S x).ncard := MulAction.index_stabilizer S x
    have hindex_map : (H.map eS.toMonoidHom).index = H.index :=
      Subgroup.index_map_eq H eS.surjective (by
        rw [show eS.toMonoidHom.ker = ⊥ from
          (MonoidHom.ker_eq_bot_iff eS.toMonoidHom).mpr eS.injective]
        exact bot_le)
    have hle : (H.map eS.toMonoidHom).index ≤ 10 := by
      rw [hindex_map, hidx]
      have h := Set.ncard_le_card (MulAction.orbit S x)
      exact h.trans (le_of_eq (Nat.card_fin 10))
    have h := alt8_index_le_ten (H.map eS.toMonoidHom) hle
    rw [hindex_map, hidx] at h
    exact h
  have hex : ∃ x : Fin 10, (MulAction.orbit S x).ncard = 8 := by
    by_contra h
    push Not at h
    have hall : ∀ x : Fin 10, (MulAction.orbit S x).ncard = 1 := by
      intro x
      rcases horbit x with h1 | h8
      · exact h1
      · exact absurd h8 (h x)
    have hbot : S = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      apply Equiv.ext
      intro x
      have hsing : MulAction.orbit S x = {x} := by
        obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp (hall x)
        have hxmem : x ∈ ({a} : Set (Fin 10)) := by
          rw [← ha]
          exact MulAction.mem_orbit_self x
        have hax : a = x := by simpa using hxmem.symm
        rw [ha, hax]
      have hgx : (g : AltTenPerm) x ∈ MulAction.orbit S x := by
        simpa using MulAction.mem_orbit x (⟨g, hg⟩ : S)
      rw [hsing] at hgx
      simpa using hgx
    have h1 : Nat.card S = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hcardS] at h1
    norm_num at h1
  obtain ⟨x, hx8⟩ := hex
  let O : Set (Fin 10) := MulAction.orbit S x
  have hOcard : O.ncard = 8 := hx8
  let Ω : Finset (Fin 10) := O.toFinset
  have hΩcard : Ω.card = 8 := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hOcard]
  have hOcompl : Oᶜ.ncard = 2 := by
    have h := Set.ncard_compl_of_ncard_eq_add O (n := 2) (by
      rw [Nat.card_fin, hOcard])
    exact h
  have hfix_compl : ∀ z : Fin 10, z ∉ O → ∀ g ∈ S, g • z = z := by
    intro z hz g hg
    by_contra hne
    have hgz : g • z ≠ z := hne
    have horbz := horbit z
    have hnot1 : (MulAction.orbit S z).ncard ≠ 1 := by
      intro h1
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
      have hzmem : z ∈ MulAction.orbit S z := MulAction.mem_orbit_self z
      rw [ha] at hzmem
      have haz : a = z := by simpa using hzmem.symm
      have hgzm : g • z ∈ MulAction.orbit S z := by
        simpa using MulAction.mem_orbit z (⟨g, hg⟩ : S)
      rw [ha, haz] at hgzm
      exact hgz (by simpa using hgzm)
    have h8 : (MulAction.orbit S z).ncard = 8 := by
      rcases horbz with h1 | h8
      · exact absurd h1 hnot1
      · exact h8
    have hdisj : Disjoint (MulAction.orbit S z) O := by
      rw [Set.disjoint_left]
      intro y hyz hyO
      obtain ⟨g, hgz⟩ := MulAction.mem_orbit_iff.mp hyz
      obtain ⟨h, hhx⟩ := MulAction.mem_orbit_iff.mp hyO
      have hgz' : (g : AltTenPerm) z = y := by simpa [Subgroup.smul_def] using hgz
      have hhx' : (h : AltTenPerm) x = y := by simpa [Subgroup.smul_def] using hhx
      have hzx : z ∈ O := by
        have hz' : z = ((g⁻¹ : S) * h) • x := by
          calc z = ((g⁻¹ : S) : AltTenPerm) ((g : AltTenPerm) z) := by simp
            _ = ((g⁻¹ : S) : AltTenPerm) y := by rw [hgz']
            _ = ((g⁻¹ : S) : AltTenPerm) ((h : AltTenPerm) x) := by rw [hhx']
            _ = ((g⁻¹ : S) * h) • x := by simp [Subgroup.smul_def, mul_smul]
        rw [hz']
        exact MulAction.mem_orbit _ _
      exact hz hzx
    have hsub : MulAction.orbit S z ⊆ Oᶜ := by
      intro y hy
      rw [Set.mem_compl_iff]
      intro hyO
      exact (Set.disjoint_left.mp hdisj) hy hyO
    have hle := Set.ncard_le_ncard hsub
    rw [h8, hOcompl] at hle
    norm_num at hle
  have hfixO : ∀ z ∈ O, ¬ ∀ g ∈ S, g • z = z := by
    intro z hz hfixall
    have h1 : (MulAction.orbit S z).ncard = 1 := by
      apply Set.ncard_eq_one.mpr
      refine ⟨z, ?_⟩
      ext y
      constructor
      · intro hy
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
        rw [← hg]
        simpa [Subgroup.smul_def] using hfixall (g : AltTenPerm) g.2
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact MulAction.mem_orbit_self z
    have hOz : MulAction.orbit S z = O := MulAction.orbit_eq_iff.mpr hz
    rw [hOz, hOcard] at h1
    omega
  have hFix : {r : Fin 10 | ∀ g ∈ S, g • r = r} = Oᶜ := by
    ext r
    constructor
    · intro hr
      rw [Set.mem_compl_iff]
      intro hrO
      exact hfixO r hrO hr
    · intro hr
      exact hfix_compl r hr
  have hFixcard : {r : Fin 10 | ∀ g ∈ S, g • r = r}.ncard = 2 := by
    rw [hFix, hOcompl]
  obtain ⟨p, q, hpq, hFixpq⟩ := Set.ncard_eq_two.mp hFixcard
  have hfix_pq : ∀ g ∈ S, g • p = p ∧ g • q = q := by
    intro g hg
    have hp : p ∈ ({p, q} : Set (Fin 10)) := by simp
    have hq : q ∈ ({p, q} : Set (Fin 10)) := by simp
    rw [← hFixpq] at hp hq
    exact ⟨hp g hg, hq g hg⟩
  have hS_altOn : S ≤ CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.altOn Ω := by
    intro g hg
    rw [CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.mem_altOn_iff]
    refine ⟨hSle hg, ?_⟩
    intro y hy
    have hΩcoe : (Ω : Set (Fin 10)) = O := by
      ext z
      exact Set.mem_toFinset
    have hyO : y ∉ O := by
      intro hyO
      have hyΩ : y ∈ (Ω : Set (Fin 10)) := by rwa [hΩcoe]
      exact hy (by simpa using hyΩ)
    exact hfix_compl y hyO g hg
  have : Nontrivial ↥Ω :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe, hΩcard]; norm_num)
  have hcardAltOn : Nat.card (CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.altOn Ω) =
      20160 := by
    rw [Nat.card_congr
      (CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.altOnEquiv Ω).toEquiv,
      nat_card_alternatingGroup]
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hΩcard]
    norm_num
  have hS_eq : S = CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.altOn Ω :=
    Subgroup.eq_of_le_of_card_ge hS_altOn (by rw [hcardS, hcardAltOn])
  have hSnorm : W ≤ Subgroup.normalizer (S : Set AltTenPerm) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [hS, Subgroup.map_map]
    have hcomp : (↑(MulAut.conj y) : AltTenPerm →* AltTenPerm).comp W.subtype =
        W.subtype.comp (↑(MulAut.conj (⟨y, hy⟩ : ↥W)) : ↥W →* ↥W) := by
      ext z
      simp [MulAut.conj_apply]
    rw [hcomp, ← Subgroup.map_map]
    have hchar : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (⟨y, hy⟩ : ↥W))) Wbar =
        Wbar := by
      rw [hWbar]
      exact Subgroup.characteristic_iff_map_eq.mp
        (inferInstance : (commutator ↥W).Characteristic) (MulAut.conj (⟨y, hy⟩ : ↥W))
    change Subgroup.map W.subtype
      (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (⟨y, hy⟩ : ↥W))) Wbar) =
      Subgroup.map W.subtype Wbar
    rw [hchar]
  have hpres : ∀ y ∈ W, y p ∈ ({p, q} : Set (Fin 10)) ∧
      y q ∈ ({p, q} : Set (Fin 10)) := by
    intro y hy
    have hperm : ∀ r ∈ ({p, q} : Set (Fin 10)), y r ∈ ({p, q} : Set (Fin 10)) := by
      intro r hr
      have hrmem : r ∈ {r : Fin 10 | ∀ g ∈ S, g • r = r} := by
        rw [hFixpq]
        exact hr
      have hyr : y r ∈ {r : Fin 10 | ∀ g ∈ S, g • r = r} := by
        intro g hg
        have hconj : y⁻¹ * g * y ∈ S := by
          have hyinv : y⁻¹ ∈ W := W.inv_mem hy
          have hmap := hSnorm hyinv
          rw [Subgroup.mem_normalizer_iff] at hmap
          exact (hmap g).mp hg
        have := hrmem (y⁻¹ * g * y) hconj
        calc g • (y r) = y • ((y⁻¹ * g * y) • r) := by
              simp [mul_smul]
          _ = y • r := by rw [this]
      rw [hFixpq] at hyr
      exact hyr
    exact ⟨hperm p (by simp), hperm q (by simp)⟩
  refine ⟨p, q, hpq, ?_⟩
  have hcardW : Nat.card W = 40320 := by
    rw [hW, Subgroup.card_map_of_injective AltTenGroup.subtype_injective]
    calc Nat.card Y = Nat.card (Equiv.Perm (Fin 8)) := Nat.card_congr e.toEquiv
      _ = 40320 := by
        rw [Nat.card_perm, Nat.card_fin]
        norm_num
  have hcardC : Nat.card (Subgroup.centralizer ({swap p q} : Set AltTenPerm) ⊓ AltTenGroup :
      Subgroup AltTenPerm) = 40320 := by
    have h := CFSG.HardMathSupport.RichardWeiss.Proving.PLType.card_altCent_swap
      (m := 10) (a := p) (b := q) hpq
    have h8 : Nat.factorial 8 = 40320 := by decide
    simpa [AltTenGroup, h8] using h
  have hWleC : W ≤ (Subgroup.centralizer ({swap p q} : Set AltTenPerm) ⊓
      AltTenGroup : Subgroup AltTenPerm) := by
    intro y hy
    rw [Subgroup.mem_inf]
    constructor
    · obtain ⟨hp, hq⟩ := hpres y hy
      have hp' : y p = p ∨ y p = q := by simpa using hp
      have hq' : y q = p ∨ y q = q := by simpa using hq
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (CFSG.OddStandard.AltStdBal.permC_swap_comm
          (CFSG.QuasithinUnique.L246C127.AltBig.ftc7_perm_pair hpq hp' hq'))
    · rw [hW] at hy
      exact Subgroup.map_subtype_le Y hy
  have hWeq : W = (Subgroup.centralizer ({swap p q} : Set AltTenPerm) ⊓
      AltTenGroup : Subgroup AltTenPerm) :=
    Subgroup.eq_of_le_of_card_ge hWleC (by rw [hcardW, hcardC])
  apply Subgroup.map_injective AltTenGroup.subtype_injective
  change Subgroup.map AltTenGroup.subtype Y =
    Subgroup.map AltTenGroup.subtype
      ((Subgroup.centralizer ({swap p q} : Set AltTenPerm)).subgroupOf AltTenGroup)
  rw [← hW, Subgroup.subgroupOf_map_subtype]
  exact hWeq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

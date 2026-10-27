module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.lemma_7_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG
/-! # Theorem 7.2 from BG Section 7 -/

open scoped Pointwise

section

variable {G : Type*} [Group G] [Finite G]

public theorem CFSG.generatorRank_le_card_local {H : Type*} [Group H] [Finite H] :
    generatorRank H ≤ Nat.card H := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  let e : Fin (Nat.card H) ≃ H :=
    (finCongr (Nat.card_eq_fintype_card (α := H))).trans (Fintype.equivFin H).symm
  unfold generatorRank
  refine Nat.sInf_le ?_
  refine ⟨fun i => e i, ?_⟩
  apply (Subgroup.eq_top_iff' (H := Subgroup.closure (Set.range fun i : Fin (Nat.card H) => e i))).2
  intro x
  exact Subgroup.subset_closure ⟨e.symm x, by simp [e]⟩

private theorem CFSG.primeRank_le_card {R : Type*} [Group R] [Finite R] (q : ℕ) :
    primeRank q R ≤ Nat.card R := by
  let S : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact le_trans hnA (le_trans (generatorRank_le_card_local (H := A)) (Subgroup.card_le_card_group A))
  by_cases hS : S.Nonempty
  · have hsSup_mem : sSup S ∈ S := Nat.sSup_mem hS hSbdd
    rcases hsSup_mem with ⟨A, _hAq, _hAcomm, hsSup_le⟩
    rw [primeRank]
    exact le_trans hsSup_le (le_trans (generatorRank_le_card_local (H := A)) (Subgroup.card_le_card_group A))
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have hSet :
        {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A} =
          ∅ := by
      simpa [S] using hSempty
    rw [primeRank, hSet]
    simp

private theorem CFSG.exists_pSubgroup_three_le_generatorRank_of_two_lt_groupRank
    {R : Type*} [Group R] [Finite R] (hrank : 2 < groupRank R) :
    ∃ p : Nat.Primes, ∃ B : Subgroup R,
      IsPGroup p.val B ∧ IsMulCommutative B ∧ 3 ≤ generatorRank B := by
  let S : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q R}
  have hrank' : 2 < sSup S := by
    simpa [groupRank, S] using hrank
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hqprime, hnq⟩
    exact le_trans hnq (primeRank_le_card (R := R) q)
  have hSnonempty : S.Nonempty := by
    by_contra hS
    have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have : ¬ 2 < sSup S := by simp [hSempty]
    exact this hrank'
  have hsSup_mem : sSup S ∈ S := Nat.sSup_mem hSnonempty hSbdd
  rcases hsSup_mem with ⟨q, hqprime, hsSup_le⟩
  have hqrank : 2 < primeRank q R := lt_of_lt_of_le hrank' hsSup_le
  let T : Set ℕ :=
    {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧ n ≤ generatorRank B}
  have hqrank' : 2 < sSup T := by
    simpa [primeRank, T] using hqrank
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨B, _hBq, _hBcomm, hnB⟩
    exact le_trans hnB (le_trans (generatorRank_le_card_local (H := B)) (Subgroup.card_le_card_group B))
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have : ¬ 2 < sSup T := by simp [hTempty]
    exact this hqrank'
  have htSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases htSup_mem with ⟨B, hBq, hBcomm, htSup_le⟩
  refine ⟨⟨q, hqprime⟩, B, hBq, hBcomm, ?_⟩
  exact Nat.succ_le_of_lt (lt_of_lt_of_le hqrank' htSup_le)

private theorem CFSG.not_isCyclic_of_three_le_generatorRank {H : Type*} [Group H]
    (hHrank : 3 ≤ generatorRank H) : ¬ IsCyclic H := by
  intro hcyc
  have hle : generatorRank H ≤ 1 := generatorRank_le_one_of_isCyclic (G := H) hcyc
  have hlt : 2 < generatorRank H := lt_of_lt_of_le (by decide : 2 < 3) hHrank
  exact (not_lt_of_ge (le_trans hle (by decide))) hlt

public theorem CFSG.not_isCyclic_of_two_le_generatorRank {H : Type*} [Group H]
    (hHrank : 2 ≤ generatorRank H) : ¬ IsCyclic H := by
  intro hcyc
  have hle : generatorRank H ≤ 1 := generatorRank_le_one_of_isCyclic (G := H) hcyc
  have hlt : 1 < generatorRank H := lt_of_lt_of_le (by decide : 1 < 2) hHrank
  exact (not_lt_of_ge hle) hlt

public theorem CFSG.generatorRank_le_two_of_isCyclic_subgroup_quotient
    {H : Type*} [Group H] {Y : Subgroup H} [Y.Normal]
    (hYcyc : IsCyclic Y) (hquotcyc : IsCyclic (H ⧸ Y)) :
    generatorRank H ≤ 2 := by
  classical
  obtain ⟨y, hy_top⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := Y)).1 hYcyc
  obtain ⟨xbar, hxbar_top⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := H ⧸ Y)).1 hquotcyc
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Y xbar
  let s : Fin 2 → H := fun i => if i = 0 then x else y
  have hrange : Set.range s = ({x, (y : H)} : Set H) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [s]
    · intro hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact ⟨0, by simp [s]⟩
      · exact ⟨1, by simp [s]⟩
  let S : Subgroup H := Subgroup.closure (Set.range s)
  have hxS : x ∈ S := by
    change x ∈ Subgroup.closure (Set.range s)
    rw [hrange]
    exact Subgroup.subset_closure (by simp)
  have hyS : (y : H) ∈ S := by
    change (y : H) ∈ Subgroup.closure (Set.range s)
    rw [hrange]
    exact Subgroup.subset_closure (by simp)
  have hY_le_S : Y ≤ S := by
    intro y' hy'
    have hy'_top : (⟨y', hy'⟩ : Y) ∈ (⊤ : Subgroup Y) := by simp
    have hy'_zpow : (⟨y', hy'⟩ : Y) ∈ Subgroup.zpowers y := by
      simp [hy_top]
    rcases Subgroup.mem_zpowers_iff.mp hy'_zpow with ⟨n, hn⟩
    change y' ∈ S
    have hy'_eq : y' = (((y : Y) ^ n : Y) : H) := by
      simpa using (congrArg Subtype.val hn).symm
    rw [hy'_eq]
    exact S.zpow_mem hyS n
  let q : H →* H ⧸ Y := QuotientGroup.mk' Y
  have hqx_mem : q x ∈ S.map q := Subgroup.mem_map_of_mem q hxS
  have hzpow_le : Subgroup.zpowers (q x) ≤ S.map q := (Subgroup.zpowers_le).2 hqx_mem
  have hmap_top : S.map q = ⊤ := by
    apply top_unique
    rw [← hxbar_top]
    exact hzpow_le
  have hcomap : Subgroup.comap q (S.map q) = Y ⊔ S := by
    change Subgroup.comap (QuotientGroup.mk' Y) (S.map (QuotientGroup.mk' Y)) = Y ⊔ S
    exact QuotientGroup.comap_map_mk' (N := Y) S
  have htop_eq : (⊤ : Subgroup H) = Y ⊔ S := by
    calc
      (⊤ : Subgroup H) = Subgroup.comap q ⊤ := by
        ext g
        simp [q]
      _ = Subgroup.comap q (S.map q) := by rw [hmap_top]
      _ = Y ⊔ S := hcomap
  have hYsupS : Y ⊔ S = S := sup_eq_right.mpr hY_le_S
  have hS_top : S = ⊤ := by
    have : (⊤ : Subgroup H) = S := by simpa [hYsupS] using htop_eq
    exact this.symm
  unfold generatorRank
  exact Nat.sInf_le ⟨s, by simpa [S] using hS_top⟩

public theorem CFSG.not_isCyclic_of_three_le_generatorRank_of_cyclic_quotient
    {H : Type*} [Group H] {Y : Subgroup H} [Y.Normal]
    (hHrank : 3 ≤ generatorRank H) (hquotcyc : IsCyclic (H ⧸ Y)) :
    ¬ IsCyclic Y := by
  intro hYcyc
  have hH_le_two : generatorRank H ≤ 2 :=
    generatorRank_le_two_of_isCyclic_subgroup_quotient hYcyc hquotcyc
  have hlt : 2 < generatorRank H := lt_of_lt_of_le (by decide : 2 < 3) hHrank
  exact (not_lt_of_ge hH_le_two) hlt

public theorem CFSG.exists_cyclicQuotient_fixedPoint_nonbot
    {A G : Type*} [CommGroup A] [Finite A] [Group G] [Finite G] [MulDistribMulAction A G]
    [Nontrivial G]
    (hSup : (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), fixedPointSubgroup (↥Y) G) = ⊤) :
    ∃ Y : Subgroup A, IsCyclic (A ⧸ Y) ∧ fixedPointSubgroup (↥Y) G ≠ ⊥ := by
  by_contra h
  have hall : ∀ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), fixedPointSubgroup (↥Y) G = ⊥ := by
    intro Y hYcyc
    by_contra hi
    exact h ⟨Y, hYcyc, hi⟩
  have hle_bot :
      (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), fixedPointSubgroup (↥Y) G) ≤ ⊥ := by
    refine iSup_le ?_
    intro Y
    refine iSup_le ?_
    intro hYcyc
    simp [hall Y hYcyc]
  have hbot : (⨆ (Y : Subgroup A) (_ : IsCyclic (A ⧸ Y)), fixedPointSubgroup (↥Y) G) = ⊥ :=
    le_antisymm hle_bot bot_le
  exact top_ne_bot (hSup.symm.trans hbot)

public theorem CFSG.exists_nontrivial_zpowers_fixedPoint_nonbot
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G] [MulDistribMulAction A G]
    [Nontrivial G]
    (hSup : (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) G) = ⊤) :
    ∃ a : A, a ≠ 1 ∧ fixedPointSubgroup (↥(Subgroup.zpowers a)) G ≠ ⊥ := by
  by_contra h
  have hall : ∀ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) G = ⊥ := by
    intro a ha
    by_contra hi
    exact h ⟨a, ha, hi⟩
  have hle_bot :
      (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) G) ≤ ⊥ := by
    refine iSup_le ?_
    intro a
    refine iSup_le ?_
    intro ha
    simp [hall a ha]
  have hbot : (⨆ (a : A) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) G) = ⊥ :=
    le_antisymm hle_bot bot_le
  exact top_ne_bot (hSup.symm.trans hbot)

public theorem CFSG.prime_mem_subgroupPrimeSet_of_nontrivial_center_pSubgroup
    {A : Subgroup G} {p : Nat.Primes} {B : Subgroup (Subgroup.center A)}
    (hBp : IsPGroup p.val B) (hB_ne_bot : B ≠ ⊥) :
    p ∈ subgroupPrimeSet A := by
  letI : Fact p.val.Prime := ⟨p.2⟩
  obtain ⟨n, hncard⟩ := hBp.exists_card_eq
  have hBcard_ne_one : Nat.card B ≠ 1 := by
    intro hcard
    exact hB_ne_bot ((Subgroup.eq_bot_iff_card (H := B)).2 hcard)
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    apply hBcard_ne_one
    simp [hncard, hn0]
  have hpdvdB : p.val ∣ Nat.card B := by
    rcases Nat.exists_eq_succ_of_ne_zero hn_ne_zero with ⟨m, rfl⟩
    rw [hncard, Nat.pow_succ]
    exact ⟨p.val ^ m, by simp [Nat.mul_comm]⟩
  exact dvd_trans hpdvdB
    (dvd_trans (Subgroup.card_subgroup_dvd_card B) (Subgroup.card_subgroup_dvd_card (Subgroup.center A)))

omit [Finite G] in
public theorem CFSG.le_centralizer_singleton_of_mem_center {A : Subgroup G}
    (z : Subgroup.center A) :
    A ≤ Subgroup.centralizer ({(((z : Subgroup.center A) : A) : G)} : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxz : x = (((z : Subgroup.center A) : A) : G) := by simpa using hx
  subst hxz
  let aA : A := ⟨a, ha⟩
  have hz_comm : aA * (z : A) = (z : A) * aA := (Subgroup.mem_center_iff.mp z.property) aA
  simpa [aA] using (congrArg Subtype.val hz_comm).symm

public theorem CFSG.centralizer_singleton_ne_top_of_ne_one [IsMinCE G] {z : G} (hz : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≠ ⊤ := by
  intro hcent
  have hz_center : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hgcent : g ∈ Subgroup.centralizer ({z} : Set G) := by
      simp [hcent]
    exact (Subgroup.mem_centralizer_iff.mp hgcent z (by simp)).symm
  have hz_eq_one : z = 1 := by
    have hzbot : z ∈ (⊥ : Subgroup G) := by
      simpa [center_eq_bot_of_min_ce (G := G)] using hz_center
    simpa using hzbot
  exact hz hz_eq_one

end

public theorem CFSG.theorem_7_2
    {G : Type*} [Group G] [Finite G] [IsMinCE G]
    {A : Subgroup G} (hA : Hypothesis7_1 A)
    {q : Nat.Primes} (hq : q ∉ subgroupPrimeSet A)
    (hcenterRank : 3 ≤ groupRank (Subgroup.center A)) :
    ConjugationActionTransitiveOn (section7K A)
      (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)) := by
  intro Q₁ hQ₁ Q₂ hQ₂
  have hQ₁fam : Q₁ ∈ section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
    section7HStarFamily.mem_family hQ₁
  have hQ₂fam : Q₂ ∈ section7HFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
    section7HStarFamily.mem_family hQ₂
  by_cases hQ₁bot : Q₁ = ⊥
  · have hQ₂bot : Q₂ = ⊥ := by
      have hQ₁_le_Q₂ : Q₁ ≤ Q₂ := by
        simp [hQ₁bot]
      have hQ₂_eq_Q₁ := hQ₁.2 Q₂ hQ₁_le_Q₂ hQ₂fam
      rw [hQ₁bot] at hQ₂_eq_Q₁
      exact hQ₂_eq_Q₁
    refine ⟨1, ?_⟩
    simp [hQ₁bot, hQ₂bot, Subgroup.conjBy_one]
  have hQ₂bot : Q₂ ≠ ⊥ := by
    intro hQ₂bot
    have hQ₁eq : Q₁ = ⊥ := by
      have hQ₂_le_Q₁ : Q₂ ≤ Q₁ := by
        simp [hQ₂bot]
      have hQ₁_eq_Q₂ := hQ₂.2 Q₁ hQ₂_le_Q₁ hQ₁fam
      rw [hQ₂bot] at hQ₁_eq_Q₂
      exact hQ₁_eq_Q₂
    exact hQ₁bot hQ₁eq
  letI : Nontrivial ↥Q₁ := Q₁.nontrivial_iff_ne_bot.mpr hQ₁bot
  letI : Nontrivial ↥Q₂ := Q₂.nontrivial_iff_ne_bot.mpr hQ₂bot
  have hcenterRank' : 2 < groupRank (Subgroup.center A) := lt_of_lt_of_le (by decide : 2 < 3) hcenterRank
  obtain ⟨p, B, hBp, hBcomm, hBrank⟩ :=
    exists_pSubgroup_three_le_generatorRank_of_two_lt_groupRank
      (R := Subgroup.center A) hcenterRank'
  letI : Fact p.val.Prime := ⟨p.2⟩
  letI : CommGroup B := IsMulCommutative.instCommGroup
  letI : Fact (IsPGroup p.val B) := ⟨hBp⟩
  have hB_noncyc : ¬ IsCyclic B := not_isCyclic_of_three_le_generatorRank hBrank
  have hB_ne_bot : B ≠ ⊥ := by
    intro hBbot
    apply hB_noncyc
    subst hBbot
    infer_instance
  have hpA : p ∈ subgroupPrimeSet A :=
    prime_mem_subgroupPrimeSet_of_nontrivial_center_pSubgroup (A := A) hBp hB_ne_bot
  have hp_ne_q : p ≠ q := by
    intro hpq
    exact hq (hpq ▸ hpA)
  have hpval_ne_qval : p.val ≠ q.val := by
    intro hpq
    apply hp_ne_q
    exact Subtype.ext hpq
  letI : Fact q.val.Prime := ⟨q.2⟩
  have hQ₁q : IsPGroup q.val Q₁ := isPGroup_of_isPiSubgroup_singleton hQ₁fam.2.1
  have hQ₂q : IsPGroup q.val Q₂ := isPGroup_of_isPiSubgroup_singleton hQ₂fam.2.1
  obtain ⟨n₁, hQ₁card⟩ := hQ₁q.exists_card_eq
  obtain ⟨n₂, hQ₂card⟩ := hQ₂q.exists_card_eq
  have hcopBQ₁ : Nat.Coprime p.val (Nat.card Q₁) :=
    by
      rw [hQ₁card]
      simpa using Nat.coprime_pow_primes 1 n₁ p.2 q.2 hpval_ne_qval
  let ιBA : B →* A := (Subgroup.center A).subtype.comp B.subtype
  haveI : Subgroup.Normalizes A Q₁ := ⟨hQ₁fam.2.2⟩
  letI : MulDistribMulAction (↥B) (↥Q₁) := MulDistribMulAction.compHom (↥Q₁) ιBA
  have hBQ₁fix_top :
      (⨆ (Y : Subgroup B) (_ : IsCyclic (B ⧸ Y)), fixedPointSubgroup (↥Y) ↥Q₁) = ⊤ := by
    simpa using proposition_1_16_b (G := ↥Q₁) (A := B) p.val hcopBQ₁ hB_noncyc
  obtain ⟨C, hCcyc, hCQ₁fix_nonbot⟩ :=
    exists_cyclicQuotient_fixedPoint_nonbot (A := B) (G := ↥Q₁) hBQ₁fix_top
  have hC_noncyc : ¬ IsCyclic C :=
    not_isCyclic_of_three_le_generatorRank_of_cyclic_quotient hBrank hCcyc
  letI : CommGroup C := IsMulCommutative.instCommGroup
  have hCp : IsPGroup p.val C := hBp.to_subgroup C
  letI : Fact (IsPGroup p.val C) := ⟨hCp⟩
  let ιCA : C →* A := ιBA.comp C.subtype
  haveI : Subgroup.Normalizes A Q₂ := ⟨hQ₂fam.2.2⟩
  letI : MulDistribMulAction (↥C) (↥Q₂) := MulDistribMulAction.compHom (↥Q₂) ιCA
  have hcopCQ₂ : Nat.Coprime p.val (Nat.card Q₂) :=
    by
      rw [hQ₂card]
      simpa using Nat.coprime_pow_primes 1 n₂ p.2 q.2 hpval_ne_qval
  have hCQ₂fix_top :
      (⨆ (z : C) (_ : z ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers z)) ↥Q₂) = ⊤ := by
    simpa using proposition_1_16_a (G := ↥Q₂) (A := C) p.val hcopCQ₂ hC_noncyc
  obtain ⟨z, hz_ne, hzQ₂fix_nonbot⟩ :=
    exists_nontrivial_zpowers_fixedPoint_nonbot (A := C) (G := ↥Q₂) hCQ₂fix_top
  let zB : B := z
  let zCenter : Subgroup.center A := zB
  let zA : A := zCenter
  let zG : G := zA
  let H : Subgroup G := Subgroup.centralizer ({zG} : Set G)
  have hAH : A ≤ H := by
    simpa [H, zG, zA] using le_centralizer_singleton_of_mem_center (A := A) zCenter
  have hzG_ne : zG ≠ 1 := by
    intro hzG_eq
    apply hz_ne
    apply Subtype.ext
    simpa [zG, zA, zCenter, zB] using hzG_eq
  have hHproper : H ≠ ⊤ := centralizer_singleton_ne_top_of_ne_one (G := G) (z := zG) hzG_ne
  have hHQ₁ : H ⊓ Q₁ ≠ ⊥ := by
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hCQ₁fix_nonbot with ⟨x, hxne⟩
    have hxzfix := x.2 z
    change zA • (x : Q₁) = (x : Q₁) at hxzfix
    have hxconj : zG * (x : G) * zG⁻¹ = (x : G) := by
      simpa [zG, zA, zCenter, zB,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hQ₁fam.2.2] using
        congrArg Subtype.val hxzfix
    have hxcomm : (x : G) * zG = zG * (x : G) := by
      have hxcomm' : zG * (x : G) = (x : G) * zG := by
        have := congrArg (fun t : G => t * zG) hxconj
        simpa [mul_assoc] using this
      exact hxcomm'.symm
    have hxH : (x : G) ∈ H := by
      change (x : G) ∈ Subgroup.centralizer ({zG} : Set G)
      exact Subgroup.mem_centralizer_singleton_iff.mpr hxcomm
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ?_
    refine ⟨⟨(x : G), ⟨hxH, (x : Q₁).2⟩⟩, ?_⟩
    intro hxone
    apply hxne
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hxone
  have hHQ₂ : H ⊓ Q₂ ≠ ⊥ := by
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hzQ₂fix_nonbot with ⟨x, hxne⟩
    let zgen : Subgroup.zpowers z := ⟨z, Subgroup.mem_zpowers z⟩
    have hxzfix := x.2 zgen
    change zA • (x : Q₂) = (x : Q₂) at hxzfix
    have hxconj : zG * (x : G) * zG⁻¹ = (x : G) := by
      simpa [zgen, zG, zA, zCenter, zB, ιCA, ιBA,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hQ₂fam.2.2] using
        congrArg Subtype.val hxzfix
    have hxcomm : (x : G) * zG = zG * (x : G) := by
      have hxcomm' : zG * (x : G) = (x : G) * zG := by
        have := congrArg (fun t : G => t * zG) hxconj
        simpa [mul_assoc] using this
      exact hxcomm'.symm
    have hxH : (x : G) ∈ H := by
      change (x : G) ∈ Subgroup.centralizer ({zG} : Set G)
      exact Subgroup.mem_centralizer_singleton_iff.mpr hxcomm
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ?_
    refine ⟨⟨(x : G), ⟨hxH, (x : Q₂).2⟩⟩, ?_⟩
    intro hxone
    apply hxne
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hxone
  exact lemma_7_1 hA hq hQ₁ hQ₂ hAH hHproper hHQ₁ hHQ₂

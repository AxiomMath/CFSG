module

public import CFSG.RankThree.PartTwo.Sec15.ThmDDefs
public import CFSG.RankThree.PartTwo.Sec15.ThmDStep1
public import CFSG.RankThree.PartTwo.Sec15.ThmCLemma7
public import CFSG.RankThree.PartTwo.Sec15.Item15Type
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem commutator_zpowers_le_of_forall {Y O : Subgroup G} {a : G}
    (haO : a ∈ Subgroup.normalizer (O : Set G)) (h : ∀ y ∈ Y, ⁅y, a⁆ ∈ O) :
    ⁅Y, Subgroup.zpowers a⁆ ≤ O := by
  have hpow : ∀ n : ℕ, ∀ y ∈ Y, ⁅y, a ^ n⁆ ∈ O := by
    intro n
    induction n with
    | zero => intro y hy; simpa using O.one_mem
    | succ n ih =>
      intro y hy
      have h' : ⁅y, a ^ (n + 1)⁆ = ⁅y, a⁆ * (a * ⁅y, a ^ n⁆ * a⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [h']
      exact O.mul_mem (h y hy) ((Subgroup.mem_normalizer_iff.mp haO _).mp (ih y hy))
  rw [Subgroup.commutator_le]
  intro y hy x hx
  obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers).mpr hx
  exact hpow n y hy

section Psi

@[expose] def psiOf (Y : Subgroup G) (e : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 10)) :
    ↥Y →* alternatingGroup (Fin 10) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))

theorem psiOf_surjective (Y : Subgroup G)
    (e : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 10)) :
    Function.Surjective (psiOf Y e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem psiOf_eq_one_iff (Y : Subgroup G)
    (e : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 10)) (y : ↥Y) :
    psiOf Y e y = 1 ↔ y ∈ CFSG.pPrimeCore 3 ↥Y := by
  constructor
  · intro h
    have : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y) y = 1 := by
      apply e.injective
      simpa [psiOf] using h
    exact (QuotientGroup.eq_one_iff _).mp this
  · intro h
    have : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y) y = 1 := (QuotientGroup.eq_one_iff _).mpr h
    show e (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y) y) = 1
    rw [this, map_one]

theorem psiOf_injective_quot (Y : Subgroup G)
    (e : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 10)) {x y : ↥Y}
    (h : psiOf Y e x = psiOf Y e y) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y) x = QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y) y :=
  e.injective h

end Psi

theorem mem_pCoreOf_of_mem_pPrimeCoreOf {A Y : Subgroup G} (hY : Y ∈ scriptY0 A (lB A)) {p : G}
    (hpY : p ∈ Y) (hp : p ∈ pPrimeCoreOf 3 Y) (hp2 : ∃ k : ℕ, p ^ 2 ^ k = 1) :
    p ∈ CFSG.Open.pCoreOf 2 Y := by
  obtain ⟨hodd, hmap, hcen⟩ := ThmC.lemma7_center hY
  obtain ⟨k, hk⟩ := hp2
  obtain ⟨py, hpy, hpyp⟩ := Subgroup.mem_map.mp hp
  have hpy' : py = ⟨p, hpY⟩ := Subtype.ext hpyp
  rw [hpy'] at hpy
  set z := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨p, hpY⟩ with hz
  have hzc : z ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    hcen (hmap ▸ Subgroup.mem_map_of_mem _ hpy)
  have hzk : z ^ 2 ^ k = 1 := by
    rw [hz, ← map_pow]
    have : (⟨p, hpY⟩ : ↥Y) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have h1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hzk
  have h2 : orderOf z ∣ Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) := by
    have := orderOf_dvd_natCard (⟨z, hzc⟩ : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))
    simpa using this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd) |>.symm.symm
  have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hmem : (⟨p, hpY⟩ : ↥Y) ∈ CFSG.pCore 2 ↥Y := (QuotientGroup.eq_one_iff _).mp hz1
  exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩

theorem a_le_of_faithful_a10 {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY0 A (lB A)) (hfaith : ¬ CentralizesQuot A Y)
    (hiso : Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 10))) : A ≤ Y := by
  obtain ⟨e⟩ := hiso
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.1.1.2
  letI := ker148_normal hAY
  obtain ⟨e'⟩ := nonempty_img148_equiv hAY
  have hF := hR.toSec14Std.toSec13Data.mem_partTwoF
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hR.isElemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := fun x hx => hR.isElemAbelian.2 x hx
  have hAM : A ≤ Y ⊔ A := le_sup_right
  have hYM : Y ≤ Y ⊔ A := le_sup_left
  haveI hYn : (Y.subgroupOf (Y ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hAY)
  have hN : ¬ 3 ∣ Nat.card (ker148 A Y) := by
    have h1 : Nat.card (ker148 A Y) = Nat.card (pPrimeCoreOf 3 Y) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        ((pPrimeCoreOf_le 3 Y).trans le_sup_left)).toEquiv
    rw [h1]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
  have hNY : ker148 A Y ≤ Y.subgroupOf (Y ⊔ A) := fun x hx => pPrimeCoreOf_le 3 Y hx
  have key := le_of_faithful_a10 (ker148 A Y) (Y.subgroupOf (Y ⊔ A)) (A.subgroupOf (Y ⊔ A))
    hN hNY (fun a ha b hb => Subtype.ext (hAab a ha b hb)) (fun a ha => Subtype.ext (hA3 a ha))
    ?_ (e'.trans e) ?_
  · intro a ha
    exact key (show (⟨a, hAM ha⟩ : ↥(Y ⊔ A)) ∈ A.subgroupOf (Y ⊔ A) from ha)
  · intro x hx3 hxc
    show (x : G) ∈ A
    have hx3' : (x : G) ^ 3 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx3] at this
      exact congrArg Subtype.val this
    refine mem_of_mem_partTwoF hF hx3' fun a ha => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_iff.mp hxc ⟨a, hAM ha⟩ ha
    exact congrArg Subtype.val this
  · intro a ha ha1
    by_contra hcon
    push Not at hcon
    apply hfaith
    refine ⟨(a : G), ha, fun h => ha1 (Subtype.ext h), ?_⟩
    have hO : ∀ y ∈ Y, ⁅y, (a : G)⁆ ∈ pPrimeCoreOf 3 Y := fun y hy =>
      hcon ⟨y, hYM hy⟩ hy
    have hYa := commutator_zpowers_le_of_forall
      (normalizer_le_normalizer_pPrimeCoreOf 3 Y (hAY (show (a : G) ∈ A from ha))) hO
    exact (ThmC.lemma7_centralizes hY (show (a : G) ∈ A from ha) hYa).1

end CFSG.RankThree.PartTwo.Sec15.ThmD

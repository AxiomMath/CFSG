module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09j
public import CFSG.GroupTheory.ConjQuot
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable
import CFSG.HardMathSupport.Solomon.Coordinator.Generation228

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem eq_one_of_forall_conjQuotHom_eq {P R X A : Subgroup G} [(R.subgroupOf P).Normal]
    (hRP : R ≤ P) (hXP : X ≤ normalizer (P : Set G)) (hXR : X ≤ normalizer (R : Set G))
    {p : ℕ} (hp : p.Prime) (hA : IsPGroup p A) (hAX : A ≤ X) (hRp : ¬ p ∣ Nat.card R)
    (hPA : P ⊓ centralizer (A : Set G) ≤ R) (w : ↥P ⧸ R.subgroupOf P)
    (hw : ∀ (a : G) (ha : a ∈ A), CFSG.GroupTheory.conjQuotHom hXP hXR ⟨a, hAX ha⟩ w = w) :
    w = 1 := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
  have hy : ∀ a ∈ A, (y : G)⁻¹ * (a * y * a⁻¹) ∈ R := fun a ha => by
    have h := hw a ha
    rw [CFSG.GroupTheory.conjQuotHom_apply, CFSG.GroupTheory.conjQuotAut_mk] at h
    have h' := QuotientGroup.eq.1 h.symm
    rw [mem_subgroupOf] at h'
    exact h'
  obtain ⟨n, hnR, hc⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.Generation228.exists_fixed_mem_coset hp hA
      (hAX.trans hXR) hRp hy
  have hyn : (y : G) * n ∈ R := hPA ⟨P.mul_mem y.2 (hRP hnR), hc⟩
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
  simpa using R.mul_mem hyn (R.inv_mem hnR)

theorem le_centGen9_of_commutator_le {P X E D : Subgroup G} (hP2 : ¬ 2 ∣ Nat.card P)
    (hP3 : ¬ 3 ∣ Nat.card P) (hXP : X ≤ normalizer (P : Set G)) (hEX : E ≤ X)
    (hXE : X ≤ normalizer (E : Set G)) (hE2 : ∀ e ∈ E, e ^ 2 = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE : E ≤ ⁅E, X⁆) (hDX : D ≤ X)
    (hD : Nat.card D = 3)
    (hgen : ∀ K : Subgroup G, (∀ x ∈ X, D.map (MulAut.conj x).toMonoidHom ≤ K) → X ≤ K)
    (hPP : ⁅P, P⁆ ≤ centGen9 P X E D) : P ≤ centGen9 P X E D := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := centGen9 P X E D with hR
  have hRP : R ≤ P := centGen9_le P X E D
  have hXR : X ≤ normalizer (R : Set G) := le_normalizer_centGen9 hXP hXE
  have hPR : commutator ↥P ≤ R.subgroupOf P :=
    map_le_iff_le_comap.1 ((map_subtype_commutator P).le.trans hPP)
  haveI : (R.subgroupOf P).Normal := Subgroup.Normal.of_commutator_le _ hPR
  haveI : IsMulCommutative (↥P ⧸ R.subgroupOf P) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.2 hPR
  letI : CommGroup (↥P ⧸ R.subgroupOf P) := IsMulCommutative.instCommGroup
  set ρ := CFSG.GroupTheory.conjQuotHom hXP hXR with hρ
  have hcard : ∀ {p : ℕ}, ¬ p ∣ Nat.card P → ¬ p ∣ Nat.card R :=
    fun hp h => hp (h.trans (card_dvd_of_le hRP))
  have h2 : ∀ w : ↥P ⧸ R.subgroupOf P, w * w = 1 → w = 1 := fun w hw =>
    (pow_eq_one_iff_of_coprime ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun h =>
      hP2 (h.trans (card_quotient_dvd_card _)))).1 ⟨by rw [pow_two]; exact hw, pow_card_eq_one'⟩
  have hDx : ∀ x : G, Nat.card (D.map (MulAut.conj x).toMonoidHom) = 3 :=
    fun x => (card_map_of_injective (MulAut.conj x).injective).trans hD
  have hDX' : ∀ {x : G}, x ∈ X → D.map (MulAut.conj x).toMonoidHom ≤ X :=
    fun hx => conj_smul_le_of_le hDX ⟨_, hx⟩
  have hfix : ∀ x (hx : x ∈ X), ∀ b (hb : b ∈ D.map (MulAut.conj x).toMonoidHom), b ≠ 1 →
      ∀ w, ρ ⟨b, hDX' hx hb⟩ w = w → w = 1 := by
    intro x hx b hb hb1 w hw
    refine eq_one_of_forall_conjQuotHom_eq hRP hXP hXR Nat.prime_three
      (IsPGroup.of_card (n := 1) (by rw [hDx, pow_one])) (hDX' hx) (hcard hP3)
      (inf_centralizer_map_le_centGen9 P E D hx) w fun c hc => ?_
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (mem_zpowers_of_prime_card (hDx x)
      (g := (⟨b, hb⟩ : ↥(D.map (MulAut.conj x).toMonoidHom))) (g' := ⟨c, hc⟩)
      fun h => hb1 (congrArg Subtype.val h))
    obtain rfl : b ^ k = c := congrArg Subtype.val hk
    have hst : ρ ⟨b, hDX' hx hb⟩ ∈ MulAction.stabilizer (MulAut _) w :=
      MulAction.mem_stabilizer_iff.2 (by rw [MulAut.smul_def]; exact hw)
    have h := MulAction.mem_stabilizer_iff.1 (zpow_mem hst k)
    rw [MulAut.smul_def, ← map_zpow] at h
    exact h
  let T : Subgroup ↥X :=
    (centralizer (((E.subgroupOf X).map ρ : Subgroup (MulAut _)) : Set (MulAut _))).comap ρ
  have hT : ∀ x ∈ X, D.map (MulAut.conj x).toMonoidHom ≤ T.map X.subtype := by
    intro x hx b hb
    refine ⟨⟨b, hDX' hx hb⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_comap, mem_centralizer_iff]
    rintro _ ⟨e', he', rfl⟩
    rw [← map_mul, ← map_mul]
    by_cases hb1 : b = 1
    · have h1 : (⟨b, hDX' hx hb⟩ : ↥X) = 1 := Subtype.ext hb1
      rw [h1, mul_one, one_mul]
    refine map_mul_swap_of_fpf ρ ?_ ?_ ?_ (hfix x hx b hb hb1) h2
    · have h3 := pow_card_eq_one' (G := ↥(D.map (MulAut.conj x).toMonoidHom)) (x := ⟨b, hb⟩)
      rw [hDx] at h3
      have h := congrArg Subtype.val h3
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
      exact Subtype.ext (by simpa using h)
    · exact Subtype.ext (by simpa using hE2 _ (mem_subgroupOf.1 he'))
    · have hbe : b * (e' : G) * b⁻¹ ∈ E := (hXE (hDX' hx hb) e').1 (mem_subgroupOf.1 he')
      exact Subtype.ext (hEc _ (mem_subgroupOf.1 he') _ hbe)
  have hXT : X ≤ T.map X.subtype := hgen _ hT
  have hEk : E ≤ ρ.ker.map X.subtype := hE.trans <| (commutator_le).2 fun e he g hg => by
    obtain ⟨t, ht, rfl⟩ := hXT hg
    refine ⟨⁅(⟨e, hEX he⟩ : ↥X), t⁆, ?_, by simp [commutatorElement_def]⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mem_centralizer_iff.1 (mem_comap.1 ht) _ ⟨⟨e, hEX he⟩, mem_subgroupOf.2 he, rfl⟩
  intro y hy
  have hw := eq_one_of_forall_conjQuotHom_eq hRP hXP hXR Nat.prime_two
    (fun e => ⟨1, Subtype.ext (by simpa using hE2 _ e.2)⟩) hEX (hcard hP2)
    (inf_centralizer_le_centGen9 P X E D) (⟨y, hy⟩ : ↥P) fun e he => by
      obtain ⟨k, hk, hke⟩ := hEk he
      have h1 : k = ⟨e, hEX he⟩ := Subtype.ext hke
      rw [← h1, MonoidHom.mem_ker.1 hk, MulAut.one_apply]
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at hw
  exact hw

theorem le_centGen9 {P X E D : Subgroup G} (hP : Group.IsSolvable ↥P) (hP2 : ¬ 2 ∣ Nat.card P)
    (hP3 : ¬ 3 ∣ Nat.card P) (hXP : X ≤ normalizer (P : Set G)) (hEX : E ≤ X)
    (hXE : X ≤ normalizer (E : Set G)) (hE2 : ∀ e ∈ E, e ^ 2 = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE : E ≤ ⁅E, X⁆) (hDX : D ≤ X)
    (hD : Nat.card D = 3)
    (hgen : ∀ K : Subgroup G, (∀ x ∈ X, D.map (MulAut.conj x).toMonoidHom ≤ K) → X ≤ K) :
    P ≤ centGen9 P X E D := by
  suffices h : ∀ n, ∀ Q : Subgroup G, Nat.card Q = n → Group.IsSolvable ↥Q →
      ¬ 2 ∣ Nat.card Q → ¬ 3 ∣ Nat.card Q → X ≤ normalizer (Q : Set G) →
      Q ≤ centGen9 Q X E D from h _ P rfl hP hP2 hP3 hXP
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q hn hQ hQ2 hQ3 hXQ
    by_cases hQ1 : Q = ⊥
    · rw [hQ1]
      exact bot_le
    have hQQ := commutator_le_self Q
    have hlt : ⁅Q, Q⁆ < Q := by
      haveI : Nontrivial ↥Q := (nontrivial_iff_ne_bot Q).2 hQ1
      refine lt_of_le_of_ne hQQ fun heq => (Group.IsSolvable.commutator_lt_top_of_nontrivial
        ↥Q).ne (map_injective Q.subtype_injective ?_)
      rw [map_subtype_commutator, heq, ← MonoidHom.range_eq_map, range_subtype]
    have hle := ih _ (hn ▸ card_lt_of_lt hlt) ⁅Q, Q⁆ rfl
      (solvable_of_solvable_injective (inclusion_injective hQQ))
      (fun h => hQ2 (h.trans (card_dvd_of_le hQQ))) (fun h => hQ3 (h.trans (card_dvd_of_le hQQ)))
      fun g hg => by
        rw [mem_normalizer_iff_map_conj_eq, map_commutator,
          mem_normalizer_iff_map_conj_eq.1 (hXQ hg)]
    exact le_centGen9_of_commutator_le hQ2 hQ3 hXQ hEX hXE hE2 hEc hE hDX hD hgen
      (hle.trans (centGen9_mono X E D hQQ))

theorem le_of_inf_centralizer_le {P X E D M : Subgroup G} (hP : Group.IsSolvable ↥P)
    (hP2 : ¬ 2 ∣ Nat.card P) (hP3 : ¬ 3 ∣ Nat.card P) (hXP : X ≤ normalizer (P : Set G))
    (hEX : E ≤ X) (hXE : X ≤ normalizer (E : Set G)) (hE2 : ∀ e ∈ E, e ^ 2 = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE : E ≤ ⁅E, X⁆) (hDX : D ≤ X)
    (hD : Nat.card D = 3)
    (hgen : ∀ K : Subgroup G, (∀ x ∈ X, D.map (MulAut.conj x).toMonoidHom ≤ K) → X ≤ K)
    (hME : P ⊓ centralizer (E : Set G) ≤ M)
    (hMD : ∀ x ∈ X,
      P ⊓ centralizer ((D.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) ≤ M) :
    P ≤ M :=
  (le_centGen9 hP hP2 hP3 hXP hEX hXE hE2 hEc hE hDX hD hgen).trans (centGen9_le_of hME hMD)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09

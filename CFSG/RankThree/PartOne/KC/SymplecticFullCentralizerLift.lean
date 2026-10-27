module

public import CFSG.RankThree.PartOne.KC.PlaneLifting
public import CFSG.LieType.Universal.Symplectic
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
public import CFSG.RankThree.Classical.SteinbergBJCentralCoprimeLift

public section

namespace CFSG.RankThree.PartOne.KCSpFull

open CFSG CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {r : ℕ} {K : Type} [Field K]

theorem spConj_injective {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hr : 2 ≤ r) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2)) :
    Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))) := by
  have hq2 : 2 ≤ ℓ ^ f := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  have hq : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ r) ∨
      (Nat.card K = 2 ∧ 3 ≤ r) := by
    rw [hK]
    rcases Nat.lt_or_ge (ℓ ^ f) 4 with h4 | h4
    · rcases (show ℓ ^ f = 2 ∨ ℓ ^ f = 3 by omega) with h | h
      · have : r ≠ 2 := fun hr2 => hrq ⟨hr2, h⟩
        exact Or.inr (Or.inr ⟨h, by omega⟩)
      · exact Or.inr (Or.inl ⟨h, hr⟩)
    · exact Or.inl (Or.inr h4)
  have hsimple := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r
    (by omega) hq
  obtain ⟨-, -, a, b, hab⟩ := CFSG.LieType.Universal.Symplectic.isQuasisimple r K (by omega) hq
  let e := CFSG.LieType.Universal.Symplectic.centerQuotientEquiv r K
  have hcenter : Subgroup.center (StatedProj (StatedSp r K)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (StatedProj (StatedSp r K))) with h | h
    · exact h
    · exfalso
      have hv : e b ∈ Subgroup.center (StatedProj (StatedSp r K)) := h ▸ Subgroup.mem_top _
      exact hab (e.injective (by rw [map_mul, map_mul]; exact (Subgroup.mem_center_iff.mp hv
        (e a))))
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro t ht
  rw [MonoidHom.mem_ker] at ht
  have hc : t ∈ Subgroup.center (StatedProj (StatedSp r K)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut (StatedProj (StatedSp r K)) => φ g) ht
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * t = t * g * t⁻¹ * t := by
          rw [this]
      _ = t * g := by group
  rw [hcenter] at hc
  exact hc

@[expose] noncomputable def spInnerLift (r : ℕ) (K : Type) [Field K] :
    StatedSp r K →* MulAut (StatedProj (StatedSp r K)) :=
  (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).comp (proj r K)

theorem spInnerLift_apply (x : StatedSp r K) :
    spInnerLift r K x = MulAut.conj (proj r K x) := rfl

theorem spInnerLift_eq_iff (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →*
    MulAut (StatedProj (StatedSp r K)))) {x y : StatedSp r K} :
    spInnerLift r K x = spInnerLift r K y ↔ proj r K x = proj r K y :=
  hinj.eq_iff

theorem range_spInnerLift :
    (spInnerLift r K).range =
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨proj r K x, rfl⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨x, rfl⟩ := SymplecticHigher.proj_surjective (r := r) (K := K) t
    exact ⟨x, rfl⟩

theorem ker_spInnerLift (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →*
    MulAut (StatedProj (StatedSp r K)))) :
    (spInnerLift r K).ker = (proj r K).ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, spInnerLift_apply, ← map_one MulAut.conj]
  exact hinj.eq_iff

theorem ker_proj_le_center : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
  rw [SymplecticHigher.ker_proj]
  exact SymplecticHigher.spScalars_le_center

theorem coprime_card_ker_proj [Finite K] (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.Coprime (Nat.card (proj r K).ker) p := by
  rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K hr]
  exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 2 _)
    ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))

theorem not_dvd_card_ker_spInnerLift [Finite K] (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K)))) :
    ¬ p ∣ Nat.card (spInnerLift r K).ker := by
  rw [ker_spInnerLift hinj]
  intro hd
  have := coprime_card_ker_proj (K := K) hr hp hp2
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes this hd (dvd_refl p))

theorem eq_of_spInnerLift_eq [Finite K] (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))))
    {x y : StatedSp r K} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : spInnerLift r K x = spInnerLift r K y) : x = y :=
  eq_of_map_eq_of_pow_eq_one_of_coprime (proj r K) ker_proj_le_center
    (coprime_card_ker_proj hr hp hp2) (a := 1) (b := 1) (by rwa [pow_one])
    (by rwa [pow_one]) ((spInnerLift_eq_iff hinj).mp hxy)

variable (r K) in
@[expose] def IsSpPlaneLift (p : ℕ) (A : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (Ahat : Subgroup (StatedSp r K)) : Prop :=
  IsElementaryAbelian p Ahat ∧ Nat.card Ahat = p ^ 2 ∧ Ahat.map (spInnerLift r K) = A ∧
    Set.InjOn (spInnerLift r K) Ahat

theorem exists_unique_spPlaneLift [Finite K] (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))))
    (A : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hAinn : A ≤ (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range)
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2) :
    ∃! Ahat : Subgroup (StatedSp r K), IsSpPlaneLift r K p A Ahat := by
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have hrange : A ≤ (spInnerLift r K).range := by rw [range_spInnerLift]; exact hAinn
  obtain ⟨E₀, hE₀, hE₀card, hmap⟩ := exists_lift_elementaryAbelian (spInnerLift r K) hp
    (not_dvd_card_ker_spInnerLift hr hp hp2 hinj) A hrange hAcard
  have hpow : ∀ (E : Subgroup (StatedSp r K)), IsElementaryAbelian p E →
      ∀ x ∈ E, x ^ p = 1 := fun E hE x hx => by
    have := hE
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hinjOn : ∀ (E : Subgroup (StatedSp r K)), IsElementaryAbelian p E →
      Set.InjOn (spInnerLift r K) E := fun E hE x hx y hy hxy =>
    eq_of_spInnerLift_eq hr hp hp2 hinj (hpow E hE x hx) (hpow E hE y hy) hxy
  refine ⟨E₀, ⟨hE₀, hE₀card, hmap, hinjOn E₀ hE₀⟩, ?_⟩
  rintro E₁ ⟨hE₁, -, hmap₁, -⟩
  have hle : ∀ (E E' : Subgroup (StatedSp r K)), IsElementaryAbelian p E →
      IsElementaryAbelian p E' → E.map (spInnerLift r K) = E'.map (spInnerLift r K) → E ≤ E' :=
    fun E E' hE hE' hmm x hx => by
      have : spInnerLift r K x ∈ E'.map (spInnerLift r K) := hmm ▸ Subgroup.mem_map_of_mem _ hx
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp this
      have := eq_of_spInnerLift_eq hr hp hp2 hinj (hpow E' hE' y hy) (hpow E hE x hx) hxy
      rw [← this]
      exact hy
  have hmm : E₁.map (spInnerLift r K) = E₀.map (spInnerLift r K) := by rw [hmap₁, hmap]
  exact le_antisymm (hle E₁ E₀ hE₁ hE₀ hmm) (hle E₀ E₁ hE₀ hE₁ hmm.symm)

theorem spPlaneLift_unique_lift [Finite K] (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))))
    {A : Subgroup (MulAut (StatedProj (StatedSp r K)))} {Ahat : Subgroup (StatedSp r K)}
    (hlift : IsSpPlaneLift r K p A Ahat) {a : MulAut (StatedProj (StatedSp r K))} (haA : a ∈ A)
    (ha1 : a ≠ 1) :
    ∃ x ∈ Ahat, spInnerLift r K x = a ∧ orderOf x = p ∧
      ∀ y : StatedSp r K, spInnerLift r K y = a → y ^ p = 1 → y = x := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hE, -, hmap, -⟩ := hlift
  have : a ∈ Ahat.map (spInnerLift r K) := hmap ▸ haA
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp this
  have hxp : x ^ p = 1 := by
    have := hE
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hx1 : x ≠ 1 := fun h1 => ha1 (by rw [h1, map_one])
  refine ⟨x, hx, rfl, orderOf_eq_prime hxp hx1, fun y hy hyp => ?_⟩
  exact eq_of_spInnerLift_eq hr hp hp2 hinj hyp hxp hy

end CFSG.RankThree.PartOne.KCSpFull

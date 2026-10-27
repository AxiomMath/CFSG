module

public import CFSG.Quasithin.Background.B1MoreTenC
public import CFSG.Quasithin.Background.B19Setup
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.Quasithin.EmptyFaithfulMultiple
open scoped commutatorElement

namespace B1Red

section Aux

variable {Ω : Type*} [Group Ω]

theorem conj_sq_of_card_three {F : Subgroup Ω} (hF3 : Nat.card ↥F = 3) {x : Ω}
    (hx : ∀ f ∈ F, x * f * x⁻¹ ∈ F) {f : Ω} (hf : f ∈ F) : (x * x) * f * (x * x)⁻¹ = f := by
  have hFfin : Finite ↥F := Nat.finite_of_card_ne_zero (by rw [hF3]; norm_num)
  by_cases hf1 : f = 1
  · simp [hf1]
  have hf3 : f ^ 3 = 1 := by
    have : (⟨f, hf⟩ : ↥F) ^ Nat.card ↥F = 1 := pow_card_eq_one'
    rw [hF3] at this
    exact congrArg Subtype.val this
  have hord : orderOf f = 3 :=
    ((Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hf3)).resolve_left
      fun h => hf1 (orderOf_eq_one_iff.1 h)
  have hgen : Subgroup.zpowers f = F := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hf) ?_
    rw [Nat.card_zpowers, hord, hF3]
  have hh : x * f * x⁻¹ ∈ Subgroup.zpowers f := hgen ▸ hx f hf
  have e : (x * x) * f * (x * x)⁻¹ = x * (x * f * x⁻¹) * x⁻¹ := by group
  rw [e]
  rcases B19.eq_of_mem_zpowers_three hf3 hh with h1 | h2 | h3
  · exfalso
    apply hf1
    have : f = x⁻¹ * (x * f * x⁻¹) * x := by group
    rw [this, h1]
    group
  · rw [h2]
    exact h2
  · rw [h3]
    have : x * f⁻¹ * x⁻¹ = (x * f * x⁻¹)⁻¹ := by group
    rw [this, h3, inv_inv]

end Aux

section Direct

variable {V : Type*} [CommGroup V]

theorem le_centralizer_of_innerDirectProduct [Finite V] {K J C₀ F₀ : Subgroup (MulAut V)} {s : ℕ}
    {Hs : Fin s → Subgroup (MulAut V)}
    (hC₀ : C₀ ≤ Subgroup.centralizer (F₀ : Set (MulAut V)))
    (hdir1 : IsInnerDirectProduct (fun o : Option (Fin s) => o.elim C₀ Hs) J)
    (hdir2 : IsInnerDirectProduct (fun i => oddCoreOfSub (Hs i)) F₀)
    (hcard3 : ∀ i, Nat.card ↥(oddCoreOfSub (Hs i)) = 3)
    (hKJ : K ≤ J) (hK : CFSG.Open.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) :
    ∀ k ∈ K, ∀ f ∈ F₀, k * f = f * k := by
  have hFiF₀ : ∀ i, oddCoreOfSub (Hs i) ≤ F₀ := fun i =>
    hdir2.2.2 ▸ le_iSup (fun i => oddCoreOfSub (Hs i)) i
  have hFiH : ∀ i, oddCoreOfSub (Hs i) ≤ Hs i := fun i => Subgroup.map_subtype_le _
  have hJnorm : ∀ i, J ≤ Subgroup.normalizer
      ((oddCoreOfSub (Hs i) : Subgroup (MulAut V)) : Set (MulAut V)) := by
    intro i
    rw [← hdir1.2.2]
    refine iSup_le fun o => ?_
    cases o with
    | none =>
      refine le_normalizer_of_conj fun x hx f hf => ?_
      have hxc : x * f = f * x := (Subgroup.mem_centralizer_iff.1 (hC₀ hx) f (hFiF₀ i hf)).symm
      have : x * f * x⁻¹ = f := by rw [hxc]; group
      rw [this]
      exact hf
    | some j =>
      by_cases hij : j = i
      · subst hij
        refine le_normalizer_of_conj fun x hx f hf => ?_
        obtain ⟨f₀, hf₀, rfl⟩ := hf
        have hconj := (inferInstance : (CFSG.oddCore ↥(Hs j)).Normal).conj_mem f₀ hf₀ ⟨x, hx⟩
        exact ⟨_, hconj, by simp⟩
      · refine le_normalizer_of_conj fun x hx f hf => ?_
        have hcomm : x * f = f * x :=
          hdir1.1 (some j) (some i) (fun h => hij (Option.some.inj h)) x hx f (hFiH i hf)
        have : x * f * x⁻¹ = f := by rw [hcomm]; group
        rw [this]
        exact hf
  have hsq : ∀ x ∈ J, x * x ∈ Subgroup.centralizer (F₀ : Set (MulAut V)) := by
    intro x hx
    have hle : F₀ ≤ Subgroup.centralizer ({x * x} : Set (MulAut V)) := by
      rw [← hdir2.2.2]
      refine iSup_le fun i => ?_
      intro f hf
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := conj_sq_of_card_three (hcard3 i)
        (fun f hf => (Subgroup.mem_normalizer_iff.1 (hJnorm i hx) f).1 hf) hf
      calc f * (x * x) = ((x * x) * f * (x * x)⁻¹) * (x * x) := by rw [h1]
        _ = (x * x) * f := by group
    refine Subgroup.mem_centralizer_iff.2 fun f hf => ?_
    have := hle hf
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hKo : K ≤ oTwoUpper J := by
    rcases hK with hq | h3
    · exact perfect_le_oTwoUpper' hKJ ⟨hq.1⟩
    · intro k hk
      exact mem_oTwoUpper_of_odd (hKJ hk) (odd_orderOf_of_card_three h3 hk)
  have hoS : oTwoUpper J ≤ J ⊓ Subgroup.centralizer (F₀ : Set (MulAut V)) :=
    oTwoUpper_le_of_pow_mem fun x hx => ⟨1, by
      rw [pow_one, pow_two]
      exact ⟨J.mul_mem hx hx, hsq x hx⟩⟩
  intro k hk f hf
  exact (Subgroup.mem_centralizer_iff.1 (hoS (hKo hk)).2 f hf).symm

theorem ffJP_conj_mem {X : Subgroup (MulAut V)} {P : Set (Subgroup (MulAut V))}
    (hP : IsStableFF X P) {g : MulAut V} (hg : g ∈ X) {j : MulAut V} (hj : j ∈ ffJP P X) :
    g * j * g⁻¹ ∈ ffJP P X := by
  have hle : (ffJP P X).map (MulAut.conj g).toMonoidHom ≤ ffJP P X := by
    unfold ffJP
    rw [Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hA => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hAX => ?_
    refine B19.le_ffJP (hP.2.2.1 A hA g hg) ?_
    rintro _ ⟨a, ha, rfl⟩
    exact X.mul_mem (X.mul_mem hg (hAX ha)) (X.inv_mem hg)
  have := hle ⟨j, hj, rfl⟩
  simpa [MulAut.conj_apply] using this

theorem K_le_ffJ {G K A : Subgroup (MulAut V)} (hKG : K ≤ G) (hA : IsFFStarOffender G A)
    (hKA : ⁅K, A⁆ = K) : K ≤ ffJ G := by
  calc K = ⁅K, A⁆ := hKA.symm
    _ ≤ ffJ G := by
      rw [Subgroup.commutator_le]
      intro k hk a ha
      have h1 : k * a * k⁻¹ ∈ B1.conjAut k A := by
        refine B1.mem_conjAut.2 ?_
        have e : k⁻¹ * (k * a * k⁻¹) * k = a := by group
        rw [e]
        exact ha
      have h2 : B1.conjAut k A ≤ ffJ G := B19.le_ffJ (B1.isFFStarOffender_conjAut hA (hKG hk))
      exact (ffJ G).mul_mem (h2 h1) ((ffJ G).inv_mem (B19.le_ffJ hA ha))

end Direct

end B1Red

end CFSG.Quasithin

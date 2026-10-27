module

public import CFSG.Quasithin.Background.D2Seventeen
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.Quasithin

namespace Gap6

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V]

section Fitting

variable {X : Subgroup (MulAut V)}

theorem fstar_of_solvable (hsolv : Group.IsSolvable ↥X) {g : MulAut V} (hg : g ∈ X)
    (hc : ∀ f ∈ fittingOf X, g * f = f * g) : g ∈ fittingOf X := by
  have hcen : (⟨g, hg⟩ : ↥X) ∈ Subgroup.centralizer (CFSG.fittingSubgroup ↥X : Set ↥X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f' hf'
    exact Subtype.ext (hc (f' : MulAut V) ⟨f', hf', rfl⟩).symm
  exact ⟨⟨g, hg⟩, CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv hcen, rfl⟩

theorem eq_one_of_centralizes_odd (hsolv : Group.IsSolvable ↥X) (hO2 : pCoreOf 2 X = ⊥)
    {a : MulAut V} (haX : a ∈ X) (ha2 : a ^ 2 = 1)
    (hc : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ y ∈ pCoreOf p X, a * y = y * a) : a = 1 := by
  by_contra ha1
  have hodd : oddFitting X ≤ Subgroup.centralizer ({a} : Set (MulAut V)) := by
    refine iSup_le fun p => iSup_le fun hp => iSup_le fun hp2 => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc p hp hp2 y hy).symm
  have haF : a ∈ fittingOf X := by
    refine fstar_of_solvable hsolv haX fun f hf => ?_
    have := Subgroup.mem_centralizer_singleton_iff.mp (hodd (fittingOf_le_oddFitting hO2 hf))
    exact this.symm
  have hord : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hdvd : orderOf (⟨a, haF⟩ : ↥(fittingOf X)) ∣ Nat.card (fittingOf X) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr (odd_card_fittingOf hO2)) (even_iff_two_dvd.mpr hdvd)

theorem exists_odd_prime_comm_ne_bot (hsolv : Group.IsSolvable ↥X) (hO2 : pCoreOf 2 X = ⊥)
    {A : Subgroup (MulAut V)} (hA2 : IsA2 X A) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ⁅pCoreOf p X, A⁆ ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := A)).mp hA2.ne_bot
  apply ha1
  apply Subtype.ext
  refine eq_one_of_centralizes_odd hsolv hO2 (hA2.le a.2) (hA2.isElemAbelian2.2 _ a.2)
    fun p hp hp2 y hy => ?_
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcon p hp hp2)
  have h2 := Subgroup.mem_centralizer_iff.mp (this hy) (a : MulAut V) a.2
  exact h2

end Fitting

section Rank

variable {X : Subgroup (MulAut V)}

theorem faithful_pCore_three_of_qhatStar (hV : ∀ v : V, v ^ 2 = 1) (hsolv : Group.IsSolvable ↥X)
    (hO2 : pCoreOf 2 X = ⊥) {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X) (hrk : 1 < rk A) :
    ∀ a ∈ A, (∀ y ∈ pCoreOf 3 X, a * y = y * a) → a = 1 := by
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hAk⟩, hmin⟩ := QhatStar_spec hA
  have hcen5 : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ y ∈ pCoreOf p X, ∀ a ∈ A,
      a * y = y * a := by
    intro p hp hp2 hp3 y hy a ha
    by_contra hne
    have : Fact p.Prime := ⟨hp⟩
    have hD : ⁅pCoreOf p X, A⁆ ≠ ⊥ := commutator_ne_bot_iff.mpr ⟨y, hy, a, ha, hne⟩
    exact hp3 ((D2_13 hV hr hA hp2 rfl hD).2.2.2.2 hrk).1
  intro a ha hc3
  refine eq_one_of_centralizes_odd hsolv hO2 (hA2.le ha) (hA2.isElemAbelian2.2 a ha)
    fun p hp hp2 y hy => ?_
  by_cases h3 : p = 3
  · subst h3
    exact hc3 y hy
  · exact hcen5 p hp hp2 h3 y hy a ha

theorem rk_le_two_of_qhatStar (hV : ∀ v : V, v ^ 2 = 1) (hsolv : Group.IsSolvable ↥X)
    (hO2 : pCoreOf 2 X = ⊥) (hsqtk : IsQuotientOfSQTKTC ↥X) {A : Subgroup (MulAut V)}
    (hA : A ∈ QhatStar X) : rk A ≤ 2 := by
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hAk⟩, hmin⟩ := QhatStar_spec hA
  by_contra hlt
  push Not at hlt
  have hrk : 1 < rk A := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfaith3 := faithful_pCore_three_of_qhatStar hV hsolv hO2 hA hrk
  have h131 := a131_of_faithful (X := X) (P := pCoreOf 3 X) (A := A) (p := 3) (by norm_num)
    (pCoreOf_le 3 X) (pCoreOf_isPGroup 3 X) hA2.isElemAbelian2 hA2.le
    (fun a ha y hy =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X (hA2.le ha)) y).mp hy)
    hsqtk hfaith3
  have hle := h131.2.1
  set K := pCoreOf 3 X ⊔ A with hK
  have hAK : A ≤ K := le_sup_right
  have hE : IsElemAbelian 2 (A.subgroupOf K) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact hA2.isElemAbelian2.1 _ a.2 _ b.2
    · apply Subtype.ext
      exact hA2.isElemAbelian2.2 _ hx
  have hcard : Nat.card ↥(A.subgroupOf K) = 2 ^ rk A := by
    rw [← card_eq_two_pow_of_isPGroup hA2.isElemAbelian2.isPGroup]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have := le_pRank Nat.prime_two (X := ⊤) le_top hE hcard
  omega

end Rank

section Split

omit [Finite V] in
theorem fixV_eq_sup_of_summands {A : Subgroup (MulAut V)} {U W : Subgroup V} (hsup : U ⊔ W = ⊤)
    (hinf : U ⊓ W = ⊥) (hU : ∀ g ∈ A, ∀ u ∈ U, g u ∈ U) (hW : ∀ g ∈ A, ∀ w ∈ W, g w ∈ W) :
    fixV A = (U ⊓ fixV A) ⊔ (W ⊓ fixV A) := by
  apply le_antisymm
  · intro v hv
    have hvs : v ∈ U ⊔ W := by rw [hsup]; exact Subgroup.mem_top v
    obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.mp hvs
    have hfix : ∀ g ∈ A, g u = u ∧ g w = w := by
      intro g hg
      have h1 : g u * g w = u * w := by rw [← map_mul]; exact hv g hg
      have h2 : u⁻¹ * g u = w * (g w)⁻¹ := by
        calc u⁻¹ * g u = u⁻¹ * (g u * g w) * (g w)⁻¹ := by group
          _ = u⁻¹ * (u * w) * (g w)⁻¹ := by rw [h1]
          _ = w * (g w)⁻¹ := by group
      have h3 : u⁻¹ * g u ∈ U ⊓ W :=
        ⟨U.mul_mem (U.inv_mem hu) (hU g hg u hu), h2 ▸ W.mul_mem hw (W.inv_mem (hW g hg w hw))⟩
      rw [hinf, Subgroup.mem_bot] at h3
      have hgu : g u = u := (inv_mul_eq_one.mp h3).symm
      refine ⟨hgu, ?_⟩
      have h4 : g u * g w = g u * w := by rw [h1, hgu]
      exact mul_left_cancel h4
    exact Subgroup.mul_mem_sup (⟨hu, fun g hg => (hfix g hg).1⟩ : u ∈ U ⊓ fixV A)
      (⟨hw, fun g hg => (hfix g hg).2⟩ : w ∈ W ⊓ fixV A)
  · exact sup_le inf_le_right inf_le_right

theorem rk_fixV_split {A : Subgroup (MulAut V)} {U W : Subgroup V} (hsup : U ⊔ W = ⊤)
    (hinf : U ⊓ W = ⊥) (hU : ∀ g ∈ A, ∀ u ∈ U, g u ∈ U) (hW : ∀ g ∈ A, ∀ w ∈ W, g w ∈ W) :
    rk (fixV A) = rk ↥(U ⊓ fixV A) + rk ↥(W ⊓ fixV A) := by
  have h1 := rk_sup_add_rk_inf (U ⊓ fixV A) (W ⊓ fixV A)
  have h2 : (U ⊓ fixV A) ⊓ (W ⊓ fixV A) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    have : x ∈ U ⊓ W := ⟨hx.1.1, hx.2.1⟩
    rw [hinf] at this
    exact Subgroup.mem_bot.mp this
  rw [h2, rk_bot, ← fixV_eq_sup_of_summands hsup hinf hU hW] at h1
  omega

theorem rk_split {U W : Subgroup V} (hsup : U ⊔ W = ⊤) (hinf : U ⊓ W = ⊥) :
    rk V = rk ↥U + rk ↥W := by
  have h1 := rk_sup_add_rk_inf U W
  rw [hinf, rk_bot, hsup, rk_top] at h1
  omega

end Split

end Gap6

end CFSG.Quasithin

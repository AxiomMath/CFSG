module

public import CFSG.Quasithin.EmptyFaithful.Gap6R0A

public section

namespace CFSG.Quasithin

namespace Gap6

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V]

section Fitting

variable {X : Subgroup (MulAut V)}

theorem comm_pCore_le_fitting {p : ℕ} [Fact p.Prime] {A : Subgroup (MulAut V)} (hAJ : A ≤ Jhat X)
    {S : Subgroup (MulAut V)} (hS : S ≤ pCoreOf p X) : ⁅S, A⁆ ≤ fittingOf (Jhat X) := by
  have hJX : Jhat X ≤ X := Jhat_le X
  have hPX : pCoreOf p X ≤ X := pCoreOf_le p X
  have hPn : ∀ x ∈ X, ∀ g ∈ pCoreOf p X, x * g * x⁻¹ ∈ pCoreOf p X := fun x hx g hg =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf p X hx) g).mp hg
  have hle : ⁅S, A⁆ ≤ Jhat X ⊓ pCoreOf p X := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hg₁P : g₁ ∈ pCoreOf p X := hS hg₁
    have hg₁X : g₁ ∈ X := hPX hg₁P
    have hg₂J : g₂ ∈ Jhat X := hAJ hg₂
    have hg₂X : g₂ ∈ X := hJX hg₂J
    rw [commutatorElement_def]
    refine ⟨(Jhat X).mul_mem (conj_mem_Jhat hg₁X hg₂J) ((Jhat X).inv_mem hg₂J), ?_⟩
    have e : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by group
    rw [e]
    exact (pCoreOf p X).mul_mem hg₁P (hPn g₂ hg₂X g₁⁻¹ ((pCoreOf p X).inv_mem hg₁P))
  have hP'p : IsPGroup p ↥(Jhat X ⊓ pCoreOf p X) :=
    (pCoreOf_isPGroup p X).to_le inf_le_right
  have hn : ∀ x ∈ Jhat X, ∀ g ∈ Jhat X ⊓ pCoreOf p X, x * g * x⁻¹ ∈ Jhat X ⊓ pCoreOf p X := by
    intro x hx g hg
    exact ⟨conj_mem_Jhat (hJX hx) hg.1, hPn x (hJX hx) g hg.2⟩
  exact hle.trans (le_fittingOf_of_normal inf_le_left hP'p hn)

end Fitting

section DirectSum

theorem trivial_on_C_of_direct_sum (hV : ∀ v : V, v ^ 2 = 1) {X A D : Subgroup (MulAut V)}
    (hDF : D ≤ fittingOf (Jhat X)) (hDodd : Odd (Nat.card D))
    (hdir : IsDirectSum ⊤ (commV D) (fixV (D ⊔ A))) :
    fixV (fittingOf (Jhat X)) ≤ fixV A := by
  obtain ⟨-, hinf⟩ := coprime_decomp hDodd hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top w)
  rw [← commV_eq_commSub, top_inf_eq] at hinf
  intro c hc
  have hcD : c ∈ fixV D := fixV_anti hDF hc
  have hcs : c ∈ commV D ⊔ fixV (D ⊔ A) := by rw [hdir.1]; exact Subgroup.mem_top c
  obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.mp hcs
  have hwD : w ∈ fixV D := fixV_anti le_sup_left hw
  have huD : u ∈ fixV D := by
    have : u = (u * w) * w⁻¹ := by group
    rw [this]
    exact (fixV D).mul_mem hcD ((fixV D).inv_mem hwD)
  have hu1 : u = 1 := by
    have : u ∈ commV D ⊓ fixV D := ⟨hu, huD⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact this
  subst hu1
  rw [one_mul]
  exact fixV_anti le_sup_right hw

theorem inf_fixV_le_of_direct_sum (hV : ∀ v : V, v ^ 2 = 1) {C : Subgroup V}
    {D A B : Subgroup (MulAut V)} (hDodd : Odd (Nat.card D)) (hCD : C ≤ fixV D)
    (hdir : IsDirectSum (fixV B) (commSub (fixV B) D) (fixV (D ⊔ A))) :
    C ⊓ fixV B ≤ fixV A := by
  obtain ⟨-, hinf⟩ := coprime_decomp hDodd hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top w)
  rw [← commV_eq_commSub, top_inf_eq] at hinf
  intro c hc
  have hcs : c ∈ commSub (fixV B) D ⊔ fixV (D ⊔ A) := by rw [hdir.1]; exact hc.2
  obtain ⟨n, hn, z, hz, rfl⟩ := Subgroup.mem_sup.mp hcs
  have hzD : z ∈ fixV D := fixV_anti le_sup_left hz
  have hnD : n ∈ fixV D := by
    have : n = (n * z) * z⁻¹ := by group
    rw [this]
    exact (fixV D).mul_mem (hCD hc.1) ((fixV D).inv_mem hzD)
  have hncomm : n ∈ commV D := by
    have : commSub (fixV B) D ≤ commV D := by
      rw [commV_eq_commSub]
      exact commSub_mono le_top le_rfl
    exact this hn
  have hn1 : n = 1 := by
    have : n ∈ commV D ⊓ fixV D := ⟨hncomm, hnD⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact this
  subst hn1
  rw [one_mul]
  exact fixV_anti le_sup_right hz

end DirectSum

section Hyperplane

theorem commSub_fixV_ne_bot (hV : ∀ v : V, v ^ 2 = 1) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {Q B A : Subgroup (MulAut V)} (hQp : IsPGroup p Q) (hB2 : IsPGroup 2 B)
    (hQc : ∀ q ∈ Q, ∀ b ∈ B, q * b = b * q) (hAQ : ∀ a ∈ A, ∀ z ∈ Q, a * z * a⁻¹ ∈ Q)
    (hne : ∃ y ∈ Q, ∃ t ∈ A, t * y ≠ y * t) : commSub (fixV B) A ≠ ⊥ := by
  obtain ⟨y, hyQ, t, htA, hne⟩ := hne
  have hQs : Q ≤ stabSub (fixV B) := fun q hq =>
    mem_stabSub_fixV_of_commute (fun b hb => (hQc q hq b hb).symm)
  have hfaith : ∀ q ∈ Q, (∀ u ∈ fixV B, q u = u) → q = 1 := faithful_on_fixV hV hp hQp hB2 hQc
  intro hbot
  rw [commSub_eq_bot_iff] at hbot
  have hz : t * y * t⁻¹ ∈ Q := hAQ t htA y hyQ
  have hzy : ∀ u ∈ fixV B, (t * y * t⁻¹) u = y u := by
    intro u hu
    have h1 : t⁻¹ u = u := hbot hu t⁻¹ (A.inv_mem htA)
    have h2 : y u ∈ fixV B := ((hQs hyQ) u).mpr hu
    show t (y (t⁻¹ u)) = y u
    rw [h1]
    exact hbot h2 t htA
  have h1 : (t * y * t⁻¹)⁻¹ * y = 1 := by
    refine hfaith _ (Q.mul_mem (Q.inv_mem hz) hyQ) fun u hu => ?_
    show (t * y * t⁻¹)⁻¹ (y u) = u
    rw [← hzy u hu]
    simp
  have h2 : t * y * t⁻¹ = y := inv_mul_eq_one.mp h1
  exact hne (mul_inv_eq_iff_eq_mul.mp h2)

end Hyperplane

end Gap6

end CFSG.Quasithin

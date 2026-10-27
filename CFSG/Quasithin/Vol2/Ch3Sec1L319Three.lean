module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319Common
public import CFSG.Quasithin.Vol2.Ch3Sec1L319Form

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13

section Series

variable {G : Type} [Group G]

theorem commutes_of_odd_series {y : G} {n : ℕ} (hn : Odd n) (hyn : y ^ n = 1) {L N U : Subgroup G}
    (hUe : IsElemAbelian 2 U) (hLN : L ≤ N) (hNU : N ≤ U) (hyL : ∀ l ∈ L, y * l * y⁻¹ = l)
    (hstep : ∀ x ∈ N, y * x * y⁻¹ * x⁻¹ ∈ L) : ∀ x ∈ N, y * x * y⁻¹ = x := by
  intro x hx
  set c := y * x * y⁻¹ * x⁻¹ with hc
  have hcL : c ∈ L := hstep x hx
  have hcy : y * c * y⁻¹ = c := hyL c hcL
  have hyx : y * x * y⁻¹ = c * x := by rw [hc]; group
  have hsq : c * c = 1 := by
    have := hUe.2 c (hNU (hLN hcL))
    simpa [pow_two] using this
  have key : ∀ j : ℕ, y ^ j * x * (y ^ j)⁻¹ = c ^ j * x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : y ^ (j + 1) * x * (y ^ (j + 1))⁻¹ = y * (y ^ j * x * (y ^ j)⁻¹) * y⁻¹ := by
        rw [pow_succ']; group
      rw [e, ih]
      have h2 : y * (c ^ j * x) * y⁻¹ = (y * c * y⁻¹) ^ j * (y * x * y⁻¹) := by
        rw [conj_pow]; group
      rw [h2, hcy, hyx, pow_succ]
      group
  have h1 := key n
  rw [hyn] at h1
  obtain ⟨k, rfl⟩ := hn
  have hcn : c ^ (2 * k + 1) = c := by
    rw [pow_succ, pow_mul, show c ^ 2 = 1 by simpa [pow_two] using hsq, one_pow, one_mul]
  have h2 : c ^ (2 * k + 1) = 1 := by
    have h3 : c ^ (2 * k + 1) * x = 1 * x := by simpa using h1.symm
    exact mul_right_cancel h3
  have hc1 : c = 1 := hcn ▸ h2
  calc y * x * y⁻¹ = c * x := hyx
    _ = x := by rw [hc1, one_mul]

theorem centralizes_of_odd_series {G₂ U : Subgroup G} {y : G} {n : ℕ} (hn : Odd n) (hyn : y ^ n = 1)
    (hUe : IsElemAbelian 2 U)
    (hstep : ∀ L N : Subgroup G, IsChiefStep G₂ U L N → ∀ x ∈ N, y * x * y⁻¹ * x⁻¹ ∈ L)
    {N : Subgroup G} {k : ℕ} (hs : IsChiefSeriesFrom G₂ U N k) : ∀ x ∈ N, y * x * y⁻¹ = x := by
  induction hs with
  | bot =>
    intro x hx
    rw [Subgroup.mem_bot.mp hx]
    simp
  | central hst _ _ ih =>
    exact commutes_of_odd_series hn hyn hUe hst.2.2.1.le hst.1.1 ih (hstep _ _ hst)
  | noncentral hst _ _ ih =>
    exact commutes_of_odd_series hn hyn hUe hst.2.2.1.le hst.1.1 ih (hstep _ _ hst)

end Series

@[expose] def Lemma319KerNoThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M M₀ H V : Subgroup G, InM T M → ∀ h : Hyp315Base T M M₀ H V, Hyp315.CaseII M H V →
      qInt M₀ V h.reduced.2.2.1 = 2 → IsUniqueM M₀ M → V ≤ pCoreOf 2 H → ¬ IsDualFFOn M₀ V →
      Concl319 T M V H False → NoThreeInCV M V → KerNoThree M H

theorem lemma319KerNoThree_of_common (hC : Lemma319Common) : Lemma319KerNoThree := by
  intro G _ _ T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl hno h3
  obtain ⟨hmp, -, hUT, -, -, hstep2⟩ :=
    hC G T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(kerIn (H ⊓ M) H)) 3 h3
  have hyJ : (y : G) ∈ kerIn (H ⊓ M) H := y.2
  have hyH : (y : G) ∈ H := hmp.kerIn_le_H hyJ
  have hyM : (y : G) ∈ M := (inf_le_right : H ⊓ M ≤ M) (kerIn_le hyJ)
  have hy3 : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  have hyn : (y : G) ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one _
  have hcent : ∀ x ∈ conjClosure V H, (y : G) * x * (y : G)⁻¹ = x := by
    refine centralizes_of_odd_series (n := 3) (by decide) hyn hconcl.elemAbelian ?_ hconcl.chief
    intro L N hst x hx
    by_cases hnc : IsCentralStep H L N
    · exact hnc (y : G) hyH x hx
    · have hyC : (y : G) ∈ centralizerMod L H N := by
        rw [hstep2 L N hst hnc]
        exact hyJ
      exact hyC.2.2 x hx
  exact hno (y : G) hyM (fun v hv => by rw [hcent v (le_conjClosure V H hv)]) hy3

end CFSG.Quasithin.H13.L319

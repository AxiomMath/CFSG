module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKSweep
public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Grp
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKFork

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.H13.L829N
open scoped commutatorElement

theorem nk_comm_in_Q {G : Type} [Group G] {H M K : Subgroup G} (hMH : M ≤ H)
    (hHn : H ≤ Subgroup.normalizer (K : Set G))
    (hJ : ∀ x : G, x ∈ kerIn M H ↔
      x ∈ K ⊔ pCoreOf 2 H ∧ ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    {j : G} (hj : j ∈ kerIn M H) {x : G} (hx : x ∈ K) :
    j * x * j⁻¹ * x⁻¹ ∈ K ⊓ pCoreOf 2 H := by
  have hjH : j ∈ H := hMH (kerIn_le hj)
  refine ⟨?_, ((hJ j).mp hj).2 x (Subgroup.mem_sup_left hx)⟩
  exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHn hjH) x).mp hx) (K.inv_mem hx)

theorem nk_Q_two {G : Type} [Group G] [Finite G] {H K : Subgroup G} (q : G) (hq : q ∈ K ⊓ pCoreOf 2 H) :
    ∃ m : ℕ, q ^ 2 ^ m = 1 := by
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨q, hq.2⟩
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

theorem nk_Q_norm {G : Type} [Group G] {H K : Subgroup G}
    (hHn : H ≤ Subgroup.normalizer (K : Set G)) {h : G} (hh : h ∈ H) {q : G}
    (hq : q ∈ K ⊓ pCoreOf 2 H) : h * q * h⁻¹ ∈ K ⊓ pCoreOf 2 H :=
  ⟨(Subgroup.mem_normalizer_iff.mp (hHn hh) q).mp hq.1,
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh) q).mp
      hq.2⟩

theorem nk_s9_group_data (hL32 : NKLeafL32)
    {G : Type} [Group G] [Finite G] {H T M K V : Subgroup G}
    (hT : IsSylowTwoOf T H) (hTM : T ≤ M) (hHK : H = K ⊔ T) (hKc : K ∈ cComp H)
    (hq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K))
    (hres : L32Residual H T (H ⊓ M) K)
    (hVT : V ≤ T) (hVe : IsElemAbelian 2 V) (hVJ : ¬ V ≤ kerIn (H ⊓ M) H)
    (hP7 : H ⊓ M ≤ Subgroup.normalizer (V : Set G))
    (hKG : K ≤ Subgroup.closure {x : G | ∃ h ∈ H, ∃ v ∈ V, x = h * v * h⁻¹}) :
    ∃ v ∈ V, K ≤ Subgroup.closure {x : G | ∃ k ∈ K, x = k * v * k⁻¹} ∧
      ∃ Q : Subgroup G, Q ≤ K ∧ (∀ q ∈ Q, ∃ m : ℕ, q ^ 2 ^ m = 1) ∧
        (∀ q ∈ Q, ∀ x ∈ K, x * q * x⁻¹ ∈ Q) ∧ (∀ q ∈ Q, v * q * v⁻¹ ∈ Q) ∧
        (∃ k₀ ∈ K, ∀ x ∈ K, ∃ q ∈ Q, v * x * v⁻¹ = q * (k₀ * x * k₀⁻¹)) ∧
        (∀ z ∈ K, z ∈ kerIn (H ⊓ M) H → ∀ x ∈ K, ∃ q ∈ Q, z * x * z⁻¹ = q * x) := by
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hres.1
  have hJ := hres.2.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := hT.1
  have hHn : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
  obtain ⟨hs, hna, hsolv⟩ := star_facts_case2 hKc hHK hTK hq hJ
  have hKs3 : IsPSL 3 2 1 ↥(E2.star (H ⊓ M) H K) := by
    rcases hres.2.2 with ⟨hL, -, -⟩ | ⟨hL, -, -⟩
    · exact hL
    · exact isPSL_three_two_of_isPSL_two_seven hL
  have hOut : UOut ↥(E2.star (H ⊓ M) H K)
      ((E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)).subgroupOf (E2.star (H ⊓ M) H K)) := by
    rcases hres.2.2 with ⟨-, -, hBor⟩ | ⟨-, hMK, -⟩
    · exact nk_uout_of_borel hBor (fun S hS => ((hL32 _ hKs3).2 S hS).1)
    · have hsyl := nk_star_sylow (M := H ⊓ M) hT hKc
      have hO := nk_uout_of_centralizer hsyl (fun S hS => ((hL32 _ hKs3).2 S hS).2)
      rw [← hMK] at hO
      exact hO
  obtain ⟨a, haV, haK, ha1⟩ := nk_fork_inner_star hT hTM hHK hTK hs hna (hVT.trans hTH) hVe hVJ
    hP7 hOut
  obtain ⟨av, hav, rfl⟩ := mem_star_cs5.mp haV
  obtain ⟨bk, hbk, hbkav⟩ := mem_star_cs5.mp haK
  set v : G := (av : G) with hv
  set k₀ : G := (bk : G) with hk₀
  have hvJ : v ∉ kerIn (H ⊓ M) H := by
    intro hvJ'
    apply ha1
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hvJ'
  have hjJ : k₀⁻¹ * v ∈ kerIn (H ⊓ M) H := by
    have := QuotientGroup.eq.mp hbkav
    have h2 := Subgroup.mem_subgroupOf.mp this
    simpa using h2
  have hnot : ∃ k ∈ K, ⁅v, k⁆ ∉ kerIn (H ⊓ M) H := by
    by_contra hcon
    push Not at hcon
    apply hvJ
    set ak : ↥(E2.star (H ⊓ M) H K) := ⟨QuotientGroup.mk bk, mem_star_cs5.mpr ⟨bk, hbk, rfl⟩⟩
      with hak
    have hcenAk : ak ∈ Subgroup.center ↥(E2.star (H ⊓ M) H K) := by
      rw [Subgroup.mem_center_iff]
      intro b
      obtain ⟨x, hxK, hxb⟩ := mem_star_cs5.mp b.2
      apply Subtype.ext
      show (b : E2.StarQuot (H ⊓ M) H) * QuotientGroup.mk bk =
        QuotientGroup.mk bk * (b : E2.StarQuot (H ⊓ M) H)
      rw [← hxb, hbkav]
      have h1 : (QuotientGroup.mk (av * x * av⁻¹ * x⁻¹) : E2.StarQuot (H ⊓ M) H) = 1 := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        have e : (((av * x * av⁻¹ * x⁻¹ : ↥H)) : G) = ⁅v, (x : G)⁆ := by
          simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, hv]
        rw [e]
        exact hcon (x : G) hxK
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
      set A : E2.StarQuot (H ⊓ M) H := QuotientGroup.mk av with hA
      set X : E2.StarQuot (H ⊓ M) H := QuotientGroup.mk x with hX
      have h2 : A * X = X * A := by
        calc A * X = (A * X * A⁻¹ * X⁻¹) * (X * A) := by group
          _ = X * A := by rw [h1, one_mul]
      exact h2.symm
    rw [center_eq_bot_of_simple_nonab hs hna, Subgroup.mem_bot] at hcenAk
    have h1 : (QuotientGroup.mk bk : E2.StarQuot (H ⊓ M) H) = 1 := congrArg Subtype.val hcenAk
    rw [hbkav, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  obtain ⟨k₁, hk₁, hk₁not⟩ := hnot
  have hcl := s9g_K_le_closure_conj (M := H ⊓ M) hKH hperf hs hsolv hTK (hVT hav) hk₁ hk₁not
  refine ⟨v, hav, hcl, K ⊓ pCoreOf 2 H, inf_le_left, nk_Q_two, ?_, ?_, ?_, ?_⟩
  · intro q hq x hx
    exact nk_Q_norm hHn (hKH hx) hq
  · intro q hq
    exact nk_Q_norm hHn av.2 hq
  · refine ⟨k₀, hbk, fun x hx => ?_⟩
    have h1 := nk_comm_in_Q (inf_le_left) hHn hJ hjJ hx
    refine ⟨k₀ * (k₀⁻¹ * v * x * (k₀⁻¹ * v)⁻¹ * x⁻¹) * k₀⁻¹, nk_Q_norm hHn (hKH hbk) h1, ?_⟩
    group
  · intro z hz hzJ x hx
    have h1 := nk_comm_in_Q (inf_le_left) hHn hJ hzJ hx
    exact ⟨z * x * z⁻¹ * x⁻¹, h1, by group⟩

end CFSG.Quasithin.H13.L829NK

module

public import CFSG.Quasithin.Recognition.St84.Sec4Bounds

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86

open scoped Pointwise commutatorElement

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

private theorem le_arcStab_of_le_Z_inf_Z (X : Setup Γ G)
    {d₁ e : ℕ} (hd₁ : X.HasB 1 d₁) (he : X.HasB (d₁ + 1) e) {U : Subgroup G}
    (hU : U ≤ X.Z 1 ⊓ X.Z (d₁ + 1)) :
    U ≤ X.arcStab (1 - (d₁ : ℤ)) ((1 - (d₁ : ℤ)) + ((2 * d₁ + e : ℕ) : ℤ)) := by
  refine X.le_arcStab_of_fixSet ?_
  intro j hj
  rw [Set.mem_Icc] at hj
  have h1 := X.fixSet_Z 1 hd₁
  have h2 := X.fixSet_Z (d₁ + 1) he
  refine fun q hq => ?_
  by_cases hj1 : j ≤ (1 : ℤ) + (d₁ : ℤ)
  · have hmem : j ∈ X.fixSet (X.Z 1) := by
      rw [h1, Set.mem_Icc]
      omega
    exact hmem q (hU.trans inf_le_left hq)
  · have hmem : j ∈ X.fixSet (X.Z (d₁ + 1)) := by
      rw [h2, Set.mem_Icc]
      omega
    exact hmem q (hU.trans inf_le_right hq)

theorem s46_step1 (X : Setup Γ G) {r : ℕ} (H : X.Sec4Hyp s r) {d₁ : ℕ}
    (hd₁ : X.HasB 1 d₁) {e : ℕ} (he : X.HasB (d₁ + 1) e)
    (hR : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≤ X.Z 1 ⊓ X.Z (d₁ + 1))
    (hR1 : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≠ ⊥) : 2 * d₁ + e ≤ r := by
  have hR2 : IsPGroup 2 (⁅X.Z 1, X.Z (d₁ + 1)⁆ : Subgroup G) :=
    ((pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1)).to_le (hR.trans inf_le_left)
  simpa using X.le_r_of_fixes H hR2 hR1 (X.le_arcStab_of_le_Z_inf_Z hd₁ he hR)

private theorem sup_Q_le_centralizer_sq (X : Setup Γ G) {i j : ℤ}
    (hR : ⁅X.Z j, X.Z i⁆ ≤ X.Z i) (hRelem : IsElemAbelian 2 ⁅X.Z j, X.Z i⁆) {y : G}
    (hy : y ∈ X.Z i) : X.Z j ⊔ X.Q i ≤ Subgroup.centralizer {y ^ 2} := by
  refine sup_le (fun a ha => ?_) (fun b hb => ?_)
  · have hcR : ⁅a, y⁆ ∈ ⁅X.Z j, X.Z i⁆ := Subgroup.commutator_mem_commutator ha hy
    have hc2 : ⁅a, y⁆ ^ 2 = 1 := hRelem.2 ⁅a, y⁆ hcR
    have hcomm : Commute ⁅a, y⁆ y := X.Z_commute i ⁅a, y⁆ (hR hcR) y hy
    have hconj : a * y * a⁻¹ = ⁅a, y⁆ * y :=
      conj_eq_commutatorElement_mul (g₁ := a) (g₂ := y)
    have h : a * y ^ 2 * a⁻¹ = y ^ 2 :=
      calc a * y ^ 2 * a⁻¹ = (a * y * a⁻¹) ^ 2 := by rw [conj_pow]
        _ = (⁅a, y⁆ * y) ^ 2 := by rw [hconj]
        _ = ⁅a, y⁆ ^ 2 * y ^ 2 := hcomm.mul_pow 2
        _ = y ^ 2 := by rw [hc2, one_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h)
  · have hcomm : Commute b y :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center i hy)).2 b hb
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm.pow_right 2).eq

theorem sq_le_centerOf_L (X : Setup Γ G) {i j : ℤ}
    (hP : IsSylowTwoOf (X.Z j ⊔ X.Q i) (X.L i))
    (hR : ⁅X.Z j, X.Z i⁆ ≤ X.Z i)
    (hRelem : IsElemAbelian 2 ⁅X.Z j, X.Z i⁆) :
    ∀ x ∈ X.Z i, x ^ 2 ∈ centerOf (X.L i) := by
  intro x₀ hx₀
  have hTcen : ∀ y ∈ X.Z i, ∀ t ∈ X.Z j ⊔ X.Q i, t * y ^ 2 * t⁻¹ = y ^ 2 := by
    intro y hy t ht
    exact mul_inv_eq_iff_eq_mul.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (X.sup_Q_le_centralizer_sq hR hRelem hy ht))
  have hxL : x₀ ^ 2 ∈ X.L i :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi i)) (X.Q_le_Gi i)
      ((X.Q i).pow_mem (X.Z_le_Q i hx₀) 2)
  refine Subgroup.mem_inf.mpr ⟨hxL, ?_⟩
  rw [show X.L i = Subgroup.closure {g : G | g ∈ X.Gi i ∧ ∃ n : ℕ, g ^ 2 ^ n = 1} from rfl,
    Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro g ⟨hgGi, n, hgn⟩
  have hgL : g ∈ X.L i := Subgroup.subset_closure ⟨hgGi, n, hgn⟩
  haveI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  have hT' : IsSylowTwoOf ((X.Z j ⊔ X.Q i).subgroupOf (X.Gi i))
      ((X.L i).subgroupOf (X.Gi i)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      exact Subgroup.mem_subgroupOf.mpr (hP.1 (Subgroup.mem_subgroupOf.mp hy))
    · exact hP.2.1.of_equiv
        (Subgroup.subgroupOfEquivOfLe (hP.1.trans (X.L_le_Gi i))).symm
    · show ¬ 2 ∣ ((X.Z j ⊔ X.Q i).subgroupOf (X.Gi i)).relIndex
        ((X.L i).subgroupOf (X.Gi i))
      rw [Subgroup.relIndex_subgroupOf (X.L_le_Gi i)]
      exact hP.2.2
  have hP' : IsPGroup 2 (Subgroup.zpowers (⟨g, hgGi⟩ : ↥(X.Gi i))) := by
    have hgn' : (⟨g, hgGi⟩ : ↥(X.Gi i)) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hgn)
    have hd : orderOf (⟨g, hgGi⟩ : ↥(X.Gi i)) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hgn'
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, hk]
  obtain ⟨xg, hxgH, hxgle⟩ :=
    CFSG.Quasithin.F7.isSylowTwoOf_exists_conj_le hT'
      (P := Subgroup.zpowers (⟨g, hgGi⟩ : ↥(X.Gi i)))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_subgroupOf.mpr hgL)) hP'
  set l : G := ((xg : ↥(X.Gi i)) : G) with hl
  have hlGi : l ∈ X.Gi i := xg.2
  have hmemT' : xg⁻¹ * (⟨g, hgGi⟩ : ↥(X.Gi i)) * xg ∈
      (X.Z j ⊔ X.Q i).subgroupOf (X.Gi i) :=
    mem_conjSub.mp (hxgle (Subgroup.mem_zpowers _))
  have htT : l⁻¹ * g * l ∈ X.Z j ⊔ X.Q i := by
    have h := Subgroup.mem_subgroupOf.mp hmemT'
    simpa [l] using h
  set y : G := l⁻¹ * x₀ * l with hy
  have hyZi : y ∈ X.Z i := by
    have hnorm : conjSub l⁻¹ (X.Z i) = X.Z i := X.Z_normal i l⁻¹ ((X.Gi i).inv_mem hlGi)
    have hy' : y ∈ conjSub l⁻¹ (X.Z i) := by
      rw [mem_conjSub]
      simpa [y, mul_assoc] using hx₀
    rwa [hnorm] at hy'
  have htcen := hTcen y hyZi (l⁻¹ * g * l) htT
  have hx0 : l * y * l⁻¹ = x₀ := by
    rw [hy]; group
  have hx0sq : l * y ^ 2 * l⁻¹ = x₀ ^ 2 := by
    rw [← conj_pow, hx0]
  have hgconj : g * x₀ ^ 2 * g⁻¹ = x₀ ^ 2 := by
    have hgt : g = l * (l⁻¹ * g * l) * l⁻¹ := by group
    calc g * x₀ ^ 2 * g⁻¹
        = (l * (l⁻¹ * g * l) * l⁻¹) * x₀ ^ 2 *
            (l * (l⁻¹ * g * l) * l⁻¹)⁻¹ := by conv_lhs => rw [hgt]
      _ = (l * (l⁻¹ * g * l) * l⁻¹) * (l * y ^ 2 * l⁻¹) *
            (l * (l⁻¹ * g * l) * l⁻¹)⁻¹ := by rw [hx0sq]
      _ = l * ((l⁻¹ * g * l) * y ^ 2 * (l⁻¹ * g * l)⁻¹) * l⁻¹ := by group
      _ = l * y ^ 2 * l⁻¹ := by rw [htcen]
      _ = x₀ ^ 2 := hx0sq
  calc g * x₀ ^ 2 = (g * x₀ ^ 2 * g⁻¹) * g := by group
    _ = x₀ ^ 2 * g := by rw [hgconj]

structure CaseA (X : Setup Γ G) : Prop where
  hyp : X.Sec4Hyp 7 6
  b₁ : X.HasB 1 2
  R_le : ⁅X.Z (-1), X.Z 1⁆ ≤ X.Z (-1) ⊓ X.Z 1
  R_ne : ⁅X.Z (-1), X.Z 1⁆ ≠ ⊥

structure CaseB (X : Setup Γ G) : Prop where
  hyp : X.Sec4Hyp 5 4
  b₀ : X.HasB 0 1
  b₁ : X.HasB 1 1
  R_le : ⁅X.Z 0, X.Z 1⁆ ≤ X.Z 0 ⊓ X.Z 1
  R_ne : ⁅X.Z 0, X.Z 1⁆ ≠ ⊥

private theorem comm_Z_neg_one_Z_one_of (X : Setup Γ G)
    (hR : ⁅X.Z 1, X.Z 3⁆ ≤ X.Z 1 ⊓ X.Z 3) (hR1 : ⁅X.Z 1, X.Z 3⁆ ≠ ⊥) :
    ⁅X.Z (-1), X.Z 1⁆ ≤ X.Z (-1) ⊓ X.Z 1 ∧ ⁅X.Z (-1), X.Z 1⁆ ≠ ⊥ := by
  have hτ1 : X.Z (-1) = conjSub X.τ⁻¹ (X.Z 1) := by
    have h := X.Z_add (-1) 1
    rw [show (1 : ℤ) + 2 * (-1) = -1 by norm_num, zpow_neg_one] at h
    exact h
  have hτ3 : conjSub X.τ⁻¹ (X.Z 3) = X.Z 1 := by
    have h := X.Z_add (-1) 3
    rw [show (3 : ℤ) + 2 * (-1) = 1 by norm_num, zpow_neg_one] at h
    exact h.symm
  have hτ1' : (X.Z 1).map (MulAut.conj X.τ⁻¹).toMonoidHom = X.Z (-1) := hτ1.symm
  have hτ3' : (X.Z 3).map (MulAut.conj X.τ⁻¹).toMonoidHom = X.Z 1 := hτ3
  have hmap : conjSub X.τ⁻¹ (⁅X.Z 1, X.Z 3⁆ : Subgroup G) = ⁅X.Z (-1), X.Z 1⁆ := by
    change (⁅X.Z 1, X.Z 3⁆ : Subgroup G).map (MulAut.conj X.τ⁻¹).toMonoidHom =
      ⁅X.Z (-1), X.Z 1⁆
    rw [Subgroup.map_commutator, hτ1', hτ3']
  have hRle : ⁅X.Z (-1), X.Z 1⁆ ≤ X.Z (-1) ⊓ X.Z 1 := by
    calc ⁅X.Z (-1), X.Z 1⁆ = conjSub X.τ⁻¹ ⁅X.Z 1, X.Z 3⁆ := hmap.symm
      _ ≤ conjSub X.τ⁻¹ (X.Z 1 ⊓ X.Z 3) := conjSub_mono X.τ⁻¹ hR
      _ = conjSub X.τ⁻¹ (X.Z 1) ⊓ conjSub X.τ⁻¹ (X.Z 3) := conjSub_inf X.τ⁻¹ _ _
      _ = X.Z (-1) ⊓ X.Z 1 := by rw [← hτ1, hτ3]
  have hRne : ⁅X.Z (-1), X.Z 1⁆ ≠ ⊥ := by
    intro hbot
    rw [← hmap] at hbot
    exact hR1 ((conjSub_eq_bot_iff X.τ⁻¹).mp hbot)
  exact ⟨hRle, hRne⟩

theorem caseA_of (X : Setup Γ G) {r : ℕ} (H : X.Sec4Hyp s r) {d₁ : ℕ}
    (hd₁ : X.HasB 1 d₁)
    (hR : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≤ X.Z 1 ⊓ X.Z (d₁ + 1))
    (hR1 : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≠ ⊥) (hev : Even d₁) :
    s = 7 ∧ r = 6 ∧ d₁ = 2 ∧ X.CaseA := by
  have hev' : Even ((d₁ : ℤ)) := by exact_mod_cast hev
  have hd₁' : X.HasB (d₁ + 1) d₁ :=
    (X.hasB_iff_of_even (i := d₁ + 1) (j := 1) (by simpa using hev') d₁).mpr hd₁
  have hstep : 2 * d₁ + d₁ ≤ r := X.s46_step1 H hd₁ hd₁' hR hR1
  have hb := X.hasB_one_bounds H hd₁
  have hd1 : 1 ≤ d₁ := X.one_le_of_hasB hd₁
  have hd₂ : d₁ = 2 := by
    rcases hev with ⟨k, hk⟩
    omega
  have hr6 : r = 6 := by omega
  subst hd₂
  subst hr6
  have hs7 : s = 7 := by
    by_contra hne
    have hsle : s ≤ 7 := by
      have := H.le_r
      omega
    have hslt : s < 7 := lt_of_le_of_ne hsle hne
    have hs5 : s = 5 := by
      have h5 : 5 ≤ s := H.five_le
      rcases H.odd_s with ⟨k, hk⟩
      omega
    subst hs5
    have hd3 : X.HasB 3 2 :=
      (X.hasB_iff_of_even (i := 3) (j := 1) (by exact ⟨1, by norm_num⟩) 2).mpr hd₁
    have hRfix : ⁅X.Z 1, X.Z 3⁆ ≤ X.arcStab (-1) 5 := by
      simpa using X.le_arcStab_of_le_Z_inf_Z hd₁ hd3 hR
    have hR2 : IsPGroup 2 (⁅X.Z 1, X.Z 3⁆ : Subgroup G) :=
      ((pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1)).to_le (hR.trans inf_le_left)
    have hPle := X.le_pCoreOf_arcStab_r H hR2 hRfix
    have harg : (-1 : ℤ) + ((6 : ℕ) : ℤ) = 5 := by norm_num
    rw [harg] at hPle
    have hPne : pCoreOf 2 (X.arcStab (-1) 5) ≠ ⊥ := by
      intro hbot
      rw [hbot] at hPle
      exact hR1 (le_bot_iff.mp hPle)
    obtain ⟨-, -, -, hLeft, -⟩ := X.pCoreOf_arcStab_r H (-1) hPne
    exact absurd ((H.ends_even (-1) 6 (by omega)).2 hLeft) (by norm_num)
  subst hs7
  obtain ⟨hRle, hRne⟩ := X.comm_Z_neg_one_Z_one_of hR hR1
  exact ⟨rfl, rfl, rfl, ⟨H, hd₁, hRle, hRne⟩⟩

end Setup

end CFSG.Quasithin.St84

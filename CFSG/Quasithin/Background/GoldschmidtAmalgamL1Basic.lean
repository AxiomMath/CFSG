module

public import CFSG.Quasithin.Recognition.F112WAssembly
public import CFSG.Quasithin.Background.GoldschmidtAmalgamVBase
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

omit [Finite D] in
theorem pCoreOf_top_eq (p : ℕ) : pCoreOf p (⊤ : Subgroup D) = CFSG.Open.pCore p D := by
  unfold pCoreOf
  exact map_pCore_mulEquiv p (Subgroup.topEquiv : (⊤ : Subgroup D) ≃* D)

structure GoldHyp (G₁ G₂ : Subgroup D) : Prop where
  amalgam : IsGoldschmidtVAmalgam G₁ G₂
  charTwo₁ : CharTwo G₁
  charTwo₂ : CharTwo G₂

omit [Finite D] in
theorem omega_le_centerOf (T : Subgroup D) : quasithinOmegaOneCenter T ≤ centerOf T := by
  unfold quasithinOmegaOneCenter centerOf
  rw [Subgroup.closure_le]
  exact fun x hx => hx.1

omit [Finite D] in
theorem mem_omega {T : Subgroup D} {z : D} (hz : z ∈ centerOf T) (hz2 : z ^ 2 = 1) :
    z ∈ quasithinOmegaOneCenter T :=
  Subgroup.subset_closure ⟨hz, hz2⟩

theorem omega_ne_bot {Q : Subgroup D} (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) :
    quasithinOmegaOneCenter Q ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQ1
  have hnt := hQ.center_nontrivial
  obtain ⟨n, hn0, hn⟩ := ((hQ.to_subgroup (Subgroup.center Q)).nontrivial_iff_card).1 hnt
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 2
    (hn ▸ dvd_pow_self 2 hn0.ne')
  intro hbot
  have hc2 : c ^ 2 = 1 := by
    rw [← hc]
    exact pow_orderOf_eq_one c
  have hcZ : ((c : Q) : D) ∈ centerOf Q := by
    refine ⟨(c : Q).2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp c.2) ⟨g, hg⟩)
  have hcE : ((c : Q) : D) ∈ quasithinOmegaOneCenter Q :=
    mem_omega hcZ (congrArg (fun w : Subgroup.center Q => ((w : Q) : D)) hc2)
  rw [hbot, Subgroup.mem_bot] at hcE
  have hc1 : c = 1 := Subtype.ext (Subtype.ext hcE)
  rw [hc1, orderOf_one] at hc
  exact absurd hc (by norm_num)

namespace GoldHyp

omit [Finite D] in
theorem symm (h : GoldHyp G₁ G₂) : GoldHyp G₂ G₁ where
  amalgam := h.amalgam.symm
  charTwo₁ := h.charTwo₂
  charTwo₂ := h.charTwo₁

omit [Finite D] in
theorem isSylowTwoOf_left (h : GoldHyp G₁ G₂) : IsSylowTwoOf (G₁ ⊓ G₂) G₁ :=
  h.amalgam.sylow₁

omit [Finite D] in
theorem isSylowTwoOf_right (h : GoldHyp G₁ G₂) : IsSylowTwoOf (G₁ ⊓ G₂) G₂ := by
  have := h.symm.isSylowTwoOf_left
  rwa [inf_comm] at this

omit [Finite D] in
theorem amalgamHyp (h : GoldHyp G₁ G₂) : AmalgamHyp (G₁ ⊔ G₂) G₁ G₂ (G₁ ⊓ G₂) where
  gen := rfl
  charTwo := h.charTwo₁
  sylow₁ := h.isSylowTwoOf_left
  sylow₂ := h.isSylowTwoOf_right
  o2_trivial := by
    rw [h.amalgam.gen, pCoreOf_top_eq, h.amalgam.pCore_eq_bot]

theorem relIndex_left (h : GoldHyp G₁ G₂) : (G₁ ⊓ G₂).relIndex G₁ = 3 :=
  h.amalgam.toIsGoldschmidtVTriple.relIndex_inf_left

theorem relIndex_right (h : GoldHyp G₁ G₂) : (G₁ ⊓ G₂).relIndex G₂ = 3 :=
  h.amalgam.toIsGoldschmidtVTriple.relIndex_inf_right

theorem pCoreOf_left_le (h : GoldHyp G₁ G₂) : pCoreOf 2 G₁ ≤ G₁ ⊓ G₂ :=
  isSylowTwoOf_pCoreOf_le h.isSylowTwoOf_left

theorem pCoreOf_right_le (h : GoldHyp G₁ G₂) : pCoreOf 2 G₂ ≤ G₁ ⊓ G₂ :=
  isSylowTwoOf_pCoreOf_le h.isSylowTwoOf_right

omit [Finite D] in
theorem relIndex_pCoreOf_left (h : GoldHyp G₁ G₂) : (pCoreOf 2 G₁).relIndex G₁ = 6 :=
  F112W.relIndex_pCoreOf_eq_six h.amalgam.quotient₁

omit [Finite D] in
theorem relIndex_pCoreOf_right (h : GoldHyp G₁ G₂) : (pCoreOf 2 G₂).relIndex G₂ = 6 :=
  F112W.relIndex_pCoreOf_eq_six h.amalgam.quotient₂

theorem relIndex_pCoreOf_T_left (h : GoldHyp G₁ G₂) : (pCoreOf 2 G₁).relIndex (G₁ ⊓ G₂) = 2 := by
  have h1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 G₁) (G₁ ⊓ G₂) G₁ h.pCoreOf_left_le
    inf_le_left
  rw [h.relIndex_pCoreOf_left, h.relIndex_left] at h1
  omega

theorem relIndex_pCoreOf_T_right (h : GoldHyp G₁ G₂) : (pCoreOf 2 G₂).relIndex (G₁ ⊓ G₂) = 2 := by
  have h1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 G₂) (G₁ ⊓ G₂) G₂ h.pCoreOf_right_le
    inf_le_right
  rw [h.relIndex_pCoreOf_right, h.relIndex_right] at h1
  omega

omit [Finite D] in
theorem T_le_normalizer_left (_h : GoldHyp G₁ G₂) :
    G₁ ⊓ G₂ ≤ Subgroup.normalizer (pCoreOf 2 G₁ : Set D) :=
  inf_le_left.trans (le_normalizer_pCoreOf 2 G₁)

omit [Finite D] in
theorem T_le_normalizer_right (_h : GoldHyp G₁ G₂) :
    G₁ ⊓ G₂ ≤ Subgroup.normalizer (pCoreOf 2 G₂ : Set D) :=
  inf_le_right.trans (le_normalizer_pCoreOf 2 G₂)

theorem pCoreOf_ne (h : GoldHyp G₁ G₂) (hT : Nat.card ↥(G₁ ⊓ G₂) ≠ 2) :
    pCoreOf 2 G₁ ≠ pCoreOf 2 G₂ := by
  intro heq
  have hN : (G₁ ⊔ G₂) ≤ Subgroup.normalizer (pCoreOf 2 G₁ : Set D) := by
    refine sup_le (le_normalizer_pCoreOf 2 G₁) ?_
    rw [heq]
    exact le_normalizer_pCoreOf 2 G₂
  have hNormal : (pCoreOf 2 G₁).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (pCoreOf 2 G₁ : Set D) :=
      hN (h.amalgam.gen ▸ Subgroup.mem_top g)
    exact (Subgroup.mem_normalizer_iff.1 hg n).1 hn
  have hle : pCoreOf 2 G₁ ≤ CFSG.Open.pCore 2 D :=
    h.amalgam.toIsGoldschmidtVTriple.le_pCore_of_normal_le_inf h.pCoreOf_left_le
  rw [h.amalgam.pCore_eq_bot, le_bot_iff] at hle
  have h2 := h.relIndex_pCoreOf_T_left
  rw [hle, Subgroup.relIndex_bot_left] at h2
  exact hT h2

theorem pCoreOf_sup_eq (h : GoldHyp G₁ G₂) (hne : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂) :
    pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂ = G₁ ⊓ G₂ := by
  have hle : pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂ ≤ G₁ ⊓ G₂ :=
    sup_le h.pCoreOf_left_le h.pCoreOf_right_le
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 G₁) (pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂)
    (G₁ ⊓ G₂) le_sup_left hle
  rw [h.relIndex_pCoreOf_T_left] at hmul
  have hdvd : (pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂).relIndex (G₁ ⊓ G₂) ∣ 2 := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h1)
  · exfalso
    rw [h2] at hmul
    have h3 : (pCoreOf 2 G₁).relIndex (pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂) = 1 := by omega
    have h4 : pCoreOf 2 G₂ ≤ pCoreOf 2 G₁ := le_sup_right.trans (Subgroup.relIndex_eq_one.mp h3)
    have h5 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 G₂) (pCoreOf 2 G₁) (G₁ ⊓ G₂) h4
      h.pCoreOf_left_le
    rw [h.relIndex_pCoreOf_T_left, h.relIndex_pCoreOf_T_right] at h5
    have h6 : (pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) = 1 := by omega
    exact hne (le_antisymm (Subgroup.relIndex_eq_one.mp h6) h4)

theorem relIndex_inf_pCoreOf (h : GoldHyp G₁ G₂) (hne : pCoreOf 2 G₁ ≠ pCoreOf 2 G₂) :
    (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).relIndex (G₁ ⊓ G₂) = 4 := by
  have hN : pCoreOf 2 G₁ ≤ Subgroup.normalizer (pCoreOf 2 G₂ : Set D) :=
    h.pCoreOf_left_le.trans h.T_le_normalizer_right
  have h1 := F1.relIndex_sup_eq_of_le_normalizer hN
  rw [h.pCoreOf_sup_eq hne, h.relIndex_pCoreOf_T_right] at h1
  have h2 : (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) = 2 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact h1.symm
  have h3 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) (pCoreOf 2 G₁)
    (G₁ ⊓ G₂) inf_le_left h.pCoreOf_left_le
  rw [h2, h.relIndex_pCoreOf_T_left] at h3
  omega

theorem centerOf_le_pCoreOf_left (h : GoldHyp G₁ G₂) : centerOf (G₁ ⊓ G₂) ≤ pCoreOf 2 G₁ := by
  intro z hz
  refine h.charTwo₁ ⟨hz.1.1, ?_⟩
  exact Subgroup.centralizer_le h.pCoreOf_left_le hz.2

theorem centerOf_le_pCoreOf_right (h : GoldHyp G₁ G₂) : centerOf (G₁ ⊓ G₂) ≤ pCoreOf 2 G₂ := by
  have := h.symm.centerOf_le_pCoreOf_left
  rwa [inf_comm] at this

theorem omega_ne_bot_T (h : GoldHyp G₁ G₂) (hT : G₁ ⊓ G₂ ≠ ⊥) :
    quasithinOmegaOneCenter (G₁ ⊓ G₂) ≠ ⊥ :=
  omega_ne_bot h.amalgam.toIsGoldschmidtVTriple.isPGroup_inf hT

theorem not_normalizes_both (h : GoldHyp G₁ G₂) (hT : G₁ ⊓ G₂ ≠ ⊥) :
    ¬ (G₁ ≤ Subgroup.normalizer (quasithinOmegaOneCenter (G₁ ⊓ G₂) : Set D) ∧
      G₂ ≤ Subgroup.normalizer (quasithinOmegaOneCenter (G₁ ⊓ G₂) : Set D)) := by
  rintro ⟨h1, h2⟩
  have hNormal : (quasithinOmegaOneCenter (G₁ ⊓ G₂)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (quasithinOmegaOneCenter (G₁ ⊓ G₂) : Set D) :=
      (sup_le h1 h2) (h.amalgam.gen ▸ Subgroup.mem_top g)
    exact (Subgroup.mem_normalizer_iff.1 hg n).1 hn
  have hle : quasithinOmegaOneCenter (G₁ ⊓ G₂) ≤ CFSG.Open.pCore 2 D :=
    h.amalgam.toIsGoldschmidtVTriple.le_pCore_of_normal_le_inf
      ((omega_le_centerOf _).trans (fun x hx => hx.1))
  rw [h.amalgam.pCore_eq_bot, le_bot_iff] at hle
  exact h.omega_ne_bot_T hT hle

end GoldHyp

end GoldAmL

end F6

end CFSG.Quasithin

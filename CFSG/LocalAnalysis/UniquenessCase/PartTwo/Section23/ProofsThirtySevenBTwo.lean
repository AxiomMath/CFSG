module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InnerCartanCommute
public import CFSG.LocalAnalysis.UniquenessCase.UC6Pgrp
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
public import CFSG.GroupTheory.ConjCommuteModCoprime
public import CFSG.LinearAlgebra.SL2LineStabilizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyNineAbFinal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsThirtySeven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.PartTwo
open Subgroup Matrix
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

structure B2Data (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) where
  hV : IsElemAbelian 2 c.V
  hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)
  κ : Coordinates c.L c.V hV hLV (CFSG.Open.pRank 2 D.Z)
  hker : CFSG.pCore 2 ↥c.L ≤ κ.α.ker
  hker_eq : κ.α.ker = (c.L ⊓ Subgroup.centralizer (c.V : Set G)).subgroupOf c.L
  z₀ : ↥D.Z
  hz₀1 : z₀ ≠ 1

namespace B2Data

variable {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch} (X : B2Data D Ch c)

@[expose] noncomputable def e : Fin 2 → X.κ.K :=
  Multiplicative.toAdd (X.κ.β ⟨X.z₀, uc22p22v_le_conjClosure c.N D.Z X.z₀.2⟩)

@[expose] noncomputable def eOf (z : ↥D.Z) : Fin 2 → X.κ.K :=
  Multiplicative.toAdd (X.κ.β ⟨z, uc22p22v_le_conjClosure c.N D.Z z.2⟩)

@[expose] noncomputable def P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) X.κ.K) :=
  ((D.T ⊓ c.L).subgroupOf c.L).map X.κ.α

theorem e_eq_eOf : X.e = X.eOf X.z₀ := by
  simp only [e, eOf]

theorem e_ne_zero : X.e ≠ 0 := by
  intro h
  have h1 : X.κ.β ⟨X.z₀, _⟩ = 1 := Multiplicative.toAdd.injective (by simpa [e] using h)
  have h2 : (⟨X.z₀, _⟩ : ↥c.V) = 1 := X.κ.β_bij.1 (by simpa using h1)
  exact X.hz₀1 (Subtype.ext (by simpa using congrArg Subtype.val h2))

theorem P_mulVec_eOf (z : ↥D.Z) :
    ∀ x ∈ X.P, (x : Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ X.eOf z = X.eOf z := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
  have hlT : (l : G) ∈ D.T := (Subgroup.mem_subgroupOf.mp hl).1
  have hzV : (z : G) ∈ c.V := uc22p22v_le_conjClosure c.N D.Z z.2
  have hcomm : Commute (l : G) (z : G) :=
    (Subgroup.mem_centralizer_iff.mp
      (uc22main1_T_le_centralizer D hlT) (z : G) z.2).symm
  have hconj : CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV X.hLV l ⟨z, hzV⟩ =
      ⟨z, hzV⟩ := by
    apply Subtype.ext
    exact hcomm.mul_inv_cancel
  have h := congrArg Multiplicative.toAdd (X.κ.β_act l ⟨z, hzV⟩)
  rw [hconj] at h
  simpa [eOf] using h.symm

theorem P_eq_lineStabilizer (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) :
    X.P = CFSG.LinearAlgebra.lineStabilizer X.e := by
  refine CFSG.LinearAlgebra.lineStabilizer_eq_of_le ?_ X.e_ne_zero ?_
  · intro x hx
    rw [X.e_eq_eOf, CFSG.LinearAlgebra.mem_lineStabilizer]
    exact X.P_mulVec_eOf X.z₀ x hx
  · rw [show X.P = ((D.T ⊓ c.L).subgroupOf c.L).map X.κ.α from rfl,
      card_map_alpha_T_inf_L D Ch h4 h23 h1930 c X.hV X.hLV X.κ]

theorem P_ne_bot (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) : X.P ≠ ⊥ := by
  intro hbot
  have hcardP : Nat.card X.P = Nat.card X.κ.K := by
    rw [show X.P = ((D.T ⊓ c.L).subgroupOf c.L).map X.κ.α from rfl,
      card_map_alpha_T_inf_L D Ch h4 h23 h1930 c X.hV X.hLV X.κ]
  have hKcard : Nat.card X.κ.K = 2 ^ CFSG.Open.pRank 2 D.Z := X.κ.cardK
  have hpRank : 1 ≤ CFSG.Open.pRank 2 D.Z :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.one_le_pRank_of_ne_bot Nat.prime_two
      (D.sylowM.isPGroup.to_le (uc22main1_Z_le_T D)) (uc22main1_Z_ne_bot D)
  have h2 : 2 ≤ Nat.card X.κ.K := by
    rw [hKcard]
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ CFSG.Open.pRank 2 D.Z := Nat.pow_le_pow_right (by norm_num) hpRank
  have h1 : Nat.card X.P = 1 := by rw [hbot, Subgroup.card_bot]
  omega

theorem P_conj_mem_of_inducedBar
    {a : G} (haT : a ∈ Subgroup.normalizer (D.T : Set G))
    (haL : a ∈ Subgroup.normalizer (c.L : Set G))
    {ℓ : Bar2 c.L} {l₀ : ↥c.L} (hl₀ : QuotientGroup.mk l₀ = ℓ)
    (hθ : InducedBar c.L a (MulAut.conj ℓ)) :
    ∀ x ∈ X.P, X.κ.α l₀ * x * (X.κ.α l₀)⁻¹ ∈ X.P := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
  have hlT : (l : G) ∈ D.T := (Subgroup.mem_subgroupOf.mp hl).1
  have hlL : (l : G) ∈ c.L := l.2
  have haT' : a * (l : G) * a⁻¹ ∈ D.T :=
    (Subgroup.mem_normalizer_iff.mp haT (l : G)).1 hlT
  have haL' : a * (l : G) * a⁻¹ ∈ c.L :=
    (Subgroup.mem_normalizer_iff.mp haL (l : G)).1 hlL
  refine Subgroup.mem_map.mpr ⟨⟨a * (l : G) * a⁻¹, haL'⟩, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr ⟨haT', haL'⟩
  · exact Ctx23L.alpha_conj_of_inducedBar D Ch c X.hker haL hl₀ hθ l

theorem P_mem_normalizer_of_inducedBar
    {a : G} (haT : a ∈ Subgroup.normalizer (D.T : Set G))
    (haL : a ∈ Subgroup.normalizer (c.L : Set G))
    {ℓ : Bar2 c.L} {l₀ : ↥c.L} (hl₀ : QuotientGroup.mk l₀ = ℓ)
    (hθ : InducedBar c.L a (MulAut.conj ℓ)) :
    X.κ.α l₀ ∈ Subgroup.normalizer (X.P : Set (Matrix.SpecialLinearGroup (Fin 2) X.κ.K)) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  constructor
  · intro hx
    have hθinv : InducedBar c.L a⁻¹ (MulAut.conj ℓ⁻¹) := by
      have h := inducedBar_inv haL hθ
      rwa [show (MulAut.conj ℓ)⁻¹ = MulAut.conj ℓ⁻¹ from (map_inv MulAut.conj ℓ).symm] at h
    have hl₀inv : QuotientGroup.mk l₀⁻¹ = ℓ⁻¹ := by rw [QuotientGroup.mk_inv, hl₀]
    have h := X.P_conj_mem_of_inducedBar (Subgroup.inv_mem _ haT)
      (Subgroup.inv_mem _ haL) hl₀inv hθinv x hx
    simpa using h
  · intro hx
    have h := X.P_conj_mem_of_inducedBar haT haL hl₀ hθ
      ((X.κ.α l₀)⁻¹ * x * X.κ.α l₀) hx
    have hx' : X.κ.α l₀ * ((X.κ.α l₀)⁻¹ * x * X.κ.α l₀) * (X.κ.α l₀)⁻¹ = x := by
      group
    rwa [hx'] at h

theorem mulVec_e_of_mem_B0 (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    {b : G} (hb : b ∈ c.B0) :
    ∃ cb : X.κ.K,
      (X.κ.α ⟨b, c.hB0.1.trans c.hL0L hb⟩ :
        Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ X.e = cb • X.e := by
  have hbL : b ∈ c.L := c.hB0.1.trans c.hL0L hb
  have hbM : b ∈ D.M := c.hBM hb
  obtain ⟨hUZ, -, hMN⟩ := h4 h1930 c
  have hMNZ : D.M ≤ Subgroup.normalizer (D.Z : Set G) := hUZ ▸ hMN
  have hbz : b * (X.z₀ : G) * b⁻¹ ∈ D.Z :=
    (Subgroup.mem_normalizer_iff.mp (hMNZ hbM) (X.z₀ : G)).1 X.z₀.2
  let z₁ : ↥D.Z := ⟨b * (X.z₀ : G) * b⁻¹, hbz⟩
  have hz₁V : (z₁ : G) ∈ c.V := uc22p22v_le_conjClosure c.N D.Z z₁.2
  have hz₀V : (X.z₀ : G) ∈ c.V := uc22p22v_le_conjClosure c.N D.Z X.z₀.2
  have hconj : CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV X.hLV ⟨b, hbL⟩
      ⟨X.z₀, hz₀V⟩ = ⟨z₁, hz₁V⟩ := Subtype.ext rfl
  have h' : Multiplicative.toAdd (X.κ.β ⟨z₁, hz₁V⟩) =
      (X.κ.α ⟨b, hbL⟩ : Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ
        Multiplicative.toAdd (X.κ.β ⟨X.z₀, hz₀V⟩) := by
    have h0 := congrArg Multiplicative.toAdd (X.κ.β_act ⟨b, hbL⟩ ⟨X.z₀, hz₀V⟩)
    rw [hconj] at h0
    simpa using h0
  have h : X.eOf z₁ =
      (X.κ.α ⟨b, hbL⟩ : Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ X.e := by
    change Multiplicative.toAdd (X.κ.β ⟨z₁, hz₁V⟩) =
      (X.κ.α ⟨b, hbL⟩ : Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ
        Multiplicative.toAdd (X.κ.β ⟨X.z₀, hz₀V⟩)
    exact h'
  have hfix : ∀ x ∈ X.P,
      (x : Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ X.eOf z₁ = X.eOf z₁ :=
    X.P_mulVec_eOf z₁
  have hPle : X.P ≤ CFSG.LinearAlgebra.lineStabilizer X.e := by
    rw [X.P_eq_lineStabilizer h4 h23 h1930]
  obtain ⟨cb, hcb⟩ := CFSG.LinearAlgebra.exists_eq_smul_of_forall_mulVec_eq_self
    hPle (X.P_ne_bot h4 h23 h1930) X.e_ne_zero hfix
  exact ⟨cb, h.symm.trans hcb⟩

end B2Data

theorem odd_card_B0 {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) :
    Odd (Nat.card ↥c.B0) :=
  uc22p22f_odd_card_B ({ c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl } : Ctx21 D Ch)

private theorem pCore_coprime_zpowers {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {a₁ : G} (hodd : Odd (orderOf a₁)) :
    Nat.Coprime (Nat.card ↥(CFSG.Open.pCoreOf 2 c.L))
      (Nat.card (Subgroup.zpowers a₁)) := by
  obtain ⟨n, hn⟩ := (uc22main1_isPGroup_pCoreOf c.L).exists_card_eq
  rw [hn, Nat.card_zpowers]
  exact (Nat.coprime_two_left.mpr hodd).pow_left n

private theorem pCore_coprime_B0 {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) :
    Nat.Coprime (Nat.card ↥(CFSG.Open.pCoreOf 2 c.L)) (Nat.card ↥c.B0) := by
  obtain ⟨n, hn⟩ := (uc22main1_isPGroup_pCoreOf c.L).exists_card_eq
  rw [hn]
  exact (Nat.coprime_two_left.mpr (odd_card_B0 c)).pow_left n

end Ctx23L

theorem IsInnerCartanOnL.map_conj_le_inf {A K L T M : Subgroup G} {m : ℕ} {g : G}
    (hA : IsInnerCartanOnL A K L T m)
    (hKleM : K ≤ M) (hKn : (K.subgroupOf M).Normal) (hgM : g ∈ M) (hgT : g ∈ T) :
    A.map (MulAut.conj g).toMonoidHom ≤ K ⊓ Subgroup.normalizer (T : Set G) := by
  have hgK : g ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKleM).mp hKn hgM
  have hgTN : g ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer hgT
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hgK a).1 (hA.1 ha).1
  · change (g * a * g⁻¹) ∈ Subgroup.normalizer (T : Set G)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgTN (hA.1 ha).2) (Subgroup.inv_mem _ hgTN)

theorem IsInnerCartanOnL.odd_two_pow_sub_one {A K L T : Subgroup G} {m : ℕ}
    (hA : IsInnerCartanOnL A K L T m) : Odd (2 ^ m - 1) := by
  have hcard : Nat.card A = 2 ^ m - 1 := hA.2.2.1
  have hne : 2 ^ m - 1 ≠ 0 := by rw [← hcard]; exact Nat.card_pos.ne'
  have hm : m ≠ 0 := by
    intro hm0
    rw [hm0, pow_zero] at hne
    exact hne rfl
  have hEven : Even (2 ^ m) := Nat.even_pow.mpr ⟨even_two, hm⟩
  exact Nat.Even.sub_odd Nat.one_le_two_pow hEven odd_one

theorem IsInnerCartanOnL.pow_card_sub_one_eq_one {A K L T : Subgroup G} {m : ℕ}
    (hA : IsInnerCartanOnL A K L T m) {a : G} (ha : a ∈ A) :
    a ^ (2 ^ m - 1) = 1 := by
  have h := pow_card_eq_one' (G := ↥A) (x := ⟨a, ha⟩)
  have h' := congrArg (fun x : ↥A => (x : G)) h
  simpa [hA.2.2.1] using h'

private theorem IsInnerCartanOnL.odd_orderOf_conj {A K L T : Subgroup G} {m : ℕ}
    (hA : IsInnerCartanOnL A K L T m) {a : G} (ha : a ∈ A) (g : G) :
    Odd (orderOf (g * a * g⁻¹)) := by
  have hoddA : Odd (orderOf a) := by
    refine Odd.of_dvd_nat (IsInnerCartanOnL.odd_two_pow_sub_one hA) ?_
    rw [← hA.2.2.1]
    exact Subgroup.orderOf_dvd_natCard A ha
  have hconj : IsConj a (g * a * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  exact (IsConj.orderOf_eq hconj).symm ▸ hoddA

theorem IsInnerCartanOnL.map_conj {A K L T M : Subgroup G} {m : ℕ} {g : G}
    (hA : IsInnerCartanOnL A K L T m)
    (hKleM : K ≤ M) (hKn : (K.subgroupOf M).Normal) (hgM : g ∈ M)
    (hgT : g ∈ T) (hgL : g ∈ L) :
    IsInnerCartanOnL (A.map (MulAut.conj g).toMonoidHom) K L T m := by
  have hgLN : g ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hgL
  refine ⟨IsInnerCartanOnL.map_conj_le_inf hA hKleM hKn hgM hgT, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a₀, ha₀gen⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top A).mp hA.2.1
    rw [← ha₀gen, MonoidHom.map_zpowers]
    exact Subgroup.isCyclic_zpowers _
  · rw [Subgroup.card_map_of_injective (K := A) (f := (MulAut.conj g).toMonoidHom)
      (by simpa only [MulEquiv.coe_toMonoidHom] using (MulAut.conj g).injective)]
    exact hA.2.2.1
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgLN (hA.2.2.2.1 ha))
      (Subgroup.inv_mem _ hgLN)
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨ℓ, hℓ⟩ := hA.2.2.2.2.1 a ha
    exact ⟨(QuotientGroup.mk ⟨g, hgL⟩ : Bar2 L) * ℓ *
      (QuotientGroup.mk ⟨g, hgL⟩ : Bar2 L)⁻¹,
      inducedBar_conj hgL (hA.2.2.2.1 ha) hℓ⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    intro h
    have h' : InducedBar L a 1 := inducedBar_one_of_conj_mem hgL (hA.2.2.2.1 ha) h
    have h1 : a = 1 := hA.2.2.2.2.2 a ha h'
    rw [h1]
    exact map_one _

namespace Ctx23L

namespace B2Data

variable {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch} (X : B2Data D Ch c)

theorem orderOf_alpha_lift_dvd {K A₀ : Subgroup G} {m : ℕ}
    (hA₀ : IsInnerCartanOnL A₀ K c.L D.T m)
    {a₀ : G} (ha₀ : a₀ ∈ A₀)
    {ℓ₀ : Bar2 c.L} {l₀ : ↥c.L} (hl₀ : QuotientGroup.mk l₀ = ℓ₀)
    (hθ₀ : InducedBar c.L a₀ (MulAut.conj ℓ₀)) :
    orderOf (X.κ.α l₀) ∣ 2 ^ m - 1 := by
  have ha₀L : a₀ ∈ Subgroup.normalizer (c.L : Set G) := hA₀.2.2.2.1 ha₀
  have hpow := IsInnerCartanOnL.pow_card_sub_one_eq_one hA₀ ha₀
  have haut := inducedBar_conj_pow_eq_one ha₀L hθ₀ hpow
  have hconj : MulAut.conj (ℓ₀ ^ (2 ^ m - 1)) = 1 := by
    rw [map_pow, haut]
  have hcentral : ∀ y : Bar2 c.L,
      (ℓ₀ ^ (2 ^ m - 1)) * y = y * (ℓ₀ ^ (2 ^ m - 1)) := by
    intro y
    have h := congrArg (fun f : MulAut (Bar2 c.L) => f y) hconj
    rw [MulAut.conj_apply] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  let θ : Bar2 c.L →* Matrix.SpecialLinearGroup (Fin 2) X.κ.K :=
    QuotientGroup.lift (CFSG.pCore 2 ↥c.L) X.κ.α X.hker
  have hθmk : ∀ l : ↥c.L, θ (QuotientGroup.mk l) = X.κ.α l := fun l =>
    QuotientGroup.lift_mk _ _ _
  have hθsurj : Function.Surjective θ :=
    QuotientGroup.lift_surjective_of_surjective _ _ X.κ.α_surj X.hker
  have hcenter : θ (ℓ₀ ^ (2 ^ m - 1)) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) X.κ.K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨q, rfl⟩ := hθsurj y
    rw [← map_mul, ← map_mul]
    exact congrArg θ (hcentral q).symm
  have hθz : θ (ℓ₀ ^ (2 ^ m - 1)) = 1 := by
    rw [CFSG.Walter.sl2_center_eq_bot_of_charTwo] at hcenter
    exact Subgroup.mem_bot.mp hcenter
  have hpowα : (X.κ.α l₀) ^ (2 ^ m - 1) = 1 := by
    have h : θ (QuotientGroup.mk (l₀ ^ (2 ^ m - 1))) = 1 := by
      rw [show (QuotientGroup.mk (l₀ ^ (2 ^ m - 1)) : Bar2 c.L) =
          (QuotientGroup.mk l₀) ^ (2 ^ m - 1) from by
        simpa using map_pow (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)) l₀ (2 ^ m - 1),
        hl₀]
      exact hθz
    rwa [hθmk, map_pow] at h
  exact orderOf_dvd_of_pow_eq_one hpowα

theorem P_mem_normalizer_of_mulVec_eq_smul (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) {h : Matrix.SpecialLinearGroup (Fin 2) X.κ.K} {c : X.κ.K}
    (hc : c ≠ 0) (hh : (h : Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ X.e = c • X.e) :
    h ∈ Subgroup.normalizer (X.P : Set (Matrix.SpecialLinearGroup (Fin 2) X.κ.K)) := by
  rw [X.P_eq_lineStabilizer h4 h23 h1930]
  exact CFSG.LinearAlgebra.mem_normalizer_lineStabilizer_of_mulVec_eq_smul hc hh

theorem commutator_mem_P_of_mem_zpowers (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) {h : Matrix.SpecialLinearGroup (Fin 2) X.κ.K} {d : X.κ.K}
    (hd : d ≠ 0) (hh : (h : Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ X.e = d • X.e)
    {x : Matrix.SpecialLinearGroup (Fin 2) X.κ.K} (hx : x ∈ Subgroup.zpowers h)
    {b : G} (hb : b ∈ c.B0) :
    x * X.κ.α ⟨b, c.hB0.1.trans c.hL0L hb⟩ * x⁻¹ *
      (X.κ.α ⟨b, c.hB0.1.trans c.hL0L hb⟩)⁻¹ ∈ X.P := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨cb, hcb⟩ := X.mulVec_e_of_mem_B0 h4 h23 h1930 hb
  have hxvec : ((h ^ m : Matrix.SpecialLinearGroup (Fin 2) X.κ.K) :
      Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ X.e = d ^ m • X.e :=
    CFSG.LinearAlgebra.zpow_mulVec_eq_zpow_smul_of_mulVec_eq_smul hd hh m
  rw [X.P_eq_lineStabilizer h4 h23 h1930]
  exact CFSG.LinearAlgebra.mem_lineStabilizer.mpr
    (CFSG.LinearAlgebra.commutator_mulVec_eq_self_of_mulVec_eq_smul X.e_ne_zero hxvec hcb)

theorem alpha_conj_pow_mul {a₀ : G} (hL : a₀ ∈ Subgroup.normalizer (c.L : Set G))
    {ℓ₀ : Bar2 c.L} {l₀ : ↥c.L} (hl₀ : QuotientGroup.mk l₀ = ℓ₀)
    (hθ₀ : InducedBar c.L a₀ (MulAut.conj ℓ₀)) (t : ↥c.L) (k : ℕ)
    (bL : ↥c.L) (hb : bL ∈ c.B0.subgroupOf c.L)
    (hxL : (((t : G) * a₀ * (t : G)⁻¹) ^ k * (bL : G) *
      (((t : G) * a₀ * (t : G)⁻¹) ^ k)⁻¹) ∈ c.L) :
    X.κ.α ⟨((t : G) * a₀ * (t : G)⁻¹) ^ k * (bL : G) *
        (((t : G) * a₀ * (t : G)⁻¹) ^ k)⁻¹, hxL⟩ =
      (X.κ.α t * (X.κ.α l₀) ^ k * (X.κ.α t)⁻¹) * X.κ.α bL *
        (X.κ.α t * (X.κ.α l₀) ^ k * (X.κ.α t)⁻¹)⁻¹ := by
  have htN : (t : G) ∈ Subgroup.normalizer (c.L : Set G) := Subgroup.le_normalizer t.2
  have ha₁N : ((t : G) * a₀ * (t : G)⁻¹) ∈ Subgroup.normalizer (c.L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ htN hL) (Subgroup.inv_mem _ htN)
  have ha₁kN : (((t : G) * a₀ * (t : G)⁻¹) ^ k) ∈
      Subgroup.normalizer (c.L : Set G) := Subgroup.pow_mem _ ha₁N k
  have hlift : QuotientGroup.mk (t * l₀ ^ k * t⁻¹) =
      (QuotientGroup.mk t * ℓ₀ * (QuotientGroup.mk t)⁻¹) ^ k := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_pow, hl₀, ← conj_pow]
  have hind := inducedBar_conj_pow hL hθ₀ t k
  have hα := Ctx23L.alpha_conj_of_inducedBar D Ch c X.hker ha₁kN hlift hind bL
  simpa [map_mul, map_mul, map_pow, map_inv] using hα

theorem commutator_pow_mem_pCore (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    {K A₀ : Subgroup G} {m : ℕ} (hA₀ : IsInnerCartanOnL A₀ K c.L D.T m)
    {a₀ : G} (ha₀ : a₀ ∈ A₀)
    {ℓ₀ : Bar2 c.L} {l₀ : ↥c.L} (hl₀ : QuotientGroup.mk l₀ = ℓ₀)
    (hθ₀ : InducedBar c.L a₀ (MulAut.conj ℓ₀)) {t : ↥c.L}
    (hcomm : ∀ b : ↥c.L, b ∈ c.B0.subgroupOf c.L →
      (X.κ.α t * X.κ.α l₀ * (X.κ.α t)⁻¹) * X.κ.α b =
      X.κ.α b * (X.κ.α t * X.κ.α l₀ * (X.κ.α t)⁻¹))
    (k : ℕ) {b : G} (hb : b ∈ c.B0) :
    ((t : G) * a₀ * (t : G)⁻¹) ^ k * b * (((t : G) * a₀ * (t : G)⁻¹) ^ k)⁻¹ * b⁻¹ ∈
      CFSG.Open.pCoreOf 2 c.L := by
  have hL : a₀ ∈ Subgroup.normalizer (c.L : Set G) := hA₀.2.2.2.1 ha₀
  have hbL : b ∈ c.L := c.hB0.1.trans c.hL0L hb
  let bL : ↥c.L := ⟨b, hbL⟩
  have hbB0sub : bL ∈ c.B0.subgroupOf c.L := Subgroup.mem_subgroupOf.mpr hb
  let a₁ : G := (t : G) * a₀ * (t : G)⁻¹
  have ha₁N : a₁ ∈ Subgroup.normalizer (c.L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer t.2) hL)
      (Subgroup.inv_mem _ (Subgroup.le_normalizer t.2))
  have ha₁kN : a₁ ^ k ∈ Subgroup.normalizer (c.L : Set G) := Subgroup.pow_mem _ ha₁N k
  have hxL : a₁ ^ k * b * (a₁ ^ k)⁻¹ ∈ c.L :=
    (Subgroup.mem_normalizer_iff.mp ha₁kN b).1 hbL
  have hα' := X.alpha_conj_pow_mul hL hl₀ hθ₀ t k bL hbB0sub hxL
  have hα1 : X.κ.α ⟨a₁ ^ k * b * (a₁ ^ k)⁻¹ * b⁻¹,
      c.L.mul_mem hxL (c.L.inv_mem hbL)⟩ = 1 := by
    have hsplit : (⟨a₁ ^ k * b * (a₁ ^ k)⁻¹ * b⁻¹,
        c.L.mul_mem hxL (c.L.inv_mem hbL)⟩ : ↥c.L) =
        ⟨a₁ ^ k * b * (a₁ ^ k)⁻¹, hxL⟩ * bL⁻¹ := Subtype.ext rfl
    rw [hsplit, map_mul, hα', map_inv]
    have hc : Commute (X.κ.α t * X.κ.α l₀ * (X.κ.α t)⁻¹) (X.κ.α bL) :=
      hcomm bL hbB0sub
    have hc' : Commute ((X.κ.α t * X.κ.α l₀ * (X.κ.α t)⁻¹) ^ k) (X.κ.α bL) :=
      hc.pow_left k
    rw [← conj_pow, hc'.eq]
    group
  have hker : (⟨a₁ ^ k * b * (a₁ ^ k)⁻¹ * b⁻¹,
      c.L.mul_mem hxL (c.L.inv_mem hbL)⟩ : ↥c.L) ∈ X.κ.α.ker := by
    rw [MonoidHom.mem_ker]
    exact hα1
  rw [X.hker_eq] at hker
  exact Ctx23L.inf_centralizer_V_le_pCoreOf_L D Ch h4 h23 h1930 c
    (Subgroup.mem_subgroupOf.mp hker)

private theorem P_mem_normalizer_map_B0 (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) :
    ((c.B0.subgroupOf c.L).map X.κ.α) ≤
      Subgroup.normalizer (X.P : Set (Matrix.SpecialLinearGroup (Fin 2) X.κ.K)) := by
  intro y hy
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
  have hbB0 : (b : G) ∈ c.B0 := Subgroup.mem_subgroupOf.mp hb
  obtain ⟨cb, hcb⟩ := X.mulVec_e_of_mem_B0 h4 h23 h1930 hbB0
  have hcbne : cb ≠ 0 := CFSG.LinearAlgebra.ne_zero_of_mulVec_eq_smul X.e_ne_zero hcb
  simpa using X.P_mem_normalizer_of_mulVec_eq_smul h4 h23 h1930 hcbne hcb

private theorem P_card (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) :
    Nat.card X.P = 2 ^ CFSG.Open.pRank 2 D.Z := by
  rw [show X.P = ((D.T ⊓ c.L).subgroupOf c.L).map X.κ.α from rfl,
    card_map_alpha_T_inf_L D Ch h4 h23 h1930 c X.hV X.hLV X.κ]
  exact X.κ.cardK

private theorem P_coprime_zpowers (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    {h : Matrix.SpecialLinearGroup (Fin 2) X.κ.K} (hodd : Odd (orderOf h)) :
    Nat.Coprime (Nat.card X.P) (Nat.card (Subgroup.zpowers h)) := by
  rw [X.P_card h4 h23 h1930,
    show Nat.card (Subgroup.zpowers h) = orderOf h from Nat.card_zpowers h]
  exact (Nat.coprime_two_left.mpr hodd).pow_left _

private theorem P_coprime_map_B0 (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) :
    Nat.Coprime (Nat.card X.P) (Nat.card ↥((c.B0.subgroupOf c.L).map X.κ.α)) := by
  have hdvd : Nat.card ↥((c.B0.subgroupOf c.L).map X.κ.α) ∣
      Nat.card ↥(c.B0.subgroupOf c.L) := Subgroup.card_map_dvd _ _
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (c.hB0.1.trans c.hL0L)).toEquiv] at hdvd
  have hodd : Odd (Nat.card ↥((c.B0.subgroupOf c.L).map X.κ.α)) :=
    Odd.of_dvd_nat (Ctx23L.odd_card_B0 c) hdvd
  rw [X.P_card h4 h23 h1930]
  exact (Nat.coprime_two_left.mpr hodd).pow_left _

private theorem P_commutator_mem_zpowers_B0 (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) {h : Matrix.SpecialLinearGroup (Fin 2) X.κ.K} {d : X.κ.K}
    (hd : d ≠ 0) (hd_eq : (h : Matrix (Fin 2) (Fin 2) X.κ.K) *ᵥ X.e = d • X.e)
    (x : Matrix.SpecialLinearGroup (Fin 2) X.κ.K) (hx : x ∈ Subgroup.zpowers h)
    (y : Matrix.SpecialLinearGroup (Fin 2) X.κ.K)
    (hy : y ∈ (c.B0.subgroupOf c.L).map X.κ.α) :
    x * y * x⁻¹ * y⁻¹ ∈ X.P := by
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
  have hbB0 : (b : G) ∈ c.B0 := Subgroup.mem_subgroupOf.mp hb
  simpa using X.commutator_mem_P_of_mem_zpowers h4 h23 h1930 hd hd_eq hx hbB0

private theorem isMulCommutative_map_B0 :
    IsMulCommutative ↥((c.B0.subgroupOf c.L).map X.κ.α) := by
  haveI : IsMulCommutative ↥c.B0 := c.hB0.2.1
  haveI : IsMulCommutative ↥(c.B0.subgroupOf c.L) :=
    Subgroup.subgroupOf_isMulCommutative c.L c.B0
  exact Subgroup.map_isMulCommutative (c.B0.subgroupOf c.L) X.κ.α

private theorem exists_mem_T_inf_L_of_mem_P {l₀ : ↥c.L}
    {u : Matrix.SpecialLinearGroup (Fin 2) X.κ.K} (huP : u ∈ X.P)
    (hucomm : ∀ b : ↥c.L, b ∈ c.B0.subgroupOf c.L →
      (u * X.κ.α l₀ * u⁻¹) * X.κ.α b =
      X.κ.α b * (u * X.κ.α l₀ * u⁻¹)) :
    ∃ t : ↥c.L, (t : G) ∈ D.T ∧
      ∀ b : ↥c.L, b ∈ c.B0.subgroupOf c.L →
        (X.κ.α t * X.κ.α l₀ * (X.κ.α t)⁻¹) * X.κ.α b =
        X.κ.α b * (X.κ.α t * X.κ.α l₀ * (X.κ.α t)⁻¹) := by
  rw [show X.P = ((D.T ⊓ c.L).subgroupOf c.L).map X.κ.α from rfl] at huP
  obtain ⟨t, ht, htα⟩ := Subgroup.mem_map.mp huP
  refine ⟨t, (Subgroup.mem_subgroupOf.mp ht).1, ?_⟩
  intro b hb
  have h := hucomm b hb
  rw [← htα] at h
  exact h

theorem exists_mem_P_commute (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    {K A₀ : Subgroup G} {m : ℕ} (hA₀ : IsInnerCartanOnL A₀ K c.L D.T m)
    {a₀ : G} (ha₀ : a₀ ∈ A₀)
    {ℓ₀ : Bar2 c.L} {l₀ : ↥c.L} (hl₀ : QuotientGroup.mk l₀ = ℓ₀)
    (hθ₀ : InducedBar c.L a₀ (MulAut.conj ℓ₀)) :
    ∃ t : ↥c.L, (t : G) ∈ D.T ∧
      ∀ b : ↥c.L, b ∈ c.B0.subgroupOf c.L →
        (X.κ.α t * X.κ.α l₀ * (X.κ.α t)⁻¹) * X.κ.α b =
        X.κ.α b * (X.κ.α t * X.κ.α l₀ * (X.κ.α t)⁻¹) := by
  let h : Matrix.SpecialLinearGroup (Fin 2) X.κ.K := X.κ.α l₀
  have hhnorm : h ∈ Subgroup.normalizer (X.P : Set (Matrix.SpecialLinearGroup (Fin 2) X.κ.K)) :=
    X.P_mem_normalizer_of_inducedBar (hA₀.1 ha₀).2 (hA₀.2.2.2.1 ha₀) hl₀ hθ₀
  have hPle : X.P ≤ CFSG.LinearAlgebra.lineStabilizer X.e := by
    rw [X.P_eq_lineStabilizer h4 h23 h1930]
  obtain ⟨d, hd_eq⟩ := CFSG.LinearAlgebra.exists_mulVec_eq_smul_of_normalizes
    hPle (X.P_ne_bot h4 h23 h1930) X.e_ne_zero
    (fun x hx => (Subgroup.mem_normalizer_iff''.mp hhnorm x).mp hx)
  have hd : d ≠ 0 := CFSG.LinearAlgebra.ne_zero_of_mulVec_eq_smul X.e_ne_zero hd_eq
  let H₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) X.κ.K) := Subgroup.zpowers h
  let H₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) X.κ.K) :=
    (c.B0.subgroupOf c.L).map X.κ.α
  have hH1norm : H₁ ≤
      Subgroup.normalizer (X.P : Set (Matrix.SpecialLinearGroup (Fin 2) X.κ.K)) :=
    Subgroup.zpowers_le.mpr hhnorm
  have hH2norm : H₂ ≤
      Subgroup.normalizer (X.P : Set (Matrix.SpecialLinearGroup (Fin 2) X.κ.K)) :=
    X.P_mem_normalizer_map_B0 h4 h23 h1930
  have hoddh : Odd (orderOf h) :=
    Odd.of_dvd_nat (IsInnerCartanOnL.odd_two_pow_sub_one hA₀)
      (X.orderOf_alpha_lift_dvd hA₀ ha₀ hl₀ hθ₀)
  have hcop1 := X.P_coprime_zpowers h4 h23 h1930 hoddh
  have hcop2 := X.P_coprime_map_B0 h4 h23 h1930
  have hcommutator : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y * x⁻¹ * y⁻¹ ∈ X.P :=
    X.P_commutator_mem_zpowers_B0 h4 h23 h1930 hd hd_eq
  obtain ⟨u, huP, hucomm⟩ :=
    CFSG.GroupTheory.exists_conj_commute_of_commutator_mem
      (U := X.P) (H₁ := H₁) (H₂ := H₂)
      hH1norm hH2norm hcop1 hcop2
      (Subgroup.zpowers_isMulCommutative h) X.isMulCommutative_map_B0 hcommutator
  have hucomm' : ∀ b : ↥c.L, b ∈ c.B0.subgroupOf c.L →
      (u * X.κ.α l₀ * u⁻¹) * X.κ.α b =
      X.κ.α b * (u * X.κ.α l₀ * u⁻¹) := by
    intro b hb
    have hmem : X.κ.α b ∈ H₂ := Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    simpa [h] using hucomm h (Subgroup.mem_zpowers h) (X.κ.α b) hmem
  exact X.exists_mem_T_inf_L_of_mem_P huP hucomm'

private theorem commutator_mem_pCore_zpowers (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) {K A₀ : Subgroup G} {m : ℕ}
    (hA₀ : IsInnerCartanOnL A₀ K c.L D.T m) {a₀ : G} (ha₀ : a₀ ∈ A₀)
    {ℓ₀ : Bar2 c.L} {l₀ : ↥c.L} (hl₀ : QuotientGroup.mk l₀ = ℓ₀)
    (hθ₀ : InducedBar c.L a₀ (MulAut.conj ℓ₀)) {t : ↥c.L}
    (hcomm : ∀ b : ↥c.L, b ∈ c.B0.subgroupOf c.L →
      (X.κ.α t * X.κ.α l₀ * (X.κ.α t)⁻¹) * X.κ.α b =
      X.κ.α b * (X.κ.α t * X.κ.α l₀ * (X.κ.α t)⁻¹))
    {x : G} (hx : x ∈ Subgroup.zpowers ((t : G) * a₀ * (t : G)⁻¹))
    {y : G} (hy : y ∈ c.B0) :
    x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  let n' : ℕ := (k % (orderOf ((t : G) * a₀ * (t : G)⁻¹) : ℤ)).toNat
  have hk : ((t : G) * a₀ * (t : G)⁻¹) ^ k =
      ((t : G) * a₀ * (t : G)⁻¹) ^ n' := by
    rw [← zpow_mod_orderOf ((t : G) * a₀ * (t : G)⁻¹) k]
    have hnonneg : 0 ≤ k % (orderOf ((t : G) * a₀ * (t : G)⁻¹) : ℤ) :=
      Int.emod_nonneg k (by exact_mod_cast (orderOf_pos _).ne')
    rw [← Int.toNat_of_nonneg hnonneg, zpow_natCast]
  rw [hk]
  exact X.commutator_pow_mem_pCore h4 h23 h1930 hA₀ ha₀ hl₀ hθ₀ hcomm n' hy

theorem exists_pCore_conj_commute (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    {K A₀ : Subgroup G} {m : ℕ} (hA₀ : IsInnerCartanOnL A₀ K c.L D.T m)
    {a₀ : G} (ha₀ : a₀ ∈ A₀)
    {ℓ₀ : Bar2 c.L} {l₀ : ↥c.L} (hl₀ : QuotientGroup.mk l₀ = ℓ₀)
    (hθ₀ : InducedBar c.L a₀ (MulAut.conj ℓ₀)) {t : ↥c.L}
    (hcomm : ∀ b : ↥c.L, b ∈ c.B0.subgroupOf c.L →
      (X.κ.α t * X.κ.α l₀ * (X.κ.α t)⁻¹) * X.κ.α b =
      X.κ.α b * (X.κ.α t * X.κ.α l₀ * (X.κ.α t)⁻¹)) :
    ∃ u' ∈ CFSG.Open.pCoreOf 2 c.L,
      ∀ b ∈ c.B0,
        (u' * ((t : G) * a₀ * (t : G)⁻¹) * u'⁻¹) * b =
        b * (u' * ((t : G) * a₀ * (t : G)⁻¹) * u'⁻¹) := by
  let a₁ : G := (t : G) * a₀ * (t : G)⁻¹
  have hL : a₀ ∈ Subgroup.normalizer (c.L : Set G) := hA₀.2.2.2.1 ha₀
  have htN : (t : G) ∈ Subgroup.normalizer (c.L : Set G) := Subgroup.le_normalizer t.2
  have ha₁N : a₁ ∈ Subgroup.normalizer (c.L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ htN hL) (Subgroup.inv_mem _ htN)
  have hH1norm : Subgroup.zpowers a₁ ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G) :=
    Subgroup.zpowers_le.mpr
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L ha₁N)
  have hH2norm : c.B0 ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G) :=
    fun b hb => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.L
      (c.hB0.1.trans c.hL0L hb)
  have hodd_a₁ : Odd (orderOf a₁) := by
    simpa [a₁] using IsInnerCartanOnL.odd_orderOf_conj hA₀ ha₀ (t : G)
  have hcop1 := pCore_coprime_zpowers c hodd_a₁
  have hcop2 := pCore_coprime_B0 c
  have hH1ab : IsMulCommutative ↥(Subgroup.zpowers a₁) :=
    Subgroup.zpowers_isMulCommutative a₁
  have hH2ab : IsMulCommutative ↥c.B0 := c.hB0.2.1
  have hcommutator : ∀ x ∈ Subgroup.zpowers a₁, ∀ y ∈ c.B0,
      x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L := by
    intro x hx y hy
    simpa [a₁] using
      X.commutator_mem_pCore_zpowers h4 h23 h1930 hA₀ ha₀ hl₀ hθ₀ hcomm hx hy
  obtain ⟨u', hu'U, hu'comm⟩ :=
    CFSG.GroupTheory.exists_conj_commute_of_commutator_mem
      (U := CFSG.Open.pCoreOf 2 c.L) (H₁ := Subgroup.zpowers a₁) (H₂ := c.B0)
      hH1norm hH2norm hcop1 hcop2 hH1ab hH2ab hcommutator
  exact ⟨u', hu'U, fun b hb => hu'comm a₁ (Subgroup.mem_zpowers a₁) b hb⟩

end B2Data

end Ctx23L

private theorem commutator_map_conj_eq_bot {A B : Subgroup G} {g a : G}
    (hgen : Subgroup.zpowers a = A)
    (hcomm : ∀ b ∈ B, (g * a * g⁻¹) * b = b * (g * a * g⁻¹)) :
    ⁅A.map (MulAut.conj g).toMonoidHom, B⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rw [← hgen, MonoidHom.map_zpowers]
  exact Subgroup.zpowers_le.mpr
    (Subgroup.mem_centralizer_iff.mpr (fun b hb => (hcomm b hb).symm))

theorem s23_37_B2_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) :
    S23_37_B2 D Ch := by
  intro h1930 c K hK hKn m A₀ hA₀
  classical
  obtain ⟨hV, hLV, κ, hκker, -⟩ := Ctx23L.exists_coordinates_V D Ch h4 h23 h1930 c
  have hC2 : IsPGroup 2 ↥(c.L ⊓ Subgroup.centralizer (c.V : Set G)) :=
    (Ctx23L.isPGroup_sup_inf_centralizer_V D Ch h4 h23 h1930 c).to_le
      (inf_le_inf (le_sup_left : c.L ≤ c.L ⊔ D.T) le_rfl)
  have hker : CFSG.pCore 2 ↥c.L ≤ κ.α.ker := le_of_eq (κ.ker_α hC2).symm
  obtain ⟨z₀, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (uc22main1_Z_ne_bot D)
  let X : Ctx23L.B2Data D Ch c :=
    { hV := hV, hLV := hLV, κ := κ, hker := hker, hker_eq := hκker,
      z₀ := z₀, hz₀1 := hz₀1 }
  obtain ⟨a₀, ha₀gen⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top A₀).mp hA₀.2.1
  have ha₀ : a₀ ∈ A₀ := by rw [← ha₀gen]; exact Subgroup.mem_zpowers a₀
  obtain ⟨ℓ₀, hℓ₀⟩ := hA₀.2.2.2.2.1 a₀ ha₀
  obtain ⟨l₀, hl₀⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥c.L) ℓ₀
  have hl₀' : QuotientGroup.mk l₀ = ℓ₀ := by simpa using hl₀
  obtain ⟨t, htT, hcomm⟩ :=
    X.exists_mem_P_commute h4 h23 h1930 hA₀ ha₀ hl₀' hℓ₀
  obtain ⟨u', hu'U, hu'comm⟩ :=
    X.exists_pCore_conj_commute h4 h23 h1930 hA₀ ha₀ hl₀' hℓ₀ hcomm
  let g : G := u' * (t : G)
  have hu'T : u' ∈ D.T := Ctx23L.pCoreOf_L_le_T D Ch c hu'U
  have hu'L : u' ∈ c.L := (CFSG.LieType.BorelTits.pCoreOf_le 2 c.L) hu'U
  have hgT : g ∈ D.T := D.T.mul_mem hu'T htT
  have hgL : g ∈ c.L := c.L.mul_mem hu'L t.2
  have hga : g * a₀ * g⁻¹ = u' * ((t : G) * a₀ * (t : G)⁻¹) * u'⁻¹ := by
    simp only [g]
    group
  exact ⟨A₀.map (MulAut.conj g).toMonoidHom,
    IsInnerCartanOnL.map_conj hA₀ (CFSG.Open.IsSubnormal.le hK.1) hKn
      (D.sylowM.le hgT) hgT hgL,
    commutator_map_conj_eq_bot ha₀gen (by
      intro b hb
      rw [hga]
      exact hu'comm b hb)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

module

public import CFSG.Quasithin.H13.NQCoreP134X27Inputs
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieDescent

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

structure E9Cfg {A : Type} [Group A] (L P T : Subgroup A) : Prop where
  normal : L.Normal
  le : P ≤ L
  card : Nat.card P = 9
  exp : ∀ x ∈ P, x ^ 3 = 1
  sylow : IsSylowTwoOf T ⊤
  mul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s
  irred : ∀ U : Subgroup A, U ≤ P →
    T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer (U : Set A) → U = ⊥ ∨ U = P

@[expose] def NoE9Cfg (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L P T : Subgroup A), F ↥L → E9Cfg L P T → False

@[expose] def NoX27Simple (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L P T : Subgroup A), OddConfig 3 L P T → Nat.card P = 27 →
    F ↥L → False

section Descent

variable {A : Type} [Group A] [Finite A] {L P T : Subgroup A}

theorem OddConfig.zOf_le (h : OddConfig 3 L P T) (h27 : Nat.card P = 27)
    (hZ3 : Nat.card (Subgroup.center ↥L) = 3) : zOf L ≤ P := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrank : Open.pRank 3 (⊤ : Subgroup A) ≤ 2 :=
    (CFSG.SectionRank.isStronglyQuasithin_iff.1 h.hyp.sqt) 3 Nat.prime_three (by norm_num)
  have hZn : (zOf L).Normal := zOf_normal h.normal
  have hcZ : Nat.card (zOf L) = 3 := by rw [card_zOf, hZ3]
  by_contra hle
  have hinf : P ⊓ zOf L = ⊥ := by
    have h1 : Nat.card (P ⊓ zOf L : Subgroup A) ∣ 3 := hcZ ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      apply hle
      have e : P ⊓ zOf L = zOf L := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hcZ])
      rw [← e]
      exact inf_le_left
  exact false_of_normalizes' hrank h.exp (by rw [h27]; norm_num) (le_normalizer_of_normal hZn P)
    hinf (by rw [hcZ])

theorem OddConfig.descend_x27 (h : OddConfig 3 L P T) (h27 : Nat.card P = 27)
    (hZ3 : Nat.card (Subgroup.center ↥L) = 3) :
    ∃ (A' : Type) (_ : Group A') (_ : Finite A') (L' P' T' : Subgroup A'),
      E9Cfg L' P' T' ∧ Nonempty (↥L' ≃* (↥L ⧸ Subgroup.center ↥L)) := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn := h.normal
  have hZn : (zOf L).Normal := zOf_normal hLn
  have hZP : zOf L ≤ P := h.zOf_le h27 hZ3
  have hcZ : Nat.card (zOf L) = 3 := by rw [card_zOf, hZ3]
  set Z := zOf L with hZdef
  let π : A →* A ⧸ Z := QuotientGroup.mk' Z
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hπZ : ∀ x ∈ Z, π x = 1 := fun x hx => (QuotientGroup.eq_one_iff x).mpr hx
  have hker : (π.comp P.subtype).ker = Z.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (x : A)
  have hrange : (π.comp P.subtype).range = P.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have eP : ↥(P.map π) ≃* ↥P ⧸ Z.subgroupOf P :=
    (MulEquiv.subgroupCongr hrange).symm.trans ((QuotientGroup.quotientKerEquivRange _).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker))
  have hcardP : Nat.card (P.map π) = 9 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf P)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hcZ, h27] at h1
    rw [Nat.card_congr eP.toEquiv]
    omega
  have hcommZ : ⁅P, P⁆ ≤ Z := by
    have hc : IsMulCommutative ↥(P.map π) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hcardP]; norm_num)
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h1 : π a * π b = π b * π a :=
      congrArg Subtype.val (hc.is_comm.comm ⟨π a, a, ha, rfl⟩ ⟨π b, b, hb, rfl⟩)
    have h2 : π ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h1
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hmapN : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), π t ∈ T.map π ⊓
      Subgroup.normalizer ((P.map π : Subgroup (A ⧸ Z)) : Set (A ⧸ Z)) := by
    rintro t ⟨htT, htN⟩
    refine ⟨⟨t, htT, rfl⟩, Subgroup.mem_normalizer_fintype ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.mp htN x).mp hx, by simp⟩
  refine ⟨A ⧸ Z, inferInstance, inferInstance, L.map π, P.map π, T.map π, ?_, ?_⟩
  ·
    refine ⟨Subgroup.Normal.map hLn π hπs, Subgroup.map_mono h.le, hcardP, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, h.exp x hx, map_one]
    · exact isSylowTwoOf_top_of (h.sylow.2.1.map π) fun hd =>
        index_odd_of_isSylowTwoOf_top h.sylow (hd.trans (Subgroup.index_map_dvd T hπs))
    · rintro _ ⟨t, ht, rfl⟩ _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, s, hs, he⟩ := h.mul t ht x hx
      exact ⟨π y, ⟨y, hy, rfl⟩, π s, ⟨s, hs, rfl⟩, by rw [← map_mul, ← map_mul, he]⟩
    · intro U' hUP hN
      set U : Subgroup A := P ⊓ U'.comap π with hUdef
      have hcommU : ⁅P, P⁆ ≤ U := by
        refine le_inf (commutator_self_le P) fun x hx => ?_
        show π x ∈ U'
        rw [hπZ x (hcommZ hx)]
        exact U'.one_mem
      have hNU : T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer (U : Set A) := by
        intro t ht
        obtain ⟨htT, htN⟩ := ht
        have hπN := hN (hmapN t ⟨htT, htN⟩)
        refine Subgroup.mem_normalizer_fintype fun u hu => ?_
        refine ⟨(Subgroup.mem_normalizer_iff.mp htN u).mp hu.1, ?_⟩
        show π (t * u * t⁻¹) ∈ U'
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hπN (π u)).mp hu.2
      have hU' : U.map π = U' := by
        refine le_antisymm ?_ ?_
        · rintro _ ⟨u, hu, rfl⟩
          exact hu.2
        · intro y hy
          obtain ⟨x, hx, rfl⟩ := hUP hy
          exact ⟨x, ⟨hx, hy⟩, rfl⟩
      rcases h.irred U hcommU inf_le_left hNU with hU | hU
      · left
        rw [← hU', hU]
        refine eq_bot_iff.mpr ?_
        rintro _ ⟨x, hx, rfl⟩
        exact Subgroup.mem_bot.mpr (hπZ x (hcommZ hx))
      · right
        rw [← hU', hU]
  ·
    let φ : ↥L →* A ⧸ Z := π.comp L.subtype
    have hkerL : φ.ker = Subgroup.center ↥L := by
      ext x
      rw [MonoidHom.mem_ker]
      change π x = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_zOf]
      exact ⟨fun ⟨hx, hc⟩ => hc, fun hc => ⟨x.2, hc⟩⟩
    have hrangeL : φ.range = L.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact ⟨((MulEquiv.subgroupCongr hrangeL).symm.trans
      ((QuotientGroup.quotientKerEquivRange φ).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hkerL))).symm.symm⟩

theorem OddConfig.false_of_center_one {F : ∀ (X : Type) [Group X], Prop} (hiso : IsoInvariant F)
    (hS : NoX27Simple F) (h : OddConfig 3 L P T) (h27 : Nat.card P = 27)
    (hZ1 : Nat.card (Subgroup.center ↥L) = 1) (hF : F (↥L ⧸ Subgroup.center ↥L)) : False := by
  have hZ : Subgroup.center ↥L = ⊥ := Subgroup.card_eq_one.mp hZ1
  have e : ↥L ≃* ↥L ⧸ Subgroup.center ↥L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact hS A L P T h h27 (hiso _ _ e.symm hF)

end Descent

theorem noX27ConfigQ_of_noE9Cfg {F : ∀ (X : Type) [Group X], Prop} (hiso : IsoInvariant F)
    (hS : NoX27Simple F) (hE : NoE9Cfg F) : NoX27ConfigQ F := by
  intro A _ _ L P T h h27 hZ hF
  rcases hZ with hZ1 | hZ3
  · exact h.false_of_center_one hiso hS h27 hZ1 hF
  · obtain ⟨A', _, _, L', P', T', hcfg, ⟨e⟩⟩ := h.descend_x27 h27 hZ3
    exact hE A' L' P' T' (hiso _ _ e.symm hF) hcfg

theorem noX27ConfigQ_of_noCover {F : ∀ (X : Type) [Group X], Prop} (hiso : IsoInvariant F)
    (hS : NoX27Simple F)
    (hN : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
      Nat.card (Subgroup.center X) = 3 → F (X ⧸ Subgroup.center X) → False) :
    NoX27ConfigQ F := by
  intro A _ _ L P T h h27 hZ hF
  rcases hZ with hZ1 | hZ3
  · exact h.false_of_center_one hiso hS h27 hZ1 hF
  · exact hN ↥L h.component.1 hZ3 hF

end CFSG.Quasithin.H13.NQCore

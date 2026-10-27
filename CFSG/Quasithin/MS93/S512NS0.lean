module

public import CFSG.Quasithin.MS93.S512NW
public import CFSG.Quasithin.MS93.S512NFF
public import CFSG.Quasithin.MS93.S512NMod

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512N

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Finite G] in
theorem fixV_ne_bot_of_isPGroup {S₀ : Type} [CommGroup S₀] [Finite S₀] [Nontrivial S₀]
    (hS2 : ∀ s : S₀, s ^ 2 = 1) {P : Subgroup (MulAut S₀)} (hP : IsPGroup 2 ↥P) :
    fixV P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints S₀
  have hfix : Nat.card (MulAction.fixedPoints ↥P S₀) = Nat.card (fixV P) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
  rw [hfix] at hmod
  have hV2 : IsPGroup 2 S₀ := fun v => ⟨1, by rw [pow_one]; exact hS2 v⟩
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
  have heven : Nat.card S₀ % 2 = 0 := by
    rw [hn]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hn0)
  intro hbot
  rw [hbot, Subgroup.card_bot] at hmod
  have := hmod.symm
  unfold Nat.ModEq at this
  omega

theorem mem_pCoreOf_of_ker (h : PUHyp M T L) {S₀ : Type} [CommGroup S₀]
    {ρM : ↥M →* MulAut S₀} (hρ : S38E.IsIrrRep L ρM) {m : ↥M} (hm : ρM m = 1)
    (h2 : ∃ e : ℕ, (m : G) ^ 2 ^ e = 1) : (m : G) ∈ pCoreOf 2 M := by
  refine h.mem_pCoreOf_of_rel S38E.IsIrrRep.le_normalizer_kerG hρ.not_le_kerG m.2 h2
    fun l hl => ?_
  refine ⟨⁅m, ⟨l, h.L_le hl⟩⁆, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement, hm, commutatorElement_one_left]

namespace SecHyp

variable {h : PUHyp M T L} {V : Subgroup (puAmalgam h.le).Universal} (hn : SecHyp h V)
  {S : Type} [CommGroup S] {p : ↥V →* S}
  {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
  (hs : S36E.SecData (stab _ (baseA (puAmalgam h.le))) V (V ⊓ S5.bSub h.le L (baseA _)) S p ρ)
include hn hs

theorem restrict_eq_one_of_mem_qv {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) (hne : S₀ ≠ ⊥)
    (hmin : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → IsInv ρ S₁ → S₁ ≤ S₀ → S₁ = S₀)
    (g : ↥(stab (puAmalgam h.le) (baseA _)))
    (hg : (g : (puAmalgam h.le).Universal) ∈ Qv _ (baseA (puAmalgam h.le))) :
    restrict ρ hS₀ g = 1 := by
  have := hn.finite_S hs
  have hnt : Nontrivial ↥S₀ := (Subgroup.nontrivial_iff_ne_bot S₀).2 hne
  set Qs : Subgroup ↥(stab (puAmalgam h.le) (baseA _)) :=
    (Qv _ (baseA (puAmalgam h.le))).subgroupOf (stab (puAmalgam h.le) (baseA _))
  have hQ2 : IsPGroup 2 ↥Qs := by
    have h1 : IsPGroup 2 (Qv (puAmalgam h.le) (baseA _)) :=
      (isPGroup_qv _ h.hyp20 (not_isMVtx_baseB _)).to_le
        (qv_le_qv _ h.hyp20 (isMVtx_baseA _) (adj_baseA_baseB _))
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe (qv_le_stab _ _)).symm
  have hfix := fixV_ne_bot_of_isPGroup (fun s => Subtype.ext (by
    simpa using hn.sq_eq_one hs (s : S))) (hQ2.map (restrict ρ hS₀))
  let C : Subgroup S :=
    { carrier := {s | s ∈ S₀ ∧ ∀ q : ↥(stab (puAmalgam h.le) (baseA _)), q ∈ Qs → ρ q s = s}
      one_mem' := ⟨S₀.one_mem, fun q _ => map_one _⟩
      mul_mem' := fun {s t} hs' ht => ⟨S₀.mul_mem hs'.1 ht.1, fun q hq => by
        rw [map_mul, hs'.2 q hq, ht.2 q hq]⟩
      inv_mem' := fun {s} hs' => ⟨S₀.inv_mem hs'.1, fun q hq => by rw [map_inv, hs'.2 q hq]⟩ }
  have hCinv : IsInv ρ C := by
    rintro g' s ⟨hsS, hsQ⟩
    refine ⟨hS₀ g' s hsS, fun q hq => ?_⟩
    have hq' : g'⁻¹ * q * g' ∈ Qs := by
      rw [Subgroup.mem_subgroupOf] at hq ⊢
      have := (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_qv _ _ (inv_mem g'.2)) _).1 hq
      simpa using this
    have e2 : ρ q * ρ g' = ρ g' * ρ (g'⁻¹ * q * g') := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    calc ρ q (ρ g' s) = (ρ q * ρ g') s := rfl
      _ = (ρ g' * ρ (g'⁻¹ * q * g')) s := by rw [e2]
      _ = ρ g' (ρ (g'⁻¹ * q * g') s) := rfl
      _ = ρ g' s := by rw [hsQ _ hq']
  have hCne : C ≠ ⊥ := by
    intro hbot
    apply hfix
    rw [eq_bot_iff]
    intro s hs'
    have hsC : (s : S) ∈ C := ⟨s.2, fun q hq => by
      have := hs' (restrict ρ hS₀ q) ⟨q, hq, rfl⟩
      rw [← coe_restrict_apply ρ hS₀, this]⟩
    rw [hbot, Subgroup.mem_bot] at hsC
    exact Subgroup.mem_bot.2 (Subtype.ext hsC)
  have hCS : C = S₀ := hmin C hCne hCinv fun s hs' => hs'.1
  ext s
  have hsC : (s : S) ∈ C := by rw [hCS]; exact s.2
  rw [coe_restrict_apply, hsC.2 g (Subgroup.mem_subgroupOf.2 hg)]
  rfl

theorem isIrrRep_restrict {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) (hne : S₀ ≠ ⊥)
    (hmin : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → IsInv ρ S₁ → S₁ ≤ S₀ → S₁ = S₀) :
    S38E.IsIrrRep L ((restrict ρ hS₀).comp (eM h.le)) :=
  isIrrRep_comp h hS₀ hne hmin (hn.sq_eq_one hs) (hn.restrict_eq_one_of_mem_qv hs hS₀ hne hmin)
    (hn.eq_one_of_fixed hs)

theorem mem_qv_of_restrict_eq_one {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) (hne : S₀ ≠ ⊥)
    (hmin : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → IsInv ρ S₁ → S₁ ≤ S₀ → S₁ = S₀)
    {g : ↥(stab (puAmalgam h.le) (baseA _))} (hg : restrict ρ hS₀ g = 1)
    (h2 : ∃ e : ℕ, (g : (puAmalgam h.le).Universal) ^ 2 ^ e = 1) :
    (g : (puAmalgam h.le).Universal) ∈ Qv _ (baseA (puAmalgam h.le)) := by
  have hρ := hn.isIrrRep_restrict hs hS₀ hne hmin
  obtain ⟨m, rfl⟩ := eM_surjective h.le g
  have hm2 : ∃ e : ℕ, (m : G) ^ 2 ^ e = 1 := by
    obtain ⟨e, he⟩ := h2
    refine ⟨e, ?_⟩
    have h1 : eM h.le (m ^ 2 ^ e) = 1 := by
      apply Subtype.ext
      rw [map_pow, Subgroup.coe_pow]
      exact he
    have h2 : m ^ 2 ^ e = 1 := (eM_injective h.le) (h1.trans (map_one _).symm)
    simpa using congrArg Subtype.val h2
  have hmO := mem_pCoreOf_of_ker h hρ (by rw [MonoidHom.comp_apply, hg]) hm2
  rw [coe_eM, S5B.qv_baseA_eq h]
  exact (ofA_mem_imM_iff h.le m).2 hmO

theorem card_map_restrict {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) (hne : S₀ ≠ ⊥)
    (hmin : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → IsInv ρ S₁ → S₁ ≤ S₀ → S₁ = S₀)
    {E : Subgroup (puAmalgam h.le).Universal} (hEs : E ≤ stab _ (baseA (puAmalgam h.le)))
    (hEe : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map (restrict ρ hS₀)) =
      (Qv _ (baseA (puAmalgam h.le))).relIndex E := by
  have hker : (restrict ρ hS₀).ker ⊓ E.subgroupOf (stab (puAmalgam h.le) (baseA _)) =
      (Qv _ (baseA (puAmalgam h.le))).subgroupOf (stab (puAmalgam h.le) (baseA _)) ⊓
        E.subgroupOf (stab (puAmalgam h.le) (baseA _)) := by
    ext g
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨hg, hgE⟩
      refine ⟨hn.mem_qv_of_restrict_eq_one hs hS₀ hne hmin hg ⟨1, ?_⟩, hgE⟩
      simpa using hEe.2 _ hgE
    · rintro ⟨hgQ, hgE⟩
      exact ⟨hn.restrict_eq_one_of_mem_qv hs hS₀ hne hmin g hgQ, hgE⟩
  rw [← Subgroup.relIndex_ker, ← Subgroup.inf_relIndex_right, hker, Subgroup.inf_relIndex_right,
    Subgroup.relIndex_subgroupOf hEs]

theorem card_le_fixV_restrict {k : ℕ} {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀)
    {E : Subgroup (puAmalgam h.le).Universal}
    (hidx : (fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ)).index ≤ 2 ^ k) :
    Nat.card S₀ ≤ 2 ^ k * Nat.card (fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map
      (restrict ρ hS₀))) := by
  have := hn.finite_S hs
  set C := fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ)
  have hfix : fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map (restrict ρ hS₀)) =
      C.subgroupOf S₀ := by
    ext s
    rw [Subgroup.mem_subgroupOf, mem_fixV, mem_fixV]
    constructor
    · rintro hsf _ ⟨e, he, rfl⟩
      have := hsf _ ⟨e, he, rfl⟩
      rw [← coe_restrict_apply ρ hS₀, this]
    · rintro hsf _ ⟨e, he, rfl⟩
      apply Subtype.ext
      rw [coe_restrict_apply]
      exact hsf _ ⟨e, he, rfl⟩
  have hidx' : (C.subgroupOf S₀).index ≤ 2 ^ k := by
    calc (C.subgroupOf S₀).index = C.relIndex S₀ := rfl
      _ ≤ C.relIndex ⊤ := Subgroup.relIndex_le_of_le_right le_top
          Subgroup.FiniteIndex.index_ne_zero
      _ = C.index := Subgroup.relIndex_top_right C
      _ ≤ 2 ^ k := hidx
  rw [hfix]
  have h1 := (C.subgroupOf S₀).card_mul_index
  calc Nat.card S₀ = Nat.card (C.subgroupOf S₀) * (C.subgroupOf S₀).index := h1.symm
    _ ≤ Nat.card (C.subgroupOf S₀) * 2 ^ k := Nat.mul_le_mul_left _ hidx'
    _ = 2 ^ k * Nat.card (C.subgroupOf S₀) := mul_comm _ _

theorem range_le_imL (hd : S5.IsSp4Data M T L k F a) (hk2 : 2 ≤ k) {S₀ : Subgroup S}
    (hS₀ : IsInv ρ S₀) (hne : S₀ ≠ ⊥)
    (hmin : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → IsInv ρ S₁ → S₁ ≤ S₀ → S₁ = S₀) :
    ((restrict ρ hS₀).comp (eM h.le)).range ≤
      S38E.IsIrrRep.imL L ((restrict ρ hS₀).comp (eM h.le)) := by
  have hρ := hn.isIrrRep_restrict hs hS₀ hne hmin
  rintro _ ⟨m, rfl⟩
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hsup : L.subgroupOf M ⊔ (pCoreOf 2 M).subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.L_le (pCoreOf_le' M), ← S5B.eq_sup_pCoreOf h hd hk2,
      Subgroup.subgroupOf_self]
  have hmem : m ∈ L.subgroupOf M ⊔ (pCoreOf 2 M).subgroupOf M := by
    rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨l, hl, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  refine ⟨l, hl, ?_⟩
  rw [map_mul, hρ.pCore o (Subgroup.mem_subgroupOf.1 ho), mul_one]

end SecHyp

namespace NatHyp

variable {h : PUHyp M T L} {V E Z Y : Subgroup (puAmalgam h.le).Universal}
  (hn : NatHyp h k V E Z Y)
  {S : Type} [CommGroup S] {p : ↥V →* S}
  {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
  (hs : S36E.SecData (stab _ (baseA (puAmalgam h.le))) V (V ⊓ S5.bSub h.le L (baseA _)) S p ρ)
include hn hs

theorem card_map_restrict {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) (hne : S₀ ≠ ⊥)
    (hmin : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → IsInv ρ S₁ → S₁ ≤ S₀ → S₁ = S₀) :
    Nat.card ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map (restrict ρ hS₀)) = 2 ^ k :=
  (hn.toSecHyp.card_map_restrict hs hS₀ hne hmin hn.es hn.ee).trans hn.eq

theorem card_le_fixV_restrict {S₀ : Subgroup S} (hS₀ : IsInv ρ S₀) :
    Nat.card S₀ ≤ 2 ^ k * Nat.card (fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map
      (restrict ρ hS₀))) :=
  hn.toSecHyp.card_le_fixV_restrict hs hS₀ (hn.index_fixV_le hs)

theorem exists_natSub (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (hd : S5.IsSp4Data M T L k F a) :
    ∃ (S₀ : Subgroup S) (hS₀ : IsInv ρ S₀), S₀ ≠ ⊥ ∧
      (∀ S₁ : Subgroup S, S₁ ≠ ⊥ → IsInv ρ S₁ → S₁ ≤ S₀ → S₁ = S₀) ∧
      ∃ (F' : Type) (_ : Field F') (_ : Fintype F')
        (a' : ↥(stab (puAmalgam h.le) (baseA _)) →* MSP.Sp4 F')
        (θ : ↥S₀ ≃* Multiplicative (MSP.V4 F')), Fintype.card F' = 2 ^ k ∧
        Function.Surjective a' ∧
        (∀ (g : ↥(stab (puAmalgam h.le) (baseA _))) (s : ↥S₀),
          Multiplicative.toAdd (θ (restrict ρ hS₀ g s)) =
            MSP.mat (a' g) *ᵥ Multiplicative.toAdd (θ s)) ∧
        ∀ g, a' g = 1 ↔ restrict ρ hS₀ g = 1 := by
  have := hn.toSecHyp.finite_S hs
  obtain ⟨S₀, hne, hS₀, hmin⟩ := exists_minimal_invariant ρ (hn.toSecHyp.nontrivial_S hs)
  have hρ := hn.toSecHyp.isIrrRep_restrict hs hS₀ hne hmin
  set ρM := (restrict ρ hS₀).comp (eM h.le) with hρM
  set A := (E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map (restrict ρ hS₀) with hAdef
  have hmemR : ∀ g : ↥(stab (puAmalgam h.le) (baseA _)), restrict ρ hS₀ g ∈ ρM.range := by
    intro g
    obtain ⟨m, rfl⟩ := eM_surjective h.le g
    exact ⟨m, rfl⟩
  have hAX : A ≤ ρM.range := by
    rintro _ ⟨g, -, rfl⟩
    exact hmemR g
  have hEc : E ≤ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hn.ee.1
  have hA : IsElemAbelian2 A := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_iff.1 (hEc (Subgroup.mem_subgroupOf.1 hg')) _
        (Subgroup.mem_subgroupOf.1 hg)
    · rintro _ ⟨g, hg, rfl⟩
      rw [← map_pow]
      have : g ^ 2 = 1 := Subtype.ext (by simpa using hn.ee.2 _ (Subgroup.mem_subgroupOf.1 hg))
      rw [this, map_one]
  have hAc : 2 ^ k ≤ Nat.card A := (hn.card_map_restrict hs hS₀ hne hmin).ge
  have hAf := hn.card_le_fixV_restrict hs hS₀
  have hk2 : 2 ≤ k → ρM.range ≤ S38E.IsIrrRep.imL L ρM := fun hk2 =>
    hn.toSecHyp.range_le_imL hs hd hk2 hS₀ hne hmin
  obtain ⟨F', iF, fF, φ, θ, hcard, hφs, hθ⟩ := exists_coord h14 hSQ hT h hd hρ hAX hA hAc hAf hk2
  have hφi := injective_of_coord hθ
  set c : ↥(stab (puAmalgam h.le) (baseA _)) →* ↥ρM.range :=
    (restrict ρ hS₀).codRestrict ρM.range hmemR with hc
  refine ⟨S₀, hS₀, hne, hmin, F', iF, fF, φ.comp c, θ, hcard, ?_, fun g s => hθ (c g) s,
    fun g => ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := hφs x
    obtain ⟨_, ⟨m, rfl⟩⟩ := y
    exact ⟨eM h.le m, rfl⟩
  · rw [MonoidHom.comp_apply]
    constructor
    · intro h1
      have := hφi (h1.trans (map_one φ).symm)
      exact congrArg Subtype.val this
    · intro h1
      have : c g = 1 := Subtype.ext h1
      rw [this, map_one]

end NatHyp

end S512N

end CFSG.Quasithin.MS93

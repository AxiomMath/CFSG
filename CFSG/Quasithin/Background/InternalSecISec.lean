module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.Quasithin.Background.BlueprintB2Reduced
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Background.InternalSecTwo

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open CFSG.QuasithinUnique
open scoped IsMulCommutative

section Hom

variable {G : Type} [Group G] {L U : Subgroup G}

@[expose] noncomputable def autOnHom (hLU : L ≤ Subgroup.normalizer (U : Set G)) :
    ↥L →* ↥(autOn L U) :=
  (Setup.rho U L hLU).codRestrict (autOn L U)
    (fun l => (Setup.mem_autOn_self_iff hLU).2 ⟨l, rfl⟩)

theorem autOnHom_surjective (hLU : L ≤ Subgroup.normalizer (U : Set G)) :
    Function.Surjective (autOnHom hLU) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨l, rfl⟩ := (Setup.mem_autOn_self_iff hLU).1 hφ
  exact ⟨l, rfl⟩

theorem mem_ker_autOnHom (hLU : L ≤ Subgroup.normalizer (U : Set G)) (l : ↥L) :
    l ∈ (autOnHom hLU).ker ↔ (l : G) ∈ Subgroup.centralizer (U : Set G) := by
  rw [MonoidHom.mem_ker, ← Setup.rho_eq_one_iff hLU]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem pCore_le_ker_autOnHom (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hO2 : pCoreOf 2 (autOn L U) = ⊥) : CFSG.pCore 2 ↥L ≤ (autOnHom hLU).ker := by
  set P : Subgroup ↥(autOn L U) := (CFSG.pCore 2 ↥L).map (autOnHom hLU) with hP
  have hPn : P.Normal := Subgroup.Normal.map inferInstance _ (autOnHom_surjective hLU)
  have hPp : IsPGroup 2 ↥P := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map _
  have hle : P ≤ CFSG.Open.pCore 2 ↥(autOn L U) :=
    le_sSup ⟨hPn, hPp⟩
  have hbot : CFSG.Open.pCore 2 ↥(autOn L U) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (autOn L U).subtype_injective).1 hO2
  rw [hbot, le_bot_iff, Subgroup.map_eq_bot_iff] at hle
  exact hle

theorem ker_autOnHom_ne_top (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hnt : ¬ L ≤ Subgroup.centralizer (U : Set G)) : (autOnHom hLU).ker ≠ ⊤ := by
  intro h
  apply hnt
  intro l hl
  have : (⟨l, hl⟩ : ↥L) ∈ (autOnHom hLU).ker := by rw [h]; trivial
  exact (mem_ker_autOnHom hLU _).1 this

theorem isQuasisimple_autOn (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hO2 : pCoreOf 2 (autOn L U) = ⊥)
    (hnt : ¬ L ≤ Subgroup.centralizer (U : Set G)) : CFSG.IsQuasisimple ↥(autOn L U) := by
  have hle := pCore_le_ker_autOnHom hLU hO2
  set ρ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(autOn L U) := QuotientGroup.lift _ (autOnHom hLU) hle
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨l, rfl⟩ := autOnHom_surjective hLU y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hker : ρ.ker ≠ ⊤ := by
    intro h
    apply ker_autOnHom_ne_top hLU hnt
    rw [eq_top_iff]
    intro l _
    have : (QuotientGroup.mk l : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ ρ.ker := by rw [h]; trivial
    exact this
  have h1 := CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top
    (B1Red.isQuasisimple_to_open hq) ρ hker
  have e : ↥ρ.range ≃* ↥(autOn L U) :=
    (MulEquiv.subgroupCongr (MonoidHom.range_eq_top.2 hρ)).trans Subgroup.topEquiv
  exact B1Red.isQuasisimple_of_open
    (CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm h1)

variable [Finite G]

theorem sqtkGroup_autOn (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hS : SQTKGroup ↥L)
    (hker : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (U : Set G))) : SQTKGroup ↥(autOn L U) := by
  refine sqtkGroup_of_surjective (autOnHom hLU) (autOnHom_surjective hLU) ?_ hS
  intro x
  obtain ⟨k, hk⟩ := hker ⟨((x : ↥L) : G), (x : ↥L).2, (mem_ker_autOnHom hLU _).1 x.2⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  simpa using congrArg Subtype.val hk

omit [Finite G] in
theorem isPGroup_ker_of_simple (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) (hO2 : pCoreOf 2 (autOn L U) = ⊥)
    (hnt : ¬ L ≤ Subgroup.centralizer (U : Set G)) :
    IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (U : Set G)) := by
  have hle := pCore_le_ker_autOnHom hLU hO2
  set N := (autOnHom hLU).ker with hN
  have hNn : (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hNle : N ≤ CFSG.pCore 2 ↥L := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with h | h
    · intro x hx
      have : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) x ∈
          N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    · exfalso
      apply ker_autOnHom_ne_top hLU hnt
      rw [eq_top_iff]
      intro l _
      obtain ⟨n, hn, hnl⟩ : QuotientGroup.mk' (CFSG.pCore 2 ↥L) l ∈
          N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by rw [h]; trivial
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnl
      have h3 : n * (n⁻¹ * l) ∈ N := N.mul_mem hn (hle hnl)
      rw [mul_inv_cancel_left] at h3
      exact h3
  intro x
  have hx : (⟨(x : G), x.2.1⟩ : ↥L) ∈ N := (mem_ker_autOnHom hLU _).2 x.2.2
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, hNle hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  simpa using congrArg (fun y : ↥(CFSG.pCore 2 ↥L) => ((y : ↥L) : G)) hk

theorem isPGroup_ker_of_card (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hO2 : pCoreOf 2 (autOn L U) = ⊥)
    (hc : Nat.card ↥(autOn L U) = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :
    IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (U : Set G)) := by
  have hle := pCore_le_ker_autOnHom hLU hO2
  set N := (autOnHom hLU).ker with hN
  have h1 : Nat.card ↥L = Nat.card ↥(autOn L U) * Nat.card ↥N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
        (autOnHom_surjective hLU)).toEquiv]
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
  have hpos : 0 < Nat.card ↥(autOn L U) := Nat.card_pos
  have h3 : Nat.card ↥N = Nat.card ↥(CFSG.pCore 2 ↥L) := by
    rw [← hc] at h2
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)
  have hNeq : N = CFSG.pCore 2 ↥L := (Subgroup.eq_of_le_of_card_ge hle h3.le).symm
  intro x
  have hx : (⟨(x : G), x.2.1⟩ : ↥L) ∈ N := (mem_ker_autOnHom hLU _).2 x.2.2
  rw [hNeq] at hx
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  simpa using congrArg (fun y : ↥(CFSG.pCore 2 ↥L) => ((y : ↥L) : G)) hk

end Hom

section Ambient

variable {G : Type} [Group G]

theorem two_of_sup {L T : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) : ∀ y ∈ L ⊔ T, ∃ e : ℕ, y ^ 2 ^ e ∈ L := by
  intro y hy
  obtain ⟨l, hl, t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTL).1 hy
  have key : ∀ n : ℕ, (l * t) ^ n * (t ^ n)⁻¹ ∈ L := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have htn : t ^ n ∈ Subgroup.normalizer (L : Set G) := hTL (T.pow_mem ht n)
      have h1 : t ^ n * l * (t ^ n)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htn l).mp hl
      have e : (l * t) ^ (n + 1) * (t ^ (n + 1))⁻¹ =
          ((l * t) ^ n * (t ^ n)⁻¹) * (t ^ n * l * (t ^ n)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [e]
      exact L.mul_mem ih h1
  obtain ⟨e, he⟩ := hT ⟨t, ht⟩
  have he' : t ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  refine ⟨e, ?_⟩
  have := key (2 ^ e)
  rwa [he', inv_one, mul_one] at this

theorem open_pCore_eq (p : ℕ) (H : Type*) [Group H] : CFSG.Open.pCore p H = CFSG.pCore p H :=
  CFSG.RankThreeCoreUniqueness.Helpers.pCore_eq_sSup (G := H) p

theorem pCoreOf_le_centralizer_of_isPrimeReduced {V M X : Subgroup G} (hVM : V ≤ M)
    (hR : IsPrimeReduced 2 (V.subgroupOf M)) (hX : IsSubnormal X M) :
    pCoreOf 2 X ≤ Subgroup.centralizer (V : Set G) := by
  have h1 : pCoreOf 2 X ≤ pCoreOf 2 M :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2 hX
  have h2 := pCore_le_centralizer_of_isPrimeReduced hR
  intro x hx
  obtain ⟨y, hy, rfl⟩ := h1 hx
  have hyc := Subgroup.mem_centralizer_iff.mp (h2 hy)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have := hyc ⟨v, hVM hv⟩ hv
  exact congrArg Subtype.val this

end Ambient

end CFSG.Quasithin.InternalSec

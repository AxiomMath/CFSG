module

public import CFSG.Quasithin.MS93.S310M

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S310

theorem card_eq_of_surjective {A : Type*} [Group A] [Finite A] {F₁ F₂ : Type} [Field F₁]
    [Field F₂] [Finite F₁] [Finite F₂] [CharP F₁ 2] [CharP F₂ 2] {b₁ : A →* MSP.Sp4 F₁}
    {b₂ : A →* MSP.Sp4 F₂} (h₁ : Function.Surjective b₁) (h₂ : Function.Surjective b₂)
    (hk : ∀ x : A, (∃ e : ℕ, x ^ 2 ^ e = 1) → (b₁ x = 1 ↔ b₂ x = 1)) :
    Nat.card F₁ = Nat.card F₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 A) := inferInstance
  have hcard : ∀ {F : Type} [Field F] [Finite F] [CharP F 2] {b : A →* MSP.Sp4 F},
      Function.Surjective b → Nat.card ((S : Subgroup A).map b) = Nat.card F ^ 4 := by
    intro F _ _ _ b hb
    obtain ⟨P, hP⟩ := MSP.exists_sylow_sylS (F := F)
    rw [← Sylow.coe_mapSurjective hb, Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity P,
      hP, MSP.card_sylS]
  have hker : b₁.ker ⊓ (S : Subgroup A) = b₂.ker ⊓ (S : Subgroup A) := by
    ext x
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker]
    refine ⟨fun hx => ⟨?_, hx.2⟩, fun hx => ⟨?_, hx.2⟩⟩
    · obtain ⟨e, he⟩ := S.isPGroup' ⟨x, hx.2⟩
      exact (hk x ⟨e, by simpa using congrArg Subtype.val he⟩).1 hx.1
    · obtain ⟨e, he⟩ := S.isPGroup' ⟨x, hx.2⟩
      exact (hk x ⟨e, by simpa using congrArg Subtype.val he⟩).2 hx.1
  have h4 : Nat.card F₁ ^ 4 = Nat.card F₂ ^ 4 := by
    rw [← hcard h₁, ← hcard h₂, ← Subgroup.relIndex_ker, ← Subgroup.relIndex_ker,
      ← Subgroup.inf_relIndex_right, hker, Subgroup.inf_relIndex_right]
  exact Nat.pow_left_injective (by norm_num) h4

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem mem_pCoreOf_of_map_eq_one (h : PUHyp M T L) {F : Type} [Field F]
    {b : ↥M →* MSP.Sp4 F} (hL : ¬ L ≤ S5B.kerG b) {m : ↥M} (hm : b m = 1)
    (h2 : ∃ e : ℕ, (m : G) ^ 2 ^ e = 1) : (m : G) ∈ pCoreOf 2 M := by
  refine h.mem_pCoreOf_of_rel S5B.le_normalizer_kerG hL m.2 h2 fun l hl => ?_
  refine ⟨⁅m, ⟨l, h.L_le hl⟩⁆, ?_, rfl⟩
  show _ ∈ b.ker
  rw [MonoidHom.mem_ker, map_commutatorElement, hm, commutatorElement_one_left]

theorem map_eq_one_of_mem_pCoreOf {F : Type} [Field F] [Finite F] [CharP F 2]
    {b : ↥M →* MSP.Sp4 F} (hb : Function.Surjective b) {m : ↥M} (hm : (m : G) ∈ pCoreOf 2 M) :
    b m = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥M := (pCoreOf 2 M).subgroupOf M
  have hN : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le' M)).2 (le_normalizer_pCoreOf M)
  have hN2 : IsPGroup 2 N :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).of_equiv
      (Subgroup.subgroupOfEquivOfLe (pCoreOf_le' M)).symm
  have : (N.map b).Normal := hN.map b hb
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_top : N.map b ≤ ⊤)
    (Subgroup.normalizer_eq_top (N.map b)).ge (hN2.map b)
  rw [MSP.pCoreOf_top] at hle
  exact hle ⟨m, Subgroup.mem_subgroupOf.2 hm, rfl⟩

theorem card_field_eq (h : PUHyp M T L) {k₀ : ℕ} {F₀ : Type} [Field F₀] [Fintype F₀]
    {a₀ : ↥M →* ↥(StatedSp 2 F₀)} (hd : S5.IsSp4Data M T L k₀ F₀ a₀)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    {a : ↥(stab (puAmalgam h.le) (baseA _)) →* MSP.Sp4 F} (ha : Function.Surjective a)
    {V B : Subgroup (puAmalgam h.le).Universal}
    (hnat : IsSumOfNaturalModulesVia (stab _ (baseA _)) V (V ⊓ B) a false 1) :
    Fintype.card F = Fintype.card F₀ := by
  have : CharP F₀ 2 := S5B.charP_two_of_card hd.2.1
  have hmem : ∀ m : ↥M, (puAmalgam h.le).ofA m ∈ stab (puAmalgam h.le) (baseA _) := fun m => by
    rw [puAmalgam.stab_baseA]
    exact ⟨m, Subgroup.mem_subgroupOf.2 m.2, rfl⟩
  set e := (puAmalgam h.le).ofA.codRestrict _ hmem
  have he : Function.Surjective e := by
    rintro ⟨y, hy⟩
    rw [puAmalgam.stab_baseA] at hy
    obtain ⟨m, -, rfl⟩ := hy
    exact ⟨m, rfl⟩
  set b := a.comp e
  have hb : Function.Surjective b := ha.comp he
  have hbL : ¬ L ≤ S5B.kerG b := by
    intro hL
    apply not_commutator_le_of_nat h ha hnat
    obtain ⟨βv, hs⟩ := exists_setup h ha hnat
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hyA := hs.lt_le hy
    have hy' := hy
    rw [S5B.puTrans_L_baseA h] at hy'
    obtain ⟨l, hl, hly⟩ := hy'
    obtain ⟨m, hm, hml⟩ := hL (Subgroup.mem_subgroupOf.1 hl)
    have hml' : m = l := Subtype.ext hml
    subst hml'
    have hay : a ⟨y, hyA⟩ = 1 := by
      have : (⟨y, hyA⟩ : ↥(stab (puAmalgam h.le) (baseA _))) = e m := Subtype.ext hly.symm
      rw [this]
      exact hm
    have hcV : ⁅x, y⁆ ∈ V := hs.comm_le (Subgroup.commutator_mem_commutator hx hy)
    refine (hs.ker _ hcV).1 ?_
    rw [hs.map_commutator ⟨y, hyA⟩ hx, hay, MSP.mat_one, Matrix.one_mulVec, sub_self]
  have hk : ∀ x : ↥M, (∃ e : ℕ, x ^ 2 ^ e = 1) → (b x = 1 ↔ a₀ x = 1) := by
    rintro x ⟨n, hn⟩
    have hn' : (x : G) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact ⟨fun hx => map_eq_one_of_mem_pCoreOf hd.2.2.1
        (mem_pCoreOf_of_map_eq_one h hbL hx ⟨n, hn'⟩),
      fun hx => map_eq_one_of_mem_pCoreOf hb (S5B.mem_pCoreOf_of_ker h hd hx ⟨n, hn'⟩)⟩
  have := card_eq_of_surjective hb hd.2.2.1 hk
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this

theorem k_eq_of_nat (h : PUHyp M T L) {k₀ : ℕ} {F₀ : Type} [Field F₀] [Fintype F₀]
    {a₀ : ↥M →* ↥(StatedSp 2 F₀)} (hd : S5.IsSp4Data M T L k₀ F₀ a₀)
    {k : ℕ} {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ k)
    {a : ↥(stab (puAmalgam h.le) (baseA _)) →* MSP.Sp4 F} (ha : Function.Surjective a)
    {V B : Subgroup (puAmalgam h.le).Universal}
    (hnat : IsSumOfNaturalModulesVia (stab _ (baseA _)) V (V ⊓ B) a false 1) : k = k₀ := by
  have : CharP F 2 := S5B.charP_two_of_card hF
  have he := card_field_eq h hd ha hnat
  rw [hF, hd.2.1] at he
  exact Nat.pow_right_injective le_rfl he

end S310

end CFSG.Quasithin.MS93

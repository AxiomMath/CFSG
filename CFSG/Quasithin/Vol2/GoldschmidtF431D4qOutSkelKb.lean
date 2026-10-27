module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutSkel
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFixSylMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFixTf
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFixWc

public section

namespace CFSG.Quasithin.H13.F431.D4q.Out

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.ComponentClassification.RankTwoExceptional.D4
open scoped commutatorElement

set_option linter.unusedSectionVars false


theorem mem_Tsub_bot_iff {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (α : MulAut (Cm σ)) :
    α ∈ Tsub σ ⊥ ↔ ∃ u ∈ Ust σ, MulAut.conj u = α := by
  rw [mem_Tsub_iff]
  constructor
  · rintro ⟨u, hu, δ, hδ, rfl⟩
    rw [Subgroup.mem_bot.1 hδ, fieldActor_one, mul_one]
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, 1, Subgroup.one_mem _, by rw [fieldActor_one, mul_one]⟩

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f))
  {Kb : Subgroup (MulAut (Cm σ))} (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb)
  {S2 : Subgroup (K ≃+* K)} (hS2 : IsSylowTwoOf S2 (Kb.map (theta σ hf hK hσ)))

section Fields

include hf hK hσ hinn hS2 in
theorem sylow_T (hU : IsSylowTwoOf (Ust σ) ⊤) :
    IsSylowTwoOf ((Tsub σ S2).subgroupOf Kb) (⊤ : Subgroup Kb) := by
  have h := isSylowTwoOf_subgroupOf (Kb := Kb) (Tsub_le σ hf hK hσ hinn hS2.1) le_rfl
    (isSylowTwoOf_Tsub σ hf hK hσ hinn hS2 hU)
  rwa [Subgroup.subgroupOf_self] at h

include hf hK hσ hinn hS2 in
theorem T_le_N (P : Subgroup (Cm σ)) (hUP : Ust σ ≤ P)
    (hPstab : ∀ δ' : K ≃+* K, (fieldActor σ δ' : MulAut (Cm σ)) ∈ autStab P) :
    (Tsub σ S2).subgroupOf Kb ≤ (Kb ⊓ autStab P).subgroupOf Kb := fun x hx =>
  ⟨x.2, T_le_autStab σ (mem_Tsub_iff σ S2) P hUP hPstab hx⟩

theorem S_le_T_Kb : (Tsub σ ⊥).subgroupOf Kb ≤ (Tsub σ S2).subgroupOf Kb := fun _ hx =>
  S_le_T σ (mem_Tsub_iff σ S2) (mem_Tsub_bot_iff σ) hx

theorem S_norm : (Tsub σ S2).subgroupOf Kb ≤
    Subgroup.normalizer (((Tsub σ ⊥).subgroupOf Kb : Subgroup Kb) : Set Kb) := by
  intro x hx
  have h := T_le_normalizer σ (mem_Tsub_iff σ S2) (mem_Tsub_bot_iff σ) hx
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro y
  exact h y.1

include hf hK hσ hinn hS2 in
theorem exists_cyc_Kb {n : ℕ} (hn : 1 ≤ n) (hKn : Nat.card K = 2 ^ n) :
    ∃ t₀ : Kb, (Tsub σ S2).subgroupOf Kb =
      (Tsub σ ⊥).subgroupOf Kb ⊔ Subgroup.zpowers t₀ := by
  obtain ⟨t, htT, hteq⟩ := exists_cyc σ (mem_Tsub_iff σ S2) (mem_Tsub_bot_iff σ)
    (exists_generator_of_le_aut hn hKn S2)
  have hTK := Tsub_le σ hf hK hσ hinn hS2.1
  refine ⟨⟨t, hTK htT⟩, ?_⟩
  apply Subgroup.map_injective Kb.subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hTK,
    Subgroup.map_subgroupOf_eq_of_le (Tsub_le σ hf hK hσ hinn (bot_le.trans hS2.1)),
    MonoidHom.map_zpowers]
  exact hteq

theorem f_mem {δ : K ≃+* K} (hδ : δ ∈ S2) (hg : (fieldActor σ δ : MulAut (Cm σ)) ∈ Kb) :
    (⟨fieldActor σ δ, hg⟩ : Kb) ∈ (Tsub σ S2).subgroupOf Kb :=
  fieldActor_mem_T σ (mem_Tsub_iff σ S2) hδ

include hf hK hσ in
theorem f_not {δ : K ≃+* K} (hδ : δ ≠ 1) (hg : (fieldActor σ δ : MulAut (Cm σ)) ∈ Kb) :
    (⟨fieldActor σ δ, hg⟩ : Kb) ∉ (Tsub σ ⊥).subgroupOf Kb :=
  fieldActor_not_mem_S σ hf hK hσ (mem_Tsub_bot_iff σ) hδ

theorem f_sq {δ : K ≃+* K} (hδ : δ ^ 2 = 1) (hg : (fieldActor σ δ : MulAut (Cm σ)) ∈ Kb) :
    (⟨fieldActor σ δ, hg⟩ : Kb) ^ 2 = 1 := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact fieldActor_sq σ hδ

include hf hK hσ hinn hS2 in
theorem fieldActor_mem_Kb {δ : K ≃+* K} (hδ : δ ∈ S2) :
    (fieldActor σ δ : MulAut (Cm σ)) ∈ Kb :=
  Tsub_le σ hf hK hσ hinn hS2.1 (fieldActor_mem_T σ (mem_Tsub_iff σ S2) hδ)

end Fields

section Transport

variable {e : ℕ} (hfe : f = 2 * e) {δ : K ≃+* K} (hδ : ∀ c, δ c = c ^ 2 ^ (3 * e))

include hf hfe hK hσ hδ hinn hS2 in
theorem sylow_Tf (hg : (fieldActor σ δ : MulAut (Cm σ)) ∈ Kb) (P : Subgroup (Cm σ))
    (hUP : Ust σ ≤ P) (hPself : Subgroup.normalizer (P : Set (Cm σ)) = P)
    (hPstab : ∀ δ' : K ≃+* K, (fieldActor σ δ' : MulAut (Cm σ)) ∈ autStab P) :
    IsSylowTwoOf (spTf ((Tsub σ S2).subgroupOf Kb) ⟨fieldActor σ δ, hg⟩)
      (Subgroup.centralizer ({(⟨fieldActor σ δ, hg⟩ : Kb)} : Set Kb) ⊓
        (Kb ⊓ autStab P).subgroupOf Kb) := by
  have hTK := Tsub_le σ hf hK hσ hinn hS2.1
  have h1 : spTf ((Tsub σ S2).subgroupOf Kb) ⟨fieldActor σ δ, hg⟩ =
      (Tg σ δ (Tsub σ S2)).subgroupOf Kb := by
    rw [spTf, Tg, ← subgroupOf_centralizer_singleton hg]
    rfl
  have h2 : Subgroup.centralizer ({(⟨fieldActor σ δ, hg⟩ : Kb)} : Set Kb) ⊓
      (Kb ⊓ autStab P).subgroupOf Kb = (Ng σ δ Kb P).subgroupOf Kb := by
    rw [Ng, ← subgroupOf_centralizer_singleton hg, inf_comm]
    rfl
  rw [h1, h2]
  refine isSylowTwoOf_subgroupOf (inf_le_left.trans hTK) (inf_le_left.trans inf_le_left) ?_
  exact isSylowTwoOf_Tg_Ng σ δ hf hfe hK hσ hδ hinn hS2 (mem_Tsub_iff σ S2) P hUP hPself hPstab

include hf hfe hK hσ hδ hinn hS2 in
theorem tf_lt (hg : (fieldActor σ δ : MulAut (Cm σ)) ∈ Kb) (Q Z : Subgroup (Cm σ))
    (hQU : Q ≤ Ust σ) (hZQ : Z ≤ Q) (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z)
    (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z) (hQZ : (2 ^ f) ^ 8 * Nat.card Z ≤ Nat.card Q)
    {w : Cm σ} (hw : w ∈ Q) (i : Kb) (hi : (i : MulAut (Cm σ)) = MulAut.conj w) :
    Nat.card (spTf ((Tsub σ S2).subgroupOf Kb) ⟨fieldActor σ δ, hg⟩) <
      Nat.card ↥((Tsub σ S2).subgroupOf Kb ⊓ Subgroup.centralizer ({i} : Set Kb)) := by
  have hTK := Tsub_le σ hf hK hσ hinn hS2.1
  have h1 : spTf ((Tsub σ S2).subgroupOf Kb) ⟨fieldActor σ δ, hg⟩ =
      (Tg σ δ (Tsub σ S2)).subgroupOf Kb := by
    rw [spTf, Tg, ← subgroupOf_centralizer_singleton hg]
    rfl
  have hcw : (MulAut.conj w : MulAut (Cm σ)) ∈ Kb := hi ▸ i.2
  have hi' : (⟨MulAut.conj w, hcw⟩ : Kb) = i := Subtype.ext hi.symm
  have hX1 : Tg σ δ (Tsub σ S2) ≤ Kb := inf_le_left.trans hTK
  have hX2 : Tsub σ S2 ⊓ Subgroup.centralizer ({(MulAut.conj w : MulAut (Cm σ))} :
      Set (MulAut (Cm σ))) ≤ Kb := inf_le_left.trans hTK
  have h2 : (Tsub σ S2).subgroupOf Kb ⊓ Subgroup.centralizer ({i} : Set Kb) =
      (Tsub σ S2 ⊓ Subgroup.centralizer ({(MulAut.conj w : MulAut (Cm σ))} :
        Set (MulAut (Cm σ)))).subgroupOf Kb := by
    have := subgroupOf_centralizer_singleton (Kb := Kb) hcw
    rw [hi'] at this
    rw [← this]
    rfl
  rw [h1, h2, card_subgroupOf hX1, card_subgroupOf hX2]
  exact card_Tg_lt σ δ hf hfe hK hσ hδ (mem_Tsub_iff σ S2) Q Z hQU hZQ hcomm hZc hQZ hw

include hf hfe hK hσ hδ hinn hS2 in
theorem W_le (hg : (fieldActor σ δ : MulAut (Cm σ)) ∈ Kb) :
    spWf ((Tsub σ S2).subgroupOf Kb) ⟨fieldActor σ δ, hg⟩ ≤
      centerOf ((Tsub σ ⊥).subgroupOf Kb) := by
  have hTK := Tsub_le σ hf hK hσ hinn hS2.1
  have hSK := Tsub_le σ hf hK hσ hinn (bot_le.trans hS2.1)
  have h1 : spTf ((Tsub σ S2).subgroupOf Kb) ⟨fieldActor σ δ, hg⟩ =
      (Tg σ δ (Tsub σ S2)).subgroupOf Kb := by
    rw [spTf, Tg, ← subgroupOf_centralizer_singleton hg]
    rfl
  have hX1 : Tg σ δ (Tsub σ S2) ≤ Kb := inf_le_left.trans hTK
  intro x hx
  rw [spWf, h1, mem_centerOf_inf_commutator_subgroupOf hX1] at hx
  have h2 := Wg_le_centerOf σ δ hf hfe hK hσ (mem_Tsub_iff σ S2) (mem_Tsub_bot_iff σ) hx
  rw [centerOf_subgroupOf hSK]
  exact h2

include hf hfe hK hσ hδ hinn hS2 in
theorem mem_W (hg : (fieldActor σ δ : MulAut (Cm σ)) ∈ Kb) (z : Cm σ)
    (hz : (z : ModGL TwistTag.D4.tag K) = d4z K) (hzKb : (MulAut.conj z : MulAut (Cm σ)) ∈ Kb) :
    (⟨MulAut.conj z, hzKb⟩ : Kb) ∈ spWf ((Tsub σ S2).subgroupOf Kb) ⟨fieldActor σ δ, hg⟩ := by
  have hTK := Tsub_le σ hf hK hσ hinn hS2.1
  have h1 : spTf ((Tsub σ S2).subgroupOf Kb) ⟨fieldActor σ δ, hg⟩ =
      (Tg σ δ (Tsub σ S2)).subgroupOf Kb := by
    rw [spTf, Tg, ← subgroupOf_centralizer_singleton hg]
    rfl
  have hX1 : Tg σ δ (Tsub σ S2) ≤ Kb := inf_le_left.trans hTK
  rw [spWf, h1, mem_centerOf_inf_commutator_subgroupOf hX1]
  exact conj_z_mem_Wg σ δ hf hfe hK hσ hδ (mem_Tsub_iff σ S2) z hz

end Transport


end CFSG.Quasithin.H13.F431.D4q.Out

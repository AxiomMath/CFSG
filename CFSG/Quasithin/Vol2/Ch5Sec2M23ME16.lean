module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23MStr
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Mod
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Norm3Facts

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.M23Norm3 CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
open scoped Pointwise

@[expose] def k1M : Subgroup ↥M22 where
  carrier := {g | (g : Perm (Fin 22)) 0 = 0 ∧ (g : Perm (Fin 22)) 1 = 1 ∧
    ker1P ⇑(g : Perm (Fin 22))}
  mul_mem' := by
    rintro a b ⟨ha0, ha1, ha⟩ ⟨hb0, hb1, hb⟩
    refine ⟨?_, ?_, fun h hh p hp => ?_⟩
    · change (a : Perm (Fin 22)) ((b : Perm (Fin 22)) 0) = 0
      rw [hb0, ha0]
    · change (a : Perm (Fin 22)) ((b : Perm (Fin 22)) 1) = 1
      rw [hb1, ha1]
    · change (a : Perm (Fin 22)) ((b : Perm (Fin 22)) p) ∈ h
      exact ha h hh _ (hb h hh p hp)
  one_mem' := ⟨rfl, rfl, fun _ _ _ hp => hp⟩
  inv_mem' := by
    rintro a ⟨ha0, ha1, ha⟩
    refine ⟨?_, ?_, fun h hh p hp => ?_⟩
    · change (a : Perm (Fin 22))⁻¹ 0 = 0
      rw [Equiv.Perm.inv_eq_iff_eq, ha0]
    · change (a : Perm (Fin 22))⁻¹ 1 = 1
      rw [Equiv.Perm.inv_eq_iff_eq, ha1]
    · change (a : Perm (Fin 22))⁻¹ p ∈ h
      set σ : Perm (Fin 22) := (a : Perm (Fin 22)) with hσ
      have hpow : ∀ k : ℕ, ∀ q ∈ h, (σ ^ k) q ∈ h := by
        intro k
        induction k with
        | zero => exact fun q hq => hq
        | succ k ih =>
          intro q hq
          rw [pow_succ, Equiv.Perm.mul_apply]
          exact ih _ (ha h hh q hq)
      have hinv : σ⁻¹ = σ ^ (orderOf σ - 1) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos σ),
          pow_orderOf_eq_one]
      rw [hinv]
      exact hpow _ p hp

@[expose] def k2M : Subgroup ↥M22 where
  carrier := {g | ker2P ⇑(g : Perm (Fin 22))}
  mul_mem' := by
    intro a b ha hb p hp
    change (a : Perm (Fin 22)) ((b : Perm (Fin 22)) p) = p
    rw [hb p hp, ha p hp]
  one_mem' := fun _ _ => rfl
  inv_mem' := by
    intro a ha p hp
    change (a : Perm (Fin 22))⁻¹ p = p
    rw [Equiv.Perm.inv_eq_iff_eq, ha p hp]

theorem card_k1M :
    Nat.card k1M = 16 := by
  rw [← count_kernel_point, ← card_m22_subtype]
  rfl

theorem card_k2M :
    Nat.card k2M = 16 := by
  rw [← count_kernel_hexad, ← card_m22_subtype]
  rfl

theorem le_k1M_or_le_k2M
    {E : Subgroup ↥M22} (hEb : ∀ g ∈ E, borelP ⇑(g : Perm (Fin 22)))
    (hE2 : ∀ g ∈ E, g * g = 1) (hEc : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hE16 : Nat.card E = 16) : E ≤ k1M ∨ E ≤ k2M := by
  apply le_or_le_of_subset_union
  intro x hx
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hb := hEb x hx
  have hinv : ∀ g ∈ E, invP ⇑(g : Perm (Fin 22)) := fun g hg p => by
    have := congrArg (fun y : ↥M22 => (y : Perm (Fin 22)) p) (hE2 g hg)
    simpa [Equiv.Perm.mul_apply] using this
  have hbad : badBorel ⇑(x : Perm (Fin 22)) = true := by
    have hk1 : ¬ ker1P ⇑(x : Perm (Fin 22)) := fun h => h1 ⟨hb.1, hb.2.1, h⟩
    have hk2 : ¬ ker2P ⇑(x : Perm (Fin 22)) := fun h => h2 h
    unfold badBorel
    rw [ite_eq_left ⟨hb, hinv x hx, hk1, hk2⟩, decide_eq_true_iff]
    unfold borelInvCentCount
    rw [← card_m22_subtype, ← hE16]
    refine Nat.card_le_card_of_injective
      (fun g : ↥E => (⟨(g : ↥M22), hEb g g.2, hinv g g.2, fun p => ?_⟩ :
        {y : ↥M22 // borelP ⇑(y : Perm (Fin 22)) ∧ invP ⇑(y : Perm (Fin 22)) ∧
          commP ⇑(x : Perm (Fin 22)) ⇑(y : Perm (Fin 22))})) ?_
    · have := congrArg (fun y : ↥M22 => (y : Perm (Fin 22)) p) (hEc x hx g g.2)
      simpa [Equiv.Perm.mul_apply] using this
    · intro a b hab
      have h' := congrArg Subtype.val hab
      exact Subtype.ext h'
  have h0 : 0 < m22Count (fun x => badBorel x = true) := by
    rw [← card_m22_subtype]
    exact Nat.card_pos_iff.mpr ⟨⟨⟨x, hbad⟩⟩, inferInstance⟩
  rw [m22Count_borel_eq_zero] at h0
  exact absurd h0 (lt_irrefl 0)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_image_of_isElemAbelian
    {A A' : Subgroup G} (φ₁ : ↥m22TwoStab ≃* ↥A)
    (hiff : ∀ p : ↥m22TwoStab, ((φ₁ p : ↥A) : G) ∈ A' ↔ (p : ↥M22) ∈ m22PtHexStab)
    {E : Subgroup G} (hEA : E ≤ A ⊓ A') (hE2 : ∀ g ∈ E, g * g = 1)
    (hEc : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hE16 : Nat.card E = 16) :
    E = (k1M.subgroupOf m22TwoStab).map (A.subtype.comp φ₁.toMonoidHom) ∨
      E = (k2M.subgroupOf m22TwoStab).map (A.subtype.comp φ₁.toMonoidHom) := by
  set f : ↥m22TwoStab →* G := A.subtype.comp φ₁.toMonoidHom with hf
  have hfinj : Function.Injective f := Subtype.val_injective.comp φ₁.injective
  set E' : Subgroup ↥m22TwoStab := E.comap f with hE'
  have hmapE : E'.map f = E := by
    apply le_antisymm (Subgroup.map_comap_le f E)
    intro g hg
    refine ⟨φ₁.symm ⟨g, (hEA hg).1⟩, ?_, ?_⟩
    · show f (φ₁.symm ⟨g, (hEA hg).1⟩) ∈ E
      simpa [hf] using hg
    · simp [hf]
  have hcardE' : Nat.card E' = 16 := by
    rw [← hE16, ← hmapE, Subgroup.card_map_of_injective hfinj]
  set E₀ : Subgroup ↥M22 := E'.map m22TwoStab.subtype with hE₀
  have hcardE₀ : Nat.card E₀ = 16 := by
    rw [hE₀, Subgroup.card_map_of_injective m22TwoStab.subtype_injective, hcardE']
  have hmem₀ : ∀ g ∈ E₀, ∃ p : ↥m22TwoStab, (p : ↥M22) = g ∧ f p ∈ E := by
    rintro g ⟨p, hp, rfl⟩
    exact ⟨p, rfl, hp⟩
  have hEb : ∀ g ∈ E₀, borelP ⇑(g : Perm (Fin 22)) := by
    intro g hg
    obtain ⟨p, rfl, hp⟩ := hmem₀ g hg
    have h01 := L34Amalgam.mem_m22TwoStab_iff.mp p.2
    have hph := M22Witt.mem_m22PtHexStab_iff.mp ((hiff p).mp (hEA hp).2)
    exact ⟨h01.1, h01.2, hph.2⟩
  have hE₀2 : ∀ g ∈ E₀, g * g = 1 := by
    intro g hg
    obtain ⟨p, rfl, hp⟩ := hmem₀ g hg
    have h := hE2 _ hp
    rw [← map_mul] at h
    have h' : p * p = 1 := hfinj (by rw [h, map_one])
    exact congrArg Subtype.val h'
  have hE₀c : ∀ g ∈ E₀, ∀ h ∈ E₀, g * h = h * g := by
    intro g hg h hh
    obtain ⟨p, rfl, hp⟩ := hmem₀ g hg
    obtain ⟨q, rfl, hq⟩ := hmem₀ h hh
    have h1 := hEc _ hp _ hq
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (hfinj h1)
  have hE'eq : ∀ K₀ : Subgroup ↥M22, E₀ = K₀ → E' = K₀.subgroupOf m22TwoStab := by
    intro K₀ hK
    ext p
    rw [Subgroup.mem_subgroupOf, ← hK, hE₀]
    constructor
    · intro hp
      exact ⟨p, hp, rfl⟩
    · rintro ⟨q, hq, hqp⟩
      rwa [← Subtype.ext hqp]
  rcases le_k1M_or_le_k2M hEb hE₀2 hE₀c hcardE₀ with h1 | h2
  · left
    rw [← hmapE, hE'eq k1M (Subgroup.eq_of_le_of_card_ge h1 (by rw [card_k1M, hcardE₀]))]
  · right
    rw [← hmapE, hE'eq k2M (Subgroup.eq_of_le_of_card_ge h2 (by rw [card_k2M, hcardE₀]))]

theorem pCoreOf_M2_ne_pCoreOf_L {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Equiv.Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hS : IsM23Setting T H M2 π) (h16 : Nat.card ↥(pCoreOf 2 L) = 16) :
    pCoreOf 2 M2 ≠ pCoreOf 2 L := by
  intro hUV
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hHKT : H = oTwoUpper H ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' hTH
  have hKM : oTwoUpper H ≤ M := by
    rw [← normalizer_pCoreOf_L_eq hyp h16, ← hUV]
    exact hS.K_lt.le.trans (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M2))
  exact hyp.hStar.2.1 (hHKT ▸ sup_le hKM hyp.T_le)

theorem eq_or_eq_of_isElemAbelian_of_le_inf_L
    (h526 : Stmt5_2_6) (h527 : Stmt5_2_7) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz)
    (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) {E : Subgroup G} (hE : E ≤ T ⊓ L)
    (hE2 : ∀ g ∈ E, g * g = 1) (hEc : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hE16 : Nat.card E = 16) : E = pCoreOf 2 M2 ∨ E = pCoreOf 2 L := by
  obtain ⟨-, ⟨hG1, hG2, hG12, hSL, -, -⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  have hTL : T ⊓ L ≤ (L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H)) ⊓
      (D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H) := by
    rw [hG1, hG2, hG12, ← hSL]
    exact le_sup_left.trans le_sup_left
  obtain ⟨W1, W2, hW⟩ : ∃ W1 W2 : Subgroup G, ∀ E' : Subgroup G, E' ≤ T ⊓ L →
      (∀ g ∈ E', g * g = 1) → (∀ g ∈ E', ∀ h ∈ E', g * h = h * g) → Nat.card E' = 16 →
        E' = W1 ∨ E' = W2 := by
    rcases isParabolicIsoData_of_isAmalgamOfGroup hM23.1 with ⟨φ₁, -, -, hiff⟩ |
        ⟨φ₁, -, -, hiff⟩
    · exact ⟨_, _, fun E' hE' h2 hc h16 =>
        eq_image_of_isElemAbelian φ₁ hiff (hE'.trans hTL) h2 hc h16⟩
    · exact ⟨_, _, fun E' hE' h2 hc h16 =>
        eq_image_of_isElemAbelian φ₁ hiff (hE'.trans (hTL.trans (le_of_eq (inf_comm _ _)))) h2 hc
          h16⟩
  obtain ⟨-, hUle, hVle, -⟩ := inf_L_facts_of_setting h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨hbl, -, h16, hUQ, -⟩ := setting_L_facts h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨hab, hU16, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  have hU := hW (pCoreOf 2 M2) hUle
    (fun g hg => by rw [← sq]; exact hab.2 g hg)
    (fun g hg h hh => congrArg Subtype.val (hab.1.1.comm ⟨g, hg⟩ ⟨h, hh⟩)) hU16
  have hVsq := hbl.1.2.2.1
  rw [hUQ] at hVsq
  have hV := hW (pCoreOf 2 L) hVle
    (fun g hg => by rw [← sq]; exact hVsq.2 g hg)
    (fun g hg h hh => (Subgroup.mem_centralizer_iff.mp (hVsq.1 hh).2) g hg) h16
  have hne := pCoreOf_M2_ne_pCoreOf_L hyp hS h16
  rcases hW E hE hE2 hEc hE16 with rfl | rfl <;> rcases hU with hU | hU <;>
    rcases hV with hV | hV
  all_goals first
    | exact Or.inl hU.symm
    | exact Or.inr hV.symm
    | exact absurd (hU.trans hV.symm) hne

end CFSG.Quasithin.H13

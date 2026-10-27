module

public import CFSG.RankThree.PartTwo.KFacts.KS116LinRep

public section

namespace CFSG.RankThree.PartTwo.KFacts.NDC

section CommutingPair

open Representation
open scoped commutatorElement

private theorem perfect_top_of_perfect {H : Type} [Group H] (K : Subgroup H)
    (hK : ⁅K, K⁆ = K) : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact hK

private theorem inv_of_stable_AB {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    {H : Type} [Group H] (ρ : Representation F H V) (A B : Subgroup H) (hAB : A ⊔ B = ⊤)
    (W : Submodule F V) (hWA : ∀ a ∈ A, W ≤ W.comap (ρ a)) (hWB : ∀ b ∈ B, W ≤ W.comap (ρ b)) :
    ∀ h : H, W ≤ W.comap (ρ h) := by
  let M : Subgroup H :=
    { carrier := {h | ∀ w ∈ W, ρ h w ∈ W ∧ ρ h⁻¹ w ∈ W}
      mul_mem' := fun {x y} hx hy w hw => by
        refine ⟨?_, ?_⟩
        · rw [map_mul, Module.End.mul_apply]
          exact (hx _ (hy w hw).1).1
        · rw [mul_inv_rev, map_mul, Module.End.mul_apply]
          exact (hy _ (hx w hw).2).2
      one_mem' := fun w hw => by
        simp only [map_one, inv_one, Module.End.one_apply]
        exact ⟨hw, hw⟩
      inv_mem' := fun {x} hx w hw =>
        ⟨(hx w hw).2, by rw [inv_inv]; exact (hx w hw).1⟩ }
  have hAM : A ≤ M := fun a ha w hw =>
    ⟨Submodule.mem_comap.mp (hWA a ha hw), Submodule.mem_comap.mp (hWA a⁻¹ (A.inv_mem ha) hw)⟩
  have hBM : B ≤ M := fun b hb w hw =>
    ⟨Submodule.mem_comap.mp (hWB b hb hw), Submodule.mem_comap.mp (hWB b⁻¹ (B.inv_mem hb) hw)⟩
  have hsup : A ⊔ B ≤ M := sup_le hAM hBM
  intro h
  have hmem : h ∈ A ⊔ B := by rw [hAB]; exact Subgroup.mem_top h
  have hh : ∀ w ∈ W, ρ h w ∈ W ∧ ρ h⁻¹ w ∈ W := hsup hmem
  intro w hw
  exact Submodule.mem_comap.mpr (hh w hw).1

theorem no_commuting_perfect_pair_aux {F : Type} [Field F] [Finite F] :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V],
      Module.finrank F V = n → n ≤ 3 →
      ∀ (H : Type) [Group H] (ρ : Representation F H V) (A B : Subgroup H),
        A ⊔ B = ⊤ → ⁅A, A⁆ = A → ⁅B, B⁆ = B →
        (∀ a ∈ A, ∀ b ∈ B, ρ a * ρ b = ρ b * ρ a) →
        (∃ a ∈ A, ρ a ≠ 1) → (∃ b ∈ B, ρ b ≠ 1) → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn hn3 H _ ρ A B hAB hA hB hc hA1 hB1
  classical
  have hcv : ∀ a ∈ A, ∀ b ∈ B, ∀ v : V, ρ a (ρ b v) = ρ b (ρ a v) := by
    intro a ha b hb v
    have h' : (ρ a * ρ b) v = (ρ b * ρ a) v := by rw [hc a ha b hb]
    rwa [Module.End.mul_apply, Module.End.mul_apply] at h'
  have h2 : 2 ≤ Module.finrank F V := two_le_finrank_of_perfect_nontrivial ρ hA hA1
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  by_cases hcase1 : ∃ U : Submodule F V, (∀ h : H, U ≤ U.comap (ρ h)) ∧ U ≠ ⊥ ∧ U ≠ ⊤
  ·
    obtain ⟨U, hUinv, hU0, hUtop⟩ := hcase1
    have hlt : Module.finrank F U < n := by
      have := Submodule.finrank_lt hUtop
      omega
    have hUpos : 0 < Module.finrank F U :=
      Nat.pos_of_ne_zero (fun h0 => hU0 (Submodule.finrank_eq_zero.mp h0))
    have hsum := Submodule.finrank_quotient_add_finrank U
    have hqlt : Module.finrank F (V ⧸ U) < n := by omega
    have hcU : ∀ a ∈ A, ∀ b ∈ B,
        (ρ.subrepresentation U hUinv) a * (ρ.subrepresentation U hUinv) b =
          (ρ.subrepresentation U hUinv) b * (ρ.subrepresentation U hUinv) a :=
      fun a ha b hb => sub_mul_comm ρ U hUinv (hc a ha b hb)
    have hcQ : ∀ a ∈ A, ∀ b ∈ B,
        (ρ.quotient U hUinv) a * (ρ.quotient U hUinv) b =
          (ρ.quotient U hUinv) b * (ρ.quotient U hUinv) a :=
      fun a ha b hb => quot_mul_comm ρ U hUinv (hc a ha b hb)
    have hAU_or : (∃ a ∈ A, (ρ.subrepresentation U hUinv) a ≠ 1) ∨
        (∃ a ∈ A, (ρ.quotient U hUinv) a ≠ 1) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨a, ha, ha1⟩ := hA1
      exact ha1 (trivial_of_sub_quot ρ U hUinv hA (fun s hs => hcon.1 s hs)
        (fun s hs => hcon.2 s hs) a ha)
    have hBU_or : (∃ b ∈ B, (ρ.subrepresentation U hUinv) b ≠ 1) ∨
        (∃ b ∈ B, (ρ.quotient U hUinv) b ≠ 1) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨b, hb, hb1⟩ := hB1
      exact hb1 (trivial_of_sub_quot ρ U hUinv hB (fun s hs => hcon.1 s hs)
        (fun s hs => hcon.2 s hs) b hb)
    have hAUBU : (∃ a ∈ A, (ρ.subrepresentation U hUinv) a ≠ 1) →
        (∃ b ∈ B, (ρ.subrepresentation U hUinv) b ≠ 1) → False := fun hAU hBU =>
      ih (Module.finrank F U) hlt U rfl (by omega) H (ρ.subrepresentation U hUinv) A B hAB hA hB
        hcU hAU hBU
    have hAQBQ : (∃ a ∈ A, (ρ.quotient U hUinv) a ≠ 1) →
        (∃ b ∈ B, (ρ.quotient U hUinv) b ≠ 1) → False := fun hAQ hBQ =>
      ih (Module.finrank F (V ⧸ U)) hqlt (V ⧸ U) rfl (by omega) H (ρ.quotient U hUinv) A B hAB
        hA hB hcQ hAQ hBQ
    have hAUBQ : (∃ a ∈ A, (ρ.subrepresentation U hUinv) a ≠ 1) →
        (∃ b ∈ B, (ρ.quotient U hUinv) b ≠ 1) → False := fun hAU hBQ => by
      have e1 := two_le_finrank_of_perfect_nontrivial (ρ.subrepresentation U hUinv) hA hAU
      have e2 := two_le_finrank_of_perfect_nontrivial (ρ.quotient U hUinv) hB hBQ
      omega
    have hAQBU : (∃ a ∈ A, (ρ.quotient U hUinv) a ≠ 1) →
        (∃ b ∈ B, (ρ.subrepresentation U hUinv) b ≠ 1) → False := fun hAQ hBU => by
      have e1 := two_le_finrank_of_perfect_nontrivial (ρ.quotient U hUinv) hA hAQ
      have e2 := two_le_finrank_of_perfect_nontrivial (ρ.subrepresentation U hUinv) hB hBU
      omega
    rcases hAU_or with hAU | hAQ <;> rcases hBU_or with hBU | hBQ
    · exact hAUBU hAU hBU
    · exact hAUBQ hAU hBQ
    · exact hAQBU hAQ hBU
    · exact hAQBQ hAQ hBQ
  ·
    have hcase2 : ∀ U : Submodule F V, (∀ h : H, U ≤ U.comap (ρ h)) → U ≠ ⊥ → U = ⊤ := by
      intro U hUinv hU0
      by_contra hUtop
      exact hcase1 ⟨U, hUinv, hU0, hUtop⟩
    obtain ⟨C, hC⟩ : ∃ C : Submodule F V, ∀ v, v ∈ C ↔ ∀ a ∈ A, ρ a v = v := by
      refine ⟨{ carrier := {v | ∀ a ∈ A, ρ a v = v}
                add_mem' := ?_
                zero_mem' := ?_
                smul_mem' := ?_ }, fun v => Iff.rfl⟩
      · intro x y hx hy a ha
        simp only [map_add, hx a ha, hy a ha]
      · intro a _
        exact map_zero _
      · intro c x hx a ha
        simp only [map_smul, hx a ha]
    have hinvC : ∀ a ∈ A, C ≤ C.comap (ρ a) := by
      intro a ha v hv
      rw [Submodule.mem_comap, hC]
      intro a' ha'
      rw [(hC v).mp hv a ha]
      exact (hC v).mp hv a' ha'
    have hinvCB : ∀ b ∈ B, C ≤ C.comap (ρ b) := by
      intro b hb v hv
      rw [Submodule.mem_comap, hC]
      intro a ha
      rw [hcv a ha b hb v, (hC v).mp hv a ha]
    have hCbot : C = ⊥ := by
      by_contra hne
      have hCtop : C = ⊤ := hcase2 C (inv_of_stable_AB ρ A B hAB C hinvC hinvCB) hne
      obtain ⟨a, ha, ha1⟩ := hA1
      apply ha1
      ext v
      rw [Module.End.one_apply]
      have hvC : v ∈ C := by rw [hCtop]; exact Submodule.mem_top
      exact (hC v).mp hvC a ha
    have hC0 : ∀ v : V, (∀ a ∈ A, ρ a v = v) → v = 0 := by
      intro v hv
      have hvC : v ∈ C := (hC v).mpr hv
      rw [hCbot, Submodule.mem_bot] at hvC
      exact hvC
    have hne_top : (⊤ : Submodule F V) ≠ ⊥ := by
      intro h
      have h0 : Module.finrank F (⊤ : Submodule F V) = 0 := Submodule.finrank_eq_zero.mpr h
      rw [finrank_top] at h0
      omega
    have hex : ∃ k : ℕ, ∃ T : Submodule F V, T ≠ ⊥ ∧ (∀ a ∈ A, T ≤ T.comap (ρ a)) ∧
        Module.finrank F T = k :=
      ⟨_, ⊤, hne_top, fun a _ v _ => Submodule.mem_comap.mpr Submodule.mem_top, rfl⟩
    obtain ⟨S, hS0, hSA, hSk⟩ := Nat.find_spec hex
    have hmin : ∀ T : Submodule F V, T ≠ ⊥ → (∀ a ∈ A, T ≤ T.comap (ρ a)) →
        Module.finrank F S ≤ Module.finrank F T := by
      intro T hT hTA
      rw [hSk]
      exact Nat.find_min' hex ⟨T, hT, hTA, rfl⟩
    have hminS : ∀ T : Submodule F V, T ≠ ⊥ → (∀ a ∈ A, T ≤ T.comap (ρ a)) → T ≤ S → T = S :=
      fun T hT hTA hTS => Submodule.eq_of_le_of_finrank_le hTS (hmin T hT hTA)
    by_cases hSt : S = ⊤
    ·
      have hirr : ∀ U : Submodule F V, (∀ a ∈ A, U ≤ U.comap (ρ a)) → U = ⊥ ∨ U = ⊤ := by
        intro U hUA
        by_cases hU0 : U = ⊥
        · exact Or.inl hU0
        · right
          exact (hminS U hU0 hUA (by rw [hSt]; exact le_top)).trans hSt
      have hsc : ∀ b ∈ B, ∀ b' ∈ B, ρ b * ρ b' = ρ b' * ρ b := fun b hb b' hb' =>
        schur_commute ρ A hirr (ρ b) (ρ b') (fun a ha => (hc a ha b hb).symm)
          (fun a ha => (hc a ha b' hb').symm)
      obtain ⟨b, hb, hb1⟩ := hB1
      exact hb1 (perfect_trivial_of_comm ρ hB hsc b hb)
    ·
      have hS2 : 2 ≤ Module.finrank F S := by
        by_contra hlt
        have hlt1 : Module.finrank F S ≤ 1 := by omega
        let ρA : Representation F A V := ρ.comp A.subtype
        have hSA' : ∀ g : A, S ≤ S.comap (ρA g) := fun g => hSA g.1 g.2
        let ρAS : Representation F A S := ρA.subrepresentation S hSA'
        have hcS : ∀ g ∈ (⊤ : Subgroup A), ∀ g' ∈ (⊤ : Subgroup A),
            ρAS g * ρAS g' = ρAS g' * ρAS g :=
          fun g _ g' _ => comm_of_finrank_le_one hlt1 (ρAS g) (ρAS g')
        have htriv := perfect_trivial_of_comm ρAS (perfect_top_of_perfect A hA) hcS
        have hfixA : ∀ a ∈ A, ∀ u ∈ S, ρ a u = u := by
          intro a ha u hu
          have h1 : ρAS ⟨a, ha⟩ = 1 := htriv ⟨a, ha⟩ (Subgroup.mem_top _)
          exact (sub_apply_eq_one_iff ρA S hSA' ⟨a, ha⟩).mp h1 u hu
        apply hS0
        rw [Submodule.eq_bot_iff]
        intro u hu
        exact hC0 u (fun a ha => hfixA a ha u hu)
      have hinj : ∀ b : H, Function.Injective (ρ b) := fun b =>
        Function.LeftInverse.injective (g := ρ b⁻¹) (fun x => by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])
      have hfinr : ∀ b : H, Module.finrank F ↥(S.map (ρ b)) = Module.finrank F S := fun b =>
        ((Submodule.equivMapOfInjective (ρ b) (hinj b) S).finrank_eq).symm
      have hSbA : ∀ b ∈ B, ∀ a ∈ A, S.map (ρ b) ≤ (S.map (ρ b)).comap (ρ a) := by
        intro b hb a ha x hx
        obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hx
        rw [Submodule.mem_comap, hcv a ha b hb s]
        exact Submodule.mem_map_of_mem (Submodule.mem_comap.mp (hSA a ha hs))
      have hSb_eq : ∀ b ∈ B, S.map (ρ b) = S := by
        intro b hb
        by_contra hne
        have hTA : ∀ a ∈ A, (S ⊓ S.map (ρ b)) ≤ (S ⊓ S.map (ρ b)).comap (ρ a) := by
          intro a ha x hx
          rw [Submodule.mem_inf] at hx
          rw [Submodule.mem_comap, Submodule.mem_inf]
          exact ⟨Submodule.mem_comap.mp (hSA a ha hx.1),
            Submodule.mem_comap.mp (hSbA b hb a ha hx.2)⟩
        by_cases hT0 : S ⊓ S.map (ρ b) = ⊥
        · have hsum := Submodule.finrank_sup_add_finrank_inf_eq S (S.map (ρ b))
          rw [hT0, finrank_bot, hfinr b] at hsum
          have hle := Submodule.finrank_le (S ⊔ S.map (ρ b))
          omega
        · have hTS : S ⊓ S.map (ρ b) = S := hminS _ hT0 hTA inf_le_left
          have hSle : S ≤ S.map (ρ b) := hTS.symm.le.trans inf_le_right
          exact hne (Submodule.eq_of_le_of_finrank_le hSle (hfinr b).le).symm
      have hSB : ∀ b ∈ B, S ≤ S.comap (ρ b) := by
        intro b hb s hs
        rw [Submodule.mem_comap]
        have hmem : ρ b s ∈ S.map (ρ b) := Submodule.mem_map_of_mem hs
        rwa [hSb_eq b hb] at hmem
      have hHS := inv_of_stable_AB ρ A B hAB S hSA hSB
      exact hSt (hcase2 S hHS hS0)

theorem no_commuting_perfect_pair {F : Type} [Field F] [Finite F] {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (hd : Module.finrank F V ≤ 3) (ρ : Representation F G V) (A B : Subgroup G)
    (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, ρ a * ρ b = ρ b * ρ a)
    (hA1 : ∃ a ∈ A, ρ a ≠ 1) (hB1 : ∃ b ∈ B, ρ b ≠ 1) : False := by
  have hAK : A ≤ A ⊔ B := le_sup_left
  have hBK : B ≤ A ⊔ B := le_sup_right
  have hinj : Function.Injective (A ⊔ B).subtype := Subgroup.subtype_injective _
  have hmapA : (A.subgroupOf (A ⊔ B)).map (A ⊔ B).subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAK]
  have hmapB : (B.subgroupOf (A ⊔ B)).map (A ⊔ B).subtype = B := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBK]
  have hsup : A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B) = ⊤ := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_sup, hmapA, hmapB, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hA' : ⁅A.subgroupOf (A ⊔ B), A.subgroupOf (A ⊔ B)⁆ = A.subgroupOf (A ⊔ B) := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hmapA]
    exact hA
  have hB' : ⁅B.subgroupOf (A ⊔ B), B.subgroupOf (A ⊔ B)⁆ = B.subgroupOf (A ⊔ B) := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hmapB]
    exact hB
  have hc' : ∀ a ∈ A.subgroupOf (A ⊔ B), ∀ b ∈ B.subgroupOf (A ⊔ B),
      (ρ.comp (A ⊔ B).subtype) a * (ρ.comp (A ⊔ B).subtype) b =
        (ρ.comp (A ⊔ B).subtype) b * (ρ.comp (A ⊔ B).subtype) a :=
    fun a ha b hb => hc a (Subgroup.mem_subgroupOf.mp ha) b (Subgroup.mem_subgroupOf.mp hb)
  obtain ⟨a, ha, ha1⟩ := hA1
  obtain ⟨b, hb, hb1⟩ := hB1
  exact no_commuting_perfect_pair_aux (F := F) (Module.finrank F V) V rfl hd (↥(A ⊔ B))
    (ρ.comp (A ⊔ B).subtype) (A.subgroupOf (A ⊔ B)) (B.subgroupOf (A ⊔ B)) hsup hA' hB' hc'
    ⟨⟨a, hAK ha⟩, Subgroup.mem_subgroupOf.mpr ha, ha1⟩
    ⟨⟨b, hBK hb⟩, Subgroup.mem_subgroupOf.mpr hb, hb1⟩

end CommutingPair

end CFSG.RankThree.PartTwo.KFacts.NDC

end

module

public import CFSG.Open.LocalVocabulary
import CFSG.Mathlib.GroupTheory.PermCenter

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Open

theorem exists_permHom {H : Type*} [Group H] {X : Type*} (act : H → X → X)
    (hone : ∀ x, act 1 x = x) (hmul : ∀ g h x, act (g * h) x = act g (act h x)) {n : ℕ}
    (p : Fin n → X) (hinj : Function.Injective p)
    (hinv : ∀ (h : H) (i : Fin n), ∃ j : Fin n, act h (p i) = p j) :
    ∃ π : H →* Equiv.Perm (Fin n), ∀ (h : H) (i : Fin n), act h (p i) = p (π h i) := by
  classical
  let f : H → Fin n → Fin n := fun h i => Classical.choose (hinv h i)
  have hf : ∀ h i, act h (p i) = p (f h i) := fun h i => Classical.choose_spec (hinv h i)
  have hf1 : f 1 = id := by
    funext i
    exact hinj (by rw [← hf 1 i, hone]; rfl)
  have hfcomp : ∀ g h, f (g * h) = f g ∘ f h := by
    intro g h
    funext i
    apply hinj
    calc p (f (g * h) i) = act (g * h) (p i) := (hf (g * h) i).symm
      _ = act g (act h (p i)) := hmul g h (p i)
      _ = act g (p (f h i)) := by rw [hf h i]
      _ = p (f g (f h i)) := hf g (f h i)
  have hleft : ∀ h, f h⁻¹ ∘ f h = id := by
    intro h
    rw [← hfcomp h⁻¹ h, inv_mul_cancel, hf1]
  have hright : ∀ h, f h ∘ f h⁻¹ = id := by
    intro h
    rw [← hfcomp h h⁻¹, mul_inv_cancel, hf1]
  let πfun : H → Equiv.Perm (Fin n) := fun h =>
    Equiv.ofBijective (f h)
      ⟨Function.LeftInverse.injective (fun i => congrFun (hleft h) i),
       Function.RightInverse.surjective (fun i => congrFun (hright h) i)⟩
  have hπ : ∀ h i, πfun h i = f h i := fun h i => Equiv.ofBijective_apply (f h) _ i
  have hmulπ : ∀ g h, πfun (g * h) = πfun g * πfun h := by
    intro g h
    apply Equiv.ext
    intro i
    rw [Equiv.Perm.mul_apply, hπ, hπ, hπ]
    exact congrFun (hfcomp g h) i
  have honeπ : πfun 1 = 1 := by
    apply Equiv.ext
    intro i
    rw [hπ, hf1]
    rfl
  exact ⟨{ toFun := πfun, map_one' := honeπ, map_mul' := hmulπ }, fun h i => hf h i⟩

theorem eq_alternatingGroup_of_card {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : 2 * Nat.card H = n.factorial) : H = alternatingGroup (Fin n) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  haveI : Nonempty ↥H := ⟨⟨1, H.one_mem⟩⟩
  have hcard : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hindex : Nat.card H * H.index = Nat.card H * 2 := by
    calc Nat.card H * H.index = Nat.card (Equiv.Perm (Fin n)) := H.card_mul_index
      _ = n.factorial := hcard
      _ = 2 * Nat.card H := hH.symm
      _ = Nat.card H * 2 := Nat.mul_comm _ _
  exact Nat.eq_of_mul_eq_mul_left hpos hindex

theorem normal_pGroup_eq_bot_of_simple {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) (K : Subgroup S) (hK : K.Normal) (h2 : IsPGroup 2 K) :
    K = ⊥ := by
  haveI : K.Normal := hK
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
  · exact h
  · exfalso
    rw [h] at h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hS : IsPGroup 2 S := h2.of_equiv Subgroup.topEquiv
    obtain ⟨a, b, hab⟩ := hnc
    haveI : Nontrivial S := ⟨a, b, fun h => hab (by rw [h])⟩
    have hcen : Nontrivial (Subgroup.center S) := hS.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hc | hc
    · obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : Subgroup.center S)
      rw [hc, Subgroup.mem_bot] at hx
      exact hx1 (Subtype.ext hx)
    · have ha : a ∈ Subgroup.center S := by rw [hc]; exact Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

theorem perm5_normal_two_eq_bot (K : Subgroup (Equiv.Perm (Fin 5))) (hK : K.Normal)
    (h2 : IsPGroup 2 K) : K = ⊥ := by
  classical
  let A : Subgroup (Equiv.Perm (Fin 5)) := alternatingGroup (Fin 5)
  have hcenter : Subgroup.center (Equiv.Perm (Fin 5)) = ⊥ :=
    CFSG.center_perm_eq_bot_of_three_le_card (by simp)
  have hKA : K ⊓ A = ⊥ := by
    have hLnorm : ((K ⊓ A).subgroupOf A).Normal := by
      rw [Subgroup.normal_subgroupOf_iff inf_le_right]
      intro h k hh hk
      exact ⟨hK.conj_mem h hh.1 k, A.mul_mem (A.mul_mem hk hh.2) (A.inv_mem hk)⟩
    haveI : IsSimpleGroup ↥A := alternatingGroup.isSimpleGroup_five
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ A).subgroupOf A) with hbot | htop
    · rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hxA : x ∈ A := (Subgroup.mem_inf.mp hx).2
      have hxL : (⟨x, hxA⟩ : ↥A) ∈ (K ⊓ A).subgroupOf A := by
        rw [Subgroup.mem_subgroupOf]; exact hx
      rw [hbot, Subgroup.mem_bot] at hxL
      exact Subtype.ext_iff.mp hxL
    · exfalso
      have hAK : A ≤ K := by
        intro x hx
        have hxA : (⟨x, hx⟩ : ↥A) ∈ (K ⊓ A).subgroupOf A := by
          rw [htop]; exact Subgroup.mem_top _
        rw [Subgroup.mem_subgroupOf] at hxA
        exact (Subgroup.mem_inf.mp hxA).1
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hA2 : IsPGroup 2 ↥A := h2.to_le hAK
      obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2) (G := ↥A)).mp hA2
      have hAcard : Nat.card ↥A = 60 := by
        change Nat.card ↥(alternatingGroup (Fin 5)) = 60
        rw [nat_card_alternatingGroup, Nat.card_fin]
        norm_num
      have h3 : 3 ∣ 2 ^ m := by rw [← hm, hAcard]; norm_num
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hinj : Function.Injective (Equiv.Perm.sign.comp K.subtype) :=
    (MonoidHom.ker_eq_bot_iff _).mp (by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hxA : (x : Equiv.Perm (Fin 5)) ∈ A := by
        change (x : Equiv.Perm (Fin 5)) ∈ alternatingGroup (Fin 5)
        rw [Equiv.Perm.mem_alternatingGroup]; exact hx
      have hxKA : (x : Equiv.Perm (Fin 5)) ∈ K ⊓ A := ⟨x.2, hxA⟩
      rw [hKA, Subgroup.mem_bot] at hxKA
      exact Subtype.ext hxKA)
  rw [Subgroup.eq_bot_iff_forall]
  intro τ hτ
  have hmem : τ ∈ Subgroup.center (Equiv.Perm (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro σ
    have hconj : σ * τ * σ⁻¹ ∈ K := hK.conj_mem τ hτ σ
    have hsign : (Equiv.Perm.sign.comp K.subtype) ⟨σ * τ * σ⁻¹, hconj⟩ =
        (Equiv.Perm.sign.comp K.subtype) ⟨τ, hτ⟩ := by
      show Equiv.Perm.sign (σ * τ * σ⁻¹) = Equiv.Perm.sign τ
      rw [map_mul, map_mul, map_inv,
        mul_comm (Equiv.Perm.sign σ) (Equiv.Perm.sign τ), mul_assoc, mul_inv_cancel, mul_one]
    have heq : (⟨σ * τ * σ⁻¹, hconj⟩ : ↥K) = ⟨τ, hτ⟩ := hinj hsign
    have hval : σ * τ * σ⁻¹ = τ := congrArg Subtype.val heq
    calc σ * τ = (σ * τ * σ⁻¹) * σ := by group
      _ = τ * σ := by rw [hval]
  rwa [hcenter, Subgroup.mem_bot] at hmem

theorem ker_eq_of_counts {X K : Type*} [Group X] [Finite X] [Group K] (p : X →* K)
    (E : Subgroup X) (hE : E ≤ p.ker) {a b : ℕ} (ha : a ≤ Nat.card E)
    (hb : b ≤ Nat.card p.range) (hX : Nat.card X ≤ a * b) :
    E = p.ker ∧ Nat.card E = a ∧ Nat.card p.range = b := by
  haveI : Nonempty X := ⟨1⟩
  have hquot : Nat.card (X ⧸ p.ker) = Nat.card p.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange p).toEquiv
  have hkerX : Nat.card p.ker * Nat.card p.range = Nat.card X := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup p.ker, hquot, Nat.mul_comm]
  have hEker : Nat.card E ≤ Nat.card p.ker := Subgroup.card_le_of_le hE
  have hchain : a * b ≤ Nat.card E * Nat.card p.range := Nat.mul_le_mul ha hb
  have hchain2 : Nat.card E * Nat.card p.range ≤ Nat.card p.ker * Nat.card p.range :=
    Nat.mul_le_mul_right _ hEker
  have hchain3 : Nat.card p.ker * Nat.card p.range ≤ a * b := by rw [hkerX]; exact hX
  have hEab : Nat.card E * Nat.card p.range = a * b :=
    le_antisymm (le_trans hchain2 hchain3) hchain
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have habpos : 0 < a * b := lt_of_lt_of_le hXpos hX
  have hapos : 0 < a := Nat.pos_of_mul_pos_right habpos
  have hbpos : 0 < b := Nat.pos_of_mul_pos_left habpos
  have habp : a * b = a * Nat.card p.range := by
    apply le_antisymm
    · exact Nat.mul_le_mul_left a hb
    · calc a * Nat.card p.range ≤ Nat.card E * Nat.card p.range := Nat.mul_le_mul_right _ ha
        _ = a * b := hEab
  have hrange : Nat.card p.range = b := (Nat.eq_of_mul_eq_mul_left hapos habp).symm
  have hrange_pos : 0 < Nat.card p.range := hrange.symm ▸ hbpos
  have hEa : Nat.card E = a := by
    apply Nat.eq_of_mul_eq_mul_right hrange_pos
    rw [hEab, habp]
  have hker_eq : Nat.card p.ker * Nat.card p.range = Nat.card E * Nat.card p.range :=
    le_antisymm (by rw [hEab]; exact hchain3) hchain2
  have hker_a : Nat.card p.ker = a := by
    rw [Nat.eq_of_mul_eq_mul_right hrange_pos hker_eq, hEa]
  exact ⟨Subgroup.eq_of_le_of_card_ge hE (by rw [hker_a, hEa]), hEa, hrange⟩

theorem mem_of_card_le_length {Γ : Type*} [Group Γ] (Q : Subgroup Γ) [Finite Q] (l : List Γ)
    (hnd : l.Nodup) (hl : ∀ x ∈ l, x ∈ Q) (hc : Nat.card Q ≤ l.length) : ∀ q ∈ Q, q ∈ l := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  intro q hq
  let t : Finset Γ := (Finset.univ : Finset Q).map (Function.Embedding.subtype (· ∈ Q))
  have htcard : t.card = Nat.card Q := by
    rw [Finset.card_map, Finset.card_univ, ← Nat.card_eq_fintype_card]
  have hsub : l.toFinset ⊆ t := by
    intro x hx
    rw [List.mem_toFinset] at hx
    show x ∈ (Finset.univ : Finset Q).map (Function.Embedding.subtype (· ∈ Q))
    rw [Finset.mem_map]
    exact ⟨⟨x, hl x hx⟩, Finset.mem_univ _, rfl⟩
  have hcardle : t.card ≤ l.toFinset.card := by
    rw [htcard, List.toFinset_card_of_nodup hnd]; exact hc
  have heq : l.toFinset = t := Finset.eq_of_subset_of_card_le hsub hcardle
  have hqt : q ∈ t := by
    show q ∈ (Finset.univ : Finset Q).map (Function.Embedding.subtype (· ∈ Q))
    rw [Finset.mem_map]
    exact ⟨⟨q, hq⟩, Finset.mem_univ _, rfl⟩
  rw [← heq] at hqt
  exact List.mem_toFinset.mp hqt

theorem isElemAbelian_of_list {Γ : Type*} [Group Γ] (Q : Subgroup Γ) (l : List Γ)
    (hQ : ∀ q ∈ Q, q ∈ l) (hcomm : ∀ a ∈ l, ∀ b ∈ l, a * b = b * a)
    (hsq : ∀ a ∈ l, a ^ 2 = 1) : IsElemAbelian 2 Q := by
  refine ⟨?_, ?_⟩
  · rw [isMulCommutative_iff]
    intro a b
    exact Subtype.ext (hcomm a.1 (hQ a.1 a.2) b.1 (hQ b.1 b.2))
  · intro x hx
    exact hsq x (hQ x hx)

end CFSG.Quasithin.AppendixH.H12

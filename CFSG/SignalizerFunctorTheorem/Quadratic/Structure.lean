module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Decomposition

public section

namespace CFSG.SignalizerFunctorTheorem.Quadratic

section Generic

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem str_blocks_bot : blocks (⊥ : Subgroup (LGL p V)) = ∅ := by
  ext E
  simp only [blocks, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨A, hA, -⟩
  have hAbot : A = ⊥ := le_bot_iff.mp hA.1.1
  exact hA.2.1 (by rw [hAbot]; exact commSub_bot)

theorem str_isAVMin_of_le {H F B : Subgroup (LGL p V)} (hFH : F ≤ H) (hB : IsAVMin H B)
    (hBF : B ≤ F) : IsAVMin F B := by
  refine ⟨⟨hBF, hB.1.2.1, hB.1.2.2⟩, hB.2.1, ?_⟩
  intro B' hB' hne hle
  exact hB.2.2 B' ⟨hB'.1.trans hFH, hB'.2.1, hB'.2.2⟩ hne hle

theorem str_isAVMin_of_isAVMin {H F B : Subgroup (LGL p V)} (hFH : F ≤ H) (hB : IsAVMin F B) :
    IsAVMin H B := by
  refine ⟨⟨hB.1.1.trans hFH, hB.1.2.1, hB.1.2.2⟩, hB.2.1, ?_⟩
  intro B' hB' hne hle
  exact hB.2.2 B' ⟨hle.trans hB.1.1, hB'.2.1, hB'.2.2⟩ hne hle

theorem str_blocks_le {H C : Subgroup (LGL p V)} (hC : C ∈ blocks H) : C ≤ H := by
  obtain ⟨B, hB, rfl⟩ := hC
  exact dec_blk_le hB

theorem str_mem_sup_of_commute {G : Type*} [Group G] {P R : Subgroup G}
    (h : ∀ a ∈ P, ∀ b ∈ R, a * b = b * a) {x : G} (hx : x ∈ P ⊔ R) :
    ∃ a ∈ P, ∃ b ∈ R, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ P, ∃ b ∈ R, x = a * b}
      one_mem' := ⟨1, P.one_mem, 1, R.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', P.mul_mem ha ha', b * b', R.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← h a' ha' b hb]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, P.inv_mem ha, b⁻¹, R.inv_mem hb, ?_⟩
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
          _ = a⁻¹ * b⁻¹ := (h a⁻¹ (P.inv_mem ha) b⁻¹ (R.inv_mem hb)).symm }
  have hle : P ⊔ R ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, R.one_mem, (mul_one a).symm⟩)
      (fun b hb => ⟨1, P.one_mem, b, hb, (one_mul b).symm⟩)
  exact hle hx

end Generic

section Ker

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  {H : Subgroup (LGL p V)} {A : Subgroup (LGL p V)}

theorem str_blk_eq_blk_ker (hH : Hyp H)
    (hGen : (⨆ (B : Subgroup (LGL p V)) (_ : IsAVMin H B), B) = H) (hA : IsAVMin H A)
    {B : Subgroup (LGL p V)} (hBF : B ≤ kerOn H (commSub (blk H A))) :
    blk H B = blk (kerOn H (commSub (blk H A))) B := by
  have hFH : kerOn H (commSub (blk H A)) ≤ H := fun g hg => hg.1
  apply le_antisymm
  · refine dec_blk_le_of_normalizes (fun h hh => ?_) dec_le_blk
    have hN : H ≤ Subgroup.normalizer
        ((blk (kerOn H (commSub (blk H A))) B : Subgroup (LGL p V)) : Set (LGL p V)) := by
      refine le_trans (le_of_eq (dec_sup hH hGen hA).symm) (sup_le ?_ ?_)
      · exact dec_le_normalizer_of_commute fun e he s hs =>
          dec_commute hH hGen hA e he s (dec_blk_le_of_le hBF hs)
      · exact fun f hf => dec_mem_normalizer_blk hf
    exact hN hh
  · exact iSup₂_le fun f hf => le_iSup₂_of_le f (hFH hf) le_rfl

theorem str_hyp_ker (hH : Hyp H)
    (hGen : (⨆ (B : Subgroup (LGL p V)) (_ : IsAVMin H B), B) = H) (hA : IsAVMin H A) :
    Hyp (kerOn H (commSub (blk H A))) := by
  have hFH : kerOn H (commSub (blk H A)) ≤ H := fun g hg => hg.1
  refine ⟨?_, ?_⟩
  · have := hH.solvable
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hFH)
  · intro N hNF hN hNp
    have hNH : N ≤ H := hNF.trans hFH
    refine hH.noP N hNH ?_ hNp
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNH]
    refine le_trans (le_of_eq (dec_sup hH hGen hA).symm)
      (sup_le ?_ ((Subgroup.normal_subgroupOf_iff_le_normalizer hNF).mp hN))
    exact dec_le_normalizer_of_commute fun e he n hn => dec_commute hH hGen hA e he n (hNF hn)

theorem str_gen_ker (hH : Hyp H)
    (hGen : (⨆ (B : Subgroup (LGL p V)) (_ : IsAVMin H B), B) = H) (hA : IsAVMin H A) :
    (⨆ (B : Subgroup (LGL p V)) (_ : IsAVMin (kerOn H (commSub (blk H A))) B), B) =
      kerOn H (commSub (blk H A)) := by
  have hFH : kerOn H (commSub (blk H A)) ≤ H := fun g hg => hg.1
  apply le_antisymm
  · exact iSup₂_le fun B hB => hB.1.1
  · have hRF : (⨆ (B : Subgroup (LGL p V)) (_ : IsAVMin (kerOn H (commSub (blk H A))) B), B) ≤
        kerOn H (commSub (blk H A)) := iSup₂_le fun B hB => hB.1.1
    have hHER : H ≤ blk H A ⊔ ⨆ (B : Subgroup (LGL p V))
        (_ : IsAVMin (kerOn H (commSub (blk H A))) B), B := by
      refine le_trans (le_of_eq hGen.symm) (iSup₂_le fun B hB => ?_)
      rcases dec_avmin hH hGen hA hB with h | h
      · exact h.trans le_sup_left
      · exact (le_iSup₂ (f := fun (B : Subgroup (LGL p V))
          (_ : IsAVMin (kerOn H (commSub (blk H A))) B) => B) B
          (str_isAVMin_of_le hFH hB h)).trans le_sup_right
    intro f hf
    obtain ⟨e, he, r, hr, hfe⟩ := str_mem_sup_of_commute
      (fun e he r hr => dec_commute hH hGen hA e he r (hRF hr)) (hHER (hFH hf))
    have heF : e ∈ kerOn H (commSub (blk H A)) := by
      have : e = f * r⁻¹ := by rw [hfe]; group
      rw [this]
      exact (kerOn H (commSub (blk H A))).mul_mem hf
        ((kerOn H (commSub (blk H A))).inv_mem (hRF hr))
    have he1 : e = 1 := by
      have : e ∈ blk H A ⊓ kerOn H (commSub (blk H A)) := ⟨he, heF⟩
      rw [dec_inf hH hGen hA] at this
      exact Subgroup.mem_bot.mp this
    rw [hfe, he1, one_mul]
    exact hr

theorem str_card_lt (hH : Hyp H)
    (hGen : (⨆ (B : Subgroup (LGL p V)) (_ : IsAVMin H B), B) = H) (hA : IsAVMin H A) :
    Nat.card (kerOn H (commSub (blk H A))) < Nat.card H := by
  have hFH : kerOn H (commSub (blk H A)) ≤ H := fun g hg => hg.1
  by_contra hcon
  have hFeq : kerOn H (commSub (blk H A)) = H :=
    Subgroup.eq_of_le_of_card_ge hFH (not_lt.mp hcon)
  have hE : blk H A ≤ kerOn H (commSub (blk H A)) := by
    rw [hFeq]
    exact dec_blk_le hA
  have hEbot : blk H A = ⊥ := by
    have : blk H A ≤ blk H A ⊓ kerOn H (commSub (blk H A)) := le_inf le_rfl hE
    rw [dec_inf hH hGen hA] at this
    exact le_bot_iff.mp this
  have hcard := (dec_isBlock hH hGen hA).2.card
  rw [hEbot, Subgroup.card_bot] at hcard
  rcases (dec_isBlock hH hGen hA).1 with h | h <;> rw [h] at hcard <;> norm_num at hcard

theorem str_blocks_eq (hH : Hyp H)
    (hGen : (⨆ (B : Subgroup (LGL p V)) (_ : IsAVMin H B), B) = H) (hA : IsAVMin H A) :
    blocks H = insert (blk H A) (blocks (kerOn H (commSub (blk H A)))) := by
  have hFH : kerOn H (commSub (blk H A)) ≤ H := fun g hg => hg.1
  ext C
  constructor
  · rintro ⟨B, hB, rfl⟩
    rcases dec_avmin hH hGen hA hB with h | h
    · exact Or.inl (dec_blk_of_le hH hGen hA hB h)
    · refine Or.inr ⟨B, str_isAVMin_of_le hFH hB h, ?_⟩
      exact str_blk_eq_blk_ker hH hGen hA h
  · rintro (rfl | ⟨B, hB, rfl⟩)
    · exact ⟨A, hA, rfl⟩
    · exact ⟨B, str_isAVMin_of_isAVMin hFH hB, (str_blk_eq_blk_ker hH hGen hA hB.1.1).symm⟩

end Ker

section Indep

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem str_iSupIndep_insert {E : Subgroup (LGL p V)} {𝓕 : Set (Subgroup (LGL p V))}
    {W : Submodule (ZMod p) V} (hW : ∀ M ∈ 𝓕, commSub M ≤ W) (hEW : Disjoint (commSub E) W)
    (hE : E ∉ 𝓕) (h𝓕 : iSupIndep (fun M : 𝓕 => commSub (M : Subgroup (LGL p V)))) :
    iSupIndep (fun M : (insert E 𝓕 : Set (Subgroup (LGL p V))) =>
      commSub (M : Subgroup (LGL p V))) := by
  rw [iSupIndep_def]
  rintro ⟨M, hM⟩
  rcases hM with rfl | hM
  · refine Disjoint.mono_right ?_ hEW
    refine iSup₂_le fun j hj => ?_
    obtain ⟨N, hN⟩ := j
    rcases hN with rfl | hN
    · exact absurd rfl hj
    · exact hW N hN
  · have hi := iSupIndep_def.mp h𝓕 ⟨M, hM⟩
    have hS'W : (⨆ (j : 𝓕) (_ : j ≠ ⟨M, hM⟩), commSub (j : Subgroup (LGL p V))) ≤ W :=
      iSup₂_le fun j _ => hW j j.2
    have hle : (⨆ (j : (insert E 𝓕 : Set (Subgroup (LGL p V))))
        (_ : j ≠ ⟨M, Or.inr hM⟩), commSub (j : Subgroup (LGL p V))) ≤
        commSub E ⊔ ⨆ (j : 𝓕) (_ : j ≠ ⟨M, hM⟩), commSub (j : Subgroup (LGL p V)) := by
      refine iSup₂_le fun j hj => ?_
      obtain ⟨N, hN⟩ := j
      rcases hN with rfl | hN
      · exact le_sup_left
      · refine le_sup_of_le_right ?_
        refine le_iSup₂_of_le (⟨N, hN⟩ : 𝓕) (fun h => hj ?_) le_rfl
        have h' : N = M := congrArg Subtype.val h
        subst h'
        rfl
    refine Disjoint.mono_right hle ?_
    rw [Submodule.disjoint_def]
    intro x hxM hx
    obtain ⟨a, ha, s, hs, rfl⟩ := Submodule.mem_sup.mp hx
    have hxW : a + s ∈ W := hW M hM hxM
    have haW : a ∈ W := by
      have := W.sub_mem hxW (hS'W hs)
      simpa using this
    have ha0 : a = 0 := Submodule.disjoint_def.mp hEW a ha haW
    subst ha0
    rw [zero_add] at hxM ⊢
    exact Submodule.disjoint_def.mp hi s hxM hs

end Indep

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]

theorem structure_aux (n : ℕ) :
    ∀ H : Subgroup (LGL p V), Nat.card H = n → Hyp H →
      (⨆ (B : Subgroup (LGL p V)) (_ : IsAVMin H B), B) = H →
      (H ≠ ⊥ → p = 2 ∨ p = 3) ∧ IsBlockSystem p (blocks H) ∧
        H = ⨆ E ∈ blocks H, E := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H hn hH hGen
  by_cases hbot : H = ⊥
  · subst hbot
    rw [str_blocks_bot]
    refine ⟨fun h => absurd rfl h, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · exact fun E hE => (Set.notMem_empty E hE).elim
    · exact fun E hE => (Set.notMem_empty E hE).elim
    · exact fun E hE => (Set.notMem_empty E hE).elim
    · exact iSupIndep_def.mpr fun i => (Set.notMem_empty _ i.2).elim
    · simp
  · obtain ⟨A, hA⟩ : ∃ A, IsAVMin H A := by
      by_contra hno
      apply hbot
      rw [← hGen]
      exact iSup_eq_bot.mpr fun B => iSup_eq_bot.mpr fun hB => absurd ⟨B, hB⟩ hno
    have hFH : kerOn H (commSub (blk H A)) ≤ H := fun g hg => hg.1
    obtain ⟨-, hsysF, hjoinF⟩ := ih (Nat.card (kerOn H (commSub (blk H A))))
      (hn ▸ str_card_lt hH hGen hA) (kerOn H (commSub (blk H A))) rfl (str_hyp_ker hH hGen hA)
      (str_gen_ker hH hGen hA)
    have hblocks := str_blocks_eq hH hGen hA
    have hEmem : blk H A ∈ blocks H := ⟨A, hA, rfl⟩
    refine ⟨fun _ => (dec_isBlock hH hGen hA).1, ?_, ?_⟩
    · rw [hblocks]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro C hC
        rcases hC with rfl | hC
        · exact (dec_isBlock hH hGen hA).2
        · exact hsysF.isBlock C hC
      · intro C hC C' hC' hne g hg g' hg'
        rcases hC with rfl | hC <;> rcases hC' with rfl | hC'
        · exact absurd rfl hne
        · exact dec_commute hH hGen hA g hg g' (str_blocks_le hC' hg')
        · exact (dec_commute hH hGen hA g' hg' g (str_blocks_le hC hg)).symm
        · exact hsysF.commute C hC C' hC' hne g hg g' hg'
      · intro C hC C' hC' hne g hg w hw
        rcases hC with rfl | hC <;> rcases hC' with rfl | hC'
        · exact absurd rfl hne
        · have hw' : w ∈ fixSub (blk H A) :=
            dec_commSub_ker hH hGen hA (commSub_mono _ _ (str_blocks_le hC') hw)
          exact hw' g hg
        · exact (str_blocks_le hC hg).2 w hw
        · exact hsysF.trivial_on C hC C' hC' hne g hg w hw
      · refine str_iSupIndep_insert (W := fixSub (blk H A)) ?_ (dec_isCompl hH hGen hA).disjoint ?_
          hsysF.indep
        · exact fun M hM => (commSub_mono _ _ (str_blocks_le hM)).trans
            (dec_commSub_ker hH hGen hA)
        · intro hE
          have h1 : commSub (blk H A) ≤ fixSub (blk H A) :=
            (commSub_mono _ _ (str_blocks_le hE)).trans (dec_commSub_ker hH hGen hA)
          exact dec_ne_bot_of_card (dec_isBlock hH hGen hA).2.card_comm
            ((dec_isCompl hH hGen hA).disjoint.eq_bot_of_le h1)
    · apply le_antisymm
      · refine le_trans (le_of_eq (dec_sup hH hGen hA).symm) (sup_le ?_ ?_)
        · exact le_iSup₂ (f := fun (E : Subgroup (LGL p V)) (_ : E ∈ blocks H) => E)
            (blk H A) hEmem
        · refine le_trans (le_of_eq hjoinF) (iSup₂_le fun C hC => ?_)
          refine le_iSup₂_of_le C ?_ le_rfl
          rw [hblocks]
          exact Or.inr hC
      · exact iSup₂_le fun C hC => str_blocks_le hC

theorem structure_theorem {H : Subgroup (LGL p V)} (hH : Hyp H)
    (hS3 : (⨆ (A : Subgroup (LGL p V)) (_ : IsAV H A), A) = H) :
    (H ≠ ⊥ → p = 2 ∨ p = 3) ∧ IsBlockSystem p (blocks H) ∧ H = ⨆ E ∈ blocks H, E := by
  have hgen : (⨆ (B : Subgroup (LGL p V)) (_ : IsAVMin H B), B) = H := by
    apply le_antisymm
    · exact iSup₂_le fun B hB => hB.1.1
    · refine le_trans (le_of_eq hS3.symm) (iSup₂_le fun A hA => ?_)
      exact le_iSup_isAVMin hH hA
  exact structure_aux (Nat.card H) H rfl hH hgen

end CFSG.SignalizerFunctorTheorem.Quadratic

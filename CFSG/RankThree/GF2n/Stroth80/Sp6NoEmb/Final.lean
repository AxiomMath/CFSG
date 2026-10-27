module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.HomPat
public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Reduce
public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.HalfCase
public import CFSG.RankThree.GF2n.Stroth80.Sec84InputStmt
public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Quotient

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module Representation CFSG.Open
open scoped TensorProduct
open CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal (block)
open CFSG.QuasithinUnique.Setup.SL2Modules (frobTensor)

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}

theorem update_slotLabel_eq_threeLabel {s l : Fin 3} (h : s ≠ l) (A B : Finset ℕ) :
    Function.update (slotLabel s A) l B = threeLabel s l A B := by
  funext u
  by_cases hul : u = l
  · subst hul
    rw [Function.update_self, threeLabel, if_neg (Ne.symm h), if_pos rfl]
  · rw [Function.update_of_ne hul, threeLabel, slotLabel, if_neg hul]

theorem eq_twoLabel_of {J : Fin 3 → Finset ℕ} {l : Fin 3} {B : Finset ℕ}
    (h : ∀ k, k ≠ l → J k = B) : J = twoLabel l (J l) B := by
  funext k
  by_cases hk : k = l
  · subst hk
    rw [twoLabel, if_pos rfl]
  · rw [twoLabel, if_neg hk, h k hk]

theorem eq_slotLabel_of {J : Fin 3 → Finset ℕ} {l : Fin 3} (h : ∀ k, k ≠ l → J k = ∅) :
    J = slotLabel l (J l) := by
  funext k
  by_cases hk : k = l
  · subst hk
    rw [slotLabel_self]
  · rw [slotLabel_of_ne hk, h k hk]

@[expose] def IntertwiningMap.comp' {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] {ρ : Representation K G V}
    {σ : Representation K G W} (π : ρ.IntertwiningMap σ) (α : G' →* G) :
    Representation.IntertwiningMap (ρ.comp α) (σ.comp α) :=
  ⟨π.toLinearMap, fun g => π.isIntertwining' (α g)⟩

theorem card_of_finrank {M : Type} [AddCommGroup M] [Module K M] [FiniteDimensional K M] :
    Nat.card M = Fintype.card K ^ finrank K M := by
  classical
  haveI : Finite M := Module.finite_of_finite K
  haveI := Fintype.ofFinite M
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K)]

theorem no_embedding_core [Algebra (ZMod 2) K] (hK : Fintype.card K = 2 ^ n) (hn : 2 ≤ n)
    {N : Type} [AddCommGroup N] [Module (ZMod 2) N] [Finite N]
    {ρN : Representation (ZMod 2) (StatedSp 3 K) N} (hNirr : ρN.IsIrreducible)
    (hNcard : Nat.card N = Fintype.card K ^ 8)
    {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    {ρX : Representation K (StatedSp 3 K) X} (hXirr : ρX.IsIrreducible) (hXdim : finrank K X ≤ 8)
    (f : N →+ ((Fin 3 ⊕ Fin 3 → K) →ₗ[K] X)) (hf : ∀ g a, f (ρN g a) = linHom natRep ρX g (f a))
    (hinj : Function.Injective f) : False := by
  classical
  have hK4 : 4 ≤ Fintype.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  rcases pattern_cases hK ρX hXdim with htriv | ⟨a, ha, hconst⟩ | ⟨a, ha, z, -, hslot⟩
  ·
    have h1 := finrank_eq_one_of_trivial hXirr (trivial_of_pat_trivial hK hn htriv)
    have hfin : finrank K ((Fin 3 ⊕ Fin 3 → K) →ₗ[K] X) = 6 := by
      rw [Module.finrank_linearMap, h1, Module.finrank_fintype_fun_eq_card]
      simp
    haveI : Finite ((Fin 3 ⊕ Fin 3 → K) →ₗ[K] X) := Module.finite_of_finite K
    have hc := Nat.card_le_card_of_injective f hinj
    rw [hNcard, card_of_finrank (K := K), hfin] at hc
    have := (Nat.pow_le_pow_iff_right (by omega : 2 ≤ Fintype.card K)).mp hc
    omega
  all_goals
    obtain ⟨Yb, _, _, _, ρY, π, hYirr, hπ, hY8, hYM⟩ :=
      exists_quotient_of_embedding hK hNirr hNcard (linHom natRep ρX) f hf hinj
    have hYp : ∀ J, pat (ρY.comp block) J ≤ pat ((baseChangeRep (K := K) ρN).comp block) J :=
      fun J => pat_le_of_surjective (IntertwiningMap.comp' π block)
        (show Function.Surjective (IntertwiningMap.comp' π block) from hπ) J
    have hshift : ∀ J, IsLabel n J → pat ((baseChangeRep (K := K) ρN).comp block) (shiftL n J) =
        pat ((baseChangeRep (K := K) ρN).comp block) J :=
      fun J hJ => pat_baseChange_shift hK ρN hJ
    have hperm : ∀ J, IsLabel n J → ∀ σ : Equiv.Perm (Fin 3),
        pat ((baseChangeRep (K := K) ρN).comp block) (J ∘ σ) =
          pat ((baseChangeRep (K := K) ρN).comp block) J :=
      fun J hJ σ => pat_block_perm hK _ hJ σ
    have hsum : ∑ J ∈ labels n, pat ((baseChangeRep (K := K) ρN).comp block) J * 2 ^ lsize J =
        8 * n := by
      have h1 : finrank K (K ⊗[ZMod 2] N) = ∑ J ∈ labels n,
          pat ((baseChangeRep (K := K) ρN).comp block) J * 2 ^ lsize J :=
        finrank_eq_sum_pat hK _
      rw [← h1, Module.finrank_baseChange, finrank_zmod_eq hK hNcard]
    have hp1 : ∀ J, pat (ρY.comp block) J ≠ 0 → 1 ≤ pat ((baseChangeRep (K := K) ρN).comp block) J :=
      fun J h => (Nat.one_le_iff_ne_zero.mpr h).trans (hYp J)
    have hex : ∃ J, IsLabel n J ∧ pat (ρY.comp block) J ≠ 0 := by
      by_contra hcon
      push Not at hcon
      haveI := subsingleton_of_pat_eq_zero hK (ρY.comp block) hcon
      have : finrank K Yb = 0 := finrank_zero_of_subsingleton
      omega
  ·
    obtain ⟨J, hJ, hJne⟩ := hex
    have hM : pat ((linHom natRep ρX).comp block) J ≠ 0 := fun h => hJne (Nat.le_zero.mp (h ▸ hYM J))
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · rw [pat_linHom_natRep_of_const_zero hK hn ρX hconst hJ] at hM
      obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hM
      by_cases hk : ∀ k, k ≠ l → J k = {0}
      · rw [if_pos hk] at hl
        by_cases h1 : J l = ∅
        · rw [eq_twoLabel_of hk, h1] at hJne
          have := hp1 _ hJne
          rw [p_twoLabel_empty_zero hshift hperm hsum.le hn1 l] at this
          omega
        · rw [if_neg h1, zero_add] at hl
          by_cases h2 : J l = {1}
          · rw [eq_twoLabel_of hk, h2] at hJne
            have := hp1 _ hJne
            rw [p_twoLabel_one_zero hshift hperm hsum.le hn l] at this
            omega
          · exact hl (if_neg h2)
      · exact hl (if_neg hk)
    · rw [pat_linHom_natRep_of_const_pos hK ρX ha0 ha hconst hJ] at hM
      obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hM
      split_ifs at hl with hk
      · rw [eq_twoLabel_of hk.1, hk.2] at hJne
        have := hp1 _ hJne
        rw [p_twoLabel_pair_single hshift hperm hsum.le ha0 ha l] at this
        omega
      · exact hl rfl
  ·
    have hz : z = 0 := slot_pattern_eq_zero hK hn hXirr ha hslot
    subst hz
    have hsingle : ∀ i ∈ ({a} : Finset ℕ), i < n := singleton_lt ha
    have hsupp : ∀ J, IsLabel n J → pat (ρY.comp block) J ≠ 0 →
        ∃ l, (∀ k, k ≠ l → J k = ∅) ∧
          slPat (linHom natSL (frobTensor K K {a})) (J l) ≠ 0 := by
      intro J hJ hJne
      have hM : pat ((linHom natRep ρX).comp block) J ≠ 0 := fun h =>
        hJne (Nat.le_zero.mp (h ▸ hYM J))
      rw [pat_linHom_natRep_of_slot_eq hK ρX ha hslot hJ] at hM
      obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hM
      rw [zero_mul, zero_add] at hl
      by_cases h1 : ∃ s ∈ Finset.univ.erase l, J = Function.update (slotLabel s {a}) l {0}
      · exfalso
        obtain ⟨s, hs, rfl⟩ := h1
        have hsl : s ≠ l := Finset.ne_of_mem_erase hs
        rw [update_slotLabel_eq_threeLabel hsl] at hJne
        have := hp1 _ hJne
        rw [p_threeLabel hshift hperm hsum.le ha hsl] at this
        omega
      · push Not at h1
        rw [Finset.sum_eq_zero fun s hs => if_neg (h1 s hs), add_zero] at hl
        split_ifs at hl with hk
        · exact ⟨l, hk, hl⟩
        · exact absurd rfl hl
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    ·
      have hsupp0 : ∀ J, IsLabel n J → pat (ρY.comp block) J ≠ 0 →
          J = trivLabel ∨ ∃ l, J = slotLabel l {1} := by
        intro J hJ hJne
        obtain ⟨l, hk, hl⟩ := hsupp J hJ hJne
        rw [CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.slPat_linHom_natSL_zero hK hn (hJ l)] at hl
        by_cases h1 : J l = ∅
        · left
          rw [eq_slotLabel_of hk, h1]
          funext k
          by_cases hkl : k = l
          · subst hkl; rw [slotLabel_self]; rfl
          · rw [slotLabel_of_ne hkl]; rfl
        · rw [if_neg h1, zero_add] at hl
          by_cases h2 : J l = {1}
          · right
            exact ⟨l, by rw [eq_slotLabel_of hk, h2]⟩
          · exact absurd (if_neg h2) hl
      have hle1 : ∀ l, pat (ρY.comp block) (slotLabel l {1}) ≤ 1 := by
        intro l
        refine (hYM _).trans ?_
        rw [pat_linHom_natRep_of_slot_eq hK ρX (by omega) hslot
          (isLabel_slotLabel (singleton_lt (by omega)) l)]
        rw [Finset.sum_eq_single l]
        · rw [zero_mul, zero_add, if_pos (fun k hk => slotLabel_of_ne hk _),
            CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.slPat_linHom_natSL_zero hK hn
              (fun i hi => by rw [slotLabel_self] at hi; exact (Finset.mem_singleton.mp hi) ▸ (by omega)),
            slotLabel_self, Finset.sum_eq_zero]
          · simp
          · intro s hs
            rw [if_neg]
            intro h
            have := congrFun h l
            rw [slotLabel_self, Function.update_self] at this
            exact absurd (Finset.singleton_injective this) (by decide)
        · intro l' _ hl'
          rw [zero_mul, zero_add, if_neg, zero_add, Finset.sum_eq_zero]
          · intro s hs
            rw [if_neg]
            intro h
            have := congrFun h l'
            rw [Function.update_self, slotLabel_of_ne hl'] at this
            exact Finset.singleton_ne_empty 0 this.symm
          · intro h
            have := h l (Ne.symm hl')
            rw [slotLabel_self] at this
            exact Finset.singleton_ne_empty 1 this
        · intro h
          exact absurd (Finset.mem_univ l) h
      by_cases hall : ∀ l, pat (ρY.comp block) (slotLabel l {1}) = 0
      ·
        have htr := trivial_of_pat_trivial hK hn (ρ := ρY) fun J hJ hJt => by
          by_contra hne
          rcases hsupp0 J hJ hne with h | ⟨l, rfl⟩
          · exact hJt h
          · exact hne (hall l)
        have := finrank_eq_one_of_trivial hYirr htr
        omega
      · push Not at hall
        obtain ⟨l₀, hl₀⟩ := hall
        have h1 : ∀ l, pat (ρY.comp block) (slotLabel l {1}) = 1 := by
          intro l
          have := pat_slotLabel_eq hK ρY (show 1 < n by omega) l₀ l
          have h2 := hle1 l
          have h3 := hle1 l₀
          omega
        have hpat : ∀ J, IsLabel n J → pat (ρY.comp block) J =
            (if J = trivLabel then pat (ρY.comp block) trivLabel else 0) +
              ∑ s : Fin 3, if J = slotLabel s {1} then 1 else 0 := by
          intro J hJ
          by_cases hJt : J = trivLabel
          · subst hJt
            rw [if_pos rfl, Finset.sum_eq_zero fun s _ => if_neg
              (Ne.symm (slotLabel_ne_trivLabel (Finset.singleton_nonempty 1) s)), add_zero]
          · rw [if_neg hJt, zero_add]
            by_cases hJs : ∃ l, J = slotLabel l {1}
            · obtain ⟨l, rfl⟩ := hJs
              rw [h1 l, Finset.sum_eq_single l (fun s _ hs => if_neg fun h =>
                hs (slotLabel_inj (Finset.singleton_nonempty 1) h).symm)
                (fun h => absurd (Finset.mem_univ l) h), if_pos rfl]
            · push Not at hJs
              rw [Finset.sum_eq_zero fun s _ => if_neg (hJs s)]
              by_contra hne
              rcases hsupp0 J hJ hne with h | ⟨l, hl⟩
              · exact hJt h
              · exact hJs l hl
        have ht := slot_pattern_eq_zero hK hn hYirr (show 1 < n by omega) hpat
        have hdim := finrank_eq_sum_pat hK (ρY.comp block)
        rw [sum_labels_slot_pattern (show 1 < n by omega) _ hpat, ht] at hdim
        simp [trivLabel, slotLabel, Fin.sum_univ_three] at hdim
        omega
    ·
      have hsuppa : ∀ J, IsLabel n J → pat (ρY.comp block) J ≠ 0 → ∃ l, J = slotLabel l {0, a} := by
        intro J hJ hJne
        obtain ⟨l, hk, hl⟩ := hsupp J hJ hJne
        rw [slPat_linHom_natSL_single hK ha0 ha (hJ l)] at hl
        split_ifs at hl with h1
        · exact ⟨l, by rw [eq_slotLabel_of hk, h1]⟩
        · exact absurd rfl hl
      by_cases h2a : 2 * a = n
      ·
        obtain ⟨J, hJ, hJne⟩ := hex
        obtain ⟨l, rfl⟩ := hsuppa J hJ hJne
        let U₀ := kerSubG π
        have hU₀ : U₀.toSubmodule ≠ ⊤ := by
          intro h
          have hne := ((CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff _).mp hYirr).1
          obtain ⟨y, hy⟩ := exists_ne (0 : Yb)
          obtain ⟨x, rfl⟩ := hπ y
          have : x ∈ U₀.toSubmodule := h ▸ Submodule.mem_top
          exact hy this
        have hW := (Representation.irreducible_iff_isSimpleModule_asModule ρN).mp hNirr
        refine half_case_false h2a.symm ha0 (pat ((baseChangeRep (K := K) ρN).comp block))
          (pat (ρY.comp block)) hshift hperm hsum (fun J hJ => ?_) hsuppa ⟨l, hp1 _ hJne⟩
        have h := pat_le_sum_frobIter hK hn1 ρN hW U₀ hU₀ hJ
        refine h.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
        exact pat_congr (equivComp (equivQuotKerG π hπ) block) _
      · obtain ⟨J, hJ, hJne⟩ := hex
        obtain ⟨l, rfl⟩ := hsuppa J hJ hJne
        have := hp1 _ hJne
        rw [p_slotLabel_pair hshift hperm hsum.le ha0 ha h2a l] at this
        omega

theorem sp6NoEmbedding_holds : Sp6NoEmbeddingStatement := by
  unfold Sp6NoEmbeddingStatement
  intro K _ _ _ hK4 N _ _ _ hNcard _ hNirr X _ _ _ _ hXlin hXdim f hf hinj
  classical
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Fintype.card K = 2 ^ (n : ℕ) := hn
  have hn2 : 2 ≤ (n : ℕ) := by
    have h4 : 4 ≤ 2 ^ (n : ℕ) := by rw [← hK, ← Nat.card_eq_fintype_card]; exact hK4
    by_contra h
    push Not at h
    interval_cases h' : (n : ℕ) <;> simp_all
  have h2 : ∀ a : N, (2 : ℕ) • a = 0 := by
    intro a
    apply hinj
    rw [map_nsmul, map_zero, two_nsmul, ← two_smul K (f a), CharTwo.two_eq_zero, zero_smul]
  letI : Module (ZMod 2) N := AddCommGroup.zmodModule h2
  let ρN : Representation (ZMod 2) (StatedSp 3 K) N :=
    { toFun := fun g => (DistribSMul.toAddMonoidHom N g).toZModLinearMap 2
      map_one' := LinearMap.ext fun a => one_smul _ a
      map_mul' := fun g h => LinearMap.ext fun a => mul_smul g h a }
  let ρX : Representation K (StatedSp 3 K) X :=
    { toFun := fun g =>
        { toFun := fun x => g • x
          map_add' := smul_add g
          map_smul' := hXlin g }
      map_one' := LinearMap.ext fun x => one_smul _ x
      map_mul' := fun g h => LinearMap.ext fun x => mul_smul g h x }
  have hNnt : Nontrivial N := by
    rw [← Finite.one_lt_card_iff_nontrivial, hNcard]
    calc 1 < 2 := by norm_num
      _ ≤ Nat.card K := by omega
      _ ≤ Nat.card K ^ 8 := Nat.le_self_pow (by norm_num) _
  have hNirr' : ρN.IsIrreducible := by
    rw [CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff]
    refine ⟨hNnt, fun U hU => ?_⟩
    rcases hNirr U.toAddSubgroup (fun g a ha => hU g a ha) with h | h
    · exact Or.inl (Submodule.toAddSubgroup_injective (h.trans Submodule.bot_toAddSubgroup.symm))
    · exact Or.inr (Submodule.toAddSubgroup_injective (h.trans Submodule.top_toAddSubgroup.symm))
  have hf' : ∀ g a, f (ρN g a) = linHom natRep ρX g (f a) := by
    intro g a
    refine LinearMap.ext fun v => ?_
    rw [linHom_apply, LinearMap.comp_apply, LinearMap.comp_apply, natRep_apply]
    exact hf g a v
  obtain ⟨Z, _, _, _, ρZ, hZirr, hZdim, f', hf'', hinj'⟩ :=
    exists_irreducible_target hNirr' natRep ρX f hf' hinj
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  exact no_embedding_core hK hn2 hNirr' (by rw [hNcard, Nat.card_eq_fintype_card]) hZirr
    (hZdim.trans hXdim.le) f' hf'' hinj'

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

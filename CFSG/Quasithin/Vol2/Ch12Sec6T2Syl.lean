module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N
open scoped IsMulCommutative Pointwise

namespace S126T2

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

@[expose] def pairs : Finset (Fin 8 × Fin 8) := Finset.univ.filter fun p => p.1 < p.2

theorem card_pairs : pairs.card = 28 := by
  decide

theorem pair_trans {a b c d e f : Fin 8} (h1 : (c = a ∧ d = b) ∨ (c = b ∧ d = a))
    (h2 : (e = c ∧ f = d) ∨ (e = d ∧ f = c)) : (e = a ∧ f = b) ∨ (e = b ∧ f = a) := by
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem pair_symm {a b c d : Fin 8} (h : (c = a ∧ d = b) ∨ (c = b ∧ d = a)) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem pair_sort (a b : Fin 8) (h : a ≠ b) :
    ∃ p ∈ pairs, (p.1 = a ∧ p.2 = b) ∨ (p.1 = b ∧ p.2 = a) := by
  rcases lt_or_gt_of_ne h with h | h
  · exact ⟨(a, b), by simp [pairs, h], Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨(b, a), by simp [pairs, h], Or.inr ⟨rfl, rfl⟩⟩

theorem relIndex_C (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {W : Subgroup G} (hLW : L ≤ W)
    (hW : W ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) :
    (W ⊓ Gv v).relIndex W = 28 := by
  classical
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hLTL : W ≤ Subgroup.normalizer (L : Set G) := hW.trans inf_le_left
  have hLTV : W ≤ Subgroup.normalizer (V : Set G) := hW.trans inf_le_right
  let _ : MulAction ↥W G :=
    MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp W.subtype)
  have hsmul : ∀ (t : ↥W) (x : G), t • x = (t : G) * x * (t : G)⁻¹ := fun t x => rfl
  have hstab : MulAction.stabilizer ↥W v = (Gv v).subgroupOf W := by
    ext t
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, Gv,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc (t : G) * v = t * v * (t : G)⁻¹ * t := by group
        _ = v * t := by rw [h]
    · intro h
      rw [h, mul_inv_cancel_right]
  have hrel : (W ⊓ Gv v).relIndex W = (MulAction.orbit ↥W v).ncard := by
    rw [← MulAction.index_stabilizer, hstab, Subgroup.relIndex, Subgroup.inf_subgroupOf_left]
  rw [hrel]
  have hex : ∀ p : Fin 8 × Fin 8, ∃ l : G, l ∈ L ∧ (p.1 ≠ p.2 → ∃ σ : Equiv.Perm (Fin 8),
      ActsAs F l σ ∧ ((σ 0 = p.1 ∧ σ 1 = p.2) ∨ (σ 0 = p.2 ∧ σ 1 = p.1))) := by
    intro p
    by_cases hp : p.1 ≠ p.2
    · have hy : HasWt 2 (QuotientGroup.mk (pe 0 1) : D8) :=
        ⟨pe 0 1, rfl, S126L20a.wt_pe (by decide)⟩
      have hy' : HasWt 2 (QuotientGroup.mk (pe p.1 p.2) : D8) :=
        ⟨pe p.1 p.2, rfl, S126L20a.wt_pe hp⟩
      obtain ⟨σ, hσ⟩ := exists_dAct (by norm_num) hy hy'
      obtain ⟨l, hl⟩ := S126L19a.psi_surjective F hH σ
      refine ⟨l, l.2, fun _ => ⟨σ, hl ▸ S126L19a.actsAs_psi F hH l, ?_⟩⟩
      rw [S126L20a.dAct_pe] at hσ
      have h01 : (σ : Equiv.Perm (Fin 8)) 0 ≠ (σ : Equiv.Perm (Fin 8)) 1 :=
        fun e => absurd ((σ : Equiv.Perm (Fin 8)).injective e) (by decide)
      rcases mk_pe_eq_mk_pe h01 hσ with h | h
      · exact Or.inl ⟨h.1.symm, h.2.symm⟩
      · exact Or.inr ⟨h.2.symm, h.1.symm⟩
    · exact ⟨1, L.one_mem, fun h => absurd h hp⟩
  choose l hlL hlσ using hex
  set f : Fin 8 × Fin 8 → G := fun p => l p * v * (l p)⁻¹ with hf
  have hval : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (V : Set G)) (σ : Equiv.Perm (Fin 8)),
      ActsAs F x σ → F.β ⟨x * v * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx v).1 hv⟩ =
        QuotientGroup.mk (pe (σ 0) (σ 1)) := by
    intro x hx σ hσ
    rw [hσ ⟨v, hv⟩ _ rfl, hβ, S126L20a.dAct_pe]
  have himage : MulAction.orbit ↥W v = f '' (pairs : Set (Fin 8 × Fin 8)) := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨τ, hτ⟩ := exists_actsAs F hH (hLTL x.2) (hLTV x.2)
      have hτ01 : τ 0 ≠ τ 1 := fun e => absurd (τ.injective e) (by decide)
      obtain ⟨p, hp, hpe⟩ := pair_sort (τ 0) (τ 1) hτ01
      have hp12 : p.1 ≠ p.2 := by
        rcases hpe with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hτ01
        · rw [h1, h2]; exact hτ01.symm
      obtain ⟨σ, hσ, hσp⟩ := hlσ p hp12
      refine ⟨p, hp, ?_⟩
      change l p * v * (l p)⁻¹ = (x : G) * v * (x : G)⁻¹
      have hlN := hLV (hlL p)
      have hmul : ActsAs F ((l p)⁻¹ * x) (σ⁻¹ * τ) := hσ.inv.mul hτ (hLTV x.2)
      have hfix : ((σ⁻¹ * τ) 0 = 0 ∧ (σ⁻¹ * τ) 1 = 1) ∨ ((σ⁻¹ * τ) 0 = 1 ∧ (σ⁻¹ * τ) 1 = 0) := by
        simp only [Equiv.Perm.mul_apply]
        rw [Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.inv_eq_iff_eq,
          Equiv.Perm.inv_eq_iff_eq]
        rcases hσp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hpe with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inl ⟨by rw [h1, h3], by rw [h2, h4]⟩
        · exact Or.inr ⟨by rw [h2, h4], by rw [h1, h3]⟩
        · exact Or.inr ⟨by rw [h2, h3], by rw [h1, h4]⟩
        · exact Or.inl ⟨by rw [h1, h4], by rw [h2, h3]⟩
      have hmem := (mem_Gv_iff h1222 F hH hv hβ (Subgroup.mul_mem _ (Subgroup.inv_mem _
        (hLTL (hLW (hlL p)))) (hLTL x.2)) (Subgroup.mul_mem _
        (Subgroup.inv_mem _ hlN) (hLTV x.2)) hmul).2 hfix
      rw [Gv, Subgroup.mem_centralizer_singleton_iff] at hmem
      calc l p * v * (l p)⁻¹ = l p * (v * ((l p)⁻¹ * x)) * (x : G)⁻¹ := by group
        _ = l p * (((l p)⁻¹ * x) * v) * (x : G)⁻¹ := by rw [hmem]
        _ = (x : G) * v * (x : G)⁻¹ := by group
    · rintro ⟨p, -, rfl⟩
      exact ⟨⟨l p, hLW (hlL p)⟩, rfl⟩
  have hinj : Set.InjOn f (pairs : Set (Fin 8 × Fin 8)) := by
    intro p hp q hq hpq
    have hp' : p.1 < p.2 := (Finset.mem_filter.1 hp).2
    have hq' : q.1 < q.2 := (Finset.mem_filter.1 hq).2
    obtain ⟨σ, hσ, hσp⟩ := hlσ p hp'.ne
    obtain ⟨σ', hσ', hσq⟩ := hlσ q hq'.ne
    have h1 := hval _ (hLV (hlL p)) σ hσ
    have h2 := hval _ (hLV (hlL q)) σ' hσ'
    have h3 : F.β ⟨l p * v * (l p)⁻¹, (Subgroup.mem_normalizer_iff.1 (hLV (hlL p)) v).1 hv⟩ =
        F.β ⟨l q * v * (l q)⁻¹, (Subgroup.mem_normalizer_iff.1 (hLV (hlL q)) v).1 hv⟩ := by
      congr 1
      exact Subtype.ext hpq
    rw [h1, h2] at h3
    have hσ01 : σ 0 ≠ σ 1 := fun e => absurd (σ.injective e) (by decide)
    have key := mk_pe_eq_mk_pe hσ01 h3
    rcases pair_trans (pair_trans hσp key) (pair_symm hσq) with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Prod.ext e1.symm e2.symm
    · exfalso
      rw [e1, e2] at hq'
      exact lt_asymm hp' hq'
  rw [himage, hinj.ncard_image, Set.ncard_coe_finset, card_pairs]

theorem isSylowTwoOf_Tv_of_le (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {W : Subgroup G}
    (hLW : L ⊔ T ≤ W)
    (hW : W ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) :
    CFSG.QuasithinUnique.IsSylowTwoOf (Tv T v) (W ⊓ Gv v) := by
  have hTW : T ≤ W := le_sup_right.trans hLW
  have hTvH : Tv T v ≤ W ⊓ Gv v := inf_le_inf_right _ hTW
  refine ⟨hTvH, hH.hyp.sylow.1.to_le inf_le_left, ?_⟩
  have hT := isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow hTW
  have h1 := Subgroup.relIndex_mul_relIndex (Tv T v) (W ⊓ Gv v) W hTvH inf_le_left
  have h2 := Subgroup.relIndex_mul_relIndex (Tv T v) T W inf_le_left hTW
  rw [relIndex_C h1222 F hH hv hβ (le_sup_left.trans hLW) hW] at h1
  rw [relIndex_Tv h1222 F hH hv hβ] at h2
  have hodd : ¬ 2 ∣ T.relIndex W := hT.2.2
  change ¬ 2 ∣ (Tv T v).relIndex (W ⊓ Gv v)
  omega

theorem isSylowTwoOf_Tv (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    CFSG.QuasithinUnique.IsSylowTwoOf (Tv T v) ((L ⊔ T) ⊓ Gv v) :=
  isSylowTwoOf_Tv_of_le h1222 F hH hv hβ le_rfl
    (le_inf (sup_le Subgroup.le_normalizer hH.hyp.normalizes)
      (sup_le hH.hyp.irrPlus.2.2.1 (S126L19b.T_le_normalizer_V h1222 hH)))

omit [Finite G] in
theorem two_pow_mem_of_mem_sup {L T : Subgroup G} (hT : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {c : G} (hc : c ∈ L ⊔ T) :
    ∃ k : ℕ, c ^ 2 ^ k ∈ L := by
  have hc' : c ∈ (L : Set G) * (T : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTL]
    exact hc
  obtain ⟨l, hl, t, ht, rfl⟩ := hc'
  have key : ∀ m : ℕ, ∃ l' ∈ L, (l * t) ^ m = l' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ m ih =>
      obtain ⟨l', hl', h⟩ := ih
      refine ⟨l' * (t ^ m * l * (t ^ m)⁻¹), mul_mem hl' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hTL (pow_mem ht m)) l).1 hl
      · rw [pow_succ, h]
        group
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨l', hl', h⟩ := key (2 ^ k)
  exact ⟨k, by rw [h, htk, mul_one]; exact hl'⟩

omit [IsMulCommutative ↥V] in
theorem isPGroup_CLT_V (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
  have hT2 : IsPGroup 2 T := hH.hyp.sylow.1
  have hCL := S126L19a.isPGroup_ker h1222 hH
  intro c
  obtain ⟨k, hk⟩ := two_pow_mem_of_mem_sup hT2 hH.hyp.normalizes c.2.1
  obtain ⟨m, hm⟩ := hCL ⟨⟨_, hk⟩, Subgroup.pow_mem _ c.2.2 _⟩
  have hm' : ((c : G) ^ 2 ^ k) ^ 2 ^ m = 1 := by
    have := congrArg (fun z : ↥((Subgroup.centralizer (V : Set G)).subgroupOf L) =>
      ((z : ↥L) : G)) hm
    simpa using this
  refine ⟨k + m, Subtype.ext ?_⟩
  rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, hm']

end S126T2

end CFSG.Quasithin.H13

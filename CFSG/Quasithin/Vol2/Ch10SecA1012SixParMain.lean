module

public import CFSG.Quasithin.Vol2.Ch10SecA1012SixPar
public import CFSG.Quasithin.Vol2.Ch10SecA1012SixParAux
public import CFSG.Quasithin.Vol2.Ch10SecASL2OverQ

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem le_normalizer_T0_of_ne (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I)
    (hSL : ∃ (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ), 2 ≤ n ∧ Nat.card K = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K))
    {X : Subgroup G} (hTX : T ≤ X) (hX : X ≤ fsuL0 T L ⊔ T) (hne : X ≠ fsuL0 T L ⊔ T) :
    X ≤ Subgroup.normalizer (T0 T L : Set G) := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hyp.not_normal h
  obtain ⟨K, _, _, n, hn, hK, ⟨eL⟩⟩ := hSL
  have hloc := hyp.fsu.maximal.1
  have hT := hyp.fsu.sylow
  obtain ⟨φ, hφs, hφk, hφL, hφLt⟩ := exists_fsuL0_prod h37 h38 hyp ht htn
  have hsL := isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian
    hyp.fsu.qtke hyp.fsu.faithful hyp.not_normal
  have hsLt := isSimpleGroup_conjugate h37 h38 hyp ht htn
  have hker : φ.ker ≤ (T0 T L).subgroupOf (fsuL0 T L) := by
    rw [hφk]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact pCoreOf_fsuL0_le_T0 hT hx
  set Y := ((X ⊓ fsuL0 T L).subgroupOf (fsuL0 T L)).map φ with hYdef
  set S₁ := ((T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) with hS₁
  set S₂ := ((T ⊓ CFSG.conjugate L t).subgroupOf (CFSG.conjugate L t)).map
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(CFSG.conjugate L t))) with hS₂
  have hL0syl : IsSylowTwoOf (T0 T L) (fsuL0 T L) :=
    B6.isSylowTwoOf_inf_normal ⟨le_sup_right, hloc.1, hloc.2.2.1⟩ (fsuL0_le_sup T L)
      (sup_le ((le_fsuL0 T L).trans Subgroup.le_normalizer) (le_fsuM T L))
  have hsyl₁ : IsSylowTwoOf S₁ ⊤ :=
    isSylowTwoOf_map_of_surjective (isSylowTwoOf_inf hloc) _ (QuotientGroup.mk'_surjective _)
  have hTLt : IsSylowTwoOf (T ⊓ CFSG.conjugate L t) (CFSG.conjugate L t) := by
    have h := B6.isSylowTwoOf_inf_normal hL0syl (conjugate_le_fsuL0 ht)
      (fsuL0_le_normalizer_conjugate hloc (le_fsuM T L ht))
    rwa [inf_assoc, inf_eq_right.mpr (conjugate_le_fsuL0 ht)] at h
  have hsyl₂ : IsSylowTwoOf S₂ ⊤ :=
    isSylowTwoOf_map_of_surjective hTLt _ (QuotientGroup.mk'_surjective _)
  have hφT0 : ((T0 T L).subgroupOf (fsuL0 T L)).map φ = S₁.prod S₂ := by
    refine (eq_of_isSylowTwoOf_le ?_ ?_ ?_).symm
    · refine ⟨le_top, ?_, ?_⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩⟩
        obtain ⟨i, hi⟩ := hsyl₁.2.1 ⟨a, ha⟩
        obtain ⟨j, hj⟩ := hsyl₂.2.1 ⟨b, hb⟩
        refine ⟨i + j, Subtype.ext (Prod.ext ?_ ?_)⟩
        · have h1 : a ^ 2 ^ i = 1 := by simpa using congrArg Subtype.val hi
          simp [pow_add, pow_mul, h1]
        · have h2 : b ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
          simp [pow_add, pow_mul', h2]
      · rw [show ((S₁.prod S₂).subgroupOf ⊤).index = (S₁.prod S₂).index from
          Subgroup.relIndex_top_right _, Subgroup.index_prod]
        have h1 := hsyl₁.2.2
        have h2 := hsyl₂.2.2
        rw [show (S₁.subgroupOf ⊤).index = S₁.index from Subgroup.relIndex_top_right _] at h1
        rw [show (S₂.subgroupOf ⊤).index = S₂.index from Subgroup.relIndex_top_right _] at h2
        exact fun h => ((Nat.Prime.dvd_mul Nat.prime_two).mp h).elim h1 h2
    · exact (hL0syl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hL0syl.1).symm).map φ
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      obtain ⟨⟨s, hs⟩, hsT, rfl⟩ := ha
      obtain ⟨⟨s', hs'⟩, hs'T, rfl⟩ := hb
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hsT hs'T
      have hm1 : φ ⟨s, le_fsuL0 T L hs⟩ ∈ ((T0 T L).subgroupOf (fsuL0 T L)).map φ :=
        ⟨⟨s, le_fsuL0 T L hs⟩, Subgroup.mem_subgroupOf.mpr ⟨hsT.1, le_fsuL0 T L hs⟩, rfl⟩
      have hm2 : φ ⟨s', conjugate_le_fsuL0 ht hs'⟩ ∈ ((T0 T L).subgroupOf (fsuL0 T L)).map φ :=
        ⟨⟨s', conjugate_le_fsuL0 ht hs'⟩,
          Subgroup.mem_subgroupOf.mpr ⟨hs'T.1, conjugate_le_fsuL0 ht hs'⟩, rfl⟩
      convert Subgroup.mul_mem _ hm1 hm2 using 1
      rw [hφL s hs, hφLt s' hs']
      simp
  have hT0X : T0 T L ≤ X ⊓ fsuL0 T L := inf_le_inf_right _ hTX
  have hS₁Y : S₁ ≤ Y.map (MonoidHom.fst _ _) := by
    intro a ha
    have : (a, 1) ∈ Y := by
      have h := (Subgroup.mem_prod.mpr ⟨ha, Subgroup.one_mem S₂⟩ : (a, 1) ∈ S₁.prod S₂)
      rw [← hφT0] at h
      obtain ⟨y, hy, hye⟩ := h
      exact ⟨y, (Subgroup.mem_subgroupOf.mpr (hT0X (Subgroup.mem_subgroupOf.mp hy))), hye⟩
    exact ⟨_, this, rfl⟩
  have hS₂Y : S₂ ≤ Y.map (MonoidHom.snd _ _) := by
    intro b hb
    have : (1, b) ∈ Y := by
      have h := (Subgroup.mem_prod.mpr ⟨Subgroup.one_mem S₁, hb⟩ : (1, b) ∈ S₁.prod S₂)
      rw [← hφT0] at h
      obtain ⟨y, hy, hye⟩ := h
      exact ⟨y, (Subgroup.mem_subgroupOf.mpr (hT0X (Subgroup.mem_subgroupOf.mp hy))), hye⟩
    exact ⟨_, this, rfl⟩
  have lift : ∀ x : ↥(fsuL0 T L), φ x ∈ Y → (x : G) ∈ X := by
    intro x hx
    obtain ⟨y, hy, hye⟩ := hx
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
    have hk : y⁻¹ * x ∈ φ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hye, inv_mul_cancel]
    have h1 := hker hk
    rw [Subgroup.mem_subgroupOf] at h1
    have := X.mul_mem hy.1 (hTX h1.1)
    simpa using this
  have hcard₁ : 1 < Nat.card S₁ := by
    have hQ : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ n * (4 ^ n - 1) := by
      rw [Nat.card_congr eL.toEquiv, card_SL_two_pow hK]
    rw [card_eq_of_isSylowTwoOf_top hsyl₁ (odd_four_pow_sub_one (by omega)) hQ]
    exact Nat.one_lt_two_pow (by omega)
  have hcard₂ : 1 < Nat.card S₂ := by
    have hQ : Nat.card (↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t)) =
        2 ^ n * (4 ^ n - 1) := by
      rw [Nat.card_congr ((quotConjEquiv L t).trans eL).toEquiv, card_SL_two_pow hK]
    rw [card_eq_of_isSylowTwoOf_top hsyl₂ (odd_four_pow_sub_one (by omega)) hQ]
    exact Nat.one_lt_two_pow (by omega)
  have hπ₁ : Y.map (MonoidHom.fst _ _) ≤ Subgroup.normalizer (S₁ : Set _) := by
    rcases le_normalizer_or_eq_top_of_mulEquiv hn hK eL hsyl₁ hS₁Y with h | h
    · exact h
    · exfalso
      apply hne
      refine eq_of_le_of_le_sup h37 h38 hyp ht htn hTX hX (Or.inl fun l hl => ?_)
      have hN := normal_comap_inl h
      have hY1 : Y.comap (MonoidHom.inl _ _) = ⊤ := by
        rcases hsL.eq_bot_or_eq_top_of_normal (Y.comap (MonoidHom.inl _ _)) with h1 | h1
        · exfalso
          refine (Subgroup.one_lt_card_iff_ne_bot S₁).mp hcard₁ (le_bot_iff.mp fun a ha => ?_)
          rw [← h1, Subgroup.mem_comap]
          have h2 := (Subgroup.mem_prod.mpr ⟨ha, Subgroup.one_mem S₂⟩ : (a, 1) ∈ S₁.prod S₂)
          rw [← hφT0] at h2
          obtain ⟨y, hy, hye⟩ := h2
          exact ⟨y, Subgroup.mem_subgroupOf.mpr (hT0X (Subgroup.mem_subgroupOf.mp hy)), hye⟩
        · exact h1
      have h2 : ((⟨l, hl⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ Y.comap (MonoidHom.inl _ _) :=
        hY1 ▸ Subgroup.mem_top _
      rw [Subgroup.mem_comap] at h2
      exact lift ⟨l, le_fsuL0 T L hl⟩ (by rw [hφL l hl]; exact h2)
  have hπ₂ : Y.map (MonoidHom.snd _ _) ≤ Subgroup.normalizer (S₂ : Set _) := by
    rcases le_normalizer_or_eq_top_of_mulEquiv hn hK ((quotConjEquiv L t).trans eL) hsyl₂ hS₂Y
      with h | h
    · exact h
    · exfalso
      apply hne
      refine eq_of_le_of_le_sup h37 h38 hyp ht htn hTX hX (Or.inr fun l hl => ?_)
      have hN := normal_comap_inr h
      have hY2 : Y.comap (MonoidHom.inr _ _) = ⊤ := by
        rcases hsLt.eq_bot_or_eq_top_of_normal (Y.comap (MonoidHom.inr _ _)) with h1 | h1
        · exfalso
          refine (Subgroup.one_lt_card_iff_ne_bot S₂).mp hcard₂ (le_bot_iff.mp fun b hb => ?_)
          rw [← h1, Subgroup.mem_comap]
          have h2 := (Subgroup.mem_prod.mpr ⟨Subgroup.one_mem S₁, hb⟩ : (1, b) ∈ S₁.prod S₂)
          rw [← hφT0] at h2
          obtain ⟨y, hy, hye⟩ := h2
          exact ⟨y, Subgroup.mem_subgroupOf.mpr (hT0X (Subgroup.mem_subgroupOf.mp hy)), hye⟩
        · exact h1
      have h2 : ((⟨l, hl⟩ : ↥(CFSG.conjugate L t)) :
          ↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t)) ∈
          Y.comap (MonoidHom.inr _ _) := hY2 ▸ Subgroup.mem_top _
      rw [Subgroup.mem_comap] at h2
      exact lift ⟨l, conjugate_le_fsuL0 ht hl⟩ (by rw [hφLt l hl]; exact h2)
  have hY : ∀ x : ↥(fsuL0 T L), (x : G) ∈ X →
      (x : G) ∈ Subgroup.normalizer (T0 T L : Set G) := by
    intro x hx
    have hxY : φ x ∈ Y := ⟨x, Subgroup.mem_subgroupOf.mpr ⟨hx, x.2⟩, rfl⟩
    refine mem_normalizer_of_map inf_le_right φ hker ?_
    rw [hφT0]
    exact mem_normalizer_prod (hπ₁ ⟨_, hxY, rfl⟩) (hπ₂ ⟨_, hxY, rfl⟩)
  intro x hx
  have hx' : x ∈ ((fsuL0 T L ⊔ T : Subgroup G) : Set G) := hX hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (le_fsuM T L)] at hx'
  obtain ⟨l, hl, s, hs, rfl⟩ := Set.mem_mul.mp hx'
  have hlX : l ∈ X := by simpa using X.mul_mem hx (X.inv_mem (hTX hs))
  have hsN : s ∈ Subgroup.normalizer (T0 T L : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, le_fsuM T L hs⟩
  exact Subgroup.mul_mem _ (hY ⟨l, hl⟩ hlX) hsN

end CFSG.Quasithin.Vol2.Ch10.SecA

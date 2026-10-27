module

public import CFSG.Quasithin.Vol2.Ch9Sec2SL
public import CFSG.Quasithin.Vol2.Ch10SecA1012SixPar
public import CFSG.Quasithin.Vol2.Ch10SecA1012SixParAux
public import CFSG.Quasithin.Vol2.Ch10SecASL2OverQ

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Vol2.Ch10.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem eq_of_le_of_le_sup_of_fsu (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {X : Subgroup G} (hTX : T ≤ X)
    (hX : X ≤ fsuL0 T L ⊔ T) (hL : L ≤ X ∨ CFSG.conjugate L t ≤ X) : X = fsuL0 T L ⊔ T := by
  have htX := hTX ht
  have hL' : L ≤ X := by
    rcases hL with h | h
    · exact h
    · intro l hl
      have h1 : t⁻¹ * l * t ∈ CFSG.conjugate L t := by
        rw [Vol2.Ch10.SecA.mem_conjugate_iff]
        simpa [mul_assoc] using hl
      have := X.mul_mem (X.mul_mem htX (h h1)) (X.inv_mem htX)
      simpa [mul_assoc] using this
  refine le_antisymm hX (sup_le ?_ hTX)
  rw [fsuL0_eq_sup_of_fsu h37 h38 hfsu hnn ht htn]
  refine sup_le hL' fun y hy => ?_
  rw [Vol2.Ch10.SecA.mem_conjugate_iff] at hy
  have := X.mul_mem (X.mul_mem (X.inv_mem htX) (hL' hy)) htX
  simpa [mul_assoc] using this

theorem le_normalizer_T0_of_ne_of_fsu
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G))
    (hSL : ∃ (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ), 2 ≤ n ∧ Nat.card K = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K))
    {X : Subgroup G} (hTX : T ≤ X) (hX : X ≤ fsuL0 T L ⊔ T) (hne : X ≠ fsuL0 T L ⊔ T) :
    X ≤ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hnn h
  obtain ⟨K, _, _, n, hn, hK, ⟨eL⟩⟩ := hSL
  have hloc := hfsu.maximal.1
  have hT := hfsu.sylow
  obtain ⟨φ, hφs, hφk, hφL, hφLt⟩ := exists_fsuL0_prod_of_fsu h37 h38 hfsu hnn ht htn
  have hsL := isSimpleGroup_of_not_normal h37 h38 hfsu.simple hfsu.nonabelian
    hfsu.qtke hfsu.faithful hnn
  have hsLt := isSimpleGroup_conjugate_of_fsu h37 h38 hfsu hnn ht htn
  have hker : φ.ker ≤ (T ⊓ fsuL0 T L).subgroupOf (fsuL0 T L) := by
    rw [hφk]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact pCoreOf_fsuL0_le_T0 hT hx
  set Y := ((X ⊓ fsuL0 T L).subgroupOf (fsuL0 T L)).map φ with hYdef
  set S₁ := ((T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) with hS₁
  set S₂ := ((T ⊓ CFSG.conjugate L t).subgroupOf (CFSG.conjugate L t)).map
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(CFSG.conjugate L t))) with hS₂
  have hL0syl : IsSylowTwoOf (T ⊓ fsuL0 T L) (fsuL0 T L) :=
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
  have hφT0 : ((T ⊓ fsuL0 T L).subgroupOf (fsuL0 T L)).map φ = S₁.prod S₂ := by
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
      have hm1 : φ ⟨s, le_fsuL0 T L hs⟩ ∈ ((T ⊓ fsuL0 T L).subgroupOf (fsuL0 T L)).map φ :=
        ⟨⟨s, le_fsuL0 T L hs⟩, Subgroup.mem_subgroupOf.mpr ⟨hsT.1, le_fsuL0 T L hs⟩, rfl⟩
      have hm2 : φ ⟨s', conjugate_le_fsuL0 ht hs'⟩ ∈
          ((T ⊓ fsuL0 T L).subgroupOf (fsuL0 T L)).map φ :=
        ⟨⟨s', conjugate_le_fsuL0 ht hs'⟩,
          Subgroup.mem_subgroupOf.mpr ⟨hs'T.1, conjugate_le_fsuL0 ht hs'⟩, rfl⟩
      convert Subgroup.mul_mem _ hm1 hm2 using 1
      rw [hφL s hs, hφLt s' hs']
      simp
  have hT0X : T ⊓ fsuL0 T L ≤ X ⊓ fsuL0 T L := inf_le_inf_right _ hTX
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
      refine eq_of_le_of_le_sup_of_fsu h37 h38 hfsu hnn ht htn hTX hX (Or.inl fun l hl => ?_)
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
      refine eq_of_le_of_le_sup_of_fsu h37 h38 hfsu hnn ht htn hTX hX (Or.inr fun l hl => ?_)
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
      (x : G) ∈ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) := by
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
  have hsN : s ∈ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, le_fsuM T L hs⟩
  exact Subgroup.mul_mem _ (hY ⟨l, hl⟩ hlX) hsN

theorem not_le_normalizer_T0_of_fsu
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G))
    (hSL : ∃ (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ), 2 ≤ n ∧ Nat.card K = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K)) :
    ¬ fsuL0 T L ≤ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) := by
  intro hN
  obtain ⟨K, _, _, n, hn, hK, ⟨eL⟩⟩ := hSL
  have hloc := hfsu.maximal.1
  have hsL := isSimpleGroup_of_not_normal h37 h38 hfsu.simple hfsu.nonabelian
    hfsu.qtke hfsu.faithful hnn
  have hsyl₁ := isSylowTwoOf_map_of_surjective (isSylowTwoOf_inf hloc)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (QuotientGroup.mk'_surjective _)
  have hQ : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ n * (4 ^ n - 1) := by
    rw [Nat.card_congr eL.toEquiv, card_SL_two_pow hK]
  have hc := card_eq_of_isSylowTwoOf_top hsyl₁ (odd_four_pow_sub_one (by omega)) hQ
  have hnorm : ((T ⊓ L).subgroupOf L).Normal := by
    refine ⟨fun s hs l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    have h1 := (Subgroup.mem_normalizer_iff.mp (hN (le_fsuL0 T L l.2)) s).mp
      ⟨hs.1, le_fsuL0 T L hs.2⟩
    exact ⟨h1.1, L.mul_mem (L.mul_mem l.2 hs.2) (L.inv_mem l.2)⟩
  have hnorm' := hnorm.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (QuotientGroup.mk'_surjective _)
  rcases hsL.eq_bot_or_eq_top_of_normal
      (((T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with h | h
  · rw [h, Subgroup.card_bot] at hc
    have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    omega
  · rw [h, Subgroup.card_top, hQ] at hc
    have h16 : 16 ≤ 4 ^ n := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h2 : 0 < 2 ^ n := by positivity
    have : 2 ^ n * (4 ^ n - 1) > 2 ^ n * 1 := Nat.mul_lt_mul_of_pos_left (by omega) h2
    omega

theorem minParabolic_L0T_of_fsu
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hnn : ¬ T ≤ Subgroup.normalizer (L : Set G))
    (hSL : ∃ (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ), 2 ≤ n ∧ Nat.card K = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K)) :
    MinParabolic (fsuL0 T L ⊔ T) T
      ((fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)) := by
  have hnot := not_le_normalizer_T0_of_fsu h37 h38 hfsu hnn hSL
  have hTN : T ≤ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, le_fsuM T L hs⟩
  refine ⟨isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow le_sup_right, fun h => hnot ?_, ?_⟩
  · intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨h (Subgroup.mem_sup_left hx), fsuL0_le_fsuM T L hx⟩
  · set M0 := (fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)
      with hM0
    have hTM0 : T ≤ M0 := le_inf le_sup_right hTN
    have hM0lt : M0 < fsuL0 T L ⊔ T := by
      refine lt_of_le_of_ne inf_le_left fun h => hnot ?_
      intro x hx
      have : x ∈ M0 := h ▸ (Subgroup.mem_sup_left hx : x ∈ fsuL0 T L ⊔ T)
      exact this.2
    have hkey : ∀ X : Subgroup G, T ≤ X → X ≤ fsuL0 T L ⊔ T → X ≠ fsuL0 T L ⊔ T → X ≤ M0 :=
      fun X hTX hX hne => le_inf hX (le_normalizer_T0_of_ne_of_fsu h37 h38 hfsu hnn hSL hTX hX hne)
    ext N
    constructor
    · rintro ⟨⟨hNlt, hNmax⟩, hTN'⟩
      have hNM0 := hkey N hTN' hNlt.le hNlt.ne
      by_contra hne
      exact hM0lt.ne (hNmax M0 (lt_of_le_of_ne hNM0 hne) hM0lt.le)
    · rintro rfl
      refine ⟨⟨hM0lt, fun K hK hKH => ?_⟩, hTM0⟩
      by_contra hne
      exact lt_irrefl _ (lt_of_lt_of_le hK (hkey K (hTM0.trans hK.le) hKH hne))

variable {n : ℕ}

theorem Setup.minParabolic (S : Setup T L I n)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) :
    MinParabolic (fsuL0 T L ⊔ T) T
      ((fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)) := by
  obtain ⟨K, hF, hfin, hK, he⟩ := S.exists_quot_equiv_sl2 h37c h38c
  exact minParabolic_L0T_of_fsu h37c h38c S.hyp.fsu S.not_le_normalizer_L
    ⟨K, hF, hfin, n, S.two_le, hK, he⟩

end CFSG.Quasithin.H13.Ch9

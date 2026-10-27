module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem838T
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8310D

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement Pointwise

namespace Ch837

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_three_dvd_card_of_isSz {X : Type} [Group X] {f : ℕ}
    (h : IsSz f X) : ¬ 3 ∣ Nat.card X := by
  obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := h
  rw [hf] at hK
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  have h2 : (2 ^ (2 * a + 1)) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at h2 ⊢
  intro h3
  have hq1 : 1 ≤ q := by omega
  have h1 : (((q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℕ) : ZMod 3)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h3
  have h2' : (q : ZMod 3) = 2 := by
    rw [← ZMod.natCast_mod, h2]
    rfl
  push_cast [Nat.cast_sub hq1] at h1
  rw [h2'] at h1
  exact absurd h1 (by decide)

theorem le_sup_inf_normalizer_of_isSylowTwoOf {Y N S : Subgroup G} (hNY : N ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) (hS : IsSylowTwoOf S N) :
    Y ≤ N ⊔ (Y ⊓ Subgroup.normalizer (S : Set G)) := by
  intro y hy
  have hS' : IsSylowTwoOf (S.map (MulAut.conj y).toMonoidHom) N := by
    have h := B6.isSylowTwoOf_conjSub hS y
    have hN : B6.conjSub y N = N := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYN hy)
    rw [hN] at h
    exact h
  obtain ⟨h, hhN, hh⟩ := IsSylowTwoOf.exists_conj hS hS'
  have hmem : ∀ s : G, s ∈ S → y * s * y⁻¹ ∈ S.map (MulAut.conj h).toMonoidHom := fun s hs => by
    rw [← hh]
    exact ⟨s, hs, rfl⟩
  have hmem' : ∀ s : G, s ∈ S → h * s * h⁻¹ ∈ S.map (MulAut.conj y).toMonoidHom := fun s hs => by
    rw [hh]
    exact ⟨s, hs, rfl⟩
  have hm : h⁻¹ * y ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      obtain ⟨s', hs', he⟩ := hmem s hs
      have he' : h * s' * h⁻¹ = y * s * y⁻¹ := he
      have : h⁻¹ * y * s * (h⁻¹ * y)⁻¹ = s' := by
        calc h⁻¹ * y * s * (h⁻¹ * y)⁻¹ = h⁻¹ * (y * s * y⁻¹) * h := by group
          _ = h⁻¹ * (h * s' * h⁻¹) * h := by rw [he']
          _ = s' := by group
      rw [this]
      exact hs'
    · intro hs
      set s₀ := h⁻¹ * y * s * (h⁻¹ * y)⁻¹ with hs₀
      obtain ⟨s', hs', he⟩ := hmem' s₀ hs
      have he' : y * s' * y⁻¹ = h * s₀ * h⁻¹ := he
      have : s = s' := by
        have e1 : h * s₀ * h⁻¹ = y * s * y⁻¹ := by rw [hs₀]; group
        have e2 : y * s' * y⁻¹ = y * s * y⁻¹ := he'.trans e1
        exact (by simpa using e2 : s' = s).symm
      rw [this]
      exact hs'
  have hhY : h ∈ Y := hNY hhN
  have hmY : h⁻¹ * y ∈ Y := Y.mul_mem (Y.inv_mem hhY) hy
  have : y = h * (h⁻¹ * y) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hhN) (Subgroup.mem_sup_right ⟨hmY, hm⟩)

omit [Finite G] in
theorem isElemAbelian_subgroupOf {p : ℕ} {X E : Subgroup G} (hEX : E ≤ X)
    (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.subgroupOf X) ∧ Nat.card (E.subgroupOf X) = Nat.card E := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv⟩
  · apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val (hE.1.is_comm.comm ⟨_, Subgroup.mem_subgroupOf.mp a.2⟩
      ⟨_, Subgroup.mem_subgroupOf.mp b.2⟩)
    exact this
  · apply Subtype.ext
    exact hE.2 _ (Subgroup.mem_subgroupOf.mp hx)

theorem exists_eq_conjByElt_of_le_conjClosure (hK : LocalSQTK G)
    (h37 : Vol2Native.A37ForSQTKCat) {H T J K' : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥)
    (hTH : T ≤ H) (hJc : J ∈ cComp H) (hK'c : K' ∈ cComp H) (hle : K' ≤ conjClosure J T) :
    ∃ t ∈ T, K' = conjByElt t J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  set N := pCoreOf 2 K' with hNdef
  have hc : ∀ t ∈ T, ⁅K', conjByElt t J⁆ ≤ N := fun t ht =>
    (Vol2Native.lemma_1_2_1_two hK h37 hH hK'c (conjSub_mem_cComp_of_mem hJc (hTH ht))
      (hcon t ht)).1.trans inf_le_left
  have hNn : ∀ t ∈ T, conjByElt t J ≤ Subgroup.normalizer (N : Set G) := fun t ht =>
    (le_normalizer_of_commutator_le ((hc t ht).trans
      (CFSG.LieType.BorelTits.pCoreOf_le 2 K'))).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K')
  let S' : Subgroup G :=
    { carrier := {y | y ∈ Subgroup.normalizer (N : Set G) ∧ ∀ a ∈ K', ⁅a, y⁆ ∈ N}
      mul_mem' := fun {y₁ y₂} hy₁ hy₂ => ⟨Subgroup.mul_mem _ hy₁.1 hy₂.1, fun a ha => by
        have e : ⁅a, y₁ * y₂⁆ = ⁅a, y₁⁆ * (y₁ * ⁅a, y₂⁆ * y₁⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact N.mul_mem (hy₁.2 a ha) ((Subgroup.mem_normalizer_iff.mp hy₁.1 _).mp (hy₂.2 a ha))⟩
      one_mem' := ⟨Subgroup.one_mem _, fun a _ => by
        simp only [commutatorElement_def, mul_one, inv_one, mul_inv_cancel]
        exact N.one_mem⟩
      inv_mem' := fun {y} hy => ⟨Subgroup.inv_mem _ hy.1, fun a ha => by
        have e : ⁅a, y⁻¹⁆ = y⁻¹ * ⁅a, y⁆⁻¹ * y⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy.1) _).mp
          (N.inv_mem (hy.2 a ha))⟩ }
  have hcl : conjClosure J T ≤ S' := by
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro x ⟨t, ht, j, hj, rfl⟩
    have hx : t * j * t⁻¹ ∈ conjByElt t J := ⟨j, hj, rfl⟩
    exact ⟨hNn t ht hx, fun a ha => hc t ht (Subgroup.commutator_mem_commutator ha hx)⟩
  have hK'O : K' ≤ N := by
    calc K' = ⁅K', K'⁆ := (perfect_of_mem_cComp hK'c).symm
      _ ≤ ⁅K', conjClosure J T⁆ := Subgroup.commutator_mono le_rfl hle
      _ ≤ N := by
        rw [Subgroup.commutator_le]
        intro a ha y hy
        exact (hcl hy).2 a ha
  have h2g : IsPGroup 2 K' := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K').to_le hK'O
  have : Group.IsNilpotent ↥K' := h2g.isNilpotent
  exact not_isSolvable_of_mem_cComp hK'c inferInstance

theorem isSz_of_mem_cComp_ch83Yz
    (h36 : Vol2Native.A36ForSQTKCat) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hlist : SQTKList3Dvd) (h326 : Stmt3_2_6C)
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) {z : G} (hz2 : orderOf z = 2)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z) {J : Subgroup G}
    (hJ : J ∈ cComp (ch83Yz T L z)) :
    ∃ f : ℕ, 3 ≤ f ∧ IsSz f (↥J ⧸ CFSG.pCore 2 ↥J) ∧ ¬ 3 ∣ Nat.card ↥J := by
  classical
  have := hyp.fsu.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  set Gz := Subgroup.centralizer ({z} : Set G) with hGzdef
  set X := ch83X T L z with hXdef
  have hXGz : X ≤ Gz := (twoResidual_le _).trans inf_le_right
  set N₀ := Gz ⊓ Subgroup.normalizer (X : Set G) with hN₀def
  have hXN₀ : X ≤ N₀ := le_inf hXGz Subgroup.le_normalizer
  have hYzN₀ : ch83Yz T L z ≤ N₀ :=
    le_inf (centralizerSection_le_left _ _ _) (centralizerSection_le_normalizer_left _ _ _)
  have hN₀Yz : N₀ ≤ Subgroup.normalizer (ch83Yz T L z : Set G) :=
    le_normalizer_centralizerSection Gz X
  have hJN₀ : J ∈ cComp N₀ := cComp_mem_of_subnormal
    (IsSubnormal.step hYzN₀ ((Subgroup.normal_subgroupOf_iff_le_normalizer hYzN₀).mpr hN₀Yz)
      (IsSubnormal.refl N₀)) hJ
  have hcomm : ∀ y ∈ X, z * y * z⁻¹ = y := fun y hy => by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hXGz hy)
    rw [← h, mul_inv_cancel_right]
  have hzN₀ : z ∈ N₀ := by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, ?_⟩
    show z ∈ Subgroup.normalizer (X : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hcomm x hx]
      exact hx
    · intro hx
      have h1 := hcomm _ hx
      have h2 : z * x * z⁻¹ = x := by
        have := congrArg (fun w => z⁻¹ * w * z) h1
        simpa [mul_assoc] using this
      rw [← h2]
      exact hx
  have hN₀Gz : N₀ ≤ Gz := inf_le_left
  have hzO : Subgroup.zpowers z ≤ pCoreOf 2 N₀ := zpowers_le_pCoreOf hz2 hzN₀ hN₀Gz
  have hN₀O : pCoreOf 2 N₀ ≠ ⊥ := fun h => by
    rw [h] at hzO
    exact hz1 (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp hzO))
  have hKl : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  set R : Subgroup ↥N₀ := CFSG.pCore 2 ↥N₀ with hRdef
  have hRp : IsPGroup 2 R := CFSG.pCore_isPGroup
  let π : ↥N₀ →* ↥N₀ ⧸ R := QuotientGroup.mk' R
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hKl hN₀O
  have : Finite (↥N₀ ⧸ R) := inferInstance
  have hJb := modO2Image_mem_cComp hJN₀
  have hA := h36 _ hQ _ hJb
  obtain ⟨φ, -, hXi, hrel, P, hP, hPc, -⟩ := xi_data h37 h38 h326 hyp hV hrow hN hz2 hzV
  set Kb : Subgroup (↥N₀ ⧸ R) := (X.subgroupOf N₀).map π with hKbdef
  have hXn : (X.subgroupOf N₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXN₀).mpr inf_le_right
  have hKbn : Kb.Normal := Subgroup.Normal.map hXn π hπ
  have : Group.IsSolvable ↥(X ⊔ T) := isSolvable_of_oTwoQuot_equiv φ
  have hXs : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (le_sup_left : X ≤ X ⊔ T))
      (Subgroup.inclusion_injective _)
  have hKbs : Group.IsSolvable ↥Kb := by
    have : Group.IsSolvable ↥(X.subgroupOf N₀) :=
      Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hXN₀).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hXN₀).symm.surjective
    exact Group.isSolvable_of_surjective (f := π.subgroupMap (X.subgroupOf N₀))
      (π.subgroupMap_surjective _)
  have hcardX : Nat.card X = Nat.card (pCoreOf 2 X) * 9 := by
    have h := Subgroup.relIndex_mul_card (H := pCoreOf 2 X) (K := X)
    rw [inf_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 X), hrel] at h
    rw [← h, mul_comm]
  have hKb23 : ∀ r : ℕ, r.Prime → r ∣ Nat.card Kb → r = 2 ∨ r = 3 := by
    intro r hr hd
    have h1 : Nat.card Kb ∣ Nat.card ↥(X.subgroupOf N₀) :=
      Subgroup.card_dvd_of_surjective (π.subgroupMap_surjective (X.subgroupOf N₀))
    have h2 : Nat.card ↥(X.subgroupOf N₀) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN₀).toEquiv
    have hdX : r ∣ Nat.card X := hd.trans (h2 ▸ h1)
    rw [hcardX] at hdX
    rcases (Nat.Prime.dvd_mul hr).mp hdX with h | h
    · obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
      rw [hk] at h
      exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
    · right
      have h' : r ∣ 3 ^ 2 := by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact h
      exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h')
  have hPel := Ch8310.isElemAbelian_of_isXi hXi hP hPc
  have hPN₀ : P ≤ N₀ := hP.le.trans hXN₀
  obtain ⟨hP', hP'card⟩ := isElemAbelian_subgroupOf hPN₀ hPel
  obtain ⟨hEb, hEbcard⟩ := isElemAbelian_map_quotient R hRp (by norm_num : (3 : ℕ) ≠ 2) hP'
  set Eb : Subgroup (↥N₀ ⧸ R) := (P.subgroupOf N₀).map π with hEbdef
  have hEbK : Eb ≤ Kb := Subgroup.map_mono (Subgroup.comap_mono hP.le)
  have hEbc : Nat.card Eb = 3 ^ 2 := by rw [hEbcard, hP'card, hPc]; norm_num
  have hSQ : CFSG.IsStronglyQuasithin ↥N₀ :=
    isStronglyQuasithin_of_pCoreOf_ne_bot_of_evenRank hyp.fsu.qtke.2.2 hN₀O
  have hr3N : CFSG.Open.pRank 3 (⊤ : Subgroup ↥N₀) ≤ 2 :=
    (CFSG.SectionRank.isStronglyQuasithin_iff.mp hSQ) 3 Nat.prime_three (by norm_num)
  have hr3 : CFSG.Open.pRank 3 (⊤ : Subgroup (↥N₀ ⧸ R)) ≤ 2 := by
    rw [CFSG.SectionRank.pRank_quotient_two_group R hRp Nat.prime_three (by norm_num)]
    exact hr3N
  obtain ⟨-, -, f, hfodd, hf3, hSz⟩ :=
    cComp_simple_suzuki_of_a36 hlist hr3 hJb hA hKbs hKb23 hEbK hEb hEbc
  obtain ⟨ψ, hψs, hψk⟩ := exists_modO2_surjection hJN₀
  have e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* ↥(modO2Image N₀ J) :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have hSzJ : IsSz f (↥J ⧸ CFSG.pCore 2 ↥J) := IsSz.of_mulEquiv e.symm hSz
  refine ⟨f, hf3, hSzJ, fun h3 => ?_⟩
  have hcard : Nat.card ↥J = Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) * Nat.card (CFSG.pCore 2 ↥J) :=
    (CFSG.pCore 2 ↥J).card_eq_card_quotient_mul_card_subgroup
  rw [hcard] at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
  · exact not_three_dvd_card_of_isSz hSzJ h
  · obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥J))
    rw [hk] at h
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)) (by norm_num)

omit [Finite G] in
theorem isSylowTwoOf_of_le_of_le {S P Y : Subgroup G} (hS : IsSylowTwoOf S Y) (hSP : S ≤ P)
    (hPY : P ≤ Y) : IsSylowTwoOf S P := by
  refine ⟨hSP, hS.2.1, fun h => hS.2.2 ?_⟩
  have e := Subgroup.relIndex_mul_relIndex S P Y hSP hPY
  exact h.trans (Dvd.intro _ e)

theorem le_fsuM_of_mem_cComp_ch83Yz
    (hNoN : E2.E22StatementNoN) (h443 : Stmt4_4_3Orbit') (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h3228 : Stmt3_2_2_eight)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h326 : Stmt3_2_6C) (h3108 : Stmt3_2_10_eight)
    (h836 : Stmt8_3_6) (hKG : KGRankOneOvergroups) {T L I : Subgroup G}
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) {z : G} (hz2 : orderOf z = 2)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z) {J : Subgroup G}
    (hJ : J ∈ cComp (ch83Yz T L z)) {f : ℕ} (hf3 : 3 ≤ f) (hSz : IsSz f (↥J ⧸ CFSG.pCore 2 ↥J))
    (h3J : ¬ 3 ∣ Nat.card ↥J) : J ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hyp.fsu.simple
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hzT : z ∈ T := fsuV_le_T hyp.fsu hV hN hzmem.1
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  set Gz := Subgroup.centralizer ({z} : Set G) with hGzdef
  set X := ch83X T L z with hXdef
  set Yz := ch83Yz T L z with hYzdef
  set M := fsuM T L with hMdef
  set S := ch83S T L z with hSdef
  have hTM : T ≤ M := le_normalizer_conjClosure L T
  have hXGz : X ≤ Gz := (twoResidual_le _).trans inf_le_right
  have hTX := le_normalizer_ch83X (L := L) hTz
  obtain ⟨hSeq, -⟩ := pCoreOf_sup_eq_inf_centralizerSection hyp.fsu.sylow hTz hXGz hTX
  have hYzGz : Yz ≤ Gz := centralizerSection_le_left _ _ _
  have hTYz : T ≤ Subgroup.normalizer (Yz : Set G) := fun t ht =>
    le_normalizer_centralizerSection Gz X ⟨hTz ht, hTX ht⟩
  set Cl := conjClosure J T with hCldef
  have hJYz : J ≤ Yz := le_of_mem_cComp hJ
  have hClYz : Cl ≤ Yz := conjClosure_le fun t ht j hj =>
    (Subgroup.mem_normalizer_iff.mp (hTYz ht) j).mp (hJYz hj)
  have hTCl : T ≤ Subgroup.normalizer (Cl : Set G) := le_normalizer_conjClosure J T
  set H₀ := Cl ⊔ T with hH₀def
  have hH₀Gz : H₀ ≤ Gz := sup_le (hClYz.trans hYzGz) hTz
  have hzO : Subgroup.zpowers z ≤ pCoreOf 2 H₀ :=
    zpowers_le_pCoreOf hz2 (Subgroup.mem_sup_right hzT) hH₀Gz
  have hPH₀ : pCoreOf 2 H₀ ≠ ⊥ := fun h => by
    rw [h] at hzO
    exact hz1 (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp hzO))
  have hSQ : IsSQTKIn H₀ :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian hPH₀
  have hTH₀ : IsSylowTwoOf T H₀ := isSylowTwoOf_of_le hyp.fsu.sylow le_sup_right
  have hJH₀ : J ≤ H₀ := (le_conjClosure J T).trans le_sup_left
  have hYzn : ((Yz).subgroupOf (Yz ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTYz)
  have hJYT : J ∈ cComp (Yz ⊔ T) :=
    cComp_mem_of_subnormal (IsSubnormal.step le_sup_left hYzn (IsSubnormal.refl _)) hJ
  have hJc₀ : J ∈ cComp H₀ := cComp_mem_of_le hJYT hJH₀ (sup_le_sup_right hClYz T)
  obtain ⟨hBsolv, hover⟩ := hKG G H₀ T J hSQ hPH₀ hTH₀ hJc₀ rfl ⟨f, Or.inr ⟨hf3, hSz⟩⟩
  set B := H₀ ⊓ Subgroup.normalizer ((T ⊓ Cl : Subgroup G) : Set G) with hBdef
  have hTKS : T ⊓ Cl ≤ S := by
    rw [hSdef, ch83S, hSeq]
    exact inf_le_inf_left T hClYz
  set B₀ := Cl ⊓ Subgroup.normalizer ((T ⊓ Cl : Subgroup G) : Set G) with hB₀def
  have hST : S ≤ T := pCoreOf_le_of_isSylowIn (isSylowTwoOf_of_le hyp.fsu.sylow le_sup_right)
  have hTN : T ≤ Subgroup.normalizer ((T ⊓ Cl : Subgroup G) : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, hTCl hs⟩
  have hTB₀ : T ≤ Subgroup.normalizer (B₀ : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTCl hs, Subgroup.le_normalizer (hTN hs)⟩
  have hSB₀ : S ≤ Subgroup.normalizer (B₀ : Set G) := hST.trans hTB₀
  set H₁ := B₀ ⊔ S with hH₁def
  have hH₁B : H₁ ≤ B := sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
    (le_inf (hST.trans le_sup_right) (hST.trans hTN))
  have : Group.IsSolvable ↥B := hBsolv
  have : Group.IsSolvable ↥H₁ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hH₁B)
  have hTS : T ≤ Subgroup.normalizer (S : Set G) := fun s hs =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_right hs)
  have hTH₁ : T ≤ Subgroup.normalizer (H₁ : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTB₀ hs),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTS hs)]
  have hS₁ : IsSylowTwoOf S H₁ := by
    have hT' : IsSylowTwoOf T (H₁ ⊔ T) := isSylowTwoOf_of_le hyp.fsu.sylow le_sup_right
    have hinf := B6.isSylowTwoOf_inf_normal hT' le_sup_left (sup_le Subgroup.le_normalizer hTH₁)
    have heq : T ⊓ H₁ = S := by
      refine le_antisymm (fun x hx => ?_) (le_inf hST le_sup_right)
      have hx2 : x ∈ ((B₀ ⊔ S : Subgroup G) : Set G) := hx.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left B₀ S hSB₀] at hx2
      obtain ⟨b, hb, c, hc', rfl⟩ := Set.mem_mul.mp hx2
      have hbT : b ∈ T := by
        have := T.mul_mem hx.1 (T.inv_mem (hST hc'))
        rwa [mul_inv_cancel_right] at this
      exact S.mul_mem (hTKS ⟨hbT, hb.1⟩) hc'
    rw [← heq]
    exact hinf
  have hzS : z ∈ S := zpowers_le_pCoreOf hz2 (Subgroup.mem_sup_right hzT) (sup_le hXGz hTz)
    (Subgroup.mem_zpowers z)
  have hn₁ : E1.nParam H₁ = 1 := by
    have hn1 : E1.nParam H₁ ≤ 1 := E1.solvable_nParam_le_one inferInstance
    have hn0 : E1.nParam H₁ ≠ 0 := by
      intro h
      have hodd := E1.odd_of_nParam_le_zero (le_of_eq h)
      have h2 : 2 ∣ Nat.card ↥H₁ := by
        have := Subgroup.orderOf_dvd_natCard H₁ (Subgroup.mem_sup_right hzS)
        rwa [hz2] at this
      exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h2)
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by simp) hn1)
    rw [← hk] at hn1 hn0 ⊢
    have hk1 : k ≤ 1 := by exact_mod_cast hn1
    have hk0 : k ≠ 0 := by exact_mod_cast hn0
    have : k = 1 := by omega
    rw [this]
    rfl
  have hH₁M : H₁ ≤ M := h836 G T L I hyp h731 hc hrow z hz2 hzV H₁ hS₁ hn₁
  have hBM : B ≤ M := by
    intro x hx
    have hx1 : x ∈ ((Cl ⊔ T : Subgroup G) : Set G) := hx.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Cl T hTCl] at hx1
    obtain ⟨k, hk, u, hu, rfl⟩ := Set.mem_mul.mp hx1
    have hkN : k ∈ Subgroup.normalizer ((T ⊓ Cl : Subgroup G) : Set G) := by
      have := Subgroup.mul_mem _ hx.2 (Subgroup.inv_mem _ (hTN hu))
      rwa [mul_inv_cancel_right] at this
    exact M.mul_mem (hH₁M (Subgroup.mem_sup_left ⟨hk, hkN⟩)) (hTM hu)
  by_contra hJM
  have hH₀M : ¬ H₀ ≤ M := fun h => hJM (hJH₀.trans h)
  have hstar : IsHStar T M H₀ := ⟨⟨le_sup_right, hPH₀⟩, hH₀M, fun Y hY hYH₀ hYM =>
    (hover Y hY.1 hYH₀).resolve_right fun hYN => hYM ((le_inf hYH₀ hYN).trans hBM)⟩
  have hns₀ : ¬ Group.IsSolvable ↥H₀ := fun hs => not_isSolvable_of_mem_cComp hJc₀
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJH₀))
  have hKl : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  refine Ch838.false_of_isHStar_of_not_three_dvd hNoN h443 h37 h38 h39 h3228 hC58 h317 h326 h3108
    hyp hrow hV hz2 hzV hstar hH₀Gz hns₀ fun K' hK'c _ h3 => h3J ?_
  have hH₀N : H₀ ≤ Subgroup.normalizer (Cl : Set G) := sup_le Subgroup.le_normalizer hTCl
  have h2q : ∀ y ∈ H₀, ∃ k : ℕ, y ^ 2 ^ k ∈ Cl :=
    B6.isTwoQuotient_of_sup_eq hyp.fsu.sylow.1 hH₀N (sup_comm _ _)
  have hK'Cl : K' ≤ Cl := (Ch838.le_twoResidual_of_mem_cComp hK'c).trans
    (twoResidual_le_of_isTwoQuotient le_sup_left hH₀N h2q)
  obtain ⟨t, -, rfl⟩ := exists_eq_conjByElt_of_le_conjClosure hKl h37 hPH₀ le_sup_right hJc₀ hK'c
    hK'Cl
  have hcard : Nat.card ↥(conjByElt t J) = Nat.card ↥J :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  rwa [hcard] at h3

end Ch837

open Ch837 in
theorem claim837YNonsolv_of_lie
    (hNoN : E2.E22StatementNoN) (h443 : Stmt4_4_3Orbit') (h36 : Vol2Native.A36ForSQTKCat)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (hlist : SQTKList3Dvd) (h3228 : Stmt3_2_2_eight)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h326 : Stmt3_2_6C) (h3108 : Stmt3_2_10_eight)
    (h836 : Stmt8_3_6) (hKG : KGRankOneOvergroups) : Claim837YNonsolv := by
  intro G _ _ T L I hyp h731 hc hrow z hz2 hzV _
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hyp.fsu.simple
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hzT : z ∈ T := fsuV_le_T hyp.fsu hV hN hzmem.1
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  set Gz := Subgroup.centralizer ({z} : Set G) with hGzdef
  set X := ch83X T L z with hXdef
  set Yz := ch83Yz T L z with hYzdef
  set M := fsuM T L with hMdef
  set S := ch83S T L z with hSdef
  have hTM : T ≤ M := le_normalizer_conjClosure L T
  have hXGz : X ≤ Gz := (twoResidual_le _).trans inf_le_right
  have hTX := le_normalizer_ch83X (L := L) hTz
  obtain ⟨-, hSYz⟩ := pCoreOf_sup_eq_inf_centralizerSection hyp.fsu.sylow hTz hXGz hTX
  have hYzGz : Yz ≤ Gz := centralizerSection_le_left _ _ _
  have hST : S ≤ T := pCoreOf_le_of_isSylowIn (isSylowTwoOf_of_le hyp.fsu.sylow le_sup_right)
  have hzS : z ∈ S := zpowers_le_pCoreOf hz2 (Subgroup.mem_sup_right hzT) (sup_le hXGz hTz)
    (Subgroup.mem_zpowers z)
  have hSYz' : S ≤ Yz := hSYz.1
  have hzO : Subgroup.zpowers z ≤ pCoreOf 2 Yz := zpowers_le_pCoreOf hz2 (hSYz' hzS) hYzGz
  have hYzO : pCoreOf 2 Yz ≠ ⊥ := fun h => by
    rw [h] at hzO
    exact hz1 (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp hzO))
  have hNS : Subgroup.normalizer (S : Set G) ≤ M :=
    normalizer_ch83S_le h37 h38 h39 h326 h3108 hyp hV hrow hN z
  have hKl : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hcomp : ∀ J ∈ cComp Yz, J ≤ M := fun J hJ => by
    obtain ⟨f, hf3, hSz, h3J⟩ :=
      isSz_of_mem_cComp_ch83Yz h36 h37 h38 hlist h326 hyp hrow hV hN hz2 hzV hJ
    exact le_fsuM_of_mem_cComp_ch83Yz hNoN h443 h37 h38 h39 h3228 hC58 h317 h326 h3108 h836 hKG
      hyp h731 hrow hV hN hz2 hzV hJ hf3 hSz h3J
  set H' := conjClosure S Yz with hH'def
  have hH'Yz : H' ≤ Yz := conjClosure_le fun y hy s hs =>
    Yz.mul_mem (Yz.mul_mem hy (hSYz' hs)) (Yz.inv_mem hy)
  have hYzH' : Yz ≤ Subgroup.normalizer (H' : Set G) := le_normalizer_conjClosure S Yz
  have hSH' : S ≤ H' := le_conjClosure S Yz
  have hSH'syl : IsSylowTwoOf S H' := isSylowTwoOf_of_le_of_le hSYz hSH' hH'Yz
  have hfr := le_sup_inf_normalizer_of_isSylowTwoOf hH'Yz hYzH' hSH'syl
  suffices hH'M : H' ≤ M from fun y hy =>
    (sup_le hH'M (inf_le_right.trans hNS)) (hfr hy)
  by_cases hSeq' : S = H'
  · rw [← hSeq']
    exact hST.trans hTM
  have hlt : S < H' := lt_of_le_of_ne hSH' hSeq'
  have hmul : ((H' ⊔ (Yz ⊓ Subgroup.normalizer (S : Set G)) : Subgroup G) : Set G) =
      (H' : Set G) * ((Yz ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left H' _ (inf_le_left.trans hYzH')
  have hres : twoPrimeResidual H' = H' := by
    rw [← conjClosure_eq_twoPrimeResidual hSH'syl]
    refine le_antisymm (conjClosure_le fun h hh s hs =>
      H'.mul_mem (H'.mul_mem hh (hSH' hs)) (H'.inv_mem hh)) ?_
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨y, hy, s, hs, rfl⟩
    have hy' : y ∈ ((H' ⊔ (Yz ⊓ Subgroup.normalizer (S : Set G)) : Subgroup G) : Set G) := hfr hy
    rw [hmul] at hy'
    obtain ⟨h, hh, m, hm, rfl⟩ := Set.mem_mul.mp hy'
    have hms : m * s * m⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hm.2 s).mp hs
    have e : h * m * s * (h * m)⁻¹ = h * (m * s * m⁻¹) * h⁻¹ := by group
    rw [e]
    exact Subgroup.subset_closure ⟨h, hh, _, hms, rfl⟩
  rw [← generated_by_uFamHat hSH'syl hlt hres]
  refine iSup₂_le fun P hP => ?_
  obtain ⟨⟨hPH', hSP, hmax⟩, hPN⟩ := hP
  have hPYz : P ≤ Yz := hPH'.trans hH'Yz
  have hSPsyl : IsSylowTwoOf S P := isSylowTwoOf_of_le_of_le hSYz hSP.le hPYz
  have hPGz : P ≤ Gz := hPYz.trans hYzGz
  have hzOP : Subgroup.zpowers z ≤ pCoreOf 2 P := zpowers_le_pCoreOf hz2 (hSP.le hzS) hPGz
  have hPO : pCoreOf 2 P ≠ ⊥ := fun h => by
    rw [h] at hzOP
    exact hz1 (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp hzOP))
  by_cases hPs : Group.IsSolvable ↥P
  ·
    have hn : E1.nParam P = 1 := by
      have hn1 : E1.nParam P ≤ 1 := E1.solvable_nParam_le_one hPs
      have hn0 : E1.nParam P ≠ 0 := by
        intro h
        have hodd := E1.odd_of_nParam_le_zero (le_of_eq h)
        have h2 : 2 ∣ Nat.card ↥P := by
          have := Subgroup.orderOf_dvd_natCard P (hSP.le hzS)
          rwa [hz2] at this
        exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h2)
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by simp) hn1)
      rw [← hk] at hn1 hn0 ⊢
      have hk1 : k ≤ 1 := by exact_mod_cast hn1
      have hk0 : k ≠ 0 := by exact_mod_cast hn0
      have : k = 1 := by omega
      rw [this]
      rfl
    exact h836 G T L I hyp h731 hc hrow z hz2 hzV P hSPsyl hn
  obtain ⟨MP, hMP⟩ := Set.ncard_eq_one.mp hmax
  have hmin : MinParabolic P S MP := ⟨hSPsyl, hPN, hMP⟩
  have hSQP : SQTKGroup ↥P :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian hPO
  obtain ⟨⟨KP, hKPc, hPKP, -, -⟩, -⟩ := hNoN G P S MP hmin hSQP hPs
  have hKPl : KP ∈ lFamily S := by
    show KP ∈ cComp (KP ⊔ S)
    rw [← hPKP]
    exact hKPc
  obtain ⟨J, hJc, hKPJ⟩ := Vol2Native.lemma_1_2_4_exists hKl h37 h39 hYzO hSYz
    ((le_of_mem_cComp hKPc).trans hPYz) hKPl
  rw [hPKP]
  exact sup_le (hKPJ.trans (hcomp J hJc)) (hST.trans hTM)

theorem stmt8_3_7_of_torus
    (h36 : Vol2Native.A36ForSQTKCat) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (hlist : SQTKList3Dvd)
    (h3228 : Stmt3_2_2_eight) (hC58 : TheoremC58) (h317 : AS317Sylow) (h332 : Stmt3_3_2MTwo)
    (h326 : Stmt3_2_6C) (h3108 : Stmt3_2_10_eight) (h134 : EmptyFaithfulMultiple.Prop134E9He)
    (h734 : Stmt7_3_4) (h836 : Stmt8_3_6) (hOut : KG838Out) (hKG : KGRankOneOvergroups)
    (hNoN : E2.E22StatementNoN) (h443 : Stmt4_4_3Orbit') : Stmt8_3_7 :=
  stmt8_3_7_of_lie h37 h38 h39 h3228 hC58 h317 h332 h326 h3108 h134 h734 h836 hOut hKG hNoN h443
    (claim837YNonsolv_of_lie hNoN h443 h36 h37 h38 h39 hlist h3228 hC58 h317 h326 h3108 h836 hKG)

end CFSG.Quasithin.H13

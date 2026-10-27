module

public import CFSG.Quasithin.Vol2.Ch9KGFFSpKP
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathAct

public section

namespace CFSG.Quasithin.C41Pf.SpN

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.Quasithin.H13.Ch9.KGFF.SpM

variable {K : Type} [Field K]

theorem exists_sl2_mulVec_e0 {v : Fin 2 → K} (hv : v ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], by simp [det_fin_two, h1]⟩, ?_⟩
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], by simp [det_fin_two, h0]⟩, ?_⟩
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_sl2_mulVec_eq {v w : Fin 2 → K} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v = w := by
  obtain ⟨a, ha⟩ := exists_sl2_mulVec_e0 hv
  obtain ⟨b, hb⟩ := exists_sl2_mulVec_e0 hw
  refine ⟨b * a⁻¹, ?_⟩
  have hinv : ((a⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v =
      ![1, 0] := by
    rw [← ha, Matrix.mulVec_mulVec]
    have e : ((a⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (a : Matrix (Fin 2) (Fin 2) K) = 1 :=
      congrArg Subtype.val (inv_mul_cancel a)
    rw [e, Matrix.one_mulVec]
  have e2 : ((b * a⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (b : Matrix (Fin 2) (Fin 2) K) * ((a⁻¹ : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) := rfl
  rw [e2, ← Matrix.mulVec_mulVec, hinv, hb]

theorem mem_isoFlag_of_fixed_rad_one [Finite K] [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4)
    {δ : Kˣ} (hδ : (δ : K) ≠ 1) {w : Fin 2 ⊕ Fin 2 → K}
    (hR : ∀ r ∈ rad (K := K) 1, spMat r *ᵥ w = w) : w ∈ isoFlag 2 K 2 := by
  have h1 := hR _ (u_mem_rad_one hK4 δ hδ e11 e11_sym)
  have h2 := hR _ (u_mem_rad_one hK4 δ hδ e22 e22_sym)
  have b0 : w (Sum.inr 0) = 0 := by
    have := congrFun h1 (Sum.inl 0)
    rw [mulVec_u_inl] at this
    simpa [e11, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have b1 : w (Sum.inr 1) = 0 := by
    have := congrFun h2 (Sum.inl 1)
    rw [mulVec_u_inl] at this
    simpa [e22, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  rw [mem_isoFlag]
  refine ⟨fun j => ?_, fun j hj => ?_⟩
  · fin_cases j
    · exact b0
    · exact b1
  · have := j.isLt
    omega

theorem fixed_of_mem_rad_one [Finite K] {r : StatedSp 2 K} (hr : r ∈ rad (K := K) 1)
    {w : Fin 2 ⊕ Fin 2 → K} (hw : w ∈ isoFlag 2 K 2) : spMat r *ᵥ w = w := by
  obtain ⟨hr', h1⟩ := blkN_eq_one_of_mem_rad hr
  have hQ : r ∈ Q2 K 1 := perfectCore_le _ hr'
  have hblk : ∀ i k : Fin 2, spMat r (Sum.inl i) (Sum.inl k) =
      (1 : Matrix (Fin 2) (Fin 2) K) i k := by
    intro i k
    have := congrFun₂ (congrArg Subtype.val h1) i k
    rw [blkN_coe] at this
    fin_cases i <;> fin_cases k <;> simpa [blkIdx, sigma2] using this
  rw [mem_isoFlag] at hw
  have hw0 : ∀ k : Fin 2, w (Sum.inr k) = 0 := hw.1
  funext y
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  simp only [hw0, mul_zero, Finset.sum_const_zero, add_zero]
  rcases y with i | i
  · simp [hblk, Matrix.one_apply]
  · simp [spMat_inr_inl_of_mem_Q2_one hQ, hw0]

variable [Finite K]

theorem le_rad_of_isPGroup [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4) {j : Fin 2}
    {X : Subgroup (StatedSp 2 K)} (hXN : X ≤ perfectCore (Q2 K j))
    (hnorm : ∀ n ∈ perfectCore (Q2 K j), ∀ x ∈ X, n * x * n⁻¹ ∈ X) (h2 : IsPGroup 2 ↥X) :
    X ≤ rad j := by
  have := sl2_isSimple (K := K) hK4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Xc : Subgroup ↥(perfectCore (Q2 K j)) := X.subgroupOf (perfectCore (Q2 K j)) with hXc
  have hXcn : Xc.Normal := ⟨fun x hx n => hnorm n n.2 x hx⟩
  have hY := Subgroup.Normal.map hXcn (blkN j) (blkN_surjective hK4 j)
  have hY2 : IsPGroup 2 ↥(Xc.map (blkN j)) :=
    (h2.of_equiv (Subgroup.subgroupOfEquivOfLe hXN).symm).map (blkN j)
  rcases Subgroup.Normal.eq_bot_or_eq_top (Xc.map (blkN j)) with hbot | htop
  · intro x hx
    have hx' : (⟨x, hXN hx⟩ : ↥(perfectCore (Q2 K j))) ∈ Xc := hx
    have h1 : blkN j ⟨x, hXN hx⟩ ∈ Xc.map (blkN j) := ⟨_, hx', rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact mem_rad (hXN hx) h1
  · exfalso
    rw [htop] at hY2
    have h2' : IsPGroup 2 (SpecialLinearGroup (Fin 2) K) := hY2.of_equiv Subgroup.topEquiv
    have : Nontrivial (SpecialLinearGroup (Fin 2) K) := IsSimpleGroup.toNontrivial
    have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
      CFSG.LinearGroups.special_linear_dimension_two_perfect (K := K) hK4
    exact Group.IsPerfect.not_isNilpotent _ h2'.isNilpotent

theorem eq_perfectCore_of_normal [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4)
    (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) {j : Fin 2} {Y : Subgroup (StatedSp 2 K)}
    (hYN : Y ≤ perfectCore (Q2 K j))
    (hnorm : ∀ n ∈ perfectCore (Q2 K j), ∀ y ∈ Y, n * y * n⁻¹ ∈ Y) (hperf : ⁅Y, Y⁆ = Y)
    (hne : Y ≠ ⊥) : Y = perfectCore (Q2 K j) := by
  have := sl2_isSimple (K := K) hK4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := perfectCore (Q2 K j) with hN
  set Yc : Subgroup ↥N := Y.subgroupOf N with hYc
  have hYcn : Yc.Normal := ⟨fun y hy n => hnorm n n.2 y hy⟩
  have hY := Subgroup.Normal.map hYcn (blkN j) (blkN_surjective hK4 j)
  rcases Subgroup.Normal.eq_bot_or_eq_top (Yc.map (blkN j)) with hbot | htop
  ·
    exfalso
    have hYrad : Y ≤ rad j := by
      intro y hy
      have hy' : (⟨y, hYN hy⟩ : ↥N) ∈ Yc := hy
      have h1 : blkN j ⟨y, hYN hy⟩ ∈ Yc.map (blkN j) := ⟨_, hy', rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact mem_rad (hYN hy) h1
    have hY2 : IsPGroup 2 ↥Y := (rad_isPGroup hK j).to_le hYrad
    rcases Subgroup.bot_or_nontrivial Y with hb | hnt
    · exact hne hb
    · have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
      exact Group.IsPerfect.not_isNilpotent _ hY2.isNilpotent
  ·
    refine le_antisymm hYN fun n hn => ?_
    have hsurj : ∀ x : ↥N, ∃ y ∈ Yc, (blkN j) y = (blkN j) x := by
      intro x
      have hx : (blkN j) x ∈ Yc.map (blkN j) := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨y, hy, he⟩ := hx
      exact ⟨y, hy, he⟩
    let π := QuotientGroup.mk' Yc
    have hQ2 : IsPGroup 2 (↥N ⧸ Yc) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Yc q
      obtain ⟨y, hy, he⟩ := hsurj x
      have hr : ((y⁻¹ * x : ↥N) : StatedSp 2 K) ∈ rad j :=
        mem_rad (y⁻¹ * x).2 (by rw [map_mul, map_inv, he, inv_mul_cancel])
      obtain ⟨a, ha⟩ := rad_isPGroup hK j ⟨_, hr⟩
      refine ⟨a, ?_⟩
      have hy1 : QuotientGroup.mk' Yc y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
      have e : (QuotientGroup.mk' Yc x : ↥N ⧸ Yc) = QuotientGroup.mk' Yc (y⁻¹ * x) := by
        rw [map_mul, map_inv, hy1, inv_one, one_mul]
      rw [e, ← map_pow]
      have h3 : (y⁻¹ * x) ^ 2 ^ a = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val ha
        simpa using this
      rw [h3, map_one]
    have hQperf : Group.IsPerfect (↥N ⧸ Yc) := by
      have hNp : Group.IsPerfect ↥N := Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)
      refine ⟨?_⟩
      have h1 : commutator (↥N ⧸ Yc) = (commutator ↥N).map π := by
        rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          QuotientGroup.range_mk']
      rw [h1, Group.isPerfect_def.mp hNp, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
    have hsub : Subsingleton (↥N ⧸ Yc) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isNilpotent _ hQ2.isNilpotent
    have h1 : (QuotientGroup.mk' Yc ⟨n, hn⟩ : ↥N ⧸ Yc) = 1 := Subsingleton.elim _ _
    have h2 : (⟨n, hn⟩ : ↥N) ∈ Yc := (QuotientGroup.eq_one_iff _).mp h1
    exact h2

end CFSG.Quasithin.C41Pf.SpN

namespace CFSG.Quasithin.C41Pf

open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

theorem isParabolic2_map_top [Finite G] {K P : Subgroup G} {X : Type} [Group X]
    (α : ↥K →* X) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K)
    (hP : IsParabolic2 K P) : IsParabolic2 (⊤ : Subgroup X) ((P.subgroupOf K).map α) := by
  obtain ⟨hPK, S, hS, hSP⟩ := hP
  have hrange : α.range = ⊤ := MonoidHom.range_eq_top.mpr hα
  have hSyl := CFSG.QuasithinUnique.Setup.Wreath.isSylowTwoOf_map_hom hS α
  rw [hrange] at hSyl
  refine ⟨le_top, _, hSyl, ?_⟩
  rintro y ⟨-, hyN⟩
  obtain ⟨k, rfl⟩ := hα y
  have hOS : CFSG.Open.pCoreOf 2 K ≤ S :=
    CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS
  have hkN : (k : G) ∈ Subgroup.normalizer (S : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    have hsK : s ∈ K := hS.1 hs
    have hks : (k : G) * s * (k : G)⁻¹ ∈ K := K.mul_mem (K.mul_mem k.2 hsK) (K.inv_mem k.2)
    have h1 : α ⟨_, hks⟩ ∈ (S.subgroupOf K).map α := by
      have h2 := (Subgroup.mem_normalizer_iff.mp hyN (α ⟨s, hsK⟩)).mp ⟨⟨s, hsK⟩, hs, rfl⟩
      have e : α ⟨_, hks⟩ = α k * α ⟨s, hsK⟩ * (α k)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact h2
    obtain ⟨s', hs', he⟩ := h1
    have h3 : s'⁻¹ * ⟨_, hks⟩ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    rw [hker] at h3
    have h4 : ((s'⁻¹ * ⟨_, hks⟩ : ↥K) : G) ∈ S := by
      have hO : CFSG.Open.pCoreOf 2 K = (CFSG.pCore 2 ↥K).map K.subtype := by
        unfold CFSG.Open.pCoreOf
        try with_reducible rfl
      exact hOS (hO ▸ ⟨_, h3, rfl⟩)
    have h5 : ((s' : ↥K) : G) ∈ S := hs'
    have e : (k : G) * s * (k : G)⁻¹ = (s' : G) * ((s'⁻¹ * ⟨_, hks⟩ : ↥K) : G) := by
      simp
    rw [e]
    exact S.mul_mem h5 h4
  exact ⟨k, hSP ⟨k.2, hkN⟩, rfl⟩

theorem isPSL_two_two_two_of_equiv_sl2 {X : Type} [Group X] {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = 4) (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    IsPSL 2 2 2 X := by
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, F, inferInstance, inferInstance,
    by rw [hF]; norm_num,
    ⟨e.trans CFSG.QuasithinUnique.Vol2Native.A312L.sl2EquivStatedProj⟩⟩
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega

end CFSG.Quasithin.C41Pf

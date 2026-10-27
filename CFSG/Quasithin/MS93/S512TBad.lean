module

public import CFSG.Quasithin.MS93.S512TBase
public import CFSG.Quasithin.MS93.S5A54
public import CFSG.Quasithin.MS93.S512TSp

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512T

section Sp4

variable {F : Type} [Field F]

theorem not_qPoint_le_qLine [Finite F] (hF : 1 < Nat.card F) {p l : Submodule F (MSP.V4 F)}
    (hp : MSP.IsPoint p) (hl : MSP.IsLine l) : ¬ MSP.qPoint p ≤ MSP.qLine l := by
  intro hle
  have h1 := card_qPoint_inf_qLine_le hp hl
  rw [inf_eq_left.2 hle, MSP.card_qPoint hp] at h1
  have h3 : Nat.card F ^ 2 < Nat.card F ^ 3 := Nat.pow_lt_pow_right hF (by norm_num)
  omega

end Sp4

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section AtM

omit [Finite G] in
theorem imM_le_centralizer_iff (hTM : T ≤ M) {K K' : Subgroup G} (hK : K ≤ M) (hK' : K' ≤ M) :
    imM hTM K ≤ Subgroup.centralizer (imM hTM K' : Set (puAmalgam hTM).Universal) ↔
      K ≤ Subgroup.centralizer (K' : Set G) := by
  constructor
  · intro h1
    have h2 : imM hTM K ≤ imM hTM (K ⊓ Subgroup.centralizer (K' : Set G)) := by
      rw [imM_inf_centralizer hTM K hK']
      exact le_inf le_rfl h1
    exact ((imM_le_imM_iff hTM hK).1 h2).trans inf_le_right
  · intro h1
    calc imM hTM K ≤ imM hTM (K ⊓ Subgroup.centralizer (K' : Set G)) :=
          imM_mono hTM (le_inf le_rfl h1)
      _ = imM hTM K ⊓ Subgroup.centralizer (imM hTM K' : Set (puAmalgam hTM).Universal) :=
          imM_inf_centralizer hTM K hK'
      _ ≤ _ := inf_le_right

omit [Finite G] in
theorem le_normalizer_of_imM (hTM : T ≤ M) {K X : Subgroup G} (hK : K ≤ M) (hX : X ≤ M)
    (hn : imM hTM K ≤ Subgroup.normalizer (imM hTM X : Set (puAmalgam hTM).Universal)) :
    K ≤ Subgroup.normalizer (X : Set G) := by
  refine le_normalizer_of_map_conj_le fun t ht => ?_
  rintro _ ⟨x, hx, rfl⟩
  have htM := hK ht
  have hxM := hX hx
  have h1 : (puAmalgam hTM).ofA ⟨t, htM⟩ ∈
      Subgroup.normalizer (imM hTM X : Set (puAmalgam hTM).Universal) :=
    hn ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  have h2 := (Subgroup.mem_normalizer_iff.1 h1 ((puAmalgam hTM).ofA ⟨x, hxM⟩)).1
    ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  rw [← map_inv, ← map_mul, ← map_mul] at h2
  obtain ⟨m, hm, he⟩ := h2
  have hme := (puAmalgam hTM).ofA_injective he
  subst hme
  exact Subgroup.mem_subgroupOf.1 hm

omit [Finite G] [Fintype F] in
theorem imSp_le_of_imM_le_vPre (hTM : T ≤ M) {K : Subgroup G} {Y : Subgroup ↥(StatedSp 2 F)}
    (hK : imM hTM K ≤ S5.vPre hTM a Y) : (K.subgroupOf M).map a ≤ Y := by
  rw [imM, S5.vPre, Subgroup.map_le_map_iff_of_injective (puAmalgam hTM).ofA_injective] at hK
  exact Subgroup.map_le_iff_le_comap.2 hK

theorem isLine_commSp_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {E : Subgroup G}
    (hEM : E ≤ M) (hrel : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = (2 ^ k) ^ 2)
    (hquad : ⁅Uq M T L, E⁆ ≤ Subgroup.centralizer (E : Set G)) :
    MSP.IsLine (MSP.commSp ((E.subgroupOf M).map a)) ∧
      MSP.fixSp ((E.subgroupOf M).map a) = MSP.commSp ((E.subgroupOf M).map a) := by
  have hk : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hd.1
  have h1 := relIndex_eq_pow_M h hd hEM
  rw [hrel] at h1
  have hd2 : Module.finrank F (MSP.commSp ((E.subgroupOf M).map a)) = 2 :=
    (Nat.pow_right_injective hk h1).symm
  have hle := commSp_le_fixSp_M h hd hEM hquad
  rw [S5B.fixSp_eq_perp_commSp] at hle ⊢
  have hline : MSP.IsLine (MSP.commSp ((E.subgroupOf M).map a)) :=
    ⟨hd2, fun x hx y hy => MSP.mem_perp.1 (hle hy) x hx⟩
  exact ⟨hline, hline.perp_eq⟩

theorem map_le_qLine_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {E K : Subgroup G}
    (hKM : K ≤ M) (hK : ⁅Uq M T L, E⁆ ≤ Subgroup.centralizer (K : Set G)) :
    (K.subgroupOf M).map a ≤ MSP.qLine (MSP.commSp ((E.subgroupOf M).map a)) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  rw [MSP.le_fixer_iff]
  intro w hw
  obtain ⟨u, hu, rfl⟩ := S5B.exists_mem_commutator_vec_eq h c hw
  exact (S5B.mem_centralizer_iff_vec h hlift c hKM u).1 (hK hu)

theorem le_centralizer_of_map_le_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E K : Subgroup G} (hEM : E ≤ M) (hKM : K ≤ M)
    (hK : (K.subgroupOf M).map a ≤ MSP.qLine (MSP.commSp ((E.subgroupOf M).map a))) :
    K ≤ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  rw [Subgroup.le_centralizer_iff]
  intro x hx
  have hxU : x ∈ Uq M T L := commutator_le_left_of_le_normalizer (hEM.trans hUn) hx
  have hv := S5B.vec_mem_commSp h c hEM ⟨x, hxU⟩ hx
  exact (S5B.mem_centralizer_iff_vec h hlift c hKM ⟨x, hxU⟩).2 (MSP.le_fixer_iff.1 hK hv)

theorem commSp_eq_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {E N : Subgroup G}
    (hNM : N ≤ M) (hEN : E ≤ N) (hN : ⁅Uq M T L, E⁆ ≤ Subgroup.centralizer (N : Set G))
    (hl : MSP.IsLine (MSP.commSp ((E.subgroupOf M).map a))) :
    MSP.commSp ((N.subgroupOf M).map a) = MSP.commSp ((E.subgroupOf M).map a) :=
  le_antisymm ((MSP.commSp_mono (map_le_qLine_M h hd hNM hN)).trans (MSP.commSp_qLine_le hl))
    (MSP.commSp_mono (Subgroup.map_mono fun _ hx => hEN hx))

omit [Finite G] [Fintype F] in
theorem map_le_stab_M {N K : Subgroup G} (hKN : K ≤ Subgroup.normalizer (N : Set G)) :
    (K.subgroupOf M).map a ≤ MSP.stab (MSP.commSp ((N.subgroupOf M).map a)) := by
  rintro _ ⟨m, hm, rfl⟩
  have hmN : (m : G) ∈ Subgroup.normalizer (N : Set G) := hKN (Subgroup.mem_subgroupOf.1 hm)
  have hconj : ((N.subgroupOf M).map a).map (MulAut.conj (a m)).toMonoidHom ≤
      (N.subgroupOf M).map a := by
    rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    have hn' : (m : G) * n * (m : G)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.1 hmN n).1 (Subgroup.mem_subgroupOf.1 hn)
    refine ⟨m * n * m⁻¹, Subgroup.mem_subgroupOf.2 (by simpa using hn'), ?_⟩
    simp [MulAut.conj_apply, map_mul, map_inv]
  refine MSP.mem_stab_of_le fun v hv => ?_
  have h1 : MSP.mat (a m) *ᵥ v ∈
      (MSP.commSp ((N.subgroupOf M).map a)).map (Matrix.mulVecLin (MSP.mat (a m))) :=
    ⟨v, hv, rfl⟩
  rw [← MSP.commSp_map_conj] at h1
  exact MSP.commSp_mono hconj h1

theorem jOffM_le_qLine_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hcard : Nat.card (S5.offSetM M T L (2 ^ k)) = 1) {l₁ : Submodule F (MSP.V4 F)}
    (hl₁ : MSP.IsLine l₁) (hJ₁ : ((S5.jOffM M T L (2 ^ k)).subgroupOf M).map a ≤ MSP.qLine l₁)
    {E : Subgroup G} (hET : E ≤ T) (hEcard : Nat.card ((E.subgroupOf M).map a) = (2 ^ k) ^ 2)
    {l' : Submodule F (MSP.V4 F)} (hl' : MSP.IsLine l')
    (hfix : MSP.fixSp ((E.subgroupOf M).map a) = l')
    (hT' : (T.subgroupOf M).map a ≤ MSP.stab l') :
    ((S5.jOffM M T L (2 ^ k)).subgroupOf M).map a ≤ MSP.qLine l' := by
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hq2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hd.1
  have hcard' : Nat.card (S5.candMax ((T.subgroupOf M).map a)) = 1 := by
    have := S5.IsSp4Data.card_offSetM hd h hlift
    rw [hcard] at this
    exact this.symm
  obtain ⟨A₀, hA⟩ := Set.ncard_eq_one.1 (by rw [← Nat.card_coe_set_eq]; exact hcard')
  have hA₀ : A₀ ∈ S5.candMax ((T.subgroupOf M).map a) := by
    rw [hA]
    exact Set.mem_singleton A₀
  have hJ : S5.jOffM M T L (2 ^ k) = S5.liftT T a A₀ :=
    S5.IsSp4Data.jOffM_eq_of_candMax_eq hd h hlift hA
  have hJA : ((S5.jOffM M T L (2 ^ k)).subgroupOf M).map a = A₀ := by
    rw [hJ]
    exact S5.imSp_liftT hA₀.1.1
  rw [hJA] at hJ₁ ⊢
  by_contra hne_le
  have hne : l₁ ≠ l' := by
    rintro rfl
    exact hne_le hJ₁
  have hcA : Nat.card A₀ ≤ (2 ^ k) ^ 2 := by
    have h1 := Subgroup.card_le_of_le (le_inf hJ₁ (hA₀.1.1.trans hT'))
    have h2 := card_qLine_inf_stab_le hl₁ hl' hne
    rw [hFq] at h2
    exact h1.trans h2
  have hV : Nat.card (MSP.V4 F) = (2 ^ k) ^ 4 := by rw [MSP.card_V4, hFq]
  have hl'c : Nat.card l' = (2 ^ k) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F), hl'.1, hFq]
  have hEc : S5.IsCandSp ((T.subgroupOf M).map a) ((E.subgroupOf M).map a) := by
    refine ⟨Subgroup.map_mono fun x hx => hET hx, ?_, ?_⟩
    · rw [hfix, hV, hl'c, hEcard]
      exact (by ring : (2 ^ k) ^ 4 = (2 ^ k) ^ 2 * (2 ^ k) ^ 2).le
    · rw [hfix, hV, hl'c, hFq]
      exact (by ring : (2 ^ k) ^ 4 = (2 ^ k) ^ 2 * (2 ^ k) ^ 2).le
  have hEmax : (E.subgroupOf M).map a ∈ S5.candMax ((T.subgroupOf M).map a) :=
    ⟨hEc, fun B hB => (hA₀.2 B hB).trans (hcA.trans hEcard.ge)⟩
  rw [hA] at hEmax
  have hEA : (E.subgroupOf M).map a = A₀ := hEmax
  have hEl' : (E.subgroupOf M).map a ≤ MSP.qLine l' := MSP.le_fixer_iff.2 hfix.ge
  have h3 := Subgroup.card_le_of_le (le_inf (hEA.le.trans hJ₁) hEl')
  have h4 := card_qLine_inf_qLine_le hl₁ hl' hne
  rw [hFq] at h4
  rw [hEcard] at h3
  nlinarith

theorem jOffM_eq_of_le_qLine_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hT : (T.subgroupOf M).map a ≤ MSP.qLine l)
    (hJ2 : (2 ^ k) ^ 2 ≤ Nat.card (((S5.jOffM M T L (2 ^ k)).subgroupOf M).map a)) :
    S5.jOffM M T L (2 ^ k) = T := by
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hJT : S5.jOffM M T L (2 ^ k) ≤ T := iSup₂_le fun E hE => hE.1.1
  have hV : Nat.card (MSP.V4 F) = (2 ^ k) ^ 4 := by rw [MSP.card_V4, hFq]
  have hlc : Nat.card l = (2 ^ k) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F), hl.1, hFq]
  have hfix : (2 ^ k) ^ 2 ≤ Nat.card (MSP.fixSp ((T.subgroupOf M).map a)) := by
    rw [← hlc]
    exact Nat.card_mono (Set.toFinite _) fun x hx => MSP.le_fixer_iff.1 hT hx
  have hTJ : (2 ^ k) ^ 2 ≤ Nat.card ((T.subgroupOf M).map a) :=
    hJ2.trans (Subgroup.card_le_of_le (Subgroup.map_mono fun x hx => hJT hx))
  have hTc : S5.IsCandSp ((T.subgroupOf M).map a) ((T.subgroupOf M).map a) := by
    refine ⟨le_rfl, ?_, ?_⟩
    · rw [hV]
      calc (2 ^ k) ^ 4 = (2 ^ k) ^ 2 * (2 ^ k) ^ 2 := by ring
        _ ≤ _ := Nat.mul_le_mul hfix hTJ
    · rw [hV, hFq]
      calc (2 ^ k) ^ 4 = (2 ^ k) ^ 2 * (2 ^ k) ^ 2 := by ring
        _ ≤ _ := Nat.mul_le_mul hfix le_rfl
  have hTmax : (T.subgroupOf M).map a ∈ S5.candMax ((T.subgroupOf M).map a) :=
    ⟨hTc, fun B hB => Subgroup.card_le_of_le hB.1⟩
  have hsup : (⨆ A ∈ S5.candMax ((T.subgroupOf M).map a), A) = (T.subgroupOf M).map a :=
    le_antisymm (iSup₂_le fun A hA => hA.1.1) (le_iSup₂_of_le _ hTmax le_rfl)
  exact S5.IsSp4Data.jOffM_eq_of_iSup hd h hlift hsup

theorem commutator_le_of_card_le_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E N : Subgroup G} (hNM : N ≤ M) (hEN : E ≤ N)
    (hEcard : Nat.card ((E.subgroupOf M).map a) = (2 ^ k) ^ 2)
    (hNcard : Nat.card ((N.subgroupOf M).map a) ≤ (2 ^ k) ^ 2) :
    ⁅Uq M T L, N⁆ ≤ ⁅Uq M T L, E⁆ := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have heq : (E.subgroupOf M).map a = (N.subgroupOf M).map a :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono fun x hx => hEN hx) (hNcard.trans hEcard.ge)
  rw [Subgroup.commutator_le]
  intro u hu n hn
  have hnM : n ∈ M := hNM hn
  obtain ⟨e, he, hae⟩ : ∃ e ∈ E.subgroupOf M, a e = a ⟨n, hnM⟩ := by
    have : a ⟨n, hnM⟩ ∈ (N.subgroupOf M).map a := ⟨⟨n, hnM⟩, hn, rfl⟩
    rw [← heq] at this
    exact this
  have hmU : ∀ v ∈ Uq M T L, ((e⁻¹ * ⟨n, hnM⟩ : ↥M) : G) * v * ((e⁻¹ * ⟨n, hnM⟩ : ↥M) : G)⁻¹ =
      v := by
    intro v hv
    have hv' : ((e⁻¹ * ⟨n, hnM⟩ : ↥M) : G) * v * ((e⁻¹ * ⟨n, hnM⟩ : ↥M) : G)⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (hUn (e⁻¹ * ⟨n, hnM⟩ : ↥M).2) v).1 hv
    refine hlift _ (e⁻¹ * ⟨n, hnM⟩ : ↥M).2 v hv ?_
    have hvec := c.vec_commutator (e⁻¹ * ⟨n, hnM⟩) ⟨v, hv⟩ hv'
    have ham : a (e⁻¹ * ⟨n, hnM⟩) = 1 := by rw [map_mul, map_inv, hae, inv_mul_cancel]
    rw [ham, MSP.mat_one, Matrix.one_mulVec, sub_self] at hvec
    exact ((c.vec_eq_zero_iff _).1 hvec).2
  have hn' : n = (e : G) * ((e⁻¹ * ⟨n, hnM⟩ : ↥M) : G) := by simp
  have key : ⁅u, n⁆ = ⁅u, (e : G)⁆ := by
    have hmu := hmU u⁻¹ (inv_mem hu)
    rw [hn', commutatorElement_def, commutatorElement_def]
    calc u * ((e : G) * ((e⁻¹ * ⟨n, hnM⟩ : ↥M) : G)) * u⁻¹ *
          ((e : G) * ((e⁻¹ * ⟨n, hnM⟩ : ↥M) : G))⁻¹ =
        u * e * (((e⁻¹ * ⟨n, hnM⟩ : ↥M) : G) * u⁻¹ * ((e⁻¹ * ⟨n, hnM⟩ : ↥M) : G)⁻¹) *
          (e : G)⁻¹ := by group
      _ = u * e * u⁻¹ * (e : G)⁻¹ := by rw [hmu]
  rw [key]
  exact Subgroup.commutator_mem_commutator hu (Subgroup.mem_subgroupOf.1 he)

theorem card_le_of_qPoint_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p)
    (hTp : (T.subgroupOf M).map a = MSP.qPoint p) {E N : Subgroup G} (hNT : N ≤ T)
    (hN : ⁅Uq M T L, E⁆ ≤ Subgroup.centralizer (N : Set G))
    (hl : MSP.IsLine (MSP.commSp ((E.subgroupOf M).map a))) :
    Nat.card ((N.subgroupOf M).map a) ≤ (2 ^ k) ^ 2 := by
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hN1 : (N.subgroupOf M).map a ≤
      MSP.qPoint p ⊓ MSP.qLine (MSP.commSp ((E.subgroupOf M).map a)) :=
    le_inf (hTp ▸ Subgroup.map_mono fun x hx => hNT hx) (map_le_qLine_M h hd (hNT.trans h.le) hN)
  have h2 := card_qPoint_inf_qLine_le hp hl
  rw [hFq] at h2
  exact (Subgroup.card_le_of_le hN1).trans h2

theorem card_commutator_le_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {E : Subgroup G}
    (hEM : E ≤ M) (hrel : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = (2 ^ k) ^ 2)
    (hquad : ⁅Uq M T L, E⁆ ≤ Subgroup.centralizer (E : Set G)) :
    Nat.card ↥⁅Uq M T L, E⁆ ≤ (2 ^ k) ^ 3 := by
  obtain ⟨nv⟩ := S5.IsSp4Data.nonempty_natVec hd
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hU := nv.card_Uq
  have hU0 := (sp4Lift_holds G M T L h k F _ _ a hd).1
  have hV : Nat.card (MSP.V4 F) = (2 ^ k) ^ 4 := by rw [MSP.card_V4, hFq]
  have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer (E : Set G)) (Uq M T L)
  have h2 : ⁅Uq M T L, E⁆ ≤ Subgroup.centralizer (E : Set G) ⊓ Uq M T L :=
    le_inf hquad (commutator_le_left_of_le_normalizer (hEM.trans hUn))
  have h3 : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) *
      Nat.card ↥(Subgroup.centralizer (E : Set G) ⊓ Uq M T L) ≤
      (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) * (2 ^ k) ^ 3 := by
    rw [h1, hU, hV, hrel]
    calc Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) * (2 ^ k) ^ 4 ≤
        2 ^ k * (2 ^ k) ^ 4 := Nat.mul_le_mul_right _ hU0
      _ = (2 ^ k) ^ 2 * (2 ^ k) ^ 3 := by ring
  exact (Subgroup.card_le_of_le h2).trans
    (Nat.le_of_mul_le_mul_left h3 (by rw [hrel]; positivity))

end AtM

section Base

theorem le_stabCenter_of_le_centralizer (hq2 : S5B.Q2Cent) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {R : Subgroup (puAmalgam h.le).Universal} (hRX : R ≤ XM _ (baseA (puAmalgam h.le)))
    (hRL : puTrans h.le L (baseA _) ≤ Subgroup.centralizer (R : Set _)) :
    R ≤ stabCenter _ (baseA (puAmalgam h.le)) := by
  rw [S5B.xm_baseA_eq h] at hRX
  obtain ⟨R₀, hR₀X, hR₀M, rfl⟩ := S5B.exists_eq_imM h.le hRX
  rw [S5B.puTrans_L_baseA h, imM_le_centralizer_iff h.le h.L_le hR₀M] at hRL
  have hZc := S5B.zq_le_centralizer hq2 h hmin hb hd
  rw [S5B.stabCenter_baseA h.le]
  exact imM_mono h.le (le_inf hR₀M ((le_inf hR₀X (Subgroup.le_centralizer_iff.1 hRL)).trans hZc))

end Base

section Vertex

theorem bad_vertex (h54 : S54) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {δ ε : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) (hδε : (puAmalgam h.le).treeGraph.Adj δ ε)
    {E N : Subgroup (puAmalgam h.le).Universal} (hEε : E ≤ Qv _ ε)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) = (2 ^ k) ^ 2)
    (hquad : ⁅S5.uSub h.le L δ, E⁆ ≤ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal))
    (hEQ : (Qv _ δ).relIndex E = (2 ^ k) ^ 2) (hNs : N ≤ stab _ δ) (hEN : E ≤ N)
    (hNc : ⁅S5.uSub h.le L δ, E⁆ ≤ Subgroup.centralizer (N : Set (puAmalgam h.le).Universal)) :
    Nat.card ↥⁅S5.uSub h.le L δ, E⁆ < (2 ^ k) ^ 4 ∧
      (Qv _ ε ≤ Subgroup.normalizer (N : Set (puAmalgam h.le).Universal) →
        Nat.card (S5.offSet h.le L (2 ^ k) (baseA _) (baseB _)) = 1 →
        (∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
          Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.stab l) ∧
          S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l)) →
        (2 ^ k) ^ 2 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex
          (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)) →
        S5.jOff h.le L (2 ^ k) δ ε ≤ Subgroup.centralizer
          ((⁅S5.uSub h.le L δ, E⁆ : Subgroup _) : Set (puAmalgam h.le).Universal)) ∧
      (Qv _ ε ≤ Subgroup.centralizer
          ((⁅S5.uSub h.le L δ, E⁆ : Subgroup _) : Set (puAmalgam h.le).Universal) →
        (∀ p : Submodule F (MSP.V4 F), MSP.IsPoint p →
          S5.vIm h.le a (Qv _ (baseB (puAmalgam h.le))) ≠ MSP.qPoint p) ∧
        S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) = Qv _ (baseB (puAmalgam h.le)) ∧
        ∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
          Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.stab l) ∧
          S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l)) ∧
      (N ≤ Qv _ ε → (Qv _ δ).relIndex N ≤ (2 ^ k) ^ 2 →
        ⁅S5.uSub h.le L δ, N⁆ ≤ ⁅S5.uSub h.le L δ, E⁆) ∧
      (N ≤ Qv _ ε → ∀ p : Submodule F (MSP.V4 F), MSP.IsPoint p →
        S5.vIm h.le a (Qv _ (baseB (puAmalgam h.le))) = MSP.qPoint p →
        (Qv _ δ).relIndex N ≤ (2 ^ k) ^ 2) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hq2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hd.1
  have hJT : S5.jOffM M T L (2 ^ k) ≤ T := iSup₂_le fun E hE => hE.1.1
  have hJM : S5.jOffM M T L (2 ^ k) ≤ M := hJT.trans h.le
  obtain ⟨c, rfl, rfl⟩ := exists_smul_base_edge _ hδ hδε
  have hEst : E ≤ stab _ (c • baseA (puAmalgam h.le)) :=
    hEε.trans (qv_le_stab_of_adj _ hδε.symm)
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le c hEst
  obtain ⟨N₀, hN₀M, rfl⟩ := S5B.exists_eq_map_imM h.le c hNs
  have hU : S5.uSub h.le L (c • baseA (puAmalgam h.le)) =
      (imM h.le (Uq M T L)).map (MulAut.conj c).toMonoidHom := by
    rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h]
  have hQε : Qv _ (c • baseB (puAmalgam h.le)) = (imM h.le T).map (MulAut.conj c).toMonoidHom := by
    rw [qv_smul, puAmalgam.qv_baseB]
  have hQδ : Qv _ (c • baseA (puAmalgam h.le)) =
      (imM h.le (pCoreOf 2 M)).map (MulAut.conj c).toMonoidHom := by
    rw [qv_smul, S5B.qv_baseA_eq h]
  have hJ : S5.jOff h.le L (2 ^ k) (c • baseA (puAmalgam h.le)) (c • baseB _) =
      (imM h.le (S5.jOffM M T L (2 ^ k))).map (MulAut.conj c).toMonoidHom := by
    rw [S5B.jOff_smul h.le hLn, S5.jOff_baseA h]
  have hcommM : ⁅Uq M T L, E₀⁆ ≤ M := commutator_le_of_le (Uq_le h.L_le) hE₀M
  have hUE : ⁅S5.uSub h.le L (c • baseA (puAmalgam h.le)),
      (imM h.le E₀).map (MulAut.conj c).toMonoidHom⁆ =
      (imM h.le ⁅Uq M T L, E₀⁆).map (MulAut.conj c).toMonoidHom := by
    rw [hU, ← Subgroup.map_commutator, imM_commutator h.le (Uq_le h.L_le) hE₀M]
  have hUN : ⁅S5.uSub h.le L (c • baseA (puAmalgam h.le)),
      (imM h.le N₀).map (MulAut.conj c).toMonoidHom⁆ =
      (imM h.le ⁅Uq M T L, N₀⁆).map (MulAut.conj c).toMonoidHom := by
    rw [hU, ← Subgroup.map_commutator, imM_commutator h.le (Uq_le h.L_le) hN₀M]
  have hE₀T : E₀ ≤ T := by
    rw [hQε, map_conj_le_map_conj_iff, imM_le_imM_iff h.le hE₀M] at hEε
    exact hEε
  have hrel₀ : (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) = (2 ^ k) ^ 2 := by
    rw [hU, PU.centralizer_map_mulEquiv,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective,
      S5B.relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₀M] at hrel
    exact hrel
  have hquad₀ : ⁅Uq M T L, E₀⁆ ≤ Subgroup.centralizer (E₀ : Set G) := by
    rw [hUE, PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff,
      imM_le_centralizer_iff h.le hcommM hE₀M] at hquad
    exact hquad
  have hEQ₀ : Nat.card ((E₀.subgroupOf M).map a) = (2 ^ k) ^ 2 := by
    rw [hQδ, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective,
      S5B.relIndex_imM h.le hE₀M] at hEQ
    exact (S5.IsSp4Data.card_imSp hd h hE₀T).trans hEQ
  have hEN₀ : E₀ ≤ N₀ := by
    rwa [map_conj_le_map_conj_iff, imM_le_imM_iff h.le hE₀M] at hEN
  have hNc₀ : ⁅Uq M T L, E₀⁆ ≤ Subgroup.centralizer (N₀ : Set G) := by
    rw [hUE, PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff,
      imM_le_centralizer_iff h.le hcommM hN₀M] at hNc
    exact hNc
  obtain ⟨hl', hfix⟩ := isLine_commSp_M h hd hE₀M hrel₀ hquad₀
  have hrelN : N₀ ≤ T → (Qv _ (c • baseA (puAmalgam h.le))).relIndex
      ((imM h.le N₀).map (MulAut.conj c).toMonoidHom) = Nat.card ((N₀.subgroupOf M).map a) := by
    intro hN₀T
    rw [hQδ, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective,
      S5B.relIndex_imM h.le hN₀M]
    exact (S5.IsSp4Data.card_imSp hd h hN₀T).symm
  have hN₀T : (imM h.le N₀).map (MulAut.conj c).toMonoidHom ≤ Qv _ (c • baseB (puAmalgam h.le)) →
      N₀ ≤ T := by
    intro hNT
    rw [hQε, map_conj_le_map_conj_iff, imM_le_imM_iff h.le hN₀M] at hNT
    exact hNT
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hUE, Subgroup.card_map_of_injective (MulAut.conj c).injective, S5B.card_imM h.le hcommM]
    calc _ ≤ (2 ^ k) ^ 3 := card_commutator_le_M h hd hE₀M hrel₀ hquad₀
      _ < (2 ^ k) ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  · intro hQN hcard hline hJ2
    obtain ⟨l₁, hl₁, hTl, hJl⟩ := hline
    have hJ₁ : ((S5.jOffM M T L (2 ^ k)).subgroupOf M).map a ≤ MSP.qLine l₁ :=
      imSp_le_of_imM_le_vPre h.le (by rw [← S5.jOff_baseA h]; exact hJl)
    have hcardM : Nat.card (S5.offSetM M T L (2 ^ k)) = 1 :=
      (S5.card_offSet_baseA h (2 ^ k)).symm.trans hcard
    have hTN : T ≤ Subgroup.normalizer (N₀ : Set G) := by
      rw [hQε, normalizer_map_conj, map_conj_le_map_conj_iff] at hQN
      exact le_normalizer_of_imM h.le h.le hN₀M hQN
    have hT' : (T.subgroupOf M).map a ≤ MSP.stab (MSP.commSp ((E₀.subgroupOf M).map a)) := by
      rw [← commSp_eq_M h hd hN₀M hEN₀ hNc₀ hl']
      exact map_le_stab_M hTN
    have hJl' := jOffM_le_qLine_M h hd hcardM hl₁ hJ₁ hE₀T hEQ₀ hl' hfix hT'
    have hcent := le_centralizer_of_map_le_M h hd hE₀M hJM hJl'
    rw [hJ, hUE, PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff,
      imM_le_centralizer_iff h.le hJM hcommM]
    exact hcent
  · intro hQR
    have hTR : T ≤ Subgroup.centralizer ((⁅Uq M T L, E₀⁆ : Subgroup G) : Set G) := by
      rw [hQε, hUE, PU.centralizer_map_mulEquiv, map_conj_le_map_conj_iff,
        imM_le_centralizer_iff h.le h.le hcommM] at hQR
      exact hQR
    have hTl : (T.subgroupOf M).map a ≤ MSP.qLine (MSP.commSp ((E₀.subgroupOf M).map a)) :=
      map_le_qLine_M h hd h.le (Subgroup.le_centralizer_iff.1 hTR)
    have hF : 1 < Nat.card F := by rw [hFq]; omega
    have hnotpt : ∀ p : Submodule F (MSP.V4 F), MSP.IsPoint p →
        S5.vIm h.le a (Qv _ (baseB (puAmalgam h.le))) ≠ MSP.qPoint p := by
      intro p hp heq
      rw [puAmalgam.qv_baseB, S5.vIm_imM h] at heq
      exact not_qPoint_le_qLine hF hp hl' ((le_of_eq heq.symm).trans hTl)
    refine ⟨hnotpt, ?_⟩
    rcases h54 G M T L h hmin hb k F _ _ a hd with ⟨-, hline, hJ2⟩ | ⟨-, -, p, hp, hTq⟩
    · rw [S5B.qv_baseA_eq h, S5.jOff_baseA h, S5B.relIndex_imM h.le hJM] at hJ2
      have hJ2' : (2 ^ k) ^ 2 ≤ Nat.card (((S5.jOffM M T L (2 ^ k)).subgroupOf M).map a) :=
        le_of_le_of_eq hJ2 (S5.IsSp4Data.card_imSp hd h hJT).symm
      have hJT' := jOffM_eq_of_le_qLine_M h hd hl' hTl hJ2'
      refine ⟨by rw [S5.jOff_baseA h, hJT', puAmalgam.qv_baseB], hline⟩
    · exact absurd hTq (hnotpt p hp)
  · intro hNT hNc
    rw [hrelN (hN₀T hNT)] at hNc
    have key := commutator_le_of_card_le_M h hd hN₀M hEN₀ hEQ₀ hNc
    rw [hUN, hUE, map_conj_le_map_conj_iff,
      imM_le_imM_iff h.le (commutator_le_of_le (Uq_le h.L_le) hN₀M)]
    exact key
  · intro hNT p hp hTq
    have hTp : (T.subgroupOf M).map a = MSP.qPoint p := by
      rw [puAmalgam.qv_baseB, S5.vIm_imM h] at hTq
      exact hTq
    rw [hrelN (hN₀T hNT)]
    exact card_le_of_qPoint_M h hd hp hTp (hN₀T hNT) hNc₀ hl'

end Vertex

end S512T

end CFSG.Quasithin.MS93

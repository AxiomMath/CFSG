module

public import CFSG.Quasithin.MS93.S33SpShape
public import CFSG.Quasithin.MS93.S5Stmt

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section General

variable {H : Type*} [Group H]

theorem centralizer_singleton_conj (g x : H) :
    Subgroup.centralizer ({(MulAut.conj g).toMonoidHom x} : Set H) =
      (Subgroup.centralizer ({x} : Set H)).map (MulAut.conj g).toMonoidHom := by
  have h1 : ({(MulAut.conj g).toMonoidHom x} : Set H) = (MulAut.conj g).toMonoidHom '' {x} :=
    Set.image_singleton.symm
  rw [← Subgroup.centralizer_closure, h1, ← MonoidHom.map_closure, PU.centralizer_map_mulEquiv,
    Subgroup.centralizer_closure]

theorem exists_mul_of_mem_sup_normalizer {A N : Subgroup H}
    (hAN : A ≤ Subgroup.normalizer (N : Set H)) {x : H} (hx : x ∈ A ⊔ N) :
    ∃ y ∈ A, ∃ n ∈ N, x = y * n := by
  have hx' : x ∈ ((A ⊔ N : Subgroup H) : Set H) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A N hAN] at hx'
  obtain ⟨y, hy, n, hn, hyn⟩ := hx'
  exact ⟨y, hy, n, hn, hyn.symm⟩

end General

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section Elem

variable {F : Type} [Field F] [Fintype F] {A : Subgroup G} {αA : ↥A →* ↥(StatedSp 2 F)}

theorem card_le_relIndex_of_ne_one (h : PUHyp M T L) (hAM : A ≤ M)
    (c : MSP.NatCoord A (Uq M T L) (Uq M T L ⊓ Zq M L) αA) {m : ↥A} (hm : αA m ≠ 1) :
    Fintype.card F ≤ (Subgroup.centralizer ({(m : G)} : Set G)).relIndex (Uq M T L) := by
  set K : Subgroup G := Subgroup.closure {(m : G)} with hK
  have hΓ1 : (K.subgroupOf A).map αA ≠ ⊥ := by
    intro hbot
    apply hm
    have hmem : αA m ∈ (K.subgroupOf A).map αA :=
      ⟨m, Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure rfl), rfl⟩
    rw [hbot] at hmem
    exact hmem
  have hd := finrank_fixSp_le_three hΓ1
  have h1 := card_le_fixSp_mul h hAM c K
  rw [hK, Subgroup.centralizer_closure, MSP.card_V4, MSP.card_fixSp, Nat.card_eq_fintype_card]
    at h1
  have hq1 : 1 < Fintype.card F := Fintype.one_lt_card
  have h2 : Fintype.card F ^ 3 * Fintype.card F ≤ Fintype.card F ^ 3 *
      (Subgroup.centralizer ({(m : G)} : Set G)).relIndex (Uq M T L) := by
    rw [← pow_succ]
    exact h1.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hd))
  exact Nat.le_of_mul_le_mul_left h2 (pow_pos (by omega) 3)

end Elem

theorem relIndex_centralizer_ofA (h : PUHyp M T L) (m : ↥M) {K : Subgroup G} (hK : K ≤ M) :
    (Subgroup.centralizer ({(puAmalgam h.le).ofA m} : Set (puAmalgam h.le).Universal)).relIndex
        (imM h.le K) =
      (Subgroup.centralizer ({(m : G)} : Set G)).relIndex K := by
  have e : Subgroup.centralizer ({(puAmalgam h.le).ofA m} : Set (puAmalgam h.le).Universal) ⊓
      imM h.le K = imM h.le (Subgroup.centralizer ({(m : G)} : Set G) ⊓ K) := by
    ext x
    rw [Subgroup.mem_inf, imM, imM, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨hx, y, hy, rfl⟩
      refine ⟨y, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_subgroupOf.1 hy⟩),
        rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      rw [← map_mul, ← map_mul] at hx
      exact congrArg Subtype.val ((puAmalgam h.le).ofA_injective hx)
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyC, hyK⟩ := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hy)
      refine ⟨?_, y, Subgroup.mem_subgroupOf.2 hyK, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hyC)
  rw [← Subgroup.inf_relIndex_right, e, relIndex_imM h.le hK, Subgroup.inf_relIndex_right]

theorem relIndex_centralizer_ne_two (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    {a : ↥M →* ↥(StatedSp 2 F)} (hd : S5.IsSp4Data M T L k F a) (hk : 2 ≤ k)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) (baseA _) α')
    {t : (puAmalgam h.le).Universal} (ht : t ∈ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1)) :
    (Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal)).relIndex (ZM _ α') ≠ 2 := by
  obtain ⟨-, hcard, -, hnat⟩ := hd
  rw [← h.Uq_inf_Zq] at hnat
  obtain ⟨c⟩ := MSP.nonempty_natCoord hnat
  obtain ⟨g, hgα, hgβ, -, -⟩ := exists_conj_of_isCritical _ h.hyp20 h.critDist_pos hc
  rw [← hgβ, puAmalgam.qv_smul_baseB] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  obtain ⟨m, hmT, rfl⟩ := ht'
  have hZ : ZM (puAmalgam h.le) (baseA _) = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
  rw [← hgα, zm_smul, centralizer_singleton_conj,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective, hZ,
    relIndex_centralizer_ofA h m (Z0q_le M T)]
  intro h2
  have hmT' : (m : G) ∈ T := Subgroup.mem_subgroupOf.1 hmT
  by_cases ham : a m = 1
  ·
    have hmQ := mem_pCoreOf_of_actTriv h hmT' ((image_eq_one_iff h le_rfl c m).1 ham)
    have hle : Z0q M T ≤ Subgroup.centralizer ({(m : G)} : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (h.pCoreOf_le_centralizer_Z0q hmQ) z hz
    rw [Subgroup.relIndex_eq_one.2 hle] at h2
    exact absurd h2 (by norm_num)
  · have h1 := card_le_relIndex_of_ne_one h le_rfl c ham
    have h3 : (Subgroup.centralizer ({(m : G)} : Set G)).relIndex (Uq M T L) ≤
        (Subgroup.centralizer ({(m : G)} : Set G)).relIndex (Z0q M T) :=
      Subgroup.relIndex_le_of_le_right (Uq_le_Z0q h.L_le) Subgroup.index_ne_zero_of_finite
    have h4 : 4 ≤ Fintype.card F := by
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega

theorem not_isHatTriple_of_relIndex_two (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) (baseA _) α')
    (hrel : (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) = 2)
    (t₁ t₂ t₃ : (puAmalgam h.le).Universal) : ¬ S5.IsHatTriple _ (baseA _) α' t₁ t₂ t₃ := by
  rintro ⟨-, -, -, h1, h2, -, hne, hsup, -⟩
  have h20 := h.hyp20
  have hb := h.critDist_pos
  have hc' := ms22_iii _ h20 hb h.centHyp hc
  have hZQ : ZM (puAmalgam h.le) (baseA _) ≤
      Subgroup.normalizer (Qv _ α' : Set (puAmalgam h.le).Universal) :=
    (zm_le_stab_of_isCritical _ h20 hb hc').trans (stab_le_normalizer_qv _ α')
  have hnQ : ∀ {t : (puAmalgam h.le).Universal},
      (Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal)).relIndex (ZM _ α') = 2 →
        t ∉ Qv _ α' := by
    intro t ht htQ
    have hle : ZM (puAmalgam h.le) α' ≤ Subgroup.centralizer ({t} : Set _) := by
      intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp
        (zm_le_centralizer_qv _ h20 (hc.isMVtx_right _ h20) hz) t htQ).symm
    rw [Subgroup.relIndex_eq_one.2 hle] at ht
    exact absurd ht (by norm_num)
  have hmem : ∀ {t}, t ∈ ({t₁, t₂} : Set (puAmalgam h.le).Universal) →
      t ∈ ZM (puAmalgam h.le) (baseA _) ⊔ Qv _ α' := by
    intro t ht
    rw [hsup]
    exact (le_sup_left : Subgroup.closure _ ≤ _) (Subgroup.subset_closure ht)
  have ht₁ := hmem (Set.mem_insert _ _)
  have ht₂ := hmem (Set.mem_insert_of_mem _ rfl)
  obtain ⟨z₁, hz₁, x₁, hx₁, rfl⟩ := exists_mul_of_mem_sup_normalizer hZQ ht₁
  obtain ⟨z₂, hz₂, x₂, hx₂, rfl⟩ := exists_mul_of_mem_sup_normalizer hZQ ht₂
  have hz₁Q : z₁ ∉ Qv _ α' := fun hz => hnQ h1 (mul_mem hz hx₁)
  have hz₂Q : z₂ ∉ Qv _ α' := fun hz => hnQ h2 (mul_mem hz hx₂)
  have hidx : ((Qv _ α').subgroupOf (ZM (puAmalgam h.le) (baseA _))).index = 2 := hrel
  have h12 : z₁ * z₂⁻¹ ∈ Qv _ α' := by
    have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨z₁, hz₁⟩)
      (b := (⟨z₂, hz₂⟩ : ↥(ZM (puAmalgam h.le) (baseA _)))⁻¹)).2 (by
        simp only [Subgroup.mem_subgroupOf, inv_mem_iff]
        exact iff_of_false hz₁Q hz₂Q)
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv] using this
  have hconj : z₂ * (x₁ * x₂⁻¹) * z₂⁻¹ ∈ Qv _ α' :=
    (Subgroup.mem_normalizer_iff.1 (hZQ hz₂) _).1 (mul_mem hx₁ (inv_mem hx₂))
  apply hne
  have e : z₁ * x₁ * (z₂ * x₂)⁻¹ = z₁ * z₂⁻¹ * (z₂ * (x₁ * x₂⁻¹) * z₂⁻¹) := by group
  rw [e]
  exact mul_mem h12 hconj

theorem vIm_eq_map_pre (h : PUHyp M T L) {F : Type} [Field F] (a : ↥M →* ↥(StatedSp 2 F))
    (K : Subgroup (puAmalgam h.le).Universal) :
    S5.vIm h.le a K = ((pre h.le K).subgroupOf M).map a := by
  rw [S5.vIm, pre, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

theorem zHat_eq_of_two_le (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    {a : ↥M →* ↥(StatedSp 2 F)} (hd : S5.IsSp4Data M T L k F a) (hk : 2 ≤ k)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) (baseA _) α') :
    S5.zHat _ (baseA _) α' = ZM _ α' := by
  unfold S5.zHat
  refine le_antisymm inf_le_left (le_inf le_rfl (le_iInf fun t => le_iInf fun ht =>
    le_iInf fun _ => ?_))
  exact absurd ht.2.2.2.1 (relIndex_centralizer_ne_two h hd hk hc ht.1)

theorem shape_of_sp4Data (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    {a : ↥M →* ↥(StatedSp 2 F)} (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) (baseA _) α') :
    ((Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) = 2 ^ k ∧
        S5.zHat _ (baseA _) α' = ZM _ α' ∧
        ∃ p : Submodule F (MSP.V4 F), MSP.IsPoint p ∧ S5.vIm h.le a (ZM _ α') = MSP.xPoint p) ∨
      ((2 ^ k) ^ 2 ≤ (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) ∧
        (2 ^ k) ^ 2 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') ∧
        Module.finrank F (MSP.fixSp (S5.vIm h.le a (ZM _ α'))) ≤ 2) := by
  obtain ⟨hk1, hcard, -, hnat⟩ := id hd
  rw [← h.Uq_inf_Zq] at hnat
  obtain ⟨μ, hμ, hrel₁, hrel₂⟩ := exists_conj_vertex h hc
  rw [vIm_eq_map_pre h a]
  rcases shapes_at h hc hμ hrel₁ hrel₂ le_rfl hnat (pre_le h.le _) le_rfl hnat
      (pre_le h.le _) with ⟨-, ⟨p', hp', hpe'⟩, h1, -⟩ | ⟨h1, h2, -, hd2⟩
  · refine Or.inl ⟨h1.trans hcard, ?_, p', hp', hpe'⟩
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by omega
      unfold S5.zHat
      refine le_antisymm inf_le_left (le_inf le_rfl (le_iInf fun t => le_iInf fun ht =>
        le_iInf fun _ => ?_))
      exact absurd ht (not_isHatTriple_of_relIndex_two h hc (by rw [h1, hcard]; norm_num) _ _ _)
    · exact zHat_eq_of_two_le h hd hk hc
  · rw [hcard] at h1 h2
    exact Or.inr ⟨h1, h2, hd2⟩

theorem of_isHatTriple (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    {a : ↥M →* ↥(StatedSp 2 F)} (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) (baseA _) α') {t₁ t₂ t₃ : (puAmalgam h.le).Universal}
    (ht : S5.IsHatTriple _ (baseA _) α' t₁ t₂ t₃) :
    k = 1 ∧ 4 ≤ (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) ∧
      4 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') ∧
      Module.finrank F (MSP.fixSp (S5.vIm h.le a (ZM _ α'))) ≤ 2 := by
  have hk1 : 1 ≤ k := hd.1
  have hk : k = 1 := by
    by_contra hk
    exact relIndex_centralizer_ne_two h hd (by omega) hc ht.1 ht.2.2.2.1
  subst hk
  rcases shape_of_sp4Data h hd hc with ⟨hrel, -, -⟩ | ⟨h1, h2, h3⟩
  · exact absurd ht (not_isHatTriple_of_relIndex_two h hc (by rw [hrel]; norm_num) _ _ _)
  · exact ⟨rfl, le_of_eq_of_le (by norm_num) h1, le_of_eq_of_le (by norm_num) h2, h3⟩

end CFSG.Quasithin.MS93.S33

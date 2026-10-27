module

public import CFSG.Quasithin.MS93.S5Q2X52Coc
public import CFSG.Quasithin.MS93.S5Q2V
public import CFSG.Quasithin.MS93.S511SMod

public section

namespace CFSG.Quasithin.MS93.S5C

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem xq_inf_centralizer_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) {E : Subgroup G} (hTE : T ≤ Subgroup.normalizer (E : Set G))
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) (hEl : S5.imSp a E ≤ MSP.qLine l)
    (hcard : 2 * Nat.card F < Nat.card (S5.imSp a E)) :
    Xq M ⊓ Subgroup.centralizer (E : Set G) ≤ Uq M T L ⊔ Zq M L := by
  have := hd.charP
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hNn := S5Q2.X52.le_normalizer_uq_sup_cXL h
  have hNX := S5Q2.X52.uq_sup_cXL_le_xq h
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := h.isPGroup.to_le h.pCore_le
  have hYX : Xq M ⊓ Subgroup.centralizer (E : Set G) ≤ Xq M := inf_le_left
  by_contra hY
  obtain ⟨x, hxY, hxN, hxT⟩ := S5.exists_fixed_mod_of_isPGroup h.isPGroup
    (hQ2.to_le ((sup_le hYX hNX).trans (Xq_le_pCoreOf M)))
    (le_normalizer_inf (h.le.trans (le_normalizer_Xq M)) (le_normalizer_centralizer hTE))
    (h.le.trans hNn) ((hYX.trans (Xq_le M)).trans hNn)
    (S5.le_normalizer_of_commute fun n hn y hy => S5.commute_of_mem_Xq (hNX hn) (hYX hy)) hY
  have hxF : x ∈ S5Q2.X52.xFix h := by
    refine ⟨hxY.1, S5Q2.X52.forall_mem_of_L_T h (fun l hl => ?_) hxT⟩
    have := hXL (Subgroup.commutator_mem_commutator hxY.1 hl)
    rw [← commutatorElement_inv]
    exact Subgroup.mem_sup_left ((Uq M T L).inv_mem this)
  obtain ⟨B, m₀, hB, hBm⟩ := S5Q2.X52.exists_cform_of_mem_xFix hd h nv hxF hxN
  have hφ := S5.cocSp_mul hd h nv hxF.1 hxF.2
  have hvan : ∀ g ∈ S5.imSp a E, S5.cocSp hd nv x g = 0 := by
    rintro _ ⟨e, he, rfl⟩
    have e' : (e : ↥M) = ⟨(e : G), e.2⟩ := rfl
    rw [e', S5.cocSp_a hd h nv hxF.1 hxF.2]
    have : ⁅(e : G), x⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.1 hxY.2 _ he
    rw [this, S5.uCoord_one]
  obtain ⟨g₀, rfl⟩ := MSP.exists_map_ln₀_eq hl
  rw [MSP.qLine_map_eq] at hEl
  set J₀ := (S5.imSp a E).map (MulAut.conj g₀⁻¹).toMonoidHom with hJ₀
  have hJ₀eq : J₀.map (MulAut.conj g₀).toMonoidHom = S5.imSp a E := by
    rw [hJ₀, Subgroup.map_map]
    have : ((MulAut.conj g₀).toMonoidHom.comp (MulAut.conj g₀⁻¹).toMonoidHom) =
        MonoidHom.id _ := by
      refine MonoidHom.ext fun y => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        MonoidHom.id_apply]
      group
    rw [this, Subgroup.map_id]
  have hJ₀Q : J₀ ≤ MSP.Q₁ F := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have := hEl hz
    rw [MSP.mem_map_conj] at this
    simpa using this
  have hvan₀ := S5.cform_vanish_of_conj hφ hBm (A := J₀) (g₀ := g₀) (by
    rw [hJ₀eq]
    exact hvan)
  have hle := S5.card_le_of_cform_Q₁ hB (S := (J₀ : Set (MSP.Sp4 F))) hJ₀Q hvan₀
  have hcJ : Nat.card J₀ = Nat.card (S5.imSp a E) :=
    Subgroup.card_map_of_injective (MulAut.conj g₀⁻¹).injective
  have hc : Nat.card (J₀ : Set (MSP.Sp4 F)) = Nat.card J₀ := rfl
  rw [hc, hcJ] at hle
  omega

theorem commute_of_mem_xq_inf_centralizer (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hk : 2 ≤ k) (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) {E : Subgroup G} (hEM : E ≤ M)
    (hTE : T ≤ Subgroup.normalizer (E : Set G)) {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hEl : S5.imSp a E ≤ MSP.qLine l) (hcard : 2 * Nat.card F < Nat.card (S5.imSp a E))
    {x : G} (hx : x ∈ Xq M ⊓ Subgroup.centralizer (E : Set G)) {y : G} (hy : y ∈ M)
    (hyl : a ⟨y, hy⟩ ∈ MSP.qLine l) : y * x = x * y := by
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hZc := S5Q2.zq_le_centralizer_of_two_le h hd hk
  obtain ⟨u, hu, c, hc, rfl⟩ :=
    (S5.mem_Uq_sup_cXL h).1 (xq_inf_centralizer_le h hd hXL hTE hl hEl hcard hx)
  have hcM : ∀ m ∈ M, m * c = c * m := fun m hm => Subgroup.mem_centralizer_iff.1 (hZc hc) m hm
  have huE : u ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h1 := Subgroup.mem_centralizer_iff.1 hx.2 e he
    have h2 := hcM e (hEM he)
    calc e * u = e * (u * c) * c⁻¹ := by group
      _ = u * c * e * c⁻¹ := by rw [h1]
      _ = u * (c * e) * c⁻¹ := by group
      _ = u * (e * c) * c⁻¹ := by rw [h2]
      _ = u * e := by group
  have hv := nv.vec_mem_fixSp ⟨u, hu⟩ huE
  rw [S511S.fixSp_eq_of_le_qLine hl hEl (lt_of_le_of_lt (by omega) hcard)] at hv
  have hfix : MSP.mat (a ⟨y, hy⟩) *ᵥ nv.vec ⟨u, hu⟩ = nv.vec ⟨u, hu⟩ := MSP.mem_fixer.1 hyl _ hv
  have hyu : y * u * y⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_Uq h.le_normalizer hy) u).1 hu
  have hvec := nv.vec_conj ⟨y, hy⟩ ⟨u, hu⟩ hyu
  have h0 : y * u * y⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    have : nv.vec (⟨y * u * y⁻¹, hyu⟩ * (⟨u, hu⟩ : ↥(Uq M T L))⁻¹) = 0 := by
      rw [nv.vec_mul, nv.vec_inv, hvec, hfix, add_neg_cancel]
    exact (nv.vec_eq_zero_iff _).1 this
  have hyu' := hlift y hy u hu h0
  have hyc := hcM y hy
  calc y * (u * c) = (y * u * y⁻¹) * (y * c) := by group
    _ = u * (c * y) := by rw [hyu', hyc]
    _ = u * c * y := by group

theorem commute_of_mem_uq_sup_inf_centralizer (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup G} (hEM : E ≤ M) {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hEl : S5.imSp a E ≤ MSP.qLine l) (hcard : Nat.card F < Nat.card (S5.imSp a E))
    (hodd : 2 ≤ k ∨ ¬ S5.imSp a E ≤ commutator (MSP.Sp4 F))
    {x : G} (hxN : x ∈ Uq M T L ⊔ Zq M L) (hxE : x ∈ Subgroup.centralizer (E : Set G))
    {y : G} (hy : y ∈ M) (hyl : a ⟨y, hy⟩ ∈ MSP.qLine l) : y * x = x * y := by
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  obtain ⟨u, hu, c, hc, rfl⟩ := (S5.mem_Uq_sup_cXL h).1 hxN
  have heu : ∀ e ∈ E, e * u = u * e := by
    intro e he
    have heM := hEM he
    have h1 := Subgroup.mem_centralizer_iff.1 hxE e he
    have hecM : e * c * e⁻¹ ∈ S5.cXL M L :=
      (Subgroup.mem_normalizer_iff.1 (S5.le_normalizer_cXL h heM) c).1 hc
    have heu' : e * u * e⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (hUn heM) u).1 hu
    have hw : e * u * e⁻¹ * u⁻¹ = c * (e * c * e⁻¹)⁻¹ := by
      have e1 : e * u * e⁻¹ = u * c * (e * c * e⁻¹)⁻¹ := by
        calc e * u * e⁻¹ = e * (u * c) * e⁻¹ * (e * c * e⁻¹)⁻¹ := by group
          _ = u * c * e * e⁻¹ * (e * c * e⁻¹)⁻¹ := by rw [h1]
          _ = u * c * (e * c * e⁻¹)⁻¹ := by group
      rw [e1]
      have hcu : c * (e * c * e⁻¹)⁻¹ * u⁻¹ = u⁻¹ * (c * (e * c * e⁻¹)⁻¹) :=
        (S5.commute_of_mem_Xq (S5.cXL_le ((S5.cXL M L).mul_mem hc ((S5.cXL M L).inv_mem hecM)))
          (h.Uq_le_Xq ((Uq M T L).inv_mem hu)))
      calc u * c * (e * c * e⁻¹)⁻¹ * u⁻¹ = u * (c * (e * c * e⁻¹)⁻¹ * u⁻¹) := by group
        _ = u * (u⁻¹ * (c * (e * c * e⁻¹)⁻¹)) := by rw [hcu]
        _ = c * (e * c * e⁻¹)⁻¹ := by group
    have hwL : e * u * e⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      rw [hw]
      exact ((S5.cXL M L).mul_mem hc ((S5.cXL M L).inv_mem hecM)).2
    have := hlift e heM u hu hwL
    calc e * u = e * u * e⁻¹ * e := by group
      _ = u * e := by rw [this]
  have hec : ∀ e ∈ E, e * c = c * e := by
    intro e he
    have h1 := Subgroup.mem_centralizer_iff.1 hxE e he
    have h2 := heu e he
    calc e * c = u⁻¹ * (e * (u * c)) := by rw [← mul_assoc e u c, h2]; group
      _ = u⁻¹ * (u * c * e) := by rw [h1]
      _ = c * e := by group
  have hcZ : c ∈ Subgroup.centralizer (M : Set G) := by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · have hk1 : k = 1 := by
        have := hd.1
        omega
      subst hk1
      rcases hodd with hk2 | hJo
      · omega
      · obtain ⟨_, ⟨e, he, rfl⟩, heo⟩ := Set.not_subset.1 hJo
        exact S5Q2.mem_centralizer_of_commute h hd heo hc (hec e (Subgroup.mem_subgroupOf.1 he))
    · exact S5Q2.zq_le_centralizer_of_two_le h hd hk hc
  have huE : u ∈ Subgroup.centralizer (E : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun e he => heu e he
  have hv := nv.vec_mem_fixSp ⟨u, hu⟩ huE
  rw [S511S.fixSp_eq_of_le_qLine hl hEl hcard] at hv
  have hfix : MSP.mat (a ⟨y, hy⟩) *ᵥ nv.vec ⟨u, hu⟩ = nv.vec ⟨u, hu⟩ := MSP.mem_fixer.1 hyl _ hv
  have hyu : y * u * y⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (hUn hy) u).1 hu
  have hvec := nv.vec_conj ⟨y, hy⟩ ⟨u, hu⟩ hyu
  have h0 : y * u * y⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    have : nv.vec (⟨y * u * y⁻¹, hyu⟩ * (⟨u, hu⟩ : ↥(Uq M T L))⁻¹) = 0 := by
      rw [nv.vec_mul, nv.vec_inv, hvec, hfix, add_neg_cancel]
    exact (nv.vec_eq_zero_iff _).1 this
  have hyu' := hlift y hy u hu h0
  have hyc : y * c = c * y := Subgroup.mem_centralizer_iff.1 hcZ y hy
  calc y * (u * c) = (y * u * y⁻¹) * (y * c) := by group
    _ = u * (c * y) := by rw [hyu', hyc]
    _ = u * c * y := by group

omit [Finite G] [Fintype F] in
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

theorem xm_inf_centralizer_le_centralizer_vPre (h : PUHyp M T L) (h32 : S32)
    (hd : S5.IsSp4Data M T L k F a) (hk : 2 ≤ k)
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ Qv _ (baseB (puAmalgam h.le)))
    (hTE : Qv _ (baseB (puAmalgam h.le)) ≤
      Subgroup.normalizer (E : Set (puAmalgam h.le).Universal))
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) (hEl : E ≤ S5.vPre h.le a (MSP.qLine l))
    (hcard : (2 ^ k) ^ 2 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex E) :
    XM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal) := by
  have hXL : ⁅Xq M, L⁆ ≤ Uq M T L := (h32 G M T L h).2.1
  rw [puAmalgam.qv_baseB] at hE hTE
  obtain ⟨E₀, hE₀T, hE₀M, rfl⟩ := S5.exists_eq_imM h.le hE
  have hTE₀ : T ≤ Subgroup.normalizer (E₀ : Set G) := le_normalizer_of_imM h.le h.le hE₀M hTE
  have hEl₀ : S5.imSp a E₀ ≤ MSP.qLine l := by
    rw [imM, S5.vPre, Subgroup.map_le_map_iff_of_injective (puAmalgam h.le).ofA_injective] at hEl
    exact Subgroup.map_le_iff_le_comap.2 hEl
  have hcard₀ : 2 * Nat.card F < Nat.card (S5.imSp a E₀) := by
    rw [hd.card_imSp h hE₀T, hd.nat_card_eq]
    rw [S5.qv_baseA_eq h, S5.relIndex_imM h.le hE₀M] at hcard
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    nlinarith
  rw [S5.xm_baseA_eq h, ← imM_inf_centralizer h.le _ hE₀M]
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact commute_of_mem_xq_inf_centralizer h hd hk hXL hE₀M hTE₀ hl hEl₀ hcard₀
    (Subgroup.mem_subgroupOf.1 hx) y.2 hy

end CFSG.Quasithin.MS93.S5C

module

public import CFSG.Quasithin.Vol2.Ch10SecC9C3
public import CFSG.Quasithin.Vol2.Ch10SecC9Out
public import CFSG.Quasithin.Vol2.Ch10SecC9B

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem omegaOne_le_omegaOneCenterOf {w : G} (hw : w ∈ T) :
    quasithinOmegaOneCenter T ≤ omegaOneCenterOf (T ⊓ Subgroup.centralizer ({w} : Set G)) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro z ⟨⟨hzT, hzc⟩, hz2⟩
  refine Subgroup.subset_closure ⟨⟨⟨hzT, ?_⟩, Subgroup.centralizer_le
    (SetLike.coe_subset_coe.mpr inf_le_left) hzc⟩, hz2⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzc w hw).symm

omit [Finite G] in
theorem omegaOne_le_centralizer : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1.2

theorem centralizer_Z_le (hyp : Hyp10 G T L I) (h1026 : Stmt10_2_6)
    (hZL : ⁅quasithinOmegaOneCenter T, L⁆ = ⊥) (hV : fsuVM T L I ≠ ⊥) :
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ fsuM T L := by
  have hZT : quasithinOmegaOneCenter T ≤ T := (Subgroup.closure_le _).mpr fun _ hz => hz.1.1
  have hZc := omegaOne_le_centralizer (T := T)
  have hLZ : L ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [← Subgroup.le_centralizer_iff]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hZL
  have hTZ : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [← Subgroup.le_centralizer_iff]
    exact hZc
  have hL0Z : fsuL0 T L ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨h, hh, l, hl, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTZ hh) (hLZ hl)) (Subgroup.inv_mem _ (hTZ hh))
  obtain ⟨z, hz, hz1, hzc⟩ := exists_mem_centralizer_ne_one hyp.fsu.sylow.1 (SecA.fsuVM_le_T hyp)
    le_rfl (SecA.le_normalizer_fsuVM T L I) hV
  have hZ1 : quasithinOmegaOneCenter T ≠ ⊥ := fun h => by
    have : z ∈ quasithinOmegaOneCenter T :=
      Subgroup.subset_closure ⟨⟨SecA.fsuVM_le_T hyp hz, hzc⟩, (SecA.isElemAbelian_fsuVM hyp).2 z hz⟩
    rw [h, Subgroup.mem_bot] at this
    exact hz1 this
  refine centralizer_le_of_isUniqueM hyp h1026 (hyp.fsu.sylow.1.to_le hZT) hZ1 ?_
    (sup_le hL0Z (inf_le_left.trans hTZ))
  intro x hx
  exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZT) (hZc hx)

theorem thompsonJ_le_of_conj {u w m : G}
    (hJ : thompsonJ T ≤ Subgroup.centralizer ({u} : Set G))
    (hcon : ∀ x ∈ T ⊓ Subgroup.centralizer ({u} : Set G),
      m * x * m⁻¹ ∈ T ⊓ Subgroup.centralizer ({w} : Set G)) :
    thompsonJ T ≤ Subgroup.centralizer ({w} : Set G) := by
  have hJT : thompsonJ T ≤ T := B6.thompsonJ_le T
  have em : ∀ y : G, m * (m⁻¹ * y * m) * m⁻¹ = y := fun y => by group
  have h1 : B6.conjSub m (thompsonJ T) ≤ T := fun y hy => by
    rw [B6.mem_conjSub] at hy
    have := hcon _ ⟨hJT hy, hJ hy⟩
    rw [em] at this
    exact this.1
  have h2 := conjSub_thompsonJ_eq h1
  intro y hy
  have hy' : y ∈ B6.conjSub m (thompsonJ T) := by rw [h2]; exact hy
  rw [B6.mem_conjSub] at hy'
  have := hcon _ ⟨hJT hy', hJ hy'⟩
  rw [em] at this
  exact this.2

theorem claim_case3_ne (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1013 : Stmt10_1_3) (h1026 : Stmt10_2_6) (h1028 : Stmt10_2_8)
    (h484 : ASInputs.AS_B_4_8_four) (h3210 : TmpL6_3_2_10_nine) (h3 : Case10_1_1Three T L I)
    (hne : cV1 T L I ≠ ⊥) (hne' : fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {v : G}
    (hv : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hv1 : v ≠ 1)
    (hvM : ¬ Subgroup.centralizer ({v} : Set G) ≤ fsuM T L) : ∃ w, ClaimOut T L I t w := by
  have hL : LBarL32 L := h3.1
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, -, hV2, -⟩ := hdec t ht htn
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV2V : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I := commutator_le_left_of_le_normalizer
    ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hvV := hV2V hv
  have hVne : fsuVM T L I ≠ ⊥ := fun h => hv1 (by rw [h] at hvV; exact Subgroup.mem_bot.mp hvV)
  have hMC := SecA.le_normalizer_centralizer (V := fsuL0 T L) (X := fsuM T L) le_rfl
  have hconjC : ∀ g ∈ fsuM T L, ∀ x, g * x * g⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G) →
      x ∈ Subgroup.centralizer (fsuL0 T L : Set G) := fun g hg x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (hMC ((fsuM T L).inv_mem hg)) _).mp hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
  have hvC : v ∉ Subgroup.centralizer (fsuL0 T L : Set G) := fun h =>
    hvM (centralizer_le_of_mem_fsuCVM_case3 h1026 h1028 hyp hL hne' ⟨hvV, h⟩ hv1)
  obtain ⟨U₂, hU₂⟩ := exists_isU hyp hV2V
  obtain ⟨l, hl, hlU⟩ := exists_conj_mem_U h37 h38 hyp h1011 h484 h3 hne ht htn hU₂ hv hvC
  have hlM : l ∈ fsuM T L := SecA.fsuL0_le_fsuM T L (SecA.conjugate_le_fsuL0 ht hl)
  have huC : l * v * l⁻¹ ∉ Subgroup.centralizer (fsuL0 T L : Set G) := fun h =>
    hvC (hconjC l hlM v h)
  have huW := hU₂.1 hlU
  have huV1 : l * v * l⁻¹ ∉ fsuUL T L I := fun h =>
    huC (inf_V2_le_fsuCVM hyp h1011 ht htn ⟨h, huW⟩).2
  have huM : ¬ Subgroup.centralizer ({l * v * l⁻¹} : Set G) ≤ fsuM T L := by
    rwa [centralizer_conj_le_iff hlM]
  have hJu := thompsonJ_le_centralizer_of_mem_U h37 h38 hyp h1011 h1012 h484 h3210 h3 hne ht htn
    hU₂ hlU huC
  obtain ⟨m, hm, hwW, hwV1, hSyl, hcon⟩ := exists_conj_in_V2 h37 h38 hyp ht htn huW huV1
  have hJw := thompsonJ_le_of_conj hJu hcon
  have hwU := mem_U_of_thompsonJ_le h37 h38 hyp h1011 h1012 h484 h3210 h3 hne ht htn hU₂ hwW hJw
  have hwC : m * (l * v * l⁻¹) * m⁻¹ ∉ Subgroup.centralizer (fsuL0 T L : Set G) := fun h =>
    huC (hconjC m hm _ h)
  have hwV := hV2V hwW
  have hwM : ¬ Subgroup.centralizer ({m * (l * v * l⁻¹) * m⁻¹} : Set G) ≤ fsuM T L := by
    rwa [centralizer_conj_le_iff hm]
  obtain ⟨U₁, hU₁⟩ := exists_isU hyp (commutator_le_left_of_le_normalizer hLN)
  obtain ⟨R₁, hR₁⟩ := exists_isR (T := T) (L := L) (I := I) L U₁
  obtain ⟨R₂, hR₂⟩ := exists_isR (T := T) (L := L) (I := I) (CFSG.conjugate L t) U₂
  have h28 := h1028 G T L I hyp hL hne'
  have hZw := (h28.2.2.2.2 t ht htn U₁ U₂ R₁ R₂ hU₁ hU₂ hR₁ hR₂ ⟨_, hwV⟩ hwU hwC).2.2.2
  have hLZw : L ≤ Subgroup.centralizer
      (omegaOneCenterOf (T ⊓ Subgroup.centralizer ({m * (l * v * l⁻¹) * m⁻¹} : Set G)) :
        Set G) := by
    rw [hZw, Subgroup.le_centralizer_iff]
    refine sup_le ?_ ((Subgroup.zpowers_le).mpr (hV2 hwW))
    rw [h28.2.2.1]
    exact inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
      (SecA.le_fsuL0 T L)))
  have hCZw := (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
    (omegaOne_le_omegaOneCenterOf (SecA.fsuVM_le_T hyp hwV)))).trans
    (centralizer_Z_le hyp h1026 h28.1 hVne)
  have hwZw : m * (l * v * l⁻¹) * m⁻¹ ∈
      omegaOneCenterOf (T ⊓ Subgroup.centralizer ({m * (l * v * l⁻¹) * m⁻¹} : Set G)) := by
    rw [hZw]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hNZw := normalizer_le_of_centralizer_le h37 h38 hyp h1011 h1013 h1026 ht htn hwW hwC hwZw
    hLZw hCZw
  have hNTw := (normalizer_le_normalizer_of_map_mulEquiv omegaOneCenterOf_map_mulEquiv _).trans
    hNZw
  exact ⟨_, hwW, hwV1, hwM, isSylowTwoOf_of_normalizer_le hSyl (inf_le_right.trans hNTw), hJw,
    fun _ s hs => (hU₂.2 _ hwW).mp hwU s hs⟩

end CFSG.Quasithin.Vol2.Ch10.SecC

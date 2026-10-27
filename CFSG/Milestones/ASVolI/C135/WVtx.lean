module

public import CFSG.Quasithin.MS93.S45B12
public import CFSG.Quasithin.MS93.S45Q4PD

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S45
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]
  {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)}

theorem burnsideC134w_inf_centralizer_ltil_le_zloc (c : Ctx M T L φ) (h14 : MS14AS)
    (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4) {p p' : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}
    (hp : IsGoodPath _ p N) (hp' : IsGoodPath _ p' N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a)
    (haN : a + 30 ≤ N) (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU1 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)))
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1))) :
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓
        Subgroup.centralizer (Ltil c.hyp.le L (p a) : Set (puAmalgam c.hyp.le).Universal) ≤
      Zloc c.hyp.le L (p a) := by
  have h := c.hyp
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 34 := ⟨a - 34, by omega⟩
  have hk : Even k := (Nat.even_add.mp ha).mpr (by decide)
  have hα := c.isMVtx_of_isGoodPath hp (k := k + 34) (by omega) ha
  obtain ⟨ψ, hψs, hψ, hT⟩ := c.exists_coord_qv hα (hp.adj (k + 34) (by omega))
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hα hψs hψ
  have hdB := c.isSum_bloc hα hd
  have hdt := c.dual_eq_true hp (x := k + 28) (hk.add (by decide)) (by omega) (by omega) hψs hψ hdB
  subst hdt
  obtain ⟨hsup2, hinf2, h₁m, h₂m⟩ :=
    c.mid_layer h14 hSQ hZV hQ4 hp ha (by omega) (by omega) hp' hpp' hU1 hU3 hψs hψ hT
  obtain ⟨hinf3, h₁t, h₂t⟩ := c.top_layer h14 hSQ hZV hQ4 hp ha h34 haN hp' hpp' hU1 hU3 hψs hψ
  have hF7 := c.commutator_qv_ltil_le_top' hZV hQ4 hp hp' ha h34 haN hpp' hU3
  have hXQ := c.top_le_qv hp hp' ha (by omega) hpp'
  have hLt := c.exists_ltil_toSL3_eq hα hψs hψ
  have hLs : Ltil h.le L (p (k + 34)) ≤ stab (puAmalgam h.le) (p (k + 34)) := ltil_le_stab h _
  have hγ := c.isMVtx_of_isGoodPath hp (k := k + 34 + 2) (by omega) (ha.add even_two)
  have hd2 : (puAmalgam h.le).treeGraph.dist (p (k + 34)) (p (k + 34 + 2)) = 2 := by
    rw [hp.dist_eq' (i := k + 34) (j := k + 34 + 2) (by omega) (by omega)]; omega
  have hWhs : whv h (p (k + 34)) (p (k + 34 + 2)) ≤ stab (puAmalgam h.le) (p (k + 34)) :=
    (c.whv_le_qv_of_dist hγ hd2 (by simp)).trans (qv_le_stab _ _)
  intro x hx
  obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxl : ∀ l ∈ Ltil h.le L (p (k + 34)), ⁅x, l⁆ = 1 := fun l hl => by
    rw [commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_centralizer_iff.mp hxC l hl).symm
  have hxW : x ∈ whv h (p (k + 34)) (p (k + 34 + 2)) := by
    refine mem_of_forall_commutator_eq_one h₁t h₂t hinf3 ?_ hLs hLt (hF7 hxV) hxl
    refine sup_le ?_ hWhs
    exact (Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_sup
      (S4A.le_normalizer_conjCl _ _) (S4A.le_normalizer_conjCl _ _))).trans
      ((le_sup_left.trans hXQ).trans (qv_le_stab _ _))
  have hxVh : x ∈ Vcirc h.le L (p (k + 34)) ⊔ ZM _ (p (k + 34)) :=
    mem_of_forall_commutator_eq_one h₁m h₂m hinf2 ((le_sup_left.trans hsup2.le).trans hWhs) hLs
      hLt (hsup2 ▸ hxW) hxl
  have hxZ : x ∈ ZM (puAmalgam h.le) (p (k + 34)) :=
    mem_z_of_forall_commutator_mem' hd hLt hxVh fun l hl => by rw [hxl l hl]; exact one_mem _
  rw [c.zloc_eq_zm_inf_centralizer hα]
  exact Subgroup.mem_inf.mpr ⟨hxZ, hxC⟩

theorem burnsideC134w_center_le_uloc_sup (c : Ctx M T L φ) (h14 : MS14AS) (hSQ : SQTKQuot)
    (hZV : c.HZV) (hQ4 : c.HQ4) {p p' : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}
    (hp : IsGoodPath _ p N) (hp' : IsGoodPath _ p' N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a)
    (haN : a + 30 ≤ N) (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU1 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)))
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1))) :
    centerOf ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ≤
      Uloc c.hyp.le L (p a) ⊔
        Zloc c.hyp.le L (p a) ⊓ ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ := by
  have h := c.hyp
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hZ := c.center_le_zm h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3
  have hQs : Qv (puAmalgam h.le) (p a) ≤ stab (puAmalgam h.le) (p a) := qv_le_stab _ _
  have hUZ : Uloc h.le L (p a) ≤ ZM _ (p a) := uloc_le_zm h c.full hα
  have hZQ : ZM (puAmalgam h.le) (p a) ≤ Qv _ (p a) :=
    zm_le_qv_of_dist_lt _ hα (by simp [c.b8])
  have hZc := zloc_le_centralizer_stab h c.full hα
  have hUn : Uloc h.le L (p a) ≤ Subgroup.normalizer (Zloc h.le L (p a) : Set _) :=
    (hUZ.trans (hZQ.trans hQs)).trans (c.stab_le_normalizer_of_le_centralizer hZc)
  have hUL : ⁅Uloc h.le L (p a), Ltil h.le L (p a)⁆ = Uloc h.le L (p a) :=
    c.commutator_uloc_ltil hα
  have hUV : Uloc h.le L (p a) ≤ ⁅Qv (puAmalgam h.le) (p a), Ltil h.le L (p a)⁆ := by
    rw [← hUL]
    exact Subgroup.commutator_mono (hUZ.trans hZQ) le_rfl
  have hle : centerOf ⁅Qv (puAmalgam h.le) (p a), Ltil h.le L (p a)⁆ ≤
      ⁅Qv (puAmalgam h.le) (p a), Ltil h.le L (p a)⁆ ⊓ ZM _ (p a) := le_inf inf_le_left hZ
  rw [zm_eq_uloc_sup_zloc h c.full hα, inf_comm, sup_inf_eq_of_le hUV hUn] at hle
  exact hle

theorem burnsideC134w_case13W_vertex (c : Ctx M T L φ) (h14 : MS14AS) (hSQ : SQTKQuot)
    (hZV : c.HZV) (hQ4 : c.HQ4) {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}
    (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a) (haN : a + 30 ≤ N)
    {ψ : ↥(stab (puAmalgam c.hyp.le) (p a)) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ (p a)) (Uloc c.hyp.le L (p a)) ⊥ ψ false 1)
    (hT : natImage ψ (Qv (puAmalgam c.hyp.le) (p (a + 1))) = rootGroup 1 0 ⊔ rootGroup 2 0) :
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓
        Subgroup.centralizer (Ltil c.hyp.le L (p a) : Set _) ≤ Zloc c.hyp.le L (p a) ∧
      centerOf ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ =
        Uloc c.hyp.le L (p a) ⊔ ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓
          Subgroup.centralizer (Ltil c.hyp.le L (p a) : Set _) ∧
      ⁅centerOf ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆,
        Ltil c.hyp.le L (p a)⁆ = Uloc c.hyp.le L (p a) ∧
      IsSumOfNaturalModulesVia (stab _ (p a))
        (⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓
          (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)))
        (centerOf ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆) ψ true 1 ∧
      IsSumOfNaturalModulesVia (stab _ (p a))
        (⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓
          Subgroup.centralizer (Vcirc c.hyp.le L (p a) : Set _))
        (⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓
          (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a))) ψ true 2 ∧
      IsSumOfNaturalModulesVia (stab _ (p a))
        ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆
        (⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓
          Subgroup.centralizer (Vcirc c.hyp.le L (p a) : Set _)) ψ false 2 := by
  have h := c.hyp
  have h20 := h.hyp20
  have : CharP F 2 := c.charP
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 34 := ⟨a - 34, by omega⟩
  have hk : Even k := (Nat.even_add.mp ha).mpr (by decide)
  have hα := c.isMVtx_of_isGoodPath hp (k := k + 34) (by omega) ha
  obtain ⟨p', hp', hpp', hU1, hU3⟩ := c.exists_branch hp ha (by omega) (by omega)
  have hB4 := c.inf_centralizer_vcirc_le_whv h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3
  have hB5 := c.commutator_qv_ltil_le_top hZV hp hp' ha h34 haN hpp' hU3
  have hW1 := burnsideC134w_inf_centralizer_ltil_le_zloc c h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp'
    hU1 hU3
  have hW2 := burnsideC134w_center_le_uloc_sup c h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3
  set Qα := Qv (puAmalgam h.le) (p (k + 34)) with hQα
  set Lt := Ltil h.le L (p (k + 34)) with hLt
  set V := ⁅Qα, Lt⁆ with hV
  set U := Uloc h.le L (p (k + 34)) with hU
  set Zl := Zloc h.le L (p (k + 34)) with hZl
  set Z := ZM (puAmalgam h.le) (p (k + 34)) with hZ
  set Vc := Vcirc h.le L (p (k + 34)) with hVc
  set Vh := Vc ⊔ Z with hVh
  set Wh := whv h (p (k + 34)) (p (k + 34 + 2)) with hWh
  set X₁ := conjCl (stab (puAmalgam h.le) (p (k + 34)))
    (Vcirc h.le L (p (k + 34 + 4)) ⊔ ZM _ (p (k + 34 + 4))) ⊔ Wh with hX₁
  set X₂ := conjCl (stab (puAmalgam h.le) (p (k + 34)))
    (Vcirc h.le L (p' (k + 34 + 4)) ⊔ ZM _ (p' (k + 34 + 4))) ⊔ Wh with hX₂
  set X₁' := ⁅X₁, stab (puAmalgam h.le) (p (k + 34))⁆ ⊔ Wh with hX₁'
  set X₂' := ⁅X₂, stab (puAmalgam h.le) (p (k + 34))⁆ ⊔ Wh with hX₂'
  have hpa : p' (k + 34) = p (k + 34) := hpp' (k + 34) (by omega)
  have hpa2 : p' (k + 34 + 2) = p (k + 34 + 2) := hpp' (k + 34 + 2) (by omega)
  have hγ := c.isMVtx_of_isGoodPath hp (k := k + 34 + 2) (by omega) (ha.add even_two)
  have hQs : Qα ≤ stab (puAmalgam h.le) (p (k + 34)) := qv_le_stab _ _
  have hKQ : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Qα : Set _) :=
    stab_le_normalizer_qv _ _
  have hLs : Lt ≤ stab (puAmalgam h.le) (p (k + 34)) := ltil_le_stab h _
  have hKL : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Lt : Set _) :=
    stab_le_normalizer_ltil h _
  have hKV : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (V : Set _) :=
    le_normalizer_commutator hKQ hKL
  have hVQ : V ≤ Qα := Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hKQ)
  have hKU : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (U : Set _) := hψ.1
  have hKZ : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Z : Set _) :=
    stab_le_normalizer_zm _ _
  have hKVc : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Vc : Set _) :=
    c.stab_le_normalizer_vcirc _
  have hKVh : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Vh : Set _) :=
    le_normalizer_sup hKVc hKZ
  have hKWh : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Wh : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hZQ : Z ≤ Qα := zm_le_qv_of_dist_lt _ hα (by simp [c.b8])
  have hVvQ : Vv (puAmalgam h.le) (p (k + 34)) ≤ Qα := c.vv_le_qv' hα
  have hUZ : U ≤ Z := uloc_le_zm h c.full hα
  have hZloc : Zl ≤ Z := zloc_le_zm h c.full hα
  have hZc := zloc_le_centralizer_stab h c.full hα
  have hUL : ⁅U, Lt⁆ = U := c.commutator_uloc_ltil hα
  have hUVc : U ≤ Vc := by
    rw [← hUL]
    exact Subgroup.commutator_mono (hUZ.trans (le_sup_right.trans (c.vhat_le_vv hα))) le_rfl
  have hVcV : Vc ≤ V := Subgroup.commutator_mono hVvQ le_rfl
  have hUV : U ≤ V := hUVc.trans hVcV
  have hZcen : Z ≤ Subgroup.centralizer (Qα : Set _) := zm_le_centralizer_qv _ h20 hα
  have hHZ : V ⊓ Subgroup.centralizer (Lt : Set _) ≤ Zl := hW1
  have hHc : V ⊓ Subgroup.centralizer (Lt : Set _) ≤ Subgroup.centralizer (Lt : Set _) :=
    inf_le_right
  have hHV : V ⊓ Subgroup.centralizer (Lt : Set _) ≤ V := inf_le_left
  have hF3 : centerOf V = U ⊔ V ⊓ Subgroup.centralizer (Lt : Set _) := by
    refine le_antisymm (hW2.trans (sup_le_sup_left ?_ _))
      (le_inf (sup_le hUV hHV) ?_)
    · rw [inf_comm]
      exact inf_le_inf_left _ (hZc.trans (Subgroup.centralizer_le hLs))
    · exact (sup_le hUZ (hHZ.trans hZloc)).trans (hZcen.trans (Subgroup.centralizer_le hVQ))
  have hVZ : V ⊓ Z = centerOf V := by
    refine le_antisymm ?_ ?_
    · exact le_inf inf_le_left (inf_le_right.trans (hZcen.trans (Subgroup.centralizer_le hVQ)))
    · exact le_inf inf_le_left (hW2.trans (sup_le hUZ (inf_le_left.trans hZloc)))
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hα hψs hψ
  have hdB := c.isSum_bloc hα hd
  have hdt := c.dual_eq_true hp (x := k + 28) (hk.add (by decide)) (by omega) (by omega) hψs hψ hdB
  subst hdt
  have hWhQ : Wh ≤ Qα := conjCl_le_of_le_normalizer ((c.vhat_le_vv hγ).trans (vi_le_qv _ (by
    rw [tdist_comm, hp.dist_eq' (i := k + 34) (j := k + 34 + 2) (by omega) (by omega), c.b8]
    omega))) hKQ
  have hVhWh : Vh ≤ Wh := c.vhat_le_whv' hZV hp ha (by omega) (by omega)
  obtain ⟨hsup2, hinf2, h₁m, h₂m⟩ :=
    c.mid_layer h14 hSQ hZV hQ4 hp ha (by omega) (by omega) hp' hpp' hU1 hU3 hψs hψ hT
  have hL2 : IsSumOfNaturalModulesVia (stab (puAmalgam h.le) (p (k + 34))) Wh Vh ψ true 2 :=
    S46.isSumOfNaturalModulesVia_two h₁m h₂m hKWh ((hWhQ.trans hQs).trans h₁m.1)
      ((hWhQ.trans hQs).trans h₂m.1) hinf2 hsup2
  obtain ⟨hinf3, h₁t, h₂t⟩ := c.top_layer h14 hSQ hZV hQ4 hp ha h34 haN hp' hpp' hU1 hU3 hψs hψ
  have hμ := c.isMVtx_of_isGoodPath hp (k := k + 34 + 4) (by omega) (ha.add (by decide))
  have hμ' := c.isMVtx_of_isGoodPath hp' (k := k + 34 + 4) (by omega) (ha.add (by decide))
  have hX₁Q : X₁ ≤ Qα := by
    refine sup_le (conjCl_le_of_le_normalizer ((c.vhat_le_vv hμ).trans (vi_le_qv _ ?_)) hKQ)
      hWhQ
    rw [tdist_comm, hp.dist_eq' (i := k + 34) (j := k + 34 + 4) (by omega) (by omega), c.b8]
    omega
  have hX₂Q : X₂ ≤ Qα := by
    refine sup_le (conjCl_le_of_le_normalizer ((c.vhat_le_vv hμ').trans (vi_le_qv _ ?_)) hKQ)
      hWhQ
    rw [← hpa, tdist_comm, hp'.dist_eq' (i := k + 34) (j := k + 34 + 4) (by omega) (by omega),
      c.b8]
    omega
  have hX₁s : X₁ ≤ stab (puAmalgam h.le) (p (k + 34)) := hX₁Q.trans hQs
  have hX₂s : X₂ ≤ stab (puAmalgam h.le) (p (k + 34)) := hX₂Q.trans hQs
  have hX₁'X₁ : X₁' ≤ X₁ := sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp
    (le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hKWh)) le_sup_right
  have hX₂'X₂ : X₂' ≤ X₂ := sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp
    (le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hKWh)) le_sup_right
  have hL3 : IsSumOfNaturalModulesVia (stab (puAmalgam h.le) (p (k + 34))) (X₁' ⊔ X₂') Wh ψ
      false 2 :=
    S46.isSumOfNaturalModulesVia_two h₁t h₂t (le_normalizer_sup h₁t.1 h₂t.1)
      ((sup_le (hX₁'X₁.trans hX₁s) (hX₂'X₂.trans hX₂s)).trans h₁t.1)
      ((sup_le (hX₁'X₁.trans hX₁s) (hX₂'X₂.trans hX₂s)).trans h₂t.1) hinf3 rfl
  have hKX₁' : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (X₁' : Set _) := h₁t.1
  have hKX₂' : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (X₂' : Set _) := h₂t.1
  have hKXt : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer ((X₁' ⊔ X₂' :
      Subgroup _) : Set _) := le_normalizer_sup hKX₁' hKX₂'
  have hF9 : (V ⊓ Wh) ⊔ Vh = Wh := by
    refine le_antisymm (sup_le inf_le_right hVhWh) ?_
    refine (show Wh ≤ _ from hsup2.symm.le).trans (sup_le ?_ ?_)
    · rw [← c.sup_inf_eq_of_dual hα hψs hψ h₁m hKV (Subgroup.commutator_mono
        ((le_sup_left.trans hsup2.le).trans hWhQ) le_rfl)]
      exact sup_le_sup_right (inf_le_inf_left _ (le_sup_left.trans hsup2.le)) _
    · rw [← c.sup_inf_eq_of_dual hα hψs hψ h₂m hKV (Subgroup.commutator_mono
        ((le_sup_right.trans hsup2.le).trans hWhQ) le_rfl)]
      exact sup_le_sup_right (inf_le_inf_left _ (le_sup_right.trans hsup2.le)) _
  have hV6 : X₁ ⊔ X₂ ≤ conjCl (stab (puAmalgam h.le) (p (k + 34)))
      (whv h (p (k + 34 + 2)) (p (k + 34))) := by
    have e : whv h (p (k + 34 + 2)) (p (k + 34 + 4)) = whv h (p (k + 34 + 2)) (p (k + 34)) :=
      c.whv_eq_of_isGoodPath hp (a := k + 34 + 2) (ha.add even_two) (by omega) (by omega)
    have hγγ : Vcirc h.le L (p (k + 34 + 2)) ⊔ ZM _ (p (k + 34 + 2)) ≤
        whv h (p (k + 34 + 2)) (p (k + 34)) := by
      rw [← e]; exact c.vhat_le_whv' hZV hp (a := k + 34 + 2) (ha.add even_two) (by omega)
        (by omega)
    have hμγ : Vcirc h.le L (p (k + 34 + 4)) ⊔ ZM _ (p (k + 34 + 4)) ≤
        whv h (p (k + 34 + 2)) (p (k + 34)) := by
      rw [← e]; exact c.vhat_le_whv_self
    have hμ'γ : Vcirc h.le L (p' (k + 34 + 4)) ⊔ ZM _ (p' (k + 34 + 4)) ≤
        whv h (p (k + 34 + 2)) (p (k + 34)) := by
      have e' : whv h (p' (k + 34 + 2)) (p' (k + 34 + 4)) =
          whv h (p' (k + 34 + 2)) (p' (k + 34)) :=
        c.whv_eq_of_isGoodPath hp' (a := k + 34 + 2) (ha.add even_two) (by omega) (by omega)
      rw [hpa, hpa2] at e'
      rw [← e']; exact c.vhat_le_whv_self
    have hWhγ : Wh ≤ conjCl (stab (puAmalgam h.le) (p (k + 34)))
        (whv h (p (k + 34 + 2)) (p (k + 34))) := conjCl_mono hγγ
    exact sup_le (sup_le (conjCl_mono hμγ) hWhγ) (sup_le (conjCl_mono hμ'γ) hWhγ)
  have hDD : ⁅X₁ ⊔ X₂, X₁ ⊔ X₂⁆ ≤ X₁' ⊔ X₂' :=
    ((Subgroup.commutator_mono hV6 hV6).trans
      (c.commutator_vsix_le hZV hQ4 hp ha h34 (by omega))).trans (le_sup_right.trans le_sup_left)
  have hDL : ⁅X₁ ⊔ X₂, Lt⁆ ≤ X₁' ⊔ X₂' := by
    refine S46.commutator_sup_le_of_le_normalizer hKXt hX₁s hX₂s ?_ ?_
    · exact ((Subgroup.commutator_mono le_rfl hLs).trans le_sup_left).trans le_sup_left
    · exact ((Subgroup.commutator_mono le_rfl hLs).trans le_sup_left).trans le_sup_right
  have hF7 : V ≤ X₁' ⊔ X₂' := by
    rw [hV, Subgroup.commutator_le]
    intro q hq l hl
    exact commutator_mem_of_perfect (S4A.ltil_perfect h hα)
      (sup_le (hX₁'X₁.trans le_sup_left) (hX₂'X₂.trans le_sup_right)) hDD hDL
      (fun l hl => hB5 (Subgroup.commutator_mem_commutator hq hl)) hl
  have hKVW : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer ((V ⊔ Wh : Subgroup _) :
      Set _) := le_normalizer_sup hKV hKWh
  have hstab : stab (puAmalgam h.le) (p (k + 34)) = Lt ⊔ Qα := stab_eq_ltil_sup_qv h c.full hα
  have hC1₁ := c.commutator_top_qv_le hZV hQ4 hp ha h34 (by omega)
  have hC1₂ := c.commutator_top_qv_le hZV hQ4 hp' ha h34 (by omega)
  rw [hpa, hpa2] at hC1₂
  have hXi : ∀ X : Subgroup (puAmalgam h.le).Universal, X ≤ Qα → ⁅X, Qα⁆ ≤ Wh →
      ⁅X, stab (puAmalgam h.le) (p (k + 34))⁆ ⊔ Wh ≤ V ⊔ Wh := by
    intro X hXQ hXW
    refine sup_le ?_ le_sup_right
    refine (Subgroup.commutator_mono le_rfl hstab.le).trans ?_
    rw [Subgroup.commutator_comm]
    refine S46.commutator_sup_le_of_le_normalizer hKVW hLs hQs ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono hXQ le_rfl).trans le_sup_left
    · rw [Subgroup.commutator_comm]
      exact hXW.trans le_sup_right
  have hF8 : V ⊔ Wh = X₁' ⊔ X₂' :=
    le_antisymm (sup_le hF7 (le_sup_right.trans le_sup_left))
      (sup_le (hXi X₁ hX₁Q hC1₁) (hXi X₂ hX₂Q hC1₂))
  have hWhC : Wh ≤ Subgroup.centralizer (Vc : Set _) :=
    (c.whv_le_centralizer_vv hγ (by
      rw [hp.dist_eq' (i := k + 34) (j := k + 34 + 2) (by omega) (by omega)]; omega)).trans
      (Subgroup.centralizer_le (c.vcirc_le_vv _))
  have hF6 : V ⊓ Subgroup.centralizer (Vc : Set _) = V ⊓ Wh :=
    le_antisymm (le_inf inf_le_left hB4) (le_inf inf_le_left (inf_le_right.trans hWhC))
  have hVhn : Vh ≤ Subgroup.normalizer (Z : Set _) :=
    (sup_le (c.vcirc_le_vv _ |>.trans hVvQ) hZQ).trans (hQs.trans hKZ)
  refine ⟨hHZ, hF3, ?_, ?_, ?_, ?_⟩
  ·
    rw [hF3]
    refine le_antisymm ?_ (hUL.symm.le.trans (Subgroup.commutator_mono le_sup_left le_rfl))
    refine S46.commutator_sup_le_of_le_normalizer hKU (hUZ.trans (hZQ.trans hQs))
      (hHV.trans (hVQ.trans hQs)) hUL.le ?_
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hHc]
    exact bot_le
  ·
    have h1 := S4A.isSumOfNaturalModulesVia_transfer hd (sup_eq_left.mpr le_sup_right)
      (inf_eq_right.mpr le_sup_right) inf_le_right
      (le_antisymm (sup_le inf_le_right le_sup_right)
        (sup_le ((le_inf hVcV le_sup_left).trans le_sup_left) le_sup_right))
      (le_normalizer_inf hKV hKVh) hKZ hVhn
    have e : V ⊓ Vh ⊓ Z = centerOf V := by
      rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Z ≤ Vh), hVZ]
    rwa [e] at h1
  ·
    rw [hF6]
    have h1 := S4A.isSumOfNaturalModulesVia_transfer hL2 (sup_eq_left.mpr hVhWh)
      (inf_eq_right.mpr hVhWh) inf_le_right hF9 (le_normalizer_inf hKV hKWh) hKVh
      ((hWhQ.trans hQs).trans hKVh)
    have e : V ⊓ Wh ⊓ Vh = V ⊓ Vh := by
      rw [inf_assoc, inf_eq_right.mpr hVhWh]
    rwa [e] at h1
  ·
    rw [hF6]
    exact S4A.isSumOfNaturalModulesVia_transfer hL3
      (sup_eq_left.mpr (le_sup_right.trans le_sup_left))
      (inf_eq_right.mpr (le_sup_right.trans le_sup_left)) hF7 hF8 hKV hKWh
      ((sup_le (hX₁'X₁.trans hX₁s) (hX₂'X₂.trans hX₂s)).trans hKWh)

theorem burnsideC134w_exists_case13W_of_isGoodPath (c : Ctx M T L φ) (h14 : MS14AS)
    (hSQ : SQTKQuot) (hZV : c.HZV) {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}
    (hp : IsGoodPath _ p N) (hN : 64 ≤ N) {δ : Vtx (puAmalgam c.hyp.le)} (hδ : p 34 = δ) :
    ∃ ψ : ↥(stab (puAmalgam c.hyp.le) δ) →* ↥(StatedSL 3 F), Function.Surjective ψ ∧
      IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1 ∧
      ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ ⊓
          Subgroup.centralizer (Ltil c.hyp.le L δ : Set _) ≤ Zloc c.hyp.le L δ ∧
      centerOf ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ =
        Uloc c.hyp.le L δ ⊔ ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ ⊓
          Subgroup.centralizer (Ltil c.hyp.le L δ : Set _) ∧
      ⁅centerOf ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆, Ltil c.hyp.le L δ⁆ =
        Uloc c.hyp.le L δ ∧
      IsSumOfNaturalModulesVia (stab _ δ)
        (⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ ⊓ (Vcirc c.hyp.le L δ ⊔ ZM _ δ))
        (centerOf ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆) ψ true 1 ∧
      IsSumOfNaturalModulesVia (stab _ δ)
        (⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ ⊓
          Subgroup.centralizer (Vcirc c.hyp.le L δ : Set _))
        (⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ ⊓ (Vcirc c.hyp.le L δ ⊔ ZM _ δ))
        ψ true 2 ∧
      IsSumOfNaturalModulesVia (stab _ δ) ⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆
        (⁅Qv (puAmalgam c.hyp.le) δ, Ltil c.hyp.le L δ⁆ ⊓
          Subgroup.centralizer (Vcirc c.hyp.le L δ : Set _)) ψ false 2 := by
  subst hδ
  have hα := c.isMVtx_of_isGoodPath hp (k := 34) (by omega) (by decide)
  obtain ⟨ψ, hψs, hψ, hT⟩ := c.exists_coord_qv hα (hp.adj 34 (by omega))
  exact ⟨ψ, hψs, hψ, burnsideC134w_case13W_vertex c h14 hSQ hZV (S45Q4.hQ4 c) hp (a := 34)
    (by decide) le_rfl (by omega) hψs hψ hT⟩

end CFSG.Quasithin.MS93

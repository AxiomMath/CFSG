module

public import CFSG.Quasithin.MS93.S46R468B
public import CFSG.Quasithin.MS93.S468Red
public import CFSG.Quasithin.MS93.S46KC2Lin

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix

section Natural

variable {G : Type} [Group G] {K V : Subgroup G} {F : Type} [Field F]
  {ψ : ↥K →* ↥(StatedSL 3 F)}

theorem mem_map_conj_iff_coord (hψ : IsSumOfNaturalModulesVia K V ⊥ ψ false 1)
    {S : Subgroup G} {s : Submodule F (Fin 3 → F)} (hS : S ≤ V)
    (hs : ∀ v : ↥V, (v : G) ∈ S ↔ natVec hψ v ∈ s) (g : ↥K) (v : ↥V) :
    (v : G) ∈ S.map (MulAut.conj (g : G)).toMonoidHom ↔
      natVec hψ v ∈ s.map (Matrix.mulVecLin ((toSL3 ψ g : SL3 F) : Matrix (Fin 3) (Fin 3) F)) := by
  constructor
  · rintro ⟨u, hu, he⟩
    have huV := hS hu
    rw [natVec_conj hψ g ⟨u, huV⟩ v he.symm]
    exact Submodule.mem_map_of_mem ((hs ⟨u, huV⟩).mp hu)
  · rintro ⟨y, hy, hye⟩
    have hmem : (g : G)⁻¹ * v * (g : G) ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hψ.1 (g⁻¹).2) v).mp v.2
      simpa using this
    refine ⟨_, (hs ⟨_, hmem⟩).mpr ?_, by simp [mul_assoc]⟩
    have e := natVec_conj hψ g ⟨_, hmem⟩ v (by simp [mul_assoc])
    rw [Matrix.mulVecLin_apply, e] at hye
    have hy' : y = natVec hψ ⟨_, hmem⟩ := by
      have := congrArg (fun z => (((toSL3 ψ g)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ z) hye
      simpa only [inv_mulVec_mulVec_SL3] using this
    rwa [← hy']

end Natural

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem exists_isPtOn_span (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1) {v : Fin 3 → F}
    (hv : v ∈ fixN (natImage ψ (Qv (puAmalgam c.pu.le) β))) (hv0 : v ≠ 0) :
    ∃ P : Subgroup (puAmalgam c.pu.le).Universal, IsPtOn (puAmalgam c.pu.le) x β P ∧
      P ≤ Uloc c.pu.le L x ∧
      ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔ natVec hψ u ∈ F ∙ v := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  set W := fixN (natImage ψ (Qv (puAmalgam c.pu.le) β)) with hWdef
  have hW2 : Module.finrank F W = 2 := (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxβ hψ).1
  have hvW : F ∙ v ≤ W := (Submodule.span_singleton_le_iff_mem _ _).mpr hv
  have hlt : F ∙ v < W := lt_of_le_of_ne hvW fun he => by
    have h1 := finrank_span_singleton (K := F) hv0
    rw [he, hW2] at h1
    omega
  obtain ⟨w, hwW, hwv⟩ := IsConcreteLE.exists_of_lt hlt
  have hWt : W < ⊤ := lt_top_iff_ne_top.mpr fun he => by
    have h1 := hW2
    rw [he, finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨z, -, hzW⟩ := IsConcreteLE.exists_of_lt hWt
  have hli : ∀ {a : Fin 3 → F}, a ∉ F ∙ v → LinearIndependent F ![v, a] := fun {a} ha =>
    (LinearIndependent.pair_iff' hv0).mpr fun t ht => ha (ht ▸ Submodule.smul_mem _ t
      (Submodule.mem_span_singleton_self v))
  obtain ⟨A, hAv, hAw⟩ := exists_sl3_mulVec_pair (hli hwv) (hli fun hz => hzW (hvW hz))
  obtain ⟨k, hk⟩ := toSL3_surjective hψs A
  have hkx : (k : (puAmalgam c.pu.le).Universal) • x = x := MulAction.mem_stabilizer_iff.mp k.2
  set β'' := (k : (puAmalgam c.pu.le).Universal) • β with hβ''
  have hxβ'' : (puAmalgam c.pu.le).treeGraph.Adj x β'' := by
    have := (adj_smul _ (k : (puAmalgam c.pu.le).Universal) x β).mpr hxβ
    rwa [hkx] at this
  have hU'' : Usup (puAmalgam c.pu.le) x β'' = (Usup (puAmalgam c.pu.le) x β).map
      (MulAut.conj (k : (puAmalgam c.pu.le).Universal)).toMonoidHom := by
    rw [← usup_smul, hkx]
  have hUle := usup_le_uloc' c.pu hfull hx hxβ
  have hUle'' := usup_le_uloc' c.pu hfull hx hxβ''
  have hm := mem_usup_iff c.pu c.via h464' hsq hx hxβ hψ
  have hm'' := mem_usup_iff c.pu c.via h464' hsq hx hxβ'' hψ
  set W'' := fixN (natImage ψ (Qv (puAmalgam c.pu.le) β'')) with hW''def
  have hW''2 : Module.finrank F W'' =
      2 := (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxβ'' hψ).1
  have hW''A : ∀ y : Fin 3 → F, y ∈ W'' ↔
      y ∈ W.map (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) F)) := by
    intro y
    obtain ⟨u, rfl⟩ := natVec_surjective hψ y
    rw [← hm'', hU'', mem_map_conj_iff_coord hψ hUle hm k u, hk]
  have hvW'' : v ∈ W'' :=
    (hW''A v).mpr (Submodule.mem_map.mpr ⟨v, hv, by rw [Matrix.mulVecLin_apply, hAv]⟩)
  have hzW'' : z ∈ W'' :=
    (hW''A z).mpr (Submodule.mem_map.mpr ⟨w, hwW, by rw [Matrix.mulVecLin_apply, hAw]⟩)
  have hne : W ≠ W'' := fun he => hzW (he ▸ hzW'')
  have hinf : W ⊓ W'' = F ∙ v := by
    refine (Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.mem_inf.mpr ⟨hv, hvW''⟩)) ?_).symm
    rw [finrank_span_singleton hv0, S45.finrank_inf_eq_one hW2 hW''2 hne]
  refine ⟨Usup (puAmalgam c.pu.le) x β ⊓ Usup _ x β'', ⟨β'', hxβ'', fun he => hne ?_, rfl⟩,
    inf_le_left.trans hUle, fun u => ?_⟩
  · exact ((S45.eq_iff_of_natVec_iff hψ hUle'' hUle hm'' hm).mp he).symm
  · rw [Subgroup.mem_inf, hm, hm'', ← hinf, Submodule.mem_inf]

theorem exists_conj_pt (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {P P' : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P) (hP' : IsPtOn (puAmalgam c.pu.le) x β P') :
    ∃ g ∈ stab (puAmalgam c.pu.le) x,
      g ∈ Subgroup.normalizer (Qv (puAmalgam c.pu.le) β : Set (puAmalgam c.pu.le).Universal) ∧
      P.map (MulAut.conj g).toMonoidHom = P' := by
  by_cases he : P = P'
  · exact ⟨1, Subgroup.one_mem _, Subgroup.one_mem _, by rw [he, map_conj_one]⟩
  · obtain ⟨g, hg, hgN, hgP, -⟩ := exists_conj_pts h464 h465 h466a c hx hxβ hP hP' hP' hP he
      (Ne.symm he)
    exact ⟨g, hg, hgN, hgP⟩

theorem zm_le_bzero (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) : ZM (puAmalgam c.pu.le) x ≤ bzero c x := by
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  intro z hz
  refine ⟨zm_le_vv c.pu hx hz, fun w hw => ?_⟩
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (commute_zm_vv c.pu hb hx hz hw)]
  exact Subgroup.one_mem _

theorem mem_bzero_of_forall_vv (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P) {w : (puAmalgam c.pu.le).Universal}
    (hw : ∀ ℓ, (puAmalgam c.pu.le).treeGraph.Adj x ℓ → P ≤ Usup (puAmalgam c.pu.le) x ℓ →
      w ∈ Vv (puAmalgam c.pu.le) ℓ) : w ∈ bzero c x := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have hP0 := hP
  obtain ⟨β₁, hxβ₁, hne₁, hPe⟩ := hP0
  have hPβ : P ≤ Usup (puAmalgam c.pu.le) x β := hPe ▸ inf_le_left
  have hPβ₁ : P ≤ Usup (puAmalgam c.pu.le) x β₁ := hPe ▸ inf_le_right
  have hwV : w ∈ Vv (puAmalgam c.pu.le) x := I466b.vv_le_vv_of_adj c.pu hx hxβ (hw β hxβ hPβ)
  refine ⟨hwV, ?_⟩
  set Z := Zloc c.pu.le L x with hZdef
  let S : Subgroup (puAmalgam c.pu.le).Universal :=
    { carrier := {v | v ∈ Vv (puAmalgam c.pu.le) x ∧ ⁅w, v⁆ ∈ Z}
      one_mem' := ⟨Subgroup.one_mem _, by
        rw [commutatorElement_one_right]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb', hb''⟩
        refine ⟨Subgroup.mul_mem _ ha hb', ?_⟩
        have e : ⁅w, a * b⁆ = ⁅w, a⁆ * (a * ⁅w, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ ha' ((Subgroup.mem_normalizer_iff.mp
          (vv_le_normalizer_zloc c x ha) _).mp hb'')
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        have e : ⁅w, a⁻¹⁆ = a⁻¹ * ⁅w, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (vv_le_normalizer_zloc c x
          (Subgroup.inv_mem _ ha)) _).mp (Subgroup.inv_mem _ ha') }
  suffices hVS : Vv (puAmalgam c.pu.le) x ≤ S from fun v hv => (hVS hv).2
  rw [vv_eq_iSup_vv hx]
  refine iSup₂_le fun ℓ hxℓ => fun v hv => ⟨I466b.vv_le_vv_of_adj c.pu hx hxℓ hv, ?_⟩
  have hℓ : ¬ IsMVtx (puAmalgam c.pu.le) ℓ := (isMVtx_iff_of_adj _ hxℓ).mp hx
  by_cases hPℓ : P ≤ Usup (puAmalgam c.pu.le) x ℓ
  · rw [commutatorElement_eq_one_iff_mul_comm.mpr (vv_comm c.pu hb hℓ (hw ℓ hxℓ hPℓ) hv)]
    exact Subgroup.one_mem _
  have hβ : ¬ IsMVtx (puAmalgam c.pu.le) β := (isMVtx_iff_of_adj _ hxβ).mp hx
  have hβ₁ : ¬ IsMVtx (puAmalgam c.pu.le) β₁ := (isMVtx_iff_of_adj _ hxβ₁).mp hx
  have hd : ∀ {ρ}, (puAmalgam c.pu.le).treeGraph.Adj x ρ →
      (puAmalgam c.pu.le).treeGraph.dist ρ ℓ ≤ 2 := fun {ρ} hxρ => by
    by_cases he : ρ = ℓ
    · rw [he, SimpleGraph.dist_self]; omega
    · exact (dist_eq_two_of_adj_adj _ hxρ.symm hxℓ he).le
  have h1 : ⁅w, v⁆ ∈ (Usup (puAmalgam c.pu.le) x β ⊓ Usup _ x ℓ) ⊔ Z := by
    rw [← zh_inf_zh_eq h464 h465 c hx hxβ hxℓ]
    exact commutator_vv_vv_le_zh_inf h464 c hβ hℓ (hd hxβ)
      (Subgroup.commutator_mem_commutator (hw β hxβ hPβ) hv)
  have h2 : ⁅w, v⁆ ∈ (Usup (puAmalgam c.pu.le) x β₁ ⊓ Usup _ x ℓ) ⊔ Z := by
    rw [← zh_inf_zh_eq h464 h465 c hx hxβ₁ hxℓ]
    exact commutator_vv_vv_le_zh_inf h464 c hβ₁ hℓ (hd hxβ₁)
      (Subgroup.commutator_mem_commutator (hw β₁ hxβ₁ hPβ₁) hv)
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc c.pu c.via hx
  obtain ⟨p, -, hp1, hPU, hPp⟩ := exists_coord_of_isPtOn h464 h465 c hx hxβ hψ hP
  have hmℓ := mem_usup_iff c.pu c.via h464' hsq hx hxℓ hψ
  have hUℓ := usup_le_uloc' c.pu hfull hx hxℓ
  have hpℓ : p ⊓ fixN (natImage ψ (Qv (puAmalgam c.pu.le) ℓ)) = ⊥ := by
    have hlt : p ⊓ fixN (natImage ψ (Qv (puAmalgam c.pu.le) ℓ)) < p := by
      refine lt_of_le_of_ne inf_le_left fun he => hPℓ fun y hy => ?_
      have hyU := hPU hy
      have := (hPp ⟨y, hyU⟩).mp hy
      rw [← he] at this
      exact (hmℓ ⟨y, hyU⟩).mpr this.2
    have := Submodule.finrank_lt_finrank_of_lt hlt
    rw [hp1] at this
    exact Submodule.finrank_eq_zero.mp (by omega)
  have hPℓbot : P ⊓ Usup (puAmalgam c.pu.le) x ℓ = ⊥ := by
    refine le_bot_iff.mp fun y hy => ?_
    have hyU := hPU hy.1
    have h1 := (hPp ⟨y, hyU⟩).mp hy.1
    have h2 := (hmℓ ⟨y, hyU⟩).mp hy.2
    have h3 : natVec hψ ⟨y, hyU⟩ = 0 := by
      have : natVec hψ ⟨y, hyU⟩ ∈ p ⊓ fixN (natImage ψ (Qv (puAmalgam c.pu.le) ℓ)) := ⟨h1, h2⟩
      rw [hpℓ] at this
      exact this
    have h4 : (⟨y, hyU⟩ : ↥(Uloc c.pu.le L x)) = 1 :=
      natVec_injective hψ (by rw [h3, natVec_one])
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h4)
  set A₁ := Usup (puAmalgam c.pu.le) x β ⊓ Usup _ x ℓ with hA₁
  set A₂ := Usup (puAmalgam c.pu.le) x β₁ ⊓ Usup _ x ℓ with hA₂
  set U := Uloc c.pu.le L x with hUdef
  have hA₁U : A₁ ≤ U := inf_le_left.trans (usup_le_uloc' c.pu hfull hx hxβ)
  have hA₂U : A₂ ≤ U := inf_le_left.trans (usup_le_uloc' c.pu hfull hx hxβ₁)
  have hA₁₂ : A₁ ⊓ A₂ = ⊥ := by
    refine le_bot_iff.mp (le_trans ?_ hPℓbot.le)
    rw [hPe]
    exact le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
      (inf_le_left.trans inf_le_right)
  have hZc : Z ≤ Subgroup.centralizer (stab (puAmalgam c.pu.le) x : Set _) :=
    zloc_le_centralizer_stab c.pu hfull hx
  have hUs : U ≤ stab (puAmalgam c.pu.le) x := puTrans_le_stab c.pu.le _ x
  have hZn : ∀ {A : Subgroup (puAmalgam c.pu.le).Universal}, A ≤ U →
      Z ≤ Subgroup.normalizer (A : Set _) := fun {A} hA =>
    (hZc.trans (Subgroup.centralizer_le (hA.trans hUs))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hnZ : ∀ {A : Subgroup (puAmalgam c.pu.le).Universal}, A ≤ U →
      A ≤ Subgroup.normalizer (Z : Set _) := fun {A} hA =>
    (hA.trans hUs).trans ((Subgroup.le_centralizer_iff.mp hZc).trans
      (Subgroup.centralizer_le_normalizer _))
  have hUZ : Z ⊓ U = ⊥ := by rw [inf_comm]; exact uloc_inf_zloc c.pu hfull x
  have hmeet : (A₁ ⊔ Z) ⊓ (A₂ ⊔ Z) ≤ Z := by
    have e1 : (Z ⊔ A₁) ⊓ (A₂ ⊔ Z) = Z ⊔ (A₁ ⊓ (A₂ ⊔ Z)) :=
      S45.sup_inf_eq_of_le le_sup_right (hZn hA₁U)
    have e2 : (A₂ ⊔ Z) ⊓ U = A₂ ⊔ (Z ⊓ U) := S45.sup_inf_eq_of_le hA₂U (hnZ hA₂U)
    have e3 : A₁ ⊓ (A₂ ⊔ Z) ≤ A₁ ⊓ A₂ := by
      refine le_inf inf_le_left ?_
      have : A₁ ⊓ (A₂ ⊔ Z) ≤ (A₂ ⊔ Z) ⊓ U := le_inf inf_le_right (inf_le_left.trans hA₁U)
      rw [e2, hUZ, sup_bot_eq] at this
      exact this
    rw [sup_comm A₁ Z, e1, hA₁₂] at *
    exact sup_le le_rfl (e3.trans bot_le)
  exact hmeet ⟨h1, h2⟩

theorem mem_ptQ_of_toSL3_mem (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1)
    {P : Subgroup (puAmalgam c.pu.le).Universal} (hPU : P ≤ Uloc c.pu.le L x) {i j : Fin 3}
    (hij : i ≠ j)
    (hPc : ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔
      natVec hψ u ∈ F ∙ (Pi.single i 1 : Fin 3 → F))
    {k : ↥(stab (puAmalgam c.pu.le) x)} (hk : toSL3 ψ k ∈ (rootGroup i j : Subgroup (SL3 F))) :
    (k : (puAmalgam c.pu.le).Universal) ∈ ptQ (puAmalgam c.pu.le) x P := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hsingle : ∀ cc : F, ((rootElt i j cc : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (Pi.single i 1 : Fin 3 → F) = Pi.single i 1 := fun cc => by
    rw [rootElt_mulVec hij, Pi.single_eq_of_ne hij.symm, mul_zero, Pi.single_zero, add_zero]
  have hmap : ∀ k' : ↥(stab (puAmalgam c.pu.le) x),
      toSL3 ψ k' ∈ (rootGroup i j : Subgroup (SL3 F)) →
      P.map (MulAut.conj (k' : (puAmalgam c.pu.le).Universal)).toMonoidHom = P := by
    intro k' hk'
    obtain ⟨cc, hcc⟩ := hk'
    refine map_conj_eq_of_coord hψ hPU hPU hPc hPc k' ?_
    rw [← hcc, Submodule.map_span, Set.image_singleton, Matrix.mulVecLin_apply, hsingle]
  refine ⟨k.2, mem_normalizer_of_map_conj_le (hmap k hk).le ?_, fun z hz => ?_⟩
  · have := hmap k⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hk)
    rw [Subgroup.coe_inv] at this
    exact this.le
  · obtain ⟨cc, hcc⟩ := hk
    obtain ⟨u, hu, ζ, hζ, rfl⟩ := I466b.exists_uloc_mul_zloc c.pu hfull hx hz
    set kk : (puAmalgam c.pu.le).Universal := (k : (puAmalgam c.pu.le).Universal) with hkk
    have hζk : ζ * kk = kk * ζ :=
      (Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab c.pu hfull hx hζ) k k.2).symm
    have e1 : ⁅u * ζ, kk⁆ = ⁅u, kk⁆ := by
      simp only [commutatorElement_def]
      calc u * ζ * kk * (u * ζ)⁻¹ * kk⁻¹ = u * (ζ * kk) * ζ⁻¹ * u⁻¹ * kk⁻¹ := by group
        _ = u * (kk * ζ) * ζ⁻¹ * u⁻¹ * kk⁻¹ := by rw [hζk]
        _ = u * kk * u⁻¹ * kk⁻¹ := by group
    rw [e1]
    have hmem : ⁅u, kk⁆ ∈ Uloc c.pu.le L x := S468.commutator_mem_uloc c.pu hψ ⟨u, hu⟩ k
    refine (hPc ⟨_, hmem⟩).mpr ?_
    rw [natVec_commutator hψ k ⟨u, hu⟩ ⟨_, hmem⟩ rfl, ← hcc, rootElt_mulVec hij,
      sub_add_cancel_left]
    refine Submodule.neg_mem _ (Submodule.mem_span_singleton.mpr ⟨cc * natVec hψ ⟨u, hu⟩ j, ?_⟩)
    rw [← Pi.single_smul, smul_eq_mul, mul_one]

theorem s468At_of_ptQ (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    (h : ∀ P, IsPtOn (puAmalgam c.pu.le) x β P →
      ⁅Vv (puAmalgam c.pu.le) β, ptQ (puAmalgam c.pu.le) x P⁆ ≤ bzero c x) :
    S468At (puAmalgam c.pu.le) x β := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have hβ : ¬ IsMVtx (puAmalgam c.pu.le) β := (isMVtx_iff_of_adj _ hxβ).mp hx
  obtain ⟨ψ, hψs, hψU, hψT⟩ := exists_coord_qv h464 h465 h466a c hx hxβ
  have hW : fixN (natImage ψ (Qv (puAmalgam c.pu.le) β)) = coordZero 0 := by
    rw [hψT, fixN_sup, fixN_rootGroup (by decide), fixN_rootGroup (by decide), inf_idem]
  have hei : ∀ i : Fin 3, i ≠ 0 → (Pi.single i 1 : Fin 3 → F) ∈
      fixN (natImage ψ (Qv (puAmalgam c.pu.le) β)) := fun i hi => by
    rw [hW]
    show (Pi.single i (1 : F) : Fin 3 → F) 0 = 0
    exact Pi.single_eq_of_ne (Ne.symm hi) _
  have hei0 : ∀ i : Fin 3, (Pi.single i 1 : Fin 3 → F) ≠ 0 := fun i he => by
    have := congrFun he i
    simp at this
  obtain ⟨P₁, hP₁, hP₁U, hP₁c⟩ :=
    exists_isPtOn_span h464 h465 c hx hxβ hψs hψU (hei 1 (by decide)) (hei0 1)
  obtain ⟨P₂, hP₂, hP₂U, hP₂c⟩ :=
    exists_isPtOn_span h464 h465 c hx hxβ hψs hψU (hei 2 (by decide)) (hei0 2)
  let S : Subgroup (puAmalgam c.pu.le).Universal :=
    { carrier := {k | k ∈ stab (puAmalgam c.pu.le) x ∧
        ∀ y ∈ Vv (puAmalgam c.pu.le) β, ⁅y, k⁆ ∈ bzero c x}
      one_mem' := ⟨Subgroup.one_mem _, fun y _ => by
        rw [commutatorElement_one_right]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, fun y hy => ?_⟩
        have e : ⁅y, a * b⁆ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ (ha' y hy) ((Subgroup.mem_normalizer_iff.mp
          (stab_le_normalizer_bzero c x ha) _).mp (hb' y hy))
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun y hy => ?_⟩
        have e : ⁅y, a⁻¹⁆ = a⁻¹ * ⁅y, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_bzero c x
          (Subgroup.inv_mem _ ha)) _).mp (Subgroup.inv_mem _ (ha' y hy)) }
  have hTS : Qv (puAmalgam c.pu.le) β ≤ S := fun t ht =>
    ⟨qv_le_stab_of_adj _ hxβ.symm ht, fun y hy => zm_le_bzero c hx (zh_le_zm _ hxβ
      (commutator_vv_qv_le_zh c.pu h464' hβ (Subgroup.commutator_mem_commutator hy ht)))⟩
  have hQS : ∀ {P}, IsPtOn (puAmalgam c.pu.le) x β P → ptQ (puAmalgam c.pu.le) x P ≤ S :=
    fun {P} hP k hk => ⟨(mem_ptQ.mp hk).1, fun y hy =>
      h P hP (Subgroup.commutator_mem_commutator hy hk)⟩
  let D : Subgroup (SL3 F) := (S.subgroupOf (stab (puAmalgam c.pu.le) x)).map (toSL3 ψ)
  have hlift : ∀ B : SL3 F, (∀ k : ↥(stab (puAmalgam c.pu.le) x), toSL3 ψ k = B →
      (k : (puAmalgam c.pu.le).Universal) ∈ S) → B ∈ D := by
    intro B hB
    obtain ⟨k, hk⟩ := toSL3_surjective hψs B
    exact ⟨k, Subgroup.mem_subgroupOf.mpr (hB k hk), hk⟩
  have hR : ∀ k : ↥(stab (puAmalgam c.pu.le) x),
      toSL3 ψ k ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) →
        (k : (puAmalgam c.pu.le).Universal) ∈ S := fun k hk =>
    hTS (S468.mem_qv_of_toSL3_mem c.pu c.via hx hxβ hψU hψT hk)
  have h10 : ∀ cc : F, rootElt 1 0 cc ∈ D := fun cc => hlift _ fun k hk => hR k (by
    rw [hk]; exact Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 cc))
  have h20 : ∀ cc : F, rootElt 2 0 cc ∈ D := fun cc => hlift _ fun k hk => hR k (by
    rw [hk]; exact Subgroup.mem_sup_right (rootElt_mem_rootGroup 2 0 cc))
  have h12 : ∀ cc : F, rootElt 1 2 cc ∈ D := fun cc => hlift _ fun k hk =>
    hQS hP₁ (mem_ptQ_of_toSL3_mem c hx hψU hP₁U (i := 1) (j := 2) (by decide) hP₁c
      (by rw [hk]; exact rootElt_mem_rootGroup 1 2 cc))
  have h21 : ∀ cc : F, rootElt 2 1 cc ∈ D := fun cc => hlift _ fun k hk =>
    hQS hP₂ (mem_ptQ_of_toSL3_mem c hx hψU hP₂U (i := 2) (j := 1) (by decide) hP₂c
      (by rw [hk]; exact rootElt_mem_rootGroup 2 1 cc))
  have hL : ∀ k : ↥(stab (puAmalgam c.pu.le) x),
      toSL3 ψ k ∈ (S468.stabX0 : Subgroup (SL3 F)) → (k : (puAmalgam c.pu.le).Universal) ∈ S := by
    intro k hk
    have hrow : ((toSL3 ψ k : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 0 1 := by
      funext j
      rw [S468.row_zero_of_mem_stabX0 hk j]
      by_cases hj : j = 0
      · subst hj; simp
      · simp [hj]
    obtain ⟨s, hs, hse⟩ := KC2.mem_of_row_zero h10 h20 h12 h21 hrow
    have h1 : toSL3 ψ (s⁻¹ * k) = 1 := by rw [map_mul, map_inv, hse, inv_mul_cancel]
    have h2 := (toSL3_eq_one_iff_mem_qv c.pu c.via hx hψU _).mp h1
    have e : (k : (puAmalgam c.pu.le).Universal) = (s : (puAmalgam c.pu.le).Universal) *
        ((s⁻¹ * k : ↥(stab (puAmalgam c.pu.le) x)) : (puAmalgam c.pu.le).Universal) := by simp
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_subgroupOf.mp hs)
      (hTS (qv_le_qv _ c.pu.hyp20 hx hxβ h2))
  intro g hg y hy v hv
  have hgS := hL ⟨g, hg.1⟩ (S468.toSL3_mem_of_commutator_mem_zh c.pu c.via hx hxβ hψU hψT h464'
    hsq (k := ⟨g, hg.1⟩) hg.2.2.1)
  have hZ := (hgS.2 y hy).2 v hv
  refine ⟨⟨_, puTrans_le_stab c.pu.le _ x hZ⟩, Subgroup.mem_center_iff.mpr fun a => Subtype.ext ?_,
    rfl⟩
  exact Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab c.pu hfull hx hZ) a a.2

theorem not_commutator_vv_ptQ_le (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {α β : Vtx (puAmalgam c.pu.le)}
    (hbad : ¬ S468At (puAmalgam c.pu.le) α β) (hα : IsMVtx (puAmalgam c.pu.le) α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) {x ℓ : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ)
    {P : Subgroup (puAmalgam c.pu.le).Universal} (hP : IsPtOn (puAmalgam c.pu.le) x ℓ P) :
    ¬ ⁅Vv (puAmalgam c.pu.le) ℓ, ptQ (puAmalgam c.pu.le) x P⁆ ≤ bzero c x := by
  intro hle
  obtain ⟨g₀, hg₀α, hg₀β⟩ := exists_smul_edge_of_isMVtx _ hα hαβ hx hxℓ
  apply hbad
  rw [← s468At_smul g₀, hg₀α, hg₀β]
  have hℓ : ¬ IsMVtx (puAmalgam c.pu.le) ℓ := (isMVtx_iff_of_adj _ hxℓ).mp hx
  refine s468At_of_ptQ h464 h465 h466a c hx hxℓ fun P' hP' => ?_
  obtain ⟨g, hg, hgN, hgP⟩ := exists_conj_pt h464 h465 h466a c hx hxℓ hP hP'
  have hgx : g • x = x := MulAction.mem_stabilizer_iff.mp hg
  have hV : (Vv (puAmalgam c.pu.le) ℓ).map (MulAut.conj g).toMonoidHom = Vv _ ℓ := by
    rw [← show Vv (puAmalgam c.pu.le) (g • ℓ) = (Vv _ ℓ).map (MulAut.conj g).toMonoidHom from
      vi_smul _ g ℓ 2]
    exact vv_smul_eq_of_mem_normalizer c.pu hℓ hgN
  have hQ : ptQ (puAmalgam c.pu.le) x P' = (ptQ _ x P).map (MulAut.conj g).toMonoidHom := by
    rw [← ptQ_smul, hgx, hgP]
  rw [hQ, ← hV, ← Subgroup.map_commutator, ← map_conj_eq_of_mem_normalizer
    (stab_le_normalizer_bzero c x hg)]
  exact Subgroup.map_mono hle

theorem exists_pencil_le_ptQ (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {α β γ : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx (puAmalgam c.pu.le) α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) (hγ : IsMVtx (puAmalgam c.pu.le) γ)
    (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) γ β P)
    (hn : ¬ Usup (puAmalgam c.pu.le) α β ≤ P ⊔ Zloc c.pu.le L γ) :
    ∃ p, IsPtOn (puAmalgam c.pu.le) α β p ∧
      pencil (puAmalgam c.pu.le) γ P ≤ Qv (puAmalgam c.pu.le) β ⊓ ptQ _ α p := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have hYT : pencil (puAmalgam c.pu.le) γ P ≤ Qv (puAmalgam c.pu.le) β :=
    pencil_le fun β' hγβ' _ => by
      have hβ' : ¬ IsMVtx (puAmalgam c.pu.le) β' := (isMVtx_iff_of_adj _ hγβ').mp hγ
      refine vv_le_qv_of_dist_le_two c.b4 hβ' ?_
      by_cases he : β' = β
      · rw [he, SimpleGraph.dist_self]; omega
      · exact (dist_eq_two_of_adj_adj _ hγβ'.symm hγβ he).le
  have hYs : pencil (puAmalgam c.pu.le) γ P ≤ stab (puAmalgam c.pu.le) α :=
    hYT.trans (qv_le_stab_of_adj _ hαβ.symm)
  obtain ⟨β₁, hγβ₁, hne₁, hPe⟩ := hP
  have hPU : P ≤ Usup (puAmalgam c.pu.le) γ β := hPe ▸ inf_le_left
  have hPc : Nat.card ↥P = Fintype.card F := by
    rw [hPe]; exact card_usup_inf_usup h464 h465 c hγ hγβ hγβ₁ (Ne.symm hne₁)
  have hcomm := commutator_zm_pencil_le h464 h465 h466a c hα hαβ hγ hγβ hPU hPc
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc c.pu c.via hα
  obtain ⟨hW2, hcW⟩ := I466b.fixN_natImage_qv c.pu c.via h464' hsq hα hαβ hψ
  set W := fixN (natImage ψ (Qv (puAmalgam c.pu.le) β)) with hWdef
  set C := commN (natImage ψ (pencil (puAmalgam c.pu.le) γ P)) with hCdef
  have hCW : C ≤ W := by
    rw [← hcW]
    refine commN_mono fun B hB => ?_
    obtain ⟨a, ha, rfl⟩ := mem_natImage.mp hB
    exact mem_natImage.mpr ⟨a, hYT ha, rfl⟩
  have hUC : ⁅Uloc c.pu.le L α, pencil (puAmalgam c.pu.le) γ P⁆ ≤ Uloc c.pu.le L α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hYs.trans hψ.1)
  have hCne : C ≠ W := by
    intro hCW'
    apply hn
    refine le_trans ?_ (hcomm.trans inf_le_left)
    rw [commutator_zm_eq_uloc c.pu hfull hα hYs]
    intro y hy
    have hyU := usup_le_uloc' c.pu hfull hα hαβ hy
    exact (mem_commutator_iff_natVec hψ hYs ⟨y, hyU⟩).mpr
      (by rw [← hCdef, hCW']; exact (mem_usup_iff c.pu c.via h464' hsq hα hαβ hψ ⟨y, hyU⟩).mp hy)
  obtain ⟨v, hvW, hv0, hCv⟩ : ∃ v ∈ W, v ≠ 0 ∧ C ≤ F ∙ v := by
    have hlt : C < W := lt_of_le_of_ne hCW hCne
    have hCle : Module.finrank F C ≤ 1 := by
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    by_cases hC0 : C = ⊥
    · have hWne : W ≠ ⊥ := fun he => by
        rw [he, finrank_bot] at hW2
        omega
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
      exact ⟨v, hv, hv0, by rw [hC0]; exact bot_le⟩
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hC0
      have hC1 : Module.finrank F C = 1 := by
        have : Module.finrank F C ≠ 0 := fun h0 => hC0 (Submodule.finrank_eq_zero.mp h0)
        omega
      exact ⟨v, hCW hv, hv0, (eq_span_singleton_of_mem_of_finrank_eq_one hC1 hv hv0).le⟩
  obtain ⟨p, hp, hpU, hpc⟩ := exists_isPtOn_span h464 h465 c hα hαβ hψs hψ hvW hv0
  have hpU' : p ≤ Usup (puAmalgam c.pu.le) α β := by
    obtain ⟨_, _, _, he⟩ := hp
    rw [he]
    exact inf_le_left
  refine ⟨p, hp, le_inf hYT fun y hy => ⟨hYs hy, ?_, fun z hz => ?_⟩⟩
  ·
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha => ?_)
    exact (Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β (h464' α β hα hαβ (hpU' ha)))
      y (hYT hy)).symm
  · have hzy : ⁅z, y⁆ ∈ ⁅Uloc c.pu.le L α, pencil (puAmalgam c.pu.le) γ P⁆ := by
      rw [← commutator_zm_eq_uloc c.pu hfull hα hYs]
      exact Subgroup.commutator_mem_commutator hz hy
    exact (hpc ⟨_, hUC hzy⟩).mpr (hCv ((mem_commutator_iff_natVec hψ hYs ⟨_, hUC hzy⟩).mp hzy))

end CFSG.Quasithin.MS93.S46R

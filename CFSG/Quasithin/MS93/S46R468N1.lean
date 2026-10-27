module

public import CFSG.Quasithin.MS93.S46R468C1A
public import CFSG.Quasithin.MS93.S46R468LvA

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix

section General

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem le_normalizer_pencil {x : Vtx X} {P K : Subgroup X.Universal} (hK : K ≤ stab X x)
    (hKP : K ≤ Subgroup.normalizer (P : Set X.Universal)) :
    K ≤ Subgroup.normalizer (pencil X x P : Set X.Universal) :=
  le_normalizer_of_map_conj_le fun k hk => by
    rw [← pencil_smul, MulAction.mem_stabilizer_iff.mp (hK hk),
      map_conj_eq_of_mem_normalizer (hKP hk)]

end General

theorem mulVec_eq_self_of_mem_pt0 {F : Type} [Field F] {A : SL3 F}
    (hA : A ∈ (stabE0 : Subgroup (SL3 F))) {v : Fin 3 → F} (hv : v ∈ (pt0 : Submodule F _)) :
    (A : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
  have hv' : v = v 0 • (Pi.single 0 1 : Fin 3 → F) := by
    funext i
    fin_cases i
    · simp
    · simp [show v 1 = 0 from hv.1]
    · simp [show v 2 = 0 from hv.2]
  rw [hv', Matrix.mulVec_smul, mem_stabE0.mp hA]

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem ptL_le_normalizer (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)}
    (hψU : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1)
    {P : Subgroup (puAmalgam c.pu.le).Universal} (hPU : P ≤ Uloc c.pu.le L x)
    (hP : ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔
      natVec hψU u ∈ pt0) :
    ptL (puAmalgam c.pu.le) x ψ ≤ Subgroup.normalizer (P : Set (puAmalgam c.pu.le).Universal) := by
  have key : ∀ g ∈ ptL (puAmalgam c.pu.le) x ψ,
      P.map (MulAut.conj g).toMonoidHom = P := by
    intro g hg
    obtain ⟨hgs, hgE⟩ := mem_ptL_iff.mp hg
    refine map_conj_eq_of_coord hψU hPU hPU hP hP ⟨g, hgs⟩ ?_
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [Matrix.mulVecLin_apply, mulVec_eq_self_of_mem_pt0 hgE hw]
      exact hw
    · intro hv
      exact ⟨v, hv, by rw [Matrix.mulVecLin_apply, mulVec_eq_self_of_mem_pt0 hgE hv]⟩
  intro g hg
  exact mem_normalizer_of_map_conj_le (key g hg).le (key g⁻¹ (Subgroup.inv_mem _ hg)).le

theorem commutator_pencil_pencil_le (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P) :
    ⁅pencil (puAmalgam c.pu.le) x P, pencil _ x P⁆ ≤ P ⊔ Zloc c.pu.le L x := by
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hPc := card_of_isPtOn h464 h465 c hx hxβ hP
  have hPZ : P ⊔ Zloc c.pu.le L x ≤ ZM (puAmalgam c.pu.le) x :=
    sup_le ((le_uloc_of_isPtOn c hx hP).trans (uloc_le_zm c.pu hfull hx)) (zloc_le_zm c.pu hfull hx)
  have hpen : pencil (puAmalgam c.pu.le) x P = ⨆ m, ⨆ (_ : (puAmalgam c.pu.le).treeGraph.Adj x m ∧
      P ≤ Usup (puAmalgam c.pu.le) x m), Vv (puAmalgam c.pu.le) m :=
    le_antisymm (pencil_le fun m hm hP' => le_iSup₂_of_le m ⟨hm, hP'⟩ le_rfl)
      (iSup₂_le fun m h => vv_le_pencil h.1 h.2)
  have h := I467.commutator_biSup_le_of (H := pencil (puAmalgam c.pu.le) x P)
    (N := P ⊔ Zloc c.pu.le L x) (A := fun m => Vv (puAmalgam c.pu.le) m)
    (p := fun m => (puAmalgam c.pu.le).treeGraph.Adj x m ∧ P ≤ Usup (puAmalgam c.pu.le) x m)
    (fun m hm => commutator_vv_pencil_le h464 h465 h466a c hx hm.1 hm.2 hPc)
    (fun m hm => by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ c.pu.hyp20 hx (hPZ ha)) v
        (vv_le_qv c.pu hb hx (I466b.vv_le_vv_of_adj c.pu hx hm.1 hv))).symm)
  rw [← hpen] at h
  exact h

theorem mul_self_mem_ptSub (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P) {v : (puAmalgam c.pu.le).Universal}
    (hv : v ∈ pencil (puAmalgam c.pu.le) x P) : v * v ∈ ptSub (puAmalgam c.pu.le) x P := by
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hYY : ∀ a ∈ pencil (puAmalgam c.pu.le) x P, ∀ b ∈ pencil (puAmalgam c.pu.le) x P,
      ⁅a, b⁆ ∈ ptSub (puAmalgam c.pu.le) x P := fun a ha b hb' =>
    zm_le_ptSub c hx hP (sup_le ((le_uloc_of_isPtOn c hx hP).trans (uloc_le_zm c.pu hfull hx))
      (zloc_le_zm c.pu hfull hx) (commutator_pencil_pencil_le h464 h465 h466a c hx hxβ hP
        (Subgroup.commutator_mem_commutator ha hb')))
  let S : Subgroup (puAmalgam c.pu.le).Universal :=
    { carrier := {w | w ∈ pencil (puAmalgam c.pu.le) x P ∧ w * w ∈ ptSub (puAmalgam c.pu.le) x P}
      one_mem' := ⟨Subgroup.one_mem _, by rw [one_mul]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb', hb''⟩
        refine ⟨Subgroup.mul_mem _ ha hb', ?_⟩
        have e : a * b * (a * b) = a * a * ⁅a⁻¹, b⁆ * (b * b) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha' (hYY _ (Subgroup.inv_mem _ ha) _ hb')) hb''
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        have e : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        rw [e]
        exact Subgroup.inv_mem _ ha' }
  have hYS : pencil (puAmalgam c.pu.le) x P ≤ S := pencil_le fun m hxm hPm w hw =>
    ⟨vv_le_pencil hxm hPm hw, by
      rw [vv_mul_self_eq_one c.pu hb ((isMVtx_iff_of_adj _ hxm).mp hx) hw]
      exact Subgroup.one_mem _⟩
  exact (hYS hv).2

theorem ptQ_inf_ptQ_le_qv (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {P R : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P) (hR : IsPtOn (puAmalgam c.pu.le) x β R) (hPR : P ≠ R) :
    ptQ (puAmalgam c.pu.le) x P ⊓ ptQ _ x R ≤ Qv _ x := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc c.pu c.via hx
  obtain ⟨p, -, hp1, hPU, hPp⟩ := exists_coord_of_isPtOn h464 h465 c hx hxβ hψ hP
  obtain ⟨r, -, hr1, hRU, hRr⟩ := exists_coord_of_isPtOn h464 h465 c hx hxβ hψ hR
  have hpr : p ≠ r := fun e => hPR ((S45.eq_iff_of_natVec_iff hψ hPU hRU hPp hRr).mpr e)
  have hpr0 : p ⊓ r = ⊥ := by
    have hlt : p ⊓ r < p := lt_of_le_of_ne inf_le_left fun he => hpr
      (Submodule.eq_of_le_of_finrank_eq (he ▸ inf_le_right) (by rw [hp1, hr1]))
    have := Submodule.finrank_lt_finrank_of_lt hlt
    rw [hp1] at this
    exact Submodule.finrank_eq_zero.mp (by omega)
  rintro t ⟨htP, htR⟩
  have hts : t ∈ stab (puAmalgam c.pu.le) x := (mem_ptQ.mp htP).1
  refine (toSL3_eq_one_iff_mem_qv c.pu c.via hx hψ ⟨t, hts⟩).mp ?_
  have hfix : ∀ v : Fin 3 → F,
      ((toSL3 ψ ⟨t, hts⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
    intro v
    obtain ⟨u, rfl⟩ := natVec_surjective hψ v
    have hmem := S468.commutator_mem_uloc c.pu hψ u ⟨t, hts⟩
    have h1 := (hPp ⟨_, hmem⟩).mp ((mem_ptQ.mp htP).2.2 u (uloc_le_zm c.pu hfull hx u.2))
    have h2 := (hRr ⟨_, hmem⟩).mp ((mem_ptQ.mp htR).2.2 u (uloc_le_zm c.pu hfull hx u.2))
    have h3 : natVec hψ ⟨_, hmem⟩ ∈ p ⊓ r := ⟨h1, h2⟩
    rw [hpr0, Submodule.mem_bot, natVec_commutator hψ ⟨t, hts⟩ u ⟨_, hmem⟩ rfl, sub_eq_zero] at h3
    exact h3.symm
  exact Subtype.ext (Matrix.ext_of_mulVec_single fun i => by
    rw [hfix, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec])

theorem card_map_ptTheta (c : Hyp46 M T L φ) {x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)}
    (hψU : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1)
    {P : Subgroup (puAmalgam c.pu.le).Universal} (hPU : P ≤ Uloc c.pu.le L x)
    (hP : ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔
      natVec hψU u ∈ pt0)
    {A : Subgroup (puAmalgam c.pu.le).Universal} (hA : A ≤ ptL (puAmalgam c.pu.le) x ψ) :
    Nat.card ((A.subgroupOf (ptL (puAmalgam c.pu.le) x ψ)).map (ptTheta ψ)) =
      (ptQ (puAmalgam c.pu.le) x P).relIndex A := by
  have hker : (ptTheta ψ).ker = (ptQ (puAmalgam c.pu.le) x P).subgroupOf (ptL _ x ψ) := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ptTheta_eq_one_iff c hx hψU hPU hP k]
  rw [← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hA]

end CFSG.Quasithin.MS93.S46R

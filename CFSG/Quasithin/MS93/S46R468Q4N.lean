module

public import CFSG.Quasithin.MS93.S46R468N1
public import CFSG.Quasithin.MS93.S46R468C4T
public import CFSG.Quasithin.MS93.S46R468E

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix MatrixGroups

section Torus

variable {F : Type} [Field F]

theorem diagTwo_mulVec (t : Fˣ) (w : Fin 2 → F) :
    ((diagTwo t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ w =
      ![(t : F) * w 0, ((t⁻¹ : Fˣ) : F) * w 1] := by
  ext i
  fin_cases i <;> simp [coe_diagTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem torus_mulVec (t : Fˣ) (b : F) (w : Fin 2 → F) :
    ((SL2Model.e12 b * diagTwo t * SL2Model.e12 b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ w =
      ![(t : F) * w 0 + ((t : F) * b + b * ((t⁻¹ : Fˣ) : F)) * w 1,
        ((t⁻¹ : Fˣ) : F) * w 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  ext i
  fin_cases i
  · simp [coe_diagTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [coe_diagTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mulVec_conj_eq_smul (A B : SL(2, F)) {v : Fin 2 → F} {s : F}
    (hB : (B : Matrix (Fin 2) (Fin 2) F) *ᵥ ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
      s • ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v)) :
    ((A⁻¹ * B * A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = s • v := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hB, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_mulVec]

theorem eq_zero_of_torus_mulVec (b : F) {t : Fˣ} (ht : t ≠ 1) {w : Fin 2 → F}
    (hw : ((SL2Model.e12 b * diagTwo t * SL2Model.e12 b : SL(2, F)) :
      Matrix (Fin 2) (Fin 2) F) *ᵥ w = w) : w = 0 := by
  rw [torus_mulVec] at hw
  have ht₁ : (t : F) - 1 ≠ 0 := sub_ne_zero.mpr fun h => ht (Units.ext h)
  have ht₂ : ((t⁻¹ : Fˣ) : F) - 1 ≠ 0 :=
    sub_ne_zero.mpr fun h => ht (inv_eq_one.mp (Units.ext h))
  have h1 : (((t⁻¹ : Fˣ) : F) - 1) * w 1 = 0 := by
    have := congrFun hw 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
    linear_combination this
  have hw1 : w 1 = 0 := (mul_eq_zero.mp h1).resolve_left ht₂
  have h0 : ((t : F) - 1) * w 0 = 0 := by
    have := congrFun hw 0
    simp only [Matrix.cons_val_zero, hw1, mul_zero, add_zero] at this
    linear_combination this
  have hw0 : w 0 = 0 := (mul_eq_zero.mp h0).resolve_left ht₁
  ext i
  fin_cases i
  · exact hw0
  · exact hw1

variable [CharP F 2]

theorem torus_eq_conj (t : Fˣ) (b : F) :
    SL2Model.e12 b * diagTwo t * SL2Model.e12 b = MulAut.conj (SL2Model.e12 b) (diagTwo t) := by
  rw [MulAut.conj_apply, ← eq_inv_of_mul_eq_one_left (SL2Model.e12_mul_self b)]

theorem odd_orderOf_torus [Fintype F] (t : Fˣ) (b : F) :
    Odd (orderOf (SL2Model.e12 b * diagTwo t * SL2Model.e12 b : SL(2, F))) := by
  rw [torus_eq_conj, MulEquiv.orderOf_eq]
  exact odd_orderOf_diagTwo t

theorem torus_mulVec_of_ne (t : Fˣ) {f : Fin 2 → F} (hf : f 1 ≠ 0) :
    ((SL2Model.e12 (f 0 / f 1) * diagTwo t * SL2Model.e12 (f 0 / f 1) : SL(2, F)) :
      Matrix (Fin 2) (Fin 2) F) *ᵥ f = ((t⁻¹ : Fˣ) : F) • f := by
  rw [torus_mulVec]
  have e : ((t : F) * (f 0 / f 1) + f 0 / f 1 * ((t⁻¹ : Fˣ) : F)) * f 1 =
      (t : F) * f 0 + ((t⁻¹ : Fˣ) : F) * f 0 := by
    field_simp
  ext i
  fin_cases i
  · simp only [Matrix.cons_val_zero, Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
    rw [e, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · simp

end Torus

section General

variable {G : Type*} [Group G]

theorem commutator_mem_of_mem_closure_odd {K Y N : Subgroup G}
    (hKY : K ≤ Subgroup.normalizer (Y : Set G)) (hNY : N ≤ Y)
    (h : ∀ k ∈ K, Odd (orderOf k) → ∀ v ∈ Y, ⁅k, v⁆ ∈ N) {k : G}
    (hk : k ∈ Subgroup.closure {g | g ∈ K ∧ Odd (orderOf g)}) : ∀ v ∈ Y, ⁅k, v⁆ ∈ N := by
  have hK : Subgroup.closure {g | g ∈ K ∧ Odd (orderOf g)} ≤ K :=
    (Subgroup.closure_le _).mpr fun g hg => hg.1
  induction hk using Subgroup.closure_induction with
  | mem g hg => exact h g hg.1 hg.2
  | one =>
    intro v _
    rw [commutatorElement_one_left]
    exact N.one_mem
  | mul a b _ _ iha ihb =>
    intro v hv
    have e : ⁅a * b, v⁆ = ⁅a, ⁅b, v⁆⁆ * ⁅b, v⁆ * ⁅a, v⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem (N.mul_mem (iha _ (hNY (ihb v hv))) (ihb v hv)) (iha v hv)
  | inv a ha iha =>
    intro v hv
    have hv' : a⁻¹ * v * a⁻¹⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hKY (K.inv_mem (hK ha))) v).mp hv
    have e : ⁅a⁻¹, v⁆ = ⁅a, a⁻¹ * v * a⁻¹⁻¹⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.inv_mem (iha _ hv')

end General

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem map_conj_vv_eq_of_usup (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {x ℓ ℓ' : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ) (hxℓ' : (puAmalgam c.pu.le).treeGraph.Adj x ℓ')
    {k : (puAmalgam c.pu.le).Universal} (hk : k ∈ stab (puAmalgam c.pu.le) x)
    (he : Usup (puAmalgam c.pu.le) x (k • ℓ) = Usup _ x ℓ') :
    (Vv (puAmalgam c.pu.le) ℓ).map (MulAut.conj k).toMonoidHom = Vv _ ℓ' := by
  have hkx : k • x = x := MulAction.mem_stabilizer_iff.mp hk
  have hxkℓ : (puAmalgam c.pu.le).treeGraph.Adj x (k • ℓ) := by
    have := (adj_smul _ k x ℓ).mpr hxℓ
    rwa [hkx] at this
  rw [← vv_eq_of_usup_eq h464 h465 h466a c hx hxkℓ hxℓ' he]
  exact (vi_smul _ k ℓ 2).symm

theorem usup_smul_eq_of_ptTheta (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)}
    (hψU : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1)
    (hT : natImage ψ (Qv (puAmalgam c.pu.le) β) = qLn) (g : ↥(ptL (puAmalgam c.pu.le) x ψ))
    (hg : ((ptTheta ψ g : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single 0 1) 1 = 0) :
    Usup (puAmalgam c.pu.le) x ((g : (puAmalgam c.pu.le).Universal) • β) = Usup _ x β := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hgs : (g : (puAmalgam c.pu.le).Universal) ∈ stab _ x := ptL_le_stab ψ g.2
  have hA := (mem_ptL_iff.mp g.2).snd
  have he1 : (fun j : Fin 2 => (Pi.single 1 1 : Fin 3 → F) j.succ) = Pi.single 0 1 := by
    funext j
    fin_cases j <;> simp
  have hW : (ln01 : Submodule F (Fin 3 → F)).map (Matrix.mulVecLin
      ((toSL3 ψ ⟨g, hgs⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F)) = ln01 := by
    refine map_eq_ln01_of_mem hA finrank_ln01 (by simp [mem_ln01]) (w := Pi.single 1 1)
      (by simp [mem_ln01]) (by simp [mem_pt0]) ?_
    have h2 := mulVec_succ_of_mem_stabE0 hA (Pi.single 1 1) 1
    rw [show (Fin.succ (1 : Fin 2) : Fin 3) = 2 from rfl] at h2
    rw [h2, he1, ← ptTheta_apply]
    exact hg
  have hkx : (g : (puAmalgam c.pu.le).Universal) • x = x := MulAction.mem_stabilizer_iff.mp hgs
  have h1 := usup_smul (puAmalgam c.pu.le) (g : (puAmalgam c.pu.le).Universal) x β
  rw [hkx] at h1
  rw [h1]
  exact map_conj_eq_of_coord hψU (usup_le_uloc' c.pu hfull hx hxβ)
    (usup_le_uloc' c.pu hfull hx hxβ) (mem_usup_iff_ln01 h464 h465 c hx hxβ hψU hT)
    (mem_usup_iff_ln01 h464 h465 c hx hxβ hψU hT) ⟨g, hgs⟩ hW

theorem key_at_line (h464 : I464) (h465 : I465) (h466a : I466a) {c : Hyp46 M T L φ}
    (hq : 4 ≤ Fintype.card F) {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P)
    {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψU : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1)
    (hPc : ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔
      natVec hψU u ∈ pt0)
    (hT : natImage ψ (Qv (puAmalgam c.pu.le) β) = qLn)
    {N : Subgroup (puAmalgam c.pu.le).Universal} {βv : ↥N →* Multiplicative (Fin 2 → F)}
    (hUN : ptSub (puAmalgam c.pu.le) x P ≤ N) (hNY : N ≤ pencil (puAmalgam c.pu.le) x P)
    (hβker : ∀ y : ↥N, βv y = 1 ↔ (y : (puAmalgam c.pu.le).Universal) ∈ ptSub _ x P)
    (hodd : ∀ k ∈ ptL (puAmalgam c.pu.le) x ψ, Odd (orderOf k) →
      ∀ v ∈ pencil (puAmalgam c.pu.le) x P, ⁅k, v⁆ ∈ N)
    (hβeq : ∀ (k : ↥(ptL (puAmalgam c.pu.le) x ψ)) (u v : ↥N),
      (v : (puAmalgam c.pu.le).Universal) = k * u * k⁻¹ →
      Multiplicative.toAdd (βv v) =
        (ptTheta ψ k : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (βv u))
    {m : Vtx (puAmalgam c.pu.le)} (hxm : (puAmalgam c.pu.le).treeGraph.Adj x m)
    (hPm : P ≤ Usup (puAmalgam c.pu.le) x m) (hmβ : Usup (puAmalgam c.pu.le) x m ≠ Usup _ x β) :
    pencil (puAmalgam c.pu.le) x P ≤ Vv _ β ⊔ Vv _ m ⊔ ptSub _ x P := by
  classical
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hchar : CharP F 2 := charP_two_of_isSL3FullVia c.via
  have hβ : ¬ IsMVtx (puAmalgam c.pu.le) β := (isMVtx_iff_of_adj _ hxβ).mp hx
  have hPU := le_uloc_of_isPtOn c hx hP
  have hPZ : P ≤ ZM (puAmalgam c.pu.le) x := hPU.trans (uloc_le_zm c.pu hfull hx)
  have hPβ : P ≤ Usup (puAmalgam c.pu.le) x β := by
    obtain ⟨_, _, _, he⟩ := hP
    rw [he]
    exact inf_le_left
  set K := ptL (puAmalgam c.pu.le) x ψ with hKdef
  set Y := pencil (puAmalgam c.pu.le) x P with hYdef
  set U := ptSub (puAmalgam c.pu.le) x P with hUdef
  have hKs : K ≤ stab (puAmalgam c.pu.le) x := ptL_le_stab ψ
  have hKP : K ≤ Subgroup.normalizer (P : Set (puAmalgam c.pu.le).Universal) :=
    ptL_le_normalizer c hψU hPU hPc
  have hKY : K ≤ Subgroup.normalizer (Y : Set (puAmalgam c.pu.le).Universal) :=
    le_normalizer_pencil hKs hKP
  have hKU : K ≤ Subgroup.normalizer (U : Set (puAmalgam c.pu.le).Universal) :=
    le_normalizer_ptSub hKs hKP
  have : Finite ↥(stab (puAmalgam c.pu.le) x) := finite_stab c.pu hx
  have : Finite ↥K := Finite.of_injective _ (Subgroup.inclusion_injective hKs)
  have hZU : ZM (puAmalgam c.pu.le) x ≤ U := zm_le_ptSub c hx hP
  have hUY : U ≤ Y := ptSub_le_pencil x P
  have hYY : ∀ v ∈ Y, ∀ w ∈ Y, ⁅v, w⁆ ∈ U := fun v hv w hw =>
    hZU (sup_le hPZ (zloc_le_zm c.pu hfull hx)
      (commutator_pencil_pencil_le h464 h465 h466a c hx hxβ hP
        (Subgroup.commutator_mem_commutator hv hw)))
  have hYU : ∀ v ∈ Y, ∀ u ∈ U, v * u * v⁻¹ ∈ U := fun v hv u hu => by
    have e : v * u * v⁻¹ = ⁅v, u⁆ * u := by rw [commutatorElement_def]; group
    rw [e]
    exact U.mul_mem (hYY v hv u (hUY hu)) hu
  set K₀ := Subgroup.closure {g | g ∈ K ∧ Odd (orderOf g)} with hK₀def
  have hK₀K : K₀ ≤ K := (Subgroup.closure_le _).mpr fun g hg => hg.1
  have hK₀c : ∀ k ∈ K₀, ∀ v ∈ Y, ⁅k, v⁆ ∈ N := fun k hk =>
    commutator_mem_of_mem_closure_odd hKY hNY hodd hk
  have hK₀N : ∀ k ∈ K₀, ∀ n ∈ N, k * n * k⁻¹ ∈ N := fun k hk n hn => by
    have e : k * n * k⁻¹ = ⁅k, n⁆ * n := by rw [commutatorElement_def]; group
    rw [e]
    exact N.mul_mem (hK₀c k hk n (hNY hn)) hn
  have hoddK₀ : ∀ h : ↥K, Odd (orderOf h) → (h : (puAmalgam c.pu.le).Universal) ∈ K₀ :=
    fun h hh => Subgroup.subset_closure ⟨h.2, by rwa [Subgroup.orderOf_coe]⟩
  have hβU : ∀ (u n : (puAmalgam c.pu.le).Universal) (hu : u ∈ U) (hn : n ∈ N)
      (hun : u * n ∈ N), βv ⟨u * n, hun⟩ = βv ⟨n, hn⟩ := by
    intro u n hu hn hun
    have e : (⟨u * n, hun⟩ : ↥N) = ⟨u, hUN hu⟩ * ⟨n, hn⟩ := rfl
    rw [e, map_mul, (hβker _).mpr hu, one_mul]
  have hfixβ : ∀ g : ↥K, ((ptTheta ψ g : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single 0 1) 1 = 0 →
      ∀ v ∈ Vv (puAmalgam c.pu.le) β, (g : (puAmalgam c.pu.le).Universal) * v * (g : _)⁻¹ ∈
        Vv (puAmalgam c.pu.le) β := fun g hg v hv => by
    rw [← map_conj_vv_eq_of_usup h464 h465 h466a c hx hxβ hxβ (hKs g.2)
      (usup_smul_eq_of_ptTheta h464 h465 c hx hxβ hψU hT g hg)]
    exact conj_mem_map_conj hv
  have hline : ∀ m', (puAmalgam c.pu.le).treeGraph.Adj x m' → P ≤ Usup _ x m' →
      ∃ k ∈ K₀, (Vv (puAmalgam c.pu.le) β).map (MulAut.conj k).toMonoidHom = Vv _ m' ∧
        Usup (puAmalgam c.pu.le) x (k • β) = Usup _ x m' := fun m' hxm' hPm' => by
    obtain ⟨k, hk, he⟩ := exists_closure_odd_smul h464 h465 c hx hψs hψU hPc hxβ hxm' hPβ hPm'
    exact ⟨k, hk, map_conj_vv_eq_of_usup h464 h465 h466a c hx hxβ hxm' (hKs (hK₀K hk)) he, he⟩
  have hline' : ∀ m', (puAmalgam c.pu.le).treeGraph.Adj x m' → P ≤ Usup _ x m' →
      Usup (puAmalgam c.pu.le) x m' ≠ Usup _ x β →
      ∃ (k : _) (hk : k ∈ K₀),
        (Vv (puAmalgam c.pu.le) β).map (MulAut.conj k).toMonoidHom = Vv _ m' ∧
        ∃ f : Fin 2 → F,
          (ptTheta ψ ⟨k, hK₀K hk⟩ : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single 0 1 = f ∧ f 1 ≠ 0 :=
    fun m' hxm' hPm' hne => by
      obtain ⟨k, hk, hkV, hkU⟩ := hline m' hxm' hPm'
      exact ⟨k, hk, hkV, _, rfl, fun h0 => hne (by
        rw [← hkU]
        exact usup_smul_eq_of_ptTheta h464 h465 c hx hxβ hψU hT ⟨k, hK₀K hk⟩ h0)⟩
  have hYle : Y ≤ Vv (puAmalgam c.pu.le) β ⊔ N := by
    refine pencil_le fun m' hxm' hPm' => ?_
    obtain ⟨k, hk, hkV, -⟩ := hline m' hxm' hPm'
    rw [← hkV]
    rintro _ ⟨v, hv, rfl⟩
    have e : (MulAut.conj k).toMonoidHom v = ⁅k, v⁆ * v := by
      simp [commutatorElement_def, mul_assoc]
    rw [e, sup_comm]
    exact Subgroup.mul_mem_sup (hK₀c k hk v (vv_le_pencil hxβ hPβ hv)) hv
  obtain ⟨t, ht, hte⟩ : ∃ t ∈ (Qv (puAmalgam c.pu.le) β).subgroupOf K,
      ptTheta ψ t = SL2Model.e12 1 := by
    have h1 : SL2Model.e12 (1 : F) ∈ ((Qv (puAmalgam c.pu.le) β).subgroupOf K).map (ptTheta ψ) :=
      by rw [map_ptTheta_qv hT]; exact SL2Model.e12_mem_Rg 1
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.mp h1
    exact ⟨t, ht, hte⟩
  have hA1 : ∀ n (hn : n ∈ N), n ∈ Vv (puAmalgam c.pu.le) β →
      Multiplicative.toAdd (βv ⟨n, hn⟩) 1 = 0 := by
    intro n hn hnV
    have htQ : (t : (puAmalgam c.pu.le).Universal) ∈ Qv (puAmalgam c.pu.le) β :=
      Subgroup.mem_subgroupOf.mp ht
    have hc : ⁅(t : (puAmalgam c.pu.le).Universal), n⁆ ∈ U := by
      rw [← commutatorElement_inv]
      exact U.inv_mem (hZU (zh_le_zm _ hxβ (commutator_vv_qv_le_zh c.pu h464' hβ
        (Subgroup.commutator_mem_commutator hnV htQ))))
    have e : (t : (puAmalgam c.pu.le).Universal) * n * (t : (puAmalgam c.pu.le).Universal)⁻¹ =
        ⁅(t : (puAmalgam c.pu.le).Universal), n⁆ * n := by
      rw [commutatorElement_def]; group
    have hmem : ⁅(t : (puAmalgam c.pu.le).Universal), n⁆ * n ∈ N := N.mul_mem (hUN hc) hn
    have h1 := hβeq t ⟨n, hn⟩ ⟨_, hmem⟩ e.symm
    rw [hβU _ n hc hn hmem, hte, SL2Model.e12_coe] at h1
    have h2 := congrFun h1 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h2
    exact h2
  by_cases hcase : ∃ n ∈ N, n ∈ Vv (puAmalgam c.pu.le) β ∧ n ∉ U
  ·
    obtain ⟨n₀, hn₀N, hn₀V, hn₀U⟩ := hcase
    set w₀ := Multiplicative.toAdd (βv ⟨n₀, hn₀N⟩) with hw₀def
    have hw₀1 : w₀ 1 = 0 := hA1 n₀ hn₀N hn₀V
    have hw₀0 : w₀ 0 ≠ 0 := by
      intro h0
      apply hn₀U
      refine (hβker ⟨n₀, hn₀N⟩).mp ?_
      have hw : w₀ = 0 := by
        funext i
        fin_cases i
        · exact h0
        · exact hw₀1
      exact hw
    have hfill : ∀ a : F, ∃ n, ∃ hn : n ∈ N, n ∈ Vv (puAmalgam c.pu.le) β ∧
        Multiplicative.toAdd (βv ⟨n, hn⟩) = a • Pi.single 0 1 := by
      intro a
      by_cases ha : a = 0
      · refine ⟨1, N.one_mem, (Vv _ β).one_mem, ?_⟩
        rw [ha, zero_smul]
        have e : (⟨1, N.one_mem⟩ : ↥N) = 1 := rfl
        rw [e, map_one]
        rfl
      · set s : Fˣ := Units.mk0 (a / w₀ 0) (div_ne_zero ha hw₀0) with hsdef
        obtain ⟨h, hh, hho⟩ :=
          exists_odd_preimage_of_surjective (ptTheta_surjective hψs) (odd_orderOf_diagTwo s)
        have hhβ := hfixβ h (by rw [hh, diagTwo_mulVec]; simp)
        have hmemN := hK₀N _ (hoddK₀ h hho) n₀ hn₀N
        refine ⟨_, hmemN, hhβ n₀ hn₀V, ?_⟩
        rw [hβeq h ⟨n₀, hn₀N⟩ ⟨_, hmemN⟩ rfl, hh, diagTwo_mulVec, ← hw₀def, hw₀1]
        funext i
        fin_cases i
        · simp [hsdef, div_mul_cancel₀ _ hw₀0]
        · simp
    obtain ⟨k₀, hk₀, hk₀V, f, hfdef, hf⟩ := hline' m hxm hPm hmβ
    have hNle : N ≤ Vv (puAmalgam c.pu.le) β ⊔ Vv _ m ⊔ U := by
      intro n hn
      set w := Multiplicative.toAdd (βv ⟨n, hn⟩) with hwdef
      obtain ⟨n₁, hn₁N, hn₁V, hn₁w⟩ := hfill (w 0 - w 1 / f 1 * f 0)
      obtain ⟨n₂, hn₂N, hn₂V, hn₂w⟩ := hfill (w 1 / f 1)
      have hn₂'N := hK₀N k₀ hk₀ n₂ hn₂N
      have hn₂'V : k₀ * n₂ * k₀⁻¹ ∈ Vv (puAmalgam c.pu.le) m := by
        rw [← hk₀V]
        exact conj_mem_map_conj hn₂V
      have hw₂ : Multiplicative.toAdd (βv ⟨_, hn₂'N⟩) = (w 1 / f 1) • f := by
        rw [hβeq ⟨k₀, hK₀K hk₀⟩ ⟨n₂, hn₂N⟩ ⟨_, hn₂'N⟩ rfl, hn₂w, Matrix.mulVec_smul, hfdef]
      have hmem : (n₁ * (k₀ * n₂ * k₀⁻¹))⁻¹ * n ∈ N :=
        N.mul_mem (N.inv_mem (N.mul_mem hn₁N hn₂'N)) hn
      have hu : (n₁ * (k₀ * n₂ * k₀⁻¹))⁻¹ * n ∈ U := by
        refine (hβker ⟨_, hmem⟩).mp ?_
        have e : (⟨_, hmem⟩ : ↥N) = (⟨n₁, hn₁N⟩ * ⟨_, hn₂'N⟩)⁻¹ * ⟨n, hn⟩ := rfl
        rw [e, map_mul, map_inv, map_mul]
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_inv, toAdd_mul, hn₁w, hw₂, ← hwdef, toAdd_one]
        funext i
        fin_cases i
        · simp
          field_simp
          ring
        · simp
          field_simp
          ring
      have e : n = n₁ * (k₀ * n₂ * k₀⁻¹) * ((n₁ * (k₀ * n₂ * k₀⁻¹))⁻¹ * n) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left hn₁V))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right hn₂'V))) (Subgroup.mem_sup_right hu)
    exact hYle.trans (sup_le (le_sup_left.trans le_sup_left) hNle)
  ·
    push Not at hcase
    obtain ⟨a, ha⟩ : ∃ a : Fˣ, a ≠ 1 := by
      have h1 : 1 < Fintype.card Fˣ := by rw [Fintype.card_units]; omega
      exact Fintype.exists_ne_of_one_lt_card h1 1
    have hnorm : Vv (puAmalgam c.pu.le) β ≤
        Subgroup.normalizer (N : Set (puAmalgam c.pu.le).Universal) := by
      intro v hv
      rw [Subgroup.mem_normalizer_iff]
      intro n
      have hvY : v ∈ Y := vv_le_pencil hxβ hPβ hv
      constructor
      · intro hn
        have e : v * n * v⁻¹ = ⁅v, n⁆ * n := by rw [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem (hUN (hYY v hvY n (hNY hn))) hn
      · intro hn
        have hv' : v⁻¹ ∈ Y := Y.inv_mem hvY
        have e : n = ⁅v⁻¹, v * n * v⁻¹⁆ * (v * n * v⁻¹) := by
          rw [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem (hUN (hYY _ hv' _ (hNY hn))) hn
    have hYβ : Y ≤ Vv (puAmalgam c.pu.le) β ⊔ U := by
      refine pencil_le fun m' hxm' hPm' => ?_
      by_cases hm'β : Usup (puAmalgam c.pu.le) x m' = Usup _ x β
      · rw [vv_eq_of_usup_eq h464 h465 h466a c hx hxm' hxβ hm'β]
        exact le_sup_left
      obtain ⟨k, hk, hkV, f, hfdef, hkf⟩ := hline' m' hxm' hPm' hm'β
      have hkK : k ∈ K := hK₀K hk
      have hm'N : ∀ n ∈ N, n ∈ Vv (puAmalgam c.pu.le) m' → n ∈ U := by
        intro n hn hnV
        rw [← hkV] at hnV
        obtain ⟨v, hv, rfl⟩ := hnV
        have e : (MulAut.conj k).toMonoidHom v = k * v * k⁻¹ := rfl
        rw [e] at hn ⊢
        have hvN : v ∈ N := by
          have h1 := hK₀N k⁻¹ (K₀.inv_mem hk) _ hn
          rwa [show k⁻¹ * (k * v * k⁻¹) * k⁻¹⁻¹ = v by group] at h1
        exact (Subgroup.mem_normalizer_iff.mp (hKU hkK) v).mp (hcase v hvN hv)
      obtain ⟨⟨g, hgK⟩, hh, hho⟩ := exists_odd_preimage_of_surjective
        (ptTheta_surjective hψs) (odd_orderOf_torus a (f 0 / f 1))
      have hgo : Odd (orderOf g) := by rwa [Subgroup.orderOf_mk] at hho
      have hgβ := hfixβ ⟨g, hgK⟩ (by rw [hh, torus_mulVec]; simp)
      have hgm' : ∀ v ∈ Vv (puAmalgam c.pu.le) m', g * v * g⁻¹ ∈ Vv (puAmalgam c.pu.le) m' := by
        intro v hv
        rw [← hkV] at hv ⊢
        obtain ⟨u, hu, rfl⟩ := hv
        have hθ' : ((ptTheta ψ ((⟨k, hkK⟩ : ↥K)⁻¹ * ⟨g, hgK⟩ * ⟨k, hkK⟩) :
            Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single 0 1) = ((a⁻¹ : Fˣ) : F) • Pi.single 0 1 := by
          rw [map_mul, map_mul, map_inv, hh]
          refine mulVec_conj_eq_smul _ _ ?_
          rw [hfdef]
          exact torus_mulVec_of_ne a hkf
        have h1 := hfixβ _ (by rw [hθ']; simp) u hu
        have e : g * (MulAut.conj k).toMonoidHom u * g⁻¹ =
            k * ((k⁻¹ * g * k) * u * (k⁻¹ * g * k)⁻¹) * k⁻¹ := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [e]
        exact conj_mem_map_conj h1
      intro v' hv'
      have hv'Y : v' ∈ Y := vv_le_pencil hxm' hPm' hv'
      have h1 : v' ∈ ((Vv (puAmalgam c.pu.le) β ⊔ N : Subgroup _) : Set _) := hYle hv'Y
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at h1
      obtain ⟨v, hv, n, hn, rfl⟩ := h1
      have hvY : v ∈ Y := vv_le_pencil hxβ hPβ hv
      have hcv : ⁅g, v⁆ ∈ U := by
        refine hcase _ (hodd g hgK hgo v hvY) ?_
        rw [commutatorElement_def]
        exact (Vv _ β).mul_mem (hgβ v hv) ((Vv _ β).inv_mem hv)
      have hcv' : ⁅g, v * n⁆ ∈ U := by
        refine hm'N _ (hodd g hgK hgo _ hv'Y) ?_
        rw [commutatorElement_def]
        exact (Vv _ m').mul_mem (hgm' _ hv') ((Vv _ m').inv_mem hv')
      have hcn : ⁅g, n⁆ ∈ U := by
        have e : ⁅g, n⁆ = v⁻¹ * (⁅g, v⁆⁻¹ * ⁅g, v * n⁆) * v⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact hYU _ (Y.inv_mem hvY) _ (U.mul_mem (U.inv_mem hcv) hcv')
      have e : g * n * g⁻¹ = ⁅g, n⁆ * n := by rw [commutatorElement_def]; group
      have hmem : ⁅g, n⁆ * n ∈ N := N.mul_mem (hUN hcn) hn
      have h2 := hβeq ⟨g, hgK⟩ ⟨n, hn⟩ ⟨_, hmem⟩ e.symm
      rw [hβU _ n hcn hn hmem, hh] at h2
      have h3 := eq_zero_of_torus_mulVec (f 0 / f 1) ha h2.symm
      have hnU : n ∈ U := (hβker ⟨n, hn⟩).mp h3
      exact Subgroup.mul_mem_sup hv hnU
    exact hYβ.trans (sup_le_sup_right le_sup_left _)

theorem key_of_natural (h464 : I464) (h465 : I465) (h466a : I466a) {c : Hyp46 M T L φ}
    (hq : 4 ≤ Fintype.card F) {x β : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P)
    {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψU : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1)
    (hPc : ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔
      natVec hψU u ∈ pt0)
    (hT : natImage ψ (Qv (puAmalgam c.pu.le) β) = qLn)
    {N : Subgroup (puAmalgam c.pu.le).Universal} {βv : ↥N →* Multiplicative (Fin 2 → F)}
    (hUN : ptSub (puAmalgam c.pu.le) x P ≤ N) (hNY : N ≤ pencil (puAmalgam c.pu.le) x P)
    (hβker : ∀ y : ↥N, βv y = 1 ↔ (y : (puAmalgam c.pu.le).Universal) ∈ ptSub _ x P)
    (hodd : ∀ k ∈ ptL (puAmalgam c.pu.le) x ψ, Odd (orderOf k) →
      ∀ v ∈ pencil (puAmalgam c.pu.le) x P, ⁅k, v⁆ ∈ N)
    (hβeq : ∀ (k : ↥(ptL (puAmalgam c.pu.le) x ψ)) (u v : ↥N),
      (v : (puAmalgam c.pu.le).Universal) = k * u * k⁻¹ →
      Multiplicative.toAdd (βv v) =
        (ptTheta ψ k : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (βv u)) :
    ∀ ℓ ℓ', (puAmalgam c.pu.le).treeGraph.Adj x ℓ → (puAmalgam c.pu.le).treeGraph.Adj x ℓ' →
      P ≤ Usup (puAmalgam c.pu.le) x ℓ → P ≤ Usup (puAmalgam c.pu.le) x ℓ' →
      Usup (puAmalgam c.pu.le) x ℓ ≠ Usup _ x ℓ' →
      pencil (puAmalgam c.pu.le) x P ≤ Vv _ ℓ ⊔ Vv _ ℓ' ⊔ ptSub _ x P := by
  intro ℓ ℓ' hxℓ hxℓ' hPℓ hPℓ' hne
  have hPU := le_uloc_of_isPtOn c hx hP
  have hPβ : P ≤ Usup (puAmalgam c.pu.le) x β := by
    obtain ⟨_, _, _, he⟩ := hP
    rw [he]
    exact inf_le_left
  have hKs : ptL (puAmalgam c.pu.le) x ψ ≤ stab _ x := ptL_le_stab ψ
  have hKP : ptL (puAmalgam c.pu.le) x ψ ≤
      Subgroup.normalizer (P : Set (puAmalgam c.pu.le).Universal) :=
    ptL_le_normalizer c hψU hPU hPc
  obtain ⟨k, hk, hkℓ⟩ := exists_closure_odd_smul h464 h465 c hx hψs hψU hPc hxℓ hxβ hPℓ hPβ
  have hkK : k ∈ ptL (puAmalgam c.pu.le) x ψ := (Subgroup.closure_le _).mpr (fun g hg => hg.1) hk
  have hkx : k • x = x := MulAction.mem_stabilizer_iff.mp (hKs hkK)
  have hU : ∀ n, Usup (puAmalgam c.pu.le) x (k • n) =
      (Usup (puAmalgam c.pu.le) x n).map (MulAut.conj k).toMonoidHom := fun n => by
    have h1 := usup_smul (puAmalgam c.pu.le) k x n
    rwa [hkx] at h1
  have hxkℓ' : (puAmalgam c.pu.le).treeGraph.Adj x (k • ℓ') := by
    have := (adj_smul _ k x ℓ').mpr hxℓ'
    rwa [hkx] at this
  have hPkℓ' : P ≤ Usup (puAmalgam c.pu.le) x (k • ℓ') := by
    rw [hU, ← map_conj_eq_of_mem_normalizer (hKP hkK)]
    exact Subgroup.map_mono hPℓ'
  have hne' : Usup (puAmalgam c.pu.le) x (k • ℓ') ≠ Usup _ x β := by
    rw [← hkℓ, hU, hU]
    exact fun h => hne (Subgroup.map_injective (MulAut.conj k).injective h).symm
  have h1 := key_at_line (c := c) h464 h465 h466a hq hx hxβ hP hψs hψU hPc hT hUN hNY hβker hodd
    hβeq hxkℓ' hPkℓ' hne'
  have hVℓ := map_conj_vv_eq_of_usup h464 h465 h466a c hx hxℓ hxβ (hKs hkK) hkℓ
  have hVℓ' : Vv (puAmalgam c.pu.le) (k • ℓ') =
      (Vv (puAmalgam c.pu.le) ℓ').map (MulAut.conj k).toMonoidHom := vi_smul _ k ℓ' 2
  have hY : (pencil (puAmalgam c.pu.le) x P).map (MulAut.conj k).toMonoidHom =
      pencil (puAmalgam c.pu.le) x P :=
    map_conj_eq_of_mem_normalizer (le_normalizer_pencil hKs hKP hkK)
  have hUU : (ptSub (puAmalgam c.pu.le) x P).map (MulAut.conj k).toMonoidHom =
      ptSub (puAmalgam c.pu.le) x P :=
    map_conj_eq_of_mem_normalizer (le_normalizer_ptSub hKs hKP hkK)
  rw [← hVℓ, hVℓ', ← hY, ← hUU, ← Subgroup.map_sup, ← Subgroup.map_sup] at h1
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj k).injective).mp h1

end CFSG.Quasithin.MS93.S46R

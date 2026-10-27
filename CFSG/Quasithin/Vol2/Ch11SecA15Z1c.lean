module

public import CFSG.Quasithin.Vol2.Ch11SecA15Z1b
public import CFSG.Quasithin.Vol2.Ch11SecA15R1b
public import CFSG.Quasithin.Vol2.Ch11SecA15Z1
public import CFSG.Quasithin.Vol2.Ch11SecAFacts15c

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped Matrix IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem exists_V1_of_sp4Block (hF : Facts15c) (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁) (hB : IsSp4Block L) {z : G}
    (hz : z ∈ centerOf (ROf T L V₁)) :
    ∃ u ∈ V₁, u⁻¹ * z ∈ Subgroup.centralizer (L : Set G) := by
  classical
  obtain ⟨hS, F, _, _, hF4, α, hα, hker, β, hβs, hβker, hβ⟩ := hB
  have hF4' : Fintype.card F = 2 ^ 2 := by rw [hF4]; norm_num
  obtain ⟨hk, h2n⟩ := kindSp4_of_modO2Surj hG2 h1102 h hF4' ⟨hα, hker⟩
  subst h2n
  obtain ⟨_, K, _, _, π, hK, hπ⟩ := sp4_realization hG2 h1102 h hk
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hflag := isFlagW_of_isVi h hU
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at hflag
  have hRC := hF.cocycleSp4 K hK4 _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ hflag
  unfold RadicalCocycle at hRC
  rw [← autOn_lOf_eq h hU] at hRC
  have hz0 := centerOf_ROf_le_pCoreOf_msG0 h hz
  have hzc : ∀ l ∈ L, l * z * l⁻¹ * z⁻¹ ∈ blockU L := commutator_mem_blockU h hz0
  have hzk : ∀ k ∈ pCoreOf 2 L, k * z = z * k := fun k hk => commute_of_mem_centerOf_ROf h hz hk
  have hVU := fsuV_le_blockU h1102 h
  let bb : G → (Fin 2 ⊕ Fin 2 → F) := fun x =>
    if hx : x ∈ blockU L then Multiplicative.toAdd (β ⟨x, hx⟩) else 0
  have bb_def : ∀ x (hx : x ∈ blockU L), bb x = Multiplicative.toAdd (β ⟨x, hx⟩) :=
    fun x hx => dite_eq_left hx
  have bb_mul : ∀ x ∈ blockU L, ∀ y ∈ blockU L, bb (x * y) = bb x + bb y := by
    intro x hx y hy
    rw [bb_def _ (Subgroup.mul_mem _ hx hy), bb_def x hx, bb_def y hy, ← toAdd_mul, ← map_mul]
    rfl
  have bb_inv : ∀ x ∈ blockU L, bb x⁻¹ = - bb x := by
    intro x hx
    rw [bb_def _ (Subgroup.inv_mem _ hx), bb_def x hx, ← toAdd_inv, ← map_inv]
    rfl
  have bb_conj : ∀ l (hl : l ∈ L), ∀ x ∈ blockU L,
      bb (l * x * l⁻¹) = ((α ⟨l, hl⟩ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ bb x := by
    intro l hl x hx
    have hx' : l * x * l⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockU L hl) x).mp hx
    rw [bb_def _ hx', bb_def x hx]
    exact hβ ⟨l, hl⟩ ⟨x, hx⟩ ⟨_, hx'⟩ rfl
  have bb_zero : ∀ x ∈ blockU L, bb x = 0 ↔ x ∈ blockZ L := by
    intro x hx
    rw [bb_def x hx]
    constructor
    · intro h0
      have : (⟨x, hx⟩ : ↥(blockU L)) ∈ β.ker := by
        rw [MonoidHom.mem_ker]
        exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
      rw [hβker, Subgroup.mem_subgroupOf] at this
      exact this
    · intro h0
      have : (⟨x, hx⟩ : ↥(blockU L)) ∈ β.ker := by
        rw [hβker, Subgroup.mem_subgroupOf]
        exact h0
      rw [MonoidHom.mem_ker] at this
      rw [this, toAdd_one]
  have hdec : ∀ l ∈ L, ∃ v ∈ fsuV T I, bb v = bb (l * z * l⁻¹ * z⁻¹) := by
    intro l hl
    have hmem : l * z * l⁻¹ * z⁻¹ ∈ ((fsuV T I ⊔ blockZ L : Subgroup G) : Set G) := by
      rw [fsuV_sup_blockZ h1102 h hS]; exact hzc l hl
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
      ((blockZ_le_centralizer_fsuV h1102 h hS).trans
        (Subgroup.centralizer_le_normalizer _))] at hmem
    obtain ⟨v, hv, c, hc, he⟩ := hmem
    refine ⟨v, hv, ?_⟩
    rw [← he, bb_mul v (hVU hv) c hc.1, (bb_zero c hc.1).mpr hc, add_zero]
  choose vrep hvrep hbbvrep using hdec
  have hsec : ∀ g : ↥(autOn L (fsuV T I)), ∃ l, ∃ _ : l ∈ L,
      ∃ hlV : l ∈ Subgroup.normalizer (fsuV T I : Set G),
        (g : MulAut ↥(fsuV T I)) = conjV (fsuV T I) l hlV := fun g => mem_autOn_iff.mp g.2
  choose lrep hlrep hlrepV hlrepeq using hsec
  let d : ↥(autOn L (fsuV T I)) → ↥(fsuV T I) := fun g =>
    ⟨vrep (lrep g) (hlrep g), hvrep _ _⟩
  have hdg : ∀ (g : ↥(autOn L (fsuV T I))) (l : G) (hl : l ∈ L)
      (hlV : l ∈ Subgroup.normalizer (fsuV T I : Set G)),
      (g : MulAut ↥(fsuV T I)) = conjV (fsuV T I) l hlV →
        bb (d g : G) = bb (l * z * l⁻¹ * z⁻¹) := by
    intro g l hl hlV hg
    change bb (vrep (lrep g) (hlrep g)) = _
    rw [hbbvrep, commutator_eq_of_conjV_eq h1102 h hzk (hlrep g) hl (hlrepV g) hlV
      ((hlrepeq g).symm.trans hg)]
  have hZ : ∀ x : ↥(fsuV T I), bb (x : G) = 0 →
      x ∈ (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact ((bb_zero _ (hVU x.2)).mp hx).2
  have hcoc : ∀ g g' : ↥(autOn L (fsuV T I)),
      d (g * g') * ((g : MulAut ↥(fsuV T I)) (d g') * d g)⁻¹ ∈
        (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) := by
    intro g g'
    apply hZ
    set a := lrep g with ha
    set b := lrep g' with hb
    have haL := hlrep g
    have hbL := hlrep g'
    have hab : ((g * g' : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) =
        conjV (fsuV T I) (a * b) (Subgroup.mul_mem _ (hlrepV g) (hlrepV g')) := by
      rw [conjV_mul (fsuV T I) (hlrepV g) (hlrepV g'), Subgroup.coe_mul, ← hlrepeq g,
        ← hlrepeq g']
    have h1 := hdg (g * g') (a * b) (L.mul_mem haL hbL) _ hab
    have h2 := hdg g a haL (hlrepV g) (hlrepeq g)
    have h3 := hdg g' b hbL (hlrepV g') (hlrepeq g')
    have hgd : (((g : MulAut ↥(fsuV T I)) (d g') : ↥(fsuV T I)) : G) = a * (d g' : G) * a⁻¹ := by
      rw [hlrepeq g, conjV_apply_coe]
    have hdV : ∀ g'' : ↥(autOn L (fsuV T I)), (d g'' : G) ∈ blockU L := fun g'' => hVU (d g'').2
    have hcomm : a * b * z * (a * b)⁻¹ * z⁻¹ =
        a * (b * z * b⁻¹ * z⁻¹) * a⁻¹ * (a * z * a⁻¹ * z⁻¹) := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgd]
    rw [bb_mul _ (hdV _) _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
        ((Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockU L haL) _).mp (hdV g')) (hdV g))),
      bb_inv _ (Subgroup.mul_mem _
        ((Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockU L haL) _).mp (hdV g')) (hdV g)),
      bb_mul _ ((Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockU L haL) _).mp (hdV g'))
        _ (hdV g),
      bb_conj a haL _ (hdV g'), h1, h2, h3, hcomm,
      bb_mul _ ((Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockU L haL) _).mp (hzc b hbL))
        _ (hzc a haL),
      bb_conj a haL _ (hzc b hbL)]
    abel
  have hX : LOf L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    lOf_le_L.trans (L_le_normalizer_fsuV h)
  have hvan : ∀ (x : ↥(autOn L (fsuV T I))) (y : ↥(autOn (LOf L V₁) (fsuV T I))),
      y ∈ CFSG.pCore 2 ↥(autOn (LOf L V₁) (fsuV T I)) → (y : MulAut ↥(fsuV T I)) = x →
        d x ∈ (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) := by
    intro x y hy hyx
    obtain ⟨k, hk, rfl⟩ := exists_mem_pCoreOf_of_mem_pCore hX
      (isPGroup_lOf_inf_centralizer h1102 h) hy
    apply hZ
    rw [hdg x k (lOf_le_L k.2) (hX k.2) (by rw [← hyx, autOnHom'_coe])]
    have hkz : (k : G) * z = z * k :=
      Subgroup.mem_centralizer_iff.mp hz.2 k (pCoreOf_lOf_le_ROf h hU hk)
    have : (k : G) * z * (k : G)⁻¹ * z⁻¹ = 1 := by
      rw [hkz]
      group
    rw [this]
    exact (bb_zero 1 (Subgroup.one_mem _)).mpr (Subgroup.one_mem _)
  obtain ⟨u, huU, hu⟩ := hRC d hcoc hvan
  rw [Subgroup.mem_subgroupOf] at huU
  refine ⟨u, huU, mem_centralizer_of_perfect h.fsu.faithful.1.2.1.2.1 (blockZ_comm hS)
    blockZ_commute_L fun l hl => ?_⟩
  have hlV := L_le_normalizer_fsuV h hl
  have hg := hu ⟨conjV (fsuV T I) l hlV, conjV_mem_autOn hl hlV⟩
  rw [Subgroup.mem_subgroupOf] at hg
  have huL : l * (u : G) * l⁻¹ ∈ fsuV T I :=
    (Subgroup.mem_normalizer_iff.mp hlV u).mp u.2
  have hgu : ((conjV (fsuV T I) l hlV u : ↥(fsuV T I)) : G) = l * u * l⁻¹ := conjV_apply_coe _ _ _
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgu] at hg
  have hdl := hdg ⟨conjV (fsuV T I) l hlV, conjV_mem_autOn hl hlV⟩ l hl hlV rfl
  have hmemU : ∀ {x : G}, x ∈ fsuV T I → x ∈ blockU L := fun hx => hVU hx
  have hgU : (d ⟨conjV (fsuV T I) l hlV, conjV_mem_autOn hl hlV⟩ : G) *
      (l * (u : G) * l⁻¹ * (u : G)⁻¹)⁻¹ ∈ blockU L :=
    Subgroup.mul_mem _ (hmemU (d _).2) (Subgroup.inv_mem _
      (Subgroup.mul_mem _ (hmemU huL) (Subgroup.inv_mem _ (hmemU u.2))))
  have hg0 := (bb_zero _ hgU).mpr ⟨hgU, hg⟩
  rw [bb_mul _ (hmemU (d _).2) _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hmemU huL)
      (Subgroup.inv_mem _ (hmemU u.2)))), bb_inv _ (Subgroup.mul_mem _ (hmemU huL)
      (Subgroup.inv_mem _ (hmemU u.2))), bb_mul _ (hmemU huL) _ (Subgroup.inv_mem _
      (hmemU u.2)), bb_inv _ (hmemU u.2), hdl] at hg0
  have he : l * ((u : G)⁻¹ * z) * l⁻¹ * ((u : G)⁻¹ * z)⁻¹ =
      (l * (u : G) * l⁻¹)⁻¹ * (l * z * l⁻¹ * z⁻¹) * u := by group
  have hmem : l * ((u : G)⁻¹ * z) * l⁻¹ * ((u : G)⁻¹ * z)⁻¹ ∈ blockU L := by
    rw [he]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hmemU huL)) (hzc l hl))
      (hmemU u.2)
  refine (bb_zero _ hmem).mp ?_
  rw [he, bb_mul _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hmemU huL)) (hzc l hl)) _
      (hmemU u.2), bb_mul _ (Subgroup.inv_mem _ (hmemU huL)) _ (hzc l hl),
    bb_inv _ (hmemU huL)]
  linear_combination (exp := 1) hg0

end CFSG.Quasithin.Vol2.Ch11.SecA

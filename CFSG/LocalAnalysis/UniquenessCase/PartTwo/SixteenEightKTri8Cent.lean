module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTri8Perm
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V} {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁] [Finite K₂]
  {I₁ I₂ : Subgroup (Vtil V₀ V hV)}
  {π₁ : ↥(StatedOmega (StatedQuadPlus 4 K₁)) →* ↥(lBar V₀ V hV L)}
  {π₂ : ↥(StatedOmega (StatedQuadPlus 4 K₂)) →* ↥(lBar V₀ V hV L)}


section CentNatSection

variable {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {K : Type} [Field K] [Finite K]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
  {X : Subgroup (MulAut W)} {U Z : Subgroup W} {π : ↥Γ →* ↥X}

private theorem s16k_cent_fixes_nat_section (hK : Nat.card K = 2)
    (hscal : CFSG.RankThree.GF2n.Stroth80.AddCommutantScalar Γ)
    (hR : (FFModel.nat Γ).RealizesVia X U Z π)
    {c : MulAut W} (hc : c ∈ Subgroup.centralizer (X : Set (MulAut W)))
    (hcU : U.map c.toMonoidHom = U) (hcZ : Z.map c.toMonoidHom = Z) :
    ∀ u ∈ U, c u * u⁻¹ ∈ Z := by
  classical
  obtain ⟨hsurj, hUinv, -, hβ⟩ := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hR
  obtain ⟨β, hβs, hβk, hβe⟩ := hβ
  have hcU_mem : ∀ u ∈ U, c u ∈ U := by
    intro u hu
    rw [← hcU]
    exact Subgroup.mem_map_of_mem c.toMonoidHom hu
  have hcZmem : ∀ z : W, c z ∈ Z ↔ z ∈ Z := by
    intro z
    have h := (Subgroup.mem_map_equiv (f := c) (K := Z) (x := c z))
    rw [hcZ] at h
    simpa using h
  let cU : ↥U →* ↥U :=
    { toFun := fun u => ⟨c u, hcU_mem u u.2⟩
      map_one' := Subtype.ext (map_one c)
      map_mul' := fun u v => Subtype.ext (map_mul c (u : W) (v : W)) }
  have hker_cU : ∀ x ∈ β.ker, cU x ∈ β.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (hβk (cU x)).mpr ((hcZmem (x : W)).mpr ((hβk x).mp hx))
  let e := QuotientGroup.quotientKerEquivOfSurjective β hβs
  let m : ↥U ⧸ β.ker →* ↥U ⧸ β.ker := QuotientGroup.map β.ker β.ker cU hker_cU
  let g : Multiplicative (ι → K) →* Multiplicative (ι → K) :=
    (QuotientGroup.kerLift β).comp (m.comp e.symm.toMonoidHom)
  have he_mk : ∀ u : ↥U, e (QuotientGroup.mk u) = β u := by
    intro u
    exact QuotientGroup.kerLift_mk β u
  have hg_apply : ∀ u : ↥U, g (β u) = β (cU u) := by
    intro u
    have hsymm : e.symm (β u) = QuotientGroup.mk u := by
      rw [← he_mk u]
      exact MulEquiv.symm_apply_apply e (QuotientGroup.mk u)
    have hmk : m (QuotientGroup.mk u) = QuotientGroup.mk (cU u) :=
      QuotientGroup.map_mk β.ker β.ker cU hker_cU u
    calc g (β u) = (QuotientGroup.kerLift β) (m (e.symm (β u))) := rfl
      _ = (QuotientGroup.kerLift β) (m (QuotientGroup.mk u)) := by rw [hsymm]
      _ = (QuotientGroup.kerLift β) (QuotientGroup.mk (cU u)) := by rw [hmk]
      _ = β (cU u) := QuotientGroup.kerLift_mk β (cU u)
  have hg_nat : ∀ (γ : ↥Γ) (x : Multiplicative (ι → K)),
      g (natAct Γ γ x) = natAct Γ γ (g x) := by
    intro γ x
    obtain ⟨u, rfl⟩ := hβs x
    have hu : ((π γ : ↥X) : MulAut W) (u : W) ∈ U := hUinv (π γ) (u : W) u.2
    have hcu : ((π γ : ↥X) : MulAut W) ((cU u : ↥U) : W) ∈ U := hUinv (π γ) _ (cU u).2
    rw [← hβe γ u hu, hg_apply, hg_apply, ← hβe γ (cU u) hcu]
    congr 1
    apply Subtype.ext
    show c (((π γ : ↥X) : MulAut W) (u : W)) =
      ((π γ : ↥X) : MulAut W) (c (u : W))
    exact (congrArg (fun mm : MulAut W => mm (u : W))
      ((Subgroup.mem_centralizer_iff.1 hc) (π γ) (π γ).2)).symm
  let f : (ι → K) →+ (ι → K) :=
    { toFun := fun v => (g (Multiplicative.ofAdd v)).toAdd
      map_zero' := by simp
      map_add' := fun v w => by
        show (g (Multiplicative.ofAdd (v + w))).toAdd =
          (g (Multiplicative.ofAdd v)).toAdd + (g (Multiplicative.ofAdd w)).toAdd
        rw [ofAdd_add, map_mul, toAdd_mul] }
  have hf_comm : ∀ A ∈ Γ, ∀ v : ι → K,
      f ((A : Matrix ι ι K) *ᵥ v) = (A : Matrix ι ι K) *ᵥ f v := by
    intro A hA v
    have h := hg_nat ⟨A, hA⟩ (Multiplicative.ofAdd v)
    have h' := congrArg Multiplicative.toAdd h
    simpa [f, natAct] using h'
  obtain ⟨a, ha⟩ := hscal f hf_comm
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hsingle : (Pi.single i (1 : K) : ι → K) ≠ 0 := by
    intro h0
    have := congrFun h0 i
    simp at this
  obtain ⟨u₀, hu₀⟩ := hβs (Multiplicative.ofAdd (Pi.single i (1 : K)))
  have hu₀nz : (u₀ : W) ∉ Z := by
    intro hZ
    have h1 : Multiplicative.ofAdd (Pi.single i (1 : K)) =
        (1 : Multiplicative (ι → K)) := by
      rw [← hu₀, (hβk u₀).mpr hZ]
    exact hsingle ((ofAdd_eq_one).mp h1)
  have hcu₀nz : (cU u₀ : W) ∉ Z := by
    intro hZ
    exact hu₀nz ((hcZmem (u₀ : W)).mp hZ)
  have hg_u₀ : g (β u₀) ≠ 1 := by
    rw [hg_apply]
    intro h1
    exact hcu₀nz ((hβk (cU u₀)).mp h1)
  have ha_ne : a ≠ 0 := by
    intro ha0
    have h2 : Multiplicative.toAdd (g (β u₀)) = 0 := by
      have hv : f (Multiplicative.toAdd (β u₀)) = 0 := by
        rw [ha, ha0]
        simp
      simpa [f] using hv
    have h3 : g (β u₀) = 1 := by
      have := congrArg Multiplicative.ofAdd h2
      simpa using this
    exact hg_u₀ h3
  have ha1 : a = 1 := by
    haveI : Fintype K := Fintype.ofFinite K
    have hcardK : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
    haveI : Subsingleton Kˣ := Fintype.card_le_one_iff_subsingleton.1
      (by rw [Fintype.card_units, hcardK])
    have h1 : (Units.mk0 a ha_ne : Kˣ) = 1 := Subsingleton.elim _ _
    simpa using congrArg (fun u : Kˣ => (u : K)) h1
  intro u hu
  have hv : f (Multiplicative.toAdd (β ⟨u, hu⟩)) =
      Multiplicative.toAdd (β ⟨u, hu⟩) := by
    rw [ha, ha1, one_smul]
  have h2 : Multiplicative.toAdd (g (β ⟨u, hu⟩)) =
      Multiplicative.toAdd (β ⟨u, hu⟩) := by
    simpa [f] using hv
  have h3 : g (β ⟨u, hu⟩) = β ⟨u, hu⟩ := by
    have := congrArg Multiplicative.ofAdd h2
    simpa using this
  rw [hg_apply] at h3
  have h4 : β (cU ⟨u, hu⟩ * ⟨u, hu⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, h3, mul_inv_cancel]
  have h5 : ((cU ⟨u, hu⟩ * ⟨u, hu⟩⁻¹ : ↥U) : W) ∈ Z := (hβk _).mp h4
  simpa [cU] using h5

end CentNatSection


private theorem s16k_mem_fixV_map_iff (h : S16gRowCtx D V₀ V L hV)
    {c : MulAut (Vtil V₀ V hV)} (hcL : ∀ l ∈ lBar V₀ V hV L, c * l = l * c)
    (z : Vtil V₀ V hV) :
    c z ∈ fixV (lBar V₀ V hV L) ↔ z ∈ fixV (lBar V₀ V hV L) := by
  constructor
  · intro hz
    rw [mem_fixV] at hz ⊢
    intro l hl
    have h1 : c ((l : MulAut (Vtil V₀ V hV)) z) =
        (l : MulAut (Vtil V₀ V hV)) (c z) := by
      have := congrArg (fun mm : MulAut (Vtil V₀ V hV) => mm z) (hcL l hl)
      simpa using this
    have h2 : c ((l : MulAut (Vtil V₀ V hV)) z) = c z := by rw [h1, hz l hl]
    exact c.injective h2
  · intro hz
    rw [mem_fixV] at hz ⊢
    intro l hl
    have h1 : c ((l : MulAut (Vtil V₀ V hV)) z) =
        (l : MulAut (Vtil V₀ V hV)) (c z) := by
      have := congrArg (fun mm : MulAut (Vtil V₀ V hV) => mm z) (hcL l hl)
      simpa using this
    rw [← h1, hz l hl]

private theorem s16k_equivVia_of_swap (h : S16gRowCtx D V₀ V L hV)
    (hc : S16kTri8Cfg D V₀ V L hV I₁ I₂ π₁ π₂) {c : MulAut (Vtil V₀ V hV)}
    (hcL : ∀ l ∈ lBar V₀ V hV L, c * l = l * c)
    (hI₁ : I₁.map c.toMonoidHom = I₂) :
    S16kModelsEquivVia (FFModel.nat (StatedOmega (StatedQuadPlus 4 K₁)))
      (FFModel.nat (StatedOmega (StatedQuadPlus 4 K₁))).act
      (FFModel.nat (StatedOmega (StatedQuadPlus 4 K₂))) π₁ π₂ := by
  classical
  obtain ⟨-, hUinv₁, -, hβ₁⟩ := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hc.real₁
  obtain ⟨β₁, hβ₁s, hβ₁k, hβ₁e⟩ := hβ₁
  obtain ⟨-, hUinv₂, -, hβ₂⟩ := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hc.real₂
  obtain ⟨β₂, hβ₂s, hβ₂k, hβ₂e⟩ := hβ₂
  let Z := fixV (lBar V₀ V hV L)
  have hZiff : ∀ z : Vtil V₀ V hV, c z ∈ Z ↔ z ∈ Z := s16k_mem_fixV_map_iff h hcL
  let cI : ↥I₁ ≃* ↥I₂ := (c.subgroupMap I₁).trans (MulEquiv.subgroupCongr hI₁)
  have hker₁ : β₁.ker = Z.subgroupOf I₁ := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβ₁k u
  have hker₂ : β₂.ker = Z.subgroupOf I₂ := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβ₂k u
  have hcI_symm_coe : ∀ x : ↥I₂, (cI.symm x : Vtil V₀ V hV) = c.symm x := by
    intro x
    rfl
  have hkerI : (Z.subgroupOf I₁).map cI.toMonoidHom = Z.subgroupOf I₂ := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rw [hcI_symm_coe x]
    simpa using (hZiff (c.symm (x : Vtil V₀ V hV))).symm
  have hkerI' : β₁.ker.map (cI : ↥I₁ →* ↥I₂) = β₂.ker := by
    rw [hker₁, hker₂]
    exact hkerI
  let q : ↥I₁ ⧸ β₁.ker ≃* ↥I₂ ⧸ β₂.ker :=
    QuotientGroup.congr β₁.ker β₂.ker cI hkerI'
  let e₁ := QuotientGroup.quotientKerEquivOfSurjective β₁ hβ₁s
  let e₂ := QuotientGroup.quotientKerEquivOfSurjective β₂ hβ₂s
  let A : Multiplicative (Fin 4 ⊕ Fin 4 → K₁) ≃* Multiplicative (Fin 4 ⊕ Fin 4 → K₂) :=
    (e₁.symm.trans q).trans e₂
  have hA : ∀ u : ↥I₁, A (β₁ u) = β₂ (cI u) := by
    intro u
    have he₁ : e₁ (QuotientGroup.mk u) = β₁ u := QuotientGroup.kerLift_mk β₁ u
    have hsymm : e₁.symm (β₁ u) = QuotientGroup.mk u := by
      rw [← he₁]
      exact MulEquiv.symm_apply_apply e₁ (QuotientGroup.mk u)
    have hmk : q (QuotientGroup.mk u) = QuotientGroup.mk (cI u) := by
      simpa [q] using
        (QuotientGroup.congr_mk (G' := β₁.ker) (H' := β₂.ker) cI hkerI' u)
    calc A (β₁ u) = e₂ (q (e₁.symm (β₁ u))) := rfl
      _ = e₂ (q (QuotientGroup.mk u)) := by rw [hsymm]
      _ = e₂ (QuotientGroup.mk (cI u)) := by rw [hmk]
      _ = β₂ (cI u) := QuotientGroup.kerLift_mk β₂ (cI u)
  refine ⟨A, ?_, ?_, ?_⟩
  · intro m
    exact iff_of_true (Subgroup.mem_top m) (Subgroup.mem_top (A m))
  · intro m
    exact (Subgroup.mem_bot).trans
      ((MulEquiv.map_eq_one_iff A).symm.trans (Subgroup.mem_bot).symm)
  · intro γ₁ γ₂ hπ m
    obtain ⟨u, rfl⟩ := hβ₁s m
    show A (natAct (StatedOmega (StatedQuadPlus 4 K₁)) γ₁ (β₁ u)) =
      natAct (StatedOmega (StatedQuadPlus 4 K₂)) γ₂ (A (β₁ u))
    rw [← hβ₁e γ₁ u (hUinv₁ (π₁ γ₁) u u.2), hA, hA,
      ← hβ₂e γ₂ (cI u) (hUinv₂ (π₂ γ₂) (cI u) (cI u).2)]
    apply congrArg β₂
    apply Subtype.ext
    change c (((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
        (u : Vtil V₀ V hV)) =
      ((π₂ γ₂ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
        (c (u : Vtil V₀ V hV))
    have hcomm : c (((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
        (u : Vtil V₀ V hV)) =
        ((π₁ γ₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV))
          (c (u : Vtil V₀ V hV)) :=
      congrArg (fun mm : MulAut (Vtil V₀ V hV) => mm (u : Vtil V₀ V hV))
        (hcL (π₁ γ₁) (π₁ γ₁).2)
    rw [hcomm]
    exact congrArg (fun mm : MulAut (Vtil V₀ V hV) => mm (c (u : Vtil V₀ V hV)))
      (congrArg Subtype.val hπ)


theorem s16k_tri8_cent_eq_one (h : S16gRowCtx D V₀ V L hV)
    (hc : S16kTri8Cfg D V₀ V L hV I₁ I₂ π₁ π₂) {c : MulAut (Vtil V₀ V hV)}
    (hcM : c ∈ Mbar D.M V₀ V hV) (hcL : ∀ l ∈ lBar V₀ V hV L, c * l = l * c) :
    c = 1 := by
  let Z := fixV (lBar V₀ V hV L)
  have hcC : c ∈ Subgroup.centralizer
      (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    Subgroup.mem_centralizer_iff.2 fun l hl => (hcL l hl).symm
  have hcZ : Z.map c.toMonoidHom = Z := by
    apply le_antisymm
    · rintro z ⟨w, hw, rfl⟩
      exact (s16k_mem_fixV_map_iff h hcL w).2 hw
    · intro z hz
      have hw : c.symm z ∈ Z := (s16k_mem_fixV_map_iff h hcL (c.symm z)).1 (by simpa using hz)
      have hmap := Subgroup.mem_map_of_mem c.toMonoidHom hw
      simpa using hmap
  rcases s16k_tri8_perm h hc hcM with ⟨hI₁, hI₂⟩ | ⟨hI₁, hI₂⟩
  · have hfix₁ : ∀ u ∈ I₁, c u * u⁻¹ ∈ Z :=
      s16k_cent_fixes_nat_section (K := K₁) hc.card₁
        (CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedOmegaPlus (m := 4)
          (by norm_num))
        hc.real₁ hcC hI₁ hcZ
    have hfix₂ : ∀ u ∈ I₂, c u * u⁻¹ ∈ Z :=
      s16k_cent_fixes_nat_section (K := K₂) hc.card₂
        (CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedOmegaPlus (m := 4)
          (by norm_num))
        hc.real₂ hcC hI₂ hcZ
    have hfmem : ∀ v : Vtil V₀ V hV, c v * v⁻¹ ∈ Z := by
      intro v
      have hmem : v ∈ fixV (lBar V₀ V hV L) ⊔ (I₁ ⊔ I₂) := by
        rw [hc.sup]
        exact Subgroup.mem_top v
      obtain ⟨z, w, hzw⟩ := (Subgroup.mem_sup').1 hmem
      obtain ⟨u₁, u₂, hu₁₂⟩ := (Subgroup.mem_sup').1 w.2
      have hv : v = (z : Vtil V₀ V hV) *
          ((u₁ : Vtil V₀ V hV) * (u₂ : Vtil V₀ V hV)) := by
        rw [← hzw, ← hu₁₂]
      have hz : c (z : Vtil V₀ V hV) * (z : Vtil V₀ V hV)⁻¹ ∈ Z :=
        Z.mul_mem ((s16k_mem_fixV_map_iff h hcL (z : Vtil V₀ V hV)).2 z.2)
          (Z.inv_mem z.2)
      have h1 : c (u₁ : Vtil V₀ V hV) * (u₁ : Vtil V₀ V hV)⁻¹ ∈ Z := hfix₁ _ u₁.2
      have h2 : c (u₂ : Vtil V₀ V hV) * (u₂ : Vtil V₀ V hV)⁻¹ ∈ Z := hfix₂ _ u₂.2
      have heq : c v * v⁻¹ =
          (c (z : Vtil V₀ V hV) * (z : Vtil V₀ V hV)⁻¹) *
            (c (u₁ : Vtil V₀ V hV) * (u₁ : Vtil V₀ V hV)⁻¹) *
              (c (u₂ : Vtil V₀ V hV) * (u₂ : Vtil V₀ V hV)⁻¹) := by
        rw [hv, map_mul, map_mul, mul_inv_rev, mul_inv_rev]
        ac_rfl
      rw [heq]
      exact Z.mul_mem (Z.mul_mem hz h1) h2
    let f : Vtil V₀ V hV →* ↥Z :=
      { toFun := fun v => ⟨c v * v⁻¹, hfmem v⟩
        map_one' := by
          apply Subtype.ext
          show c 1 * 1⁻¹ = (1 : Vtil V₀ V hV)
          rw [map_one, inv_one, mul_one]
        map_mul' := fun v w => by
          apply Subtype.ext
          show c (v * w) * (v * w)⁻¹ = (c v * v⁻¹) * (c w * w⁻¹)
          rw [map_mul, mul_inv_rev]
          ac_rfl }
    have hf_comm : ∀ l : ↥(lBar V₀ V hV L), ∀ v : Vtil V₀ V hV,
        f ((l : MulAut (Vtil V₀ V hV)) v) = f v := by
      intro l v
      apply Subtype.ext
      show c ((l : MulAut (Vtil V₀ V hV)) v) * ((l : MulAut (Vtil V₀ V hV)) v)⁻¹ =
        c v * v⁻¹
      have h1 : c ((l : MulAut (Vtil V₀ V hV)) v) =
          (l : MulAut (Vtil V₀ V hV)) (c v) := by
        have := congrArg (fun mm : MulAut (Vtil V₀ V hV) => mm v) (hcL l l.2)
        simpa using this
      have h2 : ((l : MulAut (Vtil V₀ V hV)) v)⁻¹ =
          (l : MulAut (Vtil V₀ V hV)) v⁻¹ :=
        (map_inv (l : MulAut (Vtil V₀ V hV)) v).symm
      rw [h1, h2, ← map_mul]
      exact (mem_fixV.1 (hfmem v)) (l : MulAut (Vtil V₀ V hV)) l.2
    have hf_one : f = 1 := by
      have hker : commSub ⊤ (lBar V₀ V hV L) ≤ f.ker := by
        rw [commSub, Subgroup.closure_le]
        rintro x ⟨l, hl, w, -, rfl⟩
        change f (((l : MulAut (Vtil V₀ V hV)) w) * w⁻¹) = 1
        rw [map_mul, map_inv, hf_comm ⟨l, hl⟩ w, mul_inv_cancel]
      rw [h.comm_top] at hker
      refine MonoidHom.ext fun v => ?_
      have : v ∈ f.ker := hker (Subgroup.mem_top v)
      exact MonoidHom.mem_ker.mp this
    refine MulEquiv.ext fun v => ?_
    have h1 : f v = 1 := by rw [hf_one]; rfl
    have h2 : c v * v⁻¹ = 1 := by
      have := congrArg (fun x : ↥Z => (x : Vtil V₀ V hV)) h1
      simpa [f] using this
    exact mul_inv_eq_one.mp h2
  · exact absurd (s16k_equivVia_of_swap h hc hcL hI₁) hc.ne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

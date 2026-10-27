module

public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelCentral

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

private theorem m4_fixedSub_iff_rootLine {ρ : Representation (ZMod 2) SL(2, F) W}
    {φ : W ≃+ (Fin 2 → F)}
    (hφ : ∀ g w, φ (ρ g w) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (φ w))
    {A : Subgroup SL(2, F)} {x : SL(2, F)}
    (hx : ∀ g, g ∈ A ↔ x⁻¹ * g * x ∈ (upperSylow (F := F) : Subgroup (SL(2, F)))) (w : W) :
    w ∈ fixedSub ρ A ↔ φ w ∈ rootLine x := by
  rw [mem_fixedSub]
  constructor
  · intro hw
    refine mem_rootLine_of_fixed x (φ w) (fun g hg => ?_)
    have h1 : ρ g w = w := hw g ((hx g).mpr hg)
    calc g • (φ w) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (φ w) := smul_eq_mulVec' g _
      _ = φ (ρ g w) := (hφ g w).symm
      _ = φ w := by rw [h1]
  · intro hw g hg
    apply φ.injective
    rw [hφ]
    simpa [smul_eq_mulVec'] using
      fixed_of_conj_mem x g ((hx g).mp hg) (φ w) hw

private theorem m4_conj_normalizer {A : Subgroup SL(2, F)} {x : SL(2, F)}
    (hx : ∀ g, g ∈ A ↔ x⁻¹ * g * x ∈ (upperSylow (F := F) : Subgroup (SL(2, F))))
    {t : SL(2, F)}
    (ht : t ∈ Subgroup.normalizer (upperSylow (F := F) : Set (SL(2, F)))) :
    x * t * x⁻¹ ∈ Subgroup.normalizer (A : Set (SL(2, F))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hconj : x⁻¹ * ((x * t * x⁻¹) * g * (x * t * x⁻¹)⁻¹) * x =
      t * (x⁻¹ * g * x) * t⁻¹ := by group
  constructor
  · intro hg
    have h1 : x⁻¹ * g * x ∈ upperSylow := (hx g).mp hg
    rw [hx ((x * t * x⁻¹) * g * (x * t * x⁻¹)⁻¹), hconj]
    exact (Subgroup.mem_normalizer_iff.mp ht (x⁻¹ * g * x)).mp h1
  · intro hg
    have h1 : x⁻¹ * ((x * t * x⁻¹) * g * (x * t * x⁻¹)⁻¹) * x ∈ upperSylow :=
      (hx ((x * t * x⁻¹) * g * (x * t * x⁻¹)⁻¹)).mp hg
    rw [hconj] at h1
    exact (hx g).mpr ((Subgroup.mem_normalizer_iff.mp ht (x⁻¹ * g * x)).mpr h1)

private theorem m4_tMat_smul_apply_one (c : F) (hc : c ≠ 0) (v : Fin 2 → F) :
    (tMat c hc • v) 1 = c⁻¹ * v 1 := by
  have hv : v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> simp
  rw [hv, smul_eq_mulVec', tMat_coe]
  simp [Matrix.mulVec, Fin.sum_univ_two, hc]

private theorem m4_smul_conj_single (x : SL(2, F)) (a : F) :
    x⁻¹ • (a • (x • (Pi.single 0 1 : Fin 2 → F))) = a • (Pi.single 0 1 : Fin 2 → F) := by
  rw [smul_eq_mulVec', Matrix.mulVec_smul, ← smul_eq_mulVec', inv_smul_smul]

private theorem m4s_line_mem {ρ : Representation (ZMod 2) SL(2, F) W}
    {A : Subgroup SL(2, F)} {x : SL(2, F)} {φ : W ≃+ (Fin 2 → F)}
    {U : Submodule (ZMod 2) W} {ψ : W →+ (Fin 2 → F)}
    (hfix : ∀ w : W, w ∈ fixedSub ρ A ↔ φ w ∈ rootLine x)
    (hlt : fixedSub ρ A < U) (hψ : ∀ w, ψ w = x⁻¹ • φ w) :
    ∀ a : F, a • (Pi.single 0 1 : Fin 2 → F) ∈ U.toAddSubgroup.map ψ := by
  intro a
  have hroot : a • (x • (Pi.single 0 1 : Fin 2 → F)) ∈ rootLine x :=
    Submodule.smul_mem _ a (smul_single_mem_rootLine x)
  have hmem : φ.symm (a • (x • (Pi.single 0 1 : Fin 2 → F))) ∈ fixedSub ρ A :=
    (hfix _).mpr (by simpa using hroot)
  refine AddSubgroup.mem_map.mpr
    ⟨φ.symm (a • (x • (Pi.single 0 1 : Fin 2 → F))), le_of_lt hlt hmem, ?_⟩
  rw [hψ, AddEquiv.apply_symm_apply, m4_smul_conj_single]

private theorem m4s_tMat_mem [Algebra (ZMod 2) F]
    {ρ : Representation (ZMod 2) SL(2, F) W}
    {A : Subgroup SL(2, F)} {x : SL(2, F)} {φ : W ≃+ (Fin 2 → F)}
    {U : Submodule (ZMod 2) W} {ψ : W →+ (Fin 2 → F)}
    (hφ : ∀ g w, φ (ρ g w) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (φ w))
    (hx : ∀ g, g ∈ A ↔ x⁻¹ * g * x ∈ (upperSylow (F := F) : Subgroup (SL(2, F))))
    (hU : ∀ n ∈ Subgroup.normalizer (A : Set (SL(2, F))), ∀ w ∈ U, ρ n w ∈ U)
    (hψ : ∀ w, ψ w = x⁻¹ • φ w) :
    ∀ (c : F) (hc : c ≠ 0), ∀ v ∈ U.toAddSubgroup.map ψ,
      tMat c hc • v ∈ U.toAddSubgroup.map ψ := by
  intro c hc v hv
  obtain ⟨u, hu, huw⟩ := AddSubgroup.mem_map.mp hv
  have ht : tMat c hc ∈ Subgroup.normalizer (upperSylow (F := F) : Set (SL(2, F))) :=
    tMat_mem_normalizer c hc
  have hn : x * tMat c hc * x⁻¹ ∈ Subgroup.normalizer (A : Set (SL(2, F))) :=
    m4_conj_normalizer hx ht
  refine AddSubgroup.mem_map.mpr ⟨ρ (x * tMat c hc * x⁻¹) u, hU _ hn u hu, ?_⟩
  rw [← huw]
  show ψ (ρ (x * tMat c hc * x⁻¹) u) = tMat c hc • ψ u
  rw [hψ, hφ, ← smul_eq_mulVec', hψ]
  change x⁻¹ • ((x * tMat c hc * x⁻¹) • φ u) = tMat c hc • (x⁻¹ • φ u)
  rw [mul_smul, mul_smul, inv_smul_smul]

private theorem m4s_exists_ne_zero {ρ : Representation (ZMod 2) SL(2, F) W}
    {A : Subgroup SL(2, F)} {x : SL(2, F)} {φ : W ≃+ (Fin 2 → F)}
    {U : Submodule (ZMod 2) W} {ψ : W →+ (Fin 2 → F)}
    (hfix : ∀ w : W, w ∈ fixedSub ρ A ↔ φ w ∈ rootLine x)
    (hlt : fixedSub ρ A < U) (hψ : ∀ w, ψ w = x⁻¹ • φ w) :
    ∃ v ∈ U.toAddSubgroup.map ψ, v 1 ≠ 0 := by
  have hne : fixedSub ρ A ≠ U := ne_of_lt hlt
  have hnotle : ¬ U ≤ fixedSub ρ A := fun hle => hne (le_antisymm (le_of_lt hlt) hle)
  obtain ⟨u, huU, hu_not⟩ :=
    Set.not_subset.mp (show ¬ (U : Set W) ⊆ fixedSub ρ A from hnotle)
  refine ⟨ψ u, AddSubgroup.mem_map_of_mem ψ huU, ?_⟩
  intro hv1
  apply hu_not
  change u ∈ fixedSub ρ A
  rw [hfix u]
  have hv : ψ u = (ψ u 0) • (Pi.single 0 1 : Fin 2 → F) := by
    ext i
    fin_cases i <;> simp [hv1]
  have hφu : φ u = x • ψ u := by rw [hψ, smul_inv_smul]
  rw [hφu, hv, smul_eq_mulVec', Matrix.mulVec_smul, ← smul_eq_mulVec']
  exact Submodule.smul_mem _ _ (smul_single_mem_rootLine x)

private theorem m4s_eq_top_of_line_and_tMat {V : AddSubgroup (Fin 2 → F)}
    (hline : ∀ a : F, a • (Pi.single 0 1 : Fin 2 → F) ∈ V)
    (hV : ∀ (c : F) (hc : c ≠ 0), ∀ v ∈ V, tMat c hc • v ∈ V)
    (hne : ∃ v ∈ V, v 1 ≠ 0) : V = ⊤ := by
  obtain ⟨v₀, hv₀U, hv₀⟩ := hne
  rw [AddSubgroup.eq_top_iff']
  intro v
  by_cases hv1 : v 1 = 0
  · have hv : v = (v 0) • (Pi.single 0 1 : Fin 2 → F) := by
      ext i
      fin_cases i <;> simp [hv1]
    rw [hv]
    exact hline _
  · let c : F := v₀ 1 * (v 1)⁻¹
    have hc : c ≠ 0 := mul_ne_zero hv₀ (inv_ne_zero hv1)
    have hcval : c⁻¹ * v₀ 1 = v 1 := by
      have h1 : c⁻¹ = v 1 * (v₀ 1)⁻¹ := by
        rw [show c = v₀ 1 * (v 1)⁻¹ from rfl, mul_inv_rev, inv_inv]
      rw [h1, mul_assoc, inv_mul_cancel₀ hv₀, mul_one]
    have hw : tMat c hc • v₀ ∈ V := hV c hc v₀ hv₀U
    have hw1 : (tMat c hc • v₀) 1 = v 1 := by
      rw [m4_tMat_smul_apply_one c hc v₀, hcval]
    have hsub : tMat c hc • v₀ - ((tMat c hc • v₀) 0) •
        (Pi.single 0 1 : Fin 2 → F) ∈ V :=
      AddSubgroup.sub_mem _ hw (hline _)
    have hdecomp : v = (v 0) • (Pi.single 0 1 : Fin 2 → F) +
        (tMat c hc • v₀ - ((tMat c hc • v₀) 0) • (Pi.single 0 1 : Fin 2 → F)) := by
      ext i
      fin_cases i <;> simp [hw1]
    rw [hdecomp]
    exact AddSubgroup.add_mem _ (hline _) hsub

theorem IsNaturalModule.eq_top_of_normalizer_invariant
    {ρ : Representation (ZMod 2) SL(2, F) W} (hρ : IsNaturalModule ρ)
    {A : Subgroup SL(2, F)} (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = Nat.card F)
    {U : Submodule (ZMod 2) W}
    (hU : ∀ n ∈ Subgroup.normalizer (A : Set (SL(2, F))), ∀ w ∈ U, ρ n w ∈ U)
    (hlt : fixedSub ρ A < U) : U = ⊤ := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨φ, hφ⟩ := hρ
  obtain ⟨x, hx⟩ := eq_conj_rootGroup A hA2 hA
  let ψ : W →+ (Fin 2 → F) :=
    { toFun := fun w => x⁻¹ • φ w
      map_zero' := by simp
      map_add' := fun a b => by rw [φ.map_add, smul_add] }
  let U' : AddSubgroup (Fin 2 → F) := U.toAddSubgroup.map ψ
  have hψ_apply : ∀ w, ψ w = x⁻¹ • φ w := fun _ => rfl
  have hψ_inj : Function.Injective ψ := by
    intro a b h
    apply φ.injective
    have h1 := congrArg (fun v => x • v) h
    simpa [ψ] using h1
  have hfix_iff : ∀ w : W, w ∈ fixedSub ρ A ↔ φ w ∈ rootLine x :=
    fun w => m4_fixedSub_iff_rootLine hφ hx w
  have hline : ∀ a : F, a • (Pi.single 0 1 : Fin 2 → F) ∈ U' :=
    m4s_line_mem hfix_iff hlt hψ_apply
  have hU' : ∀ (c : F) (hc : c ≠ 0), ∀ v ∈ U', tMat c hc • v ∈ U' :=
    m4s_tMat_mem hφ hx hU hψ_apply
  have hstrict : ∃ v ∈ U', v 1 ≠ 0 :=
    m4s_exists_ne_zero hfix_iff hlt hψ_apply
  have htop : U' = ⊤ := m4s_eq_top_of_line_and_tMat hline hU' hstrict
  rw [Submodule.eq_top_iff']
  intro w
  have hmem : ψ w ∈ U' := by rw [htop]; exact AddSubgroup.mem_top (ψ w)
  obtain ⟨u, hu, huw⟩ := AddSubgroup.mem_map.mp hmem
  have huw' : u = w := hψ_inj huw
  rw [← huw']
  exact hu

end CFSG.RankThree.GF2n.Tim81.Sec2

end

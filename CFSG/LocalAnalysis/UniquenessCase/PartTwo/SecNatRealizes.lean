module

public import CFSG.RankThree.FFModules.BinaryTransport
public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt
public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.Quasithin.Background.StabSubBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open scoped Matrix commutatorElement Pointwise

variable {E : Type} [CommGroup E] [Module (ZMod 2) (Additive E)]

theorem mem_span_ofMul_iff_mem_closure (T : Set E) (w : E) :
    Additive.ofMul w ∈ Submodule.span (ZMod 2) (Additive.ofMul '' T) ↔
      w ∈ Subgroup.closure T := by
  have hpre : Additive.ofMul '' T = Additive.toMul ⁻¹' T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨Additive.toMul x, hx, ofMul_toMul x⟩
  have hclosure : (Subgroup.closure T).toAddSubgroup =
      AddSubgroup.closure (Additive.ofMul '' T) := by
    rw [Subgroup.toAddSubgroup_closure, hpre]
  have hspan : (Submodule.span (ZMod 2) (Additive.ofMul '' T)).toAddSubgroup =
      AddSubgroup.closure (Additive.ofMul '' T) := by
    refine le_antisymm ?_ ?_
    · have hle : Submodule.span (ZMod 2) (Additive.ofMul '' T) ≤
          (AddSubgroup.toZModSubmodule (n := 2))
            (AddSubgroup.closure (Additive.ofMul '' T)) := by
        refine Submodule.span_le.2 (fun x hx => ?_)
        exact (AddSubgroup.mem_toZModSubmodule 2).2 (AddSubgroup.subset_closure hx)
      intro x hx
      have hx' : x ∈ (AddSubgroup.toZModSubmodule (n := 2))
          (AddSubgroup.closure (Additive.ofMul '' T)) := hle hx
      exact (AddSubgroup.mem_toZModSubmodule 2).1 hx'
    · exact (AddSubgroup.closure_le _).2 (fun x hx => Submodule.subset_span hx)
  have hmem : ∀ x : Additive E,
      x ∈ Submodule.span (ZMod 2) (Additive.ofMul '' T) ↔
        x ∈ AddSubgroup.closure (Additive.ofMul '' T) := by
    intro x
    rw [← hspan]
    exact Iff.rfl
  rw [hmem (Additive.ofMul w), ← hclosure]
  change Additive.toMul (Additive.ofMul w) ∈ Subgroup.closure T ↔ w ∈ Subgroup.closure T
  rw [toMul_ofMul]

theorem mem_commOn_autRep_comp {Q : Type*} [Group Q] (ι : Q →* MulAut E) (B : Subgroup Q)
    (w : E) :
    Additive.ofMul w ∈ commOn ((autRep E).comp ι) B ⊤ ↔
      w ∈ commSub (⊤ : Subgroup E) (B.map ι) := by
  have hgen : {v : Additive E | ∃ a ∈ B, ∃ u ∈ (⊤ : Submodule (ZMod 2) (Additive E)),
      v = ((autRep E).comp ι) a u - u} =
      Additive.ofMul '' {c : E | ∃ x ∈ B.map ι, ∃ u ∈ (⊤ : Subgroup E), x u * u⁻¹ = c} := by
    ext v
    constructor
    · rintro ⟨a, ha, u, -, rfl⟩
      refine ⟨Additive.toMul (((autRep E).comp ι) a u - u), ⟨ι a,
        Subgroup.mem_map_of_mem _ ha, Additive.toMul u, Subgroup.mem_top _, ?_⟩,
        ofMul_toMul _⟩
      have h1 : ((autRep E).comp ι) a u =
          Additive.ofMul ((ι a) (Additive.toMul u)) := rfl
      rw [h1, toMul_sub, toMul_ofMul, div_eq_mul_inv]
    · rintro ⟨c, ⟨x, hx, u, -, rfl⟩, rfl⟩
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
      refine ⟨a, ha, Additive.ofMul u, Submodule.mem_top, ?_⟩
      have h1 : ((autRep E).comp ι) a (Additive.ofMul u) =
          Additive.ofMul ((ι a) (Additive.toMul (Additive.ofMul u))) := rfl
      rw [h1, toMul_ofMul, ofMul_mul, ofMul_inv, sub_eq_add_neg]
  rw [commOn, commSub, hgen, mem_span_ofMul_iff_mem_closure]

theorem natL2_realizes_autSub_commSub {Q : Type} [Group Q] (ι : Q →* MulAut E)
    {L : Subgroup Q} {n : ℕ}
    (hnat : CFSG.LocalAnalysis.UniquenessCase.UC22.Ext.NatL2 ((autRep E).comp ι) L
      (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.commOn ((autRep E).comp ι) L ⊤)
      (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.commOn ((autRep E).comp ι) L ⊤ ⊓
        CFSG.RankThree.FFModules.fixSub ((autRep E).comp ι) L) n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      (FFModel.nat (StatedSL 2 F)).Realizes
        (CFSG.Quasithin.autSub (L.map ι) (commSub (⊤ : Subgroup E) (L.map ι))) ⊤
        (CFSG.Quasithin.fixV (CFSG.Quasithin.autSub (L.map ι)
          (commSub (⊤ : Subgroup E) (L.map ι)))) := by
  classical
  obtain ⟨F, hFf, hFfin, hFcard, hAinv, hBinv, hBA, φ, ψ, hψ0, hψker, hψsurj, hψeq⟩ := hnat
  letI : Field F := hFf
  have : Finite F := hFfin
  let ρ : Representation (ZMod 2) Q (Additive E) := (autRep E).comp ι
  let H : Subgroup (MulAut E) := L.map ι
  let U : Subgroup E := commSub (⊤ : Subgroup E) H
  have hst : H ≤ CFSG.Quasithin.stabSub U := by
    intro g hg
    exact StabLat.mem_stabSub_commSub
      (mem_stabSub.mpr fun _ => iff_of_true (Subgroup.mem_top _) (Subgroup.mem_top _))
      (Subgroup.le_normalizer hg)
  have hUmem : ∀ w : E, Additive.ofMul w ∈ commOn ρ L ⊤ ↔ w ∈ U := by
    intro w
    exact mem_commOn_autRep_comp ι L w
  have hfixmem : ∀ w : E, Additive.ofMul w ∈ fixSub ρ L ↔ w ∈ CFSG.Quasithin.fixV H := by
    intro w
    rw [mem_fixSub_autRep_comp ι L (Additive.ofMul w), toMul_ofMul]
  have hZmem : ∀ w : U, Additive.ofMul (w : E) ∈
      (commOn ρ L ⊤ ⊓ fixSub ρ L) ↔ w ∈ CFSG.Quasithin.fixV (CFSG.Quasithin.autSub H U) := by
    intro w
    have hUw : Additive.ofMul (w : E) ∈ commOn ρ L ⊤ := (hUmem (w : E)).2 w.2
    have h1 : Additive.ofMul (w : E) ∈ (commOn ρ L ⊤ ⊓ fixSub ρ L) ↔
        Additive.ofMul (w : E) ∈ fixSub ρ L :=
      ⟨fun h => h.2, fun h => ⟨hUw, h⟩⟩
    rw [h1, hfixmem, CFSG.Quasithin.mem_fixV_autSub]
    constructor
    · intro h g hg _
      exact h g hg
    · intro h g hg
      exact h g hg (hst hg)
  let toAut : L →* ↥(CFSG.Quasithin.autSub H U) :=
    { toFun := fun l =>
        ⟨CFSG.Quasithin.resHom U ⟨ι l, hst (Subgroup.mem_map_of_mem ι l.2)⟩,
          Subgroup.mem_map_of_mem (CFSG.Quasithin.resHom U)
            (Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem ι l.2))⟩
      map_one' := by
        refine Subtype.ext ?_
        ext u
        change (ι ((1 : ↥L) : Q)) ((u : U) : E) = ((u : U) : E)
        rw [show ((1 : ↥L) : Q) = 1 from rfl, map_one ι]
        rfl
      map_mul' := by
        intro a b
        refine Subtype.ext ?_
        ext u
        change (ι (a * b)) ((u : U) : E) = (ι a) ((ι b) ((u : U) : E))
        rw [map_mul]
        rfl }
  have htoAutSurj : Function.Surjective toAut := by
    intro h
    obtain ⟨g, hgH, hgh⟩ := (CFSG.Quasithin.mem_autSub).1 h.2
    obtain ⟨l, hl, hlh⟩ := (Subgroup.mem_map (f := ι)).1 hgH
    refine ⟨⟨l, hl⟩, ?_⟩
    have h1 : (⟨ι (⟨l, hl⟩ : ↥L), hst (Subgroup.mem_map_of_mem ι hl)⟩ :
        CFSG.Quasithin.stabSub U) = g :=
      Subtype.ext hlh
    refine Subtype.ext ?_
    rw [← hgh]
    change CFSG.Quasithin.resHom U ⟨ι (⟨l, hl⟩ : ↥L), hst (Subgroup.mem_map_of_mem ι hl)⟩ =
      CFSG.Quasithin.resHom U g
    rw [h1]
  let π : ↥(StatedSL 2 F) →* ↥(CFSG.Quasithin.autSub H U) := toAut.comp φ.symm.toMonoidHom
  have hπsurj : Function.Surjective π := htoAutSurj.comp φ.symm.surjective
  let f : ↥(⊤ : Subgroup U) →* Multiplicative (Fin 2 → F) :=
    { toFun := fun u => Multiplicative.ofAdd (ψ (Additive.ofMul (((u : U) : E))))
      map_one' := by simp
      map_mul' := by
        intro u v
        change Multiplicative.ofAdd (ψ (Additive.ofMul (((u : U) : E) * ((v : U) : E)))) =
          Multiplicative.ofAdd (ψ (Additive.ofMul ((u : U) : E))) *
            Multiplicative.ofAdd (ψ (Additive.ofMul ((v : U) : E)))
        rw [ofMul_mul, map_add, ofAdd_add] }
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x, hxA, hx⟩ := hψsurj (Multiplicative.toAdd y)
    have hxU : Additive.toMul x ∈ U := by
      rw [← hUmem (Additive.toMul x), ofMul_toMul]
      exact hxA
    refine ⟨⟨⟨Additive.toMul x, hxU⟩, Subgroup.mem_top _⟩, ?_⟩
    change Multiplicative.ofAdd (ψ (Additive.ofMul (Additive.toMul x))) = y
    rw [ofMul_toMul, hx, ofAdd_toAdd]
  have hfk : ∀ u : ↥(⊤ : Subgroup U),
      f u = 1 ↔ ((u : U) ∈ CFSG.Quasithin.fixV (CFSG.Quasithin.autSub H U)) := by
    intro u
    have hmemA : Additive.ofMul ((u : U) : E) ∈ commOn ρ L ⊤ := (hUmem _).2 u.1.2
    have h1 : f u = 1 ↔ ψ (Additive.ofMul ((u : U) : E)) = 0 := by
      constructor
      · intro h
        exact ofAdd_eq_one.1 h
      · intro h
        change Multiplicative.ofAdd (ψ (Additive.ofMul ((u : U) : E))) = 1
        rw [h, ofAdd_zero]
    rw [h1]
    have h2 : ψ (Additive.ofMul ((u : U) : E)) = 0 ↔
        Additive.ofMul ((u : U) : E) ∈ commOn ρ L ⊤ ⊓ fixSub ρ L :=
      ⟨fun h => hψker _ hmemA h, fun h => hψ0 _ h⟩
    rw [h2, hZmem]
  have hfe : ∀ (γ : ↥(StatedSL 2 F)) (u : ↥(⊤ : Subgroup U))
      (hu : ((π γ : ↥(CFSG.Quasithin.autSub H U)) : MulAut U) (u : U) ∈ (⊤ : Subgroup U)),
      f ⟨((π γ : ↥(CFSG.Quasithin.autSub H U)) : MulAut U) (u : U), hu⟩ =
        natAct (StatedSL 2 F) γ (f u) := by
    intro γ u hu
    have hact : (((((π γ : ↥(CFSG.Quasithin.autSub H U)) : MulAut U) (u : U)) : U) : E) =
        (ι (φ.symm γ)) ((u : U) : E) := rfl
    have hmemA : Additive.ofMul ((u : U) : E) ∈ commOn ρ L ⊤ := (hUmem _).2 u.1.2
    have hψapp := hψeq (φ.symm γ) (Additive.ofMul ((u : U) : E)) hmemA
    have hφ : φ (φ.symm γ) = γ := φ.apply_symm_apply γ
    have hLHS : f ⟨((π γ : ↥(CFSG.Quasithin.autSub H U)) : MulAut U) (u : U), hu⟩ =
        Multiplicative.ofAdd (ψ (Additive.ofMul ((ι (φ.symm γ)) ((u : U) : E)))) := by
      change Multiplicative.ofAdd (ψ (Additive.ofMul
        (((((π γ : ↥(CFSG.Quasithin.autSub H U)) : MulAut U) (u : U)) : U) : E))) = _
      rw [hact]
    rw [hLHS]
    have hRHS : natAct (StatedSL 2 F) γ (f u) =
        Multiplicative.ofAdd ((((γ : ↥(StatedSL 2 F)) : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) *ᵥ ψ (Additive.ofMul ((u : U) : E))) := rfl
    have hsec : ψ (Additive.ofMul ((ι (φ.symm γ)) ((u : U) : E))) =
        ((((φ (φ.symm γ) : ↥(StatedSL 2 F)) : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) *ᵥ ψ (Additive.ofMul ((u : U) : E))) := by
      simpa [ρ, autRep_apply] using hψapp
    rw [hsec, hφ, hRHS]
  exact ⟨F, hFf, hFfin, hFcard,
    ⟨π, G64.realizesVia_nat_of (Γ := StatedSL 2 F) hπsurj le_top
      (fun _ _ _ => Subgroup.mem_top _)
      (fun h z hz => by
        have hz' : (h : MulAut U) z = z := hz h h.2
        rw [hz']
        exact hz)
      f hfs hfk hfe⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

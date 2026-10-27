module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMChain
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarConnGen
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarLinData
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylPath
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleThree

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open NSJoin

abbrev nsBar_Idx {G : Type} [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G)
    (D J : Subgroup G) : Type _ :=
  Option {q : G × Subgroup G // GGNbr p B x D J q.1 q.2}

@[expose] noncomputable def nsBar_AX {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G}
    {x : G} {D J : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {L : Subgroup G} :
    nsBar_Idx p B x D J → Subgroup (V ≃ₗ[ZMod p] V) :=
  fun X => match X with
    | none => (ggAutomizer L Bs).map (ggLin (p := p) ι)
    | some q => (ggAutomizer q.1.2 Bs).map (ggLin (p := p) ι)

@[expose] noncomputable def nsBar_A {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) : Subgroup (V ≃ₗ[ZMod p] V) :=
  (ggAInf p B Bs x L D J).map (ggLin (p := p) ι)

@[expose] noncomputable def nsBar_U {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) : Submodule (ZMod p) V :=
  ggLinCom ((nsBar_A p B Bs x L D J ι : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V))

private lemma nsBar_ggInducedSubgroup_mono {G : Type} [Group G] {H H' : Subgroup G} (Bs : Subgroup G)
    (h : H ≤ H') : ggInducedSubgroup H Bs ≤ ggInducedSubgroup H' Bs := by
  rintro φ ⟨g, hg, hgN, hφ⟩
  exact ⟨g, h hg, hgN, hφ⟩

private lemma nsBar_ggAInf_le_induced {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G) :
    ggAInf p B Bs x L D J ≤ ggInducedSubgroup ⊤ Bs := by
  simp only [ggAInf]
  refine sup_le ?_ ?_
  · rw [ggAutomizer_eq]
    exact nsBar_ggInducedSubgroup_mono Bs le_top
  · refine iSup_le fun y => iSup_le fun K => iSup_le fun _ => ?_
    rw [ggAutomizer_eq]
    exact nsBar_ggInducedSubgroup_mono Bs le_top

theorem nsBar_hfix {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V)
    (hC : ∀ b : ↥Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ b = b) → b = 1) :
    ggLinFix ((nsBar_A p B Bs x L D J ι : Subgroup (V ≃ₗ[ZMod p] V)) :
      Set (V ≃ₗ[ZMod p] V)) = ⊥ := by
  rw [nsBar_A]
  exact ggLinFix_map_eq_bot (p := p) ι (ggAInf p B Bs x L D J) hC

theorem nsBar_hnotr {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) (hNT : GGNoTransvection p Bs)
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ nsBar_A p B Bs x L D J ι) :
    g ≠ 1 → ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}) := by
  intro _ h
  rw [nsBar_A, Subgroup.mem_map] at hg
  obtain ⟨φ, hφ, rfl⟩ := hg
  exact hNT φ (nsBar_ggAInf_le_induced p B Bs x L D J hφ)
    ((ggIsTransvection_iff_ggLin (p := p) ι φ).mpr h)

theorem nsBar_hJr {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {J : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥Bs ≃+ V) (hp2 : p ≠ 2)
    (h : ∃ r ∈ ggAutomizer J Bs, ∃ r' ∈ ggAutomizer J Bs, GGIsReflection p r ∧
      GGIsReflection p r' ∧ orderOf (r * r') = 3) :
    ∃ r ∈ (ggAutomizer J Bs).map (ggLin (p := p) ι), GGLinRefl r := by
  obtain ⟨r, hr, r', hr', hreflr, -, -⟩ := h
  exact ⟨ggLin (p := p) ι r, Subgroup.mem_map_of_mem _ hr,
    (ggIsReflection_iff_ggLinRefl (p := p) hp2 ι r).mp hreflr⟩

private lemma nsBar_mul_comm_of_sq_eq_one {G : Type*} [Group G] {x y : G}
    (hx : x * x = 1) (hy : y * y = 1) (h : (x * y) ^ 2 = 1) : x * y = y * x := by
  have h' : (x * y) * (x * y) = 1 := by simpa [pow_two] using h
  have h2 : y * x = x * y := by
    calc y * x = (x * x) * (y * x) * (y * y) := by rw [hx, hy]; group
      _ = x * ((x * y) * (x * y)) * y := by group
      _ = x * 1 * y := by rw [h']
      _ = x * y := by group
  exact h2.symm

theorem nsBar_three_le_finrank
    {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop} (hBase : NSBaseFrameInputOf T)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg0 : NSRegularCfgOf T p B Bs x L D J 𝒦)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V] (ι : Additive ↥Bs ≃+ V) :
    3 ≤ Module.finrank (ZMod p)
      (ggLinCom (((ggAInf p B Bs x L D J).map (ggLin (p := p) ι) : Subgroup (V ≃ₗ[ZMod p] V)) :
        Set (V ≃ₗ[ZMod p] V))) := by
  have hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦 := ggSecFiveRouteCfg'_of_routeCfg hcfg0.1
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hp2 : p ≠ 2 := hconf.1.2.2.2.2.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨ι', instι', M, hMAD, hW, -, hcard3⟩ := hBase G p B Bs x L D J 𝒦 hcfg0
  have hM : GGIsWeylMatrix M := hMAD.elim (fun h => h.isWeylMatrix) (fun h => h.isWeylMatrix)
  obtain ⟨f, hrefl⟩ := hW
  have hcard : 3 ≤ Nat.card ι' := by
    rw [Nat.card_eq_fintype_card]
    exact hcard3
  obtain ⟨a, v, b, hab_ne, hav, hvb, hab2, hm3⟩ :=
    ggWeylMatrix_exists_path_of_rank M hM hcard
  let F : M.Group →* MulAut ↥Bs := (ggAutomizer L Bs).subtype.comp f.toMonoidHom
  let r₁ : V ≃ₗ[ZMod p] V := ggLin (p := p) ι (F (M.simple a))
  let r₂ : V ≃ₗ[ZMod p] V := ggLin (p := p) ι (F (M.simple v))
  let r₃ : V ≃ₗ[ZMod p] V := ggLin (p := p) ι (F (M.simple b))
  let Ag : Subgroup (V ≃ₗ[ZMod p] V) := (ggAInf p B Bs x L D J).map (ggLin (p := p) ι)
  have hF_inj : Function.Injective F := by
    intro x y h
    exact f.injective (Subtype.ext (by simpa [F] using h))
  have hr1 : GGLinRefl r₁ := by
    show GGLinRefl (ggLin (p := p) ι (F (M.simple a)))
    exact (ggIsReflection_iff_ggLinRefl (p := p) hp2 ι (F (M.simple a))).mp
      (by simpa [F] using hrefl a)
  have hr2 : GGLinRefl r₂ := by
    show GGLinRefl (ggLin (p := p) ι (F (M.simple v)))
    exact (ggIsReflection_iff_ggLinRefl (p := p) hp2 ι (F (M.simple v))).mp
      (by simpa [F] using hrefl v)
  have hr3 : GGLinRefl r₃ := by
    show GGLinRefl (ggLin (p := p) ι (F (M.simple b)))
    exact (ggIsReflection_iff_ggLinRefl (p := p) hp2 ι (F (M.simple b))).mp
      (by simpa [F] using hrefl b)
  have hcomm_simple : M.simple a * M.simple b = M.simple b * M.simple a := by
    refine nsBar_mul_comm_of_sq_eq_one ?_ ?_ ?_
    · simpa [CoxeterMatrix.toCoxeterSystem_simple] using
        (CoxeterSystem.simple_mul_simple_self M.toCoxeterSystem a)
    · simpa [CoxeterMatrix.toCoxeterSystem_simple] using
        (CoxeterSystem.simple_mul_simple_self M.toCoxeterSystem b)
    · have h := CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem a b
      rw [CoxeterMatrix.toCoxeterSystem_simple] at h
      have ho : orderOf (M.simple a * M.simple b) = 2 := h.trans hab2
      rw [← ho]
      exact pow_orderOf_eq_one _
  have h13 : r₁ * r₃ = r₃ * r₁ := by
    have hmul13 : r₁ * r₃ = ggLin (p := p) ι (F (M.simple a * M.simple b)) := by
      show ggLin (p := p) ι (F (M.simple a)) * ggLin (p := p) ι (F (M.simple b)) =
        ggLin (p := p) ι (F (M.simple a * M.simple b))
      rw [← map_mul (ggLin (p := p) ι), ← map_mul F]
    have hmul31 : r₃ * r₁ = ggLin (p := p) ι (F (M.simple b * M.simple a)) := by
      show ggLin (p := p) ι (F (M.simple b)) * ggLin (p := p) ι (F (M.simple a)) =
        ggLin (p := p) ι (F (M.simple b * M.simple a))
      rw [← map_mul (ggLin (p := p) ι), ← map_mul F]
    rw [hmul13, hmul31, hcomm_simple]
  have hsimple_ne : M.simple a ≠ M.simple b := by
    intro h
    exact hab_ne (CoxeterSystem.simple_injective M.toCoxeterSystem
      (by simpa [CoxeterMatrix.toCoxeterSystem_simple] using h))
  have hne : r₁ ≠ r₃ := by
    intro h
    have h' : ggLin (p := p) ι (F (M.simple a)) =
        ggLin (p := p) ι (F (M.simple b)) := h
    exact hsimple_ne (hF_inj ((ggLin_injective (p := p) ι) h'))
  have hmul12 : r₁ * r₂ = ggLin (p := p) ι (F (M.simple a * M.simple v)) := by
    show ggLin (p := p) ι (F (M.simple a)) * ggLin (p := p) ι (F (M.simple v)) =
      ggLin (p := p) ι (F (M.simple a * M.simple v))
    rw [← map_mul (ggLin (p := p) ι), ← map_mul F]
  have hmul23 : r₂ * r₃ = ggLin (p := p) ι (F (M.simple v * M.simple b)) := by
    show ggLin (p := p) ι (F (M.simple v)) * ggLin (p := p) ι (F (M.simple b)) =
      ggLin (p := p) ι (F (M.simple v * M.simple b))
    rw [← map_mul (ggLin (p := p) ι), ← map_mul F]
  have ho1 : orderOf (r₁ * r₂) = M.M a v := by
    rw [hmul12]
    rw [orderOf_injective (ggLin (p := p) ι) (ggLin_injective (p := p) ι)]
    rw [orderOf_injective F hF_inj]
    have h := CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem a v
    rw [CoxeterMatrix.toCoxeterSystem_simple] at h
    exact h
  have ho2 : orderOf (r₂ * r₃) = M.M v b := by
    rw [hmul23]
    rw [orderOf_injective (ggLin (p := p) ι) (ggLin_injective (p := p) ι)]
    rw [orderOf_injective F hF_inj]
    have h := CoxeterSystem.orderOf_simple_mul_simple M.toCoxeterSystem v b
    rw [CoxeterMatrix.toCoxeterSystem_simple] at h
    exact h
  have hAInf_mem : ∀ i : ι', F (M.simple i) ∈ ggAInf p B Bs x L D J := by
    intro i
    rw [ggAInf]
    exact Subgroup.mem_sup_left (f (M.simple i)).2
  have hAg_mem : ∀ i : ι', ggLin (p := p) ι (F (M.simple i)) ∈ Ag := by
    intro i
    exact Subgroup.mem_map_of_mem (ggLin (p := p) ι) (hAInf_mem i)
  have hr1_mem : r₁ ∈ Ag := hAg_mem a
  have hr2_mem : r₂ ∈ Ag := hAg_mem v
  have hr3_mem : r₃ ∈ Ag := hAg_mem b
  have hclos_le : Subgroup.closure ({r₁, r₂, r₃} : Set (V ≃ₗ[ZMod p] V)) ≤ Ag := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hr1_mem
    · exact hr2_mem
    · exact hr3_mem
  have hnotr : ∀ g ∈ Subgroup.closure ({r₁, r₂, r₃} : Set (V ≃ₗ[ZMod p] V)), g ≠ 1 →
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}) := by
    intro g hg hg1
    exact nsBar_hnotr (p := p) ι hNT (by rw [nsBar_A]; exact hclos_le hg) hg1
  have hthree :=
    ggLin_three_indep hp2 r₁ r₂ r₃ hr1 hr2 hr3 h13 hne
      (M.M a v) (M.M v b) hav hvb hm3 ho1 ho2 hnotr
  have hle : ggLinMove r₁ ⊔ ggLinMove r₂ ⊔ ggLinMove r₃ ≤
      ggLinCom (Ag : Set (V ≃ₗ[ZMod p] V)) := by
    rw [ggLinCom]
    refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · exact le_iSup₂_of_le r₁ hr1_mem le_rfl
      · exact le_iSup₂_of_le r₂ hr2_mem le_rfl
    · exact le_iSup₂_of_le r₃ hr3_mem le_rfl
  change 3 ≤ Module.finrank (ZMod p) (ggLinCom (Ag : Set (V ≃ₗ[ZMod p] V)))
  exact le_trans hthree (Submodule.finrank_mono hle)

end CFSG.StandardType

end

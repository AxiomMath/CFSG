module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed

public section

namespace CFSG.StandardType

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)}

omit [Finite G] in
private theorem closure_range_simple_eq {ι : Type} {M : CoxeterMatrix ι}
    {A : Subgroup (MulAut ↥Bs)} {e : M.Group ≃* ↥A} :
    Subgroup.closure (Set.range fun i : ι => ((e (M.simple i) : ↥A) : MulAut ↥Bs)) = A := by
  let f : M.Group →* MulAut ↥Bs := A.subtype.comp e.toMonoidHom
  have hf : f.range = A := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  have hgen : Subgroup.closure (Set.range M.simple) = ⊤ :=
    M.toCoxeterSystem.subgroup_closure_range_simple
  calc Subgroup.closure (Set.range fun i : ι => ((e (M.simple i) : ↥A) : MulAut ↥Bs))
      = Subgroup.closure (f '' Set.range M.simple) := by
        congr 1
        ext φ
        simp [f]
    _ = Subgroup.map f (Subgroup.closure (Set.range M.simple)) := by
        rw [MonoidHom.map_closure]
    _ = f.range := by rw [hgen, Subgroup.map_top]
    _ = A := hf

theorem GGSecFiveRouteCfg.reflGenerated_ggAInf (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) :
    GGReflGenerated p (ggAInf p B Bs x L D J) := by
  have hgen := closure_range_simple_eq (A := ggAutomizerJoin L Bs 𝒦) (M := M) (e := e)
  have hAle : ggAutomizerJoin L Bs 𝒦 ≤
      Subgroup.closure {φ | φ ∈ ggAInf p B Bs x L D J ∧ GGIsReflection p φ} := by
    rw [← hgen]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨i, rfl⟩ := hx
    exact Subgroup.subset_closure
      ⟨GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1 (e (M.simple i)).2, hP.2 i⟩
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr fun φ hφ => hφ.1)
  rw [ggAInf]
  refine sup_le ?_ (iSup_le fun y => iSup_le fun K => iSup_le fun hN => ?_)
  · exact le_sup_left.trans hAle
  · rw [hR.2.1 y K hN]
    exact (Subgroup.closure_le _).mpr fun φ hφ =>
      Subgroup.subset_closure ⟨ggAutomizer_le_ggAInf_of_nbr hN hφ.1, hφ.2⟩

variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem GGSecFiveRouteCfg.reflGen_map_ggAInf [Fact p.Prime] [Finite V]
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp2 : p ≠ 2) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (ιV : Additive ↥Bs ≃+ V) :
    ZS.ReflGen p ((ggAInf p B Bs x L D J).map (ggLin (p := p) ιV)) := by
  unfold ZS.ReflGen
  have h := GGSecFiveRouteCfg.reflGenerated_ggAInf hR hP
  unfold GGReflGenerated at h
  have hset : (ggLin (p := p) ιV ''
      {φ | φ ∈ ggAInf p B Bs x L D J ∧ GGIsReflection p φ}) =
      {t | t ∈ (ggAInf p B Bs x L D J).map (ggLin (p := p) ιV) ∧ ZS.IsRefl p t} := by
    ext t
    constructor
    · rintro ⟨φ, ⟨hφ, hφrefl⟩, rfl⟩
      exact ⟨Subgroup.mem_map_of_mem _ hφ,
        (ggIsReflection_iff_ggLinRefl hp2 ιV φ).mp hφrefl⟩
    · rintro ⟨ht, htrefl⟩
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp ht
      exact ⟨φ, ⟨hφ, (ggIsReflection_iff_ggLinRefl hp2 ιV φ).mpr htrefl⟩, rfl⟩
  have h1 : (ggAInf p B Bs x L D J).map (ggLin (p := p) ιV) =
      Subgroup.closure (ggLin (p := p) ιV ''
        {φ | φ ∈ ggAInf p B Bs x L D J ∧ GGIsReflection p φ}) := by
    conv_lhs => rw [h]
    rw [MonoidHom.map_closure]
  have h2 : Subgroup.closure {t | t ∈ (ggAInf p B Bs x L D J).map (ggLin (p := p) ιV) ∧
        ZS.IsRefl p t} =
      Subgroup.closure (ggLin (p := p) ιV ''
        {φ | φ ∈ ggAInf p B Bs x L D J ∧ GGIsReflection p φ}) := by
    conv_rhs => rw [hset]
  conv_lhs => rw [h1]
  exact h2.symm

theorem GGSecFiveRouteCfg.noTransvection_map_ggAInf [Fact p.Prime] [Finite V]
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (ιV : Additive ↥Bs ≃+ V) :
    ∀ τ ∈ (ggAInf p B Bs x L D J).map (ggLin (p := p) ιV),
      Module.finrank (ZMod p) (LinearMap.range ((τ : V →ₗ[ZMod p] V) - LinearMap.id)) = 1 →
        ∃ v, τ (τ v - v) ≠ τ v - v := by
  intro τ hτ hrank
  obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hτ
  by_contra h
  push Not at h
  refine hR.1.2.2.2.1 φ (ggRM_ainf_le_induced (G := G) hφ) ?_
  refine (ggIsTransvection_iff_ggLin ιV φ).mpr ⟨hrank, ?_⟩
  rintro w ⟨v, hv⟩ a ha
  rw [Set.mem_singleton_iff] at ha
  rw [ha]
  rw [← hv]
  exact h v

omit [Finite G] in
theorem card_map_ggLin [Fact p.Prime] (ιV : Additive ↥Bs ≃+ V) (A : Subgroup (MulAut ↥Bs)) :
    Nat.card (A.map (ggLin (p := p) ιV)) = Nat.card A :=
  Subgroup.card_map_of_injective (ggLin_injective ιV)

end CFSG.StandardType

end

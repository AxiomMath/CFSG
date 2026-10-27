module

public import CFSG.Quasithin.Background.F6GoldschmidtList
public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem nonempty_iso_ofSubgroups_of_isAmalgamIso {D E : Type} [Group D] [Group E]
    {H₁ H₂ : Subgroup D} {K₁ K₂ : Subgroup E} (h : F6.IsAmalgamIso H₁ H₂ K₁ K₂) :
    Nonempty ((RankTwoAmalgam.ofSubgroups H₁ H₂).Iso (RankTwoAmalgam.ofSubgroups K₁ K₂)) := by
  obtain ⟨φ₁, φ₂, hag, hagi⟩ := h
  have hf : ∀ x : ↥(H₁ ⊓ H₂), (φ₁ ⟨x, (Subgroup.mem_inf.1 x.2).1⟩ : E) ∈ K₁ ⊓ K₂ := fun x =>
    Subgroup.mem_inf.2 ⟨(φ₁ _).2, by
      rw [hag x (Subgroup.mem_inf.1 x.2).1 (Subgroup.mem_inf.1 x.2).2]
      exact (φ₂ _).2⟩
  have hg : ∀ y : ↥(K₁ ⊓ K₂), (φ₁.symm ⟨y, (Subgroup.mem_inf.1 y.2).1⟩ : D) ∈ H₁ ⊓ H₂ := fun y =>
    Subgroup.mem_inf.2 ⟨(φ₁.symm _).2, by
      rw [hagi y (Subgroup.mem_inf.1 y.2).1 (Subgroup.mem_inf.1 y.2).2]
      exact (φ₂.symm _).2⟩
  let φ12 : ↥(H₁ ⊓ H₂) ≃* ↥(K₁ ⊓ K₂) :=
    { toFun := fun x => ⟨(φ₁ ⟨x, (Subgroup.mem_inf.1 x.2).1⟩ : E), hf x⟩
      invFun := fun y => ⟨(φ₁.symm ⟨y, (Subgroup.mem_inf.1 y.2).1⟩ : D), hg y⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp
      right_inv := fun y => by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        exact congrArg (fun z : ↥K₁ => (z : E)) (φ₁.map_mul ⟨(x : D), (Subgroup.mem_inf.1 x.2).1⟩
          ⟨(y : D), (Subgroup.mem_inf.1 y.2).1⟩) }
  refine ⟨{ φ1 := φ₁, φ12 := φ12, φ2 := φ₂, comm1 := fun g => rfl, comm2 := ?_ }⟩
  intro g
  change ↥(H₁ ⊓ H₂) at g
  apply Subtype.ext
  exact hag (g : D) (Subgroup.mem_inf.1 g.2).1 (Subgroup.mem_inf.1 g.2).2

theorem isSylowTwoOf_top_of_sylow {W : Type} [Group W] [Finite W] (S : Sylow 2 W) :
    IsSylowTwoOf (S : Subgroup W) ⊤ := by
  refine ⟨le_top, S.isPGroup', ?_⟩
  have e1 : ((S : Subgroup W).subgroupOf ⊤).index = (S : Subgroup W).index :=
    Subgroup.relIndex_top_right _
  rw [e1]
  exact S.not_dvd_index

@[expose] def TwoLocalPairProp (W : Type*) [Group W] : Prop :=
  ∀ S K₁ K₂ : Subgroup W, IsSylowTwoOf S ⊤ → IsMaximalTwoLocal K₁ → IsMaximalTwoLocal K₂ →
    K₁ ≠ K₂ → S ≤ K₁ → S ≤ K₂ → IsYAmalgamPair S K₁ K₂

theorem f6_bridge_of_pair {IsY : ∀ (W : Type) [Group W], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
    (hP : ∀ (W : Type) [Group W] [Finite W], IsY W → P W)
    (hpair : ∀ (W : Type) [Group W] [Finite W], IsY W → TwoLocalPairProp W)
    (D : Type) [Group D] [Finite D] (H₁ H₂ : Subgroup D) (h : F6.IsYAmalgam IsY H₁ H₂) :
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂) P := by
  obtain ⟨W, _, _, K₁, K₂, hW, ⟨hK₁, hK₂, hne, S, hS⟩, hiso⟩ := h
  have hS1 : (S : Subgroup W) ≤ K₁ := by
    rw [hS]
    exact inf_le_left
  have hS2 : (S : Subgroup W) ≤ K₂ := by
    rw [hS]
    exact inf_le_right
  exact ⟨W, inferInstance, hP W hW, (S : Subgroup W), K₁, K₂,
    hpair W hW S K₁ K₂ (isSylowTwoOf_top_of_sylow S) hK₁ hK₂ hne hS1 hS2,
    nonempty_iso_ofSubgroups_of_isAmalgamIso hiso⟩

end CFSG.Quasithin

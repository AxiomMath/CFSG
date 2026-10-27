module

public import CFSG.Quasithin.Background.F3Amalgam
public import CFSG.Quasithin.Background.F1VertexCore
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.Recognition.F112WSetup
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.Quasithin.EmptyFaithful.F112HypW

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F112R

universe u v

section Faithful

variable {α : RankTwoAmalgam.{u}} {Y : Type v} [Group Y]

theorem eq_one_of_forall_smul_eq_of_coreIn (c : α.Completion Y) (hc : c.IsFaithful)
    (hcore : coreIn (c.φ1.range ⊓ c.φ2.range) (c.φ1.range ⊔ c.φ2.range) = ⊥)
    {h : ↥(α.Ghat1 ⊔ α.Ghat2)} (hfix : ∀ w : α.Γhat, h • w = w) : h = 1 := by
  classical
  have hgfix : ∀ w : c.Γ, c.theta0 hc h • w = w := by
    intro w
    obtain ⟨v, rfl⟩ := (c.coverData hc).Θ_surjective w
    calc c.theta0 hc h • c.Θ hc v = c.Θ hc (h • v) := (c.Θ_smul hc h v).symm
      _ = c.Θ hc v := by rw [hfix v]
  have hmem : ((c.theta0 hc h : ↥(c.φ1.range ⊔ c.φ2.range)) : Y) ∈
      coreIn (c.φ1.range ⊓ c.φ2.range) (c.φ1.range ⊔ c.φ2.range) := by
    rw [mem_coreIn]
    refine ⟨(c.theta0 hc h).2, fun y hy => ?_⟩
    rw [Subgroup.mem_inf]
    constructor
    · have hfixγ : c.theta0 hc h •
          ((⟨y, hy⟩ : ↥(c.φ1.range ⊔ c.φ2.range)) •
            CosetGeom.γ₀ (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range) =
          (⟨y, hy⟩ : ↥(c.φ1.range ⊔ c.φ2.range)) •
            CosetGeom.γ₀ (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range :=
        hgfix _
      have h2 : ((⟨y, hy⟩ : ↥(c.φ1.range ⊔ c.φ2.range))⁻¹ * c.theta0 hc h *
          ⟨y, hy⟩) • CosetGeom.γ₀ (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range =
          CosetGeom.γ₀ (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range := by
        have := congrArg (fun w => (⟨y, hy⟩ : ↥(c.φ1.range ⊔ c.φ2.range))⁻¹ • w) hfixγ
        simpa [mul_smul, mul_assoc] using this
      have hstab : (((⟨y, hy⟩ : ↥(c.φ1.range ⊔ c.φ2.range))⁻¹ * c.theta0 hc h *
          ⟨y, hy⟩ : ↥(c.φ1.range ⊔ c.φ2.range)) : Y) ∈
          CosetGeom.stab (CosetGeom.γ₀ (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range) :=
        CosetGeom.mem_stab_of_smul_eq h2
      rw [CosetGeom.stab_γ₀ (le_sup_left : c.φ1.range ≤ c.φ1.range ⊔ c.φ2.range)] at hstab
      simpa using hstab
    · have hfixγ : c.theta0 hc h •
          ((⟨y, hy⟩ : ↥(c.φ1.range ⊔ c.φ2.range)) •
            CosetGeom.γ₁ (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range) =
          (⟨y, hy⟩ : ↥(c.φ1.range ⊔ c.φ2.range)) •
            CosetGeom.γ₁ (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range :=
        hgfix _
      have h2 : ((⟨y, hy⟩ : ↥(c.φ1.range ⊔ c.φ2.range))⁻¹ * c.theta0 hc h *
          ⟨y, hy⟩) • CosetGeom.γ₁ (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range =
          CosetGeom.γ₁ (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range := by
        have := congrArg (fun w => (⟨y, hy⟩ : ↥(c.φ1.range ⊔ c.φ2.range))⁻¹ • w) hfixγ
        simpa [mul_smul, mul_assoc] using this
      have hstab : (((⟨y, hy⟩ : ↥(c.φ1.range ⊔ c.φ2.range))⁻¹ * c.theta0 hc h *
          ⟨y, hy⟩ : ↥(c.φ1.range ⊔ c.φ2.range)) : Y) ∈
          CosetGeom.stab (CosetGeom.γ₁ (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range) :=
        CosetGeom.mem_stab_of_smul_eq h2
      rw [CosetGeom.stab_γ₁ (le_sup_right : c.φ2.range ≤ c.φ1.range ⊔ c.φ2.range)] at hstab
      simpa using hstab
  have htheta1 : (c.theta0 hc h : Y) = 1 := by
    have := hmem
    rw [hcore] at this
    exact Subgroup.mem_bot.mp this
  have h1 : c.theta0 hc h = 1 := Subtype.ext htheta1
  exact (c.stabIso hc (CosetGeom.γ₀ (α.Ghat1 ⊔ α.Ghat2) α.Ghat1 α.Ghat2)).inj
    h (hfix _) h1

end Faithful

section F112

variable {G : Type} [Group G] [Finite G]

abbrev f112Completion (L1 L2 S : Subgroup G) :
    (f112Amalgam L1 L2 S).Completion ↥((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) :=
  RankTwoAmalgam.inclusionCompletion ((L1 ⊔ bigB L1 L2 S)) ((L2 ⊔ bigB L1 L2 S))
    ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) rfl

abbrev f112Acting (L1 L2 S : Subgroup G) : Type :=
  ↥((f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)

abbrev f112Gamma (L1 L2 S : Subgroup G) : Type := (f112Amalgam L1 L2 S).Γhat

abbrev f112Gamma0 (L1 L2 S : Subgroup G) : f112Gamma L1 L2 S :=
  CosetGeom.γ₀ ((f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
    (f112Amalgam L1 L2 S).Ghat1 (f112Amalgam L1 L2 S).Ghat2

abbrev f112Gamma1 (L1 L2 S : Subgroup G) : f112Gamma L1 L2 S :=
  CosetGeom.γ₁ ((f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
    (f112Amalgam L1 L2 S).Ghat1 (f112Amalgam L1 L2 S).Ghat2

theorem f112_parabolic_inf_eq_bigB {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S :=
  (prop_F19_of_listed rankOneListedFacts hF.1).1

theorem f112_parabolic_sup_eq (L1 L2 S : Subgroup G) :
    (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S) = L1 ⊔ L2 ⊔ S := by
  have hB1 : borelOf L1 S ≤ L1 := F1.borelOf_le L1 S
  have hB2 : borelOf L2 S ≤ L2 := F1.borelOf_le L2 S
  have hB : bigB L1 L2 S ≤ L1 ⊔ L2 ⊔ S := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact hB1.trans (le_sup_left.trans le_sup_left)
    · exact hB2.trans (le_sup_right.trans le_sup_left)
    · show S ≤ (L1 ⊔ L2) ⊔ S
      exact le_sup_right
  apply le_antisymm
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) hB)
      (sup_le (le_sup_right.trans le_sup_left) hB)
  · refine sup_le (sup_le ?_ ?_) ?_
    · show L1 ≤ (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)
      exact le_sup_left.trans le_sup_left
    · show L2 ≤ (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)
      exact le_sup_left.trans le_sup_right
    · show S ≤ (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)
      have hSB : S ≤ bigB L1 L2 S := le_sup_right
      exact hSB.trans ((le_sup_right (a := L1) (b := bigB L1 L2 S)).trans le_sup_left)

theorem f112_coreIn_parabolic_eq_bot {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    coreIn (bigB L1 L2 S) ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) = ⊥ := by
  rw [f112_parabolic_sup_eq]
  exact (prop_F19_of_listed rankOneListedFacts hF.1).2.2.1

theorem f112_isSylowTwoOf_P1 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) : IsSylowTwoOf S ((L1 ⊔ bigB L1 L2 S)) :=
  F112W.isSylowTwoOf_parabolic (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem f112_isSylowTwoOf_P2 {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) : IsSylowTwoOf S ((L2 ⊔ bigB L1 L2 S)) :=
  F112W.isSylowTwoOf_parabolic' (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem f112Completion_isFaithful (L1 L2 S : Subgroup G) :
    (f112Completion L1 L2 S).IsFaithful :=
  RankTwoAmalgam.inclusionCompletion_isFaithful ((L1 ⊔ bigB L1 L2 S)) ((L2 ⊔ bigB L1 L2 S))
    ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) rfl

theorem f112_coreIn_ranges_eq_bot {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    coreIn ((f112Completion L1 L2 S).φ1.range ⊓ (f112Completion L1 L2 S).φ2.range)
      ((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range) = ⊥ := by
  classical
  have h1range : (f112Completion L1 L2 S).φ1.range =
      ((L1 ⊔ bigB L1 L2 S)).subgroupOf ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) :=
    Subgroup.inclusion_range (le_sup_left : (L1 ⊔ bigB L1 L2 S) ≤
      (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))
  have h2range : (f112Completion L1 L2 S).φ2.range =
      ((L2 ⊔ bigB L1 L2 S)).subgroupOf ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) :=
    Subgroup.inclusion_range (le_sup_right : (L2 ⊔ bigB L1 L2 S) ≤
      (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))
  have hK : (f112Completion L1 L2 S).φ1.range ⊓ (f112Completion L1 L2 S).φ2.range =
      ((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)).subgroupOf
        ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) := by
    rw [h1range, h2range]
    ext z
    simp [Subgroup.mem_subgroupOf]
  have hmap : (coreIn ((f112Completion L1 L2 S).φ1.range ⊓ (f112Completion L1 L2 S).φ2.range)
        ((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)).map
        ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)).subtype =
      coreIn ((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S))
        ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) := by
    rw [(f112Completion L1 L2 S).gen, hK]
    ext z
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hwcore, rfl⟩
      rw [mem_coreIn] at hwcore
      refine ⟨w.2, fun g hg => ?_⟩
      have := hwcore.2 ⟨g, hg⟩ (Subgroup.mem_top _)
      simpa [Subgroup.mem_subgroupOf] using this
    · rintro ⟨hzw, hconj⟩
      refine ⟨⟨z, hzw⟩, ?_, rfl⟩
      rw [mem_coreIn]
      refine ⟨Subgroup.mem_top _, fun g _ => ?_⟩
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hconj (g : G) g.2)
  have hbot : coreIn ((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S))
      ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) = ⊥ := by
    rw [f112_parabolic_inf_eq_bigB hF]
    exact f112_coreIn_parabolic_eq_bot hF
  have hmap' : (coreIn ((f112Completion L1 L2 S).φ1.range ⊓ (f112Completion L1 L2 S).φ2.range)
      ((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)).map
      ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)).subtype = ⊥ := by
    rw [hmap, hbot]
  exact (Subgroup.map_eq_bot_iff_of_injective _
    ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)).subtype_injective).mp hmap'

theorem f112_eq_one_of_forall_smul_eq {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {h : f112Acting L1 L2 S}
    (hfix : ∀ w : f112Gamma L1 L2 S, h • w = w) : h = 1 :=
  eq_one_of_forall_smul_eq_of_coreIn (f112Completion L1 L2 S) (f112Completion_isFaithful L1 L2 S)
    (f112_coreIn_ranges_eq_bot hF) hfix

end F112

section Stabilizers

variable {α : RankTwoAmalgam.{u}} {Y : Type v} [Group Y]

private def constGPath {V : Type*} {Γ : SimpleGraph V} (v : V) : GPath Γ 0 where
  toFun _ := v
  adj i hi := by omega
  tail i _ := rfl

private theorem stabPath_zero {V : Type*} {Γ : SimpleGraph V} {H : Type*} [Group H]
    [MulAction H V] [GraphAction H Γ] (p : GPath Γ 0) :
    p.stabPath = MulAction.stabilizer H (p 0) := by
  ext g
  simp [GPath.stabPath, MulAction.mem_stabilizer_iff]

private theorem stabilizer_cosetGeom_γ₀ {X : Type*} [Group X] (A B : Subgroup X) :
    MulAction.stabilizer ↥(A ⊔ B) (CosetGeom.γ₀ (A ⊔ B) A B) = A.subgroupOf (A ⊔ B) := by
  refine Subgroup.map_injective (Subgroup.subtype_injective (A ⊔ B)) ?_
  rw [Subgroup.map_subgroupOf_eq_of_le (le_sup_left : A ≤ A ⊔ B)]
  simpa [CosetGeom.stab] using CosetGeom.stab_γ₀ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)
    (le_sup_left : A ≤ A ⊔ B)

private theorem stabilizer_cosetGeom_γ₁ {X : Type*} [Group X] (A B : Subgroup X) :
    MulAction.stabilizer ↥(A ⊔ B) (CosetGeom.γ₁ (A ⊔ B) A B) = B.subgroupOf (A ⊔ B) := by
  refine Subgroup.map_injective (Subgroup.subtype_injective (A ⊔ B)) ?_
  rw [Subgroup.map_subgroupOf_eq_of_le (le_sup_right : B ≤ A ⊔ B)]
  simpa [CosetGeom.stab] using CosetGeom.stab_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)
    (le_sup_right : B ≤ A ⊔ B)

private theorem stabilizer_cosetGeom_inl {X : Type*} [Group X] (A B : Subgroup X)
    (x : ↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B)) :
    Nonempty (MulAction.stabilizer ↥(A ⊔ B) (Sum.inl x : CosetGeom (A ⊔ B) A B) ≃* ↥A) := by
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_γ₀ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) x
  rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_cosetGeom_γ₀]
  exact ⟨(Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ B))⟩

private theorem stabilizer_cosetGeom_inr {X : Type*} [Group X] (A B : Subgroup X)
    (y : ↥(A ⊔ B) ⧸ B.subgroupOf (A ⊔ B)) :
    Nonempty (MulAction.stabilizer ↥(A ⊔ B) (Sum.inr y : CosetGeom (A ⊔ B) A B) ≃* ↥B) := by
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) y
  rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_cosetGeom_γ₁]
  exact ⟨(Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe (le_sup_right : B ≤ A ⊔ B))⟩

private theorem stabilizer_cosetGeom_equiv {X : Type*} [Group X] (A B : Subgroup X)
    (u : CosetGeom (A ⊔ B) A B) :
    Nonempty (MulAction.stabilizer ↥(A ⊔ B) u ≃* ↥A) ∨
      Nonempty (MulAction.stabilizer ↥(A ⊔ B) u ≃* ↥B) := by
  cases u with
  | inl x => exact Or.inl (stabilizer_cosetGeom_inl A B x)
  | inr y => exact Or.inr (stabilizer_cosetGeom_inr A B y)

theorem stabilizer_equiv_of_completion (c : α.Completion Y) (hc : c.IsFaithful)
    (v : α.Γhat) :
    Nonempty (MulAction.stabilizer ↥(α.Ghat1 ⊔ α.Ghat2) v ≃* ↥(c.φ1.range)) ∨
      Nonempty (MulAction.stabilizer ↥(α.Ghat1 ⊔ α.Ghat2) v ≃* ↥(c.φ2.range)) := by
  classical
  have hdom : (constGPath v : GPath α.graphHat 0).stabPath =
      MulAction.stabilizer ↥(α.Ghat1 ⊔ α.Ghat2) v := stabPath_zero _
  have hcod : ((c.graphCovering hc).pathMap (constGPath v)).stabPath =
      MulAction.stabilizer ↥(c.φ1.range ⊔ c.φ2.range) (c.Θ hc v) := by
    rw [stabPath_zero]
    congr 1
  obtain ⟨-, -, ⟨e⟩⟩ := c.lemma_F33_3 hc v (constGPath v) rfl
  have e' : MulAction.stabilizer ↥(α.Ghat1 ⊔ α.Ghat2) v ≃*
      MulAction.stabilizer ↥(c.φ1.range ⊔ c.φ2.range) (c.Θ hc v) :=
    (MulEquiv.subgroupCongr hdom.symm).trans (e.trans (MulEquiv.subgroupCongr hcod))
  rcases stabilizer_cosetGeom_equiv (c.φ1.range) (c.φ2.range) (c.Θ hc v) with
    ⟨⟨e''⟩⟩ | ⟨⟨e''⟩⟩
  · exact Or.inl ⟨e'.trans e''⟩
  · exact Or.inr ⟨e'.trans e''⟩

end Stabilizers

section F112Vertices

variable {G : Type} [Group G] [Finite G]

private theorem range_f112Completion_φ1 (L1 L2 S : Subgroup G) :
    (f112Completion L1 L2 S).φ1.range =
      ((L1 ⊔ bigB L1 L2 S)).subgroupOf ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) :=
  Subgroup.inclusion_range (le_sup_left : (L1 ⊔ bigB L1 L2 S) ≤
    (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))

private theorem range_f112Completion_φ2 (L1 L2 S : Subgroup G) :
    (f112Completion L1 L2 S).φ2.range =
      ((L2 ⊔ bigB L1 L2 S)).subgroupOf ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) :=
  Subgroup.inclusion_range (le_sup_right : (L2 ⊔ bigB L1 L2 S) ≤
    (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S))

private theorem range_f112Completion_equiv_left (L1 L2 S : Subgroup G) :
    Nonempty (↥((f112Completion L1 L2 S).φ1.range) ≃* ↥((L1 ⊔ bigB L1 L2 S))) :=
  ⟨(MulEquiv.subgroupCongr (range_f112Completion_φ1 L1 L2 S)).trans
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : (L1 ⊔ bigB L1 L2 S) ≤
      (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)))⟩

private theorem range_f112Completion_equiv_right (L1 L2 S : Subgroup G) :
    Nonempty (↥((f112Completion L1 L2 S).φ2.range) ≃* ↥((L2 ⊔ bigB L1 L2 S))) :=
  ⟨(MulEquiv.subgroupCongr (range_f112Completion_φ2 L1 L2 S)).trans
    (Subgroup.subgroupOfEquivOfLe (le_sup_right : (L2 ⊔ bigB L1 L2 S) ≤
      (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)))⟩

theorem f112_stabilizer_Θγ₀ (L1 L2 S : Subgroup G) :
    MulAction.stabilizer ↥((f112Completion L1 L2 S).φ1.range ⊔
        (f112Completion L1 L2 S).φ2.range)
      ((f112Completion L1 L2 S).Θ (f112Completion_isFaithful L1 L2 S)
        (f112Gamma0 L1 L2 S)) =
      (f112Completion L1 L2 S).φ1.range.subgroupOf
        ((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range) := by
  rw [show (f112Completion L1 L2 S).Θ (f112Completion_isFaithful L1 L2 S)
        (f112Gamma0 L1 L2 S) =
      CosetGeom.γ₀ ((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)
        (f112Completion L1 L2 S).φ1.range (f112Completion L1 L2 S).φ2.range from
    ((f112Completion L1 L2 S).coverData (f112Completion_isFaithful L1 L2 S)).Θ_γ₀]
  exact stabilizer_cosetGeom_γ₀ _ _

theorem f112_stabilizer_Θγ₁ (L1 L2 S : Subgroup G) :
    MulAction.stabilizer ↥((f112Completion L1 L2 S).φ1.range ⊔
        (f112Completion L1 L2 S).φ2.range)
      ((f112Completion L1 L2 S).Θ (f112Completion_isFaithful L1 L2 S)
        (f112Gamma1 L1 L2 S)) =
      (f112Completion L1 L2 S).φ2.range.subgroupOf
        ((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range) := by
  rw [show (f112Completion L1 L2 S).Θ (f112Completion_isFaithful L1 L2 S)
        (f112Gamma1 L1 L2 S) =
      CosetGeom.γ₁ ((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)
        (f112Completion L1 L2 S).φ1.range (f112Completion L1 L2 S).φ2.range from
    ((f112Completion L1 L2 S).coverData (f112Completion_isFaithful L1 L2 S)).Θ_γ₁]
  exact stabilizer_cosetGeom_γ₁ _ _

private theorem coe_stabIso_equiv {α : RankTwoAmalgam.{u}} {Y : Type v} [Group Y]
    (c : α.Completion Y) (hc : c.IsFaithful) (v : α.Γhat)
    (h : MulAction.stabilizer ↥(α.Ghat1 ⊔ α.Ghat2) v) :
    ((((c.stabIso hc v).equiv h : MulAction.stabilizer ↥(c.φ1.range ⊔ c.φ2.range)
      (c.Θ hc v)) : ↥(c.φ1.range ⊔ c.φ2.range))) =
      ((c.theta0 hc h : ↥(c.φ1.range ⊔ c.φ2.range))) := by
  show ((((c.stabIso hc v).restrict h : MulAction.stabilizer ↥(c.φ1.range ⊔ c.φ2.range)
      (c.Θ hc v)) : ↥(c.φ1.range ⊔ c.φ2.range))) =
      ((c.theta0 hc h : ↥(c.φ1.range ⊔ c.φ2.range)))
  exact GraphCovering.StabIso.coe_restrict _ h

noncomputable def f112RangeEquiv0 (L1 L2 S : Subgroup G) :
    ↥((f112Completion L1 L2 S).φ1.range) ≃* ↥(L1 ⊔ bigB L1 L2 S) :=
  (MulEquiv.subgroupCongr (range_f112Completion_φ1 L1 L2 S)).trans
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : L1 ⊔ bigB L1 L2 S ≤
      L1 ⊔ bigB L1 L2 S ⊔ (L2 ⊔ bigB L1 L2 S)))

noncomputable def f112RangeEquiv1 (L1 L2 S : Subgroup G) :
    ↥((f112Completion L1 L2 S).φ2.range) ≃* ↥(L2 ⊔ bigB L1 L2 S) :=
  (MulEquiv.subgroupCongr (range_f112Completion_φ2 L1 L2 S)).trans
    (Subgroup.subgroupOfEquivOfLe (le_sup_right : L2 ⊔ bigB L1 L2 S ≤
      L1 ⊔ bigB L1 L2 S ⊔ (L2 ⊔ bigB L1 L2 S)))

private theorem coe_f112RangeEquiv0 (L1 L2 S : Subgroup G)
    (a : ↥((f112Completion L1 L2 S).φ1.range)) :
    ((f112RangeEquiv0 L1 L2 S a : ↥(L1 ⊔ bigB L1 L2 S)) : G) =
      ((Subgroup.inclusion (le_sup_left : (f112Completion L1 L2 S).φ1.range ≤
          (f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range) a :
        ↥((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)) : G) :=
  rfl

private theorem coe_f112RangeEquiv1 (L1 L2 S : Subgroup G)
    (a : ↥((f112Completion L1 L2 S).φ2.range)) :
    ((f112RangeEquiv1 L1 L2 S a : ↥(L2 ⊔ bigB L1 L2 S)) : G) =
      ((Subgroup.inclusion (le_sup_right : (f112Completion L1 L2 S).φ2.range ≤
          (f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range) a :
        ↥((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)) : G) :=
  rfl

@[expose] noncomputable def f112StabEquiv0 (L1 L2 S : Subgroup G) :
    MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S) ≃*
      ↥(L1 ⊔ bigB L1 L2 S) :=
  ((f112Completion L1 L2 S).stabIso (f112Completion_isFaithful L1 L2 S)
      (f112Gamma0 L1 L2 S)).equiv.trans
    ((MulEquiv.subgroupCongr (f112_stabilizer_Θγ₀ L1 L2 S)).trans
      ((Subgroup.subgroupOfEquivOfLe (le_sup_left :
          (f112Completion L1 L2 S).φ1.range ≤
            (f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)).trans
        (f112RangeEquiv0 L1 L2 S)))

@[expose] noncomputable def f112StabEquiv1 (L1 L2 S : Subgroup G) :
    MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S) ≃*
      ↥(L2 ⊔ bigB L1 L2 S) :=
  ((f112Completion L1 L2 S).stabIso (f112Completion_isFaithful L1 L2 S)
      (f112Gamma1 L1 L2 S)).equiv.trans
    ((MulEquiv.subgroupCongr (f112_stabilizer_Θγ₁ L1 L2 S)).trans
      ((Subgroup.subgroupOfEquivOfLe (le_sup_right :
          (f112Completion L1 L2 S).φ2.range ≤
            (f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)).trans
        (f112RangeEquiv1 L1 L2 S)))

theorem coe_f112StabEquiv0 (L1 L2 S : Subgroup G)
    (h : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)) :
    ((f112StabEquiv0 L1 L2 S h : ↥(L1 ⊔ bigB L1 L2 S)) : G) =
      (((f112Completion L1 L2 S).theta0 (f112Completion_isFaithful L1 L2 S) h :
        ↥((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)) : G) := by
  simp [f112StabEquiv0, GraphCovering.StabIso.coe_restrict, MulEquiv.subgroupCongr_apply,
    Subgroup.subgroupOfEquivOfLe_apply_coe, coe_f112RangeEquiv0, coe_stabIso_equiv,
    RankTwoAmalgam.Completion.coe_theta0]

theorem coe_f112StabEquiv1 (L1 L2 S : Subgroup G)
    (h : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)) :
    ((f112StabEquiv1 L1 L2 S h : ↥(L2 ⊔ bigB L1 L2 S)) : G) =
      (((f112Completion L1 L2 S).theta0 (f112Completion_isFaithful L1 L2 S) h :
        ↥((f112Completion L1 L2 S).φ1.range ⊔ (f112Completion L1 L2 S).φ2.range)) : G) := by
  simp [f112StabEquiv1, GraphCovering.StabIso.coe_restrict, MulEquiv.subgroupCongr_apply,
    Subgroup.subgroupOfEquivOfLe_apply_coe, coe_f112RangeEquiv1, coe_stabIso_equiv,
    RankTwoAmalgam.Completion.coe_theta0]

theorem f112_stabilizer_equiv {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (v : f112Gamma L1 L2 S) :
    Nonempty (MulAction.stabilizer (f112Acting L1 L2 S) v ≃* ↥(L1 ⊔ bigB L1 L2 S)) ∨
      Nonempty (MulAction.stabilizer (f112Acting L1 L2 S) v ≃* ↥(L2 ⊔ bigB L1 L2 S)) := by
  rcases stabilizer_equiv_of_completion (f112Completion L1 L2 S)
    (f112Completion_isFaithful L1 L2 S) v with h | h
  · obtain ⟨e⟩ := h
    obtain ⟨e'⟩ := range_f112Completion_equiv_left L1 L2 S
    exact Or.inl ⟨e.trans e'⟩
  · obtain ⟨e⟩ := h
    obtain ⟨e'⟩ := range_f112Completion_equiv_right L1 L2 S
    exact Or.inr ⟨e.trans e'⟩

private theorem sylow_card_eq_of_mulEquiv {W : Type*} [Group W] [Finite W]
    {X : Type*} [Group X] {P S : Subgroup X} (hS : IsSylowTwoOf S P) (e : W ≃* ↥P)
    (T : Sylow 2 W) : Nat.card T = Nat.card S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥P := Finite.of_injective e.symm e.symm.injective
  obtain ⟨S', hS'⟩ := F7.isSylowTwoOf_exists_sylow hS
  have h1 : Nat.card T = Nat.card S' := by
    rw [Sylow.card_eq_multiplicity T, Sylow.card_eq_multiplicity S',
      Nat.card_congr e.toEquiv]
  have h2 : Nat.card S' = Nat.card S := by
    rw [hS']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv
  rw [h1, h2]

theorem f112_finite_stabilizer {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (v : f112Gamma L1 L2 S) :
    Finite (MulAction.stabilizer (f112Acting L1 L2 S) v) := by
  rcases f112_stabilizer_equiv hF v with h | h
  · obtain ⟨e⟩ := h
    exact Finite.of_injective e e.injective
  · obtain ⟨e⟩ := h
    exact Finite.of_injective e e.injective

theorem f112_card_sylow_stabilizer {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (v : f112Gamma L1 L2 S)
    [Finite (MulAction.stabilizer (f112Acting L1 L2 S) v)]
    (T : Sylow 2 (MulAction.stabilizer (f112Acting L1 L2 S) v)) :
    Nat.card T = Nat.card S := by
  rcases f112_stabilizer_equiv hF v with h | h
  · obtain ⟨e⟩ := h
    exact sylow_card_eq_of_mulEquiv (f112_isSylowTwoOf_P1 hF) e T
  · obtain ⟨e⟩ := h
    exact sylow_card_eq_of_mulEquiv (f112_isSylowTwoOf_P2 hF) e T

end F112Vertices

section Neighbours

private theorem stabilizer_subgroupOf_eq {H : Type*} [Group H] {V : Type*} [MulAction H V]
    (K : Subgroup H) (x : V) :
    MulAction.stabilizer ↥K x = (MulAction.stabilizer H x).subgroupOf K := by
  ext k
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
  rfl

private theorem natCard_neighborSet_of_graphCovering {Vh V : Type*} {Γh : SimpleGraph Vh}
    {Γ : SimpleGraph V} {θ : Vh → V} (h : GraphCovering Γh Γ θ) (v : Vh) :
    Nat.card (Γh.neighborSet v) = Nat.card (Γ.neighborSet (θ v)) := by
  classical
  refine Nat.card_congr ?_
  refine
    { toFun := fun w => ⟨θ w.1, h.adj v w.1 w.2⟩
      invFun := fun w => ⟨(h.loc_surj v w.1 w.2).choose,
        (h.loc_surj v w.1 w.2).choose_spec.1⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro w
    exact Subtype.ext (h.loc_inj v _ w.1
      (h.loc_surj v (θ w.1) (h.adj v w.1 w.2)).choose_spec.1 w.2
      (h.loc_surj v (θ w.1) (h.adj v w.1 w.2)).choose_spec.2)
  · intro w
    exact Subtype.ext (h.loc_surj v w.1 w.2).choose_spec.2

private theorem natCard_neighborSet_smul {X : Type*} [Group X] {A B : Subgroup X}
    (g : ↥(A ⊔ B)) (u : CosetGeom (A ⊔ B) A B) :
    Nat.card ((CosetGeom.graph (A ⊔ B) A B).neighborSet (g • u)) =
      Nat.card ((CosetGeom.graph (A ⊔ B) A B).neighborSet u) := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun w => ⟨g⁻¹ • w.1, ?_⟩
      invFun := fun w => ⟨g • w.1, (CosetGeom.smul_adj g).mpr w.2⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }
  have := (CosetGeom.smul_adj g⁻¹).mpr w.2
  simpa using this

private theorem natCard_neighborSet_γ₀ {X : Type*} [Group X] (A B : Subgroup X) :
    Nat.card ((CosetGeom.graph (A ⊔ B) A B).neighborSet (CosetGeom.γ₀ (A ⊔ B) A B)) =
      (A ⊓ B).relIndex A := by
  classical
  have hset : (CosetGeom.graph (A ⊔ B) A B).neighborSet (CosetGeom.γ₀ (A ⊔ B) A B) =
      MulAction.orbit ↥(A.subgroupOf (A ⊔ B)) (CosetGeom.γ₁ (A ⊔ B) A B) := by
    ext w
    constructor
    · intro hw
      cases w with
      | inl x => exact (CosetGeom.not_adj_inl_inl (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)
          (x := ((1 : ↥(A ⊔ B)) : ↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B))) (x' := x) hw).elim
      | inr y =>
        obtain ⟨g, hgA, hgy⟩ := CosetGeom.adj_γ₀_inr_iff (G₀ := A ⊔ B) (G₁ := A) (G₂ := B).mp hw
        refine ⟨⟨g, Subgroup.mem_subgroupOf.mpr hgA⟩, ?_⟩
        change ((g : ↥(A ⊔ B)) • CosetGeom.γ₁ (A ⊔ B) A B) = Sum.inr y
        rw [CosetGeom.smul_γ₁]
        exact congrArg Sum.inr hgy
    · rintro ⟨a, rfl⟩
      change ((a : ↥(A ⊔ B)) • CosetGeom.γ₁ (A ⊔ B) A B) ∈
        (CosetGeom.graph (A ⊔ B) A B).neighborSet (CosetGeom.γ₀ (A ⊔ B) A B)
      rw [CosetGeom.smul_γ₁]
      exact CosetGeom.adj_γ₀_inr_iff (G₀ := A ⊔ B) (G₁ := A) (G₂ := B).mpr ⟨(a : ↥(A ⊔ B)),
        Subgroup.mem_subgroupOf.mp a.2, rfl⟩
  rw [hset, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
  have hstab : MulAction.stabilizer ↥(A.subgroupOf (A ⊔ B)) (CosetGeom.γ₁ (A ⊔ B) A B) =
      (MulAction.stabilizer ↥(A ⊔ B) (CosetGeom.γ₁ (A ⊔ B) A B)).subgroupOf
        (A.subgroupOf (A ⊔ B)) :=
    stabilizer_subgroupOf_eq (H := ↥(A ⊔ B)) (V := CosetGeom (A ⊔ B) A B)
      (A.subgroupOf (A ⊔ B)) (CosetGeom.γ₁ (A ⊔ B) A B)
  rw [hstab, stabilizer_cosetGeom_γ₁]
  have hrel : ((B.subgroupOf (A ⊔ B)).subgroupOf (A.subgroupOf (A ⊔ B))).index =
      B.relIndex A :=
    Subgroup.relIndex_subgroupOf (H := B) (K := A) (L := A ⊔ B) le_sup_left
  rw [hrel]
  exact (Subgroup.inf_relIndex_left A B).symm

private theorem natCard_neighborSet_γ₁ {X : Type*} [Group X] (A B : Subgroup X) :
    Nat.card ((CosetGeom.graph (A ⊔ B) A B).neighborSet (CosetGeom.γ₁ (A ⊔ B) A B)) =
      (A ⊓ B).relIndex B := by
  classical
  have hset : (CosetGeom.graph (A ⊔ B) A B).neighborSet (CosetGeom.γ₁ (A ⊔ B) A B) =
      MulAction.orbit ↥(B.subgroupOf (A ⊔ B)) (CosetGeom.γ₀ (A ⊔ B) A B) := by
    ext w
    constructor
    · intro hw
      cases w with
      | inr y => exact (CosetGeom.not_adj_inr_inr (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)
          (y := ((1 : ↥(A ⊔ B)) : ↥(A ⊔ B) ⧸ B.subgroupOf (A ⊔ B))) (y' := y) hw).elim
      | inl x =>
        obtain ⟨g, hgB, hgx⟩ := CosetGeom.adj_γ₁_inl_iff (G₀ := A ⊔ B) (G₁ := A) (G₂ := B).mp hw
        refine ⟨⟨g, Subgroup.mem_subgroupOf.mpr hgB⟩, ?_⟩
        change ((g : ↥(A ⊔ B)) • CosetGeom.γ₀ (A ⊔ B) A B) = Sum.inl x
        rw [CosetGeom.smul_γ₀]
        exact congrArg Sum.inl hgx
    · rintro ⟨b, rfl⟩
      change ((b : ↥(A ⊔ B)) • CosetGeom.γ₀ (A ⊔ B) A B) ∈
        (CosetGeom.graph (A ⊔ B) A B).neighborSet (CosetGeom.γ₁ (A ⊔ B) A B)
      rw [CosetGeom.smul_γ₀]
      exact CosetGeom.adj_γ₁_inl_iff (G₀ := A ⊔ B) (G₁ := A) (G₂ := B).mpr ⟨(b : ↥(A ⊔ B)),
        Subgroup.mem_subgroupOf.mp b.2, rfl⟩
  rw [hset, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
  have hstab : MulAction.stabilizer ↥(B.subgroupOf (A ⊔ B)) (CosetGeom.γ₀ (A ⊔ B) A B) =
      (MulAction.stabilizer ↥(A ⊔ B) (CosetGeom.γ₀ (A ⊔ B) A B)).subgroupOf
        (B.subgroupOf (A ⊔ B)) :=
    stabilizer_subgroupOf_eq (H := ↥(A ⊔ B)) (V := CosetGeom (A ⊔ B) A B)
      (B.subgroupOf (A ⊔ B)) (CosetGeom.γ₀ (A ⊔ B) A B)
  rw [hstab, stabilizer_cosetGeom_γ₀]
  have hrel : ((A.subgroupOf (A ⊔ B)).subgroupOf (B.subgroupOf (A ⊔ B))).index =
      A.relIndex B :=
    Subgroup.relIndex_subgroupOf (H := A) (K := B) (L := A ⊔ B) le_sup_right
  rw [hrel]
  exact (Subgroup.inf_relIndex_right A B).symm

end Neighbours

section F112Neighbours

variable {G : Type} [Group G] [Finite G]

theorem f112_natCard_neighborSet_of_vtype_false
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) {v : f112Gamma L1 L2 S}
    (hv : CosetGeom.vtype v = false) :
    Nat.card ((f112Amalgam L1 L2 S).graphHat.neighborSet v) =
      (bigB L1 L2 S).relIndex ((L1 ⊔ bigB L1 L2 S)) := by
  classical
  have hc : (f112Completion L1 L2 S).IsFaithful := f112Completion_isFaithful L1 L2 S
  have hv' : CosetGeom.vtype ((f112Completion L1 L2 S).Θ hc v) = false := by
    cases v with
    | inl x => rfl
    | inr y => simp [CosetGeom.vtype] at hv
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ (G₀ := (f112Completion L1 L2 S).φ1.range ⊔
    (f112Completion L1 L2 S).φ2.range) (G₁ := (f112Completion L1 L2 S).φ1.range)
    (G₂ := (f112Completion L1 L2 S).φ2.range) hv'
  rw [natCard_neighborSet_of_graphCovering ((f112Completion L1 L2 S).graphCovering hc), hg,
    natCard_neighborSet_smul]
  rw [natCard_neighborSet_γ₀]
  have hK : (f112Completion L1 L2 S).φ1.range ⊓ (f112Completion L1 L2 S).φ2.range =
      ((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)).subgroupOf
        ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) := by
    rw [range_f112Completion_φ1 L1 L2 S, range_f112Completion_φ2 L1 L2 S]
    ext z
    simp [Subgroup.mem_subgroupOf]
  rw [hK, range_f112Completion_φ1 L1 L2 S,
    Subgroup.relIndex_subgroupOf (le_sup_left : (L1 ⊔ bigB L1 L2 S) ≤
      (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)), f112_parabolic_inf_eq_bigB hF]

theorem f112_natCard_neighborSet_of_vtype_true
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) {v : f112Gamma L1 L2 S}
    (hv : CosetGeom.vtype v = true) :
    Nat.card ((f112Amalgam L1 L2 S).graphHat.neighborSet v) =
      (bigB L1 L2 S).relIndex ((L2 ⊔ bigB L1 L2 S)) := by
  classical
  have hc : (f112Completion L1 L2 S).IsFaithful := f112Completion_isFaithful L1 L2 S
  have hv' : CosetGeom.vtype ((f112Completion L1 L2 S).Θ hc v) = true := by
    cases v with
    | inl x => simp [CosetGeom.vtype] at hv
    | inr y => rfl
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₁ (G₀ := (f112Completion L1 L2 S).φ1.range ⊔
    (f112Completion L1 L2 S).φ2.range) (G₁ := (f112Completion L1 L2 S).φ1.range)
    (G₂ := (f112Completion L1 L2 S).φ2.range) hv'
  rw [natCard_neighborSet_of_graphCovering ((f112Completion L1 L2 S).graphCovering hc), hg,
    natCard_neighborSet_smul]
  rw [natCard_neighborSet_γ₁]
  have hK : (f112Completion L1 L2 S).φ1.range ⊓ (f112Completion L1 L2 S).φ2.range =
      ((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)).subgroupOf
        ((L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)) := by
    rw [range_f112Completion_φ1 L1 L2 S, range_f112Completion_φ2 L1 L2 S]
    ext z
    simp [Subgroup.mem_subgroupOf]
  rw [hK, range_f112Completion_φ2 L1 L2 S,
    Subgroup.relIndex_subgroupOf (le_sup_right : (L2 ⊔ bigB L1 L2 S) ≤
      (L1 ⊔ bigB L1 L2 S) ⊔ (L2 ⊔ bigB L1 L2 S)), f112_parabolic_inf_eq_bigB hF]

theorem f112_natCard_neighborSet {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (v : f112Gamma L1 L2 S) :
    Nat.card ((f112Amalgam L1 L2 S).graphHat.neighborSet v) =
        (bigB L1 L2 S).relIndex ((L1 ⊔ bigB L1 L2 S)) ∨
      Nat.card ((f112Amalgam L1 L2 S).graphHat.neighborSet v) =
        (bigB L1 L2 S).relIndex ((L2 ⊔ bigB L1 L2 S)) := by
  cases hv : CosetGeom.vtype v
  · exact Or.inl (f112_natCard_neighborSet_of_vtype_false hF hv)
  · exact Or.inr (f112_natCard_neighborSet_of_vtype_true hF hv)

theorem f112_stabilizer_transitive_on_nbrs {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {v w w' : f112Gamma L1 L2 S}
    (hw : w ∈ (f112Amalgam L1 L2 S).graphHat.neighborSet v)
    (hw' : w' ∈ (f112Amalgam L1 L2 S).graphHat.neighborSet v) :
    ∃ g : f112Acting L1 L2 S,
      g ∈ MulAction.stabilizer (f112Acting L1 L2 S) v ∧ g • w = w' := by
  classical
  have hc : (f112Completion L1 L2 S).IsFaithful := f112Completion_isFaithful L1 L2 S
  have h1 : (f112Completion L1 L2 S).graph.Adj
      ((f112Completion L1 L2 S).Θ hc v) ((f112Completion L1 L2 S).Θ hc w) :=
    ((f112Completion L1 L2 S).graphCovering hc).adj v w hw
  have h2 : (f112Completion L1 L2 S).graph.Adj
      ((f112Completion L1 L2 S).Θ hc v) ((f112Completion L1 L2 S).Θ hc w') :=
    ((f112Completion L1 L2 S).graphCovering hc).adj v w' hw'
  obtain ⟨g, hgstab, hgw⟩ := CosetGeom.stab_transitive_on_nbrs h1 h2
  obtain ⟨gh, hghv, hghg⟩ := ((f112Completion L1 L2 S).stabIso hc v).surj g
    (CosetGeom.smul_eq_of_mem_stab hgstab)
  refine ⟨gh, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff]
    exact hghv
  · have hadj : (f112Amalgam L1 L2 S).graphHat.Adj v (gh • w) := by
      have := (CosetGeom.smul_adj gh).mpr hw
      rwa [hghv] at this
    refine ((f112Completion L1 L2 S).graphCovering hc).loc_inj v (gh • w) w' hadj hw' ?_
    rw [(f112Completion L1 L2 S).Θ_smul hc gh w]
    rw [show (f112Completion L1 L2 S).theta0 hc gh = g from hghg, hgw]

end F112Neighbours

section TreeFacts

variable {G : Type} [Group G] [Finite G]

theorem f112_graphHat_connected (L1 L2 S : Subgroup G) :
    (f112Amalgam L1 L2 S).graphHat.Connected :=
  CosetGeom.connected (G₀ := (f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)
    (G₁ := (f112Amalgam L1 L2 S).Ghat1) (G₂ := (f112Amalgam L1 L2 S).Ghat2) rfl

private theorem f112_two_le_relIndex_left {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    2 ≤ (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hlt : L1 ⊓ bigB L1 L2 S < L1 := by
    rw [F1.inf_bigB_eq_borelOf hR]
    exact F1.lt_borelOf hR
  have hne : ((bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S)) ≠ ⊤ := by
    intro htop
    have hP1leB : L1 ⊔ bigB L1 L2 S ≤ bigB L1 L2 S := by
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥(L1 ⊔ bigB L1 L2 S)) ∈
          (bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S) := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hx'
    exact hlt.ne (le_antisymm inf_le_left
      (le_inf le_rfl ((le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S).trans hP1leB)))
  exact Nat.succ_le_of_lt (Subgroup.one_lt_index_of_ne_top hne)

private theorem f112_two_le_relIndex_right {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    2 ≤ (bigB L1 L2 S).relIndex (L2 ⊔ bigB L1 L2 S) := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hlt : L2 ⊓ bigB L1 L2 S < L2 := by
    rw [← bigB_comm L1 L2 S, F1.inf_bigB_eq_borelOf hR.symm]
    exact F1.lt_borelOf hR.symm
  have hne : ((bigB L1 L2 S).subgroupOf (L2 ⊔ bigB L1 L2 S)) ≠ ⊤ := by
    intro htop
    have hP2leB : L2 ⊔ bigB L1 L2 S ≤ bigB L1 L2 S := by
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥(L2 ⊔ bigB L1 L2 S)) ∈
          (bigB L1 L2 S).subgroupOf (L2 ⊔ bigB L1 L2 S) := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hx'
    exact hlt.ne (le_antisymm inf_le_left
      (le_inf le_rfl ((le_sup_left : L2 ≤ L2 ⊔ bigB L1 L2 S).trans hP2leB)))
  exact Nat.succ_le_of_lt (Subgroup.one_lt_index_of_ne_top hne)

theorem f112_no_dead_ends {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) {v w : f112Gamma L1 L2 S}
    (h : (f112Amalgam L1 L2 S).graphHat.Adj v w) :
    ∃ u, (f112Amalgam L1 L2 S).graphHat.Adj v u ∧ u ≠ w := by
  by_contra hno
  push Not at hno
  have hsub : (f112Amalgam L1 L2 S).graphHat.neighborSet v = {w} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨h, fun u hu => hno u hu⟩
  have h2 : 2 ≤ Nat.card ((f112Amalgam L1 L2 S).graphHat.neighborSet v) := by
    rcases f112_natCard_neighborSet hF v with hc | hc
    · rw [hc]
      exact f112_two_le_relIndex_left hF
    · rw [hc]
      exact f112_two_le_relIndex_right hF
  rw [hsub] at h2
  have h1 : Nat.card ({w} : Set (f112Gamma L1 L2 S)) = 1 := by simp
  rw [h1] at h2
  omega

end TreeFacts

section Core

variable {G : Type} [Group G]

private theorem mem_pCoreOf_iff_mem_pCore {L : Subgroup G} {x : ↥L} :
    (x : G) ∈ pCoreOf 2 L ↔ x ∈ pCore 2 ↥L := by
  rw [pCoreOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    simpa [Subtype.ext hyx] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem pCoreOf_le_normalCore_map {L P Q : Subgroup G}
    (hpPL : pCoreOf 2 L ≤ pCoreOf 2 P) (hpPQ : pCoreOf 2 P ≤ Q) :
    pCoreOf 2 L ≤ L ⊓ (Q.subgroupOf P).normalCore.map P.subtype := by
  have hpPsub : (pCoreOf 2 P).subgroupOf P = pCore 2 ↥P :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective (pCore 2 ↥P)
  haveI : ((pCoreOf 2 P).subgroupOf P).Normal := by
    rw [hpPsub]
    exact pCore_normal
  have hle : (pCoreOf 2 P).subgroupOf P ≤ Q.subgroupOf P := fun z hz =>
    Subgroup.mem_subgroupOf.mpr (hpPQ (Subgroup.mem_subgroupOf.mp hz))
  have hcore : (pCoreOf 2 P).subgroupOf P ≤ (Q.subgroupOf P).normalCore :=
    Subgroup.normal_le_normalCore.2 hle
  refine le_inf (pCoreOf_le (r := 2) L) ?_
  calc pCoreOf 2 L ≤ pCoreOf 2 P := hpPL
    _ = ((pCoreOf 2 P).subgroupOf P).map P.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (pCoreOf_le (r := 2) P)).symm
    _ ≤ ((Q.subgroupOf P).normalCore).map P.subtype := Subgroup.map_mono hcore

private theorem inf_normalCore_map_le_pCoreOf {L P Q : Subgroup G}
    (hLP : L ≤ P) (hpPL : pCoreOf 2 L ≤ pCoreOf 2 P) (hpPQ : pCoreOf 2 P ≤ Q)
    (hproper : L ⊓ Q < L) (hsimple : IsSimpleGroup (L ⧸ pCore 2 ↥L)) :
    L ⊓ (Q.subgroupOf P).normalCore.map P.subtype ≤ pCoreOf 2 L := by
  classical
  have hMle : ((Q.subgroupOf P).normalCore.map P.subtype) ≤ Q := by
    rintro x ⟨k, hk, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (Subgroup.normalCore_le _ hk)
  have hMleP : ((Q.subgroupOf P).normalCore.map P.subtype) ≤ P := Subgroup.map_subtype_le _
  have hMnorm : (((Q.subgroupOf P).normalCore.map P.subtype).subgroupOf P).Normal := by
    rw [show (((Q.subgroupOf P).normalCore.map P.subtype).subgroupOf P) =
        (Q.subgroupOf P).normalCore from
      Subgroup.comap_map_eq_self_of_injective P.subtype_injective _]
    exact Subgroup.normalCore_normal _
  have hPN : P ≤ Subgroup.normalizer (((Q.subgroupOf P).normalCore.map P.subtype : Subgroup G) :
      Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMleP).mp hMnorm
  have hLN : L ≤ Subgroup.normalizer (((Q.subgroupOf P).normalCore.map P.subtype : Subgroup G) :
      Set G) := hLP.trans hPN
  have hNnorm : ((L ⊓ (Q.subgroupOf P).normalCore.map P.subtype).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (Subgroup.le_normalizer_inf Subgroup.le_normalizer hLN)
  intro x hx
  set M : Subgroup G := (Q.subgroupOf P).normalCore.map P.subtype with hMdef
  set N : Subgroup ↥L := (L ⊓ M).subgroupOf L with hNdef
  let π : ↥L →* ↥L ⧸ pCore 2 ↥L := QuotientGroup.mk' (pCore 2 ↥L)
  let Nbar : Subgroup (↥L ⧸ pCore 2 ↥L) := N.map π
  have hxN : (⟨x, hx.1⟩ : ↥L) ∈ N := Subgroup.mem_subgroupOf.mpr hx
  have hNbarNormal : Nbar.Normal := hNnorm.map π (QuotientGroup.mk'_surjective _)
  have hNbarLe : Nbar ≤ ((L ⊓ Q).subgroupOf L).map π := by
    refine Subgroup.map_mono ?_
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr
      ⟨(Subgroup.mem_subgroupOf.mp hy).1, hMle (Subgroup.mem_subgroupOf.mp hy).2⟩
  have hpcle : pCoreOf 2 L ≤ L ⊓ Q := le_inf (pCoreOf_le (r := 2) L) (hpPL.trans hpPQ)
  have hpcle' : pCore 2 ↥L ≤ (L ⊓ Q).subgroupOf L := fun z hz =>
    Subgroup.mem_subgroupOf.mpr
      (hpcle ((mem_pCoreOf_iff_mem_pCore (L := L) (x := z)).mpr hz))
  have hproperImg : ((L ⊓ Q).subgroupOf L).map π ≠ ⊤ := by
    intro htop
    have hH' : (L ⊓ Q).subgroupOf L = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : π y ∈ ((L ⊓ Q).subgroupOf L).map π := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨h, hh, hph⟩ := hy
      have hk : h⁻¹ * y ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hph, inv_mul_cancel]
      have hπker : π.ker = pCore 2 ↥L := QuotientGroup.ker_mk' (pCore 2 ↥L)
      have hk' : h⁻¹ * y ∈ (L ⊓ Q).subgroupOf L := by
        rw [hπker] at hk
        exact hpcle' hk
      have : y = h * (h⁻¹ * y) := by group
      rw [this]
      exact Subgroup.mul_mem ((L ⊓ Q).subgroupOf L) hh hk'
    have hLle : L ≤ L ⊓ Q := by
      intro z hz
      have : (⟨z, hz⟩ : ↥L) ∈ (L ⊓ Q).subgroupOf L := by
        rw [hH']
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    exact hproper.ne (le_antisymm inf_le_left hLle)
  haveI : IsSimpleGroup (L ⧸ pCore 2 ↥L) := hsimple
  haveI : Nbar.Normal := hNbarNormal
  have hNbarBot : Nbar = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Nbar with h | h
    · exact h
    · exact (hproperImg (le_antisymm le_top (h ▸ hNbarLe))).elim
  have hxker : π ⟨x, hx.1⟩ = 1 := by
    have hmem : π ⟨x, hx.1⟩ ∈ Nbar := Subgroup.mem_map_of_mem π hxN
    rwa [hNbarBot] at hmem
  have hxpc : (⟨x, hx.1⟩ : ↥L) ∈ pCore 2 ↥L := by
    have hmem : (⟨x, hx.1⟩ : ↥L) ∈ π.ker := MonoidHom.mem_ker.mpr hxker
    have hπker : π.ker = pCore 2 ↥L := QuotientGroup.ker_mk' (pCore 2 ↥L)
    rwa [hπker] at hmem
  exact (mem_pCoreOf_iff_mem_pCore (L := L) (x := ⟨x, hx.1⟩)).mpr hxpc

end Core

section F112Core

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def f112K1 (L1 L2 S : Subgroup G) : Subgroup ↥((L1 ⊔ bigB L1 L2 S)) :=
  (((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)).subgroupOf ((L1 ⊔ bigB L1 L2 S))).normalCore

@[expose] noncomputable def f112K2 (L1 L2 S : Subgroup G) : Subgroup ↥((L2 ⊔ bigB L1 L2 S)) :=
  (((L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S)).subgroupOf ((L2 ⊔ bigB L1 L2 S))).normalCore

instance f112K1_normal (L1 L2 S : Subgroup G) : (f112K1 L1 L2 S).Normal :=
  Subgroup.normalCore_normal _

instance f112K2_normal (L1 L2 S : Subgroup G) : (f112K2 L1 L2 S).Normal :=
  Subgroup.normalCore_normal _

theorem f112_inf_map_K1_eq_pCoreOf {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hL1 : IsSimpleGroup (oTwoQuot ↥L1)) :
    L1 ⊓ (f112K1 L1 L2 S).map ((L1 ⊔ bigB L1 L2 S)).subtype = pCoreOf 2 L1 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hproper : L1 ⊓ ((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)) < L1 := by
    rw [f112_parabolic_inf_eq_bigB hF, F1.inf_bigB_eq_borelOf hR]
    exact F1.lt_borelOf hR
  have hpPQ : pCoreOf 2 ((L1 ⊔ bigB L1 L2 S)) ≤ (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) := by
    rw [f112_parabolic_inf_eq_bigB hF]
    exact (F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF)).trans le_sup_right
  refine le_antisymm ?_ ?_
  · exact inf_normalCore_map_le_pCoreOf (L := L1) (P := (L1 ⊔ bigB L1 L2 S))
      (Q := (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)) le_sup_left
      (Hyp111.pCoreOf_le_pCoreOf_vertex hF.1) hpPQ hproper hL1
  · exact pCoreOf_le_normalCore_map (L := L1) (P := (L1 ⊔ bigB L1 L2 S))
      (Q := (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S))
      (Hyp111.pCoreOf_le_pCoreOf_vertex hF.1) hpPQ

theorem f112_inf_map_K2_eq_pCoreOf {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hL2 : IsSimpleGroup (oTwoQuot ↥L2)) :
    L2 ⊓ (f112K2 L1 L2 S).map ((L2 ⊔ bigB L1 L2 S)).subtype = pCoreOf 2 L2 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hinf' : (L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S) = bigB L1 L2 S := by
    rw [inf_comm]
    exact f112_parabolic_inf_eq_bigB hF
  have hproper : L2 ⊓ ((L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S)) < L2 := by
    rw [hinf', ← bigB_comm L1 L2 S, F1.inf_bigB_eq_borelOf hR.symm]
    exact F1.lt_borelOf hR.symm
  have hpPQ : pCoreOf 2 ((L2 ⊔ bigB L1 L2 S)) ≤ (L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S) := by
    rw [hinf']
    exact (F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF)).trans le_sup_right
  have hpPL : pCoreOf 2 L2 ≤ pCoreOf 2 ((L2 ⊔ bigB L1 L2 S)) := by
    have h := Hyp111.pCoreOf_le_pCoreOf_vertex (L1 := L2) (L2 := L1) hF.1.symm
    simpa [bigB_comm L1 L2 S] using h
  refine le_antisymm ?_ ?_
  · exact inf_normalCore_map_le_pCoreOf (L := L2) (P := (L2 ⊔ bigB L1 L2 S))
      (Q := (L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S)) le_sup_left hpPL hpPQ hproper hL2
  · exact pCoreOf_le_normalCore_map (L := L2) (P := (L2 ⊔ bigB L1 L2 S))
      (Q := (L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S)) hpPL hpPQ

theorem f112_exists_normal_iso_oTwoQuot_left {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hL1 : IsSimpleGroup (oTwoQuot ↥L1)) :
    ∃ N : Subgroup (↥((L1 ⊔ bigB L1 L2 S)) ⧸ f112K1 L1 L2 S),
      N.Normal ∧ Nonempty (↥N ≃* oTwoQuot ↥L1) := by
  classical
  haveI : (f112K1 L1 L2 S).Normal := Subgroup.normalCore_normal _
  let ψ : ↥L1 →* ↥((L1 ⊔ bigB L1 L2 S)) ⧸ f112K1 L1 L2 S :=
    (QuotientGroup.mk' (f112K1 L1 L2 S)).comp
      (Subgroup.inclusion (le_sup_left : L1 ≤ (L1 ⊔ bigB L1 L2 S)))
  have hψrange : ψ.range = (L1.subgroupOf ((L1 ⊔ bigB L1 L2 S))).map
      (QuotientGroup.mk' (f112K1 L1 L2 S)) := by
    rw [show ψ = (QuotientGroup.mk' (f112K1 L1 L2 S)).comp
        (Subgroup.inclusion (le_sup_left : L1 ≤ (L1 ⊔ bigB L1 L2 S))) from rfl,
      MonoidHom.range_comp, Subgroup.inclusion_range]
  have hL1n : (L1.subgroupOf ((L1 ⊔ bigB L1 L2 S))).Normal := by
    have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (le_sup_left : L1 ≤ (L1 ⊔ bigB L1 L2 S))).mpr
      (sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left hR).1)
  refine ⟨ψ.range, ?_, ?_⟩
  · rw [hψrange]
    exact hL1n.map _ (QuotientGroup.mk'_surjective _)
  · have hker : ψ.ker = pCore 2 ↥L1 := by
      ext x
      rw [MonoidHom.mem_ker]
      show ((Subgroup.inclusion (le_sup_left : L1 ≤ (L1 ⊔ bigB L1 L2 S)) x :
          ↥(L1 ⊔ bigB L1 L2 S)) : ↥(L1 ⊔ bigB L1 L2 S) ⧸ f112K1 L1 L2 S) = 1 ↔
        x ∈ pCore 2 ↥L1
      rw [QuotientGroup.eq_one_iff]
      constructor
      · intro hxK
        have hmem : ((Subgroup.inclusion (le_sup_left : L1 ≤ (L1 ⊔ bigB L1 L2 S)) x :
            ↥((L1 ⊔ bigB L1 L2 S))) : G) ∈
            L1 ⊓ (f112K1 L1 L2 S).map ((L1 ⊔ bigB L1 L2 S)).subtype :=
          ⟨x.2, ⟨_, hxK, rfl⟩⟩
        rw [f112_inf_map_K1_eq_pCoreOf hF hL1] at hmem
        exact (mem_pCoreOf_iff_mem_pCore (L := L1) (x := x)).mp hmem
      · intro hxp
        have hmem : ((Subgroup.inclusion (le_sup_left : L1 ≤ (L1 ⊔ bigB L1 L2 S)) x :
            ↥((L1 ⊔ bigB L1 L2 S))) : G) ∈
            L1 ⊓ (f112K1 L1 L2 S).map ((L1 ⊔ bigB L1 L2 S)).subtype := by
          rw [f112_inf_map_K1_eq_pCoreOf hF hL1]
          exact (mem_pCoreOf_iff_mem_pCore (L := L1) (x := x)).mpr hxp
        obtain ⟨-, y, hyK, hy⟩ := hmem
        have hy' : y = Subgroup.inclusion (le_sup_left : L1 ≤ (L1 ⊔ bigB L1 L2 S)) x :=
          Subtype.ext hy
        rwa [hy'] at hyK
    exact ⟨(QuotientGroup.quotientKerEquivRange ψ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)⟩

theorem f112_exists_normal_iso_oTwoQuot_right {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hL2 : IsSimpleGroup (oTwoQuot ↥L2)) :
    ∃ N : Subgroup (↥((L2 ⊔ bigB L1 L2 S)) ⧸ f112K2 L1 L2 S),
      N.Normal ∧ Nonempty (↥N ≃* oTwoQuot ↥L2) := by
  classical
  haveI : (f112K2 L1 L2 S).Normal := Subgroup.normalCore_normal _
  let ψ : ↥L2 →* ↥((L2 ⊔ bigB L1 L2 S)) ⧸ f112K2 L1 L2 S :=
    (QuotientGroup.mk' (f112K2 L1 L2 S)).comp
      (Subgroup.inclusion (le_sup_left : L2 ≤ (L2 ⊔ bigB L1 L2 S)))
  have hψrange : ψ.range = (L2.subgroupOf ((L2 ⊔ bigB L1 L2 S))).map
      (QuotientGroup.mk' (f112K2 L1 L2 S)) := by
    rw [show ψ = (QuotientGroup.mk' (f112K2 L1 L2 S)).comp
        (Subgroup.inclusion (le_sup_left : L2 ≤ (L2 ⊔ bigB L1 L2 S))) from rfl,
      MonoidHom.range_comp, Subgroup.inclusion_range]
  have hL2n : (L2.subgroupOf ((L2 ⊔ bigB L1 L2 S))).Normal := by
    have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (le_sup_left : L2 ≤ (L2 ⊔ bigB L1 L2 S))).mpr
      (sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left hR).2)
  refine ⟨ψ.range, ?_, ?_⟩
  · rw [hψrange]
    exact hL2n.map _ (QuotientGroup.mk'_surjective _)
  · have hker : ψ.ker = pCore 2 ↥L2 := by
      ext x
      rw [MonoidHom.mem_ker]
      show ((Subgroup.inclusion (le_sup_left : L2 ≤ (L2 ⊔ bigB L1 L2 S)) x :
          ↥((L2 ⊔ bigB L1 L2 S))) : ↥((L2 ⊔ bigB L1 L2 S)) ⧸ f112K2 L1 L2 S) = 1 ↔
        x ∈ pCore 2 ↥L2
      rw [QuotientGroup.eq_one_iff]
      constructor
      · intro hxK
        have hmem : ((Subgroup.inclusion (le_sup_left : L2 ≤ (L2 ⊔ bigB L1 L2 S)) x :
            ↥((L2 ⊔ bigB L1 L2 S))) : G) ∈
            L2 ⊓ (f112K2 L1 L2 S).map ((L2 ⊔ bigB L1 L2 S)).subtype :=
          ⟨x.2, ⟨_, hxK, rfl⟩⟩
        rw [f112_inf_map_K2_eq_pCoreOf hF hL2] at hmem
        exact (mem_pCoreOf_iff_mem_pCore (L := L2) (x := x)).mp hmem
      · intro hxp
        have hmem : ((Subgroup.inclusion (le_sup_left : L2 ≤ (L2 ⊔ bigB L1 L2 S)) x :
            ↥((L2 ⊔ bigB L1 L2 S))) : G) ∈
            L2 ⊓ (f112K2 L1 L2 S).map ((L2 ⊔ bigB L1 L2 S)).subtype := by
          rw [f112_inf_map_K2_eq_pCoreOf hF hL2]
          exact (mem_pCoreOf_iff_mem_pCore (L := L2) (x := x)).mpr hxp
        obtain ⟨-, y, hyK, hy⟩ := hmem
        have hy' : y = Subgroup.inclusion (le_sup_left : L2 ≤ (L2 ⊔ bigB L1 L2 S)) x :=
          Subtype.ext hy
        rwa [hy'] at hyK
    exact ⟨(QuotientGroup.quotientKerEquivRange ψ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)⟩

end F112Core

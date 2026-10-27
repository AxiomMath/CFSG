module

public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B2F

namespace E2

@[expose] def IsL2Natural {W : Type*} [CommGroup W] (L : Subgroup (MulAut W)) (C : Subgroup W)
    (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
    ∃ (e : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
      (β : ↥(commV L) →* Multiplicative (Fin 2 → F)),
      Function.Surjective β ∧ β.ker = (commV L ⊓ C).subgroupOf (commV L) ∧
      ∀ (h : ↥L) (u : ↥(commV L)) (hu : (h : MulAut W) (u : W) ∈ commV L),
        Multiplicative.toAdd (β ⟨(h : MulAut W) u, hu⟩) =
          (e h : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))

@[expose] def IsA5Module {W : Type*} [CommGroup W] (L : Subgroup (MulAut W)) : Prop :=
  ∃ (θ : ↥L ≃* Equiv.Perm (Fin 5)) (β : ↥(commV L) ≃* Multiplicative (evenWeight 5)),
    ∀ (h : ↥L) (u : ↥(commV L)) (hu : (h : MulAut W) (u : W) ∈ commV L) (i : Fin 5),
      ((Multiplicative.toAdd (β ⟨(h : MulAut W) u, hu⟩) : evenWeight 5) : Fin 5 → ZMod 2) i =
        ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) ((θ h)⁻¹ i)

variable {Γ : Type} [Group Γ]

@[expose] def E23Concl [Finite Γ] (H T V : Subgroup Γ) (hV : IsElemAbelian 2 V) : Prop :=
  twoResidual H ≤ thompsonJ H ∧
  ∃ I : Finset (Subgroup (MulAut (IntMod V hV))),
    (I.card = 1 ∨ I.card = 2) ∧
    autI hV (thompsonJ H) = ⨆ L ∈ I, L ∧
    (∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) ∧
    (∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥) ∧
    (∀ L ∈ I, ∀ L' ∈ I, ∃ t ∈ autI hV T, B1.conjAut t L = L') ∧
    (∀ L ∈ I, (∃ n : ℕ, IsL2Natural L (fixV (autI hV (twoResidual H))) n) ∨ IsA5Module L) ∧
    fixV (autI hV (twoResidual H)) ⊔ ⨆ L ∈ I, commV L = ⊤ ∧
    (∀ L ∈ I, commV L ⊓
        (fixV (autI hV (twoResidual H)) ⊔ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L') ≤
      fixV (autI hV (twoResidual H))) ∧
    ((∀ L ∈ I, ∃ n : ℕ, IsL2Natural L (fixV (autI hV (twoResidual H))) n) →
      autI hV (baum T) = autI hV (thompsonJ T) ∧
      IsSylowTwoOf (autI hV (thompsonJ T)) (autI hV (thompsonJ H)) ∧
      IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T) ∧
      conjClosure (omegaOneCenterOf (thompsonJ T)) (twoResidual H) =
        ⁅V, twoResidual H⁆ ⊔
          (omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (twoResidual H : Set Γ))) ∧
    ((∀ L ∈ I, IsA5Module L) →
      autI hV (baum T) = autI hV (thompsonJ T) ∧
      autI hV (thompsonJ T) = ⨆ L ∈ I, (L ⊓ autI hV (thompsonJ T)) ∧
      ∀ L ∈ I, Nat.card ↥(L ⊓ autI hV (thompsonJ T)) = 4 ∧
        ∃ θ : ↥L ≃* Equiv.Perm (Fin 5), L ⊓ autI hV (thompsonJ T) =
          Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ ⟨x, hx⟩).IsSwap})

@[expose] def E23Statement : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (hV : IsElemAbelian 2 V),
    MinParabolic H T M → SQTKGroup ↥H → CharTwo H → IsTwoReducedIn H V →
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ) → E23Concl H T V hV

@[expose] def E23Nonsolvable : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (hV : IsElemAbelian 2 V),
    MinParabolic H T M → SQTKGroup ↥H → CharTwo H → IsTwoReducedIn H V →
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ) → ¬ Group.IsSolvable H →
    E23Concl H T V hV

@[expose] def E23FourStatement : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ),
    MinParabolic H T M → SQTKGroup ↥H → CharTwo H → IsTwoReducedIn H V →
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ) →
    (∀ C : Subgroup Γ, C ≤ baum T → C ≠ ⊥ → (C.subgroupOf (baum T)).Characteristic →
      ¬ H ≤ Subgroup.normalizer (C : Set Γ)) →
    ∃ L : Subgroup Γ, IsChi0Block H L ∧ H = L ⊔ T ∧ (¬ IsAltType L 3 → L ∈ cComp H)

section Solvable

variable {W : Type*} [CommGroup W]

theorem isL2Natural_of_actsAsNaturalL2 {L : Subgroup (MulAut W)} {C : Subgroup W}
    (h : ActsAsNaturalL2 L (commV L)) (hC : commV L ⊓ C = ⊥) : IsL2Natural L C 1 := by
  obtain ⟨e, φ, hφ⟩ := h
  refine ⟨le_rfl, ZMod 2, inferInstance, inferInstance, by simp, e, φ.toMonoidHom,
    φ.surjective, ?_, fun g u hu => ?_⟩
  · rw [hC, Subgroup.bot_subgroupOf]
    ext u
    simp only [MonoidHom.mem_ker, MulEquiv.coe_toMonoidHom, Subgroup.mem_bot]
    exact ⟨fun hu => φ.injective (by rw [hu, map_one]), fun hu => by rw [hu, map_one]⟩
  · simpa using congrArg Multiplicative.toAdd (hφ g u hu)

theorem inf_sup_le_of_independent {A B C : Subgroup W} (hC : C ⊓ (A ⊔ B) = ⊥)
    (hAB : A ⊓ B = ⊥) : A ⊓ (C ⊔ B) ≤ C := by
  rintro x ⟨hxA, hxCB⟩
  obtain ⟨c, hc, b, hb, rfl⟩ := Subgroup.mem_sup.1 hxCB
  have hc' : c ∈ A ⊔ B := by
    have : c = (c * b) * b⁻¹ := by group
    rw [this]
    exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left hxA) (Subgroup.mem_sup_right (B.inv_mem hb))
  have hc1 : c = 1 := by
    have : c ∈ C ⊓ (A ⊔ B) := ⟨hc, hc'⟩
    rw [hC, Subgroup.mem_bot] at this
    exact this
  rw [hc1, one_mul] at hxA ⊢
  have : b ∈ A ⊓ B := ⟨hxA, hb⟩
  rw [hAB, Subgroup.mem_bot] at this
  rw [this]
  exact C.one_mem

end Solvable

open E2 in
theorem e23Concl_of_isSolvable [Finite Γ] {H T M V : Subgroup Γ} (hV : IsElemAbelian 2 V)
    (h : MinParabolic H T M) (hsolv : Group.IsSolvable H)
    (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set Γ)) :
    E23Concl H T V hV := by
  obtain ⟨hKJ, I, hcard, hJeq, hcomm, hind, htrans, hnat, hsup, hinf, hcind⟩ :=
    E2_3_one_of_isSolvable hV h hsolv hSQT hred hJ
  obtain ⟨hS, hsyl, hSK, -, hcl⟩ := E2_3_two_of_isSolvable hV h hsolv hSQT hred hJ
  have hsolvX : Group.IsSolvable ↥(autI hV H) := isSolvable_autI hV hred.2.1 hsolv
  have hLH : ∀ L ∈ I, L ≤ autI hV H := fun L hL =>
    (le_iSup₂_of_le L hL le_rfl : L ≤ ⨆ L ∈ I, L).trans
      (hJeq.symm.le.trans (autI_mono hV (thompsonJ_le_self H)))
  have hnotA5 : ∀ L ∈ I, ¬ IsA5Module L := by
    rintro L hL ⟨θ, -, -⟩
    apply Equiv.Perm.not_isSolvable_fin_5
    have : Group.IsSolvable ↥L := by
      have := subgroup_solvable_of_solvable ((L.subgroupOf (autI hV H)))
      exact Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe (hLH L hL)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (hLH L hL)).surjective
    exact Group.isSolvable_of_surjective (f := θ.toMonoidHom) θ.surjective
  have hlast : ∀ L ∈ I, commV L ⊓
      (fixV (autI hV (twoResidual H)) ⊔ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L') ≤
        fixV (autI hV (twoResidual H)) := by
    intro L hL
    set F := fun (L'' : Subgroup (MulAut (IntMod V hV))) (_ : L'' ∈ I) => commV L'' with hF
    have hW : commV L ⊔ (⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L') ≤ ⨆ L'' ∈ I, commV L'' :=
      sup_le (le_iSup₂_of_le (f := F) L hL le_rfl)
        (iSup₂_le fun L' hL' => iSup_le fun _ => le_iSup₂_of_le (f := F) L' hL' le_rfl)
    have hC : fixV (autI hV (twoResidual H)) ⊓
        (commV L ⊔ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L') = ⊥ :=
      le_bot_iff.1 ((inf_le_inf_left _ hW).trans hinf.le)
    exact inf_sup_le_of_independent hC (hcind L hL)
  have hCL : ∀ L ∈ I, commV L ⊓ fixV (autI hV (twoResidual H)) = ⊥ := fun L hL =>
    le_bot_iff.1 ((le_inf inf_le_right (inf_le_left.trans
      (le_iSup₂_of_le (f := fun (L'' : Subgroup (MulAut (IntMod V hV))) (_ : L'' ∈ I) =>
        commV L'') L hL le_rfl))).trans hinf.le)
  have hA5 : (∀ L ∈ I, IsA5Module L) → False := by
    intro hA5
    obtain ⟨L, hL⟩ := Finset.card_pos.1 (by omega : 0 < I.card)
    exact hnotA5 L hL (hA5 L hL)
  unfold E23Concl
  exact ⟨hKJ, I, hcard, hJeq, hcomm, hind, htrans,
    fun L hL => Or.inl ⟨1, isL2Natural_of_actsAsNaturalL2 (hnat L hL) (hCL L hL)⟩, hsup, hlast,
    fun _ => ⟨hS, hsyl, hSK, hcl⟩, fun h5 => (hA5 h5).elim⟩

theorem e23Statement_of_nonsolvable (hns : E23Nonsolvable) : E23Statement := by
  intro Γ _ _ H T M V hV h hsqtk hchar hred hJ
  by_cases hsolv : Group.IsSolvable H
  · refine e23Concl_of_isSolvable hV h hsolv (fun p hp hp2 => ?_) hred hJ
    have h1 := hsqtk.1 p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    rwa [← pRank_top_subtype]
  · exact hns Γ H T M V hV h hsqtk hchar hred hJ hsolv

end E2

end CFSG.Quasithin

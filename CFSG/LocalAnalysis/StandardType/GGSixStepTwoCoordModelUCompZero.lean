module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUCompBasic

public section

namespace CFSG.StandardType

namespace CoordSU

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm NsFrameComp CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary Multiplicative

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

local notation "Xe" x:max => ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
  Module.End K (Fin n → K))

theorem lin_ι_apply_of_eq_zero (F : PieceFrame f n K h p A) {β : Fin F.r → ZMod p} {k : Fin F.r}
    (hk : β k = 0) {u : Fin n → K} (hu : u ∈ rng (F.y k)) : lin (F.ι (ofAdd β)) u = u := by
  rw [F.ι_on _ k u hu, toAdd_ofAdd, hk, ZMod.val_zero, pow_zero, lin_one]
  rfl

theorem lin_ι_eq_self_of_supp (F : PieceFrame f n K h p A) {β t : Fin F.r → ZMod p}
    (hsupp : ∀ k, t k ≠ 0 → β k ≠ 0) {v : Fin n → K} (hv : lin (F.ι (ofAdd β)) v = v) :
    lin (F.ι (ofAdd t)) v = v :=
  (F.ι_fix _ v).mpr fun k hk => (F.ι_fix _ v).mp hv k (hsupp k hk)

theorem ι_mem_sb_zero (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) {β s : Fin F.r → ZMod p}
    (hsβ : ∀ k, s k ≠ 0 → β k = 0)
    (hmem : (X - C 1 : K[X]) ∈ primaryFactors (Xe (F.ι (ofAdd β)))) :
    F.ι (ofAdd s) ∈ sb h (F.ι (ofAdd β)) (X - C 1) := by
  have hp := hA.prime
  set x := F.ι (ofAdd β) with hx
  have hxA : x ∈ A := ι_mem F _
  have H := primaryData h hp hA.ne_two (hA.pow x hxA)
  have hsq := H.squarefree
  have hsC := mem_centralizer_of_mem hA hxA (ι_mem F (ofAdd s))
  have hU := toUnitHom_mem_unitaryCentralizer (h := h) hsC
  have htriv : ∀ b ∈ primaryFactors (Xe x), b ≠ X - C 1 →
      ∀ v ∈ primaryComponent (Xe x) b, lin (F.ι (ofAdd s)) v = v := by
    intro b hb hb1 v hv
    refine (F.ι_fix _ v).mpr fun k hk => Submodule.mem_orthogonalBilin.mpr fun u hu => ?_
    have huV : u ∈ primaryComponent (Xe x) (X - C 1) := by
      rw [primaryComponent_X_sub_C_one, LinearMap.mem_ker, LinearMap.sub_apply,
        Module.End.one_apply, sub_eq_zero]
      exact lin_ι_apply_of_eq_zero F (hsβ k hk) hu
    exact orthogonal_of_ne_dualPoly H hmem hb (by rw [dualPoly_X_sub_C_one]; exact hb1) huV hv
  refine mem_specialBlock.mpr ⟨⟨hU, fun b hb hbS v hv => htriv b hb ?_ v hv⟩, hU.2, ?_⟩
  · intro e
    exact hbS (Or.inl e)
  · exact blockDetHom_X_sub_C_one_eq_one hsq hmem htriv (det_lin _ h)

theorem ι_comm_sb_zero (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) {β t : Fin F.r → ZMod p}
    (hsupp : ∀ k, t k ≠ 0 → β k ≠ 0) {g : ↥(unitarySU 2 f K n)}
    (hg : g ∈ sb h (F.ι (ofAdd β)) (X - C 1)) : F.ι (ofAdd t) * g = g * F.ι (ofAdd t) := by
  have hp := hA.prime
  set x := F.ι (ofAdd β) with hx
  have hxA : x ∈ A := ι_mem F _
  have htC := mem_centralizer_of_mem hA hxA (ι_mem F (ofAdd t))
  have hgC : g ∈ Subgroup.centralizer {x} := sb_le_centralizer hg
  have hgtriv := (mem_specialBlock.mp (mem_sb.mp hg)).1.2
  refine mul_comm_of_forall_primaryComponent h hp hA.ne_two (hA.pow x hxA) fun b hb v hv => ?_
  by_cases hb1 : b = X - C 1
  · subst hb1
    have hfix : ∀ w ∈ primaryComponent (Xe x) (X - C 1), lin x w = w := by
      intro w hw
      rw [primaryComponent_X_sub_C_one, LinearMap.mem_ker, LinearMap.sub_apply,
        Module.End.one_apply, sub_eq_zero] at hw
      exact hw
    rw [lin_ι_eq_self_of_supp F hsupp (hfix v hv),
      lin_ι_eq_self_of_supp F hsupp (hfix _ (lin_mem_primaryComponent hgC hv))]
  · have hoff : ∀ w ∈ primaryComponent (Xe x) b, lin g w = w := fun w hw =>
      hgtriv b hb (fun hbS => by
        rcases hbS with hbS | hbS
        · exact hb1 hbS
        · rw [dualPoly_X_sub_C_one] at hbS
          exact hb1 hbS) w hw
    rw [hoff v hv, hoff _ (lin_mem_primaryComponent htC hv)]

theorem exists_pair_of_card_le_two {r : ℕ} (hr : 0 < r) {T : Finset (Fin r)} (hT : T.card ≤ 2) :
    ∃ j j' : Fin r, ∀ i ∈ T, i = j ∨ i = j' := by
  rcases Nat.lt_or_ge T.card 2 with h2 | h2
  · rcases Nat.lt_or_ge T.card 1 with h1 | h1
    · have hT0 : T = ∅ := Finset.card_eq_zero.mp (by omega)
      exact ⟨⟨0, hr⟩, ⟨0, hr⟩, fun i hi => by simp [hT0] at hi⟩
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (by omega : T.card = 1)
      exact ⟨a, a, fun i hi => by rw [ha, Finset.mem_singleton] at hi; exact Or.inl hi⟩
  · obtain ⟨a, b, -, hab⟩ := Finset.card_eq_two.mp (by omega : T.card = 2)
    exact ⟨a, b, fun i hi => by
      rw [hab, Finset.mem_insert, Finset.mem_singleton] at hi
      exact hi⟩

variable {G : Type} [Group G] {φ : ↥(unitarySU 2 f K n) →* G}

theorem card_supp_le_two [Finite G] (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    (hinj : Function.Injective (φ.comp F.ι)) {β : Fin F.r → ZMod p} {L₁ : Subgroup G}
    (hL₁ : L₁ = (sb h (F.ι (ofAdd β)) (X - C 1)).map φ)
    (hcard : Nat.card ((φ.comp F.ι).range ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤
      p ^ 2) : (supp β).card ≤ 2 := by
  classical
  have hp := hA.prime
  set e : (supp β → ZMod p) → (Fin F.r → ZMod p) :=
    fun t k => if hk : k ∈ supp β then t ⟨k, hk⟩ else 0 with he
  have he_inj : Function.Injective e := by
    intro t t' htt'
    funext ⟨k, hk⟩
    have := congrFun htt' k
    simpa [he, hk] using this
  have hsupp : ∀ t k, e t k ≠ 0 → β k ≠ 0 := by
    intro t k hk
    by_cases hks : k ∈ supp β
    · exact mem_supp.mp hks
    · exact absurd (by simp [he, hks]) hk
  have hle := card_le_card_inf_centralizer (L₁ := L₁) hinj e he_inj fun t => by
    rw [hL₁]
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    rw [MonoidHom.comp_apply, ← map_mul, ← map_mul, ι_comm_sb_zero hA F (hsupp t) hg]
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_finsetCard] at hle
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (hle.trans hcard)

theorem comp_zero [Finite G] (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) (hr : 0 < F.r)
    (hinj : Function.Injective (φ.comp F.ι)) {β : Fin F.r → ZMod p} {L₁ : Subgroup G}
    (hL₁ : L₁ = (sb h (F.ι (ofAdd β)) (X - C 1)).map φ)
    (hmem : (X - C 1 : K[X]) ∈ primaryFactors (Xe (F.ι (ofAdd β))))
    (hcard : Nat.card ((φ.comp F.ι).range ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤
      p ^ 2) :
    ∃ j j' : Fin F.r, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
      ∀ s : Fin F.r → ZMod p, s j = 0 → s j' = 0 → φ (F.ι (ofAdd s)) ∈ L₁ := by
  obtain ⟨j, j', hjj⟩ := exists_pair_of_card_le_two hr (card_supp_le_two hA F hinj hL₁ hcard)
  have hβ : ∀ i, β i ≠ 0 → i = j ∨ i = j' := fun i hi => hjj i (mem_supp.mpr hi)
  refine ⟨j, j', fun i hij hij' => ?_, fun s hsj hsj' => ?_⟩
  · by_contra hne
    rcases hβ i hne with h1 | h1
    · exact hij h1
    · exact hij' h1
  · rw [hL₁]
    refine Subgroup.mem_map_of_mem _ (ι_mem_sb_zero hA F (fun k hk => ?_) hmem)
    by_contra hne
    rcases hβ k hne with h1 | h1
    · exact hk (h1 ▸ hsj)
    · exact hk (h1 ▸ hsj')

end CoordSU

end CFSG.StandardType

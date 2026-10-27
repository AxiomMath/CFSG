module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepJoint
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepSide
public import CFSG.LocalAnalysis.StandardType.GGRCCycleBalanced
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepSmallClassify
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem lr6Group_map_conj {p : ℕ} [Fact p.Prime]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {J : Type}
    (r : J → (V ≃ₗ[ZMod p] V)) (t u : V ≃ₗ[ZMod p] V)
    (hu : ∀ j, u * r j * u⁻¹ = r j) :
    (lr6Group r t).map (ggLinConj u).toMonoidHom =
      lr6Group r (u * t * u⁻¹) := by
  have hc : ∀ v : V ≃ₗ[ZMod p] V, ggLinConj u v = u * v * u⁻¹ := by
    intro v
    ext w
    rfl
  rw [lr6Group, lr6Group, MonoidHom.map_closure]
  congr 1
  rw [Set.image_union]
  congr 1
  · ext v
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, (hc (r j)).trans (hu j) |>.symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨r j, Set.mem_range_self j, (hc (r j)).trans (hu j)⟩
  · change ((ggLinConj u) '' {t} : Set (V ≃ₗ[ZMod p] V)) = {u * t * u⁻¹}
    simp only [Set.image_singleton, hc]

theorem ggJoint_oneNode_parabolic_conj {p : ℕ} [Fact p.Prime]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {J : Type}
    {r : J → (V ≃ₗ[ZMod p] V)} {t u : V ≃ₗ[ZMod p] V}
    (hu : ∀ j, u * r j * u⁻¹ = r j)
    {M : CoxeterMatrix (Option J)}
    (f : M.Group ≃* ↥(lr6Group r t))
    (hf : ∀ o : Option J, (f (M.simple o) : V ≃ₗ[ZMod p] V) = o.elim t r) :
    ∃ f' : M.Group ≃* ↥(lr6Group r (u * t * u⁻¹)),
      ∀ o : Option J, (f' (M.simple o) : V ≃ₗ[ZMod p] V) =
        o.elim (u * t * u⁻¹) r := by
  let e : ↥(lr6Group r t) ≃* ↥(lr6Group r (u * t * u⁻¹)) :=
    (Subgroup.equivMapOfInjective (lr6Group r t) (ggLinConj u).toMonoidHom
      (ggLinConj u).injective).trans (MulEquiv.subgroupCongr (lr6Group_map_conj r t u hu))
  refine ⟨f.trans e, ?_⟩
  intro o
  change ggLinConj u (f (M.simple o) : V ≃ₗ[ZMod p] V) = _
  rw [hf]
  cases o with
  | none => ext w; rfl
  | some j =>
      have he : ggLinConj u (r j) = u * r j * u⁻¹ := by ext w; rfl
      exact he.trans (hu j)

theorem ggJoint_oneNode_pairing_conj {p : ℕ} [Fact p.Prime]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {J : Type}
    {h : J → V} {α : J → Module.Dual (ZMod p) V}
    {ht : V} {β : Module.Dual (ZMod p) V} {C : Matrix (Option J) (Option J) ℤ}
    (hC : ∀ i j : Option J, (C i j : ZMod p) =
      (i.elim β α) (j.elim ht h))
    (u : V ≃ₗ[ZMod p] V) (hh : ∀ j, u (h j) = h j)
    (hα : ∀ j w, α j (u w) = α j w) :
    ∀ i j : Option J, (C i j : ZMod p) =
      (i.elim (β.comp u.symm.toLinearMap) α) (j.elim (u ht) h) := by
  have hh' : ∀ j, u.symm (h j) = h j := by
    intro j
    apply u.injective
    rw [LinearEquiv.apply_symm_apply, hh]
  intro i j
  rw [hC]
  cases i <;> cases j <;> simp only [Option.elim, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hh', hα]

theorem ggJoint_exists_added_not_mem (hExcl : LR6SmallRankExcl)
    (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G]
    {p N : ℕ} [Fact p.Prime] (hcell : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7))
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K Y : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} (hb : b₁ ≠ b₂)
    {Λa : Type} [Fintype Λa] [DecidableEq Λa] (hΛa : Nat.card Λa = 2)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)
      ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    (e : Fin (N - 1) ≃ Λ) (hML : ML = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCL : GGIntCartan ML CL) (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hconn : GGDeletedConnected2 ML b₁ b₂)
    (hJM : ∀ i j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂},
      MK.M (Sum.inl i) (Sum.inl j) = ML.M i.1 j.1)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ ⊕ Λa → MulAut ↥Bs}
    {h : Λ ⊕ Λa → V} {α : Λ ⊕ Λa → Module.Dual (ZMod p) V}
    (hlin : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection p (φ o))
    (hpairL : ∀ i j, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p))
    (hpairK : ∀ i j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (i.map Subtype.val id) (h (j.map Subtype.val id)) = (CK i j : ZMod p))
    (hfY : ∃ f : MK.Group ≃* ↥(ggAutomizer Y Bs),
      ∀ o, (f (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id))
    (hAY : ggAutomizer Y Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hφtop : ∀ o, φ o ∈ ggAutomizer ⊤ Bs)
    (hJL : ∀ j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}, φ (Sum.inl j) ∈ ggAutomizer L Bs)
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)))
    {z : V} (F : GGIndepAFrame p N (fun i => h (Sum.inl (e i)))
      (fun i => α (Sum.inl (e i))) z)
    (hmove : ∃ a : Λa, α (Sum.inr a) z ≠ 0) :
    ∃ a : Λa, h (Sum.inr a) ∉
      Submodule.span (ZMod p) (Set.range fun i => h (Sum.inl i)) := by
  classical
  have hp5 : 5 ≤ p := by rcases hcell with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  have hN5 : 5 ≤ N := by rcases hcell with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let H : Submodule (ZMod p) V :=
    Submodule.span (ZMod p) (Set.range fun i : Λ => h (Sum.inl i))
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (Sum.inl (e i)))
  let hf : Fin (N - 1) → V := fun i => h (Sum.inl (e i))
  let af : Fin (N - 1) → Module.Dual (ZMod p) V := fun i => α (Sum.inl (e i))
  let A : Subgroup (MulAut ↥Bs) := Subgroup.closure (Set.range φ)
  have hAtop : A ≤ ggAutomizer ⊤ Bs := by
    rw [Subgroup.closure_le]
    rintro _ ⟨o, rfl⟩
    exact hφtop o
  have hφA : ∀ o, φ o ∈ A := fun o => Subgroup.subset_closure (Set.mem_range_self o)
  have hr : ∀ i w, r i w = w - af i w • hf i := fun i w => hlin (Sum.inl (e i)) w
  have hVN : Module.finrank (ZMod p) V ≤ N := ggIndepFrame_finrank_le (by omega) F
  have hrange : Set.range hf = Set.range (fun i : Λ => h (Sum.inl i)) :=
    e.surjective.range_comp (fun i : Λ => h (Sum.inl i))
  have hαj : ∀ j : Λ, α (Sum.inl j) (h (Sum.inl j)) = 2 := by
    intro j
    rw [hpairL, hCL.1]
    norm_num
  have hαa : ∀ a : Λa, α (Sum.inr a) (h (Sum.inr a)) = 2 := by
    intro a
    simpa using (hpairK (Sum.inr a) (Sum.inr a)).trans (by rw [hCK.1]; norm_num)
  have hclose : ∀ (t : MulAut ↥Bs) (htA : t ∈ A) (ht : V)
      (β : Module.Dual (ZMod p) V),
      (∀ w, ggLin (p := p) ι t w = w - β w • ht) → β ht = 2 → β z ≠ 0 → ht ∈ H →
      ∀ (S : Finset (Fin (N - 1))) (M : CoxeterMatrix (Option ↥S))
        (C : Matrix (Option ↥S) (Option ↥S) ℤ),
      (∀ i, i ∈ S ↔ e i ≠ b₁ ∧ e i ≠ b₂) →
      (∃ s ≤ 2, ∀ i : Fin (N - 1), i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + (N - 3)) →
      GGIsWeylMatrix M → GGIntCartan M C →
      (∀ i j : Option ↥S, (C i j : ZMod p) =
        (i.elim β fun a => af a) (j.elim ht fun b => hf b)) →
      (∃ c : ↥S, ∀ j : ↥S, C none (some j) ≠ 0 ↔ j = c) →
      (∃ f : M.Group ≃* ↥(lr6Group (fun j : ↥S => r j) (ggLin (p := p) ι t)),
        ∀ o, (f (M.simple o) : V ≃ₗ[ZMod p] V) = o.elim (ggLin (p := p) ι t) fun j => r j) →
      False := by
    intro t htA ht β htl hβ hβz hht S M C hS hSint hW hC hpair hattach hiso
    have hRA : lr6Group r (ggLin (p := p) ι t) ≤ A.map (ggLin (p := p) ι) := by
      rw [lr6Group, Subgroup.closure_le]
      rintro _ (⟨i, rfl⟩ | rfl)
      · exact Subgroup.mem_map.mpr ⟨φ (Sum.inl (e i)), hφA _, rfl⟩
      · exact Subgroup.mem_map.mpr ⟨t, htA, rfl⟩
    have htri : LR6JTriangleBalanced S hf af r (lr6Group r (ggLin (p := p) ι t)) := by
      intro j hj j' hj' hne ψ hψ ht' β' htl' hβ' hnc
      obtain ⟨ψ', hψ'A, hψ'eq⟩ := Subgroup.mem_map.mp (hRA hψ)
      have htl'' : ∀ w, ggLin (p := p) ι
          (ψ' * φ (Sum.inl (e j)) * ψ'⁻¹) w = w - β' w • ht' := by
        intro w
        have heq : ggLin (p := p) ι (ψ' * φ (Sum.inl (e j)) * ψ'⁻¹) = ψ * r j * ψ⁻¹ := by
          rw [map_mul, map_mul, map_inv, hψ'eq]
        rw [heq]
        exact htl' w
      have hnc' : ψ' * φ (Sum.inl (e j)) * ψ'⁻¹ * φ (Sum.inl (e j')) ≠
          φ (Sum.inl (e j')) * (ψ' * φ (Sum.inl (e j)) * ψ'⁻¹) := by
        intro heq
        apply hnc
        have heq' := congrArg (ggLin (p := p) ι) heq
        simpa only [map_mul, map_inv, hψ'eq, r] using heq'
      exact ggRC_cycleBalanced_two hJr hPump hLB hSP hp5 hH hlin (hαj _) (hαj _)
        hφtop hJL hJ ((hS j).mp hj) ((hS j').mp hj') hψ'A hβ' htl'' hnc'
    have hnt := ggIndep_nt hH.2.2.2.1 hAtop e
      (φ := fun i : Λ => φ (Sum.inl i)) (fun i => hφA _) htA (ι := ι)
    have hht' : ht ∈ Submodule.span (ZMod p) (Set.range hf) := by
      simpa only [hrange] using hht
    exact hExcl p N hcell V hVN hf af z r ht β (ggLin (p := p) ι t)
      F hr htl hβ hβz hht'
      ⟨S, M, C, hSint, hW, hC, hpair, hattach, htri, hiso⟩ hnt
  by_contra hnot
  push Not at hnot
  change ∀ a : Λa, h (Sum.inr a) ∈ H at hnot
  obtain ⟨a, ha⟩ := hmove
  haveI : Nonempty Λa := ⟨a⟩
  haveI : Nonempty {i : Λ // i ≠ b₁ ∧ i ≠ b₂} := by
    obtain ⟨s, hs, hS⟩ := ggChainA_deleted_interval (by omega) e b₁ b₂ hb
      (by rwa [← hML])
    let j : Fin (N - 1) := ⟨s, by omega⟩
    exact ⟨⟨e j, (hS j).mpr ⟨by simp [j], by simp [j]; omega⟩⟩⟩
  have hselected : ∀ b : Λa, (∃ j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂},
      MK.M (Sum.inr b) (Sum.inl j) ≠ 2) → α (Sum.inr b) z ≠ 0 → False := by
    intro b hattach hbz
    obtain ⟨S, M, C, hS, hSint, hW, hC, hpair, hattach', hiso⟩ :=
      ggJoint_oneNode_sideClause_selected (p := p) (N := N) (Bs := Bs) (K := Y)
        hb b hN5 e hML hconn hWMK hCK hJM hattach hlin hpairK hfY hAY
    exact hclose (φ (Sum.inr b)) (hφA _) (h (Sum.inr b)) (α (Sum.inr b))
      (hlin _) (hαa b) hbz (hnot b) S M C hS hSint hW hC hpair hattach' hiso
  by_cases hattachA : ∃ j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂},
      MK.M (Sum.inr a) (Sum.inl j) ≠ 2
  · exact hselected a hattachA ha
  have hnoA : ∀ j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, MK.M (Sum.inr a) (Sum.inl j) = 2 := by
    simpa using hattachA
  obtain ⟨b, j₀, hbJ⟩ := ggJoint_exists_attached_added_node hWMK
  have hab : a ≠ b := by rintro rfl; exact hbJ (hnoA j₀)
  have hcover : ∀ c : Λa, c = a ∨ c = b := by
    intro c
    by_contra hc
    have hca : c ≠ a := fun heq => hc (Or.inl heq)
    have hcb : c ≠ b := fun heq => hc (Or.inr heq)
    have h3 : 3 ≤ Fintype.card Λa := by
      calc 3 = ({a, b, c} : Finset Λa).card := by simp [hab, hca, hcb, Ne.symm hca, Ne.symm hcb]
        _ ≤ Fintype.card Λa := Finset.card_le_univ _
    rw [← Nat.card_eq_fintype_card, hΛa] at h3
    omega
  have habond : MK.M (Sum.inr a) (Sum.inr b) ≠ 2 := by
    rcases Relation.ReflTransGen.cases_head
        (ggRC_weyl_connected hWMK (Sum.inr a) (Sum.inl j₀)) with heq | ⟨c, hc, _⟩
    · exact (Sum.inr_ne_inl heq).elim
    · cases c with
      | inl j => exact (hc.2 (hnoA j)).elim
      | inr c =>
          rcases hcover c with rfl | rfl
          · exact (hc.1 rfl).elim
          · exact hc.2
  by_cases hbz : α (Sum.inr b) z = 0
  · let u : V ≃ₗ[ZMod p] V := ggLin (p := p) ι (φ (Sum.inr a))
    let t : MulAut ↥Bs := φ (Sum.inr a) * φ (Sum.inr b) * (φ (Sum.inr a))⁻¹
    let ht : V := u (h (Sum.inr b))
    let β : Module.Dual (ZMod p) V := (α (Sum.inr b)).comp u.symm.toLinearMap
    have hinv : (φ (Sum.inr a))⁻¹ = φ (Sum.inr a) :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using (hrefl (Sum.inr a)).1)
    have huinv : u.symm = u := by
      change (ggLin (p := p) ι (φ (Sum.inr a)))⁻¹ = _
      rw [← map_inv, hinv]
    have hzero : ∀ j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂},
        α (Sum.inr a) (h (Sum.inl j)) = 0 ∧ α (Sum.inl j) (h (Sum.inr a)) = 0 := by
      intro j
      have hc : CK (Sum.inr a) (Sum.inl j) = 0 :=
        (l05nBL_cartan_eq_zero_iff hCK Sum.inr_ne_inl).mpr (hnoA j)
      have hc' : CK (Sum.inl j) (Sum.inr a) = 0 :=
        hCK.eq_zero_symm Sum.inl_ne_inr hc
      constructor
      · have heq := hpairK (Sum.inr a) (Sum.inl j)
        simpa only [Sum.map_inr, Sum.map_inl, id_eq, hc, Int.cast_zero] using heq
      · have heq := hpairK (Sum.inl j) (Sum.inr a)
        simpa only [Sum.map_inr, Sum.map_inl, id_eq, hc', Int.cast_zero] using heq
    have hh : ∀ j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, u (h (Sum.inl j)) = h (Sum.inl j) := by
      intro j
      rw [show u = ggLin (p := p) ι (φ (Sum.inr a)) from rfl, hlin, (hzero j).1,
        zero_smul, sub_zero]
    have haf : ∀ j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, ∀ w, α (Sum.inl j) (u w) = α (Sum.inl j) w := by
      intro j w
      rw [show u = ggLin (p := p) ι (φ (Sum.inr a)) from rfl, hlin, map_sub, map_smul,
        (hzero j).2, smul_zero, sub_zero]
    have hβz : β z ≠ 0 := by
      have hba : α (Sum.inr b) (h (Sum.inr a)) ≠ 0 := by
        have heq : α (Sum.inr b) (h (Sum.inr a)) =
            (CK (Sum.inr b) (Sum.inr a) : ZMod p) := by
          simpa only [Sum.map_inr, id_eq] using hpairK (Sum.inr b) (Sum.inr a)
        rw [heq]
        exact (hCK.cast_pair_ne_zero_of_bond hp5
          (show Sum.inr a ≠ Sum.inr b from fun h => hab (Sum.inr.inj h)) habond).2
      change α (Sum.inr b) (u.symm z) ≠ 0
      rw [huinv, show u = ggLin (p := p) ι (φ (Sum.inr a)) from rfl, hlin,
        map_sub, map_smul, hbz, smul_eq_mul, zero_sub]
      exact neg_ne_zero.mpr (mul_ne_zero ha hba)
    have htH : ht ∈ H := by
      change u (h (Sum.inr b)) ∈ H
      rw [show u = ggLin (p := p) ι (φ (Sum.inr a)) from rfl, hlin]
      exact H.sub_mem (hnot b) (H.smul_mem _ (hnot a))
    have hβht : β ht = 2 := by
      change α (Sum.inr b) (u.symm (u (h (Sum.inr b)))) = 2
      rw [LinearEquiv.symm_apply_apply, hαa]
    have htl : ∀ w, ggLin (p := p) ι t w = w - β w • ht := by
      intro w
      rw [show t = φ (Sum.inr a) * φ (Sum.inr b) * (φ (Sum.inr a))⁻¹ from rfl,
        map_mul, map_mul, map_inv]
      change u (ggLin (p := p) ι (φ (Sum.inr b)) (u.symm w)) = _
      rw [hlin (Sum.inr b), map_sub, map_smul, LinearEquiv.apply_symm_apply]
      rfl
    obtain ⟨S, M, C, hS, hSint, hW, hC, hpair, hattach, hiso⟩ :=
      ggJoint_oneNode_sideClause_selected (p := p) (N := N) (Bs := Bs) (K := Y)
        hb b hN5 e hML hconn hWMK hCK hJM ⟨j₀, hbJ⟩ hlin hpairK hfY hAY
    have hhS : ∀ j : ↥S, u (hf j) = hf j := fun j => hh ⟨e j, (hS j).mp j.2⟩
    have haS : ∀ j : ↥S, ∀ w, af j (u w) = af j w := fun j => haf ⟨e j, (hS j).mp j.2⟩
    have huS : ∀ j : ↥S, u * r j * u⁻¹ = r j := by
      intro j
      ext w
      change u (r j (u.symm w)) = r j w
      rw [hr, map_sub, map_smul, hhS, LinearEquiv.apply_symm_apply, hr]
      have hhα := haS j (u.symm w)
      rw [LinearEquiv.apply_symm_apply] at hhα
      rw [← hhα]
    have hpair' := ggJoint_oneNode_pairing_conj hpair u hhS haS
    obtain ⟨f, hf'⟩ := hiso
    have hiso' := ggJoint_oneNode_parabolic_conj huS f hf'
    have heq : ggLin (p := p) ι t = u * ggLin (p := p) ι (φ (Sum.inr b)) * u⁻¹ := by
      rw [show t = φ (Sum.inr a) * φ (Sum.inr b) * (φ (Sum.inr a))⁻¹ from rfl,
        map_mul, map_mul, map_inv]
    rw [← heq] at hiso'
    exact hclose t (A.mul_mem (A.mul_mem (hφA _) (hφA _)) (A.inv_mem (hφA _))) ht β
      htl hβht hβz htH S M C hS hSint hW hC hpair' hattach hiso'
  · exact hselected b ⟨j₀, hbJ⟩ hbz

theorem ggJoint_weyl_small_two (hUse : ZS.UseInput) (hExcl : LR6SmallRankExcl)
    (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G]
    {p N : ℕ} [Fact p.Prime] (hcell : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7))
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X Y : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ} (hb : b₁ ≠ b₂)
    {Λa : Type} [Fintype Λa] [DecidableEq Λa] (hΛa : Nat.card Λa = 2)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)}
    {CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa)
      ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ}
    (e : Fin (N - 1) ≃ Λ) (hML : ML = (CoxeterMatrix.A (N - 1)).reindex e)
    (hWML : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    (hWMK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hconn : GGDeletedConnected2 ML b₁ b₂)
    (hJM : ∀ i j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂},
      MK.M (Sum.inl i) (Sum.inl j) = ML.M i.1 j.1)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ ⊕ Λa → MulAut ↥Bs}
    {h : Λ ⊕ Λa → V} {α : Λ ⊕ Λa → Module.Dual (ZMod p) V}
    (hlin : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection p (φ o))
    (hpairL : ∀ i j, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod p))
    (hpairK : ∀ i j : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (i.map Subtype.val id) (h (j.map Subtype.val id)) = (CK i j : ZMod p))
    (hfY : ∃ f : MK.Group ≃* ↥(ggAutomizer Y Bs),
      ∀ o, (f (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id))
    (hAX : ggAutomizer X Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hAY : ggAutomizer Y Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hJL : ∀ j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}, φ (Sum.inl j) ∈ ggAutomizer L Bs)
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)))
    {z : G} (hz : z ∈ Bs)
    (F : GGIndepAFrame p N (fun i => h (Sum.inl (e i)))
      (fun i => α (Sum.inl (e i))) (ι (Additive.ofMul ⟨z, hz⟩)))
    (hmove : ∃ t ∈ ggAutomizer Y Bs, GGIsReflection p t ∧ t ⟨z, hz⟩ ≠ ⟨z, hz⟩)
    (hstab : Nat.card ↥((ggAutomizer X Bs ⊔ ggAutomizer Y Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz⟩ : ↥Bs)) ≤
        (p - 1) * 6 * Nat.card ↥(ggAutomizer X Bs))
    (hpm1 : GGIndepPm1 p N ι (ggAutomizer X Bs ⊔ ggAutomizer Y Bs)) :
    GGWeylReflectionGroup p (ggAutomizer X Bs ⊔ ggAutomizer Y Bs) := by
  classical
  have hp5 : 5 ≤ p := by rcases hcell with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  have hN5 : 5 ≤ N := by rcases hcell with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
  have hpN : N = p := by rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  let A : Subgroup (MulAut ↥Bs) := ggAutomizer X Bs ⊔ ggAutomizer Y Bs
  have hA : A = Subgroup.closure (Set.range φ) := by
    apply le_antisymm
    · apply sup_le
      · rw [hAX]
        exact Subgroup.closure_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl i, rfl⟩)
      · rw [hAY]
        exact Subgroup.closure_mono (by
          rintro _ (⟨j, rfl⟩ | ⟨a, rfl⟩)
          · exact ⟨Sum.inl j, rfl⟩
          · exact ⟨Sum.inr a, rfl⟩)
    · rw [Subgroup.closure_le]
      rintro _ ⟨o, rfl⟩
      cases o with
      | inl i => exact Subgroup.mem_sup_left (hAX ▸ Subgroup.subset_closure ⟨i, rfl⟩)
      | inr a => exact Subgroup.mem_sup_right (hAY ▸ Subgroup.subset_closure (Or.inr ⟨a, rfl⟩))
  have hAtop : A ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  have hφA : ∀ o, φ o ∈ A := fun o => hA ▸ Subgroup.subset_closure (Set.mem_range_self o)
  have hφtop : ∀ o, φ o ∈ ggAutomizer ⊤ Bs := fun o => hAtop (hφA o)
  have hmove' : ∃ a : Λa, α (Sum.inr a) (ι (Additive.ofMul ⟨z, hz⟩)) ≠ 0 := by
    by_contra hno
    push Not at hno
    have hfix : ggAutomizer Y Bs ≤ MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz⟩ : ↥Bs) := by
      rw [hAY, Subgroup.closure_le]
      rintro _ (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · change φ (Sum.inl j.1) ∈ MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz⟩ : ↥Bs)
        rw [MulAction.mem_stabilizer_iff]
        apply (ggLin_fix_iff (p := p) ι _ ⟨z, hz⟩).mpr
        rw [hlin, show α (Sum.inl j.1) (ι (Additive.ofMul ⟨z, hz⟩)) = 0 from by
          simpa using F.x_ker (e.symm j.1), zero_smul, sub_zero]
      · change φ (Sum.inr a) ∈ MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz⟩ : ↥Bs)
        rw [MulAction.mem_stabilizer_iff]
        apply (ggLin_fix_iff (p := p) ι _ ⟨z, hz⟩).mpr
        rw [hlin, hno, zero_smul, sub_zero]
    obtain ⟨t, ht, _, htz⟩ := hmove
    exact htz (MulAction.mem_stabilizer_iff.mp (hfix ht))
  haveI : Nonempty {i : Λ // i ≠ b₁ ∧ i ≠ b₂} := by
    obtain ⟨s, hs, hS⟩ := ggChainA_deleted_interval (by omega) e b₁ b₂ hb
      (by rwa [← hML])
    let j : Fin (N - 1) := ⟨s, by omega⟩
    exact ⟨⟨e j, (hS j).mpr ⟨by simp [j], by simp [j]; omega⟩⟩⟩
  have ha := ggJoint_exists_added_not_mem hExcl hJr hPump hLB hSP hcell hH hb hΛa e hML
    hCL hWMK hCK hconn hJM hlin hrefl hpairL hpairK hfY hAY hφtop hJL hJ F hmove'
  let g : Λ ⊕ Λa → (V ≃ₗ[ZMod p] V) := fun o => ggLin (p := p) ι (φ o)
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  obtain ⟨hVdim, hirr⟩ := ggJoint_absIrred_of_added_not_mem hp5 (by omega) hWML hCL hWMK
    hCK e g h α hlin hpairL hpairK F hmove' ha
  have hmap : A.map (ggLin (p := p) ι) = Subgroup.closure (Set.range g) := by
    rw [hA, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [← hmap] at hirr
  have hgen : ZS.ReflGen p (A.map (ggLin (p := p) ι)) := by
    change A.map (ggLin (p := p) ι) = Subgroup.closure
      {t | t ∈ A.map (ggLin (p := p) ι) ∧ ZS.IsRefl p t}
    apply le_antisymm
    · conv_lhs => rw [hmap]
      apply Subgroup.closure_mono
      rintro _ ⟨o, rfl⟩
      exact ⟨Subgroup.mem_map.mpr ⟨φ o, hφA o, rfl⟩,
        (ggRC_isReflection_iff_linRefl ι (φ o)).mp (hrefl o)⟩
    · rw [Subgroup.closure_le]
      exact fun _ ht => ht.1
  have hcardAX : Nat.card ↥(ggAutomizer X Bs) ≤ Nat.factorial N :=
    ggIndep_card_A1 (by omega) hN5 hz ι (fun i w => hlin (Sum.inl i) w) hAX e F
  have hcardBs : Nat.card ↥Bs = p ^ N := by
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = p ^ Module.finrank (ZMod p) V := (FiniteField.pow_finrank_eq_natCard p V).symm
      _ = p ^ N := by rw [hVdim]
  have hcard : Nat.card ↥(A.map (ggLin (p := p) ι)) ≤ p ^ N * (6 * (p - 1) * Nat.factorial N) := by
    calc Nat.card ↥(A.map (ggLin (p := p) ι)) = Nat.card ↥A :=
          (Nat.card_congr (Subgroup.equivMapOfInjective A (ggLin (p := p) ι)
            (ggLin_injective ι)).toEquiv).symm
      _ ≤ Nat.card ↥Bs * ((p - 1) * 6 * Nat.card ↥(ggAutomizer X Bs)) :=
          ggIndep_card_join_le A ⟨z, hz⟩ hstab
      _ ≤ p ^ N * ((p - 1) * 6 * Nat.factorial N) := by
          rw [hcardBs]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hcardAX)
      _ = p ^ N * (6 * (p - 1) * Nat.factorial N) := by ring
  have hlinW : ZS.LinWeyl p (A.map (ggLin (p := p) ι)) :=
    ZS.linWeyl_of_smallDim_p5_p7 hUse (by rcases hcell with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h])
      (hVdim.trans hpN) _ hirr hgen (by
        intro g hg htv
        obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hg
        have htInd : t ∈ ggInduced ⊤ Bs := by
          have hh := hAtop ht
          rwa [ggAutomizer_eq] at hh
        exact hH.2.2.2.1 t htInd (ggRC_isTransvection_of_lin ι t htv))
      (by simpa only [hpN] using hcard)
      (by cases hpN; exact hpm1 hirr)
  exact ggRC_weylReflGroup_of_linWeyl ι A hlinW

end CFSG.StandardType

end

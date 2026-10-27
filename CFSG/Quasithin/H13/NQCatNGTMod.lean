module

public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.Quasithin.H13.NQCat.NGT

open CFSG.Quasithin

section Sec

variable {V : Type*} [CommGroup V] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {L : Subgroup (MulAut V)} {U Z : Subgroup V}
  {π : ↥Γ →* ↥L}

@[expose] noncomputable def natSecEquiv (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    ↥(FFModel.nat Γ).sec ⧸ (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec ≃*
      Multiplicative (ι → K) where
  toFun := QuotientGroup.lift _ (FFModel.nat Γ).sec.subtype fun x hx => hx
  invFun x := QuotientGroup.mk ⟨x, Subgroup.mem_top x⟩
  left_inv y := by
    induction y using QuotientGroup.induction_on with
    | H m => rfl
  right_inv x := rfl
  map_mul' := map_mul _

theorem exists_natMap (h : (FFModel.nat Γ).RealizesVia L U Z π) :
    ∃ β' : ↥U →* Multiplicative (ι → K), Function.Surjective β' ∧
      (∀ u : ↥U, β' u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (γ : Γ) (u : ↥U) (hu : ((π γ : L) : MulAut V) (u : V) ∈ U),
        β' ⟨((π γ : L) : MulAut V) (u : V), hu⟩ =
          Multiplicative.ofAdd (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec
            (Multiplicative.toAdd (β' u))) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  refine ⟨(natSecEquiv Γ).toMonoidHom.comp β, (natSecEquiv Γ).surjective.comp hβs,
    fun u => ?_, fun γ u hu => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hβk]
  · obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have h1 := hβe γ u m hu (Subgroup.mem_top _) hm.symm
    change natSecEquiv Γ (β ⟨_, hu⟩) = Multiplicative.ofAdd
      (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec
        (Multiplicative.toAdd (natSecEquiv Γ (β u))))
    rw [← hm]
    exact (congrArg (natSecEquiv Γ) h1).trans rfl

theorem exists_sec_of_inv [Finite V] (h : (FFModel.nat Γ).RealizesVia L U Z π)
    (Q : Subgroup (MulAut V)) {W : Subgroup V} (hZW : Z ≤ W) (hWU : W ≤ U)
    (hinv : ∀ q ∈ Q, ∀ w ∈ W, (q : MulAut V) w ∈ W) :
    ∃ S : AddSubgroup (ι → K), Nat.card W = Nat.card Z * Nat.card S ∧
      (∀ γ : Γ, ((π γ : L) : MulAut V) ∈ Q → ∀ v ∈ S,
        ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈ S) ∧
      (S = ⊥ → W = Z) := by
  classical
  have hZU : Z ≤ U := h.2.1
  have hHU : ∀ l : ↥L, ∀ u ∈ U, (l : MulAut V) u ∈ U := h.2.2.2.1
  obtain ⟨β', -, hβ'k, hβ'e⟩ := exists_natMap h
  set T : Subgroup (Multiplicative (ι → K)) := (W.subgroupOf U).map β' with hT
  refine ⟨Subgroup.toAddSubgroup' T, ?_, ?_, fun hS => ?_⟩
  ·
    have hcard : Nat.card (W.subgroupOf U) = Nat.card T *
        Nat.card ((β'.domRestrict (W.subgroupOf U)).ker) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (β'.domRestrict (W.subgroupOf U)).ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
        MonoidHom.domRestrict_range, hT]
    have hker : Nat.card ((β'.domRestrict (W.subgroupOf U)).ker) = Nat.card Z := by
      refine Nat.card_congr
        { toFun := fun x => ⟨((x : W.subgroupOf U) : U), (hβ'k _).1 x.2⟩
          invFun := fun z => ⟨⟨⟨z, hZU z.2⟩, hZW z.2⟩, (hβ'k ⟨z, hZU z.2⟩).2 z.2⟩
          left_inv := fun x => by ext; rfl
          right_inv := fun z => by ext; rfl }
    have hW : Nat.card (W.subgroupOf U) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWU).toEquiv
    have hT' : Nat.card (Subgroup.toAddSubgroup' T) = Nat.card T :=
      Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd fun _ => Iff.rfl)
    rw [← hW, hcard, hker, hT', mul_comm]
  ·
    intro γ hγ v hv
    obtain ⟨u, hu, huv⟩ := hv
    have hu' : ((π γ : L) : MulAut V) (u : V) ∈ U := hHU (π γ) u u.2
    refine ⟨⟨_, hu'⟩, hinv _ hγ u hu, ?_⟩
    rw [hβ'e γ u hu', huv]
    rfl
  ·
    refine le_antisymm (fun w hw => ?_) hZW
    have h0 : Multiplicative.toAdd (β' ⟨w, hWU hw⟩) ∈ Subgroup.toAddSubgroup' T :=
      ⟨⟨w, hWU hw⟩, hw, rfl⟩
    rw [hS, AddSubgroup.mem_bot] at h0
    exact (hβ'k _).1 (congrArg Multiplicative.ofAdd h0)

theorem exists_inv_of_sec [Finite V] (h : (FFModel.nat Γ).RealizesVia L U Z π)
    (Q : Subgroup (MulAut V)) (hQL : Q ≤ L) (S : AddSubgroup (ι → K))
    (hS : ∀ γ : Γ, ((π γ : L) : MulAut V) ∈ Q → ∀ v ∈ S,
      ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈ S) :
    ∃ W : Subgroup V, Z ≤ W ∧ W ≤ U ∧ (∀ q ∈ Q, ∀ w ∈ W, (q : MulAut V) w ∈ W) ∧
      Nat.card W = Nat.card Z * Nat.card S := by
  classical
  have hsurj : Function.Surjective π := h.1
  have hZU : Z ≤ U := h.2.1
  have hHU : ∀ l : ↥L, ∀ u ∈ U, (l : MulAut V) u ∈ U := h.2.2.2.1
  obtain ⟨β', hβ's, hβ'k, hβ'e⟩ := exists_natMap h
  set T : Subgroup (Multiplicative (ι → K)) := S.toSubgroup with hT
  set W' : Subgroup ↥U := T.comap β' with hW'
  refine ⟨W'.map U.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro z hz
    refine ⟨⟨z, hZU hz⟩, ?_, rfl⟩
    show β' ⟨z, hZU hz⟩ ∈ T
    rw [(hβ'k _).2 hz]
    exact T.one_mem
  · rintro q hq _ ⟨u, hu, rfl⟩
    obtain ⟨γ, hγ⟩ := hsurj ⟨q, hQL hq⟩
    have hγq : ((π γ : L) : MulAut V) = q := by rw [hγ]
    have hu' : ((π γ : L) : MulAut V) (u : V) ∈ U := hHU (π γ) u u.2
    refine ⟨⟨_, hu'⟩, ?_, by simp [hγq]⟩
    show β' ⟨_, hu'⟩ ∈ T
    rw [hβ'e γ u hu']
    exact hS γ (hγq ▸ hq) _ hu
  ·
    have hW : Nat.card (W'.map U.subtype) = Nat.card W' :=
      Nat.card_congr (Subgroup.equivMapOfInjective W' U.subtype U.subtype_injective).toEquiv.symm
    have hrange : (β'.domRestrict W').range = T := by
      rw [MonoidHom.domRestrict_range, hW', Subgroup.map_comap_eq_self_of_surjective hβ's]
    have hcard : Nat.card W' = Nat.card T * Nat.card ((β'.domRestrict W').ker) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (β'.domRestrict W').ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, hrange]
    have hker : Nat.card ((β'.domRestrict W').ker) = Nat.card Z := by
      refine Nat.card_congr
        { toFun := fun x => ⟨((x : W') : U), (hβ'k _).1 x.2⟩
          invFun := fun z => ⟨⟨⟨z, hZU z.2⟩, by
              show β' ⟨z, hZU z.2⟩ ∈ T
              rw [(hβ'k _).2 z.2]
              exact T.one_mem⟩, (hβ'k ⟨z, hZU z.2⟩).2 z.2⟩
          left_inv := fun x => by ext; rfl
          right_inv := fun z => by ext; rfl }
    have hTS : Nat.card T = Nat.card S :=
      Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun _ => Iff.rfl)
    rw [hW, hcard, hker, hTS, mul_comm]

end Sec

section Transfer

variable {V : Type*} [CommGroup V] [Finite V] {ι : Type} [Fintype ι] [DecidableEq ι]
  {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {L : Subgroup (MulAut V)}
  {U Z : Subgroup V} {π : ↥Γ →* ↥L}

omit [Finite V] in
theorem card_sup_mul_card_inf_comm (A B : Subgroup V) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card B (A ⊔ B)
  have h2 := Subgroup.relIndex_mul_card B A
  rw [inf_eq_left.2 le_sup_right, Subgroup.relIndex_sup_right] at h1
  rw [← h1, ← h2, inf_comm]
  ring

theorem secA_of_realizes (h : (FFModel.nat Γ).RealizesVia L U Z π) :
    ∀ Q : Subgroup (MulAut V), Q ≤ L → ∀ S : AddSubgroup (ι → K),
      (∀ γ : Γ, ((π γ : L) : MulAut V) ∈ Q → ∀ v ∈ S,
        ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈ S) →
      ∃ W : Subgroup V, Z ≤ W ∧ W ≤ U ∧ (∀ q ∈ Q, ∀ w ∈ W, (q : MulAut V) w ∈ W) ∧
        Nat.card W = Nat.card Z * Nat.card S :=
  fun Q hQL S hS => exists_inv_of_sec h Q hQL S hS

theorem secB_of_realizes (h : (FFModel.nat Γ).RealizesVia L U Z π) :
    ∀ Q : Subgroup (MulAut V), Q ≤ L → ∀ W : Subgroup V, Z ≤ W → W ≤ U →
      (∀ q ∈ Q, ∀ w ∈ W, (q : MulAut V) w ∈ W) → W ≠ Z →
      ∃ S : AddSubgroup (ι → K), S ≠ ⊥ ∧
        (∀ γ : Γ, ((π γ : L) : MulAut V) ∈ Q → ∀ v ∈ S,
          ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈ S) ∧
        Nat.card Z * Nat.card S ≤ Nat.card W := by
  intro Q _ W hZW hWU hinv hne
  obtain ⟨S, hcard, hS, h0⟩ := exists_sec_of_inv h Q hZW hWU hinv
  exact ⟨S, fun hS0 => hne (h0 hS0), hS, hcard.ge⟩

omit [Finite V] in
theorem inv_inf {Q : Subgroup (MulAut V)} {A B : Subgroup V}
    (hA : ∀ q ∈ Q, ∀ a ∈ A, (q : MulAut V) a ∈ A) (hB : ∀ q ∈ Q, ∀ b ∈ B, (q : MulAut V) b ∈ B) :
    ∀ q ∈ Q, ∀ x ∈ A ⊓ B, (q : MulAut V) x ∈ A ⊓ B :=
  fun q hq x hx => ⟨hA q hq x hx.1, hB q hq x hx.2⟩

omit [Finite V] in
theorem inv_sup {Q : Subgroup (MulAut V)} {A B : Subgroup V}
    (hA : ∀ q ∈ Q, ∀ a ∈ A, (q : MulAut V) a ∈ A) (hB : ∀ q ∈ Q, ∀ b ∈ B, (q : MulAut V) b ∈ B) :
    ∀ q ∈ Q, ∀ x ∈ A ⊔ B, (q : MulAut V) x ∈ A ⊔ B := by
  intro q hq x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hx
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hA q hq a ha) (hB q hq b hb)

theorem secA_of_sum {I : Fin 2 → Subgroup V}
    (hI : ∀ i, (FFModel.nat Γ).RealizesVia L (I i) Z π) (hIU : ∀ i, I i ≤ U) :
    ∀ Q : Subgroup (MulAut V), Q ≤ L → ∀ S : AddSubgroup (ι → K),
      (∀ γ : Γ, ((π γ : L) : MulAut V) ∈ Q → ∀ v ∈ S,
        ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈ S) →
      ∃ W : Subgroup V, Z ≤ W ∧ W ≤ U ∧ (∀ q ∈ Q, ∀ w ∈ W, (q : MulAut V) w ∈ W) ∧
        Nat.card W = Nat.card Z * Nat.card S := by
  intro Q hQL S hS
  obtain ⟨W, hZW, hWI, hinv, hcard⟩ := exists_inv_of_sec (hI 0) Q hQL S hS
  exact ⟨W, hZW, hWI.trans (hIU 0), hinv, hcard⟩

theorem secB_of_sum {I : Fin 2 → Subgroup V}
    (hI : ∀ i, (FFModel.nat Γ).RealizesVia L (I i) Z π) (hU : I 0 ⊔ I 1 = U)
    (hind : I 0 ⊓ I 1 = Z) :
    ∀ Q : Subgroup (MulAut V), Q ≤ L → ∀ W : Subgroup V, Z ≤ W → W ≤ U →
      (∀ q ∈ Q, ∀ w ∈ W, (q : MulAut V) w ∈ W) → W ≠ Z →
      ∃ S : AddSubgroup (ι → K), S ≠ ⊥ ∧
        (∀ γ : Γ, ((π γ : L) : MulAut V) ∈ Q → ∀ v ∈ S,
          ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈ S) ∧
        Nat.card Z * Nat.card S ≤ Nat.card W := by
  intro Q hQL W hZW hWU hinv hne
  have hZI : ∀ i, Z ≤ I i := fun i => (hI i).2.1
  have hIinv : ∀ i, ∀ q ∈ Q, ∀ x ∈ I i, (q : MulAut V) x ∈ I i := fun i q hq x hx =>
    (hI i).2.2.2.1 ⟨q, hQL hq⟩ x hx
  by_cases h0 : W ⊓ I 0 = Z
  ·
    set W' := (W ⊔ I 0) ⊓ I 1 with hW'
    have hZW' : Z ≤ W' := le_inf ((hZI 0).trans le_sup_right) (hZI 1)
    have hW'inv := inv_inf (inv_sup hinv (hIinv 0)) (hIinv 1)
    have hW'ne : W' ≠ Z := by
      intro hW'Z
      apply hne
      refine le_antisymm (fun w hw => ?_) hZW
      have hwU : w ∈ I 0 ⊔ I 1 := hU ▸ hWU hw
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hwU
      have hbW' : b ∈ W' := by
        refine ⟨?_, hb⟩
        have hb' : b = (a * b) * a⁻¹ := by
          rw [mul_comm a b, mul_assoc, mul_inv_cancel, mul_one]
        rw [hb']
        exact Subgroup.mul_mem_sup hw ((I 0).inv_mem ha)
      rw [hW'Z] at hbW'
      have hab : a * b ∈ W ⊓ I 0 := ⟨hw, (I 0).mul_mem ha (hZI 0 hbW')⟩
      rwa [h0] at hab
    have hW'I : W' ⊓ I 0 = Z := by
      refine le_antisymm ?_ (le_inf hZW' (hZI 0))
      calc W' ⊓ I 0 ≤ I 0 ⊓ I 1 := le_inf inf_le_right (inf_le_left.trans inf_le_right)
        _ = Z := hind
    have hcard : Nat.card W' ≤ Nat.card W := by
      have h1 := card_sup_mul_card_inf_comm W (I 0)
      have h2 := card_sup_mul_card_inf_comm W' (I 0)
      rw [h0] at h1
      rw [hW'I] at h2
      have h3 : Nat.card ↥(W' ⊔ I 0) ≤ Nat.card ↥(W ⊔ I 0) :=
        Subgroup.card_le_of_le (sup_le (inf_le_left) le_sup_right)
      have hI0 : 0 < Nat.card ↥(I 0) := Nat.card_pos
      have h4 : Nat.card W' * Nat.card ↥(I 0) ≤ Nat.card W * Nat.card ↥(I 0) := by
        rw [← h1, ← h2]
        exact Nat.mul_le_mul_right _ h3
      exact Nat.le_of_mul_le_mul_right h4 hI0
    obtain ⟨S, hcardS, hS, hS0⟩ := exists_sec_of_inv (hI 1) Q hZW' inf_le_right hW'inv
    exact ⟨S, fun h => hW'ne (hS0 h), hS, hcardS ▸ hcard⟩
  · obtain ⟨S, hcardS, hS, hS0⟩ := exists_sec_of_inv (hI 0) Q (le_inf hZW (hZI 0))
      inf_le_right (inv_inf hinv (hIinv 0))
    refine ⟨S, fun h => h0 (hS0 h), hS, ?_⟩
    rw [← hcardS]
    exact Subgroup.card_le_of_le inf_le_left

@[expose] def NatTransfer (X : Subgroup (MulAut V)) (U Z : Subgroup V)
    (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) (π : ↥Γ →* ↥X) : Prop :=
  Function.Surjective π ∧ Function.Injective π ∧
    (∀ Q : Subgroup (MulAut V), Q ≤ X → ∀ S : AddSubgroup (ι → K),
      (∀ γ : Γ, ((π γ : X) : MulAut V) ∈ Q → ∀ v ∈ S,
        ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈ S) →
      ∃ W : Subgroup V, Z ≤ W ∧ W ≤ U ∧ (∀ q ∈ Q, ∀ w ∈ W, (q : MulAut V) w ∈ W) ∧
        Nat.card W = Nat.card Z * Nat.card S) ∧
    ∀ Q : Subgroup (MulAut V), Q ≤ X → ∀ W : Subgroup V, Z ≤ W → W ≤ U →
      (∀ q ∈ Q, ∀ w ∈ W, (q : MulAut V) w ∈ W) → W ≠ Z →
      ∃ S : AddSubgroup (ι → K), S ≠ ⊥ ∧
        (∀ γ : Γ, ((π γ : X) : MulAut V) ∈ Q → ∀ v ∈ S,
          ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈ S) ∧
        Nat.card Z * Nat.card S ≤ Nat.card W

theorem natTransfer_of_realizes (h : (FFModel.nat Γ).RealizesVia L U Z π) :
    NatTransfer L U Z Γ π :=
  ⟨h.1, FFC.injective_of_faithful_sec (FFModel.nat_faithful Γ) h, secA_of_realizes h,
    secB_of_realizes h⟩

theorem natTransfer_of_sum {I : Fin 2 → Subgroup V}
    (hI : ∀ i, (FFModel.nat Γ).RealizesVia L (I i) Z π) (hU : I 0 ⊔ I 1 = U)
    (hind : I 0 ⊓ I 1 = Z) : NatTransfer L U Z Γ π :=
  ⟨(hI 0).1, FFC.injective_of_faithful_sec (FFModel.nat_faithful Γ) (hI 0),
    secA_of_sum hI (fun i => hU ▸ (by fin_cases i; exacts [le_sup_left, le_sup_right])),
    secB_of_sum hI hU hind⟩

omit [Finite V] in
theorem map_inv_of_inv {P : Subgroup (MulAut V)} {W : Subgroup V}
    (hW : ∀ p ∈ P, ∀ w ∈ W, (p : MulAut V) w ∈ W) (g : MulAut V) :
    ∀ p ∈ P.map (MulAut.conj g).toMonoidHom, ∀ w ∈ W.map g.toMonoidHom,
      (p : MulAut V) w ∈ W.map g.toMonoidHom := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨w, hw, rfl⟩
  refine ⟨(p : MulAut V) w, hW p hp w hw, ?_⟩
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem no_swap_of_transfer
    (hA : ∀ Q : Subgroup (MulAut V), Q ≤ L → ∀ S : AddSubgroup (ι → K),
      (∀ γ : Γ, ((π γ : L) : MulAut V) ∈ Q → ∀ v ∈ S,
        ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈ S) →
      ∃ W : Subgroup V, Z ≤ W ∧ W ≤ U ∧ (∀ q ∈ Q, ∀ w ∈ W, (q : MulAut V) w ∈ W) ∧
        Nat.card W = Nat.card Z * Nat.card S)
    (hB : ∀ Q : Subgroup (MulAut V), Q ≤ L → ∀ W : Subgroup V, Z ≤ W → W ≤ U →
      (∀ q ∈ Q, ∀ w ∈ W, (q : MulAut V) w ∈ W) → W ≠ Z →
      ∃ S : AddSubgroup (ι → K), S ≠ ⊥ ∧
        (∀ γ : Γ, ((π γ : L) : MulAut V) ∈ Q → ∀ v ∈ S,
          ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈ S) ∧
        Nat.card Z * Nat.card S ≤ Nat.card W)
    {Pa Pb : Subgroup (MulAut V)} (hPa : Pa ≤ L) (hPb : Pb ≤ L) (q : ℕ)
    (hsmall : ∃ S : AddSubgroup (ι → K), S ≠ ⊥ ∧ Nat.card S ≤ q ∧
      ∀ γ : Γ, ((π γ : L) : MulAut V) ∈ Pa → ∀ v ∈ S,
        ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈ S)
    (hbig : ∀ S : AddSubgroup (ι → K), S ≠ ⊥ →
      (∀ γ : Γ, ((π γ : L) : MulAut V) ∈ Pb → ∀ v ∈ S,
        ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v ∈ S) → q < Nat.card S)
    (g : MulAut V) (hgU : U.map g.toMonoidHom = U) (hgZ : Z.map g.toMonoidHom = Z)
    (hg : Pa.map (MulAut.conj g).toMonoidHom = Pb) : False := by
  obtain ⟨S, hS0, hSq, hSinv⟩ := hsmall
  obtain ⟨W, hZW, hWU, hWinv, hWcard⟩ := hA Pa hPa S hSinv
  have hgW : ∀ p ∈ Pb, ∀ w ∈ W.map g.toMonoidHom, (p : MulAut V) w ∈ W.map g.toMonoidHom :=
    hg ▸ map_inv_of_inv hWinv g
  have hZgW : Z ≤ W.map g.toMonoidHom := hgZ ▸ Subgroup.map_mono hZW
  have hgWU : W.map g.toMonoidHom ≤ U := hgU ▸ Subgroup.map_mono hWU
  have hcardgW : Nat.card (W.map g.toMonoidHom) = Nat.card W :=
    Subgroup.card_map_of_injective g.injective
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hgWne : W.map g.toMonoidHom ≠ Z := by
    intro h0
    have h2 : Nat.card W = Nat.card Z := by rw [← hcardgW, h0]
    rw [hWcard] at h2
    have h3 : Nat.card S = 1 :=
      Nat.eq_of_mul_eq_mul_left hZpos (h2.trans (mul_one _).symm)
    exact hS0 (AddSubgroup.eq_bot_of_card_eq S h3)
  obtain ⟨S', hS'0, hS'inv, hS'card⟩ := hB Pb hPb _ hZgW hgWU hgW hgWne
  have hle : Nat.card S' ≤ Nat.card S := by
    rw [hcardgW, hWcard] at hS'card
    exact Nat.le_of_mul_le_mul_left hS'card hZpos
  have := hbig S' hS'0 hS'inv
  omega

end Transfer

end CFSG.Quasithin.H13.NQCat.NGT

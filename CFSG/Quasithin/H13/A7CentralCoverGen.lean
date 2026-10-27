module

public import CFSG.Quasithin.SteinbergCBSevenEven

public section

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Quasithin.SteinbergCB
open CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup (eq_one_of_forall_commute_alternating)
open scoped Pointwise

variable {G : Type*} [Group G]

theorem isSolvable_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    [Group.IsSolvable B] : Group.IsSolvable A :=
  Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem alternatingSeven_eq_one_of_commute {a : alternatingGroup (Fin 7)}
    (ha : ∀ b : alternatingGroup (Fin 7), a * b = b * a) : a = 1 := by
  have h : (a : Perm (Fin 7)) = 1 := by
    refine eq_one_of_forall_commute_alternating (by simp) fun g hg => ?_
    exact congrArg Subtype.val (ha ⟨g, hg⟩)
  exact Subtype.ext h

@[expose] def conjSub (L : Subgroup G) (x : G) (hx : x ∈ normalizer (L : Set G)) : L →* L where
  toFun l := ⟨x * l * x⁻¹, (mem_normalizer_iff.1 hx l).1 l.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjSub (L : Subgroup G) (x : G) (hx : x ∈ normalizer (L : Set G)) (l : L) :
    (conjSub L x hx l : G) = x * l * x⁻¹ :=
  rfl

theorem conjSub_mul (L : Subgroup G) {x y : G} (hx : x ∈ normalizer (L : Set G))
    (hy : y ∈ normalizer (L : Set G)) (l : L) :
    conjSub L (x * y) (mul_mem hx hy) l = conjSub L x hx (conjSub L y hy l) :=
  Subtype.ext (by simp only [coe_conjSub]; group)

theorem conjSub_one (L : Subgroup G) (h : (1 : G) ∈ normalizer (L : Set G)) (l : L) :
    conjSub L 1 h l = l :=
  Subtype.ext (by simp [coe_conjSub])

theorem conjSub_inv_conjSub (L : Subgroup G) {x : G} (hx : x ∈ normalizer (L : Set G))
    (hx' : x⁻¹ ∈ normalizer (L : Set G)) (l : L) : conjSub L x⁻¹ hx' (conjSub L x hx l) = l :=
  Subtype.ext (by simp only [coe_conjSub]; group)

theorem conjSub_conjSub_inv (L : Subgroup G) {x : G} (hx : x ∈ normalizer (L : Set G))
    (hx' : x⁻¹ ∈ normalizer (L : Set G)) (l : L) : conjSub L x hx (conjSub L x⁻¹ hx' l) = l :=
  Subtype.ext (by simp only [coe_conjSub]; group)

section Induced

variable {L : Subgroup G} {φ : L →* alternatingGroup (Fin 7)}

@[expose] noncomputable def indFun (hφ : Function.Surjective φ) (x : G)
    (hx : x ∈ normalizer (L : Set G)) (a : alternatingGroup (Fin 7)) : alternatingGroup (Fin 7) :=
  φ (conjSub L x hx (Function.surjInv hφ a))

theorem indFun_apply (hφ : Function.Surjective φ) {x : G} (hx : x ∈ normalizer (L : Set G))
    (hk : ∀ k : L, φ k = 1 → φ (conjSub L x hx k) = 1) (l : L) :
    indFun hφ x hx (φ l) = φ (conjSub L x hx l) := by
  set l' := Function.surjInv hφ (φ l) with hl'
  have h1 : φ l' = φ l := Function.surjInv_eq hφ _
  have h2 : φ (l'⁻¹ * l) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
  have h3 := hk _ h2
  rw [map_mul, map_mul, map_inv, map_inv, inv_mul_eq_one] at h3
  exact h3

@[expose] noncomputable def indAut (hφ : Function.Surjective φ) {x : G}
    (hx : x ∈ normalizer (L : Set G)) (hx' : x⁻¹ ∈ normalizer (L : Set G))
    (hk : ∀ k : L, φ k = 1 → φ (conjSub L x hx k) = 1)
    (hk' : ∀ k : L, φ k = 1 → φ (conjSub L x⁻¹ hx' k) = 1) :
    MulAut (alternatingGroup (Fin 7)) where
  toFun := indFun hφ x hx
  invFun := indFun hφ x⁻¹ hx'
  left_inv a := by
    obtain ⟨l, rfl⟩ := hφ a
    rw [indFun_apply hφ hx hk, indFun_apply hφ hx' hk', conjSub_inv_conjSub]
  right_inv a := by
    obtain ⟨l, rfl⟩ := hφ a
    rw [indFun_apply hφ hx' hk', indFun_apply hφ hx hk, conjSub_conjSub_inv]
  map_mul' a b := by
    obtain ⟨l, rfl⟩ := hφ a
    obtain ⟨m, rfl⟩ := hφ b
    show indFun hφ x hx (φ l * φ m) = indFun hφ x hx (φ l) * indFun hφ x hx (φ m)
    rw [← map_mul, indFun_apply hφ hx hk, indFun_apply hφ hx hk, indFun_apply hφ hx hk, map_mul,
      map_mul]

theorem indAut_apply (hφ : Function.Surjective φ) {x : G} (hx : x ∈ normalizer (L : Set G))
    (hx' : x⁻¹ ∈ normalizer (L : Set G)) (hk : ∀ k : L, φ k = 1 → φ (conjSub L x hx k) = 1)
    (hk' : ∀ k : L, φ k = 1 → φ (conjSub L x⁻¹ hx' k) = 1) (l : L) :
    indAut hφ hx hx' hk hk' (φ l) = φ (conjSub L x hx l) :=
  indFun_apply hφ hx hk l

variable {X : Subgroup G}

@[expose] noncomputable def indHom (hX : X ≤ normalizer (L : Set G))
    (hφ : Function.Surjective φ)
    (hker : ∀ x (hx : x ∈ X) (k : L), φ k = 1 → φ (conjSub L x (hX hx) k) = 1) :
    X →* MulAut (alternatingGroup (Fin 7)) where
  toFun x := indAut hφ (hX x.2) (hX (inv_mem x.2)) (hker x x.2) (hker x⁻¹ (inv_mem x.2))
  map_one' := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨l, rfl⟩ := hφ a
    simp only [OneMemClass.coe_one, MulAut.one_apply]
    rw [indAut_apply, conjSub_one]
  map_mul' x y := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨l, rfl⟩ := hφ a
    simp only [Subgroup.coe_mul, MulAut.mul_apply]
    rw [indAut_apply, indAut_apply, indAut_apply, conjSub_mul L (hX x.2) (hX y.2)]

theorem indHom_apply (hX : X ≤ normalizer (L : Set G)) (hφ : Function.Surjective φ)
    (hker : ∀ x (hx : x ∈ X) (k : L), φ k = 1 → φ (conjSub L x (hX hx) k) = 1) (x : X) (l : L) :
    indHom hX hφ hker x (φ l) = φ (conjSub L x (hX x.2) l) :=
  indAut_apply hφ (hX x.2) (hX (inv_mem x.2)) (hker x x.2) (hker x⁻¹ (inv_mem x.2)) l

@[expose] noncomputable def conjEquivSeven : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
  MulEquiv.ofBijective (conjPerm 7) ⟨conjPerm_injective (by norm_num),
    conjPerm_surjective (Or.inr le_rfl)⟩

theorem conjEquivSeven_apply (σ : Perm (Fin 7)) : conjEquivSeven σ = conjPerm 7 σ :=
  rfl

theorem exists_perm_rep (hLX : L ≤ X) (hX : X ≤ normalizer (L : Set G))
    (hφ : Function.Surjective φ)
    (hker : ∀ x (hx : x ∈ X) (k : L), φ k = 1 → φ (conjSub L x (hX hx) k) = 1) :
    ∃ ρ : X →* Perm (Fin 7), ∀ l : L, ρ ⟨l, hLX l.2⟩ = (φ l : Perm (Fin 7)) := by
  refine ⟨conjEquivSeven.symm.toMonoidHom.comp (indHom hX hφ hker), fun l => ?_⟩
  apply conjEquivSeven.injective
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.apply_symm_apply]
  refine MulEquiv.ext fun a => ?_
  obtain ⟨m, rfl⟩ := hφ a
  rw [indHom_apply]
  apply Subtype.ext
  rw [conjEquivSeven_apply, conjPerm_apply]
  have : conjSub L (⟨l, hLX l.2⟩ : X) (hX (hLX l.2)) m = l * m * l⁻¹ :=
    Subtype.ext (by rw [coe_conjSub]; rfl)
  rw [this, map_mul, map_mul, map_inv]
  rfl

end Induced

theorem conj_mem_of_subgroupOf_normal {R X : Subgroup G} (hRX : R ≤ X)
    (hn : (R.subgroupOf X).Normal) {x r : G} (hx : x ∈ X) (hr : r ∈ R) : x * r * x⁻¹ ∈ R := by
  have h := hn.conj_mem ⟨r, hRX hr⟩ (by rwa [mem_subgroupOf]) ⟨x, hx⟩
  rwa [mem_subgroupOf] at h

theorem eq_alternating_or_top_of_le {F : Subgroup (Perm (Fin 7))}
    (hF : alternatingGroup (Fin 7) ≤ F) : F = alternatingGroup (Fin 7) ∨ F = ⊤ := by
  have h := Subgroup.index_dvd_of_le hF
  rw [alternatingGroup.index_eq_two] at h
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · exact Or.inr (Subgroup.index_eq_one.1 h1)
  · exact Or.inl (Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2)

theorem nat_card_perm_seven : Nat.card (Perm (Fin 7)) = 5040 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem nat_card_alternating_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 7)
  rw [nat_card_perm_seven] at h
  omega

theorem sevenA_inf_sup_sevenB_inf {F : Subgroup (Perm (Fin 7))}
    (hF : F = alternatingGroup (Fin 7) ∨ F = ⊤) : sevenA ⊓ F ⊔ sevenB ⊓ F = F := by
  rcases hF with rfl | rfl
  · exact (A7_two_solvable_even_overgroups_generate_A7).2.2.2.2.2.2
  · rw [inf_top_eq, inf_top_eq, sevenA_sup_sevenB]

theorem sevenP_inf_card {F : Subgroup (Perm (Fin 7))}
    (hF : F = alternatingGroup (Fin 7) ∨ F = ⊤) :
    IsPGroup 2 ((sevenP ⊓ F).subgroupOf F) ∧ ¬ 2 ∣ ((sevenP ⊓ F).subgroupOf F).index := by
  have hcard : ∀ {H : Subgroup (Perm (Fin 7))}, H ≤ F →
      Nat.card (H.subgroupOf F) = Nat.card H := fun hH =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  have key : ∀ m n : ℕ, Nat.card F = 315 * 2 ^ n →
      Nat.card (sevenP ⊓ F : Subgroup (Perm (Fin 7))) = 2 ^ n →
      IsPGroup 2 ((sevenP ⊓ F).subgroupOf F) ∧ ¬ 2 ∣ ((sevenP ⊓ F).subgroupOf F).index := by
    intro _ n hF hP
    have h1 := hcard (inf_le_right : sevenP ⊓ F ≤ F)
    refine ⟨IsPGroup.of_card (h1.trans hP), fun h2 => ?_⟩
    have h3 := Subgroup.card_mul_index ((sevenP ⊓ F).subgroupOf F)
    rw [h1, hP, hF] at h3
    have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
    obtain ⟨c, hc⟩ := h2
    rw [hc] at h3
    have : 2 ^ n * (2 * c) = 2 ^ n * 315 := by rw [h3]; ring
    have := Nat.eq_of_mul_eq_mul_left hpos this
    omega
  rcases hF with rfl | rfl
  · exact key 0 3 (by rw [nat_card_alternating_seven]; norm_num) nat_card_sevenP_even
  · refine key 0 4 (by rw [Subgroup.card_top, nat_card_perm_seven]; norm_num) ?_
    rw [inf_top_eq, nat_card_sevenP]
    norm_num

theorem map_conj_eq_of_mem {F : Subgroup (Perm (Fin 7))} {f : Perm (Fin 7)} (hf : f ∈ F) :
    F.map (MulAut.conj f).toMonoidHom = F := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hf hy) (inv_mem hf)
  · intro hx
    refine ⟨f⁻¹ * x * f, mul_mem (mul_mem (inv_mem hf) hx) hf, ?_⟩
    change f * (f⁻¹ * x * f) * f⁻¹ = x
    group

theorem A7_every_normalized_central_cover_has_solvable_Sylow_generators [Finite G]
    (T : Sylow 2 G) {L R : Subgroup G} (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hRL : R ≤ L) (hR : IsPGroup 2 R) (hRn : (R.subgroupOf (L ⊔ T)).Normal)
    [(R.subgroupOf L).Normal] (θ : L ⧸ R.subgroupOf L →* alternatingGroup (Fin 7))
    (hθ : Function.Surjective θ) (hθc : θ.ker ≤ center (L ⧸ R.subgroupOf L)) :
    (∃ H₁ H₂ : Subgroup G, (T : Subgroup G) ≤ H₁ ∧ H₁ ≤ L ⊔ T ∧ (T : Subgroup G) ≤ H₂ ∧
        H₂ ≤ L ⊔ T ∧ Group.IsSolvable H₁ ∧ Group.IsSolvable H₂ ∧ H₁ ⊔ H₂ = L ⊔ T) ∧
      ∀ M : Subgroup G, (∀ H : Subgroup G, (T : Subgroup G) ≤ H → Group.IsSolvable H → H ≤ M) →
        L ≤ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := L ⊔ T with hXdef
  have hLX : L ≤ X := le_sup_left
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hRX : R ≤ X := hRL.trans hLX
  have hXN : X ≤ normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  set φ : L →* alternatingGroup (Fin 7) :=
    θ.comp (QuotientGroup.mk' (R.subgroupOf L)) with hφdef
  have hφ : Function.Surjective φ := hθ.comp (QuotientGroup.mk'_surjective _)
  have hkerφ : ∀ k : L, φ k = 1 ↔ ∀ l : L, ((k * l * k⁻¹ * l⁻¹ : L) : G) ∈ R := by
    intro k
    constructor
    · intro hk l
      have hc : (QuotientGroup.mk k : L ⧸ R.subgroupOf L) ∈ center (L ⧸ R.subgroupOf L) :=
        hθc hk
      have h1 := Subgroup.mem_center_iff.1 hc (QuotientGroup.mk l)
      have h2 : (QuotientGroup.mk (k * l * k⁻¹ * l⁻¹) : L ⧸ R.subgroupOf L) = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.mk_inv, ← h1]
        group
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h2
      exact h2
    · intro hk
      apply alternatingSeven_eq_one_of_commute
      intro b
      obtain ⟨l, rfl⟩ := hφ b
      have h1 : (QuotientGroup.mk (k * l * k⁻¹ * l⁻¹) : L ⧸ R.subgroupOf L) = 1 := by
        rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
        exact hk l
      have h2 : (QuotientGroup.mk k : L ⧸ R.subgroupOf L) * QuotientGroup.mk l =
          QuotientGroup.mk l * QuotientGroup.mk k := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.mk_inv] at h1
        calc _ = (QuotientGroup.mk k * QuotientGroup.mk l * (QuotientGroup.mk k)⁻¹ *
              (QuotientGroup.mk l)⁻¹) * (QuotientGroup.mk l * QuotientGroup.mk k :
                L ⧸ R.subgroupOf L) := by group
          _ = _ := by rw [h1, one_mul]
      change θ (QuotientGroup.mk k) * θ (QuotientGroup.mk l) =
        θ (QuotientGroup.mk l) * θ (QuotientGroup.mk k)
      rw [← map_mul, ← map_mul, h2]
  have hker : ∀ x (hx : x ∈ X) (k : L), φ k = 1 → φ (conjSub L x (hXN hx) k) = 1 := by
    intro x hx k hk
    rw [hkerφ] at hk ⊢
    intro l
    have hl' := hk (conjSub L x⁻¹ (hXN (inv_mem hx)) l)
    have h := conj_mem_of_subgroupOf_normal hRX hRn hx hl'
    have he : ((conjSub L x (hXN hx) k * l * (conjSub L x (hXN hx) k)⁻¹ * l⁻¹ : L) : G) =
        x * ((k * conjSub L x⁻¹ (hXN (inv_mem hx)) l * k⁻¹ *
          (conjSub L x⁻¹ (hXN (inv_mem hx)) l)⁻¹ : L) : G) * x⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjSub]
      group
    rw [he]
    exact h
  obtain ⟨ρ, hρ⟩ := exists_perm_rep hLX hXN hφ hker
  set F : Subgroup (Perm (Fin 7)) := ρ.range with hFdef
  have hAF : alternatingGroup (Fin 7) ≤ F := by
    intro a ha
    obtain ⟨l, hl⟩ := hφ ⟨a, ha⟩
    exact ⟨⟨l, hLX l.2⟩, by rw [hρ, hl]⟩
  have hF := eq_alternating_or_top_of_le hAF
  set N : Subgroup X := ρ.ker with hNdef
  have hN : Group.IsSolvable N := by
    have hK : Group.IsSolvable φ.ker := by
      let g : φ.ker →* θ.ker :=
        { toFun := fun k => ⟨QuotientGroup.mk k.1, k.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hθab : Group.IsSolvable θ.ker := Group.isSolvable_of_comm fun a b => by
        apply Subtype.ext
        exact Subgroup.mem_center_iff.1 (hθc b.2) a
      have hRs : Group.IsSolvable (R.subgroupOf L) := by
        have : Finite R := inferInstance
        have hp : IsPGroup 2 (R.subgroupOf L) := by
          refine IsPGroup.of_equiv hR (Subgroup.subgroupOfEquivOfLe hRL).symm
        have : Group.IsNilpotent (R.subgroupOf L) := hp.isNilpotent
        infer_instance
      let f : R.subgroupOf L →* φ.ker :=
        { toFun := fun r => ⟨r.1, by
            change θ (QuotientGroup.mk r.1) = 1
            rw [(QuotientGroup.eq_one_iff r.1).2 r.2, map_one]⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      refine Group.isSolvable_of_ker_le_range f g fun k hk => ?_
      have hk' : (QuotientGroup.mk k.1 : L ⧸ R.subgroupOf L) = 1 :=
        congrArg Subtype.val hk
      rw [QuotientGroup.eq_one_iff] at hk'
      exact ⟨⟨k.1, hk'⟩, rfl⟩
    have hLn : (L.subgroupOf X).Normal :=
      ⟨fun l hl x => by
        rw [mem_subgroupOf] at hl ⊢
        exact (mem_normalizer_iff.1 (hXN x.2) l).1 hl⟩
    have hXL : Group.IsSolvable (X ⧸ L.subgroupOf X) := by
      have hp : IsPGroup 2 (X ⧸ L.subgroupOf X) := by
        have hsurj : Function.Surjective
            ((QuotientGroup.mk' (L.subgroupOf X)).comp (Subgroup.inclusion hTX)) := by
          intro q
          obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
          have hx : (x : G) ∈ ((T : Subgroup G) : Set G) * (L : Set G) := by
            rw [← Subgroup.coe_mul_of_left_le_normalizer_right (T : Subgroup G) L hTL, sup_comm]
            exact x.2
          obtain ⟨t, ht, l, hl, hlt⟩ := hx
          refine ⟨⟨t, ht⟩, ?_⟩
          rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
            QuotientGroup.eq, mem_subgroupOf]
          have : (((Subgroup.inclusion hTX ⟨t, ht⟩)⁻¹ * x : X) : G) = l := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
            rw [← hlt]
            group
          rw [this]
          exact hl
        exact T.isPGroup'.of_surjective _ hsurj
      have : Group.IsNilpotent (X ⧸ L.subgroupOf X) := hp.isNilpotent
      infer_instance
    let g : N →* X ⧸ L.subgroupOf X := (QuotientGroup.mk' (L.subgroupOf X)).comp N.subtype
    let f : φ.ker →* N :=
      { toFun := fun k => ⟨⟨k.1, hLX k.1.2⟩, by
          change ρ ⟨k.1, hLX k.1.2⟩ = 1
          rw [hρ]
          have hk : φ k.1 = 1 := k.2
          rw [hk]
          rfl⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_ker_le_range f g fun n hn => ?_
    have hn' : (n : X) ∈ L.subgroupOf X := by
      have : (QuotientGroup.mk (n : X) : X ⧸ L.subgroupOf X) = 1 := hn
      rwa [QuotientGroup.eq_one_iff] at this
    rw [mem_subgroupOf] at hn'
    have hφn : φ ⟨((n : X) : G), hn'⟩ = 1 := by
      have h1 : ρ (n : X) = 1 := n.2
      have h2 := hρ ⟨((n : X) : G), hn'⟩
      have h3 : (⟨((n : X) : G), hLX hn'⟩ : X) = (n : X) := rfl
      rw [h3, h1] at h2
      exact Subtype.ext h2.symm
    exact ⟨⟨⟨((n : X) : G), hn'⟩, hφn⟩, rfl⟩
  obtain ⟨hPp, hPi⟩ := sevenP_inf_card hF
  set PF : Sylow 2 F := hPp.toSylow hPi with hPF
  set TF : Subgroup F := ((T : Subgroup G).subgroupOf X).map ρ.rangeRestrict with hTF
  have hTFp : IsPGroup 2 TF := by
    refine IsPGroup.map ?_ _
    exact IsPGroup.of_equiv T.isPGroup' (Subgroup.subgroupOfEquivOfLe hTX).symm
  obtain ⟨Q, hQ⟩ := hTFp.exists_le_sylow
  obtain ⟨f, hf⟩ := MulAction.exists_smul_eq F PF Q
  set c : Perm (Fin 7) →* Perm (Fin 7) := (MulAut.conj (f : Perm (Fin 7))).toMonoidHom with hc
  set S₁ : Subgroup (Perm (Fin 7)) := (sevenA ⊓ F).map c with hS₁
  set S₂ : Subgroup (Perm (Fin 7)) := (sevenB ⊓ F).map c with hS₂
  have hcinj : Function.Injective c := (MulAut.conj (f : Perm (Fin 7))).injective
  have hS₁s : Group.IsSolvable S₁ := by
    have := isSolvable_sevenA
    have : Group.IsSolvable (sevenA ⊓ F : Subgroup (Perm (Fin 7))) :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (inf_le_left : sevenA ⊓ F ≤ sevenA))
        (Subgroup.inclusion_injective inf_le_left)
    exact isSolvable_of_mulEquiv (Subgroup.equivMapOfInjective _ c hcinj).symm
  have hS₂s : Group.IsSolvable S₂ := by
    have := isSolvable_sevenB
    have : Group.IsSolvable (sevenB ⊓ F : Subgroup (Perm (Fin 7))) :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (inf_le_left : sevenB ⊓ F ≤ sevenB))
        (Subgroup.inclusion_injective inf_le_left)
    exact isSolvable_of_mulEquiv (Subgroup.equivMapOfInjective _ c hcinj).symm
  have hρT : ∀ t (ht : t ∈ (T : Subgroup G)), ρ ⟨t, hTX ht⟩ ∈ (sevenP ⊓ F).map c := by
    intro t ht
    have h1 : ρ.rangeRestrict ⟨t, hTX ht⟩ ∈ TF :=
      Subgroup.mem_map_of_mem _ (by rw [mem_subgroupOf]; exact ht)
    have h2 := hQ h1
    rw [← hf, Sylow.coe_subgroup_smul] at h2
    obtain ⟨y, hy, hye⟩ := h2
    have hy' : (y : Perm (Fin 7)) ∈ sevenP ⊓ F := by
      have : y ∈ (PF : Subgroup F) := hy
      rw [hPF, IsPGroup.toSylow_coe, mem_subgroupOf] at this
      exact this
    refine ⟨y, hy', ?_⟩
    have h3 : (f : Perm (Fin 7)) * y * (f : Perm (Fin 7))⁻¹ = ρ ⟨t, hTX ht⟩ :=
      congrArg Subtype.val hye
    exact h3
  have hPA : sevenP ⊓ F ≤ sevenA ⊓ F :=
    inf_le_inf_right _ (sevenA_inf_sevenB ▸ inf_le_left)
  have hPB : sevenP ⊓ F ≤ sevenB ⊓ F :=
    inf_le_inf_right _ (sevenA_inf_sevenB ▸ inf_le_right)
  set K₁ : Subgroup X := S₁.comap ρ with hK₁
  set K₂ : Subgroup X := S₂.comap ρ with hK₂
  have hNK₁ : N ≤ K₁ := fun n hn => by
    change ρ n ∈ S₁
    rw [(MonoidHom.mem_ker).1 hn]
    exact one_mem _
  have hNK₂ : N ≤ K₂ := fun n hn => by
    change ρ n ∈ S₂
    rw [(MonoidHom.mem_ker).1 hn]
    exact one_mem _
  have hKs : ∀ (S : Subgroup (Perm (Fin 7))), Group.IsSolvable S →
      Group.IsSolvable (S.comap ρ) := by
    intro S hS
    let g : S.comap ρ →* S :=
      { toFun := fun k => ⟨ρ k.1, k.2⟩
        map_one' := Subtype.ext (map_one ρ)
        map_mul' := fun a b => Subtype.ext (map_mul ρ a.1 b.1) }
    let f : N →* S.comap ρ :=
      { toFun := fun n => ⟨n, by
            change ρ n ∈ S
            rw [(MonoidHom.mem_ker).1 n.2]
            exact one_mem _⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_ker_le_range f g fun k hk => ?_
    have hk' : ρ k = 1 := congrArg Subtype.val hk
    exact ⟨⟨k, hk'⟩, rfl⟩
  have hHs : ∀ K : Subgroup X, Group.IsSolvable K → Group.IsSolvable (K.map X.subtype) :=
    fun K _ => isSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective K X.subtype X.subtype_injective).symm
  have hgen : K₁ ⊔ K₂ = ⊤ := by
    have h1 : S₁ ⊔ S₂ = F := by
      rw [hS₁, hS₂, ← Subgroup.map_sup, sevenA_inf_sup_sevenB_inf hF]
      exact map_conj_eq_of_mem f.2
    have h2 : (K₁ ⊔ K₂).map ρ = S₁ ⊔ S₂ := by
      rw [Subgroup.map_sup, hK₁, hK₂, Subgroup.map_comap_eq, Subgroup.map_comap_eq]
      have hS₁F : S₁ ≤ ρ.range := by
        rw [← hFdef, hS₁]
        intro x hx
        rw [← map_conj_eq_of_mem f.2]
        exact Subgroup.map_mono inf_le_right hx
      have hS₂F : S₂ ≤ ρ.range := by
        rw [← hFdef, hS₂]
        intro x hx
        rw [← map_conj_eq_of_mem f.2]
        exact Subgroup.map_mono inf_le_right hx
      rw [inf_eq_right.2 hS₁F, inf_eq_right.2 hS₂F]
    rw [eq_top_iff]
    intro x _
    have hx : ρ x ∈ (K₁ ⊔ K₂).map ρ := by
      rw [h2, h1]
      exact ⟨x, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hx
    have hxy : x = y * (y⁻¹ * x) := by group
    rw [hxy]
    refine mul_mem hy (Subgroup.mem_sup_left (hNK₁ ?_))
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  refine ⟨⟨K₁.map X.subtype, K₂.map X.subtype, ?_, Subgroup.map_subtype_le _, ?_,
    Subgroup.map_subtype_le _, hHs _ (hKs _ hS₁s), hHs _ (hKs _ hS₂s), ?_⟩, ?_⟩
  · intro t ht
    refine ⟨⟨t, hTX ht⟩, ?_, rfl⟩
    change ρ ⟨t, hTX ht⟩ ∈ S₁
    exact Subgroup.map_mono hPA (hρT t ht)
  · intro t ht
    refine ⟨⟨t, hTX ht⟩, ?_, rfl⟩
    change ρ ⟨t, hTX ht⟩ ∈ S₂
    exact Subgroup.map_mono hPB (hρT t ht)
  · rw [← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · intro M hM
    have h1 : K₁.map X.subtype ≤ M := hM _ (fun t ht => ⟨⟨t, hTX ht⟩,
      Subgroup.map_mono hPA (hρT t ht), rfl⟩) (hHs _ (hKs _ hS₁s))
    have h2 : K₂.map X.subtype ≤ M := hM _ (fun t ht => ⟨⟨t, hTX ht⟩,
      Subgroup.map_mono hPB (hρT t ht), rfl⟩) (hHs _ (hKs _ hS₂s))
    have h3 : X = K₁.map X.subtype ⊔ K₂.map X.subtype := by
      rw [← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hLX.trans (h3 ▸ sup_le h1 h2)

end CFSG.Quasithin.H13.A7

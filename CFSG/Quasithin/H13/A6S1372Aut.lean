module

public import CFSG.Quasithin.H13.A6S13721b
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

namespace AutA6Rank

@[expose] def pslInvC : List (List ℕ) :=
  Core.pslLit.filter fun c => Core.cmul c c == Core.cid && c != Core.cid

@[expose] def outInvC : List (List ℕ) :=
  Core.autL.filter fun c => Core.cmul c c == Core.cid && !Core.pslLit.contains c

theorem rank_check : pslInvC.all (fun a => pslInvC.all (fun b => b == a ||
    Core.cmul a b != Core.cmul b a || pslInvC.all (fun c => Core.cmul a c != Core.cmul c a ||
      Core.cmul b c != Core.cmul c b || c == a || c == b || c == Core.cmul a b))) = true := by
  decide +kernel

theorem coset_check : outInvC.all (fun x => outInvC.all (fun y =>
    Core.cmul (Core.cmul x y) (Core.cmul x y) != Core.cid ||
      Core.pslLit.contains (Core.cmul x y))) = true := by
  decide +kernel

theorem code_mem_pslInvC {a : P10} (ha : a ∈ A6Models.psl29) (ha2 : a * a = 1) (ha1 : a ≠ 1) :
    code a ∈ pslInvC := by
  unfold pslInvC
  rw [List.mem_filter]
  refine ⟨(mem_psl29_iff a).1 ha, ?_⟩
  rw [← code_mul, ha2, code_one]
  simp only [beq_self_eq_true, Bool.true_and, bne_iff_ne, ne_eq]
  rw [← code_one]
  exact fun h => ha1 (code_injective h)

theorem code_mem_outInvC {a : P10} (ha : a ∈ A6Models.autA6) (ha2 : a * a = 1)
    (hap : a ∉ A6Models.psl29) : code a ∈ outInvC := by
  unfold outInvC
  rw [List.mem_filter]
  refine ⟨code_mem_autL ha, ?_⟩
  rw [← code_mul, ha2, code_one]
  simp only [beq_self_eq_true, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true]
  rw [mem_psl29_iff] at hap
  simpa [List.contains_eq_any_beq] using hap

theorem eq_mul_of_commute {a b c : P10} (ha : a ∈ A6Models.psl29) (hb : b ∈ A6Models.psl29)
    (hc : c ∈ A6Models.psl29) (ha2 : a * a = 1) (hb2 : b * b = 1) (hc2 : c * c = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hab : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b)
    (hcab : a * b = b * a) (hcac : a * c = c * a) (hcbc : b * c = c * b) : c = a * b := by
  have h := rank_check
  rw [List.all_eq_true] at h
  have h1 := h _ (code_mem_pslInvC ha ha2 ha1)
  rw [List.all_eq_true] at h1
  have h2 := h1 _ (code_mem_pslInvC hb hb2 hb1)
  have e1 : (code b == code a) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact fun h => hab (code_injective h)
  have e2 : (Core.cmul (code a) (code b) != Core.cmul (code b) (code a)) = false := by
    rw [← code_mul, ← code_mul, hcab]
    simp
  rw [e1, e2, Bool.false_or, Bool.false_or, List.all_eq_true] at h2
  have h3 := h2 _ (code_mem_pslInvC hc hc2 hc1)
  have e3 : (Core.cmul (code a) (code c) != Core.cmul (code c) (code a)) = false := by
    rw [← code_mul, ← code_mul, hcac]
    simp
  have e4 : (Core.cmul (code b) (code c) != Core.cmul (code c) (code b)) = false := by
    rw [← code_mul, ← code_mul, hcbc]
    simp
  have e5 : (code c == code a) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact fun h => hca (code_injective h)
  have e6 : (code c == code b) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact fun h => hcb (code_injective h)
  rw [e3, e4, e5, e6] at h3
  simp only [Bool.false_or, beq_iff_eq] at h3
  rw [← code_mul] at h3
  exact code_injective h3

theorem mul_mem_psl29 {x y : P10} (hx : x ∈ A6Models.autA6) (hy : y ∈ A6Models.autA6)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxp : x ∉ A6Models.psl29) (hyp : y ∉ A6Models.psl29)
    (hxy2 : x * y * (x * y) = 1) : x * y ∈ A6Models.psl29 := by
  have h := coset_check
  rw [List.all_eq_true] at h
  have h1 := h _ (code_mem_outInvC hx hx2 hxp)
  rw [List.all_eq_true] at h1
  have h2 := h1 _ (code_mem_outInvC hy hy2 hyp)
  have e : (Core.cmul (Core.cmul (code x) (code y)) (Core.cmul (code x) (code y)) != Core.cid) =
      false := by
    rw [← code_mul, ← code_mul, hxy2, code_one]
    simp
  rw [e, Bool.false_or, ← code_mul] at h2
  rw [mem_psl29_iff]
  simpa [List.contains_eq_any_beq] using h2

theorem card_le_four {X : Subgroup P10} {a b c d : P10}
    (h : ∀ x ∈ X, x = a ∨ x = b ∨ x = c ∨ x = d) : Nat.card X ≤ 4 := by
  have hsub : (X : Set P10) ⊆ {a, b, c, d} := fun x hx => by
    rcases h x hx with rfl | rfl | rfl | rfl <;> simp
  calc Nat.card X = Nat.card (X : Set P10) := rfl
    _ ≤ Nat.card ({a, b, c, d} : Set P10) := Nat.card_mono (Set.toFinite _) hsub
    _ = ({a, b, c, d} : Set P10).ncard := (Nat.card_coe_set_eq _)
    _ ≤ 4 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
      rw [Set.ncard_singleton]

theorem card_le_four_of_le_psl29 {X : Subgroup P10} (hX : X ≤ A6Models.psl29)
    (h2 : ∀ x ∈ X, x * x = 1) : Nat.card X ≤ 4 := by
  have hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    have h1 := h2 _ (X.mul_mem hx hy)
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (h2 x hx)
    have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h2 y hy)
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = y * x := by rw [mul_inv_rev, hx', hy']
  by_cases hA : ∀ x ∈ X, x = 1
  · exact card_le_four (a := 1) (b := 1) (c := 1) (d := 1) fun x hx => Or.inl (hA x hx)
  push Not at hA
  obtain ⟨a, haX, ha1⟩ := hA
  by_cases hB : ∀ x ∈ X, x = 1 ∨ x = a
  · exact card_le_four (c := 1) (d := 1) fun x hx => (hB x hx).elim Or.inl
      (fun h => Or.inr (Or.inl h))
  push Not at hB
  obtain ⟨b, hbX, hb1, hba⟩ := hB
  refine card_le_four (a := 1) (b := a) (c := b) (d := a * b) fun c hcX => ?_
  by_cases hc1 : c = 1
  · exact Or.inl hc1
  by_cases hca : c = a
  · exact Or.inr (Or.inl hca)
  by_cases hcb : c = b
  · exact Or.inr (Or.inr (Or.inl hcb))
  exact Or.inr (Or.inr (Or.inr (eq_mul_of_commute (hX haX) (hX hbX) (hX hcX) (h2 a haX)
    (h2 b hbX) (h2 c hcX) ha1 hb1 hc1 hba hca hcb (hcomm a haX b hbX) (hcomm a haX c hcX)
    (hcomm b hbX c hcX))))

theorem card_le_eight {X : Subgroup P10} (hX : X ≤ A6Models.autA6) (h2 : ∀ x ∈ X, x * x = 1) :
    Nat.card X ≤ 8 := by
  set Y : Subgroup P10 := X ⊓ A6Models.psl29 with hY
  have hY4 : Nat.card Y ≤ 4 :=
    card_le_four_of_le_psl29 inf_le_right fun y hy => h2 y hy.1
  have hXY : Nat.card X ≤ 2 * Nat.card Y := by
    by_cases hall : ∀ x ∈ X, x ∈ A6Models.psl29
    · have : X ≤ Y := fun x hx => ⟨hx, hall x hx⟩
      have h1 : Nat.card X ≤ Nat.card Y := Subgroup.card_le_of_le this
      omega
    push Not at hall
    obtain ⟨x₀, hx₀X, hx₀p⟩ := hall
    have hsub : (X : Set P10) ⊆ (Y : Set P10) ∪ (fun y => x₀ * y) '' (Y : Set P10) := by
      intro x hx
      by_cases hxp : x ∈ A6Models.psl29
      · exact Or.inl ⟨hx, hxp⟩
      · refine Or.inr ⟨x₀ * x, ⟨X.mul_mem hx₀X hx, mul_mem_psl29 (hX hx₀X) (hX hx) (h2 _ hx₀X)
          (h2 _ hx) hx₀p hxp (h2 _ (X.mul_mem hx₀X hx))⟩, ?_⟩
        show x₀ * (x₀ * x) = x
        rw [← mul_assoc, h2 _ hx₀X, one_mul]
    calc Nat.card X = (X : Set P10).ncard := (Nat.card_coe_set_eq _)
      _ ≤ ((Y : Set P10) ∪ (fun y => x₀ * y) '' (Y : Set P10)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (Y : Set P10).ncard + ((fun y => x₀ * y) '' (Y : Set P10)).ncard :=
          Set.ncard_union_le _ _
      _ ≤ (Y : Set P10).ncard + (Y : Set P10).ncard :=
          Nat.add_le_add_left (Set.ncard_image_le (Set.toFinite _)) _
      _ = 2 * Nat.card Y := by
          rw [← two_mul]
          exact congrArg (2 * ·) (Nat.card_coe_set_eq (Y : Set P10)).symm
  omega

variable {G : Type} [Group G] {K P E : Subgroup G}

@[expose] def conjK (hEK : E ≤ Subgroup.normalizer (K : Set G)) (e : ↥E) (k : ↥K) : ↥K :=
  ⟨(e : G) * k * (e : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hEK e.2) k).mp k.2⟩

theorem conjK_coe (hEK : E ≤ Subgroup.normalizer (K : Set G)) (e : ↥E) (k : ↥K) :
    ((conjK hEK e k : ↥K) : G) = (e : G) * k * (e : G)⁻¹ := rfl

theorem alpha_conjK_eq (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) {α : ↥K →* alternatingGroup (Fin 6)}
    (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P) (e : ↥E) {k k' : ↥K} (h : α k = α k') :
    α (conjK hEK e k) = α (conjK hEK e k') := by
  have h1 : α (k⁻¹ * k') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 : ((k⁻¹ * k' : ↥K) : G) ∈ P := (hα _).1 h1
  have h3 : (e : G) * ((k⁻¹ * k' : ↥K) : G) * (e : G)⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (hEP e.2) _).mp h2
  have h4 : α ((conjK hEK e k)⁻¹ * conjK hEK e k') = 1 := by
    rw [hα]
    convert h3 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjK_coe]
    group
  rw [map_mul, map_inv, inv_mul_eq_one] at h4
  exact h4

@[expose] noncomputable def gamFun (hEK : E ≤ Subgroup.normalizer (K : Set G))
    {α : ↥K →* alternatingGroup (Fin 6)} (hs : Function.Surjective α) (e : ↥E)
    (a : alternatingGroup (Fin 6)) : alternatingGroup (Fin 6) :=
  α (conjK hEK e (Function.surjInv hs a))

theorem gamFun_apply (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) {α : ↥K →* alternatingGroup (Fin 6)}
    (hs : Function.Surjective α) (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P) (e : ↥E) (k : ↥K) :
    gamFun hEK hs e (α k) = α (conjK hEK e k) :=
  alpha_conjK_eq hEK hEP hα e (Function.surjInv_eq hs (α k))

theorem gamFun_mul (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) {α : ↥K →* alternatingGroup (Fin 6)}
    (hs : Function.Surjective α) (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P) (e : ↥E)
    (a b : alternatingGroup (Fin 6)) :
    gamFun hEK hs e (a * b) = gamFun hEK hs e a * gamFun hEK hs e b := by
  obtain ⟨k, rfl⟩ := hs a
  obtain ⟨k', rfl⟩ := hs b
  rw [← map_mul, gamFun_apply hEK hEP hs hα, gamFun_apply hEK hEP hs hα,
    gamFun_apply hEK hEP hs hα, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [conjK_coe, Subgroup.coe_mul]
  group

theorem gamFun_comp (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) {α : ↥K →* alternatingGroup (Fin 6)}
    (hs : Function.Surjective α) (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P) (e e' : ↥E)
    (a : alternatingGroup (Fin 6)) :
    gamFun hEK hs (e * e') a = gamFun hEK hs e (gamFun hEK hs e' a) := by
  obtain ⟨k, rfl⟩ := hs a
  rw [gamFun_apply hEK hEP hs hα, gamFun_apply hEK hEP hs hα, gamFun_apply hEK hEP hs hα]
  congr 1
  apply Subtype.ext
  simp only [conjK_coe, Subgroup.coe_mul, mul_inv_rev]
  group

theorem gamFun_one (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) {α : ↥K →* alternatingGroup (Fin 6)}
    (hs : Function.Surjective α) (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P)
    (a : alternatingGroup (Fin 6)) : gamFun hEK hs 1 a = a := by
  obtain ⟨k, rfl⟩ := hs a
  rw [gamFun_apply hEK hEP hs hα]
  congr 1
  apply Subtype.ext
  simp [conjK_coe]

@[expose] noncomputable def gam (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) {α : ↥K →* alternatingGroup (Fin 6)}
    (hs : Function.Surjective α) (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P) :
    ↥E →* MulAut (alternatingGroup (Fin 6)) where
  toFun e :=
    { toFun := gamFun hEK hs e
      invFun := gamFun hEK hs e⁻¹
      left_inv := fun a => by
        rw [← gamFun_comp hEK hEP hs hα, inv_mul_cancel, gamFun_one hEK hEP hs hα]
      right_inv := fun a => by
        rw [← gamFun_comp hEK hEP hs hα, mul_inv_cancel, gamFun_one hEK hEP hs hα]
      map_mul' := gamFun_mul hEK hEP hs hα e }
  map_one' := MulEquiv.ext fun a => gamFun_one hEK hEP hs hα a
  map_mul' e e' := MulEquiv.ext fun a => gamFun_comp hEK hEP hs hα e e' a

theorem gam_apply (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) {α : ↥K →* alternatingGroup (Fin 6)}
    (hs : Function.Surjective α) (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P) (e : ↥E) (k : ↥K) :
    gam hEK hEP hs hα e (α k) = α (conjK hEK e k) :=
  gamFun_apply hEK hEP hs hα e k

theorem mem_ker_gam_iff (hKP : K ≤ Subgroup.normalizer (P : Set G))
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) (hEP : E ≤ Subgroup.normalizer (P : Set G))
    {α : ↥K →* alternatingGroup (Fin 6)} (hs : Function.Surjective α)
    (hα : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P)
    (hfaith : ∀ e ∈ E, (∀ k ∈ K, e * k * e⁻¹ * k⁻¹ ∈ P) → e ∈ P) (e : ↥E) :
    e ∈ (gam hEK hEP hs hα).ker ↔ (e : G) ∈ P := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    refine hfaith e e.2 fun k hk => ?_
    have h1 := congrArg (fun γ : MulAut (alternatingGroup (Fin 6)) => γ (α ⟨k, hk⟩)) h
    simp only [gam_apply, MulAut.one_apply] at h1
    have h2 : α (conjK hEK e ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := (hα _).1 h2
    simpa [conjK_coe] using h3
  · intro he
    refine MulEquiv.ext fun a => ?_
    obtain ⟨k, rfl⟩ := hs a
    rw [gam_apply, MulAut.one_apply]
    have h1 : α ((conjK hEK e k) * k⁻¹) = 1 := by
      rw [hα]
      have hk : (k : G) * (e : G)⁻¹ * (k : G)⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hKP k.2) _).mp (P.inv_mem he)
      have e1 : ((conjK hEK e k * k⁻¹ : ↥K) : G) =
          (e : G) * ((k : G) * (e : G)⁻¹ * (k : G)⁻¹) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjK_coe]
        group
      rw [e1]
      exact P.mul_mem he hk
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1

end AutA6Rank

@[expose] def AutA6Rank.conjAutHom : ↥A6Models.autA6 →* MulAut ↥A6Models.psl29 where
  toFun := DoubleA3.conjAut
  map_one' := MulEquiv.ext fun x => Subtype.ext (by simp [DoubleA3.conjAut_apply])
  map_mul' := fun a b => MulEquiv.ext fun x => Subtype.ext (by
    simp only [MulAut.mul_apply, DoubleA3.conjAut_apply, Subgroup.coe_mul]
    group)

@[expose] noncomputable def AutA6Rank.conjAutEquiv : ↥A6Models.autA6 ≃* MulAut ↥A6Models.psl29 :=
  MulEquiv.ofBijective AutA6Rank.conjAutHom
    ⟨DoubleA3.conjAut_injective, DoubleA3.conjAut_surjective⟩

theorem factAutA6Rank_holds : FactAutA6Rank := by
  intro G _ _ K P E hKP hEP hEK ⟨α, hs, hα⟩ hfaith hsq
  classical
  set Γ := AutA6Rank.gam hEK hEP hs hα with hΓ
  obtain ⟨ψ, -⟩ := DoubleA3.exists_psl_equiv
  have hker : Γ.ker = P.subgroupOf E := by
    ext e
    rw [AutA6Rank.mem_ker_gam_iff hKP hEK hEP hs hα hfaith, Subgroup.mem_subgroupOf]
  have hidx : (P ⊓ E).relIndex E = Nat.card Γ.range := by
    rw [Subgroup.inf_relIndex_right, Subgroup.relIndex, ← hker, Subgroup.index_ker]
  set Ξ : MulAut (alternatingGroup (Fin 6)) →* Equiv.Perm (Fin 10) :=
    A6Models.autA6.subtype.comp
      ((MulAut.congr ψ.symm).trans AutA6Rank.conjAutEquiv.symm).toMonoidHom with hΞ
  have hΞi : Function.Injective Ξ := by
    rw [hΞ, MonoidHom.coe_comp]
    exact A6Models.autA6.subtype_injective.comp (MulEquiv.injective _)
  have hX : Γ.range.map Ξ ≤ A6Models.autA6 := by
    rintro _ ⟨γ, -, rfl⟩
    exact (((MulAut.congr ψ.symm).trans AutA6Rank.conjAutEquiv.symm) γ).2
  have hX2 : ∀ x ∈ Γ.range.map Ξ, x * x = 1 := by
    rintro _ ⟨γ, ⟨e, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul]
    have he : e * e ∈ Γ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact hsq e e.2
    rw [MonoidHom.mem_ker.mp he, map_one]
  have h8 := AutA6Rank.card_le_eight hX hX2
  rw [Subgroup.card_map_of_injective hΞi] at h8
  rw [hidx]
  exact h8

end CFSG.Quasithin.H13.A6

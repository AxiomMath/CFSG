module

public import CFSG.Quasithin.Vol2.Ch3Sec3CZL32
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3325

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Par32
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative commutatorElement

namespace CZA6

@[expose] def w0 : A6Coc.Vec4 := A6Coc.crd (A6Coc.duad 4 5)

theorem fix_D8 : ∀ v : A6Coc.Vec4, A6Coc.act b1 v = v → A6Coc.act s1 v = v → v = 0 ∨ v = w0 := by
  decide +kernel

theorem b1_mem_sylowS6 : b1 ∈ sylowS6 := by
  rw [S6Syl.sylowS6_eq]
  show b1 ∈ S6Syl.elemsS
  decide +kernel

theorem s1_mem_sylowS6 : s1 ∈ sylowS6 := by
  rw [S6Syl.sylowS6_eq]
  show s1 ∈ S6Syl.elemsS
  decide +kernel

@[expose] def swaps0123 : List (Equiv.Perm (Fin 6)) :=
  [Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 0 3, Equiv.swap 1 2, Equiv.swap 1 3, Equiv.swap 2 3]

theorem swaps0123_mem_p1 : ∀ x ∈ swaps0123, code x ∈ codesP1 := by decide +kernel

theorem mem_swaps0123 {i j : Fin 6} (hi : (i : ℕ) < 4) (hj : (j : ℕ) < 4) (hij : i ≠ j) :
    Equiv.swap i j ∈ swaps0123 := by
  revert i j
  decide

theorem mem_p1_of_fix {τ : Equiv.Perm (Fin 6)} (h4 : τ 4 = 4) (h5 : τ 5 = 5) : τ ∈ p1 := by
  have hS : ∀ f ∈ {x | x ∈ swaps0123}, Equiv.Perm.IsSwap f := by
    intro f hf
    change f ∈ swaps0123 at hf
    simp only [swaps0123, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, by decide, rfl⟩
  have hlt : ∀ x : Fin 6, x ≠ 4 → x ≠ 5 → (x : ℕ) < 4 := by decide
  have hcl : τ ∈ Subgroup.closure {x | x ∈ swaps0123} := by
    rw [mem_closure_isSwap hS]
    refine ⟨Set.toFinite _, fun x => ?_⟩
    by_cases hx : τ x = x
    · rw [hx]
      exact MulAction.mem_orbit_self x
    · have hx4 : x ≠ 4 := fun h => hx (h ▸ h4)
      have hx5 : x ≠ 5 := fun h => hx (h ▸ h5)
      have hτ4 : τ x ≠ 4 := fun h => hx4 (τ.injective (h.trans h4.symm))
      have hτ5 : τ x ≠ 5 := fun h => hx5 (τ.injective (h.trans h5.symm))
      have hmem : Equiv.swap x (τ x) ∈ Subgroup.closure {x | x ∈ swaps0123} :=
        Subgroup.subset_closure (mem_swaps0123 (hlt x hx4 hx5) (hlt _ hτ4 hτ5) (Ne.symm hx))
      exact MulAction.mem_orbit_iff.mpr ⟨⟨_, hmem⟩, Equiv.swap_apply_left x (τ x)⟩
  have hle : Subgroup.closure {x | x ∈ swaps0123} ≤ p1 := by
    rw [Subgroup.closure_le]
    intro x hx
    have := swaps0123_mem_p1 x hx
    rw [← codes_P1] at this
    exact (mem_p1_iff x).mpr (mem_of_code_mem this)
  exact hle hcl

theorem mem_p1_of_act_w0 {τ : Equiv.Perm (Fin 6)} (h : A6Coc.act τ w0 = w0) : τ ∈ p1 := by
  rw [w0, A6Coc.act_duad] at h
  rcases A6Coc.duad_check 4 5 (τ 4) (τ 5) (by decide) h with ⟨h4, h5⟩ | ⟨h4, h5⟩
  · exact mem_p1_of_fix h4 h5
  · have h1 : τ * c45 ∈ p1 := by
      apply mem_p1_of_fix
      · rw [Equiv.Perm.mul_apply, c45_eq, Equiv.swap_apply_left, h5]
      · rw [Equiv.Perm.mul_apply, c45_eq, Equiv.swap_apply_right, h4]
    have h2 : c45 ∈ p1 := r1_le_p1 c45_mem_r1
    have := p1.mul_mem h1 (p1.inv_mem h2)
    rwa [mul_inv_cancel_right] at this

theorem gens1_fix_w0 : ∀ x ∈ gens1, A6Coc.act x w0 = w0 := by decide +kernel

theorem act_w0_of_mem_p1 {τ : Equiv.Perm (Fin 6)} (h : τ ∈ p1) : A6Coc.act τ w0 = w0 := by
  let S : Subgroup (Equiv.Perm (Fin 6)) :=
    { carrier := {x | A6Coc.act x w0 = w0}
      mul_mem' := fun {a b} ha hb => by
        show A6Coc.act (a * b) w0 = w0
        rw [A6Coc.act_mul, hb, ha]
      one_mem' := A6Coc.act_one w0
      inv_mem' := fun {a} ha => by
        show A6Coc.act a⁻¹ w0 = w0
        conv_lhs => rw [← ha]
        rw [← A6Coc.act_mul, inv_mul_cancel, A6Coc.act_one] }
  have hle : p1 ≤ S := by
    rw [p1, Subgroup.closure_le]
    intro x hx
    exact gens1_fix_w0 x hx
  exact hle h

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_image_sylow {T L : Subgroup G}
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Equiv.Perm (Fin 6))
    (hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G)) (hTidx : ¬ 2 ∣ T.index)
    (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hLTN (Subgroup.mem_sup_right ht)⟩ ∈ sylowS6)
    (hH : (ρ.comp (Subgroup.inclusion hLTN)).range = alternatingGroup (Fin 6) ∨
      (ρ.comp (Subgroup.inclusion hLTN)).range = ⊤)
    {x : Equiv.Perm (Fin 6)} (hx : x ∈ sylowS6) (hxA : x ∈ alternatingGroup (Fin 6)) :
    ∃ t, ∃ ht : t ∈ T, ρ ⟨t, hLTN (Subgroup.mem_sup_right ht)⟩ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := ρ.comp (Subgroup.inclusion hLTN) with hf
  set H := f.range with hHdef
  set I := (T.subgroupOf (L ⊔ T)).map f with hI
  have hle : I ≤ sylowS6 := by
    rintro _ ⟨y, hy, rfl⟩
    exact hρT y hy
  have hIH : I ≤ H := Subgroup.map_le_range f _
  have hodd : ¬ 2 ∣ (I.subgroupOf H).index := by
    have h1 := Subgroup.index_map_dvd (H := T.subgroupOf (L ⊔ T)) f.rangeRestrict_surjective
    have h2 : (T.subgroupOf (L ⊔ T)).map f.rangeRestrict = I.subgroupOf H := by
      ext y
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, hzy⟩
        exact ⟨z, hz, Subtype.ext hzy⟩
    rw [h2] at h1
    exact fun h3 => hTidx ((h3.trans h1).trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))
  have hmul : Nat.card I * (I.subgroupOf H).index = Nat.card H := by
    have := Subgroup.card_mul_index (I.subgroupOf H)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIH).toEquiv] at this
  have hdvd : Nat.card I ∣ 16 := by
    rw [← S6Syl.card_sylowS6]
    exact Subgroup.card_dvd_of_le hle
  have h720 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hA360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    have := two_mul_nat_card_alternatingGroup (α := Fin 6)
    rw [h720] at this
    omega
  have h45 : Equiv.swap (4 : Fin 6) 5 ∈ sylowS6 :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hSA : 2 * Nat.card ↥(sylowS6 ⊓ alternatingGroup (Fin 6)) = 16 := by
    rw [two_mul_card_inf_alternatingGroup h45 (Equiv.Perm.sign_swap (by decide)),
      S6Syl.card_sylowS6]
  obtain ⟨c, hc⟩ : ∃ c, Nat.card I = c := ⟨_, rfl⟩
  rw [hc] at hmul hdvd
  have hc16 : c ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
  have hmem : x ∈ I := by
    rcases hH with hHA | hHT
    · have hcard : Nat.card H = 360 := by rw [hHA, hA360]
      rw [hcard] at hmul
      have hc8 : c = 8 := by interval_cases c <;> omega
      have hIA : I ≤ sylowS6 ⊓ alternatingGroup (Fin 6) := le_inf hle (hHA ▸ hIH)
      have hIeq : I = sylowS6 ⊓ alternatingGroup (Fin 6) :=
        Subgroup.eq_of_le_of_card_ge hIA (by rw [hc, hc8]; omega)
      rw [hIeq]
      exact ⟨hx, hxA⟩
    · have hcard : Nat.card H = 720 := by rw [hHT, Subgroup.card_top, h720]
      rw [hcard] at hmul
      have hc16' : c = 16 := by interval_cases c <;> omega
      have hIeq : I = sylowS6 :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hc16', S6Syl.card_sylowS6])
      rw [hIeq]
      exact hx
  obtain ⟨y, hy, hyx⟩ := hmem
  exact ⟨y, hy, hyx⟩

theorem exists_rho_cZ
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hA6 : IsAltBlockType L 6)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ ρ : ↥(Subgroup.normalizer (L : Set G)) →* Equiv.Perm (Fin 6),
      ∃ β : ↥(blockU L) →* Multiplicative A6Coc.Vec4,
      Function.Surjective β ∧ β.ker = (blockZ L).subgroupOf (blockU L) ∧
      (∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
        (u' : G) = g * u * g⁻¹ →
          Multiplicative.toAdd (β u') = A6Coc.act (ρ g) (Multiplicative.toAdd (β u))) ∧
      (∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ ∈ sylowS6) ∧
      (∀ s ∈ alternatingGroup (Fin 6), ∃ ℓ, ∃ hℓ : ℓ ∈ L,
        ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = s) ∧
      (∀ ℓ (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ ∈ alternatingGroup (Fin 6)) ∧
      (∀ g, g ∈ L ⊔ T → ∀ hgN : g ∈ Subgroup.normalizer (L : Set G),
        (ρ ⟨g, hgN⟩ = 1 ↔ g ∈ Subgroup.centralizer (vPlus L T : Set G))) ∧
      (∀ g, g ∈ L ⊔ T → ∀ hgN : g ∈ Subgroup.normalizer (L : Set G), ρ ⟨g, hgN⟩ = 1 →
        g ∈ qL L T) ∧
      oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) =
        oTwoUpper (pre ρ (sup_le Subgroup.le_normalizer hTL) p1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hshort, α, hA⟩ := id hA6
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hQV : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hUV : blockU L ≤ vPlus L T := h.blockU_le_vPlus h38 h39 hshort hTL
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  obtain ⟨ρ, β', hβs', hβk', hβe', hρT, hρLA, hρL, hK⟩ := exists_rho hA hTL hT2
  have hcent : ∀ g (hgN : g ∈ Subgroup.normalizer (L : Set G)),
      (∀ u ∈ blockU L, g * u * g⁻¹ = u) → ρ ⟨g, hgN⟩ = 1 := by
    intro g hgN hu
    apply A6Coc.eq_of_heartAct_eq
    intro y
    rw [heartAct_one]
    obtain ⟨u, hu'⟩ := hβs' (Multiplicative.ofAdd y)
    have hy : y = Multiplicative.toAdd (β' u) := by rw [hu']; rfl
    rw [hy]
    exact (hβe' ⟨g, hgN⟩ u u (hu u u.2).symm).symm
  let β'' : ↥(blockU L) →* Multiplicative A6Coc.Vec4 :=
    (AddMonoidHom.toMultiplicative A6Coc.eps).comp β'
  have hβs'' : Function.Surjective β'' := by
    intro y
    obtain ⟨u, hu⟩ := hβs' (Multiplicative.ofAdd (A6Coc.epsInv (Multiplicative.toAdd y)))
    refine ⟨u, Multiplicative.toAdd.injective ?_⟩
    show A6Coc.eps (Multiplicative.toAdd (β' u)) = Multiplicative.toAdd y
    rw [hu]
    exact A6Coc.eps_epsInv _
  have hβe'' : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ →
        Multiplicative.toAdd (β'' u') = A6Coc.act (ρ g) (Multiplicative.toAdd (β'' u)) := by
    intro g u u' hu'
    show A6Coc.eps (Multiplicative.toAdd (β' u')) =
      A6Coc.act (ρ g) (A6Coc.eps (Multiplicative.toAdd (β' u)))
    rw [hβe' g u u' hu', A6Coc.eps_heartAct]
  have hβk'' : β''.ker = (blockZ L).subgroupOf (blockU L) := by
    rw [← hβk']
    ext u
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h1
      apply Multiplicative.toAdd.injective
      apply A6Coc.eps_injective
      rw [toAdd_one, map_zero]
      exact congrArg Multiplicative.toAdd h1
    · intro h1
      show Multiplicative.ofAdd (A6Coc.eps (Multiplicative.toAdd (β' u))) = 1
      rw [h1, toAdd_one, map_zero]
      rfl
  have hHrange := eq_alternatingGroup_or_eq_top (H := (ρ.comp (Subgroup.inclusion hLTN)).range)
    (fun s hs => by
      obtain ⟨ℓ, hℓ, e⟩ := hρL s hs
      exact ⟨⟨ℓ, Subgroup.mem_sup_left hℓ⟩, e⟩)
  obtain ⟨t₁, ht₁, e₁⟩ := mem_image_sylow ρ hLTN hTidx (fun t ht => hρT t ht) hHrange
    b1_mem_sylowS6 b1_mem_alt
  obtain ⟨t₂, ht₂, e₂⟩ := mem_image_sylow ρ hLTN hTidx (fun t ht => hρT t ht) hHrange
    s1_mem_sylowS6 s1_mem_alt
  refine ⟨ρ, β'', hβs'', hβk'', hβe'', hρT, hρL, hρLA, fun g hg hgN =>
    ⟨fun h1 => hQV (hK g hg hgN h1), fun h1 => hcent g hgN fun u hu => ?_⟩, hK, ?_⟩
  · have hc := Subgroup.mem_centralizer_iff.mp h1 u (hUV hu)
    calc g * u * g⁻¹ = u * g * g⁻¹ := by rw [← hc]
      _ = u := by group
  refine CZCore.cZ_core h38 h39 h hshort hTL ρ β'' hβk'' A6Coc.act A6Coc.act_zero hβe''
    (fun v hv => ?_) (fun x hx => mem_p1_of_act_w0 hx) (fun x hx => act_w0_of_mem_p1 hx)
  apply fix_D8
  · rw [← e₁]
    exact hv t₁ ht₁
  · rw [← e₂]
    exact hv t₂ ht₂

@[expose] def c012 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def c123 : Equiv.Perm (Fin 6) := Equiv.swap 1 2 * Equiv.swap 2 3

theorem c012_mem_alt : c012 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, c012]
  exact sign_pair (by decide) (by decide)

theorem c123_mem_alt : c123 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, c123]
  exact sign_pair (by decide) (by decide)

theorem c012_mem_p1 : c012 ∈ p1 := mem_p1_of_fix (by decide) (by decide)

theorem c123_mem_p1 : c123 ∈ p1 := mem_p1_of_fix (by decide) (by decide)

theorem centralizer_check : ∀ x ∈ S6Syl.elemsS, x * c012 = c012 * x → x * c123 = c123 * x →
    x = 1 ∨ x = Equiv.swap 4 5 := by
  decide +kernel

theorem commute_of_commute_pow {x c : Equiv.Perm (Fin 6)} (hc : c * (c * c) = 1) (k : ℕ)
    (h : x * c ^ 2 ^ k = c ^ 2 ^ k * x) : x * c = c * x := by
  have hc3 : c ^ 3 = 1 := by rw [pow_three]; exact hc
  have h2 : ∀ k : ℕ, c ^ 2 ^ k = c ∨ c ^ 2 ^ k = c * c := by
    intro k
    induction k with
    | zero => left; rw [pow_zero, pow_one]
    | succ k ih =>
      rw [pow_succ, pow_mul]
      rcases ih with e | e
      · right; rw [e, sq]
      · left
        rw [e, sq]
        calc c * c * (c * c) = c ^ 3 * c := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
          _ = c := by rw [hc3, one_mul]
  rcases h2 k with e | e
  · rwa [e] at h
  · rw [e] at h
    have h4 : c = c * c * (c * c) := by
      calc c = c ^ 3 * c := by rw [hc3, one_mul]
        _ = c * c * (c * c) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [h4]
    calc x * (c * c * (c * c)) = (x * (c * c)) * (c * c) := by group
      _ = (c * c * x) * (c * c) := by rw [h]
      _ = c * c * (x * (c * c)) := by group
      _ = c * c * (c * c * x) := by rw [h]
      _ = c * c * (c * c) * x := by group

theorem xs3_a6
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hA6 : IsAltBlockType L 6) :
    Nonempty (↥(oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) ⧸
      CFSG.pCore 2
        ↥(oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) ≃*
      Equiv.Perm (Fin 3)) := by
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  obtain ⟨ρ, -, -, -, -, hρT, hρL, -, -, hK, hX⟩ := exists_rho_cZ h38 h39 h hA6 hTL
  have hH := eq_alternatingGroup_or_eq_top (H := (ρ.comp (Subgroup.inclusion hLTN)).range)
    (fun s hs => by
      obtain ⟨ℓ, hℓ, e⟩ := hρL s hs
      exact ⟨⟨ℓ, Subgroup.mem_sup_left hℓ⟩, e⟩)
  obtain ⟨-, -, hXT, ⟨e⟩, -, -⟩ := parabolic ρ hLTN hT2 hTidx
    (fun g hg h1 => hK g hg (hLTN hg) h1) (fun t ht => hρT t ht) hρL hH
    sylowS6_le_p1 r1_le_p1 p1_le_normalizer (fun x hx => sq_eq_one_of_mem_r1 hx) card_p1 card_r1
    c45_mem_r1 s1_mem_alt t1_mem_alt s1_mem_p1 t1_mem_p1 comm_not_mem_r1
  exact nonempty_quot_pCore_congr (by rw [hX, hXT]) ⟨e⟩

theorem insp3_3_27_a6
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hA6 : IsAltBlockType L 6) {z₁ z₂ : MulAut ↥(vPlus L T)}
    (hz₁ : z₁ ∈ autOn T (vPlus L T)) (hz₂ : z₂ ∈ autOn T (vPlus L T)) (hn₁ : z₁ ≠ 1)
    (hn₂ : z₂ ≠ 1)
    (hy₁ : ∀ y ∈ autOn (oTwoUpper (L ⊓ Subgroup.centralizer
      (quasithinOmegaOneCenter T : Set G))) (vPlus L T), z₁ * y = y * z₁)
    (hy₂ : ∀ y ∈ autOn (oTwoUpper (L ⊓ Subgroup.centralizer
      (quasithinOmegaOneCenter T : Set G))) (vPlus L T), z₂ * y = y * z₂) : z₁ = z₂ := by
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := hred.2.2.2.1
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  obtain ⟨ρ, -, -, -, -, hρT, hρL, -, hker, -, hX⟩ := exists_rho_cZ h38 h39 h hA6 hTL
  have hconj : ∀ (a b : G) (ha : a ∈ L ⊔ T) (hb : b ∈ L ⊔ T),
      conjAct (vPlus L T) ⟨a, hLTV ha⟩ = conjAct (vPlus L T) ⟨b, hLTV hb⟩ ↔
        ρ ⟨a, hLTN ha⟩ = ρ ⟨b, hLTN hb⟩ := by
    intro a b ha hb
    have hab : a⁻¹ * b ∈ L ⊔ T := (L ⊔ T).mul_mem ((L ⊔ T).inv_mem ha) hb
    have e1 : (conjAct (vPlus L T) ⟨a, hLTV ha⟩)⁻¹ * conjAct (vPlus L T) ⟨b, hLTV hb⟩ =
        conjAct (vPlus L T) ⟨a⁻¹ * b, hLTV hab⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    have e2 : (ρ ⟨a, hLTN ha⟩)⁻¹ * ρ ⟨b, hLTN hb⟩ = ρ ⟨a⁻¹ * b, hLTN hab⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [← inv_mul_eq_one, e1, A4.conjAct_eq_one_iff, ← inv_mul_eq_one, e2]
    exact (hker _ hab _).symm
  have key : ∀ z : MulAut ↥(vPlus L T), z ∈ autOn T (vPlus L T) → z ≠ 1 →
      (∀ y ∈ autOn (oTwoUpper (L ⊓ Subgroup.centralizer
        (quasithinOmegaOneCenter T : Set G))) (vPlus L T), z * y = y * z) →
      ∃ t, ∃ ht : t ∈ T, z = conjAct (vPlus L T) ⟨t, hLTV (Subgroup.mem_sup_right ht)⟩ ∧
        ρ ⟨t, hLTN (Subgroup.mem_sup_right ht)⟩ = Equiv.swap 4 5 := by
    intro z hz hn hy
    obtain ⟨g, hgT, rfl⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.mp hz
    refine ⟨g, hgT, rfl, ?_⟩
    have hgLT : (g : G) ∈ L ⊔ T := Subgroup.mem_sup_right hgT
    have hcomm : ∀ c ∈ alternatingGroup (Fin 6), c ∈ p1 → c * (c * c) = 1 →
        ρ ⟨g, hLTN hgLT⟩ * c = c * ρ ⟨g, hLTN hgLT⟩ := by
      intro c hcA hcp hc3
      obtain ⟨ℓ, hℓ, hρℓ⟩ := hρL c hcA
      have hℓLT : ℓ ∈ L ⊔ T := Subgroup.mem_sup_left hℓ
      have hℓP : ℓ ∈ pre ρ hLTN p1 := (mem_pre ρ hLTN).mpr ⟨hℓLT, hρℓ ▸ hcp⟩
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper _ hℓP
      rw [← hX] at hk
      have hkLT : ℓ ^ 2 ^ k ∈ L ⊔ T := (L ⊔ T).pow_mem hℓLT _
      have hyk := hy (conjAct (vPlus L T) ⟨ℓ ^ 2 ^ k, hLTV hkLT⟩)
        (CFSG.QuasithinUnique.Setup.mem_autOn_iff.mpr ⟨⟨ℓ ^ 2 ^ k, hLTV hkLT⟩, hk, rfl⟩)
      have hgk : (g : G) * ℓ ^ 2 ^ k ∈ L ⊔ T := (L ⊔ T).mul_mem hgLT hkLT
      have hkg : ℓ ^ 2 ^ k * (g : G) ∈ L ⊔ T := (L ⊔ T).mul_mem hkLT hgLT
      have e1 : conjAct (vPlus L T) ⟨(g : G) * ℓ ^ 2 ^ k, hLTV hgk⟩ =
          conjAct (vPlus L T) ⟨ℓ ^ 2 ^ k * (g : G), hLTV hkg⟩ := by
        rw [show (⟨(g : G) * ℓ ^ 2 ^ k, hLTV hgk⟩ : ↥(Subgroup.normalizer (vPlus L T : Set G))) =
            g * ⟨ℓ ^ 2 ^ k, hLTV hkLT⟩ from rfl,
          show (⟨ℓ ^ 2 ^ k * (g : G), hLTV hkg⟩ : ↥(Subgroup.normalizer (vPlus L T : Set G))) =
            ⟨ℓ ^ 2 ^ k, hLTV hkLT⟩ * g from rfl, map_mul, map_mul]
        exact hyk
      have e2 := (hconj _ _ hgk hkg).mp e1
      rw [show (⟨(g : G) * ℓ ^ 2 ^ k, hLTN hgk⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          ⟨g, hLTN hgLT⟩ * ⟨ℓ, hLTN hℓLT⟩ ^ 2 ^ k from rfl,
        show (⟨ℓ ^ 2 ^ k * (g : G), hLTN hkg⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          ⟨ℓ, hLTN hℓLT⟩ ^ 2 ^ k * ⟨g, hLTN hgLT⟩ from rfl, map_mul, map_mul, map_pow,
        show ρ ⟨ℓ, hLTN hℓLT⟩ = c from hρℓ] at e2
      exact commute_of_commute_pow hc3 k e2
    have h1 := hcomm c012 c012_mem_alt c012_mem_p1 (by decide)
    have h2 := hcomm c123 c123_mem_alt c123_mem_p1 (by decide)
    have hS : ρ ⟨g, hLTN hgLT⟩ ∈ S6Syl.elemsS := by
      have := hρT g hgT
      rw [S6Syl.sylowS6_eq] at this
      exact this
    rcases centralizer_check _ hS h1 h2 with h0 | h0
    · exfalso
      apply hn
      have := (hconj (g : G) 1 hgLT (L ⊔ T).one_mem).mpr (by rw [h0]; exact (map_one ρ).symm)
      rw [this]
      exact map_one _
    · exact h0
  obtain ⟨t₁, ht₁, rfl, e₁⟩ := key z₁ hz₁ hn₁ hy₁
  obtain ⟨t₂, ht₂, rfl, e₂⟩ := key z₂ hz₂ hn₂ hy₂
  exact (hconj t₁ t₂ (Subgroup.mem_sup_right ht₁) (Subgroup.mem_sup_right ht₂)).mpr
    (e₁.trans e₂.symm)

@[expose] def Fact3_3_25XS3Rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    T ≤ Subgroup.normalizer (L : Set G) → (CFSG.Quasithin.IsHatA6Block L ∨ IsG2Block L) →
    Nonempty (↥(oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) ⧸
      CFSG.pCore 2
        ↥(oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) ≃*
      Equiv.Perm (Fin 3))

theorem fact3_3_25XS3_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hR : Fact3_3_25XS3Rest) : Fact3_3_25XS3 := by
  intro G _ _ T M L D h hTL hb
  rcases hb with hA | hH | hG | hLn
  · exact xs3_a6 h38 h39 h hTL hA
  · exact hR G T M L D h hTL (Or.inl hH)
  · exact hR G T M L D h hTL (Or.inr hG)
  · exact CZL32.xs3_l32 h38 h39 h hTL hLn

@[expose] def Insp3_3_27Rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    T ≤ Subgroup.normalizer (L : Set G) → IsG2Block L →
    ∀ z₁ ∈ autOn T (vPlus L T), ∀ z₂ ∈ autOn T (vPlus L T),
      (∀ s ∈ autOn T (vPlus L T), z₁ * s = s * z₁) →
      (∀ s ∈ autOn T (vPlus L T), z₂ * s = s * z₂) → z₁ ^ 2 = 1 → z₂ ^ 2 = 1 → z₁ ≠ 1 →
      z₂ ≠ 1 →
      (∀ y ∈ autOn (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)))
          (vPlus L T), z₁ * y = y * z₁) →
      (∀ y ∈ autOn (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)))
          (vPlus L T), z₂ * y = y * z₂) → z₁ = z₂

theorem insp3_3_27_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hR : Insp3_3_27Rest) : Insp3_3_27 := by
  intro G _ _ T M L D h hTL hblock hP z₁ hz₁ z₂ hz₂ hc₁ hc₂ h2₁ h2₂ hn₁ hn₂ hy₁ hy₂
  rcases hblock with hA | hG | hLn
  · exact insp3_3_27_a6 h38 h39 h hTL hA hz₁ hz₂ hn₁ hn₂ hy₁ hy₂
  · exact hR G T M L D h hTL hG z₁ hz₁ z₂ hz₂ hc₁ hc₂ h2₁ h2₂ hn₁ hn₂ hy₁ hy₂
  · exact absurd (h.isPSL_of_isLnBlock h38 h39 hTL hLn) hP

end CZA6

end CFSG.Quasithin.H13

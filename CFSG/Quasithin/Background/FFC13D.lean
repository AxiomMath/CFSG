module

public import CFSG.Quasithin.Background.FFC12E

public section

namespace CFSG.Quasithin

open scoped commutatorElement

namespace B69

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem mem_M_of_conj_closed {X T M L : Subgroup (MulAut V)} (hmp : MinParabolic X T M)
    (hO2 : CFSG.Open.pCoreOf 2 X = ⊥) (hL : CFSG.Open.IsComponentOf L X)
    (hTL : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L) {b : MulAut V} (hbX : b ∈ X)
    (hbn : ∀ y ∈ T ⊓ L, b * y * b⁻¹ ∈ T ⊓ L) (hbn' : ∀ y ∈ T ⊓ L, b⁻¹ * y * b ∈ T ⊓ L)
    (hbc : ∀ L' : Subgroup (MulAut V), CFSG.Open.IsComponentOf L' X → L ≠ L' →
      ∀ z ∈ L', z * b = b * z) : b ∈ M := by
  set gens : Set (MulAut V) := {y | y ∈ T ∧ ∃ L' : Subgroup (MulAut V),
    CFSG.Open.IsComponentOf L' X ∧ y ∈ L'} with hgens
  set U : Subgroup (MulAut V) := Subgroup.closure gens with hU
  have hUT : U ≤ T := (Subgroup.closure_le T).2 fun y hy => hy.1
  have hUX : U ≤ X := hUT.trans hmp.isSylow.1
  have hU2 : IsPGroup 2 ↥U := hmp.isSylow.2.1.to_le hUT
  have hTn : T ≤ Subgroup.normalizer (U : Set (MulAut V)) := by
    intro t ht
    have htX : t ∈ X := hmp.isSylow.1 ht
    have htX' : t⁻¹ ∈ X := X.inv_mem htX
    refine mem_normalizer_closure_of_gens (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨hyT, L', hL', hyL'⟩ := hy
      refine Subgroup.subset_closure ⟨T.mul_mem (T.mul_mem ht hyT) (T.inv_mem ht),
        B6.conjSub t L', B113.isComponentOf_conj hL' htX, ?_⟩
      rw [B6.mem_conjSub]
      have : t⁻¹ * (t * y * t⁻¹) * t = y := by group
      rw [this]
      exact hyL'
    · obtain ⟨hyT, L', hL', hyL'⟩ := hy
      refine Subgroup.subset_closure ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hyT) ht,
        B6.conjSub t⁻¹ L', B113.isComponentOf_conj hL' htX', ?_⟩
      rw [B6.mem_conjSub]
      have : (t⁻¹)⁻¹ * (t⁻¹ * y * t) * t⁻¹ = y := by group
      rw [this]
      exact hyL'
  have hTLne : T ⊓ L ≠ ⊥ := by
    intro hbot
    have h := hTL.2.2
    rw [hbot, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h
    exact not_odd_card_quasisimple hL.2.2 (Nat.odd_iff.2 (by omega))
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply hTLne
    rw [eq_bot_iff]
    intro y hy
    have : y ∈ U := Subgroup.subset_closure ⟨hy.1, L, hL, hy.2⟩
    rw [hbot] at this
    exact this
  have hXn : ¬ X ≤ Subgroup.normalizer (U : Set (MulAut V)) := by
    intro hn
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUX hn hU2
    rw [hO2] at this
    exact hUne (le_bot_iff.1 this)
  set R : Subgroup (MulAut V) := X ⊓ Subgroup.normalizer (U : Set (MulAut V)) with hR
  have hTR : T ≤ R := le_inf hmp.isSylow.1 hTn
  have hRX : R < X := lt_of_le_of_ne inf_le_left (fun h => hXn (h ▸ inf_le_right))
  have hRM : R ≤ M := hmp.le_of_lt hTR hRX
  have key : ∀ c : MulAut V, (∀ y ∈ T ⊓ L, c * y * c⁻¹ ∈ T ⊓ L) →
      (∀ L' : Subgroup (MulAut V), CFSG.Open.IsComponentOf L' X → L ≠ L' →
        ∀ z ∈ L', z * c = c * z) → ∀ y ∈ gens, c * y * c⁻¹ ∈ U := by
    intro c hcn hcc y hy
    obtain ⟨hyT, L', hL', hyL'⟩ := hy
    by_cases hLL' : L = L'
    · subst hLL'
      have h1 : c * y * c⁻¹ ∈ T ⊓ L := hcn y ⟨hyT, hyL'⟩
      exact Subgroup.subset_closure ⟨h1.1, L, hL, h1.2⟩
    · have hcomm : y * c = c * y := hcc L' hL' hLL' y hyL'
      have h1 : c * y * c⁻¹ = y := by
        calc c * y * c⁻¹ = (y * c) * c⁻¹ := by rw [hcomm]
          _ = y := by group
      rw [h1]
      exact Subgroup.subset_closure ⟨hyT, L', hL', hyL'⟩
  have hbc' : ∀ L' : Subgroup (MulAut V), CFSG.Open.IsComponentOf L' X → L ≠ L' →
      ∀ z ∈ L', z * b⁻¹ = b⁻¹ * z := fun L' hL' hne z hz =>
    Commute.inv_right (hbc L' hL' hne z hz)
  have hbn'' : ∀ y ∈ T ⊓ L, b⁻¹ * y * b⁻¹⁻¹ ∈ T ⊓ L := fun y hy => by
    rw [inv_inv]
    exact hbn' y hy
  have hbU : b ∈ Subgroup.normalizer (U : Set (MulAut V)) :=
    mem_normalizer_closure_of_gens (key b hbn hbc)
      (fun y hy => by simpa using key b⁻¹ hbn'' hbc' y hy)
  exact hRM ⟨hbX, hbU⟩

theorem commute_of_mem_sup_of_ne {X L A : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L X)
    (hAc : ∀ L' : Subgroup (MulAut V), CFSG.Open.IsComponentOf L' X → L ≠ L' → ⁅L', A⁆ = ⊥)
    {L' : Subgroup (MulAut V)} (hL' : CFSG.Open.IsComponentOf L' X) (hne : L ≠ L')
    {b : MulAut V} (hb : b ∈ L ⊔ A) : ∀ z ∈ L', z * b = b * z := by
  have hLc : L ≤ Subgroup.centralizer (L' : Set (MulAut V)) := fun l hl =>
    Subgroup.mem_centralizer_iff.2 fun z hz => components_mul_comm_of_ne hL hL' hne z hz l hl
  have hAc' : A ≤ Subgroup.centralizer (L' : Set (MulAut V)) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun z hz =>
      mul_comm_of_commutator_eq_bot (hAc L' hL' hne) z hz a ha
  exact Subgroup.mem_centralizer_iff.1 ((sup_le hLc hAc') hb)

end Main

theorem nat_card_eq_four_of_isSylowTwoOf_sixty {G : Type*} [Group G] [Finite G] {Q L : Subgroup G}
    (hQ : CFSG.QuasithinUnique.IsSylowTwoOf Q L) (hL : Nat.card L = 60) : Nat.card Q = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQ.2.1
  have hmul := Subgroup.card_mul_index (Q.subgroupOf L)
  have hcard : Nat.card (Q.subgroupOf L) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ.1).toEquiv
  rw [hcard, hk, hL] at hmul
  have hodd := hQ.2.2
  have hk6 : k < 6 := by
    by_contra hk6
    have h64 : 2 ^ 6 ∣ 2 ^ k := pow_dvd_pow 2 (not_lt.1 hk6)
    have h60 : 2 ^ k ∣ 60 := ⟨_, hmul.symm⟩
    have := Nat.le_of_dvd (by norm_num) (h64.trans h60)
    omega
  rw [hk]
  interval_cases k <;> omega

theorem mStructure_of {V : Type} [CommGroup V] [Finite V] {X T M A L : Subgroup (MulAut V)}
    (hmp : MinParabolic X T M) (hO2 : CFSG.Open.pCoreOf 2 X = ⊥)
    (hL : CFSG.Open.IsComponentOf L X) (hAX : A ≤ X)
    (hAc : ∀ L' : Subgroup (MulAut V), CFSG.Open.IsComponentOf L' X → L ≠ L' → ⁅L', A⁆ = ⊥)
    (π' : Equiv.Perm (Fin 5) →* ↥(L ⊔ A)) (hπ'i : Function.Injective π')
    (hπ's : Function.Surjective π')
    (hLeq : L = (alternatingGroup (Fin 5)).map ((L ⊔ A).subtype.comp π'))
    (hN : ∀ V₀ : Subgroup (Equiv.Perm (Fin 5)), V₀ ≤ alternatingGroup (Fin 5) → Nat.card V₀ = 4 →
      ∃ p : Fin 5, ∀ σ : Equiv.Perm (Fin 5),
        σ ∈ Subgroup.normalizer (V₀ : Set (Equiv.Perm (Fin 5))) ↔ σ p = p)
    (hmax : ∀ (p : Fin 5) (R : Subgroup (Equiv.Perm (Fin 5))),
      MulAction.stabilizer (Equiv.Perm (Fin 5)) p ≤ R →
        R = MulAction.stabilizer (Equiv.Perm (Fin 5)) p ∨ R = ⊤) :
    ∃ ρ : Equiv.Perm (Fin 5), (M ⊓ (L ⊔ A)).subgroupOf (L ⊔ A) =
      (MulAction.stabilizer (Equiv.Perm (Fin 5)) (⟨0, by omega⟩ : Fin 5)).map
        (π'.comp (MulAut.conj ρ).toMonoidHom) := by
  have hLAX : L ⊔ A ≤ X := sup_le hL.1 hAX
  have hTL : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    A312.isSylowTwoOf_inf_of_subnormal hL.2.1 hmp.isSylow
  set φ : Equiv.Perm (Fin 5) →* MulAut V := (L ⊔ A).subtype.comp π' with hφ
  have hφi : Function.Injective φ := fun a b h => hπ'i (Subtype.ext h)
  have hφmem : ∀ σ, φ σ ∈ L ⊔ A := fun σ => (π' σ).2
  have hLφ : ∀ x ∈ L, ∃ τ ∈ alternatingGroup (Fin 5), φ τ = x := fun x hx =>
    Subgroup.mem_map.1 (hLeq.le hx)
  set V₀ : Subgroup (Equiv.Perm (Fin 5)) := (T ⊓ L).comap φ with hV₀
  have hV₀A : V₀ ≤ alternatingGroup (Fin 5) := by
    intro σ hσ
    obtain ⟨τ, hτ, hτσ⟩ := hLφ (φ σ) (hσ : φ σ ∈ T ⊓ L).2
    rwa [← hφi hτσ]
  have hV₀map : V₀.map φ = T ⊓ L := by
    ext x
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact hσ
    · intro hx
      obtain ⟨τ, -, hτ⟩ := hLφ x hx.2
      have hτ' : φ τ ∈ T ⊓ L := by rw [hτ]; exact hx
      exact ⟨τ, hτ', hτ⟩
  have hLcard : Nat.card L = 60 := by
    rw [congrArg (fun K : Subgroup (MulAut V) => Nat.card ↥K) hLeq,
      Subgroup.card_map_of_injective hφi, nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card, Nat.factorial]
  have hV₀card : Nat.card V₀ = 4 :=
    calc Nat.card V₀ = Nat.card (V₀.map φ) := (Subgroup.card_map_of_injective hφi).symm
      _ = Nat.card (T ⊓ L : Subgroup (MulAut V)) := by rw [hV₀map]
      _ = 4 := nat_card_eq_four_of_isSylowTwoOf_sixty hTL hLcard
  obtain ⟨p, hp⟩ := hN V₀ hV₀A hV₀card
  have hStab : ∀ σ : Equiv.Perm (Fin 5), σ p = p → φ σ ∈ M := by
    intro σ hσ
    have hσ' : σ⁻¹ p = p := by
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
      exact hσ.symm
    have hnσ := Subgroup.mem_normalizer_iff.1 ((hp σ).2 hσ)
    have hnσ' := Subgroup.mem_normalizer_iff.1 ((hp σ⁻¹).2 hσ')
    refine mem_M_of_conj_closed hmp hO2 hL hTL (hLAX (hφmem σ)) ?_ ?_ ?_
    · intro y hy
      obtain ⟨τ, -, rfl⟩ := hLφ y hy.2
      have h : φ (σ * τ * σ⁻¹) ∈ T ⊓ L := (hnσ τ).1 hy
      simpa only [map_mul, map_inv] using h
    · intro y hy
      obtain ⟨τ, -, rfl⟩ := hLφ y hy.2
      have h : φ (σ⁻¹ * τ * σ⁻¹⁻¹) ∈ T ⊓ L := (hnσ' τ).1 hy
      simpa only [map_mul, map_inv, inv_inv] using h
    · intro L' hL' hne z hz
      exact commute_of_mem_sup_of_ne hL hAc hL' hne (hφmem σ) z hz
  set R : Subgroup (Equiv.Perm (Fin 5)) := M.comap φ with hR
  have hSR : MulAction.stabilizer (Equiv.Perm (Fin 5)) p ≤ R := fun σ hσ =>
    hStab σ (MulAction.mem_stabilizer_iff.1 hσ)
  have hRtop : R ≠ ⊤ := by
    intro htop
    apply not_component_le_M hmp hO2 hL
    intro x hx
    obtain ⟨τ, -, rfl⟩ := hLφ x hx
    have : τ ∈ R := htop ▸ Subgroup.mem_top τ
    exact this
  have hReq : R = MulAction.stabilizer (Equiv.Perm (Fin 5)) p :=
    (hmax p R hSR).resolve_right hRtop
  have hσR : ∀ σ : Equiv.Perm (Fin 5), φ σ ∈ M ↔ σ p = p := by
    intro σ
    have h : σ ∈ R ↔ σ ∈ MulAction.stabilizer (Equiv.Perm (Fin 5)) p := by rw [hReq]
    exact h.trans MulAction.mem_stabilizer_iff
  set a : Fin 5 := ⟨0, by omega⟩ with ha
  have hρa : Equiv.swap a p a = p := Equiv.swap_apply_left a p
  have hρp : Equiv.swap a p p = a := Equiv.swap_apply_right a p
  have hρρ : Equiv.swap a p * Equiv.swap a p = 1 := Equiv.swap_mul_self a p
  have hρi : (Equiv.swap a p)⁻¹ = Equiv.swap a p := Equiv.swap_inv a p
  refine ⟨Equiv.swap a p, ?_⟩
  ext x
  obtain ⟨σ, rfl⟩ := hπ's x
  constructor
  · intro hx
    have hσ : σ p = p := (hσR σ).1 hx.1
    refine ⟨Equiv.swap a p * σ * Equiv.swap a p, ?_, ?_⟩
    · show (Equiv.swap a p * σ * Equiv.swap a p) a = a
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hρa, hσ, hρp]
    · show π' (MulAut.conj (Equiv.swap a p) (Equiv.swap a p * σ * Equiv.swap a p)) = π' σ
      rw [MulAut.conj_apply]
      have : Equiv.swap a p * (Equiv.swap a p * σ * Equiv.swap a p) * (Equiv.swap a p)⁻¹ =
          (Equiv.swap a p * Equiv.swap a p) * σ := by group
      rw [this, hρρ, one_mul]
  · rintro ⟨τ, hτ, hτσ⟩
    have h1 : MulAut.conj (Equiv.swap a p) τ = σ := hπ'i hτσ
    rw [MulAut.conj_apply, hρi] at h1
    have hτa : τ a = a := MulAction.mem_stabilizer_iff.1 hτ
    have hσp : σ p = p := by
      rw [← h1, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hρp, hτa, hρa]
    exact ⟨(hσR σ).2 hσp, (π' σ).2⟩

end B69

end CFSG.Quasithin

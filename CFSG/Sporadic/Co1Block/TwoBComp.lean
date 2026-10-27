module

public import CFSG.Sporadic.Co1Block.TwoBD

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

abbrev ιC : C₁ →* GL24 := GA.subtype.comp C₁.subtype

theorem ιC_injective : Function.Injective ιC :=
  GA.subtype_injective.comp C₁.subtype_injective

@[expose] def liftC (g : GL24) (hg : g ∈ GA ⊓ Subgroup.centralizer {A₁}) : C₁ :=
  ⟨⟨g, (Subgroup.mem_inf.1 hg).1⟩, mem_C₁_of (Subgroup.mem_inf.1 hg).2⟩

theorem ιC_liftC (g : GL24) (hg : g ∈ GA ⊓ Subgroup.centralizer {A₁}) : ιC (liftC g hg) = g :=
  rfl

theorem C₁_induction
    (M : Submonoid C₁)
    (hS : ∀ c : C₁, ιC c ∈ brayEltsG A₁ twoBD1 twoBBray → c ∈ M) (c : C₁) : c ∈ M := by
  have hc : ιC c ∈ Submonoid.closure {g | g ∈ brayEltsG A₁ twoBD1 twoBBray} := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    have h := coe_mem_C₁ c
    rw [← twoBE_eq] at h
    exact h
  have hle : Submonoid.closure {g | g ∈ brayEltsG A₁ twoBD1 twoBBray} ≤ M.map ιC := by
    rw [Submonoid.closure_le]
    intro g hg
    have hgE : g ∈ GA ⊓ Subgroup.centralizer {A₁} := twoBE_le (Subgroup.subset_closure hg)
    exact ⟨liftC g hgE, hS _ hg, rfl⟩
  obtain ⟨c', hc', he⟩ := hle hc
  rwa [ιC_injective he] at hc'

attribute [local instance] triMulAction

theorem conj_mem_of_closure {G : Type*} [Group G] {s : Set G} {K : Subgroup G} (u : G)
    (hs : ∀ x ∈ s, u * x * u⁻¹ ∈ K) {d : G} (hd : d ∈ Subgroup.closure s) : u * d * u⁻¹ ∈ K :=
  (Subgroup.closure_le (K.comap (MulAut.conj u).toMonoidHom)).2 hs hd

theorem conjArr_rep {σ g : Array ℕ} {S G : Equiv.Perm (Fin 1365)} (hσ : Rep 1365 σ S)
    (hinv : isInvA 1365 σ (invCand 1365 σ) = true) (hg : Rep 1365 g G) :
    Rep 1365 (conjArr σ g) (S * G * S⁻¹) :=
  rep_compA (rep_compA hσ hg) (rep_inv_of_isInvA hσ hinv)

theorem bray_conj_mem
    {c : C₁} (hc : ιC c ∈ brayEltsG A₁ twoBD1 twoBBray)
    {d : Equiv.Perm (Fin 1365)} (hd : d ∈ twoBD) : triHom c * d * (triHom c)⁻¹ ∈ twoBD := by
  obtain ⟨r, hr, hrc⟩ :=
    forall₂_mem_left (rep_brayElts rep_A₁ (centCheck_parts twoB_cent_check).1) hc
  have hσ := rep_triHom hrc (twoB_tri_parts.2.2.1 r hr)
  obtain ⟨hinv, hsx, hsy⟩ := twoB_tri_parts.2.2.2.2.2.2.2.2.2.2.2.2.2 r hr
  refine conj_mem_of_closure _ (fun x hx => ?_) hd
  rcases hx with rfl | rfl
  · exact mem_twoBD_of_sift (conjArr_rep hσ hinv rep_x) hsx
  · exact mem_twoBD_of_sift (conjArr_rep hσ hinv rep_y) hsy

theorem triHom_conj_mem
    (c : C₁) {d : Equiv.Perm (Fin 1365)} (hd : d ∈ twoBD) :
    triHom c * d * (triHom c)⁻¹ ∈ twoBD := by
  let M : Submonoid C₁ :=
    { carrier := {c | ∀ d ∈ twoBD, triHom c * d * (triHom c)⁻¹ ∈ twoBD}
      one_mem' := fun d hd => by rwa [map_one, one_mul, inv_one, mul_one]
      mul_mem' := fun {a b} ha hb d hd => by
        have e : triHom (a * b) * d * (triHom (a * b))⁻¹ =
            triHom a * (triHom b * d * (triHom b)⁻¹) * (triHom a)⁻¹ := by
          rw [map_mul]
          group
        rw [e]
        exact ha _ (hb d hd) }
  exact C₁_induction M (fun c hc d hd => bray_conj_mem hc hd) c d hd

theorem range_le :

    triHom.range ≤ Subgroup.normalizer (twoBD : Set (Equiv.Perm (Fin 1365))) := by
  rintro _ ⟨c, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro d
  refine ⟨triHom_conj_mem c, fun hd => ?_⟩
  have := triHom_conj_mem c⁻¹ hd
  have e : triHom c⁻¹ * (triHom c * d * (triHom c)⁻¹) * (triHom c⁻¹)⁻¹ = d := by
    rw [map_inv]
    group
  rwa [e] at this

theorem twoBD_le_range :
    twoBD ≤ triHom.range := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem card_range_mul_card_ker :
    Nat.card triHom.range * Nat.card triHom.ker = 2012774400 := by
  rw [← card_cent_a₁, Subgroup.card_eq_card_quotient_mul_card_subgroup triHom.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange triHom).toEquiv]

theorem exists_card_range_ker :
    ∃ t, Nat.card triHom.range = Nat.card twoBD * t ∧
    t * Nat.card triHom.ker = 2 ^ 3 := by
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le twoBD_le_range
  have h := card_range_mul_card_ker
  rw [ht, card_twoBD, mul_assoc] at h
  exact ⟨t, ht, by omega⟩

theorem exists_card_range :
    ∃ k, Nat.card triHom.range = Nat.card twoBD * 2 ^ k := by
  obtain ⟨t, ht, h8⟩ := exists_card_range_ker
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ h8)
  exact ⟨k, by rw [ht, hk]⟩

theorem exists_card_ker :
    ∃ m, Nat.card triHom.ker = 2 ^ m := by
  obtain ⟨t, -, h8⟩ := exists_card_range_ker
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ h8)
  exact ⟨m, hm⟩

theorem card_quotient_center_a₁
    (B : Subgroup C₁) (hB : CFSG.IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 251596800 := by
  obtain ⟨k, hk⟩ := exists_card_range
  obtain ⟨m, hm⟩ := exists_card_ker
  rw [card_quotient_center_of_isComponent triHom twoBD twoBD_le_range range_le
    isSimpleGroup_twoBD xD yD xD_yD_ne hk hm B hB, card_twoBD]

end CFSG.Sporadic.Co1Block

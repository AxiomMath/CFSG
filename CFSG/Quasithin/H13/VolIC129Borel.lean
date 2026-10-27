module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCSL25

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

@[expose] def V0set : Finset (Perm (Fin 5)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

theorem V0set_one : (1 : Perm (Fin 5)) ∈ V0set := by decide +kernel

theorem V0set_mul : ∀ a ∈ V0set, ∀ b ∈ V0set, a * b ∈ V0set := by decide +kernel

theorem V0set_inv : ∀ a ∈ V0set, a⁻¹ ∈ V0set := by decide +kernel

@[expose] def V0std : Subgroup (Perm (Fin 5)) := mkSub V0set V0set_one V0set_mul V0set_inv

theorem fixed_V0set : ∀ v : Fin 5 → ZMod 2, isEven v → (∀ σ ∈ V0set, pact σ v = v) →
    v = 0 ∨ v = z0 := by decide +kernel

theorem fix4_of_normalizes_V0set :
    ∀ τ : Perm (Fin 5), (∀ v ∈ V0set, τ * v * τ⁻¹ ∈ V0set) → τ 4 = 4 := by decide +kernel

theorem V0set_card : V0set.card = 4 := by decide +kernel

theorem sign_of_mem_V0set : ∀ σ ∈ V0set, Perm.sign σ = 1 := by decide +kernel

@[expose] def V0alt : Subgroup (alternatingGroup (Fin 5)) :=
  V0std.comap (alternatingGroup (Fin 5)).subtype

theorem mem_V0alt (σ : alternatingGroup (Fin 5)) : σ ∈ V0alt ↔ (σ : Perm (Fin 5)) ∈ V0set :=
  Iff.rfl

theorem card_V0alt : Nat.card V0alt = 4 := by
  have h1 : Nat.card V0alt = Nat.card V0std := by
    refine Nat.card_congr
      { toFun := fun σ => ⟨(σ : alternatingGroup (Fin 5)), σ.2⟩
        invFun := fun σ => ⟨⟨σ, ?_⟩, σ.2⟩
        left_inv := fun σ => rfl
        right_inv := fun σ => rfl }
    exact Equiv.Perm.mem_alternatingGroup.mpr (sign_of_mem_V0set σ σ.2)
  rw [h1, V0std, mkSub_card, V0set_card]

@[expose] noncomputable def V0sylow : Sylow 2 (alternatingGroup (Fin 5)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.ofCard V0alt (by
    rw [card_V0alt, AppC.card_alt5]
    have h60 : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
    rw [h60, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two]
    have h15 : (15 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    simp [h15])

theorem coe_V0sylow : ((V0sylow : Sylow 2 (alternatingGroup (Fin 5))) :
    Subgroup (alternatingGroup (Fin 5))) = V0alt := rfl

theorem fix_of_mem_normalizer (P : Sylow 2 (alternatingGroup (Fin 5)))
    {σ : alternatingGroup (Fin 5)}
    (hσ : σ ∈ Subgroup.normalizer ((P : Subgroup (alternatingGroup (Fin 5))) :
      Set (alternatingGroup (Fin 5))))
    {x : Fin 5 → ZMod 2} (hx : isEven x)
    (hP : ∀ π ∈ (P : Subgroup (alternatingGroup (Fin 5))), pact (π : Perm (Fin 5)) x = x) :
    pact (σ : Perm (Fin 5)) x = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) V0sylow P
  have hmemP : ∀ π : alternatingGroup (Fin 5),
      π ∈ (P : Subgroup (alternatingGroup (Fin 5))) ↔ g⁻¹ * π * g ∈ V0alt := by
    intro π
    rw [← hg, Sylow.coe_subgroup_smul, coe_V0sylow, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa [MulAut.smul_def, mul_assoc] using hv
    · intro h
      exact ⟨g⁻¹ * π * g, h, by simp [MulAut.smul_def, mul_assoc]⟩
  set y := pact ((g : Perm (Fin 5))⁻¹) x with hy
  have hyeven : isEven y := by
    have h1 := pact_mem ((g : Perm (Fin 5))⁻¹) (x := x) hx
    exact h1
  have hyfix : ∀ v ∈ V0set, pact v y = y := by
    intro v hv
    have hvA : v ∈ alternatingGroup (Fin 5) :=
      Equiv.Perm.mem_alternatingGroup.mpr (sign_of_mem_V0set v hv)
    have hπ : g * ⟨v, hvA⟩ * g⁻¹ ∈ (P : Subgroup (alternatingGroup (Fin 5))) := by
      rw [hmemP, show g⁻¹ * (g * ⟨v, hvA⟩ * g⁻¹) * g = ⟨v, hvA⟩ by group]
      exact (mem_V0alt _).mpr hv
    have h1 := hP _ hπ
    rw [hy, ← pact_mul]
    have e : v * (g : Perm (Fin 5))⁻¹ = (g : Perm (Fin 5))⁻¹ * ((g * ⟨v, hvA⟩ * g⁻¹ :
        alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
      simp [mul_assoc]
    rw [e, pact_mul, h1]
  set τ : Perm (Fin 5) := ((g⁻¹ * σ * g : alternatingGroup (Fin 5)) : Perm (Fin 5)) with hτ
  have hτ4 : τ 4 = 4 := by
    refine fix4_of_normalizes_V0set τ fun v hv => ?_
    have hvA : v ∈ alternatingGroup (Fin 5) :=
      Equiv.Perm.mem_alternatingGroup.mpr (sign_of_mem_V0set v hv)
    have h1 : g * ⟨v, hvA⟩ * g⁻¹ ∈ (P : Subgroup (alternatingGroup (Fin 5))) := by
      rw [hmemP, show g⁻¹ * (g * ⟨v, hvA⟩ * g⁻¹) * g = ⟨v, hvA⟩ by group]
      exact (mem_V0alt _).mpr hv
    have h2 := (Subgroup.mem_normalizer_iff.mp hσ _).mp h1
    rw [hmemP] at h2
    have h3 : g⁻¹ * (σ * (g * ⟨v, hvA⟩ * g⁻¹) * σ⁻¹) * g =
        (g⁻¹ * σ * g) * ⟨v, hvA⟩ * (g⁻¹ * σ * g)⁻¹ := by group
    rw [h3] at h2
    exact h2
  have hτy : pact τ y = y := by
    rcases fixed_V0set y hyeven hyfix with h | h
    · rw [h]
      funext i
      simp [pact]
    · rw [h]
      exact z0_fixed τ hτ4
  have e : (σ : Perm (Fin 5)) = (g : Perm (Fin 5)) * τ * (g : Perm (Fin 5))⁻¹ := by
    simp [hτ, mul_assoc]
  rw [e, pact_mul, pact_mul, ← hy, hτy, hy, ← pact_mul, mul_inv_cancel, pact_one]

theorem conj_eq_of_alt5 {G : Type} [Group G] [Finite G] {L S : Subgroup G} (hL : IsShort2 L)
    (h5 : IsAltType L 5) (hS : IsSylowTwoOf S L) {y : G} (hyL : y ∈ L)
    (hyN : y ∈ Subgroup.normalizer (S : Set G)) {u : G} (hu : u ∈ blockU L)
    (huS : ∀ s ∈ S, s * u = u * s) : y * u * y⁻¹ = u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := AppC.blockZ_eq_bot_of_alt5 hL h5
  obtain ⟨α, hα, -, β, -, hβk, hβe⟩ := h5
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  have hS2 : IsPGroup 2 (S.subgroupOf L) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let S' : Sylow 2 ↥L := hS2.toSylow hS.2.2
  let P : Sylow 2 (alternatingGroup (Fin 5)) := S'.mapSurjective hα
  have hP : (P : Subgroup (alternatingGroup (Fin 5))) = (S.subgroupOf L).map α := by
    rw [Sylow.coe_mapSurjective]
    rfl
  set x : Fin 5 → ZMod 2 :=
    ((Multiplicative.toAdd (β ⟨u, hu⟩) : evenWeight 5) : Fin 5 → ZMod 2) with hx
  have hxeven : isEven x := (Multiplicative.toAdd (β ⟨u, hu⟩)).2
  have hfixP : ∀ π ∈ (P : Subgroup (alternatingGroup (Fin 5))),
      pact (π : Perm (Fin 5)) x = x := by
    intro π hπ
    rw [hP] at hπ
    obtain ⟨s, hs, rfl⟩ := hπ
    have hsS : (s : G) ∈ S := hs
    have h1 := hβe s ⟨u, hu⟩ ⟨u, hu⟩ (by
      show u = (s : G) * u * (s : G)⁻¹
      rw [huS _ hsS]
      group)
    funext i
    exact (h1 i).symm
  have hyP : α ⟨y, hyL⟩ ∈ Subgroup.normalizer
      ((P : Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5))) := by
    rw [hP]
    refine Subgroup.le_normalizer_map α ⟨⟨y, hyL⟩, ?_, rfl⟩
    refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hyN h
  have h2 := fix_of_mem_normalizer P hyP hxeven hfixP
  have hmem : y * u * y⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (Subgroup.le_normalizer hyL)) u).mp hu
  have h3 := hβe ⟨y, hyL⟩ ⟨u, hu⟩ ⟨y * u * y⁻¹, hmem⟩ rfl
  have h4 : β ⟨y * u * y⁻¹, hmem⟩ = β ⟨u, hu⟩ := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    rw [h3 i]
    exact congrFun h2 i
  exact congrArg Subtype.val (hβinj h4)

end CFSG.Quasithin.H13.VolI

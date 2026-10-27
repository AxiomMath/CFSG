module

public import CFSG.Quasithin.Vol2.Ch1Quotient
public import CFSG.Quasithin.Background.A3Structure312Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.SzN2

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin

theorem exists_mulEquiv_map_eq {M : Type} [Group M] [Finite M] {U₀ U : Subgroup M}
    (hU₀ : IsSylowTwoOf U₀ ⊤) (hU : IsSylowTwoOf U ⊤) :
    ∃ φ : M ≃* M, U.map φ.toMonoidHom = U₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj
    (isSylowTwoOf_iff_isSylowOf.1 hU₀) (isSylowTwoOf_iff_isSylowOf.1 hU)
  refine ⟨(MulAut.conj k).symm, ?_⟩
  ext y
  rw [Subgroup.mem_map_equiv]
  change k * y * k⁻¹ ∈ U ↔ y ∈ U₀
  rw [hk (k * y * k⁻¹)]
  have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
  rw [e]

theorem solvable_overgroup_le_normalizer_of_sylow {M : Type} [Group M] [Finite M]
    {U₀ : Subgroup M} (hU₀ : IsSylowTwoOf U₀ ⊤)
    (h₀ : ∀ Y : Subgroup M, U₀ ≤ Y → Group.IsSolvable ↥Y → Y ≤ Subgroup.normalizer (U₀ : Set M))
    {U Y : Subgroup M} (hU : IsSylowTwoOf U ⊤) (hUY : U ≤ Y) (hY : Group.IsSolvable ↥Y) :
    Y ≤ Subgroup.normalizer (U : Set M) := by
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_map_eq hU₀ hU
  have h1 : U₀ ≤ Y.map φ.toMonoidHom := hφ ▸ Subgroup.map_mono hUY
  have h3 := h₀ _ h1 (map_isSolvable_equiv φ Y hY)
  rw [← hφ, ← Subgroup.map_equiv_normalizer_eq] at h3
  exact (Subgroup.map_le_map_iff_of_injective φ.injective).mp h3

theorem solvable_overgroup_orderOf_ne_of_sylow {M : Type} [Group M] [Finite M]
    {U₀ : Subgroup M} (hU₀ : IsSylowTwoOf U₀ ⊤) {n : ℕ}
    (h₀ : ∀ Y : Subgroup M, U₀ ≤ Y → Group.IsSolvable ↥Y → ∀ y ∈ Y, orderOf y ≠ n)
    {U Y : Subgroup M} (hU : IsSylowTwoOf U ⊤) (hUY : U ≤ Y) (hY : Group.IsSolvable ↥Y) :
    ∀ y ∈ Y, orderOf y ≠ n := by
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_map_eq hU₀ hU
  intro y hy
  have h1 : U₀ ≤ Y.map φ.toMonoidHom := hφ ▸ Subgroup.map_mono hUY
  have h := h₀ _ h1 (map_isSolvable_equiv φ Y hY) (φ y) ⟨y, hy, rfl⟩
  rwa [MulEquiv.orderOf_eq] at h

section Quotient

variable {Γ M : Type} [Group Γ] [Group M]

theorem ker_le_of_isSylowTwoOf [Finite Γ] {ρ : Γ →* M} (hk : IsPGroup 2 ρ.ker) {S : Subgroup Γ}
    (hS : IsSylowTwoOf S ⊤) : ρ.ker ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ S.index := by
    have h := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at h
  exact hk.le_sylow_of_normal (IsPGroup.toSylow hS.2.1 hidx)

theorem mem_normalizer_of_ker_le (ρ : Γ →* M) {S : Subgroup Γ} (hkS : ρ.ker ≤ S) {x : Γ}
    (hx : ρ x ∈ Subgroup.normalizer ((S.map ρ : Subgroup M) : Set M)) :
    x ∈ Subgroup.normalizer (S : Set Γ) := by
  have hmem : ∀ g : Γ, g ∈ S ↔ ρ g ∈ S.map ρ := fun g => by
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq_self hkS]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [hmem h, hmem (x * h * x⁻¹), map_mul, map_mul, map_inv]
  exact Subgroup.mem_normalizer_iff.mp hx (ρ h)

theorem normalizes_of_solvable_overgroup [Finite Γ] (ρ : Γ →* M) (hρ : Function.Surjective ρ)
    (hk : IsPGroup 2 ρ.ker)
    (hM : ∀ Ū Y : Subgroup M, IsSylowTwoOf Ū ⊤ → Ū ≤ Y → Group.IsSolvable ↥Y →
      Y ≤ Subgroup.normalizer (Ū : Set M))
    {S X : Subgroup Γ} (hS : IsSylowTwoOf S ⊤) (hSX : S ≤ X) (hX : Group.IsSolvable ↥X) :
    X ≤ Subgroup.normalizer (S : Set Γ) := by
  have hkS := ker_le_of_isSylowTwoOf hk hS
  have hŪ := isSylowTwoOf_top_map_of_surjective hS ρ hρ
  have hY : Group.IsSolvable ↥(X.map ρ) :=
    Group.isSolvable_of_surjective (f := ρ.subgroupMap X) (MonoidHom.subgroupMap_surjective ρ X)
  have h1 := hM (S.map ρ) (X.map ρ) hŪ (Subgroup.map_mono hSX) hY
  intro x hx
  exact mem_normalizer_of_ker_le ρ hkS (h1 ⟨x, hx, rfl⟩)

theorem not_three_dvd_of_solvable_overgroup [Finite Γ] (ρ : Γ →* M) (hρ : Function.Surjective ρ)
    (hk : IsPGroup 2 ρ.ker)
    (hM : ∀ Ū Y : Subgroup M, IsSylowTwoOf Ū ⊤ → Ū ≤ Y → Group.IsSolvable ↥Y →
      ∀ y ∈ Y, orderOf y ≠ 3)
    {S X : Subgroup Γ} (hS : IsSylowTwoOf S ⊤) (hSX : S ≤ X) (hX : Group.IsSolvable ↥X) :
    ¬ 3 ∣ Nat.card ↥X := by
  intro hdvd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 hdvd
  have hxΓ : orderOf (x : Γ) = 3 := by rw [Subgroup.orderOf_coe, hx]
  have hŪ := isSylowTwoOf_top_map_of_surjective hS ρ hρ
  have hY : Group.IsSolvable ↥(X.map ρ) :=
    Group.isSolvable_of_surjective (f := ρ.subgroupMap X) (MonoidHom.subgroupMap_surjective ρ X)
  have h1 := hM (S.map ρ) (X.map ρ) hŪ (Subgroup.map_mono hSX) hY (ρ x)
    (Subgroup.mem_map_of_mem ρ x.2)
  have hdv : orderOf (ρ (x : Γ)) ∣ 3 := hxΓ ▸ orderOf_map_dvd ρ (x : Γ)
  have h1' : orderOf (ρ (x : Γ)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdv with h | h
    · exact h
    · exact absurd h h1
  have hker : (x : Γ) ∈ ρ.ker := MonoidHom.mem_ker.2 (orderOf_eq_one_iff.1 h1')
  obtain ⟨k, hk'⟩ := hk ⟨(x : Γ), hker⟩
  have hpow : (x : Γ) ^ 2 ^ k = 1 := congrArg Subtype.val hk'
  have h3 : 3 ∣ 2 ^ k := hxΓ ▸ orderOf_dvd_of_pow_eq_one hpow
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem map_mem_normalizer_map (ρ : Γ →* M) (hρ : Function.Surjective ρ) {S : Subgroup Γ}
    (hkS : ρ.ker ≤ S) {x : Γ} (hx : x ∈ Subgroup.normalizer (S : Set Γ)) :
    ρ x ∈ Subgroup.normalizer ((S.map ρ : Subgroup M) : Set M) := by
  have hmem : ∀ g : Γ, g ∈ S ↔ ρ g ∈ S.map ρ := fun g => by
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq_self hkS]
  rw [Subgroup.mem_normalizer_iff]
  intro m
  obtain ⟨g, rfl⟩ := hρ m
  rw [← hmem g, ← map_inv, ← map_mul, ← map_mul, ← hmem (x * g * x⁻¹)]
  exact Subgroup.mem_normalizer_iff.mp hx g

theorem exists_maxParabolic_pair [Finite Γ] [Finite M] (ρ : Γ →* M) (hρ : Function.Surjective ρ)
    (hk : IsPGroup 2 ρ.ker)
    (hM : ∀ Ū : Subgroup M, IsSylowTwoOf Ū ⊤ → ∃ P : Fin 2 → Subgroup M, P 0 ≠ P 1 ∧
      (∀ A : Subgroup M, Ū ≤ A → (A ⋖ ⊤ ↔ ∃ j, A = P j)) ∧
        ∀ j, Subgroup.normalizer (Ū : Set M) ≤ P j)
    {S : Subgroup Γ} (hS : IsSylowTwoOf S ⊤) :
    ∃ P : Fin 2 → Subgroup Γ, P 0 ≠ P 1 ∧ (∀ j, IsMaxParabolic2 (⊤ : Subgroup Γ) (P j)) ∧
      (∀ j, Subgroup.normalizer (S : Set Γ) ≤ P j) ∧
      ∀ Q : Subgroup Γ, IsMaxParabolic2 (⊤ : Subgroup Γ) Q →
        Subgroup.normalizer (S : Set Γ) ≤ Q → ∃ j, Q = P j := by
  have hkS := ker_le_of_isSylowTwoOf hk hS
  have hŪ := isSylowTwoOf_top_map_of_surjective hS ρ hρ
  obtain ⟨P, hne, hmax, hN⟩ := hM (S.map ρ) hŪ
  have hUP : ∀ j, S.map ρ ≤ P j := fun j => Subgroup.le_normalizer.trans (hN j)
  have hcov : ∀ j, P j ⋖ ⊤ := fun j => (hmax (P j) (hUP j)).2 ⟨j, rfl⟩
  have hmap : ∀ j, ((P j).comap ρ).map ρ = P j := fun j =>
    Subgroup.map_comap_eq_self_of_surjective hρ (P j)
  have hkP : ∀ j, ρ.ker ≤ (P j).comap ρ := fun j => Subgroup.ker_le_comap ρ (P j)
  have hNS : ∀ j, Subgroup.normalizer (S : Set Γ) ≤ (P j).comap ρ := fun j x hx =>
    hN j (map_mem_normalizer_map ρ hρ hkS hx)
  have hpar : ∀ j, IsParabolic2 (⊤ : Subgroup Γ) ((P j).comap ρ) := fun j =>
    ⟨le_top, S, hS, fun x hx => hNS j hx.2⟩
  have hnet : ∀ j, (P j).comap ρ ≠ ⊤ := fun j h => by
    have := hmap j
    rw [h, Subgroup.map_top_of_surjective _ hρ] at this
    exact (hcov j).lt.ne this.symm
  have hmaxpar : ∀ j, IsMaxParabolic2 (⊤ : Subgroup Γ) ((P j).comap ρ) := fun j => by
    refine ⟨hpar j, hnet j, fun Q _ hQ hPQ => ?_⟩
    have hkQ : ρ.ker ≤ Q := (hkP j).trans hPQ
    have h1 : P j ≤ Q.map ρ := hmap j ▸ Subgroup.map_mono hPQ
    have h2 : Q.map ρ ≠ ⊤ := fun h => hQ (by
      rw [← Subgroup.comap_map_eq_self hkQ, h, Subgroup.comap_top])
    have h3 : Q.map ρ = P j := by
      by_contra h
      exact (hcov j).2 (lt_of_le_of_ne h1 (Ne.symm h)) (lt_top_iff_ne_top.2 h2)
    calc Q = (Q.map ρ).comap ρ := (Subgroup.comap_map_eq_self hkQ).symm
      _ = (P j).comap ρ := by rw [h3]
  refine ⟨fun j => (P j).comap ρ, fun h => hne ?_, hmaxpar, hNS, ?_⟩
  · have := congrArg (Subgroup.map ρ) h
    rwa [hmap 0, hmap 1] at this
  · intro Q hQ hNQ
    have hSQ : S ≤ Q := Subgroup.le_normalizer.trans hNQ
    have hkQ : ρ.ker ≤ Q := hkS.trans hSQ
    have h2 : Q.map ρ ≠ ⊤ := fun h => hQ.2.1 (by
      rw [← Subgroup.comap_map_eq_self hkQ, h, Subgroup.comap_top])
    obtain h | ⟨A, hA, hQA⟩ := eq_top_or_exists_le_coatom (Q.map ρ)
    · exact absurd h h2
    · have hUA : S.map ρ ≤ A := (Subgroup.map_mono hSQ).trans hQA
      obtain ⟨j, rfl⟩ := (hmax A hUA).1 hA.covBy_top
      refine ⟨j, ?_⟩
      have hQP : Q ≤ (P j).comap ρ := fun q hq => hQA (Subgroup.mem_map_of_mem ρ hq)
      exact (hQ.2.2 _ (hpar j) (hnet j) hQP).symm

theorem exists_hom_of_quotient_equiv [Finite Γ] (e : Γ ⧸ CFSG.pCore 2 Γ ≃* M) :
    ∃ ρ : Γ →* M, Function.Surjective ρ ∧ IsPGroup 2 ρ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 Γ)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact CFSG.pCore_isPGroup

end Quotient

section Subgroup

variable {G : Type} [Group G] {L : Subgroup G} {M : Type} [Group M]

theorem isMaxParabolic2_top_of_map {P : Subgroup G} (h : IsMaxParabolic2 L P) :
    IsMaxParabolic2 (⊤ : Subgroup ↥L) (P.subgroupOf L) := by
  obtain ⟨hpar, hne, hmax⟩ := h
  have hPL : P ≤ L := hpar.1
  refine ⟨?_, ?_, ?_⟩
  · rw [A312.isParabolic2_top_iff, Subgroup.map_subgroupOf_eq_of_le hPL]
    exact hpar
  · intro htop
    apply hne
    have := congrArg (Subgroup.map L.subtype) htop
    rwa [Subgroup.map_subgroupOf_eq_of_le hPL, Subgroup.map_top, Subgroup.range_subtype] at this
  · intro Q' hQ' hQ'top hPQ'
    have hQ : IsParabolic2 L (Q'.map L.subtype) := (A312.isParabolic2_top_iff L Q').mp hQ'
    have hQL : Q'.map L.subtype ≠ L := by
      intro h
      apply hQ'top
      have := congrArg (fun K : Subgroup G => K.subgroupOf L) h
      simpa [A4.subgroupOf_map_subtype', Subgroup.subgroupOf_self] using this
    have hPQ : P ≤ Q'.map L.subtype := by
      have := Subgroup.map_mono (f := L.subtype) hPQ'
      rwa [Subgroup.map_subgroupOf_eq_of_le hPL] at this
    have h1 := hmax _ hQ hQL hPQ
    calc Q' = (Q'.map L.subtype).subgroupOf L := (A4.subgroupOf_map_subtype' L Q').symm
      _ = P.subgroupOf L := by rw [h1]

theorem L_normalizes_of_solvable_overgroup [Finite G] {S₀ X : Subgroup G} (ρ : ↥L →* M)
    (hρ : Function.Surjective ρ) (hk : IsPGroup 2 ρ.ker)
    (hM : ∀ Ū Y : Subgroup M, IsSylowTwoOf Ū ⊤ → Ū ≤ Y → Group.IsSolvable ↥Y →
      Y ≤ Subgroup.normalizer (Ū : Set M))
    (hS : IsSylowTwoOf S₀ L) (hSX : S₀ ≤ X) (hXL : X ≤ L) (hX : Group.IsSolvable ↥X) :
    X ≤ Subgroup.normalizer (S₀ : Set G) := by
  have hX' : Group.IsSolvable ↥(X.subgroupOf L) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hXL).toMonoidHom) (MulEquiv.injective _)
  have h := normalizes_of_solvable_overgroup ρ hρ hk hM (isSylowTwoOf_top_subgroupOf hS)
    (fun x hx => hSX hx : S₀.subgroupOf L ≤ X.subgroupOf L) hX'
  intro x hx
  have hxL : x ∈ L := hXL hx
  have h1 := (A312.mem_normalizer_map_subtype_iff L (S₀.subgroupOf L) ⟨x, hxL⟩).mp
    (h (show (⟨x, hxL⟩ : ↥L) ∈ X.subgroupOf L from hx))
  rwa [Subgroup.map_subgroupOf_eq_of_le hS.1] at h1

theorem L_not_three_dvd_of_solvable_overgroup [Finite G] {S₀ X : Subgroup G} (ρ : ↥L →* M)
    (hρ : Function.Surjective ρ) (hk : IsPGroup 2 ρ.ker)
    (hM : ∀ Ū Y : Subgroup M, IsSylowTwoOf Ū ⊤ → Ū ≤ Y → Group.IsSolvable ↥Y →
      ∀ y ∈ Y, orderOf y ≠ 3)
    (hS : IsSylowTwoOf S₀ L) (hSX : S₀ ≤ X) (hXL : X ≤ L) (hX : Group.IsSolvable ↥X) :
    ¬ 3 ∣ Nat.card ↥X := by
  have hX' : Group.IsSolvable ↥(X.subgroupOf L) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hXL).toMonoidHom) (MulEquiv.injective _)
  have h := not_three_dvd_of_solvable_overgroup ρ hρ hk hM (isSylowTwoOf_top_subgroupOf hS)
    (fun x hx => hSX hx : S₀.subgroupOf L ≤ X.subgroupOf L) hX'
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv] at h

theorem L_exists_maxParabolic_pair [Finite G] [Finite M] {S₀ : Subgroup G} (ρ : ↥L →* M)
    (hρ : Function.Surjective ρ) (hk : IsPGroup 2 ρ.ker)
    (hM : ∀ Ū : Subgroup M, IsSylowTwoOf Ū ⊤ → ∃ P : Fin 2 → Subgroup M, P 0 ≠ P 1 ∧
      (∀ A : Subgroup M, Ū ≤ A → (A ⋖ ⊤ ↔ ∃ j, A = P j)) ∧
        ∀ j, Subgroup.normalizer (Ū : Set M) ≤ P j)
    (hS : IsSylowTwoOf S₀ L) :
    ∃ P₁ P₂ : Subgroup G, IsMaxParabolic2 L P₁ ∧ IsMaxParabolic2 L P₂ ∧ P₁ ≠ P₂ ∧
      L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ P₁ ∧ L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ P₂ ∧
      ∀ P : Subgroup G, IsMaxParabolic2 L P → L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ P →
        P = P₁ ∨ P = P₂ := by
  obtain ⟨P, hne, hmaxpar, hNS, huniq⟩ :=
    exists_maxParabolic_pair ρ hρ hk hM (isSylowTwoOf_top_subgroupOf hS)
  have hnorm : ∀ g : ↥L, g ∈ Subgroup.normalizer ((S₀.subgroupOf L : Subgroup ↥L) : Set ↥L) ↔
      (g : G) ∈ Subgroup.normalizer (S₀ : Set G) := fun g => by
    rw [A312.mem_normalizer_map_subtype_iff, Subgroup.map_subgroupOf_eq_of_le hS.1]
  have hP : ∀ j, L ⊓ Subgroup.normalizer (S₀ : Set G) ≤ (P j).map L.subtype := fun j g hg =>
    ⟨⟨g, hg.1⟩, hNS j ((hnorm ⟨g, hg.1⟩).mpr hg.2), rfl⟩
  refine ⟨(P 0).map L.subtype, (P 1).map L.subtype,
    A312.isMaxParabolic2_top_map L (P 0) (hmaxpar 0),
    A312.isMaxParabolic2_top_map L (P 1) (hmaxpar 1),
    fun h => hne (Subgroup.map_injective L.subtype_injective h), hP 0, hP 1, ?_⟩
  intro Q hQ hNQ
  have hQL : Q ≤ L := hQ.1.1
  have hN' : Subgroup.normalizer ((S₀.subgroupOf L : Subgroup ↥L) : Set ↥L) ≤ Q.subgroupOf L :=
    fun y hy => hNQ ⟨y.2, (hnorm y).mp hy⟩
  obtain ⟨j, hj⟩ := huniq _ (isMaxParabolic2_top_of_map hQ) hN'
  have hQj : Q = (P j).map L.subtype := by
    rw [← hj, Subgroup.map_subgroupOf_eq_of_le hQL]
  fin_cases j
  · exact Or.inl hQj
  · exact Or.inr hQj

end Subgroup

end CFSG.Quasithin.SzN2

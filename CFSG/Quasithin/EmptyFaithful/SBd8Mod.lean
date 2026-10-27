module

public import CFSG.Quasithin.EmptyFaithful.SBd8Abs
public import CFSG.Quasithin.EmptyFaithful.S152UAut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBd8

section ConjAct

variable {Γ : Type} [Group Γ] {X : Subgroup Γ}

theorem conjAct_coe (s : Subgroup.normalizer (X : Set Γ)) (x : X) :
    ((conjAct X s x : X) : Γ) = (s : Γ) * x * (s : Γ)⁻¹ := conj_coe_apply X s x

theorem conjAct_symm_coe (s : Subgroup.normalizer (X : Set Γ)) (x : X) :
    ((((conjAct X s)⁻¹ x : X)) : Γ) = (s : Γ)⁻¹ * x * (s : Γ) := by
  have h : conjAct X s⁻¹ = (conjAct X s)⁻¹ := map_inv _ _
  rw [← h, conj_coe_apply]
  simp

theorem map_conjAct_subgroupOf_eq_iff {P : Subgroup Γ} (hPX : P ≤ X) {s : Γ}
    (hs : s ∈ Subgroup.normalizer (X : Set Γ)) :
    (P.subgroupOf X).map (conjAct X ⟨s, hs⟩).toMonoidHom = P.subgroupOf X ↔
      s ∈ Subgroup.normalizer (P : Set Γ) := by
  set α := conjAct X ⟨s, hs⟩ with hα
  have hmem : ∀ y : X, y ∈ (P.subgroupOf X).map α.toMonoidHom ↔ (s : Γ)⁻¹ * y * s ∈ P := by
    intro y
    have h1 := Subgroup.mem_map_equiv (f := (α : X ≃* X)) (K := P.subgroupOf X) (x := y)
    have h2 : (α : X ≃* X).symm y = α⁻¹ y := rfl
    rw [show (α : X ≃* X).toMonoidHom = α.toMonoidHom from rfl] at h1
    rw [h1, h2, Subgroup.mem_subgroupOf]
    have h3 := conjAct_symm_coe (X := X) ⟨s, hs⟩ y
    rw [hα, h3]
  have hsX : ∀ g : Γ, g ∈ X ↔ (s⁻¹ * g * s) ∈ X := fun g => by
    have := Subgroup.mem_normalizer_iff''.1 hs g
    exact this
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff'']
    intro g
    constructor
    · intro hg
      have hgX : g ∈ X := hPX hg
      have h1 : (⟨g, hgX⟩ : X) ∈ P.subgroupOf X := Subgroup.mem_subgroupOf.2 hg
      rw [← h, hmem] at h1
      exact h1
    · intro hg
      have hgX : g ∈ X := (hsX g).2 (hPX hg)
      have h1 : (s : Γ)⁻¹ * (⟨g, hgX⟩ : X) * s ∈ P := hg
      rw [← hmem, h] at h1
      exact Subgroup.mem_subgroupOf.1 h1
  · intro h
    ext y
    rw [hmem, Subgroup.mem_subgroupOf]
    exact ((Subgroup.mem_normalizer_iff''.1 h (y : Γ)).symm)

end ConjAct

section SubgroupOf

variable {Γ : Type} [Group Γ] {H : Subgroup Γ}

theorem mem_normalizer_subgroupOf_iff {U : Subgroup Γ} (hUH : U ≤ H) (x : H) :
    x ∈ Subgroup.normalizer ((U.subgroupOf H : Subgroup H) : Set H) ↔
      (x : Γ) ∈ Subgroup.normalizer (U : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff'', Subgroup.mem_normalizer_iff'']
  constructor
  · intro h g
    constructor
    · intro hg
      have hgH : g ∈ H := hUH hg
      have := (h ⟨g, hgH⟩).1 (Subgroup.mem_subgroupOf.2 hg)
      exact Subgroup.mem_subgroupOf.1 this
    · intro hg
      have hgH : g ∈ H := by
        have : (x : Γ) * ((x : Γ)⁻¹ * g * x) * (x : Γ)⁻¹ ∈ H :=
          H.mul_mem (H.mul_mem x.2 (hUH hg)) (H.inv_mem x.2)
        simpa [mul_assoc] using this
      have := (h ⟨g, hgH⟩).2 (Subgroup.mem_subgroupOf.2 hg)
      exact Subgroup.mem_subgroupOf.1 this
  · intro h y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact h (y : Γ)

theorem isSylowTwoOf_iff_subgroupOf {T : Subgroup Γ} (hTH : T ≤ H) :
    IsSylowTwoOf T H ↔ IsSylowTwoOf (T.subgroupOf H) ⊤ := by
  have h := SBd3T.isSylowTwoOf_map_iff H.subtype H.subtype_injective (T.subgroupOf H) ⊤
  rw [Subgroup.map_subgroupOf_eq_of_le hTH, Subgroup.map_top, Subgroup.range_subtype] at h
  exact h

theorem isMaxSubgroupIn_map_iff {P' N' : Subgroup H} :
    IsMaxSubgroupIn (P'.map H.subtype) (N'.map H.subtype) ↔ IsMaxSubgroupIn P' N' := by
  have hinj := H.subtype_injective
  constructor
  · rintro ⟨hlt, hmax⟩
    refine ⟨(Subgroup.map_lt_map_iff_of_injective hinj).1 hlt, fun Q hNQ hQP => ?_⟩
    have h1 := hmax (Q.map H.subtype) ((Subgroup.map_lt_map_iff_of_injective hinj).2 hNQ)
      (Subgroup.map_mono hQP)
    exact Subgroup.map_injective hinj h1
  · rintro ⟨hlt, hmax⟩
    refine ⟨(Subgroup.map_lt_map_iff_of_injective hinj).2 hlt, fun K hNK hKP => ?_⟩
    have hKH : K ≤ H := hKP.trans (by rintro _ ⟨x, -, rfl⟩; exact x.2)
    have hK : (K.subgroupOf H).map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
    rw [← hK] at hNK hKP ⊢
    have h1 := hmax (K.subgroupOf H) ((Subgroup.map_lt_map_iff_of_injective hinj).1 hNK)
      ((Subgroup.map_le_map_iff_of_injective hinj).1 hKP)
    rw [h1]

theorem ncard_maxOver_map (P' T' : Subgroup H) :
    (maxOver (P'.map H.subtype) (T'.map H.subtype)).ncard = (maxOver P' T').ncard := by
  have hinj := H.subtype_injective
  have : maxOver (P'.map H.subtype) (T'.map H.subtype) =
      (maxOver P' T').image (Subgroup.map H.subtype) := by
    ext N
    constructor
    · rintro ⟨hN, hTN⟩
      have hNH : N ≤ H := hN.1.le.trans (by rintro _ ⟨x, -, rfl⟩; exact x.2)
      refine ⟨N.subgroupOf H, ⟨?_, ?_⟩, Subgroup.map_subgroupOf_eq_of_le hNH⟩
      · rw [← Subgroup.map_subgroupOf_eq_of_le hNH] at hN
        exact isMaxSubgroupIn_map_iff.1 hN
      · rw [← Subgroup.map_subgroupOf_eq_of_le hNH] at hTN
        exact (Subgroup.map_le_map_iff_of_injective hinj).1 hTN
    · rintro ⟨N', ⟨hN', hTN'⟩, rfl⟩
      exact ⟨isMaxSubgroupIn_map_iff.2 hN', Subgroup.map_mono hTN'⟩
  rw [this]
  exact Set.ncard_image_of_injective _ (Subgroup.map_injective hinj)

theorem isMinParabolicOf_map_iff (P' : Subgroup H) :
    IsMinParabolicOf H (P'.map H.subtype) ↔ IsMinParabolicOf (⊤ : Subgroup H) P' := by
  have hinj := H.subtype_injective
  constructor
  · rintro ⟨T, hT, ⟨⟨hPH, hTP, hcard⟩, hnn⟩⟩
    have hTH : T ≤ H := hT.1
    have hTm : (T.subgroupOf H).map H.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTH
    refine ⟨T.subgroupOf H, (isSylowTwoOf_iff_subgroupOf hTH).1 hT, ⟨⟨le_top, ?_, ?_⟩, ?_⟩⟩
    · rw [← hTm] at hTP
      exact (Subgroup.map_lt_map_iff_of_injective hinj).1 hTP
    · rw [← hTm] at hcard
      rwa [ncard_maxOver_map] at hcard
    · intro hP'
      apply hnn
      rintro _ ⟨p', hp', rfl⟩
      exact (mem_normalizer_subgroupOf_iff hTH p').1 (hP' hp')
  · rintro ⟨T', hT', ⟨⟨-, hTP, hcard⟩, hnn⟩⟩
    have hTH : T'.map H.subtype ≤ H := by rintro _ ⟨x, -, rfl⟩; exact x.2
    refine ⟨T'.map H.subtype, ?_, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
    · rw [isSylowTwoOf_iff_subgroupOf hTH]
      have h1 : (T'.map H.subtype).subgroupOf H = T' :=
        Subgroup.comap_map_eq_self_of_injective hinj T'
      rw [h1]
      exact hT'
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
    · exact (Subgroup.map_lt_map_iff_of_injective hinj).2 hTP
    · rwa [ncard_maxOver_map]
    · intro hP
      apply hnn
      intro p hp'
      have h1 : (T'.map H.subtype).subgroupOf H = T' :=
        Subgroup.comap_map_eq_self_of_injective hinj T'
      have := (mem_normalizer_subgroupOf_iff hTH p).2 (hP ⟨p, hp', rfl⟩)
      rwa [h1] at this

theorem le_of_isMinParabolicOf {P : Subgroup Γ} (h : IsMinParabolicOf H P) : P ≤ H := by
  obtain ⟨T, -, ⟨⟨hPH, -, -⟩, -⟩⟩ := h
  exact hPH

theorem isMinParabolicOf_subgroupOf_iff {P : Subgroup Γ} (hPH : P ≤ H) :
    IsMinParabolicOf H P ↔ IsMinParabolicOf (⊤ : Subgroup H) (P.subgroupOf H) := by
  have := isMinParabolicOf_map_iff (H := H) (P.subgroupOf H)
  rwa [Subgroup.map_subgroupOf_eq_of_le hPH] at this

end SubgroupOf

structure OvgData (X : Type) [Group X] [Finite X] (A : Subgroup (MulAut X)) (U K : Subgroup X) :
    Prop where
  quasi : CFSG.IsQuasisimple X
  U_syl : IsSylowTwoOf U ⊤
  A_U : ∀ α ∈ A, U.map α.toMonoidHom = U
  U_le : U ≤ K
  K_ne : K ≠ ⊤
  A_K : ∀ α ∈ A, K.map α.toMonoidHom = K
  K_max : ∀ K' : Subgroup X, K ≤ K' → K' ≠ ⊤ → (∀ α ∈ A, K'.map α.toMonoidHom = K') → K' ≤ K
  three_dvd : 3 ∣ Nat.card ↥K
  not_nine : ¬ 9 ∣ Nat.card ↥K
  Y_solv : Group.IsSolvable ↥(oPrimeResidualOf 3 K)

section Transport

variable {Γ : Type} [Group Γ] [Finite Γ] {X J S₀ K : Subgroup Γ}

theorem isSylowTwoOf_inf_X (d : Insp28Data X J S₀ K) : IsSylowTwoOf (S₀ ⊓ X) X := by
  have hS₀N : S₀ ≤ Subgroup.normalizer (X : Set Γ) := d.syl.1.trans d.J_norm
  refine CFSG.QuasithinUnique.Unc25Small.isSylowTwoOf_inf_of_mul d.syl (N := X)
    (by rw [d.J_eq]; exact le_sup_left) fun h hh => ?_
  rw [d.J_eq] at hh
  obtain ⟨n, hn, s, hs, rfl⟩ := mem_sup_of_le_normalizer (N := X) (H := S₀) hS₀N hh
  exact ⟨n, hn, s, hs, rfl⟩

theorem oPrimeResidualOf_subgroupOf (hKX : K ≤ X) :
    oPrimeResidualOf 3 (K.subgroupOf X) = (oPrimeResidualOf 3 K).subgroupOf X := by
  apply Subgroup.map_injective X.subtype_injective
  have h1 : (oPrimeResidualOf 3 K) ≤ X := by
    refine (Subgroup.closure_le _).2 fun x hx => hKX hx.1
  rw [SBd3T.map_oPrimeResidualOf X.subtype 3 Nat.prime_three, Subgroup.map_subgroupOf_eq_of_le hKX,
    Subgroup.map_subgroupOf_eq_of_le h1]

theorem ovgData_of_insp28Data (d : Insp28Data X J S₀ K) :
    OvgData ↥X (autOn S₀ X) ((S₀ ⊓ X).subgroupOf X) (K.subgroupOf X) := by
  have hS₀N : S₀ ≤ Subgroup.normalizer (X : Set Γ) := d.syl.1.trans d.J_norm
  have hα : ∀ α ∈ autOn S₀ X, ∃ s : Γ, ∃ hs : s ∈ Subgroup.normalizer (X : Set Γ),
      s ∈ S₀ ∧ conjAct X ⟨s, hs⟩ = α := fun α hα => by
    obtain ⟨s, hs, hsS, h⟩ := mem_autOn_iff_exists.1 hα
    exact ⟨s, hs, hsS, h⟩
  refine ⟨d.quasi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isSylowTwoOf_iff_subgroupOf inf_le_right).1 (isSylowTwoOf_inf_X d)
  · intro α hα'
    obtain ⟨s, hs, hsS, rfl⟩ := hα α hα'
    exact (map_conjAct_subgroupOf_eq_iff inf_le_right hs).2
      (mem_normalizer_inf' (Subgroup.le_normalizer hsS) (hS₀N hsS))
  · intro y hy
    exact Subgroup.mem_subgroupOf.2 (d.U_le (Subgroup.mem_subgroupOf.1 hy))
  · intro h
    apply d.K_ne
    apply le_antisymm d.K_le
    intro x hx
    have : (⟨x, hx⟩ : X) ∈ K.subgroupOf X := by rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  · intro α hα'
    obtain ⟨s, hs, hsS, rfl⟩ := hα α hα'
    exact (map_conjAct_subgroupOf_eq_iff d.K_le hs).2 (d.S₀_norm hsS)
  · intro K'' hKK'' hK''top hinv
    have hK₂X : K''.map X.subtype ≤ X := by rintro _ ⟨y, -, rfl⟩; exact y.2
    have hK₂sub : (K''.map X.subtype).subgroupOf X = K'' :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective K''
    have hKK₂ : K ≤ K''.map X.subtype := fun k hk =>
      ⟨⟨k, d.K_le hk⟩, hKK'' (Subgroup.mem_subgroupOf.2 hk), rfl⟩
    have hK₂ne : K''.map X.subtype ≠ X := by
      intro h
      apply hK''top
      rw [← hK₂sub, h, Subgroup.subgroupOf_self]
    have hnorm : S₀ ≤ Subgroup.normalizer ((K''.map X.subtype : Subgroup Γ) : Set Γ) := by
      intro s hs
      have h1 := hinv (conjAct X ⟨s, hS₀N hs⟩) (mem_autOn_iff_exists.2 ⟨s, hS₀N hs, hs, rfl⟩)
      rw [← hK₂sub] at h1
      exact (map_conjAct_subgroupOf_eq_iff hK₂X (hS₀N hs)).1 h1
    have h2 := d.K_max _ hKK₂ hK₂X hK₂ne hnorm
    intro y hy
    exact Subgroup.mem_subgroupOf.2 (h2 ⟨y, hy, rfl⟩)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.K_le).toEquiv]
    exact d.three_dvd
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.K_le).toEquiv]
    exact d.not_nine
  · rw [oPrimeResidualOf_subgroupOf d.K_le]
    have h1 : (oPrimeResidualOf 3 K) ≤ X := (Subgroup.closure_le _).2 fun x hx => d.K_le hx.1
    have := d.Y_solv
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe h1).toMonoidHom) (Subgroup.subgroupOfEquivOfLe h1).injective

@[expose] def ModelConcl (X : Type) [Group X] [Finite X] (A : Subgroup (MulAut X)) (U K : Subgroup X) :
    Prop :=
  ((∃ n : ℕ, Even n ∧ IsPSL 2 2 n X) ∧ K = Subgroup.normalizer (U : Set X)) ∨
  ((IsPSL 3 2 1 X ∨ IsAlt 6 X ∨ IsPSU 3 3 1 X) ∧ IsMinParabolicOf (⊤ : Subgroup X) K ∧
    ∀ P : Subgroup X, IsMinParabolicOf (⊤ : Subgroup X) P → Subgroup.normalizer (U : Set X) ≤ P →
      ∀ α ∈ A, P.map α.toMonoidHom = P) ∨
  (IsAlt 8 X ∧ IsMinParabolicOf (⊤ : Subgroup X) K ∧ ∃ α ∈ A, ∀ x : X, α ≠ MulAut.conj x)

theorem insp28Concl_of_modelConcl (d : Insp28Data X J S₀ K)
    (h8 : ∀ α ∈ autOn S₀ X, IsAlt 8 ↥X → (∀ x : ↥X, α ≠ MulAut.conj x) →
      Nonempty (↥J ≃* Equiv.Perm (Fin 8)))
    (h : ModelConcl ↥X (autOn S₀ X) ((S₀ ⊓ X).subgroupOf X) (K.subgroupOf X)) :
    Insp28Concl X J S₀ K := by
  have hS₀N : S₀ ≤ Subgroup.normalizer (X : Set Γ) := d.syl.1.trans d.J_norm
  rcases h with ⟨hn, hK⟩ | ⟨hX, hmin, hP⟩ | ⟨h8', hmin, α, hα, hnon⟩
  · left
    refine ⟨hn, S₀ ⊓ X, isSylowTwoOf_inf_X d, ?_⟩
    ext x
    constructor
    · intro hx
      have hxX := d.K_le hx
      have h1 : (⟨x, hxX⟩ : X) ∈ K.subgroupOf X := hx
      rw [hK] at h1
      exact ⟨hxX, (mem_normalizer_subgroupOf_iff inf_le_right ⟨x, hxX⟩).1 h1⟩
    · rintro ⟨hxX, hxN⟩
      have h1 : (⟨x, hxX⟩ : X) ∈ Subgroup.normalizer (((S₀ ⊓ X).subgroupOf X : Subgroup X) : Set X) :=
        (mem_normalizer_subgroupOf_iff inf_le_right ⟨x, hxX⟩).2 hxN
      rw [← hK] at h1
      exact h1
  · right; left
    refine ⟨hX, (isMinParabolicOf_subgroupOf_iff d.K_le).2 hmin, ?_⟩
    intro P hPm hN
    have hPX := le_of_isMinParabolicOf hPm
    have hPm' := (isMinParabolicOf_subgroupOf_iff hPX).1 hPm
    have hN' : Subgroup.normalizer (((S₀ ⊓ X).subgroupOf X : Subgroup X) : Set X) ≤
        P.subgroupOf X := by
      intro y hy
      have h1 := (mem_normalizer_subgroupOf_iff inf_le_right y).1 hy
      exact Subgroup.mem_subgroupOf.2 (hN ⟨y.2, h1⟩)
    intro s hs
    have h1 := hP _ hPm' hN' (conjAct X ⟨s, hS₀N hs⟩)
      (mem_autOn_iff_exists.2 ⟨s, hS₀N hs, hs, rfl⟩)
    exact (map_conjAct_subgroupOf_eq_iff hPX (hS₀N hs)).1 h1
  · right; right
    exact ⟨h8 α hα h8' hnon, (isMinParabolicOf_subgroupOf_iff d.K_le).2 hmin⟩

end Transport

end SBd8

end CFSG.Quasithin

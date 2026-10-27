module

public import CFSG.Quasithin.Vol2.GoldschmidtF431AGThm
public import CFSG.Quasithin.Vol2.GoldschmidtF431AGTrans
public import CFSG.Quasithin.Vol2.GoldschmidtF431Datum
public import CFSG.Quasithin.Recognition.CertTwoLocal

public section

namespace CFSG.Quasithin.H13.F431.AG

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {D : Type} [Group D] (A : LieAmalgamExt D)

@[expose] noncomputable def innK (hinn : (MulAut.conj : D →* MulAut D).range ≤ A.K) :
    D →* ↥A.K :=
  (MulAut.conj : D →* MulAut D).codRestrict A.K fun g => hinn ⟨g, rfl⟩

theorem innK_injective (hinj : Function.Injective (MulAut.conj : D →* MulAut D))
    (hinn : (MulAut.conj : D →* MulAut D).range ≤ A.K) : Function.Injective (innK A hinn) :=
  fun _ _ h => hinj (congrArg Subtype.val h)

theorem mul_innK_mul_inv (hinn : (MulAut.conj : D →* MulAut D).range ≤ A.K) (φ : ↥A.K) (x : D) :
    φ * innK A hinn x * φ⁻¹ = innK A hinn ((φ : MulAut D) x) := by
  refine Subtype.ext (MulEquiv.ext fun y => ?_)
  simp [innK]

instance normal_range_innK (hinn : (MulAut.conj : D →* MulAut D).range ≤ A.K) :
    (innK A hinn).range.Normal :=
  ⟨fun x hx φ => by
    obtain ⟨d, rfl⟩ := hx
    exact ⟨(φ : MulAut D) d, (mul_innK_mul_inv A hinn φ d).symm⟩⟩

theorem mem_autStab_iff_map_eq (φ : MulAut D) (P : Subgroup D) :
    φ ∈ autStab P ↔ P.map φ.toMonoidHom = P := by
  constructor
  · intro h
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (h y).mp hy
    · intro hx
      refine ⟨φ⁻¹ x, (h (φ⁻¹ x)).mpr (by simpa using hx), by simp⟩
  · intro h x
    conv_rhs => rw [← h]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := φ.injective hyx
      exact this ▸ hy

theorem isSylowTwoOf_map_range [Finite D] {K : Type*} [Group K] (ι : D →* K)
    (hι : Function.Injective ι) {T : Subgroup D} (h : IsSylowTwoOf T ⊤) :
    IsSylowTwoOf (T.map ι) ι.range := by
  refine F7.isSylowTwoOf_of_relIndex (Subgroup.map_le_range ι T) (h.2.1.map ι) ?_
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hι]
  exact F7.isSylowTwoOf_odd_relIndex h

section Stab

theorem mem_autStab_iff_mem_normalizer_map (hinn : (MulAut.conj : D →* MulAut D).range ≤ A.K)
    (hinj : Function.Injective (MulAut.conj : D →* MulAut D)) (P : Subgroup D) (φ : ↥A.K) :
    (φ : MulAut D) ∈ autStab P ↔
      φ ∈ Subgroup.normalizer (((P.map (innK A hinn)) : Subgroup ↥A.K) : Set ↥A.K) := by
  have hι := innK_injective A hinj hinn
  have := normal_range_innK A hinn
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro k
    by_cases hk : k ∈ (innK A hinn).range
    · obtain ⟨x, rfl⟩ := hk
      rw [mul_innK_mul_inv A hinn, Subgroup.mem_map_iff_mem hι, Subgroup.mem_map_iff_mem hι]
      exact h x
    · have h1 : k ∉ P.map (innK A hinn) := fun hm => hk (Subgroup.map_le_range _ P hm)
      have h2 : φ * k * φ⁻¹ ∉ P.map (innK A hinn) := fun hm => hk (by
        have := (Subgroup.Normal.conj_mem (inferInstance : (innK A hinn).range.Normal) _
          (Subgroup.map_le_range _ P hm) φ⁻¹)
        simpa [mul_assoc] using this)
      exact ⟨fun a => absurd a h1, fun a => absurd a h2⟩
  · intro h x
    have := Subgroup.mem_normalizer_iff.mp h (innK A hinn x)
    rwa [mul_innK_mul_inv A hinn, Subgroup.mem_map_iff_mem hι, Subgroup.mem_map_iff_mem hι] at this

theorem stab_of_stab_TD [Finite D] {ψ : MulAut D} (hψ : ψ ∈ A.Mbar) (hT : ψ ∈ autStab A.TD) :
    ψ ∈ autStab A.P1 ∧ ψ ∈ autStab A.P2 := by
  have hT' : A.TD.map ψ.toMonoidHom = A.TD := (mem_autStab_iff_map_eq ψ A.TD).mp hT
  have h' := IsYAmalgamPair.map ψ A.yam
  rw [hT'] at h'
  have h1 := (A.yam.2.2 _).mp ((h'.2.2 _).mpr (Or.inl rfl))
  have h2 := (A.yam.2.2 _).mp ((h'.2.2 _).mpr (Or.inr rfl))
  have hne : A.P1 ≠ A.P2 := A.yam.2.1
  have hinj := Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (hinj (h1.trans h2.symm)) hne
  · exact ⟨(mem_autStab_iff_map_eq ψ _).mpr h1, (mem_autStab_iff_map_eq ψ _).mpr h2⟩
  · have hinf : (A.P1 ⊓ A.P2).map ψ.toMonoidHom = A.P1 ⊓ A.P2 := by
      rw [Subgroup.map_inf _ _ _ ψ.injective, h1, h2, inf_comm]
    have := A.diag ψ hψ ((mem_autStab_iff_map_eq ψ _).mpr hinf)
    have h3 := (mem_autStab_iff_map_eq ψ _).mp this
    exact absurd (h3.symm.trans h1) hne
  · exact absurd (hinj (h1.trans h2.symm)) hne

end Stab

theorem ag_of_borelTits [Finite D] (hinj : Function.Injective (MulAut.conj : D →* MulAut D))
    (hinn : (MulAut.conj : D →* MulAut D).range ≤ A.K) (hBT : Holds D 2)
    (habove : ∀ P : Subgroup D, Subgroup.normalizer (A.TD : Set D) ≤ P → P ≠ ⊤ →
      P ≤ A.P1 ∨ P ≤ A.P2)
    {E : Subgroup ↥A.K} (hE : IsAGMember (A.TD.map (innK A hinn)) E) :
    Subgroup.normalizer (E : Set ↥A.K) ≤ A.Mb1 ∨ Subgroup.normalizer (E : Set ↥A.K) ≤ A.Mb2 := by
  have hι := innK_injective A hinj hinn
  have := normal_range_innK A hinn
  have hT : IsSylowTwoOf (A.TD.map (innK A hinn)) (innK A hinn).range :=
    isSylowTwoOf_map_range _ hι A.yam.1
  have hKM : A.K ≤ A.Mbar := sup_le inf_le_left inf_le_left
  have habove' : ∀ B : Subgroup ↥A.K, B ≤ (innK A hinn).range →
      (innK A hinn).range ⊓ Subgroup.normalizer
        ((A.TD.map (innK A hinn) : Subgroup ↥A.K) : Set ↥A.K) ≤ B →
      B ≠ (innK A hinn).range →
      B ≤ A.P1.map (innK A hinn) ∨ B ≤ A.P2.map (innK A hinn) := by
    intro B hBX hNB hBne
    have hBeq : (B.comap (innK A hinn)).map (innK A hinn) = B := Subgroup.map_comap_eq_self hBX
    have hN : Subgroup.normalizer (A.TD : Set D) ≤ B.comap (innK A hinn) := fun d hd =>
      hNB (Subgroup.mem_inf.mpr ⟨⟨d, rfl⟩, (mem_normalizer_map_iff _ hι A.TD d).mpr hd⟩)
    have hne : B.comap (innK A hinn) ≠ ⊤ := fun h =>
      hBne (by rw [← hBeq, h, ← MonoidHom.range_eq_map])
    rcases habove _ hN hne with h | h
    · exact Or.inl (hBeq ▸ Subgroup.map_mono h)
    · exact Or.inr (hBeq ▸ Subgroup.map_mono h)
  have hfix : ∀ φ ∈ Subgroup.normalizer
      ((A.TD.map (innK A hinn) : Subgroup ↥A.K) : Set ↥A.K),
      φ ∈ Subgroup.normalizer ((A.P1.map (innK A hinn) : Subgroup ↥A.K) : Set ↥A.K) ∧
        φ ∈ Subgroup.normalizer ((A.P2.map (innK A hinn) : Subgroup ↥A.K) : Set ↥A.K) := by
    intro φ hφ
    have h0 := (mem_autStab_iff_mem_normalizer_map A hinn hinj A.TD φ).mpr hφ
    obtain ⟨h1, h2⟩ := stab_of_stab_TD A (hKM φ.2) h0
    exact ⟨(mem_autStab_iff_mem_normalizer_map A hinn hinj A.P1 φ).mp h1,
      (mem_autStab_iff_mem_normalizer_map A hinn hinj A.P2 φ).mp h2⟩
  rcases normalizer_le_of_isAGMember (borelTitsIn_of_holds _ hι hBT) hT habove'
    (fun φ hφ => (hfix φ hφ).1) (fun φ hφ => (hfix φ hφ).2) hE with h | h
  · refine Or.inl fun φ hφ => Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
      ⟨hKM φ.2, (mem_autStab_iff_mem_normalizer_map A hinn hinj A.P1 φ).mpr (h hφ)⟩)
  · refine Or.inr fun φ hφ => Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
      ⟨hKM φ.2, (mem_autStab_iff_mem_normalizer_map A hinn hinj A.P2 φ).mpr (h hφ)⟩)

end CFSG.Quasithin.H13.F431.AG

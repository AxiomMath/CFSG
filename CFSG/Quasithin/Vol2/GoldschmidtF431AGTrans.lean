module

public import CFSG.Quasithin.Vol2.GoldschmidtF431AGMain

public section

namespace CFSG.Quasithin.H13.F431.AG

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {D K : Type*} [Group D] [Group K] (ι : D →* K)

theorem pCoreOf_map_injective (hι : Function.Injective ι) (L : Subgroup D) :
    pCoreOf 2 (L.map ι) = (pCoreOf 2 L).map ι := by
  unfold pCoreOf
  let e : ↥L ≃* ↥(L.map ι) := L.equivMapOfInjective ι hι
  rw [← map_pCore_mulEquiv 2 e, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem mem_normalizer_map_iff (hι : Function.Injective ι) (L : Subgroup D) (d : D) :
    ι d ∈ Subgroup.normalizer ((L.map ι : Subgroup K) : Set K) ↔
      d ∈ Subgroup.normalizer (L : Set D) := by
  simp only [Subgroup.mem_normalizer_iff]
  constructor
  · intro H x
    have := H (ι x)
    rwa [← map_mul, ← map_inv, ← map_mul, Subgroup.mem_map_iff_mem hι,
      Subgroup.mem_map_iff_mem hι] at this
  · intro H h
    by_cases hh : h ∈ ι.range
    · obtain ⟨x, rfl⟩ := hh
      rw [← map_mul, ← map_inv, ← map_mul, Subgroup.mem_map_iff_mem hι,
        Subgroup.mem_map_iff_mem hι]
      exact H x
    · have h1 : h ∉ L.map ι := fun hm => hh (Subgroup.map_le_range ι L hm)
      have h2 : ι d * h * (ι d)⁻¹ ∉ L.map ι := by
        intro hm
        apply hh
        have := ι.range.mul_mem (ι.range.mul_mem (ι.range.inv_mem ⟨d, rfl⟩)
          (Subgroup.map_le_range ι L hm)) ⟨d, rfl⟩
        simpa [mul_assoc] using this
      exact ⟨fun a => absurd a h1, fun a => absurd a h2⟩

theorem range_inf_normalizer_eq (hι : Function.Injective ι) (L : Subgroup D) :
    ι.range ⊓ Subgroup.normalizer ((L.map ι : Subgroup K) : Set K) =
      (Subgroup.normalizer (L : Set D)).map ι := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨d, rfl⟩, hn⟩ := Subgroup.mem_inf.mp hx
    exact ⟨d, (mem_normalizer_map_iff ι hι L d).mp hn, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact Subgroup.mem_inf.mpr ⟨⟨d, rfl⟩, (mem_normalizer_map_iff ι hι L d).mpr hd⟩

theorem isSylowTwoOf_map_sylow [Finite D] (hι : Function.Injective ι) (S₀ : Sylow 2 D) :
    IsSylowTwoOf ((S₀ : Subgroup D).map ι) ι.range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine F7.isSylowTwoOf_of_relIndex (Subgroup.map_le_range ι _) (S₀.isPGroup'.map ι) ?_
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hι,
    Subgroup.relIndex_top_right]
  exact S₀.not_dvd_index

theorem borelTitsIn_of_holds [Finite D] (hι : Function.Injective ι) (h : Holds D 2) :
    BorelTitsIn ι.range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro A hA hA0 hAp
  set A₀ := A.comap ι with hA₀
  have hAeq : A₀.map ι = A := Subgroup.map_comap_eq_self hA
  have hA₀0 : A₀ ≠ ⊥ := fun h0 => hA0 (by rw [← hAeq, h0, Subgroup.map_bot])
  have hA₀p : IsPGroup 2 A₀ := by
    intro x
    obtain ⟨k, hk⟩ := hAp ⟨ι x, x.2⟩
    refine ⟨k, Subtype.ext (hι ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨S₀, P₀, hP₀, hN, hcore, hU, hS⟩ := h A₀ hA₀0 hA₀p
  have hAn : ι.range ⊓ Subgroup.normalizer (A : Set K) =
      (Subgroup.normalizer (A₀ : Set D)).map ι := by
    rw [← hAeq]
    exact range_inf_normalizer_eq ι hι A₀
  have hSn : ι.range ⊓ Subgroup.normalizer (((S₀ : Subgroup D).map ι : Subgroup K) : Set K) =
      (Subgroup.normalizer ((S₀ : Subgroup D) : Set D)).map ι :=
    range_inf_normalizer_eq ι hι _
  refine ⟨(S₀ : Subgroup D).map ι, P₀.map ι, isSylowTwoOf_map_sylow ι hι S₀,
    Subgroup.map_le_range ι _, ?_, ?_, ?_, ?_, ?_⟩
  · intro hP
    apply hP₀
    rw [MonoidHom.range_eq_map] at hP
    exact Subgroup.map_injective hι hP
  · rw [hAn]
    exact Subgroup.map_mono hN
  · rw [hAn, pCoreOf_map_injective ι hι, pCoreOf_map_injective ι hι]
    exact Subgroup.map_mono hcore
  · rw [← hAeq, pCoreOf_map_injective ι hι]
    exact Subgroup.map_mono hU
  · rw [hSn]
    exact Subgroup.map_mono hS

end CFSG.Quasithin.H13.F431.AG

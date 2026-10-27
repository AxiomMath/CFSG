module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBComap
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBLevel

public section

namespace CFSG.Quasithin.GoldMLB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.GoldMLA
open scoped commutatorElement

variable {W Y : Type} [Group W] [Finite W] [Group Y] [Finite Y]

theorem LieLevel.comap {π : W →* Y} (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    {S₀ : Subgroup W} {U : Subgroup Y} {P : Fin 2 → Subgroup Y} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hSU : S₀.map π = U) (h : LieLevel (⊤ : Subgroup Y) U P) :
    LieLevel (⊤ : Subgroup W) S₀ (fun j => (P j).comap π) := by
  have hker : π.ker ≤ S₀ := ker_le_sylow π hk hS₀
  have hcomap : ∀ A : Subgroup W, S₀ ≤ A → (A.map π).comap π = A := fun A hA =>
    Subgroup.comap_map_eq_self (hker.trans hA)
  have hmapc : ∀ j, ((P j).comap π).map π = P j := fun j =>
    Subgroup.map_comap_eq_self_of_surjective hπ (P j)
  have hSP : ∀ j, S₀ ≤ (P j).comap π := fun j x hx =>
    h.S_le j (hSU ▸ Subgroup.mem_map_of_mem π hx)
  have hUA : ∀ A : Subgroup W, S₀ ≤ A → U ≤ A.map π := fun A hA =>
    hSU ▸ Subgroup.map_mono hA
  have hperf : ∀ j, (perfectCore ((P j).comap π)).map π = perfectCore (P j) := fun j => by
    rw [map_perfectCore, hmapc]
  have hnorm : ∀ x : W, x ∈ Subgroup.normalizer (S₀ : Set W) ↔
      π x ∈ Subgroup.normalizer (U : Set Y) := fun x => by
    rw [mem_normalizer_iff_comap π hπ hker, hSU]
  refine
    { le_L := fun _ => le_top
      S_le := hSP
      ne := fun he => h.ne (Subgroup.comap_injective hπ he)
      ne_L := fun j he => h.ne_L j
        (Subgroup.comap_injective hπ (he.trans (Subgroup.comap_top π).symm))
      cover := fun A hSA _ hA => ?_
      maxl := fun j A hPA _ => ?_
      solv01 := ?_
      nonsolv := fun A hSA _ hA hns => ?_
      norm_le := fun j x hx => ?_
      solv := fun A hSA _ hs x hx => ?_
      charTwo := fun j => charTwo_comap π hπ hk (h.charTwo j)
      split := fun j g hg => ?_
      hall := fun j x hx k hk' => ?_ }
  ·
    have hne : A.map π ≠ ⊤ := fun he => hA (by rw [← hcomap A hSA, he, Subgroup.comap_top])
    rcases h.cover (A.map π) (hUA A hSA) le_top hne with h1 | h1
    · exact Or.inl (Subgroup.map_le_iff_le_comap.mp h1)
    · exact Or.inr (Subgroup.map_le_iff_le_comap.mp h1)
  ·
    have hSA : S₀ ≤ A := (hSP j).trans hPA
    have h1 : P j ≤ A.map π := by
      rw [← hmapc j]
      exact Subgroup.map_mono hPA
    rcases h.maxl j (A.map π) h1 le_top with h2 | h2
    · left
      rw [← hcomap A hSA, h2]
    · right
      rw [← hcomap A hSA, h2, Subgroup.comap_top]
  ·
    have h1 : ((P 0).comap π ⊓ (P 1).comap π).map π = P 0 ⊓ P 1 := by
      rw [← Subgroup.comap_inf]
      exact Subgroup.map_comap_eq_self_of_surjective hπ _
    exact isSolvable_of_map π hk (by rw [h1]; exact h.solv01)
  ·
    have hne : A.map π ≠ ⊤ := fun he => hA (by rw [← hcomap A hSA, he, Subgroup.comap_top])
    have hns' : ¬ Group.IsSolvable ↥(A.map π) := fun hs => hns (isSolvable_of_map π hk hs)
    obtain ⟨j, hjk, hj⟩ := h.nonsolv (A.map π) (hUA A hSA) le_top hne hns'
    refine ⟨j, fun k => ?_, ?_⟩
    · rw [← Subgroup.map_le_iff_le_comap]
      exact hjk k
    · have h1 : perfectCore ((P j).comap π) ≤ (A.map π).comap π :=
        Subgroup.map_le_iff_le_comap.mp (by rw [hperf]; exact hj)
      rwa [hcomap A hSA] at h1
  ·
    exact Subgroup.mem_comap.mpr (h.norm_le j ⟨Subgroup.mem_top _, (hnorm x).mp hx.2⟩)
  ·
    have hs' : Group.IsSolvable ↥(A.map π) := isSolvable_map π hs
    exact (hnorm x).mpr (h.solv (A.map π) (hUA A hSA) le_top hs' (Subgroup.mem_map_of_mem π hx))
  ·
    have hg' : π g ∈ P j := hg
    obtain ⟨a, ha, b, hb, hab⟩ := h.split j (π g) hg'
    have ha' : a ∈ (perfectCore ((P j).comap π)).map π := by rw [hperf j]; exact ha
    obtain ⟨a₀, ha₀, rfl⟩ := ha'
    have ha₀P : a₀ ∈ (P j).comap π := perfectCore_le _ ha₀
    have hcP : a₀⁻¹ * g ∈ (P j).comap π := ((P j).comap π).mul_mem (((P j).comap π).inv_mem ha₀P) hg
    have hπc : π (a₀⁻¹ * g) = b := by
      rw [map_mul, map_inv, hab]
      group
    refine ⟨a₀, ha₀, a₀⁻¹ * g, mem_leviCent.mpr ⟨hcP, fun x hx => ?_⟩, by group⟩
    have hπx : π x ∈ perfectCore (P j) := by
      rw [← hperf j]
      exact Subgroup.mem_map_of_mem π hx
    have h1 : π ⁅a₀⁻¹ * g, x⁆ ∈ pCoreOf 2 (perfectCore (P j)) := by
      have := (mem_leviCent.mp hb).2 (π x) hπx
      rwa [map_commutatorElement, hπc]
    have h2 : ⁅a₀⁻¹ * g, x⁆ ∈ perfectCore ((P j).comap π) := by
      have hn : a₀⁻¹ * g ∈ Subgroup.normalizer (((P j).comap π : Subgroup W) : Set W) :=
        Subgroup.le_normalizer hcP
      have := conj_mem_perfectCore hn hx
      have hxinv := (perfectCore ((P j).comap π)).inv_mem hx
      have := (perfectCore ((P j).comap π)).mul_mem this hxinv
      simpa [commutatorElement_def, mul_assoc] using this
    have h3 := comap_pCoreOf_inf_le π hk (perfectCore ((P j).comap π))
    rw [hperf j] at h3
    exact h3 ⟨h1, h2⟩
  ·
    have hxP := mem_leviCent.mp hx
    have hπx : π x ∈ leviCent (P j) := by
      refine mem_leviCent.mpr ⟨hxP.1, fun y hy => ?_⟩
      have hy' : y ∈ (perfectCore ((P j).comap π)).map π := by rw [hperf j]; exact hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy'
      have h1 := Subgroup.mem_map_of_mem π (hxP.2 y₀ hy₀)
      rw [map_commutatorElement] at h1
      have h2 := map_pCoreOf_le π hπ (perfectCore ((P j).comap π)) h1
      rw [hperf j] at h2
      exact h2
    have hpow : (π x) ^ 2 ^ k = 1 := by rw [← map_pow, hk', map_one]
    have h3 := h.hall j (π x) hπx k hpow
    have h4 := comap_pCoreOf_inf_le π hk ((P j).comap π)
    rw [hmapc j] at h4
    exact h4 ⟨h3, hxP.1⟩

end CFSG.Quasithin.GoldMLB

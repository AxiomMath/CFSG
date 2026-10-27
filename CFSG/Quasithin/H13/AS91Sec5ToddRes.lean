module

public import CFSG.Quasithin.H13.AS91Sec5Todd
public import CFSG.Quasithin.H13.AS91Sec5ToddFacts
public import CFSG.Quasithin.H13.AS91Sec5KerFacts
public import CFSG.Quasithin.H13.AS91Sec5KerOrbit
public import CFSG.Quasithin.H13.AS91Sec7Plane

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)
open CFSG.Quasithin.H.Mathieu (W11 rho11)
open CFSG.Monster.Code (AutPerm)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

private theorem Eker_le_E (m : G ⧸ c.G2) : c.Eker m ≤ c.E := fun _ he => (c.mem_Eker.1 he).1

private theorem Epl_le_E (σ : G ⧸ c.G3) : c.Epl σ ≤ c.E := fun _ he => (c.mem_Epl.1 he).1

end Loc49

namespace ResM24T

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24T c)

theorem card_eq_of_mem_iff {H : Subgroup G} (hH : H ≤ c.E) {B : Subgroup W11}
    (hB : ∀ e : ↥c.E, (e : G) ∈ H ↔ ρ.todd e ∈ B) : Nat.card H = Nat.card B := by
  have e1 : Nat.card (H.subgroupOf c.E) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  have e2 : (H.subgroupOf c.E).map ρ.todd.toMonoidHom = B := by
    ext w
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact (hB e).1 he
    · intro hw
      refine ⟨ρ.todd.symm w, ?_, by simp⟩
      exact (hB _).2 (by simpa using hw)
  rw [← e1, ← e2, Subgroup.card_map_of_injective (MulEquiv.injective ρ.todd)]


theorem mem_Eker_iff {m : G ⧸ c.G2} (hm : c.OnL c.x0 m) (e : ↥c.E) :
    (e : G) ∈ c.Eker m ↔ ρ.todd e ∈ M24G.annOf (ρ.trio m) := by
  let A : Subgroup W11 := ((c.Eker m).subgroupOf c.E).map ρ.todd.toMonoidHom
  have hmemA : ∀ e : ↥c.E, ρ.todd e ∈ A ↔ (e : G) ∈ c.Eker m := fun e => by
    refine ⟨?_, fun he => ⟨e, he, rfl⟩⟩
    rintro ⟨e', he', he'e⟩
    obtain rfl : e' = e := ρ.todd.injective he'e
    exact he'
  have hcard : Nat.card A = 512 := by
    have h1 : Nat.card A = Nat.card ((c.Eker m).subgroupOf c.E) :=
      Subgroup.card_map_of_injective (MulEquiv.injective ρ.todd)
    have h2 : Nat.card ((c.Eker m).subgroupOf c.E) = Nat.card (c.Eker m) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (c.Eker_le_E m)).toEquiv
    rw [h1, h2, c.card_Eker hm]
    norm_num
  have hinv : ∀ (σ : S24) (hσ : σ ∈ M24g), σ • ρ.trio m = ρ.trio m → ∀ w ∈ A,
      rho11 AutPerm le_rfl ⟨σ, hσ⟩ w ∈ A := by
    intro σ hσ hσt w hw
    obtain ⟨h, rfl⟩ := ρ.exists_φ_eq hσ
    have hhm : (h : G) • m = m := by
      refine ρ.trio_injOn ((c.cInc_x0_smul h.2).2 hm) hm ?_
      rw [ρ.trio_smul_line h hm]
      exact hσt
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.1 hw
    have he'' : (h : G) * (e' : G) * (h : G)⁻¹ ∈ c.Eker m := by
      have h1 := (c.conj_mem_Eker_iff h (m := m) (e := (e' : G))).2 he'
      rwa [hhm] at h1
    exact Subgroup.mem_map.2 ⟨⟨(h : G) * (e' : G) * (h : G)⁻¹, c.conj_mem_E h e'.2⟩, he'',
      ρ.todd_equiv h e'⟩
  have hA : A = M24G.annOf (ρ.trio m) :=
    M24G.eq_annOf_of_invariant (ρ.isTrio_trio hm) A hcard hinv
  have h := hmemA e
  rw [hA] at h
  exact h.symm

theorem card_Eker_inf_eq {m n : G ⧸ c.G2} (hm : c.OnL c.x0 m) (hn : c.OnL c.x0 n) :
    Nat.card ↥(c.Eker m ⊓ c.Eker n) =
      Nat.card ↥(M24G.annOf (ρ.trio m) ⊓ M24G.annOf (ρ.trio n)) :=
  ρ.card_eq_of_mem_iff (inf_le_left.trans (c.Eker_le_E m)) fun e => by
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ρ.mem_Eker_iff hm, ρ.mem_Eker_iff hn]

theorem delta_of_mem_deltaAt {i : Fin 5} {m n : G ⧸ c.G2} (hm : c.OnL c.x0 m)
    (hn : c.OnL c.x0 n) (h : n ∈ c.deltaAt i c.x0 m) :
    M24G.Delta (ρ.trio m) (ρ.trio n) i := by
  have h1 := (ρ.mem_deltaAt_iff i (one_smul G c.x0) hm hn).1 h
  simpa using h1

include ρ in
theorem card_Eker_inf_one {m n : G ⧸ c.G2} (hm : c.OnL c.x0 m) (hn : c.OnL c.x0 n)
    (h : n ∈ c.deltaAt 1 c.x0 m) : Nat.card ↥(c.Eker m ⊓ c.Eker n) = 2 ^ 8 := by
  rw [ρ.card_Eker_inf_eq hm hn, M24G.card_annOf_inf_one (ρ.isTrio_trio hm) (ρ.isTrio_trio hn)
    (ρ.delta_of_mem_deltaAt hm hn h)]
  norm_num

include ρ in
theorem card_Eker_inf_two {m n : G ⧸ c.G2} (hm : c.OnL c.x0 m) (hn : c.OnL c.x0 n)
    (h : n ∈ c.deltaAt 2 c.x0 m ∨ n ∈ c.deltaAt 3 c.x0 m ∨ n ∈ c.deltaAt 4 c.x0 m) :
    Nat.card ↥(c.Eker m ⊓ c.Eker n) = 2 ^ 7 := by
  have hΔ : M24G.Delta (ρ.trio m) (ρ.trio n) 2 ∨ M24G.Delta (ρ.trio m) (ρ.trio n) 3 ∨
      M24G.Delta (ρ.trio m) (ρ.trio n) 4 := by
    rcases h with h | h | h
    · exact Or.inl (ρ.delta_of_mem_deltaAt hm hn h)
    · exact Or.inr (Or.inl (ρ.delta_of_mem_deltaAt hm hn h))
    · exact Or.inr (Or.inr (ρ.delta_of_mem_deltaAt hm hn h))
  rw [ρ.card_Eker_inf_eq hm hn, M24G.card_annOf_inf_two (ρ.isTrio_trio hm) (ρ.isTrio_trio hn) hΔ]
  norm_num

include ρ in
theorem smul_two {m n : G ⧸ c.G2} (hm : c.OnL c.x0 m) (hn : c.OnL c.x0 n)
    (h : n ∈ c.deltaAt 2 c.x0 m ∨ n ∈ c.deltaAt 3 c.x0 m ∨ n ∈ c.deltaAt 4 c.x0 m)
    {p q : G ⧸ c.G1} (hp : c.OnL p n) (hpx : p ≠ c.x0) (hq : c.OnL q n) (hqx : q ≠ c.x0) :
    ∃ e ∈ c.Eker m, e • p = q :=
  c.smul_of_card_inf_eq hm hn (ρ.card_Eker_inf_two hm hn h) hp hpx hq hqx

include ρ in
theorem orbit_one {m n : G ⧸ c.G2} (hm : c.OnL c.x0 m) (hn : c.OnL c.x0 n)
    (h : n ∈ c.deltaAt 1 c.x0 m) {p : G ⧸ c.G1} (hp : c.OnL p n) (hpx : p ≠ c.x0) :
    ∃ q, c.OnL q n ∧ q ≠ c.x0 ∧ q ≠ p ∧ (∃ e ∈ c.Eker m, e • p = q) ∧
      ∀ e ∈ c.Eker m, e • p = p ∨ e • p = q :=
  c.orbit_of_card_inf_eq hm hn (ρ.card_Eker_inf_one hm hn h) hp hpx

include ρ in
theorem not_le {m n : G ⧸ c.G2} (hm : c.OnL c.x0 m) (hn : c.OnL c.x0 n) (hmn : m ≠ n) :
    ¬ c.Eker n ≤ c.Eker m := by
  obtain ⟨i, hi, -⟩ := ρ.deltaAt_existsUnique hm hn
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hmn ((ρ.mem_deltaAt_zero_iff hm hn).1 hi).symm
  refine c.not_le_of_card_inf_lt hn ?_
  fin_cases i
  · exact absurd rfl hi0
  · rw [ρ.card_Eker_inf_one hm hn hi]
    norm_num
  · rw [ρ.card_Eker_inf_two hm hn (Or.inl hi)]
    norm_num
  · rw [ρ.card_Eker_inf_two hm hn (Or.inr (Or.inl hi))]
    norm_num
  · rw [ρ.card_Eker_inf_two hm hn (Or.inr (Or.inr hi))]
    norm_num

theorem exists_line_of_mem_triosOf_one {σ : G ⧸ c.G3} (hσ : c.OnP c.x0 σ)
    {t : Finset (Finset (Fin 24))} (ht : t ∈ M24G.triosOf (ρ.sext σ)) :
    ∃ n, c.OnL c.x0 n ∧ c.LnP n σ ∧ ρ.trio n = t := by
  have h := ρ.exists_line_of_mem_triosOf (g := 1) (one_smul G c.x0) hσ (by simpa using ht)
  simpa using h

theorem trio_mem_triosOf_one {σ : G ⧸ c.G3} {n : G ⧸ c.G2} (hσ : c.OnP c.x0 σ)
    (hn : c.OnL c.x0 n) (hnσ : c.LnP n σ) : ρ.trio n ∈ M24G.triosOf (ρ.sext σ) := by
  have h := ρ.trio_mem_triosOf (g := 1) (one_smul G c.x0) hσ hn hnσ
  simpa using h

theorem mem_Epl_iff {σ : G ⧸ c.G3} (hσ : c.OnP c.x0 σ) (e : ↥c.E) :
    (e : G) ∈ c.Epl σ ↔ ρ.todd e ∈ M24G.annOf (M24G.octsOf (ρ.sext σ)) := by
  rw [M24G.mem_annOf_octsOf_iff (ρ.isSextet_sext hσ), c.mem_Epl]
  constructor
  · rintro ⟨-, h⟩ t ht
    obtain ⟨n, hn, hnσ, rfl⟩ := ρ.exists_line_of_mem_triosOf_one hσ ht
    exact (ρ.mem_Eker_iff hn e).1 (h n hn hnσ)
  · intro h
    exact ⟨e.2, fun m hm hmσ => (ρ.mem_Eker_iff hm e).2 (h _ (ρ.trio_mem_triosOf_one hσ hm hmσ))⟩

include ρ in
theorem card_Epl {σ : G ⧸ c.G3} (hσ : c.OnP c.x0 σ) : Nat.card (c.Epl σ) = 2 ^ 7 := by
  rw [ρ.card_eq_of_mem_iff (c.Epl_le_E σ) (ρ.mem_Epl_iff hσ),
    M24G.card_annOf_octsOf (ρ.isSextet_sext hσ)]
  norm_num

include ρ in
theorem Epl_inj {σ σ' : G ⧸ c.G3} (hσ : c.OnP c.x0 σ) (hσ' : c.OnP c.x0 σ')
    (h : c.Epl σ = c.Epl σ') : σ = σ' := by
  have hA : M24G.annOf (M24G.octsOf (ρ.sext σ)) = M24G.annOf (M24G.octsOf (ρ.sext σ')) := by
    ext w
    obtain ⟨e, rfl⟩ := ρ.todd.surjective w
    rw [← ρ.mem_Epl_iff hσ, ← ρ.mem_Epl_iff hσ', h]
  exact ρ.sext_injOn hσ hσ'
    (M24G.annOf_octsOf_inj (ρ.isSextet_sext hσ) (ρ.isSextet_sext hσ') hA)

include ρ in
theorem kerFacts : c.KerFacts where
  card_inf_one := ρ.card_Eker_inf_one
  card_inf_two := ρ.card_Eker_inf_two
  smul_two := ρ.smul_two
  orbit_one := ρ.orbit_one
  not_le := ρ.not_le
  card_Epl := ρ.card_Epl
  Epl_inj := ρ.Epl_inj

end ResM24T

theorem kerFacts_of
    (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24T c)) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z), c.KerFacts := by
  intro G _ _ z hJ c
  obtain ⟨ρ⟩ := hres G z hJ c
  exact ρ.kerFacts

end CFSG.Quasithin.H13.AS91

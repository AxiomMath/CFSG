module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompA
public import CFSG.Quasithin.H13.L32ACSkPfB
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.L32A.C.SkPf

variable {M : Type} [Group M]

@[expose] def CBAt (M : Type) [Group M] (U : Subgroup M) : Prop :=
  ∀ b ∈ Subgroup.normalizer (U : Set M), (∀ u ∈ U, b * u = u * b) → b ∈ U

@[expose] def InvAt (M : Type) [Group M] (U : Subgroup M) : Prop :=
  ∀ z ∈ U, z ≠ 1 → (∀ u ∈ U, z * u = u * z) →
    ∃ y : M, Odd (orderOf y) ∧ z * y * z⁻¹ = y⁻¹ ∧ ¬ (y ^ 3 = 1 ∨ y ^ 5 = 1)

theorem map_eq_of_fix {U : Subgroup M} {ν : MulAut M} (hfix : ∀ u ∈ U, ν u = u) :
    U.map ν.toMonoidHom = U := by
  ext x
  refine ⟨?_, fun hx => ⟨x, hx, hfix x hx⟩⟩
  rintro ⟨u, hu, rfl⟩
  change ν u ∈ U
  rw [hfix u hu]
  exact hu

theorem normalizer_le_centMod_of_fix {U : Subgroup M} {ν : MulAut M} (hfix : ∀ u ∈ U, ν u = u)
    (hCB : CBAt M U) : Subgroup.normalizer (U : Set M) ≤ centMod U ν := by
  intro b hb
  refine ⟨hb, ?_⟩
  have hνb : ν b ∈ Subgroup.normalizer (U : Set M) := map_mem_normalizer (map_eq_of_fix hfix) hb
  have hc : ∀ u ∈ U, (b⁻¹ * ν b) * u = u * (b⁻¹ * ν b) := by
    intro u hu
    have hbu : b * u * b⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hb u).mp hu
    have h1 : ν (b * u * b⁻¹) = b * u * b⁻¹ := hfix _ hbu
    rw [map_mul, map_mul, map_inv, hfix u hu] at h1
    calc (b⁻¹ * ν b) * u = b⁻¹ * (ν b * u * (ν b)⁻¹) * ν b := by group
      _ = b⁻¹ * (b * u * b⁻¹) * ν b := by rw [h1]
      _ = u * (b⁻¹ * ν b) := by group
  have hmem : b⁻¹ * ν b ∈ U := hCB _ (mul_mem (inv_mem hb) hνb) hc
  have h2 := (Subgroup.mem_normalizer_iff.mp hb _).mp hmem
  have e : b * (b⁻¹ * ν b) * b⁻¹ = ν b * b⁻¹ := by group
  rwa [e] at h2

theorem mem_normalizer_of_centralizes {U : Subgroup M} {z : M} (hz : ∀ u ∈ U, z * u = u * z) :
    z ∈ Subgroup.normalizer (U : Set M) :=
  Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun u hu => (hz u hu).symm)

theorem exists_eq_conj_of_fix {U : Subgroup M} (hN4 : N4At M U) (h34 : ¬ IsPSL 3 2 2 M)
    (hCB : CBAt M U) {ν : MulAut M} (hν : ∃ k : ℕ, ν ^ 2 ^ k = 1) (hfix : ∀ u ∈ U, ν u = u) :
    ∃ z ∈ U, (∀ u ∈ U, z * u = u * z) ∧ ν = MulAut.conj z := by
  rcases hN4 ν hν (map_eq_of_fix hfix) (normalizer_le_centMod_of_fix hfix hCB) with
    ⟨z, rfl⟩ | h34'
  · have hzc : ∀ u ∈ U, z * u = u * z := fun u hu => by
      have h1 : MulAut.conj z u = u := hfix u hu
      rw [MulAut.conj_apply] at h1
      calc z * u = z * u * z⁻¹ * z := by group
        _ = u * z := by rw [h1]
    exact ⟨z, hCB z (mem_normalizer_of_centralizes hzc) hzc, hzc, rfl⟩
  · exact absurd h34' h34

theorem AutConf.exists_fix [Finite M] {U : Subgroup M} (hU : IsSylowTwoOf U ⊤) {ν : MulAut M}
    {Lb Pb : Subgroup (MulAut M)} (h : AutConf M ν Lb Pb) :
    ∃ (ν' : MulAut M) (Lb' Pb' : Subgroup (MulAut M)), AutConf M ν' Lb' Pb' ∧
      ∀ u ∈ U, ν' u = u := by
  obtain ⟨S, hS, hSν⟩ := h.sylow
  obtain ⟨g, hg⟩ := exists_map_conj_eq hS hU
  refine ⟨_, _, _, h.map (MulAut.conj g), ?_⟩
  intro u hu
  rw [← hg] at hu
  obtain ⟨s, hs, rfl⟩ := hu
  change MulAut.conj g (ν ((MulAut.conj g).symm (MulAut.conj g s))) = MulAut.conj g s
  rw [MulEquiv.symm_apply_apply, hSν s hs]

theorem not_autConf_of_at [Finite M] {U : Subgroup M} (hU : IsSylowTwoOf U ⊤) (hN4 : N4At M U)
    (h34 : ¬ IsPSL 3 2 2 M) (hCB : CBAt M U) (hInv : InvAt M U) {ν : MulAut M}
    {Lb Pb : Subgroup (MulAut M)} (h : AutConf M ν Lb Pb) : False := by
  obtain ⟨ν', Lb', Pb', h', hfix⟩ := h.exists_fix hU
  obtain ⟨z, hzU, hzc, rfl⟩ := exists_eq_conj_of_fix hN4 h34 hCB ⟨1, by simpa using h'.sq⟩ hfix
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact h'.ne_one (map_one _)
  obtain ⟨y, hodd, hinv, hy⟩ := hInv z hzU hz1 hzc
  exact hy (h'.inv y hodd (by rw [MulAut.conj_apply]; exact hinv))

section Map

variable {M' : Type} [Group M']

theorem CBAt.map (e : M ≃* M') {U : Subgroup M} (h : CBAt M U) :
    CBAt M' (U.map e.toMonoidHom) := by
  intro b hb hc
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [normalizer_map, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hb
  refine ⟨b, h b hb fun u hu => e.injective ?_, rfl⟩
  rw [map_mul, map_mul]
  exact hc (e u) ⟨u, hu, rfl⟩

theorem InvAt.map (e : M ≃* M') {U : Subgroup M} (h : InvAt M U) :
    InvAt M' (U.map e.toMonoidHom) := by
  rintro _ ⟨z, hz, rfl⟩ hz1 hzc
  have hz1' : z ≠ 1 := fun h1 => hz1 (by rw [h1]; exact map_one e)
  have hzc' : ∀ u ∈ U, z * u = u * z := fun u hu => e.injective (by
    rw [map_mul, map_mul]
    exact hzc (e u) ⟨u, hu, rfl⟩)
  obtain ⟨y, hodd, hinv, hy⟩ := h z hz hz1' hzc'
  refine ⟨e y, ?_, ?_, ?_⟩
  · rwa [MulEquiv.orderOf_eq]
  · change e z * e y * (e z)⁻¹ = (e y)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, hinv, map_inv]
  · rintro (h3 | h5)
    · exact hy (Or.inl (e.injective (by rw [map_pow, h3, map_one])))
    · exact hy (Or.inr (e.injective (by rw [map_pow, h5, map_one])))

end Map

theorem card_of_isPSL34 {X : Type} [Group X] (h : IsPSL 3 2 2 X) : Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

end CFSG.Quasithin.H13.S126C

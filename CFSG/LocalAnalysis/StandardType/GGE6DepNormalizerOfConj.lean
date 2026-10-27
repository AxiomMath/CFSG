module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs

public section

namespace CFSG.StandardType.GGE6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem conj_mem_bstar_of_conj_mem_normalizer_range {p : ℕ} (hp : p.Prime)
    {Bs L : Subgroup G} {x : G} (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs : IsElemAbelian p Bs) (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥L))
    (hBsL : ∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k) {n : G} (hnL : n ∈ L)
    (hn : MulAut.conj (⟨n, hnL⟩ : ↥L) ∈
      Subgroup.normalizer ((ggGamma L hBsN).range : Set (MulAut ↥L))) {b : G} (hb : b ∈ Bs) :
    n * b * n⁻¹ ∈ Bs := by
  have hx : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := hker ▸ Subgroup.mem_zpowers x
  have hxpow : ∀ k : ℕ, x ^ k ∈ Bs ∧ ∀ m ∈ L, m * x ^ k = x ^ k * m := fun k =>
    ⟨(Bs.pow_mem hx.1 k), fun m hm =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hx.2 k) m hm⟩
  have hsplit : ∀ b ∈ Bs, ∃ l ∈ L, l ∈ Bs ∧ ∃ k : ℕ, b = l * x ^ k := by
    intro b hb
    obtain ⟨l, hlL, k, hbl⟩ := hBsL b hb
    refine ⟨l, hlL, ?_, k, hbl⟩
    have h := Bs.mul_mem hb (Bs.inv_mem (hxpow k).1)
    rwa [hbl, mul_inv_cancel_right] at h
  obtain ⟨l, hlL, hlBs, k, rfl⟩ := hsplit b hb
  set γ := ggGamma L hBsN with hγ
  have hmem : MulAut.conj (⟨n, hnL⟩ : ↥L) * γ ⟨l, hlBs⟩ * (MulAut.conj (⟨n, hnL⟩ : ↥L))⁻¹ ∈
      γ.range := (Subgroup.mem_normalizer_iff.mp hn (γ ⟨l, hlBs⟩)).mp ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ := MonoidHom.mem_range.mp hmem
  have hbm : ∀ m ∈ L, (b' : G) * m * (b' : G)⁻¹ = (n * l * n⁻¹) * m * (n * l * n⁻¹)⁻¹ := by
    intro m hm
    have h1 := congrArg (fun a : MulAut ↥L => ((a ⟨m, hm⟩ : ↥L) : G)) hb'
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, hγ] at h1
    push_cast at h1
    rw [ggGamma_coe, ggGamma_coe] at h1
    push_cast at h1
    rw [h1]
    group
  obtain ⟨l', hl'L, hl'Bs, k', hb'eq⟩ := hsplit b' b'.2
  set c := n * l * n⁻¹ with hc
  have hcL : c ∈ L := L.mul_mem (L.mul_mem hnL hlL) (L.inv_mem hnL)
  set z := l'⁻¹ * c with hz
  have hzL : z ∈ L := L.mul_mem (L.inv_mem hl'L) hcL
  have hzc : ∀ m ∈ L, m * z = z * m := by
    intro m hm
    have h1 := hbm m hm
    rw [hb'eq] at h1
    have h2 : l' * m * l'⁻¹ = c * m * c⁻¹ := by
      rw [← h1]
      have hxm := (hxpow k').2 m hm
      calc l' * m * l'⁻¹ = l' * (m * x ^ k') * (x ^ k')⁻¹ * l'⁻¹ := by group
        _ = l' * (x ^ k' * m) * (x ^ k')⁻¹ * l'⁻¹ := by rw [hxm]
        _ = l' * x ^ k' * m * (l' * x ^ k')⁻¹ := by group
    have h3 : m = z * m * z⁻¹ := by
      rw [hz]
      calc m = l'⁻¹ * (l' * m * l'⁻¹) * l' := by group
        _ = l'⁻¹ * (c * m * c⁻¹) * l' := by rw [h2]
        _ = l'⁻¹ * c * m * (l'⁻¹ * c)⁻¹ := by group
    calc m * z = (z * m * z⁻¹) * z := by rw [← h3]
      _ = z * m := by group
  have hl'p : l' ^ p = 1 := hBs.2 l' hl'Bs
  have hcp : c ^ p = 1 := by
    rw [hc, conj_pow, hBs.2 l hlBs]
    group
  have hzp : z ^ p = 1 := by
    have hcomm : Commute l' z := hzc l' hl'L
    have hcl : c = l' * z := by rw [hz]; group
    rw [hcl, hcomm.mul_pow, hl'p, one_mul] at hcp
    exact hcp
  have hz1 : z = 1 := by
    let z' : ↥(Subgroup.center ↥L) :=
      ⟨⟨z, hzL⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2)⟩
    have hz'p : z' ^ p = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hzp
    have h1 : orderOf z' ∣ p := orderOf_dvd_of_pow_eq_one hz'p
    have h2 : orderOf z' ∣ Nat.card ↥(Subgroup.center ↥L) := orderOf_dvd_natCard z'
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · have hz'1 : z' = 1 := orderOf_eq_one_iff.mp h
      exact congrArg (fun t : ↥(Subgroup.center ↥L) => ((t : ↥L) : G)) hz'1
    · exact absurd (h ▸ h2) hZ
  have hcl : c = l' := by
    have : c = l' * z := by rw [hz]; group
    rw [this, hz1, mul_one]
  have hnx : n * x ^ k * n⁻¹ = x ^ k := by
    rw [(hxpow k).2 n hnL]
    group
  have hres : n * (l * x ^ k) * n⁻¹ = l' * x ^ k := by
    calc n * (l * x ^ k) * n⁻¹ = (n * l * n⁻¹) * (n * x ^ k * n⁻¹) := by group
      _ = l' * x ^ k := by rw [hnx, ← hc, hcl]
  rw [hres]
  exact Bs.mul_mem hl'Bs (hxpow k).1

theorem mem_normalizer_of_conj_mem_normalizer_range {p : ℕ} (hp : p.Prime) {Bs L : Subgroup G}
    {x : G} (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hBs : IsElemAbelian p Bs)
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥L))
    (hBsL : ∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k) {n : G} (hnL : n ∈ L)
    (hn : MulAut.conj (⟨n, hnL⟩ : ↥L) ∈
      Subgroup.normalizer ((ggGamma L hBsN).range : Set (MulAut ↥L))) :
    n ∈ Subgroup.normalizer (Bs : Set G) := by
  have hn' : MulAut.conj (⟨n⁻¹, L.inv_mem hnL⟩ : ↥L) ∈
      Subgroup.normalizer ((ggGamma L hBsN).range : Set (MulAut ↥L)) := by
    have h : MulAut.conj (⟨n⁻¹, L.inv_mem hnL⟩ : ↥L) = (MulAut.conj (⟨n, hnL⟩ : ↥L))⁻¹ := by
      rw [← map_inv]
      rfl
    rw [h]
    exact Subgroup.inv_mem _ hn
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨conj_mem_bstar_of_conj_mem_normalizer_range hp hBsN hBs hker hZ hBsL hnL hn, fun hh => ?_⟩
  have h2 := conj_mem_bstar_of_conj_mem_normalizer_range hp hBsN hBs hker hZ hBsL
    (L.inv_mem hnL) hn' hh
  have e : n⁻¹ * (n * h * n⁻¹) * n⁻¹⁻¹ = h := by group
  rwa [e] at h2

end CFSG.StandardType.GGE6Dep

end

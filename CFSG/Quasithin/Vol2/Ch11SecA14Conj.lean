module

public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem isSubnormal_map_equiv (e : G ≃* G) {H K : Subgroup G} (h : IsSubnormal H K) :
    IsSubnormal (H.map e.toMonoidHom) (K.map e.toMonoidHom) :=
  h.map e.toMonoidHom

theorem map_map_symm (e : G ≃* G) (H : Subgroup G) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  ext x
  simp

theorem isCComponent_map_equiv (e : G ≃* G) {K X : Subgroup G} (h : quasithinIsCComponent K X) :
    quasithinIsCComponent (K.map e.toMonoidHom) (X.map e.toMonoidHom) := by
  obtain ⟨hK1, hKK, hKX, hmin⟩ := h
  refine ⟨?_, ?_, isSubnormal_map_equiv e hKX, ?_⟩
  · intro hb
    apply hK1
    rw [← map_map_symm e K, hb, Subgroup.map_bot]
  · rw [← Subgroup.map_commutator, hKK]
  · intro K' hK' hK'1 hK'K' hsn
    have hKK : (K'.map e.symm.toMonoidHom).map e.toMonoidHom = K' := by
      have := map_map_symm e.symm K'
      rwa [MulEquiv.symm_symm] at this
    have h1 : K'.map e.symm.toMonoidHom < K := by
      refine lt_of_le_of_ne ?_ fun heq => hK'.ne ?_
      · have := Subgroup.map_mono (f := e.symm.toMonoidHom) hK'.le
        rwa [map_map_symm] at this
      · rw [← hKK, heq]
    refine hmin _ h1 ?_ ?_ ?_
    · intro hb
      apply hK'1
      rw [← map_map_symm e.symm K', MulEquiv.symm_symm, hb, Subgroup.map_bot]
    · rw [← Subgroup.map_commutator, hK'K']
    · have := isSubnormal_map_equiv e.symm hsn
      rwa [map_map_symm] at this

theorem mem_map_conj {H : Subgroup G} {g x : G} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  rw [mem_map_conj]
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x)
  rw [inv_inv] at this
  exact this.symm

theorem map_conj_normalizer (H : Subgroup G) (g : G) :
    (Subgroup.normalizer (H : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  ext x
  rw [mem_map_conj, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx y
    rw [mem_map_conj, mem_map_conj]
    have := hx (g⁻¹ * y * g)
    rw [this]
    constructor <;> intro h <;> convert h using 1 <;> group
  · intro hx y
    have := hx (g * y * g⁻¹)
    rw [mem_map_conj, mem_map_conj] at this
    constructor
    · intro hy
      have h1 := this.mp (by simpa [mul_assoc] using hy)
      convert h1 using 1
      group
    · intro hy
      have h1 := this.mpr (by convert hy using 1; group)
      simpa [mul_assoc] using h1

theorem map_conj_centralizer (H : Subgroup G) (g : G) :
    (Subgroup.centralizer (H : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  ext x
  rw [mem_map_conj, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    rw [SetLike.mem_coe, mem_map_conj] at hy
    have := hx _ hy
    calc y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = x * y := by group
  · intro hx y hy
    have h1 : g * y * g⁻¹ ∈ ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
      rw [SetLike.mem_coe, mem_map_conj]
      simpa [mul_assoc] using hy
    have := hx _ h1
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * x * g * y := by group

variable [Finite G]

theorem map_conj_perfectCore (H : Subgroup G) (g : G) :
    (perfectCore H).map (MulAut.conj g).toMonoidHom =
      perfectCore (H.map (MulAut.conj g).toMonoidHom) :=
  map_perfectCore _ H

omit [Finite G] in
theorem mem_normalizer_map_conj {H : Subgroup G} {w t : G} :
    t ∈ Subgroup.normalizer ((H.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G) ↔
      w⁻¹ * t * w ∈ Subgroup.normalizer (H : Set G) := by
  rw [← map_conj_normalizer, mem_map_conj]

theorem map_conj_lOf {L : Subgroup G} (U : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    (LOf L U).map (MulAut.conj g).toMonoidHom = LOf L (U.map (MulAut.conj g).toMonoidHom) := by
  rw [LOf, map_conj_perfectCore]
  congr 1
  ext x
  rw [mem_map_conj, Subgroup.mem_inf, Subgroup.mem_inf, mem_normalizer_map_conj]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := (Subgroup.mem_normalizer_iff.mp hg _).mp h1
    simpa [mul_assoc] using this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp h1
    simpa using this

theorem mem_normalizer_of_map_le {N : Subgroup G} {g : G}
    (h : N.map (MulAut.conj g).toMonoidHom ≤ N) : g ∈ Subgroup.normalizer (N : Set G) := by
  have hc : Nat.card ↥(N.map (MulAut.conj g).toMonoidHom) = Nat.card ↥N :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq := Subgroup.eq_of_le_of_card_ge h (le_of_eq hc.symm)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    apply h
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq, mem_map_conj] at hx
    simpa [mul_assoc] using hx

end CFSG.Quasithin.Vol2.Ch11.SecA

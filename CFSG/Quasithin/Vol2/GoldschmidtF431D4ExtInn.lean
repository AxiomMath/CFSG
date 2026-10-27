module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Datum
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Resid
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Props
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Am

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42.Am CFSG.Quasithin.D4Hex

section Residual

variable {G : Type} [Group G] {M : Subgroup G} {Q : Type} [Group Q]

theorem map_mem_of_mem_twoPrimeResidual (f : ↥M →* Q) (J : Subgroup Q) [J.Normal]
    (hodd : ¬ 2 ∣ J.relIndex f.range) {z : G} (hz : z ∈ twoPrimeResidual M) :
    ∃ hzM : z ∈ M, f ⟨z, hzM⟩ ∈ J := by
  have hzM : z ∈ M := twoPrimeResidual_le M hz
  refine ⟨hzM, ?_⟩
  set K' : Subgroup ↥M := J.comap f with hK'
  set N : Subgroup G := K'.map M.subtype with hN
  have hconj : ∀ g ∈ M, ∀ h ∈ N, g * h * g⁻¹ ∈ N := by
    intro g hg h hh
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hh
    refine Subgroup.mem_map.2 ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, ?_, rfl⟩
    exact (inferInstance : K'.Normal).conj_mem k hk ⟨g, hg⟩
  have hnorm : M ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
    Subgroup.mem_normalizer_iff.2 fun h => ⟨hconj g hg h, fun hh => by
      have := hconj g⁻¹ (M.inv_mem hg) _ hh
      simpa [mul_assoc] using this⟩
  have hsub : N.subgroupOf M = K' := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
      have : k = x := Subtype.ext hkx
      rwa [this] at hk
    · intro hx
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
  have hidx : N.relIndex M = J.relIndex f.range := by
    rw [Subgroup.relIndex, hsub, hK', Subgroup.index_comap]
  have hres := mem_of_mem_twoPrimeResidual (Subgroup.map_subtype_le K') hnorm
    (by rw [hidx]; exact hodd) hz
  obtain ⟨k, hk, hkz⟩ := Subgroup.mem_map.1 hres
  have : k = ⟨z, hzM⟩ := Subtype.ext hkz
  rw [← this]
  exact hk

end Residual

section Inn

variable {D : Type} [Group D] {G : Type} [Group G] {M1 M2 : Subgroup G}

theorem normal_range_conj : (MulAut.conj : D →* MulAut D).range.Normal where
  conj_mem := by
    rintro _ ⟨d, rfl⟩ φ
    refine ⟨φ d, ?_⟩
    ext y
    show φ d * y * (φ d)⁻¹ = φ (d * φ.symm y * d⁻¹)
    simp [map_mul, map_inv]

namespace LieExt

theorem exists_zero_data_inn [Finite G] (E : LieExt D M1 M2)
    (hZ : Function.Injective (MulAut.conj : D →* MulAut D))
    (hodd : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index) {z : G}
    (hzr : z ∈ twoPrimeResidual M1)
    (hzc : z ∈ Subgroup.centralizer (twoPrimeResidual M1 : Set G)) (hz2 : z ^ 2 = 1)
    (hz : z ≠ 1) :
    ∃ n : D, ((E.phi1 ⟨z, twoPrimeResidual_le M1 hzr⟩ : ↥E.N1) : MulAut D) = MulAut.conj n ∧
      n ≠ 1 ∧ n * n = 1 ∧ (∀ x, x ∈ E.P1 ↔ n * x * n⁻¹ ∈ E.P1) ∧
      ∀ s : D, (∀ x, x ∈ E.P1 ↔ s * x * s⁻¹ ∈ E.P1) → (∃ k : ℕ, orderOf s = 2 ^ k) →
        n * s = s * n := by
  have hz1 : z ∈ M1 := twoPrimeResidual_le M1 hzr
  have : (MulAut.conj : D →* MulAut D).range.Normal := normal_range_conj
  set α : ↥E.N1 := E.phi1 ⟨z, hz1⟩ with hα
  set f : ↥M1 →* MulAut D := E.N1.subtype.comp E.phi1.toMonoidHom with hf
  have hrange : f.range = E.N1 := by
    rw [hf, MonoidHom.range_comp, MonoidHom.range_eq_top.2 E.phi1.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hodd' : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.relIndex f.range := fun h =>
    hodd (h.trans (by
      rw [hrange]
      exact Subgroup.relIndex_dvd_index_of_normal _ _))
  obtain ⟨hzM', hαJ⟩ := map_mem_of_mem_twoPrimeResidual f (MulAut.conj : D →* MulAut D).range
    hodd' hzr
  obtain ⟨n, hn⟩ := hαJ
  have hαst : ∀ x, x ∈ E.P1 ↔ (α : MulAut D) x ∈ E.P1 := α.2.2
  have hz1' : (⟨z, hz1⟩ : ↥M1) ≠ 1 := fun h => hz (congrArg Subtype.val h)
  have hsq : (⟨z, hz1⟩ : ↥M1) * ⟨z, hz1⟩ = 1 :=
    Subtype.ext (by simpa [pow_two] using hz2)
  have hn' : MulAut.conj n = (α : MulAut D) := hn
  refine ⟨n, hn'.symm, ?_, ?_, fun x => ?_, ?_⟩
  · rintro rfl
    apply hz1'
    apply E.phi1.injective
    apply Subtype.ext
    rw [map_one]
    show (α : MulAut D) = 1
    rw [← hn']
    simp
  · apply hZ
    have h1 : α * α = 1 := by
      rw [hα, ← map_mul, hsq, map_one]
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_mul, ← hn', ← map_mul] at h2
    simpa using h2
  · have := hαst x
    rw [← hn'] at this
    exact this
  · intro s hs hso
    have hsM : MulAut.conj s ∈ E.Mbar := E.inn_le ⟨s, rfl⟩
    have hsst : MulAut.conj s ∈ autStab E.P1 := fun x => hs x
    set b : ↥E.N1 := ⟨MulAut.conj s, hsM, hsst⟩ with hb
    set m : ↥M1 := E.phi1.symm b with hm
    have hord : ∃ k : ℕ, orderOf (m : G) = 2 ^ k := by
      obtain ⟨k, hk⟩ := hso
      refine ⟨k, ?_⟩
      have hordb : orderOf b = 2 ^ k := by
        rw [← Subgroup.orderOf_coe b]
        show orderOf (MulAut.conj s) = 2 ^ k
        rw [orderOf_injective _ hZ, hk]
      rw [Subgroup.orderOf_coe, hm, MulEquiv.orderOf_eq, hordb]
    have hcomm := central_commutes_pgroup hzc m.2 hord
    have hcomm' : (⟨z, hz1⟩ : ↥M1) * m = m * ⟨z, hz1⟩ := Subtype.ext hcomm
    have h3 := congrArg E.phi1 hcomm'
    rw [map_mul, map_mul, hm, MulEquiv.apply_symm_apply, ← hα] at h3
    have h4 := congrArg Subtype.val h3
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hn', hb] at h4
    apply hZ
    simpa [map_mul] using h4

theorem map_conj_eq_inf (P : Subgroup D)
    (hSelf : ∀ g : D, (∀ x, x ∈ P ↔ g * x * g⁻¹ ∈ P) → g ∈ P) :
    P.map (MulAut.conj : D →* MulAut D) = (MulAut.conj : D →* MulAut D).range ⊓ autStab P := by
  ext φ
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p, rfl⟩, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · exact P.mul_mem (P.mul_mem hp hx) (P.inv_mem hp)
    · have := P.mul_mem (P.mul_mem (P.inv_mem hp) hx) hp
      simpa [mul_assoc] using this
  · rintro ⟨⟨g, rfl⟩, hst⟩
    exact ⟨g, hSelf g fun x => hst x, rfl⟩

theorem exists_innIso (E : LieExt D M1 M2) (hM : E.Mbar = (MulAut.conj : D →* MulAut D).range)
    (hZ : Function.Injective (MulAut.conj : D →* MulAut D))
    (hSelf1 : ∀ g : D, (∀ x, x ∈ E.P1 ↔ g * x * g⁻¹ ∈ E.P1) → g ∈ E.P1)
    (hSelf2 : ∀ g : D, (∀ x, x ∈ E.P2 ↔ g * x * g⁻¹ ∈ E.P2) → g ∈ E.P2) :
    ∃ e : (RankTwoAmalgam.ofSubgroups E.P1 E.P2).Iso (RankTwoAmalgam.ofSubgroups M1 M2),
      ∀ (m : ↥M1) (n : D) (hn : n ∈ E.P1), ((E.phi1 m : ↥E.N1) : MulAut D) = MulAut.conj n →
        ((d4IsoV1 e ⟨n, hn⟩ : ↥M1) : G) = m := by
  have h1 : E.P1.map (MulAut.conj : D →* MulAut D) = E.Mbar ⊓ autStab E.P1 := by
    rw [hM]
    exact map_conj_eq_inf E.P1 hSelf1
  have h2 : E.P2.map (MulAut.conj : D →* MulAut D) = E.Mbar ⊓ autStab E.P2 := by
    rw [hM]
    exact map_conj_eq_inf E.P2 hSelf2
  refine ⟨isoTrans (ofSubgroupsMapInj (MulAut.conj : D →* MulAut D) hZ E.P1 E.P2)
    (isoTrans (ofSubgroupsCongr h1 h2) (isoSymm E.iso)), ?_⟩
  intro m n hn hmn
  have hmem : MulAut.conj n ∈ E.Mbar ⊓ autStab E.P1 := by
    rw [← h1]
    exact ⟨n, hn, rfl⟩
  have e1 : E.phi1 m = ⟨MulAut.conj n, hmem⟩ := Subtype.ext hmn
  have e2 : E.phi1.symm ⟨MulAut.conj n, hmem⟩ = m := by
    rw [MulEquiv.symm_apply_eq]
    exact e1.symm
  show ((E.phi1.symm ⟨MulAut.conj n, hmem⟩ : ↥M1) : G) = m
  rw [e2]

end LieExt

end Inn

end CFSG.Quasithin.H13.F431

module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs518F
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParModel
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParAut
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_mulEquiv_sylow_eq {X : Type} [Group X] [Finite X] (hX : LieModel X .PSL 3 2 2)
    {S₀ : Subgroup X} (hS : IsSylowTwoOf S₀ ⊤) :
    ∃ (k : Type) (_ : Field k), Nat.card k = 4 ∧ ∃ e : X ≃* projectiveSL 3 k,
      S₀.map e.toMonoidHom = projUnitriangular 3 k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hX
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  have hS2 : IsPGroup 2 (S₀.map e.toMonoidHom) := hS.2.1.map _
  have hSi : ¬ 2 ∣ (S₀.map e.toMonoidHom).index := by
    rw [Subgroup.index_map_of_bijective e.bijective]
    have := hS.2.2
    change ¬ 2 ∣ S₀.relIndex ⊤ at this
    rwa [Subgroup.relIndex_top_right] at this
  let PS : Sylow 2 (projectiveSL 3 k) := hS2.toSylow hSi
  obtain ⟨PU, hPU⟩ := exists_sylow_projUnitriangular (K := k) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL 3 k) PS PU
  refine ⟨k, inferInstance, hk, e.trans (MulAut.conj g), ?_⟩
  rw [← hPU, ← hg, Sylow.coe_subgroup_smul]
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨e y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem map_map_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (α : MulAut X)
    (H : Subgroup X) :
    (H.map α.toMonoidHom).map e.toMonoidHom =
      (H.map e.toMonoidHom).map (MulAut.congr e α).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.congr_apply]

theorem l34ParabolicFact : L34ParabolicFact := by
  intro X _ _ hX S₀ hS
  obtain ⟨k, _, hk, e, he⟩ := exists_mulEquiv_sylow_eq hX hS
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₀ : S₀ = (projUnitriangular 3 k).map e.symm.toMonoidHom := by
    rw [← he, Subgroup.map_map]
    simp
  refine ⟨(projStabilizer (flagSpace 3 k 1)).map e.symm.toMonoidHom,
    (KGL34P.radP (k := k)).map e.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hS₀, ← Subgroup.map_equiv_normalizer_eq, normalizer_projUnitriangular 2]
    exact Subgroup.map_mono (projUpperTriangular_le_projStabilizer 1)
  ·
    rw [hS₀]
    exact Subgroup.map_mono KGL34P.radP_le_projUnitriangular
  ·
    rw [← Subgroup.map_equiv_normalizer_eq, KGL34P.normalizer_radP hk]
  ·
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨a, ha, hax⟩ := x.2
      obtain ⟨b, hb, hby⟩ := y.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hax, ← hby, ← map_mul, ← map_mul, KGL34P.radP_comm ha hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, KGL34P.radP_sq hk ha, map_one]
  · rw [Subgroup.card_map_of_injective e.symm.injective, KGL34P.card_radP hk]
  ·
    let ι : ↥(projStabilizer (flagSpace 3 k 1)) ≃*
        ↥((projStabilizer (flagSpace 3 k 1)).map e.symm.toMonoidHom) :=
      e.symm.subgroupMap _
    refine ⟨(KGL34P.piL2 hk).comp ι.symm.toMonoidHom,
      (KGL34P.piL2_surjective hk).comp ι.symm.surjective, ?_⟩
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, KGL34P.ker_piL2,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    obtain ⟨y, rfl⟩ := ι.surjective x
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have : z = (y : projectiveSL 3 k) := e.symm.injective hzy
      rwa [← this]
  ·
    intro α hα hαS
    set α' := MulAut.congr e α with hα'
    have hord : orderOf α' = orderOf α :=
      orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α
    have hU : (projUnitriangular 3 k).map α'.toMonoidHom = projUnitriangular 3 k := by
      rw [← he, ← map_map_congr, hαS]
    have hR := KGL34P.map_radP_of_odd hk (hord ▸ hα) hU
    have h2 := map_map_congr e.symm α' (KGL34P.radP (k := k))
    rw [hR] at h2
    have h3 : MulAut.congr e.symm α' = α := by
      ext x
      simp [hα', MulAut.congr_apply]
    rw [h3] at h2
    exact h2.symm

theorem l34TwoAutFact : L34TwoAutFact := by
  intro X _ _ hX S₀ hS α δ hα hαS hδ3 hδ hαδ b hb hbS hαb
  obtain ⟨k, _, hk, e, he⟩ := exists_mulEquiv_sylow_eq hX hS
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c := MulAut.congr e with hc
  have hmemU : ∀ x : X, e x ∈ projUnitriangular 3 k ↔ x ∈ S₀ := by
    intro x
    rw [← he, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hcapp : ∀ (β : MulAut X) (x : X), c β (e x) = e (β x) := by
    intro β x
    simp [hc, MulAut.congr_apply]
  obtain ⟨m, hm⟩ := hα
  obtain ⟨m', hm'⟩ := hαδ
  have hbB : e b ∈ projUpperTriangular 3 k := by
    rw [← normalizer_projUnitriangular (n := 3) (K := k) 2, ← he,
      ← Subgroup.map_equiv_normalizer_eq]
    exact ⟨b, hb, rfl⟩
  obtain ⟨x', hx'U, hx'⟩ := KGL34P.eq_conj_of_twoAut hk (α := c α) (δ := c δ)
    ⟨m, by rw [← map_pow, hm, map_one]⟩ (by rw [← he, ← map_map_congr, hαS])
    (by rw [← map_pow, hδ3, map_one])
    (by
      rintro ⟨y, hy⟩
      apply hδ
      refine ⟨e.symm y, c.injective ?_⟩
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply, hy])
    ⟨m', by rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, hm', map_one]⟩
    hbB (fun h => hbS ((hmemU b).mp h))
    (by rw [hcapp, ← map_inv, ← map_mul, hmemU]; exact hαb)
  refine ⟨e.symm x', (hmemU _).mp (by rwa [e.apply_symm_apply]), c.injective ?_⟩
  rw [hx', CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply]

end CFSG.Quasithin.H13

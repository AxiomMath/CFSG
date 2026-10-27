module

public import CFSG.Quasithin.EmptyFaithful.S152O4Model
public import CFSG.Quasithin.EmptyFaithful.S152L25

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem coe_mem_commutator_of_commV {V A : Subgroup G} (hV : IsElemAbelian 2 V)
    {B : Subgroup (MulAut V)} (hB : B ≤ autOn A V) {u : V}
    (hu : u ∈ @commV ↥V (commGroupOfElemAbelian hV) B) : (u : G) ∈ ⁅V, A⁆ := by
  have hle : @commV ↥V (commGroupOfElemAbelian hV) B ≤ (⁅V, A⁆).comap V.subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨g, hgN, hgA, rfl⟩ := mem_autOn_iff_exists.mp (hB hx)
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have h1 : V.subtype (conjAct V ⟨g, hgN⟩ v * v⁻¹) = ⁅g, (v : G)⁆ := by
      simp [conjAct_apply_coe', commutatorElement_def]
    rw [h1, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hgA v.2
  exact hle hu

variable [Finite G]

theorem claim15225F : Claim15225F := by
  intro G _ _ T Mc M hs H hH hii B₀ hB₀
  obtain ⟨hV, hΩ⟩ := hii.1.2.2
  have hTM : T ≤ M := hs.mf.1.1.2
  have hMV := le_normalizer_V154 T Mc M
  have hB₀M : B₀ ≤ autOn M (V154 T Mc M) := hB₀.1.trans (A4.autOn_mono hTM)
  let _inst : CommGroup ↥(V154 T Mc M) := commGroupOfElemAbelian hV
  have hexp : ∀ w : ↥(V154 T Mc M), w * w = 1 := fun w =>
    Subtype.ext (by simpa [sq] using F7.isElemAbelian_pow_eq_one hV w.2)
  obtain ⟨u, hu, hu1, c, hc, hc1, hc3, hcu⟩ :=
    S152O.exists_fixed_vector_of_isOmegaFourPlus hexp hΩ hB₀M hB₀.2.1 hB₀.2.2
  refine ⟨(u : G), ?_, fun h => hu1 (Subtype.ext h), ?_⟩
  · exact coe_mem_commutator_of_commV hV (autOn_preOn_B0 hB₀).ge hu
  · intro hle
    obtain ⟨x, hxN, hxM, rfl⟩ := mem_autOn_iff_exists.mp hc
    have hxz : x * (u : G) * x⁻¹ = (u : G) := by
      have := congrArg (fun a : ↥(V154 T Mc M) => (a : G)) hcu
      simpa [conjAct_apply_coe'] using this
    have hxC : x ∈ Subgroup.centralizer ({(u : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      calc (u : G) * x = (x * (u : G) * x⁻¹) * x := by rw [hxz]
        _ = x * (u : G) := by group
    have hcS : conjAct (V154 T Mc M) ⟨x, hxN⟩ ∈
        autOn (M ⊓ Subgroup.centralizer ({(u : G)} : Set G)) (V154 T Mc M) :=
      mem_autOn_iff_exists.mpr ⟨x, hxN, ⟨hxM, hxC⟩, rfl⟩
    have hcT := hle hcS
    have hT2 : IsPGroup 2 (autOn T (V154 T Mc M)) := by
      have h1 : IsPGroup 2 (T.subgroupOf (Subgroup.normalizer (V154 T Mc M : Set G))) :=
        hs.qtfe.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe (hTM.trans hMV)).symm
      exact h1.map (conjAct (V154 T Mc M))
    obtain ⟨k, hk⟩ := hT2 ⟨_, hcT⟩
    have hk' : (conjAct (V154 T Mc M) ⟨x, hxN⟩) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hk3 : orderOf (conjAct (V154 T Mc M) ⟨x, hxN⟩) ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    have hk2 : orderOf (conjAct (V154 T Mc M) ⟨x, hxN⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h1 : orderOf (conjAct (V154 T Mc M) ⟨x, hxN⟩) = 1 := by
      have hcop : Nat.Coprime (orderOf (conjAct (V154 T Mc M) ⟨x, hxN⟩)) 2 := by
        have := Nat.Coprime.coprime_dvd_left hk3 (by norm_num : Nat.Coprime 3 2)
        exact this
      exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) hk2
    exact hc1 (orderOf_eq_one_iff.mp h1)

end CFSG.Quasithin

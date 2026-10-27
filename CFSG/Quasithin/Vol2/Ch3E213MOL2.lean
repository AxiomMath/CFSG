module

public import CFSG.Quasithin.Vol2.Ch3E213MOL1
public import CFSG.Quasithin.Vol2.Ch3E213MOS10
public import CFSG.Quasithin.Vol2.Ch3E213MOLFacts

public section

namespace CFSG.Quasithin.Ch3E213M.OL

open CFSG.Open CFSG.GH74.GLS.IVK CFSG.GH74.GLS B6

theorem center_eq_bot_of_simple {K : Type} [Group K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) : Subgroup.center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ Subgroup.center K := by rw [h]; trivial
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem conj_injective_of_center {K : Type} [Group K] (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [← hZ, Subgroup.mem_center_iff]
  intro y
  have h := congrArg (fun φ : MulAut K => φ y) (MonoidHom.mem_ker.mp hx)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc y * x = x * y * x⁻¹ * x := by rw [h]
    _ = x * y := by group

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem map_zOf_subgroupOf {K S : Subgroup X} (hSK : S ≤ K) :
    (E2P.zOf (S.subgroupOf K)).map K.subtype = E2P.zOf S := by
  rw [OS.map_zOf K.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hSK]

theorem false_of_asHyp (hA : KFactL3U3OuterInv)
    {K T M V : Subgroup X} (hX : E2P.ASHyp K T M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : (p % 4 = 1 ∧ IsPSU 3 p 1 ↥K) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 ↥K))
    (hMK : M ⊓ K = K ⊓ Subgroup.centralizer (E2P.zOf (T ⊓ K) : Set X))
    (hsq : ∀ v ∈ V, v * v = 1) (hV4 : 4 ≤ Nat.card V) (hVM : V ≤ pCoreOf 2 M) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hX.normal
  have := hX.simple
  have hinjK := conj_injective_of_center (center_eq_bot_of_simple hX.nonab)
  obtain ⟨z, hz, hzS, hQ, hinv⟩ := hA ↥K p hp hp5 hK (toSylow2 hX.isSylow_inf)
  rw [toSylow2_coe] at hzS
  have hzX : E2P.zOf (T ⊓ K) = Subgroup.zpowers (z : X) := by
    rw [← map_zOf_subgroupOf inf_le_right, hzS, MonoidHom.map_zpowers]
    rfl
  have hιinj := OS.conjNormal_injective hX.cent
  have hKinn : K.map (MulAut.conjNormal : X →* MulAut ↥K) = innAut ↥K := OS.map_conjNormal_eq
  have hD : (M.map (MulAut.conjNormal : X →* MulAut ↥K)) ⊓ innAut ↥K =
      (Subgroup.centralizer ({z} : Set ↥K)).map MulAut.conj := by
    rw [← hKinn, ← Subgroup.map_inf_eq _ _ _ hιinj, hMK, hzX]
    ext y
    constructor
    · rintro ⟨x, ⟨hxK, hxC⟩, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hxC (z : X) (Subgroup.mem_zpowers _)
      refine ⟨⟨x, hxK⟩, ?_, (MulAut.conjNormal_val (h := (⟨x, hxK⟩ : ↥K))).symm⟩
      show (⟨x, hxK⟩ : ↥K) ∈ Subgroup.centralizer ({z} : Set ↥K)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext h1.symm
    · rintro ⟨k, hk, rfl⟩
      have hk' : k ∈ Subgroup.centralizer ({z} : Set ↥K) := hk
      refine ⟨k, ⟨k.2, ?_⟩, MulAut.conjNormal_val⟩
      show (k : X) ∈ Subgroup.centralizer (Subgroup.zpowers (z : X) : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hc : Commute (z : X) (k : X) :=
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hk')).symm
      exact (hc.zpow_left j).eq
  have hVM' : V.map (MulAut.conjNormal : X →* MulAut ↥K) ≤
      pCoreOf 2 (M.map (MulAut.conjNormal : X →* MulAut ↥K)) :=
    (Subgroup.map_mono hVM).trans (CFSG.LieType.BorelTits.map_pCoreOf_le _ _)
  have hsq' : ∀ v ∈ V.map (MulAut.conjNormal : X →* MulAut ↥K), v * v = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul, hsq v hv, map_one]
  have hV4' : 4 ≤ Nat.card (V.map (MulAut.conjNormal : X →* MulAut ↥K)) := by
    rw [Subgroup.card_map_of_injective hιinj]
    exact hV4
  obtain ⟨v, -, hv2, hvI, hvC⟩ := exists_outer_inv hinjK hz hD hQ hVM' hsq' hV4'
  exact hvI (hinv v hv2 hvC)

end CFSG.Quasithin.Ch3E213M.OL

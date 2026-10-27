module

public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Transv

public section

namespace CFSG.Quasithin

namespace FA5

section World

variable {G : Type*} [Group G]

theorem normalizerMonoidHom_eq_one_iff (V : Subgroup G) (n : Subgroup.normalizer (V : Set G)) :
    V.normalizerMonoidHom n = 1 ↔ (n : G) ∈ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h a ha
    have := congrArg (fun f : MulAut V => (f ⟨a, ha⟩ : G)) h
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at this
    calc a * (n : G) = ((n : G) * a * (n : G)⁻¹) * (n : G) := by rw [this]
      _ = (n : G) * a := by group
  · intro h
    ext a
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply]
    have := Subgroup.mem_centralizer_iff.mp h a a.2
    calc (n : G) * (a : G) * (n : G)⁻¹ = (a : G) * (n : G) * (n : G)⁻¹ := by rw [this]
      _ = a := by group

theorem fixSub_normalizerMonoidHom (V : Subgroup G) (n : Subgroup.normalizer (V : Set G)) :
    fixSub (V.normalizerMonoidHom n) = (V ⊓ Subgroup.centralizer {(n : G)}).subgroupOf V := by
  ext v
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_fixSub]
  constructor
  · intro h
    refine ⟨v.2, ?_⟩
    have h' := congrArg (fun y : V => (y : G)) h
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe] at h'
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    calc (n : G) * (v : G) = ((n : G) * (v : G) * (n : G)⁻¹) * (n : G) := by group
      _ = (v : G) * (n : G) := by rw [h']
  · rintro ⟨-, h⟩
    ext
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have := Subgroup.mem_centralizer_iff.mp h n (Set.mem_singleton _)
    calc (n : G) * (v : G) * (n : G)⁻¹ = (v : G) * (n : G) * (n : G)⁻¹ := by rw [this]
      _ = v := by group

variable [Finite G]

theorem centralizes_of_inverted_transvection {V : Subgroup G}
    (hV2 : ∀ a ∈ V, a * a = 1) {x z q : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (hz : z ∈ Subgroup.normalizer (V : Set G))
    (hq : q ∈ Subgroup.centralizer (V : Set G)) (hx5 : x ^ 5 = 1)
    (hz2 : z * z ∈ Subgroup.centralizer (V : Set G)) (hinv : z * x * z⁻¹ = x⁻¹ * q)
    (hidx : (V ⊓ Subgroup.centralizer {z}).relIndex V ≤ 2) :
    x ∈ Subgroup.centralizer (V : Set G) := by
  let ρ := V.normalizerMonoidHom
  let nx : Subgroup.normalizer (V : Set G) := ⟨x, hx⟩
  let nz : Subgroup.normalizer (V : Set G) := ⟨z, hz⟩
  let nq : Subgroup.normalizer (V : Set G) :=
    ⟨q, Subgroup.centralizer_le_normalizer (V : Set G) hq⟩
  have hV2' : ∀ a : V, a * a = 1 := fun a => Subtype.ext (hV2 a a.2)
  have hρq : ρ nq = 1 := (normalizerMonoidHom_eq_one_iff V nq).mpr hq
  have hξ5 : ρ nx ^ 5 = 1 := by
    rw [← map_pow]
    have : nx ^ 5 = 1 := Subtype.ext (by simpa using hx5)
    rw [this, map_one]
  have hζ2 : ρ nz ^ 2 = 1 := by
    rw [← map_pow]
    apply (normalizerMonoidHom_eq_one_iff V _).mpr
    simpa [pow_two] using hz2
  have hinv' : ρ nz * ρ nx * (ρ nz)⁻¹ = (ρ nx)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    have : nz * nx * nz⁻¹ = nx⁻¹ * nq := Subtype.ext (by simpa using hinv)
    rw [this, map_mul, hρq, mul_one]
    exact map_inv ρ nx
  have hidx' : (fixSub (ρ nz)).index ≤ 2 := by
    have := fixSub_normalizerMonoidHom V nz
    rw [this]
    exact hidx
  have := eq_one_of_inverted_transvection hV2' hξ5 hζ2 hinv' hidx'
  exact (normalizerMonoidHom_eq_one_iff V nx).mp this

theorem centralizes_of_alt5_transvection {V L : Subgroup G}
    (hV2 : ∀ a ∈ V, a * a = 1)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (φ : L →* alternatingGroup (Fin 5))
    (hφ : Function.Surjective φ)
    (hker : ∀ l : L, φ l = 1 → (l : G) ∈ Subgroup.centralizer (V : Set G))
    {l : L} (hl1 : φ l ≠ 1) (hl2 : φ l ^ 2 = 1)
    (hidx : (V ⊓ Subgroup.centralizer {(l : G)}).relIndex V ≤ 2) :
    L ≤ Subgroup.centralizer (V : Set G) := by
  let ρ : L →* MulAut V := V.normalizerMonoidHom.comp (Subgroup.inclusion hLV)
  have hV2' : ∀ a : V, a * a = 1 := fun a => Subtype.ext (hV2 a a.2)
  have hρ1 : ∀ n : L, ρ n = 1 ↔ (n : G) ∈ Subgroup.centralizer (V : Set G) := fun n =>
    normalizerMonoidHom_eq_one_iff V (Subgroup.inclusion hLV n)
  have hle : φ.ker ≤ ρ.ker := fun n hn => (hρ1 n).mpr (hker n (MonoidHom.mem_ker.mp hn))
  let ρ' : alternatingGroup (Fin 5) →* MulAut V := MonoidHom.liftOfSurjective φ hφ ⟨ρ, hle⟩
  have hρ' : ∀ n : L, ρ' (φ n) = ρ n := fun n =>
    MonoidHom.liftOfRightInverse_comp_apply φ (Function.surjInv hφ)
      (Function.rightInverse_surjInv hφ) ⟨ρ, hle⟩ n
  have hidx' : (fixSub (ρ' (φ l))).index ≤ 2 := by
    rw [hρ' l]
    have := fixSub_normalizerMonoidHom V (Subgroup.inclusion hLV l)
    change (fixSub (V.normalizerMonoidHom (Subgroup.inclusion hLV l))).index ≤ 2
    rw [this]
    exact hidx
  intro n hn
  have h1 : ρ' (φ ⟨n, hn⟩) = 1 :=
    alt5_trivial_of_transvection hV2' hl1 hl2 hidx' (φ ⟨n, hn⟩)
  rw [hρ'] at h1
  exact (hρ1 ⟨n, hn⟩).mp h1

end World

end FA5

end CFSG.Quasithin

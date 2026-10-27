module

public import CFSG.LocalAnalysis.StandardType.GGHalfJoinInner
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem mem_closure_pair_zpow_mul {G : Type*} [Group G] {u v : G} (hcomm : Commute u v)
    {g : G} (hg : g ∈ Subgroup.closure ({u, v} : Set G)) :
    ∃ a c : ℤ, g = u ^ a * v ^ c := by
  refine Subgroup.closure_induction'' (p := fun g _ => ∃ a c : ℤ, g = u ^ a * v ^ c)
    ?_ ?_ ?_ ?_ hg
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨-1, 0, by simp⟩
    · exact ⟨0, -1, by simp⟩
  · exact ⟨0, 0, by simp⟩
  · intro r s _ _ hr hs
    obtain ⟨a, c, hrc⟩ := hr
    obtain ⟨a', c', hsc⟩ := hs
    refine ⟨a + a', c + c', ?_⟩
    rw [hrc, hsc]
    have hcvs : Commute (v ^ c) (u ^ a') := (hcomm.symm).zpow_zpow c a'
    calc u ^ a * v ^ c * (u ^ a' * v ^ c')
        = u ^ a * (v ^ c * u ^ a') * v ^ c' := by group
      _ = u ^ a * (u ^ a' * v ^ c) * v ^ c' := by rw [hcvs.eq]
      _ = (u ^ a * u ^ a') * (v ^ c * v ^ c') := by group
      _ = u ^ (a + a') * v ^ (c + c') := by rw [← zpow_add, ← zpow_add]

theorem GGHalfJoin.normalizes_kx {G : Type} [Group G] {Bs K' J TJ D : Subgroup G} {x y' kx : G}
    {τ : ↥Bs →* ↥K'} (hD : D = Subgroup.closure {x, y'}) (hcomm : x * y' = y' * x)
    (hxBs : x ∈ Bs) (hy'Bs : y' ∈ Bs) (hK'y' : K' ≤ Subgroup.centralizer ({y'} : Set G))
    (hP : GGHalfInnerPart Bs K' J TJ x y' τ kx)
    (hstab : ∀ φ ∈ ggInduced ⊤ Bs, ((φ ⟨y', hy'Bs⟩ : ↥Bs) : G) = y' →
      ∀ b : ↥Bs, (b : G) ∈ D → ((φ b : ↥Bs) : G) ∈ D)
    {m' : G} (hm' : m' ∈ K')
    (hnorm : m' ∈ Subgroup.normalizer ((Subgroup.zpowers kx ⊔ TJ : Subgroup G) : Set G)) :
    m' * kx * m'⁻¹ ∈ Subgroup.zpowers kx := by
  have hN : m' ∈ Subgroup.normalizer (Bs : Set G) := hP.norm m' hm' hnorm
  let φ : MulAut ↥Bs := ggConjAut Bs hN
  have hφ : φ ∈ ggInduced ⊤ Bs := ggConjAut_mem_ggInduced (Subgroup.mem_top m') hN
  have hcy : m' * y' = y' * m' := Subgroup.mem_centralizer_singleton_iff.mp (hK'y' hm')
  have hfix : ((φ ⟨y', hy'Bs⟩ : ↥Bs) : G) = y' := by
    show ((ggConjAut Bs hN ⟨y', hy'Bs⟩ : ↥Bs) : G) = y'
    rw [ggConjAut_apply]
    show m' * y' * m'⁻¹ = y'
    rw [hcy, mul_assoc, mul_inv_cancel, mul_one]
  have hxD : x ∈ D := by
    rw [hD]
    exact Subgroup.subset_closure (by simp)
  have hmxD : ((φ ⟨x, hxBs⟩ : ↥Bs) : G) ∈ D := hstab φ hφ hfix ⟨x, hxBs⟩ hxD
  rw [hD] at hmxD
  obtain ⟨a, c, ha⟩ := mem_closure_pair_zpow_mul (u := x) (v := y') hcomm hmxD
  have ha' : m' * x * m'⁻¹ = x ^ a * y' ^ c := by
    have h := ha
    rw [ggConjAut_apply] at h
    simpa using h
  let b : ↥Bs := ⟨x, hxBs⟩
  let b'' : ↥Bs := ⟨y', hy'Bs⟩
  let b' : ↥Bs := φ b
  have hτb : (τ b : G) = kx := by
    show (τ ⟨x, hxBs⟩ : G) = kx
    exact hP.kx_def hxBs
  have hb' : b' = b ^ a * b'' ^ c := by
    apply Subtype.ext
    show ((ggConjAut Bs hN b : ↥Bs) : G) = ((b ^ a * b'' ^ c : ↥Bs) : G)
    rw [ggConjAut_apply, Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow]
    exact ha'
  have heq : (τ b' : G) = m' * (τ b : G) * m'⁻¹ :=
    hP.equivariant m' hm' hN b b' (by
      show ((ggConjAut Bs hN b : ↥Bs) : G) = m' * (b : G) * m'⁻¹
      rw [ggConjAut_apply])
  have hτb'' : τ b'' = 1 := hP.y'_triv hy'Bs
  have his : (τ b' : G) = kx ^ a := by
    have h1 : τ b' = (τ b) ^ a * (τ b'') ^ c := by
      rw [hb', map_mul, map_zpow, map_zpow]
    rw [h1, hτb'', one_zpow, mul_one, Subgroup.coe_zpow, hτb]
  have heq' : (τ b' : G) = m' * kx * m'⁻¹ := by rw [heq, hτb]
  have hfinal : m' * kx * m'⁻¹ = kx ^ a := heq'.symm.trans his
  rw [hfinal]
  exact Subgroup.mem_zpowers_iff.mpr ⟨a, rfl⟩

end CFSG.StandardType

end

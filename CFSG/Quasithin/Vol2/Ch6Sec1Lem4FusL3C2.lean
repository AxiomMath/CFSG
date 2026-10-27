module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3A
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3C1
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3CB
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3B2b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section L3C2

private theorem leviOfL3_le_L3C2 {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal) (u : G) :
    leviOfL3 N u ≤ N := by
  unfold leviOfL3
  exact (Subgroup.commutator_mono inf_le_left inf_le_left).trans (Subgroup.commutator_le_left N N)

private theorem mem_normalizer_levi_of_fix_L3C2 {G : Type*} [Group G] {N : Subgroup G}
    (hN : N.Normal) {z g : G} (hg : g * z * g⁻¹ = z) :
    g ∈ Subgroup.normalizer ((leviOfL3 N z : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h1 := leviOfL3_conj hN g z
  rw [hg] at h1
  exact h1.symm

private theorem mem_normalizer_of_centralizes_L3C2 {G : Type*} [Group G] {S : Subgroup G} {y : G}
    (hC : S ≤ Subgroup.centralizer ({y} : Set G)) :
    y ∈ Subgroup.normalizer (S : Set G) := by
  have hCy : ∀ k ∈ S, y * k * y⁻¹ = k := by
    intro k hk
    have hck : k * y = y * k := Subgroup.mem_centralizer_singleton_iff.mp (hC hk)
    rw [← hck, mul_inv_cancel_right]
  have hCy' : ∀ k ∈ S, y⁻¹ * k * y = k := by
    intro k hk
    calc y⁻¹ * k * y = y⁻¹ * (y * k * y⁻¹) * y := by rw [hCy k hk]
      _ = k := by group
  rw [Subgroup.mem_normalizer_iff]
  intro s
  show s ∈ S ↔ y * s * y⁻¹ ∈ S
  constructor
  · intro hs
    rw [hCy s hs]
    exact hs
  · intro hs
    have h2 : y * s * y⁻¹ = s := by
      rw [← hCy' _ hs]
      group
    rw [h2] at hs
    exact hs

theorem locFusL3_of_facts {G : Type} [Group G] [Finite G] {N : Subgroup G} (hN : N.Normal)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : L3FusFacts N p) : LocFusL3 G N := by
  intro T X E hTs hXN hXO hX5 hXn hTX hXnT hE hEa hE1
  obtain ⟨y, hy5, rfl⟩ := exists_eq_zpowers_of_L3FusFacts hp hp5 h hTs.2.1 hXN hXO hX5 hXn
  have hyN : y ∈ N := hXN (Subgroup.mem_zpowers y)
  have hS : IsSylowTwoOf (T ⊓ N) N := isSylowTwoOf_inf_normal614 hN hTs
  have hSy : T ⊓ N ≤ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) :=
    inf_le_left.trans hTX
  have hSc : ¬ T ⊓ N ≤ Subgroup.centralizer ({y} : Set G) := by
    intro hC
    exact hXnT (Subgroup.zpowers_le.mpr (mem_normalizer_of_centralizes_L3C2 hC))
  have hp6 : 5 < p := by
    rcases hp5.lt_or_eq with h5 | h5
    · exact h5
    · subst h5
      exact (false_of_L3FusFacts_five h hyN hy5 hS hSy hSc).elim
  obtain ⟨z, hzS, hz2, hzy, -, hyK⟩ :=
    exists_involution_of_sylow_normalizes hp hp5 h hyN hy5 hS hSy hSc
  have hzN : z ∈ N := (Subgroup.mem_inf.mp hzS).2
  have hK₂ : IsL3Levi (leviOfL3 N z) z p := (h.levi z hzN hz2).1
  have hK₂N : leviOfL3 N z ≤ N := leviOfL3_le_L3C2 hN z
  have hXK₂ : Subgroup.zpowers y ≤ leviOfL3 N z := Subgroup.zpowers_le.mpr hyK
  have hfix : ∀ g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G),
      g * z * g⁻¹ = z :=
    fun g hg => conj_eq_of_normalizes_zpowers614 hN hp6 h hyN hy5 hzN hz2 hyK hzy hg
  have hTK₂ : T ≤ Subgroup.normalizer ((leviOfL3 N z : Subgroup G) : Set G) := by
    intro t ht
    exact mem_normalizer_levi_of_fix_L3C2 hN (hfix t (hTX ht))
  have hTs₂ : IsSylowTwoOf T (leviOfL3 N z ⊔ T) := by
    refine ⟨le_sup_right, hTs.2.1, fun h2 => hTs.2.2 ?_⟩
    have hm := Subgroup.relIndex_mul_relIndex T (leviOfL3 N z ⊔ T) (N ⊔ T) le_sup_right
      (sup_le_sup_right hK₂N T)
    show 2 ∣ T.relIndex (N ⊔ T)
    rw [← hm]
    exact dvd_mul_of_dvd_left h2 _
  have hETs : IsSylowTwoOf T (Subgroup.zpowers y ⊔ T) := by
    refine ⟨le_sup_right, hTs.2.1, fun h2 => hTs.2.2 ?_⟩
    have hm := Subgroup.relIndex_mul_relIndex T (Subgroup.zpowers y ⊔ T) (N ⊔ T) le_sup_right
      (sup_le_sup_right hXN T)
    show 2 ∣ T.relIndex (N ⊔ T)
    rw [← hm]
    exact dvd_mul_of_dvd_left h2 _
  have hET : E ≤ T := hE.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hETs)
  have hOy : pCoreOf 2 (Subgroup.zpowers y ⊔ T) ≤ Subgroup.centralizer ({y} : Set G) :=
    pCoreOf_le_centralizer614 hy5 hTX
  by_cases hEK : E ≤ pCoreOf 2 (leviOfL3 N z ⊔ T)
  ·
    have hEC : E ≤ Subgroup.centralizer (leviOfL3 N z : Set G) :=
      le_centralizer_of_le_pCoreOf_levi614 hp hp5 hK₂ hTK₂ hEK
    obtain ⟨n, hnN, hnT, hnC⟩ :=
      caseB_L3 hN hp6 h hTs hyN hy5 hzN hz2 hyK hTX hET hEa hE1 hEC
    exact ⟨n, hnN, hnT, fun h' => hnC (h'.trans hOy)⟩
  ·
    obtain ⟨F, hF, hFin, hFp, ⟨ϕ⟩⟩ := hK₂.exists_equiv_psl2 hp hp5
    obtain ⟨k, hkK, hkT, hkX⟩ :=
      kg614FusionL2_of_psl2_prime (leviOfL3 N z) T (Subgroup.zpowers y) hp hp5 hFp ϕ hTK₂ hTs₂
        hXK₂ hXO hX5 hXn hTX hE hEa hEK
    exact ⟨k, hK₂N hkK, hkT, hkX⟩

end L3C2

end CFSG.Quasithin.H13

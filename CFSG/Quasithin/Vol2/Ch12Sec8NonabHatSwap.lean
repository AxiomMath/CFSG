module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabTen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

section Conj

variable {G : Type} [Group G]

theorem rconj_one_eq (X : Subgroup G) : rconj X 1 = X := by
  ext y
  rw [mem_rconj]
  simp

theorem rconj_rconj_eq (X : Subgroup G) (a b : G) : rconj (rconj X a) b = rconj X (a * b) := by
  ext y
  simp only [mem_rconj]
  have e : a * (b * y * b⁻¹) * a⁻¹ = (a * b) * y * (a * b)⁻¹ := by group
  rw [e]

theorem rconj_centralizer_eq (Z : Subgroup G) (s : G) :
    rconj (Subgroup.centralizer (Z : Set G)) s = Subgroup.centralizer (rconj Z s : Set G) := by
  ext y
  rw [mem_rconj, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hy c hc
    have h1 := hy _ (mem_rconj.mp hc)
    calc c * y = s⁻¹ * ((s * c * s⁻¹) * (s * y * s⁻¹)) * s := by group
      _ = s⁻¹ * ((s * y * s⁻¹) * (s * c * s⁻¹)) * s := by rw [h1]
      _ = y * c := by group
  · intro hy c hc
    have hc' : s⁻¹ * c * s ∈ rconj Z s := by
      rw [mem_rconj]
      have e : s * (s⁻¹ * c * s) * s⁻¹ = c := by group
      rw [e]
      exact hc
    have h1 := hy _ hc'
    calc c * (s * y * s⁻¹) = s * ((s⁻¹ * c * s) * y) * s⁻¹ := by group
      _ = s * (y * (s⁻¹ * c * s)) * s⁻¹ := by rw [h1]
      _ = (s * y * s⁻¹) * c := by group

theorem conjClosure_rconj_le (A K : Subgroup G) (s : G) :
    conjClosure (rconj A s) (rconj K s) ≤ rconj (conjClosure A K) s := by
  refine conjClosure_le fun k hk a ha => ?_
  rw [mem_rconj] at hk ha ⊢
  have e : s * (k * a * k⁻¹) * s⁻¹ = (s * k * s⁻¹) * (s * a * s⁻¹) * (s * k * s⁻¹)⁻¹ := by group
  rw [e]
  exact mem_conjClosure hk ha

theorem rconj_conjClosure_eq (A K : Subgroup G) (s : G) :
    rconj (conjClosure A K) s = conjClosure (rconj A s) (rconj K s) := by
  refine le_antisymm ?_ (conjClosure_rconj_le A K s)
  have h1 := conjClosure_rconj_le (rconj A s) (rconj K s) s⁻¹
  rw [rconj_rconj_inv_eq, rconj_rconj_inv_eq] at h1
  have h2 := rconj_le_rconj h1 s
  have h3 := rconj_rconj_inv_eq (conjClosure (rconj A s) (rconj K s)) s⁻¹
  rw [inv_inv] at h3
  rw [h3] at h2
  exact h2

theorem rconj_uOfL22_eq (T M : Subgroup G) {s : G}
    (hs : s ∈ Subgroup.normalizer (VZ T M : Set G)) :
    rconj (uOfL22 T M) s =
      conjClosure (VZ T M)
        (Subgroup.centralizer (rconj (quasithinOmegaOneCenter T) s : Set G)) := by
  unfold uOfL22
  rw [rconj_conjClosure_eq, rconj_eq_of_mem_normalizer hs, rconj_centralizer_eq]

theorem rconj_omegaOneCenter_congr {T : Subgroup G} {z : G}
    (hz1 : z ∈ quasithinOmegaOneCenter T)
    (hall : ∀ w ∈ quasithinOmegaOneCenter T, w = 1 ∨ w = z) {s₁ s₂ : G}
    (h : s₁⁻¹ * z * s₁ = s₂⁻¹ * z * s₂) :
    rconj (quasithinOmegaOneCenter T) s₁ = rconj (quasithinOmegaOneCenter T) s₂ := by
  have key : ∀ a b : G, a⁻¹ * z * a = b⁻¹ * z * b →
      ∀ y ∈ rconj (quasithinOmegaOneCenter T) a, y ∈ rconj (quasithinOmegaOneCenter T) b := by
    intro a b hab y hy
    rw [mem_rconj] at hy ⊢
    rcases hall _ hy with h1 | h1
    · have hy1 : y = 1 := by
        calc y = a⁻¹ * (a * y * a⁻¹) * a := by group
          _ = 1 := by rw [h1]; group
      rw [hy1]
      simp
    · have hy' : y = a⁻¹ * z * a := by
        calc y = a⁻¹ * (a * y * a⁻¹) * a := by group
          _ = a⁻¹ * z * a := by rw [h1]
      rw [hy', hab]
      have e : b * (b⁻¹ * z * b) * b⁻¹ = z := by group
      rw [e]
      exact hz1
  ext y
  exact ⟨key s₁ s₂ h y, key s₂ s₁ h.symm y⟩

end Conj

namespace Hyp1281Two

section ConjW

variable {G : Type} [Group G]

theorem rconj_wOfU_eq_of_mem_normalizer (T M : Subgroup G) {s : G}
    (hs : s ∈ Subgroup.normalizer (VZ T M : Set G)) :
    rconj (wOfU T M) s =
      conjClosure (VZ T M)
          (Subgroup.centralizer (rconj (quasithinOmegaOneCenter T) s : Set G)) ⊓
        Subgroup.centralizer (VZ T M : Set G) := by
  unfold wOfU
  rw [rconj_inf_eq, rconj_uOfL22_eq T M hs, rconj_centralizer_eq, rconj_eq_of_mem_normalizer hs]

end ConjW

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

theorem exists_swap (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
    (hg : GoodElt128 T L g) :
    ∃ t : G, t ∈ Subgroup.normalizer (VZ T M : Set G) ∧
      rconj (quasithinOmegaOneCenter T) t⁻¹ = rconj (quasithinOmegaOneCenter T) g ∧
      rconj (wOfU T M) t⁻¹ = rconj (wOfU T M) g ∧
      rconj (rconj (wOfU T M) g) t⁻¹ = wOfU T M := by
  classical
  obtain ⟨z, hzZ, hz1, hall⟩ := h.exists_zgen
  have hzV : z ∈ VZ T M := omegaOneCenter_le_VZ T M hzZ
  have hzz : z * z = 1 := by
    simpa [sq] using h.almostSpecialHyp_g1.sq_eq_one_of_mem_V hzV
  have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hzc : ∀ u ∈ uOfL22 T M, z * u = u * z := fun u hu =>
    (Subgroup.mem_centralizer_iff.mp (h.omegaOneCenter_le_centerOf_uOfL22 hzZ).2 u hu).symm
  have hgN : g ∈ Subgroup.normalizer (VZ T M : Set G) :=
    ((le_sup_left : L ≤ L ⊔ T).trans h.LT_le_normalizer_VZ) hg.mem
  obtain ⟨z', hz'def⟩ : ∃ z', z' = g⁻¹ * z * g := ⟨_, rfl⟩
  have hz'V : z' ∈ VZ T M := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) z).mp hzV
    rw [hz'def]
    simpa using this
  have hz'1 : z' ≠ 1 := by
    intro h1
    apply hz1
    have : z = g * z' * g⁻¹ := by rw [hz'def]; group
    rw [this, h1]
    group
  have hz'nZ : z' ∉ quasithinOmegaOneCenter T := by
    intro hz'Z
    rcases hall _ hz'Z with h1 | h1
    · exact hz'1 h1
    · apply hg.not_mem
      rw [h.normalizer_Z_eq_centralizer, Subgroup.mem_centralizer_iff]
      intro w hw
      rcases hall w hw with h2 | h2
      · rw [h2]
        simp
      · rw [h2]
        have h3 : g⁻¹ * z * g = z := by rw [← hz'def]; exact h1
        calc z * g = g * (g⁻¹ * z * g) := by group
          _ = g * z := by rw [h3]
  have hcases := h.VZ_cases hzZ hz1 hz'V hz'nZ
  have hgz' : g * z' * g⁻¹ = z := by rw [hz'def]; group
  have hg3 : g ^ 3 ∈ Subgroup.centralizer (VZ T M : Set G) :=
    h.pCoreOf_LT_le_centralizer (h.pow_three_mem_pCoreOf_LT hg.mem)
  have hyV : g⁻¹ * z' * g ∈ VZ T M := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) z').mp hz'V
    simpa using this
  have hy : g⁻¹ * z' * g = z * z' := by
    rcases hcases _ hyV with h0 | h0 | h0 | h0
    · exfalso
      apply hz'1
      have : z' = g * (g⁻¹ * z' * g) * g⁻¹ := by group
      rw [this, h0]
      group
    · exfalso
      apply hz'nZ
      have e : g⁻¹ * g⁻¹ * g⁻¹ * z * (g * g * g) = z' := by
        calc g⁻¹ * g⁻¹ * g⁻¹ * z * (g * g * g) = g⁻¹ * (g⁻¹ * (g⁻¹ * z * g) * g) * g := by group
          _ = g⁻¹ * (g⁻¹ * z' * g) * g := by rw [← hz'def]
          _ = g⁻¹ * z * g := by rw [h0]
          _ = z' := hz'def.symm
      have e2 : g⁻¹ * g⁻¹ * g⁻¹ * z * (g * g * g) = z := by
        have e3 : g * g * g = g ^ 3 := by rw [pow_three, mul_assoc]
        rw [e3]
        have hh := Subgroup.mem_centralizer_iff.mp hg3 z hzV
        calc g⁻¹ * g⁻¹ * g⁻¹ * z * g ^ 3 = g⁻¹ * g⁻¹ * g⁻¹ * (z * g ^ 3) := by group
          _ = g⁻¹ * g⁻¹ * g⁻¹ * (g ^ 3 * z) := by rw [hh]
          _ = z := by group
      rw [← e, e2]
      exact hzZ
    · exfalso
      apply hz'nZ
      have e : z' = z := by
        calc z' = g * (g⁻¹ * z' * g) * g⁻¹ := by group
          _ = g * z' * g⁻¹ := by rw [h0]
          _ = z := hgz'
      rw [e]
      exact hzZ
    · exact h0
  have hgz : g * z * g⁻¹ = z' * z := by
    have h1 : z' = (g * z * g⁻¹) * z := by
      calc z' = g * (g⁻¹ * z' * g) * g⁻¹ := by group
        _ = g * (z * z') * g⁻¹ := by rw [hy]
        _ = (g * z * g⁻¹) * (g * z' * g⁻¹) := by group
        _ = (g * z * g⁻¹) * z := by rw [hgz']
    calc g * z * g⁻¹ = ((g * z * g⁻¹) * z) * z⁻¹ := by group
      _ = z' * z⁻¹ := by rw [← h1]
      _ = z' * z := by rw [hz_inv]
  obtain ⟨u₀, hu₀U, hu₀W⟩ : ∃ u₀ ∈ uOfL22 T M, u₀ ∉ wOfU T M := by
    by_contra hall'
    push Not at hall'
    exact h.not_le_centralizer_VZ_of_nonabelian hU fun u hu => (hall' u hu).2
  have hu₀N : u₀ ∈ Subgroup.normalizer (VZ T M : Set G) := h.uOfL22_le_normalizer_VZ hu₀U
  have hu₀Z : u₀ ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    h.uOfL22_le_g1 hu₀U
  have hu₀C : u₀ ∉ Subgroup.centralizer (VZ T M : Set G) := fun hc => hu₀W ⟨hu₀U, hc⟩
  have hu₀z : u₀ * z * u₀⁻¹ = z := by
    have h1 := hzc u₀ hu₀U
    calc u₀ * z * u₀⁻¹ = (z * u₀) * u₀⁻¹ := by rw [h1]
      _ = z := by group
  have hu₀z' : u₀ * z' * u₀⁻¹ = z * z' :=
    h.conj_eq_of_not_centralizes hzZ hz1 hz'V hz'nZ hu₀N hu₀Z hu₀C
  obtain ⟨t, ht⟩ : ∃ t, t = g * u₀ * g⁻¹ := ⟨_, rfl⟩
  have htN : t ∈ Subgroup.normalizer (VZ T M : Set G) := by
    rw [ht]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hu₀N) (Subgroup.inv_mem _ hgN)
  have htz : t * z * t⁻¹ = z' := by
    have e1 : t * z * t⁻¹ = g * (u₀ * z' * u₀⁻¹) * g⁻¹ := by
      rw [ht, hz'def]
      group
    rw [e1, hu₀z']
    have e2 : g * (z * z') * g⁻¹ = (g * z * g⁻¹) * (g * z' * g⁻¹) := by group
    rw [e2, hgz, hgz', mul_assoc, hzz, mul_one]
  have htz' : t * z' * t⁻¹ = z := by
    have e1 : t * z' * t⁻¹ = g * (u₀ * (g⁻¹ * z' * g) * u₀⁻¹) * g⁻¹ := by
      rw [ht]
      group
    rw [e1, hy]
    have e2 : u₀ * (z * z') * u₀⁻¹ = (u₀ * z * u₀⁻¹) * (u₀ * z' * u₀⁻¹) := by group
    rw [e2, hu₀z, hu₀z']
    have e3 : z * (z * z') = z' := by rw [← mul_assoc, hzz, one_mul]
    rw [e3]
    exact hgz'
  have hrz : rconj (quasithinOmegaOneCenter T) t⁻¹ = rconj (quasithinOmegaOneCenter T) g := by
    refine rconj_omegaOneCenter_congr hzZ hall ?_
    rw [inv_inv, ← hz'def]
    exact htz
  have hrz2 : rconj (quasithinOmegaOneCenter T) (g * t⁻¹) =
      rconj (quasithinOmegaOneCenter T) 1 := by
    refine rconj_omegaOneCenter_congr hzZ hall ?_
    have e : (g * t⁻¹)⁻¹ * z * (g * t⁻¹) = t * (g⁻¹ * z * g) * t⁻¹ := by group
    rw [e, ← hz'def, htz']
    simp
  have ht'N : t⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) := Subgroup.inv_mem _ htN
  refine ⟨t, htN, hrz, ?_, ?_⟩
  · rw [rconj_wOfU_eq_of_mem_normalizer T M ht'N, rconj_wOfU_eq_of_mem_normalizer T M hgN, hrz]
  · rw [rconj_rconj_eq]
    have hgt : g * t⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
      Subgroup.mul_mem _ hgN ht'N
    have h1N : (1 : G) ∈ Subgroup.normalizer (VZ T M : Set G) := Subgroup.one_mem _
    have h2 := rconj_wOfU_eq_of_mem_normalizer T M hgt
    rw [hrz2, ← rconj_wOfU_eq_of_mem_normalizer T M h1N, rconj_one_eq] at h2
    exact h2

end Hyp1281Two

end CFSG.Quasithin

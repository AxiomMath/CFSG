module

public import CFSG.Quasithin.H13.A5S1327a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

section Unique

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_of_isUniqueM {Y M : Subgroup G} (hM : IsUniqueM Y M) {x : G}
    (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) (hY : Y ≤ Subgroup.centralizer ({x} : Set G)) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := Subgroup.zpowers x with hP
  have hP1 : P ≠ ⊥ := by
    intro h
    exact hx1 ((Subgroup.zpowers_eq_bot).mp h)
  have hP2 : IsPGroup 2 ↥P := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hx2 hx1
  have hloc : IsTwoLocal (Subgroup.normalizer (P : Set G)) := ⟨P, hP1, hP2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hCN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (P : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hP, MonoidHom.map_zpowers]
    congr 1
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    show g * x * g⁻¹ = x
    rw [this]; group
  have hM'eq : M' = M := hM.2 M' ⟨hM', (hY.trans hCN).trans hle⟩
  rw [← hM'eq]
  exact hCN.trans hle

end Unique

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem borelOf_L_le_centralizer_z : borelOf L T ≤ Subgroup.centralizer ({S.z} : Set G) := by
  intro x hx
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hx.1
  have hsign : (S.frame.ρ ⟨x, hxN⟩).sign = 1 := (S.frame.image_L _).1 ⟨_, hx.1, rfl⟩
  have h4 : S.frame.ρ ⟨x, hxN⟩ 4 = 4 := by
    refine fix4_of_normalizes_K4 _ hsign fun τ hτ => ?_
    obtain ⟨t, htTL, rfl⟩ := S.K4_TL τ hτ
    have hxt : x * t * x⁻¹ ∈ T ⊓ L := (Subgroup.mem_normalizer_iff.mp hx.2 t).mp htTL
    have hxtN : x * t * x⁻¹ ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le hxt.1
    have := S.InK4_of_mem_TL ⟨_, hxtN⟩ hxt
    have e : (⟨x * t * x⁻¹, hxtN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨x, hxN⟩ * t * (⟨x, hxN⟩)⁻¹ := rfl
    rwa [e, map_mul, map_mul, map_inv] at this
  have hxz : x * S.z * x⁻¹ = S.z := by
    rw [S.conj_eq_iff ⟨x, hxN⟩ ⟨S.z, S.z_mem_V⟩, S.psi_z]
    exact pact_W4 h4
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * S.z = x * S.z * x⁻¹ * x := by group
    _ = S.z * x := by rw [hxz]

theorem borelOf_L_le_centralizer_of_decomp {ζ : G}
    (h : ∃ v ∈ S.V1, ∃ c ∈ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G), ζ = v * c) :
    borelOf L T ≤ Subgroup.centralizer ({ζ} : Set G) := by
  obtain ⟨v, hv, c, hc, rfl⟩ := h
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxv : x * v = v * x := by
    rcases S.mem_V1.1 hv with rfl | rfl
    · group
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (S.borelOf_L_le_centralizer_z hx))
  have hxc : x * c = c * x :=
    Subgroup.mem_centralizer_iff.mp hc x (Subgroup.mem_sup_left hx.1)
  calc x * (v * c) = (x * v) * c := by group
    _ = v * (x * c) := by rw [hxv]; group
    _ = v * c * x := by rw [hxc]; group

end Setting

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem borels_of_centralizer {H K VH : Subgroup G} (S' : Setting G T K VH)
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (hHK : H = K ⊔ T)
    (hdL : ∀ z' ∈ quasithinOmegaOneCenter T, ∃ v ∈ S.V1,
      ∃ c ∈ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G), z' = v * c)
    (hdK : ∀ z' ∈ quasithinOmegaOneCenter T, ∃ v ∈ S'.V1,
      ∃ c ∈ Subgroup.centralizer ((K ⊔ T : Subgroup G) : Set G), z' = v * c)
    {ζ : G} (hζZ : ζ ∈ quasithinOmegaOneCenter T) (hζK : ζ ∈ Subgroup.centralizer (K : Set G))
    (hζ1 : ζ ≠ 1) :
    borelOf L T ≤ Subgroup.normalizer (K : Set G) ∧
      borelOf K T ≤ Subgroup.normalizer (L : Set G) := by
  classical
  set Z := quasithinOmegaOneCenter T with hZdef
  have hHM : ¬ H ≤ Subgroup.normalizer (L : Set G) := hH.2.1
  have hZT : ∀ x ∈ Z, T ≤ Subgroup.centralizer ({x} : Set G) := fun x hx t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp hx).2.1) t ht)
  have hsq : ∀ x ∈ Z, x ^ 2 = 1 := fun x hx => (mem_quasithinOmegaOneCenter_iff.mp hx).2.2
  have hcentK : ∀ x ∈ Z, x ∈ Subgroup.centralizer (K : Set G) →
      K ⊔ T ≤ Subgroup.centralizer ({x} : Set G) := fun x hx hxK =>
    sup_le (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hxK k hk)) (hZT x hx)
  have hcentL : ∀ x ∈ Z, x ∈ Subgroup.centralizer (L : Set G) →
      L ⊔ T ≤ Subgroup.centralizer ({x} : Set G) := fun x hx hxL =>
    sup_le (fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hxL l hl)) (hZT x hx)
  have hCζ : Subgroup.centralizer ({ζ} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    centralizer_le_of_isUniqueM S'.uniqueM hζ1 (hsq ζ hζZ) (hcentK ζ hζZ hζK)
  have hζL : ζ ∉ Subgroup.centralizer (L : Set G) := by
    intro h
    apply hHM
    have hC := centralizer_le_of_isUniqueM S.uniqueM hζ1 (hsq ζ hζZ) (hcentL ζ hζZ h)
    rw [hHK]
    exact (hcentK ζ hζZ hζK).trans hC
  have hB1 : borelOf L T ≤ Subgroup.normalizer (K : Set G) :=
    (S.borelOf_L_le_centralizer_of_decomp (hdL ζ hζZ)).trans hCζ
  obtain ⟨ζ', hζ'Z, hζ'L, hζ'1⟩ : ∃ ζ' ∈ Z, ζ' ∈ Subgroup.centralizer (L : Set G) ∧ ζ' ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hHZ
    rw [hHK]
    refine sup_le ?_ (T_le_centralizer_omegaOneCenter T)
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨v, hv, c, hc, rfl⟩ := hdL x hx
    have hcZ : c ∈ Z := by
      have hvZ : v ∈ Z := by
        rcases S.mem_V1.1 hv with rfl | rfl
        · exact Z.one_mem
        · exact S.z_mem_omegaOneCenter
      have : c = v⁻¹ * (v * c) := by group
      rw [this]
      exact Z.mul_mem (Z.inv_mem hvZ) hx
    have hc1 : c = 1 := hcon c hcZ (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr le_sup_left) hc)
    subst hc1
    obtain ⟨v₀, hv₀, c₀, hc₀, hζdec⟩ := hdL ζ hζZ
    have hc₀Z : c₀ ∈ Z := by
      have hv₀Z : v₀ ∈ Z := by
        rcases S.mem_V1.1 hv₀ with rfl | rfl
        · exact Z.one_mem
        · exact S.z_mem_omegaOneCenter
      have : c₀ = v₀⁻¹ * ζ := by rw [hζdec]; group
      rw [this]
      exact Z.mul_mem (Z.inv_mem hv₀Z) hζZ
    have hc₀1 : c₀ = 1 := hcon c₀ hc₀Z (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr le_sup_left) hc₀)
    rw [hc₀1, mul_one] at hζdec
    have hζz : ζ = S.z := by
      rcases S.mem_V1.1 hv₀ with rfl | rfl
      · exact absurd hζdec hζ1
      · exact hζdec
    rcases S.mem_V1.1 hv with rfl | rfl
    · simp
    · rw [mul_one, ← hζz]
      exact (Subgroup.mem_centralizer_iff.mp hζK k hk).symm
  have hCζ' : Subgroup.centralizer ({ζ'} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_of_isUniqueM S.uniqueM hζ'1 (hsq ζ' hζ'Z) (hcentL ζ' hζ'Z hζ'L)
  have hB2 : borelOf K T ≤ Subgroup.normalizer (L : Set G) :=
    (S'.borelOf_L_le_centralizer_of_decomp (hdK ζ' hζ'Z)).trans hCζ'
  exact ⟨hB1, hB2⟩

end Setting

end CFSG.Quasithin.H13.A5

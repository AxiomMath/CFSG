module

public import CFSG.Quasithin.Background.E2Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

theorem MinParabolic.twoResidual_le_sup_pCore {X : Type*} [Group X] [Finite X]
    {T M : Subgroup X} (h : MinParabolic (⊤ : Subgroup X) T M) (hsolv : Group.IsSolvable X)
    {Y : Subgroup X} (hY : twoResidual (⊤ : Subgroup X) ≤ Y ⊔ kerIn M ⊤) :
    twoResidual (⊤ : Subgroup X) ≤ Y ⊔ CFSG.Open.pCore 2 X := by
  obtain ⟨p, hpp, hp2, hO2p2, hJbar, -, -⟩ := h.solvable_structure hsolv
  have : Fact p.Prime := ⟨hpp⟩
  set Q := CFSG.Open.pCore 2 X with hQ
  set φ := QuotientGroup.mk' Q with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective Q
  set P := CFSG.Open.pCore p (X ⧸ Q) with hP
  have hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal p
  have h2P : ∀ y : X ⧸ Q, ∃ k : ℕ, y ^ 2 ^ k ∈ P := by
    intro y
    obtain ⟨x, rfl⟩ := hφs y
    obtain ⟨k, hk⟩ := (B6.upperTwo_eq_top_iff (O2p X p)).mp hO2p2 x
    exact ⟨k, by rw [← map_pow]; exact Subgroup.mem_comap.mp hk⟩
  have hKP : twoResidual (⊤ : Subgroup (X ⧸ Q)) = P := E2.twoResidual_eq_pCore hpp hp2 h2P
  have hKmap : (twoResidual (⊤ : Subgroup X)).map φ = P := by
    rw [twoResidual_map_top hφs, hKP]
  have h1 : P ≤ Y.map φ ⊔ (frattini P).map P.subtype :=
    calc P = (twoResidual (⊤ : Subgroup X)).map φ := hKmap.symm
      _ ≤ (Y ⊔ kerIn M ⊤).map φ := Subgroup.map_mono hY
      _ = Y.map φ ⊔ (kerIn M ⊤).map φ := Subgroup.map_sup _ _ _
      _ = Y.map φ ⊔ (frattini P).map P.subtype := by rw [hJbar]
  have hΦn : ((frattini P).map P.subtype).Normal := inferInstance
  have h2 : P ≤ Y.map φ := by
    have h3 : (Y.map φ).subgroupOf P ⊔ frattini P = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, hy, f, hf, hyf⟩ := Subgroup.mem_sup_of_normal_right.mp (h1 x.2)
      obtain ⟨f', hf', rfl⟩ := hf
      have hyP : y ∈ P := by
        have : y = (x : X ⧸ Q) * ((f' : P) : X ⧸ Q)⁻¹ := by
          rw [← hyf, Subgroup.coe_subtype, mul_inv_cancel_right]
        rw [this]
        exact P.mul_mem x.2 (P.inv_mem f'.2)
      have hx : x = ⟨y, hyP⟩ * f' := Subtype.ext (by simpa using hyf.symm)
      rw [hx]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hy))
        (Subgroup.mem_sup_right hf')
    have h4 := frattini_nongenerating h3
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ (Y.map φ).subgroupOf P := by rw [h4]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  calc twoResidual (⊤ : Subgroup X) ≤ (Y.map φ).comap φ := by
        rw [← Subgroup.map_le_iff_le_comap, hKmap]
        exact h2
    _ = Y ⊔ Q := by rw [Subgroup.comap_map_eq, hφ, QuotientGroup.ker_mk']

theorem MinParabolic.twoResidual_le_sup_pCoreOf {G : Type*} [Group G] [Finite G]
    {H T M : Subgroup G} (h : MinParabolic H T M) (hsolv : Group.IsSolvable H)
    {Y : Subgroup G} (hYH : Y ≤ H) (hY : twoResidual H ≤ Y ⊔ kerIn M H) :
    twoResidual H ≤ Y ⊔ pCoreOf 2 H := by
  have hKH : twoResidual H ≤ H := twoResidual_le H
  have hJH : kerIn M H ≤ H := h.kerIn_le_H
  have hY' : twoResidual (⊤ : Subgroup H) ≤
      Y.subgroupOf H ⊔ kerIn (M.subgroupOf H) ⊤ := by
    rw [B6.twoResidual_top_eq_subgroupOf, B6.kerIn_subgroupOf_top,
      ← Subgroup.map_le_map_iff_of_injective H.subtype_injective, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hKH, Subgroup.map_subgroupOf_eq_of_le hYH,
      Subgroup.map_subgroupOf_eq_of_le hJH]
    exact hY
  have h1 := h.subgroupOf.twoResidual_le_sup_pCore hsolv hY'
  rw [B6.twoResidual_top_eq_subgroupOf,
    ← Subgroup.map_le_map_iff_of_injective H.subtype_injective, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hKH, Subgroup.map_subgroupOf_eq_of_le hYH] at h1
  exact h1

theorem MinParabolic.exists_prime_pow_mem_pCoreOf {G : Type*} [Group G] [Finite G]
    {H T M : Subgroup G} (h : MinParabolic H T M) (hsolv : Group.IsSolvable H) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∀ k ∈ twoResidual H, ∃ a : ℕ, k ^ p ^ a ∈ pCoreOf 2 H := by
  obtain ⟨p, hpp, hp2, hO2p2, -, -, -⟩ := h.subgroupOf.solvable_structure hsolv
  have : Fact p.Prime := ⟨hpp⟩
  refine ⟨p, hpp, hp2, fun k hk => ?_⟩
  set Q := CFSG.Open.pCore 2 H with hQ
  set φ := QuotientGroup.mk' Q with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective Q
  set P := CFSG.Open.pCore p (H ⧸ Q) with hP
  have h2P : ∀ y : H ⧸ Q, ∃ k : ℕ, y ^ 2 ^ k ∈ P := by
    intro y
    obtain ⟨x, rfl⟩ := hφs y
    obtain ⟨k, hk⟩ := (B6.upperTwo_eq_top_iff (O2p H p)).mp hO2p2 x
    exact ⟨k, by rw [← map_pow]; exact Subgroup.mem_comap.mp hk⟩
  have hKP : twoResidual (⊤ : Subgroup (H ⧸ Q)) = P := E2.twoResidual_eq_pCore hpp hp2 h2P
  have hkH : k ∈ H := twoResidual_le H hk
  have hk' : (⟨k, hkH⟩ : H) ∈ twoResidual (⊤ : Subgroup H) := by
    rw [B6.twoResidual_top_eq_subgroupOf]
    exact hk
  have hkP : φ ⟨k, hkH⟩ ∈ P := by
    rw [← hKP, ← twoResidual_map_top hφs]
    exact Subgroup.mem_map_of_mem φ hk'
  obtain ⟨a, ha⟩ := CFSG.LieType.BorelTits.pCore_isPGroup (G := H ⧸ Q) p ⟨_, hkP⟩
  have ha' : φ (⟨k, hkH⟩ ^ p ^ a) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val ha
  rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha'
  exact ⟨a, ⟨_, ha', by simp⟩⟩

end CFSG.Quasithin

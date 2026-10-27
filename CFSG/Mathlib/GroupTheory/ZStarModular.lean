module

public import CFSG.LocalAnalysis.ZStar

@[expose] public section

namespace CFSG.ZStarModular

private theorem inv_conj_of_sq_one {G : Type*} [Group G] {τ g : G} (hτ2 : τ * τ = 1) :
    τ * (g⁻¹ * τ * g * τ⁻¹) * τ⁻¹ = (g⁻¹ * τ * g * τ⁻¹)⁻¹ := by
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  have hR : (g⁻¹ * τ * g * τ)⁻¹ = τ * g⁻¹ * τ * g := by
    simp only [mul_inv_rev, inv_inv, hτinv]
    group
  have hL : τ * (g⁻¹ * τ * g * τ) * τ = τ * g⁻¹ * τ * g := by
    rw [show τ * (g⁻¹ * τ * g * τ) * τ = τ * g⁻¹ * τ * g * (τ * τ) by group]
    rw [hτ2, mul_one]
  rw [hτinv, hL, hR]

private theorem mul_conj_pow_eq_of_inv {G : Type*} [Group G] {τ u : G}
    (hu : τ * u * τ⁻¹ = u⁻¹) (k : ℕ) (hpow : u ^ (2 * k + 1) = 1) :
    u ^ k * (u * τ) * (u ^ k)⁻¹ = τ := by
  have hconj (m : ℕ) : (MulAut.conj τ) (u ^ m) = (u ^ m)⁻¹ := by
    rw [map_pow]
    rw [show (MulAut.conj τ) u = u⁻¹ by rw [MulAut.conj_apply]; exact hu]
    rw [inv_pow]
  have hconj_inv : (MulAut.conj τ) ((u ^ k)⁻¹) = u ^ k := by
    rw [map_inv, hconj k, inv_inv]
  have hτv : τ * (u ^ k)⁻¹ = u ^ k * τ := by
    have h' : τ * (u ^ k)⁻¹ * τ⁻¹ = u ^ k := by
      rw [← MulAut.conj_apply, hconj_inv]
    conv_rhs => rw [← h']
    group
  calc u ^ k * (u * τ) * (u ^ k)⁻¹
      = (u ^ k * u) * (τ * (u ^ k)⁻¹) := by group
    _ = u ^ (k + 1) * (τ * (u ^ k)⁻¹) := by rw [← pow_succ]
    _ = u ^ (k + 1) * (u ^ k * τ) := by rw [hτv]
    _ = u ^ ((k + 1) + k) * τ := by rw [← mul_assoc, ← pow_add]
    _ = u ^ (2 * k + 1) * τ := by rw [show (k + 1) + k = 2 * k + 1 by omega]
    _ = τ := by rw [hpow, one_mul]

private theorem exists_mul_centralizer_of_conj_mem_coset_aux {G : Type*} [Group G]
    (Y : Subgroup G) (hY : Odd (Nat.card Y)) {τ : G} (hτ : τ ^ 2 = 1) {g : G}
    (hg : g⁻¹ * τ * g * τ⁻¹ ∈ Y) :
    ∃ y ∈ Y, ∃ w ∈ Subgroup.centralizer ({τ} : Set G), g = w * y := by
  have hτ2 : τ * τ = 1 := by rwa [pow_two] at hτ
  obtain ⟨k, hk⟩ := hY
  have hpow : (g⁻¹ * τ * g * τ⁻¹) ^ (2 * k + 1) = 1 := by
    have h := pow_card_eq_one' (G := Y) (x := (⟨g⁻¹ * τ * g * τ⁻¹, hg⟩ : Y))
    rw [hk] at h
    simpa using h
  have hτu : τ * (g⁻¹ * τ * g * τ⁻¹) * τ⁻¹ = (g⁻¹ * τ * g * τ⁻¹)⁻¹ :=
    inv_conj_of_sq_one hτ2
  have hmain := mul_conj_pow_eq_of_inv hτu k hpow
  have huτ : (g⁻¹ * τ * g * τ⁻¹) * τ = g⁻¹ * τ * g := by group
  set v : G := (g⁻¹ * τ * g * τ⁻¹) ^ k with hv
  have hmain' : v * (g⁻¹ * τ * g) * v⁻¹ = τ := by
    rw [huτ] at hmain
    exact hmain
  refine ⟨v, ?_, g * v⁻¹, ?_, ?_⟩
  · rw [hv]; exact Y.pow_mem hg k
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have hgv : (g * v⁻¹) * τ * (g * v⁻¹)⁻¹ = τ := by
      have h1 : (g * v⁻¹) * τ * (g * v⁻¹)⁻¹
          = g * v⁻¹ * (v * (g⁻¹ * τ * g) * v⁻¹) * v * g⁻¹ := by
        conv_lhs => rw [← hmain']
        group
      rw [h1]; group
    have hwτ : (g * v⁻¹) * τ = τ * (g * v⁻¹) := by
      conv_rhs => rw [← hgv]
      group
    rw [hwτ]
  · group

theorem exists_odd_normal_of_isolated {G : Type} [Group G] [Finite G] {N C : Subgroup G}
    (hCN : C ≤ N) (hC : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C) {s : G} (hsN : s ∈ N)
    (hs2 : s * s ∈ C) (hs1 : s ∉ C)
    (hiso : ∀ g ∈ N, g * s * g⁻¹ * s * (g * s * g⁻¹)⁻¹ * s⁻¹ ∈ C → g * s * g⁻¹ * s⁻¹ ∈ C) :
    ∃ Y : Subgroup G, C ≤ Y ∧ Y ≤ N ∧ (∀ n ∈ N, ∀ y ∈ Y, n * y * n⁻¹ ∈ Y) ∧
      Odd (C.relIndex Y) ∧
      ∀ n ∈ N, ∃ y ∈ Y, ∃ w ∈ N, w * s * w⁻¹ * s⁻¹ ∈ C ∧ n = y * w := by
  classical
  let CN : Subgroup ↥N := C.subgroupOf N
  have hCNn : CN.Normal :=
    (Subgroup.normal_subgroupOf_iff hCN).mpr fun h k hh hk => hC k hk h hh
  let X := ↥N ⧸ CN
  let fintypeX : Fintype X := Fintype.ofFinite X
  let σ : ↥N := ⟨s, hsN⟩
  let t : X := QuotientGroup.mk' CN σ
  have ht1 : t ≠ 1 := by
    intro h
    have hσ : σ ∈ CN := (QuotientGroup.eq_one_iff σ).mp h
    exact hs1 ((Subgroup.mem_subgroupOf).mp hσ)
  have ht2 : t * t = 1 := by
    have hmem : σ * σ ∈ CN := (Subgroup.mem_subgroupOf).mpr hs2
    have h : (QuotientGroup.mk' CN) (σ * σ) = 1 := (QuotientGroup.eq_one_iff (σ * σ)).mpr hmem
    simpa [t, map_mul] using h
  have hisolated : ∀ x : X, (x * t * x⁻¹) * t = t * (x * t * x⁻¹) → x * t * x⁻¹ = t := by
    intro x hx
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective CN x
    set b : ↥N := a * σ * a⁻¹ with hb
    have hA : (QuotientGroup.mk' CN) a * t * ((QuotientGroup.mk' CN) a)⁻¹
        = (QuotientGroup.mk' CN) b := by
      simp only [t, hb, map_mul, map_inv]
    have hcomm : (QuotientGroup.mk' CN) (b * σ * b⁻¹ * σ⁻¹) = 1 := by
      rw [show (QuotientGroup.mk' CN) (b * σ * b⁻¹ * σ⁻¹)
            = (QuotientGroup.mk' CN) b * t * ((QuotientGroup.mk' CN) b)⁻¹ * t⁻¹ by
          simp only [t, map_mul, map_inv]]
      rw [← hA]
      rw [hx]; group
    have hmemCN : b * σ * b⁻¹ * σ⁻¹ ∈ CN := (QuotientGroup.eq_one_iff _).mp hcomm
    have hmemC : (b : G) * s * (b : G)⁻¹ * s⁻¹ ∈ C := by
      have h := (Subgroup.mem_subgroupOf).mp hmemCN
      simpa [hb] using h
    have hconclC : (b : G) * s⁻¹ ∈ C := by
      have h := hiso (a : G) a.2 (by simpa [hb] using hmemC)
      simpa [hb] using h
    have hconclCN : b * σ⁻¹ ∈ CN :=
      (Subgroup.mem_subgroupOf).mpr (by simpa using hconclC)
    have hbσ : (QuotientGroup.mk' CN) b = (QuotientGroup.mk' CN) σ := by
      change (b : X) = (σ : X)
      rw [QuotientGroup.eq_iff_div_mem]
      simpa [div_eq_mul_inv] using hconclCN
    rw [hA, hbσ]
  obtain ⟨M, hMnormal, hModd, hMcomm⟩ := CFSG.ZStar.glauberman_zStar X t ht1 ht2 hisolated
  set Y : Subgroup G := (M.comap (QuotientGroup.mk' CN)).map N.subtype with hY
  have hCY : C ≤ Y := by
    intro c hc
    rw [hY, Subgroup.mem_map]
    refine ⟨⟨c, hCN hc⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hone : (QuotientGroup.mk' CN) (⟨c, hCN hc⟩ : ↥N) = 1 :=
      (QuotientGroup.eq_one_iff (⟨c, hCN hc⟩ : ↥N)).mpr ((Subgroup.mem_subgroupOf).mpr hc)
    rw [hone]
    exact M.one_mem
  have hYN : Y ≤ N := by
    rw [hY]
    exact Subgroup.map_subtype_le _
  have hYnorm : ∀ n ∈ N, ∀ y ∈ Y, n * y * n⁻¹ ∈ Y := by
    intro n hn y hy
    rw [hY, Subgroup.mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [hY, Subgroup.mem_map]
    refine ⟨⟨n, hn⟩ * a * ⟨n, hn⟩⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_comap] at ha ⊢
      rw [show (QuotientGroup.mk' CN) (⟨n, hn⟩ * a * ⟨n, hn⟩⁻¹)
            = (QuotientGroup.mk' CN) ⟨n, hn⟩ * (QuotientGroup.mk' CN) a
              * ((QuotientGroup.mk' CN) ⟨n, hn⟩)⁻¹ by rw [map_mul, map_mul, map_inv]]
      exact hMnormal.conj_mem _ ha _
    · simp
  have hOdd : Odd (C.relIndex Y) := by
    have h1 : CN.relIndex (M.comap (QuotientGroup.mk' CN)) = Nat.card M := by
      have hker := Subgroup.relIndex_ker (f := QuotientGroup.mk' CN)
        (K := M.comap (QuotientGroup.mk' CN))
      simpa only [QuotientGroup.ker_mk' CN,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective CN) M] using hker
    have h2 : (CN.map N.subtype).relIndex ((M.comap (QuotientGroup.mk' CN)).map N.subtype)
        = CN.relIndex (M.comap (QuotientGroup.mk' CN)) :=
      Subgroup.relIndex_map_map_of_injective _ _ N.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hCN] at h2
    have hrel : C.relIndex Y = Nat.card M := by
      rw [hY]
      exact h2.trans h1
    rw [hrel]
    exact hModd
  have hdecomp : ∀ n ∈ N, ∃ y ∈ Y, ∃ w ∈ N, w * s * w⁻¹ * s⁻¹ ∈ C ∧ n = y * w := by
    intro n hn
    set x : X := (QuotientGroup.mk' CN) ⟨n, hn⟩ with hx
    have hg : x⁻¹⁻¹ * t * x⁻¹ * t⁻¹ ∈ M := by
      rw [inv_inv]
      exact hMcomm x
    obtain ⟨y, hyM, w, hwcent, hxinv⟩ :=
      exists_mul_centralizer_of_conj_mem_coset_aux M hModd
        (by rw [pow_two]; exact ht2) hg
    have hx_eq : x = y⁻¹ * w⁻¹ := by
      rw [← inv_inv x, hxinv]; group
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective CN y
    obtain ⟨wN, hwN⟩ := QuotientGroup.mk'_surjective CN w
    have haM : a ∈ M.comap (QuotientGroup.mk' CN) := by
      rw [Subgroup.mem_comap, ha]
      exact hyM
    have haY : (a : G) ∈ Y := by
      rw [hY, Subgroup.mem_map]
      exact ⟨a, haM, rfl⟩
    have hxN : (QuotientGroup.mk' CN) ⟨n, hn⟩ = (QuotientGroup.mk' CN) (a⁻¹ * wN⁻¹) := by
      rw [hx] at hx_eq
      rw [← ha, ← hwN] at hx_eq
      simpa only [map_mul, map_inv] using hx_eq
    set c : ↥N := ⟨n, hn⟩ * (a⁻¹ * wN⁻¹)⁻¹ with hc_def
    have hcCN : c ∈ CN := by
      have h := (QuotientGroup.eq_iff_div_mem).mp hxN
      rw [hc_def]
      simpa [div_eq_mul_inv] using h
    have hn_eq : (⟨n, hn⟩ : ↥N) = c * a⁻¹ * wN⁻¹ := by
      rw [hc_def]; group
    have hwcent' : (QuotientGroup.mk' CN) wN⁻¹ ∈ Subgroup.centralizer ({t} : Set X) := by
      have : (QuotientGroup.mk' CN) wN⁻¹ = w⁻¹ := by rw [map_inv, hwN]
      rw [this]
      exact (Subgroup.centralizer ({t} : Set X)).inv_mem hwcent
    have hcomm_w : (QuotientGroup.mk' CN) (wN⁻¹ * σ * (wN⁻¹)⁻¹ * σ⁻¹) = 1 := by
      have h2 : t * (QuotientGroup.mk' CN) wN⁻¹ = (QuotientGroup.mk' CN) wN⁻¹ * t :=
        (Subgroup.mem_centralizer_iff).mp hwcent' t (Set.mem_singleton t)
      rw [show (QuotientGroup.mk' CN) (wN⁻¹ * σ * (wN⁻¹)⁻¹ * σ⁻¹)
            = (QuotientGroup.mk' CN) wN⁻¹ * t * ((QuotientGroup.mk' CN) wN⁻¹)⁻¹ * t⁻¹ by
          simp only [t, map_mul, map_inv]]
      rw [← h2]; group
    have hwC : ((wN⁻¹ : ↥N) : G) * s * ((wN⁻¹ : ↥N) : G)⁻¹ * s⁻¹ ∈ C := by
      have h := (Subgroup.mem_subgroupOf).mp
        ((QuotientGroup.eq_one_iff (wN⁻¹ * σ * (wN⁻¹)⁻¹ * σ⁻¹)).mp hcomm_w)
      simpa using h
    have hyY : ((c * a⁻¹ : ↥N) : G) ∈ Y := by
      have hcY : (c : G) ∈ Y := hCY ((Subgroup.mem_subgroupOf).mp hcCN)
      have haY' : ((a⁻¹ : ↥N) : G) ∈ Y := by simpa using Y.inv_mem haY
      simpa using Y.mul_mem hcY haY'
    have hwN' : ((wN⁻¹ : ↥N) : G) ∈ N := by simp
    have hn_eq' : n = ((c * a⁻¹ : ↥N) : G) * ((wN⁻¹ : ↥N) : G) := by
      exact congrArg (fun z : ↥N => (z : G)) hn_eq
    exact ⟨((c * a⁻¹ : ↥N) : G), hyY, ((wN⁻¹ : ↥N) : G), hwN', hwC, hn_eq'⟩
  exact ⟨Y, hCY, hYN, hYnorm, hOdd, hdecomp⟩

end CFSG.ZStarModular

end

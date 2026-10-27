module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegKG
public import CFSG.LocalAnalysis.StandardType.KGNormMod

public section

namespace CFSG.StandardType.KGUniv

private lemma lift_mem_ker {C K : Type} [Group C] [Group K] (κ : C →* K)
    (lift : MulAut K →* MulAut C) (hlift : ∀ α x, κ (lift α x) = α (κ x))
    (α : MulAut K) {z : C} (hz : z ∈ κ.ker) : lift α z ∈ κ.ker := by
  rw [MonoidHom.mem_ker] at hz ⊢
  rw [hlift α z, hz, map_one]

private lemma lift_inv_mem_ker {C K : Type} [Group C] [Group K] (κ : C →* K)
    (lift : MulAut K →* MulAut C) (hlift : ∀ α x, κ (lift α x) = α (κ x))
    (α : MulAut K) {z : C} (hz : z ∈ κ.ker) : (lift α)⁻¹ z ∈ κ.ker := by
  have h := lift_mem_ker κ lift hlift α⁻¹ hz
  rwa [map_inv] at h

private lemma lift_mem_ker_iff {C K : Type} [Group C] [Group K] (κ : C →* K)
    (lift : MulAut K →* MulAut C) (hlift : ∀ α x, κ (lift α x) = α (κ x))
    (α : MulAut K) (t : C) : lift α t ∈ κ.ker ↔ t ∈ κ.ker := by
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hlift α t]
  constructor
  · intro h
    have h' := congrArg (fun x => (α⁻¹ : MulAut K) x) h
    simpa using h'
  · intro h
    rw [h, map_one]

private lemma apply_iterate {C K : Type} [Group C] [Group K] (κ : C →* K)
    (lift : MulAut K →* MulAut C) (hlift : ∀ α x, κ (lift α x) = α (κ x))
    (α : MulAut K) (i : ℕ) (y : C) : κ (((lift α) ^ i) y) = (α ^ i) (κ y) := by
  rw [← map_pow lift α i]
  exact hlift (α ^ i) y

private lemma map_norm {C K : Type} [Group C] [Group K] (κ : C →* K)
    (lift : MulAut K →* MulAut C) (hlift : ∀ α x, κ (lift α x) = α (κ x))
    (α : MulAut K) (p : ℕ) (s : C) :
    κ (((List.range p).map fun i => ((lift α) ^ i) s).prod) =
      ((List.range p).map fun i => (α ^ i) (κ s)).prod := by
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact apply_iterate κ lift hlift α i s

private lemma map_stable {C K : Type} [Group C] [Group K] (κ : C →* K)
    (hκ : Function.Surjective κ) (lift : MulAut K →* MulAut C)
    (hlift : ∀ α x, κ (lift α x) = α (κ x)) (α : MulAut K)
    {TC : Subgroup C} (hstab : ∀ t : C, lift α t ∈ TC ↔ t ∈ TC) :
    ∀ t : K, α t ∈ TC.map κ ↔ t ∈ TC.map κ := by
  have hγker : ∀ z ∈ κ.ker, (lift α)⁻¹ z ∈ κ.ker :=
    fun z hz => lift_inv_mem_ker κ lift hlift α hz
  intro t
  constructor
  · intro ht
    obtain ⟨c', hc', hc'eq⟩ := Subgroup.mem_map.mp ht
    obtain ⟨c'', hc''⟩ := hκ t
    rw [← hc''] at hc'eq ⊢
    have hz : (lift α) c'' * c'⁻¹ ∈ κ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hlift α c'', ← hc'eq, mul_inv_cancel]
    have hzc : (lift α) c'' = ((lift α) c'' * c'⁻¹) * c' := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have hc''eq : c'' = (lift α)⁻¹ ((lift α) c'' * c'⁻¹) * (lift α)⁻¹ c' := by
      calc c'' = (lift α)⁻¹ (((lift α) c'' * c'⁻¹) * c') := by
            rw [← hzc, MulAut.inv_apply_self]
        _ = (lift α)⁻¹ ((lift α) c'' * c'⁻¹) * (lift α)⁻¹ c' := by rw [map_mul]
    have hinv : (lift α)⁻¹ c' ∈ TC := by
      have h := (hstab ((lift α)⁻¹ c')).1
      rw [MulAut.apply_inv_self] at h
      exact h hc'
    have h1 : κ c'' = κ ((lift α)⁻¹ ((lift α) c'' * c'⁻¹)) * κ ((lift α)⁻¹ c') := by
      calc κ c'' = κ ((lift α)⁻¹ ((lift α) c'' * c'⁻¹) * (lift α)⁻¹ c') :=
            congrArg κ hc''eq
        _ = κ ((lift α)⁻¹ ((lift α) c'' * c'⁻¹)) * κ ((lift α)⁻¹ c') := by rw [map_mul]
    have h2 : κ ((lift α)⁻¹ ((lift α) c'' * c'⁻¹)) = 1 := by
      have h := hγker ((lift α) c'' * c'⁻¹) hz
      rwa [MonoidHom.mem_ker] at h
    rw [h2, one_mul] at h1
    exact Subgroup.mem_map.mpr ⟨(lift α)⁻¹ c', hinv, h1.symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact Subgroup.mem_map.mpr ⟨(lift α) c, (hstab c).2 hc, hlift α c⟩

theorem kgLangTorusConcl_of_cover {p : ℕ} (hp : p.Prime) {K R C : Type} [Group K] [Group R]
    [Group C] [Finite C]
    (θ : K ⧸ Subgroup.center K ≃* R) (θC : C ⧸ Subgroup.center C ≃* R)
    (I : Set (MulAut R)) (A : Subgroup (MulAut K)) (α₀ : MulAut K)
    (κ : C →* K) (hκ : Function.Surjective κ) (hκc : κ.ker ≤ Subgroup.center C)
    (hcop : Nat.Coprime (Nat.card (Subgroup.center C)) p)
    (lift : MulAut K →* MulAut C) (hlift : ∀ α x, κ (lift α x) = α (κ x))
    (hind : ∀ α, kgInducedAut θC (lift α) = kgInducedAut θ α)
    (hconcl : KGLangTorusConcl p θC I (A.map lift) (lift α₀)) :
    KGLangTorusConcl p θ I A α₀ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨TC, hab, hstab, hfix, hnorm, e0, he, he1, hep, heA⟩ := hconcl
  have hYβ : ∀ t : C, lift α₀ t ∈ (TC ⊓ κ.ker : Subgroup C) ↔ t ∈ (TC ⊓ κ.ker : Subgroup C) := by
    intro t
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (hstab t) (lift_mem_ker_iff κ lift hlift α₀ t)
  have hYp : Nat.Coprime (Nat.card (TC ⊓ κ.ker : Subgroup C)) p := by
    have hle : (TC ⊓ κ.ker : Subgroup C) ≤ Subgroup.center C :=
      le_trans inf_le_right hκc
    exact Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_le hle) hcop
  refine ⟨TC.map κ, ?_, map_stable κ hκ lift hlift α₀ hstab, ?_, ?_, ?_⟩
  · intro a ha c hc
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hc
    rw [← map_mul, ← map_mul, hab x hx y hy]
  · intro α hαA hαI t ht
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp ht
    have hliftA : lift α ∈ A.map lift := Subgroup.mem_map.mpr ⟨α, hαA, rfl⟩
    have hI' : kgInducedAut θC (lift α) ∈ I := by rw [hind α]; exact hαI
    rw [← hlift α c, hfix (lift α) hliftA hI' c hc]
  · rintro t ht htfix
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ht
    have hxker : x⁻¹ * lift α₀ x ∈ κ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hlift α₀ x, htfix, inv_mul_cancel]
    have hxTC : x⁻¹ * lift α₀ x ∈ TC := TC.mul_mem (TC.inv_mem hx) ((hstab x).2 hx)
    have hxY : x⁻¹ * lift α₀ x ∈ (TC ⊓ κ.ker : Subgroup C) :=
      Subgroup.mem_inf.mpr ⟨hxTC, hxker⟩
    obtain ⟨s, hs, hsY⟩ :=
      exists_norm_mod_of_fixed_mod hp TC (TC ⊓ κ.ker) hab (lift α₀) hstab
        inf_le_left hYβ hYp hnorm x hx hxY
    refine ⟨κ s, Subgroup.mem_map.mpr ⟨s, hs, rfl⟩, ?_⟩
    have hN : κ (((List.range p).map fun i => ((lift α₀) ^ i) s).prod) =
        ((List.range p).map fun i => (α₀ ^ i) (κ s)).prod := map_norm κ lift hlift α₀ p s
    have hsYker : x * (((List.range p).map fun i => ((lift α₀) ^ i) s).prod)⁻¹ ∈ κ.ker :=
      (Subgroup.mem_inf.mp hsY).2
    have hkx : κ x = κ (((List.range p).map fun i => ((lift α₀) ^ i) s).prod) := by
      have h1 := hsYker
      rw [MonoidHom.mem_ker, map_mul, map_inv] at h1
      calc κ x = (κ x * (κ (((List.range p).map fun i => ((lift α₀) ^ i) s).prod))⁻¹)
            * κ (((List.range p).map fun i => ((lift α₀) ^ i) s).prod) := by
              rw [mul_assoc, inv_mul_cancel, mul_one]
        _ = 1 * κ (((List.range p).map fun i => ((lift α₀) ^ i) s).prod) := by rw [h1]
        _ = κ (((List.range p).map fun i => ((lift α₀) ^ i) s).prod) := by rw [one_mul]
    rw [hN] at hkx
    exact hkx
  · refine ⟨κ e0, Subgroup.mem_map.mpr ⟨e0, he, rfl⟩, ?_, ?_, ?_⟩
    · intro hκe
      have heker : e0 ∈ κ.ker := by rw [MonoidHom.mem_ker]; exact hκe
      have heZ : e0 ∈ Subgroup.center C := hκc heker
      have hord : orderOf e0 = p := orderOf_eq_prime hep he1
      have hdvd : p ∣ Nat.card (Subgroup.center C) := by
        rw [← hord]
        exact Subgroup.orderOf_dvd_natCard (Subgroup.center C) heZ
      exact (Nat.Prime.one_lt hp).ne' (hcop.symm.eq_one_of_dvd hdvd)
    · rw [← map_pow, hep, map_one]
    · intro α hα
      rw [← hlift α e0, heA (lift α) (Subgroup.mem_map.mpr ⟨α, hα, rfl⟩)]

end CFSG.StandardType.KGUniv

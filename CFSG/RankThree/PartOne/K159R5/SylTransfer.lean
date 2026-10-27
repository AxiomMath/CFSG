module

public import CFSG.RankThree.PartOne.K159R5.Rank

public section

namespace CFSG.RankThree.PartOne.K159R5

variable {Γ C : Type} [Group Γ] [Group C]

theorem SylAb.of_map {p : ℕ} (Φ : Γ →* C) {Y : Subgroup Γ}
    (hk : ∀ t ∈ Y, (∃ k : ℕ, t ^ p ^ k = 1) → Φ t = 1 → t = 1) (h : SylAb p (Y.map Φ)) :
    SylAb p Y := by
  intro T hTY hTp x hx y hy
  have hTm : IsPGroup p ↥(T.map Φ) := by
    intro u
    obtain ⟨t, ht, htu⟩ := u.2
    obtain ⟨k, hk'⟩ := hTp ⟨t, ht⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : t ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk'
    have h2 : (u : C) = Φ t := htu.symm
    simp [h2, ← map_pow, h1]
  have hcomm := h (T.map Φ) (Subgroup.map_mono hTY) hTm (Φ x) (Subgroup.mem_map_of_mem Φ hx) (Φ y)
    (Subgroup.mem_map_of_mem Φ hy)
  have hcT : x * y * (y * x)⁻¹ ∈ T := T.mul_mem (T.mul_mem hx hy) (T.inv_mem (T.mul_mem hy hx))
  obtain ⟨k, hk'⟩ := hTp ⟨_, hcT⟩
  have h1 : (x * y * (y * x)⁻¹) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk'
  have h2 : Φ (x * y * (y * x)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_mul, hcomm, mul_inv_cancel]
  have := hk _ (hTY hcT) ⟨k, h1⟩ h2
  exact mul_inv_eq_one.1 this

theorem SylAb.map_of_injOn {p : ℕ} (Φ : Γ →* C) {Y : Subgroup Γ}
    (hinj : ∀ x ∈ Y, ∀ y ∈ Y, Φ x = Φ y → x = y) (h : SylAb p Y) : SylAb p (Y.map Φ) := by
  intro Q hQ hQp u hu v hv
  obtain ⟨x, hxY, rfl⟩ := hQ hu
  obtain ⟨y, hyY, rfl⟩ := hQ hv
  have hTp : IsPGroup p ↥(Q.comap Φ ⊓ Y) := by
    intro t
    obtain ⟨k, hk⟩ := hQp ⟨Φ t, t.2.1⟩
    refine ⟨k, Subtype.ext (hinj _ (pow_mem t.2.2 _) 1 Y.one_mem ?_)⟩
    have h1 : (Φ (t : Γ)) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    simpa [map_pow] using h1
  have := h (Q.comap Φ ⊓ Y) inf_le_right hTp x ⟨hu, hxY⟩ y ⟨hv, hyY⟩
  simpa using congrArg Φ this

theorem SylAb.of_hom {p : ℕ} {G H : Type} [Group G] [Group H] {Y : Subgroup G} (f : ↥Y →* H)
    (hf : Function.Injective f)
    (hH : ∀ T : Subgroup H, IsPGroup p ↥T → ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) : SylAb p Y := by
  have h1 : SylAb p (⊤ : Subgroup ↥Y) :=
    SylAb.of_map f (fun t _ _ ht => hf (by rw [ht, map_one])) (fun P _ hP x hx y hy => hH P hP x hx y hy)
  have h2 := SylAb.map_of_injOn Y.subtype (fun x _ y _ hxy => Subtype.ext hxy) h1
  have h3 : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rwa [h3] at h2

theorem SylAb.of_cover {p : ℕ} (hp : p.Prime) (Φ : Γ →* C) (hker : ¬ p ∣ Nat.card Φ.ker)
    {Y : Subgroup Γ} (h : SylAb p (Y.map Φ)) : SylAb p Y := by
  refine SylAb.of_map Φ (fun t _ ⟨k, hk⟩ ht => ?_) h
  have htk : t ∈ Φ.ker := ht
  by_contra hne
  have hne' : (⟨t, htk⟩ : Φ.ker) ≠ 1 := fun h' => hne (congrArg Subtype.val h')
  have hord : orderOf (⟨t, htk⟩ : Φ.ker) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk))
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hord
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, pow_zero, orderOf_eq_one_iff] at hj
    exact hne' hj
  apply hker
  exact (hj ▸ dvd_pow_self p hj0).trans (orderOf_dvd_natCard _)

end CFSG.RankThree.PartOne.K159R5

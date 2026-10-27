module

public import CFSG.RankThree.PartOne.CTP.IStd
public import CFSG.RankThree.PartOne.CTP.ThetaAbs

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.RankThree.PartOne

variable {G : Type} [Group G] [Finite G]

theorem pairLayer_conj_centralizes {c : G} {f₀ : ℕ} {I K BK : Subgroup G}
    {J : Fin 3 → Fin 3 → Subgroup G} (hcfg : IConfig c f₀ I K BK J) (hF : IFacts c f₀ I K BK J)
    {b h : G} (hbI : I ∈ thetaComponentsAt 5 b) (hh : h * h = 1)
    (h5norm : ∀ x : G, x * b = b * x → (∃ k : ℕ, orderOf x = 5 ^ k) →
      x ∈ Subgroup.normalizer (I : Set G))
    {a₀ b₀ : Fin 3} (hab : a₀ ≠ b₀) (hJ'K : conjBy h (J a₀ b₀) ≤ Subgroup.centralizer (K : Set G))
    (hline : Subgroup.zpowers b = conjBy h (BK ⊓ J a₀ b₀)) :
    ∀ y ∈ conjBy h (pairLayer I BK (J a₀ b₀)), ∀ u ∈ I, y * u = u * y := by
  obtain ⟨x, t, hxM, hx25, hx5, htJ, ht2, htx, hMgen⟩ := hF.generation a₀ b₀ hab
  have hhinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh
  set x' : G := h * x * h⁻¹ with hx'
  set t' : G := h * t * h⁻¹ with ht'
  have hxe : x = h * x' * h := by
    calc x = (h * h) * x * (h * h) := by rw [hh]; group
      _ = h * (h * x * h⁻¹) * h := by rw [hhinv]; group
  have hx'5 : Subgroup.zpowers (x' ^ 5) = Subgroup.zpowers b := by
    rw [hline, ← hx5]
    have hpow : x' ^ 5 = h * x ^ 5 * h⁻¹ := by rw [hx', conj_pow]
    rw [hpow]
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨(x ^ 5) ^ k, ⟨k, rfl⟩, by simp [MulAut.conj_apply, conj_zpow]⟩
    · rintro ⟨z, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, by simp [MulAut.conj_apply, conj_zpow]⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hx'5 ▸ Subgroup.mem_zpowers b)
  have hcomm : x' * b = b * x' := by
    rw [← hm]
    exact (((Commute.refl x').pow_right 5).zpow_right m).eq
  have hx'ord : orderOf x' = 25 := by
    rw [hx']
    exact (MulEquiv.orderOf_eq (MulAut.conj h) x).trans hx25
  have ht'x' : t' * x' * t'⁻¹ = x'⁻¹ := by
    have : t' * x' * t'⁻¹ = h * (t * x * t⁻¹) * h⁻¹ := by simp only [ht', hx']; group
    rw [this, htx]
    simp only [hx']
    group
  have ht'b : t' * b * t'⁻¹ = b⁻¹ := by
    have h1 : t' * x' ^ 5 * t'⁻¹ = (x' ^ 5)⁻¹ := by
      rw [← conj_pow, ht'x', inv_pow]
    have h2 : t' * (x' ^ 5) ^ m * t'⁻¹ = ((x' ^ 5)⁻¹) ^ m := by
      rw [← conj_zpow, h1]
    rw [← hm, h2, inv_zpow]
  have hzp : Subgroup.zpowers (t' * b * t'⁻¹) = Subgroup.zpowers b := by
    rw [ht'b, Subgroup.zpowers_inv]
  have ht'J' : t' ∈ conjBy h (J a₀ b₀) := by
    rw [Equivariance.mem_conjBy]
    have : h⁻¹ * t' * h = t := by simp only [ht']; group
    rw [this]
    exact htJ
  have ht'K : ∀ k ∈ K, t' * k = k * t' := fun k hk =>
    (Subgroup.mem_centralizer_iff.mp (hJ'K ht'J') k hk).symm
  have hKfix : conjBy t' K = K := conjBy_eq_of_commute ht'K
  have hIfix : conjBy t' I = I :=
    theta_conj_eq (by norm_num : Nat.Prime 5) hbI hcfg.K_le hF.K_perfect hF.K_ne_bot hzp hKfix
  have ht'N : t' ∈ Subgroup.normalizer (I : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have h1 : t' * z * t'⁻¹ ∈ conjBy t' I ↔ z ∈ I := by
      rw [Equivariance.mem_conjBy]
      have : t'⁻¹ * (t' * z * t'⁻¹) * t' = z := by group
      rw [this]
    rw [hIfix] at h1
    exact h1.symm
  have ht'sq : t' ^ 2 = 1 := by
    have h2 : t ^ 2 = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht2] at this
    rw [ht', conj_pow, h2]
    group
  have ht'I : ∀ u ∈ I, t' * u = u * t' := hF.inv_centralizes t' ht'N ht'sq ht'K
  have hx'N : x' ∈ Subgroup.normalizer (I : Set G) :=
    h5norm x' hcomm ⟨2, by rw [hx'ord]; norm_num⟩
  have hx'I : ∀ u ∈ I, x' * u = u * x' :=
    commute_of_inverted_odd hx'N ht'I ht'x' (by rw [hx'ord]; norm_num)
  have hxhI : ∀ y ∈ conjBy h I, x * y = y * x := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := hy
    have hy' : (MulAut.conj h).toMonoidHom u = h * u * h := by
      simp [MulAut.conj_apply, hhinv]
    rw [hy']
    have key := hx'I u hu
    calc x * (h * u * h) = h * (x' * u) * h := by
          conv_lhs => rw [hxe]
          calc h * x' * h * (h * u * h) = h * x' * (h * h) * u * h := by group
            _ = h * (x' * u) * h := by rw [hh]; group
      _ = h * (u * x') * h := by rw [key]
      _ = h * u * h * x := by
          conv_rhs => rw [hxe]
          calc h * (u * x') * h = h * u * (h * h) * x' * h := by rw [hh]; group
            _ = h * u * h * (h * x' * h) := by group
  have hJ0K : J a₀ b₀ ≤ K := hF.J_le_K a₀ b₀ hab
  have hIeq : I = K ⊔ Subgroup.zpowers x := by
    have h1 := hF.K_sup_M a₀ b₀ hab
    rw [hMgen] at h1
    refine h1.symm.trans (le_antisymm ?_ ?_)
    · exact sup_le le_sup_left (sup_le (hJ0K.trans le_sup_left) le_sup_right)
    · exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have hJ'I : ∀ y ∈ conjBy h (J a₀ b₀), ∀ u ∈ I, y * u = u * y := by
    intro y hy u hu
    have hyK : ∀ k ∈ K, k * y = y * k := Subgroup.mem_centralizer_iff.mp (hJ'K hy)
    have hyI : y ∈ conjBy h I :=
      Subgroup.map_mono (hJ0K.trans hcfg.K_le) hy
    have hyx : x * y = y * x := hxhI y hyI
    have hle : I ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [hIeq]
      refine sup_le (fun k hk => ?_) ?_
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff.mp hz]
        exact (hyK k hk).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff.mp hz]
        exact hyx.symm
    exact Subgroup.mem_centralizer_iff.mp (hle hu) y (Set.mem_singleton y)
  intro y hy u hu
  rw [hMgen] at hy
  have hle : conjBy h (J a₀ b₀ ⊔ Subgroup.zpowers x) ≤ Subgroup.centralizer (I : Set G) := by
    unfold conjBy
    rw [Subgroup.map_sup]
    refine sup_le (fun z hz => ?_) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hJ'I z hz v hv).symm
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have : (MulAut.conj h).toMonoidHom (x ^ k) = x' ^ k := by
        simp [MulAut.conj_apply, hx', conj_zpow]
      rw [this]
      exact (Commute.zpow_left (show Commute x' v from hx'I v hv) k).eq.symm
  exact (Subgroup.mem_centralizer_iff.mp (hle hy) u hu).symm

end CFSG.RankThree.PartOne.CTP

module

public import CFSG.RankThree.PartTwo.Sec13.K135D1cA
public import CFSG.RankThree.PartTwo.Sec13.K135D1cBC

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem r3_u_normalizes {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    (hno : ∀ A T : Subgroup N, CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 3 → T ≠ ⊥ →
      IsPGroup 2 T → ¬ A ≤ Subgroup.normalizer (T : Set N))
    (hmult : ∀ J : Subgroup N, CFSG.IsComponent J → ¬ p ∣ Nat.card (Subgroup.center J))
    (hdvd : ∀ J : Subgroup N, CFSG.IsComponent J → p ∣ Nat.card J)
    {Y : Subgroup N} (hY : Nat.card Y = p) (hYc : Y ≤ Subgroup.center N)
    {u : N} (hu2 : u * u = 1)
    {F Ū : Subgroup N} (hFexp : ∀ f ∈ F, f ^ p = 1) (hFu : ∀ f ∈ F, u * f = f * u)
    (hfix : ∀ J : Subgroup N, CFSG.IsComponent J → F ≤ Subgroup.normalizer (J : Set N))
    (hŪ2 : IsPGroup 2 Ū) (hŪF : F ≤ Subgroup.normalizer (Ū : Set N)) (hŪcomm : Ū ≤ ⁅Ū, F⁆)
    {J₀ : Subgroup N} (hJ₀ : CFSG.IsComponent J₀) (hŪJ : Ū ≤ Subgroup.normalizer (J₀ : Set N))
    (hŪnc : ¬ Ū ≤ Subgroup.centralizer (J₀ : Set N)) :
    u ∈ Subgroup.normalizer (J₀ : Set N) := by
  classical
  by_contra hu
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : J₀.map (MulAut.conj u).toMonoidHom ≠ J₀ := fun h =>
    hu (r3e_mem_normalizer_of_map_eq h)
  have hm₀ := hmult J₀ hJ₀
  refine r3_swap_false hp hno hY hYc hmult hJ₀ hne (hfix J₀ hJ₀) hŪJ hŪ2 hŪF hŪcomm hŪnc ?_
  intro f hf
  have hfJ : f ∈ Subgroup.normalizer (J₀ : Set N) := hfix J₀ hJ₀ hf
  let n : Subgroup.normalizer (J₀ : Set N) := ⟨f, hfJ⟩
  have hfb : (actS J₀ n) ^ p = 1 := by
    have hn : n ^ p = 1 := Subtype.ext (by simpa using hFexp f hf)
    rw [← map_pow, hn, map_one]
  have hSdvd : p ∣ Nat.card (↥J₀ ⧸ Subgroup.center ↥J₀) := by
    have h1 : Nat.card (↥J₀ ⧸ Subgroup.center ↥J₀) * Nat.card (Subgroup.center ↥J₀) =
        Nat.card ↥J₀ := by
      rw [← Subgroup.index_mul_card (Subgroup.center ↥J₀)]
      rfl
    exact (hp.dvd_mul.mp (h1 ▸ hdvd J₀ hJ₀)).resolve_right hm₀
  obtain ⟨s, hso, hfs⟩ := exists_fixed_orderOf_eq_prime hp hSdvd (actS J₀ n) hfb
  obtain ⟨x0, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨w', hwo', hfw'⟩ := exists_lift_fixed_orderOf_eq_prime hp hm₀
    (J₀.normalizerMonoidHom n) x0 hso hfs
  have hwJ : (w' : N) ∈ J₀ := w'.2
  have hwo : orderOf (w' : N) = p := by
    rw [Subgroup.orderOf_coe]
    exact hwo'
  have hfw : f * (w' : N) * f⁻¹ = (w' : N) := congrArg Subtype.val hfw'
  obtain ⟨hvo, huv, hYv, hvconj⟩ := r3_wDelta hp hJ₀ hu2 hne hm₀ hY hYc hwJ hwo
  have hcu : Commute u f := hFu f hf
  have hcw : Commute (w' : N) f := by
    show (w' : N) * f = f * (w' : N)
    calc (w' : N) * f = (f * (w' : N) * f⁻¹) * f := by rw [hfw]
      _ = f * (w' : N) := by group
  have hcv : Commute ((w' : N) * (u * (w' : N) * u⁻¹)) f :=
    hcw.mul_left ((hcu.mul_left hcw).mul_left hcu.inv_left)
  by_cases hfA : f ∈ Y ⊔ Subgroup.zpowers ((w' : N) * (u * (w' : N) * u⁻¹))
  ·
    have hYcomm : ∀ y ∈ Y, ∀ g ∈ Subgroup.zpowers ((w' : N) * (u * (w' : N) * u⁻¹)),
        y * g = g * y := fun y hy g _ => ((Subgroup.mem_center_iff.1 (hYc hy)) g).symm
    obtain ⟨y, hy, g, hg, hyg⟩ := r2a_mem_sup hYcomm hfA
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hwp : (w' : N) ^ p = 1 := by
      have := pow_orderOf_eq_one (w' : N)
      rwa [hwo] at this
    refine ⟨(w' : N) ^ k, zpow_mem hwJ k, ?_, ?_⟩
    · calc ((w' : N) ^ k) ^ p = ((w' : N) ^ p) ^ k := by
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
        _ = 1 := by rw [hwp, one_zpow]
    · intro j hj
      rw [← hyg]
      have hyc : ∀ z : N, y * z = z * y := fun z => ((Subgroup.mem_center_iff.1 (hYc hy)) z).symm
      have h1 : y * ((w' : N) * (u * (w' : N) * u⁻¹)) ^ k * j *
          (y * ((w' : N) * (u * (w' : N) * u⁻¹)) ^ k)⁻¹ =
          ((w' : N) * (u * (w' : N) * u⁻¹)) ^ k * j *
            (((w' : N) * (u * (w' : N) * u⁻¹)) ^ k)⁻¹ := by
        have e : y * ((w' : N) * (u * (w' : N) * u⁻¹)) ^ k * j *
            (y * ((w' : N) * (u * (w' : N) * u⁻¹)) ^ k)⁻¹ =
            y * (((w' : N) * (u * (w' : N) * u⁻¹)) ^ k * j *
              (((w' : N) * (u * (w' : N) * u⁻¹)) ^ k)⁻¹) * y⁻¹ := by group
        rw [e, hyc]
        group
      rw [h1]
      exact hvconj k j hj
  · exfalso
    obtain ⟨F', hF'el, hF'card, hF'eq⟩ := r3_cube_of_central_commuting hp hY hYc hvo
      (hFexp f hf) hcv.eq hYv hfA
    have hcen : ∀ g : N, u * g = g * u → g ∈ Subgroup.centralizer ({u} : Set N) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hg
    have hF'u : ∀ g ∈ F', u * g = g * u := by
      have hle : F' ≤ Subgroup.centralizer ({u} : Set N) := by
        rw [hF'eq]
        refine sup_le (sup_le ?_ ?_) ?_
        · intro y hy
          exact hcen y (Subgroup.mem_center_iff.mp (hYc hy) u)
        · exact Subgroup.zpowers_le.mpr (hcen _ huv)
        · exact Subgroup.zpowers_le.mpr (hcen _ (hFu f hf))
      intro g hg
      exact Subgroup.mem_centralizer_iff.mp (hle hg) u rfl
    have hF'N : F' ≤ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup N) : Set N) := by
      intro g hg
      have hgc : g ∈ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup N) : Set N) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        exact (Commute.zpow_left (show Commute u g from hF'u g hg) m).eq
      exact Subgroup.centralizer_le_normalizer _ hgc
    have hu1 : u ≠ 1 := fun h => hu (by rw [h]; exact one_mem _)
    have hZne : Subgroup.zpowers u ≠ ⊥ := fun h => hu1 (Subgroup.zpowers_eq_bot.mp h)
    have hu21 : u ^ 2 = 1 := by rw [pow_two]; exact hu2
    have hZ2 : IsPGroup 2 (Subgroup.zpowers u) := by
      intro g
      refine ⟨1, ?_⟩
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
      apply Subtype.ext
      simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu21, one_zpow]
    exact hno F' (Subgroup.zpowers u) hF'el hF'card hZne hZ2 hF'N

end CFSG.RankThree.PartTwo.Sec13.F135Last

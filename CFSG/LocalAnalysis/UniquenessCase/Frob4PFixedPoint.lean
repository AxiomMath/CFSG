module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem eq_one_of_commute_of_prime_card {P₀ : Subgroup G} {d y : G}
    (hcard : (Nat.card P₀).Prime) (hdc : d ∉ centralizer (P₀ : Set G))
    (hy : y ∈ P₀) (hcomm : y * d = d * y) : y = 1 := by
  let C : Subgroup P₀ := (Subgroup.centralizer ({d} : Set G)).subgroupOf P₀
  haveI : Fact (Nat.card P₀).Prime := ⟨hcard⟩
  have hC : C = ⊥ ∨ C = ⊤ := C.eq_bot_or_eq_top_of_prime_card
  have hyC : (⟨y, hy⟩ : P₀) ∈ C := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hcomm.symm
  rcases hC with hC | hC
  · rw [hC] at hyC
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hyC)
  · exfalso
    apply hdc
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhC : (⟨h, hh⟩ : P₀) ∈ C := by rw [hC]; exact Subgroup.mem_top _
    have hh' := Subgroup.mem_subgroupOf.mp hhC
    exact (Subgroup.mem_centralizer_iff.mp hh' d (Set.mem_singleton d)).symm

private theorem normalizer_le_normalizer_center_map (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer (((Subgroup.center T).map T.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg z hz
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
  have hgT : ∀ t : T, g * (t : G) * g⁻¹ ∈ T :=
    fun t => (Subgroup.mem_normalizer_iff.mp hg (t : G)).mp t.2
  let w' : T := ⟨g * (w : G) * g⁻¹, hgT w⟩
  have hw' : w' ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    have hgt : g⁻¹ * (t : G) * g ∈ T :=
      (Subgroup.mem_normalizer_iff.mp hg _).mpr (by
        rw [show g * (g⁻¹ * (t : G) * g) * g⁻¹ = (t : G) from by group]
        exact t.2)
    have hc := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hw) ⟨g⁻¹ * (t : G) * g, hgt⟩)
    simp only [Subgroup.coe_mul] at hc
    calc (t : G) * (g * (w : G) * g⁻¹)
        = g * ((g⁻¹ * (t : G) * g) * (w : G)) * g⁻¹ := by group
      _ = g * ((w : G) * (g⁻¹ * (t : G) * g)) * g⁻¹ := by rw [hc]
      _ = (g * (w : G) * g⁻¹) * (t : G) := by group
  exact Subgroup.mem_map.mpr ⟨w', hw', rfl⟩

theorem frob4P_exists_fixed_of_abelian {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    {V P₀ : Subgroup G} (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥) (hVab : IsMulCommutative V)
    (hP₀ : Nat.card P₀ = p) (hP₀V : P₀ ≤ normalizer (V : Set G))
    (hfix : ∀ y ∈ P₀, y ≠ 1 → ∀ v ∈ V, v * y = y * v → v = 1)
    {d : G} (hd : orderOf d = r) (hdV : d ∈ normalizer (V : Set G))
    (hdP : d ∈ normalizer (P₀ : Set G)) (hdc : d ∉ centralizer (P₀ : Set G)) :
    ∃ v ∈ V, v ≠ 1 ∧ v * d = d * v := by
  classical
  letI : CommGroup V := { (inferInstance : Group V) with
    mul_comm := fun a b => hVab.is_comm.comm a b }
  haveI : Fintype P₀ := Fintype.ofFinite _
  have hcardP : (Nat.card P₀).Prime := hP₀.symm ▸ hp
  by_contra hcon
  have hCV : ∀ v ∈ V, v * d = d * v → v = 1 := by
    intro v hv hcomm
    by_contra hv1
    exact hcon ⟨v, hv, hv1, hcomm⟩
  let H : Subgroup G := zpowers d
  haveI : Fintype H := Fintype.ofFinite _
  have hHV : H ≤ normalizer (V : Set G) := Subgroup.zpowers_le.mpr hdV
  have hHP : H ≤ normalizer (P₀ : Set G) := Subgroup.zpowers_le.mpr hdP
  let κ : P₀ →* MulAut V := V.normalizerMonoidHom.comp (Subgroup.inclusion hP₀V)
  let actH : H →* MulAut V := V.normalizerMonoidHom.comp (Subgroup.inclusion hHV)
  let normP : V → V := fun w => ∏ y : P₀, κ y w
  have hnormP : ∀ w : V, normP w = 1 := by
    intro w
    obtain ⟨z, hz1⟩ : ∃ z : P₀, z ≠ 1 := by
      have hnt : Nontrivial P₀ := by
        rw [← Finite.one_lt_card_iff_nontrivial, hP₀]
        exact hp.one_lt
      exact exists_ne 1
    have hfixz : κ z (normP w) = normP w := by
      show κ z (∏ y : P₀, κ y w) = ∏ y : P₀, κ y w
      rw [map_prod]
      exact Fintype.prod_bijective (fun y : P₀ => z * y) (Equiv.mulLeft z).bijective _ _
        (fun y => by rw [← MulAut.mul_apply, ← map_mul])
    have hcomm : (normP w : G) * (z : G) = (z : G) * (normP w : G) := by
      have h := congrArg Subtype.val hfixz
      simp only [κ, MonoidHom.comp_apply, Subgroup.coe_inclusion,
        Subgroup.normalizerMonoidHom_apply_apply_coe] at h
      have h' : (z : G) * (normP w : G) = (normP w : G) * (z : G) := by
        have h2 := congrArg (· * (z : G)) h
        simpa [mul_assoc] using h2
      exact h'.symm
    exact Subtype.ext (hfix z z.2 (fun hc => hz1 (Subtype.ext hc)) (normP w) (normP w).2 hcomm)
  have hC : ∀ h : H, h ≠ 1 → ∀ y ∈ P₀, y * (h : G) = (h : G) * y → y = 1 := by
    intro h hh1 y hy hcomm
    have hcardH : Nat.card H = r := by
      show Nat.card (zpowers d) = r
      rw [Nat.card_zpowers, hd]
    haveI : Fact r.Prime := ⟨hr⟩
    have hmem : (⟨d, Subgroup.mem_zpowers d⟩ : H) ∈ Subgroup.zpowers h :=
      mem_zpowers_of_prime_card hcardH hh1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hdn : (h : G) ^ n = d := by
      have := congrArg Subtype.val hn
      simpa using this
    have hdy : y * d = d * y := by
      have hh := Commute.zpow_right hcomm n
      rw [hdn] at hh
      exact hh
    exact eq_one_of_commute_of_prime_card hcardP hdc hy hdy
  have hmain : ∀ v : V, v ^ p = 1 := by
    intro v
    let F : H → P₀ → V := fun h y => κ y⁻¹ (actH h (κ y v))
    have hswap : (∏ h : H, ∏ y : P₀, F h y) = ∏ y : P₀, ∏ h : H, F h y :=
      Finset.prod_comm
    have h1case : (∏ y : P₀, F 1 y) = v ^ p := by
      have hy : ∀ y : P₀, F 1 y = v := by
        intro y
        show κ y⁻¹ (actH 1 (κ y v)) = v
        rw [map_one, MulAut.one_apply, map_inv, MulAut.inv_apply_self]
      calc (∏ y : P₀, F 1 y) = ∏ _y : P₀, v := Finset.prod_congr rfl (fun y _ => hy y)
        _ = v ^ p := by rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hP₀]
    have hother : ∀ h : H, h ≠ 1 → (∏ y : P₀, F h y) = 1 := by
      intro h hh1
      let ψf : P₀ → G := fun y => (y : G)⁻¹ * (h : G) * (y : G) * (h : G)⁻¹
      have hψmem : ∀ y : P₀, ψf y ∈ P₀ := by
        intro y
        have h1 : (y : G)⁻¹ ∈ P₀ := P₀.inv_mem y.2
        have h2 : (h : G) * (y : G) * (h : G)⁻¹ ∈ P₀ :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inclusion hHP h).2 (y : G)).mp y.2
        simpa only [ψf, mul_assoc] using P₀.mul_mem h1 h2
      let ψ : P₀ → P₀ := fun y => ⟨ψf y, hψmem y⟩
      have hψinj : Function.Injective ψ := by
        intro y₁ y₂ hy
        have hy' : ψf y₁ = ψf y₂ := by
          have := congrArg Subtype.val hy
          simpa only [ψ] using this
        have hkey : ((y₂ : G) * (y₁ : G)⁻¹) * (h : G) =
            (h : G) * ((y₂ : G) * (y₁ : G)⁻¹) := by
          have hh := hy'
          simp only [ψf] at hh
          calc ((y₂ : G) * (y₁ : G)⁻¹) * (h : G)
              = (y₂ : G) * ((y₁ : G)⁻¹ * (h : G) * (y₁ : G) * (h : G)⁻¹) *
                  (h : G) * (y₁ : G)⁻¹ := by group
            _ = (y₂ : G) * ((y₂ : G)⁻¹ * (h : G) * (y₂ : G) * (h : G)⁻¹) *
                  (h : G) * (y₁ : G)⁻¹ := by rw [hh]
            _ = (h : G) * ((y₂ : G) * (y₁ : G)⁻¹) := by group
        have hmem : (y₂ : G) * (y₁ : G)⁻¹ ∈ P₀ := P₀.mul_mem y₂.2 (P₀.inv_mem y₁.2)
        have h1 := hC h hh1 ((y₂ : G) * (y₁ : G)⁻¹) hmem hkey
        apply Subtype.ext
        have h2 : (y₂ : G) = (y₁ : G) := by
          have := congrArg (· * (y₁ : G)) h1
          simpa [mul_assoc] using this
        exact h2.symm
      have hF : ∀ y : P₀, F h y = κ (ψ y) (actH h v) := by
        intro y
        apply Subtype.ext
        simp only [F, ψ, ψf, κ, actH, MonoidHom.comp_apply, Subgroup.coe_inclusion,
          Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have hprod : (∏ y : P₀, F h y) = ∏ y : P₀, κ (ψ y) (actH h v) :=
        Finset.prod_congr rfl (fun y _ => hF y)
      rw [hprod]
      have hbij : (∏ y : P₀, κ (ψ y) (actH h v)) = ∏ z : P₀, κ z (actH h v) :=
        Fintype.prod_bijective ψ (Finite.injective_iff_bijective.mp hψinj) _ _ (fun _ => rfl)
      rw [hbij]
      exact hnormP (actH h v)
    have horder1 : (∏ h : H, ∏ y : P₀, F h y) = v ^ p := by
      rw [Finset.prod_eq_single (1 : H) (fun b _ hb => hother b hb)
        (fun h1 => absurd (Finset.mem_univ (1 : H)) h1)]
      exact h1case
    have horder2 : (∏ h : H, ∏ y : P₀, F h y) = 1 := by
      rw [hswap]
      refine Finset.prod_eq_one (fun y _ => ?_)
      have hinner : (∏ h : H, F h y) = κ y⁻¹ (∏ h : H, actH h (κ y v)) := by
        rw [← map_prod]
      rw [hinner]
      have hactH : ∀ (h : H) (x : V), ((actH h x : V) : G) =
          (h : G) * (x : G) * (h : G)⁻¹ :=
        fun h x => Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion hHV h) x
      have hnormH : (∏ h : H, actH h (κ y v)) = 1 := by
        have hcent : actH ⟨d, Subgroup.mem_zpowers d⟩ (∏ h : H, actH h (κ y v)) =
            ∏ h : H, actH h (κ y v) := by
          rw [map_prod]
          calc ∏ h : H, actH ⟨d, Subgroup.mem_zpowers d⟩ (actH h (κ y v))
              = ∏ h : H, actH ((⟨d, Subgroup.mem_zpowers d⟩ : H) * h) (κ y v) :=
                Finset.prod_congr rfl (fun h _ => by rw [← MulAut.mul_apply, ← map_mul])
            _ = ∏ h : H, actH h (κ y v) :=
                Fintype.prod_bijective (fun h : H => (⟨d, Subgroup.mem_zpowers d⟩ : H) * h)
                  (Equiv.mulLeft (⟨d, Subgroup.mem_zpowers d⟩ : H)).bijective _ _ (fun _ => rfl)
        have hcommG : (((∏ h : H, actH h (κ y v)) : V) : G) * d =
            d * (((∏ h : H, actH h (κ y v)) : V) : G) := by
          have h := congrArg Subtype.val hcent
          rw [hactH] at h
          have h' : (d : G) * (((∏ h : H, actH h (κ y v)) : V) : G) =
              (((∏ h : H, actH h (κ y v)) : V) : G) * d := by
            have h2 := congrArg (· * d) h
            simpa [mul_assoc] using h2
          exact h'.symm
        exact Subtype.ext (hCV _ (∏ h : H, actH h (κ y v)).2 hcommG)
      rw [hnormH, map_one]
    exact horder1.symm.trans horder2
  have hVbot : V = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hxp : x ^ p = 1 := by
      have := congrArg Subtype.val (hmain ⟨x, hx⟩)
      simpa using this
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hV) ⟨x, hx⟩
    have hk' : orderOf x = 2 ^ k := by rw [← Subgroup.orderOf_mk x hx, hk]
    have hdvdp : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
    have hdvd2 : orderOf x ∣ 2 ^ k := by rw [hk']
    have hcop : Nat.Coprime p (2 ^ k) := by
      have := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
      simpa using this.pow 1 k
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvdp hdvd2)
  exact hV1 hVbot

theorem frob4P_exists_fixed_of_frobenius {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    {T P₀ : Subgroup G} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hP₀ : Nat.card P₀ = p)
    (hP₀T : P₀ ≤ normalizer (T : Set G))
    (hfix : ∀ y ∈ P₀, y ≠ 1 → ∀ t ∈ T, t * y = y * t → t = 1)
    {d : G} (hd : orderOf d = r) (hdT : d ∈ normalizer (T : Set G))
    (hdP : d ∈ normalizer (P₀ : Set G)) (hdc : d ∉ centralizer (P₀ : Set G)) :
    ∃ t ∈ T, t ≠ 1 ∧ t * d = d * t := by
  classical
  let Z : Subgroup G := (Subgroup.center T).map T.subtype
  have hZT : Z ≤ T := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    exact w.2
  have hZ2 : IsPGroup 2 Z := hT.to_le hZT
  have hZab : IsMulCommutative Z := by
    have := Subgroup.map_isMulCommutative (H := Subgroup.center T) T.subtype
    simpa only [Z] using this
  have hZ1 : Z ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
    have hnt : Nontrivial (Subgroup.center T) := hT.center_nontrivial
    obtain ⟨w, hw⟩ := exists_ne (1 : Subgroup.center T)
    refine ⟨⟨(w : T), Subgroup.mem_map.mpr ⟨w, w.2, rfl⟩⟩, ?_⟩
    intro hcon
    apply hw
    have h1 : ((w : T) : G) = (1 : G) := by
      have := congrArg Subtype.val hcon
      simpa using this
    exact Subtype.ext (Subtype.ext h1)
  have hnormZT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Z : Set G) := by
    simpa only [Z] using normalizer_le_normalizer_center_map T
  have hP₀Z : P₀ ≤ normalizer (Z : Set G) := hP₀T.trans hnormZT
  have hfixZ : ∀ y ∈ P₀, y ≠ 1 → ∀ v ∈ Z, v * y = y * v → v = 1 :=
    fun y hy hy1 v hv hcomm => hfix y hy hy1 v (hZT hv) hcomm
  obtain ⟨v, hvZ, hv1, hvcomm⟩ :=
    frob4P_exists_fixed_of_abelian hp hp2 hr hZ2 hZ1 hZab hP₀ hP₀Z hfixZ hd (hnormZT hdT) hdP hdc
  exact ⟨v, hZT hvZ, hv1, hvcomm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

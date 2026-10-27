module

import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem isPerfect_alternatingGroup_six : Group.IsPerfect (alternatingGroup (Fin 6)) :=
  (Sec13.isPerfect_center_of_isSimpleGroup
    (alternatingGroup.isSimpleGroup (by simp)) (by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num [Nat.factorial])).1

theorem isPerfect_of_quot {K R : Subgroup G} (hRK : R ≤ K)
    (f : ↥K →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (hker : f.ker = R.subgroupOf K) (hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x)
    (hR2 : IsPGroup 2 R) {d e : G} (hdK : d ∈ K) (heK : e ∈ K) (hd3 : d ^ 3 = 1)
    (he3 : e ^ 3 = 1) (hde : d * e = e * d) (hdR : d ∈ Subgroup.normalizer (R : Set G))
    (heR : e ∈ Subgroup.normalizer (R : Set G))
    (hcent : ∀ x ∈ R, x * d = d * x → x * e = e * x → x = 1) : Group.IsPerfect ↥K := by
  rw [Group.isPerfect_def]
  set D := commutator ↥K with hD
  have hRD : R.subgroupOf K ≤ D := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    set x₀ : G := (x : G) with hx₀
    set y : G := x₀ * (d * x₀ * d⁻¹) * (d ^ 2 * x₀ * (d ^ 2)⁻¹) with hy
    set z : G := y * (e * y * e⁻¹) * (e ^ 2 * y * (e ^ 2)⁻¹) with hz
    have hconjR : ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ r ∈ R, g * r * g⁻¹ ∈ R :=
      fun g hg r hr => (Subgroup.mem_normalizer_iff.mp hg r).mp hr
    have hd2R : d ^ 2 ∈ Subgroup.normalizer (R : Set G) := pow_mem hdR 2
    have he2R : e ^ 2 ∈ Subgroup.normalizer (R : Set G) := pow_mem heR 2
    have hyR : y ∈ R := mul_mem (mul_mem hx (hconjR d hdR _ hx)) (hconjR _ hd2R _ hx)
    have hzR : z ∈ R := mul_mem (mul_mem hyR (hconjR e heR _ hyR)) (hconjR _ he2R _ hyR)
    have hyd : d * y * d⁻¹ = y := by
      have h1 : d * y * d⁻¹ = (d * x₀ * d⁻¹) * (d ^ 2 * x₀ * (d ^ 2)⁻¹) *
          (d ^ 3 * x₀ * (d ^ 3)⁻¹) := by
        rw [hy]
        group
      rw [h1, hd3, one_mul, inv_one, mul_one]
      have hx1 := hconjR d hdR _ hx
      have hx2 := hconjR _ hd2R _ hx
      rw [hy, hRc _ (mul_mem hx1 hx2) _ hx, ← mul_assoc]
    have hzd : d * z * d⁻¹ = z := by
      have hed : ∀ k : ℕ, d * (e ^ k * y * (e ^ k)⁻¹) * d⁻¹ = e ^ k * y * (e ^ k)⁻¹ := by
        intro k
        have hc : Commute d (e ^ k) := Commute.pow_right hde k
        calc d * (e ^ k * y * (e ^ k)⁻¹) * d⁻¹
            = e ^ k * (d * y * d⁻¹) * (e ^ k)⁻¹ := by
              rw [show d * (e ^ k * y * (e ^ k)⁻¹) * d⁻¹ =
                (d * e ^ k) * y * (d * e ^ k)⁻¹ by group, hc.eq]
              group
          _ = e ^ k * y * (e ^ k)⁻¹ := by rw [hyd]
      have he1 := hed 1
      have he2 := hed 2
      rw [pow_one] at he1
      calc d * z * d⁻¹ = (d * y * d⁻¹) * (d * (e * y * e⁻¹) * d⁻¹) *
            (d * (e ^ 2 * y * (e ^ 2)⁻¹) * d⁻¹) := by rw [hz]; group
        _ = z := by rw [hyd, he1, he2]
    have hze : e * z * e⁻¹ = z := by
      have h1 : e * z * e⁻¹ = (e * y * e⁻¹) * (e ^ 2 * y * (e ^ 2)⁻¹) *
          (e ^ 3 * y * (e ^ 3)⁻¹) := by
        rw [hz]
        group
      rw [h1, he3, one_mul, inv_one, mul_one]
      have hy1 := hconjR e heR _ hyR
      have hy2 := hconjR _ he2R _ hyR
      rw [hz, hRc _ (mul_mem hy1 hy2) _ hyR, ← mul_assoc]
    have hcomm_of : ∀ {g w : G}, g * w * g⁻¹ = w → w * g = g * w := fun {g w} hgw => by
      calc w * g = (g * w * g⁻¹) * g := by rw [hgw]
        _ = g * w := by group
    have hz1 : z = 1 := hcent z hzR (hcomm_of hzd) (hcomm_of hze)
    set φ := Abelianization.of (G := ↥K)
    set δ : ↥K := ⟨d, hdK⟩
    set ε : ↥K := ⟨e, heK⟩
    have hφc : ∀ g u : ↥K, φ (g * u * g⁻¹) = φ u := fun g u => by
      rw [map_mul, map_mul, map_inv, mul_comm (φ g), mul_assoc, mul_inv_cancel, mul_one]
    set y' : ↥K := x * (δ * x * δ⁻¹) * (δ ^ 2 * x * (δ ^ 2)⁻¹) with hy'
    set z' : ↥K := y' * (ε * y' * ε⁻¹) * (ε ^ 2 * y' * (ε ^ 2)⁻¹) with hz'
    have hzz : (z' : G) = z := rfl
    have hz'1 : z' = 1 := Subtype.ext (by rw [hzz, hz1]; rfl)
    have hφy : φ y' = φ x ^ 3 := by
      rw [hy', map_mul, map_mul, hφc, hφc, pow_succ, pow_two]
    have hφz : φ z' = φ x ^ 9 := by
      rw [hz', map_mul, map_mul, hφc, hφc, hφy, ← pow_add, ← pow_add]
    rw [hz'1, map_one] at hφz
    obtain ⟨k, hk⟩ := hR2 ⟨x₀, hx⟩
    have hxk : φ x ^ (2 ^ k) = 1 := by
      have : x ^ (2 ^ k) = 1 := Subtype.ext (by
        have := congrArg Subtype.val hk
        simpa using this)
      rw [← map_pow, this, map_one]
    have hord : orderOf (φ x) = 1 := by
      have h1 := orderOf_dvd_of_pow_eq_one hφz.symm
      have h2 := orderOf_dvd_of_pow_eq_one hxk
      have hcop : Nat.Coprime 9 (2 ^ k) :=
        Nat.Coprime.pow_right _ (by norm_num)
      exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
    rw [orderOf_eq_one_iff] at hord
    rw [hD, ← Abelianization.ker_of]
    exact hord
  rw [eq_top_iff]
  intro k _
  have hfD : (D.map f) = ⊤ := by
    rw [hD, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hf]
    exact (Group.isPerfect_def.mp isPerfect_alternatingGroup_six)
  obtain ⟨δ, hδ, hδk⟩ : f k ∈ D.map f := hfD ▸ Subgroup.mem_top (f k)
  have hker' : δ⁻¹ * k ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hδk, inv_mul_cancel]
  have : k = δ * (δ⁻¹ * k) := by group
  rw [this]
  exact mul_mem hδ (hRD (hker ▸ hker'))

theorem conj_mem_of_quot {K R : Subgroup G} (f : ↥K →* alternatingGroup (Fin 6))
    (hker : f.ker = R.subgroupOf K) {k r : G} (hk : k ∈ K) (hr : r ∈ R) (hrK : r ∈ K) :
    k * r * k⁻¹ ∈ R := by
  have hmem : (⟨r, hrK⟩ : ↥K) ∈ f.ker := hker ▸ Subgroup.mem_subgroupOf.mpr hr
  have h1 : (⟨k, hk⟩ : ↥K) * ⟨r, hrK⟩ * ⟨k, hk⟩⁻¹ ∈ f.ker :=
    (inferInstance : f.ker.Normal).conj_mem _ hmem _
  rw [hker, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem cent_le_of_quot {K R B : Subgroup G} (hRK : R ≤ K)
    (f : ↥K →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (hker : f.ker = R.subgroupOf K) (hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (hR1 : R ≠ ⊥)
    (hBK : B ≤ K) (hBR : R ⊓ Subgroup.centralizer (B : Set G) = ⊥) :
    K ⊓ Subgroup.centralizer (R : Set G) ≤ R := by
  set C : Subgroup ↥K := (K ⊓ Subgroup.centralizer (R : Set G)).subgroupOf K with hC
  have hCn : C.Normal := by
    refine ⟨fun x hx k => ?_⟩
    rw [hC, Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨(k * x * k⁻¹).2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro r hr
    have hr' : (k : G)⁻¹ * r * k ∈ R := by
      have := conj_mem_of_quot f hker (inv_mem k.2) hr (hRK hr)
      simpa using this
    have hx' := Subgroup.mem_centralizer_iff.mp hx.2 _ hr'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc r * (↑k * ↑x * (↑k)⁻¹) = ↑k * (((↑k)⁻¹ * r * ↑k) * ↑x) * (↑k)⁻¹ := by group
      _ = ↑k * (↑x * ((↑k)⁻¹ * r * ↑k)) * (↑k)⁻¹ := by rw [hx']
      _ = ↑k * ↑x * (↑k)⁻¹ * r := by group
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases (hCn.map f hf).eq_bot_or_eq_top with h0 | htop
  · intro x hx
    have hxC : (⟨x, hx.1⟩ : ↥K) ∈ C := Subgroup.mem_subgroupOf.mpr hx
    have : (⟨x, hx.1⟩ : ↥K) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      have := Subgroup.mem_map_of_mem f hxC
      rw [h0, Subgroup.mem_bot] at this
      exact this
    rw [hker, Subgroup.mem_subgroupOf] at this
    exact this
  · exfalso
    apply hR1
    rw [eq_bot_iff, ← hBR]
    intro r hr
    refine ⟨hr, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    obtain ⟨x, hxC, hxb⟩ : f ⟨b, hBK hb⟩ ∈ C.map f := htop ▸ Subgroup.mem_top _
    have hk : x⁻¹ * ⟨b, hBK hb⟩ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxb, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hk
    have hxR := (Subgroup.mem_subgroupOf.mp hxC).2
    have e1 : ((x : G)⁻¹ * b) * r = r * ((x : G)⁻¹ * b) := (hRc _ hk _ hr)
    have e2 : (x : G) * r = r * x := (Subgroup.mem_centralizer_iff.mp hxR r hr).symm
    calc b * r = (x : G) * (((x : G)⁻¹ * b) * r) := by group
      _ = (x : G) * (r * ((x : G)⁻¹ * b)) := by rw [e1]
      _ = ((x : G) * r) * ((x : G)⁻¹ * b) := by group
      _ = (r * x) * ((x : G)⁻¹ * b) := by rw [e2]
      _ = r * b := by group

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S

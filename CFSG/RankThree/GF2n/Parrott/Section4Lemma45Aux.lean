module

public import CFSG.GroupTheory.InvolutionFixedPointFree
public import CFSG.RankThree.GF2n.Parrott.Section1
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42Steps

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem pPrimeCore_inf_H_eq_bot (h : Tim79a.ParrottHyp z) : pPrimeCore 2 G ⊓ H z = ⊥ := by
  have hKn : (pPrimeCore 2 G).Normal := pPrimeCore_normal
  have hcop : Nat.Coprime (Nat.card (J z)) (Nat.card (pPrimeCore 2 G)) := by
    rw [card_J h]
    exact (pPrimeCore_coprime_card (p := 2) (G := G)).pow_left 10
  have hKJ : pPrimeCore 2 G ⊓ J z = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop.symm
  have hHN : H z ≤ normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  rw [eq_bot_iff]
  intro m hm
  rw [Subgroup.mem_bot]
  have hmJ : m ∈ Subgroup.centralizer (J z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hc : m * x * m⁻¹ * x⁻¹ ∈ pPrimeCore 2 G ⊓ J z := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h1 : x * m⁻¹ * x⁻¹ ∈ pPrimeCore 2 G := hKn.conj_mem _ (inv_mem hm.1) x
        have := Subgroup.mul_mem _ hm.1 h1
        simpa [mul_assoc] using this
      · exact Subgroup.mul_mem _ ((mem_normalizer_iff.mp (hHN hm.2) x).mp hx) (inv_mem hx)
    rw [hKJ, Subgroup.mem_bot] at hc
    have h2 : m * x = x * m := by
      calc m * x = m * x * m⁻¹ * x⁻¹ * x * m := by group
        _ = x * m := by rw [hc]; group
    exact h2.symm
  have hmJ' : m ∈ J z := h.2.2.2.1 (Subgroup.mem_inf.mpr ⟨hm.2, hmJ⟩)
  have : m ∈ pPrimeCore 2 G ⊓ J z := Subgroup.mem_inf.mpr ⟨hm.1, hmJ'⟩
  rwa [hKJ, Subgroup.mem_bot] at this

theorem eq_centralizer_sup_pPrimeCore_of_weakly_closed {T : Subgroup G} (hT : IsSylowOf 2 T ⊤)
    {x : G} (hx : orderOf x = 2) (hxT : x ∈ T)
    (hwc : ∀ g : G, g * x * g⁻¹ ∈ T → g * x * g⁻¹ = x) :
    centralizer ({x} : Set G) ⊔ pPrimeCore 2 G = ⊤ := by
  have hx2 : x * x = 1 := by
    have h1 := pow_orderOf_eq_one x
    rwa [hx, pow_two] at h1
  refine prop2_eq_centralizer_mul_oddCore hx ?_
  intro g hcomm
  have hy2 : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
    calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hxy : Commute x (g * x * g⁻¹) := hcomm.symm
  have hcm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers (g * x * g⁻¹), Commute a b := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (hxy.zpow_left i).zpow_right k
  have hA : IsPGroup 2 (Subgroup.zpowers x ⊔ Subgroup.zpowers (g * x * g⁻¹) : Subgroup G) := by
    intro a
    refine ⟨1, ?_⟩
    obtain ⟨u, hu, v, hv, huv⟩ := (CFSG.mem_sup_of_commute hcm).mp a.2
    have hu2 : u * u = 1 := by
      rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hx hu with rfl | rfl
      · exact one_mul 1
      · exact hx2
    have hv2 : v * v = 1 := by
      have hxy2 : orderOf (g * x * g⁻¹) = 2 := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
        exact hx
      rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hxy2 hv with rfl | rfl
      · exact one_mul 1
      · exact hy2
    have hc : Commute u v := hcm u hu v hv
    have hsq : (a : G) * (a : G) = 1 := by
      calc (a : G) * (a : G) = (u * v) * (u * v) := by rw [← huv]
        _ = u * (v * u) * v := by group
        _ = u * (u * v) * v := by rw [← hc.eq]
        _ = u * u * (v * v) := by group
        _ = 1 := by rw [hu2, hv2, one_mul]
    apply Subtype.ext
    simpa [pow_two] using hsq
  obtain ⟨Q, hQ⟩ := hA.exists_le_sylow
  have hQs : IsSylowOf 2 (Q : Subgroup G) ⊤ := by
    rw [isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, Q.isPGroup', Q.not_dvd_index⟩
  obtain ⟨k, -, hk⟩ := hT.exists_mem_conj hQs
  have hxQ : x ∈ (Q : Subgroup G) := hQ (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have hyQ : g * x * g⁻¹ ∈ (Q : Subgroup G) :=
    hQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have h1 : k⁻¹ * x * k ∈ T := (hk x).mp hxQ
  have h2 : k⁻¹ * (g * x * g⁻¹) * k ∈ T := (hk _).mp hyQ
  have h1' : k⁻¹ * x * k = x := by
    have := hwc k⁻¹ (by simpa using h1)
    simpa using this
  have h2' : (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ = x := hwc (k⁻¹ * g) (by
    have : (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * x * g⁻¹) * k := by group
    rw [this]
    exact h2)
  calc g * x * g⁻¹ = k * ((k⁻¹ * g) * x * (k⁻¹ * g)⁻¹) * k⁻¹ := by group
    _ = k * x * k⁻¹ := by rw [h2']
    _ = k * (k⁻¹ * x * k) * k⁻¹ := by rw [h1']
    _ = x := by group

theorem pPrimeCore_eq_bot_of_fusion (h : Tim79a.ParrottHyp z) {t' j₀ : G}
    (ht' : orderOf t' = 2) (hzt' : IsConj z t') (hj₀ : j₀ ∈ J z) (hj₀c : j₀ ∉ centerIn (J z))
    (hconj : IsConj (t' * z) j₀) : pPrimeCore 2 G = ⊥ := by
  have hKn : (pPrimeCore 2 G).Normal := pPrimeCore_normal
  have hz2 : z * z = 1 := by
    have h1 := pow_orderOf_eq_one z
    rwa [h.1, pow_two] at h1
  have ht2 : t' * t' = 1 := by
    have h1 := pow_orderOf_eq_one t'
    rwa [ht', pow_two] at h1
  have hfix : pPrimeCore 2 G ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := pPrimeCore_inf_H_eq_bot h
  have h1 : t' * z ∈ Subgroup.centralizer ((pPrimeCore 2 G : Subgroup G) : Set G) :=
    mul_mem_centralizer_of_isConj_of_inf_centralizer_eq_bot hz2 ht2 hzt' hfix
  have hconjK : ∀ (a c : G), a ∈ Subgroup.centralizer ((pPrimeCore 2 G : Subgroup G) : Set G) →
      c * a * c⁻¹ ∈ Subgroup.centralizer ((pPrimeCore 2 G : Subgroup G) : Set G) := by
    intro a c ha
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : c⁻¹ * k * c ∈ pPrimeCore 2 G := by
      simpa using hKn.conj_mem k hk c⁻¹
    have hcomm := Subgroup.mem_centralizer_iff.mp ha _ hk'
    calc k * (c * a * c⁻¹) = c * ((c⁻¹ * k * c) * a) * c⁻¹ := by group
      _ = c * (a * (c⁻¹ * k * c)) * c⁻¹ := by rw [hcomm]
      _ = c * a * c⁻¹ * k := by group
  have h2 : j₀ ∈ Subgroup.centralizer ((pPrimeCore 2 G : Subgroup G) : Set G) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← hg]
    exact hconjK _ g h1
  have hj₀noc : ¬ j₀ ∈ Subgroup.centralizer (J z : Set G) := fun hc =>
    hj₀c (Subgroup.mem_inf.mpr ⟨hj₀, hc⟩)
  rw [Subgroup.mem_centralizer_iff] at hj₀noc
  push Not at hj₀noc
  obtain ⟨x, hxJ, hx⟩ := hj₀noc
  have hcomm : ⁅x, j₀⁆ ∈ Subgroup.zpowers z := by
    have h3 : ⁅x, j₀⁆ ∈ ⁅J z, J z⁆ := Subgroup.commutator_mem_commutator hxJ hj₀
    have h4 : ⁅J z, J z⁆ = Subgroup.zpowers z := h.2.2.1
    rwa [h4] at h3
  have hcz : ⁅x, j₀⁆ = z := by
    rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two h.1 hcomm with h5 | h5
    · exfalso
      apply hx
      have h6 : x * j₀ * x⁻¹ * j₀⁻¹ = 1 := h5
      calc x * j₀ = (x * j₀ * x⁻¹ * j₀⁻¹) * (j₀ * x) := by group
        _ = j₀ * x := by rw [h6, one_mul]
    · exact h5
  have hjz : j₀ * z = z * j₀ :=
    Subgroup.mem_centralizer_iff.mp (z_mem_centerIn_J h).2 j₀ hj₀
  have hxj : x * j₀ * x⁻¹ = j₀ * z := by
    have h6 : x * j₀ * x⁻¹ * j₀⁻¹ = z := hcz
    calc x * j₀ * x⁻¹ = (x * j₀ * x⁻¹ * j₀⁻¹) * j₀ := by group
      _ = z * j₀ := by rw [h6]
      _ = j₀ * z := hjz.symm
  have h3 : j₀ * z ∈ Subgroup.centralizer ((pPrimeCore 2 G : Subgroup G) : Set G) :=
    hxj ▸ hconjK j₀ x h2
  have h4 : z ∈ Subgroup.centralizer ((pPrimeCore 2 G : Subgroup G) : Set G) := by
    have h5 := Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) h3
    have h6 : j₀⁻¹ * (j₀ * z) = z := by group
    rwa [h6] at h5
  rw [eq_bot_iff]
  intro k hk
  have hkz : k ∈ pPrimeCore 2 G ⊓ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hk, mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp h4 k hk)⟩
  rwa [hfix, Subgroup.mem_bot] at hkz

end CFSG.RankThree.GF2n.Parrott

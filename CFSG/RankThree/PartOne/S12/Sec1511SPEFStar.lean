module

public import CFSG.RankThree.PartOne.S12.Sec12FusChoice
public import CFSG.RankThree.PartOne.CTP.StrongPGlue
public import CFSG.RankThree.PartOne.KLR.NoninnerAux

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LocalCores StrongP

namespace Sec1511

variable {H : Type} [Group H] [Finite H]

theorem pCore_eq_bot_of_spe {p : ℕ} (hp : p.Prime) {Y : Subgroup H}
    (hY : IsStronglyPEmbedded p Y) : pCore p H = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  obtain ⟨P, hP, hRP⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) (le_top : pCore p H ≤ ⊤)
    (pCore_isPGroup (G := H) (p := p))
  obtain ⟨g, hg⟩ := hY.exists_conj_ge hP
  have hn : Subgroup.normalizer ((pCore p H : Subgroup H) : Set H) ≤ conjSub g Y :=
    (hY.conj g).normalizer_le hne (pCore_isPGroup (G := H) (p := p)) (hRP.trans hg)
  rw [Subgroup.normalizer_eq_top] at hn
  exact (hY.conj g).1 (top_le_iff.1 hn)

theorem le_pPrimeCore_of_isSubnormal_p {p : ℕ} [Fact p.Prime] {N : Subgroup H} (hN : N.IsSubnormal)
    (hcop : Nat.Coprime p (Nat.card N)) : N ≤ pPrimeCore p H := by
  have htop : pPrimeCore p N = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩)
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val ≠ p} hN
  rw [← pPrimeCore_eq_piCore, ← pPrimeCore_eq_piCore, htop, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact inf_eq_left.mp h.symm

theorem p_dvd_card_component {p : ℕ} [Fact p.Prime] (hO : pPrimeCore p H = ⊥) {K : Subgroup H}
    (hK : IsComponent K) : p ∣ Nat.card K := by
  by_contra h
  have hcop : Nat.Coprime p (Nat.card K) := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 h
  have hle := le_pPrimeCore_of_isSubnormal_p hK.2 hcop
  rw [hO] at hle
  have hK1 : K = ⊥ := le_bot_iff.1 hle
  have hnt : Nontrivial K := isQuasisimple_nontrivial hK.1
  exact (Subgroup.nontrivial_iff_ne_bot K).1 hnt hK1

theorem exists_pElement_component {p : ℕ} [Fact p.Prime] (hO : pPrimeCore p H = ⊥) {K : Subgroup H}
    (hK : IsComponent K) : ∃ a ∈ K, a ^ p = 1 ∧ a ≠ 1 := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) p (p_dvd_card_component hO hK)
  refine ⟨x, x.2, ?_, ?_⟩
  · have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  · intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact (Fact.out : p.Prime).one_lt.ne hx

theorem components_unique {p : ℕ} (hp : p.Prime) (hO : pPrimeCore p H = ⊥) {Y₀ : Subgroup H}
    (hY : IsStronglyPEmbedded p Y₀) {K₁ K₂ : Subgroup H} (h₁ : IsComponent K₁)
    (h₂ : IsComponent K₂) : K₁ = K₂ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have hcomm : ⁅K₁, K₂⁆ = ⊥ := (distinct_components_commute h₁ h₂).resolve_left hne
  have hK₁K₂ : K₁ ≤ Subgroup.centralizer (K₂ : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  obtain ⟨a, haK, hap, ha1⟩ := exists_pElement_component hO h₁
  obtain ⟨b, hbK, hbp, hb1⟩ := exists_pElement_component hO h₂
  have hab : ∀ k ∈ K₂, k * a = a * k := fun k hk =>
    (Subgroup.mem_centralizer_iff.1 (hK₁K₂ haK) k hk)
  have hba : ∀ k ∈ K₁, k * b = b * k := fun k hk =>
    (Subgroup.mem_centralizer_iff.1 (hK₁K₂ hk) b hbK).symm
  have hK₂K₁ : K₂ ≤ Subgroup.centralizer (K₁ : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [Subgroup.commutator_comm]; exact hcomm)
  have hUel : IsElementaryAbelian p ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
    have h1 := IsElementaryAbelian.zpowers_of_pow_eq_one hap
    have h2 := IsElementaryAbelian.zpowers_of_pow_eq_one hbp
    refine IsElementaryAbelian.sup_of_le_centralizer (E := Subgroup.zpowers a)
      (C := Subgroup.zpowers b) ?_
    exact ((Subgroup.zpowers_le.2 hbK).trans hK₂K₁).trans
      (Subgroup.centralizer_le (by exact_mod_cast (Subgroup.zpowers_le.2 haK)))
  have hlayerC : (layer H).Characteristic := layer_characteristic (G := H)
  have hlayerN : (layer H).Normal := inferInstance
  have hUle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ layer H :=
    sup_le (Subgroup.zpowers_le.2 (component_le_layer h₁ haK))
      (Subgroup.zpowers_le.2 (component_le_layer h₂ hbK))
  obtain ⟨R, hR, hUR⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hUle
    (IsElementaryAbelian.isPGroup p _)
  obtain ⟨P, hP, hRP⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) (le_top : R ≤ ⊤) hR.2.1
  obtain ⟨g, hg⟩ := hY.exists_conj_ge hP
  have hYs : IsStronglyPEmbedded p (conjSub g Y₀) := hY.conj g
  have haY : a ∈ conjSub g Y₀ := hg (hRP (hUR (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))))
  have hbY : b ∈ conjSub g Y₀ := hg (hRP (hUR (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))))
  have hK₁Y : K₁ ≤ conjSub g Y₀ := fun k hk =>
    hYs.centralizer_le hb1 hbp hbY (Subgroup.mem_centralizer_singleton_iff.2 (hba k hk))
  have hlayerY : layer H ≤ conjSub g Y₀ := by
    refine sSup_le fun L hL => ?_
    by_cases hLK : K₁ = L
    · rw [← hLK]; exact hK₁Y
    · have hc : ⁅K₁, L⁆ = ⊥ := (distinct_components_commute h₁ hL).resolve_left hLK
      have hKL : K₁ ≤ Subgroup.centralizer (L : Set H) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
      intro l hl
      exact hYs.centralizer_le ha1 hap haY (Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (hKL haK) l hl))
  have hR1 : R ≠ ⊥ := fun h => ha1 (by
    have : a ∈ R := hUR (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have hNY : Subgroup.normalizer (R : Set H) ≤ conjSub g Y₀ :=
    hYs.normalizer_le hR1 hR.2.1 (hRP.trans hg)
  have hRp' : IsPGroup p ↥(R.subgroupOf (layer H)) :=
    hR.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hR.1).symm
  let Q : Sylow p ↥(layer H) := hRp'.toSylow (by simpa [Subgroup.relIndex] using hR.2.2)
  have hfr := Sylow.normalizer_sup_eq_top Q
  have hQR : (Q : Subgroup ↥(layer H)).map (layer H).subtype = R :=
    Subgroup.map_subgroupOf_eq_of_le hR.1
  have hfr' : Subgroup.normalizer (R : Set H) ⊔ layer H = ⊤ := by
    rw [← hQR]
    exact hfr
  exact hYs.1 (top_le_iff.1 (hfr' ▸ sup_le hNY hlayerY))

omit [Finite H] in
theorem center_normal_of_normal {K : Subgroup H} [K.Normal] :
    ((Subgroup.center ↥K).map K.subtype).Normal := by
  refine ⟨fun z hz g => ?_⟩
  obtain ⟨z', hz', rfl⟩ := hz
  have hgz : g * (z' : H) * g⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem _ z'.2 g
  refine ⟨⟨g * (z' : H) * g⁻¹, hgz⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro k
  apply Subtype.ext
  have hk : g⁻¹ * (k : H) * g ∈ K := by
    have := (inferInstance : K.Normal).conj_mem _ k.2 g⁻¹
    simpa using this
  have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz' ⟨g⁻¹ * (k : H) * g, hk⟩)
  show (k : H) * (g * (z' : H) * g⁻¹) = g * (z' : H) * g⁻¹ * (k : H)
  have h2 : g⁻¹ * (k : H) * g * (z' : H) = (z' : H) * (g⁻¹ * (k : H) * g) := h1
  calc (k : H) * (g * (z' : H) * g⁻¹) = g * (g⁻¹ * (k : H) * g * (z' : H)) * g⁻¹ := by group
    _ = g * ((z' : H) * (g⁻¹ * (k : H) * g)) * g⁻¹ := by rw [h2]
    _ = g * (z' : H) * g⁻¹ * (k : H) := by group

theorem spe_fstar {p : ℕ} (hp : p.Prime) (hO : pPrimeCore p H = ⊥) {Y₀ : Subgroup H}
    (hY : IsStronglyPEmbedded p Y₀) :
    IsSimpleGroup ↥(generalizedFitting H) ∧ (∃ a b : ↥(generalizedFitting H), a * b ≠ b * a) ∧
      (generalizedFitting H).Normal ∧
      Subgroup.centralizer ((generalizedFitting H : Subgroup H) : Set H) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hF : fittingSubgroup H = ⊥ := by
    rw [Fitting_eq_pcore H p hO]
    exact pCore_eq_bot_of_spe hp hY
  have hex : ∃ K : Subgroup H, IsComponent K := by
    by_contra h
    push Not at h
    have hl : layer H = ⊥ := layer_eq_bot_of_forall h
    have hFs : generalizedFitting H = ⊥ := by rw [generalizedFitting, hF, hl]; exact bot_sup_eq _
    have hle := centralizer_generalizedFitting_le H
    rw [hFs] at hle
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y₀) p hY.2.1
    have hx1 : (x : H) ≠ 1 := by
      intro h1
      have : x = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hx
      exact hp.one_lt.ne hx
    apply hx1
    have hmem : (x : H) ∈ Subgroup.centralizer (((⊥ : Subgroup H) : Subgroup H) : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have : h = 1 := hh
      rw [this]; simp
    have := hle hmem
    rwa [Subgroup.mem_bot] at this
  obtain ⟨K, hK⟩ := hex
  have hKall : ∀ L : Subgroup H, IsComponent L → L = K := fun L hL =>
    components_unique hp hO hY hL hK
  have hlayer : layer H = K := by
    apply le_antisymm
    · exact sSup_le fun L hL => (hKall L hL).le
    · exact component_le_layer hK
  have hFS : generalizedFitting H = K := by
    rw [generalizedFitting, hF, hlayer]
    exact bot_sup_eq _
  have hKC : K.Characteristic := hlayer ▸ layer_characteristic (G := H)
  have hKN : K.Normal := inferInstance
  have hZ : Subgroup.center ↥K = ⊥ := by
    have hZn := center_normal_of_normal (K := K)
    have hZcomm : IsMulCommutative ↥((Subgroup.center ↥K).map K.subtype) := by
      refine ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      show (a : H) * b = b * a
      rw [← ha, ← hb]
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 ha' b')).symm
    have hZnil : Group.IsNilpotent ↥((Subgroup.center ↥K).map K.subtype) := inferInstance
    have hle := (fitting_characteristic (G := H)).2.2 _ hZn hZnil
    rw [hF] at hle
    rw [eq_bot_iff]
    intro z hz
    have : (z : H) ∈ (Subgroup.center ↥K).map K.subtype := ⟨z, hz, rfl⟩
    have h1 := hle this
    rw [Subgroup.mem_bot] at h1 ⊢
    exact Subtype.ext h1
  obtain ⟨-, hsimple, a, b, hab⟩ := hK.1
  have e : ↥K ⧸ (Subgroup.center ↥K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hKsimple : IsSimpleGroup ↥K := by
    have := hsimple
    exact e.symm.isSimpleGroup
  have hKnonab : ∃ x y : ↥K, x * y ≠ y * x := by
    refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
    simpa [map_mul] using h
  have hcent : Subgroup.centralizer ((generalizedFitting H : Subgroup H) : Set H) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    refine KLR.eq_one_of_centralizes_generalizedFitting ?_ ?_ (fun f hf => ?_)
    · rw [hFS]; exact hKsimple
    · rw [hFS]
      rintro ⟨⟨h⟩⟩
      obtain ⟨x, y, hxy⟩ := hKnonab
      exact hxy (h x y)
    · exact (Subgroup.mem_centralizer_iff.1 hz f hf).symm
  refine ⟨?_, ?_, generalized_fitting_characteristic.2, hcent⟩
  · rw [hFS]; exact hKsimple
  · rw [hFS]; exact hKnonab

end Sec1511

end CFSG.RankThree.PartOne

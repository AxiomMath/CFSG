module

public import CFSG.RankThree.GF2n.Tim79a34QaFacts

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open CFSG.LargeExtraspecial.Timmesfeld (Qa fStar)

variable {G : Type} [Group G] [Finite G]

theorem qpCfg_psi_mul_self {V H : Subgroup G} {n : ℕ}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    (w : Fin n ⊕ Fin n → GaloisField 2 1) :
    ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) * ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) =
      1 := by
  have hw : w + w = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (w i)
  have h : (Additive.toMul (ψ w) : ↥(wOf V H)) * Additive.toMul (ψ w) = 1 := by
    change Additive.toMul (ψ w + ψ w) = 1
    rw [← map_add, hw, map_zero]
    rfl
  exact congrArg Subtype.val h

theorem qpCfg_exists_conj_psi {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (cfg : QPCfg M V Q P H Φ ψ a T) {w : Fin n ⊕ Fin n → GaloisField 2 1} (hw : w ≠ 0) :
    ∃ x : G, x * cfg.aG * x⁻¹ = ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) := by
  have hVH : V ≤ H := cfg.hyp.setup.mc.toMinCex.V_le_H
  obtain ⟨g, hg⟩ := exists_mat_mulVec_eq_of_ne_zero cfg.ne hw
  obtain ⟨x, hx⟩ := xToXbar_surjective hVH (Φ g)
  have hgx : Φ.symm (xToXbar hVH x) = g := by
    rw [hx, MulEquiv.symm_apply_apply]
  have key := cfg.nat.equiv x a
  rw [hgx, hg] at key
  exact ⟨(x : G), key.symm⟩

theorem fixedPoint_free_involution_inverts {N : Subgroup G} (hN : N.Normal) {t : G}
    (ht : t * t = 1) (hfix : ∀ m ∈ N, t * m * t⁻¹ = m → m = 1) :
    ∀ y ∈ N, t * y * t⁻¹ = y⁻¹ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let f : N → N := fun z =>
    ⟨(z : G)⁻¹ * (t * (z : G) * t⁻¹), N.mul_mem (N.inv_mem z.2) (hN.conj_mem _ z.2 t)⟩
  have hinj : Function.Injective f := by
    intro z₁ z₂ h
    have h' : (z₁ : G)⁻¹ * (t * (z₁ : G) * t⁻¹) = (z₂ : G)⁻¹ * (t * (z₂ : G) * t⁻¹) :=
      congrArg Subtype.val h
    have hm : t * ((z₁ : G) * (z₂ : G)⁻¹) * t⁻¹ = (z₁ : G) * (z₂ : G)⁻¹ := by
      calc t * ((z₁ : G) * (z₂ : G)⁻¹) * t⁻¹
          = (t * (z₁ : G) * t⁻¹) * (t * (z₂ : G) * t⁻¹)⁻¹ := by group
        _ = ((z₁ : G) * ((z₁ : G)⁻¹ * (t * (z₁ : G) * t⁻¹))) * (t * (z₂ : G) * t⁻¹)⁻¹ := by
          group
        _ = ((z₁ : G) * ((z₂ : G)⁻¹ * (t * (z₂ : G) * t⁻¹))) * (t * (z₂ : G) * t⁻¹)⁻¹ := by
          rw [h']
        _ = (z₁ : G) * (z₂ : G)⁻¹ := by group
    apply Subtype.ext
    exact mul_inv_eq_one.mp (hfix _ (N.mul_mem z₁.2 (N.inv_mem z₂.2)) hm)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  intro y hy
  obtain ⟨z, hz⟩ := hsurj ⟨y, hy⟩
  have hy' : (z : G)⁻¹ * (t * (z : G) * t⁻¹) = y := congrArg Subtype.val hz
  subst hy'
  have hconj2 : t * (t * (z : G) * t⁻¹) * t⁻¹ = (z : G) := by
    rw [ht']
    calc t * (t * (z : G) * t) * t = (t * t) * (z : G) * (t * t) := by group
      _ = (z : G) := by rw [ht, one_mul, mul_one]
  calc t * ((z : G)⁻¹ * (t * (z : G) * t⁻¹)) * t⁻¹
      = (t * (z : G)⁻¹ * t⁻¹) * (t * (t * (z : G) * t⁻¹) * t⁻¹) := by group
    _ = (t * (z : G)⁻¹ * t⁻¹) * (z : G) := by rw [hconj2]
    _ = ((z : G)⁻¹ * (t * (z : G) * t⁻¹))⁻¹ := by group

theorem pPrimeCore_inf_eq_bot_of_fitting {M : Subgroup G}
    (hF : CFSG.generalizedFitting M = pCore 2 M) :
    pPrimeCore 2 G ⊓ M = ⊥ := by
  obtain ⟨hQ2, -, hMQ⟩ := inSubgroup_pCore_two M
  have hCQ := CFSG.RankThree.GF2n.Tim78.inf_centralizer_le_of_generalizedFitting_eq hF
  have hOodd : Odd (Nat.card (pPrimeCore 2 G)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := G))
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxO, hxM⟩ := Subgroup.mem_inf.mp hx
  have hxC : x ∈ Subgroup.centralizer ((inSubgroup (pCore 2) M : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 : x * q * x⁻¹ * q⁻¹ ∈ inSubgroup (pCore 2) M :=
      (inSubgroup (pCore 2) M).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (hMQ hxM) q).mp hq)
        ((inSubgroup (pCore 2) M).inv_mem hq)
    have h2 : x * q * x⁻¹ * q⁻¹ ∈ pPrimeCore 2 G := by
      have e : x * q * x⁻¹ * q⁻¹ = x * (q * x⁻¹ * q⁻¹) := by group
      rw [e]
      exact (pPrimeCore 2 G).mul_mem hxO
        ((pPrimeCore_normal (p := 2) (G := G)).conj_mem _ ((pPrimeCore 2 G).inv_mem hxO) q)
    have h3 : x * q * x⁻¹ * q⁻¹ = 1 :=
      CFSG.RankThree.GF2n.Tim78.eq_one_of_odd_of_isPGroup hQ2 h1
        (Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard _ h2))
    calc q * x = (x * q * x⁻¹ * q⁻¹)⁻¹ * (x * q) := by group
      _ = x * q := by rw [h3, inv_one, one_mul]
  have hxQ : x ∈ inSubgroup (pCore 2) M :=
    hCQ (Subgroup.mem_inf.mpr ⟨hxM, hxC⟩)
  exact Subgroup.mem_bot.mpr
    (CFSG.RankThree.GF2n.Tim78.eq_one_of_odd_of_isPGroup hQ2 hxQ
      (Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard _ hxO)))

theorem parrott_odd_false {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (h12 : Lemma12Statement) (cfg : QPCfg M V Q P H Φ ψ a T) :
    ¬ (Subgroup.centralizer ({cfg.aG} : Set G) ⊔ pPrimeCore 2 G = ⊤) := by
  intro hcov
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hcent : Subgroup.centralizer ({cfg.aG} : Set G) = M :=
    (h12 G M V Q P H cfg.hyp cfg.centre Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).1
  have hOM : pPrimeCore 2 G ⊓ M = ⊥ := pPrimeCore_inf_eq_bot_of_fitting hc.fitting
  have hOC' : pPrimeCore 2 G ⊓ Subgroup.centralizer ({cfg.aG} : Set G) = ⊥ := by
    rw [hcent]
    exact hOM
  have hOC : ∀ m ∈ pPrimeCore 2 G, cfg.aG * m * cfg.aG⁻¹ = m → m = 1 := by
    intro m hm hfix
    have hmC : m ∈ Subgroup.centralizer ({cfg.aG} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      calc cfg.aG * m = cfg.aG * m * cfg.aG⁻¹ * cfg.aG := by group
        _ = m * cfg.aG := by rw [hfix]
    have hmem : m ∈ pPrimeCore 2 G ⊓ Subgroup.centralizer ({cfg.aG} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hm, hmC⟩
    rw [hOC'] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hfixAll : ∀ t : G, (∃ x : G, x * cfg.aG * x⁻¹ = t) →
      ∀ m ∈ pPrimeCore 2 G, t * m * t⁻¹ = m → m = 1 := by
    rintro t ⟨x, rfl⟩ m hm hfix
    have hm' : x⁻¹ * m * x ∈ pPrimeCore 2 G := by
      have := (pPrimeCore_normal (p := 2) (G := G)).conj_mem m hm x⁻¹
      rwa [inv_inv] at this
    have hc' : cfg.aG * (x⁻¹ * m * x) * cfg.aG⁻¹ = x⁻¹ * m * x := by
      calc cfg.aG * (x⁻¹ * m * x) * cfg.aG⁻¹
          = x⁻¹ * (x * cfg.aG * x⁻¹ * m * (x * cfg.aG * x⁻¹)⁻¹) * x := by group
        _ = x⁻¹ * m * x := by rw [hfix]
    have h1 := hOC (x⁻¹ * m * x) hm' hc'
    calc m = x * (x⁻¹ * m * x) * x⁻¹ := by group
      _ = x * 1 * x⁻¹ := by rw [h1]
      _ = 1 := by group
  have hinvert : ∀ t : G, (∃ x : G, x * cfg.aG * x⁻¹ = t) → t * t = 1 →
      ∀ y ∈ pPrimeCore 2 G, t * y * t⁻¹ = y⁻¹ := fun t ht hsq =>
    fixedPoint_free_involution_inverts (pPrimeCore_normal (p := 2) (G := G)) hsq
      (hfixAll t ht)
  have hinvAG : ∀ y ∈ pPrimeCore 2 G, cfg.aG * y * cfg.aG⁻¹ = y⁻¹ :=
    hinvert cfg.aG ⟨1, by simp⟩ (qpCfg_psi_mul_self a)
  have h2n : 2 ≤ n := by
    have := cfg.three
    omega
  obtain ⟨w₁, hw₀, -, hne⟩ := exists_perp_vec_not_smul h2n cfg.ne
  have hw₁a : w₁ ≠ a := fun h => hne 1 (by rw [one_smul]; exact h)
  have hsum : ∀ x : Fin n ⊕ Fin n → GaloisField 2 1, x + x = 0 := by
    intro x
    funext i
    exact CharTwo.add_self_eq_zero (x i)
  have hw₂ : w₁ + a ≠ 0 := by
    intro h
    apply hw₁a
    calc w₁ = w₁ + (a + a) := by rw [hsum a, add_zero]
      _ = (w₁ + a) + a := by rw [add_assoc]
      _ = a := by rw [h, zero_add]
  obtain ⟨u, hu⟩ : ∃ u : G, u = ((Additive.toMul (ψ w₁) : ↥(wOf V H)) : G) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : G, v = ((Additive.toMul (ψ (w₁ + a)) : ↥(wOf V H)) : G) :=
    ⟨_, rfl⟩
  have hu_conj : ∃ x : G, x * cfg.aG * x⁻¹ = u := by
    obtain ⟨x, hx⟩ := qpCfg_exists_conj_psi cfg hw₀
    exact ⟨x, hx.trans hu.symm⟩
  have hv_conj : ∃ x : G, x * cfg.aG * x⁻¹ = v := by
    obtain ⟨x, hx⟩ := qpCfg_exists_conj_psi cfg hw₂
    exact ⟨x, hx.trans hv.symm⟩
  have hu_sq : u * u = 1 := by
    rw [hu]
    exact qpCfg_psi_mul_self w₁
  have hv_sq : v * v = 1 := by
    rw [hv]
    exact qpCfg_psi_mul_self (w₁ + a)
  have hv_eq : v = u * cfg.aG := by
    rw [hv, hu, map_add]
    rfl
  have hu_inv := hinvert u hu_conj hu_sq
  have hv_cent : ∀ y ∈ pPrimeCore 2 G, v * y * v⁻¹ = y := by
    intro y hy
    rw [hv_eq]
    calc u * cfg.aG * y * (u * cfg.aG)⁻¹ = u * (cfg.aG * y * cfg.aG⁻¹) * u⁻¹ := by group
      _ = u * y⁻¹ * u⁻¹ := by rw [hinvAG y hy]
      _ = y := by rw [hu_inv y⁻¹ ((pPrimeCore 2 G).inv_mem hy), inv_inv]
  have hOone : pPrimeCore 2 G = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    exact Subgroup.mem_bot.mpr (hfixAll v hv_conj y hy (hv_cent y hy))
  have hMtop : M = ⊤ := by
    rw [hOone, sup_bot_eq] at hcov
    rw [← hcent]
    exact hcov
  have htop : Subgroup.normalizer ((inSubgroup (pCore 2) M : Subgroup G) : Set G) = ⊤ := by
    apply top_le_iff.mp
    rw [← hMtop]
    exact (inSubgroup_pCore_two M).2.2
  have hQN : (inSubgroup (pCore 2) M).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hQle : inSubgroup (pCore 2) M ≤ pCore 2 G :=
    le_sSup ⟨hQN, (inSubgroup_pCore_two M).1⟩
  rw [hc.o2] at hQle
  have hQbot : Q = ⊥ := hc.hQ.trans (le_bot_iff.mp hQle)
  have hVQ : V ≤ Q := by
    rw [le_antisymm cfg.qp hc.P_le_Q]
    exact hc.V_le_P
  have hVbot : V ≤ ⊥ := by
    rw [← hQbot]
    exact hVQ
  have h4 := qpCfg_card_V cfg
  have hV1 : Nat.card ↥V = 1 := by
    rw [le_bot_iff.mp hVbot]
    exact Subgroup.card_bot
  omega

end CFSG.RankThree.GF2n.Tim79a

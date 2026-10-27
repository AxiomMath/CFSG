module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5AutExist2
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5AutModel

public section

namespace CFSG.Quasithin.F6.GoldAmL5

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL4 CFSG.Quasithin.F6.GoldAmN Equiv
  CFSG.Quasithin.M12AmalAut

@[expose] def iotaS3 (σ : Perm (Fin 3)) : DihedralGroup 6 :=
  if σ 1 = σ 0 + 1 then DihedralGroup.r (2 * (((σ 0 : Fin 3) : ℕ) : ZMod 6))
  else DihedralGroup.sr (-(2 * (((σ 0 : Fin 3) : ℕ) : ZMod 6)))

@[expose] def iotaZ2 (e : Multiplicative (ZMod 2)) : DihedralGroup 6 :=
  if e = 1 then 1 else DihedralGroup.r 3

@[expose] def phiFun (p : Perm (Fin 3) × Multiplicative (ZMod 2)) : DihedralGroup 6 :=
  iotaS3 p.1 * iotaZ2 p.2

theorem phiFun_mul : ∀ p q : Perm (Fin 3) × Multiplicative (ZMod 2),
    phiFun (p * q) = phiFun p * phiFun q := by decide +kernel

theorem phiFun_bijective : Function.Bijective phiFun := by decide +kernel

@[expose] def phiHom : Perm (Fin 3) × Multiplicative (ZMod 2) →* DihedralGroup 6 :=
  MonoidHom.mk' phiFun phiFun_mul

theorem phiFun_one : phiFun 1 = 1 := by decide +kernel

theorem closure_four_union_eq {D : Type*} [Group D] (a b s ρ τ : D) :
    Subgroup.closure ((Subgroup.closure ({a, b, s, ρ} : Set D) : Set D) ∪ {τ}) =
      Subgroup.closure ({a, b, s, ρ, τ} : Set D) := by
  rw [← closure_union_closure]
  congr 1
  ext g
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ G₁' G₂' : Subgroup D} {a b s ρ x y : D}

namespace AutHyp

variable (H : AutHyp G₁ G₂ G₁' G₂' a b s ρ x y)

include H

theorem tau_not_mem₂ {τ : D} (hτT : τ ∈ G₁ ⊓ G₂) (hτG : τ ∉ G₁') : τ ∉ G₂' := by
  intro h
  have : τ ∈ (G₁ ⊓ G₂) ⊓ G₂' := ⟨hτT, h⟩
  rw [H.T_inf₂] at this
  exact hτG this.1

theorem closure_y_tau {τ : D} (hτT : τ ∈ G₁ ⊓ G₂) (hτG : τ ∉ G₁') :
    Subgroup.closure ({a, b, s, ρ, y, τ} : Set D) = G₂ := by
  rw [← closure_five_union_eq, H.eG₂]
  exact closure_union_eq_of_relIndex_two H.le₂ H.idx₂ hτT.2 (H.tau_not_mem₂ hτT hτG)

omit [Finite D] in
theorem closure_x_tau {τ : D} (hτT : τ ∈ G₁ ⊓ G₂) (hτG : τ ∉ G₁') :
    Subgroup.closure ({a, b, s, ρ, x, τ} : Set D) = G₁ := by
  rw [← closure_five_union_eq, H.eG₁]
  exact closure_union_eq_of_relIndex_two H.le₁ H.idx₁ hτT.1 hτG

theorem closure_T_tau {τ : D} (hτT : τ ∈ G₁ ⊓ G₂) (hτG : τ ∉ G₁') :
    Subgroup.closure ({a, b, s, ρ, τ} : Set D) = G₁ ⊓ G₂ := by
  rw [← closure_four_union_eq, H.eT]
  exact closure_union_eq_of_relIndex_two H.T'_le_T H.relIndex_T hτT (fun h => hτG h.1)

theorem z_central {τ : D} (hτ : TauRel a b s ρ x y τ) (hτT : τ ∈ G₁ ⊓ G₂) (hτG : τ ∉ G₁') :
    ∀ t ∈ G₁ ⊓ G₂, t * H.emb zR = H.emb zR * t := by
  intro t ht
  rw [← H.closure_T_tau hτT hτG] at ht
  refine aut_commute_of_gens (S := ({a, b, s, ρ, τ} : Set D)) (fun g hg => ?_) t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with h | h | h | h | h
  · rw [h]
    have e : H.emb zR * H.emb rA = H.emb rA * H.emb zR := by
      rw [← map_mul, ← map_mul, zR_central]
    rw [H.emb_rA] at e
    exact e.symm
  · rw [h]
    have e : H.emb zR * H.emb rB = H.emb rB * H.emb zR := by
      rw [← map_mul, ← map_mul, zR_central]
    rw [H.emb_rB] at e
    exact e.symm
  · rw [h]
    have e : H.emb zR * H.emb rS = H.emb rS * H.emb zR := by
      rw [← map_mul, ← map_mul, zR_central]
    rw [H.emb_rS] at e
    exact e.symm
  · rw [h]
    have e : H.emb zR * H.emb rR = H.emb rR * H.emb zR := by
      rw [← map_mul, ← map_mul, zR_central]
    rw [H.emb_rR] at e
    exact e.symm
  · rw [h]
    have e := hτ.conj_embR H.hA.toTRel H.hAρ.toRhoRel zR
    rw [thetaStd_zR] at e
    calc τ * H.emb zR = τ * H.emb zR * (τ * τ) := by rw [hτ.hτ, mul_one]
      _ = (τ * H.emb zR * τ) * τ := by group
      _ = H.emb zR * τ := by rw [e]

theorem pCore₂_le_pCore : pCoreOf 2 G₂' ≤ pCoreOf 2 G₂ := by
  rw [← pCoreOf_inf_eq_of_relIndex_two H.le₂ H.idx₂]
  exact inf_le_left

theorem card_centerOf_pCore₂ {τ : D} (hτ : TauRel a b s ρ x y τ) (hτT : τ ∈ G₁ ⊓ G₂)
    (hτG : τ ∉ G₁') : Nat.card ↥(centerOf (pCoreOf 2 G₂)) = 2 := by
  obtain ⟨z, hz⟩ : ∃ z : D, z = H.emb zR := ⟨_, rfl⟩
  have hz2 : z * z = 1 := by rw [hz, ← map_mul, zR_sq, map_one]
  have hz1 : z ≠ 1 := fun h => zR_ne_one (H.emb_injective (by rw [← hz, h, map_one]))
  have hQP : ∀ v : Tr, inQ2 v → H.emb v ∈ pCoreOf 2 G₂ := fun v hv => by
    apply H.pCore₂_le_pCore
    rw [H.pCore₂]
    exact Subgroup.mem_map_of_mem _ hv
  have hzP : z ∈ pCoreOf 2 G₂ := by rw [hz]; exact hQP zR zR_mem_Q2
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ.hτ
  have hcentral : centerOf (pCoreOf 2 G₂) = Subgroup.zpowers z := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgP, hgc⟩ := Subgroup.mem_inf.mp hg
      have hgT : g ∈ G₁ ⊓ G₂ := H.amalgam.pCoreOf_right_le hgP
      have hgcomm : ∀ q ∈ pCoreOf 2 G₂, q * g = g * q := fun q hq =>
        Subgroup.mem_centralizer_iff.mp hgc q hq
      by_cases hgG : g ∈ G₂'
      · have hgQ : g ∈ pCoreOf 2 G₂' := by
          rw [← pCoreOf_inf_eq_of_relIndex_two H.le₂ H.idx₂]
          exact ⟨hgP, hgG⟩
        rw [H.pCore₂] at hgQ
        obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hgQ
        have : w₀ = 1 ∨ w₀ = zR := by
          apply Q2_center w₀ hw₀
          intro v hv
          apply H.emb_injective
          rw [map_mul, map_mul]
          exact (hgcomm (H.emb v) (hQP v hv)).symm
        rcases this with rfl | rfl
        · rw [map_one]; exact (Subgroup.zpowers z).one_mem
        · rw [← hz]; exact Subgroup.mem_zpowers z
      · exfalso
        have hgT' : g ∉ G₁' ⊓ G₂' := fun h => hgG h.2
        obtain ⟨t₀, ht₀⟩ : ∃ t₀ : Tr, H.emb t₀ = g * τ := by
          have := (mem_or_mul_mem_of_relIndex_two H.relIndex_T hτT (fun h => hτG h.1)
            hgT).resolve_left hgT'
          rw [← H.range_emb] at this
          exact this
        obtain ⟨v, hv, hne⟩ := thetaStd_not_inner t₀
        apply hne
        apply H.emb_injective
        have e1 := hτ.conj_embR H.hA.toTRel H.hAρ.toRhoRel v
        have hgv := hgcomm (H.emb v) (hQP v hv)
        have hg' : g = H.emb t₀ * τ := by
          rw [ht₀]
          calc g = g * (τ * τ) := by rw [hτ.hτ, mul_one]
            _ = g * τ * τ := by group
        calc H.emb (t₀ * thetaStd v * t₀⁻¹)
            = H.emb t₀ * (τ * H.emb v * τ) * (H.emb t₀)⁻¹ := by
              rw [map_mul, map_mul, map_inv, ← e1]
          _ = (H.emb t₀ * τ) * H.emb v * (H.emb t₀ * τ)⁻¹ := by
              rw [mul_inv_rev, hτinv]; group
          _ = g * H.emb v * g⁻¹ := by rw [← hg']
          _ = H.emb v := by
              calc g * H.emb v * g⁻¹ = (H.emb v * g) * g⁻¹ := by rw [hgv]
                _ = H.emb v := by group
    · rw [Subgroup.zpowers_le]
      refine ⟨hzP, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      rw [hz]
      exact H.z_central hτ hτT hτG q (H.amalgam.pCoreOf_right_le hq)
  rw [hcentral, Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1


theorem card_pCoreT₂ : Nat.card ↥(pCoreOf 2 G₂) = 64 := by
  have := card_eq_of_relIndex_two H.amalgam.pCoreOf_right_le H.amalgam.relIndex_pCoreOf_T_right
  rw [H.card_T] at this
  omega

theorem card_pCore₂ : Nat.card ↥(pCoreOf 2 G₂') = 32 := by
  have := card_eq_of_relIndex_two H.vertex₂.pCoreOf_le H.vertex₂.relIndex_pCoreOf_T
  rw [H.card_T'] at this
  omega

theorem isExtensionWith_G₂
    (h₂ : IsCentralProduct₂ ↥(pCoreOf 2 G₂') (QuaternionGroup 2) (QuaternionGroup 2)) :
    IsExtensionWith ↥G₂ (DihedralGroup 6)
      (fun N => IsCentralProduct₂ ↥N (QuaternionGroup 2) (QuaternionGroup 2)) := by
  classical
  obtain ⟨π, hπs, hπk⟩ := exists_hom_perm_three G₂ H.amalgam.amalgam.quotient₂
  let N : Subgroup ↥G₂ := G₂'.subgroupOf G₂
  have hN : N.index = 2 := H.idx₂
  have key : ∀ g h : ↥G₂, g * h ∈ N ↔ (g ∈ N ↔ h ∈ N) := fun g h =>
    Subgroup.mul_mem_iff_of_index_two hN
  let εFun : ↥G₂ → Multiplicative (ZMod 2) := fun g =>
    if g ∈ N then 1 else Multiplicative.ofAdd 1
  have hεmul : ∀ g h : ↥G₂, εFun (g * h) = εFun g * εFun h := by
    intro g h
    by_cases hg : g ∈ N
    · by_cases hh : h ∈ N
      · have : g * h ∈ N := (key g h).mpr (iff_of_true hg hh)
        simp [εFun, hg, hh, this]
      · have : g * h ∉ N := fun hgh => hh (((key g h).mp hgh).mp hg)
        simp [εFun, hg, hh, this]
    · by_cases hh : h ∈ N
      · have : g * h ∉ N := fun hgh => hg (((key g h).mp hgh).mpr hh)
        simp [εFun, hg, hh, this]
      · have : g * h ∈ N := (key g h).mpr (iff_of_false hg hh)
        simp only [εFun, hg, hh, this, ite_true, ite_false]
        decide
  let ε : ↥G₂ →* Multiplicative (ZMod 2) := MonoidHom.mk' εFun hεmul
  have hεN : ∀ g : ↥G₂, ε g = 1 ↔ g ∈ N := by
    intro g
    show εFun g = 1 ↔ g ∈ N
    by_cases hg : g ∈ N
    · simp [εFun, hg]
    · simp only [εFun, hg, ite_false, iff_false]
      decide
  let φ : ↥G₂ →* DihedralGroup 6 := phiHom.comp (π.prod ε)
  have hφapp : ∀ g : ↥G₂, φ g = phiFun (π g, ε g) := fun g => rfl
  have hφ1 : ∀ g : ↥G₂, φ g = 1 ↔ π g = 1 ∧ ε g = 1 := by
    intro g
    rw [hφapp, ← phiFun_one, phiFun_bijective.1.eq_iff]
    exact Prod.mk_eq_one
  have hker : φ.ker = (pCoreOf 2 G₂').subgroupOf G₂ := by
    ext g
    rw [MonoidHom.mem_ker, hφ1, Subgroup.mem_subgroupOf,
      ← pCoreOf_inf_eq_of_relIndex_two H.le₂ H.idx₂, Subgroup.mem_inf,
      GoldAmN.mem_pCoreOf_iff g.2, ← hπk, hεN, MonoidHom.mem_ker]
    rfl
  obtain ⟨p, hpP, hpG⟩ : ∃ p ∈ pCoreOf 2 G₂, p ∉ G₂' := by
    by_contra hcon
    push Not at hcon
    have hle : pCoreOf 2 G₂ ≤ pCoreOf 2 G₂' := by
      rw [← pCoreOf_inf_eq_of_relIndex_two H.le₂ H.idx₂]
      exact le_inf le_rfl (fun p hp => hcon p hp)
    have := Subgroup.card_le_of_le hle
    rw [H.card_pCoreT₂, H.card_pCore₂] at this
    omega
  have hpG₂ : p ∈ G₂ := pCoreOf_le 2 G₂ hpP
  have hpπ : π ⟨p, hpG₂⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hπk, ← GoldAmN.mem_pCoreOf_iff hpG₂]
    exact hpP
  have hpε : ε ⟨p, hpG₂⟩ = Multiplicative.ofAdd 1 := by
    show εFun ⟨p, hpG₂⟩ = _
    have : (⟨p, hpG₂⟩ : ↥G₂) ∉ N := fun h => hpG h
    simp only [εFun, this, ite_false]
  have hsurj : Function.Surjective φ := by
    intro d
    obtain ⟨⟨σ, e⟩, rfl⟩ := phiFun_bijective.2 d
    obtain ⟨g₁, hg₁⟩ := hπs σ
    by_cases hε : ε g₁ = e
    · exact ⟨g₁, by rw [hφapp, hg₁, hε]⟩
    · refine ⟨g₁ * ⟨p, hpG₂⟩, ?_⟩
      have hε2 : ε (g₁ * ⟨p, hpG₂⟩) = e := by
        rw [map_mul, hpε]
        revert hε
        generalize ε g₁ = u
        revert u e
        decide
      rw [hφapp, map_mul, hg₁, hpπ, mul_one, hε2]
  refine ⟨φ, hsurj, ?_⟩
  have hle : pCoreOf 2 G₂' ≤ G₂ := (pCoreOf_le 2 G₂').trans H.le₂
  exact isCentralProduct₂_of_mulEquiv
    ((MulEquiv.subgroupCongr hker).trans (Subgroup.subgroupOfEquivOfLe hle)) h₂

end AutHyp

theorem isGoldCaseAutM12Cat_of_hyp
    (H : AutHyp G₁ G₂ G₁' G₂' a b s ρ x y)
    (h₂ : IsCentralProduct₂ ↥(pCoreOf 2 G₂') (QuaternionGroup 2) (QuaternionGroup 2)) :
    IsGoldCaseAutM12Cat G₂ G₁ := by
  obtain ⟨τ, hτ, hτT, hτG⟩ := H.exists_tau
  have hiso := isAmalgamIso_of_tuples_aut H.hA H.hAρ H.hB hτ aut_ARel aut_ARho aut_MRelB
    aut_TauRel H.card card_closure_T' (by rw [H.eG₂]; exact H.tau_not_mem₂ hτT hτG)
    (by rw [H.eG₁]; exact hτG) tau_not_mem_closure_y tau_not_mem_closure_x
    (by rw [H.closure_y_tau hτT hτG, H.closure_x_tau hτT hτG, H.closure_T_tau hτT hτG, inf_comm])
    (by rw [closure_A_aut, closure_B_aut, closure_T_aut]; exact autData.inf_AB)
  rw [H.closure_y_tau hτT hτG, H.closure_x_tau hτT hτG] at hiso
  refine ⟨isYAmalgam_Aut_of_iso hiso, ?_, H.amalgam.amalgam.quotient₂,
    H.amalgam.amalgam.quotient₁, H.isExtensionWith_G₂ h₂, ?_,
    H.card_centerOf_pCore₂ hτ hτT hτG, ?_⟩
  ·
    intro hc
    rcases hc with hc | hc
    · exact hc
    · exfalso
      have hzT' : H.emb zR ∈ G₁' ⊓ G₂' := by rw [← H.range_emb]; exact ⟨zR, rfl⟩
      have hz : H.emb zR ∈ centerOf (G₂ ⊓ G₁) := by
        rw [inf_comm]
        exact ⟨H.T'_le_T hzT', Subgroup.mem_centralizer_iff.mpr fun t ht =>
          H.z_central hτ hτT hτG t ht⟩
      have hx : x ∈ G₁ := H.le₁ H.x_mem
      have h1 : x * H.emb zR = H.emb zR * x := Subgroup.mem_centralizer_iff.mp (hc hz) x hx
      have h2 : x⁻¹ * H.emb zR * x = H.emb zR := by
        calc x⁻¹ * H.emb zR * x = x⁻¹ * (H.emb zR * x) := by group
          _ = x⁻¹ * (x * H.emb zR) := by rw [h1]
          _ = H.emb zR := by group
      have h3 := aRho_conj_embR H.hA H.hAρ zR zR_mem_Q1
      rw [h2] at h3
      exact actA_zR (H.emb_injective h3.symm)
  · rw [H.card_pCoreT₂]; norm_num
  · rw [H.card_pCoreT₁]; norm_num

end CFSG.Quasithin.F6.GoldAmL5

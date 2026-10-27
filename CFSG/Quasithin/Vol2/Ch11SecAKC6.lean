module

public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAKC2
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import CFSG.Quasithin.Vol2.KGNatSL3Par
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat CFSG.ClassicalInvolution.ModelFacts.OddCover
  CFSG.QuasithinUnique.Bridge.Alt57Model Matrix
open CFSG.Quasithin.Vol2.Ch11.G2Q8

namespace KC6

theorem conj_mem_stabW_map {W : Type*} [Group W] {U : Subgroup W} {x : MulAut W}
    (hx : x ∈ stabW U) (s : MulAut W) : s * x * s⁻¹ ∈ stabW (U.map s.toMonoidHom) := by
  rw [mem_stabW]
  intro u
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  have h := (mem_stabW.mp hx) (s.symm u)
  rw [h]
  change x (s⁻¹ u) ∈ U ↔ s⁻¹ (s (x (s⁻¹ u))) ∈ U
  rw [MulAut.inv_apply_self]

variable {K : Type} [Field K] [CharP K 2]

theorem swap12_mem_stabV0 : g2A (swap12 : SL3 K) ∈ stabV0 K := by
  rw [mem_stabV0, g2Act_swap12]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6, eu]

theorem g2Act_uSL_F3 (t : K) {x : Ix3 → K} (hx : x ∈ stdF K 3) :
    g2Act (g2A (uSL 0 0 t)) x - x = Pi.single (.inr 2) (t * x (.inr 1)) := by
  have h1 : x (.inl 1) = 0 := hx (.inl 1) (by decide)
  have h2 : x (.inl 2) = 0 := hx (.inl 2) (by decide)
  have h3 : x (.inr 0) = 0 := hx (.inr 0) (by decide)
  rw [g2Act_g2A_uSL]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6, h1, h2, h3]

omit [CharP K 2] in
theorem sub_single_mem_stdF_one {z : Ix3 → K} (hz : z ∈ stdF K 2) :
    z - Pi.single (.inr 2) (z (.inr 2)) ∈ stdF K 1 := by
  intro k hk
  rcases k with k | k <;> fin_cases k
  · exact absurd hk (by decide)
  · simp [hz (.inl 1) (by decide)]
  · simp [hz (.inl 2) (by decide)]
  · simp [hz (.inr 0) (by decide)]
  · simp [hz (.inr 1) (by decide)]
  · simp

omit [CharP K 2] in
theorem ne_zero_of_not_mem {x : Ix3 → K} (h3 : x ∈ stdF K 3) (h2 : x ∉ stdF K 2) :
    x (.inr 1) ≠ 0 := by
  intro ha
  apply h2
  intro k hk
  rcases k with k | k <;> fin_cases k
  · exact absurd hk (by decide)
  · exact h3 _ (by decide)
  · exact h3 _ (by decide)
  · exact h3 _ (by decide)
  · exact ha
  · exact absurd hk (by decide)

end KC6

open KC6 in
theorem factDeltaG2_holds : FactDeltaG2 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ hZ P hP U₁ U₂ U₃ hU₁ hU₂ hU₃
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have := finite_cayleyGroup (F := K)
  have h4 := four_le_card hn hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  have hfix1 : ∀ h ∈ perfectCore (H ⊓ stabW U₁), ∀ u ∈ U₁, h u = u :=
    fix_of_perfect (perfectCore_perfect _) (fun h hh z hz => hZ h (perfectCore_le _ hh).1 z hz)
      (factPointG2A_holds K n hn hK W hW H Z π hπ P hP U₁ hU₁)
  have hrad := factRadicalFixedG2_holds K n hn hK W hW H Z π hπ P hP U₁ hU₁
  have hPS := factSylowLeviG2_holds K n hn hK W hW H Z π hπ P hP U₁ hU₁
  have hU₁' := hU₁
  have hU₂' := hU₂
  obtain ⟨hZU₁, -, hidx₁, -⟩ := hU₁'
  obtain ⟨-, -, hidx₂, -⟩ := hU₂'
  have hU1 := eq_U1_of_isFlagWG hW hf hc0 hc1 hg (by rw [hK]; exact hU₁)
  have hU2 := eq_U2_of_isFlagWG hW hf hc0 hc1 hg (by rw [hK]; exact hU₂)
  have hU3 : U₃ = hf.pre (gmapG g (stdF K 3)).toAddSubgroup := by
    obtain ⟨S, hS, hc, rfl⟩ := exists_eq_preG_of_isFlagW hW hf hc0 hc1 hg (by rw [hK]; exact hU₃)
    rw [eq_stdF_of_card hS hc]
  subst hU1 hU2 hU3
  set ψ := psiG hc0 hc1 π g with hψdef
  refine ⟨fun u _ => ⟨fun h => hrad u fun x hx => ?_, fun hu s hs => ?_⟩, ?_, ?_⟩
  ·
    rw [h x ⟨x, hx, rfl⟩, mul_inv_cancel]
    exact Z.one_mem
  ·
    obtain ⟨y, -, rfl⟩ := hs
    exact hfix1 y y.2 u hu
  ·
    intro R hR hRP U hU₁U hUU₃ hidx hRU
    have hPR : P = R := hR.eq_of_le hRP hPS hP.isPGroup
    rw [← hPR] at hRU
    have hq : 0 < 2 ^ n := by positivity
    have h12 : hf.pre (gmapG g (stdF K 1)).toAddSubgroup ≤
        hf.pre (gmapG g (stdF K 2)).toAddSubgroup :=
      fun w hw => gmapG_mono (stdF_mono (by norm_num)) hw
    have hidx12 : (hf.pre (gmapG g (stdF K 1)).toAddSubgroup).relIndex
        (hf.pre (gmapG g (stdF K 2)).toAddSubgroup) = 2 ^ n := by
      have h := Subgroup.relIndex_mul_relIndex Z _ _ hZU₁ h12
      rw [hidx₁, hidx₂, pow_one, sq] at h
      exact Nat.eq_of_mul_eq_mul_left hq h
    have hU2U : hf.pre (gmapG g (stdF K 2)).toAddSubgroup ≤ U := by
      by_cases h : U ≤ hf.pre (gmapG g (stdF K 2)).toAddSubgroup
      · have h' := Subgroup.relIndex_mul_relIndex _ _ _ hU₁U h
        rw [hidx, hidx12] at h'
        exact Subgroup.relIndex_eq_one.mp
          (Nat.eq_of_mul_eq_mul_left hq (h'.trans (mul_one _).symm))
      · obtain ⟨w, hwU, hwU₂⟩ := Set.not_subset.mp h
        have hw3 : g2Act g⁻¹ (f w) ∈ stdF K 3 := mem_gmapG.mp (hUU₃ hwU)
        have hw2 : g2Act g⁻¹ (f w) ∉ stdF K 2 := fun h2 => hwU₂ (mem_gmapG.mpr h2)
        have ha := ne_zero_of_not_mem hw3 hw2
        set y := g2Act g⁻¹ (f w) with hy
        have hfw : f w = g2Act g y := by
          rw [hy, ← g2Act_mul_apply, mul_inv_cancel, map_one]
          rfl
        have hgen : ∀ c : K, ∃ w' ∈ U, f w' = g2Act g (Pi.single (.inr 2) c) := by
          intro c
          have hmem : ((rhoG hc0 hc1 π (g * g2A (uSL 0 0 (c / y (.inr 1))) * g⁻¹) : ↥H) :
              MulAut W) ∈ P := (hg _).mpr ⟨_, g2A_mem_U0 _ _ _, rfl⟩
          refine ⟨_ * w⁻¹, U.mul_mem ((mem_stabW.mp (hRU hmem) w).mp hwU) (U.inv_mem hwU), ?_⟩
          rw [hf.map_mul_inv, IsCoord.actG hf hc0 hc1, hfw, g2Act_mul_apply, g2Act_mul_apply,
            g2Act_inv_apply, ← map_sub, g2Act_uSL_F3 _ hw3, div_mul_cancel₀ _ ha]
        intro w₂ hw₂
        have hz : g2Act g⁻¹ (f w₂) ∈ stdF K 2 := mem_gmapG.mp hw₂
        obtain ⟨w', hw'U, hw'f⟩ := hgen (g2Act g⁻¹ (f w₂) (.inr 2))
        have h1 : w₂ * w'⁻¹ ∈ U := hU₁U (by
          change f (w₂ * w'⁻¹) ∈ gmapG g (stdF K 1)
          rw [hf.map_mul_inv, hw'f, mem_gmapG, map_sub, g2Act_inv_apply]
          exact sub_single_mem_stdF_one hz)
        simpa using U.mul_mem h1 hw'U
    have h' := Subgroup.relIndex_mul_relIndex _ _ _ h12 hU2U
    rw [hidx12, hidx] at h'
    exact le_antisymm (Subgroup.relIndex_eq_one.mp
      (Nat.eq_of_mul_eq_mul_left hq (h'.trans (mul_one _).symm))) hU2U
  ·
    have hS₁ : perfectCore (H ⊓ stabW (hf.pre (gmapG g (stdF K 1)).toAddSubgroup)) =
        (stabV0 K).map ψ := gammaW_one_eqG h4 hf hc0 hc1 g
    have hA : ∀ k ∈ sl2E1 K, ψ k ∈ H ⊓ stabW (hf.pre (gmapG g (stdF K 2)).toAddSubgroup) := by
      intro k hk
      rw [← map_stabQ_eq hf hc0 hc1 g]
      exact ⟨k, sl2E1_le_stabQ hk, rfl⟩
    have hAp : ⁅(sl2E1 K).map ψ, (sl2E1 K).map ψ⁆ = (sl2E1 K).map ψ := by
      rw [← Subgroup.map_commutator, sl2E1_perfect hc0 hc1]
    set Y := ⨆ s ∈ perfectCore (H ⊓ stabW (hf.pre (gmapG g (stdF K 1)).toAddSubgroup)),
      perfectCore (H ⊓ stabW ((hf.pre (gmapG g (stdF K 2)).toAddSubgroup).map s.toMonoidHom))
    have key : ∀ s ∈ perfectCore (H ⊓ stabW (hf.pre (gmapG g (stdF K 1)).toAddSubgroup)),
        ∀ k ∈ sl2E1 K, s * ψ k * s⁻¹ ∈ Y := by
      intro s hs k hk
      have hsH : s ∈ H := (perfectCore_le _ hs).1
      have hB : ((sl2E1 K).map ψ).map (MulAut.conj s).toMonoidHom ≤
          H ⊓ stabW ((hf.pre (gmapG g (stdF K 2)).toAddSubgroup).map s.toMonoidHom) := by
        rintro _ ⟨_, ⟨k', hk', rfl⟩, rfl⟩
        obtain ⟨h1, h2⟩ := hA k' hk'
        exact ⟨H.mul_mem (H.mul_mem hsH h1) (H.inv_mem hsH), conj_mem_stabW_map h2 s⟩
      have hBp : ⁅((sl2E1 K).map ψ).map (MulAut.conj s).toMonoidHom,
          ((sl2E1 K).map ψ).map (MulAut.conj s).toMonoidHom⁆ =
          ((sl2E1 K).map ψ).map (MulAut.conj s).toMonoidHom := by
        rw [← Subgroup.map_commutator, hAp]
      exact Subgroup.mem_iSup_of_mem s (Subgroup.mem_iSup_of_mem hs
        (le_perfectCore_of_perfect hB hBp ⟨ψ k, ⟨k, hk, rfl⟩, rfl⟩))
    refine le_antisymm (iSup₂_le fun s _ => (perfectCore_le _).trans inf_le_left) ?_
    have hσ : ψ (g2A swap12) ∈
        perfectCore (H ⊓ stabW (hf.pre (gmapG g (stdF K 1)).toAddSubgroup)) := by
      rw [hS₁]
      exact ⟨_, swap12_mem_stabV0, rfl⟩
    have hgen : genE12 K ≤ Y.comap ψ := by
      rw [genE12, Subgroup.closure_le]
      rintro b (hb | ⟨b', hb', rfl⟩)
      · have h := key 1 (Subgroup.one_mem _) b (Subgroup.subset_closure hb)
        rwa [one_mul, inv_one, mul_one] at h
      · have h := key _ hσ b' (Subgroup.subset_closure hb')
        rw [← map_inv ψ, ← map_mul ψ, ← map_mul ψ] at h
        exact h
    intro x hx
    obtain ⟨δ, hδ⟩ := (rhoG_bijective hf hc0 hc1).2 ⟨x, hx⟩
    have h := hgen (show g⁻¹ * δ * g ∈ genE12 K by rw [genE12_eq_top]; exact Subgroup.mem_top _)
    rw [Subgroup.mem_comap, hψdef, psiG_apply, show g * (g⁻¹ * δ * g) * g⁻¹ = δ by group,
      hδ] at h
    exact h

end CFSG.Quasithin.Vol2.Ch11.SecA

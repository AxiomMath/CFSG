module

public import CFSG.Quasithin.Recognition.SzVBEvenCrit
public import CFSG.Quasithin.Recognition.SzVBEvenType0

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

omit [Finite G] in
private def commSub (G₁ V₀ Y : Subgroup G) (hV₀N : G₁ ≤ Subgroup.normalizer (V₀ : Set G)) :
    Subgroup G where
  carrier := {n | n ∈ G₁ ∧ ∀ y ∈ Y, n * y * n⁻¹ * y⁻¹ ∈ V₀}
  mul_mem' := by
    rintro n n' ⟨hn, hnc⟩ ⟨hn', hnc'⟩
    refine ⟨G₁.mul_mem hn hn', fun y hy => ?_⟩
    have h1 : n * (n' * y * n'⁻¹ * y⁻¹) * n⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.mp (hV₀N hn) _).mp (hnc' y hy)
    have e : n * n' * y * (n * n')⁻¹ * y⁻¹ =
        n * (n' * y * n'⁻¹ * y⁻¹) * n⁻¹ * (n * y * n⁻¹ * y⁻¹) := by group
    rw [e]
    exact V₀.mul_mem h1 (hnc y hy)
  one_mem' := ⟨G₁.one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro n ⟨hn, hnc⟩
    refine ⟨G₁.inv_mem hn, fun y hy => ?_⟩
    have h1 : n⁻¹ * (n * y * n⁻¹ * y⁻¹)⁻¹ * n⁻¹⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.mp (hV₀N (G₁.inv_mem hn)) _).mp (V₀.inv_mem (hnc y hy))
    have e : n⁻¹ * y * n⁻¹⁻¹ * y⁻¹ = n⁻¹ * (n * y * n⁻¹ * y⁻¹)⁻¹ * n⁻¹⁻¹ := by group
    rw [e]
    exact h1

omit [Finite G] in
theorem normalizes_of_normalClosure {G₁ T V₀ W₁ Y Vb : Subgroup G} (hTG : T ≤ G₁)
    (hT2 : IsPGroup 2 T) (hT3 : T.relIndex G₁ = 3) (hV₀N : G₁ ≤ Subgroup.normalizer (V₀ : Set G))
    (hYN : G₁ ≤ Subgroup.normalizer (Y : Set G)) (hV₀W : V₀ ≤ W₁) (hWY : W₁ ≤ Y)
    (hTW : T ≤ Subgroup.normalizer (W₁ : Set G)) (hVb : Vb ≤ G₁) (hVbQ : ¬ Vb ≤ pCoreOf 2 G₁)
    (hcomm : ∀ y ∈ Y, ∀ w ∈ Vb, y * w * y⁻¹ * w⁻¹ ∈ V₀) :
    G₁ ≤ Subgroup.normalizer (W₁ : Set G) := by
  obtain ⟨C, hCmem⟩ : ∃ C : Subgroup G,
      ∀ n, n ∈ C ↔ n ∈ G₁ ∧ ∀ y ∈ Y, n * y * n⁻¹ * y⁻¹ ∈ V₀ :=
    ⟨commSub G₁ V₀ Y hV₀N, fun _ => Iff.rfl⟩
  have hVbC : Vb ≤ C := fun w hw => by
    refine (hCmem w).mpr ⟨hVb hw, fun y hy => ?_⟩
    have e : w * y * w⁻¹ * y⁻¹ = (y * w * y⁻¹ * w⁻¹)⁻¹ := by group
    rw [e]
    exact V₀.inv_mem (hcomm y hy w hw)
  have hconj : ∀ g ∈ G₁, ∀ n ∈ C, g * n * g⁻¹ ∈ C := by
    intro g hg n hn
    obtain ⟨hnG, hnc⟩ := (hCmem n).mp hn
    refine (hCmem _).mpr ⟨G₁.mul_mem (G₁.mul_mem hg hnG) (G₁.inv_mem hg), fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (hYN (G₁.inv_mem hg)) y).mp hy
      simpa using this
    have h2 := (Subgroup.mem_normalizer_iff.mp (hV₀N hg) _).mp (hnc _ hy')
    have e : g * n * g⁻¹ * y * (g * n * g⁻¹)⁻¹ * y⁻¹ =
        g * (n * (g⁻¹ * y * g) * n⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact h2
  have hNC : conjClosure Vb G₁ ≤ C := conjClosure_le fun h hh w hw => hconj h hh w (hVbC hw)
  have hCG : C ≤ G₁ := fun n hn => ((hCmem n).mp hn).1
  have hCW : C ≤ Subgroup.normalizer (W₁ : Set G) := by
    have key : ∀ n ∈ C, ∀ w ∈ W₁, n * w * n⁻¹ ∈ W₁ := by
      intro n hn w hw
      have h1 := ((hCmem n).mp hn).2 w (hWY hw)
      have e : n * w * n⁻¹ = (n * w * n⁻¹ * w⁻¹) * w := by group
      rw [e]
      exact W₁.mul_mem (hV₀W h1) hw
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => key n hn w hw, fun hw => ?_⟩
    have := key n⁻¹ (C.inv_mem hn) _ hw
    simpa [mul_assoc] using this
  have hTH : T ≤ Subgroup.normalizer (W₁ : Set G) ⊓ G₁ := le_inf hTW hTG
  have hHG : Subgroup.normalizer (W₁ : Set G) ⊓ G₁ ≤ G₁ := inf_le_right
  have hmul := Subgroup.relIndex_mul_relIndex T (Subgroup.normalizer (W₁ : Set G) ⊓ G₁) G₁
    hTH hHG
  rw [hT3] at hmul
  have hdvd : (Subgroup.normalizer (W₁ : Set G) ⊓ G₁).relIndex G₁ ∣ 3 := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact (Subgroup.relIndex_eq_one.mp h1).trans inf_le_left
  · exfalso
    rw [h3] at hmul
    have h1 : T.relIndex (Subgroup.normalizer (W₁ : Set G) ⊓ G₁) = 1 := by omega
    have hHT := Subgroup.relIndex_eq_one.mp h1
    have hNT : conjClosure Vb G₁ ≤ T := hNC.trans ((le_inf hCW hCG).trans hHT)
    have hNp : IsPGroup 2 (conjClosure Vb G₁) := hT2.to_le hNT
    exact hVbQ ((le_conjClosure Vb G₁).trans
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hNT.trans hTG)
        (le_normalizer_conjClosure Vb G₁) hNp))

omit [Finite G] in
private theorem le_normalizer_iSup_Vv_nbrs (hC : GeoCtx G₀ G₁ G₂ T V z) :
    G₁ ≤ Subgroup.normalizer ((⨆ (β : CosetGeom G₀ G₁ G₂)
      (_ : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β), Vv V β : Subgroup G) : Set G) := by
  have h₁ : G₁ ≤ G₀ := hC.hyp.le₁
  have key : ∀ g ∈ G₁, conjSub g (⨆ (β : CosetGeom G₀ G₁ G₂)
      (_ : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β), Vv V β) ≤ ⨆ (β : CosetGeom G₀ G₁ G₂)
      (_ : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β), Vv V β := by
    intro g hg
    rw [conjSub_iSup]
    refine iSup_le fun β => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hβ => ?_
    have hadj : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) ((⟨g, h₁ hg⟩ : ↥G₀) • β) := by
      have := (smul_adj (⟨g, h₁ hg⟩ : ↥G₀)).mpr hβ
      rwa [smul_γ₀_of_mem h₁ hg] at this
    exact (Vv_smul hC.hyp.normalizes (⟨g, h₁ hg⟩ : ↥G₀) β).symm.le.trans
      (le_iSup₂_of_le _ hadj le_rfl)
  intro g hg
  exact F7.mem_normalizer_of_conj_le (key g hg) (key g⁻¹ (G₁.inv_mem hg))

private theorem mem_or_mul_inv_mem_of_relIndex_le_two {Q Y : Subgroup G}
    (h : Q.relIndex Y ≤ 2) {v y : G} (hv : v ∈ Y) (hvQ : v ∉ Q) (hy : y ∈ Y) :
    y ∈ Q ∨ y * v⁻¹ ∈ Q := by
  have hpos : 0 < Q.relIndex Y :=
    Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card (H := Q) (K := Y)) Nat.card_pos
  have hdvd : Q.relIndex Y ∣ 2 := by
    rcases (show Q.relIndex Y = 1 ∨ Q.relIndex Y = 2 by omega) with h1 | h2
    · rw [h1]
      exact one_dvd _
    · rw [h2]
  obtain ⟨a, -, ha⟩ := Subgroup.relIndex_dvd_two_iff.mp hdvd
  have hva : v * a ∈ Q := (ha v hv).resolve_right hvQ
  rcases ha y hy with hya | hyQ
  · right
    have e : y * a * (v * a)⁻¹ = y * v⁻¹ := by group
    simpa only [e] using Q.mul_mem hya (Q.inv_mem hva)
  · exact Or.inl hyQ

section Geo2

variable (hC : GeoCtx G₀ G₁ G₂ T V z) (hev : Even (critDist G₀ G₁ G₂ V))
  (hb : 3 ≤ critDist G₀ G₁ G₂ V) {p : ℕ → CosetGeom G₀ G₁ G₂}
  (hp : IsGeo p (critDist G₀ G₁ G₂ V)) (hp0 : p 0 = γ₀ G₀ G₁ G₂) (hp1 : p 1 = γ₁ G₀ G₁ G₂)
  (hcrit : ¬ V ≤ ballStab 1 (p (critDist G₀ G₁ G₂ V)))

include hC hev hb hp hp0 hp1 hcrit

theorem exists_nbr_not_le_pCoreOf_u :
    ∃ β : CosetGeom G₀ G₁ G₂, (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β ∧ β ≠ γ₁ G₀ G₁ G₂ ∧
      ¬ Vv V β ≤ pCoreOf 2 (stab (p (critDist G₀ G₁ G₂ V - 1))) := by
  by_contra hcon
  set b := critDist G₀ G₁ G₂ V
  have hnbr : ∀ β, (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β → β ≠ γ₁ G₀ G₁ G₂ →
      Vv V β ≤ pCoreOf 2 (stab (p (b - 1))) := fun β h1 h2 => by
    by_contra h3
    exact hcon ⟨β, h1, h2, h3⟩
  have hN : G₁ ≤ Subgroup.normalizer (V : Set G) := hC.hyp.normalizes
  have h₁ : G₁ ≤ G₀ := hC.hyp.le₁
  have h₂ : G₂ ≤ G₀ := hC.hyp.le₂
  have hV0 : V ≠ ⊥ := V_ne_bot hC
  have hvt0 : vtype (p 0) = false := by rw [hp0]; exact vtype_γ₀
  have hvtb : vtype (p b) = false := (vtype_geo_false_iff hC hp hvt0 le_rfl).mpr hev
  have hvt1 : vtype (γ₁ G₀ G₁ G₂) = true := vtype_γ₁
  have hstab0 : stab (γ₀ G₀ G₁ G₂) = G₁ := stab_γ₀ h₁
  have hstab1 : stab (γ₁ G₀ G₁ G₂) = G₂ := stab_γ₁ h₂
  have hVγ₀ : Vv V (γ₀ G₀ G₁ G₂) = V := Vv_γ₀ hN
  have hd1u : dist (γ₁ G₀ G₁ G₂) (p (b - 1)) = b - 2 := by
    have h := hp 1 (b - 1) (by omega) (by omega)
    rw [hp1] at h
    omega
  have hdub : dist (p (b - 1)) (p b) = 1 := by
    have h := hp (b - 1) b (by omega) le_rfl
    omega
  have hd0b : dist (γ₀ G₀ G₁ G₂) (p b) = b := by
    have h := hp 0 b (by omega) le_rfl
    rw [hp0] at h
    omega
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup G, Y = ⨆ (β : CosetGeom G₀ G₁ G₂)
      (_ : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β), Vv V β := ⟨_, rfl⟩
  have hVβY : ∀ β, (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β → Vv V β ≤ Y := fun β hβ => by
    rw [hY]
    exact le_iSup₂_of_le β hβ le_rfl
  have hYle : ∀ K : Subgroup G,
      (∀ β, (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β → Vv V β ≤ K) → Y ≤ K := fun K hK => by
    rw [hY]
    exact iSup₂_le hK
  have hYN : G₁ ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hY]
    exact le_normalizer_iSup_Vv_nbrs hC
  have hYQ : Y ≤ pCoreOf 2 (stab (p (b - 1))) := by
    refine hYle _ fun β hβ => ?_
    by_cases hβ1 : β = γ₁ G₀ G₁ G₂
    · subst hβ1
      have hlt : dist (γ₁ G₀ G₁ G₂) (p (b - 1)) + 1 < b := by omega
      exact Vv_le_pCoreOf_of_dist_lt_B hC hvt1 hlt
    · exact hnbr β hβ hβ1
  have hYp : IsPGroup 2 Y := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hYQ
  have hYb : Y ≤ stab (p b) :=
    hYQ.trans ((ballStab_one_eq_pCoreOf hC (p (b - 1))).symm.le.trans
      (ballStab_le_stab_of_dist_le hdub.le))
  have hrel := relIndex_pCoreOf_le_two hC hvtb hYb hYp
  have hadj01 : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) := adj_γ₀_γ₁
  have hVW : V ≤ Vv V (γ₁ G₀ G₁ G₂) := hVγ₀.symm.le.trans (Vv_le_Vv_of_adj hadj01 vtype_γ₀)
  have hWY : Vv V (γ₁ G₀ G₁ G₂) ≤ Y := hVβY _ hadj01
  have hVY : V ≤ Y := hVW.trans hWY
  have hVQ : ¬ V ≤ pCoreOf 2 (stab (p b)) := by
    rw [← ballStab_one_eq_pCoreOf hC (p b)]
    exact hcrit
  obtain ⟨v₀, hv₀V, hv₀Q⟩ := IsConcreteLE.not_le_iff_exists.mp hVQ
  have hVstab : V ≤ stab (p b) := by
    have h := Vv_le_stab_of_dist_le hC (x := γ₀ G₀ G₁ G₂) (y := p b) vtype_γ₀ hd0b.le
    rwa [hVγ₀] at h
  have hv₀N : v₀ ∈ Subgroup.normalizer (Vv V (p b) : Set G) :=
    stab_le_normalizer_Vv hN (p b) (hVstab hv₀V)
  have hcrit' : ¬ Vv V (p 0) ≤ ballStab 1 (p b) := by
    rw [hp0, hVγ₀]
    exact hcrit
  obtain ⟨hcom1, hcom2, -, -⟩ := commutator_eq_Zv_of_geo hC hev hb hp hvt0 hcrit'
  rw [hp0, hVγ₀] at hcom1 hcom2
  have hQfix : ∀ q ∈ pCoreOf 2 (stab (p b)), ∀ w ∈ Vv V (p b), q * w * q⁻¹ = w := by
    intro q hq w hw
    have h := Subgroup.mem_centralizer_iff.mp (pCoreOf_le_centralizer_Vv hC hvtb hq) w hw
    calc q * w * q⁻¹ = w * q * q⁻¹ := by rw [h]
      _ = w := mul_inv_cancel_right w q
  have hcommV : ∀ y ∈ Y, ∀ w ∈ Vv V (p b), y * w * y⁻¹ * w⁻¹ ∈ V := by
    intro y hy w hw
    rcases mem_or_mul_inv_mem_of_relIndex_le_two hrel (hVY hv₀V) hv₀Q hy with hyQ | hq
    · rw [hQfix y hyQ w hw, mul_inv_cancel]
      exact V.one_mem
    · have hw' : v₀ * w * v₀⁻¹ ∈ Vv V (p b) := (Subgroup.mem_normalizer_iff.mp hv₀N w).mp hw
      have e : y * w * y⁻¹ * w⁻¹ =
          ((y * v₀⁻¹) * (v₀ * w * v₀⁻¹) * (y * v₀⁻¹)⁻¹) * w⁻¹ := by group
      rw [e, hQfix _ hq _ hw']
      have hmem := Subgroup.commutator_mem_commutator hv₀V hw
      rw [commutatorElement_def] at hmem
      exact (Subgroup.mem_inf.mp (hcom2 hmem)).1
  have hVbG₁ : Vv V (p b) ≤ G₁ := by
    have h := Vv_le_stab_of_dist_le hC (x := p b) (y := γ₀ G₀ G₁ G₂) hvtb
      (by rw [CosetGeom.dist_comm]; exact hd0b.le)
    rwa [hstab0] at h
  have hVbQ : ¬ Vv V (p b) ≤ pCoreOf 2 G₁ := by
    intro hle
    apply hcom1
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hle.trans (CosetGeom.pCoreOf_le_centralizer hC.hyp))
  have hG₂W : G₂ ≤ Subgroup.normalizer (Vv V (γ₁ G₀ G₁ G₂) : Set G) := by
    have h := stab_le_normalizer_Vv hN (γ₁ G₀ G₁ G₂)
    rwa [hstab1] at h
  have hG₁W : G₁ ≤ Subgroup.normalizer (Vv V (γ₁ G₀ G₁ G₂) : Set G) :=
    normalizes_of_normalClosure hC.hyp.sylow₁.1 hC.hyp.sylow₁.2.1 hC.index3 hN hYN hVW hWY
      (hC.hyp.sylow₂.1.trans hG₂W) hVbG₁ hVbQ hcommV
  have hG₀W : G₀ ≤ Subgroup.normalizer (Vv V (γ₁ G₀ G₁ G₂) : Set G) :=
    hC.hyp.gen.le.trans (sup_le hG₁W hG₂W)
  have hWG₂ : Vv V (γ₁ G₀ G₁ G₂) ≤ G₂ := by
    rw [Vv_γ₁ h₂ hN]
    exact conjClosure_le fun h hh v hv =>
      G₂.mul_mem (G₂.mul_mem hh (hC.klein.V_le hv)) (G₂.inv_mem hh)
  have hWp : IsPGroup 2 (Vv V (γ₁ G₀ G₁ G₂)) :=
    F7.isPGroup_of_isElemAbelian (isElemAbelian_Vv_of_vtype hC hvt1 hb)
  have hWo : Vv V (γ₁ G₀ G₁ G₂) ≤ pCoreOf 2 G₀ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hWG₂.trans h₂) hG₀W hWp
  rw [hC.hyp.o2_trivial] at hWo
  exact hV0 (le_bot_iff.mp (hVW.trans hWo))

end Geo2

end CFSG.Quasithin.SzVB

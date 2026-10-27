module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofMain
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarDiagB

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix

section U

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {n f : ℕ} {y : G} {K : Subgroup G}

theorem ggTypeAFar_abab_mem_K (hN : GGTypeANbrCfg p B Bs x L D J n f y K)
    {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G} (hL : φ₁.range = L)
    (hk₁ : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    (hK : φ₂.range = K)
    (hk₂ : φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    (hJ : (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J)
    (hc : φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
      φ₂.comp (slUpperBlockHom n (GaloisField 2 f)))
    (hdiag : ∀ c ∈ Bs, GGActsDiag φ₁ c ∧ GGActsDiag φ₂ c)
    {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n) {u : G}
    (hu : u = φ₁ (weylRep n (GaloisField 2 f) i) * φ₂ (weylRep n (GaloisField 2 f) j) *
      φ₁ (weylRep n (GaloisField 2 f) i) * φ₂ (weylRep n (GaloisField 2 f) j))
    (hCu : u ∈ Subgroup.centralizer (Bs : Set G)) : u ∈ K := by
  classical
  have hp : p.Prime := hN.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hN.one_le_f
  have h2 : (2 : GaloisField 2 f) = 0 :=
    two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf
  have hn : 3 ≤ n := hN.three_le
  have hBp := hN.exponent
  have hBs := hN.bs_centralizer
  have hLifts : GGFarLifts φ₁ φ₂ Bs :=
    ⟨hk₁, hk₂, hc, fun b hb => (hdiag b hb).1, fun b hb => (hdiag b hb).2⟩
  have hx := hN.x_mem
  have hy := hN.y_mem
  have hy1 := hN.y_ne_one
  have hmemL : ∀ s, φ₁ s ∈ L := fun s => by rw [← hL]; exact ⟨s, rfl⟩
  have hmemK : ∀ s, φ₂ s ∈ K := fun s => by rw [← hK]; exact ⟨s, rfl⟩
  have hxL : ∀ s, x * φ₁ s = φ₁ s * x := fun s => hN.x_comm_of_mem_L _ (hmemL s)
  have hyK : ∀ s, y * φ₂ s = φ₂ s * y := fun s => hN.y_comm_of_mem_K _ (hmemK s)
  have hxK : ¬ ∀ s, x * φ₂ s = φ₂ s * x := by
    intro h
    apply hN.not_x_comm_K
    intro k hk
    rw [← hK] at hk
    obtain ⟨s, rfl⟩ := hk
    exact h s
  have hinj : ∀ g ∈ Bs, (∀ s, g * φ₁ s = φ₁ s * g) → (∀ s, g * φ₂ s = φ₂ s * g) → g = 1 := by
    intro g hg h₁ h₂
    refine hN.eq_one_of_comm_L_K g hg (fun l hl => ?_) (fun k hk => ?_)
    · rw [← hL] at hl
      obtain ⟨s, rfl⟩ := hl
      exact h₁ s
    · rw [← hK] at hk
      obtain ⟨s, rfl⟩ := hk
      exact h₂ s
  have hF4 : 4 ≤ Nat.card (GaloisField 2 f) := hN.four_le_natCard
  have hFp : p ∣ Nat.card (GaloisField 2 f)ˣ := hN.dvd_natCard_units
  obtain ⟨a, ha⟩ : ∃ a, a = φ₁ (weylRep n (GaloisField 2 f) i) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = φ₂ (weylRep n (GaloisField 2 f) j) := ⟨_, rfl⟩
  obtain ⟨b₁, hb₁⟩ : ∃ b₁, b₁ = φ₂ (slPerm h2 (Equiv.swap i.castSucc j.succ)) := ⟨_, rfl⟩
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, b₀ = φ₂ (slPerm h2 (Equiv.swap i.castSucc j.castSucc)) := ⟨_, rfl⟩
  have hxu : (a * b * a * b) * x = x * (a * b * a * b) := by
    rw [ha, hb, ← hu]
    exact (Subgroup.mem_centralizer_iff.1 hCu x hx).symm
  have hyu : (a * b * a * b) * y = y * (a * b * a * b) := by
    rw [ha, hb, ← hu]
    exact (Subgroup.mem_centralizer_iff.1 hCu y hy).symm
  have hzw := ggTypeAFar_zpowers_eq h2 hLifts hBp hBs hn hi hj hx hy hy1 hxL hyK hxK hinj ha hb hb₁
    hxu hyu
  have ha2 : a * a = 1 := by rw [ha, ← map_mul, weylRep_mul_self n h2, map_one]
  have hb2 : b * b = 1 := by rw [hb, ← map_mul, weylRep_mul_self n h2, map_one]
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hb₀' : b₀ = φ₁ (slLowerBlockHom n (GaloisField 2 f) (slPerm h2 (Equiv.swap i j))) := by
    rw [hb₀, ggFar_c_eq h2 hc]
  have hb₀L : b₀ ∈ L := by rw [hb₀']; exact hmemL _
  have hbK : b ∈ K := by rw [hb]; exact hmemK _
  have hb₁b₀ : b₁ * b₀ * b₁⁻¹ = b := by
    rw [hb₁, hb₀, hb]
    exact ggFar_b₁_mul_c h2 hi hj (by omega) φ₂
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hi0 : i = 0 := Fin.ext hi
  have hic : i.castSucc = (0 : Fin (m + 1 + 1)) := Fin.ext (by simp [hi])
  have his : i.succ = (0 : Fin (m + 1)).succ := by rw [hi0]
  have hjs : j.succ = Fin.last (m + 1) := Fin.ext (by simp; omega)
  set ψ : SpecialLinearGroup (Fin m) (GaloisField 2 f) →* G :=
    (φ₁.comp (slLowerBlockHom (m + 1) (GaloisField 2 f))).comp
      (slLowerBlockHom m (GaloisField 2 f)) with hψ
  have hψK : ∀ s, ψ s = φ₂ (slUpperBlockHom (m + 1) (GaloisField 2 f)
      (slLowerBlockHom m (GaloisField 2 f) s)) := fun s => by
    have e := DFunLike.congr_fun hc (slLowerBlockHom m (GaloisField 2 f) s)
    simp only [MonoidHom.comp_apply] at e
    exact e
  have hψL : ∀ s, ψ s ∈ L := fun s => hmemL _
  have hψK' : ∀ s, ψ s ∈ K := fun s => by rw [hψK]; exact hmemK _
  have ha_comm : ∀ s, a * ψ s = ψ s * a := fun s => by
    have e := congrArg φ₁ (slPerm_swap_zero_one_commute_lowerLower h2 s)
    rw [map_mul, map_mul] at e
    rw [ha, ← slPerm_swap_castSucc_succ h2, hic, his]
    exact e
  have hb₁_comm : ∀ s, b₁ * ψ s = ψ s * b₁ := fun s => by
    have e := congrArg φ₂ (slPerm_swap_zero_last_commute_upperLower h2 s)
    rw [map_mul, map_mul] at e
    rw [hb₁, hic, hjs, hψK]
    exact e
  have hPa : ψ.range ≤ K.map (MulAut.conj a).toMonoidHom := by
    rintro _ ⟨s, rfl⟩
    refine mem_map_conj_iff.2 ⟨ψ s, hψK' s, ?_⟩
    rw [ha_comm s]
    group
  have hPb : ψ.range ≤ L.map (MulAut.conj b₁).toMonoidHom := by
    rintro _ ⟨s, rfl⟩
    refine mem_map_conj_iff.2 ⟨ψ s, hψL s, ?_⟩
    rw [hb₁_comm s]
    group
  have hperfY : Group.IsPerfect (SpecialLinearGroup (Fin m) (GaloisField 2 f)) :=
    slPerfect_of_four_le_card (by omega) hF4
  have hY : ψ.range ≤ ⁅ψ.range, ψ.range⁆ := range_le_commutator_of_isPerfect hperfY ψ
  obtain ⟨g, hgY, hg1, hgp⟩ := exists_orderP_mem_lowerLower hFp (by omega : 2 ≤ m) hk₁
  have hgJ : g ∈ J := by
    obtain ⟨s, rfl⟩ := hgY
    rw [← hJ]
    exact ⟨slLowerBlockHom m (GaloisField 2 f) s, rfl⟩
  have hpJ : p ∣ Nat.card J := by
    have h1 : orderOf (⟨g, hgJ⟩ : J) = p := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hgp hg1
    rw [← h1]
    exact orderOf_dvd_natCard _
  have hM : K.map (MulAut.conj a).toMonoidHom = L.map (MulAut.conj b₁).toMonoidHom :=
    eq_map_conj_of_pComponents a b₁ hN.pComponent_K (hN.pComponent_L hpJ) hzw hPa hPb hY hgY hg1
      hgp
  have hbM : b ∈ L.map (MulAut.conj b₁).toMonoidHom :=
    mem_map_conj_iff.2 ⟨b₀, hb₀L, hb₁b₀⟩
  have haM : a * b * a⁻¹ ∈ L.map (MulAut.conj b₁).toMonoidHom := by
    rw [← hM]
    exact mem_map_conj_iff.2 ⟨b, hbK, rfl⟩
  have huM : u ∈ K.map (MulAut.conj a).toMonoidHom := by
    have e : u = (a * b * a⁻¹) * b := by rw [hu, ← ha, ← hb, ha']
    rw [e, hM]
    exact Subgroup.mul_mem _ haM hbM
  have hau : a * u * a = u⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, hu, ← ha, ← hb]
    calc a * (a * b * a * b) * a * (a * b * a * b)
        = (a * a) * b * a * b * (a * a) * b * a * b := by group
      _ = b * a * (b * b) * a * b := by rw [ha2]; group
      _ = b * (a * a) * b := by rw [hb2]; group
      _ = 1 := by rw [ha2, mul_one, hb2]
  obtain ⟨k, hkK, hk⟩ := mem_map_conj_iff.1 huM
  have hk' : k = u⁻¹ := by
    calc k = a⁻¹ * (a * k * a⁻¹) * a := by group
      _ = a⁻¹ * u * a := by rw [hk]
      _ = a * u * a := by rw [ha']
      _ = u⁻¹ := hau
  have hinv : u⁻¹ ∈ K := hk' ▸ hkK
  simpa using K.inv_mem hinv

end U

theorem ggTypeACompatFarExCfgInput_of_diagB (hD : GGTypeACompatDiagBInput) :
    GGTypeACompatFarExCfgInput := by
  intro G _ _ p B Bs x L D J n f y K hN
  have hn : 3 ≤ n := hN.three_le
  have hf : 1 ≤ f := hN.one_le_f
  have h2 : (2 : GaloisField 2 f) = 0 :=
    two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf
  obtain ⟨φ₁, φ₂, hL, hk₁, hK, hk₂, hJ, hc, hdiag⟩ := hD G p B Bs x L D J n f y K hN
  refine ⟨φ₁, φ₂, hL, hk₁, hK, hk₂, hJ, hc, fun i j hi hj => ?_⟩
  have hCu := ggTypeABstarFar_of_bstarDiag hN hL hk₁ hK hk₂ hJ hc hdiag hi hj
  have huK := ggTypeAFar_abab_mem_K hN hL hk₁ hK hk₂ hJ hc hdiag hi hj rfl hCu
  rw [← hK] at huK
  obtain ⟨s, hs⟩ := huK
  have hLifts : GGFarLifts φ₁ φ₂ Bs :=
    ⟨hk₁, hk₂, hc, fun b hb => (hdiag b hb).1, fun b hb => (hdiag b hb).2⟩
  have hmemL : ∀ s, φ₁ s ∈ L := fun s => by rw [← hL]; exact ⟨s, rfl⟩
  have hxL : ∀ s, x * φ₁ s = φ₁ s * x := fun s => hN.x_comm_of_mem_L _ (hmemL s)
  have hxK : ¬ ∀ s, x * φ₂ s = φ₂ s * x := by
    intro h
    apply hN.not_x_comm_K
    intro k hk
    rw [← hK] at hk
    obtain ⟨s, rfl⟩ := hk
    exact h s
  obtain ⟨τ, hτ, -, hxv⟩ := ggFar_shape_x hLifts hN.x_mem hxL hxK
  have hS : ∀ r : Fin (n + 1), ∃ g : G, ∃ τ : (GaloisField 2 f)ˣ, τ ≠ 1 ∧
      GGActsVec φ₂ g (diagAt r τ) ∧ g * φ₂ s = φ₂ s * g := by
    intro r
    obtain ⟨g, hgB, hgv⟩ := exists_mem_actsVec_diagAt h2 hN.exponent hN.bs_centralizer hk₂
      (fun b hb => (hdiag b hb).2) hN.x_mem hxv r
    refine ⟨g, τ, hτ, hgv, ?_⟩
    rw [hs]
    exact Subgroup.mem_centralizer_iff.1 hCu g hgB
  obtain ⟨h', hh'⟩ := ggActsDiag_of_commute_diagAt (by omega) h2 hk₂ hS
  rw [hs] at hh'
  have hperfK : Group.IsPerfect (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) :=
    slPerfect_of_four_le_card (by omega) hN.four_le_natCard
  exact commute_of_ggDiagConj_right h2 odd_natCard_units_of_charTwo hn hk₁ hk₂ hc hi hj rfl
    hh' (fun hcent huu =>
      eq_one_of_mem_range_of_centralizes hperfK odd_natCard_units_of_charTwo hk₂ ⟨s, hs⟩ hcent huu)

end CFSG.StandardType

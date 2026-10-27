module

public import CFSG.LocalAnalysis.StandardType.GGTypeACompatFarB
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCfg

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix

private theorem ggFarCtx_abab_mem_range₂ {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} {n f : ℕ}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G} {x y : G}
    (hC : GGFarCtx p Bs φ₁ φ₂ x y) (hFp : p ∣ Nat.card (GaloisField 2 f)ˣ)
    (hPL : LargeEvenPComponent p (Subgroup.centralizer ({x} : Set G)) φ₁.range)
    (hPK : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) φ₂.range)
    {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n) {u : G}
    (hu : u = φ₁ (weylRep n (GaloisField 2 f) i) * φ₂ (weylRep n (GaloisField 2 f) j) *
      φ₁ (weylRep n (GaloisField 2 f) i) * φ₂ (weylRep n (GaloisField 2 f) j))
    (hCu : u ∈ Subgroup.centralizer (Bs : Set G)) : u ∈ φ₂.range := by
  classical
  have hp : p.Prime := hC.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : GaloisField 2 f) = 0 := hC.two
  have hn : 3 ≤ n := hC.three_le
  have hBp := hC.exp
  have hBs := hC.cent
  have hLifts : GGFarLifts φ₁ φ₂ Bs := hC.lifts
  have hx := hC.x_mem
  have hy := hC.y_mem
  have hy1 := hC.y_ne
  have hmemL : ∀ s, φ₁ s ∈ φ₁.range := fun s => ⟨s, rfl⟩
  have hmemK : ∀ s, φ₂ s ∈ φ₂.range := fun s => ⟨s, rfl⟩
  have hxL : ∀ s, x * φ₁ s = φ₁ s * x := hC.x_comm
  have hyK : ∀ s, y * φ₂ s = φ₂ s * y := hC.y_comm
  have hxK : ¬ ∀ s, x * φ₂ s = φ₂ s * x := hC.x_ncomm
  have hinj := hC.inj
  have hF4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    have hp3 : 3 ≤ p := hp.odd_iff.mp (hp.odd_of_ne_two hC.odd)
    have hpos : 0 < Nat.card (GaloisField 2 f)ˣ := Nat.card_pos
    have hle : p ≤ Nat.card (GaloisField 2 f)ˣ := Nat.le_of_dvd hpos hFp
    have hcard : Nat.card (GaloisField 2 f) = Nat.card (GaloisField 2 f)ˣ + 1 :=
      Nat.card_eq_card_units_add_one (α := GaloisField 2 f)
    omega
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
  have hzw := ggTypeAFar_zpowers_eq h2 hLifts hBp hBs hn hi hj hx hy hy1 hxL hyK hxK hinj ha hb
    hb₁ hxu hyu
  have ha2 : a * a = 1 := by rw [ha, ← map_mul, weylRep_mul_self n h2, map_one]
  have hb2 : b * b = 1 := by rw [hb, ← map_mul, weylRep_mul_self n h2, map_one]
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hb₀' : b₀ = φ₁ (slLowerBlockHom n (GaloisField 2 f) (slPerm h2 (Equiv.swap i j))) := by
    rw [hb₀, ggFar_c_eq h2 hC.lifts.compat]
  have hb₀L : b₀ ∈ φ₁.range := by rw [hb₀']; exact hmemL _
  have hbK : b ∈ φ₂.range := by rw [hb]; exact hmemK _
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
    have e := DFunLike.congr_fun hC.lifts.compat (slLowerBlockHom m (GaloisField 2 f) s)
    simp only [MonoidHom.comp_apply] at e
    exact e
  have hψL : ∀ s, ψ s ∈ φ₁.range := fun s => hmemL _
  have hψK' : ∀ s, ψ s ∈ φ₂.range := fun s => by rw [hψK]; exact hmemK _
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
  have hPa : ψ.range ≤ φ₂.range.map (MulAut.conj a).toMonoidHom := by
    rintro _ ⟨s, rfl⟩
    refine mem_map_conj_iff.2 ⟨ψ s, hψK' s, ?_⟩
    rw [ha_comm s]
    group
  have hPb : ψ.range ≤ φ₁.range.map (MulAut.conj b₁).toMonoidHom := by
    rintro _ ⟨s, rfl⟩
    refine mem_map_conj_iff.2 ⟨ψ s, hψL s, ?_⟩
    rw [hb₁_comm s]
    group
  have hperfY : Group.IsPerfect (SpecialLinearGroup (Fin m) (GaloisField 2 f)) :=
    slPerfect_of_four_le_card (by omega) hF4
  have hY : ψ.range ≤ ⁅ψ.range, ψ.range⁆ := range_le_commutator_of_isPerfect hperfY ψ
  obtain ⟨g, hgY, hg1, hgp⟩ := exists_orderP_mem_lowerLower hFp (by omega : 2 ≤ m) hC.lifts.ker₁
  have hM : φ₂.range.map (MulAut.conj a).toMonoidHom =
      φ₁.range.map (MulAut.conj b₁).toMonoidHom :=
    eq_map_conj_of_pComponents a b₁ hPK hPL hzw hPa hPb hY hgY hg1 hgp
  have hbM : b ∈ φ₁.range.map (MulAut.conj b₁).toMonoidHom :=
    mem_map_conj_iff.2 ⟨b₀, hb₀L, hb₁b₀⟩
  have haM : a * b * a⁻¹ ∈ φ₁.range.map (MulAut.conj b₁).toMonoidHom := by
    rw [← hM]
    exact mem_map_conj_iff.2 ⟨b, hbK, rfl⟩
  have huM : u ∈ φ₂.range.map (MulAut.conj a).toMonoidHom := by
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
  have hinv : u⁻¹ ∈ φ₂.range := hk' ▸ hkK
  simpa using (φ₂.range).inv_mem hinv

theorem GGFarCtx.commute_weylRep_of_pComponents {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} {n f : ℕ}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G} {x y : G}
    (hC : GGFarCtx p Bs φ₁ φ₂ x y) (hFp : p ∣ Nat.card (GaloisField 2 f)ˣ)
    (hPL : LargeEvenPComponent p (Subgroup.centralizer ({x} : Set G)) φ₁.range)
    (hPK : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) φ₂.range)
    {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n)
    (hCu : φ₁ (weylRep n (GaloisField 2 f) i) * φ₂ (weylRep n (GaloisField 2 f) j) *
        φ₁ (weylRep n (GaloisField 2 f) i) * φ₂ (weylRep n (GaloisField 2 f) j) ∈
      Subgroup.centralizer (Bs : Set G)) :
    Commute (φ₂ (weylRep n (GaloisField 2 f) j)) (φ₁ (weylRep n (GaloisField 2 f) i)) := by
  classical
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    have hp3 : 3 ≤ p := hC.prime.odd_iff.mp (hC.prime.odd_of_ne_two hC.odd)
    have hpos : 0 < Nat.card (GaloisField 2 f)ˣ := Nat.card_pos
    have hle : p ≤ Nat.card (GaloisField 2 f)ˣ := Nat.le_of_dvd hpos hFp
    have hcard : Nat.card (GaloisField 2 f) = Nat.card (GaloisField 2 f)ˣ + 1 :=
      Nat.card_eq_card_units_add_one (α := GaloisField 2 f)
    omega
  have huK := ggFarCtx_abab_mem_range₂ hC hFp hPL hPK hi hj rfl hCu
  obtain ⟨s, hs⟩ := huK
  have h2 : (2 : GaloisField 2 f) = 0 := hC.two
  obtain ⟨τ, hτ, -, hxv⟩ := ggFar_shape_x hC.lifts hC.x_mem hC.x_comm hC.x_ncomm
  have hS : ∀ r : Fin (n + 1), ∃ g : G, ∃ τ : (GaloisField 2 f)ˣ, τ ≠ 1 ∧
      GGActsVec φ₂ g (diagAt r τ) ∧ g * φ₂ s = φ₂ s * g := by
    intro r
    obtain ⟨g, hgB, hgv⟩ := exists_mem_actsVec_diagAt h2 hC.exp hC.cent hC.lifts.ker₂
      hC.lifts.diag₂ hC.x_mem hxv r
    refine ⟨g, τ, hτ, hgv, ?_⟩
    rw [hs]
    exact Subgroup.mem_centralizer_iff.1 hCu g hgB
  obtain ⟨h', hh'⟩ := ggActsDiag_of_commute_diagAt (by omega) h2 hC.lifts.ker₂ hS
  rw [hs] at hh'
  have hperfK : Group.IsPerfect (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) :=
    slPerfect_of_four_le_card (by omega) h4
  exact commute_of_ggDiagConj_right h2 odd_natCard_units_of_charTwo hC.three_le hC.lifts.ker₁
    hC.lifts.ker₂ hC.lifts.compat hi hj rfl hh' (fun hcent huu =>
      eq_one_of_mem_range_of_centralizes hperfK odd_natCard_units_of_charTwo hC.lifts.ker₂
        ⟨s, hs⟩ hcent huu)

private theorem ggFarCfg_dvd_card_J {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}
    (h : GGTypeANbrCfg p B Bs x L D J n f y K)
    {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G}
    (hC : GGFarCtx p Bs φ₁ φ₂ x y)
    (hJ : (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J) :
    p ∣ Nat.card J := by
  have hp : p.Prime := hC.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 3 ≤ n := hC.three_le
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  obtain ⟨g, hg, hg1, hgp⟩ :=
    exists_orderP_mem_lowerLower (F := GaloisField 2 f) (X := G) (p := p) h.dvd_natCard_units
      (m := N) (by omega) hC.lifts.ker₁
  have hgJ : g ∈ J := by
    obtain ⟨s, hs⟩ := hg
    rw [← hs, ← hJ]
    exact ⟨slLowerBlockHom N (GaloisField 2 f) s, rfl⟩
  have h1 : orderOf (⟨g, hgJ⟩ : J) = p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hgp hg1
  rw [← h1]
  exact orderOf_dvd_natCard _

theorem GGTypeANbrCfg.commute_weylRep_of_diag {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}
    (hN : GGTypeANbrCfg p B Bs x L D J n f y K)
    {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G} (hL : φ₁.range = L)
    (hk₁ : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    (hK : φ₂.range = K)
    (hk₂ : φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    (hJ : (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J)
    (hc : φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
      φ₂.comp (slUpperBlockHom n (GaloisField 2 f)))
    (hdiag : ∀ c ∈ Bs, GGActsDiag φ₁ c ∧ GGActsDiag φ₂ c) {i j : Fin n} (hi : i.val = 0)
    (hj : j.val + 1 = n) :
    Commute (φ₂ (weylRep n (GaloisField 2 f) j)) (φ₁ (weylRep n (GaloisField 2 f) i)) := by
  have hC : GGFarCtx p Bs φ₁ φ₂ x y := ggFarCtx_of_cfg hN hL hk₁ hK hk₂ hc hdiag
  refine hC.commute_weylRep_of_pComponents hN.dvd_natCard_units ?_ ?_ hi hj ?_
  · rw [hL]
    exact hN.pComponent_L (ggFarCfg_dvd_card_J hN hC hJ)
  · rw [hK]
    exact hN.pComponent_K
  · exact ggTypeABstarFar_of_bstarDiag hN hL hk₁ hK hk₂ hJ hc hdiag hi hj

end CFSG.StandardType

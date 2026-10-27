module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.Setup
import CFSG.LocalAnalysis.StandardType.FF81.PropOne.LiftData
import CFSG.LocalAnalysis.StandardType.FF81.PropOne.LMonomial
import CFSG.LocalAnalysis.StandardType.FF81.PropOne.LNormalizer
import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B2Exp
import CFSG.Mathlib.GroupTheory.OddInvariantSylow
import CFSG.LocalAnalysis.StandardType.FF81.LocalSetupCen

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.RankThree.PartTwo.Sec21.FF81.Lift
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

structure B2Package {G : Type} [Group G] (b : G) {L : Subgroup G} (z : Fin 3 → ↥L)
    (B₂ : Subgroup G) : Prop where
  le_nor : B₂ ≤ nB b z
  abel : CFSG.Open.IsElemAbelian 3 B₂
  card : Nat.card B₂ = 3 ^ 6
  B₁_le : bOne z ≤ B₂
  b_nor : ∀ x ∈ B₂, b * x * b⁻¹ ∈ B₂
  comm : ∀ x ∈ B₂, b * x * b⁻¹ * x⁻¹ ∈ bOne z
  fix : ∀ x ∈ B₂, x * b = b * x → x ∈ bOne z
  D_nor : ∀ g ∈ L ⊓ Subgroup.normalizer ((bOne z : Subgroup G) : Set G),
    ∀ x ∈ B₂, g * x * g⁻¹ ∈ B₂
  tau_inv : ∀ τ ∈ L, (∀ i : Fin 3, τ * GGFF.zs z i * τ⁻¹ = (GGFF.zs z i)⁻¹) →
    ∀ x ∈ B₂, τ * x * τ⁻¹ = x⁻¹

theorem exists_b2Package {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (hB₁ : ∀ m ∈ nB b z, ∀ y ∈ bOne z, m * y * m⁻¹ ∈ bOne z)
    (hodd : Odd (Nat.card ↥(cB b z))) : ∃ B₂ : Subgroup G, B2Package b z B₂ := by
  let b₁ : G := GGFF.zs z 0
  let b₂ : G := GGFF.zs z 1
  let b₃ : G := GGFF.zs z 2
  let D : Data b b₁ b₂ b₃ := lift_data h hB₁
  let B₁ : Subgroup G := BO b₁ b₂ b₃
  have hB1eq : bOne z = B₁ := GGFF.SettingCore.tor_eq_closure z
  have hBteq : GGFF.Bt b z = BB b b₁ b₂ b₃ := GGFF.SettingCore.Bt_eq_closure b z
  have hB₁L : B₁ ≤ L := by
    rw [← hB1eq]
    exact GGFF.SettingCore.tor_le z
  have hodd' : Odd (Nat.card ↥(Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G))) := by
    rw [← hBteq]
    exact hodd
  have hÂodd : Odd (Nat.card ↥(Ahat B₁ b)) := by
    by_contra hc
    have h2 : 2 ∣ Nat.card ↥(Ahat B₁ b) :=
      even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hc)
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have htmem : (t : G) ∈ Ahat B₁ b := t.2
    have hβmem : beta b (t : G) ∈ B₁ := beta_mem htmem
    have ht2 : (t : G) ^ 2 = 1 := by
      have hord : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
      rw [← hord]
      exact pow_orderOf_eq_one _
    have hβ2 : (beta b (t : G)) ^ 2 = 1 := by
      have h := D.beta_pow htmem 2
      rw [ht2, D.beta_one] at h
      exact h.symm
    have hβ3 : (beta b (t : G)) ^ 3 = 1 := D.B₁3 _ hβmem
    have hβ1 : beta b (t : G) = 1 := by
      have h := pow_gcd_eq_one.mpr ⟨hβ2, hβ3⟩
      rwa [show Nat.gcd 2 3 = 1 from by norm_num, pow_one] at h
    have htcen : (t : G) ∈ Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) :=
      D.mem_cen_of_beta htmem hβ1
    have h2dvd : 2 ∣ Nat.card ↥(Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)) := by
      have h := Subgroup.orderOf_dvd_natCard
        (Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G)) htcen
      rwa [show orderOf (t : G) = 2 from by rw [Subgroup.orderOf_coe, ht]] at h
    exact (Odd.not_two_dvd_nat hodd') h2dvd
  have hDg_nor : dGrp b z ≤ Subgroup.normalizer (Ahat B₁ b : Set G) := by
    change Subgroup.zpowers b ⊔ (L ⊓ Subgroup.normalizer ((bOne z : Subgroup G) : Set G)) ≤
      Subgroup.normalizer (Ahat B₁ b : Set G)
    refine sup_le ?_ ?_
    · refine Subgroup.zpowers_le.mpr ?_
      have hbnor : b ∈ Subgroup.normalizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) :=
        Subgroup.le_normalizer D.b_mem_B
      exact GGFF.mem_nor_of_conj_mem fun x hx => D.conj_mem_Ahat hbnor hx
    · rintro g ⟨hgL, hgN₁⟩
      have hgb : g * b * g⁻¹ = b := by
        have hbg : g * b = b * g :=
          ((Subgroup.mem_centralizer_iff.mp (h.hypA.le hgL)) b (Set.mem_singleton b)).symm
        rw [hbg, mul_inv_cancel_right]
      have hgN₁' : g ∈ Subgroup.normalizer (B₁ : Set G) := by rwa [hB1eq] at hgN₁
      refine GGFF.mem_nor_of_conj_mem fun x hx => ?_
      have hx1 : ∀ y ∈ B₁, x * y * x⁻¹ = y :=
        ((mem_Ahat (B₁ := B₁) (b := b)).mp hx).1
      have hx2 : x * b * x⁻¹ * b⁻¹ ∈ B₁ :=
        ((mem_Ahat (B₁ := B₁) (b := b)).mp hx).2
      refine (mem_Ahat (B₁ := B₁) (b := b)).mpr ⟨?_, ?_⟩
      · intro y hy
        have hy' : g⁻¹ * y * g ∈ B₁ := by
          have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hgN₁') y).mp hy
          rwa [inv_inv] at h
        calc g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹
            = g * (x * (g⁻¹ * y * g) * x⁻¹) * g⁻¹ := by group
          _ = g * (g⁻¹ * y * g) * g⁻¹ := by rw [hx1 _ hy']
          _ = y := by group
      · change beta b (g * x * g⁻¹) ∈ B₁
        rw [beta_conj hgb x]
        exact (Subgroup.mem_normalizer_iff.mp hgN₁' (beta b x)).mp hx2
  obtain ⟨S, hSÂ, hSp, hSmax, hDgS⟩ :=
    CFSG.OddInvariantSylow.exists_isPGroup_normalizer (Y := Ahat B₁ b) (D := dGrp b z)
      hÂodd hDg_nor (isSolvable_dGrp h) (prime_eq_two_or_three_of_dvd_dGrp h)
  have hb_p : IsPGroup 3 (Subgroup.zpowers b : Subgroup G) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.hypA.ord]; norm_num)
  have hB₁p : IsPGroup 3 B₁ :=
    IsPGroup.of_card (n := 3) (by rw [D.B₁card]; norm_num)
  have hbDg : b ∈ dGrp b z := by
    change b ∈ Subgroup.zpowers b ⊔ (L ⊓ Subgroup.normalizer ((bOne z : Subgroup G) : Set G))
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hb_mem_S : b ∈ S := by
    have hsup : S ⊔ Subgroup.zpowers b ≤ Ahat B₁ b :=
      sup_le hSÂ (Subgroup.zpowers_le.mpr (D.B_le_Ahat D.b_mem_B))
    have h3 : IsPGroup 3 (S ⊔ Subgroup.zpowers b : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hSp hb_p (Subgroup.zpowers_le.mpr (hDgS hbDg))
    have hEq : S ⊔ Subgroup.zpowers b = S := hSmax _ hsup h3 le_sup_left
    have hb : b ∈ S ⊔ Subgroup.zpowers b := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    rwa [hEq] at hb
  have hB₁Â : B₁ ≤ Ahat B₁ b := by
    intro y hy
    refine (mem_Ahat (B₁ := B₁) (b := b)).mpr ⟨?_, ?_⟩
    · intro z hz
      rw [D.B₁ab y hy z hz, mul_inv_cancel_right]
    · change beta b y ∈ B₁
      rw [beta_one_of_mem D.bB₁ hy]
      exact B₁.one_mem
  have hB₁Dg : B₁ ≤ dGrp b z := by
    intro y hy
    change y ∈ Subgroup.zpowers b ⊔ (L ⊓ Subgroup.normalizer ((bOne z : Subgroup G) : Set G))
    refine Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hB₁L hy, ?_⟩)
    rw [hB1eq]
    exact Subgroup.le_normalizer hy
  have hB₁_normS : B₁ ≤ Subgroup.normalizer (S : Set G) := hB₁Dg.trans hDgS
  have hB₁_mem_S : B₁ ≤ S := by
    have hsup : S ⊔ B₁ ≤ Ahat B₁ b := sup_le hSÂ hB₁Â
    have h3 : IsPGroup 3 (S ⊔ B₁ : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hSp hB₁p hB₁_normS
    have hEq : S ⊔ B₁ = S := hSmax _ hsup h3 le_sup_left
    intro y hy
    have hy' : y ∈ S ⊔ B₁ := Subgroup.mem_sup_right hy
    rwa [hEq] at hy'
  have hB_le_S : BB b b₁ b₂ b₃ ≤ S := by
    rw [D.B_eq_sup]
    exact sup_le (Subgroup.zpowers_le.mpr hb_mem_S) hB₁_mem_S
  obtain ⟨τ, _c, hTauC⟩ := exists_tauC h
  have hτL : τ ∈ L := hTauC.tau_mem
  have hτb : τ * b * τ⁻¹ = b := by
    have hbg : τ * b = b * τ :=
      ((Subgroup.mem_centralizer_iff.mp (h.hypA.le hτL)) b (Set.mem_singleton b)).symm
    rw [hbg, mul_inv_cancel_right]
  have tau_inv_bOne : ∀ y ∈ B₁, τ * y * τ⁻¹ = y⁻¹ := by
    change ∀ y ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G), τ * y * τ⁻¹ = y⁻¹
    refine conj_inv_of_closure (S := ({b₁, b₂, b₃} : Set G)) D.B₁ab (g := τ) ?_
    rintro s (rfl | rfl | rfl)
    exacts [hTauC.inv 0, hTauC.inv 1, hTauC.inv 2]
  have hτN₁ : τ ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := by
    rw [hB1eq]
    exact GGFF.mem_nor_of_conj_mem fun y hy => by
      rw [tau_inv_bOne y hy]
      exact B₁.inv_mem hy
  have hτDg : τ ∈ dGrp b z := by
    change τ ∈ Subgroup.zpowers b ⊔ (L ⊓ Subgroup.normalizer ((bOne z : Subgroup G) : Set G))
    exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hτL, hτN₁⟩)
  have hτS : ∀ x ∈ S, τ * x * τ⁻¹ ∈ S :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp (hDgS hτDg) x).mp hx
  have hτ2 : ∀ x ∈ S, τ * (τ * x * τ⁻¹) * τ⁻¹ = x := by
    intro x _
    have hττ : τ * τ = 1 := by
      have hs := hTauC.tau_sq
      rwa [pow_two] at hs
    calc τ * (τ * x * τ⁻¹) * τ⁻¹ = (τ * τ) * x * (τ⁻¹ * τ⁻¹) := by group
      _ = x := by rw [hττ, inv_eq_of_mul_eq_one_right hττ, hττ]; group
  have hSÂ' : S ≤ Ahat (bOne z) b := by
    rw [hB1eq]
    exact hSÂ
  have hSmax' : ∀ R : Subgroup G, R ≤ Ahat (bOne z) b → IsPGroup 3 R → S ≤ R → R = S := by
    intro R hR hRp hSR
    rw [hB1eq] at hR
    exact hSmax R hR hRp hSR
  have hBA' : GGFF.Bt b z ≤ S := by rw [hBteq]; exact hB_le_S
  obtain ⟨B₂, hB₂iff, hB₂abel, hB₂card, hB₂tauinv, hB₂fix, hB₂nor⟩ :=
    exists_b2_of_sylow h hB₁ hSÂ' hSp hSmax' hBA' hτS hτ2 hτb hTauC.inv
  have hB₂_le_S : B₂ ≤ S := fun x hx => ((hB₂iff x).mp hx).1
  have hS_le_nB : S ≤ nB b z := by
    intro x hx
    change x ∈ Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G)
    rw [hBteq]
    exact D.Ahat_le_N (hSÂ hx)
  have hle_nor : B₂ ≤ nB b z := hB₂_le_S.trans hS_le_nB
  have hB₁_le_B₂ : bOne z ≤ B₂ := by
    intro y hy
    have hyB₁ : y ∈ B₁ := by rwa [hB1eq] at hy
    rw [hB₂iff]
    refine ⟨hB₁_mem_S hyB₁, ?_⟩
    rw [tau_inv_bOne y hyB₁, inv_mul_cancel]
    exact (bOne z).one_mem
  have hcomm : ∀ x ∈ B₂, b * x * b⁻¹ * x⁻¹ ∈ bOne z := by
    intro x hx
    have hxÂ : x ∈ Ahat B₁ b := hSÂ (hB₂_le_S hx)
    have hβ : beta b x ∈ B₁ := ((mem_Ahat (B₁ := B₁) (b := b)).mp hxÂ).2
    have he : b * x * b⁻¹ * x⁻¹ = (beta b x)⁻¹ := by
      rw [beta_def]; group
    rw [he]
    have : (beta b x)⁻¹ ∈ bOne z := by
      rw [hB1eq]
      exact B₁.inv_mem hβ
    exact this
  have hb_nor : ∀ x ∈ B₂, b * x * b⁻¹ ∈ B₂ := by
    intro x hx
    refine hB₂nor b ?_ ?_ ?_ x hx
    · change b ∈ Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G)
      rw [hBteq]
      exact Subgroup.le_normalizer D.b_mem_B
    · intro y hy
      exact (Subgroup.mem_normalizer_iff.mp (hDgS hbDg) y).mp hy
    · have hτb_comm : τ * b = b * τ :=
        ((Subgroup.mem_centralizer_iff.mp (h.hypA.le hτL)) b (Set.mem_singleton b)).symm
      change b⁻¹ * τ * b * τ⁻¹ ∈ Subgroup.centralizer ((GGFF.Bt b z : Subgroup G) : Set G)
      rw [show b⁻¹ * τ * b * τ⁻¹ = 1 by
        rw [show b⁻¹ * τ * b * τ⁻¹ = b⁻¹ * (τ * b) * τ⁻¹ by group, hτb_comm]; group]
      exact Subgroup.one_mem _
  have hD_nor : ∀ g ∈ L ⊓ Subgroup.normalizer ((bOne z : Subgroup G) : Set G),
      ∀ x ∈ B₂, g * x * g⁻¹ ∈ B₂ := by
    intro g hg x hx
    obtain ⟨hgL, hgN₁⟩ := hg
    have hgb : g * b * g⁻¹ = b := by
      have hbg : g * b = b * g :=
        ((Subgroup.mem_centralizer_iff.mp (h.hypA.le hgL)) b (Set.mem_singleton b)).symm
      rw [hbg, mul_inv_cancel_right]
    have hgN₁' : g ∈ Subgroup.normalizer (B₁ : Set G) := by rwa [hB1eq] at hgN₁
    have hg_nB : g ∈ nB b z := by
      change g ∈ Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G)
      refine GGFF.SettingCore.mem_nor_Bt (n := g) (b := b) (z := z) ?_ ?_
      · rw [hgb]; exact GGFF.SettingCore.b_mem_Bt b z
      · intro i
        have hzi : GGFF.zs z i ∈ bOne z := Subgroup.subset_closure (Set.mem_range_self i)
        have hmem : g * GGFF.zs z i * g⁻¹ ∈ bOne z :=
          (Subgroup.mem_normalizer_iff.mp hgN₁ (GGFF.zs z i)).mp hzi
        exact Subgroup.mem_sup_right hmem
    have hgS : ∀ y ∈ S, g * y * g⁻¹ ∈ S := by
      have hgDg : g ∈ dGrp b z := by
        change g ∈ Subgroup.zpowers b ⊔ (L ⊓ Subgroup.normalizer ((bOne z : Subgroup G) : Set G))
        exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hgL, hgN₁⟩)
      intro y hy
      exact (Subgroup.mem_normalizer_iff.mp (hDgS hgDg) y).mp hy
    have hu_b : (g⁻¹ * τ * g * τ⁻¹) * b * (g⁻¹ * τ * g * τ⁻¹)⁻¹ = b := by
      have hτib : τ⁻¹ * b * τ = b := inv_conj_of_conj hτb
      have hgib : g⁻¹ * b * g = b := inv_conj_of_conj hgb
      calc (g⁻¹ * τ * g * τ⁻¹) * b * (g⁻¹ * τ * g * τ⁻¹)⁻¹
          = (g⁻¹ * τ * g) * (τ⁻¹ * b * τ) * (g⁻¹ * τ * g)⁻¹ := by group
        _ = (g⁻¹ * τ * g) * b * (g⁻¹ * τ * g)⁻¹ := by rw [hτib]
        _ = g⁻¹ * (τ * (g * b * g⁻¹) * τ⁻¹) * g := by group
        _ = g⁻¹ * (τ * b * τ⁻¹) * g := by rw [hgb]
        _ = g⁻¹ * b * g := by rw [hτb]
        _ = b := hgib
    have hu_gen : ∀ i : Fin 3,
        (g⁻¹ * τ * g * τ⁻¹) * GGFF.zs z i * (g⁻¹ * τ * g * τ⁻¹)⁻¹ = GGFF.zs z i := by
      intro i
      have hτii : τ⁻¹ * GGFF.zs z i * τ = (GGFF.zs z i)⁻¹ := by
        have h1 : τ * (GGFF.zs z i)⁻¹ * τ⁻¹ = GGFF.zs z i := by
          rw [show τ * (GGFF.zs z i)⁻¹ * τ⁻¹ = (τ * GGFF.zs z i * τ⁻¹)⁻¹ by group,
            hTauC.inv i, inv_inv]
        exact inv_conj_of_conj h1
      have hginv_i : (g⁻¹ * τ * g) * GGFF.zs z i * (g⁻¹ * τ * g)⁻¹ = (GGFF.zs z i)⁻¹ := by
        have hziB₁ : GGFF.zs z i ∈ B₁ := by
          rw [← hB1eq]
          exact Subgroup.subset_closure (Set.mem_range_self i)
        have hgy : g * GGFF.zs z i * g⁻¹ ∈ B₁ :=
          (Subgroup.mem_normalizer_iff.mp hgN₁' _).mp hziB₁
        calc (g⁻¹ * τ * g) * GGFF.zs z i * (g⁻¹ * τ * g)⁻¹
            = g⁻¹ * (τ * (g * GGFF.zs z i * g⁻¹) * τ⁻¹) * g := by group
          _ = g⁻¹ * (g * GGFF.zs z i * g⁻¹)⁻¹ * g := by rw [tau_inv_bOne _ hgy]
          _ = (GGFF.zs z i)⁻¹ := by group
      calc (g⁻¹ * τ * g * τ⁻¹) * GGFF.zs z i * (g⁻¹ * τ * g * τ⁻¹)⁻¹
          = (g⁻¹ * τ * g) * (τ⁻¹ * GGFF.zs z i * τ) * (g⁻¹ * τ * g)⁻¹ := by group
        _ = (g⁻¹ * τ * g) * (GGFF.zs z i)⁻¹ * (g⁻¹ * τ * g)⁻¹ := by rw [hτii]
        _ = ((g⁻¹ * τ * g) * GGFF.zs z i * (g⁻¹ * τ * g)⁻¹)⁻¹ := by group
        _ = ((GGFF.zs z i)⁻¹)⁻¹ := by rw [hginv_i]
        _ = GGFF.zs z i := inv_inv _
    have hδ : g⁻¹ * τ * g * τ⁻¹ ∈ cB b z := by
      have hu_mem : g⁻¹ * τ * g * τ⁻¹ ∈
          Subgroup.centralizer ((BB b b₁ b₂ b₃ : Subgroup G) : Set G) := by
        refine D.mem_cen_of_gens fun z hz => ?_
        rcases hz with rfl | rfl | rfl | rfl
        · exact hu_b
        · exact hu_gen 0
        · exact hu_gen 1
        · exact hu_gen 2
      change g⁻¹ * τ * g * τ⁻¹ ∈
        Subgroup.centralizer ((GGFF.Bt b z : Subgroup G) : Set G)
      rw [hBteq]
      exact hu_mem
    exact hB₂nor g hg_nB hgS hδ x hx
  have htau_inv : ∀ τ' ∈ L, (∀ i : Fin 3, τ' * GGFF.zs z i * τ'⁻¹ = (GGFF.zs z i)⁻¹) →
      ∀ x ∈ B₂, τ' * x * τ'⁻¹ = x⁻¹ := by
    intro τ' hτ'L hτ'z x hx
    have hτ'inv : ∀ y ∈ B₁, τ' * y * τ'⁻¹ = y⁻¹ := by
      change ∀ y ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G), τ' * y * τ'⁻¹ = y⁻¹
      refine conj_inv_of_closure (S := ({b₁, b₂, b₃} : Set G)) D.B₁ab (g := τ') ?_
      rintro s (rfl | rfl | rfl)
      exacts [hτ'z 0, hτ'z 1, hτ'z 2]
    let u : G := τ' * τ⁻¹
    have hτinv'_B₁ : ∀ y ∈ B₁, τ⁻¹ * y * τ = y⁻¹ := by
      intro y hy
      have h1 : τ * y⁻¹ * τ⁻¹ = y := by
        rw [show τ * y⁻¹ * τ⁻¹ = (τ * y * τ⁻¹)⁻¹ by group, tau_inv_bOne y hy, inv_inv]
      exact inv_conj_of_conj h1
    have huL : u ∈ L := L.mul_mem hτ'L (L.inv_mem hτL)
    have huCen : ∀ y ∈ B₁, u * y * u⁻¹ = y := by
      intro y hy
      calc u * y * u⁻¹
          = τ' * (τ⁻¹ * y * τ) * τ'⁻¹ := by
            change (τ' * τ⁻¹) * y * (τ' * τ⁻¹)⁻¹ = _
            group
        _ = τ' * y⁻¹ * τ'⁻¹ := by rw [hτinv'_B₁ y hy]
        _ = (τ' * y * τ'⁻¹)⁻¹ := by group
        _ = (y⁻¹)⁻¹ := by rw [hτ'inv y hy]
        _ = y := inv_inv _
    have huB₁ : u ∈ B₁ := by
      have hcomm : ∀ i, (⟨u, huL⟩ : ↥L) * z i = z i * ⟨u, huL⟩ := by
        intro i
        apply Subtype.ext
        have hziB₁ : GGFF.zs z i ∈ B₁ := by
          rw [← hB1eq]
          exact Subgroup.subset_closure (Set.mem_range_self i)
        have h := mul_inv_eq_iff_eq_mul.mp (huCen (GGFF.zs z i) hziB₁)
        simpa using h
      obtain ⟨v, hv⟩ :=
        cen_of_model h.hypA.n_cases h.hypA.model h.model ⟨u, huL⟩ hcomm
      have huv : u = vecElt (GGFF.zs z) v := by
        have h := congrArg Subtype.val hv
        rw [← GGFF.SettingCore.vecElt_zs] at h
        exact h
      rw [← hB1eq, huv]
      exact GGFF.vecElt_mem_tor (GGFF.zs z) v
    have huB₂ : u ∈ B₂ := hB₁_le_B₂ (by rw [hB1eq]; exact huB₁)
    have hux : u * x = x * u := by
      have h := hB₂abel.1.is_comm.comm (⟨u, huB₂⟩ : ↥B₂) (⟨x, hx⟩ : ↥B₂)
      exact congrArg Subtype.val h
    have hutau : u * τ = τ' := by
      change τ' * τ⁻¹ * τ = τ'
      rw [inv_mul_cancel_right]
    calc τ' * x * τ'⁻¹
        = (u * τ) * x * (u * τ)⁻¹ := by rw [← hutau]
      _ = u * (τ * x * τ⁻¹) * u⁻¹ := by group
      _ = u * x⁻¹ * u⁻¹ := by rw [hB₂tauinv x hx]
      _ = x⁻¹ := by
        rw [show u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ by group]
        have huxu : u * x * u⁻¹ = x := by rw [hux]; group
        rw [huxu]
  exact ⟨B₂, hle_nor, hB₂abel, hB₂card, hB₁_le_B₂, hb_nor, hcomm, hB₂fix, hD_nor, htau_inv⟩

end CFSG.StandardType.FF81.PropOne

end

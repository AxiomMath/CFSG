module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP3
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP4Mod

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13 U42F431

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G}

theorem card_TAh :
    Nat.card TAh = 64 := by
  have : TAh = (U42.T).map incl := by
    ext a
    rw [mem_TAh_iff, Subgroup.mem_map]
  rw [this, Subgroup.card_map_of_injective incl_injective, U42.card_T]

theorem sOf_eq_imgG
    (iso : AutIso M₁ M₂) : sOf M₁ M₂ = iso.imgG TAh := by
  ext g
  rw [sOf, iso.mem_pCoreOf_iff, iso.mem_imgG]

theorem relIndex_sOf [Finite G]
    (iso : AutIso M₁ M₂) {T : Subgroup G} (hT : IsSylowTwoOf T (M₁ ⊓ M₂)) :
    (sOf M₁ M₂).relIndex T = 2 := by
  have hST : sOf M₁ M₂ ≤ T := pCoreOf_le_of_isSylowTwoOf hT
  have hS64 : Nat.card (sOf M₁ M₂) = 64 := by
    rw [sOf_eq_imgG iso, iso.card_imgG TAh_le_Bh, card_TAh]
  have hT128 : Nat.card T = 128 := by
    rw [hT.card_eq, twoPart_eq_of_card_eq (k := 7) (m := 3) (by norm_num)
      (by rw [iso.card_B]; norm_num)]
    norm_num
  have h := Subgroup.relIndex_mul_card (H := sOf M₁ M₂) (K := T)
  rw [inf_eq_left.2 hST, hS64, hT128] at h
  omega

theorem card_cen_outer_le [Finite G]
    (iso : AutIso M₁ M₂) {T : Subgroup G} (hT : IsSylowTwoOf T (M₁ ⊓ M₂)) {f : G} (hfT : f ∈ T)
    (hfS : f ∉ sOf M₁ M₂) (hf2 : f ^ 2 = 1) : Nat.card ↥(T ⊓ cenOf f) ≤ 32 := by
  obtain ⟨b, hbB, hTb⟩ := B6.isSylowTwoOf_exists_conj (isSylowTwoOf_imgG_That iso) hT
  let bh : ↥Bh := iso.phiB.symm ⟨b, hbB⟩
  have hbh : iso.toG bh = b := congrArg Subtype.val (iso.phiB.apply_symm_apply ⟨b, hbB⟩)
  have hmemT : ∀ t ∈ T, b⁻¹ * t * b ∈ iso.imgG That := fun t ht => by
    rw [hTb] at ht
    exact B6.mem_conjSub.1 ht
  obtain ⟨y, hyT, hyf⟩ := iso.mem_imgG.1 (hmemT f hfT)
  have hy_out : (y : Ah) ∉ TAh := by
    intro hyTA
    apply hfS
    refine iso.mem_pCoreOf_iff.2 ⟨bh * y * bh⁻¹, conj_TAh bh.2 hyTA, ?_⟩
    rw [AutIso.toG_mul, AutIso.toG_mul, AutIso.toG_inv, hbh, hyf]
    group
  have hy2 : y * y = 1 := by
    apply iso.toG_injective
    rw [AutIso.toG_mul, hyf, iso.toG_one]
    calc b⁻¹ * f * b * (b⁻¹ * f * b) = b⁻¹ * (f * f) * b := by group
      _ = 1 := by rw [← pow_two, hf2]; group
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff _).1 hyT
  have hl_out : l ∉ Tl := fun hlT => by
    obtain ⟨g, hg, hgrep⟩ := exists_T_of_mem_Tl hlT
    exact hy_out ((mem_TAh_iff _).2 ⟨g, hg, Subtype.ext (eq_of_repL hgrep hrep)⟩)
  have hl2 : comp l l = idL := by
    have h1 := repL_mul hrep hrep
    have h2 : ((y : Ah) : U42.P45) * ((y : Ah) : U42.P45) = 1 := congrArg
      (fun a : Bh => ((a : Ah) : U42.P45)) hy2
    rw [h2] at h1
    exact repL_unique h1 (repL_one 45)
  have hbound := card_cent_le hrep (outer_check l hl hl_out hl2)
  have hBT : T ≤ M₁ ⊓ M₂ := hT.1
  let φ : ↥(T ⊓ cenOf f) → ↥Bh := fun t => iso.phiB.symm
    ⟨b⁻¹ * t * b, (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).inv_mem hbB)
      (hBT t.2.1)) hbB⟩
  have hφ : ∀ t, iso.toG (φ t) = b⁻¹ * t * b := fun t =>
    congrArg Subtype.val (iso.phiB.apply_symm_apply _)
  have hφT : ∀ t, ((φ t : ↥Bh) : Ah) ∈ That := by
    intro t
    obtain ⟨s, hs, hse⟩ := iso.mem_imgG.1 (hmemT t t.2.1)
    have : s = φ t := iso.toG_injective (hse.trans (hφ t).symm)
    rw [← this]
    exact hs
  have hφC : ∀ t, ((φ t : ↥Bh) : Ah) ∈ Subgroup.centralizer ({(y : Ah)} : Set Ah) := by
    intro t
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : (t : G) * f = f * t := Subgroup.mem_centralizer_singleton_iff.1 t.2.2
    have : φ t * y = y * φ t := by
      apply iso.toG_injective
      rw [AutIso.toG_mul, AutIso.toG_mul, hφ, hyf]
      calc b⁻¹ * (t : G) * b * (b⁻¹ * f * b) = b⁻¹ * ((t : G) * f) * b := by group
        _ = b⁻¹ * (f * t) * b := by rw [hc]
        _ = b⁻¹ * f * b * (b⁻¹ * (t : G) * b) := by group
    exact congrArg Subtype.val this
  refine le_trans (Nat.card_le_card_of_injective
    (fun t => (⟨((φ t : ↥Bh) : Ah), Subgroup.mem_inf.2 ⟨hφT t, hφC t⟩⟩ :
      ↥(That ⊓ Subgroup.centralizer ({(y : Ah)} : Set Ah)))) ?_) hbound
  intro t₁ t₂ h
  have h1 : φ t₁ = φ t₂ := Subtype.ext (congrArg
    (fun z : ↥(That ⊓ Subgroup.centralizer ({(y : Ah)} : Set Ah)) => (z : Ah)) h)
  have h2 := congrArg iso.toG h1
  rw [hφ, hφ] at h2
  have h3 : (t₁ : G) = t₂ := by
    exact mul_left_cancel (mul_right_cancel h2)
  exact Subtype.ext h3

theorem u42AutNotExtremal :
    U42AutNotExtremal := by
  intro h2 h3 G _ _ M₁ M₂ z c T hT f hfT hfS hf2 hext
  have hTG : IsSylowTwoOf T ⊤ := h2 G M₁ M₂ z c T hT
  have hST : sOf M₁ M₂ ≤ T := pCoreOf_le_of_isSylowTwoOf hT
  have hf1 : f ≠ 1 := fun h => hfS (h ▸ Subgroup.one_mem _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf f = 2 := orderOf_eq_prime hf2 hf1
  obtain ⟨x, hx⟩ := exists_conj_mem_of_thompson_of_res c.res hTG hST
    (relIndex_sOf c.iso hT) hord
  have hu2 : (x⁻¹ * f * x) ^ 2 = 1 := by
    rw [pow_two]
    calc x⁻¹ * f * x * (x⁻¹ * f * x) = x⁻¹ * (f * f) * x := by group
      _ = 1 := by rw [← pow_two, hf2]; group
  have hu1 : x⁻¹ * f * x ≠ 1 := fun h => hf1 (by
    calc f = x * (x⁻¹ * f * x) * x⁻¹ := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨g, u', -, -, hgu, hcard⟩ := h3 G M₁ M₂ z c T hT (x⁻¹ * f * x) hx hu2 hu1
  have hu' : u' = (g * x⁻¹) * f * (g * x⁻¹)⁻¹ := by
    rw [← hgu]
    group
  have hge : 2 ^ 6 ≤ twoPart (cenOf f) := by
    have h1 : Nat.card ↥(T ⊓ cenOf u') ≤ twoPart (cenOf u') :=
      card_le_twoPart inf_le_right (hT.2.1.to_le inf_le_left)
    have h2 : twoPart (cenOf u') = twoPart (cenOf f) := by
      rw [hu', cenOf, cenOf]
      exact twoPart_centralizer_conj f (g * x⁻¹)
    exact hcard.trans (h1.trans h2.le)
  have hle := card_cen_outer_le c.iso hT hfT hfS hf2
  have := hext.card_eq
  omega

end CFSG.Quasithin.H13.F431.U42Aut

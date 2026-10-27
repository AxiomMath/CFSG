module

public import CFSG.Quasithin.Background.HM22TwelveCent
public import CFSG.Quasithin.Vol2.Ch8Sec2L8213A
public import CFSG.Certificates.Kernel.J4.ModelsSound
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.Quasithin.H.Mathieu.M22Link

open CFSG.Quasithin CFSG.Quasithin.H13

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def yG : GL (Fin 12) (ZMod 2) := conjP⁻¹ * L1442M.m22a * conjP

theorem m22a_inv : L1442M.m22a⁻¹ = L1442M.m22a :=
  inv_eq_of_mul_eq_one_right m22a_mul_self

theorem yG_conj_mem
    {g : GL (Fin 12) (ZMod 2)} (hg : g ∈ H12Cert.G) : yG * g * yG⁻¹ ∈ H12Cert.G := by
  have hx : conjP * g * conjP⁻¹ ∈ m22Zero := conj_mem_m22Zero hg
  have ha : L1442M.m22a ∈ L1442M.m22 := Subgroup.subset_closure (by simp)
  have hN := normal_m22Zero.conj_mem ⟨_, m22Zero_le_m22 hx⟩ hx ⟨_, ha⟩
  have h1 : L1442M.m22a * (conjP * g * conjP⁻¹) * L1442M.m22a⁻¹ ∈ m22Zero := hN
  rw [mem_m22Zero_iff] at h1
  have h2 : yG * g * yG⁻¹ =
      conjP⁻¹ * (L1442M.m22a * (conjP * g * conjP⁻¹) * L1442M.m22a⁻¹) * conjP := by
    simp only [yG, mul_inv_rev, inv_inv]
    group
  rw [h2]
  exact h1

theorem yG_conj_zU : yG * H12Cert.zU * yG⁻¹ = H12Cert.zU⁻¹ := by
  have h1 : L1442M.m22a * zP * L1442M.m22a⁻¹ = zP⁻¹ := by
    rw [m22a_inv, m22a_mul_zP, eq_inv_iff_mul_eq_one, ← pow_three', zP_pow_three]
  have h2 : yG * H12Cert.zU * yG⁻¹ = conjP⁻¹ * (L1442M.m22a * zP * L1442M.m22a⁻¹) * conjP := by
    simp only [yG, zP, mul_inv_rev, inv_inv]
    group
  rw [h2, h1, zP]
  group

@[expose] noncomputable def betaHom :
    ↥H12Cert.G →* ↥H12Cert.G :=
  ((MulAut.conj yG).toMonoidHom.comp H12Cert.G.subtype).codRestrict H12Cert.G fun g => by
    simpa [MulAut.conj_apply] using yG_conj_mem g.2

theorem betaHom_val
    (g : ↥H12Cert.G) : ((betaHom g : ↥H12Cert.G) : GL (Fin 12) (ZMod 2)) = yG * g * yG⁻¹ := by
  simp [betaHom, MulAut.conj_apply]

theorem betaHom_injective :
    Function.Injective betaHom := by
  intro g h hgh
  have h1 := congrArg Subtype.val hgh
  rw [betaHom_val, betaHom_val] at h1
  exact Subtype.ext (by simpa using h1)

@[expose] noncomputable def betaG :
    MulAut ↥H12Cert.G :=
  MulEquiv.ofBijective betaHom (Finite.injective_iff_bijective.mp betaHom_injective)

@[expose] def zGU : ↥H12Cert.G := ⟨H12Cert.zU, H12Cert.zU_mem⟩

theorem zGU_val : ((zGU : ↥H12Cert.G) : GL (Fin 12) (ZMod 2)) = H12Cert.zU := rfl

theorem zGU_ne_one : zGU ≠ 1 := fun h => H12Cert.zU_ne_one (by rw [← zGU_val, h]; rfl)

theorem zGU_mem_center : zGU ∈ Subgroup.center ↥H12Cert.G := by
  rw [Subgroup.mem_center_iff]
  intro x
  exact Subtype.ext (H12Cert.zU_comm x.2)

theorem betaG_zU :
    betaG zGU = zGU⁻¹ := by
  apply Subtype.ext
  rw [show ((betaG zGU : ↥H12Cert.G) : GL (Fin 12) (ZMod 2)) =
    ((betaHom zGU : ↥H12Cert.G) : GL (Fin 12) (ZMod 2)) from rfl, betaHom_val, zGU_val,
    yG_conj_zU, Subgroup.coe_inv, zGU_val]

theorem ker_conj_eq_center (K : Type*) [Group K] :
    (MulAut.conj : K →* MulAut K).ker = Subgroup.center K := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have := congrArg (fun φ : MulAut K => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  · intro h
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply, ← h x, mul_inv_cancel_right]

variable {K : Type} [Group K]

theorem card_inn : Nat.card ↥(MulAut.conj : K →* MulAut K).range =
    Nat.card (K ⧸ Subgroup.center K) := by
  rw [← ker_conj_eq_center K]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv).symm

theorem index_inn_le
    [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hM : IsSporadic .M22 (K ⧸ Subgroup.center K)) :
    (MulAut.conj : K →* MulAut K).range.index ≤ 2 := by
  obtain ⟨e⟩ := hM
  have h1 := CFSG.Quasithin.H13.card_mulAut_le_quotCenter_82 hq.1
  rw [Nat.card_congr (MulAut.congr e).toEquiv] at h1
  have h2 := CFSG.Sporadic.Schreier.m22_mulAut_card
  have h3 : Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 = Nat.card (K ⧸ Subgroup.center K) :=
    (Nat.card_congr e.toEquiv).symm
  have h4 := Subgroup.card_mul_index (MulAut.conj : K →* MulAut K).range
  rw [card_inn] at h4
  have hpos : 0 < Nat.card (K ⧸ Subgroup.center K) := Nat.card_pos
  have h5 : Nat.card (K ⧸ Subgroup.center K) * (MulAut.conj : K →* MulAut K).range.index ≤
      2 * Nat.card (K ⧸ Subgroup.center K) := by
    rw [h4]
    exact h1.trans (h3 ▸ h2)
  rw [mul_comm] at h5
  exact Nat.le_of_mul_le_mul_right h5 hpos

theorem exists_mulAut_inv
    (hK : IsHat K (CFSG.Blueprint.NativeSporadic.Carrier .M22)) :
    ∃ β : MulAut K, ∀ z ∈ Subgroup.center K, β z = z⁻¹ := by
  obtain ⟨f₀⟩ := HM22.nonempty_mulEquiv_hatM22Γ₀ hK
  let f : ↥H12Cert.G ≃* K := hatEquivG'.symm.trans f₀
  refine ⟨f.symm.trans (betaG.trans f), fun z hz => ?_⟩
  have hfz : f zGU ∈ Subgroup.center K := mem_center_of_mulEquiv f zGU_mem_center
  have hfz1 : f zGU ≠ 1 := fun h => zGU_ne_one (f.injective (h.trans (map_one f).symm))
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp
    (H12Pf.mem_zpowers_of_center hK.2.1 hz hfz hfz1)
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, ← map_zpow, MulEquiv.symm_apply_apply, map_zpow,
    betaG_zU, map_zpow, map_inv, inv_zpow, map_zpow]

theorem kg82HatM22Out_holds :
    CFSG.Quasithin.H13.KG82HatM22Out := by
  intro K _ _ hq hZ hM α hα z hz
  have hK := isHat_of_quasisimple hq hZ hM
  obtain ⟨β, hβ⟩ := exists_mulAut_inv hK
  set I := (MulAut.conj : K →* MulAut K).range with hI
  have hinner : ∀ γ ∈ I, ∀ c ∈ Subgroup.center K, γ c = c := by
    rintro _ ⟨k, rfl⟩ c hc
    rw [MulAut.conj_apply, Subgroup.mem_center_iff.mp hc k, mul_inv_cancel_right]
  have : Nontrivial ↥(Subgroup.center K) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hZ]
    norm_num
  obtain ⟨⟨c, hc⟩, hc1⟩ := exists_ne (1 : ↥(Subgroup.center K))
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hcc : c ≠ c⁻¹ := by
    intro h
    have h2 : c ^ 2 = 1 := by rw [pow_two]; nth_rw 2 [h]; exact mul_inv_cancel c
    have h3 : c ^ 3 = 1 := by
      have h := (pow_card_eq_one' : (⟨c, hc⟩ : ↥(Subgroup.center K)) ^
        Nat.card ↥(Subgroup.center K) = 1)
      rw [hZ] at h
      exact congrArg Subtype.val h
    apply hc1'
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [h2, h3, inv_one, mul_one]
  have hβI : β ∉ I := fun h => hcc ((hinner β h c hc).symm.trans (hβ c hc))
  have hαI : α ∉ I := by
    rintro ⟨k, hk⟩
    exact hα k hk.symm
  have hidx : I.index = 2 := by
    have hle : I.index ≤ 2 := index_inn_le hq hM
    have hne : I.index ≠ 1 := fun h => hβI (Subgroup.index_eq_one.mp h ▸ Subgroup.mem_top β)
    have hpos : I.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hmem : α * β⁻¹ ∈ I := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact iff_of_false hαI fun h => hβI (by simpa using I.inv_mem h)
  obtain ⟨k, hk⟩ := hmem
  have hαk : α = MulAut.conj k * β := by rw [hk, inv_mul_cancel_right]
  rw [hαk, MulAut.mul_apply, hβ z hz, MulAut.conj_apply,
    Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz) k, mul_inv_cancel_right]

end CFSG.Quasithin.H.Mathieu.M22Link

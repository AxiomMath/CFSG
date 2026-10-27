module

import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.CommutatorDimension
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcBinary
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13BridgeA
public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations
open CFSG.LocalAnalysis.WeakClosure81

variable {W : Type} [CommGroup W] [Finite W]

theorem summand_bounds (hW : ∀ w : W, w ^ 2 = 1) {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : 0 < N) {H : Subgroup (MulAut W)} (D : Subgroup ↥H) [D.Normal]
    (hDZ : D ≤ center ↥H) (hDidx : D.relIndex (center ↥H) = p)
    (hext : CFSG.IsExtraspecialPGroup p (↥H ⧸ D)) (hexp : ∀ h : ↥H, h ^ p = 1)
    (hcard : Nat.card (↥H ⧸ D) = p ^ (1 + 2 * N))
    {M : Subgroup W} (hM : StableUnder H M) (hMD : M ≤ fixV (D.map H.subtype))
    (hfree : M ⊓ fixV ((center ↥H).map H.subtype) = ⊥) (hM1 : M ≠ ⊥) :
    p ^ N * dParam p ≤ rk ↥M ∧
      ∀ x ∈ H, orderOf x = p → x ∉ (center ↥H).map H.subtype →
        (p - 1) * p ^ (N - 1) * dParam p ≤ rk ↥(commSub M (zpowers x)) := by
  classical
  have hW' : ∀ m : ↥M, m ^ 2 = 1 := fun m => Subtype.ext (by
    simpa using hW (m : W))
  have hstab : H ≤ stabSub M := by
    intro h hh
    rw [mem_stabSub]
    intro u
    exact ⟨fun hu => by
      have h2 := hM h⁻¹ (H.inv_mem hh) (h u) hu
      simpa using h2, fun hu => hM h hh u hu⟩
  let ψ : ↥H →* MulAut ↥M := (resHom M).comp (Subgroup.inclusion hstab)
  have hψ_apply : ∀ (h : ↥H) (m : ↥M), ((ψ h m : ↥M) : W) = h.1 (m : W) := by
    intro h m
    simpa [ψ] using resHom_apply M (Subgroup.inclusion hstab h) m
  have hψ_apply' : ∀ (h : ↥H) (m : ↥M),
      M.subtype ((ψ h) m) = H.subtype h (M.subtype m) := fun h m => hψ_apply h m
  have hDker : D ≤ ψ.ker := by
    intro d hd
    rw [MonoidHom.mem_ker]
    ext m
    rw [hψ_apply]
    have hmem : d.1 ∈ D.map H.subtype := by
      simpa using Subgroup.mem_map_of_mem H.subtype hd
    simpa using mem_fixV.1 (hMD m.2) d.1 hmem
  let φ : (↥H ⧸ D) →* MulAut ↥M := QuotientGroup.lift D ψ hDker
  have hφ_mk' : ∀ h : ↥H, φ (QuotientGroup.mk' D h) = ψ h := fun _ => rfl
  have hφ_mk : ∀ h : ↥H, φ (h : ↥H ⧸ D) = ψ h := fun _ => rfl
  have hDlt : D < center ↥H := by
    refine lt_of_le_of_ne hDZ ?_
    intro hEq
    rw [hEq, Subgroup.relIndex_self] at hDidx
    exact hp.ne_one hDidx.symm
  obtain ⟨c, hcZ, hcD⟩ := SetLike.exists_of_lt hDlt
  have hcenter : D ⊔ Subgroup.zpowers c = center ↥H := by
    have hle : D ⊔ Subgroup.zpowers c ≤ center ↥H :=
      sup_le hDZ (Subgroup.zpowers_le.2 hcZ)
    have hrel : D.relIndex (D ⊔ Subgroup.zpowers c) = p := by
      have hle' : D ⊔ Subgroup.zpowers c ≤ center ↥H :=
        sup_le hDZ (Subgroup.zpowers_le.2 hcZ)
      have hdvd : D.relIndex (D ⊔ Subgroup.zpowers c) ∣ p := by
        rw [← hDidx]
        exact ⟨_, (Subgroup.relIndex_mul_relIndex (H := D)
          (K := D ⊔ Subgroup.zpowers c) (L := center ↥H) le_sup_left hle').symm⟩
      have hgt : D.relIndex (D ⊔ Subgroup.zpowers c) ≠ 1 := by
        intro h1
        have hEq := Subgroup.relIndex_eq_one.mp h1
        exact hcD (hEq (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)))
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact absurd h hgt
      · exact h
    have hcard' := Subgroup.relIndex_mul_card D (D ⊔ Subgroup.zpowers c)
    rw [inf_eq_left.mpr le_sup_left, hrel] at hcard'
    have hcardc := Subgroup.relIndex_mul_card D (center ↥H)
    rw [inf_eq_left.mpr hDZ, hDidx] at hcardc
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcardc.symm, hcard']
  have hMc : M ⊓ fixV ((Subgroup.zpowers c).map H.subtype) = ⊥ := by
    have h1 : M ⊓ fixV ((Subgroup.zpowers c).map H.subtype) ≤
        M ⊓ fixV ((center ↥H).map H.subtype) := by
      refine le_inf inf_le_left ?_
      rw [← hcenter, Subgroup.map_sup, FixVLat.fixV_sup_eq]
      have h1 : M ⊓ fixV ((Subgroup.zpowers c).map H.subtype) ≤ M := inf_le_left
      exact le_inf (h1.trans hMD) inf_le_right
    exact le_antisymm (hfree ▸ h1) bot_le
  have hψc : ψ c ≠ 1 := by
    intro h1
    have hMle : M ≤ fixV ((Subgroup.zpowers c).map H.subtype) := by
      intro m hm
      have hcm : c.1 (m : W) = (m : W) := by
        have h2 := hψ_apply c ⟨m, hm⟩
        have h3 : ψ c ⟨m, hm⟩ = ⟨m, hm⟩ := by rw [h1]; rfl
        rw [h3] at h2
        exact h2.symm
      rw [MonoidHom.map_zpowers, mem_fixV_zpowers_iff_apply]
      exact hcm
    have hbot : M = ⊥ := by
      rw [← inf_eq_left.mpr hMle]
      exact hMc
    exact hM1 hbot
  have hφz : φ (QuotientGroup.mk' D c) ≠ 1 := by
    rw [hφ_mk']
    exact hψc
  have hexpE : ∀ g : ↥H ⧸ D, g ^ p = 1 := by
    intro g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective D g
    rw [← map_pow, hexp, map_one]
  have hzcenter : QuotientGroup.mk' D c ∈ Subgroup.center (↥H ⧸ D) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective D g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hcZ h]
  have : Fact p.Prime := ⟨hp⟩
  have hclaim1 : p ^ N * dParam p ≤ rk ↥M := by
    have hbound :=
      CFSG.LocalAnalysis.GLTheoremA.S2019.two_pow_le_card_of_extraspecial
        (W := ↥M) (p := p) (e := N) (hp.odd_of_ne_two hp2) hext hexpE hcard
        (fun m => by have h := hW' m; rwa [pow_two] at h) φ hzcenter hφz
    rw [card_eq_two_pow hW M] at hbound
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hbound
  refine ⟨hclaim1, ?_⟩
  intro x hxH hxord hxZ
  let xH : ↥H := ⟨x, hxH⟩
  have hxordH : orderOf xH = p := by
    rw [← Subgroup.orderOf_coe xH]
    simpa [xH] using hxord
  have hxD : xH ∉ D := fun h => hxZ (by
    have h1 := Subgroup.mem_map_of_mem H.subtype (hDZ h)
    simpa [xH] using h1)
  let xbar : ↥H ⧸ D := QuotientGroup.mk' D xH
  have hxbar1 : xbar ≠ 1 := fun h =>
    hxD ((QuotientGroup.eq_one_iff xH).mp (by simpa [xbar] using h))
  have hxbar_ord : orderOf xbar = p := by
    have hdvd : orderOf xbar ∣ p := by
      have h := orderOf_map_dvd (QuotientGroup.mk' D) xH
      rwa [hxordH] at h
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hxbar1
    · exact h
  have hXp : Nat.card (Subgroup.zpowers xbar) = p := by
    rw [Nat.card_zpowers, hxbar_ord]
  have hextTop : CFSG.IsExtraspecialPGroup p ↥(⊤ : Subgroup (↥H ⧸ D)) :=
    ExtraspecialDimensionDivisibility.extra_equiv Subgroup.topEquiv.symm hext
  have hcenterInTop :
      RankThreeUC.BinaryRepresentations.centerIn (⊤ : Subgroup (↥H ⧸ D)) =
        Subgroup.center (↥H ⧸ D) := by
    ext z
    exact ExtraspecialDimensionDivisibility.mem_centerIn_top z
  have hZm_le : (center ↥H).map (QuotientGroup.mk' D) ≤
      RankThreeUC.BinaryRepresentations.centerIn (⊤ : Subgroup (↥H ⧸ D)) := by
    rw [hcenterInTop]
    rintro z ⟨y, hy, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective D g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hy h]
  have hcardZm : Nat.card ↥((center ↥H).map (QuotientGroup.mk' D)) = p := by
    rw [← Subgroup.relIndex_ker (K := center ↥H) (QuotientGroup.mk' D),
      QuotientGroup.ker_mk']
    exact hDidx
  have hcardZ :
      Nat.card ↥(RankThreeUC.BinaryRepresentations.centerIn (⊤ : Subgroup (↥H ⧸ D))) = p := by
    rw [hcenterInTop]
    exact hext.2.2.2
  have hcenterE : RankThreeUC.BinaryRepresentations.centerIn (⊤ : Subgroup (↥H ⧸ D)) =
      (center ↥H).map (QuotientGroup.mk' D) :=
    (Subgroup.eq_of_le_of_card_ge hZm_le (by rw [hcardZm, hcardZ])).symm
  have hxbarZ : xbar ∉ RankThreeUC.BinaryRepresentations.centerIn (⊤ : Subgroup (↥H ⧸ D)) := by
    intro h
    rw [hcenterE] at h
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 h
    rw [QuotientGroup.mk'_eq_mk'] at hzx
    obtain ⟨d, hd, hzd⟩ := hzx
    have hxHcenter : xH ∈ center ↥H := by
      rw [← hzd]
      exact Subgroup.mul_mem _ hz (hDZ hd)
    exact hxZ (by
      have h1 := Subgroup.mem_map_of_mem H.subtype hxHcenter
      simpa [xH] using h1)
  have hXZ : Subgroup.zpowers xbar ≠
      RankThreeUC.BinaryRepresentations.centerIn (⊤ : Subgroup (↥H ⧸ D)) := by
    intro h
    exact hxbarZ (h ▸ Subgroup.mem_zpowers xbar)
  let : Module (ZMod 2) (Additive ↥M) := CFSG.RankThree.FFModules.moduleOfSq hW'
  have : Module.Finite (ZMod 2) (Additive ↥M) := Module.Finite.of_finite
  let ρ : Representation (ZMod 2) (↥H ⧸ D) (Additive ↥M) :=
    (CFSG.RankThree.FFModules.autRep ↥M).comp φ
  have hzmem : QuotientGroup.mk' D c ∈
      RankThreeUC.BinaryRepresentations.centerIn (⊤ : Subgroup (↥H ⧸ D)) := by
    rw [hcenterE]
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' D) hcZ
  have hfix : fixedSpace ρ
      (RankThreeUC.BinaryRepresentations.centerIn (⊤ : Subgroup (↥H ⧸ D))) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have hzv : ρ (QuotientGroup.mk' D c) v = v :=
      (mem_fixedSpace_iff ρ _ v).1 hv _ hzmem
    have hψv : ψ c v.toMul = v.toMul := by
      have h1 : (CFSG.RankThree.FFModules.autRep ↥M) (ψ c) v = v := by
        simpa [ρ, hφ_mk] using hzv
      exact Additive.ofMul.injective
        (by simpa [CFSG.RankThree.FFModules.autRep_apply] using h1)
    have hcv : c.1 ((v.toMul : ↥M) : W) = ((v.toMul : ↥M) : W) := by
      have h2 := hψ_apply c v.toMul
      rw [hψv] at h2
      exact h2.symm
    have hmem : ((v.toMul : ↥M) : W) ∈
        M ⊓ fixV ((Subgroup.zpowers c).map H.subtype) := by
      refine ⟨v.toMul.2, ?_⟩
      rw [MonoidHom.map_zpowers]
      exact mem_fixV_zpowers_iff_apply.2 hcv
    rw [hMc] at hmem
    have h1 : v.toMul = 1 := Subtype.ext (Subgroup.mem_bot.mp hmem)
    exact Additive.ofMul.injective (by simpa using h1)
  have hEnontriv : Nontrivial (↥H ⧸ D) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow (by omega) hp.one_lt
  have htop_nontriv : Nontrivial ↥(⊤ : Subgroup (↥H ⧸ D)) := by
    obtain ⟨a, b, hab⟩ := hEnontriv
    exact ⟨⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun h => hab (congrArg Subtype.val h)⟩⟩
  have hexpTop : Monoid.exponent ↥(⊤ : Subgroup (↥H ⧸ D)) = p := by
    have : Nontrivial ↥(⊤ : Subgroup (↥H ⧸ D)) := htop_nontriv
    rw [Monoid.exponent_eq_prime_iff hp]
    intro g hg
    have hgp : g ^ p = 1 := by
      have h := hexpE (g : ↥H ⧸ D)
      exact Subtype.ext (by simpa using h)
    exact orderOf_eq_prime hgp hg
  have htop : commSpace ρ
      (RankThreeUC.BinaryRepresentations.centerIn (⊤ : Subgroup (↥H ⧸ D))) = ⊤ :=
    ExtraspecialDimensionDivisibility.commSpace_eq_top ρ _ (by
      rw [hcardZ]
      exact hp.odd_of_ne_two hp2) hfix
  have hCS := ExtraspecialModuleDecomposition.finrank_commSpace hp hp2
    (⊤ : Subgroup (↥H ⧸ D)) hextTop hexpTop ρ (Subgroup.zpowers xbar) le_top hXp hXZ
  rw [htop, finrank_top, top_inf_eq] at hCS
  let m : ℕ := Module.finrank (ZMod 2) ↥(fixedSpace ρ (Subgroup.zpowers xbar))
  have hCS' : Module.finrank (ZMod 2) (Additive ↥M) = m * p := hCS
  have hdim := CommutatorDimension.dimension_formula ρ hp hp2
    (Subgroup.zpowers xbar) hXp ⊤ (fun _ _ _ _ => Submodule.mem_top)
    (by rw [finrank_top, hCS', Nat.mul_comm])
    (by rw [top_inf_eq])
  have hψzpow : ∀ (k : ℤ) (m' : ↥M),
      M.subtype (((ψ xH) ^ k) m') = (x ^ k) (M.subtype m') := by
    intro k m'
    have h1 : (ψ xH) ^ k = ψ (xH ^ k) := by rw [← MonoidHom.map_zpow]
    have h2 : H.subtype (xH ^ k) = x ^ k := by
      rw [MonoidHom.map_zpow]
      rfl
    rw [h1]
    change M.subtype (ψ (xH ^ k) m') = (x ^ k) (M.subtype m')
    rw [hψ_apply', h2]
  have hmap_le : (commSub ⊤ (Subgroup.zpowers (ψ xH))).map M.subtype ≤
      commSub M (Subgroup.zpowers x) := by
    rw [commSub, MonoidHom.map_closure, commSub]
    apply (Subgroup.closure_le _).2
    rintro w ⟨c', ⟨g, hg, u, -, rfl⟩, rfl⟩
    rw [← MonoidHom.map_zpowers] at hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
    refine Subgroup.subset_closure ⟨y.1, ?_, M.subtype u, u.2, ?_⟩
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
        change x ^ k = H.subtype (xH ^ k)
        rw [MonoidHom.map_zpow]
        rfl⟩
    · rw [map_mul, map_inv, hψ_apply']
      rfl
  have hmap_ge : commSub M (Subgroup.zpowers x) ≤
      (commSub ⊤ (Subgroup.zpowers (ψ xH))).map M.subtype := by
    rw [commSub]
    apply (Subgroup.closure_le _).2
    rintro w ⟨g, hg, u, hu, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine Subgroup.mem_map.mpr
      ⟨(((ψ xH) ^ k) ⟨u, hu⟩) * ⟨u, hu⟩⁻¹, ?_, ?_⟩
    · exact Subgroup.subset_closure
        ⟨(ψ xH) ^ k, Subgroup.zpow_mem_zpowers _ _, ⟨u, hu⟩, Subgroup.mem_top _, rfl⟩
    · rw [map_mul, map_inv, hψzpow]
      rfl
  have hcommMap : (commSub ⊤ (Subgroup.zpowers (ψ xH))).map M.subtype =
      commSub M (Subgroup.zpowers x) := le_antisymm hmap_le hmap_ge
  have hcommOnEq : commOn ρ (Subgroup.zpowers xbar) ⊤ =
      commOn (CFSG.RankThree.FFModules.autRep ↥M) (Subgroup.zpowers (ψ xH)) ⊤ := by
    unfold commOn
    congr 1
    ext w
    constructor
    · rintro ⟨g, hg, u, -, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      refine ⟨(ψ xH) ^ k, Subgroup.zpow_mem_zpowers _ _, u, trivial, ?_⟩
      have hφpow : φ (xbar ^ k) = (ψ xH) ^ k := by
        rw [map_zpow, hφ_mk']
      simp only [ρ, MonoidHom.comp_apply, hφpow]
    · rintro ⟨g, hg, u, -, rfl⟩
      have hg' : g ∈ (Subgroup.zpowers xbar).map φ := by
        rw [MonoidHom.map_zpowers, hφ_mk']
        exact hg
      obtain ⟨g₀, hg₀, hφg₀⟩ := Subgroup.mem_map.1 hg'
      refine ⟨g₀, hg₀, u, trivial, ?_⟩
      simp only [ρ, MonoidHom.comp_apply, hφg₀]
  have hfinrankComm : Module.finrank (ZMod 2) ↥(commOn ρ (Subgroup.zpowers xbar) ⊤) =
      rk ↥(commSub M (Subgroup.zpowers x)) := by
    rw [hcommOnEq, w16g_commOn_top]
    have h2 := w16g_rk_eq_finrank hW' (commSub ⊤ (Subgroup.zpowers (ψ xH)))
    rw [w16g_toSub_commSub, w16g_toSub_top, w16g_commOn_top] at h2
    rw [← h2]
    unfold rk
    rw [← hcommMap, Subgroup.card_map_of_injective M.subtype_injective]
  have hfinV : Module.finrank (ZMod 2) (Additive ↥M) = rk ↥M := by
    have h := w16g_rk_eq_finrank hW' (⊤ : Subgroup ↥M)
    rw [w16g_toSub_top, finrank_top, rk_top] at h
    exact h.symm
  have hm_bound : p ^ (N - 1) * dParam p ≤ m := by
    have hpow : p ^ N = p * p ^ (N - 1) := by
      conv_lhs => rw [show N = (N - 1) + 1 from (Nat.sub_add_cancel hN).symm]
      rw [pow_succ']
    have h2 : p * (p ^ (N - 1) * dParam p) ≤ p * m := by
      calc p * (p ^ (N - 1) * dParam p) = p ^ N * dParam p := by rw [hpow, mul_assoc]
        _ ≤ rk ↥M := hclaim1
        _ = m * p := by rw [← hfinV, hCS']
        _ = p * m := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h2 hp.pos
  have h3 : (p - 1) * (p ^ (N - 1) * dParam p) ≤ (p - 1) * m :=
    Nat.mul_le_mul_left _ hm_bound
  calc (p - 1) * p ^ (N - 1) * dParam p
      = (p - 1) * (p ^ (N - 1) * dParam p) := by rw [mul_assoc]
    _ ≤ (p - 1) * m := h3
    _ = m * (p - 1) := Nat.mul_comm _ _
    _ = rk ↥(commSub M (Subgroup.zpowers x)) := by rw [← hfinrankComm, hdim]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

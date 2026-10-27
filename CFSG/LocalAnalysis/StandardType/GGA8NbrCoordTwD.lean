module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordSplit
public import CFSG.LocalAnalysis.StandardType.GGA8NbrLabelsB
public import CFSG.LocalAnalysis.StandardType.GGA8NbrGlueB
public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordCase
public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmLSide

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Certificates.A8Nbr476 CFSG.StandardType.A8Coord

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem a8d_not_mem_zpowers {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 7 B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr 7 B x D J y K) : x ∉ Subgroup.zpowers y := by
  intro hx
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  have hDle : D ≤ Subgroup.zpowers y := by
    rw [hnb.2.1, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hx
    · exact Subgroup.mem_zpowers _
  have hy7 : y ^ 7 = 1 := hcfg.2.1.2.1.2 y hyBs
  have hord : orderOf y ≤ 7 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hy7)
  have hle : Nat.card D ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hDle
  rw [hcfg.2.2.1.2.2.1, Nat.card_zpowers] at hle
  omega

private theorem a8d_hV {G : Type} [Group G] {Bs K : Subgroup G} {x y : G} (hxBs : x ∈ Bs)
    (hyBs : y ∈ Bs) (hxy : x ∉ Subgroup.zpowers y) {w : G} (hwK : w ∈ K) (hw : orderOf w = 73)
    (hwx : w * x = x * w) (hwy : w * y = y * w) {ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V)}
    {ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)} (hF : A8Coord.GGA8KFrame Bs K y hyBs ρ ι) :
    ∀ i : Fin 3, ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) i.succ ≠ 0 := by
  obtain ⟨hy0, hK0, hρ⟩ := hF
  set xb : ↥Bs := ⟨x, hxBs⟩ with hxb
  set yb : ↥Bs := ⟨y, hyBs⟩ with hyb
  set m : ℕ := (ι (Additive.ofMul xb) 0).val with hm
  set kb : ↥Bs := Additive.toMul (Additive.ofMul xb - m • Additive.ofMul yb) with hkb
  have hιk : ι (Additive.ofMul kb) =
      ι (Additive.ofMul xb) - m • (Pi.single 0 1 : Fin 4 → ZMod 7) := by
    rw [hkb, ofMul_toMul, map_sub, map_nsmul, hy0]
  have hιk0 : ι (Additive.ofMul kb) 0 = 0 := by
    rw [hιk, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, hm,
      ZMod.natCast_zmod_val, sub_self]
  have hιks : ∀ i : Fin 3, ι (Additive.ofMul kb) i.succ = ι (Additive.ofMul xb) i.succ := by
    intro i
    rw [hιk, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero i), smul_zero,
      sub_zero]
  have hkK : (kb : G) ∈ K := (hK0 kb).mp hιk0
  have hkbG : (kb : G) = x * (y ^ m)⁻¹ := by
    rw [hkb]
    change ((Additive.toMul (Additive.ofMul xb - m • Additive.ofMul yb) : ↥Bs) : G) = _
    rw [toMul_sub, toMul_nsmul]
    simp [div_eq_mul_inv, hxb, hyb]
  have hcomm : w * (kb : G) = (kb : G) * w := by
    rw [hkbG]
    exact ((show Commute w x from hwx).mul_right
      (((show Commute w y from hwy).pow_right m).inv_right)).eq
  have hf : (fun i : Fin 3 => ι (Additive.ofMul xb) i.succ) ≠ 0 := by
    intro h0
    apply hxy
    have hιx : ι (Additive.ofMul xb) = ι (m • Additive.ofMul yb) := by
      rw [map_nsmul, hy0]
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · rw [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, hm, ZMod.natCast_zmod_val]
      · have h1 := congrFun h0 i
        simp only [Pi.zero_apply] at h1
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero i), smul_zero]
        exact h1
    have h2 : Additive.ofMul xb = m • Additive.ofMul yb := ι.injective hιx
    have hxe : xb = yb ^ m := by
      have h3 := congrArg Additive.toMul h2
      simpa [toMul_nsmul] using h3
    have hx' : x = y ^ m := by
      have h4 := congrArg Subtype.val hxe
      simpa [hxb, hyb] using h4
    rw [hx']
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y) m
  have hwρ : orderOf (ρ ⟨w, hwK⟩) = 73 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hw]
  have hct : ρ ⟨w, hwK⟩ *
        ggSL9TorusCoord (Multiplicative.ofAdd (fun i : Fin 3 => ι (Additive.ofMul xb) i.succ)) =
      ggSL9TorusCoord (Multiplicative.ofAdd (fun i : Fin 3 => ι (Additive.ofMul xb) i.succ)) *
        ρ ⟨w, hwK⟩ := by
    have h1 := hρ kb hkK
    have h2 : (fun i : Fin 3 => ι (Additive.ofMul kb) i.succ) =
        fun i : Fin 3 => ι (Additive.ofMul xb) i.succ := funext hιks
    rw [h2] at h1
    rw [← h1, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  intro i
  exact A8Coord.ggSL9_torusCoord_ne_zero_of_order73 hf hwρ hct i

theorem ggForkA8Coord2D4Input_of_mp
    (hMp : GGInnerDiagMpInput) (hLB : GGLBalanceInput) : GGForkA8Coord2D4Input := by
  intro G _ _ p B Bs x L D J hcfg hinn hNT hp y K hnb hKm hlab
  subst hp
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hmodL : StatedClassicalModel (L ⧸ Subgroup.center L) .POmegaMinus 4 2 3 :=
    statedClassicalModel_of_hasLabel_twD43 hlab
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  obtain ⟨hJK, hCJ, ⟨w, hwJ, hw73⟩, ιL, hLF⟩ :=
    ggA8Nbr_lSideOm hMp hLB hcfg hinn.1 hmodL hnb hKm
  obtain ⟨ρ, ιK, hF⟩ := A8Coord.ggA8Nbr_kFrame hMp hcfg hnb (hinn.2 y K hnb) hKm hJK hCJ hyBs
  have hyK : ∀ k ∈ K, y * k = k * y := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hnb.1.2.2.2.1 hk)).symm
  have hK := A8Coord.ggA8Nbr_kAut hyBs hyK hF
  have hJcent : ∀ g ∈ J, ∀ d ∈ D, g * d = d * g := by
    intro g hg d hd
    have h1 : g ∈ Subgroup.centralizer (D : Set G) :=
      (Subgroup.mem_inf.mp (hcfg.2.2.1.2.2.2.2.2.1.1 hg)).2
    exact (Subgroup.mem_centralizer_iff.mp h1 d hd).symm
  have hxD : x ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hyD : y ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hJx : ∀ ψ ∈ ggAutomizer J Bs, ψ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
    intro ψ hψ
    have hle : ggAutomizer J Bs ≤ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxBs⟩ : ↥Bs) := by
      rw [ggAutomizer, Subgroup.closure_le]
      rintro χ ⟨g, hgJ, -, hg⟩
      rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def]
      apply Subtype.ext
      rw [hg ⟨x, hxBs⟩]
      change g * x * g⁻¹ = x
      rw [hJcent g hgJ x hxD, mul_inv_cancel_right]
    have h1 := hle hψ
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h1
  have hV := a8d_hV hxBs hyBs (a8d_not_mem_zpowers hcfg hnb) (hJK hwJ) hw73
    (hJcent w hwJ x hxD) (hJcent w hwJ y hyD) hF
  obtain ⟨c, ι, hc, hc1, hgens⟩ :=
    A8Coord.ggA8Nbr_glueB hNT hJK ⟨x, hxBs⟩ hJx ιK ιL hK hV hLF
  exact ⟨c, ι, hc, hgens, fun h => by rw [hc1] at h; exact absurd h (by decide)⟩

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpResidual
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordLift
public import CFSG.LocalAnalysis.StandardType.GGA8NbrLModel
public import CFSG.LocalAnalysis.StandardType.GGA8NbrKFrame
public import CFSG.LocalAnalysis.StandardType.GGA8NbrKAut
public import CFSG.LocalAnalysis.StandardType.GGA8NbrOrder73
public import CFSG.LocalAnalysis.StandardType.GGA8NbrGlue

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Certificates.A8Nbr476

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGForkA8CoordA3Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → p = 7 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1 →
        GGHasLabel ⟨.A, 3, 3⟩ (L ⧸ Subgroup.center L) →
        ∃ (c : Case) (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)), c ∈ allCases ∧
          (∀ k : Fin 6, ∃ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ b : ↥Bs,
            ι (Additive.ofMul (φ b)) = Matrix.vecMul (ι (Additive.ofMul b)) (gens c k)) ∧
          (c.1 = true → StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3)

@[expose] def GGForkA8CoordRestInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → p = 7 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1 →
        (GGHasLabel ⟨.C, 3, 3⟩ (L ⧸ Subgroup.center L) ∨
          GGHasLabel ⟨.twD, 4, 3⟩ (L ⧸ Subgroup.center L)) →
        ∃ (c : Case) (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)), c ∈ allCases ∧
          (∀ k : Fin 6, ∃ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ b : ↥Bs,
            ι (Additive.ofMul (φ b)) = Matrix.vecMul (ι (Additive.ofMul b)) (gens c k)) ∧
          (c.1 = true → StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3)

theorem ggForkA8CoordInput_of_split (hA : GGForkA8CoordA3Input) (hR : GGForkA8CoordRestInput) :
    GGForkA8CoordInput :=
  fun G _ _ p B Bs x L D J h1 h2 h3 hp y K hK hKm hL =>
    hL.elim (hA G p B Bs x L D J h1 h2 h3 hp y K hK hKm)
      (hR G p B Bs x L D J h1 h2 h3 hp y K hK hKm)

private theorem a8ca_center_eq_bot :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 3)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at ha
  obtain ⟨r, hr, hrA⟩ := ha
  have hr4 : r ^ 4 = 1 := by
    simpa using hr
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 4 ≠ 0)] at hr4
    exact one_ne_zero hr4.symm
  have hr7 : r ^ 7 = 1 := by
    have h := ggSL9_units_pow_seven (Units.mk0 r hr0)
    have h' := congrArg (fun z : (GaloisField 2 3)ˣ => (z : GaloisField 2 3)) h
    simpa [Units.val_pow_eq_pow_val] using h'
  have hr1 : r = 1 := by
    have h := (pow_gcd_eq_one (a := r) (m := 4) (n := 7)).mpr ⟨hr4, hr7⟩
    simpa using h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  have hcoe : (↑a : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (GaloisField 2 3)) = 1 := by
    rw [← hrA, hr1]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply]
  rw [hcoe]

private theorem a8ca_phi_injective {G : Type} [Group G]
    (φ : Matrix.SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 3) →* G)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 3))) :
    Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro a ha
  have hc := hker ha
  rw [a8ca_center_eq_bot, Subgroup.mem_bot] at hc
  exact hc

private theorem a8ca_seven_dvd_card {G : Type} [Group G] {J : Subgroup G}
    (φ : Matrix.SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 3) →* G)
    (hφ : Function.Injective φ)
    (hJ : (φ.comp (slLowerBlockHom 3 (GaloisField 2 3))).range = J) : 7 ∣ Nat.card J := by
  have hinj : Function.Injective (φ.comp (slLowerBlockHom 3 (GaloisField 2 3))) :=
    hφ.comp slLowerBlockHom_injective
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 3)) =
      Nat.card J := by
    rw [← hJ]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  rw [← hcard, Matrix.card_SL_field (𝔽 := GaloisField 2 3) 3]
  have hq : Fintype.card (GaloisField 2 3) = 8 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]
    norm_num
  rw [hq]
  norm_num [Fin.prod_univ_three]

private theorem a8ca_not_mem_zpowers {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
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

private theorem a8ca_hV {G : Type} [Group G] {Bs K : Subgroup G} {x y : G} (hxBs : x ∈ Bs)
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

theorem ggForkA8CoordA3Input_of_mp
    (hMp : GGInnerDiagMpInput) (hLB : GGLBalanceInput) : GGForkA8CoordA3Input := by
  intro G _ _ p B Bs x L D J hcfg hinn hNT hp y K hnb hKm hlab
  subst hp
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hmodL : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3 :=
    statedClassicalModel_of_hasLabel_typeA (n := 3) (f := 3)
      ⟨by norm_num, by norm_num, fun h => by simp at h⟩ hlab
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  have hx1 : x ≠ 1 := by
    intro h
    have h7 := hcfg.orderOf_x
    rw [h, orderOf_one] at h7
    omega
  have hCJ := ggA8Nbr_bstar_inf_centralizer_J_le hMp hcfg hinn.1 hmodL hnb
  obtain ⟨φ, hrange, hker, hdiag, hJ⟩ := ggA8Nbr_exists_lift_L hMp hcfg hinn.1 hmodL hnb
  have hφinj := a8ca_phi_injective φ hker
  obtain ⟨ιL, hLx, hL, hLJ⟩ := A8Coord.ggA8Nbr_lModel hcfg.2.1.2.1 hcfg.2.1.2.2.2
    (GGConfig.bstar_inf_centralizer_L hcfg) hx1 hxBs φ hrange hker hdiag hJ
  have hJK : J ≤ K := le_of_ggNbr hLB hcfg.1 hcfg.2.2 (a8ca_seven_dvd_card φ hφinj hJ) hnb
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
  obtain ⟨w, hwJ, hw73⟩ := A8Coord.exists_orderOf_seventythree_lowerBlock φ hφinj
  rw [hJ] at hwJ
  have hV := a8ca_hV hxBs hyBs (a8ca_not_mem_zpowers hcfg hnb) (hJK hwJ) hw73
    (hJcent w hwJ x hxD) (hJcent w hwJ y hyD) hF
  obtain ⟨c, ι, hc, -, hgens⟩ :=
    A8Coord.ggA8Nbr_glue hNT hJK ⟨x, hxBs⟩ hJx ιK ιL hK hV hLx hL hLJ
  exact ⟨c, ι, hc, hgens, fun _ => hmodL⟩

end CFSG.StandardType

end

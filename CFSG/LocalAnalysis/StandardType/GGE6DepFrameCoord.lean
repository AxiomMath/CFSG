module

public import CFSG.LocalAnalysis.StandardType.GGE6DepFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelCoord
public import CFSG.LocalAnalysis.StandardType.GGE6DepZpowersInf
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

private theorem pow_mul_comm {x l : G} (h : l * x = x * l) (k : ℕ) :
    x ^ k * l = l * x ^ k := by
  induction k with
  | zero => rw [pow_zero, one_mul, mul_one]
  | succ k ih =>
    calc x ^ (k + 1) * l = (x ^ k * x) * l := by rw [pow_succ]
      _ = x ^ k * (x * l) := by rw [mul_assoc]
      _ = x ^ k * (l * x) := by rw [h]
      _ = (x ^ k * l) * x := by rw [← mul_assoc]
      _ = (l * x ^ k) * x := by rw [ih]
      _ = l * (x ^ k * x) := by rw [mul_assoc]
      _ = l * x ^ (k + 1) := by rw [pow_succ]

private theorem decomp_unique {x : G} {L : Subgroup G} {k k' : ℕ} {l l' : G}
    (hxinf : Subgroup.zpowers x ⊓ L = ⊥)
    (hxord : orderOf x = 3)
    (hl : l ∈ L) (hl' : l' ∈ L)
    (h : l * x ^ k = l' * x ^ k') : l = l' ∧ (k : ZMod 3) = (k' : ZMod 3) := by
  have h1 : l⁻¹ * l' = x ^ k * (x ^ k')⁻¹ := by
    calc l⁻¹ * l' = l⁻¹ * (l' * x ^ k') * (x ^ k')⁻¹ := by group
      _ = l⁻¹ * (l * x ^ k) * (x ^ k')⁻¹ := by rw [← h]
      _ = x ^ k * (x ^ k')⁻¹ := by group
  have hmemL : l⁻¹ * l' ∈ L := Subgroup.mul_mem _ (Subgroup.inv_mem _ hl) hl'
  have hmemZ : l⁻¹ * l' ∈ Subgroup.zpowers x := by
    rw [h1]
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) k)
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) k'))
  have hbot : l⁻¹ * l' = (1 : G) := by
    have : l⁻¹ * l' ∈ (⊥ : Subgroup G) := by
      rw [← hxinf]; exact ⟨hmemZ, hmemL⟩
    exact Subgroup.mem_bot.mp this
  have hl_eq : l = l' := inv_mul_eq_one.mp hbot
  refine ⟨hl_eq, ?_⟩
  have hpow : x ^ k = x ^ k' := by
    have hh := h; rw [hl_eq] at hh; exact mul_left_cancel hh
  have hmod : k ≡ k' [MOD 3] := by
    have := pow_eq_pow_iff_modEq.mp hpow
    rwa [hxord] at this
  exact (ZMod.natCast_eq_natCast_iff k k' 3).mpr hmod

private theorem coordE_mulVec_single_five : coordE.mulVec (Pi.single 5 (1 : ZMod 3)) = 0 := by
  decide +kernel

theorem ggE6Dep_exists_coordinates {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hcardBs : Nat.card Bs = 3 ^ 6)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxBs : x ∈ Bs)
    (hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥L))
    (hBsL : ∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k)
    (hcard : Nat.card (ggGamma L hBsN).range = 3 ^ 5) {Z : Subgroup ↥L}
    {Φ : ↥(ggGamma L hBsN).range →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup ↥L}
    {w : Fin 6 → ↥L} (hmodel : GGE6ThreeWeylModelWith Z (ggGamma L hBsN).range Φ T w) :
    ∃ ι : Additive ↥Bs ≃+ Vec6, ι (Additive.ofMul ⟨x, hxBs⟩) = Pi.single 5 1 ∧
      (∀ b : ↥Bs, (b : G) ∈ L ↔ ι (Additive.ofMul b) 5 = 0) ∧
      ∀ b : ↥Bs, ι (Additive.ofMul b) 5 = 0 →
        coordE.mulVec (ι (Additive.ofMul b)) =
          Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict b)) := by
  classical
  obtain ⟨hp3, hBsE, hxBs_tf, hLx, -⟩ := hcfg.tableB_facts
  have hxcent : x ∈ Subgroup.centralizer (L : Set G) := mem_centralizer_of_le_centralizer hLx
  have hx3 : x ^ 3 = 1 := hBsE.2 x hxBs_tf
  have hxord : orderOf x = 3 := hcfg.orderOf_x
  have hxinf : Subgroup.zpowers x ⊓ L = ⊥ :=
    GGE6Dep.zpowers_inf_eq_bot_of_centralizer hp3 hxcent hx3 hZ
  have hxcomm : ∀ l ∈ L, l * x = x * l :=
    fun l hl => Subgroup.mem_centralizer_iff.mp hxcent l hl
  have hx_ne : x ≠ 1 := by
    intro hx1
    have h := hxord
    rw [hx1, orderOf_one] at h
    norm_num at h
  have hΦinj : Function.Injective Φ := hmodel.1
  have hcardVec : Nat.card Vec6 = 3 ^ 6 := by
    rw [Vec6, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hΦrange_ne_top : Φ.range ≠ ⊤ := by
    intro htop
    have hsurj : Function.Surjective Φ := fun y => by
      have hy : y ∈ Φ.range := by rw [htop]; trivial
      exact hy
    have hle1 : Nat.card (ggGamma L hBsN).range ≤ Nat.card (Multiplicative Vec6) :=
      Nat.card_le_card_of_injective Φ hΦinj
    have hle2 : Nat.card (Multiplicative Vec6) ≤ Nat.card (ggGamma L hBsN).range :=
      Nat.card_le_card_of_surjective Φ hsurj
    have hcardVecM : Nat.card (Multiplicative Vec6) = 3 ^ 6 := by
      rw [Nat.card_congr Multiplicative.toAdd, hcardVec]
    have hle2' : 3 ^ 6 ≤ Nat.card (ggGamma L hBsN).range := hcardVecM ▸ hle2
    rw [hcard] at hle2'
    norm_num at hle2'
  have hΦiff : ∀ y : Vec6, Multiplicative.ofAdd y ∈ Φ.range ↔ y ∈ NoOffRest.hypE6 :=
    hmodel.2.1.resolve_left hΦrange_ne_top
  have hΦ_eq_one : ∀ a : (ggGamma L hBsN).range, Φ a = 1 ↔ a = 1 := by
    intro a
    constructor
    · intro h
      exact hΦinj (h.trans (map_one Φ).symm)
    · intro h
      rw [h, map_one]
  have hkerγ : (ggGamma L hBsN).ker = (Subgroup.zpowers x).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, ggGamma_eq_one_iff, Subgroup.mem_subgroupOf,
      ← hcfg.bstar_inf_centralizer_L, Subgroup.mem_inf]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  let Lf : ↥Bs → G := fun b => Classical.choose (hBsL (b : G) b.2)
  have hLf : ∀ b : ↥Bs, Lf b ∈ L :=
    fun b => (Classical.choose_spec (hBsL (b : G) b.2)).1
  let Kf : ↥Bs → ℕ :=
    fun b => Classical.choose (Classical.choose_spec (hBsL (b : G) b.2)).2
  have hKf : ∀ b : ↥Bs, (b : G) = Lf b * x ^ Kf b :=
    fun b => Classical.choose_spec (Classical.choose_spec (hBsL (b : G) b.2)).2
  let φ0 : Additive ↥Bs →+ NoOffRest.hypE6 :=
    { toFun := fun b =>
        ⟨Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict (Additive.toMul b))),
          (hΦiff _).mp ⟨(ggGamma L hBsN).rangeRestrict (Additive.toMul b), rfl⟩⟩
      map_zero' := by
        apply Subtype.ext
        show Multiplicative.toAdd
          (Φ ((ggGamma L hBsN).rangeRestrict (Additive.toMul 0))) = 0
        simp
      map_add' := by
        intro a b
        apply Subtype.ext
        change Multiplicative.toAdd
            (Φ ((ggGamma L hBsN).rangeRestrict (Additive.toMul a * Additive.toMul b))) =
          Multiplicative.toAdd
              (Φ ((ggGamma L hBsN).rangeRestrict (Additive.toMul a))) +
            Multiplicative.toAdd
              (Φ ((ggGamma L hBsN).rangeRestrict (Additive.toMul b)))
        rw [map_mul, map_mul]
        rfl }
  have hφ0_coe : ∀ b : Additive ↥Bs,
      ((φ0 b : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) =
        (Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict (Additive.toMul b))) :
          Fin 6 → ZMod 3) :=
    fun b => rfl
  have hφ0_zero : ∀ b : Additive ↥Bs,
      φ0 b = 0 ↔ Additive.toMul b ∈ (Subgroup.zpowers x).subgroupOf Bs := by
    intro b
    have h1 : φ0 b = 0 ↔ (ggGamma L hBsN) (Additive.toMul b) = 1 := by
      constructor
      · intro h
        have h3 : Multiplicative.toAdd
            (Φ ((ggGamma L hBsN).rangeRestrict (Additive.toMul b))) = 0 := by
          have h4 := congrArg (fun x : NoOffRest.hypE6 =>
            (x : Fin Tag.E6.rank → ZMod 3)) h
          rw [hφ0_coe b] at h4
          exact h4
        have hh := congrArg Multiplicative.ofAdd h3
        have h' : Φ ((ggGamma L hBsN).rangeRestrict (Additive.toMul b)) = 1 := hh
        have h'' : (ggGamma L hBsN).rangeRestrict (Additive.toMul b) = 1 :=
          (hΦ_eq_one _).mp h'
        exact Subtype.ext_iff.mp h''
      · intro h
        have h' : (ggGamma L hBsN).rangeRestrict (Additive.toMul b) = 1 := by
          apply Subtype.ext
          simpa using h
        apply Subtype.ext
        rw [hφ0_coe b, h', map_one]
        rfl
    rw [h1, ← hkerγ]
    exact MonoidHom.mem_ker
  let κm : ↥Bs →* Multiplicative (ZMod 3) :=
    { toFun := fun b => Multiplicative.ofAdd (Kf b : ZMod 3)
      map_one' := by
        have h := (decomp_unique hxinf hxord (hLf 1) (Subgroup.one_mem L)
          (k := Kf 1) (k' := 0) (by simpa using (hKf 1).symm)).2
        show Multiplicative.ofAdd (Kf 1 : ZMod 3) = 1
        rw [show (Kf 1 : ZMod 3) = 0 by simpa using h]
        rfl
      map_mul' := by
        intro b1 b2
        have heq : Lf (b1 * b2) * x ^ Kf (b1 * b2) =
            (Lf b1 * Lf b2) * x ^ (Kf b1 + Kf b2) := by
          rw [← hKf (b1 * b2)]
          show (b1 : G) * (b2 : G) = (Lf b1 * Lf b2) * x ^ (Kf b1 + Kf b2)
          rw [hKf b1, hKf b2, pow_add]
          calc Lf b1 * x ^ Kf b1 * (Lf b2 * x ^ Kf b2)
              = Lf b1 * (x ^ Kf b1 * Lf b2) * x ^ Kf b2 := by group
            _ = Lf b1 * (Lf b2 * x ^ Kf b1) * x ^ Kf b2 := by
                  rw [pow_mul_comm (hxcomm (Lf b2) (hLf b2)) (Kf b1)]
            _ = Lf b1 * Lf b2 * (x ^ Kf b1 * x ^ Kf b2) := by group
        have h := (decomp_unique hxinf hxord (hLf (b1 * b2))
          (Subgroup.mul_mem _ (hLf b1) (hLf b2)) heq).2
        have hK : (Kf (b1 * b2) : ZMod 3) = (Kf b1 : ZMod 3) + (Kf b2 : ZMod 3) := by
          simpa using h
        show Multiplicative.ofAdd (Kf (b1 * b2) : ZMod 3) =
          Multiplicative.ofAdd (Kf b1 : ZMod 3) * Multiplicative.ofAdd (Kf b2 : ZMod 3)
        rw [hK]
        rfl }
  let κ : Additive ↥Bs →+ ZMod 3 :=
    { toFun := fun b => Multiplicative.toAdd (κm (Additive.toMul b))
      map_zero' := by simp
      map_add' := by
        intro a b
        change Multiplicative.toAdd (κm (Additive.toMul a * Additive.toMul b)) =
          Multiplicative.toAdd (κm (Additive.toMul a)) +
            Multiplicative.toAdd (κm (Additive.toMul b))
        rw [map_mul]
        rfl }
  let y' : ↥Bs := ⟨x, hxBs⟩
  have hKf_x : (Kf y' : ZMod 3) = 1 := by
    have h := (decomp_unique hxinf hxord (hLf y') (Subgroup.one_mem L)
      (k := Kf y') (k' := 1) (by simpa [y'] using (hKf y').symm)).2
    simpa using h
  have hκm_x : κm y' = Multiplicative.ofAdd (1 : ZMod 3) := by
    show Multiplicative.ofAdd (Kf y' : ZMod 3) = Multiplicative.ofAdd (1 : ZMod 3)
    rw [hKf_x]
  have hκ_x : κ (Additive.ofMul y') = 1 := by
    show Multiplicative.toAdd (κm y') = 1
    rw [hκm_x]
    rfl
  have hy'3 : y' ^ 3 = 1 := by apply Subtype.ext; simpa [y'] using hx3
  have hy'ne : y' ≠ 1 := by
    intro h
    apply hx_ne
    have hh := congrArg Subtype.val h
    simpa [y'] using hh
  have hord_y' : orderOf y' = 3 := orderOf_eq_prime hy'3 hy'ne
  have hofAdd3 : (Multiplicative.ofAdd (1 : ZMod 3)) ^ 3 = 1 := by decide +kernel
  have hofAddne : (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1 := by decide +kernel
  have hord_ofAdd1 : orderOf (Multiplicative.ofAdd (1 : ZMod 3)) = 3 :=
    orderOf_eq_prime hofAdd3 hofAddne
  have hL_iff : ∀ b : ↥Bs, (b : G) ∈ L ↔ (Kf b : ZMod 3) = 0 := by
    intro b
    constructor
    · intro hbL
      have h := (decomp_unique hxinf hxord (hLf b) hbL
        (k := Kf b) (k' := 0) (by simpa using (hKf b).symm)).2
      simpa using h
    · intro hK0
      have hdvd : 3 ∣ Kf b := (ZMod.natCast_eq_zero_iff (Kf b) 3).mp hK0
      have hxpow : x ^ Kf b = 1 := by
        have hdvd' : orderOf x ∣ Kf b := by rwa [hxord]
        exact (orderOf_dvd_iff_pow_eq_one).mp hdvd'
      have hb : (b : G) = Lf b := by rw [hKf b, hxpow, mul_one]
      rw [hb]
      exact hLf b
  let cF : NoOffRest.hypE6 →+ Vec6 :=
    { toFun := fun v => coordF.mulVec (v : Fin Tag.E6.rank → ZMod 3)
      map_zero' := by simp
      map_add' := by intro v w; simp [Matrix.mulVec_add] }
  let e5hom : ZMod 3 →+ Vec6 :=
    { toFun := fun c => c • Pi.single 5 1
      map_zero' := by simp
      map_add' := by intro c d; rw [add_smul] }
  let ι0 : Additive ↥Bs →+ Vec6 := cF.comp φ0 + e5hom.comp κ
  have hι0_apply : ∀ b : Additive ↥Bs,
      ι0 b = coordF.mulVec ((φ0 b : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) +
        κ b • Pi.single 5 1 := fun b => rfl
  have hcoordE : ∀ b : Additive ↥Bs,
      coordE.mulVec (ι0 b) = ((φ0 b : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) := by
    intro b
    rw [hι0_apply b, Matrix.mulVec_add, Matrix.mulVec_smul,
      coordE_coordF ((φ0 b : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3)
        (NoOffRest.mem_hypE6.mp (φ0 b).2),
      coordE_mulVec_single_five, smul_zero]
    exact add_zero _
  have hker : ∀ b : Additive ↥Bs, ι0 b = 0 → b = 0 := by
    intro b hb
    have h5 : (ι0 b) 5 = κ b := by
      rw [hι0_apply b]
      simp only [Pi.add_apply, coordF_five
          ((φ0 b : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3)
          (NoOffRest.mem_hypE6.mp (φ0 b).2),
        Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, zero_add]
    have hκb : κ b = 0 := by rw [← h5, hb]; rfl
    have hφ0b : φ0 b = 0 := by
      apply Subtype.ext
      have hc := hcoordE b
      rw [hb] at hc
      rw [← hc]
      simp
    have hmemSub : Additive.toMul b ∈ (Subgroup.zpowers x).subgroupOf Bs :=
      (hφ0_zero b).mp hφ0b
    have hmem : Additive.toMul b ∈ Subgroup.zpowers y' := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hmemSub)
      exact Subgroup.mem_zpowers_iff.mpr ⟨j, by apply Subtype.ext; simpa [y'] using hj⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hκm1 : κm (Additive.toMul b) = 1 := by
      have h0 : Multiplicative.toAdd (κm (Additive.toMul b)) = 0 := hκb
      have hh := congrArg Multiplicative.ofAdd h0
      simpa using hh
    have h1 : (Multiplicative.ofAdd (1 : ZMod 3)) ^ j = 1 := by
      rw [← hκm_x, ← map_zpow, hj]
      exact hκm1
    have hdvd : (3 : ℤ) ∣ j := by
      have := (orderOf_dvd_iff_zpow_eq_one).mpr h1
      rwa [hord_ofAdd1] at this
    have hyj : y' ^ j = 1 := by
      have hdvd' : (orderOf y' : ℤ) ∣ j := by rw [hord_y']; exact hdvd
      exact (orderOf_dvd_iff_zpow_eq_one).mp hdvd'
    have hb1 : Additive.toMul b = 1 := by rw [← hj, hyj]
    change Additive.ofMul (Additive.toMul b) = 0
    rw [hb1]
    rfl
  have hinj : Function.Injective ι0 := by
    intro a b hab
    have h : ι0 (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hker (a - b) h)
  have hcard_Add : Nat.card (Additive ↥Bs) = 3 ^ 6 := by
    rw [Nat.card_congr Additive.toMul, hcardBs]
  have hbij : Function.Bijective ι0 :=
    hinj.bijective_of_nat_card_le (by rw [hcardVec, hcard_Add])
  refine ⟨AddEquiv.ofBijective ι0 hbij, ?_, ?_, ?_⟩
  · change ι0 (Additive.ofMul y') = Pi.single 5 1
    have hφ0y : φ0 (Additive.ofMul y') = 0 := by
      apply (hφ0_zero (Additive.ofMul y')).mpr
      exact Subgroup.mem_subgroupOf.mpr (by simpa [y'] using Subgroup.mem_zpowers x)
    rw [hι0_apply (Additive.ofMul y'), hφ0y, hκ_x]
    simp
  · intro b
    change (b : G) ∈ L ↔ ι0 (Additive.ofMul b) 5 = 0
    have h5 : (ι0 (Additive.ofMul b)) 5 = (Kf b : ZMod 3) := by
      rw [hι0_apply (Additive.ofMul b)]
      simp only [Pi.add_apply, coordF_five
          ((φ0 (Additive.ofMul b) : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3)
          (NoOffRest.mem_hypE6.mp (φ0 (Additive.ofMul b)).2),
        Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, zero_add]
      rfl
    rw [h5]
    exact hL_iff b
  · intro b _
    change coordE.mulVec (ι0 (Additive.ofMul b)) =
      Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict b))
    rw [hcoordE (Additive.ofMul b), hφ0_coe (Additive.ofMul b)]
    rfl

end E6Dep

end CFSG.StandardType

end

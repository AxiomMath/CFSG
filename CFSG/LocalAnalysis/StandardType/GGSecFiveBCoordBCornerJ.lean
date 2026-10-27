module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerStd
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerRaw
public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneSignedPermFix
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.GGQ2Frame

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


variable {G : Type} [Group G]

private theorem ggLinImage_inf {p : ℕ} {Bs : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) (P Q : Subgroup G) :
    ggLinImage (p := p) ι (P ⊓ Q) = ggLinImage ι P ⊓ ggLinImage ι Q := by
  ext v
  rw [mem_ggLinImage, Submodule.mem_inf, mem_ggLinImage, mem_ggLinImage, Subgroup.mem_inf]

private theorem corner_W_shape_φ_ne {Bs : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    (g' : ↥L) (hgN' : g' ∈ Subgroup.normalizer (Bs.subgroupOf L : Set ↥L))
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (b : ↥Bs) (hb_ne : (g' : G) * (b : G) * (g' : G)⁻¹ ≠ (b : G))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k) :
    ggLin (p := 3) R.coord ((Bs.subgroupOf L).normalizerMonoidHom ⟨g', hgN'⟩) ≠ 1 := by
  intro h1
  change ggLin (p := 3) R.coord ((Bs.subgroupOf L).normalizerMonoidHom ⟨g', hgN'⟩) = 1 at h1
  have hψ1 : (Bs.subgroupOf L).normalizerMonoidHom ⟨g', hgN'⟩ = 1 :=
    ggLin_injective R.coord (by simpa using h1)
  obtain ⟨a, ha_mem, j, hk⟩ := hsplit b b.2
  have haL : a ∈ L := (Subgroup.mem_inf.mp ha_mem).2
  have haBs : a ∈ Bs := (Subgroup.mem_inf.mp ha_mem).1
  let a' : ↥(Bs.subgroupOf L) := ⟨⟨a, haL⟩, Subgroup.mem_subgroupOf.mpr haBs⟩
  have hψa : (((Bs.subgroupOf L).normalizerMonoidHom ⟨g', hgN'⟩) a' : ↥L) = a' := by
    have h := congrArg (fun (θ : MulAut ↥(Bs.subgroupOf L)) =>
      ((θ a' : ↥(Bs.subgroupOf L)) : ↥L)) hψ1
    simpa using h
  have hga : (g' : G) * a * (g' : G)⁻¹ = a := by
    have h := congrArg (fun z : ↥L => (z : G)) hψa
    simpa [a', Subgroup.normalizerMonoidHom_apply_apply_coe] using h
  have hxcent : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hLx hy) x (Set.mem_singleton x)).symm
  have hxg : (g' : G) * x = x * (g' : G) :=
    Subgroup.mem_centralizer_iff.mp hxcent (g' : G) g'.2
  have hxk : (g' : G) * x ^ j * (g' : G)⁻¹ = x ^ j := by
    have hconj : (MulAut.conj (g' : G)) x = x := by
      rw [MulAut.conj_apply]
      calc (g' : G) * x * (g' : G)⁻¹ = (x * (g' : G)) * (g' : G)⁻¹ := by rw [hxg]
        _ = x := by group
    have h := congrArg (fun y => y ^ j) hconj
    rw [← map_zpow] at h
    simpa [MulAut.conj_apply] using h
  have hb_eq : (g' : G) * (b : G) * (g' : G)⁻¹ = (b : G) := by
    have hkG : (b : G) = a * x ^ j := hk
    calc
      (g' : G) * (b : G) * (g' : G)⁻¹ = (g' : G) * (a * x ^ j) * (g' : G)⁻¹ := by rw [hkG]
      _ = ((g' : G) * a * (g' : G)⁻¹) * ((g' : G) * x ^ j * (g' : G)⁻¹) := by group
      _ = a * x ^ j := by rw [hga, hxk]
      _ = (b : G) := hkG.symm
  exact hb_ne hb_eq

private theorem corner_W_shape_fix {B Bs : Subgroup G} {L : Subgroup G} {n : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    (g' : ↥L) (hgN' : g' ∈ Subgroup.normalizer (Bs.subgroupOf L : Set ↥L))
    (hgC : ∀ b : ↥Bs, (b : G) ∈ B → (g' : G) * (b : G) * (g' : G)⁻¹ = (b : G)) :
    ∀ w ∈ ggLinImage (p := 3) R.coord (B.subgroupOf L),
      ggLin (p := 3) R.coord ((Bs.subgroupOf L).normalizerMonoidHom ⟨g', hgN'⟩) w = w := by
  intro w hw
  obtain ⟨y, rfl⟩ : ∃ y : ↥(Bs.subgroupOf L), R.coord (Additive.ofMul y) = w :=
    ⟨Additive.toMul (R.coord.symm w), by simp⟩
  rw [ggLin_apply_ofMul]
  have hψy : (Bs.subgroupOf L).normalizerMonoidHom ⟨g', hgN'⟩ y = y := by
    apply Subtype.ext
    have hyB : ((y : ↥L) : G) ∈ B := by
      rw [← Subgroup.mem_subgroupOf, ← ofMul_mem_ggLinImage (p := 3) R.coord (B.subgroupOf L) y]
      exact hw
    have h := hgC ⟨((y : ↥L) : G), Subgroup.mem_subgroupOf.mp y.2⟩ hyB
    have hψy_eq :
        ((((Bs.subgroupOf L).normalizerMonoidHom ⟨g', hgN'⟩) y : ↥(Bs.subgroupOf L)) : ↥L) =
          g' * (y : ↥L) * g'⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe (Bs.subgroupOf L) ⟨g', hgN'⟩ y
    rw [hψy_eq]
    exact Subtype.ext (by simpa using h)
  rw [hψy]

private theorem corner_label {Bs L J : Subgroup G} {n : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    (c : PlaneRaw.Code (n - 1))
    (hadm : PlaneRaw.admissible .symplectic c)
    (hJ : J = (R.component c).map L.subtype)
    (hsmall : ∀ c, PlaneRaw.admissible .symplectic c →
      (PlaneRaw.label .symplectic c = ⟨.B2der, 0, 1⟩ ∨
        PlaneRaw.label .symplectic c = ⟨.twA, 3, 1⟩) →
      LargeEvenSmall (R.component c))
    (hnsmall : ¬ LargeEvenSmall J) :
    PlaneRaw.label .symplectic c ≠ ⟨.B2der, 0, 1⟩ ∧
      PlaneRaw.label .symplectic c ≠ ⟨.twA, 3, 1⟩ := by
  constructor
  · intro hlab
    apply hnsmall
    rw [hJ]
    exact (A6InsideSp.largeEvenSmall_map_iff L.subtype_injective (R.component c)).mpr
      (hsmall c hadm (Or.inl hlab))
  · intro hlab
    apply hnsmall
    rw [hJ]
    exact (A6InsideSp.largeEvenSmall_map_iff L.subtype_injective (R.component c)).mpr
      (hsmall c hadm (Or.inr hlab))

variable [Finite G]

private theorem corner_z {B Bs : Subgroup G} {x : G} {L D : Subgroup G}
    (hBBs : B ≤ Bs) (hBs : IsElemAbelian 3 Bs)
    (hx1 : x ≠ 1) (hxB : x ∈ B) (hDB : D ≤ B)
    (hDcard : Nat.card D = 3 ^ 2) (hxD : x ∈ D)
    (hxL : Subgroup.zpowers x ⊓ L = ⊥)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k) :
    ∃ z : ↥(Bs.subgroupOf L), ((z : ↥L) : G) ≠ 1 ∧ ((z : ↥L) : G) ∈ B ∧
      D = Subgroup.zpowers x ⊔ Subgroup.zpowers ((z : ↥L) : G) := by
  have hxBs : x ∈ Bs := hBBs hxB
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, show orderOf x = 3 from
      @orderOf_eq_prime G _ x 3 ⟨by norm_num⟩ (hBs.2 x hxBs) hx1]
  have hD_ne : D ≠ Subgroup.zpowers x := by
    intro h
    have hcard : Nat.card D = Nat.card (Subgroup.zpowers x) := by rw [h]
    rw [hDcard, hxcard] at hcard
    omega
  have hex : ∃ d ∈ D, d ∉ Subgroup.zpowers x := by
    by_contra h
    push Not at h
    exact hD_ne (le_antisymm h (Subgroup.zpowers_le.mpr hxD))
  obtain ⟨d, hdD, hd_not_zpow⟩ := hex
  have hdBs : d ∈ Bs := hBBs (hDB hdD)
  obtain ⟨a, ha_mem, k, hk⟩ := hsplit d hdBs
  obtain ⟨haBs, haL⟩ := Subgroup.mem_inf.mp ha_mem
  have ha_D : a ∈ D := by
    have ha_eq : a = d * x ^ (-k) := by
      rw [hk]
      group
    rw [ha_eq]
    exact Subgroup.mul_mem _ hdD (Subgroup.zpow_mem _ hxD (-k))
  have ha_ne : a ≠ 1 := by
    intro ha1
    apply hd_not_zpow
    rw [hk, ha1, one_mul]
    exact Subgroup.zpow_mem_zpowers x k
  let z : ↥(Bs.subgroupOf L) := ⟨⟨a, haL⟩, Subgroup.mem_subgroupOf.mpr haBs⟩
  have hzG : ((z : ↥L) : G) = a := rfl
  have h9 := isElemAbelian_zpowers_sup_zpowers_of_inf_eq_bot
    (B := B) (Bs := Bs) (L := L) (x := x) (e := z)
    hBBs hBs hx1 hxB (by rw [hzG]; exact ha_ne) hxL
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers ((z : ↥L) : G) ≤ D :=
    sup_le (Subgroup.zpowers_le.mpr hxD)
      (Subgroup.zpowers_le.mpr (by rw [hzG]; exact ha_D))
  have hDeq : D = Subgroup.zpowers x ⊔ Subgroup.zpowers ((z : ↥L) : G) :=
    (Subgroup.eq_of_le_of_card_ge hle (by
      rw [hDcard, h9.2])).symm
  exact ⟨z, by rw [hzG]; exact ha_ne, by rw [hzG]; exact hDB ha_D, hDeq⟩

private theorem corner_component {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n : ℕ}
    (hC : GGConfig 3 B Bs x L D J)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    (z : ↥(Bs.subgroupOf L))
    (hD_eq : D = Subgroup.zpowers x ⊔ Subgroup.zpowers ((z : ↥L) : G)) :
    ∃ c : PlaneRaw.Code (n - 1),
      PlaneRaw.admissible .symplectic c ∧ J = (R.component c).map L.subtype ∧
      PlaneRaw.occurs (Submodule.span PlaneRaw.F {R.coord (Additive.ofMul z)}) c := by
  have hThm : GGThmIHyp 3 B x L := hC.1
  obtain ⟨hBBs, hBs, hBscard, hBscent⟩ := hC.2.1
  obtain ⟨hStdPre, hStdSmall⟩ := hC.2.2
  obtain ⟨hDB, hDab, hDcard, hxD, hJeq, hJcomp, hDCJ⟩ := hStdPre
  obtain ⟨-, hxB, hx1, hLcomp, -⟩ := hThm.2.2.2.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hLcomp.1
  have hJcomp' : IsComponentOf J
      (L ⊓ Subgroup.centralizer (Subgroup.zpowers ((z : ↥L) : G) : Set G)) := by
    have h := hJcomp
    have hcent : Subgroup.centralizer (D : Set G) =
        Subgroup.centralizer ((Subgroup.zpowers x ⊔
          Subgroup.zpowers ((z : ↥L) : G) : Subgroup G) : Set G) := by
      rw [hD_eq]
    rw [hcent, inf_centralizer_zpowers_sup_eq (L := L) (x := x)
      (z := ((z : ↥L) : G)) hLx] at h
    exact h
  have hJsub : IsComponentOf (J.subgroupOf L)
      ((L ⊓ Subgroup.centralizer (Subgroup.zpowers ((z : ↥L) : G) : Set G)).subgroupOf L) :=
    ggIsComponentOf_subgroupOf hJcomp' inf_le_left
  rw [subgroupOf_inf_centralizer_zpowers (z := (z : ↥L))] at hJsub
  have hzmem : (z : ↥L) ∈ Bs.subgroupOf L := z.2
  obtain ⟨c, hadm, hocc, hcomp⟩ :=
    (R.occurs_iff (Subgroup.zpowers (z : ↥L)) (Subgroup.zpowers_le.mpr hzmem)
      (J.subgroupOf L)).mp hJsub
  have hJle : J ≤ L := hJcomp.1.trans inf_le_left
  refine ⟨c, hadm.2, ?_, ?_⟩
  · rw [← hcomp, Subgroup.map_subgroupOf_eq_of_le hJle]
  · have hz_eq : (⟨(z : ↥L), hzmem⟩ : ↥(Bs.subgroupOf L)) = z := Subtype.ext rfl
    have hspan : Submodule.span PlaneRaw.F {R.coord (Additive.ofMul z)} =
        ggLinImage (p := 3) R.coord (Subgroup.zpowers (z : ↥L)) := by
      simpa [hz_eq] using (span_singleton_eq_ggLinImage (p := 3) R.coord hzmem)
    exact hspan ▸ hocc

private theorem corner_cent_card_Dsub {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n : ℕ}
    (hC : GGConfig 3 B Bs x L D J)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    (c : PlaneRaw.Code (n - 1))
    (hJ : J = (R.component c).map L.subtype) :
    (D ⊓ L).subgroupOf L =
      Subgroup.centralizer (R.component c : Set ↥L) ⊓ B.subgroupOf L := by
  obtain ⟨hDB, hDab, hDcard, hxD, hJeq, hJcomp, hDCJ⟩ := hC.2.2.1
  have hsub : ((R.component c).map L.subtype).subgroupOf L = R.component c := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hyx' : y = x := Subtype.ext (by simpa using hyx)
      rwa [hyx'] at hy
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem L.subtype hx
  have hJsub : J.subgroupOf L = R.component c := by
    rw [hJ]
    exact hsub
  have hDsub : (D ⊓ L).subgroupOf L =
      Subgroup.centralizer (R.component c : Set ↥L) ⊓ B.subgroupOf L := by
    have hleJ : J ≤ L := hJcomp.1.trans inf_le_left
    calc
      (D ⊓ L).subgroupOf L =
          ((B ⊓ Subgroup.centralizer (J : Set G)) ⊓ L).subgroupOf L := by rw [hDCJ]
      _ = (B ⊓ Subgroup.centralizer (J : Set G)).subgroupOf L := by
        rw [CFSG.LocalAnalysis.GLTheoremA.S265.subgroupOf_inf',
          Subgroup.subgroupOf_self, inf_top_eq]
      _ = B.subgroupOf L ⊓ (Subgroup.centralizer (J : Set G)).subgroupOf L := by
        rw [CFSG.LocalAnalysis.GLTheoremA.S265.subgroupOf_inf']
      _ = B.subgroupOf L ⊓ Subgroup.centralizer (J.subgroupOf L : Set ↥L) := by
        rw [CFSG.LocalAnalysis.GLTheoremA.S265.subgroupOf_centralizer hleJ]
      _ = Subgroup.centralizer (R.component c : Set ↥L) ⊓ B.subgroupOf L := by
        rw [hJsub, inf_comm]
  exact hDsub

private theorem corner_cent_card_DinfL_z {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J)
    (z : ↥(Bs.subgroupOf L))
    (hxL : Subgroup.zpowers x ⊓ L = ⊥)
    (hD_eq : D = Subgroup.zpowers x ⊔ Subgroup.zpowers ((z : ↥L) : G)) :
    ((z : ↥L) : G) ≠ 1 ∧
      Nat.card (Subgroup.zpowers ((z : ↥L) : G)) = 3 ∧
      x ∉ L ∧
      Subgroup.zpowers ((z : ↥L) : G) ≤ D ⊓ L := by
  obtain ⟨hBBs, hBs, hBscard, -⟩ := hC.2.1
  have hThm : GGThmIHyp 3 B x L := hC.1
  obtain ⟨-, hxB, hx1, -, -⟩ := hThm.2.2.2.2.2.2.1
  obtain ⟨hDB, hDab, hDcard, hxD, hJeq, hJcomp, hDCJ⟩ := hC.2.2.1
  have hxBs : x ∈ Bs := hBBs hxB
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, show orderOf x = 3 from
      @orderOf_eq_prime G _ x 3 ⟨by norm_num⟩ (hBs.2 x hxBs) hx1]
  have hz_ne : ((z : ↥L) : G) ≠ 1 := by
    intro hz1
    have hDz : D = Subgroup.zpowers x := by
      rw [hD_eq, hz1, Subgroup.zpowers_one_eq_bot, sup_bot_eq]
    have : Nat.card D = 3 := by rw [hDz, hxcard]
    rw [hDcard] at this
    omega
  have hzBs : ((z : ↥L) : G) ∈ Bs := Subgroup.mem_subgroupOf.mp z.2
  have hzG3 : ((z : ↥L) : G) ^ 3 = 1 := hBs.2 _ hzBs
  have hzord : orderOf ((z : ↥L) : G) = 3 :=
    @orderOf_eq_prime G _ _ 3 ⟨by norm_num⟩ hzG3 hz_ne
  have hzcard : Nat.card (Subgroup.zpowers ((z : ↥L) : G)) = 3 := by
    rw [Nat.card_zpowers, hzord]
  have hx_not_L : x ∉ L := by
    intro hxL'
    have : x ∈ Subgroup.zpowers x ⊓ L := Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers x, hxL'⟩
    rw [hxL] at this
    exact hx1 (Subgroup.mem_bot.mp this)
  have hz_inf : Subgroup.zpowers ((z : ↥L) : G) ≤ D ⊓ L :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr
      ⟨by rw [hD_eq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _),
        (z : ↥L).2⟩)
  exact ⟨hz_ne, hzcard, hx_not_L, hz_inf⟩

private theorem corner_cent_card_DinfL {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J)
    (z : ↥(Bs.subgroupOf L))
    (hxL : Subgroup.zpowers x ⊓ L = ⊥)
    (hD_eq : D = Subgroup.zpowers x ⊔ Subgroup.zpowers ((z : ↥L) : G)) :
    Nat.card ↥(D ⊓ L) = 3 := by
  obtain ⟨hDB, hDab, hDcard, hxD, hJeq, hJcomp, hDCJ⟩ := hC.2.2.1
  obtain ⟨hz_ne, hzcard, hx_not_L, hz_inf⟩ :=
    corner_cent_card_DinfL_z hC z hxL hD_eq
  have hcard_inf : Nat.card ↥(D ⊓ L) = 3 := by
    have hdvd : Nat.card ↥(D ⊓ L) ∣ Nat.card ↥D := Subgroup.card_dvd_of_le inf_le_left
    have hdvd' : Nat.card ↥(D ⊓ L) ∣ 3 ^ 2 := by
      rw [← hDcard]
      exact hdvd
    obtain ⟨k, hk_le, hk⟩ :=
      (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd'
    have hne_bot : D ⊓ L ≠ ⊥ := by
      intro hbot
      have hz_bot : ((z : ↥L) : G) ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact hz_inf (Subgroup.mem_zpowers _)
      exact hz_ne (Subgroup.mem_bot.mp hz_bot)
    have hne_top : D ⊓ L ≠ D := by
      intro h
      have : x ∈ D ⊓ L := by rw [h]; exact hxD
      exact hx_not_L (Subgroup.mem_inf.mp this).2
    interval_cases k
    · exact absurd (Subgroup.card_eq_one.mp hk) hne_bot
    · rw [hk]
      norm_num
    · exact absurd (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, hDcard])) hne_top
  have hDinfL : D ⊓ L = Subgroup.zpowers ((z : ↥L) : G) :=
    (Subgroup.eq_of_le_of_card_ge hz_inf (by rw [hcard_inf, hzcard])).symm
  rw [hDinfL, hzcard]

private theorem corner_cent_card {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n : ℕ}
    (hC : GGConfig 3 B Bs x L D J)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    (z : ↥(Bs.subgroupOf L)) (c : PlaneRaw.Code (n - 1))
    (hn : 5 ≤ n) (hxL : Subgroup.zpowers x ⊓ L = ⊥)
    (hadm : PlaneRaw.admissible .symplectic c)
    (hJ : J = (R.component c).map L.subtype)
    (hD_eq : D = Subgroup.zpowers x ⊔ Subgroup.zpowers ((z : ↥L) : G)) :
    Nat.card ↥(PlaneRaw.cent .symplectic c ⊓
      ggLinImage (p := 3) R.coord (B.subgroupOf L)) = 3 := by
  obtain ⟨hBBs, hBs, hBscard, hBscent⟩ := hC.2.1
  have hadm' : (planeEntry .symplectic (n - 1)).admissible c := ⟨by omega, hadm⟩
  have hcent : ggLinImage (p := 3) R.coord
      (Subgroup.centralizer (R.component c : Set ↥L)) = PlaneRaw.cent .symplectic c :=
    R.cent_eq c hadm'
  have h1 : PlaneRaw.cent .symplectic c ⊓
      ggLinImage (p := 3) R.coord (B.subgroupOf L) =
      ggLinImage (p := 3) R.coord
        (Subgroup.centralizer (R.component c : Set ↥L) ⊓ B.subgroupOf L) := by
    rw [← hcent, ggLinImage_inf]
    rfl
  have hcard0 := card_ggLinImage (p := 3) R.coord
    (Subgroup.centralizer (R.component c : Set ↥L) ⊓ B.subgroupOf L)
  rw [h1]
  have hcard0' : Nat.card ↥(ggLinImage (p := 3) R.coord
      (Subgroup.centralizer (R.component c : Set ↥L) ⊓ B.subgroupOf L)) =
      Nat.card ↥((Bs.subgroupOf L) ⊓
        (Subgroup.centralizer (R.component c : Set ↥L) ⊓ B.subgroupOf L)) := by
    simpa using hcard0
  erw [hcard0']
  have hle : B.subgroupOf L ≤ Bs.subgroupOf L := Subgroup.comap_mono hBBs
  have h2 : (Bs.subgroupOf L) ⊓
      (Subgroup.centralizer (R.component c : Set ↥L) ⊓ B.subgroupOf L) =
      Subgroup.centralizer (R.component c : Set ↥L) ⊓ B.subgroupOf L :=
    inf_eq_right.mpr (le_trans inf_le_right hle)
  rw [h2, ← corner_cent_card_Dsub hC R c hJ]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
  exact corner_cent_card_DinfL hC z hxL hD_eq

private theorem corner_W_card_nat {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (hne : B ≠ Bs) :
    Nat.card Bs = 3 ^ n ∧ Nat.card B = 3 ^ (n - 1) := by
  obtain ⟨hBBs, hBs, hBscard, -⟩ := hC.2.1
  have hBs_n : Nat.card Bs = 3 ^ n := by
    rw [Nat.card_congr eta.toEquiv, Nat.card_fun]
    simp
  have hB_dvd : Nat.card B ∣ 3 ^ n := by
    rw [← hBs_n]
    exact Subgroup.card_dvd_of_le hBBs
  obtain ⟨k, hk_le, hk_eq⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hB_dvd
  have hB_n : Nat.card B = 3 ^ (n - 1) := by
    have hk_ne : k ≠ n := by
      intro hkn
      have hcard_eq : Nat.card B = Nat.card Bs := by rw [hk_eq, hkn, hBs_n]
      exact hne (Subgroup.eq_of_le_of_card_ge hBBs (le_of_eq hcard_eq.symm))
    have hle : 3 ^ n ≤ 3 ^ (k + 1) := by
      have h := hBscard
      rw [hBs_n, hk_eq] at h
      calc 3 ^ n ≤ 3 * 3 ^ k := h
        _ = 3 ^ (k + 1) := by rw [pow_succ]; ring
    have hnk : n ≤ k + 1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
    have hk_eq' : k = n - 1 := by omega
    rw [hk_eq, hk_eq']
  exact ⟨hBs_n, hB_n⟩

private theorem corner_W_card_Bs_card {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (hne : B ≠ Bs)
    (hxL : Subgroup.zpowers x ⊓ L = ⊥)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k) :
    Nat.card ↥(Bs ⊓ L) = 3 ^ (n - 1) := by
  obtain ⟨hBBs, hBs, hBscard, -⟩ := hC.2.1
  have hThm : GGThmIHyp 3 B x L := hC.1
  obtain ⟨-, hxB, hx1, -, -⟩ := hThm.2.2.2.2.2.2.1
  obtain ⟨hBs_n, -⟩ := corner_W_card_nat hC hn eta hne
  have hxBs : x ∈ Bs := hBBs hxB
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, show orderOf x = 3 from
      @orderOf_eq_prime G _ x 3 ⟨by norm_num⟩ (hBs.2 x hxBs) hx1]
  have hBsSup : (Bs ⊓ L) ⊔ Subgroup.zpowers x = Bs := by
    apply le_antisymm
    · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr hxBs)
    · intro b hb
      obtain ⟨a, ha, j, hk⟩ := hsplit b hb
      rw [hk]
      exact Subgroup.mul_mem_sup ha (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) j)
  have hBsDisj : (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥ := by
    apply le_antisymm
    · intro y hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
      have hy_bot : y ∈ (⊥ : Subgroup G) := by
        rw [← hxL]
        exact Subgroup.mem_inf.mpr ⟨hy2, (Subgroup.mem_inf.mp hy1).2⟩
      exact Subgroup.mem_bot.mp hy_bot
    · exact bot_le
  have hcommBs : ∀ a ∈ Bs ⊓ L, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hBs.1.is_comm.comm
      ⟨a, (Subgroup.mem_inf.mp ha).1⟩ ⟨b, Subgroup.zpowers_le.mpr hxBs hb⟩)
  have hBs_card_mul : Nat.card Bs = Nat.card ↥(Bs ⊓ L) * 3 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Bs ⊓ L) (Subgroup.zpowers x) hcommBs).1
    rw [hBsSup, hBsDisj, Subgroup.card_bot, mul_one, hxcard] at h
    exact h
  have h : Nat.card ↥(Bs ⊓ L) * 3 = 3 ^ n := by
    rw [← hBs_card_mul, hBs_n]
  have h' : Nat.card ↥(Bs ⊓ L) * 3 = 3 ^ (n - 1) * 3 := by
    rw [h]
    rw [show 3 ^ n = 3 ^ (n - 1) * 3 by
      rw [← pow_succ]; congr 1; omega]
  omega

private theorem corner_W_card_B_card_mul {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J)
    (hxL : Subgroup.zpowers x ⊓ L = ⊥)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k) :
    Nat.card B = Nat.card ↥(B ⊓ L) * 3 := by
  obtain ⟨hBBs, hBs, hBscard, -⟩ := hC.2.1
  have hThm : GGThmIHyp 3 B x L := hC.1
  obtain ⟨-, hxB, hx1, -, -⟩ := hThm.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hBBs hxB
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, show orderOf x = 3 from
      @orderOf_eq_prime G _ x 3 ⟨by norm_num⟩ (hBs.2 x hxBs) hx1]
  have hBSup : (B ⊓ L) ⊔ Subgroup.zpowers x = B := by
    apply le_antisymm
    · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr hxB)
    · intro b hb
      have hbBs : b ∈ Bs := hBBs hb
      obtain ⟨a, ha, j, hk⟩ := hsplit b hbBs
      have haB : a ∈ B := by
        have ha_eq : a = b * x ^ (-j) := by rw [hk]; group
        rw [ha_eq]
        exact Subgroup.mul_mem _ hb (Subgroup.zpow_mem _ hxB (-j))
      have ha_inf : a ∈ B ⊓ L :=
        Subgroup.mem_inf.mpr ⟨haB, (Subgroup.mem_inf.mp ha).2⟩
      rw [hk]
      exact Subgroup.mul_mem_sup ha_inf (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) j)
  have hBDisj : (B ⊓ L) ⊓ Subgroup.zpowers x = ⊥ := by
    apply le_antisymm
    · intro y hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
      have hy_bot : y ∈ (⊥ : Subgroup G) := by
        rw [← hxL]
        exact Subgroup.mem_inf.mpr ⟨hy2, (Subgroup.mem_inf.mp hy1).2⟩
      exact Subgroup.mem_bot.mp hy_bot
    · exact bot_le
  have hcommB : ∀ a ∈ B ⊓ L, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hBs.1.is_comm.comm
      ⟨a, hBBs (Subgroup.mem_inf.mp ha).1⟩ ⟨b, Subgroup.zpowers_le.mpr hxBs hb⟩)
  have hB_card_mul : Nat.card B = Nat.card ↥(B ⊓ L) * 3 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (B ⊓ L) (Subgroup.zpowers x) hcommB).1
    rw [hBSup, hBDisj, Subgroup.card_bot, mul_one, hxcard] at h
    exact h
  exact hB_card_mul

private theorem corner_W_card_B_card {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (hne : B ≠ Bs)
    (hxL : Subgroup.zpowers x ⊓ L = ⊥)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k) :
    Nat.card ↥(B ⊓ L) = 3 ^ (n - 2) := by
  obtain ⟨hBs_n, hB_n⟩ := corner_W_card_nat hC hn eta hne
  have hBs_inf_card := corner_W_card_Bs_card hC hn eta hne hxL hsplit
  have hB_card_mul := corner_W_card_B_card_mul hC hxL hsplit
  have hBs_card_mul : Nat.card Bs = Nat.card ↥(Bs ⊓ L) * 3 := by
    rw [hBs_n, hBs_inf_card]
    rw [show 3 ^ n = 3 ^ (n - 1) * 3 by rw [← pow_succ]; congr 1; omega]
  have h1 : Nat.card Bs = 3 * Nat.card B := by
    rw [hBs_n, hB_n]
    rw [show 3 ^ n = 3 * 3 ^ (n - 1) by
      rw [mul_comm, ← pow_succ]; congr 1; omega]
  have h : Nat.card ↥(Bs ⊓ L) = Nat.card ↥(B ⊓ L) * 3 := by
    have h2 : Nat.card ↥(Bs ⊓ L) * 3 = Nat.card ↥(B ⊓ L) * 3 * 3 := by
      rw [← hBs_card_mul, h1, hB_card_mul]
      ring_nf
    omega
  rw [hBs_inf_card] at h
  have h' : Nat.card ↥(B ⊓ L) * 3 = 3 ^ (n - 2) * 3 := by
    rw [← h]
    rw [show 3 ^ (n - 1) = 3 ^ (n - 2) * 3 by
      rw [← pow_succ]; congr 1; omega]
  omega

private theorem corner_W_card {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    (hne : B ≠ Bs)
    (hxL : Subgroup.zpowers x ⊓ L = ⊥)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1))) :
    3 * Nat.card ↥(ggLinImage (p := 3) R.coord (B.subgroupOf L)) = 3 ^ (n - 1) := by
  have hBBs : B ≤ Bs := hC.2.1.1
  have hB_inf_card := corner_W_card_B_card hC hn eta hne hxL hsplit
  have hW : Nat.card ↥(ggLinImage (p := 3) R.coord (B.subgroupOf L)) =
      Nat.card ↥(B ⊓ L) := by
    have h := card_ggLinImage (p := 3) R.coord (B.subgroupOf L)
    have hle : B.subgroupOf L ≤ Bs.subgroupOf L := Subgroup.comap_mono hBBs
    rw [inf_eq_right.mpr hle] at h
    rw [h]
    have hBeq : (B ⊓ L).subgroupOf L = B.subgroupOf L := by
      rw [CFSG.LocalAnalysis.GLTheoremA.S265.subgroupOf_inf',
        Subgroup.subgroupOf_self, inf_top_eq]
    rw [← hBeq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [hW, hB_inf_card]
  rw [show 3 * 3 ^ (n - 2) = 3 ^ (n - 1) by
    rw [mul_comm, ← pow_succ]
    congr 1
    omega]

private theorem corner_W_shape {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n : ℕ}
    (hC : GGConfig 3 B Bs x L D J)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    (hRaut : (ggAutomizer (⊤ : Subgroup ↥L) (Bs.subgroupOf L)).map (ggLin (p := 3) R.coord) =
      PlaneRaw.signedPermGroup (n - 1))
    (hW_card : 3 * Nat.card ↥(ggLinImage (p := 3) R.coord (B.subgroupOf L)) = 3 ^ (n - 1))
    (hg : ∃ g : G, g ∈ L ∧ g ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ b : ↥Bs, (b : G) ∈ B → g * b * g⁻¹ = b) ∧ ∃ b : ↥Bs, g * b * g⁻¹ ≠ b)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k) :
    (∃ k, ∀ v, v ∈ ggLinImage (p := 3) R.coord (B.subgroupOf L) ↔ v k = 0) ∨
      ∃ k l, k ≠ l ∧ ∃ s : PlaneRaw.F, s ≠ 0 ∧
        ∀ v, v ∈ ggLinImage (p := 3) R.coord (B.subgroupOf L) ↔ v k = s * v l := by
  have hThm : GGThmIHyp 3 B x L := hC.1
  obtain ⟨-, hxB, hx1, hLcomp, -⟩ := hThm.2.2.2.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hLcomp.1
  obtain ⟨g, hgL, hgN, hgC, b, hb_ne⟩ := hg
  let g' : ↥L := ⟨g, hgL⟩
  have hgN' : g' ∈ Subgroup.normalizer (Bs.subgroupOf L : Set ↥L) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h := (Subgroup.mem_normalizer_iff.mp hgN) (y : G)
    simpa [g', Subgroup.mem_subgroupOf] using h
  let ψ : MulAut ↥(Bs.subgroupOf L) := (Bs.subgroupOf L).normalizerMonoidHom ⟨g', hgN'⟩
  have hψ_ind : ψ ∈ ggInduced (⊤ : Subgroup ↥L) (Bs.subgroupOf L) := by
    refine ⟨g', Subgroup.mem_top g', hgN', ?_⟩
    intro y
    simp [ψ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hψ_aut : ψ ∈ ggAutomizer (⊤ : Subgroup ↥L) (Bs.subgroupOf L) :=
    Subgroup.subset_closure hψ_ind
  let φ : (planeEntry .symplectic (n - 1)).V ≃ₗ[ZMod 3]
      (planeEntry .symplectic (n - 1)).V := ggLin (p := 3) R.coord ψ
  have hφ : φ ∈ PlaneRaw.signedPermGroup (n - 1) := by
    rw [← hRaut]
    exact Subgroup.mem_map_of_mem _ hψ_aut
  have hfix : ∀ w ∈ ggLinImage (p := 3) R.coord (B.subgroupOf L), φ w = w := by
    intro w hw
    have h := corner_W_shape_fix R g' hgN' hgC w hw
    simpa [φ, ψ] using h
  have hφ_ne : φ ≠ 1 := by
    have hne' := corner_W_shape_φ_ne R g' hgN' hLx b hb_ne hsplit
    simpa [φ, ψ] using hne'
  exact PlaneRaw.hyperplane_eq_of_mem_signedPermGroup_fix hφ hφ_ne hW_card hfix

private theorem corner_not_small {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hn : 5 ≤ n)
    (hxL : Subgroup.zpowers x ⊓ L = ⊥)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    (hbig : ∀ S : Finset (Fin (n - 1)), 3 ≤ S.card → 7 ∣ Nat.card (R.component (.zero S)))
    (hshape : (∃ k, ∀ v, v ∈ ggLinImage (p := 3) R.coord (B.subgroupOf L) ↔ v k = 0) ∨
      ∃ k l, k ≠ l ∧ ∃ s : PlaneRaw.F, s ≠ 0 ∧
        ∀ v, v ∈ ggLinImage (p := 3) R.coord (B.subgroupOf L) ↔ v k = s * v l) :
    ¬ LargeEvenSmall J := by
  obtain ⟨i, hiW⟩ : ∃ i, Pi.single i (1 : PlaneRaw.F) ∈
      ggLinImage (p := 3) R.coord (B.subgroupOf L) := by
    rcases hshape with ⟨k, hk⟩ | ⟨k, l, hkl, s, hs, hkl_eq⟩
    · obtain ⟨i, hik⟩ : ∃ i : Fin (n - 1), i ≠ k :=
        Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) k
      exact ⟨i, (hk _).mpr (Pi.single_eq_of_ne (Ne.symm hik) 1)⟩
    · obtain ⟨i, hik, hil⟩ := Fin.exists_ne_and_ne_of_two_lt k l (by omega : 2 < n - 1)
      refine ⟨i, (hkl_eq _).mpr ?_⟩
      rw [Pi.single_eq_of_ne (Ne.symm hik), Pi.single_eq_of_ne (Ne.symm hil), mul_zero]
  let e : ↥(Bs.subgroupOf L) := Additive.toMul (R.coord.symm (Pi.single i 1))
  have he : R.coord (Additive.ofMul e) = Pi.single i 1 := by
    change R.coord (R.coord.symm (Pi.single i 1)) = Pi.single i 1
    exact AddEquiv.apply_symm_apply R.coord _
  have heB : ((e : ↥L) : G) ∈ B := by
    rw [← Subgroup.mem_subgroupOf, ← ofMul_mem_ggLinImage (p := 3) R.coord (B.subgroupOf L) e, he]
    exact hiW
  exact GGConfig.not_largeEvenSmall_of_corner_single hC hxL hsplit (by omega) R hbig he heB


theorem GGConfig.cornerRows {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) {n : ℕ} (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hM : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = n - 1 ∧
      lab.n = 1) 3 Bs L) (hne : B ≠ Bs)
    (hg : ∃ g : G, g ∈ L ∧ g ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ b : ↥Bs, (b : G) ∈ B → g * b * g⁻¹ = b) ∧ ∃ b : ↥Bs, g * b * g⁻¹ ≠ b) :
    GGSecFiveBCoordBCornerRows B Bs x L D J (n - 1) := by
  have hThm : GGThmIHyp 3 B x L := hC.1
  obtain ⟨hBBs, hBs, hBscard, hBscent⟩ := hC.2.1
  obtain ⟨hStdPre, hStdSmall⟩ := hC.2.2
  obtain ⟨hDB, hDab, hDcard, hxD, hJeq, hJcomp, hDCJ⟩ := hStdPre
  obtain ⟨-, hxB, hx1, hLcomp, -⟩ := hThm.2.2.2.2.2.2.1
  obtain ⟨hxL, hsplit, hcardE, R, hRaut, hsmall, hbig⟩ :=
    GGConfig.exists_cornerRealization hC hn eta hb hM
  obtain ⟨z, hz_ne, hzB, hD_eq⟩ :=
    corner_z hBBs hBs hx1 hxB hDB hDcard hxD hxL hsplit
  obtain ⟨c, hadm, hJ, hocc⟩ := corner_component hC R z hD_eq
  have hW_card := corner_W_card hC hn eta hne hxL hsplit R
  have hcard := corner_cent_card hC R z c hn hxL hadm hJ hD_eq
  have hshape := corner_W_shape hC R hRaut hW_card hg hsplit
  have hnsmall := corner_not_small hC hn hxL hsplit R hbig hshape
  have hns := corner_label R c hadm hJ hsmall hnsmall
  have hz_one : z ≠ 1 := by
    intro h
    exact hz_ne (by rw [h]; rfl)
  have hu_ne : R.coord (Additive.ofMul z) ≠ 0 := by
    intro h
    have h1 : Additive.ofMul z = 0 := R.coord.injective (by rwa [map_zero])
    exact hz_one (Additive.ofMul.injective (by simpa using h1))
  have huW : R.coord (Additive.ofMul z) ∈
      ggLinImage (p := 3) R.coord (B.subgroupOf L) :=
    (ofMul_mem_ggLinImage R.coord (B.subgroupOf L) z).mpr
      (Subgroup.mem_subgroupOf.mpr hzB)
  have hrows := PlaneRaw.corner_rows_of_occurs_span (by omega) hshape hu_ne huW hadm hocc hcard hns
  exact ⟨R, z, c, hD_eq, hadm, hJ, hrows⟩

end CFSG.StandardType

end

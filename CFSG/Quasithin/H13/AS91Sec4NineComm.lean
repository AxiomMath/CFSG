module

public import CFSG.Quasithin.H13.AS91Sec4NineModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeXTransport
public import CFSG.Quasithin.H13.AS91Sec4EightLift
public import CFSG.Quasithin.H13.AS91Sec4EightTodd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Coc24
open CFSG.Monster.Code (AutPerm)
open CFSG.EvenSporadicStandard.TwoFi22 (O23In)
open scoped Pointwise commutatorElement

theorem le_O23In_of_pow_mem' {G : Type} [Group G] [Finite G] {C R V : Subgroup G} (hRC : R ≤ C)
    (hRn : ∀ r n, r ∈ R → n ∈ C → n * r * n⁻¹ ∈ R) (hR2 : IsPGroup 2 ↥R) (hVC : V ≤ C)
    (hVn : ∀ v n, v ∈ V → n ∈ C → n * v * n⁻¹ ∈ V) (hV : ∀ v ∈ V, ∃ k : ℕ, v ^ 3 ^ k ∈ R) :
    V ≤ O23In C := by
  have hRle : R.subgroupOf C ≤ CFSG.pCore 2 ↥C := by
    have hRn' : (R.subgroupOf C).Normal := (normal_subgroupOf_iff hRC).2 hRn
    have hR2' : IsPGroup 2 ↥(R.subgroupOf C) :=
      hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRC).symm
    exact CFSG.EvenSporadicStandard.TwoFi22.DS81.Glue.le_pCore_of_normal hRn' hR2'
  intro v hv
  refine ⟨⟨v, hVC hv⟩, mem_comap.2 ?_, rfl⟩
  have hnorm : (V.subgroupOf C).Normal := (normal_subgroupOf_iff hVC).2 hVn
  have hnorm' : ((V.subgroupOf C).map (QuotientGroup.mk' (CFSG.pCore 2 ↥C))).Normal :=
    hnorm.map _ (QuotientGroup.mk'_surjective _)
  have hp : IsPGroup 3 ((V.subgroupOf C).map (QuotientGroup.mk' (CFSG.pCore 2 ↥C))) := by
    rintro ⟨_, y, hy, rfl⟩
    obtain ⟨k, hk⟩ := hV y hy
    refine ⟨k, Subtype.ext ?_⟩
    change (QuotientGroup.mk' (CFSG.pCore 2 ↥C) y) ^ 3 ^ k = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hRle (mem_subgroupOf.2 (by simpa using hk))
  exact CFSG.EvenSporadicStandard.TwoFi22.DS81.Glue.le_pCore_of_normal hnorm' hp
    (mem_map_of_mem _ (mem_subgroupOf.2 hv))

theorem pow_three_mem_of_mem_sup {G : Type} [Group G] {R : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    (hxR : ∀ r ∈ R, x * r * x⁻¹ ∈ R) {v : G} (hv : v ∈ R ⊔ zpowers x) : v ^ 3 ∈ R := by
  have hxR' : ∀ (k : ℕ), ∀ r ∈ R, x ^ k * r * (x ^ k)⁻¹ ∈ R := by
    intro k
    induction k with
    | zero => intro r hr; simpa using hr
    | succ k ih =>
      intro r hr
      have e : x ^ (k + 1) * r * (x ^ (k + 1))⁻¹ = x ^ k * (x * r * x⁻¹) * (x ^ k)⁻¹ := by
        rw [pow_succ, mul_inv_rev]
        group
      rw [e]
      exact ih _ (hxR r hr)
  have hnorm : zpowers x ≤ normalizer (R : Set G) := by
    rw [zpowers_le]
    refine mem_normalizer_iff.2 fun r => ⟨fun hr => hxR r hr, fun hr => ?_⟩
    have h2 := hxR' 2 _ hr
    have e : x ^ 2 * (x * r * x⁻¹) * (x ^ 2)⁻¹ = r := by
      calc x ^ 2 * (x * r * x⁻¹) * (x ^ 2)⁻¹ = x ^ 3 * r * (x ^ 3)⁻¹ := by group
        _ = r := by rw [hx3]; group
    rwa [e] at h2
  have hmem : v ∈ (R : Set G) * (zpowers x : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hnorm]
    exact hv
  obtain ⟨r, hr, y, hy, rfl⟩ := Set.mem_mul.1 hmem
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  have hconj : ∀ j : ℤ, x ^ j * r * (x ^ j)⁻¹ ∈ R := fun j =>
    (mem_normalizer_iff.1 (hnorm (zpow_mem (mem_zpowers x) j)) r).1 hr
  have h3 : x ^ (3 * k) = 1 := by
    rw [zpow_mul, show x ^ (3 : ℤ) = 1 by exact_mod_cast hx3, one_zpow]
  have e : (r * x ^ k) ^ 3 = r * (x ^ k * r * (x ^ k)⁻¹) * (x ^ (2 * k) * r * (x ^ (2 * k))⁻¹) *
      x ^ (3 * k) := by
    rw [pow_three]
    group
  rw [e, h3, mul_one]
  exact mul_mem (mul_mem hr (hconj k)) (hconj (2 * k))

namespace Data41

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z} (D : Data41 h)

section Comm

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem c_mem_normalizer : (D.c : G) ∈ normalizer (D.E : Set G) :=
  D.G13_le_normalizer hOut hTw (D.c_mem_G13 hOut hTw hHat)

theorem map_Mz_eq (e : ↥D.E ≃* W11)
    (he : D.Mb.map (MulAut.congr e).toMonoidHom = img11 AutPerm) (hez : e D.zE = z0) :
    (D.Mz.map D.Mb.subtype).map (MulAut.congr e).toMonoidHom =
      img11 AutPerm ⊓ centSub (Subgroup.zpowers z0) := by
  ext τ
  constructor
  · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    refine ⟨he ▸ mem_map_of_mem _ φ.2, mem_centSub_zpowers.2 ?_⟩
    change e (φ.1 (e.symm z0)) = z0
    rw [← hez, MulEquiv.symm_apply_apply, (D.mem_Mz.1 hφ)]
  · rintro ⟨hτ, hτz⟩
    rw [← he] at hτ
    obtain ⟨φ, hφ, rfl⟩ := hτ
    refine ⟨φ, ⟨⟨φ, hφ⟩, ?_, rfl⟩, rfl⟩
    have h1 := mem_centSub_zpowers.1 hτz
    change e (φ (e.symm z0)) = z0 at h1
    rw [← hez, MulEquiv.symm_apply_apply] at h1
    exact D.mem_Mz.2 (e.injective h1)

theorem toMb_c_mem_O23In :
    ((D.toMb ⟨D.c, D.c_mem_normalizer hOut hTw hHat⟩ : ↥D.Mb) : MulAut ↥D.E) ∈
      O23In (D.Mz.map D.Mb.subtype) := by
  set cN : ↥(normalizer (D.E : Set G)) := ⟨D.c, D.c_mem_normalizer hOut hTw hHat⟩ with hcN
  set γ : MulAut ↥D.E := ((D.toMb cN : ↥D.Mb) : MulAut ↥D.E) with hγ
  set R : Subgroup (MulAut ↥D.E) := D.Qs.map D.Mb.subtype with hR
  have hQE_G13 : h.setting.QG ⊔ D.E ≤ D.G13 := by
    refine sup_le ?_ (D.E_le_G13 hOut hTw)
    rw [h.setting_QG]
    exact le_sup_left.trans (D.QX_le hOut hTw)
  have hmemMz : ∀ {m : G} (hm : m ∈ D.G13),
      ((D.toMb ⟨m, D.G13_le_normalizer hOut hTw hm⟩ : ↥D.Mb) : MulAut ↥D.E) ∈
        D.Mz.map D.Mb.subtype := fun hm =>
    ⟨_, (D.mem_Mz_iff hOut hTw).2 ⟨_, hm, rfl⟩, rfl⟩
  have hMz : ∀ {n : MulAut ↥D.E}, n ∈ D.Mz.map D.Mb.subtype →
      ∃ (m : G) (hm : m ∈ D.G13), ((D.toMb ⟨m, D.G13_le_normalizer hOut hTw hm⟩ : ↥D.Mb) :
        MulAut ↥D.E) = n := by
    rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨m, hm, hmφ⟩ := (D.mem_Mz_iff hOut hTw).1 hφ
    exact ⟨m, hm, congrArg Subtype.val hmφ⟩
  have hRC : R ≤ D.Mz.map D.Mb.subtype := by
    rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨q, hqN, hq, rfl⟩ := D.mem_img.1 hφ
    exact hmemMz (hQE_G13 hq)
  have hRn : ∀ r n, r ∈ R → n ∈ D.Mz.map D.Mb.subtype → n * r * n⁻¹ ∈ R := by
    rintro _ n ⟨φ, hφ, rfl⟩ hn
    obtain ⟨q, hqN, hq, rfl⟩ := D.mem_img.1 hφ
    obtain ⟨m, hm, rfl⟩ := hMz hn
    have hmq : m * q * m⁻¹ ∈ h.setting.QG ⊔ D.E := by
      have hmM := D.G13_le_M hm
      have hle : (h.setting.QG ⊔ D.E).map (MulAut.conj m).toMonoidHom ≤ h.setting.QG ⊔ D.E := by
        rw [Subgroup.map_sup]
        refine sup_le_sup ?_ ?_
        · rintro _ ⟨y, hy, rfl⟩
          exact h.setting.conj_mem_QG hmM hy
        · rintro _ ⟨y, hy, rfl⟩
          exact D.conj_mem_E hm hy
      exact hle ⟨q, hq, rfl⟩
    have hmqN : m * q * m⁻¹ ∈ normalizer (D.E : Set G) := D.QE_le_N hmq
    refine ⟨D.toMb ⟨m * q * m⁻¹, hmqN⟩, D.toMb_mem_img hmqN hmq, ?_⟩
    have e1 : D.toMb ⟨m * q * m⁻¹, hmqN⟩ = D.toMb ⟨m, D.G13_le_normalizer hOut hTw hm⟩ *
        D.toMb ⟨q, hqN⟩ * (D.toMb ⟨m, D.G13_le_normalizer hOut hTw hm⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1]
    rfl
  have hR2 : IsPGroup 2 ↥R := by
    have hc : Nat.card ↥R = 2 ^ 6 := by
      rw [hR, Subgroup.card_map_of_injective D.Mb.subtype_injective, D.card_Qs hOut hTw hHat]
      norm_num
    exact IsPGroup.of_card hc
  have hγMz : γ ∈ D.Mz.map D.Mb.subtype := hmemMz (D.c_mem_G13 hOut hTw hHat)
  have hγ3 : γ ^ 3 = 1 := by
    have e1 : D.toMb cN ^ 3 = 1 := by
      rw [← map_pow]
      have hc3 : (D.c : G) ^ 3 = 1 := by rw [← Subgroup.coe_pow, D.c_pow, Subgroup.coe_one]
      have : cN ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow]
        exact hc3)
      rw [this, map_one]
    rw [hγ, ← Subgroup.coe_pow, e1]
    rfl
  have hγR : ∀ r ∈ R, γ * r * γ⁻¹ ∈ R := fun r hr => hRn r γ hr hγMz
  have hVC : R ⊔ zpowers γ ≤ D.Mz.map D.Mb.subtype := sup_le hRC (zpowers_le.2 hγMz)
  have hVn : ∀ v n, v ∈ R ⊔ zpowers γ → n ∈ D.Mz.map D.Mb.subtype →
      n * v * n⁻¹ ∈ R ⊔ zpowers γ := by
    intro v n hv hn
    have hle : (R ⊔ zpowers γ).map (MulAut.conj n).toMonoidHom ≤ R ⊔ zpowers γ := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact mem_sup_left (hRn y n hy hn)
      · rw [MonoidHom.map_zpowers, zpowers_le]
        obtain ⟨m, hm, rfl⟩ := hMz hn
        have hmM := D.G13_le_M hm
        have hmH : m ∈ H z := by
          rw [← h.setting_z]
          exact mem_centralizer_singleton_iff.2 ((h.setting.mem_M_iff).1 hmM)
        have hmc : m * D.c * m⁻¹ ∈ Q z ⊔ zpowers (D.c : G) :=
          (D.toLoc41 hHat).QX_normal m hmH _ (le_sup_right (a := Q z) (mem_zpowers _))
        have hnormQ : zpowers (D.c : G) ≤ normalizer ((Q z : Subgroup G) : Set G) := by
          rw [zpowers_le, ← h.setting_QG]
          exact mem_normalizer_fintype fun q hq => h.setting.conj_mem_QG D.c.2 hq
        have hmem : m * D.c * m⁻¹ ∈ ((Q z : Subgroup G) : Set G) * (zpowers (D.c : G) : Set G) := by
          rw [← coe_mul_of_right_le_normalizer_left _ _ hnormQ]
          exact hmc
        obtain ⟨q, hq, y, hy, hqy⟩ := Set.mem_mul.1 hmem
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
        have hqG : q ∈ h.setting.QG := by rw [h.setting_QG]; exact hq
        have hqN : q ∈ normalizer (D.E : Set G) := D.QG_le_N hqG
        have hck : (D.c : G) ^ k ∈ normalizer (D.E : Set G) :=
          zpow_mem (D.c_mem_normalizer hOut hTw hHat) k
        have e1 : (D.toMb ⟨m, D.G13_le_normalizer hOut hTw hm⟩ : ↥D.Mb) * D.toMb cN *
            (D.toMb ⟨m, D.G13_le_normalizer hOut hTw hm⟩)⁻¹ =
            D.toMb ⟨q, hqN⟩ * D.toMb cN ^ k := by
          rw [← map_zpow, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
          congr 1
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_zpow]
          exact hqy.symm
        change ((D.toMb ⟨m, D.G13_le_normalizer hOut hTw hm⟩ : ↥D.Mb) : MulAut ↥D.E) * γ *
          ((D.toMb ⟨m, D.G13_le_normalizer hOut hTw hm⟩ : ↥D.Mb) : MulAut ↥D.E)⁻¹ ∈ _
        rw [hγ, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, e1, Subgroup.coe_mul,
          Subgroup.coe_zpow]
        refine mul_mem (mem_sup_left ⟨D.toMb ⟨q, hqN⟩, ?_, rfl⟩)
          (mem_sup_right (zpow_mem (mem_zpowers _) k))
        exact D.toMb_mem_img hqN (mem_sup_left hqG)
    exact hle ⟨v, hv, rfl⟩
  have hV : ∀ v ∈ R ⊔ zpowers γ, ∃ k : ℕ, v ^ 3 ^ k ∈ R := fun v hv =>
    ⟨1, by rw [pow_one]; exact pow_three_mem_of_mem_sup hγ3 hγR hv⟩
  exact le_O23In_of_pow_mem' hRC hRn hR2 hVC hVn hV (mem_sup_right (mem_zpowers γ))

theorem exists_todd_std (hM : CFSG.CGT.T75P.M24SylowInput)
    (hJ : MathieuSmallIrr24) :
    ∃ e : ↥D.E ≃* W11, D.Mb.map (MulAut.congr e).toMonoidHom = img11 AutPerm ∧ e D.zE = z0 := by
  letI : CommGroup ↥D.E := commGroupOfElem (D.isElemAbelian_E hHat hOut hTw)
  obtain ⟨e₁, he₁⟩ := cocode24_std (D.mathieuCocode24_E hOut hTw hHat hM hJ)
  have he₁' : D.Mb.map (H.congrHom e₁) = img11 AutPerm := by
    rw [img11, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
    exact he₁
  have hz1 : D.zE ≠ 1 := fun h1 => h.setting.z_ne_one (by
    rw [h.setting_z]
    exact congrArg Subtype.val h1)
  exact Nine.exists_equiv_std he₁' hz1 (D.card_orbit_zE hOut hTw hHat hM)

theorem toMb_c_pow_three :
    D.toMb ⟨D.c, D.c_mem_normalizer hOut hTw hHat⟩ ^ 3 = 1 := by
  have hc3 : (D.c : G) ^ 3 = 1 := by rw [← Subgroup.coe_pow, D.c_pow, Subgroup.coe_one]
  rw [← map_pow]
  have : (⟨D.c, D.c_mem_normalizer hOut hTw hHat⟩ : ↥(normalizer (D.E : Set G))) ^ 3 = 1 :=
    Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hc3)
  rw [this, map_one]

theorem toMb_c_ne_one : D.toMb ⟨D.c, D.c_mem_normalizer hOut hTw hHat⟩ ≠ 1 := by
  intro h1
  have hcE : (D.c : G) ∈ D.E := (D.toMb_eq_one_iff hOut hTw hHat _).1 h1
  have hc2 := D.E_sq hHat hOut hTw hcE
  have hc3 : (D.c : G) ^ 3 = 1 := by rw [← Subgroup.coe_pow, D.c_pow, Subgroup.coe_one]
  apply D.c_ne
  calc (D.c : G) = (D.c : G) ^ 3 * ((D.c : G) * (D.c : G))⁻¹ := by group
    _ = 1 := by rw [hc3, hc2]; group

theorem mem_H_of_mem_E {y : G} (hy : y ∈ D.E) : y ∈ H z := by
  have hyM := D.E_le_M hy
  rw [← h.setting_z]
  exact mem_centralizer_singleton_iff.2 ((h.setting.mem_M_iff).1 hyM)

theorem exists_lift (e : ↥D.E ≃* W11)
    (he : D.Mb.map (MulAut.congr e).toMonoidHom = img11 AutPerm) (hez : e D.zE = z0)
    {τ : MulAut W11} (hτ : τ ∈ img11 AutPerm)
    (hcomm : τ * (MulAut.congr e) ((D.toMb ⟨D.c, D.c_mem_normalizer hOut hTw hHat⟩ : ↥D.Mb) :
      MulAut ↥D.E) = (MulAut.congr e) ((D.toMb ⟨D.c, D.c_mem_normalizer hOut hTw hHat⟩ :
      ↥D.Mb) : MulAut ↥D.E) * τ)
    (hτz : τ z0 = z0) :
    ∃ g ∈ H z ⊓ centralizer (zpowers (D.c : G) : Set G),
      ∀ y : ↥D.E, g * y * g⁻¹ = (e.symm (τ (e y)) : G) := by
  set cN : ↥(normalizer (D.E : Set G)) := ⟨D.c, D.c_mem_normalizer hOut hTw hHat⟩ with hcN
  rw [← he] at hτ
  obtain ⟨φ, hφ, rfl⟩ := hτ
  obtain ⟨mN, rfl⟩ := hφ
  set m : G := (mN : G) with hm
  have hact : ∀ y : ↥D.E, m * y * m⁻¹ = (e.symm ((MulAut.congr e) (conjNormalizer D.E mN)
      (e y)) : G) := by
    intro y
    change m * y * m⁻¹ = (e.symm (e (conjNormalizer D.E mN (e.symm (e y)))) : G)
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    rfl
  have hcomm' : conjNormalizer D.E mN * conjNormalizer D.E cN =
      conjNormalizer D.E cN * conjNormalizer D.E mN := by
    apply (MulAut.congr e).injective
    rw [map_mul, map_mul]
    exact hcomm
  have hcE : (D.c : G) ∈ D.G13 := D.c_mem_G13 hOut hTw hHat
  have ha1 : D.toMb (mN * cN * mN⁻¹ * cN⁻¹) = 1 := by
    apply Subtype.ext
    change conjNormalizer D.E (mN * cN * mN⁻¹ * cN⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm']
    group
  have haE : m * D.c * m⁻¹ * (D.c : G)⁻¹ ∈ D.E := (D.toMb_eq_one_iff hOut hTw hHat _).1 ha1
  set a : G := m * D.c * m⁻¹ * (D.c : G)⁻¹ with ha
  set b : G := D.c * a * (D.c : G)⁻¹ with hb
  set d : G := D.c * b * (D.c : G)⁻¹ with hd
  have hbE : b ∈ D.E := D.conj_mem_E hcE haE
  have hdE : d ∈ D.E := D.conj_mem_E hcE hbE
  have hc3 : (D.c : G) ^ 3 = 1 := by rw [← Subgroup.coe_pow, D.c_pow, Subgroup.coe_one]
  have habd : a * b * d = 1 := by
    have h1 : (a * D.c) ^ 3 = 1 := by
      have e1 : a * D.c = m * D.c * m⁻¹ := by rw [ha]; group
      rw [e1, conj_pow, hc3, mul_one, mul_inv_cancel]
    have e2 : (a * D.c) ^ 3 = a * b * d * (D.c : G) ^ 3 := by
      rw [hd, hb, pow_three, pow_three]
      group
    rw [e2, hc3, mul_one] at h1
    exact h1
  have hcom : ∀ {x y : G}, x ∈ D.E → y ∈ D.E → x * y = y * x := fun hx hy =>
    D.E_comm hOut hTw hHat hx hy
  have hsq : ∀ {x : G}, x ∈ D.E → x * x = 1 := fun hx => D.E_sq hHat hOut hTw hx
  have hd' : d = a * b := by
    have h1 : d = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right habd
    rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq hbE),
      inv_eq_of_mul_eq_one_right (hsq haE), hcom hbE haE]
  have hmN : m ∈ normalizer (D.E : Set G) := mN.2
  have hgc : b * m * D.c = D.c * (b * m) := by
    have e1 : b * m * D.c = b * a * D.c * m := by rw [ha]; group
    have e2 : D.c * (b * m) = d * D.c * m := by rw [hd]; group
    rw [e1, e2, hd', hcom hbE haE]
  have hmE : ∀ y : ↥D.E, m * y * m⁻¹ ∈ D.E := fun y =>
    (mem_normalizer_iff.1 hmN y).1 y.2
  have hgy : ∀ y : ↥D.E, b * m * y * (b * m)⁻¹ = m * y * m⁻¹ := by
    intro y
    calc b * m * y * (b * m)⁻¹ = b * (m * y * m⁻¹) * b⁻¹ := by group
      _ = m * y * m⁻¹ * b * b⁻¹ := by rw [hcom hbE (hmE y)]
      _ = m * y * m⁻¹ := by group
  refine ⟨b * m, Subgroup.mem_inf.2 ⟨?_, ?_⟩, fun y => (hgy y).trans (hact y)⟩
  ·
    have h3 : m * (D.zE : G) * m⁻¹ = (D.zE : G) := congrArg Subtype.val
      (show (D.toMb mN : MulAut ↥D.E) D.zE = D.zE from by
        have h4 : ((MulAut.congr e) (conjNormalizer D.E mN)) z0 = z0 := hτz
        change e (conjNormalizer D.E mN (e.symm z0)) = z0 at h4
        rw [← hez, MulEquiv.symm_apply_apply] at h4
        exact e.injective h4)
    have h2 : b * m * z * (b * m)⁻¹ = z := (hgy D.zE).trans h3
    refine mem_centralizer_singleton_iff.2 ?_
    calc b * m * z = b * m * z * (b * m)⁻¹ * (b * m) := by group
      _ = z * (b * m) := by rw [h2]
  ·
    rw [mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact ((Commute.zpow_left (show Commute (D.c : G) (b * m) from hgc.symm) k)).eq

theorem z_mem_commutator
    (hM : CFSG.CGT.T75P.M24SylowInput) (hJ : MathieuSmallIrr24) :
    z ∈ ⁅H z ⊓ centralizer (zpowers (D.c : G) : Set G),
      H z ⊓ centralizer (zpowers (D.c : G) : Set G)⁆ := by
  obtain ⟨e, he, hez⟩ := D.exists_todd_std hOut hTw hHat hM hJ
  set σ : MulAut W11 := (MulAut.congr e) ((D.toMb ⟨D.c, D.c_mem_normalizer hOut hTw hHat⟩ :
    ↥D.Mb) : MulAut ↥D.E) with hσ
  have hσO : σ ∈ O23In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0)) := by
    rw [← D.map_Mz_eq hOut hTw hHat e he hez,
      CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.O23In_map_of_injective _
        (MulAut.congr e).injective]
    exact mem_map_of_mem _ (D.toMb_c_mem_O23In hOut hTw hHat)
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow, ← Subgroup.coe_pow, D.toMb_c_pow_three hOut hTw hHat, Subgroup.coe_one,
      map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply D.toMb_c_ne_one hOut hTw hHat
    apply Subtype.ext
    apply (MulAut.congr e).injective
    rw [Subgroup.coe_one, map_one]
    exact h1
  obtain ⟨τ₁, hτ₁, τ₂, hτ₂, v₁, v₂, hc1, hc2, hz1, hz2, hv1, hv2, hprod⟩ :=
    Nine.exists_comm_witness hσO hσ3 hσ1
  obtain ⟨g₁, hg₁C, hg₁⟩ := D.exists_lift hOut hTw hHat e he hez hτ₁ hc1 hz1
  obtain ⟨g₂, hg₂C, hg₂⟩ := D.exists_lift hOut hTw hHat e he hez hτ₂ hc2 hz2
  have hy : ∀ v : W11, σ v = v →
      ((e.symm v : ↥D.E) : G) ∈ H z ⊓ centralizer (zpowers (D.c : G) : Set G) := by
    intro v hv
    refine Subgroup.mem_inf.2 ⟨D.mem_H_of_mem_E hOut hTw hHat (e.symm v).2, ?_⟩
    have h1 : ((D.toMb ⟨D.c, D.c_mem_normalizer hOut hTw hHat⟩ : ↥D.Mb) : MulAut ↥D.E)
        (e.symm v) = e.symm v := by
      have h2 : e (((D.toMb ⟨D.c, D.c_mem_normalizer hOut hTw hHat⟩ : ↥D.Mb) : MulAut ↥D.E)
          (e.symm v)) = v := hv
      exact e.injective (h2.trans (MulEquiv.apply_symm_apply e v).symm)
    have h3 : (D.c : G) * (e.symm v : G) * (D.c : G)⁻¹ = (e.symm v : G) :=
      congrArg Subtype.val h1
    have hcomm : Commute (D.c : G) (e.symm v : G) := by
      show (D.c : G) * (e.symm v : G) = (e.symm v : G) * D.c
      calc (D.c : G) * (e.symm v : G) = (D.c : G) * (e.symm v : G) * (D.c : G)⁻¹ * D.c := by
            group
        _ = (e.symm v : G) * D.c := by rw [h3]
    rw [mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (Commute.zpow_left hcomm k).eq
  have hval : ∀ (g : G) (τ : MulAut W11) (v : W11),
      (∀ y : ↥D.E, g * y * g⁻¹ = (e.symm (τ (e y)) : G)) →
      ⁅g, ((e.symm v : ↥D.E) : G)⁆ = ((e.symm (τ v * v⁻¹) : ↥D.E) : G) := by
    intro g τ v hg
    rw [commutatorElement_def, hg, MulEquiv.apply_symm_apply, map_mul, map_inv, Subgroup.coe_mul,
      Subgroup.coe_inv]
  have key : ⁅g₁, ((e.symm v₁ : ↥D.E) : G)⁆ * ⁅g₂, ((e.symm v₂ : ↥D.E) : G)⁆ = z := by
    rw [hval g₁ τ₁ v₁ hg₁, hval g₂ τ₂ v₂ hg₂, ← Subgroup.coe_mul, ← map_mul, hprod, ← hez,
      MulEquiv.symm_apply_apply]
    rfl
  have hmem := mul_mem (commutator_mem_commutator hg₁C (hy v₁ hv1))
    (commutator_mem_commutator hg₂C (hy v₂ hv2))
  rwa [key] at hmem

end Comm

end Data41

end CFSG.Quasithin.H13.AS91

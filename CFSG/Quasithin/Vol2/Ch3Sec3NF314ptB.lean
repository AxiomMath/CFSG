module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptAssembly
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptBCoord
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314L

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ins314

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.CZL32
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open CFSG.Quasithin.H13.L3319
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G} {t : G}

namespace Sett

variable (e : Sett T M L t)
include e

theorem V1_le_normalizer_V2 [IsMulCommutative ↥(vPlus L T)] :
    ⁅vPlus L T, L⁆ ≤ Subgroup.normalizer ((⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G) : Set G) := by
  have hV1V : ⁅vPlus L T, L⁆ ≤ vPlus L T :=
    commutator_le_of_le_normalizer (le_sup_left.trans e.hX)
  have hV2V : ⁅vPlus L T, CFSG.conjugate L t⁆ ≤ vPlus L T :=
    commutator_le_of_le_normalizer (fun x hx => e.hX (e.L2_le hx))
  have hVcomm : ∀ a ∈ vPlus L T, ∀ b ∈ vPlus L T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((inferInstance : IsMulCommutative ↥(vPlus L T)).is_comm.comm
      (⟨a, ha⟩ : ↥(vPlus L T)) ⟨b, hb⟩)
  intro x hx
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (hVcomm x (hV1V hx) y (hV2V hy)).symm

theorem mPlus_le_normalizer_V2 :
    mPlus L T ≤ Subgroup.normalizer (⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G) := by
  rw [e.hM]
  exact sup_le (fun x hx => e.L_le_N_V2 hx) (fun x hx => e.L2_le_N_V2 hx)

theorem exists_fixed_V1 [IsMulCommutative ↥(vPlus L T)]
    (hVs : vPlus L T = ⁅vPlus L T, L⁆ ⊔ ⁅vPlus L T, CFSG.conjugate L t⁆)
    (hI : ⁅vPlus L T, L⁆ ⊓ ⁅vPlus L T, CFSG.conjugate L t⁆ = ⊥)
    {Y : Subgroup G} (hYM : Y ≤ mPlus L T) (htY : t ∈ Subgroup.normalizer (Y : Set G))
    (hfix : vPlus L T ⊓ Subgroup.centralizer (Y : Set G) ≠ ⊥) :
    ∃ u ∈ ⁅vPlus L T, L⁆, u ≠ 1 ∧ ∀ y ∈ Y, y * u = u * y := by
  have hV1V : ⁅vPlus L T, L⁆ ≤ vPlus L T :=
    commutator_le_of_le_normalizer (le_sup_left.trans e.hX)
  have hV2V : ⁅vPlus L T, CFSG.conjugate L t⁆ ≤ vPlus L T :=
    commutator_le_of_le_normalizer (fun x hx => e.hX (e.L2_le hx))
  have hN := e.V1_le_normalizer_V2
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hfix
  have hxV : (x : G) ∈ vPlus L T := x.2.1
  have hxC : ∀ y ∈ Y, y * (x : G) = (x : G) * y := fun y hy =>
    Subgroup.mem_centralizer_iff.mp x.2.2 y hy
  have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxmem : (x : G) ∈ ((⁅vPlus L T, L⁆ ⊔ ⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G) : Set G) := by
    rw [← hVs]
    exact hxV
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hxmem
  obtain ⟨v₁, hv₁, v₂, hv₂, hxv0⟩ := hxmem
  have hxv : v₁ * v₂ = (x : G) := hxv0
  have hfixv : ∀ y ∈ Y, y * v₁ * y⁻¹ = v₁ ∧ y * v₂ * y⁻¹ = v₂ := by
    intro y hy
    have hy1 : y ∈ Subgroup.normalizer (⁅vPlus L T, L⁆ : Subgroup G) :=
      NF314pt.mPlus_le_normalizer_V1 e (hYM hy)
    have hy2 : y ∈ Subgroup.normalizer (⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G) :=
      e.mPlus_le_normalizer_V2 (hYM hy)
    set a := y * v₁ * y⁻¹ with ha
    set b := y * v₂ * y⁻¹ with hb
    have haV1 : a ∈ ⁅vPlus L T, L⁆ := (Subgroup.mem_normalizer_iff.mp hy1 v₁).mp hv₁
    have hbV2 : b ∈ ⁅vPlus L T, CFSG.conjugate L t⁆ := (Subgroup.mem_normalizer_iff.mp hy2 v₂).mp hv₂
    have hab : a * b = v₁ * v₂ := by
      have h1 : y * (v₁ * v₂) * y⁻¹ = a * b := by rw [ha, hb]; group
      have h2 : y * (v₁ * v₂) * y⁻¹ = v₁ * v₂ := by
        rw [hxv]
        exact mul_inv_eq_iff_eq_mul.mpr (hxC y hy)
      rw [← h1, h2]
    have h3 : v₁⁻¹ * a = v₂ * b⁻¹ := by
      calc v₁⁻¹ * a = v₁⁻¹ * (a * b) * b⁻¹ := by group
        _ = v₂ * b⁻¹ := by rw [hab]; group
    have h4 : v₁⁻¹ * a ∈ (⊥ : Subgroup G) := hI ▸ ⟨(⁅vPlus L T, L⁆).mul_mem
      ((⁅vPlus L T, L⁆).inv_mem hv₁) haV1, h3 ▸ (⁅vPlus L T, CFSG.conjugate L t⁆).mul_mem hv₂
      ((⁅vPlus L T, CFSG.conjugate L t⁆).inv_mem hbV2)⟩
    rw [Subgroup.mem_bot, inv_mul_eq_one] at h4
    refine ⟨h4.symm, ?_⟩
    have h5 : v₂ * b⁻¹ = 1 := by rw [← h3, h4.symm]; group
    rw [mul_inv_eq_one] at h5
    exact h5.symm
  by_cases hv1 : v₁ = 1
  ·
    have hv2 : v₂ ≠ 1 := by
      intro h2
      apply hx1'
      rw [← hxv, hv1, h2, one_mul]
    obtain ⟨hs1, hs2⟩ := e.swap_V e.ht e.htn
    have hu : t * v₂ * t⁻¹ ∈ ⁅vPlus L T, L⁆ := by
      have h3 : (MulAut.conj t).toMonoidHom v₂ ∈
          (⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hv₂
      rw [hs2] at h3
      simpa using h3
    refine ⟨t * v₂ * t⁻¹, hu, ?_, ?_⟩
    · intro h
      apply hv2
      have : v₂ = t⁻¹ * (t * v₂ * t⁻¹) * t := by group
      rw [this, h]
      group
    · intro y hy
      have hy' : t⁻¹ * y * t ∈ Y := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htY) y).mp hy
        simpa using this
      have h1 := (hfixv _ hy').2
      have h2 : y * (t * v₂ * t⁻¹) * y⁻¹ = t * v₂ * t⁻¹ := by
        calc y * (t * v₂ * t⁻¹) * y⁻¹
            = t * ((t⁻¹ * y * t) * v₂ * (t⁻¹ * y * t)⁻¹) * t⁻¹ := by group
          _ = t * v₂ * t⁻¹ := by rw [h1]
      exact mul_inv_eq_iff_eq_mul.mp h2
  · exact ⟨v₁, hv₁, hv1, fun y hy => mul_inv_eq_iff_eq_mul.mp (hfixv y hy).1⟩

theorem V1_le_commutator [IsMulCommutative ↥(vPlus L T)]
    {k : ℕ} (c₀ : Coord (autOn L (vPlus L T)) (tildeComm L T L) (cvPlus L T) k)
    (hcv : cvPlus L T = ⊥)
    (hVs : vPlus L T = ⁅vPlus L T, L⁆ ⊔ ⁅vPlus L T, CFSG.conjugate L t⁆)
    (hI : ⁅vPlus L T, L⁆ ⊓ ⁅vPlus L T, CFSG.conjugate L t⁆ = ⊥)
    {Y : Subgroup G} (hYX : Y ≤ L ⊔ T) (hYM : Y ≤ mPlus L T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    {y : G} (hyY : y ∈ Y) (hy3 : y ^ 3 = 1)
    (hy2 : y ∈ Subgroup.centralizer ((⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G) : Set G))
    (hy1 : y ∉ Subgroup.centralizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G))
    {u : G} (hu : u ∈ ⁅vPlus L T, L⁆) (hu1 : u ≠ 1) (huY : ∀ y ∈ Y, y * u = u * y) :
    ⁅vPlus L T, L⁆ ≤ ⁅vPlus L T, Y⁆ := by
  obtain ⟨c, hcS⟩ := c₀.exists_imgSub_bSub Sett.autOn_inf_le e.card_autOn_inf
  set V := vPlus L T with hV
  set ρ := conjOf V (L ⊔ T) e.hX with hρ
  have hV1V : ⁅V, L⁆ ≤ V := commutator_le_of_le_normalizer (le_sup_left.trans e.hX)
  have huV : u ∈ V := hV1V hu
  have hyX : y ∈ L ⊔ T := hYX hyY
  have hyM' : y ∈ ((mPlus L T : Subgroup G) : Set G) := hYM hyY
  rw [e.coe_mPlus] at hyM'
  obtain ⟨l₂, hl₂, l, hl, hyll⟩ := hyM'
  have hl₂X : l₂ ∈ L ⊔ T := e.L2_le hl₂
  have hlX : l ∈ L ⊔ T := Subgroup.mem_sup_left hl
  have hVC : V ≤ Subgroup.centralizer ({l₂} : Set G) := by
    rw [hVs]
    refine sup_le (fun v hv => ?_) (fun v hv => ?_)
    · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff.mp hh]
      exact e.L2_centralizes_V1 hI hl₂ hv
    · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff.mp hh]
      have h1 := Subgroup.mem_centralizer_iff.mp hy2 v hv
      have h2 := e.L_centralizes_V2 hI hl hv
      rw [← hyll] at h1
      calc l₂ * v = l₂ * (l * v * l⁻¹) := by rw [h2]; group
        _ = (l₂ * l * v) * l⁻¹ := by group
        _ = (v * (l₂ * l)) * l⁻¹ := by rw [h1]
        _ = v * l₂ := by group
  have hl₂C : l₂ ∈ Subgroup.centralizer (V : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hVC hv) l₂ (Set.mem_singleton _)).symm
  have hρl₂ : ρ ⟨l₂, hl₂X⟩ = 1 := (conjOf_eq_one_iff e.hX ⟨l₂, hl₂X⟩).mpr hl₂C
  have hρy : ρ ⟨y, hyX⟩ ∈ autOn L V := by
    have h1 : (⟨y, hyX⟩ : ↥(L ⊔ T)) = ⟨l₂, hl₂X⟩ * ⟨l, hlX⟩ := Subtype.ext hyll.symm
    rw [h1, map_mul, hρl₂, one_mul]
    exact conjOf_mem_autOn e.hX hl
  obtain ⟨γ, hγ⟩ := c.exists_img hρy
  have hγ3 : γ ^ 3 = 1 := by
    apply c.π.injective
    have h1 : c.π γ = ⟨ρ ⟨y, hyX⟩, hρy⟩ := Subtype.ext hγ
    rw [map_pow, h1, map_one]
    apply Subtype.ext
    have h2 : (⟨y, hyX⟩ : ↥(L ⊔ T)) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    have h3 : ρ ⟨y, hyX⟩ ^ 3 = 1 := by rw [← map_pow, h2, map_one]
    simpa using h3
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    have h1 : ρ ⟨y, hyX⟩ = 1 := by rw [← hγ, c.img_one]
    have hyC := (conjOf_eq_one_iff e.hX ⟨y, hyX⟩).mp h1
    apply hy1
    exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_iff.mp hyC v (hV1V hv)
  have himg : ∀ b ∈ bSub, ∃ y' ∈ Y, ∃ hy'X : y' ∈ L ⊔ T,
      c.img (b * γ * b⁻¹) = ρ ⟨y', hy'X⟩ := by
    intro b hb
    have h1 : c.img b ∈ c.imgSub bSub := (c.mem_imgSub).mpr ⟨b, hb, rfl⟩
    rw [hcS] at h1
    obtain ⟨x, hx, hxρ⟩ := exists_conjOf_eq e.hX (inf_le_right.trans le_sup_left) h1
    have hxT : (x : G) ∈ T := hx.1
    refine ⟨x * y * x⁻¹, (Subgroup.mem_normalizer_iff.mp (hTY hxT) y).mp hyY,
      (L ⊔ T).mul_mem ((L ⊔ T).mul_mem x.2 hyX) ((L ⊔ T).inv_mem x.2), ?_⟩
    rw [c.img_conj, ← hxρ, hγ, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have huU : (⟨u, huV⟩ : ↥V) ∈ tildeComm L T L :=
    Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hu)
  have hfix : ∀ b ∈ bSub, c.img (b * γ * b⁻¹) ⟨u, huV⟩ = ⟨u, huV⟩ := by
    intro b hb
    obtain ⟨y', hy'Y, hy'X, him⟩ := himg b hb
    rw [him]
    apply Subtype.ext
    rw [conjOf_coe]
    exact mul_inv_eq_iff_eq_mul.mpr (huY y' hy'Y)
  have hW : ∀ b ∈ bSub, ∀ u' ∈ tildeComm L T L,
      u' * c.img (b * γ * b⁻¹) u'⁻¹ ∈ (⁅V, Y⁆).subgroupOf V := by
    intro b hb u' _
    obtain ⟨y', hy'Y, hy'X, him⟩ := himg b hb
    rw [him, Subgroup.mem_subgroupOf]
    have h1 : ((u' * (ρ ⟨y', hy'X⟩) u'⁻¹ : ↥V) : G) = ⁅(u' : G), y'⁆ := by
      have h2 : (((ρ ⟨y', hy'X⟩) u'⁻¹ : ↥V) : G) = y' * (u' : G)⁻¹ * y'⁻¹ :=
        conjOf_coe e.hX ⟨y', hy'X⟩ u'⁻¹
      rw [Subgroup.coe_mul, h2, commutatorElement_def]
      group
    rw [h1]
    exact Subgroup.commutator_mem_commutator u'.2 hy'Y
  have hle := c.le_of_commutators hcv hγ3 hγ1 huU (fun h => hu1 (congrArg Subtype.val h)) hfix hW
  intro v hv
  have hvV : v ∈ V := hV1V hv
  have hvU : (⟨v, hvV⟩ : ↥V) ∈ tildeComm L T L :=
    Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hv)
  exact Subgroup.mem_subgroupOf.mp (hle hvU)

end Sett

end CFSG.Quasithin.H13.Ins314

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.CZL32 CFSG.Quasithin.H13.Ins314
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open CFSG.Quasithin.H13.L3319
open scoped IsMulCommutative commutatorElement

theorem leafVY_of
    (h36 : A36ForSQTK) (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (lC : LeafYsplit) :
    LeafVY := by
  intro G _ _ T M L D H K cfg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have c : NFConfig G T M L D H K := cfg.nf
  have h := c.hyp
  obtain ⟨⟨hTL, hcomm, hcase, hPSL⟩, hfix⟩ := cfg.site
  obtain ⟨t, ht, htn, hM, hcommA, hbot, -, htc, htcI, hmod⟩ := hcase
  have hcard : Nat.card ↥(autOn L (vPlus L T)) = 168 := by
    obtain ⟨e⟩ := nonempty_equiv_of_isPSL hPSL
    rw [Nat.card_congr e.toEquiv, card_L3Γ]
  have sett : Sett T M L t := ⟨h.toSetup331, ht, htn, hM, hcommA, hbot, h37, h38, hcard⟩
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hV2 : ∀ x ∈ vPlus L T, x ^ 2 = 1 := hred.2.1.2
  have hTsylLT : IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right
  have hTH : T ≤ H := c.inH.1
  have hVO : vPlus L T ≤ pCoreOf 2 (L ⊔ T) := hred.1.trans inf_le_left
  have hVT : vPlus L T ≤ T := hVO.trans (pCoreOf_le_of_isSylowTwoOf hTsylLT)
  have hC0 := c.inf_centralizer_mPlus_eq_bot h36 h5 h128 h37 h38 h39
  have h74 : vPlus L T = ⁅vPlus L T, mPlus L T⁆ := by
    have := (h7 G T M L D h).2.2.2.2
    rwa [hC0, sup_bot_eq] at this
  have hCV := inf_centralizer_mPlus_vPlus_eq_bot h.sylow.1 hVT hV2 hC0
  have hI := sett.V1_inf_V2 htcI hCV
  have hVs := sett.V_eq_sup h74
  have hcv : cvPlus L T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ Subgroup.centralizer (mPlus L T : Set G) ⊓ vPlus L T := ⟨hx, x.2⟩
    rw [hCV] at hx'
    exact Subtype.ext (Subgroup.mem_bot.mp hx')
  have hYH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hYX : oTwoUpper H ≤ L ⊔ T := hYH.trans c.HLT
  have hYM : oTwoUpper H ≤ mPlus L T := oTwoUpper_le_mPlus sett c.HLT
  have hTY : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := fun x hx =>
    le_normalizer_oTwoUpper H (hTH hx)
  have hfixV : vPlus L T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) ≠ ⊥ := by
    rw [h74]
    exact hfix
  obtain ⟨u, hu, hu1, huY⟩ := sett.exists_fixed_V1 hVs hI hYM (hTY ht) hfixV
  obtain ⟨y, hyY, -, hy3, hy2, hy1⟩ := lC G T M L D H K cfg t ht htn
  obtain ⟨k, -, ⟨c₀⟩⟩ := exists_coord hPSL hmod
  have hV1 : ⁅vPlus L T, L⁆ ≤ ⁅vPlus L T, oTwoUpper H⁆ :=
    sett.V1_le_commutator c₀ hcv hVs hI hYX hYM hTY hyY hy3 hy2 hy1 hu hu1 huY
  have htN : t ∈ Subgroup.normalizer (⁅vPlus L T, oTwoUpper H⁆ : Subgroup G) :=
    Ins314.mem_normalizer_commutator (sett.T_le_normalizer_V ht) (hTY ht)
  have hV2le : ⁅vPlus L T, CFSG.conjugate L t⁆ ≤ ⁅vPlus L T, oTwoUpper H⁆ := by
    intro v hv
    obtain ⟨-, hs2⟩ := sett.swap_V ht htn
    have h3 : (MulAut.conj t).toMonoidHom v ∈
        (⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hv
    rw [hs2] at h3
    have h4 : t * v * t⁻¹ ∈ ⁅vPlus L T, oTwoUpper H⁆ := hV1 (by simpa using h3)
    have h5 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) _).mp h4
    simpa [mul_assoc] using h5
  exact le_antisymm (hVs.le.trans (sup_le hV1 hV2le))
    (commutator_le_of_le_normalizer (hYX.trans sett.hX))

end CFSG.Quasithin.H13.NF314pt

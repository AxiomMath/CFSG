module

public import CFSG.Quasithin.Vol2.Ch12Sec1Thm
public import CFSG.Quasithin.Vol2.Ch12Sec1Cent
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem24
public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL specialLinearGroupEquivStatedSL_coe)
open scoped IsMulCommutative commutatorElement Matrix

namespace Sec121Q

theorem det_updateCol_one {n : ℕ} (i : Fin n) (x : Fin n → ZMod 2) :
    ((1 : Matrix (Fin n) (Fin n) (ZMod 2)).updateCol i x).det = x i := by
  have h := Matrix.det_updateCol_sum (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i x
  have hx : (fun k => ∑ j, x j • (1 : Matrix (Fin n) (Fin n) (ZMod 2)) k j) = x := by
    funext k
    simp [Matrix.one_apply]
  rw [hx, Matrix.det_one, smul_eq_mul, mul_one] at h
  exact h

theorem exists_sl_mulVec_eq_of_coord {n : ℕ} {x y : Fin n → ZMod 2} {i : Fin n} (hx : x i = 1)
    (hy : y i = 1) :
    ∃ A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2), (A : Matrix _ _ _) *ᵥ x = y := by
  set Bx : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
    ⟨(1 : Matrix (Fin n) (Fin n) (ZMod 2)).updateCol i x, by rw [det_updateCol_one, hx]⟩
  set By : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
    ⟨(1 : Matrix (Fin n) (Fin n) (ZMod 2)).updateCol i y, by rw [det_updateCol_one, hy]⟩
  have hBe : ∀ (v : Fin n → ZMod 2), ((1 : Matrix (Fin n) (Fin n) (ZMod 2)).updateCol i v) *ᵥ
      Pi.single i 1 = v := by
    intro v
    funext k
    simp [Matrix.mulVec, dotProduct, Matrix.updateCol_apply, Pi.single_apply]
  refine ⟨By * Bx⁻¹, ?_⟩
  have h1 : ((Bx⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix _ _ _) *ᵥ x =
      Pi.single i 1 := by
    have h2 : (Bx : Matrix _ _ _) *ᵥ Pi.single i 1 = x := hBe x
    rw [← h2, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h1]
  exact hBe y

theorem exists_sl_mulVec_eq {n : ℕ} {x y : Fin n → ZMod 2} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2), (A : Matrix _ _ _) *ᵥ x = y := by
  have h01 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
  have hxi : x i = 1 := h01 _ hi
  have hyj : y j = 1 := h01 _ hj
  by_cases hyi : y i = 1
  · exact exists_sl_mulVec_eq_of_coord hxi hyi
  · have hij : i ≠ j := fun h => hyi (h ▸ hyj)
    set z : Fin n → ZMod 2 := Pi.single i 1 + Pi.single j 1
    have hzi : z i = 1 := by simp [z, hij]
    have hzj : z j = 1 := by simp [z, hij.symm]
    obtain ⟨A₁, hA₁⟩ := exists_sl_mulVec_eq_of_coord hxi hzi
    obtain ⟨A₂, hA₂⟩ := exists_sl_mulVec_eq_of_coord hzj hyj
    refine ⟨A₂ * A₁, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hA₁, hA₂]

theorem eq_bot_or_eq_top_of_binaryNaturalSL {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
    {n : ℕ} (hnat : BinaryNaturalSL H ⊤ ⊥ n 1) (J : Subgroup W)
    (hJ : ∀ h ∈ H, ∀ w ∈ J, (h : MulAut W) w ∈ J) : J = ⊥ ∨ J = ⊤ := by
  obtain ⟨π, -, -, -, -, -, -, -, β, -, hβ1, hβe⟩ :=
    CFSG.Quasithin.FFC.BinaryNaturalSL.exists_zmod hnat
  by_cases hJb : J = ⊥
  · exact Or.inl hJb
  right
  obtain ⟨⟨u, huJ⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hJb
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  rw [eq_top_iff]
  intro w _
  by_cases hw1 : w = 1
  · rw [hw1]; exact J.one_mem
  have hβinj : ∀ a b : ↥(⊤ : Subgroup W), β a = β b → a = b := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    rw [hβ1, Subgroup.mem_bot] at h1
    exact Subtype.ext (mul_inv_eq_one.mp h1)
  obtain ⟨mu, hmu⟩ := QuotientGroup.mk_surjective (β ⟨u, Subgroup.mem_top u⟩)
  obtain ⟨mw, hmw⟩ := QuotientGroup.mk_surjective (β ⟨w, Subgroup.mem_top w⟩)
  have hne : ∀ (m : ↥(FFModel.nat (Assembly.LowTwoRank.StatedSL n (ZMod 2))).sec) (x : W),
      (QuotientGroup.mk m : ↥(FFModel.nat (Assembly.LowTwoRank.StatedSL n (ZMod 2))).sec ⧸
        (FFModel.nat (Assembly.LowTwoRank.StatedSL n (ZMod 2))).ker.subgroupOf
          (FFModel.nat (Assembly.LowTwoRank.StatedSL n (ZMod 2))).sec) =
        β ⟨x, Subgroup.mem_top x⟩ →
      x ≠ 1 →
        Multiplicative.toAdd (m.1 : Multiplicative (Fin n → ZMod 2)) ≠ (0 : Fin n → ZMod 2) := by
    intro m x hm hx h0
    apply hx
    have hm1 : m = 1 := by
      apply Subtype.ext
      show (m.1 : Multiplicative (Fin n → ZMod 2)) = 1
      exact (Multiplicative.toAdd (α := Fin n → ZMod 2)).injective
        (h0.trans (toAdd_one (α := Fin n → ZMod 2)).symm)
    have h1 : β ⟨x, Subgroup.mem_top x⟩ = 1 := by
      rw [← hm, hm1]
      rfl
    rw [hβ1, Subgroup.mem_bot] at h1
    exact h1
  obtain ⟨A, hA⟩ := exists_sl_mulVec_eq (hne mu u hmu hu1') (hne mw w hmw hw1)
  set γ := specialLinearGroupEquivStatedSL n (ZMod 2) A with hγ
  have h1 := hβe γ ⟨u, Subgroup.mem_top u⟩ mu (Subgroup.mem_top _) (Subgroup.mem_top _) hmu.symm
  have h2 : (⟨(FFModel.nat (Assembly.LowTwoRank.StatedSL n (ZMod 2))).act γ mu.1,
      Subgroup.mem_top _⟩ : ↥(FFModel.nat (Assembly.LowTwoRank.StatedSL n (ZMod 2))).sec) =
      mw := by
    apply Subtype.ext
    show Multiplicative.ofAdd (((γ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      Multiplicative.toAdd mu.1) = mw.1
    rw [hγ, specialLinearGroupEquivStatedSL_coe]
    exact (congrArg Multiplicative.ofAdd hA).trans (ofAdd_toAdd _)
  have h3 : β ⟨((π γ : ↥H) : MulAut W) u, Subgroup.mem_top _⟩ = β ⟨w, Subgroup.mem_top w⟩ :=
    h1.trans ((congrArg QuotientGroup.mk h2).trans hmw)
  have h4 : ((π γ : ↥H) : MulAut W) u = w := congrArg Subtype.val (hβinj _ _ h3)
  rw [← h4]
  exact hJ _ (π γ).2 u huJ

theorem ne_bot_of_binaryNaturalSL {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
    {n : ℕ} (hnat : BinaryNaturalSL H ⊤ ⊥ n 1) (hn : 2 ≤ n) : H ≠ ⊥ := by
  obtain ⟨K, _, _, -, ⟨e⟩⟩ := hnat.exists_equiv
  intro hH
  have : Subsingleton ↥H := by rw [hH]; infer_instance
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  set t : Matrix.SpecialLinearGroup (Fin n) K :=
    ⟨Matrix.transvection ⟨0, by omega⟩ ⟨1, by omega⟩ 1,
      Matrix.det_transvection_of_ne _ _ hij 1⟩ with ht
  have ht1 : t ≠ 1 := by
    intro h1
    have h2 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin n) K =>
      (A : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨1, by omega⟩) h1
    simp [ht, Matrix.transvection, hij] at h2
  apply ht1
  apply (specialLinearGroupEquivStatedSL n K).injective
  apply e.injective
  exact Subsingleton.elim _ _

section Hyp

variable {G : Type} [Group G]

theorem eq_bot_or_eq_of_natural {L X : Subgroup G} [IsMulCommutative ↥X] {n : ℕ}
    (hLX : L ≤ Subgroup.normalizer (X : Set G))
    (hnat : BinaryNaturalSL (V := ↥X) (autOn L X) ⊤ ⊥ n 1) (J : Subgroup G) (hJX : J ≤ X)
    (hLJ : L ≤ Subgroup.normalizer (J : Set G)) : J = ⊥ ∨ J = X := by
  have hinv : ∀ a ∈ autOn L X, ∀ w ∈ J.subgroupOf X, (a : MulAut ↥X) w ∈ J.subgroupOf X := by
    intro a ha w hw
    obtain ⟨⟨l, hl⟩, rfl⟩ := (A4.mem_autOn_iff hLX).mp ha
    rw [Subgroup.mem_subgroupOf, A4.actionOn_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hLJ hl) w).mp hw
  rcases eq_bot_or_eq_top_of_binaryNaturalSL hnat (J.subgroupOf X) hinv with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hJX hx⟩ : ↥X) ∈ J.subgroupOf X := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · right
    refine le_antisymm hJX fun x hx => ?_
    have : (⟨x, hx⟩ : ↥X) ∈ J.subgroupOf X := h ▸ Subgroup.mem_top _
    exact this

theorem ne_bot_of_natural {L X : Subgroup G} [IsMulCommutative ↥X] {n : ℕ} (hn : 2 ≤ n)
    (hnat : BinaryNaturalSL (V := ↥X) (autOn L X) ⊤ ⊥ n 1) : X ≠ ⊥ := by
  intro hX
  apply ne_bot_of_binaryNaturalSL hnat hn
  rw [eq_bot_iff]
  intro a _
  rw [Subgroup.mem_bot]
  have : Subsingleton ↥X := by rw [hX]; infer_instance
  exact MulEquiv.ext fun x => Subsingleton.elim _ _

variable [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ}

theorem normalizer_le_of_hyp121 (hyp : Hyp121 G T L V V₁ V₂ n) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  obtain ⟨hnorm, -, -⟩ := hyp.reduced
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hyp.le).mp hnorm

theorem pCoreOf_le_centralizer_of_hyp121 (hyp : Hyp121 G T L V V₁ V₂ n) :
    pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
  InternalSec.pCoreOf_le_centralizer_of_isPrimeReduced hyp.le hyp.reduced
    (A4.subnormal_of_normal Subgroup.le_normalizer
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl))

theorem inf_centralizer_le_pCoreOf_of_hyp121 (hyp : Hyp121 G T L V V₁ V₂ n) {X : Subgroup G}
    [IsMulCommutative ↥X] (hXV : X ≤ V) (hLX : L ≤ Subgroup.normalizer (X : Set G))
    (hnat : BinaryNaturalSL (V := ↥X) (autOn L X) ⊤ ⊥ n 1) :
    L ⊓ Subgroup.centralizer (X : Set G) ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 : 2 ≤ n := by rcases hyp.rank with h | h <;> omega
  have hn3 : 3 ≤ n := by rcases hyp.rank with h | h <;> omega
  have hO2L := pCoreOf_le_centralizer_of_hyp121 hyp
  obtain ⟨eL⟩ := hyp.iso
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    CFSG.Quasithin.Vol2.Ch11.SecA.isSimpleGroup_SL_zmod_two hn3
  have : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := eL.isSimpleGroup
  set N₁ := (L ⊓ Subgroup.centralizer (X : Set G)).subgroupOf L with hN₁
  have hN₁n : N₁.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hN₁, Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 hx.1) (L.inv_mem g.2),
      Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hv' : (g : G)⁻¹ * v * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (hLX (L.inv_mem g.2)) v).mp hv
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hv'
    calc v * ((g : G) * x * (g : G)⁻¹) = g * ((g : G)⁻¹ * v * g * x) * (g : G)⁻¹ := by group
      _ = g * (x * ((g : G)⁻¹ * v * g)) * (g : G)⁻¹ := by rw [hc]
      _ = (g : G) * x * (g : G)⁻¹ * v := by group
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N₁.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with h | h
  · intro x hx
    have hx1 : (⟨x, hx.1⟩ : ↥L) ∈ N₁ := by
      rw [hN₁, Subgroup.mem_subgroupOf]
      exact hx
    have hx2 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hx.1⟩ ∈
        N₁.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := Subgroup.mem_map_of_mem _ hx1
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx2
    exact ⟨⟨x, hx.1⟩, hx2, rfl⟩
  · exfalso
    apply ne_bot_of_binaryNaturalSL hnat hn2
    refine Lem12.autOn_eq_bot_of_le_centralizer fun l hl => ?_
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨l, hl⟩ ∈
        N₁.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := h ▸ Subgroup.mem_top _
    obtain ⟨c, hc, hcl⟩ := hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcl
    have hq : (c : G)⁻¹ * l ∈ Subgroup.centralizer (X : Set G) :=
      Subgroup.centralizer_le (by exact_mod_cast hXV) (hO2L ⟨_, hcl, rfl⟩)
    have hc' : (c : G) ∈ L ⊓ Subgroup.centralizer (X : Set G) := hc
    have : l = c * ((c : G)⁻¹ * l) := by group
    rw [this]
    exact Subgroup.mul_mem _ hc'.2 hq

theorem inf_centralizer_le_centralizer_of_hyp121 (hyp : Hyp121 G T L V V₁ V₂ n)
    {X : Subgroup G} [IsMulCommutative ↥X] (hXV : X ≤ V)
    (hLX : L ≤ Subgroup.normalizer (X : Set G))
    (hnat : BinaryNaturalSL (V := ↥X) (autOn L X) ⊤ ⊥ n 1) :
    L ⊓ Subgroup.centralizer (X : Set G) ≤ Subgroup.centralizer (V : Set G) :=
  (inf_centralizer_le_pCoreOf_of_hyp121 hyp hXV hLX hnat).trans
    (pCoreOf_le_centralizer_of_hyp121 hyp)

theorem eq_one_of_commute_of_hyp121 (hyp : Hyp121 G T L V V₁ V₂ n) [IsMulCommutative ↥V]
    {c : MulAut ↥V} (hc : ∀ y ∈ autOn L V, c * y = y * c) : c = 1 := by
  have hn2 : 2 ≤ n := by rcases hyp.rank with h | h <;> omega
  obtain ⟨hc₁, hnat₁⟩ := hyp.nat₁
  obtain ⟨hc₂, hnat₂⟩ := hyp.nat₂
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hV₂V : V₂ ≤ V := hyp.sup ▸ le_sup_right
  exact Sec121.eq_one_of_commute_autOn hn2 hV₁V hV₂V hyp.sup hyp.inf
    (Subgroup.le_normalizer.trans (normalizer_le_of_hyp121 hyp)) hyp.norm₁ hyp.norm₂
    (ne_bot_of_natural hn2 hnat₁) (ne_bot_of_natural hn2 hnat₂)
    (eq_bot_or_eq_of_natural hyp.norm₁ hnat₁) (eq_bot_or_eq_of_natural hyp.norm₂ hnat₂)
    hnat₁ hnat₂ hyp.dual hc

end Hyp

end Sec121Q

open Sec121Q Sec121 Sec121Thm

theorem setup121Q_holds : Setup121Q := by
  intro G _ _ T L V V₁ V₂ n hyp hTL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hc₁, hnat₁⟩ := hyp.nat₁
  have hVe := isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have := hVe.1
  have hMV := normalizer_le_of_hyp121 hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer.trans hMV
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV (hTL.trans hMV)
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hO2L := pCoreOf_le_centralizer_of_hyp121 hyp
  have hCL : L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L := fun x hx =>
    inf_centralizer_le_pCoreOf_of_hyp121 hyp hV₁V hyp.norm₁ hnat₁
      ⟨hx.1, Subgroup.centralizer_le (by exact_mod_cast hV₁V) hx.2⟩
  have hC2 : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
    rintro ⟨c, hcLT, hcV⟩
    obtain ⟨l, hl, t, ht, rfl⟩ := Lem24.exists_mul_of_mem_sup_normal hTL hcLT
    obtain ⟨k, hk⟩ := hyp.sylow.1 ⟨t, ht⟩
    have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨z, hz, hzc⟩ := Lem24.exists_pow_eq_mul_pow hl (hTL ht) (2 ^ k)
    rw [hk', mul_one] at hzc
    have hzC : z ∈ L ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨hz, hzc ▸ Subgroup.pow_mem _ hcV _⟩
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨z, hCL hzC⟩
    have hj' : z ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    refine ⟨k + j, Subtype.ext ?_⟩
    show (l * t) ^ 2 ^ (k + j) = 1
    rw [pow_add, pow_mul, hzc, hj']
  have hNC : Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      inferInstance
  have hge : T ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T) :=
    (inf_le_inf_right _ le_sup_right).trans
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        ((le_inf Subgroup.le_normalizer (hLTV.trans hNC)).trans
          Subgroup.inf_normalizer_le_normalizer_inf) hC2)
  have hO2LT : L ⊓ pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      ((le_inf Subgroup.le_normalizer
          (le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)))).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).to_le inf_le_right)
  have hle : pCoreOf 2 (L ⊔ T) ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
    refine le_inf (B6.pCoreOf_two_le_of_isSylowTwoOf
      (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right)) fun q hq => ?_
    have hqLT : q ∈ L ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 (L ⊔ T) hq
    have hQn : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
    have hLN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
    have hc : ∀ y ∈ autOn L V, A4.actionOn V (L ⊔ T) hLTV ⟨q, hqLT⟩ * y =
        y * A4.actionOn V (L ⊔ T) hLTV ⟨q, hqLT⟩ := by
      intro y hy
      obtain ⟨⟨l, hl⟩, rfl⟩ := (A4.mem_autOn_iff hLV).mp hy
      set k := l⁻¹ * q⁻¹ * l * q with hk
      have hkL : k ∈ L := by
        have h1 : q⁻¹ * l * q⁻¹⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (hLN ((L ⊔ T).inv_mem hqLT)) l).mp hl
        have h2 := L.mul_mem (L.inv_mem hl) h1
        simpa [hk, mul_assoc] using h2
      have hkQ : k ∈ pCoreOf 2 (L ⊔ T) := by
        have h1 : l⁻¹ * q⁻¹ * l⁻¹⁻¹ ∈ pCoreOf 2 (L ⊔ T) :=
          (Subgroup.mem_normalizer_iff.mp (hQn (Subgroup.mem_sup_left (L.inv_mem hl))) _).mp
            (Subgroup.inv_mem _ hq)
        have h2 := Subgroup.mul_mem _ h1 hq
        simpa [hk, mul_assoc] using h2
      have hkV := Subgroup.mem_centralizer_iff.mp (hO2L (hO2LT ⟨hkL, hkQ⟩))
      refine MulEquiv.ext fun v => Subtype.ext ?_
      simp only [MulAut.mul_apply, A4.actionOn_apply_coe]
      have hkv : v.1 * k = k * v.1 := hkV v.1 v.2
      have e1 : l * q = q * l * k := by rw [hk]; group
      calc q * (l * v.1 * l⁻¹) * q⁻¹ = q * l * (v.1 * k) * k⁻¹ * l⁻¹ * q⁻¹ := by group
        _ = q * l * (k * v.1) * k⁻¹ * l⁻¹ * q⁻¹ := by rw [hkv]
        _ = (q * l * k) * v.1 * (q * l * k)⁻¹ := by group
        _ = (l * q) * v.1 * (l * q)⁻¹ := by rw [e1]
        _ = l * (q * v.1 * q⁻¹) * l⁻¹ := by group
    exact (A4.actionOn_eq_one_iff hLTV ⟨q, hqLT⟩).mp (eq_one_of_commute_of_hyp121 hyp hc)
  exact le_antisymm hle hge

theorem stmt12_1_11_of_lemmas (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h1217 : Lem1217)
    (h1218 : Lem1218) (h1219 : Lem1219) (h12110 : Lem12110) : Stmt12_1_11 :=
  stmt12_1_11_of h1001 h331 setup121Q_holds h1217 h1218 h1219 h12110

end CFSG.Quasithin.H13

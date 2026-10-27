module

public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.Vol2.Ch1Quotient
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.SteinbergBMQuasisimpleCenterlessImage
public import CFSG.Quasithin.Vol2.Ch3Sec1Cases
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqBasic
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqOrb

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.Lem1227Eq
open scoped commutatorElement

namespace Lem1227Lt

structure LtHyp (G : Type) [Group G] [Finite G] (T K Y : Subgroup G) : Prop where
  hYloc : quasithinIsLocal T Y
  hKloc : quasithinIsLocal T K
  hTY : T ≤ Subgroup.normalizer (Y : Set G)
  hTK : T ≤ Subgroup.normalizer (K : Set G)
  hKY : K < Y
  hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)

namespace LtHyp

variable {G : Type} [Group G] [Finite G] {T K Y : Subgroup G}

theorem sylow (h : LtHyp G T K Y) : IsSylowTwoOf T (Y ⊔ T) :=
  ⟨le_sup_right, h.hYloc.1, h.hYloc.2.2.1⟩

theorem sup_le_normalizer (h : LtHyp G T K Y) : Y ⊔ T ≤ Subgroup.normalizer (Y : Set G) :=
  sup_le Subgroup.le_normalizer h.hTY

theorem cComp (h : LtHyp G T K Y) : Y ∈ cComp (Y ⊔ T) := cComp_of_isLocal h.hYloc

theorem K_perfect (h : LtHyp G T K Y) : ⁅K, K⁆ = K :=
  perfect_of_mem_cComp (cComp_of_isLocal h.hKloc)

theorem K_ne_bot (h : LtHyp G T K Y) : K ≠ ⊥ := ne_bot_of_mem_cComp (cComp_of_isLocal h.hKloc)

theorem pCoreOf_le (h : LtHyp G T K Y) : pCoreOf 2 Y ≤ T := by
  have h1 : pCoreOf 2 Y ≤ pCoreOf 2 (Y ⊔ T) :=
    pCoreOf_le_pCoreOf_of_normal le_sup_left h.sup_le_normalizer
  intro x hx
  have hx' := h1 hx
  obtain ⟨y, hy, rfl⟩ := hx'
  have hy' : y ∈ CFSG.pCore 2 ↥(Y ⊔ T) := by
    exact hy
  exact (pCore_two_le_subgroupOf h.sylow hy' : y ∈ T.subgroupOf (Y ⊔ T))

theorem lemmaA (h : LtHyp G T K Y) : ¬ Y ≤ K ⊔ pCoreOf 2 Y := by
  intro hY
  have hRY : pCoreOf 2 Y ≤ Y := LieType.BorelTits.pCoreOf_le 2 Y
  have hKRN : K ⊔ pCoreOf 2 Y ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer (h.pCoreOf_le.trans h.hTK)
  have hYeq : Y = K ⊔ pCoreOf 2 Y := le_antisymm hY (sup_le h.hKY.le hRY)
  have hYN : Y ≤ Subgroup.normalizer (K : Set G) := hYeq ▸ hKRN
  have hKn : (K.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.hKY.le).mpr hYN
  have hYn : (Y.subgroupOf (Y ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr h.sup_le_normalizer
  have hsub : IsSubnormal K (Y ⊔ T) :=
    IsSubnormal.step h.hKY.le hKn (IsSubnormal.step le_sup_left hYn (IsSubnormal.refl _))
  exact not_subnormal_of_mem_cComp h.cComp h.hKY h.K_ne_bot h.K_perfect hsub

theorem sylow_inf (h : LtHyp G T K Y) : IsSylowTwoOf (T ⊓ Y) Y := by
  have hYn : (Y.subgroupOf (Y ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr h.sup_le_normalizer
  exact A312.isSylowTwoOf_inf_of_subnormal
    (IsSubnormal.step le_sup_left hYn (IsSubnormal.refl _)) h.sylow

theorem K'_perfect (h : LtHyp G T K Y) : ⁅K.subgroupOf Y, K.subgroupOf Y⁆ = K.subgroupOf Y := by
  have hK : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr h.K_perfect
  let e := Subgroup.subgroupOfEquivOfLe h.hKY.le
  have : Group.IsPerfect ↥(K.subgroupOf Y) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.isPerfect_iff.mp this

end LtHyp

section Phi

variable {G : Type} [Group G] [Finite G] {T K Y : Subgroup G} {Λ : Type} [Group Λ]

abbrev conjY (h : LtHyp G T K Y) (t : ↥T) : MulAut ↥Y := Y.normalizerMonoidHom ⟨(t : G), h.hTY t.2⟩

theorem coe_conjY (h : LtHyp G T K Y) (t : ↥T) (y : ↥Y) :
    ((conjY h t y : ↥Y) : G) = t * y * (t : G)⁻¹ := rfl

theorem exists_act {Y' : Type*} [Group Y'] (φ : Y' →* Λ) (hφ : Function.Surjective φ)
    (c : MulAut Y') (hc : ∀ y, φ y = 1 → φ (c y) = 1) (hc' : ∀ y, φ y = 1 → φ (c.symm y) = 1) :
    ∃ α : MulAut Λ, ∀ y, α (φ y) = φ (c y) := by
  have h1 : φ.ker ≤ (φ.comp c.toMonoidHom).ker := fun y hy => hc y hy
  have h2 : φ.ker ≤ (φ.comp c.symm.toMonoidHom).ker := fun y hy => hc' y hy
  set α₀ : Λ →* Λ := φ.liftOfSurjective hφ ⟨φ.comp c.toMonoidHom, h1⟩ with hα₀
  set α₁ : Λ →* Λ := φ.liftOfSurjective hφ ⟨φ.comp c.symm.toMonoidHom, h2⟩ with hα₁
  have e0 : ∀ y, α₀ (φ y) = φ (c y) := fun y =>
    φ.liftOfRightInverse_comp_apply (Function.surjInv hφ) (Function.rightInverse_surjInv hφ)
      ⟨φ.comp c.toMonoidHom, h1⟩ y
  have e1 : ∀ y, α₁ (φ y) = φ (c.symm y) := fun y =>
    φ.liftOfRightInverse_comp_apply (Function.surjInv hφ) (Function.rightInverse_surjInv hφ)
      ⟨φ.comp c.symm.toMonoidHom, h2⟩ y
  refine ⟨MulEquiv.mk' { toFun := α₀, invFun := α₁, left_inv := ?_, right_inv := ?_ }
    (fun x y => map_mul α₀ x y), e0⟩
  · intro x
    obtain ⟨y, rfl⟩ := hφ x
    show α₁ (α₀ (φ y)) = φ y
    rw [e0, e1]
    simp
  · intro x
    obtain ⟨y, rfl⟩ := hφ x
    show α₀ (α₁ (φ y)) = φ y
    rw [e1, e0]
    simp

@[expose] def imgK (K Y : Subgroup G) (φ : ↥Y →* Λ) : Subgroup Λ := (K.subgroupOf Y).map φ

@[expose] def imgS (T Y : Subgroup G) (φ : ↥Y →* Λ) : Subgroup Λ := ((T ⊓ Y).subgroupOf Y).map φ

abbrev psi (h : LtHyp G T K Y) (φ : ↥Y →* Λ) : ↥K →* Λ := φ.comp (Subgroup.inclusion h.hKY.le)

theorem imgK_eq_range (h : LtHyp G T K Y) (φ : ↥Y →* Λ) : imgK K Y φ = (psi h φ).range := by
  ext b
  simp only [imgK, Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨(y : G), hy⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨Subgroup.inclusion h.hKY.le k, k.2, rfl⟩

theorem imgK_perfect (h : LtHyp G T K Y) (φ : ↥Y →* Λ) :
    ⁅imgK K Y φ, imgK K Y φ⁆ = imgK K Y φ := by
  unfold imgK
  rw [← Subgroup.map_commutator, h.K'_perfect]

theorem imgK_ne_bot (h : LtHyp G T K Y) (φ : ↥Y →* Λ)
    (hkc : ∀ y : ↥Y, φ y = 1 →
      (QuotientGroup.mk y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    imgK K Y φ ≠ ⊥ := by
  intro hbot
  have hle : K.subgroupOf Y ≤ φ.ker := (Subgroup.map_eq_bot_iff _).mp hbot
  have : (CFSG.pCore 2 ↥Y).Normal := CFSG.pCore_normal
  set π : ↥Y →* ↥Y ⧸ CFSG.pCore 2 ↥Y := QuotientGroup.mk' _ with hπ
  have hC : (K.subgroupOf Y).map π ≤ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    rintro _ ⟨k, hk, rfl⟩
    exact hkc k (hle hk)
  have hCperf : ⁅(K.subgroupOf Y).map π, (K.subgroupOf Y).map π⁆ = (K.subgroupOf Y).map π := by
    rw [← Subgroup.map_commutator, h.K'_perfect]
  have hCbot : (K.subgroupOf Y).map π = ⊥ := by
    rw [← hCperf]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hC.trans (Subgroup.center_le_centralizer _))
  have hKπ : K.subgroupOf Y ≤ CFSG.pCore 2 ↥Y := by
    have := (Subgroup.map_eq_bot_iff _).mp hCbot
    rwa [hπ, QuotientGroup.ker_mk'] at this
  have hp : IsPGroup 2 ↥(K.subgroupOf Y) := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).to_le hKπ
  have hpK : IsPGroup 2 ↥K := hp.of_equiv (Subgroup.subgroupOfEquivOfLe h.hKY.le)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥K := hpK.isNilpotent
  exact not_isSolvable_of_mem_cComp (cComp_of_isLocal h.hKloc) inferInstance

theorem commutator_mul_central_left' {Y' : Type*} [Group Y'] {c : Y'}
    (hc : c ∈ Subgroup.center Y') (y w : Y') : ⁅y * c, w⁆ = ⁅y, w⁆ := by
  have h : ⁅c, w⁆ = 1 := Commute.commutator_eq (Subgroup.mem_center_iff.mp hc w).symm
  rw [commutatorElement_mul_left_eq_conj_mul, h]
  simp

theorem commutator_mul_central_right' {Y' : Type*} [Group Y'] {c : Y'}
    (hc : c ∈ Subgroup.center Y') (y w : Y') : ⁅y, w * c⁆ = ⁅y, w⁆ := by
  have h : ⁅y, c⁆ = 1 := Commute.commutator_eq (Subgroup.mem_center_iff.mp hc y)
  rw [commutatorElement_mul_right_eq_mul_conj, h]
  simp

theorem imgK_ne_top (h : LtHyp G T K Y) (φ : ↥Y →* Λ)
    (hkc : ∀ y : ↥Y, φ y = 1 →
      (QuotientGroup.mk y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    imgK K Y φ ≠ ⊤ := by
  intro htop
  apply h.lemmaA
  have step1 : ∀ y : ↥Y, ∃ k ∈ K.subgroupOf Y, φ k = φ y := by
    intro y
    have : φ y ∈ imgK K Y φ := htop ▸ Subgroup.mem_top _
    obtain ⟨k, hk, hky⟩ := this
    exact ⟨k, hk, hky⟩
  have hq := h.hYq
  have : (CFSG.pCore 2 ↥Y).Normal := CFSG.pCore_normal
  set π : ↥Y →* ↥Y ⧸ CFSG.pCore 2 ↥Y := QuotientGroup.mk' _ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hNc : φ.ker.map π ≤ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hkc y hy
  have step3 : ∀ w : ↥Y ⧸ CFSG.pCore 2 ↥Y, ∃ c ∈ (K.subgroupOf Y).map π,
      ∃ z ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y), w = c * z := by
    intro w
    obtain ⟨y, rfl⟩ := hπs w
    obtain ⟨k, hk, hky⟩ := step1 y
    refine ⟨π k, ⟨k, hk, rfl⟩, π (k⁻¹ * y), hNc ⟨k⁻¹ * y, ?_, rfl⟩, ?_⟩
    · show k⁻¹ * y ∈ φ.ker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hky, inv_mul_cancel]
    · rw [← map_mul]
      congr 1
      group
  have hCtop : (K.subgroupOf Y).map π = ⊤ := by
    rw [eq_top_iff]
    have hc : commutator (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ (K.subgroupOf Y).map π := by
      rw [commutator_def]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      obtain ⟨c₁, hc₁, z₁, hz₁, rfl⟩ := step3 a
      obtain ⟨c₂, hc₂, z₂, hz₂, rfl⟩ := step3 b
      rw [commutator_mul_central_left' hz₁, commutator_mul_central_right' hz₂,
        commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hc₁ hc₂) (inv_mem hc₁)) (inv_mem hc₂)
    rw [Group.isPerfect_def.mp hq.1] at hc
    exact hc
  intro y hy
  obtain ⟨k, hk, hky⟩ : ∃ k ∈ K.subgroupOf Y, π k = π ⟨y, hy⟩ := by
    have : π ⟨y, hy⟩ ∈ (K.subgroupOf Y).map π := hCtop ▸ Subgroup.mem_top _
    exact this
  have hr : k⁻¹ * ⟨y, hy⟩ ∈ CFSG.pCore 2 ↥Y := (QuotientGroup.eq (s := CFSG.pCore 2 ↥Y)).1 hky
  have hrG : ((k⁻¹ * ⟨y, hy⟩ : ↥Y) : G) ∈ pCoreOf 2 Y := (mem_pCore_iff_coe _).1 hr
  have hkG : ((k : ↥Y) : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
  have hyeq : y = ((k : ↥Y) : G) * ((k⁻¹ * ⟨y, hy⟩ : ↥Y) : G) := by simp
  rw [hyeq]
  exact Subgroup.mul_mem_sup hkG hrG

theorem isSylow_imgS (h : LtHyp G T K Y) (φ : ↥Y →* Λ) (hs : Function.Surjective φ) :
    IsSylowTwoOf (imgS T Y φ) ⊤ :=
  isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf h.sylow_inf) φ hs

theorem imgS_le_normalizer (h : LtHyp G T K Y) (φ : ↥Y →* Λ) :
    imgS T Y φ ≤ Subgroup.normalizer (imgK K Y φ : Set Λ) := by
  have key : ∀ s ∈ imgS T Y φ, ∀ b ∈ imgK K Y φ, s * b * s⁻¹ ∈ imgK K Y φ := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨k, hk, rfl⟩
    refine ⟨y * k * y⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have hyT : (y : G) ∈ T := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hy)).1
    refine Subgroup.mem_subgroupOf.2 ?_
    exact (Subgroup.mem_normalizer_iff.1 (h.hTK hyT) _).1 (Subgroup.mem_subgroupOf.1 hk)
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact key s hs b hb
  · intro hb
    have := key s⁻¹ (inv_mem hs) _ hb
    simpa [mul_assoc] using this

theorem conjY_symm (h : LtHyp G T K Y) (t : ↥T) : (conjY h t).symm = conjY h t⁻¹ := by
  refine MulEquiv.ext fun y => ?_
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  simp only [coe_conjY, Subgroup.coe_inv]
  group

theorem exists_act_T [Finite Λ] (h : LtHyp G T K Y) (φ : ↥Y →* Λ) (hs : Function.Surjective φ)
    (hinv : ∀ t : ↥T, ∀ y : ↥Y, φ y = 1 → φ (conjY h t y) = 1) (t : ↥T) :
    ∃ α : MulAut Λ, (∀ y : ↥Y, α (φ y) = φ (conjY h t y)) ∧
      (imgK K Y φ).map α.toMonoidHom = imgK K Y φ ∧
      (imgS T Y φ).map α.toMonoidHom = imgS T Y φ := by
  obtain ⟨α, hα⟩ := exists_act φ hs (conjY h t) (hinv t)
    (fun y hy => by rw [conjY_symm]; exact hinv t⁻¹ y hy)
  refine ⟨α, hα, ?_, ?_⟩
  · have hle : (imgK K Y φ).map α.toMonoidHom ≤ imgK K Y φ := by
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨conjY h t k, ?_, (hα k).symm⟩
      have hk' := Subgroup.mem_subgroupOf.1 hk
      refine Subgroup.mem_subgroupOf.2 ?_
      exact (Subgroup.mem_normalizer_iff.1 (h.hTK t.2) _).1 hk'
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective α.injective])
  · have hle : (imgS T Y φ).map α.toMonoidHom ≤ imgS T Y φ := by
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨conjY h t k, ?_, (hα k).symm⟩
      have hk' := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)
      refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, (conjY h t k).2⟩)
      exact T.mul_mem (T.mul_mem t.2 hk'.1) (T.inv_mem t.2)
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective α.injective])

theorem psi_conj (h : LtHyp G T K Y) (φ : ↥Y →* Λ) (t : ↥T) {α : MulAut Λ}
    (hα : ∀ y : ↥Y, α (φ y) = φ (conjY h t y)) (x : ↥K) :
    psi h φ (K.normalizerMonoidHom ⟨(t : G), h.hTK t.2⟩ x) = α (psi h φ x) := by
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hα]
  rfl

theorem mulAut_center {Q : Type*} [Group Q] (α : MulAut Q) {z : Q} (hz : z ∈ Subgroup.center Q) :
    α z ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g', rfl⟩ := α.surjective g
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g']

abbrev piY (Y : Subgroup G) : ↥Y →* ↥Y ⧸ CFSG.pCore 2 ↥Y := QuotientGroup.mk' _

theorem exists_act_pi (h : LtHyp G T K Y) (t : ↥T) :
    ∃ α : MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y), ∀ y, α (piY Y y) = piY Y (conjY h t y) := by
  have hker : ∀ s : ↥T, ∀ y : ↥Y, piY Y y = 1 → piY Y (conjY h s y) = 1 := by
    intro s y hy
    have hy' : y ∈ CFSG.pCore 2 ↥Y := (QuotientGroup.eq_one_iff y).1 hy
    have h1 := CFSG.pCore_map_iso 2 (conjY h s)
    have h2 : conjY h s y ∈ CFSG.pCore 2 ↥Y := by
      rw [← h1]
      exact ⟨y, hy', rfl⟩
    exact (QuotientGroup.eq_one_iff _).2 h2
  exact exists_act (piY Y) (QuotientGroup.mk'_surjective _) (conjY h t) (hker t)
    (fun y hy => by rw [conjY_symm]; exact hker t⁻¹ y hy)

variable {X : Type} [Group X]

abbrev phiOf (Y : Subgroup G) (ν : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* X) : ↥Y →* X := ν.comp (piY Y)

theorem ker_nu (h : LtHyp G T K Y) [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a)
    {ν : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* X} (hν : Function.Surjective ν) :
    ν.ker = Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
  (SteinbergBM.five_quasisimple_centerless_image h.hYq hX ν hν).1

theorem phi_hkc (h : LtHyp G T K Y) [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a)
    {ν : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* X} (hν : Function.Surjective ν) (y : ↥Y) :
    phiOf Y ν y = 1 ↔
      (QuotientGroup.mk y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  rw [← ker_nu h hX hν]
  rfl

omit [Finite G] in
theorem phi_surj {ν : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* X} (hν : Function.Surjective ν) :
    Function.Surjective (phiOf Y ν) :=
  hν.comp (QuotientGroup.mk'_surjective _)

theorem hinv_of_hk (h : LtHyp G T K Y) {Λ : Type} [Group Λ] (φ : ↥Y →* Λ)
    (hk : ∀ y : ↥Y, φ y = 1 ↔
      (QuotientGroup.mk y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (t : ↥T) (y : ↥Y) (hy : φ y = 1) : φ (conjY h t y) = 1 := by
  obtain ⟨α, hα⟩ := exists_act_pi h t
  have h1 := (hk y).1 hy
  have h2 : (QuotientGroup.mk (conjY h t y) : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈
      Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    have := mulAut_center α h1
    rwa [show (QuotientGroup.mk y : ↥Y ⧸ CFSG.pCore 2 ↥Y) = piY Y y from rfl, hα] at this
  exact (hk _).2 h2

end Phi

end Lem1227Lt

end CFSG.Quasithin.H13

module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S4b
public import CFSG.Quasithin.Vol2.Ch3Sec3InspWalter
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S2c
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S3b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ASInputs
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem star_sup {B N K K' : Subgroup G} [(N.subgroupOf B).Normal] (hK : K ≤ B) (hK' : K' ≤ B) :
    star B N (K ⊔ K') = star B N K ⊔ star B N K' := by
  unfold star
  rw [Subgroup.subgroupOf_sup hK hK', Subgroup.map_sup]

omit [Finite G] in
theorem mk_mem_normalizer_star {B N K : Subgroup G} [(N.subgroupOf B).Normal] {g : G}
    (hgB : g ∈ B) (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    QuotientGroup.mk' (N.subgroupOf B) ⟨g, hgB⟩ ∈
      Subgroup.normalizer ((star B N K : Subgroup (↥B ⧸ N.subgroupOf B)) :
        Set (↥B ⧸ N.subgroupOf B)) := by
  have h1 : (⟨g, hgB⟩ : ↥B) ∈ Subgroup.normalizer ((K.subgroupOf B : Subgroup ↥B) : Set ↥B) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hg x
  exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ h1)

omit [Finite G] in
theorem star_conj {B N K : Subgroup G} [(N.subgroupOf B).Normal] {g : G} (hgB : g ∈ B) :
    (star B N K).map (MulAut.conj (QuotientGroup.mk' (N.subgroupOf B) ⟨g, hgB⟩)).toMonoidHom =
      star B N (conjByElt g K) := by
  ext q
  rw [Subgroup.mem_map, mem_star_iff]
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨k, hkB, hk, rfl⟩ := mem_star_iff.mp hs
    refine ⟨g * k * g⁻¹, B.mul_mem (B.mul_mem hgB hkB) (B.inv_mem hgB), ?_, ?_⟩
    · rw [mem_conjByElt]
      simpa [mul_assoc] using hk
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← map_mul, ← map_inv, ← map_mul]
      rfl
  · rintro ⟨k, hkB, hk, rfl⟩
    rw [mem_conjByElt] at hk
    have hk' : g⁻¹ * k * g ∈ B := B.mul_mem (B.mul_mem (B.inv_mem hgB) hkB) hgB
    refine ⟨QuotientGroup.mk' (N.subgroupOf B) ⟨g⁻¹ * k * g, hk'⟩, mk_mem_star hk' hk, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    ext
    simp [mul_assoc]

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

variable {B₀ : Subgroup G}

theorem centralizer_star_Y (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] :
    Subgroup.centralizer ((star (X ⊔ T ⊔ D) B₀ (conjClosure X D) :
      Subgroup (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D))) :
        Set (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D))) = ⊥ := by
  have hconjB₀ : ∀ {g : G}, g ∈ X ⊔ T ⊔ D → ∀ {b : G}, b ∈ B₀ → g * b * g⁻¹ ∈ B₀ :=
    fun hg b hb => (Subgroup.mem_normalizer_iff.mp (hB.nor hg) b).mp hb
  have hYn : ∀ {g : G}, g ∈ X ⊔ T ⊔ D → ∀ {y : G}, y ∈ conjClosure X D →
      g * y * g⁻¹ ∈ conjClosure X D :=
    fun hg y hy => (Subgroup.mem_normalizer_iff.mp (H.hBY hg) y).mp hy
  let C : Subgroup G :=
    { carrier := {k | k ∈ X ⊔ T ⊔ D ∧ ∀ y ∈ conjClosure X D, ⁅k, y⁆ ∈ B₀}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(X ⊔ T ⊔ D).mul_mem ha hb, fun y hy => ?_⟩
        have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact B₀.mul_mem (hconjB₀ ha (hb' y hy)) (ha' y hy)
      one_mem' := ⟨(X ⊔ T ⊔ D).one_mem, fun y _ => by
        rw [commutatorElement_one_left]; exact B₀.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨(X ⊔ T ⊔ D).inv_mem ha, fun y hy => ?_⟩
        have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact hconjB₀ ((X ⊔ T ⊔ D).inv_mem ha) (B₀.inv_mem (ha' y hy)) }
  have hCB : C ≤ X ⊔ T ⊔ D := fun k hk => hk.1
  have hB₀C : B₀ ≤ C := fun b hb => ⟨hB.le hb, fun y hy => by
    have e : ⁅b, y⁆ = b * (y * b⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact B₀.mul_mem hb (hconjB₀ (Y_le_B hy) (B₀.inv_mem hb))⟩
  have hCn : X ⊔ T ⊔ D ≤ Subgroup.normalizer (C : Set G) :=
    Main3324.le_normalizer_of_conj fun g hg k hk =>
      ⟨(X ⊔ T ⊔ D).mul_mem ((X ⊔ T ⊔ D).mul_mem hg hk.1) ((X ⊔ T ⊔ D).inv_mem hg),
        fun y hy => by
          have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ conjClosure X D := hYn ((X ⊔ T ⊔ D).inv_mem hg) hy
          have e : ⁅g * k * g⁻¹, y⁆ = g * ⁅k, g⁻¹ * y * g⁻¹⁻¹⁆ * g⁻¹ := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact hconjB₀ hg (hk.2 _ hy')⟩
  have hCB₀ : C ≤ B₀ := by
    by_contra hcon
    have hlt : B₀ < C := lt_of_le_of_ne hB₀C fun h => hcon (le_of_eq h.symm)
    have hYC := (H.X_le_of_normal hCn (hB.max C hlt hCB hCn)).2
    apply H.not_abel hA hB
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (hYC ha).2 b hb
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨⟨c, hc⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
  rw [Subgroup.mem_bot]
  refine (mk_eq_one_iff hc).mpr (hCB₀ ⟨hc, fun y hy => ?_⟩)
  have h1 := Subgroup.mem_centralizer_iff.mp hq _ (mk_mem_star (Y_le_B hy) hy)
  exact (mk_comm_iff hc (Y_le_B hy)).mp h1.symm

theorem isStronglyQuasithin_star (hA21 : AsA21SQTKSection) (hB : IsB₀ X T D B₀)
    (hY : conjClosure X D ≤ ⁅conjClosure X D, conjClosure X D⁆ ⊔ B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] {K : Subgroup G} (hK : K ∈ cComp (X ⊔ T ⊔ D))
    (hBK : X ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G)) (hKB₀ : ¬ K ≤ B₀) :
    CFSG.IsStronglyQuasithin ↥(star (X ⊔ T ⊔ D) B₀ K) := by
  obtain ⟨hsimp, hnab⟩ := H.isSimpleGroup_star hB hY hK hBK hKB₀
  have hBsq := H.isSQTKCat_B
  have hSQ : SQTKGroup ↥(X ⊔ T ⊔ D) :=
    ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mp hBsq.1, hBsq.2⟩
  let π : ↥(K.subgroupOf (X ⊔ T ⊔ D)) →* ↥(star (X ⊔ T ⊔ D) B₀ K) :=
    (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D))).subgroupMap (K.subgroupOf (X ⊔ T ⊔ D))
  have hπ : Function.Surjective π := MonoidHom.subgroupMap_surjective _ _
  have hq : CFSG.IsQuasisimple ↥(⊤ : Subgroup ↥(star (X ⊔ T ⊔ D) B₀ K)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  have hlayer : CFSG.layer ↥(⊤ : Subgroup ↥(star (X ⊔ T ⊔ D) B₀ K)) = ⊤ :=
    eq_top_iff.mpr (le_sSup (⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq,
      Subgroup.IsSubnormal.top⟩ :
        CFSG.IsComponent (⊤ : Subgroup ↥(⊤ : Subgroup ↥(star (X ⊔ T ⊔ D) B₀ K)))))
  have h2 : IsPGroup 2 (↥(star (X ⊔ T ⊔ D) B₀ K) ⧸
      (⊤ : Subgroup ↥(star (X ⊔ T ⊔ D) B₀ K))) :=
    fun q => ⟨0, by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [pow_zero, pow_one, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_top x⟩
  exact CFSG.SectionRank.isStronglyQuasithin_iff.mpr
    (hA21 ↥(X ⊔ T ⊔ D) hSQ (K.subgroupOf (X ⊔ T ⊔ D)) ↥(star (X ⊔ T ⊔ D) B₀ K) π hπ ⊤ hlayer
      h2).1

theorem isSylowTwoOf_star_T [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] :
    IsSylowTwoOf (star (X ⊔ T ⊔ D) B₀ T) ⊤ := by
  have hTB : T ≤ X ⊔ T ⊔ D := le_sup_right.trans le_sup_left
  have hT2 : IsPGroup 2 ↥(T.subgroupOf (X ⊔ T ⊔ D)) :=
    H.h.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTB).symm
  refine ⟨le_top, hT2.map _, fun h2 => H.isSylowTwoOf_B.2.2 ?_⟩
  have h1 := Subgroup.index_map_dvd (H := T.subgroupOf (X ⊔ T ⊔ D))
    (QuotientGroup.mk'_surjective (B₀.subgroupOf (X ⊔ T ⊔ D)))
  have h4 : 2 ∣ (star (X ⊔ T ⊔ D) B₀ T).index := by
    rw [← Subgroup.relIndex_top_right]
    exact h2
  exact h4.trans h1

theorem isoS3_star (hB : IsB₀ X T D B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] :
    Nonempty (↥(star (X ⊔ T ⊔ D) B₀ (X ⊔ T)) ⧸ CFSG.pCore 2 ↥(star (X ⊔ T ⊔ D) B₀ (X ⊔ T)) ≃*
      Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXTB : X ⊔ T ≤ X ⊔ T ⊔ D := le_sup_left
  let ψ : ↥(X ⊔ T) →* ↥(star (X ⊔ T ⊔ D) B₀ (X ⊔ T)) :=
    { toFun := fun x => ⟨QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨x, hXTB x.2⟩,
        mk_mem_star (hXTB x.2) x.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul (QuotientGroup.mk' _)
        (⟨a, hXTB a.2⟩ : ↥(X ⊔ T ⊔ D)) ⟨b, hXTB b.2⟩) }
  have hψs : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    obtain ⟨k, hkB, hk, rfl⟩ := mem_star_iff.mp hq
    exact ⟨⟨k, hk⟩, rfl⟩
  have hR2 : IsPGroup 2 ↥((pCoreOf 2 (X ⊔ T)).subgroupOf (X ⊔ T)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ T)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).symm
  have hker : IsPGroup 2 ↥ψ.ker := hR2.to_le fun k hk => by
    rw [Subgroup.mem_subgroupOf]
    have h1 : QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨k, hXTB k.2⟩ = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
    exact hB.inf ⟨k.2, (mk_eq_one_iff (hXTB k.2)).mp h1⟩
  obtain ⟨e⟩ := H.isoS3_open
  obtain ⟨e'⟩ := gold_isoS3_of_surjective_kernel ψ hψs hker e
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open _ 2)).trans e'⟩

theorem star_ne (hB : IsB₀ X T D B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] {g : G} (hg : g ∈ D)
    (hgR : g ∉ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G)) :
    star (X ⊔ T ⊔ D) B₀ (X ⊔ T) ≠ star (X ⊔ T ⊔ D) B₀ (conjByElt g (X ⊔ T)) := by
  intro heq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXTB : X ⊔ T ≤ X ⊔ T ⊔ D := le_sup_left
  have hG₂B : conjByElt g (X ⊔ T) ≤ X ⊔ T ⊔ D := conj_le_B hg
  have hle : ∀ {K K' : Subgroup G}, K ≤ X ⊔ T ⊔ D → K' ≤ X ⊔ T ⊔ D →
      star (X ⊔ T ⊔ D) B₀ K ≤ star (X ⊔ T ⊔ D) B₀ K' → K ≤ K' ⊔ B₀ := by
    intro K K' hK hK' h k hk
    obtain ⟨k', hk'B, hk', e⟩ := mem_star_iff.mp (h (mk_mem_star (hK hk) hk))
    have hb : k'⁻¹ * k ∈ B₀ := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf] at e
      exact e
    have e' : k = k' * (k'⁻¹ * k) := by group
    rw [e']
    exact Subgroup.mul_mem_sup hk' hb
  have h21 := hle hG₂B hXTB heq.symm.le
  have h12 := hle hXTB hG₂B heq.le
  have hRT := H.R_le_T
  have hR'T : conjByElt g (pCoreOf 2 (X ⊔ T)) ≤ T :=
    (Subgroup.map_mono hRT).trans (le_of_eq (H.conjByElt_T hg))
  have hR'G₂ : conjByElt g (pCoreOf 2 (X ⊔ T)) ≤ conjByElt g (X ⊔ T) := by
    rw [← pCoreOf_conj]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hR'n : conjByElt g (pCoreOf 2 (X ⊔ T)) ≤ Subgroup.normalizer (B₀ : Set G) :=
    (hR'G₂.trans hG₂B).trans hB.nor
  have hG₂nR' : conjByElt g (X ⊔ T) ≤
      Subgroup.normalizer (conjByElt g (pCoreOf 2 (X ⊔ T)) : Set G) := by
    rw [← pCoreOf_conj]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hG₁n : X ⊔ T ≤ Subgroup.normalizer
      ((conjByElt g (pCoreOf 2 (X ⊔ T)) ⊔ B₀ : Subgroup G) : Set G) := by
    intro x hx
    have hx' := h12 hx
    rw [sup_comm] at hx'
    obtain ⟨b, hb, y, hy, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer (hG₂B.trans hB.nor)).mp hx'
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer (Subgroup.mem_sup_right hb))
      (ChiefCount.mem_normalizer_sup (hG₂nR' hy) (hB.nor (hG₂B hy)))
  have hN₀n : X ⊔ T ≤ Subgroup.normalizer
      (((X ⊔ T) ⊓ (conjByElt g (pCoreOf 2 (X ⊔ T)) ⊔ B₀) : Subgroup G) : Set G) :=
    fun x hx => ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hx) (hG₁n hx)
  have hR'2 : IsPGroup 2 ↥(conjByElt g (pCoreOf 2 (X ⊔ T))) := H.h.sylow.1.to_le hR'T
  have hN₀2 : IsPGroup 2 ↥((X ⊔ T) ⊓ (conjByElt g (pCoreOf 2 (X ⊔ T)) ⊔ B₀)) := by
    rintro ⟨n, hnXT, hn⟩
    rw [sup_comm] at hn
    obtain ⟨b, hb, r, hr, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hR'n).mp hn
    obtain ⟨k, hk⟩ := hR'2 ⟨r, hr⟩
    have hk' : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨c, hc, ec⟩ := pow_mul_mem hb (hR'n hr) (2 ^ k)
    rw [hk', mul_one] at ec
    have hcXT : c ∈ X ⊔ T := ec ▸ (X ⊔ T).pow_mem hnXT _
    have hcT : c ∈ T := hRT (hB.inf ⟨hcXT, hc⟩)
    obtain ⟨m, hm⟩ := H.h.sylow.1 ⟨c, hcT⟩
    have hm' : c ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    refine ⟨k + m, Subtype.ext ?_⟩
    show (b * r) ^ 2 ^ (k + m) = 1
    rw [pow_add, pow_mul, ec, hm']
  have hN₀R : (X ⊔ T) ⊓ (conjByElt g (pCoreOf 2 (X ⊔ T)) ⊔ B₀) ≤ pCoreOf 2 (X ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hN₀n hN₀2
  have hR'R : conjByElt g (pCoreOf 2 (X ⊔ T)) ≤ pCoreOf 2 (X ⊔ T) := by
    intro r hr
    have hr' := h21 (hR'G₂ hr)
    rw [sup_comm] at hr'
    obtain ⟨b, hb, x, hx, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer (hXTB.trans hB.nor)).mp hr'
    have hxN : x ∈ (X ⊔ T) ⊓ (conjByElt g (pCoreOf 2 (X ⊔ T)) ⊔ B₀) := by
      refine ⟨hx, ?_⟩
      have e : x = b⁻¹ * (b * x) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (B₀.inv_mem hb)) (Subgroup.mem_sup_left hr)
    have hxR := hN₀R hxN
    have hbT : b ∈ T := by
      have e : b = (b * x) * x⁻¹ := by group
      rw [e]
      exact T.mul_mem (hR'T hr) (T.inv_mem (hRT hxR))
    exact (pCoreOf 2 (X ⊔ T)).mul_mem (hB.inf ⟨Subgroup.mem_sup_right hbT, hb⟩) hxR
  apply hgR
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hR'R (card_conjByElt g _).symm.le

theorem iInf_le_B₀ (hB : IsB₀ X T D B₀)
    (hX : ∀ d ∈ D, X ≤ Subgroup.normalizer
      ((pCoreOf 2 (X ⊔ T) ⊓ conjByElt d (pCoreOf 2 (X ⊔ T)) : Subgroup G) : Set G)) :
    (⨅ d : ↥D, conjByElt (d : G) (pCoreOf 2 (X ⊔ T))) ≤ B₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRT := H.R_le_T
  have hmem : ∀ {r : G}, r ∈ (⨅ d : ↥D, conjByElt (d : G) (pCoreOf 2 (X ⊔ T))) ↔
      ∀ d ∈ D, r ∈ conjByElt d (pCoreOf 2 (X ⊔ T)) := by
    intro r
    rw [Subgroup.mem_iInf]
    exact ⟨fun h d hd => h ⟨d, hd⟩, fun h d => h d d.2⟩
  have hRD : (⨅ d : ↥D, conjByElt (d : G) (pCoreOf 2 (X ⊔ T))) ≤ pCoreOf 2 (X ⊔ T) := by
    intro r hr
    have h1 := hmem.mp hr 1 D.one_mem
    rw [mem_conjByElt] at h1
    simpa using h1
  have hRD2 := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ T)).to_le hRD
  have hXn : X ≤ Subgroup.normalizer
      ((⨅ d : ↥D, conjByElt (d : G) (pCoreOf 2 (X ⊔ T)) : Subgroup G) : Set G) :=
    Main3324.le_normalizer_of_conj fun x hx r hr => hmem.mpr fun d hd => by
      have h1 : r ∈ pCoreOf 2 (X ⊔ T) ⊓ conjByElt d (pCoreOf 2 (X ⊔ T)) :=
        ⟨hRD hr, hmem.mp hr d hd⟩
      exact ((Subgroup.mem_normalizer_iff.mp (hX d hd hx) r).mp h1).2
  have hTR : T ≤ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G) :=
    le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hTn : T ≤ Subgroup.normalizer
      ((⨅ d : ↥D, conjByElt (d : G) (pCoreOf 2 (X ⊔ T)) : Subgroup G) : Set G) :=
    Main3324.le_normalizer_of_conj fun t ht r hr => hmem.mpr fun d hd =>
      (Subgroup.mem_normalizer_iff.mp (H.T_le_normalizer_conj hTR hd ht) r).mp (hmem.mp hr d hd)
  have hDn : D ≤ Subgroup.normalizer
      ((⨅ d : ↥D, conjByElt (d : G) (pCoreOf 2 (X ⊔ T)) : Subgroup G) : Set G) :=
    Main3324.le_normalizer_of_conj fun d' hd' r hr => hmem.mpr fun d hd => by
      have h1 := hmem.mp hr (d'⁻¹ * d) (D.mul_mem (D.inv_mem hd') hd)
      rw [mem_conjByElt] at h1 ⊢
      have e : d⁻¹ * (d' * r * d'⁻¹) * d = (d'⁻¹ * d)⁻¹ * r * (d'⁻¹ * d) := by group
      rw [e]
      exact h1
  have hTB : T ≤ X ⊔ T ⊔ D := le_sup_right.trans le_sup_left
  have hO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (hRD.trans (hRT.trans hTB)) (sup_le (sup_le hXn hTn) hDn) hRD2
  obtain ⟨-, hT₀, -⟩ := H.T₀_eq hB.le hB.nor hB.inf hB.max
  exact hO.trans ((le_of_eq hT₀.symm).trans inf_le_right)

theorem comm_mem_iInf {t t' : G} (ht : t ∈ T) (ht' : t' ∈ T) :
    ⁅t, t'⁆ ∈ ⨅ d : ↥D, conjByElt (d : G) (pCoreOf 2 (X ⊔ T)) := by
  rw [Subgroup.mem_iInf]
  intro d
  exact comm_mem_of_relIndex_two (H.relIndex_conj_R d.2) ht ht'

theorem exists_not_caseTwo (hIW : InspWalter3320) (hA21 : AsA21SQTKSection)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (hA : AS_A_1_31) (hB : IsB₀ X T D B₀) :
    ∃ g ∈ D, g ∉ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G) ∧
      ¬ F6.IsF618CaseTwo (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g)) := by
  by_contra hcon
  push Not at hcon
  have hN : (B₀.subgroupOf (X ⊔ T ⊔ D)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hB.nor
  have hX : ∀ d ∈ D, X ≤ Subgroup.normalizer
      ((pCoreOf 2 (X ⊔ T) ⊓ conjByElt d (pCoreOf 2 (X ⊔ T)) : Subgroup G) : Set G) := by
    intro d hd
    by_cases hdR : d ∈ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G)
    · have h1 : conjByElt d (pCoreOf 2 (X ⊔ T)) = pCoreOf 2 (X ⊔ T) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hdR
      rw [h1, inf_idem]
      exact le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    · rw [← H.pCoreOf_eq_of_caseTwo hd hdR (hcon d hd hdR)]
      exact (le_sup_left.trans le_sup_left).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hcomm : ∀ t ∈ T, ∀ t' ∈ T, ⁅t, t'⁆ ∈ B₀ := fun t ht t' ht' =>
    H.iInf_le_B₀ hB hX (H.comm_mem_iInf ht ht')
  have hY := H.le_commutator_sup hA hB
  obtain ⟨K, hK, hKB₀⟩ := H.exists_cComp_not_le h39 hB hY
  have hBK := H.le_normalizer_of_T_le h37 h38 hK
    (H.T_le_normalizer_of_comm h37 h38 hB hY hcomm hK hKB₀)
  have hsimp := H.isSimpleGroup_star hB hY hK hBK hKB₀
  have hsq := H.isStronglyQuasithin_star hA21 hB hY hK hBK hKB₀
  rw [H.star_eq_star_Y hB hK hBK hKB₀] at hsimp hsq
  obtain ⟨hsimp, hnab⟩ := hsimp
  obtain ⟨g, hg, hgR⟩ := Set.not_subset.mp H.hD
  have hgB : g ∈ X ⊔ T ⊔ D := Subgroup.mem_sup_right hg
  have hSab : ∀ a ∈ star (X ⊔ T ⊔ D) B₀ T, ∀ b ∈ star (X ⊔ T ⊔ D) B₀ T, a * b = b * a := by
    intro a ha b hb
    obtain ⟨t, htB, ht, rfl⟩ := mem_star_iff.mp ha
    obtain ⟨t', htB', ht', rfl⟩ := mem_star_iff.mp hb
    exact (mk_comm_iff htB htB').mpr (hcomm t ht t' ht')
  have hW := hIW _ (star (X ⊔ T ⊔ D) B₀ (conjClosure X D)) (star (X ⊔ T ⊔ D) B₀ T)
    (star (X ⊔ T ⊔ D) B₀ (X ⊔ T)) (star_normal H.hBY) hsimp hnab (H.centralizer_star_Y hA hB)
    hsq H.isSylowTwoOf_star_T hSab (star_mono le_sup_right) (H.isoS3_star hB) _
    (mk_mem_normalizer_star hgB (H.h.DN hg))
  rw [star_conj hgB] at hW
  have htop := hW (H.star_ne hB hg hgR).symm
  rw [← star_sup le_sup_left (conj_le_B hg)] at htop
  have hsolv := H.isSolvable_gZero_of_caseTwo hg hgR (hcon g hg hgR)
  apply H.not_isSolvable_star_Y hB hY
  have h1 := isSolvable_star (N := B₀) (gZero_le hg) hsolv
  rw [htop] at h1
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective le_top)

end Hyp3320

end S3320

end CFSG.Quasithin.H13

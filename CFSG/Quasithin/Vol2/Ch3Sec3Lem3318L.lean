module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318K
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318G
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318J

public section

namespace CFSG.Quasithin.H13.L3318

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq map_perfectCore_comap)
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Data

variable {T M L D : Subgroup G} {α : ↥L →* SpecialLinearGroup (Fin 4) (ZMod 2)}
  {Φ : (Fin 1 → Multiplicative (Fin 4 → ZMod 2)) →* ↥(vPlus L T)}

theorem isQ1_of_mem (hD : Data G T M L D 4 1 α Φ) {y : G}
    (hy : y ∈ liftCore α (flagStabilizer 4 (ZMod 2) {1})) :
    IsQ1 ((α ⟨y, liftCore_le α _ hy⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  have hP0 := perfectCore_le _ (mem_perfectCore_of_mem_liftCore hD.surj hy)
  have hP : α ⟨y, liftCore_le α _ hy⟩ ∈ stabilizer (flagSpace 4 (ZMod 2) 1) := by
    rw [← flagStabilizer_singleton]
    exact hP0
  rw [stabilizer_one_iff (Nat.card_zmod 2) (by norm_num)] at hP
  refine ⟨?_, fun i => ?_⟩
  · have := hP 0
    simpa using this
  · have := hP i.succ
    simpa [Fin.succ_ne_zero] using this

theorem exists_levi_one' (hD : Data G T M L D 4 1 α Φ) :
    ∃ ψ : ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1})) →* SpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective ψ ∧
      ψ.ker = CFSG.pCore 2 ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1})) ∧
      ∀ y : ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1})),
        ((ψ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          blk ((α ⟨y, liftCore_le α _ y.2⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  obtain ⟨ψ, hs, hk, he⟩ := hD.exists_levi_one
  exact ⟨ψ, hs, hk, fun y => by rw [he]; exact blkAt_eq_blk _ _⟩

theorem isRad1_of_ker (hD : Data G T M L D 4 1 α Φ)
    {ψ : ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1})) →* SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hψe : ∀ y : ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1})),
      ((ψ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        blk ((α ⟨y, liftCore_le α _ y.2⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)))
    {x : ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1}))} (hx : ψ x = 1) :
    IsRad1 ((α ⟨x, liftCore_le α _ x.2⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  refine ⟨hD.isQ1_of_mem x.2, fun i j => ?_⟩
  have h := congrFun (congrFun (hψe x) i) j
  rw [hx, Matrix.SpecialLinearGroup.coe_one, blk_apply, Matrix.one_apply] at h
  exact h.symm

theorem rowOf_conj (hD : Data G T M L D 4 1 α Φ)
    {ψ : ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1})) →* SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hψe : ∀ y : ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1})),
      ((ψ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        blk ((α ⟨y, liftCore_le α _ y.2⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (y : ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1})))
    {x : ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1}))} (hx : ψ x = 1) :
    rowOf ((α ⟨(y * x * y⁻¹ : ↥(liftCore α _)), liftCore_le α _ (y * x * y⁻¹).2⟩ :
        SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      CFSG.RankThree.FFModules.dualMat (ψ y) *ᵥ
        rowOf ((α ⟨x, liftCore_le α _ x.2⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  set αY := α.comp (Subgroup.inclusion (liftCore_le α (flagStabilizer 4 (ZMod 2) {1})))
    with hαY
  have hx' : ψ (y * x * y⁻¹) = 1 := by rw [map_mul, map_mul, hx, mul_one, map_inv, mul_inv_cancel]
  have hcomm : ((αY (y * x * y⁻¹) : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) * ((αY y : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      ((αY y : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
        ((αY x : SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul,
      ← map_mul, inv_mul_cancel_right]
  have h1 := vecMul_rowOf (hD.isQ1_of_mem y.2) (hD.isRad1_of_ker hψe hx)
    (hD.isRad1_of_ker hψe hx') hcomm
  rw [← hψe] at h1
  exact eq_dualMat h1

theorem false_of_case2
    (hD : Data G T M L D 4 1 α Φ) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h12 : Step3_3_12R)
    (hQW : c134Q (liftCore α (flagStabilizer 4 (ZMod 2) {3}) ⊔ T)
      (liftCore α (flagStabilizer 4 (ZMod 2) {3})) ⊓ pCoreOf 2 L = W₃ Φ) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψs, hψk, hψe⟩ := hD.exists_levi_one'
  have hred := Hyp331.vPlus_reduced hD.hyp.toSetup331
  have hVT : vPlus L T ≤ T := (hred.1.trans inf_le_left).trans
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hD.hyp.toSetup331.isSylowTwoOf)
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hWV : ⁅vPlus L T, L⁆ ≤ vPlus L T := Ch3Sec3.commutator_le_left_of_le_normalizer hLV
  have hcommV : ∀ a ∈ vPlus L T, ∀ b ∈ vPlus L T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hred.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hLnorm : (L.subgroupOf (L ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hD.TL)
  have hOY₂ : pCoreOf 2 L ≤ pCoreOf 2 (liftCore α (flagStabilizer 4 (ZMod 2) {3}) ⊔ T) :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T)
      le_sup_left hLnorm).trans (hD.pCoreOf_le_pCoreOf (liftCore_le α _))
  have hY₂W : ⁅pCoreOf 2 L, liftCore α (flagStabilizer 4 (ZMod 2) {3})⁆ ≤ ⁅vPlus L T, L⁆ := by
    have h1 : ⁅pCoreOf 2 L, liftCore α (flagStabilizer 4 (ZMod 2) {3})⁆ ≤
        c134Q (liftCore α (flagStabilizer 4 (ZMod 2) {3}) ⊔ T)
          (liftCore α (flagStabilizer 4 (ZMod 2) {3})) :=
      Subgroup.commutator_mono hOY₂ le_rfl
    have h2 : ⁅pCoreOf 2 L, liftCore α (flagStabilizer 4 (ZMod 2) {3})⁆ ≤ pCoreOf 2 L :=
      Ch3Sec3.commutator_le_left_of_le_normalizer
        ((liftCore_le α _).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))
    exact (le_inf h1 h2).trans (hQW.le.trans hD.W₃_le_commV)
  have hY₁W := hD.le_C hY₂W
  have htype : L3312.Type3312R (↥(liftCore α (flagStabilizer 4 (ZMod 2) {1})) ⧸
      CFSG.pCore 2 ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1}))) :=
    Or.inr (Or.inl (isPSL_of_hom le_rfl hψs hψk))
  have hDY : D ≤ Subgroup.normalizer (liftCore α (flagStabilizer 4 (ZMod 2) {1}) : Set G) := by
    obtain ⟨-, -, -, -, h | ⟨hpsl, -⟩⟩ := h12 G T M L D _ hD.hyp hD.mem_lFamilyOf_one
      hD.pCoreOf_ne_bot_one htype
    · exact h
    · exact absurd hpsl (not_isPSL_two_two le_rfl (by norm_num) hψs hψk)
  have hmemY : ∀ {d : G}, d ∈ D → ∀ {y : G}, y ∈ liftCore α (flagStabilizer 4 (ZMod 2) {1}) →
      d * y * d⁻¹ ∈ liftCore α (flagStabilizer 4 (ZMod 2) {1}) := fun hd y hy =>
    (Subgroup.mem_normalizer_iff.mp (hDY hd) y).mp hy
  have hS₀ : IsSylowTwoOf (T ⊓ liftCore α (flagStabilizer 4 (ZMod 2) {1}))
      (liftCore α (flagStabilizer 4 (ZMod 2) {1})) :=
    A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo hD.hyp.sylow le_sup_right)
      le_sup_left (sup_le Subgroup.le_normalizer (hD.le_normalizer_Y {1}))
  have hU : ((T ⊓ liftCore α (flagStabilizer 4 (ZMod 2) {1})).subgroupOf
      (liftCore α (flagStabilizer 4 (ZMod 2) {1}))).map ψ = unitriangular 3 (ZMod 2) := by
    obtain ⟨g, hg⟩ := exists_conj_unitriangular hS₀ (K := ZMod 2) (by norm_num) hψs
    have hle : ((T ⊓ liftCore α (flagStabilizer 4 (ZMod 2) {1})).subgroupOf
        (liftCore α (flagStabilizer 4 (ZMod 2) {1}))).map ψ ≤ unitriangular 3 (ZMod 2) := by
      rintro _ ⟨t, ht, rfl⟩
      have ht' := Subgroup.mem_subgroupOf.mp ht
      have hu : α ⟨t, liftCore_le α _ t.2⟩ ∈ unitriangular 4 (ZMod 2) := by
        rw [← hD.mapU]
        exact ⟨⟨t, liftCore_le α _ t.2⟩, Subgroup.mem_subgroupOf.mpr ⟨ht'.1,
          liftCore_le α _ t.2⟩, rfl⟩
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · rw [hψe, blk_apply]
        exact hu.1 _ _ (Fin.succ_lt_succ_iff.mpr hij)
      · rw [hψe, blk_apply]
        exact hu.2 _
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [← hg, ← Subgroup.map_map, Subgroup.card_map_of_injective (MulEquiv.injective _)]
  have hclaim : ∀ {d : G} (hd : d ∈ D) (y : ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1}))),
      ψ ⟨d * y * d⁻¹, hmemY hd y.2⟩ = ψ y := by
    intro d hd y
    obtain ⟨θ, hθ⟩ := L3316.exists_inducedAut hψs hψk (hDY hd)
    have hθU : ∀ u ∈ unitriangular 3 (ZMod 2), θ u ∈ unitriangular 3 (ZMod 2) := by
      intro u hu
      rw [← hU] at hu ⊢
      obtain ⟨t, ht, rfl⟩ := hu
      rw [hθ]
      have ht' := Subgroup.mem_subgroupOf.mp ht
      refine ⟨⟨d * t * d⁻¹, _⟩, Subgroup.mem_subgroupOf.mpr ⟨?_, hmemY hd t.2⟩, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hD.hyp.DN hd) _).mp ht'.1
    have hθpow : ∀ (j : ℕ) (l : ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1}))),
        (θ ^ j) (ψ l) = ψ ⟨d ^ j * l * (d ^ j)⁻¹, (Subgroup.mem_normalizer_iff.mp
          (Subgroup.pow_mem _ (hDY hd) j) l).mp l.2⟩ := by
      intro j
      induction j with
      | zero =>
        intro l
        simp only [pow_zero, MulAut.one_apply, one_mul, inv_one, mul_one]
      | succ j ih =>
        intro l
        rw [pow_succ', MulAut.mul_apply, ih, hθ]
        congr 1
        apply Subtype.ext
        simp only [pow_succ', _root_.mul_inv_rev]
        group
    have hodd : Odd (orderOf d) := by
      have h1 : orderOf (⟨d, hd⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hD.hyp.Dodd h1
    have hθm : θ ^ orderOf d = 1 := by
      refine MulEquiv.ext fun u => ?_
      obtain ⟨l, rfl⟩ := hψs u
      rw [hθpow, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      simp [pow_orderOf_eq_one]
    have h1 := eq_one_of_mulAut_odd (Nat.card_zmod 2) θ hθU hodd hθm
    rw [← hθ, h1, MulAut.one_apply]
  have hWT : ⁅vPlus L T, L⁆ ≤ T := hWV.trans hVT
  have hWY : ⁅vPlus L T, L⁆ ≤ liftCore α (flagStabilizer 4 (ZMod 2) {1}) :=
    hD.commV_le_commutator.trans (Ch3Sec3.commutator_le_right_of_le_normalizer
      (hWT.trans (hD.le_normalizer_Y {1})))
  have hWP : ⁅vPlus L T, L⁆ ≤ pCoreOf 2 (liftCore α (flagStabilizer 4 (ZMod 2) {1})) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWY
      ((liftCore_le α _).trans hD.le_normalizer_commV) (hD.hyp.sylow.1.to_le hWT)
  have hPker : ∀ {x : G} (hx : x ∈ pCoreOf 2 (liftCore α (flagStabilizer 4 (ZMod 2) {1}))),
      ψ ⟨x, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx⟩ = 1 := by
    intro x hx
    have : (⟨x, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx⟩ :
        ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1}))) ∈ ψ.ker := by
      rw [hψk]
      exact (Lem3328.mem_pCore_iff _).mpr hx
    exact this
  have hdP : ∀ {d : G}, d ∈ D → ∀ {x : G},
      x ∈ pCoreOf 2 (liftCore α (flagStabilizer 4 (ZMod 2) {1})) →
      d * x * d⁻¹ ∈ pCoreOf 2 (liftCore α (flagStabilizer 4 (ZMod 2) {1})) := fun hd x hx =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf
      2 _ (hDY hd)) x).mp hx
  have hPL : pCoreOf 2 (liftCore α (flagStabilizer 4 (ZMod 2) {1})) ≤ L :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (liftCore_le α _)
  have hO : ∀ {x : G} (hx : x ∈ pCoreOf 2 (liftCore α (flagStabilizer 4 (ZMod 2) {1}))),
      rowOf ((α ⟨x, hPL hx⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) = 0 → x ∈ pCoreOf 2 L := by
    intro x hx h0
    have h1 := eq_one_of_rowOf (hD.isRad1_of_ker hψe (hPker hx)) h0
    have h2 : α ⟨x, hPL hx⟩ = 1 := Subtype.ext h1
    have h3 : (⟨x, hPL hx⟩ : ↥L) ∈ α.ker := h2
    rw [hD.ker] at h3
    exact (Lem3328.mem_pCore_iff _).mp h3
  have hrow0 : ∀ {x : G} (hx : x ∈ pCoreOf 2 (liftCore α (flagStabilizer 4 (ZMod 2) {1}))),
      (∀ y ∈ liftCore α (flagStabilizer 4 (ZMod 2) {1}), y * x * y⁻¹ = x) →
      rowOf ((α ⟨x, hPL hx⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) = 0 := by
    intro x hx hfix
    apply MSY.fixed_eq_zero
    intro h
    obtain ⟨g, hg⟩ := exists_dualMat_eq h
    obtain ⟨y, hy⟩ := hψs g
    have h1 := hD.rowOf_conj hψe y (x := ⟨x, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx⟩)
      (hPker hx)
    have hα : α ⟨((y * ⟨x, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx⟩ * y⁻¹ :
        ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1}))) : G), liftCore_le α _
          (y * ⟨x, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx⟩ * y⁻¹).2⟩ =
        α ⟨x, hPL hx⟩ := by
      congr 1
      exact Subtype.ext (hfix y y.2)
    rw [hα, hy, hg] at h1
    exact h1.symm
  have hWd : ∀ {d : G}, d ∈ D →
      (⁅vPlus L T, L⁆).map (MulAut.conj d).toMonoidHom ≤ ⁅vPlus L T, L⁆ := by
    intro d hd
    let zc : ZMod 2 → (Fin 1 → Multiplicative (Fin 4 → ZMod 2)) :=
      fun c _ => Multiplicative.ofAdd (Fin.cons c 0)
    let wa : (Fin 3 → ZMod 2) → (Fin 1 → Multiplicative (Fin 4 → ZMod 2)) :=
      fun a _ => Multiplicative.ofAdd (Fin.cons 0 a)
    have hzP : ∀ c, d * (Φ (zc c) : G) * d⁻¹ ∈
        pCoreOf 2 (liftCore α (flagStabilizer 4 (ZMod 2) {1})) := fun c =>
      hdP hd (hWP (hD.mem_commV _))
    have hwP : ∀ a, d * (Φ (wa a) : G) * d⁻¹ ∈
        pCoreOf 2 (liftCore α (flagStabilizer 4 (ZMod 2) {1})) := fun a =>
      hdP hd (hWP (hD.mem_commV _))
    have hz0 : ∀ c, rowOf ((α ⟨_, hPL (hzP c)⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) = 0 := by
      intro c
      refine hrow0 (hzP c) fun y hy => ?_
      have hy' : d⁻¹ * y * d⁻¹⁻¹ ∈ liftCore α (flagStabilizer 4 (ZMod 2) {1}) :=
        hmemY (D.inv_mem hd) hy
      have h1 := (hD.comm_iff ⟨_, liftCore_le α _ hy'⟩ (zc c)).mpr fun _ =>
        mulVec_cons_zero (hD.isQ1_of_mem hy') c
      simp only [inv_inv] at h1
      calc y * (d * (Φ (zc c) : G) * d⁻¹) * y⁻¹ =
            d * ((d⁻¹ * y * d) * (Φ (zc c) : G) * (d⁻¹ * y * d)⁻¹) * d⁻¹ := by group
        _ = d * (Φ (zc c) : G) * d⁻¹ := by rw [h1]
    have hwmul : ∀ a a', wa (a + a') = wa a * wa a' := fun a a' => by
      funext i
      apply Multiplicative.toAdd.injective
      simp only [wa, Pi.mul_apply, toAdd_mul, toAdd_ofAdd]
      rw [cons_add_cons, add_zero]
    have hw0 : wa 0 = 1 := by
      funext i
      apply Multiplicative.toAdd.injective
      simp only [wa, toAdd_ofAdd, Pi.one_apply, toAdd_one]
      funext s
      refine Fin.cases ?_ (fun s => ?_) s <;> simp
    let ε : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) :=
      { toFun := fun a => rowOf ((α ⟨_, hPL (hwP a)⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2))
        map_zero' := by
          have h1 : (⟨d * (Φ (wa 0) : G) * d⁻¹, hPL (hwP 0)⟩ : ↥L) = 1 :=
            Subtype.ext (by simp [hw0])
          show rowOf ((α ⟨d * (Φ (wa 0) : G) * d⁻¹, hPL (hwP 0)⟩ :
            SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 0
          rw [h1, map_one, Matrix.SpecialLinearGroup.coe_one]
          funext j
          simp [rowOf, (Fin.succ_ne_zero j).symm]
        map_add' := fun a a' => by
          have h1 : (⟨d * (Φ (wa (a + a')) : G) * d⁻¹, hPL (hwP (a + a'))⟩ : ↥L) =
              ⟨d * (Φ (wa a) : G) * d⁻¹, hPL (hwP a)⟩ *
                ⟨d * (Φ (wa a') : G) * d⁻¹, hPL (hwP a')⟩ :=
            Subtype.ext (by
              show d * (Φ (wa (a + a')) : G) * d⁻¹ =
                (d * (Φ (wa a) : G) * d⁻¹) * (d * (Φ (wa a') : G) * d⁻¹)
              rw [hwmul, map_mul, Subgroup.coe_mul]
              group)
          show rowOf ((α ⟨d * (Φ (wa (a + a')) : G) * d⁻¹, hPL (hwP (a + a'))⟩ :
            SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = _
          rw [h1, map_mul, Matrix.SpecialLinearGroup.coe_mul]
          exact rowOf_mul (hD.isRad1_of_ker hψe (hPker (hwP a)))
            (hD.isRad1_of_ker hψe (hPker (hwP a'))) }
    have hε : ∀ (g : SpecialLinearGroup (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2),
        ε (g *ᵥ v) = CFSG.RankThree.FFModules.dualMat g *ᵥ ε v := by
      intro g a
      obtain ⟨y, rfl⟩ := hψs g
      have hyw : (y : G) * (Φ (wa a) : G) * (y : G)⁻¹ = (Φ (wa ((ψ y :
          SpecialLinearGroup (Fin 3) (ZMod 2)) *ᵥ a)) : G) * (Φ (zc (rowOf ((α ⟨y,
          liftCore_le α _ y.2⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)) ⬝ᵥ a)) : G) := by
        have : (y : G) * (Φ (wa a) : G) * (y : G)⁻¹ =
            (Φ (vecAct 1 ((α ⟨y, liftCore_le α _ y.2⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
              Matrix (Fin 4) (Fin 4) (ZMod 2)) (wa a)) : G) :=
          hD.equiv ⟨y, liftCore_le α _ y.2⟩ (wa a)
        rw [this, ← Subgroup.coe_mul, ← map_mul]
        congr 2
        funext i
        apply Multiplicative.toAdd.injective
        simp only [vecAct_apply, wa, zc, toAdd_ofAdd, Pi.mul_apply, toAdd_mul]
        rw [mulVec_cons, cons_add_cons, zero_add, add_zero, hψe]
      set y' : ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1})) :=
        ⟨d * y * d⁻¹, hmemY hd y.2⟩ with hy'
      set x' : ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1})) :=
        ⟨d * (Φ (wa a) : G) * d⁻¹, CFSG.LieType.BorelTits.pCoreOf_le 2 _ (hwP a)⟩ with hx'
      have h1 := hD.rowOf_conj hψe y' (x := x') (hPker (hwP a))
      rw [hy', hclaim hd y] at h1
      have h2 : ((y' * x' * y'⁻¹ : ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1}))) : G) =
          (d * (Φ (wa ((ψ y : SpecialLinearGroup (Fin 3) (ZMod 2)) *ᵥ a)) : G) * d⁻¹) *
            (d * (Φ (zc (rowOf ((α ⟨y, liftCore_le α _ y.2⟩ :
              SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) ⬝ᵥ a)) :
                G) * d⁻¹) := by
        simp only [hy', hx', Subgroup.coe_mul, Subgroup.coe_inv]
        calc d * y * d⁻¹ * (d * (Φ (wa a) : G) * d⁻¹) * (d * y * d⁻¹)⁻¹ =
              d * ((y : G) * (Φ (wa a) : G) * (y : G)⁻¹) * d⁻¹ := by group
          _ = _ := by rw [hyw]; group
      have hα : α ⟨((y' * x' * y'⁻¹ : ↥(liftCore α (flagStabilizer 4 (ZMod 2) {1}))) : G),
          liftCore_le α _ (y' * x' * y'⁻¹).2⟩ =
          α ⟨_, hPL (hwP ((ψ y : SpecialLinearGroup (Fin 3) (ZMod 2)) *ᵥ a))⟩ *
            α ⟨_, hPL (hzP (rowOf ((α ⟨y, liftCore_le α _ y.2⟩ :
              SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) ⬝ᵥ a))⟩ := by
        rw [← map_mul]
        congr 1
        exact Subtype.ext h2
      rw [hα, Matrix.SpecialLinearGroup.coe_mul,
        rowOf_mul (hD.isRad1_of_ker hψe (hPker (hwP _))) (hD.isRad1_of_ker hψe (hPker (hzP _))),
        hz0, add_zero] at h1
      exact h1
    have hε0 := eq_zero_of_nat_dual ε hε
    set S := (pCoreOf 2 L).comap ((MulAut.conj d).toMonoidHom.comp
      ((vPlus L T).subtype.comp Φ)) with hSdef
    have hS : S = ⊤ := by
      refine eq_top_of_mulSingle_mem S fun i t => ?_
      have hi : Pi.mulSingle i (Multiplicative.ofAdd (Pi.single t (1 : ZMod 2) : Fin 4 → ZMod 2)) =
          fun _ => Multiplicative.ofAdd (Pi.single t (1 : ZMod 2) : Fin 4 → ZMod 2) := by
        funext j
        rw [Subsingleton.elim j i, Pi.mulSingle_eq_same]
      show d * (Φ _ : G) * d⁻¹ ∈ pCoreOf 2 L
      rw [hi]
      refine Fin.cases ?_ (fun j => ?_) t
      · have : (fun _ : Fin 1 => Multiplicative.ofAdd
            (Pi.single (0 : Fin 4) (1 : ZMod 2) : Fin 4 → ZMod 2)) = zc 1 := by
          funext i
          apply Multiplicative.toAdd.injective
          simp only [zc, toAdd_ofAdd]
          funext s
          refine Fin.cases ?_ (fun s => ?_) s <;> simp [Fin.succ_ne_zero]
        rw [this]
        exact hO (hzP 1) (hz0 1)
      · have : (fun _ : Fin 1 => Multiplicative.ofAdd
            (Pi.single j.succ (1 : ZMod 2) : Fin 4 → ZMod 2)) = wa (Pi.single j 1) := by
          funext i
          apply Multiplicative.toAdd.injective
          simp only [wa, toAdd_ofAdd]
          funext s
          refine Fin.cases ?_ (fun s => ?_) s
          · simp [(Fin.succ_ne_zero j).symm]
          · by_cases hs : s = j
            · subst hs
              simp
            · simp [hs, Fin.succ_inj]
        rw [this]
        refine hO (hwP _) ?_
        have := congrArg (fun f : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) => f (Pi.single j 1)) hε0
        exact this
    have hWdO : (⁅vPlus L T, L⁆).map (MulAut.conj d).toMonoidHom ≤ pCoreOf 2 L := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := hD.exists_eq hy
      have : c ∈ S := hS ▸ Subgroup.mem_top c
      exact this
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (MulAut.conj d).toMonoidHom x ∈
        (⁅⁅vPlus L T, L⁆, liftCore α (flagStabilizer 4 (ZMod 2) {1})⁆).map
          (MulAut.conj d).toMonoidHom := ⟨x, hD.commV_le_commutator hx, rfl⟩
    have hY : (liftCore α (flagStabilizer 4 (ZMod 2) {1})).map (MulAut.conj d).toMonoidHom =
        liftCore α (flagStabilizer 4 (ZMod 2) {1}) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hDY hd)
    rw [Subgroup.map_commutator, hY] at h1
    exact hY₁W (Subgroup.commutator_mono hWdO le_rfl h1)
  have hDN : D ≤ Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) := fun d hd =>
    Ch1Sec3.mem_normalizer_of_map_conj_le (hWd hd) (hWd (D.inv_mem hd))
  have hW1 : ⁅vPlus L T, L⁆ ≠ ⊥ := by
    intro hbot
    have h1 := hD.mem_commV
      (Pi.mulSingle 0 (Multiplicative.ofAdd (Pi.single (0 : Fin 4) (1 : ZMod 2))))
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : Φ (Pi.mulSingle 0 (Multiplicative.ofAdd (Pi.single (0 : Fin 4) (1 : ZMod 2)))) = 1 :=
      Subtype.ext h1
    have h3 := hD.inj (h2.trans (map_one Φ).symm)
    have h4 := congrFun (congrArg Multiplicative.toAdd (congrFun h3 0)) 0
    simp at h4
  have hN : L ⊔ T ≤ Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) :=
    sup_le hD.le_normalizer_commV fun t ht =>
      Ch1Sec3.commutator_le_normalizer (Hyp331.le_normalizer_vPlus L T ht) (hD.TL ht)
  exact Hyp331.not_le_normalizer hD.hyp h38 h39 hW1 (hD.commV_le.trans le_sup_left) hN hDN

end Data

end CFSG.Quasithin.H13.L3318

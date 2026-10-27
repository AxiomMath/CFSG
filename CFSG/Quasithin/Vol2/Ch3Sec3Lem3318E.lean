module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318D
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318C
public import CFSG.Quasithin.Vol2.Ch3Sec3Ln2C

public section

namespace CFSG.Quasithin.H13.L3318

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftCore_eq map_perfectCore_comap)
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem seven_dvd_card_sl {m : ℕ} (hm3 : 3 ≤ m) (hm4 : m ≤ 4) :
    7 ∣ Nat.card (SpecialLinearGroup (Fin m) (ZMod 2)) := by
  have hq : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  interval_cases m
  · rw [Matrix.card_SL_field, hq]
    decide
  · rw [Matrix.card_SL_field, hq]
    decide

omit [Finite G] in
theorem isPSL_of_hom {Y : Subgroup G} {m : ℕ} (hm : 3 ≤ m)
    {f : ↥Y →* SpecialLinearGroup (Fin m) (ZMod 2)} (hf : Function.Surjective f)
    (hk : f.ker = CFSG.pCore 2 ↥Y) : IsPSL m 2 1 (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  refine ⟨⟨Nat.prime_two, le_rfl, by omega, fun h => ?_, fun h => ?_⟩, ZMod 2, inferInstance,
    inferInstance, by rw [Nat.card_zmod]; norm_num, ⟨?_⟩⟩
  · have := congrArg Prod.fst h
    simp only at this
    omega
  · have := congrArg Prod.fst h
    simp only at this
    omega
  · exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective f hf).trans
        (slEquivStatedProj (Nat.card_zmod 2) m))

omit [Finite G] in
theorem not_isPSL_two_two {Y : Subgroup G} {m : ℕ} (hm3 : 3 ≤ m) (hm4 : m ≤ 4)
    {f : ↥Y →* SpecialLinearGroup (Fin m) (ZMod 2)} (hf : Function.Surjective f)
    (hk : f.ker = CFSG.pCore 2 ↥Y) : ¬ IsPSL 2 2 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  rintro ⟨-, K, _, _, hK, ⟨e⟩⟩
  have h1 : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = Nat.card (SpecialLinearGroup (Fin m) (ZMod 2)) :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)).toEquiv
  have h2 : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ∣ 60 := by
    rw [Nat.card_congr e.toEquiv]
    refine (Subgroup.card_quotient_dvd_card _).trans ?_
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    norm_num
  have h3 := seven_dvd_card_sl hm3 hm4
  rw [← h1] at h3
  have := h3.trans h2
  omega

namespace Data

variable {T M L D : Subgroup G} {n k : ℕ} {α : ↥L →* SpecialLinearGroup (Fin n) (ZMod 2)}
  {Φ : (Fin k → Multiplicative (Fin n → ZMod 2)) →* ↥(vPlus L T)}

theorem n_pos (hD : Data G T M L D n k α Φ) : 0 < n := by
  have := hD.n4
  omega

@[expose] def c₀ (hD : Data G T M L D n k α Φ) : Fin k → Multiplicative (Fin n → ZMod 2) :=
  Pi.mulSingle ⟨0, hD.k1⟩ (Multiplicative.ofAdd (Pi.single ⟨0, hD.n_pos⟩ 1))

theorem mulVec_eq_of_col (hD : Data G T M L D n k α Φ) {A : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hA : ∀ r : Fin n, A r ⟨0, hD.n_pos⟩ = if (r : ℕ) = 0 then 1 else 0) {v : Fin n → ZMod 2}
    (hv : ∀ j : Fin n, (j : ℕ) ≠ 0 → v j = 0) : A *ᵥ v = v := by
  funext r
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single ⟨0, hD.n_pos⟩]
  · rw [hA r]
    by_cases hr : (r : ℕ) = 0
    · rw [ite_eq_left hr, one_mul, show r = ⟨0, hD.n_pos⟩ from Fin.ext hr]
    · rw [ite_eq_right hr, zero_mul, hv r hr]
  · intro j _ hj
    rw [hv j (fun h => hj (Fin.ext h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem inf_centralizer_eq (hD : Data G T M L D n k α Φ) :
    L ⊓ Subgroup.centralizer
        ((⁅vPlus L T, L⁆ ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) : Subgroup G) :
          Set G) =
      liftPre α (stabilizer (flagSpace n (ZMod 2) 1)) := by
  set X := ⁅vPlus L T, L⁆ ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) with hX
  have hcomm : ∀ (g y : G), g * y * g⁻¹ = y ↔ g * y = y * g := fun g y => by
    constructor
    · intro h
      calc g * y = g * y * g⁻¹ * g := by group
        _ = y * g := by rw [h]
    · intro h
      rw [h, mul_inv_cancel_right]
  have hfix : ∀ c, (Φ c : G) ∈ X ↔ ∀ t ∈ T ⊓ L, t * (Φ c : G) * t⁻¹ = (Φ c : G) := by
    intro c
    refine ⟨fun h t ht => (hcomm _ _).mpr (Subgroup.mem_centralizer_iff.mp h.2 t ht),
      fun h => ⟨hD.mem_commV c, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩⟩
    exact (hcomm _ _).mp (h t ht)
  apply le_antisymm
  · rintro x ⟨hxL, hxC⟩
    refine ⟨⟨x, hxL⟩, ?_, rfl⟩
    show α ⟨x, hxL⟩ ∈ stabilizer (flagSpace n (ZMod 2) 1)
    rw [stabilizer_one_iff (Nat.card_zmod 2) hD.n_pos]
    have hc₀ : (Φ hD.c₀ : G) ∈ X := by
      rw [hfix]
      intro t ht
      refine (hD.comm_iff ⟨t, ht.2⟩ hD.c₀).mpr fun i => ?_
      by_cases hi : i = ⟨0, hD.k1⟩
      · subst hi
        rw [c₀, Pi.mulSingle_eq_same, toAdd_ofAdd]
        refine hD.mulVec_eq_of_col (hD.col_zero_of_mem ht.1) fun j hj => ?_
        rw [Pi.single_apply, ite_eq_right (fun h => hj (by rw [h]))]
      · rw [c₀, Pi.mulSingle_eq_of_ne hi, toAdd_one, Matrix.mulVec_zero]
    have h1 := (hcomm x (Φ hD.c₀ : G)).mpr (Subgroup.mem_centralizer_iff.mp hxC _ hc₀).symm
    have h2 := (hD.comm_iff ⟨x, hxL⟩ hD.c₀).mp h1 ⟨0, hD.k1⟩
    rw [c₀, Pi.mulSingle_eq_same, toAdd_ofAdd] at h2
    intro r
    have h3 := congrFun h2 r
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h3
    rw [h3, Pi.single_apply]
    by_cases hr : (r : ℕ) = 0
    · rw [ite_eq_left (Fin.ext hr), ite_eq_left hr]
    · rw [ite_eq_right (fun h => hr (by rw [h])), ite_eq_right hr]
  · rintro _ ⟨l, hl, rfl⟩
    refine ⟨l.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨c, rfl⟩ := hD.exists_eq hy.1
    have hcT := (hfix c).mp hy
    have hl' : α l ∈ stabilizer (flagSpace n (ZMod 2) 1) := hl
    rw [stabilizer_one_iff (Nat.card_zmod 2) hD.n_pos] at hl'
    have h1 : (l : G) * (Φ c : G) * (l : G)⁻¹ = (Φ c : G) :=
      (hD.comm_iff l c).mpr fun i => hD.mulVec_eq_of_col hl' fun j hj => hD.coord_eq_zero hcT i j hj
    exact ((hcomm _ _).mp h1).symm

theorem le_normalizer_liftPre (hD : Data G T M L D n k α Φ) (I : Set ℕ) :
    T ≤ Subgroup.normalizer (liftPre α (flagStabilizer n (ZMod 2) I) : Set G) := by
  have hT1 : T ≤ Subgroup.normalizer (liftPre α (stabilizer (flagSpace n (ZMod 2) 1)) : Set G) := by
    rw [← hD.inf_centralizer_eq]
    intro t ht
    have hTV := Hyp331.le_normalizer_vPlus L T
    have hTTL : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer ht) (hD.TL ht)
    refine ChiefCount.mem_normalizer_inf (hD.TL ht)
      (normalizer_le_normalizer_centralizer _ (ChiefCount.mem_normalizer_inf
        (Ch1Sec3.commutator_le_normalizer (hTV ht) (hD.TL ht))
        (normalizer_le_normalizer_centralizer _ hTTL)))
  have hk : α.ker = CFSG.pCore 2 ↥L := hD.ker
  exact Ln2.le_normalizer_liftPre hD.TL (Nat.card_zmod 2) (by have := hD.n4; omega) hD.surj hk
    hD.mapU hT1 I

theorem le_centralizer (hD : Data G T M L D n k α Φ) :
    liftCore α (flagStabilizer n (ZMod 2) {1}) ≤
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  set Z := quasithinOmegaOneCenter T with hZ
  have hZT : Z ≤ T := (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_left
  have hZC : Z ≤ Subgroup.centralizer (T : Set G) :=
    (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_right
  have hY₁ : liftCore α (flagStabilizer n (ZMod 2) {1}) ≤
      L ⊓ Subgroup.centralizer
        ((⁅vPlus L T, L⁆ ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) : Subgroup G) :
          Set G) := by
    rw [hD.inf_centralizer_eq, ← flagStabilizer_singleton]
    exact perfectCore_le _
  obtain ⟨-, hdec⟩ := hD.hyp.vPlus_decomp
  rw [Hyp331.mPlus_eq_of_le hD.TL] at hdec
  have hZV : Z ≤ (Z ⊓ Subgroup.centralizer (L : Set G)) ⊔ ⁅vPlus L T, L⁆ := by
    intro z hz
    have hzV : z ∈ vPlus L T := le_conjClosure _ _ hz
    rw [hdec] at hzV
    exact (sup_comm (⁅vPlus L T, L⁆) _ ▸ hzV)
  have hN : Z ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) := fun z hz =>
    Ch1Sec3.commutator_le_normalizer (Hyp331.le_normalizer_vPlus L T (hZT hz.1))
      (Subgroup.centralizer_le_normalizer _ hz.2)
  have hZle : Z ≤ (Z ⊓ Subgroup.centralizer (L : Set G)) ⊔ (Z ⊓ ⁅vPlus L T, L⁆) :=
    (le_inf le_rfl hZV).trans (ChiefCount.inf_sup_le inf_le_left hN)
  intro y hy
  have hyC := (hY₁ hy).2
  have hyL : y ∈ L := (hY₁ hy).1
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzC : z ∈ Subgroup.centralizer ({y} : Set G) := by
    refine hZle.trans (sup_le ?_ ?_) hz
    · intro w hw
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hw.2 y hyL).symm)
    · intro w hw
      have hwX : w ∈ ⁅vPlus L T, L⁆ ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
        ⟨hw.2, Subgroup.centralizer_le inf_le_left (hZC hw.1)⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hyC w hwX))
  exact Subgroup.mem_centralizer_singleton_iff.mp hzC

theorem isPGroup_ker (hD : Data G T M L D n k α Φ) : IsPGroup 2 ↥α.ker := by
  rw [hD.ker]
  exact CFSG.pCore_isPGroup

theorem mem_lFamilyOf_one (hD : Data G T M L D n k α Φ) :
    liftCore α (flagStabilizer n (ZMod 2) {1}) ∈ lFamilyOf L T := by
  have hn := hD.n4
  have hno : ∀ c ∈ ({1} : Set ℕ), ¬ (1 < c ∧ c < 1 + (n - 1)) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    omega
  exact Ln2.liftCore_mem_lFamilyOf hD.hyp.sylow hD.hyp.toSetup331.pCoreOf_ne_bot
    (Nat.card_zmod 2) hD.n5 hD.surj hD.ker (I := {1}) (a := 1) (m := n - 1) (by omega)
    (by omega) (Or.inr rfl) (Or.inl (by omega)) hno (hD.le_normalizer_liftPre {1})

theorem mem_lFamilyOf_three (hD : Data G T M L D n k α Φ) :
    liftCore α (flagStabilizer n (ZMod 2) {3}) ∈ lFamilyOf L T := by
  have hn := hD.n4
  have hno : ∀ c ∈ ({3} : Set ℕ), ¬ (0 < c ∧ c < 0 + 3) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    omega
  exact Ln2.liftCore_mem_lFamilyOf hD.hyp.sylow hD.hyp.toSetup331.pCoreOf_ne_bot
    (Nat.card_zmod 2) hD.n5 hD.surj hD.ker (I := {3}) (a := 0) (m := 3) (by omega) le_rfl
    (Or.inl rfl) (Or.inr rfl) hno (hD.le_normalizer_liftPre {3})

theorem sup_eq (hD : Data G T M L D n k α Φ) :
    L ⊔ T = liftCore α (flagStabilizer n (ZMod 2) {1}) ⊔
      liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T := by
  have hkT : α.ker.map L.subtype ≤ T := by
    rw [hD.ker]
    intro x hx
    obtain ⟨l, hl, rfl⟩ := hx
    have h1 : (l : G) ∈ pCoreOf 2 L := (Lem3328.mem_pCore_iff l).mp hl
    have hS₀ : IsSylowTwoOf (T ⊓ L) L :=
      A4.isSylowTwoOf_inf_normal hD.hyp.toSetup331.isSylowTwoOf le_sup_left
        (sup_le Subgroup.le_normalizer hD.TL)
    exact ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS₀).trans inf_le_left) h1
  exact Ln2.sup_liftCore_eq (Nat.card_zmod 2) hD.n4 hD.n5 hD.surj hkT hD.mapU

theorem exists_levi_one (hD : Data G T M L D n k α Φ) :
    ∃ ψ : ↥(liftCore α (flagStabilizer n (ZMod 2) {1})) →*
        SpecialLinearGroup (Fin (n - 1)) (ZMod 2),
      Function.Surjective ψ ∧
      ψ.ker = CFSG.pCore 2 ↥(liftCore α (flagStabilizer n (ZMod 2) {1})) ∧
      ∀ y : ↥(liftCore α (flagStabilizer n (ZMod 2) {1})),
        ((ψ y : SpecialLinearGroup (Fin (n - 1)) (ZMod 2)) :
          Matrix (Fin (n - 1)) (Fin (n - 1)) (ZMod 2)) =
          blkAt 1 (n - 1) (by have := hD.n4; omega)
            ((α ⟨y, liftCore_le α _ y.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)) := by
  have hn := hD.n4
  have hno : ∀ c ∈ ({1} : Set ℕ), ¬ (1 < c ∧ c < 1 + (n - 1)) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    omega
  obtain ⟨ψ, hψs, hψk, hψe⟩ := exists_levi (Nat.card_zmod 2) hD.n5 hD.surj hD.isPGroup_ker
    (I := {1}) (a := 1) (m := n - 1) (by omega) (by omega) (Or.inr rfl) (Or.inl (by omega)) hno
  exact ⟨ψ, hψs, Ln2.ker_eq_pCore_of_hom (Nat.card_zmod 2) (by omega) hψs hψk, hψe⟩

theorem exists_levi_three (hD : Data G T M L D n k α Φ) :
    ∃ ψ : ↥(liftCore α (flagStabilizer n (ZMod 2) {3})) →* SpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective ψ ∧
      ψ.ker = CFSG.pCore 2 ↥(liftCore α (flagStabilizer n (ZMod 2) {3})) ∧
      ∀ y : ↥(liftCore α (flagStabilizer n (ZMod 2) {3})),
        ((ψ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          blkAt 0 3 (by have := hD.n4; omega)
            ((α ⟨y, liftCore_le α _ y.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)) := by
  have hn := hD.n4
  have hno : ∀ c ∈ ({3} : Set ℕ), ¬ (0 < c ∧ c < 0 + 3) := by
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    omega
  obtain ⟨ψ, hψs, hψk, hψe⟩ := exists_levi (Nat.card_zmod 2) hD.n5 hD.surj hD.isPGroup_ker
    (I := {3}) (a := 0) (m := 3) (by omega) le_rfl (Or.inl rfl) (Or.inr rfl) hno
  exact ⟨ψ, hψs, Ln2.ker_eq_pCore_of_hom (Nat.card_zmod 2) le_rfl hψs hψk, hψe⟩

theorem pCoreOf_ne_bot_one (hD : Data G T M L D n k α Φ) :
    pCoreOf 2 (liftCore α (flagStabilizer n (ZMod 2) {1}) ⊔ T ⊔ D) ≠ ⊥ := by
  set Z := quasithinOmegaOneCenter T with hZ
  have hZT : Z ≤ T := (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_left
  have hZ2 : IsPGroup 2 Z := hD.hyp.sylow.1.to_le hZT
  have hZ1 : Z ≠ ⊥ := Setup.omegaOneCenterOf_ne_bot hD.hyp.sylow.1 hD.hyp.toSetup331.T_ne_bot
  have hN : liftCore α (flagStabilizer n (ZMod 2) {1}) ⊔ T ⊔ D ≤
      Subgroup.normalizer (Z : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact hD.le_centralizer.trans (Subgroup.centralizer_le_normalizer _)
    · exact (CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T).trans
        (Subgroup.centralizer_le_normalizer _)
    · exact hD.hyp.DN.trans (Hyp331.normalizer_le_normalizer_of_characteristic hZT
        (CFSG.QuasithinUnique.L246C127.characteristic_omegaOneCenter T))
  have hle : Z ≤ pCoreOf 2 (liftCore α (flagStabilizer n (ZMod 2) {1}) ⊔ T ⊔ D) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (hZT.trans (le_sup_right.trans le_sup_left))
      hN hZ2
  intro hbot
  rw [hbot, le_bot_iff] at hle
  exact hZ1 hle

theorem false_of_pCoreOf_ne_bot (hD : Data G T M L D n k α Φ) (h15 : Step3_3_15R)
    (hO : pCoreOf 2 (liftCore α (flagStabilizer n (ZMod 2) {3}) ⊔ T ⊔ D) ≠ ⊥) : False := by
  have hn := hD.n4
  have hn5 := hD.n5
  obtain ⟨ψ₁, hψ₁s, hψ₁k, -⟩ := hD.exists_levi_one
  obtain ⟨ψ₂, hψ₂s, hψ₂k, -⟩ := hD.exists_levi_three
  have ht₁ : L3312.Type3312R (↥(liftCore α (flagStabilizer n (ZMod 2) {1})) ⧸
      CFSG.pCore 2 ↥(liftCore α (flagStabilizer n (ZMod 2) {1}))) := by
    have h := isPSL_of_hom (by omega) hψ₁s hψ₁k
    rcases (by omega : n - 1 = 3 ∨ n - 1 = 4) with h3 | h4
    · rw [h3] at h
      exact Or.inr (Or.inl h)
    · rw [h4] at h
      exact Or.inr (Or.inr h)
  have ht₂ : L3312.Type3312R (↥(liftCore α (flagStabilizer n (ZMod 2) {3})) ⧸
      CFSG.pCore 2 ↥(liftCore α (flagStabilizer n (ZMod 2) {3}))) :=
    Or.inr (Or.inl (isPSL_of_hom le_rfl hψ₂s hψ₂k))
  obtain ⟨Y, hY, -, hpsl, -⟩ := h15 G T M L D _ _ hD.hyp hD.mem_lFamilyOf_one
    hD.mem_lFamilyOf_three hD.sup_eq hD.pCoreOf_ne_bot_one hO ht₁ ht₂
  rcases hY with rfl | rfl
  · exact not_isPSL_two_two (by omega) (by omega) hψ₁s hψ₁k hpsl
  · exact not_isPSL_two_two le_rfl (by norm_num) hψ₂s hψ₂k hpsl

end Data

end CFSG.Quasithin.H13.L3318

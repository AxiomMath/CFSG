module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321D
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321Three
public import CFSG.Quasithin.Vol2.Ch3Sec3Ln2B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace L3321

variable {G : Type} [Group G]

theorem thetaOf_le_self (X : Subgroup G) : thetaOf X ≤ X :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem thetaOf_mono {X Y : Subgroup G} (h : X ≤ Y) : thetaOf X ≤ thetaOf Y :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem mem_normalizer_thetaOf {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (thetaOf X : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ x ∈ thetaOf X, g * x * g⁻¹ ∈ thetaOf X := by
    intro g hg x hx
    have h1 := L3322.map_thetaOf_le X (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    have h2 : X.map (MulAut.conj g).toMonoidHom = X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 hg
    rw [h2] at h1
    exact h1 ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

theorem mem_normalizer_centralizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ c ∈ Subgroup.centralizer (X : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      simpa using this
    have h1 := hc _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * x := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hc
  simpa [mul_assoc] using this

@[expose] def matU3 : Fin 3 → Matrix (Fin 4) (Fin 4) (ZMod 2)
  | 0 => !![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  | 1 => !![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  | 2 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1]

theorem det_matU3 : ∀ k, (matU3 k).det = 1 := by decide +kernel

@[expose] def elU3 (k : Fin 3) : SL4 := ⟨matU3 k, det_matU3 k⟩

theorem elU3_mem (k : Fin 3) : elU3 k ∈ FLc.Ut 4 := by
  have h1 : ∀ k : Fin 3, ∀ p : Fin 4 × Fin 4, p.2 < p.1 → matU3 k p.1 p.2 = 0 := by
    decide +kernel
  have h2 : ∀ k : Fin 3, ∀ i : Fin 4, matU3 k i i = 1 := by decide +kernel
  rw [mem_unitriangular]
  exact ⟨fun i j hij => h1 k (i, j) hij, fun i => h2 k i⟩

theorem reflection_mul_pow_one :
    (reflection 4 (ZMod 2) 1 (by norm_num) (by norm_num) * elU3 0) ^ 3 = 1 ∧
      reflection 4 (ZMod 2) 1 (by norm_num) (by norm_num) * elU3 0 ≠ 1 := by
  refine ⟨Subtype.ext (by decide +kernel), fun h => ?_⟩
  have := congrArg (fun A : SL4 => (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 0) h
  revert this
  decide +kernel

theorem reflection_mul_pow_two :
    (reflection 4 (ZMod 2) 2 (by norm_num) (by norm_num) * elU3 1) ^ 3 = 1 ∧
      reflection 4 (ZMod 2) 2 (by norm_num) (by norm_num) * elU3 1 ≠ 1 := by
  refine ⟨Subtype.ext (by decide +kernel), fun h => ?_⟩
  have := congrArg (fun A : SL4 => (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 1) h
  revert this
  decide +kernel

theorem reflection_mul_pow_three :
    (reflection 4 (ZMod 2) 3 (by norm_num) (by norm_num) * elU3 2) ^ 3 = 1 ∧
      reflection 4 (ZMod 2) 3 (by norm_num) (by norm_num) * elU3 2 ≠ 1 := by
  refine ⟨Subtype.ext (by decide +kernel), fun h => ?_⟩
  have := congrArg (fun A : SL4 => (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 2) h
  revert this
  decide +kernel

theorem exists_mul_orderOf_three (i : ℕ) (hi : FLc.IsNode 4 i) :
    ∃ u ∈ FLc.Ut 4, orderOf (reflection 4 (ZMod 2) i hi.1 hi.2 * u) = 3 := by
  obtain ⟨hi1, hi4⟩ := hi
  interval_cases i
  · exact ⟨elU3 0, elU3_mem 0,
      orderOf_eq_prime reflection_mul_pow_one.1 reflection_mul_pow_one.2⟩
  · exact ⟨elU3 1, elU3_mem 1,
      orderOf_eq_prime reflection_mul_pow_two.1 reflection_mul_pow_two.2⟩
  · exact ⟨elU3 2, elU3_mem 2,
      orderOf_eq_prime reflection_mul_pow_three.1 reflection_mul_pow_three.2⟩

theorem le_closure_sup (P : Subgroup SL4) (hP : FLc.Ut 4 ≤ P) :
    P ≤ Subgroup.closure {w | w ∈ P ∧ orderOf w = 3} ⊔ FLc.Ut 4 := by
  set H' := Subgroup.closure {w | w ∈ P ∧ orderOf w = 3} ⊔ FLc.Ut 4 with hH'
  have hU : FLc.Ut 4 ≤ H' := le_sup_right
  have hcuts : FLc.cuts H' ⊆ FLc.cuts P := by
    intro i hi
    obtain ⟨hi1, hin, hr⟩ := hi
    refine ⟨hi1, hin, fun hrP => hr ?_⟩
    obtain ⟨u, hu, hord⟩ := exists_mul_orderOf_three i ⟨hi1, hin⟩
    have hw : reflection 4 (ZMod 2) i hi1 hin * u ∈ P := P.mul_mem hrP (hP hu)
    have h1 : reflection 4 (ZMod 2) i hi1 hin * u ∈ H' :=
      Subgroup.mem_sup_left (Subgroup.subset_closure ⟨hw, hord⟩)
    have h2 := H'.mul_mem h1 (H'.inv_mem (hU hu))
    simpa using h2
  calc P = FLc.QI 4 (FLc.cuts P) := FLc.eq_QI_cuts hP
    _ ≤ FLc.QI 4 (FLc.cuts H') :=
      (FLc.QI_le_QI_iff fun j hj => FLc.isNode_of_mem_cuts hj).2 hcuts
    _ = H' := (FLc.eq_QI_cuts hU).symm

theorem le_thetaOf_sup {L T : Subgroup G} {α : ↥L →* SL4} (hαk : α.ker = CFSG.pCore 2 ↥L)
    (hU : ((T ⊓ L).subgroupOf L).map α = FLc.Ut 4)
    (hOT : (CFSG.pCore 2 ↥L).map L.subtype ≤ T) {X : Subgroup G} (hXL : X ≤ L)
    (hTX : T ⊓ L ≤ X) : X ≤ thetaOf X ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup SL4 := (X.subgroupOf L).map α with hP
  have hUP : FLc.Ut 4 ≤ P := by
    rw [← hU]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L hTX)
  set Y : Subgroup ↥L := (thetaOf X ⊔ (T ⊓ L)).subgroupOf L with hY
  have hle : Subgroup.closure {w | w ∈ P ∧ orderOf w = 3} ⊔ FLc.Ut 4 ≤ Y.map α := by
    refine sup_le ((Subgroup.closure_le _).2 ?_) ?_
    · rintro w ⟨⟨y, hyX, rfl⟩, hw3⟩
      have hw3' : α y ^ 3 = 1 := by rw [← hw3]; exact pow_orderOf_eq_one _
      have hy3 : y ^ 3 ∈ CFSG.pCore 2 ↥L := by
        rw [← hαk, MonoidHom.mem_ker, map_pow, hw3']
      obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hy3⟩
      have hj' : (y ^ 3) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      set y' := y ^ (4 ^ j) with hy'
      have h4 : 4 ^ j = 3 * (4 ^ j / 3) + 1 := by
        have h1 : 4 ^ j % 3 = 1 := by
          rw [Nat.pow_mod]
          norm_num
        omega
      have hαy' : α y' = α y := by
        rw [hy', map_pow, h4, pow_succ, pow_mul, hw3', one_pow, one_mul]
      have hy'3 : y' ^ 3 = 1 := by
        rw [hy', ← pow_mul, mul_comm, pow_mul, show 4 ^ j = 2 ^ j * 2 ^ j by
          rw [← mul_pow]; norm_num, pow_mul, hj', one_pow]
      have hy'1 : y' ≠ 1 := by
        intro h1
        rw [h1, map_one] at hαy'
        rw [← hαy', orderOf_one] at hw3
        exact absurd hw3 (by norm_num)
      have hy'o : orderOf (y' : G) = 3 := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_eq_prime hy'3 hy'1
      have hy'X : (y' : G) ∈ X := by
        rw [hy']
        exact X.pow_mem hyX _
      refine ⟨y', ?_, hαy'⟩
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨hy'X, hy'o⟩)
    · rw [← hU]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_right)
  intro x hx
  obtain ⟨z, hz, hzx⟩ := hle (le_closure_sup P hUP ⟨⟨x, hXL hx⟩, hx, rfl⟩)
  have hk : z⁻¹ * ⟨x, hXL hx⟩ ∈ CFSG.pCore 2 ↥L := by
    rw [← hαk, MonoidHom.mem_ker, map_mul, map_inv, hzx, inv_mul_cancel]
  have hkT : ((z⁻¹ * ⟨x, hXL hx⟩ : ↥L) : G) ∈ T := hOT ⟨_, hk, rfl⟩
  have e : x = (z : G) * ((z⁻¹ * ⟨x, hXL hx⟩ : ↥L) : G) := by simp
  rw [e]
  refine Subgroup.mul_mem _ ?_ (Subgroup.mem_sup_right hkT)
  have hz' : (z : G) ∈ thetaOf X ⊔ (T ⊓ L) := hz
  exact (sup_le_sup_left inf_le_left _ : thetaOf X ⊔ (T ⊓ L) ≤ thetaOf X ⊔ T) hz'

variable [Finite G]

theorem step3_3_21e_of (h5 : Stmt3_3_5) (h14 : Stmt3_3_14) (hGA : GriessAllModelsStatement)
    (hd : Step3_3_21d) : Step3_3_21e := by
  intro G _ _ T M L D h ⟨e⟩ hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  by_contra hne
  obtain ⟨⟨z, hzZ, hzL⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hz1 : z ≠ 1 := fun h1 => hz1' (Subtype.ext h1)
  have hz2 : IsPGroup 2 (Subgroup.zpowers (z : G)) := by
    have hzT : (z : G) ∈ T := L3317.omegaOneCenter_le T hzZ
    exact h.sylow.1.to_le ((Subgroup.zpowers_le).2 hzT)
  have hzc : ∀ g ∈ Subgroup.centralizer ({(z : G)} : Set G),
      g ∈ Subgroup.normalizer (Subgroup.zpowers (z : G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [MonoidHom.map_zpowers]
    congr 1
    show g * z * g⁻¹ = z
    rw [hg, mul_inv_cancel_right]
  have hzM : Subgroup.normalizer (Subgroup.zpowers (z : G) : Set G) ≤ M := by
    refine L3322.normalizer_le_M h5 h hML ?_ hz2 ?_
    · intro hb
      apply hz1
      have : (z : G) ∈ Subgroup.zpowers (z : G) := Subgroup.mem_zpowers _
      rw [hb, Subgroup.mem_bot] at this
      exact this
    · refine sup_le (fun l hl => hzc l ?_) (fun t ht => hzc t ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.1 hzL l hl
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := conj_omegaOneCenter ht hzZ
        calc t * z = (t * z * t⁻¹) * t := by group
          _ = z * t := by rw [h1]
  have hCM : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M := fun g hg =>
    hzM (hzc g (Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hg z hzZ).symm))
  obtain ⟨α₀, hα₀s, hα₀k, -⟩ := Ln2.exists_modO2Surj h hGA hTL (K := ZMod 2) (Nat.card_zmod 2)
    le_rfl (by norm_num) e
  obtain ⟨α, hαs, hαk, hαU⟩ := Ln2.exists_unitriangular (L3317.isSylowTwoOf_inf h hTL)
    (by norm_num) hα₀s hα₀k
  have hθ : thetaOf (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) =
      thetaOf (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) := by
    refine le_antisymm ((Subgroup.closure_le _).2 ?_) (thetaOf_mono inf_le_right)
    rintro x ⟨hx, hx3⟩
    have hxL : x ∈ L := mem_of_orderOf_three hαs hαk h.maxM.1 h.LM h.qtke.2.2 (hCM hx)
      (hMN (hCM hx)) hx3
    exact Subgroup.subset_closure ⟨⟨hxL, hx⟩, hx3⟩
  have hOT : (CFSG.pCore 2 ↥L).map L.subtype ≤ T := by
    have h1 := EscapingLocal.pCoreOf_le_of_isSylowTwoOf (L3317.isSylowTwoOf_inf h hTL)
    rw [← A7.pCoreOf_eq_map_cfsgPCore]
    exact h1.trans inf_le_left
  have hTX : T ⊓ L ≤ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    fun t ht => ⟨ht.2, CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T ht.1⟩
  have hsup : L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T =
      thetaOf (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T :=
    le_antisymm (sup_le (le_thetaOf_sup hαk hαU hOT inf_le_left hTX) le_sup_right)
      (sup_le_sup_right (thetaOf_le_self _) T)
  have hDR : D ≤ Subgroup.normalizer ((pCoreOf 2
      (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T)) : Set G) := by
    intro d hdD
    have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
    have hdZ : d ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
      A4.normalizer_le_normalizer_omegaOneCenterOf T hdT
    have hdC : d ∈ Subgroup.normalizer
        (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) : Set G) :=
      mem_normalizer_centralizer hdZ
    have hdθ := mem_normalizer_thetaOf hdC
    rw [hθ] at hdθ
    rw [hsup]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (L3312.mem_normalizer_sup' hdθ hdT)
  exact Hyp331.not_D_le h (hDR.trans (hd G T M L D h ⟨e⟩ hmod))

end L3321

end CFSG.Quasithin.H13

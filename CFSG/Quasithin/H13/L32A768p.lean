module

public import CFSG.Quasithin.H13.L32A768n
public import CFSG.Quasithin.H13.L32A768l
public import CFSG.Quasithin.H13.L32A767u
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Setup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.Quasithin.H13.U3L134

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType

section Generic

theorem map_subtype_normal_of_characteristic {Q : Type*} [Group Q] {N : Subgroup Q}
    (hN : N.Normal) (C : Subgroup ↥N) [hC : C.Characteristic] : (C.map N.subtype).Normal := by
  have := hN
  refine ⟨?_⟩
  rintro _ ⟨c, hc, rfl⟩ g
  let σ : MulAut ↥N := MulAut.conjNormal g
  have h1 : σ c ∈ C := by
    rw [← Subgroup.characteristic_iff_map_eq.mp hC σ]
    exact ⟨c, hc, rfl⟩
  exact ⟨σ c, h1, by simp [σ, MulAut.conjNormal_apply]⟩

theorem case34_data {X : Type} [Group X] [Finite X] (h : A36Case3 X ∨ A36Case4 X) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ ψ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p),
      Function.Surjective ψ ∧ ψ.ker = CFSG.fittingSubgroup X ∧
      CFSG.generalizedFitting X = CFSG.fittingSubgroup X ∧
      Nat.Coprime (Nat.card ↥(CFSG.fittingSubgroup X)) 6 := by
  rcases h with ⟨p, hp, hp3, hgF, ⟨eF⟩, ⟨-, ψ, hψs, hψk, -⟩⟩ | ⟨hgF, -, ⟨eS⟩, hprimes⟩
  · refine ⟨p, hp, hp3, ψ, hψs, hψk, hgF, ?_⟩
    have hcard : Nat.card ↥(CFSG.fittingSubgroup X) = p ^ 2 := by
      rw [Nat.card_congr (eF.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hcard]
    refine Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h6 => ?_)
    have := Nat.le_of_dvd (by norm_num) h6
    interval_cases p <;> (revert hp h6; decide)
  · refine ⟨5, Nat.prime_five, by norm_num, eS.toMonoidHom.comp (QuotientGroup.mk' _),
      eS.surjective.comp (QuotientGroup.mk'_surjective _), ?_, hgF, ?_⟩
    · ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    · have h2 : ¬ 2 ∣ Nat.card ↥(CFSG.fittingSubgroup X) := fun h2 => by
        rcases (hprimes 2 Nat.prime_two h2).1 with h | h | h <;> norm_num at h
      have h3 : ¬ 3 ∣ Nat.card ↥(CFSG.fittingSubgroup X) := fun h3 => by
        rcases (hprimes 3 Nat.prime_three h3).1 with h | h | h <;> norm_num at h
      rw [show (6 : ℕ) = 2 * 3 by norm_num]
      exact Nat.Coprime.mul_right
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2))
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))

theorem exists_sl2_ne_one {p : ℕ} [Fact p.Prime] :
    ∃ y : Matrix.SpecialLinearGroup (Fin 2) (ZMod p), y ≠ 1 := by
  refine ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, fun h => ?_⟩
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
    (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1) h
  simp at this

theorem fitting_ne_bot_of_sl2 {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (ψ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) (hψ : Function.Surjective ψ)
    (hgF : CFSG.generalizedFitting X = CFSG.fittingSubgroup X) :
    CFSG.fittingSubgroup X ≠ ⊥ := by
  intro hbot
  have hC := CFSG.centralizer_generalizedFitting_le X
  rw [hgF, hbot] at hC
  obtain ⟨y, hy⟩ := exists_sl2_ne_one (p := p)
  obtain ⟨x, rfl⟩ := hψ y
  apply hy
  have hx : x ∈ (⊥ : Subgroup X) := hC (by
    rw [Subgroup.coe_bot, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh, one_mul, mul_one])
  rw [Subgroup.mem_bot] at hx
  rw [hx, map_one]

theorem not_isQuasisimple_of_sl2 {I X : Type*} [Group I] [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (ρ : I →* X) (hρ : Function.Surjective ρ)
    (ψ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) (hψ : Function.Surjective ψ)
    (hψk : ψ.ker = CFSG.fittingSubgroup X)
    (hgF : CFSG.generalizedFitting X = CFSG.fittingSubgroup X) : ¬ CFSG.IsQuasisimple I := by
  intro hq
  obtain ⟨y₀, hy₀⟩ := exists_sl2_ne_one (p := p)
  obtain ⟨x₀, hx₀⟩ := hψ y₀
  obtain ⟨k₀, rfl⟩ := hρ x₀
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple (φ := ψ.comp ρ) hq
    ⟨k₀, by rw [MonoidHom.comp_apply, hx₀]; exact hy₀⟩
  have hFZ : CFSG.fittingSubgroup X ≤ Subgroup.center X := by
    intro f hf
    obtain ⟨k, rfl⟩ := hρ f
    have hk : k ∈ (ψ.comp ρ).ker := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hψk]
      exact hf
    have hkZ := Subgroup.mem_center_iff.mp (hker hk)
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨k', rfl⟩ := hρ x
    rw [← map_mul, ← map_mul, hkZ k']
  have hC := CFSG.centralizer_generalizedFitting_le X
  rw [hgF] at hC
  have htop : CFSG.fittingSubgroup X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    apply hC
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (Subgroup.mem_center_iff.mp (hFZ hf) x).symm
  apply hy₀
  rw [← hx₀, ← MonoidHom.mem_ker, hψk, htop]
  trivial

theorem exists_odd_order_preimage {A B : Type*} [Group A] [Finite A] [Group B] (f : A →* B)
    (a : A) (hodd : Odd (orderOf (f a))) : ∃ b : A, Odd (orderOf b) ∧ f b = f a := by
  obtain ⟨k, r, hr, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos a).ne'
  have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
  have hord : orderOf (a ^ 2 ^ k) = r := by
    rw [orderOf_pow' _ h2k, hk, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
  have hcop : Nat.Coprime (2 ^ k) (orderOf (f a)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  obtain ⟨j, hj⟩ := A4.mem_zpowers_pow_of_coprime hcop
  refine ⟨(a ^ 2 ^ k) ^ j, ?_, by rw [map_zpow, map_pow]; exact hj⟩
  refine (hord ▸ hr).of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]

theorem isSolvable_of_le_normalizer {G : Type*} [Group G] {A B : Subgroup G} (hAB : A ≤ B)
    [Group.IsSolvable ↥A] [(A.subgroupOf B).Normal] [Group.IsSolvable (↥B ⧸ A.subgroupOf B)] :
    Group.IsSolvable ↥B := by
  have : Group.IsSolvable ↥(A.subgroupOf B) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hAB).symm.toMonoidHom)
      (MulEquiv.surjective _)
  exact Group.isSolvable_of_ker_le_range (A.subgroupOf B).subtype
    (QuotientGroup.mk' (A.subgroupOf B)) (by
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end Generic

section Pre

variable {G : Type} [Group G]

theorem mem_pre2 {H : Subgroup G} {P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} {x : G} :
    x ∈ preimageModTwoCore H P ↔
      ∃ hx : x ∈ H, (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem pre2_le (H : Subgroup G) (P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
    preimageModTwoCore H P ≤ H := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem pCoreOf_le_pre2 (H : Subgroup G) (P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
    pCoreOf 2 H ≤ preimageModTwoCore H P := by
  intro x hx
  have hxH : x ∈ H := pCoreOf_le 2 H hx
  refine mem_pre2.mpr ⟨hxH, ?_⟩
  have h1 : (QuotientGroup.mk (⟨x, hxH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (C2Six.mem_pCore_two_iff.mpr hx)
  rw [h1]
  exact P.one_mem

theorem le_normalizer_pre2 (H : Subgroup G) {P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)}
    (hP : P.Normal) : H ≤ Subgroup.normalizer (preimageModTwoCore H P : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨hxH, hxP⟩ := mem_pre2.mp hx
    have h' : g * x * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg hxH) (H.inv_mem hg)
    refine mem_pre2.mpr ⟨h', ?_⟩
    have e : (⟨g * x * g⁻¹, h'⟩ : ↥H) = ⟨g, hg⟩ * ⟨x, hxH⟩ * (⟨g, hg⟩ : ↥H)⁻¹ := rfl
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hP.conj_mem _ hxP _
  · intro hx
    obtain ⟨hxH, hxP⟩ := mem_pre2.mp hx
    have hxH' : x ∈ H := by
      have := H.mul_mem (H.mul_mem (H.inv_mem hg) hxH) hg
      simpa [mul_assoc] using this
    refine mem_pre2.mpr ⟨hxH', ?_⟩
    have e : (⟨x, hxH'⟩ : ↥H) = (⟨g, hg⟩ : ↥H)⁻¹ * ⟨g * x * g⁻¹, hxH⟩ * (⟨g, hg⟩ : ↥H)⁻¹⁻¹ :=
      Subtype.ext (by simp [mul_assoc])
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hP.conj_mem _ hxP _

end Pre

section Main

variable {G : Type} [Group G]

omit [Group G] in
theorem eq_one_of_pow_two_pow_of_odd {M : Type*} [Monoid M] {x : M} {k : ℕ} (h2 : x ^ 2 ^ k = 1)
    (hodd : Odd (orderOf x)) : x = 1 := by
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h1 : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (dvd_refl (orderOf x))
    rwa [Nat.Coprime.gcd_eq_one hcop] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

omit [Group G] in
theorem eq_one_of_pow_two_pow_of_pow_three' {M : Type*} [Monoid M] {x : M} {k : ℕ}
    (h2 : x ^ 2 ^ k = 1) (h3 : x ^ 3 = 1) : x = 1 :=
  eq_one_of_pow_two_pow_of_odd h2 ((by decide : Odd 3).of_dvd_nat (orderOf_dvd_of_pow_eq_one h3))

theorem mem_normalizer_of_mem_centralizer {S : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (S : Set G)) : c ∈ Subgroup.normalizer (S : Set G) := by
  have key : ∀ d ∈ Subgroup.centralizer (S : Set G), ∀ y ∈ S, d * y * d⁻¹ = y :=
    fun d hd y hy => by rw [← Subgroup.mem_centralizer_iff.mp hd y hy, mul_inv_cancel_right]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [key c hc x hx]
    exact hx
  · intro hx
    have := key c⁻¹ (inv_mem hc) _ hx
    rw [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this
    rw [this]
    exact hx

variable [Finite G] {T L V : Subgroup G}

theorem lemma14_7_68_case34_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h13314 : A6.Stmt13_3_14) (h63 : Thm14_7_63)
    (h674 : Lemma14_7_67_four) : Lemma14_7_68_case34 := by
  intro G _ _ T L V h u hu hu1 hT hS I hI hIn hKI hne hcase _
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1334 : A6.Stmt13_3_4 := U3.stmt13_3_4_of h1332
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have hF : HypF98 T V L (fsuV1 T V) V (hz T V) :=
    Setting147.hypF98 ⟨h, h.isHzOne_hz h63⟩ (stmt13_3_2_two_of_stmt13_3_2 h1332) hMod h1222
  have C : Ctx764 G T L V := ⟨h, hMod, h63, hF, h1222, h1332, h1334⟩
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  obtain ⟨z, hzV1, hz1, hgen⟩ := exists_gen_of_card_two hV1
  obtain ⟨-, hHM⟩ := h674 G T L V h
  set Gu := Subgroup.centralizer ({u} : Set G) with hGu
  have hIG : I ≤ Gu := le_of_mem_cComp hI
  have hKG : kz T V ≤ Gu := hKI.trans hIG
  set X := modO2Image Gu I with hX
  obtain ⟨p, hp, hp3, ψ, hψs, hψk, hgF, hcop⟩ := case34_data hcase
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ρ, hρs, -⟩ := CFSG.Quasithin.exists_modO2_surjection hI
  have hq : ¬ CFSG.IsQuasisimple ↥I := not_isQuasisimple_of_sl2 ρ hρs ψ hψs hψk hgF
  have hC2 : CharTwo Gu := C.charTwo_centralizer h13314 hzV1 hz1 hgen hu hu1 hS hI hKI hq
  have hyp := C.hypC23_centralizer hHM hu hu1 hT
  set R := pCoreOf 2 (yU T V u) with hR
  have hRG : R ≤ Gu := hyp.radical.1
  have hRp : IsPGroup 2 R := pCoreOf_isPGroup 2 _
  have hR1 : R ≠ ⊥ := hyp.radical.2.1
  have hO2R : pCoreOf 2 Gu ≤ R := by
    have hn : ((pCoreOf 2 Gu).subgroupOf Gu).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 Gu)).mpr
        (le_normalizer_pCoreOf 2 Gu)
    have hOT := A4.le_of_normal_of_isSylowTwoOf hS (pCoreOf_le 2 Gu) hn (pCoreOf_isPGroup 2 Gu)
    exact le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right)
      ((yU_le_centralizer h hMod hu).trans (le_normalizer_pCoreOf 2 Gu)) (pCoreOf_isPGroup 2 Gu)
  have hXn : X.Normal := hIn.map _ (QuotientGroup.mk'_surjective _)
  set F := CFSG.fittingSubgroup ↥X with hFdef
  set F' : Subgroup (↥Gu ⧸ CFSG.pCore 2 ↥Gu) := F.map X.subtype with hF'
  have hF'n : F'.Normal := map_subtype_normal_of_characteristic hXn F
  have hF'card : Nat.card ↥F' = Nat.card ↥F :=
    Subgroup.card_map_of_injective X.subtype_injective
  have hF'ord : ∀ f ∈ F', Nat.Coprime (orderOf f) 6 := by
    intro f hf
    have h1 : orderOf (⟨f, hf⟩ : ↥F') ∣ Nat.card ↥F' := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hF'card] at h1
    exact Nat.Coprime.coprime_dvd_left h1 hcop
  set Y₀ := preimageModTwoCore Gu F' with hY₀
  have hY₀G : Y₀ ≤ Gu := pre2_le Gu F'
  have hOY : pCoreOf 2 Gu ≤ Y₀ := pCoreOf_le_pre2 Gu F'
  have hGN : Gu ≤ Subgroup.normalizer (Y₀ : Set G) := le_normalizer_pre2 Gu hF'n
  let g : ↥Y₀ →* ↥F' := ((QuotientGroup.mk' (CFSG.pCore 2 ↥Gu)).comp
    (Subgroup.inclusion hY₀G)).codRestrict F' (fun y => by
      obtain ⟨hy, hyF⟩ := mem_pre2.mp y.2
      exact hyF)
  have hg1 : ∀ y : ↥Y₀, g y = 1 ↔ (y : G) ∈ pCoreOf 2 Gu := by
    intro y
    have e : g y = 1 ↔ (QuotientGroup.mk (Subgroup.inclusion hY₀G y) :
        ↥Gu ⧸ CFSG.pCore 2 ↥Gu) = 1 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [e]
    exact (QuotientGroup.eq_one_iff _).trans C2Six.mem_pCore_two_iff
  have hgs : Function.Surjective g := by
    rintro ⟨f, hf⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Gu) f
    exact ⟨⟨x, mem_pre2.mpr ⟨x.2, hf⟩⟩, rfl⟩
  have hY₀3 : ∀ y ∈ Y₀, y ^ 3 = 1 → y = 1 := by
    intro y hy hy3
    have h1 : g ⟨y, hy⟩ = 1 := by
      have hcop' := hF'ord _ (g ⟨y, hy⟩).2
      have hd : orderOf (g ⟨y, hy⟩) ∣ 3 := orderOf_dvd_of_pow_eq_one (by
        rw [← map_pow]
        exact (congrArg g (Subtype.ext hy3 : (⟨y, hy⟩ : ↥Y₀) ^ 3 = 1)).trans (map_one g))
      have h3 : orderOf (g ⟨y, hy⟩) = 1 := by
        rw [← Subgroup.orderOf_coe] at hd ⊢
        exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right (by norm_num) hcop') hd
      exact orderOf_eq_one_iff.mp h3
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 Gu ⟨y, (hg1 _).mp h1⟩
    have h2 : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact eq_one_of_pow_two_pow_of_pow_three' h2 hy3
  have hRN : R ≤ Subgroup.normalizer (Y₀ : Set G) := hRG.trans hGN
  set X₁ := Y₀ ⊔ R with hX₁
  have hX₁G : X₁ ≤ Gu := sup_le hY₀G hRG
  have hY₀X : Y₀ ≤ X₁ := le_sup_left
  have hRX : R ≤ X₁ := le_sup_right
  have hX₁N : X₁ ≤ Subgroup.normalizer (Y₀ : Set G) := hX₁G.trans hGN
  have hYn : (Y₀.subgroupOf X₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hY₀X).mpr hX₁N
  have hidx : Y₀.relIndex X₁ = Y₀.relIndex R := by
    rw [hX₁, sup_comm]
    exact A4.relIndex_sup_eq_of_le_normalizer' hRN
  have hq2 : IsPGroup 2 (↥X₁ ⧸ Y₀.subgroupOf X₁) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hRp
    have hdvd : Y₀.relIndex R ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card Y₀ R
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    refine IsPGroup.of_card (n := m) ?_
    rw [← Subgroup.index_eq_card, ← Subgroup.relIndex, hidx, hm]
  have hsolvY : Group.IsSolvable ↥Y₀ := by
    have : Group.IsNilpotent ↥F' := (Group.isNilpotent_congr
      (F.equivMapOfInjective X.subtype X.subtype_injective)).mp inferInstance
    have hOp : IsPGroup 2 ↥((pCoreOf 2 Gu).subgroupOf Y₀) :=
      (pCoreOf_isPGroup 2 Gu).comap_of_injective Y₀.subtype Y₀.subtype_injective
    have := hOp.isNilpotent
    refine Group.isSolvable_of_ker_le_range ((pCoreOf 2 Gu).subgroupOf Y₀).subtype g ?_
    intro y hy
    exact ⟨⟨y, (hg1 y).mp hy⟩, rfl⟩
  have hsolv : Group.IsSolvable ↥X₁ := by
    have := hq2.isNilpotent
    exact isSolvable_of_le_normalizer hY₀X
  have hOX : pCoreOf 2 Gu ≤ pCoreOf 2 X₁ :=
    le_pCoreOf_of_le_normalizer 2 (hOY.trans hY₀X) (hX₁G.trans (le_normalizer_pCoreOf 2 Gu))
      (pCoreOf_isPGroup 2 Gu)
  have hCX : CharTwo X₁ := by
    intro x hx
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxC' : x ∈ Subgroup.centralizer (pCoreOf 2 Gu : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hOX) hxC
    exact hOX (hC2 ⟨hX₁G hxX, hxC'⟩)
  have hSyl : IsSylowTwoOf R X₁ := by
    refine ⟨hRX, hRp, ?_⟩
    have e1 := Subgroup.relIndex_mul_relIndex (R ⊓ Y₀) R X₁ inf_le_left hRX
    have e2 := Subgroup.relIndex_mul_relIndex (R ⊓ Y₀) Y₀ X₁ inf_le_right hY₀X
    have e3 : (R ⊓ Y₀).relIndex R = Y₀.relIndex R := by
      rw [inf_comm]
      exact Subgroup.inf_relIndex_right Y₀ R
    have hpos : 0 < (R ⊓ Y₀).relIndex R := by
      rcases Nat.eq_zero_or_pos ((R ⊓ Y₀).relIndex R) with h0 | h0
      · have := Subgroup.relIndex_mul_card (H := R ⊓ Y₀) (K := R)
        rw [h0, zero_mul] at this
        exact absurd this.symm Nat.card_pos.ne'
      · exact h0
    have e4 : R.relIndex X₁ = (R ⊓ Y₀).relIndex Y₀ := by
      have := e1.trans e2.symm
      rw [hidx, ← e3, mul_comm ((R ⊓ Y₀).relIndex Y₀)] at this
      exact Nat.eq_of_mul_eq_mul_left hpos this
    have e5 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 Gu) (R ⊓ Y₀) Y₀ (le_inf hO2R hOY)
      inf_le_right
    have hOY' : (pCoreOf 2 Gu).relIndex Y₀ = Nat.card ↥F' := by
      have hk : g.ker = (pCoreOf 2 Gu).subgroupOf Y₀ := by
        ext y
        rw [MonoidHom.mem_ker, hg1]
        rfl
      rw [Subgroup.relIndex, ← hk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hgs,
        Subgroup.card_top]
    intro h2
    rw [show (R.subgroupOf X₁).index = R.relIndex X₁ from rfl, e4] at h2
    have h2' : 2 ∣ Nat.card ↥F := hF'card ▸ hOY' ▸ h2.trans (Dvd.intro_left _ e5)
    exact absurd (Nat.Coprime.coprime_dvd_left h2' hcop) (by norm_num)
  have hX₁3 : ∀ w ∈ X₁, w ^ 3 = 1 → w = 1 := by
    intro w hw hw3
    obtain ⟨k, hk⟩ := hq2 (QuotientGroup.mk (⟨w, hw⟩ : ↥X₁))
    have hk' : ((⟨w, hw⟩ : ↥X₁) ^ 2 ^ k) ∈ Y₀.subgroupOf X₁ := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hk
    have hy : w ^ 2 ^ k ∈ Y₀ := by
      have := Subgroup.mem_subgroupOf.mp hk'
      simpa using this
    have hy3 : (w ^ 2 ^ k) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hw3, one_pow]
    exact eq_one_of_pow_two_pow_of_pow_three' (hY₀3 _ hy hy3) hw3
  obtain ⟨hU, -, hcase', -⟩ := B2_16 hsolv hCX hSyl rfl
  have hX₁H : X₁ ≤ hz T V := by
    rcases hcase' with ⟨-, hfac⟩ | ⟨hJ, I', hSyl', hJI, -, -, hnat, -, -, -, -⟩
    · intro x hx
      obtain ⟨n, hn, c, hc, rfl⟩ := hfac x hx
      have hcg : cgsIn Gu R ≤ hz T V ⊓ Gu := hyp.cgs
      have hJR : thompsonJ R ≤ R := iSup₂_le fun _ hA => hA.1
      have hZR : quasithinOmegaOneCenter R ≤ R := (Subgroup.closure_le _).mpr fun _ hx => hx.1.1
      have hn' := hcg (L246.C123.le_cgsIn_of_char hJR (Setup.thompsonJ_ne_bot hRp hR1)
        (Setup.characteristic_thompsonJ R) ⟨hX₁G hn.1, hn.2⟩)
      have hc' := hcg (L246.C123.le_cgsIn_of_char hZR (quasithinOmegaOneCenter_ne_bot hRp hR1)
        (L246C127.characteristic_omegaOneCenter R)
        ⟨hX₁G hc.1, mem_normalizer_of_mem_centralizer hc.2⟩)
      exact mul_mem hn'.1 hc'.1
    · exfalso
      set E := conjClosure (quasithinOmegaOneCenter R) X₁ with hE
      have hXE : X₁ ≤ Subgroup.normalizer (E : Set G) := le_normalizer_conjClosure _ _
      have hJX : thompsonJ X₁ ≤ X₁ := iSup₂_le fun _ hA => hA.1
      have hIX : ∀ L' ∈ I', L' ≤ autI hU X₁ := fun L' hL' =>
        (le_iSup₂_of_le L' hL' le_rfl).trans (hJI.symm.le.trans (autI_mono hU hJX))
      obtain ⟨L₀, hL₀⟩ : I'.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hI0
        apply hJ
        have h1 : autI hU (thompsonJ X₁) = ⊥ := by
          rw [hJI, hI0]
          simp
        have hJRN : thompsonJ R ≤ Subgroup.normalizer (E : Set G) :=
          (iSup₂_le fun _ hA => hA.1 : thompsonJ R ≤ R).trans (le_sup_right.trans hXE)
        exact (autI_eq_bot_iff hU hJRN).mp (le_bot_iff.mp (h1 ▸ hSyl'.1))
      obtain ⟨c₀, hc₀L, hc₀3, hc₀1, -⟩ := exists_three_of_actsAsNaturalL2 (hnat L₀ hL₀)
      obtain ⟨y, hy, hyc⟩ := hIX L₀ hL₀ hc₀L
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      set w : G := (y : G) with hwdef
      have hwX : w ∈ X₁ := hy
      have h3 : 3 ∣ orderOf w := by
        have h1 : orderOf c₀ = 3 := orderOf_eq_prime hc₀3 hc₀1
        rw [hwdef, Subgroup.orderOf_coe, ← h1, ← hyc]
        exact orderOf_map_dvd _ _
      have hw := hX₁3 _ (X₁.pow_mem hwX (orderOf w / 3)) (by
        rw [← pow_mul, Nat.div_mul_cancel h3, pow_orderOf_eq_one])
      have hord := orderOf_pow_orderOf_div (orderOf_pos w).ne' h3
      rw [hw, orderOf_one] at hord
      omega
  obtain ⟨f₀, hf₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (fitting_ne_bot_of_sl2 ψ hψs hgF)
  set f₁ : ↥Gu ⧸ CFSG.pCore 2 ↥Gu := ((f₀ : ↥X) : ↥Gu ⧸ CFSG.pCore 2 ↥Gu) with hf₁
  have hf₁F : f₁ ∈ F' := ⟨f₀, f₀.2, rfl⟩
  have hf₁1 : f₁ ≠ 1 := fun h1 => hf₀1 (Subtype.ext (Subtype.ext h1))
  obtain ⟨i, hi, hif⟩ := (f₀ : ↥X).2
  let σ : ↥I →* ↥Gu ⧸ CFSG.pCore 2 ↥Gu :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Gu)).comp (Subgroup.inclusion hIG)
  have hσi : σ ⟨i, hi⟩ = f₁ := hif
  have hodd : Odd (orderOf f₁) := by
    have := hF'ord f₁ hf₁F
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 =>
      absurd (Nat.Coprime.coprime_dvd_left h2 this) (by norm_num))
  rw [← hσi] at hodd
  obtain ⟨b, hbodd, hb⟩ := exists_odd_order_preimage σ ⟨i, hi⟩ hodd
  rw [hσi] at hb
  set l : G := (b : G) with hl
  have hlI : l ∈ I := b.2
  have hlodd : Odd (orderOf l) := by rw [hl, Subgroup.orderOf_coe]; exact hbodd
  have hlY : l ∈ Y₀ := mem_pre2.mpr ⟨hIG hlI, by
    have : σ b = f₁ := hb
    rw [← this] at hf₁F
    exact hf₁F⟩
  have hl1 : l ≠ 1 := by
    intro h1
    apply hf₁1
    rw [← hb]
    have : b = 1 := Subtype.ext h1
    rw [this, map_one]
  have hlK : l ∈ kz T V := by
    rw [← oTwoUpper_inf_hz_eq hKI]
    exact mem_oTwoUpper_of_odd ⟨hlI, hX₁H (hY₀X hlY)⟩ hlodd
  obtain ⟨eK⟩ := nonempty_quot_kz_alt5 h hMod h63
  let πK : ↥(kz T V) →* alternatingGroup (Fin 5) := eK.toMonoidHom.comp (QuotientGroup.mk' _)
  have hπKs : Function.Surjective πK := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπK1 : ∀ k : ↥(kz T V), πK k = 1 ↔ (k : G) ∈ pCoreOf 2 (kz T V) := by
    intro k
    show eK (QuotientGroup.mk k) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact (QuotientGroup.eq_one_iff _).trans C2Six.mem_pCore_two_iff
  set N := Y₀.subgroupOf (kz T V) with hN
  have hNn : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (hKG.trans hGN)
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have := hNn.map πK hπKs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map πK) with hb' | ht
  ·
    have h1 : πK ⟨l, hlK⟩ ∈ N.map πK := ⟨⟨l, hlK⟩, hlY, rfl⟩
    rw [hb', Subgroup.mem_bot, hπK1] at h1
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (kz T V) ⟨l, h1⟩
    have h2 : l ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact hl1 (eq_one_of_pow_two_pow_of_odd h2 hlodd)
  ·
    obtain ⟨a, -, ha2, -, ha1, -⟩ := alt5_two_involutions
    have ha : a ∈ N.map πK := ht ▸ Subgroup.mem_top a
    obtain ⟨n, hnN, rfl⟩ := ha
    have hnY : (n : G) ∈ Y₀ := hnN
    set m := orderOf (g ⟨n, hnY⟩) with hm
    have hmodd : Odd m := by
      have := hF'ord _ (g ⟨n, hnY⟩).2
      rw [Subgroup.orderOf_coe] at this
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 =>
        absurd (Nat.Coprime.coprime_dvd_left h2 this) (by norm_num))
    have hgm : g (⟨n, hnY⟩ ^ m) = 1 := by rw [map_pow, hm, pow_orderOf_eq_one]
    have hnm : ((n : G)) ^ m ∈ pCoreOf 2 Gu := by
      have := (hg1 _).mp hgm
      simpa using this
    have hnmK : ((n ^ m : ↥(kz T V)) : G) ∈ pCoreOf 2 (kz T V) :=
      inf_pCoreOf_le_of_le hKG ⟨(n ^ m).2, by simpa using hnm⟩
    have hπ1 : πK n ^ m = 1 := by
      rw [← map_pow]
      exact (hπK1 _).mpr hnmK
    have hord : orderOf (πK n) = 2 := orderOf_eq_prime ha2 ha1
    have hd := orderOf_dvd_of_pow_eq_one hπ1
    rw [hord] at hd
    exact absurd (even_iff_two_dvd.mpr hd) (Nat.not_even_iff_odd.mpr hmodd)

end Main

end CFSG.Quasithin.H13.L32A

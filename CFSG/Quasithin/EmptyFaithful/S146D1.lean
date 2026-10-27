module

public import CFSG.Quasithin.EmptyFaithful.S146B0
public import CFSG.Quasithin.Vol2.Ch1Rank
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section Rank

variable {X : Type*} [Group X] [Finite X]

theorem pRank_add_le_pRank_sup {p : ℕ} (hp : p.Prime) {A B : Subgroup X}
    (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hAB : A ⊓ B = ⊥) :
    CFSG.Open.pRank p A + CFSG.Open.pRank p B ≤ CFSG.Open.pRank p (A ⊔ B) := by
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨E₁, hE₁A, hE₁, hc₁⟩ := CFSG.SectionRank.exists_pRank hp1 A
  obtain ⟨E₂, hE₂B, hE₂, hc₂⟩ := CFSG.SectionRank.exists_pRank hp1 B
  let f : E₁ × E₂ →* X := MonoidHom.noncommCoprod E₁.subtype E₂.subtype
    (fun x y => hc x (hE₁A x.2) y (hE₂B y.2))
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have h : (x : X) * y = 1 := hxy
    have hx : (x : X) ∈ A ⊓ B := Subgroup.mem_inf.2 ⟨hE₁A x.2, by
      rw [eq_inv_of_mul_eq_one_left h]
      exact B.inv_mem (hE₂B y.2)⟩
    rw [hAB, Subgroup.mem_bot] at hx
    have hy : (y : X) = 1 := by rw [hx, one_mul] at h; exact h
    rw [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext hx, Subtype.ext hy⟩
  have hc₁' := hE₁.1
  have hc₂' := hE₂.1
  refine CFSG.SectionRank.le_pRank_of_injective hp1 (A := E₁ × E₂) ?_ ?_ ?_ f hf ?_
  · rintro ⟨a, b⟩ ⟨c, d⟩
    exact Prod.ext (mul_comm' a c) (mul_comm' b d)
  · rintro ⟨a, b⟩
    exact Prod.ext (Subtype.ext (hE₁.2 a a.2)) (Subtype.ext (hE₂.2 b b.2))
  · rw [Nat.card_prod, hc₁, hc₂, pow_add]
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    exact (A ⊔ B).mul_mem (Subgroup.mem_sup_left (hE₁A a.2)) (Subgroup.mem_sup_right (hE₂B b.2))

end Rank

section Concrete

theorem isElemAbelian_zpowers_of_pow_eq_one {Y : Type*} [Group Y] {p : ℕ} {c : Y} (hc : c ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers c) := CFSG.Open.isElemAbelian_zpowers hc

theorem one_le_pRank_zpowers {Y : Type*} [Group Y] [Finite Y] {c : Y} (hc : orderOf c = 3) :
    1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
  CFSG.SectionRank.le_pRank (by norm_num) le_top
    (isElemAbelian_zpowers_of_pow_eq_one (hc ▸ pow_orderOf_eq_one c)) (k := 1)
    (by rw [Nat.card_zpowers, hc]; simp)

theorem one_le_pRank_sl32 :
    1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) 3
    (by rw [Matrix.card_SL_field]; simp [Fin.prod_univ_succ])
  exact one_le_pRank_zpowers hx

@[expose] def a6ThreeA : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (show (0 : Fin 6) ≠ 1 by decide),
      Equiv.Perm.sign_swap (show (1 : Fin 6) ≠ 2 by decide)]
    decide⟩

@[expose] def a6ThreeB : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 3 4 * Equiv.swap 4 5, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (show (3 : Fin 6) ≠ 4 by decide),
      Equiv.Perm.sign_swap (show (4 : Fin 6) ≠ 5 by decide)]
    decide⟩

theorem a6ThreeA_pow_three : a6ThreeA ^ 3 = 1 := by decide +kernel

theorem a6ThreeB_pow_three : a6ThreeB ^ 3 = 1 := by decide +kernel

theorem a6ThreeA_ne_one : a6ThreeA ≠ 1 := by decide +kernel

theorem a6ThreeB_ne_one : a6ThreeB ≠ 1 := by decide +kernel

theorem a6ThreeA_commute : a6ThreeA * a6ThreeB = a6ThreeB * a6ThreeA := by decide +kernel

theorem orderOf_a6ThreeA : orderOf a6ThreeA = 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime a6ThreeA_pow_three a6ThreeA_ne_one

theorem orderOf_a6ThreeB : orderOf a6ThreeB = 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime a6ThreeB_pow_three a6ThreeB_ne_one

theorem mem_zpowers_of_orderOf_eq_three {Y : Type*} [Group Y] {c : Y} (hc : orderOf c = 3) {x : Y}
    (hx : x ∈ Subgroup.zpowers c) : x = 1 ∨ x = c ∨ x = c ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h := zpow_mod_orderOf c k
  rw [hc] at h
  rcases (by omega : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2) with
    h0 | h0 | h0
  · left; rw [← h, h0, zpow_zero]
  · right; left; rw [← h, h0, zpow_one]
  · right; right; rw [← h, h0, zpow_two, pow_two]

theorem a6Three_inf_eq_bot :
    Subgroup.zpowers a6ThreeA ⊓ Subgroup.zpowers a6ThreeB = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxA, hxB⟩
  rw [Subgroup.mem_bot]
  have hA := mem_zpowers_of_orderOf_eq_three orderOf_a6ThreeA hxA
  have hB := mem_zpowers_of_orderOf_eq_three orderOf_a6ThreeB hxB
  have key : ∀ y z : alternatingGroup (Fin 6),
      (y = 1 ∨ y = a6ThreeA ∨ y = a6ThreeA ^ 2) → (z = 1 ∨ z = a6ThreeB ∨ z = a6ThreeB ^ 2) →
      y = z → y = 1 := by
    decide +kernel
  exact key x x hA hB rfl

theorem two_le_pRank_alternatingGroup_six :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 6))) := by
  have h1 := one_le_pRank_zpowers orderOf_a6ThreeA
  have h2 := one_le_pRank_zpowers orderOf_a6ThreeB
  have hc : ∀ x ∈ Subgroup.zpowers a6ThreeA, ∀ y ∈ Subgroup.zpowers a6ThreeB, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_zpow (show Commute a6ThreeA a6ThreeB from a6ThreeA_commute) i j)).eq
  have := pRank_add_le_pRank_sup Nat.prime_three hc a6Three_inf_eq_bot
  have h3 : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers a6ThreeA) := by
    refine CFSG.SectionRank.le_pRank (by norm_num) le_rfl
      (isElemAbelian_zpowers_of_pow_eq_one a6ThreeA_pow_three) (k := 1) ?_
    rw [Nat.card_zpowers, orderOf_a6ThreeA]; simp
  have h4 : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers a6ThreeB) := by
    refine CFSG.SectionRank.le_pRank (by norm_num) le_rfl
      (isElemAbelian_zpowers_of_pow_eq_one a6ThreeB_pow_three) (k := 1) ?_
    rw [Nat.card_zpowers, orderOf_a6ThreeB]; simp
  have h5 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num)
    (le_top : Subgroup.zpowers a6ThreeA ⊔ Subgroup.zpowers a6ThreeB ≤ ⊤)
  omega

end Concrete

section Components

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem subgroupOf_pCoreOf_eq (K : Subgroup G) :
    (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := CFSG.openPCoreOf_subgroupOf 2 K

@[expose] def kbarEquivQuot (K : Subgroup G) : KBar K ≃* ↥K ⧸ CFSG.pCore 2 ↥K :=
  QuotientGroup.quotientMulEquivOfEq (subgroupOf_pCoreOf_eq K)

theorem nonempty_kbar_mulEquiv_modO2Image {H K : Subgroup G} (hK : K ∈ cComp H) :
    Nonempty (KBar K ≃* ↥(modO2Image H K)) := by
  obtain ⟨e⟩ := modO2_mulEquiv hK
  exact ⟨(kbarEquivQuot K).trans e⟩

theorem not_isMulCommutative_kbar {H K : Subgroup G} (hK : K ∈ cComp H) :
    ¬ IsMulCommutative (KBar K) := by
  intro hc
  have h0 : Group.IsSolvable (KBar K) := Group.isSolvable_of_comm fun a b => mul_comm' a b
  have h1 : Group.IsSolvable (↥K ⧸ CFSG.pCore 2 ↥K) :=
    Group.isSolvable_of_surjective (f := (kbarEquivQuot K).toMonoidHom) (kbarEquivQuot K).surjective
  have h2 : Group.IsSolvable ↥(CFSG.pCore 2 ↥K) := isSolvable_pCore_two_group ↥K
  have : Group.IsSolvable ↥K :=
    Group.isSolvable_of_ker_le_range (CFSG.pCore 2 ↥K).subtype (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  exact not_isSolvable_of_mem_cComp hK this

theorem center_eq_bot_of_isSimpleGroup {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (h : ¬ IsMulCommutative Y) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h1 | h1
  · exact h1
  · exact absurd (Subgroup.center_eq_top_iff.mp h1) h

theorem eq_one_of_forall_commute_modO2Image {H K : Subgroup G} (hK : K ∈ cComp H)
    (hs : IsSimpleGroup (KBar K)) :
    ∀ x ∈ modO2Image H K, (∀ y ∈ modO2Image H K, x * y = y * x) → x = 1 := by
  obtain ⟨e⟩ := nonempty_kbar_mulEquiv_modO2Image hK
  have hcen := center_eq_bot_of_isSimpleGroup (not_isMulCommutative_kbar hK)
  intro x hx hcomm
  have hmem : e.symm ⟨x, hx⟩ ∈ Subgroup.center (KBar K) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := hcomm (e z : _) (e z).2
    have : (⟨x, hx⟩ : ↥(modO2Image H K)) * e z = e z * ⟨x, hx⟩ := Subtype.ext hz
    have h2 := congrArg e.symm this
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h2
    exact h2.symm
  rw [hcen, Subgroup.mem_bot] at hmem
  have : (⟨x, hx⟩ : ↥(modO2Image H K)) = 1 := by
    have h3 := congrArg e hmem
    rw [MulEquiv.apply_symm_apply, map_one] at h3
    exact h3
  exact congrArg Subtype.val this

omit [Finite G] in
theorem modO2Image_commute {H K₁ K₂ : Subgroup G} (hc : ⁅K₁, K₂⁆ ≤ pCoreOf 2 H) :
    ∀ x ∈ modO2Image H K₁, ∀ y ∈ modO2Image H K₂, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
  have ha' : (a : G) ∈ K₁ := ha
  have hb' : (b : G) ∈ K₂ := hb
  have hmem : (⁅(a : G), (b : G)⁆ : G) ∈ pCoreOf 2 H :=
    hc (Subgroup.commutator_mem_commutator ha' hb')
  obtain ⟨c, hcP, hcc⟩ := Subgroup.mem_map.mp hmem
  have hcab : c = a * b * a⁻¹ * b⁻¹ :=
    Subtype.ext (by simpa [commutatorElement_def] using hcc)
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (a * b * a⁻¹ * b⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (hcab ▸ (by exact hcP))
  simp only [map_mul, map_inv] at h1
  exact (commutatorElement_eq_one_iff_mul_comm.mp (by simpa [commutatorElement_def] using h1))

theorem inf_eq_bot_of_commute_of_center {X : Type*} [Group X] {R S : Subgroup X}
    (hRS : ∀ x ∈ S, ∀ y ∈ R, x * y = y * x)
    (hcen : ∀ x ∈ R, (∀ y ∈ R, x * y = y * x) → x = 1) : R ⊓ S = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxR, hxS⟩
  exact Subgroup.mem_bot.mpr (hcen x hxR fun y hy => hRS x hxS y hy)

omit [Finite G] in
theorem KbarIsL3Two.nonempty {K : Subgroup G} (h : KbarIsL3Two K) :
    Nonempty (KBar K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := h

omit [Finite G] in
theorem KbarIsA6.nonempty {K : Subgroup G} (h : KbarIsA6 K) :
    Nonempty (KBar K ≃* ↥(alternatingGroup (Fin 6))) := h

theorem le_pRank_modO2Image_of_equiv {H K : Subgroup G} (hK : K ∈ cComp H) {L : Type} [Group L]
    [Finite L] (φ : KBar K ≃* L) {n : ℕ} (hn : n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)) :
    n ≤ CFSG.Open.pRank 3 (modO2Image H K) := by
  obtain ⟨e⟩ := nonempty_kbar_mulEquiv_modO2Image hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) (φ.symm.trans e)
  have h2 := pRank_top_subtype (p := 3) (modO2Image H K)
  omega

theorem false_of_two_cComp {H K K' : Subgroup G} (hK : K ∈ cComp H) (hs : IsSimpleGroup (KBar K))
    (hc : ⁅K, K'⁆ ≤ pCoreOf 2 H) (hrank : CFSG.Open.pRank 3 H ≤ 2) {a b : ℕ}
    (ha : a ≤ CFSG.Open.pRank 3 (modO2Image H K)) (hb : b ≤ CFSG.Open.pRank 3 (modO2Image H K'))
    (hab : 2 < a + b) : False := by
  have hcomm := modO2Image_commute hc
  have hinf : modO2Image H K ⊓ modO2Image H K' = ⊥ :=
    inf_eq_bot_of_commute_of_center (fun x hx y hy => (hcomm y hy x hx).symm)
      (eq_one_of_forall_commute_modO2Image hK hs)
  have h1 := pRank_add_le_pRank_sup Nat.prime_three hcomm hinf
  have h2 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num)
    (le_top : modO2Image H K ⊔ modO2Image H K' ≤ ⊤)
  have h3 := pRank_modO2_eq H Nat.prime_three (by norm_num)
  omega

theorem false_of_three_cComp {H K₁ K₂ K₃ : Subgroup G} (hK₁ : K₁ ∈ cComp H)
    (hK₃ : K₃ ∈ cComp H) (hs₁ : IsSimpleGroup (KBar K₁)) (hs₃ : IsSimpleGroup (KBar K₃))
    (hc₁₂ : ⁅K₁, K₂⁆ ≤ pCoreOf 2 H) (hc₁₃ : ⁅K₁, K₃⁆ ≤ pCoreOf 2 H) (hc₂₃ : ⁅K₂, K₃⁆ ≤ pCoreOf 2 H)
    (hrank : CFSG.Open.pRank 3 H ≤ 2) (h₁ : 1 ≤ CFSG.Open.pRank 3 (modO2Image H K₁))
    (h₂ : 1 ≤ CFSG.Open.pRank 3 (modO2Image H K₂))
    (h₃ : 1 ≤ CFSG.Open.pRank 3 (modO2Image H K₃)) : False := by
  have hcomm₁₂ := modO2Image_commute hc₁₂
  have hcomm₁₃ := modO2Image_commute hc₁₃
  have hcomm₂₃ := modO2Image_commute hc₂₃
  have hinf₁₂ : modO2Image H K₁ ⊓ modO2Image H K₂ = ⊥ :=
    inf_eq_bot_of_commute_of_center (fun x hx y hy => (hcomm₁₂ y hy x hx).symm)
      (eq_one_of_forall_commute_modO2Image hK₁ hs₁)
  have h12 := pRank_add_le_pRank_sup Nat.prime_three hcomm₁₂ hinf₁₂
  have hcomm : ∀ x ∈ modO2Image H K₁ ⊔ modO2Image H K₂, ∀ y ∈ modO2Image H K₃, x * y = y * x := by
    have hle : modO2Image H K₁ ⊔ modO2Image H K₂ ≤
        Subgroup.centralizer (modO2Image H K₃ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hcomm₁₃ x hx y hy).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hcomm₂₃ x hx y hy).symm
    intro x hx y hy
    exact ((Subgroup.mem_centralizer_iff.mp (hle hx)) y hy).symm
  have hinf : (modO2Image H K₁ ⊔ modO2Image H K₂) ⊓ modO2Image H K₃ = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_commute_of_center (fun x hx y hy => (hcomm x hx y hy))
      (eq_one_of_forall_commute_modO2Image hK₃ hs₃)
  have h123 := pRank_add_le_pRank_sup Nat.prime_three hcomm hinf
  have h4 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num)
    (le_top : (modO2Image H K₁ ⊔ modO2Image H K₂) ⊔ modO2Image H K₃ ≤ ⊤)
  have h5 := pRank_modO2_eq H Nat.prime_three (by norm_num)
  omega

end Components

section Main

variable {G : Type} [Group G] [Finite G]

theorem stage14621_of_a3 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    Stage14621 := by
  intro G _ _ T M S hB c19 c20 K hK
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hpc : pCoreOf 2 (mcOf T) ≠ ⊥ := hHTM.1.2
  have hqtke := S.hyp.qtke
  have hsimp := S.hyp.simple
  have hnab := S.hyp.nonabelian
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hTsyl : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hL : ∀ L ∈ cComp (mcOf T), KbarIsL3Two L ∨ KbarIsA6 L := fun L hL => (c20 _ hHTM L hL).1
  have hsimpL : ∀ L ∈ cComp (mcOf T), IsSimpleGroup (KBar L) := (c19 _ hHTM).2
  have hrank : CFSG.Open.pRank 3 (mcOf T) ≤ 2 :=
    pRank_le_two_of_pCoreOf_ne_bot hqtke hpc Nat.prime_three (by norm_num)
  have hcomm : ∀ L₁ ∈ cComp (mcOf T), ∀ L₂ ∈ cComp (mcOf T), L₁ ≠ L₂ →
      ⁅L₁, L₂⁆ ≤ pCoreOf 2 (mcOf T) := fun L₁ h₁ L₂ h₂ hne =>
    (lemma_1_2_1_two hqtke hsimp hnab h37 hpc h₁ h₂ hne).1.trans
      (lemma_1_2_1_two hqtke hsimp hnab h37 hpc h₁ h₂ hne).2
  have hspan : cCompSpan (mcOf T) = perfectCore (mcOf T) := lemma_1_2_1_one hqtke hsimp hnab h39 hpc
  have hrk1 : ∀ L ∈ cComp (mcOf T), 1 ≤ CFSG.Open.pRank 3 (modO2Image (mcOf T) L) := by
    intro L hL'
    rcases hL L hL' with h | h
    · obtain ⟨φ⟩ := h.nonempty
      exact le_pRank_modO2Image_of_equiv hL' φ one_le_pRank_sl32
    · obtain ⟨φ⟩ := h.nonempty
      exact le_pRank_modO2Image_of_equiv hL' φ (by
        have := two_le_pRank_alternatingGroup_six
        omega)
  have hrk2 : ∀ L ∈ cComp (mcOf T), KbarIsA6 L →
      2 ≤ CFSG.Open.pRank 3 (modO2Image (mcOf T) L) := by
    intro L hL' h
    obtain ⟨φ⟩ := h.nonempty
    exact le_pRank_modO2Image_of_equiv hL' φ two_le_pRank_alternatingGroup_six
  have hKle : K ≤ perfectCore (mcOf T) := hspan ▸ le_cCompSpan hK
  by_cases hKeq : perfectCore (mcOf T) = K
  · exact Or.inl ⟨hKeq, hL K hK⟩
  obtain ⟨K', hK', hK'ne⟩ : ∃ K' ∈ cComp (mcOf T), K' ≠ K := by
    by_contra hcon
    push Not at hcon
    apply hKeq
    refine le_antisymm ?_ hKle
    rw [← hspan]
    exact sSup_le fun L hL' => (hcon L hL').le
  have hKK' : K ≠ K' := hK'ne.symm
  have hKL3 : KbarIsL3Two K := by
    rcases hL K hK with h | h
    · exact h
    · exact (false_of_two_cComp hK (hsimpL K hK) (hcomm K hK K' hK' hKK') hrank (hrk2 K hK h)
        (hrk1 K' hK') (by omega)).elim
  have hK'L3 : KbarIsL3Two K' := by
    rcases hL K' hK' with h | h
    · exact h
    · exact (false_of_two_cComp hK' (hsimpL K' hK') (hcomm K' hK' K hK hK'ne) hrank (hrk2 K' hK' h)
        (hrk1 K hK) (by omega)).elim
  have hthree : ∀ L ∈ cComp (mcOf T), L = K ∨ L = K' := by
    intro L hL'
    by_contra hcon
    push Not at hcon
    exact false_of_three_cComp hK hL' (hsimpL K hK) (hsimpL L hL')
      (hcomm K hK K' hK' hKK') (hcomm K hK L hL' hcon.1.symm) (hcomm K' hK' L hL' hcon.2.symm) hrank
      (hrk1 K hK) (hrk1 K' hK') (hrk1 L hL')
  have hperf : perfectCore (mcOf T) = K ⊔ K' := by
    rw [← hspan]
    apply le_antisymm
    · exact sSup_le fun L hL' => by
        rcases hthree L hL' with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
    · exact sup_le (le_cCompSpan hK) (le_cCompSpan hK')
  have hnorm : ∀ L ∈ cComp (mcOf T), (∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set G)) →
      mcOf T ≤ Subgroup.normalizer (L : Set G) := by
    intro L hL' hLT
    have hn := lemma_1_2_4_normal hqtke hsimp hnab h37 h38 hpc hTsyl
      (cComp_subset_lFamily hTH hL') le_rfl hL' hLT
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hL')).mp hn
  have hconj : ∀ t ∈ T, ∀ L ∈ cComp (mcOf T), conjSub t L ∈ cComp (mcOf T) := fun t ht L hL' =>
    map_conj_mem_cComp hL' (hTH ht)
  by_cases hKn : ∀ t ∈ T, t ∈ Subgroup.normalizer (K : Set G)
  ·
    have hKH := hnorm K hK hKn
    by_cases hKn' : ∀ t ∈ T, t ∈ Subgroup.normalizer (K' : Set G)
    · exact Or.inr (Or.inr ⟨K', hK', hK'ne, hKH, hnorm K' hK' hKn', hperf, hKL3, hK'L3⟩)
    · exfalso
      push Not at hKn'
      obtain ⟨t, ht, htn⟩ := hKn'
      have hc1 := hconj t ht K' hK'
      have hne : conjSub t K' ≠ K' := fun h => htn (A38.map_conj_eq_iff.mp h)
      rcases hthree _ hc1 with h | h
      ·
        have h2 : conjSub t⁻¹ (conjSub t K') = K' := conjSub_conjSub_inv t K'
        have h3 : conjSub t⁻¹ K = K := A38.map_conj_eq_iff.mpr (Subgroup.inv_mem _ (hKH (hTH ht)))
        rw [h] at h2
        exact hKK' (h3.symm.trans h2)
      · exact hne h
  ·
    right; left
    push Not at hKn
    obtain ⟨t, ht, htn⟩ := hKn
    have hc1 := hconj t ht K hK
    have hne : conjSub t K ≠ K := fun h => htn (A38.map_conj_eq_iff.mp h)
    refine ⟨⟨t, ht, htn, ?_⟩, hKL3⟩
    rcases hthree _ hc1 with h | h
    · exact (hne h).elim
    · rw [hperf, h]

end Main

end CFSG.Quasithin

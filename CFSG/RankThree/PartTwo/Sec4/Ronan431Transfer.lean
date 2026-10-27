module

public import CFSG.RankThree.PartTwo.Sec4.Ronan431Cfg

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (descAut aBar descAut_mk descAut_eq_one_iff
  descAut_mem_aBar mem_aBar_iff isE27_aBar isPGroup_center_of_isComponent quotPCoreTwoCongr
  equivBar map_le_autFix isSubnormal_bar descAut_mem_bar mk_comp_injective_of_inf_eq_bot
  inf_eq_bot_of_center_eq_bot mem_centralizer_of_conj_mem_pCoreOf map_mem_pCoreOf_map_iff
  pCoreOf_map_of_injective quotCenterEquivOfEqBot pCore_two_le_center)
open CFSG.Assembly.RankThreeEven (projSp)

@[expose] def Item4_31List42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.pRank 3 (⊤ : Subgroup G) = 3 →
    aschbacherSolvableCore 3 G = ⊥ →
    ∀ A : Subgroup G, Late.IsE27 A → ∀ c ∈ A, c ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    Census.List42 (L ⧸ Subgroup.center L) →
    ∀ K : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G), IsComponent K →
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 6)) →
      Nonempty (L ≃* alternatingGroup (Fin 6)) ∨ Nonempty (L ≃* Blueprint.NativeSporadic.J3) ∨
        Nonempty (L ≃* projSp 3 (GaloisField 2 1)) ∨ Nonempty (L ≃* alternatingGroup (Fin 9)) ∨
        Nonempty (L ≃* projSp 2 (GaloisField 2 3))

section Rank

variable {X : Type} [Group X] [Finite X]

theorem isElemAbelian_of_le {p : ℕ} {A F : Subgroup X} (hA : CFSG.Open.IsElemAbelian p A)
    (hFA : F ≤ A) : CFSG.Open.IsElemAbelian p F :=
  ⟨⟨⟨fun x y => Subtype.ext (by
    have h := congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hFA x.2⟩ ⟨y, hFA y.2⟩)
    exact h)⟩⟩,
    fun x hx => hA.2 x (hFA hx)⟩

theorem elemAbelian_sup_of_commute {E F : Subgroup X} (hE : CFSG.Open.IsElemAbelian 3 E)
    (hF : CFSG.Open.IsElemAbelian 3 F) (hc : ∀ e ∈ E, ∀ f ∈ F, e * f = f * e)
    (hinf : E ⊓ F = ⊥) :
    CFSG.Open.IsElemAbelian 3 (E ⊔ F) ∧
      Nat.card (E ⊔ F : Subgroup X) = Nat.card E * Nat.card F := by
  have hcomm : ∀ (a : E) (b : F), Commute (E.subtype a) (F.subtype b) := fun a b =>
    hc a a.2 b b.2
  set φ := MonoidHom.noncommCoprod E.subtype F.subtype hcomm with hφ
  have hrange : φ.range = E ⊔ F := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ h
    have h' : (a : X) * (b : X) = 1 := h
    have hab : (a : X) = (b : X)⁻¹ := eq_inv_of_mul_eq_one_left h'
    have hmem : (a : X) ∈ E ⊓ F := ⟨a.2, hab ▸ F.inv_mem b.2⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hb : (b : X) = 1 := by rw [hmem, one_mul] at h'; exact h'
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hb)
  have hmemr : ∀ x ∈ E ⊔ F, ∃ a ∈ E, ∃ b ∈ F, x = a * b := by
    intro x hx
    rw [← hrange] at hx
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact ⟨a, a.2, b, b.2, rfl⟩
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨a, ha, b, hb, hx⟩ := hmemr x x.2
    obtain ⟨a', ha', b', hb', hy⟩ := hmemr y y.2
    apply Subtype.ext
    change (x : X) * y = y * x
    rw [hx, hy]
    have h1 : a * a' = a' * a := congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
    have h2 : b * b' = b' * b := congrArg Subtype.val (hF.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
    have h3 := hc a ha b' hb'
    have h4 := hc a' ha' b hb
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [h4]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [h1, h2]
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [h3]
      _ = a' * b' * (a * b) := by group
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmemr x hx
    have hab : Commute a b := hc a ha b hb
    rw [hab.mul_pow, hE.2 a ha, hF.2 b hb, one_mul]
  · rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

theorem false_of_pRank_le_of_card {E : Subgroup X} (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3)
    (hE : CFSG.Open.IsElemAbelian 3 E) {k : ℕ} (hk : 4 ≤ k) (hcard : Nat.card E = 3 ^ k) :
    False := by
  have := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_top hE hcard
  omega

theorem pRank_top_le_of_subgroup (H : Subgroup X) :
    CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) H.subtype H.subtype_injective

end Rank

section Fix

variable {X : Type} [Group X] [Finite X]

theorem eq_one_of_mem_of_commute {K : Subgroup X} (hT : IsType431 (K ⧸ CFSG.pCore 2 K)) {x : X}
    (hx : x ∈ K) (hcomm : ∀ k ∈ K, k * x = x * k) (h9 : x ^ 9 = 1) : x = 1 := by
  have hz : (⟨x, hx⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2)
  have h9' : (⟨x, hx⟩ : K) ^ 9 = 1 := Subtype.ext (by simpa using h9)
  exact congrArg Subtype.val (eq_one_of_mem_center_of_isType431 hT hz h9')

theorem exists_e9 {K : Subgroup X} (hT : IsType431 (K ⧸ CFSG.pCore 2 K)) :
    ∃ E : Subgroup X, E ≤ K ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ x ∈ E, (∀ k ∈ K, k * x = x * k) → x = 1 := by
  obtain ⟨R, hR, hR9, -⟩ := exists_elemAbelian_nine_of_isType431 hT
  refine ⟨R.map K.subtype, Subgroup.map_subtype_le R, CFSG.SectionRank.isElemAbelian_map hR _,
    ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hR9]
  · rintro _ ⟨r, hr, rfl⟩ hcomm
    refine eq_one_of_mem_of_commute hT r.2 hcomm ?_
    have h9 : r ^ 9 = 1 := by
      rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hR.2 r hr, one_pow]
    simpa using congrArg Subtype.val h9

theorem map_eq_of_pRank_le (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) {L : Subgroup X}
    (hL : IsComponent L) {E : Subgroup X} (hEL : E ≤ L) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) (hEc : ∀ x ∈ E, (∀ l ∈ L, l * x = x * l) → x = 1) (α : X ≃* X) :
    L.map α.toMonoidHom = L := by
  by_contra hne
  have hL' : IsComponent (L.map α.toMonoidHom) := CFSG.LocalCores.isComponent_map_mulEquiv α hL
  rcases CFSG.LocalCores.distinct_components_commute hL hL' with h | h
  · exact hne h.symm
  have hcomm : L ≤ Subgroup.centralizer ((L.map α.toMonoidHom : Subgroup X) : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  set E' := E.map α.toMonoidHom with hE'
  have hE'L' : E' ≤ L.map α.toMonoidHom := Subgroup.map_mono hEL
  have hE'e : CFSG.Open.IsElemAbelian 3 E' := CFSG.SectionRank.isElemAbelian_map hE _
  have hE'9 : Nat.card E' = 9 := by rw [hE', Subgroup.card_map_of_injective α.injective, hE9]
  have hc : ∀ e ∈ E, ∀ f ∈ E', e * f = f * e := fun e he f hf =>
    (Subgroup.mem_centralizer_iff.mp (hcomm (hEL he)) f (hE'L' hf)).symm
  have hinf : E ⊓ E' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hEc x hx.1 fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hcomm hl) x (hE'L' hx.2)).symm
  obtain ⟨hEE', hcard⟩ := elemAbelian_sup_of_commute hE hE'e hc hinf
  exact false_of_pRank_le_of_card hrank hEE' (le_refl 4) (by rw [hcard, hE9, hE'9]; norm_num)

theorem normal_of_pRank_le (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) {L : Subgroup X}
    (hL : IsComponent L) {E : Subgroup X} (hEL : E ≤ L) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) (hEc : ∀ x ∈ E, (∀ l ∈ L, l * x = x * l) → x = 1) : L.Normal :=
  ⟨fun n hn g => by
    have h := map_eq_of_pRank_le hrank hL hEL hE hE9 hEc (MulAut.conj g)
    rw [← h]
    exact ⟨n, hn, rfl⟩⟩

theorem eq_top_of_isComponent {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    {K : Subgroup Q} (hK : IsComponent K) : K = ⊤ := by
  have htop : IsComponent (⊤ : Subgroup Q) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQ,
      Subgroup.IsSubnormal.top⟩
  rcases CFSG.LocalCores.distinct_components_commute hK htop with h | h
  · exact h
  · exfalso
    haveI : Group.IsPerfect K := hK.1.1
    haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
    have hle : ⁅K, K⁆ ≤ ⁅K, (⊤ : Subgroup Q)⁆ := Subgroup.commutator_mono le_rfl le_top
    rw [h, le_bot_iff, Subgroup.commutator_eq_self] at hle
    exact (Subgroup.nontrivial_iff_ne_bot K).mp inferInstance hle

end Fix

section Config

variable {G : Type} [Group G] [Finite G]

theorem zpowers_eq_inf_centralizer (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3)
    {A : Subgroup G} (hA : Late.IsE27 A) {c : G} (hc : c ∈ A) (hc1 : c ≠ 1) {K' : Subgroup G}
    (hK'c : K' ≤ Subgroup.centralizer {c}) {E : Subgroup G} (hEK' : E ≤ K')
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEc : ∀ x ∈ E, (∀ k ∈ K', k * x = x * k) → x = 1) :
    Subgroup.zpowers c = A ⊓ Subgroup.centralizer (K' : Set G) := by
  set F := A ⊓ Subgroup.centralizer (K' : Set G) with hF
  have hcF : Subgroup.zpowers c ≤ F := by
    rw [Subgroup.zpowers_le]
    refine ⟨hc, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hK'c hk)
  have hFe : CFSG.Open.IsElemAbelian 3 F := isElemAbelian_of_le hA.1 inf_le_left
  have hcomm : ∀ f ∈ F, ∀ e ∈ E, f * e = e * f := fun f hf e he =>
    (Subgroup.mem_centralizer_iff.mp hf.2 e (hEK' he)).symm
  have hinf : F ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hEc x hx.2 fun k hk => Subgroup.mem_centralizer_iff.mp hx.1.2 k hk
  obtain ⟨hFE, hcard⟩ := elemAbelian_sup_of_commute hFe hE hcomm hinf
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 : IsPGroup 3 F := fun x => ⟨1, Subtype.ext (by simpa using hFe.2 x x.2)⟩
  obtain ⟨m, hm⟩ := hF3.exists_card_eq
  have hm1 : m ≤ 1 := by
    by_contra hlt
    exact false_of_pRank_le_of_card hrank hFE (k := m + 2) (by omega)
      (by rw [hcard, hm, hE9, pow_add]; norm_num)
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hA.1.2 c hc) hc1
  refine Subgroup.eq_of_le_of_card_ge hcF ?_
  rw [Nat.card_zpowers, hc3, hm]
  calc 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm1
    _ = 3 := by norm_num

theorem inf_centralizer_eq_bot {A : Subgroup G} (hA : Late.IsE27 A) {c : G} {L K' : Subgroup G}
    (hK'L : K' ≤ L) (hcent : Subgroup.zpowers c = A ⊓ Subgroup.centralizer (K' : Set G))
    (hLc : ¬ L ≤ Subgroup.centralizer {c}) : A ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  by_contra ha1
  have haK' : a ∈ Subgroup.zpowers c := by
    rw [hcent]
    exact ⟨ha.1, Subgroup.centralizer_le (s := (K' : Set G)) (t := (L : Set G)) hK'L ha.2⟩
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at haK'
    exact ha1 haK'
  have hcA : c ∈ A := by
    have : c ∈ Subgroup.zpowers c := Subgroup.mem_zpowers c
    rw [hcent] at this
    exact this.1
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hA.1.2 c hcA) hc1
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hA.1.2 a ha.1) ha1
  have hle : Subgroup.zpowers a ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr haK'
  have heq : Subgroup.zpowers a = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hc3, ha3])
  have hcL : c ∈ Subgroup.centralizer (L : Set G) := by
    have : c ∈ Subgroup.zpowers a := heq ▸ Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr ha.2) this
  apply hLc
  intro l hl
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hcL l hl

theorem center_eq_bot_of_pRank (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3)
    {A : Subgroup G} (hA : Late.IsE27 A) {L : Subgroup G} (hLn : L.Normal)
    (hAC : A ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hZ3 : IsPGroup 3 (Subgroup.center L)) :
    Subgroup.center L = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  set Z' : Subgroup G := (Subgroup.center L).map L.subtype with hZ'
  have hZ'n : Z'.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZ'3 : IsPGroup 3 Z' := hZ3.map L.subtype
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA.1.2 x x.2)⟩
  set P : Subgroup G := A ⊔ Z' with hP
  have hP3 : IsPGroup 3 P := IsPGroup.to_sup_of_normal_right hA3 hZ'3
  haveI : Group.IsNilpotent P := hP3.isNilpotent
  set H : Subgroup P := Z'.subgroupOf P with hH
  haveI : H.Normal := Subgroup.normal_subgroupOf
  obtain ⟨⟨z₀, hz₀Z⟩, hz₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hHne : H ≠ ⊥ := by
    intro hb
    have hmem : (⟨(z₀ : G), le_sup_right (a := A) ⟨z₀, hz₀Z, rfl⟩⟩ : P) ∈ H :=
      ⟨z₀, hz₀Z, rfl⟩
    rw [hb, Subgroup.mem_bot] at hmem
    apply hz₀1
    apply Subtype.ext
    apply Subtype.ext
    have h1 : ((z₀ : L) : G) = 1 := congrArg Subtype.val hmem
    exact h1
  obtain ⟨⟨y, hyH⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hHne)
  have hyZ' : ((y : P) : G) ∈ Z' := hyH.1
  have hyc : y ∈ Subgroup.center P := hyH.2
  have hy1' : ((y : P) : G) ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext h))
  obtain ⟨n, hn⟩ := hZ'3 ⟨_, hyZ'⟩
  have hn' : ((y : P) : G) ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hord : orderOf ((y : P) : G) ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hn'
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hy1' hj
  have h3dvd : 3 ∣ orderOf ((y : P) : G) := by
    rw [hj]
    exact dvd_pow_self 3 hj0
  set z : G := ((y : P) : G) ^ (orderOf ((y : P) : G) / 3) with hz
  have hz3 : orderOf z = 3 := orderOf_pow_orderOf_div (orderOf_pos _).ne' h3dvd
  have hzZ' : z ∈ Z' := Z'.pow_mem hyZ' _
  have hzA : ∀ a ∈ A, a * z = z * a := by
    intro a ha
    have haP : a ∈ P := le_sup_left (b := Z') ha
    have hcomm := Subgroup.mem_center_iff.mp hyc ⟨a, haP⟩
    have hcomm' : a * ((y : P) : G) = ((y : P) : G) * a := congrArg Subtype.val hcomm
    exact (Commute.pow_right hcomm' _).eq
  have hzpow : z ^ 3 = 1 := by rw [← hz3, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz3; norm_num at hz3
  by_cases hzmem : z ∈ A
  ·
    have hzC : z ∈ Subgroup.centralizer (L : Set G) := by
      obtain ⟨w, hw, hwz⟩ := hzZ'
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      rw [← hwz]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨l, hl⟩)
    have : z ∈ A ⊓ Subgroup.centralizer (L : Set G) := ⟨hzmem, hzC⟩
    rw [hAC, Subgroup.mem_bot] at this
    exact hz1 this
  ·
    obtain ⟨-, hcard⟩ := CFSG.RankThree.PartTwo.sup_zpowers_card (p := 3) hA.1.1 hzmem hzpow hzA
    have hE := Sec15.isElemAbelian_sup_zpowers hA.1 hzpow hzA
    exact false_of_pRank_le_of_card hrank hE (k := 4) le_rfl (by rw [hcard, hA.2]; norm_num)

theorem inf_center_eq_bot431 {L K' : Subgroup G} (hK'L : K' ≤ L) (hK'q : IsQuasisimple K')
    (hK'type : IsType431 (K' ⧸ CFSG.pCore 2 K')) (hZ : IsPGroup 3 (Subgroup.center L)) :
    K'.subgroupOf L ⊓ Subgroup.center L = ⊥ := by
  set e : K'.subgroupOf L ≃* K' := Subgroup.subgroupOfEquivOfLe hK'L
  have hZK' : Subgroup.center (K' ⧸ CFSG.pCore 2 K') = ⊥ := center_quot_eq_bot_of_isType431 hK'type
  exact inf_eq_bot_of_center_eq_bot (Γ := L)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hK'q)
    (RonanK429.center_eq_bot_of_mulEquiv (quotPCoreTwoCongr e) hZK') le_rfl hZ

theorem cfgS431_of (hθ : aschbacherSolvableCore 3 G = ⊥)
    {A : Subgroup G} (hA : Late.IsE27 A) {c : G} (hc : c ∈ A)
    {L : Subgroup G} (hL : IsComponent L) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hAC : A ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hLc : ¬ L ≤ Subgroup.centralizer {c})
    {K' : Subgroup G} (hK'M : K' ≤ L ⊓ Subgroup.centralizer {c}) (hK'q : IsQuasisimple K')
    (hK'sn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {c})).IsSubnormal)
    (hK'type : IsType431 (K' ⧸ CFSG.pCore 2 K')) (hAK' : A ≤ Subgroup.normalizer (K' : Set G))
    (hcent : Subgroup.zpowers c = A ⊓ Subgroup.centralizer (K' : Set G))
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤ 3) :
    K'.subgroupOf L ⊓ Subgroup.center L = ⊥ ∧
      CfgS431 (L ⧸ Subgroup.center L) (aBar hAN) (descAut L ⟨c, hAN hc⟩)
        ((K'.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L))) := by
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have hLp : Group.IsPerfect L := hL.1.1
  have hZ3 := isPGroup_center_of_isComponent hθ hL
  have hinf := inf_center_eq_bot431 hK'L hK'q hK'type hZ3
  set K₁ : Subgroup L := K'.subgroupOf L with hK₁
  set Kb : Subgroup (L ⧸ Subgroup.center L) := K₁.map (QuotientGroup.mk' (Subgroup.center L))
    with hKb
  have hinj := mk_comp_injective_of_inf_eq_bot hinf
  refine ⟨hinf, ?_⟩
  refine
    { isE27 := isE27_aBar hLp hAN hAC hA
      mem := descAut_mem_aBar hAN hc
      ne_one := ?_
      pRank_le := hrk
      le_autFix := map_le_autFix (hAN hc) (hK'M.trans inf_le_right)
      isSubnormal := isSubnormal_bar (hAN hc) hK'M hK'sn
      isPerfect := ?_
      map_mem := fun x hx y hy => descAut_mem_bar hK'L hAN hAK' hx hy
      isType := ?_
      faithful := ?_ }
  · intro h1
    rw [descAut_eq_one_iff hLp] at h1
    apply hLc
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp h1 l hl)
  · haveI : Group.IsPerfect K' := hK'q.1
    haveI : Group.IsPerfect K₁ := Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hK'L).symm.toMonoidHom) (MulEquiv.surjective _)
    exact Group.IsPerfect.map _
  · exact isType431_of_mulEquiv (quotPCoreTwoCongr (equivBar hK'L hinf)).symm hK'type
  · intro x hx hxK
    obtain ⟨a, ha, rfl⟩ := (mem_aBar_iff hAN).mp hx
    have haK' : a ∈ Subgroup.centralizer (K' : Set G) := by
      refine mem_centralizer_of_conj_mem_pCoreOf hK'q (hAK' ha) fun k hk => ?_
      set l : L := ⟨k, hK'L hk⟩ with hl
      have hlK₁ : l ∈ K₁ := hk
      have hak : a * k * a⁻¹ ∈ K' := (Subgroup.mem_normalizer_iff.mp (hAK' ha) k).mp hk
      set l' : L := L.normalizerMonoidHom ⟨a, hAN ha⟩ l * l⁻¹ with hl'
      have hl'K₁ : l' ∈ K₁ := by
        change a * k * a⁻¹ * k⁻¹ ∈ K'
        exact Subgroup.mul_mem _ hak (Subgroup.inv_mem _ hk)
      have h1 := hxK (l : L ⧸ Subgroup.center L) ⟨l, hlK₁, rfl⟩
      have h2 : QuotientGroup.mk' (Subgroup.center L) l' ∈ CFSG.Open.pCoreOf 2 Kb := h1
      rw [map_mem_pCoreOf_map_iff 2 _ hinj hl'K₁] at h2
      have h3 : L.subtype l' ∈ CFSG.Open.pCoreOf 2 (K₁.map L.subtype) := by
        rw [pCoreOf_map_of_injective 2 L.subtype (L.subtype_injective.comp K₁.subtype_injective)]
        exact ⟨l', h2, rfl⟩
      rw [hK₁, Subgroup.map_subgroupOf_eq_of_le hK'L] at h3
      exact h3
    have haz : a ∈ Subgroup.zpowers c := by
      rw [hcent]
      exact ⟨ha, haK'⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp haz
    have hN : (⟨a, hAN ha⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨c, hAN hc⟩ : Subgroup.normalizer (L : Set G)) ^ m :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm.symm)
    rw [hN, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ m

theorem pCore_two_eq_bot_of_isComponent (hθ : aschbacherSolvableCore 3 G = ⊥) {L : Subgroup G}
    (hL : IsComponent L) : CFSG.pCore 2 L = ⊥ := by
  have hle := pCore_two_le_center hL.1
  have hZ3 := isPGroup_center_of_isComponent hθ hL
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 L)) ⟨x, hx⟩
  obtain ⟨b, hb⟩ := hZ3 ⟨x, hle hx⟩
  have ha' : x ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hb' : x ^ 3 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hcop : Nat.Coprime (2 ^ a) (3 ^ b) := Nat.Coprime.pow a b (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one ha')
    (orderOf_dvd_of_pow_eq_one hb'))

theorem mem_normalizer_inf_centralizer {L : Subgroup G} (hLn : L.Normal) {a c : G}
    (hac : a * c = c * a) :
    a ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer {c} : Subgroup G) : Set G) := by
  have hac' : a⁻¹ * c = c * a⁻¹ := by
    calc a⁻¹ * c = a⁻¹ * (c * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * c) * a⁻¹ := by rw [hac]
      _ = c * a⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hL : h ∈ L := hh.1
    have hC : h * c = c * h := Subgroup.mem_centralizer_singleton_iff.mp hh.2
    refine Subgroup.mem_inf.mpr ⟨hLn.conj_mem h hL a, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc a * h * a⁻¹ * c = a * h * (a⁻¹ * c) := by group
      _ = a * h * (c * a⁻¹) := by rw [hac']
      _ = a * (h * c) * a⁻¹ := by group
      _ = a * (c * h) * a⁻¹ := by rw [hC]
      _ = (a * c) * h * a⁻¹ := by group
      _ = (c * a) * h * a⁻¹ := by rw [hac]
      _ = c * (a * h * a⁻¹) := by group
  · intro hh
    have hL : a * h * a⁻¹ ∈ L := hh.1
    have hC : a * h * a⁻¹ * c = c * (a * h * a⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp hh.2
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · have := hLn.conj_mem _ hL a⁻¹
      simpa [mul_assoc] using this
    · calc h * c = a⁻¹ * (a * h * a⁻¹) * (a * c) := by group
        _ = a⁻¹ * (a * h * a⁻¹) * (c * a) := by rw [hac]
        _ = a⁻¹ * ((a * h * a⁻¹) * c) * a := by group
        _ = a⁻¹ * (c * (a * h * a⁻¹)) * a := by rw [hC]
        _ = a⁻¹ * (c * a) * h := by group
        _ = a⁻¹ * (a * c) * h := by rw [hac]
        _ = c * h := by group

end Config

section Main

theorem item4_31List42_of_rowsS (R : K431RowsS) : Item4_31List42 := by
  intro G _ _ hrank hθ A hA c hcA hc1 L hL hlist K hK hKt
  have hrank' : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3 := hrank.le
  obtain ⟨φ⟩ := hKt
  have hTK : IsType431 (K ⧸ CFSG.pCore 2 K) := ⟨φ⟩
  set K' : Subgroup G := K.map (L ⊓ Subgroup.centralizer {c} : Subgroup G).subtype with hK'def
  set eK : K ≃* K' := K.equivMapOfInjective (L ⊓ Subgroup.centralizer {c} : Subgroup G).subtype
    (Subgroup.subtype_injective _) with heK
  have hK'q : IsQuasisimple K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  have hK'type : IsType431 (K' ⧸ CFSG.pCore 2 K') :=
    isType431_of_mulEquiv (quotPCoreTwoCongr eK).symm hTK
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {c} := Subgroup.map_subtype_le K
  have hK'sn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {c})).IsSubnormal := by
    rw [hK'def, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
    exact hK.2
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have hK'c : K' ≤ Subgroup.centralizer {c} := hK'M.trans inf_le_right
  obtain ⟨E₀, hE₀K, hE₀, hE₀9, hE₀c⟩ := exists_e9 hTK
  set E : Subgroup G := E₀.map (L ⊓ Subgroup.centralizer {c} : Subgroup G).subtype with hEdef
  have hEK' : E ≤ K' := Subgroup.map_mono hE₀K
  have hE : CFSG.Open.IsElemAbelian 3 E := CFSG.SectionRank.isElemAbelian_map hE₀ _
  have hE9 : Nat.card E = 9 := by
    rw [hEdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hE₀9]
  have hEc : ∀ x ∈ E, (∀ k ∈ K', k * x = x * k) → x = 1 := by
    rintro _ ⟨x₀, hx₀, rfl⟩ hcomm
    have h1 : x₀ = 1 := hE₀c x₀ hx₀ fun k hk => Subtype.ext (hcomm _ ⟨k, hk, rfl⟩)
    rw [h1, map_one]
  have hEcL : ∀ x ∈ E, (∀ l ∈ L, l * x = x * l) → x = 1 := fun x hx hcomm =>
    hEc x hx fun k hk => hcomm k (hK'L hk)
  have hLn : L.Normal := normal_of_pRank_le hrank' hL (hEK'.trans hK'L) hE hE9 hEcL
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := fun a _ => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    exact Subgroup.mem_top a
  have hcommA : ∀ a ∈ A, a * c = c * a := fun a ha =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩)
  have hrankM : CFSG.Open.pRank 3 (⊤ : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G)) ≤ 3 :=
    (pRank_top_le_of_subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G)).trans hrank'
  have hAK' : A ≤ Subgroup.normalizer (K' : Set G) := by
    intro a ha
    have haM : a ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer {c} : Subgroup G) : Set G) :=
      mem_normalizer_inf_centralizer hLn (hcommA a ha)
    set α : MulAut (L ⊓ Subgroup.centralizer {c} : Subgroup G) :=
      (L ⊓ Subgroup.centralizer {c} : Subgroup G).normalizerMonoidHom ⟨a, haM⟩ with hα
    have hKα := map_eq_of_pRank_le hrankM hK hE₀K hE₀ hE₀9 hE₀c α
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hcomp : (L ⊓ Subgroup.centralizer {c} : Subgroup G).subtype.comp α.toMonoidHom =
        (MulAut.conj a).toMonoidHom.comp (L ⊓ Subgroup.centralizer {c} : Subgroup G).subtype := by
      ext m
      rfl
    calc K'.map (MulAut.conj a).toMonoidHom =
        (K.map α.toMonoidHom).map (L ⊓ Subgroup.centralizer {c} : Subgroup G).subtype := by
          rw [hK'def, Subgroup.map_map, Subgroup.map_map, hcomp]
      _ = K' := by rw [hKα]
  have hcent := zpowers_eq_inf_centralizer hrank' hA hcA hc1 hK'c hEK' hE hE9 hEc
  by_cases hLc : L ≤ Subgroup.centralizer {c}
  ·
    left
    have hML : (L ⊓ Subgroup.centralizer {c} : Subgroup G) = L := inf_eq_left.mpr hLc
    have hMq : IsQuasisimple (L ⊓ Subgroup.centralizer {c} : Subgroup G) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hML).symm hL.1
    have hKtop : K = ⊤ := eq_top_of_isComponent hMq hK
    set eKL : K ≃* L := ((MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv).trans
      (MulEquiv.subgroupCongr hML) with heKL
    have hO2 := pCore_two_eq_bot_of_isComponent hθ hL
    have e₁ : L ⧸ CFSG.pCore 2 L ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot
    exact ⟨e₁.symm.trans ((quotPCoreTwoCongr eKL).symm.trans φ)⟩
  ·
    have hAC := inf_centralizer_eq_bot hA hK'L hcent hLc
    have hZ3 := isPGroup_center_of_isComponent hθ hL
    have hZ := center_eq_bot_of_pRank hrank' hA hLn hAC hZ3
    have hrkL : CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤ 3 := by
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (quotCenterEquivOfEqBot hZ)]
      exact (pRank_top_le_of_subgroup L).trans hrank'
    obtain ⟨-, hcfg⟩ :=
      cfgS431_of hθ hA hcA hL hAN hAC hLc hK'M hK'q hK'sn hK'type hAK' hcent hrkL
    have hrow := R.rowS_of_list42 hL.1.2.1 hL.1.2.2 hlist
    exact ConclS431.of_mulEquiv (quotCenterEquivOfEqBot hZ) (hrow _ _ _ hcfg)

end Main

end CFSG.RankThree.PartTwo.Sec4.Ronan431

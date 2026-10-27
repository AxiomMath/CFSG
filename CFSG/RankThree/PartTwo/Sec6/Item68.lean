module

public import CFSG.RankThree.PartTwo.Sec6.Item68Tools
public import CFSG.RankThree.PartTwo.Sec6.Item65One
public import CFSG.RankThree.PartTwo.KFacts.KS6OuterIndex
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_le_three_of_isCyclic {B : Subgroup G} (hB : IsCyclic B)
    (hB3 : ∀ x ∈ B, x ^ 3 = 1) : Nat.card B ≤ 3 := by
  obtain ⟨g, hg⟩ := hB.exists_generator
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  have : g ^ 3 = 1 := Subtype.ext (by simpa using hB3 g g.2)
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one this)

theorem exists_mem_sup_not_mem_thetaQuotCentralizer (h45 : Sec4.Item4_5) (h66 : Item6_6)
    (hKf : KFacts.KS6OuterIndex) (hG : PartTwoStanding G) {A : Subgroup G}
    (hA : A ∈ partTwoS G) {E : Subgroup G} (hE : E ∈ collectionIn (partTwoE G) A) {c : G}
    (hcE : c ∈ E) (hc1 : c ≠ 1) {L : Subgroup G} (hLc : L ∈ thetaComponentsAt 3 c)
    (hLs : L ∈ lStar A) :
    ∃ b ∈ E, b ∈ L ⊔ thetaQuotCentralizer L ∧ b ∉ thetaQuotCentralizer L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hEmem, hEA⟩ := hE
  have hEab := hEmem.1
  have hE27 : Nat.card E = 27 := hEmem.2.1
  have hAab := hA.1.1
  set H := Subgroup.centralizer ({c} : Set G) with hH
  have hEH : E ≤ H := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hEab.1.is_comm.comm ⟨x, hx⟩ ⟨c, hcE⟩))
  have hAL := le_normalizer_of_mem_thetaComponentsAt h45 hG.toTheoremFourHyp hAab (hEA hcE) hc1
  have hEL : E ≤ Subgroup.normalizer (L : Set G) := hEA.trans (hAL L hLc)
  have hH4 : SectionFourHyp H :=
    hG.toTheoremFourHyp.sectionFourHyp (centralizer_ne_top_of_ne_one hG.toTheoremFourHyp hc1)
  have h3Z : 3 ∣ Nat.card (Subgroup.center H) := by
    set c' : H := ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hc'3 : orderOf c' = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (hEab.2 c hcE) hc1
    have hle : Subgroup.zpowers c' ≤ Subgroup.center H := by
      rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hc'3] at this
  obtain ⟨hLH, hL'⟩ := mem_thetaComponentsIn_iff.mp hLc
  have hFN : E.subgroupOf H ≤ Subgroup.normalizer ((L.subgroupOf H : Subgroup H) : Set H) :=
    fun x hx => mem_normalizer_of_mem_normalizer_map (by
      rw [Subgroup.map_subgroupOf_eq_of_le hLH]
      exact hEL (Subgroup.mem_subgroupOf.mp hx))
  have hk := hKf H hH4 h3Z (L.subgroupOf H) hL' (E.subgroupOf H) (isElemAbelian_subgroupOf hEab)
    hFN
  rw [card_subgroupOf_of_le hEH, hE27] at hk
  have hle : Nat.card ((E.subgroupOf H) ⊓ ((L.subgroupOf H) ⊔
      thetaQuotCentralizer (L.subgroupOf H)) : Subgroup H) ≤
      Nat.card (E ⊓ (L ⊔ thetaQuotCentralizer L) : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    refine Subgroup.card_le_of_le ((Subgroup.map_inf_le _ _ _).trans (inf_le_inf ?_ ?_))
    · rw [Subgroup.map_subgroupOf_eq_of_le hEH]
    · rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLH]
      refine sup_le_sup_left ?_ L
      have h2 := map_thetaQuotCentralizer_le (L.subgroupOf H)
      rwa [Subgroup.map_subgroupOf_eq_of_le hLH] at h2
  have hcyc := h66 G hG A hA L hLs
  have hAC : Nat.card (A ⊓ thetaQuotCentralizer L : Subgroup G) ≤ 3 :=
    card_le_three_of_isCyclic hcyc fun x hx => hAab.2 x hx.1
  have hEC : Nat.card (E ⊓ thetaQuotCentralizer L : Subgroup G) ≤ 3 :=
    (Subgroup.card_le_of_le (inf_le_inf_right _ hEA)).trans hAC
  by_contra hcon
  push Not at hcon
  have hsub : E ⊓ (L ⊔ thetaQuotCentralizer L) ≤ E ⊓ thetaQuotCentralizer L :=
    fun b hb => ⟨hb.1, hcon b hb.1 hb.2⟩
  have := Subgroup.card_le_of_le hsub
  omega

theorem exists_isPGroup_mem_of_mem_sup {L : Subgroup G} {b : G} (hb3 : b ^ 3 = 1)
    (hbLC : b ∈ L ⊔ thetaQuotCentralizer L) :
    ∃ x ∈ L, (∃ k : ℕ, x ^ (3 ^ k) = 1) ∧ x⁻¹ * b ∈ thetaQuotCentralizer L := by
  set C := thetaQuotCentralizer L with hC
  have hCL : C ≤ Subgroup.normalizer (L : Set G) := thetaQuotCentralizer_le_normalizer L
  have hLC : L ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thetaQuotCentralizer L)
  have hbN : b ∈ Subgroup.normalizer (C : Set G) := sup_le hLC Subgroup.le_normalizer hbLC
  have hb' : b ∈ (L : Set G) * (C : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L C hCL]
    exact hbLC
  obtain ⟨y, hyL, z, hzC, hyz⟩ := hb'
  simp only at hyz
  subst hyz
  have hy3 : y ^ 3 ∈ C := by
    set b := y * z with hb
    have hbb : b * b ∈ Subgroup.normalizer (C : Set G) := Subgroup.mul_mem _ hbN hbN
    have hbbb : b * b * b ∈ Subgroup.normalizer (C : Set G) := Subgroup.mul_mem _ hbb hbN
    have e : y ^ 3 = (b * z⁻¹ * b⁻¹) * (b * b * z⁻¹ * (b * b)⁻¹) *
        (b * b * b * z⁻¹ * (b * b * b)⁻¹) * (b * b * b) := by
      rw [pow_three, hb]
      group
    rw [e]
    refine C.mul_mem (C.mul_mem (C.mul_mem ?_ ?_) ?_) ?_
    · exact (Subgroup.mem_normalizer_iff.mp hbN _).mp (C.inv_mem hzC)
    · exact (Subgroup.mem_normalizer_iff.mp hbb _).mp (C.inv_mem hzC)
    · exact (Subgroup.mem_normalizer_iff.mp hbbb _).mp (C.inv_mem hzC)
    · rw [← pow_three', hb3]
      exact C.one_mem
  obtain ⟨n, hn, k, hk⟩ := exists_pow_mem_mul_zpowers_cube y
  refine ⟨y ^ n, L.pow_mem hyL n, ⟨k, hk⟩, ?_⟩
  have h1 : y⁻¹ * y ^ n ∈ C := Subgroup.zpowers_le.mpr hy3 hn
  rw [show (y ^ n)⁻¹ * (y * z) = (y⁻¹ * y ^ n)⁻¹ * z by group]
  exact C.mul_mem (C.inv_mem h1) hzC

omit [Finite G] in
theorem mul_conj_mem_pPrimeCore_of_mem_partTwoS {A : Subgroup G} (hA : A ∈ partTwoS G)
    {c : G} (hcA : c ∈ A) (hc1 : c ≠ 1) {b : G} (hbA : b ∈ A) {v : G}
    (hv : v ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G))) :
    b * v * b⁻¹ * v⁻¹ ∈ inSubgroup (CFSG.pPrimeCore 2)
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G))) := by
  set Θ := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) with hΘ
  set R := ⁅Θ, A⁆ with hR
  have hRodd : Odd (Nat.card R) := hA.2.1 c hcA hc1
  have hAab := hA.1.1
  have hAH : A ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨c, hcA⟩))
  have hAΘ : A ≤ Subgroup.normalizer (Θ : Set G) := hAH.trans (le_normalizer_theta _)
  have hRΘ : R ≤ Θ := Subgroup.le_normalizer_iff_commutator_le_left.mp hAΘ
  have hΘR : Θ ≤ Subgroup.normalizer (R : Set G) := le_normalizer_commutator_left Θ A
  have hRn : (R.subgroupOf Θ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRΘ).mpr hΘR
  have hRcop : Nat.Coprime 2 (Nat.card (R.subgroupOf Θ)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRΘ).toEquiv]
    exact Nat.coprime_two_left.mpr hRodd
  have hRO : R.subgroupOf Θ ≤ CFSG.pPrimeCore 2 Θ := le_sSup ⟨hRn, hRcop⟩
  have hmem : b * v * b⁻¹ * v⁻¹ ∈ R := by
    have h2 := R.inv_mem (Subgroup.commutator_mem_commutator hv hbA)
    rwa [commutatorElement_def, show (v * b * v⁻¹ * b⁻¹)⁻¹ = b * v * b⁻¹ * v⁻¹ by group] at h2
  exact ⟨⟨_, hRΘ hmem⟩, hRO (Subgroup.mem_subgroupOf.mpr hmem), rfl⟩

theorem map_conj_mem_thetaComponentsAt {c x : G} (hx : x ∈ Subgroup.centralizer ({c} : Set G))
    {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c) :
    L.map (MulAut.conj x).toMonoidHom ∈ thetaComponentsAt 3 c := by
  set H := Subgroup.centralizer ({c} : Set G) with hH
  obtain ⟨L', hL', rfl⟩ := hL
  refine ⟨L'.map (MulAut.conj (⟨x, hx⟩ : H)).toMonoidHom,
    map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj (⟨x, hx⟩ : H)) hL', ?_⟩
  show (L'.map (MulAut.conj (⟨x, hx⟩ : H)).toMonoidHom).map H.subtype =
    (L'.map H.subtype).map (MulAut.conj x).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem commutator_le_theta_of_ne_mem_thetaComponentsAt {c : G} {L₁ L₂ : Subgroup G}
    (h₁ : L₁ ∈ thetaComponentsAt 3 c) (h₂ : L₂ ∈ thetaComponentsAt 3 c) (hne : L₁ ≠ L₂) :
    ⁅L₁, L₂⁆ ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
  obtain ⟨K₁, hK₁, rfl⟩ := h₁
  obtain ⟨K₂, hK₂, rfl⟩ := h₂
  have hne' : K₁ ≠ K₂ := fun h => hne (by rw [h])
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono (commutator_le_theta_of_ne hK₁ hK₂ hne')

omit [Finite G] in
theorem ne_map_conj_of_not_mem_normalizer {L : Subgroup G} {h : G}
    (hhL : h ∉ Subgroup.normalizer (L : Set G)) : L ≠ L.map (MulAut.conj h).toMonoidHom := by
  intro heq
  have h1 : L.map (MulAut.conj (1 : G)).toMonoidHom = L := by
    ext y
    simp
  have := inv_mul_mem_normalizer_of_map_conj_eq (z := h) (c := 1) (P := L) (heq.symm.trans h1.symm)
  rw [inv_one, one_mul] at this
  exact hhL this

theorem commutator_conj_mem_theta {c : G} {L : Subgroup G} (hLc : L ∈ thetaComponentsAt 3 c)
    {b x h : G} (hxL : x ∈ L) (hxb : x⁻¹ * b ∈ thetaQuotCentralizer L)
    (hhc : h ∈ Subgroup.centralizer ({c} : Set G)) (hhb : h * b = b * h) :
    x * (h * x * h⁻¹) * x⁻¹ * (h * x * h⁻¹)⁻¹ ∈
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
  have hθL : inSubgroup (aschbacherSolvableCore 3) L ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
    rw [theta_eq_inf_of_mem_thetaComponentsAt hLc]
    exact inf_le_right
  by_cases hhL : h ∈ Subgroup.normalizer (L : Set G)
  · set Q := thetaQuotCentralizer L with hQ
    have hhQ : h ∈ Subgroup.normalizer (Q : Set G) :=
      normalizer_le_normalizer_thetaQuotCentralizer L hhL
    have h1 : h * (x⁻¹ * b) * h⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hhQ _).mp hxb
    have h2 : h * (x⁻¹ * b) * h⁻¹ = (h * x * h⁻¹)⁻¹ * b := by
      rw [show h * (x⁻¹ * b) * h⁻¹ = (h * x * h⁻¹)⁻¹ * (h * b * h⁻¹) by group, hhb,
        mul_inv_cancel_right]
    have hzQ : x⁻¹ * (h * x * h⁻¹) ∈ Q := by
      have := Q.mul_mem hxb (Q.inv_mem (h2 ▸ h1))
      rwa [show x⁻¹ * b * ((h * x * h⁻¹)⁻¹ * b)⁻¹ = x⁻¹ * (h * x * h⁻¹) by group] at this
    have h3 := (mem_thetaQuotCentralizer_iff.mp hzQ).2 x hxL
    have hxx : x * x ∈ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) L : Set G) :=
      le_normalizer_theta L (L.mul_mem hxL hxL)
    have h4 := (Subgroup.mem_normalizer_iff.mp hxx _).mp (inv_mem h3)
    rw [show (x * x) * (x⁻¹ * (x⁻¹ * (h * x * h⁻¹) * x * (x⁻¹ * (h * x * h⁻¹))⁻¹))⁻¹ *
      (x * x)⁻¹ = x * (h * x * h⁻¹) * x⁻¹ * (h * x * h⁻¹)⁻¹ by group] at h4
    exact hθL h4
  · have hLh : L.map (MulAut.conj h).toMonoidHom ∈ thetaComponentsAt 3 c :=
      map_conj_mem_thetaComponentsAt hhc hLc
    have hcomm := commutator_le_theta_of_ne_mem_thetaComponentsAt hLc hLh
      (ne_map_conj_of_not_mem_normalizer hhL)
    have hmem : h * x * h⁻¹ ∈ L.map (MulAut.conj h).toMonoidHom := ⟨x, hxL, by simp⟩
    have := hcomm (Subgroup.commutator_mem_commutator hxL hmem)
    rwa [commutatorElement_def] at this

theorem mem_thetaQuotCentralizer_of_commute {c : G} {L : Subgroup G}
    (hLc : L ∈ thetaComponentsAt 3 c) {t x r : G} (htc : t ∈ Subgroup.centralizer ({c} : Set G))
    (htL : t ∉ Subgroup.normalizer (L : Set G)) (hxL : x ∈ L)
    (hrx : r⁻¹ * x ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)))
    (htr : t * r = r * t) : x ∈ thetaQuotCentralizer L := by
  set H := Subgroup.centralizer ({c} : Set G) with hH
  set Θ := inSubgroup (aschbacherSolvableCore 3) H with hΘ
  have hHΘ : H ≤ Subgroup.normalizer (Θ : Set G) := le_normalizer_theta H
  set K := L.map (MulAut.conj t).toMonoidHom with hK
  have hKc : K ∈ thetaComponentsAt 3 c := map_conj_mem_thetaComponentsAt htc hLc
  have hLK : ⁅L, K⁆ ≤ Θ := commutator_le_theta_of_ne_mem_thetaComponentsAt hLc hKc
    (ne_map_conj_of_not_mem_normalizer htL)
  have hLH : L ≤ H := le_centralizer_of_mem_thetaComponentsAt hLc
  set k := t * x * t⁻¹ with hk
  have hkK : k ∈ K := ⟨x, hxL, by simp [hk]⟩
  have hkH : k ∈ H := H.mul_mem (H.mul_mem htc (hLH hxL)) (H.inv_mem htc)
  set u := k⁻¹ * x with hu
  have hrt : r * t⁻¹ * r⁻¹ = t⁻¹ := by
    calc r * t⁻¹ * r⁻¹ = t⁻¹ * (t * r) * t⁻¹ * r⁻¹ := by group
      _ = t⁻¹ * (r * t) * t⁻¹ * r⁻¹ := by rw [htr]
      _ = t⁻¹ := by group
  have hu' : u = t * (r⁻¹ * x)⁻¹ * t⁻¹ * (r⁻¹ * x) := by
    calc u = t * x⁻¹ * t⁻¹ * x := by rw [hu, hk]; group
      _ = t * x⁻¹ * (r * t⁻¹ * r⁻¹) * x := by rw [hrt]
      _ = t * (r⁻¹ * x)⁻¹ * t⁻¹ * (r⁻¹ * x) := by group
  have huΘ : u ∈ Θ := by
    rw [hu']
    exact Θ.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHΘ htc) _).mp (Θ.inv_mem hrx)) hrx
  refine mem_thetaQuotCentralizer_iff.mpr ⟨Subgroup.le_normalizer hxL, fun l hl => ?_⟩
  rw [theta_eq_inf_of_mem_thetaComponentsAt hLc]
  refine ⟨L.mul_mem (L.inv_mem hl) (L.mul_mem (L.mul_mem hxL hl) (L.inv_mem hxL)), ?_⟩
  have e : l⁻¹ * (x * l * x⁻¹) = ⁅l⁻¹, k⁆ * (k * (l⁻¹ * u * l * u⁻¹) * k⁻¹) := by
    rw [hu, commutatorElement_def]
    group
  rw [e]
  refine Θ.mul_mem (hLK (Subgroup.commutator_mem_commutator (L.inv_mem hl) hkK)) ?_
  have h1 : l⁻¹ * u * l⁻¹⁻¹ ∈ Θ :=
    (Subgroup.mem_normalizer_iff.mp (hHΘ (H.inv_mem (hLH hl))) u).mp huΘ
  rw [inv_inv] at h1
  exact (Subgroup.mem_normalizer_iff.mp (hHΘ hkH) _).mp (Θ.mul_mem h1 (Θ.inv_mem huΘ))

theorem le_normalizer_of_mem_fourGroupsPlus (h45 : Sec4.Item4_5) (h66 : Item6_6)
    (hKf : KFacts.KS6OuterIndex) (hG : PartTwoStanding G) {A : Subgroup G}
    (hA : A ∈ partTwoS G) {E : Subgroup G} (hE : E ∈ collectionIn (partTwoE G) A) {c : G}
    (hcE : c ∈ E) (hc1 : c ≠ 1) {L : Subgroup G} (hLc : L ∈ thetaComponentsAt 3 c)
    (hLs : L ∈ lStar A) {T : Subgroup G} (hT : T ∈ fourGroupsPlus E) :
    T ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEmem := hE.1
  have hEA := hE.2
  have hEab := hEmem.1
  have hAab := hA.1.1
  have hE3 : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian hEab
  set H := Subgroup.centralizer ({c} : Set G) with hH
  have hEH : E ≤ H := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hEab.1.is_comm.comm ⟨x, hx⟩ ⟨c, hcE⟩))
  have hTplus := hT
  obtain ⟨hTU, -⟩ := hT
  obtain ⟨hET, -, hT4⟩ := mem_fourGroups_iff.mp hTU
  have hTC : E ≤ Subgroup.centralizer (T : Set G) := (mem_fourGroupsPlus_iff.mp hTplus).2
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4]; norm_num)
  have hTcomm : ∀ e ∈ E, ∀ t ∈ T, t * e = e * t := fun e he t ht =>
    Subgroup.mem_centralizer_iff.mp (hTC he) t ht
  have hTH : T ≤ H := fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr
    (hTcomm c hcE t ht)
  have hLH : L ≤ H := le_centralizer_of_mem_thetaComponentsAt hLc
  have hLp := isPerfect_of_mem_thetaComponentsAt hLc
  have hLq := isQuasisimple_of_mem_thetaComponentsAt hLc
  have hAL := le_normalizer_of_mem_thetaComponentsAt h45 hG.toTheoremFourHyp hAab (hEA hcE) hc1
  have hEL : E ≤ Subgroup.normalizer (L : Set G) := hEA.trans (hAL L hLc)
  by_contra hTL
  obtain ⟨t, htT, htL⟩ := IsConcreteLE.not_le_iff_exists.mp hTL
  obtain ⟨b, hbE, hbLC, hbC⟩ :=
    exists_mem_sup_not_mem_thetaQuotCentralizer h45 h66 hKf hG hA hE hcE hc1 hLc hLs
  have hb3 : b ^ 3 = 1 := hEab.2 b hbE
  obtain ⟨x, hxL, ⟨k₀, hxk⟩, hxb⟩ := exists_isPGroup_mem_of_mem_sup hb3 hbLC
  set Θ := inSubgroup (aschbacherSolvableCore 3) H with hΘ
  set O := inSubgroup (CFSG.pPrimeCore 2) Θ with hO
  have hHΘ : H ≤ Subgroup.normalizer (Θ : Set G) := le_normalizer_theta H
  have hHO : H ≤ Subgroup.normalizer (O : Set G) :=
    hHΘ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  set C := centralizerMod H Θ O hHΘ hHO with hCdef
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := le_normalizer_centralizerMod hHΘ hHO
  have hΘH : Θ ≤ H := theta_le H
  have hbC' : b ∈ C := mem_centralizerMod.mpr ⟨hEH hbE, fun v hv =>
    mul_conj_mem_pPrimeCore_of_mem_partTwoS hA (hEA hcE) hc1 (hEA hbE) hv⟩
  have hbL : Subgroup.zpowers b ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr (hEL hbE)
  have hLb : ⁅L, Subgroup.zpowers b⁆ = L := commutator_eq_of_not_le_theta hLp hLq hbL
    fun h => hbC ((commutator_le_theta_iff hbL).mp h (Subgroup.mem_zpowers b))
  have hLC : L ≤ C := by
    rw [← hLb, Subgroup.commutator_le]
    intro l hl y hy
    have hyC : y ∈ C := (Subgroup.zpowers_le.mpr hbC') hy
    rw [commutatorElement_def]
    exact C.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHC (hLH hl)) y).mp hyC) (C.inv_mem hyC)
  set ET := E ⊔ T with hETdef
  have hETH : ET ≤ H := sup_le hEH hTH
  have hETb : ET ≤ Subgroup.centralizer ({b} : Set G) := by
    refine sup_le (fun e he => Subgroup.mem_centralizer_singleton_iff.mpr ?_)
      (fun t' ht' => Subgroup.mem_centralizer_singleton_iff.mpr (hTcomm b hbE t' ht'))
    exact congrArg Subtype.val (hEab.1.is_comm.comm ⟨e, he⟩ ⟨b, hbE⟩)
  set Γ : Set G := {y | ∃ g ∈ ET, y = g * x * g⁻¹} with hΓ
  have hΓH : Γ ⊆ H := by
    rintro _ ⟨g, hg, rfl⟩
    exact H.mul_mem (H.mul_mem (hETH hg) (hLH hxL)) (H.inv_mem (hETH hg))
  have hΓC : Γ ⊆ C := by
    rintro _ ⟨g, hg, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hHC (hETH hg)) x).mp (hLC hxL)
  have hΓ3 : ∀ s ∈ Γ, ∃ k : ℕ, s ^ (3 ^ k) = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨k₀, by rw [conj_pow, hxk, mul_one, mul_inv_cancel]⟩
  have hΓc : ∀ s ∈ Γ, ∀ s' ∈ Γ, s * s' * s⁻¹ * s'⁻¹ ∈ Θ := by
    rintro _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩
    set h := g₁⁻¹ * g₂ with hhdef
    have hhET : h ∈ ET := ET.mul_mem (ET.inv_mem hg₁) hg₂
    have hhb : h * b = b * h := Subgroup.mem_centralizer_singleton_iff.mp (hETb hhET)
    have h1 := commutator_conj_mem_theta hLc hxL hxb (hETH hhET) hhb
    have h2 := (Subgroup.mem_normalizer_iff.mp (hHΘ (hETH hg₁)) _).mp h1
    rwa [show g₁ * (x * (h * x * h⁻¹) * x⁻¹ * (h * x * h⁻¹)⁻¹) * g₁⁻¹ =
      g₁ * x * g₁⁻¹ * (g₂ * x * g₂⁻¹) * (g₁ * x * g₁⁻¹)⁻¹ * (g₂ * x * g₂⁻¹)⁻¹ by
        rw [hhdef]; group] at h2
  set P := Subgroup.closure Γ ⊔ Θ with hPdef
  have hPH : P ≤ H := sup_le ((Subgroup.closure_le _).mpr hΓH) hΘH
  have hPC : P ≤ C ⊔ Θ := sup_le_sup_right ((Subgroup.closure_le _).mpr hΓC) Θ
  obtain ⟨hΘsol, hΘ3⟩ := theta_solvable_and_not_dvd H
  have hOodd : Odd (Nat.card O) := by
    rw [hO, inSubgroup, Subgroup.card_map_of_injective Θ.subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hETP : ET ≤ Subgroup.normalizer (P : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun g hg y hy => ?_
    have hle : P ≤ P.comap (MulAut.conj g).toMonoidHom := by
      refine sup_le ((Subgroup.closure_le _).mpr ?_) ?_
      · rintro _ ⟨g', hg', rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap]
        refine Subgroup.mem_sup_left (Subgroup.subset_closure ⟨g * g', ET.mul_mem hg hg', ?_⟩)
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · intro v hv
        rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hHΘ (hETH hg)) v).mp hv)
    exact hle hy
  obtain ⟨R, hR3, hRN, hRlift⟩ := exists_invariant_isPGroup_lift (P := P) (S := T) (O := O)
    hΘsol hΘ3 hOodd le_sup_right (hPH.trans hHΘ)
    (fun y hy => exists_pow_mem_of_mem_closure_sup hΘH hHΘ hΓH hΓ3 hΓc hy)
    hE3 hT2 hET hETP (hETH.trans hHΘ)
    (fun y hy hy3 v hv => by
      obtain ⟨k, hk⟩ := hy3
      exact (mem_centralizerMod.mp (mem_of_mem_sup_of_pow_eq_one (p := 3)
        (hΘH.trans hHC) hΘ3 (hPC hy) hk)).2 v hv)
  have hRT : R ≤ Subgroup.centralizer (T : Set G) :=
    rank3II_6_4_2 G hG E hEmem T hTplus T hTU.1 le_rfl R
      ((mem_invariantPiSubgroups_piOf_iff Nat.prime_three).mpr ⟨le_top, hR3, hRN⟩)
  have hxP : x ∈ P := Subgroup.mem_sup_left (Subgroup.subset_closure ⟨1, ET.one_mem, by group⟩)
  obtain ⟨r, hrR, hrx⟩ := hRlift x hxP
  have htr : t * r = r * t := Subgroup.mem_centralizer_iff.mp (hRT hrR) t htT
  have hxC := mem_thetaQuotCentralizer_of_commute hLc (hTH htT) htL hxL hrx htr
  apply hbC
  have := (thetaQuotCentralizer L).mul_mem hxC hxb
  rwa [mul_inv_cancel_left] at this

theorem rank3II_6_8 (h45 : Sec4.Item4_5) (h66 : Item6_6) (hKf : KFacts.KS6OuterIndex) :
    Item6_8 := by
  intro G _ _ hG A hA E hE L hL T hT
  obtain ⟨hLE, hLs⟩ := hL
  obtain ⟨c, hcE, hc1, hLc⟩ := mem_thetaComponentFamily_iff.mp hLE
  exact le_normalizer_of_mem_fourGroupsPlus h45 h66 hKf hG hA hE hcE hc1 hLc hLs hT

theorem rank3II_6_8_of_inputs (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hB3 : BThreeProperty) (hKf : KFacts.KS6OuterIndex) : Item6_8 :=
  rank3II_6_8 h45 (rank3II_6_6_of_inputs h45 h48 h49 hB3) hKf

end CFSG.RankThree.PartTwo.Sec6

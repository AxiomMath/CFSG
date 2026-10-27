module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8310B
public import CFSG.Quasithin.Vol2.Ch11SecBL2OPSL
public import CFSG.Quasithin.Vol2.Ch1Sec3A5PSL
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.Quasithin.H13.Ch8310P

open CFSG.Glauberman.Dickson CFSG.Quasithin.H13.Ch8310

section Prod

variable {X : Type*} [Group X] {N₁ N₂ : Subgroup X}

@[expose] def mulMap (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) : ↥N₁ × ↥N₂ →* X :=
  N₁.subtype.noncommCoprod N₂.subtype fun a b =>
    show Commute (N₁.subtype a) (N₂.subtype b) from hc a a.2 b b.2

theorem mulMap_injective (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hd : N₁ ⊓ N₂ = ⊥) :
    Function.Injective (mulMap hc) := by
  unfold mulMap
  rw [MonoidHom.noncommCoprod_injective]
  refine ⟨N₁.subtype_injective, N₂.subtype_injective, ?_⟩
  rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
  exact hd

theorem mulMap_range (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) :
    (mulMap hc).range = N₁ ⊔ N₂ := by
  unfold mulMap
  rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]

@[expose] noncomputable def prodEquiv (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hd : N₁ ⊓ N₂ = ⊥) : ↥N₁ × ↥N₂ ≃* ↥(N₁ ⊔ N₂) :=
  (MonoidHom.ofInjective (mulMap_injective hc hd)).trans (MulEquiv.subgroupCongr (mulMap_range hc))

theorem prodEquiv_apply (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hd : N₁ ⊓ N₂ = ⊥)
    (x : ↥N₁ × ↥N₂) : ((prodEquiv hc hd x : ↥(N₁ ⊔ N₂)) : X) = (x.1 : X) * x.2 := rfl

@[expose] noncomputable def pr₁ (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hd : N₁ ⊓ N₂ = ⊥) :
    ↥(N₁ ⊔ N₂) →* ↥N₁ :=
  (MonoidHom.fst _ _).comp (prodEquiv hc hd).symm.toMonoidHom

@[expose] noncomputable def pr₂ (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hd : N₁ ⊓ N₂ = ⊥) :
    ↥(N₁ ⊔ N₂) →* ↥N₂ :=
  (MonoidHom.snd _ _).comp (prodEquiv hc hd).symm.toMonoidHom

variable (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hd : N₁ ⊓ N₂ = ⊥)

theorem pr_mul (x : ↥(N₁ ⊔ N₂)) : ((pr₁ hc hd x : ↥N₁) : X) * ((pr₂ hc hd x : ↥N₂) : X) = x := by
  have h := congrArg Subtype.val ((prodEquiv hc hd).apply_symm_apply x)
  rw [prodEquiv_apply] at h
  exact h

theorem pr_eq {x : ↥(N₁ ⊔ N₂)} {a : ↥N₁} {b : ↥N₂} (h : (a : X) * b = x) :
    pr₁ hc hd x = a ∧ pr₂ hc hd x = b := by
  have h1 : (prodEquiv hc hd).symm x = (a, b) := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [prodEquiv_apply]
    exact h.symm
  exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩

variable {Y : Subgroup X}

theorem proj1_eq_map :
    proj1 N₁ N₂ Y hc = ((Y.subgroupOf (N₁ ⊔ N₂)).map (pr₁ hc hd)).map N₁.subtype := by
  ext a
  rw [mem_proj1]
  constructor
  · rintro ⟨ha, b, hb, hab⟩
    have hJ : a * b ∈ N₁ ⊔ N₂ := Subgroup.mul_mem_sup ha hb
    exact ⟨⟨a, ha⟩, ⟨⟨a * b, hJ⟩, Subgroup.mem_subgroupOf.mpr hab,
      (pr_eq hc hd (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) rfl).1⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(pr₁ hc hd y).2, (pr₂ hc hd y : X), (pr₂ hc hd y).2, ?_⟩
    show ((pr₁ hc hd y : ↥N₁) : X) * _ ∈ Y
    rw [pr_mul]
    exact Subgroup.mem_subgroupOf.mp hy

theorem proj1_le : proj1 N₁ N₂ Y hc ≤ N₁ := fun _ ha => ha.1

theorem inf_le_proj1 : Y ⊓ N₁ ≤ proj1 N₁ N₂ Y hc := fun a ha =>
  ⟨ha.2, 1, N₂.one_mem, by rw [mul_one]; exact ha.1⟩

theorem proj1_mono {Y' : Subgroup X} (h : Y ≤ Y') : proj1 N₁ N₂ Y hc ≤ proj1 N₁ N₂ Y' hc :=
  fun _ ⟨ha, b, hb, hab⟩ => ⟨ha, b, hb, h hab⟩

theorem proj1_conj_mem {a : X} (ha : a ∈ proj1 N₁ N₂ Y hc) {f : X} (hf : f ∈ Y ⊓ N₁) :
    a * f * a⁻¹ ∈ Y ⊓ N₁ := by
  obtain ⟨haN, b, hb, hab⟩ := ha
  refine ⟨?_, N₁.mul_mem (N₁.mul_mem haN hf.2) (N₁.inv_mem haN)⟩
  have e : a * f * a⁻¹ = (a * b) * f * (a * b)⁻¹ := by
    have h1 := hc f hf.2 b hb
    calc a * f * a⁻¹ = a * (f * b) * b⁻¹ * a⁻¹ := by group
      _ = a * (b * f) * b⁻¹ * a⁻¹ := by rw [h1]
      _ = (a * b) * f * (a * b)⁻¹ := by group
  rw [e]
  exact Y.mul_mem (Y.mul_mem hab hf.1) (Y.inv_mem hab)

include hd in
theorem commutator_proj1 (hY : ⁅Y, Y⁆ = Y) (hYJ : Y ≤ N₁ ⊔ N₂) :
    ⁅proj1 N₁ N₂ Y hc, proj1 N₁ N₂ Y hc⁆ = proj1 N₁ N₂ Y hc := by
  set J := N₁ ⊔ N₂ with hJ
  set Y' := Y.subgroupOf J with hY'
  have hY'm : Y'.map J.subtype = Y := Subgroup.map_subgroupOf_eq_of_le hYJ
  have hY'p : ⁅Y', Y'⁆ = Y' := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_commutator, hY'm, hY]
  rw [proj1_eq_map hc hd, ← hY', ← Subgroup.map_commutator, ← Subgroup.map_commutator, hY'p]

include hd in
theorem card_eq_card_proj1_mul [Finite X] (hYJ : Y ≤ N₁ ⊔ N₂) :
    Nat.card Y = Nat.card (proj1 N₁ N₂ Y hc) * Nat.card ↥(Y ⊓ N₂) := by
  set f : ↥Y →* ↥N₁ := (pr₁ hc hd).comp (Subgroup.inclusion hYJ) with hf
  have hker : f.ker.map Y.subtype = Y ⊓ N₂ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : pr₁ hc hd (Subgroup.inclusion hYJ y) = 1 := hy
      have h2 := pr_mul hc hd (Subgroup.inclusion hYJ y)
      rw [h1] at h2
      refine ⟨y.2, ?_⟩
      have e : (y : X) = ((pr₂ hc hd (Subgroup.inclusion hYJ y) : ↥N₂) : X) := by
        rw [OneMemClass.coe_one, one_mul] at h2
        rw [h2]
        rfl
      rw [Subgroup.coe_subtype, e]
      exact (pr₂ hc hd _).2
    · rintro ⟨hxY, hxN⟩
      refine ⟨⟨x, hxY⟩, ?_, rfl⟩
      have h := pr_eq hc hd (x := Subgroup.inclusion hYJ ⟨x, hxY⟩) (a := 1) (b := ⟨x, hxN⟩)
        (by simp)
      exact h.1
  have hrange : f.range.map N₁.subtype = proj1 N₁ N₂ Y hc := by
    rw [proj1_eq_map hc hd, hf, MonoidHom.range_comp]
    congr 2
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr z.2
    · intro hy
      exact ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
  rw [h1, ← hker, ← hrange, Subgroup.card_map_of_injective N₁.subtype_injective,
    Subgroup.card_map_of_injective Y.subtype_injective]

end Prod

section PSL2

theorem not_isCyclic_of_card_four {E : Type*} [Group E] (h4 : Nat.card E = 4)
    (h2 : ∀ e : E, e ^ 2 = 1) : ¬ IsCyclic E := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h := orderOf_dvd_of_pow_eq_one (h2 g)
  rw [hg, h4] at h
  exact absurd h (by decide)

theorem false_of_injective_isCyclic {Q C : Type*} [Group Q] [Group C] [IsCyclic C]
    {E : Subgroup Q} (h4 : Nat.card E = 4) (h2 : ∀ e ∈ E, e ^ 2 = 1) (f : ↥E →* C)
    (hf : Function.Injective f) : False :=
  not_isCyclic_of_card_four h4 (fun e => Subtype.ext (by simpa using h2 e e.2))
    (isCyclic_of_injective f hf)

variable {p : ℕ} [hp : Fact p.Prime]

theorem eq_top_of_equiv_psl2_galoisField (hp2 : p ≠ 2)
    {Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))}
    (e : ↥Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1)) : Y = ⊤ := by
  have hF : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  have hK : Nat.card (GaloisField p 1) = p ^ 1 := GaloisField.card p 1 one_ne_zero
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hc1 := CFSG.GorensteinWalter.psl2_card_formula (GaloisField p 1)
    ⟨p, 1, hp.out, hodd, le_rfl, hK⟩
  have hc2 := CFSG.GorensteinWalter.psl2_card_formula (ZMod p) ⟨p, 1, hp.out, hodd, le_rfl, hF⟩
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_congr e.toEquiv, hc1, hc2, hK, hF]

theorem card_dvd_three_of_pow_three (hp5 : 5 ≤ p)
    {Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))}
    (hY : ∀ y ∈ Y, y ^ 3 = 1) : Nat.card Y ∣ 3 := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have h3 : IsPGroup 3 Y := fun y => ⟨1, by rw [pow_one]; exact Subtype.ext (hY y y.2)⟩
  obtain ⟨b, hb⟩ := h3.exists_card_eq
  have hF : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  have hcyc : IsCyclic Y → Nat.card Y ∣ 3 := fun _ => by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Y)
    rw [← hg]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (hY g g.2))
  have hnq : ∀ q : ℕ, q.Prime → q ≠ 3 → ¬ q ∣ Nat.card Y := fun q hq hq3 h => by
    rw [hb] at h
    exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h))
  have h2 : ¬ 2 ∣ Nat.card Y := hnq 2 Nat.prime_two (by norm_num)
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification hF Y with
    hel | ⟨z, -, -, hc⟩ | ⟨z, -, hz, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, N, C, -, hNel, hNc, hC, -, -, hsup⟩ | ⟨m, -, hmf, ⟨e⟩⟩ | ⟨m, hm, hmf, -⟩
  ·
    have hP : IsPGroup p Y := @IsElementaryAbelian.isPGroup p Y _ hel
    obtain ⟨a, ha⟩ := hP.exists_card_eq
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [ha, h0, pow_zero]
      exact one_dvd 3
    · exact absurd (ha ▸ dvd_pow_self p (by omega)) (hnq p hp.out hp3)
  · exact hcyc hc
  · exact absurd ⟨z, hz⟩ h2
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h2
    exact absurd (by decide) h2
  · rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin] at h2
    exact absurd (by decide) h2
  · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h2
    exact absurd (by decide) h2
  ·
    have hNdvd : Nat.card N ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card N
    have hm0 : m = 0 := by
      by_contra hm0
      rw [hNc] at hNdvd
      exact hnq p hp.out hp3 ((dvd_pow_self p hm0).trans hNdvd)
    have hNbot : N = ⊥ := by
      rw [hm0, pow_zero] at hNc
      exact Subgroup.eq_bot_of_card_eq N hNc
    rw [hNbot, bot_sup_eq] at hsup
    subst hsup
    exact hcyc (isCyclic_of_surjective Subgroup.topEquiv.toMonoidHom
      Subgroup.topEquiv.surjective)
  · have hm1 : m = 1 := Nat.dvd_one.mp hmf
    subst hm1
    have htop := eq_top_of_equiv_psl2_galoisField hp2 e
    have hpY : p ∣ Nat.card Y := by
      rw [htop, Subgroup.card_top]
      exact CFSG.Quasithin.L139A5.p_dvd_card_psl2 hp2
    exact absurd hpY (hnq p hp.out hp3)
  · exfalso
    have := Nat.le_of_dvd one_pos hmf
    omega

theorem dihedral_false {z : ℕ} [NeZero z] {E : Subgroup (DihedralGroup z)} (h4 : Nat.card E = 4)
    (h2 : ∀ e ∈ E, e ^ 2 = 1) {c : DihedralGroup z} (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1)
    (hcE : c ∈ Subgroup.normalizer (E : Set (DihedralGroup z))) : False := by
  obtain ⟨j, rfl⟩ : ∃ j, c = DihedralGroup.r j := by
    cases c with
    | r j => exact ⟨j, rfl⟩
    | sr i =>
      exfalso
      apply hc1
      have h2' : (DihedralGroup.sr i : DihedralGroup z) ^ 2 = 1 := by
        rw [sq, DihedralGroup.sr_mul_self]
      calc (DihedralGroup.sr i : DihedralGroup z)
          = DihedralGroup.sr i ^ 3 * (DihedralGroup.sr i ^ 2)⁻¹ := by group
        _ = 1 := by rw [hc3, h2', inv_one, mul_one]
  obtain ⟨i, hi⟩ : ∃ i, DihedralGroup.sr i ∈ E := by
    by_contra hno
    push Not at hno
    have hle : E ≤ Subgroup.zpowers (DihedralGroup.r 1) := by
      intro x hx
      cases x with
      | r k =>
        refine ⟨(k.val : ℤ), ?_⟩
        show DihedralGroup.r 1 ^ ((k.val : ℕ) : ℤ) = _
        rw [zpow_natCast, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
      | sr k => exact absurd hx (hno k)
    have := Subgroup.isCyclic_of_le hle
    exact not_isCyclic_of_card_four h4 (fun e => Subtype.ext (by simpa using h2 e e.2)) this
  have hconj := (Subgroup.mem_normalizer_iff.mp hcE _).mp hi
  rw [DihedralGroup.r_mul_sr, DihedralGroup.inv_r, DihedralGroup.sr_mul_r] at hconj
  have hprod := E.mul_mem hi hconj
  rw [DihedralGroup.sr_mul_sr] at hprod
  have hsq := h2 _ hprod
  rw [sq, DihedralGroup.r_mul_r, DihedralGroup.one_def] at hsq
  have h4j := DihedralGroup.r.inj hsq
  rw [DihedralGroup.r_pow, DihedralGroup.one_def] at hc3
  have h3j := DihedralGroup.r.inj hc3
  push_cast at h3j
  have hj : j = 0 := by linear_combination -h4j - h3j
  exact hc1 (by rw [hj, DihedralGroup.one_def])

theorem card_eq_twelve_or_simple (hp7 : 7 ≤ p)
    (h8 : ¬ 8 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)))
    {D E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))} (hED : E ≤ D)
    (hE4 : Nat.card E = 4) (hE2 : ∀ e ∈ E, e ^ 2 = 1)
    {c : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)} (hcD : c ∈ D) (hc1 : c ≠ 1)
    (hc3 : c ^ 3 = 1) (hcE : c ∈ Subgroup.normalizer (E : Set _)) :
    Nat.card D = 12 ∨ (IsSimpleGroup D ∧ ∃ d ∈ D, ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ orderOf d = r) := by
  have hp2 : p ≠ 2 := by omega
  have hF : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  set E' := E.subgroupOf D with hE'
  have hE'4 : Nat.card E' = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hED).toEquiv]
    exact hE4
  have hE'2 : ∀ e ∈ E', e ^ 2 = 1 := fun e he =>
    Subtype.ext (by simpa using hE2 _ (Subgroup.mem_subgroupOf.mp he))
  have h4D : 4 ∣ Nat.card D := hE4 ▸ Subgroup.card_dvd_of_le hED
  have hcE' : (⟨c, hcD⟩ : ↥D) ∈ Subgroup.normalizer (E' : Set ↥D) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [hE', Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hcE x
  have hc1' : (⟨c, hcD⟩ : ↥D) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hc3' : (⟨c, hcD⟩ : ↥D) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification hF D with
    hel | ⟨z, -, -, hcyc⟩ | ⟨z, -, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, N, C, hN, hNel, -, hC, -, -, hsup⟩ | ⟨m, -, hmf, ⟨e⟩⟩ | ⟨m, hm, hmf, -⟩
  ·
    exfalso
    have hP : IsPGroup p D := @IsElementaryAbelian.isPGroup p D _ hel
    obtain ⟨a, ha⟩ := hP.exists_card_eq
    have h2 : 2 ∣ p ^ a := ha ▸ (dvd_trans (by norm_num : 2 ∣ 4) h4D)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp (Nat.prime_two.dvd_of_dvd_pow h2)
    omega
  · have := hcyc
    exact (not_isCyclic_of_card_four hE'4 (fun e => Subtype.ext (by simpa using hE'2 e e.2))
      inferInstance).elim
  ·
    exfalso
    have hz0 : NeZero z := ⟨by
      rintro rfl
      rw [mul_zero] at hz
      exact absurd hz Nat.card_pos.ne'⟩
    refine dihedral_false (E := E'.map e.toMonoidHom) ?_ ?_ (c := e ⟨c, hcD⟩) ?_ ?_ ?_
    · rw [Subgroup.card_map_of_injective e.injective]
      exact hE'4
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE'2 x hx, map_one]
    · rwa [Ne, MulEquiv.map_eq_one_iff]
    · rw [← map_pow, hc3', map_one]
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      obtain ⟨x, rfl⟩ := e.surjective y
      constructor
      · rintro ⟨w, hw, hwx⟩
        have hwx' : w = x := e.injective hwx
        subst hwx'
        refine ⟨_, (Subgroup.mem_normalizer_iff.mp hcE' w).mp hw, ?_⟩
        simp
      · rintro ⟨w, hw, hwx⟩
        have hw' : w = ⟨c, hcD⟩ * x * (⟨c, hcD⟩ : ↥D)⁻¹ := by
          apply e.injective
          rw [map_mul, map_mul, map_inv]
          exact hwx
        rw [hw'] at hw
        exact ⟨x, (Subgroup.mem_normalizer_iff.mp hcE' x).mpr hw, rfl⟩
  · left
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  · exfalso
    apply h8
    have h24 : Nat.card D = 24 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      rfl
    exact (show 8 ∣ Nat.card D by rw [h24]; norm_num).trans (Subgroup.card_subgroup_dvd_card D)
  · right
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    refine ⟨e.isSimpleGroup, ?_⟩
    have h5 : 5 ∣ Nat.card D := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 5 h5
    exact ⟨d, d.2, 5, by norm_num, le_rfl, by rw [Subgroup.orderOf_coe]; exact hd⟩
  ·
    exfalso
    have : IsCyclic (↥D ⧸ N) := by
      refine isCyclic_of_surjective ((QuotientGroup.mk' N).comp C.subtype) ?_
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
      have hx : x ∈ ((N ⊔ C : Subgroup ↥D) : Set ↥D) := by rw [hsup]; trivial
      rw [Subgroup.normal_mul] at hx
      obtain ⟨y, hy, w, hw, rfl⟩ := hx
      refine ⟨⟨w, hw⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      have h1 := hN.conj_mem y hy w⁻¹
      simpa [mul_assoc] using h1
    refine false_of_injective_isCyclic hE'4 hE'2 ((QuotientGroup.mk' N).comp E'.subtype) ?_
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : ↥D) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    have hxp : (x : ↥D) ^ p = 1 := by
      have := @elemPow_eq_one_of_isElementaryAbelian p _ _ N hNel (x : ↥D) hxN
      exact this
    have hx2 : (x : ↥D) ^ 2 = 1 := hE'2 _ x.2
    have hg : Nat.gcd 2 p = 1 :=
      Nat.coprime_two_left.mpr (hp.out.odd_of_ne_two hp2)
    have h1 : (x : ↥D) ^ Nat.gcd 2 p = 1 := pow_gcd_eq_one.mpr ⟨hx2, hxp⟩
    rw [hg, pow_one] at h1
    exact Subtype.ext h1
  ·
    right
    have hm1 : m = 1 := Nat.dvd_one.mp hmf
    subst hm1
    have htop := eq_top_of_equiv_psl2_galoisField hp2 e
    subst htop
    have := CFSG.Quasithin.Vol2.Ch11.SecB.isSimpleGroup_psl2 (p := p) (by omega)
    refine ⟨Subgroup.topEquiv.isSimpleGroup, ?_⟩
    have hpD : p ∣
        Nat.card (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) := by
      rw [Subgroup.card_top]
      exact CFSG.Quasithin.L139A5.p_dvd_card_psl2 hp2
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥(⊤ : Subgroup _)) p hpD
    exact ⟨d, d.2, p, hp.out, by omega, by rw [Subgroup.orderOf_coe]; exact hd⟩
  · exfalso
    have := Nat.le_of_dvd one_pos hmf
    omega

end PSL2

section Orders

theorem mul_sq_sub_one_ne_of_lt {a M : ℕ} (h1 : a * (a ^ 2 - 1) < M)
    (h2 : M < (a + 1) * ((a + 1) ^ 2 - 1)) (q : ℕ) : q * (q ^ 2 - 1) ≠ M := by
  have hmono : ∀ x y : ℕ, x ≤ y → x * (x ^ 2 - 1) ≤ y * (y ^ 2 - 1) := fun x y h =>
    Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)
  intro hq
  rcases le_or_gt q a with h | h
  · have := hmono q a h
    omega
  · have := hmono (a + 1) q h
    omega

theorem mul_sq_sub_one_ne {p : ℕ} (hp7 : 7 ≤ p) :
    p * (p ^ 2 - 1) ≠ 2 * 60 ∧ p * (p ^ 2 - 1) ≠ 2 * 62400 ∧ p * (p ^ 2 - 1) ≠ 2 * 20160 ∧
      p * (p ^ 2 - 1) ≠ 2 * 979200 := by
  refine ⟨fun h => ?_, mul_sq_sub_one_ne_of_lt (a := 49) (by norm_num) (by norm_num) p,
    mul_sq_sub_one_ne_of_lt (a := 34) (by norm_num) (by norm_num) p,
    mul_sq_sub_one_ne_of_lt (a := 125) (by norm_num) (by norm_num) p⟩
  have h7 : 7 * (7 ^ 2 - 1) ≤ p * (p ^ 2 - 1) :=
    Nat.mul_le_mul hp7 (Nat.sub_le_sub_right (Nat.pow_le_pow_left hp7 2) 1)
  omega

theorem card_lie_two {Y : Type} [Group Y]
    (h : E2.IsBenderOf 2 Y ∨ IsPSL 3 2 2 Y ∨ IsPSp4 2 2 Y) :
    Nat.card Y = 60 ∨ Nat.card Y = 62400 ∨ Nat.card Y = 20160 ∨ Nat.card Y = 979200 := by
  rcases h with ⟨-, hL | hS | hU⟩ | hL | hS
  · left
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hL).1 rfl]
    decide
  · exfalso
    obtain ⟨-, a, -, -, -, -, hf, -⟩ := hS
    omega
  · right; left
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hU).2.1 rfl]
    decide
  · right; right; left
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hL).1 rfl]
    decide
  · right; right; right
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hS).2.2.1 rfl]
    decide

theorem five_dvd_card_lie_two {Y : Type} [Group Y]
    (h : E2.IsBenderOf 2 Y ∨ IsPSL 3 2 2 Y ∨ IsPSp4 2 2 Y) : 5 ∣ Nat.card Y := by
  rcases card_lie_two h with h | h | h | h <;> rw [h] <;> norm_num

end Orders

end CFSG.Quasithin.H13.Ch8310P

module

public import CFSG.RankThree.GF2n.Tim78S31Split
public import CFSG.RankThree.GF2n.Tim78C4C4
public import CFSG.RankThree.GF2n.Tim78S31Model

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem comm_of_mul_mul_self {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * (a * b) = 1) : a * b = b * a := by
  calc a * b = (a * b) * (a * (b * b) * a) := by rw [hb, mul_one, ha, mul_one]
    _ = ((a * b) * (a * b)) * (b * a) := by group
    _ = b * a := by rw [hab, one_mul]

omit [Finite G] in
theorem iSup_isElemAbelian {ι : Type*} (S : ι → Subgroup G) (hS : ∀ i, ∀ x ∈ S i, x * x = 1)
    (hc : ∀ i j, ∀ a ∈ S i, ∀ b ∈ S j, a * b = b * a) :
    Assembly.IsElemAbelian 2 (⨆ i, S i) := by
  have h1 : ∀ i, (⨆ j, S j) ≤ Subgroup.centralizer (S i : Set G) := fun i =>
    iSup_le fun j y hy => Subgroup.mem_centralizer_iff.mpr fun x hx => hc i j x hx y hy
  have h2 : (⨆ j, S j) ≤ Subgroup.centralizer ((⨆ j, S j : Subgroup G) : Set G) :=
    iSup_le fun i x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (h1 i hy) x hx).symm
  have hab : ∀ x ∈ ⨆ i, S i, ∀ y ∈ ⨆ i, S i, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (h2 hy) x hx
  let E : Subgroup G :=
    { carrier := {z | z ∈ ⨆ i, S i ∧ z * z = 1}
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hab b hb.1 a ha.1]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by
        rw [← mul_inv_rev, ha.2, inv_one]⟩ }
  have hE : (⨆ i, S i) ≤ E := iSup_le fun i z hz => ⟨Subgroup.mem_iSup_of_mem i hz, hS i z hz⟩
  refine ⟨⟨⟨fun a b => Subtype.ext (hab _ a.2 _ b.2)⟩⟩, fun z hz => ?_⟩
  rw [sq]
  exact (hE hz).2

omit [Finite G] in
theorem mul_self_of_mem_conj {V : Subgroup G} (hVe : ∀ v ∈ V, v * v = 1) {k a : G}
    (ha : a ∈ conjSubgroup k V) : a * a = 1 := by
  have h := hVe _ (mem_conjSubgroup.mp ha)
  calc a * a = k * ((k⁻¹ * a * k) * (k⁻¹ * a * k)) * k⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem comm_of_commute_conj {V : Subgroup G} (hV : IsRootTypeTI V) {g h x y : G}
    (hx : x ∈ conjSubgroup g V) (hx1 : x ≠ 1) (hy : y ∈ conjSubgroup h V) (hy1 : y ≠ 1)
    (hxy : x * y = y * x) : ∀ a ∈ conjSubgroup g V, ∀ b ∈ conjSubgroup h V, a * b = b * a := by
  refine commute_of_isRootTypeTI hV fun hbot => hx1 ?_
  have hN : x ∈ Subgroup.normalizer (conjSubgroup h V : Set G) :=
    Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hV.1 h) hy hy1 hxy
  have : x ∈ conjSubgroup g V ⊓ Subgroup.normalizer (conjSubgroup h V : Set G) := ⟨hx, hN⟩
  rwa [hbot, Subgroup.mem_bot] at this

theorem orderOf_mul_eq_four_left {V : Subgroup G} (hVe : ∀ v ∈ V, v * v = 1)
    (hV : IsRootTypeTI V) {g h d e : G} (hd : d ∈ conjSubgroup g V) (hd1 : d ≠ 1)
    (he : e ∈ conjSubgroup h V) (hde : orderOf (d * e) = 4) {x : G}
    (hx : x ∈ conjSubgroup g V) (hx1 : x ≠ 1) : orderOf (x * e) = 4 := by
  have hee := mul_self_of_mem_conj hVe he
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hconj : ∀ a ∈ conjSubgroup g V, e * a * e⁻¹ ∈ conjSubgroup (e * g) V := fun a ha => by
    rw [conjSubgroup_mul, mem_conjSubgroup, show e⁻¹ * (e * a * e⁻¹) * e = a by group]
    exact ha
  have hne1 : ∀ a : G, a ≠ 1 → e * a * e⁻¹ ≠ 1 := fun a ha h' => ha (by
    calc a = e⁻¹ * (e * a * e⁻¹) * e := by group
      _ = 1 := by rw [h']; group)
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [mul_one] at hde
    have := orderOf_dvd_of_pow_eq_one (show d ^ 2 = 1 by rw [sq]; exact mul_self_of_mem_conj hVe hd)
    rw [hde] at this
    exact absurd this (by norm_num)
  have hgne : conjSubgroup (e * g) V ≠ conjSubgroup g V := by
    intro heq
    have hN : e ∈ Subgroup.normalizer (conjSubgroup g V : Set G) := by
      rw [← conjSubgroup_eq_self_iff, ← conjSubgroup_mul]
      exact heq
    have hc := commute_of_isRootTypeTI hV (g := h) (h := g) (fun hbot => he1 (by
      have : e ∈ conjSubgroup h V ⊓ Subgroup.normalizer (conjSubgroup g V : Set G) := ⟨he, hN⟩
      rwa [hbot, Subgroup.mem_bot] at this)) e he d hd
    have h2 : (d * e) ^ 2 = 1 := by
      rw [sq, show d * e * (d * e) = d * (e * d) * e by group, hc,
        show d * (d * e) * e = (d * d) * (e * e) by group, mul_self_of_mem_conj hVe hd, hee,
        one_mul]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hde] at this
    exact absurd this (by norm_num)
  have hdd : d * (e * d * e⁻¹) = (e * d * e⁻¹) * d := by
    refine comm_of_mul_mul_self (mul_self_of_mem_conj hVe hd)
      (mul_self_of_mem_conj hVe (hconj d hd)) ?_
    have e1 : d * (e * d * e⁻¹) = (d * e) ^ 2 := by
      rw [hei, sq]
      group
    rw [e1, ← sq, ← pow_mul, show 2 * 2 = orderOf (d * e) by rw [hde]]
    exact pow_orderOf_eq_one _
  have hcomm := comm_of_commute_conj hV hd hd1 (hconj d hd) (hne1 d hd1) hdd
  have hxx := hcomm x hx _ (hconj x hx)
  have hsq1 : (x * (e * x * e⁻¹)) * (x * (e * x * e⁻¹)) = 1 := by
    calc (x * (e * x * e⁻¹)) * (x * (e * x * e⁻¹)) =
        x * ((e * x * e⁻¹) * x) * (e * x * e⁻¹) := by group
      _ = x * (x * (e * x * e⁻¹)) * (e * x * e⁻¹) := by rw [hxx]
      _ = (x * x) * ((e * x * e⁻¹) * (e * x * e⁻¹)) := by group
      _ = 1 := by rw [mul_self_of_mem_conj hVe hx, mul_self_of_mem_conj hVe (hconj x hx), one_mul]
  have hxne : x * (e * x * e⁻¹) ≠ 1 := by
    intro h1
    have hxe : e * x * e⁻¹ = x := by
      calc e * x * e⁻¹ = x⁻¹ * (x * (e * x * e⁻¹)) := by group
        _ = x := by rw [h1, mul_one, inv_eq_of_mul_eq_one_right (mul_self_of_mem_conj hVe hx)]
    apply hgne
    refine conjSubgroup_eq_of_inf_ne_bot hV.1 fun hbot => hx1 ?_
    have : x ∈ conjSubgroup (e * g) V ⊓ conjSubgroup g V :=
      Subgroup.mem_inf.mpr ⟨by rw [← hxe]; exact hconj x hx, hx⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have h2 : orderOf ((x * e) ^ 2) = 2 ^ 1 := by
    have e1 : (x * e) ^ 2 = x * (e * x * e⁻¹) := by
      rw [hei, sq]
      group
    rw [e1, pow_one]
    exact orderOf_eq_prime (by rw [sq]; exact hsq1) hxne
  have := orderOf_eq_of_orderOf_sq (le_refl 1) h2
  rw [this]
  norm_num

theorem orderOf_mul_eq_four {V : Subgroup G} (hVe : ∀ v ∈ V, v * v = 1)
    (hV : IsRootTypeTI V) {g h d e : G} (hd : d ∈ conjSubgroup g V) (hd1 : d ≠ 1)
    (he : e ∈ conjSubgroup h V) (he1 : e ≠ 1) (hde : orderOf (d * e) = 4) {x y : G}
    (hx : x ∈ conjSubgroup g V) (hx1 : x ≠ 1) (hy : y ∈ conjSubgroup h V) (hy1 : y ≠ 1) :
    orderOf (x * y) = 4 := by
  have h1 := orderOf_mul_eq_four_left hVe hV hd hd1 he hde hx hx1
  have h2 : orderOf (e * x) = 4 := by
    rw [orderOf_mul_comm']
    exact h1
  have h3 := orderOf_mul_eq_four_left hVe hV he he1 hx h2 hy hy1
  rw [orderOf_mul_comm']
  exact h3

omit [Finite G] in
theorem exists_pair_four {V : Subgroup G} (hVe : ∀ v ∈ V, v * v = 1) {R : Subgroup G}
    (hR : IsPGroup 2 R) {g h : G} (hgR : conjSubgroup g V ≤ R) (hhR : conjSubgroup h V ≤ R)
    (hnc : ¬ ∀ a ∈ conjSubgroup g V, ∀ b ∈ conjSubgroup h V, a * b = b * a) :
    ∃ g' h' : G, conjSubgroup g' V ≤ R ∧ conjSubgroup h' V ≤ R ∧
      ∃ d ∈ conjSubgroup g' V, d ≠ 1 ∧ ∃ e ∈ conjSubgroup h' V, e ≠ 1 ∧
        orderOf (d * e) = 4 := by
  simp only [not_forall] at hnc
  obtain ⟨d, hd, e, he, hde⟩ := hnc
  have hdd := mul_self_of_mem_conj hVe hd
  have key : ∀ m : ℕ, 2 ≤ m → ∀ h e : G, conjSubgroup h V ≤ R → e ∈ conjSubgroup h V →
      orderOf (d * e) = 2 ^ m →
      ∃ g' h' : G, conjSubgroup g' V ≤ R ∧ conjSubgroup h' V ≤ R ∧
        ∃ d ∈ conjSubgroup g' V, d ≠ 1 ∧ ∃ e ∈ conjSubgroup h' V, e ≠ 1 ∧
          orderOf (d * e) = 4 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro hm h e hhR he hord
    have hee := mul_self_of_mem_conj hVe he
    by_cases hm2 : m = 2
    · subst hm2
      refine ⟨g, h, hgR, hhR, d, hd, ?_, e, he, ?_, by rw [hord]; norm_num⟩
      · rintro rfl
        rw [one_mul] at hord
        have := orderOf_dvd_of_pow_eq_one (show e ^ 2 = 1 by rw [sq]; exact hee)
        rw [hord] at this
        exact absurd this (by norm_num)
      · rintro rfl
        rw [mul_one] at hord
        have := orderOf_dvd_of_pow_eq_one (show d ^ 2 = 1 by rw [sq]; exact hdd)
        rw [hord] at this
        exact absurd this (by norm_num)
    ·
      have heR : e ∈ R := hhR he
      have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
      have hR' : conjSubgroup (e * g) V ≤ R := by
        intro z hz
        rw [conjSubgroup_mul, mem_conjSubgroup] at hz
        have := hgR hz
        rw [show z = e * (e⁻¹ * z * e) * e⁻¹ by group]
        exact R.mul_mem (R.mul_mem heR this) (R.inv_mem heR)
      have hde' : e * d * e⁻¹ ∈ conjSubgroup (e * g) V := by
        rw [conjSubgroup_mul, mem_conjSubgroup, show e⁻¹ * (e * d * e⁻¹) * e = d by group]
        exact hd
      have hord' : orderOf (d * (e * d * e⁻¹)) = 2 ^ (m - 1) := by
        have e1 : d * (e * d * e⁻¹) = (d * e) ^ 2 := by
          rw [hei, sq]
          group
        rw [e1]
        exact orderOf_sq_of_orderOf_eq (by omega) hord
      exact ih (m - 1) (by omega) (by omega) _ _ hR' hde' hord'
  have hdeR : d * e ∈ R := R.mul_mem (hgR hd) (hhR he)
  obtain ⟨k, hk⟩ := hR ⟨d * e, hdeR⟩
  have hk' : (d * e) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  have hee := mul_self_of_mem_conj hVe he
  refine key m ?_ h e hhR he hm
  by_contra hm2
  apply hde
  rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
  · rw [pow_zero, orderOf_eq_one_iff] at hm
    have : e = d := by
      calc e = d⁻¹ * (d * e) := by group
        _ = d := by rw [hm, mul_one, inv_eq_of_mul_eq_one_right hdd]
    rw [this]
  · refine comm_of_mul_mul_self hdd hee ?_
    rw [← sq, ← pow_one 2, ← hm]
    exact pow_orderOf_eq_one _

theorem tim78_3_1_core (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {B₁ : Subgroup G} (hBc : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y = y * x) (hB2 : IsPGroup 2 B₁)
    (hBti : IsTI B₁) (hexp : ∀ x ∈ B₁, x ^ 4 = 1) (hne : PartTwo.omegaOneSub B₁ ≠ B₁)
    (h4 : 4 ≤ Nat.card ↥(PartTwo.omegaOneSub B₁)) {R : Subgroup G} (hR : IsPGroup 2 R) :
    Assembly.IsElemAbelian 2 (⨆ g : {g : G // conjSubgroup g (PartTwo.omegaOneSub B₁) ≤ R},
      conjSubgroup (g : G) (PartTwo.omegaOneSub B₁)) ∨
    (Nat.card ↥(PartTwo.omegaOneSub B₁) = 4 ∧ (PartTwo.omegaOneSub B₁).relIndex B₁ = 4 ∧
      ∃ g : G, ∃ _ : ((PartTwo.omegaOneSub B₁ ⊔ PartTwo.omegaOneSub (conjSubgroup g B₁)).subgroupOf
        (B₁ ⊔ conjSubgroup g B₁)).Normal,
        Nonempty (↥(B₁ ⊔ conjSubgroup g B₁) ⧸
          (PartTwo.omegaOneSub B₁ ⊔ PartTwo.omegaOneSub (conjSubgroup g B₁)).subgroupOf
            (B₁ ⊔ conjSubgroup g B₁) ≃* PSL(2, GaloisField 2 2))) := by
  classical
  have hVe : ∀ v ∈ PartTwo.omegaOneSub B₁, v * v = 1 := fun v hv =>
    ((mem_omegaOneSub_iff hBc).mp hv).2
  have hexp_ne : ∃ x ∈ B₁, x ^ 2 ≠ 1 := by
    obtain ⟨x, hx, hxV⟩ : ∃ x ∈ B₁, x ∉ PartTwo.omegaOneSub B₁ := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      exact hne (le_antisymm (PartTwo.omegaOneSub_le B₁) hcon)
    exact ⟨x, hx, fun h2 => hxV ((mem_omegaOneSub_iff hBc).mpr ⟨hx, by rw [← sq]; exact h2⟩)⟩
  have hB1 : B₁ ≠ ⊥ := by
    intro h
    obtain ⟨x, hx, hx2⟩ := hexp_ne
    rw [h, Subgroup.mem_bot] at hx
    rw [hx, one_pow] at hx2
    exact hx2 rfl
  have Sx : Setup210 B₁ B₁ :=
    { comm := hBc
      two := hB2
      exp_ne := hexp_ne
      ti := hBti
      conj := ⟨1, (conjSubgroup_one B₁).symm⟩
      ne_bot := by
        rw [inf_of_le_left Subgroup.le_normalizer]
        exact hB1 }
  have hroot := (tim78_2_10_a hCen hU Sx).2
  by_cases hall : ∀ g h : G, conjSubgroup g (PartTwo.omegaOneSub B₁) ≤ R →
      conjSubgroup h (PartTwo.omegaOneSub B₁) ≤ R →
      ∀ a ∈ conjSubgroup g (PartTwo.omegaOneSub B₁), ∀ b ∈ conjSubgroup h (PartTwo.omegaOneSub B₁),
        a * b = b * a
  · left
    exact iSup_isElemAbelian _ (fun i v hv => mul_self_of_mem_conj hVe hv)
      (fun i j => hall i j i.2 j.2)
  · right
    simp only [not_forall] at hall
    obtain ⟨g, h, hgR, hhR, hnc⟩ := hall
    obtain ⟨g', h', -, -, d, hd, hd1, e, he, he1, hde⟩ :=
      exists_pair_four hVe hR hgR hhR (by simpa only [not_forall] using hnc)
    have K : Core31 B₁ (h'⁻¹ * g') :=
      { comm := hBc
        two := hB2
        ti := hBti
        exp := hexp
        exp_ne := hexp_ne
        card4 := h4
        ord := by
          intro a ha ha1 b hb hb1
          rw [omegaOneSub_conj hBc, mem_conjSubgroup] at ha
          have ha' : h' * a * h'⁻¹ ∈ conjSubgroup g' (PartTwo.omegaOneSub B₁) := by
            rw [mem_conjSubgroup, show g'⁻¹ * (h' * a * h'⁻¹) * g' =
              (h'⁻¹ * g')⁻¹ * a * (h'⁻¹ * g') by group]
            exact ha
          have hb' : h' * b * h'⁻¹ ∈ conjSubgroup h' (PartTwo.omegaOneSub B₁) := by
            rw [mem_conjSubgroup, show h'⁻¹ * (h' * b * h'⁻¹) * h' = b by group]
            exact hb
          have hne1 : ∀ z : G, z ≠ 1 → h' * z * h'⁻¹ ≠ 1 := fun z hz h1 => hz (by
            calc z = h'⁻¹ * (h' * z * h'⁻¹) * h' := by group
              _ = 1 := by rw [h1]; group)
          have h1 := orderOf_mul_eq_four hVe hroot hd hd1 he he1 hde ha' (hne1 a ha1) hb'
            (hne1 b hb1)
          rw [show h' * a * h'⁻¹ * (h' * b * h'⁻¹) = h' * (a * b) * h'⁻¹ by group,
            ← MulAut.conj_apply, MulEquiv.orderOf_eq] at h1
          exact h1 }
    obtain ⟨α, hα, hα1, hnc', x, hx, hxC⟩ := K.exists_data31 hCen hU
    have D : Data31 B₁ (h'⁻¹ * g') α x := ⟨K, hα, hα1, hnc', hx, hxC⟩
    obtain ⟨f, hf, hrel, hN, ⟨e'⟩⟩ := D.linear hCen hU
    rcases (show f = 2 ∨ 3 ≤ f by omega) with rfl | hf3
    · exact ⟨by rw [D.card_eq hCen hU, hrel]; norm_num, by rw [hrel]; norm_num, α, hN, ⟨e'⟩⟩
    · exact (D.false_of_linear hCen hU hf3 hrel e').elim

theorem tim78_3_1_of_isPGroup (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {B₁ : Subgroup G} (hBc : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y = y * x) (hB2 : IsPGroup 2 B₁)
    (hBti : IsTI B₁) (hexp : ∀ x ∈ B₁, x ^ 4 = 1) (hne : PartTwo.omegaOneSub B₁ ≠ B₁)
    (h4 : 4 ≤ Nat.card ↥(PartTwo.omegaOneSub B₁)) {R : Subgroup G} (hR : IsPGroup 2 R) :
    Assembly.IsElemAbelian 2 (⨆ g : {g : G // conjSubgroup g (PartTwo.omegaOneSub B₁) ≤ R},
      conjSubgroup (g : G) (PartTwo.omegaOneSub B₁)) ∨
    (Nonempty (↥B₁ ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧
      ∃ g : G, ∃ _ : ((PartTwo.omegaOneSub B₁ ⊔ PartTwo.omegaOneSub (conjSubgroup g B₁)).subgroupOf
        (B₁ ⊔ conjSubgroup g B₁)).Normal,
        Nonempty (↥(B₁ ⊔ conjSubgroup g B₁) ⧸
          (PartTwo.omegaOneSub B₁ ⊔ PartTwo.omegaOneSub (conjSubgroup g B₁)).subgroupOf
            (B₁ ⊔ conjSubgroup g B₁) ≃* PSL(2, GaloisField 2 2))) := by
  rcases tim78_3_1_core hCen hU hBc hB2 hBti hexp hne h4 hR with h | ⟨hc, hrel, hrest⟩
  · exact Or.inl h
  · exact Or.inr ⟨mulEquiv_C4_C4 hBc hexp hc hrel, hrest⟩

theorem tim78_3_1_of_eight_le (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {B₁ : Subgroup G} (hBc : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y = y * x) (hB2 : IsPGroup 2 B₁)
    (hBti : IsTI B₁) (hexp : ∀ x ∈ B₁, x ^ 4 = 1) (hne : PartTwo.omegaOneSub B₁ ≠ B₁)
    (h8 : 8 ≤ Nat.card ↥(PartTwo.omegaOneSub B₁)) {R : Subgroup G} (hR : IsPGroup 2 R) :
    Assembly.IsElemAbelian 2 (⨆ g : {g : G // conjSubgroup g (PartTwo.omegaOneSub B₁) ≤ R},
      conjSubgroup (g : G) (PartTwo.omegaOneSub B₁)) := by
  rcases tim78_3_1_core hCen hU hBc hB2 hBti hexp hne (by omega) hR with h | ⟨hc, -⟩
  · exact h
  · omega

end CFSG.RankThree.GF2n.Tim78

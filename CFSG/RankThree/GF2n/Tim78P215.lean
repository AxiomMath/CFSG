module

public import CFSG.RankThree.GF2n.Tim78P214
public import CFSG.RankThree.GF2n.Tim78Critical
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitNormalFour

public section

open scoped IsMulCommutative

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G]

theorem four_le_card_omegaOneSub {B : Subgroup G} (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hB2 : IsPGroup 2 B) (hncyc : ¬ IsCyclic B) : 4 ≤ Nat.card ↥(PartTwo.omegaOneSub B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hsB, hss, hs1, t, htB, htt, ht1, hst⟩ : ∃ s ∈ B, s * s = 1 ∧ s ≠ 1 ∧
      ∃ t ∈ B, t * t = 1 ∧ t ≠ 1 ∧ s ≠ t := by
    by_contra hcon
    apply hncyc
    have : IsMulCommutative ↥B := ⟨⟨fun a b => Subtype.ext (hBc a a.2 b b.2)⟩⟩
    refine CFSG.ComponentClassification.FooteLit.isCyclic_of_unique_involution hB2
      fun x y hx hy => ?_
    by_contra h
    simp only [not_or] at h
    obtain ⟨hx1, hy1, hxy⟩ := h
    have hx' : (x : G) * x = 1 := congrArg Subtype.val (show x * x = 1 by rw [← sq]; exact hx)
    have hy' : (y : G) * y = 1 := congrArg Subtype.val (show y * y = 1 by rw [← sq]; exact hy)
    exact hcon ⟨x, x.2, hx', fun h' => hx1 (Subtype.ext h'), y, y.2, hy',
      fun h' => hy1 (Subtype.ext h'), fun h' => hxy (Subtype.ext h')⟩
  have hsL : s ∈ PartTwo.omegaOneSub B := (mem_omegaOneSub_iff hBc).mpr ⟨hsB, hss⟩
  have htL : t ∈ PartTwo.omegaOneSub B := (mem_omegaOneSub_iff hBc).mpr ⟨htB, htt⟩
  have hne2 : Nat.card ↥(PartTwo.omegaOneSub B) ≠ 2 := by
    intro h2
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(PartTwo.omegaOneSub B))).mp h2
    have e1 := hy ⟨s, hsL⟩ (fun h => hs1 (congrArg Subtype.val h))
    have e2 := hy ⟨t, htL⟩ (fun h => ht1 (congrArg Subtype.val h))
    exact hst (congrArg Subtype.val (e1.trans e2.symm))
  have hL2 : IsPGroup 2 ↥(PartTwo.omegaOneSub B) := hB2.to_le (PartTwo.omegaOneSub_le B)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hL2
  rcases n with _ | _ | n
  · exfalso
    have hbot := Subgroup.eq_bot_of_card_eq _ (by simpa using hn)
    rw [hbot] at hsL
    exact hs1 (Subgroup.mem_bot.mp hsL)
  · exact absurd (by simpa using hn) hne2
  · rw [hn]
    exact le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))

section Transport

variable {M B : Subgroup G}

omit [Finite G] in
theorem mem_conjSubgroup_subgroupOf {g x : ↥M} :
    x ∈ conjSubgroup g (B.subgroupOf M) ↔ (x : G) ∈ conjSubgroup (g : G) B := by
  rw [mem_conjSubgroup, mem_conjSubgroup, Subgroup.mem_subgroupOf]
  rfl

omit [Finite G] in
theorem omegaOneSub_subgroupOf (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    PartTwo.omegaOneSub (B.subgroupOf M) = (PartTwo.omegaOneSub B).subgroupOf M := by
  have hBc' : ∀ x ∈ B.subgroupOf M, ∀ y ∈ B.subgroupOf M, x * y = y * x := fun x hx y hy =>
    Subtype.ext (hBc _ hx _ hy)
  ext x
  rw [mem_omegaOneSub_iff hBc', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    mem_omegaOneSub_iff hBc]
  exact and_congr Iff.rfl ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

omit [Finite G] in
theorem isTI_subgroupOf
    (hTI : ∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ B ⊓ conjSubgroup g B = B) :
    IsTI (B.subgroupOf M) := by
  intro g
  rcases hTI g g.2 with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have : (x : G) ∈ B ⊓ conjSubgroup (g : G) B :=
      Subgroup.mem_inf.mpr ⟨hx1, mem_conjSubgroup_subgroupOf.mp hx2⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  · right
    refine le_antisymm inf_le_left fun x hx => Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [mem_conjSubgroup_subgroupOf]
    have hx' : (x : G) ∈ B := hx
    rw [← h] at hx'
    exact (Subgroup.mem_inf.mp hx').2

end Transport

theorem tim78_2_15 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {M : Subgroup G}
    (hF : generalizedFitting M = pCore 2 M) {B : Subgroup G} (hBM : B ≤ M)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB2 : IsPGroup 2 B)
    (hTI : ∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ B ⊓ conjSubgroup g B = B) :
    PartTwo.omegaOneSub B = B ∨ IsCyclic B ∨
      (PartTwo.omegaOneSub B ≤ inSubgroup (pCore 2) M ∧
        Assembly.IsElemAbelian 2
          (⨆ (g : G) (_ : g ∈ M), conjSubgroup g (PartTwo.omegaOneSub B))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases ha : PartTwo.omegaOneSub B = B
  · exact Or.inl ha
  by_cases hb : IsCyclic B
  · exact Or.inr (Or.inl hb)
  right
  right
  set Q := inSubgroup (pCore 2) M with hQ
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two M
  obtain ⟨x, hxB, hx2⟩ := exists_sq_ne_one hBc ha
  have hxM := hBM hxB
  have hNB : ∀ y ∈ M, ∀ c ∈ B, c ≠ 1 → y * c = c * y →
      y ∈ Subgroup.normalizer (B : Set G) := by
    intro y hy c hc hc1 hyc
    rw [← conjSubgroup_eq_self_iff]
    rcases hTI y hy with h | h
    · exfalso
      apply hc1
      have hcy : y⁻¹ * c * y = c := by
        calc y⁻¹ * c * y = y⁻¹ * (y * c) := by rw [hyc]; group
          _ = c := by group
      have : c ∈ B ⊓ conjSubgroup y B :=
        Subgroup.mem_inf.mpr ⟨hc, by rw [mem_conjSubgroup, hcy]; exact hc⟩
      rwa [h, Subgroup.mem_bot] at this
    · exact (Subgroup.eq_of_le_of_card_ge (h.symm.le.trans inf_le_right)
        (card_conjSubgroup y B).le).symm
  have hBQ : B ⊓ Q ≠ ⊥ := by
    intro hBQ
    obtain ⟨k, hk⟩ := hB2 ⟨x, hxB⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hx2' : x ^ 2 ∈ B := B.pow_mem hxB 2
    have hC : Q ⊓ Subgroup.centralizer ({x} : Set G) =
        Q ⊓ Subgroup.centralizer ({x ^ 2} : Set G) := by
      apply le_antisymm
      · intro c hc
        obtain ⟨hcQ, hcC⟩ := Subgroup.mem_inf.mp hc
        rw [Subgroup.mem_centralizer_singleton_iff] at hcC
        refine Subgroup.mem_inf.mpr ⟨hcQ, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff, sq]
        calc c * (x * x) = (c * x) * x := by group
          _ = (x * c) * x := by rw [hcC]
          _ = x * (c * x) := by group
          _ = x * (x * c) := by rw [hcC]
          _ = x * x * c := by group
      · intro c hc
        obtain ⟨hcQ, hcC⟩ := Subgroup.mem_inf.mp hc
        rw [Subgroup.mem_centralizer_singleton_iff] at hcC
        refine Subgroup.mem_inf.mpr ⟨hcQ, ?_⟩
        have hcN := hNB c (hQM hcQ) (x ^ 2) hx2' hx2 hcC
        have h1 : x * c * x⁻¹ * c⁻¹ ∈ Q :=
          Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMQ hxM) c).mp hcQ) (Q.inv_mem hcQ)
        have h2 : x * c * x⁻¹ * c⁻¹ ∈ B := by
          rw [mul_assoc, mul_assoc]
          refine B.mul_mem hxB ?_
          have := (Subgroup.mem_normalizer_iff.mp hcN x⁻¹).mp (B.inv_mem hxB)
          rwa [← mul_assoc]
        have h3 : x * c * x⁻¹ * c⁻¹ ∈ B ⊓ Q := Subgroup.mem_inf.mpr ⟨h2, h1⟩
        rw [hBQ, Subgroup.mem_bot] at h3
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc c * x = (x * c * x⁻¹ * c⁻¹)⁻¹ * (x * c) := by group
          _ = x * c := by rw [h3, inv_one, one_mul]
    have hxQ := tim78_2_3 hF hxM ⟨k, hk'⟩ hC
    have : x ^ 2 ∈ B ⊓ Q := Subgroup.mem_inf.mpr ⟨hx2', hxQ⟩
    rw [hBQ, Subgroup.mem_bot] at this
    exact hx2 this
  obtain ⟨t, htBQ, ht1, htt⟩ : ∃ t ∈ B ⊓ Q, t ≠ 1 ∧ t * t = 1 := by
    have hp : IsPGroup 2 ↥(B ⊓ Q) := hB2.to_le inf_le_left
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hBQ (Subgroup.eq_bot_of_card_eq _ (by simpa using hn))
    obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(B ⊓ Q)) 2
      (by rw [hn]; exact dvd_pow_self 2 hn0)
    refine ⟨t', t'.2, fun h => ?_, ?_⟩
    · have : t' = 1 := Subtype.ext h
      rw [this, orderOf_one] at ht'
      exact absurd ht' (by norm_num)
    · have := pow_orderOf_eq_one t'
      rw [ht', sq] at this
      exact congrArg Subtype.val this
  obtain ⟨htB, htQ⟩ := Subgroup.mem_inf.mp htBQ
  set B' : Subgroup ↥M := B.subgroupOf M with hB'
  have hB'c : ∀ y ∈ B', ∀ z ∈ B', y * z = z * y := fun y hy z hz => Subtype.ext (hBc _ hy _ hz)
  have hB'2 : IsPGroup 2 B' := hB2.comap_of_injective _ Subtype.val_injective
  have hB'TI : IsTI B' := isTI_subgroupOf hTI
  have hB'ne : B' ≠ ⊥ := by
    intro h
    have hmem : (⟨x, hxM⟩ : ↥M) ∈ B' := hxB
    rw [h, Subgroup.mem_bot] at hmem
    exact hx2 (by rw [show x = 1 from congrArg Subtype.val hmem, one_pow])
  have hL' : PartTwo.omegaOneSub B' = (PartTwo.omegaOneSub B).subgroupOf M :=
    omegaOneSub_subgroupOf hBc
  have T : Setup210 B' B' :=
    { comm := hB'c
      two := hB'2
      exp_ne := ⟨⟨x, hxM⟩, hxB, fun h => hx2 (by simpa using congrArg Subtype.val h)⟩
      ti := hB'TI
      conj := ⟨1, (conjSubgroup_one B').symm⟩
      ne_bot := by
        rw [inf_of_le_left Subgroup.le_normalizer]
        exact hB'ne }
  have hroot := (tim78_2_10_a hCen hU T).2
  have hQ' : ∀ z : ↥M, z ∈ pCore 2 ↥M ↔ (z : G) ∈ Q := fun z => by
    rw [hQ, inSubgroup]
    exact ⟨fun h => ⟨z, h, rfl⟩, fun ⟨w, hw, hwz⟩ => (Subtype.ext hwz : w = z) ▸ hw⟩
  have hL'elem : Assembly.IsElemAbelian 2 (PartTwo.omegaOneSub B') :=
    ⟨⟨⟨fun a b => Subtype.ext (hB'c _ ((mem_omegaOneSub_iff hB'c).mp a.2).1 _
        ((mem_omegaOneSub_iff hB'c).mp b.2).1)⟩⟩,
      fun z hz => by rw [sq]; exact ((mem_omegaOneSub_iff hB'c).mp hz).2⟩
  have hL0Q : PartTwo.omegaOneSub B ≤ Q := by
    rcases tim78_2_13 hL'elem hroot with h | h
    · exfalso
      apply ht1
      have hmem : (⟨t, hBM htB⟩ : ↥M) ∈ PartTwo.omegaOneSub B' ⊓ pCore 2 ↥M := by
        refine Subgroup.mem_inf.mpr ⟨?_, (hQ' _).mpr htQ⟩
        rw [hL', Subgroup.mem_subgroupOf]
        exact (mem_omegaOneSub_iff hBc).mpr ⟨htB, htt⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · intro z hz
      have hzM : z ∈ M := hBM (PartTwo.omegaOneSub_le B hz)
      have hz' : (⟨z, hzM⟩ : ↥M) ∈ PartTwo.omegaOneSub B' := by
        rw [hL', Subgroup.mem_subgroupOf]
        exact hz
      exact (hQ' _).mp (h hz')
  refine ⟨hL0Q, ?_⟩
  have hBQ2 : IsPGroup 2 ↥(B ⊔ Q) := IsPGroup.to_sup_of_normal_right' hB2 hQ2
    (fun b hb => hMQ (hBM hb))
  set S' : Subgroup ↥M := (B ⊔ Q).subgroupOf M with hS'
  have hS'2 : IsPGroup 2 S' := hBQ2.comap_of_injective _ Subtype.val_injective
  have hBS' : B' ≤ S' := fun z hz => Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hz)
  have h4 : 4 ≤ Nat.card ↥(PartTwo.omegaOneSub B) := four_le_card_omegaOneSub hBc hB2 hb
  have hBne' : PartTwo.omegaOneSub B' ≠ B' := by
    intro h
    apply ha
    refine le_antisymm (PartTwo.omegaOneSub_le B) fun z hz => ?_
    have hz' : (⟨z, hBM hz⟩ : ↥M) ∈ PartTwo.omegaOneSub B' := by
      rw [h]
      exact hz
    rw [hL', Subgroup.mem_subgroupOf] at hz'
    exact hz'
  have hcomm : ∀ g ∈ M, ∀ a ∈ PartTwo.omegaOneSub B,
      ∀ b ∈ conjSubgroup g (PartTwo.omegaOneSub B), a * b = b * a := by
    intro g hg a ha b hb
    set g' : ↥M := ⟨g, hg⟩ with hg'
    have hconj : PartTwo.omegaOneSub (conjSubgroup g' B') =
        conjSubgroup g' (PartTwo.omegaOneSub B') := omegaOneSub_conj hB'c g'
    have hle : PartTwo.omegaOneSub (conjSubgroup g' B') ≤ S' := by
      rw [hconj]
      intro z hz
      rw [mem_conjSubgroup, hL', Subgroup.mem_subgroupOf] at hz
      have h1 : ((g'⁻¹ * z * g' : ↥M) : G) ∈ Q := hL0Q hz
      have h2 : (z : G) ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.mp (hMQ hg) _).mp h1
        rwa [show g * ((g'⁻¹ * z * g' : ↥M) : G) * g⁻¹ = (z : G) by
          show g * (g⁻¹ * (z : G) * g) * g⁻¹ = (z : G)
          group] at this
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right h2)
    have h4' : 4 ≤ Nat.card ↥(PartTwo.omegaOneSub (conjSubgroup g' B') ⊓ S') := by
      rw [inf_of_le_left hle, hconj, card_conjSubgroup, hL',
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          ((PartTwo.omegaOneSub_le B).trans hBM)).toEquiv]
      exact h4
    have key := tim78_2_14_b hCen hU hB'c hB'2 hB'TI hBne' hS'2 hBS' g' h4'
    have haM : a ∈ M := hBM (PartTwo.omegaOneSub_le B ha)
    have hbM : b ∈ M := by
      have hb' := mem_conjSubgroup.mp hb
      have := M.mul_mem (M.mul_mem hg (hBM (PartTwo.omegaOneSub_le B hb'))) (M.inv_mem hg)
      rwa [show g * (g⁻¹ * b * g) * g⁻¹ = b by group] at this
    have ha' : (⟨a, haM⟩ : ↥M) ∈ PartTwo.omegaOneSub B' := by
      rw [hL', Subgroup.mem_subgroupOf]
      exact ha
    have hb' : (⟨b, hbM⟩ : ↥M) ∈ PartTwo.omegaOneSub (conjSubgroup g' B') := by
      rw [hconj, mem_conjSubgroup, hL', Subgroup.mem_subgroupOf]
      exact mem_conjSubgroup.mp hb
    exact congrArg Subtype.val (key _ ha' _ hb')
  set W := ⨆ (g : G) (_ : g ∈ M), conjSubgroup g (PartTwo.omegaOneSub B) with hW
  have hc1 : ∀ g ∈ M,
      W ≤ Subgroup.centralizer (conjSubgroup g (PartTwo.omegaOneSub B) : Set G) := by
    intro g hg
    refine iSup₂_le fun k hk y hy => Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hz' := mem_conjSubgroup.mp hz
    have hy' : g⁻¹ * y * g ∈ conjSubgroup (g⁻¹ * k) (PartTwo.omegaOneSub B) := by
      rw [mem_conjSubgroup, show (g⁻¹ * k)⁻¹ * (g⁻¹ * y * g) * (g⁻¹ * k) = k⁻¹ * y * k by group]
      exact mem_conjSubgroup.mp hy
    have h := hcomm (g⁻¹ * k) (M.mul_mem (M.inv_mem hg) hk) _ hz' _ hy'
    calc z * y = g * ((g⁻¹ * z * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * z * g)) * g⁻¹ := by rw [h]
      _ = y * z := by group
  have hc2 : W ≤ Subgroup.centralizer (W : Set G) := by
    refine iSup₂_le fun g hg z hz => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hc1 g hg hy) z hz).symm
  have hcW : ∀ y ∈ W, ∀ z ∈ W, y * z = z * y := fun y hy z hz =>
    Subgroup.mem_centralizer_iff.mp (hc2 hz) y hy
  let E : Subgroup G :=
    { carrier := {z | z ∈ W ∧ z * z = 1}
      one_mem' := ⟨W.one_mem, mul_one 1⟩
      mul_mem' := fun {a b} ha hb => ⟨W.mul_mem ha.1 hb.1, by
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hcW b hb.1 a ha.1]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨W.inv_mem ha.1, by rw [← mul_inv_rev, ha.2, inv_one]⟩ }
  have hWE : W ≤ E := by
    refine iSup₂_le fun g hg z hz => ⟨?_, ?_⟩
    · exact (le_iSup₂ (f := fun g (_ : g ∈ M) => conjSubgroup g (PartTwo.omegaOneSub B)) g hg) hz
    · have h := ((mem_omegaOneSub_iff hBc).mp (mem_conjSubgroup.mp hz)).2
      calc z * z = g * ((g⁻¹ * z * g) * (g⁻¹ * z * g)) * g⁻¹ := by group
        _ = 1 := by rw [h, mul_one, mul_inv_cancel]
  refine ⟨⟨⟨fun a b => Subtype.ext (hcW _ a.2 _ b.2)⟩⟩, fun z hz => ?_⟩
  rw [sq]
  exact (hWE hz).2

end CFSG.RankThree.GF2n.Tim78

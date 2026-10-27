module

public import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec13.Item136Transfer
import CFSG.RankThree.PartTwo.Sec13.Item136Lift

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section More

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mk_mem_zpowers_of_mem {c : G} {x : G} (hx : x ∈ Subgroup.zpowers c)
    (hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
        ⟨x, hxN⟩ ∈ Subgroup.zpowers (QuotientGroup.mk'
          (aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
          ⟨c, Subgroup.le_normalizer (Subgroup.mem_zpowers c)⟩) := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨i, ?_⟩
  simp only
  rw [← map_zpow]
  rfl

theorem eq_of_mem_thetaComponentsAt_of_maximal {c : G} (hc : orderOf c = 3)
    {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    {E : Subgroup G} (hEL : E ≤ Subgroup.zpowers c ⊔ L) (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hmax : ∀ F : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F → E ≤ F →
      Nat.card F ≤ Nat.card E)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 c) (h3 : 3 ∣ Nat.card K) : K = L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hKL
  set N := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hN
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 N) with hπ
  have hKN : K ≤ N := le_normalizer_zpowers_of_mem hK
  have hLN : L ≤ N := le_normalizer_zpowers_of_mem hL
  have hK₁ := subgroupOf_normalizer_mem_thetaComponents hK
  have hL₁ := subgroupOf_normalizer_mem_thetaComponents hL
  have hne₁ : K.subgroupOf N ≠ L.subgroupOf N := by
    intro h
    apply hKL
    have h' := congrArg (Subgroup.map N.subtype) h
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hKN, inf_eq_left.mpr hLN] at h'
  set Kb := (K.subgroupOf N).map π with hKb
  set Lb := (L.subgroupOf N).map π with hLb
  have hKc := isComponent_map_of_mem_thetaComponents Nat.prime_three hK₁
  have hLc := isComponent_map_of_mem_thetaComponents Nat.prime_three hL₁
  have hneb : Kb ≠ Lb := fun h =>
    hne₁ ((theta_component_quotient_correspondence Nat.prime_three).1.injOn hK₁ hL₁ h)
  have hcomm : ⁅Kb, Lb⁆ = ⊥ :=
    (LocalCores.distinct_components_commute hKc hLc).resolve_left hneb
  have hKLc : ∀ x ∈ Kb, ∀ y ∈ Lb, x * y = y * x := by
    intro x hx y hy
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
    exact (Subgroup.mem_centralizer_iff.mp this y hy).symm
  have hcN : c ∈ N := Subgroup.le_normalizer (Subgroup.mem_zpowers c)
  set cb := π ⟨c, hcN⟩ with hcb
  have hcX : ∀ {X : Subgroup G}, X ∈ thetaComponentsAt 3 c → ∀ x ∈ (X.subgroupOf N).map π,
      cb * x = x * cb := by
    intro X hX x hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [hcb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hkC := Sec6.le_centralizer_of_mem_thetaComponentsAt hX (Subgroup.mem_subgroupOf.mp hk)
    exact (Subgroup.mem_centralizer_singleton_iff.mp hkC).symm
  have hcK : ∀ x ∈ Kb, cb * x = x * cb := hcX hK
  have hcL : ∀ x ∈ Lb, cb * x = x * cb := hcX hL
  have hzK : ∀ z ∈ Subgroup.zpowers cb, ∀ x ∈ Kb, z * x = x * z := by
    intro z hz x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_left (hcK x hx) i))
  have hzL : ∀ z ∈ Subgroup.zpowers cb, ∀ x ∈ Lb, z * x = x * z := by
    intro z hz x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_left (hcL x hx) i))
  have hZb : ∀ y ∈ Lb, (∀ z ∈ Lb, y * z = z * y) → y = 1 := by
    intro y hy hyc
    obtain ⟨η, -⟩ := exists_lBarEquiv hL
    have hmem : η.symm ⟨y, hy⟩ ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply η.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      exact (hyc _ (η w).2).symm
    rw [hZ, Subgroup.mem_bot] at hmem
    have h1 := congrArg η hmem
    rw [MulEquiv.apply_symm_apply, map_one] at h1
    exact congrArg Subtype.val h1
  have hcLn : (Subgroup.zpowers c : Subgroup G) ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun l hl => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (Sec6.le_centralizer_of_mem_thetaComponentsAt hL hl)
  have hdec : ∀ e ∈ E, ∃ y ∈ Subgroup.zpowers c, ∃ l ∈ L, y * l = e := by
    intro e he
    have he' : e ∈ ((Subgroup.zpowers c ⊔ L : Subgroup G) : Set G) := hEL he
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcLn] at he'
    obtain ⟨y, hy, l, hl, rfl⟩ := Set.mem_mul.mp he'
    exact ⟨y, hy, l, hl, rfl⟩
  have hcC : c ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hEC : E ≤ Subgroup.centralizer ({c} : Set G) :=
    hEL.trans (sup_le (Subgroup.zpowers_le.mpr hcC)
      (Sec6.le_centralizer_of_mem_thetaComponentsAt hL))
  have hEN : E ≤ N := hEC.trans (centralizer_le_normalizer_zpowers c)
  set E₁ := E.subgroupOf N with hE₁
  set Eb := E₁.map π with hEb
  have hE3 : IsPGroup 3 E₁ := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hE.2 _ (Subgroup.mem_subgroupOf.mp x.2)
  have hdecb : ∀ x ∈ Eb, ∃ z ∈ Subgroup.zpowers cb, ∃ w ∈ Lb, z * w = x := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨y, hy, l, hl, hyl⟩ := hdec e (Subgroup.mem_subgroupOf.mp he)
    have hyN : y ∈ N := (Subgroup.zpowers_le.mpr hcN) hy
    have hlN : l ∈ N := hLN hl
    refine ⟨π ⟨y, hyN⟩, mk_mem_zpowers_of_mem hy hyN, π ⟨l, hlN⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl), ?_⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext hyl
  have hEK : ∀ x ∈ Eb, ∀ k ∈ Kb, x * k = k * x := by
    intro x hx k hk
    obtain ⟨z, hz, w, hw, rfl⟩ := hdecb x hx
    rw [mul_assoc, (hKLc k hk w hw).symm, ← mul_assoc, hzK z hz k hk, mul_assoc]
  have hEKc : ∀ x ∈ Eb, x ∈ Kb → x ∈ Subgroup.zpowers cb := by
    intro x hx hxK
    obtain ⟨z, hz, w, hw, rfl⟩ := hdecb x hx
    have hw1 : w = 1 := by
      refine hZb w hw fun v hv => ?_
      have hx := hKLc _ hxK v hv
      have hzv := hzL z hz v hv
      calc w * v = z⁻¹ * ((z * w) * v) := by group
        _ = z⁻¹ * (v * (z * w)) := by rw [hx]
        _ = z⁻¹ * (v * z) * w := by group
        _ = z⁻¹ * (z * v) * w := by rw [hzv]
        _ = v * w := by group
    rw [hw1, mul_one]
    exact hz
  have hEb3 : ∀ x ∈ Eb, x ^ 3 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow]
    have : e ^ 3 = 1 := Subtype.ext (by simpa using hE.2 _ (Subgroup.mem_subgroupOf.mp he))
    rw [this, map_one]
  have hEbc : ∀ x ∈ Eb, ∀ y ∈ Eb, x * y = y * x := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩
    rw [← map_mul, ← map_mul]
    have := hE.1
    have hef : (e : G) * f = f * e := congrArg Subtype.val
      (mul_comm' (⟨(e : G), Subgroup.mem_subgroupOf.mp he⟩ : E)
        ⟨(f : G), Subgroup.mem_subgroupOf.mp hf⟩)
    congr 1
    exact Subtype.ext hef
  have hcardE : Nat.card Eb = Nat.card E := by
    rw [hEb, card_map_eq_of_injOn π (injOn_mk_of_isPGroup Nat.prime_three hE3)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
  have hk3 : ∀ k ∈ Kb, k ^ 3 = 1 → k ∈ Eb := by
    intro k hk hk3
    by_contra hkE
    set B := Eb ⊔ Subgroup.zpowers k with hB
    have hEbk : Eb ≤ Subgroup.normalizer (Subgroup.zpowers k : Set _) := by
      intro x hx
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (hEK x hx k hk).symm i)
    have hBdec : ∀ b ∈ B, ∃ x ∈ Eb, ∃ i : ℤ, x * k ^ i = b := by
      intro b hb
      have hb' : b ∈ ((Eb ⊔ Subgroup.zpowers k : Subgroup _) : Set _) := hb
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hEbk] at hb'
      obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hb'
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ⟨x, hx, i, rfl⟩
    have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
      intro a ha b hb
      obtain ⟨x, hx, i, rfl⟩ := hBdec a ha
      obtain ⟨y, hy, j, rfl⟩ := hBdec b hb
      have hxk : Commute x k := hEK x hx k hk
      have hyk : Commute y k := hEK y hy k hk
      have hxy : Commute x y := hEbc x hx y hy
      exact (Commute.mul_left (hxy.mul_right (hxk.zpow_right j))
        (((hyk.zpow_right i).symm).mul_right (Commute.zpow_zpow_self k i j))).eq
    have hB3 : ∀ b ∈ B, b ^ 3 = 1 := by
      intro b hb
      obtain ⟨x, hx, i, rfl⟩ := hBdec b hb
      have hxk : Commute x k := hEK x hx k hk
      rw [(hxk.zpow_right i).mul_pow, hEb3 x hx, one_mul, ← zpow_natCast, ← zpow_mul,
        mul_comm, zpow_mul, zpow_natCast, hk3, one_zpow]
    have hBp : IsPGroup 3 B := fun b => ⟨1, Subtype.ext (by simpa using hB3 b b.2)⟩
    obtain ⟨S, hES, -, hS3, hSB⟩ := exists_isPGroup_le_map_eq (M := ⊤) hBp
      (by rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]; exact le_top)
      hE3 le_top le_sup_left
    have hinj := injOn_mk_of_isPGroup Nat.prime_three hS3
    have hSc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
      intro s hs t ht
      refine hinj (S.mul_mem hs ht) (S.mul_mem ht hs) ?_
      rw [map_mul, map_mul]
      have hsB : π s ∈ B := hSB ▸ Subgroup.mem_map_of_mem π hs
      have htB : π t ∈ B := hSB ▸ Subgroup.mem_map_of_mem π ht
      exact hBc _ hsB _ htB
    have hS3' : ∀ s ∈ S, s ^ 3 = 1 := by
      intro s hs
      refine hinj (S.pow_mem hs 3) S.one_mem ?_
      have hsB : π s ∈ B := hSB ▸ Subgroup.mem_map_of_mem π hs
      rw [map_pow, hB3 _ hsB, map_one]
    set F := S.map N.subtype with hF
    have hFab : CFSG.Assembly.IsElemAbelian 3 F := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
      · obtain ⟨_, ⟨s, hs, rfl⟩⟩ := a
        obtain ⟨_, ⟨t, ht, rfl⟩⟩ := b
        exact Subtype.ext (by simpa using congrArg Subtype.val (hSc s hs t ht))
      · rintro _ ⟨s, hs, rfl⟩
        simpa using congrArg Subtype.val (hS3' s hs)
    have hEF : E ≤ F := by
      intro e he
      exact ⟨⟨e, hEN he⟩, hES (Subgroup.mem_subgroupOf.mpr he), rfl⟩
    have hcardF : Nat.card F = Nat.card B := by
      rw [hF, Subgroup.card_map_of_injective N.subtype_injective, ← hSB,
        card_map_eq_of_injOn π hinj]
    have hlt : Nat.card Eb < Nat.card B := by
      refine Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => hkE ?_)
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers k)
    have := hmax F hFab hEF
    omega
  have hKperf : Group.IsPerfect Kb := hKc.1.1
  set Z := (Subgroup.zpowers cb).subgroupOf Kb with hZdef
  have hZc : Z ≤ Subgroup.center Kb := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact (hzK _ (Subgroup.mem_subgroupOf.mp hz) _ x.2).symm
  have hZ3 : Nat.card Z ≤ 3 := by
    have h1 : Nat.card Z ≤ Nat.card (Subgroup.zpowers cb) :=
      Nat.card_le_card_of_injective (fun z => (⟨(z : _), Subgroup.mem_subgroupOf.mp z.2⟩ :
        Subgroup.zpowers cb)) (fun a b hab => Subtype.ext (Subtype.ext
          (congrArg Subtype.val hab :)))
    have h2 : Nat.card (Subgroup.zpowers cb) ≤ 3 := by
      rw [Nat.card_zpowers]
      have : orderOf cb ∣ orderOf c := by
        refine (orderOf_map_dvd π _).trans ?_
        rw [Subgroup.orderOf_mk]
      rw [hc] at this
      exact Nat.le_of_dvd (by norm_num) this
    exact h1.trans h2
  have hZall : ∀ x : Kb, x ^ 3 = 1 → x ∈ Z := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx3 : (x : N ⧸ aschbacherSolvableCore 3 N) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hx, Subgroup.coe_one]
    exact hEKc _ (hk3 _ x.2 hx3) x.2
  have hnd := not_three_dvd_card_of_forall_pow_three_mem hKperf Z hZc hZ3 hZall
  apply hnd
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hkN : (k : G) ∈ N := hKN k.2
  set k₁ : N := ⟨k, hkN⟩
  have hk₁ : orderOf k₁ = 3 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hk]
  have hk3 : IsPGroup 3 (Subgroup.zpowers k₁) := by
    rintro ⟨x, hx⟩
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hk₁,
      pow_orderOf_eq_one, one_zpow]
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hk3
  have hkb : orderOf (π k₁) = 3 := by
    have hk13 : k₁ ^ 3 = 1 := hk₁ ▸ pow_orderOf_eq_one k₁
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hk13, map_one]
    · intro h1
      have : k₁ = 1 := hinj (Subgroup.mem_zpowers k₁) (Subgroup.one_mem _) (by rw [h1, map_one])
      rw [this, orderOf_one] at hk₁
      exact absurd hk₁ (by norm_num)
  have hmem : π k₁ ∈ Kb := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr k.2)
  have hdvd := Subgroup.orderOf_dvd_natCard Kb hmem
  rwa [hkb] at hdvd

end More

end CFSG.RankThree.PartTwo.Sec13

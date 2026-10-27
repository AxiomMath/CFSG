module

public import CFSG.Timmesfeld.Bridge.RootSetsConn6
public import CFSG.Timmesfeld.Bridge.RootSetsConn5

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

theorem bender_le_sylow {B : Type*} [Group B] [Finite B]
    (hB : CFSG.BenderSuzuki.IsBenderGroup B) (S : Sylow 2 B) {t : B} (htS : t ∈ S)
    (ht1 : t ≠ 1) {H : Subgroup B} (hH : IsPGroup 2 H) (htH : t ∈ H) : H ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ : ∃ g : B, g • S = S' := MulAction.exists_smul_eq B S S'
  have hse := Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer hB S
  by_cases hgN : g ∈ Subgroup.normalizer (S : Set B)
  · rw [← hg, Sylow.smul_eq_iff_mem_normalizer.2 hgN] at hS'
    exact hS'
  · exfalso
    have htS' : t ∈ (S' : Subgroup B) := hS' htH
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htS'
    obtain ⟨s, hs, hst⟩ := htS'
    set N := Subgroup.normalizer (S : Set B)
    have htM : t ∈ N ⊓ N.map (MulAut.conj g).toMonoidHom := by
      refine ⟨Subgroup.le_normalizer htS, s, Subgroup.le_normalizer hs, ?_⟩
      rw [← hst]
      rfl
    have hodd := hse.2.2 g hgN
    have h2 : 2 ∣ Nat.card (N ⊓ N.map (MulAut.conj g).toMonoidHom : Subgroup B) := by
      have hdvd := orderOf_dvd_natCard (⟨t, htM⟩ : (N ⊓ N.map (MulAut.conj g).toMonoidHom :
        Subgroup B))
      rw [Subgroup.orderOf_mk] at hdvd
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 S.isPGroup') ⟨t, htS⟩
      rw [Subgroup.orderOf_mk] at hk
      rcases k with _ | k
      · exact absurd (orderOf_eq_one_iff.1 (by simpa using hk)) ht1
      · exact (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans (hk ▸ hdvd)
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

variable {G : Type} [Group G] {D : Set G}

@[expose] def zcore (D : Set G) (x : G) (P : Subgroup G) : Subgroup G :=
  (Subgroup.center (lsub D x P) ⊓ CFSG.pCore 2 (lsub D x P)).map (lsub D x P).subtype

@[expose] def Step6ThreeProduct (D : Set G) (x : G) (P : Subgroup G) : Prop :=
  ∀ d ∈ D, d ∈ P → ∀ e ∈ D, e ∈ P → ∀ f ∈ D, f ∈ P → d * f ∈ qcore D x P →
    ∃ u ∈ D, u ∈ P ∧ ∃ w ∈ zcore D x P, d * e * f = u * w

namespace Step6

variable {a b c x z : G} {P : Subgroup G}

theorem exists_sylow_ge (hC : ConnCex D) (h : Step6 D a b c x z P) :
    ∃ S : Sylow 2 (lsub D x P ⧸ CFSG.pCore 2 (lsub D x P)),
      (P.subgroupOf (lsub D x P)).map (QuotientGroup.mk' (CFSG.pCore 2 (lsub D x P))) ≤ S := by
  have := hC.setting.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((h.hP2.comap_subtype (K := lsub D x P)).map _).exists_le_sylow

theorem isPGroup_preimage (hC : ConnCex D)
    (S : Sylow 2 (lsub D x P ⧸ CFSG.pCore 2 (lsub D x P))) :
    IsPGroup 2 (((S : Subgroup _).comap
      (QuotientGroup.mk' (CFSG.pCore 2 (lsub D x P)))).map (lsub D x P).subtype) := by
  have := hC.setting.finite
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 (lsub D x P))).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  exact ((S.isPGroup').comap_of_ker_isPGroup _ hker).map _

theorem mem_of_mem_sylow (hC : ConnCex D) (h : Step6 D a b c x z P)
    {S : Sylow 2 (lsub D x P ⧸ CFSG.pCore 2 (lsub D x P))}
    (hS : (P.subgroupOf (lsub D x P)).map (QuotientGroup.mk' (CFSG.pCore 2 (lsub D x P))) ≤ S)
    {y : lsub D x P} (hy : (y : G) ∈ D)
    (hyS : QuotientGroup.mk' (CFSG.pCore 2 (lsub D x P)) y ∈ S) : (y : G) ∈ P := by
  have hPle : ∀ l ∈ D, l ∈ P → l ∈ ((S : Subgroup _).comap
      (QuotientGroup.mk' (CFSG.pCore 2 (lsub D x P)))).map (lsub D x P).subtype :=
    fun l hl hlP => ⟨⟨l, mem_lsub_of_mem hl hlP⟩, hS ⟨⟨l, mem_lsub_of_mem hl hlP⟩, hlP, rfl⟩, rfl⟩
  have hyz : Commute (y : G) z :=
    (Subgroup.mem_centralizer_singleton_iff.1 (h.lsub_le_centralizer y.2))
  exact h.mem_of_isPGroup hC (isPGroup_preimage hC S) hPle hy hyz ⟨y, hyS, rfl⟩

theorem mul_mem_qcore_of_mul_mem_qcore (hB : OddTranspBender) (hC : ConnCex D)
    {a₁ b₁ c₁ x₁ z₁ a₂ b₂ c₂ x₂ z₂ : G} (h₁ : Step6 D a₁ b₁ c₁ x₁ z₁ P)
    (h₂ : Step6 D a₂ b₂ c₂ x₂ z₂ P) (h3 : Step6ThreeProduct D x₁ P) {e f : G} (he : e ∈ D)
    (hf : f ∈ D) (heP : e ∈ P) (hfP : f ∈ P) (hq : e * f ∈ qcore D x₁ P) :
    e * f ∈ qcore D x₂ P := by
  by_contra hq2
  have := hC.setting.finite
  have hD := hC.setting.root
  have hN := hC.setting.normal
  have hef : e ≠ f := by
    rintro rfl
    exact hq2 (by rw [hD.mul_self_eq_one he]; exact one_mem _)
  set X := lsub D x₂ P with hX
  set Q := CFSG.pCore 2 X with hQ
  set π := QuotientGroup.mk' Q with hπ
  have hS := h₂.setup hC
  have hBX := h₂.isBenderGroup_pCore hB hC
  set eX : X := ⟨e, mem_lsub_of_mem he heP⟩ with heX
  set fX : X := ⟨f, mem_lsub_of_mem hf hfP⟩ with hfX
  set xX : X := ⟨x₂, mem_lsub_x⟩ with hxX
  have heE : eX ∈ lclass D x₂ P := h₂.mem_lclass hC he heP
  have hfE : fX ∈ lclass D x₂ P := h₂.mem_lclass hC hf hfP
  have hxE : xX ∈ lclass D x₂ P := mem_classIn_self _ x₂
  have hre : Reach D a₂ e := h₂.reach_of_mem hC he heP
  have hrf : Reach D a₂ f := h₂.reach_of_mem hC hf hfP
  have hcex : ¬ Commute e x₂ := fun hc =>
    h₂.hax (reach_trans hre (reach_of_commute he h₂.hx hc))
  have hcfx : ¬ Commute f x₂ := fun hc =>
    h₂.hax (reach_trans hrf (reach_of_commute hf h₂.hx hc))
  have hcef : Commute e f := h₂.commute_of_mem hC he hf heP hfP
  have hef2 : eX * fX * (eX * fX) = 1 := Subtype.ext (hC.mul_mul_self_of_commute he hf hcef)
  have htri : Asc72.IsTriangle (lclass D x₂ P) eX xX fX :=
    ⟨heE, hfE, hxE, fun h' => hef (congrArg Subtype.val h'), Subtype.ext hcef.eq,
      fun h' => hcex (congrArg Subtype.val h'.eq), fun h' => hcfx (congrArg Subtype.val h'.eq)⟩
  obtain ⟨Sb, hSb⟩ := h₂.exists_sylow_ge hC
  have hu1 : π (eX * fX) ≠ 1 := fun h1 => hq2 ⟨eX * fX, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  have huS : π (eX * fX) ∈ Sb :=
    hSb ⟨eX * fX, (P.subgroupOf X).mul_mem (Subgroup.mem_subgroupOf.2 heP)
      (Subgroup.mem_subgroupOf.2 hfP), rfl⟩
  rcases Asc72.IsTriangle.orderOf_cases hS.oddT hS.normal htri with ⟨hodd, -⟩ | h4 |
    ⟨n, hn, -, hord⟩
  ·
    have hm := Asc72.IsTriangle.mul_mem_of_odd hS.oddT hS.normal htri hodd
    exact h₁.not_mem_qcore hC (classIn_subset_of_normal hN _ h₂.hx hm) hq
  ·
    have h2grp : IsPGroup 2 (Subgroup.closure ({π (eX * fX), π xX} : Set (X ⧸ Q))) := by
      refine isPGroup_two_closure_pair (k := 2) ?_ ?_ ?_
      · rw [← map_mul, hef2, map_one]
      · rw [← map_mul, hS.oddT.mul_self_eq_one hxE, map_one]
      · rw [← map_mul, ← map_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, ← h4, pow_orderOf_eq_one,
          map_one]
    have hle := bender_le_sylow hBX Sb huS hu1 h2grp (Subgroup.subset_closure (by simp))
    have hxS : π xX ∈ Sb := hle (Subgroup.subset_closure (by simp))
    have hxP : x₂ ∈ P := h₂.mem_of_mem_sylow hC hSb (y := xX) h₂.hx hxS
    exact h₂.hax (h₂.reach_of_mem hC h₂.hx hxP)
  ·
    obtain ⟨-, -, hte, htf, htx, hw⟩ :=
      Asc72.IsTriangle.third_kind hS.oddT hS.normal htri hn hord
    set tX := (eX * fX * xX) ^ n with htX
    set wX := eX * fX * tX with hwX
    have hwD : (wX : G) ∈ D := classIn_subset_of_normal hN _ h₂.hx hw
    have hcw : Commute (eX * fX) wX := (Commute.refl _).mul_right (hte.mul_right htf).symm
    have h2grp : IsPGroup 2 (Subgroup.closure ({π (eX * fX), π wX} : Set (X ⧸ Q))) := by
      refine isPGroup_closure_of_pairwise ?_ ?_
      · rintro s (rfl | rfl) t (rfl | rfl) -
        · exact Commute.refl _
        · exact hcw.map π
        · exact (hcw.map π).symm
        · exact Commute.refl _
      · rintro s (rfl | rfl)
        · rw [← map_mul, hef2, map_one]
        · rw [← map_mul, hS.oddT.mul_self_eq_one hw, map_one]
    have hle := bender_le_sylow hBX Sb huS hu1 h2grp (Subgroup.subset_closure (by simp))
    have hwS : π wX ∈ Sb := hle (Subgroup.subset_closure (by simp))
    have hwP : (wX : G) ∈ P := h₂.mem_of_mem_sylow hC hSb hwD hwS
    have htw : tX = eX * fX * wX := by
      rw [hwX, ← mul_assoc (eX * fX), hef2, one_mul]
    have hteq : (tX : G) = e * f * (wX : G) := congrArg Subtype.val htw
    have hcfw : Commute f (wX : G) := h₂.commute_of_mem hC hf hwD hfP hwP
    obtain ⟨u, huD, huP, zs, hzs, hdec⟩ := h3 e he heP (wX : G) hwD hwP f hf hfP hq
    have htu : (tX : G) = u * zs := by
      rw [hteq, ← hdec, mul_assoc, hcfw.eq, ← mul_assoc]
    have hct : ∀ l ∈ D, l ∈ P → Commute l (tX : G) := by
      intro l hl hlP
      rw [hteq]
      exact ((h₂.commute_of_mem hC hl he hlP heP).mul_right
        (h₂.commute_of_mem hC hl hf hlP hfP)).mul_right (h₂.commute_of_mem hC hl hwD hlP hwP)
    have hXc : lsub D x₂ P ≤ Subgroup.centralizer ({(tX : G)} : Set G) := by
      rw [lsub, Subgroup.closure_le]
      rintro y (rfl | ⟨hyD, hyP⟩)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val htx.eq).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hct y hyD hyP).eq
    have hue : u ∈ classIn X e := by
      rw [classIn_eq_of_mem (h₂.mem_classIn hC he heP)]
      exact h₂.mem_classIn hC huD huP
    obtain ⟨g, hgX, hug⟩ := hue
    have hgt : g * (tX : G) * g⁻¹ = tX := by
      rw [Subgroup.mem_centralizer_singleton_iff.1 (hXc hgX), mul_inv_cancel_right]
    have hzs_eq : zs = g * f * g⁻¹ * (g * (wX : G) * g⁻¹) := by
      have h1 : zs = u * tX := by
        rw [htu, ← mul_assoc, hD.mul_self_eq_one huD, one_mul]
      have h2 : e * (tX : G) = f * wX := by
        rw [hteq, ← mul_assoc, ← mul_assoc, hD.mul_self_eq_one he, one_mul]
      rw [h1, hug]
      calc g * e * g⁻¹ * (tX : G) = g * e * g⁻¹ * (g * (tX : G) * g⁻¹) := by rw [hgt]
        _ = g * (e * tX) * g⁻¹ := by group
        _ = g * (f * wX) * g⁻¹ := by rw [h2]
        _ = g * f * g⁻¹ * (g * (wX : G) * g⁻¹) := by group
    have hfw : f ≠ (wX : G) := by
      intro hfw
      have hte' : (tX : G) = e := by
        rw [hteq, ← hfw, mul_assoc, hD.mul_self_eq_one hf, mul_one]
      exact hcex (by rw [← hte']; exact congrArg Subtype.val htx.eq)
    obtain ⟨zz, ⟨hzc, -⟩, hzz⟩ := hzs
    have hcen : ∀ y ∈ lsub D x₁ P, Commute y zs := fun y hy => by
      rw [← hzz]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc ⟨y, hy⟩)
    have hza := hcen a₁ (mem_lsub_of_mem h₁.ha h₁.haP)
    have hzx := hcen x₁ mem_lsub_x
    rw [hzs_eq] at hza hzx
    exact h₁.false_of_commute_mul hC (hN g f hf) (hN g _ hwD)
      (fun h' => hfw (mul_left_cancel (mul_right_cancel h'))) ((Commute.conj_iff g).2 hcfw)
      hza hzx

end Step6

end CFSG.Timmesfeld.Bridge

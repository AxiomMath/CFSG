module

public import CFSG.Quasithin.EmptyFaithful.R3c13Def
public import CFSG.Quasithin.EmptyFaithful.R3c10Elim

public section

namespace CFSG.Quasithin.R3c13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Quasithin.R3c10
open scoped commutatorElement

section Gen

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_sup_zpowers_cases {V : Subgroup G} {y : G} (hy3 : orderOf y = 3)
    (hyN : y ∈ Subgroup.normalizer (V : Set G)) {c : G} (hc : c ∈ V ⊔ Subgroup.zpowers y) :
    ∃ v ∈ V, ∃ j : ℕ, j < 3 ∧ c = v * y ^ j := by
  have hle : Subgroup.zpowers y ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hyN
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left V (Subgroup.zpowers y) hle
  have hmem : c ∈ ((V ⊔ Subgroup.zpowers y : Subgroup G) : Set G) := hc
  rw [hmul] at hmem
  obtain ⟨v, hv, w, hw, hvw⟩ := Set.mem_mul.mp hmem
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have h1 : y ^ (n % ((orderOf y : ℕ) : ℤ)) = y ^ n := zpow_mod_orderOf y n
  rw [hy3] at h1
  have hn0 : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have hn3 : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
  refine ⟨v, hv, (n % 3).toNat, by omega, ?_⟩
  rw [← hvw, ← h1]
  congr 1
  rw [← zpow_natCast, Int.toNat_of_nonneg hn0]
  rfl

omit [Finite G] in
theorem cent_sup_zpowers {V : Subgroup G} {y : G} (hy3 : orderOf y = 3)
    (hyN : y ∈ Subgroup.normalizer (V : Set G)) (hyn : ¬ ∀ v ∈ V, y * v = v * y)
    (hVc : ∀ u ∈ V, ∀ v ∈ V, u * v = v * u) {c : G} (hc : c ∈ V ⊔ Subgroup.zpowers y)
    (hcc : ∀ w ∈ V, c * w = w * c) : c ∈ V := by
  obtain ⟨v, hv, j, hj, rfl⟩ := mem_sup_zpowers_cases hy3 hyN hc
  have hyj : ∀ w ∈ V, y ^ j * w = w * y ^ j := by
    intro w hw
    have h1 := hcc w hw
    have h2 : v * w = w * v := hVc v hv w hw
    calc y ^ j * w = v⁻¹ * (v * y ^ j * w) := by group
      _ = v⁻¹ * (w * (v * y ^ j)) := by rw [h1]
      _ = v⁻¹ * (w * v) * y ^ j := by group
      _ = v⁻¹ * (v * w) * y ^ j := by rw [h2]
      _ = w * y ^ j := by group
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  interval_cases j
  · simpa using hv
  · exfalso
    exact hyn fun w hw => by simpa using hyj w hw
  · exfalso
    apply hyn
    intro w hw
    have h4 : y = (y ^ 2) ^ 2 := by
      calc y = y ^ 4 * (y ^ 3)⁻¹ := by group
        _ = (y ^ 2) ^ 2 := by rw [hy3']; group
    rw [h4]
    have hc2 : Commute (y ^ 2) w := (hyj w hw)
    exact (hc2.pow_left 2).eq

theorem el_core {L V₂ Yp : Subgroup G} (hYL : Yp ≤ L) (hV2Y : V₂ ≤ Yp)
    (hYN : Yp ≤ Subgroup.normalizer (V₂ : Set G)) (hV4 : Nat.card V₂ = 4)
    (hV2 : ∀ v ∈ V₂, v * v = 1)
    (hgen : Yp = Subgroup.closure {x : G | x ∈ Yp ∧ ∃ k : ℕ, orderOf x = 3 ^ k})
    (hcard : ∃ m : ℕ, Nat.card Yp = 2 ^ m * 3) (hact : ¬ Yp ≤ Subgroup.centralizer (V₂ : Set G))
    (hZ2 : ∀ z ∈ centerOf L, ∃ k : ℕ, orderOf z = 2 ^ k)
    (hVz : ∀ x ∈ V₂, x ∈ centerOf L → x = 1)
    (hC : ∀ c ∈ L, (∀ v ∈ V₂, c * v = v * c) → ∃ v ∈ V₂, c * v⁻¹ ∈ centerOf L) :
    Nonempty (↥Yp ≃* alternatingGroup (Fin 4)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := hcard
  have hVc : ∀ u ∈ V₂, ∀ v ∈ V₂, u * v = v * u := by
    intro u hu v hv
    have h1 : u * v * (u * v) = 1 := hV2 _ (V₂.mul_mem hu hv)
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hV2 u hu)
    have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hV2 v hv)
    have hinv : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right h1
    calc u * v = (u * v)⁻¹ := hinv.symm
      _ = v⁻¹ * u⁻¹ := mul_inv_rev _ _
      _ = v * u := by rw [hu', hv']
  have hY3 : ∀ x ∈ Yp, (∃ k : ℕ, orderOf x = 3 ^ k) → x ^ 3 = 1 := by
    intro x hx ⟨k, hk⟩
    have hd : orderOf x ∣ 2 ^ m * 3 := hm ▸ Subgroup.orderOf_dvd_natCard Yp hx
    have hcop : Nat.Coprime (orderOf x) (2 ^ m) := by
      rw [hk]
      exact Nat.Coprime.pow_left k (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 3 2))
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left hd)
  obtain ⟨y, hyY, hy3, hyn⟩ : ∃ y ∈ Yp, orderOf y = 3 ∧ ¬ ∀ v ∈ V₂, y * v = v * y := by
    by_contra hcon
    push Not at hcon
    apply hact
    rw [hgen, Subgroup.closure_le]
    intro x hx
    obtain ⟨hxY, hxk⟩ := hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    by_cases hx1 : x = 1
    · rw [hx1]
      simp
    · have hx3 : orderOf x = 3 := by
        have h3 := hY3 x hxY hxk
        have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hx1
        · exact h
      exact (hcon x hxY hx3 v hv).symm
  have hyN : y ∈ Subgroup.normalizer (V₂ : Set G) := hYN hyY
  set A : Subgroup G := V₂ ⊔ Subgroup.zpowers y with hA
  have hAY : A ≤ Yp := sup_le hV2Y ((Subgroup.zpowers_le).mpr hyY)
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  obtain ⟨ι, hιinj, -⟩ := R3c9.exists_mulAut_embedding ↥V₂ hV4
  let θ : ↥(Subgroup.normalizer (V₂ : Set G)) →* Equiv.Perm (Fin 3) :=
    ι.comp (Subgroup.normalizerMonoidHom V₂)
  have hθ : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (V₂ : Set G)), θ ⟨x, hx⟩ = 1 →
      ∀ v ∈ V₂, x * v = v * x := by
    intro x hx h1 v hv
    have h2 : Subgroup.normalizerMonoidHom V₂ ⟨x, hx⟩ = 1 := by
      apply hιinj
      rw [map_one]
      exact h1
    have h3 := congrArg (fun f : MulAut ↥V₂ => ((f ⟨v, hv⟩ : ↥V₂) : G)) h2
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h3
    calc x * v = (x * v * x⁻¹) * x := by group
      _ = v * x := by rw [h3]
  have hA3 : ∀ g ∈ Yp, (∃ k : ℕ, orderOf g = 3 ^ k) → g ∈ A := by
    intro g hgY hgk
    have hg3 : g ^ 3 = 1 := hY3 g hgY hgk
    have hgN : g ∈ Subgroup.normalizer (V₂ : Set G) := hYN hgY
    set σ : Equiv.Perm (Fin 3) := θ ⟨y, hyN⟩ with hσ
    set τ : Equiv.Perm (Fin 3) := θ ⟨g, hgN⟩ with hτ
    have hσ1 : σ ≠ 1 := by
      intro h1
      exact hyn (hθ y hyN h1)
    have hσ3 : σ ^ 3 = 1 := by
      rw [hσ, ← map_pow]
      have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (V₂ : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hy3')
      rw [this, map_one]
    have hτ3 : τ ^ 3 = 1 := by
      rw [hτ, ← map_pow]
      have : (⟨g, hgN⟩ : ↥(Subgroup.normalizer (V₂ : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hg3)
      rw [this, map_one]
    obtain ⟨i, hi, hci⟩ : ∃ i : ℕ, i < 3 ∧ ∀ v ∈ V₂, (g * (y ^ i)⁻¹) * v = v * (g * (y ^ i)⁻¹) := by
      have hyi : ∀ i : ℕ, y ^ i ∈ Subgroup.normalizer (V₂ : Set G) := fun i =>
        Subgroup.pow_mem _ hyN i
      have key : ∀ i : ℕ, τ = σ ^ i → ∀ v ∈ V₂, (g * (y ^ i)⁻¹) * v = v * (g * (y ^ i)⁻¹) := by
        intro i hτi
        have hmem : g * (y ^ i)⁻¹ ∈ Subgroup.normalizer (V₂ : Set G) :=
          Subgroup.mul_mem _ hgN (Subgroup.inv_mem _ (hyi i))
        refine hθ _ hmem ?_
        have : (⟨g * (y ^ i)⁻¹, hmem⟩ : ↥(Subgroup.normalizer (V₂ : Set G))) =
            ⟨g, hgN⟩ * (⟨y, hyN⟩ ^ i)⁻¹ := Subtype.ext (by simp)
        rw [this, map_mul, map_inv, map_pow, ← hσ, ← hτ, hτi]
        exact mul_inv_cancel _
      rcases R3c9.perm3_mem_powers σ τ hσ1 hσ3 hτ3 with h | h | h
      · exact ⟨0, by norm_num, key 0 (by simpa using h)⟩
      · exact ⟨1, by norm_num, key 1 (by simpa using h)⟩
      · exact ⟨2, by norm_num, key 2 h⟩
    have hyiY : y ^ i ∈ Yp := Subgroup.pow_mem _ hyY i
    have hc0Y : g * (y ^ i)⁻¹ ∈ Yp := Subgroup.mul_mem _ hgY (Subgroup.inv_mem _ hyiY)
    obtain ⟨v, hv, hz⟩ := hC _ (hYL hc0Y) hci
    set z : G := g * (y ^ i)⁻¹ * v⁻¹ with hzdef
    have hzc : ∀ h ∈ L, h * z = z * h := fun h hh =>
      Subgroup.mem_centralizer_iff.mp hz.2 h hh
    set a : G := v * y ^ i with hadef
    have haA : a ∈ A := Subgroup.mul_mem _ (Subgroup.mem_sup_left hv)
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)) i)
    have haY : a ∈ Yp := hAY haA
    have hgaz : g = a * z := by
      calc g = (g * (y ^ i)⁻¹ * v⁻¹) * (v * y ^ i) := by group
        _ = z * a := rfl
        _ = a * z := (hzc a (hYL haY)).symm
    have hcomm : Commute a z := hzc a (hYL haY)
    have h3 : a ^ 3 * z ^ 3 = 1 := by
      rw [← hcomm.mul_pow, ← hgaz]
      exact hg3
    have ha3 : a ^ 3 = (z ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h3
    have hzC : z ∈ centerOf L := hz
    have ha3C : a ^ 3 ∈ centerOf L := by
      rw [ha3]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hzC 3)
    have ha3A : a ^ 3 ∈ V₂ ⊔ Subgroup.zpowers y := Subgroup.pow_mem _ haA 3
    have ha3V : a ^ 3 ∈ V₂ := by
      refine cent_sup_zpowers hy3 hyN hyn hVc ha3A fun w hw => ?_
      exact (Subgroup.mem_centralizer_iff.mp ha3C.2 w (hYL (hV2Y hw))).symm
    have ha31 : a ^ 3 = 1 := hVz _ ha3V ha3C
    have hz31 : z ^ 3 = 1 := by
      rw [ha31, one_mul] at h3
      exact h3
    obtain ⟨k, hk⟩ := hZ2 z hzC
    have hdvd : 2 ^ k ∣ 3 := by
      rw [← hk]
      exact orderOf_dvd_of_pow_eq_one hz31
    have hk0 : 2 ^ k = 1 :=
      (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).eq_one_of_dvd hdvd
    have hz1 : z = 1 := by
      rw [hk0, orderOf_eq_one_iff] at hk
      exact hk
    rw [hgaz, hz1, mul_one]
    exact haA
  have hYA : Yp ≤ A := by
    rw [hgen, Subgroup.closure_le]
    intro x hx
    exact hA3 x hx.1 hx.2
  have hK3 : ¬ 9 ∣ Nat.card Yp := by
    rw [hm]
    intro h9
    have h3 : 3 ∣ 2 ^ m := by
      have : 3 * 3 ∣ 3 * 2 ^ m := by
        calc 3 * 3 = 9 := by norm_num
          _ ∣ 2 ^ m * 3 := h9
          _ = 3 * 2 ^ m := by ring
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  refine R3c9.isAlt4_of_selfCent (K := Yp) (V := V₂) (Y := Yp) hV2Y hYN hV4
    (fun v hv => by rw [sq]; exact hV2 v hv) hVc hgen hV2Y hK3 hact ?_
  intro c hc hcc _
  exact cent_sup_zpowers hy3 hyN hyn hVc (hYA hc) hcc

theorem quot_cent {L Q V₂ : Subgroup G} (hZ : centerOf L = CFSG.Open.pCoreOf 2 L)
    (hQ : IsSylowTwoOf Q L) (hV4 : Nat.card V₂ = 4) (hV2 : ∀ x ∈ V₂, x * x = 1)
    (hVQ : V₂ ≤ Q) (hQV : Q ≤ Subgroup.normalizer (V₂ : Set G))
    (hVz : ∀ x ∈ V₂, x ∈ centerOf L → x = 1)
    (hX : SylowKleinSelfCent (↥L ⧸ Subgroup.center ↥L)) :
    ∀ g ∈ L, (∀ v ∈ V₂, g * v = v * g) → ∃ v ∈ V₂, g * v⁻¹ ∈ centerOf L := by
  classical
  intro g hgL hgc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Tsyl, hT, hTcomap, hNcomap⟩ := exists_quotSylow hZ hQ
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  set T' : Subgroup (↥L ⧸ Z) := (Tsyl : Subgroup (↥L ⧸ Z)) with hTdef
  have hTsyl : IsSylowTwoOf T' ⊤ :=
    K1.isSylowTwoOf_top_iff.mpr ⟨Tsyl.isPGroup', Tsyl.not_dvd_index⟩
  have hVL : V₂ ≤ L := hVQ.trans hQ.1
  set Vbar : Subgroup (↥L ⧸ Z) := (V₂.subgroupOf L).map π with hVbar
  have hVT : Vbar ≤ T' := by
    rw [hT]
    refine Subgroup.map_mono fun x hx => ?_
    exact Subgroup.mem_subgroupOf.mpr (hVQ (Subgroup.mem_subgroupOf.mp hx))
  have hKcard : Nat.card (V₂.subgroupOf L) = 4 := by
    rw [← hV4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVL).toEquiv
  have hinj : Function.Injective (π.comp (V₂.subgroupOf L).subtype) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk' : π (k : ↥L) = 1 := hk
    have hkZ : (k : ↥L) ∈ Z := by
      rw [← hker]
      exact hk'
    have hkc : ((k : ↥L) : G) ∈ centerOf L := SBc2.mem_centerOf_iff_center.mpr hkZ
    have hkV : ((k : ↥L) : G) ∈ V₂ := Subgroup.mem_subgroupOf.mp k.2
    exact Subtype.ext (Subtype.ext (hVz _ hkV hkc))
  have hVbar4 : Nat.card Vbar = 4 := by
    have h1 : (π.comp (V₂.subgroupOf L).subtype).range = Vbar := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hKcard
  have hVbar2 : ∀ v ∈ Vbar, v * v = 1 := by
    rintro _ ⟨x₀, hx₀, rfl⟩
    rw [← map_mul]
    have hxV : (x₀ : G) ∈ V₂ := Subgroup.mem_subgroupOf.mp hx₀
    have : x₀ * x₀ = 1 := Subtype.ext (hV2 _ hxV)
    rw [this, map_one]
  have hTN : T' ≤ Subgroup.normalizer (Vbar : Set (↥L ⧸ Z)) := by
    intro t' ht'
    rw [hT] at ht'
    obtain ⟨l, hl, rfl⟩ := ht'
    have hlQ : (l : G) ∈ Q := Subgroup.mem_subgroupOf.mp hl
    have hlV : (l : G) ∈ Subgroup.normalizer (V₂ : Set G) := hQV hlQ
    have hlV' : l ∈ Subgroup.normalizer ((V₂.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      (SBc2.mem_normalizer_subgroupOf_iff hVL l).mpr hlV
    refine A4.mem_normalizer_of_conj_mem fun vbar hvbar => ?_
    obtain ⟨a, ha, rfl⟩ := hvbar
    refine ⟨l * a * l⁻¹, (Subgroup.mem_normalizer_iff.mp hlV' a).mp ha, ?_⟩
    simp [map_mul, map_inv]
  have hmem : π ⟨g, hgL⟩ ∈ Vbar := hX T' Vbar hTsyl hVT hVbar4 hVbar2 hTN (π ⟨g, hgL⟩) (by
    rintro _ ⟨x₀, hx₀, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hgc _ (Subgroup.mem_subgroupOf.mp hx₀)))
  obtain ⟨x₀, hx₀, hx₀π⟩ := hmem
  refine ⟨(x₀ : G), Subgroup.mem_subgroupOf.mp hx₀, ?_⟩
  have h1 : (⟨g, hgL⟩ : ↥L) * x₀⁻¹ ∈ Z := by
    rw [← hker]
    show π ((⟨g, hgL⟩ : ↥L) * x₀⁻¹) = 1
    rw [map_mul, map_inv, ← hx₀π, mul_inv_cancel]
  exact SBc2.mem_centerOf_iff_center.mpr h1

theorem el_a4 {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp1 T Mc M V₁ V₂ Yp I L t) (o : Concl15343Open T M V₁ V₂ Yp I L)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L)
    (hX : SylowKleinSelfCent (↥L ⧸ Subgroup.center ↥L)) : False := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hLc : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hV2S : V₂ ≤ Sgp153 T V₁ := R3c8.V₂_le_Sgp153 hh.hyp hh.decomp
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hYpM : Yp ≤ M := hh.Yp_le_Y153.trans (Y153_le Mc M)
  have hYpI : Yp ≤ I := le_sup_left.trans c.inH.1.1
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := fun s hs => hN (hSI hs)
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  set Q : Subgroup G := Sgp153 T V₁ ⊓ L with hQdef
  have hMIY : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := fun x hx => by
    have : x ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by rw [c.facts.norm_eq]; exact hx
    exact this.2
  have hMIV : M ⊓ I ≤ Subgroup.normalizer (V₂ : Set G) :=
    R3c8.MI_le_normalizer_V₂ hh o.b_V1 o.b_V2.1 c.facts.norm_eq
  have hV2Y : V₂ ≤ Yp := by
    have h1 : ⁅V₂, Yp⁆ ≤ Yp := by
      rw [Subgroup.commutator_le]
      intro v hv y hy
      have hvN : v ∈ Subgroup.normalizer (Yp : Set G) := hMIY ⟨hSM (hV2S hv), hSI (hV2S hv)⟩
      have h2 : v * y * v⁻¹ ∈ Yp := (Subgroup.mem_normalizer_iff.mp hvN y).mp hy
      have : ⁅v, y⁆ = (v * y * v⁻¹) * y⁻¹ := rfl
      rw [this]
      exact Yp.mul_mem h2 (Yp.inv_mem hy)
    rwa [o.b_V2.1] at h1
  have hYN : Yp ≤ Subgroup.normalizer (V₂ : Set G) := fun y hy => hMIV ⟨hYpM hy, hYpI hy⟩
  obtain ⟨eV⟩ := o.b_V2.2
  have hV4 : Nat.card V₂ = 4 := by
    rw [Nat.card_congr eV.toEquiv, Nat.card_eq_fintype_card]
    simp
  have hV2sq : ∀ v ∈ V₂, v * v = 1 := by
    intro v hv
    have h1 : eV ⟨v, hv⟩ * eV ⟨v, hv⟩ = 1 := by
      ext i
      simp
      exact CharTwo.add_self_eq_zero _
    have : (⟨v, hv⟩ : ↥V₂) * ⟨v, hv⟩ = 1 := eV.injective (by rw [map_mul, h1, map_one])
    simpa using congrArg Subtype.val this
  obtain ⟨a, hcard⟩ : ∃ a : ℕ, Nat.card ↥Yp = 2 ^ a * 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥Yp)
    obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 :
      IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥Yp)).exists_card_eq
    refine ⟨a, ?_⟩
    have h2 : Nat.card (↥Yp ⧸ CFSG.Open.pCore 2 ↥Yp) = 3 := o.a_ord
    rw [h1, ha, h2, mul_comm]
  have hgen : Yp = Subgroup.closure {x : G | x ∈ Yp ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
    apply le_antisymm
    · conv_lhs => rw [o.a_eq]
      rw [oPrimeResidualOf, Subgroup.closure_le]
      intro x hx
      have hxY : x ∈ Yp := by
        rw [o.a_eq]
        exact Subgroup.subset_closure hx
      exact Subgroup.subset_closure ⟨hxY, hx.2⟩
    · rw [Subgroup.closure_le]
      exact fun x hx => hx.1
  have hact : ¬ Yp ≤ Subgroup.centralizer (V₂ : Set G) := by
    intro hle
    have h1 : ⁅Yp, V₂⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    have h2 : ⁅V₂, Yp⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h1
    rw [o.b_V2.1] at h2
    have : Nat.card V₂ = 1 := by rw [h2]; simp
    omega
  have hfix : ∀ x ∈ V₂, (∀ b ∈ Yp, b * x = x * b) → x = 1 :=
    fixed_eq_one_of_gen hV4 hgen hYN hact
  have hV2L : V₂ ≤ L := hV2Y.trans hYL
  have hVQ : V₂ ≤ Q := le_inf hV2S hV2L
  have hQS : Q ≤ Sgp153 T V₁ := inf_le_left
  have hQV : Q ≤ Subgroup.normalizer (V₂ : Set G) := fun q hq => hMIV ⟨hSM (hQS hq), hSI (hQS hq)⟩
  have hVz : ∀ x ∈ V₂, x ∈ centerOf L → x = 1 := fun x hx hxc =>
    hfix x hx fun b hb => Subgroup.mem_centralizer_iff.mp hxc.2 b (hYL hb)
  have hZ2 : ∀ z ∈ centerOf L, ∃ k : ℕ, orderOf z = 2 ^ k := by
    intro z hz
    have hzQ : z ∈ Q := by
      rw [hZ] at hz
      exact QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hQsyl hz
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hQsyl.2.1) (⟨z, hzQ⟩ : ↥Q)
    exact ⟨j, (Subgroup.orderOf_coe (⟨z, hzQ⟩ : ↥Q)).trans hj⟩
  have hC := quot_cent hZ hQsyl hV4 hV2sq hVQ hQV hVz hX
  obtain ⟨e⟩ := el_core hYL hV2Y hYN hV4 hV2sq hgen ⟨a, hcard⟩ hact hZ2 hVz hC
  exact o.d_notA4 ⟨e⟩

end Gen

end CFSG.Quasithin.R3c13

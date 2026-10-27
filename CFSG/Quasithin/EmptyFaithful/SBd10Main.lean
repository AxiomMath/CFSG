module

public import CFSG.Quasithin.EmptyFaithful.SBd10Env
public import CFSG.Quasithin.EmptyFaithful.SBd9Borel
public import CFSG.Quasithin.EmptyFaithful.SBd10U34

public section

namespace CFSG.Quasithin.SBd10

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Quasithin.R3c9
  CFSG.Quasithin.SBd9
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter sylowCenter_le)

theorem le_of_two_distinct {G : Type} [Group G] {V K : Subgroup G} (hV4 : Nat.card ↥V = 4)
    {v w : G} (hv : v ∈ V) (hw : w ∈ V) (hvK : v ∈ K) (hwK : w ∈ K) (hv1 : v ≠ 1) (hw1 : w ≠ 1)
    (hvw : v ≠ w) : V ≤ K := by
  classical
  have : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hV4]; norm_num)
  set W : Subgroup G := V ⊓ K with hW
  have hWV : W ≤ V := inf_le_left
  have : Finite ↥W := Finite.of_injective (Subgroup.inclusion hWV) (Subgroup.inclusion_injective hWV)
  have hdvd : Nat.card ↥W ∣ 4 := hV4 ▸ Subgroup.card_dvd_of_le hWV
  have h3 : 3 ≤ Nat.card ↥W := by
    have hinj : Function.Injective
        (![(⟨1, W.one_mem⟩ : ↥W), ⟨v, ⟨hv, hvK⟩⟩, ⟨w, ⟨hw, hwK⟩⟩] : Fin 3 → ↥W) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [Subtype.ext_iff, eq_comm]
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  have h4 : Nat.card ↥W = 4 := by
    have : Nat.card ↥W ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card ↥W <;> omega
  have hWeq : W = V := Subgroup.eq_of_le_of_card_ge hWV (by rw [h4, hV4])
  rw [← hWeq]
  exact inf_le_right


theorem mem_normalizer_sylowCenter {G : Type} [Group G] {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) : g ∈ Subgroup.normalizer (sylowCenter Q : Set G) := by
  have key : ∀ g' ∈ Subgroup.normalizer (Q : Set G), ∀ x ∈ sylowCenter Q,
      g' * x * g'⁻¹ ∈ sylowCenter Q := by
    intro g' hg' x hx
    obtain ⟨hxQ, hxc⟩ := mem_sylowCenter.mp hx
    refine mem_sylowCenter.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg' x).mp hxQ, fun t ht => ?_⟩
    have ht' : g'⁻¹ * t * g' ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg') t).mp ht
      simpa using this
    have h1 := hxc _ ht'
    calc t * (g' * x * g'⁻¹) = g' * ((g'⁻¹ * t * g') * x) * g'⁻¹ := by group
      _ = g' * (x * (g'⁻¹ * t * g')) * g'⁻¹ := by rw [h1]
      _ = g' * x * g'⁻¹ * t := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key g hg h hh, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using this


theorem inf_conj_eq_bot {G : Type} [Group G] [Finite G]
    {L Q V₂ YL Lt : Subgroup G} (hBender : fusionIsBenderGroup ↥L) (hLs : IsSimpleGroup ↥L)
    (hQ : IsSylowTwoOf Q L) (hV₂Z : V₂ ≤ sylowCenter Q) (hZ4 : Nat.card ↥(sylowCenter Q) = 4)
    (hV₂4 : Nat.card ↥V₂ = 4) (hYLB : YL ≤ L ⊓ Subgroup.normalizer (Q : Set G))
    (hYLgen : YL ≤ Subgroup.closure {x : G | x ∈ YL ∧ ∃ k : ℕ, orderOf x = 3 ^ k})
    (hYLnc : ¬ ∀ y ∈ YL, ∀ v ∈ V₂, y * v = v * y)
    (hBLt : L ⊓ Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (Lt : Set G))
    (hV₂Lt : ∀ v ∈ V₂, ∀ w ∈ Lt, v * w = w * v)
    (hLt1 : ∀ z ∈ Lt, (∀ w ∈ Lt, z * w = w * z) → z = 1) : L ⊓ Lt = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B : Subgroup G := L ⊓ Subgroup.normalizer (Q : Set G) with hBdef
  set X : Subgroup G := L ⊓ Lt with hXdef
  have hQL : Q ≤ L := hQ.1
  have hBX : B ≤ Subgroup.normalizer (X : Set G) := fun b hb =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hb.1, hBLt hb⟩
  have hV₂eq : V₂ = sylowCenter Q := Subgroup.eq_of_le_of_card_ge hV₂Z (by rw [hV₂4, hZ4])
  have hV₂Q : V₂ ≤ Q := hV₂Z.trans (sylowCenter_le Q)
  have hV₂notLt : ¬ V₂ ≤ Lt := by
    intro h
    have hb : V₂ = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      exact Subgroup.mem_bot.mpr (hLt1 v (h hv) (hV₂Lt v hv))
    rw [hb, Subgroup.card_bot] at hV₂4
    omega
  by_contra hXne
  have hXL : X ≤ L := inf_le_left
  have hQR : Q ≤ L ⊓ Subgroup.normalizer (X : Set G) :=
    fun q hq => ⟨hQL hq, hBX ⟨hQL hq, Subgroup.le_normalizer hq⟩⟩
  rcases GoldS146R.bender_overgroup hBender hQ hQR inf_le_left with hR | hR
  ·
    have hXB : X ≤ B := fun x hx => by
      have hxR : x ∈ L ⊓ Subgroup.normalizer (X : Set G) := ⟨hXL hx, Subgroup.le_normalizer hx⟩
      exact ⟨hXL hx, hR hxR⟩
    have hXQ : X ⊓ Q ≠ ⊥ := by
      intro hbot
      apply hXne
      rw [eq_bot_iff]
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (Q : Set G) := (hXB hx).2
      have hcomm : ∀ p ∈ Q, x * p = p * x := by
        intro p hp
        have hpB : p ∈ B := ⟨hQL hp, Subgroup.le_normalizer hp⟩
        have h1 : x * p * x⁻¹ * p⁻¹ ∈ X := by
          have hpx : p * x⁻¹ * p⁻¹ ∈ X := by
            have := (Subgroup.mem_normalizer_iff.mp (hBX hpB) x⁻¹).mp (X.inv_mem hx)
            simpa using this
          have : x * (p * x⁻¹ * p⁻¹) ∈ X := X.mul_mem hx hpx
          simpa [mul_assoc] using this
        have h2 : x * p * x⁻¹ * p⁻¹ ∈ Q := by
          have := (Subgroup.mem_normalizer_iff.mp hxN p).mp hp
          exact Q.mul_mem this (Q.inv_mem hp)
        have h3 : x * p * x⁻¹ * p⁻¹ ∈ X ⊓ Q := ⟨h1, h2⟩
        rw [hbot, Subgroup.mem_bot] at h3
        calc x * p = (x * p * x⁻¹ * p⁻¹) * (p * x) := by group
          _ = p * x := by rw [h3, one_mul]
      have hxQ : x ∈ Q := bender_cent_le hBender hQ x (hXL hx) hcomm
      have : x ∈ X ⊓ Q := ⟨hx, hxQ⟩
      rw [hbot] at this
      exact this
    have hQ2 : IsPGroup 2 ↥Q := hQ.2.1
    have hnil : Group.IsNilpotent ↥Q := hQ2.isNilpotent
    have hPn : ((X ⊓ Q).subgroupOf Q).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
      intro q hq
      have hqB : q ∈ B := ⟨hQL hq, Subgroup.le_normalizer hq⟩
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨(Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hBX hqB, Subgroup.le_normalizer hq⟩), Subgroup.le_normalizer hq⟩
    have hPne : (X ⊓ Q).subgroupOf Q ≠ ⊥ := by
      intro h
      apply hXQ
      rw [eq_bot_iff]
      intro x hx
      have hxQ : x ∈ Q := hx.2
      have : (⟨x, hxQ⟩ : ↥Q) ∈ (X ⊓ Q).subgroupOf Q := hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hPne
    obtain ⟨⟨w, hwmem⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcen
    have hwP : w ∈ (X ⊓ Q).subgroupOf Q := hwmem.1
    have hwC : w ∈ Subgroup.center ↥Q := hwmem.2
    have hv1 : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext (Subtype.ext h))
    have hvX : (w : G) ∈ X := hwP.1
    have hvQ : (w : G) ∈ Q := w.2
    have hvZ : (w : G) ∈ sylowCenter Q := by
      refine mem_sylowCenter.mpr ⟨hvQ, fun t ht => ?_⟩
      have := Subgroup.mem_center_iff.mp hwC ⟨t, ht⟩
      exact congrArg Subtype.val this
    have hvV₂ : (w : G) ∈ V₂ := hV₂eq ▸ hvZ
    obtain ⟨y, hyYL, ⟨k, hk⟩, hnc⟩ : ∃ y ∈ YL, (∃ k : ℕ, orderOf y = 3 ^ k) ∧
        ¬ ∀ v ∈ V₂, y * v = v * y := by
      by_contra hcon
      push Not at hcon
      apply hYLnc
      have hle : YL ≤ Subgroup.centralizer (V₂ : Set G) := by
        refine hYLgen.trans ((Subgroup.closure_le _).mpr fun y hy => ?_)
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro v hv
        exact (hcon y hy.1 hy.2 v hv).symm
      intro y hy v hv
      exact (Subgroup.mem_centralizer_iff.mp (hle hy) v hv).symm
    have hyB : y ∈ B := hYLB hyYL
    have hyN : y ∈ Subgroup.normalizer (V₂ : Set G) := by
      rw [hV₂eq]
      exact mem_normalizer_sylowCenter hyB.2
    have hfpf := fpf_of_orderOf_threePow hV₂4 hk hyN hnc
    have hw1' : y * (w : G) * y⁻¹ ≠ 1 := fun h => hv1 (by
      have := congrArg (fun z => y⁻¹ * z * y) h
      simpa [mul_assoc] using this)
    have hwV₂ : y * (w : G) * y⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hyN _).mp hvV₂
    have hwX : y * (w : G) * y⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hBX hyB) _).mp hvX
    have hV₂X : V₂ ≤ X :=
      le_of_two_distinct hV₂4 hvV₂ hwV₂ hvX hwX hv1 hw1' (fun h => hfpf _ hvV₂ hv1 h.symm)
    exact hV₂notLt (hV₂X.trans inf_le_right)
  ·
    have hnormL : (X.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXL).mpr fun l hl => (hR hl).2
    rcases hLs.eq_bot_or_eq_top_of_normal (X.subgroupOf L) with h | h
    · apply hXne
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hXL hx⟩ : ↥L) ∈ X.subgroupOf L := hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · have hLX : L ≤ X := fun l hl => by
        have : (⟨l, hl⟩ : ↥L) ∈ X.subgroupOf L := by rw [h]; trivial
        exact this
      exact hV₂notLt ((hV₂Q.trans (hQL.trans hLX)).trans inf_le_right)


section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

omit [Finite G] in
theorem mem_map_conj_iff {L : Subgroup G} {t g : G} :
    g ∈ L.map (MulAut.conj t).toMonoidHom ↔ t⁻¹ * g * t ∈ L := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    have : t⁻¹ * (t * l * t⁻¹) * t = l := by group
    simpa [this] using hl
  · intro h
    refine ⟨t⁻¹ * g * t, h, ?_⟩
    show t * (t⁻¹ * g * t) * t⁻¹ = g
    group

theorem conj_mem_normalizer_V₁ (D : Decomp153 T M V₁ V₂ t) {x : G}
    (hx : x ∈ Subgroup.normalizer (V₂ : Set G)) :
    t⁻¹ * x * t ∈ Subgroup.normalizer (V₁ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have e1 : g ∈ V₁ ↔ t * g * t⁻¹ ∈ V₂ := by
    rw [mem_V₂_iff_conj_mem_V₁ D (t * g * t⁻¹), show t⁻¹ * (t * g * t⁻¹) * t = g by group]
  have e2 : (t⁻¹ * x * t) * g * (t⁻¹ * x * t)⁻¹ =
      t⁻¹ * (x * (t * g * t⁻¹) * x⁻¹) * t := by group
  rw [e2, e1, ← mem_V₂_iff_conj_mem_V₁ D (x * (t * g * t⁻¹) * x⁻¹)]
  exact Subgroup.mem_normalizer_iff.mp hx (t * g * t⁻¹)

theorem normalizer_V₂_le_normalizer_conj (D : Decomp153 T M V₁ V₂ t)
    (hN : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)) {x : G}
    (hx : x ∈ Subgroup.normalizer (V₂ : Set G)) :
    x ∈ Subgroup.normalizer ((L.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  have hy := hN (conj_mem_normalizer_V₁ D hx)
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [mem_map_conj_iff, mem_map_conj_iff]
  have e : t⁻¹ * (x * g * x⁻¹) * t = (t⁻¹ * x * t) * (t⁻¹ * g * t) * (t⁻¹ * x * t)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp hy _

theorem odd_orderOf_threePow {Yp : Subgroup G} (hE9 : IsElemAbelianOfRank 3 2 (OTwoQuot Yp)) :
    ∀ x ∈ Yp, Odd (orderOf x) → ∃ k : ℕ, orderOf x = 3 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e9⟩ := hE9
  have h9 : Nat.card (OTwoQuot Yp) = 9 := by
    rw [Nat.card_congr e9.toEquiv]
    simp
  obtain ⟨b, hb⟩ : ∃ b : ℕ, Nat.card ↥Yp = 2 ^ b * 9 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥Yp)
    obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 :
      IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥Yp)).exists_card_eq
    refine ⟨a, ?_⟩
    have h2 : Nat.card (↥Yp ⧸ CFSG.Open.pCore 2 ↥Yp) = 9 := h9
    rw [h1, ha, h2]
    ring
  intro x hx hodd
  have hd : orderOf x ∣ 2 ^ b * 9 := hb ▸ Subgroup.orderOf_dvd_natCard Yp hx
  have hcop : Nat.Coprime (orderOf x) (2 ^ b) :=
    Nat.Coprime.pow_right b (Nat.coprime_two_right.mpr hodd)
  have h9' : orderOf x ∣ 3 ^ 2 := hcop.dvd_of_dvd_mul_left hd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h9'
  exact ⟨k, hk⟩

end Main


section Rest

open CFSG.Quasithin.R3c3

theorem input15340U34Rest_holds
    (h11 : StageLemma14111) (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h312 : A312ForSQTK) : Input15340U34Rest := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hL0 hr hU hLs hY h3L h3C hE9 hnot hYY hB hBM hQV h1 h2 h3 h4
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hq := hh.hyp.qtfe
  have hperf : Group.IsPerfect ↥L := c.c33.quasisimple.1
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  set S := Sgp153 T V₁ with hSdef
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := by
    have := le_normalizer_conjClosure L S
    rwa [← hL0] at this
  have hSyl : IsSylowTwoOf S I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (S ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  let eC := R3c3.quotCenterEquivOfSimple hLs hperf
  have hU' : IsPSU 3 2 2 ↥L := R3c3.isPSU_of_mulEquiv eC.symm hU
  have hBender : fusionIsBenderGroup ↥L :=
    K1.fusionIsBenderGroup_of_stated_psu_three (by norm_num) hU'
  have hZ1 : centerOf L = ⊥ := by
    have h0 := CFSG.Quasithin.R3c3.center_eq_bot_of_simple_perfect hLs hperf
    rw [eq_bot_iff]
    intro x hx
    have hxL : x ∈ L := hx.1
    have : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := SBc2.mem_centerOf_iff_center.mp hx
    rw [h0] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp this))
  have hLcen : ∀ g ∈ L, g ∈ Subgroup.centralizer (L : Set G) → g = 1 := fun g hgL hgC => by
    have : g ∈ centerOf L := ⟨hgL, hgC⟩
    rw [hZ1] at this
    exact Subgroup.mem_bot.mp this
  have hC : ∀ v ∈ V₁, ∀ x ∈ L, v * x = x * v := by
    intro v hv x hx
    have hvC : v ∈ Subgroup.centralizer (L : Set G) := ((oTwoUpper_le _).trans inf_le_right) (h1 hv)
    exact (Subgroup.mem_centralizer_iff.mp hvC x hx).symm
  have hN₁ := normalizer_V₁_le_normalizer_L h11 h113 h37 h38 h39 h312 c hL0 hLs hU' hYY hC
  obtain ⟨⟨z, hzL, hzN, hz5⟩, hZ4⟩ := borel_data_u34 hU' hQsyl
  have hzB : z ∈ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := ⟨hzL, hzN⟩
  have hzM : z ∈ M := (hBM hzB).1
  have hzpow : z ^ 5 = 1 := hz5 ▸ pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz5
    omega
  have hzV : z ∈ Subgroup.centralizer (VZ T M : Set G) := by
    have h72 := pow72_mem_centralizer hh hzM
    have : z = (z ^ 72) ^ 3 := by
      rw [← pow_mul, show 72 * 3 = 5 * 43 + 1 by norm_num, pow_add, pow_mul, hzpow, one_pow, one_mul,
        pow_one]
    rw [this]
    exact Subgroup.pow_mem _ h72 3
  have hV₂L : V₂ ≤ L := h3.trans ((oTwoUpper_le _).trans inf_le_right)
  have hV₂Z : V₂ ≤ sylowCenter (S ⊓ L) := by
    intro v hv
    have hvS : v ∈ S := VZ_le_Sgp153 hh (hh.decomp.le₂ hv)
    refine mem_sylowCenter.mpr ⟨⟨hvS, hV₂L hv⟩, fun q hq => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hQV hq) v (hh.decomp.le₂ hv)).symm
  have hV₂eq : V₂ = sylowCenter (S ⊓ L) :=
    Subgroup.eq_of_le_of_card_ge hV₂Z (by rw [hh.decomp.card₂, hZ4])
  have hYLL : oTwoUpper (Yp ⊓ L) ≤ L := (oTwoUpper_le _).trans inf_le_right
  have hYLB : oTwoUpper (Yp ⊓ L) ≤ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    le_inf hYLL (((oTwoUpper_le _).trans inf_le_left).trans (le_sup_left.trans hB))
  have hodd3 := odd_orderOf_threePow hE9
  have hYLgen : oTwoUpper (Yp ⊓ L) ≤
      Subgroup.closure {x : G | x ∈ oTwoUpper (Yp ⊓ L) ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hodd3 x hx.1.1 hx.2⟩
  set Lt : Subgroup G := L.map (MulAut.conj t).toMonoidHom with hLtdef
  have hBLt : L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Lt : Set G) := fun b hb =>
    normalizer_V₂_le_normalizer_conj hh.decomp hN₁ (by
      rw [hV₂eq]
      exact mem_normalizer_sylowCenter hb.2)
  have hV₂Lt : ∀ v ∈ V₂, ∀ w ∈ Lt, v * w = w * v := by
    intro v hv w hw
    have hv₁ : t⁻¹ * v * t ∈ V₁ := (mem_V₂_iff_conj_mem_V₁ hh.decomp v).mp hv
    have hwL : t⁻¹ * w * t ∈ L := mem_map_conj_iff.mp hw
    have hcomm := hC _ hv₁ _ hwL
    calc v * w = t * ((t⁻¹ * v * t) * (t⁻¹ * w * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * w * t) * (t⁻¹ * v * t)) * t⁻¹ := by rw [hcomm]
      _ = w * v := by group
  have hLt1 : ∀ w ∈ Lt, (∀ w' ∈ Lt, w * w' = w' * w) → w = 1 := by
    intro w hw hwc
    have hwL : t⁻¹ * w * t ∈ L := mem_map_conj_iff.mp hw
    have hc : t⁻¹ * w * t ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hlLt : t * l * t⁻¹ ∈ Lt := mem_map_conj_iff.mpr (by
        rw [show t⁻¹ * (t * l * t⁻¹) * t = l by group]
        exact hl)
      have := hwc _ hlLt
      calc l * (t⁻¹ * w * t) = t⁻¹ * ((t * l * t⁻¹) * w) * t := by group
        _ = t⁻¹ * (w * (t * l * t⁻¹)) * t := by rw [← this]
        _ = (t⁻¹ * w * t) * l := by group
    have h1' := hLcen _ hwL hc
    have : w = t * (t⁻¹ * w * t) * t⁻¹ := by group
    rw [this, h1']
    group
  have hXbot : L ⊓ Lt = ⊥ :=
    inf_conj_eq_bot hBender hLs hQsyl hV₂Z hZ4 hh.decomp.card₂ hYLB hYLgen h4 hBLt hV₂Lt hLt1
  set z' : G := t * z * t⁻¹ with hz'def
  have hz'5 : z' ^ 5 = 1 := by
    rw [hz'def, conj_pow, hzpow]
    group
  have hz'ne : z' ≠ 1 := fun h => hz1 (by
    have := congrArg (fun w => t⁻¹ * w * t) h
    simpa [hz'def, mul_assoc] using this)
  have htN : t ∈ Subgroup.normalizer (VZ T M : Set G) := hh.hyp.le_normalizer hh.decomp.t_mem
  have hz'V : z' ∈ Subgroup.centralizer (VZ T M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hu : t⁻¹ * v * t ∈ VZ T M := (Subgroup.mem_normalizer_iff''.mp htN v).mp hv
    have hcz := Subgroup.mem_centralizer_iff.mp hzV _ hu
    calc v * z' = t * ((t⁻¹ * v * t) * z) * t⁻¹ := by rw [hz'def]; group
      _ = t * (z * (t⁻¹ * v * t)) * t⁻¹ := by rw [hcz]
      _ = z' * v := by rw [hz'def]; group
  have hz'C₁ : z' ∈ Subgroup.centralizer (V₁ : Set G) :=
    Subgroup.centralizer_le (hh.decomp.le₁) hz'V
  have hz'I₁ : z' ∈ Subgroup.normalizer (V₁ : Set G) := Subgroup.centralizer_le_normalizer _ hz'C₁
  have hz'N : z' ∈ Subgroup.normalizer (L : Set G) := hN₁ hz'I₁
  have hz'L : z' ∉ L := by
    intro hz'L
    have hz'Lt : z' ∈ Lt := ⟨z, hzL, rfl⟩
    have : z' ∈ L ⊓ Lt := ⟨hz'L, hz'Lt⟩
    rw [hXbot, Subgroup.mem_bot] at this
    exact hz'ne this
  have : Group.IsPerfect ↥L := hperf
  obtain ⟨j, hjL, e, heC, hje⟩ := normalizer_pow_five_u34 L hU hz'N hz'5
  have hjeC : j * e = e * j := (Subgroup.mem_centralizer_iff.mp heC j hjL)
  have he1 : e ≠ 1 := fun h => hz'L (by rw [hje, h, mul_one]; exact hjL)
  have he5 : e ^ 5 = 1 := by
    have h1' : (j * e) ^ 5 = j ^ 5 * e ^ 5 := (Commute.mul_pow (hjeC : Commute j e) 5)
    rw [← hje, hz'5] at h1'
    have h2' : e ^ 5 = (j ^ 5)⁻¹ := eq_inv_of_mul_eq_one_right h1'.symm
    have hmemL : e ^ 5 ∈ L := by rw [h2']; exact L.inv_mem (L.pow_mem hjL 5)
    exact hLcen _ hmemL (Subgroup.pow_mem _ heC 5)
  have hLI₁ : L ≤ Subgroup.normalizer (V₁ : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv => hC v hv x hx)
  have heI₁ : e ∈ Subgroup.normalizer (V₁ : Set G) := by
    have hjI : j ∈ Subgroup.normalizer (V₁ : Set G) := hLI₁ hjL
    have : e = j⁻¹ * z' := by rw [hje]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hjI) hz'I₁
  obtain ⟨x, y, hx5, hy5, hxy, hx1, hxy1⟩ := exists_two_five_u34 hU'
  set I₁ : Subgroup G := Subgroup.normalizer (V₁ : Set G) with hI₁
  let φ : ↥L →* ↥I₁ := Subgroup.inclusion hLI₁
  have hφ : Function.Injective φ := Subgroup.inclusion_injective hLI₁
  let E : ↥I₁ := ⟨e, heI₁⟩
  have hrk : 3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥I₁) := by
    refine CFSG.SectionRank.ClassicalEven.three_le_pRank_of_gens (x := φ x) (y := φ y) (z := E)
      (by rw [← map_pow, hx5, map_one]) (by rw [← map_pow, hy5, map_one])
      (Subtype.ext (by simpa [E] using he5)) ?_ ?_ ?_ (fun h => hx1 (hφ (by rw [h, map_one])))
      (fun n h => hxy1 n (hφ (by rw [map_pow, h]))) ?_
    · exact (Commute.map (show Commute x y from hxy) φ)
    · refine Subtype.ext ?_
      change (x : G) * e = e * (x : G)
      exact (Subgroup.mem_centralizer_iff.mp heC x x.2)
    · refine Subtype.ext ?_
      change (y : G) * e = e * (y : G)
      exact (Subgroup.mem_centralizer_iff.mp heC y y.2)
    · intro n m h
      have h' := congrArg Subtype.val h
      have hmemL : e ∈ L := by
        have : ((x ^ n * y ^ m : ↥L) : G) = e := h'
        rw [← this]
        exact (x ^ n * y ^ m : ↥L).2
      exact he1 (hLcen _ hmemL heC)
  have hpC : pCoreOf 2 I₁ ≠ ⊥ := by
    have hV₁2 : IsPGroup 2 ↥V₁ := IsPGroup.of_card (n := 2) (by rw [hh.decomp.card₁]; norm_num)
    have hle : V₁ ≤ pCoreOf 2 I₁ := le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hV₁2
    intro hb
    rw [hb, le_bot_iff] at hle
    have := hh.decomp.card₁
    rw [hle, Subgroup.card_bot] at this
    omega
  have hle2 : CFSG.Open.pRank 5 I₁ ≤ 2 :=
    pRank_le_two_of_pCoreOf_ne_bot hq.qtke hpC (by norm_num) (by norm_num)
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at hle2
  omega

end Rest


section Top

theorem input15340U34_proved (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (hlist : Lemma115_3_List) (hA : R3c2.Input15333Two) : Input15340U34 :=
  input15340U34_of_rest h113 hlist hA (input15340U34Rest_holds h11 h113 h37 h38 h39 h312)

end Top

end CFSG.Quasithin.SBd10

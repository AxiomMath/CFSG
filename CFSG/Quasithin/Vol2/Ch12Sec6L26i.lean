module

public import CFSG.Quasithin.Vol2.Ch12Sec6L26h
public import CFSG.Quasithin.Vol2.Ch12Sec6L26f
public import CFSG.Quasithin.Vol2.Ch12Sec6L26g
public import CFSG.Quasithin.Vol2.Ch12Sec6L26e

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom CFSG.SectionRank
open CFSG.Blueprint CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F Equiv
open scoped IsMulCommutative

namespace S126L26

section Abstract

variable {P : Type} [Group P] [Finite P] {M : Type} [Group M] [Finite M]

theorem card_fix_conj {M : Type*} [Mul M] (f g : MulAut M) :
    Nat.card {w : M // (g * f * g⁻¹) w = w} = Nat.card {w : M // f w = w} :=
  Nat.card_congr
    { toFun := fun w => ⟨g⁻¹ w.1, by
        have h := congrArg (⇑(g⁻¹ : MulAut M)) w.2
        simpa [MulAut.mul_apply] using h⟩
      invFun := fun w => ⟨g w.1, by simp [MulAut.mul_apply, w.2]⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }

theorem false_of_five_action [Nontrivial P] (hP : IsPGroup 5 P)
    (hrk : CFSG.Open.pRank 5 (⊤ : Subgroup P) ≤ 2) (hM : IsPGroup 2 M) (ρ : P →* MulAut M)
    (hρ : ∀ z : P, z ≠ 1 → ∃ w : M, ρ z w ≠ w) (τ σ : MulAut P) (hτ3 : τ ^ 3 = 1)
    (hσ2 : σ ^ 2 = 1) (hτσ : τ * σ = σ * τ) (hτ1 : τ ≠ 1) (hσ1 : σ ≠ 1)
    (h8 : ∀ y : P, y ^ 5 = 1 → y ≠ 1 → σ y = y⁻¹ →
      Nat.card {w : M // ρ y w = w} * 2 ^ 8 = Nat.card M) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨Y, hY, hYf⟩ := exists_isSupercritical_faithful (p := 5) (P := P) (by norm_num) hP
  have hYc : Y.Characteristic := hY.characteristic
  have hmove : ∀ β : MulAut P, (orderOf β).Coprime 5 → β ≠ 1 → ∃ y ∈ Y, β y ≠ y := by
    intro β hβ hβ1
    by_contra hall
    push Not at hall
    exact hβ1 (hYf β hβ fun x hx => by rw [hall x hx, inv_mul_cancel]; exact Subgroup.one_mem _)
  obtain ⟨y₁, hy₁Y, hy₁⟩ := hmove τ
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hτ3) (by norm_num)) hτ1
  obtain ⟨y₂, hy₂Y, hy₂⟩ := hmove σ
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hσ2) (by norm_num)) hσ1
  obtain ⟨τY, hτdef⟩ : ∃ f, f = MulAut.characteristic Y τ := ⟨_, rfl⟩
  obtain ⟨σY, hσdef⟩ : ∃ f, f = MulAut.characteristic Y σ := ⟨_, rfl⟩
  have hτY : ∀ y : ↥Y, (τY y : P) = τ y := fun y => by
    rw [hτdef, MulAut.characteristic_apply_apply_coe]
  have hσY : ∀ y : ↥Y, (σY y : P) = σ y := fun y => by
    rw [hσdef, MulAut.characteristic_apply_apply_coe]
  have hτ3' : τY ^ 3 = 1 := by rw [hτdef, ← map_pow, hτ3, map_one]
  have hσ2' : σY ^ 2 = 1 := by rw [hσdef, ← map_pow, hσ2, map_one]
  have hτσ' : τY * σY = σY * τY := by
    rw [hτdef, hσdef, ← map_mul (MulAut.characteristic Y), ← map_mul (MulAut.characteristic Y),
      hτσ]
  have hτ1' : ∃ y : ↥Y, τY y ≠ y := ⟨⟨y₁, hy₁Y⟩, fun e => hy₁ (by
    have := congrArg Subtype.val e
    rwa [hτY] at this)⟩
  have hσ1' : ∃ y : ↥Y, σY y ≠ y := ⟨⟨y₂, hy₂Y⟩, fun e => hy₂ (by
    have := congrArg Subtype.val e
    rwa [hσY] at this)⟩
  have hexp : ∀ y : ↥Y, y ^ 5 = 1 := fun y =>
    Subtype.ext (by simpa using hY.pow_eq_one y.1 y.2)
  rcases hY.iso_cases (by norm_num) hP hrk with he | he | hX3
  ·
    obtain ⟨e⟩ := he
    have hcard5 : Nat.card Y = 5 := by
      rw [Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd), Nat.card_zmod]
    have hfix := S126Y.fix_of_card_five Y hcard5 τ (fun y hy => by
      have := (τY ⟨y, hy⟩).2
      rwa [hτY] at this) hτ3
    exact hy₁ (hfix y₁ hy₁Y)
  ·
    obtain ⟨e⟩ := he
    have hcommY : ∀ a b : ↥Y, a * b = b * a := fun a b => e.injective (by
      rw [map_mul, map_mul]
      exact mul_comm _ _)
    have hcard25 : Nat.card ↥Y = 25 := by
      rw [Nat.card_congr (e.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod]
      simp [Nat.card_eq_fintype_card]
    have hinvY := S126Y.inv_of_comm hcommY hcard25 hexp τY σY hτ3' hσ2' hτσ' hτ1' hσ1'
    let ε : Multiplicative (ZMod 5 × ZMod 5) ≃* Multiplicative (Fin 2 → ZMod 5) :=
      AddEquiv.toMultiplicative (LinearEquiv.finTwoArrow ℤ (ZMod 5)).toAddEquiv.symm
    let ψ : Multiplicative (ZMod 5 × ZMod 5) ≃* ↥Y := ε.trans e.symm
    let _ : MulDistribMulAction (Multiplicative (ZMod 5 × ZMod 5)) M :=
      MulDistribMulAction.compHom M ((ρ.comp Y.subtype).comp ψ.toMonoidHom)
    refine S126W.false_of_all_eight hM fun g hg => ?_
    show Nat.card {w // ρ (ψ g : P) w = w} * 2 ^ 8 = _
    refine h8 _ ?_ ?_ ?_
    · have := congrArg Subtype.val (hexp (ψ g))
      simpa using this
    · intro h1
      apply hg
      apply ψ.injective
      rw [map_one]
      exact Subtype.ext h1
    · have := congrArg Subtype.val (hinvY (ψ g))
      simpa [hσY] using this
  ·
    obtain ⟨hext, hc125, -⟩ := hX3
    have hZ5 : Nat.card (Subgroup.center ↥Y) = 5 := hext.center_order_p
    have hntZ : Nontrivial (Subgroup.center ↥Y) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hZ5]; norm_num)
    obtain ⟨⟨z₀, hz₀Z⟩, hz₀1⟩ := exists_ne (1 : Subgroup.center ↥Y)
    have hzc : ∀ x : ↥Y, z₀ * x = x * z₀ := fun x =>
      (Subgroup.mem_center_iff.mp hz₀Z x).symm
    have hz₀1' : z₀ ≠ 1 := fun e => hz₀1 (Subtype.ext e)
    have hz5 : orderOf z₀ = 5 := by
      rcases (Nat.dvd_prime Nat.prime_five).mp (orderOf_dvd_of_pow_eq_one (hexp z₀)) with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hz₀1'
      · exact h1
    have hZeq : Subgroup.center ↥Y = Subgroup.zpowers z₀ := by
      refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
      · rw [Subgroup.zpowers_le]
        exact hz₀Z
      · rw [hZ5, Nat.card_zpowers, hz5]
    have hqcomm := (hext.quotient_elementary_abelian).toIsMulCommutative
    have hcommY : ∀ a b : ↥Y, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z₀ := by
      intro a b
      rw [← hZeq, ← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hqcomm.is_comm.comm (a : ↥Y ⧸ Subgroup.center ↥Y) (b : ↥Y ⧸ Subgroup.center ↥Y)]
      group
    have hnab : ∃ a b : ↥Y, a * b ≠ b * a := by
      by_contra hall
      push Not at hall
      have htop : Subgroup.center ↥Y = ⊤ := by
        rw [eq_top_iff]
        intro a _
        exact Subgroup.mem_center_iff.mpr fun b => hall b a
      have h1 := congrArg (fun K : Subgroup ↥Y => Nat.card K) htop
      simp only [hZ5, Subgroup.card_top, hc125] at h1
      norm_num at h1
    obtain ⟨c, hc⟩ : ∃ c : ↥Y, c⁻¹ * σY c ∉ Subgroup.zpowers z₀ := by
      by_contra hall
      push Not at hall
      obtain ⟨y, hy⟩ := hσ1'
      exact hy (S126Y.eq_of_triv_mod hzc hz5 hcommY hnab σY hσ2' hall y)
    have hσσ : ∀ y, σY (σY y) = y := fun y => by
      rw [← MulAut.mul_apply, ← pow_two, hσ2', MulAut.one_apply]
    obtain ⟨d, hddef⟩ : ∃ d : ↥Y, c⁻¹ * σY c = d := ⟨_, rfl⟩
    rw [hddef] at hc
    have hσd : σY d = d⁻¹ := by
      rw [← hddef, map_mul, map_inv, hσσ, mul_inv_rev, inv_inv]
    have hd5 : d ^ 5 = 1 := hexp d
    have hz5' : z₀ ^ 5 = 1 := hexp z₀
    have hdz : d * z₀ = z₀ * d := (hzc d).symm
    obtain ⟨φ₀, hφ₀def⟩ : ∃ f, f = S126Y.e25Hom d z₀ hd5 hz5' hdz := ⟨_, rfl⟩
    let _ : MulDistribMulAction (Multiplicative (ZMod 5 × ZMod 5)) M :=
      MulDistribMulAction.compHom M ((ρ.comp Y.subtype).comp φ₀)
    refine S126W.false_of_five_eight hM (fun g hg => ?_) ?_
    · obtain ⟨a, hadef⟩ : ∃ a, (Multiplicative.toAdd g).1.val = a := ⟨_, rfl⟩
      obtain ⟨b, hbdef⟩ : ∃ b, (Multiplicative.toAdd g).2.val = b := ⟨_, rfl⟩
      have ha0 : a ≠ 0 := fun h0 => hg ((ZMod.val_eq_zero _).mp (hadef.trans h0))
      have ha5 : a < 5 := by
        rw [← hadef]
        exact ZMod.val_lt _
      have hdaZ : d ^ a ∉ Subgroup.zpowers z₀ := by
        intro hda
        apply hc
        obtain ⟨a', ha'⟩ : ∃ a' : ℕ, a * a' % 5 = 1 := by
          have key : ∀ r : ℕ, r < 5 → r ≠ 0 → ∃ a' : ℕ, a' < 5 ∧ r * a' % 5 = 1 := by decide
          obtain ⟨a', -, h'⟩ := key a ha5 ha0
          exact ⟨a', h'⟩
        have : d = (d ^ a) ^ a' := by
          rw [← pow_mul, S126Y.pow_eq_pow_mod_five hd5 (a * a'), ha', pow_one]
        rw [this]
        exact Subgroup.pow_mem _ hda _
      have hdac : ¬ ∀ x : ↥Y, d ^ a * x = x * d ^ a := by
        intro hall
        apply hdaZ
        rw [← hZeq]
        exact Subgroup.mem_center_iff.mpr fun x => (hall x).symm
      obtain ⟨x, hx⟩ := S126Y.exists_conj_mul hzc hz5 hcommY hdac b
      have hφ₀ : φ₀ g = x * d ^ a * x⁻¹ := by
        rw [hφ₀def, S126Y.e25Hom_apply, hadef, hbdef, hx]
        exact ((Commute.pow_pow (show Commute d z₀ from hdz) a b)).eq
      show Nat.card {w // ρ (φ₀ g : P) w = w} * 2 ^ 8 = _
      rw [hφ₀]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [card_fix_conj]
      refine h8 _ ?_ ?_ ?_
      · have := congrArg Subtype.val (hexp (d ^ a))
        simpa using this
      · intro h1
        apply hdaZ
        have : d ^ a = 1 := Subtype.ext h1
        rw [this]
        exact Subgroup.one_mem _
      · have hσda : σY (d ^ a) = (d ^ a)⁻¹ := by rw [map_pow, hσd, inv_pow]
        have := congrArg Subtype.val hσda
        simpa [hσY] using this
    ·
      obtain ⟨w, hw⟩ := hρ z₀ (fun h1 => hz₀1' (Subtype.ext h1))
      refine ⟨w, ?_⟩
      show ρ (φ₀ (Multiplicative.ofAdd ((0, 1) : ZMod 5 × ZMod 5)) : P) w ≠ w
      have hφz : φ₀ (Multiplicative.ofAdd ((0, 1) : ZMod 5 × ZMod 5)) = z₀ := by
        rw [hφ₀def, S126Y.e25Hom_apply]
        show d ^ (0 : ZMod 5).val * z₀ ^ (1 : ZMod 5).val = z₀
        rw [show (0 : ZMod 5).val = 0 from rfl, show (1 : ZMod 5).val = 1 from rfl, pow_zero,
          pow_one, one_mul]
      rw [hφz]
      exact hw

end Abstract

variable {G : Type} [Group G] [Finite G]

section Act

variable {T V L V₁ Vp H : Subgroup G}

theorem rhoU_Q (h : HypF91 T V L V₁ Vp H) (q : ↥H) (hq : (q : G) ∈ pCoreOf 2 H) :
    rhoU h q = 1 := by
  refine MulEquiv.ext fun w => Subtype.ext ?_
  rw [rhoU_apply, MulAut.one_apply]
  obtain ⟨u, hu, hue⟩ := (mem_tildeOf_iff h.H_normalizes_V₁
    (h.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H))).mp w.2
  rw [← hue, h.toTilde_comm_Q hq hu, mul_inv_cancel_right]

@[expose] noncomputable def rhoQ (h : HypF91 T V L V₁ Vp H) :
    ↥H ⧸ (pCoreOf 2 H).subgroupOf H →* MulAut ↥(tildeOf V₁ (conjClosure Vp H)) :=
  QuotientGroup.lift _ (rhoU h) fun q hq => rhoU_Q h q hq

theorem rhoQ_mk (h : HypF91 T V L V₁ Vp H) (y : ↥H) :
    rhoQ h (y : ↥H ⧸ (pCoreOf 2 H).subgroupOf H) = rhoU h y :=
  QuotientGroup.lift_mk _ _ _

theorem isPGroup_M (h : HypF91 T V L V₁ Vp H) :
    IsPGroup 2 ↥(tildeOf V₁ (conjClosure Vp H)) :=
  isPGroup_of_isElemAbelian h.isElemAbelian_tilde

theorem exists_moved (h : HypF91 T V L V₁ Vp H) {z : G} (hz : z ∈ H) (hzQ : z ∉ pCoreOf 2 H) :
    ∃ w : ↥(tildeOf V₁ (conjClosure Vp H)), rhoU h ⟨z, hz⟩ w ≠ w := by
  by_contra hall
  push Not at hall
  apply hzQ
  rw [h.pCoreOf_eq_centralizerMod]
  refine ⟨hz, h.H_normalizes_V₁ hz, fun u hu => ?_⟩
  have hUH : conjClosure Vp H ≤ H := h.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hw : toTilde h.H_normalizes_V₁ ⟨u, hUH hu⟩ ∈ tildeOf V₁ (conjClosure Vp H) :=
    (mem_tildeOf_iff h.H_normalizes_V₁ hUH).mpr ⟨⟨u, hUH hu⟩, hu, rfl⟩
  have h1 := congrArg Subtype.val (hall ⟨_, hw⟩)
  rw [rhoU_apply] at h1
  have h2 : toTilde h.H_normalizes_V₁ ⟨z, hz⟩ * toTilde h.H_normalizes_V₁ ⟨u, hUH hu⟩ =
      toTilde h.H_normalizes_V₁ ⟨u, hUH hu⟩ * toTilde h.H_normalizes_V₁ ⟨z, hz⟩ := by
    calc _ = toTilde h.H_normalizes_V₁ ⟨z, hz⟩ * toTilde h.H_normalizes_V₁ ⟨u, hUH hu⟩ *
          (toTilde h.H_normalizes_V₁ ⟨z, hz⟩)⁻¹ * toTilde h.H_normalizes_V₁ ⟨z, hz⟩ := by group
      _ = _ := by rw [h1]
  exact (toTilde_comm_iff h.H_normalizes_V₁).mp h2

end Act

section Frame

variable {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem exists_t (h1222 : Stmt12_2_2) (h1224 : Lemma12_6_24) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : S126.InHz T L F.V1 H) {X : Subgroup G} (hXH : X ≤ H)
    (hXn : H ≤ Subgroup.normalizer (X : Set G))
    (hX5 : ∀ x ∈ X, ∃ n : ℕ, x ^ 5 ^ n ∈ pCoreOf 2 H) {v₀ x₀ : G} (hv₀ : v₀ ∈ V)
    (hx₀ : x₀ ∈ X) (hvx₀ : v₀ * x₀ * v₀⁻¹ * x₀⁻¹ ∉ pCoreOf 2 H) :
    ∃ t ∈ Li L F.V1, t ^ 3 = 1 ∧ ∃ x ∈ X, t * x * t⁻¹ * x⁻¹ ∉ pCoreOf 2 H := by
  obtain ⟨h, -, -, -, -⟩ := setup126 h1224 F hH hZ hHz
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hvH : v₀ ∈ H := h.V_le_H hv₀
  have hV : ¬ V ≤ pCoreOf 2 H := by
    intro hle
    apply hvx₀
    have h1 : x₀ * v₀⁻¹ * x₀⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (hQn (hXH hx₀)) _).mp ((pCoreOf 2 H).inv_mem (hle hv₀))
    have e : v₀ * x₀ * v₀⁻¹ * x₀⁻¹ = v₀ * (x₀ * v₀⁻¹ * x₀⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem (hle hv₀) h1
  have hL1H : Li L F.V1 ≤ H := le_sup_left.trans h.L₁T_le_H
  have hA : ∃ x ∈ X, ∃ l ∈ Li L F.V1, x * l * x⁻¹ * l⁻¹ ∉ pCoreOf 2 H := by
    by_contra hA
    push Not at hA
    have hXK : X ≤ centralizerMod (pCoreOf 2 H) H (Li L F.V1) := fun x hx =>
      ⟨hXH hx, hQn (hXH hx), hA x hx⟩
    have hVO := le_pCoreOf_K h1222 h1224 F hH hZ hHz hV
    have hw1 : v₀ * x₀ * v₀⁻¹ * x₀⁻¹ ∈
        pCoreOf 2 (centralizerMod (pCoreOf 2 H) H (Li L F.V1)) := by
      have h1 : x₀ * v₀⁻¹ * x₀⁻¹ ∈ pCoreOf 2 (centralizerMod (pCoreOf 2 H) H (Li L F.V1)) :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ (hXK hx₀)) _).mp
          (Subgroup.inv_mem _ (hVO hv₀))
      have e : v₀ * x₀ * v₀⁻¹ * x₀⁻¹ = v₀ * (x₀ * v₀⁻¹ * x₀⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (hVO hv₀) h1
    have hw2 : v₀ * x₀ * v₀⁻¹ * x₀⁻¹ ∈ X := by
      have h1 : v₀ * x₀ * v₀⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hXn hvH) _).mp hx₀
      exact X.mul_mem h1 (X.inv_mem hx₀)
    obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 _) ⟨_, hw1⟩
    have ha' : (v₀ * x₀ * v₀⁻¹ * x₀⁻¹) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨b, hb⟩ := hX5 _ hw2
    exact hvx₀ (mem_of_pow_mem (Nat.Coprime.pow a b (by norm_num : Nat.Coprime 2 5))
      (by rw [ha']; exact Subgroup.one_mem _) hb)
  obtain ⟨x₁, hx₁, l₁, hl₁, hxl⟩ := hA
  by_contra hB
  push Not at hB
  have hle : Li L F.V1 ≤ centralizerMod (pCoreOf 2 H) H X := by
    show oTwoRes _ ≤ _
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨huLN, m, hm, hum⟩
    have huL1 : u ∈ Li L F.V1 := Subgroup.subset_closure ⟨huLN, m, hm, hum⟩
    have hu3 := S126L19b.pow_three_of_mem h1222 F hH huLN.1 huLN.2 hm hum
    exact ⟨hL1H huL1, hQn (hL1H huL1), hB u huL1 hu3⟩
  apply hxl
  have := (pCoreOf 2 H).inv_mem ((hle hl₁).2.2 x₁ hx₁)
  convert this using 1
  group

theorem centralizes_five (h1222 : Stmt12_2_2) (h1224 : Lemma12_6_24) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : S126.InHz T L F.V1 H) {X : Subgroup G} (hXH : X ≤ H)
    (hXn : H ≤ Subgroup.normalizer (X : Set G))
    (hX5 : ∀ x ∈ X, ∃ n : ℕ, x ^ 5 ^ n ∈ pCoreOf 2 H) :
    ∀ v ∈ V, ∀ x ∈ X, v * x * v⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨v₀, hv₀, x₀, hx₀, hvx₀⟩ := hcon
  obtain ⟨t, htL1, ht3, x₂, hx₂, htx₂⟩ :=
    exists_t h1222 h1224 F hH hZ hHz hXH hXn hX5 hv₀ hx₀ hvx₀
  obtain ⟨h, hidx, hyp5, hcard, hC⟩ := setup126 h1224 F hH hZ hHz
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hvH : v₀ ∈ H := h.V_le_H hv₀
  have hx₀Q : x₀ ∉ pCoreOf 2 H := by
    intro hx
    apply hvx₀
    have h1 : v₀ * x₀ * v₀⁻¹ ∈ pCoreOf 2 H := (Subgroup.mem_normalizer_iff.mp (hQn hvH) _).mp hx
    exact (pCoreOf 2 H).mul_mem h1 ((pCoreOf 2 H).inv_mem hx)
  have hv₀Q : v₀ ∉ pCoreOf 2 H := by
    intro hv
    apply hvx₀
    have h1 : x₀ * v₀⁻¹ * x₀⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (hQn (hXH hx₀)) _).mp ((pCoreOf 2 H).inv_mem hv)
    have e : v₀ * x₀ * v₀⁻¹ * x₀⁻¹ = v₀ * (x₀ * v₀⁻¹ * x₀⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem hv h1
  have hV : ¬ V ≤ pCoreOf 2 H := fun hle => hv₀Q (hle hv₀)
  have hv₀p : v₀ ∉ F.V5 := fun h5 => hv₀Q (h.Vp_le_pCoreOf_and_commutator_le.1 h5)
  have hL1H : Li L F.V1 ≤ H := le_sup_left.trans h.L₁T_le_H
  have hVK := V_le_K h1222 h1224 F hH hZ hHz
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot hH.hyp.qtke hH.hyp.simple
    hH.hyp.nonabelian hHz.1.2
  have htH : t ∈ H := hL1H htL1
  set N : Subgroup ↥H := (pCoreOf 2 H).subgroupOf H with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hQn
  set π : ↥H →* ↥H ⧸ N := QuotientGroup.mk' N with hπ
  have hπ1 : ∀ y : ↥H, π y = 1 ↔ (y : G) ∈ pCoreOf 2 H := fun y =>
    (QuotientGroup.eq_one_iff y).trans Subgroup.mem_subgroupOf
  have hπc : ∀ a b : ↥H, π a * π b * (π a)⁻¹ = π b ↔
      (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ pCoreOf 2 H := by
    intro a b
    have e : ((a * b * a⁻¹ * b⁻¹ : ↥H) : G) = (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ := rfl
    rw [← e, ← hπ1, map_mul, map_mul, map_mul, map_inv, map_inv]
    constructor
    · intro e1
      rw [e1, mul_inv_cancel]
    · intro e1
      calc π a * π b * (π a)⁻¹ = π a * π b * (π a)⁻¹ * (π b)⁻¹ * π b := by group
        _ = π b := by rw [e1, one_mul]
  set P' : Subgroup (↥H ⧸ N) := (X.subgroupOf H).map π with hP'
  have hP'n : ∀ y : ↥H, π y ∈ Subgroup.normalizer (P' : Set (↥H ⧸ N)) := by
    intro y
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨y * x * y⁻¹, ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.mp (hXn y.2) x).mp hx
    · rintro ⟨x, hx, hxe⟩
      refine ⟨y⁻¹ * x * y, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hXn (H.inv_mem y.2)) x).mp hx
        refine Subgroup.mem_subgroupOf.mpr ?_
        simpa [mul_assoc] using this
      · have : π x = π y * w * (π y)⁻¹ := hxe
        simp only [map_mul, map_inv, this]
        group
  let α : ↥H →* MulAut ↥P' := P'.normalizerMonoidHom.comp (π.codRestrict _ hP'n)
  have hα : ∀ (y : ↥H) (q : ↥P'), ((α y q : ↥P') : ↥H ⧸ N) = π y * q * (π y)⁻¹ := fun y q =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hP'5 : IsPGroup 5 ↥P' := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    obtain ⟨n, hn⟩ := hX5 x hx
    refine ⟨n, Subtype.ext ?_⟩
    show π x ^ 5 ^ n = 1
    rw [← map_pow, hπ1]
    exact hn
  have hx₀P : π ⟨x₀, hXH hx₀⟩ ∈ P' := ⟨⟨x₀, hXH hx₀⟩, hx₀, rfl⟩
  have hnt : Nontrivial ↥P' := ⟨⟨⟨_, hx₀P⟩, 1, fun e => hx₀Q ((hπ1 _).1
    (congrArg Subtype.val e))⟩⟩
  have hrk : CFSG.Open.pRank 5 (⊤ : Subgroup ↥P') ≤ 2 := by
    have h1 : CFSG.Open.pRank 5 (⊤ : Subgroup ↥H) ≤ 2 := hSQ.1 5 Nat.prime_five (by norm_num)
    have hN5 : ¬ 5 ∣ Nat.card N := by
      have h2 : IsPGroup 2 ↥N :=
        (pCoreOf_isPGroup 2 H).of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
      obtain ⟨k, hk⟩ := h2.exists_card_eq
      rw [hk]
      intro hd
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).mp
        (Nat.prime_five.dvd_of_dvd_pow hd)
      omega
    have h3 := pRank_quotient_eq N hN5
    have h4 := pRank_top_le_of_injective (p := 5) (by norm_num) P'.subtype P'.subtype_injective
    omega
  have hαt3 : α ⟨t, htH⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨t, htH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using ht3)
    rw [this, map_one]
  have hv2 : v₀ ^ 2 = 1 := isElemAbelian_pow_eq_one h.elemAbelian hv₀
  have hαv2 : α ⟨v₀, hvH⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨v₀, hvH⟩ : ↥H) ^ 2 = 1 := Subtype.ext (by simpa using hv2)
    rw [this, map_one]
  have hαt1 : α ⟨t, htH⟩ ≠ 1 := by
    intro h1
    apply htx₂
    have := congrArg (fun f : MulAut ↥P' => ((f ⟨π ⟨x₂, hXH hx₂⟩, ⟨_, hx₂, rfl⟩⟩ : ↥P') :
      ↥H ⧸ N)) h1
    simp only [hα, MulAut.one_apply] at this
    exact (hπc ⟨t, htH⟩ ⟨x₂, hXH hx₂⟩).1 this
  have hαv1 : α ⟨v₀, hvH⟩ ≠ 1 := by
    intro h1
    apply hvx₀
    have := congrArg (fun f : MulAut ↥P' => ((f ⟨π ⟨x₀, hXH hx₀⟩, hx₀P⟩ : ↥P') : ↥H ⧸ N)) h1
    simp only [hα, MulAut.one_apply] at this
    exact (hπc ⟨v₀, hvH⟩ ⟨x₀, hXH hx₀⟩).1 this
  have htv : α ⟨t, htH⟩ * α ⟨v₀, hvH⟩ = α ⟨v₀, hvH⟩ * α ⟨t, htH⟩ := by
    rw [← map_mul, ← map_mul]
    have hq : (((⟨v₀, hvH⟩ * ⟨t, htH⟩ : ↥H)⁻¹ * (⟨t, htH⟩ * ⟨v₀, hvH⟩) : ↥H) : G) ∈
        pCoreOf 2 H := by
      have h1 := (pCoreOf 2 H).inv_mem ((hVK hv₀).2.2 t htL1)
      have h2 := (Subgroup.mem_normalizer_iff.mp (hQn (H.inv_mem (H.mul_mem hvH htH))) _).mp h1
      convert h2 using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have h1 : α ((⟨v₀, hvH⟩ * ⟨t, htH⟩ : ↥H)⁻¹ * (⟨t, htH⟩ * ⟨v₀, hvH⟩)) = 1 := by
      refine MulEquiv.ext fun q => Subtype.ext ?_
      rw [hα, (hπ1 _).2 hq, one_mul, inv_one, mul_one]
      rfl
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  have hρ : ∀ z : ↥P', z ≠ 1 → ∃ w, (rhoQ h).comp P'.subtype z w ≠ w := by
    intro z hz1
    obtain ⟨x, -, hxz⟩ := z.2
    have hxQ : (x : G) ∉ pCoreOf 2 H := fun hxQ => hz1 (Subtype.ext (by
      rw [← hxz]
      exact (hπ1 x).2 hxQ))
    obtain ⟨w, hw⟩ := exists_moved h x.2 hxQ
    refine ⟨w, ?_⟩
    show rhoQ h (z : ↥H ⧸ N) w ≠ w
    rw [← hxz, show π x = (x : ↥H ⧸ N) from rfl, rhoQ_mk]
    exact hw
  have h8 : ∀ y : ↥P', y ^ 5 = 1 → y ≠ 1 → α ⟨v₀, hvH⟩ y = y⁻¹ →
      Nat.card {w // (rhoQ h).comp P'.subtype y w = w} * 2 ^ 8 =
        Nat.card ↥(tildeOf F.V1 (conjClosure F.V5 H)) := by
    intro y hy5 hy1 hyinv
    obtain ⟨x, -, hxy⟩ := y.2
    show Nat.card {w // rhoQ h (y : ↥H ⧸ N) w = w} * 2 ^ 8 = _
    rw [← hxy, show π x = (x : ↥H ⧸ N) from rfl, rhoQ_mk]
    refine card_fix_eight h hidx hV hyp5 hcard hC hv₀ hv₀p x.2 ?_ ?_ ?_
    · have h1 := congrArg Subtype.val hy5
      rw [Subgroup.coe_pow, ← hxy, ← map_pow] at h1
      exact (hπ1 _).1 h1
    · intro hxQ
      apply hy1
      refine Subtype.ext ?_
      rw [← hxy]
      exact (hπ1 x).2 hxQ
    · have h1 := congrArg Subtype.val hyinv
      rw [hα, Subgroup.coe_inv, ← hxy] at h1
      have h2 : π (⟨v₀, hvH⟩ * x * ⟨v₀, hvH⟩⁻¹ * x) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, h1, inv_mul_cancel]
      exact (hπ1 _).1 h2
  exact false_of_five_action hP'5 hrk (isPGroup_M h) ((rhoQ h).comp P'.subtype) hρ
    (α ⟨t, htH⟩) (α ⟨v₀, hvH⟩) hαt3 hαv2 htv hαt1 hαv1 h8

theorem centralizes_of_odd (h1222 : Stmt12_2_2) (h1224 : Lemma12_6_24) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : S126.InHz T L F.V1 H) {X : Subgroup G} (hXH : X ≤ H)
    (hXn : H ≤ Subgroup.normalizer (X : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hXr : ∀ x ∈ X, ∃ n : ℕ, x ^ r ^ n ∈ pCoreOf 2 H) :
    ∀ v ∈ V, ∀ x ∈ X, v * x * v⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
  by_cases hr5 : r = 5
  · subst hr5
    exact centralizes_five h1222 h1224 F hH hZ hHz hXH hXn hXr
  · exact centralizes_of_ne_five h1222 h1224 F hH hZ hHz hXH hXn hr hr2 hr5 hXr

end Frame

end S126L26

end CFSG.Quasithin.H13

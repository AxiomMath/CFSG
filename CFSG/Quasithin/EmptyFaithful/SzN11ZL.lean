module

public import CFSG.Quasithin.EmptyFaithful.SzN11Avg
public import CFSG.Quasithin.EmptyFaithful.A38cAutOn
public import CFSG.Quasithin.EmptyFaithful.A38cOrders
public import CFSG.Quasithin.EmptyFaithful.SzN6RL

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.Ch10.SecA CFSG.Quasithin.S1417 CFSG.QuasithinUnique.EscapingLocal
open scoped commutatorElement

section Short

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem szN11_short_of_lin2 (ctx : Ctx15316 T Mc M V₁ V₂ Yp I L t) {n : ℕ} (hn : 1 < n)
    (hlin : IsLin2Type L n) : IsShort2 L := by
  have hR : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := ctx.c16.R_norm
  obtain ⟨h1, -, h3⟩ := ctx.c16.desc
  obtain ⟨F₀, hF₀, hFin₀, hcard₀, α, hαs, hαk, -⟩ := id hlin
  have hF₀' : Nat.card F₀ = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard₀
  have e₀ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Matrix.SpecialLinearGroup (Fin 2) F₀ :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  have hN : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ n * (4 ^ n - 1) := by
    rw [Nat.card_congr e₀.toEquiv, card_SL_two_pow hF₀']
  have hsl : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F₀) :=
    isSimpleGroup_sl_two_pow hn hcard₀
  have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := e₀.isSimpleGroup
  have hShape : ShapeCard (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) := Or.inl ⟨n, hn, hN⟩
  have hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ Subgroup.centralizer
      (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)) : Set G) := h1.1.trans inf_le_right
  have hNV : L ⊔ R153 T V₁ Yp ≤ Subgroup.normalizer
      (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)) : Set G) := h1.2.2.2.1
  rcases h3 with ⟨hchi, -⟩ | hb | hc | hd | he | hf | hg | hh
  · exact hchi.1.1
  · obtain ⟨⟨m, α', hm5, hm8, hshort, -⟩, -⟩ := hb
    exact hshort
  · exact hc.1.1
  · exact hd.1.1
  · rcases he.1 with h | h <;> exact h.1
  · exact hf.1.1
  · exfalso
    obtain ⟨⟨m, F, _, _, hm1, hF, ⟨e⟩⟩, -, -⟩ := hg
    have hF' : Nat.card F = 2 ^ m := by rw [Nat.card_eq_fintype_card]; exact hF
    have hA : Nat.card ↥(autOn L (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)))) =
        2 ^ (3 * m) * ((2 ^ (3 * m) - 1) * (2 ^ (2 * m) - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL, card_SL_three_pow hF']
    have hnt : 1 < Nat.card ↥(autOn L
        (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)))) := by
      rw [hA]
      have h8 : 2 ≤ 2 ^ (3 * m) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h7 : 1 ≤ 2 ^ (3 * m) - 1 := by omega
      have h3 : 1 ≤ 2 ^ (2 * m) - 1 := by
        have : 2 ≤ 2 ^ (2 * m) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      calc 1 < 2 ^ (3 * m) := by omega
        _ ≤ 2 ^ (3 * m) * ((2 ^ (3 * m) - 1) * (2 ^ (2 * m) - 1)) :=
          Nat.le_mul_of_pos_right _ (Nat.mul_pos h7 h3)
    have heq := card_autOn_eq_card_quot hR hO hNV hnt
    rw [hA, hN] at heq
    exact card_sl_two_ne_card_sl_three (by omega) hm1 heq.symm
  · exfalso
    obtain ⟨hSL, -, -⟩ := hh
    rcases hSL with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have hA : Nat.card ↥(autOn L
          (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)))) = 20160 := by
        rw [Nat.card_congr e.toEquiv, card_statedSL,
          card_SL_four_of_two (K := ZMod 2) (by simp)]
      have heq := card_autOn_eq_card_quot hR hO hNV (by rw [hA]; norm_num)
      rw [hA] at heq
      exact not_shapeCard_20160 (heq ▸ hShape)
    · have hA : Nat.card ↥(autOn L
          (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)))) = 9999360 := by
        rw [Nat.card_congr e.toEquiv, card_statedSL,
          card_SL_five_of_two (K := ZMod 2) (by simp)]
      have heq := card_autOn_eq_card_quot hR hO hNV (by rw [hA]; norm_num)
      rw [hA] at heq
      exact not_shapeCard_9999360 (heq ▸ hShape)

end Short

theorem szN11_isElemAbelian_blockU {G : Type} [Group G] {L : Subgroup G} (hsh : IsShort2 L) :
    IsElemAbelian 2 (blockU L) := by
  obtain ⟨-, -, ⟨hUQ, hU2⟩, -⟩ := hsh
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, hU2⟩
  exact (Subgroup.mem_centralizer_iff.mp (hUQ a.2).2 b (hUQ b.2).1).symm

section Main

theorem lin2ZLInYL_holds (h37 : A37ForSQTK) (h38 : A38ForSQTK) : Lin2ZLInYL := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hn _ _
  classical
  obtain ⟨n, hn1, hlin⟩ := hn
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hI : IsHPlus Yp (Sgp153 T V₁) M I := c.ctx.inH
  have hF : Facts15311 T M V₁ Yp I := c.facts
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c.conc.1
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLI
  have hRL : IsSylowTwoOf (R153 T V₁ Yp ⊓ L) L :=
    lin2RLSylow_holds h37 h38 G T Mc M V₁ V₂ Yp I L t c ⟨n, hn1, hlin⟩
  have hsh : IsShort2 L := szN11_short_of_lin2 c hn1 hlin
  have hU : IsElemAbelian 2 (blockU L) := szN11_isElemAbelian_blockU hsh
  have hUQ : blockU L ≤ pCoreOf 2 L := szN4_blockU_le_pCoreOf
  have hQS₀ : pCoreOf 2 L ≤ R153 T V₁ Yp ⊓ L := pCoreOf_le_of_isSylowTwoOf hRL
  have hUS₀ : blockU L ≤ R153 T V₁ Yp ⊓ L := hUQ.trans hQS₀
  have hSsyl : IsSylowTwoOf (Sgp153 T V₁) (Yp ⊔ Sgp153 T V₁) :=
    A4.isSylowTwoOf_mono hF.sylow le_sup_right hI.1.1
  have hRS : R153 T V₁ Yp ≤ Sgp153 T V₁ := pCoreOf_le_of_isSylowTwoOf hSsyl
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) :=
    S153D.Sgp153_le_normalizer_Yp hh
  have hS₀N : ∀ s ∈ R153 T V₁ Yp ⊓ L, ∀ x ∈ Yp, s * x * s⁻¹ ∈ Yp :=
    fun s hs x hx => (Subgroup.mem_normalizer_iff.mp (hSN (hRS hs.1)) x).mp hx
  obtain ⟨y, hyY, hyo, hy1⟩ : ∃ y ∈ Yp ⊓ L, Odd (orderOf y) ∧ y ≠ 1 := by
    by_contra hno
    push Not at hno
    apply c.c16.YL_ne
    rw [eq_bot_iff]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, ho⟩
    exact Subgroup.mem_bot.mpr (hno x hx ho)
  have hyL : y ∈ L := hyY.2
  have hyYL : y ∈ YL153 Yp L := mem_oTwoUpper_of_odd hyY hyo
  have hYLn : ∀ s ∈ R153 T V₁ Yp ⊓ L, ∀ x ∈ YL153 Yp L, s * x * s⁻¹ ∈ YL153 Yp L := by
    intro s hs x hx
    have hsL : s ∈ L := hs.2
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      have hxo : Odd (orderOf (s * x * s⁻¹)) := by
        have : orderOf (s * x * s⁻¹) = orderOf x := by
          rw [← MulAut.conj_apply]
          exact MulEquiv.orderOf_eq _ _
        rw [this]
        exact hx.2
      exact mem_oTwoUpper_of_odd
        ⟨hS₀N s hs x hx.1.1, L.mul_mem (L.mul_mem hsL hx.1.2) (L.inv_mem hsL)⟩ hxo
    | one => simp
    | mul a b _ _ ha hb =>
      have : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
      rw [this]
      exact (YL153 Yp L).mul_mem ha hb
    | inv a _ ha =>
      have : s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ := by group
      rw [this]
      exact (YL153 Yp L).inv_mem ha
  have hUn : ∀ g ∈ L, ∀ u ∈ blockU L, g * u * g⁻¹ ∈ blockU L := fun g hg u hu =>
    (Subgroup.mem_normalizer_iff.mp (szN4_mem_normalizer_blockU (Subgroup.le_normalizer hg)) u).mp hu
  let Wk : Subgroup G := YL153 Yp L ⊓ blockU L
  have hS₀Wk : ∀ s ∈ R153 T V₁ Yp ⊓ L, ∀ x, x ∈ Wk ↔ s * x * s⁻¹ ∈ Wk := by
    intro s hs x
    have hsL : s ∈ L := hs.2
    have hsinv : s⁻¹ ∈ R153 T V₁ Yp ⊓ L := (R153 T V₁ Yp ⊓ L).inv_mem hs
    constructor
    · rintro ⟨hxY, hxU⟩
      exact ⟨hYLn s hs x hxY, hUn s hsL x hxU⟩
    · rintro ⟨hxY, hxU⟩
      have h1 := hYLn s⁻¹ hsinv _ hxY
      have h2 := hUn s⁻¹ (L.inv_mem hsL) _ hxU
      have e : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
      rw [e] at h1 h2
      exact ⟨h1, h2⟩
  have hcommW : ∀ u ∈ blockU L, u * y * u⁻¹ * y⁻¹ ∈ Wk := by
    intro u hu
    have hu1 : u * y * u⁻¹ ∈ YL153 Yp L := by
      refine mem_oTwoUpper_of_odd ⟨hS₀N u (hUS₀ hu) y hyY.1,
        L.mul_mem (L.mul_mem (szN4_blockU_le hu) hyL) (L.inv_mem (szN4_blockU_le hu))⟩ ?_
      have : orderOf (u * y * u⁻¹) = orderOf y := by
        rw [← MulAut.conj_apply]
        exact MulEquiv.orderOf_eq _ _
      rw [this]
      exact hyo
    refine ⟨(YL153 Yp L).mul_mem hu1 ((YL153 Yp L).inv_mem hyYL), ?_⟩
    have : u * y * u⁻¹ * y⁻¹ = u * (y * u⁻¹ * y⁻¹) := by group
    rw [this]
    exact (blockU L).mul_mem hu (hUn y hyL u⁻¹ ((blockU L).inv_mem hu))
  have hLN : L ≤ Subgroup.normalizer (blockU L : Set G) := fun g hg =>
    szN4_mem_normalizer_blockU (Subgroup.le_normalizer hg)
  let ψ : ↥L →* MulAut (IntMod (blockU L) hU) := (convI hU).comp (Subgroup.inclusion hLN)
  have hψ : ∀ (l : ↥L) (m : IntMod (blockU L) hU),
      (ψ l m).val = (l : G) * m.val * (l : G)⁻¹ := fun l m => convI_apply_val hU ⟨l, hLN l.2⟩ m
  let W : Subgroup (IntMod (blockU L) hU) := Wk.comap (inclMod hU)
  let Zs : Subgroup (IntMod (blockU L) hU) := (blockZ L).comap (inclMod hU)
  have hWmem : ∀ m : IntMod (blockU L) hU, m ∈ W ↔ m.val ∈ Wk := fun m => Iff.rfl
  have hZmem : ∀ m : IntMod (blockU L) hU, m ∈ Zs ↔ m.val ∈ blockZ L := fun m => Iff.rfl
  let B : Subgroup ↥L := (Subgroup.normalizer (Wk : Set G)).subgroupOf L
  have hBidx : ¬ 2 ∣ B.index := by
    have hle : (R153 T V₁ Yp ⊓ L).subgroupOf L ≤ B := by
      intro s hs
      have hs' : (s : G) ∈ R153 T V₁ Yp ⊓ L := hs
      show (s : G) ∈ Subgroup.normalizer (Wk : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro x
      exact hS₀Wk s hs' x
    intro h2
    exact hRL.2.2 (h2.trans (Subgroup.index_dvd_of_le hle))
  have hBW : ∀ b ∈ B, ∀ w ∈ W, ψ b w ∈ W := by
    intro b hb w hw
    have hbN : (b : G) ∈ Subgroup.normalizer (Wk : Set G) := hb
    rw [hWmem, hψ]
    exact (Subgroup.mem_normalizer_iff.mp hbN _).mp ((hWmem w).mp hw)
  have hZfix : ∀ g : ↥L, ∀ z ∈ Zs, ψ g z = z := by
    intro g z hz
    apply IntMod.val_injective
    rw [hψ]
    have hzC : z.val ∈ Subgroup.centralizer (L : Set G) := ((hZmem z).mp hz).2
    have := Subgroup.mem_centralizer_iff.mp hzC g g.2
    calc (g : G) * z.val * (g : G)⁻¹ = (z.val * g) * (g : G)⁻¹ := by rw [this]
      _ = z.val := by group
  have hWZ : ∀ m : IntMod (blockU L) hU, ∃ w ∈ W, ∃ z ∈ Zs, m = w * z := by
    let yL : ↥L := ⟨y, hyL⟩
    let σ : MulAut (IntMod (blockU L) hU) := ψ yL
    have hord : orderOf yL = orderOf y := Subgroup.orderOf_mk y hyL
    have hσ : σ ^ orderOf yL = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hm2 : orderOf yL % 2 = 1 := by
      rw [hord]
      exact Nat.odd_iff.mp hyo
    have hW' : ∀ m : IntMod (blockU L) hU, σ m * m⁻¹ ∈ W := by
      intro m
      rw [hWmem]
      have h1 : (σ m * m⁻¹).val = (m.val * y * m.val⁻¹ * y⁻¹)⁻¹ := by
        rw [IntMod.val_mul, IntMod.val_inv]
        have : (σ m).val = y * m.val * y⁻¹ := hψ yL m
        rw [this]
        group
      rw [h1]
      exact Wk.inv_mem (hcommW m.val m.val_mem)
    intro m
    obtain ⟨w, hw, c, hc, rfl⟩ := szN11_decomp σ hm2 hσ (fun m => IntMod.sq_eq_one m) hW' m
    refine ⟨w, hw, c, ?_, rfl⟩
    have hcy : y * c.val * y⁻¹ = c.val := by
      have h1 := congrArg IntMod.val hc
      have h2 : (σ c).val = y * c.val * y⁻¹ := hψ yL c
      rw [h2] at h1
      exact h1
    have hcC := S153F.lin2NatFixedPoints_proved G L n hlin y hyL hyo hy1 c.val c.val_mem hcy
    exact (hZmem c).mpr ⟨c.val_mem, hcC⟩
  have hcomm : ∀ {A : Type} [CommGroup A] (ρ : IntMod (blockU L) hU →* A),
      (∀ (g : ↥L) (m : IntMod (blockU L) hU), ρ (ψ g m) = ρ m) → ∀ m, ρ m = 1 := by
    intro A _ ρ hρ m
    let K : Subgroup G := ρ.ker.map (inclMod hU)
    have hK : ⁅blockU L, L⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro h₁ hh₁ h₂ hh₂
      let n₁ : IntMod (blockU L) hU := IntMod.mk hU ⟨h₁, hh₁⟩
      have hker : n₁ * (ψ ⟨h₂, hh₂⟩ n₁)⁻¹ ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hρ ⟨h₂, hh₂⟩ n₁, mul_inv_cancel]
      refine ⟨n₁ * (ψ ⟨h₂, hh₂⟩ n₁)⁻¹, hker, ?_⟩
      · show (n₁ * (ψ ⟨h₂, hh₂⟩ n₁)⁻¹).val = ⁅h₁, h₂⁆
        rw [IntMod.val_mul, IntMod.val_inv, hψ]
        simp only [commutatorElement_def, n₁]
        show h₁ * (h₂ * h₁ * h₂⁻¹)⁻¹ = h₁ * h₂ * h₁⁻¹ * h₂⁻¹
        group
    obtain ⟨m', hm', hm'v⟩ := hK (szN4_blockU_le_commutator hperf m.val_mem)
    have : m' = m := IntMod.val_injective hm'v
    rw [← this]
    exact hm'
  have hZW : Zs ≤ W :=
    szN11_central_le ψ hBidx (fun m => IntMod.sq_eq_one m) hBW hZfix hWZ hcomm
  intro z hz
  have hzmem : IntMod.mk hU ⟨z, hz.1⟩ ∈ Zs := hz
  exact ((hWmem _).mp (hZW hzmem)).1

end Main

end CFSG.Quasithin

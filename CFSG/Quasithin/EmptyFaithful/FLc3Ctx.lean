module

public import CFSG.Quasithin.EmptyFaithful.S151XB
public import CFSG.Quasithin.Background.FLc2UD
public import CFSG.Quasithin.Background.FLc3Excl
public import CFSG.Quasithin.Background.FLc2Simple

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Facts15128 (T Mc Z₁ Z₂ L : Subgroup G) : Prop where
  hU : IsElemAbelian 2 (uOf1527 Z₂ L)
  LU : L ≤ Subgroup.normalizer (uOf1527 Z₂ L : Set G)
  ZU : Z₂ ≤ uOf1527 Z₂ L
  ULU : uLOf1527 Z₂ L ≤ uOf1527 Z₂ L
  ZUle : zUOf1528 Z₂ L ≤ uLOf1527 Z₂ L
  SL : ∀ s ∈ s1516 T Z₁, ∀ l ∈ L, s * l * s⁻¹ ∈ L
  SZ : ∀ s ∈ s1516 T Z₁, ∀ z ∈ Z₂, s * z * s⁻¹ = z
  S2 : IsPGroup 2 (s1516 T Z₁)
  QS : q1_1516 Mc Z₁ ≤ s1516 T Z₁
  MQ : ∀ m ∈ mZ1516 Mc Z₁ ⊓ L, ∀ q ∈ q1_1516 Mc Z₁, m * q * m⁻¹ ∈ q1_1516 Mc Z₁
  ZUS : ∀ s ∈ s1516 T Z₁ ⊓ L, ∀ z ∈ zUOf1528 Z₂ L, s * z * s⁻¹ = z
  CM : ∀ l ∈ L, (∀ z ∈ zUOf1528 Z₂ L, l * z * l⁻¹ = z) → l ∈ mZ1516 Mc Z₁ ⊓ L
  hSylL : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L
  MLne : mZ1516 Mc Z₁ ⊓ L ≠ L
  decomp : ∀ z ∈ Z₂, ∃ u ∈ uLOf1527 Z₂ L, ∀ h ∈ L, h * (z * u) * h⁻¹ = z * u

theorem facts_of_ctx {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15128 T Mc M Z₁ Z₂ V₁ V₂ L) :
    Facts15128 T Mc Z₁ Z₂ L := by
  have hq := hc.ctx.qtfe
  have hM := hc.ctx.mf
  have hS := hc.ctx.setting
  have h18 := hc.h18
  have hsmall := ce15Small_of_four_or_six hc.h24.one
  have h7 := not_seven_of_four_or_six hc.h24.one
  have hdiag := hS.diagonal hsmall h7
  have hL1520 : IsL1520 T Mc Z₁ L := hc.hL.isL1520 h18.four (hS.pCore_g1_ne_bot hq hM)
  have hSylL : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow h18.four hL1520
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  obtain ⟨hU, -⟩ := hc.h27
  have hLN : g1_1516 Z₁ ≤ Subgroup.normalizer (L : Set G) := by
    have h := normalizer_le_normalizer_oPrimeResidualOf1516 3 (g1_1516 Z₁)
    rw [← hc.h25.one] at h
    exact Subgroup.le_normalizer.trans h
  have hSG : s1516 T Z₁ ≤ g1_1516 Z₁ := inf_le_right
  have hSL : ∀ s ∈ s1516 T Z₁, ∀ l ∈ L, s * l * s⁻¹ ∈ L := fun s hs l hl =>
    (Subgroup.mem_normalizer_iff.1 (hLN (hSG hs)) l).1 hl
  have hSZ : ∀ s ∈ s1516 T Z₁, ∀ z ∈ Z₂, s * z * s⁻¹ = z := by
    intro s hs z hz
    have hsC : s ∈ Subgroup.centralizer (Z₂ : Set G) := by
      have : s ∈ T ⊓ Subgroup.centralizer (Z₂ : Set G) := by rw [← hdiag.2]; exact hs
      exact this.2
    have := Subgroup.mem_centralizer_iff.1 hsC z hz
    calc s * z * s⁻¹ = (s * z) * s⁻¹ := rfl
      _ = (z * s) * s⁻¹ := by rw [← this]
      _ = z := by group
  have hSMZ : s1516 T Z₁ ≤ mZ1516 Mc Z₁ := le_inf hSG (inf_le_left.trans hq.t_le_mc)
  have hMZG : mZ1516 Mc Z₁ ≤ g1_1516 Z₁ := inf_le_left
  have hSylMZ : IsSylowTwoOf (s1516 T Z₁) (mZ1516 Mc Z₁) :=
    A4.isSylowTwoOf_mono h18.four hSMZ hMZG
  have hQS : q1_1516 Mc Z₁ ≤ s1516 T Z₁ :=
    CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSylMZ
  have hMZN : mZ1516 Mc Z₁ ≤ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) := by
    intro m hm
    have h5 := h18.five.2.1
    have : m ∈ g1_1516 Z₁ ⊓ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) := by rw [← h5]; exact hm
    exact this.2
  have hMQ : ∀ m ∈ mZ1516 Mc Z₁ ⊓ L, ∀ q ∈ q1_1516 Mc Z₁, m * q * m⁻¹ ∈ q1_1516 Mc Z₁ :=
    fun m hm q hq' => (Subgroup.mem_normalizer_iff.1 (hMZN hm.1) q).1 hq'
  have hCZ2 : ∀ x : G, x ∈ L → (x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ↔
      x ∈ Subgroup.centralizer (Z₂ : Set G)) := by
    intro x hx
    have h := congrArg (fun K : Subgroup G => x ∈ K) hdiag.1
    simp only [Subgroup.mem_inf, eq_iff_iff] at h
    constructor
    · intro hxc
      exact (h.1 ⟨hLG hx, hxc⟩).2
    · intro hxc
      exact (h.2 ⟨hLG hx, hxc⟩).2
  have hCZ : L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ mZ1516 Mc Z₁ ⊓ L := by
    intro x ⟨hxL, hxZ⟩
    refine ⟨⟨hLG hxL, ?_⟩, hxL⟩
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hq.omegaOneCenter_ne_bot
    have hzmem : (z : G) ∈ quasithinOmegaOneCenter T := z.2
    have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hHyp := h18.six (z : G) hzmem hz1'
    apply hHyp.centralizer_z_le
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hxZ (z : G) hzmem).symm
  have hMlne : mZ1516 Mc Z₁ ⊓ L ≠ L := fun h => hc.hL.not_le (by
    calc L = mZ1516 Mc Z₁ ⊓ L := h.symm
      _ ≤ mZ1516 Mc Z₁ := inf_le_left)
  have hLU : L ≤ Subgroup.normalizer (uOf1527 Z₂ L : Set G) := le_normalizer_conjClosure Z₂ L
  have hZ₂U : Z₂ ≤ uOf1527 Z₂ L := le_conjClosure Z₂ L
  have hULU : uLOf1527 Z₂ L ≤ uOf1527 Z₂ L := by
    unfold uLOf1527
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have h1 : l * u⁻¹ * l⁻¹ ∈ uOf1527 Z₂ L := (Subgroup.mem_normalizer_iff.1 (hLU hl) u⁻¹).1
      ((uOf1527 Z₂ L).inv_mem hu)
    have : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact (uOf1527 Z₂ L).mul_mem hu h1
  have hUc : ∀ a ∈ uOf1527 Z₂ L, ∀ b ∈ uOf1527 Z₂ L, a * b = b * a := fun a ha b hb => by
    have := hU.1
    exact setLike_mul_comm ha hb
  have hU2 : ∀ a ∈ uOf1527 Z₂ L, a ^ 2 = 1 := hU.2
  have hodd : Odd ((s1516 T Z₁ ⊓ L).relIndex L) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSylL.2.2)
  have hSLZ : ∀ s ∈ s1516 T Z₁ ⊓ L, ∀ z ∈ Z₂, s * z * s⁻¹ = z := fun s hs z hz => hSZ s hs.1 z hz
  have hd := FLc.ud_decomp hLU hUc hU2 hodd hZ₂U hSLZ
  have hcz := FLc.centralizer_zU_eq hd hZ₂U hULU
  refine ⟨hU, hLU, hZ₂U, hULU, inf_le_right, hSL, hSZ, h18.four.2.1, hQS, hMQ, ?_, ?_, hSylL, hMlne, hd⟩
  ·
    intro s hs z hz
    have hz' : z ∈ Z₂ ⊔ (uOf1527 Z₂ L ⊓ Subgroup.centralizer (L : Set G)) := hz.1
    have hle : Z₂ ⊔ (uOf1527 Z₂ L ⊓ Subgroup.centralizer (L : Set G)) ≤
        Subgroup.centralizer ({s} : Set G) := by
      refine sup_le (fun w hw => ?_) (fun c hc' => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have := hSZ s hs.1 w hw
        calc w * s = (s * w * s⁻¹) * s := by rw [this]
          _ = s * w := by group
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1 hc'.2 s hs.2).symm
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hz')
    calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [this]
      _ = z := by group
  ·
    intro l hl hfix
    have hcent : l ∈ Subgroup.centralizer (FLc.projZU Z₂ L (uOf1527 Z₂ L) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have := hfix z hz
      calc z * l = (l * z * l⁻¹) * l := by rw [this]
        _ = l * z := by group
    have h2 : l ∈ Subgroup.centralizer (Z₂ : Set G) := (hcz l hl).2 hcent
    exact hCZ ⟨hl, (hCZ2 l hl).2 h2⟩

omit [Finite G] in
theorem rho_conj_range {U : Subgroup G} {n : ℕ} {ρ₀ : FLc.SLt n →* MulAut ↥U}
    {H : Subgroup (MulAut ↥U)} (hrange : ∀ k ∈ H, ∃ g, ρ₀ g = k) (hrange' : ∀ g, ρ₀ g ∈ H)
    (h : FLc.SLt n) :
    (∀ k ∈ H, ∃ g, (ρ₀.comp (MulAut.conj h).toMonoidHom) g = k) ∧
      ∀ g, (ρ₀.comp (MulAut.conj h).toMonoidHom) g ∈ H := by
  refine ⟨fun k hk => ?_, fun g => hrange' _⟩
  obtain ⟨g, hg⟩ := hrange k hk
  refine ⟨h⁻¹ * g * h, ?_⟩
  show ρ₀ (h * (h⁻¹ * g * h) * h⁻¹) = k
  rw [← hg]
  congr 1
  group

omit [Finite G] in
theorem rho_inj_of_ne_bot {T Mc Z₁ Z₂ L : Subgroup G} (hF : Facts15128 T Mc Z₁ Z₂ L) {n : ℕ}
    (hn : 3 ≤ n) (ρ₀ : FLc.SLt n →* MulAut ↥(uOf1527 Z₂ L))
    (hrange : ∀ k ∈ autOn L (uOf1527 Z₂ L), ∃ g, ρ₀ g = k) (hne : uLOf1527 Z₂ L ≠ ⊥) :
    Function.Injective ρ₀ := by
  have := FLc.isSimpleGroup_SLt hn
  refine FLc.injective_of_ne_one ρ₀ ?_
  by_contra hall
  push Not at hall
  apply hne
  unfold uLOf1527
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  obtain ⟨g, hg⟩ := hrange (conjAct (uOf1527 Z₂ L) ⟨l, hF.LU hl⟩)
    (FLc.mem_autOn_iff.2 ⟨l, hF.LU hl, hl, rfl⟩)
  have h1 : conjAct (uOf1527 Z₂ L) ⟨l, hF.LU hl⟩ = 1 := by rw [← hg, hall g]
  have h2 := FLc.conjAct_coe (hF.LU hl) (⟨u, hu⟩ : ↥(uOf1527 Z₂ L))
  rw [h1] at h2
  have h3 : u = l * u * l⁻¹ := h2
  calc l * u = (l * u * l⁻¹) * l := by group
    _ = u * l := by rw [← h3]

theorem exists_normalized_rho {T Mc Z₁ Z₂ L : Subgroup G} (hF : Facts15128 T Mc Z₁ Z₂ L) {n : ℕ}
    (hn : 1 ≤ n) (ρ₀ : FLc.SLt n →* MulAut ↥(uOf1527 Z₂ L))
    (hrange : ∀ k ∈ autOn L (uOf1527 Z₂ L), ∃ g, ρ₀ g = k)
    (hrange' : ∀ g, ρ₀ g ∈ autOn L (uOf1527 Z₂ L)) :
    ∃ h : FLc.SLt n, ∀ u ∈ FLc.Ut n, (ρ₀.comp (MulAut.conj h).toMonoidHom) u ∈
      autOn (s1516 T Z₁ ⊓ L) (uOf1527 Z₂ L) := by
  let _ : CommGroup ↥(uOf1527 Z₂ L) := commGroupOfElemAbelian hF.hU
  have hsyl := FLc.exists_sylow_autOn hF.LU hF.hSylL hrange hrange'
  have hTle : autOn (s1516 T Z₁ ⊓ L) (uOf1527 Z₂ L) ≤ ρ₀.range := fun a ha => by
    obtain ⟨x, hx, hxS, rfl⟩ := FLc.mem_autOn_iff.1 ha
    obtain ⟨g, hg⟩ := hrange _ (FLc.mem_autOn_iff.2 ⟨x, hx, hxS.2, rfl⟩)
    exact ⟨g, hg⟩
  obtain ⟨h, hh⟩ := FLc.exists_rho_conj hn hTle hsyl
  refine ⟨h, fun u hu => ?_⟩
  rw [← hh]
  exact ⟨u, hu, rfl⟩

omit [Finite G] in
theorem autOn_ML_of_fixZ {T Mc Z₁ Z₂ L : Subgroup G} (hF : Facts15128 T Mc Z₁ Z₂ L) {n : ℕ}
    (ρ : FLc.SLt n →* MulAut ↥(uOf1527 Z₂ L)) (hrange' : ∀ g, ρ g ∈ autOn L (uOf1527 Z₂ L)) {J : Set ℕ}
    (hfixZ : ∀ x ∈ FLc.QI n J, ∀ v : ↥(uOf1527 Z₂ L), (v : G) ∈ zUOf1528 Z₂ L → ρ x v = v) :
    ∀ x ∈ FLc.QI n J, ρ x ∈ autOn (mZ1516 Mc Z₁ ⊓ L) (uOf1527 Z₂ L) := by
  intro x hx
  obtain ⟨l, hl, hlL, hρl⟩ := FLc.mem_autOn_iff.1 (hrange' x)
  have hlM : l ∈ mZ1516 Mc Z₁ ⊓ L := by
    refine hF.CM l hlL fun z hz => ?_
    have hzU : z ∈ uOf1527 Z₂ L := hF.ULU (hF.ZUle hz)
    have h1 := hfixZ x hx ⟨z, hzU⟩ hz
    rw [← hρl] at h1
    have h2 := congrArg (fun w : ↥(uOf1527 Z₂ L) => (w : G)) h1
    simpa [FLc.conjAct_coe hl] using h2
  rw [← hρl]
  exact FLc.mem_autOn_iff.2 ⟨l, hl, hlM, rfl⟩

omit [Finite G] in
theorem ctx_core_asym {T Mc Z₁ Z₂ L : Subgroup G} (hF : Facts15128 T Mc Z₁ Z₂ L) {n : ℕ} (hn : 3 ≤ n)
    (ρ : FLc.SLt n →* MulAut ↥(uOf1527 Z₂ L)) (hρinj : Function.Injective ρ)
    (hrange : ∀ k ∈ autOn L (uOf1527 Z₂ L), ∃ g, ρ g = k)
    (hrange' : ∀ g, ρ g ∈ autOn L (uOf1527 Z₂ L))
    (hT : ∀ u ∈ FLc.Ut n, ρ u ∈ autOn (s1516 T Z₁ ⊓ L) (uOf1527 Z₂ L)) {I I' : Set ℕ}
    (hII' : I ⊆ I') (hI' : ∀ i ∈ I', FLc.IsNode n i) (hasym : ∃ i ∈ I', n - i ∉ I')
    (hfixZ : ∀ x ∈ FLc.QI n I, ∀ v : ↥(uOf1527 Z₂ L), (v : G) ∈ zUOf1528 Z₂ L → ρ x v = v)
    (hmod : ∀ A'' : Subgroup (FLc.SLt n), A'' ≤ FLc.Ut n →
      (∀ y ∈ A'', ∀ i j : Fin n, i < j → (∀ d ∈ I, (i : ℕ) < d → (j : ℕ) < d) →
        FLc.mat y i j = 0) → A'' ≠ ⊥ →
      Nat.card (A''.map ρ) * Nat.card (@fixV ↥(uOf1527 Z₂ L) (commGroupOfElemAbelian hF.hU)
        (A''.map ρ)) < Nat.card ↥(uOf1527 Z₂ L))
    {A : Subgroup (MulAut ↥(uOf1527 Z₂ L))} (hAQ : A ≤ autOn (q1_1516 Mc Z₁) (uOf1527 Z₂ L))
    (hA : A ≠ ⊥) :
    Nat.card A * Nat.card (@fixV ↥(uOf1527 Z₂ L) (commGroupOfElemAbelian hF.hU) A) <
      Nat.card ↥(uOf1527 Z₂ L) :=
  FLc.core_not_ff_asym hF.hU hn ρ hρinj hF.LU hF.SL (le_refl _) hF.ZU hF.SZ hF.S2 hF.QS hF.MQ
    inf_le_right hrange hrange' hT hII' hI' hasym (autOn_ML_of_fixZ hF ρ hrange' hfixZ) hmod hAQ hA

theorem normalize_rho {T Mc Z₁ Z₂ L : Subgroup G} (hF : Facts15128 T Mc Z₁ Z₂ L) {n : ℕ} (hn : 3 ≤ n)
    (ρ₀ : FLc.SLt n →* MulAut ↥(uOf1527 Z₂ L))
    (hrange : ∀ k ∈ autOn L (uOf1527 Z₂ L), ∃ g, ρ₀ g = k)
    (hrange' : ∀ g, ρ₀ g ∈ autOn L (uOf1527 Z₂ L)) (hne : uLOf1527 Z₂ L ≠ ⊥) :
    ∃ h : FLc.SLt n, Function.Injective (ρ₀.comp (MulAut.conj h).toMonoidHom) ∧
      (∀ k ∈ autOn L (uOf1527 Z₂ L), ∃ g, (ρ₀.comp (MulAut.conj h).toMonoidHom) g = k) ∧
      (∀ g, (ρ₀.comp (MulAut.conj h).toMonoidHom) g ∈ autOn L (uOf1527 Z₂ L)) ∧
      (∀ u ∈ FLc.Ut n, (ρ₀.comp (MulAut.conj h).toMonoidHom) u ∈
        autOn (s1516 T Z₁ ⊓ L) (uOf1527 Z₂ L)) ∧
      (∀ s ∈ FLc.Ut n, ∀ v : ↥(uOf1527 Z₂ L), (v : G) ∈ zUOf1528 Z₂ L →
        (ρ₀.comp (MulAut.conj h).toMonoidHom) s v = v) := by
  have hinj := rho_inj_of_ne_bot hF hn ρ₀ hrange hne
  obtain ⟨h, hT⟩ := exists_normalized_rho hF (by omega) ρ₀ hrange hrange'
  obtain ⟨hr1, hr2⟩ := rho_conj_range hrange hrange' h
  refine ⟨h, fun x y hxy => (MulAut.conj h).injective (hinj hxy), hr1, hr2, hT, ?_⟩
  intro s hs v hv
  obtain ⟨y, hy, hyS, hρy⟩ := FLc.mem_autOn_iff.1 (hT s hs)
  apply Subtype.ext
  rw [← hρy, FLc.conjAct_coe hy]
  exact hF.ZUS y hyS (v : G) hv

theorem ctx_excl {T Mc Z₁ Z₂ L : Subgroup G} (hF : Facts15128 T Mc Z₁ Z₂ L)
    (hex : @FLc.ExclConcl ↥(uOf1527 Z₂ L) (commGroupOfElemAbelian hF.hU) (autOn L (uOf1527 Z₂ L))
      ((uLOf1527 Z₂ L).subgroupOf (uOf1527 Z₂ L)))
    (hoff : Q1Offender15128 T Mc Z₁ Z₂ L) : False := by
  let _ : CommGroup ↥(uOf1527 Z₂ L) := commGroupOfElemAbelian hF.hU
  obtain ⟨n, I, I', ρ₀, hn3, hrange', hrange, hne, hII', hI', hasym, hfix, hmod⟩ := hex
  have hne' : uLOf1527 Z₂ L ≠ ⊥ := fun h => hne (by rw [h, Subgroup.bot_subgroupOf])
  have hρ₀inj := rho_inj_of_ne_bot hF hn3 ρ₀ hrange hne'
  obtain ⟨h, hinj, hr1, hr2, hT, hfixS⟩ := normalize_rho hF hn3 ρ₀ hrange hrange' hne'
  obtain ⟨hU', A, hAQ, hAoff⟩ := hoff
  have hA : A ≠ ⊥ := hAoff.2.1
  have hlt := ctx_core_asym hF hn3 (ρ₀.comp (MulAut.conj h).toMonoidHom) hinj hr1 hr2 hT hII' hI' hasym
    (fun x hx v hv => hfix h v (hF.ZUle hv) (fun s hs => hfixS s hs v hv) x hx)
    (fun A'' hU hR hne => hmod hρ₀inj h A'' hU hR hne) hAQ hA
  have hge := @FLc.card_le_of_offender ↥(uOf1527 Z₂ L) (commGroupOfElemAbelian hF.hU) _ _ hAoff
  exact absurd hlt (not_lt.2 hge)

end CFSG.Quasithin

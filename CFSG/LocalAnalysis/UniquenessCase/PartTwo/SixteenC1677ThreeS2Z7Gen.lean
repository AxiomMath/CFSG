module

public import CFSG.HardMathSupport.Lang.Proving.FixedOrderCongruence
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSixOrder
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Sylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase11
public import CFSG.Quasithin.Background.OddCoprimeFixV
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {T : Type} [CommGroup T] [Finite T]

private theorem s168e3_z7_zpowers_eq {C : Subgroup (MulAut T)} (hC : IsCyclicOrd ↥C 7)
    {c : MulAut T} (hc : c ∈ C) (hc1 : c ≠ 1) : Subgroup.zpowers c = C := by
  have hc' : (⟨c, hc⟩ : ↥C) ≠ 1 := fun h => hc1 (Subtype.ext_iff.mp h)
  have hdvd : orderOf (⟨c, hc⟩ : ↥C) ∣ 7 := by
    rw [← hC.2]
    exact orderOf_dvd_natCard _
  have hord : orderOf (⟨c, hc⟩ : ↥C) = 7 := by
    rcases Nat.prime_seven.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd h (fun hh => hc' (orderOf_eq_one_iff.mp hh))
    · exact h
  have hordc : orderOf c = 7 := by
    rw [← Subgroup.orderOf_mk c hc]
    exact hord
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc)
  rw [Nat.card_zpowers, hordc, hC.2]

private theorem s168e3_z7_free (hT : ∀ v : T, v ^ 2 = 1) {C : Subgroup (MulAut T)}
    (hC : IsCyclicOrd ↥C 7) {u : T} (hu : u ∈ commSub ⊤ C) (hu1 : u ≠ 1)
    {c : MulAut T} (hc : c ∈ C) (hc1 : c ≠ 1) : c u ≠ u := by
  intro hcu
  have hodd : Odd (Nat.card ↥C) := by rw [hC.2]; norm_num
  have hfix : u ∈ fixV C := by
    rw [← s168e3_z7_zpowers_eq hC hc hc1, mem_fixV]
    intro x hx
    have hstab : Subgroup.zpowers c ≤ MulAction.stabilizer (MulAut T) u :=
      Subgroup.zpowers_le.mpr (by rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def])
    have := hstab hx
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
  have hcomm : u ∈ commV C := by rwa [commV_eq_commSub]
  have hbot := commV_inf_fixV_eq_bot_of_odd_card hT C hodd
  have : u ∈ commV C ⊓ fixV C := ⟨hcomm, hfix⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact hu1 this

private theorem s168e3_z7_order_three_fix {W : Type} [CommGroup W] [Finite W]
    (hW : Nat.card W = 8) {f : MulAut W} (hf : f ^ 3 = 1) :
    ∃ u : W, u ≠ 1 ∧ f u = u := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := CFSG.HardMathSupport.Lang.Proving.card_modEq_card_fixedPoints_of_pow_prime f hf
  rw [hW] at hmod
  have hmod2 : Nat.card {x : W // f x = x} ≡ 2 [MOD 3] :=
    hmod.symm.trans (by decide : (8 : ℕ) ≡ 2 [MOD 3])
  have hpos : 0 < Nat.card {x : W // f x = x} :=
    Finite.card_pos_iff.mpr ⟨⟨1, map_one f⟩⟩
  have hne : Nat.card {x : W // f x = x} ≠ 1 := by
    intro h
    rw [h] at hmod2
    exact absurd hmod2 (by decide)
  have hlt : 1 < Nat.card {x : W // f x = x} := by omega
  haveI : Nontrivial {x : W // f x = x} := Finite.one_lt_card_iff_nontrivial.mp hlt
  let oneSub : {x : W // f x = x} := ⟨1, map_one f⟩
  obtain ⟨u, hu⟩ := exists_ne oneSub
  exact ⟨u.1, fun h => hu (Subtype.ext h), u.2⟩

private theorem s168e3_z7_order_three_fix_stab {U : Subgroup T} (hUcard : Nat.card U = 8)
    {b : MulAut T} (hbU : b ∈ stabSub U) (hb3 : b ^ 3 = 1) :
    ∃ u ∈ U, u ≠ 1 ∧ b u = u := by
  let g : stabSub U := ⟨b, hbU⟩
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  have hf3 : (resHom U g) ^ 3 = 1 := by
    rw [← map_pow, hg3, map_one]
  obtain ⟨u, hu1, hfu⟩ := s168e3_z7_order_three_fix hUcard hf3
  refine ⟨u.1, u.2, fun h => hu1 (Subtype.ext h), ?_⟩
  have h := resHom_apply U g u
  rw [hfu] at h
  exact h.symm

private theorem s168e3_z7_centSub_card {E : Subgroup (MulAut T)} (hEcard : Nat.card E = 9)
    {V : Subgroup T} (hEV : E ≤ stabSub V) (hV168 : Nat.card (MulAut ↥V) = 168) :
    3 ≤ Nat.card ↥(E ⊓ centSub V) := by
  have hprod := card_autSub_mul hEV
  rw [hEcard] at hprod
  have hdvd : Nat.card (autSub E V) ∣ 3 := by
    have hd9 : Nat.card (autSub E V) ∣ 9 := ⟨Nat.card ↥(E ⊓ centSub V), hprod.symm⟩
    have hd168 : Nat.card (autSub E V) ∣ 168 := by
      have := Subgroup.card_subgroup_dvd_card (autSub E V)
      rwa [hV168] at this
    have := Nat.dvd_gcd hd9 hd168
    rw [show Nat.gcd 9 168 = 3 by norm_num] at this
    exact this
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h1 | h3
  · rw [h1, one_mul] at hprod
    omega
  · rw [h3] at hprod
    omega

private theorem s168e3_z7_exists_b {E : Subgroup (MulAut T)} (hEcard : Nat.card E = 9)
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) {U V : Subgroup T} (hUcard : Nat.card U = 8)
    (hEV : E ≤ stabSub V) (hEU : E ≤ stabSub U)
    (hV168 : Nat.card (MulAut ↥V) = 168) :
    ∃ b ∈ E ⊓ centSub V, orderOf b = 3 ∧ ∃ u ∈ U, u ≠ 1 ∧ b u = u := by
  have hk : 3 ≤ Nat.card ↥(E ⊓ centSub V) := s168e3_z7_centSub_card hEcard hEV hV168
  haveI : Nontrivial ↥(E ⊓ centSub V) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨b, hb1⟩ := exists_ne (1 : ↥(E ⊓ centSub V))
  have hbE : (b : MulAut T) ∈ E := b.2.1
  have hbV : (b : MulAut T) ∈ centSub V := b.2.2
  have hb3 : (b : MulAut T) ^ 3 = 1 := hE3 b hbE
  have hbne : (b : MulAut T) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hord : orderOf (b : MulAut T) = 3 := by
    have hdvd : orderOf (b : MulAut T) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hb3
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd h (fun hh => hbne (orderOf_eq_one_iff.mp hh))
    · exact h
  obtain ⟨u, huU, hu1, hbu⟩ := s168e3_z7_order_three_fix_stab hUcard (hEU hbE) hb3
  exact ⟨b, ⟨hbE, hbV⟩, hord, u, huU, hu1, hbu⟩

private theorem s168e3_z7_orbit (hT : ∀ v : T, v ^ 2 = 1) {C : Subgroup (MulAut T)}
    (hC : IsCyclicOrd ↥C 7) (hW : Nat.card ↥(commSub ⊤ C) = 8)
    {u : T} (hu : u ∈ commSub ⊤ C) (hu1 : u ≠ 1) :
    ∀ y ∈ commSub ⊤ C, y ≠ 1 → ∃ c ∈ C, c u = y := by
  haveI : IsCyclic ↥C := hC.1
  have hCW : C ≤ stabSub (commSub ⊤ C) := by
    intro c hc
    apply s16n9b_mem_stabSub_of_map_eq
    rw [← s15_Infra_commSub_top_map_conj C c]
    congr 1
    ext y
    simp only [Subgroup.mem_map]
    have hconj : ∀ z ∈ C, (MulAut.conj c).toMonoidHom z = z := by
      intro z hz
      change MulAut.conj c z = z
      rw [MulAut.conj_apply]
      have hcomm : z * c = c * z := setLike_mul_comm hz hc
      rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hconj z hz]
      exact hz
    · intro hy
      exact ⟨y, hy, hconj y hy⟩
  let φ : ↥C → ↥(commSub ⊤ C) :=
    fun c => ⟨(c : MulAut T) u, (mem_stabSub.1 (hCW c.2) u).2 hu⟩
  have hφ_ne : ∀ c : ↥C, φ c ≠ 1 := by
    intro c h
    apply hu1
    have h1 : (c : MulAut T) u = 1 := congrArg Subtype.val h
    have h2 : (c : MulAut T)⁻¹ ((c : MulAut T) u) = (c : MulAut T)⁻¹ 1 := congrArg _ h1
    rw [MulAut.inv_apply_self, map_one] at h2
    exact h2
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    have h1 : (a : MulAut T) u = (b : MulAut T) u := congrArg Subtype.val hab
    by_contra hab1
    have hne : ((b⁻¹ * a : ↥C) : MulAut T) ≠ 1 := by
      intro h
      apply hab1
      have h2 : (b⁻¹ * a : ↥C) = 1 := Subtype.ext h
      have h3 := congrArg (fun d : ↥C => b * d) h2
      simpa using h3
    have h2 : ((b⁻¹ * a : ↥C) : MulAut T) u = u := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, h1, MulAut.inv_apply_self]
    exact s168e3_z7_free hT hC hu hu1 (b⁻¹ * a : ↥C).2 hne h2
  have hrange : (Set.range φ).ncard = 7 := by
    rw [← Set.image_univ, Set.InjOn.ncard_image hφ_inj.injOn, Set.ncard_univ, hC.2]
  have hS : ({w : ↥(commSub ⊤ C) | w ≠ 1} : Set ↥(commSub ⊤ C)).ncard = 7 := by
    have h := Set.ncard_sdiff_singleton_of_mem (s := (Set.univ : Set ↥(commSub ⊤ C)))
      (a := (1 : ↥(commSub ⊤ C))) (Set.mem_univ 1)
    rw [show (Set.univ \ {(1 : ↥(commSub ⊤ C))} : Set ↥(commSub ⊤ C)) = {w | w ≠ 1} by
      ext w; simp] at h
    rw [h, Set.ncard_univ, hW]
  have hsub : Set.range φ ⊆ {w : ↥(commSub ⊤ C) | w ≠ 1} := by
    rintro _ ⟨c, rfl⟩
    exact hφ_ne c
  have heq : ({w : ↥(commSub ⊤ C) | w ≠ 1} : Set ↥(commSub ⊤ C)).ncard = (Set.range φ).ncard :=
    by rw [hS, hrange]
  have hrange_eq : Set.range φ = {w : ↥(commSub ⊤ C) | w ≠ 1} :=
    Set.eq_of_subset_of_ncard_le hsub heq.le
  intro y hy hy1
  have : (⟨y, hy⟩ : ↥(commSub ⊤ C)) ∈ Set.range φ := by
    rw [hrange_eq]
    exact fun h => hy1 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := this
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

theorem s168e3_z7_card_dvd (hT : ∀ v : T, v ^ 2 = 1) {M A : Subgroup (MulAut T)} {g : MulAut T}
    (h : S16n9bTwo M A g) (hrk : rk ↥(commSub ⊤ A) = 3) :
    Nat.card ↥M ∣ 2 * 168 ^ 2 := by
  have hWcard : Nat.card ↥(commSub ⊤ A) = 8 := by
    rw [card_eq_two_pow hT (commSub ⊤ A), hrk]
    norm_num
  have hW'card : Nat.card ↥((commSub ⊤ A).map g.toMonoidHom) = 8 := by
    rw [card_eq_two_pow hT ((commSub ⊤ A).map g.toMonoidHom),
      s16n9b_rk_map g (commSub ⊤ A), hrk]
    norm_num
  refine s15_Six_card_dvd_of_two_summands (fun a => ?_) hWcard hW'card h.inf h.sup ?_
  · rw [← pow_two]
    exact hT a
  · intro φ hφ
    have hgB := s15_Infra_commSub_top_map_conj A g
    rcases h.conj φ hφ with hAφ | hAφ
    · refine ⟨Or.inl ?_, Or.inr ?_⟩
      · rw [← s15_Infra_commSub_top_map_conj A φ, hAφ]
      · rw [← hgB, ← s15_Infra_commSub_top_map_conj _ φ,
          s16n9b_two_normalizes_conj h hφ hAφ]
    · refine ⟨Or.inr ?_, ?_⟩
      · rw [← s15_Infra_commSub_top_map_conj A φ, hAφ, hgB]
      · rcases h.conj (φ * g) (M.mul_mem hφ h.mem) with h1 | h1
        · exact Or.inl (by
            rw [← hgB, ← s15_Infra_commSub_top_map_conj _ φ,
              s16n9b_map_conj_map_conj A g φ, h1])
        · exact Or.inr (by
            rw [← hgB, ← s15_Infra_commSub_top_map_conj _ φ,
              s16n9b_map_conj_map_conj A g φ, h1, hgB])

theorem s168e3_z7_fix (hT : ∀ v : T, v ^ 2 = 1) {M A : Subgroup (MulAut T)} {g : MulAut T}
    (h : S16n9bTwo M A g) (hrk : rk ↥(commSub ⊤ A) = 3) (hA : IsCyclicOrd ↥A 7)
    (h3 : 2 ≤ CFSG.Open.pRank 3 M) :
    ∀ x : T, x ≠ 1 → ∃ b ∈ M, orderOf b = 3 ∧ b x = x := by
  have h3' : 2 ≤ CFSG.pRank 3 ↥M := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank 3 M]
    exact h3
  obtain ⟨E, hEM, hEea, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := 3) Nat.prime_three (M := M) (k := 2) h3'
  have hEcard9 : Nat.card E = 9 := by rw [hEcard]; norm_num
  have hE3 : ∀ e ∈ E, e ^ 3 = 1 := hEea.2
  have hAe : ∀ e ∈ E, A.map (MulAut.conj e).toMonoidHom = A := fun e he =>
    s16n9b_two_normalizes_of_odd h (hEM he) (n := 3) (by decide) (hE3 e he)
  have hstW : E ≤ stabSub (commSub ⊤ A) := by
    intro e he
    apply s16n9b_mem_stabSub_of_map_eq
    rw [← s15_Infra_commSub_top_map_conj A e, hAe e he]
  have hgB : commSub ⊤ (A.map (MulAut.conj g).toMonoidHom) = (commSub ⊤ A).map g.toMonoidHom :=
    s15_Infra_commSub_top_map_conj A g
  have hstW' : E ≤ stabSub ((commSub ⊤ A).map g.toMonoidHom) := by
    intro e he
    apply s16n9b_mem_stabSub_of_map_eq
    rw [← hgB, ← s15_Infra_commSub_top_map_conj _ e,
      s16n9b_two_normalizes_conj h (hEM he) (hAe e he)]
  have hWcard : Nat.card ↥(commSub ⊤ A) = 8 := by
    rw [card_eq_two_pow hT (commSub ⊤ A), hrk]
    norm_num
  have hW'card : Nat.card ↥((commSub ⊤ A).map g.toMonoidHom) = 8 := by
    rw [card_eq_two_pow hT ((commSub ⊤ A).map g.toMonoidHom),
      s16n9b_rk_map g (commSub ⊤ A), hrk]
    norm_num
  have h168 : Nat.card (MulAut ↥(commSub ⊤ A)) = 168 := s16n9b_card_mulAut_rank_three hT hrk
  have h168' : Nat.card (MulAut ↥((commSub ⊤ A).map g.toMonoidHom)) = 168 :=
    s16n9b_card_mulAut_rank_three hT (by rw [s16n9b_rk_map g (commSub ⊤ A)]; exact hrk)
  obtain ⟨b₁, hb₁, hb₁ord, u₁, hu₁W, hu₁1, hb₁u₁⟩ :=
    s168e3_z7_exists_b hEcard9 hE3 hWcard hstW' hstW h168'
  obtain ⟨b₂, hb₂, hb₂ord, u₂, hu₂W', hu₂1, hb₂u₂⟩ :=
    s168e3_z7_exists_b hEcard9 hE3 hW'card hstW hstW' h168
  have hAgM : A.map (MulAut.conj g).toMonoidHom ≤ M := by
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 ha
    show MulAut.conj g a₀ ∈ M
    rw [MulAut.conj_apply]
    exact M.mul_mem (M.mul_mem h.mem (h.le ha₀)) (M.inv_mem h.mem)
  intro x hx
  have hxmem : x ∈ commSub ⊤ A ⊔ (commSub ⊤ A).map g.toMonoidHom := by
    rw [h.sup]
    exact Subgroup.mem_top x
  obtain ⟨y, hyW, z, hzW', hxyz⟩ := Subgroup.mem_sup.1 hxmem
  rcases eq_or_ne y 1 with hy1 | hy1
  · have hz1 : z ≠ 1 := by
      rintro rfl
      exact hx (by rw [← hxyz, hy1, mul_one])
    have hCcyc : IsCyclicOrd ↥(A.map (MulAut.conj g).toMonoidHom) 7 :=
      ⟨(MulEquiv.isCyclic (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective)).mp hA.1, by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA.2]⟩
    have hCW' : Nat.card ↥(commSub ⊤ (A.map (MulAut.conj g).toMonoidHom)) = 8 := by
      rw [hgB]
      exact hW'card
    obtain ⟨l, hlC, hlu₂⟩ :=
      s168e3_z7_orbit hT hCcyc hCW' (by rw [hgB]; exact hu₂W') hu₂1 z
        (by rw [hgB]; exact hzW') hz1
    have hlM : l ∈ M := hAgM hlC
    have hl_inv_z : l⁻¹ z = u₂ := by rw [← hlu₂, MulAut.inv_apply_self]
    have hbz : (l * b₂ * l⁻¹) z = z := by
      change (l * b₂ * l⁻¹) z = z
      rw [MulAut.mul_apply, MulAut.mul_apply, hl_inv_z, hb₂u₂, hlu₂]
    have hby : (l * b₂ * l⁻¹) y = y := by rw [hy1]; exact map_one _
    have hb_eq : l * b₂ * l⁻¹ = (MulAut.conj l).toMonoidHom b₂ :=
      (MulAut.conj_apply l b₂).symm
    refine ⟨l * b₂ * l⁻¹, ?_, ?_, ?_⟩
    · exact M.mul_mem (M.mul_mem hlM (hEM hb₂.1)) (M.inv_mem hlM)
    · rw [hb_eq, orderOf_injective (MulAut.conj l).toMonoidHom (MulAut.conj l).injective b₂,
        hb₂ord]
    · rw [← hxyz, map_mul, hby, hbz, hxyz]
  · obtain ⟨l, hlA, hlu₁⟩ := s168e3_z7_orbit hT hA hWcard hu₁W hu₁1 y hyW hy1
    have hlM : l ∈ M := h.le hlA
    have hlz : l z = z := h.fixA l hlA z hzW'
    have hlinvz : l⁻¹ z = z := h.fixA l⁻¹ (A.inv_mem hlA) z hzW'
    have hb₁z : b₁ z = z := hb₁.2 z hzW'
    have hl_inv_y : l⁻¹ y = u₁ := by rw [← hlu₁, MulAut.inv_apply_self]
    have hby : (l * b₁ * l⁻¹) y = y := by
      change (l * b₁ * l⁻¹) y = y
      rw [MulAut.mul_apply, MulAut.mul_apply, hl_inv_y, hb₁u₁, hlu₁]
    have hbz : (l * b₁ * l⁻¹) z = z := by
      change (l * b₁ * l⁻¹) z = z
      rw [MulAut.mul_apply, MulAut.mul_apply, hlinvz, hb₁z, hlz]
    have hb_eq : l * b₁ * l⁻¹ = (MulAut.conj l).toMonoidHom b₁ :=
      (MulAut.conj_apply l b₁).symm
    refine ⟨l * b₁ * l⁻¹, ?_, ?_, ?_⟩
    · exact M.mul_mem (M.mul_mem hlM (hEM hb₁.1)) (M.inv_mem hlM)
    · rw [hb_eq, orderOf_injective (MulAut.conj l).toMonoidHom (MulAut.conj l).injective b₁,
        hb₁ord]
    · rw [← hxyz, map_mul, hby, hbz, hxyz]

end Generic

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

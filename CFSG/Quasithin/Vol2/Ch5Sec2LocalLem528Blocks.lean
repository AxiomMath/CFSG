module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528
public import CFSG.Quasithin.Vol2.Ch1EightFourMain
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528BEmb
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528BTr
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528BRows
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528BGL

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.Ch1Four
open CFSG.Quasithin.Vol2.Ch11.SecA CFSG.LieType.BorelTits
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_blockU_of_isLin2Type {K : Subgroup G} {n : ℕ} (h : IsLin2Type K n) :
    Nat.card (blockU K) = 2 ^ (2 * n) * Nat.card (blockZ K) := by
  obtain ⟨F, _, _, hF, -, -, -, β, hβs, hβk, -⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv, hβk] at h1
  have hZU : blockZ K ≤ blockU K := inf_le_left
  have h2 : Nat.card ((blockZ K).subgroupOf (blockU K)) = Nat.card (blockZ K) := by
    rw [← Subgroup.card_map_of_injective (blockU K).subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZU]
  have h3 : Nat.card (Multiplicative (Fin 2 → F)) = 2 ^ (2 * n) := by
    rw [show Nat.card (Multiplicative (Fin 2 → F)) = Nat.card (Fin 2 → F) from rfl, Nat.card_fun,
      Nat.card_fin, Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm]
  rw [h1, h3, h2]

omit [Finite G] in
theorem le_normalizer_blockZ' (K : Subgroup G) :
    K ≤ Subgroup.normalizer (blockZ K : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp
    (le_normalizer_commutator_of (le_normalizer_pCoreOf 2 K) Subgroup.le_normalizer hk) x
  have h2 : x ∈ Subgroup.centralizer (K : Set G) ↔
      k * x * k⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro hc y hy
      have h3 := hc (k⁻¹ * y * k) (mul_mem (mul_mem (inv_mem hk) hy) hk)
      calc y * (k * x * k⁻¹) = k * ((k⁻¹ * y * k) * x) * k⁻¹ := by group
        _ = k * (x * (k⁻¹ * y * k)) * k⁻¹ := by rw [h3]
        _ = k * x * k⁻¹ * y := by group
    · intro hc y hy
      have h3 := hc (k * y * k⁻¹) (mul_mem (mul_mem hk hy) (inv_mem hk))
      calc y * x = k⁻¹ * ((k * y * k⁻¹) * (k * x * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * x * k⁻¹) * (k * y * k⁻¹)) * k := by rw [h3]
        _ = x * y := by group
  simp only [blockZ, Subgroup.mem_inf]
  exact ⟨fun h => ⟨h1.mp h.1, h2.mp h.2⟩, fun h => ⟨h1.mpr h.1, h2.mpr h.2⟩⟩

omit [Finite G] in
theorem pCore_eq_subgroupOf {B Q : Subgroup G} (hQ : pCoreOf 2 B = Q) :
    CFSG.pCore 2 ↥B = Q.subgroupOf B := by
  rw [← hQ]
  exact (Subgroup.comap_map_eq_self_of_injective B.subtype_injective _).symm

noncomputable def toModO2Image {H B : Subgroup G} (hBH : B ≤ H) : ↥B →* ↥(modO2Image H B) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap (B.subgroupOf H)).comp
    (Subgroup.subgroupOfEquivOfLe hBH).symm.toMonoidHom

omit [Finite G] in
theorem toModO2Image_surjective {H B : Subgroup G} (hBH : B ≤ H) :
    Function.Surjective (toModO2Image hBH) :=
  (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hBH).symm.surjective

omit [Finite G] in
theorem mem_ker_toModO2Image {H B : Subgroup G} (hBH : B ≤ H) (b : ↥B) :
    b ∈ (toModO2Image hBH).ker ↔ (b : G) ∈ pCoreOf 2 H := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h1
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨b, hBH b.2⟩ : ↥H) = 1 :=
      congrArg Subtype.val h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact ⟨_, h2, rfl⟩
  · rintro ⟨y, hy, hyb⟩
    apply Subtype.ext
    change QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨b, hBH b.2⟩ : ↥H) = 1
    have hy' : (⟨b, hBH b.2⟩ : ↥H) = y := Subtype.ext hyb.symm
    rw [hy', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hy

omit [Finite G] in
theorem ker_toModO2Image {H B Q : Subgroup G} (hBH : B ≤ H) (hQ : B ⊓ pCoreOf 2 H = Q) :
    (toModO2Image hBH).ker = Q.subgroupOf B := by
  ext b
  rw [mem_ker_toModO2Image, Subgroup.mem_subgroupOf, ← hQ, Subgroup.mem_inf]
  exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩

omit [Finite G] in
theorem card_modO2Image_mul {H B : Subgroup G} (hBH : B ≤ H) :
    Nat.card ↥(modO2Image H B) * Nat.card ↥(B ⊓ pCoreOf 2 H) = Nat.card ↥B := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (toModO2Image hBH).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (toModO2Image_surjective hBH)).toEquiv, ker_toModO2Image hBH rfl] at h1
  have h2 : Nat.card ↥(((B ⊓ pCoreOf 2 H).subgroupOf B).map B.subtype) =
      Nat.card ↥((B ⊓ pCoreOf 2 H).subgroupOf B) :=
    Subgroup.card_map_of_injective B.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left] at h2
  rw [h1, h2]

theorem card_pCore_modO2Image_eq_one {H B : Subgroup G} (hBH : B ≤ H)
    (h : B ⊓ pCoreOf 2 H = pCoreOf 2 B) :
    Nat.card (CFSG.pCore 2 ↥(modO2Image H B)) = 1 := by
  obtain ⟨e⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hBH
  have h1 := card_modO2Image_mul hBH
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B)
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.pCore 2 ↥(modO2Image H B))
  have hQ : Nat.card ↥(B ⊓ pCoreOf 2 H) = Nat.card (CFSG.pCore 2 ↥B) := by
    rw [h]
    exact Subgroup.card_map_of_injective B.subtype_injective
  have h4 : Nat.card (ModO2 B) = Nat.card (ModO2 (modO2Image H B)) := Nat.card_congr e.toEquiv
  change Nat.card ↥B = Nat.card (ModO2 B) * _ at h2
  change Nat.card ↥(modO2Image H B) = Nat.card (ModO2 (modO2Image H B)) * _ at h3
  have hpos : 0 < Nat.card (CFSG.pCore 2 ↥B) := Nat.card_pos
  have hposq : 0 < Nat.card (ModO2 B) := Nat.card_pos
  rw [h3, hQ, ← h4] at h1
  rw [h2] at h1
  have : Nat.card (ModO2 B) * Nat.card (CFSG.pCore 2 ↥(modO2Image H B)) =
      Nat.card (ModO2 B) := by
    have := Nat.eq_of_mul_eq_mul_right hpos (h1.trans (by ring))
    exact this
  exact Nat.eq_of_mul_eq_mul_left hposq (this.trans (mul_one _).symm)

omit [Finite G] in
theorem eq_top_of_isPGroup_quotient [Finite G] {L : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (N : Subgroup ↥L) [N.Normal] (hN : IsPGroup 2 (↥L ⧸ N)) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hnt : Nontrivial (↥L ⧸ N) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    apply hne
    rw [eq_top_iff]
    intro x _
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  have hLp : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  have hQp : Group.IsPerfect (↥L ⧸ N) := inferInstance
  have := Fintype.ofFinite (↥L ⧸ N)
  have : Group.IsNilpotent (↥L ⧸ N) := hN.isNilpotent
  exact Group.IsPerfect.not_isNilpotent (↥L ⧸ N) inferInstance

end Helpers

theorem stmt5_2_8_blocks_of
    (h37 : A37ForSQTK) (h526 : Stmt5_2_6)
    (h312 : A312ForSQTK) (hExc : FactExcParabolicO2Ne) (hHat : HatA7Faithful6)
    (hA7 : A7Q528Fact) : Stmt5_2_8_blocks := by
  intro G _ _ T M L V H B D L₂ n hyp hc Kh hlt hKh
  obtain ⟨hα, -, -, hKb, hKlin⟩ := hc
  have h := hyp.toHyp5_0_1
  have hn : 2 ≤ n := h.two_le
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hL₂K, hcore, -, -, -, -, -⟩ := h526 G T M L V H B D L₂ n hyp
  obtain ⟨-, -, -, hKT, hα'⟩ := alt_a_of_amalgam h526 hyp hα
  have hTr := pCoreOf_perfectCore_of_amalgam (G₁ := sec52G1 M L H B L₂)
    (G₂ := sec52G2 M H D L₂) hn
  rw [← hcore] at hTr
  set K := oTwoUpper H with hKdef
  set Q := pCoreOf 2 K with hQdef
  have hKloc : quasithinIsLocal T K := hyp.isLocal_oTwoUpper hL₂K
  have hTN : T ≤ Subgroup.normalizer (K : Set G) :=
    hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  have e : Emb528 T K Kh := ⟨h.qtke, h.simple, h.nonabelian, h.sylow, hKloc, hKh.1, hlt.le, hTN⟩
  have hshort : IsShort2 K := hKb.1
  have hQK : Q ≤ K := pCoreOf_le 2 K
  have hUle : blockU K ≤ blockQ K :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_pCoreOf 2 K)
  have hQcard : Nat.card Q = 2 ^ (2 * n) ∨ Nat.card Q = 2 ^ (3 * n) := by
    rcases hα with hα | hα
    · exact Or.inl (hTr.1 hα)
    · exact Or.inr (hTr.2 hα).1
  have hUQ : blockU K = Q := by
    rcases hα with hα | hα
    · refine Subgroup.eq_of_le_of_card_ge hUle ?_
      rw [hTr.1 hα, card_blockU_of_isLin2Type hKlin]
      exact Nat.le_mul_of_pos_right _ Nat.card_pos
    · exact (hTr.2 hα).2
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro a ha b hb
    have hb' := (Subgroup.mem_inf.mp (hshort.2.2.1.1 (hUQ ▸ hb))).2
    exact Subgroup.mem_centralizer_iff.mp hb' a ((Subgroup.mem_inf.mp
      (hshort.2.2.1.1 (hUQ ▸ ha))).1)
  have hQ2 : ∀ a ∈ Q, a ^ 2 = 1 := fun a ha => hshort.2.2.1.2 a (hUQ ▸ ha)
  have hQKh : pCoreOf 2 Kh = Q := by
    refine le_antisymm ((e.pCoreOf_le_pCoreOf_KT h37).trans hKT.le) ?_
    have := e.blockU_le h37 hshort
    rwa [hUQ] at this
  have hCh : CharTwo Kh := CharTwo.of_normal e.charTwo le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (e.sup_le_normalizer h37))
  have hfaith : Kh ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := by
    have := hCh
    unfold CharTwo at this
    rwa [hQKh] at this
  have hQKh' : Q ≤ Kh := hQK.trans hlt.le
  have hKhN : Kh ≤ Subgroup.normalizer (Q : Set G) := hQKh ▸ le_normalizer_pCoreOf 2 Kh
  set H' := Kh ⊔ T with hH'
  have hKH' : K ≤ H' := hlt.le.trans le_sup_left
  have hKhH' : Kh ≤ H' := le_sup_left
  have hKinf : K ⊓ pCoreOf 2 H' = pCoreOf 2 K := by
    have h1 : K ⊓ pCoreOf 2 H' = K ⊓ (Kh ⊓ pCoreOf 2 H') := by
      rw [← inf_assoc, inf_eq_left.mpr hlt.le]
    rw [h1, e.inf_pCoreOf_eq h37, hQKh, inf_eq_right.mpr hQK]
  have hKhinf : Kh ⊓ pCoreOf 2 H' = Q := by rw [e.inf_pCoreOf_eq h37, hQKh]
  have hO2B : Nat.card (CFSG.pCore 2 ↥(modO2Image H' K)) = 1 :=
    card_pCore_modO2Image_eq_one hKH' hKinf
  obtain ⟨F, _, _, hF, αK, hαs, hαk, -⟩ := hKlin
  have hFc : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have eK : ModO2 K ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective αK hαs)
  obtain ⟨eKB⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hKH'
  have eB : ModO2 (modO2Image H' K) ≃* Matrix.SpecialLinearGroup (Fin 2) F := eKB.symm.trans eK
  have hD : BarData (modO2Image H' K) n := barData_of_quot_SL2 hn hFc eB
  have hK4 := NQCat.exists_finset_card_four_of_card hn hFc
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hFc
  have := Vol2Native.A312L.sl2_isSimple hK4
  have hbotB : CFSG.pCore 2 ↥(modO2Image H' K) = ⊥ := Subgroup.eq_bot_of_card_eq _ hO2B
  have eB' : ↥(modO2Image H' K) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    QuotientGroup.quotientBot.symm.trans ((QuotientGroup.quotientMulEquivOfEq hbotB.symm).trans eB)
  have hsB : IsSimpleGroup ↥(modO2Image H' K) := eB'.isSimpleGroup
  have hnabB : ∃ a b : ↥(modO2Image H' K), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := Vol2Native.A312L.sl2_nonabelian hK4
    exact ⟨eB'.symm a, eB'.symm b, fun h => hab (by
      have := congrArg eB' h
      simpa using this)⟩
  have hcardB : Nat.card ↥(modO2Image H' K) = 2 ^ n * oSL2 n := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(modO2Image H' K)),
      hO2B, mul_one]
    exact hD.cardQ
  have hS : IsSylowTwoOf T H' := ⟨le_sup_right, hKh.1.1, hKh.1.2.2.1⟩
  have hB : K ∈ lFamily T := mem_lFamily_of_isLocal hKloc
  have hBL : modO2Image H' K ≤ modO2Image H' Kh := Subgroup.map_mono fun x hx => hlt.le hx
  set ρ := toModO2Image hKhH' with hρ
  have hρs : Function.Surjective ρ := toModO2Image_surjective hKhH'
  have hρk : ρ.ker = Q.subgroupOf Kh := ker_toModO2Image hKhH' hKhinf
  have hNn : (Q.subgroupOf Kh).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQKh').mpr hKhN
  let _ : CommGroup ↥(Q.subgroupOf Kh) :=
    { (inferInstance : Group ↥(Q.subgroupOf Kh)) with
      mul_comm := fun a b => Subtype.ext (Subtype.ext (hQab _ a.2 _ b.2)) }
  set φ : ↥Kh →* MulAut ↥(Q.subgroupOf Kh) := MulAut.conjNormal with hφ
  have hφk : φ.ker = Q.subgroupOf Kh := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hxC : (x : G) ∈ Kh ⊓ Subgroup.centralizer (Q : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
        have h1 := congrArg (fun f : MulAut ↥(Q.subgroupOf Kh) =>
          ((f ⟨⟨q, hQKh' hq⟩, hq⟩ : ↥(Q.subgroupOf Kh)) : G)) hx
        simp only [hφ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
        have h1' : (x : G) * q * (x : G)⁻¹ = q := by simpa using h1
        calc q * (x : G) = (x : G) * q * (x : G)⁻¹ * (x : G) := by rw [h1']
          _ = (x : G) * q := by group
      exact hfaith hxC
    · intro hx
      ext q
      simp only [hφ, MulAut.conjNormal_apply, MulAut.one_apply]
      have hc : (x : G) * ((q : ↥Kh) : G) = ((q : ↥Kh) : G) * (x : G) := hQab _ hx _ q.2
      change (x : G) * ((q : ↥Kh) : G) * (x : G)⁻¹ = ((q : ↥Kh) : G)
      rw [hc, mul_inv_cancel_right]
  have eLφ : ↥(modO2Image H' Kh) ≃* φ.range :=
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hρk.trans hφk.symm)).trans
        (QuotientGroup.quotientKerEquivRange φ))
  have hNcard : Nat.card ↥(Q.subgroupOf Kh) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQKh').toEquiv
  have hN2 : ∀ v : ↥(Q.subgroupOf Kh), v ^ 2 = 1 := fun v =>
    Subtype.ext (Subtype.ext (by simpa using hQ2 _ v.2))
  have hLdvd : ∀ d, Nat.card Q = 2 ^ d →
      Nat.card ↥(modO2Image H' Kh) ∣ Nat.card (GL (Fin d) (ZMod 2)) := by
    intro d hd
    rw [Nat.card_congr eLφ.toEquiv, ← card_mulAut_of_sq_eq_one hN2 (hNcard.trans hd)]
    exact Subgroup.card_subgroup_dvd_card φ.range
  rcases lemma_1_2_4_list h.qtke h.simple h.nonabelian h312 hKh.1.2.2.2 hS hKH' hB
      (cComp_of_isLocal hKh.1) hlt.le with heq | hcase | hnq
  · exact absurd (eq_of_modO2Image_eq hKloc hKh.1 hlt.le heq) hlt.ne
  swap
  · exact (false_of_a312Nonquasi_of_simple hsB hn hcardB hBL hnq).elim
  rcases rows_simple hD hsB hnabB hO2B hcase with hC2 | ⟨rfl, hL7⟩
  · exact (false_of_a312C2_of_simple hExc hD hO2B hC2).elim
  have hdvd6 : Nat.card ↥(modO2Image H' Kh) ∣ 20158709760 := by
    rcases hQcard with hQ | hQ
    · exact (hLdvd 4 hQ).trans (by rw [card_GL4_two]; decide)
    · exact (hLdvd 6 hQ).trans (by rw [card_GL6_two])
  rcases hL7 with hA | hHt | hX
  rotate_left
  ·
    exfalso
    rcases hQcard with hQ | hQ
    · exact false_of_hat7_dvd_gl4 ((hLdvd 4 hQ).trans (by rw [card_GL4_two])) hHt
    · exact hHat φ.range (IsHat.of_mulEquiv eLφ hHt) ↥(Q.subgroupOf Kh) hN2
        (by rw [hNcard, hQ]) φ.range.subtype φ.range.subtype_injective
  · exact (false_of_dvd_gl6 hdvd6 hX).elim
  obtain ⟨eA⟩ := hA
  set αKh : ↥Kh →* alternatingGroup (Fin 7) := eA.toMonoidHom.comp ρ with hαKh
  have hαKhs : Function.Surjective αKh := eA.surjective.comp hρs
  have hαKhk : αKh.ker = Q.subgroupOf Kh := by
    have h1 : αKh.ker = ρ.ker := by
      ext x
      simp only [hαKh, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact map_eq_one_iff _ eA.injective
    rw [h1, hρk]
  have hQ6 : Nat.card Q ≤ 2 ^ 6 := by
    rcases hQcard with hQ | hQ
    · rw [hQ]
      norm_num
    · rw [hQ]
  have hrel : ¬ 7 ∣ Q.relIndex K := by
    have h1 := Subgroup.relIndex_mul_card (H := Q) (K := K)
    rw [inf_eq_left.mpr hQK] at h1
    have h2 : Nat.card ↥K = Nat.card (ModO2 K) * Nat.card Q := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)]
      congr 1
      exact (Subgroup.card_map_of_injective K.subtype_injective).symm
    have h3 : Nat.card (ModO2 K) = 60 := by
      rw [Nat.card_congr eK.toEquiv, card_SL_two hFc]
      decide
    have hpos : 0 < Nat.card Q := Nat.card_pos
    rw [h2, h3] at h1
    have h4 : Q.relIndex K = 60 := Nat.eq_of_mul_eq_mul_right hpos h1
    rw [h4]
    decide
  obtain ⟨hQ4, hirr⟩ := hA7 G Kh Q K hQKh' hKhN hQab hQ2 hfaith hQ6
    ⟨αKh, hαKhs, hαKhk⟩ hQK hlt.le hUQ hrel
  have hαL : IsAmalgamOfGroup (sec52Alpha M L H B D L₂) (IsLieOverTwo .PSL 3 2) := by
    rcases hα with hα | hα
    · exact hα
    · have := (hTr.2 hα).1
      rw [hQ4] at this
      norm_num at this
  refine ⟨hα' ▸ hαL, ?_⟩
  have hUKh : blockU Kh = Q := by
    refine le_antisymm ?_ ?_
    · show ⁅blockQ Kh, Kh⁆ ≤ Q
      rw [show blockQ Kh = Q from hQKh]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hQKh ▸ le_normalizer_pCoreOf 2 Kh)
    · rw [← hUQ]
      exact Subgroup.commutator_mono (le_of_eq (hQKh.trans rfl).symm) hlt.le
  have hZKh : blockZ Kh = ⊥ := by
    have hZQ : blockZ Kh ≤ Q := hUKh ▸ inf_le_left
    rcases hirr (blockZ Kh) hZQ (le_normalizer_blockZ' Kh) with h0 | h0
    · exact h0
    · exfalso
      have hQC : Q ≤ Subgroup.centralizer (Kh : Set G) := h0 ▸ inf_le_right
      have hbot : ⁅Q, K⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro q hq k hk
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_iff.mp (hQC hq) k (hlt.le hk)).symm
      have : Nat.card Q = 1 := by
        rw [← hUQ]
        change Nat.card ↥(⁅blockQ K, K⁆) = 1
        rw [show blockQ K = Q from rfl, hbot, Subgroup.card_bot]
      rw [hQ4] at this
      norm_num at this
  have hpKh : CFSG.pCore 2 ↥Kh = Q.subgroupOf Kh := pCore_eq_subgroupOf hQKh
  refine ⟨⟨fun N _ hN => eq_top_of_isPGroup_quotient hKh.1.2.1.2.1 N hN, hCh, ?_, ?_, ?_⟩,
    ⟨αKh, hαKhs, hαKhk.trans hpKh.symm⟩, ?_⟩
  · rw [hUKh, show blockQ Kh = Q from hQKh]
    refine ⟨le_inf le_rfl fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
      hQab b hb a ha, hQ2⟩
  · left
    have eKA : ↥Kh ⧸ CFSG.pCore 2 ↥Kh ≃* alternatingGroup (Fin 7) :=
      (QuotientGroup.quotientMulEquivOfEq (hpKh.trans hαKhk.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective αKh hαKhs)
    have hA7s : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by norm_num)
    have := eKA.isSimpleGroup
    refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
    obtain ⟨a, b, hab⟩ : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a :=
      ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
        ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
        fun h => by have := congrArg Subtype.val h; revert this; decide⟩
    exact ⟨eKA.symm a, eKA.symm b, fun h => hab (by simpa using congrArg eKA h)⟩
  · rw [hZKh, hUKh]
    refine ⟨bot_lt_iff_ne_bot.mpr fun h0 => ?_, fun W hW1 hW2 hW3 => ?_⟩
    · rw [h0, Subgroup.card_bot] at hQ4
      norm_num at hQ4
    · rcases hirr W hW2 hW3 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr h0
  · rw [hZKh, hUKh, Subgroup.bot_subgroupOf, Subgroup.index_bot, hQ4]

end CFSG.Quasithin.H13

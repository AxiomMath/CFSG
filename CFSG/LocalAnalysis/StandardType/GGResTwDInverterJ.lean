module

public import CFSG.LocalAnalysis.StandardType.GGResTwDInverter
public import CFSG.LocalAnalysis.StandardType.GGCartanALinear
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitary
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitaryDatum
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimUnitary
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepNine
public import CFSG.LocalAnalysis.StandardType.GGCartanATypeArith
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkTransport
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdPair
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section CartanA

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {r : ℕ}

theorem cartanA_span_irred (hp2 : p ≠ 2) (hpr : ¬ p ∣ r + 1) {h : Fin r → V}
    {α : Fin r → Module.Dual (ZMod p) V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A r i j : ZMod p))
    (W : Submodule (ZMod p) V) (hW : W ≤ Submodule.span (ZMod p) (Set.range h))
    (hinv : ∀ i, ∀ w ∈ W, w - α i w • h i ∈ W) :
    W = ⊥ ∨ W = Submodule.span (ZMod p) (Set.range h) := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hex : ∃ i, α i w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw0 (cartanA_eq_zero_of_mem_span hpr hpair (hW hwW) hcon)
  obtain ⟨i₀, hi₀⟩ := hex
  have hsmul : ∀ i (c : ZMod p), c ≠ 0 → c • h i ∈ W → h i ∈ W := by
    intro i c hc hci
    have := W.smul_mem c⁻¹ hci
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hmoved : ∀ i, ∀ v ∈ W, α i v • h i ∈ W := by
    intro i v hv
    have := W.sub_mem hv (hinv i v hv)
    rwa [sub_sub_cancel] at this
  have hi₀W : h i₀ ∈ W := hsmul i₀ _ hi₀ (hmoved i₀ w hwW)
  have hall : ∀ j, h j ∈ W := by
    intro j
    induction ggCartanAMod_conn r p i₀ j with
    | refl => exact hi₀W
    | tail _ hbc ih =>
      refine hsmul _ _ ?_ (hmoved _ _ ih)
      rw [hpair, (CartanMatrix.A_isSymm r).apply]
      exact hbc
  refine le_antisymm hW (Submodule.span_le.mpr ?_)
  rintro _ ⟨j, rfl⟩
  exact hall j

end CartanA

section Displacement

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V]

theorem ggCoroot_eq_pow_displacement (hp2 : p ≠ 2) (ι : Additive ↥Bs ≃+ V) {φ : MulAut ↥Bs}
    {hv : V} {αv : Module.Dual (ZMod p) V}
    (hφ : ∀ w, ggLin (p := p) ι φ w = w - αv w • hv) (h2 : αv hv = 2) :
    ∃ k : ℕ, ((Additive.toMul (ι.symm hv))⁻¹ * φ (Additive.toMul (ι.symm hv))) ^ k =
      Additive.toMul (ι.symm hv) := by
  set c : ↥Bs := Additive.toMul (ι.symm hv) with hc
  have hιc : ι (Additive.ofMul c) = hv := by simp [hc]
  have hιd : ι (Additive.ofMul (c⁻¹ * φ c)) = (-2 : ZMod p) • hv := by
    rw [ofMul_mul, map_add, ofMul_inv, map_neg, ← ggLin_apply_ofMul (p := p) ι φ c, hιc, hφ, h2]
    module
  have h20 : (-2 : ZMod p) ≠ 0 := by
    rw [neg_ne_zero]
    exact zmod_two_ne_zero hp2
  refine ⟨((-2 : ZMod p)⁻¹).val, ?_⟩
  apply Additive.ofMul.injective
  apply ι.injective
  rw [ofMul_pow, map_nsmul, hιd, hιc, ← Nat.cast_smul_eq_nsmul (ZMod p), smul_smul,
    ZMod.natCast_zmod_val, inv_mul_cancel₀ h20, one_smul]

theorem ggCoroot_mem_ggBstarComm (hp2 : p ≠ 2) (ι : Additive ↥Bs ≃+ V) {φ : MulAut ↥Bs}
    {hv : V} {αv : Module.Dual (ZMod p) V}
    (hφ : ∀ w, ggLin (p := p) ι φ w = w - αv w • hv) (h2 : αv hv = 2)
    (hφX : φ ∈ ggAutomizer X Bs) : Additive.toMul (ι.symm hv) ∈ ggBstarComm X Bs := by
  obtain ⟨k, hk⟩ := ggCoroot_eq_pow_displacement hp2 ι hφ h2
  have hd : (Additive.toMul (ι.symm hv))⁻¹ * φ (Additive.toMul (ι.symm hv)) ∈
      ggBstarComm X Bs := Subgroup.subset_closure ⟨_, φ, hφX, rfl⟩
  rw [← hk]
  exact Subgroup.pow_mem _ hd k

end Displacement

theorem card_mul_pow_three_le_of_not_le {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs U : Subgroup G} {y : G} (hBs : IsElemAbelian p Bs) (hUB : U ≤ Bs)
    (hyB : y ∈ Bs) (hcard : ¬ Nat.card Bs ≤ p * Nat.card ↥(U ⊔ Subgroup.zpowers y))
    (hyU : y ∉ U) : Nat.card U * p ^ 3 ≤ Nat.card Bs := by
  have hp : p.Prime := Fact.out
  have hpg : IsPGroup p Bs := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hBs.2 g g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  have hU'B : U ⊔ Subgroup.zpowers y ≤ Bs := sup_le hUB (Subgroup.zpowers_le.mpr hyB)
  have hUU' : U ≤ U ⊔ Subgroup.zpowers y := le_sup_left
  have hdvdU' : Nat.card ↥(U ⊔ Subgroup.zpowers y) ∣ p ^ n := hn ▸ Subgroup.card_dvd_of_le hU'B
  have hdvdU : Nat.card U ∣ p ^ n := hn ▸ Subgroup.card_dvd_of_le hUB
  have hlt : Nat.card U < Nat.card ↥(U ⊔ Subgroup.zpowers y) := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hUU') fun heq => hyU ?_
    rw [Subgroup.eq_of_le_of_card_ge hUU' heq.ge]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp hdvdU'
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvdU
  rw [hi, hj] at hlt
  have hji : j < i := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
  push Not at hcard
  rw [hn, hi, ← pow_succ'] at hcard
  have hin : i + 1 < n := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hcard
  rw [hj, hn, ← pow_add]
  exact Nat.pow_le_pow_right hp.pos (by omega)

open CFSG.StandardType.LineU in
theorem GGResHyp.exists_twD_inverter_of_unitary_J
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel GGOrthTorusLabel p Bs L)
    {F : Type} [Field F] [Finite F] [CharP F 2] {f m : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    (hm : 4 ≤ m) (hpm : ¬ p ∣ m)
    {χ : ↥(unitarySU 2 f F m) →* J} (hM : UnitTB.Model χ)
    (hdiag : ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range, ∃ t : Fin m → F,
      ActsDiagU χ a t)
    (hcodim : Nat.card ↥((ggBstarComm J Bs).map Bs.subtype) * p ^ 3 ≤ Nat.card Bs) :
    (ggBstarComm J Bs).map Bs.subtype = Bs ⊓ J ∧ Nat.card ↥(Bs ⊓ J) = p ^ (m - 1) ∧
      ∃ n : G, n ∈ L ∧ n ∈ Subgroup.normalizer (Bs : Set G) ∧ n * x * n⁻¹ = x ∧
        ∀ u ∈ Bs ⊓ J, n * u * n⁻¹ = u⁻¹ := by
  classical
  obtain ⟨rJ, rfl⟩ : ∃ rJ, m = rJ + 1 := ⟨m - 1, by omega⟩
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have hNJ : Bs ≤ Subgroup.normalizer (J : Set G) := hH.Bs_le_normalizer_J
  have hJL : J ≤ L := hH.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hpr : ¬ p ∣ rJ + 1 := hpm
  obtain ⟨V, hVadd, hVmod, ι, -, φ, h, α, -, -, -, hlin, -, hpair, -, hcl⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover hF hf hp2 hpq (by omega : 3 ≤ rJ)
      hBs hSC hNJ hM hdiag
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have hα2 : ∀ i, α i (h i) = 2 := by
    intro i
    rw [hpair i i, (ggIntCartan_A rJ).1 i]
    norm_num
  have hAJ : ∀ i, φ i ∈ ggAutomizer J Bs := fun i => by
    rw [hcl]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  set Usp : Subgroup G := ggSpanSub ι (Submodule.span (ZMod p) (Set.range h)) with hUsp
  have hcorJ : ∀ i, ((Additive.toMul (ι.symm (h i)) : ↥Bs) : G) ∈ J :=
    fun i => ggCoroot_mem hp2 hNJ ι (hlin i) (hα2 i) (hAJ i)
  have hUeq : (ggBstarComm J Bs).map Bs.subtype = Usp := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      exact coe_mem_ggSpanSub_iff.mpr (ggBstarComm_le_span hlin hcl hc)
    · exact ggSpanSub_le ι fun i =>
        ⟨_, ggCoroot_mem_ggBstarComm hp2 ι (hlin i) (hα2 i) (hAJ i), rfl⟩
  have hUJ : Usp ≤ Bs ⊓ J := le_inf (ggSpanSub_le_bs ι _) (ggSpanSub_le ι hcorJ)
  have hcard : Nat.card Usp = p ^ rJ := by
    rw [card_ggSpanSub, ← FiniteField.pow_finrank_eq_natCard p,
      finrank_span_eq_card (cartanA_linearIndependent hpr hpair), Fintype.card_fin]
  have hperf : Group.IsPerfect ↥(unitarySU 2 f F (rJ + 1)) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) hF (by omega) fun h3 => by
      have := congrArg Prod.fst h3
      simp only at this
      omega
  have hkerC : χ.ker ≤ Subgroup.center ↥(unitarySU 2 f F (rJ + 1)) := fun g hg => by
    obtain ⟨c, hc⟩ := hM.ker g (MonoidHom.mem_ker.mp hg)
    exact SmallU.mem_center_of_scalar hc
  have hcomap := CFSG.LocalCores.comap_center_eq_of_perfect hperf χ hM.surj hkerC
  have hcenterpow : ∀ s ∈ Subgroup.center ↥(unitarySU 2 f F (rJ + 1)), s ^ (rJ + 1) = 1 := by
    intro s hs
    have hdvd : Nat.card (Subgroup.center ↥(unitarySU 2 f F (rJ + 1))) ∣ rJ + 1 := by
      rw [CFSG.SeitzReduction.UnitaryPilot.center_unitarySU_eq_unitaryScalars hM.field,
        card_unitaryScalars hM.field (by omega)]
      exact Nat.gcd_dvd_left _ _
    have h1 : (⟨s, hs⟩ : Subgroup.center ↥(unitarySU 2 f F (rJ + 1))) ^
        Nat.card (Subgroup.center ↥(unitarySU 2 f F (rJ + 1))) = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_pow] at h2
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one h2).trans hdvd)
  have hBJC : Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
    refine le_antisymm (fun z hz => ?_) bot_le
    obtain ⟨⟨hzB, hzJ⟩, hzC⟩ := hz
    obtain ⟨s, hs⟩ := hM.surj ⟨z, hzJ⟩
    have hsC : s ∈ Subgroup.center ↥(unitarySU 2 f F (rJ + 1)) := by
      rw [← hcomap, Subgroup.mem_comap, hs, Subgroup.mem_center_iff]
      intro j
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hzC j j.2
    have hzm : z ^ (rJ + 1) = 1 := by
      have h1 := congrArg (fun t : ↥J => (t : G)) (congrArg χ (hcenterpow s hsC))
      simpa [map_pow, hs] using h1
    have hzp : z ^ p = 1 := hBs.2 z hzB
    have hcop : Nat.Coprime (rJ + 1) p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpr).symm
    have hz1 := pow_gcd_eq_one.mpr ⟨hzm, hzp⟩
    rw [hcop.gcd_eq_one, pow_one] at hz1
    exact Subgroup.mem_bot.mpr hz1
  have hAp : ∀ a ∈ (ggGamma J hNJ).range, a ^ p = 1 := by
    rintro a ⟨b, rfl⟩
    have hb : b ^ p = 1 := Subtype.ext (hBs.2 (b : G) b.2)
    rw [← map_pow, hb, map_one]
  have hγ : Nat.card (ggGamma J hNJ).range ≤ p ^ rJ :=
    UnitTB.card_diagonal_pow_le hM (by omega) hp hAp hdiag
  have hBJcard : Nat.card ↥(Bs ⊓ J) ≤ p ^ rJ := by
    let e : ↥(Bs ⊓ J) → (ggGamma J hNJ).range := fun z =>
      ⟨ggGamma J hNJ ⟨z, z.2.1⟩, ⟨z, z.2.1⟩, rfl⟩
    have he : Function.Injective e := by
      intro a b hab
      have h1 : ggGamma J hNJ ⟨a, a.2.1⟩ = ggGamma J hNJ ⟨b, b.2.1⟩ := congrArg Subtype.val hab
      have h2 : ggGamma J hNJ (⟨a, a.2.1⟩ * (⟨b, b.2.1⟩ : ↥Bs)⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      have h3 := (ggGamma_eq_one_iff J hNJ _).mp h2
      have h4 : (a : G) * (b : G)⁻¹ ∈ Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G) :=
        ⟨(Bs ⊓ J).mul_mem a.2 ((Bs ⊓ J).inv_mem b.2), h3⟩
      rw [hBJC, Subgroup.mem_bot, mul_inv_eq_one] at h4
      exact Subtype.ext h4
    exact (Nat.card_le_card_of_injective e he).trans hγ
  have hBJeq : Usp = Bs ⊓ J :=
    Subgroup.eq_of_le_of_card_ge hUJ (by rw [hcard]; exact hBJcard)
  refine ⟨hUeq.trans hBJeq, by rw [← hBJeq, hcard, Nat.add_sub_cancel], ?_⟩
  rw [← hBJeq]
  let W : Set G := {w | w ∈ J ∧ w ∈ Subgroup.normalizer (Bs : Set G)}
  have hWL : W ⊆ L := fun w hw => hJL hw.1
  have hWN : W ⊆ Subgroup.normalizer (Bs : Set G) := fun w hw => hw.2
  have hdisp : ∀ w ∈ W, ∀ b ∈ Bs, b⁻¹ * (w * b * w⁻¹) ∈ Usp := by
    intro w hw b hb
    rw [← hUeq]
    exact ⟨(⟨b, hb⟩ : ↥Bs)⁻¹ * ggConjAut Bs hw.2 ⟨b, hb⟩,
      Subgroup.subset_closure ⟨⟨b, hb⟩, ggConjAut Bs hw.2,
        ggConjAut_mem_ggAutomizer hw.1 hw.2, rfl⟩, rfl⟩
  have hgen : Usp ≤ Subgroup.closure {c | ∃ w ∈ W, ∃ b ∈ Bs, c = b⁻¹ * (w * b * w⁻¹)} := by
    refine ggSpanSub_le ι fun i => ?_
    obtain ⟨n, hnJ, hnN, hn⟩ := mem_ggAutomizer_iff.mp (hAJ i)
    obtain ⟨k, hk⟩ := ggCoroot_eq_pow_displacement hp2 ι (hlin i) (hα2 i)
    rw [← hk, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, hn]
    refine Subgroup.pow_mem _ (Subgroup.subset_closure ?_) k
    exact ⟨n, ⟨hnJ, hnN⟩, _, (Additive.toMul (ι.symm (h i))).2, rfl⟩
  have hirr : ∀ U' : Subgroup G, U' ≤ Usp → (∀ w ∈ W, ∀ u ∈ U', w * u * w⁻¹ ∈ U') →
      U' = ⊥ ∨ U' = Usp := by
    intro U' hU' hinvU
    let A : AddSubgroup V :=
      { carrier := {v | ((Additive.toMul (ι.symm v) : ↥Bs) : G) ∈ U'}
        add_mem' := fun {a b} ha hb => by
          change ((Additive.toMul (ι.symm (a + b)) : ↥Bs) : G) ∈ U'
          rw [map_add, toMul_add, Subgroup.coe_mul]
          exact U'.mul_mem ha hb
        zero_mem' := by
          change ((Additive.toMul (ι.symm 0) : ↥Bs) : G) ∈ U'
          rw [map_zero, toMul_zero, Subgroup.coe_one]
          exact U'.one_mem
        neg_mem' := fun {a} ha => by
          change ((Additive.toMul (ι.symm (-a)) : ↥Bs) : G) ∈ U'
          rw [map_neg, toMul_neg, Subgroup.coe_inv]
          exact U'.inv_mem ha }
    let Wv : Submodule (ZMod p) V := AddSubgroup.toZModSubmodule p A
    have hmemWv : ∀ v, v ∈ Wv ↔ ((Additive.toMul (ι.symm v) : ↥Bs) : G) ∈ U' :=
      fun _ => Iff.rfl
    have hWle : Wv ≤ Submodule.span (ZMod p) (Set.range h) := by
      intro v hv
      have h1 := hU' ((hmemWv v).mp hv)
      rw [hUsp, coe_mem_ggSpanSub_iff, ofMul_toMul, AddEquiv.apply_symm_apply] at h1
      exact h1
    have hWinv : ∀ i, ∀ w ∈ Wv, w - α i w • h i ∈ Wv := by
      intro i w hw
      obtain ⟨n, hnJ, hnN, hn⟩ := mem_ggAutomizer_iff.mp (hAJ i)
      rw [← hlin i w, hmemWv, ggLin_apply, AddEquiv.symm_apply_apply, toMul_ofMul, hn]
      exact hinvU n ⟨hnJ, hnN⟩ _ ((hmemWv w).mp hw)
    rcases cartanA_span_irred hp2 hpr hpair Wv hWle hWinv with hbot | htop
    · left
      refine le_antisymm (fun g hg => ?_) bot_le
      have hgB : g ∈ Bs := ggSpanSub_le_bs ι _ (hU' hg)
      have hv : ι (Additive.ofMul (⟨g, hgB⟩ : ↥Bs)) ∈ Wv := by
        rw [hmemWv, AddEquiv.symm_apply_apply, toMul_ofMul]
        exact hg
      rw [hbot, Submodule.mem_bot, map_eq_zero_iff ι ι.injective] at hv
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val (ofMul_eq_zero.mp hv))
    · right
      refine le_antisymm hU' fun g hg => ?_
      obtain ⟨v, hv, rfl⟩ := mem_ggSpanSub.mp hg
      rw [← htop] at hv
      exact (hmemWv v).mp hv
  rw [hUeq] at hcodim
  exact hH.exists_twD_inverter_of_irred hp2 hMark ((hUJ.trans inf_le_right).trans hJL) hWL hWN
    hdisp hgen hirr hcodim

open CFSG.StandardType.LineU in
theorem GGResHyp.exists_unitary_J_block_of_K
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : r ≠ 5) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLabK : GGHasLabel ⟨.twA, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛK : LargeEvenInLambda2 ⟨.twA, r, f⟩)
    (hcard : ¬ Nat.card Bs ≤ p * Nat.card
      ↥((ggBstarComm K Bs).map Bs.subtype ⊔ Subgroup.zpowers y))
    (hyU : y ∉ (ggBstarComm K Bs).map Bs.subtype) :
    Nat.card Bs = p ^ (r + 2) ∧
      (ggBstarComm J Bs).map Bs.subtype ≤ (ggBstarComm K Bs).map Bs.subtype ∧
      Nat.card ↥((ggBstarComm K Bs).map Bs.subtype) * p ^ 3 ≤ Nat.card Bs ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (S : Finset (Fin (r + 1)))
        (χ : ↥(unitarySU 2 f F S.card) →* J),
        Nat.card F = (2 ^ f) ^ 2 ∧ S.card = r ∧ UnitTB.Model χ ∧
        ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range, ∃ t : Fin S.card → F,
          ActsDiagU χ a t := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have hyB : y ∈ Bs := hH.1.2.1.1 hnb.1.2.1
  have hxD : x ∈ D := hH.1.2.2.1.2.2.2.1
  have hx : x ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hxD)
  have hNJ : Bs ≤ Subgroup.normalizer (J : Set G) := hH.Bs_le_normalizer_J
  have hUK3 : Nat.card ↥((ggBstarComm K Bs).map Bs.subtype) * p ^ 3 ≤ Nat.card Bs :=
    card_mul_pow_three_le_of_not_le hBs (fun _ ⟨c, _, hc⟩ => hc ▸ c.2) hyB hcard hyU
  obtain ⟨F, hField, hFinite, hChar, hNK, ψ, hF, hM, hdiag⟩ :=
    exists_diagonal_cover_of_large_unitary_side hRig hH (Or.inr ⟨y, hnb⟩) hr hr5 hpq hpd
      hLabK hΛK
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hf1 : 1 ≤ f := hΛK.1
  obtain ⟨V, hVadd, hVmod, ι, -, φK, hK, αK, -, -, -, hlinK, -, hpairK, -, hclK⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover hF hf1 hp2 hpq (by omega : 3 ≤ r) hBs hSC hNK
      hM hdiag
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have hαK2 : ∀ i, αK i (hK i) = 2 := by
    intro i
    rw [hpairK i i, (ggIntCartan_A r).1 i]
    norm_num
  have hindK : LinearIndependent (ZMod p) (fun k : Fin (r - 1) => hK ⟨k, by omega⟩) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h0 : c = 0 := ggCartanAMod_rows_indep r p c fun j => by
      have hj := congrArg (αK j) hc
      rw [map_sum, map_zero] at hj
      rw [← hj]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [map_smul, smul_eq_mul, hpairK, ggCartanAMod, (CartanMatrix.A_isSymm r).apply]
    intro k
    rw [h0, Pi.zero_apply]
  have hcorK : ∀ k : Fin (r - 1),
      ((Additive.toMul (ι.symm (hK ⟨k, by omega⟩)) : ↥Bs) : G) ∈
        (ggBstarComm K Bs).map Bs.subtype := fun k =>
    ⟨_, ggCoroot_mem_ggBstarComm hp2 ι (hlinK _) (hαK2 _)
      (by rw [hclK]; exact Subgroup.subset_closure ⟨_, rfl⟩), rfl⟩
  have hUKlow : p ^ (r - 1) ≤ Nat.card ↥((ggBstarComm K Bs).map Bs.subtype) := by
    have hspan : Nat.card ↥(Submodule.span (ZMod p)
        (Set.range fun k : Fin (r - 1) => hK ⟨k, by omega⟩)) = p ^ (r - 1) := by
      rw [← FiniteField.pow_finrank_eq_natCard p, finrank_span_eq_card hindK, Fintype.card_fin]
    have hle := Subgroup.card_le_of_le (ggSpanSub_le (p := p) ι hcorK)
    rwa [card_ggSpanSub, hspan] at hle
  have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 (hPJ G p B x L D J hH.1.1 hH.1.2.2) hnb
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggIsComponentOf_inf_centralizer_nbr hH.1 hnb hJK
  obtain ⟨S, hJblock, hS2⟩ := exists_block_of_diagonal_unitary_component (by omega : 2 ≤ r) hf1
    hpq hBs hNK hF hM hdiag (Set.singleton_subset_iff.mpr hx) hcomp
  obtain ⟨χ, hχs, hχker, hχdiag⟩ := exists_diagCover_blockSU hM hNK hdiag le_rfl S hJblock hNJ
  have hMJ : UnitTB.Model χ := ⟨hM.field, hχs, hχker⟩
  have hdiagJ : ∀ a ∈ (ggGamma J hNJ).range, ∃ t : Fin S.card → F, ActsDiagU χ a t := by
    rintro _ ⟨b, rfl⟩
    exact hχdiag b
  have hxJ : x ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hjD : j ∈ Subgroup.centralizer (D : Set G) := (hH.1.2.2.1.2.2.2.2.2.1.1 hj).2
    exact ((Subgroup.mem_centralizer_iff.mp hjD) x hxD).symm
  have hxK : x ∉ Subgroup.centralizer (K : Set G) := by
    intro hxK
    apply hnb.2.2.2
    have hz : Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.zpowers_le.mpr hxK
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hz)]
    exact bot_le
  have hSle : S.card ≤ r := by
    by_contra hcon
    have hSu : S = Finset.univ := by
      apply Finset.eq_univ_of_card
      have h1 := Finset.card_le_univ S
      rw [Fintype.card_fin] at h1 ⊢
      omega
    have htop : TableBUE.blockSU (K := F) (n := f) (Finset.univ : Finset (Fin (r + 1))) = ⊤ := by
      ext g
      simp only [Subgroup.mem_top, iff_true]
      intro i j hij
      simp at hij
    have hJeqK : J = K := by
      rw [hJblock, hSu, htop, ← MonoidHom.range_eq_map, MonoidHom.range_comp,
        MonoidHom.range_eq_top_of_surjective _ hM.surj, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    exact hxK (hJeqK ▸ hxJ)
  have hS3 : 3 ≤ S.card := hH.unitaryModel_J_degree_ge_three hS2 hMJ hdiagJ
  have hAp : ∀ a ∈ (ggGamma J hNJ).range, a ^ p = 1 := by
    rintro a ⟨b, rfl⟩
    have hb : b ^ p = 1 := Subtype.ext (hBs.2 (b : G) b.2)
    rw [← map_pow, hb, map_one]
  have hγJ : Nat.card (ggGamma J hNJ).range ≤ p ^ (S.card - 1) :=
    UnitTB.card_diagonal_pow_le hMJ hS3 hp hAp hdiagJ
  have hBsle : Nat.card Bs ≤ p ^ (S.card - 1) * p ^ 3 := by
    have hker : (ggGamma J hNJ).ker = (Subgroup.centralizer (J : Set G)).subgroupOf Bs := by
      ext b
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff]
    have hkerCard : Nat.card ↥((Subgroup.centralizer (J : Set G)).subgroupOf Bs) =
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := by
      rw [← Subgroup.inf_subgroupOf_left]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hc := TableB.card_range_mul_card_ker (ggGamma J hNJ)
    rw [hker, hkerCard] at hc
    rw [← hc]
    exact Nat.mul_le_mul hγJ hH.1.card_bstar_inf_centralizer_J_le
  have hSr : S.card = r := by
    have h1 : p ^ (r - 1) * p ^ 3 ≤ p ^ (S.card - 1) * p ^ 3 :=
      (Nat.mul_le_mul_right _ hUKlow).trans (hUK3.trans hBsle)
    have h2 : p ^ (r - 1) ≤ p ^ (S.card - 1) :=
      Nat.le_of_mul_le_mul_right h1 (pow_pos hp.pos 3)
    have h3 : r - 1 ≤ S.card - 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
    omega
  have hUJK : (ggBstarComm J Bs).map Bs.subtype ≤ (ggBstarComm K Bs).map Bs.subtype := by
    refine Subgroup.map_mono (Subgroup.closure_mono ?_)
    rintro _ ⟨b, φ', hφ', rfl⟩
    exact ⟨b, φ', ggAutomizer_mono Bs hJK hφ', rfl⟩
  have hBseq : Nat.card Bs = p ^ (r + 2) := by
    refine le_antisymm ?_ ?_
    · calc Nat.card Bs ≤ p ^ (S.card - 1) * p ^ 3 := hBsle
        _ = p ^ (r + 2) := by rw [hSr, ← pow_add]; congr 1; omega
    · calc p ^ (r + 2) = p ^ (r - 1) * p ^ 3 := by rw [← pow_add]; congr 1; omega
        _ ≤ Nat.card ↥((ggBstarComm K Bs).map Bs.subtype) * p ^ 3 :=
          Nat.mul_le_mul_right _ hUKlow
        _ ≤ Nat.card Bs := hUK3
  exact ⟨hBseq, hUJK, hUK3, F, inferInstance, inferInstance, inferInstance, S, χ, hF, hSr, hMJ,
    hdiagJ⟩

open CFSG.StandardType.LineU in
theorem GGResHyp.exists_twD_inverter_of_unitary_K
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel GGOrthTorusLabel p Bs L)
    {r f : ℕ} (hr : 4 ≤ r) (hr5 : r ≠ 5) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLabK : GGHasLabel ⟨.twA, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛK : LargeEvenInLambda2 ⟨.twA, r, f⟩)
    (hcard : ¬ Nat.card Bs ≤ p * Nat.card
      ↥((ggBstarComm K Bs).map Bs.subtype ⊔ Subgroup.zpowers y))
    (hyU : y ∉ (ggBstarComm K Bs).map Bs.subtype) :
    (ggBstarComm K Bs).map Bs.subtype = Bs ⊓ J ∧ ggBstarComm K Bs = (Bs ⊓ J).subgroupOf Bs ∧
      ∃ n : G, n ∈ L ∧ n ∈ Subgroup.normalizer (Bs : Set G) ∧ n * x * n⁻¹ = x ∧
        ∀ u ∈ Bs ⊓ J, n * u * n⁻¹ = u⁻¹ := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨hBseq, hUJK, hUK3, F, _, _, _, S, χ, hF, hSr, hMJ, hdiagJ⟩ :=
    hH.exists_unitary_J_block_of_K hRig hLB hPJ hr hr5 hpq hpd hLabK hΛK hcard hyU
  have hpS : ¬ p ∣ S.card := by
    rw [hSr]
    intro h
    exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h).mp hpd))
  have hcodim : Nat.card ↥((ggBstarComm J Bs).map Bs.subtype) * p ^ 3 ≤ Nat.card Bs :=
    (Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hUJK)).trans hUK3
  obtain ⟨hUJeq, hUJcard, n, hnL, hnN, hnx, hnu⟩ :=
    hH.exists_twD_inverter_of_unitary_J hMark hF hΛK.1 hpq (by omega : 4 ≤ S.card) hpS hMJ
      hdiagJ hcodim
  have hUeq : (ggBstarComm K Bs).map Bs.subtype = Bs ⊓ J := by
    rw [← hUJeq]
    symm
    refine Subgroup.eq_of_le_of_card_ge hUJK ?_
    rw [hUJeq, hUJcard]
    refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hp.pos 3)
    calc Nat.card ↥((ggBstarComm K Bs).map Bs.subtype) * p ^ 3 ≤ Nat.card Bs := hUK3
      _ = p ^ (S.card - 1) * p ^ 3 := by rw [hBseq, hSr, ← pow_add]; congr 1; omega
  refine ⟨hUeq, ?_, n, hnL, hnN, hnx, hnu⟩
  rw [← hUeq]
  exact (Subgroup.comap_map_eq_self_of_injective Bs.subtype_injective _).symm

theorem GGResHyp.exists_twD_inverter_of_unitary_marking
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel GGOrthTorusLabel p Bs L)
    (hMarkK : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ lab.rank ≠ 5 ∧ p ∣ lab.rank + 1 ∧
        p ∣ 2 ^ lab.n + 1) p Bs K)
    (hcard : ¬ Nat.card Bs ≤ p * Nat.card
      ↥((ggBstarComm K Bs).map Bs.subtype ⊔ Subgroup.zpowers y))
    (hyU : y ∉ (ggBstarComm K Bs).map Bs.subtype) :
    (ggBstarComm K Bs).map Bs.subtype = Bs ⊓ J ∧ ggBstarComm K Bs = (Bs ⊓ J).subgroupOf Bs ∧
      ∃ n : G, n ∈ L ∧ n ∈ Subgroup.normalizer (Bs : Set G) ∧ n * x * n⁻¹ = x ∧
        ∀ u ∈ Bs ⊓ J, n * u * n⁻¹ = u⁻¹ := by
  obtain ⟨⟨t, r, f⟩, hΛ, hhas, -, -, -, -, -, ⟨htag, hr, hr5, hpd, hpq⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel hMarkK
  change t = .twA at htag
  subst htag
  exact hH.exists_twD_inverter_of_unitary_K hRig hLB hPJ hMark hr hr5 hpq hpd hhas hΛ hcard hyU

theorem ggInnerDiagOnLabel_twA_of_tbTor {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {Bs K : Subgroup G}
    (hK : GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hNs : ¬ GGInnerDiagOnLabel GGTBTorNonsingularCov p Bs K)
    (hSplit : ¬ GGInnerDiagOnLabel GGTBTorSplitLinearCov p Bs K) :
    GGInnerDiagOnLabel (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ lab.rank ≠ 5 ∧
      p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1) p Bs K := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hK
  obtain ⟨-, -, -, -, -, -, -, hcov, -, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨r, m, N, C, M, hrow⟩ := id hcov
  have hsing : (p : ℤ) ∣ C.det := by
    by_contra hdet
    apply hNs
    refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I _ ⟨hs, hnab, θ, -, hnorm, hind⟩
    exact ⟨hs, hnab, θ, ⟨r, m, N, C, M, hrow, hdet⟩, hnorm, hind⟩
  have hnd : ∀ k : ℕ, k ∣ 4 → ¬ (p : ℤ) ∣ (k : ℤ) := by
    intro k hk hpk
    have hp4 : p ∣ 4 := (Int.natCast_dvd_natCast.mp hpk).trans hk
    have hp22 : p ∣ 2 * 2 := hp4
    rcases (Nat.Prime.dvd_mul hp).mp hp22 with h | h <;>
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hlab' := hlab
  obtain ⟨t, l, n⟩ := lab
  cases hrow with
  | aDep htag hr hpd hpm _ =>
    rcases htag with htag | htag
    ·
      exfalso
      apply hSplit
      refine ⟨hperf, ⟨t, l, n⟩, hlab, largeEvenRawDatum_mono ?_ hraw⟩
      rintro R _ I _ ⟨hs, hnab, θ, -, hnorm, hind⟩
      refine ⟨hs, hnab, θ, ⟨hcov, htag, hr, ?_⟩, hnorm, hind⟩
      have hm : ggTorM ⟨t, l, n⟩ = 2 ^ n - 1 := by
        change t = .A at htag
        simp [ggTorM, htag]
      rwa [hm] at hpm
    ·
      have hm : ggTorM ⟨t, l, n⟩ = 2 ^ n + 1 := by
        change t = .twA at htag
        simp [ggTorM, htag]
      rw [hm] at hpm
      have hr5 : l ≠ 5 := by
        rintro rfl
        have h6 : p ∣ 2 * 3 := hpd
        rcases (Nat.Prime.dvd_mul hp).mp h6 with h | h
        · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
        · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
      refine ⟨hperf, ⟨t, l, n⟩, hlab, largeEvenRawDatum_mono ?_ hraw⟩
      rintro R _ I _ ⟨hs, hnab, θ, -, hnorm, hind⟩
      exact ⟨hs, hnab, θ, ⟨htag, hr, hr5, hpd, hpm⟩, hnorm, hind⟩
  | e6Three _ hp3' _ => exact absurd hp3' hp3
  | e8Three _ hp3' => exact absurd hp3' hp3
  | aInd _ hpd _ =>
    rw [CartanMatrix.A_det] at hsing
    exact absurd (by exact_mod_cast hsing) hpd
  | c htag _ =>
    have hl : 0 < l := by
      rcases htag with htag | htag <;>
      · change t = _ at htag
        subst htag
        exact lt_of_lt_of_le (by norm_num) hlab'.2.1
    rw [CartanMatrix.C_det hl] at hsing
    exact absurd hsing (hnd 2 (by norm_num))
  | d htag =>
    have hl : 2 ≤ l := by
      rcases htag with ⟨htag, -⟩ | ⟨htag, -⟩ <;>
      · change t = _ at htag
        subst htag
        have := hlab'.2
        simp only at this
        omega
    rw [CartanMatrix.D_det hl] at hsing
    exact absurd hsing (hnd 4 dvd_rfl)
  | e6Ind hp3' _ _ =>
    rw [CartanMatrix.E₆_det] at hsing
    exact (hp3' ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
      (by exact_mod_cast hsing))).elim
  | e7 _ _ =>
    rw [CartanMatrix.E₇_det] at hsing
    exact absurd hsing (hnd 2 (by norm_num))
  | e8Ind _ _ _ =>
    rw [CartanMatrix.E₈_det] at hsing
    exact absurd hsing (hnd 1 (one_dvd 4))
  | f4 _ _ _ =>
    rw [CartanMatrix.F₄_det] at hsing
    exact absurd hsing (hnd 1 (one_dvd 4))
  | g2 _ _ =>
    rw [CartanMatrix.G₂_det] at hsing
    exact absurd hsing (hnd 1 (one_dvd 4))
  | relD htag =>
    have hl : 0 < l - 1 := by
      rcases htag with ⟨htag, -⟩ | ⟨htag, -⟩ <;>
      · change t = _ at htag
        subst htag
        have := hlab'.2
        simp only at this
        omega
    rw [CartanMatrix.B_det hl] at hsing
    exact absurd hsing (hnd 2 (by norm_num))
  | relE6 _ _ =>
    rw [CartanMatrix.F₄_det] at hsing
    exact absurd hsing (hnd 1 (one_dvd 4))
  | relA5 _ _ =>
    rw [CartanMatrix.C_det (by norm_num)] at hsing
    exact absurd hsing (hnd 2 (by norm_num))

theorem GGResHyp.exists_twD_inverter_of_tbTor
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp3 : p ≠ 3)
    (hK : GGInnerDiagOnLabel GGTBTorCov p Bs K)
    (hNs : ¬ GGInnerDiagOnLabel GGTBTorNonsingularCov p Bs K)
    (hSplit : ¬ GGInnerDiagOnLabel GGTBTorSplitLinearCov p Bs K)
    (hMark : GGInnerDiagOnLabel GGOrthTorusLabel p Bs L)
    (hcard : ¬ Nat.card Bs ≤ p * Nat.card
      ↥((ggBstarComm K Bs).map Bs.subtype ⊔ Subgroup.zpowers y))
    (hyU : y ∉ (ggBstarComm K Bs).map Bs.subtype) :
    (ggBstarComm K Bs).map Bs.subtype = Bs ⊓ J ∧ ggBstarComm K Bs = (Bs ⊓ J).subgroupOf Bs ∧
      ∃ n : G, n ∈ L ∧ n ∈ Subgroup.normalizer (Bs : Set G) ∧ n * x * n⁻¹ = x ∧
        ∀ u ∈ Bs ⊓ J, n * u * n⁻¹ = u⁻¹ :=
  hH.exists_twD_inverter_of_unitary_marking hRig hLB hPJ hMark
    (ggInnerDiagOnLabel_twA_of_tbTor Fact.out hH.1.1.2.2.2.2.2.1.2.1 hp3 hK hNs hSplit) hcard hyU

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniCover
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniBlock
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorUniConfig
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorPGU6
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentUniLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInUniTransPow
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniTypeDet
import CFSG.LocalAnalysis.StandardType.KGLangS1AUniTransfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.SemisimpleCentralizers
  CFSG.StandardType.S2MathAs51642Interfaces

private theorem cuq2m_exists_heldGU_lift {d m : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ m) ^ 2) (hm : 1 ≤ m)
    (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ 2 ^ m)
    {u : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m)))}
    (hu : u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m)))
      (LargeEvenGUSet (Fin d) K (2 ^ m))) :
    ∃ (s : GL (Fin d) K) (hsN : s ∈ Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K))),
      s ∈ Held.heldGU d K τ hτ ∧
        u = TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨s, hsN⟩ := by
  have hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m K :=
    unitaryFieldData_of_card hm hK
  have hS : LargeEvenGUSet (Fin d) K (2 ^ m) ⊆
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K)) :=
    fun B hB => TableBUE.gu_subset_normalizer (d := d) hF hB
  obtain ⟨M, hM, rfl⟩ := TableB.exists_eq_projConj hS hu
  obtain ⟨c, hc⟩ := CFSG.LocalAnalysis.GLTheoremA.T171Sh.exists_scalar_mul_mem_heldGU
    (d := d) (n := m) hτ hτQ hK M hM
  have hz : Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ LargeEvenScalars (Fin d) K := ⟨c, rfl⟩
  have hzN : (Matrix.GeneralLinearGroup.scalar (Fin d) c) ∈
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K)) :=
    TableB.scalar_mem_normalizer _ hz
  have hMN : (M : GL (Fin d) K) ∈
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K)) :=
    hS hM
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin d) c * (M : GL (Fin d) K),
    mul_mem hzN hMN, hc, ?_⟩
  have hmul : (⟨Matrix.GeneralLinearGroup.scalar (Fin d) c * (M : GL (Fin d) K),
      mul_mem hzN hMN⟩ : Subgroup.normalizer
        (LargeEvenSUGroup (Fin d) K (2 ^ m) : Set (GL (Fin d) K))) =
      ⟨Matrix.GeneralLinearGroup.scalar (Fin d) c, hzN⟩ * ⟨M, hMN⟩ := rfl
  rw [hmul, map_mul, TableB.projConj_of_scalar _ hz, one_mul]

private theorem cuq2m_exists_unitaryInvolution {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ m) ^ 2) :
    ∃ τ : K ≃+* K, (∀ x, τ (τ x) = x) ∧ ∀ x, τ x = x ^ 2 ^ m := by
  have h := unitaryFieldData_of_card hm hK
  let τ : K ≃+* K := RingEquiv.ofBijective h.bar
    ⟨h.bar.injective, fun y => ⟨h.bar y, h.bar_bar y⟩⟩
  exact ⟨τ, fun x => h.bar_bar x, fun x => h.bar_apply x⟩

private lemma cuq2m_E_isElemAbelian
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    {L : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hAb : IsElemAbelian p Bs) {R : Type} [Group R] [Finite R]
    (θ : L ⧸ Subgroup.center L ≃* R) :
    IsElemAbelian p ((ggGamma L hN).range.map (ggInducedAut θ)) := by
  let hcomp : Bs →* MulAut R := (ggInducedAut θ).comp (ggGamma L hN)
  have hrange : hcomp.range = (ggGamma L hN).range.map (ggInducedAut θ) := by
    ext a
    simp only [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨ggGamma L hN b, ⟨b, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, rfl⟩
  rw [← hrange]
  refine isElemAbelian_range (fun a b => hAb.1.is_comm.comm a b)
    (fun b => Subtype.ext (by simpa using hAb.2 b b.2)) hcomp

private lemma cuq2m_E_subset_I
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    {L : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : L ⧸ Subgroup.center L ≃* R)
    (hact : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∀ a ∈ (ggGamma L hN).range.map (ggInducedAut θ), a ∈ I := by
  intro a ha
  let hcomp : Bs →* MulAut R := (ggInducedAut θ).comp (ggGamma L hN)
  have hrange : hcomp.range = (ggGamma L hN).range.map (ggInducedAut θ) := by
    ext a
    simp only [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨ggGamma L hN b, ⟨b, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, rfl⟩
  rw [← hrange] at ha
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp ha
  obtain ⟨φ, hφI, hφ⟩ := hact c⁻¹ (inv_mem c.2)
  have heq : hcomp c = φ := by
    simp only [hcomp, MonoidHom.comp_apply]
    ext x
    obtain ⟨y, rfl⟩ := θ.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    have hrel : ((ggGamma L hN c l : L) : G) = (c⁻¹)⁻¹ * (l : G) * c⁻¹ := by
      rw [ggGamma_coe]
      simp [Subgroup.coe_inv]
    have h1 := hφ l (ggGamma L hN c l) hrel
    rw [ggInducedAut_apply]
    exact h1.symm
  rw [hc] at heq
  rwa [heq]

theorem toralUni_of_not_dvd {d m p : ℕ} (hd : 3 ≤ d) (hm : 1 ≤ m) (hdq : ¬(d = 3 ∧ 2 ^ m = 2))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ m) ^ 2)
    (hp : p.Prime) (hpd : ¬ p ∣ d ∨ ¬ p ∣ 2 ^ m + 1)
    {E : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m))))}
    (hE : IsElemAbelian p E)
    (hEI : ∀ a ∈ E, a ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m))) (LargeEvenGUSet (Fin d) K (2 ^ m))) :
    ToralUni _ E := by
  classical
  unfold ToralUni
  intro d' m' K' _ _ hK' θ
  have hm' : 1 ≤ m' := by
    by_contra h
    have h0 : m' = 0 := by omega
    subst h0
    have h2 : 2 ≤ Nat.card K' := by
      have := Finite.one_lt_card (α := K')
      omega
    rw [hK'] at h2
    norm_num at h2
  have hUF' : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m' K' :=
    unitaryFieldData_of_card hm' hK'
  obtain ⟨hd', hm'eq⟩ := kgLangS1A_psu_typeDet (d := d) (d₁ := d') (m₀ := m) (m := m')
    (F₀ := K) (E := K') hd hm hK hdq hUF' θ
  subst d'
  subst m'
  have hdq' : (d, 2 ^ m) ≠ (3, 2) := by
    intro h
    exact hdq ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
  have hcop : ¬ p ∣ Nat.gcd d (2 ^ m + 1) := by
    intro h
    rcases hpd with hpd | hpd
    · exact hpd (h.trans (Nat.gcd_dvd_left _ _))
    · exact hpd (h.trans (Nat.gcd_dvd_right _ _))
  obtain ⟨τ, hτ, hτQ⟩ := cuq2m_exists_unitaryInvolution hm hK
  rw [isMulCommutative_iff]
  intro g' h'
  obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp g'.2)
  obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp h'.2)
  obtain ⟨s, hsN, hsGU, hsEq⟩ := cuq2m_exists_heldGU_lift hK hm τ hτ hτQ (hEI a ha)
  obtain ⟨t, htN, htGU, htEq⟩ := cuq2m_exists_heldGU_lift hK hm τ hτ hτQ (hEI b hb)
  have hsp : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨s, hsN⟩ ^ p = 1 := by
    rw [← hsEq]
    exact hE.2 a ha
  have hcomm : TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨s, hsN⟩ *
      TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨t, htN⟩ =
      TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨t, htN⟩ *
      TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨s, hsN⟩ := by
    rw [← hsEq, ← htEq]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hst : (t : GL (Fin d) K) * s = s * t :=
    q1CentUni_commute_of_projConj hK hm hd hdq' τ hτ hτQ hp hcop hsGU htGU hsN htN hsp hcomm
  have hM : ∀ x, θ.symm (TableB.projConj (LargeEvenSUGroup (Fin d) K' (2 ^ m)) g'.1 x) =
      TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨s, hsN⟩ (θ.symm x) := by
    intro x
    rw [haeq.symm]
    show θ.symm (θ (a (θ.symm x))) =
      TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨s, hsN⟩ (θ.symm x)
    rw [MulEquiv.symm_apply_apply, hsEq]
  have hN : ∀ x, θ.symm (TableB.projConj (LargeEvenSUGroup (Fin d) K' (2 ^ m)) h'.1 x) =
      TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨t, htN⟩ (θ.symm x) := by
    intro x
    rw [hbeq.symm]
    show θ.symm (θ (b (θ.symm x))) =
      TableB.projConj (LargeEvenSUGroup (Fin d) K (2 ^ m)) ⟨t, htN⟩ (θ.symm x)
    rw [MulEquiv.symm_apply_apply, htEq]
  have htransfer := kgLangS1A_uni_commute_transfer (d := d) (m := m) (F₀ := K') (E := K)
    hd hm hK' hK hdq θ.symm hM hN hst.symm
  exact Subtype.ext (Subtype.ext htransfer)


theorem q2TorUni_notDvd_config :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
      GGConfig p B Bs x L D J →
      GGMarkingAll (K := ↥L) (fun lab R _ I _ θ =>
        lab.tag = .twA → ¬ p ∣ Nat.gcd (lab.rank + 1) (2 ^ lab.n + 1) →
          ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G),
          (∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
          ToralUni R ((ggGamma L hN).range.map (ggInducedAut θ))) := by
  intro G _ _ p B Bs x L D J hcfg
  unfold GGMarkingAll
  intro P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  refine ⟨hperf, lab, hlab, ?_⟩
  by_cases htag : lab.tag = .twA
  · unfold LargeEvenRawDatumLegacy at hraw ⊢
    rw [htag] at hraw ⊢
    obtain ⟨K, fieldInst, finiteInst, hK, hQ⟩ := hraw
    refine ⟨K, fieldInst, finiteInst, hK, ?_⟩
    obtain ⟨hs, hna, θ, hPθ⟩ := hQ
    refine ⟨hs, hna, θ, hPθ, ?_⟩
    intro _ hcop hN hact
    unfold LargeEvenInLambda2 at hlab
    rw [htag] at hlab
    obtain ⟨-, -, -, -, -, hβ, hSstar, -⟩ := hcfg.1
    have hp : p.Prime := hβ.1
    have hBle : B ≤ Bs := hcfg.2.1.1
    have hAb : IsElemAbelian p Bs := hcfg.2.1.2.1
    have hd : 3 ≤ lab.rank + 1 := by have := hlab.2.1; omega
    have hm : 1 ≤ lab.n := hlab.1
    have hdq : ¬((lab.rank + 1) = 3 ∧ 2 ^ lab.n = 2) := by
      rintro ⟨h1, h2⟩
      have hr2 : lab.rank = 2 := by omega
      have hn2 : 2 ≤ lab.n := hlab.2.2 hr2
      have h4 : 4 ≤ 2 ^ lab.n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    have hE : IsElemAbelian p ((ggGamma L hN).range.map (ggInducedAut θ)) :=
      cuq2m_E_isElemAbelian hN hAb θ
    have hEI : ∀ a ∈ (ggGamma L hN).range.map (ggInducedAut θ),
        a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (lab.rank + 1)) K (2 ^ lab.n)))
          (LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n)) :=
      cuq2m_E_subset_I (p := p) hN θ hact
    have hpd : ¬ p ∣ lab.rank + 1 ∨ ¬ p ∣ 2 ^ lab.n + 1 := by
      by_contra h
      simp only [not_or, not_not] at h
      exact hcop (Nat.dvd_gcd h.1 h.2)
    exact toralUni_of_not_dvd (d := lab.rank + 1) (m := lab.n) (p := p)
      hd hm hdq hK hp hpd hE hEI
  · refine largeEvenRawDatum_mono (fun R _ I F hh => ?_) hraw
    obtain ⟨hs, hna, θ, hPθ⟩ := hh
    refine ⟨hs, hna, θ, hPθ, ?_⟩
    intro htag' _ _ _
    exact absurd htag' htag

theorem q2UConfigToral_twA : Q2UConfigToral ToralUni (fun _ lab => lab.tag = .twA) := by
  intro G _ _ p B Bs x L D J hcfg P hP
  have h1 := q2TorUni_notDvd_config G p B Bs x L D J hcfg P hP
  have h2 := q1TorUni_config G p B Bs x L D J hcfg _ h1
  have h3 := q1TorPGU6_config G p B Bs x L D J hcfg _ h2
  refine largeEvenMarking_mono (fun lab R _ I F θ hh => ?_) h3
  obtain ⟨⟨⟨hP', hT1⟩, hT2⟩, hT3⟩ := hh
  refine ⟨hP', fun hS _ hN hact => ?_⟩
  by_cases hg : p ∣ Nat.gcd (lab.rank + 1) (2 ^ lab.n + 1)
  · by_cases h56 : lab.rank = 5 ∧ p = 3
    · refine hT3 ⟨hS, h56.1, h56.2, ?_⟩ hN hact
      rw [h56.2] at hg
      exact hg.trans (Nat.gcd_dvd_right _ _)
    · exact hT2 ⟨hS, hg, h56⟩ hN hact
  · exact hT1 hS hg hN hact

theorem q2URLevelOn_twA : Q2URLevelOn ToralUni (fun _ lab => lab.tag = .twA) := by
  intro p d m lab hΛ hS hSplit hshape hpm hdm
  obtain ⟨t, l, n⟩ := lab
  have ht : t = .twA := hS
  subst ht
  dsimp only [LargeEvenInLambda2] at hΛ
  obtain ⟨hn, hl2, hln⟩ := hΛ
  have hd : 3 ≤ l + 1 := by omega
  have hdq : ((l + 1, 2 ^ n) : ℕ × ℕ) ≠ (3, 2) := by
    rintro h
    have h1 : l + 1 = 3 := congrArg Prod.fst h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    have hl : l = 2 := by omega
    have hn2 : 2 ≤ n := hln hl
    have hpow : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    norm_num at hpow
    omega
  have hpodd : Odd p := by
    rcases hshape with ⟨hp3, -⟩ | ⟨hp5, -⟩
    · subst hp3; norm_num
    · subst hp5; norm_num
  have hd3 : 3 ≤ d := by
    rcases hshape with ⟨-, hd3 | hd6⟩ | ⟨-, hd5⟩
    · omega
    · omega
    · omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  refine ⟨K, i1, i2, hK, hq', ?_⟩
  intro A hAab hAI hTor u huA huord J hJ hAJ E iE hE hJE M hM
  let N := l + 1
  let H : Subgroup (GL (Fin N) K) := LargeEvenSUGroup (Fin N) K (2 ^ n)
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    unitaryFieldData_of_card (n := n) hn hK
  obtain ⟨τ, hτ, hτQ⟩ := exists_unitaryInvolution (m := n) hn hK
  have htorus : IsMulCommutative ↥(A.comap (TableB.projConj H)) :=
    toralUni_commute_datum (d := N) (m := n) (K := K) hK hTor
  obtain ⟨s, hsN, hs_held, hs_proj⟩ :=
    q1CentUni_exists_lift (d := N) (m := n) hK hn τ hτ hτQ (hAI u huA)
  have hsp : TableB.projConj H ⟨s, hsN⟩ ^ p = 1 := by
    rw [← hs_proj, ← huord, pow_orderOf_eq_one]
  have hsp_scal : s ^ p ∈ LargeEvenScalars (Fin N) K :=
    q1CentUni_pow_mem_scalars (d := N) (m := n) hK hn hd hdq hsN hsp
  have hso : Odd (orderOf s) :=
    q1CentUni_odd_orderOf (d := N) (m := n) hK hn hpodd hsp_scal
  have hJc : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup (TableB.projConj H ⟨s, hsN⟩)) := by
    rw [← hs_proj]
    exact hJ
  obtain ⟨C, hC, hCSU, hJeq⟩ :=
    q1TorUni_component_lift (d := N) (m := n) (K := K) τ hτ hτQ s hs_held hsN J hJc
  obtain ⟨a, mD, D, iD, hD, ψ, π, hsquare⟩ :=
    q2Uni_block (N := N) (m := n) hK τ hτ hτQ s hs_held hso C hC hCSU J hJeq
      (d := d) (m' := m) hE hd3 hdm hJE
  let Dom : Subgroup (GL (Fin N) K) :=
    Subgroup.centralizer ({s} : Set (GL (Fin N) K)) ⊓
      CFSG.LieType.SemisimpleCentralizers.Held.heldGU N K τ hτ
  have hGUle : CFSG.LieType.SemisimpleCentralizers.Held.heldGU N K τ hτ ≤
      Subgroup.normalizer (H : Set (GL (Fin N) K)) := by
    intro k hk
    exact TableBUE.gu_subset_normalizer (d := N) hUF
      (q1CentUni_heldGU_subset_guSet (d := N) (m := n) τ hτ hτQ hk)
  let φ : ↥Dom →* Subgroup.normalizer (H : Set (GL (Fin N) K)) :=
    { toFun := fun h => ⟨(h : GL (Fin N) K), hGUle (Subgroup.mem_inf.mp h.2).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let H₀ : Subgroup ↥Dom := (A.comap (TableB.projConj H)).comap φ
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : Subgroup.normalizer (H : Set (GL (Fin N) K)) =>
      (z : GL (Fin N) K)) hab
  have hH₀comm : IsMulCommutative ↥H₀ := by
    rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    apply hφinj
    change φ ((a : ↥Dom) * (b : ↥Dom)) = φ ((b : ↥Dom) * (a : ↥Dom))
    have ha : φ (a : ↥Dom) ∈ A.comap (TableB.projConj H) := a.2
    have hb : φ (b : ↥Dom) ∈ A.comap (TableB.projConj H) := b.2
    have hcomm := (isMulCommutative_iff.mp htorus)
      ⟨φ (a : ↥Dom), ha⟩ ⟨φ (b : ↥Dom), hb⟩
    rw [map_mul, map_mul]
    exact congrArg Subtype.val hcomm
  haveI : IsMulCommutative ↥H₀ := hH₀comm
  let f : ↥H₀ →* ↥(TableB.unitGroup (ι := Fin a) hD.bar) := π.comp H₀.subtype
  let G : Subgroup ↥(TableB.unitGroup (ι := Fin a) hD.bar) := f.range
  have hGcomm : IsMulCommutative G := inferInstance
  refine ⟨a, mD, D, iD, hD, ψ, G, hGcomm, ?_⟩
  intro α hαM
  obtain ⟨b, hbA, hrel⟩ := hM α hαM
  obtain ⟨k, hkN, hk_held, hk_proj⟩ :=
    q1CentUni_exists_lift (d := N) (m := n) hK hn τ hτ hτQ (hAI b hbA)
  have hkN₀ : (⟨k, hkN⟩ : Subgroup.normalizer (H : Set (GL (Fin N) K))) ∈
      A.comap (TableB.projConj H) := by
    rw [Subgroup.mem_comap, ← hk_proj]
    exact hbA
  have hsN₀ : (⟨s, hsN⟩ : Subgroup.normalizer (H : Set (GL (Fin N) K))) ∈
      A.comap (TableB.projConj H) := by
    rw [Subgroup.mem_comap, ← hs_proj]
    exact huA
  have hk_cent : k ∈ Subgroup.centralizer ({s} : Set (GL (Fin N) K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hcomm := (isMulCommutative_iff.mp htorus)
      ⟨⟨k, hkN⟩, hkN₀⟩ ⟨⟨s, hsN⟩, hsN₀⟩
    have hgl := congrArg (fun z : ↥(A.comap (TableB.projConj H)) =>
      ((z : Subgroup.normalizer (H : Set (GL (Fin N) K))) : GL (Fin N) K)) hcomm
    exact hgl.symm
  let h : ↥Dom := ⟨k, Subgroup.mem_inf.mpr ⟨hk_cent, hk_held⟩⟩
  have hφh : φ h = ⟨k, hkN⟩ := Subtype.ext rfl
  have hh₀ : h ∈ H₀ := by
    rw [Subgroup.mem_comap, Subgroup.mem_comap, hφh, ← hk_proj]
    exact hbA
  refine ⟨f ⟨h, hh₀⟩, ?_, ?_⟩
  · exact MonoidHom.mem_range.mpr ⟨⟨h, hh₀⟩, rfl⟩
  · ext y
    obtain ⟨x, rfl⟩ := ψ.surjective y
    induction x using QuotientGroup.induction_on with
    | H j =>
      have hcond : ((⟨b (j : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))),
          hAJ b hbA (j : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))) j.2⟩ : ↥J) :
          LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))) =
          TableB.projConj H ⟨(h : GL (Fin N) K), hGUle (Subgroup.mem_inf.mp h.2).2⟩
            (j : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))) := by
        have h1 : TableB.projConj H
            ⟨(h : GL (Fin N) K), hGUle (Subgroup.mem_inf.mp h.2).2⟩ =
            TableB.projConj H (φ h) := rfl
        rw [h1, hφh]
        exact congrArg (fun z : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))) =>
          z (j : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n)))) hk_proj
      have hSq := hsquare h (hGUle (Subgroup.mem_inf.mp h.2).2) j
        ⟨b (j : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))),
          hAJ b hbA (j : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))) j.2⟩ hcond
      have hrelj := hrel j
        ⟨b (j : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))),
          hAJ b hbA (j : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))) j.2⟩ rfl
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [hrelj]
      exact hSq.symm

theorem ggBstarAbelianPreimageJUniS1On_twA :
    GGBstarAbelianPreimageJUniS1On (fun _ lab => lab.tag = .twA) :=
  ggBstarAbelianPreimageJUniS1On_of_rLevelToral q2UConfigToral_twA q2URLevelOn_twA

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGSignedPermEvenSupport
public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGE6DepNormalizerOfConj
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CoprimeSplit
public import CFSG.LocalAnalysis.StandardType.GGF4NbrAutReflKGReduce
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
public import CFSG.LocalAnalysis.StandardType.GGSignedPermCount

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_conj_eq_sgnSetAut {p : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {k : ℕ} (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    (hd : ∀ i j : Fin k, i ≠ j → ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (SpCoord.sgnAut i * SpCoord.sgnAut j))
    (T : Finset (Fin k)) (hT : Even T.card) :
    ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (SpCoord.sgnSetAut T) := by
  refine SpCoord.sgnSetAut_mem_of_even (S := {α | ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ α}) ?_ ?_ hd T hT
  · have h1 : MulAut.conj (1 : L') ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
      rw [map_one]
      exact Subgroup.one_mem _
    refine ⟨1, h1, MulEquiv.ext fun a => Subtype.ext ?_⟩
    rw [ggConjAut_apply, show MulAut.congr Θ 1 = 1 from map_one _]
    simp
  · rintro α ⟨n₁, hn₁, h₁⟩ β ⟨n₂, hn₂, h₂⟩
    have h12 : MulAut.conj (n₁ * n₂) ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
      rw [map_mul]
      exact Subgroup.mul_mem _ hn₁ hn₂
    refine ⟨n₁ * n₂, h12, MulEquiv.ext fun a => Subtype.ext ?_⟩
    rw [ggConjAut_apply, show MulAut.congr Θ (α * β) = MulAut.congr Θ α * MulAut.congr Θ β from
      map_mul _ _ _, MulAut.mul_apply, ← h₁, ← h₂, ggConjAut_apply, ggConjAut_apply, map_mul]
    group

@[expose] def GGOrthTorusLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ (p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1)

theorem ggInnerDiagOnLabel_orthTorus_of_twD {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G}
    (h : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twD ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) p Bs L) :
    GGInnerDiagOnLabel GGOrthTorusLabel p Bs L :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨⟨ht, hr, hp⟩, hP⟩ => ⟨⟨Or.inr ht, hr, Or.inl hp⟩, hP⟩) h

theorem GGResHyp.exists_twD_inverter
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel GGOrthTorusLabel p Bs L) :
    ¬ p ∣ Nat.card (Subgroup.center L) ∧
    ∃ (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (k : ℕ)
      (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥(ggGamma L hN).range),
      (∀ (n : ↥L) (hn : MulAut.conj n ∈
          Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))),
        SpCoord.IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut (ggGamma L hN).range hn))) ∧
      ∀ T : Finset (Fin k), Even T.card →
        ∃ n : G, n ∈ L ∧ n ∈ Subgroup.normalizer (Bs : Set G) ∧ n * x * n⁻¹ = x ∧
          ∀ (u : G) (hu : u ∈ Bs), u ∈ L →
            (∀ i ∉ T, (Θ.symm ⟨ggGamma L hN ⟨u, hu⟩, ⟨⟨u, hu⟩, rfl⟩⟩) i = 1) →
            n * u * n⁻¹ = u⁻¹ := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R0, _, I0, F0, -, -, θ0, ⟨htag, hrank, hpn⟩, -, -⟩ := largeEvenRawDatum_exists hraw
  let P : LargeEvenRawCont := fun R _ I _ =>
    Subgroup.center R = ⊥ ∧ GGCenterPrime p R ∧
      (I ⊆ Set.range (MulAut.conj : R →* MulAut R)) ∧
      GGTorusEvenSignedPermEltSC p R (fun _ => True)
  have hModels : LargeEvenLabelAll lab P := by
    intro Q hQ
    obtain ⟨t, l, f⟩ := lab
    dsimp only at htag hrank hpn
    rcases htag with rfl | rfl
    ·
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      rw [if_neg (by omega : l ≠ 3)] at hQ ⊢
      obtain ⟨E, _, _, hE, hQ⟩ := hQ
      have : CharP E 2 := charP_two_of_card hE
      obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := E) hp hp2 (by omega : 3 ≤ l)
      have hT : GGTorusEvenSignedPermEltSC p (OrthRest.RPlus E l) fun _ => True := by
        rw [← hE] at hpn
        by_cases hsplit : p ∣ Nat.card E - 1 ∨ (Even l ∧ p ∣ Nat.card E + 1)
        · exact (ggOrthEvenTorusInput_holds.1 E l p hrank hp hsplit).mono (fun _ _ => trivial)
        · have hplus : p ∣ Nat.card E + 1 := hpn.resolve_right fun h => hsplit (Or.inl h)
          have hodd : Odd l := Nat.not_even_iff_odd.mp fun he => hsplit (Or.inr ⟨he, hplus⟩)
          have hl5 : 5 ≤ l := by
            obtain ⟨j, hj⟩ := hodd
            omega
          exact ggTorusEvenSignedPermEltSC_of_signedEltSC
            (ggOrthSignedTorusInput_holds.1 E l p hl5 hodd hp hplus)
      exact ⟨E, inferInstance, inferInstance, hE, hQ, hZ, hcp, (fun _ h => h), hT⟩
    ·
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      rw [if_neg (by omega : l ≠ 2), if_neg (by omega : l ≠ 3)] at hQ ⊢
      obtain ⟨E, _, _, hE, b, c, hbc, hQ⟩ := hQ
      have : CharP E 2 := charP_two_of_card hE
      obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := E) hp hp2
        (by omega : 3 ≤ l - 1) hbc
      have hT : GGTorusEvenSignedPermEltSC p (OrthRest.RMinus E (l - 1) b c) fun _ => True := by
        rw [← hE] at hpn
        by_cases hev : Even (l - 1) ∧ p ∣ Nat.card E + 1
        · obtain ⟨hev, hplus⟩ := hev
          have hm4 : 4 ≤ l - 1 := by
            obtain ⟨j, hj⟩ := hev
            omega
          exact (ggOrthEvenTorusInput_holds.2 E (l - 1) p b c hm4 hev hbc hp hplus).mono
            (fun _ _ => trivial)
        · refine ggTorusEvenSignedPermEltSC_of_signedEltSC
            (ggOrthSignedTorusInput_holds.2 E (l - 1) p b c (by omega) hbc hp ?_)
          rcases hpn with hplus | hminus
          · exact Or.inr ⟨Nat.not_even_iff_odd.mp fun he => hev ⟨he, hplus⟩, hplus⟩
          · exact Or.inl hminus
      exact ⟨E, inferInstance, inferInstance, hE, b, c, hbc, hQ, hZ, hcp, (fun _ h => h), hT⟩
  obtain ⟨R, _, I, F, ⟨-, -, θ, -, hN, hind⟩, hZ, hcp, hI, hT⟩ :=
    largeEvenRawDatum_exists (hModels _ hraw)
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hN hind hb
  have h3 := hH.pow_three_le_card_range (Or.inl rfl) hN
  have hTB := ggTorusTBGroup_of_marking (r := 3) hp hBs hSC hperf θ hN hBsI h3 h3
  obtain ⟨k, Θ, -, -, -, hd, -, -, hsp⟩ := OrthExcEven.exists_evenSignedPermModelSC
    hp hp2 hI hZ hcp hT (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf
    hTB.2.2.2.1 hTB.2.2.2.2.1 h3 hTB.2.2.2.2.2.2.2
  have hZL : ¬ p ∣ Nat.card (Subgroup.center L) :=
    hcp L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf
  have hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    hH.1.bstar_inf_centralizer_L
  have hsplit := ggBstar_split_of_inner_coprime hp hH.1.2.1
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hZL) hN
    (F4AutRefl.exists_conj_of_inn hperf θ hI hN hind)
  have hBsL : ∀ b ∈ Bs, ∃ l ∈ L, ∃ m : ℕ, b = l * x ^ m := by
    intro b hb
    obtain ⟨l, hl, c, hc, hbc⟩ := hsplit b hb
    rw [hker] at hc
    obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers).mpr hc
    exact ⟨l, hl.2, m, by rw [hbc, ← hm]⟩
  refine ⟨hZL, hN, k, Θ, hsp, fun T hT => ?_⟩
  obtain ⟨n, hn, hnΘ⟩ := exists_conj_eq_sgnSetAut Θ hd T hT
  have hnBs : (n : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    GGE6Dep.mem_normalizer_of_conj_mem_normalizer_range hp hN hBs hker hZL hBsL n.2 hn
  refine ⟨n, n.2, hnBs, ?_, ?_⟩
  ·
    have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
      (hker.ge (Subgroup.mem_zpowers x)).2
    rw [Subgroup.mem_centralizer_iff] at hxC
    rw [hxC (n : G) n.2, mul_inv_cancel_right]
  · intro u hu huL hsupp
    have hc : (n : G) * u * (n : G)⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hnBs u).mp hu
    have hγc : ggGamma L hN ⟨(n : G) * u * (n : G)⁻¹, hc⟩ =
        MulAut.conj n * ggGamma L hN ⟨u, hu⟩ * (MulAut.conj n)⁻¹ :=
      ggGamma_conj L hN n ⟨u, hu⟩ hc
    set a : ↥(ggGamma L hN).range := ⟨ggGamma L hN ⟨u, hu⟩, ⟨⟨u, hu⟩, rfl⟩⟩
      with ha
    have hΘ : ggConjAut (ggGamma L hN).range hn a = a⁻¹ := by
      rw [hnΘ, MulAut.congr_apply]
      change Θ (SpCoord.sgnSetAut T (Θ.symm a)) = a⁻¹
      rw [SpCoord.sgnSetAut_apply_of_support hsupp, map_inv, MulEquiv.apply_symm_apply]
    have hγ : ggGamma L hN ⟨(n : G) * u * (n : G)⁻¹, hc⟩ = (ggGamma L hN ⟨u, hu⟩)⁻¹ := by
      rw [hγc]
      have h1 := congrArg Subtype.val hΘ
      rw [ggConjAut_apply] at h1
      exact h1
    have hprod : ggGamma L hN (⟨(n : G) * u * (n : G)⁻¹, hc⟩ * ⟨u, hu⟩) = 1 := by
      rw [map_mul, hγ, inv_mul_cancel]
    rw [ggGamma_eq_one_iff] at hprod
    have hmemL : (n : G) * u * (n : G)⁻¹ * u ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem n.2 huL) (L.inv_mem n.2)) huL
    have hmem : (n : G) * u * (n : G)⁻¹ * u ∈ Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨⟨Bs.mul_mem hc hu, hmemL⟩, hprod⟩
    rw [inf_center_eq_bot_of_isElemAbelian_of_not_dvd hp hBs hZL, Subgroup.mem_bot] at hmem
    exact eq_inv_of_mul_eq_one_left hmem

theorem GGResHyp.exists_twD_inverter_of_irred
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel GGOrthTorusLabel p Bs L)
    {U : Subgroup G} (hUL : U ≤ L) {W : Set G} (hWL : W ⊆ L)
    (hWN : W ⊆ Subgroup.normalizer (Bs : Set G))
    (hdisp : ∀ w ∈ W, ∀ b ∈ Bs, b⁻¹ * (w * b * w⁻¹) ∈ U)
    (hgen : U ≤ Subgroup.closure {c | ∃ w ∈ W, ∃ b ∈ Bs, c = b⁻¹ * (w * b * w⁻¹)})
    (hirr : ∀ U' : Subgroup G, U' ≤ U → (∀ w ∈ W, ∀ u ∈ U', w * u * w⁻¹ ∈ U') →
      U' = ⊥ ∨ U' = U)
    (hcodim : Nat.card U * p ^ 3 ≤ Nat.card Bs) :
    ∃ n : G, n ∈ L ∧ n ∈ Subgroup.normalizer (Bs : Set G) ∧ n * x * n⁻¹ = x ∧
      ∀ u ∈ U, n * u * n⁻¹ = u⁻¹ := by
  classical
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hZL, hN, k, Θ, hsp, hinv⟩ := hH.exists_twD_inverter hp2 hMark
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    hH.1.bstar_inf_centralizer_L
  let φ : ↥Bs →* (Fin k → Multiplicative (ZMod p)) :=
    Θ.symm.toMonoidHom.comp (ggGamma L hN).rangeRestrict
  have hφ : ∀ b : ↥Bs, φ b = Θ.symm ⟨ggGamma L hN b, ⟨b, rfl⟩⟩ := fun b => rfl
  have hφsurj : Function.Surjective φ := by
    intro f
    obtain ⟨b, hb⟩ := (ggGamma L hN).rangeRestrict_surjective (Θ f)
    exact ⟨b, by rw [show φ b = Θ.symm ((ggGamma L hN).rangeRestrict b) from rfl, hb,
      MulEquiv.symm_apply_apply]⟩
  have hwA : ∀ w (hw : w ∈ W), MulAut.conj (⟨w, hWL hw⟩ : ↥L) ∈
      Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)) :=
    fun w hw => conj_mem_normalizer_range_ggGamma hN (hWL hw) (hWN hw)
  let hW : W → MulAut (Fin k → Multiplicative (ZMod p)) := fun w =>
    (MulAut.congr Θ).symm (ggConjAut (ggGamma L hN).range (hwA w.1 w.2))
  have hWapp : ∀ (w : W) f, hW w f = Θ.symm (ggConjAut (ggGamma L hN).range (hwA w.1 w.2) (Θ f)) := by
    intro w f
    rw [show hW w = (MulAut.congr Θ).symm (ggConjAut (ggGamma L hN).range (hwA w.1 w.2)) from rfl,
      MulAut.congr_symm_apply]
    rfl
  let H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p))) := Subgroup.closure (Set.range hW)
  have hWH : ∀ w : W, hW w ∈ H := fun w => Subgroup.subset_closure ⟨w, rfl⟩
  have hconj : ∀ (w : W) (b : ↥Bs) (hwb : (w : G) * b * (w : G)⁻¹ ∈ Bs),
      φ ⟨(w : G) * b * (w : G)⁻¹, hwb⟩ = hW w (φ b) := by
    intro w b hwb
    rw [hWapp, hφ, hφ, MulEquiv.apply_symm_apply]
    congr 1
    apply Subtype.ext
    rw [ggConjAut_apply]
    exact ggGamma_conj L hN ⟨w, hWL w.2⟩ b hwb
  have hHsp : ∀ g ∈ H, SpCoord.IsSignedPerm ⇑g := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨w, rfl⟩ := hg
      exact hsp ⟨w, hWL w.2⟩ (hwA w.1 w.2)
    | one => exact SignedPermCount.isSignedPerm_one p k
    | mul g h _ _ hg hh => exact SignedPermCount.isSignedPerm_mul hg hh
    | inv g _ hg => exact SignedPermCount.isSignedPerm_inv hg
  have hwb : ∀ w ∈ W, ∀ b ∈ Bs, w * b * w⁻¹ ∈ Bs :=
    fun w hw b hb => (Subgroup.mem_normalizer_iff.mp (hWN hw) b).mp hb
  have hUBs : U ≤ Bs := by
    refine hgen.trans ((Subgroup.closure_le _).mpr ?_)
    rintro c ⟨w, hw, b, hb, rfl⟩
    exact Bs.mul_mem (Bs.inv_mem hb) (hwb w hw b hb)
  set M : Subgroup (Fin k → Multiplicative (ZMod p)) := (U.subgroupOf Bs).map φ with hM
  have hdispφ : ∀ (w : W) (b : ↥Bs) (h : (b : G)⁻¹ * ((w : G) * b * (w : G)⁻¹) ∈ Bs),
      φ ⟨(b : G)⁻¹ * ((w : G) * b * (w : G)⁻¹), h⟩ = (φ b)⁻¹ * hW w (φ b) := by
    intro w b h
    rw [← hconj w b (hwb w w.2 b b.2), ← map_inv, ← map_mul]
    rfl
  have hMle : M ≤ SpCoord.commMod H := by
    have key : ∀ c ∈ Subgroup.closure {c | ∃ w ∈ W, ∃ b ∈ Bs, c = b⁻¹ * (w * b * w⁻¹)},
        ∃ hc : c ∈ Bs, φ ⟨c, hc⟩ ∈ SpCoord.commMod H := by
      intro c hc
      induction hc using Subgroup.closure_induction with
      | mem c hc =>
        obtain ⟨w, hw, b, hb, rfl⟩ := hc
        refine ⟨Bs.mul_mem (Bs.inv_mem hb) (hwb w hw b hb), ?_⟩
        rw [hdispφ ⟨w, hw⟩ ⟨b, hb⟩]
        exact SpCoord.displacement_mem_commMod (hWH ⟨w, hw⟩) _
      | one =>
        refine ⟨Bs.one_mem, ?_⟩
        rw [show (⟨1, Bs.one_mem⟩ : ↥Bs) = 1 from rfl, map_one]
        exact Subgroup.one_mem _
      | mul a b _ _ ha hb =>
        obtain ⟨ha1, ha2⟩ := ha
        obtain ⟨hb1, hb2⟩ := hb
        refine ⟨Bs.mul_mem ha1 hb1, ?_⟩
        rw [show (⟨a * b, Bs.mul_mem ha1 hb1⟩ : ↥Bs) = ⟨a, ha1⟩ * ⟨b, hb1⟩ from rfl, map_mul]
        exact Subgroup.mul_mem _ ha2 hb2
      | inv a _ ha =>
        obtain ⟨ha1, ha2⟩ := ha
        refine ⟨Bs.inv_mem ha1, ?_⟩
        rw [show (⟨a⁻¹, Bs.inv_mem ha1⟩ : ↥Bs) = (⟨a, ha1⟩ : ↥Bs)⁻¹ from rfl, map_inv]
        exact Subgroup.inv_mem _ ha2
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨hc, hmem⟩ := key u (hgen (Subgroup.mem_subgroupOf.mp hu))
    exact hmem
  have hdispM : ∀ g ∈ H, ∀ f, f⁻¹ * g f ∈ M := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨w, rfl⟩ := hg
      intro f
      obtain ⟨b, rfl⟩ := hφsurj f
      have h1 : (b : G)⁻¹ * ((w : G) * b * (w : G)⁻¹) ∈ Bs :=
        Bs.mul_mem (Bs.inv_mem b.2) (hwb w w.2 b b.2)
      rw [← hdispφ w b h1]
      exact ⟨⟨_, h1⟩, hdisp w w.2 b b.2, rfl⟩
    | one =>
      intro f
      rw [MulAut.one_apply, inv_mul_cancel]
      exact M.one_mem
    | mul g h _ _ hg hh =>
      intro f
      have h2 := M.mul_mem (hh f) (hg (h f))
      rwa [mul_assoc, mul_inv_cancel_left, ← MulAut.mul_apply] at h2
    | inv g _ hg =>
      intro f
      have h2 := M.inv_mem (hg (g⁻¹ f))
      rwa [MulAut.apply_inv_self, mul_inv_rev, inv_inv] at h2
  have hCM : SpCoord.commMod H = M :=
    le_antisymm ((Subgroup.closure_le _).mpr (by
      rintro _ ⟨g, hg, f, rfl⟩
      exact hdispM g hg f)) hMle
  have hφinj : ∀ u : ↥Bs, (u : G) ∈ U → φ u = 1 → u = 1 := by
    intro u hu h1
    have h2 : ggGamma L hN u = 1 := by
      have h3 : (ggGamma L hN).rangeRestrict u = 1 := by
        have h4 : Θ.symm ((ggGamma L hN).rangeRestrict u) = Θ.symm 1 := by
          rw [map_one]
          exact h1
        exact Θ.symm.injective h4
      exact congrArg Subtype.val h3
    rw [ggGamma_eq_one_iff] at h2
    have hmem : (u : G) ∈ Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) := ⟨⟨u.2, hUL hu⟩, h2⟩
    rw [inf_center_eq_bot_of_isElemAbelian_of_not_dvd hp hBs hZL, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hcoord : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]
    congr 1
    exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)
  have hcardM : Nat.card M = Nat.card U := by
    have hinjr : Function.Injective (φ.comp (U.subgroupOf Bs).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro u hu
      rw [MonoidHom.mem_ker] at hu
      have := hφinj u (Subgroup.mem_subgroupOf.mp u.2) hu
      exact Subgroup.mem_bot.mpr (Subtype.ext this)
    have hMr : M = (φ.comp (U.subgroupOf Bs).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hMr, ← Nat.card_congr (MonoidHom.ofInjective hinjr).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUBs).toEquiv]
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hx1 : x ≠ 1 := hH.1.data_L.2.1
  have hxp : orderOf x = p := orderOf_eq_prime (hBs.2 x hxBs) hx1
  have hcardBs : Nat.card Bs = p ^ k * p := by
    have h := TableB.card_range_mul_card_ker (ggGamma L hN)
    have hkerG : (ggGamma L hN).ker = (Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
      ext b
      rw [MonoidHom.mem_ker, ggGamma_eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
    have hkercard : Nat.card (ggGamma L hN).ker = p := by
      rw [hkerG, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hker,
        Nat.card_zpowers, hxp]
    have hAcard : Nat.card (ggGamma L hN).range = p ^ k := by
      rw [← hcoord]
      exact (Nat.card_congr Θ.toEquiv).symm
    rw [← h, hkercard, hAcard]
  have hcard : Nat.card (SpCoord.commMod H) * p ^ 2 ≤ p ^ k := by
    rw [hCM, hcardM]
    rw [hcardBs, pow_succ] at hcodim
    have hpos : 0 < p := hp.pos
    have h5 : Nat.card U * p ^ 2 * p ≤ p ^ k * p := by
      calc Nat.card U * p ^ 2 * p = Nat.card U * p ^ 3 := by ring
        _ ≤ p ^ k * p := by simpa [pow_succ] using hcodim
    exact Nat.le_of_mul_le_mul_right h5 hpos
  have hirr' : ∀ M' : Subgroup (Fin k → Multiplicative (ZMod p)), M' ≤ SpCoord.commMod H →
      (∀ g ∈ H, ∀ m ∈ M', g m ∈ M') → M' = ⊥ ∨ M' = SpCoord.commMod H := by
    intro M' hM' hinvM'
    rw [hCM] at hM' ⊢
    set U' : Subgroup G := ((M'.comap φ) ⊓ U.subgroupOf Bs).map Bs.subtype with hU'
    have hU'U : U' ≤ U := by
      rintro _ ⟨u, hu, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hu.2
    have hU'W : ∀ w ∈ W, ∀ u ∈ U', w * u * w⁻¹ ∈ U' := by
      rintro w hw _ ⟨u, hu, rfl⟩
      have hwu : w * (u : G) * w⁻¹ ∈ Bs := hwb w hw u u.2
      refine ⟨⟨_, hwu⟩, ⟨?_, ?_⟩, rfl⟩
      · show φ ⟨w * (u : G) * w⁻¹, hwu⟩ ∈ M'
        rw [hconj ⟨w, hw⟩ u hwu]
        exact hinvM' _ (hWH ⟨w, hw⟩) _ hu.1
      · have hdu := hdisp w hw u u.2
        have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu.2
        have h2 := U.mul_mem huU hdu
        rw [mul_inv_cancel_left] at h2
        exact Subgroup.mem_subgroupOf.mpr h2
    rcases hirr U' hU'U hU'W with hbot | htop
    · left
      rw [eq_bot_iff]
      intro m hm
      obtain ⟨u, hu, rfl⟩ := hM' hm
      have h2 : (u : G) ∈ U' := ⟨u, ⟨hm, hu⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h2
      rw [show u = 1 from Subtype.ext h2, map_one]
      exact Subgroup.one_mem _
    · right
      refine le_antisymm hM' ?_
      rintro _ ⟨u, hu, rfl⟩
      have h2 : (u : G) ∈ U' := by
        rw [htop]
        exact Subgroup.mem_subgroupOf.mp hu
      obtain ⟨u', hu', hu'u⟩ := h2
      rw [show u = u' from Subtype.ext hu'u.symm]
      exact hu'.1
  obtain ⟨T, hTev, hTsupp⟩ := SpCoord.exists_even_support_of_irreducible hp hHsp hirr' hcard
  obtain ⟨n, hnL, hnN, hnx, hninv⟩ := hinv T hTev
  refine ⟨n, hnL, hnN, hnx, fun u hu => ?_⟩
  refine hninv u (hUBs hu) (hUL hu) fun i hi => ?_
  have hmem : φ ⟨u, hUBs hu⟩ ∈ SpCoord.commMod H :=
    hMle ⟨⟨u, hUBs hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  exact hTsupp _ hmem i hi

end CFSG.StandardType

end

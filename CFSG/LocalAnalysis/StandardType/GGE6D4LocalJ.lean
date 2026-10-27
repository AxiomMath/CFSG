module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDatumOfTor
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorJInputs
import CFSG.LocalAnalysis.StandardType.GGE6D4LocalDatum
import CFSG.LocalAnalysis.StandardType.GGE6D4LocalPos
import CFSG.LocalAnalysis.StandardType.GGResLeaf
import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepPos
import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected
import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbr

public section

namespace CFSG.StandardType.E6D4J

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem two_isUnit {m : ℕ} (hm : Odd m) : IsUnit (2 : ZMod m) := by
  have h := (ZMod.isUnit_iff_coprime 2 m).mpr (Nat.coprime_two_left.mpr hm)
  exact_mod_cast h

theorem cartanD4_ker {m : ℕ} (hm : Odd m) (a : Fin 4 → ZMod m)
    (h : ∀ j, ∑ k, (CartanMatrix.D 4 j k : ZMod m) * a k = 0) : a = 0 := by
  have e0 : (2 : ZMod m) * a 0 + -1 * a 1 + 0 * a 2 + 0 * a 3 = 0 := by
    simpa [Fin.sum_univ_four, CartanMatrix.D_four] using h 0
  have e1 : (-1 : ZMod m) * a 0 + 2 * a 1 + -1 * a 2 + -1 * a 3 = 0 := by
    simpa [Fin.sum_univ_four, CartanMatrix.D_four] using h 1
  have e2 : (0 : ZMod m) * a 0 + -1 * a 1 + 2 * a 2 + 0 * a 3 = 0 := by
    simpa [Fin.sum_univ_four, CartanMatrix.D_four] using h 2
  have e3 : (0 : ZMod m) * a 0 + -1 * a 1 + 0 * a 2 + 2 * a 3 = 0 := by
    simpa [Fin.sum_univ_four, CartanMatrix.D_four] using h 3
  have hu := two_isUnit hm
  have a0 : a 0 = 0 := hu.mul_right_eq_zero.mp (by linear_combination 2 * e0 + 2 * e1 + e2 + e3)
  have a1 : a 1 = 0 :=
    hu.mul_right_eq_zero.mp (by linear_combination 2 * e0 + 4 * e1 + 2 * e2 + 2 * e3)
  have a2 : a 2 = 0 := hu.mul_right_eq_zero.mp (by linear_combination e0 + 2 * e1 + 2 * e2 + e3)
  have a3 : a 3 = 0 := hu.mul_right_eq_zero.mp (by linear_combination e0 + 2 * e1 + e2 + 2 * e3)
  funext i
  fin_cases i
  · exact a0
  · exact a1
  · exact a2
  · exact a3

theorem eq_one_of_mem_cor_of_conj {m N : ℕ} {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (w : GGTorusTorWit m N L' A) (hw : w.Holds C M)
    (hC : ∀ a : Fin N → ZMod m, (∀ j, ∑ k, (C j k : ZMod m) * a k = 0) → a = 0)
    {t : L'} (ht : t ∈ ⨆ k, (w.cor k).range) (hc : MulAut.conj t = 1) : t = 1 := by
  obtain ⟨-, -, hcorT, hαmul, -, hcomm, -, hpair, -⟩ := hw
  let Φ : (Fin N → Multiplicative (ZMod m)) →* L' :=
    MonoidHom.noncommPiCoprod (fun k => w.cor k) (fun i j _ x y => hcomm i j x y)
  have hrange : Φ.range = ⨆ k, (w.cor k).range := MonoidHom.noncommPiCoprod_range _
  have hΦs : ∀ k y, Φ (Pi.mulSingle k y) = w.cor k y := fun k y =>
    MonoidHom.noncommPiCoprod_mulSingle (fun k => w.cor k) k y
  obtain ⟨a, rfl⟩ : t ∈ Φ.range := hrange ▸ ht
  have hmem : ∀ g, MulAut.conj (Φ g) ∈ w.T := by
    intro g
    have h1 : ⨆ k, (w.cor k).range ≤ w.T.comap (MulAut.conj : L' →* MulAut L') :=
      iSup_le fun k => by
        rintro _ ⟨ζ, rfl⟩
        exact hcorT k ζ
    exact h1 (hrange ▸ ⟨g, rfl⟩)
  have key : ∀ j, ∑ k, (C j k : ZMod m) * Multiplicative.toAdd (a k) = 0 := by
    intro j
    let β : (Fin N → Multiplicative (ZMod m)) →* Multiplicative (ZMod m) :=
      (ggTorAlphaHom w.T (w.α j) (hαmul j)).comp
        (((MulAut.conj : L' →* MulAut L').comp Φ).codRestrict w.T hmem)
    have hβ : ∀ g, β g = w.α j (MulAut.conj (Φ g)) := fun g => rfl
    have hβs : ∀ k y, β (Pi.mulSingle k y) = y ^ C j k := by
      intro k y
      rw [hβ, hΦs, hpair]
    have h1 : β a = 1 := by
      rw [hβ, hc]
      exact ggTor_alpha_one w.T (w.α j) (hαmul j)
    rw [← Finset.univ_prod_mulSingle a, map_prod] at h1
    simp only [hβs] at h1
    have h2 := congrArg Multiplicative.toAdd h1
    rw [toAdd_prod, toAdd_one] at h2
    simpa only [toAdd_zpow, zsmul_eq_mul] using h2
  have ha := hC _ key
  have h1 : a = 1 := funext fun k => toAdd_eq_zero.mp (congrFun ha k)
  rw [h1, map_one]


theorem row_cases {labJ labX : LargeEvenLabel} (hrow : ggRowTwoNode 3 labJ labX)
    (htag : labX.tag = .E6 ∨ labX.tag = .twE6) :
    ∃ n, labJ = ⟨.D, 4, n⟩ ∧ ((3 ∣ 2 ^ n - 1 ∧ labX = ⟨.E6, 0, n⟩) ∨
      (3 ∣ 2 ^ n + 1 ∧ labX = ⟨.twE6, 0, n⟩)) := by
  rcases hrow with ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨hJ, -, h3, hX⟩ | ⟨hJ, -, h3, hX⟩
  · subst hX
    rcases htag with h | h <;> simp at h
  · subst hX
    rcases htag with h | h <;> simp at h
  · exact ⟨labJ.n, hJ, Or.inl ⟨h3, hX⟩⟩
  · exact ⟨labJ.n, hJ, Or.inr ⟨h3, hX⟩⟩

theorem odd_and_dvd_ggTorMpm {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1) :
    Odd (ggTorMpm 3 ⟨.D, 4, n⟩) ∧ 3 ∣ ggTorMpm 3 ⟨.D, 4, n⟩ := by
  have hev : Even (2 ^ n) := (Nat.even_pow' (by omega)).mpr even_two
  have hq : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
  have hoddSub : Odd (2 ^ n - 1) := by
    obtain ⟨a, ha⟩ := hev
    exact ⟨a - 1, by omega⟩
  have hoddAdd : Odd (2 ^ n + 1) := hev.add_one
  unfold ggTorMpm
  dsimp only
  split_ifs with h
  · exact ⟨hoddSub, h⟩
  · exact ⟨hoddAdd, h3.resolve_left h⟩

theorem torData_J (hRig : GGLabelRigidInput) (hD : GGTBTorD) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K) (hInnJ : GGInnerDiagOn Bs J) {n : ℕ}
    (hJΛ : LargeEvenInLambda2 ⟨.D, 4, n⟩)
    (hJl : GGHasLabel ⟨.D, 4, n⟩ (↥J ⧸ Subgroup.center ↥J))
    (h3 : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1) :
    ∃ hN : Bs ≤ Subgroup.normalizer (J : Set G),
      GGTorusTorData (ggTorMpm 3 ⟨.D, 4, n⟩) 4 (CartanMatrix.D 4) (ggCoxeterMatrixD 4) ↥J
        (ggGamma J hN).range := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hrc : ((LargeEvenLabel.mk .D 4 n).tag = .D ∧ (3 ∣ 2 ^ (LargeEvenLabel.mk .D 4 n).n - 1 ∨
      (3 ∣ 2 ^ (LargeEvenLabel.mk .D 4 n).n + 1 ∧ Even (LargeEvenLabel.mk .D 4 n).rank))) ∨
      ((LargeEvenLabel.mk .D 4 n).tag = .twD ∧ 3 ∣ 2 ^ (LargeEvenLabel.mk .D 4 n).n + 1 ∧
        Odd (LargeEvenLabel.mk .D 4 n).rank) := by
    refine Or.inl ⟨rfl, ?_⟩
    rcases h3 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, ⟨2, rfl⟩⟩
  have hW := hD 3 hp3 hp2 ⟨.D, 4, n⟩ hJΛ hrc
  have hL := hLift 3 ⟨.D, 4, n⟩ _ _ _ _ _ hp3 hp2 hJΛ (GGTBTorRowAt.d hrc)
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have hJperf : commutator ↥J = ⊤ := hInnJ.1
  have hEnn : ggTorEnn 3 ⟨.D, 4, n⟩ ≤ 1 := by
    unfold ggTorEnn
    split_ifs <;> norm_num
  have h3c : 3 ^ 3 ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range := by
    obtain ⟨R, _, I, F, ⟨⟨θ⟩, hl⟩⟩ := largeEvenRawDatum_exists (hL _ hJl)
    have hr := GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hl
    have hle : 3 ≤ 4 - ggTorEnn 3 ⟨.D, 4, n⟩ := by omega
    exact le_trans (Nat.pow_le_pow_right (by norm_num) hle) hr
  have hTB : GGTorusTBAt 3 Bs J := by
    intro r R _ θ I hN hBsI hlift
    exact ggTorusTBGroup_of_marking hp3 hBs hSC hJperf θ hN hBsI
      (GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hlift) h3c
  exact ggTorData_of_hasLabel hRig hInnJ hTB hJΛ hJl hW hL

theorem inf_centralizer_eq_one_of_torData {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    {m : ℕ} (hm : Odd m) (h3m : 3 ∣ m) (hBs : IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hTor : GGTorusTorData m 4 (CartanMatrix.D 4) (ggCoxeterMatrixD 4) ↥J
      (ggGamma J hN).range) :
    ∀ b ∈ Bs ⊓ J, b ∈ Subgroup.centralizer (J : Set G) → b = 1 := by
  obtain ⟨w, hw⟩ := hTor
  intro b hb hbc
  obtain ⟨hbBs, hbJ⟩ := Subgroup.mem_inf.mp hb
  have hb3 : (⟨b, hbJ⟩ : ↥J) ^ 3 = 1 := Subtype.ext (by simpa using hBs.2 b hbBs)
  have hconj : MulAut.conj (⟨b, hbJ⟩ : ↥J) = 1 := by
    refine MulEquiv.ext fun l => Subtype.ext ?_
    show b * (l : G) * b⁻¹ = l
    rw [← Subgroup.mem_centralizer_iff.mp hbc (l : G) l.2, mul_inv_cancel_right]
  have hA : MulAut.conj (⟨b, hbJ⟩ : ↥J) ∈ (ggGamma J hN).range := by
    rw [hconj]
    exact one_mem _
  have hmem := w.mem_cor_of_conj_mem Nat.prime_three (by norm_num) hm h3m hw _ hb3 hA
  have h1 := eq_one_of_mem_cor_of_conj w hw (cartanD4_ker hm) hmem hconj
  simpa using congrArg Subtype.val h1

theorem clauses_of_torData {G : Type} [Group G] [Finite G] {B Bs J : Subgroup G} {m : ℕ}
    (hm : Odd m) (h3m : 3 ∣ m) (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hBBs : B ≤ Bs) (hidx : Nat.card Bs ≤ 3 * Nat.card B)
    (hD : Nat.card (B ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) = 3 ^ 2)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hTor : GGTorusTorData m 4 (CartanMatrix.D 4) (ggCoxeterMatrixD 4) ↥J
      (ggGamma J hN).range) :
    (Nat.card Bs = 3 ^ 6 ∨ Nat.card Bs = 3 ^ 7) ∧ Nat.card (Bs ⊓ J : Subgroup G) = 3 ^ 4 ∧
      GGReflGenerated 3 (ggAutomizer J Bs) ∧ Nat.card ↥(ggAutomizer J Bs) = 192 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hM : GGIsWeylMatrix (ggCoxeterMatrixD 4) :=
    Or.inl ⟨4, Equiv.refl _, by norm_num, Or.inr (Or.inr ⟨le_rfl,
      CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)⟩)⟩
  have hRG : GGReflGenerated 3 (ggAutomizer J Bs) := by
    obtain ⟨Λ, hΛf, hΛd, M, C, V, hVadd, hVmod, ι, φ, h, a, hM', hC', hlin, hrefl, hpair,
      ⟨f, hf⟩, hcl⟩ := ggResXDatum_of_torData hp2 hm h3m hM (ggIntCartan_D 4) hBs hSC hN hTor
    exact ggIndep_reflGenerated_of_closure hrefl hcl
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨hnk, hbk, -⟩ := ggTD_core hm h3m hBs hSC hN w hw
  obtain ⟨e, -⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have h192 : Nat.card ↥(ggAutomizer J Bs) = 192 := by
    rw [← Nat.card_congr e.toEquiv, OrthF3.card_coxeterD_eq 4 le_rfl]
    norm_num [Nat.factorial]
  have hAle : Nat.card (ggGamma J hN).range ≤ 3 ^ 4 :=
    ggTD_card_range_le_pow hm h3m hBs hSC hN w hw
  have hmul := NbrU63.card_range_ggGamma_mul_card_inf hN
  have hCc := E6D4Pos.card_inf_centralizer hBs hBBs hidx hD
  have hZ := inf_centralizer_eq_one_of_torData hm h3m hBs hN ⟨w, hw⟩
  have hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ) := hw.2.2.2.2.2.1
  have hEinj : Function.Injective (ggTorE h3m w.cor hcomm) := by
    rw [injective_iff_map_eq_one]
    intro f hf
    have hk := ggTor_ker Nat.prime_three hm.pos.ne' h3m w hw hcomm f (by rw [hf, map_one])
    have h0 := cartanD4_ker (⟨1, rfl⟩ : Odd 3) (fun k => Multiplicative.toAdd (f k)) hk
    exact funext fun k => toAdd_eq_zero.mp (congrFun h0 k)
  have hHcard : Nat.card ((ggTorE h3m w.cor hcomm).range.map J.subtype) = 3 ^ 4 := by
    rw [← Nat.card_congr ((ggTorE h3m w.cor hcomm).range.equivMapOfInjective J.subtype
      J.subtype_injective).toEquiv, ← Nat.card_congr (MonoidHom.ofInjective hEinj).toEquiv,
      Nat.card_fun, Nat.card_fin, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hHS : (ggTorE h3m w.cor hcomm).range.map J.subtype ≤ Bs ⊓ J := by
    rintro _ ⟨t, ⟨f, rfl⟩, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, (ggTorE h3m w.cor hcomm f).2⟩
    have hcl : Subgroup.closure (Set.range fun k => w.cor k (ggZetaP 3 m)) ≤
        Bs.comap J.subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      exact hbk k
    exact hcl (ggTorE_mem_closure h3m w.cor hcomm f)
  have hSge : 3 ^ 4 ≤ Nat.card (Bs ⊓ J : Subgroup G) := by
    rw [← hHcard]
    exact Subgroup.card_le_of_le hHS
  have hdisj : Disjoint (Bs ⊓ J) (Bs ⊓ Subgroup.centralizer (J : Set G)) := by
    rw [Subgroup.disjoint_def]
    intro b hbS hbC
    exact hZ b hbS (Subgroup.mem_inf.mp hbC).2
  have hnorm : Bs ⊓ Subgroup.centralizer (J : Set G) ≤
      Subgroup.normalizer ((Bs ⊓ J : Subgroup G) : Set G) := by
    intro c hc
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_inf] at hs
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 s hs.2
  have hsup := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj
  have hsupBs : Nat.card ((Bs ⊓ J) ⊔ (Bs ⊓ Subgroup.centralizer (J : Set G)) : Subgroup G) ≤
      Nat.card Bs := Subgroup.card_le_of_le (sup_le inf_le_left inf_le_left)
  have hCpos : 0 < Nat.card (Bs ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) := Nat.card_pos
  have hBsle : Nat.card Bs ≤
      3 ^ 4 * Nat.card (Bs ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) := by
    rw [← hmul]
    exact Nat.mul_le_mul_right _ hAle
  have hSle : Nat.card (Bs ⊓ J : Subgroup G) ≤ 3 ^ 4 := by
    refine Nat.le_of_mul_le_mul_right ?_ hCpos
    rw [← hsup]
    exact hsupBs.trans hBsle
  have hS : Nat.card (Bs ⊓ J : Subgroup G) = 3 ^ 4 := le_antisymm hSle hSge
  have hBs4 : Nat.card Bs =
      3 ^ 4 * Nat.card (Bs ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) := by
    refine le_antisymm hBsle ?_
    rw [← hS, ← hsup]
    exact hsupBs
  refine ⟨?_, hS, hRG, h192⟩
  rcases hCc with h | h
  · exact Or.inl (by rw [hBs4, h]; norm_num)
  · exact Or.inr (by rw [hBs4, h]; norm_num)

theorem ggE6D4TwoNodeLocalInput_of_rest (hRig : GGLabelRigidInput) (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) (hQ1 : GGBstarInnerDiagJInput)
    (hRest : GGE6D4TwoNodeLocalRest) : GGE6D4TwoNodeLocalInput := by
  intro G _ _ B Bs x L D J y K hH X z hXz labJ labX hJΛ hXΛ hJl hXl hrow htag
  obtain ⟨hX4, hside⟩ := hRest G B Bs x L D J y K hH X z hXz labJ labX hJΛ hXΛ hJl hXl hrow htag
  obtain ⟨-, hE6, -, -, -, hDt, -⟩ := hT
  obtain ⟨n, rfl, hcase⟩ := row_cases hrow htag
  have h3 : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hInnJ : GGInnerDiagOn Bs J := hQ1 G 3 B Bs x L D J hH.1 hH.2.2.1.1
  obtain ⟨hN, hTor⟩ := torData_J hRig hDt hLift hH hInnJ hJΛ hJl h3
  obtain ⟨hm, h3m⟩ := odd_and_dvd_ggTorMpm (n := n) hJΛ.1 h3
  have hDeq : D = B ⊓ Subgroup.centralizer (J : Set G) := hH.1.2.2.1.2.2.2.2.2.2
  have hDc : Nat.card (B ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) = 3 ^ 2 := by
    rw [← hDeq]
    exact hH.1.2.2.1.2.2.1
  obtain ⟨h1, h2, h3', h5⟩ := clauses_of_torData hm h3m hH.1.2.1.2.1 hH.1.2.1.2.2.2 hH.1.2.1.1
    hH.1.2.1.2.2.1 hDc hN hTor
  have hXD : GGResXDatumE6x 3 Bs X z := by
    rcases hcase with ⟨h, rfl⟩ | ⟨-, rfl⟩
    · refine E6D4Loc.ggResXDatumE6x_split hRig hE6 hLift hH hXz hXΛ hXl rfl ?_
      unfold ggTorM
      simpa using h
    · exact hX4 rfl
  exact ⟨h1, h2, h3', hXD, h5, hside⟩

end E6D4J

end CFSG.StandardType

end

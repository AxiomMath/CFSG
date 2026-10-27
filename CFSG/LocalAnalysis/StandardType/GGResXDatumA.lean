module

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGTDAutomizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupSymmetricFour
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThreePerm
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResXDatumA {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X : Subgroup G) (n : ℕ) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (e : Fin n ≃ Λ),
    M = (CoxeterMatrix.A n).reindex e ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧ (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
      (∃ f : M.Group ≃* ↥(ggAutomizer X Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ)

theorem GGResXDatumA.card_automizer {G : Type} [Group G] [Finite G]
    {p n : ℕ} [Fact p.Prime] {Bs X : Subgroup G} (hD : GGResXDatumA p Bs X n) :
    Nat.card (ggAutomizer X Bs) = (n + 1).factorial := by
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM,
    _, _, _, _, _, ⟨f, _⟩, _⟩ := hD
  have hc : Nat.card (ggAutomizer X Bs) = Nat.card M.Group :=
    (Nat.card_congr f.toEquiv).symm
  rw [hM, Nat.card_congr ((CoxeterMatrix.A n).reindexGroupEquiv e).toEquiv] at hc
  obtain ⟨fP, _⟩ := ggCoxeterA_mulEquivPerm n
  rw [Nat.card_congr fP.toEquiv, Nat.card_perm, Nat.card_fin] at hc
  exact hc

theorem GGResXDatumA.rank_unique {G : Type} [Group G] [Finite G]
    {p n m : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hD : GGResXDatumA p Bs X n) (hD' : GGResXDatumA p Bs X m) : n = m := by
  have hc : (n + 1).factorial = (m + 1).factorial :=
    hD.card_automizer.symm.trans hD'.card_automizer
  by_contra hne
  have hh : 1 < n + 1 ∨ 1 < m + 1 := by omega
  have he := (Nat.factorial_inj' hh).mp hc
  omega

theorem GGResXDatumA.mulEquiv_perm {G : Type} [Group G] [Finite G]
    {p n : ℕ} [Fact p.Prime] {Bs X : Subgroup G} (hD : GGResXDatumA p Bs X n) :
    Nonempty (ggAutomizer X Bs ≃* Equiv.Perm (Fin (n + 1))) := by
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM,
    _, _, _, _, _, ⟨f, _⟩, _⟩ := hD
  subst M
  obtain ⟨eP, _⟩ := ggCoxeterA_mulEquivPerm n
  exact ⟨f.symm.trans ((CoxeterMatrix.reindexGroupEquiv (CoxeterMatrix.A n) e).trans eP)⟩

theorem GGResXDatumA.gamma_injective {G : Type} [Group G] [Finite G]
    {p n : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hD : GGResXDatumA p Bs X n) (hn : 3 ≤ n) :
    Function.Injective (ggAutomizerGammaHom hN) := by
  classical
  have hp : p.Prime := Fact.out
  have hkerp := ggAutomizerGammaHom_ker_isPGroup hBs hN
  obtain ⟨e⟩ := hD.mulEquiv_perm
  apply (MonoidHom.ker_eq_bot_iff _).mp
  by_cases h4 : n = 3
  · subst n
    exact CFSG.GorensteinWalter.normal_pSubgroup_eq_bot_of_mulEquiv_perm_four
      ⟨e⟩ p hp (hp.odd_of_ne_two hp2) _ inferInstance hkerp
  · let Q := (ggAutomizerGammaHom hN).ker.map e.toMonoidHom
    have hQn : Q.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
    have hQp : IsPGroup p Q := hkerp.map e.toMonoidHom
    have hQle : Q ≤ CFSG.pCore p (Equiv.Perm (Fin (n + 1))) :=
      le_sSup (show Q ∈ CFSG.normalPSubgroups p (Equiv.Perm (Fin (n + 1))) from ⟨hQn, hQp⟩)
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.SymThree.pCore_perm_eq_bot
      (by omega : 5 ≤ n + 1) p] at hQle
    apply le_antisymm ?_ bot_le
    intro a ha
    have hmem : e a ∈ Q := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have he1 : e a = 1 := hQle hmem
    exact e.injective (by simpa using he1)

theorem GGResXDatumA.card_dvd_gamma {G : Type} [Group G] [Finite G]
    {p n : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hD : GGResXDatumA p Bs X n) (hn : 3 ≤ n) :
    Nat.card (ggAutomizer X Bs) ∣
      Nat.card (ggAutomizer (MulAut.conj : X →* MulAut X).range (ggGamma X hN).range) :=
  Subgroup.card_dvd_of_injective (ggAutomizerGammaHom hN)
    (hD.gamma_injective hp2 hBs hN hn)

theorem GGResXDatumA.prime_dvd_gamma_of_singular {G : Type} [Group G] [Finite G]
    {p n : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hD : GGResXDatumA p Bs X n) (hn : 3 ≤ n) (hpn : p ∣ n + 1) :
    p ∣ Nat.card (ggAutomizer (MulAut.conj : X →* MulAut X).range (ggGamma X hN).range) := by
  have hdiv := hD.card_dvd_gamma hp2 hBs hN hn
  rw [hD.card_automizer] at hdiv
  exact (hpn.trans (Nat.dvd_factorial (Nat.succ_pos n) le_rfl)).trans hdiv

theorem GGResXDatumA.prime_dvd_gamma {G : Type} [Group G] [Finite G]
    {p n ℓ : ℕ} [Fact p.Prime] (hℓ : ℓ.Prime) (hne : ℓ ≠ p)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hD : GGResXDatumA p Bs X n)
    (hbound : ℓ ≤ n + 1) :
    ℓ ∣ Nat.card (ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
      (ggGamma X hN).range) := by
  apply prime_dvd_ggAutomizer_dvd_gamma Fact.out hℓ hne hBs hN
  rw [hD.card_automizer]
  exact Nat.dvd_factorial hℓ.pos hbound

private theorem l05nTA_no_five_GL_three (k : ℕ) (hk : k ≤ 3) :
    ¬ 5 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin k) (ZMod 3)) := by
  interval_cases k <;> rw [Matrix.card_GL_field] <;> simp only [ZMod.card] <;> decide

theorem three_card_ge_of_five_dvd_aut {H : Type} [Group H] {A : Subgroup H} [Finite A]
    (hA : IsElemAbelian 3 A) (h5 : 5 ∣ Nat.card (MulAut A)) : 3 ^ 4 ≤ Nat.card A := by
  classical
  obtain ⟨V, iV, iM, ⟨ι⟩⟩ := exists_ggLinData hA
  have : Finite V := Finite.of_equiv (Additive A) ι.toEquiv
  have : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hcard : 3 ^ Module.finrank (ZMod 3) V = Nat.card A := by
    rw [FiniteField.pow_finrank_eq_natCard]
    exact (card_eq_of_ggLin ι).symm
  by_contra hbad
  have hk : Module.finrank (ZMod 3) V ≤ 3 := by
    by_contra hgt
    have hh : 3 ^ 4 ≤ 3 ^ Module.finrank (ZMod 3) V :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hcard] at hh
    exact hbad hh
  let b := Module.finBasis (ZMod 3) V
  let e : Matrix.GeneralLinearGroup (Fin (Module.finrank (ZMod 3) V)) (ZMod 3) ≃*
      (V ≃ₗ[ZMod 3] V) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) V)
  let ρ : MulAut A →* Matrix.GeneralLinearGroup (Fin (Module.finrank (ZMod 3) V)) (ZMod 3) :=
    e.symm.toMonoidHom.comp (ggLin (p := 3) ι)
  have hi : Function.Injective ρ := e.symm.injective.comp (ggLin_injective ι)
  exact l05nTA_no_five_GL_three _ hk
    (dvd_trans h5 (Subgroup.card_dvd_of_injective ρ hi))

theorem GGResXDatumA.three_image_card_ge {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} {n : ℕ} (hBs : IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hD : GGResXDatumA 3 Bs X n)
    (hn : 4 ≤ n) : 3 ^ 4 ≤ Nat.card (ggGamma X hN).range := by
  have h5 := hD.prime_dvd_gamma (by norm_num : Nat.Prime 5) (by norm_num : 5 ≠ 3)
    hBs hN (by omega : 5 ≤ n + 1)
  have hAp : IsElemAbelian 3 (ggGamma X hN).range := isElemAbelian_range
    (fun a b : Bs => hBs.1.is_comm.comm a b)
    (fun b : Bs => Subtype.ext (by simpa using hBs.2 b b.2)) (ggGamma X hN)
  exact three_card_ge_of_five_dvd_aut hAp
    (dvd_trans h5 (Subgroup.card_subgroup_dvd_card _))

private lemma l05nTA_coxeter_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M = M.reindex (Equiv.refl ι) := by
  apply CoxeterMatrix.ext
  ext i j
  rw [CoxeterMatrix.reindex_apply]
  simp

private lemma l05nTA_odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ]
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  exact ⟨2 ^ k - 1, by omega⟩

private lemma l05nTA_odd_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ]
  exact ⟨2 ^ k, by omega⟩

private lemma l05nTA_odd_ggTorM {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    Odd (ggTorM lab) := by
  unfold ggTorM
  split_ifs with h
  · exact l05nTA_odd_two_pow_add_one hlab.1
  · exact l05nTA_odd_two_pow_sub_one hlab.1

private lemma l05nTA_weyl_A {n : ℕ} (hn : 1 ≤ n) : GGIsWeylMatrix (CoxeterMatrix.A n) :=
  Or.inl ⟨n, Equiv.refl _, hn, Or.inl (l05nTA_coxeter_reindex_refl _)⟩

private theorem l05nTA_lin {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)} {Bs X : Subgroup G}
    (hm : Odd m) (hpm : p ∣ m) (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (w : GGTorusTorWit m N ↥X (ggGamma X hN).range) (hw : w.Holds C M)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) :
    ∃ (hnk : ∀ k, ((w.n k : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G))
      (hbk : ∀ k, ((w.cor k (ggZetaP p m) : ↥X) : G) ∈ Bs)
      (α : Fin N → Module.Dual (ZMod p) V),
      (∀ i v, ggLin (p := p) ι (ggTDρB X Bs (ggTDnH w hnk i)) v =
        v - α i v • ι (Additive.ofMul ⟨_, hbk i⟩)) ∧
      (∀ i j, α i (ι (Additive.ofMul ⟨_, hbk j⟩)) = (C i j : ZMod p)) := by
  obtain ⟨hnk, hbk, F, hFadd, hFφ, hFC, hF1, hFsep⟩ := ggTD_core hm hpm hBs hS hN w hw
  let f : Fin N → Additive ↥Bs →+ ZMod p := fun k =>
    AddMonoidHom.mk' (fun b => F k (Additive.toMul b)) (fun b b' => hFadd k _ _)
  let α : Fin N → Module.Dual (ZMod p) V := fun k =>
    ((f k).comp ι.symm.toAddMonoidHom).toZModLinearMap p
  have hα : ∀ k v, α k v = F k (Additive.toMul (ι.symm v)) := fun _ _ => rfl
  refine ⟨hnk, hbk, α, fun i v => ?_, fun i j => ?_⟩
  · rw [ggLin_apply]
    have hφb : ggTDρB X Bs (ggTDnH w hnk i) (Additive.toMul (ι.symm v)) =
        ((⟨_, hbk i⟩ : ↥Bs) ^ (F i (Additive.toMul (ι.symm v))).val)⁻¹ *
          Additive.toMul (ι.symm v) := by
      apply Subtype.ext
      rw [ggTDρB_apply]
      push_cast
      exact hFφ i _
    rw [hφb, ofMul_mul, ofMul_inv, ofMul_pow, map_add, map_neg, map_nsmul, ofMul_toMul,
      AddEquiv.apply_symm_apply, hα, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    abel
  · rw [hα, AddEquiv.symm_apply_apply, toMul_ofMul]
    exact hFC i j

private theorem l05nTA_datum_of_torData {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : Odd m) (hpm : p ∣ m) {C : Matrix (Fin N) (Fin N) ℤ} {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hM : GGIsWeylMatrix (CoxeterMatrix.A N)) (hMC : GGIntCartan (CoxeterMatrix.A N) C)
    (hTor : GGTorusTorData m N C (CoxeterMatrix.A N) ↥X (ggGamma X hN).range) :
    GGResXDatumA p Bs X N := by
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨V, hVadd, hVmod, hι⟩ :=
    exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  obtain ⟨hnk, hbk, α, hlin, hpair⟩ := l05nTA_lin hm hpm hBs hS hN w hw V ι
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hcl := ggTD_closure hN hw hp2 hBs hnk
  have hfx : ∀ i, α i (ι (Additive.ofMul (⟨_, hbk i⟩ : ↥Bs))) = 2 := by
    intro i
    rw [hpair i i, hMC.1 i]
    norm_num
  refine ⟨Fin N, inferInstance, inferInstance, CoxeterMatrix.A N, C, V, hVadd, hVmod, ι,
    (fun k => ggTDρB X Bs (ggTDnH w hnk k)),
    (fun k => ι (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs))), α, Equiv.refl _,
    l05nTA_coxeter_reindex_refl _, hM, hMC, hlin, ?_, hpair, ⟨e, he⟩, hcl⟩
  intro i
  exact ggIsReflection_of_eq_reflection hp2 ι (hfx i) (ggLin_eq_reflection ι (hfx i) (hlin i))

private theorem l05nTA_core_L (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel (fun p lab => (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧
      p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab) p Bs L) :
    ∃ (lab : LargeEvenLabel) (hN : Bs ≤ Subgroup.normalizer (L : Set G)),
      LargeEvenInLambda2 lab ∧ (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧
        p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab ∧
        GGTorusTorData (ggTorM lab) lab.rank (CartanMatrix.A lab.rank)
          (CoxeterMatrix.A lab.rank) ↥L (ggGamma L hN).range := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  obtain ⟨R₀, _instR₀, I₀, F₀, hQ0⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ0, hBody0⟩ := hQ0
  obtain ⟨hP, -, -⟩ := hBody0
  have hrow : GGTBTorRowAt p lab (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank
      (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) :=
    GGTBTorRowAt.aDep hP.1 (by omega) hP.2.2.1 hP.2.2.2 (by rintro ⟨-, h5, -⟩; omega)
  have hWl : LargeEvenLabelAll lab (fun R _ I _ =>
      GGTorusTorW p (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank
        (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) R I) :=
    hW p lab (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank (CartanMatrix.A lab.rank)
      (CoxeterMatrix.A lab.rank) hp hp2 hlab hrow
  have hLl : LargeEvenLabelAll lab (fun R _ _ _ =>
      GGTorusLift p (lab.rank - 1 - ggTorEnn p lab) R) :=
    hLift p lab (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank (CartanMatrix.A lab.rank)
      (CoxeterMatrix.A lab.rank) hp hp2 hlab hrow
  have hBoth := largeEvenLabelAll_and hWl hLl
  obtain ⟨R, _instR, I, F, hQ, hWtor, hlift⟩ := largeEvenRawDatum_exists (hBoth _ hraw)
  obtain ⟨-, -, θ, hP', hN, hBsI⟩ := hQ
  have hTB := ggTorusTBGroup_of_L hH.1 hperf θ hN
    (fun b hb => ggLAut_mem_of_induces L θ hN hBsI hb) hlift
  refine ⟨lab, hN, hlab, hP'.1, hP'.2.1, hP'.2.2.1, hP'.2.2.2, ?_⟩
  exact hWtor ↥L (ggQuotHom θ) (ggGamma L hN).range hTB

theorem ggResXDatumA_of_tbTor (hT : GGTBTorAll) (hLift : GGTBTorLiftRows) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel (fun p lab => (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧
      p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab) p Bs L) :
    ∃ n : ℕ, 6 ≤ n ∧ p ∣ n + 1 ∧ GGResXDatumA p Bs L n := by
  have hW : GGTBTorWRows := ggTBTorWRows_of_all hT
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  obtain ⟨lab, hN, hlab, _htag, hrank, hdvd, hdvdM, hTor⟩ := l05nTA_core_L hW hLift hH h
  exact ⟨lab.rank, hrank, hdvd,
    l05nTA_datum_of_torData hH.1.1.2.2.2.2.2.1.2.1 (l05nTA_odd_ggTorM hlab) hdvdM hBs hS hN
      (l05nTA_weyl_A (by omega)) (ggIntCartan_A lab.rank) hTor⟩

end CFSG.StandardType

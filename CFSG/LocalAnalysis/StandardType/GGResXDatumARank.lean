module

public import CFSG.LocalAnalysis.StandardType.GGResXDatumA
public import CFSG.LocalAnalysis.StandardType.GGResHdRoNarrowDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nAR_coxeter_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M = M.reindex (Equiv.refl ι) := by
  apply CoxeterMatrix.ext
  ext i j
  rw [CoxeterMatrix.reindex_apply]
  simp

private lemma l05nAR_odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ]
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  exact ⟨2 ^ k - 1, by omega⟩

private lemma l05nAR_odd_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ]
  exact ⟨2 ^ k, by omega⟩

private lemma l05nAR_odd_ggTorM {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    Odd (ggTorM lab) := by
  unfold ggTorM
  split_ifs with h
  · exact l05nAR_odd_two_pow_add_one hlab.1
  · exact l05nAR_odd_two_pow_sub_one hlab.1

private lemma l05nAR_weyl_A {n : ℕ} (hn : 1 ≤ n) : GGIsWeylMatrix (CoxeterMatrix.A n) :=
  Or.inl ⟨n, Equiv.refl _, hn, Or.inl (l05nAR_coxeter_reindex_refl _)⟩

private theorem l05nAR_lin {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
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

private theorem l05nAR_datum_of_torData {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
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
  obtain ⟨hnk, hbk, α, hlin, hpair⟩ := l05nAR_lin hm hpm hBs hS hN w hw V ι
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hcl := ggTD_closure hN hw hp2 hBs hnk
  have hfx : ∀ i, α i (ι (Additive.ofMul (⟨_, hbk i⟩ : ↥Bs))) = 2 := by
    intro i
    rw [hpair i i, hMC.1 i]
    norm_num
  refine ⟨Fin N, inferInstance, inferInstance, CoxeterMatrix.A N, C, V, hVadd, hVmod, ι,
    (fun k => ggTDρB X Bs (ggTDnH w hnk k)),
    (fun k => ι (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs))), α, Equiv.refl _,
    l05nAR_coxeter_reindex_refl _, hM, hMC, hlin, ?_, hpair, ⟨e, he⟩, hcl⟩
  intro i
  exact ggIsReflection_of_eq_reflection hp2 ι (hfx i) (ggLin_eq_reflection ι (hfx i) (hlin i))

theorem ggResXDatumA_core_L (hT : GGTBTorANarrow) (hLift : GGTBTorLiftADepRows) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel (fun p lab => (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧
      p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab) p Bs L) :
    ∃ (lab : LargeEvenLabel) (hN : Bs ≤ Subgroup.normalizer (L : Set G)),
      LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) ∧
        (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧
        p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab ∧
        GGTorusTorData (ggTorM lab) lab.rank (CartanMatrix.A lab.rank)
          (CoxeterMatrix.A lab.rank) ↥L (ggGamma L hN).range := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  have hHas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hraw
  obtain ⟨R₀, _instR₀, I₀, F₀, hQ0⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ0, hBody0⟩ := hQ0
  obtain ⟨hP, -, -⟩ := hBody0
  have hWl : LargeEvenLabelAll lab (fun R _ I _ =>
      GGTorusTorW p (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank
        (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) R I) :=
    hT p hp hp2 lab hlab hP.1 hP.2.1 hP.2.2.1 hP.2.2.2
  have hLl : LargeEvenLabelAll lab (fun R _ _ _ =>
      GGTorusLift p (lab.rank - 1 - ggTorEnn p lab) R) :=
    hLift p hp hp2 lab hlab hP.1 hP.2.1 hP.2.2.1 hP.2.2.2
  have hBoth := largeEvenLabelAll_and hWl hLl
  obtain ⟨R, _instR, I, F, hQ, hWtor, hlift⟩ := largeEvenRawDatum_exists (hBoth _ hraw)
  obtain ⟨-, -, θ, hP', hN, hBsI⟩ := hQ
  have hTB := ggTorusTBGroup_of_L hH.1 hperf θ hN
    (fun b hb => ggLAut_mem_of_induces L θ hN hBsI hb) hlift
  refine ⟨lab, hN, hlab, hHas, hP'.1, hP'.2.1, hP'.2.2.1, hP'.2.2.2, ?_⟩
  exact hWtor ↥L (ggQuotHom θ) (ggGamma L hN).range hTB

theorem ggResXDatumA_core_K (hT : GGTBTorANarrow) (hLift : GGTBTorLiftADepRows) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel (fun p lab => (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧
      p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab) p Bs K) :
    ∃ (lab : LargeEvenLabel) (hN : Bs ≤ Subgroup.normalizer (K : Set G)),
      LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧
        (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧
        p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab ∧
        GGTorusTorData (ggTorM lab) lab.rank (CartanMatrix.A lab.rank)
          (CoxeterMatrix.A lab.rank) ↥K (ggGamma K hN).range := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  have hHas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hraw
  obtain ⟨R₀, _instR₀, I₀, F₀, hQ0⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ0, hBody0⟩ := hQ0
  obtain ⟨hP, -, -⟩ := hBody0
  have hWl : LargeEvenLabelAll lab (fun R _ I _ =>
      GGTorusTorW p (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank
        (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) R I) :=
    hT p hp hp2 lab hlab hP.1 hP.2.1 hP.2.2.1 hP.2.2.2
  have hLl : LargeEvenLabelAll lab (fun R _ _ _ =>
      GGTorusLift p (lab.rank - 1 - ggTorEnn p lab) R) :=
    hLift p hp hp2 lab hlab hP.1 hP.2.1 hP.2.2.1 hP.2.2.2
  have hBoth := largeEvenLabelAll_and hWl hLl
  obtain ⟨R, _instR, I, F, hQ, hWtor, hlift⟩ := largeEvenRawDatum_exists (hBoth _ hraw)
  obtain ⟨-, -, θ, hP', hN, hBsI⟩ := hQ
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hTB := ggTorusTBGroup_of_nbr hH.1 hnb hperf θ hN
    (fun b hb => ggLAut_mem_of_induces K θ hN hBsI hb) hlift
  refine ⟨lab, hN, hlab, hHas, hP'.1, hP'.2.1, hP'.2.2.1, hP'.2.2.2, ?_⟩
  exact hWtor ↥K (ggQuotHom θ) (ggGamma K hN).range hTB


theorem ggResXDatumA_of_tbTorA_rank (hT : GGTBTorANarrow) (hLift : GGTBTorLiftADepRows) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel (fun p lab => (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧
      p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab) p Bs L) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) ∧
      (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab ∧
      GGResXDatumA p Bs L lab.rank := by
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  obtain ⟨lab, hN, hlab, hHas, htag, hrank, hdvd, hdvdM, hTor⟩ :=
    ggResXDatumA_core_L hT hLift hH h
  exact ⟨lab, hlab, hHas, htag, hrank, hdvd, hdvdM,
    l05nAR_datum_of_torData hH.1.1.2.2.2.2.2.1.2.1 (l05nAR_odd_ggTorM hlab) hdvdM hBs hS hN
      (l05nAR_weyl_A (by omega)) (ggIntCartan_A lab.rank) hTor⟩

theorem ggResXDatumA_of_tbTor_rank (hT : GGTBTorAll) (hLift : GGTBTorLiftRows) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel (fun p lab => (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧
      p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab) p Bs L) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) ∧
      (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab ∧
      GGResXDatumA p Bs L lab.rank := by
  exact ggResXDatumA_of_tbTorA_rank (ggTBTorANarrow_of_all hT) (ggTBTorLiftADepRows_of_rows hLift)
    hH h

theorem ggResXDatumA_of_tbTorA_rank_K (hT : GGTBTorANarrow) (hLift : GGTBTorLiftADepRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel (fun p lab => (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧
      p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab) p Bs K) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧
      (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab ∧
      GGResXDatumA p Bs K lab.rank := by
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  obtain ⟨lab, hN, hlab, hHas, htag, hrank, hdvd, hdvdM, hTor⟩ :=
    ggResXDatumA_core_K hT hLift hH h
  exact ⟨lab, hlab, hHas, htag, hrank, hdvd, hdvdM,
    l05nAR_datum_of_torData hH.1.1.2.2.2.2.2.1.2.1 (l05nAR_odd_ggTorM hlab) hdvdM hBs hS hN
      (l05nAR_weyl_A (by omega)) (ggIntCartan_A lab.rank) hTor⟩

theorem ggResXDatumA_of_tbTor_rank_K (hT : GGTBTorAll) (hLift : GGTBTorLiftRows) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel (fun p lab => (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧
      p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab) p Bs K) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧
      (lab.tag = .A ∨ lab.tag = .twA) ∧ 6 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧ p ∣ ggTorM lab ∧
      GGResXDatumA p Bs K lab.rank := by
  exact ggResXDatumA_of_tbTorA_rank_K (ggTBTorANarrow_of_all hT)
    (ggTBTorLiftADepRows_of_rows hLift) hH h

end CFSG.StandardType

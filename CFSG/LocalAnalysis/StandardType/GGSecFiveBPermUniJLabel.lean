module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrameClass
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniModelTwoCenter
import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA2
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrOfEnnola
import CFSG.LocalAnalysis.StandardType.GGSignedCoordReflGroup

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2

theorem GGInnerDiagOnLabel.exists_and_n_eq {G : Type} [Group G] {S : ℕ → LargeEvenLabel → Prop}
    {p : ℕ} {Bs L : Subgroup G} (h : GGInnerDiagOnLabel S p Bs L) :
    ∃ lab : LargeEvenLabel, S p lab ∧
      GGInnerDiagOnLabel (fun p lab' => S p lab' ∧ lab'.n = lab.n) p Bs L := by
  obtain ⟨hcommL, lab, hlab2, hrawlab⟩ := h
  obtain ⟨R, hGR, Ilab, Flab, -, -, θ, hPS, hBsN, hind⟩ :=
    largeEvenRawDatum_exists hrawlab
  refine ⟨lab, hPS, hcommL, lab, hlab2, ?_⟩
  refine largeEvenRawDatum_mono ?_ hrawlab
  rintro R _ I F ⟨hs, hna, θ, hPS', hBsN', hind'⟩
  exact ⟨hs, hna, θ, ⟨hPS', rfl⟩, hBsN', hind'⟩

theorem GGInnerDiagOnLabel.exists_n_eq_of_two_le {G : Type} [Group G]
    {S : ℕ → LargeEvenLabel → Prop} {p : ℕ} {Bs L : Subgroup G}
    (h : GGInnerDiagOnLabel (fun p lab => S p lab ∧ 2 ≤ lab.n) p Bs L) :
    ∃ f : ℕ, 2 ≤ f ∧ GGInnerDiagOnLabel (fun p lab => S p lab ∧ lab.n = f) p Bs L := by
  obtain ⟨lab, ⟨-, hf⟩, h'⟩ := h.exists_and_n_eq
  exact ⟨lab.n, hf, h'.mono' (fun lab' h => ⟨h.1.1, h.2⟩)⟩

theorem GGInnerDiagOnLabel.n_eq_one_of_le_one {G : Type} [Group G] {n p : ℕ}
    {Bs L : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n ≤ 1) p Bs L) :
    GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n = 1) p Bs L := by
  obtain ⟨lab, ⟨hU, hle⟩, h'⟩ := h.exists_and_n_eq
  have hU' : lab.tag = .twA ∧ lab.rank = n - 1 ∧ p ∣ 2 ^ lab.n + 1 := hU
  have h1 : lab.n = 1 := by
    rcases Nat.lt_or_ge lab.n 1 with h0 | h1
    · have h2 : p ∣ 2 := by simpa [show lab.n = 0 by omega] using hU'.2.2
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2) hp2
    · omega
  exact h'.mono' fun lab' h => ⟨h.1.1, h.2.trans h1⟩

private theorem blockRes_diagonal {K : Type} [Field K] {d : ℕ} (S : Finset (Fin d)) (c : K) :
    TableBUE.blockRes S (Matrix.diagonal (fun _ : Fin d => c)) =
      Matrix.diagonal (fun _ : Fin S.card => c) := by
  ext a b
  change (Matrix.diagonal (fun _ : Fin d => c)) (S.equivFin.symm a) (S.equivFin.symm b) =
    (Matrix.diagonal (fun _ : Fin S.card => c)) a b
  by_cases hab : a = b
  · subst b
    simp only [Matrix.diagonal_apply_eq]
  · have hne : ((S.equivFin.symm a : ↥S) : Fin d) ≠ S.equivFin.symm b :=
      fun h => hab (S.equivFin.symm.injective (Subtype.ext h))
    rw [Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hab]

theorem GGSecFiveBPermUniLFrame.ggHasLabel_map_blockSU {G : Type} [Group G] {p n f : ℕ}
    {K : Type} [Field K] [Finite K] {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
    {σ : ↥(unitarySU 2 f K n) →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 f K)
    (S : Finset (Fin n)) (hS : 3 ≤ S.card) (hSq : (S.card, 2 ^ f) ≠ (3, 2)) :
    GGHasLabel ⟨.twA, S.card - 1, f⟩
      (↥((TableBUE.blockSU (K := K) (n := f) S).map σ) ⧸
        Subgroup.center ↥((TableBUE.blockSU (K := K) (n := f) S).map σ)) := by
  let Y : Subgroup G := (TableBUE.blockSU (K := K) (n := f) S).map σ
  have hY : (σ.comp (TableBUE.blockExtSU S hK)).range = Y := by
    rw [MonoidHom.range_comp, TableBUE.range_blockExtSU]
  let ψ : ↥(unitarySU 2 f K S.card) →* ↥Y :=
    (σ.comp (TableBUE.blockExtSU S hK)).codRestrict Y fun g =>
      hY ▸ MonoidHom.mem_range.mpr ⟨g, rfl⟩
  have hsurj : Function.Surjective ψ := by
    intro y
    have hy : (y : G) ∈ (σ.comp (TableBUE.blockExtSU S hK)).range := by
      rw [hY]
      exact y.2
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hy
    exact ⟨g, Subtype.ext hg⟩
  have hker : ∀ g : ↥(unitarySU 2 f K S.card), ψ g = 1 →
      ∃ c : K, ((g : GL (Fin S.card) K) : Matrix (Fin S.card) (Fin S.card) K) =
        Matrix.diagonal (fun _ => c) := by
    intro g hg
    have hg' : σ (TableBUE.blockExtSU S hK g) = 1 := congrArg Subtype.val hg
    obtain ⟨c, hc⟩ := hF.2.1 _ hg'
    refine ⟨c, ?_⟩
    have hr := congrArg (TableBUE.blockRes S) hc
    rw [TableBUE.coe_blockExtSU, TableBUE.blockRes_blockExt, blockRes_diagonal] at hr
    exact hr
  exact ggHasLabel_of_unitaryModel (X := Y) ⟨hK, hsurj, hker⟩ hS hSq

private theorem mem_D_iff_const {G F : Type} [Group G] [Field F] {p n f : ℕ}
    {B Bs : Subgroup G} {L D J : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F n) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ} {I : Finset (Fin n)}
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hDB : D ≤ B) (hJeq : D = B ⊓ Subgroup.centralizer (J : Set G))
    (hJI : J = (TableBUE.blockSU (K := F) (n := f) I).map σ)
    (hconst : ∀ b : ↥Bs, (b : G) ∈ D → ∀ i ∈ I, ∀ j ∈ I, eta b i = eta b j)
    (hB : B = Bs ∨ (∃ a a' : Fin n, a ≠ a' ∧
      ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a')) ∧ ∀ i j : Fin n, i ≠ j →
        (∀ b : ↥Bs, (b : G) ∈ D → eta b i = eta b j) → i ∈ I ∧ j ∈ I) :
    ∀ b : ↥Bs, (b : G) ∈ D ↔ ∀ i ∈ I, ∀ j ∈ I, eta b i = eta b j := by
  intro b
  refine ⟨hconst b, fun h => ?_⟩
  rw [hJeq]
  refine ⟨?_, ?_⟩
  · rcases hB with hBeq | ⟨⟨a, a', haa', hroot⟩, hpair⟩
    · rw [hBeq]
      exact b.2
    · have hDa : ∀ d : ↥Bs, (d : G) ∈ D → eta d a = eta d a' :=
        fun d hd => (hroot d).mp (hDB hd)
      exact (hroot b).mpr (h a (hpair a a' haa' hDa).1 a' (hpair a a' haa' hDa).2)
  · rw [hJI]
    exact hLF.mem_centralizer_map_blockSU_of_const b h

private theorem class_card {G F : Type} [Group G] [Field F] {p n f : ℕ}
    {B Bs : Subgroup G} {L D J : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F n) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ} {I : Finset (Fin n)}
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hDB : D ≤ B) (hDBs : D ≤ Bs) (hJeq : D = B ⊓ Subgroup.centralizer (J : Set G))
    (hJI : J = (TableBUE.blockSU (K := F) (n := f) I).map σ)
    (hconst : ∀ b : ↥Bs, (b : G) ∈ D → ∀ i ∈ I, ∀ j ∈ I, eta b i = eta b j)
    (hB : B = Bs ∨ (∃ a a' : Fin n, a ≠ a' ∧
      ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a')) ∧ ∀ i j : Fin n, i ≠ j →
        (∀ b : ↥Bs, (b : G) ∈ D → eta b i = eta b j) → i ∈ I ∧ j ∈ I)
    (hI2 : 2 ≤ I.card) :
    Nat.card ↥D = p ^ (n - I.card + 1) := by
  have hDmem := mem_D_iff_const hLF hDB hJeq hJI hconst hB
  have hcardD : Nat.card ↥D = Nat.card {v : Fin n → Multiplicative (ZMod p) //
      ∀ i ∈ I, ∀ j ∈ I, v i = v j} := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun d => ⟨eta ⟨(d : G), hDBs d.2⟩, fun i hi j hj => ?_⟩
        invFun := fun v => ⟨((eta.symm v.1 : ↥Bs) : G), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · exact hconst ⟨(d : G), hDBs d.2⟩ d.2 i hi j hj
    · rw [hDmem]
      intro i hi j hj
      simpa only [MulEquiv.apply_symm_apply] using v.2 i hi j hj
    · intro d; apply Subtype.ext; simp
    · intro v; apply Subtype.ext; simp
  have hcardS : Nat.card {v : Fin n → Multiplicative (ZMod p) //
      ∀ i ∈ I, ∀ j ∈ I, v i = v j} = p ^ (n - I.card + 1) := by
    obtain ⟨a, haI⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
    have e : {v : Fin n → Multiplicative (ZMod p) // ∀ i ∈ I, ∀ j ∈ I, v i = v j} ≃
        {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ aPermutationOn n p I, u f = f} :=
      Equiv.subtypeEquivRight fun f => (forall_aPermutationOn_fix_iff I f).symm
    rw [Nat.card_congr e]
    exact card_fix_aPermutationOn ⟨a, haI⟩
  rw [hcardD, hcardS]

private theorem class_erase {G : Type} [Group G] {p n : ℕ} {D : Subgroup G} {I : Finset (Fin n)}
    (hp : p.Prime) (hDcard : Nat.card ↥D = p ^ 2)
    (hcard : Nat.card ↥D = p ^ (n - I.card + 1)) : ∃ k : Fin n, I = Finset.univ.erase k := by
  have hk2 : n - I.card + 1 = 2 := by
    have h1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (le_of_eq (hcard.symm.trans hDcard))
    have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (le_of_eq (hDcard.symm.trans hcard))
    omega
  have hIcard : I.card = n - 1 := by
    have hle : I.card ≤ n := by simpa using Finset.card_le_univ I
    omega
  have hkI : ∃ k : Fin n, k ∉ I := by
    by_contra h
    push Not at h
    have hle := Finset.card_le_card (s := Finset.univ) (t := I) fun t _ => h t
    rw [Finset.card_univ, Fintype.card_fin] at hle
    omega
  obtain ⟨k, hk⟩ := hkI
  refine ⟨k, ?_⟩
  have hsub : I ⊆ Finset.univ.erase k := fun t ht =>
    Finset.mem_erase.mpr ⟨fun h => hk (h ▸ ht), Finset.mem_univ t⟩
  have hcard' : (Finset.univ.erase k).card ≤ I.card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    omega
  exact Finset.eq_of_subset_of_card_le hsub hcard'

private theorem exists_class_data {G F : Type} [Group G] [Finite G] [Field F] [Finite F]
    [CharP F 2] {p n f : ℕ}
    {Bs : Subgroup G} {L D J : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f F n) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ}
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hfield : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F)
    (hf : 2 ≤ f) (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    (hDBs : D ≤ Bs)
    (hJc : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)))
    (hJL : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G))) :
    ∃ I : Finset (Fin n), 2 ≤ I.card ∧ J = (TableBUE.blockSU (K := F) (n := f) I).map σ ∧
      (∀ b : ↥Bs, (b : G) ∈ D → ∀ i ∈ I, ∀ j ∈ I, eta b i = eta b j) ∧
      (∀ i j : Fin n, i ≠ j →
        (∀ b : ↥Bs, (b : G) ∈ D → eta b i = eta b j) → i ∈ I ∧ j ∈ I) := by
  obtain ⟨I, hI2, hJI, hIconst, hIpair⟩ :=
    hLF.exists_eq_map_blockSU_of_layer (K := F) (f := f)
      hfield hf hp hpq hDBs hJc hJL
  refine ⟨I, hI2, hJI, ?_, ?_⟩
  · intro b hb i hi j hj
    have hbeq : (⟨(b : G), hDBs hb⟩ : ↥Bs) = b := Subtype.ext rfl
    have h := hIconst (b : G) hb i hi j hj
    rwa [hbeq] at h
  · intro i j hij h
    exact hIpair i j hij fun d hd => h ⟨d, hDBs hd⟩ hd

private theorem exists_class_data_one {G F : Type} [Group G] [Finite G] [Field F] [Finite F]
    [CharP F 2] {p n : ℕ}
    {Bs : Subgroup G} {L D J : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {σ : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F n) →* G}
    {χ : Multiplicative (ZMod p) →* Fˣ}
    (hLF : GGSecFiveBPermUniLFrame Bs L eta 1 σ χ)
    (hfield : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F)
    (hp : p.Prime) (hpq : p ∣ 2 ^ 1 + 1)
    (hDBs : D ≤ Bs)
    (hJc : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)))
    (hJL : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G))) :
    ∃ I : Finset (Fin n), 4 ≤ I.card ∧ J = (TableBUE.blockSU (K := F) (n := 1) I).map σ ∧
      (∀ b : ↥Bs, (b : G) ∈ D → ∀ i ∈ I, ∀ j ∈ I, eta b i = eta b j) := by
  obtain ⟨I, hI4, hJI, hIconst, -⟩ :=
    hLF.exists_eq_map_blockSU_of_layer_two (K := F) hfield hp hpq hDBs hJc hJL
  refine ⟨I, hI4, hJI, ?_⟩
  intro b hb i hi j hj
  have hbeq : (⟨(b : G), hDBs hb⟩ : ↥Bs) = b := Subtype.ext rfl
  have h := hIconst (b : G) hb i hi j hj
  rwa [hbeq] at h

variable {G : Type} [Group G] [Finite G] {p n f : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}

private theorem exists_uniLFrame_core
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hn : 4 ≤ n)
    (hz : f = 1 → Line63.H5.twoCenter L = ⊥)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hL : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n = f) p Bs L)
    (hB : B = Bs ∨ ∃ a a' : Fin n, a ≠ a' ∧ ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a'))
    (hB1 : f = 1 → B = Bs) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (σ : ↥(unitarySU 2 f F n) →* G) (χ : Multiplicative (ZMod p) →* Fˣ) (k : Fin n),
      UnitaryFieldData 2 f F ∧ p ∣ 2 ^ f + 1 ∧ GGSecFiveBPermUniLFrame Bs L eta 1 σ χ ∧
      J = (TableBUE.blockSU (K := F) (n := f) (Finset.univ.erase k)).map σ ∧
      (∀ b : ↥Bs, ((b : G) ∈ D ↔ ∀ i j : Fin n, i ≠ k → j ≠ k → eta b i = eta b j)) ∧
      (f = 1 → 5 ≤ n) := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  obtain ⟨hpq, F, hFld, hFin, hChar, hN, φ, hFcard, hM, hdiag⟩ :=
    exists_unitary_model_of_uniLabel_of_twoCenter hR hn hz hL
  obtain ⟨-, hBsE, -, -, -⟩ := hR.1.1.tableB_facts
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  obtain ⟨σ, χ, hLF⟩ := exists_uniLFrame_of_model hp hp2 hBsE hBsC
    hR.1.1.card_bstar_inf_centralizer_L.le hn eta hLA hN φ hM hdiag 1
  have hDB : D ≤ B := hR.1.1.2.2.1.1
  have hDBs : D ≤ Bs := hDB.trans hR.1.1.2.1.1
  obtain ⟨I, hI2, hJI, hconst, hBp, hI4⟩ : ∃ I : Finset (Fin n), 2 ≤ I.card ∧
      J = (TableBUE.blockSU (K := F) (n := f) I).map σ ∧
      (∀ b : ↥Bs, (b : G) ∈ D → ∀ i ∈ I, ∀ j ∈ I, eta b i = eta b j) ∧
      (B = Bs ∨ (∃ a a' : Fin n, a ≠ a' ∧ ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a')) ∧
        ∀ i j : Fin n, i ≠ j → (∀ b : ↥Bs, (b : G) ∈ D → eta b i = eta b j) →
          i ∈ I ∧ j ∈ I) ∧ (f = 1 → 4 ≤ I.card) := by
    rcases Nat.lt_or_ge f 2 with hf | hf
    · obtain rfl | rfl : f = 0 ∨ f = 1 := by omega
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by simpa using hpq)) hp2
      · obtain ⟨I, hI4, hJI, hconst⟩ := exists_class_data_one hLF hM.field hp hpq hDBs
          hR.1.1.2.2.1.2.2.2.2.2.1 hR.1.1.2.2.1.2.2.2.2.1
        exact ⟨I, by omega, hJI, hconst, Or.inl (hB1 rfl), fun _ => hI4⟩
    · obtain ⟨I, hI2, hJI, hconst, hpair⟩ := exists_class_data hLF hM.field hf hp hpq hDBs
        hR.1.1.2.2.1.2.2.2.2.2.1 hR.1.1.2.2.1.2.2.2.2.1
      exact ⟨I, hI2, hJI, hconst, hB.imp id fun h => ⟨h, hpair⟩, fun h => by omega⟩
  have hJeq : D = B ⊓ Subgroup.centralizer (J : Set G) :=
    hR.1.1.2.2.1.2.2.2.2.2.2
  have hcardD : Nat.card ↥D = p ^ 2 := hR.1.1.2.2.1.2.2.1
  have hcard : Nat.card ↥D = p ^ (n - I.card + 1) :=
    class_card hLF hDB hDBs hJeq hJI hconst hBp hI2
  obtain ⟨k, hIerase⟩ := class_erase (D := D) hp hcardD hcard
  have hJ : J = (TableBUE.blockSU (K := F) (n := f) (Finset.univ.erase k)).map σ := by
    rw [hJI, hIerase]
  refine ⟨F, hFld, hFin, hChar, σ, χ, k, hM.field, hpq, hLF, hJ, fun b => ?_, fun h1 => ?_⟩
  · have hmem := mem_D_iff_const (I := I) hLF hDB hJeq hJI hconst hBp b
    rw [hIerase] at hmem
    constructor
    · intro hb i j hi hj
      exact hmem.mp hb i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
        j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
    · intro h
      exact hmem.mpr fun i hi j hj =>
        h i j (Finset.mem_erase.mp hi).1 (Finset.mem_erase.mp hj).1
  · have h4 := hI4 h1
    rw [hIerase, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
      Fintype.card_fin] at h4
    omega

theorem GGSecFiveRouteCfg.ggHasLabel_J_of_uniLabel
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hn : 4 ≤ n)
    (hz : f = 1 → Line63.H5.twoCenter L = ⊥)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (hL : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n = f) p Bs L)
    (hB : B = Bs ∨ ∃ a a' : Fin n, a ≠ a' ∧ ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b a = eta b a'))
    (hB1 : f = 1 → B = Bs) :
    GGHasLabel ⟨.twA, n - 2, f⟩ (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨F, hFld, hFin, hChar, σ, χ, k, hK, hpq, hLF, hJ, -, hn5⟩ :=
    exists_uniLFrame_core hR hn hz eta hLA hL hB hB1
  let S : Finset (Fin n) := Finset.univ.erase k
  have hScard : S.card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  have hS : 3 ≤ S.card := by omega
  have hSq : (S.card, 2 ^ f) ≠ (3, 2) := by
    intro h
    have h3 : S.card = 3 := congrArg Prod.fst h
    have h2 : 2 ^ f = 2 := congrArg Prod.snd h
    have h2' : 2 ^ f = 2 ^ 1 := by simpa using h2
    have hf1 : f = 1 := Nat.pow_right_injective (by norm_num : 1 < 2) h2'
    have := hn5 hf1
    omega
  have hlab := GGSecFiveBPermUniLFrame.ggHasLabel_map_blockSU (S := S) hLF hK hS hSq
  have hcard : S.card - 1 = n - 2 := by omega
  have hlabel : (⟨.twA, S.card - 1, f⟩ : LargeEvenLabel) = ⟨.twA, n - 2, f⟩ := by
    rw [hcard]
  rw [hJ]
  exact hlabel ▸ hlab

end CFSG.StandardType

end

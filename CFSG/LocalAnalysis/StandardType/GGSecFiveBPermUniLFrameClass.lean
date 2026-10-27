module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
public import CFSG.Assembly.LargeEvenDefs
import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUComp
import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock
import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2

variable {G : Type} [Group G] {p n f : ℕ} {K : Type} [Field K] {Bs X : Subgroup G}
  {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
  {σ : ↥(unitarySU 2 f K n) →* G} {χ : Multiplicative (ZMod p) →* Kˣ}

private theorem GGSecFiveBPermUniLFrame.suPairs_diagHom
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (b : ↥Bs) :
    ((b : G), diagHom n (fun k => χ (eta b (π k)))) ∈ SUTorus.suPairs σ := by
  obtain ⟨D, hD, hDm, hconj⟩ := hF.2.2.2 b
  let d : Fin n → Kˣ := fun k => χ (eta b (π k))
  have hD_eq : D = diagHom n d := by
    apply Units.ext
    rw [hDm, coe_diagHom]
  refine SUTorus.mem_suPairs.mpr ⟨?_, ?_⟩
  · rw [← hD_eq]
    exact hD
  · intro u v hv
    have hv' : (v : GL (Fin n) K) = D * u * D⁻¹ := by
      rw [hv, ← hD_eq]
    have hcv : LineU.conjN D hD u = v := by
      apply Subtype.ext
      rw [LineU.coe_conjN]
      exact hv'.symm
    rw [hconj u, hcv]

private theorem GGSecFiveBPermUniLFrame.ker_le_center
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) :
    σ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n) := by
  intro g hg
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨c, hc⟩ := hF.2.1 g (MonoidHom.mem_ker.mp hg)
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hc]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact mul_comm _ _

private theorem GGSecFiveBPermUniLFrame.blockSU_eq_bot_of_card_le_one
    {d n : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 n K)
    {I : Finset (Fin d)} (hI : I.card ≤ 1) :
    TableBUE.blockSU (K := K) (n := n) I = ⊥ := by
  rcases Nat.eq_zero_or_pos I.card with h0 | hpos
  · rw [Finset.card_eq_zero.mp h0, Subgroup.eq_bot_iff_forall]
    intro x hx
    have hM := TableBUE.mem_blockSU.mp hx
    apply Subtype.ext
    apply Units.ext
    ext a b
    simpa using hM a b (Or.inl (by simp))
  · have h1 : I.card = 1 := by omega
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    exact SUTorus.blockSU_singleton hK i

private theorem GGSecFiveBPermUniLFrame.two_le_card_diagClass
    (hK : UnitaryFieldData 2 f K) {m : ℕ}
    {ψ : ↥(unitarySU 2 f K (m + 1)) →* G} {S : Set G}
    {δ : G → Fin (m + 1) → Kˣ} {i : Fin (m + 1)} {J : Subgroup G}
    (hJq : CFSG.Assembly.IsQuasisimple ↥J)
    (hiJ : J ≤ (TableBUE.blockSU (K := K) (n := f)
      (LinTorus.diagClass S δ i)).map ψ) :
    2 ≤ (LinTorus.diagClass S δ i).card := by
  by_contra hlt
  have hcard : (LinTorus.diagClass S δ i).card ≤ 1 := by omega
  have hbot : (TableBUE.blockSU (K := K) (n := f)
      (LinTorus.diagClass S δ i)).map ψ = ⊥ := by
    rw [GGSecFiveBPermUniLFrame.blockSU_eq_bot_of_card_le_one hK hcard, Subgroup.map_bot]
  have hJbot : J = ⊥ := le_bot_iff.mp (hiJ.trans (le_of_eq hbot))
  haveI : Subsingleton ↥J := by
    rw [hJbot]
    exact ⟨fun x y => Subtype.ext (by
      rw [Subgroup.mem_bot.mp x.2, Subgroup.mem_bot.mp y.2])⟩
  haveI : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hJq.2.toNontrivial
  haveI : Subsingleton (↥J ⧸ Subgroup.center ↥J) := inferInstance
  exact not_subsingleton _ ‹Subsingleton (↥J ⧸ Subgroup.center ↥J)›

private theorem diagClass_eq_of_inter_nonempty {F : Type} [Field F] {G : Type} [Group G]
    {m : ℕ} {S : Set G} {δ : G → Fin (m + 1) → Fˣ} {i j : Fin (m + 1)}
    (h : (LinTorus.diagClass S δ i ∩ LinTorus.diagClass S δ j).Nonempty) :
    LinTorus.diagClass S δ i = LinTorus.diagClass S δ j := by
  obtain ⟨k, hk⟩ := h
  have hk1 : k ∈ LinTorus.diagClass S δ i := (Finset.mem_inter.mp hk).1
  have hk2 : k ∈ LinTorus.diagClass S δ j := (Finset.mem_inter.mp hk).2
  ext l
  rw [LinTorus.mem_diagClass, LinTorus.mem_diagClass]
  constructor
  · intro hl e he
    calc δ e l = δ e i := hl e he
      _ = δ e k := (LinTorus.mem_diagClass.mp hk1 e he).symm
      _ = δ e j := LinTorus.mem_diagClass.mp hk2 e he
  · intro hl e he
    calc δ e l = δ e j := hl e he
      _ = δ e k := (LinTorus.mem_diagClass.mp hk2 e he).symm
      _ = δ e i := LinTorus.mem_diagClass.mp hk1 e he

private theorem GGSecFiveBPermUniLFrame.blockSU_diagClass_le_of_layer
    {m : ℕ} {ψ : ↥(unitarySU 2 f K (m + 1)) →* G} {S : Set G}
    {δ : G → Fin (m + 1) → Kˣ} {J : Subgroup G}
    (hK : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)))
    (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs ψ)
    (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer S))
    (hJL : J = LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer S))
    {i : Fin (m + 1)} (h2 : 2 ≤ (LinTorus.diagClass S δ i).card) :
    (TableBUE.blockSU (K := K) (n := f) (LinTorus.diagClass S δ i)).map ψ ≤ J := by
  have hsub := SUTorus.isSubnormal_map_blockSU (ψ := ψ) hker hδ i
  have hq := SURepair.isQuasisimple_map_blockSU_of_two_le (ψ := ψ) hK hf hker h2
  have hcomp : IsComponentOf ((TableBUE.blockSU (K := K) (n := f)
      (LinTorus.diagClass S δ i)).map ψ) (ψ.range ⊓ Subgroup.centralizer S) :=
    ⟨hsub.le, hsub, hq⟩
  have hle : (TableBUE.blockSU (K := K) (n := f)
      (LinTorus.diagClass S δ i)).map ψ ≤
      LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer S) := le_sSup hcomp
  rwa [← hJL] at hle

private theorem GGSecFiveBPermUniLFrame.eq_map_blockSU_of_le_of_two_le
    {m : ℕ} {ψ : ↥(unitarySU 2 f K (m + 1)) →* G} {S : Set G}
    {δ : G → Fin (m + 1) → Kˣ} {J : Subgroup G}
    (hK : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)))
    (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs ψ)
    (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer S))
    (hJL : J = LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer S))
    {i : Fin (m + 1)}
    (hiJ : J ≤ (TableBUE.blockSU (K := K) (n := f) (LinTorus.diagClass S δ i)).map ψ)
    (h2 : 2 ≤ (LinTorus.diagClass S δ i).card) :
    J = (TableBUE.blockSU (K := K) (n := f) (LinTorus.diagClass S δ i)).map ψ :=
  le_antisymm hiJ (GGSecFiveBPermUniLFrame.blockSU_diagClass_le_of_layer
    (ψ := ψ) (S := S) (δ := δ) (J := J) hK hf hker hδ hJ hJL h2)

private theorem GGSecFiveBPermUniLFrame.not_disjoint_diagClass_of_layer
    {m : ℕ} {ψ : ↥(unitarySU 2 f K (m + 1)) →* G} {S : Set G}
    {δ : G → Fin (m + 1) → Kˣ} {J : Subgroup G}
    (hK : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)))
    (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs ψ)
    (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer S))
    (hJL : J = LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer S)) {i i₀ : Fin (m + 1)}
    (hJI : J = (TableBUE.blockSU (K := K) (n := f) (LinTorus.diagClass S δ i₀)).map ψ)
    (h2 : 2 ≤ (LinTorus.diagClass S δ i).card) :
    ¬ Disjoint (LinTorus.diagClass S δ i) (LinTorus.diagClass S δ i₀) := by
  intro hdisj
  have hYCJ := GGSecFiveBPermUniLFrame.blockSU_diagClass_le_of_layer
    (ψ := ψ) (S := S) (δ := δ) (J := J) hK hf hker hδ hJ hJL h2
  have hYCq := SURepair.isQuasisimple_map_blockSU_of_two_le (ψ := ψ)
    (S := LinTorus.diagClass S δ i) hK hf hker h2
  have hYCI : (TableBUE.blockSU (K := K) (n := f)
      (LinTorus.diagClass S δ i)).map ψ ≤
      (TableBUE.blockSU (K := K) (n := f)
        (LinTorus.diagClass S δ i₀)).map ψ :=
    hYCJ.trans (le_of_eq hJI)
  apply commutator_ne_bot_of_isQuasisimple hYCq
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (commute_map_blockSU_of_disjoint ψ hdisj x hx y (hYCI hy)).symm

private theorem GGSecFiveBPermUniLFrame.mem_of_forall_coord_eq
    {m : ℕ} {ψ : ↥(unitarySU 2 f K (m + 1)) →* G} {S : Set G}
    {δ : G → Fin (m + 1) → Kˣ} {J : Subgroup G}
    (hK : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)))
    (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs ψ)
    (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer S))
    (hJL : J = LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer S))
    {i₀ : Fin (m + 1)}
    (hJI : J = (TableBUE.blockSU (K := K) (n := f) (LinTorus.diagClass S δ i₀)).map ψ) :
    ∀ i j : Fin (m + 1), i ≠ j →
      (∀ (d : G) (hd : d ∈ S), δ d i = δ d j) →
        i ∈ LinTorus.diagClass S δ i₀ ∧ j ∈ LinTorus.diagClass S δ i₀ := by
  intro i j hij heta
  have hiC : i ∈ LinTorus.diagClass S δ i := LinTorus.self_mem_diagClass S δ i
  have hjC : j ∈ LinTorus.diagClass S δ i := by
    rw [LinTorus.mem_diagClass]
    intro d hd
    exact (heta d hd).symm
  have hC2 : 2 ≤ (LinTorus.diagClass S δ i).card := by
    have hsub : ({i, j} : Finset (Fin (m + 1))) ⊆ LinTorus.diagClass S δ i := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hiC
      · exact hjC
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair hij] at hcard
    omega
  have hiI : i ∈ LinTorus.diagClass S δ i₀ := by
    by_contra hiI
    have hdisj : Disjoint (LinTorus.diagClass S δ i) (LinTorus.diagClass S δ i₀) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      by_contra hne
      have hCI := diagClass_eq_of_inter_nonempty (Finset.nonempty_iff_ne_empty.mpr hne)
      exact hiI (hCI ▸ hiC)
    exact (GGSecFiveBPermUniLFrame.not_disjoint_diagClass_of_layer
      (ψ := ψ) (S := S) (δ := δ) (J := J) hK hf hker hδ hJ hJL hJI hC2) hdisj
  refine ⟨hiI, ?_⟩
  have hCI : LinTorus.diagClass S δ i = LinTorus.diagClass S δ i₀ :=
    diagClass_eq_of_inter_nonempty ⟨i, Finset.mem_inter.mpr ⟨hiC, hiI⟩⟩
  exact hCI ▸ hjC

private theorem GGSecFiveBPermUniLFrame.false_of_n_eq_zero
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) {D J : Subgroup G}
    (hJ : IsComponentOf J (X ⊓ Subgroup.centralizer (D : Set G))) (hn : n = 0) : False := by
  subst hn
  haveI : Subsingleton ↥(unitarySU 2 f K 0) :=
    ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i _ => Fin.elim0 i))⟩
  have hσ1 : σ = 1 := MonoidHom.ext fun g => by
    rw [MonoidHom.one_apply, show g = 1 from Subsingleton.elim g 1, map_one]
  have hX : X = ⊥ := hF.1.symm.trans (MonoidHom.range_eq_bot_iff.mpr hσ1)
  have hJbot : J = ⊥ := le_bot_iff.mp (by simpa [hX] using hJ.1)
  haveI : Subsingleton ↥J := by
    rw [hJbot]
    exact ⟨fun x y => Subtype.ext (by
      rw [Subgroup.mem_bot.mp x.2, Subgroup.mem_bot.mp y.2])⟩
  haveI : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2.toNontrivial
  haveI : Subsingleton (↥J ⧸ Subgroup.center ↥J) := inferInstance
  exact not_subsingleton _ ‹Subsingleton (↥J ⧸ Subgroup.center ↥J)›

theorem GGSecFiveBPermUniLFrame.mem_centralizer_map_blockSU_of_const
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) {I : Finset (Fin n)} (b : ↥Bs)
    (hb : ∀ i ∈ I, ∀ j ∈ I, eta b (π i) = eta b (π j)) :
    (b : G) ∈ Subgroup.centralizer
      (((TableBUE.blockSU (K := K) (n := f) I).map σ : Subgroup G) : Set G) := by
  classical
  cases n with
  | zero =>
    haveI : Subsingleton ↥(unitarySU 2 f K 0) :=
      ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i _ => Fin.elim0 i))⟩
    have hσ1 : σ = 1 := MonoidHom.ext fun g => by
      rw [MonoidHom.one_apply, show g = 1 from Subsingleton.elim g 1, map_one]
    have hX : σ.range = ⊥ := MonoidHom.range_eq_bot_iff.mpr hσ1
    have hbot : ((TableBUE.blockSU (K := K) (n := f) I).map σ : Subgroup G) = ⊥ :=
      le_bot_iff.mp ((Subgroup.map_le_range σ _).trans (le_of_eq hX))
    rw [hbot]
    simp [Subgroup.mem_centralizer_iff]
  | succ m =>
    exact SUTorus.mem_centralizer_map_blockSU (m := m) (ψ := σ)
      (d := fun k => χ (eta b (π k))) (hF.suPairs_diagHom b)
      (fun i hi j hj => congrArg χ (hb i hi j hj))

theorem GGSecFiveBPermUniLFrame.exists_eq_map_blockSU_of_layer [Finite G] [Finite K] [CharP K 2]
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1) {D J : Subgroup G} (hD : D ≤ Bs)
    (hJ : IsComponentOf J (X ⊓ Subgroup.centralizer (D : Set G)))
    (hJL : J = LargeEvenLayer (X ⊓ Subgroup.centralizer (D : Set G))) :
    ∃ I : Finset (Fin n), 2 ≤ I.card ∧ J = (TableBUE.blockSU (K := K) (n := f) I).map σ ∧
      (∀ (d : G) (hd : d ∈ D), ∀ i ∈ I, ∀ j ∈ I,
        eta ⟨d, hD hd⟩ (π i) = eta ⟨d, hD hd⟩ (π j)) ∧
      ∀ i j : Fin n, i ≠ j →
        (∀ (d : G) (hd : d ∈ D), eta ⟨d, hD hd⟩ (π i) = eta ⟨d, hD hd⟩ (π j)) →
          i ∈ I ∧ j ∈ I := by
  classical
  cases n with
  | zero => exact (hF.false_of_n_eq_zero hJ rfl).elim
  | succ m =>
    rw [← hF.1] at hJ hJL
    let δ : G → Fin (m + 1) → Kˣ :=
      fun e k => if h : e ∈ Bs then χ (eta ⟨e, h⟩ (π k)) else 1
    have hδ : ∀ e ∈ (D : Set G), (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs σ := by
      intro e he
      have heB : e ∈ Bs := hD he
      have h := hF.suPairs_diagHom (⟨e, heB⟩ : ↥Bs)
      simpa [δ, dif_pos heB] using h
    have hker : σ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)) := hF.ker_le_center
    obtain ⟨i, hiJ⟩ := SUTorus.exists_le_map_blockSU (ψ := σ) (m := m) hK hp hpq hker hδ hJ
    let I : Finset (Fin (m + 1)) := LinTorus.diagClass (D : Set G) δ i
    have hiJ' : J ≤ (TableBUE.blockSU (K := K) (n := f) I).map σ := by
      simpa [I] using hiJ
    have hI2 : 2 ≤ I.card :=
      GGSecFiveBPermUniLFrame.two_le_card_diagClass hK hJ.2.2 hiJ'
    have hJI : J = (TableBUE.blockSU (K := K) (n := f) I).map σ :=
      GGSecFiveBPermUniLFrame.eq_map_blockSU_of_le_of_two_le
        (ψ := σ) (S := (D : Set G)) (δ := δ) (J := J)
        (i := i) hK hf hker hδ hJ hJL (by simpa [I] using hiJ) hI2
    refine ⟨I, hI2, hJI, ?_, ?_⟩
    · intro d hd i' hi' j' hj'
      have hi : δ d i' = δ d i :=
        LinTorus.mem_diagClass.mp (by simpa [I] using hi') d hd
      have hj : δ d j' = δ d i :=
        LinTorus.mem_diagClass.mp (by simpa [I] using hj') d hd
      exact hF.2.2.1 (by simpa [δ, dif_pos (hD hd)] using hi.trans hj.symm)
    · intro i j hij heta
      have hδij : ∀ (d : G) (hd : d ∈ (D : Set G)), δ d i = δ d j := by
        intro d hd
        have h := congrArg χ (heta d hd)
        simpa [δ, dif_pos (hD hd)] using h
      exact GGSecFiveBPermUniLFrame.mem_of_forall_coord_eq
        (S := (D : Set G)) hK hf hker hδ hJ hJL (by simpa [I] using hJI) i j hij hδij

private theorem GGSecFiveBPermUniLFrame.diagHom_conj_permGL_matrix {F : Type} [Field F]
    {n : ℕ} (τ : Equiv.Perm (Fin n)) (d : Fin n → Fˣ) :
    (((diagHom n d * permGL τ * (diagHom n d)⁻¹ * (permGL τ)⁻¹) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun k => ((d k : F) * (((d (τ.symm k))⁻¹ : Fˣ) : F))) := by
  have h2 := permGL_mul_diagHom_mul_inv (K := F) τ (fun k => (d k)⁻¹)
  have hmain : (diagHom n d * permGL τ * (diagHom n d)⁻¹ * (permGL τ)⁻¹ : GL (Fin n) F) =
      diagHom n (fun k => d k * (d (τ.symm k))⁻¹) := by
    rw [← map_inv (diagHom (K := F) n) d]
    calc diagHom n d * permGL τ * diagHom n (fun k => (d k)⁻¹) * (permGL τ)⁻¹
        = diagHom n d * (permGL τ * diagHom n (fun k => (d k)⁻¹) * (permGL τ)⁻¹) := by
          group
      _ = diagHom n d * diagHom n ((fun k => (d k)⁻¹) ∘ τ.symm) := by rw [h2]
      _ = diagHom n (fun k => d k * (d (τ.symm k))⁻¹) := by
            rw [← map_mul]
            rfl
  rw [hmain, coe_diagHom]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]

private theorem GGSecFiveBPermUniLFrame.exists_scalar_diag_swap
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 f K)
    {S : Finset (Fin n)} (b : ↥Bs)
    (hb : (b : G) ∈ Subgroup.centralizer
      (((TableBUE.blockSU (K := K) (n := f) S).map σ : Subgroup G) : Set G))
    {i j : Fin n} (hi : i ∈ S) (hj : j ∈ S) :
    ∃ c : K, ∀ k : Fin n,
      ((χ (eta b (π k)) : K) *
        (((χ (eta b (π (Equiv.swap i j k))))⁻¹ : Kˣ) : K)) = c := by
  classical
  let d : Fin n → Kˣ := fun k => χ (eta b (π k))
  obtain ⟨D, hD, hDm, hconj⟩ := hF.2.2.2 b
  have hDmd : (D : Matrix (Fin n) (Fin n) K) = Matrix.diagonal (fun k => (d k : K)) := hDm
  have hD_eq : D = diagHom n d := by
    apply Units.ext
    rw [hDmd, coe_diagHom]
  let P : ↥(unitarySU 2 f K n) :=
    ⟨permGL (Equiv.swap i j), TableBUE.permGL_swap_mem hK i j⟩
  have hPblock : P ∈ TableBUE.blockSU (K := K) (n := f) S :=
    TableBUE.mem_blockSU.mpr (TableBUE.isBlockOn_permGL_swap hi hj)
  have hPmem : σ P ∈ (TableBUE.blockSU (K := K) (n := f) S).map σ :=
    Subgroup.mem_map.mpr ⟨P, hPblock, rfl⟩
  have hcomm : σ P * (b : G) = (b : G) * σ P :=
    Subgroup.mem_centralizer_iff.mp hb (σ P) hPmem
  have hfix : (b : G) * σ P * (b : G)⁻¹ = σ P := by
    rw [← hcomm]
    group
  have hσeq : σ (LineU.conjN D hD P) = σ P := by
    rw [← hconj P]
    exact hfix
  have hker1 : σ (LineU.conjN D hD P * P⁻¹) = 1 := by
    rw [map_mul, map_inv, hσeq, mul_inv_cancel]
  obtain ⟨c, hc'⟩ := hF.2.1 (LineU.conjN D hD P * P⁻¹) hker1
  refine ⟨c, fun k => ?_⟩
  have e1 : ((LineU.conjN D hD P * P⁻¹ : ↥(unitarySU 2 f K n)) : GL (Fin n) K) =
      diagHom n d * permGL (Equiv.swap i j) * (diagHom n d)⁻¹ *
        (permGL (Equiv.swap i j))⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, LineU.coe_conjN, hD_eq]
  have hmat : (((LineU.conjN D hD P * P⁻¹ : ↥(unitarySU 2 f K n)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun k => ((d k : K) * (((d (Equiv.swap i j k))⁻¹ : Kˣ) : K))) := by
    rw [e1]
    simpa [Equiv.symm_swap] using
      GGSecFiveBPermUniLFrame.diagHom_conj_permGL_matrix (Equiv.swap i j) d
  have h := congrFun (congrFun (hmat.symm.trans hc') k) k
  simpa [d] using h

private theorem GGSecFiveBPermUniLFrame.eq_of_scalar_diag_swap {d : Fin n → Kˣ}
    (hn : 3 ≤ n) {i j : Fin n}
    (hc : ∃ c : K, ∀ k : Fin n,
      ((d k : K) * (((d (Equiv.swap i j k))⁻¹ : Kˣ) : K)) = c) :
    d i = d j := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨k, hki, hkj⟩ := LineU.exists_not_mem_two hn i j
  have hc1 : c = 1 := by
    have h := hc k
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj] at h
    have h1 : ((d k : K) * (((d k)⁻¹ : Kˣ) : K)) = 1 := by
      rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero (d k))]
    rw [h1] at h
    exact h.symm
  have hdi : ((d i : K) * (((d j)⁻¹ : Kˣ) : K)) = 1 := by
    have h := hc i
    rw [Equiv.swap_apply_left, hc1] at h
    exact h
  apply Units.ext
  have h1 : (d i : K) * ((d j : K))⁻¹ = 1 := by
    simpa [Units.val_inv_eq_inv_val] using hdi
  exact (mul_inv_eq_one₀ (Units.ne_zero (d j))).mp h1

theorem GGSecFiveBPermUniLFrame.eq_of_mem_centralizer_map_blockSU
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (hK : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    {S : Finset (Fin n)} (b : ↥Bs)
    (hb : (b : G) ∈ Subgroup.centralizer
      (((TableBUE.blockSU (K := K) (n := f) S).map σ : Subgroup G) : Set G)) :
    ∀ i ∈ S, ∀ j ∈ S, eta b (π i) = eta b (π j) := by
  intro i hi j hj
  by_cases hij : i = j
  · rw [hij]
  exact hF.2.2.1 (GGSecFiveBPermUniLFrame.eq_of_scalar_diag_swap
    hn (GGSecFiveBPermUniLFrame.exists_scalar_diag_swap
      (S := S) hF hK b hb hi hj))

private theorem GGSecFiveBPermUniLFrame.four_le_card_diagClass_of_component_two
    (hK : UnitaryFieldData 2 1 K) {m : ℕ}
    {ψ : ↥(unitarySU 2 1 K (m + 1)) →* G} {S : Set G}
    {δ : G → Fin (m + 1) → Kˣ} {i : Fin (m + 1)} {J : Subgroup G}
    (hJq : CFSG.Assembly.IsQuasisimple ↥J)
    (hiJ : J ≤ (TableBUE.blockSU (K := K) (n := 1)
      (LinTorus.diagClass S δ i)).map ψ) :
    4 ≤ (LinTorus.diagClass S δ i).card := by
  by_contra hlt
  have h1 : 1 ≤ (LinTorus.diagClass S δ i).card :=
    Finset.card_pos.mpr ⟨i, LinTorus.self_mem_diagClass S δ i⟩
  have h3 : (LinTorus.diagClass S δ i).card ≤ 3 := by omega
  have hsolv : Group.IsSolvable ↥((TableBUE.blockSU (K := K) (n := 1)
      (LinTorus.diagClass S δ i)).map ψ) :=
    WitSU.isSolvable_map_blockSU_two_one hK ψ h1 h3
  have hsolvJ : Group.IsSolvable ↥J :=
    @Group.isSolvable_of_isSolvable_injective ↥J
      ↥((TableBUE.blockSU (K := K) (n := 1) (LinTorus.diagClass S δ i)).map ψ) _ _
      (Subgroup.inclusion hiJ) (Subgroup.inclusion_injective hiJ) hsolv
  exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).mp hJq)
    hsolvJ

private theorem GGSecFiveBPermUniLFrame.isComponentOf_map_blockSU_two
    {m : ℕ} {ψ : ↥(unitarySU 2 1 K (m + 1)) →* G} {S : Set G}
    {δ : G → Fin (m + 1) → Kˣ}
    (hK : UnitaryFieldData 2 1 K)
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 1 K (m + 1)))
    (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs ψ)
    {i : Fin (m + 1)} (h4 : 4 ≤ (LinTorus.diagClass S δ i).card) :
    IsComponentOf ((TableBUE.blockSU (K := K) (n := 1)
      (LinTorus.diagClass S δ i)).map ψ) (ψ.range ⊓ Subgroup.centralizer S) := by
  have hsub := SUTorus.isSubnormal_map_blockSU (ψ := ψ) hker hδ i
  have hq := SUTorus.isQuasisimple_map_blockSU (f := 1) (n := m + 1) hK hker
    (V := LinTorus.diagClass S δ i) (by omega) (by
      intro h
      have h3 : (LinTorus.diagClass S δ i).card = 3 := by
        simpa using congrArg Prod.fst h
      omega)
  exact ⟨hsub.le, hsub, hq⟩

private theorem GGSecFiveBPermUniLFrame.blockSU_diagClass_le_of_layer_two
    {m : ℕ} {ψ : ↥(unitarySU 2 1 K (m + 1)) →* G} {S : Set G}
    {δ : G → Fin (m + 1) → Kˣ} {J : Subgroup G}
    (hK : UnitaryFieldData 2 1 K)
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 1 K (m + 1)))
    (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs ψ)
    (hJL : J = LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer S))
    {i : Fin (m + 1)} (h4 : 4 ≤ (LinTorus.diagClass S δ i).card) :
    (TableBUE.blockSU (K := K) (n := 1) (LinTorus.diagClass S δ i)).map ψ ≤ J := by
  have hcomp := GGSecFiveBPermUniLFrame.isComponentOf_map_blockSU_two
    (ψ := ψ) (S := S) (δ := δ) hK hker hδ h4
  have hle : (TableBUE.blockSU (K := K) (n := 1) (LinTorus.diagClass S δ i)).map ψ ≤
      LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer S) := le_sSup hcomp
  rwa [← hJL] at hle

private theorem GGSecFiveBPermUniLFrame.eq_map_blockSU_of_le_of_layer_two
    {m : ℕ} {ψ : ↥(unitarySU 2 1 K (m + 1)) →* G} {S : Set G}
    {δ : G → Fin (m + 1) → Kˣ} {J : Subgroup G}
    (hK : UnitaryFieldData 2 1 K)
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 1 K (m + 1)))
    (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs ψ)
    (hJL : J = LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer S))
    {i : Fin (m + 1)}
    (hiJ : J ≤ (TableBUE.blockSU (K := K) (n := 1)
      (LinTorus.diagClass S δ i)).map ψ)
    (h4 : 4 ≤ (LinTorus.diagClass S δ i).card) :
    J = (TableBUE.blockSU (K := K) (n := 1) (LinTorus.diagClass S δ i)).map ψ :=
  le_antisymm hiJ (GGSecFiveBPermUniLFrame.blockSU_diagClass_le_of_layer_two
    (ψ := ψ) (S := S) (δ := δ) (J := J) hK hker hδ hJL h4)

theorem GGSecFiveBPermUniLFrame.exists_eq_map_blockSU_of_layer_two [Finite G] [Finite K]
    [CharP K 2] {σ₁ : ↥(unitarySU 2 1 K n) →* G}
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ₁ χ) (hK : UnitaryFieldData 2 1 K)
    (hp : p.Prime) (hpq : p ∣ 2 ^ 1 + 1) {D J : Subgroup G} (hD : D ≤ Bs)
    (hJ : IsComponentOf J (X ⊓ Subgroup.centralizer (D : Set G)))
    (hJL : J = LargeEvenLayer (X ⊓ Subgroup.centralizer (D : Set G))) :
    ∃ I : Finset (Fin n), 4 ≤ I.card ∧ J = (TableBUE.blockSU (K := K) (n := 1) I).map σ₁ ∧
      (∀ (d : G) (hd : d ∈ D), ∀ i ∈ I, ∀ j ∈ I,
        eta ⟨d, hD hd⟩ (π i) = eta ⟨d, hD hd⟩ (π j)) ∧
      ∀ i ∈ I, ∀ j : Fin n,
        (∀ (d : G) (hd : d ∈ D), eta ⟨d, hD hd⟩ (π j) = eta ⟨d, hD hd⟩ (π i)) → j ∈ I := by
  classical
  cases n with
  | zero => exact (hF.false_of_n_eq_zero hJ rfl).elim
  | succ m =>
    rw [← hF.1] at hJ hJL
    let δ : G → Fin (m + 1) → Kˣ :=
      fun e k => if h : e ∈ Bs then χ (eta ⟨e, h⟩ (π k)) else 1
    have hδ : ∀ e ∈ (D : Set G), (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs σ₁ := by
      intro e he
      have heB : e ∈ Bs := hD he
      have h := hF.suPairs_diagHom (⟨e, heB⟩ : ↥Bs)
      simpa [δ, dif_pos heB] using h
    have hker : σ₁.ker ≤ Subgroup.center ↥(unitarySU 2 1 K (m + 1)) := hF.ker_le_center
    obtain ⟨i, hiJ⟩ := SUTorus.exists_le_map_blockSU (ψ := σ₁) (m := m) hK hp hpq hker hδ hJ
    let I : Finset (Fin (m + 1)) := LinTorus.diagClass (D : Set G) δ i
    have hiJ' : J ≤ (TableBUE.blockSU (K := K) (n := 1) I).map σ₁ := by
      simpa [I] using hiJ
    have hI4 : 4 ≤ I.card := by
      simpa [I] using GGSecFiveBPermUniLFrame.four_le_card_diagClass_of_component_two
        (S := (D : Set G)) (δ := δ) hK hJ.2.2 hiJ
    have hJI : J = (TableBUE.blockSU (K := K) (n := 1) I).map σ₁ := by
      simpa [I] using
        GGSecFiveBPermUniLFrame.eq_map_blockSU_of_le_of_layer_two
          (ψ := σ₁) (S := (D : Set G)) (δ := δ) (J := J) (i := i)
          hK hker hδ hJL hiJ (by simpa [I] using hI4)
    refine ⟨I, hI4, hJI, ?_, ?_⟩
    · intro d hd i' hi' j' hj'
      have hi : δ d i' = δ d i :=
        LinTorus.mem_diagClass.mp (by simpa [I] using hi') d hd
      have hj : δ d j' = δ d i :=
        LinTorus.mem_diagClass.mp (by simpa [I] using hj') d hd
      exact hF.2.2.1 (by simpa [δ, dif_pos (hD hd)] using hi.trans hj.symm)
    · intro i' hi' j heta
      refine LinTorus.mem_diagClass.mpr fun d hd => ?_
      have h1 : δ d j = δ d i' := by
        have h := congrArg χ (heta d hd)
        simpa [δ, dif_pos (hD hd)] using h
      have h2 : δ d i' = δ d i :=
        LinTorus.mem_diagClass.mp (by simpa [I] using hi') d hd
      exact h1.trans h2

private theorem GGSecFiveBPermUniLFrame.component_le_blockSU_two [Finite G]
    {m : ℕ} {ψ : ↥(unitarySU 2 1 K (m + 1)) →* G} {S : Set G}
    {δ : G → Fin (m + 1) → Kˣ} {I : Finset (Fin (m + 1))} {i : Fin (m + 1)}
    (hK : UnitaryFieldData 2 1 K) (hp : p.Prime) (hpq : p ∣ 2 ^ 1 + 1)
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 1 K (m + 1)))
    (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs ψ)
    (hsmall : ∀ T : Finset (Fin (m + 1)), 4 ≤ T.card →
      (∀ e ∈ S, ∀ a ∈ T, ∀ b ∈ T, δ e a = δ e b) → T ⊆ I)
    (hIC : I ⊆ LinTorus.diagClass S δ i)
    (hCeq : LinTorus.diagClass S δ i = I)
    {J' : Subgroup G} (hJ' : IsComponentOf J' (ψ.range ⊓ Subgroup.centralizer S)) :
    J' ≤ (TableBUE.blockSU (K := K) (n := 1) I).map ψ := by
  obtain ⟨j, hjJ'⟩ := SUTorus.exists_le_map_blockSU
    (ψ := ψ) (m := m) hK hp hpq hker hδ hJ'
  let Cj : Finset (Fin (m + 1)) := LinTorus.diagClass S δ j
  have hCj4 : 4 ≤ Cj.card := by
    simpa [Cj] using GGSecFiveBPermUniLFrame.four_le_card_diagClass_of_component_two
      (S := S) (δ := δ) hK hJ'.2.2 hjJ'
  have hconstCj : ∀ e ∈ S, ∀ a ∈ Cj, ∀ b ∈ Cj, δ e a = δ e b := by
    intro e he a ha b hb
    exact (LinTorus.mem_diagClass.mp (by simpa [Cj] using ha) e he).trans
      (LinTorus.mem_diagClass.mp (by simpa [Cj] using hb) e he).symm
  have hCjI : Cj ⊆ I := hsmall Cj hCj4 hconstCj
  have hjCj : j ∈ Cj := LinTorus.self_mem_diagClass S δ j
  have hjC : j ∈ LinTorus.diagClass S δ i := (hCjI.trans hIC) hjCj
  have hCjC : Cj = LinTorus.diagClass S δ i := by
    have h := diagClass_eq_of_inter_nonempty (S := S) (δ := δ) (i := j) (j := i)
      ⟨j, Finset.mem_inter.mpr ⟨by simpa [Cj] using hjCj, hjC⟩⟩
    simpa [Cj] using h
  have hjJ'' : J' ≤ (TableBUE.blockSU (K := K) (n := 1) Cj).map ψ := by
    simpa [Cj] using hjJ'
  rw [hCjC.trans hCeq] at hjJ''
  exact hjJ''

private theorem GGSecFiveBPermUniLFrame.layer_le_map_blockSU_two [Finite G]
    {m : ℕ} {ψ : ↥(unitarySU 2 1 K (m + 1)) →* G} {S : Set G}
    {δ : G → Fin (m + 1) → Kˣ} {I : Finset (Fin (m + 1))} {i : Fin (m + 1)}
    (hX : ψ.range = X) (hK : UnitaryFieldData 2 1 K) (hp : p.Prime)
    (hpq : p ∣ 2 ^ 1 + 1)
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 1 K (m + 1)))
    (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs ψ)
    (hsmall : ∀ T : Finset (Fin (m + 1)), 4 ≤ T.card →
      (∀ e ∈ S, ∀ a ∈ T, ∀ b ∈ T, δ e a = δ e b) → T ⊆ I)
    (hIC : I ⊆ LinTorus.diagClass S δ i)
    (hCeq : LinTorus.diagClass S δ i = I) :
    LargeEvenLayer (X ⊓ Subgroup.centralizer S) ≤
      (TableBUE.blockSU (K := K) (n := 1) I).map ψ := by
  change sSup {K | IsComponentOf K (X ⊓ Subgroup.centralizer S)} ≤
    (TableBUE.blockSU (K := K) (n := 1) I).map ψ
  apply sSup_le
  intro J' hJ'
  have hJ'range : IsComponentOf J' (ψ.range ⊓ Subgroup.centralizer S) := by
    simpa [← hX] using hJ'
  exact GGSecFiveBPermUniLFrame.component_le_blockSU_two
    (ψ := ψ) (S := S) (δ := δ) (I := I) (i := i) hK hp hpq hker hδ
    hsmall hIC hCeq hJ'range

theorem GGSecFiveBPermUniLFrame.layer_eq_map_blockSU_two [Finite G] [Finite K] [CharP K 2]
    {σ₁ : ↥(unitarySU 2 1 K n) →* G}
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ₁ χ) (hK : UnitaryFieldData 2 1 K)
    (hp : p.Prime) (hpq : p ∣ 2 ^ 1 + 1) {D : Subgroup G} (hD : D ≤ Bs) {I : Finset (Fin n)}
    (hI4 : 4 ≤ I.card)
    (hconst : ∀ (d : G) (hd : d ∈ D), ∀ i ∈ I, ∀ j ∈ I,
        eta ⟨d, hD hd⟩ (π i) = eta ⟨d, hD hd⟩ (π j))
    (hsmall : ∀ S : Finset (Fin n), 4 ≤ S.card →
        (∀ (d : G) (hd : d ∈ D), ∀ i ∈ S, ∀ j ∈ S,
          eta ⟨d, hD hd⟩ (π i) = eta ⟨d, hD hd⟩ (π j)) → S ⊆ I) :
    IsComponentOf ((TableBUE.blockSU (K := K) (n := 1) I).map σ₁)
        (X ⊓ Subgroup.centralizer (D : Set G)) ∧
      (TableBUE.blockSU (K := K) (n := 1) I).map σ₁ =
        LargeEvenLayer (X ⊓ Subgroup.centralizer (D : Set G)) := by
  classical
  cases n with
  | zero =>
    rw [Finset.eq_empty_of_isEmpty I] at hI4
    exact absurd hI4 (by simp)
  | succ m =>
    obtain ⟨i, hiI⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
    let δ : G → Fin (m + 1) → Kˣ :=
      fun e k => if h : e ∈ Bs then χ (eta ⟨e, h⟩ (π k)) else 1
    have hδ : ∀ e ∈ (D : Set G), (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs σ₁ := by
      intro e he
      have heB : e ∈ Bs := hD he
      have h := hF.suPairs_diagHom (⟨e, heB⟩ : ↥Bs)
      simpa [δ, dif_pos heB] using h
    have hker : σ₁.ker ≤ Subgroup.center ↥(unitarySU 2 1 K (m + 1)) := hF.ker_le_center
    have hsmallδ : ∀ T : Finset (Fin (m + 1)), 4 ≤ T.card →
        (∀ e ∈ (D : Set G), ∀ a ∈ T, ∀ b ∈ T, δ e a = δ e b) → T ⊆ I := by
      intro T hT hconstT
      apply hsmall T hT
      intro d hd a ha b hb
      exact hF.2.2.1 (by simpa [δ, dif_pos (hD hd)] using hconstT d hd a ha b hb)
    let C : Finset (Fin (m + 1)) := LinTorus.diagClass (D : Set G) δ i
    have hIC : I ⊆ C := fun j hj =>
      LinTorus.mem_diagClass.mpr fun d hd => by
        have h := congrArg χ (hconst d hd j hj i hiI)
        simpa [δ, dif_pos (hD hd)] using h
    have hC4 : 4 ≤ C.card := hI4.trans (Finset.card_le_card hIC)
    have hconstC : ∀ e ∈ (D : Set G), ∀ a ∈ C, ∀ b ∈ C, δ e a = δ e b :=
      fun e he a ha b hb =>
        (LinTorus.mem_diagClass.mp (by simpa [C] using ha) e he).trans
          (LinTorus.mem_diagClass.mp (by simpa [C] using hb) e he).symm
    have hCeq : C = I := Finset.Subset.antisymm (hsmallδ C hC4 hconstC) hIC
    have hcomp : IsComponentOf ((TableBUE.blockSU (K := K) (n := 1) I).map σ₁)
        (σ₁.range ⊓ Subgroup.centralizer (D : Set G)) := by
      have h := GGSecFiveBPermUniLFrame.isComponentOf_map_blockSU_two
        (ψ := σ₁) (S := (D : Set G)) (δ := δ) (i := i) hK hker hδ
        (by simpa [C] using hC4)
      rwa [show LinTorus.diagClass (D : Set G) δ i = I from by simpa [C] using hCeq] at h
    refine ⟨?_, ?_⟩
    · simpa [hF.1] using hcomp
    · refine le_antisymm ?_ (GGSecFiveBPermUniLFrame.layer_le_map_blockSU_two
        (ψ := σ₁) (S := (D : Set G)) (δ := δ) (I := I) (i := i)
        hF.1 hK hp hpq hker hδ hsmallδ hIC hCeq)
      have hle : (TableBUE.blockSU (K := K) (n := 1) I).map σ₁ ≤
          LargeEvenLayer (σ₁.range ⊓ Subgroup.centralizer (D : Set G)) := le_sSup hcomp
      simpa [hF.1] using hle

end CFSG.StandardType

end

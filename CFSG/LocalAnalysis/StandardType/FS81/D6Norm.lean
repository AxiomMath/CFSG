module

public import CFSG.LocalAnalysis.StandardType.FS81.StdLoc
public import CFSG.LocalAnalysis.StandardType.FS81.D6NormAux
public import CFSG.LocalAnalysis.StandardType.FS81.D6Inner
public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthCore
public import CFSG.LocalAnalysis.StandardType.FS81.BasisMonomial
public import CFSG.LocalAnalysis.StandardType.FS81.RowElemAbOrth
public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthModels

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC
open CFSG.RankThree.Classical2 (orthDerived)
open Module

private theorem Basis3.b_ne_b_ne_inv {G : Type} [Group G] {k : ℕ} (B : Basis3 G k)
    {a b : Fin k} (hab : a ≠ b) : B.b a ≠ B.b b ∧ B.b a ≠ (B.b b)⁻¹ := by
  constructor
  · intro h
    have h1 : B.vec (Pi.single a 1 - Pi.single b 1) = 1 := by
      have h2 : B.vec (Pi.single a 1 - Pi.single b 1) = B.b a * (B.b b)⁻¹ := by
        calc B.vec (Pi.single a 1 - Pi.single b 1)
            = B.vec (Pi.single a 1) * B.vec (-(Pi.single b 1 : Coords k)) := by
              rw [sub_eq_add_neg, B.vec_add]
          _ = B.b a * (B.b b)⁻¹ := by
              rw [B.vec_single, show B.vec (-(Pi.single b 1 : Coords k)) =
                (B.vec (Pi.single b 1 : Coords k))⁻¹ from Basis3.vec_neg B _, B.vec_single]
      rw [h2, h, mul_inv_cancel]
    have h0 : (Pi.single a 1 - Pi.single b 1 : Coords k) = 0 := B.indep _ h1
    have h2 : (Pi.single a 1 - Pi.single b 1 : Coords k) a = 0 := by rw [h0]; rfl
    simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab, sub_zero] at h2
    exact one_ne_zero h2
  · intro h
    have h1 : B.vec (Pi.single a 1 + Pi.single b 1) = 1 := by
      have h2 : B.vec (Pi.single a 1 + Pi.single b 1) = B.b a * B.b b := by
        rw [B.vec_add, B.vec_single, B.vec_single]
      rw [h2, h, inv_mul_cancel]
    have h0 : (Pi.single a 1 + Pi.single b 1 : Coords k) = 0 := B.indep _ h1
    have h2 : (Pi.single a 1 + Pi.single b 1 : Coords k) a = 0 := by rw [h0]; rfl
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab, add_zero] at h2
    exact one_ne_zero h2

private theorem disjoint_zpowers_of_le_centralizer {G : Type} [Group G] {b₀ : G} {K : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G)) (hcenter : Subgroup.center K = ⊥) :
    Disjoint (Subgroup.zpowers b₀) K := by
  rw [Subgroup.disjoint_def]
  intro x hx hxK
  have hxZ : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute b₀ (y : G) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hKC y.2)).symm
    exact Subtype.ext (hc.zpow_left z).eq.symm
  rw [hcenter] at hxZ
  have hx1 : (⟨x, hxK⟩ : ↥K) = 1 := Subgroup.mem_bot.mp hxZ
  simpa using congrArg Subtype.val hx1

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC in
private theorem exists_mulEquiv_frame_D6_of_match {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (e₀ : ↥K ≃* ↥D6M.Om12) {B B' : Basis3 G (Row.D6.n + 1)}
    (hB : Adapted B b₀ K E) (hB' : Adapted B' b₀ K E)
    (F : SevOm.Frame D6M.Q12 3
      (((E ⊓ K).subgroupOf K).map ((orthDerived D6M.Q12).subtype.comp e₀.toMonoidHom)) 6)
    (hU : ∀ j, finrank (ZMod 2) (F.U j) = 2)
    (hφB' : ∀ (j : Fin 6) (hj : B'.b j.succ ∈ K),
      ((e₀ ⟨B'.b j.succ, hj⟩ : ↥(orthDerived D6M.Q12)) : D6M.V12 ≃ₗ[ZMod 2] D6M.V12) =
        F.ι (Multiplicative.ofAdd (Pi.single j 1)))
    (jmap : Fin 6 → Fin 6)
    (hjmap : ∀ i, B.b i.succ = B'.b (jmap i).succ ∨ B.b i.succ = (B'.b (jmap i).succ)⁻¹)
    (hinj : Function.Injective jmap) {l₀ : Fin 6 → D6M.V12 × D6M.V12}
    (hl₀ : IsFrame D6M.Q12 (List.ofFn l₀)) :
    ∃ e : ↥K ≃* ↥D6M.Om12, ∀ (i : Fin 6) (hi : B.b i.succ ∈ K),
      ((e ⟨B.b i.succ, hi⟩ : ↥D6M.Om12) : D6M.V12 ≃ₗ[ZMod 2] D6M.V12) =
        rot D6M.Q12 (l₀ i).1 (l₀ i).2 := by
  classical
  let A : Subgroup (D6M.V12 ≃ₗ[ZMod 2] D6M.V12) :=
    ((E ⊓ K).subgroupOf K).map ((orthDerived D6M.Q12).subtype.comp e₀.toMonoidHom)
  have hBi : ∀ i : Fin 6, B.b i.succ ∈ K := fun i => hB.2.2 i.succ (Fin.succ_ne_zero i)
  have hBj : ∀ j : Fin 6, B'.b j.succ ∈ K := fun j => hB'.2.2 j.succ (Fin.succ_ne_zero j)
  have hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup D6M.Q12 := by
    intro a ha
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp ha
    exact Subgroup.commutator_le_self _ (e₀ x).2
  have hdimV : finrank (ZMod 2) D6M.V12 = 2 * 6 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, two_mul]
  have htop : (⨆ i, F.U i) = ⊤ := F.iSup_pieces_eq_top hdimV hU
  have hpair : ∀ j : Fin 6, ∃ p : D6M.V12 × D6M.V12,
      MinusPair D6M.Q12 p.1 p.2 ∧ p.1 ∈ F.U j ∧ p.2 ∈ F.U j ∧
        rot D6M.Q12 p.1 p.2 = F.ι (Multiplicative.ofAdd (Pi.single j 1)) := by
    intro j
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff (F.U j)).mp (F.ne_bot j)
    obtain ⟨hmp, hmem, hrot⟩ := F.exists_rot_pair hAO htop j (hU j) hx hx0
    exact ⟨(x, F.ι (Multiplicative.ofAdd (Pi.single j 1)) x), hmp, hx, hmem, hrot⟩
  choose gp hgp using hpair
  let m : Fin 6 → D6M.V12 × D6M.V12 := fun i =>
    if B.b i.succ = B'.b (jmap i).succ then gp (jmap i) else (gp (jmap i)).swap
  let T : Fin 6 → (D6M.V12 ≃ₗ[ZMod 2] D6M.V12) := fun i =>
    ((e₀ ⟨B.b i.succ, hBi i⟩ : ↥D6M.Om12) : D6M.V12 ≃ₗ[ZMod 2] D6M.V12)
  have hmp_m : ∀ i, MinusPair D6M.Q12 (m i).1 (m i).2 := by
    intro i
    by_cases h : B.b i.succ = B'.b (jmap i).succ
    · rw [show m i = gp (jmap i) from by simp [m, h]]
      exact (hgp (jmap i)).1
    · rw [show m i = (gp (jmap i)).swap from by simp [m, h]]
      exact ((hgp (jmap i)).1).symm
  have hmem_m : ∀ i, (m i).1 ∈ F.U (jmap i) ∧ (m i).2 ∈ F.U (jmap i) := by
    intro i
    by_cases h : B.b i.succ = B'.b (jmap i).succ
    · rw [show m i = gp (jmap i) from by simp [m, h]]
      exact ⟨(hgp (jmap i)).2.1, (hgp (jmap i)).2.2.1⟩
    · rw [show m i = (gp (jmap i)).swap from by simp [m, h]]
      exact ⟨(hgp (jmap i)).2.2.1, (hgp (jmap i)).2.1⟩
  have hrot_m : ∀ i, rot D6M.Q12 (m i).1 (m i).2 = T i := by
    intro i
    by_cases h : B.b i.succ = B'.b (jmap i).succ
    · have hm : m i = gp (jmap i) := by simp [m, h]
      have hsub : (⟨B.b i.succ, hBi i⟩ : ↥K) = ⟨B'.b (jmap i).succ, hBj (jmap i)⟩ :=
        Subtype.ext h
      rw [hm, (hgp (jmap i)).2.2.2]
      rw [show T i = ((e₀ ⟨B'.b (jmap i).succ, hBj (jmap i)⟩ : ↥D6M.Om12) :
        D6M.V12 ≃ₗ[ZMod 2] D6M.V12) from by simp only [T, hsub]]
      exact (hφB' (jmap i) (hBj (jmap i))).symm
    · have h1 : B.b i.succ = (B'.b (jmap i).succ)⁻¹ := (hjmap i).resolve_left h
      have hm : m i = (gp (jmap i)).swap := by simp [m, h]
      have hsub : (⟨B.b i.succ, hBi i⟩ : ↥K) =
          (⟨B'.b (jmap i).succ, hBj (jmap i)⟩ : ↥K)⁻¹ := Subtype.ext (by simpa using h1)
      rw [hm, rot_swap]
      change (rot D6M.Q12 (gp (jmap i)).1 (gp (jmap i)).2)⁻¹ = T i
      rw [(hgp (jmap i)).2.2.2]
      rw [show T i = ((e₀ (⟨B'.b (jmap i).succ, hBj (jmap i)⟩ : ↥K)⁻¹ : ↥D6M.Om12) :
        D6M.V12 ≃ₗ[ZMod 2] D6M.V12) from by simp only [T, hsub]]
      rw [map_inv, Subgroup.coe_inv, (hφB' (jmap i) (hBj (jmap i))).symm]
  have hframe : IsFrame D6M.Q12 (List.ofFn m) := by
    refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      exact hmp_m i
    · rw [List.pairwise_ofFn]
      intro i i' hii
      have hne : jmap i ≠ jmap i' := fun hh => (ne_of_lt hii) (hinj hh)
      exact ⟨F.orth _ _ hne (m i).1 (hmem_m i).1 (m i').1 (hmem_m i').1,
        F.orth _ _ hne (m i).1 (hmem_m i).1 (m i').2 (hmem_m i').2,
        F.orth _ _ hne (m i).2 (hmem_m i).2 (m i').1 (hmem_m i').1,
        F.orth _ _ hne (m i).2 (hmem_m i).2 (m i').2 (hmem_m i').2⟩
  obtain ⟨g, hgO, hgmap⟩ := exists_isometry_frame (Q := D6M.Q12) (n := 6)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 6 (ZMod 2)) hframe hl₀ (by simp) (by simp)
  have hgpt : ∀ i : Fin 6, g (m i).1 = (l₀ i).1 ∧ g (m i).2 = (l₀ i).2 := by
    intro i
    have h' : List.ofFn (fun i => (g (m i).1, g (m i).2)) = List.ofFn l₀ := by
      rw [List.ofFn_comp']
      exact hgmap
    have hfun : (fun i => (g (m i).1, g (m i).2)) = l₀ := List.ofFn_inj.mp h'
    exact Prod.mk.inj (congrFun hfun i)
  have hconj_mem : ∀ {h : D6M.V12 ≃ₗ[ZMod 2] D6M.V12},
      h ∈ TauCeti.QuadraticMap.orthogonalGroup D6M.Q12 →
      ∀ x ∈ D6M.Om12, h * x * h⁻¹ ∈ D6M.Om12 := by
    intro h hh x hx
    have hO : (TauCeti.QuadraticMap.orthogonalGroup D6M.Q12).map
        (MulAut.conj h).toMonoidHom = TauCeti.QuadraticMap.orthogonalGroup D6M.Q12 := by
      apply le_antisymm
      · rintro y ⟨z, hz, rfl⟩
        simpa [MulAut.conj_apply] using mul_mem (mul_mem hh hz) (inv_mem hh)
      · intro y hy
        refine Subgroup.mem_map.mpr
          ⟨h⁻¹ * y * h, mul_mem (mul_mem (inv_mem hh) hy) hh, ?_⟩
        show h * (h⁻¹ * y * h) * h⁻¹ = y
        group
    have hmapOm : D6M.Om12.map (MulAut.conj h).toMonoidHom = D6M.Om12 := by
      show (⁅_, _⁆ : Subgroup (D6M.V12 ≃ₗ[ZMod 2] D6M.V12)).map _ = _
      rw [Subgroup.map_commutator, hO]
    have h' := Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom hx
    rw [hmapOm] at h'
    simpa [MulAut.conj_apply] using h'
  let cg : ↥D6M.Om12 ≃* ↥D6M.Om12 :=
    { toFun := fun x =>
        ⟨g * (x : D6M.V12 ≃ₗ[ZMod 2] D6M.V12) * g⁻¹, hconj_mem hgO x x.2⟩
      invFun := fun x =>
        ⟨g⁻¹ * (x : D6M.V12 ≃ₗ[ZMod 2] D6M.V12) * g, hconj_mem (inv_mem hgO) x x.2⟩
      left_inv := fun x => Subtype.ext (by group)
      right_inv := fun x => Subtype.ext (by group)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  refine ⟨e₀.trans cg, ?_⟩
  intro i hi
  have hsub : (⟨B.b i.succ, hi⟩ : ↥K) = ⟨B.b i.succ, hBi i⟩ := Subtype.ext rfl
  rw [hsub]
  change g * T i * g⁻¹ = rot D6M.Q12 (l₀ i).1 (l₀ i).2
  rw [← hrot_m i, conj_rot hgO, (hgpt i).1, (hgpt i).2]

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC in
theorem exists_mulEquiv_frame_D6 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G (Row.D6.n + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOut Row.D6 B b₀) {l₀ : Fin 6 → D6M.V12 × D6M.V12}
    (hl₀ : IsFrame D6M.Q12 (List.ofFn l₀)) :
    ∃ e : ↥K ≃* ↥D6M.Om12, ∀ (i : Fin 6) (hi : B.b i.succ ∈ K),
      ((e ⟨B.b i.succ, hi⟩ : ↥D6M.Om12) : D6M.V12 ≃ₗ[ZMod 2] D6M.V12) =
        rot D6M.Q12 (l₀ i).1 (l₀ i).2 := by
  classical
  have hstd' : StdLoc b₀ K E Row.D6 := hstd
  obtain ⟨-, hHyp, hCanon⟩ := hstd
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨hb₀, hKC, -, hcenter, -, -, -, -⟩ := hA
  obtain ⟨hrow, hdisj, hsup, hmax, hcard, -⟩ := hCanon
  obtain ⟨-, ⟨e₀⟩⟩ := isSimpleGroup_and_mulEquiv_of_isRow_D6 hrow hcenter
  have hdisjK : Disjoint (Subgroup.zpowers b₀) K :=
    disjoint_zpowers_of_le_centralizer hKC hcenter
  obtain ⟨B', F, hB', heven, hU, hφB'⟩ := exists_basis_frame_of_model
    (V := D6M.V12) (Q := D6M.Q12)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 6 (ZMod 2))
    exists_totallySingular_three_quadPlus_six (n := 6) (by norm_num) e₀ hb₀ hKC hdisjK hsup hmax
    hcard
  have hR : B.realized K ⊆ evenFix0 6 := by
    rw [(realized_centralizer_eq_realized_D6 hstd' hB hrec).2]
    exact fun _ hx => hx
  have hex : ∀ i : Fin 6, ∃ j : Fin 6,
      B.b i.succ = B'.b j.succ ∨ B.b i.succ = (B'.b j.succ)⁻¹ :=
    fun i => exists_eq_or_eq_inv_of_realized_evenFix0 (n := 6) (by norm_num) hdisjK hB hB' hR
      heven i
  choose jmap hjmap using hex
  have hinj : Function.Injective jmap := by
    intro i i' hii
    by_contra hne
    have h1 := hjmap i
    have h2 := hjmap i'
    rw [hii] at h1
    have hconj : B.b i.succ = B.b i'.succ ∨ B.b i.succ = (B.b i'.succ)⁻¹ := by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · left; rw [h1, h2]
      · right; rw [h1, h2, inv_inv]
      · right; rw [h1, h2]
      · left; rw [h1, h2]
    have hne' : i.succ ≠ i'.succ := fun hh => hne (Fin.succ_inj.mp hh)
    rcases hconj with h | h
    · exact (Basis3.b_ne_b_ne_inv B hne').1 h
    · exact (Basis3.b_ne_b_ne_inv B hne').2 h
  exact exists_mulEquiv_frame_D6_of_match e₀ hB hB' F hU hφB' jmap hjmap hinj hl₀

end CFSG.StandardType.FrameRoute.FS81

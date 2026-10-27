module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Defs
public import CFSG.LocalAnalysis.StandardType.FS81.D6InnerAux
public import CFSG.LocalAnalysis.StandardType.FS81.BasisMonomial
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainBasic
public import CFSG.LocalAnalysis.StandardType.FS81.RootLineRigidAux
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Pointwise

@[expose] def wtSupport {k : ℕ} (v : Coords k) : Finset (Fin k) :=
  Finset.univ.filter fun i => v i ≠ 0

@[simp] theorem mem_wtSupport {k : ℕ} {v : Coords k} {i : Fin k} :
    i ∈ wtSupport v ↔ v i ≠ 0 := by
  simp [wtSupport]

theorem wt_eq_card_wtSupport {k : ℕ} (v : Coords k) : wt v = (wtSupport v).card := rfl

theorem wtSupport_add_single_of_apply_eq_zero {k : ℕ} {v : Coords k} {j : Fin k}
    (hj : v j = 0) :
    wtSupport (v + Pi.single j 1) = insert j (wtSupport v) := by
  ext i
  by_cases h : i = j
  · subst h
    simp [wtSupport, hj]
  · simp [wtSupport, h]

theorem wt_add_single_of_apply_eq_zero {k : ℕ} {v : Coords k} {j : Fin k} (hj : v j = 0) :
    wt (v + Pi.single j 1) = wt v + 1 := by
  rw [wt_eq_card_wtSupport, wtSupport_add_single_of_apply_eq_zero hj,
    Finset.card_insert_of_notMem (by simp [hj]), wt_eq_card_wtSupport]

theorem wt_pi_single_one {k : ℕ} (i : Fin k) : wt (Pi.single i (1 : ZMod 3)) = 1 := by
  rw [wt_eq_card_wtSupport]
  have hsupp : wtSupport (Pi.single i (1 : ZMod 3)) = {i} := by
    ext x
    rw [mem_wtSupport, Pi.single_apply, Finset.mem_singleton]
    by_cases hx : x = i
    · rw [if_pos hx, hx]
      exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩
    · rw [if_neg hx]
      exact ⟨fun h => absurd rfl h, fun h => absurd h hx⟩
  rw [hsupp, Finset.card_singleton]

theorem prod_add_single_of_apply_eq_one {k : ℕ} {v : Coords k} {j : Fin k}
    (hj : v j = 1) (hprod : ∏ i, v i = 1) :
    ∏ i, (v + (Pi.single j 1 : Coords k)) i = 2 := by
  have hsplit : ∏ i, (v + (Pi.single j 1 : Coords k)) i =
      (v j + 1) * ∏ i ∈ Finset.univ.erase j, v i := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => (v + (Pi.single j 1 : Coords k)) i) (Finset.mem_univ j)]
    congr 1
    · rw [Pi.add_apply, Pi.single_apply, if_pos rfl]
    · refine Finset.prod_congr rfl fun i hi => ?_
      rw [Pi.add_apply, Pi.single_apply, if_neg (Finset.ne_of_mem_erase hi), add_zero]
  have hsplit2 : ∏ i, v i = v j * ∏ i ∈ Finset.univ.erase j, v i :=
    (Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)).symm
  have hrest : ∏ i ∈ Finset.univ.erase j, v i = 1 := by
    rw [hprod, hj, one_mul] at hsplit2
    exact hsplit2.symm
  rw [hsplit, hj, hrest, mul_one]
  decide

@[expose] def twD5Good (v : Coords (5 + 1)) : Prop :=
  (wt v ≤ 2 ∧ v 0 ≠ 0) ∨ (wt v = 6 ∧ ∏ i, v i = 1)

theorem not_twD5Good_add_single_of_wt_eq_six {v : Coords (5 + 1)} (hwt6 : wt v = 6)
    (hprod : ∏ i, v i = 1) : ¬ twD5Good (v + Pi.single 2 1) := by
  intro h2
  have hc2 : v 2 ≠ 0 := (wt_eq_iff_forall_ne_zero v).mp hwt6 2
  have h := wt_single_add_smul (u := v) (j := 2) hc2 (c := (1 : ZMod 3)) (by decide)
  rw [one_smul] at h
  rcases RootLineAux.eq_one_or_eq_neg_one_of_ne_zero (v 2) hc2 with hcase | hcase
  · have hwt : wt (v + (Pi.single (2 : Fin (5 + 1)) 1 : Coords (5 + 1))) = 6 := by
      have hif : ¬ ((1 : ZMod 3) + 1 * v 2 = 0) := by rw [hcase]; decide
      rw [add_comm (v) (Pi.single (2 : Fin (5 + 1)) 1), h, if_neg hif, hwt6]
    have hprod' : ∏ i, (v + (Pi.single (2 : Fin (5 + 1)) 1 : Coords (5 + 1))) i = 2 :=
      prod_add_single_of_apply_eq_one hcase hprod
    rcases h2 with ⟨h2a, -⟩ | ⟨-, h2c⟩
    · omega
    · rw [hprod'] at h2c
      exact absurd h2c (by decide)
  · have hwt : wt (v + (Pi.single (2 : Fin (5 + 1)) 1 : Coords (5 + 1))) = 5 := by
      have hif : ((1 : ZMod 3) + 1 * v 2 = 0) := by rw [hcase]; decide
      rw [add_comm (v) (Pi.single (2 : Fin (5 + 1)) 1), h, if_pos hif]
      omega
    rcases h2 with ⟨h2a, -⟩ | ⟨h2b, -⟩ <;> omega

theorem support_subset_pair_of_twD5Good {v : Coords (5 + 1)}
    (h1 : twD5Good v) (h2 : twD5Good (v + Pi.single 2 1)) :
    ∀ i, v i ≠ 0 → i = 0 ∨ i = 2 := by
  classical
  intro i hi
  by_contra hcon
  obtain ⟨hi0, hi2⟩ := not_or.mp hcon
  rcases h1 with ⟨hwt, h0⟩ | ⟨hwt6, hprod⟩
  · have hpair : ({0, i} : Finset (Fin (5 + 1))) ⊆ wtSupport v := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simpa using h0
      · simpa using hi
    have hc2 : v 2 = 0 := by
      by_contra hc2
      have hsub : ({0, i, 2} : Finset (Fin (5 + 1))) ⊆ wtSupport v := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · simpa using h0
        · simpa using hi
        · simpa using hc2
      have hcard3 : ({0, i, 2} : Finset (Fin (5 + 1))).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hi0]),
          Finset.card_insert_of_notMem (by simp [hi2]), Finset.card_singleton]
      have hle := Finset.card_le_card hsub
      rw [hcard3] at hle
      have h3 : 3 ≤ wt v := hle
      omega
    have hwt2 : wt v = 2 := by
      have h2le : 2 ≤ wt v := by
        have hle := Finset.card_le_card hpair
        rw [Finset.card_pair (Ne.symm hi0)] at hle
        exact hle
      omega
    have hwt3 : wt (v + (Pi.single (2 : Fin (5 + 1)) 1 : Coords (5 + 1))) = 3 := by
      rw [wt_add_single_of_apply_eq_zero hc2, hwt2]
    rcases h2 with ⟨h2a, -⟩ | ⟨h2b, -⟩ <;> omega
  · exact absurd h2 (not_twD5Good_add_single_of_wt_eq_six hwt6 hprod)

theorem eq_single_add_single_of_support_subset_pair {v : Coords (5 + 1)}
    (h : ∀ i, v i ≠ 0 → i = 0 ∨ i = 2) :
    v = Pi.single (0 : Fin (5 + 1)) (v 0) + Pi.single (2 : Fin (5 + 1)) (v 2) := by
  funext k
  rw [Pi.add_apply, Pi.single_apply, Pi.single_apply]
  by_cases hk0 : k = 0
  · subst hk0
    rw [if_pos rfl, if_neg (show ¬((0 : Fin (5 + 1)) = 2) by decide), add_zero]
  · by_cases hk2 : k = 2
    · subst hk2
      rw [if_neg (show ¬((2 : Fin (5 + 1)) = 0) by decide), if_pos rfl, zero_add]
    · have hk : v k = 0 := by
        by_contra hne
        rcases h k hne with h' | h'
        · exact hk0 h'
        · exact hk2 h'
      rw [if_neg hk0, if_neg hk2, zero_add]
      exact hk

theorem disjoint_of_forall_pow_three_eq_one_of_coprime {G : Type} [Group G]
    {E O : Subgroup G} (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hcop : Nat.Coprime 3 (Nat.card O)) :
    Disjoint E O := by
  refine Subgroup.disjoint_def.mpr fun {g} hgE hgO => ?_
  have h3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (hE3 g hgE)
  have hO : orderOf g ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hgO
  have hcopg : Nat.Coprime 3 (orderOf g) := hcop.coprime_dvd_right hO
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcopg h3 (dvd_refl _))

theorem not_dvd_index_subgroupOf_sup_of_coprime {G : Type} [Group G] [Finite G]
    {E O : Subgroup G} (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hcop : Nat.Coprime 3 (Nat.card O))
    (hnormal : E ≤ Subgroup.normalizer (O : Set G)) :
    ¬ 3 ∣ (E.subgroupOf (E ⊔ O)).index := by
  have hdisj : Disjoint E O := disjoint_of_forall_pow_three_eq_one_of_coprime hE3 hcop
  have hcard : Nat.card ↥(E ⊔ O) = Nat.card E * Nat.card O := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer O E
      hnormal hdisj.symm
    rw [sup_comm, h, mul_comm]
  have hcardE : Nat.card ↥(E.subgroupOf (E ⊔ O)) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have hmul := Subgroup.card_mul_index (E.subgroupOf (E ⊔ O))
  have hEq : Nat.card E * (E.subgroupOf (E ⊔ O)).index = Nat.card E * Nat.card O := by
    calc Nat.card E * (E.subgroupOf (E ⊔ O)).index
        = Nat.card ↥(E.subgroupOf (E ⊔ O)) * (E.subgroupOf (E ⊔ O)).index := by rw [hcardE]
      _ = Nat.card ↥(E ⊔ O) := hmul
      _ = Nat.card E * Nat.card O := hcard
  have hidx : (E.subgroupOf (E ⊔ O)).index = Nat.card O := by
    refine Nat.mul_left_cancel (n := Nat.card E) ?_ hEq
    exact Nat.card_pos_iff.mpr ⟨⟨1, E.one_mem⟩, inferInstance⟩
  rw [hidx]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop

theorem exists_mem_conj_of_mem_sup_of_coprime {G : Type} [Group G] [Finite G]
    {E O : Subgroup G} (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hEpg : IsPGroup 3 E)
    (hcop : Nat.Coprime 3 (Nat.card O))
    (hnormal : E ≤ Subgroup.normalizer (O : Set G)) {x : G} (hx : x ∈ E ⊔ O)
    (hxord : orderOf x = 3) :
    ∃ o ∈ O, o * x * o⁻¹ ∈ E := by
  classical
  have hindex := not_dvd_index_subgroupOf_sup_of_coprime hE3 hcop hnormal
  have hEA : IsPGroup 3 (E.subgroupOf (E ⊔ O)) := hEpg.comap_subtype
  let T : Sylow 3 ↥(E ⊔ O) := hEA.toSylow hindex
  have hTcoe : (T : Subgroup ↥(E ⊔ O)) = E.subgroupOf (E ⊔ O) := rfl
  have hxpow : IsPGroup 3 (Subgroup.zpowers (⟨x, hx⟩ : ↥(E ⊔ O))) := by
    have hord : orderOf (⟨x, hx⟩ : ↥(E ⊔ O)) = 3 := by
      rw [Subgroup.orderOf_mk, hxord]
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]
    norm_num
  obtain ⟨S, hS⟩ := hxpow.exists_le_sylow
  have hfin : Finite (Sylow 3 ↥(E ⊔ O)) := Sylow.finite_of_finiteIndex T
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq ↥(E ⊔ O) S T
  have hmemS : (⟨x, hx⟩ : ↥(E ⊔ O)) ∈ (S : Subgroup ↥(E ⊔ O)) :=
    hS (Subgroup.mem_zpowers _)
  have hmemT : (MulAut.conj y) (⟨x, hx⟩ : ↥(E ⊔ O)) ∈ (T : Subgroup ↥(E ⊔ O)) := by
    rw [← hy, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul (⟨x, hx⟩ : ↥(E ⊔ O)) (MulAut.conj y)
      (S : Subgroup ↥(E ⊔ O)) hmemS
  have hyxy : (y : G) * x * (y : G)⁻¹ ∈ E := by
    have h1 : ((MulAut.conj y) (⟨x, hx⟩ : ↥(E ⊔ O)) : G) ∈ E := by
      rw [hTcoe] at hmemT
      exact Subgroup.mem_subgroupOf.mp hmemT
    simpa [MulAut.conj_apply] using h1
  have hset : ((E ⊔ O : Subgroup G) : Set G) = (E : Set G) * (O : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right E O hnormal
  have hyE : (y : G) ∈ (E : Set G) * (O : Set G) := by
    rw [← hset]
    exact y.2
  obtain ⟨e, heE, o, hoO, heo⟩ := Set.mem_mul.mp hyE
  refine ⟨o, hoO, ?_⟩
  have hconj : e * (o * x * o⁻¹) * e⁻¹ = (y : G) * x * (y : G)⁻¹ := by
    rw [← heo]
    group
  have h1 : e * (o * x * o⁻¹) * e⁻¹ ∈ E := by rw [hconj]; exact hyxy
  have h2 : e⁻¹ * (e * (o * x * o⁻¹) * e⁻¹) * e ∈ E :=
    E.mul_mem (E.mul_mem (E.inv_mem heE) h1) heE
  rwa [show e⁻¹ * (e * (o * x * o⁻¹) * e⁻¹) * e = o * x * o⁻¹ by group] at h2

theorem isConjLine_zpowers_mul_of_recOutTwD5 {G : Type} [Group G] [Finite G] {b₀ : G}
    {B : Basis3 G (5 + 1)} (hb0 : B.b 0 = b₀) (hrec : RecOutTwD5 B b₀) {g e : G}
    (hg0 : g * b₀ * g⁻¹ = e) (hg2 : g * B.b 2 * g⁻¹ = B.b 2) :
    IsConjLine b₀ (Subgroup.zpowers (e * B.b 2)) := by
  have hne0 : (Pi.single (0 : Fin (5 + 1)) 1 + Pi.single (2 : Fin (5 + 1)) 1 :
      Coords (5 + 1)) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have hwt0 : wt (Pi.single (0 : Fin (5 + 1)) 1 + Pi.single (2 : Fin (5 + 1)) 1) ≤ 2 := by
    have h0 : (Pi.single (0 : Fin (5 + 1)) (1 : ZMod 3) : Coords (5 + 1)) 2 = 0 := by
      rw [Pi.single_apply, if_neg (show ¬((2 : Fin (5 + 1)) = 0) by decide)]
    rw [wt_add_single_of_apply_eq_zero (v := Pi.single (0 : Fin (5 + 1)) 1) (j := 2) h0,
      wt_pi_single_one]
  have hcoord0 : (Pi.single (0 : Fin (5 + 1)) 1 + Pi.single (2 : Fin (5 + 1)) 1 :
      Coords (5 + 1)) 0 ≠ 0 := by
    rw [Pi.add_apply, Pi.single_apply, Pi.single_apply,
      if_pos rfl, if_neg (show ¬((0 : Fin (5 + 1)) = 2) by decide), add_zero]
    exact one_ne_zero
  have hline0 : IsConjLine b₀
      (B.line (Pi.single (0 : Fin (5 + 1)) 1 + Pi.single (2 : Fin (5 + 1)) 1)) :=
    (hrec.2.2.2 _ hne0).mpr (Or.inl ⟨hwt0, hcoord0⟩)
  have hconj := isConjLine_map_conj hline0 g
  have hmap : (B.line (Pi.single (0 : Fin (5 + 1)) 1 +
      Pi.single (2 : Fin (5 + 1)) 1)).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (e * B.b 2) := by
    rw [Basis3.line, MonoidHom.map_zpowers, Basis3.vec_add, Basis3.vec_single, Basis3.vec_single,
      hb0]
    congr 1
    show g * (b₀ * B.b 2) * g⁻¹ = e * B.b 2
    calc g * (b₀ * B.b 2) * g⁻¹ = (g * b₀ * g⁻¹) * (g * B.b 2 * g⁻¹) := by group
      _ = e * B.b 2 := by rw [hg0, hg2]
  rwa [hmap] at hconj

theorem exists_zpow_mul_zpow_of_recOutTwD5 {G : Type} [Group G] [Finite G] {b₀ : G}
    {B : Basis3 G (5 + 1)} (hb0 : B.b 0 = b₀) (hrec : RecOutTwD5 B b₀) {e : G}
    (he : e ∈ B.span) (he1 : e ≠ 1)
    (h1 : IsConjLine b₀ (Subgroup.zpowers e))
    (h2 : IsConjLine b₀ (Subgroup.zpowers (e * B.b 2))) :
    ∃ k m : ℕ, e = b₀ ^ k * (B.b 2) ^ m := by
  classical
  obtain ⟨c, hc⟩ := B.exists_vec_eq he
  have hcne : c ≠ 0 := by
    intro hc0
    exact he1 (by rw [← hc, hc0, Basis3.vec_zero])
  have hline1 : IsConjLine b₀ (B.line c) := by
    rw [Basis3.line, hc]
    exact h1
  have hgood1 : twD5Good c := (hrec.2.2.2 c hcne).mp hline1
  have hne2 : c + Pi.single (2 : Fin (5 + 1)) 1 ≠ 0 := by
    intro h0
    have hc0 : c 0 = 0 := by
      have := congrFun h0 0
      simpa using this
    rcases hgood1 with ⟨-, h0ne⟩ | ⟨hwt6, -⟩
    · exact h0ne hc0
    · exact ((wt_eq_iff_forall_ne_zero c).mp hwt6 0) hc0
  have hline2 : IsConjLine b₀ (B.line (c + Pi.single (2 : Fin (5 + 1)) 1)) := by
    rw [Basis3.line, Basis3.vec_add, Basis3.vec_single, hc]
    exact h2
  have hgood2 : twD5Good (c + Pi.single (2 : Fin (5 + 1)) 1) :=
    (hrec.2.2.2 _ hne2).mp hline2
  have hsupp := support_subset_pair_of_twD5Good hgood1 hgood2
  have hdecomp : c = Pi.single (0 : Fin (5 + 1)) (c 0) + Pi.single (2 : Fin (5 + 1)) (c 2) :=
    eq_single_add_single_of_support_subset_pair hsupp
  refine ⟨(c 0).val, (c 2).val, ?_⟩
  conv_lhs => rw [← hc, hdecomp]
  rw [Basis3.vec_add, Basis3.vec_single_eq_pow, Basis3.vec_single_eq_pow, hb0]

theorem conj_mul_fix_of_commute {G : Type} [Group G] {o h b : G} (ho : o * b = b * o)
    (hh : h * b = b * h) : (o * h) * b * (o * h)⁻¹ = b := by
  calc (o * h) * b * (o * h)⁻¹ = o * (h * b * h⁻¹) * o⁻¹ := by group
    _ = o * b * o⁻¹ := by rw [show h * b * h⁻¹ = b by rw [hh]; group]
    _ = b := by rw [show o * b * o⁻¹ = b by rw [ho]; group]

theorem conj_mem_sup_zpowers_sup {G : Type} [Group G] {b₀ b₂ o : G} {H O : Subgroup G}
    (hb0H : b₀ ∈ H) (hoO : o ∈ O)
    (hOnorm : H ≤ Subgroup.normalizer (O : Set G)) (ho2 : o * b₂ = b₂ * o) {k m : ℕ} :
    o⁻¹ * (b₀ ^ k * b₂ ^ m) * o ∈ Subgroup.zpowers b₀ ⊔ Subgroup.zpowers b₂ ⊔ O := by
  have ho2' : o⁻¹ * b₂ * o = b₂ := by
    rw [show o⁻¹ * b₂ * o = o⁻¹ * (b₂ * o) by group, ← ho2]
    group
  have hconjpow : ∀ n : ℕ, o⁻¹ * b₂ ^ n * o = b₂ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        calc o⁻¹ * (b₂ ^ n * b₂) * o = (o⁻¹ * b₂ ^ n * o) * (o⁻¹ * b₂ * o) := by group
          _ = b₂ ^ n * b₂ := by rw [ih, ho2']
  have hb0kH : b₀ ^ k ∈ H := Subgroup.pow_mem H hb0H k
  have hconj : b₀ ^ k * o * (b₀ ^ k)⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.mp (hOnorm hb0kH) o).mp hoO
  have h1 : o⁻¹ * b₀ ^ k * o ∈ O ⊔ Subgroup.zpowers b₀ := by
    have hz : o⁻¹ * (b₀ ^ k * o * (b₀ ^ k)⁻¹) ∈ O :=
      O.mul_mem (O.inv_mem hoO) hconj
    rw [show o⁻¹ * b₀ ^ k * o = (o⁻¹ * (b₀ ^ k * o * (b₀ ^ k)⁻¹)) * b₀ ^ k by group]
    exact Subgroup.mul_mem_sup hz (Subgroup.pow_mem _ (Subgroup.mem_zpowers b₀) k)
  have hsplit : o⁻¹ * (b₀ ^ k * b₂ ^ m) * o = (o⁻¹ * b₀ ^ k * o) * b₂ ^ m := by
    rw [show o⁻¹ * (b₀ ^ k * b₂ ^ m) * o
        = (o⁻¹ * b₀ ^ k * o) * (o⁻¹ * b₂ ^ m * o) by group, hconjpow m]
  rw [hsplit]
  have hb2m : b₂ ^ m ∈ Subgroup.zpowers b₂ :=
    Subgroup.pow_mem _ (Subgroup.mem_zpowers b₂) m
  have hle : (O ⊔ Subgroup.zpowers b₀) ⊔ Subgroup.zpowers b₂ ≤
      Subgroup.zpowers b₀ ⊔ Subgroup.zpowers b₂ ⊔ O := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_sup_right
    · exact le_trans le_sup_left le_sup_left
    · exact le_trans le_sup_right le_sup_left
  exact hle (Subgroup.mul_mem_sup h1 hb2m)

theorem exists_mem_conj_mem_of_mem_sup_primeCore {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    {x : G} (hx : x ∈ E ⊔ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)))
    (hxord : orderOf x = 3) :
    ∃ o ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)), o * x * o⁻¹ ∈ E := by
  classical
  obtain ⟨-, hHyp, -⟩ := hstd
  obtain ⟨-, -, -, -, -, -, -, -, hEmax, -, -, -⟩ := hHyp
  have hElem : IsElemAbelian 3 E := hEmax.2.1
  set H : Subgroup G := Subgroup.centralizer ({B.b 2} : Set G) with hH
  set O : Subgroup G := GLAPPrimeCoreOf 3 H with hO
  have hb2E : B.b 2 ∈ E := by
    rw [← hB.1]
    exact Subgroup.subset_closure (Set.mem_range_self 2)
  have hEH : E ≤ H := by
    rw [hH]
    exact (Subgroup.le_centralizer_iff_isMulCommutative.mpr hElem.1).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb2E))
  have hOnorm : H ≤ Subgroup.normalizer (O : Set G) := by
    rw [hO]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
      (gLAPPrimeCoreOf_normal 3 H)
  have hcop : Nat.Coprime 3 (Nat.card O) := by
    have hmap : O = (pPrimeCore 3 ↥H).map H.subtype := rfl
    rw [hmap, Subgroup.card_map_of_injective H.subtype_injective]
    exact coprime_card_pPrimeCore 3 ↥H
  have hxA : x ∈ E ⊔ O := hx
  obtain ⟨o, hoO, hoxo⟩ := exists_mem_conj_of_mem_sup_of_coprime hElem.2 hElem.isPGroup hcop
    (hEH.trans hOnorm) hxA hxord
  exact ⟨o, hoO, hoxo⟩

theorem mem_sup_zpowers_sup_primeCore_of_mem_sup {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) {h : G} (hh : h ∈ Subgroup.centralizer ({B.b 2} : Set G))
    (hE : h * b₀ * h⁻¹ ∈ E ⊔ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G))) :
    h * b₀ * h⁻¹ ∈ Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2) ⊔
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({B.b 2} : Set G)) := by
  classical
  have hstd0 : StdTwD5 b₀ K E := hstd
  obtain ⟨-, hHyp, -⟩ := hstd0
  obtain ⟨hb0ord, -, -, -, -, -, -, -, hEmax, hb0E, -, -⟩ := hHyp
  have hElem : IsElemAbelian 3 E := hEmax.2.1
  set H : Subgroup G := Subgroup.centralizer ({B.b 2} : Set G) with hH
  set O : Subgroup G := GLAPPrimeCoreOf 3 H with hO
  set x : G := h * b₀ * h⁻¹ with hx
  have hxord : orderOf x = 3 := by
    have h' : x = MulAut.conj h b₀ := by rw [hx, MulAut.conj_apply]
    rw [h', MulEquiv.orderOf_eq, hb0ord]
  have hxA : x ∈ E ⊔ O := by rw [hx]; exact hE
  obtain ⟨o, hoO, hoxo⟩ := exists_mem_conj_mem_of_mem_sup_primeCore hstd hB hxA hxord
  have hOH : O ≤ H := by rw [hO]; exact Subgroup.map_subtype_le _
  have hOnorm : H ≤ Subgroup.normalizer (O : Set G) := by
    rw [hO]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
      (gLAPPrimeCoreOf_normal 3 H)
  have hb2E : B.b 2 ∈ E := by rw [← hB.1]; exact Subgroup.subset_closure (Set.mem_range_self 2)
  have hEH : E ≤ H := by
    rw [hH]
    exact (Subgroup.le_centralizer_iff_isMulCommutative.mpr hElem.1).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb2E))
  have hcommH : ∀ z ∈ H, z * B.b 2 = B.b 2 * z := fun z hz =>
    ((Subgroup.mem_centralizer_iff.mp hz) (B.b 2) (by simp)).symm
  have ho2 : o * B.b 2 = B.b 2 * o := hcommH o (hOH hoO)
  have hh2 : h * B.b 2 = B.b 2 * h := hcommH h hh
  have hgfix : (o * h) * B.b 2 * (o * h)⁻¹ = B.b 2 := conj_mul_fix_of_commute ho2 hh2
  have hg0 : (o * h) * b₀ * (o * h)⁻¹ = o * x * o⁻¹ := by rw [hx]; group
  have he1 : o * x * o⁻¹ ≠ 1 := by
    have hord : orderOf (o * x * o⁻¹) = 3 := by
      rw [show o * x * o⁻¹ = MulAut.conj o x from rfl, MulEquiv.orderOf_eq, hxord]
    exact fun h1 => by rw [h1, orderOf_one] at hord; omega
  have hline1 : IsConjLine b₀ (Subgroup.zpowers (o * x * o⁻¹)) := ⟨o * h, by rw [hg0]⟩
  have hline2 := isConjLine_zpowers_mul_of_recOutTwD5 hB.2.1 hrec hg0 hgfix
  obtain ⟨k, m, hkm⟩ := exists_zpow_mul_zpow_of_recOutTwD5 hB.2.1 hrec
    (by rw [hB.1]; exact hoxo) he1 hline1 hline2
  have hxeq : x = o⁻¹ * (b₀ ^ k * (B.b 2) ^ m) * o := by
    rw [show x = o⁻¹ * (o * x * o⁻¹) * o by group, hkm]
  rw [hxeq]
  exact conj_mem_sup_zpowers_sup (hEH hb0E) hoO hOnorm ho2

end CFSG.StandardType.FrameRoute.FS81

end

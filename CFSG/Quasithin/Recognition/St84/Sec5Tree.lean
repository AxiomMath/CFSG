module

public import CFSG.Quasithin.Recognition.St84.Sec5Basic
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteFinal
import CFSG.Quasithin.Recognition.GoldschmidtFan86OrbitTreeDef
import CFSG.Holt.Fixed

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

namespace Setup

abbrev N (Y : Setup Γ G) : Subgroup G := Subgroup.normalizer (Y.K : Set G)

@[expose] def Qs (Y : Setup Γ G) (i : ℤ) : Subgroup G :=
  Y.Q i ⊓ Subgroup.centralizer (Y.K : Set G)

@[expose] def J (Y : Setup Γ G) (i : ℤ) : Subgroup G :=
  oTwoPrime (Y.N ⊓ Y.Gi i)

theorem J_le_L (Y : Setup Γ G) (i : ℤ) : Y.J i ≤ Y.L i :=
  oTwoPrime_mono inf_le_right

theorem Qs_add (Y : Setup Γ G) (m i : ℤ) :
    Y.Qs (i + 2 * m) = (Y.Qs i).map (MulAut.conj (Y.τ ^ m)).toMonoidHom := by
  have hn : Y.τ ^ m ∈ Y.N := Y.N.zpow_mem Y.τ_norm m
  have hK : conjSub (Y.τ ^ m) Y.K = Y.K := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hcent : conjSub (Y.τ ^ m) (Subgroup.centralizer (Y.K : Set G)) =
      Subgroup.centralizer (Y.K : Set G) := by rw [← conjSub_centralizer, hK]
  unfold Setup.Qs
  rw [Y.Q_add m i]
  rw [show (Y.Q i ⊓ Subgroup.centralizer (Y.K : Set G)).map
        (MulAut.conj (Y.τ ^ m)).toMonoidHom
      = conjSub (Y.τ ^ m) (Y.Q i) ⊓
        conjSub (Y.τ ^ m) (Subgroup.centralizer (Y.K : Set G)) from
    conjSub_inf (Y.τ ^ m) _ _, hcent]

abbrev DtV (Y : Setup Γ G) : Type :=
  {v : V // Odd (Γ.dist (Y.vert 0) v) ∧ ∀ k ∈ Y.K, k • v = v}

@[expose] def dtGraph (Y : Setup Γ G) : SimpleGraph Y.DtV where
  Adj u v := u ≠ v ∧ ∃ w : V, Γ.Adj u.1 w ∧ Γ.Adj w v.1 ∧ ∀ k ∈ Y.K, k • w = w
  symm := ⟨fun u v h => by
    obtain ⟨hne, w, huw, hwv, hwK⟩ := h
    exact ⟨hne.symm, w, hwv.symm, huw.symm, hwK⟩⟩
  loopless := ⟨fun u h => by
    obtain ⟨hne, -⟩ := h
    exact hne rfl⟩

instance instMulActionDtV (Y : Setup Γ G) : MulAction ↥Y.N Y.DtV where
  smul n u :=
    ⟨(n : G) • u.1, by
      have hsum := IsTree.even_dist_add_dist_add_dist Y.hyp.isTree (Y.vert 0) u.1
        ((n : G) • u.1)
      obtain ⟨a, ha⟩ := u.2.1
      obtain ⟨b, hb⟩ := Y.hyp.preservesParts (n : G) u.1
      obtain ⟨c, hc⟩ := hsum
      exact ⟨c - a - b - 1, by omega⟩, by
      intro k hk
      have hconj : (n : G)⁻¹ * k * (n : G) ∈ Y.K :=
        ((Subgroup.mem_normalizer_iff''.mp n.2) k).mp hk
      calc k • ((n : G) • u.1)
          = (k * (n : G)) • u.1 := (mul_smul k (n : G) u.1).symm
        _ = ((n : G) * ((n : G)⁻¹ * k * (n : G))) • u.1 := by
            rw [show k * (n : G) = (n : G) * ((n : G)⁻¹ * k * (n : G)) by group]
        _ = (n : G) • (((n : G)⁻¹ * k * (n : G)) • u.1) :=
            mul_smul (n : G) ((n : G)⁻¹ * k * (n : G)) u.1
        _ = (n : G) • u.1 := by rw [u.2.2 ((n : G)⁻¹ * k * (n : G)) hconj]⟩
  one_smul u := Subtype.ext (one_smul G u.1)
  mul_smul m n u := Subtype.ext (mul_smul (m : G) (n : G) u.1)

@[expose] def dtBase (Y : Setup Γ G) : Y.DtV :=
  ⟨Y.vert 1, by
    refine ⟨?_, fun k hk => Y.K_fix k hk 1⟩
    rw [dist_eq_one_iff_adj.mpr (by simpa using Y.adj 0)]
    exact ⟨0, by norm_num⟩⟩

@[simp] theorem dtBase_val (Y : Setup Γ G) : (Y.dtBase).1 = Y.vert 1 := rfl

private theorem dtV_ne_vert_zero (Y : Setup Γ G) (u : Y.DtV) : u.1 ≠ Y.vert 0 := by
  intro h
  have h1 := u.2.1
  rw [h] at h1
  simp only [dist_self] at h1
  obtain ⟨m, hm⟩ := h1
  omega


theorem kfix_smul_iff (Y : Setup Γ G) {n : G} (hn : n ∈ Y.N) (w : V) :
    (∀ k ∈ Y.K, k • (n • w) = n • w) ↔ (∀ k ∈ Y.K, k • w = w) :=
  ⟨fun h => by
    simpa [CFSG.Holt.fixSet] using
      CFSG.Holt.smul_mem_fixSet_of_mem_normalizer (Ω := V) (inv_mem hn) h,
   fun h => CFSG.Holt.smul_mem_fixSet_of_mem_normalizer (Ω := V) hn h⟩

private theorem kfix_of_adj_dist_add_one (Y : Setup Γ G) {a x : V}
    (hax : Γ.Adj a x) (hdist : Γ.dist (Y.vert 0) a + 1 = Γ.dist (Y.vert 0) x)
    (hx : ∀ k ∈ Y.K, k • x = x) : ∀ k ∈ Y.K, k • a = a := by
  intro k hk
  have hkx : k • x = x := hx k hk
  have hdist' : Γ.dist (Y.vert 0) (k • a) + 1 = Γ.dist (Y.vert 0) x := by
    have h1 : Γ.dist (Y.vert 0) (k • a) = Γ.dist (Y.vert 0) a := by
      calc Γ.dist (Y.vert 0) (k • a) = Γ.dist (k • Y.vert 0) (k • a) := by
            rw [Y.K_fix k hk 0]
        _ = Γ.dist (Y.vert 0) a :=
            IsTree.dist_smul Y.hyp.isTree Y.hyp.adj_smul k (Y.vert 0) a
    rw [h1]
    exact hdist
  have hadj' : Γ.Adj (k • a) x := by
    rw [← hkx]
    exact (Y.hyp.adj_smul k a x).2 hax
  exact IsTree.eq_of_dist_succ Y.hyp.isTree hadj' hax hdist' hdist

private theorem exists_kfix_parent (Y : Setup Γ G) {x : V} (hx : x ≠ Y.vert 0)
    (hxK : ∀ k ∈ Y.K, k • x = x) :
    ∃ a : V, Γ.Adj a x ∧ Γ.dist (Y.vert 0) a + 1 = Γ.dist (Y.vert 0) x ∧
      (∀ k ∈ Y.K, k • a = a) := by
  have hpos : 0 < Γ.dist (Y.vert 0) x := Y.hyp.isTree.connected.pos_dist_of_ne (Ne.symm hx)
  obtain ⟨a, hax, hd⟩ := IsTree.exists_adj_dist_succ Y.hyp.isTree
    (u := Y.vert 0) (v := x) (n := Γ.dist (Y.vert 0) x - 1) (by omega)
  have hdist : Γ.dist (Y.vert 0) a + 1 = Γ.dist (Y.vert 0) x := by omega
  exact ⟨a, hax, hdist, kfix_of_adj_dist_add_one Y hax hdist hxK⟩

theorem dt_adj_smul (Y : Setup Γ G) (n : ↥Y.N) (u v : Y.DtV) :
    Y.dtGraph.Adj (n • u) (n • v) ↔ Y.dtGraph.Adj u v := by
  have hn : (n : G) ∈ Y.N := n.2
  constructor
  · rintro ⟨hne, w, huw, hwv, hwK⟩
    have huw' : Γ.Adj ((n : G) • u.1) w := huw
    have hwv' : Γ.Adj w ((n : G) • v.1) := hwv
    refine ⟨fun h => hne (by rw [h]), (n : G)⁻¹ • w, ?_, ?_, ?_⟩
    · exact (Y.hyp.adj_smul (n : G) u.1 ((n : G)⁻¹ • w)).mp (by simpa using huw')
    · exact (Y.hyp.adj_smul (n : G) ((n : G)⁻¹ • w) v.1).mp (by simpa using hwv')
    · exact (kfix_smul_iff Y (inv_mem hn) w).mpr hwK
  · rintro ⟨hne, w, huw, hwv, hwK⟩
    refine ⟨fun h => hne (MulAction.injective n h), (n : G) • w, ?_, ?_, ?_⟩
    · exact (Y.hyp.adj_smul (n : G) u.1 w).mpr huw
    · exact (Y.hyp.adj_smul (n : G) w v.1).mpr hwv
    · exact (kfix_smul_iff Y hn w).mpr hwK

private theorem dt_finite_stab (Y : Setup Γ G) (u : Y.DtV) :
    Finite (MulAction.stabilizer ↥Y.N u) := by
  haveI : Finite (MulAction.stabilizer G u.1) := Y.hyp.finite_stab u.1
  refine Finite.of_injective (f := fun n : MulAction.stabilizer ↥Y.N u =>
    (⟨(((n : ↥Y.N) : G)), ?_⟩ : MulAction.stabilizer G u.1)) ?_
  · refine MulAction.mem_stabilizer_iff.mpr ?_
    have h : (n : ↥Y.N) • u = u := n.2
    exact congrArg Subtype.val h
  · intro a b hab
    have h1 : ((a : ↥Y.N) : G) = ((b : ↥Y.N) : G) :=
      congrArg (fun z : MulAction.stabilizer G u.1 => (z : G)) hab
    exact Subtype.ext (Subtype.ext h1)

private theorem exists_conj_K_eq_K (Y : Setup Γ G) {u w : V} (huw : Γ.Adj u w)
    (huK : ∀ k ∈ Y.K, k • u = u) (hwK : ∀ k ∈ Y.K, k • w = w) {g₀ : G}
    (hg₀w : g₀ • Y.vert 0 = w) (hg₀u : g₀ • Y.vert 1 = u) :
    ∃ n ∈ MulAction.stabilizer G u ⊓ MulAction.stabilizer G w,
      Y.K = conjSub n⁻¹ (conjSub g₀ Y.K) := by
  set F : Subgroup G := MulAction.stabilizer G u ⊓ MulAction.stabilizer G w with hF
  set S : Subgroup G := pCoreOf 2 F with hS
  have hSF : S ≤ F := CFSG.LieType.BorelTits.pCoreOf_le 2 F
  have hFnormal : F ≤ Subgroup.normalizer (S : Set G) := by
    have h := CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 F
    rwa [← hS] at h
  haveI : Finite ↥F := finite_of_le_stabilizer Y.hyp (H := F) inf_le_left
  have hSylow : IsSylowTwoOf S F := by
    have h := isSylowTwoOf_pCoreOf_edgeStab Y.hyp huw
    rwa [← hS, ← hF] at h
  have hSnorm : (S.subgroupOf F).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hFnormal
  have hconjF : conjSub g₀ (Y.Gi 0 ⊓ Y.Gi 1) = F := by
    rw [hF, conjSub_inf, (stabilizer_smul_eq_conjSub g₀ (Y.vert 0)).symm,
      (stabilizer_smul_eq_conjSub g₀ (Y.vert 1)).symm, hg₀w, hg₀u, inf_comm]
  have hKF : Y.K ≤ F := by
    intro k hk
    exact ⟨MulAction.mem_stabilizer_iff.mpr (huK k hk),
      MulAction.mem_stabilizer_iff.mpr (hwK k hk)⟩
  have hKgF : conjSub g₀ Y.K ≤ F := by
    rw [← hconjF]
    exact conjSub_mono g₀ Y.K_le_inf
  have hSsupKg : S ⊔ conjSub g₀ Y.K = F := by
    have h := congrArg (conjSub g₀) Y.K_sup
    rw [conjSub_sup, (pCoreOf_conjSub g₀ (Y.Gi 0 ⊓ Y.Gi 1)).symm, hconjF] at h
    rw [← hS] at h
    rw [sup_comm]
    exact h
  have hSinfKg : S ⊓ conjSub g₀ Y.K = ⊥ := by
    have h := congrArg (conjSub g₀) Y.K_inf
    rw [conjSub_inf, (pCoreOf_conjSub g₀ (Y.Gi 0 ⊓ Y.Gi 1)).symm, hconjF,
      conjSub_bot] at h
    rw [← hS] at h
    rw [inf_comm]
    exact h
  have hSinfK : S ⊓ Y.K = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_odd_of_isPGroup Y.odd_card_K hSylow.2.1
  have hcardF : Nat.card ↥F = Nat.card ↥Y.K * Nat.card ↥S := by
    have hnormalKg : conjSub g₀ Y.K ≤ Subgroup.normalizer (S : Set G) :=
      hKgF.trans hFnormal
    have hdisj : Disjoint S (conjSub g₀ Y.K) := by
      rw [disjoint_iff, hSinfKg]
    have h1 := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      S (conjSub g₀ Y.K) hnormalKg hdisj
    rw [hSsupKg, card_conjSub] at h1
    rw [h1, mul_comm]
  have hsupK : S ⊔ Y.K = F := by
    have hnormalK : Y.K ≤ Subgroup.normalizer (S : Set G) := hKF.trans hFnormal
    have hdisj : Disjoint S Y.K := by
      rw [disjoint_iff, hSinfK]
    have h2 := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      S Y.K hnormalK hdisj
    have hle : S ⊔ Y.K ≤ F := sup_le hSF hKF
    have hcard : Nat.card ↥F ≤ Nat.card ↥(S ⊔ Y.K) := by rw [h2, mul_comm, hcardF]
    exact Subgroup.eq_of_le_of_card_ge hle hcard
  obtain ⟨n, hnS, hn⟩ := exists_conj_eq_of_complement hSF hSnorm hSylow hKgF hKF
    hSsupKg hsupK hSinfKg hSinfK
  exact ⟨n, hSF hnS, hn⟩

theorem exists_normalizer_K_edge (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {u w : V}
    (hu1 : Odd (Γ.dist (Y.vert 0) u)) (huK : ∀ k ∈ Y.K, k • u = u)
    (huw : Γ.Adj u w) (hwK : ∀ k ∈ Y.K, k • w = w) :
    ∃ g ∈ Y.N, g • Y.vert 1 = u ∧ g • Y.vert 0 = w := by
  have hadj0 : Γ.Adj (Y.vert 0) (Y.vert 1) := by simpa using Y.adj 0
  obtain ⟨g₀, -, hg₀ | hg₀⟩ := Y.hyp.edgeTrans (Y.vert 0) (Y.vert 1) u w hadj0 huw
  · exfalso
    have hpar := Y.hyp.preservesParts g₀ (Y.vert 0)
    rw [hg₀.1] at hpar
    exact Nat.not_even_iff_odd.mpr hu1 hpar
  have hg₀w : g₀ • Y.vert 0 = w := hg₀.1
  have hg₀u : g₀ • Y.vert 1 = u := hg₀.2
  obtain ⟨n, hnF, hn⟩ := exists_conj_K_eq_K Y huw huK hwK hg₀w hg₀u
  have hnu : n⁻¹ • u = u := by
    simpa using (congrArg (fun z => n⁻¹ • z)
      (MulAction.mem_stabilizer_iff.mp hnF.1)).symm
  have hnw : n⁻¹ • w = w := by
    simpa using (congrArg (fun z => n⁻¹ • z)
      (MulAction.mem_stabilizer_iff.mp hnF.2)).symm
  refine ⟨n⁻¹ * g₀, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conjSub (n⁻¹ * g₀) Y.K = Y.K
    rw [conjSub_mul, ← hn]
  · calc (n⁻¹ * g₀) • Y.vert 1 = n⁻¹ • (g₀ • Y.vert 1) := mul_smul _ _ _
      _ = n⁻¹ • u := by rw [hg₀u]
      _ = u := hnu
  · calc (n⁻¹ * g₀) • Y.vert 0 = n⁻¹ • (g₀ • Y.vert 0) := mul_smul _ _ _
      _ = n⁻¹ • w := by rw [hg₀w]
      _ = w := hnw

theorem card_fixed_nbrs_of_even (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {u w : V}
    (hu1 : Odd (Γ.dist (Y.vert 0) u)) (huK : ∀ k ∈ Y.K, k • u = u)
    (huw : Γ.Adj u w) (hwK : ∀ k ∈ Y.K, k • w = w) :
    Nat.card {x : V // Γ.Adj w x ∧ ∀ k ∈ Y.K, k • x = x} = 2 := by
  obtain ⟨g, hgN, hgu, hgw⟩ := Y.exists_normalizer_K_edge H hu1 huK huw hwK
  have hinvw : g⁻¹ • w = Y.vert 0 := by rw [← hgw, inv_smul_smul]
  have hn0 : 2 ≤ Y.n 0 := by rw [H.n_zero]; exact H.two_le
  obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Y.K_ne_bot H)
  have hkK : (k : G) ∈ Y.K := k.2
  have hk1' : (k : G) ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hkKi : (k : G) ∈ Y.Ki 0 := ⟨hkK, Y.K_le_L_zero H hkK⟩
  let x₀ : {x : V // Γ.Adj (Y.vert 0) x ∧ ∀ j ∈ Y.K, j • x = x} :=
    ⟨Y.vert (-1), by
      refine ⟨?_, fun j hj => Y.K_fix j hj (-1)⟩
      have h := Y.adj (-1)
      rw [show (-1 : ℤ) + 1 = 0 by norm_num] at h
      exact h.symm⟩
  have hbase : Nat.card {x : V // Γ.Adj (Y.vert 0) x ∧ ∀ j ∈ Y.K, j • x = x} = 2 := by
    rw [Nat.card_eq_two_iff' x₀]
    let x₁ : {x : V // Γ.Adj (Y.vert 0) x ∧ ∀ j ∈ Y.K, j • x = x} :=
      ⟨Y.vert 1, by
        refine ⟨?_, fun j hj => Y.K_fix j hj 1⟩
        simpa using Y.adj 0⟩
    refine ⟨x₁, ?_, ?_⟩
    · intro h
      have hv : Y.vert 1 = Y.vert (-1) := congrArg Subtype.val h
      have h2 := Y.vert_injective hv
      norm_num at h2
    · intro y hy
      have hyK : (k : G) • y.1 = y.1 := y.2.2 k hkK
      have htf := (Y.torus_fixed 0 hn0 hkKi hk1' y.1 y.2.1).mp hyK
      simp only [zero_sub, zero_add] at htf
      rcases htf with h | h
      · exact absurd (Subtype.ext h) hy
      · exact Subtype.ext h
  rw [← hbase]
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨g⁻¹ • x.1, ?_⟩
      invFun := fun y => ⟨g • y.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨?_, (kfix_smul_iff Y (inv_mem hgN) x.1).mpr x.2.2⟩
    have h1 : Γ.Adj (g⁻¹ • w) (g⁻¹ • x.1) :=
      (Y.hyp.adj_smul g (g⁻¹ • w) (g⁻¹ • x.1)).mp (by simpa using x.2.1)
    rwa [hinvw] at h1
  · refine ⟨?_, (kfix_smul_iff Y hgN y.1).mpr y.2.2⟩
    have h1 : Γ.Adj (g • Y.vert 0) (g • y.1) :=
      (Y.hyp.adj_smul g (Y.vert 0) y.1).mpr y.2.1
    rwa [hgw] at h1
  · intro x
    exact Subtype.ext (by simp)
  · intro y
    exact Subtype.ext (by simp)

theorem eq_of_kfix_adj_ne (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {u w y y' : V}
    (hu1 : Odd (Γ.dist (Y.vert 0) u)) (huK : ∀ k ∈ Y.K, k • u = u)
    (huw : Γ.Adj u w) (hwK : ∀ k ∈ Y.K, k • w = w)
    (hyw : Γ.Adj w y) (hyK : ∀ k ∈ Y.K, k • y = y) (hyu : y ≠ u)
    (hy'w : Γ.Adj w y') (hy'K : ∀ k ∈ Y.K, k • y' = y') (hy'u : y' ≠ u) :
    y = y' := by
  have hcard : Nat.card {x : V // Γ.Adj w x ∧ ∀ k ∈ Y.K, k • x = x} = 2 :=
    Y.card_fixed_nbrs_of_even H hu1 huK huw hwK
  let x₀ : {x : V // Γ.Adj w x ∧ ∀ k ∈ Y.K, k • x = x} := ⟨u, huw.symm, huK⟩
  rw [Nat.card_eq_two_iff' x₀] at hcard
  obtain ⟨z, -, huniq⟩ := hcard
  have hy : (⟨y, hyw, hyK⟩ : {x : V // Γ.Adj w x ∧ ∀ k ∈ Y.K, k • x = x}) ≠ x₀ := by
    intro h
    exact hyu (congrArg Subtype.val h)
  have hy' : (⟨y', hy'w, hy'K⟩ : {x : V // Γ.Adj w x ∧ ∀ k ∈ Y.K, k • x = x}) ≠ x₀ := by
    intro h
    exact hy'u (congrArg Subtype.val h)
  exact (congrArg Subtype.val (huniq _ hy)).trans
    (congrArg Subtype.val (huniq _ hy')).symm

private theorem dt_vertex_trans (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    ∀ u v : Y.DtV, ∃ n : ↥Y.N, n • u = v := by
  intro u v
  have hu0 := dtV_ne_vert_zero Y u
  obtain ⟨w, hwu, -, hwK⟩ := exists_kfix_parent Y hu0 u.2.2
  obtain ⟨g, hgN, hgu, -⟩ := Y.exists_normalizer_K_edge H u.2.1 u.2.2 hwu.symm hwK
  have hv0 := dtV_ne_vert_zero Y v
  obtain ⟨z, hzv, -, hzK⟩ := exists_kfix_parent Y hv0 v.2.2
  obtain ⟨h, hhN, hhv, -⟩ := Y.exists_normalizer_K_edge H v.2.1 v.2.2 hzv.symm hzK
  refine ⟨⟨h * g⁻¹, Y.N.mul_mem hhN (Y.N.inv_mem hgN)⟩, ?_⟩
  apply Subtype.ext
  show ((h : G) * (g : G)⁻¹) • u.1 = v.1
  rw [mul_smul, show (g : G)⁻¹ • u.1 = Y.vert 1 by rw [← hgu, inv_smul_smul], hhv]

private theorem dt_loc_trans (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (u : Y.DtV) {a b : Y.DtV}
    (ha : Y.dtGraph.Adj u a) (hb : Y.dtGraph.Adj u b) :
    ∃ n ∈ MulAction.stabilizer ↥Y.N u, n • a = b := by
  have hu0 := dtV_ne_vert_zero Y u
  obtain ⟨w, hwu, -, hwK⟩ := exists_kfix_parent Y hu0 u.2.2
  obtain ⟨g, hgN, hgu, -⟩ := Y.exists_normalizer_K_edge H u.2.1 u.2.2 hwu.symm hwK
  let ginv : ↥Y.N := ⟨g⁻¹, Y.N.inv_mem hgN⟩
  have hgu' : ginv • u = Y.dtBase := by
    apply Subtype.ext
    show (g : G)⁻¹ • u.1 = Y.vert 1
    rw [← hgu, inv_smul_smul]
  have ha' : Y.dtGraph.Adj Y.dtBase (ginv • a) := by
    rw [← hgu']
    exact (Y.dt_adj_smul ginv u a).mpr ha
  have hb' : Y.dtGraph.Adj Y.dtBase (ginv • b) := by
    rw [← hgu']
    exact (Y.dt_adj_smul ginv u b).mpr hb
  have ha'_ne : (ginv • a).1 ≠ Y.vert 1 := fun h => ha'.1 (Subtype.ext h.symm)
  have hb'_ne : (ginv • b).1 ≠ Y.vert 1 := fun h => hb'.1 (Subtype.ext h.symm)
  obtain ⟨δ, hδ1, hδa, hδK⟩ := ha'.2
  obtain ⟨δ', hδ'1, hδ'b, hδ'K⟩ := hb'.2
  by_cases hδ : δ = δ'
  · have hab : (ginv • a).1 = (ginv • b).1 :=
      eq_of_kfix_adj_ne Y H Y.dtBase.2.1 Y.dtBase.2.2 hδ1 hδK hδa (ginv • a).2.2 ha'_ne
        (hδ ▸ hδ'b) (ginv • b).2.2 hb'_ne
    have hsum : ginv • a = ginv • b := Subtype.ext hab
    have hab2 : a = b := by
      have h := congrArg (fun z : Y.DtV => (⟨g, hgN⟩ : ↥Y.N) • z) hsum
      simpa using h
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    simp [hab2]
  · obtain ⟨x, hx, hxδ⟩ := Y.exists_normalizer_K_one H hδ1 hδ'1
    have hxN : x ∈ Y.N := hx.1
    have hxfix1 : x • Y.vert 1 = Y.vert 1 := MulAction.mem_stabilizer_iff.mp hx.2
    have hδ'1' : Γ.Adj (Y.vert 1) δ' := by
      have h : Γ.Adj (x • Y.vert 1) (x • δ) := (Y.hyp.adj_smul x (Y.vert 1) δ).mpr hδ1
      rwa [hxδ, hxfix1] at h
    have hδ'a : Γ.Adj δ' (x • (ginv • a).1) := by
      have h : Γ.Adj (x • δ) (x • (ginv • a).1) := (Y.hyp.adj_smul x δ (ginv • a).1).mpr hδa
      rwa [hxδ] at h
    have hyna : x • (ginv • a).1 ≠ Y.vert 1 := by
      intro h
      apply ha'_ne
      have h2 : x • (ginv • a).1 = x • Y.vert 1 := by rw [h, hxfix1]
      exact MulAction.injective x h2
    have hxa : x • (ginv • a).1 = (ginv • b).1 :=
      eq_of_kfix_adj_ne Y H Y.dtBase.2.1 Y.dtBase.2.2 hδ'1' hδ'K hδ'a
        ((kfix_smul_iff Y hxN (ginv • a).1).mpr (ginv • a).2.2) hyna
        hδ'b (ginv • b).2.2 hb'_ne
    let gN : ↥Y.N := ⟨g, hgN⟩
    let xN : ↥Y.N := ⟨x, hxN⟩
    refine ⟨gN * xN * gN⁻¹, ?_, ?_⟩
    · refine MulAction.mem_stabilizer_iff.mpr ?_
      apply Subtype.ext
      show ((gN * xN * gN⁻¹ : ↥Y.N) : G) • u.1 = u.1
      rw [show ((gN * xN * gN⁻¹ : ↥Y.N) : G) = (g : G) * (x : G) * (g : G)⁻¹ from rfl,
        mul_smul, mul_smul, show (g : G)⁻¹ • u.1 = Y.vert 1 by rw [← hgu, inv_smul_smul],
        hxfix1, hgu]
    · apply Subtype.ext
      show ((gN * xN * gN⁻¹ : ↥Y.N) : G) • a.1 = b.1
      rw [show ((gN * xN * gN⁻¹ : ↥Y.N) : G) = (g : G) * (x : G) * (g : G)⁻¹ from rfl,
        mul_smul, mul_smul]
      rw [show (x : G) • ((g : G)⁻¹ • a.1) = (ginv • b).1 from hxa]
      rw [show (g : G) • (ginv • b).1 = b.1 by
        rw [show (ginv • b).1 = (g : G)⁻¹ • b.1 from rfl, smul_inv_smul]]

private noncomputable def gate (Y : Setup Γ G) {u v : Y.DtV} (h : Y.dtGraph.Adj u v) : V :=
  Classical.choose h.2

private theorem gate_spec (Y : Setup Γ G) {u v : Y.DtV} (h : Y.dtGraph.Adj u v) :
    Γ.Adj u.1 (Y.gate h) ∧ Γ.Adj (Y.gate h) v.1 ∧ ∀ k ∈ Y.K, k • Y.gate h = Y.gate h :=
  Classical.choose_spec h.2

theorem even_dist_of_adj_odd (Y : Setup Γ G) {a b : V}
    (hb : Odd (Γ.dist (Y.vert 0) b)) (hab : Γ.Adj a b) : Even (Γ.dist (Y.vert 0) a) := by
  obtain ⟨m, hm⟩ := hb
  rcases IsTree.dist_adj_cases Y.hyp.isTree (r := Y.vert 0) hab with h | h
  · exact ⟨m, by omega⟩
  · exact ⟨m + 1, by omega⟩

theorem odd_dist_of_adj_even (Y : Setup Γ G) {a b : V}
    (ha : Even (Γ.dist (Y.vert 0) a)) (hab : Γ.Adj a b) : Odd (Γ.dist (Y.vert 0) b) := by
  obtain ⟨m, hm⟩ := ha
  rcases IsTree.dist_adj_cases Y.hyp.isTree (r := Y.vert 0) hab with h | h
  · exact ⟨m, by omega⟩
  · rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; omega
    · exact ⟨m - 1, by omega⟩

theorem odd_dist_vert_of_even (Y : Setup Γ G) (o : V) {k : ℕ} (hk : Odd k)
    (h0 : Even (Γ.dist o (Y.vert 0))) : Odd (Γ.dist o (Y.vert (k : ℤ))) := by
  have hstart : Odd (Γ.dist o ((Y.line.arc 0 k).vert 0) + k) := by
    simpa [Line.arc] using h0.add_odd hk
  have h := (CFSG.Quasithin.St84.odd_dist_vert_iff Y.hyp.isTree (Y.line.arc 0 k) o).mpr hstart
  simpa [Line.arc] using h

theorem odd_dist_vert_succ_of_odd (Y : Setup Γ G) (o : V) {k : ℕ} (hk : Odd k)
    (h0 : Odd (Γ.dist o (Y.vert 0))) :
    Odd (Γ.dist o (Y.vert ((k : ℤ) + 1))) := by
  have hiff : Odd (Γ.dist o (Y.vert 1)) ↔ Odd (Γ.dist o (Y.vert 0) + 1) := by
    simpa [Line.arc] using
      CFSG.Quasithin.St84.odd_dist_vert_iff Y.hyp.isTree (Y.line.arc 0 1) o
  have h1odd : ¬ Odd (Γ.dist o (Y.vert 1)) := by
    rw [hiff]
    simpa using (Nat.not_odd_iff_even.mpr h0.add_one)
  have h1 : Even (Γ.dist o (Y.vert 1)) := Nat.not_odd_iff_even.mp h1odd
  have h := odd_dist_vert_of_even (Y.shift 1) o hk (by simpa [Setup.shift_vert] using h1)
  simpa [Setup.shift_vert] using h

private theorem exists_other_nbr (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {δ : V}
    (hδ1 : Γ.Adj (Y.vert 1) δ) (hδK : ∀ k ∈ Y.K, k • δ = δ) :
    ∃! y : V, Γ.Adj δ y ∧ (∀ k ∈ Y.K, k • y = y) ∧ y ≠ Y.vert 1 := by
  have hcard : Nat.card {x : V // Γ.Adj δ x ∧ ∀ k ∈ Y.K, k • x = x} = 2 :=
    Y.card_fixed_nbrs_of_even H Y.dtBase.2.1 Y.dtBase.2.2 hδ1 hδK
  let x₀ : {x : V // Γ.Adj δ x ∧ ∀ k ∈ Y.K, k • x = x} := ⟨Y.vert 1, hδ1.symm, Y.dtBase.2.2⟩
  rw [Nat.card_eq_two_iff' x₀] at hcard
  obtain ⟨z, hz, huniq⟩ := hcard
  refine ⟨z.1, ⟨z.2.1, z.2.2, fun h => hz (Subtype.ext h)⟩, ?_⟩
  rintro y ⟨hy1, hy2, hy3⟩
  refine congrArg Subtype.val (huniq ⟨y, hy1, hy2⟩ ?_)
  intro h
  exact hy3 (congrArg Subtype.val h)

private noncomputable def otherNbr (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {δ : V}
    (hδ1 : Γ.Adj (Y.vert 1) δ) (hδK : ∀ k ∈ Y.K, k • δ = δ) : V :=
  Classical.choose (exists_other_nbr Y H hδ1 hδK)

private theorem otherNbr_spec (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {δ : V}
    (hδ1 : Γ.Adj (Y.vert 1) δ) (hδK : ∀ k ∈ Y.K, k • δ = δ) :
    Γ.Adj δ (Y.otherNbr H hδ1 hδK) ∧
      (∀ k ∈ Y.K, k • Y.otherNbr H hδ1 hδK = Y.otherNbr H hδ1 hδK) ∧
      Y.otherNbr H hδ1 hδK ≠ Y.vert 1 :=
  (Classical.choose_spec (exists_other_nbr Y H hδ1 hδK)).1

private theorem finite_nbrSet (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (u : Y.DtV) :
    Finite (Y.dtGraph.neighborSet u) := by
  haveI : Finite (Γ.neighborSet u.1) := Y.hyp.finite_neighborSet u.1
  refine Finite.of_injective
    (f := fun v : Y.dtGraph.neighborSet u =>
      (⟨Y.gate v.2, (gate_spec Y v.2).1⟩ : Γ.neighborSet u.1)) ?_
  intro v v' hv
  have hg : Y.gate v.2 = Y.gate v'.2 := congrArg Subtype.val hv
  have hvne : v.1.1 ≠ u.1 := fun h => v.2.1 (Subtype.ext h.symm)
  have hv'ne : v'.1.1 ≠ u.1 := fun h => v'.2.1 (Subtype.ext h.symm)
  have h1 : v.1.1 = v'.1.1 :=
    eq_of_kfix_adj_ne Y H u.2.1 u.2.2 (gate_spec Y v.2).1 (gate_spec Y v.2).2.2
      (gate_spec Y v.2).2.1 v.1.2.2 hvne
      (hg ▸ (gate_spec Y v'.2).2.1) v'.1.2.2 hv'ne
  exact Subtype.ext (Subtype.ext h1)

private theorem card_nbr_dtBase (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Nat.card (Y.dtGraph.neighborSet Y.dtBase) = 3 := by
  have hval : Nat.card (Γ.neighborSet (Y.vert 1)) = 3 := by
    have h := (Y.hyp.valency (Y.vert 1)).2
    rw [show nOf Γ (Y.vert 1) = Y.n 1 from rfl, H.n_one] at h
    simpa using h
  haveI : Finite (Γ.neighborSet (Y.vert 1)) := Y.hyp.finite_neighborSet (Y.vert 1)
  haveI : Finite (Y.dtGraph.neighborSet Y.dtBase) := finite_nbrSet Y H Y.dtBase
  have hle1 : Nat.card (Y.dtGraph.neighborSet Y.dtBase) ≤
      Nat.card (Γ.neighborSet (Y.vert 1)) := by
    refine Nat.card_le_card_of_injective
      (f := fun v : Y.dtGraph.neighborSet Y.dtBase =>
        (⟨Y.gate v.2, (gate_spec Y v.2).1⟩ : Γ.neighborSet (Y.vert 1))) ?_
    intro v v' hv
    have hg : Y.gate v.2 = Y.gate v'.2 := congrArg Subtype.val hv
    have hvne : v.1.1 ≠ Y.vert 1 := fun h => v.2.1 (Subtype.ext h.symm)
    have hv'ne : v'.1.1 ≠ Y.vert 1 := fun h => v'.2.1 (Subtype.ext h.symm)
    have h1 : v.1.1 = v'.1.1 :=
      eq_of_kfix_adj_ne Y H Y.dtBase.2.1 Y.dtBase.2.2 (gate_spec Y v.2).1 (gate_spec Y v.2).2.2
        (gate_spec Y v.2).2.1 v.1.2.2 hvne
        (hg ▸ (gate_spec Y v'.2).2.1) v'.1.2.2 hv'ne
    exact Subtype.ext (Subtype.ext h1)
  have hle2 : Nat.card (Γ.neighborSet (Y.vert 1)) ≤
      Nat.card (Y.dtGraph.neighborSet Y.dtBase) := by
    refine Nat.card_le_card_of_injective
      (f := fun δ : Γ.neighborSet (Y.vert 1) =>
        (⟨⟨Y.otherNbr H δ.2 (Y.K_fixes_nbr_one H δ.2),
            odd_dist_of_adj_even Y (even_dist_of_adj_odd Y Y.dtBase.2.1 δ.2.symm)
              (otherNbr_spec Y H δ.2 (Y.K_fixes_nbr_one H δ.2)).1,
            (otherNbr_spec Y H δ.2 (Y.K_fixes_nbr_one H δ.2)).2.1⟩,
          ⟨fun h => (otherNbr_spec Y H δ.2 (Y.K_fixes_nbr_one H δ.2)).2.2
              (congrArg Subtype.val h).symm,
            δ.1, δ.2, (otherNbr_spec Y H δ.2 (Y.K_fixes_nbr_one H δ.2)).1,
            Y.K_fixes_nbr_one H δ.2⟩⟩ : Y.dtGraph.neighborSet Y.dtBase)) ?_
    intro δ δ' hδ
    have hy : Y.otherNbr H δ.2 (Y.K_fixes_nbr_one H δ.2) =
        Y.otherNbr H δ'.2 (Y.K_fixes_nbr_one H δ'.2) := by
      have h := congrArg (fun z : Y.dtGraph.neighborSet Y.dtBase => z.1.1) hδ
      simpa using h
    apply Subtype.ext
    exact common_nbr_unique Y.hyp.isTree
      (otherNbr_spec Y H δ.2 (Y.K_fixes_nbr_one H δ.2)).2.2.symm δ.2
      (otherNbr_spec Y H δ.2 (Y.K_fixes_nbr_one H δ.2)).1.symm δ'.2
      (by rw [hy]; exact (otherNbr_spec Y H δ'.2 (Y.K_fixes_nbr_one H δ'.2)).1.symm)
  omega

theorem dt_card_nbr (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (u : Y.DtV) :
    Nat.card (Y.dtGraph.neighborSet u) = 3 := by
  have hu0 := dtV_ne_vert_zero Y u
  obtain ⟨w, hwu, -, hwK⟩ := exists_kfix_parent Y hu0 u.2.2
  obtain ⟨g, hgN, hgu, -⟩ := Y.exists_normalizer_K_edge H u.2.1 u.2.2 hwu.symm hwK
  let gN : ↥Y.N := ⟨g, hgN⟩
  have hgN_dtBase : gN • Y.dtBase = u := by
    apply Subtype.ext
    show (g : G) • Y.vert 1 = u.1
    exact hgu
  have hgN'_u : gN⁻¹ • u = Y.dtBase := by
    rw [← hgN_dtBase, inv_smul_smul]
  haveI : Finite (Y.dtGraph.neighborSet Y.dtBase) := finite_nbrSet Y H Y.dtBase
  haveI : Finite (Y.dtGraph.neighborSet u) := finite_nbrSet Y H u
  have hle1 : Nat.card (Y.dtGraph.neighborSet u) ≤
      Nat.card (Y.dtGraph.neighborSet Y.dtBase) := by
    refine Nat.card_le_card_of_injective
      (f := fun v : Y.dtGraph.neighborSet u =>
        (⟨gN⁻¹ • v.1, ?_⟩ : Y.dtGraph.neighborSet Y.dtBase)) ?_
    · rw [← hgN'_u]
      exact (Y.dt_adj_smul gN⁻¹ u v.1).mpr v.2
    · intro a b hab
      have h := congrArg (fun z : Y.dtGraph.neighborSet Y.dtBase => gN • z.1) hab
      apply Subtype.ext
      simpa using h
  have hle2 : Nat.card (Y.dtGraph.neighborSet Y.dtBase) ≤
      Nat.card (Y.dtGraph.neighborSet u) := by
    refine Nat.card_le_card_of_injective
      (f := fun v : Y.dtGraph.neighborSet Y.dtBase =>
        (⟨gN • v.1, ?_⟩ : Y.dtGraph.neighborSet u)) ?_
    · rw [← hgN_dtBase]
      exact (Y.dt_adj_smul gN Y.dtBase v.1).mpr v.2
    · intro a b hab
      have h := congrArg (fun z : Y.dtGraph.neighborSet u => gN⁻¹ • z.1) hab
      apply Subtype.ext
      simpa using h
  have h3 := card_nbr_dtBase Y H
  omega

private theorem kfix_nbrs_even (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {w : V}
    (hw0 : w ≠ Y.vert 0) (hweven : Even (Γ.dist (Y.vert 0) w))
    (hwK : ∀ k ∈ Y.K, k • w = w) :
    ∃ p q : V, Γ.Adj p w ∧ Γ.Adj q w ∧ p ≠ q ∧
      (∀ k ∈ Y.K, k • p = p) ∧ (∀ k ∈ Y.K, k • q = q) ∧
      Γ.dist (Y.vert 0) p + 1 = Γ.dist (Y.vert 0) w ∧
      Γ.dist (Y.vert 0) w + 1 = Γ.dist (Y.vert 0) q ∧
      (∀ x : V, Γ.Adj w x → (∀ k ∈ Y.K, k • x = x) → x = p ∨ x = q) := by
  obtain ⟨p, hpw, hpdist, hpK⟩ := exists_kfix_parent Y hw0 hwK
  have hpod : Odd (Γ.dist (Y.vert 0) p) := odd_dist_of_adj_even Y hweven hpw.symm
  have hcard : Nat.card {x : V // Γ.Adj w x ∧ ∀ k ∈ Y.K, k • x = x} = 2 :=
    Y.card_fixed_nbrs_of_even H hpod hpK hpw hwK
  let x₀ : {x : V // Γ.Adj w x ∧ ∀ k ∈ Y.K, k • x = x} := ⟨p, hpw.symm, hpK⟩
  rw [Nat.card_eq_two_iff' x₀] at hcard
  obtain ⟨z, hz, huniq⟩ := hcard
  have hzK : ∀ k ∈ Y.K, k • z.1 = z.1 := z.2.2
  have hz1 : Γ.dist (Y.vert 0) w + 1 = Γ.dist (Y.vert 0) z.1 := by
    rcases IsTree.dist_adj_cases Y.hyp.isTree (r := Y.vert 0) z.2.1 with h | h
    · exact h.symm
    · exfalso
      have hzp : z.1 = p :=
        IsTree.eq_of_dist_succ Y.hyp.isTree z.2.1.symm hpw h.symm hpdist
      exact hz (Subtype.ext hzp)
  have hzp : z.1 ≠ p := fun h => hz (Subtype.ext h)
  refine ⟨p, z.1, hpw, z.2.1.symm, hzp.symm, hpK, hzK, hpdist, hz1, ?_⟩
  intro x hxw hxK
  by_cases hxx : (⟨x, hxw, hxK⟩ : {x : V // Γ.Adj w x ∧ ∀ k ∈ Y.K, k • x = x}) = x₀
  · exact Or.inl (congrArg Subtype.val hxx)
  · exact Or.inr (congrArg Subtype.val (huniq _ hxx))

private theorem dt_adj_height_cases (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {p q : Y.DtV}
    (hpq : Y.dtGraph.Adj p q) :
    (Γ.dist (Y.vert 0) p.1 = 1 ∧ Γ.dist (Y.vert 0) q.1 = 1) ∨
      Γ.dist (Y.vert 0) p.1 + 2 = Γ.dist (Y.vert 0) q.1 ∨
      Γ.dist (Y.vert 0) q.1 + 2 = Γ.dist (Y.vert 0) p.1 := by
  by_cases hw : Y.gate hpq = Y.vert 0
  · left
    have h1 : Γ.Adj (Y.vert 0) p.1 := by
      have h := (gate_spec Y hpq).1.symm
      rwa [hw] at h
    have h2 : Γ.Adj (Y.vert 0) q.1 := by
      have h := (gate_spec Y hpq).2.1
      rwa [hw] at h
    exact ⟨dist_eq_one_iff_adj.mpr h1, dist_eq_one_iff_adj.mpr h2⟩
  · have hweven : Even (Γ.dist (Y.vert 0) (Y.gate hpq)) :=
      even_dist_of_adj_odd Y p.2.1 (gate_spec Y hpq).1.symm
    obtain ⟨p', q', hp'w, hq'w, hpq'ne, hp'K, hq'K, hp'd, hq'd, hclass⟩ :=
      kfix_nbrs_even Y H hw hweven (gate_spec Y hpq).2.2
    have hp_mem : p.1 = p' ∨ p.1 = q' := hclass p.1 (gate_spec Y hpq).1.symm p.2.2
    have hq_mem : q.1 = p' ∨ q.1 = q' := hclass q.1 (gate_spec Y hpq).2.1 q.2.2
    rcases hp_mem with hp | hp <;> rcases hq_mem with hq | hq
    · exact absurd (hp.trans hq.symm) (fun h => hpq.1 (Subtype.ext h))
    · right; left; rw [hp, hq]; omega
    · right; right; rw [hp, hq]; omega
    · exact absurd (hp.trans hq.symm) (fun h => hpq.1 (Subtype.ext h))

private theorem dt_unique_height (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {u z z' : Y.DtV}
    (hz : Y.dtGraph.Adj u z) (hz' : Y.dtGraph.Adj u z')
    (hz2 : Γ.dist (Y.vert 0) z.1 + 2 = Γ.dist (Y.vert 0) u.1)
    (hz'2 : Γ.dist (Y.vert 0) z'.1 + 2 = Γ.dist (Y.vert 0) u.1) :
    z = z' := by
  have hw0 : Y.gate hz ≠ Y.vert 0 := by
    intro h
    have h1 : Γ.dist (Y.vert 0) u.1 = 1 := by
      rw [dist_eq_one_iff_adj]
      have hadj := (gate_spec Y hz).1.symm
      rwa [h] at hadj
    omega
  have hw0' : Y.gate hz' ≠ Y.vert 0 := by
    intro h
    have h1 : Γ.dist (Y.vert 0) u.1 = 1 := by
      rw [dist_eq_one_iff_adj]
      have hadj := (gate_spec Y hz').1.symm
      rwa [h] at hadj
    omega
  have hd : Γ.dist (Y.vert 0) (Y.gate hz) + 1 = Γ.dist (Y.vert 0) u.1 := by
    rcases IsTree.dist_adj_cases Y.hyp.isTree (r := Y.vert 0) (gate_spec Y hz).1 with h | h
    · rcases IsTree.dist_adj_cases Y.hyp.isTree (r := Y.vert 0) (gate_spec Y hz).2.1
        with h2 | h2 <;> omega
    · exact h.symm
  have hd' : Γ.dist (Y.vert 0) (Y.gate hz') + 1 = Γ.dist (Y.vert 0) u.1 := by
    rcases IsTree.dist_adj_cases Y.hyp.isTree (r := Y.vert 0) (gate_spec Y hz').1 with h | h
    · rcases IsTree.dist_adj_cases Y.hyp.isTree (r := Y.vert 0) (gate_spec Y hz').2.1
        with h2 | h2 <;> omega
    · exact h.symm
  have hgw : Y.gate hz = Y.gate hz' :=
    IsTree.eq_of_dist_succ Y.hyp.isTree (gate_spec Y hz).1.symm (gate_spec Y hz').1.symm hd hd'
  have hzu : z.1 ≠ u.1 := fun h => hz.1 (Subtype.ext h.symm)
  have hz'u : z'.1 ≠ u.1 := fun h => hz'.1 (Subtype.ext h.symm)
  have h1 : z.1 = z'.1 :=
    eq_of_kfix_adj_ne Y H u.2.1 u.2.2 (gate_spec Y hz).1 (gate_spec Y hz).2.2
      (gate_spec Y hz).2.1 z.2.2 hzu
      (hgw ▸ (gate_spec Y hz').2.1) z'.2.2 hz'u
  exact Subtype.ext h1

private theorem dt_height_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {v : Y.DtV}
    (hv : Γ.dist (Y.vert 0) v.1 = 1) : v.1 = Y.vert 1 ∨ v.1 = Y.vert (-1) := by
  have hn0 : 2 ≤ Y.n 0 := by rw [H.n_zero]; exact H.two_le
  have hcad : Γ.Adj (Y.vert 0) v.1 := by
    rw [← dist_eq_one_iff_adj]; exact hv
  obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Y.K_ne_bot H)
  have hkK : (k : G) ∈ Y.K := k.2
  have hk1' : (k : G) ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hkKi : (k : G) ∈ Y.Ki 0 := ⟨hkK, Y.K_le_L_zero H hkK⟩
  have hkfix : (k : G) • v.1 = v.1 := v.2.2 k hkK
  have h := (Y.torus_fixed 0 hn0 hkKi hk1' v.1 hcad).mp hkfix
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

private theorem dt_connected (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.dtGraph.Connected := by
  have key : ∀ n : ℕ, ∀ u : Y.DtV, Γ.dist (Y.vert 0) u.1 = n →
      Y.dtGraph.Reachable u Y.dtBase := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro u hu
      have hodd : Odd n := by rw [← hu]; exact u.2.1
      by_cases hu1 : u.1 = Y.vert 1
      · have hbase : u = Y.dtBase := Subtype.ext hu1
        rw [hbase]
      · have hu0 := dtV_ne_vert_zero Y u
        obtain ⟨w, hwu, huww, hwK⟩ := exists_kfix_parent Y hu0 u.2.2
        have hweven : Even (Γ.dist (Y.vert 0) w) := even_dist_of_adj_odd Y u.2.1 hwu
        by_cases hn1 : n = 1
        · have hv : u.1 = Y.vert (-1) := by
            rcases dt_height_one Y H (v := u) (by rw [hu]; exact hn1) with h | h
            · exact absurd h hu1
            · exact h
          have hadj : Y.dtGraph.Adj u Y.dtBase := by
            refine ⟨?_, Y.vert 0, ?_, ?_, fun k hk => Y.K_fix k hk 0⟩
            · exact fun h => hu1 (congrArg Subtype.val h)
            · rw [hv]
              have h := Y.adj (-1)
              rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at h
            · simpa using Y.adj 0
          exact ⟨Walk.cons hadj Walk.nil⟩
        · have hn3 : 3 ≤ n := by
            obtain ⟨m, hm⟩ := hodd
            omega
          have hw0 : w ≠ Y.vert 0 := by
            intro h
            rw [h] at huww
            simp only [SimpleGraph.dist_self] at huww
            omega
          obtain ⟨p, hpw, hpwd, hpK⟩ := exists_kfix_parent Y hw0 hwK
          have hpod : Odd (Γ.dist (Y.vert 0) p) := odd_dist_of_adj_even Y hweven hpw.symm
          let pv : Y.DtV := ⟨p, hpod, hpK⟩
          have hadj : Y.dtGraph.Adj u pv := by
            refine ⟨?_, w, hwu.symm, hpw.symm, hwK⟩
            intro h
            have h2 : Γ.dist (Y.vert 0) p = Γ.dist (Y.vert 0) u.1 := by
              rw [show p = u.1 from (congrArg Subtype.val h).symm]
            omega
          have hpdist : Γ.dist (Y.vert 0) p = n - 2 := by omega
          exact SimpleGraph.Reachable.trans ⟨Walk.cons hadj Walk.nil⟩
            (ih (n - 2) (by omega) pv hpdist)
  haveI : Nonempty Y.DtV := ⟨Y.dtBase⟩
  exact ⟨fun u v => (key _ u rfl).trans (key _ v rfl).symm⟩

private theorem adj_getVert_pred_last (Y : Setup Γ G) {u : Y.DtV} (c : Y.dtGraph.Walk u u)
    (hlen : 0 < c.length) :
    Y.dtGraph.Adj (c.getVert c.length) (c.getVert (c.length - 1)) := by
  have h := c.adj_getVert_succ (i := c.length - 1) (by omega)
  have hu : c.getVert (c.length - 1 + 1) = u := by
    rw [show c.length - 1 + 1 = c.length from by omega]
    exact Walk.getVert_length c
  have hv : c.getVert c.length = u := Walk.getVert_length c
  have e : (c.getVert (c.length - 1 + 1)).1 = (c.getVert c.length).1 := by
    rw [hu, hv]
  obtain ⟨hne, w, h1, h2, h3⟩ := h
  refine ⟨?_, ⟨w, ?_, h1.symm, h3⟩⟩
  · intro hEq
    exact hne (hEq.symm.trans (hv.trans hu.symm))
  · rw [← e]
    exact h2.symm

private theorem adj_getVert_one (Y : Setup Γ G) {u : Y.DtV} (c : Y.dtGraph.Walk u u)
    (hlen : 0 < c.length) :
    Y.dtGraph.Adj (c.getVert c.length) (c.getVert 1) := by
  have h := c.adj_getVert_succ (i := 0) (by omega)
  have h0 : c.getVert 0 = u := Walk.getVert_zero c
  have hv : c.getVert c.length = u := Walk.getVert_length c
  have e : (c.getVert 0).1 = (c.getVert c.length).1 := by
    rw [h0, hv]
  obtain ⟨hne, w, h1, h2, h3⟩ := h
  refine ⟨?_, ⟨w, ?_, h2, h3⟩⟩
  · intro hEq
    exact hne (h0.trans (hv.symm.trans hEq))
  · rw [← e]
    exact h1

private theorem not_isCycle_of_height_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {u : Y.DtV} {c : Y.dtGraph.Walk u u}
    (hall : ∀ k, k ≤ c.length → Γ.dist (Y.vert 0) (c.getVert k).1 = 1) : ¬ c.IsCycle := by
  intro hc
  have hlen : 3 ≤ c.length := hc.three_le_length
  have hmem : ∀ k, k ≤ c.length → (c.getVert k).1 = Y.vert 1 ∨ (c.getVert k).1 = Y.vert (-1) :=
    fun k hk => dt_height_one Y H (hall k hk)
  have hinj := hc.getVert_injOn'
  have h0 : (0:ℕ) ≤ c.length - 1 := by omega
  have h1' : (1:ℕ) ≤ c.length - 1 := by omega
  have h2' : (2:ℕ) ≤ c.length - 1 := by omega
  rcases hmem 0 (by omega) with e0 | e0 <;>
    rcases hmem 1 (by omega) with e1 | e1 <;>
    rcases hmem 2 (by omega) with e2 | e2
  · exact absurd (hinj h0 h1' (Subtype.ext (e0.trans e1.symm))) (by omega)
  · exact absurd (hinj h0 h1' (Subtype.ext (e0.trans e1.symm))) (by omega)
  · exact absurd (hinj h0 h2' (Subtype.ext (e0.trans e2.symm))) (by omega)
  · exact absurd (hinj h1' h2' (Subtype.ext (e1.trans e2.symm))) (by omega)
  · exact absurd (hinj h1' h2' (Subtype.ext (e1.trans e2.symm))) (by omega)
  · exact absurd (hinj h0 h2' (Subtype.ext (e0.trans e2.symm))) (by omega)
  · exact absurd (hinj h0 h1' (Subtype.ext (e0.trans e1.symm))) (by omega)
  · exact absurd (hinj h0 h1' (Subtype.ext (e0.trans e1.symm))) (by omega)

private theorem dist_add_two_of_adj_of_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {p q : Y.DtV} (hpq : Y.dtGraph.Adj p q) (h3 : 3 ≤ Γ.dist (Y.vert 0) p.1)
    (hle : Γ.dist (Y.vert 0) q.1 ≤ Γ.dist (Y.vert 0) p.1) :
    Γ.dist (Y.vert 0) q.1 + 2 = Γ.dist (Y.vert 0) p.1 := by
  rcases dt_adj_height_cases Y H hpq with ⟨h1, -⟩ | h | h <;> omega

private theorem dt_isAcyclic (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.dtGraph.IsAcyclic := by
  intro u c hc
  have hlen : 3 ≤ c.length := hc.three_le_length
  obtain ⟨i, hi_mem, hi_max⟩ := Finset.exists_max_image (Finset.Icc 1 c.length)
    (fun i => Γ.dist (Y.vert 0) (c.getVert i).1) ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi_mem).1
  have hile : i ≤ c.length := (Finset.mem_Icc.mp hi_mem).2
  have hbound : ∀ k, k ≤ c.length →
      Γ.dist (Y.vert 0) (c.getVert k).1 ≤ Γ.dist (Y.vert 0) (c.getVert i).1 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have h := hi_max c.length (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
      rw [Walk.getVert_length] at h
      simpa using h
    · exact hi_max k (Finset.mem_Icc.mpr ⟨hkpos, hk⟩)
  by_cases hA : Γ.dist (Y.vert 0) (c.getVert i).1 = 1
  ·
    refine absurd hc (not_isCycle_of_height_one Y H fun k hk => ?_)
    have h1 := hbound k hk
    obtain ⟨m, hm⟩ := (c.getVert k).2.1
    omega
  ·
    have hA3 : 3 ≤ Γ.dist (Y.vert 0) (c.getVert i).1 := by
      obtain ⟨m, hm⟩ := (c.getVert i).2.1
      omega
    by_cases hi1' : i = 1
    ·
      subst hi1'
      have hprev : Y.dtGraph.Adj (c.getVert 1) (c.getVert 0) := by
        have h := c.adj_getVert_succ (i := 0) (by omega)
        exact h.symm
      have hnext : Y.dtGraph.Adj (c.getVert 1) (c.getVert 2) :=
        c.adj_getVert_succ (i := 1) (by omega)
      have h1 := dist_add_two_of_adj_of_le Y H hprev hA3 (hbound _ (by omega))
      have h2 := dist_add_two_of_adj_of_le Y H hnext hA3 (hbound _ (by omega))
      have heq2 : c.getVert 0 = c.getVert 2 := dt_unique_height Y H hprev hnext h1 h2
      have hinj := hc.getVert_injOn'
        (show 0 ≤ c.length - 1 from by omega)
        (show 2 ≤ c.length - 1 from by omega) heq2
      omega
    · rcases lt_or_eq_of_le hile with hlt | heq
      ·
        have hprev : Y.dtGraph.Adj (c.getVert i) (c.getVert (i - 1)) := by
          have h := c.adj_getVert_succ (i := i - 1) (by omega)
          rw [show i - 1 + 1 = i from by omega] at h
          exact h.symm
        have hnext : Y.dtGraph.Adj (c.getVert i) (c.getVert (i + 1)) :=
          c.adj_getVert_succ (by omega)
        have h1 := dist_add_two_of_adj_of_le Y H hprev hA3 (hbound _ (by omega))
        have h2 := dist_add_two_of_adj_of_le Y H hnext hA3 (hbound _ (by omega))
        have heq2 : c.getVert (i - 1) = c.getVert (i + 1) :=
          dt_unique_height Y H hprev hnext h1 h2
        have hinj := hc.getVert_injOn
          (show i - 1 ∈ {k | 1 ≤ k ∧ k ≤ c.length} from by
            simp only [Set.mem_ofPred_eq]; omega)
          (show i + 1 ∈ {k | 1 ≤ k ∧ k ≤ c.length} from by
            simp only [Set.mem_ofPred_eq]; omega) heq2
        omega
      ·
        subst heq
        have hprev : Y.dtGraph.Adj (c.getVert c.length) (c.getVert (c.length - 1)) :=
          adj_getVert_pred_last Y c (by omega)
        have hnext : Y.dtGraph.Adj (c.getVert c.length) (c.getVert 1) :=
          adj_getVert_one Y c (by omega)
        have h1 := dist_add_two_of_adj_of_le Y H hprev hA3 (hbound _ (by omega))
        have h2 := dist_add_two_of_adj_of_le Y H hnext hA3 (hbound _ (by omega))
        have heq2 : c.getVert (c.length - 1) = c.getVert 1 :=
          dt_unique_height Y H hprev hnext h1 h2
        have hinj := hc.getVert_injOn
          (show c.length - 1 ∈ {k | 1 ≤ k ∧ k ≤ c.length} from by
            simp only [Set.mem_ofPred_eq]; omega)
          (show 1 ∈ {k | 1 ≤ k ∧ k ≤ c.length} from by
            simp only [Set.mem_ofPred_eq]; omega) heq2
        omega

theorem dt_isTree (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) : Y.dtGraph.IsTree :=
  ⟨dt_connected Y H, dt_isAcyclic Y H⟩

theorem dt_kernel (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {g : G}
    (hfix : ∀ u : Y.DtV, g • u.1 = u.1) : g ∈ Y.K := by
  have hGT : g ∈ Y.GT := by
    rw [Setup.GT, Fan86.mem_fixSet]
    rintro v ⟨i, rfl⟩
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' i
    ·
      have hodd1 : Odd (i - 1) := ⟨m - 1, by omega⟩
      have hodd2 : Odd (i + 1) := ⟨m, by omega⟩
      have hfix1 : g • Y.vert (i - 1) = Y.vert (i - 1) :=
        hfix ⟨Y.vert (i - 1), (odd_dist_vert_iff Y _).mpr hodd1,
          fun k hk => Y.K_fix k hk (i - 1)⟩
      have hfix2 : g • Y.vert (i + 1) = Y.vert (i + 1) :=
        hfix ⟨Y.vert (i + 1), (odd_dist_vert_iff Y _).mpr hodd2,
          fun k hk => Y.K_fix k hk (i + 1)⟩
      have hadj1 : Γ.Adj (Y.vert (i - 1)) (Y.vert i) := by
        have h := Y.adj (i - 1)
        rwa [show i - 1 + 1 = i by omega] at h
      have hadj2 : Γ.Adj (Y.vert (i + 1)) (Y.vert i) := (Y.adj i).symm
      have h1 : Γ.Adj (Y.vert (i - 1)) (g • Y.vert i) := by
        rw [← hfix1]
        exact (Y.hyp.adj_smul g (Y.vert (i - 1)) (Y.vert i)).mpr hadj1
      have h2 : Γ.Adj (Y.vert (i + 1)) (g • Y.vert i) := by
        rw [← hfix2]
        exact (Y.hyp.adj_smul g (Y.vert (i + 1)) (Y.vert i)).mpr hadj2
      have hne : Y.vert (i - 1) ≠ Y.vert (i + 1) := by
        intro h
        have := Y.vert_injective h
        omega
      exact common_nbr_unique Y.hyp.isTree hne h1 h2 hadj1 hadj2
    ·
      exact hfix ⟨Y.vert i, (odd_dist_vert_iff Y i).mpr ⟨m, by omega⟩,
        fun k hk => Y.K_fix k hk i⟩
  rwa [Y.GT_eq_K_of_sec5Hyp H] at hGT

theorem exists_tutte_arc_le_K (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 5 ∧
      ∀ (P : Arc Y.dtGraph k) (g : G), g ∈ Y.N →
        (∀ i, i ≤ k → g • (P.vert i).1 = (P.vert i).1) → g ∈ Y.K := by
  obtain ⟨k, h1, h2, h3⟩ :=
    CFSG.Quasithin.Fan86.Tutte.tutteTree (Y.DtV) Y.dtGraph (dt_isTree Y H) (dt_card_nbr Y H)
      ↥Y.N (fun n u v => Y.dt_adj_smul n u v) (dt_vertex_trans Y H) (dt_finite_stab Y)
      (dt_loc_trans Y H)
  refine ⟨k, h1, h2, ?_⟩
  intro P g hgN hfix
  have hfix' : ∀ i, i ≤ k → (⟨g, hgN⟩ : ↥Y.N) • P.vert i = P.vert i :=
    fun i hi => Subtype.ext (hfix i hi)
  have hall := h3 P ⟨g, hgN⟩ hfix'
  exact dt_kernel Y H (fun u => congrArg Subtype.val (hall u))

def dtArc (Y : Setup Γ G) (a : ℤ) (ha : Odd a) (k : ℕ) : Arc Y.dtGraph k where
  vert i :=
    ⟨Y.vert (a + 2 * (i : ℤ)),
      ((Y.odd_dist_vert_iff (a + 2 * (i : ℤ))).mpr (by
        obtain ⟨m, hm⟩ := ha
        exact ⟨m + (i : ℤ), by push_cast [hm]; ring⟩)),
      fun k hk => Y.K_fix k hk _⟩
  adj i _ := by
    refine ⟨?_, Y.vert (a + 2 * (i : ℤ) + 1), ?_, ?_, fun k hk => Y.K_fix k hk _⟩
    · intro h
      have := Y.vert_injective (congrArg Subtype.val h)
      push_cast at this
      omega
    · have h := Y.adj (a + 2 * (i : ℤ))
      convert h using 2 <;> push_cast <;> ring
    · have h := Y.adj (a + 2 * (i : ℤ) + 1)
      convert h using 2 <;> push_cast <;> ring
  nb i _ := by
    intro h
    have := Y.vert_injective (congrArg Subtype.val h)
    push_cast at this
    omega

theorem mem_K_of_fixes_odd_vert (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {g : G} (hg : g ∈ Y.N)
    {a : ℤ} (ha : Odd a)
    (hfix : ∀ j : ℕ, j ≤ 5 → g • Y.vert (a + 2 * j) = Y.vert (a + 2 * j)) : g ∈ Y.K := by
  obtain ⟨k, hk1, hk5, hK⟩ := exists_tutte_arc_le_K Y H
  refine hK (dtArc Y a ha k) g hg fun i hi => ?_
  exact hfix i (le_trans hi hk5)

private theorem arcStab_eq_K_sup_pCore (Y : Setup Γ G) {m r : ℤ} (hmr : m < r) :
    Y.arcStab m r = Y.K ⊔ pCoreOf 2 (Y.arcStab m r) := by
  have hK : Y.K ≤ Y.arcStab m r := Y.K_le_GT.trans (Y.GT_le_arcStab m r)
  have hA : Y.arcStab m r ≤ Y.Gi (r - 1) ⊓ Y.Gi ((r - 1) + 1) := by
    rw [show r - 1 + 1 = r by ring]
    exact le_inf (Y.arcStab_le_Gi_right_pred hmr) (Y.arcStab_le_Gi_right hmr)
  exact ((Y.pCoreOf_eq_inf_edgeSylow (r - 1) hK hA).2).symm


private theorem card_nbr_diff (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (u v : Y.DtV)
    (hv : Y.dtGraph.Adj u v) : Nat.card {a : Y.DtV // Y.dtGraph.Adj u a ∧ a ≠ v} = 2 := by
  have h := Set.ncard_sdiff_singleton_of_mem (s := Y.dtGraph.neighborSet u) hv
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, dt_card_nbr Y H u] at h
  exact h

private theorem Qs_one_fixes_kfix_nbr (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {q : G}
    (hq : q ∈ Y.Qs 1) {w y : V} (h1w : Γ.Adj (Y.vert 1) w) (hwK : ∀ k ∈ Y.K, k • w = w)
    (hwy : Γ.Adj w y) (hyK : ∀ k ∈ Y.K, k • y = y) (hyu : y ≠ Y.vert 1) : q • y = y := by
  have hqN : q ∈ Y.N := Subgroup.centralizer_le_normalizer (Y.K : Set G) hq.2
  have hqu : q • Y.vert 1 = Y.vert 1 := MulAction.mem_stabilizer_iff.mp (Y.Q_le_Gi 1 hq.1)
  have hqw : q • w = w := Y.Q_fixes_neighbors_vert 1 w h1w q hq.1
  have hadj : Γ.Adj w (q • y) := by
    have h := (Y.hyp.adj_smul q w y).mpr hwy
    rwa [hqw] at h
  have hK : ∀ k ∈ Y.K, k • (q • y) = q • y := (kfix_smul_iff Y hqN y).mpr hyK
  have hne : q • y ≠ Y.vert 1 := by
    intro h
    have h2 : q • y = q • Y.vert 1 := by rw [h, hqu]
    exact hyu (MulAction.injective q h2)
  exact eq_of_kfix_adj_ne Y H Y.dtBase.2.1 Y.dtBase.2.2 h1w hwK hadj hK hne hwy hyK hyu

private theorem Qs_one_fixes_vert (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {q : G}
    (hq : q ∈ Y.Qs 1) : q • Y.vert (-1) = Y.vert (-1) ∧ q • Y.vert 3 = Y.vert 3 := by
  constructor
  · refine Qs_one_fixes_kfix_nbr Y H hq (w := Y.vert 0) (y := Y.vert (-1)) (Y.adj 0).symm
      (fun k hk => Y.K_fix k hk 0) ?_ (fun k hk => Y.K_fix k hk (-1)) ?_
    · have h := Y.adj (-1)
      rw [show (-1 : ℤ) + 1 = 0 by norm_num] at h
      exact h.symm
    · intro h
      have := Y.vert_injective h
      norm_num at this
  · refine Qs_one_fixes_kfix_nbr Y H hq (w := Y.vert 2) (y := Y.vert 3) (Y.adj 1)
      (fun k hk => Y.K_fix k hk 2) ?_ (fun k hk => Y.K_fix k hk 3) ?_
    · exact Y.adj 2
    · intro h
      have := Y.vert_injective h
      norm_num at this

private theorem card_two_arcs_avoiding (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {x v : Y.DtV} (hxv : Y.dtGraph.Adj x v) :
    Nat.card (Σ b : {b : Y.DtV // Y.dtGraph.Adj x b ∧ b ≠ v},
      {c : Y.DtV // Y.dtGraph.Adj b.1 c ∧ c ≠ x}) = 4 := by
  have hcardB : Nat.card {b : Y.DtV // Y.dtGraph.Adj x b ∧ b ≠ v} = 2 :=
    card_nbr_diff Y H x v hxv
  have hcardC : ∀ b : {b : Y.DtV // Y.dtGraph.Adj x b ∧ b ≠ v},
      Nat.card {c : Y.DtV // Y.dtGraph.Adj b.1 c ∧ c ≠ x} = 2 :=
    fun b => card_nbr_diff Y H b.1 x b.2.1.symm
  haveI : Finite {b : Y.DtV // Y.dtGraph.Adj x b ∧ b ≠ v} :=
    Nat.finite_of_card_ne_zero (by rw [hcardB]; norm_num)
  haveI : ∀ b : {b : Y.DtV // Y.dtGraph.Adj x b ∧ b ≠ v},
      Finite {c : Y.DtV // Y.dtGraph.Adj b.1 c ∧ c ≠ x} :=
    fun b => Nat.finite_of_card_ne_zero (by rw [hcardC b]; norm_num)
  haveI : Fintype {b : Y.DtV // Y.dtGraph.Adj x b ∧ b ≠ v} := Fintype.ofFinite _
  rw [Nat.card_sigma]
  simp only [hcardC]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcardB]
  norm_num

private theorem eq_one_of_Qs_one_fixes (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {g : G}
    (hg : g ∈ Y.Qs 1) (h0 : g • Y.vert (-3) = Y.vert (-3)) (h5 : g • Y.vert 5 = Y.vert 5)
    (h7 : g • Y.vert 7 = Y.vert 7) : g = 1 := by
  have hgN : g ∈ Y.N := Subgroup.centralizer_le_normalizer (Y.K : Set G) hg.2
  have h1 := (Qs_one_fixes_vert Y H hg).1
  have h3 := (Qs_one_fixes_vert Y H hg).2
  have hb : g • Y.vert 1 = Y.vert 1 := MulAction.mem_stabilizer_iff.mp (Y.Q_le_Gi 1 hg.1)
  have hall : ∀ i : ℕ, i ≤ 5 →
      g • Y.vert (-3 + 2 * (i : ℤ)) = Y.vert (-3 + 2 * (i : ℤ)) := by
    intro i hi
    interval_cases i
    · simpa using h0
    · simpa using h1
    · simpa using hb
    · simpa using h3
    · simpa using h5
    · simpa using h7
  have hK : g ∈ Y.K :=
    Y.mem_K_of_fixes_odd_vert H hgN (a := -3) ⟨-2, by norm_num⟩ hall
  have hKQs : Y.K ⊓ Y.Qs 1 = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_inf] at hz
    have h2 : z ∈ Y.edgeSylow 0 := Y.Q_le_edgeSylow 0 hz.2.1
    have hz' : z ∈ Y.K ⊓ Y.edgeSylow 0 := ⟨hz.1, h2⟩
    rwa [Y.K_inf_edgeSylow 0] at hz'
  have hbot : g ∈ Y.K ⊓ Y.Qs 1 := ⟨hK, hg⟩
  rw [hKQs] at hbot
  exact Subgroup.mem_bot.mp hbot

private theorem smul_mem_nbr_ne (Y : Setup Γ G) (n : ↥Y.N) {u a v : Y.DtV}
    (hua : Y.dtGraph.Adj u a) (hav : a ≠ v) (hu : n • u = u) (hv : n • v = v) :
    Y.dtGraph.Adj u (n • a) ∧ n • a ≠ v := by
  constructor
  · have h := (Y.dt_adj_smul n u a).mpr hua
    rwa [hu] at h
  · intro h
    apply hav
    have hiv : n⁻¹ • v = v := by
      have h1 := congrArg (fun z : Y.DtV => n⁻¹ • z) hv
      simpa using h1.symm
    calc a = n⁻¹ • (n • a) := (inv_smul_smul n a).symm
      _ = n⁻¹ • v := by rw [h]
      _ = v := hiv

theorem card_Qs_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) : Nat.card (Y.Qs 1) ≤ 8 := by
  classical
  let P5 := dtArc Y (-3) ⟨-2, by norm_num⟩ 5
  let x' : Y.DtV := P5.vert 1
  let x : Y.DtV := P5.vert 3
  let a₀ : Y.DtV := P5.vert 0
  let b₀ : Y.DtV := P5.vert 4
  let c₀ : Y.DtV := P5.vert 5
  have hP5adj : ∀ i : ℕ, i < 5 → Y.dtGraph.Adj (P5.vert i) (P5.vert (i + 1)) :=
    fun i hi => P5.adj i hi
  have hP5nb : ∀ i : ℕ, i + 2 ≤ 5 → P5.vert i ≠ P5.vert (i + 2) :=
    fun i hi => P5.nb i hi
  have hbase2 : Y.dtBase = P5.vert 2 := Subtype.ext rfl
  have hdt_x' : Y.dtGraph.Adj Y.dtBase x' := by
    rw [hbase2]
    exact (hP5adj 1 (by norm_num)).symm
  have hdt_x : Y.dtGraph.Adj Y.dtBase x := by
    rw [hbase2]
    exact hP5adj 2 (by norm_num)
  have ha₀x' : Y.dtGraph.Adj x' a₀ := (hP5adj 0 (by norm_num)).symm
  have hxb₀ : Y.dtGraph.Adj x b₀ := hP5adj 3 (by norm_num)
  have hb₀c₀ : Y.dtGraph.Adj b₀ c₀ := hP5adj 4 (by norm_num)
  have ha₀ : a₀ ≠ Y.dtBase := by
    rw [hbase2]
    exact hP5nb 0 (by norm_num)
  have hb₀ : b₀ ≠ Y.dtBase := by
    rw [hbase2]
    exact (hP5nb 2 (by norm_num)).symm
  have hc₀ : c₀ ≠ x := (hP5nb 3 (by norm_num)).symm
  have hQsN : ∀ q ∈ Y.Qs 1, q ∈ Y.N := fun q hq =>
    Subgroup.centralizer_le_normalizer (Y.K : Set G) hq.2
  have hQs_dtBase : ∀ q ∈ Y.Qs 1, q • Y.dtBase.1 = Y.dtBase.1 := fun q hq =>
    MulAction.mem_stabilizer_iff.mp (Y.Q_le_Gi 1 hq.1)
  have hQs_x'_v : ∀ q ∈ Y.Qs 1, q • x'.1 = x'.1 := fun q hq =>
    (Qs_one_fixes_vert Y H hq).1
  have hQs_x_v : ∀ q ∈ Y.Qs 1, q • x.1 = x.1 := fun q hq =>
    (Qs_one_fixes_vert Y H hq).2
  let A₀ := {a : Y.DtV // Y.dtGraph.Adj x' a ∧ a ≠ Y.dtBase}
  let B := {b : Y.DtV // Y.dtGraph.Adj x b ∧ b ≠ Y.dtBase}
  let Cb : B → Type := fun b => {c : Y.DtV // Y.dtGraph.Adj b.1 c ∧ c ≠ x}
  let D := Sigma Cb
  have hcardA₀ : Nat.card A₀ = 2 := card_nbr_diff Y H x' Y.dtBase hdt_x'.symm
  have hcardD : Nat.card D = 4 := card_two_arcs_avoiding Y H hdt_x.symm
  haveI : Finite A₀ := Nat.finite_of_card_ne_zero (by rw [hcardA₀]; norm_num)
  haveI : Finite D := Nat.finite_of_card_ne_zero (by rw [hcardD]; norm_num)
  let toN : Y.Qs 1 → ↥Y.N := fun q => ⟨q.1, hQsN q.1 q.2⟩
  have hinj : Function.Injective (fun q : Y.Qs 1 =>
      ((⟨toN q • a₀, smul_mem_nbr_ne Y (toN q) ha₀x' ha₀
          (show toN q • x' = x' from Subtype.ext (hQs_x'_v q.1 q.2))
          (show toN q • Y.dtBase = Y.dtBase from Subtype.ext (hQs_dtBase q.1 q.2))⟩ : A₀),
       (⟨⟨toN q • b₀, smul_mem_nbr_ne Y (toN q) hxb₀ hb₀
          (show toN q • x = x from Subtype.ext (hQs_x_v q.1 q.2))
          (show toN q • Y.dtBase = Y.dtBase from Subtype.ext (hQs_dtBase q.1 q.2))⟩,
        ⟨toN q • c₀, (Y.dt_adj_smul (toN q) b₀ c₀).mpr hb₀c₀,
        by
          intro h
          have h' : (toN q • c₀).1 = (toN q • x).1 := by
            rw [h, show toN q • x = x from Subtype.ext (hQs_x_v q.1 q.2)]
          exact hc₀ (Subtype.ext (MulAction.injective (toN q) h'))⟩⟩ : D))) := by
    intro q q' hq
    have h1 : q.1 • a₀.1 = q'.1 • a₀.1 :=
      congrArg (fun z => (((z.1 : A₀) : Y.DtV)).1) hq
    have h2 : q.1 • b₀.1 = q'.1 • b₀.1 :=
      congrArg (fun z => (((z.2 : D).1.1 : Y.DtV)).1) hq
    have h3 : q.1 • c₀.1 = q'.1 • c₀.1 :=
      congrArg (fun z => (((z.2 : D).2.1 : Y.DtV)).1) hq
    have hmemQ : q'.1⁻¹ * q.1 ∈ Y.Qs 1 := (Y.Qs 1).mul_mem ((Y.Qs 1).inv_mem q'.2) q.2
    have h0' : (q'.1⁻¹ * q.1) • a₀.1 = a₀.1 := by rw [mul_smul, h1, inv_smul_smul]
    have h5' : (q'.1⁻¹ * q.1) • b₀.1 = b₀.1 := by rw [mul_smul, h2, inv_smul_smul]
    have h7' : (q'.1⁻¹ * q.1) • c₀.1 = c₀.1 := by rw [mul_smul, h3, inv_smul_smul]
    exact Subtype.ext (inv_mul_eq_one.mp (eq_one_of_Qs_one_fixes Y H hmemQ h0' h5' h7')).symm
  have h8 : Nat.card (Y.Qs 1) ≤ Nat.card (A₀ × D) :=
    Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, hcardA₀, hcardD] at h8
  omega

private theorem exists_mem_pCoreOf_smul_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {a r : ℤ} (hr : Odd r) (har : a < r) (hreg : Y.RightTransAt a r) {z : V}
    (hz : Γ.Adj (Y.vert r) z) (hz1 : z ≠ Y.vert (r - 1)) :
    ∃ g ∈ pCoreOf 2 (Y.arcStab a r), g • z = Y.vert (r + 1) := by
  have hne : Y.vert (r + 1) ≠ Y.vert (r - 1) := by
    intro h
    have := Y.vert_injective h
    omega
  have hadj1 : Γ.Adj (Y.vert r) (Y.vert (r + 1)) := Y.adj r
  obtain ⟨g, hgA, hg⟩ := hreg z (Y.vert (r + 1)) hz hz1 hadj1 hne
  set R : Subgroup G := pCoreOf 2 (Y.arcStab a r) with hR
  have hArec : Y.K ⊔ R = Y.arcStab a r := by
    rw [hR]
    exact (Y.arcStab_eq_K_sup_pCore har).symm
  have hKnormR : Y.K ≤ Subgroup.normalizer (R : Set G) :=
    (le_sup_left.trans (le_of_eq hArec)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.arcStab a r))
  have hcoe : (↑(Y.K ⊔ R) : Set G) = (Y.K : Set G) * (R : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Y.K R hKnormR
  have hxmul : g ∈ (Y.K : Set G) * (R : Set G) := by
    rw [← hcoe]
    exact hArec.symm ▸ hgA
  obtain ⟨k, hk, s, hs, hks⟩ := hxmul
  refine ⟨s, hs, ?_⟩
  rw [← hks, mul_smul] at hg
  have hky : k • Y.vert (r + 1) = Y.vert (r + 1) := Y.K_fixes_nbr_odd H hr hadj1 k hk
  have h1 : k • (s • z) = k • Y.vert (r + 1) := by rw [hg, hky]
  exact MulAction.injective k h1

private theorem pCoreOf_arcStab_fixes_vert (Y : Setup Γ G) {a r : ℤ} {g : G}
    (hg : g ∈ pCoreOf 2 (Y.arcStab a r)) {i : ℕ} (hi : a + 2 * (i : ℤ) ≤ r) :
    g • Y.vert (a + 2 * (i : ℤ)) = Y.vert (a + 2 * (i : ℤ)) := by
  refine Fan86.mem_fixSet.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hg) _
    (Set.mem_image_of_mem _ ?_)
  exact Set.mem_Icc.mpr ⟨by omega, hi⟩

theorem le_eight_of_regular (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {a : ℤ} (ha : Odd a) {m : ℕ}
    (hreg : Y.RightTransAt a (a + (2 * m : ℕ)))
    (hc : pCoreOf 2 (Y.arcStab a (a + (2 * m : ℕ))) ≤
      Subgroup.centralizer (Y.K : Set G)) :
    m ≤ 4 := by
  by_contra hm
  push Not at hm
  have hra : a < a + (2 * m : ℕ) := by
    have h2 : (0:ℤ) < (2 * m : ℕ) := by
      have : 0 < 2 * m := by omega
      exact_mod_cast this
    omega
  set r : ℤ := a + (2 * m : ℕ) with hr
  have hr_odd : Odd r := by
    obtain ⟨k, hk⟩ := ha
    exact ⟨k + (m : ℤ), by rw [hr]; push_cast [hk]; ring⟩
  set A : Subgroup G := Y.arcStab a r with hA
  set R : Subgroup G := pCoreOf 2 A with hR
  have hRN : R ≤ Y.N :=
    hc.trans (Subgroup.centralizer_le_normalizer (Y.K : Set G))
  obtain ⟨z, hz, hzx, hz1⟩ := exists_adj_ne_ne (a := Y.vert (r + 1)) (b := Y.vert (r - 1))
    (Y.hyp.three_le_card (Y.vert r))
  obtain ⟨s, hsR, hs⟩ := exists_mem_pCoreOf_smul_eq Y H hr_odd hra hreg hz hz1
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hsR' : s ∈ R := hsR
    rw [hbot] at hsR'
    have h1 : s = 1 := Subgroup.mem_bot.mp hsR'
    rw [h1] at hs
    simp only [one_smul] at hs
    exact hzx hs
  have harcFix : ∀ g ∈ R, ∀ i : ℕ, i ≤ 5 →
      g • (Y.vert (a + 2 * (i : ℤ))) = Y.vert (a + 2 * (i : ℤ)) :=
    fun g hg i hi => pCoreOf_arcStab_fixes_vert Y hg (by rw [hr]; push_cast; omega)
  have hRK : R ≤ Y.K :=
    fun g hg => Y.mem_K_of_fixes_odd_vert H (hRN hg) ha (harcFix g hg)
  have hRbot : R = ⊥ := by
    have h := inf_eq_bot_of_odd_of_isPGroup Y.odd_card_K (pCoreOf_isPGroup' A)
    rw [inf_comm, inf_eq_left.mpr hRK] at h
    exact h
  exact hRne hRbot

end Setup

end CFSG.Quasithin.St84

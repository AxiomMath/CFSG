module

public import CFSG.RankThree.GF2n.Tim81.Sec5.I6Planes
public import CFSG.RankThree.GF2n.Tim81.Sec5.Stmts

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open scoped MatrixGroups commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {M V : Subgroup G}

private theorem fSet.V_le {A : Subgroup G} (hA : A ∈ fSet M V) : V ≤ A := by
  obtain ⟨-, -, U, -, x, -, rfl⟩ := hA
  exact le_sup_left

private theorem fSet.le_Pc {A : Subgroup G} (hA : A ∈ fSet M V) : A ≤ Pc M V := hA.1

private theorem fSet.card {A : Subgroup G} (hA : A ∈ fSet M V) :
    Nat.card A = Nat.card V ^ 2 := hA.2.1

private theorem Sec45Shape.not_mem_centralizer_of_not_mem_kOf {H : Subgroup G} {h₀ : G}
    (h : RootHyp M V) (hS : Sec45Shape M V H h₀) {y x : G} (hy : y ∈ H) (hyV : conjSubgroup y V ≠ V)
    (hx : x ∈ Pc M V) (hxK : x ∉ kOf V H) :
    x ∉ Subgroup.centralizer (conjSubgroup y V : Set G) := by
  intro hxC
  have hc3 := hS.sup_commutator_eq h hy hyV hx hxK
  have hbot : ⁅conjSubgroup y V, Subgroup.zpowers x⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.zpowers_le.mpr hxC)
  have hVeq : V = Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G) := by
    rw [← hc3.1, hbot, sup_bot_eq]
  have hq : Nat.card V ^ 2 = Nat.card V := by
    calc Nat.card V ^ 2
        = Nat.card ↥(Tim79a.xOf V H ⊓ Subgroup.centralizer ({x} : Set G)) :=
          (hS.xOf_inf_centralizer_le_and_card h hx hxK).2.symm
      _ = Nat.card V := by rw [← hVeq]
  have h4 := h.four_le_card
  nlinarith [Nat.card_pos (α := ↥V)]

private theorem fSet.exists_plane (hS : Sec5Hyp M V) {A : Subgroup G} (hA : A ∈ fSet M V) :
    ∃ g x : G, conjSubgroup g V ∈ sigmaSet M V ∧ x ∈ Pc M V ∧
      x ∉ kOf V (hOf M V g) ∧
      A = Tim79a.xOf V (hOf M V g) ⊓ Subgroup.centralizer ({x} : Set G) ∧
      A = V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x⁆ := by
  obtain ⟨-, hcard, U, hU, x, hxP, hAeq⟩ := hA
  obtain ⟨g, rfl, hH⟩ := hU
  have h := hS.toRootHyp
  have hSg := hS.shape ⟨g, rfl, hH⟩
  obtain ⟨y, hyH, -, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hSg.Pc_le hSg.hH
  have hUy : conjSubgroup y V ∈ sigmaSet M V := by
    rw [← hVy]
    exact ⟨g, rfl, hH⟩
  have hyV : conjSubgroup y V ≠ V := ne_of_mem_sigmaSet h hUy
  have hxK : x ∉ kOf V (hOf M V g) := by
    intro hxK
    have hcent : x ∈ Subgroup.centralizer (conjSubgroup y V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hxK).2 u
        (conjSubgroup_le_xOf_of_mem (V := V) (H := hOf M V g) hyH hu)
    have hbot : ⁅conjSubgroup g V, Subgroup.zpowers x⁆ = ⊥ := by
      rw [hVy, Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.zpowers_le.mpr hcent)
    have hAeqV : A = V := by rw [hAeq, hbot, sup_bot_eq]
    have hq : Nat.card V ^ 2 = Nat.card V := by rw [← hcard, hAeqV]
    have h4 := h.four_le_card
    have hq1 : Nat.card V = 1 := by nlinarith [Nat.card_pos (α := ↥V)]
    omega
  have hAplane : A = Tim79a.xOf V (hOf M V g) ⊓ Subgroup.centralizer ({x} : Set G) := by
    rw [hAeq, hVy]
    exact (hSg.sup_commutator_eq h hyH hyV hxP hxK).1
  exact ⟨g, x, ⟨g, rfl, hH⟩, hxP, hxK, hAplane, hAeq⟩

private theorem fSet.isMulCommutative (hS : Sec5Hyp M V) {A : Subgroup G}
    (hA : A ∈ fSet M V) : IsMulCommutative A := by
  obtain ⟨g, x, hUg, -, -, hAplane, -⟩ := fSet.exists_plane hS hA
  have h := hS.toRootHyp
  have hSg := hS.shape hUg
  have hW := hSg.isElemAbelian h
  have hAW : A ≤ Tim79a.xOf V (hOf M V g) := by
    rw [hAplane]
    exact inf_le_left
  refine isMulCommutative_subgroup_iff.mpr ?_
  intro a ha b hb
  exact (isMulCommutative_subgroup_iff.mp hW.1) a (hAW ha) b (hAW hb)

theorem Sec5Hyp.stmt51b (hS : Sec5Hyp M V) :
    ∀ A ∈ fSet M V, ∀ x ∈ A, x ∉ V →
      Pc M V ⊓ Subgroup.centralizer ({x} : Set G) = Pc M V ⊓ Subgroup.centralizer (A : Set G) := by
  intro A hA x hxA hxV
  obtain ⟨g, x₀, hUg, hx0P, hx0K, hAplane, -⟩ := fSet.exists_plane hS hA
  have h := hS.toRootHyp
  have hSg := hS.shape hUg
  have hxPlane : x ∈ Tim79a.xOf V (hOf M V g) ⊓ Subgroup.centralizer ({x₀} : Set G) := by
    rw [← hAplane]
    exact hxA
  have hd1 := hSg.Pc_inf_centralizer_eq_of_mem h hx0P hx0K hxPlane hxV
  rw [hd1, ← hAplane]

theorem Sec5Hyp.stmt51d (hS : Sec5Hyp M V) : Sec5.Stmt51d M V := by
  intro A hA
  obtain ⟨g, x₀, hUg, hx0P, hx0K, hAplane, -⟩ := fSet.exists_plane hS hA
  have h := hS.toRootHyp
  have hSg := hS.shape hUg
  have hd2 := hSg.card_Pc_inf_centralizer_plane h hx0P hx0K
  rw [← hAplane] at hd2
  exact hd2

theorem Sec5Hyp.conj_mem_fSet (hS : Sec5Hyp M V) {m : G} (hm : m ∈ M) {A : Subgroup G}
    (hA : A ∈ fSet M V) : conjSubgroup m A ∈ fSet M V := by
  obtain ⟨hAP, hcard, U, hU, x, hxP, hAeq⟩ := hA
  have h := hS.toRootHyp
  have hVm : conjSubgroup m V = V :=
    conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer hm)
  have hPm : conjSubgroup m (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer_Pc hm)
  let x' : G := m * x * m⁻¹
  have hx'P : x' ∈ Pc M V := by
    rw [← hPm]
    exact Subgroup.mem_map.mpr ⟨x, hxP, rfl⟩
  refine ⟨?_, ?_, conjSubgroup m U, hS.conj_mem_sigmaSet hm hU, x', hx'P, ?_⟩
  · calc conjSubgroup m A ≤ conjSubgroup m (Pc M V) := Subgroup.map_mono hAP
      _ = Pc M V := hPm
  · rw [card_conjSubgroup, hcard]
  · rw [hAeq, conjSubgroup_sup_eq_sup, hVm]
    congr 1
    change (⁅U, Subgroup.zpowers x⁆).map (MulAut.conj m).toMonoidHom =
      ⁅conjSubgroup m U, Subgroup.zpowers x'⁆
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
    rfl

theorem Sec5Hyp.stmt51a (hS : Sec5Hyp M V) : Sec5.Stmt51a M V := by
  intro U hU x hxP hxC
  obtain ⟨g, rfl, hH⟩ := hU
  have h := hS.toRootHyp
  have hSg := hS.shape ⟨g, rfl, hH⟩
  obtain ⟨y, hyH, -, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hSg.Pc_le hSg.hH
  have hUy : conjSubgroup y V ∈ sigmaSet M V := by
    rw [← hVy]
    exact ⟨g, rfl, hH⟩
  have hyV : conjSubgroup y V ≠ V := ne_of_mem_sigmaSet h hUy
  have hxK : x ∉ kOf V (hOf M V g) := by
    intro hxK
    apply hxC
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hUW : conjSubgroup g V ≤ Tim79a.xOf V (hOf M V g) := by
      rw [hVy]
      exact conjSubgroup_le_xOf_of_mem hyH
    exact Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hxK).2 u (hUW hu)
  have hc3 := hSg.sup_commutator_eq h hyH hyV hxP hxK
  have hEq : V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x⁆ =
      Tim79a.xOf V (hOf M V g) ⊓ Subgroup.centralizer ({x} : Set G) := by
    rw [hVy]
    exact hc3.1
  have hcard : Nat.card ↥(V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x⁆) = Nat.card V ^ 2 := by
    rw [hEq]
    exact (hSg.xOf_inf_centralizer_le_and_card h hxP hxK).2
  have hle : V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x⁆ ≤ Pc M V := by
    rw [hEq]
    exact (hSg.xOf_inf_centralizer_le_and_card h hxP hxK).1
  exact ⟨hle, hcard, conjSubgroup g V, ⟨g, rfl, hH⟩, x, hxP, rfl⟩

theorem RootHyp.sigmaSet_nonempty (h : RootHyp M V) {H : Subgroup G}
    (hH : IsHMember M V H) (hVH : V ≤ inSubgroup (pCore 2) H) :
    (sigmaSet M V).Nonempty := by
  have hPH : Pc M V ≤ H := hH.2.1
  obtain ⟨g, hgH, hgM⟩ := Set.not_subset.mp hH.2.2
  have hL : ¬ hOf M V g ≤ M := by
    intro hLM
    have hPgM : conjSubgroup g (Pc M V) ≤ M := le_sup_right.trans hLM
    have hPgH : conjSubgroup g (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hPH hgH
    have hnorm : imgK V H (conjSubgroup g (Pc M V)) ≤
        Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := (mem_imgK_iff).mp hz
      have hyM : (y : G) ∈ M := hPgM hy
      have hyN : (y : G) ∈ Subgroup.normalizer (Pc M V : Set G) :=
        h.toHyp.le_normalizer_Pc hyM
      have hconjP : conjSubgroup (y : G) (Pc M V) = Pc M V :=
        conjSubgroup_eq_self_iff.mpr hyN
      have himg : imgK V H (conjSubgroup (y : G) (Pc M V)) =
          conjSubgroup (piK V H y) (imgK V H (Pc M V)) := imgK_conjSubgroup y.2 hPH
      rw [hconjP] at himg
      exact conjSubgroup_eq_self_iff.mp himg.symm
    have heq := h.weaklyClosed_imgK hPH hgH hnorm
    have hsup : conjSubgroup g (Pc M V) ⊔ kOf V H = Pc M V ⊔ kOf V H :=
      ((imgK_eq_iff_sup_kOf_eq (V := V) (H := H) hPH hPgH).mp heq.symm).symm
    exact hgM (h.conjSubgroup_eq_self_of_sup_conj_Pc_eq hPH hgH hsup).1
  have hLH : hOf M V g ≤ H := sup_le hPH (conjSubgroup_le_of_le_of_mem hPH hgH)
  have hVLeL : V ≤ hOf M V g := h.toHyp.le_Pc.trans le_sup_left
  have hO2 : inSubgroup (pCore 2) (hOf M V g) ≠ ⊥ := by
    have hVle : V ≤ inSubgroup (pCore 2) (hOf M V g) := by
      have hLHnorm : hOf M V g ≤
          Subgroup.normalizer ((inSubgroup (pCore 2) H) : Set G) :=
        hLH.trans (inSubgroup_pCore_two H).2.2
      have h2 : IsPGroup 2 ↥(inSubgroup (pCore 2) H ⊓ hOf M V g) :=
        (inSubgroup_pCore_two H).1.to_le inf_le_left
      have hnorm : hOf M V g ≤ Subgroup.normalizer
          ((inSubgroup (pCore 2) H ⊓ hOf M V g : Subgroup G) : Set G) :=
        fun x hx => mem_normalizer_inf (hLHnorm hx) (Subgroup.le_normalizer hx)
      exact (le_inf hVH hVLeL).trans
        (Tim78.le_inSubgroup_pCore (M := hOf M V g) inf_le_right hnorm h2)
    intro hbot
    exact h.toHyp.ne_bot (le_bot_iff.mp (hVle.trans_eq hbot))
  exact ⟨conjSubgroup g V, (mem_sigmaSet_iff h.toHyp).mpr ⟨hO2, le_sup_left, hL⟩⟩

private theorem Sec5Hyp.not_forall_fSet_le_centralizer (hS : Sec5Hyp M V)
    {A B : Subgroup G} (hA : A ∈ fSet M V)
    (hlt : V < A ⊓ B) :
    ¬ ∀ C : Subgroup G, C ∈ fSet M V →
      C ≤ Pc M V ⊓ Subgroup.centralizer (A : Set G) := by
  intro hall
  have h := hS.toRootHyp
  let N : Subgroup G := ⨆ m : ↥M, conjSubgroup (m : G) A
  have hAN : A ≤ N := by
    have h1 := le_iSup (fun m : ↥M => conjSubgroup (m : G) A) (⟨1, M.one_mem⟩ : ↥M)
    simpa [N, conjSubgroup_one] using h1
  have hMN : M ≤ Subgroup.normalizer (N : Set G) := by
    simpa only [N, CGT.Timmesfeld75.conjSubgroup, iSup_subtype] using
      CFSG.Quasithin.MS93.le_normalizer_iSup_conj M A
  have hNP : N ≤ Pc M V := by
    refine iSup_le fun m => ?_
    calc conjSubgroup (m : G) A ≤ conjSubgroup (m : G) (Pc M V) :=
          Subgroup.map_mono (fSet.le_Pc hA)
      _ = Pc M V := conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer_Pc m.2)
  have hNleCA : N ≤ Pc M V ⊓ Subgroup.centralizer (A : Set G) := by
    refine iSup_le fun m => hall _ ?_
    exact hS.conj_mem_fSet m.2 hA
  have hAcentN : A ≤ Subgroup.centralizer (N : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hnCA : n ∈ Subgroup.centralizer (A : Set G) := (Subgroup.mem_inf.mp (hNleCA hn)).2
    exact (Subgroup.mem_centralizer_iff.mp hnCA a ha).symm
  have hZnorm : M ≤ Subgroup.normalizer
      ((N ⊓ Subgroup.centralizer (N : Set G) : Subgroup G) : Set G) :=
    fun m hm => mem_normalizer_inf (hMN hm) (mem_normalizer_centralizer (hMN hm))
  have hZleM : N ⊓ Subgroup.centralizer (N : Set G) ≤ M :=
    inf_le_left.trans (hNP.trans h.toHyp.Pc_le_M)
  have hZcomm : IsMulCommutative ↥(N ⊓ Subgroup.centralizer (N : Set G)) := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    have hxN : (x : G) ∈ N := (Subgroup.mem_inf.mp x.2).1
    have hyC : (y : G) ∈ Subgroup.centralizer (N : Set G) := (Subgroup.mem_inf.mp y.2).2
    exact Subgroup.mem_centralizer_iff.mp hyC (x : G) hxN
  have hVltZ : V < N ⊓ Subgroup.centralizer (N : Set G) :=
    lt_of_lt_of_le (lt_of_lt_of_le hlt inf_le_left) (le_inf hAN hAcentN)
  have hZleV := h.toHyp.maxAb.le_of_ge ⟨hZleM, hZnorm, hZcomm⟩ hVltZ.le
  exact (not_le_of_gt hVltZ) hZleV

private theorem Sec5Hyp.stmt51e_setup (hS : Sec5Hyp M V) {A B : Subgroup G}
    (hA : A ∈ fSet M V) (hB : B ∈ fSet M V) (hne : A ⊓ B ≠ V) :
    Pc M V ⊓ Subgroup.centralizer (A : Set G) =
        Pc M V ⊓ Subgroup.centralizer (B : Set G) ∧
      A ≤ Pc M V ⊓ Subgroup.centralizer (A : Set G) ∧
      B ≤ Pc M V ⊓ Subgroup.centralizer (A : Set G) ∧
      A ⊔ B ≤ Pc M V ∧ V < A ⊓ B ∧ ⁅Pc M V, Pc M V⁆ ≤ V := by
  obtain ⟨g, x₀, hUg, -, -, -, -⟩ := fSet.exists_plane hS hA
  have hSg := hS.shape hUg
  have hVle : V ≤ A ⊓ B := le_inf (fSet.V_le hA) (fSet.V_le hB)
  have hlt : V < A ⊓ B := lt_of_le_of_ne hVle (Ne.symm hne)
  have hnotsub : ¬ ((A ⊓ B : Subgroup G) : Set G) ⊆ (V : Set G) := by
    intro hsub
    exact hne (le_antisymm hsub hVle)
  obtain ⟨x, hx, hxV⟩ := Set.not_subset.mp hnotsub
  have hxA : x ∈ A := (Subgroup.mem_inf.mp hx).1
  have hxB : x ∈ B := (Subgroup.mem_inf.mp hx).2
  have hCxA := hS.stmt51b A hA x hxA hxV
  have hCxB := hS.stmt51b B hB x hxB hxV
  have hCA : Pc M V ⊓ Subgroup.centralizer (A : Set G) =
      Pc M V ⊓ Subgroup.centralizer (B : Set G) := hCxA.symm.trans hCxB
  have hBcomm := fSet.isMulCommutative hS hB
  have hBcent : B ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hBcomm
  have hBsingle : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxB)
  have hBle : B ≤ Pc M V ⊓ Subgroup.centralizer (A : Set G) := by
    have hBx : B ≤ Pc M V ⊓ Subgroup.centralizer ({x} : Set G) :=
      le_inf (fSet.le_Pc hB) (hBcent.trans hBsingle)
    rwa [hCxA] at hBx
  have hAcomm := fSet.isMulCommutative hS hA
  have hAle : A ≤ Pc M V ⊓ Subgroup.centralizer (A : Set G) :=
    le_inf (fSet.le_Pc hA) (Subgroup.le_centralizer_iff_isMulCommutative.mpr hAcomm)
  have hEsub : A ⊔ B ≤ Pc M V := sup_le (fSet.le_Pc hA) (fSet.le_Pc hB)
  exact ⟨hCA, hAle, hBle, hEsub, hlt, by rw [hSg.commutator_Pc hS.toRootHyp]⟩

private theorem Sec5Hyp.stmt51e_card {A B : Subgroup G}
    (hA : A ∈ fSet M V) (hB : B ∈ fSet M V) (hAB : A ≠ B) (hlt : V < A ⊓ B)
    (hBle : B ≤ Pc M V ⊓ Subgroup.centralizer (A : Set G)) :
    Nat.card V ^ 2 < Nat.card ↥(A ⊔ B) := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hBle hb)).2 a ha
  have hEcard : Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card V ^ 4 := by
    rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hcomm).1,
      fSet.card hA, fSet.card hB]
    ring
  have hcardVlt : Nat.card V < Nat.card ↥(A ⊓ B) := Subgroup.card_lt_of_lt hlt
  have hInfLtA : A ⊓ B < A := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hEq
    have hAleB : A ≤ B := hEq ▸ inf_le_right
    exact hAB (Subgroup.eq_of_le_of_card_ge hAleB
      (le_of_eq (by rw [fSet.card hA, fSet.card hB])))
  have hcardInfLt : Nat.card ↥(A ⊓ B) < Nat.card V ^ 2 := by
    have h1 := Subgroup.card_lt_of_lt hInfLtA
    rwa [fSet.card hA] at h1
  have hq2pos : 0 < Nat.card V ^ 2 := pow_pos (Nat.card_pos (α := ↥V)) 2
  have hmul : Nat.card V ^ 2 * Nat.card ↥(A ⊓ B) <
      Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := by
    calc Nat.card V ^ 2 * Nat.card ↥(A ⊓ B)
        < Nat.card V ^ 2 * Nat.card V ^ 2 :=
          Nat.mul_lt_mul_of_pos_left hcardInfLt hq2pos
      _ = Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := by rw [hEcard]; ring
  exact Nat.lt_of_mul_lt_mul_right hmul

private theorem Sec5Hyp.stmt51e_third (hS : Sec5Hyp M V) {A B : Subgroup G}
    (hA : A ∈ fSet M V) (hlt : V < A ⊓ B) :
    ∃ C ∈ fSet M V, ∃ c ∈ C, c ∉ V ∧
      C ⊓ (Pc M V ⊓ Subgroup.centralizer (A : Set G)) = V := by
  have hnotAll := hS.not_forall_fSet_le_centralizer hA hlt
  push Not at hnotAll
  obtain ⟨C, hC, hCnotle⟩ := hnotAll
  obtain ⟨c, hcC, hcCA⟩ := Set.not_subset.mp hCnotle
  have hcV : c ∉ V := by
    intro hcV
    apply hcCA
    refine Subgroup.mem_inf.mpr ⟨fSet.le_Pc hC hcC, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hVP : V ≤ Subgroup.centralizer (Pc M V : Set G) := by
      rw [hS.toRootHyp.toHyp.centralizer_Pc]
    exact Subgroup.mem_centralizer_iff.mp (hVP hcV) a (fSet.le_Pc hA ha)
  refine ⟨C, hC, c, hcC, hcV, ?_⟩
  refine le_antisymm ?_ (le_inf (fSet.V_le hC) (le_inf hS.toRootHyp.toHyp.le_Pc ?_))
  · intro y hy
    by_contra hyV
    have hyC : y ∈ C := (Subgroup.mem_inf.mp hy).1
    have hyCA : y ∈ Pc M V ⊓ Subgroup.centralizer (A : Set G) := (Subgroup.mem_inf.mp hy).2
    have hCy := hS.stmt51b C hC y hyC hyV
    have hAleCy : A ≤ Pc M V ⊓ Subgroup.centralizer ({y} : Set G) := by
      refine le_inf (fSet.le_Pc hA) ?_
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyCA).2 a ha
    have hALE : A ≤ Pc M V ⊓ Subgroup.centralizer (C : Set G) := by
      rwa [hCy] at hAleCy
    apply hCnotle
    refine le_inf (fSet.le_Pc hC) ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hALE ha)).2 z hz).symm
  · intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hVP : V ≤ Subgroup.centralizer (Pc M V : Set G) := by
      rw [hS.toRootHyp.toHyp.centralizer_Pc]
    exact Subgroup.mem_centralizer_iff.mp (hVP hv) a (fSet.le_Pc hA ha)

private theorem Sec5Hyp.stmt51e_product (hS : Sec5Hyp M V) {A C : Subgroup G}
    (hA : A ∈ fSet M V) (hC : C ∈ fSet M V)
    (hCcap : C ⊓ (Pc M V ⊓ Subgroup.centralizer (A : Set G)) = V) :
    (Pc M V : Set G) =
      (C : Set G) * ((Pc M V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
  let D : Subgroup G := Pc M V ⊓ Subgroup.centralizer (A : Set G)
  have hDcard : Nat.card D * Nat.card V = Nat.card ↥(Pc M V) := hS.stmt51d A hA
  have hCcard : Nat.card C = Nat.card V ^ 2 := fSet.card hC
  have hCcap' : C ⊓ D = V := hCcap
  have hcardCD : Nat.card ↥((C : Set G) * (D : Set G)) = Nat.card ↥(Pc M V) := by
    have hqpos : 0 < Nat.card V := Nat.card_pos
    have h1 : Nat.card ↥((C : Set G) * (D : Set G)) * Nat.card V =
        Nat.card ↥(Pc M V) * Nat.card V := by
      calc Nat.card ↥((C : Set G) * (D : Set G)) * Nat.card V
          = Nat.card C * Nat.card D := by
              have h' := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf C D
              rw [show C ⊓ D = V from hCcap'] at h'
              exact h'
        _ = Nat.card V ^ 2 * Nat.card D := by rw [hCcard]
        _ = (Nat.card D * Nat.card V) * Nat.card V := by ring
        _ = Nat.card ↥(Pc M V) * Nat.card V := by rw [hDcard]
    exact Nat.eq_of_mul_eq_mul_right hqpos h1
  have hDleP : D ≤ Pc M V := inf_le_left
  have hCDsub : (C : Set G) * (D : Set G) ⊆ (Pc M V : Set G) := by
    rintro p ⟨c', hc', d, hd', rfl⟩
    exact (Pc M V).mul_mem (fSet.le_Pc hC hc') (hDleP hd')
  refine ((Set.toFinite (Pc M V : Set G)).eq_of_subset_of_card_le hCDsub ?_).symm
  exact le_of_eq hcardCD.symm

private theorem Sec5Hyp.stmt51e_exists_t (hS : Sec5Hyp M V) {A B : Subgroup G} {c : G}
    (hcP : c ∈ Pc M V) (hVA : V ≤ A ⊔ B)
    (hEsub : A ⊔ B ≤ Pc M V) (hEgt : Nat.card V ^ 2 < Nat.card ↥(A ⊔ B))
    (hDZ : ⁅Pc M V, Pc M V⁆ ≤ V) :
    ∃ t : G, t ∈ (A ⊔ B) ⊓ Subgroup.centralizer ({c} : Set G) ∧ t ∉ V := by
  have hZD : V ≤ Subgroup.centralizer (Pc M V : Set G) := by
    rw [hS.toRootHyp.toHyp.centralizer_Pc]
  have hrel := CFSG.LocalAnalysis.EvenBN.Common.relIndex_inf_centralizer_le
    (D := Pc M V) (Z := V) (A := A ⊔ B) hDZ hZD hEsub hcP
  have hE_le : Nat.card ↥(A ⊔ B) ≤
      Nat.card ↥((A ⊔ B) ⊓ Subgroup.centralizer ({c} : Set G)) * Nat.card V := by
    have hkr : Nat.card ↥(A ⊔ B) =
        Nat.card ↥((A ⊔ B) ⊓ Subgroup.centralizer ({c} : Set G)) *
          ((A ⊔ B) ⊓ Subgroup.centralizer ({c} : Set G)).relIndex (A ⊔ B) := by
      have h1 := Subgroup.relIndex_mul_card
        (H := (A ⊔ B) ⊓ Subgroup.centralizer ({c} : Set G)) (K := A ⊔ B)
      rw [inf_eq_left.mpr inf_le_left] at h1
      rw [← h1, mul_comm]
    calc Nat.card ↥(A ⊔ B)
        = Nat.card ↥((A ⊔ B) ⊓ Subgroup.centralizer ({c} : Set G)) *
            ((A ⊔ B) ⊓ Subgroup.centralizer ({c} : Set G)).relIndex (A ⊔ B) := hkr
      _ ≤ Nat.card ↥((A ⊔ B) ⊓ Subgroup.centralizer ({c} : Set G)) * Nat.card V :=
          Nat.mul_le_mul_left _ hrel
  have hCEgt : Nat.card V <
      Nat.card ↥((A ⊔ B) ⊓ Subgroup.centralizer ({c} : Set G)) := by
    have hqpos : 0 < Nat.card V := Nat.card_pos
    have hlt' : Nat.card V * Nat.card V <
        Nat.card ↥((A ⊔ B) ⊓ Subgroup.centralizer ({c} : Set G)) * Nat.card V := by
      calc Nat.card V * Nat.card V = Nat.card V ^ 2 := by ring
        _ < Nat.card ↥(A ⊔ B) := hEgt
        _ ≤ Nat.card ↥((A ⊔ B) ⊓ Subgroup.centralizer ({c} : Set G)) * Nat.card V := hE_le
    exact Nat.lt_of_mul_lt_mul_right hlt'
  have hVleCE : V ≤ (A ⊔ B) ⊓ Subgroup.centralizer ({c} : Set G) := by
    refine le_inf hVA ?_
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hZD hv) c hcP).symm
  have hVneCE : V ≠ (A ⊔ B) ⊓ Subgroup.centralizer ({c} : Set G) := by
    intro hEq
    rw [hEq] at hCEgt
    exact lt_irrefl _ hCEgt
  have hnotsubCE : ¬
      (((A ⊔ B) ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) ⊆ (V : Set G) := by
    intro hsub
    exact hVneCE (le_antisymm hVleCE hsub)
  obtain ⟨t, ht, htV⟩ := Set.not_subset.mp hnotsubCE
  exact ⟨t, ht, htV⟩

private theorem Sec5Hyp.stmt51e_final (hS : Sec5Hyp M V) {A B C : Subgroup G} {c t : G}
    (hC : C ∈ fSet M V) (hcC : c ∈ C) (hcV : c ∉ V)
    (hCA : Pc M V ⊓ Subgroup.centralizer (A : Set G) =
        Pc M V ⊓ Subgroup.centralizer (B : Set G))
    (hAle : A ≤ Pc M V ⊓ Subgroup.centralizer (A : Set G))
    (hBle : B ≤ Pc M V ⊓ Subgroup.centralizer (A : Set G))
    (hEsub : A ⊔ B ≤ Pc M V)
    (hPset : (Pc M V : Set G) =
      (C : Set G) * ((Pc M V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G))
    (htE : t ∈ A ⊔ B) (htCc : t ∈ Subgroup.centralizer ({c} : Set G)) (htV : t ∉ V) : False := by
  let D : Subgroup G := Pc M V ⊓ Subgroup.centralizer (A : Set G)
  have htP : t ∈ Pc M V := hEsub htE
  have htCC : t ∈ Subgroup.centralizer (C : Set G) := by
    have h1 : t ∈ Pc M V ⊓ Subgroup.centralizer ({c} : Set G) := ⟨htP, htCc⟩
    have h1' : t ∈ Pc M V ⊓ Subgroup.centralizer (C : Set G) := by
      rwa [hS.stmt51b C hC c hcC hcV] at h1
    exact h1'.2
  have hEleCA : A ⊔ B ≤ Pc M V ⊓ Subgroup.centralizer (A : Set G) := sup_le hAle hBle
  have hDE : D = Pc M V ⊓ Subgroup.centralizer (A ⊔ B : Subgroup G) := by
    refine le_antisymm ?_ ?_
    · intro d hd
      have hdB : d ∈ Pc M V ⊓ Subgroup.centralizer (B : Set G) := by rwa [← hCA]
      refine Subgroup.mem_inf.mpr ⟨hd.1, ?_⟩
      have hAd : A ≤ Subgroup.centralizer ({d} : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 a ha
      have hBd : B ≤ Subgroup.centralizer ({d} : Set G) := by
        intro b hb
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hdB).2 b hb
      exact fun e he => Subgroup.mem_centralizer_singleton_iff.mp (sup_le hAd hBd he)
    · exact inf_le_inf le_rfl
        (Subgroup.centralizer_le (fun x hx => Subgroup.mem_sup_left hx))
  have htD : t ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hdE : d ∈ Subgroup.centralizer (A ⊔ B : Subgroup G) :=
      (Subgroup.mem_inf.mp (hDE ▸ hd)).2
    exact (Subgroup.mem_centralizer_iff.mp hdE t htE).symm
  have htCP : t ∈ Subgroup.centralizer (Pc M V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    rw [hPset] at hp
    obtain ⟨c', hc', d, hd', rfl⟩ := hp
    calc c' * d * t = c' * (d * t) := by group
      _ = c' * (t * d) := by rw [Subgroup.mem_centralizer_iff.mp htD d hd']
      _ = c' * t * d := by group
      _ = t * c' * d := by rw [Subgroup.mem_centralizer_iff.mp htCC c' hc']
      _ = t * (c' * d) := by group
  have htZ : t ∈ Pc M V ⊓ Subgroup.centralizer (Pc M V : Set G) := ⟨htP, htCP⟩
  rw [hS.toRootHyp.toHyp.center_Pc] at htZ
  exact htV htZ

theorem Sec5Hyp.stmt51e (hS : Sec5Hyp M V) : Sec5.Stmt51e M V := by
  intro A hA B hB
  by_cases hAB : A = B
  · exact Or.inl hAB
  right
  by_contra hne
  obtain ⟨hCA, hAle, hBle, hEsub, hlt, hDZ⟩ := hS.stmt51e_setup hA hB hne
  have hEgt := stmt51e_card hA hB hAB hlt hBle
  obtain ⟨C, hC, c, hcC, hcV, hCcap⟩ := hS.stmt51e_third hA hlt
  have hcP : c ∈ Pc M V := fSet.le_Pc hC hcC
  have hPset := hS.stmt51e_product hA hC hCcap
  have hVA : V ≤ A ⊔ B := (fSet.V_le hA).trans le_sup_left
  obtain ⟨t, ht, htV⟩ := hS.stmt51e_exists_t hcP hVA hEsub hEgt hDZ
  exact hS.stmt51e_final hC hcC hcV hCA hAle hBle hEsub hPset
    (Subgroup.mem_inf.mp ht).1 (Subgroup.mem_inf.mp ht).2 htV

private theorem Sec5Hyp.exists_shape_of_mem_sigmaSet (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) :
    ∃ g y : G, U = conjSubgroup g V ∧ y ∈ hOf M V g ∧
      Sec45Shape M V (hOf M V g) g ∧ conjSubgroup y V ≠ V ∧
      conjSubgroup g V = conjSubgroup y V ∧
      ⁅Pc M V, U⁆ = Pc M V ⊓ Tim79a.xOf V (hOf M V g) := by
  obtain ⟨g, rfl, hH⟩ := hU
  have h := hS.toRootHyp
  have hSg := hS.shape ⟨g, rfl, hH⟩
  obtain ⟨y, hyH, -, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hSg.Pc_le hSg.hH
  have hUy : conjSubgroup y V ∈ sigmaSet M V := by
    rw [← hVy]
    exact ⟨g, rfl, hH⟩
  have hyV : conjSubgroup y V ≠ V := ne_of_mem_sigmaSet h hUy
  refine ⟨g, y, rfl, hyH, hSg, hyV, hVy, ?_⟩
  rw [hVy]
  exact hSg.commutator_Pc_conj_eq h hyH hyV

theorem Sec5Hyp.stmt52a (hS : Sec5Hyp M V) : Sec5.Stmt52a M V := by
  intro U hU x hx
  obtain ⟨g, y, rfl, hyH, hSg, hyV, hVy, ha3g⟩ := hS.exists_shape_of_mem_sigmaSet hU
  have h := hS.toRootHyp
  have hxPW : x ∈ Pc M V ⊓ Tim79a.xOf V (hOf M V g) := by
    rwa [ha3g] at hx
  obtain ⟨x', hx'P, hx'K, hxC⟩ := hSg.exists_centralizing_not_mem_kOf h hxPW
  have hc3 := hSg.sup_commutator_eq h hyH hyV hx'P hx'K
  have hx'A : x ∈ V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x'⁆ := by
    have hmem : x ∈ Tim79a.xOf V (hOf M V g) ⊓ Subgroup.centralizer ({x'} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hxPW.2, hxC⟩
    rw [← hc3.1] at hmem
    rwa [← hVy] at hmem
  have hx'C : x' ∉ Subgroup.centralizer (conjSubgroup g V : Set G) := by
    rw [hVy]
    exact hSg.not_mem_centralizer_of_not_mem_kOf h hyH hyV hx'P hx'K
  have hAmem : V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x'⁆ ∈ fSet M V :=
    hS.stmt51a (conjSubgroup g V) hU x' hx'P hx'C
  have hAplane : V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x'⁆ =
      Tim79a.xOf V (hOf M V g) ⊓ Subgroup.centralizer ({x'} : Set G) := by
    rw [hVy]
    exact hc3.1
  have hAle : V ⊔ ⁅conjSubgroup g V, Subgroup.zpowers x'⁆ ≤
      ⁅Pc M V, conjSubgroup g V⁆ := by
    rw [ha3g, hAplane]
    exact le_inf (hSg.xOf_inf_centralizer_le_and_card h hx'P hx'K).1 inf_le_left
  exact ⟨_, hAmem, hx'A, hAle⟩

end CFSG.RankThree.GF2n.Tim81

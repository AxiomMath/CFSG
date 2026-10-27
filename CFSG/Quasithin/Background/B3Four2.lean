module

public import CFSG.Quasithin.Background.B3Four1

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ} {k : Mod}

theorem chkGenTabs_spec {gens : List Tab} (h : chkGenTabs n gens = true) :
    subOK n (closeT n gens) = true ∧ (∀ g ∈ gens, g ∈ closeT n gens) ∧
      Subgroup.closure {x : Gp n | tab x ∈ gens} = subOf n (closeT n gens) := by
  simp only [chkGenTabs, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨hS, hg⟩, hc⟩ := h
  exact ⟨hS, hg, closure_tabs_eq_subOf gens _ hS hg hc⟩

theorem cj_subOf_eq' {L K : List Tab} (hL : subOK n L = true) (hK : subOK n K = true) {g : Tab}
    (hg : isTab n g = true) (h : seteqT (conjT g L) K = true) :
    ∃ γ : Gp n, tab γ = g ∧ cj γ (subOf n L) = subOf n K := by
  obtain ⟨γ, rfl⟩ := exists_tab_eq hg
  refine ⟨γ, rfl, ?_⟩
  simp only [seteqT, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, conjT,
    List.mem_map] at h
  obtain ⟨h1, h2⟩ := h
  ext x
  rw [mem_cj, mem_subOf hL, mem_subOf hK]
  constructor
  · intro hx
    have := h1 (cjT (tab γ) (tab (γ⁻¹ * x * γ))) ⟨_, hx, rfl⟩
    rw [cjT_tab] at this
    simpa [mul_assoc] using this
  · intro hx
    obtain ⟨l, hl, hlx⟩ := h2 _ hx
    obtain ⟨y, rfl⟩ := exists_tab_eq ((subOK_spec hL).1 l hl)
    rw [cjT_tab] at hlx
    have h3 := tab_injective hlx
    rw [← h3]
    simpa [mul_assoc] using hl

theorem conjAut_eq_map_conj {W : Type*} [CommGroup W] (g : MulAut W) (A : Subgroup (MulAut W)) :
    B1.conjAut g A = A.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [B1.mem_conjAut, Subgroup.mem_map_equiv]
  simp

theorem exists_conj_le_sylow_sub {G : Type*} [Group G] [Finite G] {H T A : Subgroup G}
    (hTH : T ≤ H) (hTp : IsPGroup 2 T) (hidx : ¬ 2 ∣ (T.subgroupOf H).index) (hAH : A ≤ H)
    (hAp : IsPGroup 2 A) : ∃ g ∈ H, cj g A ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hTp
  have hTY : IsPGroup 2 ↥(T.subgroupOf H) := by
    apply IsPGroup.of_card (n := m)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv, hm]
  let TS : Sylow 2 ↥H := hTY.toSylow hidx
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hAp
  have hAY : IsPGroup 2 ↥(A.subgroupOf H) := by
    apply IsPGroup.of_card (n := j)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hj]
  obtain ⟨g, hg⟩ := exists_conj_le_sylow TS (A.subgroupOf H) hAY
  refine ⟨g.1, g.2, fun x hx => ?_⟩
  have ha : (g.1)⁻¹ * x * g.1 ∈ A := mem_cj.1 hx
  have haH : (g.1)⁻¹ * x * g.1 ∈ H := hAH ha
  have hmem : (g * ⟨(g.1)⁻¹ * x * g.1, haH⟩ * g⁻¹ : ↥H) ∈ cj g (A.subgroupOf H) := by
    rw [mem_cj]
    have e : (g⁻¹ * (g * ⟨(g.1)⁻¹ * x * g.1, haH⟩ * g⁻¹) * g : ↥H) =
        ⟨(g.1)⁻¹ * x * g.1, haH⟩ := by group
    rw [e, Subgroup.mem_subgroupOf]
    exact ha
  have h2 : ((g * ⟨(g.1)⁻¹ * x * g.1, haH⟩ * g⁻¹ : ↥H) : G) ∈ T := hg hmem
  simpa [mul_assoc] using h2

theorem isFFStar_iff_offG {H K : Subgroup (Gp n)} (hKH : K ≤ H) :
    IsFFStarOffender (H.map (Mod.act n k)) (K.map (Mod.act n k)) ↔ IsOffG n k K := by
  unfold IsOffG
  exact ⟨fun h => ⟨h.1.trans (Subgroup.map_mono le_top), h.2⟩,
    fun h => ⟨Subgroup.map_mono hKH, h.2⟩⟩

theorem mem_offsH_iff (b : Bool) {K : List Tab} (hK : K ∈ Dl n) :
    K ∈ offsH n k b ↔ offOK n k (Dl n) K = true ∧ subsetT K (Tgl n b) = true := by
  simp only [offsH, offsK, List.mem_filter, hK, true_and, offP_mkDF]

theorem mem_offsH_iff' (hn : 5 ≤ n) (b : Bool) (hTl : subOK n (Tl n) = true)
    (hEA : chkEA n (Tl n) (Dl n) = true) {K : List Tab} (hK : K ∈ Dl n) :
    K ∈ offsH n k b ↔ IsOffG n k (subOf n K) ∧ subsetT K (Tgl n b) = true := by
  rw [mem_offsH_iff b hK, isOffG_iff_offOK hn k hTl hEA hK]

theorem mem_Dl_of_mem_offsH {b : Bool} {K : List Tab} (hK : K ∈ offsH n k b) : K ∈ Dl n :=
  (List.mem_filter.1 (List.mem_filter.1 hK).1).1

structure Std (n : ℕ) (b : Bool) : Prop where
  five : 5 ≤ n
  hTl : subOK n (Tl n) = true
  hEA : chkEA n (Tl n) (Dl n) = true
  hT0 : subOK n (Tgl n b) = true
  hsub : ∀ t ∈ Tgl n b, t ∈ Tl n
  hTH : Tgrp n b ≤ Hg n b
  hp : IsPGroup 2 (Tgrp n b)
  hidx : ¬ 2 ∣ ((Tgrp n b).subgroupOf (Hg n b)).index

theorem offsH_spec {b : Bool} (hS : Std n b) {K : List Tab} (hK : K ∈ offsH n k b) :
    K ∈ Dl n ∧ subOK n K = true ∧ IsOffG n k (subOf n K) ∧ subOf n K ≤ Tgrp n b := by
  have hD : K ∈ Dl n := mem_Dl_of_mem_offsH hK
  obtain ⟨-, hmem, -⟩ := chkEA_spec hS.hEA
  have hKok : subOK n K = true := (hmem K hD).1
  obtain ⟨hoff, hsubs⟩ := (mem_offsH_iff' hS.five b hS.hTl hS.hEA hD).1 hK
  refine ⟨hD, hKok, hoff, fun x hx => ?_⟩
  rw [mem_subOf hKok] at hx
  rw [mem_Tgrp b hS.hT0]
  simp only [subsetT, List.all_eq_true, List.contains_iff_mem] at hsubs
  exact hsubs _ hx

theorem exists_offsH {b : Bool} (hS : Std n b) {A : Subgroup (Gp n)} (hA : IsOffG n k A)
    (hAT : A ≤ Tgrp n b) : ∃ K ∈ offsH n k b, subOf n K = A := by
  obtain ⟨hcomm, hsq⟩ := hA.comm_sq hS.five
  obtain ⟨C, hC, hCok, hAC⟩ := exists_mem_D hS.hTl hS.hEA A
    (fun x hx => hS.hsub _ ((mem_Tgrp b hS.hT0).1 (hAT hx))) hcomm hsq
  have hAeq : A = subOf n C := subOf_eq hCok hAC
  refine ⟨C, (mem_offsH_iff' hS.five b hS.hTl hS.hEA hC).2 ⟨by rw [← hAeq]; exact hA, ?_⟩,
    hAeq.symm⟩
  simp only [subsetT, List.all_eq_true, List.contains_iff_mem]
  intro t ht
  obtain ⟨x, rfl⟩ := exists_tab_eq ((subOK_spec hCok).1 t ht)
  exact (mem_Tgrp b hS.hT0).1 (hAT ((hAC x).2 ht))

open Classical in
@[expose] noncomputable def SP (n : ℕ) (k : Mod) (b : Bool)
    (P : Set (Subgroup (MulAut (Mod.V n k)))) : List (List Tab) :=
  (offsH n k b).filter (fun K => decide ((subOf n K).map (Mod.act n k) ∈ P))

theorem mem_SP {b : Bool} {P : Set (Subgroup (MulAut (Mod.V n k)))} {K : List Tab} :
    K ∈ SP n k b P ↔ K ∈ offsH n k b ∧ (subOf n K).map (Mod.act n k) ∈ P := by
  unfold SP
  simp only [List.mem_filter, decide_eq_true_eq]

theorem SP_sublist (b : Bool) (P : Set (Subgroup (MulAut (Mod.V n k)))) :
    (SP n k b P).Sublist (offsH n k b) :=
  List.filter_sublist

theorem lookup_map_pair {α β : Type*} [BEq α] [LawfulBEq α] (f : α → β) {l : List α} {a : α}
    (h : a ∈ l) : (l.map (fun x => (x, f x))).lookup a = some (f a) := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    by_cases hx : a = x
    · subst hx
      simp
    · have hl : a ∈ l := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h hx
        · exact h
      have hne : (a == x) = false := by simpa using hx
      simp only [List.map_cons, List.lookup_cons, hne]
      exact ih hl

theorem stableB_SP {b : Bool} (hS : Std n b) {P : Set (Subgroup (MulAut (Mod.V n k)))}
    (hP : IsStableFF ((Hg n b).map (Mod.act n k)) P) :
    stableB (nbrTab n k (Hl n b) (offsH n k b)) (SP n k b P) = true := by
  simp only [stableB, List.all_eq_true, List.contains_iff_mem]
  intro K hK K' hK'
  obtain ⟨hKo, hKP⟩ := mem_SP.1 hK
  have hlk : (nbrTab n k (Hl n b) (offsH n k b)).lookup K =
      some (nbrK n k (Hl n b) (offsH n k b) K) :=
    lookup_map_pair (fun K => nbrK n k (Hl n b) (offsH n k b) K) hKo
  rw [hlk] at hK'
  simp only [Option.getD_some, nbrK, List.mem_filter, Bool.or_eq_true] at hK'
  obtain ⟨hK'o, hfl⟩ := hK'
  refine mem_SP.2 ⟨hK'o, ?_⟩
  obtain ⟨hDK, hKok, hKoff, hKT⟩ := offsH_spec hS hKo
  obtain ⟨hDK', hKok', hKoff', hKT'⟩ := offsH_spec hS hK'o
  rcases hfl with hfus | hles
  · simp only [fusB, List.any_eq_true] at hfus
    obtain ⟨g, hg, hgc⟩ := hfus
    obtain ⟨σ, hσ, rfl⟩ := (Hl_spec b).2 g hg
    obtain ⟨γ, hγ, hcj⟩ := cj_subOf_eq' hKok hKok' (isTab_tab σ) hgc
    have hγσ : γ = σ := tab_injective hγ
    subst hγσ
    rw [← hcj, map_cj, conjAut_eq_map_conj]
    exact hP.2.2.1 _ hKP _ (Subgroup.mem_map_of_mem _ hσ)
  · simp only [lesB, Bool.and_eq_true, beq_iff_eq] at hles
    obtain ⟨hsubs, hF⟩ := hles
    have hle : subOf n K' ≤ subOf n K := by
      intro x hx
      rw [mem_subOf hKok'] at hx
      rw [mem_subOf hKok]
      simp only [subsetT, List.all_eq_true, List.contains_iff_mem] at hsubs
      exact hsubs _ hx
    refine hP.2.2.2 _ hKP _ ?_
    refine ⟨((isFFStar_iff_offG (hKT'.trans hS.hTH)).2 hKoff').isA2,
      ((isFFStar_iff_offG (hKT.trans hS.hTH)).2 hKoff).isA2, Subgroup.map_mono hle, ?_⟩
    have e1 := fval_eq hS.five k hKok' (K := subOf n K') (fun x => mem_subOf hKok')
    have e2 := fval_eq hS.five k hKok (K := subOf n K) (fun x => mem_subOf hKok)
    rw [hF] at e1
    exact Nat.eq_of_mul_eq_mul_right (cN_pos k) (e1.trans e2.symm)

theorem exists_pullback_le (hn : 5 ≤ n) (k : Mod) {B : Subgroup (Gp n)}
    {A : Subgroup (MulAut (Mod.V n k))} (hA : A ≤ B.map (Mod.act n k)) :
    ∃ A' : Subgroup (Gp n), A' ≤ B ∧ A'.map (Mod.act n k) = A := by
  have hinj := act_injective hn k
  refine ⟨A.comap (Mod.act n k), fun x hx => ?_,
    Subgroup.map_comap_eq_self (hA.trans (Subgroup.map_le_range _ _))⟩
  obtain ⟨h, hh, hhx⟩ := hA hx
  rw [← hinj hhx]
  exact hh

theorem isOffG_of_stable {b : Bool} {P : Set (Subgroup (MulAut (Mod.V n k)))}
    (hP : IsStableFF ((Hg n b).map (Mod.act n k)) P) {A' : Subgroup (Gp n)}
    (hA : A'.map (Mod.act n k) ∈ P) : IsOffG n k A' := by
  have h := hP.2.1 _ hA
  exact ⟨h.1.trans (Subgroup.map_mono le_top), h.2⟩

theorem SP_ne_nil {b : Bool} (hS : Std n b) {P : Set (Subgroup (MulAut (Mod.V n k)))}
    (hP : IsStableFF ((Hg n b).map (Mod.act n k)) P) : SP n k b P ≠ [] := by
  obtain ⟨A, hA⟩ := hP.1
  obtain ⟨A', hA'H, hmap⟩ := exists_pullback_le hS.five k (hP.2.1 A hA).1
  rw [← hmap] at hA
  have hoff : IsOffG n k A' := isOffG_of_stable hP hA
  have hA'p : IsPGroup 2 A' := isPGroup_of_sq (hoff.comm_sq hS.five).2
  obtain ⟨g, hgH, hg⟩ := exists_conj_le_sylow_sub hS.hTH hS.hp hS.hidx hA'H hA'p
  obtain ⟨K, hKo, hK⟩ := exists_offsH hS (hoff.cj g) hg
  refine List.ne_nil_of_mem (a := K) (mem_SP.2 ⟨hKo, ?_⟩)
  rw [hK, map_cj, conjAut_eq_map_conj]
  exact hP.2.2.1 _ hA _ (Subgroup.mem_map_of_mem _ hgH)

theorem ffJP_SP {b : Bool} (hS : Std n b) {P : Set (Subgroup (MulAut (Mod.V n k)))}
    (hP : IsStableFF ((Hg n b).map (Mod.act n k)) P) {B : List Tab} (hB : subOK n B = true)
    (hBT : subsetT B (Tgl n b) = true) (hJ : jOK n B (SP n k b P) = true) :
    ffJP P ((subOf n B).map (Mod.act n k)) =
      (subOf n (jOf n B (SP n k b P))).map (Mod.act n k) := by
  obtain ⟨hJok, hJgens, hJcl⟩ := chkGenTabs_spec hJ
  have hinj := act_injective hS.five k
  have hBle : subOf n B ≤ Tgrp n b := by
    intro x hx
    rw [mem_subOf hB] at hx
    rw [mem_Tgrp b hS.hT0]
    simp only [subsetT, List.all_eq_true, List.contains_iff_mem] at hBT
    exact hBT _ hx
  apply le_antisymm
  · refine iSup_le fun A => iSup_le fun hA => iSup_le fun hAB => ?_
    obtain ⟨A', hA'H, hmap⟩ := exists_pullback_le hS.five k
      (hAB.trans (Subgroup.map_mono (hBle.trans hS.hTH)))
    have hA'B : A' ≤ subOf n B := by
      intro x hx
      have h1 : Mod.act n k x ∈ A := by rw [← hmap]; exact Subgroup.mem_map_of_mem _ hx
      obtain ⟨y, hy, hyx⟩ := hAB h1
      rw [← hinj hyx]
      exact hy
    have hA' : A'.map (Mod.act n k) ∈ P := by rw [hmap]; exact hA
    obtain ⟨K, hKo, hK⟩ := exists_offsH hS (isOffG_of_stable hP hA') (hA'B.trans hBle)
    obtain ⟨-, hKok, -, -⟩ := offsH_spec hS hKo
    have hKP : (subOf n K).map (Mod.act n k) ∈ P := by rw [hK]; exact hA'
    have hKB : subsetT K B = true := by
      simp only [subsetT, List.all_eq_true, List.contains_iff_mem]
      intro t ht
      obtain ⟨x, rfl⟩ := exists_tab_eq ((subOK_spec hKok).1 t ht)
      have hx : x ∈ A' := by rw [← hK]; exact (mem_subOf hKok).2 ht
      exact (mem_subOf hB).1 (hA'B hx)
    rw [← hmap, ← hK]
    refine Subgroup.map_mono fun x hx => ?_
    rw [mem_subOf hKok] at hx
    have hjo : jOf n B (SP n k b P) =
        closeT n ((SP n k b P).filter (fun K => subsetT K B)).flatten := rfl
    rw [hjo, mem_subOf hJok]
    apply hJgens
    simp only [List.mem_flatten, List.mem_filter]
    exact ⟨K, ⟨mem_SP.2 ⟨hKo, hKP⟩, hKB⟩, hx⟩
  · have hjo : jOf n B (SP n k b P) =
        closeT n ((SP n k b P).filter (fun K => subsetT K B)).flatten := rfl
    rw [hjo, ← hJcl, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_ofPred_eq, List.mem_flatten, List.mem_filter] at hx
    obtain ⟨K, ⟨hKS, hKB⟩, hxK⟩ := hx
    obtain ⟨hKo, hKP⟩ := mem_SP.1 hKS
    obtain ⟨-, hKok, -, -⟩ := offsH_spec hS hKo
    have hKle : subOf n K ≤ subOf n B := by
      intro y hy
      rw [mem_subOf hKok] at hy
      rw [mem_subOf hB]
      simp only [subsetT, List.all_eq_true, List.contains_iff_mem] at hKB
      exact hKB _ hy
    have hle : (subOf n K).map (Mod.act n k) ≤ ffJP P ((subOf n B).map (Mod.act n k)) :=
      le_iSup_of_le _ (le_iSup_of_le hKP (le_iSup_of_le (Subgroup.map_mono hKle) le_rfl))
    exact hle (Subgroup.mem_map_of_mem _ ((mem_subOf hKok).2 hxK))

end CFSG.Quasithin.B3

module

public import CFSG.Milestones.ASVolI.C31.J4NP.Aff
public import CFSG.Milestones.ASVolI.C31.J4NP.Enc
public import CFSG.Milestones.ASVolI.C31.J4NP.Orbit
public import CFSG.Milestones.ASVolI.C31.J4NP.TreeDefs
public import Certificates.Data.CFSGNative.J4Tree.Node

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.J4Tree.Native CFSG.J4Tree.Native.Node

section BFS

variable {α : Type} (gs : List α) (step : α → Code → Code) (P : Code → Prop)

theorem burnsideJ4NP_bfs_inner_sound (hP : ∀ y, P y → ∀ g ∈ gs, P (step g y)) (x : Code)
    (hx : P x) : ∀ (l : List α) (acc : Std.HashSet Code × List Code),
      (∀ y ∈ acc.1, P y) → (∀ y ∈ acc.2, P y) → (∀ g ∈ l, g ∈ gs) →
      (∀ y ∈ (l.foldl (fun (acc : Std.HashSet Code × List Code) g =>
        let y := step g x
        if acc.1.contains y then acc else (acc.1.insert y, y :: acc.2)) acc).1, P y) ∧
      (∀ y ∈ (l.foldl (fun (acc : Std.HashSet Code × List Code) g =>
        let y := step g x
        if acc.1.contains y then acc else (acc.1.insert y, y :: acc.2)) acc).2, P y) := by
  intro l
  induction l with
  | nil => intro acc h1 h2 _; exact ⟨h1, h2⟩
  | cons g l ih =>
    intro acc h1 h2 hg
    simp only [List.foldl_cons]
    have hg' : g ∈ gs := hg g List.mem_cons_self
    have hl : ∀ g ∈ l, g ∈ gs := fun g' hg'' => hg g' (List.mem_cons_of_mem _ hg'')
    split_ifs with hc
    · exact ih acc h1 h2 hl
    · refine ih _ ?_ ?_ hl
      · intro y hy
        rw [Std.HashSet.mem_insert] at hy
        rcases hy with hy | hy
        · have : step g x = y := beq_iff_eq.mp hy
          rw [← this]
          exact hP x hx g hg'
        · exact h1 y hy
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hP x hx g hg'
        · exact h2 y hy

theorem burnsideJ4NP_bfsStep_sound (hP : ∀ y, P y → ∀ g ∈ gs, P (step g y))
    (S : Std.HashSet Code) (F : List Code) (hS : ∀ y ∈ S, P y) (hF : ∀ y ∈ F, P y) :
    (∀ y ∈ (bfsStep gs step S F).1, P y) ∧ (∀ y ∈ (bfsStep gs step S F).2, P y) := by
  unfold bfsStep
  have key : ∀ (l : List Code) (acc : Std.HashSet Code × List Code), (∀ y ∈ acc.1, P y) →
      (∀ y ∈ acc.2, P y) → (∀ x ∈ l, P x) →
      (∀ y ∈ (l.foldl (fun acc x => gs.foldl (fun (acc : Std.HashSet Code × List Code) g =>
        let y := step g x
        if acc.1.contains y then acc else (acc.1.insert y, y :: acc.2)) acc) acc).1, P y) ∧
      (∀ y ∈ (l.foldl (fun acc x => gs.foldl (fun (acc : Std.HashSet Code × List Code) g =>
        let y := step g x
        if acc.1.contains y then acc else (acc.1.insert y, y :: acc.2)) acc) acc).2, P y) := by
    intro l
    induction l with
    | nil => intro acc h1 h2 _; exact ⟨h1, h2⟩
    | cons x l ih =>
      intro acc h1 h2 hl
      simp only [List.foldl_cons]
      have hx : P x := hl x List.mem_cons_self
      obtain ⟨h1', h2'⟩ := burnsideJ4NP_bfs_inner_sound gs step P hP x hx gs acc h1 h2
        (fun g hg => hg)
      exact ih _ h1' h2' (fun x' hx' => hl x' (List.mem_cons_of_mem _ hx'))
  exact key F (S, []) hS (fun y hy => absurd hy List.not_mem_nil) hF

theorem burnsideJ4NP_bfsRun_sound (hP : ∀ y, P y → ∀ g ∈ gs, P (step g y)) :
    ∀ (n : ℕ) (st : Std.HashSet Code × List Code), (∀ y ∈ st.1, P y) → (∀ y ∈ st.2, P y) →
      ∀ y ∈ (bfsRun gs step n st).1, P y := by
  intro n
  induction n with
  | zero => intro st h1 _ y hy; exact h1 y hy
  | succ n ih =>
    intro st h1 h2 y hy
    simp only [bfsRun] at hy
    split_ifs at hy
    · exact h1 y hy
    · obtain ⟨h1', h2'⟩ := burnsideJ4NP_bfsStep_sound gs step P hP st.1 st.2 h1 h2
      exact ih _ h1' h2' y hy

theorem burnsideJ4NP_bfsFrom_sound (hP : ∀ y, P y → ∀ g ∈ gs, P (step g y)) (x₀ : Code)
    (h0 : P x₀) (n : ℕ) : ∀ y ∈ bfsFrom gs step x₀ n, P y := by
  refine burnsideJ4NP_bfsRun_sound gs step P hP n _ ?_ ?_
  · intro y hy
    rw [Std.HashSet.mem_insert] at hy
    rcases hy with hy | hy
    · have : x₀ = y := beq_iff_eq.mp hy
      exact this ▸ h0
    · have := Std.HashSet.contains_iff_mem.mpr hy
      simp [Std.HashSet.contains_empty] at this
  · intro y hy
    rw [List.mem_singleton] at hy
    exact hy ▸ h0

theorem burnsideJ4NP_closedUnder_spec {S : Std.HashSet Code} (h : closedUnder gs step S = true) :
    ∀ x ∈ S, ∀ g ∈ gs, step g x ∈ S := by
  simp only [closedUnder, List.all_eq_true] at h
  intro x hx g hg
  exact Std.HashSet.contains_iff_mem.mp (h x (Std.HashSet.mem_toList.mpr hx) g hg)

end BFS

theorem burnsideJ4NP_hashSet_nodup (S : Std.HashSet Code) : S.toList.Nodup :=
  Std.HashSet.distinct_toList.imp fun {a b} h hab => by simp [hab] at h

@[expose] noncomputable def burnsideJ4NP_encJ (g : J) : Code :=
  open scoped Classical in if h : g ∈ Hj then burnsideJ4NP_enc ⟨g, h⟩ else 1

theorem burnsideJ4NP_encJ_of_mem {g : J} (hg : g ∈ Hj) :
    burnsideJ4NP_encJ g = burnsideJ4NP_enc ⟨g, hg⟩ := by
  classical
  unfold burnsideJ4NP_encJ
  exact dif_pos hg

theorem burnsideJ4NP_treeElt_mem_P0 {ce : ℕ × ℕ}
    (he : ce.2 < 1024) : burnsideJ4NP_treeElt ce ∈ P0 :=
  eta_mul_Kel_mem he

theorem burnsideJ4NP_treeElt_mem
    {ce : ℕ × ℕ} (he : ce.2 < 1024) : burnsideJ4NP_treeElt ce ∈ Hj :=
  P0_le_Hj (burnsideJ4NP_treeElt_mem_P0 he)

section Enc

theorem burnsideJ4NP_encJ_mul {g h : J} (hg : g ∈ Hj) (hh : h ∈ Hj) :
    burnsideJ4NP_encJ (g * h) = burnsideJ4NP_encJ g * burnsideJ4NP_encJ h := by
  rw [burnsideJ4NP_encJ_of_mem (Hj.mul_mem hg hh), burnsideJ4NP_encJ_of_mem hg,
    burnsideJ4NP_encJ_of_mem hh]
  exact burnsideJ4NP_enc_isEnc.map_mul ⟨g, hg⟩ ⟨h, hh⟩

theorem burnsideJ4NP_encJ_one : burnsideJ4NP_encJ 1 = 1 := by
  rw [burnsideJ4NP_encJ_of_mem Hj.one_mem]
  exact burnsideJ4NP_enc_isEnc.map_one

theorem burnsideJ4NP_encJ_injOn : Set.InjOn burnsideJ4NP_encJ (Hj : Set J) := by
  intro g hg h hh e
  rw [burnsideJ4NP_encJ_of_mem hg, burnsideJ4NP_encJ_of_mem hh] at e
  exact congrArg Subtype.val (burnsideJ4NP_enc_isEnc.inj e)

theorem burnsideJ4NP_encJ_inj {g h : J} (hg : g ∈ Hj) (hh : h ∈ Hj)
    (e : burnsideJ4NP_encJ g = burnsideJ4NP_encJ h) : g = h :=
  burnsideJ4NP_encJ_injOn hg hh e

theorem burnsideJ4NP_encJ_mul₃ {g x g' : J} (hg : g ∈ Hj) (hx : x ∈ Hj) (hg' : g' ∈ Hj) :
    burnsideJ4NP_encJ (g * x * g') =
      burnsideJ4NP_encJ g * burnsideJ4NP_encJ x * burnsideJ4NP_encJ g' := by
  rw [burnsideJ4NP_encJ_mul (Hj.mul_mem hg hx) hg', burnsideJ4NP_encJ_mul hg hx]

theorem burnsideJ4NP_commute_iff_code {x y : J} (hx : x ∈ Hj) (hy : y ∈ Hj) :
    x * y = y * x ↔ burnsideJ4NP_encJ x * burnsideJ4NP_encJ y =
      burnsideJ4NP_encJ y * burnsideJ4NP_encJ x := by
  rw [← burnsideJ4NP_encJ_mul hx hy, ← burnsideJ4NP_encJ_mul hy hx]
  exact ⟨fun h => by rw [h], fun h => burnsideJ4NP_encJ_inj (Hj.mul_mem hx hy) (Hj.mul_mem hy hx) h⟩

theorem burnsideJ4NP_sq_iff_code {x : J} (hx : x ∈ Hj) :
    x * x = 1 ↔ burnsideJ4NP_encJ x * burnsideJ4NP_encJ x = 1 := by
  rw [← burnsideJ4NP_encJ_mul hx hx, ← burnsideJ4NP_encJ_one]
  exact ⟨fun h => by rw [h], fun h => burnsideJ4NP_encJ_inj (Hj.mul_mem hx hx) Hj.one_mem h⟩

theorem burnsideJ4NP_encJ_inv {g : J} (hg : g ∈ Hj) {a : Code} (ha : burnsideJ4NP_encJ g * a = 1)
    (hwf : a.wf = true) : burnsideJ4NP_encJ g⁻¹ = a := by
  rw [burnsideJ4NP_encJ_of_mem (Hj.inv_mem hg)]
  refine (burnsideJ4NP_enc_eq_iff (burnsideJ4NP_codeWF_of_wf hwf)).2 ?_
  have h1 := congrArg burnsideJ4NP_codeMat ha
  rw [burnsideJ4NP_codeMat_mul, burnsideJ4NP_codeMat_one, burnsideJ4NP_encJ_of_mem hg,
    burnsideJ4NP_codeMat_enc] at h1
  calc burnsideJ4NP_rho g⁻¹
      = burnsideJ4NP_rho g⁻¹ * (burnsideJ4NP_rho g * burnsideJ4NP_codeMat a) := by
        rw [h1, Matrix.mul_one]
    _ = (burnsideJ4NP_rho g⁻¹ * burnsideJ4NP_rho g) * burnsideJ4NP_codeMat a := by
        rw [Matrix.mul_assoc]
    _ = burnsideJ4NP_codeMat a := by rw [burnsideJ4NP_rho_inv_mul hg, Matrix.one_mul]

theorem burnsideJ4NP_encJ_treeElt {ce : ℕ × ℕ}
    (he : ce.2 < 1024) : burnsideJ4NP_encJ (burnsideJ4NP_treeElt ce) = cc ce := by
  rw [burnsideJ4NP_encJ_of_mem (burnsideJ4NP_treeElt_mem he)]
  exact burnsideJ4NP_enc_eta_mul_Kel ce.1 he

theorem burnsideJ4NP_map_encJ_treeElt {l : List (ℕ × ℕ)}
    (hl : ∀ ce ∈ l, ce.2 < 1024) :
    (l.map burnsideJ4NP_treeElt).map burnsideJ4NP_encJ = l.map cc := by
  rw [List.map_map]
  exact List.map_congr_left fun ce hce => burnsideJ4NP_encJ_treeElt (hl ce hce)

theorem burnsideJ4NP_bfs_closure_sound {gens : List J} (hgH : ∀ g ∈ gens, g ∈ Hj) (n : ℕ) :
    ∀ r ∈ bfsFrom (gens.map burnsideJ4NP_encJ) rmul 1 n,
      ∃ x ∈ Subgroup.closure {g | g ∈ gens}, burnsideJ4NP_encJ x = r := by
  have hle : Subgroup.closure {g | g ∈ gens} ≤ Hj := (Subgroup.closure_le Hj).mpr hgH
  refine burnsideJ4NP_bfsFrom_sound _ _ _ ?_ 1 ⟨1, Subgroup.one_mem _, burnsideJ4NP_encJ_one⟩ n
  rintro y ⟨x, hx, rfl⟩ g' hg'
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
  refine ⟨x * g, Subgroup.mul_mem _ hx (Subgroup.subset_closure hg), ?_⟩
  exact burnsideJ4NP_encJ_mul (hle hx) (hgH g hg)

theorem burnsideJ4NP_mem_closure_iff_bfs {gens : List J} (hgH : ∀ g ∈ gens, g ∈ Hj) {n : ℕ}
    (h1 : (bfsFrom (gens.map burnsideJ4NP_encJ) rmul 1 n).contains 1 = true)
    (hcl : closedUnder (gens.map burnsideJ4NP_encJ) rmul
      (bfsFrom (gens.map burnsideJ4NP_encJ) rmul 1 n) = true) {x : J} (hx : x ∈ Hj) :
    x ∈ Subgroup.closure {g | g ∈ gens} ↔
      burnsideJ4NP_encJ x ∈ bfsFrom (gens.map burnsideJ4NP_encJ) rmul 1 n := by
  set T := bfsFrom (gens.map burnsideJ4NP_encJ) rmul 1 n
  have hc := burnsideJ4NP_closedUnder_spec _ _ hcl
  have := burnsideJ4NP_mem_closure_iff_of_closed_enc (H := Hj) (enc := burnsideJ4NP_encJ)
    burnsideJ4NP_encJ_injOn (fun x hx y hy => burnsideJ4NP_encJ_mul hx hy) burnsideJ4NP_encJ_one
    (gens := {g | g ∈ gens}) (fun g hg => hgH g hg) T.toList.toFinset
    (by rw [List.mem_toFinset, Std.HashSet.mem_toList]; exact Std.HashSet.contains_iff_mem.mp h1)
    (fun r hr g hg => by
      rw [List.mem_toFinset, Std.HashSet.mem_toList] at hr ⊢
      exact hc r hr _ (List.mem_map_of_mem hg))
    (fun r hr => by
      rw [List.mem_toFinset, Std.HashSet.mem_toList] at hr
      exact burnsideJ4NP_bfs_closure_sound hgH n r hr) hx
  rw [this, List.mem_toFinset, Std.HashSet.mem_toList]

theorem burnsideJ4NP_card_closure_bfs {gens : List J} (hgH : ∀ g ∈ gens, g ∈ Hj) {n : ℕ}
    (h1 : (bfsFrom (gens.map burnsideJ4NP_encJ) rmul 1 n).contains 1 = true)
    (hcl : closedUnder (gens.map burnsideJ4NP_encJ) rmul
      (bfsFrom (gens.map burnsideJ4NP_encJ) rmul 1 n) = true) :
    Nat.card (Subgroup.closure {g | g ∈ gens}) =
      (bfsFrom (gens.map burnsideJ4NP_encJ) rmul 1 n).size := by
  set T := bfsFrom (gens.map burnsideJ4NP_encJ) rmul 1 n
  have hc := burnsideJ4NP_closedUnder_spec _ _ hcl
  rw [burnsideJ4NP_card_closure_of_closed_enc (H := Hj) (enc := burnsideJ4NP_encJ)
    burnsideJ4NP_encJ_injOn (fun x hx y hy => burnsideJ4NP_encJ_mul hx hy) burnsideJ4NP_encJ_one
    (gens := {g | g ∈ gens}) (fun g hg => hgH g hg) T.toList.toFinset
    (by rw [List.mem_toFinset, Std.HashSet.mem_toList]; exact Std.HashSet.contains_iff_mem.mp h1)
    (fun r hr g hg => by
      rw [List.mem_toFinset, Std.HashSet.mem_toList] at hr ⊢
      exact hc r hr _ (List.mem_map_of_mem hg))
    (fun r hr => by
      rw [List.mem_toFinset, Std.HashSet.mem_toList] at hr
      exact burnsideJ4NP_bfs_closure_sound hgH n r hr),
    List.toFinset_card_of_nodup (burnsideJ4NP_hashSet_nodup T), Std.HashSet.length_toList]

theorem burnsideJ4NP_card_orbit_bfs {gens : List J} (hgH : ∀ g ∈ gens, g ∈ Hj)
    {gp : List (Code × Code)}
    (hgp : ∀ p ∈ gp, ∃ g ∈ gens, p = (burnsideJ4NP_encJ g, burnsideJ4NP_encJ g⁻¹))
    (hgp' : ∀ g ∈ gens, (burnsideJ4NP_encJ g, burnsideJ4NP_encJ g⁻¹) ∈ gp)
    {y : J} (hy : y ∈ Hj) {n : ℕ}
    (hy0 : (bfsFrom gp conjP (burnsideJ4NP_encJ y) n).contains (burnsideJ4NP_encJ y) = true)
    (hcl : closedUnder gp conjP (bfsFrom gp conjP (burnsideJ4NP_encJ y) n) = true) :
    Nat.card (Subgroup.closure {g | g ∈ gens}) =
      (bfsFrom gp conjP (burnsideJ4NP_encJ y) n).size *
        Nat.card ↥(Subgroup.closure {g | g ∈ gens} ⊓ Subgroup.centralizer {y}) := by
  set K := Subgroup.closure {g | g ∈ gens}
  set O := bfsFrom gp conjP (burnsideJ4NP_encJ y) n
  have hle : K ≤ Hj := (Subgroup.closure_le Hj).mpr hgH
  have hc := burnsideJ4NP_closedUnder_spec _ _ hcl
  have hsound : ∀ r ∈ O, ∃ k ∈ K, burnsideJ4NP_encJ (k * y * k⁻¹) = r := by
    refine burnsideJ4NP_bfsFrom_sound _ _ _ ?_ _ ⟨1, K.one_mem, by rw [one_mul, inv_one, mul_one]⟩ n
    rintro r ⟨k, hk, rfl⟩ p hp
    obtain ⟨g, hg, rfl⟩ := hgp p hp
    refine ⟨g * k, K.mul_mem (Subgroup.subset_closure hg) hk, ?_⟩
    have hkH := hle hk
    have hgH' := hgH g hg
    have e : g * k * y * (g * k)⁻¹ = g * (k * y * k⁻¹) * g⁻¹ := by group
    rw [e, burnsideJ4NP_encJ_mul₃ hgH' (Hj.mul_mem (Hj.mul_mem hkH hy) (Hj.inv_mem hkH))
      (Hj.inv_mem hgH')]
    simp only [conjP]
  rw [burnsideJ4NP_card_eq_orbit_mul_centralizer_enc (K := K) rfl y burnsideJ4NP_encJ
    (fun k hk k' hk' e => burnsideJ4NP_encJ_inj
      (Hj.mul_mem (Hj.mul_mem (hle hk) hy) (Hj.inv_mem (hle hk)))
      (Hj.mul_mem (Hj.mul_mem (hle hk') hy) (Hj.inv_mem (hle hk'))) e)
    O.toList.toFinset
    (by rw [List.mem_toFinset, Std.HashSet.mem_toList]; exact Std.HashSet.contains_iff_mem.mp hy0)
    (fun k hk hmem g hg => by
      rw [List.mem_toFinset, Std.HashSet.mem_toList] at hmem ⊢
      have hkH := hle hk
      have hgH' := hgH g hg
      rw [burnsideJ4NP_encJ_mul₃ hgH' (Hj.mul_mem (Hj.mul_mem hkH hy) (Hj.inv_mem hkH))
        (Hj.inv_mem hgH')]
      have := hc _ hmem _ (hgp' g hg)
      simp only [conjP] at this
      exact this)
    (fun r hr => by
      rw [List.mem_toFinset, Std.HashSet.mem_toList] at hr
      exact hsound r hr),
    List.toFinset_card_of_nodup (burnsideJ4NP_hashSet_nodup O), Std.HashSet.length_toList]

end Enc

theorem burnsideJ4NP_closure_elemAb {G : Type*} [Group G] {s : Set G}
    (hc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) (hs : ∀ a ∈ s, a * a = 1) :
    (∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x) ∧
      ∀ x ∈ Subgroup.closure s, x * x = 1 := by
  have hcomm : ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x := by
    have hle : Subgroup.closure s ≤ Subgroup.centralizer s :=
      (Subgroup.closure_le _).mpr fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
        (hc a ha b hb).symm
    intro x hx y hy
    have hx' : x ∈ Subgroup.centralizer (Subgroup.closure s : Set G) := by
      rw [Subgroup.centralizer_closure]
      exact hle hx
    exact (Subgroup.mem_centralizer_iff.mp hx' y hy).symm
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem a ha => exact hs a ha
  | one => simp
  | mul a b ha hb iha ihb =>
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hcomm b hb a ha]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha =>
    calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
      _ = 1 := by rw [iha, inv_one]

end CFSG.ASVolI

module

public import CFSG.Quasithin.Background.SmithB45MatIndDefs
public import CFSG.CharacterTheory.SteinbergBYNortonCriterion

public section

namespace CFSG.Quasithin.B45Mat.Ind

open CFSG.QuasithinUnique.Setup.X3E CFSG.Quasithin.H.Mathieu CFSG.CharacterTheory.SteinbergBY

theorem getD_map_range {α : Type*} (f : ℕ → α) (d : α) {n k : ℕ} (hk : k < n) :
    ((List.range n).map f).getD k d = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

theorem lin_eq_of_toVec {N : ℕ} {cols : List ℕ} {f : Vec N →ₗ[ZMod 2] Vec N}
    (h : ∀ k : Fin N, toVec N (cols.getD k.val 0) = f (Pi.single k 1)) : lin N cols = f :=
  linearMap_ext_basis fun k => by rw [lin_single, h k]

theorem lin_eq_id {N : ℕ} {cols : List ℕ} (h : ∀ j < N, cols.getD j 0 = 1 <<< j) :
    lin N cols = LinearMap.id :=
  lin_eq_of_toVec fun k => by rw [h k.val k.isLt, toVec_one_shiftLeft N k.val k.isLt]; rfl

theorem lin_comp_lin {N : ℕ} {A B C : List ℕ}
    (h : ∀ j < N, papply N A (B.getD j 0) = C.getD j 0) : lin N A ∘ₗ lin N B = lin N C :=
  (lin_eq_of_toVec fun k => by
    rw [LinearMap.comp_apply, lin_single, ← toVec_papply, h k.val k.isLt]).symm

theorem lin_inv_of_baseOK {N : ℕ} {P Pi : List ℕ} (h : baseOK N P Pi = true) :
    lin N Pi ∘ₗ lin N P = LinearMap.id ∧ lin N P ∘ₗ lin N Pi = LinearMap.id := by
  simp only [baseOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine ⟨?_, ?_⟩
  · rw [lin_comp_lin (C := (List.range N).map fun j => 1 <<< j) fun j hj => by
      rw [h.1 j hj, getD_map_range _ _ hj]]
    exact lin_eq_id fun j hj => getD_map_range _ _ hj
  · rw [lin_comp_lin (C := (List.range N).map fun j => 1 <<< j) fun j hj => by
      rw [h.2 j hj, getD_map_range _ _ hj]]
    exact lin_eq_id fun j hj => getD_map_range _ _ hj

theorem lin_conjCols (N : ℕ) (Pi K P : List ℕ) :
    lin N (conjCols N Pi K P) = lin N Pi ∘ₗ lin N K ∘ₗ lin N P :=
  lin_eq_of_toVec fun k => by
    rw [conjCols, getD_map_range _ _ k.isLt, toVec_papply, toVec_papply, LinearMap.comp_apply,
      LinearMap.comp_apply, lin_single]

theorem nsOK_facts {N : ℕ} {ns : List ℕ} (h : nsOK N ns = true) :
    2 ≤ ns.length ∧ ns.getD 0 0 = 0 ∧ ns.getD (ns.length - 1) 0 = N ∧
      ∀ i < ns.length - 1, ns.getD i 0 < ns.getD (i + 1) 0 := by
  simp only [nsOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem flagSide_facts {ns : List ℕ} {blk : ℕ → List ℕ} {M : List ℕ}
    (h : flagSide ns blk M = true) :
    (∀ i < ns.length, ∀ j < ns.getD i 0, M.getD j 0 < 2 ^ ns.getD i 0) ∧
      ∀ i < ns.length - 1, blkCols M (ns.getD i 0) (ns.getD (i + 1) 0 - ns.getD i 0) = blk i := by
  simp only [flagSide, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at h
  exact h

theorem exists_iso_of_flagOK {N : ℕ} {K : Bool → List ℕ} {P : List ℕ} {ns : List ℕ}
    {blk : ℕ → Bool → List ℕ} (h : flagOK N K P ns blk = true)
    (hirr : ∀ i < ns.length - 1,
      IrredPair fun z => lin (ns.getD (i + 1) 0 - ns.getD i 0) (blk i z))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (gW : Bool → (W →ₗ[ZMod 2] W))
    (hW : IrredPair gW) (hWne : (⊤ : Submodule (ZMod 2) W) ≠ ⊥) (φ : Vec N →ₗ[ZMod 2] W)
    (hφ : Function.Surjective φ) (hφeq : ∀ z v, φ (lin N (K z) v) = gW z (φ v)) :
    ∃ i < ns.length - 1, ∃ Ψ : Vec (ns.getD (i + 1) 0 - ns.getD i 0) ≃ₗ[ZMod 2] W,
      ∀ z s, Ψ (lin _ (blk i z) s) = gW z (Ψ s) := by
  unfold flagOK flagCore at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hbase, hns⟩, hf0⟩, hf1⟩ := h
  obtain ⟨hPiP, hPPi⟩ := lin_inv_of_baseOK hbase
  obtain ⟨hlen, h0, hN, hmono⟩ := nsOK_facts hns
  set Pi := invCols N P
  set M : Bool → List ℕ := fun z => conjCols N Pi (K z) P with hMdef
  have hside : ∀ z, flagSide ns (fun i => blk i z) (M z) = true := by
    intro z
    cases z
    · exact hf0
    · exact hf1
  have hinv : ∀ i ≤ ns.length - 1, ∀ z, ∀ v ∈ Fl N (ns.getD i 0),
      lin N (M z) v ∈ Fl N (ns.getD i 0) := fun i hi z v hv =>
    lin_mem_Fl (fun j hj => (flagSide_facts (hside z)).1 i (by omega) j hj) hv
  have hle : ∀ i < ns.length - 1, ns.getD i 0 + (ns.getD (i + 1) 0 - ns.getD i 0) ≤ N := by
    intro i hi
    have h1 : ns.getD (i + 1) 0 ≤ ns.getD (ns.length - 1) 0 :=
      ns_mono (ns := fun i => ns.getD i 0) hmono (i + 1) (ns.length - 1) (by omega) le_rfl
    have h2 := hmono i hi
    omega
  have hblk : ∀ i < ns.length - 1, ∀ z,
      blockMap N (ns.getD i 0) (ns.getD (i + 1) 0 - ns.getD i 0) (lin N (M z)) =
        lin (ns.getD (i + 1) 0 - ns.getD i 0) (blk i z) := by
    intro i hi z
    rw [blockMap_lin (hle i hi), (flagSide_facts (hside z)).2 i hi]
  have hφ' : Function.Surjective (φ ∘ₗ lin N P) := by
    intro w
    obtain ⟨v, rfl⟩ := hφ w
    refine ⟨lin N Pi v, ?_⟩
    rw [LinearMap.comp_apply, ← LinearMap.comp_apply (lin N P), hPPi, LinearMap.id_apply]
  have heq : ∀ z v, (φ ∘ₗ lin N P) (lin N (M z) v) = gW z ((φ ∘ₗ lin N P) v) := by
    intro z v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, lin_conjCols, ← hφeq]
    congr 1
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← LinearMap.comp_apply (lin N P), hPPi,
      LinearMap.id_apply]
  obtain ⟨i, hi, Ψ, hΨ⟩ := chain_jh (fun i => ns.getD i 0) (ns.length - 1) h0 hN hmono
    (fun z => lin N (M z)) hinv (fun i hi => by simpa only [hblk i hi] using hirr i hi) gW hW
    hWne (φ ∘ₗ lin N P) hφ' heq
  refine ⟨i, hi, Ψ, fun z s => ?_⟩
  rw [← hblk i hi z]
  exact hΨ z s

theorem ofBits_congr {d : ℕ} {f g : ℕ → Bool} (h : ∀ i < d, f i = g i) :
    ofBits d f = ofBits d g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [ofBits_testBit, ofBits_testBit]
  by_cases hi : i < d
  · rw [h i hi]
  · simp [hi]

theorem nortonOK_of_fast {d : ℕ} {cols : Bool → List ℕ} {aW : List (List Bool)}
    {kers : List (ℕ × List (List Bool) × List ℕ)} {psi : ℕ} {dw : List (List Bool)}
    {rCols minv : List ℕ} (h : nortonFastOK d cols aW kers psi dw rCols minv = true) :
    nortonOK d cols aW kers psi dw rCols minv = true := by
  have hmk : ∀ k,
      (ofBits d fun l => (((List.range d).map (rowAt d cols psi dw)).getD l 0).testBit k) =
        mkAt d cols psi dw k := fun k => ofBits_congr fun l hl => by
    rw [getD_map_range _ _ hl]
  unfold nortonFastOK nortonCore at h
  simp only [hmk] at h
  exact h

theorem irredPair_of_nortonFastOK {d : ℕ} {cols : Bool → List ℕ} {aW : List (List Bool)}
    {kers : List (ℕ × List (List Bool) × List ℕ)} {psi : ℕ} {dw : List (List Bool)}
    {rCols minv : List ℕ} (h : nortonFastOK d cols aW kers psi dw rCols minv = true) :
    IrredPair fun b => lin d (cols b) :=
  nortonOK_sound (nortonOK_of_fast h)

theorem irredPair_one (g : Bool → (Vec 1 →ₗ[ZMod 2] Vec 1)) : IrredPair g := by
  intro U _
  by_cases hU : U = ⊥
  · exact Or.inl hU
  · right
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    refine eq_top_of_basis_mem fun k => ?_
    have hk : k = 0 := Subsingleton.elim _ _
    have hu : u = Pi.single 0 1 := by
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      have h1 : u 0 ≠ 0 := fun h => hu0 (funext fun j => by rw [Subsingleton.elim j 0, h]; rfl)
      have h2 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
      rw [Pi.single_eq_same, h2 _ h1]
    rw [hk, ← hu]
    exact huU

@[expose] noncomputable def pmap (d : ℕ) (cols : Bool → List ℕ) (p : List (List Bool)) :
    Vec d →ₗ[ZMod 2] Vec d :=
  (p.map (wmap fun b => lin d (cols b))).sum

theorem toVec_pApply (d : ℕ) (cols : Bool → List ℕ) (p : List (List Bool)) (v : ℕ) :
    toVec d (pApply d cols p v) = pmap d cols p (toVec d v) := by
  unfold pApply pmap
  suffices h : ∀ (acc : ℕ) (q : List (List Bool)),
      toVec d (q.foldl (fun acc w => acc ^^^ wapp d cols w v) acc) =
        toVec d acc + (q.map (wmap fun b => lin d (cols b))).sum (toVec d v) by
    rw [h 0 p, toVec_zero, zero_add]
  intro acc q
  induction q generalizing acc with
  | nil => simp
  | cons w q ih =>
    rw [List.foldl_cons, ih, toVec_xor, toVec_wapp, List.map_cons, List.sum_cons,
      LinearMap.add_apply, add_assoc]

theorem pmap_intertwine {d : ℕ} {A B : Bool → List ℕ} (S : Vec d →ₗ[ZMod 2] Vec d)
    (hS : ∀ z v, S (lin d (A z) v) = lin d (B z) (S v)) (p : List (List Bool)) (v : Vec d) :
    S (pmap d A p v) = pmap d B p (S v) := by
  unfold pmap
  induction p with
  | nil => simp
  | cons w p ih =>
    rw [List.map_cons, List.sum_cons, LinearMap.add_apply, map_add, ih, List.map_cons,
      List.sum_cons, LinearMap.add_apply, wmap_intertwine _ _ S hS w v]

theorem eq_zero_of_homZeroOK {d : ℕ} {A B : Bool → List ℕ} {u : ℕ} {gw : List (List Bool)}
    {masks : List ℕ} {p₁ p₂ : List (List Bool)} {L₁ L₂ : List ℕ}
    (h : homZeroOK d A B u gw masks p₁ p₂ L₁ L₂ = true) (S : Vec d →ₗ[ZMod 2] Vec d)
    (hS : ∀ z v, S (lin d (A z) v) = lin d (B z) (S v)) : S = 0 := by
  simp only [homZeroOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h₁, h₂⟩, hspin⟩, hL⟩ := h
  have hp₁ : pmap d B p₁ (S (toVec d u)) = 0 := by
    rw [← pmap_intertwine S hS, ← toVec_pApply, h₁, toVec_zero, map_zero]
  have hp₂ : pmap d B p₂ (S (toVec d u)) = 0 := by
    rw [← pmap_intertwine S hS, ← toVec_pApply, h₂, toVec_zero, map_zero]
  have hid : lin d L₁ ∘ₗ pmap d B p₁ + lin d L₂ ∘ₗ pmap d B p₂ = LinearMap.id := by
    refine linearMap_ext_basis fun k => ?_
    have h1 := congrArg (toVec d) (hL k.val k.isLt)
    rw [toVec_xor, toVec_papply, toVec_papply, toVec_pApply, toVec_pApply,
      toVec_one_shiftLeft d k.val k.isLt] at h1
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.id_apply]
    exact h1
  have hSu : S (toVec d u) = 0 := by
    have h1 := LinearMap.congr_fun hid (S (toVec d u))
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hp₁, hp₂, map_zero,
      map_zero, add_zero, LinearMap.id_apply] at h1
    exact h1.symm
  refine linearMap_ext_basis fun k => ?_
  have h1 := congrArg (toVec d) (hspin k.val k.isLt)
  rw [toVec_xorSelW, toVec_one_shiftLeft d k.val k.isLt] at h1
  rw [← h1, map_sum, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  split_ifs
  · rw [wmap_intertwine _ _ S hS, hSu, map_zero]
  · exact map_zero S

theorem lin_packCols {n : ℕ} (t : Vector (Vector (ZMod 2) n) n) :
    lin n (packCols t) = Matrix.toLin' (untab t) :=
  lin_eq_of_toVec fun k => by
    funext i
    have h1 : (packCols t).getD k.val 0 =
        ofBits n fun i => if h : i < n then t[i][k] == 1 else false := by
      simp [packCols]
    rw [h1, toVec_ofBits]
    simp only [i.isLt, ↓reduceDIte, Matrix.toLin'_apply, Matrix.mulVec_single_one]
    have h2 : ∀ c : ZMod 2, (if (c == 1) = true then (1 : ZMod 2) else 0) = c := by decide
    exact h2 _

end CFSG.Quasithin.B45Mat.Ind

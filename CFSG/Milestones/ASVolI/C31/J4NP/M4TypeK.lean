module

public import CFSG.Milestones.ASVolI.C31.J4NP.M4TypeGen
public import CFSG.Milestones.ASVolI.C31.J4NP.TreeBFS
public import Certificates.Certificate7951
public import Certificates.Certificate7952

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
open CFSG.J4Tree.Native CFSG.J4Tree.Native.Node CFSG.J4Tree.M4

@[expose] noncomputable def burnsideJ4NP_m4K : Subgroup J := burnsideJ4NP_coordSub kGens

@[expose] noncomputable def burnsideJ4NP_m4F : Subgroup J := burnsideJ4NP_coordSub fBasis

@[expose] noncomputable def burnsideJ4NP_m4Y136 : Subgroup J := burnsideJ4NP_coordSub y136

@[expose] noncomputable def burnsideJ4NP_m4Y266 : Subgroup J := burnsideJ4NP_coordSub y266

theorem burnsideJ4NP_m4_coordsOK {L : List (ℕ × ℕ)} (h : coordsOK L = true) :
    ∀ ce ∈ L, ce.2 < 1024 := by
  simpa [coordsOK] using h

theorem burnsideJ4NP_m4_mem_centralizer_closure {S : Set J} {x : J}
    (h : ∀ s ∈ S, s * x = x * s) : x ∈ Subgroup.centralizer ((Subgroup.closure S : Subgroup J) :
      Set J) := by
  have hle : Subgroup.closure S ≤ Subgroup.centralizer {x} :=
    (Subgroup.closure_le _).mpr fun s hs => by
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact h s hs
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have := hle hs
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

section Codes

theorem burnsideJ4NP_m4_treeElt_mem_Hj {L : List (ℕ × ℕ)} (h : coordsOK L = true) :
    ∀ g ∈ L.map burnsideJ4NP_treeElt, g ∈ Hj := by
  intro g hg
  obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hg
  exact burnsideJ4NP_treeElt_mem (burnsideJ4NP_m4_coordsOK h ce hce)

theorem burnsideJ4NP_m4_coordSub_le_Hj {L : List (ℕ × ℕ)} (h : coordsOK L = true) :
    burnsideJ4NP_coordSub L ≤ Hj :=
  (Subgroup.closure_le Hj).mpr fun g hg => burnsideJ4NP_m4_treeElt_mem_Hj h g hg

theorem burnsideJ4NP_m4_closureOf_eq {L : List (ℕ × ℕ)} (h : coordsOK L = true) :
    closureOf (L.map cc) =
      bfsFrom ((L.map burnsideJ4NP_treeElt).map burnsideJ4NP_encJ) rmul 1 rounds := by
  rw [burnsideJ4NP_map_encJ_treeElt (burnsideJ4NP_m4_coordsOK h)]
  rfl

theorem burnsideJ4NP_m4_mem_coordSub_iff {L : List (ℕ × ℕ)} (h : coordsOK L = true)
    (hS : subOK (L.map cc) (closureOf (L.map cc)) = true) {x : J} (hx : x ∈ Hj) :
    x ∈ burnsideJ4NP_coordSub L ↔ (closureOf (L.map cc)).contains (burnsideJ4NP_encJ x) = true := by
  have hgH := burnsideJ4NP_m4_treeElt_mem_Hj h
  unfold subOK at hS
  rw [Bool.and_eq_true] at hS
  rw [burnsideJ4NP_m4_closureOf_eq h] at hS ⊢
  rw [burnsideJ4NP_map_encJ_treeElt (burnsideJ4NP_m4_coordsOK h)] at hS
  have key := burnsideJ4NP_mem_closure_iff_bfs (n := rounds) hgH
    (by rw [burnsideJ4NP_map_encJ_treeElt (burnsideJ4NP_m4_coordsOK h)]; exact hS.1)
    (by rw [burnsideJ4NP_map_encJ_treeElt (burnsideJ4NP_m4_coordsOK h)]; exact hS.2) hx
  rw [burnsideJ4NP_coordSub, key, Std.HashSet.contains_iff_mem]

theorem burnsideJ4NP_m4_card_coordSub {L : List (ℕ × ℕ)} (h : coordsOK L = true)
    (hS : subOK (L.map cc) (closureOf (L.map cc)) = true) :
    Nat.card ↥(burnsideJ4NP_coordSub L) = (closureOf (L.map cc)).size := by
  have hgH := burnsideJ4NP_m4_treeElt_mem_Hj h
  unfold subOK at hS
  rw [Bool.and_eq_true] at hS
  rw [burnsideJ4NP_m4_closureOf_eq h] at hS ⊢
  exact burnsideJ4NP_card_closure_bfs (n := rounds) hgH
    (by rw [burnsideJ4NP_map_encJ_treeElt (burnsideJ4NP_m4_coordsOK h)] at hS ⊢; exact hS.1)
    (by rw [burnsideJ4NP_map_encJ_treeElt (burnsideJ4NP_m4_coordsOK h)] at hS ⊢; exact hS.2)

theorem burnsideJ4NP_m4_encJ_treeElt {L : List (ℕ × ℕ)} (h : coordsOK L = true) {ce : ℕ × ℕ}
    (hce : ce ∈ L) : burnsideJ4NP_encJ (burnsideJ4NP_treeElt ce) = cc ce :=
  burnsideJ4NP_encJ_treeElt (burnsideJ4NP_m4_coordsOK h ce hce)

theorem burnsideJ4NP_m4_mem_centralizer_coordSub {L : List (ℕ × ℕ)} (h : coordsOK L = true)
    {x : J} (hx : x ∈ Hj)
    (hc : (L.map cc).all (fun y => burnsideJ4NP_encJ x * y == y * burnsideJ4NP_encJ x) = true) :
    x ∈ Subgroup.centralizer (burnsideJ4NP_coordSub L : Set J) := by
  apply burnsideJ4NP_m4_mem_centralizer_closure
  intro s hs
  obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hs
  have hsH := burnsideJ4NP_treeElt_mem (burnsideJ4NP_m4_coordsOK h ce hce)
  rw [List.all_eq_true] at hc
  have := hc (cc ce) (List.mem_map_of_mem hce)
  rw [beq_iff_eq, ← burnsideJ4NP_m4_encJ_treeElt h hce] at this
  exact ((burnsideJ4NP_commute_iff_code hx hsH).mpr this).symm

theorem burnsideJ4NP_m4_not_mem_centralizer_coordSub {L : List (ℕ × ℕ)} (h : coordsOK L = true)
    {x : J} (hx : x ∈ Hj)
    (hc : (L.map cc).any (fun y => burnsideJ4NP_encJ x * y != y * burnsideJ4NP_encJ x) = true) :
    x ∉ Subgroup.centralizer (burnsideJ4NP_coordSub L : Set J) := by
  intro hmem
  rw [List.any_eq_true] at hc
  obtain ⟨y, hy, hne⟩ := hc
  obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hy
  have hsH := burnsideJ4NP_treeElt_mem (burnsideJ4NP_m4_coordsOK h ce hce)
  have h1 := Subgroup.mem_centralizer_iff.mp hmem _
    (Subgroup.subset_closure (List.mem_map_of_mem hce))
  rw [← burnsideJ4NP_m4_encJ_treeElt h hce] at hne
  rw [(burnsideJ4NP_commute_iff_code hx hsH).mp h1.symm] at hne
  simp at hne

end Codes

section Checks

theorem burnsideJ4NP_m4_codeChecks_parts :
    treeOrd 539 = 16384 ∧ coordsOK kGens = true ∧ coordsOK fBasis = true ∧
      coordsOK (treeWv 539) = true ∧ coordsOK (treeBasis 539) = true ∧ coordsOK y136 = true ∧
      coordsOK y266 = true ∧ coordsOK [h136, h266] = true ∧ coordsOK (treeWv 136) = true ∧
      coordsOK (treeWv 266) = true ∧
      k539OK (closureOf (kGens.map cc)) (closureOf (fBasis.map cc))
        (closureOf ((treeWv 539).map cc)) (closureOf ((treeBasis 539).map cc)) (kGens.map cc)
        (fBasis.map cc) ((treeWv 539).map cc) ((treeBasis 539).map cc)
        (pairsOf (kGens.map cc)) (codeOfWord gWord) (codeOfWord gWord).inv = true ∧
      hOK (cc h136) (y136.map cc) ((treeWv 136).map cc) = true ∧
      hOK (cc h266) (y266.map cc) ((treeWv 266).map cc) = true ∧
      yOK y136 (treeWv 136) yin136 o136 = true ∧ yOK y266 (treeWv 266) yin266 o266 = true := by
  have h := Certificates.certificate7952
  unfold codeChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

theorem burnsideJ4NP_m4_k539_parts :
    subOK (kGens.map cc) (closureOf (kGens.map cc)) = true ∧
    subOK (fBasis.map cc) (closureOf (fBasis.map cc)) = true ∧
    subOK ((treeWv 539).map cc) (closureOf ((treeWv 539).map cc)) = true ∧
    subOK ((treeBasis 539).map cc) (closureOf ((treeBasis 539).map cc)) = true ∧
    (closureOf (kGens.map cc)).size = 16384 ∧
    ((treeBasis 539).map cc).all (closureOf ((treeWv 539).map cc)).contains = true ∧
    ((treeWv 539).map cc).all (closureOf ((treeBasis 539).map cc)).contains = true ∧
    (kGens.map cc).all (fun k => ((treeWv 539).map cc).all fun w => k * w == w * k) = true ∧
    (fBasis.map cc).all (closureOf (kGens.map cc)).contains = true ∧
    (fBasis.map cc).all (· != 1) = true ∧
    pairsOK (pairsOf (kGens.map cc)) = true ∧
    (closureOf (kGens.map cc)).toList.all
      (classOK (pairsOf (kGens.map cc)) (closureOf (fBasis.map cc))) = true ∧
    (fBasis.map cc).all (basisClassOK (pairsOf (kGens.map cc))) = true ∧
    codeOfWord gWord * (codeOfWord gWord).inv = 1 ∧ (codeOfWord gWord).inv.wf = true ∧
    (fBasis.map cc).all (fun b => (closureOf (fBasis.map cc)).contains
      (codeOfWord gWord * b * (codeOfWord gWord).inv)) = true ∧
    ((treeWv 539).map cc).any (fun w => !(closureOf ((treeWv 539).map cc)).contains
      (codeOfWord gWord * w * (codeOfWord gWord).inv)) = true ∧
    sextMasks.all (fun c => (closureOf ((treeWv 539).map cc)).contains (etaCode c)) = true := by
  have h := burnsideJ4NP_m4_codeChecks_parts.2.2.2.2.2.2.2.2.2.2.1
  unfold k539OK at h
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

theorem burnsideJ4NP_m4_hk : coordsOK kGens = true := burnsideJ4NP_m4_codeChecks_parts.2.1

theorem burnsideJ4NP_m4_hf : coordsOK fBasis = true := burnsideJ4NP_m4_codeChecks_parts.2.2.1

theorem burnsideJ4NP_m4_hw : coordsOK (treeWv 539) = true :=
  burnsideJ4NP_m4_codeChecks_parts.2.2.2.1

theorem burnsideJ4NP_m4_hr : coordsOK (treeBasis 539) = true :=
  burnsideJ4NP_m4_codeChecks_parts.2.2.2.2.1

theorem burnsideJ4NP_m4_h_parts :
    coordsOK y136 = true ∧ coordsOK y266 = true ∧ coordsOK [h136, h266] = true ∧
      coordsOK (treeWv 136) = true ∧ coordsOK (treeWv 266) = true ∧
      hOK (cc h136) (y136.map cc) ((treeWv 136).map cc) = true ∧
      hOK (cc h266) (y266.map cc) ((treeWv 266).map cc) = true := by
  obtain ⟨-, -, -, -, -, h6, h7, h8, h9, h10, -, h12, h13, -, -⟩ := burnsideJ4NP_m4_codeChecks_parts
  exact ⟨h6, h7, h8, h9, h10, h12, h13⟩

end Checks

section K539

theorem burnsideJ4NP_m4K_le_Hj : burnsideJ4NP_m4K ≤ Hj :=
  burnsideJ4NP_m4_coordSub_le_Hj burnsideJ4NP_m4_hk

theorem burnsideJ4NP_m4_card_K : Nat.card ↥burnsideJ4NP_m4K = 16384 := by
  rw [burnsideJ4NP_m4K, burnsideJ4NP_m4_card_coordSub burnsideJ4NP_m4_hk
    burnsideJ4NP_m4_k539_parts.1]
  exact burnsideJ4NP_m4_k539_parts.2.2.2.2.1

theorem burnsideJ4NP_m4_isPGroup_K : IsPGroup 2 ↥burnsideJ4NP_m4K :=
  IsPGroup.of_card (n := 14) (by rw [burnsideJ4NP_m4_card_K]; norm_num)

theorem burnsideJ4NP_m4_mem_K_iff {x : J} (hx : x ∈ Hj) :
    x ∈ burnsideJ4NP_m4K ↔ (closureOf (kGens.map cc)).contains (burnsideJ4NP_encJ x) = true :=
  burnsideJ4NP_m4_mem_coordSub_iff burnsideJ4NP_m4_hk burnsideJ4NP_m4_k539_parts.1 hx

theorem burnsideJ4NP_m4_mem_F_iff {x : J} (hx : x ∈ Hj) :
    x ∈ burnsideJ4NP_m4F ↔ (closureOf (fBasis.map cc)).contains (burnsideJ4NP_encJ x) = true :=
  burnsideJ4NP_m4_mem_coordSub_iff burnsideJ4NP_m4_hf burnsideJ4NP_m4_k539_parts.2.1 hx

theorem burnsideJ4NP_m4_mem_W_iff {x : J} (hx : x ∈ Hj) :
    x ∈ burnsideJ4NP_Wv 539 ↔
      (closureOf ((treeWv 539).map cc)).contains (burnsideJ4NP_encJ x) = true :=
  burnsideJ4NP_m4_mem_coordSub_iff burnsideJ4NP_m4_hw burnsideJ4NP_m4_k539_parts.2.2.1 hx

theorem burnsideJ4NP_m4_mem_Rep_iff {x : J} (hx : x ∈ Hj) :
    x ∈ burnsideJ4NP_Rep 539 ↔
      (closureOf ((treeBasis 539).map cc)).contains (burnsideJ4NP_encJ x) = true :=
  burnsideJ4NP_m4_mem_coordSub_iff burnsideJ4NP_m4_hr burnsideJ4NP_m4_k539_parts.2.2.2.1 hx

theorem burnsideJ4NP_m4_coordSub_le {L : List (ℕ × ℕ)} (hL : coordsOK L = true) {X : Subgroup J}
    {S : Std.HashSet Code} (hX : ∀ x ∈ Hj, x ∈ X ↔ S.contains (burnsideJ4NP_encJ x) = true)
    (h : (L.map cc).all S.contains = true) : burnsideJ4NP_coordSub L ≤ X := by
  rw [burnsideJ4NP_coordSub, Subgroup.closure_le]
  intro g hg
  obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hg
  rw [SetLike.mem_coe, hX _ (burnsideJ4NP_treeElt_mem (burnsideJ4NP_m4_coordsOK hL ce hce)),
    burnsideJ4NP_m4_encJ_treeElt hL hce]
  rw [List.all_eq_true] at h
  exact h _ (List.mem_map_of_mem hce)

theorem burnsideJ4NP_m4_Rep_eq_Wv : burnsideJ4NP_Rep 539 = burnsideJ4NP_Wv 539 :=
  le_antisymm
    (burnsideJ4NP_m4_coordSub_le burnsideJ4NP_m4_hr (fun _ hx => burnsideJ4NP_m4_mem_W_iff hx)
      burnsideJ4NP_m4_k539_parts.2.2.2.2.2.1)
    (burnsideJ4NP_m4_coordSub_le burnsideJ4NP_m4_hw (fun _ hx => burnsideJ4NP_m4_mem_Rep_iff hx)
      burnsideJ4NP_m4_k539_parts.2.2.2.2.2.2.1)

theorem burnsideJ4NP_m4_K_le_centralizer :
    burnsideJ4NP_m4K ≤ Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Wv 539 : Set J) := by
  have hc := burnsideJ4NP_m4_k539_parts.2.2.2.2.2.2.2.1
  rw [burnsideJ4NP_m4K, burnsideJ4NP_coordSub, Subgroup.closure_le]
  intro g hg
  obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hg
  have hgH := burnsideJ4NP_treeElt_mem (burnsideJ4NP_m4_coordsOK burnsideJ4NP_m4_hk ce hce)
  refine ⟨hgH, ?_⟩
  apply burnsideJ4NP_m4_mem_centralizer_coordSub burnsideJ4NP_m4_hw hgH
  rw [burnsideJ4NP_m4_encJ_treeElt burnsideJ4NP_m4_hk hce]
  rw [List.all_eq_true] at hc
  exact hc _ (List.mem_map_of_mem hce)

theorem burnsideJ4NP_m4_centralizerH_W539
    (h539 : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep 539 : Set J)) = treeOrd 539) :
    Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Wv 539 : Set J) = burnsideJ4NP_m4K := by
  refine (Subgroup.eq_of_le_of_card_ge burnsideJ4NP_m4_K_le_centralizer ?_).symm
  rw [← burnsideJ4NP_m4_Rep_eq_Wv, h539, burnsideJ4NP_m4_codeChecks_parts.1,
    burnsideJ4NP_m4_card_K]

theorem burnsideJ4NP_m4_pairs_spec :
    (∀ p ∈ pairsOf (kGens.map cc), ∃ g ∈ kGens.map burnsideJ4NP_treeElt,
      p = (burnsideJ4NP_encJ g, burnsideJ4NP_encJ g⁻¹)) ∧
    ∀ g ∈ kGens.map burnsideJ4NP_treeElt,
      (burnsideJ4NP_encJ g, burnsideJ4NP_encJ g⁻¹) ∈ pairsOf (kGens.map cc) := by
  have hp := burnsideJ4NP_m4_k539_parts.2.2.2.2.2.2.2.2.2.2.1
  unfold CFSG.J4Tree.M4.pairsOK at hp
  rw [List.all_eq_true] at hp
  have key : ∀ ce ∈ kGens, burnsideJ4NP_encJ (burnsideJ4NP_treeElt ce)⁻¹ = (cc ce).inv := by
    intro ce hce
    have h1 := hp (cc ce, (cc ce).inv) (by
      unfold pairsOf
      exact List.mem_map.mpr ⟨cc ce, List.mem_map_of_mem hce, rfl⟩)
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    have hgH := burnsideJ4NP_treeElt_mem (burnsideJ4NP_m4_coordsOK burnsideJ4NP_m4_hk ce hce)
    refine burnsideJ4NP_encJ_inv hgH ?_ h1.2
    rw [burnsideJ4NP_m4_encJ_treeElt burnsideJ4NP_m4_hk hce]
    exact h1.1
  refine ⟨fun p hp' => ?_, fun g hg => ?_⟩
  · unfold pairsOf at hp'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp'
    obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp ha
    refine ⟨burnsideJ4NP_treeElt ce, List.mem_map_of_mem hce, ?_⟩
    rw [burnsideJ4NP_m4_encJ_treeElt burnsideJ4NP_m4_hk hce, key ce hce]
  · obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hg
    rw [burnsideJ4NP_m4_encJ_treeElt burnsideJ4NP_m4_hk hce, key ce hce]
    unfold pairsOf
    exact List.mem_map.mpr ⟨cc ce, List.mem_map_of_mem hce, rfl⟩

theorem burnsideJ4NP_m4_card_orbit {x : J} (hx : x ∈ Hj)
    (h : orbOK (pairsOf (kGens.map cc)) (burnsideJ4NP_encJ x)
      (orbitOf (pairsOf (kGens.map cc)) (burnsideJ4NP_encJ x)) = true) :
    16384 = (orbitOf (pairsOf (kGens.map cc)) (burnsideJ4NP_encJ x)).size *
      Nat.card ↥(burnsideJ4NP_m4K ⊓ Subgroup.centralizer {x}) := by
  unfold orbOK at h
  rw [Bool.and_eq_true] at h
  rw [← burnsideJ4NP_m4_card_K]
  exact burnsideJ4NP_card_orbit_bfs (gens := kGens.map burnsideJ4NP_treeElt)
    (burnsideJ4NP_m4_treeElt_mem_Hj burnsideJ4NP_m4_hk) burnsideJ4NP_m4_pairs_spec.1
    burnsideJ4NP_m4_pairs_spec.2 hx (n := rounds) h.1 h.2

theorem burnsideJ4NP_m4_closure_classSet :
    Subgroup.closure (burnsideJ4NP_classSet burnsideJ4NP_m4K 4096) = burnsideJ4NP_m4F := by
  have hcls := burnsideJ4NP_m4_k539_parts.2.2.2.2.2.2.2.2.2.2.2.1
  have hbas := burnsideJ4NP_m4_k539_parts.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFK := burnsideJ4NP_m4_k539_parts.2.2.2.2.2.2.2.2.1
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro t ⟨htK, ht2, htc⟩
    have htH := burnsideJ4NP_m4K_le_Hj htK
    have hmem := (burnsideJ4NP_m4_mem_K_iff htH).mp htK
    rw [List.all_eq_true] at hcls
    have h1 := hcls _ (Std.HashSet.mem_toList.mpr (Std.HashSet.contains_iff_mem.mp hmem))
    unfold classOK at h1
    have hsq : burnsideJ4NP_encJ t * burnsideJ4NP_encJ t = 1 :=
      (burnsideJ4NP_sq_iff_code htH).mp ht2
    rw [hsq] at h1
    simp only [bne_self_eq_false, Bool.false_or] at h1
    unfold classCore at h1
    rw [Bool.and_eq_true] at h1
    have h2 := burnsideJ4NP_m4_card_orbit htH h1.1
    rw [htc] at h2
    have h4 : (orbitOf (pairsOf (kGens.map cc)) (burnsideJ4NP_encJ t)).size = 4 := by omega
    rw [h4] at h1
    simp only [bne_self_eq_false, Bool.false_or] at h1
    exact (burnsideJ4NP_m4_mem_F_iff htH).mpr h1.2
  · rw [burnsideJ4NP_m4F, burnsideJ4NP_coordSub, Subgroup.closure_le]
    intro b hb
    obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hb
    have hbH := burnsideJ4NP_treeElt_mem (burnsideJ4NP_m4_coordsOK burnsideJ4NP_m4_hf ce hce)
    rw [List.all_eq_true] at hbas hFK
    have h1 := hbas _ (List.mem_map_of_mem hce)
    have h2 := hFK _ (List.mem_map_of_mem hce)
    rw [← burnsideJ4NP_m4_encJ_treeElt burnsideJ4NP_m4_hf hce] at h1 h2
    unfold basisClassOK basisCore at h1
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨hsq, horb, hsize⟩ := h1
    refine Subgroup.subset_closure ⟨(burnsideJ4NP_m4_mem_K_iff hbH).mpr h2,
      (burnsideJ4NP_sq_iff_code hbH).mpr hsq, ?_⟩
    have h3 := burnsideJ4NP_m4_card_orbit hbH horb
    rw [hsize] at h3
    omega

theorem burnsideJ4NP_m4_normalizer_K_le :
    Subgroup.normalizer (burnsideJ4NP_m4K : Set J) ≤
      Subgroup.normalizer (burnsideJ4NP_m4F : Set J) := by
  rw [← burnsideJ4NP_m4_closure_classSet]
  exact burnsideJ4NP_normalizer_le_normalizer_classSet _ _

theorem burnsideJ4NP_m4_F_le_K : burnsideJ4NP_m4F ≤ burnsideJ4NP_m4K :=
  burnsideJ4NP_m4_coordSub_le burnsideJ4NP_m4_hf (fun _ hx => burnsideJ4NP_m4_mem_K_iff hx)
    burnsideJ4NP_m4_k539_parts.2.2.2.2.2.2.2.2.1

theorem burnsideJ4NP_m4_F_isPGroup_ne_bot :
    IsPGroup 2 ↥burnsideJ4NP_m4F ∧ burnsideJ4NP_m4F ≠ ⊥ := by
  refine ⟨burnsideJ4NP_m4_isPGroup_K.to_le burnsideJ4NP_m4_F_le_K, fun hbot => ?_⟩
  have hne := burnsideJ4NP_m4_k539_parts.2.2.2.2.2.2.2.2.2.1
  rw [List.all_eq_true] at hne
  have hce : (1834, 608) ∈ fBasis := by simp [fBasis]
  have h1 := hne _ (List.mem_map_of_mem hce)
  have hbH := burnsideJ4NP_treeElt_mem (burnsideJ4NP_m4_coordsOK burnsideJ4NP_m4_hf _ hce)
  have hmem : burnsideJ4NP_treeElt (1834, 608) ∈ burnsideJ4NP_m4F :=
    Subgroup.subset_closure (List.mem_map_of_mem hce)
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [← burnsideJ4NP_m4_encJ_treeElt burnsideJ4NP_m4_hf hce, hmem, burnsideJ4NP_encJ_one] at h1
  simp at h1

@[expose] noncomputable def burnsideJ4NP_m4g : J := wordProd xJ gWord

theorem burnsideJ4NP_m4g_mem : burnsideJ4NP_m4g ∈ Hj := wordProd_mem_Hj (by decide)

theorem burnsideJ4NP_m4_encJ_g : burnsideJ4NP_encJ burnsideJ4NP_m4g = codeOfWord gWord := by
  rw [burnsideJ4NP_encJ_of_mem burnsideJ4NP_m4g_mem]
  exact burnsideJ4NP_enc_wordProd (by decide)

theorem burnsideJ4NP_m4_encJ_g_inv :
    burnsideJ4NP_encJ burnsideJ4NP_m4g⁻¹ = (codeOfWord gWord).inv := by
  refine burnsideJ4NP_encJ_inv burnsideJ4NP_m4g_mem ?_
    burnsideJ4NP_m4_k539_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [burnsideJ4NP_m4_encJ_g]
  exact burnsideJ4NP_m4_k539_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem burnsideJ4NP_m4_encJ_conj_g {x : J} (hx : x ∈ Hj) :
    burnsideJ4NP_encJ (burnsideJ4NP_m4g * x * burnsideJ4NP_m4g⁻¹) =
      codeOfWord gWord * burnsideJ4NP_encJ x * (codeOfWord gWord).inv := by
  rw [burnsideJ4NP_encJ_mul₃ burnsideJ4NP_m4g_mem hx (Hj.inv_mem burnsideJ4NP_m4g_mem),
    burnsideJ4NP_m4_encJ_g, burnsideJ4NP_m4_encJ_g_inv]

theorem burnsideJ4NP_m4_g_mem_normalizer_F :
    burnsideJ4NP_m4g ∈ Subgroup.normalizer (burnsideJ4NP_m4F : Set J) := by
  have hg := burnsideJ4NP_m4_k539_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [List.all_eq_true] at hg
  apply burnsideJ4NP_mem_normalizer_closure
  intro b hb
  obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hb
  have hbH := burnsideJ4NP_treeElt_mem (burnsideJ4NP_m4_coordsOK burnsideJ4NP_m4_hf ce hce)
  have hgbH : burnsideJ4NP_m4g * burnsideJ4NP_treeElt ce * burnsideJ4NP_m4g⁻¹ ∈ Hj :=
    Hj.mul_mem (Hj.mul_mem burnsideJ4NP_m4g_mem hbH) (Hj.inv_mem burnsideJ4NP_m4g_mem)
  show _ ∈ burnsideJ4NP_m4F
  rw [burnsideJ4NP_m4_mem_F_iff hgbH, burnsideJ4NP_m4_encJ_conj_g hbH,
    burnsideJ4NP_m4_encJ_treeElt burnsideJ4NP_m4_hf hce]
  exact hg _ (List.mem_map_of_mem hce)

theorem burnsideJ4NP_m4_g_not_mem_normalizer_W :
    burnsideJ4NP_m4g ∉ Subgroup.normalizer (burnsideJ4NP_Wv 539 : Set J) := by
  intro hN
  have hg := burnsideJ4NP_m4_k539_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [List.any_eq_true] at hg
  obtain ⟨w, hw, hnot⟩ := hg
  obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hw
  have hwH := burnsideJ4NP_treeElt_mem (burnsideJ4NP_m4_coordsOK burnsideJ4NP_m4_hw ce hce)
  have hwW : burnsideJ4NP_treeElt ce ∈ burnsideJ4NP_Wv 539 :=
    Subgroup.subset_closure (List.mem_map_of_mem hce)
  have h1 := (Subgroup.mem_normalizer_iff.mp hN _).mp hwW
  have hgwH : burnsideJ4NP_m4g * burnsideJ4NP_treeElt ce * burnsideJ4NP_m4g⁻¹ ∈ Hj :=
    Hj.mul_mem (Hj.mul_mem burnsideJ4NP_m4g_mem hwH) (Hj.inv_mem burnsideJ4NP_m4g_mem)
  rw [burnsideJ4NP_m4_mem_W_iff hgwH, burnsideJ4NP_m4_encJ_conj_g hwH,
    burnsideJ4NP_m4_encJ_treeElt burnsideJ4NP_m4_hw hce] at h1
  rw [h1] at hnot
  simp at hnot

end K539

section Pts

theorem burnsideJ4NP_m4_pt77 : ∀ i, 0 < i → i < 77 → ∃ c ∈ sextMasks,
    (CFSG.Quasithin.J4M2.ptElt i)⁻¹ * eta uJ 11 c * CFSG.Quasithin.J4M2.ptElt i ∉ Eg uJ 11 :=
  Certificates.certificate7951

theorem burnsideJ4NP_m4_eta_mem_W {c : ℕ} (hc : c ∈ sextMasks) :
    eta uJ 11 c ∈ burnsideJ4NP_Wv 539 := by
  have h := burnsideJ4NP_m4_k539_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [List.all_eq_true] at h
  have hH : eta uJ 11 c ∈ Hj := Eg_le_Hj (eta_mem_Eg 11 le_rfl c)
  rw [burnsideJ4NP_m4_mem_W_iff hH, burnsideJ4NP_encJ_of_mem hH, burnsideJ4NP_enc_eta]
  exact h c hc

theorem burnsideJ4NP_m4_centralizer_le_Hj :
    Subgroup.centralizer (burnsideJ4NP_Wv 539 : Set J) ≤ Hj :=
  burnsideJ4NP_centralizer_le_Hj_of_pts sextMasks
    (by rw [CFSG.Quasithin.J4Loc.z0_eq]; exact burnsideJ4NP_m4_eta_mem_W (by decide))
    (fun _ hc => burnsideJ4NP_m4_eta_mem_W hc) burnsideJ4NP_m4_pt77

theorem burnsideJ4NP_m4_centralizer_W539
    (h539 : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep 539 : Set J)) = treeOrd 539) :
    Subgroup.centralizer (burnsideJ4NP_Wv 539 : Set J) = burnsideJ4NP_m4K := by
  rw [← burnsideJ4NP_m4_centralizerH_W539 h539]
  exact (inf_eq_right.mpr burnsideJ4NP_m4_centralizer_le_Hj).symm

theorem burnsideJ4NP_verdictW_m4_539
    (h539 : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep 539 : Set J)) = treeOrd 539) :
    burnsideJ4NP_VerdictW (burnsideJ4NP_Wv 539) :=
  burnsideJ4NP_verdictW_of_char (burnsideJ4NP_m4_centralizer_W539 h539)
    burnsideJ4NP_m4_isPGroup_K burnsideJ4NP_m4_normalizer_K_le
    burnsideJ4NP_m4_F_isPGroup_ne_bot.1 burnsideJ4NP_m4_F_isPGroup_ne_bot.2
    burnsideJ4NP_m4_g_mem_normalizer_F burnsideJ4NP_m4_g_not_mem_normalizer_W

end Pts

end CFSG.ASVolI

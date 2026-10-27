module

public import CFSG.Quasithin.Vol2.KGFactC31M24Cases
public import CFSG.Quasithin.Vol2.KGFactC31FrameSound

public section

namespace CFSG.Quasithin.KGC31.M24

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31 Matrix _root_.Certificates

theorem centralizer_map_conj (H : Subgroup G₀) (c : G₀) :
    Subgroup.centralizer ((H.map (MulAut.conj c).toMonoidHom : Subgroup G₀) : Set G₀) =
      (Subgroup.centralizer (H : Set G₀)).map (MulAut.conj c).toMonoidHom := by
  have h := map_centralizer_eq (MulAut.conj c).toMonoidHom (MulAut.conj c).injective H
  rw [MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective, top_inf_eq] at h
  exact h.symm

@[expose] def candOf (p : ℕ × List ℤ) : List (Equiv.Perm (Fin 24)) :=
  if p.1 = 1 then List.ofFn fun i => ((elt p.2 : G₀) : Equiv.Perm (Fin 24)) *
      ((vO i : G₀) : Equiv.Perm (Fin 24)) * ((elt p.2 : G₀) : Equiv.Perm (Fin 24))⁻¹
  else List.ofFn fun i => ((elt p.2 : G₀) : Equiv.Perm (Fin 24)) *
      ((vT i : G₀) : Equiv.Perm (Fin 24)) * ((elt p.2 : G₀) : Equiv.Perm (Fin 24))⁻¹

theorem forall₂_frameCands {fr : List (ℕ × List ℤ)}
    (hinv : ∀ p ∈ fr, invOK 24 (wordT 24 gensT p.2) (invT 24 (wordT 24 gensT p.2)) = true) :
    List.Forall₂ (List.Forall₂ (Rep 24)) (frameCands fr) (fr.map candOf) := by
  unfold frameCands
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun p hp => ?_
  have hc : Rep 24 (wordT 24 gensT p.2) ((elt p.2 : G₀) : Equiv.Perm (Fin 24)) := rep_elt _
  have hci := Rep.inv_of_invOK hc (hinv p hp)
  unfold candOf
  split_ifs
  · exact forall₂_conjTab forall₂_o hc hci
  · exact forall₂_conjTab forall₂_t hc hci

theorem map_sup_orbSub {U : Subgroup G₀} {ug : List (Equiv.Perm (Fin 24))}
    (hU : U.map NativeSporadic.M24.subtype = Subgroup.closure {g | g ∈ ug}) (x v : G₀) :
    (U ⊔ orbSub x v).map NativeSporadic.M24.subtype =
      Subgroup.closure {g | g ∈ ug ∨ ∃ j : ℕ, g = (x : Equiv.Perm (Fin 24)) ^ j * v *
        (x : Equiv.Perm (Fin 24))⁻¹ ^ j} := by
  rw [Subgroup.map_sup, hU, orbSub_map, orbSub, ← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_range, inv_pow]
  constructor
  · rintro (h | ⟨j, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, rfl⟩
  · rintro (h | ⟨j, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, rfl⟩

theorem frame_cases
    {k : ℕ} (hk : k < 26)
    {fr : List (ℕ × List ℤ)}
    (hchk : frameCheck 24 7 x7T (conjAll (candT k) u5T) (frameVs k) (frameCands fr) = true)
    (hinv : ∀ p ∈ fr, invOK 24 (wordT 24 gensT p.2) (invT 24 (wordT 24 gensT p.2)) = true)
    {v : G₀} (hvC : v ∈ Subgroup.centralizer
      (((eSub basis_u5).map (MulAut.conj (cand k)).toMonoidHom : Subgroup G₀) : Set G₀))
    (hvU : v ∉ (eSub basis_u5).map (MulAut.conj (cand k)).toMonoidHom)
    (hW : ∀ a ∈ (eSub basis_u5).map (MulAut.conj (cand k)).toMonoidHom ⊔ orbSub x7 v,
      ∀ b ∈ (eSub basis_u5).map (MulAut.conj (cand k)).toMonoidHom ⊔ orbSub x7 v,
        a * b = b * a)
    (hW2 : ∀ a ∈ (eSub basis_u5).map (MulAut.conj (cand k)).toMonoidHom ⊔ orbSub x7 v,
      a * a = 1) :
    (∃ e : G₀, (eSub basis_u5).map (MulAut.conj (cand k)).toMonoidHom ⊔ orbSub x7 v =
        (eSub basis_o).map (MulAut.conj e).toMonoidHom) ∨
      ∃ e : G₀, (eSub basis_u5).map (MulAut.conj (cand k)).toMonoidHom ⊔ orbSub x7 v =
        (eSub basis_t).map (MulAut.conj e).toMonoidHom := by
  set c := cand k with hc
  set U := (eSub basis_u5).map (MulAut.conj c).toMonoidHom with hU
  set W := U ⊔ orbSub x7 v with hWdef
  set ug : List (Equiv.Perm (Fin 24)) := List.ofFn fun i => ((c : G₀) : Equiv.Perm (Fin 24)) *
    ((vU5 i : G₀) : Equiv.Perm (Fin 24)) * ((c : G₀) : Equiv.Perm (Fin 24))⁻¹ with hug
  have hub : List.Forall₂ (Rep 24) (conjAll (candT k) u5T) ug := forall₂_cand hk forall₂_u5
  have hUmap : U.map NativeSporadic.M24.subtype = Subgroup.closure {g | g ∈ ug} :=
    (closure_ofFn_conj basis_u5 c).symm
  have hvQ : v ∈ Qg.map (MulAut.conj c).toMonoidHom := by
    rw [← cent_u5, ← centralizer_map_conj]
    exact hvC
  obtain ⟨q, hq, rfl⟩ := hvQ
  have hqP : (q : Equiv.Perm (Fin 24)) ∈ (enumeration qChain).reverse := by
    rw [List.mem_reverse, mem_enumeration_iff _ c_q_check, qChain, certificate_originalSubgroup,
      qGen, ← map_genOf]
    exact ⟨q, hq, rfl⟩
  obtain ⟨Tq, hTq, hTqq⟩ := exists_tab_of_mem (forall₂_allTables hn24 qChain) hqP
  have hcT : Rep 24 (candT k) ((c : G₀) : Equiv.Perm (Fin 24)) := rep_elt _
  have hcinv := List.all_eq_true.mp a_candInv k (List.mem_range.mpr hk)
  have hcTi := Rep.inv_of_invOK hcT hcinv
  have hTv : Rep 24 (conjTab 24 (candT k) (invT 24 (candT k)) Tq)
      ((((MulAut.conj c).toMonoidHom q : G₀)) : Equiv.Perm (Fin 24)) :=
    Rep.compT (Rep.compT hcT hTqq) hcTi
  have hTmem : conjTab 24 (candT k) (invT 24 (candT k)) Tq ∈ frameVs k :=
    List.mem_map.mpr ⟨Tq, hTq, rfl⟩
  set v := (MulAut.conj c).toMonoidHom q with hvdef
  have hvU' : (v : Equiv.Perm (Fin 24)) ∉ Subgroup.closure {g | g ∈ ug} := by
    rw [← hUmap]
    rintro ⟨u, hu, hvu⟩
    exact hvU (by rw [← Subtype.val_injective hvu]; exact hu)
  have hmemW : ∀ g ∈ ug ++ orbList 7 (x7 : Equiv.Perm (Fin 24)) (v : Equiv.Perm (Fin 24)),
      ∃ w ∈ W, (w : Equiv.Perm (Fin 24)) = g := by
    intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · have : g ∈ U.map NativeSporadic.M24.subtype := hUmap ▸ Subgroup.subset_closure hg
      obtain ⟨u, hu, rfl⟩ := this
      exact ⟨u, le_sup_left (a := U) hu, rfl⟩
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hg
      refine ⟨x7 ^ j * v * (x7 ^ j)⁻¹, le_sup_right (a := U) (conj_mem_orbSub x7 v j), ?_⟩
      simp [inv_pow]
  have hsq : ∀ g ∈ ug ++ orbList 7 (x7 : Equiv.Perm (Fin 24)) (v : Equiv.Perm (Fin 24)),
      g * g = 1 := by
    intro g hg
    obtain ⟨w, hw, rfl⟩ := hmemW g hg
    have := congrArg Subtype.val (hW2 w hw)
    simpa using this
  have hcomm : ∀ g ∈ ug ++ orbList 7 (x7 : Equiv.Perm (Fin 24)) (v : Equiv.Perm (Fin 24)),
      ∀ h ∈ ug ++ orbList 7 (x7 : Equiv.Perm (Fin 24)) (v : Equiv.Perm (Fin 24)),
        g * h = h * g := by
    intro g hg h hh
    obtain ⟨w, hw, rfl⟩ := hmemW g hg
    obtain ⟨w', hw', rfl⟩ := hmemW h hh
    have := congrArg Subtype.val (hW w hw w' hw')
    simpa using this
  have hx7 : Rep 24 x7T ((x7 : G₀) : Equiv.Perm (Fin 24)) := rep_elt w7
  obtain ⟨cg, hcg, hcl⟩ := closure_eq_of_frameCheck hn24 (by norm_num : 0 < 7) hchk
    (forall₂_frameCands hinv) hub hx7 (coe_pow_order orderOf_x7) hTmem hTv hvU' hsq hcomm
  rw [← map_sup_orbSub hUmap] at hcl
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hcg
  have hinj := Subgroup.map_injective (f := NativeSporadic.M24.subtype) Subtype.val_injective
  unfold candOf at hcl
  split_ifs at hcl
  · exact Or.inl ⟨elt p.2, hinj (by rw [hcl, closure_ofFn_conj basis_o])⟩
  · exact Or.inr ⟨elt p.2, hinj (by rw [hcl, closure_ofFn_conj basis_t])⟩

theorem frameConj_inv :
    ∀ p ∈ fr0W ++ fr1W ++ fr2W,
      invOK 24 (wordT 24 gensT p.2) (invT 24 (wordT 24 gensT p.2)) = true := by
  intro p hp
  exact List.all_eq_true.mp a_frameInv _ (List.mem_map.mpr ⟨p, hp, rfl⟩)

theorem frame_cases12
    {v : G₀}
    (hvC : v ∈ Subgroup.centralizer
      (((eSub basis_u5).map (MulAut.conj (cand 12)).toMonoidHom : Subgroup G₀) : Set G₀))
    (hvU : v ∉ (eSub basis_u5).map (MulAut.conj (cand 12)).toMonoidHom)
    (hW : ∀ a ∈ (eSub basis_u5).map (MulAut.conj (cand 12)).toMonoidHom ⊔ orbSub x7 v,
      ∀ b ∈ (eSub basis_u5).map (MulAut.conj (cand 12)).toMonoidHom ⊔ orbSub x7 v,
        a * b = b * a)
    (hW2 : ∀ a ∈ (eSub basis_u5).map (MulAut.conj (cand 12)).toMonoidHom ⊔ orbSub x7 v,
      a * a = 1) :
    (∃ e : G₀, (eSub basis_u5).map (MulAut.conj (cand 12)).toMonoidHom ⊔ orbSub x7 v =
        (eSub basis_o).map (MulAut.conj e).toMonoidHom) ∨
      ∃ e : G₀, (eSub basis_u5).map (MulAut.conj (cand 12)).toMonoidHom ⊔ orbSub x7 v =
        (eSub basis_t).map (MulAut.conj e).toMonoidHom :=
  frame_cases (by norm_num) a_frame0 (fun p hp => frameConj_inv p (by simp [hp])) hvC hvU hW
    hW2

theorem frame_cases17
    {v : G₀}
    (hvC : v ∈ Subgroup.centralizer
      (((eSub basis_u5).map (MulAut.conj (cand 17)).toMonoidHom : Subgroup G₀) : Set G₀))
    (hvU : v ∉ (eSub basis_u5).map (MulAut.conj (cand 17)).toMonoidHom)
    (hW : ∀ a ∈ (eSub basis_u5).map (MulAut.conj (cand 17)).toMonoidHom ⊔ orbSub x7 v,
      ∀ b ∈ (eSub basis_u5).map (MulAut.conj (cand 17)).toMonoidHom ⊔ orbSub x7 v,
        a * b = b * a)
    (hW2 : ∀ a ∈ (eSub basis_u5).map (MulAut.conj (cand 17)).toMonoidHom ⊔ orbSub x7 v,
      a * a = 1) :
    (∃ e : G₀, (eSub basis_u5).map (MulAut.conj (cand 17)).toMonoidHom ⊔ orbSub x7 v =
        (eSub basis_o).map (MulAut.conj e).toMonoidHom) ∨
      ∃ e : G₀, (eSub basis_u5).map (MulAut.conj (cand 17)).toMonoidHom ⊔ orbSub x7 v =
        (eSub basis_t).map (MulAut.conj e).toMonoidHom :=
  frame_cases (by norm_num) a_frame1 (fun p hp => frameConj_inv p (by simp [hp])) hvC hvU hW
    hW2

theorem frame_cases18
    {v : G₀}
    (hvC : v ∈ Subgroup.centralizer
      (((eSub basis_u5).map (MulAut.conj (cand 18)).toMonoidHom : Subgroup G₀) : Set G₀))
    (hvU : v ∉ (eSub basis_u5).map (MulAut.conj (cand 18)).toMonoidHom)
    (hW : ∀ a ∈ (eSub basis_u5).map (MulAut.conj (cand 18)).toMonoidHom ⊔ orbSub x7 v,
      ∀ b ∈ (eSub basis_u5).map (MulAut.conj (cand 18)).toMonoidHom ⊔ orbSub x7 v,
        a * b = b * a)
    (hW2 : ∀ a ∈ (eSub basis_u5).map (MulAut.conj (cand 18)).toMonoidHom ⊔ orbSub x7 v,
      a * a = 1) :
    (∃ e : G₀, (eSub basis_u5).map (MulAut.conj (cand 18)).toMonoidHom ⊔ orbSub x7 v =
        (eSub basis_o).map (MulAut.conj e).toMonoidHom) ∨
      ∃ e : G₀, (eSub basis_u5).map (MulAut.conj (cand 18)).toMonoidHom ⊔ orbSub x7 v =
        (eSub basis_t).map (MulAut.conj e).toMonoidHom :=
  frame_cases (by norm_num) a_frame2 (fun p hp => frameConj_inv p (by simp [hp])) hvC hvU hW
    hW2

end CFSG.Quasithin.KGC31.M24

end

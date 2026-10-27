module

public import CFSG.Sporadic.Co2Smith.GlNJG4

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.RankThree.Co2 CFSG.Certificates

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem prod_val_of_rows {g : ℕ → K} {R : ℕ → Array ℕ} :
    ∀ w : List ℕ, (∀ k ∈ w, (g k).val.val = rowsMatrix 22 (R k)) →
      ((w.map g).prod).val.val = rowsMatrix 22 (Native.glNJWord R w)
  | [], _ => by
    rw [List.map_nil, List.prod_nil, val_val_one, Native.glNJWord, List.foldr_nil,
      rowsMatrix_idRows]
  | k :: w, hw => by
    have ih := prod_val_of_rows w fun j hj => hw j (List.mem_cons_of_mem _ hj)
    rw [List.map_cons, List.prod_cons, val_val_mul, hw k List.mem_cons_self, ih,
      ← rowsMatrix_mulRows]
    rfl

section K


@[expose] noncomputable def qsK (s k : ℕ) : K := if k = 1 then jcElt s * qK 1 else qK k

theorem qsK_mem_QKs (s : ℕ) {k : ℕ} (hk : k < 2) : qsK s k ∈ QKs s := by
  unfold qsK
  split_ifs with h
  · exact subset_closure (Set.mem_insert_of_mem _ rfl)
  · have : k = 0 := by omega
    subst this
    exact subset_closure (Set.mem_insert _ _)

theorem qsK_val (s : ℕ) {k : ℕ} (hk : k < 2) :
    (qsK s k).val.val = rowsMatrix 22 (Native.glNJGs s k) := by
  unfold qsK Native.glNJGs
  split_ifs with h
  · subst h
    exact val_mul_rows (jcElt_val s) (qK_val (by norm_num))
  · exact qK_val (by omega)

@[expose] noncomputable def qsN (s : ℕ) (k : ℕ) : normalizer (Jc : Set K) :=
  if hk : k < 2 then ⟨qsK s k, QKs_le_N s (qsK_mem_QKs s hk)⟩ else 1

theorem piK_qsN (s : ℕ) {k : ℕ} (hk : k < 2) : piK (qsN s k) = piK (qN k) := by
  have e : qsN s k = (if k = 1 then ⟨jcElt s, le_normalizer (jcElt_mem s)⟩ else 1) * qN k := by
    apply Subtype.ext
    simp only [qsN, qN, hk, dite_true, show k < 3 by omega]
    unfold qsK
    split_ifs with h1
    · subst h1
      rfl
    · simp
  rw [e, map_mul]
  split_ifs
  · rw [piK_Jc (jcElt_mem s), one_mul]
  · rw [map_one, one_mul]

theorem piK_prod_qsN (s : ℕ) :
    ∀ w : List ℕ, (∀ k ∈ w, k < 2) → piK (w.map (qsN s)).prod = piK (w.map qN).prod
  | [], _ => rfl
  | k :: w, hw => by
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, map_mul, map_mul,
      piK_qsN s (hw k List.mem_cons_self),
      piK_prod_qsN s w fun j hj => hw j (List.mem_cons_of_mem _ hj)]

theorem prod_qsN_val (s : ℕ) :
    ∀ w : List ℕ, (∀ k ∈ w, k < 2) → (((w.map (qsN s)).prod : normalizer (Jc : Set K)) : K) =
      (w.map (qsK s)).prod
  | [], _ => rfl
  | k :: w, hw => by
    rw [List.map_cons, List.prod_cons, Subgroup.coe_mul,
      prod_qsN_val s w fun j hj => hw j (List.mem_cons_of_mem _ hj), List.map_cons,
      List.prod_cons]
    simp [qsN, show k < 2 from hw k List.mem_cons_self]

theorem prod_qN_val :
    ∀ w : List ℕ, (∀ k ∈ w, k < 3) → (((w.map qN).prod : normalizer (Jc : Set K)) : K) =
      (w.map qK).prod
  | [], _ => rfl
  | k :: w, hw => by
    rw [List.map_cons, List.prod_cons, Subgroup.coe_mul,
      prod_qN_val w fun j hj => hw j (List.mem_cons_of_mem _ hj), List.map_cons,
      List.prod_cons, qN_val (hw k List.mem_cons_self)]

theorem prod_qsK_mem (s : ℕ) :
    ∀ w : List ℕ, (∀ k ∈ w, k < 2) → (w.map (qsK s)).prod ∈ QKs s
  | [], _ => one_mem _
  | k :: w, hw => by
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (qsK_mem_QKs s (hw k List.mem_cons_self))
      (prod_qsK_mem s w fun j hj => hw j (List.mem_cons_of_mem _ hj))

end K

section Fus

variable
  {G : Type} [Group G] {z : G} (φ : centralizer ({z} : Set G) ≃* Cz)

theorem not_comp_fusion [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2)
    (hφz : φ (zH z) = z0C) {L : Subgroup G} (hL : IsNJComp φ L) {s : ℕ} (hs : s = 18 ∨ s = 94)
    (hLs : ∀ y : Cz, phiH φ y ∈ L ↔ (y : K) ∈ QKs s) : False := by
  obtain ⟨hA, hX, hXp, hx2, -, hax, hfix⟩ := glNJFus_spec
  have hA3 : ∀ k ∈ Native.glNJFusA, k < 3 := hA
  have hX3 : ∀ k ∈ Native.glNJFusX, k < 3 := fun k hk => by have := hX k hk; omega
  have hXp3 : ∀ k ∈ Native.glNJFusXp, k < 3 := fun k hk => by have := hXp k hk; omega
  set xN := (Native.glNJFusX.map (qsN s)).prod
  set xpN := (Native.glNJFusXp.map (qsN s)).prod
  set x0 := (Native.glNJFusX.map qN).prod
  set x0p := (Native.glNJFusXp.map qN).prod
  set aN := (Native.glNJFusA.map qN).prod
  have hx0r : (x0 : K).val.val = rowsMatrix 22 (Native.glNJWord Native.glNJG Native.glNJFusX) := by
    rw [prod_qN_val _ hX3]
    exact prod_qK_val _ hX3
  have hx0pr : (x0p : K).val.val =
      rowsMatrix 22 (Native.glNJWord Native.glNJG Native.glNJFusXp) := by
    rw [prod_qN_val _ hXp3]
    exact prod_qK_val _ hXp3
  have har : (aN : K).val.val = rowsMatrix 22 (Native.glNJWord Native.glNJG Native.glNJFusA) := by
    rw [prod_qN_val _ hA3]
    exact prod_qK_val _ hA3
  have hx0sq : x0 * x0 = 1 :=
    Subtype.ext (eq_of_rows (val_mul_rows hx0r hx0r) val_one_rows hx2)
  have hax' : aN * x0p = x0 * aN :=
    Subtype.ext (eq_of_rows (val_mul_rows har hx0pr) (val_mul_rows hx0r har) hax)
  have hpx : piK xN = piK x0 := piK_prod_qsN s _ hX
  have hpxp : piK xpN = piK x0p := piK_prod_qsN s _ hXp
  have hxK : (xN : K) = (Native.glNJFusX.map (qsK s)).prod := prod_qsN_val s _ hX
  have hxpK : (xpN : K) = (Native.glNJFusXp.map (qsK s)).prod := prod_qsN_val s _ hXp
  have hxQ : (xN : K) ∈ QKs s := by rw [hxK]; exact prod_qsK_mem s _ hX
  have hxpQ : (xpN : K) ∈ QKs s := by rw [hxpK]; exact prod_qsK_mem s _ hXp
  have hxz : (xN : K) ∈ Cz := QKs_le_Cz s hxQ
  have hxpz : (xpN : K) ∈ Cz := QKs_le_Cz s hxpQ
  have hQJ : ∀ y ∈ QKs s, y ∈ Jc → y = 1 := by
    intro y hy hJ
    have h1 := hL.inf _ ((hLs ⟨y, QKs_le_Cz s hy⟩).2 hy) ((mem_JGc φ).2 ⟨_, hJ, rfl⟩)
    exact congrArg Subtype.val (phiH_injective φ (h1.trans (map_one _).symm))
  have hx0pz : piK x0p 0 = 0 := by
    rw [← hpxp]
    exact (piK_zero_iff xpN).2 hxpz
  have hk : piK x0 (piK aN 0) = piK aN 0 := by
    calc piK x0 (piK aN 0) = piK (x0 * aN) 0 := by rw [map_mul]; rfl
      _ = piK (aN * x0p) 0 := by rw [hax']
      _ = piK aN 0 := by rw [map_mul, Equiv.Perm.mul_apply, hx0pz]
  set y : normalizer (JGc φ : Set G) := ⟨phiH φ ⟨xN, hxz⟩, phiH_mem_NG φ xN.2⟩
  have hyL : (y : G) ∈ L := (hLs ⟨xN, hxz⟩).2 hxQ
  have hpy : piG φ hz y = piK x0 := by
    rw [← hpx]
    exact piG_phiH φ hz ⟨xN, hxz⟩ xN.2
  obtain ⟨l, hlL, hpl⟩ := piG_L_surj φ hz hφz hL hLs (piK_mem_njAut aN)
  set y' := l⁻¹ * y * l
  have hy'L : (y' : G) ∈ L := by
    show (l : G)⁻¹ * y * l ∈ L
    exact L.mul_mem (L.mul_mem (L.inv_mem hlL) hyL) hlL
  have hx0pe : x0p = aN⁻¹ * x0 * aN := by
    rw [mul_assoc, ← hax', ← mul_assoc, inv_mul_cancel, one_mul]
  have hpy' : piG φ hz y' = piK x0p := by
    show piG φ hz (l⁻¹ * y * l) = _
    rw [map_mul, map_mul, map_inv, hpl, hpy, hx0pe, map_mul, map_mul, map_inv]
  have hy'H : (y' : G) ∈ centralizer ({z} : Set G) :=
    (piG_zero_iff φ hz hφz y').1 (by rw [hpy']; exact hx0pz)
  set X'' := φ ⟨y', hy'H⟩
  have hX''y : phiH φ X'' = y' := phiH_apply_symm φ _ hy'H
  have hX''Q : (X'' : K) ∈ QKs s := (hLs X'').1 (by rw [hX''y]; exact hy'L)
  have hX''N : (X'' : K) ∈ normalizer (Jc : Set K) :=
    (phiH_mem_NG_iff φ X'').1 (by rw [hX''y]; exact y'.2)
  have hpX'' : piK ⟨X'', hX''N⟩ = piK xpN := by
    rw [← piG_phiH φ hz X'' hX''N, hpxp]
    have e : (⟨phiH φ X'', phiH_mem_NG φ hX''N⟩ : normalizer (JGc φ : Set G)) = y' :=
      Subtype.ext hX''y
    rw [e, hpy']
  have hX''eq : (X'' : K) = xpN := congrArg Subtype.val (piK_inj_of_inf hQJ hX''Q hxpQ hpX'')
  have key : fixK (xN : K) = fixK (xpN : K) := by
    by_cases h1 : (xN : K) = 1
    · have hy1 : (y : G) = 1 := by
        show phiH φ ⟨xN, hxz⟩ = 1
        rw [show (⟨xN, hxz⟩ : Cz) = 1 from Subtype.ext h1, map_one]
      have hy'1 : (y' : G) = 1 := by
        show (l : G)⁻¹ * y * l = 1
        rw [hy1, mul_one, inv_mul_cancel]
      have hX1 : X'' = 1 := phiH_injective φ (by rw [hX''y, hy'1, map_one])
      rw [h1, ← hX''eq, hX1]
      rfl
    · have hsq : (xN : K) * xN = 1 := by
        refine hQJ _ (mul_mem hxQ hxQ) (mem_Jc_of_piK_eq_one (g := xN * xN) ?_)
        rw [map_mul, hpx, ← map_mul, hx0sq, map_one]
      have hsq' : (X'' : K) * X'' = 1 := by
        have hy2 : (y : G) * y = 1 := by
          show phiH φ ⟨xN, hxz⟩ * phiH φ ⟨xN, hxz⟩ = 1
          rw [← map_mul, show (⟨xN, hxz⟩ * ⟨xN, hxz⟩ : Cz) = 1 from Subtype.ext hsq, map_one]
        have hy'2 : phiH φ (X'' * X'') = 1 := by
          rw [map_mul, hX''y]
          show (l : G)⁻¹ * y * l * ((l : G)⁻¹ * y * l) = 1
          calc (l : G)⁻¹ * y * l * ((l : G)⁻¹ * y * l) = (l : G)⁻¹ * (y * y) * l := by group
            _ = 1 := by rw [hy2]; group
        exact congrArg Subtype.val (phiH_injective φ (hy'2.trans (map_one _).symm))
      have hne' : (X'' : K) ≠ 1 := by
        intro h2
        apply h1
        have hy'1 : (y' : G) = 1 := by
          rw [← hX''y, show X'' = 1 from Subtype.ext h2, map_one]
        have hy1 : (y : G) = 1 := by
          have e : (y : G) = l * y' * (l : G)⁻¹ := by
            show (y : G) = l * ((l : G)⁻¹ * y * l) * (l : G)⁻¹
            group
          rw [e, hy'1, mul_one, mul_inv_cancel]
        have : (⟨xN, hxz⟩ : Cz) = 1 := phiH_injective φ (hy1.trans (map_one _).symm)
        exact congrArg Subtype.val this
      have hconj : IsConj (φ.symm ⟨xN, hxz⟩ : G) (φ.symm X'' : G) := by
        refine isConj_iff.2 ⟨(l : G)⁻¹, ?_⟩
        rw [← phiH_apply, ← phiH_apply, hX''y, inv_inv]
        rfl
      have hf := fixFusion hz φ ⟨xN, hxz⟩ X'' (Subtype.ext hsq)
        (fun e => h1 (congrArg Subtype.val e)) (Subtype.ext hsq')
        (fun e => hne' (congrArg Subtype.val e)) hconj
      rw [← hX''eq]
      exact hf
  rw [fixK_eq_glNJFixR (by rw [hxK]; exact prod_val_of_rows _ fun k hk => qsK_val s (hX k hk)),
    fixK_eq_glNJFixR (by rw [hxpK]; exact prod_val_of_rows _ fun k hk => qsK_val s (hXp k hk))]
    at key
  exact hfix s (by rcases hs with rfl | rfl <;> simp) key

end Fus

end CFSG.Sporadic.Co2Smith

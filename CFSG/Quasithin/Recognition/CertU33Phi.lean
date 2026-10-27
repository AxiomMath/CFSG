module

public import CFSG.Quasithin.Recognition.CertU33Outer
public import CFSG.Quasithin.Recognition.CertG2TwoData

public section

namespace CFSG.Quasithin

open CFSG.CosetTable CFSG.Sporadic.Bridge CFSG.Monster.B.Co2

@[expose] def u33El (s : String) : U33G := wordProd u33GenPG (u33W s)

theorem u33PresHom_u33El (s : String) : u33PresHom (u33El s) = wordProd u33GenP (u33W s) :=
  u33PresHom_wordProd' _

theorem u33El_eq (s : String) : u33El s = wordProd u33GenPG (u33W s) := rfl

theorem wordProd_u33GenPG_mk (w : List (Fin 5 × Bool)) :
    wordProd u33GenPG (w.map fun l => (l.1.val, l.2)) =
      PresentedGroup.mk _ (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    obtain ⟨i, b⟩ := x
    have e : FreeGroup.mk ((i, b) :: w) = FreeGroup.mk [(i, b)] * FreeGroup.mk w := rfl
    rw [e, map_mul, ← ih]
    cases b with
    | true =>
      simp only [wordProd, List.map_cons, List.prod_cons, ↓reduceIte]
      rw [u33GenPG_of]
      rfl
    | false =>
      simp only [wordProd, List.map_cons, List.prod_cons, Bool.false_eq_true, ↓reduceIte]
      rw [u33GenPG_of]
      rfl

theorem u33El_eq_mk (s : String) :
    u33El s = PresentedGroup.mk _ (FreeGroup.mk (u33Word s)) :=
  wordProd_u33GenPG_mk _

theorem u33GenP_fin (k : Fin 5) : u33GenP k.val = u33Img k := by
  simp [u33GenP]

theorem u33_conjB_L : ∀ k < 5,
    compL (u33WordL (u33W (g2ConjStrings.getD (5 * 1 + k) ""))) (u33WordL (u33W "asy")) =
      compL (u33WordL (u33W "asy")) (u33WordL (u33W (u33PiConjW.getD k ""))) := by
  decide +kernel

theorem u33_letters_conjB :
    ∀ k < 5, ∀ l ∈ u33W (g2ConjStrings.getD (5 * 1 + k) ""), l.1 < 5 := by
  decide +kernel

theorem u33_letters_asy : ∀ l ∈ u33W "asy", l.1 < 5 := by
  decide +kernel

theorem u33_conjB_perm (k : ℕ) (hk : k < 5) :
    wordProd u33GenP (u33W (g2ConjStrings.getD (5 * 1 + k) "")) *
        wordProd u33GenP (u33W "asy") =
      wordProd u33GenP (u33W "asy") * wordProd u33GenP (u33W (u33PiConjW.getD k "")) := by
  have h1 := repL_mul (u33_wordL_rep _ (u33_letters_conjB k hk))
    (u33_wordL_rep _ u33_letters_asy)
  have h2 := repL_mul (u33_wordL_rep _ u33_letters_asy)
    (u33_wordL_rep _ (u33Pi_conj_letters k hk))
  rw [u33_conjB_L k hk] at h1
  exact eq_of_repL h1 h2

theorem u33_conjB_G
    (k : ℕ) (hk : k < 5) :
    (u33El "asy")⁻¹ * u33El (g2ConjStrings.getD (5 * 1 + k) "") * u33El "asy" =
      u33El (u33PiConjW.getD k "") := by
  have h : u33El (g2ConjStrings.getD (5 * 1 + k) "") * u33El "asy" =
      u33El "asy" * u33El (u33PiConjW.getD k "") := by
    apply u33PresHom_injective
    simp only [map_mul, u33PresHom_u33El]
    exact u33_conjB_perm k hk
  calc (u33El "asy")⁻¹ * u33El (g2ConjStrings.getD (5 * 1 + k) "") * u33El "asy"
      = (u33El "asy")⁻¹ * (u33El (g2ConjStrings.getD (5 * 1 + k) "") * u33El "asy") :=
        mul_assoc _ _ _
    _ = (u33El "asy")⁻¹ * (u33El "asy" * u33El (u33PiConjW.getD k "")) := by rw [h]
    _ = u33El (u33PiConjW.getD k "") := inv_mul_cancel_left _ _

@[expose] noncomputable def u33ToJ
    : U33G ≃* ↥u33J :=
  (MulEquiv.ofBijective u33PresHom.rangeRestrict
    ⟨fun _ _ h => u33PresHom_injective (congrArg Subtype.val h),
      u33PresHom.rangeRestrict_surjective⟩).trans
    (MulEquiv.subgroupCongr range_u33PresHom)

theorem u33ToJ_coe (x : U33G) :
    ((u33ToJ x : ↥u33J) : Equiv.Perm (Fin 28)) = u33PresHom x := rfl

@[expose] noncomputable def u33Phi'
    : MulAut U33G :=
  u33ToJ.trans (u33Phi.trans u33ToJ.symm)

theorem u33PresHom_phi'
    (x : U33G) :
    u33PresHom (u33Phi' x) = u33Pi * u33PresHom x * u33Pi := by
  have h : u33ToJ (u33Phi' x) = u33Phi (u33ToJ x) := by
    simp [u33Phi']
  exact congrArg Subtype.val h

theorem u33Phi'_gen
    (k : Fin 5) :
    u33Phi' (PresentedGroup.of k) = u33El (u33PiConjW.getD k "") := by
  apply u33PresHom_injective
  rw [u33PresHom_phi', u33PresHom_of, u33PresHom_u33El, ← u33Pi_conj k k.2, u33GenP_fin]

theorem u33_centralizer_gens
    (c : Equiv.Perm (Fin 28))
    (hc : ∀ k < 5, c * u33GenP k = u33GenP k * c) : c = 1 := by
  refine u33_centralizer_trivial c fun x hx => ?_
  unfold u33J at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨hsz, -⟩ := u33Chain_check
    rw [hsz] at hk
    have hg : permOfArr 28 u33Gens[k]! = u33GenP k := by
      rw [show u33GenP k = u33Img ⟨k, hk⟩ by simp [u33GenP, hk]]
      exact permOfArr_u33Gens ⟨k, hk⟩
    rw [hg]
    exact hc k hk
  | one => simp
  | mul x y _ _ hx hy =>
    calc c * (x * y) = (c * x) * y := (mul_assoc _ _ _).symm
      _ = x * (c * y) := by rw [hx, mul_assoc]
      _ = x * y * c := by rw [hy, mul_assoc]
  | inv x _ hx =>
    calc c * x⁻¹ = x⁻¹ * (x * c) * x⁻¹ := by group
      _ = x⁻¹ * (c * x) * x⁻¹ := by rw [hx]
      _ = x⁻¹ * c := by group

theorem u33Phi'_not_inner
    : ¬ ∃ w : U33G, ∀ x : U33G, u33Phi' x = w * x * w⁻¹ := by
  rintro ⟨w, hw⟩
  have key : ∀ k < 5, (u33PresHom w)⁻¹ * u33Pi * u33GenP k =
      u33GenP k * ((u33PresHom w)⁻¹ * u33Pi) := by
    intro k hk
    have h1 := congrArg u33PresHom (hw (u33GenPG k))
    rw [u33PresHom_phi', map_mul, map_mul, map_inv, u33PresHom_genPG] at h1
    calc (u33PresHom w)⁻¹ * u33Pi * u33GenP k
        = (u33PresHom w)⁻¹ * (u33Pi * u33GenP k * (u33Pi * u33Pi)) := by
          rw [u33Pi_sq]; group
      _ = (u33PresHom w)⁻¹ * (u33Pi * u33GenP k * u33Pi) * u33Pi := by group
      _ = (u33PresHom w)⁻¹ * (u33PresHom w * u33GenP k * (u33PresHom w)⁻¹) * u33Pi := by
          rw [h1]
      _ = u33GenP k * ((u33PresHom w)⁻¹ * u33Pi) := by group
  have hc := u33_centralizer_gens _ key
  have hP : u33Pi = u33PresHom w := by
    have := congrArg (u33PresHom w * ·) hc
    simpa using this
  exact u33Pi_not_mem (by rw [hP]; exact (u33ToJ w).2)

theorem u33_asy_L : compL (u33WordL (u33W "asy"))
    (compL (compL u33PiTab (u33WordL (u33W "asy"))) u33PiTab) = List.range 28 := by
  decide +kernel

theorem u33_asy_phi
    : u33El "asy" * u33Phi' (u33El "asy") = 1 := by
  apply u33PresHom_injective
  rw [map_mul, u33PresHom_phi', u33PresHom_u33El, map_one]
  have h := repL_mul (u33_wordL_rep _ u33_letters_asy)
    (repL_mul (repL_mul u33_pi_rep (u33_wordL_rep _ u33_letters_asy)) u33_pi_rep)
  rw [u33_asy_L] at h
  exact eq_of_repL h (repL_one 28)

theorem hom_mem_closure {G : Type*} [Group G] (φ : G →* G) {S : Set G}
    (h : ∀ s ∈ S, φ s ∈ Subgroup.closure S) : ∀ x ∈ Subgroup.closure S, φ x ∈ Subgroup.closure S := by
  intro x hx
  have : (Subgroup.closure S).map φ ≤ Subgroup.closure S := by
    rw [MonoidHom.map_closure]
    exact (Subgroup.closure_le _).2 (by rintro _ ⟨s, hs, rfl⟩; exact h s hs)
  exact this ⟨x, hx, rfl⟩

theorem u33_A_L : ∃ i < 32, u33TelTab.getD i [] = u33WordL (u33W "A") := by
  decide +kernel

theorem u33_B_L : ∃ i < 32, u33TelTab.getD i [] = u33WordL (u33W "B") := by
  decide +kernel

theorem u33_byay_L : ∃ i < 32, u33TelTab.getD i [] = u33WordL (u33W "byay") := by
  decide +kernel

theorem u33_letters_ABbyay : (∀ l ∈ u33W "A", l.1 < 5) ∧ (∀ l ∈ u33W "B", l.1 < 5) ∧
    (∀ l ∈ u33W "byay", l.1 < 5) := by
  decide +kernel

theorem u33El_mem_T
    {s : String} (h : ∃ i < 32, u33TelTab.getD i [] = u33WordL (u33W s))
    (hl : ∀ l ∈ u33W s, l.1 < 5) : u33El s ∈ u33Data.T := by
  obtain ⟨i, hi, h⟩ := h
  rw [u33Data.mem_T_iff]
  refine ⟨⟨i, hi⟩, u33PresHom_injective ?_⟩
  refine eq_of_repL (l := u33TelTab.getD i []) ?_ ?_
  · have := u33_telTab_rep i hi
    rwa [← u33Tel_hom] at this
  · rw [u33PresHom_u33El, h]
    exact u33_wordL_rep _ hl

theorem u33Phi'_genPG
    (k : ℕ) (hk : k < 5) :
    u33Phi' (u33GenPG k) = u33El (u33PiConjW.getD k "") := by
  have := u33Phi'_gen ⟨k, hk⟩
  rwa [← u33GenPG_of ⟨k, hk⟩] at this

theorem u33Phi'_T
    : ∀ x ∈ u33Data.T, u33Phi' x ∈ u33Data.T := by
  obtain ⟨hA, hB, hbyay⟩ := u33_letters_ABbyay
  have hmem : ∀ s ∈ ({u33GenPG 0, u33GenPG 1, u33GenPG 2} : Set U33G),
      u33Phi'.toMonoidHom s ∈ Subgroup.closure ({u33GenPG 0, u33GenPG 1, u33GenPG 2} : Set U33G) := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · show u33Phi' (u33GenPG 0) ∈ _
      rw [u33Phi'_genPG 0 (by norm_num)]
      exact u33El_mem_T (s := "A") u33_A_L hA
    · show u33Phi' (u33GenPG 1) ∈ _
      rw [u33Phi'_genPG 1 (by norm_num)]
      exact u33El_mem_T (s := "B") u33_B_L hB
    · show u33Phi' (u33GenPG 2) ∈ _
      rw [u33Phi'_genPG 2 (by norm_num)]
      exact u33El_mem_T (s := "byay") u33_byay_L hbyay
  exact hom_mem_closure _ hmem

theorem u33_letters_xaa : ∀ l ∈ u33W "xaa", l.1 < 4 := by decide +kernel

theorem u33_letters_aYA : ∀ l ∈ u33W "aYA", l.1 = 0 ∨ l.1 = 4 := by decide +kernel

theorem u33Phi'_A
    : ∀ x ∈ u33Data.A, u33Phi' x ∈ u33Data.A := by
  have hmem : ∀ s ∈ ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 3} : Set U33G),
      u33Phi'.toMonoidHom s ∈
        Subgroup.closure ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 3} : Set U33G) := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact u33Data.T_le_A (u33Phi'_T _ u33Data.a_mem_T)
    · exact u33Data.T_le_A (u33Phi'_T _ u33Data.b_mem_T)
    · exact u33Data.T_le_A (u33Phi'_T _ u33Data.s_mem_T)
    · show u33Phi' (u33GenPG 3) ∈ _
      rw [u33Phi'_genPG 3 (by norm_num)]
      show u33El "xaa" ∈ _
      rw [u33El_eq]
      refine wordProd_mem_pred (P := fun k => k < 4) ?_ u33_letters_xaa
      intro i hi
      apply Subgroup.subset_closure
      interval_cases i <;> simp
  exact hom_mem_closure _ hmem

theorem u33Phi'_B
    : ∀ x ∈ u33Data.B, u33Phi' x ∈ u33Data.B := by
  have hmem : ∀ s ∈ ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 4} : Set U33G),
      u33Phi'.toMonoidHom s ∈
        Subgroup.closure ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 4} : Set U33G) := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact u33Data.T_le_B (u33Phi'_T _ u33Data.a_mem_T)
    · exact u33Data.T_le_B (u33Phi'_T _ u33Data.b_mem_T)
    · exact u33Data.T_le_B (u33Phi'_T _ u33Data.s_mem_T)
    · show u33Phi' (u33GenPG 4) ∈ _
      rw [u33Phi'_genPG 4 (by norm_num)]
      show u33El "aYA" ∈ _
      rw [u33El_eq]
      refine wordProd_mem_pred (P := fun k => k = 0 ∨ k = 4) ?_ u33_letters_aYA
      intro i hi
      apply Subgroup.subset_closure
      rcases hi with rfl | rfl <;> simp
  exact hom_mem_closure _ hmem

theorem u33_PVP_L : ∀ i < 3, compL (compL u33PiTab (u33VTab i)) u33PiTab = u33VTab i := by
  decide +kernel

theorem u33Phi'_V
    (u : U33G) (hu : u ∈ u33VSet) : u33Phi' u = u := by
  obtain ⟨i, hi⟩ := hu
  apply u33PresHom_injective
  rw [u33PresHom_phi', hi]
  have h := repL_mul (repL_mul u33_pi_rep (u33_vTab_rep i)) u33_pi_rep
  rw [u33_PVP_L i i.2] at h
  exact eq_of_repL h (u33_vTab_rep i)

theorem u33Phi'_PA
    : ∀ x ∈ u33Extra.PA, u33Phi' x ∈ u33Extra.PA :=
  hom_mem_closure u33Phi'.toMonoidHom (S := u33VSet) fun s hs => by
    show u33Phi' s ∈ _
    rw [u33Phi'_V s hs]
    exact Subgroup.subset_closure hs

theorem u33_PZP_L : compL (compL u33PiTab u33ZTab) u33PiTab = u33ZTab := by
  decide +kernel

theorem u33Phi'_z
    : u33Phi' u33z = u33z := by
  apply u33PresHom_injective
  rw [u33PresHom_phi', u33PresHom_z]
  have h := repL_mul (repL_mul u33_pi_rep u33_z_rep) u33_pi_rep
  rw [u33_PZP_L] at h
  exact eq_of_repL h u33_z_rep

theorem u33Phi'_PB
    : ∀ x ∈ u33Extra.PB, u33Phi' x ∈ u33Extra.PB :=
  hom_mem_closure u33Phi'.toMonoidHom (S := {u33z}) fun s hs => by
    rw [Set.mem_singleton_iff] at hs
    subst hs
    show u33Phi' u33z ∈ _
    rw [u33Phi'_z]
    exact Subgroup.subset_closure rfl

end CFSG.Quasithin

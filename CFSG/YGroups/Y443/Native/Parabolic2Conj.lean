module

public import CFSG.YGroups.Y443.Native.Parabolic2Gen
public import CFSG.YGroups.Y443.Native.Parabolic2CheckA

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Open CFSG.YGroups.Y443Native

@[expose] noncomputable def Grho : Gmat := ⟨wordLin rhoWord, wordLin_mem_Gmat _⟩

theorem coe_Grho : ((Grho : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = wordLin rhoWord := rfl

theorem rho_sq :
    wordLin rhoWord * wordLin rhoWord = 1 := by
  have h := p2_a.1
  rw [wordLin_append] at h
  exact h

theorem rho_inv :
    (wordLin rhoWord)⁻¹ = wordLin rhoWord := inv_eq_of_mul_eq_one_right rho_sq

theorem rho_comm_gL_of_mem
    {s : ℕ} (hs : s ∈ rhoGens) :
    wordLin rhoWord * gL s = gL (armSwapL s) * wordLin rhoWord := by
  have h := p2_a.2.1 s hs
  rw [wordLin_append, wordLin_append, wordLin_Lw, wordLin_Lw] at h
  exact h

theorem rho_comm_gL_of_five_eight
    {s : ℕ} (hs5 : 5 ≤ s) (hs8 : s ≤ 8) :
    wordLin rhoWord * gL s = gL (armSwapL s) * wordLin rhoWord := by
  have h4 : armSwapL (s - 4) = s := by
    unfold armSwapL
    split_ifs <;> omega
  have h5 : armSwapL s = s - 4 := by
    unfold armSwapL
    split_ifs <;> omega
  have hmem : s - 4 ∈ rhoGens := by
    simp only [rhoGens, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have h := rho_comm_gL_of_mem hmem
  rw [h4] at h
  have e1 : gL s = wordLin rhoWord * gL (s - 4) * (wordLin rhoWord)⁻¹ :=
    eq_mul_inv_of_mul_eq h.symm
  rw [h5, e1, rho_inv]
  calc wordLin rhoWord * (wordLin rhoWord * gL (s - 4) * wordLin rhoWord)
      = (wordLin rhoWord * wordLin rhoWord) * gL (s - 4) * wordLin rhoWord := by
        simp only [mul_assoc]
    _ = gL (s - 4) * wordLin rhoWord := by rw [rho_sq, one_mul]

theorem rho_conj_gL
    {s : ℕ} (hs : s ≤ 11) :
    wordLin rhoWord * gL s * (wordLin rhoWord)⁻¹ = gL (armSwapL s) := by
  have key : wordLin rhoWord * gL s = gL (armSwapL s) * wordLin rhoWord := by
    by_cases h0 : s = 0
    · subst h0
      simp [gL, armSwapL]
    · by_cases h4 : s ≤ 4
      · exact rho_comm_gL_of_mem (by
          simp only [rhoGens, List.mem_cons, List.not_mem_nil, or_false]
          omega)
      · by_cases h8 : s ≤ 8
        · exact rho_comm_gL_of_five_eight (by omega) h8
        · exact rho_comm_gL_of_mem (by
            simp only [rhoGens, List.mem_cons, List.not_mem_nil, or_false]
            omega)
  rw [key, mul_inv_cancel_right]

theorem armSwapL_le {s : ℕ} (hs : s ≤ 11) : armSwapL s ≤ 11 := by
  unfold armSwapL
  split_ifs <;> omega

theorem rho_conj_evalGL :
    ∀ l : List ℕ, (∀ c ∈ l, c ≤ 11) →
    wordLin rhoWord * evalGL l * (wordLin rhoWord)⁻¹ = evalGL (l.map armSwapL)
  | [], _ => by simp [evalGL]
  | [_], _ => by simp [evalGL]
  | a :: b :: l, h => by
    have ha := h a (by simp)
    have hb := h b (by simp)
    have ih := rho_conj_evalGL l (fun c hc => h c (by simp [hc]))
    have e1 : wordLin rhoWord * (gL a)⁻¹ * (wordLin rhoWord)⁻¹ = (gL (armSwapL a))⁻¹ := by
      rw [← rho_conj_gL ha]
      group
    simp only [List.map_cons, evalGL]
    calc wordLin rhoWord * ((gL a)⁻¹ * gL b * evalGL l) * (wordLin rhoWord)⁻¹
        = (wordLin rhoWord * (gL a)⁻¹ * (wordLin rhoWord)⁻¹) *
          (wordLin rhoWord * gL b * (wordLin rhoWord)⁻¹) *
          (wordLin rhoWord * evalGL l * (wordLin rhoWord)⁻¹) := by group
      _ = (gL (armSwapL a))⁻¹ * gL (armSwapL b) * evalGL (l.map armSwapL) := by
        rw [e1, rho_conj_gL hb, ih]

theorem rho_conj_cbar :
    wordLin rhoWord * evalGL slet * (wordLin rhoWord)⁻¹ = evalGL sletP :=
  rho_conj_evalGL slet slet_le

theorem axL_eq_axElt {s : ℕ} {g : E443Gen} (hg : y443GenOfLetter s = some g) :
    axL s = axElt g := by
  apply Subtype.ext
  show y443Gen 0 * y443Gen s = _
  simp only [y443Gen, hg]
  rfl

theorem exists_letter_of_gen : ∀ g : E443Gen, ∃ s : Fin 12, y443GenOfLetter s.val = some g := by
  decide

theorem hom_ext_axL {G : Type*} [Group G] {f f' : MonsterY443Derived →* G}
    (h : ∀ s : ℕ, s ≤ 11 → f (axL s) = f' (axL s)) : f = f' := by
  have h1 : f.comp e443Phi.toMonoidHom = f'.comp e443Phi.toMonoidHom := by
    refine PresentedGroup.ext fun g => ?_
    obtain ⟨s, hs⟩ := exists_letter_of_gen g
    show f (e443Phi (PresentedGroup.of g)) = f' (e443Phi (PresentedGroup.of g))
    rw [← axElt_eq, ← axL_eq_axElt hs]
    exact h s.val (Nat.le_of_lt_succ s.isLt)
  refine MonoidHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := e443Phi.surjective y
  exact DFunLike.congr_fun h1 x

theorem fM_rho_axL
    {ρ' : MonsterY443Derived →* MonsterY443Derived}
    (h : ∀ s : ℕ, s ≤ 11 → ρ' (axL s) = axL (armSwapL s)) {s : ℕ} (hs : s ≤ 11) :
    fM (ρ' (axL s)) = Grho * fM (axL s) * Grho⁻¹ := by
  refine Subtype.ext ?_
  rw [h s hs, fM_axL (armSwapL_le hs), Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    fM_axL hs]
  exact (rho_conj_gL hs).symm

theorem fM_comp_of_axL
    {ρ' : MonsterY443Derived →* MonsterY443Derived}
    (h : ∀ s : ℕ, s ≤ 11 → ρ' (axL s) = axL (armSwapL s)) :
    fM.comp ρ' = (MulAut.conj Grho).toMonoidHom.comp fM :=
  hom_ext_axL fun _ hs => by simpa [MulAut.conj_apply] using fM_rho_axL h hs

theorem fM_apply_of_axL
    {ρ' : MonsterY443Derived →* MonsterY443Derived}
    (h : ∀ s : ℕ, s ≤ 11 → ρ' (axL s) = axL (armSwapL s)) (x : MonsterY443Derived) :
    ((fM (ρ' x) : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) =
      wordLin rhoWord * ((fM x : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * (wordLin rhoWord)⁻¹ := by
  have := congrArg (fun f : MonsterY443Derived →* Gmat => ((f x : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB))
    (fM_comp_of_axL h)
  simpa [MulAut.conj_apply, coe_Grho] using this

@[expose] noncomputable def omegaP : SpaceB ≃ₗ[ℚ] SpaceB :=
  wordLin omegaWord * (wordLin rhoWord)⁻¹

theorem omegaP_mem : omegaP ∈ Gmat :=
  mul_mem (wordLin_mem_Gmat _) (inv_mem (wordLin_mem_Gmat _))

theorem omegaP_conj :
    omegaP * evalGL sletP * omegaP⁻¹ = tStar := by
  rw [← rho_conj_cbar]
  calc omegaP * (wordLin rhoWord * evalGL slet * (wordLin rhoWord)⁻¹) * omegaP⁻¹
      = wordLin omegaWord * evalGL slet * (wordLin omegaWord)⁻¹ := by
        unfold omegaP
        group
    _ = tStar := omega_conj_slet

theorem cbarP_mem_shortClass :
    evalGL sletP ∈ shortClass :=
  mem_shortClass_of_conj omegaP_mem omegaP_conj

theorem cbarP_ne_one :
    evalGL sletP ≠ 1 := by
  intro h
  have h1 := omegaP_conj
  rw [h, mul_one, mul_inv_cancel] at h1
  exact tStar_ne_one h1.symm

theorem centralizer_cbarP_eq :
    Gmat ⊓ Subgroup.centralizer {evalGL sletP} = Cgen.map (MulAut.conj omegaP⁻¹).toMonoidHom :=
  centralizer_eq_conj_Cgen omegaP_mem omegaP_conj

theorem conj_mem_Cgen_of_comm_cbarP
    {x : SpaceB ≃ₗ[ℚ] SpaceB} (hx : x ∈ Gmat)
    (hxc : x * evalGL sletP = evalGL sletP * x) : omegaP * x * omegaP⁻¹ ∈ Cgen :=
  conj_mem_Cgen_of_comm omegaP_mem omegaP_conj hx hxc

theorem m_comm :
    wordLin mWord * wordLin omegaWord = wordLin omegaWord * wordLin rhoWord := by
  have h := p2_a.2.2.1
  rw [wordLin_append, wordLin_append] at h
  exact h

theorem mWord_eq :
    wordLin mWord = wordLin omegaWord * wordLin rhoWord * (wordLin omegaWord)⁻¹ :=
  eq_mul_inv_of_mul_eq m_comm

theorem mWord_mul_self :
    wordLin mWord * wordLin mWord = 1 := by
  rw [mWord_eq]
  calc wordLin omegaWord * wordLin rhoWord * (wordLin omegaWord)⁻¹ *
        (wordLin omegaWord * wordLin rhoWord * (wordLin omegaWord)⁻¹)
      = wordLin omegaWord * (wordLin rhoWord * wordLin rhoWord) * (wordLin omegaWord)⁻¹ := by
        group
    _ = 1 := by
        rw [rho_sq]
        group

theorem mWord_inv :
    (wordLin mWord)⁻¹ = wordLin mWord := inv_eq_of_mul_eq_one_right mWord_mul_self

theorem tStar_inv : tStar⁻¹ = tStar := inv_eq_of_mul_eq_one_right tStar_mul_self

theorem omega_conj_cbarP :
    wordLin omegaWord * evalGL sletP * (wordLin omegaWord)⁻¹ =
      wordLin mWord * tStar * wordLin mWord := by
  have e1 : wordLin omegaWord * (wordLin rhoWord)⁻¹ * (wordLin omegaWord)⁻¹ = wordLin mWord := by
    rw [rho_inv]
    exact mWord_eq.symm
  rw [← rho_conj_cbar]
  calc wordLin omegaWord * (wordLin rhoWord * evalGL slet * (wordLin rhoWord)⁻¹) *
        (wordLin omegaWord)⁻¹
      = (wordLin omegaWord * wordLin rhoWord * (wordLin omegaWord)⁻¹) *
        (wordLin omegaWord * evalGL slet * (wordLin omegaWord)⁻¹) *
        (wordLin omegaWord * (wordLin rhoWord)⁻¹ * (wordLin omegaWord)⁻¹) := by group
    _ = wordLin mWord * tStar * wordLin mWord := by rw [← mWord_eq, omega_conj_slet, e1]

theorem q_comm :
    wordLin qWord * (tStar * wordLin mWord * tStar * wordLin mWord) = tStar * wordLin qWord := by
  have h := p2_a.2.2.2
  rw [wordLin_append, wordLin_append, wordLin_tWord] at h
  have hz : wordLin zmWord = tStar * wordLin mWord * tStar * wordLin mWord := by
    simp only [zmWord, mtmWord, wordLin_append, wordLin_tWord, mul_assoc]
  rw [hz] at h
  exact h

theorem q_conj :
    wordLin qWord * (tStar * wordLin mWord * tStar * wordLin mWord) * (wordLin qWord)⁻¹ =
      tStar := by
  rw [q_comm, mul_assoc, mul_inv_cancel, mul_one]

theorem tm_sq :
    (tStar * wordLin mWord * tStar * wordLin mWord) *
      (tStar * wordLin mWord * tStar * wordLin mWord) = 1 := by
  rw [eq_conj_of_conj q_conj]
  calc (wordLin qWord)⁻¹ * tStar * wordLin qWord * ((wordLin qWord)⁻¹ * tStar * wordLin qWord)
      = (wordLin qWord)⁻¹ * (tStar * tStar) * wordLin qWord := by group
    _ = 1 := by
        rw [tStar_mul_self]
        group

theorem mtm_comm :
    tStar * (wordLin mWord * tStar * wordLin mWord) =
      (wordLin mWord * tStar * wordLin mWord) * tStar := by
  have hinv : (tStar * wordLin mWord * tStar * wordLin mWord)⁻¹ =
      wordLin mWord * tStar * wordLin mWord * tStar := by
    simp only [mul_inv_rev, tStar_inv, mWord_inv, mul_assoc]
  calc tStar * (wordLin mWord * tStar * wordLin mWord)
      = tStar * wordLin mWord * tStar * wordLin mWord := by group
    _ = (tStar * wordLin mWord * tStar * wordLin mWord)⁻¹ :=
        (inv_eq_of_mul_eq_one_right tm_sq).symm
    _ = wordLin mWord * tStar * wordLin mWord * tStar := hinv
    _ = (wordLin mWord * tStar * wordLin mWord) * tStar := by group

theorem cbar_comm_cbarP :
    evalGL slet * evalGL sletP = evalGL sletP * evalGL slet := by
  have e1 := eq_conj_of_conj omega_conj_slet
  have e2 := eq_conj_of_conj omega_conj_cbarP
  rw [e1, e2]
  calc (wordLin omegaWord)⁻¹ * tStar * wordLin omegaWord *
        ((wordLin omegaWord)⁻¹ * (wordLin mWord * tStar * wordLin mWord) * wordLin omegaWord)
      = (wordLin omegaWord)⁻¹ * (tStar * (wordLin mWord * tStar * wordLin mWord)) *
        wordLin omegaWord := by group
    _ = (wordLin omegaWord)⁻¹ * ((wordLin mWord * tStar * wordLin mWord) * tStar) *
        wordLin omegaWord := by rw [mtm_comm]
    _ = (wordLin omegaWord)⁻¹ * (wordLin mWord * tStar * wordLin mWord) * wordLin omegaWord *
        ((wordLin omegaWord)⁻¹ * tStar * wordLin omegaWord) := by group

theorem cbar_mul_cbarP_eq :
    evalGL slet * evalGL sletP =
      (wordLin omegaWord)⁻¹ * (tStar * wordLin mWord * tStar * wordLin mWord) *
        wordLin omegaWord := by
  rw [eq_conj_of_conj omega_conj_slet, eq_conj_of_conj omega_conj_cbarP]
  group

theorem omegaQ_conj :
    (wordLin qWord * wordLin omegaWord) * (evalGL slet * evalGL sletP) *
      (wordLin qWord * wordLin omegaWord)⁻¹ = tStar := by
  rw [cbar_mul_cbarP_eq]
  calc (wordLin qWord * wordLin omegaWord) *
        ((wordLin omegaWord)⁻¹ * (tStar * wordLin mWord * tStar * wordLin mWord) *
          wordLin omegaWord) * (wordLin qWord * wordLin omegaWord)⁻¹
      = wordLin qWord * (tStar * wordLin mWord * tStar * wordLin mWord) *
        (wordLin qWord)⁻¹ := by group
    _ = tStar := q_conj

theorem cbar_mul_cbarP_mem_shortClass :
    evalGL slet * evalGL sletP ∈ shortClass :=
  mem_shortClass_of_conj (mul_mem (wordLin_mem_Gmat _) (wordLin_mem_Gmat _)) omegaQ_conj

theorem centralizer_cbar_mul_cbarP_eq :
    Gmat ⊓ Subgroup.centralizer {evalGL slet * evalGL sletP} =
      Cgen.map (MulAut.conj (wordLin qWord * wordLin omegaWord)⁻¹).toMonoidHom :=
  centralizer_eq_conj_Cgen (mul_mem (wordLin_mem_Gmat _) (wordLin_mem_Gmat _)) omegaQ_conj

end CFSG.YGroups.Y443

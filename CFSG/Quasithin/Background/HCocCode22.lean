module

public import CFSG.Quasithin.Background.HCocBase
public import CFSG.Quasithin.Background.HZCode22B

public section

namespace CFSG.Quasithin.H.Code22

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc CFSG.Monster.B.TwoA CFSG.Quasithin.H.Mathieu.H16Pf

theorem mogA_mem22 : mogA ∈ mog22 :=
  ⟨⟨mogA_mem, (mem_stab_iff 0 _).2 rfl⟩, (mem_stab_iff 1 _).2 rfl⟩

theorem mogB_mem22 : mogB ∈ mog22 :=
  ⟨⟨mogB_mem, (mem_stab_iff 0 _).2 rfl⟩, (mem_stab_iff 1 _).2 rfl⟩

theorem mog22_eq_closure :
    mog22 = Subgroup.closure {mogA, mogB} := by
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 ?_)
  · rw [mog22_eq_map_P0]
    rintro _ ⟨p, hp, rfl⟩
    rw [← range_psiM] at hp
    obtain ⟨g, rfl⟩ := hp
    change psiHom g ∈ _
    have hg : (g : Equiv.Perm (Fin 22)) ∈
        Subgroup.closure ({CFSG.Sporadic.Mathieu.m22gA, CFSG.Sporadic.Mathieu.m22gB} :
          Set (Equiv.Perm (Fin 22))) := by
      rw [← CFSG.Sporadic.Mathieu.m22_eq]
      exact g.2
    have h := Subgroup.mem_map_of_mem psiHom hg
    rw [MonoidHom.map_closure, Set.image_pair, psi_m22gA, psi_m22gB] at h
    exact h
  · rintro _ (rfl | rfl)
    · exact mogA_mem22
    · exact mogB_mem22

@[expose] def mogAArr : Array ℕ :=
  #[0, 1, 10, 13, 11, 12, 6, 7, 16, 23, 2, 4, 5, 3, 17, 22, 8, 14, 18, 19, 20, 21, 15, 9]

@[expose] def mogBArr : Array ℕ :=
  #[0, 1, 15, 6, 18, 13, 16, 5, 21, 17, 3, 11, 12, 23, 20, 4, 10, 19, 2, 22, 14, 8, 9, 7]

theorem hasArr_mogA : HasArr mogA mogAArr := by
  unfold HasArr
  decide +kernel

theorem hasArr_mogB : HasArr mogB mogBArr := by
  unfold HasArr
  decide +kernel

@[expose] def c22A : List ℕ := [340, 569, 608, 530, 768, 373, 64, 500, 289, 305]

@[expose] def c22B : List ℕ := [216, 928, 154, 688, 108, 807, 324, 417, 734, 963]

@[expose] def c22Cons : List (Option ℕ × List ℕ × List ℕ) :=
  [(none, [0, 0], [100608, 705256, 421408, 0, 233216, 0, 0, 0, 0, 0]),
    (none, [1, 1, 1, 1], [519584, 0, 0, 362496, 0, 0, 0, 0, 0, 0]),
    (some 3, [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1],
      [0, 747584, 240704, 434240, 183712, 0, 0, 0, 534528, 0]),
    (some 7, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0],
      [0, 851968, 0, 0, 0, 0, 0, 0, 609280, 0]),
    (some 15, [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
      [0, 0, 0, 0, 0, 0, 0, 0, 212992, 0]),
    (some 11, [1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0],
      [0, 0, 0, 0, 411648, 0, 0, 0, 0, 0])]

@[expose] def c22Phi : List ℕ := [13, 3, 17, 0, 20, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]

theorem c22A_eq : matOf 10 (actC10 mogAArr) = c22A := by
  decide +kernel

theorem c22B_eq : matOf 10 (actC10 mogBArr) = c22B := by
  decide +kernel

theorem c22_lt : ∀ c ∈ c22A ++ c22B, c < 2 ^ 10 := by
  decide +kernel

theorem c22_ok :
    consOK 10 16 [c22A, c22B] (fun t => matOf 10 (actC10 (koArr t))) c22Cons = true := by
  decide +kernel

theorem c22_cert :
    matOf (2 * 10) (fun v => v ^^^ actM (w0Basis.map (packB 10 c22A c22B)) (actM c22Phi v)) =
      matOf (2 * 10) (conSum [c22A, c22B] 10 0 1 c22Cons) := by
  decide +kernel

@[expose] noncomputable def cRhoA : MulAut W10 :=
  rhoC10 mog22 mog22_le_mog22plus ⟨mogA, mogA_mem22⟩

@[expose] noncomputable def cRhoB : MulAut W10 :=
  rhoC10 mog22 mog22_le_mog22plus ⟨mogB, mogB_mem22⟩

theorem actsBy_cRhoA : ActsBy cRhoA c22A := by
  rw [← c22A_eq]
  exact actsBy_of_xorLin (xorLin_actC10 mogAArr)
    (rhoC10_toW mog22 mog22_le_mog22plus _ hasArr_mogA)

theorem actsBy_cRhoB : ActsBy cRhoB c22B := by
  rw [← c22B_eq]
  exact actsBy_of_xorLin (xorLin_actC10 mogBArr)
    (rhoC10_toW mog22 mog22_le_mog22plus _ hasArr_mogB)

theorem imgC_le_closure :
    imgC mog22 ≤ Subgroup.closure {cRhoA, cRhoB} := by
  rw [← range_rhoC10_eq_imgC, MonoidHom.range_eq_map,
    ← CFSG.Sporadic.Mathieu.closure_pair_eq_top mog22_eq_closure mogA_mem22 mogB_mem22,
    MonoidHom.map_closure, Set.image_pair]
  rfl

theorem ko_tgt (t : ℕ) (ht : t < 16) :
    ∃ ρ ∈ imgC fixO, ActsBy ρ (matOf 10 (actC10 (koArr t))) :=
  ⟨koRho ⟨t, ht⟩, koRho_mem_imgC_fixO _, actsBy_of_xorLin (xorLin_actC10 _) (koRho_toW _)⟩

theorem coc_std
    {δ : MulAut W10 → W10}
    (hδ : ∀ g ∈ imgC mog22, ∀ k ∈ imgC mog22, δ (g * k) = δ g * g (δ k))
    (hR : ∀ r ∈ radZ (imgC mog22) z0, δ r ∈ Subgroup.zpowers z0) :
    ∃ w ∈ vZ (imgC mog22) z0, ∀ g ∈ imgC mog22, δ g = w * (g w)⁻¹ := by
  rw [radZ_std] at hR
  rw [vZ_std]
  obtain ⟨m, hm, h⟩ := eq_inner_std hδ (p := 0) (z := 1) hR (by norm_num) (by decide)
    imgC_le_closure (rhoC10_mem_imgC _) (rhoC10_mem_imgC _) actsBy_cRhoA actsBy_cRhoB c22_lt
    ko_tgt c22_ok w0_lt c22_cert
  exact ⟨toW 10 m, toW_mem_maskSub hm, h⟩

theorem coc_of_code22
    {V : Type} [CommGroup V]
    [Finite V] {H : Subgroup (MulAut V)} (h : MathieuCode22 H ⊤ ⊥) {z : V} (hz1 : z ≠ 1)
    {S : Subgroup (MulAut V)} (hSH : S ≤ H) (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2)
    (hzS : z ∈ fixV S) {δ : MulAut V → V} (hδ : ∀ g ∈ H, ∀ k ∈ H, δ (g * k) = δ g * g (δ k))
    (hR : ∀ r ∈ radZ H z, δ r ∈ Subgroup.zpowers z) :
    ∃ w ∈ vZ H z, ∀ g ∈ H, δ g = w * (g w)⁻¹ := by
  obtain ⟨e, he, hez⟩ := exists_equiv_z0 h hz1 hSH hS hzS
  refine coc_of_map e hδ hR fun δ₀ hδ₀ hR₀ => ?_
  have key : ∀ (A : Subgroup (MulAut W10)) (w : W10), A = imgC mog22 → w = z0 →
      ∀ δ₀ : MulAut W10 → W10, (∀ g ∈ A, ∀ k ∈ A, δ₀ (g * k) = δ₀ g * g (δ₀ k)) →
        (∀ r ∈ radZ A w, δ₀ r ∈ Subgroup.zpowers w) →
          ∃ w' ∈ vZ A w, ∀ g ∈ A, δ₀ g = w' * (g w')⁻¹ := by
    rintro A w rfl rfl δ₀ hδ₀ hR₀
    exact coc_std hδ₀ hR₀
  exact key _ _ he hez δ₀ hδ₀ hR₀

end CFSG.Quasithin.H.Code22

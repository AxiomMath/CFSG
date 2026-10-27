module

public import CFSG.Quasithin.Vol2.Ch10SecD33H
public import CFSG.Quasithin.Vol2.Ch10SecD33E

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem not_isSolvable_symFiveWrTwo : ¬ Group.IsSolvable SymFiveWrTwo := by
  intro hs
  let f : Equiv.Perm (Fin 5) →* SymFiveWrTwo :=
    { toFun := fun g => ⟨fun _ => g, 1⟩
      map_one' := rfl
      map_mul' := fun a b => by
        refine RegularWreathProduct.ext ?_ ?_
        · funext x
          rfl
        · exact (one_mul 1).symm }
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg (fun w : SymFiveWrTwo => w.left 1) hab
    exact this
  exact Equiv.Perm.not_isSolvable_fin_5 (Group.isSolvable_of_isSolvable_injective hf)

theorem le_of_case_two
    (hW : FactSymFiveWrTwo) (hA : FactPSL2NormA5) (hK : LocalSQTK G)
    (h37 : Vol2Native.A37ForSQTKCat) {X K₁ H T : Subgroup G} (hX : pCoreOf 2 X ≠ ⊥)
    (hK₁ : K₁ ∈ cComp X) {s : G} (hs : s ∈ T) (hsn : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hTK : T ≤ Subgroup.normalizer ((K₁ ⊔ CFSG.conjugate K₁ s : Subgroup G) : Set G))
    (hT : IsSylowTwoOf T X) (hTH : T ≤ H) (hHX : H ≤ X)
    (hO : oTwoUpper H ≤ K₁ ⊔ CFSG.conjugate K₁ s) (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* SymFiveWrTwo)
    (htype : (∃ m : ℕ, 0 < m ∧ Even m ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = 2 ^ m ∧
        Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p))) :
    K₁ ≤ H := by
  have hsX : s ∈ X := hT.1 hs
  have hTsH : IsSylowTwoOf T H := A4.isSylowTwoOf_mono hT hTH hHX
  have hHns : ¬ Group.IsSolvable ↥H := fun hs' =>
    not_isSolvable_symFiveWrTwo (Group.isSolvable_of_surjective
      (f := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _)))
  have hP := not_isSolvable_barSub_proj hK h37 hX hK₁ hsX hsn (hTK hs) hTsH (hTH hs) hO hHns
  set P := barSub K₁ (K₁ ⊓ ((H ⊓ (K₁ ⊔ CFSG.conjugate K₁ s)) ⊔ CFSG.conjugate K₁ s)) with hPdef
  obtain ⟨U, hU⟩ := exists_sylow_barSub hK₁ hT
  have hUP : (U : Subgroup _) ≤ P := by
    rw [hU]
    refine Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      ⟨(Subgroup.mem_subgroupOf.mp hx).2, Subgroup.mem_sup_left ⟨hTH (Subgroup.mem_subgroupOf.mp
        hx).1, Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx).2⟩⟩
  have htop : ∀ {Y : Type} [Group Y] (φ : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Y),
      P.map φ.toMonoidHom = ⊤ → P = ⊤ := fun φ h => by
    rw [eq_top_iff]
    intro x _
    have hx : φ x ∈ P.map φ.toMonoidHom := by rw [h]; trivial
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← φ.injective hyx]
    exact hy
  have hPφ : ∀ {Y : Type} [Group Y] (φ : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Y),
      ¬ Group.IsSolvable ↥(P.map φ.toMonoidHom) := fun φ h =>
    hP (CFSG.Walter.isSolvable_map_mulEquiv φ P h)
  have hfinish : IsSimpleGroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) →
      2 ∣ Nat.card (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) → P = ⊤ → K₁ ≤ H := fun hsimp heven hPt =>
    le_of_barSub_proj_eq_top hK h37 hX hK₁ hsX hsn hT hTH hsimp heven hPt
  rcases htype with ⟨m, hm0, hmev, F, _, _, hF, ⟨φ⟩⟩ | ⟨p, hp, hp2, ⟨φ⟩⟩
  ·
    have hm : 2 ≤ m := by obtain ⟨k, hk⟩ := hmev; omega
    refine hfinish (isSimpleGroup_of_sl2 φ hm hF) (two_dvd_card_of_sl2 φ (by omega) hF)
      (htop φ ?_)
    exact sl2_eq_top_of_sylow_le hm hF (U.mapSurjective (f := φ.toMonoidHom) φ.surjective)
      (Subgroup.map_mono hUP) (hPφ φ)
  · have : Fact p.Prime := ⟨hp⟩
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    by_cases hp3' : p = 3
    ·
      exfalso
      subst hp3'
      have hsol : Group.IsSolvable ↥(barSub K₁ K₁) := by
        have := isSolvable_psl2_three
        have : Group.IsSolvable (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) :=
          Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
        infer_instance
      exact not_isSolvable_of_mem_cComp hK₁ (isSolvable_of_barSub le_rfl hsol)
    have hp5 : 5 ≤ p := by
      have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by decide)
      omega
    rcases psl2_prime_eq_top_or_alt5 hp5 (hPφ φ) with htop' | heA
    · exact hfinish (isSimpleGroup_of_psl2 hp5 φ) (two_dvd_card_of_psl2 hp2 φ) (htop φ htop')
    · obtain ⟨eA⟩ := heA
      by_cases hp5' : p = 5
      ·
        subst hp5'
        refine hfinish (isSimpleGroup_of_psl2 le_rfl φ) (two_dvd_card_of_psl2 hp2 φ)
          (htop φ ?_)
        apply Subgroup.eq_top_of_card_eq
        have hFc : Nat.card (ZMod 5) = 5 ^ 1 := by rw [Nat.card_zmod, pow_one]
        have hcard := CFSG.GorensteinWalter.psl2_card_formula (ZMod 5)
          (CFSG.Walter.isOddPrimePower_of_card hFc (by decide) one_pos)
        rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin, hcard,
          Nat.card_zmod]
        decide
      ·
        exfalso
        have hp7 : 7 ≤ p := by
          have h6 : p ≠ 6 := fun h => by rw [h] at hp; exact absurd hp (by decide)
          omega
        have eP : ↥P ≃* alternatingGroup (Fin 5) :=
          (P.equivMapOfInjective φ.toMonoidHom φ.injective).trans eA
        have : Nontrivial ↥P := eP.toEquiv.nontrivial
        have hPs : IsSimpleGroup ↥P :=
          IsSimpleGroup.isSimpleGroup_of_surjective eP.symm.toMonoidHom eP.symm.surjective
        have hAP : barSub K₁ (H ⊓ K₁) ≤ P := Subgroup.map_mono fun x hx =>
          Subgroup.mem_subgroupOf.mpr ⟨(Subgroup.mem_subgroupOf.mp hx).2,
            Subgroup.mem_sup_left ⟨(Subgroup.mem_subgroupOf.mp hx).1,
              Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx).2⟩⟩
        have hUA : (U : Subgroup _) ≤ barSub K₁ (H ⊓ K₁) := by
          rw [hU]
          exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
            ⟨hTH (Subgroup.mem_subgroupOf.mp hx).1, (Subgroup.mem_subgroupOf.mp hx).2⟩
        have hN : ((barSub K₁ (H ⊓ K₁)).subgroupOf P).Normal := ⟨fun a ha g => by
          rw [Subgroup.mem_subgroupOf] at ha ⊢
          exact conj_mem_barSub_inf hK h37 hX hK₁ hsX hsn g.2 ha⟩
        have hAeq : barSub K₁ (H ⊓ K₁) = P := by
          rcases hN.eq_bot_or_eq_top with hbot | htopN
          · exfalso
            apply Sylow.ne_bot_of_dvd_card U (two_dvd_card_of_psl2 hp2 φ)
            rw [eq_bot_iff]
            intro x hx
            have hxP : x ∈ P := hUP hx
            have : (⟨x, hxP⟩ : ↥P) ∈ (barSub K₁ (H ⊓ K₁)).subgroupOf P :=
              Subgroup.mem_subgroupOf.mpr (hUA hx)
            rw [hbot, Subgroup.mem_bot] at this
            rw [Subgroup.mem_bot]
            exact congrArg Subtype.val this
          · refine le_antisymm hAP fun x hx => ?_
            have : (⟨x, hx⟩ : ↥P) ∈ (barSub K₁ (H ⊓ K₁)).subgroupOf P := by
              rw [htopN]
              trivial
            exact Subgroup.mem_subgroupOf.mp this
        have hA5 : Nonempty (↥(barSub K₁ (H ⊓ K₁)) ≃* alternatingGroup (Fin 5)) :=
          ⟨(MulEquiv.subgroupCongr hAeq).trans eP⟩
        exact false_of_alt5 hW hA hK h37 hX hK₁ hs hTK hT hTH hHX hO e hp7 φ hA5

omit [Finite G] in
theorem nonempty_quot_equiv_of_eq {W : Type} [Group W] {A B : Subgroup G} (h : A = B)
    (e : Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* W)) : Nonempty (↥A ⧸ CFSG.pCore 2 ↥A ≃* W) := by
  subst h
  exact e

theorem stmt10_3_3_of
    (hW : FactSymFiveWrTwo) (hA : FactPSL2NormA5) (hAut : FactAutSL)
    (hMax : FactMaxP) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1023 : Stmt10_2_3) (h1024 : Stmt10_2_4) (h10213 : Stmt10_2_13) (h1031 : Stmt10_3_1)
    (h1032 : Stmt10_3_2) : Stmt10_3_3 := by
  intro G _ _ T L I h t v₁ v₂ hd
  have h3 := (h10213 G T L I h).1
  have hc := (h1031 G T L I h).1
  have := h.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1
  obtain ⟨H, hH, hHz, hO, hHK, ⟨e⟩⟩ := exists_isHStar_le_KzT hW h37 h38 h1023 h10213 h1032 h
    h3 hc hd
  have hTz := T_le_centralizer_z h37 h38 h h3 hc hd
  have hT : IsSylowTwoOf T (Subgroup.centralizer ({v₁ * v₂} : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTz
  have hX := pCoreOf_Gz_ne_bot h37 h38 h hc hd
  have hGzK : Subgroup.centralizer ({v₁ * v₂} : Set G) ≤
      Subgroup.normalizer (Kz T L (v₁ * v₂) : Set G) := le_normalizer_conjClosure _ _
  rcases concl10_2_4_Kz hW h37 h38 h1023 h1024 h10213 h1032 hMax h h3 hc hd with
    ⟨K₁, s, hs, hK₁, hsn, hKz, htype⟩ | ⟨-, k, hk, ⟨eA⟩⟩
  · have hTK : T ≤ Subgroup.normalizer ((K₁ ⊔ CFSG.conjugate K₁ s : Subgroup G) : Set G) := by
      rw [← hKz]
      exact hTz.trans hGzK
    have hK1H : K₁ ≤ H := le_of_case_two hW hA hK h37 hX hK₁ hs hsn hTK hT hH.1.1 hHz
      (hKz ▸ hO) e htype
    have hK2H : CFSG.conjugate K₁ s ≤ H := by
      intro x hx
      rw [SecA.mem_conjugate_iff] at hx
      have e1 : x = s⁻¹ * (s * x * s⁻¹) * s := by group
      rw [e1]
      exact H.mul_mem (H.mul_mem (H.inv_mem (hH.1.1 hs)) (hK1H hx)) (hH.1.1 hs)
    have heq : Kz T L (v₁ * v₂) ⊔ T = H :=
      le_antisymm (sup_le (hKz ▸ sup_le hK1H hK2H) hH.1.1) hHK
    exact nonempty_quot_equiv_of_eq heq ⟨e⟩
  · exact (not_case_three_Kz hW hAut h37 h38 h1023 h10213 h1032 h h3 hc hd k hk eA).elim

end CFSG.Quasithin.Vol2.Ch10.SecD

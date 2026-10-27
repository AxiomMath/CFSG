module

public import CFSG.LocalAnalysis.WeakClosure81.W16LPU3StdPsu
public import CFSG.LocalAnalysis.WeakClosure81.W16LPU3StdQA
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenKFacts

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.CGT.PushingUpLit.CGT6
open CFSG.Open
open scoped MatrixGroups

section Certified


private theorem w16l_quasithin_conjSubgroup_eq {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    CFSG.Quasithin.conjSubgroup A g = CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ A := rfl

theorem w16l_exists_conj_eq_map_Sig01_Q {Q : Type} [Group Q] [Finite Q] {n : ℕ}
    (hX : IsU3Shape Q n) {F : Type} [Field F] (h : UnitaryFieldData 2 n F)
    (π : ↥(unitarySU 2 n F 3) →* Q) (ε : (Q ⧸ Subgroup.center Q) ≃* unitaryPSU h 3)
    (hπ : Function.Surjective π) (hε : ∀ g, ε (QuotientGroup.mk (π g)) = unitaryProj h 3 g)
    {R : Subgroup Q} (hR : IsElemAbelian 2 R) (hRc : Nat.card R = 2 ^ n) {g : Q}
    (hg : CFSG.Quasithin.conjSubgroup R g ≠ R) :
    ∃ k : Q, CFSG.Quasithin.conjSubgroup (R ⊔ CFSG.Quasithin.conjSubgroup R g) k =
      (Sig01 h).map π := by
  classical
  haveI : Finite F := h.finite
  have hn : 2 ≤ n := two_le_of_isPSUGp hX.2.1
  have hn1 : 1 < n := by omega
  have hK : KGroup1616Input := kGroup1616Input_holds
  set ρ : Q →* unitaryPSU h 3 :=
    ε.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q)) with hρdef
  have hker_eq : ρ.ker = Subgroup.center Q := by
    rw [hρdef, MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center Q))
      ε.toMonoidHom ε.injective]
    exact QuotientGroup.ker_mk' (Subgroup.center Q)
  have hker : ρ.ker ≤ Subgroup.center Q := le_of_eq hker_eq
  have hρsurj : Function.Surjective ρ := by
    rw [hρdef]
    intro y
    obtain ⟨z, hz⟩ := ε.surjective y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) z
    exact ⟨w, by simpa using hz⟩
  have hoddk : Odd (Nat.card ρ.ker) := by
    rw [hker_eq]
    exact Odd.of_dvd_nat (by norm_num) hX.2.2
  have hρπ : ρ.comp π = unitaryProj h 3 := by
    ext y
    simpa [MonoidHom.comp_apply, hρdef] using hε y
  obtain ⟨S₁, hS₁⟩ := exists_sylow_center_eq hK hn1 hX hR hRc
  obtain ⟨S, hS⟩ := w16l_exists_sylow_cenS_eq_map ρ hρsurj hoddk S₁
  set T : Subgroup (unitaryPSU h 3) := R.map ρ with hTdef
  have hTcen : T = cenS S := by
    rw [hTdef, hS₁, hS]
  have hTmem : ∃ S' : Sylow 2 (unitaryPSU h 3), T = cenS S' := ⟨S, hTcen⟩
  have hTconj : CFSG.CGT.Timmesfeld75.conjSubgroup (ρ g⁻¹) T =
      (CFSG.Quasithin.conjSubgroup R g).map ρ := by
    rw [hTdef, ← CFSG.CGT.Timmesfeld75.map_conjSubgroup ρ g⁻¹ R,
      w16l_quasithin_conjSubgroup_eq R g]
  have hne : CFSG.CGT.Timmesfeld75.conjSubgroup (ρ g⁻¹) T ≠ T := by
    intro heq
    have hconjmap : (CFSG.Quasithin.conjSubgroup R g).map ρ = R.map ρ := by
      rw [← hTconj, heq, hTdef]
    have hle : CFSG.Quasithin.conjSubgroup R g ≤ R := by
      intro y hy
      have hRg : IsElemAbelian 2 (CFSG.Quasithin.conjSubgroup R g) :=
        hR.map (MulAut.conj g⁻¹).toMonoidHom
      have hy2 : y * y = 1 := by
        have h := hRg.2 y hy
        rwa [pow_two] at h
      have hρy : ρ y ∈ R.map ρ := by
        rw [← hconjmap]
        exact Subgroup.mem_map_of_mem ρ hy
      exact w16l_mem_of_sq_eq_one_of_map_mem ρ hker hoddk hy2 hρy
    have hcard : Nat.card (CFSG.Quasithin.conjSubgroup R g) = Nat.card R := by
      rw [w16l_quasithin_conjSubgroup_eq R g]
      exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    exact hg (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm))
  have hcardL : Nat.card ↥(T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup (ρ g⁻¹) T) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    have hsup : T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup (ρ g⁻¹) T =
        (R ⊔ CFSG.Quasithin.conjSubgroup R g).map ρ := by
      rw [hTconj, hTdef, ← Subgroup.map_sup]
    rw [hsup]
    exact w16l_card_map_sup_root ρ hker hX hR hRc hg
  obtain ⟨xbar, hbar⟩ :=
    w16l_exists_conj_eq_map_Sig01 h hn hTmem (g := ρ g⁻¹) hne hcardL
  obtain ⟨x, hx⟩ := hρsurj xbar
  refine ⟨x⁻¹, ?_⟩
  set L : Subgroup Q := R ⊔ CFSG.Quasithin.conjSubgroup R g with hLdef
  set N : Subgroup Q := (Sig01 h).map π with hNdef
  have hmap : (CFSG.Quasithin.conjSubgroup L x⁻¹).map ρ = N.map ρ := by
    have hLmap : L.map ρ = T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup (ρ g⁻¹) T := by
      rw [hLdef, Subgroup.map_sup, hTconj, hTdef]
    calc
      (CFSG.Quasithin.conjSubgroup L x⁻¹).map ρ
          = (CFSG.CGT.Timmesfeld75.conjSubgroup x L).map ρ := by
              rw [w16l_quasithin_conjSubgroup_eq L x⁻¹, inv_inv]
      _ = CFSG.CGT.Timmesfeld75.conjSubgroup (ρ x) (L.map ρ) :=
              CFSG.CGT.Timmesfeld75.map_conjSubgroup ρ x L
      _ = CFSG.CGT.Timmesfeld75.conjSubgroup xbar
            (T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup (ρ g⁻¹) T) := by rw [hx, hLmap]
      _ = (Sig01 h).map (unitaryProj h 3) := hbar
      _ = N.map ρ := by rw [hNdef, Subgroup.map_map, hρπ]
  have hle : CFSG.Quasithin.conjSubgroup L x⁻¹ ≤ N := by
    have hLsup : CFSG.Quasithin.conjSubgroup L x⁻¹ =
        CFSG.Quasithin.conjSubgroup R x⁻¹ ⊔
          CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.conjSubgroup R g) x⁻¹ := by
      rw [hLdef]
      simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_sup]
    have hA : IsElemAbelian 2 (CFSG.Quasithin.conjSubgroup R x⁻¹) :=
      hR.map (MulAut.conj (x⁻¹)⁻¹).toMonoidHom
    have hB : IsElemAbelian 2
        (CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.conjSubgroup R g) x⁻¹) :=
      (hR.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj (x⁻¹)⁻¹).toMonoidHom
    have hAle : CFSG.Quasithin.conjSubgroup R x⁻¹ ≤ N := by
      intro y hy
      have hy2 : y * y = 1 := by
        have h := hA.2 y hy
        rwa [pow_two] at h
      have hρy : ρ y ∈ N.map ρ := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem ρ
          (Subgroup.map_mono (f := (MulAut.conj (x⁻¹)⁻¹).toMonoidHom) le_sup_left hy)
      exact w16l_mem_of_sq_eq_one_of_map_mem ρ hker hoddk hy2 hρy
    have hBle : CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.conjSubgroup R g) x⁻¹ ≤ N := by
      intro y hy
      have hy2 : y * y = 1 := by
        have h := hB.2 y hy
        rwa [pow_two] at h
      have hρy : ρ y ∈ N.map ρ := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem ρ
          (Subgroup.map_mono (f := (MulAut.conj (x⁻¹)⁻¹).toMonoidHom) le_sup_right hy)
      exact w16l_mem_of_sq_eq_one_of_map_mem ρ hker hoddk hy2 hρy
    rw [hLsup]
    exact sup_le hAle hBle
  have hNle : Nat.card N ≤ Nat.card (Sig01 h) := by
    rw [hNdef]
    refine Nat.card_le_card_of_surjective
      (fun y : ↥(Sig01 h) => (⟨π y, Subgroup.mem_map_of_mem π y.2⟩ :
        ↥((Sig01 h).map π))) ?_
    rintro ⟨z, hz⟩
    rw [Subgroup.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨⟨y, hy⟩, rfl⟩
  have hLimg_le : Nat.card (L.map ρ) ≤ Nat.card L := by
    refine Nat.card_le_card_of_surjective
      (fun y : ↥L => (⟨ρ y, Subgroup.mem_map_of_mem ρ y.2⟩ : ↥(L.map ρ))) ?_
    rintro ⟨z, hz⟩
    rw [Subgroup.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨⟨y, hy⟩, rfl⟩
  have hcard_ge : Nat.card N ≤ Nat.card (CFSG.Quasithin.conjSubgroup L x⁻¹) := by
    have hLimg : Nat.card (L.map ρ) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [hLdef]
      exact w16l_card_map_sup_root ρ hker hX hR hRc hg
    have hconj : Nat.card (CFSG.Quasithin.conjSubgroup L x⁻¹) = Nat.card L := by
      rw [CFSG.Quasithin.conjSubgroup]
      exact Subgroup.card_map_of_injective (MulAut.conj (x⁻¹)⁻¹).injective
    calc
      Nat.card N ≤ Nat.card (Sig01 h) := hNle
      _ = 2 ^ n * ((2 ^ n) ^ 2 - 1) := card_Sig01 h
      _ = Nat.card (L.map ρ) := hLimg.symm
      _ ≤ Nat.card L := hLimg_le
      _ = Nat.card (CFSG.Quasithin.conjSubgroup L x⁻¹) := hconj.symm
  exact Subgroup.eq_of_le_of_card_ge hle hcard_ge

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end

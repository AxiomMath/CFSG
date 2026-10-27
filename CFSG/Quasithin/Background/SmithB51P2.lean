module

public import CFSG.Quasithin.Background.SmithB51P2L3
public import CFSG.Quasithin.Background.B5Part1
public import CFSG.Quasithin.H13.VolII16
public import CFSG.Quasithin.Background.B5FinS8Core
public import CFSG.Quasithin.SteinbergCBI16Alt5
public import CFSG.Quasithin.SteinbergCBI16Alt7

public section

namespace CFSG.Quasithin.B5

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank

namespace P2

variable {V : Type} [CommGroup V]

theorem commV_inv (L : Subgroup (MulAut V)) : ∀ g ∈ L, ∀ w ∈ commV L, g w ∈ commV L :=
  FFC.commV_invariant_self L

theorem isIntDirect_of_h1 [Finite V] {L : Subgroup (MulAut V)}
    (hH1 : ∀ f ∈ Z1A (FFC.muW (commV_inv L)), f ∈ B1A (FFC.muW (commV_inv L)))
    (hfix : fixV L ⊓ commV L = ⊥) : IsIntDirect (commV L) (fixV L) ⊤ :=
  ⟨FFC.sup_fixV_eq_top_of_h1 (commV_inv L)
    (fun g hg v => Subgroup.subset_closure ⟨g, hg, v, rfl⟩) hH1, by rw [inf_comm]; exact hfix⟩

theorem alternatingNatural_eight {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : SLExteriorTwo H U Z 4) : AlternatingNatural H U Z 8 := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨π.comp B5FinS8.alpha, FFModel.RealizesVia.of_surjHom (FFModel.altDn_isActionModel 8) hπ
    B5FinS8.alpha B5FinS8.alpha_surjective B5FinS8.ehat8 B5FinS8.ehat8_surjective
    (fun σ m _ => B5FinS8.qHom_alt σ m.1 m.2) (fun m => B5FinS8.ehat8_ker m)⟩

theorem card_ne_one_of_field {K : Type} [Field K] [Finite K] : Nat.card K ≠ 1 :=
  (Finite.one_lt_card (α := K)).ne'

theorem case_i [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} (hirr : commV L ∈ IrrPlus L ⊤)
    (hB42 : B42ModulePair L (commV L) (fixV L ⊓ commV L))
    (hnd : ¬ IsIntDirect (commV L) (fixV L) ⊤) :
    B51NaturalList2 L (commV L) (fixV L ⊓ commV L) := by
  have hcov := (H13.VolI.asI16Cover328_holds V hV L hirr).1
  have hLU := commV_inv L
  rcases hB42 with h2 | ⟨n, h3⟩ | hSp | hG2 | hG2' | h5 | h6 | h7 | hA7 | h36 | h4 | h5' |
    hE4 | hE5
  · exact Or.inl h2
  ·
    rcases Nat.lt_trichotomy n 1 with hn | rfl | hn
    · exfalso
      obtain ⟨K, _, _, hK, -⟩ := h3
      have hn0 : n = 0 := by omega
      rw [hn0, pow_zero] at hK
      exact card_ne_one_of_field hK
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h3)))))
    · exfalso
      have hZ := hcov (Or.inr (Or.inr (Or.inl ⟨n, hn, h3⟩)))
      rw [hZ] at h3
      obtain ⟨K, _, _, hK, hR⟩ := h3
      exact hnd (isIntDirect_of_h1 (FFC.natural_h1_vanish hK hn hLU hR) hZ)
  · exact Or.inr (Or.inl hSp)
  · exact Or.inr (Or.inr (Or.inl hG2))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hG2')))))
  ·
    exfalso
    have hZ := hcov (Or.inl h5)
    rw [hZ] at h5
    obtain ⟨π, hπ⟩ := h5
    exact hnd (isIntDirect_of_h1
      (h1_altDn SteinbergCB.I16.coords5 SteinbergCB.I16.Z1A_le_B1A_5 hLU hπ) hZ)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h6)))
  ·
    exfalso
    have hZ := hcov (Or.inr (Or.inl h7))
    rw [hZ] at h7
    obtain ⟨π, hπ⟩ := h7
    exact hnd (isIntDirect_of_h1
      (h1_altDn SteinbergCB.I16.coords7 SteinbergCB.I16.Z1A_le_B1A_7 hLU hπ) hZ)
  ·
    exfalso
    have hZ := hcov (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hA7)))))))
    rw [hZ] at hA7
    obtain ⟨α, π, hπ⟩ := hA7
    exact hnd (isIntDirect_of_h1 (h1_a7Four hLU hπ) hZ)
  ·
    exfalso
    have hZ := hcov (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h36)))))))
    rw [hZ] at h36
    exact hnd (isIntDirect_of_h1 (h1_tripleA6Six hLU h36) hZ)
  ·
    exfalso
    have hZ := hcov (Or.inr (Or.inr (Or.inr (Or.inl h4))))
    rw [hZ] at h4
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h4
    exact hnd (isIntDirect_of_h1 (h1_nat (Or.inl rfl) hLU hπ) hZ)
  ·
    exfalso
    have hZ := hcov (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5')))))
    rw [hZ] at h5'
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h5'
    exact hnd (isIntDirect_of_h1 (h1_nat (Or.inr rfl) hLU hπ) hZ)
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (alternatingNatural_eight hE4)))))
  ·
    exfalso
    have hZ := hcov (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE5))))))
    rw [hZ] at hE5
    obtain ⟨π, hπ⟩ := hE5
    exact hnd (isIntDirect_of_h1 (h1_wedge hLU hπ) hZ)

theorem case_ii [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L : Subgroup (MulAut V)} (h : B51Hyp G L) (hii : B51Case1ii G L) :
    IsIntDirect (commV L) (fixV L) ⊤ := by
  obtain ⟨hGL, n, K, _, _, hK, I, π, hind, hsup, hreal, -, -⟩ := hii
  have hLI : ∀ i, ∀ g ∈ L, ∀ w ∈ I i, g w ∈ I i := fun i g hg w hw =>
    (hreal i).2.2.2.1 ⟨g, hg⟩ w hw
  have h01 : I 0 ⊓ I 1 = ⊥ := (hind.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1)).eq_bot
  have hsup01 : I 0 ⊔ I 1 = commV L := by
    rw [← hsup]
    refine le_antisymm (sup_le (le_iSup I 0) (le_iSup I 1)) (iSup_le fun i => ?_)
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hfix : fixV L ⊓ commV L = ⊥ := by
    rw [← hsup01]
    exact fixV_inf_sup h01 (hLI 0) (hLI 1) (fixV_inf_nat (by norm_num) (hreal 0))
      (fixV_inf_nat (by norm_num) (hreal 1))
  rcases Nat.lt_trichotomy n 1 with hn | rfl | hn
  · exfalso
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hK
    exact card_ne_one_of_field hK
  · exact ⟨sup_fixV_eq_top_L3 hV h hGL hK h01 hsup01 (hreal 0) (hreal 1),
      by rw [inf_comm]; exact hfix⟩
  · exact isIntDirect_of_h1 (h1_sup h01 hsup01 (hLI 0) (hLI 1) (commV_inv L)
      (FFC.natural_h1_vanish hK hn (hLI 0) ⟨π, hreal 0⟩)
      (FFC.natural_h1_vanish hK hn (hLI 1) ⟨π, hreal 1⟩)) hfix

theorem case_iii [Finite V] {G L : Subgroup (MulAut V)} {n : ℕ}
    (hiii : B51Case1iii G L n) : IsIntDirect (commV L) (fixV L) ⊤ := by
  obtain ⟨-, hn, π, U₁, U₂, ⟨hsup, h12⟩, h₁, h₂⟩ := hiii
  have hL₁ : ∀ g ∈ L, ∀ w ∈ U₁, g w ∈ U₁ := fun g hg w hw => h₁.2.2.2.1 ⟨g, hg⟩ w hw
  have hL₂ : ∀ g ∈ L, ∀ w ∈ U₂, g w ∈ U₂ := fun g hg w hw => h₂.2.2.2.1 ⟨g, hg⟩ w hw
  have hn2 : 2 ≤ n := by omega
  have hfix : fixV L ⊓ commV L = ⊥ := by
    rw [← hsup]
    exact fixV_inf_sup h12 hL₁ hL₂ (fixV_inf_nat hn2 h₁) (fixV_inf_dualNat hn2 h₂)
  exact isIntDirect_of_h1 (h1_sup h12 hsup hL₁ hL₂ (commV_inv L) (h1_nat hn hL₁ h₁)
    (h1_dualNat hn hL₂ h₂)) hfix

theorem case_iv [Finite V] {G L : Subgroup (MulAut V)}
    (hiv : B51Case1iv G L) : IsIntDirect (commV L) (fixV L) ⊤ := by
  obtain ⟨-, n, hn, k, -, -, I, π, -, hind, hsup, hreal⟩ := hiv
  have hLI : ∀ i, ∀ g ∈ L, ∀ w ∈ I i, g w ∈ I i := fun i g hg w hw =>
    (hreal i).2.2.2.1 ⟨g, hg⟩ w hw
  have hind' : ∀ i, I i ⊓ (⨆ (j) (_ : j ≠ i), I j) = ⊥ := fun i => by simpa using hind i
  have hn2 : 2 ≤ n := by omega
  obtain ⟨hLW, hH1, hfix⟩ := h1_fixV_biSup I hind' hLI (fun i => h1_nat hn (hLI i) (hreal i))
    (fun i => fixV_inf_nat hn2 (hreal i)) Finset.univ
  have hW : (⨆ i ∈ Finset.univ, I i) = commV L := by
    rw [← hsup]
    simp
  rw [hW] at hfix
  exact isIntDirect_of_h1 (h1_congr hW hLW (commV_inv L) hH1) hfix

end P2

theorem asB51P2_holds :
    AsB51P2 := by
  intro V _ _ hV G L h h1 hnd
  rcases h1.2 with hi | hii | ⟨n, hiii⟩ | hiv
  · exact ⟨hi.1, P2.case_i hV hi.1 hi.2.1 hnd⟩
  · exact absurd (P2.case_ii hV h hii) hnd
  · exact absurd (P2.case_iii hiii) hnd
  · exact absurd (P2.case_iv hiv) hnd

end CFSG.Quasithin.B5

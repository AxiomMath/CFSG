module

public import CFSG.Quasithin.Vol2.Ch11SecU1Fin
public import CFSG.Quasithin.Vol2.Ch11SecU1Out3
public import CFSG.Quasithin.Vol2.Ch11SecU1L3
public import CFSG.Quasithin.Vol2.Ch11SecU1Sig3
public import CFSG.Quasithin.Vol2.Ch11SecU1Mem1
public import CFSG.Quasithin.Vol2.Ch11SecU1Mem3
public import CFSG.Walter.Cited.PSL2Small
public import CFSG.Quasithin.Vol2.Ch11SecU1In2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem setting_of_psl2_sq
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G))
    (hF : IsPSL 2 p 2 ↥(CFSG.generalizedFitting G)) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : Setting (CFSG.generalizedFitting G) := by
  have : Fact p.Prime := ⟨hp⟩
  set L := CFSG.generalizedFitting G with hLdef
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hF
  let e : L ≃* PSL2 K :=
    e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hodd : IsOddPrimePower (Nat.card K) := ⟨p, 2, hp, hpodd, by norm_num, hK⟩
  have h25 : 25 ≤ Nat.card K := by rw [hK]; nlinarith
  have h4 : Nat.card K % 4 = 1 := by
    rw [hK]
    obtain ⟨k, rfl⟩ := hpodd
    ring_nf
    omega
  have hnab : ∃ a b : L, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hZ := psl2_center_eq_bot K
    have hbig : Nat.card (PSL2 K) ≠ 1 := fun h1 => by
      have h2 := CFSG.Walter.Suzuki.two_dvd_card_psl2 K hodd
      rw [show Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) = 1 from h1] at h2
      norm_num at h2
    apply hbig
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
    have ha : a ∈ Subgroup.center (PSL2 K) := Subgroup.mem_center_iff.mpr fun c => by
      have := hcon (e.symm c) (e.symm a)
      exact e.symm.injective (by rw [map_mul, map_mul, this])
    have hb : b ∈ Subgroup.center (PSL2 K) := Subgroup.mem_center_iff.mpr fun c => by
      have := hcon (e.symm c) (e.symm b)
      exact e.symm.injective (by rw [map_mul, map_mul, this])
    rw [hZ, Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  have hAS := SecE3.almostSimple_generalizedFitting hs hnab hT hFT
  have hLn := hAS.normal
  obtain ⟨ι, hι⟩ := exists_adapted hK hodd (by omega) e hAS.centralizer_eq
  refine ⟨hAS, ?_, fun x hx y hy h1 h2 => inner_conj_of_equiv e hK hpodd hx hy h1 h2,
    fun x hx h1 => inner_solvable_of_equiv e hK hpodd hp5 hx h1,
    fun x hx h1 => inner_max_of_equiv e hK hp5 hx h1,
    fun x hx h1 y hy hcen => inner_center_of_equiv e hK hpodd hp5 hx h1 hy hcen,
    fun x hx h1 => inner_torus_of_equiv e hLn hK hpodd hp5 hx h1, fun b hbL hb2 => ?_,
    fun t₁ t₂ h₁ h₂ o₁ o₂ hc => outer_pair_of_adapted hι hp (by omega) hK h₁ h₂ o₁ o₂ hc⟩
  · rw [Nat.card_congr e.toEquiv]
    exact CFSG.Walter.Suzuki.two_dvd_card_psl2 K hodd
  · by_cases hr : (ι b).right = 1
    · exact Or.inl (oddTorus_of_adapted hLn hι hodd h4 (by omega) hbL hb2 hr)
    · refine Or.inr (sigmaFacts_of_adapted hι (sigmaPGammaL2_holds K p hp hp5 hK (ι b) ?_ hr))
      rw [orderOf_injective ι hι.1 b, hb2]

end CFSG.Quasithin.Vol2.Ch11.SecU1

namespace CFSG.Quasithin.E2.E22N

open Vol2.Ch11.SecU1

theorem e114ResRestL2_holds :
    E114ResRestL2 := by
  intro G _ _ T _ hFs hT hFT ⟨p, hp, hp3, hP⟩
  have hp5 : 5 ≤ p := by
    rcases (by omega : p = 4 ∨ 5 ≤ p) with h | h
    · subst h
      norm_num at hp
    · exact h
  exact nParam_le_one_of_setting torusMember_holds componentMember_holds
    (setting_of_psl2_sq hp hp5 hFs hP hT.1 hFT)

theorem e114OneResRest_of_L3Eps
    (h : E114ResRestL3Eps) : E114OneResRest :=
  e114OneResRest_of_L2_L3Eps e114ResRestL2_holds h

end CFSG.Quasithin.E2.E22N

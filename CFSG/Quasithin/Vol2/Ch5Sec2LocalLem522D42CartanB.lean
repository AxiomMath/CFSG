module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42Cartan
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42Eight
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotD4Aut
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113C2

public section

namespace CFSG.Quasithin.H13.D42

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem dvd_card_rank2 (h510 : Stmt5_1_10) (hF : FactL2LieParabolic)
    {T M L V H B D L₂ Dp : Subgroup G} {n p : ℕ} (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n p)
    (hL8 : LieModel (O2Q L₂) .PSL 2 2 3) (hSL₂ : IsSylowTwoOf (T ⊓ L₂) L₂)
    (hKC : quasithinIsCComponent (oTwoUpper H) H) (hnb : ¬ IsBenderAny (O2Q (oTwoUpper H)))
    {P : Subgroup G} (hP : IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P)
    (hL₂P : quasithinIsCComponent L₂ P) : 49 ∣ Nat.card ↥B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  obtain ⟨k, hk, htype, -, hMK⟩ :=
    nonBender_type h510 hyp.toHyp5_1_8 hyp.notation59 hKC hnb rfl
  obtain ⟨-, hpsl, -, -⟩ := l2Lie_nonBender hF hk htype hTK hMK hP hL₂P
  obtain ⟨D₀, hD₀, -, -⟩ := F1.exists_cartan hSL₂
  have h1 := (isCyclic_card_of_isHall_borelOf hk (Or.inl ⟨by simp [classicalTags], hpsl⟩) hSL₂
    hD₀).2
  have h2 := (isCyclic_card_of_isHall_borelOf (by norm_num) hL8 hSL₂ hD₀).2
  have hk3 : k = 3 := by
    have h3 : 2 ^ k - 1 = 7 := h1.symm.trans (h2.trans (by norm_num))
    have h4 := Nat.one_le_two_pow (n := k)
    generalize hq : 2 ^ k = q at h3 h4
    have h5 : 2 ^ k = 2 ^ 3 := by omega
    exact Nat.pow_right_injective le_rfl h5
  subst hk3
  obtain ⟨-, -, -, hBH, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hyp.notation59
  rw [hMK] at hBH
  have hOT : pCoreOf 2 (oTwoUpper H) ≤ T ⊓ oTwoUpper H := F7.isSylowTwoOf_pCoreOf_le hTK
  have hBK : B ≤ oTwoUpper H := hBH.1.trans inf_le_left
  have hBb : Lin2.IsHallTwoPrimeOf (modO2Image (oTwoUpper H) B)
      (Subgroup.normalizer ((modO2Image (oTwoUpper H) (T ⊓ oTwoUpper H) :
        Subgroup (O2Q (oTwoUpper H))) : Set (O2Q (oTwoUpper H)))) := by
    have h1 := isHallTwoPrimeOf_modO2Image (X := oTwoUpper H) inf_le_left hBH
    rwa [modO2Image_inf_normalizer le_rfl inf_le_right (fun x hx => hOT hx.2),
      Vol2.Ch11.SecS.modO2Image_self, top_inf_eq] at h1
  have hdvd := dvd_card_of_rank2_eight htype (Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hTK) hBb
  rwa [Vol2.Ch11.SecS.card_modO2Image_of_odd hBK hBH.2.1] at hdvd

theorem dvd_card_B (h510 : Stmt5_1_10) (hF : FactL2LieParabolic)
    (h38 : Vol2Native.A38ForSQTKCat) {T M L V H B D L₂ Dp : Subgroup G} {n p : ℕ}
    (hyp : Hyp5_2_2p G T M L V H B D L₂ Dp n p) (hL₂K : L₂ < oTwoUpper H)
    (hL8 : LieModel (O2Q L₂) .PSL 2 2 3) (hSL₂ : IsSylowTwoOf (T ⊓ L₂) L₂) :
    49 ∣ Nat.card ↥B := by
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hyp.choice
  rcases hcase with ⟨-, rfl⟩ | ⟨hnb, rfl, P, hP, hL₂P⟩
  ·
    obtain ⟨-, -, hBorel, hBH, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hyp.notation59
    rw [hyp.toHyp5_1_8.borel_eq hBorel] at hBH
    obtain ⟨K₂, tc⟩ := exists_twoComp h38 hloc hyp.hStar.1.2 hTH hK₁ hKeq hL₂K
    have h49 := tc.sq_dvd_card hK₁ hTH (by norm_num) hL8 hBH
    norm_num at h49
    exact h49
  · exact dvd_card_rank2 h510 hF hyp hL8 hSL₂ hK₁ hnb hP hL₂P

theorem exists_seven_trivial {B L₂ : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L₂ : Set G))
    (hL8 : LieModel (O2Q L₂) .PSL 2 2 3) (h49 : 49 ∣ Nat.card ↥B) :
    ∃ b ∈ B, b ≠ 1 ∧ b ^ 7 = 1 ∧ ∀ x ∈ L₂, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 L₂ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set φ : ↥B →* MulAut (O2Q L₂) := (quotConjAut L₂).comp (Subgroup.inclusion hBN) with hφ
  have hA : Nat.card (MulAut (O2Q L₂)) = 1512 := by
    rw [card_mulAut_of_lieModel_L2 (by norm_num) hL8]
    norm_num
  have hrange : Nat.card φ.range ∣ 1512 := hA ▸ Subgroup.card_subgroup_dvd_card _
  have hcard := Subgroup.card_ker_mul_card_range φ
  have h7 : 7 ∣ Nat.card φ.ker := by
    by_contra hn
    have hcop : Nat.Coprime (7 ^ 2) (Nat.card φ.ker) :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hn)
    rw [← hcard] at h49
    have h1 : 7 ^ 2 ∣ Nat.card φ.range := hcop.dvd_of_dvd_mul_left (by simpa using h49)
    have h2 := h1.trans hrange
    norm_num at h2
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥φ.ker) 7 h7
  have hb7 : ((b : ↥B) : G) ^ 7 = 1 := by
    have h1 : b ^ 7 = 1 := by rw [← hb, pow_orderOf_eq_one]
    simpa using congrArg (fun y : ↥φ.ker => ((y : ↥B) : G)) h1
  refine ⟨((b : ↥B) : G), (b : ↥B).2, fun h1 => ?_, hb7, fun x hx => ?_⟩
  · have h2 : b = 1 := Subtype.ext (Subtype.ext h1)
    rw [h2, orderOf_one] at hb
    norm_num at hb
  · have hker : quotConjAut L₂ (Subgroup.inclusion hBN (b : ↥B)) = 1 := b.2
    exact commutator_mem_of_quotConjAut_eq_one hker ⟨x, hx⟩

end CFSG.Quasithin.H13.D42

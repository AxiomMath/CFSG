module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveNineteenL2
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qu
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace TwelveNineteen

private theorem card_sup_mul_card_inf {X : Type*} [Group X] {A N : Subgroup X}
    (hAN : A ≤ normalizer (N : Set X)) :
    Nat.card (A ⊔ N : Subgroup X) * Nat.card (A ⊓ N : Subgroup X) =
      Nat.card A * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A N hAN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (A ⊔ N))
  have h3 : Nat.card (N.subgroupOf A) = Nat.card (A ⊓ N : Subgroup X) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (A ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem exists_conj_le_normalizer_sup {p : ℕ} [Fact p.Prime] {H N R S T : Subgroup G}
    (hNH : N ≤ H) (hHN : H ≤ normalizer (N : Set G)) (hHR : H ≤ normalizer (R : Set G))
    (hRN : R ≤ N) (hR : ¬ 2 ∣ R.relIndex N) (hS : IsSylowOf p S N) (hTH : T ≤ H)
    (hT : IsPGroup 2 T) :
    ∃ k ∈ H, T ≤ normalizer ((S.map (MulAut.conj k).toMonoidHom ⊔ R : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup G := H ⊓ normalizer ((S ⊔ R : Subgroup G) : Set G) with hKdef
  have hKH : K ≤ H := inf_le_left
  have hKN : K ≤ normalizer (N : Set G) := hKH.trans hHN
  have hfr := uc22p22qq_frattini hS (M := H)
    (fun m hm y hy => (mem_normalizer_iff.1 (hHN hm) y).1 hy)
  have hSRn : normalizer (S : Set G) ⊓ H ≤ normalizer ((S ⊔ R : Subgroup G) : Set G) :=
    CFSG.Quasithin.A1a.le_normalizer_sup inf_le_left (inf_le_right.trans hHR)
  have hsup : K ⊔ N = H := by
    refine le_antisymm (sup_le hKH hNH) fun m hm => ?_
    obtain ⟨y, hy, hyn⟩ := hfr m hm
    have hyH : y⁻¹ * m ∈ H := H.mul_mem (H.inv_mem (hNH hy)) hm
    have hyK : y⁻¹ * m ∈ K := ⟨hyH, hSRn ⟨hyn, hyH⟩⟩
    have hm' : m = y * (y⁻¹ * m) := by group
    rw [hm']
    exact (K ⊔ N).mul_mem (mem_sup_right hy) (mem_sup_left hyK)
  have hprod := card_sup_mul_card_inf hKN
  rw [hsup] at hprod
  have hRK : R ≤ K ⊓ N :=
    le_inf (fun r hr => ⟨hNH (hRN hr), Subgroup.le_normalizer (mem_sup_right hr)⟩) hRN
  have e1 := relIndex_mul_card (H := K) (K := H)
  rw [inf_eq_left.2 hKH] at e1
  have e2 := relIndex_mul_card (H := R) (K := N)
  rw [inf_eq_left.2 hRN] at e2
  have e3 := relIndex_mul_card (H := R) (K := K ⊓ N)
  rw [inf_eq_left.2 hRK] at e3
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hdiv : K.relIndex H * R.relIndex (K ⊓ N) = R.relIndex N := by
    have h' : (K.relIndex H * R.relIndex (K ⊓ N)) * (Nat.card K * Nat.card R) =
        R.relIndex N * (Nat.card K * Nat.card R) := by
      calc (K.relIndex H * R.relIndex (K ⊓ N)) * (Nat.card K * Nat.card R)
          = (K.relIndex H * Nat.card K) * (R.relIndex (K ⊓ N) * Nat.card R) := by ring
        _ = Nat.card K * Nat.card N := by rw [e1, e3]; exact hprod
        _ = R.relIndex N * (Nat.card K * Nat.card R) := by rw [← e2]; ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hKpos hRpos) h'
  have hKodd : ¬ 2 ∣ K.relIndex H := fun h2 => hR (hdiv ▸ dvd_mul_of_dvd_left h2 _)
  obtain ⟨B, hB⟩ := exists_isSylowOf 2 K
  obtain ⟨hBK, hBp, hBi⟩ := (isSylowOf_iff (p := 2)).1 hB
  have hBH : IsSylowOf 2 B H := by
    refine (isSylowOf_iff (p := 2)).2 ⟨hBK.trans hKH, hBp, fun h2 => ?_⟩
    rw [← relIndex_mul_relIndex B K H hBK hKH] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
    · exact hBi h
    · exact hKodd h
  obtain ⟨k, hkH, hk⟩ := UC6.exists_conj_le_of_isSylowOf hBH hTH hT
  refine ⟨k, hkH, fun x hx => ?_⟩
  have hA' : S.map (MulAut.conj k).toMonoidHom ⊔ R =
      (S ⊔ R).map (MulAut.conj k).toMonoidHom := by
    have hRk : R.map (MulAut.conj k).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp (hHR hkH)
    rw [Subgroup.map_sup, hRk]
  have hmem : ∀ z : G, z ∈ S.map (MulAut.conj k).toMonoidHom ⊔ R ↔ k⁻¹ * z * k ∈ S ⊔ R := by
    intro z
    rw [hA', Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hy : k⁻¹ * x * k ∈ normalizer ((S ⊔ R : Subgroup G) : Set G) := (hBK (hk x hx)).2
  rw [mem_normalizer_iff]
  intro z
  rw [hmem, hmem, mem_normalizer_iff.1 hy]
  have e : k⁻¹ * x * k * (k⁻¹ * z * k) * (k⁻¹ * x * k)⁻¹ = k⁻¹ * (x * z * x⁻¹) * k := by group
  rw [e]

theorem permutes_of_le_normalizer_sup {X R T : Subgroup G} (hRT : R ≤ T)
    (hT : T ≤ normalizer ((X ⊔ R : Subgroup G) : Set G)) (hXR : X ≤ normalizer (R : Set G)) :
    Permutes X T := by
  have h1 : ((X ⊔ R : Subgroup G) : Set G) = (X : Set G) * R :=
    Subgroup.coe_mul_of_left_le_normalizer_right X R hXR
  have h2 : ((R ⊔ X : Subgroup G) : Set G) = (R : Set G) * X :=
    Subgroup.coe_mul_of_right_le_normalizer_left R X hXR
  have h3 : ((X ⊔ R : Subgroup G) : Set G) * T = (T : Set G) * (X ⊔ R : Subgroup G) :=
    (Subgroup.set_mul_normalizer_comm (T : Set G) (X ⊔ R) hT).symm
  have hRT' : (R : Set G) * T = T := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right R T (hRT.trans le_normalizer),
      sup_eq_right.2 hRT]
  have hTR' : (T : Set G) * R = T := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left T R (hRT.trans le_normalizer),
      sup_eq_left.2 hRT]
  unfold Permutes
  calc (X : Set G) * T = X * (R * T) := by rw [hRT']
    _ = (X * R) * T := (mul_assoc _ _ _).symm
    _ = ((X ⊔ R : Subgroup G) : Set G) * T := by rw [h1]
    _ = T * ((X ⊔ R : Subgroup G) : Set G) := h3
    _ = T * (R * X) := by rw [sup_comm, h2]
    _ = (T * R) * X := (mul_assoc _ _ _).symm
    _ = T * X := by rw [hTR']

theorem not_two_dvd_relIndex (D : Data G) (h613 : UC6.R6_13 D) {p : ℕ} {P P₀ : Subgroup G}
    (hH : UC6.Hyp612 D p P P₀) :
    ¬ 2 ∣ (pCoreOf 2 D.M).relIndex
      ((P₀ ⊔ P ⊓ UC6.inftyOf (centralizer (P₀ : Set G))) ⊔ uniqueFourPrimeCore p D.M) := by
  obtain ⟨⟨-, -, -, -, -, hfrob⟩, -⟩ := h613 p P P₀ hH
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  have hpP : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  haveI : Fact p.Prime := ⟨hpP⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := UC6.inftyOf (centralizer (P₀ : Set G)) with hLdef
  set C := centralizer (L : Set G) with hCdef
  set S : Subgroup G := P₀ ⊔ P ⊓ L with hSdef
  set Q := uniqueFourPrimeCore p D.M with hQdef
  set R := pCoreOf 2 D.M with hRdef
  have hRQ : R ≤ Q := RankThreeTheoremC.Generic49U3.pCoreOf_two_le_relPPrimeCore hp2 D.M
  have hSP : S ≤ P := sup_le hH.le inf_le_left
  have hSM : S ≤ D.M := hSP.trans hH.sylow.le
  have hSp : IsPGroup p S := hH.sylow.isPGroup.to_le hSP
  obtain ⟨hCM, -⟩ := uc22p22qk_frob_unpack D hfrob
  have hMR : D.M ≤ normalizer (R : Set G) := uc22p22qu_M_le_normalizer_R D.M
  have hMQ : D.M ≤ normalizer (Q : Set G) := fun m hm =>
    uc22p22qk_mem_normalizer fun q hq =>
      RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_conj_mem hq hm
  have hCodd : ¬ 2 ∣ Nat.card C := by
    intro h2
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 h2
    have hodd := uc22p22qu_Dd_odd D hfrob c c.2
    rw [← Subgroup.orderOf_coe] at hc
    rw [hc] at hodd
    exact (Nat.not_odd_iff_even.2 even_two) hodd
  have hRC : R ⊓ C = ⊥ := hfrob.2.2.2.2.2.2.1
  have hprod := card_sup_mul_card_inf (hCM.trans hMR)
  rw [inf_comm, hRC, Subgroup.card_bot, mul_one] at hprod
  have e1 := relIndex_mul_card (H := R) (K := C ⊔ R)
  rw [inf_eq_left.2 le_sup_right, hprod] at e1
  have hRCi : R.relIndex (C ⊔ R) = Nat.card C :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [e1])
  have hQRC : Q ≤ C ⊔ R := by
    intro q hq
    obtain ⟨r, hr, d, hd, rfl⟩ := uc22p22qu_Q_le D hfrob q hq
    exact (C ⊔ R).mul_mem (mem_sup_right hr) (mem_sup_left hd)
  have hQodd : ¬ 2 ∣ R.relIndex Q := by
    intro h2
    apply hCodd
    rw [← hRCi, ← relIndex_mul_relIndex R Q (C ⊔ R) hRQ hQRC]
    exact dvd_mul_of_dvd_left h2 _
  have hprod2 := card_sup_mul_card_inf (hSM.trans hMQ)
  have e2 := relIndex_mul_card (H := Q) (K := S ⊔ Q)
  rw [inf_eq_left.2 le_sup_right] at e2
  have hNQodd : ¬ 2 ∣ Q.relIndex (S ⊔ Q) := by
    intro h2
    have hdvd : Q.relIndex (S ⊔ Q) ∣ Nat.card S := by
      refine ⟨Nat.card (S ⊓ Q : Subgroup G), Nat.eq_of_mul_eq_mul_right
        (Nat.card_pos (α := Q)) ?_⟩
      rw [← hprod2, ← e2]
      ring
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hSp
    rw [hn] at hdvd
    have h2p : 2 ∣ p ^ n := h2.trans hdvd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpP).1 (Nat.prime_two.dvd_of_dvd_pow h2p)
    exact hp2 this.symm
  rw [← relIndex_mul_relIndex R Q (S ⊔ Q) hRQ le_sup_right]
  intro h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
  · exact hQodd h
  · exact hNQodd h

theorem exists_permutes (D : Data G) (hstd : Sigma23Std D) (h613 : UC6.R6_13 D) {p : ℕ}
    {P P₀ : Subgroup G} (hH : UC6.Hyp612 D p P P₀) :
    ∃ X : Subgroup G, X ≤ D.M ∧ IsPGroup p X ∧ (∀ x ∈ X, x ^ p = 1) ∧
      p ^ 2 < Nat.card X ∧ Permutes X D.T := by
  obtain ⟨⟨-, hsolv, hwc, -, -, -⟩, -, -, ⟨-, h4b, -⟩, -⟩ := h613 p P P₀ hH
  have hpσ : p ∈ D.sig := by
    rw [D.sig_sub]
    exact Or.inl (Or.inr hH.mem_sig2)
  have hpP : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  haveI : Fact p.Prime := ⟨hpP⟩
  set L := UC6.inftyOf (centralizer (P₀ : Set G)) with hLdef
  set S : Subgroup G := P₀ ⊔ P ⊓ L with hSdef
  set Q := uniqueFourPrimeCore p D.M with hQdef
  set R := pCoreOf 2 D.M with hRdef
  have hSP : S ≤ P := sup_le hH.le inf_le_left
  have hSM : S ≤ D.M := hSP.trans hH.sylow.le
  have hSp : IsPGroup p S := hH.sylow.isPGroup.to_le hSP
  have hRQ : R ≤ Q := RankThreeTheoremC.Generic49U3.pCoreOf_two_le_relPPrimeCore hp2 D.M
  have hRN : R ≤ S ⊔ Q := hRQ.trans le_sup_right
  have hNM : S ⊔ Q ≤ D.M := sup_le hSM (sSup_le fun _ hN => hN.1)
  have hNeq : S ⊔ Q = (P₀ ⊔ Q) ⊔ (P ⊓ L ⊔ R) := by
    apply le_antisymm
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
        (le_sup_right.trans le_sup_left)
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        (sup_le (le_sup_right.trans le_sup_left) (hRQ.trans le_sup_right))
  have hMN : D.M ≤ normalizer ((S ⊔ Q : Subgroup G) : Set G) := by
    rw [hNeq]
    exact CFSG.Quasithin.A1a.le_normalizer_sup (uc22p22qu_P0Q_normal D hH hsolv hwc) h4b
  have hMR : D.M ≤ normalizer (R : Set G) := uc22p22qu_M_le_normalizer_R D.M
  obtain ⟨k, hkM, hTk⟩ := exists_conj_le_normalizer_sup hNM hMN hMR hRN
    (not_two_dvd_relIndex D h613 hH) (uc22p22qu_isSylowOf_sup hSM hSp) D.sylowM.le
    D.sylowM.isPGroup
  obtain ⟨hE, hbig⟩ := isElemAbelian_sup_P1 D hstd h613 hH
  have hXM : S.map (MulAut.conj k).toMonoidHom ≤ D.M := by
    rintro _ ⟨s, hs, rfl⟩
    exact D.M.mul_mem (D.M.mul_mem hkM (hSM hs)) (D.M.inv_mem hkM)
  have hinj : Function.Injective (MulAut.conj k).toMonoidHom := (MulAut.conj k).injective
  refine ⟨S.map (MulAut.conj k).toMonoidHom, hXM, ?_, ?_, ?_, ?_⟩
  · exact hSp.map _
  · rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, hE.2 s hs, map_one]
  · rwa [Subgroup.card_map_of_injective hinj]
  · exact permutes_of_le_normalizer_sup (uc22p22e_pCoreOf_le_T D) hTk (hXM.trans hMR)

end TwelveNineteen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

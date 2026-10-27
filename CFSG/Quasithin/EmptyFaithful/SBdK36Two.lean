module

public import CFSG.Quasithin.EmptyFaithful.SBdK36Gen
public import CFSG.Quasithin.EmptyFaithful.SBdK36Abs
public import CFSG.Quasithin.EmptyFaithful.SBdK36Model
public import CFSG.Quasithin.EmptyFaithful.S153IClose

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace SBd

theorem isSylowTwoOf_restrict {G : Type*} [Group G] {P C A : Subgroup G} (hP : IsSylowTwoOf P A)
    (hPC : P ≤ C) (hCA : C ≤ A) : IsSylowTwoOf P C := by
  refine ⟨hPC, hP.2.1, fun hdvd => hP.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex P C A hPC hCA
  have h2 : 2 ∣ P.relIndex A := by rw [← h1]; exact Dvd.dvd.mul_right hdvd _
  exact h2

theorem card_sup_mul_card_inf_of_le_normalizer {G : Type*} [Group G] {X N : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) =
      Nat.card X * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem card_sup_le_of_normalizer {G : Type*} [Group G] [Finite G] {Y S P O : Subgroup G}
    (hSY : S ≤ Subgroup.normalizer (Y : Set G)) {a b : ℕ} (hS : Nat.card S ≤ a * Nat.card P)
    (hOS : O ≤ S) (hOY : O ≤ Y) (hY : Nat.card Y ≤ b * Nat.card O) :
    Nat.card ↥(Y ⊔ S) ≤ a * b * Nat.card P := by
  have h := card_sup_mul_card_inf_of_le_normalizer hSY
  rw [sup_comm] at h
  have hO : Nat.card O ≤ Nat.card ↥(S ⊓ Y) := Subgroup.card_le_of_le (le_inf hOS hOY)
  have hpos : 0 < Nat.card ↥(S ⊓ Y) := Nat.card_pos
  have h1 : Nat.card ↥(Y ⊔ S) * Nat.card ↥(S ⊓ Y) ≤ (a * b * Nat.card P) * Nat.card ↥(S ⊓ Y) := by
    rw [h]
    calc Nat.card S * Nat.card Y ≤ (a * Nat.card P) * (b * Nat.card O) :=
          Nat.mul_le_mul hS hY
      _ = (a * b * Nat.card P) * Nat.card O := by ring
      _ ≤ (a * b * Nat.card P) * Nat.card ↥(S ⊓ Y) := Nat.mul_le_mul_left _ hO
  exact Nat.le_of_mul_le_mul_right h1 hpos

theorem exists_zpow_eq_pow_fin {Q : Type*} [Group Q] {x : Q} (h3 : x ^ 3 = 1) (k : ℤ) :
    ∃ j : Fin 3, x ^ k = x ^ (j : ℕ) := by
  refine ⟨⟨(k % 3).toNat, by omega⟩, ?_⟩
  have : x ^ k = x ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul]
    simp [h3]
  rw [this]
  have hk : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  rw [← zpow_natCast]
  congr 1
  simp [Int.toNat_of_nonneg hk]

section StarData

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem zstar_structure_of_rank_two (h113 : StageLemma14113) (hh : Hyp153 G T Mc M)
    {A B : OTwoQuot M} (hc : S153D.StarCoords hh V₁ A B)
    (hr : CFSG.Open.pRank 3 (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) = 2) :
    ⁅A, B⁆ ≠ 1 ∧ S153D.ZstarOf hh ≤ Subgroup.zpowers ⁅A, B⁆ := by
  set K : Subgroup G := Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G) with hK
  have hKY : K ≤ Y153 Mc M := inf_le_left
  have hYpY : oTwoUpper K ≤ Y153 Mc M := (oTwoUpper_le _).trans hKY
  have hAK : A ∈ imageOTwoQuot M K := hc.A_mem
  have hAY : A ∈ imageOTwoQuot M (Y153 Mc M) := imageOTwoQuot_mono hKY hAK
  have hBY : B ∈ imageOTwoQuot M (Y153 Mc M) := hc.B_mem
  have hYpK : imageOTwoQuot M (oTwoUpper K) = imageOTwoQuot M K :=
    S153D.imageOTwoQuot_oTwoUpper_eq h113 hh hKY
  rcases S153D.Zstar_structure h113 hh hAY hBY hc.comm_mem hc.gen with hZ | ⟨hz1, hZle⟩
  · exfalso
    have h9 := S153D.nine_dvd_card_quot h113 hh hYpY hr
    have hle : imageOTwoQuot M (oTwoUpper K) ≤ Subgroup.zpowers A := by
      intro u hu
      rw [hYpK] at hu
      obtain ⟨j, c, hcZ, rfl⟩ := hc.genK u hu
      rw [hZ, Subgroup.mem_bot] at hcZ
      rw [hcZ, mul_one]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers A) j
    have h3 : Nat.card ↥(imageOTwoQuot M (oTwoUpper K)) ∣ 3 := by
      refine (Subgroup.card_dvd_of_le hle).trans ?_
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (S153D.star_cube h113 hh hAY)
    have := h9.trans h3
    omega
  · exact ⟨hz1, hZle⟩

theorem card_imageOTwoQuot_Yp_le (h113 : StageLemma14113) (hh : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t)
    {A B : OTwoQuot M} (hc : S153D.StarCoords hh V₁ A B)
    (hz : S153D.ZstarOf hh ≤ Subgroup.zpowers ⁅A, B⁆) :
    Nat.card ↥(imageOTwoQuot M (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)))) ≤ 9 := by
  set K : Subgroup G := Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G) with hK
  have hKY : K ≤ Y153 Mc M := inf_le_left
  have hYpK : imageOTwoQuot M (oTwoUpper K) = imageOTwoQuot M K :=
    S153D.imageOTwoQuot_oTwoUpper_eq h113 hh hKY
  rw [hYpK]
  have hAK : A ∈ imageOTwoQuot M K := hc.A_mem
  have hAY : A ∈ imageOTwoQuot M (Y153 Mc M) := imageOTwoQuot_mono hKY hAK
  have hzK : ⁅A, B⁆ ∈ imageOTwoQuot M K := S153D.Zstar_le_imageK hh D hc.comm_mem
  have hA3 : A ^ 3 = 1 := S153D.star_cube h113 hh hAY
  have hz3 : ⁅A, B⁆ ^ 3 = 1 := S153D.star_cube h113 hh hc.comm_mem.2
  let f : Fin 3 × Fin 3 → ↥(imageOTwoQuot M K) := fun p =>
    ⟨A ^ (p.1 : ℕ) * ⁅A, B⁆ ^ (p.2 : ℕ),
      Subgroup.mul_mem _ (Subgroup.pow_mem _ hAK _) (Subgroup.pow_mem _ hzK _)⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨j, c, hcZ, rfl⟩ := hc.genK y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hz hcZ)
    obtain ⟨j', hj'⟩ := exists_zpow_eq_pow_fin hA3 j
    obtain ⟨i', hi'⟩ := exists_zpow_eq_pow_fin hz3 i
    exact ⟨(j', i'), Subtype.ext (by simp [f, hj', hi'])⟩
  have := Nat.card_le_card_of_surjective f hf
  simpa [Nat.card_prod] using this

end StarData

theorem input15336OneCaseTwo_proved (h11 : StageLemma14111) (h113 : StageLemma14113) :
    Input15336OneCaseTwo := by
  intro G _ _ T Mc M V₁ V₂ Yp t h hr hcase I hI
  have hsylI : IsSylowTwoOf (Sgp153 T V₁) I := h.lemma_15_3_11_one h11 h113 hI
  obtain ⟨-, hYp⟩ := hcase
  subst hYp
  have hh : Hyp153 G T Mc M := h.hyp
  have D : Decomp153 T M V₁ V₂ t := h.decomp
  have hsyl : IsSylowTwoOf (Sgp153 T V₁)
      (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ⊔ Sgp153 T V₁) :=
    isSylowTwoOf_restrict hsylI le_sup_right hI.1.1
  have hRT := S153D.R_le_of_case_two h113 hh D hr hsyl
  obtain ⟨A, B, hc⟩ := S153D.exists_starCoords h113 hh D
  obtain ⟨hz1, hZle⟩ := zstar_structure_of_rank_two h113 hh hc hr
  have hcardY := card_imageOTwoQuot_Yp_le h113 hh D hc hZle
  have hYM : Y153 Mc M ≤ M := Y153_le Mc M
  have hTM : T ≤ M := hh.T_le
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := hh.le_normalizer
  have hTN : T ≤ Subgroup.normalizer (VZ T M : Set G) := hTM.trans hMV
  have hTY : T ≤ Subgroup.normalizer (Y153 Mc M : Set G) := hTM.trans (le_normalizer_Y153 Mc M)
  have hKY : Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G) ≤ Y153 Mc M := inf_le_left
  have hYpY : oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ≤ Y153 Mc M :=
    (oTwoUpper_le _).trans hKY
  have hYpK : imageOTwoQuot M (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) =
      imageOTwoQuot M (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) :=
    S153D.imageOTwoQuot_oTwoUpper_eq h113 hh hKY
  have hzK := S153D.Zstar_le_imageK hh D hc.comm_mem
  obtain ⟨a, haM, haYp, haA⟩ := mem_imageOTwoQuot_iff.mp (hYpK ▸ hc.A_mem)
  obtain ⟨z₀, hz₀M, hz₀Yp, hz₀z⟩ := mem_imageOTwoQuot_iff.mp (hYpK ▸ hzK)
  have hz₀C : z₀ ∈ Subgroup.centralizer (VZ T M : Set G) := by
    refine (A4.actionOn_eq_one_iff hMV ⟨z₀, hz₀M⟩).mp ?_
    have := hc.comm_mem.1
    rw [← hz₀z] at this
    exact this
  have hsylbar := hh.isSylowTwoOf_autI
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -, -⟩ := D.model
  have hYbar : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := hh.autOn_Y153 h113
  set S : Subgroup G := Sgp153 T ((commV L₁).map (inclMod hV)) with hSdef
  set Yp : Subgroup G := oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer
    (((commV L₁).map (inclMod hV) : Subgroup G) : Set G)) with hYpdef
  set H : Subgroup G := Yp ⊔ S with hHdef
  have hSM : S ≤ M := inf_le_left.trans hTM
  have hSY : S ≤ Subgroup.normalizer (Y153 Mc M : Set G) := inf_le_left.trans hTY
  have hSYp : S ≤ Subgroup.normalizer (Yp : Set G) := S153D.Sgp153_le_normalizer_Yplus hh
  have hHM : H ≤ M := sup_le (hYpY.trans hYM) hSM
  have hHN : H ≤ Subgroup.normalizer (VZ T M : Set G) := hHM.trans hMV
  have hHYp : H ≤ Subgroup.normalizer (Yp : Set G) := sup_le Subgroup.le_normalizer hSYp
  have hYpN : Yp ≤ Subgroup.normalizer (VZ T M : Set G) := (hYpY.trans hYM).trans hMV
  have hSVN : S ≤ Subgroup.normalizer (VZ T M : Set G) := hSM.trans hMV
  have hRS : pCoreOf 2 H ≤ S := pCoreOf_le_of_isSylowTwoOf hsyl
  have hRC : pCoreOf 2 H ≤ Subgroup.centralizer (VZ T M : Set G) := hRT.trans inf_le_right
  have hPR : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ pCoreOf 2 H := by
    have hP : pCoreOf 2 (Y153 Mc M ⊔ T) = T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
      hh.lemma_15_3_7_pCore h113
    have hV₁V : ((commV L₁).map (inclMod hV) : Subgroup G) ≤ VZ T M := map_inclMod_le hV _
    have hPS : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ S := inf_centralizer_le_nS T _ hV₁V
    have hHYT : H ≤ Y153 Mc M ⊔ T := sup_le_sup hYpY inf_le_left
    have hHP : H ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) :
        Set G) := by
      rw [← hP]
      exact hHYT.trans (le_normalizer_pCoreOf 2 _)
    exact le_pCoreOf_of_le_normalizer 2 (hPS.trans le_sup_right) hHP (hP ▸ pCoreOf_isPGroup 2 _)
  have hOYpR : pCoreOf 2 Yp ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Yp).trans le_sup_left)
      (hHYp.trans (normalizer_le_normalizer_pCoreOf 2 Yp)) (pCoreOf_isPGroup 2 Yp)
  have hautle : autI hV H ≤ L₁ ⊔ L₂ := by
    rw [autI_sup hV hYpN hSVN]
    refine sup_le ((autI_mono hV hYpY).trans ?_) ?_
    · rw [hYbar]
      exact hS.oTwoUpper_le_sup
    · rw [autI_nS hV hS hTM]
      exact inf_le_right
  obtain ⟨e, he₁, he₂⟩ := exists_mulEquiv_sup_perm hS
  let ρ : ↥H →* MulAut (IntMod (VZ T M) hV) := convHom hV H hHN
  have hρmem : ∀ x : ↥H, ρ x ∈ L₁ ⊔ L₂ := fun x => by
    have : ρ x ∈ autI hV H := (range_convHom hV H hHN) ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩
    exact hautle this
  let ρ' : ↥H →* ↥(L₁ ⊔ L₂) := ρ.codRestrict (L₁ ⊔ L₂) hρmem
  let ψ₂ : ↥H →* Equiv.Perm (Fin 3) := (MonoidHom.snd _ _).comp (e.toMonoidHom.comp ρ')
  have hψ₂C : ∀ x : ↥H, (x : G) ∈ Subgroup.centralizer (VZ T M : Set G) → ψ₂ x = 1 := by
    intro x hx
    have h1 : ρ x = 1 := (convI_eq_one_iff hV ⟨x, hHN x.2⟩).2 hx
    have h2 : ρ' x = 1 := Subtype.ext h1
    simp [ψ₂, h2]
  have hψ₂L₁ : ∀ x : ↥H, ρ x ∈ L₁ → ψ₂ x = 1 := fun x hx => he₁ (ρ x) hx
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := hS.exists_sylowFacts hsylbar
  have hs₁S : s₁ ∈ autI hV S := by rw [hSdef, autI_nS hV hS hTM]; exact hF.sylow.s₁_mem_S
  have hs₂S : s₂ ∈ autI hV S := by rw [hSdef, autI_nS hV hS hTM]; exact hF.sylow.s₂_mem_S
  obtain ⟨r₁, hr₁S, hr₁⟩ := (mem_autI hV).1 hs₁S
  obtain ⟨r₂, hr₂S, hr₂⟩ := (mem_autI hV).1 hs₂S
  have haH : a ∈ H := Subgroup.mem_sup_left haYp
  have haN : a ∈ Subgroup.normalizer (VZ T M : Set G) := hMV haM
  have haKc : a ∈ Y153 Mc M ⊓ Subgroup.centralizer
      (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) := oTwoUpper_le _ haYp
  have hx₂L : convI hV ⟨a, haN⟩ ∈ L₂ := by
    have hgX : convI hV ⟨a, haN⟩ ∈ autI hV M := convI_mem_autI hV haM haN
    refine (hS.mem_L₂_iff hgX).2 ?_
    exact (mem_centralizer_map_inclMod_iff hV haN (commV L₁)).1 haKc.2
  have hx₂1 : convI hV ⟨a, haN⟩ ≠ 1 := by
    intro h1
    apply hc.A_ne
    rw [← haA]
    exact h1
  have hx₂odd : Odd (orderOf (convI hV ⟨a, haN⟩)) := by
    refine hS.odd_orderOf_of_mem_oTwoUpper ?_
    rw [← hYbar]
    exact convI_mem_autI hV haKc.1 haN
  have hψ₂s : Function.Surjective ψ₂ := by
    have hcard6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    set x₂ := convI hV ⟨a, haN⟩ with hx₂def
    have hψa : ψ₂ ⟨a, haH⟩ = (e ⟨x₂, Subgroup.mem_sup_right hx₂L⟩).2 := rfl
    have hy1 := he₂ x₂ hx₂L
    have hy2 : (e ⟨x₂, Subgroup.mem_sup_right hx₂L⟩).2 ≠ 1 := by
      intro h2
      have h0 : e ⟨x₂, Subgroup.mem_sup_right hx₂L⟩ = 1 := Prod.ext hy1 h2
      have h3 : (⟨x₂, Subgroup.mem_sup_right hx₂L⟩ : ↥(L₁ ⊔ L₂)) = 1 :=
        e.injective (by rw [h0, map_one])
      exact hx₂1 (congrArg Subtype.val h3)
    have hord3 : orderOf (e ⟨x₂, Subgroup.mem_sup_right hx₂L⟩).2 = 3 := by
      have h1 : orderOf (e ⟨x₂, Subgroup.mem_sup_right hx₂L⟩).2 ∣
          orderOf (e ⟨x₂, Subgroup.mem_sup_right hx₂L⟩) :=
        orderOf_map_dvd (MonoidHom.snd (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3))) _
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk] at h1
      have h6 : orderOf (e ⟨x₂, Subgroup.mem_sup_right hx₂L⟩).2 ∣ 6 := by
        rw [← hcard6]
        exact orderOf_dvd_natCard _
      have hodd := Odd.of_dvd_nat hx₂odd h1
      have h3 : orderOf (e ⟨x₂, Subgroup.mem_sup_right hx₂L⟩).2 ∣ 3 := by
        have hcop : Nat.Coprime (orderOf (e ⟨x₂, Subgroup.mem_sup_right hx₂L⟩).2) 2 :=
          Nat.coprime_two_right.mpr hodd
        exact hcop.dvd_of_dvd_mul_left (by simpa using h6)
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hy2
      · exact h
    have hr₂H : (r₂ : G) ∈ H := Subgroup.mem_sup_right hr₂S
    have hs₂L : s₂ ∈ L₂ := hF.sylow.s₂_mem_L
    have hψr : ψ₂ ⟨r₂, hr₂H⟩ = (e ⟨s₂, Subgroup.mem_sup_right hs₂L⟩).2 := by
      show (e ⟨ρ ⟨r₂, hr₂H⟩, _⟩).2 = _
      have : ρ ⟨r₂, hr₂H⟩ = s₂ := hr₂
      simp only [this]
    have hy1' := he₂ s₂ hs₂L
    have hy2' : (e ⟨s₂, Subgroup.mem_sup_right hs₂L⟩).2 ≠ 1 := by
      intro h2
      have h0 : e ⟨s₂, Subgroup.mem_sup_right hs₂L⟩ = 1 := Prod.ext hy1' h2
      have h3 : (⟨s₂, Subgroup.mem_sup_right hs₂L⟩ : ↥(L₁ ⊔ L₂)) = 1 :=
        e.injective (by rw [h0, map_one])
      exact hF.sylow.s₂_ne (congrArg Subtype.val h3)
    have hsq : (e ⟨s₂, Subgroup.mem_sup_right hs₂L⟩).2 * (e ⟨s₂, Subgroup.mem_sup_right hs₂L⟩).2 = 1 := by
      have : e ⟨s₂, Subgroup.mem_sup_right hs₂L⟩ * e ⟨s₂, Subgroup.mem_sup_right hs₂L⟩ = 1 := by
        rw [← map_mul]
        have : (⟨s₂, Subgroup.mem_sup_right hs₂L⟩ * ⟨s₂, Subgroup.mem_sup_right hs₂L⟩ : ↥(L₁ ⊔ L₂)) = 1 :=
          Subtype.ext hF.s₂_sq
        rw [this, map_one]
      exact congrArg Prod.snd this
    have hord2 : orderOf (e ⟨s₂, Subgroup.mem_sup_right hs₂L⟩).2 = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hsq) hy2'
    have h3dvd : 3 ∣ Nat.card ψ₂.range := by
      have hmem : ψ₂ ⟨a, haH⟩ ∈ ψ₂.range := ⟨_, rfl⟩
      have := orderOf_dvd_natCard (⟨ψ₂ ⟨a, haH⟩, hmem⟩ : ↥ψ₂.range)
      rwa [Subgroup.orderOf_mk, hψa, hord3] at this
    have h2dvd : 2 ∣ Nat.card ψ₂.range := by
      have hmem : ψ₂ ⟨r₂, hr₂H⟩ ∈ ψ₂.range := ⟨_, rfl⟩
      have := orderOf_dvd_natCard (⟨ψ₂ ⟨r₂, hr₂H⟩, hmem⟩ : ↥ψ₂.range)
      rwa [Subgroup.orderOf_mk, hψr, hord2] at this
    have h6dvd : 6 ∣ Nat.card ψ₂.range :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2dvd h3dvd
    have hle : Nat.card ψ₂.range ≤ 6 := by
      rw [← hcard6]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card _)
    have heq : Nat.card ψ₂.range = 6 := le_antisymm hle (Nat.le_of_dvd Nat.card_pos h6dvd)
    have htop : ψ₂.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [heq, hcard6])
    exact MonoidHom.range_eq_top.mp htop
  have hcardN : Nat.card (CFSG.Open.pCore 2 ↥H) = Nat.card (pCoreOf 2 H) :=
    (Subgroup.card_map_of_injective H.subtype_injective).symm
  have hS4 : Nat.card S ≤ 4 * Nat.card (pCoreOf 2 H) := by
    have h1 := card_autI_mul_card_inf hV hSVN
    have h2 : Nat.card (autI hV S) = 4 := by
      rw [hSdef, autI_nS hV hS hTM]
      exact hS.card_S hsylbar
    have h3 : S ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ pCoreOf 2 H :=
      (inf_le_inf_right _ (inf_le_left : S ≤ T)).trans hPR
    have h4 := Subgroup.card_le_of_le h3
    rw [h2] at h1
    omega
  have hY9 : Nat.card Yp ≤ 9 * Nat.card (pCoreOf 2 Yp) := by
    obtain ⟨φ, -⟩ := hh.exists_mulEquiv_imageOTwoQuot_of_le_Y153 h113 hYpY
    have h1 : Nat.card (OTwoQuot Yp) = Nat.card (imageOTwoQuot M Yp) := Nat.card_congr φ.toEquiv
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥Yp)
    have h3 : Nat.card (CFSG.Open.pCore 2 ↥Yp) = Nat.card (pCoreOf 2 Yp) :=
      (Subgroup.card_map_of_injective Yp.subtype_injective).symm
    rw [h3] at h2
    have h4 : Nat.card (OTwoQuot Yp) ≤ 9 := h1 ▸ hcardY
    calc Nat.card Yp = Nat.card (OTwoQuot Yp) * Nat.card (pCoreOf 2 Yp) := h2
      _ ≤ 9 * Nat.card (pCoreOf 2 Yp) := Nat.mul_le_mul_right _ h4
  have hcardQ : Nat.card (OTwoQuot H) ≤ 36 := by
    have h1 := card_sup_le_of_normalizer hSYp hS4 (hOYpR.trans hRS) (pCoreOf_le 2 Yp) hY9
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥H)
    rw [hcardN] at h2
    have hpos : 0 < Nat.card (pCoreOf 2 H) := Nat.card_pos
    have h3 : Nat.card (OTwoQuot H) * Nat.card (pCoreOf 2 H) ≤ 36 * Nat.card (pCoreOf 2 H) := by
      rw [← h2]
      calc Nat.card ↥H ≤ 4 * 9 * Nat.card (pCoreOf 2 H) := h1
        _ = 36 * Nat.card (pCoreOf 2 H) := by norm_num
    exact Nat.le_of_mul_le_mul_right h3 hpos
  have hNψ : CFSG.Open.pCore 2 ↥H ≤ ψ₂.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    exact hψ₂C y (hRC ((Subgroup.mem_map_iff_mem H.subtype_injective).mpr hy))
  let ψ₂' : OTwoQuot H →* Equiv.Perm (Fin 3) := QuotientGroup.lift _ ψ₂ hNψ
  have hψ₂'mk : ∀ x : ↥H, ψ₂' (QuotientGroup.mk x) = ψ₂ x := fun x => rfl
  have hψ₂'s : Function.Surjective ψ₂' := fun q => by
    obtain ⟨x, hx⟩ := hψ₂s q
    exact ⟨QuotientGroup.mk x, by rw [hψ₂'mk, hx]⟩
  have hz₀H : z₀ ∈ H := Subgroup.mem_sup_left hz₀Yp
  have hOYM : Yp ⊓ pCoreOf 2 M ≤ pCoreOf 2 H := by
    have hHn : H ≤ Subgroup.normalizer ((Yp ⊓ pCoreOf 2 M : Subgroup G) : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hHYp hg, le_normalizer_pCoreOf 2 M (hHM hg)⟩
    exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_left) hHn
      ((pCoreOf_isPGroup 2 M).to_le inf_le_right)
  have hz₀cube : z₀ ^ 3 ∈ pCoreOf 2 M := hh.cube_mem_pCoreOf_M h113 (hYpY hz₀Yp)
  have hz3 : (QuotientGroup.mk (⟨z₀, hz₀H⟩ : ↥H) : OTwoQuot H) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, mk_eq_one_iff_mem_pCoreOf]
    exact hOYM ⟨Subgroup.pow_mem _ hz₀Yp 3, hz₀cube⟩
  have hz1' : (QuotientGroup.mk (⟨z₀, hz₀H⟩ : ↥H) : OTwoQuot H) ≠ 1 := by
    intro h1
    rw [mk_eq_one_iff_mem_pCoreOf] at h1
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨z₀, h1⟩
    have hk' : z₀ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hz₀O : z₀ ∈ pCoreOf 2 M := S153D.mem_of_cube_of_pow_two_pow (pCoreOf 2 M) hz₀cube hk'
    have h2 := (mk_eq_one_iff_mem_pCoreOf (⟨z₀, hz₀M⟩ : ↥M)).2 hz₀O
    rw [hz₀z] at h2
    exact hz1 h2
  have hzK : ψ₂' (QuotientGroup.mk (⟨z₀, hz₀H⟩ : ↥H)) = 1 := hψ₂C ⟨z₀, hz₀H⟩ hz₀C
  have hr₁H : (r₁ : G) ∈ H := Subgroup.mem_sup_right hr₁S
  have hST : S ≤ T := inf_le_left
  have hr₁T : (r₁ : G) ∈ T := hST hr₁S
  have hr₁M : (r₁ : G) ∈ M := hTM hr₁T
  have hρr₁ : ρ ⟨r₁, hr₁H⟩ = s₁ := hr₁
  have hr₁sq : (r₁ : G) ^ 2 ∈ pCoreOf 2 H := by
    have h1 : convI hV (r₁ ^ 2) = 1 := by rw [map_pow, hr₁, pow_two]; exact hF.s₁_sq
    have h2 := (convI_eq_one_iff hV (r₁ ^ 2)).1 h1
    exact hPR ⟨Subgroup.pow_mem _ hr₁T 2, h2⟩
  have hr2 : (QuotientGroup.mk (⟨(r₁ : G), hr₁H⟩ : ↥H) : OTwoQuot H) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, mk_eq_one_iff_mem_pCoreOf]
    exact hr₁sq
  have hr1' : (QuotientGroup.mk (⟨(r₁ : G), hr₁H⟩ : ↥H) : OTwoQuot H) ≠ 1 := by
    intro h1
    rw [mk_eq_one_iff_mem_pCoreOf] at h1
    have h3 : convI hV r₁ = 1 := (convI_eq_one_iff hV r₁).2 (hRC h1)
    exact hF.sylow.s₁_ne (hr₁.symm.trans h3)
  have hrK : ψ₂' (QuotientGroup.mk (⟨(r₁ : G), hr₁H⟩ : ↥H)) = 1 :=
    hψ₂L₁ ⟨r₁, hr₁H⟩ (by rw [hρr₁]; exact hF.sylow.s₁_mem_L)
  have hAY : A ∈ imageOTwoQuot M (Y153 Mc M) := imageOTwoQuot_mono hKY hc.A_mem
  have hBY : B ∈ imageOTwoQuot M (Y153 Mc M) := hc.B_mem
  have hρinv : S153D.starOf hh (r₁ : G) hr₁T * ⁅A, B⁆ * (S153D.starOf hh (r₁ : G) hr₁T)⁻¹ =
      ⁅A, B⁆⁻¹ := by
    obtain ⟨e₁, e₂, he₁, he₂, ⟨⟨cA, hcA, hA⟩, ⟨cB, hcB, hB⟩⟩, hconc⟩ := hc.sign (r₁ : G) hr₁S
    have hρact : S153D.actV hh (S153D.starOf hh (r₁ : G) hr₁T) = s₁ := hr₁
    have he₂1 : e₂ = 1 := by
      rcases he₂ with h | h
      · exact h
      · exfalso
        rw [h, zpow_neg_one] at hA
        have h1 := congrArg (S153D.actV hh) hA
        have hcA1 : S153D.actV hh cA = 1 := (MonoidHom.mem_ker).1 hcA.1
        have hactA : S153D.actV hh A = convI hV ⟨a, haN⟩ := by rw [← haA]; rfl
        rw [map_mul, map_mul, map_inv, map_mul, map_inv, hcA1, mul_one, hρact, hactA] at h1
        have hcomm : s₁ * convI hV ⟨a, haN⟩ = convI hV ⟨a, haN⟩ * s₁ :=
          hS.comm s₁ hF.sylow.s₁_mem_L _ hx₂L
        have h2 : s₁ * convI hV ⟨a, haN⟩ * s₁⁻¹ = convI hV ⟨a, haN⟩ := by
          rw [hcomm]; group
        have hcube : convI hV ⟨a, haN⟩ ^ 3 = 1 := by
          have h3 := congrArg (S153D.actV hh) (S153D.star_cube h113 hh hAY)
          rw [map_pow, map_one, hactA] at h3
          exact h3
        exact hx₂1 (S153D.eq_one_of_eq_inv_of_cube hcube (h2.symm.trans h1))
    have he₁m : e₁ = -1 := by
      rcases he₁ with h | h
      · exfalso
        have h3 : convI hV r₁ = 1 := (convI_eq_one_iff hV r₁).2 (hconc h he₂1)
        exact hF.sylow.s₁_ne (hr₁.symm.trans h3)
      · exact h
    rw [he₂1, zpow_one] at hA
    rw [he₁m, zpow_neg_one] at hB
    have hcen1 : cA * (B⁻¹ * cB) = (B⁻¹ * cB) * cA :=
      S153D.Zstar_central h113 hh hcA
        ((imageOTwoQuot M (Y153 Mc M)).mul_mem ((imageOTwoQuot M (Y153 Mc M)).inv_mem hBY) hcB.2)
    have hcen2 : cB * A = A * cB := S153D.Zstar_central h113 hh hcB hAY
    have hzB : ⁅A, B⁆ * B = B * ⁅A, B⁆ := S153D.Zstar_central h113 hh hc.comm_mem hBY
    rw [S153D.conj_commutator', hA, hB, S153D.comm_mul_central_left hcen1,
      S153D.comm_mul_central_right hcen2]
    exact S153D.comm_inv_right hzB
  have hnc : (QuotientGroup.mk (⟨z₀, hz₀H⟩ : ↥H) : OTwoQuot H) *
      QuotientGroup.mk (⟨(r₁ : G), hr₁H⟩ : ↥H) ≠
      QuotientGroup.mk (⟨(r₁ : G), hr₁H⟩ : ↥H) * QuotientGroup.mk (⟨z₀, hz₀H⟩ : ↥H) := by
    intro hcomm
    rw [mk_commute_iff] at hcomm
    have hcomm' : z₀ * (r₁ : G) * z₀⁻¹ * (r₁ : G)⁻¹ ∈ pCoreOf 2 H := hcomm
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨_, hcomm'⟩
    have hk' : (z₀ * (r₁ : G) * z₀⁻¹ * (r₁ : G)⁻¹) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hdM : z₀ * (r₁ : G) * z₀⁻¹ * (r₁ : G)⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem (M.mul_mem hz₀M hr₁M) (M.inv_mem hz₀M)) (M.inv_mem hr₁M)
    have himage : (QuotientGroup.mk (⟨z₀ * (r₁ : G) * z₀⁻¹ * (r₁ : G)⁻¹, hdM⟩ : ↥M) : OTwoQuot M) =
        ⁅A, B⁆ * S153D.starOf hh (r₁ : G) hr₁T * ⁅A, B⁆⁻¹ * (S153D.starOf hh (r₁ : G) hr₁T)⁻¹ := by
      have e : (⟨z₀ * (r₁ : G) * z₀⁻¹ * (r₁ : G)⁻¹, hdM⟩ : ↥M) =
          ⟨z₀, hz₀M⟩ * ⟨(r₁ : G), hr₁M⟩ * ⟨z₀, hz₀M⟩⁻¹ * ⟨(r₁ : G), hr₁M⟩⁻¹ := rfl
      rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, hz₀z]
      rfl
    have hpow : (⁅A, B⁆ * S153D.starOf hh (r₁ : G) hr₁T * ⁅A, B⁆⁻¹ *
        (S153D.starOf hh (r₁ : G) hr₁T)⁻¹) ^ 2 ^ k = 1 := by
      rw [← himage, ← QuotientGroup.mk_pow]
      have : (⟨z₀ * (r₁ : G) * z₀⁻¹ * (r₁ : G)⁻¹, hdM⟩ : ↥M) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using hk')
      rw [this, QuotientGroup.mk_one]
    exact hz1 (eq_one_of_inv_of_commutator_pow (S153D.star_cube h113 hh hc.comm_mem.2) hρinv hpow)
  obtain ⟨e'⟩ := exists_mulEquiv_perm_three_prod ψ₂' hψ₂'s hcardQ hzK hrK hz3 hz1' hr2 hr1' hnc
  let φ : ↥H →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
    e'.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))
  refine ⟨φ, e'.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  have hΦ : frattini (OTwoQuot H) = ⊥ := frattini_eq_bot_of_mulEquiv e'
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_oTwoPhi_iff]
  constructor
  · intro h
    have h1 : (QuotientGroup.mk x : OTwoQuot H) = 1 := e'.injective (by rw [map_one]; exact h)
    refine ⟨x.2, ?_⟩
    rw [hΦ, Subgroup.mem_bot]
    exact h1
  · rintro ⟨hx, h⟩
    rw [hΦ, Subgroup.mem_bot] at h
    show e' (QuotientGroup.mk x) = 1
    rw [show (QuotientGroup.mk x : OTwoQuot H) = 1 from h, map_one]

end SBd

end CFSG.Quasithin

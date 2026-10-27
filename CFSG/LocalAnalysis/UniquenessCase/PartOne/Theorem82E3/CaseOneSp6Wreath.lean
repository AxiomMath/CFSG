module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneSp6Fusion
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Setup
import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath
import CFSG.LocalAnalysis.UniquenessCase.UC1K327Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326 (ZWr z2Of)
open CFSG.LocalAnalysis.UniquenessCase.PartOne
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (K6c K7 LieFam811 IsLie811 IsSignedCoords qPlusPi)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Case811Sylow

variable {c : Ctx82E3 D}

theorem exists_zwr (h : Case811Sylow c) (hD1 : Sp6SylowWreath) {f : ℕ}
    (hlie : IsLie811 c.Lbar .psp6 2 f) : ∃ n : ℕ, 1 ≤ n ∧ Nonempty (↥h.P ≃* ZWr n) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  have hPsylL : CFSG.ABGLocalTools.IsSylowOf 3 h.P c.L :=
    h.sylow.of_le h.P_le_L c.hyp81.1
  have hPsylLtop : CFSG.ABGLocalTools.IsSylowOf 3 (h.P.subgroupOf c.L) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (K := c.L)).mp ?_
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.P_le_L,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hPsylL
  let PX : Subgroup c.Lbar := (h.P.subgroupOf c.L).map π
  have hPXsyl : CFSG.ABGLocalTools.IsSylowOf 3 PX ⊤ := by
    have h1 := CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC327.isSylowOf_map π hPsylLtop
    simpa [PX, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective O)] using h1
  have hN3 : ¬ 3 ∣ Nat.card O :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) Nat.prime_three (by norm_num)
  have hPL3 : IsPGroup 3 (h.P.subgroupOf c.L) := h.sylow.isPGroup.comap_subtype
  have hinj : Function.Injective (π.comp (h.P.subgroupOf c.L).subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3) (N := O) hN3 hPL3
  obtain ⟨hPXle, hPXp, hPXdvd⟩ := (CFSG.ABGLocalTools.isSylowOf_iff (p := 3)).mp hPXsyl
  let Q : Sylow 3 c.Lbar := hPXp.toSylow (by simpa [Subgroup.relIndex_top_right] using hPXdvd)
  have hQ : (Q : Subgroup c.Lbar) = PX := by
    simp [Q]
  obtain ⟨n, hn, ⟨e'⟩⟩ := hD1 c.Lbar f hlie Q
  let g : ↥(h.P.subgroupOf c.L) →* c.Lbar := π.comp (h.P.subgroupOf c.L).subtype
  have hrange : g.range = PX := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let ψ : ↥(h.P.subgroupOf c.L) ≃* ↥PX :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let θ : ↥h.P ≃* ↥(h.P.subgroupOf c.L) := (Subgroup.subgroupOfEquivOfLe h.P_le_L).symm
  exact ⟨n, hn, ⟨(θ.trans ψ).trans ((MulEquiv.subgroupCongr hQ.symm).trans e')⟩⟩

def sgnAct (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3) (u : Fin 3 → ZMod 3) :
    Fin 3 → ZMod 3 := fun i => ε i * u (σ i)

private theorem sgnAct_iterate_twelve :
    ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) →
      ∀ u : Fin 3 → ZMod 3, (sgnAct σ ε)^[12] u = u := by
  unfold sgnAct
  decide +kernel

private def SgnActIsId (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3) : Prop :=
  ∀ u : Fin 3 → ZMod 3, sgnAct σ ε u = u

private instance (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3) : Decidable (SgnActIsId σ ε) := by
  unfold SgnActIsId
  infer_instance

private def SgnActCubeIsId (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3) : Prop :=
  ∀ u : Fin 3 → ZMod 3, (sgnAct σ ε)^[3] u = u

private instance (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3) :
    Decidable (SgnActCubeIsId σ ε) := by
  unfold SgnActCubeIsId
  infer_instance

private def SgnActFixes (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3)
    (w : Fin 3 → ZMod 3) : Prop :=
  w ≠ 0 ∧ (∃ i, w i = 0) ∧ sgnAct σ ε w = w

private instance (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3) (w : Fin 3 → ZMod 3) :
    Decidable (SgnActFixes σ ε w) := by
  unfold SgnActFixes
  infer_instance

private def SgnActCheck (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3) : Prop :=
  SgnActCubeIsId σ ε → (∃ w, SgnActFixes σ ε w) → SgnActIsId σ ε

private instance (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3) : Decidable (SgnActCheck σ ε) := by
  unfold SgnActCheck
  infer_instance

private theorem sgnActCheck_all :
    ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), SgnActCheck σ ε := by
  decide +kernel

private theorem gcd_twelve_pow_three_dvd (k : ℕ) : Nat.gcd 12 (3 ^ k) ∣ 3 := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (Nat.gcd_dvd_right 12 (3 ^ k))
  have h12 : Nat.gcd 12 (3 ^ k) ∣ 12 := Nat.gcd_dvd_left _ _
  rw [hi] at h12 ⊢
  rcases Nat.lt_or_ge i 2 with hi2 | hi2
  · interval_cases i <;> norm_num
  · exfalso
    have h9 : 9 ∣ 3 ^ i := by
      have : 3 ^ 2 ∣ 3 ^ i := pow_dvd_pow 3 hi2
      simpa using this
    have := h9.trans h12
    omega

private theorem sgnAct_cube_of_pow {σ : Equiv.Perm (Fin 3)} {ε : Fin 3 → ZMod 3}
    (hε : ∀ i, ε i ≠ 0) {k : ℕ} (hk : ∀ u : Fin 3 → ZMod 3, (sgnAct σ ε)^[3 ^ k] u = u) :
    SgnActCubeIsId σ ε := by
  intro u
  have h12 : Function.IsPeriodicPt (sgnAct σ ε) 12 u := sgnAct_iterate_twelve σ ε hε u
  have hk' : Function.IsPeriodicPt (sgnAct σ ε) (3 ^ k) u := hk u
  exact (h12.gcd hk').trans_dvd (gcd_twelve_pow_three_dvd k)

private theorem eq_sum_basis (u : Fin 3 → ZMod 3) :
    u = (u 0).val • (![1, 0, 0] : Fin 3 → ZMod 3) + (u 1).val • (![0, 1, 0] : Fin 3 → ZMod 3) +
      (u 2).val • (![0, 0, 1] : Fin 3 → ZMod 3) := by
  revert u
  decide +kernel

namespace SignedLift

variable {h : Case811Sylow c} (s : SignedLift h)

theorem pt_injective : Function.Injective s.pt := fun u v huv => by
  have h1 : s.ptHom (Multiplicative.ofAdd u) = s.ptHom (Multiplicative.ofAdd v) := huv
  exact Multiplicative.ofAdd.injective (s.ptHom_injective h1)

theorem exists_perm_of_mem_normalizer {g : ↥c.L}
    (hg : (g : G) ∈ Subgroup.normalizer (h.A : Set G)) :
    ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧
      ∀ u : Fin 3 → ZMod 3, (g : G) * s.pt u * (g : G)⁻¹ = s.pt (sgnAct σ ε u) := by
  classical
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)
  have hgNX : g ∈ Subgroup.normalizer ((h.A.subgroupOf c.L) : Set ↥c.L) := by
    have hgSub : g ∈ (Subgroup.normalizer (h.A : Set G)).subgroupOf c.L :=
      Subgroup.mem_subgroupOf.mpr hg
    rwa [Subgroup.subgroupOf_normalizer_eq h.A_le_L] at hgSub
  have hπg : π g ∈ Subgroup.normalizer (h.Abar : Set c.Lbar) :=
    Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hgNX)
  obtain ⟨σ, ε, hε, hform⟩ := s.signed.2.2.1 (π g) hπg
  refine ⟨σ, ε, hε, fun u => ?_⟩
  have hmem : ∀ v, s.a v ∈ h.A.subgroupOf c.L := fun v => by
    rw [← s.range]
    exact MonoidHom.mem_range.mpr ⟨v, rfl⟩
  let x : ↥c.L := g * s.a (Multiplicative.ofAdd u) * g⁻¹
  have hxX : x ∈ h.A.subgroupOf c.L := (Subgroup.mem_normalizer_iff.mp hgNX _).mp (hmem _)
  have himg : π x = π (s.a (Multiplicative.ofAdd (sgnAct σ ε u))) := by
    show π (g * s.a (Multiplicative.ofAdd u) * g⁻¹) = _
    rw [map_mul, map_mul, map_inv, s.apply, s.apply, hform]
    rfl
  have hxeq : x = s.a (Multiplicative.ofAdd (sgnAct σ ε u)) := by
    have hsub : (⟨x, hxX⟩ : h.A.subgroupOf c.L) =
        ⟨s.a (Multiplicative.ofAdd (sgnAct σ ε u)), hmem _⟩ :=
      s.inj_mk (by simpa [π] using himg)
    exact congrArg Subtype.val hsub
  have := congrArg (fun z : ↥c.L => (z : G)) hxeq
  simpa [x, pt] using this

private theorem conj_pow_pt {g : G} {σ : Equiv.Perm (Fin 3)} {ε : Fin 3 → ZMod 3}
    (hg : ∀ u : Fin 3 → ZMod 3, g * s.pt u * g⁻¹ = s.pt (sgnAct σ ε u)) (m : ℕ)
    (u : Fin 3 → ZMod 3) : g ^ m * s.pt u * (g ^ m)⁻¹ = s.pt ((sgnAct σ ε)^[m] u) := by
  induction m generalizing u with
  | zero => simp
  | succ m ih =>
    have h1 : g ^ (m + 1) * s.pt u * (g ^ (m + 1))⁻¹ =
        g * (g ^ m * s.pt u * (g ^ m)⁻¹) * g⁻¹ := by
      rw [pow_succ', mul_inv_rev]
      group
    rw [h1, ih, hg, Function.iterate_succ_apply']

theorem exists_cube_of_mem_P {g : G} (hg : g ∈ h.P) :
    ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧
      (∀ u : Fin 3 → ZMod 3, g * s.pt u * g⁻¹ = s.pt (sgnAct σ ε u)) ∧
        ∀ u : Fin 3 → ZMod 3, (sgnAct σ ε)^[3] u = u := by
  have hgL : g ∈ c.L := h.P_le_L hg
  have hgN : g ∈ Subgroup.normalizer (h.A : Set G) :=
    h.mem_normalizer_A_of_mem_normalizer_P (Subgroup.le_normalizer hg)
  obtain ⟨σ, ε, hε, hact⟩ := s.exists_perm_of_mem_normalizer (g := ⟨g, hgL⟩) hgN
  refine ⟨σ, ε, hε, hact, ?_⟩
  obtain ⟨k, hk⟩ := h.sylow.isPGroup ⟨g, hg⟩
  have hk' : g ^ 3 ^ k = 1 := congrArg Subtype.val hk
  refine sgnAct_cube_of_pow hε (k := k) fun u => ?_
  apply s.pt_injective
  have := s.conj_pow_pt hact (3 ^ k) u
  rw [hk'] at this
  simpa using this.symm

theorem exists_center_weight3 {n : ℕ} (hn : 1 ≤ n) (e : ↥h.P ≃* ZWr n) :
    ∃ w : Fin 3 → ZMod 3, (∀ i, w i ≠ 0) ∧
      (∀ g ∈ h.P, g * s.pt w = s.pt w * g) ∧
      (∀ x ∈ h.P, (∀ g ∈ h.P, g * x = x * g) → x ^ 3 = 1 →
        x ∈ Subgroup.zpowers (s.pt w)) := by
  classical
  obtain ⟨AP, hET, -, -, huniq, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.zwr_unique_E27 hn e
  let AQ : Subgroup ↥h.P := h.A.subgroupOf h.P
  have hAQ_elem : CFSG.Open.IsElemAbelian 3 AQ := h.elemAbelian.subgroupOf h.P
  have hAQ_card : Nat.card AQ = 27 := by
    change Nat.card ↥(h.A.subgroupOf h.P) = 27
    rw [← h.card_A]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.A_le).toEquiv
  have hAQ_eq : AQ = AP := huniq AQ hAQ_elem hAQ_card
  obtain ⟨hcard1, -, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.zwr_A_uniserial hn e hET
  rw [← hAQ_eq] at hcard1
  let Zc : Subgroup ↥h.P := AQ ⊓ Subgroup.center ↥h.P
  have hZc_card : Nat.card Zc = 3 := hcard1
  let Z : Subgroup G := Zc.map h.P.subtype
  have hZ_card : Nat.card Z = 3 := by
    rw [Subgroup.card_map_of_injective h.P.subtype_injective]
    exact hZc_card
  have hZ_le_A : Z ≤ h.A := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  have hZ_central : ∀ z ∈ Z, ∀ g ∈ h.P, g * z = z * g := by
    rintro _ ⟨x, hx, rfl⟩ g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx.2 ⟨g, hg⟩)
  obtain ⟨w, hw0, hZw⟩ := s.exists_pt_of_card_three hZ_le_A hZ_card
  have hpt_central : ∀ g ∈ h.P, g * s.pt w = s.pt w * g := fun g hg =>
    hZ_central _ (hZw ▸ Subgroup.mem_zpowers _) g hg
  refine ⟨w, ?_, hpt_central, ?_⟩
  · by_contra hcon
    push Not at hcon
    have hall : ∀ g ∈ h.P, ∀ u : Fin 3 → ZMod 3, g * s.pt u = s.pt u * g := by
      intro g hg u
      obtain ⟨σ, ε, hε, hact, hcube⟩ := s.exists_cube_of_mem_P hg
      have hfix : sgnAct σ ε w = w := by
        apply s.pt_injective
        rw [← hact w]
        calc g * s.pt w * g⁻¹ = (s.pt w * g) * g⁻¹ := by rw [hpt_central g hg]
          _ = s.pt w := by group
      have hid : SgnActIsId σ ε := sgnActCheck_all σ ε hcube ⟨w, hw0, hcon, hfix⟩
      have hu := hact u
      rw [hid u] at hu
      calc g * s.pt u = (g * s.pt u * g⁻¹) * g := by group
        _ = s.pt u * g := by rw [hu]
    have hAQ_le : AQ ≤ Subgroup.center ↥h.P := by
      intro x hx
      obtain ⟨u, hu⟩ := s.exists_pt_of_mem (show (x : G) ∈ h.A from hx)
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      show (g : G) * (x : G) = (x : G) * (g : G)
      rw [← hu]
      exact hall g g.2 u
    have hZcAQ : Zc = AQ := inf_eq_left.mpr hAQ_le
    rw [hZcAQ, hAQ_card] at hZc_card
    omega
  · intro x hx hxc hx3
    have hN : Zc.Normal := Subgroup.normal_of_le_center inf_le_right
    have hN1 : Zc ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hZc_card
      omega
    have hxc' : (⟨x, hx⟩ : ↥h.P) ∈ Subgroup.center ↥h.P := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hxc g g.2)
    have hx3' : (⟨x, hx⟩ : ↥h.P) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    have hmem := CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.zwr_normal_contains_omega_center
      hn e hN hN1 _ hxc' hx3'
    rw [← hZw]
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩

theorem exists_weight_one_not_mem_z2 {n : ℕ} (hn : 1 ≤ n) (e : ↥h.P ≃* ZWr n) :
    ∃ v : Fin 3 → ZMod 3, v ≠ 0 ∧ (∃ i, v i = 0) ∧
      s.pt v ∉ CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.z2Of h.P := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨AP, hET, -, -, huniq, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.zwr_unique_E27 hn e
  let AQ : Subgroup ↥h.P := h.A.subgroupOf h.P
  have hAQ_elem : CFSG.Open.IsElemAbelian 3 AQ := h.elemAbelian.subgroupOf h.P
  have hAQ_card : Nat.card AQ = 27 := by
    change Nat.card ↥(h.A.subgroupOf h.P) = 27
    rw [← h.card_A]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.A_le).toEquiv
  have hAQ_eq : AQ = AP := huniq AQ hAQ_elem hAQ_card
  obtain ⟨-, hcard2, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.zwr_A_uniserial hn e hET
  rw [← hAQ_eq] at hcard2
  let S : Subgroup ↥h.P := AQ ⊓ Subgroup.upperCentralSeries ↥h.P 2
  have hS_card : Nat.card (S.map h.P.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective h.P.subtype_injective]
    exact hcard2
  have hAQmap : AQ.map h.P.subtype = h.A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.A_le]
  have hmemS : ∀ v : Fin 3 → ZMod 3,
      s.pt v ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.z2Of h.P →
        s.pt v ∈ S.map h.P.subtype := by
    intro v hv
    rw [Subgroup.map_inf AQ (Subgroup.upperCentralSeries ↥h.P 2) h.P.subtype
      h.P.subtype_injective, hAQmap]
    exact ⟨s.pt_mem_A v, hv⟩
  let T : Subgroup (Multiplicative (Fin 3 → ZMod 3)) := (S.map h.P.subtype).comap s.ptHom
  have hTmem : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → (∃ i, v i = 0) →
      Multiplicative.ofAdd v ∈ T := fun v hv hz =>
    hmemS v (hcon v hv hz)
  have hT0 : Multiplicative.ofAdd (![1, 0, 0] : Fin 3 → ZMod 3) ∈ T :=
    hTmem _ (by decide) ⟨1, rfl⟩
  have hT1 : Multiplicative.ofAdd (![0, 1, 0] : Fin 3 → ZMod 3) ∈ T :=
    hTmem _ (by decide) ⟨0, rfl⟩
  have hT2 : Multiplicative.ofAdd (![0, 0, 1] : Fin 3 → ZMod 3) ∈ T :=
    hTmem _ (by decide) ⟨0, rfl⟩
  have hTall : ∀ u : Fin 3 → ZMod 3, Multiplicative.ofAdd u ∈ T := by
    intro u
    rw [eq_sum_basis u, ofAdd_add, ofAdd_add, ofAdd_nsmul, ofAdd_nsmul, ofAdd_nsmul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hT0 _)
      (Subgroup.pow_mem _ hT1 _)) (Subgroup.pow_mem _ hT2 _)
  have hA_le : h.A ≤ S.map h.P.subtype := by
    intro x hx
    obtain ⟨u, rfl⟩ := s.exists_pt_of_mem hx
    exact hTall u
  have := Subgroup.card_le_of_le hA_le
  rw [h.card_A, hS_card] at this
  omega

end SignedLift

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

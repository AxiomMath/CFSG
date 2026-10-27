module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.K326Dichotomy
import CFSG.GroupTheory.QuasisimpleOPrimeResidual
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneSp6Fusion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326 (K326P2S ZWr z2Of)
open CFSG.LocalAnalysis.UniquenessCase.PartOne
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (K6c K7 LieFam811 IsLie811 IsSignedCoords qPlusPi)

variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem two_le_of_dvd_qPlusPi {f p : ℕ} (hp5 : 5 ≤ p) (hpq : p ∣ qPlusPi 2 f) : 2 ≤ f := by
  by_contra hf
  push Not at hf
  interval_cases f
  · unfold qPlusPi at hpq
    norm_num at hpq
    have := Nat.le_of_dvd (by norm_num) hpq
    omega
  · unfold qPlusPi at hpq
    norm_num at hpq
    omega

namespace Case811Sylow

variable {c : Ctx82E3 D}

namespace SignedLift

variable {h : Case811Sylow c} (s : SignedLift h)

theorem relPPrimeCore_le_of_good {H : Subgroup G} (hEH : s.planeG ≤ H)
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → v 2 = 0 → GoodPoint D.M (s.pt v)) :
    CFSG.Open.relPPrimeCore 3 H ≤ D.M := by
  refine sSup_le fun N hN => ?_
  obtain ⟨hNH, hNn, hNc⟩ := hN
  have hconj : ∀ k ∈ H, ∀ y ∈ N, k * y * k⁻¹ ∈ N := fun k hk y hy =>
    (Subgroup.normal_subgroupOf_iff hNH).mp hNn y k hy hk
  have hnorm : s.planeG ≤ Subgroup.normalizer (N : Set G) := by
    intro x hx
    have hxH : x ∈ H := hEH hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hconj x hxH y hy, fun hy => ?_⟩
    have := hconj x⁻¹ (H.inv_mem hxH) _ hy
    simpa [mul_assoc] using this
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 3
    Nat.prime_three s.planeG N
    (fun m => Subtype.ext (by simpa using s.elemAbelian_planeG.2 (m : G) m.2))
    (by rw [s.card_planeG]; norm_num)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hNc) hnorm
  rw [hgen]
  refine iSup_le fun m => iSup_le fun hm => ?_
  obtain ⟨u, hu, hmu⟩ := Subgroup.mem_map.mp m.2
  have hmv : (m : G) = s.pt (Multiplicative.toAdd u) := hmu.symm
  have hv0 : Multiplicative.toAdd u ≠ 0 := by
    intro h0
    apply hm
    apply Subtype.ext
    rw [hmv, h0, pt_zero]
    rfl
  have hv2 : Multiplicative.toAdd u 2 = 0 := hu
  exact inf_le_right.trans (by rw [hmv]; exact (hgood _ hv0 hv2).centralizer_le)

theorem center_dichotomy (hK : K326P2S) {n : ℕ} (hn : 1 ≤ n) (e : ↥h.P ≃* ZWr n)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 h.P ⊤)
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M)
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → (∃ i, v i = 0) → GoodPoint D.M (s.pt v))
    {v₁ : Fin 3 → ZMod 3} (hv₁ : v₁ ≠ 0) (hv₁z : ∃ i, v₁ i = 0)
    (hv₁Z : s.pt v₁ ∉ z2Of h.P) {w : Fin 3 → ZMod 3} (hw0 : w ≠ 0)
    (hwc : ∀ g ∈ h.P, g * s.pt w = s.pt w * g)
    (hwΩ : ∀ x ∈ h.P, (∀ g ∈ h.P, g * x = x * g) → x ^ 3 = 1 →
      x ∈ Subgroup.zpowers (s.pt w)) :
    Subgroup.centralizer ((Subgroup.zpowers (s.pt w) : Subgroup G) : Set G) ≤ D.M ∨
      (n = 1 ∧ K326Exceptional
        (↥(Subgroup.centralizer ((Subgroup.zpowers (s.pt w) : Subgroup G) : Set G)) ⧸
          CFSG.pPrimeCore 3
            ↥(Subgroup.centralizer ((Subgroup.zpowers (s.pt w) : Subgroup G) : Set G)))) := by
  have hB1 : Subgroup.zpowers (s.pt w) ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact s.pt_ne_one hw0
  have hBc : ∀ x ∈ Subgroup.zpowers (s.pt w), ∀ g ∈ h.P, g * x = x * g := by
    intro x hx g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_right (hwc g hg) k).eq
  have hCa : Subgroup.centralizer ({s.pt v₁} : Set G) ≤ D.M :=
    (hgood v₁ hv₁ hv₁z).centralizer_le
  rcases h.k326_dichotomy_omega hK hn e hPG hNA (s.pt_mem_A v₁) hv₁Z hCa hB1 hBc hwΩ with
    hfirst | hexc
  · left
    have hEH : s.planeG ≤
        Subgroup.centralizer ((Subgroup.zpowers (s.pt w) : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hBc b hb x (h.A_le (s.planeG_le_A hx))).symm
    have hR := s.relPPrimeCore_le_of_good hEH (fun v hv0 hv2 => hgood v hv0 ⟨2, hv2⟩)
    exact hfirst.trans (sup_le inf_le_right hR)
  · right
    exact hexc

theorem false_of_exceptional (hN8 : K7Sp6Weight3) {f : ℕ} (hf : 2 ≤ f)
    (hlie : IsLie811 c.Lbar .psp6 2 f) {w : Fin 3 → ZMod 3} (hw3 : ∀ i, w i ≠ 0)
    (hexc : K326Exceptional
        (↥(Subgroup.centralizer ((Subgroup.zpowers (s.pt w) : Subgroup G) : Set G)) ⧸
          CFSG.pPrimeCore 3
            ↥(Subgroup.centralizer ((Subgroup.zpowers (s.pt w) : Subgroup G) : Set G)))) :
    False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Kb, hKb_le, hKb_q, hKb_3⟩ := hN8 c.Lbar f hf hlie h.Abar h.isElemAbelian_Abar
    h.card_Abar s.c₀ s.signed w hw3
  let Hw : Subgroup G := Subgroup.centralizer ((Subgroup.zpowers (s.pt w) : Subgroup G) : Set G)
  let O : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' O
  let b₀ : ↥c.L := s.a (Multiplicative.ofAdd w)
  have hb₀3 : b₀ ^ 3 = 1 := Subtype.ext (s.pt_pow_three w)
  have hN3 : ¬ 3 ∣ Nat.card O :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)) Nat.prime_three (by norm_num)
  have hQ3 : IsPGroup 3 (Subgroup.zpowers b₀) :=
    (CFSG.Open.isElemAbelian_zpowers (p := 3) hb₀3).isPGroup
  have hcen := CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := 3) (N := O) hN3 hQ3
  have hmapz : (Subgroup.zpowers b₀).map π =
      Subgroup.zpowers (s.c₀ (Multiplicative.ofAdd w)) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact s.apply _
  let CL : Subgroup ↥c.L := Subgroup.centralizer ((Subgroup.zpowers b₀ : Subgroup ↥c.L) : Set ↥c.L)
  have hKb_le' : Kb ≤ CL.map π := by
    rw [← hcen, hmapz, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hKb_le
  let f₀ : ↥CL →* c.Lbar := π.comp CL.subtype
  let K₁ : Subgroup ↥CL := Kb.comap f₀
  let α : ↥K₁ →* c.Lbar := f₀.comp K₁.subtype
  have hrange : f₀.range = CL.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hα : α.range = Kb := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    change (Kb.comap f₀).map f₀ = Kb
    rw [Subgroup.map_comap_eq, hrange, inf_eq_right.mpr hKb_le']
  have hjmem : ∀ g : ↥CL, ((g : ↥c.L) : G) ∈ Hw := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hz : b₀ ^ k ∈ Subgroup.zpowers b₀ := Subgroup.zpow_mem_zpowers b₀ k
    have := Subgroup.mem_centralizer_iff.mp g.2 (b₀ ^ k) hz
    exact congrArg Subtype.val this
  let j : ↥CL →* ↥Hw := (c.L.subtype.comp CL.subtype).codRestrict Hw hjmem
  have hj_inj : Function.Injective j := by
    intro x y hxy
    have : ((j x : ↥Hw) : G) = ((j y : ↥Hw) : G) := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  let O' : Subgroup ↥Hw := CFSG.pPrimeCore 3 ↥Hw
  let β : ↥K₁ →* (↥Hw ⧸ O') := (QuotientGroup.mk' O').comp (j.comp K₁.subtype)
  have hker : ¬ 3 ∣ Nat.card β.ker := by
    have hle : β.ker.map (j.comp K₁.subtype) ≤ O' := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp hx
    have hinj : Function.Injective (j.comp K₁.subtype) := hj_inj.comp K₁.subtype_injective
    have hd : Nat.card β.ker ∣ Nat.card O' := by
      rw [← Subgroup.card_map_of_injective hinj]
      exact Subgroup.card_dvd_of_le hle
    have hcop : ¬ 3 ∣ Nat.card O' :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥Hw))
    exact fun h3 => hcop (h3.trans hd)
  have hsolv : Group.IsSolvable ↥(CFSG.GH74.GLS.oPrimeResidual 3 (↥Hw ⧸ O')) := by
    have := Fintype.ofFinite ↥(CFSG.GH74.GLS.oPrimeResidual 3 (↥Hw ⧸ O'))
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (a := 3) (b := 4)
      (by rw [Fintype.card_eq_nat_card, hexc.2.1]; norm_num)
  have hq : CFSG.IsQuasisimple ↥α.range := by
    rw [hα]
    exact hKb_q
  have h3 : 3 ∣ Nat.card (↥α.range ⧸ Subgroup.center ↥α.range) := by
    rw [hα]
    exact hKb_3
  exact CFSG.GroupTheory.not_isSolvable_oPrimeResidual_of_quasisimple_image Nat.prime_three α β
    hq h3 hker hsolv

theorem good_center (hK : K326P2S) (hN8 : K7Sp6Weight3) {f p : ℕ}
    (hlie : IsLie811 c.Lbar .psp6 2 f) (hp : p ∈ D.sig) (hpq : p ∣ qPlusPi 2 f)
    (hdvd : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))
    {n : ℕ} (hn : 1 ≤ n) (e : ↥h.P ≃* ZWr n)
    (hPG : CFSG.ABGLocalTools.IsSylowOf 3 h.P ⊤)
    (hNA : Subgroup.normalizer (h.A : Set G) ≤ D.M)
    (hgood : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → (∃ i, v i = 0) → GoodPoint D.M (s.pt v))
    {v₁ : Fin 3 → ZMod 3} (hv₁ : v₁ ≠ 0) (hv₁z : ∃ i, v₁ i = 0)
    (hv₁Z : s.pt v₁ ∉ z2Of h.P) {w : Fin 3 → ZMod 3} (hw3 : ∀ i, w i ≠ 0)
    (hwc : ∀ g ∈ h.P, g * s.pt w = s.pt w * g)
    (hwΩ : ∀ x ∈ h.P, (∀ g ∈ h.P, g * x = x * g) → x ^ 3 = 1 →
      x ∈ Subgroup.zpowers (s.pt w)) : GoodPoint D.M (s.pt w) := by
  have hw0 : w ≠ 0 := by
    intro h0
    exact hw3 0 (by rw [h0]; rfl)
  rcases s.center_dichotomy hK hn e hPG hNA hgood hv₁ hv₁z hv₁Z hw0 hwc hwΩ with hle | ⟨-, hexc⟩
  · refine h.good_of_centralizer_le hp hdvd (s.pt_mem_A w) (s.orderOf_pt hw0) ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hle
    exact hle
  · have hf : 2 ≤ f := two_le_of_dvd_qPlusPi (c.five_le_of_mem_sigma hp) hpq
    exact (s.false_of_exceptional hN8 hf hlie hw3 hexc).elim

end SignedLift

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

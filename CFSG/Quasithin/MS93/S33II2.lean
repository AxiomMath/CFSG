module

public import CFSG.Quasithin.MS93.S33DMain
public import CFSG.Quasithin.MS93.S33LamH
public import CFSG.Quasithin.MS93.S33LamF
public import CFSG.Quasithin.MS93.S33Stmt5

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S33

theorem s33X5_of (hX2 : S33X52) :
    ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
      (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a → ⁅Xq M, L⁆ ≤ Uq M T L →
      ∀ (α' : Vtx (puAmalgam h.le)) (Y : Subgroup (puAmalgam h.le).Universal), S33Hyp h α' Y →
        Y ≤ Subgroup.centralizer (XM (puAmalgam h.le) (baseA _) : Set (puAmalgam h.le).Universal) →
        (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) = 2 ^ k →
        Xq M = Uq M T L ⊔ Zq M L := by
  intro G _ _ M T L h k F _ _ a hd hXL α' Y hS hYX hrel
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by have := hd.1; omega
    exact hX2 G M T L h F _ _ a hd hXL α' Y hS hYX (hrel.trans (pow_one 2))
  · exact s33X5_of_two_le h hd hk hXL (S5Q2.zq_le_centralizer_of_two_le h hd hk) hS hYX hrel

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem lam_hat_of_data (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {α' : Vtx (puAmalgam h.le)} {Y : Subgroup (puAmalgam h.le).Universal} (hyp : S33Hyp h α' Y)
    (hΛ : 4 ≤ (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _))) :
    ∃ t₁ ∈ Qv _ (geo _ α' (baseA _) 1), ∃ t₂ ∈ Qv _ (geo _ α' (baseA _) 1),
      ∃ t₃ ∈ Qv _ (geo _ α' (baseA _) 1),
      (∀ t ∈ ({t₁, t₂, t₃} : Set (puAmalgam h.le).Universal),
        (Subgroup.centralizer ({t} : Set (puAmalgam h.le).Universal)).relIndex (ZM _ α') = 2) ∧
      t₁ * t₂⁻¹ ∉ Qv _ α' ∧
      ZM _ (baseA _) ⊔ Qv _ α' =
        Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' ∧
      Qv _ (geo _ α' (baseA _) 1) ⊓
          Subgroup.centralizer (critR _ (baseA _) α' : Set (puAmalgam h.le).Universal) ⊔
        Qv _ α' = Subgroup.closure ({t₁, t₂, t₃} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' ∧
      ¬ Y ≤ Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := S5B.charP_two_of_card hd.2.1
  obtain ⟨-, hcard, hsurj, hnat⟩ := hd
  have hnatM := hnat
  rw [← h.Uq_inf_Zq] at hnatM
  have hc := hyp.1
  obtain ⟨g, hgα, hgβ, hμ, hgeo⟩ := exists_conj_of_isCritical _ h.hyp20 h.critDist_pos hc
  obtain ⟨hET, hYT, hYR, hYn, hrel₁, hrel₂⟩ := conj_data h hyp hgα hgβ hμ hgeo
  obtain ⟨-, -, β, hβ, hβker, hβα⟩ := id hnatM
  have hAβ := isCoordAct_of_natSp hβα
  have hEA : pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le))) ≤ M := pre_le h.le _
  set Γ := ((pre h.le (ZM _ (g⁻¹ • baseA (puAmalgam h.le)))).subgroupOf M).map a with hΓ
  have hΓcard : Nat.card Γ = (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) := by
    rw [hΓ, card_image_eq_relIndex h le_rfl (natCoordOf β hβ hβker hAβ) hEA, hrel₁,
      relIndex_qv_zm_eq h hμ]
  rcases shapes_at h hc hμ hrel₁ hrel₂ le_rfl hnatM hEA le_rfl hnatM (pre_le h.le _) with
    ⟨-, -, hP, -⟩ | ⟨-, -, hfix, -⟩
  · rw [hP, hcard] at hΛ
    norm_num at hΛ
  obtain ⟨hEab, hE2, hUE, -, -⟩ := pre_zm_props h hμ
  have hΓq : 4 ≤ Nat.card Γ := by rw [hΓcard]; exact hΛ
  have hYA : pre h.le (Y.map (MulAut.conj g⁻¹).toMonoidHom) ≤ M := hYT.trans h.le
  obtain ⟨-, hCM, hlift⟩ := Sp4L.sp4Lift_of_nat h (k := 1) le_rfl hcard hsurj hnat
  have hCfix : ∀ x ∈ M, ∀ z ∈ Uq M T L ⊓ Zq M L, x * z * x⁻¹ = z := by
    intro x hx z hz
    rw [h.Uq_inf_Zq, hCM] at hz
    rw [Subgroup.mem_centralizer_iff.mp hz.2 x hx, mul_inv_cancel_right]
  obtain ⟨hq, p, p', hp, hp', hpp, hΓeq⟩ := lam_core h le_rfl hβ hβker hAβ (k := 1) le_rfl
    hcard h.L_le hsurj hCfix hEA hEab hE2 hUE (by rw [hcard]; exact hΓq) hfix hYA hYR hYn
  have hΓ2 : IsPGroup 2 Γ := by
    rintro ⟨_, e, he, rfl⟩
    exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, ← map_pow,
      show e ^ 2 = 1 from Subtype.ext (by simpa using hE2 _ (Subgroup.mem_subgroupOf.1 he)),
      map_one, Subgroup.coe_one])⟩
  have hq' := commSp_le_fixSp_of_quadratic h le_rfl hβ hβker hAβ hEA hEab hUE
  obtain ⟨hl, -, hcf⟩ := line_of_quadratic hΓ2 hq' hfix
  have hl' : MSP.IsLine (MSP.commSp Γ) := hcf ▸ hl
  obtain ⟨t₁, ht₁, t₂, ht₂, t₃, ht₃, hi₁, hi₂, hi₃, h12, hsupE, hsup3, hYnot⟩ :=
    lam_triple h le_rfl hβ hβker hAβ hlift hq h.le hET hEab hUE hp hp' hpp hΓeq hΓq hl' hYT hYR
      hYn
  exact hat_of_pre h hgα hgβ hμ hET (hET ht₁) (hET ht₂) ht₃.1 hi₁ hi₂ hi₃ h12 hsupE hsup3 hYnot

theorem relIndex_or_hat (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} {Y : Subgroup (puAmalgam h.le).Universal} (hS : S33Hyp h α' Y) :
    (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) = 2 ^ k ∨
      ∃ t₁ t₂ t₃ : (puAmalgam h.le).Universal,
        S5.IsHatTriple _ (baseA (puAmalgam h.le)) α' t₁ t₂ t₃ ∧
          t₃ ∉ Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α' := by
  rcases shape_of_sp4Data h hd hS.1 with ⟨hrel, -, -⟩ | ⟨hΛ, -, -⟩
  · exact Or.inl hrel
  · right
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by have := hd.1; omega
      obtain ⟨t₁, ht₁, t₂, ht₂, t₃, ht₃, hidx, h12n, h12, hCY, hYn⟩ :=
        lam_hat_of_data h hd hS (by simpa using hΛ)
      have ht : S5.IsHatTriple _ (baseA (puAmalgam h.le)) α' t₁ t₂ t₃ :=
        ⟨ht₁, ht₂, ht₃, hidx t₁ (by simp), hidx t₂ (by simp), hidx t₃ (by simp), h12n, h12, hCY⟩
      exact ⟨t₁, t₂, t₃, ht, ht.not_mem_of_not_le (le_inf hS.2.1 hS.2.2.1) hYn⟩
    · exfalso
      have hsurj : Function.Surjective (a.comp (Subgroup.inclusion h.L_le)) := by
        intro y
        have hy : y ∈ (L.subgroupOf M).map a :=
          (S5B.map_L_eq_top h hd hk).symm ▸ Subgroup.mem_top y
        obtain ⟨m, hm, rfl⟩ := hy
        exact ⟨⟨m, Subgroup.mem_subgroupOf.1 hm⟩, rfl⟩
      have hnat := S5B.isSumOfNaturalModulesVia_restrict h.L_le hd.2.2.2
      rw [← h.Uq_inf_Zq] at hnat
      exact lam_false_of_two_le h hk hd.2.1 hsurj hnat hS (by rw [pow_mul']; exact hΛ)

end S33

namespace S5B

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem s33ii2_of' (hX2 : S33.S33X52) (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {Y : Subgroup (puAmalgam h.le).Universal}
    (hYT : Y ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1))
    (hYR : Y ≤ Subgroup.centralizer (critR _ (baseA (puAmalgam h.le)) α' : Set _))
    (hYX : Y ≤ Subgroup.centralizer (XM _ (baseA (puAmalgam h.le)) : Set _))
    (hY : ¬ ⁅ZM (puAmalgam h.le) α', Y⁆ ≤
      ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ⊔
        ⁅critA (puAmalgam h.le) (baseA _) α', Y⁆)
    (hYZ : ¬ ⁅Y, S5.zHat _ (baseA (puAmalgam h.le)) α'⁆ ≤ critR _ (baseA (puAmalgam h.le)) α') :
    (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k ∧
      Xq M = Uq M T L ⊔ Zq M L ∧
      (⁅⁅critA _ (baseA (puAmalgam h.le)) α', Y⁆, Y⁆ = ⊥ →
        Nat.card ↥⁅Y, critA _ (baseA (puAmalgam h.le)) α'⁆ = 2 ^ k ∧
          ⁅Y, critA _ (baseA (puAmalgam h.le)) α'⁆ ≤
            critR _ (baseA (puAmalgam h.le)) α' ⊔ stabCenter _ α') := by
  have hS : S33.S33Hyp h α' Y := ⟨hc, hYT, hYR, hY⟩
  have hrel : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k := by
    rcases S33.relIndex_or_hat h hd hS with hrel | ⟨t₁, t₂, t₃, ht, hn⟩
    · exact hrel
    · exact absurd ((Subgroup.commutator_mono (le_inf hYT hYR) le_rfl).trans
        (commutator_zHat_le_critR h hc ht hn)) hYZ
  have hXU : Xq M = Uq M T L ⊔ Zq M L :=
    S33.s33X5_of hX2 G M T L h k F _ _ a hd hXL α' Y hS hYX hrel
  exact ⟨hrel, hXU, fun hAYY =>
    S33.s33D5_holds G M T L h k F _ _ a hd hXL α' Y hS hYX hrel hXU hAYY⟩

theorem commutator_zHat_le' (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {Y : Subgroup (puAmalgam h.le).Universal}
    (hYT : Y ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1))
    (hYR : Y ≤ Subgroup.centralizer (critR _ (baseA (puAmalgam h.le)) α' : Set _))
    (hAY : ⁅critA _ (baseA (puAmalgam h.le)) α', Y⁆ = ⊥) :
    ⁅Y, S5.zHat _ (baseA (puAmalgam h.le)) α'⁆ ≤
      ⁅XM _ (baseA (puAmalgam h.le)), XM _ α'⁆ ⊔ critR _ (baseA (puAmalgam h.le)) α' := by
  by_cases hY : ⁅ZM (puAmalgam h.le) α', Y⁆ ≤
      ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ⊔
        ⁅critA (puAmalgam h.le) (baseA _) α', Y⁆
  · rw [hAY, sup_bot_eq] at hY
    rw [Subgroup.commutator_comm]
    exact ((Subgroup.commutator_mono inf_le_left le_rfl).trans hY).trans le_sup_left
  · have hS : S33.S33Hyp h α' Y := ⟨hc, hYT, hYR, hY⟩
    rcases S33.relIndex_or_hat h hd hS with hrel | ⟨t₁, t₂, t₃, ht, hn⟩
    · exfalso
      have hAYY : ⁅⁅critA _ (baseA (puAmalgam h.le)) α', Y⁆, Y⁆ = ⊥ := by
        rw [hAY, Subgroup.commutator_bot_left]
      have hge := (S33.d_main h hd hS hrel hAYY).1
      rw [Subgroup.commutator_comm, hAY, Subgroup.card_bot] at hge
      have : 2 ≤ 2 ^ k := Nat.le_self_pow (by have := hd.1; omega) 2
      omega
    · exact ((Subgroup.commutator_mono (le_inf hYT hYR) le_rfl).trans
        (commutator_zHat_le_critR h hc ht hn)).trans le_sup_right

end S5B

end CFSG.Quasithin.MS93

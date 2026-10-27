module

public import CFSG.RankThree.GF2n.Smith81.Lin26TwoModel
public import CFSG.RankThree.GF2n.Smith81.Lin26Plane

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Pointwise Matrix

section TwoModule

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {V₁ V₂ : Subgroup G}

private theorem coprime_sq_sub_one (q : ℕ) (hq : 1 ≤ q) : Nat.Coprime q (q ^ 2 - 1) := by
  have h1 : q ^ 2 - 1 + 1 = q ^ 2 := Nat.sub_add_cancel (Nat.one_le_pow _ _ hq)
  have h2 : Nat.Coprime (q ^ 2 - 1) (q ^ 2 - 1 + 1) := by simp
  rw [h1] at h2
  exact (Nat.Coprime.coprime_dvd_right (dvd_pow_self q two_ne_zero) h2).symm

theorem LinSetup.card_LB_le_two (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂) :
    Nat.card (LB M Q B) ≤ Nat.card Q * Nat.card Z := by
  have hw : Width Q Z 2 := LinSetup.width hc.hyp hS
  have hmul := hc.card_LB_mul hw
  obtain ⟨K, hK, hKfin, hKcard, φ, hrange, hker, -⟩ := hS
  have hLL : LB M Q B ≤ Lgen M (LB M Q B) := le_Lgen_self M (LB M Q B)
  have hQL : Q ≤ LB M Q B := le_sup_left
  let ψ : ↥(LB M Q B) →* GL (Fin 2) K := φ.comp (Subgroup.inclusion hLL)
  have hψker : ψ.ker = Q.subgroupOf (LB M Q B) := by
    ext x
    have h1 : ψ x = 1 ↔ φ (Subgroup.inclusion hLL x) = 1 := Iff.rfl
    rw [MonoidHom.mem_ker, h1, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    rfl
  have hcard : Nat.card (LB M Q B) = Nat.card Q * Nat.card ψ.range := by
    have h1 := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker, hψker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv] at h1
    exact h1.symm
  set r := Nat.card ψ.range with hr
  set q := Nat.card Z with hq
  have hq1 : 1 ≤ q := Nat.card_pos
  have hrL : r ∣ Nat.card (LB M Q B) := ⟨Nat.card Q, by rw [hcard, mul_comm]⟩
  have hLdvd : Nat.card (LB M Q B) ∣ q ^ 9 := by
    refine ⟨Nat.card ↥(Q ⊓ QB B), ?_⟩
    rw [hmul]
    unfold Width at hw
    rw [hw, ← pow_add]
  have hr9 : r ∣ q ^ 9 := hrL.trans hLdvd
  have hrSL : r ∣ q * (q ^ 2 - 1) := by
    have h1 : ψ.range ≤ φ.range := by
      rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    have h2 := Subgroup.card_dvd_of_le h1
    rw [hrange, StatedAPI.card_statedSL_two, hKcard] at h2
    exact h2
  have hcop : Nat.Coprime r (q ^ 2 - 1) :=
    Nat.Coprime.coprime_dvd_left hr9
      (Nat.Coprime.pow_left 9 (coprime_sq_sub_one q hq1))
  have hrq : r ∣ q := hcop.dvd_of_dvd_mul_right hrSL
  have hrle : r ≤ q := Nat.le_of_dvd Nat.card_pos hrq
  rw [hcard]
  exact Nat.mul_le_mul_left _ hrle

theorem LinSetup.card_inf_QB_ge_two (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂) :
    Nat.card Z ^ 3 ≤ Nat.card ↥(Q ⊓ QB B) := by
  have hw : Width Q Z 2 := LinSetup.width hc.hyp hS
  have hmul := hc.card_LB_mul hw
  have hle := LinSetup.card_LB_le_two hc hS
  have hQ : Nat.card Q = Nat.card Z ^ 5 := hw
  have hq : 0 < Nat.card Z := Nat.card_pos
  have hD : 0 < Nat.card ↥(Q ⊓ QB B) := Nat.card_pos
  by_contra hcon
  push Not at hcon
  have h1 : Nat.card (LB M Q B) * Nat.card ↥(Q ⊓ QB B) <
      Nat.card Q * Nat.card Z * Nat.card Z ^ 3 :=
    calc Nat.card (LB M Q B) * Nat.card ↥(Q ⊓ QB B)
        ≤ Nat.card Q * Nat.card Z * Nat.card ↥(Q ⊓ QB B) := Nat.mul_le_mul_right _ hle
      _ < Nat.card Q * Nat.card Z * Nat.card Z ^ 3 :=
        Nat.mul_lt_mul_of_pos_left hcon (Nat.mul_pos Nat.card_pos hq)
  rw [hmul, hQ] at h1
  have h2 : Nat.card Z ^ 5 * Nat.card Z ^ (2 * 2) =
      Nat.card Z ^ 5 * Nat.card Z * Nat.card Z ^ 3 := by
    ring
  omega

theorem LinSetup.inf_QB_inf_eq_two (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂)
    (hBV : B ≤ V₁) : Q ⊓ QB B ⊓ V₂ = Z := by
  obtain ⟨hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hsup, hN₁, hN₂, hc₁, hc₂⟩ := hS.basic
  have hN₂' : LB M Q B ≤ Subgroup.normalizer (V₂ : Set G) :=
    (le_Lgen_self M (LB M Q B)).trans hN₂
  have hYZ : (B ⊔ Z) ⊓ V₂ = Z := by
    refine le_antisymm ?_ (le_inf le_sup_right hZV₂)
    exact (inf_le_inf_right _ (sup_le hBV hZV₁)).trans hint.le
  exact hc.inf_QB_inf_eq_of_sup_inf hZV₂ hN₂' hYZ

theorem LinSetup.le_QB_two (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂) (hBV : B ≤ V₁) :
    V₁ ≤ QB B := by
  classical
  obtain ⟨TM⟩ := exists_tensorModel hc hS
  obtain ⟨hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hsup, hN₁, hN₂, hc₁, hc₂⟩ := hS.basic
  obtain ⟨u₁, hu₁, hP₁⟩ := TM.exists_plane_of_module hc hZV₁ hV₁Q hN₁ hc₁
  obtain ⟨u₂, hu₂, hP₂⟩ := TM.exists_plane_of_module hc hZV₂ hV₂Q hN₂ hc₂
  have hZQB : Z ≤ QB B := hc.Z_le_QB.1
  have hZD : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hZQB
  have hDQ : Q ⊓ QB B ≤ Q := inf_le_left
  have hBD : B ≤ Q ⊓ QB B := le_inf hc.le hc.B_le_QB
  have hDV₂ : Q ⊓ QB B ⊓ V₂ = Z := LinSetup.inf_QB_inf_eq_two hc hS hBV
  have hcard : Nat.card Z ^ 3 ≤ Nat.card ↥(Q ⊓ QB B) := LinSetup.card_inf_QB_ge_two hc hS
  let Δ : AddSubgroup (Matrix (Fin 2) (Fin 2) TM.F) :=
    (TM.M₀.img (Q ⊓ QB B)).map TM.Φ.toAddMonoidHom
  have hΔmem : ∀ X, X ∈ Δ ↔ ∃ e ∈ TM.M₀.img (Q ⊓ QB B), TM.Φ e = X := fun X =>
    AddSubgroup.mem_map
  have hdet : ∀ X ∈ Δ, X.det = 0 := by
    intro X hX
    obtain ⟨e, he, rfl⟩ := (hΔmem X).mp hX
    have h0 : TM.M₀.Qf e = 0 :=
      (TM.M₀.isElemAbelian_iff TM.gm.reg hDQ).mp hc.inf_QB_elemAbelian e he
    rw [← TM.qf, h0, map_zero]
  obtain ⟨b, hbB, hbZ⟩ : ∃ b ∈ B, b ∉ Z := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg⟩ := hc.conj
    have hBZ : B ≤ Z := hcon
    apply hc.ne
    refine (Subgroup.eq_of_le_of_card_ge hBZ ?_)
    rw [hg, card_conjSubgroup]
  have hbQ : b ∈ Q := hc.le hbB
  have hbV : b ∈ V₁ := hBV hbB
  have hπb : TM.M₀.π b ≠ 0 := fun h => hbZ ((TM.M₀.π_ker b hbQ).mp h)
  obtain ⟨n₀, hn₀eq⟩ : ∃ n₀ : Fin 2 → TM.F, TM.Φ (TM.M₀.π b) = Matrix.vecMulVec n₀ u₁ :=
    (hP₁ _).mp (TM.M₀.pi_mem_img hbV hbQ)
  have hn₀ : n₀ ≠ 0 := by
    rintro rfl
    rw [Matrix.zero_vecMulVec] at hn₀eq
    exact hπb (TM.Φ.injective (by rw [hn₀eq, map_zero]))
  have hbΔ : Matrix.vecMulVec n₀ u₁ ∈ Δ :=
    (hΔmem _).mpr ⟨TM.M₀.π b, TM.M₀.pi_mem_img (hBD hbB) hbQ, hn₀eq⟩
  have hintΔ : ∀ X ∈ Δ, X ∈ planeAdd u₂ → X = 0 := by
    intro X hX hX2
    obtain ⟨e, he, rfl⟩ := (hΔmem X).mp hX
    obtain ⟨d, hdD, hdQ, rfl⟩ := he
    have hdV : d ∈ V₂ := (TM.M₀.mem_img_iff hZV₂ hdQ).mp ((hP₂ _).mpr hX2)
    have hdZ : d ∈ Z := by rw [← hDV₂]; exact ⟨hdD, hdV⟩
    rw [(TM.M₀.π_ker d hdQ).mpr hdZ, map_zero]
  have hcardΔ : Nat.card TM.F ^ 2 ≤ Nat.card Δ := by
    have h1 : Nat.card Δ = Nat.card (TM.M₀.img (Q ⊓ QB B)) :=
      AddSubgroup.card_map_of_injective TM.Φ.injective
    have h2 := TM.M₀.card_eq hDQ hZD
    rw [h1, TM.card_F]
    have hz : 0 < Nat.card Z := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have h3 : Nat.card Z * Nat.card (TM.M₀.img (Q ⊓ QB B)) < Nat.card Z * Nat.card Z ^ 2 :=
      Nat.mul_lt_mul_of_pos_left hlt hz
    have h4 : Nat.card Z * Nat.card Z ^ 2 = Nat.card Z ^ 3 := by ring
    omega
  have hΔeq : Δ = planeAdd u₁ :=
    eq_planeAdd_of_isotropic hu₁ hu₂ Δ hdet hn₀ hbΔ hintΔ hcardΔ
  intro a ha
  have haQ : a ∈ Q := hV₁Q ha
  have h1 : TM.Φ (TM.M₀.π a) ∈ Δ := by
    rw [hΔeq]
    exact (hP₁ _).mp (TM.M₀.pi_mem_img ha haQ)
  obtain ⟨e, he, hΦe⟩ := (hΔmem _).mp h1
  have hπe : e = TM.M₀.π a := TM.Φ.injective hΦe
  rw [hπe] at he
  exact ((TM.M₀.mem_img_iff hZD haQ).mp he).2

theorem LinSetup.exists_swap {n : ℕ} (hS : LinSetup M Q Z B n V₁ V₂) :
    ∃ x ∈ M, conjSubgroup x V₁ = V₂ := by
  obtain ⟨K, hK, hfin, hcard, φ, hrange, hker, hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hsup,
    hs₁, hs₂, hswap, hcent⟩ := hS
  exact hswap

theorem LinSetup.inf_QB_eq_two_base (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂)
    (hBV : B ≤ V₁) : Q ⊓ QB B = V₁ := by
  obtain ⟨hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hsup, hN₁, hN₂, hc₁, hc₂⟩ := hS.basic
  have hle : V₁ ≤ QB B := LinSetup.le_QB_two hc hS hBV
  have hDV₂ : Q ⊓ QB B ⊓ V₂ = Z := LinSetup.inf_QB_inf_eq_two hc hS hBV
  refine le_antisymm (fun d hd => ?_) (le_inf hV₁Q hle)
  obtain ⟨a, ha, b, hb, rfl⟩ := LinSetup.exists_mul hc.hyp hS d hd.1
  have haD : a ∈ Q ⊓ QB B := ⟨hV₁Q ha, hle ha⟩
  have hbD : b ∈ Q ⊓ QB B := by
    have h := (Q ⊓ QB B).mul_mem ((Q ⊓ QB B).inv_mem haD) hd
    rwa [inv_mul_cancel_left] at h
  have hbZ : b ∈ Z := by rw [← hDV₂]; exact ⟨hbD, hb⟩
  exact V₁.mul_mem ha (hZV₁ hbZ)

theorem inf_QB_conj_of_mem (hH : StrothHyp M Q Z) {r : G} (hr : r ∈ M) (A : Subgroup G) :
    Q ⊓ QB (conjSubgroup r A) = conjSubgroup r (Q ⊓ QB A) := by
  have hQ : conjSubgroup r Q = Q := conjSubgroup_eq_self_iff.mpr (hH.Q_normal.2 hr)
  have hxQ : ∀ x, x ∈ Q ↔ r⁻¹ * x * r ∈ Q := fun x => by
    rw [← mem_conjSubgroup, hQ]
  rw [QB_conj]
  ext x
  simp only [Subgroup.mem_inf, mem_conjSubgroup]
  rw [hxQ x]

theorem LinSetup.exists_conj_of_le_V₁_two (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂)
    {Y : Subgroup G} (hBV : B ≤ V₁) (hY : Ctx M Q Z Y) (hYV : Y ≤ V₁) :
    ∃ r ∈ Lgen M (LB M Q B), conjSubgroup r B = Y := by
  classical
  obtain ⟨TM⟩ := exists_tensorModel hc hS
  obtain ⟨hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hsup, hN₁, hN₂, hc₁, hc₂⟩ := hS.basic
  obtain ⟨u₁, hu₁, hP₁⟩ := TM.exists_plane_of_module hc hZV₁ hV₁Q hN₁ hc₁
  have hline : ∀ {A : Subgroup G}, Ctx M Q Z A → ∃ e : TM.M₀.E, e ≠ 0 ∧
      ∀ v, v ∈ TM.M₀.img A ↔ ∃ s : TM.K, v = s • e := by
    intro A hA
    obtain ⟨g, hg⟩ := hA.conj
    have h := TM.gm.line g (by rw [← hg]; exact hA.ne) (by rw [← hg]; exact hA.le)
    rw [← hg] at h
    exact h
  obtain ⟨eB, heB0, heB⟩ := hline hc
  obtain ⟨eY, heY0, heY⟩ := hline hY
  have hmemB : eB ∈ TM.M₀.img B := (heB eB).mpr ⟨1, (one_smul _ _).symm⟩
  have hmemY : eY ∈ TM.M₀.img Y := (heY eY).mpr ⟨1, (one_smul _ _).symm⟩
  obtain ⟨nB, hnB⟩ := (hP₁ eB).mp (TM.M₀.img_mono hBV hmemB)
  obtain ⟨nY, hnY⟩ := (hP₁ eY).mp (TM.M₀.img_mono hYV hmemY)
  have hnB0 : nB ≠ 0 := by
    rintro rfl
    rw [Matrix.zero_vecMulVec] at hnB
    exact heB0 (TM.Φ.injective (by rw [hnB, map_zero]))
  have hnY0 : nY ≠ 0 := by
    rintro rfl
    rw [Matrix.zero_vecMulVec] at hnY
    exact heY0 (TM.Φ.injective (by rw [hnY, map_zero]))
  obtain ⟨g, hgdet, hgn⟩ := exists_det_one_mulVec_eq hnB0 hnY0
  obtain ⟨s, hs⟩ := TensorModel.exists_lgen_phi_eq TM g hgdet
  have hsM : (s : G) ∈ M := hc.Lgen_le_M s.2
  have hconj : conjSubgroup (s : G) B ≤ Z ⊔ Y := by
    intro x hx
    have hb : (s : G)⁻¹ * x * (s : G) ∈ B := mem_conjSubgroup.mp hx
    have hbQ : (s : G)⁻¹ * x * (s : G) ∈ Q := hc.le hb
    have hxeq : (s : G) * ((s : G)⁻¹ * x * (s : G)) * (s : G)⁻¹ = x := by group
    have hxQ : x ∈ Q := by
      rw [← hxeq]
      exact conj_mem_Q hc.hyp hsM hbQ
    obtain ⟨c, hc'⟩ := (heB _).mp (TM.M₀.pi_mem_img hb hbQ)
    have hact := TM.act s _ hbQ
    rw [hxeq] at hact
    have hΦ : TM.Φ (TM.M₀.π x) = TM.Φ (c • eY) := by
      rw [hact, hs, hc', TM.smul, hnB, Matrix.mul_smul, Matrix.mul_vecMulVec, hgn, ← hnY,
        TM.smul]
    have hπx : TM.M₀.π x = c • eY := TM.Φ.injective hΦ
    have himg : TM.M₀.π x ∈ TM.M₀.img (Z ⊔ Y) :=
      TM.M₀.img_mono le_sup_right ((heY _).mpr ⟨c, hπx⟩)
    exact (TM.M₀.mem_img_iff le_sup_left hxQ).mp himg
  obtain ⟨p, hpQ, hp⟩ := hY.exists_conj_of_le_ZB (hc.conj_of_mem hsM) hconj
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hQLg : Q ≤ Lgen M (LB M Q B) := fun x hx => le_Lgen_self M (LB M Q B) (hQL hx)
  refine ⟨p⁻¹ * (s : G), Subgroup.mul_mem _ (Subgroup.inv_mem _ (hQLg hpQ)) s.2, ?_⟩
  rw [conjSubgroup_mul, ← hp, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]

theorem LinSetup.inf_QB_eq_two (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂) (hBV : B ≤ V₁)
    {Y : Subgroup G} (hY : Ctx M Q Z Y) :
    (Y ≤ V₁ → Q ⊓ QB Y = V₁) ∧ (Y ≤ V₂ → Q ⊓ QB Y = V₂) := by
  obtain ⟨hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hsup, hN₁, hN₂, hc₁, hc₂⟩ := hS.basic
  have hbase := LinSetup.inf_QB_eq_two_base hc hS hBV
  have h1 : ∀ {A : Subgroup G}, Ctx M Q Z A → A ≤ V₁ → Q ⊓ QB A = V₁ := by
    intro A hA hAV
    obtain ⟨r, hrL, hr⟩ := LinSetup.exists_conj_of_le_V₁_two hc hS hBV hA hAV
    have hrM : r ∈ M := hc.Lgen_le_M hrL
    rw [← hr, inf_QB_conj_of_mem hc.hyp hrM, hbase]
    exact conjSubgroup_eq_self_iff.mpr (hN₁ hrL)
  refine ⟨h1 hY, fun hYV => ?_⟩
  obtain ⟨x, hxM, hx⟩ := hS.exists_swap
  have hY' : Ctx M Q Z (conjSubgroup x⁻¹ Y) := hY.conj_of_mem (M.inv_mem hxM)
  have hY'V : conjSubgroup x⁻¹ Y ≤ V₁ := by
    intro z hz
    have hz' : x * z * x⁻¹ ∈ Y := by simpa [mem_conjSubgroup] using hz
    have h2 : x * z * x⁻¹ ∈ conjSubgroup x V₁ := by rw [hx]; exact hYV hz'
    rw [mem_conjSubgroup] at h2
    simpa [mul_assoc] using h2
  have h3 := h1 hY' hY'V
  have hYeq : Y = conjSubgroup x (conjSubgroup x⁻¹ Y) := by
    rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  rw [hYeq, inf_QB_conj_of_mem hc.hyp hxM, h3, hx]

theorem LinSetup.inf_QB_eq_two_of_le (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂)
    (hBV : B ≤ V₁ ∨ B ≤ V₂) {Y : Subgroup G} (hY : Ctx M Q Z Y) :
    (Y ≤ V₁ → Q ⊓ QB Y = V₁) ∧ (Y ≤ V₂ → Q ⊓ QB Y = V₂) := by
  rcases hBV with h | h
  · exact LinSetup.inf_QB_eq_two hc hS h hY
  · exact (LinSetup.inf_QB_eq_two hc hS.symm h hY).symm

end TwoModule

end CFSG.RankThree.GF2n.Smith81

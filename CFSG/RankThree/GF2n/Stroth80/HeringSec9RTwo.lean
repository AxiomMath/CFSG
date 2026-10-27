module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9REnd
public import CFSG.RankThree.GF2n.Stroth80.HeringSec6NbarGe
public import CFSG.CGT.Timmesfeld75.Fusion

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem isSLModel_of_mulEquiv {X Y : Type} [Group X] [Group Y] {q : ℕ} (e : X ≃* Y)
    (h : IsSLModel 2 q X) : IsSLModel 2 q Y := by
  obtain ⟨K, hK, hfin, hcard, ⟨e'⟩⟩ := h
  exact ⟨K, hK, hfin, hcard, ⟨e.symm.trans e'⟩⟩

theorem mem_X_of_comm_mem_Q (hc : Ctx M Q Z B) {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {l : G}
    (hl : l ∈ LB M Q B) (hcomm : ∀ y ∈ Y, ⁅l, y⁆ ∈ Q) : l ∈ X := by
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hXM : X ≤ M := hXR.trans (hc.Rt_le_M t)
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hnorm : (LB M Q B ⊓ X) ≤ Subgroup.normalizer ((LB M Q B ⊓ Y : Subgroup G) : Set G) :=
    normalizer_of_commutator_le (X := LB M Q B ⊓ Y) (Y := LB M Q B ⊓ X)
      (le_inf hQL hQY) fun a ha y hy => by
        have := Q.inv_mem (hcXY y hy.2 a ha.2)
        rwa [commutatorElement_inv] at this
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm
    (h4.2.2 ▸ hl : l ∈ (LB M Q B ⊓ X) ⊔ (LB M Q B ⊓ Y))
  have hbQ : b ∈ Q := by
    refine mem_of_comm_mem_Q hq4 hq2 hYsl hb.2 fun y hy => ?_
    have hbe : b = a⁻¹ * l := by rw [← hab]; group
    have e : ⁅b, y⁆ = a⁻¹ * ⁅l, y⁆ * a * ⁅a⁻¹, y⁆ := by
      rw [hbe]; simp only [commutatorElement_def]; group
    rw [e]
    have h1 : ⁅a⁻¹, y⁆ ∈ Q := hcXY a⁻¹ (X.inv_mem ha.2) y hy
    have h2 : a⁻¹ * ⁅l, y⁆ * a ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hQn (M.inv_mem (hXM ha.2))) _).mp (hcomm y hy)
      simpa using this
    exact Q.mul_mem h2 h1
  rw [← hab]
  exact X.mul_mem ha.2 (hQX hbQ)

theorem relIndex_LB_inf_X (hc : Ctx M Q Z B) {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) :
    (LB M Q B ⊓ X).relIndex (LB M Q B) = Nat.card Z := by
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hnorm : (LB M Q B ⊓ Y) ≤ Subgroup.normalizer ((LB M Q B ⊓ X : Subgroup G) : Set G) :=
    normalizer_of_commutator_le (X := LB M Q B ⊓ X) (Y := LB M Q B ⊓ Y)
      (le_inf hQL hQX) fun a ha y hy => hcXY a ha.2 y hy.2
  have h1 := relIndex_sup_right_of_le_normalizer hnorm
  rw [sup_comm, ← h4.2.2] at h1
  have e : (LB M Q B ⊓ X) ⊓ (LB M Q B ⊓ Y) = Q := by
    refine le_antisymm (fun x hx => ?_) (le_inf (le_inf hQL hQX) (le_inf hQL hQY))
    have : x ∈ X ⊓ Y := ⟨hx.1.2, hx.2.2⟩
    rwa [hXYQ] at this
  have h2 : (LB M Q B ⊓ X).relIndex (LB M Q B ⊓ Y) = Q.relIndex (LB M Q B ⊓ Y) := by
    rw [← Subgroup.inf_relIndex_right (LB M Q B ⊓ X) (LB M Q B ⊓ Y), e]
  rw [h1, h2, h4.2.1]

theorem conj_Y_eq_of_conj_mem (hc : Ctx M Q Z B) {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h1 : OneConcl hc X Y) {e g : G}
    (he : e ∈ LB M Q B ⊓ X) (heQ : e ∉ Q) (hg : g ∈ M)
    (hge : g * e * g⁻¹ ∈ LB M Q B ⊓ X) : conjSubgroup g Y = Y := by
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hgeQ : g * e * g⁻¹ ∉ Q := fun h => heQ (by
    have := (Subgroup.mem_normalizer_iff.mp (hQn (M.inv_mem hg)) _).mp h
    simpa [mul_assoc] using this)
  obtain ⟨hea, hnorme, -, -⟩ := h1 e he heQ
  obtain ⟨-, -, -, huniq⟩ := h1 (g * e * g⁻¹) hge hgeQ
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  refine huniq (conjSubgroup g Y) ?_ ?_ ?_ ?_
  · intro q hq
    rw [mem_conjSubgroup]
    exact hQY (by
      have := (Subgroup.mem_normalizer_iff.mp (hQn (M.inv_mem hg)) q).mp hq
      simpa using this)
  · have hY : Y ≤ Rt M (LB M Q B) e := le_sup_right.trans hea
    calc conjSubgroup g Y ≤ conjSubgroup g (Rt M (LB M Q B) e) := Subgroup.map_mono hY
      _ = Rt M (LB M Q B) (g * e * g⁻¹) := conjSubgroup_Rt_eq hg e
  · intro r hr
    rw [← conjSubgroup_Rt_eq hg e, mem_conjSubgroup] at hr
    have h2 := hnorme _ hr
    rw [← conjSubgroup_mul r g Y, show r * g = g * (g⁻¹ * r * g) by group,
      conjSubgroup_mul, h2]
  · have h := QuotSat.conj (fun _ _ _ _ e h => isSLModel_of_mulEquiv e h) hYsl g
    rwa [hc.conj_Q_eq hg] at h

theorem odd_sq_sub_one {q : ℕ} (hq : 2 ∣ q) (hq0 : 0 < q) : Odd (q ^ 2 - 1) := by
  obtain ⟨c, rfl⟩ := hq
  have hc1 : 1 ≤ c := by omega
  have e : (2 * c) ^ 2 = 4 * (c * c) := by ring
  rw [e]
  have ht : 1 ≤ c * c := Nat.mul_pos hc1 hc1
  generalize c * c = u at ht
  exact ⟨2 * u - 1, by omega⟩

theorem conj_Y_eq_of_normalizes_LB (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y : Subgroup G} (hsplit : Split95 M Q Z B t X Y)
    (h4 : Sec4Concl M Q Z B X Y) (h1 : OneConcl hc X Y) {h : G} (hh : h ∈ M)
    (hL : conjSubgroup h (LB M Q B) = LB M Q B) : conjSubgroup h Y = Y := by
  classical
  have hs5 := hs.toSec5
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hn4 : 4 ≤ n := HS6.four_le_of_omegaPlus_two h34 hc hs5 hs.plus4
  have hcard := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.2.1
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hEidx := relIndex_LB_inf_X hc hsplit h4
  by_contra hne
  set E := LB M Q B ⊓ X with hE
  have hno : ∀ e ∈ E, e ∉ Q → h * e * h⁻¹ ∉ E := fun e he heQ hge =>
    hne (conj_Y_eq_of_conj_mem hc hsplit h1 he heQ hh hge)
  have hinf : E ⊓ conjSubgroup h E ≤ Q := by
    intro z hz
    by_contra hzQ
    have hz' : h⁻¹ * z * h ∈ E := mem_conjSubgroup.mp hz.2
    have hz'Q : h⁻¹ * z * h ∉ Q := fun hq => hzQ (by
      have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hh) _).mp hq
      simpa [mul_assoc] using this)
    refine hno _ hz' hz'Q ?_
    rw [show h * (h⁻¹ * z * h) * h⁻¹ = z by group]
    exact hz.1
  have hEc : (conjSubgroup h E).relIndex (LB M Q B) = Nat.card Z := by
    have h2 := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj h).toMonoidHom)
      E (LB M Q B) (MulAut.conj h).injective
    have h3 : (LB M Q B).map (MulAut.conj h).toMonoidHom = LB M Q B := hL
    rw [h3] at h2
    exact h2.trans hEidx
  have hle : (E ⊓ conjSubgroup h E).relIndex (LB M Q B) ≤ Nat.card Z * Nat.card Z := by
    refine (Subgroup.relIndex_inf_le (H := E) (K := conjSubgroup h E) (L := LB M Q B)).trans ?_
    rw [hEc, hEidx]
  have hdvd : Q.relIndex (LB M Q B) ∣ (E ⊓ conjSubgroup h E).relIndex (LB M Q B) :=
    Subgroup.relIndex_dvd_of_le_left (LB M Q B) hinf
  have hQrel : Q.relIndex (LB M Q B) = Nat.card Z ^ (n - 1) := by
    have h5 := Subgroup.relIndex_mul_card (H := Q) (K := LB M Q B)
    rw [inf_eq_left.mpr hQL, hcard] at h5
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h5, mul_comm])
  have hpos : 0 < (E ⊓ conjSubgroup h E).relIndex (LB M Q B) :=
    Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card _ _) Nat.card_pos
  have hle2 : Nat.card Z ^ (n - 1) ≤ Nat.card Z * Nat.card Z :=
    hQrel ▸ (Nat.le_of_dvd hpos hdvd).trans hle
  have hpow : Nat.card Z ^ 3 ≤ Nat.card Z ^ (n - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith [hpow, hle2, hq4]

theorem exists_conj_le_of_odd_relIndex {R P S : Subgroup G} (hSR : S ≤ R)
    (hP : IsPGroup 2 ↥P) (hS : IsPGroup 2 ↥S) (hidx : ¬ 2 ∣ P.relIndex R) :
    ∃ s ∈ R, S ≤ conjSubgroup s P := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₁, hS₁⟩ := (hS.comap_subtype (K := R)).exists_le_sylow
  let S₀ : Sylow 2 R := (hP.comap_subtype (K := R)).toSylow hidx
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq R S₀ S₁
  refine ⟨c, c.2, fun z hz => ?_⟩
  have hzR : z ∈ R := hSR hz
  have hmem : (⟨z, hzR⟩ : R) ∈ S₁ := hS₁ hz
  rw [← hc] at hmem
  exact mem_conjSubgroup.2 ((mem_sylow_smul_iff_inv_mul_mul_mem S₀ c ⟨z, hzR⟩).1 hmem)

theorem exists_Rt_conj_of_P (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {x k : G} (hk : k ∈ M)
    (hxk : x ∈ conjSubgroup k (LB M Q B)) {P : Subgroup G} (hP2 : IsPGroup 2 ↥P)
    (hodd : ¬ 2 ∣ P.relIndex (Rt M (LB M Q B) x))
    (hPnorm : P ≤ Subgroup.normalizer (LB M Q B : Set G)) :
    ∃ s ∈ Rt M (LB M Q B) x, conjSubgroup k (LB M Q B) = conjSubgroup s (LB M Q B) := by
  have hs5 := hs.toSec5
  have hL2 : IsPGroup 2 ↥(LB M Q B) := hc.isPGroup_LB h34 hs5.width hs5.n_gt hs5.noA2 hs5.gen
  have hkL2 : IsPGroup 2 ↥(conjSubgroup k (LB M Q B)) := by
    obtain ⟨m, hm⟩ := hL2.exists_card_eq
    exact IsPGroup.of_card (n := m) (by rw [card_conjSubgroup]; exact hm)
  have hL2R : conjSubgroup k (LB M Q B) ≤ Rt M (LB M Q B) x := conjSubgroup_le_Rt hk hxk
  obtain ⟨s, hsR, hle⟩ := exists_conj_le_of_odd_relIndex hL2R hP2 hkL2 hodd
  refine ⟨s, hsR, ?_⟩
  have hsM : s ∈ M := hc.Rt_le_M x hsR
  have hc_s := hc.conj_of_mem hsM
  have hwc := (stroth_3_5 h34 hc_s hs5.width hs5.n_gt (hc.noA2_conj hs5.noA2 hsM)
    (hs5.gen.conj_of_mem hsM)).1
  have hLs : LB M Q (conjSubgroup s B) = conjSubgroup s (LB M Q B) := hc.LB_conj hsM
  have h1' : conjSubgroup (k * s⁻¹) (LB M Q (conjSubgroup s B)) ≤
      Subgroup.normalizer (LB M Q (conjSubgroup s B) : Set G) := by
    rw [hLs, ← conjSubgroup_mul, show k * s⁻¹ * s = k by group]
    calc conjSubgroup k (LB M Q B) ≤ conjSubgroup s P := hle
      _ ≤ conjSubgroup s (Subgroup.normalizer (LB M Q B : Set G)) := Subgroup.map_mono hPnorm
      _ = Subgroup.normalizer (conjSubgroup s (LB M Q B) : Set G) := conj_normalizer s _
  have := hwc (k * s⁻¹) (M.mul_mem hk (M.inv_mem hsM)) h1'
  rwa [hLs, ← conjSubgroup_mul, show k * s⁻¹ * s = k by group] at this

theorem odd_relIndex_caseI (hc : Ctx M Q Z B) {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {x : G}
    (hxL : x ∈ LB M Q B) (hR : Rt M (LB M Q B) x = (LB M Q B ⊓ X) ⊔ Y)
    (hnorm : ∀ r ∈ Rt M (LB M Q B) x, conjSubgroup r Y = Y) :
    ¬ 2 ∣ (LB M Q B).relIndex (Rt M (LB M Q B) x) := by
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  have hqev : 2 ∣ Nat.card Z := by
    obtain ⟨s, hs'⟩ := hq2
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hs'
      omega
    rw [hs']
    exact dvd_pow_self 2 hs0
  have hqpos : 0 < Nat.card Z := Nat.card_pos
  obtain ⟨hYQn, hYmod⟩ := hYsl
  obtain ⟨hYcard, -⟩ := isSLModel_two_data hq4 hq2 hYmod
  have hQYidx : Q.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1) := hYcard
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hLR : LB M Q B ≤ Rt M (LB M Q B) x := le_Rt (M := M) (LB M Q B) hxL
  have hYRx : Y ≤ Rt M (LB M Q B) x := by rw [hR]; exact le_sup_right
  have hLN : LB M Q B ≤ Subgroup.normalizer (Y : Set G) := fun l hl =>
    conjSubgroup_eq_self_iff.mp (hnorm l (hLR hl))
  have hRL : Y ⊔ LB M Q B = Rt M (LB M Q B) x := by
    refine le_antisymm (sup_le hYRx hLR) ?_
    rw [hR]
    exact sup_le (le_trans inf_le_left le_sup_right) le_sup_left
  have hprod := card_sup_mul_card_inf_of_le_normalizer hLN
  rw [hRL] at hprod
  have e1 : (LB M Q B).relIndex (Rt M (LB M Q B) x) * Nat.card ↥(LB M Q B) =
      Nat.card ↥(Rt M (LB M Q B) x) := by
    have := Subgroup.relIndex_mul_card (H := LB M Q B) (K := Rt M (LB M Q B) x)
    rwa [inf_eq_left.mpr hLR] at this
  have e2 : Nat.card ↥(Y ⊓ LB M Q B) = Nat.card Z * Nat.card Q := by
    have := Subgroup.relIndex_mul_card (H := Q) (K := LB M Q B ⊓ Y)
    rw [inf_eq_left.mpr (le_inf hQL hQY), h4.2.1] at this
    rw [inf_comm]
    exact this.symm
  have e3 : Nat.card ↥Y = Nat.card Z * (Nat.card Z ^ 2 - 1) * Nat.card Q := by
    have := Subgroup.relIndex_mul_card (H := Q) (K := Y)
    rw [inf_eq_left.mpr hQY, hQYidx] at this
    exact this.symm
  have key : (LB M Q B).relIndex (Rt M (LB M Q B) x) * (Nat.card Z * Nat.card Q) =
      Nat.card Z * (Nat.card Z ^ 2 - 1) * Nat.card Q := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(LB M Q B))) ?_
    rw [e2, e3] at hprod
    calc (LB M Q B).relIndex (Rt M (LB M Q B) x) * (Nat.card Z * Nat.card Q) *
          Nat.card ↥(LB M Q B)
        = ((LB M Q B).relIndex (Rt M (LB M Q B) x) * Nat.card ↥(LB M Q B)) *
          (Nat.card Z * Nat.card Q) := by ring
      _ = Nat.card ↥(Rt M (LB M Q B) x) * (Nat.card Z * Nat.card Q) := by rw [e1]
      _ = _ := by rw [← hprod]
  have hpos : 0 < Nat.card Z * Nat.card Q := Nat.mul_pos hqpos Nat.card_pos
  have hrel : (LB M Q B).relIndex (Rt M (LB M Q B) x) = Nat.card Z ^ 2 - 1 := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [key]; ring
  rw [hrel]
  exact (odd_sq_sub_one hqev hqpos).not_two_dvd_nat

theorem caseII_data (h34 : Stroth34Statement) (h311a : Stroth311aStatement) (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {x : G}
    (hxL : x ∈ LB M Q B) (hxQ : x ∉ Q) (hYRx : Y ≤ Rt M (LB M Q B) x)
    (hII : OmegaPlusNat hc x 2) :
    IsPGroup 2 ↥(LB M Q B ⊔ hc.CN x) ∧
      ¬ 2 ∣ (LB M Q B ⊔ hc.CN x).relIndex (Rt M (LB M Q B) x) ∧
      LB M Q B ⊔ hc.CN x ≤ Subgroup.normalizer (LB M Q B : Set G) := by
  have hs5 := hs.toSec5
  have hsx : Sec5Hyp hc n x := ⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hxL, hxQ⟩
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  have hqev : 2 ∣ Nat.card Z := by
    obtain ⟨s, hs'⟩ := hq2
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hs'
      omega
    rw [hs']
    exact dvd_pow_self 2 hs0
  have hqpos : 0 < Nat.card Z := Nat.card_pos
  obtain ⟨hYQn, hYmod⟩ := hYsl
  obtain ⟨hYcard, -⟩ := isSLModel_two_data hq4 hq2 hYmod
  have hQYidx : Q.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1) := hYcard
  have hN2 : IsPGroup 2 ↥(hc.CN x) := isPGroup_CN h34 h311a hs hxL hxQ
  have hNR : hc.CN x ≤ Rt M (LB M Q B) x := fun y hy => (Ctx.mem_CN.mp hy).1
  have hLR : LB M Q B ≤ Rt M (LB M Q B) x := le_Rt (M := M) (LB M Q B) hxL
  have hRne : Rt M (LB M Q B) x ≠ LB M Q B := by
    intro hRL
    have hYL : Y ≤ LB M Q B := hRL ▸ hYRx
    have h2 := h4.2.1
    rw [inf_eq_right.mpr hYL, hQYidx] at h2
    have h3 : Nat.card Z ^ 2 - 1 = 1 := by
      refine Nat.eq_of_mul_eq_mul_left hqpos ?_
      rw [h2, mul_one]
    have h16 : 16 ≤ Nat.card Z ^ 2 := by nlinarith
    omega
  have hidxN : (hc.CN x).relIndex (LB M Q B) = Nat.card Z ^ 2 :=
    HS6.relIndex_omegaPlus_four_of_ne h34 hc hsx hRne hII
  have hLNn : LB M Q B ≤ Subgroup.normalizer ((hc.CN x : Subgroup G) : Set G) := fun l hl =>
    Subgroup.mem_normalizer_fintype fun y hy => hc.CN_conj_mem hxL (hLR hl) hy
  have hNnL : hc.CN x ≤ Subgroup.normalizer (LB M Q B : Set G) := fun y hy => by
    have h := hc.CN_normalizes_conj_LB h35 hxL (h := 1) (Subgroup.one_mem _) hy
    rwa [conjSubgroup_one] at h
  have hprod := card_sup_mul_card_inf_of_le_normalizer hLNn
  have e1 : (hc.CN x).relIndex (LB M Q B) * Nat.card ↥(hc.CN x ⊓ LB M Q B) =
      Nat.card ↥(LB M Q B) := Subgroup.relIndex_mul_card (hc.CN x) (LB M Q B)
  have hcardP : Nat.card ↥(LB M Q B ⊔ hc.CN x) = Nat.card Z ^ 2 * Nat.card ↥(hc.CN x) := by
    rw [sup_comm]
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(hc.CN x ⊓ LB M Q B))) ?_
    rw [hprod, ← e1, hidxN]
    ring
  have hP2 : IsPGroup 2 ↥(LB M Q B ⊔ hc.CN x) := by
    obtain ⟨a, ha⟩ := hN2.exists_card_eq
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact IsPGroup.of_card (n := 2 * e + a) (by rw [hcardP, ha, he]; ring)
  have hPR : LB M Q B ⊔ hc.CN x ≤ Rt M (LB M Q B) x := sup_le hLR hNR
  obtain ⟨K, fK, finK, hK, φ, hφ, hker, -⟩ := hII
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hRcard : Nat.card ↥(Rt M (LB M Q B) x) =
      Nat.card ↥(hc.CN x) * (Nat.card Z * (Nat.card Z ^ 2 - 1)) ^ 2 := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hker, hφ, card_omegaPlus_four (hK ▸ hq4), hK] at h1
    have h2 : Nat.card ↥((hc.CN x).subgroupOf (Rt M (LB M Q B) x)) = Nat.card ↥(hc.CN x) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNR).toEquiv
    rw [h2] at h1
    exact h1.symm
  refine ⟨hP2, ?_, sup_le Subgroup.le_normalizer hNnL⟩
  have h1 := Subgroup.relIndex_mul_card (H := LB M Q B ⊔ hc.CN x) (K := Rt M (LB M Q B) x)
  rw [inf_eq_left.mpr hPR, hcardP, hRcard] at h1
  have hpos : 0 < Nat.card Z ^ 2 * Nat.card ↥(hc.CN x) := Nat.mul_pos (pow_pos hqpos 2) Nat.card_pos
  have hrel : (LB M Q B ⊔ hc.CN x).relIndex (Rt M (LB M Q B) x) = (Nat.card Z ^ 2 - 1) ^ 2 := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1]
    ring
  rw [hrel]
  exact ((odd_sq_sub_one hqev hqpos).pow).not_two_dvd_nat

theorem exists_Rt_conj_of_mem (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) (h1 : OneConcl hc X Y)
    {x k : G} (hx : x ∈ LB M Q B ⊓ X) (hxQ : x ∉ Q) (hk : k ∈ M)
    (hxk : x ∈ conjSubgroup k (LB M Q B)) :
    ∃ s ∈ Rt M (LB M Q B) x, conjSubgroup k (LB M Q B) = conjSubgroup s (LB M Q B) := by
  obtain ⟨hea, hnorme, hdich, -⟩ := h1 x hx hxQ
  have hxL : x ∈ LB M Q B := hx.1
  have hs5 := hs.toSec5
  rcases hdich with hI | hII
  · exact exists_Rt_conj_of_P h34 hc hs hk hxk
      (hc.isPGroup_LB h34 hs5.width hs5.n_gt hs5.noA2 hs5.gen)
      (odd_relIndex_caseI hc hsplit h4 hxL hI hnorme) fun l hl => Subgroup.le_normalizer hl
  · obtain ⟨hP2, hodd, hPn⟩ := caseII_data h34 h311a hc hs hsplit h4 hxL hxQ
      (le_sup_right.trans hea) hII
    exact exists_Rt_conj_of_P h34 hc hs hk hxk hP2 hodd hPn

theorem conj_Y_eq_of_conj_mem_LB (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) (h1 : OneConcl hc X Y)
    {x g : G} (hx : x ∈ LB M Q B ⊓ X) (hxQ : x ∉ Q) (hg : g ∈ M)
    (hgx : g * x * g⁻¹ ∈ LB M Q B) : conjSubgroup g Y = Y := by
  have hxk : x ∈ conjSubgroup g⁻¹ (LB M Q B) := by
    rw [mem_conjSubgroup, inv_inv]
    exact hgx
  obtain ⟨s, hsR, hconj⟩ :=
    exists_Rt_conj_of_mem h34 h311a hc hs hsplit h4 h1 hx hxQ (M.inv_mem hg) hxk
  have hsM : s ∈ M := hc.Rt_le_M x hsR
  have hhL : conjSubgroup (g * s) (LB M Q B) = LB M Q B := by
    rw [conjSubgroup_mul, ← hconj, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  have hhY := conj_Y_eq_of_normalizes_LB h34 hc hs hsplit h4 h1 (M.mul_mem hg hsM) hhL
  have hsY : conjSubgroup s⁻¹ Y = Y := (h1 x hx hxQ).2.1 s⁻¹ ((Rt M (LB M Q B) x).inv_mem hsR)
  calc conjSubgroup g Y = conjSubgroup ((g * s) * s⁻¹) Y := by rw [mul_inv_cancel_right]
    _ = conjSubgroup (g * s) (conjSubgroup s⁻¹ Y) := conjSubgroup_mul _ _ _
    _ = Y := by rw [hsY, hhY]

end HS9

theorem sec97Two_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement) :
    Sec97TwoStatement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit h4 h1
  intro x hx g hg hgx
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  by_cases hxQ : x ∈ Q
  · have hgQ : g * x * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQn hg) x).mp hxQ
    exact ⟨hgx, hsplit.1.1 hgQ⟩
  · have hgY := HS9.conj_Y_eq_of_conj_mem_LB h34 h311a hc hs hsplit h4 h1 hx hxQ hg hgx
    refine ⟨hgx, HS9.mem_X_of_comm_mem_Q hc hsplit h4 hgx fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ Y := by
      have : y ∈ conjSubgroup g Y := by rw [hgY]; exact hy
      exact mem_conjSubgroup.mp this
    have e : ⁅g * x * g⁻¹, y⁆ = g * ⁅x, g⁻¹ * y * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hQn hg) _).mp (hsplit.1.2.2.2.2.2.2 x hx.2 _ hy')

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.RankThree.GF2n.Smith81.S81LFusion
public import CFSG.RankThree.GF2n.Smith81.Sec220Coprime

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

section Step2

variable [Finite G] {M Q Z B₀ : Subgroup G}

private theorem s5_exists_comm_ne_one (hc : Ctx M Q Z B₀) :
    ∃ d ∈ QB B₀, ∃ z₁ ∈ Z, ⁅d, z₁⁆ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hg⟩ := hc.conj
  have hQB : QB B₀ = conjSubgroup g Q := by rw [hg]; exact QB_conj_eq hc.hyp g
  have hZB : Z ≤ B₀ := by
    intro w hw
    rw [hg, mem_conjSubgroup, ← hc.hyp.centralizer_Q, Subgroup.mem_centralizer_iff]
    intro q hq
    have hgq : g * q * g⁻¹ ∈ QB B₀ := by
      rw [hQB, mem_conjSubgroup]
      have e : g⁻¹ * (g * q * g⁻¹) * g = q := by group
      rw [e]
      exact hq
    have h1 := commutatorElement_eq_one_iff_mul_comm.mp (hcon _ hgq w hw)
    calc q * (g⁻¹ * w * g) = g⁻¹ * ((g * q * g⁻¹) * w) * g := by group
      _ = g⁻¹ * (w * (g * q * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * w * g * q := by group
  have hcard : Nat.card B₀ = Nat.card Z := by rw [hg]; exact card_conjSubgroup g Z
  exact hc.ne (Subgroup.eq_of_le_of_card_ge hZB hcard.le).symm

theorem exists_conj_Z_le_sup (hctx : Ctx M Q Z B₀) {v : G} (hodd : Odd (orderOf v))
    (hvZ : ∀ y ∈ Z, v * y * v⁻¹ = y) (hB₀C : B₀ ≤ Cv v)
    (hvN : v ∈ Subgroup.normalizer (B₀ : Set G)) :
    ∃ c ∈ Cv v, conjSubgroup c Z ≠ Z ∧ ∀ x ∈ conjSubgroup c Z, ∃ b ∈ B₀, ∃ y ∈ Z, x = b * y := by
  have Hs := hctx.hyp
  obtain ⟨g, hg⟩ := hctx.conj
  have hB₀Z : IsZConjugate Z B₀ := ⟨g, hg⟩
  have hZCv : ∀ y ∈ Z, y ∈ Cv v := fun y hy => by
    refine mem_Cv.mpr ?_
    have h := hvZ y hy
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  obtain ⟨d, hdQB, z₁, hz₁, hdz⟩ := s5_exists_comm_ne_one hctx
  have hZQB : Z ≤ QB B₀ := hctx.Z_le_QB.1
  have hcommB : ∀ y ∈ Z, ⁅d, y⁆ ∈ B₀ := fun y hy =>
    IsZConjugate.comm_mem_QB Hs hB₀Z hdQB (hZQB hy)
  have hZd : ∀ x ∈ conjSubgroup d Z, (∃ b ∈ B₀, ∃ y ∈ Z, x = b * y) ∧ x ∈ Cv v := by
    intro x hx
    have hy : d⁻¹ * x * d ∈ Z := mem_conjSubgroup.mp hx
    have hxe : x = ⁅d, d⁻¹ * x * d⁆ * (d⁻¹ * x * d) := by
      rw [commutatorElement_def]
      group
    refine ⟨⟨_, hcommB _ hy, _, hy, hxe⟩, ?_⟩
    rw [hxe]
    exact (Cv v).mul_mem (hB₀C (hcommB _ hy)) (hZCv _ hy)
  have hvNQB : v ∈ Subgroup.normalizer (QB B₀ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => IsZConjugate.conj_mem_QB Hs hB₀Z hvN hx, fun hx => ?_⟩
    have h1 := IsZConjugate.conj_mem_QB Hs hB₀Z (Subgroup.inv_mem _ hvN) hx
    have e : v⁻¹ * (v * x * v⁻¹) * v⁻¹⁻¹ = x := by group
    rwa [e] at h1
  have hvz₁ : v * z₁ = z₁ * v := (mem_Cv.mp (hZCv z₁ hz₁)).symm
  have hsZd : d * z₁ * d⁻¹ ∈ conjSubgroup d Z := by
    rw [mem_conjSubgroup]
    have e : d⁻¹ * (d * z₁ * d⁻¹) * d = z₁ := by group
    rw [e]
    exact hz₁
  have hvs : v * (d * z₁ * d⁻¹) = (d * z₁ * d⁻¹) * v := (mem_Cv.mp (hZd _ hsZd).2).symm
  obtain ⟨r, hr, hre⟩ := exists_mem_centralizer_conj_of_fixed (hB₀Z.isPGroup_QB Hs) hvNQB
    hodd hvz₁ hvs hdQB rfl
  have hz₁1 : z₁ ≠ 1 := by
    rintro rfl
    exact hdz (commutatorElement_one_right d)
  have hs1 : d * z₁ * d⁻¹ ≠ 1 := by
    intro h1
    apply hz₁1
    calc z₁ = d⁻¹ * (d * z₁ * d⁻¹) * d := by group
      _ = 1 := by rw [h1]; group
  have hsZr : d * z₁ * d⁻¹ ∈ conjSubgroup r Z := by
    rw [hre, mem_conjSubgroup]
    have e : r⁻¹ * (r * z₁ * r⁻¹) * r = z₁ := by group
    rw [e]
    exact hz₁
  have hZrd : conjSubgroup r Z = conjSubgroup d Z :=
    IsZConjugate.eq_of_mem Hs ⟨r, rfl⟩ ⟨d, rfl⟩ hs1 hsZr hsZd
  refine ⟨r, hr.2, ?_, ?_⟩
  · rw [hZrd]
    intro e
    have hmem : d * z₁ * d⁻¹ ∈ Z := e ▸ hsZd
    have hcZ : ⁅d, z₁⁆ ∈ Z := by
      rw [commutatorElement_def]
      exact Z.mul_mem hmem (Z.inv_mem hz₁)
    have h0 := Subgroup.mem_inf.mpr ⟨hcZ, hcommB z₁ hz₁⟩
    rw [hctx.inf_eq_bot, Subgroup.mem_bot] at h0
    exact hdz h0
  · rw [hZrd]
    intro x hx
    exact (hZd x hx).1

theorem exists_ctx_of_mem_Qv (Hs : StrothHyp M Q Z) {v z t : G} (hz : z ∈ Z) (hvH0 : v ∈ H0 M Z)
    (hzt : IsConj z t) (htQv : t ∈ Qv Q v) (htZ : t ∉ Z) :
    ∃ B₀ : Subgroup G, Ctx M Q Z B₀ ∧ t ∈ B₀ ∧ B₀ ≤ Qv Q v ∧
      v ∈ Subgroup.normalizer (B₀ : Set G) := by
  have hvM : v ∈ M := hvH0.1
  have hyv : ∀ y ∈ Z, y * v = v * y := fun y hy => Subgroup.mem_centralizer_iff.mp hvH0.2 y hy
  have hvZ : ∀ y ∈ Z, v * y * v⁻¹ = y := fun y hy => by
    rw [← hyv y hy, mul_inv_cancel_right]
  obtain ⟨g, hg⟩ := isConj_iff.mp hzt
  have htQ : t ∈ Q := htQv.1
  have ht1 : t ≠ 1 := fun h => htZ (h ▸ Z.one_mem)
  have htB₀ : t ∈ conjSubgroup g Z := by
    rw [mem_conjSubgroup, ← hg]
    have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    rw [e]
    exact hz
  have hB₀Z : IsZConjugate Z (conjSubgroup g Z) := ⟨g, rfl⟩
  have hB₀Q : conjSubgroup g Z ≤ Q := by
    have := IsZConjugate.le_QB_of_mem Hs (IsZConjugate.self Z) hB₀Z ht1 htB₀
      (by rw [Hs.QB_Z]; exact htQ)
    rwa [Hs.QB_Z] at this
  have hB₀ne : conjSubgroup g Z ≠ Z := fun e => htZ (e ▸ htB₀)
  have hctx : Ctx M Q Z (conjSubgroup g Z) := ⟨Hs, ⟨g, rfl⟩, hB₀Q, hB₀ne⟩
  have htv : t * v = v * t := mem_Cv.mp htQv.2
  have hvt : v * t * v⁻¹ = t := by rw [← htv, mul_inv_cancel_right]
  have hvN : v ∈ Subgroup.normalizer ((conjSubgroup g Z : Subgroup G) : Set G) :=
    IsZConjugate.mem_normalizer_of_commute Hs hB₀Z ht1 htB₀ htv.symm
  have hB₀C : conjSubgroup g Z ≤ Cv v := le_Cv_of_fixed_mem hctx hvM hvZ hvN htB₀ htZ hvt
  exact ⟨conjSubgroup g Z, hctx, htB₀, fun x hx => ⟨hB₀Q hx, hB₀C hx⟩, hvN⟩

end Step2

section Main

variable [Finite G]

theorem e3l45S5_holds : E3L45S5Statement := by
  intro G _ _ M Q Z B z v hW t hzt htQv
  have Hs : StrothHyp M Q Z := hW.rem.ctx.hyp
  have hvH0 : v ∈ H0 M Z := hW.v_mem_H0
  have hodd : Odd (orderOf v) := hW.hv.2.1
  have hvM : v ∈ M := hvH0.1
  have hZQ : Z ≤ Q := Hs.Z_normal.1
  have hyv : ∀ y ∈ Z, y * v = v * y := fun y hy => Subgroup.mem_centralizer_iff.mp hvH0.2 y hy
  have hvZ : ∀ y ∈ Z, v * y * v⁻¹ = y := fun y hy => by
    rw [← hyv y hy, mul_inv_cancel_right]
  have hZQv : Z ≤ Qv Q v := fun y hy => ⟨hZQ hy, mem_Cv.mpr (hyv y hy)⟩
  have hZcent : ∀ y ∈ Z, ∀ q ∈ Q, q * y = y * q := fun y hy q hq => by
    have hy' : y ∈ Subgroup.centralizer (Q : Set G) := by rw [Hs.centralizer_Q]; exact hy
    exact Subgroup.mem_centralizer_iff.mp hy' q hq
  by_cases htZ : t ∈ Z
  · exact ⟨1, Subgroup.one_mem _, by rw [conjSubgroup_one]; exact htZ,
      by rw [conjSubgroup_one]; exact hZQv⟩
  obtain ⟨B₀, hctx, htB₀, hB₀Qv, hvN⟩ := exists_ctx_of_mem_Qv Hs hW.hz hvH0 hzt htQv htZ
  have htQ : t ∈ Q := htQv.1
  have hB₀Q : B₀ ≤ Q := fun x hx => (hB₀Qv hx).1
  have hB₀C : B₀ ≤ Cv v := fun x hx => (hB₀Qv hx).2
  obtain ⟨c₁, hc₁C, hc₁ne, hc₁le⟩ := exists_conj_Z_le_sup hctx hodd hvZ hB₀C hvN
  have hZc₁Q : conjSubgroup c₁ Z ≤ Qv Q v := by
    intro x hx
    obtain ⟨b, hb, y, hy, rfl⟩ := hc₁le x hx
    exact (Qv Q v).mul_mem ⟨hB₀Q hb, hB₀C hb⟩ (hZQv hy)
  have hZc₁Q' : conjSubgroup c₁ Z ≤ Q := fun x hx => (hZc₁Q hx).1
  have hctx₁ : Ctx M Q Z (conjSubgroup c₁ Z) := ⟨Hs, ⟨c₁, rfl⟩, hZc₁Q', hc₁ne⟩
  obtain ⟨K, _, _, _, γ, M₀, hgm⟩ := stroth_globalModelData Hs
  have hπt : M₀.π t ≠ 0 := fun h0 => htZ ((M₀.π_ker t htQ).mp h0)
  have hline₀ := Ctx.img_eq_line_of_ne hctx hgm htB₀ hπt
  have ha₀ : c₁ * z * c₁⁻¹ ∈ conjSubgroup c₁ Z := by
    rw [mem_conjSubgroup]
    have e : c₁⁻¹ * (c₁ * z * c₁⁻¹) * c₁ = z := by group
    rw [e]
    exact hW.hz
  have ha₀Z : c₁ * z * c₁⁻¹ ∉ Z := by
    intro h
    have h0 := Subgroup.mem_inf.mpr ⟨h, ha₀⟩
    rw [hctx₁.inf_eq_bot, Subgroup.mem_bot] at h0
    exact hW.hz1 (by simpa using h0)
  have ha₀Q : c₁ * z * c₁⁻¹ ∈ Q := hZc₁Q' ha₀
  have hπa₀ : M₀.π (c₁ * z * c₁⁻¹) ≠ 0 := fun h0 => ha₀Z ((M₀.π_ker _ ha₀Q).mp h0)
  obtain ⟨b₀, hb₀, y₀, hy₀, hab⟩ := hc₁le _ ha₀
  have hπab : M₀.π (c₁ * z * c₁⁻¹) = M₀.π b₀ := by
    rw [hab, M₀.π_mul b₀ (hB₀Q hb₀) y₀ (hZQ hy₀), (M₀.π_ker y₀ (hZQ hy₀)).mpr hy₀, add_zero]
  obtain ⟨s₀, hs₀⟩ := (hline₀ (M₀.π b₀)).mp (M₀.pi_mem_img hb₀ (hB₀Q hb₀))
  have hs₀0 : s₀ ≠ 0 := fun h0 => hπa₀ (by rw [hπab, hs₀, h0, zero_smul])
  have hline₁ := Ctx.img_eq_line_of_ne hctx₁ hgm ha₀ hπa₀
  obtain ⟨a, haZ, haQ, haπ⟩ := (hline₁ (M₀.π t)).mpr ⟨s₀⁻¹, by
    rw [hπab, hs₀, smul_smul, inv_mul_cancel₀ hs₀0, one_smul]⟩
  have hz₀ : a⁻¹ * t ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ haQ htQ).mp haπ
  have haQv : a ∈ Qv Q v := hZc₁Q haZ
  have haZ' : a ∉ Z := fun h0 => hπt (by rw [← haπ]; exact (M₀.π_ker a haQ).mpr h0)
  obtain ⟨x, hx, hxa⟩ := exists_comm_eq_of_mem_Qv Hs hvH0 hodd haQv haZ' hz₀
  have hta : x * a * x⁻¹ = t := by
    have h1 : x * a * x⁻¹ * a⁻¹ = a⁻¹ * t := by rw [← hxa, commutatorElement_def]
    have h2 : a * (a⁻¹ * t) = (a⁻¹ * t) * a := hZcent _ hz₀ a haQ
    calc x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
      _ = (a⁻¹ * t) * a := by rw [h1]
      _ = a * (a⁻¹ * t) := h2.symm
      _ = t := by group
  have hxta : x⁻¹ * t * x = a := by rw [← hta]; group
  refine ⟨x * c₁, (Cv v).mul_mem hx.2 hc₁C, ?_, ?_⟩
  · rw [conjSubgroup_mul, mem_conjSubgroup, hxta]
    exact haZ
  · rw [conjSubgroup_mul]
    intro y hy
    rw [mem_conjSubgroup] at hy
    have h1 : x⁻¹ * y * x ∈ Qv Q v := hZc₁Q hy
    have e : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    rw [e]
    exact (Qv Q v).mul_mem ((Qv Q v).mul_mem hx h1) ((Qv Q v).inv_mem hx)

end Main

end CFSG.RankThree.GF2n.Smith81

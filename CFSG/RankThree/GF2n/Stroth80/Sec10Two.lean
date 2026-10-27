module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec10Lagrange
public import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec57Y
public import CFSG.RankThree.GF2n.Smith81.Lin31Back
public import CFSG.RankThree.GF2n.Smith81.LinTLNoSwap
public import CFSG.RankThree.GF2n.Smith81.Sec220Conj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem Good101.exists_eq_conj_mem_B (hc : Ctx M Q Z B) {t : G}
    (ht : Good101 M Q Z B t) : ∃ g : G, ∃ b ∈ B, t = g * b * g⁻¹ := by
  obtain ⟨g₀, hg₀⟩ := hc.conj
  obtain ⟨g, z, hz, -, hgt⟩ := ht.1
  have hzB : z ∈ conjSubgroup g₀⁻¹ B := by
    rw [hg₀, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    exact hz
  have hbz : g₀ * z * g₀⁻¹ ∈ B := by simpa using mem_conjSubgroup.mp hzB
  refine ⟨g * g₀⁻¹, g₀ * z * g₀⁻¹, hbz, ?_⟩
  rw [← hgt]
  group

theorem Good101.exists_sit (hc : Ctx M Q Z B) {t : G} (ht : Good101 M Q Z B t) :
    ∃ Y : Subgroup G, Sit M Q Z Y t := by
  obtain ⟨g, z, hz, hz1, hgt⟩ := ht.1
  exact ⟨conjSubgroup g Z,
    hgt.symm ▸ Sit.of_conj hc.hyp hz hz1 (hgt.symm ▸ ht.2.1) (hgt.symm ▸ ht.2.2.1)⟩

theorem StrothHyp.le_QB_of_mem_QB (H : StrothHyp M Q Z) {X Y : Subgroup G}
    (hX : ∃ h : G, X = conjSubgroup h Z) (hY : ∃ g : G, Y = conjSubgroup g Z) {t : G}
    (htY : t ∈ Y) (ht1 : t ≠ 1) (htX : t ∈ QB X) : X ≤ QB Y := by
  by_cases hXY : X = Y
  · rw [hXY]
    obtain ⟨h, rfl⟩ := hY
    rw [QB_conj, H.QB_Z]
    exact Subgroup.map_mono H.Z_normal.1
  obtain ⟨h, rfl⟩ := hX
  obtain ⟨g, hg⟩ := hY
  have hXY' : conjSubgroup h Z ≠ conjSubgroup g Z := by
    intro hh
    exact hXY (by rw [hg]; exact hh)
  have htY' : t ∈ conjSubgroup g Z := hg ▸ htY
  have hXt : t ∉ conjSubgroup h Z := by
    intro hmem
    exact hXY' (conjSubgroup_eq_of_mem_ne_one H ht1 hmem htY')
  have hQBh : QB (conjSubgroup h Z) = conjSubgroup h Q := by
    rw [QB_conj, H.QB_Z]
  have htQ : h⁻¹ * t * h ∈ Q := by
    rw [← mem_conjSubgroup, ← hQBh]
    exact htX
  have hconj : ∃ (k z : G), z ∈ Z ∧ h⁻¹ * t * h = k * z * k⁻¹ :=
    ⟨h⁻¹ * g, g⁻¹ * t * g, mem_conjSubgroup.mp htY', by group⟩
  obtain ⟨k, hkQ, htk⟩ :=
    stroth_2_6 H htQ (fun hmem => hXt (mem_conjSubgroup.mpr hmem)) hconj
  have htF : t ∈ conjSubgroup (h * k) Z := by
    rw [mem_conjSubgroup]
    rw [show (h * k)⁻¹ * t * (h * k) = k⁻¹ * (h⁻¹ * t * h) * k from by group]
    exact mem_conjSubgroup.mp htk
  have hYX : Y = conjSubgroup (h * k) Z :=
    hg.trans (conjSubgroup_eq_of_mem_ne_one H ht1 htY' htF)
  have hYQB : Y ≤ QB (conjSubgroup h Z) := by
    rw [hYX, hQBh, conjSubgroup_mul]
    exact Subgroup.map_mono hkQ
  have hne : Y ≠ conjSubgroup h Z := by rw [hg]; exact Ne.symm hXY'
  exact H.le_QB_of_le_QB ⟨g, hg⟩ ⟨h, rfl⟩ hne hYQB

theorem Good101.le_QB_zpowers (hc : Ctx M Q Z B) {t : G} (ht : Good101 M Q Z B t) :
    B ≤ QB (Subgroup.zpowers t) := by
  obtain ⟨Y, hs⟩ := ht.exists_sit hc
  exact (hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one ht.2.2.2.1).trans
    (QB_le_QB_zpowers hs)

theorem Sec10Hyp.Vt_le (h57 : Stroth57Statement) {hc : Ctx M Q Z B} {n : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t) :
    Vt M (LB M Q B) B Z t ≤ (Q ⊓ QB (Subgroup.zpowers t)) ⊔ Z := by
  obtain ⟨m, hm, hsl⟩ := SLlike.exists_SLMNat (H.slLike ht)
  obtain ⟨g, b, hb, hgt⟩ := ht.exists_eq_conj_mem_B hc
  exact h57 G M Q Z B hc n t (H.toSec5 ht.mem_LB ht.2.2.1) (SLMNat.toSLNat hsl hm)
    ⟨g⁻¹, b, hb, by rw [hgt]; group⟩ (ht.le_QB_zpowers hc)

theorem Ctx.exists_conj_mem_of_le_sup (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) {P : Subgroup G}
    (hPQ : P ≤ Q) (hle : conjSubgroup m B ≤ P ⊔ Z) :
    ∃ w ∈ Q, ∃ a ∈ conjSubgroup (w * m) B, a ≠ 1 ∧ a ∈ P := by
  have hcC : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
  obtain ⟨c, hcC', hc1⟩ := hcC.exists_ne_one
  have hcQ : c ∈ Q := (sup_le hPQ hc.Z_le_Q) (hle hcC')
  have hcZ : c ∉ Z := by
    intro hZ
    have hmem : c ∈ Z ⊓ conjSubgroup m B := Subgroup.mem_inf.mpr ⟨hZ, hcC'⟩
    rw [hcC.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact hc1 hmem
  have hnorm : P ≤ Subgroup.normalizer (Z : Set G) :=
    fun x hx => hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hPQ hx))
  obtain ⟨a, ha, z', hz', haz⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm (hle hcC')
  have haQ : a ∈ Q := hPQ ha
  have haZ : a ∉ Z := by
    intro haZ
    exact hcZ (haz ▸ Z.mul_mem haZ hz')
  have hza : z'⁻¹ * a = a * z'⁻¹ := Z_central hc.hyp (Z.inv_mem hz') haQ
  have hcomm : a * z'⁻¹ * a⁻¹ = z'⁻¹ := by
    rw [← hza, mul_assoc, mul_inv_cancel, mul_one]
  have hmemZ : a * z'⁻¹ * a⁻¹ ∈ Z := by rw [hcomm]; exact Z.inv_mem hz'
  obtain ⟨w, hwQ, hw⟩ := exists_comm_eq hc.hyp hcQ hcZ hmemZ
  have hwca : w * c * w⁻¹ = a := by
    rw [show w * c * w⁻¹ = ⁅w, c⁆ * c by rw [commutatorElement_def]; group, hw, ← haz]
    group
  have ha_conj : a ∈ conjSubgroup (w * m) B := by
    rw [conjSubgroup_mul, ← hwca]
    exact mem_conjSubgroup.mpr (by
      rw [show w⁻¹ * (w * c * w⁻¹) * w = c by group]
      exact hcC')
  exact ⟨w, hwQ, a, ha_conj, fun h1 => haZ (h1.symm ▸ Z.one_mem), ha⟩

theorem Sec10Hyp.exists_conj_mem_QB_zpowers (h57 : Stroth57Statement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t) {m : G} (hm : m ∈ M)
    (htm : t ∈ conjSubgroup m (LB M Q B)) :
    ∃ w ∈ Q, ∃ a ∈ conjSubgroup (w * m) B, a ≠ 1 ∧ a ∈ QB (Subgroup.zpowers t) := by
  have hV : Vt M (LB M Q B) B Z t ≤ (Q ⊓ QB (Subgroup.zpowers t)) ⊔ Z :=
    Sec10Hyp.Vt_le h57 H ht
  have hCV : conjSubgroup m B ≤ Vt M (LB M Q B) B Z t := sec39_conjB_le_Vt hm htm
  obtain ⟨w, hw, a, ha, ha1, haQ⟩ :=
    Ctx.exists_conj_mem_of_le_sup (hc := hc) (m := m) (P := Q ⊓ QB (Subgroup.zpowers t))
      hm inf_le_left (hCV.trans hV)
  exact ⟨w, hw, a, ha, ha1, haQ.2⟩

theorem Ctx.mem_QB_of_inf_QB_zpowers {X Y : Subgroup G} (hX : Ctx M Q Z X) {t : G}
    (hs : Sit M Q Z Y t) {a : G} (haX : a ∈ X) (ha1 : a ≠ 1)
    (hat : a ∈ QB (Subgroup.zpowers t)) : t ∈ QB X := by
  obtain ⟨h, hXh⟩ := hX.conj
  have hatN : a ∈ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) :=
    QB_zpowers_le_normalizer hat
  have hat_comm : a * t = t * a := comm_of_mem_normalizer_zpowers hs hatN
  have hta : t * a * t⁻¹ = a := by rw [← hat_comm]; group
  have hta' : t⁻¹ * a * t = a := by
    rw [mul_assoc, hat_comm, ← mul_assoc, inv_mul_cancel, one_mul]
  have ha_conj : a ∈ conjSubgroup t X := mem_conjSubgroup.mpr (by rw [hta']; exact haX)
  have h1 : a ∈ conjSubgroup h Z := hXh ▸ haX
  have h2 : a ∈ conjSubgroup (t * h) Z := by
    rw [conjSubgroup_mul, ← hXh]
    exact ha_conj
  have hZeq : conjSubgroup h Z = conjSubgroup (t * h) Z :=
    conjSubgroup_eq_of_mem_ne_one hX.hyp ha1 h1 h2
  have hXeq : conjSubgroup t X = X := by
    rw [hXh, ← conjSubgroup_mul]
    exact hZeq.symm
  have htN : t ∈ Subgroup.normalizer (X : Set G) := conjSubgroup_eq_self_iff.mp hXeq
  have htM : t ∈ conjSubgroup h M := by
    have hN := (hX.QB_eq hXh).1
    rwa [hN] at htN
  by_contra htQB
  have htQ' : t ∉ conjSubgroup h Q := by
    have hQB := (hX.QB_eq hXh).2
    rwa [hQB] at htQB
  obtain ⟨k, hk⟩ := hs.conj
  have hconjY : Y = conjSubgroup (k * h⁻¹) (conjSubgroup h Z) := by
    rw [hk, show conjSubgroup (k * h⁻¹) (conjSubgroup h Z) = conjSubgroup (k * h⁻¹ * h) Z from
      (conjSubgroup_mul (k * h⁻¹) h Z).symm]
    congr 1
    group
  have hs' : Sit (conjSubgroup h M) (conjSubgroup h Q) (conjSubgroup h Z) Y t :=
    ⟨hX.hyp.conj h, ⟨k * h⁻¹, hconjY⟩, hs.mem, hs.ne_one, htM, htQ'⟩
  have hbot := Z_inf_QB_zpowers hs'
  have hamem : a ∈ conjSubgroup h Z ⊓ QB (Subgroup.zpowers t) :=
    Subgroup.mem_inf.mpr ⟨hXh ▸ haX, hat⟩
  rw [hbot, Subgroup.mem_bot] at hamem
  exact ha1 hamem

theorem Ctx.exists_comm_eq_of_mem_QB {X : Subgroup G} (hX : Ctx M Q Z X) {n : ℕ}
    (hw : Width Q Z n) (hn : 1 ≤ n) (hno : NoA2 Q Z (LB M Q X)) {t : G} (htX : t ∈ QB X)
    (htQ : t ∉ Q) {v : G} (hv : v ∈ X) : ∃ a ∈ Q ⊓ QB X, ⁅t, a⁆ = v := by
  obtain ⟨h, hXh⟩ := hX.conj
  have hQB : QB X = conjSubgroup h Q := (hX.QB_eq hXh).2
  have h33 := hX.card_of_3_3 hw hn hno (stroth_3_3 hX hw hn)
  have hAcard : Nat.card ↥(Q ⊓ QB X) = Nat.card Z ^ (n + 1) := h33.2
  have hQcard : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hw
  have hcard : Nat.card ↥(Q ⊓ QB X) ^ 2 =
      Nat.card (conjSubgroup h Q) * Nat.card (conjSubgroup h Z) := by
    rw [card_conjSubgroup, card_conjSubgroup, hAcard, hQcard]
    have h1 : (Nat.card Z ^ (n + 1)) ^ 2 = Nat.card Z ^ (2 * n + 2) := by
      rw [show 2 * n + 2 = (n + 1) * 2 by omega, pow_mul]
    have h2 : Nat.card Z ^ (2 * n + 1) * Nat.card Z = Nat.card Z ^ (2 * n + 2) := by
      conv_rhs => rw [show 2 * n + 2 = 2 * n + 1 + 1 by omega, pow_succ]
    rw [h1, h2]
  have hAab : ∀ a ∈ Q ⊓ QB X, ∀ b ∈ Q ⊓ QB X, a * b = b * a := by
    haveI : IsMulCommutative ↥(Q ⊓ QB X) := hX.inf_QB_elemAbelian.1
    exact fun a ha b hb => Subgroup.mul_comm_of_mem_isMulCommutative (H := Q ⊓ QB X) ha hb
  exact StrothHyp.exists_comm_eq_of_lagrangian (hX.hyp.conj h) (A := Q ⊓ QB X)
    (by rw [hQB]; exact inf_le_right)
    (fun x hx => Subgroup.mem_inf.mpr
      ⟨hX.le (hXh.symm ▸ hx), hX.B_le_QB (hXh.symm ▸ hx)⟩)
    hAab hcard (by rw [← hQB]; exact htX)
    (fun hmem => htQ (Subgroup.mem_inf.mp hmem).1)
    (by rw [← hXh]; exact hv)

private theorem commute_inv_mul_of_commutator_eq {t a y : G} (h : ⁅t, a⁆ = ⁅t, y⁆) :
    t * (a⁻¹ * y) = (a⁻¹ * y) * t := by
  have h' : t * a * t⁻¹ * a⁻¹ = t * y * t⁻¹ * y⁻¹ := by
    simpa [commutatorElement_def] using h
  have key : a * t⁻¹ * a⁻¹ = y * t⁻¹ * y⁻¹ := by
    have h2 : t * (a * t⁻¹ * a⁻¹) = t * (y * t⁻¹ * y⁻¹) := by
      rw [show t * (a * t⁻¹ * a⁻¹) = t * a * t⁻¹ * a⁻¹ by group,
        show t * (y * t⁻¹ * y⁻¹) = t * y * t⁻¹ * y⁻¹ by group, h']
    exact mul_left_cancel h2
  have key2 : y⁻¹ * a * t⁻¹ = t⁻¹ * y⁻¹ * a := by
    have h3 : y⁻¹ * (a * t⁻¹ * a⁻¹) * a = y⁻¹ * (y * t⁻¹ * y⁻¹) * a := by rw [key]
    rwa [show y⁻¹ * (a * t⁻¹ * a⁻¹) * a = y⁻¹ * a * t⁻¹ by group,
      show y⁻¹ * (y * t⁻¹ * y⁻¹) * a = t⁻¹ * y⁻¹ * a by group] at h3
  calc t * (a⁻¹ * y) = (y⁻¹ * a * t⁻¹)⁻¹ := by group
    _ = (t⁻¹ * y⁻¹ * a)⁻¹ := by rw [key2]
    _ = (a⁻¹ * y) * t := by group

theorem Ctx.LB_le_sup_centralizer {X : Subgroup G} (hX : Ctx M Q Z X) {n : ℕ}
    (hw : Width Q Z n) (hn : 1 ≤ n) (hno : NoA2 Q Z (LB M Q X)) {t : G} (htX : t ∈ QB X)
    (htQ : t ∉ Q) :
    LB M Q X ≤ Q ⊔ (LB M Q X ⊓ Subgroup.centralizer ({t} : Set G)) := by
  refine sup_le le_sup_left ?_
  intro y hy
  obtain ⟨hyQB, hyM⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨a, ha, hav⟩ := hX.exists_comm_eq_of_mem_QB hw hn hno htX htQ (hX.comm_QB_le_B htX hyQB)
  have haQ : a ∈ Q := (Subgroup.mem_inf.mp ha).1
  have hcomm : t * (a⁻¹ * y) = (a⁻¹ * y) * t := commute_inv_mul_of_commutator_eq hav
  have hmem : a⁻¹ * y ∈ LB M Q X ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (LB M Q X).mul_mem ((LB M Q X).inv_mem (sec39_Q_le_LB haQ))
        (Subgroup.mem_sup_right ⟨hyQB, hyM⟩)
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hcomm
  have hy : y = a * (a⁻¹ * y) := by group
  rw [hy]
  exact Subgroup.mul_mem_sup haQ hmem

theorem stroth_10_2 (h57 : Stroth57Statement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec10Hyp hc n → Good101 M Q Z B t →
        Rt M (LB M Q B) t = Q ⊔ (Rt M (LB M Q B) t ⊓ Subgroup.centralizer ({t} : Set G)) := by
  intro G _ _ M Q Z B hc n t H ht
  have hle : Rt M (LB M Q B) t ≤
      Q ⊔ (Rt M (LB M Q B) t ⊓ Subgroup.centralizer ({t} : Set G)) := by
    refine iSup₂_le fun m hm => iSup_le fun htm => ?_
    obtain ⟨w, hwQ, a, ha, ha1, haQB⟩ := H.exists_conj_mem_QB_zpowers h57 ht hm htm
    have hwm : w * m ∈ M := M.mul_mem (hc.hyp.Q_normal.1 hwQ) hm
    have hX : Ctx M Q Z (conjSubgroup (w * m) B) := hc.conj_of_mem hwm
    have hno : NoA2 Q Z (LB M Q (conjSubgroup (w * m) B)) := hc.noA2_conj H.noA2 hwm
    obtain ⟨Y, hs⟩ := ht.exists_sit hc
    have htX : t ∈ QB (conjSubgroup (w * m) B) :=
      hX.mem_QB_of_inf_QB_zpowers hs ha ha1 haQB
    have hwLB : w ∈ conjSubgroup m (LB M Q B) := by
      have h1 : w ∈ conjSubgroup m Q := by
        rw [hc.conj_Q_eq hm]
        exact hwQ
      exact Subgroup.map_mono sec39_Q_le_LB h1
    have hLB : LB M Q (conjSubgroup (w * m) B) = conjSubgroup m (LB M Q B) := by
      rw [hc.LB_conj hwm, conjSubgroup_mul,
        conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hwLB)]
    have hmain := hX.LB_le_sup_centralizer H.width (by have := H.n_gt; omega : 1 ≤ n)
      hno htX ht.2.2.1
    rw [hLB] at hmain
    have hsub : conjSubgroup m (LB M Q B) ≤ Rt M (LB M Q B) t :=
      le_iSup₂_of_le m hm (le_iSup_of_le htm le_rfl)
    exact hmain.trans (sup_le_sup (le_refl Q) (inf_le_inf_right _ hsub))
  refine le_antisymm hle ?_
  exact sup_le (hc.Q_le_Rt ht.mem_LB) inf_le_left

end CFSG.RankThree.GF2n.Stroth80

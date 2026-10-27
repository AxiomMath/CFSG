module

public import CFSG.RankThree.GF2n.Stroth80.Sec84Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec8RtConj
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GroupTheory.SteinbergBY
  (isPGroup_inSubgroup_pCore le_inSubgroup_pCore le_normalizer_inSubgroup_pCore mem_normalizer_inf)
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_exists_Z0_not_Q (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : ∃ s ∈ Z0, s ∉ Q := by
  by_contra h
  push_neg at h
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre hs.toSec5.mem hZ0
  have hcard := sec86ZCard_of_51 h51 hA G M Q Z B hc n t hs Z0 hZ0
  have heq : Z0 = Q := le_antisymm h hQZ0
  rw [heq] at hcard
  have hq : 4 ≤ Nat.card Z := hc.hyp.q4
  have hpos : 0 < Nat.card Q := Nat.card_pos
  nlinarith

theorem sec8_normalizes_of_zt (hZt : Sec8ZtStatement) (h51 : Stroth51Statement)
    (hA : Sec8AExistsStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g : G}
    (hg : g ∈ NormH0 M Z Z0) :
    conjSubgroup g (Rt M (LB M Q B) t) = Rt M (LB M Q B) t ∧
      conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t := by
  obtain ⟨s, hsZ0, hsQ⟩ := sec8_exists_Z0_not_Q h51 hA hc hs hZ0
  have hgM : g ∈ M := hg.1.1
  have hgN : g ∈ Subgroup.normalizer (Z0 : Set G) := hg.2
  have hs' : g * s * g⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp hgN s).mp hsZ0
  have hs'Q : g * s * g⁻¹ ∉ Q := by
    intro h
    apply hsQ
    have h2 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hgM)) _).mp h
    simpa [mul_assoc] using h2
  obtain ⟨hR1, hV1⟩ := hZt G M Q Z B hc n t hs Z0 hZ0 s hsZ0 hsQ
  obtain ⟨hR2, hV2⟩ := hZt G M Q Z B hc n t hs Z0 hZ0 (g * s * g⁻¹) hs' hs'Q
  refine ⟨?_, ?_⟩
  · calc conjSubgroup g (Rt M (LB M Q B) t) = conjSubgroup g (Rt M (LB M Q B) s) := by rw [hR1]
      _ = Rt M (LB M Q B) (g * s * g⁻¹) := conjSubgroup_Rt_eq hgM s
      _ = Rt M (LB M Q B) t := hR2
  · calc conjSubgroup g (Vt M (LB M Q B) B Z t) = conjSubgroup g (Vt M (LB M Q B) B Z s) := by
          rw [hV1]
      _ = Vt M (LB M Q B) B Z (g * s * g⁻¹) :=
          conjSubgroup_Vt_eq hgM (hc.conj_Z_eq hgM) s
      _ = Vt M (LB M Q B) B Z t := hV2

theorem mem_CN_conj_of_normalizes (hc : Ctx M Q Z B) {t g x : G} (hgM : g ∈ M)
    (hR : conjSubgroup g (Rt M (LB M Q B) t) = Rt M (LB M Q B) t)
    (hV : conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t)
    (hx : x ∈ hc.CN t) : g * x * g⁻¹ ∈ hc.CN t := by
  obtain ⟨hxR, hxV⟩ := Ctx.mem_CN.mp hx
  refine Ctx.mem_CN.mpr ⟨?_, fun v hv => ?_⟩
  · exact ((Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp hR) x).mp hxR)
  · have hgv : g⁻¹ * v * g ∈ Vt M (LB M Q B) B Z t := by
      have h := (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp hV)
        (g⁻¹ * v * g)).mpr (by simpa [mul_assoc] using hv)
      exact h
    have h1 := hxV _ hgv
    have h2 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hgM) _).mp h1
    have e : g * ⁅x, g⁻¹ * v * g⁆ * g⁻¹ = ⁅g * x * g⁻¹, v⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h2

theorem conjSubgroup_CN_eq (hc : Ctx M Q Z B) {t g : G} (hgM : g ∈ M)
    (hR : conjSubgroup g (Rt M (LB M Q B) t) = Rt M (LB M Q B) t)
    (hV : conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t) :
    conjSubgroup g (hc.CN t) = hc.CN t := by
  refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) (by rw [card_conjSubgroup])
  have hy' := (mem_conjSubgroup).mp hy
  have := mem_CN_conj_of_normalizes hc hgM hR hV hy'
  simpa [mul_assoc] using this

theorem sec8_Rt_le_NormH0 (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : Rt M (LB M Q B) t ≤ NormH0 M Z Z0 := by
  have hnormR : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  exact fun ρ hρ =>
    Subgroup.mem_inf.mpr ⟨hc.Rt_le_H0 t hρ, IsCentrePre.mem_normalizer hZ0 hnormR hρ⟩

theorem step85CNNormal_of_zt (hZt : Sec8ZtStatement) (h51 : Stroth51Statement)
    (hA : Sec8AExistsStatement) (hNt : StrothNtStatement) : Step85CNNormalStatement := by
  intro G _ _ M Q Z B _ hc n t hs Z0 hZ0
  have h5 := hs.toSec5
  have hCN2 : IsPGroup 2 ↥(hc.CN t) := by
    have h := hNt G M Q Z B hc n h5.width h5.n_gt h5.noA2 h5.gen t h5.mem h5.notQ
    rw [← h]
    exact isPGroup_inSubgroup_pCore 2 _
  set π := QuotientGroup.mk' (Q.subgroupOf M) with hπ
  have hbar2 : IsPGroup 2 ↥(bar M Q (hc.CN t)) := by
    have h1 : IsPGroup 2 ↥((hc.CN t).subgroupOf M) := hCN2.comap_subtype
    exact h1.map π
  have hNb2 : IsPGroup 2 ↥((bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))) :=
    hbar2.comap_subtype
  have hNbN : ((bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨c, hcmem, hcn⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hn)
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp g.2
    have hkK : (k : G) ∈ NormH0 M Z Z0 := Subgroup.mem_subgroupOf.mp hk
    obtain ⟨hkR, hkV⟩ := sec8_normalizes_of_zt hZt h51 hA hc hs hZ0 hkK
    have hcCN : (c : G) ∈ hc.CN t := Subgroup.mem_subgroupOf.mp hcmem
    have hkcCN : ((k * c * k⁻¹ : ↥M) : G) ∈ hc.CN t :=
      mem_CN_conj_of_normalizes hc k.2 hkR hkV hcCN
    rw [Subgroup.mem_subgroupOf]
    show (g : Mbar M Q) * (n : Mbar M Q) * (g : Mbar M Q)⁻¹ ∈ bar M Q (hc.CN t)
    rw [← hkg, ← hcn, ← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hkcCN)
  exact le_sSup ⟨hNbN, hNb2⟩

theorem sec85First_a (hZt : Sec8ZtStatement) (h51 : Stroth51Statement)
    (hA : Sec8AExistsStatement) (hNt : StrothNtStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec8Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {x : G}
    (hx : x ∈ inSubgroup (pCore 2) (NormH0 M Z Z0)) {ρ : G} (hρ : ρ ∈ Rt M (LB M Q B) t) :
    ⁅x, ρ⁆ ∈ hc.CN t := by
  have h5 := hs.toSec5
  have hRK := sec8_Rt_le_NormH0 hc hZ0
  have hxK : x ∈ NormH0 M Z Z0 := by
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hρK : ρ ∈ NormH0 M Z Z0 := hRK hρ
  obtain ⟨hxR, -⟩ := sec8_normalizes_of_zt hZt h51 hA hc hs hZ0 hxK
  have hxρR : x * ρ * x⁻¹ ∈ Rt M (LB M Q B) t :=
    (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp hxR) ρ).mp hρ
  have hcommR : ⁅x, ρ⁆ ∈ Rt M (LB M Q B) t := by
    have e : ⁅x, ρ⁆ = (x * ρ * x⁻¹) * ρ⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact (Rt M (LB M Q B) t).mul_mem hxρR ((Rt M (LB M Q B) t).inv_mem hρ)
  have hcommO : ⁅x, ρ⁆ ∈ inSubgroup (pCore 2) (NormH0 M Z Z0) := by
    have h1 : ρ * x⁻¹ * ρ⁻¹ ∈ inSubgroup (pCore 2) (NormH0 M Z Z0) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_inSubgroup_pCore 2 _ hρK) x⁻¹).mp
        ((inSubgroup (pCore 2) (NormH0 M Z Z0)).inv_mem hx)
    have e : ⁅x, ρ⁆ = x * (ρ * x⁻¹ * ρ⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (inSubgroup (pCore 2) (NormH0 M Z Z0)).mul_mem hx h1
  have hP : (inSubgroup (pCore 2) (NormH0 M Z Z0) ⊓ Rt M (LB M Q B) t) ≤
      inSubgroup (pCore 2) (Rt M (LB M Q B) t) := by
    exact le_inSubgroup_pCore (isPGroup_inSubgroup_pCore 2 (NormH0 M Z Z0)).to_inf_left inf_le_right
      fun r hr => mem_normalizer_inf (le_normalizer_inSubgroup_pCore 2 _ (hRK hr))
        (Subgroup.le_normalizer hr)
  have hNt' := hNt G M Q Z B hc n h5.width h5.n_gt h5.noA2 h5.gen t h5.mem h5.notQ
  have h2 : ⁅x, ρ⁆ ∈ Nt M (LB M Q B) t := hP (Subgroup.mem_inf.mpr ⟨hcommO, hcommR⟩)
  rwa [hNt'] at h2

theorem step85First_of_parts (hZt : Sec8ZtStatement) (h51 : Stroth51Statement)
    (hA : Sec8AExistsStatement) (hNt : StrothNtStatement) (hFV : Step85FirstVStatement) :
    Step85FirstStatement := by
  intro G _ _ M Q Z B hc n t hs r hr Z0 hZ0 x hx
  have ha : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅x, ρ⁆ ∈ hc.CN t := fun ρ hρ =>
    sec85First_a hZt h51 hA hNt hc hs hZ0 hx hρ
  exact ⟨ha, hFV G M Q Z B hc n t hs r hr Z0 hZ0 x hx ha⟩

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec10Two
public import CFSG.RankThree.GF2n.Stroth80.Sec311SLTorus
public import CFSG.RankThree.GF2n.Stroth80.Sec57

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem SLMNat.exists_conj_inv_mul_mem_Z {hc : Ctx M Q Z B} {t : G} {m : ℕ}
    (h : SLMNat hc t m) (hm : 2 ≤ m) {x v : G} (hxV : x ∈ Vt M (LB M Q B) B Z t) (hxZ : x ∉ Z)
    (hvV : v ∈ Vt M (LB M Q B) B Z t) (hvZ : v ∉ Z) :
    ∃ r ∈ Rt M (LB M Q B) t, (r * x * r⁻¹)⁻¹ * v ∈ Z := by
  set V := Vt M (LB M Q B) B Z t
  obtain ⟨K, hK, hfin, -, φ, hφrange, -, hSA⟩ := h
  obtain ⟨hRnV, hZn, ψ, hψ⟩ := hSA
  haveI := hZn
  have hker : ∀ w : V, ψ (QuotientGroup.mk w) = 1 ↔ (w : G) ∈ Z := by
    intro w
    rw [← map_one ψ, ψ.injective.eq_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hne : ∀ w : V, (w : G) ∉ Z → Multiplicative.toAdd (ψ (QuotientGroup.mk w)) ≠ 0 :=
    fun w hwZ h0 => hwZ ((hker w).mp (by simpa using congrArg Multiplicative.ofAdd h0))
  obtain ⟨g, hgS, hgv⟩ := exists_statedSL_mulVec_eq_of_ne_zero hm
    (hne ⟨x, hxV⟩ hxZ) (hne ⟨v, hvV⟩ hvZ)
  obtain ⟨r, hrφ⟩ := MonoidHom.mem_range.mp (hφrange ▸ hgS)
  have hrV : (r : G) * x * (r : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hRnV r.2) x).mp hxV
  have hquot : QuotientGroup.mk' (Z.subgroupOf V) ⟨(r : G) * x * (r : G)⁻¹, hrV⟩ =
      QuotientGroup.mk' (Z.subgroupOf V) ⟨v, hvV⟩ := by
    refine ψ.injective (Multiplicative.toAdd.injective ?_)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      hψ r ⟨x, hxV⟩ ⟨(r : G) * x * (r : G)⁻¹, hrV⟩ rfl, hrφ, hgv]
  have h1 : QuotientGroup.mk' (Z.subgroupOf V)
      ((⟨(r : G) * x * (r : G)⁻¹, hrV⟩ : V)⁻¹ * ⟨v, hvV⟩) = 1 := by
    rw [map_mul, map_inv, hquot, inv_mul_cancel]
  have hmemZ : ((⟨(r : G) * x * (r : G)⁻¹, hrV⟩ : V)⁻¹ * ⟨v, hvV⟩ : V) ∈ Z.subgroupOf V :=
    (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨r, r.2, hmemZ⟩

theorem Good101.isRoot_of_mem_Vt {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G}
    (ht : Good101 M Q Z B t) {a : G} (haV : a ∈ Vt M (LB M Q B) B Z t) (haZ : a ∉ Z) :
    ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = a := by
  obtain ⟨m, hm2, hsl⟩ := SLlike.exists_SLMNat (H.slLike ht)
  obtain ⟨b, hbB, hb1⟩ := hc.exists_ne_one
  have hBV : B ≤ Vt M (LB M Q B) B Z t := by
    have h := sec39_conjB_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z) M.one_mem
      (by rw [conjSubgroup_one]; exact ht.mem_LB)
    rwa [conjSubgroup_one] at h
  have hbZ : b ∉ Z := fun hbZ => hb1 (by
    have : b ∈ Z ⊓ B := ⟨hbZ, hbB⟩
    rwa [hc.inf_eq_bot, Subgroup.mem_bot] at this)
  obtain ⟨r, hrR, hrz⟩ := hsl.exists_conj_inv_mul_mem_Z hm2 (hBV hbB) hbZ haV haZ
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hcQ : r * b * r⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hrM) b).mp (hc.le hbB)
  have hcZ : r * b * r⁻¹ ∉ Z := fun hZ => haZ (by
    have := Z.mul_mem hZ hrz
    rwa [mul_inv_cancel_left] at this)
  obtain ⟨w, -, hw⟩ := exists_comm_eq hc.hyp hcQ hcZ hrz
  obtain ⟨g₀, hg₀⟩ := hc.conj
  have hb0 : g₀⁻¹ * b * g₀ ∈ Z := by
    have h := hbB
    rw [hg₀] at h
    exact mem_conjSubgroup.mp h
  refine ⟨w * r * g₀, g₀⁻¹ * b * g₀, hb0, ?_, ?_⟩
  · intro h1
    apply hb1
    calc b = g₀ * (g₀⁻¹ * b * g₀) * g₀⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · have hwc : w * (r * b * r⁻¹) * w⁻¹ = ⁅w, r * b * r⁻¹⁆ * (r * b * r⁻¹) := by
      simp only [commutatorElement_def]; group
    have hzc := Z_central hc.hyp hrz hcQ
    calc w * r * g₀ * (g₀⁻¹ * b * g₀) * (w * r * g₀)⁻¹ = w * (r * b * r⁻¹) * w⁻¹ := by group
      _ = ⁅w, r * b * r⁻¹⁆ * (r * b * r⁻¹) := hwc
      _ = (r * b * r⁻¹)⁻¹ * a * (r * b * r⁻¹) := by rw [hw]
      _ = (r * b * r⁻¹) * ((r * b * r⁻¹)⁻¹ * a) := hzc
      _ = a := by group

theorem Sit.isRoot_of_conj {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t) {α : G}
    (hα : α ∈ Q ⊓ QB Y) (hα1 : α ≠ 1) (hconj : ∃ g : G, g * t * g⁻¹ = t * α) :
    ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = α := by
  have H := hs.hyp
  obtain ⟨kY, hkY, hQBY, -⟩ := hs.QB_eq
  have h12 := smith_1_12 hs
  obtain ⟨hαQ, hαY⟩ := hα
  have hαYn : α ∉ Y := fun hY => hα1 (by
    have : α ∈ Y ⊓ Q := ⟨hY, hαQ⟩
    rwa [h12.2, Subgroup.mem_bot] at this)
  have hα'Q : kY⁻¹ * α * kY ∈ Q := by
    have h1 : α ∈ QB Y := hαY
    rw [hQBY, mem_conjSubgroup] at h1
    exact h1
  have hα'Z : kY⁻¹ * α * kY ∉ Z := fun hZ => hαYn (by
    rw [hkY]; exact mem_conjSubgroup.mpr hZ)
  have ht'Z : kY⁻¹ * t * kY ∈ Z := by
    have := hs.mem
    rw [hkY, mem_conjSubgroup] at this
    exact this
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨q, -, hq⟩ := GM.exists_comm hD hα'Q hα'Z ht'Z
  have hconj1 : (kY * q * kY⁻¹) * α * (kY * q * kY⁻¹)⁻¹ = t⁻¹ * α := by
    have h1 : q * (kY⁻¹ * α * kY) * q⁻¹ = (kY⁻¹ * t * kY)⁻¹ * (kY⁻¹ * α * kY) := by
      rw [← hq]; simp only [commutatorElement_def]; group
    calc (kY * q * kY⁻¹) * α * (kY * q * kY⁻¹)⁻¹
        = kY * (q * (kY⁻¹ * α * kY) * q⁻¹) * kY⁻¹ := by group
      _ = t⁻¹ * α := by rw [h1]; group
  obtain ⟨y, hy⟩ := hconj
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hs.x_sq
  have hconj2 : (kY * q * kY⁻¹) * α * (kY * q * kY⁻¹)⁻¹ = y * t * y⁻¹ := by
    rw [hconj1, htinv, hy]
  refine ⟨(kY * q * kY⁻¹)⁻¹ * y * kY, kY⁻¹ * t * kY, ht'Z, ?_, ?_⟩
  · intro h1
    apply hs.ne_one
    calc t = kY * (kY⁻¹ * t * kY) * kY⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · calc (kY * q * kY⁻¹)⁻¹ * y * kY * (kY⁻¹ * t * kY) * ((kY * q * kY⁻¹)⁻¹ * y * kY)⁻¹
        = (kY * q * kY⁻¹)⁻¹ * (y * t * y⁻¹) * (kY * q * kY⁻¹) := by group
      _ = (kY * q * kY⁻¹)⁻¹ * ((kY * q * kY⁻¹) * α * (kY * q * kY⁻¹)⁻¹) *
          (kY * q * kY⁻¹) := by rw [hconj2]
      _ = α := by group

theorem Sit.exists_root_group {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t) {α : G}
    (hα : α ∈ Q ⊓ QB Y) (hα1 : α ≠ 1) (hroot : ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = α) :
    ∃ C : Subgroup G, Ctx M Q Z C ∧ α ∈ C ∧ C ≤ QB Y ∧ Y ≤ QB C := by
  have H := hs.hyp
  obtain ⟨kY, hkY, hQBY, -⟩ := hs.QB_eq
  have h12 := smith_1_12 hs
  have hZQ : Z ⊓ QB Y = ⊥ := Z_inf_QB_eq_bot hs h12
  obtain ⟨hαQ, hαY⟩ := hα
  have hαZ : α ∉ Z := fun hZ => hα1 (by
    have : α ∈ Z ⊓ QB Y := ⟨hZ, hαY⟩
    rwa [hZQ, Subgroup.mem_bot] at this)
  have hαYn : α ∉ Y := fun hY => hα1 (by
    have : α ∈ Y ⊓ Q := ⟨hY, hαQ⟩
    rwa [h12.2, Subgroup.mem_bot] at this)
  have hα'Q : kY⁻¹ * α * kY ∈ Q := by
    have h1 : α ∈ QB Y := hαY
    rw [hQBY, mem_conjSubgroup] at h1
    exact h1
  have hα'Z : kY⁻¹ * α * kY ∉ Z := fun hZ => hαYn (by
    rw [hkY]; exact mem_conjSubgroup.mpr hZ)
  obtain ⟨h', z, hzZ, -, hαeq⟩ := hroot
  obtain ⟨g', hg'Q, hαg'⟩ := stroth_2_6 H hαQ hαZ ⟨h', z, hzZ, hαeq.symm⟩
  obtain ⟨g'', hg''Q, hαg''⟩ := stroth_2_6 H hα'Q hα'Z
    ⟨kY⁻¹ * h', z, hzZ, by rw [← hαeq]; group⟩
  have hαkg'' : α ∈ conjSubgroup (kY * g'') Z := by
    rw [mem_conjSubgroup]
    have e : (kY * g'')⁻¹ * α * (kY * g'') = g''⁻¹ * (kY⁻¹ * α * kY) * g'' := by group
    rw [e]
    exact mem_conjSubgroup.mp hαg''
  have hBαeq : conjSubgroup g' Z = conjSubgroup (kY * g'') Z :=
    conjSubgroup_eq_of_mem_ne_one H hα1 hαg' hαkg''
  have hBαY : conjSubgroup g' Z ≤ QB Y := by
    rw [hBαeq, conjSubgroup_mul, hQBY]
    exact Subgroup.map_mono hg''Q
  have hBαne_Z : conjSubgroup g' Z ≠ Z := fun e => hαZ (by rw [← e]; exact hαg')
  have hBαY' : conjSubgroup g' Z ≠ Y := fun e => hαYn (by rw [← e]; exact hαg')
  exact ⟨conjSubgroup g' Z, ⟨H, ⟨g', rfl⟩, hg'Q, hBαne_Z⟩, hαg', hBαY,
    H.le_QB_of_le_QB ⟨g', rfl⟩ ⟨kY, hkY⟩ hBαY' hBαY⟩

theorem isRoot_ne_one {Z : Subgroup G} {α : G}
    (hroot : ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = α) : α ≠ 1 := by
  obtain ⟨g, z, -, hz1, hgz⟩ := hroot
  intro h1
  apply hz1
  have : g * z * g⁻¹ = 1 := hgz.trans h1
  calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
    _ = 1 := by rw [this]; group

theorem Sec10Hyp.rootTrans (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) : RootTrans M Q Z B := by
  obtain ⟨t, ht, htQ, -⟩ := H.ex
  exact rootTrans_of_all h34 hc (H.toSec5 ht htQ)
    (hspread G M Q Z B hc n H.width H.n_gt H.noA2 H.gen)

theorem Good101.mem_Vt_of_isRoot (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good101 M Q Z B t)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {α : G} (hα : α ∈ Q ⊓ QB Y)
    (hroot : ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = α) : α ∈ Vt M (LB M Q B) B Z t := by
  obtain ⟨C, hcC, hαC, -, hYC⟩ := Sit.exists_root_group hs hα (isRoot_ne_one hroot) hroot
  obtain ⟨m, hm, hmB⟩ := H.rootTrans h34 hspread C hcC
  have htLB : t ∈ LB M Q C := Subgroup.mem_sup_right ⟨hYC hs.mem, ht.2.1⟩
  have htm : t ∈ conjSubgroup m (LB M Q B) := by
    rw [← hc.LB_conj hm, hmB]
    exact htLB
  exact sec39_conjB_le_Vt hm htm (by rw [hmB]; exact hαC)

theorem Good101.exists_conj_of_isRoot (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {α : G}
    (hα : α ∈ Q ⊓ QB Y) (hroot : ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = α) :
    ∃ k ∈ Q, k * t * k⁻¹ = t * α := by
  obtain ⟨C, hcC, hαC, -, hYC⟩ := Sit.exists_root_group hs hα (isRoot_ne_one hroot) hroot
  obtain ⟨m, hm, hmB⟩ := H.rootTrans h34 hspread C hcC
  have hno : NoA2 Q Z (LB M Q C) := by rw [← hmB]; exact hc.noA2_conj H.noA2 hm
  obtain ⟨a', ha', ha't⟩ := hcC.exists_comm_eq_of_mem_QB H.width
    (by have := H.n_gt; omega) hno (hYC hs.mem) ht.2.2.1 hαC
  refine ⟨a', ha'.1, ?_⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hs.x_sq
  have htt : t * t = 1 := hs.x_sq
  rw [commutatorElement_def] at ha't
  calc a' * t * a'⁻¹ = a' * t⁻¹ * a'⁻¹ := by rw [htinv]
    _ = t * t * (a' * t⁻¹ * a'⁻¹) := by rw [htt, one_mul]
    _ = t * (t * a' * t⁻¹ * a'⁻¹) := by group
    _ = t * α := by rw [ha't]

end CFSG.RankThree.GF2n.Stroth80

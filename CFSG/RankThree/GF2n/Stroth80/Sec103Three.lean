module

public import CFSG.RankThree.GF2n.Stroth80.Sec103Inv
public import CFSG.RankThree.GF2n.Stroth80.Sec10Fuse

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.mem_Wt_Vt_of_forall (hc : Ctx M Q Z B) {t h : G} (hhQ : h ∈ Q)
    (hall : ∀ m ∈ M, t ∈ conjSubgroup m (LB M Q B) →
      conjSubgroup m B ≤ Subgroup.centralizer ({h} : Set G)) :
    h ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
  have hle : Vt M (LB M Q B) B Z t ≤ Subgroup.centralizer ({h} : Set G) := by
    refine sup_le (fun z hz => ?_) (iSup₂_le fun m hm => iSup_le fun htm => hall m hm htm)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Z_central hc.hyp hz hhQ)
  refine ⟨hhQ, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hv)

theorem Good101.exists_mem_inf_comm_eq (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {h z : G}
    (hhQ : h ∈ Q) (hz : z ∈ Z) {m : G} (hm : m ∈ M) (htm : t ∈ conjSubgroup m (LB M Q B))
    (hnc : ¬ conjSubgroup m B ≤ Subgroup.centralizer ({h} : Set G)) :
    ∃ a ∈ Q ⊓ QB Y ⊓ Vt M (LB M Q B) B Z t, ⁅h, a⁆ = z := by
  obtain ⟨b, hb, hbc⟩ := SetLike.not_le_iff_exists.mp hnc
  have hbh : b * h ≠ h * b := fun e =>
    hbc (Subgroup.mem_centralizer_singleton_iff.mpr e)
  obtain ⟨β, hβ, hβh⟩ := (hc.conj_of_mem hm).exists_mem_comm_eq hb hhQ hbh (Z.inv_mem hz)
  have hβV : β ∈ Vt M (LB M Q B) B Z t := sec39_conjB_le_Vt hm htm hβ
  have hVle := H.Vt_le (stroth_5_7 h34 hspread) ht
  rw [inf_QB_zpowers_eq hs] at hVle
  have hnorm : Q ⊓ QB Y ≤ Subgroup.normalizer (Z : Set G) :=
    fun x hx => hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 hx.1)
  obtain ⟨a, ha, z', hz', haz⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm (hVle hβV)
  have haV : a ∈ Vt M (LB M Q B) B Z t := by
    have h1 : a = β * z'⁻¹ := by rw [← haz]; group
    rw [h1]
    exact (Vt M (LB M Q B) B Z t).mul_mem hβV ((Vt M (LB M Q B) B Z t).inv_mem
      (sec39_Z_le_Vt hz'))
  refine ⟨a, ⟨ha, haV⟩, ?_⟩
  have hβQ : β ∈ Q := (hc.conj_of_mem hm).le hβ
  have hzc : z' * h = h * z' := Z_central hc.hyp hz' hhQ
  have hz'h : z'⁻¹ * h⁻¹ * z' = h⁻¹ := by
    have e : h⁻¹ * z' = z' * h⁻¹ := by
      calc h⁻¹ * z' = h⁻¹ * (z' * h) * h⁻¹ := by group
        _ = h⁻¹ * (h * z') * h⁻¹ := by rw [hzc]
        _ = z' * h⁻¹ := by group
    rw [mul_assoc, e]; group
  have h2 : a = β * z'⁻¹ := by rw [← haz]; group
  calc ⁅h, a⁆ = h * β * (z'⁻¹ * h⁻¹ * z') * β⁻¹ := by
        rw [h2, commutatorElement_def]; group
    _ = (β * h * β⁻¹ * h⁻¹)⁻¹ := by rw [hz'h]; group
    _ = z := by rw [← commutatorElement_def, hβh, inv_inv]

theorem Good101.mem_Wt_of_conj_eq_mul (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {α h z : G}
    (hα : α ∈ Q ⊓ QB Y) (hαV : α ∉ Vt M (LB M Q B) B Z t) (hhQ : h ∈ Q) (hz : z ∈ Z)
    (hconj : h * t * h⁻¹ = t * α * z) : h ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
  refine hc.mem_Wt_Vt_of_forall hhQ fun m hm htm => ?_
  by_contra hnc
  obtain ⟨a, ⟨haA, haV⟩, hha⟩ :=
    ht.exists_mem_inf_comm_eq h34 hspread H hs hhQ (Z.inv_mem hz) hm htm hnc
  obtain ⟨k, -, hkt⟩ := ht.exists_conj_of_mem_Vt h34 hspread H hs haA haV
  have e1 : h * a * h⁻¹ = ⁅h, a⁆ * a := by rw [commutatorElement_def]; group
  have hconj' : (h * k) * t * (h * k)⁻¹ = t * (α * a) := by
    calc (h * k) * t * (h * k)⁻¹ = h * (k * t * k⁻¹) * h⁻¹ := by group
      _ = h * (t * a) * h⁻¹ := by rw [hkt]
      _ = (h * t * h⁻¹) * (h * a * h⁻¹) := by group
      _ = t * α * z * (z⁻¹ * a) := by rw [hconj, e1, hha]
      _ = t * (α * a) := by group
  have hαaV := ht.mem_Vt_of_conj h34 hspread H hs ((Q ⊓ QB Y).mul_mem hα haA) ⟨h * k, hconj'⟩
  apply hαV
  have e2 : α = (α * a) * a⁻¹ := by group
  rw [e2]
  exact (Vt M (LB M Q B) B Z t).mul_mem hαaV ((Vt M (LB M Q B) B Z t).inv_mem haV)

theorem Good101.inf_QB_inf_Ut_le_Tt (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) :
    Q ⊓ QB Y ⊓ Ut Q Z t ≤ Tt Q Z (Vt M (LB M Q B) B Z t) t := by
  intro α hα
  obtain ⟨hαA, hαU⟩ := Subgroup.mem_inf.mp hα
  by_cases hαV : α ∈ Vt M (LB M Q B) B Z t
  · have h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G) :=
      (stroth_3_5 h34 hc H.width H.n_gt H.noA2 H.gen).2.1
    obtain ⟨m, hm, hsl⟩ := SLlike.exists_SLMNat (H.slLike ht)
    exact hc.Vt_le_Tt_of_SLNat (H.toSec5 ht.mem_LB ht.2.2.1) h35 (SLMNat.toSLNat hsl hm) hαV
  obtain ⟨x, hxQ, hcZ⟩ := hc.exists_comm_mul_inv_mem_Z ht.mem_LB hαU
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = ⁅x, t⁆ * α⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hcZ
  have htα : t * α = α * t := hs.QB_comm_X hs.mem hαA.2
  have htc : t * c * t⁻¹ = c := hs.x_cent (smith_1_12 hs) c hcZ
  have htc' : c * t = t * c := by
    calc c * t = t * c * t⁻¹ * t := by rw [htc]
      _ = t * c := by group
  have hαc : c * α = α * c := Z_central hc.hyp hcZ hαA.1
  have hconj : x * t * x⁻¹ = t * α * c := by
    have e : x * t * x⁻¹ = c * α * t := by rw [hcdef, commutatorElement_def]; group
    rw [e]
    calc c * α * t = c * (α * t) := by group
      _ = c * (t * α) := by rw [htα]
      _ = (c * t) * α := by group
      _ = (t * c) * α := by rw [htc']
      _ = t * (c * α) := by group
      _ = t * (α * c) := by rw [hαc]
      _ = t * α * c := by group
  have hxW := ht.mem_Wt_of_conj_eq_mul h34 hspread H hs hαA hαV hxQ hcZ hconj
  have hcomm : ⁅x, t⁆ ∈ ⁅Wt Q (Vt M (LB M Q B) B Z t), Subgroup.zpowers t⁆ :=
    Subgroup.commutator_mem_commutator hxW (Subgroup.mem_zpowers t)
  have e2 : α = c⁻¹ * ⁅x, t⁆ := by rw [hcdef]; group
  rw [e2]
  exact (Tt Q Z _ t).mul_mem (Subgroup.mem_sup_right (Z.inv_mem hcZ))
    (Subgroup.mem_sup_left hcomm)

theorem Good101.inf_QB_le_Ut_of_caseA (hc : Ctx M Q Z B) {t : G} {Y : Subgroup G}
    (hs : Sit M Q Z Y t) (hA : CaseA Q Z t) : Q ⊓ QB Y ≤ Ut Q Z t := by
  rcases hc.inf_QB_le_Ut_or_fuse hs with h | h
  · exact h
  · obtain ⟨z, hz, hne⟩ := hA
    obtain ⟨y, hy, hyt⟩ := h z hz
    exact absurd hyt (hne y hy)

theorem Good101.inf_QB_inf_Ut_le_Vt_of_not_caseA (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good101 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hB : ¬ CaseA Q Z t) : Q ⊓ QB Y ⊓ Ut Q Z t ≤ Vt M (LB M Q B) B Z t :=
  hc.W_le_Vt ht.mem_LB hs (H.rootTrans h34 hspread)
    (fun _ hu => hc.exists_conj_eq_mul_of_not_caseA ht.mem_LB hB hu)

end CFSG.RankThree.GF2n.Stroth80

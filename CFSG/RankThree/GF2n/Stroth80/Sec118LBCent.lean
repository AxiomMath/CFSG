module

public import CFSG.RankThree.GF2n.Stroth80.Sec118Nondeg
import CFSG.RankThree.GF2n.Stroth80.Sec11A2Line

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.comm_mem_sup_of_mem_LB_of_mem_inf_QB (hc : Ctx M Q Z B) {l x : G}
    (hl : l ∈ LB M Q B) (hx : x ∈ Q ⊓ QB B) : ⁅l, x⁆ ∈ (B ⊔ Z : Subgroup G) := by
  obtain ⟨s, hs, q, hq, rfl⟩ := hc.exists_mul_of_mem_LB hl
  have hsZ : ∀ z ∈ Z, s * z * s⁻¹ ∈ Z := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hs.2) z).mp hz
  have e : ⁅s * q, x⁆ = (s * ⁅q, x⁆ * s⁻¹) * ⁅s, x⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (B ⊔ Z : Subgroup G).mul_mem
    (Subgroup.mem_sup_right (hsZ _ (hc.hyp.toHyp79.comm_mem_V hq hx.1)))
    (Subgroup.mem_sup_left (hc.comm_QB_le_B hs.1 hx.2))

theorem Ctx.comm_mem_Z_of_centralizes {Y : Subgroup G} (hc : Ctx M Q Z B) (hZY : Z ≤ Y)
    (hBY : B ≤ Y) (hM : ∀ m ∈ M, ∀ y ∈ Y, m * y * m⁻¹ ∈ Y)
    (hnd : ∀ x ∈ Y, x ∈ Subgroup.centralizer (Y : Set G) → x ∈ Z) {l v : G}
    (hl : l ∈ LB M Q B) (hv : v ∈ Q) (hvS : v ∈ Subgroup.centralizer (Y : Set G)) :
    ⁅l, v⁆ ∈ Z := by
  set S : Subgroup G := Subgroup.centralizer (Y : Set G) with hS
  have hCM : ∀ m ∈ M, ∀ w ∈ S, m * w * m⁻¹ ∈ S := by
    intro m hm w hw
    rw [hS, Subgroup.mem_centralizer_iff] at hw ⊢
    intro h hh
    have h' : m⁻¹ * h * m ∈ Y := by simpa using hM m⁻¹ (M.inv_mem hm) h hh
    have h1 := hw _ h'
    calc h * (m * w * m⁻¹) = m * ((m⁻¹ * h * m) * w) * m⁻¹ := by group
      _ = m * (w * (m⁻¹ * h * m)) * m⁻¹ := by rw [h1]
      _ = m * w * m⁻¹ * h := by group
  have hcomm : ∀ m ∈ M, ∀ w ∈ S, ⁅m, w⁆ ∈ S := by
    intro m hm w hw
    have e : ⁅m, w⁆ = (m * w * m⁻¹) * w⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact S.mul_mem (hCM m hm w hw) (S.inv_mem hw)
  have hlM : l ∈ M := hc.LB_le_M hl
  have hvB : v ∈ Q ⊓ Subgroup.centralizer (B : Set G) :=
    ⟨hv, Subgroup.mem_centralizer_iff.mpr fun b hb => by
      rw [hS, Subgroup.mem_centralizer_iff] at hvS
      exact hvS b (hBY hb)⟩
  have hx : ⁅l, v⁆ ∈ Q ⊓ QB B := hc.comm_mem_inf_of_mem_LB hl hvB
  have hxS : ⁅l, v⁆ ∈ S := hcomm l hlM v hvS
  have hnd' : ∀ x ∈ Y, x ∈ S → x ∈ Z := hnd
  have hBZY : (B ⊔ Z : Subgroup G) ≤ Y := sup_le hBY hZY
  have hfix : ∀ l' ∈ LB M Q B, ⁅⁅l, v⁆, l'⁆ ∈ Z := by
    intro l' hl'
    have h1 : ⁅l', ⁅l, v⁆⁆ ∈ (B ⊔ Z : Subgroup G) :=
      hc.comm_mem_sup_of_mem_LB_of_mem_inf_QB hl' hx
    have h2 : ⁅l', ⁅l, v⁆⁆ ∈ S := hcomm l' (hc.LB_le_M hl') _ hxS
    have h3 : ⁅l', ⁅l, v⁆⁆ ∈ Z := hnd' _ (hBZY h1) h2
    have := Z.inv_mem h3
    rwa [commutatorElement_inv] at this
  have hxBZ : ⁅l, v⁆ ∈ (B ⊔ Z : Subgroup G) := hc.mem_sup_of_comm_LB_mem_Z' hx hfix
  exact hnd' _ (hBZY hxBZ) hxS

variable [(Q.subgroupOf M).Normal]

theorem Ctx.mem_commXbarPre_sup_Z_conj (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) {y : G}
    (hy : y ∈ (⁅Q, XbarPre M Q Z B⁆ ⊔ Z : Subgroup G)) :
    m * y * m⁻¹ ∈ (⁅Q, XbarPre M Q Z B⁆ ⊔ Z : Subgroup G) := by
  have hN := conjSubgroup_eq_self_iff.mpr (hc.M_le_normalizer_commXbarPre hm)
  have hZ := conjSubgroup_eq_self_iff.mpr (hc.hyp.Z_normal.2 hm)
  have hmem : m * y * m⁻¹ ∈ conjSubgroup m (⁅Q, XbarPre M Q Z B⁆ ⊔ Z : Subgroup G) :=
    ⟨y, hy, by show (MulAut.conj m) y = _; rw [MulAut.conj_apply]⟩
  rwa [conjSubgroup_sup', hN, hZ] at hmem

theorem Ctx.comm_mem_Z_of_centralizes_commXbarPre (hc : Ctx M Q Z B)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {l v : G} (hl : l ∈ LB M Q B) (hv : v ∈ Q)
    (hvY : v ∈ Subgroup.centralizer ((⁅Q, XbarPre M Q Z B⁆ ⊔ Z : Subgroup G) : Set G)) :
    ⁅l, v⁆ ∈ Z := by
  obtain ⟨a, haL, haA⟩ := ha2
  have haM : a ∈ M := hc.LB_le_M haL
  have haX : a ∈ XbarPre M Q Z B :=
    (mem_XbarPre_iff hc haM).mpr (Subgroup.subset_closure (hc.mk_mem_Ebar haL haA))
  have hBY : B ≤ (⁅Q, XbarPre M Q Z B⁆ ⊔ Z : Subgroup G) :=
    (hc.B_le_commutator_of_a2 haL haA).trans
      (sup_le_sup_right (Subgroup.commutator_mono le_rfl (by
        rw [Subgroup.zpowers_le]; exact haX)) _)
  refine hc.comm_mem_Z_of_centralizes le_sup_right hBY (fun m hm y hy =>
    hc.mem_commXbarPre_sup_Z_conj hm hy) (fun x hx hxS => ?_) hl hv hvY
  have h1 : x ∈ Subgroup.centralizer ((⁅Q, XbarPre M Q Z B⁆ : Subgroup G) : Set G) :=
    fun w hw => hxS w (Subgroup.mem_sup_left hw)
  have := hc.commXbarPre_sup_inf_centralizer_eq
  rw [← this]
  exact ⟨hx, h1⟩

end CFSG.RankThree.GF2n.Stroth80

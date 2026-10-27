module

public import CFSG.RankThree.GF2n.Stroth80.Sec10NotMemUt
public import CFSG.RankThree.GF2n.Stroth80.Sec10RootKernel
public import CFSG.RankThree.GF2n.Stroth80.Sec103Inv

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem mul_comm_of_comm_eq {h a b : G} (e : ⁅h, a⁆ = ⁅h, b⁆) :
    h * (b⁻¹ * a) = b⁻¹ * a * h := by
  have e' : h * (b⁻¹ * a) * h⁻¹ = b⁻¹ * a := by
    calc h * (b⁻¹ * a) * h⁻¹ = b⁻¹ * (⁅h, b⁆⁻¹ * ⁅h, a⁆) * a := by
          simp only [commutatorElement_def]; group
      _ = b⁻¹ * a := by rw [e, inv_mul_cancel, mul_one]
  calc h * (b⁻¹ * a) = h * (b⁻¹ * a) * h⁻¹ * h := by group
    _ = b⁻¹ * a * h := by rw [e']

theorem Sit.exists_comm_eq_of_forall {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t) {h : G}
    (hh : h ∈ Q) (hht : ⁅h, t⁆ ≠ 1) (hY : ∀ s ∈ Y, ⁅s, h⁆ ∈ Z) {z : G} (hz : z ∈ Z) :
    ∃ s ∈ Y, ⁅h, s⁆ = z := by
  have hmem : ∀ s ∈ Y, ⁅h, s⁆ ∈ Z := fun s hsY => by
    rw [← commutatorElement_inv]
    exact Z.inv_mem (hY s hsY)
  let f : ↥Y → ↥Z := fun s => ⟨⁅h, (s : G)⁆, hmem s s.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hcomm := mul_comm_of_comm_eq (congrArg Subtype.val hab : ⁅h, (a : G)⁆ = ⁅h, (b : G)⁆)
    by_contra hne
    have hu1 : (b : G)⁻¹ * a ≠ 1 := fun h1 => hne (Subtype.ext (by
      calc (a : G) = b * ((b : G)⁻¹ * a) := by group
        _ = b := by rw [h1, mul_one]))
    have hsu := Sit.of_mem_root hs (Y.mul_mem (Y.inv_mem b.2) a.2) hu1
    have h12 := smith_1_12 hsu
    have hK : h ∈ Kx Q Y := by
      rw [Kx_eq hsu h12]
      exact ⟨hh, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
    have hth := Subgroup.mem_centralizer_iff.mp (Kx_le_centralizer_X hsu h12 hK) t hs.mem
    exact hht (commutatorElement_eq_one_iff_mul_comm.mpr hth.symm)
  have hcard : Nat.card Z ≤ Nat.card Y := by
    obtain ⟨g, hg⟩ := hs.conj
    rw [hg, card_conjSubgroup]
  obtain ⟨s, hsz⟩ := (Function.Injective.bijective_of_nat_card_le hinj hcard).2 ⟨z, hz⟩
  exact ⟨s, s.2, congrArg Subtype.val hsz⟩

theorem StrothHyp.conj_mul_eq_of_comm_eq (H : StrothHyp M Q Z) {h α s : G} (hα : α ∈ Q)
    (hz : ⁅h, α⁆ ∈ Z) (he : ⁅h, s⁆ = ⁅h, α⁆) : h * (α * s) * h⁻¹ = α * s := by
  have h1 : h * α * h⁻¹ = ⁅h, α⁆ * α := by simp only [commutatorElement_def]; group
  have h2 : h * s * h⁻¹ = ⁅h, α⁆ * s := by rw [← he]; simp only [commutatorElement_def]; group
  have hz2 : ⁅h, α⁆ * ⁅h, α⁆ = 1 := by rw [← pow_two]; exact Z_sq H hz
  have hzα : ⁅h, α⁆ * α = α * ⁅h, α⁆ := Z_central H hz hα
  calc h * (α * s) * h⁻¹ = (h * α * h⁻¹) * (h * s * h⁻¹) := by group
    _ = ⁅h, α⁆ * α * (⁅h, α⁆ * s) := by rw [h1, h2]
    _ = α * (⁅h, α⁆ * ⁅h, α⁆) * s := by rw [hzα]; group
    _ = α * s := by rw [hz2, mul_one]

theorem Sec10Hyp.exists_conj_fix_of_not_caseA (h34 : Stroth34Statement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t)
    (hB : ¬ CaseA Q Z t) {α : G} (hα : α ∈ Q ⊓ QB Y) (hαU : α ∉ Ut Q Z t) {μ : G}
    (hμ : μ ∈ M) (hBY : B ≤ QB Y) (hDY : conjSubgroup μ B ≤ QB Y)
    (hne : B ≠ conjSubgroup μ B) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    ∃ h ∈ Q, h * t * h⁻¹ = t * z ∧ ∃ s ∈ Y, s ≠ 1 ∧ h * (α * s) * h⁻¹ = α * s := by
  obtain ⟨h, hh, hht⟩ : ∃ h ∈ Q, h * t * h⁻¹ = t * z := by
    by_contra hcon
    push Not at hcon
    exact hB ⟨z, hz, hcon⟩
  refine ⟨h, hh, hht, ?_⟩
  have hcomm : ⁅h, t⁆ = z := by
    rw [commutatorElement_def, hht]
    exact hs.x_cent (smith_1_12 hs) z hz
  have hhα := hc.mul_comm_ne_of_not_mem_Ut hs hα hαU hh (hcomm ▸ hz) (hcomm ▸ hz1)
  have hth : ⁅t, h⁆ ∈ Z := by
    rw [← commutatorElement_inv, hcomm]
    exact Z.inv_mem hz
  have hK : ∀ s ∈ Y, ⁅s, h⁆ ∈ Z := fun s hsY =>
    H.comm_mem_Z_of_mem_root h34 hs M.one_mem hμ (by rwa [conjSubgroup_one]) hDY
      (by rwa [conjSubgroup_one]) hsY hh hth
  have hzα : ⁅h, α⁆ ∈ Z := comm_mem_Z hc.hyp hh hα.1
  obtain ⟨s, hsY, hse⟩ := Sit.exists_comm_eq_of_forall hs hh (hcomm ▸ hz1) hK hzα
  refine ⟨s, hsY, ?_, hc.hyp.conj_mul_eq_of_comm_eq hα.1 hzα hse⟩
  rintro rfl
  apply hhα
  have h1 : ⁅h, α⁆ = 1 := by rw [← hse, commutatorElement_one_right]
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

end CFSG.RankThree.GF2n.Stroth80

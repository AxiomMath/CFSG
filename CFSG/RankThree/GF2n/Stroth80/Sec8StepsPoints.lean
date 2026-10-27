module

public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

theorem sec8PointTI_central {G : Type} [Group G] {M Q Z B : Subgroup G} (hc : Ctx M Q Z B)
    {b z : G} (hb : b ∈ B) (hz : z ∈ Z) : b * z = z * b := by
  have hz' : z ∈ cen Q := by
    rw [← hc.hyp.hZ]
    exact hz
  rw [cen_eq, Subgroup.mem_inf] at hz'
  exact Subgroup.mem_centralizer_iff.mp hz'.2 b (hc.le hb)

theorem sec8PointTI_mul_of_mem_sup {G : Type} [Group G] {B Z : Subgroup G}
    (hc : ∀ b ∈ B, ∀ z ∈ Z, b * z = z * b) {y : G} (hy : y ∈ B ⊔ Z) :
    ∃ b ∈ B, ∃ z ∈ Z, y = b * z := by
  let S : Subgroup G :=
    { carrier := {y | ∃ b ∈ B, ∃ z ∈ Z, y = b * z}
      mul_mem' := by
        rintro _ _ ⟨b₁, hb₁, z₁, hz₁, rfl⟩ ⟨b₂, hb₂, z₂, hz₂, rfl⟩
        refine ⟨b₁ * b₂, B.mul_mem hb₁ hb₂, z₁ * z₂, Z.mul_mem hz₁ hz₂, ?_⟩
        have h : z₁ * b₂ = b₂ * z₁ := (hc b₂ hb₂ z₁ hz₁).symm
        calc b₁ * z₁ * (b₂ * z₂) = b₁ * (z₁ * b₂) * z₂ := by group
          _ = b₁ * (b₂ * z₁) * z₂ := by rw [h]
          _ = b₁ * b₂ * (z₁ * z₂) := by group
      one_mem' := ⟨1, B.one_mem, 1, Z.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨b, hb, z, hz, rfl⟩
        refine ⟨b⁻¹, B.inv_mem hb, z⁻¹, Z.inv_mem hz, ?_⟩
        have h : z⁻¹ * b⁻¹ = b⁻¹ * z⁻¹ := (hc b⁻¹ (B.inv_mem hb) z⁻¹ (Z.inv_mem hz)).symm
        rw [_root_.mul_inv_rev, h] }
  have hle : B ⊔ Z ≤ S :=
    sup_le (fun b hb => ⟨b, hb, 1, Z.one_mem, by simp⟩)
      (fun z hz => ⟨1, B.one_mem, z, hz, by simp⟩)
  exact hle hy

theorem sec8PointTI_mem_sup_iff {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    {K : Type} [Field K] {γ : G → K} (hc : Ctx M Q Z B) (M₀ : Tim79.QuadModel Q Z K γ) {x : G} :
    x ∈ B ⊔ Z ↔ x ∈ Q ∧ M₀.π x ∈ M₀.img B := by
  have hBQ : B ≤ Q := hc.le
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  constructor
  · intro hx
    obtain ⟨b, hb, z, hz, rfl⟩ :=
      sec8PointTI_mul_of_mem_sup (fun _ hb _ hz => sec8PointTI_central hc hb hz) hx
    refine ⟨Q.mul_mem (hBQ hb) (hZQ hz), ?_⟩
    rw [M₀.π_mul b (hBQ hb) z (hZQ hz), (M₀.π_ker z (hZQ hz)).mpr hz, add_zero]
    exact Tim79.QuadModel.pi_mem_img M₀ hb (hBQ hb)
  · rintro ⟨hxQ, hπx⟩
    obtain ⟨u, hu, huQ, hux⟩ := (Tim79.QuadModel.mem_img M₀).mp hπx
    have hz : u⁻¹ * x ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ huQ hxQ).mp hux
    have h2 : u * (u⁻¹ * x) ∈ B ⊔ Z := Subgroup.mul_mem_sup hu hz
    rwa [mul_inv_cancel_left] at h2

theorem sec8PointTI_holds {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) {g : G} (hg : g ∈ M)
    (hd : ∃ d ∈ (B ⊔ Z : Subgroup G), d ∈ (conjSubgroup g B ⊔ Z : Subgroup G) ∧ d ∉ Z) :
    conjSubgroup g B ⊔ Z = B ⊔ Z := by
  obtain ⟨K, iF, iFin, -, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  have hc' : Ctx M Q Z (conjSubgroup g B) := hc.conj_of_mem hg
  obtain ⟨b, -, -, hb, -, -⟩ := hc.dictB h
  obtain ⟨b', -, -, hb', -, -⟩ := hc'.dictB h
  obtain ⟨d, hdB, hdB', hdZ⟩ := hd
  obtain ⟨hdQ, hπd⟩ := (sec8PointTI_mem_sup_iff hc M₀).mp hdB
  have hπd' : M₀.π d ∈ M₀.img (conjSubgroup g B) :=
    ((sec8PointTI_mem_sup_iff hc' M₀).mp hdB').2
  have hd0 : M₀.π d ≠ 0 := fun h0 => hdZ ((M₀.π_ker d hdQ).mp h0)
  obtain ⟨s, hs⟩ := (hb _).mp hπd
  obtain ⟨s', hs'⟩ := (hb' _).mp hπd'
  have hs0 : s ≠ 0 := fun h0 => hd0 (by rw [hs, h0, zero_smul])
  have hs'0 : s' ≠ 0 := fun h0 => hd0 (by rw [hs', h0, zero_smul])
  obtain ⟨c, hc0, hbc⟩ : ∃ c : K, c ≠ 0 ∧ b' = c • b :=
    ⟨s'⁻¹ * s, mul_ne_zero (inv_ne_zero hs'0) hs0, by
      rw [mul_smul, ← hs, hs', smul_smul, inv_mul_cancel₀ hs'0, one_smul]⟩
  have hlines : ∀ v : M₀.E, v ∈ M₀.img (conjSubgroup g B) ↔ v ∈ M₀.img B := by
    intro v
    rw [hb, hb']
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t * c, by rw [hbc, smul_smul]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t * c⁻¹, by rw [hbc, smul_smul, inv_mul_cancel_right₀ hc0]⟩
  ext x
  rw [sec8PointTI_mem_sup_iff hc' M₀, sec8PointTI_mem_sup_iff hc M₀, hlines]


theorem sec8PointTI_of : Sec8PointTIStatement := by
  intro G _ _ M Q Z B hc g hg hd
  exact sec8PointTI_holds hc hg hd

theorem sec8PointsTrans {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {v : G}
    (hv : v ∈ Vt M (LB M Q B) B Z t) (hvZ : v ∉ Z) :
    ∃ h ∈ Rt M (LB M Q B) t, v ∈ conjSubgroup h B ⊔ Z := by
  obtain ⟨m, _hm, K, iK, _iF, _hK, hnat⟩ := hs.sp
  obtain ⟨φ, hφ, _hker, hact⟩ := hnat
  obtain ⟨hnorm, hn, ψ, hψ⟩ := hact
  haveI := hn
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt hs.toSec5.mem
  obtain ⟨b, hbB, hbZ⟩ : ∃ b ∈ B, b ∉ Z := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg⟩ := hc.conj
    have hcard : Nat.card B = Nat.card Z := by rw [hg, card_conjSubgroup]
    have hBZ : B ≤ Z := fun x hx => hcon x hx
    exact hc.ne (Subgroup.eq_of_le_of_card_ge hBZ hcard.ge)
  have hbV : b ∈ Vt M (LB M Q B) B Z t := hBV hbB
  have hx0 : secVec ψ ⟨b, hbV⟩ ≠ 0 := fun h => hbZ ((secVec_eq_zero_iff ψ ⟨b, hbV⟩).mp h)
  have hy0 : secVec ψ ⟨v, hv⟩ ≠ 0 := fun h => hvZ ((secVec_eq_zero_iff ψ ⟨v, hv⟩).mp h)
  obtain ⟨A, hA, hAy⟩ := exists_statedSp_mulVec_eq hx0 hy0
  have hAφ : A ∈ φ.range := by rw [hφ]; exact hA
  obtain ⟨s, hsA⟩ := MonoidHom.mem_range.mp hAφ
  have hsbV : (s : G) * b * (s : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp (hnorm s.2) b).mp hbV
  have e : secVec ψ ⟨(s : G) * b * (s : G)⁻¹, hsbV⟩ = secVec ψ ⟨v, hv⟩ := by
    have h1 := hψ s ⟨b, hbV⟩ ⟨(s : G) * b * (s : G)⁻¹, hsbV⟩ rfl
    rw [hsA] at h1
    exact h1.trans hAy
  have hwB : (s : G) * b * (s : G)⁻¹ ∈ conjSubgroup (s : G) B := by
    rw [mem_conjSubgroup, show (s : G)⁻¹ * ((s : G) * b * (s : G)⁻¹) * (s : G) = b by group]
    exact hbB
  exact ⟨(s : G), s.2, mem_of_secVec_eq (S := conjSubgroup (s : G) B ⊔ Z) (y := ⟨v, hv⟩)
    (w := ⟨(s : G) * b * (s : G)⁻¹, hsbV⟩) le_sup_right ψ (Subgroup.mem_sup_left hwB) e⟩

theorem sec8PointsTrans_holds : Sec8PointsTransStatement := by
  intro G _ _ M Q Z B hc n t hs v hv hvZ
  exact sec8PointsTrans hc hs hv hvZ

end CFSG.RankThree.GF2n.Stroth80

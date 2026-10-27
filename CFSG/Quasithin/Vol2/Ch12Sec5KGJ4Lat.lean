module

public import CFSG.Quasithin.Vol2.Ch12Sec5KGJ4Gen
public import CFSG.Quasithin.Vol2.KGFactJ4M3KL
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Lift
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M3Ker
public import CFSG.Quasithin.Vol2.Ch12Sec5KGM24
public import CFSG.RankThree.PartOne.S10.PlaneContract

public section

namespace CFSG.Quasithin.H13.S125KG.J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open CFSG.Quasithin.J4Loc CFSG.Quasithin.F134.J4E9 CFSG.Quasithin.J4Fam
open scoped commutatorElement

theorem over_P0
    {Y : Subgroup J} (hY : P0 ≤ Y) : Y = ⊤ ∨ Y ≤ Hj ∨ Y ≤ M3 ∨ Y = J4M2.M2 := by
  have hF : J4Facts := j4Facts
  by_cases htop : Y = ⊤
  · exact Or.inl htop
  have h3 : Y ≤ Hj ∨ Y ≤ Subgroup.centralizer ({z0} : Set J) ∨
      Y ≤ Subgroup.normalizer (V0 : Set J) := by
    by_cases hs : Group.IsSolvable ↥Y
    · exact overgroup_of_solvable hY hs
    · exact J4Ov.j4OvergroupLocal_holds Y hY htop hs
  rcases h3 with h | h | h
  · exact Or.inr (Or.inl h)
  · rcases J4M2.J4M2Lattice hF hY h with h' | h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))
  · exact Or.inr (Or.inr (Or.inl h))

theorem transitive_X5
    {Y : Subgroup J} (hP : P0 ≤ Y) (hYM : Y ≤ M3) {y : J} (hy : y ∈ Y) (hyH : y ∉ Hj)
    {w : J ⧸ Hj} (hw : w ∈ X5) : ∃ g ∈ Y, g • basePt = w := by
  have hF : J4Facts := j4Facts
  by_cases hwb : w = basePt
  · exact ⟨1, Y.one_mem, by rw [one_smul, hwb]⟩
  have hyX : y • basePt ∈ X5 := ⟨y, hYM hy, rfl⟩
  have hyb : y • (basePt : J ⧸ Hj) ≠ basePt := fun h => hyH (smul_basePt_eq_self_iff.mp h)
  obtain ⟨e, he, hew⟩ := E_transitive_X5 hF hyX hyb hw hwb
  exact ⟨e * y, Y.mul_mem (hP (Eg_le_P0 he)) hy, by rw [mul_smul, hew]⟩

theorem le_Hj_of_le_M3
    {Y : Subgroup J} (hP : P0 ≤ Y) (hYM : Y ≤ M3) (h5 : ¬ 5 ∣ Nat.card Y) : Y ≤ Hj := by
  have hF : J4Facts := j4Facts
  intro y hy
  by_contra hyH
  apply h5
  have hfix : ∀ g : J, g • (basePt : J ⧸ Hj) = basePt ↔ g ∈ Hj := fun g =>
    smul_basePt_eq_self_iff
  have h := QT2.card_eq_orbit_mul_inf Y Hj basePt hfix
  have horb : MulAction.orbit ↥Y (basePt : J ⧸ Hj) = X5 := by
    ext w
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, hYM g.2, rfl⟩
    · intro hw
      obtain ⟨g, hg, hgw⟩ := transitive_X5 hP hYM hy hyH hw
      exact ⟨⟨g, hg⟩, hgw⟩
  rw [horb, Nat.card_coe_set_eq, ncard_X5 hF] at h
  rw [h]
  exact Dvd.intro _ rfl

theorem card_NV :
    Nat.card ↥J4Rad.NV = 2 ^ 21 * 63 := by
  have hF : J4Facts := j4Facts
  have hfix : ∀ g : J, g • (basePt : J ⧸ Hj) = basePt ↔ g ∈ Hj := fun g =>
    smul_basePt_eq_self_iff
  have h := QT2.card_eq_orbit_mul_inf M3 Hj basePt hfix
  rw [orbit_M3_eq, Nat.card_coe_set_eq, ncard_X5 hF, card_M3 hF] at h
  have hNV : M3 ⊓ Hj = J4Rad.NV := inf_comm _ _
  rw [hNV] at h
  rw [show (2 : ℕ) ^ 21 * 63 = 132120576 by norm_num]
  omega

theorem card_M2_inf_Hj :
    Nat.card ↥(J4M2.M2 ⊓ Hj) = 2 ^ 21 * 135 := by
  have hF : J4Facts := j4Facts
  have hfix : ∀ g : J, g • (basePt : J ⧸ Hj) = basePt ↔ g ∈ Hj := fun g =>
    smul_basePt_eq_self_iff
  have h := QT2.card_eq_orbit_mul_inf J4M2.M2 Hj basePt hfix
  have horb : Nat.card ↥(MulAction.orbit ↥J4M2.M2 (basePt : J ⧸ Hj)) = 77 := by
    rw [← Nat.card_congr (J4M2.ePt hF), Nat.card_fin]
  rw [horb, J4M2.card_M2 hF] at h
  rw [show (2 : ℕ) ^ 21 * 135 = 283115520 by norm_num]
  omega

theorem KL_le_NV : J4M3.KL ≤ J4Rad.NV := fun _ hk =>
  ⟨smul_basePt_eq_self_iff.mp ((mem_fixingSubgroup_iff J).mp (Subgroup.mem_inf.mp hk).2 basePt
    basePt_mem_X5), (Subgroup.mem_inf.mp hk).1⟩

theorem mem_normalizer_commutator {A B : Subgroup J} {g : J}
    (hA : g ∈ Subgroup.normalizer (A : Set J)) (hB : g ∈ Subgroup.normalizer (B : Set J)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup J) : Set J) := by
  have hc : ∀ C : Subgroup J, g ∈ Subgroup.normalizer (C : Set J) →
      C.map (MulAut.conj g).toMonoidHom = C := by
    intro C hC
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    constructor
    · intro h
      have := (Subgroup.mem_normalizer_iff.mp hC _).mp h
      simpa [mul_assoc] using this
    · intro h
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hC) _).mp h
      simpa using this
  have h := Subgroup.map_commutator A B (MulAut.conj g).toMonoidHom
  rw [hc A hA, hc B hB] at h
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  rw [← h]
  exact ⟨x, hx, rfl⟩

theorem commutator_KL :
    ⁅J4M3.KL, J4M3.KL⁆ = J4M3.KL := by
  set e := KGC31.E16.eNHom J4M3.hv0 J4M3.M3_le_eNorm with he
  have hle : ⁅J4M3.KL, J4M3.KL⁆ ≤ J4M3.KL := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact J4M3.KL.mul_mem (J4M3.KL.mul_mem (J4M3.KL.mul_mem ha hb) (J4M3.KL.inv_mem ha))
      (J4M3.KL.inv_mem hb)
  have hnorm : M3 ≤ Subgroup.normalizer
      ((⁅J4M3.KL, J4M3.KL⁆ : Subgroup J) : Set J) := fun m hm =>
    mem_normalizer_commutator (J4M3.M3_le_normalizer_KL hm) (J4M3.M3_le_normalizer_KL hm)
  have hKtop : (J4M3.KL.subgroupOf M3).map e = ⊤ := by
    refine eq_top_iff.mpr fun s _ => ?_
    obtain ⟨k, hk⟩ := J4M3.surjective_eNHom_KL s
    refine ⟨⟨k, J4M3.KL_le_M3 k.2⟩, Subgroup.mem_subgroupOf.mpr k.2, ?_⟩
    exact Subtype.ext (Units.ext (by rw [← hk]; rfl))
  have hsub : (⁅J4M3.KL, J4M3.KL⁆ : Subgroup J).subgroupOf M3 =
      ⁅J4M3.KL.subgroupOf M3, J4M3.KL.subgroupOf M3⁆ := by
    apply Subgroup.map_injective M3.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (hle.trans J4M3.KL_le_M3),
      Subgroup.map_subgroupOf_eq_of_le J4M3.KL_le_M3]
  have htop : ((⁅J4M3.KL, J4M3.KL⁆ : Subgroup J).subgroupOf M3).map e = ⊤ := by
    rw [hsub, Subgroup.map_commutator, hKtop]
    exact J4M3.commutator_top_statedSL3
  have h := J4M3.conjClosure_eq_KL hle htop
  have hcl : conjClosure (⁅J4M3.KL, J4M3.KL⁆ : Subgroup J) M3 ≤ ⁅J4M3.KL, J4M3.KL⁆ :=
    conjClosure_le fun m hm z hz => (Subgroup.mem_normalizer_iff.mp (hnorm hm) z).mp hz
  rw [h] at hcl
  exact le_antisymm hle hcl

end CFSG.Quasithin.H13.S125KG.J4

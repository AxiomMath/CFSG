module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenB8Cartan
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenPrelim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

private theorem centralizer_le_M_of_odd (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h847 : R847ThinCZ D) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M) {e m : ℕ} (hL2 : IsL2 (Bar2 K) (2 ^ e * m))
    {F : Subgroup G} (hFodd : Odd (Nat.card F)) (hFK : F ⊓ K ≠ ⊥) :
    Subgroup.centralizer (F : Set G) ≤ D.M := by
  classical
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFK
  have haF : (a : G) ∈ F := a.2.1
  have haK : (a : G) ∈ K := a.2.2
  have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hodd : Odd (orderOf (a : G)) :=
    hFodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard F haF)
  have hgt : 1 < orderOf (a : G) := by
    have hpos := orderOf_pos (a : G)
    have hne : orderOf (a : G) ≠ 1 := fun h => ha1' (orderOf_eq_one_iff.mp h)
    omega
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hgt.ne'
  have hrodd : Odd r := hodd.of_dvd_nat hrdvd
  have hr2 : r ≠ 2 := by
    rintro rfl
    norm_num at hrodd
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers (a : G)) r
    (by rwa [Nat.card_zpowers])
  let y : G := (x : G)
  have hyord : orderOf y = r := (Subgroup.orderOf_coe x).trans hxord
  have hyFK : y ∈ F ⊓ K :=
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨haF, haK⟩)) x.2
  have hNX : Subgroup.normalizer (Subgroup.zpowers y : Set G) ≤ D.M :=
    normalizer_zpowers_le_M_of_r847ThinCZ c h1930 h4 h847 hK
      (thin8_of_isL2_or_isSz (Or.inl hL2)) hyFK.2 hr hr2 hyord
  exact (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hyFK.1)).trans
    ((Subgroup.centralizer_le_normalizer (Subgroup.zpowers y : Set G)).trans hNX)

private theorem normalizer_Z_eq_M (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) :
    Subgroup.normalizer (D.Z : Set G) = D.M := by
  rw [← (h4 h1930 c).1]
  exact D.normalizer_U_eq

private theorem conjSubgroup_Z_le_V_and_normalizer (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) {v : G} (hvL : v ∈ c.L) :
    CFSG.Quasithin.conjSubgroup D.Z v⁻¹ ≤ c.V ∧
      CFSG.Quasithin.conjSubgroup D.Z v⁻¹ ≤ Subgroup.normalizer (D.Z : Set G) := by
  have hZV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  have hvN : v ∈ Subgroup.normalizer (c.V : Set G) :=
    c.sup_le_normalizer_V D Ch (Subgroup.mem_sup_left hvL)
  have hWV : CFSG.Quasithin.conjSubgroup D.Z v⁻¹ ≤ c.V := by
    intro x hx
    rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hx
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hvN) x).2
      (by simpa using hZV hx)
  have hVab : IsMulCommutative c.V := (c.isElemAbelian_V h4 h1930).1
  have hVcentZ : c.V ≤ Subgroup.centralizer (D.Z : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (congrArg Subtype.val (hVab.is_comm.comm ⟨w, hw⟩ ⟨z, hZV hz⟩)).symm
  exact ⟨hWV, hWV.trans (hVcentZ.trans (Subgroup.centralizer_le_normalizer (D.Z : Set G)))⟩

private theorem inf_conjSubgroup_Z_eq_bot (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {v : G} (hvM : v ∉ D.M) :
    D.Z ⊓ CFSG.Quasithin.conjSubgroup D.Z v⁻¹ = ⊥ := by
  rcases c.Z_right_TI h4 h1930 v⁻¹ with h | h
  · exact h
  · exfalso
    apply hvM
    have hmap : D.Z.map (MulAut.conj v).toMonoidHom = D.Z := by
      simpa [CFSG.Quasithin.conjSubgroup] using h
    have hvNZ : v ∈ Subgroup.normalizer (D.Z : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
    rwa [normalizer_Z_eq_M D Ch h4 h1930 c] at hvNZ

private theorem card_sup_Z_conj_eq (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) {v : G} (hvL : v ∈ c.L)
    (hvM : v ∉ D.M) :
    Nat.card ↥(D.Z ⊔ CFSG.Quasithin.conjSubgroup D.Z v⁻¹) = Nat.card c.V := by
  obtain ⟨hWV, hnormal⟩ := conjSubgroup_Z_le_V_and_normalizer D Ch h4 h1930 c hvL
  have hdisj : Disjoint D.Z (CFSG.Quasithin.conjSubgroup D.Z v⁻¹) := by
    rw [disjoint_iff]
    exact inf_conjSubgroup_Z_eq_bot D Ch h4 h1930 c hvM
  have hcardZ : Nat.card D.Z = 2 ^ CFSG.Open.pRank 2 D.Z :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two
      (c.isElemAbelian_Z h4 h1930)
  have hcardW : Nat.card (CFSG.Quasithin.conjSubgroup D.Z v⁻¹) = Nat.card D.Z :=
    CFSG.Quasithin.E3.card_conjSubgroup D.Z v⁻¹
  have hcardV := Ctx23L.card_V_eq D Ch h4 h23 h1930 c
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer D.Z
    (CFSG.Quasithin.conjSubgroup D.Z v⁻¹) hnormal hdisj, hcardZ, hcardW, hcardZ,
    hcardV, pow_two]

private theorem sup_Z_conj_eq_V (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {v : G} (hvL : v ∈ c.L) (hvM : v ∉ D.M) :
    D.Z ⊔ CFSG.Quasithin.conjSubgroup D.Z v⁻¹ = c.V := by
  have hZV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  have hWV := (conjSubgroup_Z_le_V_and_normalizer D Ch h4 h1930 c hvL).1
  refine Subgroup.eq_of_le_of_card_ge (sup_le hZV hWV) ?_
  rw [card_sup_Z_conj_eq D Ch h4 h23 h1930 c hvL hvM]

private theorem centralizer_le_normalizer_conjSubgroup_Z (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) {F : Subgroup G} {v : G}
    (hCFM : Subgroup.centralizer (F : Set G) ≤ D.M)
    (hvF : v ∈ Subgroup.normalizer (F : Set G)) :
    Subgroup.centralizer (F : Set G) ≤
      Subgroup.normalizer (CFSG.Quasithin.conjSubgroup D.Z v⁻¹ : Set G) := by
  let W : Subgroup G := CFSG.Quasithin.conjSubgroup D.Z v⁻¹
  have hvC : v ∈ Subgroup.normalizer (Subgroup.centralizer (F : Set G) : Set G) :=
    CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer F hvF
  have hvCinv : v⁻¹ ∈ Subgroup.normalizer (Subgroup.centralizer (F : Set G) : Set G) :=
    Subgroup.inv_mem _ hvC
  have hCFconj : Subgroup.centralizer (F : Set G) ≤ CFSG.Quasithin.conjSubgroup D.M v⁻¹ := by
    intro x hx
    rw [CFSG.Quasithin.mem_conjSubgroup_iff]
    exact hCFM (by simpa using (Subgroup.mem_normalizer_iff.mp hvCinv x).1 hx)
  have hNW : CFSG.Quasithin.conjSubgroup D.M v⁻¹ = Subgroup.normalizer (W : Set G) := by
    rw [← normalizer_Z_eq_M D Ch h4 h1930 c]
    exact CFSG.Quasithin.E3.conjSubgroup_normalizer D.Z v⁻¹
  rw [← hNW]
  exact hCFconj

theorem centralizer_F_le_N (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h847 : R847ThinCZ D) (h1930 : H1930 D)
    (c : Ctx23L D Ch) {K : Subgroup G} (hK : K ∈ calC D.M)
    {e m : ℕ} (hL2 : IsL2 (Bar2 K) (2 ^ e * m)) {F : Subgroup G}
    (hFodd : Odd (Nat.card F)) (hFK : F ⊓ K ≠ ⊥) {v : G} (hvL : v ∈ c.L) (hvM : v ∉ D.M)
    (hvF : v ∈ Subgroup.normalizer (F : Set G)) :
    Subgroup.centralizer (F : Set G) ≤ c.N := by
  have hCFM : Subgroup.centralizer (F : Set G) ≤ D.M :=
    centralizer_le_M_of_odd D Ch h4 h847 h1930 c hK hL2 hFodd hFK
  have hCFNZ : Subgroup.centralizer (F : Set G) ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [normalizer_Z_eq_M D Ch h4 h1930 c]
    exact hCFM
  have hCFNW : Subgroup.centralizer (F : Set G) ≤
      Subgroup.normalizer (CFSG.Quasithin.conjSubgroup D.Z v⁻¹ : Set G) :=
    centralizer_le_normalizer_conjSubgroup_Z D Ch h4 h1930 c hCFM hvF
  have hle : Subgroup.centralizer (F : Set G) ≤
      Subgroup.normalizer (D.Z : Set G) ⊓
        Subgroup.normalizer (CFSG.Quasithin.conjSubgroup D.Z v⁻¹ : Set G) :=
    le_inf hCFNZ hCFNW
  have hleV : Subgroup.centralizer (F : Set G) ≤
      Subgroup.normalizer
        ((D.Z ⊔ CFSG.Quasithin.conjSubgroup D.Z v⁻¹ : Subgroup G) : Set G) :=
    hle.trans (Subgroup.inf_normalizer_le_normalizer_sup D.Z
      (CFSG.Quasithin.conjSubgroup D.Z v⁻¹))
  rw [sup_Z_conj_eq_V D Ch h4 h23 h1930 c hvL hvM,
    c.normalizer_V_eq h4 h1930] at hleV
  exact hleV

end Ctx23L

theorem cartanCentralizerStep_of_weyl (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h23 : S23_23 D Ch) (h847 : R847ThinCZ D)
    (hW : H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z → ∀ DL F : Subgroup G,
      DL ≤ CFSG.Quasithin.borelOf c.L D.T → Nat.card DL = 2 ^ CFSG.Open.pRank 2 D.Z - 1 →
      (D.T ⊓ c.L) ⊔ DL = CFSG.Quasithin.borelOf c.L D.T → DL ≤ F → Odd (Nat.card F) →
      IsMulCommutative F → F ≤ c.N → F ≤ D.M → F ≤ Subgroup.normalizer (D.T : Set G) →
      ∃ v ∈ c.L, v ∉ D.M ∧ v ∈ Subgroup.normalizer (F : Set G)) :
    CartanCentralizerStep D Ch := by
  intro h1930 c h3 K hK hKn e m hm2 hL2 A₀ hA₀ hA₀card DL F hDLleB hDLcard hDLcomm hDLsup
    hDLleF hFle hFodd hFcomm hFKne hFleN hFleM hFleNT
  obtain ⟨v, hvL, hvM, hvF⟩ := hW h1930 c h3 DL F hDLleB hDLcard hDLsup hDLleF hFodd
    hFcomm hFleN hFleM hFleNT
  exact Ctx23L.centralizer_F_le_N D Ch h4 h23 h847 h1930 c hK hL2 hFodd hFKne hvL
    hvM hvF

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

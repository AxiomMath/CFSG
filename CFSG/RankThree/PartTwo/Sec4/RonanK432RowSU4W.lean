module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSp4
public import CFSG.RankThree.PartTwo.Sec4.Item424Res5ProofU4
public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
public import CFSG.RankThree.PartOne.KF.R5Levi
public import CFSG.RankThree.PartOne.N143.HeisenbergThree

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree.PartOne.KFU CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSU)

theorem su4W_three_dvd_card_units {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) (h3 : 3 ∣ q - 1) (hq : 1 ≤ q) : 3 ∣ Nat.card Fˣ := by
  obtain ⟨k, hk⟩ := h3
  have hqk : q = 3 * k + 1 := by omega
  have hsq : q ^ 2 = 3 * (3 * k ^ 2 + 2 * k) + 1 := by rw [hqk]; ring
  rw [Nat.card_units, hF, hsq, Nat.add_sub_cancel]
  exact dvd_mul_right 3 _

theorem su4W_exists_unit_cube_ne_one {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) (h3 : 3 ∣ q - 1) (hq : 1 ≤ q) :
    ∃ g : Fˣ, g ^ 3 = 1 ∧ g ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ :=
    exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (su4W_three_dvd_card_units hF h3 hq)
  refine ⟨g, ?_, ?_⟩
  · have := pow_orderOf_eq_one g
    rwa [hg] at this
  · intro h1
    rw [h1, orderOf_one] at hg
    exact absurd hg (by norm_num)

theorem su4W_fix_of_pow_three {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] {x : F} (hx : x ^ 3 = 1) (h3 : 3 ∣ p ^ f - 1) :
    unitaryInvolution F p f x = x := by
  rw [unitaryInvolution_apply]
  obtain ⟨k, hk⟩ := h3
  have hpos : 0 < p ^ f := pow_pos (Fact.out : p.Prime).pos f
  have hpk : p ^ f = 3 * k + 1 := by omega
  rw [hpk, pow_succ, pow_mul, hx, one_pow, one_mul]

theorem su4W_diagU_zpow {K : Type} [Field K] {n : ℕ} (d : Fin n → Kˣ) (k : ℤ) :
    (diagU d : GL (Fin n) K) ^ k = diagU (d ^ k) :=
  (map_zpow (diagUHom : (Fin n → Kˣ) →* GL (Fin n) K) d k).symm

noncomputable def su4W_projCover {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2) :
    SU (unitaryInvolution (GaloisField p (2 * f)) p f) 4 →* projSU 4 p f :=
  (((Matrix.ProjGenLinGroup.mk : GL (Fin 4) (GaloisField p (2 * f)) →* _).comp
      (StatedSU 4 (p ^ f) (GaloisField p (2 * f))).subtype).codRestrict (projSU 4 p f)
      (fun x => by rw [Item424Res5.projSU_eq_map]; exact ⟨x, x.2, rfl⟩)).comp
    (equivStatedSU hF 4).toMonoidHom

theorem su4W_projCover_surjective {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2) :
    Function.Surjective (su4W_projCover hF) := by
  rintro ⟨y, hy⟩
  rw [Item424Res5.projSU_eq_map, Subgroup.mem_map] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  obtain ⟨s, hs⟩ := (equivStatedSU hF 4).surjective ⟨x, hx⟩
  refine ⟨s, Subtype.ext ?_⟩
  change Matrix.ProjGenLinGroup.mk
    ((((equivStatedSU hF 4) s : StatedSU 4 (p ^ f) (GaloisField p (2 * f))) :
      GL (Fin 4) (GaloisField p (2 * f)))) = y
  rw [hs]
  exact hxy

theorem su4W_projCover_ker {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2) :
    ∀ z ∈ (su4W_projCover hF).ker, z ^ 4 = 1 := by
  intro z hz
  have h1 : Matrix.ProjGenLinGroup.mk
      ((((equivStatedSU hF 4) z : StatedSU 4 (p ^ f) (GaloisField p (2 * f))) :
        GL (Fin 4) (GaloisField p (2 * f)))) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hz)
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
  obtain ⟨c, hc⟩ := h1
  have hdet := det_eq_one_of_mem_statedSU ((equivStatedSU hF 4) z).2
  rw [← hc] at hdet
  have hc4 : (c : GaloisField p (2 * f)) ^ 4 = 1 := by
    simpa [Matrix.GeneralLinearGroup.scalar] using hdet
  have hcu : c ^ 4 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hc4, Units.val_one])
  have h4 : (equivStatedSU hF 4) z ^ 4 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hc, ← map_pow, hcu, map_one]
    rfl
  apply (equivStatedSU hF 4).injective
  rw [map_pow, h4, map_one]

theorem listRow_projSU_four_of_dvd {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (h3 : 3 ∣ p ^ f - 1) :
    ListRow (projSU 4 p f) := by
  have hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  obtain ⟨g, hg3, hg1⟩ := su4W_exists_unit_cube_ne_one hF h3 hq
  have hg3F : (g : GaloisField p (2 * f)) ^ 3 = 1 := by
    have := congrArg Units.val hg3
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have hfix : unitaryInvolution (GaloisField p (2 * f)) p f (g : GaloisField p (2 * f)) =
      (g : GaloisField p (2 * f)) :=
    su4W_fix_of_pow_three hg3F h3
  have hfix1 : unitaryInvolution (GaloisField p (2 * f)) p f
      ((1 : (GaloisField p (2 * f))ˣ) : GaloisField p (2 * f)) =
      ((1 : (GaloisField p (2 * f))ˣ) : GaloisField p (2 * f)) := by
    simp
  let a : SU (unitaryInvolution (GaloisField p (2 * f)) p f) 4 :=
    ⟨diagU (dvec4 g 1), diagU_dvec4_mem_SU _ hfix hfix1⟩
  let b : SU (unitaryInvolution (GaloisField p (2 * f)) p f) 4 :=
    ⟨diagU (dvec4 1 g), diagU_dvec4_mem_SU _ hfix1 hfix⟩
  have ha3 : a ^ 3 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow]
    change (diagU (dvec4 g 1) : GL (Fin 4) (GaloisField p (2 * f))) ^ 3 = 1
    have hd : dvec4 g 1 ^ 3 = 1 := by
      funext i
      fin_cases i <;> simp [dvec4, hg3]
    rw [diagU_pow, hd, diagU_one]
  have hb3 : b ^ 3 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow]
    change (diagU (dvec4 1 g) : GL (Fin 4) (GaloisField p (2 * f))) ^ 3 = 1
    have hd : dvec4 1 g ^ 3 = 1 := by
      funext i
      fin_cases i <;> simp [dvec4, hg3]
    rw [diagU_pow, hd, diagU_one]
  have ha1 : a ≠ 1 := by
    intro h
    have h' : (diagU (dvec4 g 1) : GL (Fin 4) (GaloisField p (2 * f))) = 1 :=
      congrArg Subtype.val h
    have hd : dvec4 g 1 = 1 := diagU_injective (h'.trans diagU_one.symm)
    exact hg1 (by simpa [dvec4] using congrFun hd 0)
  have hab : a * b = b * a := by
    apply Subtype.ext
    change diagU (dvec4 g 1) * diagU (dvec4 1 g) = diagU (dvec4 1 g) * diagU (dvec4 g 1)
    rw [diagU_mul, diagU_mul]
    exact congrArg diagU (mul_comm _ _)
  have hbn : b ∉ Subgroup.zpowers a := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : (diagU (dvec4 g 1) : GL (Fin 4) (GaloisField p (2 * f))) ^ k =
        diagU (dvec4 1 g) := by
      have := congrArg Subtype.val hk
      rw [SubgroupClass.coe_zpow] at this
      exact this
    rw [su4W_diagU_zpow] at h1
    have h2 := diagU_injective h1
    have h4 := congrFun h2 1
    simp [dvec4] at h4
    first
      | exact hg1 h4.symm
      | exact hg1 h4
  exact listRow_of_cover_pair (su4W_projCover hF) (su4W_projCover_surjective hF)
    (su4W_projCover_ker hF)
    (fun E _ hexp hcard => Item424Res5.exists_weyl_su4 hF hf h3 E hexp hcard)
    ha3 ha1 hb3 hab hbn

theorem rowOf_four_SU_of_mod_one :
    ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 → RowOf (projSU 4 p 1) := by
  intro p _ hp hp1 S _ _ _ _ ⟨e⟩
  have h3 : 3 ∣ p ^ 1 - 1 := by
    rw [pow_one]
    omega
  exact GoodRow.of_mulEquiv e.symm
    ⟨listRow_projSU_four_of_dvd le_rfl h3, outerRow_of_not_three_dvd_outer (outU4p_holds p hp hp1)⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432

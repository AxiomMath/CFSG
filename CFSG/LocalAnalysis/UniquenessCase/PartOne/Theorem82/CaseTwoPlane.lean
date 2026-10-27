module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPoints
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPoints
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKy
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixedEnd
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.RankThree.GroupTheory.SteinbergBYAschCoreConjugacy
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeCardSubgroupIntersection
import CFSG.RankThree.PartOne.CTP.StrongPTransport
import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

private theorem commute_AA {a b : G} (ha : a ∈ t.d.AA) (hb : b ∈ t.d.AA) : a * b = b * a :=
  congrArg Subtype.val ((t.d.isElemAbelian_AA.1).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

private theorem sup_A_le_AA (i j : Fin 3) : t.d.A i ⊔ t.d.A j ≤ t.d.AA :=
  sup_le (t.A_le_AA i) (t.A_le_AA j)

private theorem sup_A_eq_AA_of_pairwise {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : t.d.A i ⊔ t.d.A j ⊔ t.d.A k = t.d.AA := by
  rw [t.d.AA_def]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
      | exact (hij rfl).elim
      | exact (hik rfl).elim
      | exact (hjk rfl).elim
      | ac_rfl


private theorem inf_sup_A_sup_A_eq {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    (t.d.A i ⊔ t.d.A j) ⊓ (t.d.A j ⊔ t.d.A k) = t.d.A j := by
  have hcomm : ∀ x ∈ (t.d.A i ⊔ t.d.A j), ∀ y ∈ (t.d.A j ⊔ t.d.A k),
      x * y = y * x :=
    fun x hx y hy => t.commute_AA (t.sup_A_le_AA i j hx) (t.sup_A_le_AA j k hy)
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (t.d.A i ⊔ t.d.A j) (t.d.A j ⊔ t.d.A k) hcomm).1
  rw [t.d.card_A_sup_A hij, t.d.card_A_sup_A hjk] at hprod
  have hsup_le : (t.d.A i ⊔ t.d.A j) ⊔ (t.d.A j ⊔ t.d.A k) ≤ t.d.AA :=
    sup_le (t.sup_A_le_AA i j) (t.sup_A_le_AA j k)
  have hsup_ge : t.d.AA ≤ (t.d.A i ⊔ t.d.A j) ⊔ (t.d.A j ⊔ t.d.A k) := by
    rw [← t.sup_A_eq_AA_of_pairwise hij hik hjk]
    exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have hsup : (t.d.A i ⊔ t.d.A j) ⊔ (t.d.A j ⊔ t.d.A k) = t.d.AA :=
    le_antisymm hsup_le hsup_ge
  have hsupcard : Nat.card (((t.d.A i ⊔ t.d.A j) ⊔ (t.d.A j ⊔ t.d.A k)) : Subgroup G) = 27 := by
    rw [hsup, t.d.card_AA]
  rw [hsupcard] at hprod
  have hinfcard : Nat.card (((t.d.A i ⊔ t.d.A j) ⊓ (t.d.A j ⊔ t.d.A k)) : Subgroup G) = 3 := by
    omega
  exact (Subgroup.eq_of_le_of_card_ge (H := t.d.A j)
    (K := (t.d.A i ⊔ t.d.A j) ⊓ (t.d.A j ⊔ t.d.A k))
    (le_inf le_sup_right le_sup_left) (by rw [hinfcard, t.d.card_A j])).symm


private theorem inf_sup_A01_centralizer_y_eq_bot :
    (t.d.A 0 ⊔ t.d.A 1) ⊓ Subgroup.centralizer ({t.y} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxJ, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxy : x * t.y = t.y * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hyconj : t.y * x * t.y⁻¹ = x := by
    calc t.y * x * t.y⁻¹ = x * t.y * t.y⁻¹ := by rw [← hxy]
      _ = x := by group
  obtain ⟨a0, ha0, a1, ha1, hxeq⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => t.d.S_commute a b (t.d.A_le_S 0 ha) (t.d.A_le_S 1 hb)) hxJ
  have hb1 : t.y * a0 * t.y⁻¹ ∈ t.d.A 1 := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj t.y).toMonoidHom ha0
    rwa [t.map_conj_A 0] at h
  have hb2 : t.y * a1 * t.y⁻¹ ∈ t.d.A 2 := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj t.y).toMonoidHom ha1
    rwa [t.map_conj_A 1] at h
  have hxeq2 : x = (t.y * a0 * t.y⁻¹) * (t.y * a1 * t.y⁻¹) := by
    rw [← hyconj, ← hxeq]
    group
  have hcoord := t.eq_of_mem_A_mul_eq
    (a0 := a0) (b0 := 1) (a1 := a1) (b1 := t.y * a0 * t.y⁻¹)
    (a2 := 1) (b2 := t.y * a1 * t.y⁻¹)
    ha0 (t.d.A 0).one_mem ha1 hb1 (t.d.A 2).one_mem hb2 (by
      rw [mul_one, one_mul, hxeq, hxeq2])
  have ha0one : a0 = 1 := hcoord.1
  have hx_a1 : x = a1 := by rw [← hxeq, ha0one, one_mul]
  have hy_a1 : t.y * a1 * t.y⁻¹ = a1 := by
    simpa [hx_a1] using hyconj
  have ha1_A2 : a1 ∈ t.d.A 2 := by
    rw [← hy_a1]
    exact hb2
  have hx_A1 : x ∈ t.d.A 1 := hx_a1 ▸ ha1
  have hx_A2 : x ∈ t.d.A 2 := hx_a1 ▸ ha1_A2
  have hbot : (t.d.A 1 ⊓ t.d.A 2 : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    exact (inf_le_inf le_rfl le_sup_right).trans
      (le_of_eq (t.inf_A_sup_A_eq_bot (i := 1) (j := 0) (k := 2) (by decide) (by decide)
        (by decide)))
  exact Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_inf.mpr ⟨hx_A1, hx_A2⟩)

private theorem inf_sup_A12_centralizer_y_eq_bot :
    (t.d.A 1 ⊔ t.d.A 2) ⊓ Subgroup.centralizer ({t.y} : Set G) = ⊥ := by
  have hmapJ : (t.d.A 0 ⊔ t.d.A 1).map (MulAut.conj t.y).toMonoidHom =
      t.d.A 1 ⊔ t.d.A 2 := by
    rw [Subgroup.map_sup, t.map_conj_A 0, t.map_conj_A 1]
    simp
  have hmapC : (Subgroup.centralizer ({t.y} : Set G)).map (MulAut.conj t.y).toMonoidHom =
      Subgroup.centralizer ({t.y} : Set G) := by
    have h1 : Subgroup.centralizer ({t.y} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers t.y : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [h1, CFSG.RankThree.GroupTheory.SteinbergBY.map_centralizer_mulEquiv]
    congr 1
    rw [MonoidHom.map_zpowers]
    congr 1
    simp [MulAut.conj_apply, mul_assoc]
  have h := congrArg (Subgroup.map (MulAut.conj t.y).toMonoidHom)
    (t.inf_sup_A01_centralizer_y_eq_bot)
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj t.y).injective, hmapJ, hmapC,
    Subgroup.map_bot] at h
  exact h

private theorem inf_sup_A20_centralizer_y_eq_bot :
    (t.d.A 2 ⊔ t.d.A 0) ⊓ Subgroup.centralizer ({t.y} : Set G) = ⊥ := by
  have hmapJ : (t.d.A 1 ⊔ t.d.A 2).map (MulAut.conj t.y).toMonoidHom =
      t.d.A 2 ⊔ t.d.A 0 := by
    rw [Subgroup.map_sup, t.map_conj_A 1, t.map_conj_A 2]
    simp
  have hmapC : (Subgroup.centralizer ({t.y} : Set G)).map (MulAut.conj t.y).toMonoidHom =
      Subgroup.centralizer ({t.y} : Set G) := by
    have h1 : Subgroup.centralizer ({t.y} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers t.y : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [h1, CFSG.RankThree.GroupTheory.SteinbergBY.map_centralizer_mulEquiv]
    congr 1
    rw [MonoidHom.map_zpowers]
    congr 1
    simp [MulAut.conj_apply, mul_assoc]
  have h := congrArg (Subgroup.map (MulAut.conj t.y).toMonoidHom)
    (t.inf_sup_A12_centralizer_y_eq_bot)
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj t.y).injective, hmapJ, hmapC,
    Subgroup.map_bot] at h
  exact h

private theorem inf_sup_A_centralizer_y_eq_bot {i j : Fin 3} (hij : i ≠ j) :
    (t.d.A i ⊔ t.d.A j) ⊓ Subgroup.centralizer ({t.y} : Set G) = ⊥ := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact t.inf_sup_A01_centralizer_y_eq_bot
  · convert t.inf_sup_A20_centralizer_y_eq_bot using 1
    dsimp only
    congr 1
    ac_rfl
  · convert t.inf_sup_A01_centralizer_y_eq_bot using 1
    dsimp only
    congr 1
    ac_rfl
  · exact absurd rfl hij
  · exact t.inf_sup_A12_centralizer_y_eq_bot
  · exact t.inf_sup_A20_centralizer_y_eq_bot
  · convert t.inf_sup_A12_centralizer_y_eq_bot using 1
    dsimp only
    congr 1
    ac_rfl
  · exact absurd rfl hij

private theorem inf_Z_sup_A_eq_bot {i j : Fin 3} (hij : i ≠ j) :
    t.Z ⊓ (t.d.A i ⊔ t.d.A j) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [← t.inf_sup_A_centralizer_y_eq_bot hij]
  exact ⟨hx.2, t.Z_le_centralizer hx.1⟩


private theorem card_inf_plane {B : Subgroup G} (hBA : B ≤ t.d.AA) (hB9 : Nat.card B = 9)
    (hZB : t.Z ≤ B) {i j : Fin 3} (hij : i ≠ j) :
    Nat.card ((B ⊓ (t.d.A i ⊔ t.d.A j)) : Subgroup G) = 3 := by
  have hcomm : ∀ x ∈ B, ∀ y ∈ t.d.A i ⊔ t.d.A j, x * y = y * x :=
    fun x hx y hy => t.commute_AA (hBA hx) (t.sup_A_le_AA i j hy)
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B
    (t.d.A i ⊔ t.d.A j) hcomm).1
  rw [hB9, t.d.card_A_sup_A hij] at hprod
  have hsupcard : Nat.card ((B ⊔ (t.d.A i ⊔ t.d.A j)) : Subgroup G) ≤ 27 := by
    calc Nat.card ((B ⊔ (t.d.A i ⊔ t.d.A j)) : Subgroup G)
        ≤ Nat.card t.d.AA := Subgroup.card_le_of_le (sup_le hBA (t.sup_A_le_AA i j))
      _ = 27 := t.d.card_AA
  have hinfdvd : Nat.card ((B ⊓ (t.d.A i ⊔ t.d.A j)) : Subgroup G) ∣ 9 := by
    rw [← hB9]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hinfne9 : Nat.card ((B ⊓ (t.d.A i ⊔ t.d.A j)) : Subgroup G) ≠ 9 := by
    intro h9
    have hBeq : B ⊓ (t.d.A i ⊔ t.d.A j) = B :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h9, hB9])
    have hZle : t.Z ≤ t.d.A i ⊔ t.d.A j := hZB.trans (hBeq ▸ inf_le_right)
    have hZbot : t.Z = ⊥ := by
      have hle : t.Z ≤ t.Z ⊓ (t.d.A i ⊔ t.d.A j) := le_inf le_rfl hZle
      rw [t.inf_Z_sup_A_eq_bot hij] at hle
      exact le_bot_iff.mp hle
    have hcard : Nat.card t.Z = 1 := by rw [hZbot]; simp
    rw [t.card_Z] at hcard
    norm_num at hcard
  have hge : 3 ≤ Nat.card ((B ⊓ (t.d.A i ⊔ t.d.A j)) : Subgroup G) := by
    have h := Nat.mul_le_mul_right (Nat.card ((B ⊓ (t.d.A i ⊔ t.d.A j)) : Subgroup G)) hsupcard
    rw [hprod] at h
    omega
  have hle : Nat.card ((B ⊓ (t.d.A i ⊔ t.d.A j)) : Subgroup G) ≤ 9 :=
    Nat.le_of_dvd (by norm_num) hinfdvd
  have hne : Nat.card ((B ⊓ (t.d.A i ⊔ t.d.A j)) : Subgroup G) ≠ 9 := hinfne9
  have hdvd : Nat.card ((B ⊓ (t.d.A i ⊔ t.d.A j)) : Subgroup G) ∣ 9 := hinfdvd
  set n := Nat.card ((B ⊓ (t.d.A i ⊔ t.d.A j)) : Subgroup G) with hn
  obtain ⟨k, hk, hkn⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three (m := 2) (i := n)).mp (by simpa using hdvd)
  interval_cases k <;> simp_all <;> omega

private theorem plane_X_ne {B : Subgroup G} (hBA : B ≤ t.d.AA) (hB9 : Nat.card B = 9)
    (hZB : t.Z ≤ B) (hyB : t.y ∈ Subgroup.normalizer (B : Set G))
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    B ⊓ (t.d.A i ⊔ t.d.A j) ≠ B ⊓ (t.d.A j ⊔ t.d.A k) := by
  intro heq
  have hXcard : Nat.card ((B ⊓ (t.d.A i ⊔ t.d.A j)) : Subgroup G) = 3 :=
    t.card_inf_plane hBA hB9 hZB hij
  have hXle : B ⊓ (t.d.A i ⊔ t.d.A j) ≤ t.d.A j := by
    have h1 : B ⊓ (t.d.A i ⊔ t.d.A j) ≤ t.d.A i ⊔ t.d.A j := inf_le_right
    have h2 : B ⊓ (t.d.A i ⊔ t.d.A j) ≤ t.d.A j ⊔ t.d.A k := by
      rw [heq]
      exact inf_le_right
    have h3 : B ⊓ (t.d.A i ⊔ t.d.A j) ≤
        (t.d.A i ⊔ t.d.A j) ⊓ (t.d.A j ⊔ t.d.A k) := le_inf h1 h2
    rwa [t.inf_sup_A_sup_A_eq hij hik hjk] at h3
  have hXeq : B ⊓ (t.d.A i ⊔ t.d.A j) = t.d.A j :=
    Subgroup.eq_of_le_of_card_ge hXle (by rw [hXcard, t.d.card_A j])
  have hAjB : t.d.A j ≤ B := hXeq ▸ inf_le_left
  have hyB' : B.map (MulAut.conj t.y).toMonoidHom = B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hyB
  have hyB2 : B.map (MulAut.conj (t.y ^ 2)).toMonoidHom = B := by
    have hcomp : (MulAut.conj (t.y ^ 2)).toMonoidHom =
        (MulAut.conj t.y).toMonoidHom.comp (MulAut.conj t.y).toMonoidHom := by
      ext z
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show t.y ^ 2 * z * (t.y ^ 2)⁻¹ = t.y * (t.y * z * t.y⁻¹) * t.y⁻¹ by
        rw [pow_two]; group]
    rw [hcomp, ← Subgroup.map_map, hyB', hyB']
  have hAj1 : t.d.A (j + 1) ≤ B := by
    have h : (t.d.A j).map (MulAut.conj t.y).toMonoidHom ≤ B := by
      have := Subgroup.map_mono (f := (MulAut.conj t.y).toMonoidHom) hAjB
      rwa [hyB'] at this
    rwa [t.map_conj_A j] at h
  have hAj2 : t.d.A (j + 2) ≤ B := by
    have h : (t.d.A j).map (MulAut.conj (t.y ^ 2)).toMonoidHom ≤ B := by
      have := Subgroup.map_mono (f := (MulAut.conj (t.y ^ 2)).toMonoidHom) hAjB
      rwa [hyB2] at this
    rwa [t.map_conj_A_two j] at h
  have hdist : j ≠ j + 1 ∧ j ≠ j + 2 ∧ j + 1 ≠ j + 2 := by
    fin_cases j <;> decide
  have hAAle : t.d.AA ≤ B := by
    have h := t.sup_A_eq_AA_of_pairwise (i := j) (j := j + 1) (k := j + 2)
      hdist.1 hdist.2.1 hdist.2.2
    rw [← h]
    exact sup_le (sup_le hAjB hAj1) hAj2
  have hcard := Subgroup.card_le_of_le hAAle
  rw [t.d.card_AA, hB9] at hcard
  omega

theorem exists_mem_A_sup_A_of_mem_plane {B : Subgroup G} (hBA : B ≤ t.d.AA)
    (hB9 : Nat.card B = 9) (hZB : t.Z ≤ B)
    (hyB : t.y ∈ Subgroup.normalizer (B : Set G)) {w : G} (hwB : w ∈ B)
    (hwZ : w ∉ t.Z) : ∃ i j : Fin 3, i ≠ j ∧ w ∈ t.d.A i ⊔ t.d.A j := by
  classical
  let X01 : Subgroup G := B ⊓ (t.d.A 0 ⊔ t.d.A 1)
  let X12 : Subgroup G := B ⊓ (t.d.A 1 ⊔ t.d.A 2)
  let X20 : Subgroup G := B ⊓ (t.d.A 2 ⊔ t.d.A 0)
  have h01 : Nat.card X01 = 3 := t.card_inf_plane hBA hB9 hZB (by decide)
  have h12 : Nat.card X12 = 3 := t.card_inf_plane hBA hB9 hZB (by decide)
  have h20 : Nat.card X20 = 3 := t.card_inf_plane hBA hB9 hZB (by decide)
  have hZne01 : t.Z ≠ X01 := by
    intro h
    have hZle : t.Z ≤ t.d.A 0 ⊔ t.d.A 1 := h ▸ inf_le_right
    have hZbot : t.Z = ⊥ := by
      have hle : t.Z ≤ t.Z ⊓ (t.d.A 0 ⊔ t.d.A 1) := le_inf le_rfl hZle
      rw [t.inf_Z_sup_A_eq_bot (by decide)] at hle
      exact le_bot_iff.mp hle
    have hcard : Nat.card t.Z = 1 := by rw [hZbot]; simp
    rw [t.card_Z] at hcard
    norm_num at hcard
  have hZne12 : t.Z ≠ X12 := by
    intro h
    have hZle : t.Z ≤ t.d.A 1 ⊔ t.d.A 2 := h ▸ inf_le_right
    have hZbot : t.Z = ⊥ := by
      have hle : t.Z ≤ t.Z ⊓ (t.d.A 1 ⊔ t.d.A 2) := le_inf le_rfl hZle
      rw [t.inf_Z_sup_A_eq_bot (by decide)] at hle
      exact le_bot_iff.mp hle
    have hcard : Nat.card t.Z = 1 := by rw [hZbot]; simp
    rw [t.card_Z] at hcard
    norm_num at hcard
  have hZne20 : t.Z ≠ X20 := by
    intro h
    have hZle : t.Z ≤ t.d.A 2 ⊔ t.d.A 0 := h ▸ inf_le_right
    have hZbot : t.Z = ⊥ := by
      have hle : t.Z ≤ t.Z ⊓ (t.d.A 2 ⊔ t.d.A 0) := le_inf le_rfl hZle
      rw [t.inf_Z_sup_A_eq_bot (by decide)] at hle
      exact le_bot_iff.mp hle
    have hcard : Nat.card t.Z = 1 := by rw [hZbot]; simp
    rw [t.card_Z] at hcard
    norm_num at hcard
  have hne0112 : X01 ≠ X12 :=
    t.plane_X_ne hBA hB9 hZB hyB (i := 0) (j := 1) (k := 2) (by decide) (by decide)
      (by decide)
  have hne1220 : X12 ≠ X20 :=
    t.plane_X_ne hBA hB9 hZB hyB (i := 1) (j := 2) (k := 0) (by decide) (by decide)
      (by decide)
  have hne2001 : X20 ≠ X01 :=
    t.plane_X_ne hBA hB9 hZB hyB (i := 2) (j := 0) (k := 1) (by decide) (by decide)
      (by decide)
  let N0 : Set G := (t.Z : Set G) \ {1}
  let N1 : Set G := (X01 : Set G) \ {1}
  let N2 : Set G := (X12 : Set G) \ {1}
  let N3 : Set G := (X20 : Set G) \ {1}
  have hdisj : ∀ {P Q : Subgroup G}, Nat.card P = 3 → Nat.card Q = 3 → P ≠ Q →
      Disjoint ((P : Set G) \ {1}) ((Q : Set G) \ {1}) := by
    intro P Q hP hQ hne
    rw [Set.disjoint_left]
    intro x hxP hxQ
    have hnot : ¬ Q ≤ P := by
      intro hle
      exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hQ, hP])).symm
    have hbot : (P ⊓ Q : Subgroup G) = ⊥ :=
      CFSG.GorensteinWalter.inf_eq_bot_of_not_le_of_prime_card P Q
        (by rw [hQ]; norm_num) hnot
    have hxinf : x ∈ P ⊓ Q := ⟨hxP.1, hxQ.1⟩
    rw [hbot] at hxinf
    exact hxP.2 (Subgroup.mem_bot.mp hxinf)
  have hd01 := hdisj t.card_Z h01 hZne01
  have hd02 := hdisj t.card_Z h12 hZne12
  have hd03 := hdisj t.card_Z h20 hZne20
  have hd12 := hdisj h01 h12 hne0112
  have hd13 := hdisj h01 h20 hne2001.symm
  have hd23 := hdisj h12 h20 hne1220
  have hN0 : N0.ncard = 2 := by
    rw [show N0 = (t.Z : Set G) \ {1} from rfl,
      Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem t.Z)]
    have hZset : (t.Z : Set G).ncard = 3 := by
      rw [← Nat.card_coe_set_eq]
      exact t.card_Z
    rw [hZset]
  have hN1 : N1.ncard = 2 := by
    rw [show N1 = (X01 : Set G) \ {1} from rfl,
      Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem X01)]
    have hset : (X01 : Set G).ncard = 3 := by
      rw [← Nat.card_coe_set_eq]
      exact h01
    rw [hset]
  have hN2 : N2.ncard = 2 := by
    rw [show N2 = (X12 : Set G) \ {1} from rfl,
      Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem X12)]
    have hset : (X12 : Set G).ncard = 3 := by
      rw [← Nat.card_coe_set_eq]
      exact h12
    rw [hset]
  have hN3 : N3.ncard = 2 := by
    rw [show N3 = (X20 : Set G) \ {1} from rfl,
      Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem X20)]
    have hset : (X20 : Set G).ncard = 3 := by
      rw [← Nat.card_coe_set_eq]
      exact h20
    rw [hset]
  have hd012 : Disjoint (N0 ∪ N1) N2 := hd02.union_left hd12
  have hd0123 : Disjoint (N0 ∪ N1 ∪ N2) N3 := (hd03.union_left hd13).union_left hd23
  have hunion : (N0 ∪ N1 ∪ N2 ∪ N3).ncard = 8 := by
    rw [Set.ncard_union_eq hd0123, Set.ncard_union_eq hd012, Set.ncard_union_eq hd01,
      hN0, hN1, hN2, hN3]
    try norm_num
  have hNsub : N0 ∪ N1 ∪ N2 ∪ N3 ⊆ (B : Set G) \ {1} := by
    intro x hx
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with ((hx0 | hx1) | hx2) | hx3
    · exact ⟨hZB hx0.1, hx0.2⟩
    · exact ⟨(Subgroup.mem_inf.mp hx1.1).1, hx1.2⟩
    · exact ⟨(Subgroup.mem_inf.mp hx2.1).1, hx2.2⟩
    · exact ⟨(Subgroup.mem_inf.mp hx3.1).1, hx3.2⟩
  have hBdiff : ((B : Set G) \ {1}).ncard = 8 := by
    rw [Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem B)]
    have hBset : (B : Set G).ncard = 9 := by
      rw [← Nat.card_coe_set_eq]
      exact hB9
    rw [hBset]
  have hUeq : N0 ∪ N1 ∪ N2 ∪ N3 = (B : Set G) \ {1} :=
    Set.eq_of_subset_of_ncard_le hNsub (by rw [hunion, hBdiff])
  have hw1 : w ≠ 1 := by
    intro h
    exact hwZ (h ▸ t.Z.one_mem)
  have hwU : w ∈ N0 ∪ N1 ∪ N2 ∪ N3 := by
    rw [hUeq]
    exact ⟨hwB, hw1⟩
  rcases (by simpa only [Set.mem_union] using hwU) with ((hw0 | hw1') | hw2) | hw3
  · exact absurd hw0.1 hwZ
  · exact ⟨0, 1, by decide, (Subgroup.mem_inf.mp hw1'.1).2⟩
  · exact ⟨1, 2, by decide, (Subgroup.mem_inf.mp hw2.1).2⟩
  · exact ⟨2, 0, by decide, (Subgroup.mem_inf.mp hw3.1).2⟩

theorem normalizer_plane_le {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    {B : Subgroup G} (hBA : B ≤ t.d.AA) (hB9 : Nat.card B = 9) (hZB : t.Z ≤ B)
    (hyB : t.y ∈ Subgroup.normalizer (B : Set G)) :
    Subgroup.normalizer (B : Set G) ≤ c.S.M := by
  classical
  have hpp : p.Prime := (c.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X01 : Subgroup G := B ⊓ (t.d.A 0 ⊔ t.d.A 1)
  let X12 : Subgroup G := B ⊓ (t.d.A 1 ⊔ t.d.A 2)
  have h01 : Nat.card X01 = 3 := t.card_inf_plane hBA hB9 hZB (by decide)
  have h12 : Nat.card X12 = 3 := t.card_inf_plane hBA hB9 hZB (by decide)
  have hne : X01 ≠ X12 :=
    t.plane_X_ne hBA hB9 hZB hyB (i := 0) (j := 1) (k := 2) (by decide) (by decide)
      (by decide)
  have hnebot : X01 ≠ ⊥ := by
    intro h
    rw [h] at h01
    simp at h01
  have hnebot' : X12 ≠ ⊥ := by
    intro h
    rw [h] at h12
    simp at h12
  intro g hg
  have hBg : B.map (MulAut.conj g).toMonoidHom = B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hinj : Function.Injective
      (fun H : Subgroup G => H.map (MulAut.conj g).toMonoidHom) :=
    (MulEquiv.mapSubgroup (MulAut.conj g)).injective
  have hne' : X01.map (MulAut.conj g).toMonoidHom ≠
      X12.map (MulAut.conj g).toMonoidHom := by
    intro h
    exact hne (hinj h)
  have hpos : X01.map (MulAut.conj g).toMonoidHom ≠ t.Z ∨
      X12.map (MulAut.conj g).toMonoidHom ≠ t.Z := by
    by_contra h
    push Not at h
    exact hne' (h.1.trans h.2.symm)
  have hmain : ∀ (X : Subgroup G) (i j : Fin 3), i ≠ j → Nat.card X = 3 →
      X ≤ t.d.A i ⊔ t.d.A j → X ≤ B → X.map (MulAut.conj g).toMonoidHom ≠ t.Z →
      g ∈ c.S.M := by
    intro X i j hij hXcard hXJ hXB hXgZ
    have hXgcard : Nat.card (X.map (MulAut.conj g).toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hXcard]
    have hnotle : ¬ (X.map (MulAut.conj g).toMonoidHom : Set G) ⊆ (t.Z : Set G) := by
      intro hle
      exact hXgZ (Subgroup.eq_of_le_of_card_ge hle (by rw [hXgcard, t.card_Z]))
    obtain ⟨w, hwXg, hwZ⟩ := Set.not_subset.mp hnotle
    have hwB : w ∈ B := by
      have hXg_le_B : X.map (MulAut.conj g).toMonoidHom ≤ B := by
        have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hXB
        rwa [hBg] at this
      exact hXg_le_B hwXg
    obtain ⟨k, l, hkl, hwkl⟩ :=
      t.exists_mem_A_sup_A_of_mem_plane hBA hB9 hZB hyB hwB hwZ
    have hXnebot : X ≠ ⊥ := by
      intro h
      rw [h] at hXcard
      simp at hXcard
    have hNle : Subgroup.normalizer (X : Set G) ≤ c.S.M :=
      hN.normalizer_le hij hXJ hXnebot
    have hC : Subgroup.centralizer (X : Set G) ≤ c.S.M :=
      (Subgroup.centralizer_le_normalizer _).trans hNle
    have hpairdvd : p ∣ Nat.card
        ((c.S.M ⊓ Subgroup.centralizer ((t.d.A k ⊔ t.d.A l : Subgroup G) : Set G)) : Subgroup G) :=
      hN.dvd_card (i := k) (j := l) hkl
    have hw3 : w ^ 3 = 1 := t.d.isElemAbelian_AA.2 w (hBA hwB)
    have hw1 : w ≠ 1 := by
      intro h
      exact hwZ (h ▸ t.Z.one_mem)
    have hwcard : Nat.card (Subgroup.zpowers w) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hw3 hw1]
    have hzp : Subgroup.zpowers w ≤ X.map (MulAut.conj g).toMonoidHom :=
      Subgroup.zpowers_le.mpr hwXg
    have hXg_eq : X.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers w :=
      (Subgroup.eq_of_le_of_card_ge hzp (by rw [hwcard, hXgcard])).symm
    have hcent_eq : Subgroup.centralizer (X.map (MulAut.conj g).toMonoidHom : Set G) =
        Subgroup.centralizer ({w} : Set G) := by
      rw [hXg_eq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hcent_le : Subgroup.centralizer ((t.d.A k ⊔ t.d.A l : Subgroup G) : Set G) ≤
        Subgroup.centralizer (X.map (MulAut.conj g).toMonoidHom : Set G) := by
      rw [hcent_eq]
      exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hwkl)
    have hle : c.S.M ⊓ Subgroup.centralizer ((t.d.A k ⊔ t.d.A l : Subgroup G) : Set G) ≤
        c.S.M ⊓ Subgroup.centralizer (X.map (MulAut.conj g).toMonoidHom : Set G) :=
      inf_le_inf le_rfl hcent_le
    have hdvd := hpairdvd.trans (Subgroup.card_dvd_of_le hle)
    exact CFSG.RankThree.PartOne.IsStronglyPEmbedded.mem_of_centralizer_le
      (hY := c.isStronglyPEmbedded_of_mem_sigma hp) (hX := hC) (hp := hdvd)
  rcases hpos with h1 | h2
  · exact hmain X01 0 1 (by decide) h01 inf_le_right inf_le_left h1
  · exact hmain X12 1 2 (by decide) h12 inf_le_right inf_le_left h2

private theorem centralizer_y_inv :
    Subgroup.centralizer ({t.y⁻¹} : Set G) = Subgroup.centralizer ({t.y} : Set G) := by
  calc Subgroup.centralizer ({t.y⁻¹} : Set G)
      = Subgroup.centralizer (Subgroup.zpowers t.y⁻¹ : Set G) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    _ = Subgroup.centralizer (Subgroup.zpowers t.y : Set G) := by rw [Subgroup.zpowers_inv]
    _ = Subgroup.centralizer ({t.y} : Set G) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

private theorem dvd_card_inf_centralizer_conj {p : ℕ} [Fact p.Prime] {x w s : G}
    (hsM : s ∈ c.S.M) (hs : s * x * s⁻¹ = w)
    (h : p ∣ Nat.card ((c.S.M ⊓ Subgroup.centralizer ({w} : Set G)) : Subgroup G)) :
    p ∣ Nat.card ((c.S.M ⊓ Subgroup.centralizer ({x} : Set G)) : Subgroup G) := by
  have hxw : x = s⁻¹ * w * s := by
    calc x = s⁻¹ * (s * x * s⁻¹) * s := by group
      _ = s⁻¹ * w * s := by rw [hs]
  have hMeq : c.S.M.map (MulAut.conj s⁻¹).toMonoidHom = c.S.M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (H := c.S.M) (c.S.M.inv_mem hsM))
  have hcent_zp : (Subgroup.centralizer (Subgroup.zpowers w : Set G)).map
      (MulAut.conj s⁻¹).toMonoidHom =
      Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.map_centralizer_mulEquiv]
    congr 1
    rw [MonoidHom.map_zpowers]
    congr 1
    rw [hxw]
    try simp [MulAut.conj_apply]
  have hcent : (Subgroup.centralizer ({w} : Set G)).map
      (MulAut.conj s⁻¹).toMonoidHom = Subgroup.centralizer ({x} : Set G) := by
    have hw : Subgroup.centralizer ({w} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers w : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hx : Subgroup.centralizer ({x} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hw, hx, hcent_zp]
  have hEq : (c.S.M ⊓ Subgroup.centralizer ({w} : Set G)).map
      (MulAut.conj s⁻¹).toMonoidHom = c.S.M ⊓ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj s⁻¹).injective, hMeq, hcent]
  have hcard : Nat.card ((c.S.M ⊓ Subgroup.centralizer ({x} : Set G)) : Subgroup G) =
      Nat.card ((c.S.M ⊓ Subgroup.centralizer ({w} : Set G)) : Subgroup G) := by
    rw [← hEq, Subgroup.card_map_of_injective (MulAut.conj s⁻¹).injective]
  rw [hcard]
  exact h

theorem false_of_conj_plane {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hpL : p ∣ Nat.card c.L) {B R : Subgroup G} (hBA : B ≤ t.d.AA) (hB9 : Nat.card B = 9)
    (hZB : t.Z ≤ B) (hRP : R ≤ t.P) (hBR : t.d.AA ⊓ R = B) {h : G}
    (hh : h ∈ Subgroup.centralizer (t.Z : Set G))
    (hhR : B.map (MulAut.conj h).toMonoidHom ≤ R)
    (hne : B.map (MulAut.conj h).toMonoidHom ≠ B) : False := by
  classical
  have hpp : p.Prime := (c.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X : Subgroup G := B ⊓ (t.d.A 0 ⊔ t.d.A 1)
  have hXcard : Nat.card X = 3 := t.card_inf_plane hBA hB9 hZB (by decide)
  have hXnebot : X ≠ ⊥ := by
    intro hX
    rw [hX] at hXcard
    simp at hXcard
  have hNle : Subgroup.normalizer (X : Set G) ≤ c.S.M :=
    hN.normalizer_le (by decide) inf_le_right hXnebot
  have hC : Subgroup.centralizer (X : Set G) ≤ c.S.M :=
    (Subgroup.centralizer_le_normalizer _).trans hNle
  have hZh : t.Z.map (MulAut.conj h).toMonoidHom = t.Z :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _ hh)
  have hXneZ : X ≠ t.Z := by
    intro hXZ
    have hZle : t.Z ≤ t.d.A 0 ⊔ t.d.A 1 := hXZ ▸ inf_le_right
    have hZbot : t.Z = ⊥ := by
      have hle : t.Z ≤ t.Z ⊓ (t.d.A 0 ⊔ t.d.A 1) := le_inf le_rfl hZle
      rw [t.inf_Z_sup_A_eq_bot (by decide)] at hle
      exact le_bot_iff.mp hle
    have hcard : Nat.card t.Z = 1 := by rw [hZbot]; simp
    rw [t.card_Z] at hcard
    norm_num at hcard
  have hXhneZ : X.map (MulAut.conj h).toMonoidHom ≠ t.Z := by
    intro hXh
    have hinj : Function.Injective
        (fun H : Subgroup G => H.map (MulAut.conj h).toMonoidHom) :=
      (MulEquiv.mapSubgroup (MulAut.conj h)).injective
    exact hXneZ (hinj (by
      change X.map (MulAut.conj h).toMonoidHom = t.Z.map (MulAut.conj h).toMonoidHom
      rw [hXh, hZh]))
  have hXh_le_R : X.map (MulAut.conj h).toMonoidHom ≤ R :=
    (Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) inf_le_left).trans hhR
  by_cases hXA : X.map (MulAut.conj h).toMonoidHom ≤ t.d.AA
  · have hXh_le_B : X.map (MulAut.conj h).toMonoidHom ≤ B := by
      rw [← hBR]
      exact le_inf hXA hXh_le_R
    have hZneX : t.Z ≠ X := hXneZ.symm
    have hcomm : ∀ a ∈ t.Z, ∀ b ∈ X, a * b = b * a :=
      fun a ha b hb => t.commute_AA (t.Z_le_AA ha) (t.sup_A_le_AA 0 1 (Subgroup.mem_inf.mp hb).2)
    have hinf : (t.Z ⊓ X : Subgroup G) = ⊥ :=
      CFSG.GorensteinWalter.inf_eq_bot_of_not_le_of_prime_card t.Z X
        (by rw [hXcard]; norm_num) (by
          intro hle
          exact hZneX (Subgroup.eq_of_le_of_card_ge hle (by rw [hXcard, t.card_Z])).symm)
    have hcardZX : Nat.card ((t.Z ⊔ X) : Subgroup G) = 9 := by
      have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute t.Z X hcomm).1
      rw [hinf, t.card_Z, hXcard] at hprod
      simpa using hprod
    have hB_eq : B = t.Z ⊔ X :=
      (Subgroup.eq_of_le_of_card_ge (sup_le hZB inf_le_left)
        (by rw [hcardZX, hB9])).symm
    have hB_eq' : B = t.Z ⊔ X := hB_eq
    have hBh : B.map (MulAut.conj h).toMonoidHom = t.Z ⊔ X.map (MulAut.conj h).toMonoidHom := by
      rw [hB_eq', Subgroup.map_sup, hZh]
    have hcardXh : Nat.card ((t.Z ⊔ X.map (MulAut.conj h).toMonoidHom) : Subgroup G) = 9 := by
      have hcomm' : ∀ a ∈ t.Z, ∀ b ∈ X.map (MulAut.conj h).toMonoidHom, a * b = b * a :=
        fun a ha b hb => t.commute_AA (t.Z_le_AA ha) (hXA hb)
      have hinf' : (t.Z ⊓ X.map (MulAut.conj h).toMonoidHom : Subgroup G) = ⊥ :=
        CFSG.GorensteinWalter.inf_eq_bot_of_not_le_of_prime_card t.Z
          (X.map (MulAut.conj h).toMonoidHom)
          (by
            rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hXcard]
            norm_num)
          (by
            intro hle
            exact hXhneZ (Subgroup.eq_of_le_of_card_ge hle
              (by rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hXcard,
                t.card_Z])))
      have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute t.Z
        (X.map (MulAut.conj h).toMonoidHom) hcomm').1
      rw [hinf', t.card_Z,
        Subgroup.card_map_of_injective (MulAut.conj h).injective, hXcard] at hprod
      simpa using hprod
    have hBeq : t.Z ⊔ X.map (MulAut.conj h).toMonoidHom = B :=
      Subgroup.eq_of_le_of_card_ge (sup_le hZB hXh_le_B)
        (by rw [hcardXh, hB9])
    exact hne (by rw [hBh, hBeq])
  · obtain ⟨x, hxX, hxA⟩ := Set.not_subset.mp hXA
    have hxR : x ∈ R :=
      hhR (Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) inf_le_left hxX)
    have hxP : x ∈ t.P := hRP hxR
    have hx1 : x ≠ 1 := by
      intro hx
      exact hxA (hx ▸ t.d.AA.one_mem)
    have hx3 : x ^ 3 = 1 := by
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxX
      rw [← hyx]
      have hy3 : y ^ 3 = 1 := t.d.isElemAbelian_AA.2 y (inf_le_left.trans hBA hy)
      calc (h * y * h⁻¹) ^ 3 = ((MulAut.conj h) y) ^ 3 := by
            rw [show h * y * h⁻¹ = (MulAut.conj h) y by rfl]
        _ = (MulAut.conj h) (y ^ 3) := (map_pow (MulAut.conj h) y 3).symm
        _ = 1 := by rw [hy3, map_one]
    have hdvd_y : p ∣ Nat.card
        ((c.S.M ⊓ Subgroup.centralizer ({t.y} : Set G)) : Subgroup G) :=
      t.dvd_card_inf_centralizer (c.sig_prime p hp).2 hpL
    have hconj_cases := t.mem_AA_or_exists_conj_eq hxP hx3
    rcases hconj_cases with hxAA | ⟨s, hsS, hsxy | hsxy⟩
    · exact hxA hxAA
    · have hsM : s ∈ c.S.M := by
        have hsL : s ∈ c.L := (t.hdS ▸ hsS).2
        exact c.hyp81.1 hsL
      have hdvd_x := dvd_card_inf_centralizer_conj (c := c) (p := p) hsM hsxy hdvd_y
      have hXhcard : Nat.card (X.map (MulAut.conj h).toMonoidHom) = 3 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hXcard]
      have hzp : Subgroup.zpowers x ≤ X.map (MulAut.conj h).toMonoidHom :=
        Subgroup.zpowers_le.mpr hxX
      have hXh_eq : X.map (MulAut.conj h).toMonoidHom = Subgroup.zpowers x :=
        (Subgroup.eq_of_le_of_card_ge hzp
          (by rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1, hXhcard])).symm
      have hcent_eq : Subgroup.centralizer (X.map (MulAut.conj h).toMonoidHom : Set G) =
          Subgroup.centralizer ({x} : Set G) := by
        rw [hXh_eq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      have hdvd_Xh : p ∣ Nat.card
          ((c.S.M ⊓ Subgroup.centralizer
            (X.map (MulAut.conj h).toMonoidHom : Set G)) : Subgroup G) := by
        rw [hcent_eq]
        exact hdvd_x
      have hM : h ∈ c.S.M :=
        CFSG.RankThree.PartOne.IsStronglyPEmbedded.mem_of_centralizer_le
          (hY := c.isStronglyPEmbedded_of_mem_sigma hp) (hX := hC) (hp := hdvd_Xh)
      have hXh_le_L : X.map (MulAut.conj h).toMonoidHom ≤ c.L := by
        have hXL : X ≤ c.L := (inf_le_right.trans (t.sup_A_le_AA 0 1)).trans
          (t.hdL ▸ t.d.AA_le_L)
        have hLh : c.L.map (MulAut.conj h).toMonoidHom = c.L :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp (c.le_normalizer_L hM)
        exact (Subgroup.map_mono hXL).trans (le_of_eq hLh)
      have hxL : x ∈ c.L := hXh_le_L hxX
      have hxS : x ∈ t.d.S := by
        rw [t.hdS]
        exact ⟨hxP, hxL⟩
      exact hxA (t.d.mem_AA_of_pow_eq_one hxS hx3)
    · have hsM : s ∈ c.S.M := by
        have hsL : s ∈ c.L := (t.hdS ▸ hsS).2
        exact c.hyp81.1 hsL
      have hdvd_yinv : p ∣ Nat.card
          ((c.S.M ⊓ Subgroup.centralizer ({t.y⁻¹} : Set G)) : Subgroup G) := by
        rw [t.centralizer_y_inv]
        exact hdvd_y
      have hdvd_x := dvd_card_inf_centralizer_conj (c := c) (p := p) hsM hsxy hdvd_yinv
      have hXhcard : Nat.card (X.map (MulAut.conj h).toMonoidHom) = 3 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hXcard]
      have hzp : Subgroup.zpowers x ≤ X.map (MulAut.conj h).toMonoidHom :=
        Subgroup.zpowers_le.mpr hxX
      have hXh_eq : X.map (MulAut.conj h).toMonoidHom = Subgroup.zpowers x :=
        (Subgroup.eq_of_le_of_card_ge hzp
          (by rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1, hXhcard])).symm
      have hcent_eq : Subgroup.centralizer (X.map (MulAut.conj h).toMonoidHom : Set G) =
          Subgroup.centralizer ({x} : Set G) := by
        rw [hXh_eq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      have hdvd_Xh : p ∣ Nat.card
          ((c.S.M ⊓ Subgroup.centralizer
            (X.map (MulAut.conj h).toMonoidHom : Set G)) : Subgroup G) := by
        rw [hcent_eq]
        exact hdvd_x
      have hM : h ∈ c.S.M :=
        CFSG.RankThree.PartOne.IsStronglyPEmbedded.mem_of_centralizer_le
          (hY := c.isStronglyPEmbedded_of_mem_sigma hp) (hX := hC) (hp := hdvd_Xh)
      have hXh_le_L : X.map (MulAut.conj h).toMonoidHom ≤ c.L := by
        have hXL : X ≤ c.L := (inf_le_right.trans (t.sup_A_le_AA 0 1)).trans
          (t.hdL ▸ t.d.AA_le_L)
        have hLh : c.L.map (MulAut.conj h).toMonoidHom = c.L :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp (c.le_normalizer_L hM)
        exact (Subgroup.map_mono hXL).trans (le_of_eq hLh)
      have hxL : x ∈ c.L := hXh_le_L hxX
      have hxS : x ∈ t.d.S := by
        rw [t.hdS]
        exact ⟨hxP, hxL⟩
      exact hxA (t.d.mem_AA_of_pow_eq_one hxS hx3)

theorem pPrimeCore_le {p : ℕ} (hN : t.PairNormalizerLe p)
    {H : Subgroup G} (hA : t.d.A 0 ⊔ t.d.A 1 ≤ H) :
    (CFSG.pPrimeCore 3 ↥H).map H.subtype ≤ c.S.M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let E : Subgroup G := t.d.A 0 ⊔ t.d.A 1
  let K : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let EH : Subgroup ↥H := E.subgroupOf H
  have hEH_elem : CFSG.Open.IsElemAbelian 3 EH := by
    have h := (t.d.isElemAbelian_A_sup_A 0 1).comap (f := H.subtype) H.subtype_injective
    rw [Subgroup.comap_subtype] at h
    simpa [E] using h
  have hEcard : Nat.card E = 9 := by
    rw [show E = t.d.A 0 ⊔ t.d.A 1 from rfl, t.d.card_A_sup_A (by decide)]
    norm_num
  have hEHcard : Nat.card EH = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hEcard]
  have hrank : 3 ^ 2 ≤ Nat.card EH := by rw [hEHcard]; norm_num
  have hKnormal : K.Normal := CFSG.pPrimeCore_normal (p := 3) (G := ↥H)
  have hnorm : EH ≤ Subgroup.normalizer (K : Set ↥H) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hKnormal]
    exact le_top
  have hcop : Nat.Coprime 3 (Nat.card K) :=
    CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H)
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity
    (p := 3) Nat.prime_three (A := EH) (X := K) hEH_elem hrank hnorm hcop
  have hXeq : K.map H.subtype = ⨆ (a : ↥H) (_ : a ∈ EH) (_ : a ≠ 1),
      (K ⊓ Subgroup.centralizer ({a} : Set ↥H)).map H.subtype := by
    conv_lhs => rw [← hgen]
    simp only [Subgroup.map_iSup]
  rw [hXeq]
  refine iSup_le (fun a => iSup_le (fun ha => iSup_le (fun ha1 => ?_)))
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  have haE : (a : G) ∈ E := Subgroup.mem_subgroupOf.mp ha
  have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hYle : Subgroup.zpowers (a : G) ≤ t.d.A 0 ⊔ t.d.A 1 := by
    simpa [E] using Subgroup.zpowers_le.mpr haE
  have hYne : Subgroup.zpowers (a : G) ≠ ⊥ := by
    rw [Subgroup.zpowers_ne_bot]
    exact ha1'
  apply hN.normalizer_le (by decide) hYle hYne
  have hcomm : (z : G) * (a : G) = (a : G) * (z : G) := by
    simpa using congrArg (fun u : ↥H => (u : G))
      (Subgroup.mem_centralizer_singleton_iff.mp hz.2)
  have hzcent : (z : G) ∈ Subgroup.centralizer (Subgroup.zpowers (a : G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  exact Subgroup.centralizer_le_normalizer _ hzcent

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

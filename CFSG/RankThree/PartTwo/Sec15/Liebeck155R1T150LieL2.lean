module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Core
import CFSG.CharacterTheory.Semidihedral.AllPrimeSL2Sections
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.Glauberman.Dickson
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

private theorem k150_not_isPerfect_of_surjective_comm {X A : Type*} [Group X] [CommGroup A]
    [Nontrivial A] (φ : X →* A) (hφ : Function.Surjective φ) : ¬ Group.IsPerfect X := by
  intro hperf
  have hle := Abelianization.commutator_subset_ker φ
  rw [@Group.IsPerfect.commutator_eq_top _ _ hperf, top_le_iff] at hle
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  obtain ⟨x, rfl⟩ := hφ a
  exact ha ((MonoidHom.mem_ker).mp (hle ▸ Subgroup.mem_top x))

private def k150DihedralParity (n : ℕ) : DihedralGroup n →* Multiplicative (ZMod 2) where
  toFun
    | .r _ => 1
    | .sr _ => Multiplicative.ofAdd 1
  map_one' := rfl
  map_mul' := by
    rintro (a | a) (b | b) <;> simp only [DihedralGroup.r_mul_r,
      DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
    · rfl
    · exact (one_mul _).symm
    · exact (mul_one _).symm
    · change Multiplicative.ofAdd (0 : ZMod 2) = Multiplicative.ofAdd (1 + 1)
      decide

private theorem k150_dihedral_not_isPerfect (n : ℕ) : ¬ Group.IsPerfect (DihedralGroup n) := by
  have : Nontrivial (Multiplicative (ZMod 2)) := by
    refine ⟨⟨1, Multiplicative.ofAdd 1, ?_⟩⟩
    decide
  refine k150_not_isPerfect_of_surjective_comm (k150DihedralParity n) ?_
  intro a
  have ha : a = 1 ∨ a = Multiplicative.ofAdd 1 := by
    revert a
    decide
  rcases ha with rfl | rfl
  · exact ⟨1, rfl⟩
  · exact ⟨DihedralGroup.sr 0, rfl⟩

private theorem k150_card_alternating_four : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

private theorem k150_card_alternating_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

private theorem k150_card_perm_four : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

private theorem k150_card_psl2_three {m : ℕ} (hm : m ≠ 0) :
    Nat.card (PSL2MatrixGroup (GaloisField 3 m)) * 2 = 3 ^ m * ((3 ^ m) ^ 2 - 1) := by
  have hcard : Nat.card (GaloisField 3 m) = 3 ^ m := GaloisField.card 3 m hm
  have h := CFSG.Semidihedral.AllPrime.SL2Sections.card_psl2_mul_two (F := GaloisField 3 m)
    (by rw [hcard]; exact (show Odd 3 by decide).pow)
  rwa [hcard] at h

theorem k150_psl2_perfect_surj_false {F : Type} [Field F] [Finite F]
    {f : ℕ} (hF : Nat.card F = 3 ^ f) {J : Type} [Group J]
    (hJna : ∃ a b : J, a * b ≠ b * a) (hJ60 : 60 < Nat.card J)
    (hJord : ∀ m : ℕ, m ≠ 0 → 2 * Nat.card J ≠ 3 ^ m * ((3 ^ m) ^ 2 - 1))
    (X : Subgroup (PSL2MatrixGroup F)) (hX : Group.IsPerfect X) (π : X →* J)
    (hπ : Function.Surjective π) : False := by
  have hbig : 60 < Nat.card X := hJ60.trans_le (Nat.card_le_card_of_surjective π hπ)
  have hcomm_false : (∀ a b : X, a * b = b * a) → False := fun hc => by
    obtain ⟨a, b, hab⟩ := hJna
    obtain ⟨x, rfl⟩ := hπ a
    obtain ⟨y, rfl⟩ := hπ b
    exact hab (by rw [← map_mul, ← map_mul, hc x y])
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification hF X with
    hE | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, N, C, hN, hNe, -, hC, -, -, hNC⟩ | ⟨m, hm, hmf, ⟨e⟩⟩ | ⟨m, hm, hmf, ⟨e⟩⟩
  · exact hcomm_false fun a b => hE.toIsMulCommutative.is_comm.comm a b
  · let : CommGroup X := IsCyclic.commGroup
    exact hcomm_false fun a b => mul_comm a b
  · exact k150_dihedral_not_isPerfect z
      (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
  · rw [Nat.card_congr e.toEquiv, k150_card_alternating_four] at hbig
    omega
  · rw [Nat.card_congr e.toEquiv, k150_card_perm_four] at hbig
    omega
  · rw [Nat.card_congr e.toEquiv, k150_card_alternating_five] at hbig
    omega
  ·
    have hNcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hNe.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
      intro a ha b hb
      let : CommGroup C := IsCyclic.commGroup
      exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : C) ⟨b, hb⟩)
    have hcomm : commutator X ≤ N := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨n₁, hn₁, c₁, hc₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp
        (hNC ▸ Subgroup.mem_top a)
      obtain ⟨n₂, hn₂, c₂, hc₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp
        (hNC ▸ Subgroup.mem_top b)
      have h1 : QuotientGroup.mk' N n₁ = 1 := (QuotientGroup.eq_one_iff n₁).mpr hn₁
      have h2 : QuotientGroup.mk' N n₂ = 1 := (QuotientGroup.eq_one_iff n₂).mpr hn₂
      have hq : QuotientGroup.mk' N ⁅n₁ * c₁, n₂ * c₂⁆ = 1 := by
        rw [map_commutatorElement, map_mul, map_mul, h1, h2,
          one_mul, one_mul, ← map_commutatorElement, commutatorElement_def,
          hCcomm c₁ hc₁ c₂ hc₂, mul_inv_cancel_right, mul_inv_cancel, map_one]
      exact (QuotientGroup.eq_one_iff _).mp hq
    rw [@Group.IsPerfect.commutator_eq_top _ _ hX, top_le_iff] at hcomm
    exact hcomm_false fun a b =>
      hNcomm a (hcomm ▸ Subgroup.mem_top a) b (hcomm ▸ Subgroup.mem_top b)
  ·
    have hgal := k150_card_psl2_three hm
    have hXcard : Nat.card X = Nat.card (PSL2MatrixGroup (GaloisField 3 m)) :=
      Nat.card_congr e.toEquiv
    have hgcard : Nat.card (GaloisField 3 m) = 3 ^ m := GaloisField.card 3 m hm
    have hm1 : m ≠ 1 := by
      rintro rfl
      rw [hXcard] at hbig
      have : Nat.card (PSL2MatrixGroup (GaloisField 3 1)) * 2 = 24 := by
        rw [hgal]
        norm_num
      omega
    have hpm : 3 ^ m ≠ 3 := by
      intro h
      have : 3 ^ m = 3 ^ 1 := by rw [h]; norm_num
      exact hm1 (Nat.pow_right_injective (by norm_num : 2 ≤ 3) this)
    have hpm2 : 3 ^ m ≠ 2 := by
      intro h
      have h3 : 3 ∣ 3 ^ m := dvd_pow_self 3 hm
      rw [h] at h3
      omega
    have : IsSimpleGroup (PSL2MatrixGroup (GaloisField 3 m)) :=
      huppert_II_6_13 2 le_rfl (Or.inr (by rw [hgcard]; exact hpm2))
        (Or.inr (by rw [hgcard]; exact hpm))
    have : IsSimpleGroup X := e.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hker | hker
    · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hker
      have hbij := Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ⟩)
      exact hJord m hm (by rw [← hbij, hXcard, mul_comm]; exact hgal)
    · obtain ⟨a, b, hab⟩ := hJna
      obtain ⟨x, rfl⟩ := hπ a
      obtain ⟨y, rfl⟩ := hπ b
      have hx : π x = 1 := (MonoidHom.mem_ker).mp (hker ▸ Subgroup.mem_top x)
      have hy : π y = 1 := (MonoidHom.mem_ker).mp (hker ▸ Subgroup.mem_top y)
      exact hab (by rw [hx, hy])
  ·
    have hgcard : Nat.card (GaloisField 3 m) = 3 ^ m := GaloisField.card 3 m hm
    exact CFSG.Semidihedral.AllPrime.SL2Sections.not_isPerfect_pgl2 (F := GaloisField 3 m)
      (by rw [hgcard]; exact (show Odd 3 by decide).pow)
      (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)

theorem k150_not_psl2_card {N : ℕ} (M : ℕ) (h : 2 * N < 3 ^ M * ((3 ^ M) ^ 2 - 1))
    (hs : ∀ m, m < M → m ≠ 0 → 2 * N ≠ 3 ^ m * ((3 ^ m) ^ 2 - 1)) :
    ∀ m : ℕ, m ≠ 0 → 2 * N ≠ 3 ^ m * ((3 ^ m) ^ 2 - 1) := by
  intro m hm
  by_cases hmM : m < M
  · exact hs m hmM hm
  · have hM : M ≤ m := not_lt.mp hmM
    have h1 : 3 ^ M ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hM
    have h2 : 3 ^ M * ((3 ^ M) ^ 2 - 1) ≤ 3 ^ m * ((3 ^ m) ^ 2 - 1) :=
      Nat.mul_le_mul h1 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h1 2) 1)
    omega

theorem k150_rowAll_projSL_two_three {J : Type} [Group J]
    (hJna : ∃ a b : J, a * b ≠ b * a) (hJ60 : 60 < Nat.card J)
    (hJord : ∀ m : ℕ, m ≠ 0 → 2 * Nat.card J ≠ 3 ^ m * ((3 ^ m) ^ 2 - 1)) (e : ℕ) (he : 1 ≤ e) :
    RowAllOfK150 J (projSL 2 (GaloisField 3 e)) := by
  intro S _ _ _ _ ⟨eS⟩ σ _ _ P _ _ hPp N _
  refine ⟨fun e' => ?_⟩
  let φ : S ≃* PSL2MatrixGroup (GaloisField 3 e) := eS.trans (Sec4.projSLEquivPSL (GaloisField 3 e))
  let eP : P ≃* P.map φ.toMonoidHom := P.equivMapOfInjective φ.toMonoidHom φ.injective
  have hperf : Group.IsPerfect (P.map φ.toMonoidHom) := Group.IsPerfect.map φ.toMonoidHom
  let π : P.map φ.toMonoidHom →* J :=
    (e'.toMonoidHom.comp (QuotientGroup.mk' N)).comp eP.symm.toMonoidHom
  have hπ : Function.Surjective π :=
    (e'.surjective.comp (QuotientGroup.mk'_surjective N)).comp eP.symm.surjective
  exact k150_psl2_perfect_surj_false (GaloisField.card 3 e (by omega)) hJna hJ60 hJord
    (P.map φ.toMonoidHom) hperf π hπ

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

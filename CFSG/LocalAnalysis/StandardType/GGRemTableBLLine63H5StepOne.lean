module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5NotNine
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.Assembly

variable {K : Type} [Field K] {n : ℕ}

theorem diagHom_const_eq_scalar (z : Kˣ) :
    (diagHom 6 (fun _ => z) : GL (Fin 6) K) = GeneralLinearGroup.scalar (Fin 6) z := by
  refine Units.ext ?_
  rw [coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

theorem mem_zpowers_of_isCyclic_of_pow_three {G : Type*} [Group G] {S : Subgroup G} [Finite S]
    (hS : IsCyclic S) {x c : G} (hxS : x ∈ S) (hcS : c ∈ S) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hc3 : c ^ 3 = 1) : c ∈ Subgroup.zpowers x := by
  classical
  haveI : Fintype S := Fintype.ofFinite S
  by_contra hc
  set X : S := ⟨x, hxS⟩ with hX
  set C : S := ⟨c, hcS⟩ with hC
  have hX3 : X ^ 3 = 1 := Subtype.ext hx3
  have hX1 : X ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hC3 : C ^ 3 = 1 := Subtype.ext hc3
  have hX2 : X ^ 2 ≠ 1 := by
    intro h
    apply hX1
    calc X = X ^ 3 * (X ^ 2)⁻¹ := by group
      _ = 1 := by rw [hX3, h]; group
  have hXX : X ≠ X ^ 2 := by
    intro h
    apply hX1
    calc X = X ^ 2 * X⁻¹ := by group
      _ = X * X⁻¹ := by rw [← h]
      _ = 1 := by group
  have hC0 : C ≠ 1 := by
    intro h
    apply hc
    rw [show c = 1 from congrArg Subtype.val h]
    exact Subgroup.one_mem _
  have hCX : C ≠ X := by
    intro h
    apply hc
    rw [show c = x from congrArg Subtype.val h]
    exact Subgroup.mem_zpowers x
  have hCX2 : C ≠ X ^ 2 := by
    intro h
    apply hc
    rw [show c = x ^ 2 from congrArg Subtype.val h]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2
  have hsub : ({1, X, X ^ 2, C} : Finset S) ⊆ Finset.univ.filter (fun a : S => a ^ 3 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl | rfl
    · exact one_pow 3
    · exact hX3
    · rw [← pow_mul, mul_comm, pow_mul, hX3, one_pow]
    · exact hC3
  have hcard : ({1, X, X ^ 2, C} : Finset S).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact fun h => hCX2 h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hXX, hCX.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hX1 h.symm, fun h => hX2 h.symm, fun h => hC0 h.symm⟩
  have h := IsCyclic.card_pow_eq_one_le (α := S) (n := 3) (by norm_num)
  have := Finset.card_le_card hsub
  omega

theorem pow_three_eq_one_of_scalar_mem_unitarySU (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {w : Kˣ}
    (hw : (GeneralLinearGroup.scalar (Fin 6) w : GL (Fin 6) K) ∈ unitarySU 2 n K 6) :
    w ^ 3 = 1 := by
  obtain ⟨h1, h2⟩ := (mem_unitarySU_iff hKd).mp hw
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal] at h2
  have h3 := congrFun (congrFun h2 0) 0
  simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h3
  have h4 : (w : K) ^ (2 ^ n + 1) = 1 := by
    rw [pow_succ, ← hKd.bar_apply]
    exact h3
  have hodd : ¬ 2 ∣ 2 ^ n + 1 := by
    intro h
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by have := hKd.one_le; omega)
    have h5 := (Nat.dvd_add_right h2).mp h
    omega
  have hgcd : Nat.gcd 6 (2 ^ n + 1) = 3 := by
    obtain ⟨m, hm⟩ := hpq
    have hm2 : ¬ 2 ∣ m := fun h => hodd (by rw [hm]; exact Dvd.dvd.mul_left h 3)
    have hcop : Nat.gcd 2 m = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm2
    rw [hm, show (6 : ℕ) = 3 * 2 from rfl, Nat.gcd_mul_left, hcop]
  have h5 : (w : K) ^ Nat.gcd 6 (2 ^ n + 1) = 1 := pow_gcd_eq_one.mpr ⟨h1, h4⟩
  rw [hgcd] at h5
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, h5, Units.val_one])

section Action

variable {G : Type} [Group G]

@[expose] def ActsAs (φ : ↥(unitarySU 2 n K 6) →* G) (b : G) (M : GL (Fin 6) K) : Prop :=
  ∃ hM : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)),
    ∀ s, b * φ s * b⁻¹ = φ (conjN M hM s)

theorem commute_of_actsAs_inner {φ : ↥(unitarySU 2 n K 6) →* G} {b : G} {t : Kˣ}
    {s₀ : ↥(unitarySU 2 n K 6)}
    (h : ActsAs φ b (GeneralLinearGroup.scalar (Fin 6) t * (s₀ : GL (Fin 6) K))) (s : _) :
    (φ s₀)⁻¹ * b * φ s = φ s * ((φ s₀)⁻¹ * b) := by
  obtain ⟨hM, hact⟩ := h
  have hcomm : ∀ g : GL (Fin 6) K, GeneralLinearGroup.scalar (Fin 6) t * g =
      g * GeneralLinearGroup.scalar (Fin 6) t := fun g => ((commute_scalar t g).eq).symm
  have e : conjN _ hM s = s₀ * s * s₀⁻¹ := by
    apply Subtype.ext
    rw [coe_conjN]
    calc (GeneralLinearGroup.scalar (Fin 6) t * (s₀ : GL (Fin 6) K)) * (s : GL (Fin 6) K) *
          (GeneralLinearGroup.scalar (Fin 6) t * (s₀ : GL (Fin 6) K))⁻¹
        = GeneralLinearGroup.scalar (Fin 6) t *
            ((s₀ : GL (Fin 6) K) * (s : GL (Fin 6) K) * (s₀ : GL (Fin 6) K)⁻¹) *
            (GeneralLinearGroup.scalar (Fin 6) t)⁻¹ := by group
      _ = ((s₀ : GL (Fin 6) K) * (s : GL (Fin 6) K) * (s₀ : GL (Fin 6) K)⁻¹) *
            GeneralLinearGroup.scalar (Fin 6) t * (GeneralLinearGroup.scalar (Fin 6) t)⁻¹ := by
          rw [hcomm]
      _ = ((s₀ * s * s₀⁻¹ : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) := by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
          group
  have h1 := hact s
  rw [e, map_mul, map_mul, map_inv] at h1
  calc (φ s₀)⁻¹ * b * φ s = (φ s₀)⁻¹ * (b * φ s * b⁻¹) * b := by group
    _ = (φ s₀)⁻¹ * (φ s₀ * φ s * (φ s₀)⁻¹) * b := by rw [h1]
    _ = φ s * ((φ s₀)⁻¹ * b) := by group

theorem isElemAbelian_zpowers {g : G} (hg : g ^ 3 = 1) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers g) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    show (a : G) * b = b * a
    rw [← hi, ← hj, ← _root_.zpow_add, ← _root_.zpow_add, add_comm]
  · intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hg,
      _root_.one_zpow]

theorem false_of_injective_cover [Finite K] [Finite G] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) (φ : ↥(unitarySU 2 n K 6) →* G) (hφ : Function.Injective φ)
    {B : Subgroup G} (hB : CFSG.Open.IsElemAbelian 3 B) (hrank : LargeEvenTwoLocalRank 3 G ≤ 4)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer ((φ.range : Subgroup G) : Set G) →
      IsPGroup 3 S → IsCyclic S)
    {x : G} (hxB : x ∈ B) (hx1 : x ≠ 1) (hxC : ∀ s, x * φ s = φ s * x)
    {a b₀ : G} (haB : a ∈ B) (hbB : b₀ ∈ B) {Ma Mb : GL (Fin 6) K}
    (ha : ActsAs φ a Ma) (hb : ActsAs φ b₀ Mb)
    (hbin : ∃ (t : Kˣ) (s₀ : ↥(unitarySU 2 n K 6)),
      Mb = GeneralLinearGroup.scalar (Fin 6) t * (s₀ : GL (Fin 6) K))
    (hne : Ma * Mb ≠ Mb * Ma) : False := by
  classical
  obtain ⟨t, s₀, hMb⟩ := hbin
  subst hMb
  have hcC0 := commute_of_actsAs_inner hb
  set l : G := φ s₀ with hl
  set c : G := l⁻¹ * b₀ with hc
  have hcC : ∀ s, c * φ s = φ s * c := fun s => hcC0 s
  have hb0 : b₀ = l * c := by rw [hc]; group
  have hlc : Commute l c := (hcC s₀).symm
  have hb03 : b₀ ^ 3 = 1 := hB.2 b₀ hbB
  have hlc3 : l ^ 3 * c ^ 3 = 1 := by
    rw [← hlc.mul_pow, ← hb0]
    exact hb03
  have hc3l : c ^ 3 = (l ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right hlc3
  have hcent : ∀ s : ↥(unitarySU 2 n K 6), s₀ ^ 3 * s = s * s₀ ^ 3 := by
    intro s
    apply hφ
    rw [map_mul, map_mul, map_pow, ← hl]
    have h1 : l ^ 3 = (c ^ 3)⁻¹ := by rw [hc3l, inv_inv]
    rw [h1]
    have h2 : Commute (c ^ 3) (φ s) := (Commute.pow_left (hcC s) 3)
    exact h2.inv_left.eq
  have hscal : ((s₀ ^ 3 : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) ∈ LargeEvenScalars (Fin 6) K :=
    TableBUE.mem_scalars_of_commute hKd Nat.prime_three hpq fun g hg => by
      exact congrArg Subtype.val (hcent ⟨g, hg⟩)
  rw [largeEvenScalars_def] at hscal
  obtain ⟨w, hw⟩ := hscal
  have hw3 : w ^ 3 = 1 :=
    pow_three_eq_one_of_scalar_mem_unitarySU hKd hpq (hw ▸ (s₀ ^ 3).2)
  by_cases hw1 : w = 1
  ·
    have hs3 : s₀ ^ 3 = 1 := by
      apply Subtype.ext
      rw [← hw, hw1, map_one]
      rfl
    have hl3 : l ^ 3 = 1 := by rw [hl, ← map_pow, hs3, map_one]
    have hc3 : c ^ 3 = 1 := by rw [hc3l, hl3]; group
    have hxc : Commute x c := by
      have h1 : Commute x l := hxC s₀
      have h2 : Commute x b₀ := (CFSG.StandardType.TableB.IsElemAbelian.comm hB hxB hbB)
      rw [hc]
      exact h1.inv_right.mul_right h2
    have hxcen : x ∈ Subgroup.centralizer ((φ.range : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨s, rfl⟩
      exact (hxC s).symm
    have hccen : c ∈ Subgroup.centralizer ((φ.range : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨s, rfl⟩
      exact (hcC s).symm
    set S : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers c with hS
    have hx3 : x ^ 3 = 1 := hB.2 x hxB
    have hSab : CFSG.Open.IsElemAbelian 3 S :=
      CFSG.StandardType.TableB.isElemAbelian_sup (isElemAbelian_zpowers hx3)
        (isElemAbelian_zpowers hc3) (fun a ha b hb => by
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
          exact ((hxc.zpow_left i).zpow_right j).eq)
    have hSp : IsPGroup 3 S := fun g => ⟨1, Subtype.ext (by simpa using hSab.2 g g.2)⟩
    have hSle : S ≤ Subgroup.centralizer ((φ.range : Subgroup G) : Set G) :=
      sup_le ((Subgroup.zpowers_le).mpr hxcen) ((Subgroup.zpowers_le).mpr hccen)
    have hSc : IsCyclic S := hcyc S hSle hSp
    have hcx : c ∈ Subgroup.zpowers x :=
      mem_zpowers_of_isCyclic_of_pow_three hSc (le_sup_left (a := Subgroup.zpowers x)
        (b := Subgroup.zpowers c) (Subgroup.mem_zpowers x)) (le_sup_right
        (a := Subgroup.zpowers x) (b := Subgroup.zpowers c) (Subgroup.mem_zpowers c)) hx3 hx1 hc3
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hcx
    have hax : Commute a x := CFSG.StandardType.TableB.IsElemAbelian.comm hB haB hxB
    have hac : Commute a c := by rw [← hj]; exact hax.zpow_right j
    have hab : Commute a b₀ := CFSG.StandardType.TableB.IsElemAbelian.comm hB haB hbB
    have hal : Commute a l := by
      have : l = b₀ * c⁻¹ := by rw [hb0]; group
      rw [this]
      exact hab.mul_right hac.inv_right
    obtain ⟨hMa, hactA⟩ := ha
    have h1 := hactA s₀
    rw [← hl, hal.eq, mul_inv_cancel_right] at h1
    have h2 : conjN Ma hMa s₀ = s₀ := hφ h1.symm
    have h3 := congrArg Subtype.val h2
    rw [coe_conjN] at h3
    apply hne
    have h4 : Ma * (s₀ : GL (Fin 6) K) = (s₀ : GL (Fin 6) K) * Ma := by
      calc Ma * (s₀ : GL (Fin 6) K) = Ma * (s₀ : GL (Fin 6) K) * Ma⁻¹ * Ma := by group
        _ = (s₀ : GL (Fin 6) K) * Ma := by rw [h3]
    calc Ma * (GeneralLinearGroup.scalar (Fin 6) t * (s₀ : GL (Fin 6) K))
        = GeneralLinearGroup.scalar (Fin 6) t * (Ma * (s₀ : GL (Fin 6) K)) := by
          rw [← mul_assoc, ← mul_assoc, ((commute_scalar t Ma).eq)]
      _ = GeneralLinearGroup.scalar (Fin 6) t * ((s₀ : GL (Fin 6) K) * Ma) := by rw [h4]
      _ = (GeneralLinearGroup.scalar (Fin 6) t * (s₀ : GL (Fin 6) K)) * Ma := by
          rw [mul_assoc]
  ·
    have hs₀3 : s₀ ^ 3 = scalarSU hKd hpq hw3 := by
      apply Subtype.ext
      show ((s₀ ^ 3 : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) = diagHom 6 (fun _ => w)
      rw [← hw, diagHom_const_eq_scalar]
    by_cases h9 : 9 ∣ 2 ^ n + 1
    · have hz3 : w⁻¹ ^ 3 = 1 := by rw [inv_pow, hw3, inv_one]
      have hc3' : c ^ 3 = φ (scalarSU hKd hpq hz3) := by
        have h1 : scalarSU hKd hpq hz3 = (s₀ ^ 3)⁻¹ := by
          apply Subtype.ext
          show (diagHom 6 (fun _ => w⁻¹) : GL (Fin 6) K) = ((s₀ ^ 3 : ↥(unitarySU 2 n K 6)) :
            GL (Fin 6) K)⁻¹
          rw [← hw, ← map_inv, ← diagHom_const_eq_scalar]
        rw [h1, map_inv, map_pow, ← hl, hc3l]
      have := five_le_twoLocalRank_of_nine hKd h9 φ hφ hz3 (inv_ne_one.mpr hw1) c hcC hc3'
      omega
    · exact false_of_pow_three_eq_scalar hKd hpq h9 hw3 hw1 s₀ hs₀3

end Action

end CFSG.StandardType.Line63.H5

end

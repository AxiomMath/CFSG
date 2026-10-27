module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCore
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJInner
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCoreA5J2
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJFactor

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Equiv

namespace Wales1411W.HJProd

section Same

variable {A : Type*} [Group A]

theorem snd_eq_one_of_commute_right (hA : Function.Injective (MulAut.conj : A →* MulAut A))
    {x : A × A} (hx : ∀ a : A, ((1, a) : A × A) * x = x * (1, a)) : x.2 = 1 := by
  apply hA
  rw [map_one]
  ext a
  have h := congrArg Prod.snd (hx a)
  simp only [Prod.snd_mul] at h
  simp only [MulAut.conj_apply, MulAut.one_apply]
  rw [← h, mul_inv_cancel_right]

theorem card_ker_fst [Finite A] : Nat.card (MonoidHom.fst A A).ker = Nat.card A := by
  have h := Subgroup.card_ker_mul_card_range (MonoidHom.fst A A)
  rw [(MonoidHom.fst A A).range_eq_top_of_surjective (fun a => ⟨(a, 1), rfl⟩),
    Subgroup.card_top, Nat.card_prod] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

variable [Finite A] [IsSimpleGroup A]

theorem map_ker_snd_eq (hA : Function.Injective (MulAut.conj : A →* MulAut A))
    (β : MulAut (A × A)) :
    (MonoidHom.snd A A).ker.map β.toMonoidHom = (MonoidHom.snd A A).ker ∨
      (MonoidHom.snd A A).ker.map β.toMonoidHom = (MonoidHom.fst A A).ker := by
  set N := (MonoidHom.snd A A).ker.map β.toMonoidHom with hN
  haveI hNn : N.Normal := (MonoidHom.normal_ker _).map _ β.surjective
  have hcardN : Nat.card N = Nat.card A := by
    rw [hN, Subgroup.card_map_of_injective β.injective, card_ker_snd]
  have h1 : N ⊓ (MonoidHom.snd A A).ker = ⊥ ∨ (MonoidHom.snd A A).ker ≤ N := by
    set P := (N ⊓ (MonoidHom.snd A A).ker).map (MonoidHom.fst A A) with hP
    haveI : (N ⊓ (MonoidHom.snd A A).ker).Normal := inferInstance
    haveI hPn : P.Normal := Subgroup.Normal.map inferInstance _ fun a => ⟨(a, 1), rfl⟩
    rcases Subgroup.Normal.eq_bot_or_eq_top P with h | h
    · left
      rw [eq_bot_iff]
      intro k hk
      have hk1 : k.1 ∈ P := ⟨k, hk, rfl⟩
      rw [h, Subgroup.mem_bot] at hk1
      have hk2 : k.2 = 1 := (Subgroup.mem_inf.mp hk).2
      rw [Subgroup.mem_bot]
      exact Prod.ext hk1 hk2
    · right
      intro x hx
      have hx1 : x.1 ∈ P := h ▸ Subgroup.mem_top _
      obtain ⟨k, hk, hkx⟩ := hx1
      have hk2 : k.2 = 1 := (Subgroup.mem_inf.mp hk).2
      have : k = x := Prod.ext hkx (hk2.trans (MonoidHom.mem_ker.mp hx).symm)
      exact this ▸ (Subgroup.mem_inf.mp hk).1
  have h2 : N ⊓ (MonoidHom.fst A A).ker = ⊥ ∨ (MonoidHom.fst A A).ker ≤ N := by
    set P := (N ⊓ (MonoidHom.fst A A).ker).map (MonoidHom.snd A A) with hP
    haveI : (N ⊓ (MonoidHom.fst A A).ker).Normal := inferInstance
    haveI hPn : P.Normal := Subgroup.Normal.map inferInstance _ fun a => ⟨(1, a), rfl⟩
    rcases Subgroup.Normal.eq_bot_or_eq_top P with h | h
    · left
      rw [eq_bot_iff]
      intro k hk
      have hk2 : k.2 ∈ P := ⟨k, hk, rfl⟩
      rw [h, Subgroup.mem_bot] at hk2
      have hk1 : k.1 = 1 := (Subgroup.mem_inf.mp hk).2
      rw [Subgroup.mem_bot]
      exact Prod.ext hk1 hk2
    · right
      intro x hx
      have hx2 : x.2 ∈ P := h ▸ Subgroup.mem_top _
      obtain ⟨k, hk, hkx⟩ := hx2
      have hk1 : k.1 = 1 := (Subgroup.mem_inf.mp hk).2
      have : k = x := Prod.ext (hk1.trans (MonoidHom.mem_ker.mp hx).symm) hkx
      exact this ▸ (Subgroup.mem_inf.mp hk).1
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exfalso
      have hcomm : ⁅N, (MonoidHom.snd A A).ker⁆ = ⊥ :=
        le_bot_iff.mp (h1 ▸ Subgroup.commutator_le_inf N (MonoidHom.snd A A).ker)
      have hNC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      have hNf : N ≤ (MonoidHom.fst A A).ker := fun n hn =>
        MonoidHom.mem_ker.mpr (fst_eq_one_of_commute hA fun a =>
          (Subgroup.mem_centralizer_iff.mp (hNC hn) (a, 1) rfl))
      have hNb : N = ⊥ := by
        rw [← h2]
        exact (inf_eq_left.mpr hNf).symm
      rw [hNb, Subgroup.card_bot] at hcardN
      have : Nontrivial A := IsSimpleGroup.toNontrivial
      have h1lt := Finite.one_lt_card (α := A)
      omega
    · right
      exact (Subgroup.eq_of_le_of_card_ge h2 (by rw [hcardN, card_ker_fst])).symm
  · left
    exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [hcardN, card_ker_snd])).symm

theorem snd_eq_one_of_pow_three (hA : Function.Injective (MulAut.conj : A →* MulAut A))
    (β : MulAut (A × A)) (hβ : β ^ 3 = 1) {x : A × A} (hx : x.2 = 1) : (β x).2 = 1 := by
  rcases map_ker_snd_eq hA β with h | h
  · have hm : β x ∈ (MonoidHom.snd A A).ker.map β.toMonoidHom := ⟨x, hx, rfl⟩
    rw [h] at hm
    exact hm
  · exfalso
    have hsf : ∀ y : A × A, y.2 = 1 → (β y).1 = 1 := fun y hy => by
      have hm : β y ∈ (MonoidHom.snd A A).ker.map β.toMonoidHom := ⟨y, hy, rfl⟩
      rw [h] at hm
      exact hm
    have hfs : ∀ y : A × A, y.1 = 1 → (β y).2 = 1 := by
      intro y hy
      apply snd_eq_one_of_commute_right hA
      intro a
      have h1a : ((1, a) : A × A) ∈ (MonoidHom.snd A A).ker.map β.toMonoidHom := by
        rw [h]
        rfl
      obtain ⟨z, hz, hza⟩ := h1a
      have hz2 : z.2 = 1 := MonoidHom.mem_ker.mp hz
      have hzy : z * y = y * z := Prod.ext (by simp [hy]) (by simp [hz2])
      change β z = (1, a) at hza
      rw [← hza, ← map_mul, ← map_mul, hzy]
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    have hx1 := hsf (a, 1) rfl
    have hx2 := hfs _ hx1
    have hx3 := hsf _ hx2
    have h3 : (β ^ 3) (a, 1) = β (β (β (a, 1))) := by
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
    rw [hβ, MulAut.one_apply] at h3
    rw [← h3] at hx3
    exact ha hx3

end Same

end Wales1411W.HJProd

open Wales1411W Wales1411W.HJProd Wales1411W.HJFactor in
theorem ks1411HJCoreA5A5 : KS1411HJCoreA5A5 := by
  intro M _ _ Ybar Abar Xbar Rbar abar hset hX S T hS hT hST hsupp
  exfalso
  obtain ⟨φ⟩ := hX
  haveI := HJInner.normal_X hset
  have hA5 := a5_facts
  set ι : alternatingGroup (Fin 5) →* M :=
    Xbar.subtype.comp (φ.symm.toMonoidHom.comp (MonoidHom.inl _ _)) with hι
  have hιinj : Function.Injective ι := by
    intro a b h
    have h1 := φ.symm.injective (Subtype.ext h)
    exact congrArg Prod.fst h1
  have hιapp : ∀ a, ι a = ((φ.symm (a, 1) : ↥Xbar) : M) := fun a => rfl
  set X1 : Subgroup M := ι.range with hX1
  have hX1iso : Nonempty (↥X1 ≃* alternatingGroup (Fin 5)) := ⟨(MonoidHom.ofInjective hιinj).symm⟩
  have hX1Y : X1 ≤ Ybar := by
    rintro _ ⟨a, rfl⟩
    exact hset.le_Y (φ.symm (a, 1)).2
  have hnorm : ∀ m : M, (∀ x : alternatingGroup (Fin 5) × alternatingGroup (Fin 5), x.2 = 1 →
      (MulAut.congr φ (MulAut.conjNormal (H := Xbar) m) x).2 = 1) →
      m ∈ Subgroup.normalizer (X1 : Set M) := by
    intro m hm
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨a, rfl⟩ := hn
    set y := MulAut.congr φ (MulAut.conjNormal (H := Xbar) m) (a, 1) with hy
    have hy2 : y.2 = 1 := hm (a, 1) rfl
    have hy' : (MulAut.conjNormal (H := Xbar) m) (φ.symm (a, 1)) = φ.symm y := by
      rw [hy]
      simp [MulAut.congr_apply]
    refine ⟨y.1, ?_⟩
    rw [hιapp]
    have hyy : y = (y.1, 1) := Prod.ext rfl hy2
    rw [← hyy, ← hy', MulAut.conjNormal_apply, hιapp]
  have hA3 : ∀ g ∈ Abar, g ^ 3 = 1 := hset.isElemAbelian.2
  have hAN : Abar ≤ Subgroup.normalizer (X1 : Set M) := by
    intro ε hε
    refine hnorm ε fun x hx => snd_eq_one_of_pow_three hA5.1 _ ?_ hx
    rw [← map_pow, ← map_pow, hA3 ε hε, map_one, map_one]
  obtain ⟨⟨e, heA, heV, hea⟩, ⟨c, hcA, hcV, hco⟩⟩ := a5_factor hset hX1Y hX1iso hAN
  obtain ⟨a0, rfl⟩ := hcV
  have ha0 : a0 ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hco
    norm_num at hco
  have hRN : Rbar ≤ Subgroup.normalizer (X1 : Set M) := by
    intro r hr
    apply hnorm
    set β := MulAut.congr φ (MulAut.conjNormal (H := Xbar) r) with hβ
    rcases map_ker_snd_eq hA5.1 β with h | h
    · intro x hx
      have hm : β x ∈ (MonoidHom.snd _ _).ker.map β.toMonoidHom := ⟨x, hx, rfl⟩
      rw [h] at hm
      exact hm
    · exfalso
      have hrc : ι a0 * r = r * ι a0 :=
        Subgroup.mem_centralizer_iff.mp (hset.le_centralizer_R hr) _ hcA
      have hfix : (MulAut.conjNormal (H := Xbar) r) (φ.symm (a0, 1)) = φ.symm (a0, 1) := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply, ← hιapp]
        calc r * ι a0 * r⁻¹ = ι a0 * r * r⁻¹ := by rw [hrc]
          _ = ι a0 := by group
      have hfix' : β (a0, 1) = (a0, 1) := by
        simp [hβ, MulAut.congr_apply, hfix]
      have hm : ((a0, 1) : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∈
          (MonoidHom.snd _ _).ker.map β.toMonoidHom := ⟨(a0, 1), rfl, hfix'⟩
      rw [h] at hm
      exact ha0 hm
  have hXN : Xbar ≤ Subgroup.normalizer (X1 : Set M) := by
    intro x hx
    apply hnorm
    intro y hy
    have hc : MulAut.conjNormal (H := Xbar) x = MulAut.conj (⟨x, hx⟩ : ↥Xbar) := by
      ext z
      simp [MulAut.conjNormal_apply, MulAut.conj_apply]
    rw [hc]
    simp [MulAut.congr_apply, MulAut.conj_apply, hy]
  have hYN : Ybar ≤ Subgroup.normalizer (X1 : Set M) := by
    rw [hset.eq_sup]
    exact sup_le hXN hRN
  have hxc : ¬ X1 ≤ Subgroup.centralizer ({ι a0} : Set M) := by
    intro hle
    apply ha0
    apply hA5.1
    rw [map_one]
    ext b
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hle ⟨b, rfl⟩)
    rw [← map_mul, ← map_mul] at h
    have h' := hιinj h
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h', mul_inv_cancel_right]
  have heY : ¬ Ybar ≤ Subgroup.centralizer ({e} : Set M) := fun h =>
    hea (hset.mem_zpowers e heA h)
  have hc3 : ι a0 ^ 3 = 1 := hA3 _ hcA
  exact false_of_factor hX1Y hYN ⟨a0, rfl⟩ (by rw [hc3]; exact one_mem _) hxc heA (hA3 e heA) heV
    hS.prop hT.prop hST
    (hsupp e heA heY)

end CFSG.RankThree.PartTwo.Sec14

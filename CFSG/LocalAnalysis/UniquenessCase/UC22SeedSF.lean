module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Quasithin.Background.C124Perf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix (SpecialLinearGroup)

section Odd

theorem pow_two_pow_of_odd_kernel {A Q : Type} [Group A] [Finite A] [Group Q] (π : A →* Q)
    (hodd : ¬ 2 ∣ Nat.card π.ker) (hQ : ∀ (y : Q) (a : ℕ), y ^ 2 ^ a = 1 → y ^ 2 = 1)
    (x : A) (a : ℕ) (hx : x ^ 2 ^ a = 1) : x ^ 2 = 1 := by
  have h1 : π (x ^ 2) = 1 := by
    rw [map_pow]
    exact hQ (π x) a (by rw [← map_pow, hx, map_one])
  have hmem : x ^ 2 ∈ π.ker := MonoidHom.mem_ker.mpr h1
  have hd1 : orderOf (x ^ 2) ∣ 2 ^ a :=
    orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow])
  have hd2 : orderOf (x ^ 2) ∣ Nat.card π.ker := by
    have := orderOf_dvd_natCard (⟨x ^ 2, hmem⟩ : π.ker)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (2 ^ a) (Nat.card π.ker) :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  exact orderOf_eq_one_iff.mp ((hcop.coprime_dvd_left hd1).eq_one_of_dvd hd2)

theorem exists_pow_four_eq_one_of_perm {B : Type} [Group B] {L : Subgroup B} {N : ℕ} (hN : 4 ≤ N)
    (e : L ≃* Equiv.Perm (Fin N)) : ∃ x ∈ L, x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨σ, h4, h2⟩ : ∃ σ : Equiv.Perm (Fin N), σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
    have hne : (⟨3, by omega⟩ : Fin N) ≠ 0 := by simp [Fin.ext_iff]
    have hord : orderOf (Fin.cycleRange (⟨3, by omega⟩ : Fin N)) = 4 := by
      rw [← Equiv.Perm.lcm_cycleType, Fin.cycleType_cycleRange hne]
      simp
    exact ⟨Fin.cycleRange ⟨3, by omega⟩, by rw [← hord]; exact pow_orderOf_eq_one _,
      pow_ne_one_of_lt_orderOf (by norm_num) (by omega)⟩
  refine ⟨(e.symm σ : B), (e.symm σ).2, ?_, ?_⟩
  · have : e.symm σ ^ 4 = 1 := by rw [← map_pow, h4, map_one]
    simpa using congrArg Subtype.val this
  · intro h
    have h' : e.symm σ ^ 2 = 1 := Subtype.ext (by simpa using h)
    exact h2 (by simpa using congrArg e h')

end Odd

section SingleFactor

namespace SeedSF

theorem eq_top_of_commuting_family {Q : Type} [Group Q]
    (hQ1 : ∀ (N : Subgroup Q) [N.Normal] (x : Q), x ∈ N → x ≠ 1 → x ^ 2 = 1 → N = ⊤)
    {ι : Type*} (P : ι → Subgroup Q) (hcomm : ∀ i j, i ≠ j → ∀ a ∈ P i, ∀ b ∈ P j, a * b = b * a)
    (hnorm : (⨆ i, P i).Normal) (hinv : ∀ i, ∃ x ∈ P i, x ≠ 1 ∧ x ^ 2 = 1) (i : ι) : P i = ⊤ := by
  haveI := hnorm
  obtain ⟨x, hxP, hx1, hx2⟩ := hinv i
  have htop : (⨆ j, P j) = ⊤ := hQ1 _ x (le_iSup P i hxP) hx1 hx2
  have key : ∀ g ∈ ⨆ j, P j, ∀ n ∈ P i, g * n * g⁻¹ ∈ P i := by
    intro g hg
    refine Subgroup.iSup_induction P (C := fun g => ∀ n ∈ P i, g * n * g⁻¹ ∈ P i) hg ?_ ?_ ?_
    · intro j a ha n hn
      by_cases hji : j = i
      · subst hji
        exact mul_mem (mul_mem ha hn) (inv_mem ha)
      · rw [hcomm j i hji a ha n hn, mul_inv_cancel_right]
        exact hn
    · intro n hn
      simpa using hn
    · intro x y hx hy n hn
      simpa [mul_assoc] using hx _ (hy n hn)
  haveI : (P i).Normal := ⟨fun n hn g => key g (htop ▸ Subgroup.mem_top g) n hn⟩
  exact hQ1 (P i) x hxP hx1 hx2

theorem mem_of_pow_two_pow_mem {G Q : Type*} [Group G] [Group Q] (π : G →* Q) (hodd : ¬ 2 ∣ Nat.card π.ker)
    (JG : Subgroup G) [JG.Normal] (hJ : JG.map π = ⊤) {a : G} {k : ℕ} (ha : a ^ 2 ^ k ∈ JG) : a ∈ JG := by
  obtain ⟨j, hjJ, hj⟩ := Subgroup.mem_map.mp (hJ ▸ Subgroup.mem_top (π a))
  have hκ : j⁻¹ * a ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hj, inv_mul_cancel]
  have hκm : (j⁻¹ * a) ^ Nat.card π.ker = 1 := by
    have h1 := orderOf_dvd_natCard (⟨j⁻¹ * a, hκ⟩ : π.ker)
    rw [Subgroup.orderOf_mk] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hfa : (QuotientGroup.mk' JG) a = (QuotientGroup.mk' JG) (j⁻¹ * a) := by
    have hj1 : (QuotientGroup.mk' JG) j = 1 := (QuotientGroup.eq_one_iff j).mpr hjJ
    calc (QuotientGroup.mk' JG) a = (QuotientGroup.mk' JG) (j * (j⁻¹ * a)) := by rw [mul_inv_cancel_left]
      _ = (QuotientGroup.mk' JG) (j⁻¹ * a) := by rw [map_mul, hj1, one_mul]
  have h1 : (QuotientGroup.mk' JG a) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ha
  have h2 : (QuotientGroup.mk' JG a) ^ Nat.card π.ker = 1 := by
    rw [hfa, ← map_pow, hκm, map_one]
  have hcop : Nat.Coprime (2 ^ k) (Nat.card π.ker) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have hord : orderOf (QuotientGroup.mk' JG a) = 1 :=
    ((hcop.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1)).eq_one_of_dvd (orderOf_dvd_of_pow_eq_one h2))
  exact (QuotientGroup.eq_one_iff a).mp (orderOf_eq_one_iff.mp hord)

end SeedSF

theorem single_factor {B : Type} [Group B] {A : Subgroup B} [Finite ↥A] {Q : Type} [Group Q]
    (π : ↥A →* Q) (hπ : Function.Surjective π) (hodd : ¬ 2 ∣ Nat.card π.ker)
    (hQ1 : ∀ (N : Subgroup Q) [N.Normal] (x : Q), x ∈ N → x ≠ 1 → x ^ 2 = 1 → N = ⊤)
    (hQnc : ∃ a b : Q, a * b ≠ b * a)
    (J : Subgroup B) (hJA : J ≤ A) (hJn : (J.subgroupOf A).Normal)
    (hAJ : ∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k ∈ J)
    (I : Finset (Subgroup B)) (hne : I.Nonempty) (hIA : ∀ L ∈ I, L ≤ A) (hJ : J = ⨆ L ∈ I, L)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hinv : ∀ L ∈ I, ∃ x ∈ L, x ≠ 1 ∧ x ^ 2 = 1) :
    ∃ L : Subgroup B, I = {L} ∧ J = L ∧ J = A := by
  obtain ⟨P, hP⟩ : ∃ P : ↥I → Subgroup Q, ∀ L, P L = (L.1.subgroupOf A).map π := ⟨_, fun _ => rfl⟩
  have hmemP : ∀ (L : ↥I) (y : ↥A), (y : B) ∈ L.1 → π y ∈ P L := fun L y hy => by
    rw [hP]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hy)
  have hJA' : J.subgroupOf A = ⨆ L ∈ I, L.subgroupOf A := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hJA, hJ, Subgroup.map_iSup]
    refine iSup_congr fun L => ?_
    rw [Subgroup.map_iSup]
    exact iSup_congr fun hL => (Subgroup.map_subgroupOf_eq_of_le (hIA L hL)).symm
  have hPJ : (⨆ L : ↥I, P L) = (J.subgroupOf A).map π := by
    rw [hJA', Subgroup.map_iSup]
    simp only [Subgroup.map_iSup]
    rw [iSup_subtype']
    exact iSup_congr fun L => hP L
  have hcommP : ∀ i j : ↥I, i ≠ j → ∀ a ∈ P i, ∀ b ∈ P j, a * b = b * a := by
    intro i j hij a ha b hb
    rw [hP] at ha hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a'
      (Subgroup.mem_subgroupOf.mp ha') b' (Subgroup.mem_subgroupOf.mp hb'))
  have hinvP : ∀ i : ↥I, ∃ x ∈ P i, x ≠ 1 ∧ x ^ 2 = 1 := by
    intro i
    obtain ⟨y, hyL, hy1, hy2⟩ := hinv i.1 i.2
    have hyA : y ∈ A := hIA i.1 i.2 hyL
    have hy2' : (⟨y, hyA⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using hy2)
    refine ⟨π ⟨y, hyA⟩, hmemP i ⟨y, hyA⟩ hyL, fun h1 => hodd ?_, by rw [← map_pow, hy2', map_one]⟩
    have hker : (⟨y, hyA⟩ : ↥A) ∈ π.ker := h1
    have hord : orderOf (⟨y, hyA⟩ : ↥A) = 2 :=
      orderOf_eq_prime hy2' (fun h => hy1 (congrArg Subtype.val h))
    have := orderOf_dvd_natCard (⟨⟨y, hyA⟩, hker⟩ : π.ker)
    rwa [Subgroup.orderOf_mk, hord] at this
  have hnormP : (⨆ L : ↥I, P L).Normal := by
    rw [hPJ]
    exact Subgroup.Normal.map hJn π hπ
  have htop : ∀ i : ↥I, P i = ⊤ := SeedSF.eq_top_of_commuting_family hQ1 P hcommP hnormP hinvP
  have hsub : ∀ i j : ↥I, i = j := by
    intro i j
    by_contra hij
    obtain ⟨a, b, hab⟩ := hQnc
    refine hab (hcommP i j hij a ?_ b ?_)
    · rw [htop i]; exact Subgroup.mem_top a
    · rw [htop j]; exact Subgroup.mem_top b
  obtain ⟨L, hL⟩ := hne
  have hIL : I = {L} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hL, fun L' hL' => congrArg Subtype.val (hsub ⟨L', hL'⟩ ⟨L, hL⟩)⟩
  have hJL : J = L := by
    rw [hJ, hIL]
    simp
  have hPJtop : (J.subgroupOf A).map π = ⊤ := by
    rw [← hPJ]
    exact eq_top_iff.mpr (by rw [← htop ⟨L, hL⟩]; exact le_iSup P ⟨L, hL⟩)
  haveI := hJn
  have hJA2 : J = A := by
    refine le_antisymm hJA fun a ha => ?_
    obtain ⟨k, hk⟩ := hAJ a ha
    have h1 : (⟨a, ha⟩ : ↥A) ^ 2 ^ k ∈ J.subgroupOf A := by
      rw [Subgroup.mem_subgroupOf]
      simpa using hk
    exact Subgroup.mem_subgroupOf.mp (SeedSF.mem_of_pow_two_pow_mem π hodd (J.subgroupOf A) hPJtop h1)
  exact ⟨L, hIL, hJL, hJA2⟩

end SingleFactor

section Coprime

open CFSG.Quasithin

namespace SeedSF

theorem le_of_orderOf_three_two {G : Type*} [Group G] {A S : Subgroup G} (hA : Nat.card A = 6) {c t : G}
    (hcA : c ∈ A) (htA : t ∈ A) (hc : orderOf c = 3) (ht : orderOf t = 2) (hcS : c ∈ S) (htS : t ∈ S) :
    A ≤ S := by
  haveI : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have hcH : (⟨c, hcA⟩ : A) ∈ S.subgroupOf A := hcS
  have htH : (⟨t, htA⟩ : A) ∈ S.subgroupOf A := htS
  have h3 : 3 ∣ Nat.card (S.subgroupOf A) := by
    have := orderOf_dvd_natCard (⟨⟨c, hcA⟩, hcH⟩ : S.subgroupOf A)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hc] at this
  have h2 : 2 ∣ Nat.card (S.subgroupOf A) := by
    have := orderOf_dvd_natCard (⟨⟨t, htA⟩, htH⟩ : S.subgroupOf A)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, ht] at this
  have hle : Nat.card (S.subgroupOf A) ≤ 6 :=
    hA ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card _)
  have hpos : 0 < Nat.card (S.subgroupOf A) := Nat.card_pos
  have htop : S.subgroupOf A = ⊤ := (Subgroup.card_eq_iff_eq_top _).mp (by omega)
  intro x hx
  have : (⟨x, hx⟩ : A) ∈ S.subgroupOf A := htop ▸ Subgroup.mem_top _
  exact this

theorem mem_of_orderOf_three_of_pow_two_pow_mem {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (hx : orderOf x = 3) {k : ℕ} (hk : x ^ 2 ^ k ∈ H) : x ∈ H := by
  have hmod : (2 ^ k * 2 ^ k) % 3 = 1 := by
    rw [← mul_pow, Nat.pow_mod]
    norm_num
  have h2 := pow_mod_orderOf x (2 ^ k * 2 ^ k)
  rw [hx, hmod, pow_one] at h2
  rw [h2.trans (pow_mul x _ _)]
  exact H.pow_mem hk _

theorem exists_s3_gens {F : Type} [Field F] [CharP F 2] :
    ∃ c t : SpecialLinearGroup (Fin 2) F,
      c * c * c = 1 ∧ c ≠ 1 ∧ t * t = 1 ∧ t ≠ 1 ∧ t * c = c * c * t := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have h11 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
  have hdet1 : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : F) * h2
  have hdet2 : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : F) * h2
  obtain ⟨c, hc⟩ : ∃ c : SpecialLinearGroup (Fin 2) F,
      (c : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 1] := ⟨⟨_, hdet1⟩, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : SpecialLinearGroup (Fin 2) F,
      (t : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := ⟨⟨_, hdet2⟩, rfl⟩
  refine ⟨c, t, ?_, ?_, ?_, ?_, ?_⟩
  · refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.mul_apply, Fin.sum_univ_two, h11]
  · intro h
    have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [hc] at this
  · refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, ht, Matrix.mul_apply, Fin.sum_univ_two, h11]
  · intro h
    have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [ht] at this
  · refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, hc, ht, Matrix.mul_apply, Fin.sum_univ_two, h11]

section Norm

variable {W : Type} [CommGroup W]

@[expose] def normMap (c : MulAut W) : W →* W :=
  MonoidHom.id W * c.toMonoidHom * c.toMonoidHom.comp c.toMonoidHom

theorem normMap_apply (c : MulAut W) (w : W) : normMap c w = w * c w * c (c w) := rfl

theorem apply_cube {c : MulAut W} (hc : c * c * c = 1) (w : W) : c (c (c w)) = w := by
  simpa using congrArg (fun f : MulAut W => f w) hc

theorem normMap_apply_mul_inv {c : MulAut W} (hc : c * c * c = 1) (w : W) : normMap c (c w * w⁻¹) = 1 := by
  have h : normMap c (c w) = normMap c w := by
    rw [normMap_apply, normMap_apply, apply_cube hc]
    ac_rfl
  rw [map_mul, map_inv, h, mul_inv_cancel]

theorem apply_normMap_of_mul_eq {c t : MulAut W} (hc : c * c * c = 1) (hct : t * c = c * c * t) (w : W) :
    t (normMap c w) = normMap c (t w) := by
  have h1 : t (c w) = c (c (t w)) := by simpa using congrArg (fun f : MulAut W => f w) hct
  have h2 : t (c (c w)) = c (t w) := by
    have h : t * c * c = c * t := by
      calc t * c * c = c * c * t * c := by rw [hct]
        _ = c * c * (t * c) := by rw [mul_assoc]
        _ = c * c * (c * c * t) := by rw [hct]
        _ = (c * c * c) * (c * t) := by simp only [mul_assoc]
        _ = c * t := by rw [hc, one_mul]
    simpa using congrArg (fun f : MulAut W => f w) h
  rw [normMap_apply, normMap_apply, map_mul, map_mul, h1, h2]
  ac_rfl

theorem mem_fixV_of_mem_commV (hW : ∀ w : W, w ^ 2 = 1) {c t : MulAut W} {A : Subgroup (MulAut W)}
    (hc : c * c * c = 1) (ht : t * t = 1) (hct : t * c = c * c * t)
    (hgen : ∀ S : Subgroup (MulAut W), c ∈ S → t ∈ S → A ≤ S) {y : W} (hy : y ∈ commV A) (hcy : c y = y) :
    y ∈ fixV A := by
  have hinv : ∀ z : W, z⁻¹ = z := fun z => inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hW z)
  let X : Subgroup W := MonoidHom.eqLocus (t.toMonoidHom.comp (normMap c)) (normMap c)
  have hX : ∀ v : W, v ∈ X ↔ t (normMap c v) = normMap c v := fun v => Iff.rfl
  let S : Subgroup (MulAut W) :=
    { carrier := {x | ∀ u : W, x u * u⁻¹ ∈ X}
      one_mem' := fun u => by simp
      mul_mem' := fun {a b} ha hb u => by
        have h := X.mul_mem (ha (b u)) (hb u)
        simpa [mul_assoc] using h
      inv_mem' := fun {a} ha u => by
        have h := X.inv_mem (ha (a⁻¹ u))
        rw [MulAut.apply_inv_self] at h
        simpa [mul_comm] using h }
  have hcS : c ∈ S := fun u => by
    rw [hX, normMap_apply_mul_inv hc, map_one]
  have htS : t ∈ S := fun u => by
    have htt : t (t u) = u := by simpa using congrArg (fun f : MulAut W => f u) ht
    have htv : t (t u * u⁻¹) = (t u * u⁻¹)⁻¹ := by
      rw [map_mul, map_inv, htt]
      simp [mul_comm]
    show t u * u⁻¹ ∈ X
    rw [hX, apply_normMap_of_mul_eq hc hct, htv, map_inv, hinv]
  have hAS : A ≤ S := hgen S hcS htS
  have hyX : y ∈ X := by
    refine (Subgroup.closure_le X).mpr ?_ hy
    rintro _ ⟨x, hx, v, rfl⟩
    exact hAS hx v
  have hty : t y = y := by
    have h1 : normMap c y = y := by
      have h2 := hW y
      rw [pow_two] at h2
      rw [normMap_apply, hcy, hcy, h2, one_mul]
    have h3 := (hX y).mp hyX
    rwa [h1] at h3
  have hst : A ≤ MulAction.stabilizer (MulAut W) y :=
    hgen _ (MulAction.mem_stabilizer_iff.mpr (by rw [MulAut.smul_def]; exact hcy))
      (MulAction.mem_stabilizer_iff.mpr (by rw [MulAut.smul_def]; exact hty))
  intro x hx
  have := MulAction.mem_stabilizer_iff.mp (hst hx)
  rwa [MulAut.smul_def] at this

end Norm

end SeedSF

theorem commV_inf_fixV_twoResidual_le {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup (MulAut W)} {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : ↥A ≃* SpecialLinearGroup (Fin 2) F) :
    commV A ⊓ fixV (twoResidual A) ≤ fixV A := by
  classical
  haveI : Finite A := e.toEquiv.finite_iff.mpr inferInstance
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  by_cases h4 : 4 ≤ Nat.card F
  ·
    haveI := Fintype.ofFinite F
    have h4' : 4 ≤ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
    obtain ⟨a, ha0, ha1⟩ : ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
      have hlt : ({0, 1} : Finset F).card < (Finset.univ : Finset F).card :=
        lt_of_le_of_lt Finset.card_le_two (by rw [Finset.card_univ]; omega)
      obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      exact ⟨a, ha.1, ha.2⟩
    have hsq : a ^ 2 ≠ 1 := fun h => ha1 (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp
      (by linear_combination h + (1 - a) * h2 : (a - 1) ^ 2 = 0)))
    haveI : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) := ⟨Matrix.SL2.commutator_eq_top ha0 hsq⟩
    haveI : Group.IsPerfect ↥A := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hAA : ⁅A, A⁆ = A := by
      have h1 : (commutator ↥A).map A.subtype = ⁅A, A⁆ := by
        rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      rw [← h1, Group.IsPerfect.commutator_eq_top, Subgroup.map_top, Subgroup.range_subtype]
    have hAres : A ≤ twoResidual A := (C124.twoResidual_eq_self_of_perfect' hAA).ge
    exact inf_le_right.trans fun y hy x hx => hy x (hAres hx)
  ·
    have hF2 : Nat.card F = 2 := by
      haveI := Fintype.ofFinite F
      obtain ⟨n, -, hn⟩ := FiniteField.card F 2
      rw [Nat.card_eq_fintype_card, hn] at h4 ⊢
      have hn1 : 1 ≤ (n : ℕ) := n.pos
      rcases Nat.lt_or_ge (n : ℕ) 2 with h | h
      · rw [show (n : ℕ) = 1 by omega]
        norm_num
      · exact absurd (calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h) h4
    have hA6 : Nat.card A = 6 := by
      rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF2]
      norm_num
    obtain ⟨c₀, t₀, hc₀, hc₀1, ht₀, ht₀1, hct₀⟩ := SeedSF.exists_s3_gens (F := F)
    have hc₀o : orderOf c₀ = 3 := orderOf_eq_prime (by rw [pow_three']; exact hc₀) hc₀1
    have ht₀o : orderOf t₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht₀) ht₀1
    set c : ↥A := e.symm c₀ with hcdef
    set t : ↥A := e.symm t₀ with htdef
    have hc3 : c * c * c = 1 := by rw [hcdef, ← map_mul, ← map_mul, hc₀, map_one]
    have ht2 : t * t = 1 := by rw [htdef, ← map_mul, ht₀, map_one]
    have hct : t * c = c * c * t := by rw [hcdef, htdef, ← map_mul, ← map_mul, ← map_mul, hct₀]
    have hco : orderOf (c : MulAut W) = 3 := by
      rw [Subgroup.orderOf_coe, hcdef, MulEquiv.orderOf_eq, hc₀o]
    have hto : orderOf (t : MulAut W) = 2 := by
      rw [Subgroup.orderOf_coe, htdef, MulEquiv.orderOf_eq, ht₀o]
    have hcRes : (c : MulAut W) ∈ twoResidual A := by
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient A (c : MulAut W) c.2
      exact SeedSF.mem_of_orderOf_three_of_pow_two_pow_mem hco hk
    rintro y ⟨hy1, hy2⟩
    refine SeedSF.mem_fixV_of_mem_commV hW (c := (c : MulAut W)) (t := (t : MulAut W))
      (by simpa using congrArg Subtype.val hc3) (by simpa using congrArg Subtype.val ht2)
      (by simpa using congrArg Subtype.val hct)
      (fun S hcS htS => SeedSF.le_of_orderOf_three_two hA6 c.2 t.2 hco hto hcS htS) hy1 ?_
    exact hy2 c hcRes

end Coprime

end CFSG.LocalAnalysis.UniquenessCase.UC22

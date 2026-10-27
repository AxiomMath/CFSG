module

public import CFSG.Milestones.ASVolI.A3Aut.Core2
public import CFSG.Milestones.ASVolI.A3Aut.Case5

public section

namespace CFSG.ASVolI

open CFSG.Open

section OddPart

variable {A : Type} [Group A]

@[expose] def burnsideAut_oddPart (Φ : Subgroup A) (hΦ : ∀ x ∈ Φ, ∀ y ∈ Φ, x * y = y * x) :
    Subgroup A where
  carrier := {x | x ∈ Φ ∧ Odd (orderOf x)}
  mul_mem' := by
    rintro x y ⟨hx, hxo⟩ ⟨hy, hyo⟩
    refine ⟨Φ.mul_mem hx hy, ?_⟩
    have hc : Commute x y := hΦ x hx y hy
    exact Odd.of_dvd_nat (Nat.odd_mul.2 ⟨hxo, hyo⟩) (hc.orderOf_mul_dvd_mul_orderOf)
  one_mem' := ⟨Φ.one_mem, by rw [orderOf_one]; exact odd_one⟩
  inv_mem' := by
    rintro x ⟨hx, hxo⟩
    exact ⟨Φ.inv_mem hx, by rw [orderOf_inv]; exact hxo⟩

theorem burnsideAut_oddPart_le (Φ : Subgroup A) (hΦ : ∀ x ∈ Φ, ∀ y ∈ Φ, x * y = y * x) :
    burnsideAut_oddPart Φ hΦ ≤ Φ := fun _ hx => hx.1

theorem burnsideAut_oddPart_odd [Finite A] (Φ : Subgroup A)
    (hΦ : ∀ x ∈ Φ, ∀ y ∈ Φ, x * y = y * x) : Odd (Nat.card (burnsideAut_oddPart Φ hΦ)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(burnsideAut_oddPart Φ hΦ)) 2 h2
  have h1 : orderOf (x : A) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have h2' := x.2.2
  rw [h1] at h2'
  exact (Nat.not_even_iff_odd.2 h2') even_two

theorem burnsideAut_pow_mul_mem {I : Subgroup A} {φ : A}
    (hφ : φ ∈ Subgroup.normalizer (I : Set A)) {i : A} (hi : i ∈ I) (k : ℕ) :
    (i * φ) ^ k * (φ ^ k)⁻¹ ∈ I := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hφk : φ ^ k ∈ Subgroup.normalizer (I : Set A) := Subgroup.pow_mem _ hφ k
    have h1 : (i * φ) ^ (k + 1) * (φ ^ (k + 1))⁻¹ =
        ((i * φ) ^ k * (φ ^ k)⁻¹) * (φ ^ k * i * (φ ^ k)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [h1]
    exact I.mul_mem ih ((Subgroup.mem_normalizer_iff.1 hφk i).1 hi)

theorem burnsideAut_mem_sup_oddPart {I Φ : Subgroup A} (hΦ : ∀ x ∈ Φ, ∀ y ∈ Φ, x * y = y * x)
    (hΦI : Φ ≤ Subgroup.normalizer (I : Set A)) (hIΦ : I ⊓ Φ = ⊥) {b : A} (hb : b ∈ I ⊔ Φ)
    (hbo : Odd (orderOf b)) : b ∈ I ⊔ burnsideAut_oddPart Φ hΦ := by
  obtain ⟨i, hi, φ, hφ, rfl⟩ := (burnsideAut_mem_sup_iff hΦI).1 hb
  have h1 := burnsideAut_pow_mul_mem (hΦI hφ) hi (orderOf (i * φ))
  rw [pow_orderOf_eq_one, one_mul] at h1
  have h2 : (φ ^ orderOf (i * φ))⁻¹ ∈ I ⊓ Φ := ⟨h1, Φ.inv_mem (Φ.pow_mem hφ _)⟩
  rw [hIΦ, Subgroup.mem_bot, inv_eq_one] at h2
  have h3 : Odd (orderOf φ) := Odd.of_dvd_nat hbo (orderOf_dvd_of_pow_eq_one h2)
  exact Subgroup.mul_mem_sup hi ⟨hφ, h3⟩

theorem burnsideAut_map_conj_map_conj' {S : Type*} [Group S] (U : Subgroup S) (φ : MulAut S) :
    (U.map (MulAut.conj : S →* MulAut S)).map (MulAut.conj φ).toMonoidHom =
      (U.map φ.toMonoidHom).map (MulAut.conj : S →* MulAut S) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y : 1
  exact burnsideAut_mul_conj_mul_inv φ y

end OddPart

section Case5b

theorem burnsideAut_conj_injective_of_center {S : Type*} [Group S] (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro y hy
  rw [Subgroup.mem_center_iff]
  intro x
  have h1 := congrArg (fun φ : MulAut S => φ x) (MonoidHom.mem_ker.1 hy)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc x * y = y * x * y⁻¹ * y := by rw [h1]
    _ = y * x := by group

theorem burnsideAut_center_eq_bot {S : Type*} [Group S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have hb : b ∈ Subgroup.center S := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)

variable {G : Type} [Group G]

theorem burnsideAut_case5_of_model2 {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B) [hLn : L.Normal]
    (n : ℕ) (hn : 2 ≤ n) (hLie : CFSG.Quasithin.A315.IsLieChar2 n ↥L)
    {M : Type} [Group M] [Finite M] (hMZ : Subgroup.center M = ⊥) (e : ↥L ≃* M) {UM : Subgroup M}
    (heU : ((T ⊓ L).subgroupOf L).map e.toMonoidHom = UM)
    (hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf UM ⊤)
    {IM ΦM : Subgroup (MulAut M)}
    (hInn : (MulAut.conj : M →* MulAut M).range ≤ IM)
    (hInnOdd : ¬ 2 ∣ (MulAut.conj : M →* MulAut M).range.relIndex IM)
    (hIJ : IM.map (MulAut.congr e.symm).toMonoidHom ≤ ChA.innDiagSubgroup ↥L)
    (hΦc : ∀ x ∈ ΦM, ∀ y ∈ ΦM, x * y = y * x)
    (hΦI : ΦM ≤ Subgroup.normalizer (IM : Set (MulAut M))) (hIΦ : IM ⊓ ΦM = ⊥)
    (hΦU : ΦM ≤ Subgroup.normalizer
      ((UM.map (MulAut.conj : M →* MulAut M) : Subgroup (MulAut M)) : Set (MulAut M)))
    (hB : ∀ b ∈ B, MulAut.congr e (MulAut.conjNormal b) ∈ IM ⊔ ΦM)
    (hsb : burnsideAut_SolvBorel M UM)
    (hpin : ∀ ε : ↥L ≃* M, ((T ⊓ L).subgroupOf L).map ε.toMonoidHom = UM →
      ∀ F : Subgroup (MulAut ↥L), F ≤ ΦM.map (MulAut.congr ε.symm).toMonoidHom →
        Odd (Nat.card F) →
        (∀ x ∈ F, ∃ b ∈ B, x * (MulAut.conjNormal b)⁻¹ ∈
          IM.map (MulAut.congr ε.symm).toMonoidHom) →
        IsCyclic F ∧ Nat.card F ∣ n ∧ ChA.A315PinnedFieldGroup n ↥L ((T ⊓ L).subgroupOf L) F) :
    ChA.A315Case5Concrete L T B := by
  haveI := h.sqtk.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α : G →* MulAut ↥L := MulAut.conjNormal with hα
  have hαinj : Function.Injective α := burnsideAut_conjNormal_injective h
  set S : Subgroup ↥L := (T ⊓ L).subgroupOf L with hS
  set ψ : MulAut M ≃* MulAut ↥L := MulAut.congr e.symm with hψ
  set I : Subgroup (MulAut ↥L) := IM.map ψ.toMonoidHom with hI
  set Φ : Subgroup (MulAut ↥L) := ΦM.map ψ.toMonoidHom with hΦ
  set J : Subgroup (MulAut ↥L) := ChA.innDiagSubgroup ↥L with hJ
  set Lb : Subgroup (MulAut ↥L) := CFSG.Quasithin.A315.autImage L L with hLb
  set Sb : Subgroup (MulAut ↥L) := CFSG.Quasithin.A315.autImage L (T ⊓ L) with hSb
  set Bb : Subgroup (MulAut ↥L) := CFSG.Quasithin.A315.autImage L B with hBb
  set UbM : Subgroup (MulAut M) := UM.map (MulAut.conj : M →* MulAut M) with hUbM
  have hSbeq : Sb = S.map (MulAut.conj : ↥L →* MulAut ↥L) :=
    burnsideAut_autImage_of_le inf_le_right
  have hLbeq : Lb = (MulAut.conj : ↥L →* MulAut ↥L).range := by
    rw [hLb, burnsideAut_autImage_of_le le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  have heS : UM.map e.symm.toMonoidHom = S := by
    rw [← heU, Subgroup.map_map]
    convert Subgroup.map_id S
    ext x
    simp
  have hSbψ : Sb = UbM.map ψ.toMonoidHom := by
    rw [hSbeq, hUbM, hψ]
    have := burnsideAut_map_congr_conj e.symm UM
    rw [this, heS]
  have hInnψ : (MulAut.conj : M →* MulAut M).range.map ψ.toMonoidHom = Lb := by
    rw [hLbeq]
    exact CFSG.RankThree.PartTwo.KFacts.map_innAut_congr e.symm
  have hSbLb : Sb ≤ Lb := by
    rw [hSbeq, hLbeq]
    exact Subgroup.map_le_range _ _
  have hLbI : Lb ≤ I := by
    rw [← hInnψ]
    exact Subgroup.map_mono hInn
  have hIJ' : I ≤ J := hIJ
  set Φo : Subgroup (MulAut M) := burnsideAut_oddPart ΦM hΦc with hΦo
  have hΦoΦ : Φo ≤ ΦM := burnsideAut_oddPart_le ΦM hΦc
  set Φ₁ : Subgroup (MulAut ↥L) := Φo.map ψ.toMonoidHom with hΦ₁
  have hΦ₁I : Φ₁ ≤ Subgroup.normalizer (I : Set (MulAut ↥L)) :=
    burnsideAut_map_equiv_le_normalizer ψ (hΦoΦ.trans hΦI)
  have hIΦ₁ : I ⊓ Φ₁ = ⊥ := by
    rw [hI, hΦ₁, ← Subgroup.map_inf _ _ _ ψ.injective, eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    have : x ∈ IM ⊓ ΦM := ⟨hx.1, hΦoΦ hx.2⟩
    rw [hIΦ, Subgroup.mem_bot] at this
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hΦ₁J : Φ₁ ≤ Subgroup.normalizer (J : Set (MulAut ↥L)) := by
    haveI := burnsideAut_innDiag_normal ↥L
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hΦ₁S : Φ₁ ≤ Subgroup.normalizer (Sb : Set (MulAut ↥L)) := by
    rw [hSbψ]
    exact burnsideAut_map_equiv_le_normalizer ψ (hΦoΦ.trans hΦU)
  have hΦ₁odd : Odd (Nat.card Φ₁) := by
    rw [hΦ₁, Subgroup.card_map_of_injective ψ.injective]
    exact burnsideAut_oddPart_odd ΦM hΦc
  have hSb2 : IsPGroup 2 Sb := (h.sylow.2.1.to_le inf_le_left).map α
  have hcM : Function.Injective (MulAut.conj : M →* MulAut M) :=
    burnsideAut_conj_injective_of_center hMZ
  have hSbLbI : ¬ 2 ∣ Sb.relIndex Lb := by
    rw [hSbψ, ← hInnψ, Subgroup.relIndex_map_map_of_injective _ _ ψ.injective, hUbM,
      MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hcM]
    exact hUsyl.2.2
  have hLbIo : ¬ 2 ∣ Lb.relIndex I := by
    rw [← hInnψ, hI, Subgroup.relIndex_map_map_of_injective _ _ ψ.injective]
    exact hInnOdd
  have hSbI : ¬ 2 ∣ Sb.relIndex (I ⊓ Subgroup.normalizer (Sb : Set (MulAut ↥L))) := by
    have hSbNI : Sb ≤ I ⊓ Subgroup.normalizer (Sb : Set (MulAut ↥L)) :=
      le_inf (hSbLb.trans hLbI) Subgroup.le_normalizer
    have h1 := Subgroup.relIndex_mul_relIndex Sb (I ⊓ Subgroup.normalizer (Sb : Set (MulAut ↥L))) I
      hSbNI inf_le_left
    have h2 := Subgroup.relIndex_mul_relIndex Sb Lb I hSbLb hLbI
    intro hd
    have h3 : 2 ∣ Sb.relIndex I := h1 ▸ Dvd.dvd.mul_right hd _
    rw [← h2, Nat.Prime.dvd_mul Nat.prime_two] at h3
    rcases h3 with h3 | h3
    · exact hSbLbI h3
    · exact hLbIo h3
  have hBΦ : Bb ≤ I ⊔ Φ₁ := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 := hB b hb
    have hbo : Odd (orderOf (MulAut.congr e (α b))) := by
      rw [MulEquiv.orderOf_eq]
      refine Odd.of_dvd_nat ?_ (orderOf_map_dvd α b)
      rw [← Subgroup.orderOf_mk b hb]
      exact Odd.of_dvd_nat h.odd (orderOf_dvd_natCard _)
    have h2 := burnsideAut_mem_sup_oddPart hΦc hΦI hIΦ h1 hbo
    have h3 : ψ (MulAut.congr e (α b)) = α b := burnsideAut_congr_symm_congr e (α b)
    rw [← h3, hI, hΦ₁, ← Subgroup.map_sup]
    exact ⟨_, h2, rfl⟩
  have hsbL : burnsideAut_SolvBorel ↥L S := by
    refine burnsideAut_solvBorel_of_mulEquiv e ?_
    rw [heU]
    exact hsb
  have hBN : B ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    burnsideAut_le_normalizer_of_hyp h hsbL
  have hBS : Bb ≤ Subgroup.normalizer (Sb : Set (MulAut ↥L)) :=
    burnsideAut_map_le_normalizer_map α hBN
  have hBodd : Odd (Nat.card Bb) := by
    rw [hBb, CFSG.Quasithin.A315.autImage, Subgroup.card_map_of_injective hαinj]
    exact h.odd
  obtain ⟨χ, ⟨hχIΦ, hχN⟩, F, H, hFΦ, hFdvd, hFS, hFH, hcart, heq, hle, hFI⟩ :=
    burnsideAut_case5_core2 hSbLb hLbI hIJ' hΦ₁I hIΦ₁ hΦ₁J hΦ₁S hΦ₁odd hSb2 hSbI hBΦ hBS hBodd
  haveI : IsSimpleGroup ↥L := h.simple
  have hLZ : Subgroup.center ↥L = ⊥ := burnsideAut_center_eq_bot h.nonabelian
  have hcL : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) :=
    burnsideAut_conj_injective_of_center hLZ
  set ε : ↥L ≃* M := χ.symm.trans e with hε
  have hχS : S.map χ.toMonoidHom = S := by
    have h1 : Sb.map (MulAut.conj χ).toMonoidHom = Sb :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 hχN
    rw [hSbeq] at h1
    have h2 := burnsideAut_map_conj_map_conj' S χ
    rw [h2] at h1
    exact Subgroup.map_injective hcL h1
  have hεU : S.map ε.toMonoidHom = UM := by
    have h1 : S.map χ.symm.toMonoidHom = S := by
      conv_lhs => rw [← hχS]
      rw [Subgroup.map_map]
      convert Subgroup.map_id S
      ext x
      simp
    calc S.map ε.toMonoidHom = (S.map χ.symm.toMonoidHom).map e.toMonoidHom := by
          rw [Subgroup.map_map]; rfl
      _ = S.map e.toMonoidHom := by rw [h1]
      _ = UM := heU
  have hconj : ∀ X : Subgroup (MulAut M), (X.map ψ.toMonoidHom).map
      (MulAut.conj χ).toMonoidHom = X.map (MulAut.congr ε.symm).toMonoidHom := by
    intro X
    rw [Subgroup.map_map]
    congr 1
  have hχI : χ ∈ Subgroup.normalizer (I : Set (MulAut ↥L)) :=
    (sup_le Subgroup.le_normalizer hΦ₁I) hχIΦ
  have hIε : IM.map (MulAut.congr ε.symm).toMonoidHom = I := by
    rw [← hconj IM]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.1 hχI
  have hFΦε : F ≤ ΦM.map (MulAut.congr ε.symm).toMonoidHom := by
    rw [← hconj ΦM]
    exact hFΦ.trans (Subgroup.map_mono (Subgroup.map_mono hΦoΦ))
  have hFodd : Odd (Nat.card F) := Odd.of_dvd_nat hBodd hFdvd
  have hcond : ∀ x ∈ F, ∃ b ∈ B, x * (MulAut.conjNormal b)⁻¹ ∈
      IM.map (MulAut.congr ε.symm).toMonoidHom := by
    intro x hx
    obtain ⟨b', ⟨b, hb, rfl⟩, hxb⟩ := hFI x hx
    exact ⟨b, hb, hIε.symm ▸ hxb⟩
  obtain ⟨hcyc, hdvdn, hpinF⟩ := hpin ε hεU F hFΦε hFodd hcond
  exact ⟨hLn, n, hn, hLie, F, H, hcyc, hdvdn, hpinF, hFS, hFH, hcart, heq, hle⟩

end Case5b

end CFSG.ASVolI

module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcFrameStab
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIso
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIdx

public section

namespace CFSG.HardMathSupport.C14Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.C14Idx
  CFSG.HardMathSupport.C14Group CFSG.HardMathSupport.C14ExcIso

open scoped CFSG.ConvolutionPoints



@[expose] def eC1_restrictEnd
                                      {Γ : Type*} [Group Γ] (F : Γ →* Γ) (H : Subgroup Γ)
    (hH : ∀ g ∈ H, F g ∈ H) : H →* H :=
  (F.comp H.subtype).codRestrict H fun g => hH g g.2

theorem eC1_restrictEnd_coe
                                      {Γ : Type*} [Group Γ] (F : Γ →* Γ) (H : Subgroup Γ)
    (hH : ∀ g ∈ H, F g ∈ H) (x : H) :
    ((eC1_restrictEnd F H hH x : H) : Γ) = F x := rfl

theorem eC1_endPow_restrictEnd_coe
                                      {Γ : Type*} [Group Γ] (F : Γ →* Γ) (H : Subgroup Γ)
    (hH : ∀ g ∈ H, F g ∈ H) (n : ℕ) (x : H) :
    ((endPow (eC1_restrictEnd F H hH) n x : H) : Γ) = endPow F n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [endPow_apply, endPow_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      ← endPow_apply, ← endPow_apply, ih, eC1_restrictEnd_coe]

theorem eC1_endPow_restrictEnd
                                      {Γ : Type*} [Group Γ] (F : Γ →* Γ) (H : Subgroup Γ)
    (hH : ∀ g ∈ H, F g ∈ H) (n : ℕ) :
    endPow (eC1_restrictEnd F H hH) n = eC1_restrictEnd (endPow F n) H (fun g hg => endPow_mem hH n hg) := by
  ext x
  rw [eC1_endPow_restrictEnd_coe, eC1_restrictEnd_coe]

@[expose] def eC1_fixEquiv
                                      {Γ : Type*} [Group Γ] (F : Γ →* Γ) (H : Subgroup Γ)
    (hH : ∀ g ∈ H, F g ∈ H) : fixG (eC1_restrictEnd F H hH) ≃* ↥(H ⊓ fixG F) where
  toFun x := ⟨(x.1 : Γ), Subgroup.mem_inf.mpr ⟨x.1.2, mem_fixG.2 (by
    rw [← eC1_restrictEnd_coe F H hH x.1]
    exact congrArg Subtype.val x.2)⟩⟩
  invFun y := ⟨⟨(y.1 : Γ), y.2.1⟩, by
    apply Subtype.ext
    rw [eC1_restrictEnd_coe]
    exact mem_fixG.1 y.2.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl

theorem eC1_card_fixG_restrictEnd
                                      {Γ : Type*} [Group Γ] (F : Γ →* Γ) (H : Subgroup Γ)
    (hH : ∀ g ∈ H, F g ∈ H) :
    Nat.card (fixG (eC1_restrictEnd F H hH)) = Nat.card ↥(H ⊓ fixG F) :=
  Nat.card_congr (eC1_fixEquiv F H hH).toEquiv

theorem eC1_subgroupOf_map_subtype
                                      {Γ : Type*} [Group Γ] (H : Subgroup Γ) (K : Subgroup H) :
    (K.map H.subtype).subgroupOf H = K := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, hky⟩
    have h : k = y := Subtype.ext hky
    rwa [h] at hk
  · intro hy
    exact ⟨y, hy, rfl⟩

private def eC1_prodToSub
                                      {Γ : Type*} [Group Γ] (M Z S : Subgroup Γ) (hZM : Z ≤ M)
    (hSM : S ≤ M) (hZc : ∀ z ∈ Z, ∀ m ∈ M, z * m = m * z) : Z × S →* M where
  toFun x := ⟨(x.1 : Γ) * (x.2 : Γ), mul_mem (hZM x.1.2) (hSM x.2.2)⟩
  map_one' := by ext; simp
  map_mul' := by
    intro x y
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Prod.fst_mul, Prod.snd_mul]
    rw [mul_assoc, ← mul_assoc (y.1 : Γ) (x.2 : Γ) (y.2 : Γ),
      hZc y.1 y.1.2 x.2 (hSM x.2.2)]
    group

private theorem eC1_prodToSub_coe
                                      {Γ : Type*} [Group Γ] (M Z S : Subgroup Γ) (hZM : Z ≤ M)
    (hSM : S ≤ M) (hZc : ∀ z ∈ Z, ∀ m ∈ M, z * m = m * z) (x : Z × S) :
    (eC1_prodToSub M Z S hZM hSM hZc x : Γ) = (x.1 : Γ) * (x.2 : Γ) := rfl

private theorem eC1_card_fixed_prod_eq
                                      {Γ : Type*} [Group Γ] {p : ℕ} (F₀ : Γ →* Γ)
    (M Z S : Subgroup Γ) (hZM : Z ≤ M) (hSM : S ≤ M)
    (hMS : ∀ m ∈ M, ∃ z ∈ Z, ∃ s ∈ S, m = z * s)
    (hZc : ∀ z ∈ Z, ∀ m ∈ M, z * m = m * z) (hZab : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z)
    (hFM : ∀ g ∈ M, F₀ g ∈ M) (hFZ : ∀ z ∈ Z, F₀ z ∈ Z) (hFS : ∀ s ∈ S, F₀ s ∈ S)
    [Finite ↥(Z ⊓ S)]
    (hLZ : ∀ c ∈ Z ⊓ S, ∃ z ∈ Z, z⁻¹ * endPow F₀ p z = c)
    (hLS : ∀ c ∈ Z ⊓ S, ∃ s ∈ S, s⁻¹ * endPow F₀ p s = c) :
    Nat.card ↥(M ⊓ fixG (endPow F₀ p)) =
      Nat.card ↥(Z ⊓ fixG (endPow F₀ p)) * Nat.card ↥(S ⊓ fixG (endPow F₀ p)) := by
  have hFZ' : ∀ z ∈ Z, endPow F₀ p z ∈ Z := fun z hz => endPow_mem hFZ p hz
  have hFS' : ∀ s ∈ S, endPow F₀ p s ∈ S := fun s hs => endPow_mem hFS p hs
  have hFM' : ∀ g ∈ M, endPow F₀ p g ∈ M := fun g hg => endPow_mem hFM p hg
  let FA : Z →* Z := eC1_restrictEnd (endPow F₀ p) Z hFZ'
  let FB : S →* S := eC1_restrictEnd (endPow F₀ p) S hFS'
  let FM : M →* M := eC1_restrictEnd (endPow F₀ p) M hFM'
  let FP : Z × S →* Z × S := FA.prodMap FB
  let μ : Z × S →* M := eC1_prodToSub M Z S hZM hSM hZc
  have hμ : Function.Surjective μ := by
    rintro ⟨m, hm⟩
    obtain ⟨z, hzZ, s, hsS, hms⟩ := hMS m hm
    refine ⟨(⟨z, hzZ⟩, ⟨s, hsS⟩), ?_⟩
    apply Subtype.ext
    rw [eC1_prodToSub_coe]
    exact hms.symm
  have hK : μ.ker ≤ Subgroup.center (Z × S) := by
    intro x hx
    have h1 : (x.1 : Γ) * (x.2 : Γ) = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      rw [eC1_prodToSub_coe] at h
      simpa using h
    have hx1S : (x.1 : Γ) ∈ S := by
      have hz : (x.1 : Γ) = (x.2 : Γ)⁻¹ := by
        calc (x.1 : Γ) = (x.1 : Γ) * (x.2 : Γ) * (x.2 : Γ)⁻¹ := by group
          _ = (x.2 : Γ)⁻¹ := by rw [h1, one_mul]
      rw [hz]; exact inv_mem x.2.2
    have hx2Z : (x.2 : Γ) ∈ Z := by
      have hs : (x.2 : Γ) = (x.1 : Γ)⁻¹ := by
        calc (x.2 : Γ) = (x.1 : Γ)⁻¹ * ((x.1 : Γ) * (x.2 : Γ)) := by group
          _ = (x.1 : Γ)⁻¹ := by rw [h1, mul_one]
      rw [hs]; exact inv_mem x.1.2
    rw [Subgroup.mem_center_iff]
    intro y
    apply Prod.ext
    · apply Subtype.ext
      exact (hZab x.1 x.1.2 y.1 y.1.2).symm
    · apply Subtype.ext
      exact (hZc x.2 hx2Z y.2 (hSM y.2.2)).symm
  haveI : Finite μ.ker := by
    let f : μ.ker → ↥(Z ⊓ S) := fun k =>
      ⟨((k.1).1 : Γ), Subgroup.mem_inf.mpr ⟨(k.1).1.2, by
        have h1 : ((k.1).1 : Γ) * ((k.1).2 : Γ) = 1 := by
          have h := congrArg Subtype.val (MonoidHom.mem_ker.1 k.2)
          rw [eC1_prodToSub_coe] at h
          simpa using h
        have hz : ((k.1).1 : Γ) = ((k.1).2 : Γ)⁻¹ := by
          calc ((k.1).1 : Γ) = ((k.1).1 : Γ) * ((k.1).2 : Γ) * ((k.1).2 : Γ)⁻¹ := by group
            _ = ((k.1).2 : Γ)⁻¹ := by rw [h1, one_mul]
        rw [hz]; exact inv_mem (k.1).2.2⟩⟩
    refine Finite.of_injective f ?_
    intro k l hkl
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z : ↥(Z ⊓ S) => (z : Γ)) hkl
    · apply Subtype.ext
      have hk1 : ((k.1).1 : Γ) * ((k.1).2 : Γ) = 1 := by
        have h := congrArg Subtype.val (MonoidHom.mem_ker.1 k.2)
        rw [eC1_prodToSub_coe] at h
        simpa using h
      have hl1 : ((l.1).1 : Γ) * ((l.1).2 : Γ) = 1 := by
        have h := congrArg Subtype.val (MonoidHom.mem_ker.1 l.2)
        rw [eC1_prodToSub_coe] at h
        simpa using h
      have hk2 : ((k.1).2 : Γ) = ((k.1).1 : Γ)⁻¹ := by
        calc ((k.1).2 : Γ) = ((k.1).1 : Γ)⁻¹ * (((k.1).1 : Γ) * ((k.1).2 : Γ)) := by group
          _ = ((k.1).1 : Γ)⁻¹ := by rw [hk1, mul_one]
      have hl2 : ((l.1).2 : Γ) = ((l.1).1 : Γ)⁻¹ := by
        calc ((l.1).2 : Γ) = ((l.1).1 : Γ)⁻¹ * (((l.1).1 : Γ) * ((l.1).2 : Γ)) := by group
          _ = ((l.1).1 : Γ)⁻¹ := by rw [hl1, mul_one]
      rw [hk2, hl2, congrArg (fun z : ↥(Z ⊓ S) => (z : Γ)) hkl]
  have hcomm : ∀ h : Z × S, μ (FP h) = FM (μ h) := by
    intro h
    apply Subtype.ext
    change (eC1_restrictEnd (endPow F₀ p) Z hFZ' h.1 : Γ) *
        (eC1_restrictEnd (endPow F₀ p) S hFS' h.2 : Γ) =
      endPow F₀ p ((h.1 : Γ) * (h.2 : Γ))
    rw [eC1_restrictEnd_coe, eC1_restrictEnd_coe, map_mul]
  have hLang : ∀ k ∈ μ.ker, ∃ x : Z × S, x⁻¹ * FP x = k := by
    intro k hk
    have h1 : (k.1 : Γ) * (k.2 : Γ) = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
      rw [eC1_prodToSub_coe] at h
      simpa using h
    have hk1S : (k.1 : Γ) ∈ S := by
      have hz : (k.1 : Γ) = (k.2 : Γ)⁻¹ := by
        calc (k.1 : Γ) = (k.1 : Γ) * (k.2 : Γ) * (k.2 : Γ)⁻¹ := by group
          _ = (k.2 : Γ)⁻¹ := by rw [h1, one_mul]
      rw [hz]; exact inv_mem k.2.2
    have hk2Z : (k.2 : Γ) ∈ Z := by
      have hs : (k.2 : Γ) = (k.1 : Γ)⁻¹ := by
        calc (k.2 : Γ) = (k.1 : Γ)⁻¹ * ((k.1 : Γ) * (k.2 : Γ)) := by group
          _ = (k.1 : Γ)⁻¹ := by rw [h1, mul_one]
      rw [hs]; exact inv_mem k.1.2
    obtain ⟨a, haZ, haeq⟩ := hLZ (k.1 : Γ) ⟨k.1.2, hk1S⟩
    obtain ⟨b, hbS, hbeq⟩ := hLS (k.2 : Γ) ⟨hk2Z, k.2.2⟩
    refine ⟨(⟨a, haZ⟩, ⟨b, hbS⟩), ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change (a : Γ)⁻¹ * eC1_restrictEnd (endPow F₀ p) Z hFZ' ⟨a, haZ⟩ = (k.1 : Γ)
      rw [eC1_restrictEnd_coe]
      exact haeq
    · apply Subtype.ext
      change (b : Γ)⁻¹ * eC1_restrictEnd (endPow F₀ p) S hFS' ⟨b, hbS⟩ = (k.2 : Γ)
      rw [eC1_restrictEnd_coe]
      exact hbeq
  have h1 := card_fixed_eq_of_isogeny μ hμ hK FP FM hcomm hLang
  have h2 : Nat.card (fixG FP) = Nat.card (fixG FA) * Nat.card (fixG FB) := by
    change Nat.card (fixG (FA.prodMap FB)) = Nat.card (fixG FA) * Nat.card (fixG FB)
    exact card_fixed_prod FA FB
  have h3 : Nat.card (fixG FM) = Nat.card ↥(M ⊓ fixG (endPow F₀ p)) :=
    eC1_card_fixG_restrictEnd (endPow F₀ p) M hFM'
  have h4 : Nat.card (fixG FA) = Nat.card ↥(Z ⊓ fixG (endPow F₀ p)) :=
    eC1_card_fixG_restrictEnd (endPow F₀ p) Z hFZ'
  have h5 : Nat.card (fixG FB) = Nat.card ↥(S ⊓ fixG (endPow F₀ p)) :=
    eC1_card_fixG_restrictEnd (endPow F₀ p) S hFS'
  rw [h2, h3, h4, h5] at h1
  exact h1.symm

theorem eC1_card_subgroupOf_inf_fixG
                                      {Γ : Type*} [Group Γ] (F : Γ →* Γ) (M Z : Subgroup Γ)
    (hZM : Z ≤ M) (hM : ∀ g ∈ M, F g ∈ M) :
    Nat.card ↥(Z.subgroupOf M ⊓ fixG (eC1_restrictEnd F M hM)) =
      Nat.card ↥(Z ⊓ fixG F) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨(y.1 : Γ), Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.1 y.2.1,
        (eC1_restrictEnd_coe F M hM y.1).symm.trans (congrArg Subtype.val y.2.2)⟩⟩
      invFun := fun x => ⟨⟨(x.1 : Γ), hZM x.2.1⟩, Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.2 x.2.1,
        (by apply Subtype.ext; rw [eC1_restrictEnd_coe]; exact mem_fixG.1 x.2.2)⟩⟩
      left_inv := fun y => Subtype.ext (Subtype.ext rfl)
      right_inv := fun x => Subtype.ext rfl }

theorem eC1_not_dvd_card_fixed_S
                                      {Γ : Type*} [Group Γ] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (F₀ : Γ →* Γ) (M S E : Subgroup Γ) (hSM : S ≤ M) (hFS : ∀ s ∈ S, F₀ s ∈ S)
    [Finite ↥(S ⊓ fixG (endPow F₀ p))]
    (hEM : ∀ x ∈ E, ∀ m ∈ M, x * m = m * x)
    (hsat0 : ∀ y ∈ M, F₀ y = y → y ^ p = 1 → y ∈ E)
    (hidx0 : ¬ p ∣ ((Subgroup.closure {x | x ∈ S ⊓ fixG F₀ ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}).subgroupOf
      (S ⊓ fixG F₀)).index) :
    ¬ p ∣ Nat.card ↥(S ⊓ fixG (endPow F₀ p)) := by
  let G₀ : S →* S := eC1_restrictEnd F₀ S hFS
  let G : S →* S := endPow G₀ p
  have hFS' : ∀ s ∈ S, endPow F₀ p s ∈ S := fun s hs => endPow_mem hFS p hs
  have hGE : G = eC1_restrictEnd (endPow F₀ p) S hFS' := by
    change endPow (eC1_restrictEnd F₀ S hFS) p = eC1_restrictEnd (endPow F₀ p) S hFS'
    exact eC1_endPow_restrictEnd F₀ S hFS p
  have hcardGG : Nat.card (fixG G) = Nat.card ↥(S ⊓ fixG (endPow F₀ p)) := by
    rw [hGE]
    exact eC1_card_fixG_restrictEnd (endPow F₀ p) S hFS'
  haveI : Finite (fixG G) := by
    rw [hGE]
    exact Finite.of_equiv ↥(S ⊓ fixG (endPow F₀ p))
      (eC1_fixEquiv (endPow F₀ p) S hFS').symm
  have hG : ∀ x : S, G x = G₀^[p] x := fun x => endPow_apply G₀ p x
  have hSat : ∀ x : fixG G₀, x ^ p = 1 → x ∈ Subgroup.center (fixG G₀) := by
    intro x hx
    have hfix0 : F₀ (x.1 : Γ) = (x.1 : Γ) := by
      have h := congrArg Subtype.val x.2
      rw [eC1_restrictEnd_coe] at h
      exact h
    have hxp : (x.1 : Γ) ^ p = 1 := by
      have h1 : x.1 ^ p = 1 := congrArg Subtype.val hx
      simpa using congrArg Subtype.val h1
    have hxE : (x.1 : Γ) ∈ E := hsat0 (x.1 : Γ) (hSM x.1.2) hfix0 hxp
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Subtype.ext
    exact (hEM (x.1 : Γ) hxE (g.1 : Γ) (hSM g.1.2)).symm
  have hidx0' : ¬ p ∣ (Subgroup.closure {x : fixG G₀ | ∃ k : ℕ, x ^ 2 ^ k = 1}).index := by
    let H' : Subgroup Γ := S ⊓ fixG F₀
    let D : Subgroup H' :=
      (Subgroup.closure {x : Γ | x ∈ H' ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}).subgroupOf H'
    let K : Subgroup H' := Subgroup.closure {y : H' | ∃ k : ℕ, y ^ 2 ^ k = 1}
    have hD : D = K := by
      have hmap : Subgroup.map H'.subtype K =
          Subgroup.closure {x : Γ | x ∈ H' ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} := by
        change Subgroup.map H'.subtype (Subgroup.closure {y : H' | ∃ k : ℕ, y ^ 2 ^ k = 1}) = _
        rw [MonoidHom.map_closure]
        congr 1
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          obtain ⟨k, hk⟩ := hy
          exact ⟨y.2, ⟨k, by
            simpa using congrArg (fun z : H' => (z : Γ)) hk⟩⟩
        · rintro ⟨hxH, hxP⟩
          obtain ⟨k, hk⟩ := hxP
          exact ⟨⟨x, hxH⟩, ⟨k, Subtype.ext (by simpa using hk)⟩, rfl⟩
      change (Subgroup.closure {x : Γ | x ∈ H' ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}).subgroupOf H' = K
      rw [← hmap]
      exact eC1_subgroupOf_map_subtype H' K
    have hidx_eq : (Subgroup.closure {x : fixG G₀ | ∃ k : ℕ, x ^ 2 ^ k = 1}).index = D.index := by
      let Φ : fixG G₀ ≃* H' := eC1_fixEquiv F₀ S hFS
      have himg : Φ '' {x : fixG G₀ | ∃ k : ℕ, x ^ 2 ^ k = 1} =
          {y : H' | ∃ k : ℕ, y ^ 2 ^ k = 1} := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          obtain ⟨k, hk⟩ := hx
          exact ⟨k, by rw [← map_pow, hk, map_one]⟩
        · rintro ⟨k, hk⟩
          exact ⟨Φ.symm y, ⟨k, by
            apply Φ.injective
            rw [map_pow, Φ.apply_symm_apply, hk, map_one]⟩, Φ.apply_symm_apply y⟩
      have hmapK : Subgroup.map (Φ : fixG G₀ →* H')
            (Subgroup.closure {x : fixG G₀ | ∃ k : ℕ, x ^ 2 ^ k = 1}) = K := by
        change Subgroup.map (Φ : fixG G₀ →* H')
            (Subgroup.closure {x : fixG G₀ | ∃ k : ℕ, x ^ 2 ^ k = 1}) =
          Subgroup.closure {y : H' | ∃ k : ℕ, y ^ 2 ^ k = 1}
        rw [MonoidHom.map_closure]
        change Subgroup.closure (⇑Φ '' {x : fixG G₀ | ∃ k : ℕ, x ^ 2 ^ k = 1}) =
          Subgroup.closure {y : H' | ∃ k : ℕ, y ^ 2 ^ k = 1}
        rw [himg]
      calc (Subgroup.closure {x : fixG G₀ | ∃ k : ℕ, x ^ 2 ^ k = 1}).index
          = (Subgroup.map (Φ : fixG G₀ →* H')
              (Subgroup.closure {x : fixG G₀ | ∃ k : ℕ, x ^ 2 ^ k = 1})).index :=
            (Subgroup.index_map_equiv _ Φ).symm
        _ = K.index := by rw [hmapK]
        _ = D.index := by rw [hD]
    rw [hidx_eq]
    exact hidx0
  have hnot := not_dvd_card_fixed_of_index hp hp2 G₀ G hG hSat hidx0'
  rwa [hcardGG] at hnot

theorem prop43_abstract
    {Γ : Type*} [Group Γ] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (F₀ : Γ →* Γ)
    (M Z S E : Subgroup Γ) (hZM : Z ≤ M) (hSM : S ≤ M)
    (hMS : ∀ m ∈ M, ∃ z ∈ Z, ∃ s ∈ S, m = z * s)
    (hZc : ∀ z ∈ Z, ∀ m ∈ M, z * m = m * z) (hZab : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z)
    (hFM : ∀ g ∈ M, F₀ g ∈ M) (hFZ : ∀ z ∈ Z, F₀ z ∈ Z) (hFS : ∀ s ∈ S, F₀ s ∈ S)
    [Finite ↥(Z ⊓ S)]
    (hLZ : ∀ c ∈ Z ⊓ S, ∃ z ∈ Z, z⁻¹ * endPow F₀ p z = c)
    (hLS : ∀ c ∈ Z ⊓ S, ∃ s ∈ S, s⁻¹ * endPow F₀ p s = c)
    [Finite ↥(fixG (endPow F₀ p))]
    (hEM : ∀ x ∈ E, ∀ m ∈ M, x * m = m * x)
    (hsat0 : ∀ y ∈ M, F₀ y = y → y ^ p = 1 → y ∈ E)
    (hidx : ¬ p ∣ ((Subgroup.closure {x | x ∈ S ⊓ fixG F₀ ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}).subgroupOf
      (S ⊓ fixG F₀)).index) :
    ∀ y ∈ M, endPow F₀ p y = y → (∃ n : ℕ, y ^ p ^ n = 1) → y ∈ Z := by
  have hFM' : ∀ g ∈ M, endPow F₀ p g ∈ M := fun g hg => endPow_mem hFM p hg
  haveI : Finite ↥(M ⊓ fixG (endPow F₀ p)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      (inf_le_right : M ⊓ fixG (endPow F₀ p) ≤ fixG (endPow F₀ p)))
  haveI : Finite ↥(S ⊓ fixG (endPow F₀ p)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      (inf_le_right : S ⊓ fixG (endPow F₀ p) ≤ fixG (endPow F₀ p)))
  have hs : ¬ p ∣ Nat.card ↥(S ⊓ fixG (endPow F₀ p)) :=
    eC1_not_dvd_card_fixed_S hp hp2 F₀ M S E hSM hFS hEM hsat0 hidx
  intro y hyM hyfix hgp
  let FM : M →* M := eC1_restrictEnd (endPow F₀ p) M hFM'
  let Z' : Subgroup M := Z.subgroupOf M
  have hZ'c : Z' ≤ Subgroup.center M := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    rw [Subgroup.mem_center_iff]
    intro m
    exact Subtype.ext (hZc z hz m m.2).symm
  have hord : Nat.card (fixG FM) =
      Nat.card ↥(Z' ⊓ fixG FM : Subgroup M) * Nat.card ↥(S ⊓ fixG (endPow F₀ p)) := by
    rw [show Nat.card (fixG FM) = Nat.card ↥(M ⊓ fixG (endPow F₀ p)) from
        eC1_card_fixG_restrictEnd (endPow F₀ p) M hFM',
      show Nat.card ↥(Z' ⊓ fixG FM : Subgroup M) = Nat.card ↥(Z ⊓ fixG (endPow F₀ p)) from
        eC1_card_subgroupOf_inf_fixG (endPow F₀ p) M Z hZM hFM']
    exact eC1_card_fixed_prod_eq F₀ M Z S hZM hSM hMS hZc hZab hFM hFZ hFS hLZ hLS
  haveI : Finite (fixG FM) :=
    Finite.of_equiv ↥(M ⊓ fixG (endPow F₀ p)) (eC1_fixEquiv (endPow F₀ p) M hFM').symm
  have hg : FM ⟨y, hyM⟩ = ⟨y, hyM⟩ := by
    apply Subtype.ext
    rw [eC1_restrictEnd_coe]
    exact hyfix
  have hgp' : ∃ n : ℕ, (⟨y, hyM⟩ : M) ^ p ^ n = 1 := by
    obtain ⟨n, hn⟩ := hgp
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hmem := pElt_mem_of_card hp FM Z' hZ'c
    (Nat.card ↥(S ⊓ fixG (endPow F₀ p))) hord hs ⟨y, hyM⟩ hg hgp'
  exact Subgroup.mem_subgroupOf.1 hmem

theorem endPow_frobTwistGL
                                      {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ} {Q' : ModGL τ L} (hQ : entrywiseFrobGL τ L 2 e Q' = Q') (n : ℕ) :
    endPow (frobTwistGL τ L 2 e Q') n = frobTwistGL τ L 2 (e * n) (Q' ^ n) := by
  ext g
  rw [endPow_apply, frobTwistGL_apply, frobTwistGL_iterate 2 e hQ n g]

private theorem eC2_entrywiseFrobGL_canonicalRep
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (e : ℕ) (w : WeylGroup τ) :
    entrywiseFrobGL τ L 2 e (canonicalRep (coxeterSystem τ) L w) =
      canonicalRep (coxeterSystem τ) L w := by
  have h := entrywise_canonicalRep (K := L) (iterateFrobeniusEquiv L 2 e) w
  rw [iterateFrobeniusEquiv_toRingHom] at h
  exact h

theorem entrywiseFrobGL_frameMatrix
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {Q : ModGL τ L}
    (hQ : IsDiagramTwistMatrix τ L Q) (w : WeylGroup τ)
    (e : ℕ) :
    entrywiseFrobGL τ L 2 e (canonicalRep (coxeterSystem τ) L w * Q) =
      canonicalRep (coxeterSystem τ) L w * Q := by
  rcases hQ with rfl | ⟨t, j, rfl, rfl⟩
  · rw [mul_one, eC2_entrywiseFrobGL_canonicalRep]
  · rw [map_mul, eC2_entrywiseFrobGL_canonicalRep, entrywiseFrobGL_diagramMap_zpow t 2 e j]

theorem lang_famZ
    {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] (hBor : ExcBorelInput) {ι : Type} (a : ι → Fin τ.rank → Lˣ) {e : ℕ}
    (he : 1 ≤ e)
    {Q' : ModGL τ L} (hQfr : entrywiseFrobGL τ L 2 e Q' = Q') {p : ℕ} (hp : 1 ≤ p)
    (hstab : ∀ g ∈ famZ a, frobTwistGL τ L 2 e Q' g ∈ famZ a) :
    ∀ c ∈ famZ a, ∃ z ∈ famZ a, z⁻¹ * endPow (frobTwistGL τ L 2 e Q') p z = c := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨-, -, -, hZconn, -⟩ := hBor τ L a
  have hiter : ∀ g, endPow (frobTwistGL τ L 2 e Q') p g =
      frobTwistGL τ L 2 (e * p) (Q' ^ p) g :=
    fun g => congrArg (fun f => f g) (endPow_frobTwistGL hQfr p)
  have hQ : ∀ g ∈ famZ a, frobTwistGL τ L 2 (e * p) (Q' ^ p) g ∈ famZ a := by
    intro g hg
    rw [← hiter g]
    exact endPow_mem hstab p hg
  have hee : 1 ≤ e * p := by simpa using Nat.mul_le_mul he hp
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction (τ := τ) (k := L) (p := 2)
    hZconn (e := e * p) hee (Q' ^ p) hQ
  intro c hc
  obtain ⟨z, hz, hzc⟩ := hlang c hc
  exact ⟨z, hz, by rw [hiter z]; exact hzc⟩

theorem lang_famS
    {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] (hBor : ExcBorelInput) {ι : Type} (a : ι → Fin τ.rank → Lˣ) {e : ℕ}
    (he : 1 ≤ e)
    {Q' : ModGL τ L} (hQfr : entrywiseFrobGL τ L 2 e Q' = Q') {p : ℕ} (hp : 1 ≤ p)
    (hstab : ∀ g ∈ (famS a).map (adjointGroup τ L).subtype,
      frobTwistGL τ L 2 e Q' g ∈ (famS a).map (adjointGroup τ L).subtype) :
    ∀ c ∈ (famS a).map (adjointGroup τ L).subtype, ∃ s ∈ (famS a).map (adjointGroup τ L).subtype,
      s⁻¹ * endPow (frobTwistGL τ L 2 e Q') p s = c := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨-, -, -, -, hSconn⟩ := hBor τ L a
  have hiter : ∀ g, endPow (frobTwistGL τ L 2 e Q') p g =
      frobTwistGL τ L 2 (e * p) (Q' ^ p) g :=
    fun g => congrArg (fun f => f g) (endPow_frobTwistGL hQfr p)
  have hQ : ∀ g ∈ (famS a).map (adjointGroup τ L).subtype,
      frobTwistGL τ L 2 (e * p) (Q' ^ p) g ∈ (famS a).map (adjointGroup τ L).subtype := by
    intro g hg
    rw [← hiter g]
    exact endPow_mem hstab p hg
  have hee : 1 ≤ e * p := by simpa using Nat.mul_le_mul he hp
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction (τ := τ) (k := L) (p := 2)
    hSconn (e := e * p) hee (Q' ^ p) hQ
  intro c hc
  obtain ⟨s, hs, hsc⟩ := hlang c hc
  exact ⟨s, hs, by rw [hiter s]; exact hsc⟩

theorem central_structure
                                   {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (hBor : ExcBorelInput) {ι : Type} (a : ι → Fin τ.rank → Lˣ) :
    (famZ a).subgroupOf (adjointGroup τ L) ≤ famM a ∧ famS a ≤ famM a ∧
    (∀ m ∈ famM a, ∃ z ∈ (famZ a).subgroupOf (adjointGroup τ L), ∃ s ∈ famS a, m = z * s) ∧
    (∀ z ∈ (famZ a).subgroupOf (adjointGroup τ L), ∀ m ∈ famM a, z * m = m * z) ∧
    (∀ z ∈ (famZ a).subgroupOf (adjointGroup τ L), ∀ z' ∈ (famZ a).subgroupOf (adjointGroup τ L),
      z * z' = z' * z) ∧
    Finite ↥((famZ a).subgroupOf (adjointGroup τ L) ⊓ famS a) := by
  obtain ⟨hBor1, hBor2, hBor3, -, -⟩ := hBor τ L a
  have hZtorus : famZ a ≤ torusGroup τ L := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨lam, c, hlam, rfl⟩
    exact rootDiagUnit_mem_torusGroup (cochar lam c)
  have hZfam : famZ a ≤ familyGroup a := hZtorus.trans le_sup_left
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hZfam (Subgroup.mem_subgroupOf.mp hx)
  · rw [famS, Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  · intro m hm
    obtain ⟨z, hz, s, hs, hzs⟩ := hBor2 m hm
    refine ⟨⟨z, (hBor1 z hz).1⟩, Subgroup.mem_subgroupOf.mpr hz, s, hs, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact hzs
  · intro z hz m hm
    apply Subtype.ext
    exact (hBor1 z (Subgroup.mem_subgroupOf.mp hz)).2 m hm
  · intro z hz z' hz'
    apply Subtype.ext
    exact mul_comm_of_mem_diagonalGroup
      (torusGroup_le_diagonalGroup (hZtorus (Subgroup.mem_subgroupOf.mp hz)))
      (torusGroup_le_diagonalGroup (hZtorus (Subgroup.mem_subgroupOf.mp hz')))
  · refine Finite.of_injective
      (fun x : ↥((famZ a).subgroupOf (adjointGroup τ L) ⊓ famS a) =>
        (⟨x.1, Subgroup.mem_subgroupOf.mp x.2.1, x.2.2⟩ :
          {g : adjointGroup τ L // (g : ModGL τ L) ∈ famZ a ∧ g ∈ famS a})) ?_
    intro x y h
    exact Subtype.ext (Subtype.ext_iff.mp h)

theorem central_stability
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h5 : τ = .E8 → p ≠ 5) {ι : Type}
    [Finite ι]
    (a : ι → Fin τ.rank → Lˣ) (ha : ∀ i j, a i j ^ p = 1) {e : ℕ} {Q' : ModGL τ L}
    (hQT : ∀ t, ∃ t', Q' * rootDiagUnit τ t * Q'⁻¹ = rootDiagUnit τ t')
    (hQτ : Q' ∈ adjointGroup τ L ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ) (n : ModGL τ L),
      n ∈ adjointGroup τ L ∧ Q' = (h ▸ diagramMap t L ^ j) * n)
    (hfix : ∀ i, frobTwistGL τ L 2 e Q' (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i)) :
    (∀ g ∈ famM a, frameEndo e hQτ g ∈ famM a) ∧
    (∀ z ∈ (famZ a).subgroupOf (adjointGroup τ L),
      frameEndo e hQτ z ∈ (famZ a).subgroupOf (adjointGroup τ L)) ∧
    (∀ s ∈ famS a, frameEndo e hQτ s ∈ famS a) := by
  have hM : ∀ g ∈ famM a, frameEndo e hQτ g ∈ famM a := by
    intro g hg
    rw [famM, Subgroup.mem_subgroupOf] at hg ⊢
    rw [frameEndo_apply]
    exact (frobTwistGL_mem_familyGroup hp hp2 h3 h5 a ha hQτ hfix ⟨g.2, hg⟩).2
  have hZ : ∀ z ∈ (famZ a).subgroupOf (adjointGroup τ L),
      frameEndo e hQτ z ∈ (famZ a).subgroupOf (adjointGroup τ L) := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    rw [frameEndo_apply]
    exact frobTwistGL_mem_famZ hp hp2 a ha hQT hfix hz
  exact ⟨hM, hZ, fun s hs => commutator_stable (frameEndo e hQτ) (famM a) hM s hs⟩

private theorem eC6_coe_endPow
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {e : ℕ} {Q' : ModGL τ L}
    (hQτ : Q' ∈ adjointGroup τ L ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ) (n : ModGL τ L),
      n ∈ adjointGroup τ L ∧ Q' = (h ▸ diagramMap t L ^ j) * n) (p : ℕ) (x : adjointGroup τ L) :
    ((endPow (frameEndo e hQτ) p x : adjointGroup τ L) : ModGL τ L) =
      endPow (frobTwistGL τ L 2 e Q') p (x : ModGL τ L) := by
  induction p generalizing x with
  | zero => rfl
  | succ p ih =>
    have hstep : endPow (frameEndo e hQτ) (p + 1) x =
        frameEndo e hQτ (endPow (frameEndo e hQτ) p x) := by
      simp only [endPow_apply]
      rw [Function.iterate_succ_apply']
    rw [hstep, frameEndo_apply, ih x]
    simp only [endPow_apply]
    rw [Function.iterate_succ_apply']

theorem central_lang
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (hBor : ExcBorelInput) {p : ℕ} (hp : 1 ≤ p) {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    {e : ℕ} (he : 1 ≤ e) {Q' : ModGL τ L} (hQfr : entrywiseFrobGL τ L 2 e Q' = Q')
    (hQτ : Q' ∈ adjointGroup τ L ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ) (n : ModGL τ L),
      n ∈ adjointGroup τ L ∧ Q' = (h ▸ diagramMap t L ^ j) * n)
    (hZ : ∀ z ∈ (famZ a).subgroupOf (adjointGroup τ L),
      frameEndo e hQτ z ∈ (famZ a).subgroupOf (adjointGroup τ L))
    (hS : ∀ s ∈ famS a, frameEndo e hQτ s ∈ famS a) :
    (∀ c ∈ (famZ a).subgroupOf (adjointGroup τ L) ⊓ famS a,
      ∃ z ∈ (famZ a).subgroupOf (adjointGroup τ L), z⁻¹ * endPow (frameEndo e hQτ) p z = c) ∧
    (∀ c ∈ (famZ a).subgroupOf (adjointGroup τ L) ⊓ famS a,
      ∃ s ∈ famS a, s⁻¹ * endPow (frameEndo e hQτ) p s = c) := by
  have hstabZ : ∀ g ∈ famZ a, frobTwistGL τ L 2 e Q' g ∈ famZ a := by
    intro g hg
    have hgG : g ∈ adjointGroup τ L := ((hBor τ L a).1 g hg).1
    have hmem : (⟨g, hgG⟩ : adjointGroup τ L) ∈ (famZ a).subgroupOf (adjointGroup τ L) :=
      Subgroup.mem_subgroupOf.mpr hg
    have h := hZ ⟨g, hgG⟩ hmem
    have h2 : ((frameEndo e hQτ ⟨g, hgG⟩ : adjointGroup τ L) : ModGL τ L) ∈ famZ a :=
      Subgroup.mem_subgroupOf.mp h
    rwa [frameEndo_apply] at h2
  have hstabS : ∀ g ∈ (famS a).map (adjointGroup τ L).subtype,
      frobTwistGL τ L 2 e Q' g ∈ (famS a).map (adjointGroup τ L).subtype := by
    intro g hg
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hg
    exact Subgroup.mem_map.mpr ⟨frameEndo e hQτ s, hS s hs, rfl⟩
  have hlangZ := lang_famZ hBor a he hQfr hp hstabZ
  have hlangS := lang_famS hBor a he hQfr hp hstabS
  constructor
  · intro c hc
    rw [Subgroup.mem_inf] at hc
    have hcZ : (c : ModGL τ L) ∈ famZ a := Subgroup.mem_subgroupOf.mp hc.1
    obtain ⟨z, hz, hzeq⟩ := hlangZ (c : ModGL τ L) hcZ
    have hzG : z ∈ adjointGroup τ L := ((hBor τ L a).1 z hz).1
    refine ⟨⟨z, hzG⟩, Subgroup.mem_subgroupOf.mpr hz, ?_⟩
    apply Subtype.ext
    show (z : ModGL τ L)⁻¹ *
        ((endPow (frameEndo e hQτ) p ⟨z, hzG⟩ : adjointGroup τ L) : ModGL τ L) = (c : ModGL τ L)
    rw [eC6_coe_endPow]
    exact hzeq
  · intro c hc
    rw [Subgroup.mem_inf] at hc
    have hcS : (c : ModGL τ L) ∈ (famS a).map (adjointGroup τ L).subtype :=
      Subgroup.mem_map.mpr ⟨c, hc.2, rfl⟩
    obtain ⟨s, hs, hseq⟩ := hlangS (c : ModGL τ L) hcS
    obtain ⟨s', hs', hs'eq⟩ := Subgroup.mem_map.mp hs
    have hs'eq' : (s' : ModGL τ L) = s := hs'eq
    refine ⟨s', hs', ?_⟩
    apply Subtype.ext
    show (s' : ModGL τ L)⁻¹ *
        ((endPow (frameEndo e hQτ) p s' : adjointGroup τ L) : ModGL τ L) = (c : ModGL τ L)
    rw [eC6_coe_endPow, hs'eq']
    exact hseq

end CFSG.HardMathSupport.C14Exc

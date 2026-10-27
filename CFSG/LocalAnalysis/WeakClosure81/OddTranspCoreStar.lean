module

public import CFSG.ClassicalInvolution.Q3.Q3T8B02W
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreStar

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Cox
open CFSG.Quasithin CFSG.Open Subgroup

theorem natCard_coxeterD4 : Nat.card coxeterD4.Group = 192 := by
  classical
  obtain ⟨θ, ε, -, -, hinj, hw, hsurj, -⟩ :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Wyl4.model (MulEquiv.refl coxeterD4.Group)
  have hrange : Set.range θ =
      ↑(CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Wyl4.eltsT.toFinset) := by
    ext t
    simp only [Set.mem_range, Finset.mem_coe, List.mem_toFinset]
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨w, hw', hq, -⟩ := hw q
      rw [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Wyl4.eltsT_eq, hq]
      exact List.mem_map_of_mem hw'
    · exact hsurj t
  rw [Nat.card_congr (Equiv.ofInjective θ hinj), Nat.card_coe_set_eq, hrange,
    Set.ncard_coe_finset,
    List.toFinset_card_of_nodup CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Wyl4.eltsT_nodup,
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Wyl4.eltsT_eq, List.length_map,
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Wyl4.words_length]

private theorem sym3_key : ∀ t : Equiv.Perm (Fin 3), t ≠ 1 → ∃ u v : Equiv.Perm (Fin 3),
    u * t * u⁻¹ * (v * t * v⁻¹) = Equiv.swap 0 1 * Equiv.swap 1 2 ∨
      u * t * u⁻¹ = Equiv.swap 0 1 * Equiv.swap 1 2 := by
  decide

private theorem isLiftable_sym3 : coxeterD4.IsLiftable
    ![Equiv.swap (1 : Fin 3) 2, Equiv.swap 0 1, Equiv.swap 1 2, Equiv.swap 1 2] := by
  unfold CoxeterMatrix.IsLiftable
  decide

private theorem eq_one_of_mem_of_pow_three {H : Type*} [Group H] {P : Subgroup H}
    (hP : IsPGroup 2 P) {x : H} (hx : x ∈ P) (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3)
    (orderOf_dvd_of_pow_eq_one hk'))

theorem exists_sym3_quot {G : Type*} [Group G] {f : Fin 4 → G} (hR : IsRel MD4 f)
    (hne : f 1 ≠ f 0) :
    ∃ ρ : ↥(closure (Set.range f)) →* Equiv.Perm (Fin 3), Function.Surjective ρ ∧
      (∀ k, ρ k = 1 ↔ (k : G) ∈ pCoreOf 2 (closure (Set.range f))) ∧
      ∀ i, ρ ⟨f i, subset_closure ⟨i, rfl⟩⟩ =
        ![Equiv.swap 1 2, Equiv.swap 0 1, Equiv.swap 1 2, Equiv.swap 1 2] i := by
  classical
  set L := closure (Set.range f) with hL
  let cs : CoxeterSystem coxeterD4 coxeterD4.Group := coxeterD4.toCoxeterSystem
  have hM : ∀ i j, coxeterD4.M i j = MD4 i j := fun i j => by
    fin_cases i <;> fin_cases j <;> rfl
  have hlift : coxeterD4.IsLiftable f :=
    (IsRel.of_eq hM hR).isLiftable (fun i j => by rw [hM]; fin_cases i <;> fin_cases j <;> decide)
  let s : Fin 4 → Equiv.Perm (Fin 3) :=
    ![Equiv.swap 1 2, Equiv.swap 0 1, Equiv.swap 1 2, Equiv.swap 1 2]
  have hls : coxeterD4.IsLiftable s := isLiftable_sym3
  let θ : coxeterD4.Group →* G := cs.lift ⟨f, hlift⟩
  let ρ : coxeterD4.Group →* Equiv.Perm (Fin 3) := cs.lift ⟨s, hls⟩
  have hθs : ∀ i, θ (cs.simple i) = f i := fun i => cs.lift_apply_simple hlift i
  have hρs : ∀ i, ρ (cs.simple i) = s i := fun i => cs.lift_apply_simple hls i
  have hrange : θ.range = L := by
    rw [hL, MonoidHom.range_eq_map, ← cs.subgroup_closure_range_simple, MonoidHom.map_closure,
      ← Set.range_comp]
    congr 1
    ext x
    simp only [Set.mem_range, Function.comp_apply, hθs]
  have hmemL : ∀ w, θ w ∈ L := fun w => by
    rw [← hrange]
    exact ⟨w, rfl⟩
  let θ' : coxeterD4.Group →* L := θ.codRestrict L hmemL
  have hθ'surj : Function.Surjective θ' := by
    rintro ⟨x, hx⟩
    rw [← hrange] at hx
    obtain ⟨w, rfl⟩ := hx
    exact ⟨w, rfl⟩
  have hρsurj : Function.Surjective ρ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff,
      ← Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 2),
      Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨cs.simple 1, by rw [hρs]; rfl⟩
    · exact ⟨cs.simple 0, by rw [hρs]; rfl⟩
  have hN2 : IsPGroup 2 ρ.ker := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := ρ) hρsurj
    rw [natCard_coxeterD4, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 3),
      Fintype.card_fin] at h
    exact IsPGroup.of_card (n := 5) (by norm_num [Nat.factorial] at h ⊢; omega)
  have hKN : θ'.ker ≤ ρ.ker := by
    intro k hk
    have hθk : θ k = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).mp hk)
    rw [MonoidHom.mem_ker]
    by_contra hρk
    obtain ⟨u, v, huv⟩ := sym3_key (ρ k) hρk
    obtain ⟨wu, hwu⟩ := hρsurj u
    obtain ⟨wv, hwv⟩ := hρsurj v
    obtain ⟨k', hθk', hρk'⟩ : ∃ k', θ k' = 1 ∧ ρ k' = Equiv.swap 0 1 * Equiv.swap 1 2 := by
      rcases huv with h | h
      · refine ⟨wu * k * wu⁻¹ * (wv * k * wv⁻¹), by simp [hθk], ?_⟩
        simp only [map_mul, map_inv, hwu, hwv]
        exact h
      · refine ⟨wu * k * wu⁻¹, by simp [hθk], ?_⟩
        simp only [map_mul, map_inv, hwu]
        exact h
    have hρc : ρ (cs.simple 1 * cs.simple 0) = Equiv.swap 0 1 * Equiv.swap 1 2 := by
      rw [map_mul, hρs, hρs]
      rfl
    have hn : k'⁻¹ * (cs.simple 1 * cs.simple 0) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hρk', hρc, inv_mul_cancel]
    have hθc : θ (cs.simple 1 * cs.simple 0) = f 1 * f 0 := by rw [map_mul, hθs, hθs]
    have hmem : f 1 * f 0 ∈ ρ.ker.map θ := by
      refine ⟨_, hn, ?_⟩
      rw [map_mul, map_inv, hθk', inv_one, one_mul, hθc]
    have hb := hR.braid 1 0 (by decide)
    have s0 := hR.sq 0
    have s1 := hR.sq 1
    have hcube : (f 1 * f 0) ^ 3 = 1 := by
      calc (f 1 * f 0) ^ 3 = (f 1 * f 0 * f 1) * (f 0 * f 1 * f 0) := by
            rw [pow_three]
            simp only [mul_assoc]
        _ = (f 0 * f 1 * f 0) * (f 0 * f 1 * f 0) := by rw [hb]
        _ = f 0 * (f 1 * (f 0 * f 0) * f 1) * f 0 := by simp only [mul_assoc]
        _ = 1 := by rw [s0, mul_one, s1, mul_one, s0]
    have h1 : f 1 * f 0 = 1 := eq_one_of_mem_of_pow_three (hN2.map θ) hmem hcube
    apply hne
    calc f 1 = f 1 * (f 0 * f 0) := by rw [s0, mul_one]
      _ = (f 1 * f 0) * f 0 := (mul_assoc _ _ _).symm
      _ = f 0 := by rw [h1, one_mul]
  let ρbar : L →* Equiv.Perm (Fin 3) :=
    MonoidHom.liftOfRightInverse (f := θ') (f_inv := Function.surjInv hθ'surj)
      (Function.rightInverse_surjInv hθ'surj) ⟨ρ, hKN⟩
  have hρbar : ∀ w, ρbar (θ' w) = ρ w := fun w =>
    MonoidHom.liftOfRightInverse_comp_apply (f := θ') (f_inv := Function.surjInv hθ'surj)
      (Function.rightInverse_surjInv hθ'surj) ⟨ρ, hKN⟩ w
  have hρbarsurj : Function.Surjective ρbar := fun t => by
    obtain ⟨w, rfl⟩ := hρsurj t
    exact ⟨θ' w, hρbar w⟩
  refine ⟨ρbar, hρbarsurj, fun k => ?_, fun i => ?_⟩
  · have hmemiff : (k : G) ∈ pCoreOf 2 L ↔ k ∈ CFSG.pCore 2 L :=
      Subgroup.mem_map_iff_mem L.subtype_injective
    rw [hmemiff]
    constructor
    · intro hk
      obtain ⟨w, rfl⟩ := hθ'surj k
      rw [hρbar] at hk
      have hle : ρ.ker.map θ' ≤ CFSG.pCore 2 L := by
        show _ ≤ sSup _
        exact le_sSup ⟨Subgroup.Normal.map (inferInstance : ρ.ker.Normal) θ' hθ'surj, hN2.map θ'⟩
      exact hle ⟨w, hk, rfl⟩
    · intro hk
      by_contra hne1
      have hPn : ((CFSG.pCore 2 L).map ρbar).Normal :=
        Subgroup.Normal.map (CFSG.pCore_normal (p := 2) (G := L)) ρbar hρbarsurj
      have hPp : IsPGroup 2 ((CFSG.pCore 2 L).map ρbar) :=
        (CFSG.pCore_isPGroup (p := 2) (G := L)).map ρbar
      obtain ⟨u, v, huv⟩ := sym3_key (ρbar k) hne1
      have hk' : ρbar k ∈ (CFSG.pCore 2 L).map ρbar := ⟨k, hk, rfl⟩
      have hmem : Equiv.swap 0 1 * Equiv.swap 1 2 ∈ (CFSG.pCore 2 L).map ρbar := by
        rcases huv with h | h
        · rw [← h]
          exact mul_mem (hPn.conj_mem _ hk' u) (hPn.conj_mem _ hk' v)
        · rw [← h]
          exact hPn.conj_mem _ hk' u
      exact absurd (eq_one_of_mem_of_pow_three hPp hmem (by decide)) (by decide)
  · have : (⟨f i, subset_closure ⟨i, rfl⟩⟩ : L) = θ' (cs.simple i) := Subtype.ext (hθs i).symm
    rw [this, hρbar, hρs]

private theorem eq_of_zpowers_eq {G : Type*} [Group G] {a b : G} (hb : b * b = 1) (ha : a ≠ 1)
    (h : zpowers a = zpowers b) : a = b := by
  have hab : a ∈ zpowers b := by
    rw [← h]
    exact mem_zpowers a
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hab
  have hb2 : b ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hb
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · exact absurd (by rw [zpow_mul, hb2, one_zpow]) ha
  · rw [zpow_add, zpow_mul, hb2, one_zpow, one_mul, zpow_one]

private theorem eq_of_conj_fix {G : Type*} [Group G] {t e e' : G} (ht : t * t = 1)
    (he : e * e = 1) (he' : e' * e' = 1) (b : t * e * t = e * t * e)
    (b' : t * e' * t = e' * t * e') (h : (e * e')⁻¹ * t * (e * e') = t) : e = e' := by
  have hinv : (e * e')⁻¹ = e' * e := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right he, inv_eq_of_mul_eq_one_right he']
  rw [hinv] at h
  have h2 : e * t * e = e' * t * e' := by
    calc e * t * e = (e' * e') * (e * t * e) * (e' * e') := by rw [he', one_mul, mul_one]
      _ = e' * (e' * e * t * (e * e')) * e' := by group
      _ = e' * t * e' := by rw [h]
  have h3 : t * e * t = t * e' * t := by rw [b, b', h2]
  calc e = (t * t) * e * (t * t) := by rw [ht, one_mul, mul_one]
    _ = t * (t * e * t) * t := by group
    _ = t * (t * e' * t) * t := by rw [h3]
    _ = (t * t) * e' * (t * t) := by group
    _ = e' := by rw [ht, one_mul, mul_one]

private theorem conjSubgroup_zpowers {G : Type*} [Group G] (t x : G) :
    conjSubgroup (zpowers t) x = zpowers (x⁻¹ * t * x) := by
  unfold conjSubgroup
  rw [MonoidHom.map_zpowers]
  congr 1
  simp

theorem configB_of_star {G : Type*} [Group G] [Finite G] {t e₁ e₂ e₃ : G} (ht : t * t = 1)
    (h₁ : e₁ * e₁ = 1) (h₂ : e₂ * e₂ = 1) (h₃ : e₃ * e₃ = 1)
    (b₁ : t * e₁ * t = e₁ * t * e₁) (b₂ : t * e₂ * t = e₂ * t * e₂)
    (b₃ : t * e₃ * t = e₃ * t * e₃) (c₁₂ : e₁ * e₂ = e₂ * e₁) (c₁₃ : e₁ * e₃ = e₃ * e₁)
    (c₂₃ : e₂ * e₃ = e₃ * e₂) (hne : t ≠ e₁) (n₁₂ : e₁ ≠ e₂) (n₁₃ : e₁ ≠ e₃) (n₂₃ : e₂ ≠ e₃)
    (k₁ : IsConj t e₁) (k₂ : IsConj t e₂) (k₃ : IsConj t e₃) :
    ∃ Lh : Subgroup G, zpowers t ≤ Lh ∧ ¬ zpowers t ≤ pCoreOf 2 Lh ∧
      (⨆ (y : G) (_ : conjSubgroup (zpowers t) y ≤ Lh), conjSubgroup (zpowers t) y) = Lh ∧
      HasQuotShape Lh (pCoreOf 2 Lh : Set G) (fun Y _ => IsSymGp Y 3) ∧
      4 ≤ Set.ncard {W : Subgroup G | ∃ x ∈ pCoreOf 2 Lh, W = conjSubgroup (zpowers t) x} := by
  classical
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hne
    calc (1 : G) = e₁ * e₁ := h₁.symm
      _ = e₁ * 1 * e₁ := by rw [mul_one]
      _ = 1 * e₁ * 1 := b₁.symm
      _ = e₁ := by rw [one_mul, mul_one]
  let f : Fin 4 → G := ![e₁, t, e₂, e₃]
  have hsq : ∀ i, f i * f i = 1 := by
    intro i
    fin_cases i
    · exact h₁
    · exact ht
    · exact h₂
    · exact h₃
  have hcomm : ∀ i j, MD4 i j = 2 → f i * f j = f j * f i := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [MD4, f] at hij ⊢
    all_goals
      first
        | exact c₁₂ | exact c₁₂.symm | exact c₁₃ | exact c₁₃.symm
        | exact c₂₃ | exact c₂₃.symm
  have hbraid : ∀ i j, MD4 i j = 3 → f i * f j * f i = f j * f i * f j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [MD4, f] at hij ⊢
    all_goals
      first
        | exact b₁ | exact b₁.symm | exact b₂ | exact b₂.symm | exact b₃ | exact b₃.symm
  have hR : IsRel MD4 f := ⟨hsq, hcomm, hbraid⟩
  set Lh := closure (Set.range f) with hLh
  obtain ⟨ρ, hρsurj, hker, hval⟩ := exists_sym3_quot hR hne
  have mt : t ∈ Lh := subset_closure ⟨1, rfl⟩
  have m₁ : e₁ ∈ Lh := subset_closure ⟨0, rfl⟩
  have m₂ : e₂ ∈ Lh := subset_closure ⟨2, rfl⟩
  have m₃ : e₃ ∈ Lh := subset_closure ⟨3, rfl⟩
  have vt : ρ ⟨t, mt⟩ = Equiv.swap 0 1 := hval 1
  have v₁ : ρ ⟨e₁, m₁⟩ = Equiv.swap 1 2 := hval 0
  have v₂ : ρ ⟨e₂, m₂⟩ = Equiv.swap 1 2 := hval 2
  have v₃ : ρ ⟨e₃, m₃⟩ = Equiv.swap 1 2 := hval 3
  have hO2 : ∀ {a b : G} (ha : a ∈ Lh) (hb : b ∈ Lh), ρ ⟨a, ha⟩ = Equiv.swap 1 2 →
      ρ ⟨b, hb⟩ = Equiv.swap 1 2 → a * b ∈ pCoreOf 2 Lh := by
    intro a b ha hb hva hvb
    have := (hker (⟨a, ha⟩ * ⟨b, hb⟩)).mp (by rw [map_mul, hva, hvb]; decide)
    simpa using this
  have p₂₃ := hO2 m₂ m₃ v₂ v₃
  have p₁₃ := hO2 m₁ m₃ v₁ v₃
  have p₁₂ := hO2 m₁ m₂ v₁ v₂
  have hconj_sq : ∀ x : G, (x⁻¹ * t * x) * (x⁻¹ * t * x) = 1 := fun x => by
    rw [show (x⁻¹ * t * x) * (x⁻¹ * t * x) = x⁻¹ * (t * t) * x by group, ht, mul_one,
      inv_mul_cancel]
  have hconj_ne : ∀ x : G, x⁻¹ * t * x ≠ 1 := fun x h => ht1 (by
    calc t = x * (x⁻¹ * t * x) * x⁻¹ := by group
      _ = 1 := by rw [h, mul_one, mul_inv_cancel])
  have hfix : ∀ {e e' : G}, e * e = 1 → e' * e' = 1 → t * e * t = e * t * e →
      t * e' * t = e' * t * e' → e ≠ e' → ∀ x y : G, y * x⁻¹ = e * e' →
      conjSubgroup (zpowers t) x ≠ conjSubgroup (zpowers t) y := by
    intro e e' he he' b b' hee' x y hyx hxy
    rw [conjSubgroup_zpowers, conjSubgroup_zpowers] at hxy
    have h := eq_of_zpowers_eq (hconj_sq y) (hconj_ne x) hxy
    apply hee'
    refine eq_of_conj_fix ht he he' b b' ?_
    rw [← hyx]
    calc (y * x⁻¹)⁻¹ * t * (y * x⁻¹) = x * (y⁻¹ * t * y) * x⁻¹ := by group
      _ = x * (x⁻¹ * t * x) * x⁻¹ := by rw [← h]
      _ = t := by group
  have hi₁ : e₁⁻¹ = e₁ := inv_eq_of_mul_eq_one_right h₁
  have hi₂ : e₂⁻¹ = e₂ := inv_eq_of_mul_eq_one_right h₂
  have hi₃ : e₃⁻¹ = e₃ := inv_eq_of_mul_eq_one_right h₃
  refine ⟨Lh, (zpowers_le).mpr mt, fun hle => ?_, ?_, ⟨Equiv.Perm (Fin 3), inferInstance, ρ,
    hρsurj, hker, ⟨MulEquiv.refl _⟩⟩, ?_⟩
  · have := (hker ⟨t, mt⟩).mpr (hle (mem_zpowers t))
    rw [vt] at this
    exact absurd this (by decide)
  · refine le_antisymm (iSup₂_le fun y hy => ?_) ?_
    · exact hy
    refine (closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    have hgen : ∀ x ∈ Lh, IsConj t x → x ∈ ⨆ (y : G) (_ : conjSubgroup (zpowers t) y ≤ Lh),
        conjSubgroup (zpowers t) y := by
      intro x hx hc
      obtain ⟨c, rfl⟩ := isConj_iff.mp hc
      have hW : conjSubgroup (zpowers t) c⁻¹ = zpowers (c * t * c⁻¹) := by
        rw [conjSubgroup_zpowers, inv_inv]
      have hWle : conjSubgroup (zpowers t) c⁻¹ ≤ Lh := by
        rw [hW, zpowers_le]
        exact hx
      refine (le_iSup₂_of_le c⁻¹ hWle le_rfl : conjSubgroup (zpowers t) c⁻¹ ≤ _) ?_
      rw [hW]
      exact mem_zpowers _
    fin_cases i
    · exact hgen _ m₁ k₁
    · exact hgen _ mt (IsConj.refl t)
    · exact hgen _ m₂ k₂
    · exact hgen _ m₃ k₃
  · let Wc : G → Subgroup G := fun x => conjSubgroup (zpowers t) x
    have hsub : ({Wc 1, Wc (e₂ * e₃), Wc (e₁ * e₃), Wc (e₁ * e₂)} : Set (Subgroup G)) ⊆
        {W : Subgroup G | ∃ x ∈ pCoreOf 2 Lh, W = conjSubgroup (zpowers t) x} := by
      intro A hA
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
      rcases hA with rfl | rfl | rfl | rfl
      · exact ⟨1, one_mem _, rfl⟩
      · exact ⟨_, p₂₃, rfl⟩
      · exact ⟨_, p₁₃, rfl⟩
      · exact ⟨_, p₁₂, rfl⟩
    have d1 : Wc 1 ≠ Wc (e₂ * e₃) :=
      hfix h₂ h₃ b₂ b₃ n₂₃ 1 (e₂ * e₃) (by rw [inv_one, mul_one])
    have d2 : Wc 1 ≠ Wc (e₁ * e₃) :=
      hfix h₁ h₃ b₁ b₃ n₁₃ 1 (e₁ * e₃) (by rw [inv_one, mul_one])
    have d3 : Wc 1 ≠ Wc (e₁ * e₂) :=
      hfix h₁ h₂ b₁ b₂ n₁₂ 1 (e₁ * e₂) (by rw [inv_one, mul_one])
    have d4 : Wc (e₂ * e₃) ≠ Wc (e₁ * e₃) := hfix h₁ h₂ b₁ b₂ n₁₂ (e₂ * e₃) (e₁ * e₃) (by
      rw [mul_inv_rev, hi₂, hi₃]
      calc e₁ * e₃ * (e₃ * e₂) = e₁ * (e₃ * e₃) * e₂ := by group
        _ = e₁ * e₂ := by rw [h₃, mul_one])
    have d5 : Wc (e₂ * e₃) ≠ Wc (e₁ * e₂) := hfix h₁ h₃ b₁ b₃ n₁₃ (e₂ * e₃) (e₁ * e₂) (by
      rw [mul_inv_rev, hi₂, hi₃]
      calc e₁ * e₂ * (e₃ * e₂) = e₁ * (e₂ * e₃) * e₂ := by group
        _ = e₁ * (e₃ * e₂) * e₂ := by rw [c₂₃]
        _ = e₁ * e₃ * (e₂ * e₂) := by group
        _ = e₁ * e₃ := by rw [h₂, mul_one])
    have d6 : Wc (e₁ * e₃) ≠ Wc (e₁ * e₂) := hfix h₂ h₃ b₂ b₃ n₂₃ (e₁ * e₃) (e₁ * e₂) (by
      rw [mul_inv_rev, hi₁, hi₃]
      calc e₁ * e₂ * (e₃ * e₁) = e₁ * (e₂ * e₃) * e₁ := by group
        _ = e₁ * (e₃ * e₂) * e₁ := by rw [c₂₃]
        _ = e₁ * e₃ * (e₂ * e₁) := by group
        _ = e₁ * e₃ * (e₁ * e₂) := by rw [c₁₂]
        _ = (e₁ * (e₃ * e₁)) * e₂ := by group
        _ = (e₁ * (e₁ * e₃)) * e₂ := by rw [c₁₃]
        _ = (e₁ * e₁) * e₃ * e₂ := by group
        _ = e₂ * e₃ := by rw [h₁, one_mul, c₂₃])
    have h4 : ({Wc 1, Wc (e₂ * e₃), Wc (e₁ * e₃), Wc (e₁ * e₂)} : Set (Subgroup G)).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem (by simp [d1, d2, d3]),
        Set.ncard_insert_of_notMem (by simp [d4, d5]), Set.ncard_pair d6]
    have hfin : {W : Subgroup G | ∃ x ∈ pCoreOf 2 Lh, W = conjSubgroup (zpowers t) x}.Finite :=
      (Set.finite_range fun x : G => conjSubgroup (zpowers t) x).subset (by
        rintro _ ⟨x, -, rfl⟩
        exact ⟨x, rfl⟩)
    rw [← h4]
    exact Set.ncard_le_ncard hsub hfin

end CFSG.LocalAnalysis.WeakClosure81.CoreStar

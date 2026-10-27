module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec
public import CFSG.Quasithin.Vol2.Asc94.He42SE1
public import CFSG.Quasithin.Vol2.Asc94.He42SE2
public import CFSG.Quasithin.Vol2.Asc94.He42SE3

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

private lemma he42s7_mem_map_iff {Γ Y : Type} [Group Γ] [Group Y] (f : Γ →* Y) {K : Subgroup Γ}
    (hK : f.ker ≤ K) (g : Γ) : f g ∈ K.map f ↔ g ∈ K := by
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq_self hK]

private lemma he42s7_isPGroup_two {Γ : Type} [Group Γ] (P : Subgroup Γ)
    (h : ∀ x ∈ P, x * x = 1) : IsPGroup 2 P := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  have h2 := h _ g.2
  simp [pow_two, h2]

private lemma he42s7_orderOf_two {Γ : Type} [Group Γ] {x : Γ} (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    orderOf x = 2 := by
  have h2 : x ^ 2 = 1 := by rw [pow_two]; exact hx2
  exact orderOf_eq_prime h2 hx1

private lemma he42s7_not_solvable_alt5 : ¬ Group.IsSolvable ↥(alternatingGroup (Fin 5)) := by
  have h5 : 5 ≤ Nat.card (Fin 5) := by simp
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup h5
  haveI : Group.IsPerfect ↥(alternatingGroup (Fin 5)) :=
    Subgroup.isPerfect_iff.2 (commutator_alternatingGroup_eq_self h5)
  exact Group.IsPerfect.not_isSolvable _

private lemma he42s7_not_solvable_of_surj {P Q : Type} [Group P] [Group Q] (θ : P →* Q)
    (hθ : Function.Surjective θ) (ψ : P →* Equiv.Perm (Fin 5)) (hker : θ.ker ≤ ψ.ker)
    (hrange : ψ.range = alternatingGroup (Fin 5)) : ¬ Group.IsSolvable Q := by
  intro hQ
  let e := QuotientGroup.quotientKerEquivOfSurjective θ hθ
  let χ : Q →* Equiv.Perm (Fin 5) :=
    (QuotientGroup.lift θ.ker ψ hker).comp e.symm.toMonoidHom
  have hχ : ∀ x : P, χ (θ x) = ψ x := by
    intro x
    have e1 : e.symm (θ x) = (x : P ⧸ θ.ker) := by
      rw [MulEquiv.symm_apply_eq]; rfl
    show QuotientGroup.lift θ.ker ψ hker (e.symm (θ x)) = ψ x
    rw [e1]; rfl
  have hrχ : χ.range = alternatingGroup (Fin 5) := by
    rw [← hrange]
    apply le_antisymm
    · intro y hy
      obtain ⟨q, rfl⟩ := MonoidHom.mem_range.1 hy
      obtain ⟨x, rfl⟩ := hθ q
      rw [hχ x]
      exact MonoidHom.mem_range.2 ⟨x, rfl⟩
    · intro y hy
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
      exact MonoidHom.mem_range.2 ⟨θ x, hχ x⟩
  let f : Q →* alternatingGroup (Fin 5) :=
    χ.codRestrict (alternatingGroup (Fin 5)) (fun q => by
      rw [← hrχ]; exact MonoidHom.mem_range.2 ⟨q, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨p, hp⟩
    have hp' : p ∈ χ.range := by rw [hrχ]; exact hp
    obtain ⟨q, hq⟩ := MonoidHom.mem_range.1 hp'
    exact ⟨q, Subtype.ext hq⟩
  exact he42s7_not_solvable_alt5 (Group.isSolvable_of_surjective hf)

private lemma he42s7_normal_subgroupOf {Γ : Type} [Group Γ] (M N : Subgroup Γ)
    (hN : ∀ m ∈ M, ∀ n ∈ N, m * n = n * m) : (N.subgroupOf M).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hc : (g : Γ) * (n : Γ) = (n : Γ) * (g : Γ) := hN (g : Γ) g.2 (n : Γ) hn
  have e : (g : Γ) * (n : Γ) * (g : Γ)⁻¹ = (n : Γ) := by
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, e]
  exact hn

private noncomputable def he42s7_quot_mulEquiv {P Q : Type} [Group P] [Group Q] (φ : P →* Q)
    (hφ : Function.Surjective φ) (Z0 : Subgroup P) [Z0.Normal] (hZ0 : φ.ker = Z0) :
    (P ⧸ Z0) ≃* Q :=
  (QuotientGroup.quotientMulEquivOfEq hZ0.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

theorem HeSetup.centralizer_le_L
    (S : HeSetup G) (hB : S.BaseFacts) (hP : S.StepPsi)
    (hmain : Subgroup.center ↥S.L = S.B.subgroupOf S.L ∧
      CFSG.ComponentClassification.AS81.TypeL34
        (CFSG.ComponentClassification.RankTwoStandard.rankTwoQuot S.L))
    {z : G} (hzZ : z ∈ S.Z) (hzB : z ∉ S.B) (hz2 : z * z = 1)
    (hcent : ∀ c : G, (∀ b ∈ S.B, c * b = b * c) → c * z * c⁻¹ * z⁻¹ ∈ S.B → c ∈ S.L) :
    ∀ c : G, (∀ b ∈ S.B, c * b = b * c) → c ∈ S.L := by
  intro c hc
  by_contra hcL
  have hBA : S.B ≤ S.A := hB.B_le_Z.trans hB.Z_le_A
  have hZA : S.Z ≤ S.A := hB.Z_le_A
  have hL1L : S.L1 ≤ S.L := le_sup_left
  have hL2L : S.L2 ≤ S.L := le_sup_right
  have hAL : S.A ≤ S.L := hB.A_le_J.trans (hB.J_le_K.trans (hB.K_le_L1.trans hL1L))
  have hZL : S.Z ≤ S.L := hZA.trans hAL
  have hBL : S.B ≤ S.L := hBA.trans hAL
  obtain ⟨M, hMdef⟩ : ∃ M : Subgroup G, M = Subgroup.centralizer (S.B : Set G) := ⟨_, rfl⟩
  have hmemM : ∀ g : G, g ∈ M ↔ ∀ b ∈ S.B, b * g = g * b := by
    intro g
    rw [hMdef]
    exact Subgroup.mem_centralizer_iff
  have hAM : S.A ≤ M := fun a ha => (hmemM a).2 fun b hb => hB.A_comm b (hBA hb) a ha
  have hZM : S.Z ≤ M := hZA.trans hAM
  have hBM : S.B ≤ M := hBA.trans hAM
  have hL1M : S.L1 ≤ M := fun l hl =>
    (hmemM l).2 fun b hb => Subgroup.mem_centralizer_iff.1 (hB.L1_le_centralizer hl) b hb
  have hL2M : S.L2 ≤ M := fun l hl =>
    (hmemM l).2 fun b hb => Subgroup.mem_centralizer_iff.1 (hB.L2_le_centralizer hl) b hb
  have hLM : S.L ≤ M := sup_le hL1M hL2M
  have hcM : c ∈ M := (hmemM c).2 fun b hb => (hc b hb).symm
  have hzM : z ∈ M := hZM hzZ
  have hBmN : (S.B.subgroupOf M).Normal :=
    he42s7_normal_subgroupOf M S.B (fun m hm n hn => ((hmemM m).1 hm n hn).symm)
  obtain ⟨π, hπ⟩ : ∃ π : ↥M →* (↥M ⧸ S.B.subgroupOf M), π = QuotientGroup.mk' (S.B.subgroupOf M) :=
    ⟨_, rfl⟩
  have hπker : π.ker = S.B.subgroupOf M := by rw [hπ, QuotientGroup.ker_mk']
  have hπapply : ∀ m : ↥M, π m = (m : ↥M ⧸ S.B.subgroupOf M) := by
    intro m
    rw [hπ, QuotientGroup.mk'_apply]
  have hπone : ∀ x : ↥M, π x = 1 ↔ (x : G) ∈ S.B := by
    intro x
    rw [← MonoidHom.mem_ker, hπker, Subgroup.mem_subgroupOf]
  have hπL : π.ker ≤ S.L.subgroupOf M := by
    rw [hπker]
    intro m hm
    exact Subgroup.mem_subgroupOf.2 (hBL (Subgroup.mem_subgroupOf.1 hm))
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup (↥M ⧸ S.B.subgroupOf M), H = (S.L.subgroupOf M).map π :=
    ⟨_, rfl⟩
  have hmemH : ∀ m : ↥M, π m ∈ H ↔ m ∈ S.L.subgroupOf M := by
    intro m
    rw [hHdef]
    exact he42s7_mem_map_iff π hπL m
  have hHne : H ≠ ⊤ := by
    intro htop
    have h1 : π ⟨c, hcM⟩ ∈ H := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hcL (Subgroup.mem_subgroupOf.1 ((hmemH ⟨c, hcM⟩).1 h1))
  obtain ⟨zM, hzMval⟩ : ∃ zM : ↥M, (zM : G) = z := ⟨⟨z, hzM⟩, rfl⟩
  have hzzM : zM * zM = 1 := Subtype.ext (by simp [hzMval, hz2])
  obtain ⟨i, hidef⟩ : ∃ i : ↥M ⧸ S.B.subgroupOf M, i = π zM := ⟨_, rfl⟩
  have hzL : z ∈ S.L := hZL hzZ
  have hiH : i ∈ H := by
    rw [hidef]
    exact (hmemH zM).2 (Subgroup.mem_subgroupOf.2 (by rw [hzMval]; exact hzL))
  have hi2 : i * i = 1 := by
    rw [hidef, ← map_mul, hzzM, map_one]
  have hi1 : i ≠ 1 := by
    intro h
    apply hzB
    have h' : π zM = 1 := by rw [← hidef]; exact h
    have h'' := (hπone zM).1 h'
    rw [hzMval] at h''
    exact h''
  have hφ0 : ∀ x : ↥S.L, π (Subgroup.inclusion hLM x) ∈ H := fun x => by
    rw [hHdef]
    exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hLM x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
  let φ : ↥S.L →* ↥H := (π.comp (Subgroup.inclusion hLM)).codRestrict H hφ0
  have hφsurj : Function.Surjective φ := by
    rintro ⟨h, hh⟩
    rw [hHdef] at hh
    obtain ⟨m, hm, hmh⟩ := Subgroup.mem_map.1 hh
    exact ⟨⟨(m : G), Subgroup.mem_subgroupOf.1 hm⟩, Subtype.ext hmh⟩
  have hφker : φ.ker = Subgroup.center ↥S.L := by
    rw [hmain.1]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : φ x = 1 ↔ π (Subgroup.inclusion hLM x) = 1 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    exact h1.trans (hπone _)
  let eH : (↥S.L ⧸ Subgroup.center ↥S.L) ≃* ↥H :=
    he42s7_quot_mulEquiv φ hφsurj (Subgroup.center ↥S.L) hφker
  have hsimple : IsSimpleGroup ↥H := by
    haveI := CFSG.Quasithin.A94.He42SE.typeL34_isSimpleGroup hmain.2
    exact eH.symm.isSimpleGroup
  have hcls : ∀ j ∈ H, j * j = 1 → j ≠ 1 → ∃ h ∈ H, h * i * h⁻¹ = j := by
    intro j hjH hj2 hj1
    have hii2 : (⟨i, hiH⟩ : ↥H) * ⟨i, hiH⟩ = 1 := Subtype.ext hi2
    have hjj2 : (⟨j, hjH⟩ : ↥H) * ⟨j, hjH⟩ = 1 := Subtype.ext hj2
    have hii1 : (⟨i, hiH⟩ : ↥H) ≠ 1 := fun h => hi1 (congrArg Subtype.val h)
    have hjj1 : (⟨j, hjH⟩ : ↥H) ≠ 1 := fun h => hj1 (congrArg Subtype.val h)
    have hord_i : orderOf (eH.symm ⟨i, hiH⟩) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact he42s7_orderOf_two hii2 hii1
    have hord_j : orderOf (eH.symm ⟨j, hjH⟩) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact he42s7_orderOf_two hjj2 hjj1
    have hconj := MonoidHom.map_isConj eH.toMonoidHom
      (CFSG.Quasithin.A94.He42SE.typeL34_isConj hmain.2 hord_i hord_j)
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hconj
    obtain ⟨g, hg⟩ := isConj_iff.1 hconj
    exact ⟨(g : ↥M ⧸ S.B.subgroupOf M), g.2, by simpa using congrArg Subtype.val hg⟩
  have hcentX : ∀ c' : ↥M ⧸ S.B.subgroupOf M, c' * i = i * c' → c' ∈ H := by
    intro c' hc'
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective c'
    have hcomm : π m * i = i * π m := by
      rw [hπapply]
      exact hc'
    have hkey : π (m * zM * m⁻¹ * zM⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hidef, hcomm, mul_inv_cancel_right, mul_inv_cancel]
    have hmemB : (m : G) * z * (m : G)⁻¹ * z⁻¹ ∈ S.B := by
      have h := (hπone _).1 hkey
      simpa [hzMval] using h
    have hcomB : ∀ b ∈ S.B, (m : G) * b = b * (m : G) :=
      fun b hb => ((hmemM (m : G)).1 m.2 b hb).symm
    have hmL : (m : G) ∈ S.L := hcent (m : G) hcomB hmemB
    rw [← hπapply]
    exact (hmemH m).2 (Subgroup.mem_subgroupOf.2 hmL)
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup (↥M ⧸ S.B.subgroupOf M),
      E = (π.comp (S.Z.subgroupOf M).subtype).range := ⟨_, rfl⟩
  have hEH : E ≤ H := by
    intro e he
    rw [hEdef] at he
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 he
    exact (hmemH (x : ↥M)).2 (Subgroup.mem_subgroupOf.2 (hZL (Subgroup.mem_subgroupOf.1 x.2)))
  have hEsq : ∀ e ∈ E, e * e = 1 := by
    intro e he
    rw [hEdef] at he
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 he
    have hx : (x : ↥M) * (x : ↥M) = 1 :=
      Subtype.ext (hB.A_sq _ (hZA (Subgroup.mem_subgroupOf.1 x.2)))
    show π (x : ↥M) * π (x : ↥M) = 1
    rw [← map_mul, hx, map_one]
  have hZMcard : Nat.card ↥(S.Z.subgroupOf M) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv, hB.card_Z]
  have hBMcard : Nat.card ↥(S.B.subgroupOf M) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv, hB.card_B]
  have hBZM : S.B.subgroupOf M ≤ S.Z.subgroupOf M := Subgroup.subgroupOf_mono M hB.B_le_Z
  have hkerc : Nat.card ↥((S.B.subgroupOf M).subgroupOf (S.Z.subgroupOf M)) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBZM).toEquiv, hBMcard]
  have hker_g : (π.comp (S.Z.subgroupOf M).subtype).ker =
      (S.B.subgroupOf M).subgroupOf (S.Z.subgroupOf M) := by
    ext x
    rw [MonoidHom.mem_ker]
    simp only [Subgroup.mem_subgroupOf]
    exact hπone (x : ↥M)
  have hEcard : Nat.card E = 4 := by
    have h := Subgroup.card_ker_mul_card_range (π.comp (S.Z.subgroupOf M).subtype)
    rw [hker_g, hkerc, hZMcard, ← hEdef] at h
    omega
  obtain ⟨U, hUdef⟩ : ∃ U : Subgroup (↥M ⧸ S.B.subgroupOf M), U = (S.A.subgroupOf M).map π :=
    ⟨_, rfl⟩
  have hUH : U ≤ H := by
    rw [hUdef, hHdef]
    exact Subgroup.map_mono
      (fun x hx => Subgroup.mem_subgroupOf.2 (hAL (Subgroup.mem_subgroupOf.1 hx)))
  have hU2 : IsPGroup 2 U := by
    refine he42s7_isPGroup_two U ?_
    intro u hu
    rw [hUdef] at hu
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hu
    have hx2 : (x : ↥M) * (x : ↥M) = 1 := Subtype.ext (hB.A_sq _ (Subgroup.mem_subgroupOf.1 hx))
    rw [← map_mul, hx2, map_one]
  have hU : U ≠ ⊥ := by
    obtain ⟨a, haA, haB⟩ : ∃ a ∈ S.A, a ∉ S.B := by
      by_contra hcon
      have hle : S.A ≤ S.B := fun a ha => by_contra fun hb => hcon ⟨a, ha, hb⟩
      have h1 := Subgroup.card_le_of_le hle
      rw [hB.card_A, hB.card_B] at h1
      omega
    intro hbot
    have hmem : π ⟨a, hAM haA⟩ ∈ U := by
      rw [hUdef]
      exact Subgroup.mem_map.2 ⟨⟨a, hAM haA⟩, Subgroup.mem_subgroupOf.2 haA, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact haB ((hπone ⟨a, hAM haA⟩).1 hmem)
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup (↥M ⧸ S.B.subgroupOf M), W = (S.L1.subgroupOf M).map π :=
    ⟨_, rfl⟩
  have hWH : W ≤ H := by
    rw [hWdef, hHdef]
    exact Subgroup.map_mono
      (fun x hx => Subgroup.mem_subgroupOf.2 (hL1L (Subgroup.mem_subgroupOf.1 hx)))
  have hLN : S.L1.subgroupOf M ≤ normalizer ((S.A.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    intro l hl
    rw [Subgroup.mem_subgroupOf] at hl
    have hn := Subgroup.mem_normalizer_iff.1 (hB.L1_le_normalizer hl)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hx := hn (x : G)
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hx
  have hWU : W ≤ normalizer (U : Set (↥M ⧸ S.B.subgroupOf M)) := by
    rw [hWdef, hUdef]
    exact (Subgroup.map_mono (f := π) hLN).trans (Subgroup.le_normalizer_map π)
  have hW : ¬ Group.IsSolvable ↥W := by
    have hθ0 : ∀ l : ↥S.L1, π (Subgroup.inclusion hL1M l) ∈ W := fun l => by
      rw [hWdef]
      exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hL1M l, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
    let θ : ↥S.L1 →* ↥W := (π.comp (Subgroup.inclusion hL1M)).codRestrict W hθ0
    have hθsurj : Function.Surjective θ := by
      rintro ⟨w, hw⟩
      rw [hWdef] at hw
      obtain ⟨m, hm, hmw⟩ := Subgroup.mem_map.1 hw
      exact ⟨⟨(m : G), Subgroup.mem_subgroupOf.1 hm⟩, Subtype.ext hmw⟩
    obtain ⟨⟨ψ, hψ⟩, -⟩ := hP
    refine he42s7_not_solvable_of_surj θ hθsurj ψ ?_ hψ.range
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have hl' : π (Subgroup.inclusion hL1M l) = 1 := congrArg Subtype.val hl
    rw [hψ.ker, Subgroup.mem_subgroupOf]
    exact hBA ((hπone (Subgroup.inclusion hL1M l)).1 hl')
  have hSE := CFSG.Quasithin.A94.He42SE.stronglyEmbedded_of_class H i hiH hi2 hi1 hcls hcentX hHne
  exact CFSG.Quasithin.A94.He42SE.false_of_stronglyEmbedded H hSE hsimple E hEH hEcard hEsq U W hU
    hU2 hUH hWH hWU hW

end CFSG.Quasithin.A94.He42

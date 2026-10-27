module

public import CFSG.LocalAnalysis.StandardType.GGQ2A4Conf
public import CFSG.LocalAnalysis.StandardType.GGQTwoThmARel

public section

namespace CFSG.StandardType

open Module QTwoLin

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent

private theorem ggA4B_sum (n m : Fin 4 → ZMod 3) :
    ggA4B n m = ∑ i, n i * ggA4B (Pi.single i 1) m := by
  rw [show ggA4B n m = ∑ i, ∑ j, n i * ggA4C i j * m j from rfl]
  simp only [ggA4B_single, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem ggA4B_neg_left (u n : Fin 4 → ZMod 3) :
    ggA4B (-u) n = -ggA4B u n := by
  simp only [ggA4B, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem dual_κ_apply (K : GGQ2A4Conf V) (φ : Dual (ZMod 3) V) (n : Fin 4 → ZMod 3) :
    φ (K.κ n) = ∑ i, n i * φ (K.c i) := by
  rw [K.κ_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul]

private theorem rootFun_rootVec_eq (K : GGQ2A4Conf V) (γ δ : Fin 10) :
    K.rootFun γ (K.rootVec δ) = ggA4B (ggA4Root γ) (ggA4Root δ) := by
  have h := K.rootFun_κ γ (ggA4Root δ)
  simpa only [GGQ2A4Conf.rootVec] using h

theorem ggQ2A4_refl_coeff (K : GGQ2A4Conf V) (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hTF : TransvectionFree A) (hsA : ∀ i, K.s i ∈ A)
    {c₀ : V} {φ : Dual (ZMod 3) V} (hφ : φ c₀ = 2) (ht : Module.reflection hφ ∈ A)
    (hc₀H : c₀ ∈ K.H) :
    ∃ (ε : ZMod 3) (m : Fin 4 → ZMod 3), (ε = 1 ∨ ε = -1) ∧ c₀ = K.κ m ∧
      ∀ n, φ (K.κ n) = ε * ggA4B m n := by
  classical
  obtain ⟨m, hm⟩ := K.mem_H_iff.mp hc₀H
  subst c₀
  have hm0 : m ≠ 0 := by
    intro h0
    have h2' : (2 : ZMod 3) = 0 := by simpa [h0] using hφ.symm
    exact (by decide : (2 : ZMod 3) ≠ 0) h2'
  have hS : ∃ γ : Fin 10, K.rootFun γ (K.κ m) ≠ 0 := by
    by_contra h
    push Not at h
    have hmzero : m = 0 := by
      apply ggA4_nondeg
      intro i
      have h1 : K.α i (K.κ m) = 0 := by
        have h2' := h (Fin.castLE (by decide) i)
        rwa [K.rootFun_simple] at h2'
      rwa [K.α_κ] at h1
    exact hm0 hmzero
  have hconn : ∀ γ δ, K.rootFun γ (K.κ m) ≠ 0 → K.rootFun δ (K.κ m) ≠ 0 →
      Relation.ReflTransGen (fun γ' δ' => K.rootFun γ' (K.κ m) ≠ 0 ∧
        K.rootFun δ' (K.κ m) ≠ 0 ∧ K.rootFun γ' (K.rootVec δ') ≠ 0) γ δ := by
    intro γ δ hγ hδ
    have hγ' : ggA4B (ggA4Root γ) m ≠ 0 := fun h0 =>
      hγ ((K.rootFun_κ γ m).trans h0)
    have hδ' : ggA4B (ggA4Root δ) m ≠ 0 := fun h0 =>
      hδ ((K.rootFun_κ δ m).trans h0)
    rcases ggA4_conn_check m hm0 γ δ hγ' hδ' with hB | ⟨ζ, hζm, hγζ, hζδ⟩
    · refine Relation.ReflTransGen.single ⟨hγ, hδ, ?_⟩
      intro h0
      exact hB ((rootFun_rootVec_eq K γ δ).symm.trans h0)
    · have hζ : K.rootFun ζ (K.κ m) ≠ 0 := fun h0 =>
        hζm ((K.rootFun_κ ζ m).symm.trans h0)
      have h1 : Relation.ReflTransGen (fun γ' δ' => K.rootFun γ' (K.κ m) ≠ 0 ∧
          K.rootFun δ' (K.κ m) ≠ 0 ∧ K.rootFun γ' (K.rootVec δ') ≠ 0) γ ζ :=
        Relation.ReflTransGen.single ⟨hγ, hζ, fun h0 =>
          hγζ ((rootFun_rootVec_eq K γ ζ).symm.trans h0)⟩
      have h2 : (fun γ' δ' => K.rootFun γ' (K.κ m) ≠ 0 ∧
          K.rootFun δ' (K.κ m) ≠ 0 ∧ K.rootFun γ' (K.rootVec δ') ≠ 0) ζ δ :=
        ⟨hζ, hδ, fun h0 => hζδ ((rootFun_rootVec_eq K ζ δ).symm.trans h0)⟩
      exact h1.tail h2
  obtain ⟨ε, hε, hφε⟩ := refl_coeff_of_pairs (h := K.rootVec) (α := K.rootFun)
    (hα := K.rootFun_rootVec) (d := fun _ => (1 : ZMod 3)) (hd := fun _ => one_ne_zero)
    (hsym := by
      intro γ δ
      simp only [one_mul]
      rw [rootFun_rootVec_eq K γ δ, rootFun_rootVec_eq K δ γ, ggA4B_symm])
    A hTF (fun γ => K.rootRefl_mem hsA γ) hφ ht hS hconn
  have hc : ∀ i : Fin 4, φ (K.c i) = ε * ggA4B (Pi.single i 1) m := by
    intro i
    have h := hφε (Fin.castLE (by decide) i)
    rw [K.rootVec_simple, K.rootFun_simple, K.α_κ, one_mul] at h
    exact h
  refine ⟨ε, m, hε, rfl, ?_⟩
  intro n
  rw [dual_κ_apply]
  calc ∑ i, n i * φ (K.c i)
      = ∑ i, n i * (ε * ggA4B (Pi.single i 1) m) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hc i]
    _ = ε * ∑ i, n i * ggA4B (Pi.single i 1) m := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = ε * ggA4B n m := by rw [← ggA4B_sum]
    _ = ε * ggA4B m n := by rw [ggA4B_symm]

theorem ggQ2A4_refl_eps (K : GGQ2A4Conf V) (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hsA : ∀ i, K.s i ∈ A) (hneg : ∀ r ∈ reflGp A, ¬ ∀ h ∈ K.H, r h = -h)
    {m : Fin 4 → ZMod 3} {φ : Dual (ZMod 3) V} (hφ : φ (K.κ m) = 2)
    (hφH : ∀ n, φ (K.κ n) = -1 * ggA4B m n) : Module.reflection hφ ∉ A := by
  classical
  intro htA
  have hmm : ggA4B m m = 1 := by
    have h := hφH m
    rw [hφ, neg_one_mul] at h
    have h' : -ggA4B m m = 2 := h.symm
    calc ggA4B m m = -(-ggA4B m m) := (neg_neg _).symm
      _ = -2 := by rw [h']
      _ = 1 := by decide
  obtain ⟨w, hwmem, hw⟩ := ggA4_norm_one m hmm
  let W : V ≃ₗ[ZMod 3] V := (w.map K.s).prod
  have hWR : W ∈ reflGp A := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact Subgroup.subset_closure ⟨hsA i, K.s_isRefl i⟩
  have htR : Module.reflection hφ ∈ reflGp A :=
    Subgroup.subset_closure ⟨htA, ⟨K.κ m, φ, hφ, rfl⟩⟩
  let r : V ≃ₗ[ZMod 3] V := (Module.reflection hφ * W) ^ 3
  have hmulR : Module.reflection hφ * W ∈ reflGp A := Subgroup.mul_mem (H := reflGp A) htR hWR
  have hrR : r ∈ reflGp A := Subgroup.pow_mem (K := reflGp A) hmulR 3
  have hstep : ∀ n, (Module.reflection hφ * W) (K.κ n) =
      K.κ (ggA4RAct (-1) m (ggA4WordAct w n)) := by
    intro n
    rw [LinearEquiv.mul_apply]
    dsimp only [W]
    rw [K.word_κ]
    exact K.refl_κ hφ hφH _
  have hr_κ : ∀ n, r (K.κ n) = K.κ (ggA4Cube m w n) := by
    have hpow : ∀ (j : ℕ) (n : Fin 4 → ZMod 3),
        ((Module.reflection hφ * W) ^ j) (K.κ n) =
          K.κ ((fun v => ggA4RAct (-1) m (ggA4WordAct w v))^[j] n) := by
      intro j
      induction j with
      | zero =>
          intro n
          simp
      | succ j ih =>
          intro n
          rw [pow_succ, LinearEquiv.mul_apply, hstep, ih, Function.iterate_succ_apply]
    intro n
    dsimp only [r]
    exact hpow 3 n
  have hc : ∀ k : Fin 4, r (K.c k) = -K.c k := by
    intro k
    calc r (K.c k) = r (K.κ (Pi.single k 1)) := by rw [K.κ_single]
      _ = K.κ (ggA4Cube m w (Pi.single k 1)) := hr_κ _
      _ = K.κ (-Pi.single k 1) := by rw [hw k]
      _ = -K.κ (Pi.single k 1) := map_neg _ _
      _ = -K.c k := by rw [K.κ_single]
  have hspan : ∀ h ∈ Submodule.span (ZMod 3) (Set.range K.c), r h = -h := by
    intro h hh
    exact Submodule.span_induction (p := fun h _ => r h = -h)
      (fun x hx => by
        obtain ⟨k, rfl⟩ := hx
        exact hc k)
      (by simp)
      (fun x y _ _ ihx ihy => by rw [map_add, ihx, ihy]; abel)
      (fun a x _ ih => by rw [map_smul, ih, smul_neg]) hh
  exact hneg r hrR hspan

theorem ggQ2A4_ext_eq (K : GGQ2A4Conf V) (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hTF : TransvectionFree A) {k : Fin 5} {ψ ψ' : Dual (ZMod 3) V}
    (hψ : ψ (K.κ (ggA4F k)) = 2) (hψ' : ψ' (K.κ (ggA4F k)) = 2)
    (h1 : Module.reflection hψ ∈ A) (h2 : Module.reflection hψ' ∈ A) : ψ = ψ' := by
  by_contra hne
  exact hTF _ (Subgroup.mul_mem (H := A) h2 h1)
    (transvection_of_same_centre hψ hψ' hne)

theorem ggQ2A4_ext_all (K : GGQ2A4Conf V) (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hsA : ∀ i, K.s i ∈ A) {k : Fin 5} {ψ : Dual (ZMod 3) V} (hψ : ψ (K.κ (ggA4F k)) = 2)
    (hψH : ∀ n, ψ (K.κ n) = ggA4B (ggA4F k) n) (h : Module.reflection hψ ∈ A) (k' : Fin 5) :
    ∃ (ψ' : Dual (ZMod 3) V) (hψ' : ψ' (K.κ (ggA4F k')) = 2),
      (∀ n, ψ' (K.κ n) = ggA4B (ggA4F k') n) ∧ ψ' K.x = ψ K.x ∧ Module.reflection hψ' ∈ A := by
  classical
  let P : Fin 5 → Prop := fun k' =>
    ∃ (ψ' : Dual (ZMod 3) V) (hψ' : ψ' (K.κ (ggA4F k')) = 2),
      (∀ n, ψ' (K.κ n) = ggA4B (ggA4F k') n) ∧ ψ' K.x = ψ K.x ∧
        Module.reflection hψ' ∈ A
  have hk : P k := ⟨ψ, hψ, hψH, rfl, h⟩
  have hstep : ∀ (i : Fin 4) (k' : Fin 5), P k' → P (ggA4Pi i k') := by
    intro i k' hk'
    obtain ⟨ψ', hψ', hψ'H, hx', hrefl'⟩ := hk'
    let ψ'' : Dual (ZMod 3) V := ψ'.comp (K.s i).toLinearMap
    have hψ''H : ∀ n, ψ'' (K.κ n) = ggA4B (ggA4F (ggA4Pi i k')) n := by
      intro n
      change ψ' (K.s i (K.κ n)) = ggA4B (ggA4F (ggA4Pi i k')) n
      rw [K.s_κ, hψ'H, ggA4_F_swap_B]
    have hψ'' : ψ'' (K.κ (ggA4F (ggA4Pi i k'))) = 2 := by
      rw [hψ''H, ggA4_F_norm]
    have hx'' : ψ'' K.x = ψ K.x := by
      change ψ' (K.s i K.x) = ψ K.x
      rw [K.s_x, hx']
    have hconj : K.s i * Module.reflection hψ' * K.s i = Module.reflection hψ'' := by
      ext v
      simp only [LinearEquiv.mul_apply, Module.reflection_apply]
      rw [map_sub, map_smul, K.s_κ, ggA4_F_swap]
      change K.s i (K.s i v) - ψ' (K.s i v) • K.κ (ggA4F (ggA4Pi i k')) =
        v - ψ' (K.s i v) • K.κ (ggA4F (ggA4Pi i k'))
      rw [show K.s i (K.s i v) = v from Module.involutive_reflection (K.coroot_two i) v]
    refine ⟨ψ'', hψ'', hψ''H, hx'', ?_⟩
    rw [← hconj]
    exact Subgroup.mul_mem (H := A) (Subgroup.mul_mem (H := A) (hsA i) hrefl') (hsA i)
  let S : Finset (Fin 5) := Finset.univ.filter P
  have hkS : k ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hk
  have hSne : S.Nonempty := ⟨k, hkS⟩
  have hclosed : ∀ (i : Fin 4) (k' : Fin 5), k' ∈ S → ggA4Pi i k' ∈ S := by
    intro i k' hk'
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk' ⊢
    exact hstep i k' hk'
  have hk' : k' ∈ S := ggA4_pi_trans S hSne hclosed k'
  simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hk'

theorem ggQ2A4_refl_classify (K : GGQ2A4Conf V) (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hTF : TransvectionFree A) (hsA : ∀ i, K.s i ∈ A)
    (hcen : ∀ (c₀ : V) (φ : Dual (ZMod 3) V) (hφ : φ c₀ = 2), Module.reflection hφ ∈ A → c₀ ∈ K.H)
    (hneg : ∀ r ∈ reflGp A, ¬ ∀ h ∈ K.H, r h = -h)
    {t : V ≃ₗ[ZMod 3] V} (htA : t ∈ A) (ht : IsReflLin (p := 3) t) :
    (∃ γ : Fin 10, t = K.rootRefl γ) ∨
      ∃ (k : Fin 5) (ψ : Dual (ZMod 3) V) (hψ : ψ (K.κ (ggA4F k)) = 2),
        (∀ n, ψ (K.κ n) = ggA4B (ggA4F k) n) ∧ t = Module.reflection hψ := by
  classical
  obtain ⟨c₀, φ, hφ, rfl⟩ := ht
  obtain ⟨ε, m, hε, hc₀, hφH⟩ :=
    ggQ2A4_refl_coeff K A hTF hsA hφ htA (hcen c₀ φ hφ htA)
  subst c₀
  have hε1 : ε = 1 := by
    rcases hε with h1 | hm1
    · exact h1
    · exfalso
      have hφH' : ∀ n, φ (K.κ n) = -1 * ggA4B m n := by
        intro n
        rw [hφH n, hm1]
      exact (ggQ2A4_refl_eps K A hsA hneg hφ hφH') htA
  have hφH1 : ∀ n, φ (K.κ n) = ggA4B m n := by
    intro n
    rw [hφH n, hε1, one_mul]
  have hmm : ggA4B m m = 2 := by
    rw [← hφH1 m]
    exact hφ
  rcases ggA4_norm_two m hmm with ⟨γ, hγ | hγ⟩ | ⟨k, hk | hk⟩
  · subst m
    left
    refine ⟨γ, ?_⟩
    have hφeq : φ = K.rootFun γ := by
      by_contra hne
      exact hTF _ (Subgroup.mul_mem (H := A) (K.rootRefl_mem hsA γ) htA)
        (transvection_of_same_centre hφ (K.rootFun_rootVec γ) hne)
    subst φ
    ext v
    change v - K.rootFun γ v • K.κ (ggA4Root γ) = v - K.rootFun γ v • K.rootVec γ
    rfl
  · subst m
    left
    refine ⟨γ, ?_⟩
    have hκ : K.κ (-ggA4Root γ) = -(K.rootVec γ) := by
      rw [map_neg]
      rfl
    have h' : (-φ) (K.rootVec γ) = 2 := by
      have h := hφ
      rw [hκ, map_neg] at h
      simpa [LinearMap.neg_apply] using h
    have hflip : Module.reflection hφ = Module.reflection h' := by
      ext v
      change v - φ v • K.κ (-ggA4Root γ) = v - (-φ) v • K.rootVec γ
      rw [hκ]
      simp only [LinearMap.neg_apply, smul_neg, neg_smul]
    have heq : -φ = K.rootFun γ := by
      by_contra hne
      exact hTF _ (Subgroup.mul_mem (H := A) (K.rootRefl_mem hsA γ) (by rwa [← hflip]))
        (transvection_of_same_centre h' (K.rootFun_rootVec γ) hne)
    ext v
    change v - φ v • K.κ (-ggA4Root γ) = v - K.rootFun γ v • K.rootVec γ
    rw [hκ, ← heq]
    simp only [LinearMap.neg_apply, smul_neg, neg_smul]
  · subst m
    right
    have hψ : φ (K.κ (ggA4F k)) = 2 :=
      (hφH1 (ggA4F k)).trans (ggA4_F_norm k)
    have hrefl : Module.reflection hφ = Module.reflection hψ := by
      ext v
      change v - φ v • K.κ (ggA4F k) = v - φ v • K.κ (ggA4F k)
      rfl
    exact ⟨k, φ, hψ, hφH1, hrefl⟩
  · subst m
    right
    have hκ : K.κ (-ggA4F k) = -(K.κ (ggA4F k)) := map_neg K.κ _
    have hψ : (-φ) (K.κ (ggA4F k)) = 2 := by
      have h := hφ
      rw [hκ, map_neg] at h
      simpa [LinearMap.neg_apply] using h
    have hψH : ∀ n, (-φ) (K.κ n) = ggA4B (ggA4F k) n := by
      intro n
      rw [LinearMap.neg_apply, hφH1 n, ggA4B_neg_left]
      ring
    have hrefl : Module.reflection hφ = Module.reflection hψ := by
      ext v
      change v - φ v • K.κ (-ggA4F k) = v - (-φ) v • K.κ (ggA4F k)
      rw [hκ]
      simp only [LinearMap.neg_apply, smul_neg, neg_smul]
    exact ⟨k, -φ, hψ, hψH, hrefl⟩

theorem ggQ2A4_refl_fix_of_ext (K : GGQ2A4Conf V) (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hTF : TransvectionFree A) (hsA : ∀ i, K.s i ∈ A)
    (hcen : ∀ (c₀ : V) (φ : Dual (ZMod 3) V) (hφ : φ c₀ = 2), Module.reflection hφ ∈ A → c₀ ∈ K.H)
    (hneg : ∀ r ∈ reflGp A, ¬ ∀ h ∈ K.H, r h = -h)
    {k : Fin 5} {ψ : Dual (ZMod 3) V} (hψ : ψ (K.κ (ggA4F k)) = 2)
    (hψH : ∀ n, ψ (K.κ n) = ggA4B (ggA4F k) n) (hψx : ψ K.x = 0) (h : Module.reflection hψ ∈ A) :
    ∀ t ∈ A, IsReflLin (p := 3) t → t K.x = K.x := by
  intro t htA ht
  rcases ggQ2A4_refl_classify K A hTF hsA hcen hneg htA ht with ⟨γ, rfl⟩ |
    ⟨k', ψ', hψ', -, rfl⟩
  · exact K.rootRefl_x γ
  · obtain ⟨ψ'', hψ'', -, hx'', h''⟩ := ggQ2A4_ext_all K A hsA hψ hψH h k'
    have hψeq : ψ' = ψ'' := ggQ2A4_ext_eq K A hTF hψ' hψ'' htA h''
    rw [Module.reflection_apply, hψeq, hx'', hψx, zero_smul, sub_zero]

end CFSG.StandardType

end

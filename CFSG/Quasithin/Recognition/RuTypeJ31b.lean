module

public import CFSG.Quasithin.Recognition.RuTypeJ26b

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

theorem card_le_mul_of_fiber {α β : Type*} [Finite α] [Finite β] (g : α → β) (n : ℕ)
    (h : ∀ b, Nat.card {a // g a = b} ≤ n) : Nat.card α ≤ Nat.card β * n := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv g), Nat.card_sigma]
  calc ∑ b, Nat.card {a // g a = b} ≤ ∑ _b : β, n := Finset.sum_le_sum fun b _ => h b
    _ = Nat.card β * n := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

theorem card_fiber_le {X Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y) (y : Y) :
    Nat.card {x // f x = y} ≤ Nat.card f.ker := by
  by_cases hne : ∃ x0, f x0 = y
  · obtain ⟨x0, hx0⟩ := hne
    refine Nat.card_le_card_of_injective (fun x => ⟨x0⁻¹ * x.1, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hx0, x.2, inv_mul_cancel]⟩) ?_
    intro a b h
    exact Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
  · have : IsEmpty {x // f x = y} := ⟨fun x => hne ⟨x.1, x.2⟩⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

theorem card_preimage_le {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y] (f : X →* Y)
    (S : Set Y) : Nat.card {x // f x ∈ S} ≤ Nat.card S * Nat.card f.ker := by
  refine card_le_mul_of_fiber (fun x : {x // f x ∈ S} => (⟨f x, x.2⟩ : S)) _ fun s => ?_
  refine (Nat.card_le_card_of_injective
    (fun x => (⟨x.1.1, congrArg Subtype.val x.2⟩ : {x // f x = (s : Y)})) ?_).trans
    (card_fiber_le f s)
  intro a b h
  have h1 := congrArg Subtype.val h
  simp only at h1
  exact Subtype.ext (Subtype.ext h1)

theorem natCard_subtype_eq {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Nat.card {x // p x} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

namespace Sigma

theorem card_inv_sl : Fintype.card {g : SigmaL2F4 // g ^ 2 = 1 ∧ g.right = 1 ∧ g ≠ 1} = 15 := by
  decide +kernel

theorem card_fix_le {x : SigmaL2F4} (hx : x ≠ 1) :
    Nat.card {v : Multiplicative (Fin 2 → F4) //
      sigmaAct x (Multiplicative.toAdd v) = Multiplicative.toAdd v} ≤ 4 := by
  have e : Nat.card {v : Multiplicative (Fin 2 → F4) //
      sigmaAct x (Multiplicative.toAdd v) = Multiplicative.toAdd v} =
        Nat.card {v : Fin 2 → F4 // sigmaAct x v = v} :=
    Nat.card_congr
      { toFun := fun v => ⟨Multiplicative.toAdd v.1, v.2⟩
        invFun := fun v => ⟨Multiplicative.ofAdd v.1, v.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [e, natCard_subtype_eq]
  exact card_fix_le_four hx

end Sigma

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

omit [Finite G] in
theorem φ_ne_one {k : G} (hkH : k ∈ ruH M.T) (hkQ : k ∉ ruQ M.T) : M.φ ⟨k, hkH⟩ ≠ 1 := by
  intro h
  have hk : (⟨k, hkH⟩ : ruH M.T) ∈ M.φ.ker := h
  rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
  exact hkQ hk

theorem card_ker_ψQbar : Nat.card M.ψQbar.ker = 4 := by
  have hsurj : Function.Surjective M.ψQbar := fun y => by
    obtain ⟨q, hq⟩ := M.ψQ_surjective y
    exact ⟨(q : M.Qbar), hq⟩
  have h := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [M.card_Qbar, RuData.card_F4sq] at h
  omega

theorem card_fixQ_le {k : G} (hkH : k ∈ ruH M.T) (hkQ : k ∉ ruQ M.T) :
    Nat.card (M.fixQ hkH) ≤ 16 := by
  set F : Set (Multiplicative (Fin 2 → F4)) :=
    {v | sigmaAct (M.φ ⟨k, hkH⟩) (Multiplicative.toAdd v) = Multiplicative.toAdd v}
  have hF : Nat.card F ≤ 4 := Sigma.card_fix_le (M.φ_ne_one hkH hkQ)
  have hle : Nat.card (M.fixQ hkH) ≤ Nat.card {a : M.Qbar // M.ψQbar a ∈ F} := by
    refine Nat.card_le_card_of_injective (fun a => ⟨a.1, ?_⟩) fun a b h => by
      have h1 := congrArg Subtype.val h
      simp only at h1
      exact Subtype.ext h1
    show sigmaAct (M.φ ⟨k, hkH⟩) (Multiplicative.toAdd (M.ψQbar a.1)) =
      Multiplicative.toAdd (M.ψQbar a.1)
    rw [← M.ψQbar_actQ, (M.mem_fixQ hkH).mp a.2]
  calc Nat.card (M.fixQ hkH) ≤ Nat.card {a : M.Qbar // M.ψQbar a ∈ F} := hle
    _ ≤ Nat.card F * Nat.card M.ψQbar.ker := card_preimage_le _ _
    _ ≤ 4 * 4 := by rw [M.card_ker_ψQbar]; exact Nat.mul_le_mul_right _ hF

theorem card_ker_ψU : Nat.card M.ψU.ker = 2 := by
  rw [M.ψU_ker, card_subgroupOf_of_le M.two.Z_le_U, M.toRuData.card_Z]

theorem card_invFiber_le {k : G} (hkH : k ∈ ruH M.T) (hkQ : k ∉ ruQ M.T) (hk2 : k ^ 2 = 1)
    (a : M.Qbar) : Nat.card (M.invFiber k a) ≤ 8 := by
  by_cases hne : Nonempty (M.invFiber k a)
  · obtain ⟨⟨q, hq2, hqa⟩⟩ := hne
    set F : Set (Multiplicative (Fin 2 → F4)) :=
      {v | sigmaAct (M.φ ⟨k, hkH⟩) (Multiplicative.toAdd v) = Multiplicative.toAdd v}
    have hF : Nat.card F ≤ 4 := Sigma.card_fix_le (M.φ_ne_one hkH hkQ)
    have hW : Nat.card {u : ruU M.L M.T // M.ψU u ∈ F} ≤ 8 :=
      (card_preimage_le M.ψU F).trans (by rw [M.card_ker_ψU]; omega)
    have hk' : k⁻¹ = k := inv_eq_self_of_sq hk2
    have hkk : k * k = 1 := by rw [← pow_two]; exact hk2
    have hkq : k * q * k = (q : G)⁻¹ := by
      have h := hq2
      rw [pow_two] at h
      calc k * q * k = k * q * k * (q * (q : G)⁻¹) := by group
        _ = (k * q * (k * q)) * (q : G)⁻¹ := by group
        _ = (q : G)⁻¹ := by rw [h, one_mul]
    have hmem : ∀ q' : M.invFiber k a, (q : G)⁻¹ * q'.1 ∈ ruU M.L M.T := fun q' =>
      (M.mk_eq_mk_iff).mp (hqa.trans q'.2.2.symm)
    have hfix : ∀ q' : M.invFiber k a,
        M.ψU ⟨(q : G)⁻¹ * q'.1, hmem q'⟩ ∈ F := by
      intro q'
      set u : G := (q : G)⁻¹ * q'.1 with hu
      have huU : u ∈ ruU M.L M.T := hmem q'
      have hq' : (q'.1 : G) = q * u := by rw [hu]; group
      have h2 := q'.2.1
      rw [hq', pow_two] at h2
      have hkqu : k * (q * u) * k = (q * u)⁻¹ := by
        calc k * (q * u) * k = k * (q * u) * k * ((q * u) * (q * u)⁻¹) := by group
          _ = (k * (q * u) * (k * (q * u))) * (q * u)⁻¹ := by group
          _ = (q * u)⁻¹ := by rw [h2, one_mul]
      have hkuk : k * u * k = q * u⁻¹ * (q : G)⁻¹ := by
        have e1 : (k * q * k) * (k * u * k) = k * (q * u) * k := by
          calc (k * q * k) * (k * u * k) = k * q * (k * k) * u * k := by group
            _ = k * (q * u) * k := by rw [hkk]; group
        rw [hkq, hkqu] at e1
        calc k * u * k = q * ((q : G)⁻¹ * (k * u * k)) := by group
          _ = q * (q * u)⁻¹ := by rw [e1]
          _ = q * u⁻¹ * (q : G)⁻¹ := by group
      have hu2 : u⁻¹ = u := inv_eq_self_of_sq (M.U_sq huU)
      have hqu : q * u * (q : G)⁻¹ ∈ ruU M.L M.T := M.conj_mem_U (pCoreOf_le 2 _ q.2) huU
      have hZ : q * u * (q : G)⁻¹ * u ∈ ruZ M.T := by
        have := M.comm_mem_Z q.2 huU
        rwa [hu2] at this
      have hconj : k * u * k⁻¹ ∈ ruU M.L M.T := M.conj_mem_U hkH huU
      have he : M.ψU ⟨k * u * k⁻¹, hconj⟩ = M.ψU ⟨u, huU⟩ := by
        have hw : ((⟨u, huU⟩ : ruU M.L M.T)⁻¹ * ⟨k * u * k⁻¹, hconj⟩ : ruU M.L M.T) ∈
            M.ψU.ker := by
          rw [MonoidHom.mem_ker, M.ψU_eq_one_iff]
          show u⁻¹ * (k * u * k⁻¹) ∈ ruZ M.T
          rw [hk', hkuk, hu2, M.U_comm huU hqu]
          exact hZ
        rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hw
        exact hw.symm
      show sigmaAct (M.φ ⟨k, hkH⟩) (Multiplicative.toAdd (M.ψU ⟨u, huU⟩)) =
        Multiplicative.toAdd (M.ψU ⟨u, huU⟩)
      rw [← M.ψU_conj ⟨k, hkH⟩ ⟨u, huU⟩]
      exact congrArg Multiplicative.toAdd he
    refine (Nat.card_le_card_of_injective
      (fun q' : M.invFiber k a => (⟨⟨(q : G)⁻¹ * q'.1, hmem q'⟩, hfix q'⟩ :
        {u : ruU M.L M.T // M.ψU u ∈ F})) ?_).trans hW
    intro x y h
    have h' : (q : G)⁻¹ * x.1 = (q : G)⁻¹ * y.1 := congrArg (fun w => ((w.1 : ruU M.L M.T) : G)) h
    exact Subtype.ext (Subtype.ext (mul_left_cancel h'))
  · have := not_nonempty_iff.mp hne
    rw [Nat.card_of_isEmpty]
    omega

theorem card_inv_coset_le {k : G} (hkH : k ∈ ruH M.T) (hkQ : k ∉ ruQ M.T) (hk2 : k ^ 2 = 1) :
    Nat.card {q : ruQ M.T // (k * (q : G)) ^ 2 = 1} ≤ 128 := by
  let g : {q : ruQ M.T // (k * (q : G)) ^ 2 = 1} → M.fixQ hkH := fun q =>
    ⟨(q.1 : M.Qbar), M.mk_fixQ hkH hk2 q.2⟩
  have h := card_le_mul_of_fiber g 8 fun a => by
    refine (Nat.card_le_card_of_injective
      (fun q => (⟨q.1.1, q.1.2, congrArg Subtype.val q.2⟩ : M.invFiber k a)) ?_).trans
      (M.card_invFiber_le hkH hkQ hk2 a)
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    simp only at h1
    exact Subtype.ext (Subtype.ext h1)
  calc _ ≤ Nat.card (M.fixQ hkH) * 8 := h
    _ ≤ 16 * 8 := Nat.mul_le_mul_right _ (M.card_fixQ_le hkH hkQ)

theorem card_inv_K_le : Nat.card {x : G // x ∈ M.K ∧ x ∉ ruQ M.T ∧ x ^ 2 = 1} ≤ 15 * 128 := by
  have hKH := M.K_le_H
  let g : {x : G // x ∈ M.K ∧ x ∉ ruQ M.T ∧ x ^ 2 = 1} →
      {A : SigmaL2F4 // A ^ 2 = 1 ∧ A.right = 1 ∧ A ≠ 1} := fun x =>
    ⟨M.φ ⟨x.1, hKH x.2.1⟩, by
      rw [← map_pow]
      have : (⟨x.1, hKH x.2.1⟩ : ruH M.T) ^ 2 = 1 := Subtype.ext (by simpa using x.2.2.2)
      rw [this, map_one], by
      obtain ⟨hk, h1⟩ := M.mem_K_iff.mp x.2.1
      exact h1, M.φ_ne_one (hKH x.2.1) x.2.2.1⟩
  have hfib : ∀ A, Nat.card {x // g x = A} ≤ 128 := by
    intro A
    by_cases hne : Nonempty {x // g x = A}
    · obtain ⟨⟨⟨k, hkK, hkQ, hk2⟩, hkA⟩⟩ := hne
      have hkH : k ∈ ruH M.T := hKH hkK
      have hQ : ∀ x : {x // g x = A}, k⁻¹ * x.1.1 ∈ ruQ M.T := by
        intro x
        have hφ : M.φ ⟨x.1.1, hKH x.1.2.1⟩ = M.φ ⟨k, hkH⟩ :=
          congrArg Subtype.val (x.2.trans hkA.symm)
        have hker : (⟨k, hkH⟩ : ruH M.T)⁻¹ * ⟨x.1.1, hKH x.1.2.1⟩ ∈ M.φ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, inv_mul_cancel]
        rw [M.φ_ker, Subgroup.mem_subgroupOf] at hker
        simpa using hker
      refine (Nat.card_le_card_of_injective (fun x =>
        (⟨⟨k⁻¹ * x.1.1, hQ x⟩, by
          show (k * (k⁻¹ * x.1.1)) ^ 2 = 1
          rw [mul_inv_cancel_left]
          exact x.1.2.2.2⟩ : {q : ruQ M.T // (k * (q : G)) ^ 2 = 1})) ?_).trans
        (M.card_inv_coset_le hkH hkQ hk2)
      intro x y h
      have h' : k⁻¹ * x.1.1 = k⁻¹ * y.1.1 := congrArg (fun w => ((w.1 : ruQ M.T) : G)) h
      exact Subtype.ext (Subtype.ext (mul_left_cancel h'))
    · have := not_nonempty_iff.mp hne
      rw [Nat.card_of_isEmpty]
      omega
  have h := card_le_mul_of_fiber g 128 hfib
  rw [Nat.card_eq_fintype_card (α := {A : SigmaL2F4 // A ^ 2 = 1 ∧ A.right = 1 ∧ A ≠ 1}),
    Sigma.card_inv_sl] at h
  exact h

theorem card_conj_z_H_le : Nat.card {u : G // IsConj M.z u ∧ u * M.z = M.z * u} ≤ 4608 := by
  classical
  have := Fintype.ofFinite G
  have hHK := (M.lemma_J26).2.1
  have hKQ := M.card_inv_K_le
  have hQ := M.toRuData.card_Q
  rw [natCard_subtype_eq] at hHK hKQ ⊢
  have hQ' : (Finset.univ.filter fun x : G => x ∈ ruQ M.T).card = 2 ^ 11 := by
    rw [← natCard_subtype_eq]
    exact hQ
  have hsub : (Finset.univ.filter fun u : G => IsConj M.z u ∧ u * M.z = M.z * u) ⊆
      ((Finset.univ.filter fun x : G => x ∈ ruQ M.T) ∪
        (Finset.univ.filter fun h : G => h ∈ ruH M.T ∧ h ∉ M.K ∧ h ^ 2 = 1)) ∪
        (Finset.univ.filter fun x : G => x ∈ M.K ∧ x ∉ ruQ M.T ∧ x ^ 2 = 1) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨hzu, huz⟩ := hu
    have hu2 : u ^ 2 = 1 := by
      obtain ⟨g, rfl⟩ := isConj_iff.mp hzu
      calc (g * M.z * g⁻¹) ^ 2 = g * M.z ^ 2 * g⁻¹ := by rw [conj_pow]
        _ = 1 := by rw [M.z_sq]; group
    have huH : u ∈ ruH M.T := M.toRuData.mem_H_iff.mpr fun w hw => by
      rcases M.mem_Z_iff.mp hw with rfl | rfl
      · group
      · exact huz.symm
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hQu : u ∈ ruQ M.T
    · exact Or.inl (Or.inl hQu)
    · by_cases hKu : u ∈ M.K
      · exact Or.inr ⟨hKu, hQu, hu2⟩
      · exact Or.inl (Or.inr ⟨huH, hKu, hu2⟩)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 2 ^ 11 + 640 + 15 * 128 := by rw [hQ', hHK]; omega
    _ = 4608 := by norm_num

end RuDataM

end CFSG.Quasithin.RuType

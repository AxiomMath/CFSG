module

public import CFSG.LocalAnalysis.SteinbergCCTransitiveSpreadAlternative
public import CFSG.LocalAnalysis.SteinbergCCOddSuborbitPairing
public import CFSG.LocalAnalysis.SteinbergCCHyperplaneTournament

public section

namespace CFSG.LocalAnalysis

namespace RegularPartition

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem map_eq_self_of_fix {R : Submodule (ZMod 2) V} {h : V ≃ₗ[ZMod 2] V}
    (hR : ∀ r ∈ R, h r = r) : R.map (h : V →ₗ[ZMod 2] V) = R := by
  ext v
  constructor
  · rintro ⟨r, hr, rfl⟩
    change h r ∈ R
    rw [hR r hr]
    exact hr
  · intro hv
    exact ⟨v, hv, hR v hv⟩

theorem exists_smul_eq_of_finrank_eq_one {L : Submodule (ZMod 2) V}
    (hL : Module.finrank (ZMod 2) L = 1) {y : V} (hy : y ∈ L) (hy0 : y ≠ 0) :
    ∀ w ∈ L, ∃ c : ZMod 2, c • y = w := by
  intro w hw
  have hy0' : (⟨y, hy⟩ : L) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨y, hy⟩ : L) hy0').mp hL ⟨w, hw⟩
  exact ⟨c, congrArg Subtype.val hc⟩

theorem le_iff_mem_of_finrank_eq_one {L W : Submodule (ZMod 2) V}
    (hL : Module.finrank (ZMod 2) L = 1) {y : V} (hy : y ∈ L) (hy0 : y ≠ 0) :
    L ≤ W ↔ y ∈ W := by
  refine ⟨fun h => h hy, fun h w hw => ?_⟩
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hL hy hy0 w hw
  exact W.smul_mem c h

theorem eq_of_finrank_eq_one {L : Submodule (ZMod 2) V} (hL : Module.finrank (ZMod 2) L = 1)
    {x y : V} (hx : x ∈ L) (hy : y ∈ L) (hx0 : x ≠ 0) (hy0 : y ≠ 0) : x = y := by
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hL hy hy0 x hx
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx0 (zero_smul _ y)
  have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  rw [key c hc, one_smul]

end RegularPartition

open RegularPartition MulAction in
theorem binary_regular_subspace_family_partition {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (U R : Submodule (ZMod 2) V)
    (hUR : IsCompl U R) (hn : 3 ≤ Module.finrank (ZMod 2) U)
    (hm : 1 ≤ Module.finrank (ZMod 2) R) (Δ : Set (Submodule (ZMod 2) V)) (hRΔ : R ∈ Δ)
    (hdimΔ : ∀ Q ∈ Δ, Module.finrank (ZMod 2) Q = Module.finrank (ZMod 2) R)
    (hdisj : ∀ Q ∈ Δ, ∀ Z ∈ Δ, Q ≠ Z → Q ⊓ Z = ⊥) (h3 : 3 ≤ Δ.ncard)
    (M : Subgroup (V ≃ₗ[ZMod 2] V))
    (hMΔ : ∀ g ∈ M, ∀ Q ∈ Δ, Q.map (g : V →ₗ[ZMod 2] V) ∈ Δ)
    (hMtr : ∀ Q ∈ Δ, ∀ Z ∈ Δ, ∃ g ∈ M, Q.map (g : V →ₗ[ZMod 2] V) = Z)
    (H : Subgroup (V ≃ₗ[ZMod 2] V)) (hHM : H ≤ M)
    (hHnormal : ∀ a ∈ M, R.map (a : V →ₗ[ZMod 2] V) = R → ∀ h ∈ H, a * h * a⁻¹ ∈ H)
    (hHU : ∀ h ∈ H, U.map (h : V →ₗ[ZMod 2] V) = U) (hHR : ∀ h ∈ H, ∀ r ∈ R, h r = r)
    (hreg : ∀ u ∈ U, ∀ v ∈ U, u ≠ 0 → v ≠ 0 → ∃! h, h ∈ H ∧ h u = v) :
    (∀ g ∈ M, U.map (g : V →ₗ[ZMod 2] V) = U) ∧
      Δ.ncard = 2 ^ Module.finrank (ZMod 2) U ∧
      (∀ Q ∈ Δ, ∀ v ∈ Q, v ≠ 0 → v ∉ U) ∧ (∀ v : V, v ∉ U → ∃! Q, Q ∈ Δ ∧ v ∈ Q) ∧
      (∀ h ∈ H, ∀ Q ∈ Δ \ {R}, Q.map (h : V →ₗ[ZMod 2] V) ∈ Δ \ {R}) ∧
      (∀ Q ∈ Δ \ {R}, ∀ Z ∈ Δ \ {R}, ∃! h, h ∈ H ∧ Q.map (h : V →ₗ[ZMod 2] V) = Z) ∧
      (∀ Q₁ ∈ Δ, ∀ Q₂ ∈ Δ, ∀ Z₁ ∈ Δ, ∀ Z₂ ∈ Δ, Q₁ ≠ Q₂ → Z₁ ≠ Z₂ →
        ∃ g ∈ M, Q₁.map (g : V →ₗ[ZMod 2] V) = Z₁ ∧ Q₂.map (g : V →ₗ[ZMod 2] V) = Z₂) := by
  classical
  have hVfin : Finite V := Module.finite_of_finite (ZMod 2)
  have hSfin : Finite (Submodule (ZMod 2) V) :=
    Finite.of_injective (fun Q : Submodule (ZMod 2) V => (Q : Set V)) SetLike.coe_injective
  obtain ⟨-, -, hMRU, hgR, hwd, hcompl, -⟩ := binary_regular_complement_stabilizer_covariance
    U R hUR hn M Δ hRΔ hMtr H hHnormal hHU hHR hreg
  have hspread := binary_transitive_disjoint_subspace_spread_alternative U R hUR hn hm Δ hRΔ
    hdimΔ hdisj h3 M hMΔ hMtr H hHM hHU hHR hreg
  dsimp only at hspread
  obtain ⟨⟨hAcard, hHA, hHAreg, hAnz, hApart⟩, halt⟩ := hspread
  set A := {Q ∈ Δ | Q ⊓ U = ⊥} with hA
  set B := {Q ∈ Δ | Q ≤ U} with hB
  have hHRmap : ∀ h ∈ H, R.map (h : V →ₗ[ZMod 2] V) = R := fun h hh =>
    map_eq_self_of_fix (hHR h hh)
  have hR0 : R ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hm
    omega
  have hRA : R ∈ A := ⟨hRΔ, hUR.symm.inf_eq_bot⟩
  have hΔA : Δ = A := by
    rcases halt with ⟨-, h⟩ | ⟨hBne, hBtr, hBcard, hBodd, -, hpart, hΔcard, hΔodd⟩
    · exact h
    exfalso
    let act : MulAction M Δ :=
      { smul := fun g Q => ⟨(Q : Submodule (ZMod 2) V).map
          ((g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V), hMΔ g g.2 Q Q.2⟩
        one_smul := fun Q => Subtype.ext (submodule_map_linearEquiv_one (Q : Submodule (ZMod 2) V))
        mul_smul := fun g h Q => Subtype.ext
          (submodule_map_linearEquiv_mul (g : V ≃ₗ[ZMod 2] V) h Q) }
    have hsmul : ∀ (g : M) (Q : Δ), ((g • Q : Δ) : Submodule (ZMod 2) V) =
        (Q : Submodule (ZMod 2) V).map ((g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) := fun _ _ => rfl
    have htr : IsPretransitive M Δ := ⟨fun Q Z => by
      obtain ⟨g, hg, hgQ⟩ := hMtr Q Q.2 Z Z.2
      exact ⟨⟨g, hg⟩, Subtype.ext hgQ⟩⟩
    have hN : Odd (Nat.card Δ) := by rw [Nat.card_coe_set_eq]; exact hΔodd
    set α : Δ := ⟨R, hRΔ⟩ with hα
    have hstab : ∀ a : M, a ∈ stabilizer M α ↔ R.map ((a : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = R :=
      fun a => ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hAB : Disjoint A B := by
      rw [Set.disjoint_left]
      rintro Q ⟨hQΔ, hQA⟩ ⟨-, hQB⟩
      have h1 : Q = ⊥ := by rw [← hQA, inf_eq_left.mpr hQB]
      have h2 := hdimΔ Q hQΔ
      rw [h1, finrank_bot] at h2
      omega
    have hΔAB : A ∪ B = Δ := by
      refine Set.eq_of_subset_of_ncard_le (Set.union_subset (fun Q hQ => hQ.1)
        (fun Q hQ => hQ.1)) ?_ (Set.toFinite _)
      rw [Set.ncard_union_eq hAB (Set.toFinite _) (Set.toFinite _), hAcard, hΔcard]
    set S : Set Δ := Subtype.val ⁻¹' B with hS
    set T : Set Δ := Subtype.val ⁻¹' (A \ {R}) with hT
    have hSB : S.ncard = B.ncard := Set.ncard_preimage_of_injective_subset_range
      Subtype.val_injective (fun Q hQ => ⟨⟨Q, hQ.1⟩, rfl⟩)
    have hTA : T.ncard = A.ncard - 1 := by
      rw [hT, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
        (fun Q hQ => ⟨⟨Q, hQ.1.1⟩, rfl⟩), Set.ncard_sdiff_singleton_of_mem hRA]
    obtain ⟨β₀, hβ₀B⟩ := hBne
    have hβ₀R : β₀ ≠ R := by
      intro h
      apply hR0
      rw [← hUR.symm.inf_eq_bot, inf_eq_left.mpr (h ▸ hβ₀B.2)]
    obtain ⟨γ₀, hγ₀A, hγ₀R⟩ : ∃ γ ∈ A, γ ≠ R := by
      by_contra hcon
      push Not at hcon
      have hsub : A ⊆ {R} := fun Q hQ => hcon Q hQ
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_singleton, hAcard] at h1
      have h2 : 2 ≤ 2 ^ Module.finrank (ZMod 2) U :=
        le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ _))
      omega
    have hstabB : ∀ a : M, a ∈ stabilizer M α → ∀ Q ∈ B,
        Q.map ((a : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) ∈ B := by
      intro a ha Q hQ
      refine ⟨hMΔ a a.2 Q hQ.1, ?_⟩
      rw [← hMRU a a.2 ((hstab a).mp ha)]
      exact Submodule.map_mono hQ.2
    have hstabA : ∀ a : M, a ∈ stabilizer M α → ∀ Q ∈ A \ {R},
        Q.map ((a : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) ∈ A \ {R} := by
      intro a ha Q hQ
      have haR := (hstab a).mp ha
      refine ⟨⟨hMΔ a a.2 Q hQ.1.1, ?_⟩, fun h => hQ.2 ?_⟩
      · rw [← hMRU a a.2 haR, ← Submodule.map_inf _ (a : V ≃ₗ[ZMod 2] V).injective, hQ.1.2,
          Submodule.map_bot]
      · rw [Set.mem_singleton_iff] at h ⊢
        rw [← haR] at h
        exact Submodule.map_injective_of_injective (a : V ≃ₗ[ZMod 2] V).injective h
    have hHstab : ∀ h (hh : h ∈ H), (⟨h, hHM hh⟩ : M) ∈ stabilizer M α := fun h hh =>
      (hstab _).mpr (hHRmap h hh)
    have hSorbit : orbit (stabilizer M α) (⟨β₀, hβ₀B.1⟩ : Δ) = S := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        exact hstabB a a.2 β₀ hβ₀B
      · intro hx
        obtain ⟨h, hh, hhx⟩ := hBtr β₀ hβ₀B x hx
        exact ⟨⟨⟨h, hHM hh⟩, hHstab h hh⟩, Subtype.ext hhx⟩
    have hTorbit : orbit (stabilizer M α) (⟨γ₀, hγ₀A.1⟩ : Δ) = T := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        exact hstabA a a.2 γ₀ ⟨hγ₀A, hγ₀R⟩
      · intro hx
        obtain ⟨h, ⟨hh, hhx⟩, -⟩ := hHAreg γ₀ ⟨hγ₀A, hγ₀R⟩ x hx
        exact ⟨⟨⟨h, hHM hh⟩, hHstab h hh⟩, Subtype.ext hhx⟩
    have hβ₀S : (⟨β₀, hβ₀B.1⟩ : Δ) ∈ S := hβ₀B
    have hγ₀T : (⟨γ₀, hγ₀A.1⟩ : Δ) ∈ T := ⟨hγ₀A, hγ₀R⟩
    have hβ₀α : (⟨β₀, hβ₀B.1⟩ : Δ) ≠ α := fun h => hβ₀R (congrArg Subtype.val h)
    have hγ₀α : (⟨γ₀, hγ₀A.1⟩ : Δ) ≠ α := fun h => hγ₀R (congrArg Subtype.val h)
    have hST : S ≠ T := by
      intro h
      have : (⟨β₀, hβ₀B.1⟩ : Δ) ∈ T := h ▸ hβ₀S
      exact Set.disjoint_left.mp hAB this.1 hβ₀B
    have hcover : ∀ x : Δ, x ≠ α → x ∈ S ∨ x ∈ T := by
      intro x hx
      have hxR : (x : Submodule (ZMod 2) V) ≠ R := fun h => hx (Subtype.ext h)
      have hxΔ : (x : Submodule (ZMod 2) V) ∈ A ∪ B := by
        rw [hΔAB]
        exact x.2
      rcases hxΔ with h | h
      · exact Or.inr ⟨h, hxR⟩
      · exact Or.inl h
    obtain ⟨-, -, hcardST, hpair⟩ := odd_degree_two_suborbit_pairing hN α S T
      ⟨_, hβ₀α, hSorbit⟩ ⟨_, hγ₀α, hTorbit⟩ hST hcover (by rw [hSB]; exact hBodd)
    have hBq : B.ncard = 2 ^ Module.finrank (ZMod 2) U - 1 := by
      rw [← hSB, hcardST, hTA, hAcard]
    have hq8 : 8 ≤ 2 ^ Module.finrank (ZMod 2) U :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
    have hm1 : Module.finrank (ZMod 2) R = 1 := by
      by_contra hne
      have h2 : 2 ≤ Module.finrank (ZMod 2) R := by omega
      have h4 : 4 ≤ 2 ^ Module.finrank (ZMod 2) R :=
        le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h2)
      have h5 : (2 ^ Module.finrank (ZMod 2) U - 1) / (2 ^ Module.finrank (ZMod 2) R - 1) ≤
          (2 ^ Module.finrank (ZMod 2) U - 1) / 3 := Nat.div_le_div_left (by omega) (by norm_num)
      have h6 : (2 ^ Module.finrank (ZMod 2) U - 1) / 3 < 2 ^ Module.finrank (ZMod 2) U - 1 :=
        Nat.div_lt_self (by omega) (by norm_num)
      omega
    choose! gof hgofM hgofR using hgR
    have horb : ∀ x y : Δ, (x, y) ∈ orbit M (α, (⟨β₀, hβ₀B.1⟩ : Δ)) ↔
        (y : Submodule (ZMod 2) V) ≤ U.map (gof x : V →ₗ[ZMod 2] V) := by
      intro x y
      constructor
      · rintro ⟨g, hg⟩
        have hgx : R.map ((g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = x :=
          congrArg Subtype.val (congrArg Prod.fst hg)
        have hgy : β₀.map ((g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = y :=
          congrArg Subtype.val (congrArg Prod.snd hg)
        rw [← hgy, ← hwd g g.2 (gof x) (hgofM x x.2) (hgx.trans (hgofR x x.2).symm)]
        exact Submodule.map_mono hβ₀B.2
      · intro hy
        set g : M := ⟨gof x, hgofM x x.2⟩ with hg
        have hgx : g • α = x := Subtype.ext (hgofR x x.2)
        have hyS : g⁻¹ • y ∈ S := by
          refine ⟨(g⁻¹ • y).2, ?_⟩
          change (y : Submodule (ZMod 2) V).map
            (((g⁻¹ : M) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) ≤ U
          calc (y : Submodule (ZMod 2) V).map (((g⁻¹ : M) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)
              ≤ (U.map (gof x : V →ₗ[ZMod 2] V)).map
                (((g⁻¹ : M) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) := Submodule.map_mono hy
            _ = U := by
              rw [← submodule_map_linearEquiv_mul]
              change U.map (((g⁻¹ * g : M) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = U
              rw [inv_mul_cancel]
              exact submodule_map_linearEquiv_one U
        rw [← hSorbit] at hyS
        obtain ⟨a, ha⟩ := hyS
        refine ⟨g * a, ?_⟩
        change (g * (a : M)) • (α, (⟨β₀, hβ₀B.1⟩ : Δ)) = (x, y)
        rw [mul_smul, Prod.smul_mk, Prod.smul_mk, mem_stabilizer_iff.mp a.2, hgx]
        have ha' : (a : M) • (⟨β₀, hβ₀B.1⟩ : Δ) = g⁻¹ • y := ha
        rw [ha', smul_inv_smul]
    obtain ⟨-, -, hxor⟩ := hpair _ hβ₀S _ hγ₀T
    have hpart' : ∀ v : V, v ≠ 0 → ∃ Q, Q ∈ Δ ∧ v ∈ Q := fun v hv => (hpart v hv).exists
    choose! L hLΔ hLmem using hpart'
    have hLdim : ∀ v : V, v ≠ 0 → Module.finrank (ZMod 2) (L v) = 1 := fun v hv =>
      (hdimΔ _ (hLΔ v hv)).trans hm1
    let Uh : V → Submodule (ZMod 2) V := fun v => U.map (gof (L v) : V →ₗ[ZMod 2] V)
    have hUh : ∀ v (hv : v ≠ 0), Uh v = U.map (gof (⟨L v, hLΔ v hv⟩ : Δ) : V →ₗ[ZMod 2] V) :=
      fun _ _ => rfl
    have hhyp : ∀ x : V, x ≠ 0 → Module.finrank (ZMod 2) (V ⧸ Uh x) = 1 := by
      intro x hx
      have hc := hcompl _ (hgofM _ (hLΔ x hx))
      rw [hgofR _ (hLΔ x hx)] at hc
      have h1 := Submodule.finrank_add_eq_of_isCompl hc
      have h2 := Submodule.finrank_quotient_add_finrank (U.map (gof (L x) : V →ₗ[ZMod 2] V))
      rw [hUh x hx]
      change Module.finrank (ZMod 2) (V ⧸ U.map (gof (L x) : V →ₗ[ZMod 2] V)) = 1
      rw [hLdim x hx] at h1
      omega
    have hxor' : ∀ x y : V, x ≠ 0 → y ≠ 0 → x ≠ y → Xor (y ∈ Uh x) (x ∈ Uh y) := by
      intro x y hx hy hxy
      have hne : (⟨L x, hLΔ x hx⟩ : Δ) ≠ ⟨L y, hLΔ y hy⟩ := by
        intro h
        have h1 : L x = L y := congrArg Subtype.val h
        exact hxy (eq_of_finrank_eq_one (hLdim y hy) (h1 ▸ hLmem x hx) (hLmem y hy) hx hy)
      have h := hxor _ _ hne
      rw [horb, horb] at h
      change Xor (L y ≤ _) (L x ≤ _) at h
      rw [le_iff_mem_of_finrank_eq_one (hLdim y hy) (hLmem y hy) hy,
        le_iff_mem_of_finrank_eq_one (hLdim x hx) (hLmem x hx) hx] at h
      rw [hUh x hx, hUh y hy]
      exact h
    have hdim := binary_hyperplane_tournament_dimension_obstruction Uh hhyp hxor'
    have hVdim := Submodule.finrank_add_eq_of_isCompl hUR
    omega
  rw [← hΔA] at hAcard hHA hHAreg hAnz hApart
  have hpartU : ∀ Q ∈ Δ, ∀ v ∈ Q, v ≠ 0 → v ∉ U := fun Q hQ => (hAnz Q hQ).2
  refine ⟨?_, hAcard, hpartU, hApart, fun h hh Q hQ => ?_, hHAreg, ?_⟩
  ·
    have hle : ∀ g ∈ M, U.map (g : V →ₗ[ZMod 2] V) ≤ U := by
      rintro g hg _ ⟨u, hu, rfl⟩
      by_contra hgu
      obtain ⟨Q, ⟨hQΔ, hguQ⟩, -⟩ := hApart _ hgu
      have hu0 : u ≠ 0 := by
        rintro rfl
        exact hgu (by simp)
      have huQ : u ∈ Q.map ((g⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) :=
        ⟨g u, hguQ, by simp⟩
      exact hpartU _ (hMΔ _ (M.inv_mem hg) Q hQΔ) u huQ hu0 hu
    intro g hg
    refine le_antisymm (hle g hg) fun u hu => ⟨g⁻¹ u, hle _ (M.inv_mem hg) ⟨u, hu, rfl⟩, ?_⟩
    simp
  · exact hHA h hh Q hQ
  ·
    intro Q₁ hQ₁ Q₂ hQ₂ Z₁ hZ₁ Z₂ hZ₂ hQ hZ
    obtain ⟨g₁, hg₁M, hg₁⟩ := hMtr Q₁ hQ₁ R hRΔ
    obtain ⟨g₂, hg₂M, hg₂⟩ := hMtr Z₁ hZ₁ R hRΔ
    have hne : ∀ g : V ≃ₗ[ZMod 2] V, ∀ X Y : Submodule (ZMod 2) V, X ≠ Y →
        X.map (g : V →ₗ[ZMod 2] V) ≠ Y.map (g : V →ₗ[ZMod 2] V) := fun g X Y hXY h =>
      hXY (Submodule.map_injective_of_injective g.injective h)
    have h1 : Q₂.map (g₁ : V →ₗ[ZMod 2] V) ∈ Δ \ {R} :=
      ⟨hMΔ g₁ hg₁M Q₂ hQ₂, fun h => hne g₁ _ _ hQ (hg₁.trans (Set.mem_singleton_iff.mp h).symm)⟩
    have h2 : Z₂.map (g₂ : V →ₗ[ZMod 2] V) ∈ Δ \ {R} :=
      ⟨hMΔ g₂ hg₂M Z₂ hZ₂, fun h => hne g₂ _ _ hZ (hg₂.trans (Set.mem_singleton_iff.mp h).symm)⟩
    obtain ⟨h, ⟨hh, hhQ⟩, -⟩ := hHAreg _ h1 _ h2
    refine ⟨g₂⁻¹ * h * g₁, M.mul_mem (M.mul_mem (M.inv_mem hg₂M) (hHM hh)) hg₁M, ?_, ?_⟩
    · rw [submodule_map_linearEquiv_mul, submodule_map_linearEquiv_mul, hg₁, hHRmap h hh, ← hg₂,
        ← submodule_map_linearEquiv_mul, inv_mul_cancel, submodule_map_linearEquiv_one]
    · rw [submodule_map_linearEquiv_mul, submodule_map_linearEquiv_mul, hhQ,
        ← submodule_map_linearEquiv_mul, inv_mul_cancel, submodule_map_linearEquiv_one]

end CFSG.LocalAnalysis

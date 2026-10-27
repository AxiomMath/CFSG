module

public import CFSG.Quasithin.Vol2.Ch3n317KerGrp
public import CFSG.Quasithin.Vol2.Ch3n317KerMod

public section

open Equiv

namespace CFSG.Quasithin.Ch3n317Ker

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.Ch3n317A5

theorem isSwap_iff : ∀ σ : Perm (Fin 5),
    (∃ x y : Fin 5, x ≠ y ∧ σ = swap x y) ↔ σ * σ = 1 ∧ Perm.sign σ = -1 := by
  decide +kernel

theorem isSwap_map (ψ : Perm (Fin 5) ≃* Perm (Fin 5)) (σ : Perm (Fin 5)) :
    (ψ σ).IsSwap ↔ σ.IsSwap := by
  have hsign : Perm.sign.comp ψ.toMonoidHom = Perm.sign :=
    Perm.eq_sign_of_surjective_hom fun u => by
      obtain ⟨τ, hτ⟩ := Perm.sign_surjective (Fin 5) u
      exact ⟨ψ.symm τ, by simp [hτ]⟩
  have hs : Perm.sign (ψ σ) = Perm.sign σ := by
    have := congrArg (fun f : Perm (Fin 5) →* ℤˣ => f σ) hsign
    simpa using this
  have hsq : ψ σ * ψ σ = 1 ↔ σ * σ = 1 := by
    rw [← map_mul, map_eq_one_iff ψ ψ.injective]
  show (∃ x y : Fin 5, x ≠ y ∧ ψ σ = swap x y) ↔ (∃ x y : Fin 5, x ≠ y ∧ σ = swap x y)
  rw [isSwap_iff, isSwap_iff, hsq, hs]

theorem fourSet_mul : ∀ a b c d : Fin 5, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    (1 : Perm (Fin 5)) ∈ fourSet a b c d ∧
      ∀ σ ∈ fourSet a b c d, ∀ τ ∈ fourSet a b c d, σ * τ ∈ fourSet a b c d := by
  decide +kernel

@[expose] def fourSub (a b c d : Fin 5)
    (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) : Subgroup (Perm (Fin 5)) where
  carrier := fourSet a b c d
  one_mem' := (fourSet_mul a b c d h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2).1
  mul_mem' := fun {σ τ} hσ hτ =>
    (fourSet_mul a b c d h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2).2 σ hσ τ hτ
  inv_mem' := fun {σ} hσ => by
    have h1 := (fourSet_facts a b c d h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
      h.2.2.2.2.2).2.2.1 σ hσ
    change σ⁻¹ ∈ fourSet a b c d
    rw [inv_eq_of_mul_eq_one_right h1]
    exact hσ

section Comp

variable {W : Type*} [CommGroup W] [Finite W]

theorem a5Comp_of {L X R : Subgroup (MulAut W)} (hL : E2.IsA5Module L)
    (h4 : Nat.card ↥(L ⊓ X) = 4) (θ' : ↥L ≃* Perm (Fin 5))
    (hθ' : L ⊓ X = Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ R ∧ (θ' ⟨x, hx⟩).IsSwap}) :
    A5Comp L (L ⊓ X) := by
  classical
  obtain ⟨θ, β, hβ⟩ := hL
  have hsw : {x | ∃ hx : x ∈ L, x ∈ R ∧ (θ' ⟨x, hx⟩).IsSwap} =
      {x | ∃ hx : x ∈ L, x ∈ R ∧ (θ ⟨x, hx⟩).IsSwap} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    have e : ∀ hx : x ∈ L, θ' ⟨x, hx⟩ = (θ.symm.trans θ') (θ ⟨x, hx⟩) := fun hx => by simp
    constructor
    · rintro ⟨hx, hxR, hs⟩
      exact ⟨hx, hxR, (isSwap_map (θ.symm.trans θ') _).mp (e hx ▸ hs)⟩
    · rintro ⟨hx, hxR, hs⟩
      exact ⟨hx, hxR, (e hx).symm ▸ (isSwap_map (θ.symm.trans θ') _).mpr hs⟩
  rw [hsw] at hθ'
  have hcl4 : Nat.card ↥(Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ R ∧ (θ ⟨x, hx⟩).IsSwap}) = 4 := by
    rw [← hθ']
    exact h4
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs₁, hs₂⟩ := exists_two_swaps hcl4
  have hd : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := ⟨hab, hac, had, hbc, hbd, hcd⟩
  set φ : Perm (Fin 5) →* MulAut W := L.subtype.comp θ.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := L.subtype_injective.comp θ.symm.injective
  have hφelt : ∀ σ, φ σ = elt L θ σ := fun σ => rfl
  set Q := (fourSub a b c d hd).map φ with hQ
  have hQX : Q ≤ L ⊓ X := by
    rintro _ ⟨σ, hσ, rfl⟩
    rw [hθ', hφelt]
    change σ ∈ fourSet a b c d at hσ
    simp only [fourSet, Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with rfl | rfl | rfl | rfl
    · rw [show elt L θ 1 = 1 by simp [elt]]
      exact Subgroup.one_mem _
    · exact hs₁
    · exact hs₂
    · rw [elt_mul]
      exact Subgroup.mul_mem _ hs₁ hs₂
  have hQ4 : Nat.card Q = 4 := by
    rw [hQ, Subgroup.card_map_of_injective hφinj]
    change Nat.card ↥(fourSet a b c d : Set (Perm (Fin 5))) = 4
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    exact (fourSet_facts a b c d hab hac had hbc hbd hcd).1
  have hQe : Q = L ⊓ X := Subgroup.eq_of_le_of_card_ge hQX (by rw [h4, hQ4])
  refine ⟨θ, β, hβ, a, b, c, d, hab, hac, had, hbc, hbd, hcd, fun x => ?_⟩
  rw [← hQe]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨(θ.symm σ).2, ?_⟩
    have e : θ ⟨φ σ, (θ.symm σ).2⟩ = σ := by simp [hφ]
    rw [e]
    exact hσ
  · rintro ⟨hx, hσ⟩
    refine ⟨θ ⟨x, hx⟩, hσ, ?_⟩
    simp [hφ]

omit [Finite W] in
theorem mul_self_mem_oTwoUpper [Finite (MulAut W)] {L : Subgroup (MulAut W)}
    (θ : ↥L ≃* Perm (Fin 5)) {x : MulAut W} (hx : x ∈ L) : x * x ∈ oTwoUpper L :=
  altOf_le_of_odd (θ := θ) (fun _ hy hodd => mem_oTwoUpper_of_odd hy hodd)
    (mul_self_mem_altOf (θ := θ) hx)

omit [Finite W] in
theorem card_fixV_conjAut (g : MulAut W) (X : Subgroup (MulAut W)) :
    Nat.card ↥(fixV (B1.conjAut g X)) = Nat.card ↥(fixV X) := by
  refine Nat.card_congr
    { toFun := fun w => ⟨g⁻¹ w.1, fun x hx => ?_⟩
      invFun := fun w => ⟨g w.1, fun x hx => ?_⟩
      left_inv := fun w => by
        apply Subtype.ext
        simp
      right_inv := fun w => by
        apply Subtype.ext
        simp }
  · have hgx : g * x * g⁻¹ ∈ B1.conjAut g X := by
      rw [B1.mem_conjAut]
      simpa [mul_assoc] using hx
    have h1 := w.2 _ hgx
    have e : x (g⁻¹ w.1) = g⁻¹ ((g * x * g⁻¹) w.1) := by simp [MulAut.mul_apply]
    rw [e, h1]
  · have hx' : g⁻¹ * x * g ∈ X := B1.mem_conjAut.mp hx
    have h1 := w.2 _ hx'
    have e : x (g w.1) = g ((g⁻¹ * x * g) w.1) := by simp [MulAut.mul_apply]
    rw [e, h1]

end Comp

section Sup

variable {G : Type} [Group G]

theorem autI_sup {V : Subgroup G} (hV : IsElemAbelian 2 V) {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (V : Set G)) (hB : B ≤ Subgroup.normalizer (V : Set G)) :
    autI hV (A ⊔ B) = autI hV A ⊔ autI hV B := by
  unfold autI
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem relIndex_mul_card_inf (V A : Subgroup G) :
    (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V *
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) = Nat.card V := by
  have h := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (A : Set G)) V
  rwa [inf_right_comm, inf_idem] at h

end Sup

theorem ker317A5_of_e23 (he23 : E2.E23Nonsolvable) : Ker317A5 := by
  intro G _ _ H T M₂ V hmin hsq hchar hV hJ hns hS
  classical
  have hVe : IsElemAbelian 2 V := hV.2.2.1
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hV.2.1
  set K := twoResidual H with hKdef
  set J := thompsonJ T with hJdef
  have hTH : T ≤ H := hmin.isSylow.1
  have hKH : K ≤ H := twoResidual_le H
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTH.trans hHN
  have hJT : J ≤ T := B6.thompsonJ_le T
  have hJN : J ≤ Subgroup.normalizer (V : Set G) := hJT.trans hTN
  have hVT : V ≤ T :=
    (A4.le_pCoreOf_of_isTwoReducedIn hV).trans (pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow)
  obtain ⟨hKJ, I, hIcard, hJI, hcomm, hind, hconj, htype, hspan, hdir, h2, h3⟩ :=
    he23 G H T M₂ V hVe hmin hsq hchar hV hJ hns
  have hA5 : ∀ L ∈ I, E2.IsA5Module L := by
    by_contra hall
    push Not at hall
    obtain ⟨L₀, hL₀, hL₀a⟩ := hall
    have hL2 : ∀ L ∈ I, ∃ n : ℕ,
        E2.IsL2Natural L (fixV (autI hVe (twoResidual H))) n := by
      intro L hL
      rcases htype L hL with h | h
      · exact h
      · exfalso
        obtain ⟨t, -, ht⟩ := hconj L hL L₀ hL₀
        rcases htype L₀ hL₀ with ⟨n, hn⟩ | h0
        · have h1 := card_of_isL2Natural hn
          rw [← ht, card_conjAut, card_of_isA5Module h] at h1
          exact two_pow_mul_ne_120 n h1.symm
        · exact hL₀a h0
    exact hS (h2 hL2).2.2.1
  obtain ⟨-, hXdec, hL4⟩ := h3 hA5
  set X := autI hVe J with hXdef
  have hIH : (⨆ L ∈ I, L) ≤ autI hVe H := by
    rw [← hJI]
    exact autI_mono hVe (thompsonJ_le_self H)
  have hLH : ∀ L ∈ I, L ≤ autI hVe H := fun L hL =>
    (le_iSup₂_of_le (f := fun L' (_ : L' ∈ I) => L') L hL le_rfl).trans hIH
  have hsqL : ∀ L ∈ I, ∀ x ∈ L, x * x ∈ oTwoUpper L := by
    intro L hL x hx
    obtain ⟨θ, -⟩ := hA5 L hL
    exact mul_self_mem_oTwoUpper θ hx
  have hKD : autI hVe K = ⨆ L ∈ I, oTwoUpper L := by
    refine le_antisymm ?_ (iSup₂_le fun L hL => (Subgroup.closure_le _).mpr fun x hx =>
      E2.mem_autI_twoResidual_of_odd (hLH L hL hx.1) hx.2)
    intro φ hφ
    obtain ⟨g, hgK, rfl⟩ := (mem_autI hVe).1 hφ
    have hKD' : K ≤ ((⨆ L ∈ I, oTwoUpper L).comap (convI hVe)).map
        (Subgroup.normalizer (V : Set G)).subtype := by
      rw [hKdef, F6.twoResidual_eq_oTwoUpper, oTwoUpper, Subgroup.closure_le]
      rintro x ⟨hxH, hxo⟩
      refine ⟨⟨x, hHN hxH⟩, ?_, rfl⟩
      show convI hVe ⟨x, hHN hxH⟩ ∈ ⨆ L ∈ I, oTwoUpper L
      apply odd_mem_iSup_alt hIcard hcomm hsqL
      · rw [← hJI]
        exact convI_mem_autI hVe (hKJ (F6.mem_twoResidual_of_odd hxH hxo)) _
      · have h1 := orderOf_map_dvd (convI hVe) ⟨x, hHN hxH⟩
        rw [Subgroup.orderOf_mk] at h1
        exact hxo.of_dvd_nat h1
    obtain ⟨n, hn, hng⟩ := hKD' hgK
    have e : n = g := Subtype.ext hng
    rw [← e]
    exact hn
  have hcomp : ∀ L ∈ I, A5Comp L (L ⊓ X) := fun L hL => by
    obtain ⟨h4, θ', hθ'⟩ := hL4 L hL
    exact a5Comp_of (hA5 L hL) h4 θ' hθ'
  rw [hKD] at hspan hdir
  obtain ⟨hcnt, hstrong, g, hg, hgen⟩ := counts hIcard hcomm hind hcomp hspan hdir
  rw [← hXdec] at hcnt hstrong hgen
  rw [← hKD] at hg
  obtain ⟨k₀, hk₀K, hk₀⟩ := (mem_autI hVe).mp hg
  have hkN : (k₀ : G) ∈ Subgroup.normalizer (V : Set G) := k₀.2
  have hXk : autI hVe (B6.conjSub (k₀ : G) J) = B1.conjAut g X := by
    have e : B1.conjAut g X = X.map (MulAut.conj g).toMonoidHom := by
      ext x
      rw [B1.mem_conjAut, Subgroup.mem_map_equiv]
      simp
    rw [e, ← hk₀]
    exact (autI_cjSub hVe hkN J).symm
  have hJkN : B6.conjSub (k₀ : G) J ≤ Subgroup.normalizer (V : Set G) := fun x hx => by
    have hj : (k₀ : G)⁻¹ * x * k₀ ∈ J := B6.mem_conjSub.mp hx
    have e : x = (k₀ : G) * ((k₀ : G)⁻¹ * x * k₀) * (k₀ : G)⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkN (hJN hj)) (Subgroup.inv_mem _ hkN)
  have hgen' : autI hVe K ≤ autI hVe (J ⊔ B6.conjSub (k₀ : G) J) := by
    rw [hKD, autI_sup hVe hJN hJkN, hXk]
    exact (iSup₂_mono fun L _ => oTwoUpper_le L).trans hgen
  have hcount : (V ⊓ Subgroup.centralizer (J : Set G)).relIndex V *
      (V ⊓ Subgroup.centralizer (B6.conjSub (k₀ : G) J : Set G)).relIndex V ≤
      (V ⊓ Subgroup.centralizer ((J ⊔ B6.conjSub (k₀ : G) J : Subgroup G) :
        Set G)).relIndex V := by
    set F := Nat.card ↥(fixV X) with hF
    set D := Nat.card ↥(fixV (autI hVe K)) with hD
    have hF₁ : Nat.card ↥(V ⊓ Subgroup.centralizer (J : Set G)) = F :=
      (card_fixV_autI hVe hJN).symm
    have hF₂ : Nat.card ↥(V ⊓ Subgroup.centralizer (B6.conjSub (k₀ : G) J : Set G)) = F := by
      rw [← card_fixV_autI hVe hJkN, hXk, card_fixV_conjAut]
    have hF' : Nat.card ↥(V ⊓ Subgroup.centralizer
        ((J ⊔ B6.conjSub (k₀ : G) J : Subgroup G) : Set G)) ≤ D := by
      rw [← card_fixV_autI hVe (sup_le hJN hJkN)]
      exact Subgroup.card_le_of_le (fixV_anti hgen')
    have hcnt' : Nat.card V * D ≤ F ^ 2 := by
      rw [hD, hKD]
      exact hcnt
    have r₁ := relIndex_mul_card_inf V J
    have r₂ := relIndex_mul_card_inf V (B6.conjSub (k₀ : G) J)
    have r₃ := relIndex_mul_card_inf V (J ⊔ B6.conjSub (k₀ : G) J)
    rw [hF₁] at r₁
    rw [hF₂] at r₂
    set a := (V ⊓ Subgroup.centralizer (J : Set G)).relIndex V
    set b := (V ⊓ Subgroup.centralizer (B6.conjSub (k₀ : G) J : Set G)).relIndex V
    set c := (V ⊓ Subgroup.centralizer ((J ⊔ B6.conjSub (k₀ : G) J : Subgroup G) :
        Set G)).relIndex V
    set F' := Nat.card ↥(V ⊓ Subgroup.centralizer
        ((J ⊔ B6.conjSub (k₀ : G) J : Subgroup G) : Set G))
    have hFpos : 0 < F := Nat.card_pos
    have hF'pos : 0 < F' := Nat.card_pos
    have key : a * b * (F' * F ^ 2) ≤ c * (F' * F ^ 2) := by
      calc a * b * (F' * F ^ 2) = (a * F) * (b * F) * F' := by ring
        _ = Nat.card V * Nat.card V * F' := by rw [r₁, r₂]
        _ ≤ Nat.card V * Nat.card V * D := by gcongr
        _ = Nat.card V * (Nat.card V * D) := by ring
        _ ≤ Nat.card V * F ^ 2 := by gcongr
        _ = c * F' * F ^ 2 := by rw [r₃]
        _ = c * (F' * F ^ 2) := by ring
    exact Nat.le_of_mul_le_mul_right key (by positivity)
  have hcard : ∀ A, IsMaxElemAbelian T A → ¬ A ≤ Subgroup.centralizer (V : Set G) →
      Nat.card V = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
        Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
    intro A hA hAC
    have hAN : A ≤ Subgroup.normalizer (V : Set G) := hA.1.trans hTN
    rw [← card_autI_eq hVe hAN, ← card_fixV_autI hVe hAN]
    have hoff : IsFFStarOffender (autI hVe T) (autI hVe A) :=
      offenderImages_isFFStarOffender hVe hVT hTN ⟨A, ⟨hA, hAC⟩, rfl⟩
    have hV2 : ∀ v : IntMod V hVe, v ^ 2 = 1 := IntMod.sq_eq_one
    have hle := (rAV_le_one_iff hV2 hoff.isA2).mp (B1_4_1 hV2 hoff)
    have hge := hstrong (autI hVe A) (autI_mono hVe (B6.le_thompsonJ hA))
    exact le_antisymm hle hge
  exact pCoreOf_le_baum_of_facts hmin hV hJ hcard hk₀K hgen' hcount

theorem as317SylowNonsolvable_of_e23 (he23 : E2.E23Nonsolvable) : AS317SylowNonsolvable :=
  Ch3n317A5.as317SylowNonsolvable_of_e23 he23 (ker317A5_of_e23 he23)

end CFSG.Quasithin.Ch3n317Ker

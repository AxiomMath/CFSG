module

public import CFSG.RankThree.PartOne.KF.D8Matrix

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU

variable {p : ℕ} {K : Type} [Field K] {n : ℕ} [NeZero n]

theorem exists_d8ctx_tor (hc : D8Comb n) (hc2 : D8Comb2 hc) (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (M : Subgroup (GL (Fin n) K))
    (hT : ∀ v : D8Mod p K, (diagU (d8Vec n v) : GL (Fin n) K) ∈ M)
    (hP : ∀ τ : Equiv.Perm (Fin n), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
      (permGL τ : GL (Fin n) K) ∈ M) :
    ∃ SM : D8Ctx p K (⊤ : Subgroup ↥M) ((d8Tor p K n).subgroupOf M),
      ∀ v : D8Mod p K, (((SM.tor v : ↥((d8Tor p K n).subgroupOf M)) : ↥M) : GL (Fin n) K) =
        diagU (d8Vec n v) := by
  classical
  set T : Subgroup (GL (Fin n) K) := d8Tor p K n with hTdef
  have hTM : T ≤ M := by
    rintro _ ⟨v, rfl⟩
    exact hT v
  obtain ⟨ζ, hζ'⟩ := hζ
  set z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p _).mpr hζ'.pow_eq_one⟩ with hzdef
  have hz1 : z ≠ 1 := by
    intro h
    have h0 : ζ = 1 := congrArg Subtype.val h
    rw [h0] at hζ'
    have := hζ'.eq_orderOf
    rw [orderOf_one] at this
    exact hp.ne_one this
  have hz2 : z ^ 2 ≠ 1 := by
    intro h
    exact hz1 (eq_one_of_sq_eq_one_of_odd (hp.odd_of_ne_two hp2) h)
  have hdist : ∀ i j : Fin n, i ≠ j → ∃ x ∈ T, ent x i i ≠ ent x j j := by
    intro i j hij
    obtain ⟨v, hv⟩ := d8Ev_ne z hz1 hz2 _ _ (hc.cls_inj i j hij)
    refine ⟨diagU (d8Vec n v), ⟨v, rfl⟩, ?_⟩
    simp only [ent, diagU_apply_same]
    intro h
    exact hv (Units.ext h)
  have hpair : ∀ i j : Fin n, j ≠ Fin.rev i →
      ∃ v : D8Mod p K, d8Vec n v i * d8Vec n v j ≠ 1 := by
    intro i j hij
    have : d8Cls n j ≠ d8Rho (d8Cls n i) := by
      rw [← hc.cls_rev]
      exact hc.cls_inj _ _ hij
    exact d8Ev_mul_ne_one z hz1 hz2 _ _ this
  have hdmem : ∀ v : D8Mod p K, (diagU (d8Vec n v) : GL (Fin n) K) ∈ T := fun v => ⟨v, rfl⟩
  let torh : D8Mod p K →* ↥(T.subgroupOf M) :=
    { toFun := fun v => ⟨⟨diagU (d8Vec n v), hT v⟩, hdmem v⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        show diagU (d8Vec n 1) = 1
        have : d8Vec (p := p) (K := K) n 1 = 1 := (d8VecHom n).map_one
        rw [this]
        exact diagU_one
      map_mul' := fun v w => by
        apply Subtype.ext
        apply Subtype.ext
        show diagU (d8Vec n (v * w)) = diagU (d8Vec n v) * diagU (d8Vec n w)
        have : d8Vec (p := p) (K := K) n (v * w) = d8Vec n v * d8Vec n w :=
          (d8VecHom n).map_mul v w
        rw [this, ← diagU_mul] }
  have hinj : Function.Injective torh := by
    intro v w h
    have h1 : d8Vec n v = d8Vec n w :=
      diagU_injective (congrArg (fun x : ↥(T.subgroupOf M) => ((x : ↥M) : GL (Fin n) K)) h)
    have h0 : ∀ u : D8Mod p K, d8Vec n u 0 = ((u.1 : rootsOfUnity p K) : Kˣ) := fun u => by
      simp [d8Vec, d8Cls, d8Ev]
    have h1' : ∀ u : D8Mod p K, d8Vec n u 1 = ((u.2 : rootsOfUnity p K) : Kˣ) := fun u => by
      simp [d8Vec, d8Cls, d8Ev, hc.one_ne_zero]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [← h0 v, ← h0 w, h1]
    · rw [← h1' v, ← h1' w, h1]
  have hsurj : Function.Surjective torh := by
    rintro ⟨⟨x, hxM⟩, hxT⟩
    obtain ⟨v, hv⟩ := hxT
    refine ⟨v, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hv
  let tor : D8Mod p K ≃* ↥(T.subgroupOf M) := MulEquiv.ofBijective torh ⟨hinj, hsurj⟩
  have hcoe : ∀ v, (((tor v : ↥(T.subgroupOf M)) : ↥M) : GL (Fin n) K) = diagU (d8Vec n v) :=
    fun v => rfl
  have hconj : ∀ (γ : DihedralGroup 4) (v : D8Mod p K),
      (permGL (d8Perm hc γ) : GL (Fin n) K) * diagU (d8Vec n v) *
        (permGL (d8Perm hc γ) : GL (Fin n) K)⁻¹ = diagU (d8Vec n (d8Act γ v)) := by
    intro γ v
    rw [permGL_conj_diagU, d8Vec_act hc]
  refine ⟨{ tor := tor, exists_elt := ?_, induced := ?_ }, fun v => rfl⟩
  · intro γ
    set g : ↥M := ⟨permGL (d8Perm hc γ), hP _ (hc2.comm_rev γ)⟩ with hgdef
    have hg : g ∈ Subgroup.normalizer ((T.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
      rw [mem_normalizer_subgroupOf_iff hTM]
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · obtain ⟨v, rfl⟩ := hx
        show (permGL (d8Perm hc γ) : GL (Fin n) K) * diagU (d8Vec n v) *
          (permGL (d8Perm hc γ) : GL (Fin n) K)⁻¹ ∈ T
        rw [hconj]
        exact hdmem _
      · obtain ⟨v, rfl⟩ := hx
        show (permGL (d8Perm hc γ) : GL (Fin n) K)⁻¹ * diagU (d8Vec n v) *
          (permGL (d8Perm hc γ) : GL (Fin n) K) ∈ T
        have h1 : (permGL (d8Perm hc γ) : GL (Fin n) K)⁻¹ = permGL (d8Perm hc γ⁻¹) := by
          rw [map_inv, map_inv]
        have h2 : (permGL (d8Perm hc γ) : GL (Fin n) K) =
            (permGL (d8Perm hc γ⁻¹) : GL (Fin n) K)⁻¹ := by
          rw [map_inv, map_inv, inv_inv]
        rw [h1, h2, hconj]
        exact hdmem _
    refine ⟨g, hg, Subgroup.mem_top _, ?_⟩
    refine MulEquiv.ext fun t => ?_
    obtain ⟨v, rfl⟩ := tor.surjective t
    rw [SymCtx.congr_apply_tor]
    apply Subtype.ext
    apply Subtype.ext
    show (permGL (d8Perm hc γ) : GL (Fin n) K) * diagU (d8Vec n v) *
      (permGL (d8Perm hc γ) : GL (Fin n) K)⁻¹ = diagU (d8Vec n (d8Act γ v))
    exact hconj γ v
  · intro m hm _
    obtain ⟨h1, h2⟩ := (mem_normalizer_subgroupOf_iff hTM m).mp hm
    obtain ⟨τ, -, -, hτ⟩ := exists_perm_of_normalizes T
      (fun x hx => by obtain ⟨v, rfl⟩ := hx; exact isDiag_diagU _) hdist h1 h2
    have hτv : ∀ v : D8Mod p K, ∃ v' : D8Mod p K, diagU (d8Vec n v') =
        (m : GL (Fin n) K) * diagU (d8Vec n v) * (m : GL (Fin n) K)⁻¹ ∧
        d8Vec n v' = d8Vec n v ∘ τ.symm := by
      intro v
      obtain ⟨v', hv'⟩ := h1 (diagU (d8Vec n v)) ⟨v, rfl⟩
      have hv'' : diagU (d8Vec n v') = (m : GL (Fin n) K) * diagU (d8Vec n v) *
          (m : GL (Fin n) K)⁻¹ := hv'
      refine ⟨v', hv'', funext fun i => ?_⟩
      have h3 := hτ (diagU (d8Vec n v)) ⟨v, rfl⟩ (τ.symm i)
      rw [Equiv.apply_symm_apply, ← hv''] at h3
      simp only [ent, diagU_apply_same] at h3
      exact Units.ext h3
    have hτrev : ∀ j, τ.symm (Fin.rev j) = Fin.rev (τ.symm j) := by
      intro j
      by_contra hne
      obtain ⟨v, hv⟩ := hpair (τ.symm j) (τ.symm (Fin.rev j)) hne
      obtain ⟨v', -, hv'⟩ := hτv v
      apply hv
      have h4 := d8Vec_mul_rev hc v' j
      rw [hv'] at h4
      exact h4
    have hτc : ∀ i, τ (Fin.rev i) = Fin.rev (τ i) := by
      intro i
      have h5 := hτrev (τ i)
      rw [Equiv.symm_apply_apply] at h5
      have h6 := congrArg τ h5
      rw [Equiv.apply_symm_apply] at h6
      exact h6.symm
    obtain ⟨w, hw⟩ := hc2.closure τ hτc
    refine ⟨w, MulEquiv.ext fun t => ?_⟩
    obtain ⟨v, rfl⟩ := tor.surjective t
    rw [SymCtx.congr_apply_tor]
    obtain ⟨v', hv'1, hv'2⟩ := hτv v
    apply Subtype.ext
    apply Subtype.ext
    show (m : GL (Fin n) K) * diagU (d8Vec n v) * (m : GL (Fin n) K)⁻¹ =
      diagU (d8Vec n (d8Act w v))
    rw [← hv'1, d8Vec_act hc, hw, hv'2]


end CFSG.RankThree.PartOne.KFOUT3

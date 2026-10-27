module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeYa
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem c23ne_subgroupOf_commutator {H K₁ K₂ : Subgroup G} (h₁ : K₁ ≤ H) (h₂ : K₂ ≤ H) :
    ⁅K₁.subgroupOf H, K₂.subgroupOf H⁆ = (⁅K₁, K₂⁆ : Subgroup G).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h₁,
    Subgroup.map_subgroupOf_eq_of_le h₂,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le h₁ h₂)]

private theorem c23ne_comm_of_commutator_comm {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {q k : G} (hqs : q ∈ stabTil V₀ V) (hks : k ∈ stabTil V₀ V)
    (hq0 : q ∈ centralizer (V₀ : Set G)) (hk0 : k ∈ centralizer (V₀ : Set G))
    (hqT : ∀ v ∈ V, q * v * q⁻¹ * v⁻¹ ∈ V₀)
    (hcomm : ∀ v ∈ V, (k * q * k⁻¹ * q⁻¹) * v = v * (k * q * k⁻¹ * q⁻¹)) :
    ∀ v ∈ V, q * (k * v * k⁻¹ * v⁻¹) = (k * v * k⁻¹ * v⁻¹) * q := by
  intro v hv
  let σ : MulAut (IntMod V hV) := actStab V₀ V hV ⟨q, hqs⟩
  let τ : MulAut (IntMod V hV) := actStab V₀ V hV ⟨k, hks⟩
  have hτσ : τ * σ = σ * τ := by
    have h1 : actStab V₀ V hV (⟨k, hks⟩ * ⟨q, hqs⟩ * ⟨k, hks⟩⁻¹ * ⟨q, hqs⟩⁻¹) = 1 := by
      refine MulEquiv.ext fun x => ?_
      rw [MulAut.one_apply]
      apply IntMod.val_injective
      rw [actStab_apply_val]
      have htG : ((⟨k, hks⟩ * ⟨q, hqs⟩ * ⟨k, hks⟩⁻¹ * ⟨q, hqs⟩⁻¹ : ↥(stabTil V₀ V)) : G)
          = k * q * k⁻¹ * q⁻¹ := rfl
      rw [htG]
      have hx := hcomm x.val x.val_mem
      rw [hx]
      group
    have h2 : τ * σ * τ⁻¹ * σ⁻¹ = 1 := by
      simpa only [σ, τ, map_mul, map_inv] using h1
    calc τ * σ = (τ * σ * τ⁻¹ * σ⁻¹) * (σ * τ) := by group
      _ = σ * τ := by rw [h2, one_mul]
  let y : IntMod V hV := IntMod.mk hV ⟨v, hv⟩
  let φ : IntMod V hV := IntMod.mk hV ⟨q * v * q⁻¹ * v⁻¹,
    V.mul_mem ((Subgroup.mem_normalizer_iff.1 (stabTil_le_normalizer V₀ V hqs) v).1 hv)
      (V.inv_mem hv)⟩
  have hφ0 : (φ : IntMod V hV).val ∈ V₀ := hqT v hv
  have hσy : σ y = φ * y := by
    apply IntMod.val_injective
    rw [actStab_apply_val, IntMod.val_mul]
    show q * v * q⁻¹ = (q * v * q⁻¹ * v⁻¹) * v
    group
  have hτφ : τ φ = φ := by
    apply IntMod.val_injective
    rw [actStab_apply_val]
    have hkφ : k * (φ : IntMod V hV).val = (φ : IntMod V hV).val * k :=
      (Subgroup.mem_centralizer_iff.1 hk0 _ hφ0).symm
    rw [hkφ]
    group
  have hfix : σ (τ y * y⁻¹) = τ y * y⁻¹ := by
    have h1 : τ (σ y) = σ (τ y) := by
      rw [← MulAut.mul_apply, hτσ, MulAut.mul_apply]
    calc σ (τ y * y⁻¹)
        = σ (τ y) * σ y⁻¹ := by rw [map_mul]
      _ = σ (τ y) * (σ y)⁻¹ := by rw [map_inv]
      _ = τ (σ y) * (σ y)⁻¹ := by rw [h1]
      _ = τ (φ * y) * (φ * y)⁻¹ := by rw [hσy]
      _ = (τ φ * τ y) * (φ * y)⁻¹ := by rw [map_mul]
      _ = (φ * τ y) * (φ * y)⁻¹ := by rw [hτφ]
      _ = τ y * y⁻¹ := by
            have h : (φ * τ y) * (φ * y)⁻¹ = (φ * φ⁻¹) * (τ y * y⁻¹) := by
              rw [mul_inv_rev]
              ac_rfl
            rw [h, mul_inv_cancel, one_mul]
  have hval : (τ y * y⁻¹).val = k * v * k⁻¹ * v⁻¹ := by
    rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val]
    rfl
  have hthis : q * (k * v * k⁻¹ * v⁻¹) * q⁻¹ = k * v * k⁻¹ * v⁻¹ := by
    have h := congrArg (fun z : IntMod V hV => z.val) hfix
    have h2 : (σ (τ y * y⁻¹)).val = q * (k * v * k⁻¹ * v⁻¹) * q⁻¹ := by
      rw [actStab_apply_val, hval]
    rw [h2, hval] at h
    exact h
  calc q * (k * v * k⁻¹ * v⁻¹)
      = (q * (k * v * k⁻¹ * v⁻¹) * q⁻¹) * q := by group
    _ = (k * v * k⁻¹ * v⁻¹) * q := by rw [hthis]

theorem c23ne_comm_le_of_subnormal {H K C Q : Subgroup G} (hK : IsSubnormal K H)
    (hKp : ⁅K, K⁆ = K) (hCH : C ≤ H) (hC : (C.subgroupOf H).Normal) (hQH : Q ≤ H)
    (hQ : (Q.subgroupOf H).Normal) (hQ2 : ∀ q ∈ Q, ∃ n : ℕ, q ^ (2 ^ n) ∈ C) :
    ∀ k ∈ K, ∀ q ∈ Q, ∃ a ∈ K, ∃ c ∈ C, k * q * k⁻¹ * q⁻¹ = a * c := by
  classical
  let C' : Subgroup H := C.subgroupOf H
  letI : C'.Normal := hC
  let π : ↥H →* ↥H ⧸ C' := QuotientGroup.mk' C'
  let Kq : Subgroup (↥H ⧸ C') := (K.subgroupOf H).map π
  let Qq : Subgroup (↥H ⧸ C') := (Q.subgroupOf H).map π
  have hKH : K ≤ H := uc22p22a_le_of_isSubnormal hK
  have hKsub : Kq.IsSubnormal :=
    (CFSG.Open.IsSubnormal.subgroupOf hK).map (QuotientGroup.mk'_surjective C')
  have hKperf : Group.IsPerfect ↥Kq := by
    haveI : Group.IsPerfect ↥(K.subgroupOf H) :=
      Subgroup.isPerfect_iff.mpr (by rw [c23ne_subgroupOf_commutator hKH hKH, hKp])
    exact Group.IsPerfect.map (f := π)
  have hQnorm : Qq.Normal := hQ.map π (QuotientGroup.mk'_surjective C')
  have hQp2 : IsPGroup 2 Qq := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 g.2
    obtain ⟨n, hn⟩ := hQ2 (x : G) (Subgroup.mem_subgroupOf.1 hx)
    refine ⟨n, ?_⟩
    have hxpow : (x : H) ^ (2 ^ n) ∈ C' := by
      rw [Subgroup.mem_subgroupOf]
      exact hn
    have hπ : π ((x : H) ^ (2 ^ n)) = 1 := (QuotientGroup.eq_one_iff _).2 hxpow
    have hg : g = ⟨π x, hxg ▸ g.2⟩ := Subtype.ext hxg.symm
    rw [hg]
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hπ]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQsolv : Group.IsSolvable ↥Qq := by
    haveI : Group.IsNilpotent ↥Qq := hQp2.isNilpotent
    infer_instance
  have hsup := CFSG.SignalizerFunctorTheorem.Nonsolvable.sup_le_normalizer
    hKperf hKsub hQnorm hQsolv
  have hQN : Qq ≤ Subgroup.normalizer (Kq : Set (↥H ⧸ C')) := le_sup_right.trans hsup
  have hcommKQ : ⁅Kq, Qq⁆ ≤ Kq := Subgroup.le_normalizer_iff_commutator_le_left.1 hQN
  intro k hk q hq
  have hkH : k ∈ H := hKH hk
  have hqH : q ∈ H := hQH hq
  have hkK : (⟨k, hkH⟩ : H) ∈ K.subgroupOf H := Subgroup.mem_subgroupOf.2 hk
  have hqQ : (⟨q, hqH⟩ : H) ∈ Q.subgroupOf H := Subgroup.mem_subgroupOf.2 hq
  have hmem : ⁅π ⟨k, hkH⟩, π ⟨q, hqH⟩⁆ ∈ Kq :=
    hcommKQ (Subgroup.commutator_mem_commutator
      (Subgroup.mem_map_of_mem π hkK) (Subgroup.mem_map_of_mem π hqQ))
  have hxmem : π (⟨k, hkH⟩ * ⟨q, hqH⟩ * ⟨k, hkH⟩⁻¹ * ⟨q, hqH⟩⁻¹) ∈ Kq := by
    simpa only [map_mul, map_inv, commutatorElement_def] using hmem
  obtain ⟨aH, haH, haeq⟩ := Subgroup.mem_map.1 hxmem
  have haK : (aH : G) ∈ K := Subgroup.mem_subgroupOf.1 haH
  have hcH : aH⁻¹ * (⟨k, hkH⟩ * ⟨q, hqH⟩ * ⟨k, hkH⟩⁻¹ * ⟨q, hqH⟩⁻¹) ∈ C' := by
    have h1 : π (aH⁻¹ * (⟨k, hkH⟩ * ⟨q, hqH⟩ * ⟨k, hkH⟩⁻¹ * ⟨q, hqH⟩⁻¹)) = 1 := by
      rw [map_mul, map_inv, haeq, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hcC : (aH : G)⁻¹ * (k * q * k⁻¹ * q⁻¹) ∈ C := by
    have := hcH
    rw [Subgroup.mem_subgroupOf] at this
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  exact ⟨(aH : G), haK, (aH : G)⁻¹ * (k * q * k⁻¹ * q⁻¹), hcC, by group⟩

theorem c23ne_sq_mem_cent {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hV₀V : V₀ ≤ V) {q : G}
    (hq : q ∈ F11.CTilde M V₀ V) (hq0 : q ∈ centralizer (V₀ : Set G)) :
    q ^ 2 ∈ centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hδ : q * v * q⁻¹ * v⁻¹ ∈ V₀ := WeakClosure81.mem_cTilde_mul_inv hV hM hq hv
  have hδV : q * v * q⁻¹ * v⁻¹ ∈ V := hV₀V hδ
  have hδ2 : (q * v * q⁻¹ * v⁻¹) ^ 2 = 1 := hV.2 _ hδV
  have hqδ : (q * v * q⁻¹ * v⁻¹) * q = q * (q * v * q⁻¹ * v⁻¹) :=
    Subgroup.mem_centralizer_iff.1 hq0 _ hδ
  have hqv : q * v * q⁻¹ = (q * v * q⁻¹ * v⁻¹) * v := by group
  let d : G := q * v * q⁻¹ * v⁻¹
  have hδ2' : d ^ 2 = 1 := hδ2
  have hqδ' : d * q = q * d := hqδ
  have hqv' : q * v * q⁻¹ = d * v := by
    simp only [d]
    group
  have key : (q * q) * v * (q * q)⁻¹ = v := by
    calc (q * q) * v * (q * q)⁻¹
        = q * (q * v * q⁻¹) * q⁻¹ := by group
      _ = q * (d * v) * q⁻¹ := by rw [hqv']
      _ = (q * d * q⁻¹) * (q * v * q⁻¹) := by group
      _ = d * (q * v * q⁻¹) := by rw [← hqδ']; group
      _ = d * (d * v) := by rw [hqv']
      _ = d * d * v := by group
      _ = v := by rw [← pow_two, hδ2', one_mul]
  have : (q * q) * v = v * (q * q) := by
    calc (q * q) * v = ((q * q) * v * (q * q)⁻¹) * (q * q) := by group
      _ = v * (q * q) := by rw [key]
  simpa only [pow_two] using this.symm

theorem c23ne_exists_comm_not_cent {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : G} {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂)
    (hMs : D.M ≤ stabTil V₀ V) {q : G}
    (hq : q ∈ F11.CTilde D.M V₀ V ⊓ centralizer (V₀ : Set G))
    (hqV : ¬ V ≤ centralizer ({q} : Set G)) :
    ∃ k : G, (k ∈ K₁ ∨ k ∈ K₂) ∧ ¬ V ≤ centralizer ({k * q * k⁻¹ * q⁻¹} : Set G) := by
  classical
  by_contra hcon
  have hcent : ∀ k : G, (k ∈ K₁ ∨ k ∈ K₂) →
      V ≤ centralizer ({k * q * k⁻¹ * q⁻¹} : Set G) := by
    intro k hk
    by_contra hc
    exact hcon ⟨k, hk, hc⟩
  have hM : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hqC : q ∈ F11.CTilde D.M V₀ V := (Subgroup.mem_inf.1 hq).1
  have hq0 : q ∈ centralizer (V₀ : Set G) := (Subgroup.mem_inf.1 hq).2
  have hqT : ∀ v ∈ V, q * v * q⁻¹ * v⁻¹ ∈ V₀ :=
    fun v hv => WeakClosure81.mem_cTilde_mul_inv hV hM hqC hv
  have hqs : q ∈ stabTil V₀ V := hMs (WeakClosure81.cTilde_le_M D.M V₀ V hqC)
  have hV₀cent : V₀ ≤ centralizer ({q} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (Subgroup.mem_centralizer_iff.1 hq0 z hz).symm
  let C : Subgroup G := centralizer ({q} : Set G) ⊓ V
  have hV₀C : V₀ ⊓ V ≤ C := le_inf (inf_le_left.trans hV₀cent) inf_le_right
  have hgen : ∀ {K : Subgroup G}, K ≤ D.M → K ≤ centralizer (V₀ : Set G) →
      (∀ k ∈ K, V ≤ centralizer ({k * q * k⁻¹ * q⁻¹} : Set G)) →
      commSub ⊤ (barSub V₀ V hV K) ≤ imgTil V₀ V hV C := by
    intro K hKM hK0 hKcent
    rw [commSub, Subgroup.closure_le]
    rintro c ⟨u, hu, w, -, rfl⟩
    obtain ⟨g, hgK, hgu⟩ := (mem_barSub V₀ V hV K u).1 hu
    obtain ⟨y, rfl⟩ := mkTil_surjective V₀ V hV w
    have hgs : (g : G) ∈ stabTil V₀ V := hMs (hKM hgK)
    rw [← hgu, actTil_mk, ← map_inv, ← map_mul]
    refine (mem_imgTil V₀ V hV C _).2 ⟨actStab V₀ V hV g y * y⁻¹, ?_, rfl⟩
    have hval : (actStab V₀ V hV g y * y⁻¹).val =
        (g : G) * y.val * (g : G)⁻¹ * y.val⁻¹ := by
      rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [hval]
      exact c23ne_comm_of_commutator_comm hV hqs hgs hq0 (hK0 hgK) hqT
        (fun v hv => Subgroup.mem_centralizer_iff.1 (hKcent (g : G) hgK hv) _ (by simp))
        y.val y.val_mem
    · rw [hval]
      exact V.mul_mem
        ((Subgroup.mem_normalizer_iff.1 (stabTil_le_normalizer V₀ V hgs) y.val).1 y.val_mem)
        (V.inv_mem y.val_mem)
  have h1 : wTil V₀ V hV L ≤ imgTil V₀ V hV C := by
    have := hgen (K := K₁) (uc22p22a_le_of_isSubnormal hctx.mem₁.1)
      (le_sup_left.trans hctx.cent₀) (fun k hk => hcent k (Or.inl hk))
    rwa [hctx.bar₁] at this
  have h2 : wTil V₀ V hV (conjSubgroup L x) ≤ imgTil V₀ V hV C := by
    have := hgen (K := K₂) (uc22p22a_le_of_isSubnormal hctx.mem₂.1)
      (le_sup_right.trans hctx.cent₀) (fun k hk => hcent k (Or.inr hk))
    rwa [hctx.bar₂] at this
  have htop : (⊤ : Subgroup (Vtil V₀ V hV)) ≤ imgTil V₀ V hV C := by
    rw [← hctx.core.sup_eq]
    exact sup_le h1 h2
  have hCtop : imgTil V₀ V hV C = ⊤ := top_le_iff.1 htop
  have hVC : V ≤ C := by
    intro v hv
    have hmem : mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩) ∈ imgTil V₀ V hV C := by
      rw [hCtop]
      exact Subgroup.mem_top _
    obtain ⟨z, hzC, hzeq⟩ := (mem_imgTil V₀ V hV C _).1 hmem
    have hzV : z.val ∈ V := (inf_le_right : C ≤ V) hzC
    have hzV₀ : z.val * v⁻¹ ∈ V₀ :=
      (mkTil_eq_iff V₀ V hV z (IntMod.mk hV ⟨v, hv⟩)).1 hzeq
    have hzV₀V : z.val * v⁻¹ ∈ V₀ ⊓ V :=
      ⟨hzV₀, V.mul_mem hzV (V.inv_mem hv)⟩
    have : z.val * v⁻¹ ∈ C := hV₀C hzV₀V
    have hv_inv : v⁻¹ ∈ C := by
      have := C.mul_mem (C.inv_mem hzC) this
      simpa [mul_assoc] using this
    simpa using C.inv_mem hv_inv
  exact hqV (hVC.trans (show C ≤ centralizer ({q} : Set G) from inf_le_left))

private theorem c23ne_cent_normal {M V : Subgroup G} (hM : M ≤ normalizer (V : Set G)) :
    ((centralizer (V : Set G) ⊓ M).subgroupOf M).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnc, hnM⟩ := Subgroup.mem_inf.1 hn
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun v hv => ?_, ?_⟩
  · have hg : (g : G) ∈ normalizer (V : Set G) := hM g.2
    have hv' : (g : G)⁻¹ * v * (g : G) ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 ((normalizer (V : Set G)).inv_mem hg) v).1 hv
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hnc _ hv'
    change v * ((g : G) * (n : G) * (g : G)⁻¹) = ((g : G) * (n : G) * (g : G)⁻¹) * v
    calc v * ((g : G) * (n : G) * (g : G)⁻¹)
        = (g : G) * (((g : G)⁻¹ * v * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
      _ = (g : G) * ((n : G) * ((g : G)⁻¹ * v * (g : G))) * (g : G)⁻¹ := by rw [h1]
      _ = ((g : G) * (n : G) * (g : G)⁻¹) * v := by group
  · exact (g * n * g⁻¹).2

private theorem c23ne_q_normal {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G)) :
    ((F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)).subgroupOf M).Normal := by
  have hN := WeakClosure81.cTilde_subgroupOf_normal hV hM hM₀
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnC, hn0⟩ := Subgroup.mem_inf.1 hn
  refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
  · have := hN.conj_mem ⟨(n : G), n.2⟩ (Subgroup.mem_subgroupOf.2 hnC) g
    simpa using (Subgroup.mem_subgroupOf.1 this)
  · have hg : (g : G) ∈ normalizer (V₀ : Set G) := hM₀ g.2
    have hv' : (g : G)⁻¹ * v * (g : G) ∈ V₀ := by
      have := (Subgroup.mem_normalizer_iff.1 ((normalizer (V₀ : Set G)).inv_mem hg) v).1 hv
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hn0 _ hv'
    change v * ((g : G) * (n : G) * (g : G)⁻¹) = ((g : G) * (n : G) * (g : G)⁻¹) * v
    calc v * ((g : G) * (n : G) * (g : G)⁻¹)
        = (g : G) * (((g : G)⁻¹ * v * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
      _ = (g : G) * ((n : G) * ((g : G)⁻¹ * v * (g : G))) * (g : G)⁻¹ := by rw [h1]
      _ = ((g : G) * (n : G) * (g : G)⁻¹) * v := by group

private theorem c23ne_Y_aux {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂) (hMs : D.M ≤ stabTil V₀ V)
    (hV₀V : V₀ ≤ V) {K : Subgroup G} (hKc : K ∈ calC D.M) (hKle : K ≤ K₁ ⊔ K₂)
    (hY : c23neY V K₁ K₂ = ⊥) {q : G} (hq : q ∈ F11.CTilde D.M V₀ V ⊓ centralizer (V₀ : Set G))
    {k : G} (hk : k ∈ K) :
    V ≤ centralizer ({k * q * k⁻¹ * q⁻¹} : Set G) := by
  have hM : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hM₀ : D.M ≤ normalizer (V₀ : Set G) := fun g hg => (hMs hg).2
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hKc.1
  have hQ2 : ∀ q ∈ F11.CTilde D.M V₀ V ⊓ centralizer (V₀ : Set G),
      ∃ n : ℕ, q ^ (2 ^ n) ∈ centralizer (V : Set G) ⊓ D.M := by
    intro q hq
    obtain ⟨hqT, hq0⟩ := Subgroup.mem_inf.1 hq
    refine ⟨1, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
    · simpa using c23ne_sq_mem_cent hV hM hV₀V hqT hq0
    · simpa using D.M.pow_mem (WeakClosure81.cTilde_le_M _ _ _ hqT) 2
  obtain ⟨a, haK, c, hcC, hac⟩ := c23ne_comm_le_of_subnormal (H := D.M) hKc.1 hKc.2.1
    inf_le_right (c23ne_cent_normal hM) (inf_le_left.trans (WeakClosure81.cTilde_le_M _ _ _))
    (c23ne_q_normal hV hM hM₀) hQ2 k hk q hq
  obtain ⟨hcV, hcM⟩ := Subgroup.mem_inf.1 hcC
  have hkM : k ∈ D.M := hKM hk
  have hcomm : k * q * k⁻¹ * q⁻¹ ∈ F11.CTilde D.M V₀ V := by
    have hq1 := (Subgroup.mem_inf.1 hq).1
    have hN := WeakClosure81.cTilde_subgroupOf_normal hV hM hM₀
    have h1 := hN.conj_mem ⟨q, WeakClosure81.cTilde_le_M _ _ _ hq1⟩
      (Subgroup.mem_subgroupOf.2 hq1) ⟨k, hkM⟩
    have h2 : k * q * k⁻¹ ∈ F11.CTilde D.M V₀ V := by simpa using Subgroup.mem_subgroupOf.1 h1
    exact (F11.CTilde D.M V₀ V).mul_mem h2 ((F11.CTilde D.M V₀ V).inv_mem hq1)
  have hcT : c ∈ F11.CTilde D.M V₀ V := by
    refine (mem_cTilde_iff hV hM).2 ⟨hcM, hMs hcM,
      (actTil_eq_one_iff V₀ V hV ⟨c, hMs hcM⟩).2 fun v hv => ?_⟩
    have h1 : v * c = c * v := Subgroup.mem_centralizer_iff.1 hcV v hv
    have h2 : c * v * c⁻¹ * v⁻¹ = 1 := by rw [← h1]; group
    show c * v * c⁻¹ * v⁻¹ ∈ V₀
    rw [h2]
    exact V₀.one_mem
  have haT : a ∈ F11.CTilde D.M V₀ V := by
    have : a = (k * q * k⁻¹ * q⁻¹) * c⁻¹ := by rw [hac]; group
    rw [this]
    exact (F11.CTilde D.M V₀ V).mul_mem hcomm ((F11.CTilde D.M V₀ V).inv_mem hcT)
  have haQ : a ∈ c23neQ2 K₁ K₂ := by
    rw [← hctx.ker]
    exact Subgroup.mem_inf.2 ⟨haT, hKle haK⟩
  have haV : ∀ v ∈ V, a * v = v * a := fun v hv => by
    have h1 : ⁅v, a⁆ ∈ c23neY V K₁ K₂ := Subgroup.commutator_mem_commutator hv haQ
    rw [hY, Subgroup.mem_bot] at h1
    have h2 : v * a * v⁻¹ * a⁻¹ = 1 := h1
    calc a * v = (v * a * v⁻¹ * a⁻¹) ⁻¹ * (v * a) := by group
      _ = v * a := by rw [h2]; simp
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  have hcv : c * v = v * c := (Subgroup.mem_centralizer_iff.1 hcV v hv).symm
  calc (k * q * k⁻¹ * q⁻¹) * v = a * c * v := by rw [hac]
    _ = a * (v * c) := by rw [mul_assoc, hcv]
    _ = v * (a * c) := by rw [← mul_assoc, haV v hv, mul_assoc]
    _ = v * (k * q * k⁻¹ * q⁻¹) := by rw [hac]

theorem c23ne_Y_ne_bot {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂) (hMs : D.M ≤ stabTil V₀ V)
    (hV₀V : V₀ ≤ V) (hsmall : mSub V₀ ≤ 2) (h0 : InCalV0 D.M V₀ V) :
    c23neY V K₁ K₂ ≠ ⊥ := by
  intro hY
  obtain ⟨q, hq, hqV⟩ := c23ne_exists_q0 hctx hMs hsmall h0
  obtain ⟨k, hk, hkV⟩ := c23ne_exists_comm_not_cent hctx hMs hq hqV
  rcases hk with hk | hk
  · exact hkV (c23ne_Y_aux hctx hMs hV₀V hctx.mem₁ le_sup_left hY hq hk)
  · exact hkV (c23ne_Y_aux hctx hMs hV₀V hctx.mem₂ le_sup_right hY hq hk)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

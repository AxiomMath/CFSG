module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6Borel
public import CFSG.Quasithin.Vol2.Ch3zXLev

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.Ch3z G6

section Group

variable {G : Type*} [Group G]

theorem mem_sup_of_commute_G6 {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∃ a ∈ A, ∃ b ∈ B, x = a * b) ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, x, hx, by simp⟩
  · exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
    refine ⟨y₁ * y₂, A.mul_mem hy₁ hy₂, z₁ * z₂, B.mul_mem hz₁ hz₂, ?_⟩
    have h := hc y₂ hy₂ z₁ hz₁
    calc y₁ * z₁ * (y₂ * z₂) = y₁ * (z₁ * y₂) * z₂ := by group
      _ = y₁ * (y₂ * z₁) * z₂ := by rw [← h]
      _ = y₁ * y₂ * (z₁ * z₂) := by group
  · rintro _ _ ⟨y, hy, z, hz, rfl⟩
    refine ⟨y⁻¹, A.inv_mem hy, z⁻¹, B.inv_mem hz, ?_⟩
    have h : z * y = y * z := (hc y hy z hz).symm
    calc (y * z)⁻¹ = (z * y)⁻¹ := by rw [h]
      _ = y⁻¹ * z⁻¹ := by group

theorem isSolvable_sup_of_commute_G6 {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hA : Group.IsSolvable A) (hB : Group.IsSolvable B) : Group.IsSolvable ↥(A ⊔ B) := by
  let f : ↥A × ↥B →* ↥(A ⊔ B) :=
    { toFun := fun p => ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro p q
        apply Subtype.ext
        have h := hc (q.1 : G) q.1.2 (p.2 : G) p.2.2
        show (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G)) = (p.1 : G) * (p.2 : G) * ((q.1 : G) * (q.2 : G))
        calc (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G))
            = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
          _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by rw [h]
          _ = (p.1 : G) * (p.2 : G) * ((q.1 : G) * (q.2 : G)) := by group }
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute_G6 hc hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  exact Group.isSolvable_of_surjective hf

end Group

section Blocks

variable {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}
  {𝓗 : Finset (Subgroup (MulAut V))}

theorem symBlk_natBlock_false {M₀ H : Subgroup (MulAut V)} {m e : ℕ} (hS : SymBlk M₀ H m) (he : 2 ≤ e)
    (hN : NatBlockData H (commV H) e) : False := by
  obtain ⟨hm3, -, θ, -⟩ := hS
  have hperf : Group.IsPerfect ↥H := hN.isPerfect he
  let f : ↥H →* ℤˣ := (Equiv.Perm.sign).comp θ.toMonoidHom
  have hf : ∀ x, f x = 1 := by
    intro x
    have hr : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
    have hs : Subsingleton ↥f.range := inferInstance
    have h1 : (⟨f x, ⟨x, rfl⟩⟩ : ↥f.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val h1
  have h0 : 0 < m := by omega
  have hne : (⟨0, h0⟩ : Fin m) ≠ ⟨1, by omega⟩ := by
    intro h
    simp [Fin.ext_iff] at h
  have h1 := hf (θ.symm (Equiv.swap (⟨0, h0⟩ : Fin m) ⟨1, by omega⟩))
  simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    Equiv.Perm.sign_swap hne] at h1
  exact absurd h1 (by decide)

theorem BlkCtx.nat_eq_borel (h : BlkCtx X T M 𝓗) {H : Subgroup (MulAut V)} (hH : H ∈ 𝓗) {e : ℕ}
    (he : 2 ≤ e) (hN : NatBlockData H (commV H) e) :
    M ⊓ H = H ⊓ Subgroup.normalizer ((T ⊓ H : Subgroup (MulAut V)) : Set (MulAut V)) := by
  rcases h.symBlk_or_bad hH with ⟨m, hm⟩ | ⟨e', -, -, hM⟩
  · exact (symBlk_natBlock_false hm he hN).elim
  · exact hM

theorem BlkCtx.isSolvable_of_block (h : BlkCtx X T M 𝓗) {H₀ : Subgroup (MulAut V)} (hH₀ : H₀ ∈ 𝓗)
    (hsolv : Group.IsSolvable ↥(M ⊓ H₀))
    (hself : ∀ g ∈ H₀, g ∈ Subgroup.normalizer ((M ⊓ H₀ : Subgroup (MulAut V)) : Set (MulAut V)) →
      g ∈ M) : Group.IsSolvable ↥M := by
  classical
  have hMX : M ≤ X := h.mp.maximal.1.le
  have hblk : ∀ H ∈ 𝓗, Group.IsSolvable ↥(M ⊓ H) ∧
      ∀ g ∈ H, g ∈ Subgroup.normalizer ((M ⊓ H : Subgroup (MulAut V)) : Set (MulAut V)) → g ∈ M := by
    intro H hH
    obtain ⟨t, htT, hc⟩ := h.trans hH₀ hH
    have htM : t ∈ M := h.mp.le htT
    have hMconj : ∀ x : MulAut V, x ∈ M ↔ t⁻¹ * x * t ∈ M := by
      intro x
      constructor
      · intro hx
        exact M.mul_mem (M.mul_mem (M.inv_mem htM) hx) htM
      · intro hx
        have := M.mul_mem (M.mul_mem htM hx) (M.inv_mem htM)
        simpa [mul_assoc] using this
    have hMH : M ⊓ H = B6.conjSub t (M ⊓ H₀) := by
      ext x
      rw [← hc, Subgroup.mem_inf, B6.mem_conjSub, B6.mem_conjSub, Subgroup.mem_inf, hMconj x]
    refine ⟨?_, fun g hgH hgN => ?_⟩
    · rw [hMH]
      have e1 : ↥(M ⊓ H₀) ≃* ↥(B6.conjSub t (M ⊓ H₀)) :=
        Subgroup.equivMapOfInjective (M ⊓ H₀) (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
      exact Group.isSolvable_of_surjective (f := e1.toMonoidHom) e1.surjective
    · have hg0 : t⁻¹ * g * t ∈ H₀ := by
        rw [← hc] at hgH
        exact B6.mem_conjSub.mp hgH
      have hconj : ∀ y : MulAut V, (y ∈ M ⊓ H₀ ↔ t * y * t⁻¹ ∈ M ⊓ H) := by
        intro y
        rw [hMH, B6.mem_conjSub]
        simp [mul_assoc]
      have hgN0 : t⁻¹ * g * t ∈ Subgroup.normalizer ((M ⊓ H₀ : Subgroup (MulAut V)) : Set (MulAut V)) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [hconj y, hconj ((t⁻¹ * g * t) * y * (t⁻¹ * g * t)⁻¹)]
        have e2 : t * ((t⁻¹ * g * t) * y * (t⁻¹ * g * t)⁻¹) * t⁻¹ = g * (t * y * t⁻¹) * g⁻¹ := by
          group
        rw [e2]
        exact Subgroup.mem_normalizer_iff.mp hgN (t * y * t⁻¹)
      have := hself _ hg0 hgN0
      rw [hMconj g]
      exact this
  have hcomm : ∀ (𝓕' : Finset (Subgroup (MulAut V))), 𝓕' ⊆ 𝓗 → ∀ H₁ ∈ 𝓗, H₁ ∉ 𝓕' →
      (⨆ H ∈ 𝓕', H) ≤ Subgroup.centralizer (H₁ : Set (MulAut V)) := by
    intro 𝓕' hsub H₁ hH₁ hn
    refine iSup₂_le fun H hH x hx => ?_
    have hne : H ≠ H₁ := fun heq => hn (heq ▸ hH)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (h.comm_of_ne (hsub hH) hH₁ hne hx hy).symm
  have hstep2 : ∀ 𝓕 : Finset (Subgroup (MulAut V)), 𝓕 ⊆ 𝓗 →
      M ⊓ (⨆ H ∈ 𝓕, H) ≤ ⨆ H ∈ 𝓕, M ⊓ H := by
    intro 𝓕
    induction 𝓕 using Finset.induction_on with
    | empty =>
      intro _
      simp
    | insert H₁ 𝓕' hH₁ ih =>
      intro hsub d hd
      have hH₁𝓗 : H₁ ∈ 𝓗 := hsub (Finset.mem_insert_self _ _)
      have hsub' : 𝓕' ⊆ 𝓗 := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      rw [Finset.iSup_insert] at hd ⊢
      obtain ⟨hdM, hdJ⟩ := hd
      have hcR := hcomm 𝓕' hsub' H₁ hH₁𝓗 hH₁
      have hc' : ∀ a ∈ H₁, ∀ b ∈ (⨆ H ∈ 𝓕', H), a * b = b * a := by
        intro a ha b hb
        exact Subgroup.mem_centralizer_iff.mp (hcR hb) a ha
      obtain ⟨a, ha, r, hr, rfl⟩ := mem_sup_of_commute_G6 hc' hdJ
      have hcr : ∀ c ∈ H₁, r * c = c * r := fun c hc => (hc' c hc r hr).symm
      have hb : ∀ b ∈ M ⊓ H₁, a * b * a⁻¹ ∈ M ⊓ H₁ ∧ a⁻¹ * b * a ∈ M ⊓ H₁ := by
        intro b hb
        constructor
        · refine ⟨?_, H₁.mul_mem (H₁.mul_mem ha hb.2) (H₁.inv_mem ha)⟩
          have h1 : (a * r) * b * (a * r)⁻¹ ∈ M :=
            M.mul_mem (M.mul_mem hdM hb.1) (M.inv_mem hdM)
          have e : (a * r) * b * (a * r)⁻¹ = a * b * a⁻¹ := by
            calc (a * r) * b * (a * r)⁻¹ = a * (r * b) * r⁻¹ * a⁻¹ := by group
              _ = a * (b * r) * r⁻¹ * a⁻¹ := by rw [hcr b hb.2]
              _ = a * b * a⁻¹ := by group
          rwa [e] at h1
        · refine ⟨?_, H₁.mul_mem (H₁.mul_mem (H₁.inv_mem ha) hb.2) ha⟩
          have h1 : (a * r)⁻¹ * b * (a * r) ∈ M :=
            M.mul_mem (M.mul_mem (M.inv_mem hdM) hb.1) hdM
          have hc2 : r * (a⁻¹ * b * a) = (a⁻¹ * b * a) * r :=
            hcr _ (H₁.mul_mem (H₁.mul_mem (H₁.inv_mem ha) hb.2) ha)
          have e : (a * r)⁻¹ * b * (a * r) = a⁻¹ * b * a := by
            calc (a * r)⁻¹ * b * (a * r) = r⁻¹ * (a⁻¹ * b * a) * r := by group
              _ = r⁻¹ * ((a⁻¹ * b * a) * r) := by group
              _ = r⁻¹ * (r * (a⁻¹ * b * a)) := by rw [hc2]
              _ = a⁻¹ * b * a := by group
          rwa [e] at h1
      have haN : a ∈ Subgroup.normalizer ((M ⊓ H₁ : Subgroup (MulAut V)) : Set (MulAut V)) :=
        B6.mem_normalizer_of_forall_mem (fun b hb' => (hb b hb').1) (fun b hb' => (hb b hb').2)
      have haM : a ∈ M := (hblk H₁ hH₁𝓗).2 a ha haN
      have hrM : r ∈ M := by
        have := M.mul_mem (M.inv_mem haM) hdM
        simpa using this
      have hr' : r ∈ ⨆ H ∈ 𝓕', M ⊓ H := ih hsub' ⟨hrM, hr⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨haM, ha⟩) (Subgroup.mem_sup_right hr')
  have hstep3 : ∀ 𝓕 : Finset (Subgroup (MulAut V)), 𝓕 ⊆ 𝓗 →
      Group.IsSolvable ↥(⨆ H ∈ 𝓕, M ⊓ H) := by
    intro 𝓕
    induction 𝓕 using Finset.induction_on with
    | empty =>
      intro _
      have : (⨆ H ∈ (∅ : Finset (Subgroup (MulAut V))), M ⊓ H) = ⊥ := by simp
      rw [this]
      infer_instance
    | insert H₁ 𝓕' hH₁ ih =>
      intro hsub
      have hH₁𝓗 : H₁ ∈ 𝓗 := hsub (Finset.mem_insert_self _ _)
      have hsub' : 𝓕' ⊆ 𝓗 := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      rw [Finset.iSup_insert]
      refine isSolvable_sup_of_commute_G6 (fun a ha b hb => ?_) (hblk H₁ hH₁𝓗).1 (ih hsub')
      have hle : (⨆ H ∈ 𝓕', M ⊓ H) ≤ ⨆ H ∈ 𝓕', H :=
        iSup₂_mono fun H _ => inf_le_right
      exact Subgroup.mem_centralizer_iff.mp (hcomm 𝓕' hsub' H₁ hH₁𝓗 hH₁ (hle hb)) a ha.2
  have hDsolv : Group.IsSolvable ↥(M ⊓ ffJ X) := by
    have hle : M ⊓ ffJ X ≤ ⨆ H ∈ 𝓗, M ⊓ H := by
      rw [h.ffJ_eq]
      exact hstep2 𝓗 le_rfl
    haveI := hstep3 𝓗 le_rfl
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have htwo : ∀ m ∈ X, ∃ k : ℕ, m ^ 2 ^ k ∈ ffJ X :=
    B6.isTwoQuotient_of_sup_eq h.mp.isSylow.2.1 (B6.le_normalizer_ffJ X)
      (by rw [sup_comm]; exact h.eq_sup.symm)
  have hnorm : (((M ⊓ ffJ X : Subgroup (MulAut V))).subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro m hm
    have hJn := Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ X (hMX hm))
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨M.mul_mem (M.mul_mem hm hx1) (M.inv_mem hm), (hJn x).mp hx2⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨?_, (hJn x).mpr hx2⟩
      have := M.mul_mem (M.mul_mem (M.inv_mem hm) hx1) hm
      simpa [mul_assoc] using this
  haveI := hnorm
  have hsolvD : Group.IsSolvable ↥((M ⊓ ffJ X : Subgroup (MulAut V)).subgroupOf M) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      (M ⊓ ffJ X : Subgroup (MulAut V)) ≤ M)).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      (M ⊓ ffJ X : Subgroup (MulAut V)) ≤ M)).symm.surjective
  have hpgrp : IsPGroup 2 (↥M ⧸ (M ⊓ ffJ X : Subgroup (MulAut V)).subgroupOf M) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H m =>
      obtain ⟨k, hk⟩ := htwo (m : MulAut V) (hMX m.2)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact ⟨M.pow_mem m.2 _, hk⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsSolvable (↥M ⧸ (M ⊓ ffJ X : Subgroup (MulAut V)).subgroupOf M) := by
    haveI := hpgrp.isNilpotent
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient ((M ⊓ ffJ X : Subgroup (MulAut V)).subgroupOf M)

theorem BlkCtx.isSolvable_of_nat (h : BlkCtx X T M 𝓗) {H₀ : Subgroup (MulAut V)} (hH₀ : H₀ ∈ 𝓗)
    {e : ℕ} (he : 2 ≤ e) (hN : NatBlockData H₀ (commV H₀) e) : Group.IsSolvable ↥M := by
  have hB := BlkCtx.nat_eq_borel h hH₀ he hN
  have hQ := h.isSylowTwoOf_block hH₀
  have hUinv : ∀ g ∈ H₀, ∀ u ∈ commV H₀, g u ∈ commV H₀ := fun _ hg _ hu =>
    apply_mem_commV_of_mem hg hu
  refine BlkCtx.isSolvable_of_block h hH₀ ?_ ?_
  · rw [hB]
    exact natBlock_normalizer_solvable (by omega) hUinv hN hQ
  · intro g hg hgN
    rw [hB] at hgN
    have := normalizer_inf_normalizer_self hQ hg hgN
    exact (hB ▸ (show g ∈ H₀ ⊓ Subgroup.normalizer ((T ⊓ H₀ : Subgroup (MulAut V)) : Set (MulAut V)) from
      ⟨hg, this⟩) : g ∈ M ⊓ H₀).1

end Blocks

end CFSG.Quasithin.H13.L319

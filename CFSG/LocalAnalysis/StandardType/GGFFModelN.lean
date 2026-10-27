module

public import CFSG.LocalAnalysis.StandardType.GGFFModelNDefs
import CFSG.LocalAnalysis.StandardType.GGFFModel

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF

open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

variable {H : Type} [Group H]

private lemma cjp_map {H' : Type} [Group H'] (e : H ≃* H') (w u : H) (a : Fin 3) :
    e (cjp w a u) = cjp (e w) a (e u) := by
  simp [cjp]

private lemma rootW_map {H' : Type} [Group H'] (e : H ≃* H') (z : Fin 3 → H) :
    rootW (fun i => e (z i)) = fun j => e (rootW z j) := by
  funext j
  fin_cases j <;> rfl

private lemma rootK₁_map {H' : Type} [Group H'] (e : H ≃* H') (z : Fin 3 → H) :
    rootK₁ (fun i => e (z i)) = fun j => e (rootK₁ z j) := by
  funext j
  fin_cases j <;> simp [rootK₁]

private lemma rootK₂_map {H' : Type} [Group H'] (e : H ≃* H') (z : Fin 3 → H) :
    rootK₂ (fun i => e (z i)) = fun j => e (rootK₂ z j) := by
  funext j
  fin_cases j <;> simp [rootK₂]

private lemma gOf_map {H' : Type} [Group H'] (e : H ≃* H') (r r' : Fin 2 → H) :
    e (gOf r r') = gOf (fun j => e (r j)) (fun j => e (r' j)) := by
  simp [gOf]

private lemma rOne_map {H' : Type} [Group H'] (e : H ≃* H') (z : Fin 3 → H) (π : H) :
    (rOne z π).map e = rOne (fun i => e (z i)) (e π) := by
  rw [rOne, rOne, MonoidHom.map_closure]
  congr 1
  ext y
  simp [zetaOf]

private lemma exists_preimage_mem_rOne_set {H' : Type} [Group H'] (e : H ≃* H')
    (z : Fin 3 → H) (π : H)
    {y : H'} (hy : y ∈ ({e (z 0) * (e (z 1))⁻¹, zetaOf (fun i => e (z i)), e π} : Set H')) :
    e.symm y ∈ ({z 0 * (z 1)⁻¹, zetaOf z, π} : Set H) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, zetaOf] at hy ⊢
  rcases hy with h | h | h
  · left; rw [h]; simp
  · right; left; rw [h]; simp
  · right; right; rw [h]; simp

private lemma rootRel_map_iff {H' : Type} [Group H'] (e : H ≃* H') (w u : H) :
    RootRel (e w) (e u) ↔ RootRel w u := by
  rw [RootRel, RootRel]
  constructor
  · intro h
    apply e.injective
    simpa using h
  · intro h
    simpa using congrArg e h

private lemma trans_mul {H' : Type} [Group H'] (e : H ≃* H') (α β : MulAut H') :
    (e.trans (α * β)).trans e.symm =
      ((e.trans α).trans e.symm) * ((e.trans β).trans e.symm) := by
  ext x
  simp [MulAut.mul_apply]

private lemma eq_conj_of_trans_eq_conj {H' : Type} [Group H'] (e : H ≃* H')
    {α : MulAut H'} {k : H} (h : (e.trans α).trans e.symm = MulAut.conj k) :
    α = MulAut.conj (e k) := by
  ext x
  have hx := congrArg (fun γ : MulAut H => e (γ (e.symm x))) h
  simpa [MulAut.conj_apply] using hx

theorem ModelNB.ofMulEquiv {H' : Type} [Group H'] (e : H ≃* H') {z : Fin 3 → H} {π x₀ : H}
    {r r' : Fin 2 → H} (h : ModelNB H z π x₀ r r') :
    ModelNB H' (fun i => e (z i)) (e π) (e x₀) (fun j => e (r j)) (fun j => e (r' j)) where
  pi_cube := by rw [← map_pow, h.pi_cube, map_one]
  pi_z i := by rw [← map_inv, ← map_mul, ← map_mul, h.pi_z i]
  x0_z0 := by rw [← map_inv, ← map_mul, ← map_mul, h.x0_z0]
  x0_z1 := by rw [← map_inv, ← map_mul, ← map_mul, h.x0_z1]
  x0_z2 := by rw [← map_inv, ← map_mul, ← map_mul, h.x0_z2]
  sqrt v hv1 hv2 := by
    have hv1' : x₀ * vecElt z v * (x₀ * vecElt z v) = 1 := by
      apply e.injective
      simpa [vecElt_map] using hv1
    have hv2' : ∃ w, x₀ * vecElt z v * π * (x₀ * vecElt z v)⁻¹ * π = vecElt z w := by
      obtain ⟨w, hw⟩ := hv2
      exact ⟨w, by
        apply e.injective
        simpa [vecElt_map] using hw⟩
    obtain ⟨⟨w, hw0, hw⟩, q, hq1, hq2⟩ := h.sqrt v hv1' hv2'
    refine ⟨⟨w, hw0, ?_⟩, e q, ?_, ?_⟩
    · simpa [vecElt_map] using congrArg e hw
    · rw [← map_mul, hq1, map_mul, vecElt_map]
    · intro y hy
      have hy₀ : e.symm y ∈ ({z 0 * (z 1)⁻¹, zetaOf z, π} : Set H) :=
        exists_preimage_mem_rOne_set e z π hy
      rw [← rOne_map]
      have hmem := Subgroup.mem_map_of_mem e.toMonoidHom (by simpa using hq2 (e.symm y) hy₀)
      simpa using hmem
  root_sq j := by
    obtain ⟨h1, h2⟩ := h.root_sq j
    exact ⟨by simpa using congrArg e h1, by simpa using congrArg e h2⟩
  root_comm j := by
    obtain ⟨h1, h2, h3, h4⟩ := h.root_comm j
    rw [rootK₁_map, rootK₂_map]
    exact ⟨by simpa using congrArg e h1, by simpa using congrArg e h2,
      by simpa using congrArg e h3, by simpa using congrArg e h4⟩
  root_rel j := by
    obtain ⟨h1, h2⟩ := h.root_rel j
    rw [rootW_map]
    exact ⟨(rootRel_map_iff e _ _).2 h1, (rootRel_map_iff e _ _).2 h2⟩
  root_char j u hu1 hu2 hu3 hu4 := by
    have hu1' : e.symm u * e.symm u = 1 := by
      apply e.injective
      simpa using hu1
    have hu2' : e.symm u * rootK₁ z j = rootK₁ z j * e.symm u := by
      apply e.injective
      simpa [rootK₁_map] using hu2
    have hu3' : e.symm u * rootK₂ z j = rootK₂ z j * e.symm u := by
      apply e.injective
      simpa [rootK₂_map] using hu3
    have hu4' : RootRel (rootW z j) (e.symm u) := by
      apply (rootRel_map_iff e (rootW z j) (e.symm u)).1
      simpa [rootW_map] using hu4
    rcases h.root_char j (e.symm u) hu1' hu2' hu3' hu4' with h1 | ⟨a, h2 | h2⟩
    · left
      simpa using congrArg e h1
    · right
      refine ⟨a, Or.inl ?_⟩
      rw [rootW_map]
      simpa [cjp_map] using congrArg e h2
    · right
      refine ⟨a, Or.inr ?_⟩
      rw [rootW_map]
      simpa [cjp_map] using congrArg e h2
  root_dist j a a' := by
    rw [rootW_map]
    refine ⟨fun hq => ?_, fun hq => ?_, fun hq => ?_⟩
    · exact (h.root_dist j a a').1 (e.injective (by simpa [← cjp_map] using hq))
    · exact (h.root_dist j a a').2.1 (e.injective (by simpa [← cjp_map] using hq))
    · exact (h.root_dist j a a').2.2 (e.injective (by simpa [← cjp_map] using hq))
  braid j := by
    simpa using congrArg e (h.braid j)
  braid_eq j a a' := by
    rw [rootW_map]
    intro hq
    apply h.braid_eq j a a'
    apply e.injective
    simpa [← cjp_map] using hq
  g_pow := by
    simpa [gOf_map] using congrArg e h.g_pow
  g_ne := by
    intro h1
    apply h.g_ne
    have h2 := congrArg e.symm h1
    simpa [gOf_map] using h2
  g_out α hαout k j hj := by
    let β : MulAut H := (e.trans α).trans e.symm
    have hβout : ∀ k' : H, β ≠ MulAut.conj k' := by
      intro k' hk
      exact hαout (e k') (eq_conj_of_trans_eq_conj e (by simpa [β] using hk))
    have hne := h.g_out β hβout (e.symm k) j hj
    intro hEq
    apply hne
    apply e.injective
    calc e (β (gOf r r')) = α (gOf (fun j => e (r j)) (fun j => e (r' j))) := by
          simp [β, gOf_map]
      _ = k * gOf (fun j => e (r j)) (fun j => e (r' j)) ^ j * k⁻¹ := hEq
      _ = e (e.symm k * gOf r r' ^ j * (e.symm k)⁻¹) := by
          simp [gOf_map]

theorem ModelN.ofMulEquiv {H' : Type} [Group H'] (e : H ≃* H') {z : Fin 3 → H}
    (h : ModelN H z) : ModelN H' (fun i => e (z i)) where
  cen k hk := by
    have hk' : ∀ i, e.symm k * z i = z i * e.symm k := by
      intro i
      apply e.injective
      simpa using hk i
    obtain ⟨v, hv⟩ := h.cen (e.symm k) hk'
    refine ⟨v, ?_⟩
    have := congrArg e hv
    simpa [vecElt_map] using this
  out α β := by
    let α' : MulAut H := (e.trans α).trans e.symm
    let β' : MulAut H := (e.trans β).trans e.symm
    rcases h.out α' β' with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inl ⟨e k, eq_conj_of_trans_eq_conj e (by simpa [α'] using hk)⟩
    · exact Or.inr (Or.inl ⟨e k, eq_conj_of_trans_eq_conj e (by simpa [β'] using hk)⟩)
    · refine Or.inr (Or.inr ⟨e k, eq_conj_of_trans_eq_conj e ?_⟩)
      rw [trans_mul]
      simpa [α', β'] using hk
  o2 σ hσ2 hσz N hN hfix hnorm := by
    let τ : MulAut H := (e.trans σ).trans e.symm
    let M : Subgroup H := Subgroup.comap e.toMonoidHom N
    have hτ2 : τ * τ = 1 := by
      ext x
      have hx := congrArg (fun γ : MulAut H' => e.symm (γ (e x))) hσ2
      simpa [τ] using hx
    have hτz : ∀ i, τ (z i) = z i := by
      intro i
      apply e.injective
      simpa [τ] using hσz i
    have hM : IsPGroup 2 M := IsPGroup.comap_of_injective hN e.toMonoidHom e.injective
    have hMfix : ∀ n ∈ M, τ n = n := by
      intro n hn
      have hn' : e n ∈ N := by simpa [M] using hn
      simpa [τ] using congrArg e.symm (hfix (e n) hn')
    have hMnorm : ∀ c : H, τ c = c → ∀ n ∈ M, c * n * c⁻¹ ∈ M := by
      intro c hc n hn
      have hc' : σ (e c) = e c := by simpa [τ] using congrArg e hc
      have hn' : e n ∈ N := by simpa [M] using hn
      simpa [M] using hnorm (e c) hc' (e n) hn'
    have hMbot : M = ⊥ := h.o2 τ hτ2 hτz M hM hMfix hMnorm
    refine (Subgroup.eq_bot_iff_forall N).2 ?_
    intro x hx
    have hxM : e.symm x ∈ M := by simpa [M] using hx
    have hx1 : e.symm x = 1 := by simpa [hMbot] using hxM
    simpa using congrArg e hx1
  caseA := by
    obtain ⟨t₁, t₂, h1, h2, hc1, hc2, hcen⟩ := h.caseA
    refine ⟨e t₁, e t₂, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using congrArg e h1
    · simpa using congrArg e h2
    · simpa using congrArg e hc1
    · simpa using congrArg e hc2
    · intro y hy1 hy2
      have hy1' : e.symm y * t₁ = t₁ * e.symm y := by simpa using congrArg e.symm hy1
      have hy2' : e.symm y * t₂ = t₂ * e.symm y := by simpa using congrArg e.symm hy2
      simpa using congrArg e (hcen (e.symm y) hy1' hy2')
  syl7 P hP hcomm := by
    let Q : Subgroup H := Subgroup.comap e.toMonoidHom P
    have hQ : IsPGroup 7 Q := IsPGroup.comap_of_injective hP e.toMonoidHom e.injective
    have hQcomm : ∀ p ∈ Q, p * zetaOf z = zetaOf z * p := by
      intro p hp
      have hp' : e p ∈ P := by simpa [Q] using hp
      apply e.injective
      simpa [zetaOf] using hcomm (e p) hp'
    have hcardQ : Nat.card Q = Nat.card P := by
      have hmap : Subgroup.map e.toMonoidHom Q = P := by
        simpa [Q] using Subgroup.map_comap_eq_self_of_surjective e.surjective P
      rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) (K := Q) e.injective, hmap]
    have := h.syl7 Q hQ hQcomm
    simpa [hcardQ] using this
  caseB := by
    obtain ⟨π, x₀, r, r', hB⟩ := h.caseB
    exact ⟨e π, e x₀, fun j => e (r j), fun j => e (r' j), ModelNB.ofMulEquiv e hB⟩

theorem ModelN.conj (g : H) {z : Fin 3 → H} (h : ModelN H z) :
    ModelN H (fun i => g * z i * g⁻¹) := by
  have := h.ofMulEquiv (MulAut.conj g)
  simpa only [MulAut.conj_apply] using this

end CFSG.StandardType.GGFF

end

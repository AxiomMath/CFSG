module

public import CFSG.RankThree.PartOne.S12.Node126

public section

namespace CFSG.RankThree.PartOne

namespace LAFaithful

open scoped commutatorElement

variable {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]

def unipotentRadical (B : Submodule (ZMod p) V) : Subgroup (V ≃ₗ[ZMod p] V) where
  carrier := {h | (∀ b ∈ B, h b = b) ∧ ∀ v, h v - v ∈ B}
  mul_mem' {a b} ha hb := by
    refine ⟨fun x hx => ?_, fun v => ?_⟩
    · rw [LinearEquiv.mul_apply, hb.1 x hx, ha.1 x hx]
    · have h := B.add_mem (ha.2 (b v)) (hb.2 v)
      rw [sub_add_sub_cancel] at h
      exact h
  one_mem' := ⟨fun _ _ => rfl, fun v => by simp⟩
  inv_mem' {a} ha := by
    refine ⟨fun x hx => ?_, fun v => ?_⟩
    · have h := ha.1 x hx
      rw [LinearEquiv.coe_inv]
      exact (LinearEquiv.symm_apply_eq a).2 h.symm
    · have h := B.neg_mem (ha.2 (a.symm v))
      rwa [LinearEquiv.apply_symm_apply, neg_sub] at h

theorem conj_mem_unipotentRadical {B : Submodule (ZMod p) V} {g x : V ≃ₗ[ZMod p] V}
    (hg : ∀ b ∈ B, g b ∈ B) (hg' : ∀ b ∈ B, g⁻¹ b ∈ B) (hx : x ∈ unipotentRadical B) :
    g * x * g⁻¹ ∈ unipotentRadical B := by
  refine ⟨fun b hb => ?_, fun v => ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx.1 _ (hg' b hb)]
    exact LinearEquiv.apply_symm_apply g b
  · have h := hg _ (hx.2 (g⁻¹ v))
    rw [map_sub] at h
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have e : g (g⁻¹ v) = v := LinearEquiv.apply_symm_apply g v
    rwa [e] at h

theorem pow_apply_of_mem_unipotentRadical {B : Submodule (ZMod p) V} {x : V ≃ₗ[ZMod p] V}
    (hx : x ∈ unipotentRadical B) (k : ℕ) (v : V) :
    (x ^ k) v = v + (k : ZMod p) • (x v - v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, map_smul, hx.1 _ (hx.2 v), Nat.cast_succ,
      add_smul, one_smul]
    abel

theorem pow_prime_eq_one_of_mem_unipotentRadical {B : Submodule (ZMod p) V}
    {x : V ≃ₗ[ZMod p] V} (hx : x ∈ unipotentRadical B) : x ^ p = 1 := by
  refine LinearEquiv.ext fun v => ?_
  rw [pow_apply_of_mem_unipotentRadical hx, ZMod.natCast_self, zero_smul, add_zero]
  rfl

theorem eq_one_of_mem_unipotentRadical (Γ : Subgroup (V ≃ₗ[ZMod p] V))
    {B : Submodule (ZMod p) V} (hinv : ∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B) (hcore : CFSG.pCore p Γ = ⊥)
    {x : V ≃ₗ[ZMod p] V} (hxΓ : x ∈ Γ) (hx : x ∈ unipotentRadical B) : x = 1 := by
  have hnorm : ((unipotentRadical B).subgroupOf Γ).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_unipotentRadical (hinv g g.2) (hinv g⁻¹ (Γ.inv_mem g.2)) hn
  have hpgrp : IsPGroup p ((unipotentRadical B).subgroupOf Γ) := by
    intro y
    refine ⟨1, ?_⟩
    have hy := pow_prime_eq_one_of_mem_unipotentRadical (B := B)
      (x := ((y : Γ) : V ≃ₗ[ZMod p] V)) y.2
    exact Subtype.ext (Subtype.ext (by simpa using hy))
  have hle : (unipotentRadical B).subgroupOf Γ ≤ CFSG.pCore p Γ := le_sSup ⟨hnorm, hpgrp⟩
  have hmem : (⟨x, hxΓ⟩ : Γ) ∈ (unipotentRadical B).subgroupOf Γ := hx
  have h1 := hle hmem
  rw [hcore, Subgroup.mem_bot] at h1
  exact congrArg Subtype.val h1

theorem exists_vector_generating_quotient [Fact p.Prime] [Module.Finite (ZMod p) V]
    {B : Submodule (ZMod p) V}
    (hdim : Module.finrank (ZMod p) B + 1 = Module.finrank (ZMod p) V) :
    ∃ v₀ : V, ∀ w : V, ∃ c : ZMod p, w - c • v₀ ∈ B := by
  have h1 : Module.finrank (ZMod p) (V ⧸ B) = 1 := by
    have := Submodule.finrank_quotient_add_finrank B
    omega
  obtain ⟨vbar, -, hvbar⟩ := finrank_eq_one_iff'.mp h1
  obtain ⟨v₀, rfl⟩ := Submodule.Quotient.mk_surjective B vbar
  refine ⟨v₀, fun w => ?_⟩
  obtain ⟨c, hc⟩ := hvbar (Submodule.Quotient.mk w)
  exact ⟨c, (Submodule.Quotient.eq B).1 hc.symm⟩

theorem exists_scalar_of_stabilizes [Fact p.Prime] [Module.Finite (ZMod p) V]
    {B : Submodule (ZMod p) V}
    (hdim : Module.finrank (ZMod p) B + 1 = Module.finrank (ZMod p) V)
    {g : V ≃ₗ[ZMod p] V} (hg : ∀ b ∈ B, g b ∈ B) :
    ∃ lam : ZMod p, ∀ v, g v - lam • v ∈ B := by
  obtain ⟨v₀, hv₀⟩ := exists_vector_generating_quotient hdim
  obtain ⟨lam, hlam⟩ := hv₀ (g v₀)
  refine ⟨lam, fun v => ?_⟩
  obtain ⟨μ, hμ⟩ := hv₀ v
  have e : g v - lam • v = g (v - μ • v₀) - lam • (v - μ • v₀) + μ • (g v₀ - lam • v₀) := by
    simp only [map_sub, map_smul, smul_sub, smul_comm lam μ]
    abel
  rw [e]
  exact B.add_mem (B.sub_mem (hg _ hμ) (B.smul_mem lam hμ)) (B.smul_mem μ hlam)

theorem exists_invariant_line [Fact p.Prime] [Module.Finite (ZMod p) V]
    (Γ : Subgroup (V ≃ₗ[ZMod p] V)) {B : Submodule (ZMod p) V}
    (hdim : Module.finrank (ZMod p) B + 1 = Module.finrank (ZMod p) V)
    (hinv : ∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B) (hcore : CFSG.pCore p Γ = ⊥)
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ Γ) (hgB : ∀ b ∈ B, g b = b) {lam : ZMod p}
    (hlam : ∀ v, g v - lam • v ∈ B) (h1 : lam ≠ 1) :
    ∃ ℓ : Submodule (ZMod p) V, Module.finrank (ZMod p) ℓ = 1 ∧ Disjoint ℓ B ∧
      ∀ h ∈ Γ, ∀ x ∈ ℓ, h x ∈ ℓ := by
  let T : V →ₗ[ZMod p] V := (g : V →ₗ[ZMod p] V) - lam • LinearMap.id
  have hTapp : ∀ v, T v = g v - lam • v := fun v => rfl
  have hTB : ∀ b ∈ B, T b = (1 - lam) • b := by
    intro b hb
    rw [hTapp, hgB b hb, sub_smul, one_smul]
  have hsub : (1 - lam) ≠ 0 := sub_ne_zero.2 h1.symm
  have hrange : LinearMap.range T = B := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨v, rfl⟩
      rw [hTapp]
      exact hlam v
    · intro b hb
      refine ⟨(1 - lam)⁻¹ • b, ?_⟩
      rw [hTB _ (B.smul_mem _ hb), smul_smul, mul_inv_cancel₀ hsub, one_smul]
  have hker : Module.finrank (ZMod p) (LinearMap.ker T) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker T
    rw [hrange] at h
    omega
  have hdisj : Disjoint (LinearMap.ker T) B := by
    rw [Submodule.disjoint_def]
    intro x hxk hxB
    rw [LinearMap.mem_ker, hTB x hxB] at hxk
    exact (smul_eq_zero.1 hxk).resolve_left hsub
  refine ⟨LinearMap.ker T, hker, hdisj, fun h hh x hx => ?_⟩
  have hcB : ⁅h, g⁆ ∈ unipotentRadical B := by
    refine ⟨fun b hb => ?_, fun v => ?_⟩
    · have hb' := hinv h⁻¹ (Γ.inv_mem hh) b hb
      have e : g⁻¹ b = b := (LinearEquiv.symm_apply_eq g).2 (hgB b hb).symm
      rw [commutatorElement_def, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        LinearEquiv.mul_apply, e, hgB _ hb']
      exact LinearEquiv.apply_symm_apply h b
    · have e1 : g (g⁻¹ v) = v := LinearEquiv.apply_symm_apply g v
      have e2 : h (h⁻¹ (g⁻¹ v)) = g⁻¹ v := LinearEquiv.apply_symm_apply h (g⁻¹ v)
      have e : ⁅h, g⁆ v - v =
          h (g (h⁻¹ (g⁻¹ v)) - lam • h⁻¹ (g⁻¹ v)) - (g (g⁻¹ v) - lam • g⁻¹ v) := by
        rw [map_sub, map_smul, e2, e1]
        show h (g (h⁻¹ (g⁻¹ v))) - v = _
        abel
      rw [e]
      exact B.sub_mem (hinv h hh _ (hlam _)) (hlam _)
  have hcomm : ⁅h, g⁆ = 1 := by
    refine eq_one_of_mem_unipotentRadical Γ hinv hcore ?_ hcB
    rw [commutatorElement_def]
    exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hh hg) (Γ.inv_mem hh)) (Γ.inv_mem hg)
  have hhg : h * g = g * h := commutatorElement_eq_one_iff_mul_comm.1 hcomm
  rw [LinearMap.mem_ker] at hx ⊢
  have hgx : g x = lam • x := sub_eq_zero.1 hx
  have hgh : g (h x) = lam • h x := by
    have e : (g * h) x = (h * g) x := by rw [hhg]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgx, map_smul] at e
    exact e
  exact sub_eq_zero.2 hgh

end LAFaithful

theorem laFaithful (p : ℕ) [Fact p.Prime] : LAFaithful p := by
  intro V _ _ _ Γ B hdim hinv hcore hline g hg hgB
  obtain ⟨lam, hlam⟩ := LAFaithful.exists_scalar_of_stabilizes hdim (hinv g hg)
  by_cases h1 : lam = 1
  · refine LAFaithful.eq_one_of_mem_unipotentRadical Γ hinv hcore hg ⟨hgB, fun v => ?_⟩
    simpa [h1] using hlam v
  · exact (hline (LAFaithful.exists_invariant_line Γ hdim hinv hcore hg hgB hlam h1)).elim

end CFSG.RankThree.PartOne

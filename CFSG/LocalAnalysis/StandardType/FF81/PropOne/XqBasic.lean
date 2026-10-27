module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.HCen
import Mathlib.GroupTheory.Sylow
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open scoped Pointwise

private theorem comm_map_of_comm {G K : Type*} [Group G] [Group K] {X : Subgroup G}
    (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (f : G →* K) :
    ∀ a ∈ X.map f, ∀ b ∈ X.map f, a * b = b * a := by
  intro a ha b hb
  rw [Subgroup.mem_map] at ha hb
  obtain ⟨a0, ha0, rfl⟩ := ha
  obtain ⟨b0, hb0, rfl⟩ := hb
  calc f a0 * f b0 = f (a0 * b0) := (map_mul f a0 b0).symm
    _ = f (b0 * a0) := by rw [hX a0 ha0 b0 hb0]
    _ = f b0 * f a0 := map_mul f b0 a0

private theorem abelian_sylow_quotient_of_maximal {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (A : Subgroup G)
    (hA_le : A ≤ H) (hAisP : IsPGroup 3 A)
    (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAmax : ∀ Q : Subgroup G, Q ≤ H → IsPGroup 3 Q → A ≤ Q → Q = A) :
    ∀ P : Sylow 3 (↥H ⧸ CFSG.pPrimeCore 3 ↥H), ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  have hA3H : IsPGroup 3 (A.subgroupOf H) := hAisP.comap_subtype
  have hAmaxH : ∀ Q : Subgroup ↥H, IsPGroup 3 Q → A.subgroupOf H ≤ Q →
      Q = A.subgroupOf H := by
    intro Q hQ hle
    have hQmap : IsPGroup 3 (Q.map H.subtype) := hQ.map H.subtype
    have hQle : Q.map H.subtype ≤ H := Subgroup.map_subtype_le Q
    have hAleMap : A ≤ Q.map H.subtype := by
      intro a ha
      have haH : a ∈ H := hA_le ha
      exact Subgroup.mem_map.mpr
        ⟨⟨a, haH⟩, hle (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
    have heq : Q.map H.subtype = A := hAmax (Q.map H.subtype) hQle hQmap hAleMap
    have hcomp : A.subgroupOf H = Q := by
      rw [← heq]
      exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective Q
    exact hcomp.symm
  let AS : Sylow 3 ↥H :=
    { toSubgroup := A.subgroupOf H
      isPGroup' := hA3H
      is_maximal' := by intro Q hQ hle; exact hAmaxH Q hQ hle }
  have hcommAS : ∀ a ∈ (AS : Subgroup ↥H), ∀ b ∈ (AS : Subgroup ↥H), a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hAcomm (a : G) (Subgroup.mem_subgroupOf.mp ha) (b : G) (Subgroup.mem_subgroupOf.mp hb)
  have hSylowFinite : Finite (Sylow 3 ↥H) :=
    Sylow.finite_of_finiteIndex (Classical.choice Sylow.nonempty)
  intro P x hx y hy
  let π : ↥H →* (↥H ⧸ CFSG.pPrimeCore 3 ↥H) := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥H)
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective (f := π) hπ 3 P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) AS Q
  have hQeq : (Q : Subgroup ↥H) =
      (AS : Subgroup ↥H).map (MulAut.conj g).toMonoidHom := by
    have hhom : (MulDistribMulAction.toMonoidEnd (MulAut ↥H) ↥H) (MulAut.conj g) =
        (MulAut.conj g).toMonoidHom := by
      ext x
      rfl
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hhom]
  have hcommQ : ∀ a ∈ (Q : Subgroup ↥H), ∀ b ∈ (Q : Subgroup ↥H), a * b = b * a := by
    rw [hQeq]
    exact comm_map_of_comm hcommAS (MulAut.conj g).toMonoidHom
  have hPmap : (P : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) = (Q : Subgroup ↥H).map π := by
    rw [← hQ, Sylow.coe_mapSurjective]
  have hcommP : ∀ a ∈ (P : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H)),
      ∀ b ∈ (P : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H)), a * b = b * a := by
    rw [hPmap]
    exact comm_map_of_comm hcommQ π
  exact hcommP x hx y hy

private theorem exists_conj_betaX {G : Type*} [Group G] [Finite G] {b : G} (H : Subgroup G)
    (hb3 : b ^ 3 = 1)
    (hnor : ∀ x : ↥H, b * (x : G) * b⁻¹ ∈ H)
    (hnor_inv : ∀ x : ↥H, b⁻¹ * (x : G) * b ∈ H) :
    ∃ β : MulAut (↥H ⧸ CFSG.pPrimeCore 3 ↥H), β ^ 3 = 1 ∧
      ∀ x : ↥H, ∃ x' : ↥H, (x' : G) = b * (x : G) * b⁻¹ ∧
        β (QuotientGroup.mk x) = QuotientGroup.mk x' := by
  let c : MulAut ↥H :=
    { toFun := fun x => ⟨b * (x : G) * b⁻¹, hnor x⟩
      invFun := fun x => ⟨b⁻¹ * (x : G) * b, hnor_inv x⟩
      left_inv := by intro x; apply Subtype.ext; group
      right_inv := by intro x; apply Subtype.ext; group
      map_mul' := by
        intro x y
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group }
  have hc_apply : ∀ x : ↥H, ((c x : ↥H) : G) = b * (x : G) * b⁻¹ := fun _ => rfl
  have hc_pow_apply : ∀ (k : ℕ) (x : ↥H),
      (((c ^ k) x : ↥H) : G) = b ^ k * (x : G) * (b ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ', MulAut.mul_apply, hc_apply, ih, pow_succ']
        group
  have hc3 : c ^ 3 = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [hc_pow_apply 3 x, hb3]
    simp
  have hc_char : (CFSG.pPrimeCore 3 ↥H).map c = CFSG.pPrimeCore 3 ↥H :=
    (Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (CFSG.pPrimeCore 3 ↥H).Characteristic)) c
  let β : MulAut (↥H ⧸ CFSG.pPrimeCore 3 ↥H) :=
    QuotientGroup.congr (CFSG.pPrimeCore 3 ↥H) (CFSG.pPrimeCore 3 ↥H) c hc_char
  have hβ_mk : ∀ x : ↥H, β (QuotientGroup.mk x) = QuotientGroup.mk (c x) :=
    fun x => QuotientGroup.congr_mk _ _ c hc_char x
  have hpow : ∀ (k : ℕ) (x : ↥H),
      (β ^ k) (QuotientGroup.mk x) = QuotientGroup.mk ((c ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ', MulAut.mul_apply, ih, hβ_mk, pow_succ', MulAut.mul_apply]
  have hβ3 : β ^ 3 = 1 := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥H) y
    rw [← hx]
    have h3 : (β ^ 3) ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) x) =
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) ((c ^ 3) x) := hpow 3 x
    rw [h3, hc3]
    simp
  exact ⟨β, hβ3, fun x => ⟨c x, rfl, hβ_mk x⟩⟩

theorem abelian_sylow_xq {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J B₂ A R : Subgroup G}
    (hR : RData b z J B₂ A R) :
    ∀ P : Sylow 3 (Xq R), ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  have _ := h
  exact abelian_sylow_quotient_of_maximal (Subgroup.centralizer (R : Set G)) A
    hR.A_le hR.aStar.isP hR.aStar.comm hR.A_max

theorem exists_betaX {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J B₂ A R : Subgroup G}
    (hR : RData b z J B₂ A R) :
    ∃ β : MulAut (Xq R), β ^ 3 = 1 ∧
      ∀ x : ↥(Subgroup.centralizer (R : Set G)), ∃ x' : ↥(Subgroup.centralizer (R : Set G)),
        (x' : G) = b * (x : G) * b⁻¹ ∧ β (QuotientGroup.mk x) = QuotientGroup.mk x' := by
  have hb3 : b ^ 3 = 1 := by
    have := pow_orderOf_eq_one b
    rwa [h.hypA.ord] at this
  have hRnor : ∀ r ∈ R, b * r * b⁻¹ ∈ R := by
    intro r hr
    have hz : Subgroup.zpowers (GGFF.zs z 0) ≤ R := Subgroup.zpowers_le.mpr hR.b₁_mem
    have hmem : b * r * b⁻¹ * r⁻¹ ∈ R := hz (hR.comm r hr)
    have heq : b * r * b⁻¹ = (b * r * b⁻¹ * r⁻¹) * r := by group
    rw [heq]
    exact R.mul_mem hmem hr
  have hRnor_inv : ∀ r ∈ R, b⁻¹ * r * b ∈ R := by
    have hbR : R.map (MulAut.conj b).toMonoidHom = R := by
      apply Subgroup.eq_of_le_of_card_ge
      · intro x hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨r, hr, rfl⟩ := hx
        exact hRnor r hr
      · rw [Subgroup.card_map_of_injective (MulAut.conj b).injective]
    have hbRcomap : R.comap (MulAut.conj b).toMonoidHom = R := by
      have h := Subgroup.comap_map_eq_self_of_injective
        (f := (MulAut.conj b).toMonoidHom) (MulAut.conj b).injective R
      rwa [hbR] at h
    intro r hr
    have hs : (MulAut.conj b).toMonoidHom (b⁻¹ * r * b) ∈ R := by
      change b * (b⁻¹ * r * b) * b⁻¹ ∈ R
      have heq : b * (b⁻¹ * r * b) * b⁻¹ = r := by group
      rwa [heq]
    rw [← hbRcomap]
    exact Subgroup.mem_comap.mpr hs
  have hHnor : ∀ x : ↥(Subgroup.centralizer (R : Set G)),
      b * (x : G) * b⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hbr : b⁻¹ * r * b ∈ R := hRnor_inv r hr
    have hxbr : (x : G) * (b⁻¹ * r * b) = (b⁻¹ * r * b) * (x : G) :=
      (Subgroup.mem_centralizer_iff.mp x.2 (b⁻¹ * r * b) hbr).symm
    calc r * (b * (x : G) * b⁻¹)
        = b * (b⁻¹ * r * b) * (x : G) * b⁻¹ := by group
      _ = b * ((b⁻¹ * r * b) * (x : G)) * b⁻¹ := by group
      _ = b * ((x : G) * (b⁻¹ * r * b)) * b⁻¹ := by rw [← hxbr]
      _ = b * (x : G) * b⁻¹ * r := by group
  have hHnor_inv : ∀ x : ↥(Subgroup.centralizer (R : Set G)),
      b⁻¹ * (x : G) * b ∈ Subgroup.centralizer (R : Set G) := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hbr : b * r * b⁻¹ ∈ R := hRnor r hr
    have hxbr : (x : G) * (b * r * b⁻¹) = (b * r * b⁻¹) * (x : G) :=
      (Subgroup.mem_centralizer_iff.mp x.2 (b * r * b⁻¹) hbr).symm
    calc r * (b⁻¹ * (x : G) * b)
        = b⁻¹ * (b * r * b⁻¹) * (x : G) * b := by group
      _ = b⁻¹ * ((b * r * b⁻¹) * (x : G)) * b := by group
      _ = b⁻¹ * ((x : G) * (b * r * b⁻¹)) * b := by rw [← hxbr]
      _ = b⁻¹ * (x : G) * b * r := by group
  obtain ⟨β, hβ3, hβ⟩ :=
    exists_conj_betaX (Subgroup.centralizer (R : Set G)) hb3 hHnor hHnor_inv
  exact ⟨β, hβ3, hβ⟩

end CFSG.StandardType.FF81.PropOne

end

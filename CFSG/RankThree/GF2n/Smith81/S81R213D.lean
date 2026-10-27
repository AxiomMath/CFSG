module

public import CFSG.RankThree.GF2n.Smith81.S81RRangeEq
public import CFSG.RankThree.GF2n.Smith81.S81R213X

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LRoot

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.E3LBridge
  CFSG.RankThree.GF2n.Smith81.E3LCond CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G]

section SameRoot

variable [Finite G] {M Q Z B : Subgroup G} {K : Type} [Field K]
  [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ψ : M₀.E ≃ₗ[K] Cube K}
  {φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)} {z : G}

theorem mem_comm_sup_Z_iff {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) (Tx : XAct M₀ x)
    {c : G} (hc : c ∈ Q) : c ∈ ⁅Q, Subgroup.zpowers x⁆ ⊔ Z ↔ M₀.π c ∈ Rs Tx := by
  have H : StrothHyp M Q Z := hs.hyp
  constructor
  · intro hmem
    let S : Subgroup G :=
      { carrier := {c | c ∈ Q ∧ M₀.π c ∈ Rs Tx}
        mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, by
          rw [M₀.π_mul a ha.1 b hb.1]; exact Submodule.add_mem _ ha.2 hb.2⟩
        one_mem' := ⟨Q.one_mem, by
          rw [Tim79.QuadModel.pi_one]; exact Submodule.zero_mem _⟩
        inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, by
          rw [Tim79.QuadModel.pi_inv M₀ ha.1]; exact Submodule.neg_mem _ ha.2⟩ }
    have hle : ⁅Q, Subgroup.zpowers x⁆ ⊔ Z ≤ S := by
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_le]
        intro a ha b hb
        rcases eq_one_or_eq_of_mem_zpowers hs.x_sq hb with rfl | rfl
        · simp only [commutatorElement_def, inv_one, mul_one, mul_inv_cancel]
          exact S.one_mem
        · refine ⟨comm_mem_Q H hs.memM ha, ?_⟩
          rw [Tx.pi_comm H hs.memM ha]
          refine mem_Rs.mpr ⟨M₀.π a, ?_⟩
          rw [← neg_eq_self_QE (M₀.π a - Tx.T (M₀.π a)), neg_sub]
      · intro w hw
        have hwQ : w ∈ Q := H.Z_normal.1 hw
        refine ⟨hwQ, ?_⟩
        rw [(M₀.π_ker w hwQ).mpr hw]
        exact Submodule.zero_mem _
    exact (hle hmem).2
  · intro hR
    obtain ⟨d, hdQ, z', hz', hdz⟩ := exists_comm_of_mem_Rs hs Tx hc hR
    rw [hdz]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left
      (Subgroup.commutator_mem_commutator hdQ (Subgroup.mem_zpowers x)))
      (Subgroup.mem_sup_right hz')

theorem isConj_of_mem_X {X : Subgroup G} (H : StrothHyp M Q Z) (hz : z ∈ Z) (hz1 : z ≠ 1)
    (hX : IsZConjugate Z X) {a : G} (ha : a ∈ X) (ha1 : a ≠ 1) : IsConj z a := by
  obtain ⟨g, rfl⟩ := hX
  have h1 : g⁻¹ * a * g ∈ Z := mem_conjSubgroup.mp ha
  refine isConj_of_inZClass H hz hz1 ⟨g, g⁻¹ * a * g, h1, ?_, by group⟩
  intro h
  apply ha1
  have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
  rw [this, h]
  group

theorem ActsAs.quot_mem_Q (Dt : E3LDat M Q Z B K γ M₀ ψ φ z) {a b : G} {g : GL (Fin 6) K}
    (ha : ActsAs φ a g) (hb : ActsAs φ b g) : a⁻¹ * b ∈ Q := by
  have haL := ha.mem_Lgen
  have hbL := hb.mem_Lgen
  have h1 : φ ((⟨a, haL⟩ : Lgen M (LB M Q B))⁻¹ * ⟨b, hbL⟩) = 1 := by
    rw [map_mul, map_inv, ha.phi haL, hb.phi hbL, inv_mul_cancel]
  exact (Dt.d.ker _).mp h1

theorem comm_of_prop (Dt : E3LDat M Q Z B K γ M₀ ψ φ z)
    (hRoot : ∀ x' : G, x' ∈ M → x' ∉ Q → IsConj z x' → ∀ X : Subgroup G, IsZConjugate Z X →
      x' ∈ X → (Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers x'⁆ ⊔ Z)
    {x y : G} (hxc : IsConj z x) (hxM : x ∈ M) (hxQ : x ∉ Q) (hyc : IsConj z y) (hyM : y ∈ M)
    (hyQ : y ∉ Q) {gx gy : GL (Fin 6) K} (hgx : IsTransvec K gx) (hgy : IsTransvec K gy)
    (hx : ActsAs φ x gx) (hy : ActsAs φ y gy)
    (hprop : ∃ s : K, (gy : Matrix (Fin 6) (Fin 6) K) - 1 =
      s • ((gx : Matrix (Fin 6) (Fin 6) K) - 1)) :
    x * y = y * x := by
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  obtain ⟨X, hXZ, hxX⟩ := exists_isZConjugate_mem Dt.hz hxc
  have hs : Sit M Q Z X x := ⟨H, hXZ, hxX, ne_one_of_isConj_Z Dt.hz1 hxc, hxM, hxQ⟩
  have h12 := smith_1_12 hs
  have hXM : ∀ a ∈ X, a ∈ M := fun a ha => (h12.1 ha).1
  have hXQ : ∀ a ∈ X, a ≠ 1 → a ∉ Q := by
    intro a ha ha1 haQ
    have h : a ∈ X ⊓ Q := ⟨ha, haQ⟩
    rw [h12.2, Subgroup.mem_bot] at h
    exact ha1 h
  have hroot : ∀ a ∈ X, ∃ t : K, ∃ g : GL (Fin 6) K, ActsAs φ a g ∧
      (g : Matrix (Fin 6) (Fin 6) K) = 1 + t • ((gx : Matrix (Fin 6) (Fin 6) K) - 1) := by
    intro a ha
    by_cases ha1 : a = 1
    · refine ⟨0, 1, by rw [ha1]; exact ActsAs.one, by simp⟩
    · have hac : IsConj z a := isConj_of_mem_X H Dt.hz Dt.hz1 hXZ ha ha1
      obtain ⟨g, hg, hA⟩ := Dt.actsAs hac (hXM a ha) (hXQ a ha ha1)
      have hrange : LinearMap.range (rho K gx - 1) = LinearMap.range (rho K g - 1) := by
        obtain ⟨X₁, hs₁, T₁, -, -, hRs₁⟩ := Dt.xdata hxc hxM hxQ hgx hx
        obtain ⟨X₂, hs₂, T₂, -, -, hRs₂⟩ := Dt.xdata hac (hXM a ha) (hXQ a ha ha1) hg hA
        have hS : ⁅Q, Subgroup.zpowers x⁆ ⊔ Z = ⁅Q, Subgroup.zpowers a⁆ ⊔ Z :=
          (hRoot x hxM hxQ hxc X hXZ hxX).symm.trans
            (hRoot a (hXM a ha) (hXQ a ha ha1) hac X hXZ ha)
        have hiff : ∀ r : M₀.E, r ∈ Rs T₁ ↔ r ∈ Rs T₂ := by
          intro r
          obtain ⟨c, hcQ, rfl⟩ := M₀.π_surj r
          rw [← mem_comm_sup_Z_iff hs₁ T₁ hcQ, ← mem_comm_sup_Z_iff hs₂ T₂ hcQ, hS]
        ext ξ
        have h1 : ξ ∈ LinearMap.range (rho K gx - 1) ↔ ψ.symm ξ ∈ Rs T₁ := by
          rw [hRs₁ (ψ.symm ξ), LinearEquiv.apply_symm_apply]
        have h2 : ξ ∈ LinearMap.range (rho K g - 1) ↔ ψ.symm ξ ∈ Rs T₂ := by
          rw [hRs₂ (ψ.symm ξ), LinearEquiv.apply_symm_apply]
        rw [h1, h2, hiff]
      obtain ⟨t, -, ht⟩ := eq_smul_of_range_eq hgx hg hrange
      refine ⟨t, g, hA, ?_⟩
      rw [← ht]
      abel
  choose! t g hgA hgt using hroot
  have hinj : Function.Injective (fun a : X => t a.1) := by
    intro a b hab
    have hab' : t a.1 = t b.1 := hab
    have hg_eq : g a.1 = g b.1 := by
      apply Units.ext
      rw [hgt a.1 a.2, hgt b.1 b.2, hab']
    have hq : (a.1)⁻¹ * b.1 ∈ Q := by
      apply ActsAs.quot_mem_Q Dt (hgA a.1 a.2)
      rw [hg_eq]
      exact hgA b.1 b.2
    have hqX : (a.1)⁻¹ * b.1 ∈ X := X.mul_mem (X.inv_mem a.2) b.2
    have h : (a.1)⁻¹ * b.1 ∈ X ⊓ Q := ⟨hqX, hq⟩
    rw [h12.2, Subgroup.mem_bot] at h
    exact Subtype.ext (inv_mul_eq_one.mp h)
  have hcard : Nat.card K ≤ Nat.card X := by
    have h1 : Nat.card K = Nat.card Z := Dt.hD.card
    have h2 : Nat.card Z = Nat.card X := by
      have hX' : ∃ g₀ : G, X = conjSubgroup g₀ Z := hXZ
      obtain ⟨g₀, hg₀⟩ := hX'
      subst hg₀
      exact Nat.card_congr (MulEquiv.subgroupMap (MulAut.conj g₀) Z).toEquiv
    rw [h1, h2]
  have hbij : Function.Bijective (fun a : X => t a.1) := hinj.bijective_of_nat_card_le hcard
  obtain ⟨s, hs'⟩ := hprop
  obtain ⟨⟨x₂, hx₂X⟩, hx₂t⟩ := hbij.2 s
  have hx₂t' : t x₂ = s := hx₂t
  have hgy_eq : g x₂ = gy := by
    apply Units.ext
    rw [hgt x₂ hx₂X, hx₂t', ← hs']
    abel
  have hx₂A : ActsAs φ x₂ gy := by
    rw [← hgy_eq]
    exact hgA x₂ hx₂X
  have hx₂1 : x₂ ≠ 1 := by
    intro h
    have h1 : ActsAs φ (1 : G) gy := by rw [← h]; exact hx₂A
    have h2 := ActsAs.quot_mem_Q Dt h1 hy
    rw [inv_one, one_mul] at h2
    exact hyQ h2
  have hx₂c : IsConj z x₂ := isConj_of_mem_X H Dt.hz Dt.hz1 hXZ hx₂X hx₂1
  obtain ⟨q, hqQ, hq⟩ := conj_of_phi_eq Dt hx₂c (hXM x₂ hx₂X) (hXQ x₂ hx₂X hx₂1) hyc hyM hyQ
    hgy hx₂A hy
  have hcomm_mem : ⁅q, x₂⁆ ∈ (Q ⊓ QB X) ⊔ Z := by
    rw [hRoot x₂ (hXM x₂ hx₂X) (hXQ x₂ hx₂X hx₂1) hx₂c X hXZ hx₂X]
    exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hqQ (Subgroup.mem_zpowers x₂))
  have hxcent : ∀ c ∈ (Q ⊓ QB X) ⊔ Z, x * c = c * x := by
    intro c hc
    have hle : (Q ⊓ QB X) ⊔ Z ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (fun d hd => ?_) (fun w hw => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hs.QB_comm_X hxX (Subgroup.mem_inf.mp hd).2).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h := hs.x_cent h12 w hw
        rw [mul_inv_eq_iff_eq_mul] at h
        exact h.symm
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hle hc)
    exact h.symm
  have hy_eq : y = ⁅q, x₂⁆ * x₂ := by
    rw [hq]
    simp only [commutatorElement_def]
    group
  have hxx₂ : x * x₂ = x₂ * x := hs.X_comm x hxX x₂ hx₂X
  rw [hy_eq]
  calc x * (⁅q, x₂⁆ * x₂) = (x * ⁅q, x₂⁆) * x₂ := by group
    _ = (⁅q, x₂⁆ * x) * x₂ := by rw [hxcent _ hcomm_mem]
    _ = ⁅q, x₂⁆ * (x * x₂) := by group
    _ = ⁅q, x₂⁆ * (x₂ * x) := by rw [hxx₂]
    _ = ⁅q, x₂⁆ * x₂ * x := by group

end SameRoot

end CFSG.RankThree.GF2n.Smith81.E3LRoot

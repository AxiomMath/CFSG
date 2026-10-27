module

public import CFSG.Quasithin.Background.G2SL3Setting

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem eq_sup_of_normal_closure3 [Finite G] {L U I T₀ : Subgroup G} {g h : G}
    (hL : L = oTwoUpper L) (hgL : g ∈ L) (hhL : h ∈ L) (hI : I = U ⊔ rconj U g ⊔ rconj U h)
    (hT₀U : T₀ ≤ Subgroup.normalizer (U : Set G)) (hT₀p : IsPGroup 2 T₀) (hT₀X : T₀ ≤ L ⊔ U)
    (hdec : ∀ x ∈ L ⊔ U, ∃ o ∈ T₀, ∃ i ∈ I, x = o * i) : I = L ⊔ U := by
  have hUI : U ≤ I := by rw [hI]; exact le_sup_left.trans le_sup_left
  have hrconj : ∀ k ∈ L, rconj U k ≤ L ⊔ U := by
    intro k hk y hy
    rw [mem_rconj] at hy
    have : y = k⁻¹ * (k * y * k⁻¹) * k := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (inv_mem ((le_sup_left : L ≤ L ⊔ U) hk))
      ((le_sup_right : U ≤ L ⊔ U) hy)) ((le_sup_left : L ≤ L ⊔ U) hk)
  have hIX : I ≤ L ⊔ U := by
    rw [hI]
    exact sup_le (sup_le le_sup_right (hrconj g hgL)) (hrconj h hhL)
  have hnormU : ∀ x ∈ L ⊔ U, ∀ y ∈ U, x⁻¹ * y * x ∈ I := by
    intro x hx y hy
    obtain ⟨o, ho, i, hi, rfl⟩ := hdec x hx
    have hy' : o⁻¹ * y * o ∈ U := by
      have := (Subgroup.mem_normalizer_iff''.1 (hT₀U ho) y).1 hy
      simpa using this
    have : (o * i)⁻¹ * y * (o * i) = i⁻¹ * (o⁻¹ * y * o) * i := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (inv_mem hi) (hUI hy')) hi
  have hnormR : ∀ k ∈ L, ∀ x ∈ L ⊔ U, ∀ y ∈ rconj U k, x⁻¹ * y * x ∈ I := by
    intro k hk x hx y hy
    have hy' : k * y * k⁻¹ ∈ U := mem_rconj.1 hy
    have h1 := hnormU (k * x) (Subgroup.mul_mem _ ((le_sup_left : L ≤ L ⊔ U) hk) hx) _ hy'
    have : (k * x)⁻¹ * (k * y * k⁻¹) * (k * x) = x⁻¹ * y * x := by group
    rwa [this] at h1
  have hnormI : ∀ x ∈ L ⊔ U, ∀ y ∈ I, x⁻¹ * y * x ∈ I := by
    intro x hx
    let K : Subgroup G :=
      { carrier := {y | x⁻¹ * y * x ∈ I}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          show x⁻¹ * (a * b) * x ∈ I
          have : x⁻¹ * (a * b) * x = (x⁻¹ * a * x) * (x⁻¹ * b * x) := by group
          rw [this]
          exact I.mul_mem ha hb
        inv_mem' := fun {a} ha => by
          show x⁻¹ * a⁻¹ * x ∈ I
          have : x⁻¹ * a⁻¹ * x = (x⁻¹ * a * x)⁻¹ := by group
          rw [this]
          exact I.inv_mem ha }
    have hK : I ≤ K := by
      rw [hI]
      exact sup_le (sup_le (fun y hy => hnormU x hx y hy) (fun y hy => hnormR g hgL x hx y hy))
        (fun y hy => hnormR h hhL x hx y hy)
    exact fun y hy => hK hy
  have hXnorm : L ⊔ U ≤ Subgroup.normalizer (I : Set G) := by
    refine le_normalizer_of_conj_mem fun x hx y hy => ?_
    have := hnormI x⁻¹ (inv_mem hx) y hy
    simpa using this
  have h2 : ∀ x ∈ L ⊔ U, ∃ k : ℕ, x ^ 2 ^ k ∈ I := by
    intro x hx
    obtain ⟨o, ho, i, hi, rfl⟩ := hdec x hx
    exact exists_pow_two_pow_mem_of_le_normalizer (L := I) (T := T₀)
      (fun t ht => hXnorm (hT₀X ht)) hT₀p
      (Subgroup.mul_mem _ ((le_sup_right : T₀ ≤ I ⊔ T₀) ho) ((le_sup_left : I ≤ I ⊔ T₀) hi))
  have h3 : oTwoUpper (L ⊔ U) ≤ I := oTwoUpper_le_of_pow_mem h2
  have h4 : L ≤ I := calc
    L = oTwoUpper L := hL
    _ ≤ oTwoUpper (L ⊔ U) := oTwoUpper_mono le_sup_left
    _ ≤ I := h3
  exact le_antisymm hIX (sup_le h4 hUI)

namespace L3Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L3Setting n V V₁ L T H)

include S

omit [Finite G] in
theorem psi_of_mem_rconj {k : G} (hk : k ∈ L) {v : G} (hv : v ∈ rconj V₁ k) :
    ∃ hvV : v ∈ V, ∃ c : GaloisField 2 n,
      Multiplicative.toAdd (S.D.ψ ⟨v, hvV⟩) = c • (S.D.θ ⟨k, hk⟩⁻¹ • vE (GaloisField 2 n) 0) := by
  rw [mem_rconj] at hv
  have h1 : k * v * k⁻¹ ∈ V := S.hyp.base.le_V hv
  have hvV : v ∈ V := (Subgroup.mem_normalizer_iff.1 (S.D.hnorm hk) v).2 h1
  refine ⟨hvV, ?_⟩
  obtain ⟨c, hc⟩ := (S.D.line ⟨k * v * k⁻¹, h1⟩).1 hv
  have h2 := S.D.equiv ⟨k, hk⟩ ⟨v, hvV⟩
  have h3 : conjAct V ⟨k, S.D.hnorm hk⟩ ⟨v, hvV⟩ = ⟨k * v * k⁻¹, h1⟩ :=
    Subtype.ext (by rw [conjAct_coe_apply])
  rw [h3, natAct3_apply] at h2
  have h4 := congrArg Multiplicative.toAdd h2
  rw [toAdd_ofAdd, hc] at h4
  refine ⟨c, ?_⟩
  rw [map_inv, ← smul_comm, h4, inv_smul_smul]

omit [Finite G] in
theorem span_of_sum {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h) :
    ∀ x : Fin 3 → GaloisField 2 n, ∃ a b c : GaloisField 2 n,
      x = a • vE (GaloisField 2 n) 0 + b • (S.D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0) +
        c • (S.D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0) := by
  intro x
  let T₀ : Subgroup G :=
    { carrier := {v | ∃ hv : v ∈ V, ∃ a b c : GaloisField 2 n,
        Multiplicative.toAdd (S.D.ψ ⟨v, hv⟩) = a • vE (GaloisField 2 n) 0 +
          b • (S.D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0) +
          c • (S.D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0)}
      one_mem' := ⟨V.one_mem, 0, 0, 0, by simp⟩
      mul_mem' := by
        rintro v w ⟨hv, a, b, c, hvc⟩ ⟨hw, a', b', c', hwc⟩
        refine ⟨V.mul_mem hv hw, a + a', b + b', c + c', ?_⟩
        have : S.D.ψ ⟨v * w, V.mul_mem hv hw⟩ = S.D.ψ ⟨v, hv⟩ * S.D.ψ ⟨w, hw⟩ :=
          map_mul S.D.ψ ⟨v, hv⟩ ⟨w, hw⟩
        rw [this, toAdd_mul, hvc, hwc]
        simp only [add_smul]
        abel
      inv_mem' := by
        rintro v ⟨hv, a, b, c, hvc⟩
        refine ⟨V.inv_mem hv, -a, -b, -c, ?_⟩
        have : S.D.ψ ⟨v⁻¹, V.inv_mem hv⟩ = (S.D.ψ ⟨v, hv⟩)⁻¹ := map_inv S.D.ψ ⟨v, hv⟩
        rw [this, toAdd_inv, hvc]
        simp only [neg_smul]
        abel }
  have hV₁ : V₁ ≤ T₀ := by
    intro v hv
    have hvV : v ∈ V := S.hyp.base.le_V hv
    obtain ⟨c, hc⟩ := (S.D.line ⟨v, hvV⟩).1 hv
    exact ⟨hvV, c, 0, 0, by rw [hc]; simp⟩
  have hVg : rconj V₁ g ≤ T₀ := by
    intro v hv
    obtain ⟨hvV, c, hc⟩ := S.psi_of_mem_rconj hg hv
    exact ⟨hvV, 0, c, 0, by rw [hc]; simp⟩
  have hVh : rconj V₁ h ≤ T₀ := by
    intro v hv
    obtain ⟨hvV, c, hc⟩ := S.psi_of_mem_rconj hh hv
    exact ⟨hvV, 0, 0, c, by rw [hc]; simp⟩
  have hVT : V ≤ T₀ := by
    rw [hV]
    exact sup_le (sup_le hV₁ hVg) hVh
  obtain ⟨v, hv⟩ : ∃ v : V, S.D.ψ v = Multiplicative.ofAdd x :=
    ⟨S.D.ψ.symm _, MulEquiv.apply_symm_apply _ _⟩
  obtain ⟨hv', a, b, c, habc⟩ := hVT v.2
  refine ⟨a, b, c, ?_⟩
  have : (⟨v.1, hv'⟩ : V) = v := rfl
  rw [this, hv, toAdd_ofAdd] at habc
  exact habc

theorem Qv_le_Phi_rconj {k : G} (hk : k ∈ L) :
    Qv (S.D.θ ⟨k, hk⟩⁻¹ • vE (GaloisField 2 n) 0) ≤
      ((rconj (conjClosure V H) k).subgroupOf (L ⊔ conjClosure V H)).map S.Phi := by
  intro A hA
  set γ := S.D.θ ⟨k, hk⟩⁻¹ with hγ
  have hr : γ⁻¹ * A * γ ∈ Qv (vE (GaloisField 2 n) 0) := by
    have := (mem_Qv_conj γ (γ⁻¹ * A * γ)).1 (by simpa [mul_assoc] using hA)
    exact this
  rw [← S.Ubar_eq_Qv] at hr
  obtain ⟨u, hu⟩ := hr
  have hkLU : k ∈ L ⊔ conjClosure V H := (le_sup_left : L ≤ L ⊔ conjClosure V H) hk
  have huLU : (u : G) ∈ L ⊔ conjClosure V H :=
    (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u.2
  have hguLU : k⁻¹ * (u : G) * k ∈ L ⊔ conjClosure V H :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (inv_mem hkLU) huLU) hkLU
  refine ⟨⟨k⁻¹ * (u : G) * k, hguLU⟩, Subgroup.mem_subgroupOf.2 (inv_mul_mul_mem_rconj u.2), ?_⟩
  have h1 : (⟨k⁻¹ * (u : G) * k, hguLU⟩ : ↥(L ⊔ conjClosure V H)) =
      ⟨k, hkLU⟩⁻¹ * ⟨u, huLU⟩ * ⟨k, hkLU⟩ := Subtype.ext (by simp)
  rw [h1, map_mul, map_mul, map_inv, S.Phi_of_L ⟨k, hk⟩]
  have h2 : S.Phi ⟨u, huLU⟩ = γ⁻¹ * A * γ := hu
  rw [h2]
  simp only [hγ, map_inv, inv_inv]
  group

theorem Phi_I_surjective3 {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h) :
    ∀ A : SL(3, GaloisField 2 n), ∃ i : ↥(L ⊔ conjClosure V H),
      (i : G) ∈ conjClosure V H ⊔ rconj (conjClosure V H) g ⊔ rconj (conjClosure V H) h ∧
        S.Phi i = A := by
  set U := conjClosure V H with hU
  let J : Subgroup SL(3, GaloisField 2 n) :=
    ((U ⊔ rconj U g ⊔ rconj U h).subgroupOf (L ⊔ U)).map S.Phi
  have hJ1 : Qv (vE (GaloisField 2 n) 0) ≤ J := by
    rw [← S.Ubar_eq_Qv]
    rintro _ ⟨u, rfl⟩
    exact ⟨⟨u, (le_sup_right : U ≤ L ⊔ U) u.2⟩,
      Subgroup.mem_subgroupOf.2 ((le_sup_left : U ≤ U ⊔ rconj U g).trans le_sup_left u.2), rfl⟩
  have hJ2 : Qv (S.D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0) ≤ J := by
    refine (S.Qv_le_Phi_rconj hg).trans ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.2 ((le_sup_right : rconj U g ≤ U ⊔ rconj U g).trans
      le_sup_left (Subgroup.mem_subgroupOf.1 hx)), rfl⟩
  have hJ3 : Qv (S.D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0) ≤ J := by
    refine (S.Qv_le_Phi_rconj hh).trans ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.2 ((le_sup_right : rconj U h ≤ (U ⊔ rconj U g) ⊔ rconj U h)
      (Subgroup.mem_subgroupOf.1 hx)), rfl⟩
  intro A
  have hA : A ∈ J := by
    have : A ∈ Qv (vE (GaloisField 2 n) 0) ⊔ Qv (S.D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0) ⊔
        Qv (S.D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0) := by
      rw [Qv_sup_basis (S.span_of_sum hg hh hV)]
      exact Subgroup.mem_top A
    exact (sup_le (sup_le hJ1 hJ2) hJ3) this
  obtain ⟨i, hi, rfl⟩ := hA
  exact ⟨i, Subgroup.mem_subgroupOf.1 hi, rfl⟩

theorem G25_two_aux {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h) :
    conjClosure V H ⊔ rconj (conjClosure V H) g ⊔ rconj (conjClosure V H) h =
      L ⊔ conjClosure V H := by
  set U := conjClosure V H with hU
  have hdec : ∀ x ∈ L ⊔ U, ∃ o ∈ pCoreOf 2 (L ⊔ T) ⊓ (L ⊔ U),
      ∃ i ∈ U ⊔ rconj U g ⊔ rconj U h, x = o * i := by
    intro x hx
    obtain ⟨i, hiI, hi⟩ := S.Phi_I_surjective3 hg hh hV (S.Phi ⟨x, hx⟩)
    refine ⟨x * (i : G)⁻¹, ⟨?_, ?_⟩, i, hiI, by group⟩
    · have h1 : S.Phi (⟨x, hx⟩ * i⁻¹) = 1 := by
        rw [map_mul, map_inv, ← hi, mul_inv_cancel]
      exact (S.Phi_eq_one_iff _).1 h1
    · exact Subgroup.mul_mem _ hx (inv_mem i.2)
  exact eq_sup_of_normal_closure3 (T₀ := pCoreOf 2 (L ⊔ T) ⊓ (L ⊔ U)) S.hyp.base.oTwo_eq hg hh rfl
    (fun x hx => S.hyp.base.G22_three.2 (S.O_le_T hx.1))
    ((pCoreOf_isPGroup 2 (L ⊔ T)).to_le inf_le_left) inf_le_right hdec

end L3Setting

namespace AlmostSpecialL3Hyp

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialL3Hyp n V V₁ L T H)

include hyp

theorem G25_two {g h : G} (hg : g ∈ L) (hh : h ∈ L)
    (hV : V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h) :
    conjClosure V H ⊔ rconj (conjClosure V H) g ⊔ rconj (conjClosure V H) h =
      L ⊔ conjClosure V H := by
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let S : L3Setting n V V₁ L T H := ⟨hyp, D⟩
  exact S.G25_two_aux hg hh hV

end AlmostSpecialL3Hyp

end CFSG.Quasithin

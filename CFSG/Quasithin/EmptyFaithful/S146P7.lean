module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F9Pairing

public section

namespace CFSG.Quasithin

open scoped commutatorElement IsMulCommutative

section Abstract

variable {Γ : Type*} [Group Γ]

theorem exists_pComplement_P7 [Finite Γ] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X Q : Subgroup Γ}
    (hXnQ : ∀ g ∈ X, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hXQ : ∀ x ∈ X, ∃ k : ℕ, x ^ p ^ k ∈ Q) :
    ∃ P : Subgroup Γ, P ≤ X ∧ Odd (Nat.card P) ∧ ∀ g ∈ X, ∃ a ∈ P, ∃ q ∈ Q, g = a * q := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hNn : (Q.subgroupOf X).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have := hXnQ g g.2 n hn
      simpa using this⟩
  have : (Q.subgroupOf X).Normal := hNn
  let π : X →* X ⧸ Q.subgroupOf X := QuotientGroup.mk' (Q.subgroupOf X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  obtain ⟨R⟩ : Nonempty (Sylow p X) := inferInstance
  have hpg : IsPGroup p (X ⧸ Q.subgroupOf X) := by
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    obtain ⟨k, hk⟩ := hXQ x x.2
    refine ⟨k, ?_⟩
    have hmem : x ^ p ^ k ∈ Q.subgroupOf X := Subgroup.mem_subgroupOf.mpr (by simpa using hk)
    have := (QuotientGroup.eq_one_iff _).mpr hmem
    simpa [π] using this
  let S : Sylow p (X ⧸ Q.subgroupOf X) := Sylow.mapSurjective hπ R
  have hS : (S : Subgroup (X ⧸ Q.subgroupOf X)) = ⊤ :=
    (S.is_maximal' (Q := ⊤) (hpg.of_equiv Subgroup.topEquiv.symm) le_top).symm
  have hSmap : (S : Subgroup (X ⧸ Q.subgroupOf X)) = (R : Subgroup X).map π :=
    Sylow.coe_mapSurjective hπ R
  refine ⟨(R : Subgroup X).map X.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨r, -, rfl⟩
    exact r.2
  · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp R.isPGroup'
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    show Odd (Nat.card (R : Subgroup X))
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  · intro g hg
    have hmem : π ⟨g, hg⟩ ∈ (R : Subgroup X).map π := by
      rw [← hSmap, hS]
      exact Subgroup.mem_top _
    obtain ⟨r, hr, hrg⟩ := Subgroup.mem_map.mp hmem
    refine ⟨(r : Γ), ⟨r, hr, rfl⟩, (r : Γ)⁻¹ * g, ?_, by group⟩
    have h1 : r⁻¹ * ⟨g, hg⟩ ∈ Q.subgroupOf X := QuotientGroup.eq.mp hrg
    simpa using Subgroup.mem_subgroupOf.mp h1


theorem coprime_dec_exact_P7 [Finite Γ] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {U X Q T : Subgroup Γ}
    (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hU2 : ∀ x ∈ U, x ^ 2 = 1)
    (hXU : ∀ g ∈ X, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hQU : ∀ q ∈ Q, ∀ u ∈ U, q * u * q⁻¹ = u)
    (hXnQ : ∀ g ∈ X, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hXQ : ∀ x ∈ X, ∃ k : ℕ, x ^ p ^ k ∈ Q)
    (hTU : ∀ τ ∈ T, ∀ u ∈ U, τ * u * τ⁻¹ ∈ U) (hTX : ∀ τ ∈ T, ∀ g ∈ X, τ * g * τ⁻¹ ∈ X)
    {w : Γ} (hw : w ∈ U) (hwT : ∀ τ ∈ T, τ * w * τ⁻¹ = w) :
    ∃ k ∈ ⁅U, X⁆, ∃ c ∈ U, (∀ g ∈ X ⊔ T, g * c * g⁻¹ = c) ∧ w = k * c := by
  classical
  obtain ⟨P, hPX, hPodd, hPQ⟩ := exists_pComplement_P7 hp hp2 hXnQ hXQ
  let _ : Fintype P := Fintype.ofFinite P
  have _ : IsMulCommutative U := ⟨⟨fun x y => Subtype.ext (hUc x x.2 y y.2)⟩⟩
  have hconj : ∀ b ∈ P, ∀ k ∈ U, b * k * b⁻¹ ∈ U := fun b hb k hk => hXU b (hPX hb) k hk
  let f : P → U → U := fun b k => ⟨(b : Γ) * k * (b : Γ)⁻¹, hconj b b.2 k k.2⟩
  have hfmul : ∀ b k₁ k₂, f b (k₁ * k₂) = f b k₁ * f b k₂ := fun b k₁ k₂ =>
    Subtype.ext (by simp only [f, Subgroup.coe_mul]; group)
  let fh : P → U →* U := fun b => MonoidHom.mk' (f b) (hfmul b)
  let σ : U →* U := MonoidHom.mk' (fun k => ∏ b : P, f b k) fun k₁ k₂ => by
    show ∏ b, f b (k₁ * k₂) = (∏ b, f b k₁) * ∏ b, f b k₂
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun b _ => hfmul b k₁ k₂
  have hσ : ∀ k, σ k = ∏ b : P, f b k := fun k => rfl
  have hfcoe : ∀ b k, ((f b k : U) : Γ) = (b : Γ) * k * (b : Γ)⁻¹ := fun b k => rfl
  have hff : ∀ a b k, f a (f b k) = f (a * b) k := fun a b k =>
    Subtype.ext (by simp only [hfcoe, Subgroup.coe_mul, mul_inv_rev]; group)
  have hσfix : ∀ (a : P) (k : U), f a (σ k) = σ k := by
    intro a k
    have h1 : f a (σ k) = ∏ b : P, f a (f b k) := by
      rw [hσ]
      exact map_prod (fh a) _ _
    rw [h1, hσ]
    exact Fintype.prod_equiv (Equiv.mulLeft a) _ _ fun b => by simp only [Equiv.coe_mulLeft, hff]
  have hσconj : ∀ (a : P) (k : U), σ (f a k) = σ k := by
    intro a k
    rw [hσ, hσ]
    exact Fintype.prod_equiv (Equiv.mulRight a) _ _ fun b => by simp only [Equiv.coe_mulRight, hff]
  have hodd2 : ∀ x : U, x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hU2 x x.2)
  have hpow : ∀ x : U, x ^ Fintype.card P = x := by
    intro x
    obtain ⟨m, hm⟩ := hPodd
    rw [← Nat.card_eq_fintype_card, hm, pow_succ, pow_mul, hodd2, one_pow, one_mul]
  have hσid : ∀ x : U, (∀ a : P, f a x = x) → σ x = x := by
    intro x hx
    rw [hσ]
    simp only [hx, Finset.prod_const, Finset.card_univ]
    exact hpow x
  have hσdec : ∀ k : U, σ k = (∏ b : P, f b k * k⁻¹) * k := by
    intro k
    rw [hσ]
    calc ∏ b : P, f b k = ∏ b : P, ((f b k * k⁻¹) * k) :=
          Finset.prod_congr rfl fun b _ => by group
      _ = (∏ b : P, f b k * k⁻¹) * ∏ b : P, k := Finset.prod_mul_distrib
      _ = (∏ b : P, f b k * k⁻¹) * k := by rw [Finset.prod_const, Finset.card_univ, hpow]
  have hker : ⁅U, X⁆ ≤ σ.ker.map U.subtype := by
    refine Subgroup.commutator_le.mpr fun u hu g hg => ?_
    obtain ⟨a, ha, q, hq, rfl⟩ := hPQ g hg
    have hgu : (a * q) * u * (a * q)⁻¹ ∈ U := hXU _ hg u hu
    refine ⟨(⟨u, hu⟩ : U) * (⟨(a * q) * u * (a * q)⁻¹, hgu⟩ : U)⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
      have e : (⟨(a * q) * u * (a * q)⁻¹, hgu⟩ : U) = f ⟨a, ha⟩ ⟨u, hu⟩ := by
        apply Subtype.ext
        show (a * q) * u * (a * q)⁻¹ = a * u * a⁻¹
        calc (a * q) * u * (a * q)⁻¹ = a * (q * u * q⁻¹) * a⁻¹ := by group
          _ = a * u * a⁻¹ := by rw [hQU q hq u hu]
      rw [e, hσconj]
    · show u * ((a * q) * u * (a * q)⁻¹)⁻¹ = ⁅u, a * q⁆
      rw [commutatorElement_def]
      group
  have hinf : ∀ x : Γ, x ∈ ⁅U, X⁆ → x ∈ U → (∀ g ∈ X, g * x * g⁻¹ = x) → x = 1 := by
    intro x hxE hxU hxX
    obtain ⟨y, hy, rfl⟩ := hker hxE
    have hyfix : ∀ a : P, f a y = y := fun a => Subtype.ext (hxX a (hPX a.2))
    have h1 : σ y = y := hσid y hyfix
    have h2 : σ y = 1 := MonoidHom.mem_ker.mp hy
    rw [h2] at h1
    rw [← h1]
    rfl
  have hTcomm : ∀ τ ∈ T, ∀ x ∈ ⁅U, X⁆, τ * x * τ⁻¹ ∈ ⁅U, X⁆ := by
    intro τ hτ
    have hle : ⁅U, X⁆ ≤ (⁅U, X⁆).comap (MulAut.conj τ).toMonoidHom := by
      refine Subgroup.commutator_le.mpr fun u hu g hg => ?_
      rw [Subgroup.mem_comap]
      have e : (MulAut.conj τ).toMonoidHom ⁅u, g⁆ = ⁅τ * u * τ⁻¹, τ * g * τ⁻¹⁆ := by
        simp only [commutatorElement_def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator (hTU τ hτ u hu) (hTX τ hτ g hg)
    intro x hx
    have := hle hx
    simpa [Subgroup.mem_comap, MulAut.conj_apply] using this
  let u₀ : U := ⟨w, hw⟩
  let c₁ : U := σ u₀
  let k₁ : U := (∏ b : P, f b u₀ * u₀⁻¹)⁻¹
  have hdec : u₀ = k₁ * c₁ := by
    show u₀ = (∏ b : P, f b u₀ * u₀⁻¹)⁻¹ * σ u₀
    rw [hσdec u₀]
    group
  have hwkc : w = (k₁ : Γ) * (c₁ : Γ) := congrArg Subtype.val hdec
  have hkE : (k₁ : Γ) ∈ ⁅U, X⁆ := by
    have hbase : ∀ b : P, ((f b u₀ * u₀⁻¹ : U) : Γ) ∈ ⁅U, X⁆ := by
      intro b
      have hmem : ⁅w, (b : Γ)⁆ ∈ ⁅U, X⁆ := Subgroup.commutator_mem_commutator hw (hPX b.2)
      have e : ((f b u₀ * u₀⁻¹ : U) : Γ) = ⁅w, (b : Γ)⁆⁻¹ := by
        show (b : Γ) * w * (b : Γ)⁻¹ * w⁻¹ = ⁅w, (b : Γ)⁆⁻¹
        rw [commutatorElement_def]
        group
      rw [e]
      exact (⁅U, X⁆).inv_mem hmem
    have hprod : ((∏ b : P, f b u₀ * u₀⁻¹ : U) : Γ) ∈ ⁅U, X⁆ :=
      Finset.prod_induction _ (fun x : U => (x : Γ) ∈ ⁅U, X⁆)
        (fun a b ha hb => by simpa using (⁅U, X⁆).mul_mem ha hb)
        (by simp) (fun b _ => hbase b)
    show (((∏ b : P, f b u₀ * u₀⁻¹)⁻¹ : U) : Γ) ∈ ⁅U, X⁆
    rw [Subgroup.coe_inv]
    exact (⁅U, X⁆).inv_mem hprod
  have hc₁X : ∀ g ∈ X, g * (c₁ : Γ) * g⁻¹ = c₁ := by
    intro g hg
    obtain ⟨a, ha, q, hq, rfl⟩ := hPQ g hg
    calc (a * q) * (c₁ : Γ) * (a * q)⁻¹ = a * (q * (c₁ : Γ) * q⁻¹) * a⁻¹ := by group
      _ = a * (c₁ : Γ) * a⁻¹ := by rw [hQU q hq c₁ c₁.2]
      _ = c₁ := congrArg Subtype.val (hσfix ⟨a, ha⟩ u₀)
  have hc₁T : ∀ τ ∈ T, τ * (c₁ : Γ) * τ⁻¹ = c₁ := by
    intro τ hτ
    have hk'U : τ * (k₁ : Γ) * τ⁻¹ ∈ U := hTU τ hτ _ k₁.2
    have hc'U : τ * (c₁ : Γ) * τ⁻¹ ∈ U := hTU τ hτ _ c₁.2
    have hk'E : τ * (k₁ : Γ) * τ⁻¹ ∈ ⁅U, X⁆ := hTcomm τ hτ _ hkE
    have hc'X : ∀ g ∈ X, g * (τ * (c₁ : Γ) * τ⁻¹) * g⁻¹ = τ * (c₁ : Γ) * τ⁻¹ := by
      intro g hg
      have h1 := hc₁X _ (hTX τ⁻¹ (T.inv_mem hτ) g hg)
      calc g * (τ * (c₁ : Γ) * τ⁻¹) * g⁻¹
          = τ * (τ⁻¹ * g * τ⁻¹⁻¹ * (c₁ : Γ) * (τ⁻¹ * g * τ⁻¹⁻¹)⁻¹) * τ⁻¹ := by group
        _ = τ * (c₁ : Γ) * τ⁻¹ := by rw [h1]
    have hprod : (τ * (k₁ : Γ) * τ⁻¹) * (τ * (c₁ : Γ) * τ⁻¹) = (k₁ : Γ) * c₁ := by
      have h1 := hwT τ hτ
      rw [hwkc] at h1
      rw [← h1]
      group
    have hx : (k₁ : Γ)⁻¹ * (τ * (k₁ : Γ) * τ⁻¹) = 1 := by
      refine hinf _ ((⁅U, X⁆).mul_mem ((⁅U, X⁆).inv_mem hkE) hk'E)
        (U.mul_mem (U.inv_mem k₁.2) hk'U) fun g hg => ?_
      have hx2 : (k₁ : Γ)⁻¹ * (τ * (k₁ : Γ) * τ⁻¹) = (c₁ : Γ) * (τ * (c₁ : Γ) * τ⁻¹)⁻¹ := by
        have : (τ * (k₁ : Γ) * τ⁻¹) = (k₁ : Γ) * ((c₁ : Γ) * (τ * (c₁ : Γ) * τ⁻¹)⁻¹) := by
          calc τ * (k₁ : Γ) * τ⁻¹
              = ((τ * (k₁ : Γ) * τ⁻¹) * (τ * (c₁ : Γ) * τ⁻¹)) * (τ * (c₁ : Γ) * τ⁻¹)⁻¹ := by group
            _ = ((k₁ : Γ) * c₁) * (τ * (c₁ : Γ) * τ⁻¹)⁻¹ := by rw [hprod]
            _ = (k₁ : Γ) * ((c₁ : Γ) * (τ * (c₁ : Γ) * τ⁻¹)⁻¹) := by group
        rw [this]
        group
      rw [hx2]
      have e1 := hc₁X g hg
      have e2 := hc'X g hg
      calc g * ((c₁ : Γ) * (τ * (c₁ : Γ) * τ⁻¹)⁻¹) * g⁻¹
          = (g * (c₁ : Γ) * g⁻¹) * (g * (τ * (c₁ : Γ) * τ⁻¹) * g⁻¹)⁻¹ := by group
        _ = (c₁ : Γ) * (τ * (c₁ : Γ) * τ⁻¹)⁻¹ := by rw [e1, e2]
    have hk'eq : τ * (k₁ : Γ) * τ⁻¹ = k₁ := (inv_mul_eq_one.mp hx).symm
    have : τ * (c₁ : Γ) * τ⁻¹ = c₁ := by
      rw [hk'eq] at hprod
      exact mul_left_cancel hprod
    exact this

  refine ⟨k₁, hkE, c₁, c₁.2, ?_, hwkc⟩
  intro g hg
  have hsup : X ⊔ T ≤ Subgroup.centralizer ({(c₁ : Γ)} : Set Γ) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact mul_inv_eq_iff_eq_mul.mp (hc₁X x hx)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact mul_inv_eq_iff_eq_mul.mp (hc₁T x hx)
  have := Subgroup.mem_centralizer_singleton_iff.mp (hsup hg)
  rw [mul_inv_eq_iff_eq_mul]
  exact this

end Abstract

section Quotient

variable {G : Type} [Group G] [Finite G]

theorem decomp_mod_central_P7 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G₁ Z U X Q T : Subgroup G}
    (hZ : ∀ x ∈ G₁, ∀ b ∈ Z, x * b = b * x)
    (hUG : U ≤ G₁) (hXG : X ≤ G₁) (hTG : T ≤ G₁)
    (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hU2 : ∀ x ∈ U, x ^ 2 = 1)
    (hXU : ∀ g ∈ X, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hTU : ∀ τ ∈ T, ∀ u ∈ U, τ * u * τ⁻¹ ∈ U)
    (hTX : ∀ τ ∈ T, ∀ g ∈ X, τ * g * τ⁻¹ ∈ X)
    (hQU : ∀ q ∈ Q, ∀ u ∈ U, q * u * q⁻¹ * u⁻¹ ∈ Z)
    (hXnQ : ∀ g ∈ X, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hXQ : ∀ x ∈ X, ∃ k : ℕ, x ^ p ^ k ∈ Q)
    {w : G} (hw : w ∈ U) (hwT : ∀ τ ∈ T, τ * w * τ⁻¹ * w⁻¹ ∈ Z) :
    ∃ k ∈ ⁅U, X⁆, ∃ c ∈ U, (∀ g ∈ X ⊔ T, g * c * g⁻¹ * c⁻¹ ∈ Z) ∧ w * (k * c)⁻¹ ∈ Z := by
  classical
  have hZn : (Z.subgroupOf G₁).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have h1 : (g : G) * n = n * g := hZ g g.2 n hn
      have : ((g * n * g⁻¹ : G₁) : G) = n := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [h1]
        group
      rw [this]
      exact hn⟩
  let π : G₁ →* G₁ ⧸ Z.subgroupOf G₁ := QuotientGroup.mk' _
  let img : Subgroup G → Subgroup (G₁ ⧸ Z.subgroupOf G₁) := fun S => (S.subgroupOf G₁).map π
  have mem_img : ∀ (S : Subgroup G) (y : G₁ ⧸ Z.subgroupOf G₁),
      y ∈ img S ↔ ∃ x : G₁, (x : G) ∈ S ∧ π x = y := by
    intro S y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hπ1 : ∀ x : G₁, π x = 1 ↔ (x : G) ∈ Z := fun x =>
    (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf
  let w₁ : G₁ := ⟨w, hUG hw⟩
  have hkey := coprime_dec_exact_P7 (Γ := G₁ ⧸ Z.subgroupOf G₁) hp hp2 (U := img U) (X := img X)
    (Q := img Q) (T := img T) (w := π w₁)
    (by
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (mem_img U a).mp ha
      obtain ⟨y, hy, rfl⟩ := (mem_img U b).mp hb
      rw [← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext (hUc x hx y hy)))
    (by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := (mem_img U a).mp ha
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hU2 x hx)
      rw [this, map_one])
    (by
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (mem_img X a).mp ha
      obtain ⟨y, hy, rfl⟩ := (mem_img U b).mp hb
      refine (mem_img U _).mpr ⟨x * y * x⁻¹, ?_, by simp⟩
      simpa using hXU x hx y hy)
    (by
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (mem_img Q a).mp ha
      obtain ⟨y, hy, rfl⟩ := (mem_img U b).mp hb
      have h1 : π (x * y * x⁻¹ * y⁻¹) = 1 := (hπ1 _).mpr (by simpa using hQU x hx y hy)
      have h2 : π x * π y * (π x)⁻¹ * (π y)⁻¹ = 1 := by simpa [map_mul, map_inv] using h1
      exact mul_inv_eq_one.mp h2)
    (by
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (mem_img X a).mp ha
      obtain ⟨y, hy, rfl⟩ := (mem_img Q b).mp hb
      refine (mem_img Q _).mpr ⟨x * y * x⁻¹, ?_, by simp⟩
      simpa using hXnQ x hx y hy)
    (by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := (mem_img X a).mp ha
      obtain ⟨k, hk⟩ := hXQ x hx
      exact ⟨k, (mem_img Q _).mpr ⟨x ^ p ^ k, by simpa using hk, by simp⟩⟩)
    (by
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (mem_img T a).mp ha
      obtain ⟨y, hy, rfl⟩ := (mem_img U b).mp hb
      refine (mem_img U _).mpr ⟨x * y * x⁻¹, ?_, by simp⟩
      simpa using hTU x hx y hy)
    (by
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (mem_img T a).mp ha
      obtain ⟨y, hy, rfl⟩ := (mem_img X b).mp hb
      refine (mem_img X _).mpr ⟨x * y * x⁻¹, ?_, by simp⟩
      simpa using hTX x hx y hy)
    ((mem_img U _).mpr ⟨w₁, hw, rfl⟩)
    (by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := (mem_img T a).mp ha
      have h1 : π (x * w₁ * x⁻¹ * w₁⁻¹) = 1 := (hπ1 _).mpr (by simpa [w₁] using hwT x hx)
      have h2 : π x * π w₁ * (π x)⁻¹ * (π w₁)⁻¹ = 1 := by simpa [map_mul, map_inv] using h1
      exact mul_inv_eq_one.mp h2)
  obtain ⟨kbar, hkbar, cbar, hcbarU, hcbar, hwkc⟩ := hkey
  have hkbar' : kbar ∈ (⁅U.subgroupOf G₁, X.subgroupOf G₁⁆).map π := by
    rw [Subgroup.map_commutator]
    exact hkbar
  obtain ⟨k', hk', hk'π⟩ := Subgroup.mem_map.mp hkbar'
  have hkE : (k' : G) ∈ ⁅U, X⁆ := by
    have := Subgroup.mem_map_of_mem G₁.subtype hk'
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hUG, inf_of_le_left hXG] at this
    exact this
  obtain ⟨c', hc'U, hc'π⟩ := (mem_img U cbar).mp hcbarU
  refine ⟨k', hkE, c', hc'U, ?_, ?_⟩
  · intro g hg
    have hgG : g ∈ G₁ := (sup_le hXG hTG) hg
    have hg' : π ⟨g, hgG⟩ ∈ img X ⊔ img T := by
      have h1 : (⟨g, hgG⟩ : G₁) ∈ (X ⊔ T).subgroupOf G₁ := Subgroup.mem_subgroupOf.mpr hg
      rw [Subgroup.subgroupOf_sup hXG hTG] at h1
      have h2 := Subgroup.mem_map_of_mem π h1
      rwa [Subgroup.map_sup] at h2
    have h1 := hcbar _ hg'
    rw [← hc'π] at h1
    have h2 : π (⟨g, hgG⟩ * c' * ⟨g, hgG⟩⁻¹ * c'⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [h1]
      group
    simpa using (hπ1 _).mp h2
  · have h1 : π (w₁ * (k' * c')⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hk'π, hc'π, hwkc, mul_inv_cancel]
    simpa [w₁] using (hπ1 _).mp h1

end Quotient

end CFSG.Quasithin

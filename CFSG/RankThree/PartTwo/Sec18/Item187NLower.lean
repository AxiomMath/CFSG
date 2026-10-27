module

public import CFSG.RankThree.PartTwo.Sec18.Item187NSzFixed
import CFSG.RankThree.PartTwo.Sec18.Item187NChief
import CFSG.GF2Type.Smith1980Orth.S4Fixed

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

section Lower

variable {G : Type} [Group G] [Finite G]

theorem eight_le_card_inf_centralizer {c : G} (hc3 : c ^ 3 = 1)
    {P Kt Q : Subgroup G} (hP2 : IsPGroup 2 P) (hQ2 : IsPGroup 2 Q) (hQKt : Q ≤ Kt)
    (hKtQ : Kt ≤ Subgroup.normalizer (Q : Set G)) (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (hKtP : Kt ≤ Subgroup.normalizer (P : Set G)) (hcP : c ∈ Subgroup.normalizer (P : Set G))
    (hcKt : c ∈ Subgroup.normalizer (Kt : Set G))
    (hCP : Kt ⊓ Subgroup.centralizer (P : Set G) ≤ P)
    {T : Type} [Group T] (π : ↥Kt →* T) (hπ : Function.Surjective π)
    (hker : π.ker = Q.subgroupOf Kt) {n : ℕ} (hSz : CFSG.Blueprint.SuzukiModel T 2 n)
    (α : MulAut T) (hα1 : α ≠ 1) (hα3 : α ^ 3 = 1)
    (hα : ∀ x : ↥Kt, ∃ x' : ↥Kt, (x' : G) = c * x * c⁻¹ ∧ π x' = α (π x))
    {y : ↥Kt} (hy : orderOf (y : G) = 5) :
    8 ≤ Nat.card ↥(P ⊓ Subgroup.centralizer ({c} : Set G)) := by
  classical
  set Γ : Subgroup G := Kt ⊔ Subgroup.zpowers c with hΓdef
  have hΓP : Γ ≤ Subgroup.normalizer (P : Set G) := sup_le hKtP (Subgroup.zpowers_le.mpr hcP)
  have hΓQ : Γ ≤ Subgroup.normalizer (Q : Set G) := sup_le hKtQ (Subgroup.zpowers_le.mpr hcQ)
  have hQΓ : Q ≤ Γ := hQKt.trans le_sup_left
  have hyΓ : (y : G) ∈ Γ := Subgroup.mem_sup_left y.2
  have hyodd : Odd (orderOf (y : G)) := by rw [hy]; decide
  have hyP : (y : G) ∉ P := by
    intro h
    obtain ⟨k, hk⟩ := hP2 ⟨(y : G), h⟩
    have h1 : (y : G) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have h2 : orderOf (y : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    rw [hy] at h2
    have h3 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h2
    omega
  have hex : ∃ x ∈ P, (y : G) * x * (y : G)⁻¹ ≠ x := by
    by_contra hcon
    push Not at hcon
    apply hyP
    have hcen : (y : G) ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := hcon x hx
      calc x * (y : G) = ((y : G) * x * (y : G)⁻¹) * (y : G) := by rw [h1]
        _ = (y : G) * x := by group
    exact hCP (Subgroup.mem_inf.mpr ⟨y.2, hcen⟩)
  obtain ⟨W₀, W₁, h01, h1P, hΓ0, hΓ1, h10, hcomm, hsq, hirr, x₀, hx₀, hx₀'⟩ :=
    exists_chiefFactor hP2 hΓP hyΓ hyodd hex
  haveI hnorm : (W₀.subgroupOf W₁).Normal := normal_subgroupOf_of_le_normalizer h01 h10
  have hW₁2 : IsPGroup 2 W₁ := hP2.to_le h1P
  have hW₀2 : IsPGroup 2 W₀ := hP2.to_le (h01.trans h1P)
  have hKt0 : Kt ≤ Subgroup.normalizer (W₀ : Set G) := le_sup_left.trans hΓ0
  have hKt1 : Kt ≤ Subgroup.normalizer (W₁ : Set G) := le_sup_left.trans hΓ1
  have hcΓ0 : Subgroup.zpowers c ≤ Subgroup.normalizer (W₀ : Set G) := le_sup_right.trans hΓ0
  have hcΓ1 : Subgroup.zpowers c ≤ Subgroup.normalizer (W₁ : Set G) := le_sup_right.trans hΓ1
  have hcomm' : ∀ a b : ↥W₁ ⧸ W₀.subgroupOf W₁, a * b = b * a := by
    intro a b
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 := hcomm ((v : G)⁻¹) (W₁.inv_mem v.2) ((u : G)⁻¹) (W₁.inv_mem u.2)
    have e : (((u * v)⁻¹ * (v * u) : ↥W₁) : G) =
        ⁅((v : G)⁻¹), ((u : G)⁻¹)⁆ := by
      rw [commutatorElement_def]; simp [mul_assoc]
    rw [e]; exact h1
  have hsq' : ∀ a : ↥W₁ ⧸ W₀.subgroupOf W₁, a * a = 1 := by
    intro a
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hsq (u : G) u.2
  let ρ₀ : ↥Kt →* MulAut (↥W₁ ⧸ W₀.subgroupOf W₁) := secAct hKt0 hKt1
  have hQ_triv : ∀ x : ↥Kt, (x : G) ∈ Q → ρ₀ x = 1 := by
    intro x hxQ
    ext w
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective w
    have hw : (x : G) * (u : G) * (x : G)⁻¹ ∈ W₁ :=
      (Subgroup.mem_normalizer_iff.mp (hKt1 x.2) u).mp u.2
    have h1 := secAct_mk hKt0 hKt1 x u hw
    have key := acts_trivially_of_normal_pGroup hQ2 hQΓ hΓQ hW₁2 h01 hΓ0 hΓ1 h10 hirr
      (x : G) hxQ ((u : G)⁻¹) (W₁.inv_mem u.2)
    show ρ₀ x (QuotientGroup.mk u) = QuotientGroup.mk u
    rw [show ρ₀ x (QuotientGroup.mk u) = _ from h1, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : ((((⟨(x : G) * u * (x : G)⁻¹, hw⟩ : ↥W₁)⁻¹ * u : ↥W₁)) : G) =
        (x : G) * (u : G)⁻¹ * (x : G)⁻¹ * ((u : G)⁻¹)⁻¹ := by simp [mul_assoc]
    rw [e]; exact key
  have hker' : π.ker ≤ ρ₀.ker := by
    intro x hx
    rw [hker, Subgroup.mem_subgroupOf] at hx
    exact hQ_triv x hx
  obtain ⟨ρ, hρπ⟩ := exists_factor_hom π hπ ρ₀ hker'
  let γ : MulAut (↥W₁ ⧸ W₀.subgroupOf W₁) :=
    secAct hcΓ0 hcΓ1 ⟨c, Subgroup.mem_zpowers c⟩
  have hγ3 : γ ^ 3 = 1 := by
    have h1 : (⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hc3)
    show (secAct hcΓ0 hcΓ1 ⟨c, Subgroup.mem_zpowers c⟩) ^ 3 = 1
    rw [← map_pow, h1, map_one]
  have hγ : ∀ t : T, γ * ρ t = ρ (α t) * γ := by
    intro t
    obtain ⟨x, rfl⟩ := hπ t
    obtain ⟨x', hx'G, hx'π⟩ := hα x
    rw [hρπ x, ← hx'π, hρπ x']
    ext w
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective w
    have hu1 : (x : G) * u * (x : G)⁻¹ ∈ W₁ :=
      (Subgroup.mem_normalizer_iff.mp (hKt1 x.2) u).mp u.2
    have hu2 : c * ((x : G) * u * (x : G)⁻¹) * c⁻¹ ∈ W₁ :=
      (Subgroup.mem_normalizer_iff.mp (hcΓ1 (Subgroup.mem_zpowers c)) _).mp hu1
    have hv1 : c * (u : G) * c⁻¹ ∈ W₁ :=
      (Subgroup.mem_normalizer_iff.mp (hcΓ1 (Subgroup.mem_zpowers c)) _).mp u.2
    have hv2 : (x' : G) * (c * (u : G) * c⁻¹) * (x' : G)⁻¹ ∈ W₁ :=
      (Subgroup.mem_normalizer_iff.mp (hKt1 x'.2) (c * (u : G) * c⁻¹)).mp hv1
    have L : γ (ρ₀ x (QuotientGroup.mk u)) =
        QuotientGroup.mk (⟨c * ((x : G) * u * (x : G)⁻¹) * c⁻¹, hu2⟩ : ↥W₁) := by
      rw [show ρ₀ x (QuotientGroup.mk u) = _ from secAct_mk hKt0 hKt1 x u hu1]
      exact secAct_mk hcΓ0 hcΓ1 ⟨c, Subgroup.mem_zpowers c⟩ ⟨_, hu1⟩ hu2
    have R : ρ₀ x' (γ (QuotientGroup.mk u)) =
        QuotientGroup.mk (⟨(x' : G) * (c * (u : G) * c⁻¹) * (x' : G)⁻¹, hv2⟩ : ↥W₁) := by
      rw [show γ (QuotientGroup.mk u) = _ from
        secAct_mk hcΓ0 hcΓ1 ⟨c, Subgroup.mem_zpowers c⟩ u hv1]
      exact secAct_mk hKt0 hKt1 x' ⟨_, hv1⟩ hv2
    show γ (ρ₀ x (QuotientGroup.mk u)) = ρ₀ x' (γ (QuotientGroup.mk u))
    rw [L, R]
    congr 1
    apply Subtype.ext
    show c * ((x : G) * u * (x : G)⁻¹) * c⁻¹ = (x' : G) * (c * (u : G) * c⁻¹) * (x' : G)⁻¹
    rw [hx'G]; group
  have hρ1 : ∃ t : T, ρ t ≠ 1 := by
    refine ⟨π y, ?_⟩
    rw [hρπ y]
    intro h1
    have hyx : (y : G) * x₀ * (y : G)⁻¹ ∈ W₁ :=
      (Subgroup.mem_normalizer_iff.mp (hKt1 y.2) x₀).mp hx₀
    have e := secAct_mk hKt0 hKt1 y ⟨x₀, hx₀⟩ hyx
    have h2 : (QuotientGroup.mk (⟨(y : G) * x₀ * (y : G)⁻¹, hyx⟩ : ↥W₁) :
        ↥W₁ ⧸ W₀.subgroupOf W₁) = QuotientGroup.mk ⟨x₀, hx₀⟩ := by
      rw [← e]
      show (ρ₀ y) (QuotientGroup.mk ⟨x₀, hx₀⟩) = _
      rw [h1]; rfl
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
    have h3 : (y : G) * x₀ * (y : G)⁻¹ * x₀⁻¹ ∈ W₀ := by
      have h4 := (Subgroup.mem_normalizer_iff.mp (h10 hx₀) _).mp h2
      have h5 := W₀.inv_mem h4
      convert h5 using 1
      simp [mul_assoc]
    exact hx₀' h3
  have h8 := card_fixed_ge_eight hSz α hα1 hα3 (↥W₁ ⧸ W₀.subgroupOf W₁) hcomm' hsq' ρ γ hγ3 hγ hρ1
  let g : ↥(W₁ ⊓ Subgroup.centralizer ({c} : Set G)) →
      {w : ↥W₁ ⧸ W₀.subgroupOf W₁ // γ w = w} := fun u =>
    ⟨QuotientGroup.mk ⟨(u : G), u.2.1⟩, by
      have hcu : (u : G) * c = c * (u : G) := Subgroup.mem_centralizer_singleton_iff.mp u.2.2
      have hw : c * (u : G) * c⁻¹ ∈ W₁ :=
        (Subgroup.mem_normalizer_iff.mp (hcΓ1 (Subgroup.mem_zpowers c)) _).mp u.2.1
      show secAct hcΓ0 hcΓ1 ⟨c, Subgroup.mem_zpowers c⟩ (QuotientGroup.mk ⟨(u : G), u.2.1⟩) = _
      rw [secAct_mk hcΓ0 hcΓ1 ⟨c, Subgroup.mem_zpowers c⟩ ⟨(u : G), u.2.1⟩ hw]
      congr 1
      apply Subtype.ext
      show c * (u : G) * c⁻¹ = (u : G)
      rw [mul_inv_eq_iff_eq_mul]; exact hcu.symm⟩
  have hgsurj : Function.Surjective g := by
    rintro ⟨w, hw⟩
    obtain ⟨⟨v, hv⟩, rfl⟩ := QuotientGroup.mk_surjective w
    have hcv : c * v * c⁻¹ ∈ W₁ :=
      (Subgroup.mem_normalizer_iff.mp (hcΓ1 (Subgroup.mem_zpowers c)) _).mp hv
    have h1 := secAct_mk hcΓ0 hcΓ1 ⟨c, Subgroup.mem_zpowers c⟩ ⟨v, hv⟩ hcv
    have h2 : (QuotientGroup.mk (⟨c * v * c⁻¹, hcv⟩ : ↥W₁) : ↥W₁ ⧸ W₀.subgroupOf W₁) =
        QuotientGroup.mk ⟨v, hv⟩ := h1.symm.trans hw
    have h3 := QuotientGroup.eq.mp h2.symm
    rw [Subgroup.mem_subgroupOf] at h3
    have h4 : v⁻¹ * (c * v * c⁻¹) ∈ W₀ := by simpa using h3
    have hθH : ∀ h ∈ W₀, c * h * c⁻¹ ∈ W₀ := fun h hh =>
      (Subgroup.mem_normalizer_iff.mp (hcΓ0 (Subgroup.mem_zpowers c)) h).mp hh
    obtain ⟨h, hh, hfix⟩ := CFSG.GF2Type.Smith1980Orth.exists_fixed_mem_coset hW₀2 hc3 hθH h4
    have hvh : v * h ∈ W₁ := W₁.mul_mem hv (h01 hh)
    have hcen : v * h ∈ Subgroup.centralizer ({c} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hfix
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    refine ⟨⟨v * h, hvh, hcen⟩, ?_⟩
    apply Subtype.ext
    show (QuotientGroup.mk ⟨v * h, hvh⟩ : ↥W₁ ⧸ W₀.subgroupOf W₁) = QuotientGroup.mk ⟨v, hv⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using W₀.inv_mem hh
  have hcardg : Nat.card {w : ↥W₁ ⧸ W₀.subgroupOf W₁ // γ w = w} ≤
      Nat.card ↥(W₁ ⊓ Subgroup.centralizer ({c} : Set G)) :=
    Nat.card_le_card_of_surjective g hgsurj
  calc 8 ≤ _ := h8
    _ ≤ _ := hcardg
    _ ≤ Nat.card ↥(P ⊓ Subgroup.centralizer ({c} : Set G)) :=
      Subgroup.card_le_of_le (inf_le_inf_right _ h1P)

end Lower

end CFSG.RankThree.PartTwo.Sec18.Item187Proof

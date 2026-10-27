module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.C10KG

open scoped commutatorElement

variable {Y Y' : Type*} [Group Y] [Group Y']

theorem eq_one_of_sq_eq_one [Finite Y] {Z : Subgroup Y} (hodd : Odd (Nat.card Z)) {c : Y}
    (hc : c ∈ Z) (h2 : c ^ 2 = 1) : c = 1 := by
  have h1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have h2' : orderOf c ∣ Nat.card Z := Z.orderOf_dvd_natCard hc
  have hco : Nat.Coprime 2 (Nat.card Z) := Nat.coprime_two_left.mpr hodd
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hco h1 h2')

theorem comap_comm_of_isCyclic (φ : Y →* Y') (hZ : φ.ker ≤ Subgroup.center Y)
    {D : Subgroup Y'} (hD : IsCyclic D) :
    ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x := by
  intro x hx y hy
  let ψ : ↥(D.comap φ) →* ↥D := (φ.comp (D.comap φ).subtype).codRestrict D fun g => g.2
  have hker : ψ.ker ≤ Subgroup.center ↥(D.comap φ) := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro h
    have hg' : (g : Y) ∈ φ.ker := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
      exact MonoidHom.mem_ker.mpr this
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hZ hg') h)
  have := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center ψ hker
  exact congrArg Subtype.val (this.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem commutatorElement_mul_left_central {z : Y} (hz : z ∈ Subgroup.center Y) (a b : Y) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have hz' : ∀ g, g * z = z * g := Subgroup.mem_center_iff.mp hz
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev,
    show z * a * b * (a⁻¹ * z⁻¹) * b⁻¹ = z * (a * b * a⁻¹) * z⁻¹ * b⁻¹ by group,
    ← hz' (a * b * a⁻¹), mul_inv_cancel_right]

theorem commutatorElement_mul_right_central {z : Y} (hz : z ∈ Subgroup.center Y) (a b : Y) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have hz' : ∀ g, g * z = z * g := Subgroup.mem_center_iff.mp hz
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev,
    show a * (b * z) * a⁻¹ * (z⁻¹ * b⁻¹) = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ by group,
    ← hz' a⁻¹, show a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ by group]

theorem commutatorElement_inv_left_central {a b : Y} (hc : ⁅a, b⁆ ∈ Subgroup.center Y) :
    ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ := by
  have hc' : ∀ g, g * ⁅a, b⁆ = ⁅a, b⁆ * g := Subgroup.mem_center_iff.mp hc
  rw [← inv_inj, inv_inv]
  calc ⁅a⁻¹, b⁆⁻¹ = a⁻¹ * ⁅a, b⁆ * a := by rw [commutatorElement_def, commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [hc' a⁻¹, mul_assoc, inv_mul_cancel, mul_one]

theorem comm_of_sup {H K : Subgroup Y} (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hHK : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    ∀ x ∈ H ⊔ K, ∀ y ∈ H ⊔ K, x * y = y * x := by
  have h1 : H ⊔ K ≤ Subgroup.centralizer (H : Set Y) := sup_le
    (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hH y hy x hx)
    (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hHK y hy x hx)
  have h2 : H ⊔ K ≤ Subgroup.centralizer (K : Set Y) := sup_le
    (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (hHK x hx y hy).symm)
    (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hK y hy x hx)
  have h3 : H ⊔ K ≤ Subgroup.centralizer ((H ⊔ K : Subgroup Y) : Set Y) := by
    intro x hx
    have hle : H ⊔ K ≤ Subgroup.centralizer ({x} : Set Y) := sup_le
      (fun y hy => Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff.mp hz]
        exact (Subgroup.mem_centralizer_iff.mp (h1 hx) y hy).symm)
      (fun y hy => Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff.mp hz]
        exact (Subgroup.mem_centralizer_iff.mp (h2 hx) y hy).symm)
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hle hy) x (Set.mem_singleton x)).symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (h3 hy) x hx)

theorem comap_comm_of_weyl [Finite Y] (φ : Y →* Y') (hφ : Function.Surjective φ)
    (hZ : φ.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card φ.ker)) {A₁ A₂ : Subgroup Y'}
    (h₁ : IsCyclic A₁) (h₂ : IsCyclic A₂) (h12 : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) {w : Y'}
    (hw₁ : ∀ a ∈ A₁, w * a * w⁻¹ = a⁻¹) (hw₂ : ∀ b ∈ A₂, w * b * w⁻¹ = b) :
    ∀ x ∈ (A₁ ⊔ A₂).comap φ, ∀ y ∈ (A₁ ⊔ A₂).comap φ, x * y = y * x := by
  rw [← Subgroup.comap_sup_eq φ A₁ A₂ hφ]
  refine comm_of_sup (comap_comm_of_isCyclic φ hZ h₁) (comap_comm_of_isCyclic φ hZ h₂) ?_
  intro x hx y hy
  obtain ⟨w', rfl⟩ := hφ w
  have hcZ : ⁅x, y⁆ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
      h12 _ hx _ hy]
    group
  have hc := hZ hcZ
  have hz₁ : w' * x * w'⁻¹ * x ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hw₁ _ hx, inv_mul_cancel]
  have hz₂ : y⁻¹ * (w' * y * w'⁻¹) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hw₂ _ hy, inv_mul_cancel]
  have e1 : w' * x * w'⁻¹ = (w' * x * w'⁻¹ * x) * x⁻¹ := by group
  have e2 : w' * y * w'⁻¹ = y * (y⁻¹ * (w' * y * w'⁻¹)) := by group
  have hconj : w' * ⁅x, y⁆ * w'⁻¹ = ⁅x, y⁆⁻¹ := by
    calc w' * ⁅x, y⁆ * w'⁻¹ = ⁅w' * x * w'⁻¹, w' * y * w'⁻¹⁆ := by
          rw [commutatorElement_def, commutatorElement_def]
          group
      _ = ⁅(w' * x * w'⁻¹ * x) * x⁻¹, y * (y⁻¹ * (w' * y * w'⁻¹))⁆ :=
          congrArg₂ (fun a b => ⁅a, b⁆) e1 e2
      _ = ⁅x⁻¹, y⁆ := by
          rw [commutatorElement_mul_left_central (hZ hz₁),
            commutatorElement_mul_right_central (hZ hz₂)]
      _ = ⁅x, y⁆⁻¹ := commutatorElement_inv_left_central hc
  have hcc : w' * ⁅x, y⁆ * w'⁻¹ = ⁅x, y⁆ := by
    rw [Subgroup.mem_center_iff.mp hc w', mul_inv_cancel_right]
  have h2 : ⁅x, y⁆ ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [← hcc]
    rw [hconj, inv_mul_cancel]
  have h1 := eq_one_of_sq_eq_one hodd hcZ h2
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem isPGroup_commutator_comap [Finite Y] (φ : Y →* Y') (hφ : Function.Surjective φ)
    (hZ : φ.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card φ.ker)) {S' B' T' : Subgroup Y'}
    (hS2 : IsPGroup 2 S') (hBS : B' ≤ Subgroup.normalizer (S' : Set Y')) (hTB : T' ≤ B')
    (hBST : ∀ b ∈ B', ∃ s ∈ S', ∃ t ∈ T', b = s * t)
    (hT : ∀ x ∈ T'.comap φ, ∀ y ∈ T'.comap φ, x * y = y * x) :
    IsPGroup 2 ↥⁅B'.comap φ, B'.comap φ⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S₁ := S'.comap φ with hS₁
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 S₁))
  set P₀ : Subgroup Y := (P : Subgroup S₁).map S₁.subtype with hP₀
  have hP₀2 : IsPGroup 2 P₀ := P.isPGroup'.map _
  have hP₀S : P₀ ≤ S₁ := Subgroup.map_subtype_le _
  let ψ : ↥S₁ →* ↥S' := (φ.comp S₁.subtype).codRestrict S' fun g => g.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨s, hs⟩
    obtain ⟨y, rfl⟩ := hφ s
    exact ⟨⟨y, hs⟩, rfl⟩
  have htop : (P : Subgroup S₁).map ψ = ⊤ := by
    have h := (Sylow.mapSurjective hψ P).is_maximal' (hS2.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  have hmap : P₀.map φ = S' := by
    have hcomp : φ.comp S₁.subtype = S'.subtype.comp ψ := MonoidHom.ext fun _ => rfl
    rw [hP₀, Subgroup.map_map, hcomp, ← Subgroup.map_map, htop, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hdec : ∀ s ∈ S₁, ∃ p ∈ P₀, s = p * (p⁻¹ * s) ∧ p⁻¹ * s ∈ φ.ker := by
    intro s hs
    have hs' : φ s ∈ P₀.map φ := by rw [hmap]; exact hs
    obtain ⟨p, hp, hps⟩ := Subgroup.mem_map.mp hs'
    refine ⟨p, hp, by group, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hps, inv_mul_cancel]
  have h2el : ∀ y ∈ S₁, ∀ n : ℕ, y ^ 2 ^ n = 1 → y ∈ P₀ := by
    intro y hy n hyn
    obtain ⟨p, hp, hpy, hz⟩ := hdec y hy
    set z := p⁻¹ * y
    obtain ⟨m, hm⟩ := hP₀2 ⟨p, hp⟩
    have hpm : p ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hzc : Commute p z := (Subgroup.mem_center_iff.mp (hZ hz) p)
    have hpow : z ^ 2 ^ (m + n) = 1 := by
      have h := hzc.mul_pow (2 ^ (m + n))
      rw [← hpy, pow_add, pow_mul', hyn, one_pow, pow_mul, hpm, one_pow, one_mul] at h
      rw [pow_add]
      exact h.symm
    have hco : Nat.Coprime (2 ^ (m + n)) (Nat.card φ.ker) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hco
      (orderOf_dvd_of_pow_eq_one hpow) (φ.ker.orderOf_dvd_natCard hz))
    rw [hpy, hz1, mul_one]
    exact hp
  have hPn : ∀ b ∈ B'.comap φ, ∀ p ∈ P₀, b * p * b⁻¹ ∈ P₀ := by
    intro b hb p hp
    obtain ⟨m, hm⟩ := hP₀2 ⟨p, hp⟩
    have hpm : p ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    refine h2el _ ?_ m (by rw [conj_pow, hpm, mul_one, mul_inv_cancel])
    change φ (b * p * b⁻¹) ∈ S'
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hBS hb) _).mp (hP₀S hp)
  have hdecB : ∀ b ∈ B'.comap φ, ∃ p ∈ P₀, ∃ a ∈ T'.comap φ, b = p * a := by
    intro b hb
    obtain ⟨s, hs, t, ht, hst⟩ := hBST (φ b) hb
    obtain ⟨t', rfl⟩ := hφ t
    have hs₁ : b * t'⁻¹ ∈ S₁ := by
      change φ (b * t'⁻¹) ∈ S'
      rw [map_mul, map_inv, hst, mul_inv_cancel_right]
      exact hs
    obtain ⟨p, hp, hpb, hz⟩ := hdec _ hs₁
    refine ⟨p, hp, p⁻¹ * (b * t'⁻¹) * t', ?_, by group⟩
    change φ (p⁻¹ * (b * t'⁻¹) * t') ∈ T'
    rw [map_mul, MonoidHom.mem_ker.mp hz, one_mul]
    exact ht
  have hcomm : ⁅B'.comap φ, B'.comap φ⁆ ≤ P₀ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨p₁, hp₁, a, ha, rfl⟩ := hdecB x hx
    obtain ⟨p₂, hp₂, b, hb, rfl⟩ := hdecB y hy
    have haB : a ∈ B'.comap φ := Subgroup.comap_mono hTB ha
    have hbB : b ∈ B'.comap φ := Subgroup.comap_mono hTB hb
    have hab : a * b = b * a := hT a ha b hb
    have hab' : b * a⁻¹ = a⁻¹ * b := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hab, ← mul_assoc, inv_mul_cancel, one_mul]
    have e : ⁅p₁ * a, p₂ * b⁆ = p₁ * (a * p₂ * a⁻¹) * (b * p₁⁻¹ * b⁻¹) * p₂⁻¹ := by
      calc ⁅p₁ * a, p₂ * b⁆ = p₁ * a * p₂ * (b * a⁻¹) * p₁⁻¹ * b⁻¹ * p₂⁻¹ := by
            rw [commutatorElement_def]
            group
        _ = p₁ * a * p₂ * (a⁻¹ * b) * p₁⁻¹ * b⁻¹ * p₂⁻¹ := by rw [hab']
        _ = p₁ * (a * p₂ * a⁻¹) * (b * p₁⁻¹ * b⁻¹) * p₂⁻¹ := by group
    rw [e]
    exact P₀.mul_mem (P₀.mul_mem (P₀.mul_mem hp₁ (hPn a haB p₂ hp₂))
      (hPn b hbB _ (P₀.inv_mem hp₁))) (P₀.inv_mem hp₂)
  exact hP₀2.to_le hcomm

end CFSG.Quasithin.Vol2.Ch11.SecB.C10KG

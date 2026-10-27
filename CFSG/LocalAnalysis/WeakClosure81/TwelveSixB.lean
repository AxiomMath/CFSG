module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveSixA
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} {n : ℕ}

theorem Setting12Two.four_le_card (h : Setting12Two A M n) (hA : IsElemAbelian 2 A) :
    2 ^ 2 ≤ Nat.card ↥A := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  let π := QuotientGroup.mk' (CFSG.Quasithin.kerIn M ⊤)
  have hnc : ¬ IsCyclic ↥A := by
    intro hcyc
    haveI : IsCyclic ↥A := hcyc
    exact h.not_isCyclic_map hA
      (isCyclic_of_surjective (π.subgroupMap A) (MonoidHom.subgroupMap_surjective π A))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.A_two
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk1 : k ≤ 1 := by omega
    have hdvd : Nat.card ↥A ∣ 2 := by
      rw [hk]
      simpa using Nat.pow_dvd_pow 2 hk1
    exact hnc (isCyclic_of_card_dvd_prime hdvd)
  calc 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    _ = Nat.card ↥A := hk.symm

theorem Setting12Two.stabilizes_of_fix_eq (h : Setting12Two A M n) (hA : IsElemAbelian 2 A)
    (hKodd : Odd (Nat.card ↥(CFSG.Quasithin.kerIn M ⊤))) (ρ : G →* LGL 2 V)
    (U : Submodule (ZMod 2) V)
    (hfix : ∀ a ∈ A, a ∉ CFSG.Quasithin.kerIn M ⊤ → ∀ v : V, ρ a v = v ↔ v ∈ U) :
    ∀ x ∈ CFSG.Quasithin.kerIn M ⊤, ∀ u ∈ U, ρ x u ∈ U := by
  let K : Subgroup G := CFSG.Quasithin.kerIn M ⊤
  haveI hKnorm : K.Normal := kerIn_top_normal12 M
  let S : Subgroup G :=
    { carrier := {x | ∀ u ∈ U, ρ x u ∈ U ∧ ρ x⁻¹ u ∈ U}
      one_mem' := by
        intro u hu
        exact ⟨by simpa using hu, by simpa using hu⟩
      mul_mem' := by
        intro x y hx hy u hu
        obtain ⟨_, hxu'⟩ := hx u hu
        obtain ⟨hyu, _⟩ := hy u hu
        refine ⟨?_, ?_⟩
        · have hmul : ρ (x * y) u = ρ x (ρ y u) := by rw [map_mul, LinearEquiv.mul_apply]
          rw [hmul]
          exact (hx (ρ y u) hyu).1
        · have hmul : ρ (x * y)⁻¹ u = ρ y⁻¹ (ρ x⁻¹ u) := by
            rw [mul_inv_rev, map_mul, LinearEquiv.mul_apply]
          rw [hmul]
          exact (hy (ρ x⁻¹ u) hxu').2
      inv_mem' := by
        intro x hx u hu
        obtain ⟨hxu, hxu'⟩ := hx u hu
        exact ⟨hxu', by simpa using hxu⟩ }
  have hKS : K ≤ S := by
    have hAK : A ≤ Subgroup.normalizer (K : Set G) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    have hcop : Nat.Coprime 2 (Nat.card ↥K) := Nat.coprime_two_left.mpr hKodd
    have hrank : 2 ^ 2 ≤ Nat.card ↥A := h.four_le_card hA
    have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity
      (G := G) (p := 2) (A := A) (X := K) Nat.prime_two hA hrank hAK hcop
    have hle : (⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1),
        K ⊓ Subgroup.centralizer ({a} : Set G)) ≤ S := by
      refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
      intro x hx u hu
      obtain ⟨hxK, hxc⟩ := hx
      have haK : a ∉ K := by
        intro haK
        have hmem : a ∈ A ⊓ K := ⟨ha, haK⟩
        rw [h.inf_ker_eq_bot hKodd] at hmem
        exact ha1 (Subgroup.mem_bot.mp hmem)
      have hcomm : a * x = x * a :=
        Subgroup.mem_centralizer_iff.mp hxc a (Set.mem_singleton a)
      have hau : ρ a u = u := (hfix a ha haK u).2 hu
      refine ⟨?_, ?_⟩
      · apply (hfix a ha haK (ρ x u)).1
        calc ρ a (ρ x u) = ρ (a * x) u := by rw [map_mul, LinearEquiv.mul_apply]
          _ = ρ (x * a) u := by rw [hcomm]
          _ = ρ x (ρ a u) := by rw [map_mul, LinearEquiv.mul_apply]
          _ = ρ x u := by rw [hau]
      · have hx'c : x⁻¹ ∈ Subgroup.centralizer ({a} : Set G) :=
          (Subgroup.centralizer ({a} : Set G)).inv_mem hxc
        have hcomm' : a * x⁻¹ = x⁻¹ * a :=
          Subgroup.mem_centralizer_iff.mp hx'c a (Set.mem_singleton a)
        apply (hfix a ha haK (ρ x⁻¹ u)).1
        calc ρ a (ρ x⁻¹ u) = ρ (a * x⁻¹) u := by rw [map_mul, LinearEquiv.mul_apply]
          _ = ρ (x⁻¹ * a) u := by rw [hcomm']
          _ = ρ x⁻¹ (ρ a u) := by rw [map_mul, LinearEquiv.mul_apply]
          _ = ρ x⁻¹ u := by rw [hau]
    intro x hx
    exact hle (hgen.symm ▸ hx)
  exact fun x hx u hu => (hKS hx u hu).1

theorem Setting12Two.commute_ker (h : Setting12Two A M n) (ρ : G →* LGL 2 V)
    (hρ : Function.Injective ρ) (hq : RepQuad ρ A) (hirr : IsChiefFactor ρ ⊤ ⊥)
    (hnt : IsNoncentral ρ ⊤ ⊥) :
    ∀ x ∈ CFSG.Quasithin.kerIn M ⊤, ∀ a ∈ A, x * a = a * x := by
  let K : Subgroup G := CFSG.Quasithin.kerIn M ⊤
  haveI hKnorm : K.Normal := kerIn_top_normal12 M
  let U : Submodule (ZMod 2) V := commSub (A.map ρ)
  have hA : IsElemAbelian 2 A := isElemAbelian_of_repQuad hρ hq
  have hO : CFSG.pCore 2 G = ⊥ := pCore_eq_bot_of_irreducible ρ hρ hirr
  have hKodd : Odd (Nat.card ↥K) := h.odd_card_ker hO
  have hq' : commSpace (A.map ρ) (commSub (A.map ρ)) = ⊥ := hq
  have hUfix : ∀ a ∈ A, ∀ u ∈ U, ρ a u = u := by
    intro a ha u hu
    exact commSpace_eq_bot_iff.mp hq' (ρ a) (Subgroup.mem_map_of_mem ρ ha) u hu
  have hAtriv : ∀ a ∈ A, ∀ v : V, ρ a v - v ∈ U := by
    intro a ha v
    exact sub_mem_commSub (A := A.map ρ) (Subgroup.mem_map_of_mem ρ ha) v
  have hKU : ∀ y ∈ K, ∀ u ∈ U, ρ y u ∈ U :=
    h.stabilizes_of_fix_eq hA hKodd ρ U
      (fun a ha haK v => h.fixSub_eq_commSub hq hirr hnt ha haK v)
  intro x hx a ha
  let c : G := x⁻¹ * a⁻¹ * x * a
  have hwx : a⁻¹ * x * a ∈ K := by
    have := hKnorm.conj_mem x hx a⁻¹
    simpa using this
  have hcK : c ∈ K := by
    have hxinv : x⁻¹ ∈ K := K.inv_mem hx
    have := K.mul_mem hxinv hwx
    simpa [c, mul_assoc] using this
  have hxx : ∀ w : V, ρ x⁻¹ (ρ x w) = w := by
    intro w
    simpa [map_inv] using inv_apply_apply' (ρ x) w
  have hcu : ∀ u ∈ U, ρ c u = u := by
    intro u hu
    have hau : ρ a u = u := hUfix a ha u hu
    have hxau : ρ x u ∈ U := hKU x hx u hu
    have hainvx : ρ a⁻¹ (ρ x u) = ρ x u := hUfix a⁻¹ (A.inv_mem ha) (ρ x u) hxau
    calc ρ c u = ρ x⁻¹ (ρ a⁻¹ (ρ x (ρ a u))) := by
          simp only [c, map_mul, LinearEquiv.mul_apply]
      _ = ρ x⁻¹ (ρ a⁻¹ (ρ x u)) := by rw [hau]
      _ = ρ x⁻¹ (ρ x u) := by rw [hainvx]
      _ = u := hxx u
  have hcv : ∀ v : V, ρ c v - v ∈ U := by
    intro v
    let u₁ : V := ρ a v - v
    have hu₁ : u₁ ∈ U := hAtriv a ha v
    let u₂ : V := ρ a⁻¹ (ρ x v) - ρ x v
    have hu₂ : u₂ ∈ U := hAtriv a⁻¹ (A.inv_mem ha) (ρ x v)
    have hxu₁ : ρ x u₁ ∈ U := hKU x hx u₁ hu₁
    have hxu₂ : ρ x⁻¹ u₂ ∈ U := hKU x⁻¹ (K.inv_mem hx) u₂ hu₂
    have hxainv : ρ a⁻¹ (ρ x u₁) = ρ x u₁ :=
      hUfix a⁻¹ (A.inv_mem ha) (ρ x u₁) hxu₁
    have hv : ρ a v = v + u₁ := by
      show ρ a v = v + (ρ a v - v)
      abel
    have hv' : ρ a⁻¹ (ρ x v) = ρ x v + u₂ := by
      show ρ a⁻¹ (ρ x v) = ρ x v + (ρ a⁻¹ (ρ x v) - ρ x v)
      abel
    have hmain : ρ c v = (v + ρ x⁻¹ u₂) + u₁ := by
      calc ρ c v = ρ x⁻¹ (ρ a⁻¹ (ρ x (ρ a v))) := by
            simp only [c, map_mul, LinearEquiv.mul_apply]
        _ = ρ x⁻¹ (ρ a⁻¹ (ρ x (v + u₁))) := by rw [hv]
        _ = ρ x⁻¹ (ρ a⁻¹ (ρ x v + ρ x u₁)) := by rw [map_add]
        _ = ρ x⁻¹ (ρ a⁻¹ (ρ x v) + ρ a⁻¹ (ρ x u₁)) := by rw [map_add]
        _ = ρ x⁻¹ (ρ a⁻¹ (ρ x v) + ρ x u₁) := by rw [hxainv]
        _ = ρ x⁻¹ ((ρ x v + u₂) + ρ x u₁) := by rw [hv']
        _ = ρ x⁻¹ (ρ x v + u₂) + ρ x⁻¹ (ρ x u₁) := by rw [map_add]
        _ = (ρ x⁻¹ (ρ x v) + ρ x⁻¹ u₂) + u₁ := by rw [map_add, hxx u₁]
        _ = (v + ρ x⁻¹ u₂) + u₁ := by rw [hxx v]
    rw [hmain]
    have hsub : (v + ρ x⁻¹ u₂) + u₁ - v = ρ x⁻¹ u₂ + u₁ := by abel
    rw [hsub]
    exact U.add_mem hxu₂ hu₁
  have hc2 : ρ (c * c) = 1 := by
    apply LinearEquiv.ext
    intro v
    have hvv : ρ c v - v ∈ U := hcv v
    have hfixv : ρ c (ρ c v - v) = ρ c v - v := hcu (ρ c v - v) hvv
    have h2w : (ρ c v - v) + (ρ c v - v) = 0 := by
      have h2 : (1 + 1 : ZMod 2) = 0 := CharTwo.add_self_eq_zero 1
      calc (ρ c v - v) + (ρ c v - v) = (1 + 1 : ZMod 2) • (ρ c v - v) := by
            rw [add_smul, one_smul]
        _ = 0 := by rw [h2, zero_smul]
    calc ρ (c * c) v = ρ c (ρ c v) := by rw [map_mul, LinearEquiv.mul_apply]
      _ = ρ c (v + (ρ c v - v)) := by
            rw [show v + (ρ c v - v) = ρ c v by abel]
      _ = ρ c v + ρ c (ρ c v - v) := by rw [map_add]
      _ = ρ c v + (ρ c v - v) := by rw [hfixv]
      _ = v + ((ρ c v - v) + (ρ c v - v)) := by abel
      _ = v + 0 := by rw [h2w]
      _ = v := add_zero v
  have hc2' : c * c = 1 := by
    apply hρ
    rw [hc2, map_one]
  have hc2pow : c ^ 2 = 1 := by rw [pow_two]; exact hc2'
  have hcop : Nat.Coprime 2 (Nat.card ↥K) := Nat.coprime_two_left.mpr hKodd
  have hc1 : c = 1 := by
    have hdvd2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2pow
    have hdvdK : orderOf c ∣ Nat.card ↥K := K.orderOf_dvd_natCard hcK
    have h1 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvdK
    exact orderOf_eq_one_iff.mp h1
  have haconj : a⁻¹ * x * a = x := by
    have hxc : a⁻¹ * x * a = x * c := by
      show a⁻¹ * x * a = x * (x⁻¹ * a⁻¹ * x * a)
      group
    rw [hxc, hc1, mul_one]
  calc x * a = a * (a⁻¹ * x * a) := by group
    _ = a * x := by rw [haconj]

theorem Setting12Two.ker_le_center (h : Setting12Two A M n) (ρ : G →* LGL 2 V)
    (hρ : Function.Injective ρ) (hq : RepQuad ρ A) (hirr : IsChiefFactor ρ ⊤ ⊥)
    (hnt : IsNoncentral ρ ⊤ ⊥) : CFSG.Quasithin.kerIn M ⊤ ≤ Subgroup.center G := by
  let K : Subgroup G := CFSG.Quasithin.kerIn M ⊤
  haveI hKnorm : K.Normal := kerIn_top_normal12 M
  have hTnormal : (Subgroup.centralizer (K : Set G)).Normal := by
    refine ⟨fun t ht g => ?_⟩
    rw [Subgroup.mem_centralizer_iff] at ht ⊢
    intro b hb
    have hconj : g⁻¹ * b * g ∈ K := by
      have := hKnorm.conj_mem b hb g⁻¹
      simpa using this
    have hcomm := ht (g⁻¹ * b * g) hconj
    calc b * (g * t * g⁻¹) = g * ((g⁻¹ * b * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * b * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * t * g⁻¹) * b := by group
  have hAleT : A ≤ Subgroup.centralizer (K : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact h.commute_ker ρ hρ hq hirr hnt b hb a ha
  haveI : (Subgroup.centralizer (K : Set G)).Normal := hTnormal
  have hle : Subgroup.normalClosure (A : Set G) ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.normalClosure_le_normal hAleT
  have hTtop : Subgroup.centralizer (K : Set G) = ⊤ :=
    top_le_iff.mp (h.normalClosure_eq_top ▸ hle)
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hgT : g ∈ Subgroup.centralizer (K : Set G) := by rw [hTtop]; trivial
  exact (Subgroup.mem_centralizer_iff.mp hgT z hz).symm

theorem twelveSix_irreducible (hMult : SchurMultiplierInput) (h : Setting12Two A M n)
    (ρ : G →* LGL 2 V) (hρ : Function.Injective ρ) (hq : RepQuad ρ A)
    (hirr : IsChiefFactor ρ ⊤ ⊥) (hnt : IsNoncentral ρ ⊤ ⊥) :
    CFSG.Quasithin.kerIn M ⊤ = ⊥ := by
  have hO : CFSG.pCore 2 G = ⊥ := pCore_eq_bot_of_irreducible ρ hρ hirr
  have hKodd : Odd (Nat.card ↥(CFSG.Quasithin.kerIn M ⊤)) := h.odd_card_ker hO
  have hKcen : CFSG.Quasithin.kerIn M ⊤ ≤ Subgroup.center G :=
    h.ker_le_center ρ hρ hq hirr hnt
  have hAK : A ⊓ CFSG.Quasithin.kerIn M ⊤ = ⊥ := h.inf_ker_eq_bot hKodd
  have hgen : Subgroup.normalClosure (A : Set G) = ⊤ := h.normalClosure_eq_top
  haveI : (CFSG.Quasithin.kerIn M ⊤).Normal := kerIn_top_normal12 M
  exact twelveSix (X := G) (K := CFSG.Quasithin.kerIn M ⊤) (A := A)
    hMult hKcen hKodd h.A_two hAK ⟨n, h.one_lt_n, h.type⟩ hgen

end CFSG.LocalAnalysis.WeakClosure81

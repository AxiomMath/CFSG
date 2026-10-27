module

public import CFSG.RankThree.PartOne.S12.ReflLoc
import CFSG.LinearAlgebra.RankOneReflection
public import CFSG.RankThree.PartOne.S12.LinAlg
public import CFSG.RankThree.PartOne.S12.Sec138Local
public import CFSG.Permutation.SymmetricCoxeter

public section

namespace CFSG.RankThree.PartOne

namespace Sec138Loc

open Module LinearMap CFSG.RankThree.PartOne.ReflF

section Refl

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_reflData_field (h2 : (2 : K) ≠ 0) [Module.Finite K V] (T : V ≃ₗ[K] V)
    (hT : T * T = 1) (hrank : finrank K (LinearMap.range (Nop T)) = 1) :
    ∃ (r : V) (φ : V →ₗ[K] K), ReflData T r φ := by
  have hf : (T : Module.End K V) ^ 2 = 1 := by
    ext v
    have h := congrArg (fun g : V ≃ₗ[K] V => g v) hT
    exact h
  have hrange : finrank K (LinearMap.range (1 - (T : Module.End K V))) = 1 := by
    change finrank K (LinearMap.range (Nop T)) = 1
    exact hrank
  obtain ⟨r, φ, hpair, _, hform⟩ :=
    CFSG.LinearAlgebra.exists_reflection_of_finrank_range_one_sub_eq_one hf hrange
  refine ⟨r, φ, ?_, hpair, fun v => ?_⟩
  · intro h
    rw [h, map_zero] at hpair
    exact h2 hpair.symm
  · have h := congrArg (fun f : Module.End K V => f v) hform
    change T v = Module.reflection hpair v at h
    simpa only [Module.reflection_apply] using h

end Refl

section Irred

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {n : ℕ} {E : Subgroup G}

omit [Fact p.Prime] in
theorem irreducible_space [Fact p.Prime] (f : Multiplicative (Fin n → ZMod p) ≃* E)
    (hirr : torusIrreducible E) (U : Submodule (ZMod p) (Fin n → ZMod p))
    (hU : ∀ φ ∈ torusWeyl E, U.map (LinAlg.coordLin f φ).toLinearMap ≤ U) :
    U = ⊥ ∨ U = ⊤ := by
  obtain ⟨B, hBE, hB⟩ := LinAlg.exists_bsub_eq f U
  have hinv : torusInvariant E ⊤ B := by
    refine (LinAlg.torusInvariant_top_iff f hBE).2 fun φ hφ => ?_
    rw [hB]
    exact hU φ hφ
  rcases hirr B hBE hinv with h | h
  · left
    rw [← hB, h]
    exact LinAlg.bsub_bot f
  · right
    rw [← hB, h]
    exact LinAlg.bsub_self f

end Irred

section Dihedral

open CFSG.Permutation.SymmetricCoxeter

theorem closure_pair_equiv_perm_three {H : Type*} [Group H] {u v : H} (hu : u * u = 1)
    (hv : v * v = 1) (hcub : (u * v) ^ 3 = 1) (hne : u * v ≠ v * u) :
    Nonempty (↥(Subgroup.closure {u, v}) ≃* Equiv.Perm (Fin 3)) := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  let x : ℕ → H := fun i => if i = 0 then u else if i = 1 then v else 1
  have hbraid : u * v * u = v * u * v := by
    have h1 : (u * v * u) * (v * u * v) = 1 := by
      calc (u * v * u) * (v * u * v) = (u * v) ^ 3 := by rw [pow_three']; group
        _ = 1 := hcub
    have h2 := eq_inv_of_mul_eq_one_left h1
    rw [h2, mul_inv_rev, mul_inv_rev, hui, hvi, mul_assoc]
  have hx : IsCoxeterA 2 x := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      interval_cases i
      · simpa [x] using hu
      · simpa [x] using hv
    · intro i hi
      have : i = 0 := by omega
      subst this
      simpa [x] using hbraid
    · intro i j hij hj
      omega
  obtain ⟨ψ, hψ⟩ := exists_hom_perm 2 x hx
  have hψ0 : ψ (Equiv.swap 0 1) = u := by
    have := hψ 0 (by norm_num)
    rw [adjSwap_of_lt (by norm_num)] at this
    simpa [x] using this
  have hψ1 : ψ (Equiv.swap 1 2) = v := by
    have := hψ 1 (by norm_num)
    rw [adjSwap_of_lt (by norm_num)] at this
    simpa [x] using this
  have hu1 : u ≠ 1 := fun h => hne (by rw [h, one_mul, mul_one])
  have hv1 : v ≠ 1 := fun h => hne (by rw [h, one_mul, mul_one])
  have huv1 : u * v ≠ 1 := fun h => hne (by
    have : v = u := by
      calc v = u⁻¹ * (u * v) := by group
        _ = u := by rw [h, mul_one, hui]
    rw [this])
  have hvu1 : v * u ≠ 1 := fun h => hne (by
    have : u = v := by
      calc u = v⁻¹ * (v * u) := by group
        _ = v := by rw [h, mul_one, hvi]
    rw [this])
  have huvu1 : u * v * u ≠ 1 := fun h => hv1 (by
    calc v = u⁻¹ * (u * v * u) * u⁻¹ := by group
      _ = 1 := by rw [h, mul_one, hui, hu])
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hall : ∀ σ : Equiv.Perm (Fin 3), σ = 1 ∨ σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 1 2 ∨
        σ = Equiv.swap 0 1 * Equiv.swap 1 2 ∨ σ = Equiv.swap 1 2 * Equiv.swap 0 1 ∨
        σ = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1 := by decide
    rcases hall σ with rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · rw [hψ0] at hσ
      exact absurd hσ hu1
    · rw [hψ1] at hσ
      exact absurd hσ hv1
    · rw [map_mul, hψ0, hψ1] at hσ
      exact absurd hσ huv1
    · rw [map_mul, hψ0, hψ1] at hσ
      exact absurd hσ hvu1
    · rw [map_mul, map_mul, hψ0, hψ1] at hσ
      exact absurd hσ huvu1
  have hrange : ψ.range = Subgroup.closure {u, v} := by
    rw [MonoidHom.range_eq_map, ← closure_adjSwap 2, MonoidHom.map_closure]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_Iio, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      interval_cases i
      · left
        rw [← hψ0, adjSwap_of_lt (by norm_num)]
        rfl
      · right
        rw [← hψ1, adjSwap_of_lt (by norm_num)]
        rfl
    · rintro (rfl | rfl)
      · refine ⟨_, ⟨0, by norm_num, rfl⟩, ?_⟩
        rw [adjSwap_of_lt (by norm_num)]
        exact hψ0
      · refine ⟨_, ⟨1, by norm_num, rfl⟩, ?_⟩
        rw [adjSwap_of_lt (by norm_num)]
        exact hψ1
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

end Dihedral

section Bridge

open CFSG.RankThree.PartOne.ReflF

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {E : Subgroup G}
  {n : ℕ} (f : Multiplicative (Fin n → ZMod p) ≃* E)

omit [Finite G] in
theorem two_ne_zero_of_five_le (hp : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have hd := (ZMod.natCast_eq_zero_iff 2 p).1 h'
  have := Nat.le_of_dvd (by norm_num) hd
  omega

omit [Finite G] in
theorem three_ne_zero_of_five_le (hp : 5 ≤ p) : (3 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have hd := (ZMod.natCast_eq_zero_iff 3 p).1 h'
  have := Nat.le_of_dvd (by norm_num) hd
  omega

omit [Finite G] in
theorem coordHom_reflData (hp : 5 ≤ p) {s : MulAut E} (hs : IsAutReflection p E s) :
    ∃ (r : Fin n → ZMod p) (φ : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p),
      ReflData (LinAlg.coordHom f s) r φ := by
  obtain ⟨hord, hrank⟩ := (LinAlg.isAutReflection_iff f s).1 hs
  have hTT : LinAlg.coordHom f s * LinAlg.coordHom f s = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one (LinAlg.coordHom f s)
    rwa [hord] at this
  have hN : Nop (LinAlg.coordHom f s) = -(LinAlg.coordSub f s) := by
    refine LinearMap.ext fun x => ?_
    simp only [Nop_apply, LinearMap.neg_apply, LinAlg.coordSub_apply]
    show x - LinAlg.coordLin f s x = -(LinAlg.coordLin f s x - x)
    abel
  refine exists_reflData_field (two_ne_zero_of_five_le hp) _ hTT ?_
  rw [hN, LinearMap.range_neg]
  exact hrank

section Dstar

open CFSG.RankThree.PartOne.ReflF CFSG.RankThree

@[expose] noncomputable def dstar : Finset ((Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) :=
  (Set.toFinite (reflectionSet p E)).toFinset.image (LinAlg.coordHom f)

theorem mem_dstar {T : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)} :
    T ∈ dstar f ↔ ∃ s ∈ reflectionSet p E, LinAlg.coordHom f s = T := by
  simp [dstar, Finset.mem_image, Set.Finite.mem_toFinset]

omit [Finite G] in
theorem coordHom_pow_mul (s t : MulAut E) (k : ℕ) :
    (LinAlg.coordHom f s * LinAlg.coordHom f t) ^ k = LinAlg.coordHom f ((s * t) ^ k) := by
  rw [← map_mul, ← map_pow]

theorem isRSet_dstar (hp5 : 5 ≤ p) (hD3 : ThreeTranspD p E) : IsRSet (dstar f) where
  refl T hT := by
    obtain ⟨s, hs, rfl⟩ := (mem_dstar f).1 hT
    exact coordHom_reflData f hp5 hs.1
  conj T hT S hS := by
    obtain ⟨s, hs, rfl⟩ := (mem_dstar f).1 hT
    obtain ⟨t, ht, rfl⟩ := (mem_dstar f).1 hS
    refine (mem_dstar f).2 ⟨s * t * s⁻¹, ?_, by simp⟩
    exact WeylIso.conj_mem_reflectionSet_of_weyl Fact.out
      (WeylIso.mem_torusWeyl_of_mem_reflectionSet hs) ht
  ord T hT S hS hne := by
    obtain ⟨s, hs, rfl⟩ := (mem_dstar f).1 hT
    obtain ⟨t, ht, rfl⟩ := (mem_dstar f).1 hS
    have hle : orderOf (s * t) ≤ 3 := hD3 s hs t ht
    have hpos : 0 < orderOf (s * t) := orderOf_pos _
    have hpow := pow_orderOf_eq_one (s * t)
    have hcases : orderOf (s * t) = 1 ∨ orderOf (s * t) = 2 ∨ orderOf (s * t) = 3 := by omega
    rcases hcases with h | h | h
    · left
      rw [coordHom_pow_mul, ← h, hpow, map_one]
    · right
      left
      rw [coordHom_pow_mul, ← h, hpow, map_one]
    · right
      right
      rw [coordHom_pow_mul, ← h, hpow, map_one]

omit [Finite G] [Fact p.Prime] in
theorem mul_self_eq_one_of_reflection {s : MulAut E} (hs : IsAutReflection p E s) : s * s = 1 := by
  rw [← pow_two]
  have := pow_orderOf_eq_one s
  rwa [hs.1] at this

theorem conn_dstar (hp5 : 5 ≤ p) (hD3 : ThreeTranspD p E) (htrans : TransitiveD p E) :
    Conn (dstar f) := by
  have hR := isRSet_dstar f hp5 hD3
  have hp : p.Prime := Fact.out
  intro P hPsub hPne hPcl
  obtain ⟨T₀, hT₀⟩ := hPne
  obtain ⟨s₀, hs₀, hs₀T⟩ := (mem_dstar f).1 (hPsub hT₀)
  apply Finset.Subset.antisymm hPsub
  intro T hT
  obtain ⟨t, ht, rfl⟩ := (mem_dstar f).1 hT
  obtain ⟨x, hx, hxs⟩ := htrans s₀ hs₀ t ht
  have hconj : ∀ y ∈ torusWeyl E, ∀ s ∈ reflectionSet p E, y * s * y⁻¹ ∈ reflectionSet p E :=
    fun y hy s hs => WeylIso.conj_mem_reflectionSet_of_weyl hp hy hs
  have hgen : ∀ y ∈ reflectionSet p E, ∀ s ∈ reflectionSet p E,
      LinAlg.coordHom f s ∈ P → LinAlg.coordHom f (y * s * y⁻¹) ∈ P := by
    intro y hy s hs hsP
    have hyD : LinAlg.coordHom f y ∈ dstar f := (mem_dstar f).2 ⟨y, hy, rfl⟩
    by_cases hc : y * s = s * y
    · have : y * s * y⁻¹ = s := by rw [mul_inv_eq_iff_eq_mul]; exact hc
      rw [this]
      exact hsP
    · have hnc : LinAlg.coordHom f y * LinAlg.coordHom f s ≠
          LinAlg.coordHom f s * LinAlg.coordHom f y := by
        intro e
        rw [← map_mul, ← map_mul] at e
        exact hc (LinAlg.coordHom_injective f e)
      have hyP : LinAlg.coordHom f y ∈ P := hPcl _ hsP _ hyD (fun e => hnc e.symm)
      have hnc2 : LinAlg.coordHom f y * LinAlg.coordHom f (y * s * y⁻¹) ≠
          LinAlg.coordHom f (y * s * y⁻¹) * LinAlg.coordHom f y := by
        intro e
        apply hnc
        rw [map_mul, map_mul, map_inv] at e
        exact (hR.conj_comm_iff hyD (LinAlg.coordHom f s)).1 e
      have hmem : LinAlg.coordHom f (y * s * y⁻¹) ∈ dstar f :=
        (mem_dstar f).2 ⟨_, hconj y (WeylIso.mem_torusWeyl_of_mem_reflectionSet hy) s hs, rfl⟩
      exact hPcl _ hyP _ hmem hnc2
  have hall : ∀ y ∈ Subgroup.closure (reflectionSet p E), ∀ s ∈ reflectionSet p E,
      LinAlg.coordHom f s ∈ P →
        LinAlg.coordHom f (y * s * y⁻¹) ∈ P ∧ LinAlg.coordHom f (y⁻¹ * s * y) ∈ P := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      intro s hs hsP
      have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_reflection hy.1)
      have h1 := hgen y hy s hs hsP
      rw [hyi] at h1
      rw [hyi]
      exact ⟨h1, h1⟩
    | one =>
      intro s hs hsP
      simpa using And.intro hsP hsP
    | mul y z hy hz ihy ihz =>
      intro s hs hsP
      have hyW : y ∈ torusWeyl E := WeylIso.closure_le_weyl hy
      have hzW : z ∈ torusWeyl E := WeylIso.closure_le_weyl hz
      obtain ⟨a1, a2⟩ := ihz s hs hsP
      obtain ⟨b1, b2⟩ := ihy s hs hsP
      obtain ⟨c1, -⟩ := ihy (z * s * z⁻¹) (hconj z hzW s hs) a1
      obtain ⟨-, d2⟩ := ihz (y⁻¹ * s * y) (by
        have := hconj y⁻¹ (inv_mem hyW) s hs
        simpa using this) b2
      refine ⟨?_, ?_⟩
      · have : y * z * s * (y * z)⁻¹ = y * (z * s * z⁻¹) * y⁻¹ := by group
        rw [this]
        exact c1
      · have : (y * z)⁻¹ * s * (y * z) = z⁻¹ * (y⁻¹ * s * y) * z := by group
        rw [this]
        exact d2
    | inv y hy ih =>
      intro s hs hsP
      obtain ⟨h1, h2⟩ := ih s hs hsP
      refine ⟨?_, ?_⟩
      · simpa using h2
      · simpa using h1
  have hxW : x ∈ Subgroup.closure (reflectionSet p E) := hx
  have := (hall x hxW s₀ hs₀ (by rw [hs₀T]; exact hT₀)).1
  rw [hxs] at this
  exact this

theorem uspan_dstar (hp5 : 5 ≤ p) (hirr : torusIrreducible E)
    (hne : (reflectionSet p E).Nonempty) : Uspan (dstar f) = ⊤ := by
  have hp : p.Prime := Fact.out
  have hU : ∀ φ ∈ torusWeyl E,
      (Uspan (dstar f)).map (LinAlg.coordLin f φ).toLinearMap ≤ Uspan (dstar f) := by
    intro φ hφ
    rw [Uspan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨x, ⟨T, hT, hx⟩, rfl⟩
    obtain ⟨s, hs, rfl⟩ := (mem_dstar f).1 hT
    obtain ⟨z, rfl⟩ := hx
    have hs' : φ * s * φ⁻¹ ∈ reflectionSet p E :=
      WeylIso.conj_mem_reflectionSet_of_weyl hp hφ hs
    refine Submodule.subset_span ⟨LinAlg.coordHom f (φ * s * φ⁻¹),
      (mem_dstar f).2 ⟨_, hs', rfl⟩, ?_⟩
    refine ⟨(LinAlg.coordLin f φ) z, ?_⟩
    rw [map_mul, map_mul, map_inv, nop_conj]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    have : (LinAlg.coordHom f φ)⁻¹ ((LinAlg.coordLin f φ) z) = z := by
      show (LinAlg.coordLin f φ).symm ((LinAlg.coordLin f φ) z) = z
      exact (LinAlg.coordLin f φ).symm_apply_apply z
    rw [this]
    rfl
  rcases irreducible_space f hirr (Uspan (dstar f)) hU with h | h
  · exfalso
    obtain ⟨s, hs⟩ := hne
    obtain ⟨r, φ, hd⟩ := coordHom_reflData f hp5 hs.1
    have hmem := mem_Uspan_of_root (two_ne_zero_of_five_le hp5)
      ((mem_dstar f).2 ⟨s, hs, rfl⟩) hd
    rw [h] at hmem
    exact hd.ne ((Submodule.mem_bot _).1 hmem)
  · exact h

omit [Finite G] in
theorem coordHom_ne {s t : MulAut E} (h : s ≠ t) : LinAlg.coordHom f s ≠ LinAlg.coordHom f t :=
  fun e => h (LinAlg.coordHom_injective f e)

omit [Finite G] in
theorem coordHom_comm_iff {s t : MulAut E} :
    LinAlg.coordHom f s * LinAlg.coordHom f t = LinAlg.coordHom f t * LinAlg.coordHom f s ↔
      s * t = t * s := by
  rw [← map_mul, ← map_mul]
  exact (LinAlg.coordHom_injective f).eq_iff

theorem localSThree_of_no_four [IsElementaryAbelian p E] (hcard : Nat.card E = p ^ 4)
    (hp5 : 5 ≤ p) (hD3 : ThreeTranspD p E) (htrans : TransitiveD p E)
    (hirr : torusIrreducible E) (hne : (reflectionSet p E).Nonempty)
    (hno4 : ∀ a ∈ reflectionSet p E, ∀ b ∈ reflectionSet p E, ∀ c ∈ reflectionSet p E,
      ∀ d ∈ reflectionSet p E, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      a * b = b * a → a * c = c * a → a * d = d * a → b * c = c * b → b * d = d * b →
      c * d = d * c → False) :
    LocalSThree p E := by
  have hp : p.Prime := Fact.out
  obtain ⟨f⟩ := LinAlg.exists_coords (p := p) E hcard
  intro t ht
  have hR := isRSet_dstar f hp5 hD3
  have hconn := conn_dstar f hp5 hD3 htrans
  have hU := uspan_dstar f hp5 hirr hne
  have hdim : finrank (ZMod p) (Fin 4 → ZMod p) = 4 := Module.finrank_fin_fun _
  have h2 := two_ne_zero_of_five_le (p := p) hp5
  have h3 := three_ne_zero_of_five_le (p := p) hp5
  have hno4' : ∀ a ∈ dstar f, ∀ b ∈ dstar f, ∀ c ∈ dstar f, ∀ d ∈ dstar f, a ≠ b → a ≠ c →
      a ≠ d → b ≠ c → b ≠ d → c ≠ d → a * b = b * a → a * c = c * a → a * d = d * a →
      b * c = c * b → b * d = d * b → c * d = d * c → False := by
    intro a ha b hb c hc d hd hab hac had hbc hbd hcd cab cac cad cbc cbd ccd
    obtain ⟨a0, ha0, rfl⟩ := (mem_dstar f).1 ha
    obtain ⟨b0, hb0, rfl⟩ := (mem_dstar f).1 hb
    obtain ⟨c0, hc0, rfl⟩ := (mem_dstar f).1 hc
    obtain ⟨d0, hd0, rfl⟩ := (mem_dstar f).1 hd
    exact hno4 a0 ha0 b0 hb0 c0 hc0 d0 hd0
      (fun e => hab (by rw [e])) (fun e => hac (by rw [e])) (fun e => had (by rw [e]))
      (fun e => hbc (by rw [e])) (fun e => hbd (by rw [e])) (fun e => hcd (by rw [e]))
      ((coordHom_comm_iff f).1 cab) ((coordHom_comm_iff f).1 cac) ((coordHom_comm_iff f).1 cad)
      ((coordHom_comm_iff f).1 cbc) ((coordHom_comm_iff f).1 cbd) ((coordHom_comm_iff f).1 ccd)
  have htD : LinAlg.coordHom f t ∈ dstar f := (mem_dstar f).2 ⟨t, ht, rfl⟩
  obtain ⟨u, hu, v, hv, huv, hnc, hΔ⟩ :=
    local_structure hdim h2 h3 hR hconn hU hno4' htD
  obtain ⟨u0, hu0, rfl⟩ := (mem_dstar f).1 hu
  obtain ⟨v0, hv0, rfl⟩ := (mem_dstar f).1 hv
  have hconj : ∀ y ∈ reflectionSet p E, ∀ s ∈ reflectionSet p E, y * s * y⁻¹ ∈ reflectionSet p E :=
    fun y hy s hs => WeylIso.conj_mem_reflectionSet_of_weyl hp
      (WeylIso.mem_torusWeyl_of_mem_reflectionSet hy) hs
  have hz0 : u0 * v0 * u0⁻¹ ∈ reflectionSet p E := hconj u0 hu0 v0 hv0
  have hset : {s : MulAut E | s ∈ reflectionSet p E ∧ s * t = t * s ∧ s ≠ t} =
      {u0, v0, u0 * v0 * u0⁻¹} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hs, hc, hst⟩
      have hmem : LinAlg.coordHom f s ∈ commSet (dstar f) (LinAlg.coordHom f t) :=
        mem_commSet.2 ⟨(mem_dstar f).2 ⟨s, hs, rfl⟩, coordHom_ne f hst,
          (coordHom_comm_iff f).2 hc.symm⟩
      rw [hΔ] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h
      · exact Or.inl (LinAlg.coordHom_injective f h)
      · exact Or.inr (Or.inl (LinAlg.coordHom_injective f h))
      · refine Or.inr (Or.inr (LinAlg.coordHom_injective f ?_))
        rw [h]
        simp
    · intro h
      have key : ∀ s ∈ reflectionSet p E, LinAlg.coordHom f s ∈ commSet (dstar f)
          (LinAlg.coordHom f t) → s ∈ reflectionSet p E ∧ s * t = t * s ∧ s ≠ t := by
        intro s hs hmem
        obtain ⟨-, hne', hc⟩ := mem_commSet.1 hmem
        exact ⟨hs, ((coordHom_comm_iff f).1 hc).symm, fun e => hne' (by rw [e])⟩
      rcases h with rfl | rfl | rfl
      · exact key _ hu0 (by rw [hΔ]; simp)
      · exact key _ hv0 (by rw [hΔ]; simp)
      · refine key _ hz0 ?_
        rw [hΔ]
        simp
  rw [hset]
  have hu1 : u0 * u0 = 1 := mul_self_eq_one_of_reflection hu0.1
  have hv1 : v0 * v0 = 1 := mul_self_eq_one_of_reflection hv0.1
  have hnc0 : u0 * v0 ≠ v0 * u0 := fun e => hnc ((coordHom_comm_iff f).2 e)
  have hord3 : (u0 * v0) ^ 3 = 1 := by
    have hle : orderOf (u0 * v0) ≤ 3 := hD3 u0 hu0 v0 hv0
    have hpos : 0 < orderOf (u0 * v0) := orderOf_pos _
    have hne1 : orderOf (u0 * v0) ≠ 1 := fun h => by
      have : u0 * v0 = 1 := orderOf_eq_one_iff.1 h
      apply hnc0
      have hv : v0 = u0 := by
        calc v0 = u0⁻¹ * (u0 * v0) := by group
          _ = u0 := by rw [this, mul_one, inv_eq_of_mul_eq_one_right hu1]
      rw [hv]
    have hne2 : orderOf (u0 * v0) ≠ 2 := fun h => by
      have h2' : (u0 * v0) ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
      apply hnc0
      have e : u0 * v0 * (u0 * v0) = 1 := by rw [← pow_two]; exact h2'
      have hui : u0⁻¹ = u0 := inv_eq_of_mul_eq_one_right hu1
      have hvi : v0⁻¹ = v0 := inv_eq_of_mul_eq_one_right hv1
      calc u0 * v0 = (u0 * v0)⁻¹ := eq_inv_of_mul_eq_one_left e
        _ = v0⁻¹ * u0⁻¹ := mul_inv_rev _ _
        _ = v0 * u0 := by rw [hui, hvi]
    have : orderOf (u0 * v0) = 3 := by omega
    rw [← this]
    exact pow_orderOf_eq_one _
  have hcl : Subgroup.closure {u0, v0, u0 * v0 * u0⁻¹} = Subgroup.closure {u0, v0} := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))) (Subgroup.inv_mem _ (Subgroup.subset_closure
          (by simp)))
    · apply Subgroup.closure_mono
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
  obtain ⟨e⟩ := closure_pair_equiv_perm_three hu1 hv1 hord3 hnc0
  exact ⟨(MulEquiv.subgroupCongr hcl).trans e⟩

end Dstar

end Bridge

end Sec138Loc

end CFSG.RankThree.PartOne

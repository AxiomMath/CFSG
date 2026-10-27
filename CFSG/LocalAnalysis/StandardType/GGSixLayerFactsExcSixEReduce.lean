module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaDefs
public import CFSG.RankThree.PartOne.S11d.LieComponentLift

public section

namespace CFSG.StandardType

namespace LayerSixE

open CFSG.Assembly CFSG.RankThree.PartOne
open scoped commutatorElement

section Fix

variable {C : Type*} [Group C]

@[expose] def autFix (A : Subgroup (MulAut C)) : Subgroup C where
  carrier := {x | ∀ α ∈ A, α x = x}
  one_mem' := fun α _ => map_one α
  mul_mem' := fun {x y} hx hy α hα => by rw [map_mul, hx α hα, hy α hα]
  inv_mem' := fun {x} hx α hα => by rw [map_inv, hx α hα]

theorem mem_autFix {A : Subgroup (MulAut C)} {x : C} : x ∈ autFix A ↔ ∀ α ∈ A, α x = x :=
  Iff.rfl

end Fix

section Central

variable {L : Type*} [Group L]

theorem commutatorElement_mul_central_left {x z y : L} (hz : z ∈ Subgroup.center L) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have h : y * z = z * y := Subgroup.mem_center_iff.mp hz y
  rw [commutatorElement_def, commutatorElement_def]
  calc x * z * y * (x * z)⁻¹ * y⁻¹ = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * z) * z⁻¹ * x⁻¹ * y⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutatorElement_mul_central_right {x y w : L} (hw : w ∈ Subgroup.center L) :
    ⁅x, y * w⁆ = ⁅x, y⁆ := by
  have h : x⁻¹ * w = w * x⁻¹ := Subgroup.mem_center_iff.mp hw x⁻¹
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (y * w) * x⁻¹ * (y * w)⁻¹ = x * y * (w * x⁻¹) * w⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * w) * w⁻¹ * y⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem conj_mem_commutator_self {M : Subgroup L} {u : L} (hu : u ∈ M) {s : L}
    (hs : s ∈ ⁅M, M⁆) : u * s * u⁻¹ ∈ ⁅M, M⁆ := by
  have hle : ⁅M, M⁆ ≤ (⁅M, M⁆).comap (MulAut.conj u).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e : u * ⁅a, b⁆ * u⁻¹ = ⁅u * a * u⁻¹, u * b * u⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator (M.mul_mem (M.mul_mem hu ha) (M.inv_mem hu))
      (M.mul_mem (M.mul_mem hu hb) (M.inv_mem hu))
  exact hle hs

end Central

section Pullback

variable {L C : Type*} [Group L] [Group C]

theorem eq_one_of_sq_eq_one_of_odd {N : Subgroup L} (hodd : Odd (Nat.card N)) {z : L}
    (hz : z ∈ N) (hz2 : z ^ 2 = 1) : z = 1 := by
  have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
  have h2 : orderOf z ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hz
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h2
    exact absurd (Nat.odd_iff.mp hodd) (by omega)

theorem isSubCoreFamily_comap_of_central (π : L →* C) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center L) (hodd : Odd (Nat.card π.ker)) {Y : Subgroup C}
    {β : Type} {S : β → Subgroup C} (h : LayerCores.IsSubCoreFamily Y S) :
    LayerCores.IsSubCoreFamily (Y.comap π) (fun c => derivedPreimage π (S c)) := by
  obtain ⟨hle, hn, hq, ⟨k, hk⟩, hz⟩ := h
  have hmap : ∀ c, (derivedPreimage π (S c)).map π = S c := fun c =>
    map_derivedPreimage_of_perfect hπ (hq c).1
  have hsupmap : (⨆ c, derivedPreimage π (S c)).map π = ⨆ c, S c := by
    rw [Subgroup.map_iSup]
    exact iSup_congr hmap
  have hdec : ∀ x ∈ (⨆ c, S c).comap π, ∃ n ∈ ⨆ c, derivedPreimage π (S c),
      ∃ z ∈ Subgroup.center L, x = n * z := by
    intro x hx
    rw [Subgroup.mem_comap, ← hsupmap] at hx
    obtain ⟨n, hn, hnx⟩ := hx
    refine ⟨n, hn, n⁻¹ * x, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hnx, inv_mul_cancel]
  refine ⟨fun c => (derivedPreimage_le_comap π (S c)).trans (Subgroup.comap_mono (hle c)),
    fun c => LayerCores.ggSubnormal_trans
      (LayerCores.ggSubnormal_of_normal (derivedPreimage_le_comap π (S c))
        fun u hu s hs => conj_mem_commutator_self hu hs)
      (LayerCores.ggSubnormal_comap π (hn c)),
    fun c => isQuasisimple_derivedPreimage hπ hker (hq c), ⟨k + 1, ?_⟩, ?_⟩
  ·
    have h1 : LayerFacts.ggDer (Y.comap π) k ≤ (⨆ c, S c).comap π := by
      rw [← Subgroup.map_le_iff_le_comap, LayerFacts.map_ggDer,
        Subgroup.map_comap_eq_self_of_surjective hπ]
      exact hk
    rw [LayerFacts.ggDer_succ]
    refine (Subgroup.commutator_mono h1 h1).trans ?_
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨n, hn, z, hz, rfl⟩ := hdec x hx
    obtain ⟨n', hn', z', hz', rfl⟩ := hdec y hy
    rw [commutatorElement_mul_central_left hz, commutatorElement_mul_central_right hz']
    exact Subgroup.commutator_le_self _ (Subgroup.commutator_mem_commutator hn hn')
  ·
    intro z hzS hzc hz2
    have hπz : π z = 1 := by
      refine hz (π z) (hsupmap ▸ Subgroup.mem_map_of_mem π hzS) (fun y hy => ?_)
        (by rw [← map_pow, hz2, map_one])
      rw [← hsupmap] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      rw [← map_mul, ← map_mul, hzc y' hy']
    exact eq_one_of_sq_eq_one_of_odd hodd (MonoidHom.mem_ker.mpr hπz) hz2

end Pullback

section Induced

variable {L C : Type*} [Group L] [Group C] {G : Type*} [Group G]

@[expose] def GGInduces (π : L →* C) (ψ : L →* G) (c : G) (α : MulAut C) : Prop :=
  ∀ y y' : L, ψ y' = c * ψ y * c⁻¹ → π y' = α (π y)

variable {π : L →* C} {ψ : L →* G}

theorem exists_conj_eq {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) (y : L) :
    ∃ y' : L, ψ y' = c * ψ y * c⁻¹ :=
  (Subgroup.mem_normalizer_iff.mp hc (ψ y)).mp ⟨y, rfl⟩

theorem GGInduces.one (hker : ψ.ker ≤ π.ker) : GGInduces π ψ 1 1 := by
  intro y y' h
  rw [one_mul, inv_one, mul_one] at h
  have hk : y⁻¹ * y' ∈ π.ker :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel])
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk
  rw [← hk]
  rfl

theorem GGInduces.mul {c d : G} {α β : MulAut C} (hc : GGInduces π ψ c α)
    (hdN : d ∈ Subgroup.normalizer (ψ.range : Set G)) (hd : GGInduces π ψ d β) :
    GGInduces π ψ (c * d) (α * β) := by
  intro y y' h
  obtain ⟨y₁, hy₁⟩ := exists_conj_eq hdN y
  have h' : ψ y' = c * ψ y₁ * c⁻¹ := by rw [h, hy₁]; group
  rw [hc y₁ y' h', hd y y₁ hy₁]
  rfl

theorem GGInduces.inv {c : G} {α : MulAut C} (hc : GGInduces π ψ c α) :
    GGInduces π ψ c⁻¹ α⁻¹ := by
  intro y y' h
  have h' : ψ y = c * ψ y' * c⁻¹ := by rw [h]; group
  rw [hc y' y h', MulAut.inv_apply_self]

theorem GGInduces.pow (hker : ψ.ker ≤ π.ker) {c : G} {α : MulAut C}
    (hcN : c ∈ Subgroup.normalizer (ψ.range : Set G)) (hc : GGInduces π ψ c α) (n : ℕ) :
    GGInduces π ψ (c ^ n) (α ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact GGInduces.one hker
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hcN hc

theorem GGInduces.psi (hker : ψ.ker ≤ π.ker) (u : L) :
    GGInduces π ψ (ψ u) (MulAut.conj (π u)) := by
  intro y y' h
  have h1 := GGInduces.one hker (u * y * u⁻¹) y' (by rw [h, map_mul, map_mul, map_inv]; group)
  rw [h1, MulAut.one_apply, map_mul, map_mul, map_inv, MulAut.conj_apply]

theorem GGInduces.of_generators (hker : ψ.ker ≤ π.ker) {X : Set L}
    (hX : Subgroup.closure X = ⊤) {c : G} (hcN : c ∈ Subgroup.normalizer (ψ.range : Set G))
    {α : MulAut C} (hact : ∀ z ∈ X, ∃ z' : L, ψ z' = c * ψ z * c⁻¹ ∧ π z' = α (π z)) :
    GGInduces π ψ c α := by
  have hirr : ∀ y y'' y' : L, ψ y'' = ψ y' → π y'' = π y' := by
    intro y₀ y'' y' h
    have hk : y''⁻¹ * y' ∈ π.ker :=
      hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel])
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk
    exact hk
  let P : Subgroup L :=
    { carrier := {y | ∀ y' : L, ψ y' = c * ψ y * c⁻¹ → π y' = α (π y)}
      one_mem' := by
        intro y' h
        rw [map_one, mul_one, mul_inv_cancel] at h
        have := hirr 1 y' 1 (by rw [h, map_one])
        rw [this, map_one, map_one]
      mul_mem' := by
        intro a b ha hb y' h
        obtain ⟨a', ha'⟩ := exists_conj_eq hcN a
        have hb' : ψ (a'⁻¹ * y') = c * ψ b * c⁻¹ := by
          rw [map_mul, map_inv, h, ha', map_mul]
          group
        have e : y' = a' * (a'⁻¹ * y') := by group
        rw [e, map_mul, ha a' ha', hb _ hb', map_mul, map_mul]
      inv_mem' := by
        intro a ha y' h
        have h' : ψ y'⁻¹ = c * ψ a * c⁻¹ := by
          rw [map_inv, h, map_inv]
          group
        have h2 := ha _ h'
        rw [map_inv] at h2
        rw [map_inv, map_inv α, ← h2, inv_inv] }
  have hXP : X ⊆ P := by
    intro z hz y' h
    obtain ⟨z', hz'1, hz'2⟩ := hact z hz
    rw [hirr z y' z' (h.trans hz'1.symm), hz'2]
  intro y y' h
  have hy : y ∈ P := by
    have := (Subgroup.closure_le P).mpr hXP
    rw [hX] at this
    exact this (Subgroup.mem_top y)
  exact hy y' h

theorem GGInduces.unique (hπ : Function.Surjective π) {c : G}
    (hcN : c ∈ Subgroup.normalizer (ψ.range : Set G)) {α α' : MulAut C}
    (h : GGInduces π ψ c α) (h' : GGInduces π ψ c α') : α = α' := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := hπ x
  obtain ⟨y', hy'⟩ := exists_conj_eq hcN y
  rw [← h y y' hy', h' y y' hy']

@[expose] def inducedAut (hker : ψ.ker ≤ π.ker) (E : Subgroup G)
    (hEN : E ≤ Subgroup.normalizer (ψ.range : Set G)) : Subgroup (MulAut C) where
  carrier := {α | ∃ e ∈ E, GGInduces π ψ e α}
  one_mem' := ⟨1, E.one_mem, GGInduces.one hker⟩
  mul_mem' := by
    rintro _ _ ⟨e, he, h⟩ ⟨e', he', h'⟩
    exact ⟨e * e', E.mul_mem he he', h.mul (hEN he') h'⟩
  inv_mem' := by
    rintro _ ⟨e, he, h⟩
    exact ⟨e⁻¹, E.inv_mem he, h.inv⟩

theorem mem_inducedAut {hker : ψ.ker ≤ π.ker} {E : Subgroup G}
    {hEN : E ≤ Subgroup.normalizer (ψ.range : Set G)} {α : MulAut C} :
    α ∈ inducedAut hker E hEN ↔ ∃ e ∈ E, GGInduces π ψ e α :=
  Iff.rfl

end Induced

section Model

variable {L C : Type*} [Group L] [Group C] {G : Type*} [Group G]

theorem ggLayer_of_model [Finite L] {π : L →* C} (hπ : Function.Surjective π)
    (hπker : π.ker ≤ Subgroup.center L) (hodd : Odd (Nat.card π.ker)) {ψ : L →* G}
    (hker : ψ.ker ≤ π.ker) {D : Subgroup (MulAut C)} {p : ℕ} {E : Subgroup G}
    (hE : IsPGroup p E) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEN : E ≤ Subgroup.normalizer (ψ.range : Set G))
    (hD : ∀ e ∈ E, ∃ α ∈ D, GGInduces π ψ e α)
    (hcore : ∀ A : Subgroup (MulAut C), IsPGroup p A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      A ≤ D → ∃ (β : Type) (S : β → Subgroup C), LayerCores.IsSubCoreFamily (autFix A) S) :
    Odd (Nat.card (Subgroup.center
        ↥(LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G))))) ∧
      ∀ X : Subgroup G, X ≤ ψ.range ⊓ Subgroup.centralizer (E : Set G) → ⁅X, X⁆ = X →
        X ≤ LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G)) := by
  set A := inducedAut hker E hEN with hA
  have hAD : A ≤ D := by
    rintro α ⟨e, he, hα⟩
    obtain ⟨α', hα'D, hα'⟩ := hD e he
    rw [GGInduces.unique hπ (hEN he) hα hα']
    exact hα'D
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro α ⟨e, he, hα⟩ α' ⟨e', he', hα'⟩
    have h1 := hα.mul (hEN he') hα'
    have h2 := hα'.mul (hEN he) hα
    rw [hcomm e he e' he'] at h1
    exact GGInduces.unique hπ ((Subgroup.normalizer _).mul_mem (hEN he') (hEN he)) h1 h2
  have hAp : IsPGroup p A := by
    rintro ⟨α, e, he, hα⟩
    obtain ⟨n, hn⟩ := hE ⟨e, he⟩
    have hen : e ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine ⟨n, Subtype.ext ?_⟩
    have h1 := hα.pow hker (hEN he) (p ^ n)
    rw [hen] at h1
    exact GGInduces.unique hπ (Subgroup.one_mem _) h1 (GGInduces.one hker)
  obtain ⟨β, S, hS⟩ := hcore A hAp hAc hAD
  set M := (autFix A).comap π with hM
  have hψker : ψ.ker ≤ Subgroup.center L := hker.trans hπker
  set H := ψ.range ⊓ Subgroup.centralizer (E : Set G) with hH
  have hHM : H ≤ M.map ψ := by
    rintro _ ⟨⟨y, rfl⟩, hy⟩
    refine ⟨y, fun α hα => ?_, rfl⟩
    obtain ⟨e, he, hα⟩ := hα
    refine (hα y y ?_).symm
    rw [Subgroup.mem_centralizer_iff.mp hy e he, mul_inv_cancel_right]
  have hMH : ⁅M, M⁆ ≤ H.comap ψ := by
    rw [Subgroup.commutator_le]
    intro y₁ hy₁ y₂ hy₂
    refine ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
    obtain ⟨α, -, hα⟩ := hD e he
    have hαA : α ∈ A := ⟨e, he, hα⟩
    have hz : ∀ {y y' : L}, y ∈ M → ψ y' = e * ψ y * e⁻¹ → y⁻¹ * y' ∈ Subgroup.center L := by
      intro y y' hy hy'
      refine hπker ?_
      have hfix : α (π y) = π y := hy α hαA
      rw [MonoidHom.mem_ker, map_mul, map_inv, hα y y' hy', hfix, inv_mul_cancel]
    obtain ⟨y₁', hy₁'⟩ := exists_conj_eq (hEN he) y₁
    obtain ⟨y₂', hy₂'⟩ := exists_conj_eq (hEN he) y₂
    have hconj : ψ ⁅y₁', y₂'⁆ = e * ψ ⁅y₁, y₂⁆ * e⁻¹ := by
      rw [map_commutatorElement, map_commutatorElement, hy₁', hy₂']
      simp only [commutatorElement_def]
      group
    have hz₁ := hz hy₁ hy₁'
    have hz₂ := hz hy₂ hy₂'
    have hc : ⁅y₁', y₂'⁆ = ⁅y₁, y₂⁆ := by
      calc ⁅y₁', y₂'⁆ = ⁅y₁ * (y₁⁻¹ * y₁'), y₂ * (y₂⁻¹ * y₂')⁆ := by
            rw [mul_inv_cancel_left, mul_inv_cancel_left]
        _ = ⁅y₁, y₂⁆ := by
            rw [commutatorElement_mul_central_left hz₁, commutatorElement_mul_central_right hz₂]
    rw [hc] at hconj
    calc e * ψ ⁅y₁, y₂⁆ = e * ψ ⁅y₁, y₂⁆ * e⁻¹ * e := by group
      _ = ψ ⁅y₁, y₂⁆ * e := by rw [← hconj]
  have hS' := isSubCoreFamily_comap_of_central π hπ hπker hodd hS
  have hS'' : LayerCores.IsSubCoreFamily ⁅M, M⁆ (fun c => derivedPreimage π (S c)) := by
    have h := hS'.inf_of_commutator_le (N := ⁅M, M⁆) le_rfl
    rwa [inf_eq_right.mpr (Subgroup.commutator_le_self M)] at h
  have hC₀H : (⁅M, M⁆).map ψ ≤ H := Subgroup.map_le_iff_le_comap.mpr hMH
  have hnorm : (((⁅M, M⁆).map ψ).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hC₀H]
    rintro _ k ⟨s, hs, rfl⟩ hk
    obtain ⟨u, hu, rfl⟩ := hHM hk
    exact ⟨u * s * u⁻¹, conj_mem_commutator_self hu hs, by rw [map_mul, map_mul, map_inv]⟩
  have hcommH : ⁅H, H⁆ ≤ (⁅M, M⁆).map ψ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hHM hHM
  exact (LayerFacts.ggLayer_of_subcore ψ hψker hC₀H hnorm hcommH hS'').2

end Model

end LayerSixE

end CFSG.StandardType

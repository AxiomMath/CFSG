module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

open Subgroup CFSG.AGLEmbedding
open scoped commutatorElement

theorem commutatorElement_mul_central_left {K : Type*} [Group K] {a b z : K}
    (hz : z ∈ center K) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hz' := mem_center_iff.mp hz b
  simp only [commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hz']; group
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_central_right {K : Type*} [Group K] {a b z : K}
    (hz : z ∈ center K) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have hz' := mem_center_iff.mp hz a⁻¹
  simp only [commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [hz']; group
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_central_both {K : Type*} [Group K] {a b z w : K}
    (hz : z ∈ center K) (hw : w ∈ center K) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_central_left hz, commutatorElement_mul_central_right hw]

theorem exists_section_of_kernelTrivial {E G Q : Type} [Group E] [Finite E] [Group G] [Group Q]
    [Finite Q] (π : E →* G) (hπ : Function.Surjective π) (hker : π.ker ≤ center E)
    (hp : IsPGroup 3 π.ker) (ι : Q →* G) (hperf : Group.IsPerfect Q)
    (hkt : KernelTrivialAt Q 3) : ∃ s : Q →* E, ∀ q, π (s q) = ι q := by
  classical
  let P : Subgroup (Q × E) :=
    MonoidHom.eqLocus (ι.comp (MonoidHom.fst Q E)) (π.comp (MonoidHom.snd Q E))
  have hmemP : ∀ x : Q × E, x ∈ P ↔ ι x.1 = π x.2 := fun x => Iff.rfl
  let p : P →* Q := (MonoidHom.fst Q E).comp P.subtype
  have hps : Function.Surjective p := by
    intro q
    obtain ⟨e, he⟩ := hπ (ι q)
    exact ⟨⟨(q, e), (hmemP _).2 he.symm⟩, rfl⟩
  have hker' : ∀ x : P, x ∈ p.ker ↔ (x : Q × E).1 = 1 := fun x => Iff.rfl
  have hker_mem : ∀ x : P, x ∈ p.ker → π (x : Q × E).2 = 1 := by
    intro x hx
    have h1 := (hmemP _).1 x.2
    rw [(hker' x).1 hx, map_one] at h1
    exact h1.symm
  have hcentral : ∀ x : P, x ∈ p.ker → ∀ y : P, y * x = x * y := by
    intro x hx y
    have hxc : (x : Q × E).2 ∈ center E := hker (MonoidHom.mem_ker.2 (hker_mem x hx))
    apply Subtype.ext
    have h1 : (x : Q × E).1 = 1 := (hker' x).1 hx
    refine Prod.ext ?_ ?_
    · show (y : Q × E).1 * (x : Q × E).1 = (x : Q × E).1 * (y : Q × E).1
      rw [h1, mul_one, one_mul]
    · show (y : Q × E).2 * (x : Q × E).2 = (x : Q × E).2 * (y : Q × E).2
      exact mem_center_iff.1 hxc _
  have hpK : ∀ x : P, x ∈ p.ker → ∃ n : ℕ, x ^ 3 ^ n = 1 := by
    intro x hx
    have h1 : (x : Q × E).1 = 1 := (hker' x).1 hx
    obtain ⟨n, hn⟩ := hp ⟨(x : Q × E).2, MonoidHom.mem_ker.2 (hker_mem x hx)⟩
    refine ⟨n, Subtype.ext (Prod.ext ?_ ?_)⟩
    · show ((x : Q × E) ^ 3 ^ n).1 = 1
      rw [Prod.pow_fst, h1, one_pow]
    · show ((x : Q × E) ^ 3 ^ n).2 = 1
      rw [Prod.pow_snd]
      exact congrArg Subtype.val hn
  let D : Subgroup P := commutator P
  have htop : (⊤ : Subgroup P).map p = ⊤ := by
    rw [← MonoidHom.range_eq_map]; exact MonoidHom.range_eq_top.2 hps
  have hDmap : D.map p = ⊤ := by
    have h1 : D.map p = commutator Q := by
      show (commutator P).map p = _
      rw [_root_.commutator_def, Subgroup.map_commutator, htop, ← _root_.commutator_def]
    rw [h1]; exact Group.isPerfect_def.1 hperf
  have hsup : ∀ x : P, ∃ d ∈ D, d⁻¹ * x ∈ p.ker := by
    intro x
    obtain ⟨d, hd, hdx⟩ := (Subgroup.mem_map.1 (hDmap ▸ (Subgroup.mem_top (p x))))
    refine ⟨d, hd, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]
  have hDperf : ⁅D, D⁆ = D := by
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) ?_
    · exact D.mul_mem (D.mul_mem (D.mul_mem ha hb) (D.inv_mem ha)) (D.inv_mem hb)
    · show (commutator P) ≤ ⁅D, D⁆
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨a', ha', hka⟩ := hsup a
      obtain ⟨b', hb', hkb⟩ := hsup b
      have ea : a = a' * (a'⁻¹ * a) := by group
      have eb : b = b' * (b'⁻¹ * b) := by group
      have c1 : ∀ g : P, g * (a'⁻¹ * a) = (a'⁻¹ * a) * g := fun g => hcentral _ hka g
      have c2 : ∀ g : P, g * (b'⁻¹ * b) = (b'⁻¹ * b) * g := fun g => hcentral _ hkb g
      rw [ea, eb, commutatorElement_mul_central_both (mem_center_iff.2 c1) (mem_center_iff.2 c2)]
      exact Subgroup.commutator_mem_commutator ha' hb'
  have hDperf' : Group.IsPerfect ↥D := by
    rw [Group.isPerfect_def]
    refine Subgroup.map_injective D.subtype_injective ?_
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    simpa using hDperf
  let pD : D →* Q := p.comp D.subtype
  have hpDs : Function.Surjective pD := by
    intro q
    obtain ⟨x, hx, hxq⟩ := (Subgroup.mem_map.1 (hDmap ▸ (Subgroup.mem_top q)))
    exact ⟨⟨x, hx⟩, hxq⟩
  have hcenD : pD.ker ≤ center D := by
    intro x hx
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (hcentral (x : P) hx (y : P))
  have hpD : IsPGroup 3 pD.ker := by
    intro x
    obtain ⟨n, hn⟩ := hpK (x.1 : P) x.2
    exact ⟨n, Subtype.ext (Subtype.ext hn)⟩
  have hbot : pD.ker = ⊥ := hkt ↥D pD hpDs hcenD hpD
  have hinj : Function.Injective pD := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hbot
  let e : D ≃* Q := MulEquiv.ofBijective pD ⟨hinj, hpDs⟩
  let s : Q →* E := ((MonoidHom.snd Q E).comp (P.subtype.comp D.subtype)).comp e.symm.toMonoidHom
  refine ⟨s, fun q => ?_⟩
  have hq : pD (e.symm q) = q := e.apply_symm_apply q
  have h1 := (hmemP (e.symm q : P)).1 (e.symm q : P).2
  have h2 : ((e.symm q : D) : P).1.1 = q := hq
  show π ((((e.symm q : D) : P) : Q × E).2) = ι q
  rw [← h1, h2]

theorem surjective_of_perfect_central {E G Q : Type*} [Group E] [Group G] [Group Q] (π : E →* G)
    (hker : π.ker ≤ center E) (θ : Q →* E) (hs : Function.Surjective (π.comp θ))
    (hperf : Group.IsPerfect E) : Function.Surjective θ := by
  have hdecomp : ∀ e : E, ∃ r : Q, ∃ k ∈ center E, e = θ r * k := by
    intro e
    obtain ⟨r, hr⟩ := hs (π e)
    refine ⟨r, (θ r)⁻¹ * e, hker ?_, by group⟩
    have hr' : π (θ r) = π e := hr
    rw [MonoidHom.mem_ker, map_mul, map_inv, hr', inv_mul_cancel]
  have hcomm : _root_.commutator E ≤ θ.range := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨r₁, k₁, hk₁, rfl⟩ := hdecomp a
    obtain ⟨r₂, k₂, hk₂, rfl⟩ := hdecomp b
    rw [commutatorElement_mul_central_both hk₁ hk₂, commutatorElement_def]
    exact θ.range.mul_mem (θ.range.mul_mem (θ.range.mul_mem ⟨r₁, rfl⟩ ⟨r₂, rfl⟩)
      (θ.range.inv_mem ⟨r₁, rfl⟩)) (θ.range.inv_mem ⟨r₂, rfl⟩)
  intro e
  have h := hcomm
  rw [hperf.commutator_eq_top] at h
  exact h (Subgroup.mem_top e)

theorem exists_sq_eq_of_isPGroup_three {K : Type*} [Group K] (hK : IsPGroup 3 K) (d : K) :
    ∃ a : K, a * a = d := by
  obtain ⟨n, hn⟩ := hK d
  refine ⟨d ^ ((3 ^ n + 1) / 2), ?_⟩
  obtain ⟨m, hm⟩ : Odd (3 ^ n) := Odd.pow (by decide)
  have h1 : (3 ^ n + 1) / 2 = m + 1 := by omega
  rw [h1, ← pow_add]
  have h2 : m + 1 + (m + 1) = 3 ^ n + 1 := by omega
  rw [h2, pow_succ, hn, one_mul]

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

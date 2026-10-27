module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.H13.P31Sz

open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section Inner

variable {Y : Type*} [Group Y]

theorem mem_centralizer_of_inner (N : Subgroup Y)
    (h3 : ∀ g : ↥N ⧸ Subgroup.center ↥N, g ^ 3 = 1 → g = 1) {p : Y} (hp3 : p ^ 3 = 1) {n : ↥N}
    (hconj : ∀ m : ↥N, (n : Y) * m * (n : Y)⁻¹ = p * m * p⁻¹) :
    p ∈ Subgroup.centralizer (N : Set Y) := by
  set c : Y := (n : Y)⁻¹ * p with hc
  have hcC : c ∈ Subgroup.centralizer (N : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 := hconj ⟨m, hm⟩
    simp only at h1
    have h2 : c * m = m * c := by
      rw [hc]
      calc (n : Y)⁻¹ * p * m
          = (n : Y)⁻¹ * (p * m * p⁻¹) * p := by group
        _ = (n : Y)⁻¹ * ((n : Y) * m * (n : Y)⁻¹) * p := by rw [h1]
        _ = m * ((n : Y)⁻¹ * p) := by group
    exact h2.symm
  have hpnc : p = (n : Y) * c := by rw [hc]; group
  have hnc : Commute (n : Y) c := Subgroup.mem_centralizer_iff.1 hcC (n : Y) n.2
  have hn3 : (n : Y) ^ 3 = (c ^ 3)⁻¹ := by
    have : p ^ 3 = (n : Y) ^ 3 * c ^ 3 := by
      rw [hpnc]; exact hnc.mul_pow 3
    rw [hp3] at this
    exact eq_inv_of_mul_eq_one_left this.symm
  have hn3Z : (n ^ 3 : ↥N) ∈ Subgroup.center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    have h1 : ((n ^ 3 : ↥N) : Y) = (c ^ 3)⁻¹ := by simpa using hn3
    rw [Subgroup.coe_mul, Subgroup.coe_mul, h1]
    have hc3 : c ^ 3 ∈ Subgroup.centralizer (N : Set Y) := Subgroup.pow_mem _ hcC 3
    have hc3' : (c ^ 3)⁻¹ ∈ Subgroup.centralizer (N : Set Y) := Subgroup.inv_mem _ hc3
    exact (Subgroup.mem_centralizer_iff.1 hc3' (m : Y) m.2)
  have hnbar : (QuotientGroup.mk n : ↥N ⧸ Subgroup.center ↥N) = 1 := by
    apply h3
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hn3Z
  have hnZ : n ∈ Subgroup.center ↥N := (QuotientGroup.eq_one_iff _).1 hnbar
  have hnC : (n : Y) ∈ Subgroup.centralizer (N : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 := congrArg (fun z : ↥N => (z : Y)) (Subgroup.mem_center_iff.1 hnZ ⟨m, hm⟩)
    simpa using h1
  rw [hpnc]
  exact Subgroup.mul_mem _ hnC hcC

end Inner

section Cls

variable {Y : Type*} [Group Y]

@[expose] noncomputable def outCls (N : Subgroup Y) (g : Y) : Outer ↥N := by
  classical
  exact if hg : g ∈ Subgroup.normalizer (N : Set Y) then
    QuotientGroup.mk' (inner ↥N) (N.normalizerMonoidHom ⟨g, hg⟩) else 1

theorem outCls_of_mem {N : Subgroup Y} {g : Y} (hg : g ∈ Subgroup.normalizer (N : Set Y)) :
    outCls N g = QuotientGroup.mk' (inner ↥N) (N.normalizerMonoidHom ⟨g, hg⟩) := by
  unfold outCls
  rw [dif_pos hg]

theorem outCls_mul {N : Subgroup Y} {g h : Y} (hg : g ∈ Subgroup.normalizer (N : Set Y))
    (hh : h ∈ Subgroup.normalizer (N : Set Y)) : outCls N (g * h) = outCls N g * outCls N h := by
  rw [outCls_of_mem hg, outCls_of_mem hh,
    outCls_of_mem ((Subgroup.normalizer (N : Set Y)).mul_mem hg hh), ← map_mul, ← map_mul]
  rfl

theorem outCls_one {N : Subgroup Y} : outCls N 1 = 1 := by
  rw [outCls_of_mem (Subgroup.normalizer (N : Set Y)).one_mem]
  have : (⟨1, (Subgroup.normalizer (N : Set Y)).one_mem⟩ : ↥(Subgroup.normalizer (N : Set Y))) = 1 :=
    rfl
  rw [this, map_one, map_one]

theorem outCls_inv {N : Subgroup Y} {g : Y} (hg : g ∈ Subgroup.normalizer (N : Set Y)) :
    outCls N g⁻¹ = (outCls N g)⁻¹ := by
  have h1 : outCls N (g⁻¹ * g) = outCls N g⁻¹ * outCls N g :=
    outCls_mul ((Subgroup.normalizer (N : Set Y)).inv_mem hg) hg
  rw [inv_mul_cancel, outCls_one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem outCls_conj {N : Subgroup Y} (hcomm : ∀ a b : Outer ↥N, a * b = b * a) {g h : Y}
    (hg : g ∈ Subgroup.normalizer (N : Set Y)) (hh : h ∈ Subgroup.normalizer (N : Set Y)) :
    outCls N (h * g * h⁻¹) = outCls N g := by
  rw [outCls_mul ((Subgroup.normalizer (N : Set Y)).mul_mem hh hg)
    ((Subgroup.normalizer (N : Set Y)).inv_mem hh), outCls_mul hh hg, outCls_inv hh, mul_assoc,
    hcomm (outCls N g), ← mul_assoc, mul_inv_cancel, one_mul]

theorem exists_inner_of_outCls_eq_one {N : Subgroup Y} {g : Y}
    (hg : g ∈ Subgroup.normalizer (N : Set Y)) (h : outCls N g = 1) :
    ∃ n : ↥N, ∀ m : ↥N, (n : Y) * m * (n : Y)⁻¹ = g * m * g⁻¹ := by
  rw [outCls_of_mem hg, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n, fun m => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥N => ((φ m : ↥N) : Y)) hn
  simpa using h1

end Cls

section Swap

variable {Y : Type*} [Group Y]

theorem outCls_mul_swap (N : Subgroup Y) (hcomm : ∀ a b : Outer ↥N, a * b = b * a) (t : Y)
    (A T' : Subgroup Y) (hAN : A ≤ Subgroup.normalizer (N : Set Y)) (htT : t ∈ T')
    (htN : t ∉ Subgroup.normalizer (N : Set Y))
    (hdich : ∀ x ∈ T', x ∈ Subgroup.normalizer (N : Set Y) ∨
      t⁻¹ * x ∈ Subgroup.normalizer (N : Set Y))
    (hTA : ∀ x ∈ T', ∀ a ∈ A, x * a * x⁻¹ ∈ A) (hAT : A ≤ ⁅A, T'⁆) :
    ∀ a ∈ A, outCls N a * outCls N (t⁻¹ * a * t) = 1 := by
  letI : CommGroup (Outer ↥N) := { (inferInstance : Group (Outer ↥N)) with mul_comm := hcomm }
  set Nn : Subgroup Y := Subgroup.normalizer (N : Set Y) with hNn
  have htinv : t⁻¹ ∈ T' := T'.inv_mem htT
  have hconjA : ∀ a ∈ A, t⁻¹ * a * t ∈ A := fun a ha => by
    have := hTA t⁻¹ htinv a ha
    simpa using this
  let π : Y → Outer ↥N := fun a => outCls N a * outCls N (t⁻¹ * a * t)
  have hπone : π 1 = 1 := by
    show outCls N 1 * outCls N (t⁻¹ * 1 * t) = 1
    rw [show t⁻¹ * 1 * t = 1 by group, outCls_one, one_mul]
  have hπmul : ∀ a ∈ A, ∀ b ∈ A, π (a * b) = π a * π b := by
    intro a ha b hb
    have hta := hAN (hconjA a ha)
    have htb := hAN (hconjA b hb)
    show outCls N (a * b) * outCls N (t⁻¹ * (a * b) * t) =
      (outCls N a * outCls N (t⁻¹ * a * t)) * (outCls N b * outCls N (t⁻¹ * b * t))
    rw [show t⁻¹ * (a * b) * t = (t⁻¹ * a * t) * (t⁻¹ * b * t) by group,
      outCls_mul (hAN ha) (hAN hb), outCls_mul hta htb]
    exact mul_mul_mul_comm _ _ _ _
  have hπinv : ∀ a ∈ A, π a⁻¹ = (π a)⁻¹ := by
    intro a ha
    have hta := hAN (hconjA a ha)
    show outCls N a⁻¹ * outCls N (t⁻¹ * a⁻¹ * t) = (outCls N a * outCls N (t⁻¹ * a * t))⁻¹
    rw [show t⁻¹ * a⁻¹ * t = (t⁻¹ * a * t)⁻¹ by group, outCls_inv (hAN ha), outCls_inv hta,
      mul_inv]
  have ht2 : t * t ∈ Nn := by
    rcases hdich (t * t) (T'.mul_mem htT htT) with h | h
    · exact h
    · exact absurd (by simpa using h) htN
  have hconjN : ∀ s ∈ T', s ∈ Nn → t⁻¹ * s * t ∈ Nn := by
    intro s hs hsN
    rcases hdich (s * t) (T'.mul_mem hs htT) with h | h
    · exact absurd (by simpa using Nn.mul_mem (Nn.inv_mem hsN) h) htN
    · simpa [mul_assoc] using h
  have hcase1 : ∀ s ∈ T', s ∈ Nn → ∀ a ∈ A, π (s * a * s⁻¹) = π a := by
    intro s hs hsN a ha
    show outCls N (s * a * s⁻¹) * outCls N (t⁻¹ * (s * a * s⁻¹) * t) =
      outCls N a * outCls N (t⁻¹ * a * t)
    rw [show t⁻¹ * (s * a * s⁻¹) * t = (t⁻¹ * s * t) * (t⁻¹ * a * t) * (t⁻¹ * s * t)⁻¹ by group,
      outCls_conj hcomm (hAN ha) hsN, outCls_conj hcomm (hAN (hconjA a ha)) (hconjN s hs hsN)]
  have hcaset : ∀ a ∈ A, π (t * a * t⁻¹) = π a := by
    intro a ha
    have h1 : outCls N (t * a * t⁻¹) = outCls N (t⁻¹ * a * t) := by
      rw [show t * a * t⁻¹ = (t * t) * (t⁻¹ * a * t) * (t * t)⁻¹ by group]
      exact outCls_conj hcomm (hAN (hconjA a ha)) ht2
    show outCls N (t * a * t⁻¹) * outCls N (t⁻¹ * (t * a * t⁻¹) * t) =
      outCls N a * outCls N (t⁻¹ * a * t)
    rw [h1, show t⁻¹ * (t * a * t⁻¹) * t = a by group, mul_comm]
  have hπconj : ∀ x ∈ T', ∀ a ∈ A, π (x * a * x⁻¹) = π a := by
    intro x hx a ha
    rcases hdich x hx with hxN | hxN
    · exact hcase1 x hx hxN a ha
    · have hs : t⁻¹ * x ∈ T' := T'.mul_mem htinv hx
      have hxs : x * a * x⁻¹ = t * ((t⁻¹ * x) * a * (t⁻¹ * x)⁻¹) * t⁻¹ := by group
      rw [hxs, hcaset _ (hTA _ hs a ha), hcase1 _ hs hxN a ha]
  let Kπ : Subgroup Y :=
    { carrier := {a | a ∈ A ∧ π a = 1}
      one_mem' := ⟨A.one_mem, hπone⟩
      mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
        rw [hπmul a ha.1 b hb.1, ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by rw [hπinv a ha.1, ha.2, inv_one]⟩ }
  have hle : ⁅A, T'⁆ ≤ Kπ := by
    rw [Subgroup.commutator_le]
    intro a ha x hx
    have hxa : x * a⁻¹ * x⁻¹ ∈ A := hTA x hx a⁻¹ (A.inv_mem ha)
    have hc : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by
      rw [commutatorElement_def]; group
    refine ⟨?_, ?_⟩
    · rw [hc]
      exact A.mul_mem ha hxa
    · show π ⁅a, x⁆ = 1
      rw [hc, hπmul a ha _ hxa, hπconj x hx a⁻¹ (A.inv_mem ha), hπinv a ha, mul_inv_cancel]
  intro a ha
  exact (hle (hAT ha)).2

theorem exists_ne_one_centralizes_pair (N : Subgroup Y) (hOut : IsCyclic (Outer ↥N))
    (h3 : ∀ g : ↥N ⧸ Subgroup.center ↥N, g ^ 3 = 1 → g = 1) (t : Y) (A P T' : Subgroup Y)
    (hAN : A ≤ Subgroup.normalizer (N : Set Y)) (htT : t ∈ T')
    (htN : t ∉ Subgroup.normalizer (N : Set Y))
    (hdich : ∀ x ∈ T', x ∈ Subgroup.normalizer (N : Set Y) ∨
      t⁻¹ * x ∈ Subgroup.normalizer (N : Set Y))
    (hTA : ∀ x ∈ T', ∀ a ∈ A, x * a * x⁻¹ ∈ A) (hAT : A ≤ ⁅A, T'⁆) (hPA : P ≤ A)
    (hP3 : ∀ p ∈ P, p ^ 3 = 1) (hPnc : ¬ IsCyclic ↥P) :
    ∃ x ∈ P, x ≠ 1 ∧ x ∈ Subgroup.centralizer (N : Set Y) ∧
      x ∈ Subgroup.centralizer ((N.map (MulAut.conj t).toMonoidHom : Subgroup Y) : Set Y) := by
  have hcomm : ∀ a b : Outer ↥N, a * b = b * a := fun a b => IsCyclic.commGroup.mul_comm a b
  have hswap := outCls_mul_swap N hcomm t A T' hAN htT htN hdich hTA hAT
  have htinv : t⁻¹ ∈ T' := T'.inv_mem htT
  have hPN : P ≤ Subgroup.normalizer (N : Set Y) := hPA.trans hAN
  let θ : ↥P →* Outer ↥N :=
    (QuotientGroup.mk' (inner ↥N)).comp (N.normalizerMonoidHom.comp (Subgroup.inclusion hPN))
  have hker : θ.ker ≠ ⊥ := by
    intro hbot
    exact hPnc (isCyclic_of_injective θ ((MonoidHom.ker_eq_bot_iff θ).1 hbot))
  obtain ⟨⟨⟨p, hpP⟩, hpker⟩, hp1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hker
  have hp1' : p ≠ 1 := fun h => hp1 (Subtype.ext (Subtype.ext h))
  have hpA : p ∈ A := hPA hpP
  have hcls : outCls N p = 1 := by
    rw [outCls_of_mem (hAN hpA)]
    exact (MonoidHom.mem_ker).1 hpker
  have hp3 : p ^ 3 = 1 := hP3 p hpP
  have hqA : t⁻¹ * p * t ∈ A := by
    have := hTA t⁻¹ htinv p hpA
    simpa using this
  have hq : outCls N (t⁻¹ * p * t) = 1 := by
    have := hswap p hpA
    rwa [hcls, one_mul] at this
  obtain ⟨n₁, hn₁⟩ := exists_inner_of_outCls_eq_one (hAN hpA) hcls
  obtain ⟨n₂, hn₂⟩ := exists_inner_of_outCls_eq_one (hAN hqA) hq
  have hpC : p ∈ Subgroup.centralizer (N : Set Y) := mem_centralizer_of_inner N h3 hp3 hn₁
  have hq3 : (t⁻¹ * p * t) ^ 3 = 1 := by
    rw [show t⁻¹ * p * t = t⁻¹ * p * t⁻¹⁻¹ by rw [inv_inv], conj_pow, hp3]
    simp
  have hqC : t⁻¹ * p * t ∈ Subgroup.centralizer (N : Set Y) :=
    mem_centralizer_of_inner N h3 hq3 hn₂
  refine ⟨p, hpP, hp1', hpC, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨m, hm, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.1 hqC m hm
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc t * m * t⁻¹ * p = t * (m * (t⁻¹ * p * t)) * t⁻¹ := by group
    _ = t * ((t⁻¹ * p * t) * m) * t⁻¹ := by rw [h1]
    _ = p * (t * m * t⁻¹) := by group

end Swap

end CFSG.Quasithin.H13.P31Sz

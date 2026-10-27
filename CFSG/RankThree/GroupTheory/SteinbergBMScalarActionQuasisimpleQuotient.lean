module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem scalar_critical_action_centralizes_quasisimple_solvable_quotient [Finite G] {q : ℕ}
    (hq : q.Prime) {L N D B : Subgroup G} (hL : ⁅L, L⁆ = L) [(N.subgroupOf L).Normal]
    (hNs : Group.IsSolvable N) (hQ : CFSG.IsQuasisimple (L ⧸ N.subgroupOf L))
    (hLD : L ≤ normalizer (D : Set G)) (hDq : IsPGroup q D) (hLDc : ⁅L, D⁆ ≠ ⊥)
    (hBL : B ≤ normalizer (L : Set G)) (hBD : B ≤ normalizer (D : Set G))
    (hscalar : ∀ b ∈ B, ∃ k : ℕ, ∀ d ∈ D, (b * d * b⁻¹)⁻¹ * d ^ k ∈ CFSG.inSubgroup frattini D) :
    ⁅L, B⁆ ≤ N := by
  have : Fact q.Prime := ⟨hq⟩
  set X := normalizer (D : Set G) with hXdef
  set ρ₀ : X →* MulAut D := D.normalizerMonoidHom with hρ₀
  have hρ₀app : ∀ (x : X) (d : D), ((ρ₀ x d : D) : G) = x * d * (x : G)⁻¹ := fun _ _ => rfl
  obtain ⟨hκapp, hκq⟩ := CFSG.GroupTheory.frattini_automorphism_kernel (p := q) hDq
  set ρ : X →* MulAut (D ⧸ frattini D) := (quotientAutomorphism (frattini D)).comp ρ₀ with hρ
  have hρapp : ∀ (x : X) (d : D),
      ρ x (d : D ⧸ frattini D) = ((ρ₀ x d : D) : D ⧸ frattini D) := fun x d => hκapp (ρ₀ x) d
  have hBscalar : ∀ b (hb : b ∈ B), ∃ k : ℕ, ∀ v : D ⧸ frattini D, ρ ⟨b, hBD hb⟩ v = v ^ k := by
    intro b hb
    obtain ⟨k, hk⟩ := hscalar b hb
    refine ⟨k, fun v => ?_⟩
    induction v using QuotientGroup.induction_on with
    | H d =>
      rw [hρapp, ← QuotientGroup.mk_pow, QuotientGroup.eq]
      obtain ⟨y, hy, hyx⟩ := hk d d.2
      have hyx' : (y : G) = (b * ↑d * b⁻¹)⁻¹ * ↑d ^ k := hyx
      have hy' : (ρ₀ ⟨b, hBD hb⟩ d)⁻¹ * d ^ k = y := by
        apply Subtype.ext
        rw [hyx', coe_mul, coe_inv, coe_pow, hρ₀app]
      rw [hy']
      exact hy
  have hcommρ : ∀ (x : X), (x : G) ∈ L → ∀ (y : X), (y : G) ∈ B → ρ ⁅x, y⁆ = 1 := by
    intro x hx y hy
    obtain ⟨k, hk⟩ := hBscalar y hy
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    ext v
    rw [MulAut.mul_apply, MulAut.mul_apply, show y = ⟨y, hBD hy⟩ from rfl, hk, hk, map_pow]
  set ψ : L →* MulAut (D ⧸ frattini D) := ρ.comp (Subgroup.inclusion hLD) with hψ
  have hLtop : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ := by
    apply map_injective L.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, hL]
  have hC₀ : ψ.ker ≠ ⊤ := by
    intro htop
    apply hLDc
    set φ : L →* MulAut D := ρ₀.comp (Subgroup.inclusion hLD) with hφ
    have hφκ : φ.range ≤ (quotientAutomorphism (frattini D)).ker := by
      rintro _ ⟨l, rfl⟩
      have h : l ∈ ψ.ker := by
        rw [htop]
        exact mem_top l
      exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp h)
    have hφq : IsPGroup q φ.range := hκq.to_le hφκ
    have hφperf : Group.IsPerfect φ.range := by
      rw [Subgroup.isPerfect_iff, MonoidHom.range_eq_map, ← map_commutator, hLtop]
    have hφbot : φ.range = ⊥ := by
      by_contra hne
      have : Nontrivial φ.range := (nontrivial_iff_ne_bot _).mpr hne
      exact Group.IsPerfect.not_isNilpotent φ.range hφq.isNilpotent
    rw [eq_bot_iff, commutator_le]
    intro l hl d hd
    have h1 : φ ⟨l, hl⟩ = 1 := by
      have : φ ⟨l, hl⟩ ∈ φ.range := ⟨⟨l, hl⟩, rfl⟩
      rwa [hφbot, mem_bot] at this
    have h2 : l * d * l⁻¹ = d := by
      have := congrArg (fun σ : MulAut D => ((σ ⟨d, hd⟩ : D) : G)) h1
      exact this
    rw [mem_bot, commutatorElement_def, h2, mul_inv_cancel]
  have hN₁s : Group.IsSolvable (N.subgroupOf L) := by
    let f : N.subgroupOf L →* N := MonoidHom.mk' (fun x => ⟨((x : L) : G), x.2⟩) fun _ _ => rfl
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun x y h => ?_
    have h' := congrArg (fun z : N => (z : G)) h
    exact Subtype.ext (Subtype.ext h')
  have hCcent : ψ.ker.map (QuotientGroup.mk' (N.subgroupOf L)) ≤ center (L ⧸ N.subgroupOf L) := by
    have hn := (MonoidHom.normal_ker ψ).map (QuotientGroup.mk' (N.subgroupOf L))
      (QuotientGroup.mk'_surjective _)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hn with h | h
    · exfalso
      apply hC₀
      have hsup : ψ.ker ⊔ N.subgroupOf L = ⊤ := by
        have := congrArg (Subgroup.comap (QuotientGroup.mk' (N.subgroupOf L))) h
        rwa [comap_map_eq, QuotientGroup.ker_mk', comap_top] at this
      have hsurj : Function.Surjective
          ((QuotientGroup.mk' ψ.ker).comp (N.subgroupOf L).subtype) := by
        intro z
        obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective ψ.ker z
        have hl : l ∈ ((ψ.ker ⊔ N.subgroupOf L : Subgroup L) : Set L) := by
          rw [hsup]
          exact mem_top l
        rw [normal_mul ψ.ker (N.subgroupOf L)] at hl
        obtain ⟨c, hc, n, hn, rfl⟩ := hl
        refine ⟨⟨n, hn⟩, ?_⟩
        rw [MonoidHom.comp_apply, coe_subtype, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq]
        show n⁻¹ * (c * n) ∈ ψ.ker
        have e' : n⁻¹ * (c * n) = n⁻¹ * c * n := by group
        rw [e']
        exact (MonoidHom.normal_ker ψ).conj_mem c hc n⁻¹ |> fun h => by simpa using h
      have hQs : Group.IsSolvable (L ⧸ ψ.ker) := Group.isSolvable_of_surjective hsurj
      have hQp : Group.IsPerfect (L ⧸ ψ.ker) := by
        rw [Group.isPerfect_def, _root_.commutator_def,
          ← map_top_of_surjective _ (QuotientGroup.mk'_surjective ψ.ker), ← map_commutator,
          hLtop]
      by_contra hne
      obtain ⟨l, -, hl⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hne)
      have : Nontrivial (L ⧸ ψ.ker) :=
        ⟨⟨(l : L ⧸ ψ.ker), 1, fun h => hl ((QuotientGroup.eq_one_iff l).mp h)⟩⟩
      exact Group.IsPerfect.not_isSolvable _ hQs
    · exact h
  have hfin : ∀ b ∈ B, ∀ l ∈ L, l⁻¹ * (b * l * b⁻¹) ∈ N := by
    intro b hb
    have hbl : ∀ l ∈ L, b * l * b⁻¹ ∈ L := fun l hl => (mem_normalizer_iff.mp (hBL hb) l).mp hl
    let β : L →* L := MonoidHom.mk' (fun l => ⟨b * l * b⁻¹, hbl l l.2⟩) fun l₁ l₂ =>
      Subtype.ext (by simp only [coe_mul]; group)
    have hβ : ∀ l : L, ((β l : L) : G) = b * l * b⁻¹ := fun _ => rfl
    set π := QuotientGroup.mk' (N.subgroupOf L) with hπ
    have hcent : ∀ l : L, π (l⁻¹ * β l) ∈ center (L ⧸ N.subgroupOf L) := by
      intro l
      refine hCcent ⟨l⁻¹ * β l, ?_, rfl⟩
      have h := hcommρ ⟨(l : G)⁻¹, hLD (L.inv_mem l.2)⟩ (L.inv_mem l.2) ⟨b, hBD hb⟩ hb
      show ρ ⟨((l⁻¹ * β l : L) : G), _⟩ = 1
      convert h using 2
      apply Subtype.ext
      rw [coe_mul, coe_inv, hβ]
      show (l : G)⁻¹ * (b * l * b⁻¹) = ⁅(l : G)⁻¹, b⁆
      rw [commutatorElement_def, inv_inv]
      group
    let fb : L →* L ⧸ N.subgroupOf L := MonoidHom.mk' (fun l => π (l⁻¹ * β l)) fun l₁ l₂ => by
      have e : (l₁ * l₂)⁻¹ * β (l₁ * l₂) = l₂⁻¹ * (l₁⁻¹ * β l₁) * β l₂ := by
        rw [map_mul]
        group
      rw [e, map_mul, map_mul, map_inv, mem_center_iff.mp (hcent l₁) (π l₂)⁻¹, mul_assoc,
        ← map_inv, ← map_mul]
    have hfbker : _root_.commutator L ≤ fb.ker := by
      rw [_root_.commutator_def, commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mem_center_iff.mp (hcent y) (fb x)
    rw [_root_.commutator_def, hLtop] at hfbker
    intro l hl
    have h := hfbker (mem_top ⟨l, hl⟩)
    rw [MonoidHom.mem_ker] at h
    have h' : (⟨l, hl⟩ : L)⁻¹ * β ⟨l, hl⟩ ∈ N.subgroupOf L := (QuotientGroup.eq_one_iff _).mp h
    exact h'
  rw [commutator_le]
  intro l hl b hb
  have h := hfin b hb l⁻¹ (L.inv_mem hl)
  rw [inv_inv] at h
  rw [commutatorElement_def]
  simpa [mul_assoc] using h

end CFSG.RankThree.GroupTheory.SteinbergBM

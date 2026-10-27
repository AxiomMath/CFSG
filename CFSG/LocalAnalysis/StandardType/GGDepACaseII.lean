module

public import CFSG.LocalAnalysis.StandardType.GGDepAPerm
public import CFSG.LocalAnalysis.StandardType.GGDepAArith
public import CFSG.LocalAnalysis.StandardType.GGDepARefl
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofLinPerm
public import CFSG.LocalAnalysis.StandardType.GGRCAbsIrred
public import CFSG.LocalAnalysis.StandardType.GGRCMonomial
public import CFSG.LocalAnalysis.StandardType.GGRCMonomialHom
public import CFSG.LocalAnalysis.StandardType.GGRCPermMonomial

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nDB2a_cartan_adj (n : ℕ) {i j : Fin n}
    (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) (hne : i ≠ j) :
    CartanMatrix.A n i j = -1 := by
  simp only [CartanMatrix.A, Matrix.of_apply]
  rw [if_neg hne, if_pos h]

private theorem l05nDB2a_cartan_self (n : ℕ) (i : Fin n) : CartanMatrix.A n i i = 2 := by
  simp [CartanMatrix.A]

private theorem l05nDA2_data {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hN : 11 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hcard : Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N))
    (H : Submodule (ZMod p) V) (hHdef : H = Submodule.span (ZMod p) (Set.range h))
    (hH : ha ∈ H) (ρ : Equiv.Perm (Fin N) →* (V ≃ₗ[ZMod p] V))
    (hρA : ∀ σ, ρ σ ∈ Subgroup.closure (Set.range r))
    (hρfaith : ∀ σ, (∀ i, ρ σ (h i) = h i) → σ = 1) :
    ∃ (AH : Subgroup (↥H ≃ₗ[ZMod p] ↥H)) (ψ : Equiv.Perm (Fin N) →* ↥AH)
      (γ : ↥H ≃ₗ[ZMod p] ↥H),
      Module.finrank (ZMod p) ↥H = N - 2 ∧ ZS.AbsIrred p AH ∧
        AH = Subgroup.closure {t | t ∈ AH ∧ GGLinRefl t} ∧
        Nat.card ↥AH ≤ p ^ N * (6 * (p - 1) * Nat.factorial N) ∧ Function.Injective ψ ∧
        (∀ (σ : Equiv.Perm (Fin N)) (v : ↥H), ((((ψ σ : ↥AH) : ↥H ≃ₗ[ZMod p] ↥H) v : ↥H) : V) =
          ρ σ (v : V)) ∧
        γ ∈ AH ∧ ∀ v : ↥H, ((γ v : ↥H) : V) = ra (v : V) := by
  obtain ⟨-, hx_span, hdimSpan⟩ := ggDepA_relation F
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hp
    omega
  have hmemH : ∀ i, h i ∈ H := fun i => by
    rw [hHdef]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hxH : x ∉ H := by
    rw [hHdef]
    exact hx_span
  have hdimH : Module.finrank (ZMod p) ↥H = N - 2 := by
    rw [hHdef]
    exact hdimSpan
  let S : Set (V ≃ₗ[ZMod p] V) := Set.range r ∪ {ra}
  have hS : ∀ s ∈ S, ∀ u ∈ H, s u ∈ H := by
    intro s hs u hu
    rcases hs with ⟨i, rfl⟩ | rfl
    · rw [hr i u]
      exact H.sub_mem hu (H.smul_mem (α i u) (hmemH i))
    · rw [hra u]
      exact H.sub_mem hu (H.smul_mem (αa u) hH)
  obtain ⟨res, hres_apply, hres_card, hres_range⟩ := ggDepA_restrict H S hS
  let A : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure S
  let AH : Subgroup (↥H ≃ₗ[ZMod p] ↥H) := MonoidHom.range res
  have hcardAH : Nat.card ↥AH ≤ p ^ N * (6 * (p - 1) * Nat.factorial N) :=
    le_trans hres_card hcard
  let hU : Option (Fin (N - 1)) → ↥H :=
    fun o => o.elim ⟨ha, hH⟩ (fun i => ⟨h i, hmemH i⟩)
  let αU : Option (Fin (N - 1)) → Module.Dual (ZMod p) ↥H :=
    fun o => o.elim (αa.comp H.subtype) (fun i => (α i).comp H.subtype)
  let gH : Option (Fin (N - 1)) → (↥H ≃ₗ[ZMod p] ↥H) :=
    fun o => o.elim (res ⟨ra, Subgroup.subset_closure (Or.inr rfl)⟩)
      (fun i => res ⟨r i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)⟩)
  have hgH_mem_AH : ∀ o : Option (Fin (N - 1)), gH o ∈ AH := by
    intro o
    cases o with
    | none =>
      exact MonoidHom.mem_range.mpr
        ⟨⟨ra, Subgroup.subset_closure (Or.inr rfl)⟩, rfl⟩
    | some i =>
      exact MonoidHom.mem_range.mpr
        ⟨⟨r i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)⟩, rfl⟩
  have hclosA : AH = Subgroup.closure (Set.range gH) := by
    apply le_antisymm
    · change MonoidHom.range res ≤ Subgroup.closure (Set.range gH)
      rw [hres_range, Subgroup.closure_le]
      intro t ht
      obtain ⟨s, hs, rfl⟩ := ht
      rcases hs with ⟨i, rfl⟩ | rfl
      · exact Subgroup.subset_closure ⟨some i, congrArg res (Subtype.ext rfl)⟩
      · exact Subgroup.subset_closure ⟨none, congrArg res (Subtype.ext rfl)⟩
    · rw [Subgroup.closure_le]
      intro t ht
      obtain ⟨o, rfl⟩ := ht
      exact hgH_mem_AH o
  have hαU : ∀ o : Option (Fin (N - 1)), αU o (hU o) = 2 := by
    intro o
    cases o with
    | none =>
      simpa only [αU, hU, Option.elim_none, LinearMap.comp_apply, Submodule.subtype_apply]
        using hαa
    | some i =>
      have hA : ((CartanMatrix.A (N - 1) i i : ℤ) : ZMod p) = 2 := by
        rw [l05nDB2a_cartan_self (N - 1) i]
        simp
      simpa only [αU, hU, Option.elim_some, LinearMap.comp_apply, Submodule.subtype_apply,
        F.pair i i, hA]
  have hg : ∀ (o : Option (Fin (N - 1))) (w : ↥H), gH o w = w - αU o w • hU o := by
    intro o w
    cases o with
    | none =>
      apply Subtype.ext
      change ((res ⟨ra, Subgroup.subset_closure (Or.inr rfl)⟩ w : ↥H) : V) =
        ((w - αU none w • hU none : ↥H) : V)
      rw [hres_apply]
      show ra (w : V) = ((w - αU none w • hU none : ↥H) : V)
      rw [hra (w : V)]
      simp only [Submodule.coe_sub, Submodule.coe_smul, αU, hU, Option.elim_none,
        LinearMap.comp_apply, Submodule.subtype_apply]
    | some i =>
      apply Subtype.ext
      change ((res ⟨r i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)⟩ w : ↥H) : V) =
        ((w - αU (some i) w • hU (some i) : ↥H) : V)
      rw [hres_apply]
      show r i (w : V) = ((w - αU (some i) w • hU (some i) : ↥H) : V)
      rw [hr i (w : V)]
      simp only [Submodule.coe_sub, Submodule.coe_smul, αU, hU, Option.elim_some,
        LinearMap.comp_apply, Submodule.subtype_apply]
  have hreflU : ∀ o : Option (Fin (N - 1)), GGLinRefl (gH o) :=
    fun o => (ggDepA_linRefl_iff hp2 (gH o)).mpr ⟨hU o, αU o, hαU o, hg o⟩
  have hsome_span :
      Submodule.span (ZMod p) (Set.range (fun i => (⟨h i, hmemH i⟩ : ↥H))) = ⊤ := by
    have heq : H.subtype '' Set.range (fun i => (⟨h i, hmemH i⟩ : ↥H)) = Set.range h := by
      ext v
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨h i, hmemH i⟩, ⟨i, rfl⟩, rfl⟩
    have hmap : Submodule.map H.subtype
        (Submodule.span (ZMod p) (Set.range (fun i => (⟨h i, hmemH i⟩ : ↥H)))) =
        Submodule.map H.subtype (⊤ : Submodule (ZMod p) ↥H) := by
      rw [← Submodule.span_image (f := H.subtype)]
      rw [heq, hHdef, Submodule.map_top, Submodule.range_subtype]
    exact Submodule.map_injective_of_injective Subtype.val_injective hmap
  have hspanU : Submodule.span (ZMod p) (Set.range hU) = ⊤ := by
    apply le_antisymm le_top
    rw [← hsome_span]
    apply Submodule.span_mono
    rintro x ⟨i, rfl⟩
    exact ⟨some i, rfl⟩
  have hkerU : ∀ w : ↥H, (∀ o, αU o w = 0) → w = 0 := by
    intro w hw
    have hwSpan : (w : V) ∈ Submodule.span (ZMod p) ({x} : Set V) := by
      apply F.fix
      intro i
      have h1 := hw (some i)
      simpa only [αU, Option.elim_some, LinearMap.comp_apply, Submodule.subtype_apply] using h1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwSpan
    by_cases hc0 : c = 0
    · apply Subtype.ext
      show (w : V) = (0 : V)
      rw [← hc, hc0, zero_smul]
    · exfalso
      apply hxH
      have hmem : c⁻¹ • (w : V) ∈ H := H.smul_mem _ w.2
      have heq : c⁻¹ • (w : V) = x := by
        rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rwa [heq] at hmem
  have haSpan : ha ∈ Submodule.span (ZMod p) (Set.range h) := by
    simpa [hHdef] using hH
  obtain ⟨bcoef, hbcoef⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp haSpan
  have htwo : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hsum_ne : ∑ i : Fin (N - 1), bcoef i * αa (h i) ≠ 0 := by
    have hsum : ∑ i : Fin (N - 1), bcoef i * αa (h i) = αa ha := by
      rw [← hbcoef, map_sum]
      simp only [map_smul, smul_eq_mul]
    rw [hsum, hαa]
    exact htwo
  obtain ⟨c, -, hcmul⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hαac : αa (h c) ≠ 0 := fun h0 => hcmul (by rw [h0, mul_zero])
  have hpair_self : ∀ i : Fin (N - 1), α i (h i) = 2 := by
    intro i
    have hA : ((CartanMatrix.A (N - 1) i i : ℤ) : ZMod p) = 2 := by
      rw [l05nDB2a_cartan_self (N - 1) i]
      simp
    rw [F.pair i i, hA]
  have hcne : α c ha ≠ 0 := by
    intro h0
    exact hαac (ggDepA_pair_zero_symm hp2 A hnt
      (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩))
      (Subgroup.subset_closure (Or.inr rfl))
      (hr c) hra (hpair_self c) hαa h0)
  let E : Option (Fin (N - 1)) → Option (Fin (N - 1)) → Prop :=
    fun a b => αU a (hU b) ≠ 0 ∧ αU b (hU a) ≠ 0
  have hsymmE : ∀ a b, E a b → E b a := fun a b h => h.symm
  have hpair_adj : ∀ (k : ℕ) (hk : k < N - 1) (hk1 : k + 1 < N - 1),
      E (some ⟨k, hk⟩) (some ⟨k + 1, hk1⟩) := by
    intro k hk hk1
    have hne : (⟨k, hk⟩ : Fin (N - 1)) ≠ ⟨k + 1, hk1⟩ := by
      intro h
      have h1 : k = k + 1 := by simpa using congrArg Fin.val h
      omega
    have hA1 : ((CartanMatrix.A (N - 1) (⟨k, hk⟩ : Fin (N - 1)) ⟨k + 1, hk1⟩ : ℤ) :
        ZMod p) = -1 := by
      rw [l05nDB2a_cartan_adj (N - 1) (Or.inl rfl) hne]
      simp
    have hA2 : ((CartanMatrix.A (N - 1) (⟨k + 1, hk1⟩ : Fin (N - 1)) ⟨k, hk⟩ : ℤ) :
        ZMod p) = -1 := by
      rw [l05nDB2a_cartan_adj (N - 1) (Or.inr rfl) hne.symm]
      simp
    constructor
    · change α ⟨k, hk⟩ (h ⟨k + 1, hk1⟩) ≠ 0
      rw [F.pair (⟨k, hk⟩) (⟨k + 1, hk1⟩), hA1]
      exact neg_ne_zero.mpr one_ne_zero
    · change α ⟨k + 1, hk1⟩ (h ⟨k, hk⟩) ≠ 0
      rw [F.pair (⟨k + 1, hk1⟩) (⟨k, hk⟩), hA2]
      exact neg_ne_zero.mpr one_ne_zero
  have hpair_dn : ∀ (k : ℕ) (hk : k < N - 1) (hk1 : k + 1 < N - 1),
      E (some ⟨k + 1, hk1⟩) (some ⟨k, hk⟩) :=
    fun k hk hk1 => hsymmE _ _ (hpair_adj k hk hk1)
  have hbase_lt : 0 < N - 1 := by omega
  let base : Fin (N - 1) := ⟨0, hbase_lt⟩
  have hup : ∀ (k : ℕ) (hk : k < N - 1),
      Relation.ReflTransGen E (some base) (some ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hbase : (⟨0, hk⟩ : Fin (N - 1)) = base := Fin.ext rfl
      rw [hbase]
    | succ k ih =>
      intro hk
      have hk' : k < N - 1 := by omega
      exact (ih hk').tail (hpair_adj k hk' hk)
  have hdn : ∀ (k : ℕ) (hk : k < N - 1),
      Relation.ReflTransGen E (some ⟨k, hk⟩) (some base) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hbase : (⟨0, hk⟩ : Fin (N - 1)) = base := Fin.ext rfl
      rw [hbase]
    | succ k ih =>
      intro hk
      have hk' : k < N - 1 := by omega
      exact (Relation.ReflTransGen.single (hpair_dn k hk' hk)).trans (ih hk')
  have hconn_none : E none (some c) := by
    constructor
    · change αa (h c) ≠ 0
      exact hαac
    · change α c ha ≠ 0
      exact hcne
  have hnone_start : Relation.ReflTransGen E none (some base) :=
    (Relation.ReflTransGen.single hconn_none).trans (hdn c.val c.isLt)
  have hfrom_none : ∀ o : Option (Fin (N - 1)), Relation.ReflTransGen E none o := by
    intro o
    cases o with
    | none => exact Relation.ReflTransGen.refl
    | some b => exact hnone_start.trans (hup b.val b.isLt)
  have hsome0_none : Relation.ReflTransGen E (some base) none :=
    (hup c.val c.isLt).tail (hsymmE none (some c) hconn_none)
  have hto_none : ∀ o : Option (Fin (N - 1)), Relation.ReflTransGen E o none := by
    intro o
    cases o with
    | none => exact Relation.ReflTransGen.refl
    | some b => exact (hdn b.val b.isLt).trans hsome0_none
  have hconn : ∀ o o' : Option (Fin (N - 1)), Relation.ReflTransGen E o o' :=
    fun o o' => (hto_none o).trans (hfrom_none o')
  have hirr : ZS.AbsIrred p AH :=
    ggRC_absIrred_of_connected hp2 gH hU αU hg hαU hspanU hkerU hconn AH hclosA
  have hgen : AH = Subgroup.closure {t | t ∈ AH ∧ GGLinRefl t} := by
    apply le_antisymm
    · have hsub : Set.range gH ⊆ {t | t ∈ AH ∧ GGLinRefl t} := by
        intro x hx
        obtain ⟨o, rfl⟩ := hx
        exact ⟨hgH_mem_AH o, hreflU o⟩
      have hle := Subgroup.closure_mono hsub
      rwa [← hclosA] at hle
    · rw [Subgroup.closure_le]
      intro x hx
      exact hx.1
  have hρA' : ∀ σ : Equiv.Perm (Fin N), ρ σ ∈ A := fun σ =>
    Subgroup.closure_mono Set.subset_union_left (hρA σ)
  let ρA : Equiv.Perm (Fin N) →* A :=
    { toFun := fun σ => ⟨ρ σ, hρA' σ⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun σ τ => Subtype.ext (map_mul ρ σ τ) }
  let ψ : Equiv.Perm (Fin N) →* ↥AH :=
    { toFun := fun σ => ⟨res (ρA σ), MonoidHom.mem_range.mpr ⟨ρA σ, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        show res (ρA 1) = (1 : ↥H ≃ₗ[ZMod p] ↥H)
        rw [map_one, map_one]
      map_mul' := fun σ τ => by
        apply Subtype.ext
        show res (ρA (σ * τ)) = res (ρA σ) * res (ρA τ)
        rw [map_mul ρA σ τ, map_mul res (ρA σ) (ρA τ)] }
  have hψval : ∀ (σ : Equiv.Perm (Fin N)) (v : ↥H),
      ((((ψ σ : ↥AH) : ↥H ≃ₗ[ZMod p] ↥H) v : ↥H) : V) = ρ σ (v : V) := by
    intro σ v
    show ((res (ρA σ) v : ↥H) : V) = ρ σ (v : V)
    rw [hres_apply]
    rfl
  have hψ_inj : Function.Injective ψ := by
    intro σ τ hστ
    have hker : σ * τ⁻¹ = 1 := by
      apply hρfaith
      intro i
      have h1 : ψ (σ * τ⁻¹) = 1 := by
        rw [map_mul, hστ, map_inv]
        exact mul_inv_cancel (ψ τ)
      have hv := hψval (σ * τ⁻¹) (hU (some i))
      rw [h1] at hv
      simpa [hU] using hv.symm
    exact mul_inv_eq_one.mp hker
  let γ : ↥H ≃ₗ[ZMod p] ↥H := res ⟨ra, Subgroup.subset_closure (Or.inr rfl)⟩
  have hγmem : γ ∈ AH :=
    MonoidHom.mem_range.mpr ⟨⟨ra, Subgroup.subset_closure (Or.inr rfl)⟩, rfl⟩
  have hγapply : ∀ v : ↥H, ((γ v : ↥H) : V) = ra (v : V) := by
    intro v
    exact hres_apply ⟨ra, Subgroup.subset_closure (Or.inr rfl)⟩ v
  exact ⟨AH, ψ, γ, hdimH, hirr, hgen, hcardAH, hψ_inj, hψval, hγmem, hγapply⟩

private theorem l05nDA2_classify (hKG : GGReflClassLargeInput') {p N : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hN : 11 ≤ N) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] (hdim : Module.finrank (ZMod p) U = N - 2)
    (AU : Subgroup (U ≃ₗ[ZMod p] U)) (hirr : ZS.AbsIrred p AU)
    (hgen : AU = Subgroup.closure {t | t ∈ AU ∧ GGLinRefl t})
    (hcard : Nat.card ↥AU ≤ p ^ N * (6 * (p - 1) * Nat.factorial N))
    (ψ : Equiv.Perm (Fin N) →* ↥AU) (hψ : Function.Injective ψ)
    (hsw : ∀ a b : Fin N, a ≠ b → GGLinRefl ((ψ (Equiv.swap a b) : ↥AU) : U ≃ₗ[ZMod p] U)) :
    ∀ t ∈ AU, GGLinRefl t → ∃ σ : Equiv.Perm (Fin N), σ.IsSwap ∧
      ((ψ σ : ↥AU) : U ≃ₗ[ZMod p] U) = t := by
  intro t htAU htRefl
  have hp2 : p ≠ 2 := by omega
  obtain himp | hclass | ⟨_hndvd, e1, _he1⟩ | ⟨_hdvd, e2, _he2⟩ :=
    hKG p hp2 U (N - 2) hdim (by omega) AU hirr hgen
  ·
    exfalso
    obtain ⟨bU, hmon⟩ := ggRC_monomial_of_imprimitive hdim AU hirr hgen himp
    obtain ⟨π, _hπ, _hπker, hπcomm, _hπp⟩ := ggRC_monomial_hom bU AU hmon
    have hπ'comm : IsMulCommutative (π.comp ψ).ker := by
      rw [isMulCommutative_iff]
      intro a b
      apply Subtype.ext
      apply hψ
      show ψ ((a : Equiv.Perm (Fin N)) * (b : Equiv.Perm (Fin N))) =
        ψ ((b : Equiv.Perm (Fin N)) * (a : Equiv.Perm (Fin N)))
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (isMulCommutative_iff.mp hπcomm
        ⟨ψ (a : Equiv.Perm (Fin N)), MonoidHom.mem_ker.mpr a.2⟩
        ⟨ψ (b : Equiv.Perm (Fin N)), MonoidHom.mem_ker.mpr b.2⟩)
    exact ggRC_perm_not_monomial (N := N) (m := N - 2) (by omega) (by omega)
      (π.comp ψ) hπ'comm
  ·
    exfalso
    have h1 : 8 * Nat.card AU < p ^ ((N - 2) * (N - 3) / 2) :=
      lt_of_le_of_lt (Nat.mul_le_mul_left 8 hcard) (ggDepA_order_ineq hp hN)
    have h2 : p ^ ((N - 2) * (N - 3) / 2) ≤ 8 * Nat.card AU := by
      have hh := hclass
      rwa [show N - 2 - 1 = N - 3 by omega] at hh
    exact absurd h1 (not_lt.mpr h2)
  ·
    exfalso
    let ψ1 : Equiv.Perm (Fin N) →* Equiv.Perm (Fin (N - 2 + 1)) := e1.toMonoidHom.comp ψ
    have hψ1inj : Function.Injective ψ1 := e1.injective.comp hψ
    have hle : Nat.card (Equiv.Perm (Fin N)) ≤
        Nat.card (Equiv.Perm (Fin (N - 2 + 1))) :=
      Nat.card_le_card_of_injective ψ1 hψ1inj
    have hleN : Nat.card (Equiv.Perm (Fin N)) = Nat.factorial N := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    have hleM : Nat.card (Equiv.Perm (Fin (N - 2 + 1))) = Nat.factorial (N - 1) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
        show N - 2 + 1 = N - 1 by omega]
    have hle' : Nat.factorial N ≤ Nat.factorial (N - 1) := by
      rw [hleN, hleM] at hle
      exact hle
    have hlt : Nat.factorial (N - 1) < Nat.factorial N :=
      Nat.factorial_lt_of_lt (by omega) (by omega)
    exact absurd hle' (not_le.mpr hlt)
  ·
    have hN2 : N - 2 + 2 = N := by omega
    let ψ' : Equiv.Perm (Fin N) →* Equiv.Perm (Fin (N - 2 + 2)) := e2.toMonoidHom.comp ψ
    have hψ'inj : Function.Injective ψ' := e2.injective.comp hψ
    have hcardPermN : Nat.card (Equiv.Perm (Fin N)) = Nat.factorial N := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    have hcardPermN2 : Nat.card (Equiv.Perm (Fin (N - 2 + 2))) = Nat.factorial N := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin, hN2]
    have hcardψ' : Nat.card (Equiv.Perm (Fin N)) =
        Nat.card (Equiv.Perm (Fin (N - 2 + 2))) := by
      rw [hcardPermN, hcardPermN2]
    have hbijψ' : Function.Bijective ψ' :=
      (Nat.bijective_iff_injective_and_card ψ').mpr ⟨hψ'inj, hcardψ'⟩
    obtain ⟨τ, hτ⟩ := hbijψ'.surjective (e2 ⟨t, htAU⟩)
    have hψτ : ψ τ = ⟨t, htAU⟩ := e2.injective hτ
    let T : Equiv.Perm (Fin N) →* (U ≃ₗ[ZMod p] U) := AU.subtype.comp ψ
    have hTinj : Function.Injective T := by
      intro a b hab
      exact hψ (Subtype.ext hab)
    have hswLin : ∀ x y : Fin N, x ≠ y → IsLinRefl (T (Equiv.swap x y)) := by
      intro x y hxy
      exact (ggDepA_linRefl_iff hp2 (T (Equiv.swap x y))).mp (hsw x y hxy)
    have hTτ : T τ = t := by
      change ((ψ τ : ↥AU) : U ≃ₗ[ZMod p] U) = t
      rw [hψτ]
    have hLin : IsLinRefl (T τ) := by
      rw [hTτ]
      exact (ggDepA_linRefl_iff hp2 t).mp htRefl
    exact ⟨τ, isSwap_of_isLinRefl hp2 T hTinj hswLin hLin, hTτ⟩

private theorem l05nDA2_end {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hN : 5 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hw : αa x ≠ 0)
    (hH : ha ∈ Submodule.span (ZMod p) (Set.range h))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (ρ : Equiv.Perm (Fin N) →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ i, ρ (Equiv.swap (ggDepALeft N i) (ggDepARight N i)) = r i)
    (hρA : ∀ σ, ρ σ ∈ Subgroup.closure (Set.range r)) (hρx : ∀ σ, ρ σ x = x) {a b : Fin N}
    (hab : a ≠ b)
    (hrestr : ∀ v ∈ Submodule.span (ZMod p) (Set.range h), ra v = ρ (Equiv.swap a b) v) :
    False := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  obtain ⟨t, β, htH, hβt, hβ⟩ := ggDepA_perm_swap_refl hp hN F r hr ρ hρ hab
  have ht0 : t ≠ 0 := by
    intro h0
    have hz : β (0 : V) = (2 : ZMod p) := by simpa [h0] using hβt
    rw [map_zero] at hz
    exact h2 hz.symm
  have ha0 : ha ≠ 0 := by
    intro h0
    have hz : αa (0 : V) = (2 : ZMod p) := by simpa [h0] using hαa
    rw [map_zero] at hz
    exact h2 hz.symm
  have h2ha : (2 : ZMod p) • ha = β ha • t := by
    have e1 : ra ha = ha - (2 : ZMod p) • ha := by rw [hra ha, hαa]
    have e2 : ra ha = ha - β ha • t := by rw [hrestr ha hH, hβ]
    have e : ha - (2 : ZMod p) • ha = ha - β ha • t := by rw [← e1, e2]
    simpa using e
  set c : ZMod p := β ha / 2 with hcdef
  have hha : ha = c • t := by
    calc ha = (1 : ZMod p) • ha := (one_smul _ _).symm
      _ = ((2 : ZMod p)⁻¹ * 2) • ha := by rw [inv_mul_cancel₀ h2]
      _ = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • ha) := by rw [smul_smul]
      _ = (2 : ZMod p)⁻¹ • (β ha • t) := by rw [h2ha]
      _ = ((2 : ZMod p)⁻¹ * β ha) • t := by rw [smul_smul]
      _ = c • t := by rw [hcdef, div_eq_mul_inv, mul_comm]
  set αa' : Module.Dual (ZMod p) V := c • αa with hαa'def
  have hβeq : ∀ v ∈ Submodule.span (ZMod p) (Set.range h), β v = c * αa v := by
    intro v hv
    have e1 : ra v = v - αa v • ha := hra v
    have e2 : ra v = v - β v • t := by rw [hrestr v hv, hβ]
    have e : v - αa v • ha = v - β v • t := by rw [← e1, e2]
    have e' : αa v • ha = β v • t := by simpa using e
    rw [hha, smul_smul] at e'
    have e5 : αa v * c = β v := (smul_left_injective (ZMod p) ht0) e'
    rw [← e5, mul_comm]
  have hαa't : αa' t = 2 := by
    have hbt : β t = c * αa t := hβeq t htH
    have hcα : c * αa t = 2 := by rw [← hbt, hβt]
    rw [hαa'def, LinearMap.smul_apply, smul_eq_mul]
    exact hcα
  have hra' : ∀ v, ra v = v - αa' v • t := by
    intro v
    calc ra v = v - αa v • ha := hra v
      _ = v - αa v • (c • t) := by rw [hha]
      _ = v - (αa v * c) • t := by rw [smul_smul]
      _ = v - αa' v • t := by
            rw [hαa'def, LinearMap.smul_apply, smul_eq_mul, mul_comm]
  let d : V → ZMod p := fun v => β v - αa' v
  set g : V ≃ₗ[ZMod p] V := ra * ρ (Equiv.swap a b) with hgdef
  have hdt : d t = 0 := by
    dsimp only [d]
    rw [hβt, hαa't, sub_self]
  have hg : ∀ w, g w = w + d w • t := by
    intro w
    have hlin : αa' (w - β w • t) = αa' w - (β w * 2) := by
      rw [map_sub, map_smul, hαa't]
      rfl
    calc g w = ra (ρ (Equiv.swap a b) w) := by rw [hgdef, LinearEquiv.mul_apply]
      _ = ra (w - β w • t) := by rw [hβ w]
      _ = (w - β w • t) - αa' (w - β w • t) • t := hra' _
      _ = w + d w • t := by
            rw [hlin]
            dsimp only [d]
            module
  have hgid : ∀ w, g (g w - w) = g w - w := by
    intro w
    have hgw : g w - w = d w • t := by
      rw [hg w]
      module
    rw [hgw, hg]
    have hz : d (d w • t) = 0 := by
      dsimp only [d]
      rw [map_smul, map_smul, hβt, hαa't]
      simp [smul_eq_mul]
    rw [hz, zero_smul, add_zero]
  have hle : ggLinMove g ≤ Submodule.span (ZMod p) ({t} : Set V) := by
    intro z hz
    rw [ggLinMove, LinearMap.mem_range] at hz
    obtain ⟨w, hw⟩ := hz
    have hzw : z = d w • t := by
      rw [← hw, LinearMap.sub_apply, LinearMap.id_apply]
      have hgw : g w - w = d w • t := by
        rw [hg w]
        module
      exact hgw
    rw [hzw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton t))
  have hfrle : Module.finrank (ZMod p) (ggLinMove g) ≤ 1 := by
    haveI hsp : Module.Finite (ZMod p) (Submodule.span (ZMod p) ({t} : Set V)) :=
      Module.Finite.span_singleton (ZMod p) t
    have h1 : Module.finrank (ZMod p) (ggLinMove g) ≤
        Module.finrank (ZMod p) (Submodule.span (ZMod p) ({t} : Set V)) :=
      Submodule.finrank_mono hle
    have h2' : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({t} : Set V)) = 1 :=
      finrank_span_singleton ht0
    omega
  have hgA : g ∈ Subgroup.closure (Set.range r ∪ {ra}) := by
    have hraA : ra ∈ Subgroup.closure (Set.range r ∪ {ra}) :=
      Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton ra))
    have hρA' : ρ (Equiv.swap a b) ∈ Subgroup.closure (Set.range r ∪ {ra}) :=
      Subgroup.closure_mono (Set.subset_union_left) (hρA (Equiv.swap a b))
    rw [hgdef]
    exact Subgroup.mul_mem _ hraA hρA'
  have hfrne : Module.finrank (ZMod p) (ggLinMove g) ≠ 1 := by
    intro h1
    exact hnt g hgA ⟨h1, hgid⟩
  have hfr0 : Module.finrank (ZMod p) (ggLinMove g) = 0 := by omega
  haveI hfing : Module.Finite (ZMod p) (ggLinMove g) := by
    haveI hsp : Module.Finite (ZMod p) (Submodule.span (ZMod p) ({t} : Set V)) :=
      Module.Finite.span_singleton (ZMod p) t
    exact Submodule.finiteDimensional_of_le hle
  have hbot : ggLinMove g = ⊥ := (Submodule.finrank_eq_zero (S := ggLinMove g)).mp hfr0
  have hg1 : g = 1 := by
    ext w
    have hmem : (g.toLinearMap - (LinearMap.id : V →ₗ[ZMod p] V)) w ∈ ggLinMove g := by
      rw [ggLinMove]
      exact ⟨w, rfl⟩
    rw [hbot] at hmem
    have hz : (g.toLinearMap - (LinearMap.id : V →ₗ[ZMod p] V)) w = 0 :=
      (Submodule.mem_bot (ZMod p)).mp hmem
    rw [LinearMap.sub_apply, LinearMap.id_apply] at hz
    have := sub_eq_zero.mp hz
    simpa using this
  have hrax : ra x = x := by
    have hgx : g x = x := by rw [hg1]; rfl
    rw [hgdef, LinearEquiv.mul_apply, hρx (Equiv.swap a b)] at hgx
    exact hgx
  have hz : αa x • ha = 0 := by
    have hx : x - αa x • ha = x := by rw [← hra x, hrax]
    exact sub_eq_self.mp hx
  rcases smul_eq_zero.mp hz with hsc | hv
  · exact hw hsc
  · exact ha0 hv


theorem ggDepA_caseII_false (hKG : GGReflClassLargeInput') {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (hN : 11 ≤ N) {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V}
    (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hcard : Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N))
    (hH : ha ∈ Submodule.span (ZMod p) (Set.range h)) : False := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨ρ, hρ, hρA, hρx, hρfaith⟩ := ggDepA_perm_embed hp (by omega) F r hr
  obtain ⟨AH, ψ, γ, hdim, hirr, hgen, hcardAH, hinj, hpsi, hγmem, hγval⟩ :=
    l05nDA2_data hp hN F r hr ra ha αa hra hαa hw hnt hcard
      (Submodule.span (ZMod p) (Set.range h)) rfl hH ρ hρA hρfaith
  have hsw : ∀ a b : Fin N, a ≠ b →
      GGLinRefl ((ψ (Equiv.swap a b) : ↥AH) :
        ↥(Submodule.span (ZMod p) (Set.range h)) ≃ₗ[ZMod p]
          ↥(Submodule.span (ZMod p) (Set.range h))) := by
    intro a b hab
    obtain ⟨t, β, htH, hβt, hβ⟩ := ggDepA_perm_swap_refl hp (by omega) F r hr ρ hρ hab
    rw [ggDepA_linRefl_iff hp2]
    refine ⟨⟨t, htH⟩, β.comp (Submodule.span (ZMod p) (Set.range h)).subtype, ?_, ?_⟩
    · simpa using hβt
    · intro v
      apply Subtype.ext
      rw [hpsi, hβ]
      rfl
  have hγrefl : GGLinRefl γ := by
    rw [ggDepA_linRefl_iff hp2]
    refine ⟨⟨ha, hH⟩, αa.comp (Submodule.span (ZMod p) (Set.range h)).subtype, ?_, ?_⟩
    · simpa using hαa
    · intro v
      apply Subtype.ext
      rw [hγval, hra]
      rfl
  obtain ⟨σ, hσswap, hσeq⟩ :=
    l05nDA2_classify hKG hp hN hdim AH hirr hgen hcardAH ψ hinj hsw γ hγmem hγrefl
  obtain ⟨a, b, hab, hσab⟩ := hσswap
  rw [hσab] at hσeq
  have hrestr : ∀ v ∈ Submodule.span (ZMod p) (Set.range h), ra v = ρ (Equiv.swap a b) v := by
    intro v hv
    let v' : ↥(Submodule.span (ZMod p) (Set.range h)) := ⟨v, hv⟩
    have h1 : ((((ψ (Equiv.swap a b) : ↥AH) :
        ↥(Submodule.span (ZMod p) (Set.range h)) ≃ₗ[ZMod p]
          ↥(Submodule.span (ZMod p) (Set.range h))) v' :
          ↥(Submodule.span (ZMod p) (Set.range h))) : V) = ρ (Equiv.swap a b) v :=
      hpsi (Equiv.swap a b) v'
    have h2 : ((((ψ (Equiv.swap a b) : ↥AH) :
        ↥(Submodule.span (ZMod p) (Set.range h)) ≃ₗ[ZMod p]
          ↥(Submodule.span (ZMod p) (Set.range h))) v' :
          ↥(Submodule.span (ZMod p) (Set.range h))) : V) = ra v := by
      rw [hσeq]
      simpa using hγval v'
    exact h2.symm.trans h1
  exact l05nDA2_end hp (by omega) F r hr ra ha αa hra hαa hw hH hnt ρ hρ hρA hρx hab hrestr


end CFSG.StandardType

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitBFin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitStruct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbKit
public import CFSG.LargeExtraspecial.O62Span

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LargeExtraspecial.O62
open CFSG.LargeExtraspecial.O62.Code
open Module CFSG.RankThree.OrthogonalInvolutions

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [-instance] Multiplicative.mul Multiplicative.semigroup Multiplicative.commSemigroup
attribute [-instance] Multiplicative.mulOneClass Multiplicative.monoid Multiplicative.commMonoid
attribute [-instance] Multiplicative.divInvMonoid Multiplicative.divisionMonoid
attribute [-instance] Multiplicative.divisionCommMonoid Multiplicative.group

@[expose] noncomputable def s16c1b_κ : (V₀ ≃ₗ[ZMod 2] V₀) →* MulAut (Multiplicative V₀) where
  toFun g := AddEquiv.toMultiplicative g.toAddEquiv
  map_one' := by ext x; rfl
  map_mul' g h := by ext x; rfl

theorem s16c1b_κ_apply (g : V₀ ≃ₗ[ZMod 2] V₀) (x : V₀) :
    s16c1b_κ g (Multiplicative.ofAdd x) = Multiplicative.ofAdd (g x) := rfl

theorem s16c1b_κ_injective : Function.Injective s16c1b_κ := by
  intro g h hgh
  apply LinearEquiv.ext
  intro x
  have := congrArg (fun φ : MulAut (Multiplicative V₀) =>
    Multiplicative.toAdd (φ (Multiplicative.ofAdd x))) hgh
  simpa [s16c1b_κ_apply] using this

@[expose] noncomputable def s16c1b_ΩM : Subgroup (MulAut (Multiplicative V₀)) :=
  (Ω₀ true).map s16c1b_κ

@[expose] noncomputable def s16c1b_S₀ : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) :=
  Subgroup.closure {g | ∃ w ∈ s16c1b_gens, g = wordProd w}

@[expose] noncomputable def s16c1b_SM : Subgroup (MulAut (Multiplicative V₀)) :=
  s16c1b_S₀.map s16c1b_κ

private theorem s16c1_finrank_V₀ : Module.finrank (ZMod 2) V₀ = 6 :=
  Module.finrank_fin_fun (ZMod 2)

private theorem s16c1_S0_length : s16c1b_S0.length = 64 := by decide +kernel

private theorem s16c1_S0_nodup : s16c1b_S0.Nodup := by decide +kernel

private theorem s16c1_S0_one_mem : Code.one ∈ s16c1b_S0 := by decide +kernel

private theorem s16c1_S0_closed :
    ∀ a ∈ s16c1b_S0, ∀ b ∈ s16c1b_S0, Code.mul a b ∈ s16c1b_S0 := by decide +kernel

private theorem s16c1_okWord_gens : ∀ w ∈ s16c1b_gens,
    (∀ n ∈ w, qB true n = true) ∧ Even w.length := by decide +kernel

private theorem s16c1_wordC_gens : ∀ w ∈ s16c1b_gens, wordC w ∈ s16c1b_S0 := by
  decide +kernel

private theorem s16c1_invC_gens : ∀ w ∈ s16c1b_gens, s16c1b_invC w ∈ s16c1b_S0 := by
  decide +kernel

private theorem s16c1_κ_inj_sub :
    Function.Injective (s16c1b_κ.comp (Ω₀ true).subtype) :=
  fun a b h => Subtype.ext (s16c1b_κ_injective h)

private theorem s16c1_gens_codes :
    ∀ g ∈ s16c1b_gens.map wordC, ∃ G ∈ s16c1b_S₀, Coded G g := by
  intro g hg
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hg
  exact ⟨wordProd w, Subgroup.subset_closure ⟨w, hw, rfl⟩, coded_wordProd w⟩

private theorem s16c1_inner {g : ℕ} (hg : ∃ G ∈ s16c1b_S₀, Coded G g) :
    ∀ (l : List ℕ), (∀ x ∈ l, ∃ G ∈ s16c1b_S₀, Coded G x) →
      ∀ {acc : List ℕ}, (∀ x ∈ acc, ∃ G ∈ s16c1b_S₀, Coded G x) →
        ∀ c ∈ l.foldl (fun acc' x =>
          if acc'.contains (Code.mul g x) then acc' else acc' ++ [Code.mul g x]) acc,
          ∃ G ∈ s16c1b_S₀, Coded G c := by
  intro l
  induction l with
  | nil =>
    intro _ acc hacc c hc
    exact hacc c (by simpa using hc)
  | cons x xs ih =>
    intro hl acc hacc c hc
    rw [List.foldl_cons] at hc
    refine ih (fun y hy => hl y (List.mem_cons_of_mem x hy)) ?_ c hc
    by_cases hcont : acc.contains (Code.mul g x)
    · rw [if_pos hcont]; exact hacc
    · rw [if_neg hcont]
      intro y hy
      rw [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact hacc y hy
      · obtain ⟨G, hG, hcG⟩ := hg
        obtain ⟨X, hX, hcX⟩ := hl x List.mem_cons_self
        exact ⟨G * X, s16c1b_S₀.mul_mem hG hX, hcG.mul hcX⟩

private theorem s16c1_foldl_gens :
    ∀ (gens : List ℕ), (∀ g ∈ gens, ∃ G ∈ s16c1b_S₀, Coded G g) →
      ∀ (l : List ℕ), (∀ x ∈ l, ∃ G ∈ s16c1b_S₀, Coded G x) →
        ∀ {acc : List ℕ}, (∀ x ∈ acc, ∃ G ∈ s16c1b_S₀, Coded G x) →
          ∀ c ∈ gens.foldl (fun acc g => l.foldl (fun acc' x =>
            if acc'.contains (Code.mul g x) then acc' else acc' ++ [Code.mul g x]) acc) acc,
            ∃ G ∈ s16c1b_S₀, Coded G c := by
  intro gens
  induction gens with
  | nil =>
    intro _ l _ acc hacc c hc
    exact hacc c (by simpa using hc)
  | cons g gs ih =>
    intro hgens l hl acc hacc c hc
    rw [List.foldl_cons] at hc
    refine ih (fun y hy => hgens y (List.mem_cons_of_mem g hy)) l hl ?_ c hc
    exact s16c1_inner (hgens g List.mem_cons_self) l hl hacc

private theorem s16c1_step_subset_codes {l : List ℕ}
    (hl : ∀ x ∈ l, ∃ G ∈ s16c1b_S₀, Coded G x) :
    ∀ c ∈ s16c1b_step (s16c1b_gens.map wordC) l, ∃ G ∈ s16c1b_S₀, Coded G c := by
  unfold s16c1b_step
  exact s16c1_foldl_gens (s16c1b_gens.map wordC) s16c1_gens_codes l hl (fun x hx => hl x hx)

private theorem s16c1_iter_subset_codes (n : ℕ) :
    ∀ {l : List ℕ}, (∀ x ∈ l, ∃ G ∈ s16c1b_S₀, Coded G x) →
      ∀ c ∈ s16c1b_iter (s16c1b_gens.map wordC) n l, ∃ G ∈ s16c1b_S₀, Coded G c := by
  induction n with
  | zero => intro l hl c hc; exact hl c hc
  | succ n ih =>
    intro l hl c hc
    exact ih (s16c1_step_subset_codes hl) c hc

theorem s16c1b_S₀_spec :
    s16c1b_S₀ ≤ Ω₀ true ∧ Nat.card s16c1b_S₀ = 64 ∧
      (∀ g ∈ s16c1b_S₀, ∃ c ∈ s16c1b_S0, Coded g c) ∧
        (∀ c ∈ s16c1b_S0, ∃ g ∈ s16c1b_S₀, Coded g c) := by
  have hle : s16c1b_S₀ ≤ Ω₀ true := by
    rw [s16c1b_S₀, Subgroup.closure_le]
    rintro g ⟨w, hw, rfl⟩
    obtain ⟨hq, hev⟩ := s16c1_okWord_gens w hw
    exact (wordProd_mem_omegaGroup_iff hq).mpr hev
  have hc : ∀ g ∈ s16c1b_S₀, ∃ c ∈ s16c1b_S0, Coded g c := by
    intro g hg
    induction hg using Subgroup.closure_induction'' with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨wordC w, s16c1_wordC_gens w hw, coded_wordProd w⟩
    | inv_mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      refine ⟨s16c1b_invC w, s16c1_invC_gens w hw, ?_⟩
      rw [wordProd_inv]
      exact coded_wordProd w.reverse
    | one => exact ⟨Code.one, s16c1_S0_one_mem, coded_one⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨a, ha, hxa⟩ := ihx
      obtain ⟨b, hb, hxb⟩ := ihy
      exact ⟨Code.mul a b, s16c1_S0_closed a ha b hb, hxa.mul hxb⟩
  have hd : ∀ c ∈ s16c1b_S0, ∃ g ∈ s16c1b_S₀, Coded g c :=
    s16c1_iter_subset_codes 6 (l := [Code.one]) (fun x hx => by
      rw [List.mem_singleton] at hx
      exact ⟨1, one_mem s16c1b_S₀, by rw [hx]; exact coded_one⟩)
  have hcard : Nat.card s16c1b_S₀ = 64 := by
    have hcl : Nat.card {c // c ∈ s16c1b_S0} = 64 := by
      change Nat.card ({c | c ∈ s16c1b_S0} : Set ℕ) = 64
      rw [Nat.card_coe_set_eq, ← List.coe_toFinset, Set.ncard_coe_finset,
        List.toFinset_card_of_nodup s16c1_S0_nodup, s16c1_S0_length]
    have e : s16c1b_S₀ ≃ {c // c ∈ s16c1b_S0} :=
      { toFun := fun g => ⟨Classical.choose (hc g.1 g.2),
            (Classical.choose_spec (hc g.1 g.2)).1⟩
        invFun := fun c => ⟨Classical.choose (hd c.1 c.2),
          (Classical.choose_spec (hd c.1 c.2)).1⟩
        left_inv := by
          intro g
          have hg := Classical.choose_spec (hc g.1 g.2)
          have hg' := Classical.choose_spec (hd (Classical.choose (hc g.1 g.2))
            (Classical.choose_spec (hc g.1 g.2)).1)
          exact Subtype.ext ((hg'.2.eq_iff hg.2).mpr rfl)
        right_inv := by
          intro c
          have hc' := Classical.choose_spec (hd c.1 c.2)
          have hc'' := Classical.choose_spec (hc (Classical.choose (hd c.1 c.2)) hc'.1)
          exact Subtype.ext ((hc''.2.eq_iff hc'.2).mp rfl) }
    rw [Nat.card_congr e, hcl]
  exact ⟨hle, hcard, hc, hd⟩

theorem s16c1b_S₀_sylow : IsSylowIn 2 s16c1b_S₀ (Ω₀ true) := by
  refine ⟨s16c1b_S₀_spec.1, IsPGroup.of_card (n := 6) (by
    rw [s16c1b_S₀_spec.2.1]; norm_num), ?_⟩
  intro hdvd
  have h1 := Subgroup.relIndex_mul_card (H := s16c1b_S₀) (K := Ω₀ true)
  rw [inf_eq_left.2 s16c1b_S₀_spec.1, s16c1b_S₀_spec.2.1, s16c1_card_omega0] at h1
  have hrel : s16c1b_S₀.relIndex (Ω₀ true) = 405 := by omega
  rw [hrel] at hdvd
  norm_num at hdvd

private theorem s16c1_exists_conj_of_isSylowIn {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {S S' H : Subgroup G} (hS : IsSylowIn p S H) (hS' : IsSylowIn p S' H) :
    ∃ h ∈ H, S' = S.map (MulAut.conj h).toMonoidHom := by
  have hmem : ∃ h ∈ H, ∀ x : G, x ∈ S' ↔ h⁻¹ * x * h ∈ S := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) hS.toSylow hS'.toSylow
    have hg' : (hS.toSylow : Subgroup H).map (MulAut.conj g).toMonoidHom =
        (hS'.toSylow : Subgroup H) := by
      have h1 : ((g • hS.toSylow : Sylow p H) : Subgroup H) = (hS'.toSylow : Subgroup H) := by
        rw [hg]
      rwa [Sylow.coe_subgroup_smul] at h1
    refine ⟨g, g.2, fun x => ?_⟩
    constructor
    · intro hx
      have hxH : x ∈ H := hS'.le hx
      have hx' : (⟨x, hxH⟩ : H) ∈ (hS'.toSylow : Subgroup H) := hx
      rw [← hg', Subgroup.mem_map] at hx'
      obtain ⟨s, hs, hsx⟩ := hx'
      have h3 : (g : G)⁻¹ * x * g = (s : G) := by
        have h2 : ((MulAut.conj g s : H) : G) = x := congrArg Subtype.val hsx
        simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
        rw [← h2]; group
      rw [h3]
      exact hs
    · intro hx
      have hxH : (g : G)⁻¹ * x * g ∈ H := hS.le hx
      have hxH' : x ∈ H := by
        have := H.mul_mem (H.mul_mem g.2 hxH) (H.inv_mem g.2)
        simpa [mul_assoc] using this
      have hx' : (⟨x, hxH'⟩ : H) ∈ (hS'.toSylow : Subgroup H) := by
        rw [← hg', Subgroup.mem_map]
        refine ⟨⟨(g : G)⁻¹ * x * g, hxH⟩, hx, ?_⟩
        show (MulAut.conj g) ⟨(g : G)⁻¹ * x * g, hxH⟩ = (⟨x, hxH'⟩ : H)
        rw [MulAut.conj_apply]
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      exact hx'
  obtain ⟨h, hH, heq⟩ := hmem
  refine ⟨h, hH, ?_⟩
  ext x
  rw [heq x, Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨h⁻¹ * x * h, hx, ?_⟩
    change (MulAut.conj h) (h⁻¹ * x * h) = x
    rw [MulAut.conj_apply]
    group
  · rintro ⟨s, hs, rfl⟩
    change h⁻¹ * (MulAut.conj h) s * h ∈ S
    have : h⁻¹ * (MulAut.conj h) s * h = s := by
      rw [MulAut.conj_apply]; group
    rw [this]
    exact hs

private theorem s16c1_isSylowIn_map_of_injective {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] {p : ℕ} [Fact p.Prime] {A B : Subgroup G}
    (h : IsSylowIn p A B) {f : G →* H} (hf : Function.Injective f) :
    IsSylowIn p (A.map f) (B.map f) := by
  refine isSylowIn_of_card_eq (Subgroup.map_mono h.le) ?_
  rw [Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hf, h.card_eq]

theorem s16c1b_sylow_conj {S : Subgroup (MulAut (Multiplicative V₀))}
    (hS : IsSylowIn 2 S s16c1b_ΩM) :
    ∃ h ∈ s16c1b_ΩM, S = s16c1b_SM.map (MulAut.conj h).toMonoidHom := by
  haveI : Finite (V₀ ≃ₗ[ZMod 2] V₀) :=
    Finite.of_injective (fun f : V₀ ≃ₗ[ZMod 2] V₀ => (f : V₀ → V₀))
      (fun f g h => LinearEquiv.ext (congrFun h))
  haveI : Finite (MulAut (Multiplicative V₀)) :=
    Finite.of_injective
      (fun f : MulAut (Multiplicative V₀) => (f : Multiplicative V₀ → Multiplicative V₀))
      (fun f g h => MulEquiv.ext (congrFun h))
  have hSM : IsSylowIn 2 s16c1b_SM s16c1b_ΩM := by
    simpa [s16c1b_SM, s16c1b_ΩM] using
      s16c1_isSylowIn_map_of_injective s16c1b_S₀_sylow s16c1b_κ_injective
  exact s16c1_exists_conj_of_isSylowIn hSM hS

private theorem s16c1_ptCent_eq_map (w : Multiplicative V₀) :
    ptCent s16c1b_ΩM w =
      (MulAction.stabilizer (Ω₀ true) (Multiplicative.toAdd w)).map
        (s16c1b_κ.comp (Ω₀ true).subtype) := by
  ext φ
  constructor
  · intro hφ
    have hφM : φ ∈ s16c1b_ΩM := (Subgroup.mem_inf.mp hφ).1
    have hφw : φ ∈ MulAction.stabilizer (MulAut (Multiplicative V₀)) w :=
      (Subgroup.mem_inf.mp hφ).2
    obtain ⟨g, hg, hgφ⟩ : ∃ g ∈ Ω₀ true, s16c1b_κ g = φ := hφM
    refine ⟨⟨g, hg⟩, ?_, ?_⟩
    · change g (Multiplicative.toAdd w) = Multiplicative.toAdd w
      have h2 : s16c1b_κ g (Multiplicative.ofAdd (Multiplicative.toAdd w)) =
          Multiplicative.ofAdd (Multiplicative.toAdd w) := by
        rw [hgφ]
        exact (MulAction.mem_stabilizer_iff.mp hφw)
      rw [s16c1b_κ_apply] at h2
      exact Multiplicative.ofAdd.injective h2
    · simpa using hgφ
  · intro hφ
    obtain ⟨g, hg, hgφ⟩ :
        ∃ g ∈ MulAction.stabilizer (Ω₀ true) (Multiplicative.toAdd w),
          (s16c1b_κ.comp (Ω₀ true).subtype) g = φ := hφ
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · show φ ∈ map s16c1b_κ (Ω₀ true)
      exact ⟨g.1, g.2, hgφ⟩
    · change φ • w = w
      rw [← hgφ]
      change Multiplicative.ofAdd (g.1 (Multiplicative.toAdd w)) = w
      have hg' : g.1 (Multiplicative.toAdd w) = Multiplicative.toAdd w :=
        MulAction.mem_stabilizer_iff.mp hg
      rw [hg']
      exact ofAdd_toAdd w

theorem s16c1b_card_ptCent_eq_960_iff {w : Multiplicative V₀} (hw : w ≠ 1) :
    Nat.card (ptCent s16c1b_ΩM w) = 960 ↔ qModel true (Multiplicative.toAdd w) = 0 := by
  have hV : Module.finrank (ZMod 2) V₀ = 6 := s16c1_finrank_V₀
  have h5 : 5 ≤ Module.finrank (ZMod 2) V₀ := by rw [hV]; norm_num
  have hz0 : Multiplicative.toAdd w ≠ 0 := fun h => hw (toAdd_eq_zero.mp h)
  have hcard_eq : Nat.card (ptCent s16c1b_ΩM w) =
      Nat.card {g : ↥(Ω₀ true) //
        (g : V₀ ≃ₗ[ZMod 2] V₀) (Multiplicative.toAdd w) = Multiplicative.toAdd w} := by
    rw [s16c1_ptCent_eq_map w, Subgroup.card_map_of_injective s16c1_κ_inj_sub]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    rw [MulAction.mem_stabilizer_iff]
    rfl
  rcases zmod2_eq_zero_or_eq_one (qModel true (Multiplicative.toAdd w)) with hq | hq
  · rw [hcard_eq]
    have horb : MulAction.orbit (Ω₀ true) (Multiplicative.toAdd w) =
        {v : V₀ | v ≠ 0 ∧ qModel true v = 0} := by
      ext v
      rw [MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨fun h => hz0 ((LinearEquiv.map_eq_zero_iff (x : V₀ ≃ₗ[ZMod 2] V₀)).mp h),
          (TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
            (omegaGroup_le (qModel true) (qModel_nondegenerate true) x.2)
            (Multiplicative.toAdd w)).trans hq⟩
      · rintro ⟨hv0, hv⟩
        obtain ⟨x, hx, hxz⟩ := exists_mem_omegaGroup_apply_eq (V := V₀) (Q := qModel true)
          (qModel_nondegenerate true) h5 hz0 hv0 (hq.trans hv.symm)
        exact ⟨⟨x, hx⟩, hxz⟩
    have h27 : Nat.card (MulAction.orbit (Ω₀ true) (Multiplicative.toAdd w)) = 27 := by
      rw [horb, Nat.card_coe_set_eq]
      rcases ncard_singular_nonsingular (V := V₀) (Q := qModel true) hV
        (qModel_nondegenerate true) with h | h
      · exfalso
        have h2 := h.2
        rw [qModel_true] at h2
        rw [ncard_qMinus] at h2
        omega
      · exact h.1
    have hstab : Nat.card (MulAction.stabilizer (Ω₀ true) (Multiplicative.toAdd w)) = 960 := by
      have key : Nat.card (MulAction.orbit (Ω₀ true) (Multiplicative.toAdd w)) *
          Nat.card (MulAction.stabilizer (Ω₀ true) (Multiplicative.toAdd w)) =
          Nat.card ↥(Ω₀ true) := by
        rw [← Nat.card_prod]
        exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Ω₀ true)
          (Multiplicative.toAdd w))
      rw [h27, s16c1_card_omega0] at key
      omega
    have hsub : Nat.card {g : ↥(Ω₀ true) //
        (g : V₀ ≃ₗ[ZMod 2] V₀) (Multiplicative.toAdd w) = Multiplicative.toAdd w} =
        Nat.card (MulAction.stabilizer (Ω₀ true) (Multiplicative.toAdd w)) := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
      rw [MulAction.mem_stabilizer_iff]
      rfl
    rw [hsub, hstab, hq]
    simp
  · rw [hcard_eq, s16c1_omega0_card_stab_nonsing hq]
    constructor
    · intro h; exact absurd h (by norm_num)
    · intro h; exact absurd (hq.symm.trans h) one_ne_zero

theorem s16c1b_singTrans_model : OmegaSingTrans s16c1b_ΩM := by
  intro w w' hw hw' hc hc'
  have hq : qModel true (Multiplicative.toAdd w) = 0 :=
    (s16c1b_card_ptCent_eq_960_iff hw).mp hc
  have hq' : qModel true (Multiplicative.toAdd w') = 0 :=
    (s16c1b_card_ptCent_eq_960_iff hw').mp hc'
  have hz0 : Multiplicative.toAdd w ≠ 0 := fun h => hw (toAdd_eq_zero.mp h)
  have hz0' : Multiplicative.toAdd w' ≠ 0 := fun h => hw' (toAdd_eq_zero.mp h)
  obtain ⟨g, hg, hgz⟩ := s16c1_omega0_exists_conj hz0 hq
  obtain ⟨g', hg', hg'z⟩ := s16c1_omega0_exists_conj hz0' hq'
  refine ⟨s16c1b_κ (g' * g⁻¹), ?_, ?_⟩
  · exact Subgroup.mem_map.mpr
      ⟨g' * g⁻¹, (Ω₀ true).mul_mem hg' ((Ω₀ true).inv_mem hg), rfl⟩
  · have hg1 : g⁻¹ (Multiplicative.toAdd w) = vec 1 := by
      rw [← hgz]; simp
    change Multiplicative.ofAdd ((g' * g⁻¹) (Multiplicative.toAdd w)) = w'
    rw [LinearEquiv.mul_apply, hg1, hg'z]
    exact ofAdd_toAdd w'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

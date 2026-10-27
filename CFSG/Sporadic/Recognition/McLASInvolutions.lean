module

public import CFSG.Sporadic.Recognition.McLASSpec
public import CFSG.Sporadic.SmallOddCore.McLAut
public import CFSG.Sporadic.SmallOddCore.McLLocal
public import CFSG.Sporadic.Mathieu.M11

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint

noncomputable abbrev outerS : Equiv.Perm (Fin 275) := tp 275 outerTab

theorem tabRep_m11TabA : TabRep m11TabA Mathieu.m11gA := by
  refine ⟨rfl, fun i => ?_⟩
  fin_cases i <;> decide

theorem tabRep_m11TabB : TabRep m11TabB Mathieu.m11gB := by
  refine ⟨rfl, fun i => ?_⟩
  fin_cases i <;> decide

theorem pointsList_m11Pts : PointsList 275 11 m11Pts := ⟨rfl, by decide, by decide⟩

theorem perm_fix_of_comm {α : Type*} {g s : Equiv.Perm α} {x : α} (h : g * s = s * g)
    (hx : s x = x) : s (g x) = g x := by
  have h1 : g (s x) = s (g x) := Equiv.Perm.ext_iff.1 h x
  rw [hx] at h1
  exact h1.symm

theorem nonempty_mulEquiv_m11
    (h : m11Check = true) :
    Nonempty (↥(mclP ⊓ centralizer ({outerS} : Set (Equiv.Perm (Fin 275)))) ≃*
      ↥NativeSporadic.M11) := by
  simp only [m11Check, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have hsrep : CFSG.Monster.B.Co2.Rep 275 (natArr outerTab) outerS :=
    co2Rep_natArr_iff.2 (rep_tp h1)
  have hgrep : ∀ k < 4, CFSG.Monster.B.Co2.Rep 275 (natArr (mclCentTbl (k + 18)))
      (tp 275 (mclCentTbl (k + 18))) := fun k hk => co2Rep_natArr_iff.2 (rep_tp (h2 k hk))
  obtain ⟨-, -, -, hrows, -⟩ := mcl_involution_centralizers
  obtain ⟨-, -, -, hC, hcard, -⟩ := hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)
  dsimp only [SmallOddCore.mclC] at hC hcard
  have hC' : Subgroup.closure (tp 275 '' {x | x ∈ #[mclCentTbl 18, mclCentTbl 19, mclCentTbl 20,
      mclCentTbl 21]}) = mclP ⊓ centralizer ({outerS} : Set (Equiv.Perm (Fin 275))) := hC
  have hcardC : Nat.card ↥(mclP ⊓ centralizer ({outerS} : Set (Equiv.Perm (Fin 275)))) = 7920 :=
    hcard
  set C : Subgroup (Equiv.Perm (Fin 275)) := mclP ⊓ centralizer ({outerS} : Set _) with hCdef
  have hfix : ∀ x : Fin 275, (x : ℕ) ∈ m11Pts ↔ outerS x = x := by
    intro x
    have h := h6 x x.2
    rw [hsrep x] at h
    constructor
    · intro hx
      have h' : (((outerS x : Fin 275) : ℕ) == (x : ℕ)) = true := by
        rw [← h]; exact decide_eq_true hx
      exact Fin.ext (beq_iff_eq.1 h')
    · intro hx
      have h' : (((outerS x : Fin 275) : ℕ) == (x : ℕ)) = true := by
        rw [hx]; exact beq_self_eq_true _
      rw [← h] at h'
      exact of_decide_eq_true h'
  have hL : PointsList 275 11 m11Pts := ⟨h3, h5, h4⟩
  have hpres : ∀ g ∈ C, ∀ x : Fin 275, (x : ℕ) ∈ m11Pts → (g x : ℕ) ∈ m11Pts := by
    intro g hg x hx
    have hcomm : g * outerS = outerS * g :=
      mem_centralizer_singleton_iff.1 (mem_inf.1 hg).2
    have hsx : outerS x = x := (hfix x).1 hx
    have : outerS (g x) = g x := perm_fix_of_comm hcomm hsx
    exact (hfix (g x)).2 this
  have hgenmem : ∀ k < 4, tp 275 (mclCentTbl (k + 18)) ∈ C := by
    intro k hk
    rw [← hC']
    refine subset_closure ⟨mclCentTbl (k + 18), ?_, rfl⟩
    interval_cases k <;> simp
  let gcl : ℕ → C := fun k =>
    if hk : k < 4 then ⟨tp 275 (mclCentTbl (k + 18)), hgenmem k hk⟩ else 1
  let ρ : C →* Equiv.Perm (Fin 11) := hL.restrHom C hpres
  have hsz : m11Rest.size = 4 := by simp [m11Rest, m11Gens]
  have hrep : ∀ k < m11Rest.size, TabRep m11Rest[k]! (ρ (gcl k)) := by
    intro k hk
    have hk4 : k < 4 := by rw [hsz] at hk; exact hk
    have e : m11Rest[k]! = restrictArr m11Pts (natArr (mclCentTbl (k + 18))) := by
      rw [m11Rest, getElem!_map_eq _ _ (by simpa [m11Gens] using hk4), m11Gens,
        getElem!_pos _ k (by simpa using hk4), Array.getElem_ofFn]
    rw [e]
    have hg : (gcl k : Equiv.Perm (Fin 275)) = tp 275 (mclCentTbl (k + 18)) := by
      simp only [gcl, hk4, dite_true]
    exact hL.tabRep_restrHom C hpres (gcl k) (by rw [hg]; exact hgrep k hk4)
  have hword : ∀ w : List ℕ, (∀ j ∈ w, j < m11Rest.size) →
      TabRep (wordTabS 11 m11Rest w) (ρ ((w.map gcl).prod)) := by
    intro w hw
    have := tabRep_wordTabS (f := fun j => ρ (gcl j)) hrep w hw
    rw [map_list_prod ρ, List.map_map]
    exact this
  have hwA := hword m11WordA (by
    intro j hj
    simp only [m11WordA, List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [hsz]; omega)
  have hwB := hword m11WordB (by
    intro j hj
    simp only [m11WordB, List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [hsz]; omega)
  have hρA : ρ ((m11WordA.map gcl).prod) = Mathieu.m11gA :=
    (hwA.eq_iff tabRep_m11TabA).1 (by rw [h7])
  have hρB : ρ ((m11WordB.map gcl).prod) = Mathieu.m11gB :=
    (hwB.eq_iff tabRep_m11TabB).1 (by rw [h8])
  have hMle : NativeSporadic.M11 ≤ ρ.range := by
    rw [Mathieu.m11_eq, closure_le]
    rintro g (rfl | rfl)
    · exact ⟨_, hρA⟩
    · exact ⟨_, hρB⟩
  have hrange_le : Nat.card ρ.range ≤ Nat.card C :=
    Nat.card_le_card_of_surjective _ ρ.rangeRestrict_surjective
  have hrange_eq : NativeSporadic.M11 = ρ.range :=
    eq_of_le_of_card_ge hMle (by rw [Mathieu.card_M11, ← hcardC]; exact hrange_le)
  have hbij : Function.Bijective ρ.rangeRestrict := by
    rw [Nat.bijective_iff_surjective_and_card]
    refine ⟨ρ.rangeRestrict_surjective, ?_⟩
    rw [← hrange_eq, Mathieu.card_M11, hcardC]
  exact ⟨((MulEquiv.ofBijective ρ.rangeRestrict hbij).trans
    (MulEquiv.subgroupCongr hrange_eq.symm))⟩

theorem outer_involution_facts :
    outerS ∈ mclR ∧ orderOf outerS = 2 ∧ outerS ∉ mclP ∧
      ∀ s ∈ mclR, s ∉ mclP → orderOf s = 2 → ∃ g ∈ mclP, s = g * outerS * g⁻¹ := by
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ := mcl_involution_centralizers
  obtain ⟨-, -, h0out, -⟩ := hrows _ List.mem_cons_self
  obtain ⟨h1r, h1o, h1out, -⟩ := hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)
  dsimp only at h0out h1r h1o h1out
  have h0P : tp 275 (mclCentTbl 4) ∈ mclP := by
    by_contra h
    exact Bool.false_ne_true (h0out.2 h)
  have h1P : tp 275 (mclCentTbl 17) ∉ mclP := h1out.1 rfl
  refine ⟨h1r, h1o, h1P, fun s hs hsP hs2 => ?_⟩
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover s hs hs2
  have key : ∀ x : Equiv.Perm (Fin 275), g * x * g⁻¹ ∈ mclP → x ∈ mclP := fun x hx => by
    have := mclP.mul_mem (mclP.mul_mem (mclP.inv_mem hg) hx) hg
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
  simp only [mclRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · dsimp only at hsP
    exact absurd (mclP.mul_mem (mclP.mul_mem hg h0P) (mclP.inv_mem hg)) hsP
  · dsimp only
    exact ⟨g, hg, rfl⟩

theorem nonempty_mulEquiv_m11_of_outer
    (h : m11Check = true)
    {s : Equiv.Perm (Fin 275)} (hs : s ∈ mclR) (hsP : s ∉ mclP) (hs2 : orderOf s = 2) :
    Nonempty (↥(mclP ⊓ centralizer ({s} : Set (Equiv.Perm (Fin 275)))) ≃* ↥NativeSporadic.M11) := by
  obtain ⟨-, -, -, hall⟩ := outer_involution_facts
  obtain ⟨g, hg, rfl⟩ := hall s hs hsP hs2
  obtain ⟨e⟩ := nonempty_mulEquiv_m11 h
  rw [inf_centralizer_conj mclP hg outerS]
  exact ⟨((mclP ⊓ centralizer ({outerS} : Set (Equiv.Perm (Fin 275)))).equivMapOfInjective _
    (MulAut.conj g).injective).symm.trans e⟩

@[expose] def fixedSubgroup {G : Type*} [Group G] (σ : MulAut G) : Subgroup G where
  carrier := {g | σ g = g}
  one_mem' := map_one σ
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [map_inv, ha]

theorem mem_fixedSubgroup {G : Type*} [Group G] {σ : MulAut G} {g : G} :
    g ∈ fixedSubgroup σ ↔ σ g = g := Iff.rfl

theorem aut_transport {n : ℕ} {T : Type*} [Group T] {P R : Subgroup (Equiv.Perm (Fin n))}
    (hPR : P ≤ R) (e₀ : T ≃* P) (ψ : R ≃* MulAut P)
    (hψ : ∀ (x : R) (p : P), ((ψ x p : P) : Equiv.Perm (Fin n)) =
      (x : Equiv.Perm (Fin n)) * (p : Equiv.Perm (Fin n)) * (x : Equiv.Perm (Fin n))⁻¹)
    (hinner : (P.subgroupOf R).map ψ.toMonoidHom = inner P) :
    ∃ Φ : MulAut T ≃* R,
      (∀ (σ : MulAut T) (g : T), ((e₀ (σ g) : P) : Equiv.Perm (Fin n)) =
        (Φ σ : Equiv.Perm (Fin n)) * ((e₀ g : P) : Equiv.Perm (Fin n)) *
          (Φ σ : Equiv.Perm (Fin n))⁻¹) ∧
      (∀ σ : MulAut T, σ ∈ inner T ↔ ((Φ σ : R) : Equiv.Perm (Fin n)) ∈ P) ∧
      ∀ c : T, ((Φ (MulAut.conj c) : R) : Equiv.Perm (Fin n)) =
        ((e₀ c : P) : Equiv.Perm (Fin n)) := by
  let Φ : MulAut T ≃* R := (MulAut.congr e₀).trans ψ.symm
  have hΦ : ∀ σ : MulAut T, ψ (Φ σ) = MulAut.congr e₀ σ := fun σ => by
    simp [Φ]
  refine ⟨Φ, fun σ g => ?_, fun σ => ?_, fun c => ?_⟩
  · have h1 := hψ (Φ σ) (e₀ g)
    rw [hΦ σ] at h1
    rw [← h1]
    simp [MulAut.congr_apply]
  · have h1 : σ ∈ inner T ↔ MulAut.congr e₀ σ ∈ inner P := by
      rw [← inner_map_congr e₀]
      constructor
      · exact fun h => ⟨σ, h, rfl⟩
      · rintro ⟨τ, hτ, hτσ⟩
        have : τ = σ := (MulAut.congr e₀).injective hτσ
        rwa [this] at hτ
    rw [h1, ← hΦ σ, ← hinner]
    constructor
    · rintro ⟨x, hx, hxy⟩
      have : x = Φ σ := ψ.injective hxy
      rw [← this]
      exact hx
    · intro h
      exact ⟨Φ σ, h, rfl⟩
  · have hx : (⟨((e₀ c : P) : Equiv.Perm (Fin n)), hPR (e₀ c).2⟩ : R) = Φ (MulAut.conj c) := by
      apply ψ.injective
      rw [hΦ]
      ext p
      rw [hψ]
      simp [MulAut.congr_apply]
    rw [← hx]

noncomputable def fixedEquiv {n : ℕ} {T : Type*} [Group T] {P : Subgroup (Equiv.Perm (Fin n))}
    (e₀ : T ≃* P) (σ : MulAut T) (x : Equiv.Perm (Fin n))
    (hx : ∀ g : T, ((e₀ (σ g) : P) : Equiv.Perm (Fin n)) =
      x * ((e₀ g : P) : Equiv.Perm (Fin n)) * x⁻¹) :
    ↥(fixedSubgroup σ) ≃* ↥(P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin n)))) := by
  let ι : T →* Equiv.Perm (Fin n) := P.subtype.comp e₀.toMonoidHom
  have hmem : ∀ g : fixedSubgroup σ, ι g ∈ P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin n))) := by
    intro g
    refine mem_inf.2 ⟨(e₀ g).2, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := hx g
    rw [mem_fixedSubgroup.1 g.2] at h1
    have h2 : ((e₀ g : P) : Equiv.Perm (Fin n)) * x = x * ((e₀ g : P) : Equiv.Perm (Fin n)) := by
      calc ((e₀ g : P) : Equiv.Perm (Fin n)) * x
          = (x * ((e₀ g : P) : Equiv.Perm (Fin n)) * x⁻¹) * x := by rw [← h1]
        _ = x * ((e₀ g : P) : Equiv.Perm (Fin n)) := by group
    exact h2
  let f : ↥(fixedSubgroup σ) →* ↥(P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin n)))) :=
    (ι.comp (fixedSubgroup σ).subtype).codRestrict _ hmem
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    have h1 : ((f a : ↥(P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin n))))) :
        Equiv.Perm (Fin n)) = ((f b : ↥(P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin n))))) :
        Equiv.Perm (Fin n)) := by rw [hab]
    exact Subtype.ext (e₀.injective (Subtype.ext h1))
  · rintro ⟨π, hπ⟩
    obtain ⟨hπP, hπc⟩ := mem_inf.1 hπ
    have hc : π * x = x * π := mem_centralizer_singleton_iff.1 hπc
    refine ⟨⟨e₀.symm ⟨π, hπP⟩, ?_⟩, ?_⟩
    · rw [mem_fixedSubgroup]
      apply e₀.injective
      apply Subtype.ext
      rw [hx]
      simp only [MulEquiv.apply_symm_apply]
      calc x * π * x⁻¹ = (π * x) * x⁻¹ := by rw [hc]
        _ = π := by group
    · apply Subtype.ext
      simp [f, ι]

abbrev mclConj : NativeSporadic.McL →* MulAut NativeSporadic.McL :=
  @MulAut.conj NativeSporadic.McL inferInstance

theorem exists_aut_model :
    ∃ Φ : MulAut NativeSporadic.McL ≃* mclR,
      (∀ (σ : MulAut NativeSporadic.McL) (g : NativeSporadic.McL),
        ((mclPermEquiv (σ g) : mclP) : Equiv.Perm (Fin 275)) =
          (Φ σ : Equiv.Perm (Fin 275)) * ((mclPermEquiv g : mclP) : Equiv.Perm (Fin 275)) *
            (Φ σ : Equiv.Perm (Fin 275))⁻¹) ∧
      (∀ σ : MulAut NativeSporadic.McL,
        σ ∈ inner NativeSporadic.McL ↔ ((Φ σ : mclR) : Equiv.Perm (Fin 275)) ∈ mclP) ∧
      ∀ c : NativeSporadic.McL,
        ((Φ (mclConj c) : mclR) : Equiv.Perm (Fin 275)) =
          ((mclPermEquiv c : mclP) : Equiv.Perm (Fin 275)) := by
  obtain ⟨ψ, hψ, hinner, -⟩ := mcl_full_automorphism_model
  have hPR : mclP ≤ mclR := le_sup_left
  exact @aut_transport 275 NativeSporadic.McL inferInstance mclP mclR hPR mclPermEquiv ψ hψ hinner

abbrev mclFixed (σ : MulAut NativeSporadic.McL) : Subgroup NativeSporadic.McL :=
  @fixedSubgroup NativeSporadic.McL inferInstance σ

theorem mcl_outer_involutions
    (h : m11Check = true) :
    (∃ σ : MulAut NativeSporadic.McL, orderOf σ = 2 ∧ σ ∉ inner NativeSporadic.McL) ∧
    (∀ σ τ : MulAut NativeSporadic.McL, orderOf σ = 2 → σ ∉ inner NativeSporadic.McL →
      orderOf τ = 2 → τ ∉ inner NativeSporadic.McL →
        ∃ g : NativeSporadic.McL, mclConj g * σ * (mclConj g)⁻¹ = τ) ∧
    (∀ σ : MulAut NativeSporadic.McL, orderOf σ = 2 → σ ∉ inner NativeSporadic.McL →
      Nonempty (↥(mclFixed σ) ≃* ↥NativeSporadic.M11)) := by
  obtain ⟨Φ, hΦ1, hΦ2, hΦ3⟩ := exists_aut_model
  obtain ⟨hSR, hS2, hSP, hall⟩ := outer_involution_facts
  have hord : ∀ σ : MulAut NativeSporadic.McL,
      orderOf ((Φ σ : mclR) : Equiv.Perm (Fin 275)) = orderOf σ := fun σ => by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  refine ⟨⟨Φ.symm ⟨outerS, hSR⟩, ?_, ?_⟩, ?_, ?_⟩
  · have := hord (Φ.symm ⟨outerS, hSR⟩)
    rw [MulEquiv.apply_symm_apply] at this
    rw [← this]
    exact hS2
  · rw [hΦ2, MulEquiv.apply_symm_apply]
    exact hSP
  · intro σ τ hσ2 hσ hτ2 hτ
    have hσP : ((Φ σ : mclR) : Equiv.Perm (Fin 275)) ∉ mclP := fun hm => hσ ((hΦ2 σ).2 hm)
    have hτP : ((Φ τ : mclR) : Equiv.Perm (Fin 275)) ∉ mclP := fun hm => hτ ((hΦ2 τ).2 hm)
    obtain ⟨a, ha, hax⟩ := hall _ (Φ σ).2 hσP (by rw [hord, hσ2])
    obtain ⟨b, hb, hby⟩ := hall _ (Φ τ).2 hτP (by rw [hord, hτ2])
    have hg : b * a⁻¹ ∈ mclP := mclP.mul_mem hb (mclP.inv_mem ha)
    refine ⟨mclPermEquiv.symm ⟨b * a⁻¹, hg⟩, Φ.injective (Subtype.ext ?_)⟩
    rw [map_mul, map_mul, map_inv]
    have hc := hΦ3 (mclPermEquiv.symm ⟨b * a⁻¹, hg⟩)
    rw [MulEquiv.apply_symm_apply] at hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc, hax, hby]
    group
  · intro σ hσ2 hσ
    have hσP : ((Φ σ : mclR) : Equiv.Perm (Fin 275)) ∉ mclP := fun hm => hσ ((hΦ2 σ).2 hm)
    obtain ⟨e11⟩ := nonempty_mulEquiv_m11_of_outer h (Φ σ).2 hσP (by rw [hord, hσ2])
    exact ⟨(@fixedEquiv 275 NativeSporadic.McL inferInstance mclP mclPermEquiv σ
      ((Φ σ : mclR) : Equiv.Perm (Fin 275)) (hΦ1 σ)).trans e11⟩

theorem isConj_involutions_of_equiv {n : ℕ} {T : Type*} [Group T]
    {P : Subgroup (Equiv.Perm (Fin n))} (e : T ≃* P) {t₀ : Equiv.Perm (Fin n)}
    (hall : ∀ τ ∈ P, orderOf τ = 2 → ∃ g ∈ P, τ = g * t₀ * g⁻¹) :
    ∀ s t : T, orderOf s = 2 → orderOf t = 2 → IsConj s t := by
  intro s t hs ht
  have hs' : orderOf ((e s : P) : Equiv.Perm (Fin n)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hs]
  have ht' : orderOf ((e t : P) : Equiv.Perm (Fin n)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  obtain ⟨g₁, hg₁, h₁⟩ := hall _ (e s).2 hs'
  obtain ⟨g₂, hg₂, h₂⟩ := hall _ (e t).2 ht'
  rw [isConj_iff]
  refine ⟨e.symm ⟨g₂ * g₁⁻¹, P.mul_mem hg₂ (P.inv_mem hg₁)⟩, e.injective (Subtype.ext ?_)⟩
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [h₁, h₂]
  group

theorem mcl_involutions_conj
    (s t : NativeSporadic.McL) (hs : orderOf s = 2) (ht : orderOf t = 2) : IsConj s t :=
  @isConj_involutions_of_equiv 275 NativeSporadic.McL inferInstance mclP mclPermEquiv _
    mclT0_facts.2.2.2.2 s t hs ht

theorem card_outer_mcl :
    Nat.card (Outer NativeSporadic.McL) = 2 := by
  obtain ⟨-, -, -, ⟨e⟩, -⟩ := mcl_full_automorphism_model
  have h2 : Nat.card (Outer mclP) = 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [Nat.card_congr (@CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    NativeSporadic.McL mclP
    inferInstance _ mclPermEquiv).toEquiv, h2]

theorem card_mcl_eq :
    Nat.card NativeSporadic.McL = 2 ^ 7 * 3 ^ 6 * 5 ^ 3 * 7 * 11 := by
  rw [CFSG.Sporadic.McL.card_McL]
  norm_num

theorem mclP_involution_product_order
    (h : invProdCheck = true) :
    ∀ u ∈ mclP, ∀ v ∈ mclP, orderOf u = 2 → orderOf v = 2 →
      ∃ m ∈ ({1, 2, 3, 4, 5, 6} : Finset ℕ), orderOf (u * v) = m := by
  have hD : GroupData 275 mclP mclPGTbls mclGen mclSift := mcl_groupData
  simp only [invProdCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have hpgi : ∀ l < mclPGTbls.size, Rep 275 mclPGInvTbls[l]! (mclGen l)⁻¹ := fun l hl =>
    Rep.inv_of_invOK (hD.rep l hl) (allIn_eq_true.1 h3 l (Nat.zero_le _) hl)
  have hT : Rep 275 invTab0 (tp 275 invTab0) := rep_tp h1
  obtain ⟨-, -, -, hrows, -⟩ := mcl_involution_centralizers
  obtain ⟨-, -, -, -, -, hcls⟩ := hrows _ List.mem_cons_self
  dsimp only at hcls
  have hsize : (conjClass mclP (tp 275 invTab0)).ncard ≤
      (conjClosureH 275 mclPGTbls mclPGInvTbls invTab0 30000).1.size := by
    rw [h6]
    exact hcls.le
  obtain ⟨-, hcover⟩ := conjClosure_cover hD hpgi hT h4 h5 hsize
  have h7' := (Array.all_eq_true'.1 h7)
  intro u hu v hv hu2 hv2
  obtain ⟨g₁, hg₁, rfl⟩ := mclT0_facts.2.2.2.2 u hu hu2
  obtain ⟨g₂, hg₂, rfl⟩ := mclT0_facts.2.2.2.2 v hv hv2
  have hc : g₁⁻¹ * g₂ ∈ mclP := mclP.mul_mem (mclP.inv_mem hg₁) hg₂
  obtain ⟨k, hk, hkrep⟩ := hcover (g₁⁻¹ * g₂ * tp 275 invTab0 * (g₁⁻¹ * g₂)⁻¹) ⟨_, hc, rfl⟩
  have hent := h7' _ (getElem!_mem_array hk)
  rw [List.any_eq_true] at hent
  obtain ⟨i, hi, hio⟩ := hent
  rw [List.mem_range] at hi
  have hrepc := Rep.compT hT hkrep
  have hord := (ordTest_iff_perm hrepc (by omega : 0 < i + 1)).1 hio
  refine ⟨i + 1, by simp only [Finset.mem_insert, Finset.mem_singleton]; omega, ?_⟩
  have e : g₁ * mclT0 * g₁⁻¹ * (g₂ * mclT0 * g₂⁻¹) = g₁ * (tp 275 invTab0 *
      (g₁⁻¹ * g₂ * tp 275 invTab0 * (g₁⁻¹ * g₂)⁻¹)) * g₁⁻¹ := by
    show _ = g₁ * (mclT0 * (g₁⁻¹ * g₂ * mclT0 * (g₁⁻¹ * g₂)⁻¹)) * g₁⁻¹
    group
  rw [e, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hord]

theorem mcl_involution_product_order_le
    (h : invProdCheck = true) (u v : NativeSporadic.McL) (hu : orderOf u = 2) (hv : orderOf v = 2) :
    orderOf (u * v) ≤ 6 := by
  have hu' : orderOf ((mclPermEquiv u : mclP) : Equiv.Perm (Fin 275)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hu]
  have hv' : orderOf ((mclPermEquiv v : mclP) : Equiv.Perm (Fin 275)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hv]
  obtain ⟨m, hm, hord⟩ := mclP_involution_product_order h _ (mclPermEquiv u).2 _
    (mclPermEquiv v).2 hu' hv'
  have hprod : orderOf (u * v) = orderOf (((mclPermEquiv u : mclP) : Equiv.Perm (Fin 275)) *
      ((mclPermEquiv v : mclP) : Equiv.Perm (Fin 275))) := by
    rw [← Subgroup.coe_mul, ← map_mul, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  rw [hprod, hord]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  omega

theorem orderOf_le_of_inverted {G : Type*} [Group G] {N : ℕ}
    (hprod : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → orderOf (u * v) ≤ N)
    {x t : G} (ht : orderOf t = 2) (hinv : t * x * t⁻¹ = x⁻¹) (hx : orderOf x ≠ 2) :
    orderOf x ≤ N := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [hti] at hinv
  have hv2 : (t * x) ^ 2 = 1 := by
    calc (t * x) ^ 2 = (t * x) * (t * x) := pow_two _
      _ = (t * x * t) * x := by simp only [mul_assoc]
      _ = 1 := by rw [hinv, inv_mul_cancel]
  have hv1 : t * x ≠ 1 := by
    intro h1
    have hxt : x = t := by
      calc x = t * (t * x) := by rw [← mul_assoc, ht2, one_mul]
        _ = t := by rw [h1, mul_one]
    exact hx (by rw [hxt, ht])
  have hvo : orderOf (t * x) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hv2 hv1
  have hle := hprod t (t * x) ht hvo
  have hxe : t * (t * x) = x := by rw [← mul_assoc, ht2, one_mul]
  rwa [hxe] at hle

theorem mcl_inverted_odd_order
    (h : invProdCheck = true) {x t : NativeSporadic.McL} (ht : orderOf t = 2)
    (hinv : t * x * t⁻¹ = x⁻¹) (hodd : Odd (orderOf x)) :
    x = 1 ∨ orderOf x = 3 ∨ orderOf x = 5 := by
  obtain ⟨k, hk⟩ := hodd
  have hle := @orderOf_le_of_inverted NativeSporadic.McL inferInstance 6
    (fun u v hu hv => mcl_involution_product_order_le h u v hu hv) x t ht hinv (by omega)
  by_cases h1 : orderOf x = 1
  · exact Or.inl (orderOf_eq_one_iff.1 h1)
  · right
    omega

end CFSG.Sporadic.Recognition.McLAS

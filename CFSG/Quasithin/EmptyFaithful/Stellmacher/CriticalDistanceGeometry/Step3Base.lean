module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.S3Lines
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.ZvSupInf
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.CommVnQv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 CFSG.Quasithin.EmptyFaithful.Stellmacher

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def IsGeodesic (p : ℕ → Geo H M) (n : ℕ) : Prop :=
  ∀ i ≤ n, ∀ j ≤ n, dist (p i) (p j) = (j - i) + (i - j)

section Path

variable {p : ℕ → Geo H M} {n : ℕ}

theorem IsGeodesic.dist_of_le (hp : IsGeodesic p n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    dist (p i) (p j) = j - i := by
  have := hp i (hij.trans hj) j hj
  omega

theorem IsGeodesic.mono (hp : IsGeodesic p n) {m : ℕ} (hm : m ≤ n) : IsGeodesic p m :=
  fun i hi j hj => hp i (hi.trans hm) j (hj.trans hm)

theorem IsGeodesic.adj (hp : IsGeodesic p n) {i : ℕ} (hi : i < n) :
    (graph (H ⊔ M) H M).Adj (p i) (p (i + 1)) :=
  dist_eq_one_iff_adj.mp (by rw [hp.dist_of_le (Nat.le_succ i) hi]; omega)

theorem IsGeodesic.mem_nbrs_succ (hp : IsGeodesic p n) {i : ℕ} (hi : i < n) :
    p (i + 1) ∈ nbrs (p i) := hp.adj hi

theorem IsGeodesic.mem_nbrs_pred (hp : IsGeodesic p n) {i : ℕ} (hi : i < n) :
    p i ∈ nbrs (p (i + 1)) := (hp.adj hi).symm

end Path

theorem dist_le_dist_nbr {x ν : Geo H M} (hν : ν ∈ nbrs x) (y : Geo H M) :
    dist y ν ≤ dist y x + 1 := by
  have h1 : dist x ν = 1 := dist_eq_one_iff_adj.mpr hν
  have := dist_triangle rfl y x ν
  omega

section Existence

theorem IsGeodesic.snoc {p : ℕ → Geo H M} {n : ℕ} (hp : IsGeodesic p n) {c : Geo H M}
    (hadj : c ∈ nbrs (p n)) (hd : dist (p 0) c = n + 1) :
    IsGeodesic (fun i => if i ≤ n then p i else c) (n + 1) := by
  have hend : ∀ j ≤ n, dist (p j) c = n + 1 - j := by
    intro j hj
    have h1 := dist_le_dist_nbr hadj (p j)
    rw [hp.dist_of_le hj le_rfl] at h1
    have h2 := dist_triangle rfl (p 0) (p j) c
    rw [hd, hp.dist_of_le (Nat.zero_le j) (hj.trans le_rfl)] at h2
    omega
  intro i hi j hj
  by_cases hin : i ≤ n <;> by_cases hjn : j ≤ n <;> simp only [hin, hjn, ite_true, ite_false]
  · exact hp i hin j hjn
  · have : j = n + 1 := by omega
    rw [hend i hin]; omega
  · have : i = n + 1 := by omega
    rw [CosetGeom.dist_comm, hend j hjn]; omega
  · have : i = n + 1 := by omega
    have : j = n + 1 := by omega
    rw [CosetGeom.dist_self]; omega

theorem exists_geodesic_aux (a : Geo H M) : ∀ (n : ℕ) (c : Geo H M), dist a c = n →
    ∃ p : ℕ → Geo H M, p 0 = a ∧ p n = c ∧ IsGeodesic p n := by
  intro n
  induction n with
  | zero =>
    intro c hc
    have : a = c := (CosetGeom.dist_eq_zero_iff rfl).mp hc
    subst this
    refine ⟨fun _ => a, rfl, rfl, ?_⟩
    intro i hi j hj
    have : i = 0 := by omega
    have : j = 0 := by omega
    subst_vars
    simp [CosetGeom.dist_self]
  | succ n ih =>
    intro c hc
    obtain ⟨c', hcc', hac'⟩ := exists_adj_dist_eq rfl hc
    obtain ⟨p, hp0, hpn, hp⟩ := ih c' hac'
    refine ⟨fun i => if i ≤ n then p i else c, by simp [hp0], by simp, ?_⟩
    refine hp.snoc ?_ ?_
    · rw [hpn]; exact hcc'.symm
    · rw [hp0]; exact hc

theorem IsGeodesic.cons {p : ℕ → Geo H M} {m : ℕ} (hp : IsGeodesic p m) {a : Geo H M}
    (hadj : p 0 ∈ nbrs a) (hd : dist a (p m) = m + 1) :
    IsGeodesic (fun i => if i = 0 then a else p (i - 1)) (m + 1) := by
  have ha0 : dist a (p 0) = 1 := dist_eq_one_iff_adj.mpr hadj
  have hstart : ∀ j ≤ m, dist a (p j) = j + 1 := by
    intro j hj
    have h1 := dist_triangle rfl a (p 0) (p j)
    rw [ha0, hp.dist_of_le (Nat.zero_le j) hj] at h1
    have h2 := dist_triangle rfl a (p j) (p m)
    rw [hd, hp.dist_of_le hj le_rfl] at h2
    omega
  intro i hi j hj
  by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0 <;> simp only [hi0, hj0, ite_true, ite_false]
  · simp [CosetGeom.dist_self]
  · rw [hstart (j - 1) (by omega)]; omega
  · rw [CosetGeom.dist_comm, hstart (i - 1) (by omega)]; omega
  · have := hp (i - 1) (by omega) (j - 1) (by omega)
    omega

end Existence

section CritPath

structure CritPath {G : Type} [Group G] [Finite G] {H M : Subgroup G} (α β α' : Geo H M) where
  p : ℕ → Geo H M
  p_zero : p 0 = α
  p_one : p 1 = β
  p_b : p (bMin H M) = α'
  isGeodesic : IsGeodesic p (bMin H M)

theorem critPath_nonempty {α β α' : Geo H M} (hc : IsCritData α β α') :
    Nonempty (CritPath α β α') := by
  have hb := hc.dist_eq'
  obtain ⟨p, hp0, hpm, hp⟩ := exists_geodesic_aux β (dist β α') α' rfl
  have hcons := hp.cons (a := α) (by rw [hp0]; exact hc.adj) (by rw [hpm, hc.dist_eq]; omega)
  rw [show dist β α' + 1 = bMin H M from hb] at hcons
  refine ⟨⟨fun i => if i = 0 then α else p (i - 1), by simp, by simpa using hp0, ?_, hcons⟩⟩
  have : bMin H M ≠ 0 := by omega
  simp only [this, ite_false]
  rw [show bMin H M - 1 = dist β α' by omega, hpm]

noncomputable def critPathOf {α β α' : Geo H M} (hc : IsCritData α β α') : CritPath α β α' :=
  (critPath_nonempty hc).some

theorem IsGeodesic.reverse {p : ℕ → Geo H M} {n : ℕ} (hp : IsGeodesic p n) :
    IsGeodesic (fun i => p (n - i)) n := by
  intro i hi j hj
  have := hp (n - i) (Nat.sub_le _ _) (n - j) (Nat.sub_le _ _)
  simp only
  omega

namespace CritPath

variable {α β α' : Geo H M} (P : CritPath α β α')

theorem dist_of_le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ bMin H M) :
    dist (P.p i) (P.p j) = j - i := P.isGeodesic.dist_of_le hij hj

theorem dist_start {j : ℕ} (hj : j ≤ bMin H M) : dist α (P.p j) = j := by
  have := P.dist_of_le (Nat.zero_le j) hj
  rw [P.p_zero] at this
  omega

theorem dist_end {j : ℕ} (hj : j ≤ bMin H M) : dist (P.p j) α' = bMin H M - j := by
  have := P.dist_of_le hj le_rfl
  rwa [P.p_b] at this

theorem vtype_iff (hA : F53Amalgam H M S) {j : ℕ} (hj : j ≤ bMin H M) :
    vtype (P.p j) = vtype α ↔ Even j := by
  have h := vtype_eq_iff_even_dist hA.amalgam.gen (P.p 0) (P.p j)
  rw [P.p_zero, P.dist_start hj] at h
  rw [eq_comm]
  exact h

noncomputable abbrev γ : Geo H M := P.p (bMin H M - 1)

noncomputable abbrev δ : Geo H M := P.p (bMin H M - 2)

noncomputable abbrev ε : Geo H M := P.p (bMin H M - 3)

theorem γ_adj (hb : 1 ≤ bMin H M) : α' ∈ nbrs P.γ := by
  have := P.isGeodesic.mem_nbrs_succ (i := bMin H M - 1) (by omega)
  rwa [show bMin H M - 1 + 1 = bMin H M by omega, P.p_b] at this

theorem δ_adj (hb : 2 ≤ bMin H M) : P.γ ∈ nbrs P.δ := by
  have := P.isGeodesic.mem_nbrs_succ (i := bMin H M - 2) (by omega)
  rwa [show bMin H M - 2 + 1 = bMin H M - 1 by omega] at this

theorem ε_adj (hb : 3 ≤ bMin H M) : P.δ ∈ nbrs P.ε := by
  have := P.isGeodesic.mem_nbrs_succ (i := bMin H M - 3) (by omega)
  rwa [show bMin H M - 3 + 1 = bMin H M - 2 by omega] at this

theorem dist_start_γ (hb : 1 ≤ bMin H M) : dist α P.γ = bMin H M - 1 := P.dist_start (by omega)
theorem dist_start_δ (hb : 2 ≤ bMin H M) : dist α P.δ = bMin H M - 2 := P.dist_start (by omega)
theorem dist_start_ε (hb : 3 ≤ bMin H M) : dist α P.ε = bMin H M - 3 := P.dist_start (by omega)

@[expose] noncomputable def reverse : CritPath α' P.γ α where
  p := fun i => P.p (bMin H M - i)
  p_zero := by simpa using P.p_b
  p_one := rfl
  p_b := by simpa using P.p_zero
  isGeodesic := P.isGeodesic.reverse

end CritPath

end CritPath

section Types

omit [Finite G] in
theorem mem_nbrs_comm {δ μ : Geo H M} (h : μ ∈ nbrs δ) : δ ∈ nbrs μ :=
  (show (graph (H ⊔ M) H M).Adj δ μ from h).symm

omit [Finite G] in
theorem vtype_false_of_mem_nbrs_true {δ μ : Geo H M} (h : μ ∈ nbrs δ) (hδ : vtype δ = true) :
    vtype μ = false := by
  have := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj δ μ from h)
  cases hμ : vtype μ
  · rfl
  · exact absurd (hδ.trans hμ.symm) this

omit [Finite G] in
theorem vtype_true_of_mem_nbrs_false {δ μ : Geo H M} (h : μ ∈ nbrs δ) (hδ : vtype δ = false) :
    vtype μ = true := by
  have := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj δ μ from h)
  cases hμ : vtype μ
  · exact absurd (hδ.trans hμ.symm) this
  · rfl

omit [Finite G] in
theorem Zv_le_Qv_of_dist_lt_bMin {δ μ : Geo H M} (h : dist δ μ < bMin H M) : Zv δ ≤ Qv μ :=
  Zv_le_Qv_of_dist_lt (h.trans_le (bMin_le_bAt δ))

theorem Zv_le_stab_of_dist_le_bMin (hA : F53Amalgam H M S) {δ μ : Geo H M}
    (h : dist δ μ ≤ bMin H M) : Zv δ ≤ stab μ :=
  Zv_le_stab_of_dist_le hA (h.trans (bMin_le_bAt δ))

theorem exists_mem_nbrs_ne (hA : F53Amalgam H M S) (δ : Geo H M) {ν : Geo H M} (hν : ν ∈ nbrs δ) :
    ∃ μ ∈ nbrs δ, μ ≠ ν := by
  have h : 1 < Nat.card (nbrs δ) := by
    cases hv : vtype δ
    · rw [card_nbrs_false hA hv]; norm_num
    · rw [card_nbrs_true hA hv]; norm_num
  have : Finite (nbrs δ) := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial (nbrs δ) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨μ, hμ⟩, hne⟩ := exists_ne (⟨ν, hν⟩ : nbrs δ)
  exact ⟨μ, hμ, fun h => hne (Subtype.ext h)⟩

omit [Finite G] in
theorem exists_unique_ne_one {Z : Subgroup G} (h : Nat.card Z = 2) :
    ∃ z : G, z ∈ Z ∧ z ≠ 1 ∧ ∀ x ∈ Z, x = 1 ∨ x = z := by
  obtain ⟨z, hz, hu⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp h
  refine ⟨z.1, z.2, fun h1 => hz (Subtype.ext h1), fun x hx => ?_⟩
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · exact Or.inr (congrArg Subtype.val (hu ⟨x, hx⟩ (fun h1 => hx1 (congrArg Subtype.val h1))))

open Classical in
@[expose] noncomputable def zgen (ν : Geo H M) : G :=
  if h : Nat.card (Zv ν) = 2 then (exists_unique_ne_one h).choose else 1

theorem zgen_spec {ν : Geo H M} (h : Nat.card (Zv ν) = 2) :
    zgen ν ∈ Zv ν ∧ zgen ν ≠ 1 ∧ ∀ x ∈ Zv ν, x = 1 ∨ x = zgen ν := by
  unfold zgen
  simp only [h, ↓reduceDIte]
  exact (exists_unique_ne_one h).choose_spec

theorem comm_Zv_eq_bot_of_le_Qv (hA : F53Amalgam H M S) {K : Subgroup G} {x : Geo H M}
    (h : K ≤ Qv x) : ⁅K, Zv x⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA x hz).2 k (h hk)).symm

theorem exists_third_mem_nbrs (hA : F53Amalgam H M S) {α β δ : Geo H M} (hα : vtype α = true)
    (hβδ : β ≠ δ) : ∃ ε ∈ nbrs α, ε ≠ β ∧ ε ≠ δ := by
  by_contra hcon
  push Not at hcon
  have h := card_nbrs_true hA hα
  rw [Nat.card_coe_set_eq] at h
  have hsub : nbrs α ⊆ {β, δ} := by
    intro x hx
    by_cases hxβ : x = β
    · exact Or.inl hxβ
    · exact Or.inr (hcon x hx hxβ)
  have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair hβδ] at h2
  omega

theorem eq_of_three_mem_nbrs (hA : F53Amalgam H M S) {α β δ ε : Geo H M} (hα : vtype α = true)
    (hβδ : β ≠ δ) (hβε : β ≠ ε) (hδε : δ ≠ ε) (hβ : β ∈ nbrs α) (hδ : δ ∈ nbrs α)
    (hε : ε ∈ nbrs α) : nbrs α = {β, δ, ε} := by
  have h := card_nbrs_true hA hα
  rw [Nat.card_coe_set_eq] at h
  symm
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · intro x hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · rw [h, Set.ncard_eq_three.mpr ⟨β, δ, ε, hβδ, hβε, hδε, rfl⟩]

theorem mem_Qv_of_fixes_two_nbrs (hA : F53Amalgam H M S) {δ γ ε : Geo H M} (hδ : vtype δ = true)
    (hγ : γ ∈ nbrs δ) (hε : ε ∈ nbrs δ) (hne : γ ≠ ε) {x : G} (hxδ : x ∈ stab δ)
    (hxγ : x ∈ stab γ) (hxε : x ∈ stab ε) : x ∈ Qv δ := by
  rw [Qv_eq_iInf hA δ]
  simp only [Subgroup.mem_iInf]
  intro μ hμ
  refine ⟨hxδ, ?_⟩
  obtain ⟨η, hη, hηγ, hηε⟩ := exists_third_mem_nbrs hA hδ hne
  have hn := eq_of_three_mem_nbrs hA hδ hne hηγ.symm hηε.symm hγ hε hη
  let g : ↥(H ⊔ M) := ⟨x, stab_le δ hxδ⟩
  have hgγ : g • γ = γ := smul_eq_of_mem_stab hxγ
  have hgε : g • ε = ε := smul_eq_of_mem_stab hxε
  have hgη : g • η = η := by
    have hm : g • η ∈ nbrs δ := smul_mem_nbrs hxδ hη
    rw [hn] at hm
    rcases hm with h | h | h
    · exact absurd (smul_left_cancel g (h.trans hgγ.symm)) hηγ
    · exact absurd (smul_left_cancel g (h.trans hgε.symm)) hηε
    · exact h
  have hμ' : μ ∈ ({γ, ε, η} : Set (Geo H M)) := hn ▸ hμ
  rcases hμ' with rfl | rfl | rfl
  · exact hxγ
  · exact hxε
  · exact mem_stab_of_smul_eq hgη

end Types

@[expose] def Wv (α : Geo H M) : Subgroup G :=
  ⨆ ν : {ν : Geo H M // vtype ν = false ∧ (dist α ν = 1 ∨ dist α ν = 3)}, Zv ν.1

theorem Zv_le_Wv {α ν : Geo H M} (hν : vtype ν = false) (h : dist α ν = 1 ∨ dist α ν = 3) :
    Zv ν ≤ Wv α :=
  le_iSup (fun ν : {ν : Geo H M // vtype ν = false ∧ (dist α ν = 1 ∨ dist α ν = 3)} => Zv ν.1)
    ⟨ν, hν, h⟩

theorem Wv_le {α : Geo H M} {K : Subgroup G}
    (h : ∀ ν : Geo H M, vtype ν = false → (dist α ν = 1 ∨ dist α ν = 3) → Zv ν ≤ K) :
    Wv α ≤ K :=
  iSup_le fun ν => h ν.1 ν.2.1 ν.2.2

theorem dist_eq_one_or_three (hA : F53Amalgam H M S) {α ν : Geo H M} (hα : vtype α = true) (hν : vtype ν = false)
    (h : dist α ν ≤ 3) : dist α ν = 1 ∨ dist α ν = 3 := by
  have hne : ¬ vtype α = vtype ν := by rw [hα, hν]; decide
  have hodd : ¬ Even (dist α ν) := fun he =>
    hne ((vtype_eq_iff_even_dist hA.amalgam.gen α ν).mpr he)
  rw [Nat.not_even_iff_odd, Nat.odd_iff] at hodd
  omega

omit [Finite G] in
theorem dist_le_three_of_gen {α ν : Geo H M} (h : dist α ν = 1 ∨ dist α ν = 3) :
    dist ν α ≤ 3 := by
  rw [CosetGeom.dist_comm]; omega

omit [Finite G] in
theorem conjSub_eq_self_of_comm {K : Subgroup G} {x : G} (h : ∀ z ∈ K, z * x = x * z) :
    conjSub x K = K := by
  ext y
  rw [mem_conjSub]
  constructor
  · intro hz
    have h1 := h _ hz
    have h2 : x⁻¹ * y * x = y := by
      have : x⁻¹ * y * x * x = y * x := by
        calc x⁻¹ * y * x * x = x * (x⁻¹ * y * x) := h1
          _ = y * x := by group
      exact mul_right_cancel this
    rwa [h2] at hz
  · intro hy
    have h1 := h _ hy
    have h2 : x⁻¹ * y * x = y := by
      calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
        _ = x⁻¹ * (x * y) := by rw [h1]
        _ = y := by group
    rwa [h2]

structure Step3Ctx (H M S : Subgroup G) (α β α' : Geo H M) : Prop where
  hA : F53Amalgam H M S
  h28 : Hss28At H M
  h32 : Hss32At H M
  h113a : Hss113aAt H M
  hc : IsCritData α β α'
  hv : vtype α = true
  hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥
  heven : Even (bMin H M)
  hb6 : 6 ≤ bMin H M

namespace Step3Ctx

variable {α β α' : Geo H M} (C : Step3Ctx H M S α β α')

include C

theorem hb2 : 2 ≤ bMin H M := by have := C.hb6; omega

theorem hb3 : 3 ≤ bMin H M := by have := C.hb6; omega

theorem vtype_beta : vtype β = false := vtype_false_of_mem_nbrs_true C.hc.adj C.hv

theorem vtype_alpha' : vtype α' = true := by
  have heven' : Even (dist α α') := by rw [C.hc.dist_eq]; exact C.heven
  have := (vtype_eq_iff_even_dist C.hA.amalgam.gen α α').mpr heven'
  rw [← this]; exact C.hv

noncomputable def path : CritPath α β α' := critPathOf C.hc

theorem Zv_le_center {ν : Geo H M} (hν : vtype ν = false) : Zv ν ≤ centerOf (stab ν) := by
  have hz := C.h32 α β C.hc.adj C.hv C.hc.bAt_eq
  have h1 := Zv_eq_omegaOneCenter_of_central C.hA hz
  have h2 := Zv_central_of_conj C.hA (show vtype β = vtype ν by rw [C.vtype_beta, hν]) h1
  rw [h2]; exact omegaOneCenter_le_centerOf_self _

theorem Zv_eq_omega {ν : Geo H M} (hν : vtype ν = false) :
    Zv ν = quasithinOmegaOneCenter (stab ν) :=
  Zv_eq_omegaOneCenter_of_central C.hA (C.Zv_le_center hν)

theorem bAt_eq_of_true {ℓ : Geo H M} (hℓ : vtype ℓ = true) : bAt ℓ = bMin H M := by
  rw [← C.hc.bAt_eq]; exact bAt_eq_of_vtype_eq (by rw [hℓ, C.hv])

theorem bMin_lt_bAt {ν : Geo H M} (hν : vtype ν = false) : bMin H M < bAt ν := by
  have h1 := bMin_le_bAt (H := H) (M := M) ν
  by_contra hne
  have heq : bAt ν = bMin H M := by omega
  have h12 := centralizer_Zv_eq_Qv_of_bAt C.hA heq
  have hcen : stab ν ≤ Subgroup.centralizer (Zv ν : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((Subgroup.mem_centralizer_iff.mp (C.Zv_le_center hν hz).2) x hx).symm
  rw [inf_eq_left.mpr hcen] at h12
  exact pCoreOf_ne_stab C.hA ν h12.symm

theorem Zv_le_Qv_of_dist_le {ν x : Geo H M} (hν : vtype ν = false) (h : dist ν x ≤ bMin H M) :
    Zv ν ≤ Qv x :=
  Zv_le_Qv_of_dist_lt (h.trans_lt (C.bMin_lt_bAt hν))

theorem Zv_le_stab_of_dist_le {ν x : Geo H M} (hν : vtype ν = false)
    (h : dist ν x ≤ bMin H M + 1) : Zv ν ≤ stab x := by
  have := C.bMin_lt_bAt hν
  exact _root_.CFSG.Quasithin.F53.Zv_le_stab_of_dist_le C.hA (by omega)

theorem exists_partner {ℓ : Geo H M} (hℓ : vtype ℓ = true) :
    ∃ d' : Geo H M, IsCritPair₁ ℓ d' ∧ ⁅Zv ℓ, Zv d'⁆ ≠ ⊥ := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (δ := α) (δ' := ℓ) (by rw [hℓ, C.hv])
  refine ⟨g • α', ⟨?_, ?_⟩, ?_⟩
  · rw [Zv_smul, Qv_smul, conjSub_le_conjSub_iff']
    exact C.hc.not_le
  · rw [CosetGeom.dist_smul]; exact C.hc.dist_eq
  · rw [Zv_smul, Zv_smul, conjSub_commutator]
    exact fun h => C.hcomm ((conjSub_eq_bot_iff _).mp h)

theorem centerOf_eq_bot {ℓ : Geo H M} (hℓ : vtype ℓ = true) : centerOf (stab ℓ) = ⊥ := by
  obtain ⟨e, he⟩ := exists_adj ℓ
  have hv := vtype_false_of_mem_nbrs_true (show e ∈ nbrs ℓ from he) hℓ
  exact centerOf_eq_bot_of_Zv_central C.hA (show ℓ ∈ nbrs e from he.symm) (C.Zv_le_center hv)

theorem Nv_eq_bot {ℓ : Geo H M} (hℓ : vtype ℓ = true) : Nv ℓ = ⊥ := by
  unfold Nv
  rw [C.centerOf_eq_bot hℓ]
  simp

theorem card_Zv_true_and {ℓ : Geo H M} (hℓ : vtype ℓ = true) :
    Nat.card (Zv ℓ) = 4 ∧ Z0v ℓ = Zv ℓ := by
  obtain ⟨d', hd', hcd⟩ := C.exists_partner hℓ
  obtain ⟨h4, hsup, -⟩ := Z0v_decomp C.hA C.h28 C.h113a C.hb2 hℓ (C.bAt_eq_of_true hℓ) hd' hcd
  rw [C.Nv_eq_bot hℓ, sup_bot_eq] at hsup
  exact ⟨by rw [← hsup]; exact h4, hsup⟩

theorem card_Zv_true {ℓ : Geo H M} (hℓ : vtype ℓ = true) : Nat.card (Zv ℓ) = 4 :=
  (C.card_Zv_true_and hℓ).1

theorem card_Zv_false {ν : Geo H M} (hν : vtype ν = false) : Nat.card (Zv ν) = 2 := by
  obtain ⟨ℓ, hℓ⟩ := exists_adj ν
  have hvℓ : vtype ℓ = true := vtype_true_of_mem_nbrs_false (show ℓ ∈ nbrs ν from hℓ) hν
  have h := OrdinaryProofs.card_Zv_eq_sq C.hA hvℓ hℓ.symm (C.Zv_le_center hν)
  rw [C.card_Zv_true hvℓ] at h
  have h2 : Nat.card (Zv ν) ^ 2 = 2 ^ 2 := by omega
  exact Nat.pow_left_injective (by norm_num) h2

theorem Zv_le_Zv_of_mem_nbrs {ℓ ν : Geo H M} (hℓ : vtype ℓ = true) (hν : ν ∈ nbrs ℓ) :
    Zv ν ≤ Zv ℓ := by
  have hvν := vtype_false_of_mem_nbrs_true hν hℓ
  rw [C.Zv_eq_omega hvν]
  have h := omegaOneCenter_le_Zv C.hA (show ℓ ∈ nbrs ν from (nbr_adj hν).symm)
  exact h.1.trans h.2.2

theorem Lv_eq_Zv {ℓ ν : Geo H M} (hℓ : vtype ℓ = true) (hν : ν ∈ nbrs ℓ) : Lv ℓ ν = Zv ν := by
  obtain ⟨d', hd', hcd⟩ := C.exists_partner hℓ
  have hbℓ := C.bAt_eq_of_true hℓ
  have h1 := Lv_le_Zv_inf C.hA C.h28 C.h113a C.hb2 hℓ hbℓ hd' hcd hν
  have h2 := card_Lv C.hA C.h28 C.h113a C.hb2 hℓ hbℓ hd' hcd hν
  have h3 := C.card_Zv_false (vtype_false_of_mem_nbrs_true hν hℓ)
  exact Subgroup.eq_of_le_of_card_ge (h1.trans inf_le_right) (by omega)

theorem Zv_sup_eq_and_inf_eq_bot {ℓ ν ν' : Geo H M} (hℓ : vtype ℓ = true) (hν : ν ∈ nbrs ℓ)
    (hν' : ν' ∈ nbrs ℓ) (hne : ν ≠ ν') : Zv ν ⊔ Zv ν' = Zv ℓ ∧ Zv ν ⊓ Zv ν' = ⊥ :=
  OrdinaryProofs.Zv_sup_eq_and_inf_eq_bot C.hA hℓ (C.bAt_eq_of_true hℓ) hν hν' hne
    (C.Zv_le_center (vtype_false_of_mem_nbrs_true hν hℓ))

theorem Zv_ne_of_mem_nbrs {ℓ ν ν' : Geo H M} (hℓ : vtype ℓ = true) (hν : ν ∈ nbrs ℓ)
    (hν' : ν' ∈ nbrs ℓ) (hne : ν ≠ ν') : Zv ν ≠ Zv ν' := by
  intro h
  have := (C.Zv_sup_eq_and_inf_eq_bot hℓ hν hν' hne).2
  rw [h, inf_idem] at this
  exact Zv_ne_bot C.hA ν' this

theorem Vn_eq_Zv {ℓ : Geo H M} (hℓ : vtype ℓ = true) : Vn ℓ = Zv ℓ := by
  apply le_antisymm
  · exact iSup₂_le fun ν hν => C.Zv_le_Zv_of_mem_nbrs hℓ hν
  · obtain ⟨ν, hν⟩ := exists_adj ℓ
    obtain ⟨ν', hν', hne⟩ := exists_mem_nbrs_ne C.hA ℓ (show ν ∈ nbrs ℓ from hν)
    rw [← (C.Zv_sup_eq_and_inf_eq_bot hℓ (show ν ∈ nbrs ℓ from hν) hν' hne.symm).1]
    exact sup_le (le_iSup₂_of_le (f := fun (μ : Geo H M) (_ : μ ∈ nbrs ℓ) => Zv μ) ν hν le_rfl)
      (le_iSup₂_of_le (f := fun (μ : Geo H M) (_ : μ ∈ nbrs ℓ) => Zv μ) ν' hν' le_rfl)

theorem isElemAbelian_Vn' (δ : Geo H M) : IsElemAbelian 2 (Vn δ) :=
  isElemAbelian_Vn C.hA C.hb3 δ

theorem comm_Vn_Qv_eq {ν : Geo H M} (hν : vtype ν = false) : ⁅Vn ν, Qv ν⁆ = Zv ν := by
  apply le_antisymm
  · exact OrdinaryProofs.commutator_Vn_Qv_le C.hA hν (C.Zv_le_center hν)
  · obtain ⟨ℓ, hℓ⟩ := exists_adj ν
    have hℓn : ℓ ∈ nbrs ν := hℓ
    have hvℓ := vtype_true_of_mem_nbrs_false hℓn hν
    have := C.Lv_eq_Zv hvℓ (show ν ∈ nbrs ℓ from hℓ.symm)
    rw [← this]
    exact Subgroup.commutator_mono (Zv_le_Vn_of_mem_nbrs hℓn) le_rfl

theorem isElemAbelian_Wv (α : Geo H M) : IsElemAbelian 2 (Wv α) := by
  have e : Wv α = ⨆ ν : {ν : Geo H M // vtype ν = false ∧ (dist α ν = 1 ∨ dist α ν = 3)}, Zv ν.1 :=
    rfl
  rw [e]
  refine isElemAbelian_iSup _ (fun ν => isElemAbelian_Zv C.hA ν.1) (fun ν ν' x hx y hy => ?_)
  have h1 := dist_le_three_of_gen ν.2.2
  have h2 := dist_le_three_of_gen ν'.2.2
  have h3 := dist_triangle rfl ν.1 α ν'.1
  have hxQ : x ∈ Qv ν'.1 := C.Zv_le_Qv_of_dist_le ν.2.1 (by
    have := C.hb6
    rw [CosetGeom.dist_comm α ν'.1] at h3
    have h2' : dist α ν'.1 ≤ 3 := by rw [CosetGeom.dist_comm]; exact h2
    have h1' : dist ν.1 α ≤ 3 := h1
    omega) hx
  exact (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv C.hA ν'.1 hy).2 x hxQ)

theorem dist_gen_le {α ν : Geo H M} (h : dist α ν = 1 ∨ dist α ν = 3) (x : Geo H M) :
    dist ν x ≤ 3 + dist α x := by
  have h1 := dist_le_three_of_gen h
  have h3 := dist_triangle (G₀ := H ⊔ M) (G₁ := H) (G₂ := M) rfl ν α x
  omega

theorem Wv_le_Qv_of_dist {α x : Geo H M} (h : dist α x + 3 ≤ bMin H M) : Wv α ≤ Qv x :=
  Wv_le fun ν hν hd => C.Zv_le_Qv_of_dist_le hν (by have := C.dist_gen_le hd x; omega)

theorem Wv_le_stab_of_dist {α x : Geo H M} (h : dist α x + 3 ≤ bMin H M + 1) : Wv α ≤ stab x :=
  Wv_le fun ν hν hd => C.Zv_le_stab_of_dist_le hν (by have := C.dist_gen_le hd x; omega)

theorem comm_Wv_Zv_nbr {α β : Geo H M} (hβ : β ∈ nbrs α) : ⁅Wv α, Zv β⁆ = ⊥ := by
  have h1 : dist α β = 1 := dist_eq_one_iff_adj.mpr hβ
  exact comm_Zv_eq_bot_of_le_Qv C.hA (C.Wv_le_Qv_of_dist (by have := C.hb6; omega))

theorem Vn_le_Wv {α ℓ : Geo H M} (hα : vtype α = true) (hℓ : vtype ℓ = true)
    (h : dist α ℓ ≤ 2) : Vn ℓ ≤ Wv α := by
  refine iSup₂_le fun ν hν => ?_
  have hvν := vtype_false_of_mem_nbrs_true hν hℓ
  have h1 : dist ℓ ν = 1 := dist_eq_one_iff_adj.mpr hν
  have h2 := dist_triangle (G₀ := H ⊔ M) (G₁ := H) (G₂ := M) rfl α ℓ ν
  exact Zv_le_Wv hvν (dist_eq_one_or_three C.hA hα hvν (by omega))

theorem Zv_le_Wv_of_true {α : Geo H M} (hα : vtype α = true) : Zv α ≤ Wv α := by
  rw [← C.Vn_eq_Zv hα]
  exact C.Vn_le_Wv hα hα (by rw [CosetGeom.dist_self]; omega)

theorem Vn_le_Wv_of_mem_nbrs {α β : Geo H M} (hα : vtype α = true) (hβ : β ∈ nbrs α) :
    Vn β ≤ Wv α := by
  have hvβ := vtype_false_of_mem_nbrs_true hβ hα
  refine iSup₂_le fun μ hμ => ?_
  have hvμ := vtype_true_of_mem_nbrs_false hμ hvβ
  rw [← C.Vn_eq_Zv hvμ]
  have h1 : dist α β = 1 := dist_eq_one_iff_adj.mpr hβ
  have h2 : dist β μ = 1 := dist_eq_one_iff_adj.mpr hμ
  have h3 := dist_triangle (G₀ := H ⊔ M) (G₁ := H) (G₂ := M) rfl α β μ
  exact C.Vn_le_Wv hα hvμ (by omega)

theorem Wv_eq_iSup_Vn {α : Geo H M} (hα : vtype α = true) :
    Wv α = ⨆ ℓ : {ℓ : Geo H M // vtype ℓ = true ∧ dist α ℓ = 2}, Vn ℓ.1 := by
  apply le_antisymm
  · refine Wv_le fun ν hν hd => ?_
    have hgen := C.hA.amalgam.gen
    have key : ∃ ℓ : Geo H M, vtype ℓ = true ∧ dist α ℓ = 2 ∧ ν ∈ nbrs ℓ := by
      rcases hd with hd | hd
      · have hαν : α ∈ nbrs ν := (dist_eq_one_iff_adj.mp hd).symm
        obtain ⟨ℓ, hℓ, hne⟩ := exists_mem_nbrs_ne C.hA ν hαν
        have hvℓ := vtype_true_of_mem_nbrs_false hℓ hν
        have h1 : dist ν ℓ = 1 := dist_eq_one_iff_adj.mpr hℓ
        have h2 := dist_triangle (G₀ := H ⊔ M) (G₁ := H) (G₂ := M) rfl α ν ℓ
        have hev : Even (dist α ℓ) := (vtype_eq_iff_even_dist hgen α ℓ).mp (by rw [hα, hvℓ])
        have h0 : dist α ℓ ≠ 0 := fun h0 =>
          hne ((CosetGeom.dist_eq_zero_iff hgen).mp h0).symm
        refine ⟨ℓ, hvℓ, ?_, mem_nbrs_comm hℓ⟩
        obtain ⟨k, hk⟩ := hev
        omega
      · obtain ⟨ℓ, hℓ, hdℓ⟩ := exists_adj_dist_eq hgen (α := α) (δ := ν) (d := 2) hd
        have hvℓ := vtype_true_of_mem_nbrs_false (show ℓ ∈ nbrs ν from hℓ) hν
        exact ⟨ℓ, hvℓ, hdℓ, hℓ.symm⟩
    obtain ⟨ℓ, hvℓ, hdℓ, hνℓ⟩ := key
    exact (Zv_le_Vn_of_mem_nbrs hνℓ).trans
      (le_iSup (fun ℓ : {ℓ : Geo H M // vtype ℓ = true ∧ dist α ℓ = 2} => Vn ℓ.1) ⟨ℓ, hvℓ, hdℓ⟩)
  · exact iSup_le fun ℓ => C.Vn_le_Wv hα ℓ.2.1 ℓ.2.2.le

theorem vtype_path_iff (P : CritPath α β α') {j : ℕ} (hj : j ≤ bMin H M) : vtype (P.p j) = true ↔ Even j := by
  have := P.vtype_iff C.hA hj
  rw [C.hv] at this
  exact this

theorem vtype_γ (P : CritPath α β α') : vtype P.γ = false := by
  have hb := C.hb6
  have hj : bMin H M - 1 ≤ bMin H M := Nat.sub_le _ _
  have h := C.vtype_path_iff P hj
  obtain ⟨k, hk⟩ := C.heven
  cases hv : vtype P.γ
  · rfl
  · exfalso
    obtain ⟨m, hm⟩ := h.mp hv
    omega

theorem vtype_δ (P : CritPath α β α') : vtype P.δ = true := by
  have hb := C.hb6
  have hj : bMin H M - 2 ≤ bMin H M := Nat.sub_le _ _
  refine (C.vtype_path_iff P hj).mpr ?_
  obtain ⟨k, hk⟩ := C.heven
  exact ⟨k - 1, by omega⟩

theorem vtype_ε (P : CritPath α β α') : vtype P.ε = false := by
  have hb := C.hb6
  have hj : bMin H M - 3 ≤ bMin H M := Nat.sub_le _ _
  have h := C.vtype_path_iff P hj
  obtain ⟨k, hk⟩ := C.heven
  cases hv : vtype P.ε
  · rfl
  · exfalso
    obtain ⟨m, hm⟩ := h.mp hv
    omega

theorem comm_eq_Zv_beta : ⁅Zv α, Zv α'⁆ = Zv β := by
  obtain ⟨hq, -⟩ := comm_eq_line C.hA C.h28 C.h113a C.hb2 C.hv C.hc.bAt_eq
    (show IsCritPair₁ α α' from ⟨C.hc.not_le, C.hc.dist_eq⟩) C.hcomm C.hc
  rw [hq]
  exact C.Lv_eq_Zv C.hv C.hc.adj

theorem critData_symm (P : CritPath α β α') : IsCritData α' P.γ α := by
  have hb := C.hb6
  refine ⟨mem_nbrs_comm (P.γ_adj (by omega)), C.bAt_eq_of_true C.vtype_alpha', ?_, ?_,
    not_le_Qv_of_comm_ne C.hA C.hcomm⟩
  · rw [CosetGeom.dist_comm]; exact C.hc.dist_eq
  · rw [CosetGeom.dist_comm, P.dist_start_γ (by omega)]; omega

theorem comm_eq_Zv_γ (P : CritPath α β α') : ⁅Zv α, Zv α'⁆ = Zv P.γ := by
  have hb := C.hb6
  have hcomm' : ⁅Zv α', Zv α⁆ ≠ ⊥ := by rw [Subgroup.commutator_comm]; exact C.hcomm
  have hd' : IsCritPair₁ α' α :=
    ⟨not_le_Qv_of_comm_ne C.hA C.hcomm, by rw [CosetGeom.dist_comm]; exact C.hc.dist_eq⟩
  obtain ⟨hq, -⟩ := comm_eq_line C.hA C.h28 C.h113a C.hb2 C.vtype_alpha'
    (C.bAt_eq_of_true C.vtype_alpha') hd' hcomm' (C.critData_symm P)
  rw [Subgroup.commutator_comm, hq]
  exact C.Lv_eq_Zv C.vtype_alpha' (mem_nbrs_comm (P.γ_adj (by omega)))

theorem Zv_beta_eq_Zv_γ (P : CritPath α β α') : Zv β = Zv P.γ := by
  rw [← C.comm_eq_Zv_beta, C.comm_eq_Zv_γ P]

theorem Wv_le_stab_δ (P : CritPath α β α') : Wv α ≤ stab P.δ :=
  C.Wv_le_stab_of_dist (by rw [P.dist_start_δ C.hb2]; have := C.hb6; omega)

theorem Wv_le_stab_γ (P : CritPath α β α') : Wv α ≤ stab P.γ := by
  have hb := C.hb6
  intro x hx
  have hxδ := C.Wv_le_stab_δ P hx
  have hγ : P.γ ∈ nbrs P.δ := P.δ_adj (by omega)
  have hcen : ∀ z ∈ Zv P.γ, z * x = x * z := by
    have h := C.comm_Wv_Zv_nbr C.hc.adj
    rw [C.Zv_beta_eq_Zv_γ P] at h
    exact fun z hz => Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx) z hz
  let g : ↥(H ⊔ M) := ⟨x, stab_le _ hxδ⟩
  have hgγ : g • P.γ ∈ nbrs P.δ := smul_mem_nbrs hxδ hγ
  have hZ : Zv (g • P.γ) = Zv P.γ := by
    rw [Zv_smul]
    exact conjSub_eq_self_of_comm hcen
  have heq : g • P.γ = P.γ := by
    by_contra hne
    exact C.Zv_ne_of_mem_nbrs (C.vtype_δ P) hgγ hγ hne hZ
  exact mem_stab_of_smul_eq heq

theorem symm (P : CritPath α β α') : Step3Ctx H M S α' P.γ α where
  hA := C.hA
  h28 := C.h28
  h32 := C.h32
  h113a := C.h113a
  hc := C.critData_symm P
  hv := C.vtype_alpha'
  hcomm := by rw [Subgroup.commutator_comm]; exact C.hcomm
  heven := C.heven
  hb6 := C.hb6

theorem Qv_sup_Qv_eq_edge {ℓ ν : Geo H M} (hℓ : vtype ℓ = true) (hν : ν ∈ nbrs ℓ) :
    Qv ℓ ⊔ Qv ν = stab ℓ ⊓ stab ν :=
  C.h28 (by have := C.hb6; omega) ℓ ν hν (C.bAt_eq_of_true hℓ)

end Step3Ctx

end F53.Stellmacher
end CFSG.Quasithin

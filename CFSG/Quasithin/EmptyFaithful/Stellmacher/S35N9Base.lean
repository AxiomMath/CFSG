module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtBase
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Hom
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5GLY2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S43
open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.N9

open S35.Std S35.At

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem mem_normalizer_of_conj_mem {X : Subgroup G} {g : G} (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have hle : X.map (MulAut.conj g).toMonoidHom ≤ X := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : X.map (MulAut.conj g).toMonoidHom = X := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hx' : g * x * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hx
  obtain ⟨y, hy, hyx⟩ := hx'
  have h2 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
  have : y = x := by simpa using h2
  rw [← this]
  exact hy

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A ⊔ B)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ A ⊔ B) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => hA a ha) (fun b hb => hB b hb)
  exact hle hx

theorem exists_normalClosure (hS : Sit H M S) {γ : Geo H M} {X : Subgroup G} (hVX : Vn γ ≤ X)
    (hXW : X ≤ Wb γ) (hXL : ∀ y ∈ X, ∀ l ∈ Lr γ, ⁅y, l⁆ ∈ Vn γ) :
    ∃ E : Subgroup G, stab γ ≤ Subgroup.normalizer (E : Set G) ∧ Vn γ ≤ E ∧ X ≤ E ∧
      E ≤ Wb γ ∧ ⁅E, Lr γ⁆ ≤ Vn γ := by
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup G, E = ⨆ g : ↥(stab γ), conjSub (g : G) X := ⟨_, rfl⟩
  have hiS : ∀ {P : Subgroup G}, (∀ g : ↥(stab γ), conjSub (g : G) X ≤ P) → E ≤ P := fun h => by
    rw [hEdef]; exact iSup_le h
  have hWst : Wb γ ≤ stab γ := (Wb_le_Qv hS γ).trans (Ch.Qv_le_stab' γ)
  have hle1 : ∀ g : ↥(stab γ), conjSub (g : G) X ≤ E := fun g => by
    rw [hEdef]; exact le_iSup (fun g : ↥(stab γ) => conjSub (g : G) X) g
  have hmem : ∀ (g : ↥(stab γ)) (x : G), (g : G)⁻¹ * x * (g : G) ∈ X → x ∈ E := fun g x hx =>
    hle1 g (mem_conjSub.mpr hx)
  have hXE : X ≤ E := fun y hy => hmem 1 y (by simpa using hy)
  refine ⟨E, ?_, hVX.trans hXE, hXE, ?_, ?_⟩
  · intro k hk
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    have hle : E ≤ E.comap (MulAut.conj k).toMonoidHom := by
      refine hiS fun g x hx => ?_
      have hx' : (g : G)⁻¹ * x * (g : G) ∈ X := mem_conjSub.mp hx
      rw [Subgroup.mem_comap]
      refine hmem (⟨k, hk⟩ * g) _ ?_
      have e : ((⟨k, hk⟩ * g : ↥(stab γ)) : G)⁻¹ * (k * x * k⁻¹) * ((⟨k, hk⟩ * g : ↥(stab γ)) : G) =
          (g : G)⁻¹ * x * (g : G) := by
        simp [mul_assoc]
      show _ * (k * x * k⁻¹) * _ ∈ X
      rw [e]
      exact hx'
    exact hle hx
  · refine hiS fun g x hx => ?_
    have hx' : (g : G)⁻¹ * x * (g : G) ∈ X := mem_conjSub.mp hx
    have h1 := (Subgroup.mem_normalizer_iff.mp (Wb_normal (G := G) γ g.2) _).mp (hXW hx')
    simpa [mul_assoc] using h1
  · refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
    have hle : E ≤ S35.At.commSub (Vn γ) l := by
      refine hiS (P := S35.At.commSub (Vn γ) l) fun g y hy => ?_
      have hy' : (g : G)⁻¹ * y * (g : G) ∈ X := mem_conjSub.mp hy
      have hyst : y ∈ stab γ := by
        have := (stab γ).mul_mem ((stab γ).mul_mem g.2 (hWst (hXW hy'))) ((stab γ).inv_mem g.2)
        simpa [mul_assoc] using this
      refine S35.At.mem_commSub.mpr ⟨Vn_normal γ hyst, ?_⟩
      have hl' : (g : G)⁻¹ * l * (g : G) ∈ Lr γ := by
        have h := (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_oTwoRes (stab γ) ((stab γ).inv_mem g.2)) l).mp hl
        rwa [inv_inv] at h
      have h2 := hXL _ hy' _ hl'
      have h3 := (Subgroup.mem_normalizer_iff.mp (Vn_normal γ g.2) _).mp h2
      have e : ⁅y, l⁆ = (g : G) * ⁅(g : G)⁻¹ * y * (g : G), (g : G)⁻¹ * l * (g : G)⁆ *
          (g : G)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact h3
    exact (S35.At.mem_commSub.mp (hle hx)).2

theorem coprime_five_card_mulAut (A : Type) [Group A] [Finite A] (h : Nat.card A ≤ 4) :
    Nat.Coprime 5 (Nat.card (MulAut A)) := by
  have hinj : Function.Injective (MulAut.toPerm A) := fun a b hab => MulEquiv.ext fun x =>
    congrArg (fun f : Perm A => f x) hab
  have hd := Subgroup.card_dvd_of_injective (MulAut.toPerm A) hinj
  rw [Nat.card_perm] at hd
  refine Nat.Coprime.coprime_dvd_right hd ?_
  have hpos : 0 < Nat.card A := Nat.card_pos
  interval_cases (Nat.card A) <;> decide

theorem comm_trivial_of_card_le_four (hS : Sit H M S) {γ : Geo H M} (hγ : vtype γ = false)
    {X : Subgroup G} (hXst : X ≤ stab γ) (hL : Lr γ ≤ Subgroup.normalizer (X : Set G))
    (hc : (Vn γ).relIndex X ≤ 4) : ∀ y ∈ X, ∀ l ∈ Lr γ, ⁅y, l⁆ ∈ Vn γ := by
  have hq := quot_stab_five hS.glob.amalg hγ
  have hVst : stab γ ≤ Subgroup.normalizer (Vn γ : Set G) := Vn_normal γ
  have hnorm : ((Vn γ).subgroupOf X).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hVst (hXst g.2)) n.1).mp hn⟩
  have hLN : Lr γ ≤ Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (Vn γ : Set G) :=
    le_inf hL ((oTwoRes_le _).trans hVst)
  let ρ : ↥(Lr γ) →* MulAut (↥X ⧸ (Vn γ).subgroupOf X) :=
    (S35.B5.GLY.convHom X (Vn γ)).comp (Subgroup.inclusion hLN)
  have hcard : Nat.card (↥X ⧸ (Vn γ).subgroupOf X) ≤ 4 := hc
  have h1 : ρ = 1 :=
    S35.B5.hom_trivial_of_coprime_five hq (coprime_five_card_mulAut _ hcard) ρ
  intro y hy l hl
  have h2 : S35.B5.GLY.convHom X (Vn γ) ⟨l, hLN hl⟩ = 1 := by
    have h3 : ρ ⟨l, hl⟩ = 1 := by rw [h1]; rfl
    exact h3
  exact (S35.B5.GLY.convHom_eq_one_iff X (Vn γ) ⟨l, hLN hl⟩).mp h2 y hy

theorem relIndex_ne_zero' (A B : Subgroup G) : A.relIndex B ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

theorem relIndex_le_of_sup_eq {X N Q N₀ : Subgroup G} (hNX : N ≤ X)
    (hQn : X ≤ Subgroup.normalizer (Q : Set G)) (hsup : N ⊔ Q = X) (hN₀ : N₀ ≤ N ⊓ Q) :
    N.relIndex X ≤ N₀.relIndex Q := by
  have h1 := B6.relIndex_inf_eq_relIndex_sup (T := N) (N := Q) (hNX.trans hQn)
  rw [hsup] at h1
  rw [← h1]
  exact Subgroup.relIndex_le_of_le_left hN₀ (relIndex_ne_zero' _ _)

end S35.N9

end F53.Stellmacher

end CFSG.Quasithin

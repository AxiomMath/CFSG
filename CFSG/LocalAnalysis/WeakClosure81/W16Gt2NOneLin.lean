module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOne
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneLinB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

private theorem conjSubgroup_inf_cTilde_eq (c : Cfg1620 M V₀ V U S R H g B) {m : G}
    (hm : m ∈ M) :
    conjSubgroup (F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)) m =
      F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G) := by
  have h1 : conjSubgroup (F11.CTilde M V₀ V) m = F11.CTilde M V₀ V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (le_normalizer_cTilde_of_hyp15 c.cex.hyp hm)
  have h2 : conjSubgroup (centralizer (V₀ : Set G)) m = centralizer (V₀ : Set G) := by
    rw [E3.conjSubgroup_centralizer,
      conjSubgroup_eq_iff_mem_normalizer.mpr (c.cex.hyp.h6.le_normalizer₀ hm)]
  rw [E3.conjSubgroup_inf, h1, h2]

private theorem le_normalizer_inf_cTilde (c : Cfg1620 M V₀ V U S R H g B) :
    M ≤ Subgroup.normalizer
      ((F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G) : Subgroup G) : Set G) :=
  fun _ hm => conjSubgroup_eq_iff_mem_normalizer.1 (conjSubgroup_inf_cTilde_eq c hm)

private theorem conjSubgroup_centralizer_eq_of_mem_normalizer {V : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (V : Set G)) :
    conjSubgroup (Subgroup.centralizer (V : Set G)) n = Subgroup.centralizer (V : Set G) := by
  rw [E3.conjSubgroup_centralizer, conjSubgroup_eq_iff_mem_normalizer.mpr hn]

private theorem le_normalizer_inf_centralizer (c : Cfg1620 M V₀ V U S R H g B) :
    (F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)) ≤
      Subgroup.normalizer ((centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro a ha
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  exact conjSubgroup_centralizer_eq_of_mem_normalizer (by
    rw [c.cex.hyp.h6.normalizer_eq]
    exact cTilde_le_M M V₀ V (Subgroup.mem_inf.1 ha).1)

private theorem le_normalizer_inf_cTilde_centralizer (c : Cfg1620 M V₀ V U S R H g B) :
    (F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)) ≤
      Subgroup.normalizer
        (((F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)) ⊓
          centralizer (V : Set G) : Subgroup G) : Set G) :=
  (le_inf Subgroup.le_normalizer (le_normalizer_inf_centralizer c)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

private theorem sq_mem_centralizer_of_mem_inf_cTilde (c : Cfg1620 M V₀ V U S R H g B) {a : G}
    (ha : a ∈ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)) :
    a ^ 2 ∈ centralizer (V : Set G) := by
  have hV : IsElemAbelian 2 V := c.cex.hyp.h6.elemAbelian
  have hV₀ : V₀ ≤ V := c.cex.hyp.h6.le
  have haC : a ∈ F11.CTilde M V₀ V := (Subgroup.mem_inf.1 ha).1
  have haV₀ : a ∈ centralizer (V₀ : Set G) := (Subgroup.mem_inf.1 ha).2
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hφ : a * v * a⁻¹ * v⁻¹ ∈ V₀ :=
    (FourteenTwo.mem_cTilde_iff_comm.1 haC).2.2 v hv
  have hac : a * (a * v * a⁻¹ * v⁻¹) * a⁻¹ = a * v * a⁻¹ * v⁻¹ := by
    rw [← (Subgroup.mem_centralizer_iff.1 haV₀) (a * v * a⁻¹ * v⁻¹) hφ]
    group
  have hφ2 : (a * v * a⁻¹ * v⁻¹) ^ 2 = 1 := hV.2 _ (hV₀ hφ)
  have hmain : a * a * v * (a * a)⁻¹ = v := by
    rw [mul_inv_rev]
    calc a * a * v * (a⁻¹ * a⁻¹)
        = a * (a * v * a⁻¹) * a⁻¹ := by group
      _ = a * ((a * v * a⁻¹ * v⁻¹) * v) * a⁻¹ := by group
      _ = (a * (a * v * a⁻¹ * v⁻¹) * a⁻¹) * (a * v * a⁻¹) := by group
      _ = (a * v * a⁻¹ * v⁻¹) * (a * v * a⁻¹) := by rw [hac]
      _ = (a * v * a⁻¹ * v⁻¹) * ((a * v * a⁻¹ * v⁻¹) * v) := by group
      _ = (a * v * a⁻¹ * v⁻¹) * (a * v * a⁻¹ * v⁻¹) * v := by group
      _ = v := by
            rw [show (a * v * a⁻¹ * v⁻¹) * (a * v * a⁻¹ * v⁻¹) = 1 by
              rw [← pow_two]; exact hφ2]
            group
  rw [mul_inv_eq_iff_eq_mul] at hmain
  simpa only [pow_two] using hmain.symm

private theorem exists_mul_mem_of_relIndex_two {Q V : Subgroup G} (hrel : Q.relIndex V = 2)
    {v₀ v : G} (hv₀V : v₀ ∈ V) (hv₀Q : v₀ ∉ Q) (hvV : v ∈ V) (hvQ : v ∉ Q) :
    ∃ q ∈ Q, v = v₀ * q := by
  have hidx : (Q.subgroupOf V).index = 2 := hrel
  have hmem : (⟨v₀, hv₀V⟩ : V)⁻¹ * ⟨v, hvV⟩ ∈ Q.subgroupOf V := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    constructor
    · intro h
      exact absurd (Q.inv_mem_iff.1 (by simpa [Subgroup.mem_subgroupOf] using h)) hv₀Q
    · intro h
      exact absurd (by simpa [Subgroup.mem_subgroupOf] using h) hvQ
  exact ⟨v₀⁻¹ * v, by simpa [Subgroup.mem_subgroupOf] using hmem, by group⟩

private theorem conj_mul_conj_eq_of_mem {y v₀ q : G} (hqy : q * y = y * q) :
    y * (v₀ * q) * y⁻¹ * (v₀ * q)⁻¹ = y * v₀ * y⁻¹ * v₀⁻¹ := by
  have hqy' : q * y⁻¹ = y⁻¹ * q := by
    rw [mul_inv_eq_iff_eq_mul]
    rw [mul_assoc, hqy]
    group
  calc y * (v₀ * q) * y⁻¹ * (v₀ * q)⁻¹
      = y * v₀ * (q * y⁻¹ * q⁻¹) * v₀⁻¹ := by group
    _ = y * v₀ * y⁻¹ * v₀⁻¹ := by rw [show q * y⁻¹ * q⁻¹ = y⁻¹ by rw [hqy']; group]

theorem exists_mem_cTilde_comm_eq (h1 : W16One G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (hn : E3.mQuot V (U ⊔ V₀) = 1) {m : G} (hm : m ∈ M)
    {w : G} (hw : w ∈ V₀) :
    ∃ x ∈ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G),
      (∀ v ∈ V, m * v * m⁻¹ ∈ U ⊔ V₀ → x * v * x⁻¹ * v⁻¹ = 1) ∧
      (∀ v ∈ V, m * v * m⁻¹ ∉ U ⊔ V₀ → x * v * x⁻¹ * v⁻¹ = w) := by
  have hV : IsElemAbelian 2 V := c.cex.hyp.h6.elemAbelian
  have hV₀ : V₀ ≤ V := c.cex.hyp.h6.le
  have hrel : (U ⊔ V₀).relIndex V = 2 := by
    rw [E3.relIndex_eq_two_pow c.cex.hyp.isPGroup, hn]
    norm_num
  have hnotle : ¬ V ≤ U ⊔ V₀ := by
    intro hle
    have h1' : (U ⊔ V₀).relIndex V = 1 := Subgroup.relIndex_eq_one.2 hle
    omega
  obtain ⟨v₀, hv₀V, hv₀Q⟩ : ∃ x : G, x ∈ V ∧ x ∉ U ⊔ V₀ := by
    by_contra hcon
    exact hnotle fun x hx => by
      by_contra hxQ
      exact hcon ⟨x, hx, hxQ⟩
  have hnormV : m ∈ Subgroup.normalizer (V : Set G) := by
    rw [c.cex.hyp.h6.normalizer_eq]
    exact hm
  have hwV₀ : m * w * m⁻¹ ∈ V₀ :=
    (Subgroup.mem_normalizer_iff.1 (c.cex.hyp.h6.le_normalizer₀ hm) w).1 hw
  obtain ⟨y, hy, hyw⟩ := exists_comm_eq_of_conjSubgroup h1 hS c hv₀V hv₀Q hwV₀
  have hyA : y ∈ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G) :=
    (Subgroup.mem_inf.1 ((conjSubgroup_le_inf_cTilde h1 hS c) hy)).2
  have hyI : y ∈ conjClosure (U ⊔ V₀) H :=
    conjSubgroup_le_conjClosure_of_mem c.g_mem.1 le_sup_right hy
  have hIab : IsElemAbelian 2 (conjClosure (U ⊔ V₀) H) := c.mem.isElemAbelian c.cex
  have hxA : m⁻¹ * y * m ∈ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G) := by
    have hmem : m⁻¹ * y * m ∈
        conjSubgroup (F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)) m := by
      refine mem_conjSubgroup_iff.2 ?_
      rw [show m * (m⁻¹ * y * m) * m⁻¹ = y by group]
      exact hyA
    rwa [conjSubgroup_inf_cTilde_eq c hm] at hmem
  have key : ∀ v ∈ V, (m⁻¹ * y * m) * v * (m⁻¹ * y * m)⁻¹ * v⁻¹ =
      m⁻¹ * (y * (m * v * m⁻¹) * y⁻¹ * (m * v * m⁻¹)⁻¹) * m := fun v _ => by group
  refine ⟨m⁻¹ * y * m, hxA, ?_, ?_⟩
  · intro v hv hvQ
    have hv'I : m * v * m⁻¹ ∈ conjClosure (U ⊔ V₀) H := le_conjClosure (U ⊔ V₀) H hvQ
    have hcomm : y * (m * v * m⁻¹) = (m * v * m⁻¹) * y :=
      B2F.isElemAbelian_comm hIab hyI hv'I
    have h1' : y * (m * v * m⁻¹) * y⁻¹ * (m * v * m⁻¹)⁻¹ = 1 := by rw [hcomm]; group
    rw [key v hv, h1']
    group
  · intro v hv hvQ
    have hv'V : m * v * m⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hnormV v).1 hv
    obtain ⟨q, hqQ, hv'eq⟩ := exists_mul_mem_of_relIndex_two hrel hv₀V hv₀Q hv'V hvQ
    have hqI : q ∈ conjClosure (U ⊔ V₀) H := le_conjClosure (U ⊔ V₀) H hqQ
    have hqy : q * y = y * q := B2F.isElemAbelian_comm hIab hqI hyI
    have h1' : y * (m * v * m⁻¹) * y⁻¹ * (m * v * m⁻¹)⁻¹ = m * w * m⁻¹ := by
      rw [hv'eq, conj_mul_conj_eq_of_mem hqy, hyw]
    rw [key v hv, h1']
    group

theorem exists_mem_conj_eq_of_comm (c : Cfg1620 M V₀ V U S R H g B)
    (hn : E3.mQuot V (U ⊔ V₀) = 1)
    (hA : ∀ m ∈ M, ∀ w ∈ V₀, ∃ x ∈ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G),
      (∀ v ∈ V, m * v * m⁻¹ ∈ U ⊔ V₀ → x * v * x⁻¹ * v⁻¹ = 1) ∧
      (∀ v ∈ V, m * v * m⁻¹ ∉ U ⊔ V₀ → x * v * x⁻¹ * v⁻¹ = w))
    (hirr : ∀ v ∈ V, (∀ m ∈ M, m * v * m⁻¹ ∈ U ⊔ V₀) → v ∈ V₀)
    {U' : Subgroup G} (hle : U' ≤ U ⊔ V₀) (hinf : U' ⊓ V₀ = ⊥) (hsup : U' ⊔ V₀ = U ⊔ V₀) :
    ∃ a ∈ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G), conjSubgroup U a = U' := by
  obtain ⟨Ψ, hΨV₀, hΨmul, hΨ1, hΨU⟩ := c.exists_hom_of_complement hle hinf hsup
  obtain ⟨a, ha, hcomm⟩ := c.exists_mem_cTilde_of_hom hn hA hirr hΨV₀ hΨmul hΨ1
  have hab : ∀ u ∈ U, a * u * a⁻¹ = u * Ψ u := fun u hu => by
    have hu' : u ∈ V := c.cex.le hu
    have h2 : a * u * a⁻¹ = Ψ u * u := by
      rw [← hcomm u hu']
      group
    rw [h2]
    exact B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian (c.cex.hyp.h6.le (hΨV₀ u hu')) hu'
  refine ⟨a⁻¹, inv_mem ha, ?_⟩
  ext x
  rw [mem_conjSubgroup_iff, hΨU, inv_inv]
  constructor
  · intro hx
    refine ⟨a⁻¹ * x * a, hx, ?_⟩
    rw [← hab _ hx]
    group
  · rintro ⟨u, hu, rfl⟩
    have h3 : a⁻¹ * (u * Ψ u) * a = u := by
      rw [← hab u hu]
      group
    rw [h3]
    exact hu

theorem exists_mem_cTilde_conjSubgroup_eq (h1 : W16One G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (hn : E3.mQuot V (U ⊔ V₀) = 1) {U' : Subgroup G}
    (hle : U' ≤ U ⊔ V₀) (hinf : U' ⊓ V₀ = ⊥) (hsup : U' ⊔ V₀ = U ⊔ V₀) :
    ∃ a ∈ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G), conjSubgroup U a = U' :=
  c.exists_mem_conj_eq_of_comm hn (fun _ hm _ hw => c.exists_mem_cTilde_comm_eq h1 hS hn hm hw)
    (fun _ hv h => c.mem_of_forall_conj_mem_sup hv h) hle hinf hsup

theorem exists_mul_eq_inf (c : Cfg1620 M V₀ V U S R H g B) {a : G}
    (ha : a ∈ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)) :
    ∃ b ∈ R ⊓ (F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)),
      ∃ d ∈ centralizer (V : Set G), a = b * d := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A : Subgroup G := F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)
  let N : Subgroup G := A ⊓ centralizer (V : Set G)
  have haA : a ∈ A := ha
  have hAleC : A ≤ F11.CTilde M V₀ V := inf_le_left
  have hA_normal : (A.subgroupOf (F11.CTilde M V₀ V)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAleC]
    exact (cTilde_le_M M V₀ V).trans (le_normalizer_inf_cTilde c)
  have hSylowA : IsSylowIn 2 (R ⊓ A) A := c.sylow.inf_normal hAleC hA_normal
  have hN_normal : (N.subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact le_normalizer_inf_cTilde_centralizer c
  have hq : ∀ x ∈ A, ∃ k : ℕ, x ^ 2 ^ k ∈ N := by
    intro x hx
    refine ⟨1, ?_⟩
    exact Subgroup.mem_inf.2 ⟨by simpa using A.pow_mem hx 2,
      by simpa using sq_mem_centralizer_of_mem_inf_cTilde c hx⟩
  obtain ⟨s, hs, n, hn, hsn⟩ :=
    exists_mul_eq_of_pow_mem (p := 2) hN_normal hq hSylowA a haA
  exact ⟨s, hs, n, (Subgroup.mem_inf.1 hn).2, hsn⟩

theorem exists_mem_inf_conj_eq (h1 : W16One G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (hn : E3.mQuot V (U ⊔ V₀) = 1) {U' : Subgroup G}
    (hle : U' ≤ U ⊔ V₀) (hinf : U' ⊓ V₀ = ⊥) (hsup : U' ⊔ V₀ = U ⊔ V₀) :
    ∃ b ∈ R ⊓ (F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G)), conjSubgroup U b = U' := by
  obtain ⟨a, ha, haU⟩ := exists_mem_cTilde_conjSubgroup_eq h1 hS c hn hle hinf hsup
  obtain ⟨b, hb, d, hd, hab⟩ := exists_mul_eq_inf c ha
  have hbA : b ∈ F11.CTilde M V₀ V ⊓ centralizer (V₀ : Set G) := (Subgroup.mem_inf.1 hb).2
  have hbV : conjSubgroup U b ≤ V := by
    calc conjSubgroup U b ≤ conjSubgroup (U ⊔ V₀) b := E3.conjSubgroup_mono_left b le_sup_left
      _ = U ⊔ V₀ := conjSubgroup_sup_eq c hbA
      _ ≤ V := sup_le c.cex.le c.cex.hyp.h6.le
  have hdN : d ∈ Subgroup.normalizer (conjSubgroup U b : Set G) :=
    (Subgroup.centralizer_le_normalizer (conjSubgroup U b : Set G))
      ((Subgroup.centralizer_le hbV) hd)
  have hfix : conjSubgroup (conjSubgroup U b) d = conjSubgroup U b :=
    conjSubgroup_eq_iff_mem_normalizer.2 hdN
  have hconj : conjSubgroup U (b * d) = conjSubgroup U b := by
    rw [← conjSubgroup_conjSubgroup, hfix]
  exact ⟨b, hb, by rw [← hconj, ← hab]; exact haU⟩

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81

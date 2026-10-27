module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LNi
public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Grp4
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LNm

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
  CFSG.Quasithin.H13
open scoped commutatorElement

theorem s9g_conj_mem_kerIn {G : Type} [Group G] {M H : Subgroup G} {h x : G}
    (hh : h ∈ H) (hx : x ∈ kerIn M H) : h * x * h⁻¹ ∈ kerIn M H := by
  rw [mem_kerIn] at hx ⊢
  intro b hb
  have h1 := hx (b * h) (H.mul_mem hb hh)
  convert h1 using 1
  group

def s9gCent {G : Type} [Group G] (M H K : Subgroup G) : Subgroup G where
  carrier := {w | w ∈ H ∧ ∀ k ∈ K, ⁅w, k⁆ ∈ kerIn M H}
  one_mem' := ⟨H.one_mem, fun k _ => by simp [commutatorElement_def]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨H.mul_mem ha hb, fun k hk => ?_⟩
    have e : ⁅a * b, k⁆ = a * ⁅b, k⁆ * a⁻¹ * ⁅a, k⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (kerIn M H).mul_mem (s9g_conj_mem_kerIn ha (hb' k hk)) (ha' k hk)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨H.inv_mem ha, fun k hk => ?_⟩
    have e : ⁅a⁻¹, k⁆ = a⁻¹ * ⁅a, k⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact s9g_conj_mem_kerIn (H.inv_mem ha) ((kerIn M H).inv_mem (ha' k hk))

theorem s9g_K_le_closure_conj {G : Type} [Group G] [Finite G] {M H K T : Subgroup G}
    (hKH : K ≤ H) (hperf : ⁅K, K⁆ = K) (hs : IsSimpleGroup ↥(E2.star M H K))
    (hsolv : Group.IsSolvable ↥(K ⊓ kerIn M H)) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    {v : G} (hv : v ∈ T) {k₀ : G} (hk₀ : k₀ ∈ K) (hnot : ⁅v, k₀⁆ ∉ kerIn M H) :
    K ≤ Subgroup.closure {x : G | ∃ k ∈ K, x = k * v * k⁻¹} := by
  set gens : Set G := {x : G | ∃ k ∈ K, x = k * v * k⁻¹}
  have hvC : v ∈ Subgroup.closure gens :=
    Subgroup.subset_closure (show v ∈ gens from ⟨1, K.one_mem, by simp⟩)
  have hconjC : ∀ k ∈ K, k * v * k⁻¹ ∈ Subgroup.closure gens := fun k hk =>
    Subgroup.subset_closure (show k * v * k⁻¹ ∈ gens from ⟨k, hk, rfl⟩)
  have hCinv : ∀ g ∈ K, ∀ x ∈ Subgroup.closure gens,
      g * x * g⁻¹ ∈ Subgroup.closure gens := by
    intro g hg
    have hle : Subgroup.closure gens ≤
        (Subgroup.closure gens).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      show g * (k * v * k⁻¹) * g⁻¹ ∈ Subgroup.closure gens
      rw [show g * (k * v * k⁻¹) * g⁻¹ = g * k * v * (g * k)⁻¹ by group]
      exact hconjC _ (K.mul_mem hg hk)
    exact fun x hx => hle hx
  have hvK : ∀ k ∈ K, v * k * v⁻¹ ∈ K := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp (hTK hv) k).mp hk
  have hcommK : ∀ k ∈ K, ⁅v, k⁆ ∈ K := fun k hk => by
    rw [commutatorElement_def]
    exact K.mul_mem (hvK k hk) (K.inv_mem hk)
  have hcommC : ∀ k ∈ K, ⁅v, k⁆ ∈ Subgroup.closure gens := fun k hk => by
    rw [show ⁅v, k⁆ = v * (k * v * k⁻¹)⁻¹ by simp only [commutatorElement_def]; group]
    exact (Subgroup.closure gens).mul_mem hvC ((Subgroup.closure gens).inv_mem (hconjC k hk))
  have hC'n : ((Subgroup.closure gens).subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := hCinv (g : G) g.2 (n : G) hn
    simpa using h1
  haveI := hC'n
  set X : Set ↥K := {y : ↥K | ∃ k ∈ K, (y : G) = ⁅v, k⁆}
  have hR : Subgroup.normalClosure X ≤ (Subgroup.closure gens).subgroupOf K := by
    apply Subgroup.normalClosure_le_normal
    intro y hy
    obtain ⟨k, hk, hy⟩ := hy
    show (y : G) ∈ Subgroup.closure gens
    rw [hy]
    exact hcommC k hk
  have hRtop : Subgroup.normalClosure X = ⊤ := by
    by_contra hne
    have hle := proper_normal_le_ker_star hKH hperf hs hsolv (Subgroup.normalClosure X)
      inferInstance hne
    have hmem : (⟨⁅v, k₀⁆, hcommK k₀ hk₀⟩ : ↥K) ∈ Subgroup.normalClosure X :=
      Subgroup.subset_normalClosure ⟨k₀, hk₀, rfl⟩
    have h1 := hle hmem
    rw [MonoidHom.mem_ker, mem_ker_starHom] at h1
    exact hnot h1
  intro x hx
  have hxmem : (⟨x, hx⟩ : ↥K) ∈ Subgroup.normalClosure X := by
    rw [hRtop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp (hR hxmem)

theorem s9_outer_t {G : Type} [Group G] [Finite G] {H T M K : Subgroup G}
    (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hres : L32Residual H T M K) (hTsyl : CFSG.QuasithinUnique.IsSylowTwoOf T H) :
    ∃ τ ∈ T, ∀ k ∈ K, ∃ x ∈ K, τ * x * τ⁻¹ * (k * x * k⁻¹)⁻¹ ∉ K ⊓ kerIn M H := by
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := by
    rw [hHK]
    exact le_sup_right
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hres.1
  obtain ⟨x, hxTs, hxn⟩ : ∃ x ∈ E2.star M H T, ¬ s9gInner (E2.star M H K) x := by
    rcases hres.2.2 with hc1 | hc2
    · exact s9g4_c1 hKH hTH hHK hTK hTsyl hc1.1 hc1.2.1
    · exact s9g4_c2 hKH hTsyl (isPSL_three_two_of_isPSL_two_seven hc2.1) hc2.2.2
  obtain ⟨z, hzT, rfl⟩ := s9g3_mem_star.mp hxTs
  have htT : (z : G) ∈ T := Subgroup.mem_subgroupOf.mp hzT
  exact ⟨z, htT, s9g3_outer_translate hKH hTH htT hxn⟩

end CFSG.Quasithin.H13.L829N

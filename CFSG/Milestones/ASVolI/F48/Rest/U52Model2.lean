module

public import CFSG.Milestones.ASVolI.F48.Rest.U52Model
public import Certificates.Certificate7772
public import CFSG.Milestones.ASVolI.F48.Rest.G23ModelBase
public import CFSG.Milestones.ASVolI.F48.Rest.U52Facts

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.Open
open scoped Matrix Pointwise

attribute [local irreducible] burnsideF48t_u52LArr burnsideF48t_u52GensArr

section Scalars

variable {K : Type} [Field K] {ω : K}

theorem burnsideF48t_gf4D_surj (hK : Nat.card K = 4) (h2 : (2 : K) = 0) (hω : ω ^ 2 = ω + 1)
    (c : K) : ∃ a < 4, burnsideF48t_gf4D ω a = c := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : Fintype K := Fintype.ofFinite K
  let f : Fin 4 → K := fun a => burnsideF48t_gf4D ω a
  have hf : Function.Injective f := fun a b h =>
    Fin.ext (burnsideF48t_gf4D_inj h2 hω a.2 b.2 h)
  have hc : Fintype.card (Fin 4) = Fintype.card K := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hK]
  obtain ⟨a, ha⟩ := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hc⟩).2 c
  exact ⟨a, a.2, ha⟩

theorem burnsideF48t_u52_dv_scale (h2 : (2 : K) = 0) (hω : ω ^ 2 = ω + 1) {l : ℕ} (hl : l < 4)
    {v : Array ℕ} (hv : burnsideF48t_u52Small v) :
    burnsideF48t_u52dv ω (burnsideF48t_u52Scale l v) =
      burnsideF48t_gf4D ω l • burnsideF48t_u52dv ω v := by
  funext j
  simp only [burnsideF48t_u52dv, burnsideF48t_u52Scale, Pi.smul_apply, smul_eq_mul]
  rw [getElem!_ofFn_nat _ j.2]
  exact burnsideF48t_gf4D_mul h2 hω hl (hv j j.2)

theorem burnsideF48t_u52_small_scale {l : ℕ} (hl : l < 4) {v : Array ℕ}
    (hv : burnsideF48t_u52Small v) : burnsideF48t_u52Small (burnsideF48t_u52Scale l v) :=
  fun j hj => by
    simp only [burnsideF48t_u52Scale]
    rw [getElem!_ofFn_nat _ hj]
    exact burnsideF48t_gf4Mul_lt hl (hv j hj)

theorem burnsideF48t_u52_size_scale (l : ℕ) (v : Array ℕ) :
    (burnsideF48t_u52Scale l v).size = 5 := by
  simp [burnsideF48t_u52Scale]

end Scalars

section RGroup

variable {K : Type} [Field K] (ω : K)

@[expose] noncomputable def burnsideF48t_u52RGen (bar : K →+* K) (k : ℕ) : GL (Fin 5) K :=
  burnsideF48t_transU bar (burnsideF48t_u52dv ω burnsideF48t_u52U[k]!)

@[expose] noncomputable def burnsideF48t_u52R (bar : K →+* K) : Subgroup (GL (Fin 5) K) :=
  Subgroup.closure (Set.range fun k : Fin 6 => burnsideF48t_u52RGen ω bar k)

variable {ω}

theorem burnsideF48t_u52_RGen_mem (bar : K →+* K) {k : ℕ} (hk : k < 6) :
    burnsideF48t_u52RGen ω bar k ∈ burnsideF48t_u52R ω bar :=
  Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩

end RGroup

section PtLn


theorem burnsideF48t_u52_U' {k : ℕ} (hk : k < 6) :
    burnsideF48t_u52Small burnsideF48t_u52U[k]! ∧
      burnsideF48t_u52Dot (burnsideF48t_u52Bar burnsideF48t_u52U[k]!) burnsideF48t_u52U[k]! = 0 :=
  Certificates.certificate7772.2 k hk

theorem burnsideF48t_u52_iso' {K : Type} [Field K] {ω : K} (h2 : (2 : K) = 0) (hω : ω ^ 2 = ω + 1)
    (bar : K →+* K) (hbar : ∀ c, bar c = c ^ 2) {k : ℕ} (hk : k < 6) :
    (fun j => bar (burnsideF48t_u52dv ω burnsideF48t_u52U[k]! j)) ⬝ᵥ
      burnsideF48t_u52dv ω burnsideF48t_u52U[k]! = 0 := by
  obtain ⟨hs, hiso⟩ := burnsideF48t_u52_U' hk
  have e : (fun j => bar (burnsideF48t_u52dv ω burnsideF48t_u52U[k]! j)) =
      burnsideF48t_u52dv ω (burnsideF48t_u52Bar burnsideF48t_u52U[k]!) := by
    rw [burnsideF48t_u52_dv_bar h2 hω hs]
    funext j
    exact hbar _
  rw [e, burnsideF48t_u52_dv_dot h2 hω (burnsideF48t_u52_small_bar hs) hs, hiso]
  simp [burnsideF48t_gf4D]

theorem burnsideF48t_u52_ptln :
    (burnsideF48t_u52Pt ()).size = 165 ∧ burnsideF48t_u52LnPts.size = 297 ∧
    (burnsideF48t_u52Gens ()).size = 6 ∧
    (∀ p ∈ burnsideF48t_u52Pt (), p.size = 5 ∧ ∀ x ∈ p, x < 4) ∧
    (∀ i < 165, ∀ j < 165, i ≠ j → ∀ l ∈ [1, 2, 3],
      (burnsideF48t_u52Pt ())[i]! ≠ burnsideF48t_u52Scale l (burnsideF48t_u52Pt ())[j]!) ∧
    (∀ L ∈ burnsideF48t_u52LnPts, L.size = 5 ∧ (∀ p ∈ L, p < 165) ∧
      ∀ a < 5, ∀ b < 5, a ≠ b → L[a]! ≠ L[b]!) ∧
    (∀ l < 297, ∀ l' < 297, l ≠ l' →
      ∃ p ∈ burnsideF48t_u52LnPts[l]!, p ∉ burnsideF48t_u52LnPts[l']!) ∧
    (∀ k < 6, ∀ i < 165, ((burnsideF48t_u52Gens ())[k]!)[i]! < 165 ∧
      ∃ l ∈ [1, 2, 3], burnsideF48t_u52TV burnsideF48t_u52U[k]! (burnsideF48t_u52Pt ())[i]! =
        burnsideF48t_u52Scale l (burnsideF48t_u52Pt ())[((burnsideF48t_u52Gens ())[k]!)[i]!]!) ∧
    (∀ k < 6, ∀ l < 297, 165 ≤ ((burnsideF48t_u52Gens ())[k]!)[165 + l]! ∧
      ((burnsideF48t_u52Gens ())[k]!)[165 + l]! < 462 ∧
      (∀ p ∈ burnsideF48t_u52LnPts[l]!, ((burnsideF48t_u52Gens ())[k]!)[p]! ∈
        burnsideF48t_u52LnPts[((burnsideF48t_u52Gens ())[k]!)[165 + l]! - 165]!) ∧
      (∀ q ∈ burnsideF48t_u52LnPts[((burnsideF48t_u52Gens ())[k]!)[165 + l]! - 165]!,
        ∃ p ∈ burnsideF48t_u52LnPts[l]!, ((burnsideF48t_u52Gens ())[k]!)[p]! = q)) :=
  Certificates.certificate7772.1

theorem burnsideF48t_u52_pt_small {i : ℕ} (hi : i < 165) :
    ((burnsideF48t_u52Pt ())[i]!).size = 5 ∧ burnsideF48t_u52Small (burnsideF48t_u52Pt ())[i]! := by
  obtain ⟨hs, -, -, hp, -⟩ := burnsideF48t_u52_ptln
  have hmem : (burnsideF48t_u52Pt ())[i]! ∈ burnsideF48t_u52Pt () := by
    rw [getElem!_pos _ i (by rw [hs]; exact hi)]
    exact Array.getElem_mem _
  obtain ⟨h5, hlt⟩ := hp _ hmem
  refine ⟨h5, fun j hj => hlt _ ?_⟩
  rw [getElem!_pos _ j (by rw [h5]; exact hj)]
  exact Array.getElem_mem _

variable {K : Type} [Field K] (ω : K)

@[expose] def burnsideF48t_u52ObPt (i : ℕ) : Set (Fin 5 → K) :=
  {w | ∃ c : K, c ≠ 0 ∧ w = c • burnsideF48t_u52dv ω (burnsideF48t_u52Pt ())[i]!}

@[expose] def burnsideF48t_u52Ob' (o : Fin 462) : Set (Fin 5 → K) :=
  if (o : ℕ) < 165 then burnsideF48t_u52ObPt ω o
  else {w | ∃ p ∈ burnsideF48t_u52LnPts[(o : ℕ) - 165]!, w ∈ burnsideF48t_u52ObPt ω p}

variable {ω}

theorem burnsideF48t_u52_pt_inj (hK : Nat.card K = 4) (h2 : (2 : K) = 0) (hω : ω ^ 2 = ω + 1)
    {i j : ℕ} (hi : i < 165) (hj : j < 165) {c : K} (hc : c ≠ 0)
    (h : burnsideF48t_u52dv ω (burnsideF48t_u52Pt ())[i]! =
      c • burnsideF48t_u52dv ω (burnsideF48t_u52Pt ())[j]!) : i = j := by
  by_contra hij
  obtain ⟨a, ha4, rfl⟩ := burnsideF48t_gf4D_surj hK h2 hω c
  have ha0 : a ≠ 0 := fun h0 => hc (by rw [h0]; simp [burnsideF48t_gf4D])
  obtain ⟨hsi, hi'⟩ := burnsideF48t_u52_pt_small hi
  obtain ⟨hsj, hj'⟩ := burnsideF48t_u52_pt_small hj
  rw [← burnsideF48t_u52_dv_scale h2 hω ha4 hj'] at h
  have he := burnsideF48t_u52_dv_inj h2 hω hsi (burnsideF48t_u52_size_scale _ _) hi'
    (burnsideF48t_u52_small_scale ha4 hj') h
  have hmem : a ∈ [1, 2, 3] := by
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    omega
  exact burnsideF48t_u52_ptln.2.2.2.2.1 i hi j hj hij a hmem he

theorem burnsideF48t_u52_mem_ObPt (i : ℕ) :
    burnsideF48t_u52dv ω (burnsideF48t_u52Pt ())[i]! ∈ burnsideF48t_u52ObPt ω i :=
  ⟨1, one_ne_zero, (one_smul _ _).symm⟩

theorem burnsideF48t_u52_ObPt_eq (hK : Nat.card K = 4) (h2 : (2 : K) = 0) (hω : ω ^ 2 = ω + 1)
    {i j : ℕ} (hi : i < 165) (hj : j < 165)
    (h : burnsideF48t_u52dv ω (burnsideF48t_u52Pt ())[i]! ∈ burnsideF48t_u52ObPt ω j) : i = j := by
  obtain ⟨c, hc, he⟩ := h
  exact burnsideF48t_u52_pt_inj hK h2 hω hi hj hc he

theorem burnsideF48t_u52_Ob'_injective (hK : Nat.card K = 4) (h2 : (2 : K) = 0)
    (hω : ω ^ 2 = ω + 1) : Function.Injective (burnsideF48t_u52Ob' ω) := by
  obtain ⟨-, -, -, -, -, hL, hLd, -⟩ := burnsideF48t_u52_ptln
  have hLmem : ∀ l < 297, burnsideF48t_u52LnPts[l]! ∈ burnsideF48t_u52LnPts := fun l hl => by
    rw [getElem!_pos _ l (by rw [burnsideF48t_u52_ptln.2.1]; exact hl)]
    exact Array.getElem_mem _
  have hLlt : ∀ l < 297, ∀ p ∈ burnsideF48t_u52LnPts[l]!, p < 165 := fun l hl p hp =>
    (hL _ (hLmem l hl)).2.1 p hp
  have hsub : ∀ l l' : ℕ, l < 297 → l' < 297 →
      {w | ∃ p ∈ burnsideF48t_u52LnPts[l]!, w ∈ burnsideF48t_u52ObPt ω p} =
        {w | ∃ p ∈ burnsideF48t_u52LnPts[l']!, w ∈ burnsideF48t_u52ObPt ω p} →
      ∀ p ∈ burnsideF48t_u52LnPts[l]!, p ∈ burnsideF48t_u52LnPts[l']! := by
    intro l l' hl hl' he p hp
    have hv : burnsideF48t_u52dv ω (burnsideF48t_u52Pt ())[p]! ∈
        {w | ∃ p ∈ burnsideF48t_u52LnPts[l']!, w ∈ burnsideF48t_u52ObPt ω p} := by
      rw [← he]
      exact ⟨p, hp, burnsideF48t_u52_mem_ObPt p⟩
    obtain ⟨q, hq, hpq⟩ := hv
    rw [burnsideF48t_u52_ObPt_eq hK h2 hω (hLlt l hl p hp) (hLlt l' hl' q hq) hpq]
    exact hq
  have hpl : ∀ (i l : ℕ), i < 165 → l < 297 → burnsideF48t_u52ObPt ω i ≠
      {w | ∃ p ∈ burnsideF48t_u52LnPts[l]!, w ∈ burnsideF48t_u52ObPt ω p} := by
    intro i l hi hl he
    obtain ⟨h5, -, hd⟩ := hL _ (hLmem l hl)
    have hpt : ∀ a < 5, (burnsideF48t_u52LnPts[l]!)[a]! = i := by
      intro a ha
      have hpa : (burnsideF48t_u52LnPts[l]!)[a]! ∈ burnsideF48t_u52LnPts[l]! := by
        rw [getElem!_pos _ a (by rw [h5]; exact ha)]
        exact Array.getElem_mem _
      have hv : burnsideF48t_u52dv ω (burnsideF48t_u52Pt ())[(burnsideF48t_u52LnPts[l]!)[a]!]! ∈
          burnsideF48t_u52ObPt ω i := by
        rw [he]
        exact ⟨_, hpa, burnsideF48t_u52_mem_ObPt _⟩
      exact burnsideF48t_u52_ObPt_eq hK h2 hω (hLlt l hl _ hpa) hi hv
    exact hd 0 (by norm_num) 1 (by norm_num) (by norm_num)
      ((hpt 0 (by norm_num)).trans (hpt 1 (by norm_num)).symm)
  intro o o' h
  simp only [burnsideF48t_u52Ob'] at h
  by_cases ho : (o : ℕ) < 165 <;> by_cases ho' : (o' : ℕ) < 165 <;>
    simp only [ho, ho', if_true, if_false] at h
  · apply Fin.ext
    exact burnsideF48t_u52_ObPt_eq hK h2 hω ho ho' (h ▸ burnsideF48t_u52_mem_ObPt _)
  · exact absurd h (hpl o ((o' : ℕ) - 165) ho (by omega))
  · exact absurd h.symm (hpl o' ((o : ℕ) - 165) ho' (by omega))
  · apply Fin.ext
    by_contra hne
    have hne' : (o : ℕ) - 165 ≠ (o' : ℕ) - 165 := by omega
    obtain ⟨p, hp, hn⟩ := hLd ((o : ℕ) - 165) (by omega) ((o' : ℕ) - 165) (by omega) hne'
    exact hn (hsub _ _ (by omega) (by omega) h p hp)


theorem burnsideF48t_u52_RGen_smul_pt (h2 : (2 : K) = 0) (hω : ω ^ 2 = ω + 1) (bar : K →+* K)
    (hbar : ∀ c, bar c = c ^ 2) {k : ℕ} (hk : k < 6) {i : ℕ} (hi : i < 165) :
    burnsideF48t_u52RGen ω bar k • burnsideF48t_u52ObPt ω i =
      burnsideF48t_u52ObPt ω ((burnsideF48t_u52Gens ())[k]!)[i]! := by
  have hsq := burnsideF48t_trans_sq bar h2 (burnsideF48t_u52_iso' h2 hω bar hbar hk)
  have hus := (burnsideF48t_u52_U' hk).1
  obtain ⟨hlt, l, hl, he⟩ := burnsideF48t_u52_ptln.2.2.2.2.2.2.2.1 k hk i hi
  have hl4 : l < 4 := by
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
    omega
  have hl0 : burnsideF48t_gf4D ω l ≠ 0 := by
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> simp only [burnsideF48t_gf4D] <;> norm_num <;>
      intro h0 <;> grind
  have hact : burnsideF48t_u52RGen ω bar k • burnsideF48t_u52dv ω (burnsideF48t_u52Pt ())[i]! =
      burnsideF48t_gf4D ω l •
        burnsideF48t_u52dv ω (burnsideF48t_u52Pt ())[((burnsideF48t_u52Gens ())[k]!)[i]!]! := by
    rw [Units.smul_def, Matrix.smul_eq_mulVec, burnsideF48t_u52RGen,
      burnsideF48t_coe_transU bar hsq,
      ← burnsideF48t_u52_dv_TV h2 hω bar hbar hus (burnsideF48t_u52_pt_small hi).2, he,
      burnsideF48t_u52_dv_scale h2 hω hl4 (burnsideF48t_u52_pt_small hlt).2]
  ext w
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨v, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨c * burnsideF48t_gf4D ω l, mul_ne_zero hc hl0, ?_⟩
    rw [smul_comm, hact, smul_smul]
  · rintro ⟨c', hc', rfl⟩
    refine ⟨(c' / burnsideF48t_gf4D ω l) • burnsideF48t_u52dv ω (burnsideF48t_u52Pt ())[i]!,
      ⟨c' / burnsideF48t_gf4D ω l, div_ne_zero hc' hl0, rfl⟩, ?_⟩
    rw [smul_comm, hact, smul_smul, div_mul_cancel₀ _ hl0]

theorem burnsideF48t_u52_RGen_smul' (hK : Nat.card K = 4) (h2 : (2 : K) = 0)
    (hω : ω ^ 2 = ω + 1) (bar : K →+* K) (hbar : ∀ c, bar c = c ^ 2) {k : ℕ} (hk : k < 6)
    (o : Fin 462) :
    burnsideF48t_u52RGen ω bar k • burnsideF48t_u52Ob' ω o =
      burnsideF48t_u52Ob' ω (burnsideF48t_u52γ k o) := by
  have hγ : ((burnsideF48t_u52γ k o : Fin 462) : ℕ) = ((burnsideF48t_u52Gens ())[k]!)[(o : ℕ)]! :=
    ((burnsideF48t_u52_prep_γ hk).1 o).symm
  obtain ⟨-, -, -, -, -, hL, -, hpt, hln⟩ := burnsideF48t_u52_ptln
  by_cases ho : (o : ℕ) < 165
  · have ht := (hpt k hk o ho).1
    simp only [burnsideF48t_u52Ob', ho, if_true, hγ, ht]
    exact burnsideF48t_u52_RGen_smul_pt h2 hω bar hbar hk ho
  · obtain ⟨ht1, -, hf, hb⟩ := hln k hk ((o : ℕ) - 165) (by omega)
    have e165 : 165 + ((o : ℕ) - 165) = o := by omega
    rw [e165] at ht1 hf hb
    have ht' : ¬ ((burnsideF48t_u52Gens ())[k]!)[(o : ℕ)]! < 165 := by omega
    simp only [burnsideF48t_u52Ob', hγ, ho, ht', if_false]
    have hLmem : burnsideF48t_u52LnPts[(o : ℕ) - 165]! ∈ burnsideF48t_u52LnPts := by
      rw [getElem!_pos _ _ (by rw [burnsideF48t_u52_ptln.2.1]; omega)]
      exact Array.getElem_mem _
    have hlt := (hL _ hLmem).2.1
    ext w
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨v, ⟨p, hp, hv⟩, rfl⟩
      refine ⟨((burnsideF48t_u52Gens ())[k]!)[p]!, hf p hp, ?_⟩
      rw [← burnsideF48t_u52_RGen_smul_pt h2 hω bar hbar hk (hlt p hp)]
      exact Set.smul_mem_smul_set hv
    · rintro ⟨q, hq, hw⟩
      obtain ⟨p, hp, rfl⟩ := hb q hq
      rw [← burnsideF48t_u52_RGen_smul_pt h2 hω bar hbar hk (hlt p hp), Set.mem_smul_set] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      exact ⟨v, ⟨p, hp, hv⟩, rfl⟩

theorem burnsideF48t_u52_R_preserves' (hK : Nat.card K = 4) (h2 : (2 : K) = 0)
    (hω : ω ^ 2 = ω + 1) (bar : K →+* K) (hbar : ∀ c, bar c = c ^ 2) :
    ∀ g ∈ burnsideF48t_u52R ω bar, ∀ o, ∃ o',
      g • burnsideF48t_u52Ob' ω o = burnsideF48t_u52Ob' ω o' := by
  refine burnsideF48t_closure_preserves (burnsideF48t_u52_Ob'_injective hK h2 hω) ?_
  rintro _ ⟨k, rfl⟩ o
  exact ⟨_, burnsideF48t_u52_RGen_smul' hK h2 hω bar hbar k.2 o⟩

@[expose] noncomputable def burnsideF48t_u52ρ' (hK : Nat.card K = 4) (h2 : (2 : K) = 0)
    (hω : ω ^ 2 = ω + 1) (bar : K →+* K) (hbar : ∀ c, bar c = c ^ 2) :
    ↥(burnsideF48t_u52R ω bar) →* Equiv.Perm (Fin 462) :=
  burnsideF48t_resHom (burnsideF48t_u52_Ob'_injective hK h2 hω)
    (burnsideF48t_u52_R_preserves' hK h2 hω bar hbar)

theorem burnsideF48t_u52_ρ'_RGen (hK : Nat.card K = 4) (h2 : (2 : K) = 0) (hω : ω ^ 2 = ω + 1)
    (bar : K →+* K) (hbar : ∀ c, bar c = c ^ 2) {k : ℕ} (hk : k < 6) :
    burnsideF48t_u52ρ' hK h2 hω bar hbar ⟨burnsideF48t_u52RGen ω bar k,
      burnsideF48t_u52_RGen_mem bar hk⟩ = burnsideF48t_u52γ k :=
  Equiv.ext fun o => burnsideF48t_u52_Ob'_injective hK h2 hω (by
    rw [burnsideF48t_u52ρ', burnsideF48t_resHom_spec (P := burnsideF48t_u52Ob' ω)
      (burnsideF48t_u52_Ob'_injective hK h2 hω) (burnsideF48t_u52_R_preserves' hK h2 hω bar hbar),
      burnsideF48t_u52_RGen_smul' hK h2 hω bar hbar hk])

theorem burnsideF48t_u52_ρ'_range (hK : Nat.card K = 4) (h2 : (2 : K) = 0) (hω : ω ^ 2 = ω + 1)
    (bar : K →+* K) (hbar : ∀ c, bar c = c ^ 2) :
    (burnsideF48t_u52ρ' hK h2 hω bar hbar).range = burnsideF48t_u52X := by
  apply le_antisymm
  · have htop : (⊤ : Subgroup ↥(burnsideF48t_u52R ω bar)) = Subgroup.closure
        (Subtype.val ⁻¹' (Set.range fun k : Fin 6 => burnsideF48t_u52RGen ω bar k)) :=
      Subgroup.closure_closure_coe_preimage.symm
    rw [MonoidHom.range_eq_map, htop, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨⟨s, hs⟩, ⟨k, hks⟩, rfl⟩
    have e : (⟨s, hs⟩ : ↥(burnsideF48t_u52R ω bar)) =
        ⟨burnsideF48t_u52RGen ω bar k, burnsideF48t_u52_RGen_mem bar k.2⟩ := Subtype.ext hks.symm
    rw [SetLike.mem_coe, e, burnsideF48t_u52_ρ'_RGen hK h2 hω bar hbar k.2]
    exact burnsideF48t_u52_γ_mem k.2
  · rw [burnsideF48t_u52_X_eq, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    have hk : (k : ℕ) < 6 := burnsideF48t_u52_inv.2.2.1 ▸ k.2
    exact ⟨⟨burnsideF48t_u52RGen ω bar k, burnsideF48t_u52_RGen_mem bar hk⟩,
      burnsideF48t_u52_ρ'_RGen hK h2 hω bar hbar hk⟩

end PtLn

section Iso

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

theorem burnsideF48t_u52_SU_equiv_X' (h : UnitaryFieldData 2 1 K) (hK : Nat.card K = 4)
    {ω : K} (h2 : (2 : K) = 0) (hω : ω ^ 2 = ω + 1) :
    Nonempty (↥(StatedSU 5 (2 ^ 1) K) ≃* ↥burnsideF48t_u52X) := by
  have hbar := burnsideF48t_u52_bar h
  set ρ := burnsideF48t_u52ρ' hK h2 hω h.bar hbar with hρ
  have hRle : burnsideF48t_u52R ω h.bar ≤ StatedSU 5 (2 ^ 1) K := by
    rw [burnsideF48t_u52R, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact burnsideF48t_transU_mem h (burnsideF48t_u52_iso' h2 hω h.bar hbar k.2)
  have hSUfin : Finite ↥(StatedSU 5 (2 ^ 1) K) :=
    Nat.finite_of_card_ne_zero (by rw [burnsideF48t_u52_card_SU h]; norm_num)
  have hrange := burnsideF48t_u52_ρ'_range hK h2 hω h.bar hbar
  have hRfin : Finite ↥(burnsideF48t_u52R ω h.bar) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hRle)
  have hcardR : Nat.card ↥(burnsideF48t_u52R ω h.bar) ≤ 13685760 := by
    rw [← burnsideF48t_u52_card_SU h]
    exact Subgroup.card_le_of_le hRle
  have hcardX : 13685760 ≤ Nat.card ↥(burnsideF48t_u52R ω h.bar) := by
    rw [← burnsideF48t_u52_card_X, ← hrange]
    exact Nat.card_le_card_of_surjective _ ρ.rangeRestrict_surjective
  have hRSU : burnsideF48t_u52R ω h.bar = StatedSU 5 (2 ^ 1) K :=
    Subgroup.eq_of_le_of_card_ge hRle (by rw [burnsideF48t_u52_card_SU h]; exact hcardX)
  have hbij : Function.Bijective ρ.rangeRestrict := by
    refine ρ.rangeRestrict_surjective.bijective_of_nat_card_le ?_
    rw [hrange, burnsideF48t_u52_card_X]
    exact hcardR
  have hinj : Function.Injective ρ := fun x y hxy => hbij.1 (Subtype.ext hxy)
  exact ⟨(MulEquiv.subgroupCongr hRSU.symm).trans ((MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr hrange))⟩

theorem burnsideF48t_u52_equiv_X' {H : Type} [Group H] (hH : ChF.IsGenLie H .U5 2 1) :
    Nonempty (↥burnsideF48t_u52X ≃* H) := by
  obtain ⟨-, -, K, fK, finK, hK, ⟨e⟩⟩ := hH
  letI := fK
  haveI := finK
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  obtain ⟨h2, ω, hω⟩ := burnsideF48t_gf4_exists_ω hK4
  have h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hK4]; norm_num⟩
  obtain ⟨ψ⟩ := burnsideF48t_u52_SU_equiv_X' h hK4 h2 hω
  let e₁ : StatedProj (StatedSU 5 (2 ^ 1) K) ≃* ↥(StatedSU 5 (2 ^ 1) K) :=
    (QuotientGroup.quotientMulEquivOfEq (burnsideF48t_u52_scalars h)).trans QuotientGroup.quotientBot
  exact ⟨(ψ.symm.trans e₁.symm).trans e.symm⟩

end Iso

end CFSG.ASVolI

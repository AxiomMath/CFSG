module

public import CFSG.Quasithin.H13.A5Final
public import CFSG.Quasithin.H13.A5S136a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

theorem D_pact_E12 : ∀ σ : Equiv.Perm (Fin 5), InD σ →
    pact σ E12 = E12 ∨ pact σ E12 = pact pb E12 := by
  decide +kernel

theorem pb_E12_ne : pact pb E12 ≠ E12 := by decide +kernel

theorem InK4_pb : InK4 pb := Or.inr (Or.inr (Or.inl rfl))

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem v12_ne_one : S.v12 ≠ 1 := by
  intro h
  have h1 : (⟨S.v12, S.v12_mem_V⟩ : ↥V) = 1 := Subtype.ext h
  have h2 := S.psi_v12
  rw [h1, map_one] at h2
  exact E12_ne_one h2.symm

theorem omegaOneCenter_inf_centralizer_L (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7) :
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  by_contra hC
  set C := quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) with hCdef
  have hZT : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) := by
    rw [quasithinOmegaOneCenter, Subgroup.closure_le]
    exact fun x hx => hx.1
  have hCT : C ≤ T := inf_le_left.trans (hZT.trans inf_le_left)
  have hCp : IsPGroup 2 C := S.isPGroup_T.to_le hCT
  have hLC : L ≤ Subgroup.normalizer (C : Set G) := by
    intro l hl
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
    · have hxl : l * x = x * l :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 l hl)
      have e : l * x * l⁻¹ = x := by rw [hxl]; group
      rw [e]
      exact hx
    · have hxl : l * x = x * l :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 l hl)
      have e : l⁻¹ * x * l = x := by
        calc l⁻¹ * x * l = l⁻¹ * (x * l) := by group
          _ = l⁻¹ * (l * x) := by rw [hxl]
          _ = x := by group
      rw [e]
      exact hx
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := by
    intro t ht
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
    · have hxt : t * x = x * t :=
        (Subgroup.mem_centralizer_iff.mp (hZT (Subgroup.mem_inf.mp hx).1).2 t ht)
      have e : t * x * t⁻¹ = x := by rw [hxt]; group
      rw [e]
      exact hx
    · have hxt : t * x = x * t :=
        (Subgroup.mem_centralizer_iff.mp (hZT (Subgroup.mem_inf.mp hx).1).2 t ht)
      have e : t⁻¹ * x * t = x := by
        calc t⁻¹ * x * t = t⁻¹ * (x * t) := by group
          _ = t⁻¹ * (t * x) := by rw [hxt]
          _ = x := by group
      rw [e]
      exact hx
  have hloc : IsTwoLocal (Subgroup.normalizer (C : Set G)) := ⟨C, hC, hCp, rfl⟩
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge hloc
  have hM'eq := S.uniqueM.2 M' ⟨hM', (sup_le hLC hTC).trans hM'le⟩
  have hNM : Subgroup.normalizer (C : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    hM'eq ▸ hM'le
  obtain ⟨-, -, ⟨H, hH⟩, -, -⟩ := (h331 G T S.h13.simple S.h13.nonabelian S.h13.qtke
    S.h13.sylow).2 L S.maximal S.isQuasisimple_L
  rw [S.conjClosure_L_T] at hH
  have hHZ := h1327 G T L V S H hH
  apply hH.2.1
  refine le_trans ?_ hNM
  intro h hh
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  exact (Subgroup.mem_centralizer_iff.mp (hHZ hh) c (Subgroup.mem_inf.mp hc).1)

theorem index_Tv : ((T ⊓ Subgroup.centralizer ({S.v12} : Set G)).subgroupOf T).index = 2 := by
  have hfix : ∀ (t : G) (ht : t ∈ T), t ∈ Subgroup.centralizer ({S.v12} : Set G) ↔
      pact (S.frame.ρ ⟨t, S.frame.T_le ht⟩) E12 = E12 := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff, ← S.psi_v12,
      ← S.conj_eq_iff ⟨t, S.frame.T_le ht⟩ ⟨S.v12, S.v12_mem_V⟩]
    constructor
    · intro h
      show t * S.v12 * t⁻¹ = S.v12
      rw [h]
      group
    · intro h
      have h' : t * S.v12 * t⁻¹ = S.v12 := h
      calc t * S.v12 = t * S.v12 * t⁻¹ * t := by group
        _ = S.v12 * t := by rw [h']
  obtain ⟨g₀, hg₀T, hg₀σ⟩ := S.frame.K4_T pb InK4_pb
  rw [Subgroup.index_eq_two_iff_exists_notMem_and']
  refine ⟨⟨g₀, hg₀T⟩, fun hm => ?_, fun b => ?_⟩
  · have hm' := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hm)).2
    rw [hfix _ hg₀T] at hm'
    have : (⟨(g₀ : G), S.frame.T_le hg₀T⟩ : ↥(Subgroup.normalizer (V : Set G))) = g₀ :=
      Subtype.ext rfl
    rw [this, hg₀σ] at hm'
    exact pb_E12_ne hm'
  · have hbT : (b : G) ∈ T := b.2
    have hmul : ((⟨(g₀ : G), hg₀T⟩ : ↥T) * b : ↥T) = ⟨(g₀ : G) * b, T.mul_mem hg₀T hbT⟩ := rfl
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hmul]
    simp only [Subgroup.mem_inf]
    rw [hfix _ hbT, hfix _ (T.mul_mem hg₀T hbT)]
    have hρ : S.frame.ρ ⟨(g₀ : G) * b, S.frame.T_le (T.mul_mem hg₀T hbT)⟩ =
        S.frame.ρ g₀ * S.frame.ρ ⟨b, S.frame.T_le hbT⟩ := by
      rw [← map_mul]
      rfl
    rw [hρ, hg₀σ, map_mul, MulAut.mul_apply]
    rcases D_pact_E12 _ (S.frame.T_D ⟨b, S.frame.T_le hbT⟩ hbT) with h | h
    · right
      exact ⟨hbT, h⟩
    · left
      refine ⟨T.mul_mem hg₀T hbT, ?_⟩
      rw [h, ← MulAut.mul_apply, ← map_mul]
      have : pb * pb = 1 := by decide
      rw [this, map_one, MulAut.one_apply]

end Setting

end CFSG.Quasithin.H13.A5

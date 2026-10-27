module

public import CFSG.Quasithin.MS93.S32Basic
public import CFSG.Quasithin.MS93.Sec2Three

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section Internal

@[expose] def conjClosureIn (M : Subgroup G) (x : G) : Subgroup G :=
  Subgroup.closure {y | ∃ g ∈ M, g * x * g⁻¹ = y}

omit [Finite G] in
theorem conjClosureIn_le {x : G} (hx : x ∈ M) : conjClosureIn M x ≤ M := by
  rw [conjClosureIn, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact M.mul_mem (M.mul_mem hg hx) (M.inv_mem hg)

omit [Finite G] in
theorem mem_conjClosureIn (x : G) : x ∈ conjClosureIn M x :=
  Subgroup.subset_closure ⟨1, M.one_mem, by group⟩

omit [Finite G] in
theorem le_normalizer_conjClosureIn (x : G) :
    M ≤ Subgroup.normalizer (conjClosureIn M x : Set G) := by
  have key : ∀ m ∈ M, ∀ y ∈ conjClosureIn M x, m * y * m⁻¹ ∈ conjClosureIn M x := by
    intro m hm y hy
    have hle : conjClosureIn M x ≤ (conjClosureIn M x).comap (MulAut.conj m).toMonoidHom := by
      rw [conjClosureIn, Subgroup.closure_le]
      rintro _ ⟨g, hg, rfl⟩
      refine Subgroup.subset_closure ⟨m * g, M.mul_mem hm hg, ?_⟩
      simp [mul_assoc]
    exact hle hy
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key m hm y, fun hy => ?_⟩
  have := key m⁻¹ (M.inv_mem hm) _ hy
  simpa [mul_assoc] using this

theorem PUHyp.le_conjClosureIn (h : PUHyp M T L) {x : G} (hxT : x ∈ T)
    (hxQ : x ∉ pCoreOf 2 M) : L ≤ conjClosureIn M x := by
  by_contra hL
  apply hxQ
  obtain ⟨e, he⟩ := h.isPGroup ⟨x, hxT⟩
  refine h.mem_pCoreOf_of_rel (le_normalizer_conjClosureIn x) hL (h.le hxT)
    ⟨e, by simpa using congrArg Subtype.val he⟩ fun l hl => ?_
  have h1 : l * x⁻¹ * l⁻¹ ∈ conjClosureIn M x := by
    have : l * x * l⁻¹ ∈ conjClosureIn M x :=
      Subgroup.subset_closure ⟨l, h.L_le hl, rfl⟩
    have e : l * x⁻¹ * l⁻¹ = (l * x * l⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ this
  have e : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem _ (mem_conjClosureIn x) h1

theorem PUHyp.eq_conjClosureIn_sup (h : PUHyp M T L) {x : G} (hxT : x ∈ T)
    (hxQ : x ∉ pCoreOf 2 M) : M = conjClosureIn M x ⊔ T := by
  refine le_antisymm ?_ (sup_le (conjClosureIn_le (h.le hxT)) h.le)
  calc M = L ⊔ T := h.eq_sup
    _ ≤ conjClosureIn M x ⊔ T := sup_le_sup_right (h.le_conjClosureIn hxT hxQ) T

end Internal

section Amalgam

omit [Finite G] in
theorem imM_conjClosureIn_le (hTM : T ≤ M) (a : ↥M) :
    imM hTM (conjClosureIn M a) ≤ Subgroup.closure
      {y | ∃ k ∈ stab (puAmalgam hTM) (baseA _), k * (puAmalgam hTM).ofA a * k⁻¹ = y} := by
  set f := (puAmalgam hTM).ofA
  have key : ∀ c (hc : c ∈ conjClosureIn M a), ∀ hcM : c ∈ M,
      f ⟨c, hcM⟩ ∈ Subgroup.closure
        {y | ∃ k ∈ stab (puAmalgam hTM) (baseA _), k * f a * k⁻¹ = y} := by
    intro c hc
    induction hc using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨g, hg, rfl⟩ := hy
      intro hcM
      refine Subgroup.subset_closure ⟨f ⟨g, hg⟩, ?_, ?_⟩
      · rw [puAmalgam.stab_baseA]
        exact ⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
      · rw [← map_inv, ← map_mul, ← map_mul]
        rfl
    | one =>
      intro hcM
      have e : (⟨1, hcM⟩ : ↥M) = 1 := rfl
      rw [e, map_one]
      exact Subgroup.one_mem _
    | mul y z hy hz ihy ihz =>
      intro hcM
      have hyM := conjClosureIn_le a.2 hy
      have hzM := conjClosureIn_le a.2 hz
      have e : (⟨y * z, hcM⟩ : ↥M) = ⟨y, hyM⟩ * ⟨z, hzM⟩ := rfl
      rw [e, map_mul]
      exact Subgroup.mul_mem _ (ihy hyM) (ihz hzM)
    | inv y hy ihy =>
      intro hcM
      have hyM := conjClosureIn_le a.2 hy
      have e : (⟨y⁻¹, hcM⟩ : ↥M) = (⟨y, hyM⟩ : ↥M)⁻¹ := rfl
      rw [e, map_inv]
      exact Subgroup.inv_mem _ (ihy hyM)
  rintro _ ⟨⟨c, hcM⟩, hc, rfl⟩
  exact key c (Subgroup.mem_subgroupOf.mp hc) hcM

theorem PUHyp.gen23At_base (h : PUHyp M T L) :
    Gen23At (puAmalgam h.le) (baseA _) (baseB _) := by
  intro x hx hxQ
  rw [puAmalgam.qv_baseB] at hx ⊢
  rw [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le] at hxQ
  obtain ⟨a, ha, rfl⟩ := hx
  have haT : (a : G) ∈ T := Subgroup.mem_subgroupOf.mp ha
  have haQ : (a : G) ∉ pCoreOf 2 M := fun hq => hxQ ⟨a, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · have hM := h.eq_conjClosureIn_sup haT haQ
    have hsub : M.subgroupOf M =
        (conjClosureIn M a).subgroupOf M ⊔ T.subgroupOf M := by
      rw [← Subgroup.subgroupOf_sup (conjClosureIn_le a.2) h.le, ← hM]
    have h1 : stab (puAmalgam h.le) (baseA _) =
        imM h.le (conjClosureIn M a) ⊔ imM h.le T := by
      rw [puAmalgam.stab_baseA]
      show (M.subgroupOf M).map _ = ((conjClosureIn M a).subgroupOf M).map _ ⊔
        (T.subgroupOf M).map _
      rw [hsub, Subgroup.map_sup]
    exact h1.le.trans (sup_le_sup_right (imM_conjClosureIn_le h.le a) _)
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    refine (stab _ _).mul_mem ((stab _ _).mul_mem hk ?_) ((stab _ _).inv_mem hk)
    rw [puAmalgam.stab_baseA]
    exact ⟨a, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  · rw [puAmalgam.stab_baseA]
    exact imM_mono h.le h.le

theorem PUHyp.gen23At (h : PUHyp M T L) {γ ρ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hγρ : (puAmalgam h.le).treeGraph.Adj γ ρ) : Gen23At (puAmalgam h.le) γ ρ := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx _ (PU.isMVtx_baseA _)
    (adj_baseA_baseB _) hγ hγρ
  exact gen23At_smul _ h.gen23At_base g

omit [Finite G] in
theorem closure_conj_stab_map {X : GoldAmalgam ↥M ↥T (Hol ↥T)} (g x : X.Universal)
    (δ : Vtx X) :
    (Subgroup.closure {y | ∃ k ∈ stab X δ, k * x * k⁻¹ = y}).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure {y | ∃ k ∈ stab X (g • δ), k * (g * x * g⁻¹) * k⁻¹ = y} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨g * k * g⁻¹, ?_, ?_⟩
    · rw [mem_stab_smul]
      simpa [mul_assoc] using hk
    · simp [mul_assoc]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(g⁻¹ * k * g) * x * (g⁻¹ * k * g)⁻¹, ⟨g⁻¹ * k * g, (mem_stab_smul X).mp hk, rfl⟩, ?_⟩
    simp [mul_assoc]

theorem PUHyp.L_subgroupOf_normal (h : PUHyp M T L) : (L.subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer

theorem PUHyp.puTrans_L_le_closure (h : PUHyp M T L) {γ ρ : Vtx (puAmalgam h.le)}
    (hγ : IsMVtx _ γ) (hγρ : (puAmalgam h.le).treeGraph.Adj γ ρ) {x : (puAmalgam h.le).Universal}
    (hx : x ∈ Qv _ ρ) (hxQ : x ∉ Qv _ γ) :
    puTrans h.le L γ ≤ Subgroup.closure {y | ∃ k ∈ stab _ γ, k * x * k⁻¹ = y} := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx _ (PU.isMVtx_baseA _)
    (adj_baseA_baseB _) hγ hγρ
  rw [qv_smul, mem_map_conj, puAmalgam.qv_baseB] at hx
  rw [qv_smul, mem_map_conj, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le] at hxQ
  obtain ⟨a, ha, he⟩ := hx
  have haT : (a : G) ∈ T := Subgroup.mem_subgroupOf.mp ha
  have haQ : (a : G) ∉ pCoreOf 2 M := fun hq =>
    hxQ ⟨a, Subgroup.mem_subgroupOf.mpr hq, he⟩
  have hbase : imM h.le L ≤ Subgroup.closure
      {y | ∃ k ∈ stab (puAmalgam h.le) (baseA _), k * (puAmalgam h.le).ofA a * k⁻¹ = y} :=
    (imM_mono h.le (h.le_conjClosureIn haT haQ)).trans (imM_conjClosureIn_le h.le a)
  rw [puTrans_smul_baseA h.L_subgroupOf_normal]
  have hx' : g * (puAmalgam h.le).ofA a * g⁻¹ = x := by
    rw [he]
    group
  rw [← hx', ← closure_conj_stab_map]
  exact Subgroup.map_mono hbase

end Amalgam

end CFSG.Quasithin.MS93

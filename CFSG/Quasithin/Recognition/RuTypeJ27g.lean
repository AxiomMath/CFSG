module

public import CFSG.Quasithin.Recognition.RuTypeJ27b

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem nonempty_NQ_alt6
    : Nonempty (M.NQ ≃* alternatingGroup (Fin 6)) := by
  have hinv : ∀ u v : M.NQ, orderOf u = 2 → orderOf v = 2 → IsConj u v :=
    fun u v hu hv => (M.isConj_zQ hu).symm.trans (M.isConj_zQ hv)
  have hinvX : ∀ x : M.XQ, x ^ 2 = 1 → x ∈ M.NQ := fun x hx => M.mem_NQ_of_sq hx
  rcases I4.lemma_I_4_1_two M.NQ hinv M.orderOf_zQ M.nonempty_centralizer_zQ with h | h
  · obtain ⟨e⟩ := h
    exact (false_of_psl32 M.NQ M.NQ_index hinvX e).elim
  · exact h

instance isSimpleGroup_NQ
    : IsSimpleGroup M.NQ := by
  obtain ⟨e⟩ := M.nonempty_NQ_alt6
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have : Nontrivial M.NQ := e.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem NX_le_ker
    (W : M.GB →* Multiplicative (ZMod 2)) (hW2 : ∀ y : M.GB, y ^ 2 = 1 → W y = 1)
    (hWB : ∀ y : M.GB, (y : G) ∈ M.B → W y = 1) : M.NX ≤ W.ker := by
  classical
  set K := W.ker
  have hBK : M.B.subgroupOf M.GB ≤ K := fun y hy => hWB y (Subgroup.mem_subgroupOf.mp hy)
  set Kb := K.map (QuotientGroup.mk' (M.B.subgroupOf M.GB))
  have hKbn : Kb.Normal := Subgroup.Normal.map (MonoidHom.normal_ker W) _
    (QuotientGroup.mk'_surjective _)
  have hKinv : ∀ u : M.XQ, u ^ 2 = 1 → u ∈ Kb := by
    intro u hu
    obtain ⟨x, hx2, rfl⟩ := M.exists_lift_sq hu
    exact ⟨x, hW2 x hx2, rfl⟩
  set KN := Kb.comap M.NQ.subtype
  have hKNn : KN.Normal := Subgroup.Normal.comap hKbn _
  have hKNz : M.zQ ∈ KN := by
    show (M.zQ : M.XQ) ∈ Kb
    refine hKinv _ ?_
    have := congrArg Subtype.val (pow_orderOf_eq_one M.zQ)
    rw [M.orderOf_zQ] at this
    simpa using this
  have hKNtop : KN = ⊤ := by
    rcases hKNn.eq_bot_or_eq_top with h | h
    · exfalso
      have : M.zQ = 1 := by
        have := hKNz
        rw [h, Subgroup.mem_bot] at this
        exact this
      have h1 := M.orderOf_zQ
      rw [this, orderOf_one] at h1
      norm_num at h1
    · exact h
  intro x hx
  have hmk : (QuotientGroup.mk x : M.XQ) ∈ Kb := by
    have : (⟨(x : M.XQ), ⟨x, hx, rfl⟩⟩ : M.NQ) ∈ KN := by rw [hKNtop]; exact Subgroup.mem_top _
    exact this
  obtain ⟨k, hk, hkx⟩ := hmk
  have hkx' : (QuotientGroup.mk k : M.XQ) = QuotientGroup.mk x := hkx
  rw [QuotientGroup.eq] at hkx'
  have := mul_mem hk (hBK hkx')
  simpa using this

noncomputable abbrev GP : Subgroup G := Subgroup.normalizer (M.B : Set G)

theorem B_le_GP : M.B ≤ M.GP := Subgroup.le_normalizer

theorem GB_le_GP : M.GB ≤ M.GP := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hc : ∀ c : G, c ∈ M.GB → ∀ b ∈ M.B, c * b * c⁻¹ = b := fun c hc b hb => by
    rw [← (Subgroup.mem_centralizer_iff.mp hc) b hb, mul_inv_cancel_right]
  constructor
  · intro hy; rw [hc x hx y hy]; exact hy
  · intro hy
    have e : y = x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ := by group
    rw [e, hc x⁻¹ (inv_mem hx) _ hy]
    exact hy

theorem conj_mem_B {g x : G} (hg : g ∈ M.GP) (hx : x ∈ M.B) : g * x * g⁻¹ ∈ M.B :=
  (Subgroup.mem_normalizer_iff.mp hg x).mp hx

theorem conj_mem_GB {g x : G} (hg : g ∈ M.GP) (hx : x ∈ M.GB) : g * x * g⁻¹ ∈ M.GB := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hb' : g⁻¹ * b * g ∈ M.B := by
    have := M.conj_mem_B (inv_mem hg) hb
    rwa [inv_inv] at this
  have hc := (Subgroup.mem_centralizer_iff.mp hx) _ hb'
  calc b * (g * x * g⁻¹) = g * ((g⁻¹ * b * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * b * g)) * g⁻¹ := by rw [hc]
    _ = g * x * g⁻¹ * b := by group

@[expose] noncomputable def conjGB {g : G} (hg : g ∈ M.GP) : M.GB →* M.GB where
  toFun x := ⟨g * x * g⁻¹, M.conj_mem_GB hg x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

noncomputable abbrev NXG : Subgroup G := M.NX.map M.GB.subtype

end RuDataM

end CFSG.Quasithin.RuType

module

public import CFSG.Foundations.Basic
public import CFSG.Assembly.Defs
import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

open CFSG

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_pCoreOf (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 J : Set G) := by
  have hmap : ∀ g ∈ Subgroup.normalizer (J : Set G), ∀ x ∈ CFSG.Open.pCoreOf 2 J,
      g * x * g⁻¹ ∈ CFSG.Open.pCoreOf 2 J := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := hx
    let φ : J ≃* J := (MulAut.conj g).subgroupMap J |>.trans
      (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg))
    have hfix := (inferInstance : (pCore 2 ↥J).Characteristic).fixed φ
    have hy' : φ y ∈ pCore 2 ↥J := by
      have : y ∈ (pCore 2 ↥J).comap φ.toMonoidHom := by rw [hfix]; exact hy
      exact Subgroup.mem_comap.mp this
    exact ⟨φ y, hy', rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hmap g hg x hx, fun hx => ?_⟩
  have := hmap g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

theorem le_normalizer_pCoreOf (M : Subgroup G) :
    M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) := fun _ hm =>
  normalizer_le_normalizer_pCoreOf M (Subgroup.le_normalizer hm)

theorem isPGroup_pCoreOf (M : Subgroup G) : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) := by
  have h : IsPGroup 2 (pCore 2 ↥M) := pCore_isPGroup
  exact h.map M.subtype

theorem normalizer_eq_of_isMaximalTwoLocal [Finite G] {M : Subgroup G}
    (hM : CFSG.IsMaximalTwoLocal M) : Subgroup.normalizer (M : Set G) = M := by
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  have hQ1 : Q ≠ ⊥ := by
    intro h
    apply CFSG.CGT.PushingUp.pCore_ne_bot_of_isPLocal hM.1
    rw [eq_bot_iff]
    intro x hx
    have : (x : G) ∈ Q := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hloc : IsPLocal 2 (Subgroup.normalizer (Q : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup (isPGroup_pCoreOf M) hQ1
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf M
  have hNQ : Subgroup.normalizer (Q : Set G) = M := by
    by_contra hne
    exact hM.2 _ (lt_of_le_of_ne hMQ (Ne.symm hne)) hloc
  refine le_antisymm ?_ Subgroup.le_normalizer
  calc Subgroup.normalizer (M : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
        normalizer_le_normalizer_pCoreOf M
    _ = M := hNQ

theorem map_conj_le_centralizer {J V : Subgroup G} (hVC : V ≤ Subgroup.centralizer (J : Set G))
    (g : G) : J.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rintro _ ⟨j, hj, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨v, hv, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.mp (hVC hv) j hj
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * v * g⁻¹ * (g * j * g⁻¹) = g * (v * j) * g⁻¹ := by group
    _ = g * (j * v) * g⁻¹ := by rw [hc]
    _ = g * j * g⁻¹ * (g * v * g⁻¹) := by group

theorem inf_conj_eq_bot_of_unique [Finite G] {M J V : Subgroup G} (hM : CFSG.IsMaximalTwoLocal M)
    (huniq : ∀ M' : Subgroup G, CFSG.IsMaximalTwoLocal M' → J ≤ M' → M' = M)
    (hV2 : IsPGroup 2 V) (hVC : V ≤ Subgroup.centralizer (J : Set G)) {g : G} (hg : g ∉ M) :
    V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ := by
  by_contra hX
  set X := V ⊓ V.map (MulAut.conj g).toMonoidHom with hXdef
  have hX2 : IsPGroup 2 X := hV2.to_le inf_le_left
  have hloc := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hX2 hX
  obtain ⟨M', hNM', hM'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hcn : Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hJX : J ≤ Subgroup.centralizer (X : Set G) :=
    Subgroup.le_centralizer_iff.mp (le_trans inf_le_left hVC)
  have hM'eq : M' = M := huniq M' hM' ((hJX.trans hcn).trans hNM')
  have hJgX : J.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (X : Set G) :=
    (map_conj_le_centralizer hVC g).trans (Subgroup.centralizer_le inf_le_right)
  have hJgM : J.map (MulAut.conj g).toMonoidHom ≤ M := by
    rw [← hM'eq]
    exact (hJgX.trans hcn).trans hNM'
  have hMg := CFSG.CGT.PushingUp.isMaximalTwoLocal_map_conj hM g⁻¹
  have hJMg : J ≤ M.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro j hj
    refine ⟨g * j * g⁻¹, hJgM ⟨j, hj, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hMeq := huniq _ hMg hJMg
  have hginv : g⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMeq
  apply hg
  rw [← normalizer_eq_of_isMaximalTwoLocal hM]
  simpa using Subgroup.inv_mem _ hginv

theorem isTI_of_unique [Finite G] {M J V : Subgroup G} (hM : CFSG.IsMaximalTwoLocal M)
    (huniq : ∀ M' : Subgroup G, CFSG.IsMaximalTwoLocal M' → J ≤ M' → M' = M)
    (hV2 : IsPGroup 2 V) (hVM : M ≤ Subgroup.normalizer (V : Set G))
    (hVC : V ≤ Subgroup.centralizer (J : Set G)) (g : G) :
    V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨ V ⊓ V.map (MulAut.conj g).toMonoidHom = V := by
  by_cases hg : g ∈ M
  · right
    rw [show V.map (MulAut.conj g).toMonoidHom = V from
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hVM hg), inf_idem]
  · exact Or.inl (inf_conj_eq_bot_of_unique hM huniq hV2 hVC hg)

theorem exists_maximal_normal_elemAbelian [Finite G] (M : Subgroup G) :
    ∃ V : Subgroup G, Maximal (fun W : Subgroup G => W ≤ M ∧
      M ≤ Subgroup.normalizer (W : Set G) ∧ CFSG.Assembly.IsElemAbelian 2 W) V := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let S : Set (Subgroup G) := {W | W ≤ M ∧ M ≤ Subgroup.normalizer (W : Set G) ∧
    CFSG.Assembly.IsElemAbelian 2 W}
  have hbot : (⊥ : Subgroup G) ∈ S := by
    refine ⟨bot_le, fun m _ => ?_, ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [Subgroup.mem_bot]
      constructor
      · rintro rfl
        group
      · intro h
        have : x = m⁻¹ * (m * x * m⁻¹) * m := by group
        rw [this, h]
        group
    · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2]
    · intro x hx
      rw [Subgroup.mem_bot.mp hx, one_pow]
  have hfin : S.Finite := Set.toFinite S
  obtain ⟨V, hVS, hVmax⟩ := Finset.exists_max_image hfin.toFinset (fun W => Nat.card W)
    ⟨⊥, hfin.mem_toFinset.mpr hbot⟩
  rw [Set.Finite.mem_toFinset] at hVS
  refine ⟨V, hVS, fun W hW hVW => ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hVW (hVmax W (hfin.mem_toFinset.mpr hW))).symm ▸ le_rfl

end CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

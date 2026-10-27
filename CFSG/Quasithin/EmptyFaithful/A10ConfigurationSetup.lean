module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationFacts
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Background.CharTwoLocal

public section

namespace CFSG.Quasithin.A10

open CFSG.Open

variable {G : Type*} [Group G]

structure Emb (G : Type*) [Group G] (T M : Subgroup G) where
  ι : Wc →* G
  injective : Function.Injective ι
  range_eq : ι.range = M
  map_Th : Th.map ι = T

open scoped Pointwise

theorem exists_emb [Finite G] {T M : Subgroup G} (hT : quasithinIsSylowTwo T) (hTM : T ≤ M)
    (φ : ↥M ≃* Wc) : Nonempty (Emb G T M) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 (T.subgroupOf M) := hT.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm
  have hTidx : ¬ 2 ∣ (T.subgroupOf M).index := by
    intro h
    apply hT.2
    refine h.trans ?_
    have := Subgroup.relIndex_dvd_index_of_le hTM
    simpa [Subgroup.relIndex] using this
  let PT : Sylow 2 M := hTp.toSylow hTidx
  set S' : Subgroup M := Th.map φ.symm.toMonoidHom with hS'
  have hS'p : IsPGroup 2 S' := Th_isPGroup.map _
  have hcardM : Nat.card M = 1152 := by
    rw [Nat.card_congr φ.toEquiv, card_Wc']
  have hS'card : Nat.card S' = 128 := by
    rw [hS', Subgroup.card_map_of_injective φ.symm.injective, card_Th]
  have hS'idx : ¬ 2 ∣ S'.index := by
    have := Subgroup.card_mul_index S'
    rw [hS'card, hcardM] at this
    have h9 : S'.index = 9 := by omega
    rw [h9]
    decide
  let PS : Sylow 2 M := hS'p.toSylow hS'idx
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M PS PT
  have hmem : ∀ x : M, x ∈ (PS : Subgroup M) → m * x * m⁻¹ ∈ (PT : Subgroup M) := by
    intro x hx
    have : m * x * m⁻¹ ∈ ((m • PS : Sylow 2 M) : Subgroup M) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [hm] at this
  have hmem' : ∀ y : M, y ∈ (PT : Subgroup M) → m⁻¹ * y * m ∈ (PS : Subgroup M) := by
    intro y hy
    have : y ∈ ((m • PS : Sylow 2 M) : Subgroup M) := by rw [hm]; exact hy
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at this
    simpa [MulAut.conj_apply] using this
  refine ⟨⟨(MulAut.conj (m : G)).toMonoidHom.comp (M.subtype.comp φ.symm.toMonoidHom), ?_, ?_, ?_⟩⟩
  · intro x y hxy
    have h1 : M.subtype (φ.symm x) = M.subtype (φ.symm y) :=
      (MulAut.conj (m : G)).injective hxy
    exact φ.symm.injective (M.subtype_injective h1)
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact M.mul_mem (M.mul_mem m.2 (φ.symm y).2) (M.inv_mem m.2)
    · intro hx
      refine ⟨φ ⟨(m : G)⁻¹ * x * m, M.mul_mem (M.mul_mem (M.inv_mem m.2) hx) m.2⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply, Subgroup.coe_subtype, MulAut.conj_apply]
      group
  · ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : φ.symm w ∈ (PS : Subgroup M) := ⟨w, hw, rfl⟩
      have := hmem _ hw'
      have h2 : (m * φ.symm w * m⁻¹ : M) ∈ T.subgroupOf M := this
      exact h2
    · intro hx
      have hxM : (⟨x, hTM hx⟩ : M) ∈ (PT : Subgroup M) := hx
      obtain ⟨w, hw, hwx⟩ := (hmem' _ hxM : m⁻¹ * ⟨x, hTM hx⟩ * m ∈ (PS : Subgroup M))
      refine ⟨w, hw, ?_⟩
      have h3 : φ.symm w = m⁻¹ * ⟨x, hTM hx⟩ * m := hwx
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        Subgroup.coe_subtype, MulAut.conj_apply, h3]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group

section Transport

variable {H : Type*} [Group H] {ι : H →* G}

theorem card_map_of_inj (hι : Function.Injective ι) (S : Subgroup H) :
    Nat.card (S.map ι) = Nat.card S := Subgroup.card_map_of_injective hι

theorem isElemAbelian_map_iff (hι : Function.Injective ι) {S : Subgroup H} :
    IsElemAbelian 2 (S.map ι) ↔ IsElemAbelian 2 S := by
  constructor
  · intro h
    have := isElemAbelian_comap h hι
    rwa [Subgroup.comap_map_eq_self_of_injective hι] at this
  · intro h
    exact isElemAbelian_map h ι

theorem isMaxElemAbelian_map_iff (hι : Function.Injective ι) {S E : Subgroup H} :
    IsMaxElemAbelian (S.map ι) (E.map ι) ↔ IsMaxElemAbelian S E := by
  unfold IsMaxElemAbelian
  rw [Subgroup.map_le_map_iff_of_injective hι, isElemAbelian_map_iff hι,
    card_map_of_inj hι E]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h B' hB' hB'a
    have := h (B'.map ι) (Subgroup.map_mono hB') (isElemAbelian_map hB'a ι)
    rwa [card_map_of_inj hι] at this
  · intro h B hB hBa
    have hBr : B ≤ ι.range := hB.trans (by
      rintro _ ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩)
    have hB' : B.comap ι ≤ S := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hB hx
      rw [← hι hyx]
      exact hy
    have := h (B.comap ι) hB' (isElemAbelian_comap hBa hι)
    have e : Nat.card B = Nat.card (B.comap ι) := by
      conv_lhs => rw [← Subgroup.map_comap_eq_self hBr]
      exact card_map_of_inj hι _
    omega

theorem mem_normalizer_map_iff (hι : Function.Injective ι) {S : Subgroup H} {w : H} :
    ι w ∈ Subgroup.normalizer ((S.map ι : Subgroup G) : Set G) ↔
      w ∈ Subgroup.normalizer (S : Set H) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h s
    have := h (ι s)
    rw [Subgroup.mem_map_iff_mem hι, ← map_inv, ← map_mul, ← map_mul,
      Subgroup.mem_map_iff_mem hι] at this
    exact this
  · intro h y
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨w * s * w⁻¹, (h s).1 hs, ?_⟩
      simp
    · rintro ⟨s', hs', hs'eq⟩
      have hy : y = ι (w⁻¹ * s' * w) := by
        simp only [map_mul, map_inv]
        rw [hs'eq]
        group
      rw [hy]
      refine ⟨w⁻¹ * s' * w, ?_, rfl⟩
      have e : w * (w⁻¹ * s' * w) * w⁻¹ = s' := by group
      exact (h (w⁻¹ * s' * w)).2 (by rw [e]; exact hs')

end Transport

theorem isMaxElemAbelian_map_conj {T F : Subgroup G} (hF : IsMaxElemAbelian T F) (x : G)
    (hx : F.map (MulAut.conj x).toMonoidHom ≤ T) :
    IsMaxElemAbelian T (F.map (MulAut.conj x).toMonoidHom) := by
  refine ⟨hx, isElemAbelian_map hF.2.1 _, fun B hB hBa => ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
  exact hF.2.2 B hB hBa

theorem eq_of_le_isPGroup [Finite G] {T X : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hX : IsPGroup 2 X) (h : T ≤ X) : X = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  obtain ⟨P', hP'⟩ := hX.exists_le_sylow
  have h1 : Nat.card P' = Nat.card S := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h2 : Nat.card X ≤ Nat.card P' := Subgroup.card_le_of_le hP'
  have h3 : Nat.card T ≤ Nat.card X := Subgroup.card_le_of_le h
  have h4 : Nat.card S = Nat.card T := by rw [hS]
  exact (Subgroup.eq_of_le_of_card_ge h (by omega)).symm

theorem exists_mem_inf_normalizer_not_mem [Finite G] {U V : Subgroup G} (hV : IsPGroup 2 V)
    (hUV : U ≤ V) (hne : U ≠ V) :
    ∃ x ∈ V ⊓ Subgroup.normalizer (U : Set G), x ∉ U := by
  have : Group.IsNilpotent V := hV.isNilpotent
  have hlt : U.subgroupOf V < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne ?_
    refine le_antisymm hUV ?_
    intro v hv
    have : (⟨v, hv⟩ : V) ∈ U.subgroupOf V := htop ▸ Subgroup.mem_top _
    exact this
  have hnorm := Group.normalizerCondition_of_isNilpotent (G := V) _ hlt
  obtain ⟨x, hx, hxn⟩ := Set.exists_of_ssubset hnorm
  refine ⟨x, ?_, hxn⟩
  rw [← CT.map_subtype_normalizer hUV]
  exact ⟨x, hx, rfl⟩

end CFSG.Quasithin.A10

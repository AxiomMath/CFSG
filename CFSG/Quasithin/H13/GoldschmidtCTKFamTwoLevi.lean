module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoDelta
public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoRad
public import CFSG.Quasithin.H13.GoldschmidtI51Elem
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3SL2

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement MatrixGroups

@[expose] def NoA5Block (B : Type) [Group B] : Prop :=
  ∀ K V T₁ E : Subgroup B, V ≤ K → IsDelta5Ext ↥K (V.subgroupOf K) →
    T₁ ≤ Subgroup.normalizer (K : Set B) → IsSylowTwoOf E ⊤ → T₁ ≤ E → T₁.relIndex E ≤ 2 → False

variable {B : Type} [Group B] [Finite B]

theorem noA5Block_of_isPGroup (hB : IsPGroup 2 B) : NoA5Block B := by
  intro K V _ _ _ hΔ _ _ _ _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : IsPGroup 2 ↥K := hB.to_subgroup K
  have : Group.IsNilpotent ↥K := hK2.isNilpotent
  exact hΔ.not_isSolvable inferInstance

omit [Finite B] in
theorem levi_ker_le {T : Type} [Group T] {Q K V : Subgroup B} (hQn : Q.Normal)
    (hQ2 : IsPGroup 2 Q) (hΔ : IsDelta5Ext ↥K (V.subgroupOf K)) (g : B →* T)
    (hker : ∀ x, g x = 1 → x ∈ Q) : (g.comp K.subtype).ker ≤ V.subgroupOf K := by
  have hKQ : K ≤ Subgroup.normalizer (Q : Set B) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hQn]; exact le_top
  intro k hk
  exact Subgroup.mem_subgroupOf.2 (hΔ.inf_le hKQ hQ2 ⟨k.2, hker _ hk⟩)

theorem levi_alt5_image {T : Type} [Group T] [Finite T] {Q K V : Subgroup B} (hQn : Q.Normal)
    (hQ2 : IsPGroup 2 Q)
    (hn1 : ∀ {X Y : Subgroup T}, IsPGroup 2 X → X ≠ ⊥ → Y ≤ Subgroup.normalizer (X : Set T) →
      Group.IsSolvable ↥Y)
    (hΔ : IsDelta5Ext ↥K (V.subgroupOf K)) (g : B →* T) (hker : ∀ x, g x = 1 → x ∈ Q) :
    ((g.comp K.subtype).ker = V.subgroupOf K) ∧
      Nonempty (↥(g.comp K.subtype).range ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ : ↥K →* T := g.comp K.subtype with hψ
  have hV2 : IsPGroup 2 (V.subgroupOf K) := hΔ.isPGroup
  obtain ⟨α, c, hα, hαk, -⟩ := hΔ.exists_coords
  have hVn : (V.subgroupOf K).Normal := hαk ▸ α.normal_ker
  have hkerle : ψ.ker ≤ V.subgroupOf K := levi_ker_le hQn hQ2 hΔ g hker
  have hVker : V.subgroupOf K ≤ ψ.ker := by
    by_contra hnot
    set W : Subgroup T := (V.subgroupOf K).map ψ with hW
    have hWne : W ≠ ⊥ := by
      intro h0
      apply hnot
      intro v hv
      have : ψ v ∈ W := Subgroup.mem_map_of_mem ψ hv
      rw [h0, Subgroup.mem_bot] at this
      exact this
    have hW2 : IsPGroup 2 W := hV2.map ψ
    have hnorm : ψ.range ≤ Subgroup.normalizer (W : Set T) := by
      rintro _ ⟨k, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hw
        exact Subgroup.mem_map.2 ⟨k * v * k⁻¹, hVn.conj_mem v hv k, by simp [map_mul, map_inv]⟩
      · intro hw
        obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.1 hw
        refine Subgroup.mem_map.2 ⟨k⁻¹ * v * k, ?_, ?_⟩
        · have := hVn.conj_mem v hv k⁻¹
          simpa using this
        · simp only [map_mul, map_inv, hvw]
          group
    have hYsolv : Group.IsSolvable ↥ψ.range := hn1 hW2 hWne hnorm
    have hkerp : IsPGroup 2 ψ.ker := hV2.to_le hkerle
    have : Group.IsNilpotent ↥ψ.ker := hkerp.isNilpotent
    have : Group.IsSolvable ↥ψ.ker := inferInstance
    have hKsolv : Group.IsSolvable ↥K :=
      Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ.rangeRestrict (by
        rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
    exact hΔ.not_isSolvable hKsolv
  have hker_eq : ψ.ker = V.subgroupOf K := le_antisymm hkerle hVker
  refine ⟨hker_eq, ⟨?_⟩⟩
  exact (QuotientGroup.quotientKerEquivRange ψ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (hker_eq.trans hαk.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα))

open CFSG.QuasithinUnique.A5.G3 (solvable_of_le_normalizer sl2_index_normalizer card_SL2)

theorem relIndex_dvd_two {A C : Subgroup B} (h : A.relIndex C ≤ 2) : A.relIndex C ∣ 2 := by
  have hpos : A.relIndex C ≠ 0 := Subgroup.index_ne_zero_of_finite
  interval_cases hr : A.relIndex C <;> simp_all

theorem levi_decomp_sl2 {Q K V T1 E : Subgroup B} {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q)
    (hΔ : IsDelta5Ext ↥K (V.subgroupOf K)) (hT1K : T1 ≤ Subgroup.normalizer (K : Set B))
    (hE : IsSylowTwoOf E ⊤) (hT1E : T1 ≤ E) (hrel : T1.relIndex E ≤ 2)
    (g : B →* SL(2, F)) (hg : Function.Surjective g) (hker : ∀ x, g x = 1 → x ∈ Q) :
    ∀ b : B, ∃ k ∈ K, ∃ r ∈ Q, b = k * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hker_eq, ⟨θ⟩⟩ := levi_alt5_image hQn hQ2
    (fun {X Y} hX hX1 hYX => solvable_of_le_normalizer (by omega) hF hX hX1 hYX) hΔ g hker
  set ψ : ↥K →* SL(2, F) := g.comp K.subtype with hψ
  have hYtop : ψ.range = ⊤ := by
    by_cases h2 : n = 2
    · subst h2
      have hfin : Fintype F := Fintype.ofFinite F
      have hcard : Nat.card SL(2, F) = 60 := by
        rw [card_SL2, ← Nat.card_eq_fintype_card, hF]
        norm_num
      apply Subgroup.eq_top_of_card_eq
      rw [hcard, Nat.card_congr θ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    · exfalso
      have hn3 : 3 ≤ n := by omega
      set R : Subgroup SL(2, F) := E.map g with hR
      have hRp : IsPGroup 2 R := hE.2.1.map g
      have hRidx : ¬ 2 ∣ R.index := fun h2 => by
        have h3 := hE.2.2
        rw [show (E.subgroupOf ⊤).index = E.index from Subgroup.relIndex_top_right E] at h3
        exact h3 (h2.trans (Subgroup.index_map_dvd E hg))
      set R1 : Subgroup SL(2, F) := T1.map g with hR1
      have hR1R : R1 ≤ R := Subgroup.map_mono hT1E
      have hconj : ∀ t ∈ T1, ∀ y ∈ ψ.range, g t * y * (g t)⁻¹ ∈ ψ.range := by
        intro t ht y hy
        obtain ⟨k, rfl⟩ := hy
        have hk' : t * (k : B) * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hT1K ht) k).1 k.2
        refine ⟨⟨_, hk'⟩, ?_⟩
        have e : ψ ⟨t * (k : B) * t⁻¹, hk'⟩ = g (t * (k : B) * t⁻¹) := rfl
        rw [e, map_mul, map_mul, map_inv]
        rfl
      have hR1N : R1 ≤ Subgroup.normalizer (ψ.range : Set SL(2, F)) := by
        rintro _ ⟨t, ht, rfl⟩
        rw [Subgroup.mem_normalizer_iff]
        intro y
        refine ⟨hconj t ht y, fun hy => ?_⟩
        have := hconj t⁻¹ (T1.inv_mem ht) _ hy
        simpa [map_inv, mul_assoc] using this
      have hdvd : (R ⊓ Subgroup.normalizer (ψ.range : Set SL(2, F))).relIndex R ∣ 2 := by
        have h1 : R1.relIndex R ∣ T1.relIndex E := relIndex_map_dvd_of_le g hT1E
        have h6 : (R ⊓ Subgroup.normalizer (ψ.range : Set SL(2, F))).relIndex R ∣
            R1.relIndex R := Subgroup.relIndex_dvd_of_le_left R (le_inf hR1R hR1N)
        exact h6.trans (h1.trans (relIndex_dvd_two hrel))
      exact sl2_index_normalizer hn3 hF θ hRp hRidx hdvd
  intro b
  obtain ⟨k, hk⟩ : ∃ k : ↥K, ψ k = g b := by
    have : g b ∈ ψ.range := by rw [hYtop]; exact Subgroup.mem_top _
    exact this
  refine ⟨(k : B), k.2, (k : B)⁻¹ * b, ?_, by group⟩
  apply hker
  rw [map_mul, map_inv]
  have : g (k : B) = g b := hk
  rw [this, inv_mul_cancel]

theorem noA5Block_of_levi_sl2 {Q : Subgroup B} {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q)
    (hQab : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x) (hQB : Q ≤ ⁅Q, ⊤⁆)
    (g : B →* SL(2, F)) (hg : Function.Surjective g) (hker : ∀ x, g x = 1 → x ∈ Q) :
    NoA5Block B := by
  intro K V T1 E hVK hΔ hT1K hE hT1E hrel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKQ : K ≤ Subgroup.normalizer (Q : Set B) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hQn]; exact le_top
  have hdec := levi_decomp_sl2 hn hF hQn hQ2 hΔ hT1K hE hT1E hrel g hg hker
  have hQE : Q ≤ E :=
    CFSG.Quasithin.H13.I51.le_sylow_of_normalizes hE hQ2 le_top fun a _ n hn' =>
      hQn.conj_mem n hn' a
  have hidx : (Q ⊓ Subgroup.normalizer (K : Set B)).relIndex Q ≤ 2 := by
    have h1 : (Q ⊓ Subgroup.normalizer (K : Set B)).relIndex Q ∣ (Q ⊓ T1).relIndex Q :=
      Subgroup.relIndex_dvd_of_le_left Q (inf_le_inf_left Q hT1K)
    have h2 : (Q ⊓ T1).relIndex Q = T1.relIndex Q := Subgroup.inf_relIndex_left Q T1
    have h3 : T1.relIndex Q ≤ T1.relIndex E :=
      Subgroup.relIndex_le_of_le_right hQE Subgroup.index_ne_zero_of_finite
    have h4 : T1.relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero h4) (h2 ▸ h1)).trans (h3.trans hrel)
  have hab := abelian_of_levi_decomp (S := B) (Q := Q) (B := ⊤) (K := K) (V := V)
    (N := Subgroup.normalizer (K : Set B)) hQ2 hKQ Subgroup.le_normalizer le_rfl
    (hΔ.inf_le hKQ hQ2) (hΔ.comm_of_mem hVK) hidx hQB (fun b _ => hdec b)
  obtain ⟨x, hx, y, hy, hxy⟩ := hQab
  exact hxy (hab x hx y hy)

omit [Finite B] in
theorem noA5Block_of_levi_not_three {T : Type} [Group T] [Finite T] {Q : Subgroup B}
    (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q) (h3 : ¬ 3 ∣ Nat.card T) (g : B →* T)
    (hker : ∀ x, g x = 1 → x ∈ Q) : NoA5Block B := by
  intro K V _ _ _ hΔ _ _ _ _
  have hle := levi_ker_le hQn hQ2 hΔ g hker
  obtain ⟨α, hα, hαk, -⟩ := hΔ
  set ψ : ↥K →* T := g.comp K.subtype with hψ
  have h60 : (V.subgroupOf K).index = 60 := by
    rw [← hαk, Subgroup.index_ker, MonoidHom.range_eq_top.2 hα, Subgroup.card_top,
      Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have h1 : (V.subgroupOf K).index ∣ ψ.ker.index := Subgroup.index_dvd_of_le hle
  have h2 : ψ.ker.index = Nat.card ψ.range := Subgroup.index_ker ψ
  have h4 : Nat.card ψ.range ∣ Nat.card T := Subgroup.card_subgroup_dvd_card _
  apply h3
  have : 3 ∣ 60 := by norm_num
  exact this.trans (h60 ▸ h1.trans (h2 ▸ h4))

end CFSG.Quasithin.H13.CTK

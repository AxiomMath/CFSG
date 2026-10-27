module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIConfig

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup

variable {X : Type*} [Group X] [Finite X]

theorem exists_maximal_pgroup {Y T : Subgroup X} (hTY : T ≤ Y) (hT : IsPGroup 2 T) :
    ∃ S : Subgroup X, T ≤ S ∧ S ≤ Y ∧ IsPGroup 2 S ∧
      ∀ T' : Subgroup X, T' ≤ Y → IsPGroup 2 T' → S ≤ T' → T' = S := by
  have hTY2 : IsPGroup 2 (T.subgroupOf Y) := hT.comap_subtype
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hTY2
  refine ⟨(Q : Subgroup Y).map Y.subtype, ?_, Subgroup.map_subtype_le _, Q.isPGroup'.map _, ?_⟩
  · intro t ht
    have htY : (⟨t, hTY ht⟩ : ↥Y) ∈ T.subgroupOf Y := Subgroup.mem_subgroupOf.mpr ht
    exact Subgroup.mem_map.mpr ⟨⟨t, hTY ht⟩, hQ htY, rfl⟩
  · intro T' hT'Y hT'p hST'
    have hR : IsPGroup 2 (T'.subgroupOf Y) := hT'p.comap_subtype
    have hQR : (Q : Subgroup Y) ≤ T'.subgroupOf Y := by
      intro q hq
      exact Subgroup.mem_subgroupOf.mpr (hST' (Subgroup.mem_map_of_mem Y.subtype hq))
    have hEq : T'.subgroupOf Y = (Q : Subgroup Y) := Q.is_maximal' hR hQR
    rw [← hEq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT'Y]

theorem subgroupOf_sylow_max {Hn S : Subgroup X} (hSH : S ≤ Hn)
    (hS : ∀ U : Subgroup X, U ≤ Hn → IsPGroup 2 U → S ≤ U → U = S) :
    ∀ {Q : Subgroup ↥Hn}, IsPGroup 2 Q → S.subgroupOf Hn ≤ Q → Q = S.subgroupOf Hn := by
  intro Q hQ hle
  have hSR : S ≤ Q.map Hn.subtype := by
    intro s hs
    have hsH : (⟨s, hSH hs⟩ : ↥Hn) ∈ S.subgroupOf Hn := Subgroup.mem_subgroupOf.mpr hs
    exact Subgroup.mem_map.mpr ⟨⟨s, hSH hs⟩, hle hsH, rfl⟩
  have hRS : Q.map Hn.subtype = S := hS _ (Subgroup.map_subtype_le Q) (hQ.map _) hSR
  calc Q = (Q.map Hn.subtype).comap Hn.subtype :=
        (Subgroup.comap_map_eq_self_of_injective Hn.subtype_injective Q).symm
    _ = S.subgroupOf Hn := congrArg (fun U : Subgroup X => U.comap Hn.subtype) hRS

theorem exists_conj_of_max_pgroup {Hn S T : Subgroup X} (hSH : S ≤ Hn) (hTH : T ≤ Hn)
    (hSp : IsPGroup 2 S) (hTp : IsPGroup 2 T)
    (hS : ∀ U : Subgroup X, U ≤ Hn → IsPGroup 2 U → S ≤ U → U = S)
    (hT : ∀ U : Subgroup X, U ≤ Hn → IsPGroup 2 U → T ≤ U → U = T) :
    ∃ y ∈ Hn, ∀ t ∈ T, y⁻¹ * t * y ∈ S := by
  let P : Sylow 2 ↥Hn := ⟨S.subgroupOf Hn, hSp.comap_subtype, subgroupOf_sylow_max hSH hS⟩
  let Q : Sylow 2 ↥Hn := ⟨T.subgroupOf Hn, hTp.comap_subtype, subgroupOf_sylow_max hTH hT⟩
  have hPS : (P : Subgroup ↥Hn) = S.subgroupOf Hn := rfl
  have hQT : (Q : Subgroup ↥Hn) = T.subgroupOf Hn := rfl
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq ↥Hn Q P
  refine ⟨((m⁻¹ : ↥Hn) : X), (m⁻¹ : ↥Hn).2, fun t ht => ?_⟩
  have h1 : (⟨t, hTH ht⟩ : ↥Hn) ∈ (Q : Subgroup ↥Hn) := by
    rw [hQT]
    exact Subgroup.mem_subgroupOf.mpr ht
  have h2 := Subgroup.smul_mem_pointwise_smul (⟨t, hTH ht⟩ : ↥Hn) (MulAut.conj m) _ h1
  rw [← Sylow.coe_subgroup_smul, hm, hPS] at h2
  have h3 := Subgroup.mem_subgroupOf.mp h2
  simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using h3

namespace TIConfig

variable {H V N : Subgroup X}

theorem ne_bot_of_N_le (h : TIConfig H V N) {S : Subgroup X} (hNS : N ≤ S) : S ≠ ⊥ := by
  intro h0
  apply h.V_ne_bot
  have hVS : V ≤ S := h.V_le_N.trans hNS
  rw [h0] at hVS
  exact le_bot_iff.mp hVS

theorem normalizer_le_normalizer_V (h : TIConfig H V N) {S : Subgroup X} (hSp : IsPGroup 2 S)
    (hSne : S ≠ ⊥) (hZ : cenIn S ≤ V) : normalizer (S : Set X) ≤ normalizer (V : Set X) := by
  intro k hk
  obtain ⟨z, hzc, hz1⟩ := exists_ne_one_mem_cenIn hSp hSne
  have hzV : z ∈ V := hZ hzc
  have hkzV : k * z * k⁻¹ ∈ V := hZ (conj_mem_cenIn hk hzc)
  exact h.ti k z hzV hz1 hkzV

theorem sylow_of_maximal (h : TIConfig H V N) {S : Subgroup X} (hSK : S ≤ NormIn H V)
    (hSp : IsPGroup 2 S)
    (hS : ∀ T : Subgroup X, T ≤ NormIn H V → IsPGroup 2 T → S ≤ T → T = S) :
    ∀ T : Subgroup X, T ≤ H → IsPGroup 2 T → S ≤ T → T = S := by
  intro T hTH hTp hST
  have hNS : N ≤ S := h.N_le_of_maximal h.N_le le_rfl hSK hSp hS
  have hSne : S ≠ ⊥ := h.ne_bot_of_N_le hNS
  have hZV : cenIn S ≤ V := h.cenIn_le_V h.N_le le_rfl hSK hSp hS
  by_contra hne
  have hnTS : ¬ T ≤ S := fun hle => hne (le_antisymm hle hST)
  obtain ⟨x, hxT, hxN, hxS⟩ := exists_mem_normalizer_not_mem hTp hST hnTS
  have hxV : x ∈ normalizer (V : Set X) := normalizer_le_normalizer_V h hSp hSne hZV hxN
  have hxK : x ∈ NormIn H V := mem_NormIn.mpr ⟨hTH hxT, hxV⟩
  have hpT : IsPGroup 2 (T ⊓ NormIn H V : Subgroup X) := hTp.to_inf_left
  have hTK : S ≤ T ⊓ NormIn H V := le_inf hST hSK
  have hEq : T ⊓ NormIn H V = S := hS (T ⊓ NormIn H V) inf_le_right hpT hTK
  have hxS' : x ∈ S := by
    rw [← hEq]
    exact Subgroup.mem_inf.mpr ⟨hxT, hxK⟩
  exact hxS hxS'

end TIConfig

open TIConfig in
theorem frattini_core {Hn X' : Subgroup X} (hHX : Hn ≤ X')
    (hn : ∀ x ∈ X', x ∈ normalizer (Hn : Set X))
    {S : Subgroup X} (hSH : S ≤ Hn) (hSp : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup X, T ≤ Hn → IsPGroup 2 T → S ≤ T → T = S) :
    ∀ g ∈ X', ∃ k ∈ X', k ∈ normalizer (S : Set X) ∧ ∃ y ∈ Hn, g = k * y := by
  intro g hg
  have hgN : g ∈ normalizer (Hn : Set X) := hn g hg
  have hginvN : g⁻¹ ∈ normalizer (Hn : Set X) := (normalizer (Hn : Set X)).inv_mem hgN
  let T : Subgroup X := S.comap (MulAut.conj g⁻¹).toMonoidHom
  have hTmem : ∀ x : X, x ∈ T ↔ g⁻¹ * x * g ∈ S := by
    intro x
    simp [T, MulAut.conj_apply]
  have hTH : T ≤ Hn := by
    intro x hx
    have h1 : g⁻¹ * x * g ∈ Hn := hSH ((hTmem x).mp hx)
    have h2 := conj_mem_of_mem_normalizer hgN h1
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h2
  have hTp : IsPGroup 2 T := hSp.comap_of_injective (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective
  have hTmax : ∀ U : Subgroup X, U ≤ Hn → IsPGroup 2 U → T ≤ U → U = T := by
    intro U hUH hUp hTU
    let U' : Subgroup X := U.comap (MulAut.conj g).toMonoidHom
    have hU'mem : ∀ x : X, x ∈ U' ↔ g * x * g⁻¹ ∈ U := by
      intro x
      simp [U', MulAut.conj_apply]
    have hU'H : U' ≤ Hn := by
      intro x hx
      have h1 := hUH ((hU'mem x).mp hx)
      have h2 := conj_mem_of_mem_normalizer hginvN h1
      rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h2
    have hU'p : IsPGroup 2 U' := hUp.comap_of_injective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
    have hSU' : S ≤ U' := by
      intro s hs
      rw [hU'mem]
      apply hTU
      rw [hTmem]
      rwa [show g⁻¹ * (g * s * g⁻¹) * g = s by group]
    have hU'S : U' = S := hmax U' hU'H hU'p hSU'
    apply le_antisymm
    · intro u hu
      rw [hTmem]
      have h1 : g⁻¹ * u * g ∈ U' := by
        rw [hU'mem]
        rwa [show g * (g⁻¹ * u * g) * g⁻¹ = u by group]
      rw [hU'S] at h1
      exact h1
    · exact hTU
  obtain ⟨y, hyH, hy⟩ := exists_conj_of_max_pgroup hSH hTH hSp hTp hmax hTmax
  have hk : y⁻¹ * g ∈ X' := X'.mul_mem (X'.inv_mem (hHX hyH)) hg
  have hkS : y⁻¹ * g ∈ normalizer (S : Set X) := by
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    have hgz : g * z * g⁻¹ ∈ T := by
      rw [hTmem]
      rwa [show g⁻¹ * (g * z * g⁻¹) * g = z by group]
    have h1 := hy _ hgz
    rwa [show y⁻¹ * (g * z * g⁻¹) * y = y⁻¹ * g * z * (y⁻¹ * g)⁻¹ by group] at h1
  have hy' : g⁻¹ * y * g ∈ Hn := by
    have h1 := conj_mem_of_mem_normalizer hginvN hyH
    rwa [show g⁻¹ * y * g⁻¹⁻¹ = g⁻¹ * y * g by group] at h1
  exact ⟨y⁻¹ * g, hk, hkS, g⁻¹ * y * g, hy', by group⟩

namespace TIConfig

variable {H V N : Subgroup X}

theorem frattini_conj (h : TIConfig H V N) (hHn : ∀ x : X, x ∈ normalizer (H : Set X))
    (g : X) : ∃ k ∈ normalizer (V : Set X), ∃ y ∈ H, g = k * y := by
  obtain ⟨S, hNS, hSK, hSp, hS⟩ := exists_maximal_pgroup h.N_le h.N_pgroup
  have hSH : S ≤ H := fun x hx => (mem_NormIn.mp (hSK hx)).1
  have hmaxH := h.sylow_of_maximal hSK hSp hS
  have hZV : cenIn S ≤ V := h.cenIn_le_V h.N_le le_rfl hSK hSp hS
  have hSne : S ≠ ⊥ := h.ne_bot_of_N_le hNS
  obtain ⟨k, _, hkS, y, hy, hgky⟩ :=
    frattini_core (Hn := H) (X' := ⊤) le_top (fun x _ => hHn x) hSH hSp hmaxH g
      (Subgroup.mem_top g)
  exact ⟨k, normalizer_le_normalizer_V h hSp hSne hZV hkS, y, hy, hgky⟩

theorem refined_frattini (h : TIConfig H V N) (hHn : ∀ x : X, x ∈ normalizer (H : Set X))
    {L : Subgroup X} (hNL : N ≤ normalizer (L : Set X))
    (hY : normalizer (L : Set X) ⊓ H ≤ NormIn H V) :
    normalizer (L : Set X) ≤ normalizer (V : Set X) := by
  have hKH : NormIn H V ≤ H := fun x hx => (mem_NormIn.mp hx).1
  have hNY : N ≤ normalizer (L : Set X) ⊓ H := le_inf hNL (h.N_le.trans hKH)
  have hn : ∀ x ∈ normalizer (L : Set X),
      x ∈ normalizer ((normalizer (L : Set X) ⊓ H : Subgroup X) : Set X) := by
    intro x hx
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    obtain ⟨hzL, hzH⟩ := Subgroup.mem_inf.mp hz
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hzL)
      (Subgroup.inv_mem _ hx), conj_mem_of_mem_normalizer (hHn x) hzH⟩
  obtain ⟨S, hNS, hSY, hSp, hS⟩ := exists_maximal_pgroup hNY h.N_pgroup
  have hZV : cenIn S ≤ V := h.cenIn_le_V hNY hY hSY hSp hS
  have hSne : S ≠ ⊥ := h.ne_bot_of_N_le hNS
  have hfc := frattini_core (Hn := normalizer (L : Set X) ⊓ H) (X' := normalizer (L : Set X))
    inf_le_left hn hSY hSp hS
  intro g hg
  obtain ⟨k, _, hkS, y, hyY, hgky⟩ := hfc g hg
  have hkV : k ∈ normalizer (V : Set X) := normalizer_le_normalizer_V h hSp hSne hZV hkS
  have hyV : y ∈ normalizer (V : Set X) := (mem_NormIn.mp (hY hyY)).2
  rw [hgky]
  exact Subgroup.mul_mem _ hkV hyV

end TIConfig

end CFSG.RankThree.GF2n.Stroth80

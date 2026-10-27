module

public import CFSG.Quasithin.Vol2.Ch10SecKRPb

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRP

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Matrix

variable {Q : Type} [Group Q]

theorem commute_of_isPGroup_two {G₀ : Type*} [Group G₀] {X P : Subgroup G₀} {p : ℕ}
    [Fact p.Prime] (hp : 5 ≤ p) (ψ : ↥X ≃* SpecialLinearGroup (Fin 2) (ZMod p)) (hPX : P ≤ X)
    (hPn : ∀ x ∈ X, ∀ a ∈ P, x * a * x⁻¹ ∈ P) (h2 : IsPGroup 2 P) :
    ∀ a ∈ P, ∀ x ∈ X, a * x = x * a := by
  have hn : (P.subgroupOf X).Normal :=
    ⟨fun a ha g => Subgroup.mem_subgroupOf.mpr (hPn g g.2 a (Subgroup.mem_subgroupOf.mp ha))⟩
  have h2' : IsPGroup 2 ((P.subgroupOf X).map ψ.toMonoidHom) :=
    (h2.comap_of_injective X.subtype X.subtype_injective).map _
  have hc := le_center_of_isPGroup_two hp (hn.map ψ.toMonoidHom ψ.surjective) h2'
  intro a ha x hx
  have ha' : ψ ⟨a, hPX ha⟩ ∈ Subgroup.center (SpecialLinearGroup (Fin 2) (ZMod p)) :=
    hc ⟨⟨a, hPX ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have h' : (⟨a, hPX ha⟩ : ↥X) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨a, hPX ha⟩ :=
    ψ.injective (by
      rw [map_mul, map_mul]
      exact (Subgroup.mem_center_iff.mp ha' (ψ ⟨x, hx⟩)).symm)
  exact congrArg Subtype.val h'

theorem conj_mem_pCoreOf {B : Subgroup Q} {b c : Q} (hb : b ∈ B) (hc : c ∈ pCoreOf 2 B) :
    b * c * b⁻¹ ∈ pCoreOf 2 B := by
  obtain ⟨c', hc', rfl⟩ := hc
  refine ⟨⟨b, hb⟩ * c' * ⟨b, hb⟩⁻¹, ?_, rfl⟩
  exact CFSG.pCore_normal.conj_mem c' hc' ⟨b, hb⟩

theorem false_of_nonquasi (hSL2 : A312SL2Fact) (h36 : Vol2Native.A36CoreForSQTKCat)
    (hQ : Vol2Native.SQTKHypCat Q) {S K B₁ B₂ : Subgroup Q} (hS : IsSylowTwoOf S ⊤)
    (hK : K ∈ cComp (⊤ : Subgroup Q)) (hB₁ : B₁ ∈ lFamily S) (hB₂ : B₂ ∈ lFamily S)
    (hB₁K : B₁ ≤ K) (hB₂K : B₂ ≤ K) (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁)
    (hnq : ¬ CFSG.IsQuasisimple ↥K) : False := by
  have := hQ.finite
  have hA36 : A36Strong K := (h36 Q hQ K hK).toStrong hnq
  obtain ⟨p, hp, hp3, ⟨eK⟩⟩ := A312.exists_isSL2_oddCore hA36 hnq
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent ↥(CFSG.oddCore ↥K) := by
    rw [← hA36.2.1.1]
    infer_instance
  set π : ↥K →* ↥K ⧸ CFSG.oddCore ↥K := QuotientGroup.mk' (CFSG.oddCore ↥K) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπk : π.ker = CFSG.oddCore ↥K := QuotientGroup.ker_mk' _
  set X₁ : Subgroup (↥K ⧸ CFSG.oddCore ↥K) := (B₁.subgroupOf K).map π with hX₁
  set X₂ : Subgroup (↥K ⧸ CFSG.oddCore ↥K) := (B₂.subgroupOf K).map π with hX₂
  have hB₁c : B₁ ∈ cComp (B₁ ⊔ S) := hB₁
  have hB₂c : B₂ ∈ cComp (B₂ ⊔ S) := hB₂
  have hB₁p := perfect_subgroupOf hB₁K (perfect_of_mem_cComp hB₁c)
  have hB₂p := perfect_subgroupOf hB₂K (perfect_of_mem_cComp hB₂c)
  have hX₁p : ⁅X₁, X₁⁆ = X₁ := by rw [hX₁, ← Subgroup.map_commutator, hB₁p]
  have hX₂p : ⁅X₂, X₂⁆ = X₂ := by rw [hX₂, ← Subgroup.map_commutator, hB₂p]
  have hbot : ∀ {B : Subgroup Q}, B ≤ K → B ≠ ⊥ →
      ⁅B.subgroupOf K, B.subgroupOf K⁆ = B.subgroupOf K → (B.subgroupOf K).map π ≠ ⊥ := by
    intro B hBK hBne hBp hXb
    rw [Subgroup.map_eq_bot_iff, hπk] at hXb
    exact hBne (eq_bot_of_subgroupOf_eq_bot hBK (eq_bot_of_perfect_of_le hXb hBp))
  obtain ⟨p', hp', hp'5, ⟨ψ⟩⟩ : ∃ p' : ℕ, p'.Prime ∧ 5 ≤ p' ∧
      Nonempty (↥X₁ ≃* SpecialLinearGroup (Fin 2) (ZMod p')) := by
    rcases A312.nonquasi_of_lFamily hSL2 hS hK hB₁K hB₁ hA36 hnq with
      ⟨-, hKeq, -⟩ | ⟨-, -, N, hNn, hNeq, ⟨e5⟩⟩
    · have hp5 : 5 ≤ p := by
        rcases (show p = 4 ∨ 5 ≤ p by omega) with h4 | h5
        · exact absurd (h4 ▸ hp) (by decide)
        · exact h5
      refine ⟨p, hp, hp5, ⟨?_⟩⟩
      have htop : B₁.subgroupOf K ⊔ CFSG.oddCore ↥K = ⊤ := by
        have h1 : (B₁ ⊔ (CFSG.oddCore ↥K).map K.subtype).subgroupOf K = ⊤ := by
          rw [← hKeq]
          exact Subgroup.subgroupOf_self K
        rw [Subgroup.subgroupOf_sup hB₁K (Subgroup.map_subtype_le _)] at h1
        rwa [show ((CFSG.oddCore ↥K).map K.subtype).subgroupOf K = CFSG.oddCore ↥K from
          Subgroup.comap_map_eq_self_of_injective K.subtype_injective _] at h1
      have hX : X₁ = ⊤ := by
        have h1 : (CFSG.oddCore ↥K).map π = ⊥ := (Subgroup.map_eq_bot_iff _).mpr hπk.ge
        calc X₁ = X₁ ⊔ (CFSG.oddCore ↥K).map π := by rw [h1, sup_bot_eq]
          _ = (B₁.subgroupOf K ⊔ CFSG.oddCore ↥K).map π := (Subgroup.map_sup _ _ _).symm
          _ = ⊤ := by rw [htop, Subgroup.map_top_of_surjective π hπs]
      exact (MulEquiv.subgroupCongr hX).trans (Subgroup.topEquiv.trans eK)
    · subst hNeq
      exact ⟨5, by norm_num, le_rfl, ⟨(A312.quotEquivImage hB₁K).symm.trans e5⟩⟩
  have : Fact p'.Prime := ⟨hp'⟩
  set P₁ : Subgroup (↥K ⧸ CFSG.oddCore ↥K) := ((pCoreOf 2 B₁).subgroupOf K).map π with hP₁
  have hP₁2 : IsPGroup 2 P₁ :=
    ((isPGroup_pCoreOf B₁).comap_of_injective K.subtype K.subtype_injective).map π
  have hP₁X : P₁ ≤ X₁ := Subgroup.map_mono (Subgroup.comap_mono (Subgroup.map_subtype_le _))
  have hP₁n : ∀ x ∈ X₁, ∀ a ∈ P₁, x * a * x⁻¹ ∈ P₁ := by
    rintro x ⟨b, hb, rfl⟩ a ⟨c, hc', rfl⟩
    refine ⟨b * c * b⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact Subgroup.mem_subgroupOf.mpr
      (conj_mem_pCoreOf (Subgroup.mem_subgroupOf.mp hb) (Subgroup.mem_subgroupOf.mp hc'))
  have hcent := commute_of_isPGroup_two hp'5 ψ hP₁X hP₁n hP₁2
  have hcomm : ⁅X₁, X₂⁆ ≤ P₁ := by
    rw [hX₁, hX₂, ← Subgroup.map_commutator]
    exact Subgroup.map_mono (commutator_subgroupOf_le' hB₁K hB₂K hc)
  have hc1 : ⁅⁅X₁, X₂⁆, X₁⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hcent z (hcomm hz) x hx).symm
  have hc2 : ⁅⁅X₂, X₁⁆, X₁⁆ = ⊥ := by rw [Subgroup.commutator_comm X₂ X₁]; exact hc1
  have h3 : ⁅X₁, X₂⁆ = ⊥ := by
    have := Subgroup.commutator_commutator_eq_bot_of_rotate hc1 hc2
    rwa [hX₁p] at this
  obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ : ∃ x₁ ∈ X₁, ∃ x₂ ∈ X₁, x₁ * x₂ ≠ x₂ * x₁ := by
    by_contra hall
    push Not at hall
    apply hbot hB₁K (ne_bot_of_mem_cComp hB₁c) hB₁p
    show X₁ = ⊥
    rw [← hX₁p, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hall x hx y hy
  have hX₂c : ∀ u ∈ X₂, ∀ x ∈ X₁, u * x = x * u := by
    intro u hu x hx
    have h := Subgroup.commutator_mem_commutator hx hu
    rw [h3, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h.symm
  have hX₂ab : ∀ u ∈ X₂, ∀ v ∈ X₂, u * v = v * u := by
    intro u hu v _
    apply eK.injective
    rw [map_mul, map_mul]
    refine commute_of_forall_commute (X := X₁.map eK.toMonoidHom) ⟨x₁, hx₁, rfl⟩
      ⟨x₂, hx₂, rfl⟩ (fun h => hne (eK.injective (by rw [map_mul, map_mul]; exact h))) ?_
    rintro x ⟨y, hy, rfl⟩
    show eK u * eK y = eK y * eK u
    rw [← map_mul, ← map_mul, hX₂c u hu y hy]
  have hX₂b : X₂ = ⊥ := by
    rw [← hX₂p, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hX₂ab v hv u hu
  exact hbot hB₂K (ne_bot_of_mem_cComp hB₂c) hB₂p hX₂b

end CFSG.Quasithin.Vol2.Ch10.SecB.KRP

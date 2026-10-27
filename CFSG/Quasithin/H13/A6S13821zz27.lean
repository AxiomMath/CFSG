module

public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open scoped commutatorElement

theorem quotCenter_of_surjective {Q R : Type*} [Group Q] [Group R] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) {φ : Q →* R} (hφ : Function.Surjective φ) [Nontrivial R] :
    Nonempty ((Q ⧸ Subgroup.center Q) ≃* (R ⧸ Subgroup.center R)) ∧
      Nat.card (Subgroup.center R) ∣ Nat.card (Subgroup.center Q) := by
  classical
  obtain ⟨hperf', hs, -⟩ := hQ
  have hperf : commutator Q = ⊤ := Group.isPerfect_def.mp hperf'
  have hperfR : commutator R = ⊤ := by
    rw [commutator, ← Subgroup.map_top_of_surjective φ hφ, ← Subgroup.map_commutator,
      ← commutator, hperf, Subgroup.map_top_of_surjective φ hφ]
  have hZR : Subgroup.center R ≠ ⊤ := by
    intro h
    obtain ⟨r, hr⟩ := exists_ne (1 : R)
    apply hr
    have h1 : r ∈ commutator R := by rw [hperfR]; exact Subgroup.mem_top r
    have h2 : commutator R = ⊥ := by
      rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y
    rw [h2] at h1
    exact h1
  set P := (Subgroup.center R).comap φ with hP
  have hPn : P.Normal := Subgroup.Normal.comap inferInstance φ
  have hPt : P ≠ ⊤ := by
    intro h
    apply hZR
    rw [eq_top_iff]
    intro r _
    obtain ⟨a, rfl⟩ := hφ r
    have : a ∈ P := by rw [h]; exact Subgroup.mem_top a
    exact this
  have hPZ : P ≤ Subgroup.center Q := by
    set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
    have hmn : (P.map π).Normal := hPn.map π (QuotientGroup.mk'_surjective _)
    rcases hmn.eq_bot_or_eq_top with hbot | htop
    · intro x hx
      have h1 : π x ∈ P.map π := ⟨x, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    · exfalso
      apply hPt
      have hdec : ∀ a : Q, ∃ n ∈ P, n⁻¹ * a ∈ Subgroup.center Q := by
        intro a
        have h1 : π a ∈ P.map π := by rw [htop]; exact Subgroup.mem_top _
        obtain ⟨n, hn, hna⟩ := h1
        refine ⟨n, hn, ?_⟩
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hna
        exact hna
      rw [eq_top_iff, ← hperf]
      refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
      obtain ⟨n, hn, hz⟩ := hdec a
      obtain ⟨n', hn', hz'⟩ := hdec b
      set z := n⁻¹ * a with hzdef
      set z' := n'⁻¹ * b with hz'def
      have ha : a = n * z := by rw [hzdef]; group
      have hb : b = n' * z' := by rw [hz'def]; group
      have hzc : ∀ g : Q, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
      have hzc' : ∀ g : Q, z' * g = g * z' := fun g => (Subgroup.mem_center_iff.mp hz' g).symm
      have e : ⁅a, b⁆ = ⁅n, n'⁆ := by
        rw [commutatorElement_def, commutatorElement_def, ha, hb]
        calc n * z * (n' * z') * (n * z)⁻¹ * (n' * z')⁻¹
            = n * (z * n') * z' * z⁻¹ * n⁻¹ * z'⁻¹ * n'⁻¹ := by group
          _ = n * (n' * z) * z' * z⁻¹ * n⁻¹ * z'⁻¹ * n'⁻¹ := by rw [hzc n']
          _ = n * n' * (z * z' * z⁻¹) * n⁻¹ * z'⁻¹ * n'⁻¹ := by group
          _ = n * n' * z' * n⁻¹ * z'⁻¹ * n'⁻¹ := by
            rw [show z * z' * z⁻¹ = z' by rw [hzc z']; group]
          _ = n * n' * (z' * n⁻¹) * z'⁻¹ * n'⁻¹ := by group
          _ = n * n' * (n⁻¹ * z') * z'⁻¹ * n'⁻¹ := by rw [hzc' n⁻¹]
          _ = n * n' * n⁻¹ * n'⁻¹ := by group
      rw [e, commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem hn hn') (P.inv_mem hn)) (P.inv_mem hn')
  have hZP : Subgroup.center Q ≤ P := by
    intro z hz
    rw [hP, Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro r
    obtain ⟨a, rfl⟩ := hφ r
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz a]
  set f := QuotientGroup.map (Subgroup.center Q) (Subgroup.center R) φ hZP with hf
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, rfl⟩ := hφ r
    exact ⟨QuotientGroup.mk a, rfl⟩
  have hfi : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MonoidHom.mem_ker, hf, QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at hx
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    exact hPZ hx
  refine ⟨⟨MulEquiv.ofBijective f ⟨hfi, hfs⟩⟩, ?_⟩
  have hZmap : Subgroup.center R = (Subgroup.center Q).map φ := by
    apply le_antisymm
    · intro r hr
      obtain ⟨a, rfl⟩ := hφ r
      exact ⟨a, hPZ hr, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact hZP ha
  rw [hZmap]
  exact Subgroup.card_map_dvd _ _

end CFSG.Quasithin.H13.A6.A6S20

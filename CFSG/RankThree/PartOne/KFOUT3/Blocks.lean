module

public import CFSG.RankThree.PartOne.KFOUT3.Hexagon
public import CFSG.RankThree.PartOne.KFOUT3.Involution

public section

namespace CFSG.RankThree.PartOne.KFOUT3

section Abstract

variable {Γ : Type} [Group Γ]

@[expose] def IsRoot (T : Subgroup Γ) (u : Γ) : Prop :=
  u ≠ 1 ∧ u * u = 1 ∧ (∀ t ∈ T, Commute u (t * u * t⁻¹)) ∧ ∃ t ∈ T, t ≠ 1 ∧ Commute t u

theorem commute_map_iff (φ : Γ ≃* Γ) {a b : Γ} : Commute (φ a) (φ b) ↔ Commute a b :=
  ⟨fun h => φ.injective (by rw [map_mul, map_mul]; exact h.eq), fun h => h.map φ⟩

theorem isRoot_map {T : Subgroup Γ} (φ : Γ ≃* Γ) (hφ : ∀ t, t ∈ T ↔ φ t ∈ T) (u : Γ) :
    IsRoot T (φ u) ↔ IsRoot T u := by
  constructor
  · rintro ⟨h1, h2, h3, t, ht, ht1, htu⟩
    refine ⟨fun h => h1 (by rw [h, map_one]), φ.injective (by rw [map_mul, h2, map_one]),
      fun s hs => ?_, φ.symm t, (hφ _).2 (by rwa [MulEquiv.apply_symm_apply]),
      fun h => ht1 (by simpa using congrArg φ h), ?_⟩
    · have := h3 (φ s) ((hφ s).1 hs)
      rw [← map_mul, ← map_inv, ← map_mul] at this
      exact (commute_map_iff φ).1 this
    · rw [← commute_map_iff φ, MulEquiv.apply_symm_apply]
      exact htu
  · rintro ⟨h1, h2, h3, t, ht, ht1, htu⟩
    refine ⟨fun h => h1 (φ.injective (by rw [h, map_one])), by rw [← map_mul, h2, map_one],
      fun s hs => ?_, φ t, (hφ t).1 ht, fun h => ht1 (φ.injective (by rw [h, map_one])), ?_⟩
    · obtain ⟨s', hs', rfl⟩ : ∃ s', s' ∈ T ∧ φ s' = s :=
        ⟨φ.symm s, (hφ _).2 (by rwa [MulEquiv.apply_symm_apply]), MulEquiv.apply_symm_apply _ _⟩
      have := h3 s' hs'
      have := this.map φ
      rwa [map_mul, map_mul, map_inv] at this
    · exact htu.map φ

theorem exists_hexagon_aut_of_roots {K : Type} [Field K] {T : Subgroup Γ} (RB : Blk → K → Γ)
    (hroot : ∀ u, IsRoot T u ↔ ∃ b s, s ≠ 0 ∧ u = RB b s)
    (hcomm : ∀ b b' s s', s ≠ 0 → s' ≠ 0 → (Commute (RB b s) (RB b' s') ↔ BComm b b'))
    (φ : Γ ≃* Γ) (hφ : ∀ t, t ∈ T ↔ φ t ∈ T) :
    ∃ ρ : Equiv.Perm Blk, (∀ b b', BComm b b' ↔ BComm (ρ b) (ρ b')) ∧
      ∀ b s, s ≠ 0 → ∃ s', s' ≠ 0 ∧ φ (RB b s) = RB (ρ b) s' := by
  have hr : ∀ b s, s ≠ 0 → ∃ b' s', s' ≠ 0 ∧ φ (RB b s) = RB b' s' := by
    intro b s hs
    have h1 := (hroot (RB b s)).2 ⟨b, s, hs, rfl⟩
    obtain ⟨b', s', hs', h⟩ := (hroot (φ (RB b s))).1 ((isRoot_map φ hφ _).2 h1)
    exact ⟨b', s', hs', h⟩
  choose ρ₀ s₀ hs₀ hφ₀ using fun b => hr b 1 one_ne_zero
  have hsig : ∀ b c, BComm c b ↔ BComm (ρ₀ c) (ρ₀ b) := by
    intro b c
    rw [← hcomm c b 1 1 one_ne_zero one_ne_zero,
      ← hcomm (ρ₀ c) (ρ₀ b) (s₀ c) (s₀ b) (hs₀ c) (hs₀ b), ← hφ₀ c, ← hφ₀ b,
      commute_map_iff]
  have hinj : Function.Injective ρ₀ := by
    intro b b' h
    apply blk_eq_of_comm_iff
    intro c
    rw [hsig b c, hsig b' c, h]
  have hbij : Function.Bijective ρ₀ := Finite.injective_iff_bijective.mp hinj
  refine ⟨Equiv.ofBijective ρ₀ hbij, fun b b' => hsig b' b, ?_⟩
  intro b s hs
  obtain ⟨b'', s'', hs'', h''⟩ := hr b s hs
  have key : ∀ c, BComm c b ↔ BComm (ρ₀ c) b'' := by
    intro c
    rw [← hcomm c b 1 s one_ne_zero hs, ← hcomm (ρ₀ c) b'' (s₀ c) s'' (hs₀ c) hs'', ← hφ₀ c,
      ← h'', commute_map_iff]
  have hb : b'' = ρ₀ b := by
    apply blk_eq_of_comm_iff
    intro d
    obtain ⟨c, rfl⟩ := hbij.2 d
    rw [← key c, hsig b c]
  exact ⟨s'', hs'', by rw [hb] at h''; exact h''⟩

theorem mem_iff_of_forall_mem {Γ : Type} [Group Γ] [Finite Γ] (T : Subgroup Γ) (Ψ : Γ ≃* Γ)
    (h : ∀ t ∈ T, Ψ t ∈ T) (t : Γ) : t ∈ T ↔ Ψ t ∈ T := by
  refine ⟨h t, fun ht => ?_⟩
  have hle : T.map Ψ.toMonoidHom ≤ T := by
    rintro _ ⟨s, hs, rfl⟩
    exact h s hs
  have hcard : Nat.card T ≤ Nat.card (T.map Ψ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective Ψ.injective]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [← heq] at ht
  obtain ⟨s, hs, hst⟩ := ht
  have : s = t := Ψ.injective hst
  rwa [← this]

end Abstract

section Concrete

variable {K : Type} [Field K] [CharP K 2]

abbrev rtB (b : Blk) (s : K) : SL3 K := rt b.2 s

abbrev RB (b : Blk) (s : K) : PSL3 K := QuotientGroup.mk (rtB b s)

omit [CharP K 2] in
theorem commute_rt_same {i j : Fin 3} (h : i ≠ j) (s s' : K) : Commute (rt h s) (rt h s') := by
  show rt h s * rt h s' = rt h s' * rt h s
  rw [← rt_add, ← rt_add, add_comm]

theorem commute_RB_iff (b b' : Blk) {s s' : K} (hs : s ≠ 0) (hs' : s' ≠ 0) :
    Commute (RB b s) (RB b' s') ↔ BComm b b' := by
  rcases b with ⟨⟨i, j⟩, hij⟩
  rcases b' with ⟨⟨k, l⟩, hkl⟩
  constructor
  · intro h
    have hc := commute_of_mk_commute (rt_mul_self hij s) (rt_mul_self hkl s') h
    by_contra hbc
    simp only [BComm, not_and_or, not_not] at hbc
    by_cases hjk : j = k
    · subst hjk
      by_cases hil : i = l
      · subst hil
        exact not_commute_rt_opp hij hs hs' hc
      · exact not_commute_rt_chain hij hkl hil hs hs' hc
    · have hli : l = i := by
        rcases hbc with h1 | h1
        · exact absurd h1 hjk
        · exact h1
      subst hli
      exact not_commute_rt_chain hkl hij (fun e => hjk e.symm) hs' hs hc.symm
  · intro hbc
    exact (commute_rt hij hkl hbc.1 hbc.2 s s').map (QuotientGroup.mk' _)

theorem exists_third' : ∀ i j : Fin 3, i ≠ j → ∃ c : Fin 3, c ≠ i ∧ c ≠ j := by decide

theorem isRoot_iff {p : ℕ} {ζ : Kˣ} (hζ : IsZeta p ζ) (u : PSL3 K) :
    IsRoot (Tbar p K) u ↔ ∃ (b : Blk) (s : K), s ≠ 0 ∧ u = RB b s := by
  constructor
  · rintro ⟨hu1, hu2, hu3, t, ht, ht1, htu⟩
    obtain ⟨x, hx2, rfl⟩ := exists_involution_lift hu2
    have hx1 : x ≠ 1 := fun h => hu1 (by rw [h, QuotientGroup.mk_one])
    obtain ⟨t₀, ht₀, rfl⟩ := mem_Tbar_iff.1 ht
    have htc : t₀ ∉ Subgroup.center (SL3 K) := fun h => ht1 ((QuotientGroup.eq_one_iff _).2 h)
    have hinv2 : ∀ t' : SL3 K, t' * x * t'⁻¹ * (t' * x * t'⁻¹) = 1 := by
      intro t'
      calc t' * x * t'⁻¹ * (t' * x * t'⁻¹) = t' * (x * x) * t'⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    have htx : t₀ * x = x * t₀ := by
      have h1 : t₀ * x * t₀⁻¹ = x := by
        refine eq_of_mk_eq_of_involution (hinv2 t₀) hx2 ?_
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, htu.eq, mul_assoc,
          mul_inv_cancel, mul_one]
      exact mul_inv_eq_iff_eq_mul.1 h1
    have hcomm : ∀ t' ∈ Tor p K, Commute x (t' * x * t'⁻¹) := by
      intro t' ht'
      have h1 := hu3 (QuotientGroup.mk t') (mem_Tbar_iff.2 ⟨t', ht', rfl⟩)
      refine commute_of_mk_commute hx2 (hinv2 t') ?_
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact h1
    obtain ⟨i, j, h, s, hs, rfl⟩ := eq_rt_of_commute_conj hζ hx2 hx1 ht₀ htc htx hcomm
    exact ⟨⟨(i, j), h⟩, s, hs, rfl⟩
  · rintro ⟨b, s, hs, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact hs ((Matrix.SpecialLinearGroup.transvection_mem_center_iff b.2 s).1
        ((QuotientGroup.eq_one_iff _).1 h))
    · rw [← QuotientGroup.mk_mul, rt_mul_self, QuotientGroup.mk_one]
    · intro t ht
      obtain ⟨t₀, ht₀, rfl⟩ := mem_Tbar_iff.1 ht
      obtain ⟨v, -, hv, rfl⟩ := mem_Tor_iff.1 ht₀
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        diagSL_conj_rt]
      exact (commute_rt_same b.2 s _).map (QuotientGroup.mk' _)
    · obtain ⟨c, hci, hcj⟩ := exists_third' b.1.1 b.1.2 b.2
      refine ⟨QuotientGroup.mk (tNon ζ c), mem_Tbar_iff.2 ⟨_, tNon_mem hζ c, rfl⟩, ?_, ?_⟩
      · intro h
        exact tNon_not_center hζ c ((QuotientGroup.eq_one_iff _).1 h)
      · have h := diagSL_conj_rt (nonreg ζ c) (prod_nonreg ζ c) b.2 s
        have e : ((nonreg ζ c b.1.1 : Kˣ) : K) * (((nonreg ζ c b.1.2)⁻¹ : Kˣ) : K) * s = s := by
          rw [nonreg_of_ne ζ hci.symm, nonreg_of_ne ζ hcj.symm, ← Units.val_mul, mul_inv_cancel,
            Units.val_one, one_mul]
        rw [e] at h
        have h2 : tNon ζ c * rtB b s = rtB b s * tNon ζ c := mul_inv_eq_iff_eq_mul.1 h
        exact (show Commute (tNon ζ c) (rtB b s) from h2).map (QuotientGroup.mk' _)

end Concrete

end CFSG.RankThree.PartOne.KFOUT3

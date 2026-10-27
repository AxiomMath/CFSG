module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D3Lie
public import CFSG.Quasithin.Vol2.GoldschmidtF431D3QChar

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.D4Hex
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

section V


@[expose] noncomputable def d3V : Subgroup (MulAut D) := d4V.map (MulAut.conj : D →* MulAut D)

theorem d3V_le_centralizer : d3V ≤ Subgroup.centralizer ({d3t} : Set (MulAut D)) := by
  rintro _ ⟨v, hv, rfl⟩
  rw [d3t, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  exact congrArg MulAut.conj (Subgroup.mem_centralizer_singleton_iff.1 (d4V_le_centralizer hv))

theorem card_d3V (hs : IsSimpleGroup D) : Nat.card d3V = 4 := by
  rw [d3V, Subgroup.card_map_of_injective (conj_injective hs)]
  exact card_d4V

theorem d3V_comm : ∀ a ∈ d3V, ∀ b ∈ d3V, a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, d4V_comm a ha b hb]

theorem d3V_sq : ∀ a ∈ d3V, a ^ 2 = 1 := by
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_pow, d4V_sq a ha, map_one]

theorem zElt_mem_d4V {p : Fin 819} (hp : p ∈ line0) : zElt p ∈ d4V := by
  simp only [line0, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · rw [zElt_zero]
    exact mem_d4V_iff.2 (Or.inr (Or.inl rfl))
  · exact mem_d4V_iff.2 (Or.inr (Or.inr (Or.inl rfl)))
  · exact mem_d4V_iff.2 (Or.inr (Or.inr (Or.inr rfl)))

end V

section VNorm


theorem pt0_mem_line0 : pt0 ∈ line0 := Finset.mem_insert_self _ _

theorem pt1_mem_line0 : pt1 ∈ line0 :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem pt5_mem_line0 : pt5 ∈ line0 :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

theorem aut_mem_d4V {α : MulAut D} (h : α d4t = d4t) {v : D} (hv : v ∈ d4V) : α v ∈ d4V := by
  rcases mem_d4V_iff.1 hv with rfl | rfl | rfl | rfl
  · rw [map_one]
    exact d4V.one_mem
  · have h1 := autPt_apply α pt0
    rw [zElt_zero] at h1
    rw [← h1]
    exact zElt_mem_d4V (autPt_mem_line0 h pt0_mem_line0)
  · have h1 := autPt_apply α pt1
    show α (zElt pt1) ∈ d4V
    rw [← h1]
    exact zElt_mem_d4V (autPt_mem_line0 h pt1_mem_line0)
  · have h1 := autPt_apply α pt5
    show α (zElt pt5) ∈ d4V
    rw [← h1]
    exact zElt_mem_d4V (autPt_mem_line0 h pt5_mem_line0)

theorem d3V_norm (hs : IsSimpleGroup D) :
    ∀ x ∈ Subgroup.centralizer ({d3t} : Set (MulAut D)), ∀ v ∈ d3V, x * v * x⁻¹ ∈ d3V := by
  intro x hx v hv
  obtain ⟨v0, hv0, rfl⟩ := hv
  have hfix : x d4t = d4t := (mem_centralizer_conj_iff (conj_injective hs) x d4t).1 hx
  rw [aut_mul_conj_inv]
  exact ⟨x v0, aut_mem_d4V hfix hv0, rfl⟩

end VNorm

section VConj


theorem d3V_conj : ∀ v ∈ d3V, v ≠ 1 → ∃ x ∈ Subgroup.centralizer ({d3t} : Set (MulAut D)),
    v = x * d3z * x⁻¹ := by
  rintro _ ⟨v0, hv0, rfl⟩ hv1
  have hv01 : v0 ≠ 1 := fun h => hv1 (by rw [h, map_one])
  obtain ⟨x, hx, e⟩ := d4V_conj v0 hv0 hv01
  refine ⟨MulAut.conj x, ?_, ?_⟩
  · rw [d3t, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg MulAut.conj (Subgroup.mem_centralizer_singleton_iff.1 (d4Ct_le_centralizer hx))
  · rw [e, d3z]
    simp [map_mul, map_inv]

theorem d3_exists_q (hs : IsSimpleGroup D) : ∃ q ∈ Subgroup.centralizer ({d3t} : Set (MulAut D)),
    (∀ v ∈ d3V, q * v = v * q) ∧ q ^ 2 ∈ d3V ∧ q ^ 2 ≠ 1 := by
  obtain ⟨q0, hq0, hA, hB, hC, hsq⟩ := exists_q
  refine ⟨MulAut.conj q0, ?_, ?_, ?_, ?_⟩
  · rw [d3t, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg MulAut.conj (Subgroup.mem_centralizer_singleton_iff.1 (d4Ct_le_centralizer hq0))
  · rintro _ ⟨v0, hv0, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    rcases mem_d4V_iff.1 hv0 with rfl | rfl | rfl | rfl
    · simp
    · exact hA
    · exact hB
    · exact hC
  · rw [← map_pow, pow_two]
    refine ⟨q0 * q0, ?_, rfl⟩
    rcases hsq with h | h | h <;> rw [h]
    · exact mem_d4V_iff.2 (Or.inr (Or.inl rfl))
    · exact mem_d4V_iff.2 (Or.inr (Or.inr (Or.inl rfl)))
    · exact mem_d4V_iff.2 (Or.inr (Or.inr (Or.inr rfl)))
  · intro h
    rw [← map_pow, pow_two] at h
    have h1 : q0 * q0 = 1 := conj_injective hs (h.trans (map_one _).symm)
    rcases hsq with h2 | h2 | h2 <;> rw [h2] at h1
    · exact d4z_sq.2 h1
    · exact vB_sq.2 h1
    · exact vC_sq.2 h1

end VConj

section Cop


theorem centralizer_d3t_inf_range (hs : IsSimpleGroup D) :
    Subgroup.centralizer ({d3t} : Set (MulAut D)) ⊓ (MulAut.conj : D →* MulAut D).range =
      (Subgroup.centralizer ({d4t} : Set D)).map (MulAut.conj : D →* MulAut D) := by
  ext α
  constructor
  · rintro ⟨hα, g, rfl⟩
    refine ⟨g, ?_, rfl⟩
    have hα' : MulAut.conj g ∈ Subgroup.centralizer ({d3t} : Set (MulAut D)) := hα
    rw [d3t, mem_centralizer_conj_iff (conj_injective hs)] at hα'
    simp only [MulAut.conj_apply] at hα'
    show g ∈ Subgroup.centralizer ({d4t} : Set D)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * d4t = (g * d4t * g⁻¹) * g := by group
      _ = d4t * g := by rw [hα']
  · rintro ⟨g, hg, rfl⟩
    refine ⟨?_, g, rfl⟩
    show MulAut.conj g ∈ Subgroup.centralizer ({d3t} : Set (MulAut D))
    rw [d3t, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg MulAut.conj (Subgroup.mem_centralizer_singleton_iff.1 hg)

theorem d3_Ct_dvd (hs : IsSimpleGroup D) (hcard : Nat.card (MulAut D) ∣ 3 * Nat.card D) :
    Nat.card (Subgroup.centralizer ({d3t} : Set (MulAut D))) ∣ 9216 := by
  have hinj := conj_injective hs
  have hN := normal_conj_range D
  set C := Subgroup.centralizer ({d3t} : Set (MulAut D)) with hC
  set Inn := (MulAut.conj : D →* MulAut D).range with hInn
  have h1 := Subgroup.card_mul_index (Inn.subgroupOf C)
  have h2 : Nat.card (Inn.subgroupOf C) = 3072 := by
    rw [← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Inn ⊓ C ≤ C)).toEquiv,
      inf_comm, hC, hInn, centralizer_d3t_inf_range hs,
      Subgroup.card_map_of_injective hinj, centralizer_d4t_eq, card_d4Ct]
  have h3 : (Inn.subgroupOf C).index ∣ 3 := by
    have h4 : (Inn.subgroupOf C).index = Inn.relIndex C := rfl
    rw [h4]
    refine (Subgroup.relIndex_dvd_index_of_normal Inn C).trans ?_
    have h5 := Subgroup.card_mul_index Inn
    have hD : Nat.card Inn = Nat.card D :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [hD] at h5
    have hpos : 0 < Nat.card D := by
      have := finite_D
      exact Nat.card_pos
    rw [← h5, mul_comm 3] at hcard
    exact Nat.dvd_of_mul_dvd_mul_left hpos hcard
  rw [← h1, h2]
  exact (Nat.mul_dvd_mul_left 3072 h3).trans (by norm_num)

theorem d3_Ct_cop (hs : IsSimpleGroup D) (hcard : Nat.card (MulAut D) ∣ 3 * Nat.card D) :
    Nat.Coprime (Nat.card (Subgroup.centralizer ({d3t} : Set (MulAut D)))) 65 :=
  Nat.Coprime.coprime_dvd_left (d3_Ct_dvd hs hcard) (by norm_num)

end Cop

section Fusion


theorem d4_fusion_Q : ∀ u ∈ Subgroup.centralizer ({d4t} : Set D), IsConj d4z u → u ∈ d4V ∨
    ∃ n ∈ d4N, ∃ a ∈ d4U, ∃ b ∈ d4U, u = n * a * n⁻¹ ∧ d4t = n * b * n⁻¹ ∧
      ∃ b' ∈ d4U, b' ∉ d4Q ∧ Relation.ReflTransGen (PairLink d4U d4H d4N) (a, b) (d4z, b') := by
  intro u hu hconj
  obtain ⟨i, rfl⟩ := exists_zElt_of_isConj hconj
  have hcov := locF_parts.2.2.1 i.1 (by have := i.2; omega)
  rw [locCz_eq] at hcov
  rcases hcov with h | h | h | h | h
  · exfalso
    have hc := Subgroup.mem_centralizer_singleton_iff.1 hu
    have := (locComm_iff (validR_cz i.2) validR_t0R (repE_zElt i) repE_t0R).2 hc
    rw [this] at h
    exact absurd h (by simp)
  · have hi : i = pt0 := Fin.ext h
    subst hi
    rw [zElt_zero]
    exact Or.inl (mem_d4V_iff.2 (Or.inr (Or.inl rfl)))
  · have hi : i = pt1 := Fin.ext h
    subst hi
    exact Or.inl (mem_d4V_iff.2 (Or.inr (Or.inr (Or.inl rfl))))
  · have hi : i = pt5 := Fin.ext h
    subst hi
    exact Or.inl (mem_d4V_iff.2 (Or.inr (Or.inr (Or.inr rfl))))
  · right
    obtain ⟨hlt, heq⟩ := memR_spec h
    obtain ⟨c, hc, hrep⟩ := exists_conj_mem_of_classTreeOK cGens_hyp' repE_u0 locF_parts.2.1 _ hlt
    rw [heq] at hrep
    have hu' : zElt i = c * d4Word locU0Word * c⁻¹ :=
      eq_of_repE d4E_injective (repE_zElt i) hrep
    have hct : c * d4t = d4t * c :=
      Subgroup.mem_centralizer_singleton_iff.1 (d4Ct_le_centralizer hc)
    obtain ⟨b', hb'U, hb'Q, hchain⟩ := pair_chain_spec
    exact ⟨c, d4Ct_le_d4N hc, d4Word locU0Word, u0_mem_d4U, d4t, d4t_mem_d4U, hu',
      by rw [hct]; group, b', hb'U, hb'Q, hchain⟩

theorem pairLink_conj {p p' : D × D} (h : PairLink d4U d4H d4N p p') :
    PairLink d3T (autStab d4H) (autStab d4N) (MulAut.conj p.1, MulAut.conj p.2)
      (MulAut.conj p'.1, MulAut.conj p'.2) := by
  obtain ⟨h1, h2, h3, h4, c, hc, e1, e2⟩ := h
  refine ⟨conj_mem_d3T h1, conj_mem_d3T h2, conj_mem_d3T h3, conj_mem_d3T h4, MulAut.conj c,
    ?_, ?_, ?_⟩
  · rcases hc with hc | hc
    · exact Or.inl (conj_mem_autStab hc)
    · exact Or.inr (conj_mem_autStab hc)
  · show MulAut.conj p'.1 = MulAut.conj c * MulAut.conj p.1 * (MulAut.conj c)⁻¹
    rw [e1]
    simp [map_mul, map_inv]
  · show MulAut.conj p'.2 = MulAut.conj c * MulAut.conj p.2 * (MulAut.conj c)⁻¹
    rw [e2]
    simp [map_mul, map_inv]

end Fusion

section Main


theorem d3_fusion (hs : IsSimpleGroup D) :
    ∀ u ∈ Subgroup.centralizer ({d3t} : Set (MulAut D)), IsConj d3z u → u ∈ d3V ∨
      ∃ n ∈ autStab d4N, ∃ a ∈ d3T, ∃ b ∈ d3T, u = n * a * n⁻¹ ∧ d3t = n * b * n⁻¹ ∧
        ∃ b' ∈ d3T, Relation.ReflTransGen (PairLink d3T (autStab d4H) (autStab d4N)) (a, b)
          (d3z, b') ∧ ∀ h ∈ autStab d4H, h * d3t * h⁻¹ ≠ b' := by
  intro u hu hconj
  have hinj := conj_injective hs
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  rw [d3z, aut_mul_conj_inv] at hc
  obtain ⟨c', hc'⟩ := exists_aut_d4z c
  have hu0conj : IsConj d4z (c d4z) := isConj_iff.2 ⟨c', hc'.symm⟩
  have hu0 : c d4z ∈ Subgroup.centralizer ({d4t} : Set D) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hu
    rw [← hc, d3t, ← map_mul, ← map_mul] at h1
    exact hinj h1
  rcases d4_fusion_Q _ hu0 hu0conj with hV | ⟨n, hn, a, ha, b, hb, hun, htn, b', hb', hb'Q, hchain⟩
  · left
    rw [← hc]
    exact ⟨_, hV, rfl⟩
  · right
    refine ⟨MulAut.conj n, conj_mem_autStab hn, MulAut.conj a, conj_mem_d3T ha, MulAut.conj b,
      conj_mem_d3T hb, ?_, ?_, MulAut.conj b', conj_mem_d3T hb', ?_, ?_⟩
    · rw [← hc, hun]
      simp [map_mul, map_inv]
    · rw [d3t, htn]
      simp [map_mul, map_inv]
    · exact Relation.ReflTransGen.lift
        (fun p : D × D => ((MulAut.conj p.1 : MulAut D), (MulAut.conj p.2 : MulAut D)))
        (fun _ _ h => pairLink_conj h) (a, b) (d4z, b') hchain
    · intro h hh heq
      rw [d3t, aut_mul_conj_inv] at heq
      exact hb'Q (hinj heq ▸ d4Q_char hh d4t d4t_mem_d4Q)

theorem d3_Loc442DatumX (hs : IsSimpleGroup D)
    (hCU : ∀ x : D, (∀ u ∈ d4U, x * u = u * x) → x = 1 ∨ x = d4z)
    (hodd : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index)
    (hcard : Nat.card (MulAut D) ∣ 3 * Nat.card D) :
    ∃ q, Loc442DatumX (autStab d4H) (autStab d4N) d3T d3z d3t d3V q := by
  obtain ⟨q, hqC, hqV, hq2, hq2ne⟩ := d3_exists_q hs
  exact ⟨q,
    { lie := d3_F431LieI hs hCU hodd
      V_le := d3V_le_centralizer
      V_card := card_d3V hs
      V_comm := d3V_comm
      V_sq := d3V_sq
      V_norm := d3V_norm hs
      V_conj := d3V_conj
      q_mem := hqC
      q_comm := hqV
      q_sq := hq2
      q_sq_ne := hq2ne
      Ct_cop := d3_Ct_cop hs hcard
      fusion := d3_fusion hs }⟩

end Main

end CFSG.Quasithin.D4Hex

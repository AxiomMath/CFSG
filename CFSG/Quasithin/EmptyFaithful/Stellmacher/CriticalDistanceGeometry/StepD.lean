module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepDEF0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7

namespace F53.Stellmacher

open CosetGeom F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

set_option linter.unusedSectionVars false

omit [Finite G] in
theorem le_normalizer_of_conj_mem {X K : Subgroup G}
    (h : ∀ x ∈ X, ∀ w ∈ K, x * w * x⁻¹ ∈ K) : X ≤ Subgroup.normalizer (K : Set G) := by
  intro x hx
  refine Subgroup.mem_normalizer_iff.mpr fun w => ⟨h x hx w, fun hw => ?_⟩
  have := h x⁻¹ (X.inv_mem hx) _ hw
  simpa [mul_assoc] using this

omit [Finite G] in
theorem normalizes_fixedSpace {H0 Za Zc Zp Qc : Subgroup G} (hZaH0 : Za ≤ H0)
    (hcomm : ⁅H0, Zp⁆ ≤ Za) (hZc : Zc ≤ Subgroup.normalizer (Za : Set G))
    (hQc : ∀ q ∈ Qc, ∀ c ∈ Zc, q * c = c * q) (hQN : Qc ≤ Subgroup.normalizer (Za : Set G)) :
    Qc ⊔ Zp ≤ Subgroup.normalizer ((H0 ⊓ (Zc ⊔ Za) : Subgroup G) : Set G) := by
  refine sup_le ?_ ?_
  · refine le_normalizer_of_conj_mem fun q hq w hw => ?_
    obtain ⟨hwH0, hwW⟩ := Subgroup.mem_inf.mp hw
    obtain ⟨c, hc, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hZc w hwW
    have hcH0 : c ∈ H0 := by
      have := H0.mul_mem hwH0 (H0.inv_mem (hZaH0 ha))
      simpa using this
    have h1 : q * a * q⁻¹ ∈ Za := (Subgroup.mem_normalizer_iff.mp (hQN hq) a).mp ha
    have h2 : q * (c * a) * q⁻¹ = c * (q * a * q⁻¹) := by
      have : q * c * q⁻¹ = c := by rw [hQc q hq c hc]; group
      calc q * (c * a) * q⁻¹ = (q * c * q⁻¹) * (q * a * q⁻¹) := by group
        _ = _ := by rw [this]
    rw [h2]
    exact Subgroup.mem_inf.mpr ⟨H0.mul_mem hcH0 (hZaH0 h1), Subgroup.mul_mem_sup hc h1⟩
  · refine le_normalizer_of_conj_mem fun z hz w hw => ?_
    obtain ⟨hwH0, hwW⟩ := Subgroup.mem_inf.mp hw
    have hc : w * z * w⁻¹ * z⁻¹ ∈ Za := by
      have := hcomm (Subgroup.commutator_mem_commutator hwH0 hz)
      rwa [commutatorElement_def] at this
    have h2 : z * w * z⁻¹ = (w * z * w⁻¹ * z⁻¹)⁻¹ * w := by group
    rw [h2]
    have hinv := Za.inv_mem hc
    exact Subgroup.mem_inf.mpr ⟨H0.mul_mem (hZaH0 hinv) hwH0,
      Subgroup.mul_mem _ (Subgroup.mem_sup_right hinv) hwW⟩

theorem relIndex_ne_zero' (A B : Subgroup G) : A.relIndex B ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

theorem relIndex_Zv_smul (g : ↥(H ⊔ M)) (δ μ l : Geo H M) :
    (Zv (g • δ) ⊓ (Zv (g • μ) ⊔ Zv (g • l))).relIndex (Zv (g • δ)) =
      (Zv δ ⊓ (Zv μ ⊔ Zv l)).relIndex (Zv δ) := by
  rw [Zv_smul, Zv_smul, Zv_smul, ← conjSub_sup, ← conjSub_inf]
  exact Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj (g : G)).toMonoidHom) _ _
    (MulAut.conj (g : G)).injective

theorem smul_mem_nbrs_iff (g : ↥(H ⊔ M)) {l δ : Geo H M} : g • δ ∈ nbrs (g • l) ↔ δ ∈ nbrs l :=
  smul_adj g

theorem exists_third_nbr (hA : F53Amalgam H M S) {l β μ : Geo H M} (hv : vtype l = true)
    (hβ : β ∈ nbrs l) (hμ : μ ∈ nbrs l) (hne : β ≠ μ) :
    ∃ ν ∈ nbrs l, ν ≠ β ∧ ν ≠ μ ∧ ∀ w ∈ nbrs l, w = β ∨ w = μ ∨ w = ν := by
  have hcard : (nbrs l).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]; exact card_nbrs_true hA hv
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := Set.ncard_eq_three.mp hcard
  rw [hs] at hβ hμ ⊢
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ hμ ⊢
  rcases hβ with rfl | rfl | rfl <;> rcases hμ with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hne
    | (refine ⟨x, by simp, ?_, ?_, by simp⟩ <;> grind)
    | (refine ⟨y, by simp, ?_, ?_, by simp⟩ <;> grind)
    | (refine ⟨z, by simp, ?_, ?_, by simp⟩ <;> grind)

section Standing

variable {α β α' : Geo H M}

theorem Zv_le_Vn_of_mem_nbrs {δ μ : Geo H M} (h : μ ∈ nbrs δ) : Zv μ ≤ Vn δ :=
  le_iSup₂_of_le (f := fun (ν : Geo H M) (_ : ν ∈ nbrs δ) => Zv ν) μ h le_rfl

theorem Zv_le_Vn_self (hA : F53Amalgam H M S) (δ : Geo H M) : Zv δ ≤ Vn δ := by
  obtain ⟨μ, hμ⟩ := exists_adj δ
  have hμn : μ ∈ nbrs δ := hμ
  rw [Zv_eq_conjClosure (sylow_stab_inf_left hA hμn)]
  refine conjClosure_le fun h hh z hz => ?_
  have hz' : z ∈ Vn δ := Zv_le_Vn_of_mem_nbrs hμn ((omegaOneCenter_le_Zv hA hμn).2.2 hz)
  exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ hh) z).mp hz'

theorem Vn_le_Qv' (hb2 : 2 ≤ bMin H M) (δ : Geo H M) : Vn δ ≤ Qv δ :=
  iSup₂_le fun _ hμ => Zv_le_Qv_of_mem_nbrs (mem_nbrs_symm' hμ) hb2

theorem claim3'_core (hA : F53Amalgam H M S) (h28 : Hss28At H M) (hc : IsCritData α β α')
    (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) (hb2 : 2 ≤ bMin H M)
    {H0 : Subgroup G} (hZ : Zv α ≤ H0) (hcm : ⁅H0, Zv α'⁆ ≤ Zv α)
    {γ μ : Geo H M} (hγ : γ ∈ nbrs α) (hμ : μ ∈ nbrs α) (hγβ : γ ≠ β) :
    H0 ⊓ (Zv γ ⊔ Zv α) ≤ Zv μ ⊔ Zv α := by
  obtain ⟨-, hZα'G⟩ := Zv_le_stab_of_comm_ne hA hc hcomm
  have hβn : β ∈ nbrs α := hc.adj
  have hZα'β : Zv α' ≤ stab β :=
    Zv_le_stab_of_dist_le' hA (by have := hc.dist_eq'; rw [CosetGeom.dist_comm]; omega)
  have hnle := not_le_Qv_of_comm_ne hA hcomm
  have hZγQ : Zv γ ≤ Qv α := Zv_le_Qv_of_mem_nbrs (mem_nbrs_symm' hγ) hb2
  have hQγst : Qv γ ≤ stab α := Qv_le_stab_of_mem_nbrs hA (mem_nbrs_symm' hγ)
  have hQN : Qv γ ≤ Subgroup.normalizer (Zv α : Set G) := hQγst.trans (stab_le_normalizer_Zv hA α)
  have hN : Qv γ ⊔ Zv α' ≤ Subgroup.normalizer ((H0 ⊓ (Zv γ ⊔ Zv α) : Subgroup G) : Set G) :=
    normalizes_fixedSpace hZ hcm
      (hZγQ.trans ((pCoreOf_le 2 (stab α) : Qv α ≤ stab α).trans (stab_le_normalizer_Zv hA α)))
      (fun q hq c hc => (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA γ hc).2) q hq) hQN
  have hst : Zv α' ⊔ (stab α ⊓ stab γ) = stab α :=
    sup_edge_eq_stab hA hv hβn hγ (Ne.symm hγβ) (le_inf hZα'G hZα'β) hnle
  have h28' : Qv α ⊔ Qv γ = stab α ⊓ stab γ := h28 (by omega) α γ hγ hc.bAt_eq
  have hXQ : stab α ≤ (Qv γ ⊔ Zv α') ⊔ Qv α := by
    rw [← hst, ← h28']
    exact sup_le (le_sup_of_le_left le_sup_right)
      (sup_le le_sup_right (le_sup_of_le_left le_sup_left))
  have hXN : Qv γ ⊔ Zv α' ≤ Subgroup.normalizer (Qv α : Set G) :=
    (sup_le hQγst hZα'G).trans (le_normalizer_pCoreOf 2 (stab α))
  obtain ⟨g, hg, hgγ⟩ := stab_transitive_on_nbrs hγ hμ
  obtain ⟨x, hx, q, hq, hxq⟩ := exists_mul_of_mem_sup_of_le_normalizer hXN (g : G) (hXQ hg)
  have hqst : q ∈ stab γ := Qv_le_stab_of_mem_nbrs hA hγ hq
  have hZμ : Zv μ = conjSub x (Zv γ) := by
    rw [← hgγ, Zv_smul, hxq, conjSub_mul,
      conjSub_eq_of_mem_normalizer (stab_le_normalizer_Zv hA γ hqst)]
  have hZα : conjSub x (Zv α) = Zv α :=
    conjSub_eq_of_mem_normalizer (stab_le_normalizer_Zv hA α ((sup_le hQγst hZα'G) hx))
  have hfix : conjSub x (H0 ⊓ (Zv γ ⊔ Zv α)) = H0 ⊓ (Zv γ ⊔ Zv α) :=
    conjSub_eq_of_mem_normalizer (hN hx)
  calc H0 ⊓ (Zv γ ⊔ Zv α) = conjSub x (H0 ⊓ (Zv γ ⊔ Zv α)) := hfix.symm
    _ ≤ conjSub x (Zv γ ⊔ Zv α) := conjSub_mono x inf_le_right
    _ = Zv μ ⊔ Zv α := by rw [conjSub_sup, hZα, ← hZμ]

theorem relIndex_le_two_of_core {H0 : Subgroup G} {δ μ α : Geo H M}
    (hZδ : Zv δ ≤ Vn α) (hidx : H0.relIndex (Vn α) ≤ 2)
    (hcore : H0 ⊓ (Zv δ ⊔ Zv α) ≤ Zv μ ⊔ Zv α) :
    (Zv δ ⊓ (Zv μ ⊔ Zv α)).relIndex (Zv δ) ≤ 2 := by
  have h1 : Zv δ ⊓ H0 ≤ Zv δ ⊓ (Zv μ ⊔ Zv α) := fun x hx =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hcore
      (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2,
        Subgroup.mem_sup_left (Subgroup.mem_inf.mp hx).1⟩)⟩
  have h2 : H0.relIndex (Zv δ) ≤ H0.relIndex (Vn α) :=
    Subgroup.relIndex_le_of_le_right hZδ (relIndex_ne_zero' _ _)
  calc (Zv δ ⊓ (Zv μ ⊔ Zv α)).relIndex (Zv δ)
      ≤ (Zv δ ⊓ H0).relIndex (Zv δ) := Subgroup.relIndex_le_of_le_left h1 (relIndex_ne_zero' _ _)
    _ = H0.relIndex (Zv δ) := by rw [inf_comm, Subgroup.inf_relIndex_right]
    _ ≤ H0.relIndex (Vn α) := h2
    _ ≤ 2 := hidx

theorem claim3'_at (hA : F53Amalgam H M S) (h28 : Hss28At H M) (hc : IsCritData α β α')
    (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) (hb2 : 2 ≤ bMin H M)
    (hH3 : ∃ H0 : Subgroup G, Zv α ≤ H0 ∧ H0 ≤ Vn α ∧ H0.relIndex (Vn α) ≤ 2 ∧
      ⁅H0, Zv α'⁆ ≤ Zv α) :
    ∀ δ ∈ nbrs α, ∀ μ ∈ nbrs α, δ ≠ μ → (Zv δ ⊓ (Zv μ ⊔ Zv α)).relIndex (Zv δ) ≤ 2 := by
  obtain ⟨H0, hZ, -, hidx, hcm⟩ := hH3
  have hZV : ∀ δ ∈ nbrs α, Zv δ ≤ Vn α := fun δ hδ => Zv_le_Vn_of_mem_nbrs hδ
  have hpair : ∀ δ ∈ nbrs α, ∀ μ ∈ nbrs α, δ ≠ β →
      (Zv δ ⊓ (Zv μ ⊔ Zv α)).relIndex (Zv δ) ≤ 2 := fun δ hδ μ hμ hδβ =>
    relIndex_le_two_of_core (hZV δ hδ) hidx
      (claim3'_core hA h28 hc hv hcomm hb2 hZ hcm hδ hμ hδβ)
  intro δ hδ μ hμ hne
  by_cases hδβ : δ = β
  · rw [hδβ] at hδ hne ⊢
    obtain ⟨ν, hνn, hνβ, hνμ, hall⟩ := exists_third_nbr hA hv hδ hμ hne
    obtain ⟨g, hg, hgν⟩ := stab_transitive_on_nbrs hνn hδ
    have hgα : g • α = α := smul_eq_of_mem_stab hg
    have hmem : ∀ w ∈ nbrs α, g • w ∈ nbrs α := fun w hw => by
      have := (smul_mem_nbrs_iff g (l := α) (δ := w)).mpr hw
      rwa [hgα] at this
    have hinj : ∀ x y : Geo H M, g • x = g • y → x = y := fun x y h => smul_left_cancel g h
    have hb1 : g • β ≠ β := fun h => hνβ (hinj _ _ (hgν.trans h.symm))
    have hm1 : g • μ ≠ β := fun h => hνμ (hinj _ _ (hgν.trans h.symm))
    have hbm : g • β ≠ g • μ := fun h => hne (hinj _ _ h)
    rcases hall (g • β) (hmem β hδ) with h | h | h
    · exact absurd h hb1
    · have := relIndex_Zv_smul g ν β α
      rw [hgν, h, hgα] at this
      rw [this]
      exact hpair ν hνn β hδ hνβ
    · have h' : g • μ = μ := by
        rcases hall (g • μ) (hmem μ hμ) with h2 | h2 | h2
        · exact absurd h2 hm1
        · exact h2
        · exact absurd (h.trans h2.symm) hbm
      have := relIndex_Zv_smul g ν μ α
      rw [hgν, h', hgα] at this
      rw [this]
      exact hpair ν hνn μ hμ hνβ
  · exact hpair δ hδ μ hμ hδβ

theorem claim3'_transport (hA : F53Amalgam H M S) (h28 : Hss28At H M) (hc : IsCritData α β α')
    (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) (hb2 : 2 ≤ bMin H M)
    (hH3 : ∃ H0 : Subgroup G, Zv α ≤ H0 ∧ H0 ≤ Vn α ∧ H0.relIndex (Vn α) ≤ 2 ∧
      ⁅H0, Zv α'⁆ ≤ Zv α) :
    ∀ l : Geo H M, vtype l = true → ∀ δ ∈ nbrs l, ∀ μ ∈ nbrs l, δ ≠ μ →
      (Zv δ ⊓ (Zv μ ⊔ Zv l)).relIndex (Zv δ) ≤ 2 := by
  intro l hl δ hδ μ hμ hne
  obtain ⟨h, rfl⟩ := exists_smul_of_vtype_eq (δ := α) (δ' := l) (by rw [hl, hv])
  obtain ⟨δ0, rfl⟩ : ∃ δ0, δ = h • δ0 := ⟨h⁻¹ • δ, by simp⟩
  obtain ⟨μ0, rfl⟩ : ∃ μ0, μ = h • μ0 := ⟨h⁻¹ • μ, by simp⟩
  rw [relIndex_Zv_smul]
  exact claim3'_at hA h28 hc hv hcomm hb2 hH3 δ0 ((smul_mem_nbrs_iff h).mp hδ) μ0
    ((smul_mem_nbrs_iff h).mp hμ) fun h' => hne (by rw [h'])

theorem commutator_le_of_decomp (hA : F53Amalgam H M S) {B : Subgroup G}
    (hZα'G : Zv α' ≤ stab α) (hdec : ∀ x ∈ B, ∃ a ∈ Zv α, ∃ q ∈ Qv α', x = a * q) :
    ⁅B, Zv α'⁆ ≤ Zv α := by
  rw [Subgroup.commutator_le]
  intro b hb z hz
  obtain ⟨a, ha, q, hq, rfl⟩ := hdec b hb
  have hqz : q * z = z * q := ((Subgroup.mem_centralizer_iff.mp
    (Zv_le_centerOf_Qv hA α' hz).2) q hq)
  have hzN := stab_le_normalizer_Zv hA α (hZα'G hz)
  have h1 : z * a⁻¹ * z⁻¹ ∈ Zv α := (Subgroup.mem_normalizer_iff.mp hzN _).mp ((Zv α).inv_mem ha)
  rw [commutatorElement_def]
  have : a * q * z * (a * q)⁻¹ * z⁻¹ = a * (z * a⁻¹ * z⁻¹) := by
    have : q * z * q⁻¹ = z := by rw [hqz]; group
    calc a * q * z * (a * q)⁻¹ * z⁻¹ = a * (q * z * q⁻¹) * a⁻¹ * z⁻¹ := by group
      _ = _ := by rw [this]; group
  rw [this]
  exact (Zv α).mul_mem ha h1

theorem H3_of_index_two (hA : F53Amalgam H M S) (hc : IsCritData α β α') (hv : vtype α = true)
    (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) (hb2 : 2 ≤ bMin H M) (heven : Even (bMin H M))
    (hidx : (Vn α ⊓ stab α').relIndex (Vn α) ≤ 2) :
    ∃ H0 : Subgroup G, Zv α ≤ H0 ∧ H0 ≤ Vn α ∧ H0.relIndex (Vn α) ≤ 2 ∧
      ⁅H0, Zv α'⁆ ≤ Zv α := by
  obtain ⟨-, hZα'G⟩ := Zv_le_stab_of_comm_ne hA hc hcomm
  obtain ⟨-, hZαα'⟩ := Zv_le_stab_pair hA hc hcomm
  have hvα' := vtype_alpha'_of_even hA hc hv heven
  have hZV := Zv_le_Vn_self hA α
  have hK : IsPGroup 2 ↥(Vn α ⊓ stab α') :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab α)).to_le
      (inf_le_left.trans (Vn_le_Qv' hb2 α))
  have hdec : ∀ x ∈ Vn α ⊓ stab α', ∃ a ∈ Zv α, ∃ q ∈ Qv α', x = a * q := fun x hx =>
    exists_mul_of_isPGroup_of_vtype_true hA hvα' hK inf_le_right (le_inf hZV hZαα') hc.not_le x hx
  exact ⟨Vn α ⊓ stab α', le_inf hZV hZαα', inf_le_left, hidx,
    commutator_le_of_decomp hA hZα'G hdec⟩

end Standing

end F53.Stellmacher

end CFSG.Quasithin

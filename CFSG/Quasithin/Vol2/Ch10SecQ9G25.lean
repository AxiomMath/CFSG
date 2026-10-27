module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G24
public import CFSG.Quasithin.Vol2.Ch10SecQ9G17
public import CFSG.Quasithin.Vol2.Ch10SecQ9G23

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I W : Subgroup G} {s : G}

namespace C5Coord

variable (C : C5Coord L W s)

omit [Finite G] in
theorem eq_of_fix_W {k : L3.Γ}
    (hS : ((T ⊓ L).subgroupOf L).map C.D.ρ = SecD.L3.P0.map (MulAut.conj k).toMonoidHom)
    {a₀ e : G} (ha₀ : a₀ ∈ W) (hba₀ : C.D.b a₀ = L3.act k e0') (he : e ∈ W) (he1 : e ≠ 1)
    (hC : ∀ u ∈ T ⊓ L, u * e * u⁻¹ = e) : e = a₀ := by
  rcases C.fix_W hS he hC with h | h
  · exact absurd (C.D.b_inj _ he _ W.one_mem (h.trans C.b_one.symm)) he1
  · exact C.D.b_inj _ he _ ha₀ (h.trans hba₀.symm)

omit [Finite G] in
theorem eq_of_fix_Ws {k : L3.Γ}
    (hS : ((T ⊓ L).subgroupOf L).map C.D.ρ = SecD.L3.P0.map (MulAut.conj k).toMonoidHom)
    {b₀ e : G} (hb₀ : b₀ ∈ CFSG.conjugate W s) (hcb₀ : C.c b₀ = L3.act (τ3 k) e2')
    (he : e ∈ CFSG.conjugate W s) (he1 : e ≠ 1) (hC : ∀ u ∈ T ⊓ L, u * e * u⁻¹ = e) :
    e = b₀ := by
  rcases C.fix_Ws hS he hC with h | h
  · exact absurd (C.c_inj _ he _ (Subgroup.one_mem _) (h.trans C.c_one.symm)) he1
  · exact C.c_inj _ he _ hb₀ (h.trans hcb₀.symm)

end C5Coord

omit [Finite G] in
theorem conj_fix_of_T1 {u : G} (hu : u ∈ T1 T L) {e : G} (hC : ∀ x ∈ T ⊓ L, x * e * x⁻¹ = e) :
    ∀ x ∈ T ⊓ L, x * (u * e * u⁻¹) * x⁻¹ = u * e * u⁻¹ := by
  intro x hx
  have hx' : u⁻¹ * x * u ∈ T ⊓ L := by
    refine ⟨T.mul_mem (T.mul_mem (T.inv_mem hu.1) hx.1) hu.1, ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hu.2) x).mp hx.2
    simpa using this
  have := hC _ hx'
  calc x * (u * e * u⁻¹) * x⁻¹ = u * ((u⁻¹ * x * u) * e * (u⁻¹ * x * u)⁻¹) * u⁻¹ := by group
    _ = u * e * u⁻¹ := by rw [this]

theorem dichotomy_case5 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (h1011 : Stmt10_1_1)
    (hyp : Hyp10 G T L I) (h5 : Case10_1_1Five T L I) {v : G} (hv : v ∈ fsuUL T L I) :
    (∃ l ∈ L, orderOf l = 3 ∧ l * v = v * l) ∨
      ∃ g₀ ∈ L, T1 T L ≤ Subgroup.centralizer ({g₀ * v * g₀⁻¹} : Set G) := by
  obtain ⟨-, s, hsT, hsL, W, hWV1, hLW, hsup, hinf, ⟨hWc, hWnat⟩, hni⟩ := h5
  obtain ⟨C⟩ := exists_c5Coord h37 h38 h322 h1011 hyp hsL hWV1 hLW hsup hWnat hni
  have hirr : IrrG L W := by
    obtain ⟨K, _, _, -, π, hD⟩ := hWnat
    exact irrG_of_isIrrSec (B5.isIrr_of_realizes (by norm_num) hD).2
  have hirr' := irrG_conjugate hirr hsL
  have hLWs := le_normalizer_conjugate_of' hsL hLW
  have hWsV1 : CFSG.conjugate W s ≤ fsuUL T L I := hsup ▸ le_sup_right
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  have hc : ∀ a ∈ W, ∀ b ∈ CFSG.conjugate W s, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hV (hV1V (hWV1 ha)) (hV1V (hWsV1 hb))
  have hWne : ⁅W, L⁆ ≠ ⊥ := fun h => not_le_centralizer_of_natural hWnat
    (Subgroup.le_centralizer_iff.mpr (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h)))
  have hC1 := SecB.mem_centralizer_iff_of_le_fsuUL h37 h38 h322 hyp hWV1 hLW hWne
  rw [← hsup] at hv
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc hv
  rcases flag_fact (C.D.b a) (C.c b) with ⟨γ, hγ3, hγ1, hγa, hγb⟩ | ⟨h, hha, hhb⟩
  · exact Or.inl (C.exists_three_of_fix h37 h38 h1011 hyp (fun l hl => (hC1 _ l.2).mpr hl) hLW
      hLWs ha hb hγ3 hγ1 hγa hγb)
  right
  have hSyl := image_isSylowTwoOf (SecA.isSylowTwoOf_inf hyp.fsu.maximal.1) C.D.ρ C.D.ρ_surj
  obtain ⟨k, hk⟩ := SecD.L3.exists_conj_eq_P0 (card_eight_of_sylow hSyl)
  obtain ⟨g₀, hg₀⟩ := C.D.ρ_surj (k * h)
  refine ⟨g₀, g₀.2, ?_⟩
  set a₀ := (g₀ : G) * a * (g₀ : G)⁻¹ with ha₀
  set b₀ := (g₀ : G) * b * (g₀ : G)⁻¹ with hb₀
  have ha₀W : a₀ ∈ W := (Subgroup.mem_normalizer_iff.mp (hLW g₀.2) a).mp ha
  have hb₀W : b₀ ∈ CFSG.conjugate W s := (Subgroup.mem_normalizer_iff.mp (hLWs g₀.2) b).mp hb
  have hba₀ : C.D.b a₀ = L3.act k e0' := by rw [C.D.equi g₀ a ha, hg₀, L3.act_mul, hha]
  have hcb₀ : C.c b₀ = L3.act (τ3 k) e2' := by
    rw [C.c_equi g₀ b hb, hg₀, map_mul, L3.act_mul, hhb]
  have hP : ∀ (u : G) (hu : u ∈ T ⊓ L), ∃ p ∈ SecD.L3.P0, C.D.ρ ⟨u, hu.2⟩ = k * p * k⁻¹ := by
    intro u hu
    have h1 : C.D.ρ ⟨u, hu.2⟩ ∈ ((T ⊓ L).subgroupOf L).map C.D.ρ :=
      ⟨⟨u, hu.2⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    rw [hk] at h1
    obtain ⟨p, hp, hpe⟩ := h1
    exact ⟨p, hp, hpe.symm⟩
  have hfa : ∀ u ∈ T ⊓ L, u * a₀ * u⁻¹ = a₀ := by
    intro u hu
    have huW : u * a₀ * u⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hLW hu.2) a₀).mp ha₀W
    refine C.D.b_inj _ huW _ ha₀W ?_
    obtain ⟨p, hp, hpe⟩ := hP u hu
    rw [show u * a₀ * u⁻¹ = ((⟨u, hu.2⟩ : ↥L) : G) * a₀ * ((⟨u, hu.2⟩ : ↥L) : G)⁻¹ from rfl,
      C.D.equi _ a₀ ha₀W, hpe, hba₀, ← L3.act_mul, show k * p * k⁻¹ * k = k * p by group,
      L3.act_mul, P0_fix_e0 p hp]
  have hfb : ∀ u ∈ T ⊓ L, u * b₀ * u⁻¹ = b₀ := by
    intro u hu
    have huW : u * b₀ * u⁻¹ ∈ CFSG.conjugate W s :=
      (Subgroup.mem_normalizer_iff.mp (hLWs hu.2) b₀).mp hb₀W
    refine C.c_inj _ huW _ hb₀W ?_
    obtain ⟨p, hp, hpe⟩ := hP u hu
    rw [show u * b₀ * u⁻¹ = ((⟨u, hu.2⟩ : ↥L) : G) * b₀ * ((⟨u, hu.2⟩ : ↥L) : G)⁻¹ from rfl,
      C.c_equi _ b₀ hb₀W, hpe, hcb₀, map_mul, map_mul, map_inv, ← L3.act_mul,
      show τ3 k * τ3 p * (τ3 k)⁻¹ * τ3 k = τ3 k * τ3 p by group, L3.act_mul, tau_P0_fix_e2 p hp]
  have ha₀1 : a₀ ≠ 1 := fun h1 => by
    have h2 : L3.act k e0' = L3.act k 0 := by rw [L3.act_zero, ← hba₀, h1, C.b_one]
    exact absurd (act_injective k h2) (by decide)
  have hb₀1 : b₀ ≠ 1 := fun h1 => by
    have h2 : L3.act (τ3 k) e2' = L3.act (τ3 k) 0 := by rw [L3.act_zero, ← hcb₀, h1, C.c_one]
    exact absurd (act_injective _ h2) (by decide)
  have hf : (g₀ : G) * (a * b) * (g₀ : G)⁻¹ = a₀ * b₀ := by rw [ha₀, hb₀]; group
  rw [hf]
  intro u hu
  rw [Subgroup.mem_centralizer_singleton_iff]
  have huV1 : u ∈ Subgroup.normalizer ((W ⊔ CFSG.conjugate W s : Subgroup G) : Set G) := by
    rw [hsup]
    exact SecA.le_normalizer_commutator (X := T1 T L)
      (inf_le_left.trans (SecA.le_normalizer_fsuVM T L I)) inf_le_right hu
  have hcard : Nat.card W = Nat.card ↥(CFSG.conjugate W s) :=
    (Subgroup.card_map_of_injective (MulAut.conj s⁻¹).injective).symm
  have hua : u * a₀ * u⁻¹ ∈ CFSG.conjugate W u⁻¹ := by
    rw [SecA.mem_conjugate_iff, show u⁻¹ * (u * a₀ * u⁻¹) * u⁻¹⁻¹ = a₀ by group]
    exact ha₀W
  have hub : u * b₀ * u⁻¹ ∈ CFSG.conjugate (CFSG.conjugate W s) u⁻¹ := by
    rw [SecA.mem_conjugate_iff, show u⁻¹ * (u * b₀ * u⁻¹) * u⁻¹⁻¹ = b₀ by group]
    exact hb₀W
  have hua1 : u * a₀ * u⁻¹ ≠ 1 := fun h1 => ha₀1 (by
    calc a₀ = u⁻¹ * (u * a₀ * u⁻¹) * u := by group
      _ = 1 := by rw [h1]; group)
  have hub1 : u * b₀ * u⁻¹ ≠ 1 := fun h1 => hb₀1 (by
    calc b₀ = u⁻¹ * (u * b₀ * u⁻¹) * u := by group
      _ = 1 := by rw [h1]; group)
  have hfa' := conj_fix_of_T1 hu hfa
  have hfb' := conj_fix_of_T1 hu hfb
  have hne : ∀ X Y : Subgroup G, CFSG.conjugate X u⁻¹ = CFSG.conjugate Y u⁻¹ → X = Y := by
    intro X Y h
    have := congrArg (fun Z => CFSG.conjugate Z u) h
    simpa only [SecA.conjugate_conjugate, inv_mul_cancel, SecA.conjugate_one] using this
  have hWWs : W ≠ CFSG.conjugate W s := fun h => hirr.1 (by
    have := hinf
    rw [← h, inf_idem] at this
    exact this)
  rcases conj_eq_or_of_case5 hc hirr hirr' hLW hLWs hni hcard (Or.inl rfl) hu.2 huV1 with
    h1 | h1 <;>
  rcases conj_eq_or_of_case5 hc hirr hirr' hLW hLWs hni hcard (Or.inr rfl) hu.2 huV1 with h2 | h2
  · exact absurd (hne _ _ (h1.trans h2.symm)) hWWs
  · rw [h1] at hua
    rw [h2] at hub
    have e1 := C.eq_of_fix_W hk ha₀W hba₀ hua hua1 hfa'
    have e2 := C.eq_of_fix_Ws hk hb₀W hcb₀ hub hub1 hfb'
    calc u * (a₀ * b₀) = (u * a₀ * u⁻¹) * (u * b₀ * u⁻¹) * u := by group
      _ = a₀ * b₀ * u := by rw [e1, e2]
  · rw [h1] at hua
    rw [h2] at hub
    have e1 := C.eq_of_fix_Ws hk hb₀W hcb₀ hua hua1 hfa'
    have e2 := C.eq_of_fix_W hk ha₀W hba₀ hub hub1 hfb'
    calc u * (a₀ * b₀) = (u * a₀ * u⁻¹) * (u * b₀ * u⁻¹) * u := by group
      _ = b₀ * a₀ * u := by rw [e1, e2]
      _ = a₀ * b₀ * u := by rw [hc a₀ ha₀W b₀ hb₀W]
  · exact absurd (hne _ _ (h1.trans h2.symm)) hWWs

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

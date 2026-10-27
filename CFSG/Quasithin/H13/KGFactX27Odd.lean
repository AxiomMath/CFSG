module

public import CFSG.Quasithin.H13.KGFactX27Inv
public import CFSG.Quasithin.Vol2.F134LieOdd

public section

namespace CFSG.Quasithin.H13.KGX27

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank CFSG.Quasithin.F134.LieOdd
open CFSG.Quasithin.H13.NQCore

variable {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ}

theorem comap_map_torus3 (h : OddModel H M) :
    (((torus3 M).subgroupOf H).map (proj H)).comap (proj H) = (torus3 M).subgroupOf H := by
  apply le_antisymm
  · rintro x ⟨y, hy, hyx⟩
    have hd : y⁻¹ * x ∈ scal H := proj_eq_proj_iff.1 hyx
    obtain ⟨c, hc⟩ := mem_scal_iff.1 hd
    have hc3 := h.cube_eq_one_of_scalar hc
    have hcT : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ torus3 M := by
      rw [scalar_eq_diagHom]
      exact (mem_torus3 M).2 ⟨fun _ => c, fun _ => h.mu3 c hc3, by rw [← pow_three', hc3], rfl⟩
    have hx : x = y * (y⁻¹ * x) := by group
    rw [Subgroup.mem_subgroupOf, hx, Subgroup.coe_mul, hc]
    exact (torus3 M).mul_mem (Subgroup.mem_subgroupOf.1 hy) hcT
  · intro x hx
    exact ⟨x, hx, rfl⟩

theorem x27_std (h : OddModel H M) [Finite K] (hneg : (-1 : Kˣ) ∈ M)
    {P : Subgroup (StatedProj H)} (hP : Nat.card P = 27) (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hstd : ∀ x : H, proj H x ∈ P → (x : GL (Fin 3) K) ∈ torus3 M ⊔ Subgroup.zpowers cycGL) :
    ∃ Q : Subgroup (StatedProj H), Q ≤ P ∧ Nat.card Q = 9 ∧
      ∀ α : StatedProj H ≃* StatedProj H, P.map α.toMonoidHom = P → Q.map α.toMonoidHom = Q := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTH : torus3 M ≤ H := torus3_le M h.mono
  set Tb : Subgroup (StatedProj H) := ((torus3 M).subgroupOf H).map (proj H) with hTbdef
  set Q : Subgroup (StatedProj H) := P ⊓ Tb with hQdef
  set N : Subgroup (GL (Fin 3) K) := torus3 M ⊔ Subgroup.zpowers cycGL with hNdef
  set Et : Subgroup (GL (Fin 3) K) := (P.comap (proj H)).map H.subtype with hEtdef
  have hEtN : Et ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact hstd x hx
  have hEtcard : Nat.card Et = 81 := by
    rw [hEtdef, Subgroup.card_map_of_injective H.subtype_injective, h.card_comap, hP]
  have hTN : torus3 M ≤ N := le_sup_left
  have hidx : (torus3 M).relIndex N = 3 := by
    have h' := Subgroup.relIndex_mul_card (torus3 M) N
    rw [inf_eq_left.2 hTN, card_torus3, card_torus3_sup_cyc] at h'
    have hpos : 0 < Nat.card M ^ 2 := pow_pos Nat.card_pos 2
    exact Nat.eq_of_mul_eq_mul_right hpos h'
  have hrel : (torus3 M).relIndex Et ≤ 3 := by
    have := Subgroup.relIndex_le_of_le_right (H := torus3 M) hEtN (by rw [hidx]; norm_num)
    rwa [hidx] at this
  have hmul := Subgroup.relIndex_mul_card (torus3 M) Et
  rw [hEtcard] at hmul
  have hcube : torus3 M ⊓ Et ≤ cubeScalar M := by
    rintro y ⟨hyT, x, hx, rfl⟩
    refine ⟨hyT, ?_⟩
    have h3 : x ^ 3 ∈ scal H := proj_eq_one_iff.1 (by rw [map_pow]; exact hexp _ hx)
    obtain ⟨c, hc⟩ := mem_scal_iff.1 h3
    exact ⟨c, by rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hc]⟩
  have hle27 := (Subgroup.card_le_of_le hcube).trans (card_cubeScalar_le M)
  have hTE : Nat.card (torus3 M ⊓ Et : Subgroup (GL (Fin 3) K)) = 27 := by nlinarith
  have hQcomap : Q.comap (proj H) = P.comap (proj H) ⊓ (torus3 M).subgroupOf H := by
    rw [hQdef, Subgroup.comap_inf, hTbdef, comap_map_torus3 h]
  have hQ9 : Nat.card Q = 9 := by
    have h1 := h.card_comap Q
    rw [hQcomap] at h1
    have h2 : Nat.card (P.comap (proj H) ⊓ (torus3 M).subgroupOf H : Subgroup H) = 27 := by
      rw [← Subgroup.card_map_of_injective H.subtype_injective,
        Subgroup.map_inf_eq _ _ _ H.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hTH,
        inf_comm]
      exact hTE
    omega
  refine ⟨Q, inf_le_left, hQ9, fun α hαP => ?_⟩
  set d₀ : Fin 3 → Kˣ := ![-1, -1, 1] with hd₀def
  have hd₀T : diagHom 3 d₀ ∈ torus3 M := by
    refine (mem_torus3 M).2 ⟨d₀, fun i => ?_, by simp [hd₀def], rfl⟩
    fin_cases i
    · exact hneg
    · exact hneg
    · exact M.one_mem
  set u₀ : H := ⟨diagHom 3 d₀, hTH hd₀T⟩ with hu₀def
  have hu₀2 : u₀ ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hu₀def, diagHom_pow, Subgroup.coe_one]
    have hd2 : d₀ ^ 2 = 1 := by
      funext i
      fin_cases i <;> simp [hd₀def]
    rw [hd2, map_one]
  have hv₀1 : proj H u₀ ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := mem_scal_iff.1 (proj_eq_one_iff.1 h1)
    have e0 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hc
    have e2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) hc
    simp only [hu₀def, coe_diagHom, diagonal_apply_eq, GeneralLinearGroup.coe_scalar,
      scalar_apply, hd₀def] at e0 e2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Units.val_neg, Units.val_one] at e0 e2
    apply h.two
    linear_combination e2 - e0
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    rintro a ⟨-, x, hx, rfl⟩ b ⟨-, z, hz, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (torus3_comm M (Subgroup.mem_subgroupOf.1 hx) (Subgroup.mem_subgroupOf.1 hz))
  have hv₀Q : ∀ q ∈ Q, proj H u₀ * q = q * proj H u₀ := by
    rintro _ ⟨-, x, hx, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (torus3_comm M hd₀T (Subgroup.mem_subgroupOf.1 hx))
  by_contra hne
  set V := Q.map α.toMonoidHom with hVdef
  have hVP : V ≤ P := by
    rw [← hαP]
    exact Subgroup.map_mono inf_le_left
  have hV9 : Nat.card V = 9 := by
    rw [hVdef, Subgroup.card_map_of_injective α.injective, hQ9]
  obtain ⟨y, hyV, hyQ⟩ : ∃ y ∈ V, y ∉ Q := by
    by_contra hall
    push Not at hall
    exact hne (Subgroup.eq_of_le_of_card_ge hall (by rw [hV9, hQ9]))
  obtain ⟨x₀, rfl⟩ := proj_surjective y
  have hx₀T : (x₀ : GL (Fin 3) K) ∉ torus3 M := fun hT =>
    hyQ ⟨hVP hyV, x₀, Subgroup.mem_subgroupOf.2 hT, rfl⟩
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hQab a ha b hb]
  have hstdV : ∀ x : H, proj H x ∈ V → (x : GL (Fin 3) K) ∈ N := fun x hx => hstd x (hVP hx)
  have hv : (α (proj H u₀)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, hu₀2, map_one, map_one]
  have hvV : ∀ z ∈ V, α (proj H u₀) * z = z * α (proj H u₀) := by
    rintro _ ⟨q, hq, rfl⟩
    change α (proj H u₀) * α q = α q * α (proj H u₀)
    rw [← map_mul, ← map_mul, hv₀Q q hq]
  have h1 := h.eq_one_of_involution_centralizes hVab hstdV hyV hx₀T hV9 hv hvV
  exact hv₀1 (α.injective (by rw [h1, map_one]))

theorem x27Inv_of_oddModel (h : OddModel H M) [Finite K] (hneg : (-1 : Kˣ) ∈ M) :
    X27Inv (StatedProj H) := by
  intro P U hP hexp _ _ _
  have hE3 : IsPGroup 3 (P.comap (proj H)) := by
    rw [IsPGroup.iff_card]
    exact ⟨4, by rw [h.card_comap, hP]; norm_num⟩
  obtain ⟨g, hg⟩ := h.exists_conj_le_torus3_sup_cyc hE3
  set φ : StatedProj H ≃* StatedProj H := MulAut.conj (proj H g)⁻¹ with hφdef
  apply exists_invariant_of_map' φ
  have hP₁ : Nat.card (P.map φ.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective φ.injective, hP]
  have hexp₁ : ∀ x ∈ P.map φ.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  have hstd : ∀ x : H, proj H x ∈ P.map φ.toMonoidHom →
      (x : GL (Fin 3) K) ∈ torus3 M ⊔ Subgroup.zpowers cycGL := by
    intro x hx
    rw [Subgroup.mem_map_equiv, hφdef, MulAut.conj_symm_apply, inv_inv, ← map_inv, ← map_mul,
      ← map_mul] at hx
    have := hg (g * x * g⁻¹) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
  obtain ⟨Q, hQP, hQ9, hQ⟩ := x27_std h hneg hP₁ hexp₁ hstd
  exact ⟨Q, hQP, hQ9, fun α hαP _ => hQ α hαP⟩

theorem x27Psl3Plus : ∀ r : ℕ, r.Prime → r % 3 = 1 →
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 r 1 := by
  intro r hr hr3
  refine noX27ConfigQ_of_noE9Cfg
    (fun _ _ _ _ e h => CFSG.SectionRank.statedClassicalModel_of_mulEquiv e.symm h)
    (noX27Simple_of_x27Inv fun X _ hX => ?_) (noE9Cfg_of_e9Inv fun X _ hX => ?_)
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
    exact X27Inv.of_mulEquiv e
      (x27Inv_of_oddModel (oddModel_statedSL hr hr3 (by rw [hK, pow_one])) (Subgroup.mem_top _))
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
    exact E9Inv.of_mulEquiv e (oddModel_statedSL hr hr3 (by rw [hK, pow_one])).e9Inv

theorem x27Psu3Minus : ∀ r : ℕ, r.Prime → r ≠ 2 → r % 3 = 2 →
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 r 1 := by
  intro r hr hr2 hr3
  have hneg : ∀ (K : Type) [Field K], (-1 : Kˣ) ∈ normOne K (r ^ 1) := by
    intro K _
    rw [mem_normOne, pow_one]
    have hodd : r % 2 = 1 := hr.eq_two_or_odd.resolve_left hr2
    exact Even.neg_one_pow ⟨(r + 1) / 2, by omega⟩
  refine noX27ConfigQ_of_noE9Cfg
    (fun _ _ _ _ e h => CFSG.SectionRank.statedClassicalModel_of_mulEquiv e.symm h)
    (noX27Simple_of_x27Inv fun X _ hX => ?_) (noE9Cfg_of_e9Inv fun X _ hX => ?_)
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
    exact X27Inv.of_mulEquiv e (x27Inv_of_oddModel (oddModel_statedSU hr hr2 hr3 hK) (hneg K))
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
    exact E9Inv.of_mulEquiv e (oddModel_statedSU hr hr2 hr3 hK).e9Inv

end CFSG.Quasithin.H13.KGX27

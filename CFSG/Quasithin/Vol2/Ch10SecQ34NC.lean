module

public import CFSG.Quasithin.Vol2.Ch10SecQ34NB
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Vol2.Ch10SecQ34NA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Quasithin

variable {Y : Type} [Group Y]

theorem exists_involution_sl2_five :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5), g ≠ 1 ∧ g * g = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : 2 ∣ Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
    rw [← Nat.card_eq_fintype_card, card_sl2_zmod]
    norm_num
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 2 hd
  refine ⟨g, fun h => by rw [h, orderOf_one] at hg; exact absurd hg (by norm_num), ?_⟩
  have h1 := pow_orderOf_eq_one g
  rw [hg] at h1
  rw [← pow_two]
  exact h1

theorem exists_mem_conj_eq_inv {Kb Xb O : Subgroup Y} (hXK : Xb ≤ Kb) {F : Subgroup ↥Kb}
    [F.Normal] (hO : O = F.map Kb.subtype) [O.Normal] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hnat : NaturalSL2Action p ↥Kb F) (N : Subgroup ↥(Xb ⊔ O)) [N.Normal]
    (hN : N = O.subgroupOf (Xb ⊔ O)) (h5 : IsSL2 5 (↥(Xb ⊔ O) ⧸ N)) :
    ∃ x ∈ Xb, ∀ f ∈ O, x * f * x⁻¹ = f⁻¹ := by
  obtain ⟨φ⟩ := h5
  obtain ⟨e, ψ, -, hψk, hψa⟩ := hnat
  obtain ⟨m, hm1, hm2⟩ := exists_involution_sl2_five
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (φ.symm m)
  have hOK : O ≤ Kb := hO ▸ Subgroup.map_subtype_le F
  have hXOK : Xb ⊔ O ≤ Kb := sup_le hXK hOK
  have hyN : y ∉ N := by
    intro h
    have h1 : (QuotientGroup.mk y : ↥(Xb ⊔ O) ⧸ N) = 1 := (QuotientGroup.eq_one_iff y).mpr h
    rw [hy] at h1
    exact hm1 (by simpa using congrArg φ h1)
  have hy2N : y * y ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hy, ← map_mul, hm2, map_one]
  rw [hN, Subgroup.mem_subgroupOf] at hyN hy2N
  set yK : ↥Kb := ⟨y, hXOK y.2⟩ with hyK
  have hyF : yK ∉ F := by
    intro h
    apply hyN
    have h' : (y : Y) ∈ F.map Kb.subtype := ⟨yK, h, rfl⟩
    rwa [← hO] at h'
  have hy2F : yK * yK ∈ F := by
    obtain ⟨f, hf, hfe⟩ : ((y * y : ↥(Xb ⊔ O)) : Y) ∈ F.map Kb.subtype := by
      rw [← hO]; exact hy2N
    have : f = yK * yK := Subtype.ext (by rw [Subgroup.coe_mul]; exact hfe)
    exact this ▸ hf
  have hψ2 : ψ yK * ψ yK = 1 := by
    rw [← map_mul]
    exact (hψk ▸ hy2F : yK * yK ∈ ψ.ker)
  have hψ1 : ψ yK ≠ 1 := fun h => hyF (hψk ▸ (h : yK ∈ ψ.ker))
  have hneg := coe_eq_neg_one_of_mul_self hp2 hψ2 hψ1
  obtain ⟨x, hx, o, ho, hxo⟩ := Subgroup.mem_sup_of_normal_right.mp y.2
  set xK : ↥Kb := ⟨x, hXK hx⟩ with hxK
  have hoF : (⟨o, hOK ho⟩ : ↥Kb) ∈ F := by
    rw [hO] at ho
    obtain ⟨f, hf, hfe⟩ := ho
    have : f = ⟨o, hOK ho⟩ := Subtype.ext hfe
    exact this ▸ hf
  have hψx : ψ xK = ψ yK := by
    have hyx : yK = xK * ⟨o, hOK ho⟩ := Subtype.ext (by rw [Subgroup.coe_mul]; exact hxo.symm)
    rw [hyx, map_mul, (hψk ▸ hoF : (⟨o, hOK ho⟩ : ↥Kb) ∈ ψ.ker), mul_one]
  refine ⟨x, hx, fun f hf => ?_⟩
  rw [hO] at hf
  obtain ⟨f', hf', rfl⟩ := hf
  have h := conj_eq_inv_of_natural e ψ hψa (x := xK) (by rw [hψx]; exact hneg) ⟨f', hf'⟩
  exact congrArg Subtype.val h

theorem inf_eq_bot_of_sl2_five [Finite Y] {Xb O : Subgroup Y} [hOn : O.Normal]
    (hOodd : Odd (Nat.card O)) (hs : IsSimpleGroup (↥Xb ⧸ CFSG.pCore 2 ↥Xb))
    (N : Subgroup ↥(Xb ⊔ O)) [N.Normal] (hN : N = O.subgroupOf (Xb ⊔ O))
    (h5 : IsSL2 5 (↥(Xb ⊔ O) ⧸ N)) : Xb ⊓ O = ⊥ := by
  obtain ⟨φ⟩ := h5
  set ι : ↥Xb →* ↥(Xb ⊔ O) := Subgroup.inclusion le_sup_left with hι
  set χ : ↥Xb →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    φ.toMonoidHom.comp ((QuotientGroup.mk' N).comp ι) with hχ
  have hD : (O.subgroupOf Xb).Normal := hOn.subgroupOf Xb
  have hDodd : Odd (Nat.card (O.subgroupOf Xb)) := by
    refine hOodd.of_dvd_nat ?_
    have h1 : (O.subgroupOf Xb).map Xb.subtype ≤ O := by
      rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left
    have h2 := Subgroup.card_dvd_of_le h1
    rwa [Subgroup.card_map_of_injective Xb.subtype_injective] at h2
  have hχs : Function.Surjective χ := by
    intro σ
    obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective (φ.symm σ)
    obtain ⟨x, hx, o, ho, hxo⟩ := Subgroup.mem_sup_of_normal_right.mp z.2
    refine ⟨⟨x, hx⟩, ?_⟩
    have hxz : (QuotientGroup.mk (ι ⟨x, hx⟩) : ↥(Xb ⊔ O) ⧸ N) = QuotientGroup.mk z := by
      rw [QuotientGroup.eq, hN, Subgroup.mem_subgroupOf]
      have : ((ι ⟨x, hx⟩)⁻¹ * z : ↥(Xb ⊔ O)) = (⟨o, (le_sup_right : O ≤ Xb ⊔ O) ho⟩ : ↥(Xb ⊔ O)) :=
        Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hι, Subgroup.coe_inclusion]
          rw [← hxo]; group)
      rw [this]
      exact ho
    simp only [hχ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, hxz, hz,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  have hDχ : O.subgroupOf Xb ≤ χ.ker := by
    intro d hd
    rw [MonoidHom.mem_ker, hχ, MonoidHom.comp_apply, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr _, map_one]
    rw [hN, Subgroup.mem_subgroupOf]
    exact hd
  have hbot := eq_bot_of_odd_normal hs hDodd χ hχs hDχ not_isPGroup_two_sl2_five
  rw [eq_bot_iff]
  intro y ⟨hyX, hyO⟩
  have : (⟨y, hyX⟩ : ↥Xb) ∈ O.subgroupOf Xb := hyO
  rw [hbot, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

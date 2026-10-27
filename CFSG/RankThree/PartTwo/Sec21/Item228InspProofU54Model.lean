module

public import CFSG.RankThree.PartTwo.Sec21.Item233Res3ProofU54Lines
public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofU4Model

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228InspProof

open Matrix CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof (K16 card_K16 σ16 SU54 U54 qU
  isCentralPQuot_qU tt tt_mem exists_tt tt_mul tt_one card_mu3 σ16_mu3 σ16_involutive tt4
  tt_eq_su4Emb qU_su4Emb_injective)
open CFSG.RankThree.PartOne.KFU (D8Mod torus6 su3Emb su3Emb_injective su2Emb suBlock suBlockB
  suBlock6 b5 bB perfectResidual_centralizer_b5 perfectResidual_centralizer_bB
  perfectResidual_centralizer_b6 perfectResidual_centralizer_bA6 torus6_inf_range_su3_eq
  rhoSU3_mem_range_su2Emb card_center_SU_three card_center_mulEquiv
  map_inSubgroup_perfectResidual torus6_pow_eq_one permGL_mem_SU d8Vec_four fixF)
open CFSG.RankThree.PartOne.K1320X (su4Emb su4Emb_injective su4Emb_suBlock su4Emb_suBlockB)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (torusD weyl₁ weyl₂ conj_weyl₁ conj_weyl₂
  perfectResidual_conj)

section Generic

variable {G H : Type} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite G] [Finite H] in
theorem perfCent_top_zpowers (y : G) :
    perfCent ⊤ (Subgroup.zpowers y) =
      inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set G)) := by
  rw [perfCent, top_inf_eq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem perfCent_range_zpowers (ι : H →* G) (hι : Function.Injective ι) (h : H) :
    perfCent ι.range (Subgroup.zpowers (ι h)) =
      (inSubgroup perfectResidual (Subgroup.centralizer ({h} : Set H))).map ι := by
  rw [GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _ hι, perfCent]
  congr 1
  ext x
  rw [Subgroup.mem_inf, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
    Subgroup.mem_map]
  constructor
  · rintro ⟨⟨y, rfl⟩, hy⟩
    refine ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr (hι ?_), rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hy
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hy]

@[expose] def CmpU54 (Y T ℓ : Subgroup G) : Prop :=
  perfCent ⊤ ℓ = perfCent Y ℓ ∨
    (StatedClassicalModel (perfCent ⊤ ℓ) .PSU 3 2 2 ∧ T ⊓ perfCent ⊤ ℓ ≤ perfCent Y ℓ)

theorem cmp_conj {Y T ℓ : Subgroup G} {g : G} (hgY : g ∈ Y)
    (hgT : g ∈ Subgroup.normalizer (T : Set G)) (h : CmpU54 Y T ℓ) :
    CmpU54 Y T (ℓ.map (MulAut.conj g).toMonoidHom) := by
  have h₁ : perfCent ⊤ (ℓ.map (MulAut.conj g).toMonoidHom) =
      (perfCent ⊤ ℓ).map (MulAut.conj g).toMonoidHom :=
    perfectResidual_conj (Subgroup.mem_top g) ℓ
  have h₂ : perfCent Y (ℓ.map (MulAut.conj g).toMonoidHom) =
      (perfCent Y ℓ).map (MulAut.conj g).toMonoidHom := perfectResidual_conj hgY ℓ
  unfold CmpU54 at h ⊢
  rw [h₁, h₂]
  rcases h with h | ⟨hU, hle⟩
  · left
    rw [h]
  · right
    refine ⟨CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
      ((perfCent ⊤ ℓ).equivMapOfInjective _ (MulAut.conj g).injective) hU, ?_⟩
    have hT : T.map (MulAut.conj g).toMonoidHom = T := map_conj_self hgT
    calc T ⊓ (perfCent ⊤ ℓ).map (MulAut.conj g).toMonoidHom
        = T.map (MulAut.conj g).toMonoidHom ⊓ (perfCent ⊤ ℓ).map (MulAut.conj g).toMonoidHom := by
          rw [hT]
      _ = (T ⊓ perfCent ⊤ ℓ).map (MulAut.conj g).toMonoidHom :=
          (Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective).symm
      _ ≤ (perfCent Y ℓ).map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hle

end Generic

section Model

theorem tt_inv (a b : rootsOfUnity 3 K16) : (tt a b)⁻¹ = tt a⁻¹ b⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, tt_mul, mul_inv_cancel, mul_inv_cancel, tt_one]

theorem line_cases_U54 {ζ : rootsOfUnity 3 K16} (hζ : ζ ≠ 1) {ℓ : Subgroup U54}
    (hℓ : ℓ ≤ (torus6 σ16 3).map qU) (h3 : Nat.card ℓ = 3) :
    ℓ = Subgroup.zpowers (qU (tt ζ 1)) ∨ ℓ = Subgroup.zpowers (qU (tt 1 ζ)) ∨
      ℓ = Subgroup.zpowers (qU (tt ζ ζ)) ∨ ℓ = Subgroup.zpowers (qU (tt ζ ζ⁻¹)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial ℓ := Finite.one_lt_card_iff_nontrivial.mp (by rw [h3]; norm_num)
  obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : ℓ)
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx3 : x ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ℓ) (x := ⟨x, hx⟩)
    rw [h3] at h
    exact congrArg Subtype.val h
  have hℓx : ℓ = Subgroup.zpowers x := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx) ?_
    rw [h3, Nat.card_zpowers, orderOf_eq_prime hx3 hx1']
  obtain ⟨t, ht, rfl⟩ := hℓ hx
  obtain ⟨a, b, rfl⟩ := exists_tt ht
  rw [hℓx]
  have hi : ∀ u w : rootsOfUnity 3 K16,
      Subgroup.zpowers (qU (tt u⁻¹ w⁻¹)) = Subgroup.zpowers (qU (tt u w)) := fun u w => by
    rw [← tt_inv, map_inv, Subgroup.zpowers_inv]
  rcases U4Lines.eq_one_or_eq_or_eq_inv card_mu3 hζ a with rfl | rfl | rfl <;>
    rcases U4Lines.eq_one_or_eq_or_eq_inv card_mu3 hζ b with rfl | rfl | rfl
  · exact absurd (by rw [tt_one, map_one]) hx1'
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl (by rw [← hi, inv_one, inv_inv]))
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inl (by rw [← hi, inv_one, inv_inv])
  · exact Or.inr (Or.inr (Or.inr (by rw [← hi, inv_inv])))
  · exact Or.inr (Or.inr (Or.inl (by rw [hi])))

theorem units_facts {ζ : rootsOfUnity 3 K16} (hζ : ζ ≠ 1) :
    (ζ : K16ˣ) ≠ 1 ∧ (ζ : K16ˣ) ^ 2 ≠ 1 := by
  have h1 : (ζ : K16ˣ) ≠ 1 := fun h => hζ (Subtype.ext h)
  have h3 : (ζ : K16ˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp ζ.2
  refine ⟨h1, fun h => h1 ?_⟩
  calc (ζ : K16ˣ) = (ζ : K16ˣ) ^ 3 * ((ζ : K16ˣ) ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h, inv_one, one_mul]

theorem four_le_card_K16 : 4 ≤ Nat.card K16 := by
  rw [card_K16]
  norm_num

theorem card_fixF_σ16 : Nat.card (fixF σ16) = 4 := by
  have h : Nat.card (fixF σ16) = 2 ^ 2 := CFSG.LieType.Steinberg.card_fixedSubfield card_K16
  rw [h]
  norm_num

theorem perfCent_top_qU {x : SU54} (hx3 : x ^ 3 = 1) :
    perfCent ⊤ (Subgroup.zpowers (qU x)) =
      (inSubgroup perfectResidual (Subgroup.centralizer ({x} : Set SU54))).map qU := by
  rw [perfCent_top_zpowers, ← isCentralPQuot_qU.map_centralizer hx3]
  exact (CFSG.RankThree.PartOne.KFU.map_inSubgroup_perfectResidual _ _).symm

theorem perfCent_Y_qU (y : ↥(SU σ16 4)) :
    perfCent (qU.comp (su4Emb σ16)).range (Subgroup.zpowers (qU (su4Emb σ16 y))) =
      (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set ↥(SU σ16 4)))).map
        (qU.comp (su4Emb σ16)) :=
  perfCent_range_zpowers (qU.comp (su4Emb σ16)) qU_su4Emb_injective y

theorem cmp_short {ζ : rootsOfUnity 3 K16} (hζ : ζ ≠ 1) :
    perfCent ⊤ (Subgroup.zpowers (qU (tt ζ ζ))) =
      perfCent (qU.comp (su4Emb σ16)).range (Subgroup.zpowers (qU (tt ζ ζ))) := by
  obtain ⟨h1, h2⟩ := units_facts hζ
  have hb6 : tt ζ ζ = CFSG.RankThree.PartOne.KFU.b6 σ16 (ζ : K16ˣ) (σ16_mu3 ζ) := rfl
  have hbB : tt4 ζ ζ = bB σ16 (ζ : K16ˣ) (σ16_mu3 ζ) := by
    apply Subtype.ext
    change CFSG.RankThree.PartOne.KFU.diagU (CFSG.RankThree.PartOne.KFU.d8Vec 4 (ζ, ζ)) = _
    rw [d8Vec_four]
    rfl
  have hrange : (suBlockB σ16 σ16_involutive).range.map (su4Emb σ16) =
      (suBlock6 σ16 σ16_involutive).range := by
    rw [MonoidHom.map_range]
    congr 1
    exact MonoidHom.ext fun X => su4Emb_suBlockB σ16 σ16_involutive X
  rw [perfCent_top_qU (torus6_pow_eq_one (tt_mem ζ ζ)), hb6,
    perfectResidual_centralizer_b6 σ16 σ16_involutive four_le_card_K16 (σ16_mu3 ζ) h1 h2,
    ← hb6, tt_eq_su4Emb, perfCent_Y_qU, hbB,
    perfectResidual_centralizer_bB σ16 σ16_involutive four_le_card_K16 (σ16_mu3 ζ) h2,
    ← Subgroup.map_map, hrange]

theorem qU_injOn_su3 : Function.Injective (qU.subgroupMap (su3Emb σ16).range) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have hz' : (z : SU54) ∈ qU.ker := MonoidHom.mem_ker.mpr (congrArg Subtype.val hz)
  have hzc : (z : SU54) ∈ Subgroup.center SU54 := isCentralPQuot_qU.central hz'
  have hzH : z ∈ Subgroup.center (su3Emb σ16).range := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subgroup.mem_center_iff.mp hzc w)
  have hc : Nat.card (Subgroup.center (su3Emb σ16).range) = 1 := by
    rw [← card_center_mulEquiv (MonoidHom.ofInjective (su3Emb_injective σ16)),
      card_center_SU_three card_K16 le_rfl]
    norm_num
  rw [Subgroup.card_eq_one.mp hc] at hzH
  exact hzH

theorem mem_of_qU_mem {Hs : Subgroup SU54} {t : SU54} (ht3 : t ^ 3 = 1)
    (ht : qU t ∈ Hs.map qU) : t ∈ Hs := by
  obtain ⟨h, hh, hht⟩ := ht
  have hz : h⁻¹ * t ∈ qU.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hht, inv_mul_cancel]
  set z := h⁻¹ * t with hzdef
  have hzc : z ∈ Subgroup.center SU54 := isCentralPQuot_qU.central hz
  have htz : t = h * z := by rw [hzdef, mul_inv_cancel_left]
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder isCentralPQuot_qU.coprime 1 0
  have hzN : z ^ Nat.card qU.ker = 1 := by
    have := pow_card_eq_one' (G := qU.ker) (x := ⟨z, hz⟩)
    exact congrArg Subtype.val this
  have hzc' : z ^ c = 1 := by
    rw [← Nat.mod_add_div c (Nat.card qU.ker), pow_add, pow_mul, hzN, one_pow, mul_one]
    have : c % Nat.card qU.ker = 0 := by
      have := hc2.symm
      rw [Nat.ModEq] at this
      simpa using this.symm
    rw [this, pow_zero]
  have htc : t ^ c = t := by
    rw [← Nat.mod_add_div c 3, pow_add, pow_mul, ht3, one_pow, mul_one]
    have : c % 3 = 1 := by
      have := hc1
      rw [Nat.ModEq] at this
      simpa using this
    rw [this, pow_one]
  have hcomm : Commute h z := Subgroup.mem_center_iff.mp hzc h
  rw [← htc, htz, hcomm.mul_pow, hzc', mul_one]
  exact Hs.pow_mem hh c

theorem cmp_long {ζ : rootsOfUnity 3 K16} (hζ : ζ ≠ 1) :
    StatedClassicalModel (perfCent ⊤ (Subgroup.zpowers (qU (tt 1 ζ)))) .PSU 3 2 2 ∧
      (torus6 σ16 3).map qU ⊓ perfCent ⊤ (Subgroup.zpowers (qU (tt 1 ζ))) ≤
        perfCent (qU.comp (su4Emb σ16)).range (Subgroup.zpowers (qU (tt 1 ζ))) := by
  obtain ⟨h1, h2⟩ := units_facts hζ
  have hbA : tt 1 ζ = CFSG.RankThree.PartOne.KFU.bA6 σ16 (ζ : K16ˣ) (σ16_mu3 ζ) := rfl
  have hb5 : tt4 1 ζ = b5 σ16 (ζ : K16ˣ) (σ16_mu3 ζ) := by
    apply Subtype.ext
    change CFSG.RankThree.PartOne.KFU.diagU (CFSG.RankThree.PartOne.KFU.d8Vec 4 (1, ζ)) = _
    rw [d8Vec_four]
    rfl
  have hX : perfCent ⊤ (Subgroup.zpowers (qU (tt 1 ζ))) = (su3Emb σ16).range.map qU := by
    rw [perfCent_top_qU (torus6_pow_eq_one (tt_mem 1 ζ)), hbA,
      perfectResidual_centralizer_bA6 card_K16 le_rfl (σ16_mu3 ζ) h1 h2]
  have hY : perfCent (qU.comp (su4Emb σ16)).range (Subgroup.zpowers (qU (tt 1 ζ))) =
      (su2Emb σ16).range.map qU := by
    have hrange : (suBlock σ16).range.map (su4Emb σ16) = (su2Emb σ16).range := by
      rw [MonoidHom.map_range]
      congr 1
      exact MonoidHom.ext fun A => su4Emb_suBlock σ16 A
    rw [tt_eq_su4Emb, perfCent_Y_qU, hb5,
      perfectResidual_centralizer_b5 σ16 (by rw [card_fixF_σ16]) (σ16_mu3 ζ) h1 h2,
      ← Subgroup.map_map, hrange]
  rw [hX, hY]
  refine ⟨?_, ?_⟩
  ·
    have e : ↥((su3Emb σ16).range.map qU) ≃* ↥(SU σ16 3) :=
      (MulEquiv.ofBijective _ ⟨qU_injOn_su3, qU.subgroupMap_surjective _⟩).symm.trans
        (MonoidHom.ofInjective (su3Emb_injective σ16)).symm
    exact CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e.symm
      (U5Lines.statedClassicalModel_SU_three card_K16)
  · rintro y ⟨⟨t, ht, rfl⟩, hy⟩
    have ht3 := torus6_pow_eq_one ht
    have htS : t ∈ (su3Emb σ16).range := mem_of_qU_mem ht3 hy
    have hfix : ∀ u : K16ˣ, u ^ 3 = 1 → σ16 (u : K16) = u := fun u hu =>
      σ16_mu3 ⟨u, (mem_rootsOfUnity 3 u).mpr hu⟩
    have htR : t ∈ (CFSG.RankThree.PartOne.KFU.rhoSU3 hfix).range := by
      rw [← torus6_inf_range_su3_eq hfix]
      exact ⟨ht, htS⟩
    obtain ⟨u, rfl⟩ := htR
    exact ⟨_, rhoSU3_mem_range_su2Emb σ16 hfix u, rfl⟩

@[expose] noncomputable def w44 (i : Fin 2) : ↥(SU σ16 4) :=
  if i = 0 then ⟨weyl₁, permGL_mem_SU σ16 _ (by decide)⟩
  else ⟨weyl₂, permGL_mem_SU σ16 _ (by decide)⟩

theorem w44_zero_conj (a b : rootsOfUnity 3 K16) : w44 0 * tt4 a b * (w44 0)⁻¹ = tt4 b a := by
  apply Subtype.ext
  change weyl₁ * torusD ((a, b) : D8Mod 3 K16) * weyl₁⁻¹ = torusD ((b, a) : D8Mod 3 K16)
  exact conj_weyl₁ ((a, b) : D8Mod 3 K16)

theorem w44_one_conj (a b : rootsOfUnity 3 K16) : w44 1 * tt4 a b * (w44 1)⁻¹ = tt4 a b⁻¹ := by
  apply Subtype.ext
  change weyl₂ * torusD ((a, b) : D8Mod 3 K16) * weyl₂⁻¹ = torusD ((a, b⁻¹) : D8Mod 3 K16)
  exact conj_weyl₂ ((a, b) : D8Mod 3 K16)

theorem w44_mul_self (i : Fin 2) : w44 i * w44 i = 1 := by
  obtain ⟨h₁, h₂⟩ := weyl_mul_self (F := K16)
  fin_cases i
  · exact Subtype.ext h₁
  · exact Subtype.ext h₂

theorem w44_facts (i : Fin 2) :
    qU (su4Emb σ16 (w44 i)) ∈ (qU.comp (su4Emb σ16)).range ∧
      qU (su4Emb σ16 (w44 i)) ∈ Subgroup.normalizer (((torus6 σ16 3).map qU : Subgroup U54) :
        Set U54) ∧
      ∀ a b, qU (su4Emb σ16 (w44 i)) * qU (tt a b) * (qU (su4Emb σ16 (w44 i)))⁻¹ =
        qU (su4Emb σ16 (w44 i * tt4 a b * (w44 i)⁻¹)) := by
  have hconj : ∀ a b, qU (su4Emb σ16 (w44 i)) * qU (tt a b) * (qU (su4Emb σ16 (w44 i)))⁻¹ =
      qU (su4Emb σ16 (w44 i * tt4 a b * (w44 i)⁻¹)) := fun a b => by
    rw [tt_eq_su4Emb, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  refine ⟨⟨w44 i, rfl⟩, ?_, hconj⟩
  have hinv : qU (su4Emb σ16 (w44 i)) * qU (su4Emb σ16 (w44 i)) = 1 := by
    rw [← map_mul, ← map_mul, w44_mul_self, map_one, map_one]
  refine mem_normalizer_of_conj_le hinv ?_
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨a, b, rfl⟩ := exists_tt ht
  rw [hconj]
  fin_cases i
  · change qU (su4Emb σ16 (w44 0 * tt4 a b * (w44 0)⁻¹)) ∈ _
    rw [w44_zero_conj, ← tt_eq_su4Emb]
    exact ⟨tt b a, tt_mem b a, rfl⟩
  · change qU (su4Emb σ16 (w44 1 * tt4 a b * (w44 1)⁻¹)) ∈ _
    rw [w44_one_conj, ← tt_eq_su4Emb]
    exact ⟨tt a b⁻¹, tt_mem a b⁻¹, rfl⟩

theorem model_U54 {ℓ : Subgroup U54} (hℓ : ℓ ≤ (torus6 σ16 3).map qU) (h3 : Nat.card ℓ = 3) :
    CmpU54 (qU.comp (su4Emb σ16)).range ((torus6 σ16 3).map qU) ℓ := by
  obtain ⟨ζ, hζ⟩ := Item233Res3Proof.exists_mu3_ne_one
  have hL₁ : (Subgroup.zpowers (qU (tt 1 ζ))).map
      (MulAut.conj (qU (su4Emb σ16 (w44 0)))).toMonoidHom = Subgroup.zpowers (qU (tt ζ 1)) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    change qU (su4Emb σ16 (w44 0)) * qU (tt 1 ζ) * (qU (su4Emb σ16 (w44 0)))⁻¹ = _
    rw [(w44_facts 0).2.2, w44_zero_conj, ← tt_eq_su4Emb]
  have hL₄ : (Subgroup.zpowers (qU (tt ζ ζ))).map
      (MulAut.conj (qU (su4Emb σ16 (w44 1)))).toMonoidHom = Subgroup.zpowers (qU (tt ζ ζ⁻¹)) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    change qU (su4Emb σ16 (w44 1)) * qU (tt ζ ζ) * (qU (su4Emb σ16 (w44 1)))⁻¹ = _
    rw [(w44_facts 1).2.2, w44_one_conj, ← tt_eq_su4Emb]
  have hlong : CmpU54 (qU.comp (su4Emb σ16)).range ((torus6 σ16 3).map qU)
      (Subgroup.zpowers (qU (tt 1 ζ))) := Or.inr (cmp_long hζ)
  have hshort : CmpU54 (qU.comp (su4Emb σ16)).range ((torus6 σ16 3).map qU)
      (Subgroup.zpowers (qU (tt ζ ζ))) := Or.inl (cmp_short hζ)
  rcases line_cases_U54 hζ hℓ h3 with rfl | rfl | rfl | rfl
  · rw [← hL₁]
    exact cmp_conj (w44_facts 0).1 (w44_facts 0).2.1 hlong
  · exact hlong
  · exact hshort
  · rw [← hL₄]
    exact cmp_conj (w44_facts 1).1 (w44_facts 1).2.1 hshort

end Model

end CFSG.RankThree.PartTwo.Sec21.Item228InspProof

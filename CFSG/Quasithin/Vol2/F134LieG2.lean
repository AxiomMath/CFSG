module

public import CFSG.Quasithin.Vol2.F134LieG2Power
public import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution
public import CFSG.Quasithin.Vol2.F134LieG2Borel

public section

namespace CFSG.Quasithin.F134.LieG2

open CFSG.Quasithin.P134

theorem false_of_forall_conj_eq_pow {A : Type} [Group A] [Finite A] {L P T : Subgroup A}
    (hcfg : E9Config L P T)
    (h : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∃ s : ℕ, ∀ x ∈ P, t * x * t⁻¹ = x ^ 2 ^ s) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxP, hx1⟩ : ∃ x ∈ P, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h9 := hcfg.card
    rw [(Subgroup.eq_bot_iff_forall P).2 hcon, Subgroup.card_bot] at h9
    norm_num at h9
  have hx3 : orderOf x = 3 := orderOf_eq_prime (hcfg.exp x hxP) hx1
  have hQP : Subgroup.zpowers x ≤ P := Subgroup.zpowers_le.2 hxP
  have hN : T ⊓ Subgroup.normalizer (P : Set A) ≤
      Subgroup.normalizer (Subgroup.zpowers x : Set A) := by
    intro t ht
    obtain ⟨s, hs⟩ := h t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← conj_zpow, hs x hxP]
      exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _) k
    · intro hy
      have hyP : y ∈ P := (Subgroup.mem_normalizer_iff.1 ht.2 y).2 (hQP hy)
      rw [hs y hyP] at hy
      have h4 : (2 ^ s * 2 ^ s) % 3 = 1 := by
        rw [← mul_pow, Nat.pow_mod]
        norm_num
      have hyy : y = (y ^ 2 ^ s) ^ 2 ^ s := by
        rw [← pow_mul, ← Nat.div_add_mod (2 ^ s * 2 ^ s) 3, h4, pow_add, pow_mul,
          hcfg.exp y hyP, one_pow, one_mul, pow_one]
      rw [hyy]
      exact Subgroup.pow_mem _ hy _
  rcases hcfg.irred _ hQP hN with hbot | hP
  · have hx : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
    rw [hbot, Subgroup.mem_bot] at hx
    exact hx1 hx
  · have h9 := hcfg.card
    rw [← hP, Nat.card_zpowers, hx3] at h9
    norm_num at h9

theorem exists_mulEquiv_map_eq {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ}
    [Fact p.Prime] (e₀ : X ≃* Y) (S : Sylow p X) (S' : Sylow p Y) :
    ∃ e : X ≃* Y, (S : Subgroup X).map e.toMonoidHom = S' := by
  have : Finite Y := Finite.of_equiv X e₀.toEquiv
  have hsurj : Function.Surjective e₀.toMonoidHom := e₀.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y (S.mapSurjective hsurj) S'
  refine ⟨e₀.trans (MulAut.conj g), ?_⟩
  rw [← hg, CFSG.LieType.Chevalley.coe_smul_sylow_eq_map, Sylow.coe_mapSurjective,
    Subgroup.map_map]
  rfl

end CFSG.Quasithin.F134.LieG2

namespace CFSG.Quasithin.P134

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.F134
  CFSG.Quasithin.F134.LieG2

theorem facts134E9_g2Even :
    ∀ n : ℕ, NoE9Config fun (X : Type) [Group X] => ChevalleyExceptionalModel X .G2 2 n := by
  intro n A _ _ L P T hL hcfg
  obtain ⟨⟨-, hn1, -, hq3⟩, hmod⟩ := hL
  have hn : 2 ≤ n := by
    by_contra hlt
    obtain rfl : n = 1 := by omega
    norm_num at hq3
  obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_adjointGroup_of_untwisted hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL .G2 K) := finite_modGL
  have := hcfg.normal
  have hBC : borelGroup .G2 K ≤ adjointGroup .G2 K :=
    ((triangular_borel_structure.{0, 0} .G2 K).2.2.2.2.2.2.2.2.2.2.2 K).1
  have hUC : posUnipotent .G2 K ≤ adjointGroup .G2 K := le_sup_right.trans hBC
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have hUcard : Nat.card (posUnipotent .G2 K) = 2 ^ (6 * n) := by
    rw [card_posUnipotent, ncard_posRoots_G2, hK, ← pow_mul, mul_comm]
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 hUC card_posUnipotent
  have hS := E9Config.isSylowTwoOf_inf hcfg
  obtain ⟨e, he⟩ := exists_mulEquiv_map_eq e₀ (hUp.toSylow hUi)
    ((hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).toSylow hS.2.2)
  replace he : ((posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)).map e.toMonoidHom =
      (T ⊓ L).subgroupOf L := he
  have he_inj : Function.Injective e.toMonoidHom := e.injective
  have he_surj : Function.Surjective e.toMonoidHom := e.surjective
  have hmemU : ∀ w : L, w ∈ (T ⊓ L).subgroupOf L →
      e.symm w ∈ (posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K) := by
    intro w hw
    rw [← he, Subgroup.mem_map_equiv] at hw
    exact hw
  have hcardU' : Nat.card ((T ⊓ L).subgroupOf L) = Nat.card (posUnipotent .G2 K) := by
    rw [← he, Subgroup.card_map_of_injective he_inj, card_subgroupOf_of_le hUC]
  have hcomap : ∀ S : Subgroup L, Nat.card (S.comap e.toMonoidHom) = Nat.card S := by
    intro S
    rw [← Subgroup.card_map_of_injective he_inj,
      Subgroup.map_comap_eq_self_of_surjective he_surj]
  set PC := (P.subgroupOf L).comap e.toMonoidHom with hPC
  set HC := ((P ⊔ T ⊓ L).subgroupOf L).comap e.toMonoidHom with hHC
  have hPHC : PC ≤ HC := fun x hx => by
    change ((e x : L) : A) ∈ P ⊔ T ⊓ L
    exact le_sup_left (α := Subgroup A) hx
  have hPCcard : Nat.card PC = 9 := by
    rw [hPC, hcomap, card_subgroupOf_of_le hcfg.le, hcfg.card]
  have hHm : HC.map (adjointGroup .G2 K).subtype ≤ borelGroup .G2 K := by
    refine le_borelGroup_of_card_eq hK hn (Subgroup.map_subtype_le HC) (fun u hu => ?_) ?_
      (Subgroup.map_mono hPHC) ?_ ?_
    · refine ⟨⟨u, hUC hu⟩, ?_, rfl⟩
      have h1 : e ⟨u, hUC hu⟩ ∈ (T ⊓ L).subgroupOf L :=
        he ▸ Subgroup.mem_map_of_mem e.toMonoidHom hu
      change ((e ⟨u, hUC hu⟩ : L) : A) ∈ P ⊔ T ⊓ L
      exact le_sup_right (α := Subgroup A) h1
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hHC, hcomap,
        card_subgroupOf_of_le (E9Config.sup_inf_le hcfg), E9Config.card_sup_inf hcfg,
        ← card_subgroupOf_of_le hS.1, hcardU']
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hPCcard]
    · rintro _ ⟨y, hy, rfl⟩
      have hy3 : e (y ^ 3) = 1 := by
        rw [map_pow]
        exact Subtype.ext (by simpa using hcfg.exp _ hy)
      rw [← map_pow, (MulEquiv.map_eq_one_iff e).1 hy3, map_one]
  have hdisj : Disjoint PC ((posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hPCcard, card_subgroupOf_of_le hUC, hUcard]
    exact Nat.Coprime.pow_right _ (by norm_num)
  refine false_of_forall_conj_eq_pow hcfg fun t ht => ?_
  set β : MulAut L := MulAut.conjNormal t with hβ
  have hβU : ∀ w : L, w ∈ (T ⊓ L).subgroupOf L → β w ∈ (T ⊓ L).subgroupOf L := by
    intro w hw
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    rw [hβ, MulAut.conjNormal_apply]
    exact ⟨T.mul_mem (T.mul_mem ht.1 hw.1) (T.inv_mem ht.1), hcfg.normal.conj_mem _ hw.2 t⟩
  set α : MulAut (adjointGroup .G2 K) := (e.trans β).trans e.symm with hα
  have hαU : ((posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)).map α.toMonoidHom =
      (posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [Subgroup.card_map_of_injective α.injective])
    rintro _ ⟨z, hz, rfl⟩
    have h1 : e z ∈ (T ⊓ L).subgroupOf L := he ▸ Subgroup.mem_map_of_mem e.toMonoidHom hz
    exact hmemU _ (hβU _ h1)
  obtain ⟨s, hs⟩ := exists_pow_of_map_posUnipotent hK hn α hαU
  refine ⟨s, fun x hx => ?_⟩
  have hxL : x ∈ L := hcfg.le hx
  have htx : t * x * t⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 ht.2 x).1 hx
  have hxC : e.symm ⟨x, hxL⟩ ∈ PC := by
    change ((e (e.symm ⟨x, hxL⟩) : L) : A) ∈ P
    rw [MulEquiv.apply_symm_apply]
    exact hx
  have hxB : ((e.symm ⟨x, hxL⟩ : adjointGroup .G2 K) : ModGL .G2 K) ∈ borelGroup .G2 K :=
    hHm ⟨_, hPHC hxC, rfl⟩
  have hαx : α (e.symm ⟨x, hxL⟩) = e.symm (β ⟨x, hxL⟩) := by
    rw [hα, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hyP : (α (e.symm ⟨x, hxL⟩))⁻¹ * e.symm ⟨x, hxL⟩ ^ 2 ^ s ∈ PC := by
    change ((e ((α (e.symm ⟨x, hxL⟩))⁻¹ * e.symm ⟨x, hxL⟩ ^ 2 ^ s) : L) : A) ∈ P
    rw [map_mul, map_inv, map_pow, hαx, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
      Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hβ, MulAut.conjNormal_apply]
    exact P.mul_mem (P.inv_mem htx) (P.pow_mem hx _)
  have hy1 := Subgroup.disjoint_def.1 hdisj hyP (hs _ hxB)
  have h2 := congrArg e (inv_mul_eq_one.1 hy1)
  rw [hαx, MulEquiv.apply_symm_apply, map_pow, MulEquiv.apply_symm_apply] at h2
  have h3 := congrArg Subtype.val h2
  rwa [hβ, MulAut.conjNormal_apply, Subgroup.coe_pow] at h3

end CFSG.Quasithin.P134

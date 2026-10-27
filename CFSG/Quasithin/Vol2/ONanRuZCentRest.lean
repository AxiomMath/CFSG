module

import CFSG.Quasithin.H13.L32AKG1468d
import CFSG.Quasithin.Vol2.ONanRuZJCheck
public import CFSG.Quasithin.H13.L32ARuU1Inputs
public import CFSG.Quasithin.Vol2.Ch10SecA312AA
public import CFSG.Quasithin.Vol2.Ch10SecA312AW
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.Sporadic.Schreier.RuOddCoreBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique CFSG.Sporadic.RuSchreier

theorem mem_of_pow_odd_eq_one_of_index_two {G : Type*} [Group G] {D K : Subgroup G}
    (h2 : (D.subgroupOf K).index = 2) {x : G} (hx : x ∈ K) {m : ℕ} (hm : m % 2 = 1)
    (hxm : x ^ m = 1) : x ∈ D := by
  have : (D.subgroupOf K).Normal := Subgroup.normal_of_index_eq_two h2
  have h1 : (⟨x, hx⟩ : K) ^ 2 ∈ D.subgroupOf K := by
    simpa [h2] using Subgroup.pow_index_mem (D.subgroupOf K) (⟨x, hx⟩ : K)
  obtain ⟨n, hn⟩ : ∃ n, m = 2 * n + 1 := ⟨m / 2, by omega⟩
  have hxm' : ((⟨x, hx⟩ : K) ^ 2) ^ n * (⟨x, hx⟩ : K) = 1 := by
    have h' : (⟨x, hx⟩ : K) ^ m = 1 := Subtype.ext (by simpa using hxm)
    rw [hn] at h'
    rw [← pow_mul, ← pow_succ]
    exact h'
  have : (⟨x, hx⟩ : K) = (((⟨x, hx⟩ : K) ^ 2) ^ n)⁻¹ := eq_inv_of_mul_eq_one_right hxm'
  have h3 : (⟨x, hx⟩ : K) ∈ D.subgroupOf K := by
    rw [this]
    exact inv_mem (pow_mem h1 n)
  exact Subgroup.mem_subgroupOf.mp h3

theorem ruJ_le_of_index_two
    {D : Subgroup (Equiv.Perm (Fin 4060))} (h2 : (D.subgroupOf ruC).index = 2) : ruJ ≤ D := by
  refine closure_list_le (fun g hg => ?_)
  obtain ⟨k, hk, rfl⟩ : ∃ k < 6, g = ruJGens.getD k 1 := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    exact ⟨i, by simpa [ruJGens_length] using hi, (List.getD_eq_getElem ruJGens 1 hi).symm⟩
  obtain ⟨hm, hmA, hmB, hx, ha, hb⟩ := CFSG.Quasithin.H13.KGRu.ruOdd_pow hk
  have hjC : ruJGens.getD k 1 ∈ ruC := ruJ_leC (ruJGens_getD_mem k)
  have haC : evalSigned [ruC0, ruC1] (CFSG.Quasithin.H13.KGRu.ruOddA k) ∈ ruC :=
    evalSigned_mem (pair_mem ruC0_memC ruC1_memC) _
  have hbC : evalSigned [ruC0, ruC1] (CFSG.Quasithin.H13.KGRu.ruOddB k) ∈ ruC :=
    evalSigned_mem (pair_mem ruC0_memC ruC1_memC) _
  have hxD := mem_of_pow_odd_eq_one_of_index_two h2 (mul_mem (mul_mem hjC haC) hbC) hm hx
  have haD := mem_of_pow_odd_eq_one_of_index_two h2 haC hmA ha
  have hbD := mem_of_pow_odd_eq_one_of_index_two h2 hbC hmB hb
  have hj : ruJGens.getD k 1 = (ruJGens.getD k 1 * evalSigned [ruC0, ruC1]
      (CFSG.Quasithin.H13.KGRu.ruOddA k) * evalSigned [ruC0, ruC1]
      (CFSG.Quasithin.H13.KGRu.ruOddB k)) * (evalSigned [ruC0, ruC1]
      (CFSG.Quasithin.H13.KGRu.ruOddB k))⁻¹ * (evalSigned [ruC0, ruC1]
      (CFSG.Quasithin.H13.KGRu.ruOddA k))⁻¹ := by group
  rw [hj]
  exact mul_mem (mul_mem hxD (inv_mem hbD)) (inv_mem haD)

theorem exists_conj_ruZ_of_card_gt
    {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruP)
    (h2 : orderOf t = 2) (hc : 116480 < Nat.card ↥(ruP ⊓ Subgroup.centralizer {t})) :
    ∃ g ∈ ruP, g * ruZ * g⁻¹ = t := by
  have hinv : t ∈ {t | t ∈ ruP ∧ orderOf t = 2} := ⟨ht, h2⟩
  rw [ruInvolutions_eq] at hinv
  rcases hinv with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · exact ⟨g, hg, rfl⟩
  · rw [← Nat.card_congr (conjCentralizerEquiv hg ruA0).toEquiv, ruCentralizer_a, card_ruL]
      at hc
    exact absurd hc (lt_irrefl _)

theorem exists_embedding_ruC
    {X : Type} [Group X] [Finite X] (ψ : X ≃* ↥ruP)
    {B : Subgroup X} {u : X} (hu : orderOf u = 2) (hB : 116480 < Nat.card ↥B)
    (hbu : ∀ b : ↥B, (b : X) * u = u * b) :
    ∃ f : ↥B →* Equiv.Perm (Fin 4060), Function.Injective f ∧ ∀ b, f b ∈ ruC := by
  obtain ⟨t, ht⟩ : ∃ t : Equiv.Perm (Fin 4060), t = ((ψ u : ↥ruP) : Equiv.Perm (Fin 4060)) :=
    ⟨_, rfl⟩
  have htP : t ∈ ruP := ht ▸ (ψ u).2
  have htord : orderOf t = 2 := by rw [ht, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hu]
  have hcomm : ∀ b : ↥B, ((ψ b : ↥ruP) : Equiv.Perm (Fin 4060)) * t =
      t * ((ψ b : ↥ruP) : Equiv.Perm (Fin 4060)) := by
    intro b
    rw [ht, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hbu b]
  have hcent : 116480 < Nat.card ↥(ruP ⊓ Subgroup.centralizer {t}) := by
    refine hB.trans_le (Nat.card_le_card_of_injective
      (fun b => ⟨((ψ b : ↥ruP) : Equiv.Perm (Fin 4060)), (ψ b).2,
        Subgroup.mem_centralizer_singleton_iff.mpr (hcomm b)⟩) ?_)
    intro a b h
    have h' : ((ψ a : ↥ruP) : Equiv.Perm (Fin 4060)) = ψ b :=
      congrArg (fun x : ↥(ruP ⊓ Subgroup.centralizer {t}) => (x : Equiv.Perm (Fin 4060))) h
    exact Subtype.ext (ψ.injective (Subtype.ext h'))
  obtain ⟨g, hg, hgt⟩ := exists_conj_ruZ_of_card_gt htP htord hcent
  let f : ↥B →* Equiv.Perm (Fin 4060) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (ruP.subtype.comp (ψ.toMonoidHom.comp B.subtype))
  have hfapp : ∀ b : ↥B, f b = g⁻¹ * ((ψ b : ↥ruP) : Equiv.Perm (Fin 4060)) * g := by
    intro b
    simp [f]
  refine ⟨f, fun a b h => ?_, fun b => ?_⟩
  · rw [hfapp, hfapp] at h
    exact Subtype.ext (ψ.injective (Subtype.ext (mul_left_cancel (mul_right_cancel h))))
  · rw [ruC_eq_centralizer, hfapp, Subgroup.mem_inf]
    refine ⟨ruP.mul_mem (ruP.mul_mem (ruP.inv_mem hg) (ψ b).2) hg, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := hcomm b
    rw [← hgt] at hc
    calc g⁻¹ * ((ψ b : ↥ruP) : Equiv.Perm (Fin 4060)) * g * ruZ
        = g⁻¹ * (((ψ b : ↥ruP) : Equiv.Perm (Fin 4060)) * (g * ruZ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * ruZ * g⁻¹) * ((ψ b : ↥ruP) : Equiv.Perm (Fin 4060))) * g := by rw [hc]
      _ = ruZ * (g⁻¹ * ((ψ b : ↥ruP) : Equiv.Perm (Fin 4060)) * g) := by group

theorem comap_ruJ_eq_pCore
    {B : Type*} [Group B] [Finite B] {f : B →* Equiv.Perm (Fin 4060)}
    (hfinj : Function.Injective f) (hfC : ∀ b, f b ∈ ruC) (hB : Nat.card B = 122880)
    (hO2 : Nat.card ↥(CFSG.pCore 2 B) = 2 ^ 11) :
    ruJ ≤ f.range ∧ ruJ.comap f = CFSG.pCore 2 B := by
  have hDC : f.range ≤ ruC := by
    rintro _ ⟨b, rfl⟩
    exact hfC b
  have hDcard : Nat.card ↥f.range = 122880 := by
    rw [← hB]
    exact (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).symm
  have h2 : (f.range.subgroupOf ruC).index = 2 := by
    have h := Subgroup.card_mul_index (f.range.subgroupOf ruC)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv, hDcard, card_ruC] at h
    omega
  have hJD : ruJ ≤ f.range := ruJ_le_of_index_two h2
  have hJbN : (ruJ.comap f).Normal := by
    refine ⟨fun n hn b => ?_⟩
    rw [Subgroup.mem_comap] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    have hnj : (⟨f n, hfC n⟩ : ruC) ∈ ruJ.subgroupOf ruC := hn
    exact ruJ_normal.conj_mem _ hnj ⟨f b, hfC b⟩
  have hJbcard : Nat.card ↥(ruJ.comap f) = 2 ^ 11 := by
    have h1 : (ruJ.comap f).map f = ruJ := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.mpr hJD
    rw [← Subgroup.card_map_of_injective hfinj, h1, card_ruJ]
    norm_num
  have hJbP : IsPGroup 2 ↥(ruJ.comap f) := IsPGroup.of_card hJbcard
  exact ⟨hJD, Subgroup.eq_of_le_of_card_ge (le_sSup ⟨hJbN, hJbP⟩) (by rw [hO2, hJbcard])⟩

theorem a312ZCentRestRuA5_holds :
    A312ZCentRestRuA5 := by
  intro X _ _ T B h5 hO2 hRu hc
  obtain ⟨-, -, -, hT, -, -, -, -, ⟨z, hzT, hz1, -, hzB⟩, V, hVB, hVe, hBV, hVBV, hV1, hOV, -⟩ :=
    hc
  obtain ⟨e⟩ := hRu
  let ψ : X ≃* ↥ruP := (Subgroup.topEquiv.symm.trans e).trans ruEquivP
  have hB : Nat.card ↥B = 122880 := by
    obtain ⟨eA⟩ := h5
    have hQ : Nat.card (ModO2 B) = 60 := by
      rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B), hO2,
      show Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 60 from hQ]
    norm_num
  obtain ⟨k, hk1, hk2⟩ := exists_pow_involution hT.isPGroup (γ := ⟨z, hzT⟩)
    (fun h => hz1 (congrArg Subtype.val h))
  have hu1 : z ^ k ≠ 1 := fun h => hk1 (Subtype.ext (by simpa using h))
  have hu2 : z ^ k * z ^ k = 1 := by simpa using congrArg Subtype.val hk2
  have hord : orderOf (z ^ k) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  obtain ⟨f, hfinj, hfC⟩ := exists_embedding_ruC ψ hord (by omega) fun b =>
    (Commute.pow_left (hzB b b.2) k).eq.symm
  obtain ⟨hJD, hJbeq⟩ := comap_ruJ_eq_pCore hfinj hfC hB hO2
  have hVN : (V.subgroupOf B).Normal := by
    refine ⟨fun n hn b => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hBV b.2) n).mp hn
  have hVP : IsPGroup 2 ↥(V.subgroupOf B) := fun x => ⟨1, Subtype.ext (Subtype.ext (by
    simpa using hVe.2 ((x : B) : X) (Subgroup.mem_subgroupOf.mp x.2)))⟩
  have hVle : V.subgroupOf B ≤ ruJ.comap f := hJbeq ▸ le_sSup ⟨hVN, hVP⟩
  have hVcomm : ∀ v ∈ V, ∀ b : ↥B, (v : X) * b = b * v := by
    intro v hv b
    have hv' : (⟨v, hVB hv⟩ : ↥B) ∈ ruJ.comap f := hVle (Subgroup.mem_subgroupOf.mpr hv)
    have hcJ : ∀ j ∈ ruJ, f ⟨v, hVB hv⟩ * j = j * f ⟨v, hVB hv⟩ := by
      intro j hj
      obtain ⟨b', rfl⟩ := hJD hj
      have hb' : b' ∈ CFSG.pCore 2 ↥B := hJbeq ▸ hj
      have hb'' : (b' : X) ∈ pCoreOf 2 B := ⟨b', hb', rfl⟩
      have hvb : v * b' = b' * v := Subgroup.mem_centralizer_iff.mp (hOV hb'') v hv
      rw [← map_mul, ← map_mul]
      exact congrArg f (Subtype.ext hvb)
    have hmul : f ⟨v, hVB hv⟩ * f b = f b * f ⟨v, hVB hv⟩ := by
      rcases ruJ_center_eq hv' hcJ with h1 | h1
      · rw [h1, one_mul, mul_one]
      · rw [h1]
        exact (ruZ_central (f b) (hfC b)).symm
    exact congrArg Subtype.val (hfinj (show f (⟨v, hVB hv⟩ * b) = f (b * ⟨v, hVB hv⟩) by
      rw [map_mul, map_mul]; exact hmul))
  have hVc : V ≤ Subgroup.centralizer (B : Set X) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (hVcomm v hv ⟨b, hb⟩).symm
  exact hV1 (hVBV.symm.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hVc))

end CFSG.Quasithin.Vol2.Ch10.A312A

module

public import CFSG.Quasithin.Vol2.Ch11SecOE5F
public import CFSG.Quasithin.Vol2.Ch11SecGTBar
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.J4U

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem finite_mulAut (V : Type) [Group V] [Finite V] : Finite (MulAut V) :=
  Finite.of_injective (fun α : MulAut V => α.toEquiv) fun _ _ h => MulEquiv.toEquiv_injective h

theorem card_mulAut_eq {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) {X : Type} [Group X] (e : X ≃* SL(2, F)) :
    Nat.card (MulAut X) = 120 := by
  obtain ⟨eA⟩ := QuasithinUnique.Setup.Family.specialLinear_two_equiv_alternating_five F hF
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by norm_num)
  rw [Nat.card_congr (MulAut.congr (e.trans eA)).toEquiv,
    ← Nat.card_congr (Equiv.ofBijective _ hb), Nat.card_perm, Nat.card_fin]
  rfl

theorem not_dvd_card_mulAut {V : Type} [Group V] [Finite V] (hV : IsPGroup 2 V)
    (h8 : Nat.card V ≤ 8) : ¬ 5 ∣ Nat.card (MulAut V) := by
  intro h5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_mulAut V
  obtain ⟨α, hα⟩ := exists_prime_orderOf_dvd_card' 5 h5
  set A := Subgroup.zpowers α with hAdef
  have hA : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hα, pow_one])
  let C : Subgroup V :=
    { carrier := {v | ∀ a ∈ A, a v = v}
      mul_mem' := fun {x y} hx hy a ha => by rw [map_mul, hx a ha, hy a ha]
      one_mem' := fun a _ => map_one a
      inv_mem' := fun {x} hx a ha => by rw [map_inv, hx a ha] }
  have hmod := hA.card_modEq_card_fixedPoints V
  have hset : MulAction.fixedPoints A V = (C : Set V) := by
    ext v
    simp only [MulAction.mem_fixedPoints, Subtype.forall, Subgroup.mk_smul, MulAut.smul_def]
    rfl
  have hC : Nat.card (MulAction.fixedPoints A V) = Nat.card C := by
    rw [hset]
    rfl
  obtain ⟨k, hk⟩ := hV.exists_card_eq
  have hCdvd : Nat.card C ∣ 2 ^ k := hk ▸ Subgroup.card_subgroup_dvd_card C
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hCdvd
  have hk3 : k ≤ 3 := by
    by_contra h
    have : 16 ≤ 2 ^ k := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hC, hj, hk] at hmod
  have hjk' : j = k := by
    unfold Nat.ModEq at hmod
    interval_cases k <;> interval_cases j <;> first | rfl | (norm_num at hmod)
  have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C (by rw [hj, hjk', hk])
  have hα1 : α = 1 := MulEquiv.ext fun v => by
    have hv : v ∈ C := htop ▸ Subgroup.mem_top v
    rw [MulAut.one_apply]
    exact hv α (Subgroup.mem_zpowers α)
  rw [hα1, orderOf_one] at hα
  norm_num at hα

@[expose] noncomputable def actHom {S B : Subgroup G}
    (hSB : S ≤ Subgroup.normalizer (B : Set G)) : ↥S →* MulAut (SecG.Bar.KBar B) :=
  (SecG.Bar.aut B).comp (Subgroup.inclusion hSB)

@[expose] noncomputable def actKer {S B : Subgroup G}
    (hSB : S ≤ Subgroup.normalizer (B : Set G)) : Subgroup G :=
  (actHom hSB).ker.map S.subtype

theorem actKer_le {S B : Subgroup G} (hSB : S ≤ Subgroup.normalizer (B : Set G)) :
    actKer hSB ≤ S :=
  Subgroup.map_subtype_le _

theorem mem_actKer_iff {S B : Subgroup G} (hSB : S ≤ Subgroup.normalizer (B : Set G)) {s : G}
    (hs : s ∈ S) : s ∈ actKer hSB ↔ SecG.Bar.aut B ⟨s, hSB hs⟩ = 1 := by
  constructor
  · rintro ⟨s', hs', rfl⟩
    exact hs'
  · intro h
    exact ⟨⟨s, hs⟩, h, rfl⟩

theorem relIndex_actKer_le [Finite G] {S B : Subgroup G}
    (hS : IsPGroup 2 S) (hB : IsL24Sub S B) : (actKer hB.2.2.1).relIndex S ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSB := hB.2.2.1
  obtain ⟨-, -, -, F, _, _, hF, ⟨e⟩⟩ := id hB
  have hcard : Nat.card (MulAut (SecG.Bar.KBar B)) = 120 := card_mulAut_eq hF e
  have : Finite (MulAut (SecG.Bar.KBar B)) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h1 : (actKer hSB).relIndex S = Nat.card (actHom hSB).range := by
    rw [Subgroup.relIndex, actKer, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective, Subgroup.index_ker]
  have h2 : IsPGroup 2 (actHom hSB).range :=
    hS.of_surjective (actHom hSB).rangeRestrict (actHom hSB).rangeRestrict_surjective
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have h3 : Nat.card (actHom hSB).range ∣ 120 := hcard ▸ Subgroup.card_subgroup_dvd_card _
  rw [h1, hk]
  rw [hk] at h3
  have h4 : 2 ^ k ∣ 8 := by
    have hc : Nat.Coprime (2 ^ k) 15 := Nat.Coprime.pow_left _ (by norm_num)
    have h3' : 2 ^ k ∣ 8 * 15 := by
      rw [show (8 : ℕ) * 15 = 120 by norm_num]
      exact h3
    exact hc.dvd_of_dvd_mul_right h3'
  exact Nat.le_of_dvd (by norm_num) h4

theorem comm_mem_of_mem_actKer {S B : Subgroup G} (hSB : S ≤ Subgroup.normalizer (B : Set G))
    {s b : G} (hs : s ∈ actKer hSB) (hb : b ∈ B) : s * b * s⁻¹ * b⁻¹ ∈ pCoreOf 2 B := by
  obtain ⟨s', hs', rfl⟩ := hs
  have h1 := SecG.Bar.comm_mem_of_aut_eq_one (g := Subgroup.inclusion hSB s')
    (MonoidHom.mem_ker.mp hs') b hb
  show _ ∈ (CFSG.Open.pCore 2 ↥B).map B.subtype
  exact h1

theorem pCoreOf_le_actKer {S B : Subgroup G} (hSB : S ≤ Subgroup.normalizer (B : Set G))
    (hO : pCoreOf 2 B ≤ S) : pCoreOf 2 B ≤ actKer hSB := by
  intro o ho
  have hoS := hO ho
  rw [mem_actKer_iff hSB hoS]
  have ho' : o ∈ (CFSG.pCore 2 ↥B).map B.subtype := by
    have h : pCoreOf 2 B = (CFSG.Open.pCore 2 ↥B).map B.subtype := rfl
    rw [h] at ho
    exact ho
  obtain ⟨o', ho', rfl⟩ := ho'
  refine MulEquiv.ext fun x => ?_
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [SecG.Bar.aut_mk, MulAut.one_apply, QuotientGroup.eq]
  have e : (SecG.conjK B ⟨B.subtype o', hSB hoS⟩ k)⁻¹ * k = o' * (k⁻¹ * o'⁻¹ * k⁻¹⁻¹) :=
    Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SecG.conjK_apply_coe, Subgroup.coe_subtype]
      group)
  rw [e]
  exact mul_mem ho' ((CFSG.pCore_normal).conj_mem _ (inv_mem ho') k⁻¹)

theorem le_normalizer_actKer {S B : Subgroup G} (hSB : S ≤ Subgroup.normalizer (B : Set G))
    (hO : pCoreOf 2 B ≤ S) : B ≤ Subgroup.normalizer (actKer hSB : Set G) := by
  have hBO : B ≤ Subgroup.normalizer (pCoreOf 2 B : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B)
  have key : ∀ b ∈ B, ∀ s ∈ actKer hSB, b * s * b⁻¹ ∈ actKer hSB := by
    intro b hb s hs
    have h1 := comm_mem_of_mem_actKer hSB hs (inv_mem hb)
    have h2 : b * (s * b⁻¹ * s⁻¹ * b⁻¹⁻¹) * b⁻¹ ∈ pCoreOf 2 B :=
      (Subgroup.mem_normalizer_iff.mp (hBO hb) _).mp h1
    have e : b * s * b⁻¹ = (b * (s * b⁻¹ * s⁻¹ * b⁻¹⁻¹) * b⁻¹) * s := by group
    rw [e]
    exact mul_mem (pCoreOf_le_actKer hSB hO h2) hs
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨key b hb s, fun h => ?_⟩
  have h1 := key b⁻¹ (inv_mem hb) _ h
  have e : b⁻¹ * (b * s * b⁻¹) * b⁻¹⁻¹ = s := by group
  rwa [e] at h1

theorem le_normalizer_actKer' {S B : Subgroup G} (hSB : S ≤ Subgroup.normalizer (B : Set G)) :
    S ≤ Subgroup.normalizer (actKer hSB : Set G) := by
  have key : ∀ s ∈ S, ∀ k ∈ actKer hSB, s * k * s⁻¹ ∈ actKer hSB := by
    intro s hs k hk
    have hkS : k ∈ S := actKer_le hSB hk
    have hskS : s * k * s⁻¹ ∈ S := mul_mem (mul_mem hs hkS) (inv_mem hs)
    rw [mem_actKer_iff hSB hkS] at hk
    rw [mem_actKer_iff hSB hskS]
    have e : (⟨s * k * s⁻¹, hSB hskS⟩ : ↥(Subgroup.normalizer (B : Set G))) =
        ⟨s, hSB hs⟩ * ⟨k, hSB hkS⟩ * ⟨s, hSB hs⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, hk, mul_one, map_inv, mul_inv_cancel]
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨key s hs k, fun h => ?_⟩
  have h1 := key s⁻¹ (inv_mem hs) _ h
  have e : s⁻¹ * (s * k * s⁻¹) * s⁻¹⁻¹ = k := by group
  rwa [e] at h1

theorem normalizer_le_normalizer_center {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer (((Subgroup.center H).map H.subtype : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (H : Set G), ∀ v ∈ (Subgroup.center H).map H.subtype,
      g * v * g⁻¹ ∈ (Subgroup.center H).map H.subtype := by
    rintro g hg _ ⟨v, hv, rfl⟩
    have hvH : g * v * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hg v).mp v.2
    refine ⟨⟨_, hvH⟩, Subgroup.mem_center_iff.mpr fun h => Subtype.ext ?_, rfl⟩
    have hh : g⁻¹ * h * g ∈ H := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) h).mp h.2
      rwa [inv_inv] at this
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hv ⟨_, hh⟩)
    simp only [Subgroup.coe_mul] at hc
    simp only [Subgroup.coe_mul]
    calc (h : G) * (g * v * g⁻¹) = g * ((g⁻¹ * h * g) * v) * g⁻¹ := by group
      _ = g * (v * (g⁻¹ * h * g)) * g⁻¹ := by rw [hc]
      _ = g * v * g⁻¹ * h := by group
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨key g hg v, fun h => ?_⟩
  have h1 := key g⁻¹ (inv_mem hg) _ h
  have e : g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v := by group
  rwa [e] at h1

theorem range_eq_bot_of_not_dvd [Finite G] {S B : Subgroup G}
    (hB : IsL24Sub S B) {H : Type} [Group H] (f : ↥B →* H) (h5 : ¬ 5 ∣ Nat.card f.range) :
    f.range = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hperf, -, F, _, _, hF, ⟨e⟩⟩ := hB
  obtain ⟨eA⟩ := QuasithinUnique.Setup.Family.specialLinear_two_equiv_alternating_five F hF
  set O := CFSG.pCore 2 ↥B with hO
  set e' : (↥B ⧸ O) ≃* alternatingGroup (Fin 5) := e.trans eA with he'
  have hKn : (((f.ker).map (QuotientGroup.mk' O)).map e'.toMonoidHom).Normal :=
    ((f.normal_ker).map _ (QuotientGroup.mk'_surjective O)).map _ e'.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (((f.ker).map (QuotientGroup.mk' O)).map e'.toMonoidHom) with h | h
  ·
    exfalso
    apply h5
    have hKO : f.ker ≤ O := by
      intro x hx
      have h1 : e' (QuotientGroup.mk' O x) ∈
          ((f.ker).map (QuotientGroup.mk' O)).map e'.toMonoidHom := ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [h, Subgroup.mem_bot, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at h1
      exact h1
    have h60 : O.index = 60 := by
      rw [Subgroup.index, Nat.card_congr e.toEquiv, O11.card_sl2_four hF]
    rw [← Subgroup.index_ker]
    exact (Dvd.intro_left 12 (by norm_num : 12 * 5 = 60)).trans
      (h60 ▸ Subgroup.index_dvd_of_le hKO)
  ·
    have hK : (f.ker).map (QuotientGroup.mk' O) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have h1 : e' y ∈ ((f.ker).map (QuotientGroup.mk' O)).map e'.toMonoidHom :=
        h ▸ Subgroup.mem_top _
      obtain ⟨y', hy', hyy'⟩ := h1
      rwa [show y' = y from e'.injective hyy'] at hy'
    have hrange : f.range = O.map f := by
      apply le_antisymm
      · rintro _ ⟨b, rfl⟩
        obtain ⟨k, hk, hkb⟩ : QuotientGroup.mk' O b ∈ (f.ker).map (QuotientGroup.mk' O) :=
          hK ▸ Subgroup.mem_top _
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkb
        refine ⟨k⁻¹ * b, hkb, ?_⟩
        rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul]
      · rintro _ ⟨o, -, rfl⟩
        exact ⟨o, rfl⟩
    have h2 : IsPGroup 2 f.range := hrange ▸ (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).map f
    have : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hperf
    have : Group.IsPerfect ↥f.range :=
      Group.IsPerfect.ofSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
    have : Finite ↥f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    have := h2.isNilpotent
    have hsub := OE5.subsingleton_of_perfect_solvable (R := ↥f.range)
    rw [eq_bot_iff]
    intro y hy
    have := Subsingleton.elim (⟨y, hy⟩ : ↥f.range) 1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

theorem le_centralizer_of_card_le [Finite G] {S B : Subgroup G}
    (hB : IsL24Sub S B) {V : Subgroup G} (hV : IsPGroup 2 V) (h8 : Nat.card V ≤ 8)
    (hBV : B ≤ Subgroup.normalizer (V : Set G)) : B ≤ Subgroup.centralizer (V : Set G) := by
  set f : ↥B →* MulAut ↥V := (SecG.conjK V).comp (Subgroup.inclusion hBV) with hf
  have := finite_mulAut ↥V
  have h5 : ¬ 5 ∣ Nat.card f.range := fun h =>
    not_dvd_card_mulAut hV h8 (h.trans (Subgroup.card_subgroup_dvd_card _))
  have hbot := range_eq_bot_of_not_dvd hB f h5
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 : f ⟨b, hb⟩ = 1 := by
    have : f ⟨b, hb⟩ ∈ f.range := ⟨_, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have h2 := congrArg (fun α : MulAut ↥V => ((α ⟨v, hv⟩ : ↥V) : G)) h1
  simp only [hf, MonoidHom.comp_apply, MulAut.one_apply, SecG.conjK_apply_coe,
    Subgroup.coe_inclusion] at h2
  calc v * b = b * v * b⁻¹ * b := by rw [h2]
    _ = b * v := by group

end CFSG.Quasithin.Vol2.Ch11.SecS.J4U

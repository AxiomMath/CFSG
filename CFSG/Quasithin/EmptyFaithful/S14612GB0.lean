module

public import CFSG.Quasithin.EmptyFaithful.S14612GA2
public import CFSG.Quasithin.EmptyFaithful.S14612EF
public import CFSG.Quasithin.EmptyFaithful.S146P19
public import CFSG.Quasithin.EmptyFaithful.F918C1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
open CFSG.Quasithin.S1417
open scoped commutatorElement

section Abstract

variable {Hh : Type} [Group Hh] {W : Type} [CommGroup W] [Finite W]

theorem class_hom_data (hW : ∀ w : W, w ^ 2 = 1)
    (ρ : Hh →* MulAut W) (P0 T0 : Subgroup Hh) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk1 : ∀ x : Hh, ρ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hk2 : ∀ S : Subgroup Hh, S.Normal → IsPGroup 2 S → ∀ x ∈ S, ρ x = 1)
    (hPn : P0.Normal) (hkerP : ρ.ker ≤ P0)
    (hpp : ∀ x ∈ P0, ∃ k : ℕ, ρ (x ^ p ^ k) = 1)
    (hHeq : P0 ⊔ T0 = ⊤) (hT2 : IsPGroup 2 T0) (hTi : ¬ 2 ∣ T0.index)
    (hmin : ∀ N : Subgroup Hh, N.Normal → ρ.ker ≤ N → N ≤ P0 → N = ρ.ker ∨ N = P0)
    (hlt : ¬ P0 ≤ ρ.ker) (hcard : Nat.card ↥(P0.map ρ) ≠ p)
    (hq : qOf ρ.range ≤ 2) (hsq : IsQuotientOfSQTKTC ↥ρ.range)
    {w₀ : W} (hw₀ : ∀ t ∈ T0, ρ t w₀ = w₀)
    (hgen : Subgroup.closure {w | ∃ h : Hh, w = ρ h w₀} = ⊤) :
    PStr14612 (resBeta ρ).range (T0.map (resBeta ρ)) (P0.map (resBeta ρ)) p ∧
      fixV (P0.map (resBeta ρ)) = ⊥ ∧
      (∀ W' : Subgroup ↥(kOf ρ),
        (∀ g ∈ (resBeta ρ).range, ∀ z ∈ fixV (T0.map (resBeta ρ)), g z ∈ W') → W' = ⊤) ∧
      (∀ w : W, ∃ a ∈ kOf ρ, ∃ c ∈ fixV ρ.range, w = a * c) ∧
      kOf ρ ⊓ fixV ρ.range = ⊥ ∧ Nat.card ↥(fixV ρ.range) ≤ 2 := by
  classical
  set X : Subgroup (MulAut W) := ρ.range with hX
  set P : Subgroup (MulAut W) := P0.map ρ with hP
  set Tb : Subgroup (MulAut W) := T0.map ρ with hTb
  have hPX : P ≤ X := Subgroup.map_le_range ρ P0
  have hXeq : X = P ⊔ Tb := by
    rw [hX, hP, hTb, MonoidHom.range_eq_map, ← hHeq, Subgroup.map_sup]
  have hPn' : NormalIn X P := by
    rintro _ ⟨h, rfl⟩ _ ⟨a, ha, rfl⟩
    exact ⟨h * a * h⁻¹, hPn.conj_mem a ha h, by simp⟩
  have hPodd : Odd (Nat.card P) := by
    have : Fact p.Prime := ⟨hp⟩
    have hpg : IsPGroup p ↥P := by
      rintro ⟨x, a, ha, rfl⟩
      obtain ⟨k, hk⟩ := hpp a ha
      exact ⟨k, Subtype.ext (by simpa [map_pow] using hk)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hpg
    rw [hn]
    exact Odd.pow (hp.eq_two_or_odd'.resolve_left hp2)
  have hv : w₀ ∈ fixV Tb := by
    rintro _ ⟨t, ht, rfl⟩
    exact hw₀ t ht
  have hgen' : Subgroup.closure {w | ∃ x ∈ X, w = x w₀} = ⊤ := by
    rw [← hgen]
    congr 1
    ext w
    constructor
    · rintro ⟨_, ⟨h, rfl⟩, hw⟩
      exact ⟨h, hw⟩
    · rintro ⟨h, hw⟩
      exact ⟨ρ h, ⟨h, rfl⟩, hw⟩
  obtain ⟨v', hv', c, hc, hvv, hv'T, hcommX, hsup, hinf, hK⟩ :=
    exists_split14612 hW hPodd hPn' hPX hXeq hv hgen'
  have hkOf : kOf ρ = commV P := hcommX
  have hsplit : ∀ w : W, ∃ a ∈ kOf ρ, ∃ c ∈ fixV ρ.range, w = a * c := by
    intro w
    have hw : w ∈ commV P ⊔ fixV X := by rw [hsup]; exact Subgroup.mem_top w
    obtain ⟨a, ha, c, hc, hac⟩ := Subgroup.mem_sup.mp hw
    exact ⟨a, hkOf ▸ ha, c, hc, hac.symm⟩
  have hinfK : kOf ρ ⊓ fixV ρ.range = ⊥ := by rw [hkOf]; exact hinf
  have hkb : (resBeta ρ).ker = ρ.ker := ker_resBeta ρ hsplit
  have hV' : ∀ v : ↥(kOf ρ), v ^ 2 = 1 := fun v => Subtype.ext (hW v)
  have hstr : PStr14612 (resBeta ρ).range (T0.map (resBeta ρ)) (P0.map (resBeta ρ)) p := by
    refine pstr_of_hom hV' (resBeta ρ) P0 T0 hp hp2 ?_ ?_ hPn ?_ ?_ hHeq hT2 hTi ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have : x ∈ (resBeta ρ).ker := hx
      rw [hkb] at this
      exact hk1 x this
    · intro S hS hS2 x hx
      have h1 : x ∈ ρ.ker := hk2 S hS hS2 x hx
      rw [← hkb] at h1
      exact h1
    · rw [hkb]
      exact hkerP
    · intro x hx
      obtain ⟨k, hk⟩ := hpp x hx
      have h1 : x ^ p ^ k ∈ ρ.ker := hk
      rw [← hkb] at h1
      exact ⟨k, h1⟩
    · intro N hN hkN hNP
      rw [hkb] at hkN ⊢
      exact hmin N hN hkN hNP
    · rw [hkb]
      exact hlt
    · rw [card_map_eq_of_ker_eq hkb P0]
      exact hcard
    · exact (qhat_resBeta_le ρ hsplit hinfK).trans hq
    · exact isQuotientOfSQTK_of_mulEquiv
        ((suppData_split ρ hsplit hinfK).restrictEquiv.trans
          (MulEquiv.subgroupCongr (range_resBeta ρ).symm)) hsq
  have hfix : fixV (P0.map (resBeta ρ)) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun v hv => ?_
    have h1 : (v : W) ∈ fixV P := by
      rintro _ ⟨a, ha, rfl⟩
      have := congrArg (fun z : ↥(kOf ρ) => (z : W)) (hv (resBeta ρ a) ⟨a, ha, rfl⟩)
      simpa [resBeta_apply] using this
    have h2 : (v : W) ∈ commV P ⊓ fixV P := ⟨hkOf ▸ v.2, h1⟩
    rw [commV_inf_fixV_eq_bot hW hPodd, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hgenK : ∀ W' : Subgroup ↥(kOf ρ),
      (∀ g ∈ (resBeta ρ).range, ∀ z ∈ fixV (T0.map (resBeta ρ)), g z ∈ W') → W' = ⊤ := by
    intro W' hW'
    have hv'K : v' ∈ kOf ρ := hkOf ▸ hv'
    set z : ↥(kOf ρ) := ⟨v', hv'K⟩ with hz
    have hzfix : z ∈ fixV (T0.map (resBeta ρ)) := by
      rintro _ ⟨t, ht, rfl⟩
      refine Subtype.ext ?_
      rw [resBeta_apply]
      exact hv'T (ρ t) ⟨t, ht, rfl⟩
    have hmem : ∀ x ∈ X, x v' ∈ W'.map (kOf ρ).subtype := by
      rintro _ ⟨h, rfl⟩
      refine ⟨resBeta ρ h z, hW' _ ⟨h, rfl⟩ z hzfix, ?_⟩
      rfl
    have hKW : kOf ρ ≤ W'.map (kOf ρ).subtype := by
      have h1 : commV P ≤ W'.map (kOf ρ).subtype := by
        rw [← hK]
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨x, hx, rfl⟩
        exact hmem x hx
      exact hkOf.le.trans h1
    refine (Subgroup.eq_top_iff' _).2 fun k => ?_
    obtain ⟨w', hw', hwk⟩ := hKW k.2
    have : w' = k := Subtype.ext hwk
    rw [← this]
    exact hw'
  refine ⟨hstr, hfix, hgenK, hsplit, hinfK, ?_⟩
  have hKinv : ∀ x ∈ X, ∀ u ∈ commV P, x u ∈ commV P := fun x hx u hu =>
    hPn'.commV_invariant hx hu
  have hW1 : commV P ⊔ Subgroup.zpowers c = ⊤ := by
    rw [eq_top_iff, ← hgen']
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [hvv, map_mul, hc x hx]
    exact (commV P ⊔ Subgroup.zpowers c).mul_mem
      (Subgroup.mem_sup_left (hKinv x hx _ hv')) (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hfixle : fixV X ≤ Subgroup.zpowers c := by
    intro w hw
    have hw' : w ∈ commV P ⊔ Subgroup.zpowers c := by rw [hW1]; exact Subgroup.mem_top w
    obtain ⟨a, ha, z, hz, haz⟩ := Subgroup.mem_sup.mp hw'
    have hzF : z ∈ fixV X := (Subgroup.zpowers_le.mpr hc) hz
    have haF : a ∈ fixV X := by
      have : a = w * z⁻¹ := by rw [← haz]; group
      rw [this]
      exact (fixV X).mul_mem hw ((fixV X).inv_mem hzF)
    have h1 : a ∈ commV P ⊓ fixV X := ⟨ha, haF⟩
    rw [hinf, Subgroup.mem_bot] at h1
    rw [← haz, h1, one_mul]
    exact hz
  have hcc : c ^ 2 = 1 := hW c
  calc Nat.card ↥(fixV X) ≤ Nat.card ↥(Subgroup.zpowers c) := Subgroup.card_le_of_le hfixle
    _ = orderOf c := Nat.card_zpowers c
    _ ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hcc)

end Abstract

section Concrete

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem class_data_of_lemma1435 (h35 : Lemma1435) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p)
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (h98 : HypF98 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H) :
    PStr14612 (resBeta (rhoH h)).range ((T.subgroupOf H).map (resBeta (rhoH h)))
        ((PQ.subgroupOf H).map (resBeta (rhoH h))) p ∧
      fixV ((PQ.subgroupOf H).map (resBeta (rhoH h))) = ⊥ ∧
      (∀ W' : Subgroup ↥(kOf (rhoH h)),
        (∀ g ∈ (resBeta (rhoH h)).range, ∀ z ∈ fixV ((T.subgroupOf H).map (resBeta (rhoH h))),
          g z ∈ W') → W' = ⊤) ∧
      (∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c) ∧
      kOf (rhoH h) ⊓ fixV (rhoH h).range = ⊥ ∧ Nat.card ↥(fixV (rhoH h).range) ≤ 2 ∧
      Nat.card ↥((T.subgroupOf H).map (resBeta (rhoH h))) = (pCoreOf 2 H).relIndex T := by
  classical
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hPQH : PQ ≤ H := hred.le
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hkerEq : (rhoH h).ker = (pCoreOf 2 H).subgroupOf H := ker_rhoH_eq h
  have hker : ∀ x : ↥H, rhoH h x = 1 ↔ (x : G) ∈ pCoreOf 2 H := rhoH_eq_one_iff h
  have hPQn : (PQ.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPQH).mpr hred.normal
  have hHeq : PQ.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPQH hTH, ← hred.eq, Subgroup.subgroupOf_self]
  have hkerP : (rhoH h).ker ≤ PQ.subgroupOf H := by
    rw [hkerEq]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hred.lt.le (Subgroup.mem_subgroupOf.mp hx))
  have hT2' : IsPGroup 2 (T.subgroupOf H) := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hTi : ¬ 2 ∣ (T.subgroupOf H).index := hTsyl.2.2
  have hk1 : ∀ x : ↥H, rhoH h x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 H ⟨_, (hker x).mp hx⟩
    exact ⟨j, Subtype.ext (by simpa using congrArg Subtype.val hj)⟩
  have hk2 : ∀ S' : Subgroup ↥H, S'.Normal → IsPGroup 2 S' → ∀ x ∈ S', rhoH h x = 1 := by
    intro S' hS'n hS'2 x hx
    have hle : S'.map H.subtype ≤ pCoreOf 2 H := by
      refine le_pCoreOf 2 (Subgroup.map_subtype_le S') ?_ (hS'2.map H.subtype)
      rw [map_subtype_subgroupOf']
      exact hS'n
    exact (hker x).mpr (hle ⟨x, hx, rfl⟩)
  have hpp : ∀ x ∈ PQ.subgroupOf H, ∃ k : ℕ, rhoH h (x ^ p ^ k) = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hred.pSec (x : G) (Subgroup.mem_subgroupOf.mp hx)
    exact ⟨k, (hker _).mpr (by simpa using hk)⟩
  have hmin : ∀ N : Subgroup ↥H, N.Normal → (rhoH h).ker ≤ N → N ≤ PQ.subgroupOf H →
      N = (rhoH h).ker ∨ N = PQ.subgroupOf H := by
    intro N hNn hkN hNP
    have h1 : pCoreOf 2 H ≤ N.map H.subtype := by
      intro x hx
      refine ⟨⟨x, pCoreOf_le 2 H hx⟩, hkN ?_, rfl⟩
      rw [hkerEq]
      exact Subgroup.mem_subgroupOf.mpr hx
    have h2 : N.map H.subtype ≤ PQ := by
      rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hNP hy)
    have h3 : H ≤ Subgroup.normalizer ((N.map H.subtype : Subgroup G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le N)).mp
        (by rw [map_subtype_subgroupOf']; exact hNn)
    have e : N = (N.map H.subtype).subgroupOf H := (map_subtype_subgroupOf' N).symm
    rcases hred.minimal _ h1 h2 h3 with h4 | h4
    · left
      rw [e, h4, hkerEq]
    · right
      rw [e, h4]
  have hlt : ¬ PQ.subgroupOf H ≤ (rhoH h).ker := by
    intro hle
    obtain ⟨x, hxPQ, hxQ⟩ := IsConcreteLE.exists_of_lt hred.lt
    have hxH : x ∈ H := hPQH hxPQ
    have hx : (⟨x, hxH⟩ : ↥H) ∈ (rhoH h).ker := hle (Subgroup.mem_subgroupOf.mpr hxPQ)
    rw [hkerEq] at hx
    exact hxQ (Subgroup.mem_subgroupOf.mp hx)
  have hq : qOf (rhoH h).range ≤ 2 := by
    rw [range_rhoH]
    exact h98.lemma_14_5_18_three.1
  have hsq : IsQuotientOfSQTKTC ↥(rhoH h).range := by
    have hSQ : SQTKGroup ↥H := S.sqtkGroup_of_isHTM hH
    exact ⟨↥H, inferInstance, inferInstance, fun p hp hp2 => hSQ.1 p hp hp2, hSQ.2,
      (rhoH h).rangeRestrict, (rhoH h).rangeRestrict_surjective⟩
  obtain ⟨w₀, hw₀, hgen⟩ := exists_gen_vector S h
  have hw₀' : ∀ t ∈ T.subgroupOf H, rhoH h t w₀ = w₀ :=
    fun t ht => hw₀ t (Subgroup.mem_subgroupOf.mp ht)
  obtain ⟨hstr, hfix, hgenK, hsplit, hinf, hfc⟩ := class_hom_data (W := UMod h) IntMod.sq_eq_one
    (rhoH h) (PQ.subgroupOf H) (T.subgroupOf H) hred.prime hred.odd hk1 hk2 hPQn hkerP hpp hHeq
    hT2' hTi hmin hlt (card_map_ne h35 S hred h) hq hsq hw₀' hgen
  refine ⟨hstr, hfix, hgenK, hsplit, hinf, hfc, ?_⟩
  have hkb : (resBeta (rhoH h)).ker = (rhoH h).ker := ker_resBeta (rhoH h) hsplit
  have h1 : Nat.card ↥((T.subgroupOf H).map (resBeta (rhoH h))) =
      (resBeta (rhoH h)).ker.relIndex (T.subgroupOf H) :=
    (Subgroup.relIndex_ker (T.subgroupOf H) (resBeta (rhoH h))).symm
  rw [hkb, hkerEq, Subgroup.relIndex_subgroupOf hTH] at h1
  exact h1

theorem shape_splitting (h35 : Lemma1435) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h98 : HypF98 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H) :
    (∀ w : UMod h98.toHypF91, ∃ a ∈ kOf (rhoH h98.toHypF91),
        ∃ c ∈ fixV (rhoH h98.toHypF91).range, w = a * c) ∧
      kOf (rhoH h98.toHypF91) ⊓ fixV (rhoH h98.toHypF91).range = ⊥ ∧
      Nat.card ↥(fixV (rhoH h98.toHypF91).range) ≤ 2 := by
  obtain ⟨-, -, -, hsplit, hinf, hfc, -⟩ := class_data_of_lemma1435 h35 S hred h98.toHypF91 h98
  exact ⟨hsplit, hinf, hfc⟩

end Concrete

@[expose] def ClassAutShapeStmt : Prop :=
  ∀ {V : Type} [CommGroup V] [Finite V] {X Tb P : Subgroup (MulAut V)} {p : ℕ},
    PStr14612 X Tb P p → fixV P = ⊥ →
      (∀ W : Subgroup V, (∀ g ∈ X, ∀ z ∈ fixV Tb, g z ∈ W) → W = ⊤) →
        p = 3 → Nat.card Tb = 4 → E9Z4Str X Tb P

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem e9z4Str_of_shape (hcls : ClassAutShapeStmt) (h35 : Lemma1435) (S : Setting146 G T M)
    {H PQ : Subgroup G} {p : ℕ} (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p)
    (h98 : HypF98 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H) :
    E9Z4Str (resBeta (rhoH h98.toHypF91)).range
      ((T.subgroupOf H).map (resBeta (rhoH h98.toHypF91)))
      ((PQ.subgroupOf H).map (resBeta (rhoH h98.toHypF91))) := by
  obtain ⟨hstr, hfix, hgenK, -, -, -, hT4⟩ :=
    class_data_of_lemma1435 h35 S hred h98.toHypF91 h98
  exact hcls hstr hfix hgenK hshape.1 (hT4.trans hshape.2)

end Main

section GroupLevel

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

omit [Finite G] in
theorem HLb_range_eq {V' : Type*} [Group V'] (β : ↥H →* MulAut V') : HLb β β.range = H := by
  ext g
  exact ⟨fun hg => HLb_le _ hg, fun hg => (mem_HLb_iff hg).2 ⟨⟨g, hg⟩, rfl⟩⟩

theorem relIndex_Z_uHi_eq
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Lb : Subgroup (MulAut ↥(kOf (rhoH h)))} (hLb : Lb ≤ (resBeta (rhoH h)).range) :
    (quasithinOmegaOneCenter T).relIndex
      (⁅conjClosure (VZ T M) H, HLb (resBeta (rhoH h)) Lb⁆ ⊔ quasithinOmegaOneCenter T) =
        Nat.card ↥(commV Lb) := by
  have hd := tildeOf_comm_HLb h hsplit hLb
  have hYN := uHi_le_normalizer h (HLb (resBeta (rhoH h)) Lb) (HLb_le Lb)
  have h1 := relIndex_secImg (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (B := quasithinOmegaOneCenter T) (T := quasithinOmegaOneCenter T)
    (H := ⁅conjClosure (VZ T M) H, HLb (resBeta (rhoH h)) Lb⁆ ⊔ quasithinOmegaOneCenter T)
    le_rfl le_sup_right hYN
  have h2 : secImg (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = ⊥ := tildeOf_eq_bot_of_le le_rfl
  rw [h2, Subgroup.relIndex_bot_left] at h1
  rw [← h1]
  change Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) _) = _
  rw [hd, Subgroup.card_map_of_injective (valK_injective h)]

theorem tildeOf_uK_sup_Z_eq
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c) :
    tildeOf (quasithinOmegaOneCenter T) (uK T M H ⊔ quasithinOmegaOneCenter T) =
      (commV (resBeta (rhoH h)).range).map (valK h) := by
  have := tildeOf_comm_HLb h hsplit (le_refl (resBeta (rhoH h)).range)
  rwa [HLb_range_eq] at this

theorem card_uK_sup_Z_of_str
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    (hZ : Nat.card ↥(quasithinOmegaOneCenter T) = 2)
    {Tb P : Subgroup (MulAut ↥(kOf (rhoH h)))} (hES : E9Z4Str (resBeta (rhoH h)).range Tb P) :
    Nat.card ↥(uK T M H ⊔ quasithinOmegaOneCenter T) = 2 ^ 5 := by
  have h1 := relIndex_Z_uHi_eq h hsplit (le_refl (resBeta (rhoH h)).range)
  rw [HLb_range_eq, hES.commV_X, Subgroup.card_top, hES.card_V] at h1
  have h2 := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T)
    (uK T M H ⊔ quasithinOmegaOneCenter T)
  rw [inf_eq_left.mpr le_sup_right, hZ] at h2
  have h3 : (quasithinOmegaOneCenter T).relIndex (uK T M H ⊔ quasithinOmegaOneCenter T) = 16 := h1
  rw [h3] at h2
  omega

theorem valK_resBeta_apply
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H) (y : ↥H)
    (w : ↥(kOf (rhoH h))) :
    valK h (resBeta (rhoH h) y w) =
      secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) (quasithinOmegaOneCenter T)
          (Subgroup.inclusion h.H_normalizes_V₁ y) * valK h w *
        (secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
          (quasithinOmegaOneCenter T) (Subgroup.inclusion h.H_normalizes_V₁ y))⁻¹ := by
  have h1 := valK_comm_gen h y w
  have h2 : valK h (resBeta (rhoH h) y w) =
      valK h (resBeta (rhoH h) y w * w⁻¹) * valK h w := by
    rw [← map_mul, inv_mul_cancel_right]
  rw [h2, h1]
  group

theorem irreducible_of_str
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    {Tb P : Subgroup (MulAut ↥(kOf (rhoH h)))} (hES : E9Z4Str (resBeta (rhoH h)).range Tb P) :
    ∀ W : Subgroup G, quasithinOmegaOneCenter T ≤ W →
      W ≤ uK T M H ⊔ quasithinOmegaOneCenter T → H ≤ Subgroup.normalizer (W : Set G) →
        W = quasithinOmegaOneCenter T ∨ W = uK T M H ⊔ quasithinOmegaOneCenter T := by
  intro W hZW hWU hHW
  have hUN : uK T M H ⊔ quasithinOmegaOneCenter T ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := uHi_le_normalizer h H le_rfl
  have hdict := tildeOf_uK_sup_Z_eq h hsplit
  rw [hES.commV_X, Subgroup.map_top] at hdict
  set W' : Subgroup ↥(kOf (rhoH h)) := (tildeOf (quasithinOmegaOneCenter T) W).comap (valK h)
    with hW'
  have hinv : ∀ x ∈ (resBeta (rhoH h)).range, ∀ w ∈ W', x w ∈ W' := by
    rintro _ ⟨y, rfl⟩ w hw
    have hw' : valK h w ∈ tildeOf (quasithinOmegaOneCenter T) W := hw
    show valK h (resBeta (rhoH h) y w) ∈ tildeOf (quasithinOmegaOneCenter T) W
    rw [valK_resBeta_apply]
    exact secMk_conj_mem_secImg (a := Subgroup.inclusion h.H_normalizes_V₁ y) (hHW y.2) hw'
  rcases hES.irreducible hinv with hbot | htop
  · left
    refine le_antisymm (fun u hu => ?_) hZW
    have huN : u ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := hUN (hWU hu)
    have hmem : secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) ⟨u, huN⟩ ∈ tildeOf (quasithinOmegaOneCenter T) W :=
      secMk_mem_secImg hu
    have hmem' := secImg_mono (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (B := quasithinOmegaOneCenter T) hWU hmem
    change _ ∈ tildeOf (quasithinOmegaOneCenter T) (uK T M H ⊔ quasithinOmegaOneCenter T) at hmem'
    rw [hdict] at hmem'
    obtain ⟨k, hk⟩ := hmem'
    have hkW : k ∈ W' := by
      show valK h k ∈ tildeOf (quasithinOmegaOneCenter T) W
      rw [hk]
      exact hmem
    rw [hbot, Subgroup.mem_bot] at hkW
    rw [hkW, map_one] at hk
    exact secMk_eq_one_iff.1 hk.symm
  · right
    refine le_antisymm hWU (fun u hu => ?_)
    have huN : u ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := hUN hu
    have hmem : secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) ⟨u, huN⟩ ∈
          tildeOf (quasithinOmegaOneCenter T) (uK T M H ⊔ quasithinOmegaOneCenter T) :=
      secMk_mem_secImg hu
    rw [hdict] at hmem
    obtain ⟨k, hk⟩ := hmem
    have hkW : k ∈ W' := by rw [htop]; exact Subgroup.mem_top k
    have hmem' : secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) ⟨u, huN⟩ ∈ tildeOf (quasithinOmegaOneCenter T) W := by
      rw [← hk]
      exact hkW
    exact (secMk_mem_secImg_iff (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (B := quasithinOmegaOneCenter T) hZW).1 hmem'

theorem Setting146.relIndex_uK_sup_Z_le_two (S : Setting146 G T M) (hH : IsHTM T M H) :
    (uK T M H ⊔ quasithinOmegaOneCenter T).relIndex (conjClosure (VZ T M) H) ≤ 2 := by
  set Z := quasithinOmegaOneCenter T with hZdef
  set Y := uK T M H ⊔ Z with hY
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hZV : Z ≤ VZ T M := le_conjClosure _ _
  have hVU : VZ T M ≤ conjClosure (VZ T M) H := le_conjClosure _ _
  have hKU : uK T M H ≤ conjClosure (VZ T M) H :=
    S145.commutator_le_of_le_normalizer (le_normalizer_conjClosure _ _)
  have hYU : Y ≤ conjClosure (VZ T M) H := sup_le hKU (hZV.trans hVU)
  have hUeq : VZ T M ⊔ Y = conjClosure (VZ T M) H := by
    refine le_antisymm (sup_le hVU hYU) ?_
    rw [conjClosure_eq_sup_uK_P19 T M H]
    exact sup_le_sup_left le_sup_left _
  have hVN : VZ T M ≤ Subgroup.normalizer (Y : Set G) := fun v hv =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      congrArg Subtype.val (hUab.1.is_comm.comm ⟨a, hYU ha⟩ ⟨v, hVU hv⟩))
  have hprod := QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hVN
  rw [hUeq] at hprod
  have hV4 : Nat.card ↥(VZ T M) = 4 := S.hyp.rank_two
  have hZ2 : Nat.card ↥Z = 2 := S.card_Z
  have hi : 2 ≤ Nat.card ↥(VZ T M ⊓ Y) := by
    rw [← hZ2]
    exact Subgroup.card_le_of_le (le_inf hZV le_sup_right)
  have h2 := Subgroup.relIndex_mul_card Y (conjClosure (VZ T M) H)
  rw [inf_eq_left.mpr hYU] at h2
  have hYpos : 0 < Nat.card ↥Y := Nat.card_pos
  rw [hV4, ← h2] at hprod
  have h3 : Y.relIndex (conjClosure (VZ T M) H) * Nat.card ↥(VZ T M ⊓ Y) = 4 := by
    apply Nat.eq_of_mul_eq_mul_left hYpos
    calc Nat.card ↥Y * (Y.relIndex (conjClosure (VZ T M) H) * Nat.card ↥(VZ T M ⊓ Y))
        = Y.relIndex (conjClosure (VZ T M) H) * Nat.card ↥Y * Nat.card ↥(VZ T M ⊓ Y) := by ring
      _ = 4 * Nat.card ↥Y := hprod
      _ = Nat.card ↥Y * 4 := by ring
  by_contra hr
  push Not at hr
  nlinarith

end GroupLevel

section Final

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem shape_card_uK_Z (hcls : ClassAutShapeStmt) (h35 : Lemma1435) (S : Setting146 G T M)
    {H PQ : Subgroup G} {p : ℕ} (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p) :
    Nat.card ↥(uK T M H ⊔ quasithinOmegaOneCenter T) = 2 ^ 5 := by
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hred.isHTM)
  obtain ⟨-, -, -, hsplit, -, -, -⟩ := class_data_of_lemma1435 h35 S hred h98.toHypF91 h98
  exact card_uK_sup_Z_of_str h98.toHypF91 hsplit S.card_Z
    (e9z4Str_of_shape hcls h35 S hred hshape h98)

theorem shape_irreducible (hcls : ClassAutShapeStmt) (h35 : Lemma1435) (S : Setting146 G T M)
    {H PQ : Subgroup G} {p : ℕ} (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p) :
    ∀ W : Subgroup G, quasithinOmegaOneCenter T ≤ W →
      W ≤ uK T M H ⊔ quasithinOmegaOneCenter T → H ≤ Subgroup.normalizer (W : Set G) →
        W = quasithinOmegaOneCenter T ∨ W = uK T M H ⊔ quasithinOmegaOneCenter T := by
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hred.isHTM)
  obtain ⟨-, -, -, hsplit, -, -, -⟩ := class_data_of_lemma1435 h35 S hred h98.toHypF91 h98
  exact irreducible_of_str h98.toHypF91 hsplit (e9z4Str_of_shape hcls h35 S hred hshape h98)

end Final

end CFSG.Quasithin

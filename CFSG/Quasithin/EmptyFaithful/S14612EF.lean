module

public import CFSG.Quasithin.EmptyFaithful.S14612EE
public import CFSG.Quasithin.EmptyFaithful.S14612DC
public import CFSG.Quasithin.EmptyFaithful.S143WFin

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
open CFSG.Quasithin.S1417
open scoped commutatorElement

section Final

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem ker_rhoH_eq (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H) :
    (rhoH h).ker = (pCoreOf 2 H).subgroupOf H := by
  ext x
  rw [MonoidHom.mem_ker, rhoH_eq_one_iff h, Subgroup.mem_subgroupOf]

theorem exists_gen_vector (S : Setting146 G T M)
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H) :
    ∃ w₀ : UMod h, (∀ t : ↥H, (t : G) ∈ T → rhoH h t w₀ = w₀) ∧
      Subgroup.closure {w | ∃ x : ↥H, w = rhoH h x w₀} = ⊤ := by
  classical
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  have hZlt : quasithinOmegaOneCenter T < VZ T M := by
    refine lt_of_le_of_ne hZV fun e => ?_
    have h1 := S.card_Z
    have h2 := S.hyp.rank_two
    rw [e] at h1
    omega
  obtain ⟨v, hvV, hvZ⟩ := IsConcreteLE.exists_of_lt hZlt
  have hVT : VZ T M ≤ T := h.V_le_T
  have hTN : T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := h.T_normalizes_V₁
  have hvT : v ∈ T := hVT hvV
  have hvN : v ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := hTN hvT
  have hUN := U_le_normalizer h
  have hvU : v ∈ conjClosure (VZ T M) H := le_conjClosure _ _ hvV
  have hmem : secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) ⟨v, hvN⟩ ∈ tildeOf (quasithinOmegaOneCenter T)
        (conjClosure (VZ T M) H) := secMk_mem_secImg (x := ⟨v, hvN⟩) hvU
  set w₀ : UMod h := IntMod.mk h.isElemAbelian_tilde
    ⟨secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) ⟨v, hvN⟩, hmem⟩ with hw₀
  have hV1 : ∀ z (hz : z ∈ VZ T M),
      secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) ⟨z, hTN (hVT hz)⟩ = 1 ∨
      secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) ⟨z, hTN (hVT hz)⟩ =
        secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
          (quasithinOmegaOneCenter T) ⟨v, hvN⟩ := by
    intro z hz
    by_cases hzZ : z ∈ quasithinOmegaOneCenter T
    · left
      exact secMk_eq_one_iff.2 hzZ
    · right
      have h1 : v * z⁻¹ ∈ quasithinOmegaOneCenter T :=
        S146T.mul_inv_mem_of_card hZV S.hyp.rank_two S.card_Z hvV hz hvZ hzZ
      have h2 : z⁻¹ * v ∈ quasithinOmegaOneCenter T := by
        have := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)).inv_mem
            (hTN (hVT hz))) (v * z⁻¹)).mp h1
        simpa [mul_assoc] using this
      exact secMk_eq_secMk_iff.2 h2
  refine ⟨w₀, ?_, ?_⟩
  · intro t ht
    apply IntMod.val_injective
    rw [rhoH_val]
    have hc := S.conj_mem_mul_Z ht hvV
    have htN : (t : G) ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := hTN ht
    have e1 : (Subgroup.inclusion h.H_normalizes_V₁ t) = ⟨(t : G), htN⟩ := Subtype.ext rfl
    rw [e1]
    have e2 : secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) (⟨t, htN⟩ * ⟨v, hvN⟩ * ⟨t, htN⟩⁻¹ * ⟨v, hvN⟩⁻¹) = 1 :=
      secMk_eq_one_iff.2 hc
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one] at e2
    exact e2
  · apply eq_top_iff.2
    intro m _
    set C : Subgroup (UMod h) := Subgroup.closure {w | ∃ x : ↥H, w = rhoH h x w₀} with hC
    have hCmem : ∀ x : ↥H, rhoH h x w₀ ∈ C := fun x => Subgroup.subset_closure ⟨x, rfl⟩
    have key : ∀ g (hg : g ∈ conjClosure (VZ T M) H),
        secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
          (quasithinOmegaOneCenter T) ⟨g, hUN hg⟩ ∈ C.map (valW h) := by
      intro g hg
      refine Subgroup.closure_induction
        (p := fun g (hg : g ∈ conjClosure (VZ T M) H) =>
          secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
            (quasithinOmegaOneCenter T) ⟨g, hUN hg⟩ ∈ C.map (valW h)) ?_ ?_ ?_ ?_ hg
      · rintro _ ⟨h', hh', z, hz, rfl⟩
        have hh'N : h' ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
          h.H_normalizes_V₁ hh'
        have hzN : z ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
          hTN (hVT hz)
        have e : (⟨h' * z * h'⁻¹, hUN (mem_conjClosure hh' hz)⟩ :
            ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))) =
            ⟨h', hh'N⟩ * ⟨z, hzN⟩ * ⟨h', hh'N⟩⁻¹ := Subtype.ext rfl
        rw [e, map_mul, map_mul, map_inv]
        rcases hV1 z hz with h1 | h1
        · rw [h1, mul_one, mul_inv_cancel]
          exact (C.map (valW h)).one_mem
        · rw [h1]
          refine ⟨rhoH h ⟨h', hh'⟩ w₀, hCmem ⟨h', hh'⟩, ?_⟩
          show (rhoH h ⟨h', hh'⟩ w₀).val = _
          rw [rhoH_val]
          rfl
      · have : (⟨1, hUN (Subgroup.one_mem _)⟩ :
            ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))) = 1 := rfl
        rw [this, map_one]
        exact (C.map (valW h)).one_mem
      · intro a b ha hb hmA hmB
        have e : (⟨a * b, hUN (Subgroup.mul_mem _ ha hb)⟩ :
            ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))) =
            ⟨a, hUN ha⟩ * ⟨b, hUN hb⟩ := Subtype.ext rfl
        rw [e, map_mul]
        exact (C.map (valW h)).mul_mem hmA hmB
      · intro a ha hmA
        have e : (⟨a⁻¹, hUN (Subgroup.inv_mem _ ha)⟩ :
            ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))) = ⟨a, hUN ha⟩⁻¹ :=
          Subtype.ext rfl
        rw [e, map_inv]
        exact (C.map (valW h)).inv_mem hmA
    obtain ⟨u, hu, hum⟩ := mem_secImg.1 m.val_mem
    have hk := key (u : G) hu
    have hue : (⟨(u : G), hUN hu⟩ : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))) = u :=
      Subtype.ext rfl
    rw [hue, hum] at hk
    obtain ⟨c, hc, hcm⟩ := hk
    have : c = m := valW_injective h hcm
    rw [← this]
    exact hc

theorem card_map_ne (h35 : Lemma1435) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H) :
    Nat.card ↥((PQ.subgroupOf H).map (rhoH h)) ≠ p := by
  intro hc
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hkerEq : (rhoH h).ker = (pCoreOf 2 H).subgroupOf H := ker_rhoH_eq h
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsyl
  have hPQH : PQ ≤ H := hred.le
  have hPQn : (PQ.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPQH).mpr hred.normal
  have hHeq : PQ.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPQH hTH, ← hred.eq, Subgroup.subgroupOf_self]
  have hkerP : (rhoH h).ker ≤ PQ.subgroupOf H := by
    rw [hkerEq]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hred.lt.le (Subgroup.mem_subgroupOf.mp hx))
  have hinf : PQ.subgroupOf H ⊓ T.subgroupOf H = (rhoH h).ker := by
    apply le_antisymm
    · rintro x ⟨hxP, hxT⟩
      obtain ⟨k, hk⟩ := hred.pSec (x : G) (Subgroup.mem_subgroupOf.mp hxP)
      obtain ⟨j, hj⟩ := hT2 ⟨(x : G), Subgroup.mem_subgroupOf.mp hxT⟩
      have hj' : (x : G) ^ 2 ^ j = 1 := congrArg Subtype.val hj
      have e1 : (rhoH h x) ^ p ^ k = 1 := by
        rw [← map_pow]
        exact (rhoH_eq_one_iff h _).mpr (by simpa using hk)
      have e2 : (rhoH h x) ^ 2 ^ j = 1 := by
        rw [← map_pow]
        have : x ^ 2 ^ j = 1 := Subtype.ext (by simpa using hj')
        rw [this, map_one]
      have hcop : Nat.Coprime (2 ^ j) (p ^ k) :=
        ((Nat.coprime_primes Nat.prime_two hred.prime).mpr (Ne.symm hred.odd)).pow j k
      have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one e2) (orderOf_dvd_of_pow_eq_one e1)
      rw [Nat.Coprime.gcd_eq_one hcop] at h3
      exact MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3))
    · intro x hx
      refine ⟨hkerP hx, ?_⟩
      rw [hkerEq] at hx
      exact Subgroup.mem_subgroupOf.mpr (hQT (Subgroup.mem_subgroupOf.mp hx))
  have hTn : T.subgroupOf H ≤ Subgroup.normalizer ((PQ.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    have : (PQ.subgroupOf H).Normal := hPQn
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hprod := QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hTn
  rw [sup_comm (T.subgroupOf H) _, hHeq, inf_comm, hinf, Subgroup.card_top] at hprod
  have h1 : Nat.card ↥(T.subgroupOf H) * (T.subgroupOf H).index = Nat.card ↥H :=
    Subgroup.card_mul_index _
  have h2 := Subgroup.relIndex_mul_card ((rhoH h).ker) (PQ.subgroupOf H)
  rw [inf_eq_left.mpr hkerP, Subgroup.relIndex_ker (PQ.subgroupOf H) (rhoH h)] at h2
  have hTpos : 0 < Nat.card ↥(T.subgroupOf H) := Nat.card_pos
  have hkpos : 0 < Nat.card ↥(rhoH h).ker := Nat.card_pos
  have h4 : (T.subgroupOf H).index * Nat.card ↥(rhoH h).ker = Nat.card ↥(PQ.subgroupOf H) := by
    apply Nat.eq_of_mul_eq_mul_left hTpos
    calc Nat.card ↥(T.subgroupOf H) * ((T.subgroupOf H).index * Nat.card ↥(rhoH h).ker)
        = (Nat.card ↥(T.subgroupOf H) * (T.subgroupOf H).index) * Nat.card ↥(rhoH h).ker := by
          rw [mul_assoc]
      _ = Nat.card ↥(T.subgroupOf H) * Nat.card ↥(PQ.subgroupOf H) := by rw [h1, hprod]
  have h5 : (T.subgroupOf H).index = Nat.card ↥((PQ.subgroupOf H).map (rhoH h)) :=
    Nat.eq_of_mul_eq_mul_right hkpos (h4.trans h2.symm)
  have hrel : T.relIndex H = p := by
    rw [Subgroup.relIndex, h5, hc]
  have hp35 : p = 3 ∨ p = 5 := S.p_eq_three_or_five_of_isRedCE hred
  have hidx : T.relIndex H = 3 ∨ T.relIndex H = 5 := by rw [hrel]; exact hp35
  exact hH.2 (h35 G T M S.hyp S.notSix H hH.1 hidx)

theorem split_hom {Hh : Type} [Group Hh] {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (ρ : Hh →* MulAut W) (P0 T0 : Subgroup Hh) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hPn : P0.Normal) (hpp : ∀ x ∈ P0, ∃ k : ℕ, ρ (x ^ q ^ k) = 1)
    (hHeq : P0 ⊔ T0 = ⊤) {w₀ : W} (hw₀ : ∀ t ∈ T0, ρ t w₀ = w₀)
    (hgen : Subgroup.closure {w | ∃ h : Hh, w = ρ h w₀} = ⊤) :
    (∀ w : W, ∃ a ∈ kOf ρ, ∃ c ∈ fixV ρ.range, w = a * c) ∧ kOf ρ ⊓ fixV ρ.range = ⊥ := by
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
    have : Fact q.Prime := ⟨hq⟩
    have hpg : IsPGroup q ↥P := by
      rintro ⟨x, a, ha, rfl⟩
      obtain ⟨k, hk⟩ := hpp a ha
      exact ⟨k, Subtype.ext (by simpa [map_pow] using hk)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).mp hpg
    rw [hn]
    exact Odd.pow (hq.eq_two_or_odd'.resolve_left hq2)
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
  refine ⟨fun w => ?_, by rw [hkOf]; exact hinf⟩
  have hw : w ∈ commV P ⊔ fixV X := by rw [hsup]; exact Subgroup.mem_top w
  obtain ⟨a, ha, c', hc', hac⟩ := Subgroup.mem_sup.mp hw
  exact ⟨a, hkOf ▸ ha, c', hc', hac.symm⟩

private theorem sqtkGroup_of_isHTM_aux (S : Setting146 G T M) (hH : IsHTM T M H) : SQTKGroup ↥H :=
  ⟨stronglyQuasithin_of_pCoreOf_ne_bot S.hyp.qtke hH.1.2,
    kGroup_of_pCoreOf_ne_bot S.hyp.qtke S.hyp.simple S.hyp.nonabelian hH.1.2⟩

private theorem isQuotientOfSQTK_range_aux {Γ : Type} [Group Γ] (φ : ↥H →* Γ)
    (hH : SQTKGroup ↥H) : IsQuotientOfSQTKTC ↥φ.range :=
  ⟨↥H, inferInstance, inferInstance, fun p hp hp2 => hH.1 p hp hp2, hH.2,
    φ.rangeRestrict, φ.rangeRestrict_surjective⟩

theorem stage14612Class_of_lemma1435 (h35 : Lemma1435) : Stage14612Class := by
  intro G _ _ T M S H PQ p hred
  classical
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h := h98.toHypF91
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
  have hsq : IsQuotientOfSQTKTC ↥(rhoH h).range :=
    isQuotientOfSQTK_range_aux (rhoH h) (sqtkGroup_of_isHTM_aux S hH)
  obtain ⟨w₀, hw₀, hgen⟩ := exists_gen_vector S h
  have hw₀' : ∀ t ∈ T.subgroupOf H, rhoH h t w₀ = w₀ :=
    fun t ht => hw₀ t (Subgroup.mem_subgroupOf.mp ht)
  rcases class_hom (W := UMod h) IntMod.sq_eq_one (rhoH h) (PQ.subgroupOf H) (T.subgroupOf H)
    hred.prime hred.odd hk1 hk2 hPQn hkerP hpp hHeq hT2' hTi hmin hlt (card_map_ne h35 S hred h) hq hsq
    hw₀' hgen with ⟨hp3, hc4⟩ | ⟨L₁, L₂, hB⟩
  · right
    refine ⟨hp3, ?_⟩
    have h1 : Nat.card ↥((T.subgroupOf H).map (rhoH h)) = (rhoH h).ker.relIndex (T.subgroupOf H) :=
      (Subgroup.relIndex_ker (T.subgroupOf H) (rhoH h)).symm
    rw [hkerEq, Subgroup.relIndex_subgroupOf hTH] at h1
    exact h1.symm.trans hc4
  · left
    obtain ⟨hsplit, -⟩ := split_hom IntMod.sq_eq_one (rhoH h) (PQ.subgroupOf H) (T.subgroupOf H)
      hred.prime hred.odd hPQn hpp hHeq hw₀' hgen
    have hkb : (resBeta (rhoH h)).ker = (rhoH h).ker := ker_resBeta (rhoH h) hsplit
    have hker' : (resBeta (rhoH h)).ker.map H.subtype = pCoreOf 2 H := by
      rw [hkb, hkerEq]
      exact Subgroup.map_subgroupOf_eq_of_le (pCoreOf_le 2 H)
    exact isDecP_of_blocks h hred hsplit hker' hB

end Final

end CFSG.Quasithin

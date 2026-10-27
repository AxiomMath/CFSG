module

public import CFSG.Quasithin.EmptyFaithful.S145Facts
public import CFSG.Quasithin.Background.D2Misc
public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.EmptyFaithful.S146G2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace C1Pack

theorem eq_one_of_commute_of_hO2 {Y : Type*} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal]
    (hquot : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ N)
    (hO2 : ∀ S : Subgroup Y, S.Normal → IsPGroup 2 S → S = ⊥)
    {a : Y} (ha : ∃ m : ℕ, a ^ 2 ^ m = 1) (hc : ∀ n ∈ N, a * n = n * a) : a = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : IsPGroup 2 (Y ⧸ N) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨k, hk⟩ := hquot y
      exact ⟨k, by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).mpr hk⟩
  obtain ⟨n, hn⟩ := hq.exists_card_eq
  have hNidx : N.index = 2 ^ n := by rw [Subgroup.index_eq_card]; exact hn
  have hzp : IsPGroup 2 (Subgroup.zpowers a) := by
    obtain ⟨m, hm⟩ := ha
    have hd : orderOf a ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  have hsup : N ⊔ (P : Subgroup Y) = ⊤ := by
    have h1 : (N ⊔ (P : Subgroup Y)).index ∣ 2 ^ n :=
      hNidx ▸ Subgroup.index_dvd_of_le le_sup_left
    have h2 : (N ⊔ (P : Subgroup Y)).index ∣ (P : Subgroup Y).index :=
      Subgroup.index_dvd_of_le le_sup_right
    have h3 : ¬ 2 ∣ (P : Subgroup Y).index := P.not_dvd_index
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have hi0 : i = 0 := by
      by_contra hne
      exact h3 ((dvd_pow_self 2 hne).trans (hi ▸ h2))
    exact Subgroup.index_eq_one.mp (by rw [hi, hi0, pow_zero])
  have haP : a ∈ (P : Subgroup Y) := hP (Subgroup.mem_zpowers a)
  have hconj : ∀ y : Y, y * a * y⁻¹ ∈ (P : Subgroup Y) := by
    intro y
    have hy : y ∈ N ⊔ (P : Subgroup Y) := hsup ▸ Subgroup.mem_top y
    obtain ⟨n', hn', r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    have h1 : n' * (r * a * r⁻¹) * n'⁻¹ = r * a * r⁻¹ := by
      have hcc : ∀ m ∈ N, (r * a * r⁻¹) * m = m * (r * a * r⁻¹) := by
        intro m hm
        have hm' : r⁻¹ * m * r ∈ N := Subgroup.Normal.conj_mem' inferInstance m hm r
        have := hc _ hm'
        calc r * a * r⁻¹ * m = r * (a * (r⁻¹ * m * r)) * r⁻¹ := by group
          _ = r * ((r⁻¹ * m * r) * a) * r⁻¹ := by rw [this]
          _ = m * (r * a * r⁻¹) := by group
      rw [mul_assoc n', ← mul_assoc, (hcc n' hn').symm]
      group
    have e : n' * r * a * (n' * r)⁻¹ = n' * (r * a * r⁻¹) * n'⁻¹ := by group
    rw [e, h1]
    exact (P : Subgroup Y).mul_mem ((P : Subgroup Y).mul_mem hr haP) ((P : Subgroup Y).inv_mem hr)
  have hS : Subgroup.normalClosure ({a} : Set Y) ≤ (P : Subgroup Y) := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨b, hb, hbx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    rw [Set.mem_singleton_iff] at hb
    subst hb
    obtain ⟨y, hy⟩ := isConj_iff.mp hbx
    rw [← hy]
    exact hconj y
  have hSbot : Subgroup.normalClosure ({a} : Set Y) = ⊥ :=
    hO2 _ inferInstance ((P.2).to_le hS)
  have : a ∈ Subgroup.normalClosure ({a} : Set Y) := Subgroup.subset_normalClosure rfl
  rw [hSbot, Subgroup.mem_bot] at this
  exact this

theorem p_eq_three_or_five {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {X N : Subgroup (MulAut W)} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hNX : N ≤ X) (hNn : (N.subgroupOf X).Normal) (hNp : IsPGroup p N)
    (hquot : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ N)
    (hO2 : ∀ S : Subgroup (MulAut W), S ≤ X → (S.subgroupOf X).Normal → IsPGroup 2 S → S = ⊥)
    (hq : qOf X ≤ 2) : p = 3 ∨ p = 5 := by
  classical
  have hqh : qhatOf X ≤ 2 := (qhatOf_le_qOf X).trans hq
  obtain ⟨r, hr⟩ : ∃ r : ℚ, qhatOf X = (r : WithTop ℚ) := by
    have hne : qhatOf X ≠ ⊤ := ne_top_of_le_ne_top (by simp) hqh
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    exact ⟨r, hr.symm⟩
  have hr2 : r ≤ 2 := by
    have : ((r : ℚ) : WithTop ℚ) ≤ ((2 : ℚ) : WithTop ℚ) := by
      rw [← hr]; exact_mod_cast hqh
    exact_mod_cast this
  obtain ⟨A, hA⟩ := QhatStar_nonempty hr hr2
  have hAX : A ≤ X := QhatStar_le hA
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have : Fact p.Prime := ⟨hp⟩
  have hD : ⁅pCoreOf p X, A⁆ ≠ ⊥ := by
    intro hbot
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA2.2.1
    have hNle : N ≤ pCoreOf p X := le_pCoreOf p hNX hNn hNp
    have hcomm : ∀ n ∈ N, (a : MulAut W) * n = n * (a : MulAut W) := by
      intro n hn
      have h1 := Subgroup.commutator_le.mp hbot.le n (hNle hn) (a : MulAut W) a.2
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    have : (N.subgroupOf X).Normal := hNn
    have hquot' : ∀ y : ↥X, ∃ k : ℕ, y ^ 2 ^ k ∈ N.subgroupOf X := fun y => by
      obtain ⟨k, hk⟩ := hquot y.1 y.2
      exact ⟨k, Subgroup.mem_subgroupOf.mpr hk⟩
    have hO2' : ∀ S : Subgroup ↥X, S.Normal → IsPGroup 2 S → S = ⊥ := by
      intro S hSn hS2
      have h1 : (S.map X.subtype) ≤ X := Subgroup.map_subtype_le S
      have h2 : ((S.map X.subtype).subgroupOf X) = S :=
        Subgroup.comap_map_eq_self_of_injective X.subtype_injective S
      have h3 : IsPGroup 2 (S.map X.subtype) := hS2.map X.subtype
      have h4 := hO2 _ h1 (by rw [h2]; exact hSn) h3
      exact (Subgroup.map_eq_bot_iff_of_injective S X.subtype_injective).mp h4
    have ha' : ∃ m : ℕ, (⟨(a : MulAut W), hAX a.2⟩ : ↥X) ^ 2 ^ m = 1 := by
      refine ⟨1, Subtype.ext ?_⟩
      have := hA2.2.2.2 (a : MulAut W) a.2
      simpa using this
    have hc' : ∀ n ∈ N.subgroupOf X, (⟨(a : MulAut W), hAX a.2⟩ : ↥X) * n =
        n * (⟨(a : MulAut W), hAX a.2⟩ : ↥X) := fun n hn =>
      Subtype.ext (hcomm n (Subgroup.mem_subgroupOf.mp hn))
    have h1 := eq_one_of_commute_of_hO2 (N.subgroupOf X) hquot' hO2' ha' hc'
    have h2 : (a : MulAut W) = 1 := congrArg (fun z : ↥X => (z : MulAut W)) h1
    exact ha1 (Subtype.ext h2)
  exact (D2_13 hW hr hA hp2 rfl hD).1

section Rho

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

@[expose] noncomputable def toTilde (h : HypF91 T V L V₁ Vp H) : ↥H →* ↥(tildeOf V₁ H) :=
  ((secMk (Subgroup.normalizer (V₁ : Set G)) V₁).comp
      (Subgroup.inclusion h.H_normalizes_V₁)).codRestrict (tildeOf V₁ H)
    (fun x => secMk_mem_secImg x.2)

omit [Finite G] in
theorem toTilde_surjective (h : HypF91 T V L V₁ Vp H) : Function.Surjective (toTilde h) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := mem_secImg.mp hy
  exact ⟨⟨x, hx⟩, rfl⟩

omit [Finite G] in
theorem coe_toTilde (h : HypF91 T V L V₁ Vp H) (x : ↥H) :
    ((toTilde h x : ↥(tildeOf V₁ H)) : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) =
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ (Subgroup.inclusion h.H_normalizes_V₁ x) := rfl

@[expose] noncomputable def rhoH (h : HypF91 T V L V₁ Vp H) :
    ↥H →* MulAut (IntMod (tildeOf V₁ (conjClosure Vp H)) h.isElemAbelian_tilde) :=
  (convHom h.isElemAbelian_tilde (tildeOf V₁ H) (HypF91.tilde_le_normalizer (V₁ := V₁) (Vp := Vp) (H := H) le_rfl)).comp (toTilde h)

theorem range_rhoH (h : HypF91 T V L V₁ Vp H) :
    (rhoH h).range = autI h.isElemAbelian_tilde (tildeOf V₁ H) := by
  unfold rhoH
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ (toTilde_surjective h),
    Subgroup.map_top, range_convHom]

theorem rhoH_eq_one_iff (h : HypF91 T V L V₁ Vp H) (x : ↥H) :
    rhoH h x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  have hC := h.tilde_inf_centralizer_pCoreOf (B := H) le_rfl
  have hmem : ∀ y : ↥(tildeOf V₁ H), convHom h.isElemAbelian_tilde (tildeOf V₁ H)
      (HypF91.tilde_le_normalizer (V₁ := V₁) (Vp := Vp) (H := H) le_rfl) y = 1 ↔
        (y : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈
          Subgroup.centralizer (tildeOf V₁ (conjClosure Vp H) :
            Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) := fun y => by
    rw [convHom_apply, convI_eq_one_iff]
  show convHom h.isElemAbelian_tilde (tildeOf V₁ H) (HypF91.tilde_le_normalizer (V₁ := V₁) (Vp := Vp) (H := H) le_rfl) (toTilde h x) = 1 ↔ _
  rw [hmem, coe_toTilde]
  constructor
  · intro hx
    have hx' : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ (Subgroup.inclusion h.H_normalizes_V₁ x) ∈
        tildeOf V₁ H ⊓ Subgroup.centralizer (tildeOf V₁ (conjClosure Vp H) :
          Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) :=
      ⟨(toTilde h x).2, hx⟩
    rw [hC] at hx'
    obtain ⟨q, ⟨hqH, hqQ⟩, hqx⟩ := mem_secImg.mp hx'
    have h1 := secMk_eq_secMk_iff.mp hqx
    have h2 : ((q : G))⁻¹ * (x : G) ∈ pCoreOf 2 H := h.V₁_le_pCoreOf h1
    have e : (x : G) = (q : G) * ((q : G)⁻¹ * (x : G)) := by group
    rw [e]
    exact Subgroup.mul_mem _ hqQ h2
  · intro hx
    have hx' : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ (Subgroup.inclusion h.H_normalizes_V₁ x) ∈
        tildeOf V₁ (H ⊓ pCoreOf 2 H) :=
      secMk_mem_secImg (x := Subgroup.inclusion h.H_normalizes_V₁ x) ⟨x.2, hx⟩
    rw [← hC] at hx'
    exact hx'.2

end Rho

theorem p_eq_three_or_five_of_hom {W : Type*} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Hh : Type*} [Group Hh] (ρ : Hh →* MulAut W) (P : Subgroup Hh) [P.Normal] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hk1 : ∀ x : Hh, ρ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hk2 : ∀ S : Subgroup Hh, S.Normal → IsPGroup 2 S → ∀ x ∈ S, ρ x = 1)
    (hPp : ∀ x ∈ P, ∃ k : ℕ, ρ (x ^ p ^ k) = 1)
    (hHP : ∀ x : Hh, ∃ k : ℕ, x ^ 2 ^ k ∈ P)
    (hq : qOf ρ.range ≤ 2) : p = 3 ∨ p = 5 := by
  classical
  have hNX : P.map ρ ≤ ρ.range := Subgroup.map_le_range _ _
  have hρ'surj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have hNsub : (P.map ρ).subgroupOf ρ.range = P.map ρ.rangeRestrict := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, Subtype.ext hyx⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  refine p_eq_three_or_five hW hp hp2 hNX ?_ ?_ ?_ ?_ hq
  · rw [hNsub]
    exact Subgroup.Normal.map inferInstance _ hρ'surj
  · intro n
    obtain ⟨y, hy, hyn⟩ := n.2
    obtain ⟨k, hk⟩ := hPp y hy
    refine ⟨k, Subtype.ext ?_⟩
    have h2 : (n : MulAut W) ^ p ^ k = 1 := by
      rw [← hyn, ← map_pow]
      exact hk
    exact h2
  · rintro _ ⟨y, rfl⟩
    obtain ⟨k, hk⟩ := hHP y
    exact ⟨k, ⟨y ^ 2 ^ k, hk, map_pow _ _ _⟩⟩
  · intro S hSX hSn hS2
    have hS2' : IsPGroup 2 (S.subgroupOf ρ.range) :=
      hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm
    let St : Subgroup Hh := (S.subgroupOf ρ.range).comap ρ.rangeRestrict
    have hStn : St.Normal := hSn.comap _
    have hSt2 : IsPGroup 2 St := by
      intro s
      have hs : ρ.rangeRestrict (s : Hh) ∈ S.subgroupOf ρ.range := s.2
      obtain ⟨k, hk⟩ := hS2' ⟨ρ.rangeRestrict (s : Hh), hs⟩
      have h1 : ρ ((s : Hh) ^ 2 ^ k) = 1 := by
        have h1' := congrArg (fun z : ↥(S.subgroupOf ρ.range) => ((z : ↥ρ.range) : MulAut W)) hk
        simpa [map_pow] using h1'
      obtain ⟨j, hj⟩ := hk1 _ h1
      refine ⟨k + j, Subtype.ext ?_⟩
      have h4 : (s : Hh) ^ 2 ^ (k + j) = 1 := by rw [pow_add, pow_mul]; exact hj
      simpa using h4
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨y, rfl⟩ := hSX hx
    have hy : y ∈ St := by
      show ρ.rangeRestrict y ∈ S.subgroupOf ρ.range
      exact hx
    rw [Subgroup.mem_bot]
    exact hk2 St hStn hSt2 y hy

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem _root_.CFSG.Quasithin.Setting146.p_eq_three_or_five_of_isRedCE (S : Setting146 G T M)
    {H PQ : Subgroup G} {p : ℕ} (hred : IsRedCE T M H PQ p) : p = 3 ∨ p = 5 := by
  classical
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h91 := h98.toHypF91
  have hŨ := h91.isElemAbelian_tilde
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hTH : T ≤ H := hH.1.1
  have hPQH : PQ ≤ H := hred.le
  have hPQn : (PQ.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPQH).mpr hred.normal
  have hker : ∀ x : ↥H, rhoH h91 x = 1 ↔ (x : G) ∈ pCoreOf 2 H := rhoH_eq_one_iff h91
  refine p_eq_three_or_five_of_hom (W := IntMod _ hŨ) IntMod.sq_eq_one (rhoH h91) (PQ.subgroupOf H)
    hred.prime hred.odd ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 H ⟨_, (hker x).mp hx⟩
    exact ⟨j, Subtype.ext (by simpa using congrArg Subtype.val hj)⟩
  · intro S' hS'n hS'2 x hx
    have hle : S'.map H.subtype ≤ pCoreOf 2 H := by
      refine le_pCoreOf 2 (Subgroup.map_subtype_le S') ?_ (hS'2.map H.subtype)
      rw [map_subtype_subgroupOf']
      exact hS'n
    exact (hker x).mpr (hle ⟨x, hx, rfl⟩)
  · intro x hx
    obtain ⟨k, hk⟩ := hred.pSec (x : G) (Subgroup.mem_subgroupOf.mp hx)
    exact ⟨k, (hker _).mpr (by simpa using hk)⟩
  · intro x
    have hxPT : (x : G) ∈ PQ ⊔ T := by
      rw [← hred.eq]
      exact x.2
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup_two hT2 (hTH.trans hred.normal) hxPT
    exact ⟨k, Subgroup.mem_subgroupOf.mpr (by simpa using hk)⟩
  · rw [range_rhoH]
    exact h98.lemma_14_5_18_three.1

end Main

end C1Pack

end CFSG.Quasithin

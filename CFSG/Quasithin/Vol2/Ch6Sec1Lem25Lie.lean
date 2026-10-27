module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Case

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_mul_of_mem_sup_ch625 {K R : Subgroup G}
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ K ⊔ R) :
    ∃ k ∈ K, ∃ r ∈ R, x = k * r := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, R.one_mem, by rw [mul_one]⟩
    · exact ⟨1, K.one_mem, y, hy, by rw [one_mul]⟩
  | one => exact ⟨1, K.one_mem, 1, R.one_mem, by rw [mul_one]⟩
  | mul y z _ _ ihy ihz =>
    obtain ⟨k, hk, r, hr, rfl⟩ := ihy
    obtain ⟨k', hk', r', hr', rfl⟩ := ihz
    refine ⟨k * (r * k' * r⁻¹), K.mul_mem hk ((Subgroup.mem_normalizer_iff.mp (hRK hr) k').mp hk'),
      r * r', R.mul_mem hr hr', by group⟩
  | inv y _ ih =>
    obtain ⟨k, hk, r, hr, rfl⟩ := ih
    refine ⟨r⁻¹ * k⁻¹ * r⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp (hRK (R.inv_mem hr)) k⁻¹).mp
      (K.inv_mem hk), r⁻¹, R.inv_mem hr, by group⟩

omit [Finite G] in
theorem map_conj_map_conj_ch625 (X : Subgroup G) (a b : G) :
    (X.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      X.map (MulAut.conj (a * b)).toMonoidHom :=
  (map_conj_mul_ch625 X a b).symm

theorem le_normalizer_of_mem_cComp_ch625 {H L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ cComp H)
    (h₂ : L₂ ∈ cComp H) : L₂ ≤ Subgroup.normalizer (L₁ : Set G) := by
  obtain ⟨hLS, hn⟩ := cComp_normal_span_of_le h₁
  exact (le_cCompSpan h₂).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLS).mp hn)

namespace Dat625

variable {T M L V : Subgroup G} {n : ℕ} {l : G} {DL K : Subgroup G}
  (hI : In625) (d : Dat625 T M L V n l DL K)
include d

include hI in
theorem K_not_le_M : ¬ K ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hKM
  have hKMV : K ≤ ch6MV M V := fun k hk =>
    d.hyp.toHyp611Nat.normalizer_le d.hyp.toHyp611Nat.ZS_ne_bot inf_le_left
      ⟨hKM hk, d.K_le_H hk⟩
  have hKR : K ≤ Subgroup.normalizer (ch6R T L V l : Set G) :=
    hKMV.trans (d.hyp.MV_le_normalizer_R hI.h432 hI.h6111 hI.h6119 d.l_mem d.l_not).1
  obtain ⟨r, hr, hr1⟩ := d.exists_phi_R_ne_one hI
  apply hr1
  rw [phiK_eq_one_iff d.quasi]
  intro k hk
  have hRK := d.R_le_NK hI hr
  have h1 : r * k * r⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp hRK k).mp hk) (K.inv_mem hk)
  have h2 : r * k * r⁻¹ * k⁻¹ ∈ ch6R T L V l := by
    have e : r * k * r⁻¹ * k⁻¹ = r * (k * r⁻¹ * k⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hr ((Subgroup.mem_normalizer_iff.mp (hKR hk) _).mp
      (Subgroup.inv_mem _ hr))
  have hKRn : K ≤ Subgroup.normalizer ((K ⊓ ch6R T L V l : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hk, hKR hk⟩
  have hle : K ⊓ ch6R T L V l ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hKRn
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
  exact hle ⟨h1, h2⟩

include hI in
theorem exists_t0 : ∃ t₀ ∈ T, ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom = K ∨
    K.map (MulAut.conj t).toMonoidHom = K.map (MulAut.conj t₀).toMonoidHom := by
  have : IsSimpleGroup G := d.hyp.simple
  have hLoc : LocalSQTK G := (qtkeCore_of_cat d.hyp.nonabelian d.hyp.qtke).1
  set Hn := Subgroup.normalizer (ch6ZS T L V : Set G) with hHn
  have hTH : T ≤ Hn := d.hyp.toHyp611Nat.T_le_normalizer_ZS
  rcases Vol2Native.lemma_1_2_1_three hLoc hI.h37 hI.h38 d.hyp.pCoreOf_H_ne_bot
    (mem_cComp_normalizer_ZS d.comp) with hn | ⟨h2, -⟩
  · have hHK : Hn ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (d.K_le_H)).mp hn
    exact ⟨1, T.one_mem, fun t ht => Or.inl (map_conj_eq_of_mem_normalizer_ch6 (hHK (hTH ht)))⟩
  · by_cases hall : ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom = K
    · exact ⟨1, T.one_mem, fun t ht => Or.inl (hall t ht)⟩
    push Not at hall
    obtain ⟨t₀, ht₀, hne⟩ := hall
    refine ⟨t₀, ht₀, fun t ht => ?_⟩
    obtain ⟨a, b, hab, hX⟩ := Set.ncard_eq_two.mp h2
    have hmem : ∀ g ∈ Hn, K.map (MulAut.conj g).toMonoidHom ∈ ({a, b} : Set (Subgroup G)) :=
      fun g hg => hX ▸ ⟨g, hg, rfl⟩
    have hK : K ∈ ({a, b} : Set (Subgroup G)) := by
      have := hmem 1 Hn.one_mem
      rwa [show K.map (MulAut.conj (1 : G)).toMonoidHom = K by ext x; simp] at this
    have h0 := hmem t₀ (hTH ht₀)
    have ht' := hmem t (hTH ht)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK h0 ht'
    rcases hK with rfl | rfl <;> rcases h0 with h0 | h0 <;> rcases ht' with h1 | h1 <;>
      first
        | exact Or.inl h1
        | exact Or.inr (h1.trans h0.symm)
        | exact absurd h0 hne

include hI in
theorem mem_M_of_phi_eq_conj (kf1 : OutTwoNilpotentFact) (h23 : A23SQTKListFact) {k : G}
    (hk : k ∈ K) {s : KBar K}
    (hs : s ∈ Subgroup.normalizer ((SBar T L V K : Subgroup (KBar K)) : Set (KBar K)))
    (hks : piK K ⟨k, hk⟩ = s) : k ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set SK := ch6S T L V ⊓ K with hSK
  have hP := isSylowTwoOf_subgroupOf_top (d.isSylowTwoOf_SK hI.h432)
  obtain ⟨b, hbN, s', hs', hbs⟩ :=
    exists_mem_normalizer_map_eq_sylow (piK K) (piK_surjective K) hP hs
  obtain ⟨sk, hsk, rfl⟩ := hs'
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hsk
  set z : ↥K := (sk⁻¹ * b)⁻¹ * ⟨k, hk⟩ with hz
  have hzπ : piK K z = 1 := by
    rw [hz, map_mul, map_inv, map_mul, map_inv, hbs, hks]
    group
  have hOS : pCoreOf 2 K ≤ SK := by
    have h1 : pCoreOf 2 K ≤ pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) :=
      A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp d.comp)
    have hS := (stmt6_1_9 hI.h432 G T M L V n d.hyp.toHyp611Nat).1.2
    exact le_inf (h1.trans (F7.isSylowTwoOf_pCoreOf_le hS))
      (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
  have hzN : (z : G) ∈ Subgroup.normalizer ((SK : Subgroup G) : Set G) := by
    have hzc : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) z : KQ K) ∈ Subgroup.center (KQ K) := by
      have := (QuotientGroup.eq_one_iff _).mp hzπ
      exact this
    refine mem_normalizer_of_forall_conj_mem_of_le fun x hx => ?_
    have hxK : x ∈ K := hx.2
    have h1 := Subgroup.mem_center_iff.mp hzc (QuotientGroup.mk' _ ⟨x, hxK⟩)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_iff_div_mem] at h1
    have h2 : (z : G) * x * (z : G)⁻¹ * x⁻¹ ∈ pCoreOf 2 K := by
      rw [pCoreOf_two_eq_map_ch625]
      refine ⟨_, Subgroup.inv_mem _ h1, ?_⟩
      simp [div_eq_mul_inv, mul_assoc]
    have e : (z : G) * x * (z : G)⁻¹ = ((z : G) * x * (z : G)⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact SK.mul_mem (hOS h2) hx
  have hB : (k : G) ∈ K ⊓ Subgroup.normalizer ((SK : Subgroup G) : Set G) := by
    have hbN' := mem_normalizer_of_mem_normalizer_subgroupOf_ch625 inf_le_right hbN
    have hskN : (sk : G) ∈ Subgroup.normalizer ((SK : Subgroup G) : Set G) :=
      Subgroup.le_normalizer hsk
    have e : k = ((sk : G)⁻¹ * b) * z := by
      rw [hz]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    refine ⟨hk, ?_⟩
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hskN) hbN') hzN
  exact d.borel_le_M hI kf1 h23 hB

include hI in
theorem KT_facts {t₀ : G} (ht₀ : t₀ ∈ T) (ht₀K : ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom = K ∨
      K.map (MulAut.conj t).toMonoidHom = K.map (MulAut.conj t₀).toMonoidHom) :
    K.map (MulAut.conj t₀).toMonoidHom ∈ cComp (Subgroup.centralizer (ch6ZS T L V : Set G)) ∧
      K.map (MulAut.conj t₀).toMonoidHom ≤ Subgroup.normalizer (K : Set G) ∧
      K ≤ Subgroup.normalizer ((K.map (MulAut.conj t₀).toMonoidHom : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer ((K ⊔ K.map (MulAut.conj t₀).toMonoidHom : Subgroup G) : Set G) ∧
      (K.map (MulAut.conj t₀).toMonoidHom = K ∨
        (K.map (MulAut.conj t₀⁻¹).toMonoidHom = K.map (MulAut.conj t₀).toMonoidHom ∧
          ∀ k' ∈ K.map (MulAut.conj t₀).toMonoidHom, ∀ k ∈ K,
            k' * k * k'⁻¹ * k⁻¹ ∈ pCoreOf 2 K)) := by
  have : IsSimpleGroup G := d.hyp.simple
  have hLoc : LocalSQTK G := (qtkeCore_of_cat d.hyp.nonabelian d.hyp.qtke).1
  set I := Subgroup.centralizer (ch6ZS T L V : Set G) with hIdef
  set K' := K.map (MulAut.conj t₀).toMonoidHom with hK'
  have hTI : T ≤ Subgroup.normalizer (I : Set G) :=
    d.hyp.toHyp611Nat.T_le_normalizer_ZS.trans (F7.normalizer_le_normalizer_centralizer _)
  have hconj : ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom ∈ cComp I := by
    intro t ht
    have := quasithinIsCComponent_map (MulAut.conj t) d.comp
    rwa [map_conj_eq_of_mem_normalizer_ch6 (hTI ht)] at this
  have hK'c : K' ∈ cComp I := hconj t₀ ht₀
  refine ⟨hK'c, le_normalizer_of_mem_cComp_ch625 d.comp hK'c,
    le_normalizer_of_mem_cComp_ch625 hK'c d.comp, ?_, ?_⟩
  · intro t ht
    have hle : ∀ s ∈ T, (K ⊔ K').map (MulAut.conj s).toMonoidHom ≤ K ⊔ K' := by
      intro s hs
      rw [Subgroup.map_sup, hK', map_conj_map_conj_ch625]
      refine sup_le ?_ ?_
      · rcases ht₀K s hs with h1 | h1
        · rw [h1]; exact le_sup_left
        · rw [h1]; exact le_sup_right
      · rcases ht₀K (s * t₀) (T.mul_mem hs ht₀) with h1 | h1
        · rw [h1]; exact le_sup_left
        · rw [h1]; exact le_sup_right
    apply mem_normalizer_of_map_conj_eq_ch625
    refine le_antisymm (hle t ht) ?_
    intro x hx
    refine ⟨t⁻¹ * x * t⁻¹⁻¹, hle t⁻¹ (T.inv_mem ht) ⟨x, hx, rfl⟩, ?_⟩
    simp [mul_assoc]
  · by_cases heq : K' = K
    · exact Or.inl heq
    · right
      refine ⟨?_, fun k' hk' k hk => ?_⟩
      · rcases ht₀K t₀⁻¹ (T.inv_mem ht₀) with h1 | h1
        · exfalso
          apply heq
          have h2 : (K.map (MulAut.conj t₀⁻¹).toMonoidHom).map (MulAut.conj t₀).toMonoidHom =
              K.map (MulAut.conj t₀).toMonoidHom := by rw [h1]
          rw [map_conj_map_conj_ch625, mul_inv_cancel] at h2
          rw [hK', ← h2]
          ext x
          simp
        · exact h1
      · have hO : pCoreOf 2 I ≠ ⊥ := by
          intro h0
          apply d.hyp.toHyp611Nat.ZS_ne_bot
          rw [eq_bot_iff, ← h0]
          have hZel : IsElemAbelian 2 (ch6ZS T L V) :=
            B2F.isElemAbelian_mono inf_le_left d.hyp.toHyp611.isElemAbelian
          refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_
            (Subgroup.centralizer_le_normalizer _) (B2F.isPGroup_of_isElemAbelian hZel)
          intro z hz
          exact Subgroup.mem_centralizer_iff.mpr fun x hx => B2F.isElemAbelian_comm hZel hx hz
        have hc := (Vol2Native.lemma_1_2_1_two hLoc hI.h37 hO d.comp hK'c (Ne.symm heq)).1
        have h1 : ⁅k, k'⁆ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator hk hk'
        have h2 := (hc h1).1
        have e : k' * k * k'⁻¹ * k⁻¹ = ⁅k, k'⁆⁻¹ := by rw [commutatorElement_def]; group
        rw [e]
        exact Subgroup.inv_mem _ h2

theorem decomp_KT {K' : Subgroup G} (hK'K : K' ≤ Subgroup.normalizer (K : Set G))
    (hcase : K' = K ∨ (K' ≠ K ∧ ∀ k' ∈ K', ∀ k ∈ K, k' * k * k'⁻¹ * k⁻¹ ∈ pCoreOf 2 K))
    {h : G} (hh : h ∈ K ⊔ K') (hhN : h ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k : G, ∃ hk : k ∈ K, ∃ k' : G, h = k * k' ∧
      phiK K ⟨h, hhN⟩ = MulAut.conj (piK K ⟨k, hk⟩) ∧ (k' = 1 ∨ (K' ≠ K ∧ k' ∈ K')) := by
  rcases hcase with h0 | ⟨hne, htriv⟩
  · rw [h0, sup_idem] at hh
    refine ⟨h, hh, 1, (mul_one h).symm, ?_, Or.inl rfl⟩
    rw [← phiK_of_mem K ⟨h, hh⟩]
  · obtain ⟨k, hk, k', hk', rfl⟩ := exists_mul_of_mem_sup_ch625 hK'K hh
    refine ⟨k, hk, k', rfl, ?_, Or.inr ⟨hne, hk'⟩⟩
    have hk'N : k' ∈ Subgroup.normalizer (K : Set G) := hK'K hk'
    have h1 : phiK K ⟨k', hk'N⟩ = 1 := (phiK_eq_one_iff d.quasi _).mpr (htriv k' hk')
    have e : (⟨k * k', hhN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨k, Subgroup.le_normalizer hk⟩ * ⟨k', hk'N⟩ := Subtype.ext rfl
    rw [e, map_mul, h1, mul_one, phiK_of_mem K ⟨k, hk⟩]

theorem eq_of_conj_eq {a b : KBar K} (h : MulAut.conj a = MulAut.conj b) : a = b := by
  have h1 : MulAut.conj (a * b⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 := mem_center_of_conj_eq_one h1
  rw [d.center_KBar, Subgroup.mem_bot] at h2
  exact mul_inv_eq_one.mp h2

include hI in
theorem mem_M_of_mem_KT (kf1 : OutTwoNilpotentFact) (h23 : A23SQTKListFact) {t₀ : G}
    (ht₀ : t₀ ∈ T) (ht₀K : ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom = K ∨
      K.map (MulAut.conj t).toMonoidHom = K.map (MulAut.conj t₀).toMonoidHom) {x : G}
    (hx : x ∈ K ⊔ K.map (MulAut.conj t₀).toMonoidHom)
    (h1 : ∀ hxN : x ∈ Subgroup.normalizer (K : Set G), ∃ s ∈ Subgroup.normalizer
      ((SBar T L V K : Subgroup (KBar K)) : Set (KBar K)), phiK K ⟨x, hxN⟩ = MulAut.conj s)
    (h2 : ∀ hxN : t₀⁻¹ * x * t₀ ∈ Subgroup.normalizer (K : Set G), ∃ s ∈ Subgroup.normalizer
      ((SBar T L V K : Subgroup (KBar K)) : Set (KBar K)),
        phiK K ⟨t₀⁻¹ * x * t₀, hxN⟩ = MulAut.conj s) : x ∈ M := by
  obtain ⟨-, hK'N, -, hTKT, hcase⟩ := d.KT_facts hI ht₀ ht₀K
  set K' := K.map (MulAut.conj t₀).toMonoidHom with hK'
  have hKTN : K ⊔ K' ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hK'N
  have hcase' : K' = K ∨ (K' ≠ K ∧ ∀ k' ∈ K', ∀ k ∈ K, k' * k * k'⁻¹ * k⁻¹ ∈ pCoreOf 2 K) := by
    rcases hcase with h0 | ⟨-, htriv⟩
    · exact Or.inl h0
    · by_cases h0 : K' = K
      · exact Or.inl h0
      · exact Or.inr ⟨h0, htriv⟩
  have hxN := hKTN hx
  obtain ⟨k, hk, k', rfl, hφ, hk'⟩ := d.decomp_KT hK'N hcase' hx hxN
  obtain ⟨s, hs, hφs⟩ := h1 hxN
  have hkM : k ∈ M := d.mem_M_of_phi_eq_conj hI kf1 h23 hk hs
    (d.eq_of_conj_eq (hφ.symm.trans hφs))
  rcases hk' with rfl | ⟨hne, hk'K'⟩
  · simpa using hkM
  · have htM : t₀ ∈ M := d.hyp.T_le ht₀
    obtain ⟨k₁, hk₁, rfl⟩ := hk'K'
    obtain ⟨-, -, -, -, hcase2⟩ := d.KT_facts hI ht₀ ht₀K
    have hinvK : K.map (MulAut.conj t₀⁻¹).toMonoidHom = K' := by
      rcases hcase2 with h0 | ⟨h0, -⟩
      · exact absurd h0 hne
      · exact h0
    have hkt : t₀⁻¹ * k * t₀ ∈ K' := by
      rw [← hinvK]
      exact ⟨k, hk, by simp⟩
    have hktN : t₀⁻¹ * k * t₀ ∈ Subgroup.normalizer (K : Set G) := hK'N hkt
    have hktriv : phiK K ⟨t₀⁻¹ * k * t₀, hktN⟩ = 1 := by
      rcases hcase' with h0 | ⟨-, htriv⟩
      · exact absurd h0 hne
      · exact (phiK_eq_one_iff d.quasi _).mpr (htriv _ hkt)
    have hyN : t₀⁻¹ * (k * (MulAut.conj t₀).toMonoidHom k₁) * t₀ ∈
        Subgroup.normalizer (K : Set G) := by
      have e : t₀⁻¹ * (k * (MulAut.conj t₀).toMonoidHom k₁) * t₀ = (t₀⁻¹ * k * t₀) * k₁ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact Subgroup.mul_mem _ hktN (Subgroup.le_normalizer hk₁)
    obtain ⟨s', hs', hφs'⟩ := h2 hyN
    have e : (⟨t₀⁻¹ * (k * (MulAut.conj t₀).toMonoidHom k₁) * t₀, hyN⟩ :
        ↥(Subgroup.normalizer (K : Set G))) =
        ⟨t₀⁻¹ * k * t₀, hktN⟩ * ⟨k₁, Subgroup.le_normalizer hk₁⟩ := by
      apply Subtype.ext
      show _ = (t₀⁻¹ * k * t₀) * k₁
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e, map_mul, hktriv, one_mul, phiK_of_mem K ⟨k₁, hk₁⟩] at hφs'
    have hk₁M : k₁ ∈ M := d.mem_M_of_phi_eq_conj hI kf1 h23 hk₁ hs' (d.eq_of_conj_eq hφs')
    refine M.mul_mem hkM ?_
    show t₀ * k₁ * t₀⁻¹ ∈ M
    exact M.mul_mem (M.mul_mem htM hk₁M) (M.inv_mem htM)

end Dat625

end CFSG.Quasithin.H13

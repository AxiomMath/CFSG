module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenConf

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup CFSG.ASVolI.ChIJK
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem s716D_mem_normalizer_of_forall {W : Subgroup G} {g : G}
    (h1 : ∀ t ∈ W, g * t * g⁻¹ ∈ W) (h2 : ∀ t ∈ W, g⁻¹ * t * g ∈ W) :
    g ∈ Subgroup.normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨h1 t, fun ht => ?_⟩
  have h3 := h2 _ ht
  have e : g⁻¹ * (g * t * g⁻¹) * g = t := by group
  rwa [e] at h3

theorem s716D_le_normalizer_of_le_abelian {I A B : Subgroup G} (hI : IsMulCommutative ↥I)
    (hA : A ≤ I) (hB : B ≤ I) : A ≤ Subgroup.normalizer (B : Set G) := by
  intro x hx
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  haveI := hI
  exact setLike_mul_comm (hB hy) (hA hx)

theorem s716D_card_sup_le {A B : Subgroup G} (h : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card ↥A * Nat.card ↥B := by
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right A B h
  have h1 : Nat.card ↑((A ⊔ B : Subgroup G) : Set G) ≤
      Nat.card ↑(A : Set G) * Nat.card ↑(B : Set G) := by
    rw [hmul]
    exact Set.natCard_mul_le
  exact h1


theorem nIn_eq_inf_iSub (h : Hyp716 V H E) {Q : Type} [Group Q] {φ : ↥(kSub V H E) →* Q}
    (hφ : IsBarMap (kSub V H E) (iSub V H E) φ)
    (hVZ : barSub (kSub V H E) φ V ⊓ Subgroup.center Q = ⊥) {a : ↥(kSub V H E)}
    (hker : ∀ l : ↥(kSub V H E), (l : G) ∈ V ⊔ conjSubgroup V (a : G) →
      (((QuotientGroup.mk' (Subgroup.center Q)).comp φ) l = 1 ↔
        (l : G) ∈ pairY V (conjSubgroup V (a : G)))) :
    NIn V (conjSubgroup V (a : G)) = V ⊓ iSub V H E ∧
      NIn (conjSubgroup V (a : G)) V = conjSubgroup V (a : G) ⊓ iSub V H E := by
  have hAΩ : conjSubgroup V (a : G) ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet_of_mem_kSub h a.2
  have hVK : V ≤ kSub V H E := le_kSub h.mem
  have hAK : conjSubgroup V (a : G) ≤ kSub V H E := le_kSub hAΩ
  have hIV : iSub V H E ≤ Subgroup.normalizer (V : Set G) :=
    iSub_le_normalizer_of_mem_omegaSet h h.mem
  have hIA : iSub V H E ≤ Subgroup.normalizer (conjSubgroup V (a : G) : Set G) :=
    iSub_le_normalizer_of_mem_omegaSet h hAΩ
  have hYL : pairY V (conjSubgroup V (a : G)) ≤ V ⊔ conjSubgroup V (a : G) :=
    sup_le_sup inf_le_left inf_le_left
  have hcen : ∀ l : ↥(kSub V H E), (l : G) ∈ pairY V (conjSubgroup V (a : G)) →
      φ l ∈ Subgroup.center Q := by
    intro l hl
    have h1 := (hker l (hYL hl)).mpr hl
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center Q) _).mp h1
  constructor
  · apply le_antisymm
    · intro n hn
      have hnV : n ∈ V := (inf_le_left : NIn V (conjSubgroup V (a : G)) ≤ V) hn
      have hnY : n ∈ pairY V (conjSubgroup V (a : G)) := Subgroup.mem_sup_left hn
      have h1 : φ ⟨n, hVK hnV⟩ ∈ Subgroup.center Q := hcen ⟨n, hVK hnV⟩ hnY
      have h2 : φ ⟨n, hVK hnV⟩ ∈ barSub (kSub V H E) φ V := mem_barSub.mpr ⟨_, hnV, rfl⟩
      have h3 : φ ⟨n, hVK hnV⟩ ∈ barSub (kSub V H E) φ V ⊓ Subgroup.center Q :=
        Subgroup.mem_inf.mpr ⟨h2, h1⟩
      rw [hVZ, Subgroup.mem_bot] at h3
      exact Subgroup.mem_inf.mpr ⟨hnV, (hφ.ker_iff _).mp h3⟩
    · exact inf_le_inf_left V hIA
  · apply le_antisymm
    · intro n hn
      have hnA : n ∈ conjSubgroup V (a : G) :=
        (inf_le_left : NIn (conjSubgroup V (a : G)) V ≤ conjSubgroup V (a : G)) hn
      have hnY : n ∈ pairY V (conjSubgroup V (a : G)) := Subgroup.mem_sup_right hn
      have h1 : φ ⟨n, hAK hnA⟩ ∈ Subgroup.center Q := hcen ⟨n, hAK hnA⟩ hnY
      have h2 : φ ⟨n, hAK hnA⟩ ∈ barSub (kSub V H E) φ (conjSubgroup V (a : G)) :=
        mem_barSub.mpr ⟨_, hnA, rfl⟩
      rw [barSub_conjSubgroup] at h2
      have h2' : φ a * φ ⟨n, hAK hnA⟩ * (φ a)⁻¹ ∈ barSub (kSub V H E) φ V :=
        Quasithin.mem_conjSubgroup_iff.mp h2
      have hc : φ a * φ ⟨n, hAK hnA⟩ * (φ a)⁻¹ = φ ⟨n, hAK hnA⟩ := by
        rw [Subgroup.mem_center_iff.mp h1 (φ a), mul_inv_cancel_right]
      rw [hc] at h2'
      have h3 : φ ⟨n, hAK hnA⟩ ∈ barSub (kSub V H E) φ V ⊓ Subgroup.center Q :=
        Subgroup.mem_inf.mpr ⟨h2', h1⟩
      rw [hVZ, Subgroup.mem_bot] at h3
      exact Subgroup.mem_inf.mpr ⟨hnA, (hφ.ker_iff _).mp h3⟩
    · exact inf_le_inf_left _ hIV

theorem pairY_le_centralizer (h : Hyp716 V H E) {a : G} (ha : a ∈ kSub V H E)
    (hP₂ : PairHyp (conjSubgroup V a) V)
    (hN : NIn V (conjSubgroup V a) = V ⊓ iSub V H E) {x : G}
    (hxA : ∀ w ∈ conjSubgroup V a, ⁅x, w⁆ ∈ iSub V H E)
    (hxI : ∀ w ∈ V ⊓ iSub V H E, ⁅w, x⁆ = 1) :
    pairY V (conjSubgroup V a) ≤ Subgroup.centralizer ({x} : Set G) := by
  have hAΩ := conjSubgroup_mem_omegaSet_of_mem_kSub h ha
  have hAK : conjSubgroup V a ≤ kSub V H E := le_kSub hAΩ
  have hIab : IsMulCommutative ↥(iSub V H E) := (isElemAbelian_iSub h).1
  have hAW : conjSubgroup V a ≤
      Subgroup.normalizer ((iSub V H E ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) :
        Set G) := fun w hw =>
    mem_normalizer_inf_centralizer hIab (kSub_le_normalizer_iSub h (hAK hw)) (hxA w hw)
  have hVW : NIn V (conjSubgroup V a) ≤ iSub V H E ⊓ Subgroup.centralizer ({x} : Set G) := by
    rw [hN]
    intro w hw
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hw).2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commutatorElement_eq_one_iff_commute.mp (hxI w hw)
  have hNA := pair_nIn_le hP₂ hVW hAW
  intro y hy
  have hW : NIn V (conjSubgroup V a) ⊔ NIn (conjSubgroup V a) V ≤
      iSub V H E ⊓ Subgroup.centralizer ({x} : Set G) := sup_le hVW hNA
  exact (Subgroup.mem_inf.mp (hW hy)).2

theorem exists_not_central (h : Hyp716 V H E) {Q : Type} [Group Q]
    {φ : ↥(kSub V H E) →* Q} (hφ : IsBarMap (kSub V H E) (iSub V H E) φ) {X : Subgroup G}
    (hXK : X ≤ kSub V H E) (hX1 : X ≠ ⊥) (hXodd : Odd (Nat.card ↥X))
    (hcomm : ∀ w ∈ V ⊓ iSub V H E, ∀ x ∈ X, ⁅w, x⁆ = 1) :
    ∃ x : ↥(kSub V H E), (x : G) ∈ X ∧ φ x ∉ Subgroup.center Q := by
  by_contra hcon
  push Not at hcon
  have hIab := (isElemAbelian_iSub h).1
  have hCx : ∀ x ∈ X, iSub V H E ≤ Subgroup.centralizer ({x} : Set G) := by
    intro x hx
    have hxK : x ∈ kSub V H E := hXK hx
    have hW : kSub V H E ≤ Subgroup.normalizer
        ((iSub V H E ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
      intro k hk
      refine mem_normalizer_inf_centralizer hIab (kSub_le_normalizer_iSub h hk) ?_
      have h1 : φ ⁅(⟨x, hxK⟩ : ↥(kSub V H E)), ⟨k, hk⟩⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_commute.mpr
          (Subgroup.mem_center_iff.mp (hcon ⟨x, hxK⟩ hx) (φ ⟨k, hk⟩)).symm
      exact (hφ.ker_iff _).mp h1
    have hVW : V ⊓ iSub V H E ≤ iSub V H E ⊓ Subgroup.centralizer ({x} : Set G) := by
      intro w hw
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hw).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commutatorElement_eq_one_iff_commute.mp (hcomm w hw x hx)
    intro y hy
    exact (Subgroup.mem_inf.mp (iSub_le_of_normalized h hW hVW hy)).2
  have hXle : X ≤ pCoreOf 2 (kSub V H E) := by
    intro x hx
    apply kSub_inf_centralizer_iSub_le_pCoreOf_of_oddCore h
    refine Subgroup.mem_inf.mpr ⟨hXK hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    exact Subgroup.mem_centralizer_singleton_iff.mp (hCx x hx hi)
  have hX2 : IsPGroup 2 ↥X :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kSub V H E)).to_le hXle
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp hX2
  have hj0 : j = 0 := by
    by_contra hj0
    have heven : Even (Nat.card ↥X) := by
      rw [hj]
      exact (Nat.even_pow).mpr ⟨even_two, hj0⟩
    exact (Nat.not_even_iff_odd.mpr hXodd) heven
  rw [hj0, pow_zero] at hj
  exact hX1 ((Subgroup.eq_bot_iff_card X).mpr hj)

theorem inf_centralizer_conj_eq_bot (h : Hyp716 V H E) {Q : Type} [Group Q]
    {φ : ↥(kSub V H E) →* Q} (hφ : IsBarMap (kSub V H E) (iSub V H E) φ)
    {a : G} (ha : a ∈ kSub V H E) (hP : PairHyp V (conjSubgroup V a)) {n : ℕ} (hn : 2 ≤ n)
    (hS : IsL2Gp ↥(barSub (kSub V H E) ((QuotientGroup.mk' (Subgroup.center Q)).comp φ)
      (V ⊔ conjSubgroup V a)) n)
    (hYI : pairY V (conjSubgroup V a) ≤ iSub V H E) {X : Subgroup G} (hXK : X ≤ kSub V H E)
    (hXodd : Odd (Nat.card ↥X))
    (hXY : ∀ x ∈ X, pairY V (conjSubgroup V a) ≤ Subgroup.centralizer ({x} : Set G))
    (hXL : barSub (kSub V H E) φ X ≤
      Subgroup.centralizer (barSub (kSub V H E) φ (V ⊔ conjSubgroup V a) : Set Q))
    {k x₀ : ↥(kSub V H E)} (hx₀ : (x₀ : G) ∈ X)
    (hy₁ : φ (k⁻¹ * x₀ * k) ∈
      barSub (kSub V H E) φ (V ⊔ conjSubgroup V a) ⊔ barSub (kSub V H E) φ X)
    (hy₂ : φ (k⁻¹ * x₀ * k) ∉ barSub (kSub V H E) φ X) :
    pairY V (conjSubgroup V a) ⊓
      Subgroup.centralizer ({((k⁻¹ * x₀ * k : ↥(kSub V H E)) : G)} : Set G) = ⊥ := by
  have hVK : V ≤ kSub V H E := le_kSub h.mem
  have hAK : conjSubgroup V a ≤ kSub V H E := s716C_conjSubgroup_le hVK ha
  haveI hIab : IsMulCommutative ↥(iSub V H E) := (isElemAbelian_iSub h).1
  have hpow : ∀ x : G, x ∈ X → x ^ Nat.card ↥X = 1 := fun x hx => by
    have h1 : (⟨x, hx⟩ : ↥X) ^ Nat.card ↥X = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow] at h2
  have hx₀m : x₀ ^ Nat.card ↥X = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hpow _ hx₀)
  have hym : (k⁻¹ * x₀ * k) ^ Nat.card ↥X = 1 := by
    have h1 : (k⁻¹ * x₀ * k) ^ Nat.card ↥X = k⁻¹ * x₀ ^ Nat.card ↥X * k := by
      have h2 := conj_pow (a := k⁻¹) (b := x₀) (i := Nat.card ↥X)
      simpa using h2
    rw [h1, hx₀m, mul_one, inv_mul_cancel]
  generalize k⁻¹ * x₀ * k = y at hy₁ hy₂ hym ⊢
  obtain ⟨lb, hlb, xb, hxb, hyx⟩ := mem_sup_of_le_centralizer hXL hy₁
  obtain ⟨l, hlL, rfl⟩ := mem_barSub.mp hlb
  obtain ⟨x', hx'X, rfl⟩ := mem_barSub.mp hxb
  have hφl : φ l ≠ 1 := by
    intro h1
    apply hy₂
    rw [hyx, h1, one_mul]
    exact mem_barSub.mpr ⟨x', hx'X, rfl⟩
  have hlI : (l : G) ∉ iSub V H E := fun hl => hφl ((hφ.ker_iff l).mpr hl)
  have hlY : (l : G) ∉ pairY V (conjSubgroup V a) := fun hl => hlI (hYI hl)
  have hcomm : φ l * φ x' = φ x' * φ l :=
    Subgroup.mem_centralizer_iff.mp (hXL (mem_barSub.mpr ⟨x', hx'X, rfl⟩)) (φ l)
      (mem_barSub.mpr ⟨l, hlL, rfl⟩)
  have hx'm : x' ^ Nat.card ↥X = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hpow _ hx'X)
  have hφlm : φ l ^ Nat.card ↥X = 1 := by
    have h1 : φ y ^ Nat.card ↥X = 1 := by rw [← map_pow, hym, map_one]
    rw [hyx, Commute.mul_pow (show Commute (φ l) (φ x') from hcomm), ← map_pow φ x', hx'm,
      map_one, mul_one] at h1
    exact h1
  have hψ : ((QuotientGroup.mk' (Subgroup.center Q)).comp φ) (l ^ Nat.card ↥X) = 1 := by
    rw [MonoidHom.comp_apply, map_pow, hφlm, map_one]
  have hlmL : ((l ^ Nat.card ↥X : ↥(kSub V H E)) : G) ∈ V ⊔ conjSubgroup V a := by
    rw [Subgroup.coe_pow]
    exact Subgroup.pow_mem _ hlL _
  have hlmY : (l : G) ^ Nat.card ↥X ∈ pairY V (conjSubgroup V a) := by
    have h1 := (pair_kernel_eq hP hVK hAK ((QuotientGroup.mk' (Subgroup.center Q)).comp φ) hn hS
      (l ^ Nat.card ↥X) hlmL).mp hψ
    rwa [Subgroup.coe_pow] at h1
  have hC := pairY_inf_centralizer_eq_bot hP hVK hAK
    ((QuotientGroup.mk' (Subgroup.center Q)).comp φ) hn hS hlL hlY hXodd hlmY
  rw [eq_bot_iff]
  intro w hw
  have hwY : w ∈ pairY V (conjSubgroup V a) := (Subgroup.mem_inf.mp hw).1
  have hwy : w * (y : G) = (y : G) * w :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hw).2
  have hwI : w ∈ iSub V H E := hYI hwY
  obtain ⟨j, hj⟩ : ∃ j : ↥(kSub V H E), y = l * x' * j :=
    ⟨(l * x')⁻¹ * y, (mul_inv_cancel_left (l * x') y).symm⟩
  have hφj : φ j = 1 := by
    have h1 : φ y = φ l * φ x' * φ j := by rw [hj, map_mul, map_mul]
    rw [hyx] at h1
    exact (mul_eq_left.mp h1.symm)
  have hjI : (j : G) ∈ iSub V H E := (hφ.ker_iff j).mp hφj
  have hyG : (y : G) = (l : G) * (x' : G) * (j : G) := congrArg Subtype.val hj
  have hxw : w * (x' : G) = (x' : G) * w :=
    Subgroup.mem_centralizer_singleton_iff.mp (hXY (x' : G) hx'X hwY)
  have hjw : (j : G) * w = w * (j : G) := setLike_mul_comm hjI hwI
  rw [hyG] at hwy
  have key : (w * (l : G)) * ((x' : G) * (j : G)) = ((l : G) * w) * ((x' : G) * (j : G)) := by
    calc (w * (l : G)) * ((x' : G) * (j : G)) = w * ((l : G) * (x' : G) * (j : G)) := by group
      _ = ((l : G) * (x' : G) * (j : G)) * w := hwy
      _ = (l : G) * ((x' : G) * ((j : G) * w)) := by group
      _ = (l : G) * ((x' : G) * (w * (j : G))) := by rw [hjw]
      _ = (l : G) * (((x' : G) * w) * (j : G)) := by group
      _ = (l : G) * ((w * (x' : G)) * (j : G)) := by rw [hxw]
      _ = ((l : G) * w) * ((x' : G) * (j : G)) := by group
  have hwl : w * (l : G) = (l : G) * w := mul_right_cancel key
  have hmem : w ∈ pairY V (conjSubgroup V a) ⊓ Subgroup.centralizer ({(l : G)} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hwY, Subgroup.mem_centralizer_singleton_iff.mpr hwl⟩
  rw [hC] at hmem
  exact hmem

theorem s716D_conj_mem (h : Hyp716 V H E) {U : Subgroup G} (hU : U ∈ omegaSet V H E)
    {T : Subgroup G} (hUT : U ⊓ iSub V H E ≤ T) {u t : G} (hu : u ∈ U)
    (htI : t ∈ iSub V H E) (htT : t ∈ T) : u * t * u⁻¹ ∈ T := by
  have huN : u ∈ Subgroup.normalizer (iSub V H E : Set G) :=
    kSub_le_normalizer_iSub h (le_kSub hU hu)
  have h1 : u * t * u⁻¹ ∈ iSub V H E := (Subgroup.mem_normalizer_iff.mp huN t).mp htI
  have htN : t ∈ Subgroup.normalizer (U : Set G) := iSub_le_normalizer_of_mem_omegaSet h hU htI
  have h2 : t * u⁻¹ * t⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp htN _).mp (inv_mem hu)
  have hc : ⁅u, t⁆ ∈ U ⊓ iSub V H E := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have e : ⁅u, t⁆ = u * (t * u⁻¹ * t⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact mul_mem hu h2
    · have e : ⁅u, t⁆ = (u * t * u⁻¹) * t⁻¹ := by
        simp only [commutatorElement_def]
      rw [e]
      exact mul_mem h1 (inv_mem htI)
  have e : u * t * u⁻¹ = ⁅u, t⁆ * t := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact mul_mem (hUT hc) htT

theorem iSub_eq_sup_inf_of_kSub_eq (h : Hyp716 V H E) {a b : G} (ha : a ∈ kSub V H E)
    (hb : b ∈ kSub V H E)
    (hK : kSub V H E = iSub V H E ⊔ (V ⊔ conjSubgroup V a ⊔ conjSubgroup V b)) :
    iSub V H E = (V ⊓ iSub V H E) ⊔ (conjSubgroup V a ⊓ iSub V H E) ⊔
      (conjSubgroup V b ⊓ iSub V H E) := by
  have hAΩ : conjSubgroup V a ∈ omegaSet V H E := conjSubgroup_mem_omegaSet_of_mem_kSub h ha
  have hBΩ : conjSubgroup V b ∈ omegaSet V H E := conjSubgroup_mem_omegaSet_of_mem_kSub h hb
  haveI hIab : IsMulCommutative ↥(iSub V H E) := (isElemAbelian_iSub h).1
  set I' : Subgroup G := (V ⊓ iSub V H E) ⊔ (conjSubgroup V a ⊓ iSub V H E) ⊔
    (conjSubgroup V b ⊓ iSub V H E) with hI'
  have hI'I : I' ≤ iSub V H E := sup_le (sup_le inf_le_right inf_le_right) inf_le_right
  have hV1 : V ⊓ iSub V H E ≤ I' := le_sup_left.trans le_sup_left
  have hV2 : conjSubgroup V a ⊓ iSub V H E ≤ I' := le_sup_right.trans le_sup_left
  have hV3 : conjSubgroup V b ⊓ iSub V H E ≤ I' := le_sup_right
  have hnorm : ∀ {U : Subgroup G}, U ∈ omegaSet V H E → U ⊓ iSub V H E ≤ I' →
      U ≤ Subgroup.normalizer (I' : Set G) := by
    intro U hU hUI' u hu
    have hconj : ∀ g ∈ U, ∀ t ∈ I', g * t * g⁻¹ ∈ I' := by
      intro g hg t ht
      have hT : ∀ T : Subgroup G, T ≤ I' → T ≤ iSub V H E →
          T ≤ Subgroup.comap (MulAut.conj g).toMonoidHom I' := by
        intro T hTI' hTI t' ht'
        exact s716D_conj_mem h hU hUI' hg (hTI ht') (hTI' ht')
      have hle : I' ≤ Subgroup.comap (MulAut.conj g).toMonoidHom I' :=
        sup_le (sup_le (hT _ hV1 inf_le_right) (hT _ hV2 inf_le_right))
          (hT _ hV3 inf_le_right)
      exact hle ht
    exact s716D_mem_normalizer_of_forall (hconj u hu) (fun t ht => by
      simpa using hconj u⁻¹ (inv_mem hu) t ht)
  have hIN : iSub V H E ≤ Subgroup.normalizer (I' : Set G) :=
    s716D_le_normalizer_of_le_abelian hIab le_rfl hI'I
  have hW : kSub V H E ≤ Subgroup.normalizer (I' : Set G) := by
    rw [hK]
    exact sup_le hIN (sup_le (sup_le (hnorm h.mem hV1) (hnorm hAΩ hV2)) (hnorm hBΩ hV3))
  exact le_antisymm (iSub_le_of_normalized h hW hV1) hI'I

theorem card_iSub_le_pow_three (h : Hyp716 V H E) {a b : G} (ha : a ∈ kSub V H E)
    (hb : b ∈ kSub V H E)
    (hK : kSub V H E = iSub V H E ⊔ (V ⊔ conjSubgroup V a ⊔ conjSubgroup V b)) :
    Nat.card ↥(iSub V H E) ≤ Nat.card ↥(V ⊓ iSub V H E) ^ 3 := by
  have hI := iSub_eq_sup_inf_of_kSub_eq h ha hb hK
  haveI hIab : IsMulCommutative ↥(iSub V H E) := (isElemAbelian_iSub h).1
  have hN12 : V ⊓ iSub V H E ≤
      Subgroup.normalizer ((conjSubgroup V a ⊓ iSub V H E : Subgroup G) : Set G) :=
    s716D_le_normalizer_of_le_abelian hIab inf_le_right inf_le_right
  have hN3 : (V ⊓ iSub V H E) ⊔ (conjSubgroup V a ⊓ iSub V H E) ≤
      Subgroup.normalizer ((conjSubgroup V b ⊓ iSub V H E : Subgroup G) : Set G) :=
    s716D_le_normalizer_of_le_abelian hIab (sup_le inf_le_right inf_le_right) inf_le_right
  have ha' := card_conjSubgroup_inf_iSub h ha
  have hb' := card_conjSubgroup_inf_iSub h hb
  calc Nat.card ↥(iSub V H E)
      = Nat.card ↥((V ⊓ iSub V H E) ⊔ (conjSubgroup V a ⊓ iSub V H E) ⊔
          (conjSubgroup V b ⊓ iSub V H E)) :=
        congrArg (fun S : Subgroup G => Nat.card ↥S) hI
    _ ≤ Nat.card ↥((V ⊓ iSub V H E) ⊔ (conjSubgroup V a ⊓ iSub V H E)) *
          Nat.card ↥(conjSubgroup V b ⊓ iSub V H E) := s716D_card_sup_le hN3
    _ ≤ (Nat.card ↥(V ⊓ iSub V H E) * Nat.card ↥(conjSubgroup V a ⊓ iSub V H E)) *
          Nat.card ↥(conjSubgroup V b ⊓ iSub V H E) :=
        Nat.mul_le_mul_right _ (s716D_card_sup_le hN12)
    _ = Nat.card ↥(V ⊓ iSub V H E) ^ 3 := by rw [ha', hb']; ring

end CFSG.LocalAnalysis.WeakClosure81

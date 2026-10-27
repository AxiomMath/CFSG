module

public import CFSG.Quasithin.Vol2.Ch12Sec6L33t
public import CFSG.Quasithin.Background.C126A5Lift6
public import CFSG.Quasithin.Background.B5NonInputs

public section

namespace CFSG.Quasithin.H13.L1233

open CFSG.Open CFSG.Quasithin S126 Equiv
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Components

variable {T K H : Subgroup G}

theorem conjSub_inv_le_conjClosure {t : G} (ht : t ∈ T) : conjSub t⁻¹ K ≤ conjClosure K T := by
  intro x hx
  rw [mem_conjSub, inv_inv] at hx
  have h := mem_conjClosure (T.inv_mem ht) hx
  simpa [mul_assoc] using h

theorem conjSub_inv_ne {t : G} (htK : t ∉ Subgroup.normalizer (K : Set G)) :
    K ≠ conjSub t⁻¹ K := by
  intro h
  apply htK
  have h' : t⁻¹ ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_conjSub_eq h.symm
  simpa using Subgroup.inv_mem _ h'

end Components

section Star

variable {T L H K : Subgroup G}

omit [Finite G] in
theorem star_mono {X Y : Subgroup G} (h : X ≤ Y) : S126.star H X ≤ S126.star H Y := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx)), rfl⟩

theorem star_card_K (h2 : Case2 T L H K) : Nat.card ↥(S126.star H K) = 60 := by
  obtain ⟨-, ⟨e⟩, -, -, -, -⟩ := h2
  rw [Nat.card_congr e.toEquiv, S126.card_alternatingGroup_five]

theorem star_card_K0 (h2 : Case2 T L H K) :
    Nat.card ↥(S126.star H (conjClosure K T)) = 3600 := by
  obtain ⟨-, -, ⟨e⟩, -, -, -⟩ := h2
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, S126.card_alternatingGroup_five]

theorem isSimpleGroup_alt5 : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem exists_noncomm_alt5 : ∃ a b : ↥(alternatingGroup (Fin 5)), a * b ≠ b * a :=
  CFSG.Quasithin.C126.A5.exists_not_comm_alt_five

theorem center_eq_bot_of_simple {X : Type} [Group X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hX
    have hb : b ∈ Subgroup.center X := h ▸ Subgroup.mem_top b
    exact hab ((Subgroup.mem_center_iff.1 hb a))

theorem isSimpleGroup_star_K (h2 : Case2 T L H K) : IsSimpleGroup ↥(S126.star H K) := by
  obtain ⟨-, ⟨e⟩, -, -, -, -⟩ := h2
  exact (MulEquiv.isSimpleGroup_congr e).mpr isSimpleGroup_alt5

theorem star_conjSub_eq_map {t : G} (ht : t ∈ T) (hTH : T ≤ H) :
    S126.star H (conjSub t⁻¹ K) =
      (S126.star H K).map (MulAut.conj (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ :
        S126.HStar H)).toMonoidHom :=
  star_conjSub (H.inv_mem (hTH ht))

end Star

section Pair

variable {T L H K : Subgroup G}

theorem normalizes_of_commute_sup {P Q : Subgroup G} (hc : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a)
    {s : G} (hs : s ∈ P ⊔ Q) {p : G} (hp : p ∈ P) : s * p * s⁻¹ ∈ P := by
  rw [← range_mulHom P Q hc] at hs
  obtain ⟨⟨a, b⟩, rfl⟩ := MonoidHom.mem_range.1 hs
  rw [mulHom_apply]
  have h1 : (b : G) * p = p * (b : G) := (hc p hp b b.2).symm
  have e : (a : G) * (b : G) * p * ((a : G) * (b : G))⁻¹ = (a : G) * p * (a : G)⁻¹ := by
    calc (a : G) * (b : G) * p * ((a : G) * (b : G))⁻¹
        = (a : G) * ((b : G) * p) * (b : G)⁻¹ * (a : G)⁻¹ := by group
      _ = (a : G) * p * (a : G)⁻¹ := by rw [h1]; group
  rw [e]
  exact P.mul_mem (P.mul_mem a.2 hp) (P.inv_mem a.2)

noncomputable def starK2_equiv {t : G} (ht : t ∈ T) (hTH : T ≤ H) :
    ↥(S126.star H K) ≃* ↥(S126.star H (conjSub t⁻¹ K)) :=
  (Subgroup.equivMapOfInjective _ _
      (MulAut.conj (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ : S126.HStar H)).injective).trans
    (MulEquiv.subgroupCongr (star_conjSub_eq_map ht hTH).symm)

theorem star_card_K2 (h2 : Case2 T L H K) {t : G} (ht : t ∈ T) (hTH : T ≤ H) :
    Nat.card ↥(S126.star H (conjSub t⁻¹ K)) = 60 := by
  rw [Nat.card_congr (starK2_equiv ht hTH).symm.toEquiv, star_card_K h2]

theorem isSimpleGroup_star_K2 (h2 : Case2 T L H K) {t : G} (ht : t ∈ T) (hTH : T ≤ H) :
    IsSimpleGroup ↥(S126.star H (conjSub t⁻¹ K)) :=
  (MulEquiv.isSimpleGroup_congr (starK2_equiv ht hTH)).mp (isSimpleGroup_star_K h2)

theorem nonabelian_star_K (h2 : Case2 T L H K) :
    ∃ a b : ↥(S126.star H K), a * b ≠ b * a := by
  obtain ⟨-, ⟨e⟩, -, -, -, -⟩ := h2
  obtain ⟨a, b, hab⟩ := exists_noncomm_alt5
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem nonabelian_star_K2 (h2 : Case2 T L H K) {t : G} (ht : t ∈ T) (hTH : T ≤ H) :
    ∃ a b : ↥(S126.star H (conjSub t⁻¹ K)), a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := nonabelian_star_K h2
  exact ⟨starK2_equiv ht hTH a, starK2_equiv ht hTH b, fun h => hab (by
    have := congrArg (starK2_equiv ht hTH).symm h
    simpa using this)⟩

theorem commute_star_K_K2 (h2 : Case2 T L H K) {t : G} (ht : t ∈ T) (hKc : K ∈ cComp H)
    (hTH : T ≤ H) (htK : t ∉ Subgroup.normalizer (K : Set G)) :
    ∀ x ∈ S126.star H K, ∀ y ∈ S126.star H (conjSub t⁻¹ K), x * y = y * x :=
  commute_star hKc (conjSub_mem_cComp hKc (H.inv_mem (hTH ht))) (conjSub_inv_ne htK)
    (isSimpleGroup_star_K h2) (isSimpleGroup_star_K2 h2 ht hTH)

theorem inf_star_K_K2 (h2 : Case2 T L H K) {t : G} (ht : t ∈ T) (hKc : K ∈ cComp H)
    (hTH : T ≤ H) (htK : t ∉ Subgroup.normalizer (K : Set G)) :
    S126.star H K ⊓ S126.star H (conjSub t⁻¹ K) = ⊥ := by
  have hcomm := commute_star_K_K2 h2 ht hKc hTH htK
  rw [eq_bot_iff]
  rintro x ⟨hxA, hxB⟩
  have hc : (⟨x, hxA⟩ : ↥(S126.star H K)) ∈ Subgroup.center ↥(S126.star H K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2 x hxB)
  haveI := isSimpleGroup_star_K h2
  have hz := center_eq_bot_of_simple (nonabelian_star_K h2) ▸ hc
  rw [Subgroup.mem_bot] at hz
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hz)

theorem sup_star_K_K2 (h2 : Case2 T L H K) {t : G} (ht : t ∈ T) (hKc : K ∈ cComp H)
    (hTH : T ≤ H) (htK : t ∉ Subgroup.normalizer (K : Set G)) :
    S126.star H K ⊔ S126.star H (conjSub t⁻¹ K) = S126.star H (conjClosure K T) := by
  have hle : S126.star H K ⊔ S126.star H (conjSub t⁻¹ K) ≤ S126.star H (conjClosure K T) :=
    sup_le (star_mono (le_conjClosure K T)) (star_mono (conjSub_inv_le_conjClosure ht))
  have hc := card_sup_of_commute (commute_star_K_K2 h2 ht hKc hTH htK)
    (inf_star_K_K2 h2 ht hKc hTH htK)
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hc, star_card_K h2, star_card_K2 h2 ht hTH, star_card_K0 h2]

theorem conj_eq_or_of_sup {Q : Type} [Group Q] [Finite Q] {A B C : Subgroup Q}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊔ B = C) (hCn : C.Normal)
    (hBs : IsSimpleGroup ↥B) (hBnon : ∃ a b : ↥B, a * b ≠ b * a)
    (hAcard : Nat.card ↥A = 60) (hBcard : Nat.card ↥B = 60) (x : Q) :
    A.map (MulAut.conj x).toMonoidHom = A ∨ A.map (MulAut.conj x).toMonoidHom = B := by
  have hcomm' : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  have hAC : A ≤ C := hAB ▸ le_sup_left
  have hBC : B ≤ C := hAB ▸ le_sup_right
  have hAnorm : ∀ s ∈ C, ∀ a ∈ A, s * a * s⁻¹ ∈ A := fun s hs a ha =>
    normalizes_of_commute_sup hcomm (by rw [hAB]; exact hs) ha
  have hBnorm : ∀ s ∈ C, ∀ b ∈ B, s * b * s⁻¹ ∈ B := fun s hs b hb =>
    normalizes_of_commute_sup hcomm' (by rw [sup_comm, hAB]; exact hs) hb
  have hNcard : Nat.card ↥(A.map (MulAut.conj x).toMonoidHom) = 60 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hAcard]
  have hmemN : ∀ a ∈ A, x * a * x⁻¹ ∈ A.map (MulAut.conj x).toMonoidHom := fun a ha =>
    Subgroup.mem_map.2 ⟨a, ha, rfl⟩
  have hNmem : ∀ n ∈ A.map (MulAut.conj x).toMonoidHom, ∃ a ∈ A, x * a * x⁻¹ = n := fun n hn => by
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.1 hn
    exact ⟨a, ha, hae⟩
  have hNC : ∀ n ∈ A.map (MulAut.conj x).toMonoidHom, n ∈ C := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := hNmem n hn
    exact hCn.conj_mem a (hAC ha) x
  have hNnorm : ∀ s ∈ C, ∀ n ∈ A.map (MulAut.conj x).toMonoidHom,
      s * n * s⁻¹ ∈ A.map (MulAut.conj x).toMonoidHom := by
    intro s hs n hn
    obtain ⟨a, ha, rfl⟩ := hNmem n hn
    have hs' : x⁻¹ * s * x⁻¹⁻¹ ∈ C := hCn.conj_mem s hs x⁻¹
    have key := hAnorm _ hs' a ha
    have e : s * (x * a * x⁻¹) * s⁻¹ = x * ((x⁻¹ * s * x⁻¹⁻¹) * a * (x⁻¹ * s * x⁻¹⁻¹)⁻¹) * x⁻¹ := by
      group
    rw [e]
    exact hmemN _ key
  set N := A.map (MulAut.conj x).toMonoidHom with hNdef
  have hDn : ((N ⊓ B).subgroupOf B).Normal := by
    constructor
    intro d hd g
    rw [Subgroup.mem_subgroupOf] at hd ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨hNnorm g (hBC g.2) _ hd.1, ?_⟩
    exact B.mul_mem (B.mul_mem g.2 hd.2) (B.inv_mem g.2)
  haveI := hBs
  haveI := hDn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ B).subgroupOf B) with hbot | htop
  ·
    have hNB : ∀ y ∈ N, y ∈ B → y = 1 := by
      intro y hyN hyB
      have h1 : (⟨y, hyB⟩ : ↥B) ∈ (N ⊓ B).subgroupOf B := Subgroup.mem_subgroupOf.2 ⟨hyN, hyB⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
    have hNcomm : ∀ n ∈ N, ∀ b ∈ B, n * b = b * n := by
      intro n hn b hb
      have h1 : n * b * n⁻¹ * b⁻¹ ∈ N := by
        have hbn : b * n⁻¹ * b⁻¹ ∈ N := hNnorm b (hBC hb) n⁻¹ (N.inv_mem hn)
        have e : n * b * n⁻¹ * b⁻¹ = n * (b * n⁻¹ * b⁻¹) := by group
        rw [e]
        exact N.mul_mem hn hbn
      have h2 : n * b * n⁻¹ * b⁻¹ ∈ B :=
        B.mul_mem (hBnorm n (hNC n hn) b hb) (B.inv_mem hb)
      have h3 := hNB _ h1 h2
      calc n * b = n * b * n⁻¹ * b⁻¹ * (b * n) := by group
        _ = b * n := by rw [h3, one_mul]
    have hNA : N ≤ A := by
      intro n hn
      have hnC := hNC n hn
      rw [← hAB, ← range_mulHom A B hcomm] at hnC
      obtain ⟨⟨a₁, b₁⟩, hab⟩ := MonoidHom.mem_range.1 hnC
      rw [mulHom_apply] at hab
      have hcent : ∀ b ∈ B, (b₁ : Q) * b = b * b₁ := by
        intro b hb
        have h1 := hNcomm n hn b hb
        rw [← hab] at h1
        have h2 : b * (a₁ : Q) = a₁ * b := (hcomm a₁ a₁.2 b hb).symm
        have h3 : (a₁ : Q) * (b₁ * b) = a₁ * (b * b₁) := by
          calc (a₁ : Q) * (b₁ * b) = ((a₁ : Q) * b₁) * b := by group
            _ = b * ((a₁ : Q) * b₁) := h1
            _ = (b * a₁) * b₁ := by group
            _ = (a₁ * b) * b₁ := by rw [h2]
            _ = a₁ * (b * b₁) := by group
        exact mul_left_cancel h3
      have hz : (⟨b₁, b₁.2⟩ : ↥B) ∈ Subgroup.center ↥B := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hcent g g.2).symm
      rw [center_eq_bot_of_simple hBnon, Subgroup.mem_bot] at hz
      have hb1 : (b₁ : Q) = 1 := congrArg Subtype.val hz
      rw [← hab, hb1, mul_one]
      exact a₁.2
    left
    exact Subgroup.eq_of_le_of_card_ge hNA (by rw [hNcard, hAcard])
  ·
    have hBN : B ≤ N := by
      intro b hb
      have h1 : (⟨b, hb⟩ : ↥B) ∈ (N ⊓ B).subgroupOf B := htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 h1)).1
    right
    exact (Subgroup.eq_of_le_of_card_ge hBN (by rw [hNcard, hBcard])).symm

theorem normal_star_K0 {T H K : Subgroup G} (hK0 : H ≤ Subgroup.normalizer (conjClosure K T : Set G)) :
    (S126.star H (conjClosure K T)).Normal := by
  constructor
  rintro n ⟨x, hx, rfl⟩ g
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨y * x * y⁻¹, ?_, ?_⟩
  · have hx' : (x : G) ∈ conjClosure K T := Subgroup.mem_subgroupOf.1 hx
    have h1 := (Subgroup.mem_normalizer_iff.1 (hK0 y.2) (x : G)).1 hx'
    exact Subgroup.mem_subgroupOf.2 (by simpa using h1)
  · simp [map_mul, map_inv]

theorem conj_star_K_eq_or {T L H K : Subgroup G} (h2 : Case2 T L H K) {t : G} (ht : t ∈ T)
    (hKc : K ∈ cComp H) (hTH : T ≤ H) (htK : t ∉ Subgroup.normalizer (K : Set G))
    (hK0 : H ≤ Subgroup.normalizer (conjClosure K T : Set G)) (x : S126.HStar H) :
    (S126.star H K).map (MulAut.conj x).toMonoidHom = S126.star H K ∨
      (S126.star H K).map (MulAut.conj x).toMonoidHom = S126.star H (conjSub t⁻¹ K) :=
  conj_eq_or_of_sup (commute_star_K_K2 h2 ht hKc hTH htK) (sup_star_K_K2 h2 ht hKc hTH htK)
    (normal_star_K0 hK0) (isSimpleGroup_star_K2 h2 ht hTH) (nonabelian_star_K2 h2 ht hTH)
    (star_card_K h2) (star_card_K2 h2 ht hTH) x

omit [Finite G] in
theorem mem_normalizer_inv_mul_of_map_eq {Q : Type} [Group Q] {S : Subgroup Q} {x y : Q}
    (h : S.map (MulAut.conj x).toMonoidHom = S.map (MulAut.conj y).toMonoidHom) :
    y⁻¹ * x ∈ Subgroup.normalizer (S : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have h1 : x * g * x⁻¹ ∈ S.map (MulAut.conj y).toMonoidHom := by
      rw [← h]; exact Subgroup.mem_map.2 ⟨g, hg, rfl⟩
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.1 h1
    have hse' : y * s * y⁻¹ = x * g * x⁻¹ := by simpa [MulAut.conj_apply] using hse
    have e : y⁻¹ * x * g * (y⁻¹ * x)⁻¹ = s := by
      calc y⁻¹ * x * g * (y⁻¹ * x)⁻¹ = y⁻¹ * (x * g * x⁻¹) * y := by group
        _ = y⁻¹ * (y * s * y⁻¹) * y := by rw [hse']
        _ = s := by group
    rw [e]
    exact hs
  · intro hg
    have h1 : (MulAut.conj y) (y⁻¹ * x * g * (y⁻¹ * x)⁻¹) ∈ S.map (MulAut.conj y).toMonoidHom :=
      Subgroup.mem_map.2 ⟨_, hg, rfl⟩
    rw [← h] at h1
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.1 h1
    have e2 : y * (y⁻¹ * x * g * (y⁻¹ * x)⁻¹) * y⁻¹ = x * g * x⁻¹ := by group
    have hse2 : x * s * x⁻¹ = y * (y⁻¹ * x * g * (y⁻¹ * x)⁻¹) * y⁻¹ := hse
    have hse' : x * s * x⁻¹ = x * g * x⁻¹ := by
      rw [hse2, e2]
    have hsg : s = g := mul_left_cancel (mul_right_cancel hse')
    rw [← hsg]
    exact hs

omit [Finite G] in
theorem map_conj_one {Q : Type} [Group Q] (S : Subgroup Q) :
    S.map (MulAut.conj (1 : Q)).toMonoidHom = S := by
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using ha
  · intro hq
    exact ⟨q, hq, by simp [MulAut.conj_apply]⟩

theorem perm_star_K {T L H K : Subgroup G} (h2 : Case2 T L H K) {t : G} (ht : t ∈ T)
    (hKc : K ∈ cComp H) (hTH : T ≤ H) (htK : t ∉ Subgroup.normalizer (K : Set G))
    (hK0 : H ≤ Subgroup.normalizer (conjClosure K T : Set G)) (x : S126.HStar H) :
    x ∈ Subgroup.normalizer (S126.star H K : Set (S126.HStar H)) ∨
      (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ : S126.HStar H)⁻¹ * x ∈
        Subgroup.normalizer (S126.star H K : Set (S126.HStar H)) := by
  rcases conj_star_K_eq_or h2 ht hKc hTH htK hK0 x with h | h
  · left
    have := mem_normalizer_inv_mul_of_map_eq (x := x) (y := 1)
      (by rw [h, map_conj_one])
    simpa using this
  · right
    exact mem_normalizer_inv_mul_of_map_eq (x := x) (y := (QuotientGroup.mk ⟨t⁻¹, H.inv_mem (hTH ht)⟩ : S126.HStar H))
      (h.trans (by rw [star_conjSub_eq_map ht hTH]))

theorem card_quot_star_K0 {T L H K : Subgroup G} (h2 : Case2 T L H K) :
    Nat.card (S126.HStar H ⧸ S126.star H (conjClosure K T)) = 4 ∨
      Nat.card (S126.HStar H ⧸ S126.star H (conjClosure K T)) = 8 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (S126.star H (conjClosure K T))
  rw [star_card_K0 h2] at h
  obtain ⟨-, -, -, -, hc, -⟩ := h2
  rcases hc with hc | hc <;> rw [hc] at h
  · left; omega
  · right; omega

theorem pow_eight_mem_star_K0 {T L H K : Subgroup G} (h2 : Case2 T L H K)
    (hK0 : H ≤ Subgroup.normalizer (conjClosure K T : Set G)) (y : S126.HStar H) :
    y ^ 8 ∈ S126.star H (conjClosure K T) := by
  haveI := normal_star_K0 hK0
  have hdvd := orderOf_dvd_natCard
    (QuotientGroup.mk y : S126.HStar H ⧸ S126.star H (conjClosure K T))
  have hpow := orderOf_dvd_iff_pow_eq_one.1 hdvd
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hpow
  rcases card_quot_star_K0 h2 with hq | hq
  · rw [hq] at hpow
    rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul]
    exact (S126.star H (conjClosure K T)).pow_mem hpow 2
  · rw [hq] at hpow
    exact hpow

noncomputable def pairMulEquiv (M : Type) [Group M] : M × M ≃* (Fin 2 → M) where
  toFun p := ![p.1, p.2]
  invFun f := (f 0, f 1)
  left_inv _ := rfl
  right_inv f := by funext i; fin_cases i <;> rfl
  map_mul' x y := by funext i; fin_cases i <;> rfl

theorem layer_star_K0 {T L H K : Subgroup G} (h2 : Case2 T L H K) :
    CFSG.layer ↥(S126.star H (conjClosure K T)) = ⊤ := by
  obtain ⟨-, -, ⟨e⟩, -, -, -⟩ := h2
  haveI : ∀ _ : Fin 2, IsSimpleGroup (alternatingGroup (Fin 5)) := fun _ => isSimpleGroup_alt5
  exact CFSG.LocalCores.layer_eq_top_of_mulEquiv_pi (ι := Fin 2) (S := fun _ => alternatingGroup (Fin 5))
    (fun _ => exists_noncomm_alt5) (e.trans (pairMulEquiv _))

theorem sqtkGroup_HStar (hA21 : AsA21SQTKSection) {T L H K : Subgroup G} (hSQ : SQTKGroup ↥H)
    (h2 : Case2 T L H K) (hK0 : H ≤ Subgroup.normalizer (conjClosure K T : Set G)) :
    SQTKGroup (S126.HStar H) := by
  haveI := normal_star_K0 hK0
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (⊤ : Subgroup ↥H).subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) q
    exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩
  have hpg : IsPGroup 2 (S126.HStar H ⧸ S126.star H (conjClosure K T)) := by
    rcases card_quot_star_K0 h2 with hq | hq
    · exact IsPGroup.of_card (n := 2) (by rw [hq]; norm_num)
    · exact IsPGroup.of_card (n := 3) (by rw [hq]; norm_num)
  exact hA21 ↥H hSQ ⊤ (S126.HStar H) _ hsurj (S126.star H (conjClosure K T))
    (layer_star_K0 h2) hpg

theorem pCore_star_K_bot {T L H K : Subgroup G} (h2 : Case2 T L H K) :
    CFSG.pCore 2 ↥(S126.star H K) = ⊥ := by
  haveI := isSimpleGroup_star_K h2
  have hcard := star_card_K h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥(S126.star H K)) with h | h
  · exact h
  · exfalso
    have h1 := CFSG.pCore_isPGroup (p := 2) (G := ↥(S126.star H K))
    rw [h] at h1
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h1
    rw [Subgroup.card_top, hcard] at hn
    have hn5 : n < 6 := by
      by_contra hn6
      push Not at hn6
      have : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn6
      omega
    interval_cases n <;> norm_num at hn

theorem isQuasisimple_star_K_quot {T L H K : Subgroup G} (h2 : Case2 T L H K) :
    CFSG.IsQuasisimple (↥(S126.star H K) ⧸ CFSG.pCore 2 ↥(S126.star H K)) := by
  haveI := isSimpleGroup_star_K h2
  have e : (↥(S126.star H K) ⧸ CFSG.pCore 2 ↥(S126.star H K)) ≃* ↥(S126.star H K) :=
    (QuotientGroup.quotientMulEquivOfEq (pCore_star_K_bot h2)).trans QuotientGroup.quotientBot
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (nonabelian_star_K h2)).1

end Pair

end CFSG.Quasithin.H13.L1233

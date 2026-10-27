module

public import CFSG.Quasithin.Vol2.Ch12Sec6L32d
public import CFSG.Quasithin.Vol2.Ch12Sec6L33d

public section

namespace CFSG.Quasithin.H13.L1233

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 S126P S126L1a
  S126L24 F126 L1232 Equiv

variable {G : Type} [Group G] [Finite G]

section Pair

variable {T V L V₁ Vp H K : Subgroup G}

theorem conjSub_mem_pair (h918 : HypF918 T V L V₁ Vp H K) (h2 : Case2 T L H K) {t₀ : G}
    (ht₀ : t₀ ∈ T) (ht₀K : t₀ ∉ Subgroup.normalizer (K : Set G)) {t : G} (ht : t ∈ T) :
    conjSub t K = K ∨ conjSub t K = conjSub t₀⁻¹ K := by
  have hTH : T ≤ H := h918.toHypF98.toHypF91.T_le_H
  have hKc : K ∈ cComp H := h918.K_cComp
  have hK₂c : conjSub t₀⁻¹ K ∈ cComp H := conjSub_mem_cComp hKc (H.inv_mem (hTH ht₀))
  have hXc : conjSub t K ∈ cComp H := conjSub_mem_cComp hKc (hTH ht)
  obtain ⟨-, ⟨e₁⟩, ⟨e₀⟩, hC, -, -⟩ := id h2
  have hA5 : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hsimple : ∀ g (hg : g ∈ H), IsSimpleGroup ↥(S126.star H (conjSub g K)) := by
    intro g hg
    have hs : IsSimpleGroup ↥(S126.star H K) := e₁.isSimpleGroup
    rw [star_conjSub hg]
    exact (((S126.star H K).equivMapOfInjective _ (MulAut.conj _).injective).symm).isSimpleGroup
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  have hsK : IsSimpleGroup ↥(S126.star H K) := e₁.isSimpleGroup
  have hsK₂ := hsimple _ (H.inv_mem (hTH ht₀))
  have hsX := hsimple _ (hTH ht)
  have hc1 := commute_star hXc hKc hne1 hsX hsK
  have hc2 := commute_star hXc hK₂c hne2 hsX hsK₂
  have hKK₂ : K ≠ conjSub t₀⁻¹ K := fun he => ht₀K (by
    have h1 : t₀⁻¹ ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_conjSub_eq he.symm
    simpa using Subgroup.inv_mem _ h1)
  have hcomm := commute_star hKc hK₂c hKK₂ hsK hsK₂
  have hnonab : ¬ ∀ a b : ↥(S126.star H K), a * b = b * a := by
    intro hab
    have : ∀ a b : ↥(alternatingGroup (Fin 5)), a * b = b * a := fun a b => by
      have := congrArg e₁ (hab (e₁.symm a) (e₁.symm b))
      simpa using this
    exact absurd (this ⟨swap 0 1 * swap 1 2, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩
      ⟨swap 1 2 * swap 2 3, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩) (by decide)
  have hi : S126.star H K ⊓ S126.star H (conjSub t₀⁻¹ K) = ⊥ := by
    have hn : ((S126.star H (conjSub t₀⁻¹ K)).subgroupOf (S126.star H K)).Normal :=
        ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have := hcomm g g.2 n hn
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, this, mul_inv_cancel_right]
      exact hn⟩
    rcases hn.eq_bot_or_eq_top with hb | ht'
    · rw [Subgroup.subgroupOf_eq_bot, disjoint_iff] at hb
      rw [inf_comm]
      exact hb
    · exfalso
      apply hnonab
      intro a b
      have hb : (b : S126.HStar H) ∈ S126.star H (conjSub t₀⁻¹ K) := by
        have : b ∈ (S126.star H (conjSub t₀⁻¹ K)).subgroupOf (S126.star H K) :=
          ht' ▸ Subgroup.mem_top b
        exact this
      exact Subtype.ext (hcomm a a.2 b hb)
  have hc60 : Nat.card ↥(S126.star H K) = 60 := by
    rw [Nat.card_congr e₁.toEquiv, S126.card_alternatingGroup_five]
  have hc60' : Nat.card ↥(S126.star H (conjSub t₀⁻¹ K)) = 60 := by
    rw [star_conjSub (H.inv_mem (hTH ht₀)),
      Subgroup.card_map_of_injective (MulAut.conj _).injective, hc60]
  have hc3600 : Nat.card ↥(S126.star H (conjClosure K T)) = 3600 := by
    rw [Nat.card_congr e₀.toEquiv, Nat.card_prod, S126.card_alternatingGroup_five]
  have hK₂K₀ : conjSub t₀⁻¹ K ≤ conjClosure K T := by
    rintro _ ⟨k, hk, rfl⟩
    exact mem_conjClosure (T.inv_mem ht₀) hk
  have hstar_mono : ∀ {X Y : Subgroup G}, X ≤ Y → S126.star H X ≤ S126.star H Y :=
    fun hXY => Subgroup.map_mono fun x hx => hXY hx
  have hsup : S126.star H K ⊔ S126.star H (conjSub t₀⁻¹ K) = S126.star H (conjClosure K T) :=
    Subgroup.eq_of_le_of_card_ge (sup_le (hstar_mono (le_conjClosure K T)) (hstar_mono hK₂K₀))
      (by rw [card_sup_of_commute hcomm hi, hc60, hc60', hc3600])
  have hXC : S126.star H (conjSub t K) ≤
      Subgroup.centralizer (S126.star H (conjClosure K T) : Set (S126.HStar H)) := by
    intro x hx
    rw [← hsup, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← range_mulHom _ _ hcomm] at hy
    obtain ⟨⟨a, b⟩, rfl⟩ := hy
    rw [mulHom_apply]
    have h1 := hc1 x hx a a.2
    have h2 := hc2 x hx b b.2
    calc (a : S126.HStar H) * b * x = a * (x * b) := by rw [mul_assoc, h2]
      _ = x * (a * b) := by rw [← mul_assoc, ← h1, mul_assoc]
  rw [hC] at hXC
  obtain ⟨a, b, hab⟩ := hsX.exists_pair_ne
  apply hab
  have ha : (a : S126.HStar H) = 1 := Subgroup.mem_bot.1 (hXC a.2)
  have hb : (b : S126.HStar H) = 1 := Subgroup.mem_bot.1 (hXC b.2)
  exact Subtype.ext (ha.trans hb.symm)

theorem conjSub_eq_conjSub_inv (h918 : HypF918 T V L V₁ Vp H K) (h2 : Case2 T L H K) {t : G}
    (ht : t ∈ T) (htK : t ∉ Subgroup.normalizer (K : Set G)) : conjSub t K = conjSub t⁻¹ K := by
  rcases conjSub_mem_pair h918 h2 ht htK ht with h | h
  · exact absurd (mem_normalizer_of_conjSub_eq h) htK
  · exact h

omit [Finite G] in
theorem mem_star_of_odd (h918 : HypF918 T V L V₁ Vp H K) (h2 : Case2 T L H K)
    {x : S126.HStar H} {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) :
    x ∈ S126.star H (conjClosure K T) := by
  obtain ⟨-, -, ⟨e₀⟩, -, hcardH, -⟩ := h2
  have hc3600 : Nat.card ↥(S126.star H (conjClosure K T)) = 3600 := by
    rw [Nat.card_congr e₀.toEquiv, Nat.card_prod, S126.card_alternatingGroup_five]
  have hK₀n : (S126.star H (conjClosure K T)).Normal := by
    have : ((conjClosure K T).subgroupOf H).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.1 (h918.K₀_normal g.2) n).1 hn⟩
    exact this.map _ (QuotientGroup.mk'_surjective _)
  have hidx : (S126.star H (conjClosure K T)).index ∣ 8 := by
    have hc := (S126.star H (conjClosure K T)).card_mul_index
    rw [hc3600] at hc
    rcases hcardH with h1 | h1 <;> rw [h1] at hc
    · exact ⟨2, by omega⟩
    · exact ⟨1, by omega⟩
  have h1 : orderOf (QuotientGroup.mk x : S126.HStar H ⧸ S126.star H (conjClosure K T)) ∣ m :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hxm, QuotientGroup.mk_one])
  have h2' : orderOf (QuotientGroup.mk x : S126.HStar H ⧸ S126.star H (conjClosure K T)) ∣ 8 :=
    (orderOf_dvd_natCard _).trans hidx
  have h3 : orderOf (QuotientGroup.mk x : S126.HStar H ⧸ S126.star H (conjClosure K T)) = 1 := by
    have hco : Nat.Coprime m 8 := by
      rw [show (8 : ℕ) = 2 ^ 3 by rfl]
      exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hm)
    exact Nat.eq_one_of_dvd_coprimes hco h1 h2'
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

omit [Finite G] in
theorem mk_mem_star_of_mem_L1 (h918 : HypF918 T V L V₁ Vp H K) (h2 : Case2 T L H K) {l : G}
    (hl : l ∈ Li L V₁) (hlH : l ∈ H) :
    (QuotientGroup.mk ⟨l, hlH⟩ : S126.HStar H) ∈ S126.star H (conjClosure K T) := by
  have hYH : oTwoRes (L ⊓ Subgroup.normalizer (V₁ : Set G)) ≤ H :=
    le_sup_left.trans h918.toHypF98.toHypF91.L₁T_le_H
  have hl' : l ∈ oTwoRes (L ⊓ Subgroup.normalizer (V₁ : Set G)) := hl
  have key : ∀ x (hx : x ∈ oTwoRes (L ⊓ Subgroup.normalizer (V₁ : Set G))),
      (QuotientGroup.mk ⟨x, hYH hx⟩ : S126.HStar H) ∈ S126.star H (conjClosure K T) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨-, m, hm, hym⟩ := id hy
      refine mem_star_of_odd h918 h2 hm ?_
      rw [← QuotientGroup.mk_pow]
      have : (⟨y, hYH (Subgroup.subset_closure hy)⟩ : ↥H) ^ m = 1 :=
        Subtype.ext (by simpa using hym)
      rw [this, QuotientGroup.mk_one]
    | one => exact Subgroup.one_mem _
    | mul y z hy hz ihy ihz =>
      have := Subgroup.mul_mem _ ihy ihz
      rwa [← QuotientGroup.mk_mul] at this
    | inv y hy ihy =>
      have := Subgroup.inv_mem _ ihy
      rwa [← QuotientGroup.mk_inv] at this
  exact key l hl'

end Pair

section Norm

variable {A B : Subgroup G} {g : G}

omit [Finite G] in
theorem conj_mem_sup (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    g * x * g⁻¹ ∈ A ⊔ B := by
  rw [Subgroup.sup_eq_closure] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact Subgroup.subset_closure (Or.inl ((Subgroup.mem_normalizer_iff.1 hA y).1 hy))
    · exact Subgroup.subset_closure (Or.inr ((Subgroup.mem_normalizer_iff.1 hB y).1 hy))
  | one => simp
  | mul y z _ _ hy hz =>
    have e : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
    have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hy

omit [Finite G] in
theorem mem_normalizer_sup (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_sup hA hB, fun hx => ?_⟩
  have := conj_mem_sup (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB) hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_normalizer_inf (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => ⟨(Subgroup.mem_normalizer_iff.1 hA x).1 hx.1,
      (Subgroup.mem_normalizer_iff.1 hB x).1 hx.2⟩,
    fun hx => ⟨(Subgroup.mem_normalizer_iff.1 hA x).2 hx.1,
      (Subgroup.mem_normalizer_iff.1 hB x).2 hx.2⟩⟩

omit [Finite G] in
theorem mem_normalizer_commutator (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ g, g ∈ Subgroup.normalizer (A : Set G) → g ∈ Subgroup.normalizer (B : Set G) →
      ∀ x ∈ ⁅A, B⁆, g * x * g⁻¹ ∈ ⁅A, B⁆ := by
    intro g hA hB x hx
    rw [Subgroup.commutator_def] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      refine Subgroup.subset_closure ⟨g * a * g⁻¹, (Subgroup.mem_normalizer_iff.1 hA a).1 ha,
        g * b * g⁻¹, (Subgroup.mem_normalizer_iff.1 hB b).1 hb, ?_⟩
      simp only [commutatorElement_def]
      group
    | one => simp
    | mul y z _ _ hy hz =>
      have e : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hy hz
    | inv y _ hy =>
      have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hA hB x, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB) _ hx
  simpa [mul_assoc] using this

end Norm

section Comm

variable {T L V H K : Subgroup G} [IsMulCommutative ↥V]

theorem tilde_commutator_eq (F : Frame126 T L V) (h918 : HypF918 T V L F.V1 F.V5 H K)
    (h2 : Case2 T L H K) :
    tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆ = tildeOf F.V1 (conjClosure F.V5 H) := by
  have h := h918.toHypF98.toHypF91
  have hUN : conjClosure F.V5 H ≤ N1 F.V1 :=
    h.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans (le_N1 h))
  have hVN : F.V5 ≤ N1 F.V1 := (le_conjClosure F.V5 H).trans hUN
  have hK₀H : conjClosure K T ≤ H := h918.K₀_le_H
  have hHV₁ : H ≤ Subgroup.normalizer (F.V1 : Set G) := le_N1 h
  have hCU : ⁅conjClosure F.V5 H, conjClosure K T⁆ ≤ conjClosure F.V5 H :=
    commutator_le_conjClosure le_rfl hK₀H
  have hCN : H ≤
      Subgroup.normalizer ((⁅conjClosure F.V5 H, conjClosure K T⁆ : Subgroup G) : Set G) :=
    fun x hx =>
      mem_normalizer_commutator (le_normalizer_conjClosure F.V5 H hx) (h918.K₀_normal hx)
  have hkey : ∀ l ∈ Li L F.V1, ∀ v ∈ F.V5,
      l * v * l⁻¹ * v⁻¹ ∈ ⁅conjClosure F.V5 H, conjClosure K T⁆ ⊔ F.V1 := by
    intro l hl v hv
    have hlH : l ∈ H := h.L₁T_le_H (Subgroup.mem_sup_left hl)
    obtain ⟨⟨k, hkH⟩, hkK, hke⟩ := mk_mem_star_of_mem_L1 h918 h2 hl hlH
    have hq := mem_pCoreOf_of_mk_eq hke
    set q := k⁻¹ * l with hqd
    have hvU : v ∈ conjClosure F.V5 H := le_conjClosure F.V5 H hv
    have hz : q * v * q⁻¹ * v⁻¹ ∈ F.V1 := by
      have := F.V1.inv_mem (h.commutator_conjClosure_le v hvU q hq)
      have e : (v * q * v⁻¹ * q⁻¹)⁻¹ = q * v * q⁻¹ * v⁻¹ := by group
      rwa [e] at this
    have hkz : k * (q * v * q⁻¹ * v⁻¹) * k⁻¹ = q * v * q⁻¹ * v⁻¹ := by
      have := Subgroup.mem_centralizer_iff.1 (h.H_le_centralizer hkH) _ hz
      rw [← this, mul_inv_cancel_right]
    have hc : k * v * k⁻¹ * v⁻¹ ∈ ⁅conjClosure F.V5 H, conjClosure K T⁆ := by
      rw [Subgroup.commutator_comm]
      have := Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 hkK) hvU
      rwa [commutatorElement_def] at this
    have e : l * v * l⁻¹ * v⁻¹ = (k * (q * v * q⁻¹ * v⁻¹) * k⁻¹) * (k * v * k⁻¹ * v⁻¹) := by
      rw [hqd]
      group
    rw [e, hkz]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left hc)
  have hW'N : Li L F.V1 ⊔ T ≤ Subgroup.normalizer
      ((F.V5 ⊓ (⁅conjClosure F.V5 H, conjClosure K T⁆ ⊔ F.V1) : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_inf (h.L₁T_normalizes_Vp hg)
      (mem_normalizer_sup (hCN (h.L₁T_le_H hg)) (hHV₁ (h.L₁T_le_H hg)))
  rcases h.irred _ (le_inf h.V₁_le_Vp le_sup_right) inf_le_left hW'N with hW | hW
  ·
    exfalso
    obtain ⟨l, hlL1, hlV, hl⟩ := S126L1b.exists_mem_L1 F aP_mem aP_pow_three aP_block
    have hA : ActEq aP 1 := by
      refine actEq_of_conj F hlV (Subgroup.one_mem _) hl (ActsAs.one F) fun v hv => ?_
      have hl5 : l * v * l⁻¹ ∈ F.V5 :=
        (Subgroup.mem_normalizer_iff.1 (h.L₁T_normalizes_Vp (Subgroup.mem_sup_left hlL1)) v).1 hv
      have h1 : l * v * l⁻¹ * v⁻¹ ∈ F.V1 := by
        rw [← hW]
        exact ⟨F.V5.mul_mem hl5 (F.V5.inv_mem hv), hkey l hlL1 v hv⟩
      have hvV : v ∈ V := h.Vp_le_V hv
      have key : ∀ a ∈ V, a * v⁻¹ ∈ F.V1 → a⁻¹ * (1 * v * 1⁻¹) ∈ F.V1 := fun a haV ha => by
        have e : a⁻¹ * (1 * v * 1⁻¹) = (a * v⁻¹)⁻¹ := by
          rw [one_mul, inv_one, mul_one, mul_inv_rev, inv_inv]
          exact S126L1b.comm_of_mem (V.inv_mem haV) hvV
        rw [e]
        exact F.V1.inv_mem ha
      exact key _ (h.Vp_le_V hl5) h1
    have := indep_ab (i := 1) (j := 0) (by simpa using hA)
    exact absurd this.1 (by decide)
  ·
    have hVS : ∀ w : ↥(UT F.V1 F.V5 H), (w : SecQuot (N1 F.V1) F.V1) ∈ tildeOf F.V1 F.V5 →
        w ∈ (tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆).subgroupOf (UT F.V1 F.V5 H) := by
      intro w hw
      rw [Subgroup.mem_subgroupOf]
      obtain ⟨⟨v, hvN⟩, hv5, hvw⟩ := mem_secImg.1 hw
      have hv' : v ∈ F.V5 ⊓ (⁅conjClosure F.V5 H, conjClosure K T⁆ ⊔ F.V1) := by
        rw [hW]
        exact hv5
      have hv : v ∈ ⁅conjClosure F.V5 H, conjClosure K T⁆ ⊔ F.V1 := hv'.2
      rw [← hvw]
      have hsup : tildeOf F.V1 (⁅conjClosure F.V5 H, conjClosure K T⁆ ⊔ F.V1) =
          tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆ := by
        have e1 : tildeOf F.V1 (⁅conjClosure F.V5 H, conjClosure K T⁆ ⊔ F.V1) =
            tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆ ⊔ tildeOf F.V1 F.V1 := by
          show ((⁅conjClosure F.V5 H, conjClosure K T⁆ ⊔ F.V1).subgroupOf (N1 F.V1)).map
            (secMk (N1 F.V1) F.V1) = _
          rw [Subgroup.subgroupOf_sup (hCU.trans hUN) Subgroup.le_normalizer, Subgroup.map_sup]
          rfl
        rw [e1, tildeOf_eq_bot_of_le le_rfl, sup_bot_eq]
      rw [← hsup]
      exact secMk_mem_secImg hv
    have hinv : ∀ x : ↥H, ∀ s ∈ (tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆).subgroupOf
        (UT F.V1 F.V5 H), thetaH h x s ∈
          (tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆).subgroupOf (UT F.V1 F.V5 H) := by
      intro x s hs
      rw [Subgroup.mem_subgroupOf] at hs ⊢
      obtain ⟨⟨c, hcN⟩, hcC, hcs⟩ := mem_secImg.1 hs
      rw [thetaH_apply, ← hcs, thetaH_apply_secMk]
      exact secMk_mem_secImg ((Subgroup.mem_normalizer_iff.1 (hCN x.2) c).1 hcC)
    have htop := eq_top_of_le h _ hVS hinv
    apply le_antisymm (secImg_mono hCU)
    intro y hy
    have : (⟨y, hy⟩ : ↥(UT F.V1 F.V5 H)) ∈
        (tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆).subgroupOf (UT F.V1 F.V5 H) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact this

end Comm

end CFSG.Quasithin.H13.L1233

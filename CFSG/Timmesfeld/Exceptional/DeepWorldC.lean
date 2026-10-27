module

public import CFSG.Timmesfeld.Exceptional.DeepWorldCCount
public import CFSG.Timmesfeld.Exceptional.DeepWorldCAllNear
public import CFSG.Timmesfeld.Exceptional.DeepWorldCFiber
public import CFSG.Timmesfeld.Exceptional.DeepWorldCSylow
public import CFSG.Timmesfeld.Exceptional.DeepFixed
public import CFSG.Timmesfeld.Bridge.RootStructTwoLocalKernel

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang

theorem ncard_le_mul_ncard_image {α β : Type*} [Finite α] (s : Set α) (f : α → β) (n : ℕ)
    (hn : ∀ b ∈ f '' s, {a | a ∈ s ∧ f a = b}.ncard ≤ n) : s.ncard ≤ n * (f '' s).ncard := by
  classical
  have := Fintype.ofFinite α
  have hfin : (f '' s).Finite := (Set.toFinite s).image f
  rw [Set.ncard_eq_toFinset_card' s, Set.ncard_eq_toFinset_card _ hfin]
  have e : hfin.toFinset = s.toFinset.image f := by
    ext b
    simp
  rw [e]
  refine Finset.card_le_mul_card_image _ n fun b hb => ?_
  have h := hn b (by simpa using hb)
  rw [Set.ncard_eq_toFinset_card'] at h
  convert h using 2
  ext a
  simp

variable {G : Type*} [Group G] {D : Set G}

theorem commute_conj_iff_of_commute {g a q : G} (hga : Commute g a) :
    Commute a (g * q * g⁻¹) ↔ Commute a q := by
  have := Commute.conj_iff g (a := a) (b := q)
  rwa [hga.eq, mul_inv_cancel_right] at this

theorem mem_normalizer_nCore (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {p g : G}
    (hgp : Commute g p) : g ∈ Subgroup.normalizer (Bridge.nCore D p : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact Bridge.conj_mem_nCore hclass hgp
  · intro hh
    have := Bridge.conj_mem_nCore hclass hgp.inv_left hh
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

theorem commute_zEl_iff {p c : G} {x : Fin 2 → G} (hcfg : LineConfig p c x)
    (hW : ∀ q ∈ offLines D p x, ¬ Commute (zEl p c x) q) {q : G}
    (hq : q ∈ collinearSet D p) : Commute (zEl p c x) q ↔ ∃ i, q = x i ∨ q = p * x i := by
  obtain ⟨hzp, -, hzx, -⟩ := zEl_facts hcfg
  constructor
  · intro hzq
    by_contra hno
    push Not at hno
    exact hW q ⟨hq, hno⟩ hzq
  · rintro ⟨i, rfl | rfl⟩
    · exact hzx i
    · exact hzp.mul_right (hzx i)

namespace FiveLineSetting

variable (S : FiveLineSetting G D)
include S

theorem zEl_ne_one {p c : G} {x : Fin 2 → G} (hp : p ∈ D) (hx : ∀ i, x i ∈ collinearSet D p)
    (h10 : x 1 ≠ x 0) (h10' : x 1 ≠ p * x 0)
    (hW : ∀ q ∈ offLines D p x, ¬ Commute (zEl p c x) q) : zEl p c x ≠ 1 := by
  have := S.finite
  have hcard := ncard_offLines S.root hp hx h10 h10'
  rw [S.ten p hp] at hcard
  obtain ⟨q, hq⟩ : (offLines D p x).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  intro h1
  exact hW q hq (h1 ▸ Commute.one_left q)

end FiveLineSetting

theorem FiveLineSetting.mem_nCore_of_sameLine {G : Type} [Group G] {D : Set G}
    (S : FiveLineSetting G D) {p g : G} (hp : p ∈ D) (hgp : Commute g p)
    (hfix : ∀ q ∈ collinearSet D p, SameLine p q (g * q * g⁻¹)) : g ∈ Bridge.nCore D p := by
  have T := S.twoLocalSetting
  refine (T.fix_rootLines_iff hp (S.ncard_rootLines hp).ge hgp).1 fun L hL => ?_
  obtain ⟨y, hy, hpy, hyp, rfl⟩ := (T.mem_rootLines_iff hp).1 hL
  exact (T.map_line_eq_iff hp hy hpy hyp hgp).2
    (hfix y ((S.mem_collinearSet_iff hp).2 ⟨hy, hpy, hyp⟩))

theorem FiveLineSetting.ncard_four_le {G : Type} [Group G] {D : Set G} (S : FiveLineSetting G D)
    (hWC : ∀ c ∈ D, ∀ p ∈ D, p ∈ nbhd D c 4 → p ∉ nbhd D c 3 → ∀ x : Fin 2 → G,
      (∀ i, x i ∈ collinearSet D p) → (∀ i, x i ∈ nbhd D c 3) → x 1 ≠ x 0 → x 1 ≠ p * x 0 →
      ∀ q ∈ offLines D p x, ¬ Commute (zEl p c x) q)
    {p : G} (hp : p ∈ D) : (nbhd D p 4 \ nbhd D p 3).ncard ≤ 1800 := by
  classical
  have := S.finite
  have hD := S.root
  have hconj : ∀ g : G, ∀ y ∈ D, g * y * g⁻¹ ∈ D := fun g y hy => S.conj g hy
  have hp2 : p * p = 1 := hD.mul_self_eq_one hp
  have hp1 : p ≠ 1 := hD.ne_one hp
  have T := S.twoLocalSetting
  have h5 := S.ncard_rootLines hp
  set Γ := nbhd D p 4 \ nbhd D p 3 with hΓ
  have hsymm : ∀ c ∈ Γ, c ∈ D ∧ p ∈ nbhd D c 4 ∧ p ∉ nbhd D c 3 := fun c hc =>
    ⟨nbhd_subset hp 4 hc.1, mem_nbhd_comm hp hc.1,
      fun h => hc.2 (mem_nbhd_comm (nbhd_subset hp 4 hc.1) h)⟩
  have hex : ∀ c ∈ Γ, ∃ x : Fin 2 → G, (∀ i, x i ∈ collinearSet D p) ∧
      (∀ i, x i ∈ nbhd D c 3) ∧ x 1 ≠ x 0 ∧ x 1 ≠ p * x 0 := fun c hc =>
    exists_two_near S.hclass hD S.noLevi S.noPolar S.noPlane S.p1 (hsymm c hc).1 hp
      (hsymm c hc).2.1 (hsymm c hc).2.2
  choose! x hx hx3 h10 h10' using hex
  have hcfg : ∀ c ∈ Γ, LineConfig p c (x c) := fun c hc =>
    lineConfig_of_two_near S.hclass hD S.noLevi S.noPolar S.noPlane S.p1 (hsymm c hc).1 hp
      (hsymm c hc).2.1 (hsymm c hc).2.2 (hx c hc) (hx3 c hc) (h10 c hc) (h10' c hc)
  have hW : ∀ c ∈ Γ, ∀ q ∈ offLines D p (x c), ¬ Commute (zEl p c (x c)) q := fun c hc =>
    hWC c (hsymm c hc).1 p hp (hsymm c hc).2.1 (hsymm c hc).2.2 (x c) (hx c hc) (hx3 c hc)
      (h10 c hc) (h10' c hc)
  have hz1 : ∀ c ∈ Γ, zEl p c (x c) ≠ 1 := fun c hc =>
    S.zEl_ne_one hp (hx c hc) (h10 c hc) (h10' c hc) (hW c hc)
  have ho3 : ∀ c ∈ Γ, orderOf (zEl p c (x c)) = 3 := fun c hc =>
    orderOf_eq_prime (zEl_facts (hcfg c hc)).2.2.2 (hz1 c hc)
  set Z : G → Subgroup G := fun c => Subgroup.zpowers (zEl p c (x c)) with hZ
  set F : G → Set G := fun c => {q | q ∈ collinearSet D p ∧ Commute (zEl p c (x c)) q}
    with hF_def
  have hfib : ∀ c₀ ∈ Γ, {c | c ∈ Γ ∧ Z c = Z c₀}.ncard ≤ 45 := by
    intro c₀ hc₀
    refine (Set.ncard_le_ncard (fun c hc => ?_) (Set.toFinite _)).trans
      (ncard_lineOrbit_le (hcfg c₀ hc₀) hp1 (hz1 c₀ hc₀))
    obtain ⟨hcΓ, hZc⟩ := hc
    obtain ⟨hcD, hp4, hp3⟩ := hsymm c hcΓ
    have hmem : zEl p c₀ (x c₀) ∈ Z c := by
      rw [hZc]
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hzc : Commute (zEl p c₀ (x c₀)) c := by
      rw [← hk]
      exact (zEl_facts (hcfg c hcΓ)).2.1.zpow_left k
    exact S.mem_lineOrbit_of_far hp (hcfg c₀ hc₀) (hW c₀ hc₀) hcD hp4 hp3 hzc
  have hM : Nat.card (Bridge.nCore D p) = 32 := by
    rw [T.card_nCore hp h5.ge, h5]
    norm_num
  have hsyl : ∀ c₀ ∈ Γ, {Zs | ∃ c ∈ Γ, F c = F c₀ ∧ Zs = Z c}.ncard ≤ 4 := by
    intro c₀ hc₀
    set z₀ := zEl p c₀ (x c₀)
    obtain ⟨hz₀p, -, hz₀x, hz₀3⟩ := zEl_facts (hcfg c₀ hc₀)
    have hxM : ∀ i, x c₀ i ∈ Bridge.nCore D p := fun i =>
      T.mem_nCore_of_mem_collinearSet hp (hx c₀ hc₀ i)
    refine ncard_le_four hM (ho3 c₀ hc₀) (mem_normalizer_nCore S.hclass hz₀p)
      (le_card_closure (hcfg c₀ hc₀) hp1 (hz1 c₀ hc₀)) ?_ ?_ ?_
    · refine Subgroup.closure_le _ |>.2 ?_
      rintro y (rfl | rfl)
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
          (Subgroup.mem_sup_left (Subgroup.mul_mem _ (hxM 0) (hxM 1)))
      · exact Subgroup.mem_sup_left (hxM 0)
    · intro k hk
      have hle : Subgroup.closure ({z₀ * (x c₀ 0 * x c₀ 1), x c₀ 0} : Set G) ≤
          Subgroup.centralizer {z₀} := by
        refine Subgroup.closure_le _ |>.2 ?_
        rintro y (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        · exact ((Commute.refl z₀).mul_right ((hz₀x 0).mul_right (hz₀x 1))).eq.symm
        · exact (hz₀x 0).eq.symm
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hk)
    · rintro Zs ⟨c, hc, hFeq, rfl⟩
      refine ⟨zEl p c (x c), ?_, ho3 c hc, rfl⟩
      set z' := zEl p c (x c)
      obtain ⟨hz'p, -, -, hz'3⟩ := zEl_facts (hcfg c hc)
      have hsame : ∀ q ∈ collinearSet D p, (Commute z' q ↔ Commute z₀ q) := fun q hq => by
        have := Set.ext_iff.1 hFeq q
        simp only [F, Set.mem_ofPred_eq] at this
        exact ⟨fun h => (this.1 ⟨hq, h⟩).2, fun h => (this.2 ⟨hq, h⟩).2⟩
      set O := {q | q ∈ collinearSet D p ∧ ¬ Commute z₀ q} with hO_def
      have hOoff : O = offLines D p (x c₀) := by
        ext q
        simp only [O, offLines, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hq, hnc⟩
          refine ⟨hq, fun i => ⟨fun e => hnc ?_, fun e => hnc ?_⟩⟩
          · rw [e]
            exact hz₀x i
          · rw [e]
            exact hz₀p.mul_right (hz₀x i)
        · rintro ⟨hq, hne⟩
          exact ⟨hq, fun h => hW c₀ hc₀ q ⟨hq, hne⟩ h⟩
      have hO6 : O.ncard = 6 := by
        have := ncard_offLines hD hp (hx c₀ hc₀) (h10 c₀ hc₀) (h10' c₀ hc₀)
        rw [S.ten p hp, ← hOoff] at this
        omega
      have hOp : ∀ q ∈ O, p * q ∈ O := by
        rintro q ⟨hq, hnc⟩
        refine ⟨mul_mem_collinearSet hD hp hq, fun h => hnc ?_⟩
        have := hz₀p.mul_right h
        rwa [← mul_assoc, hp2, one_mul] at this
      have hz₀O : ∀ q ∈ O, z₀ * q * z₀⁻¹ ∈ O := by
        rintro q ⟨hq, hnc⟩
        exact ⟨conj_mem_collinearSet_of_commute hconj hz₀p hq,
          fun h => hnc ((commute_conj_iff_of_commute (Commute.refl z₀)).1 h)⟩
      have hz'O : ∀ q ∈ O, z' * q * z'⁻¹ ∈ O := by
        rintro q ⟨hq, hnc⟩
        have hq' := conj_mem_collinearSet_of_commute hconj hz'p hq
        refine ⟨hq', fun h => hnc ?_⟩
        rw [← hsame _ hq'] at h
        exact (hsame q hq).1 ((commute_conj_iff_of_commute (Commute.refl z')).1 h)
      have hz₀f : ∀ q ∈ O, ¬ Commute z₀ q := fun q hq => hq.2
      have hz'f : ∀ q ∈ O, ¬ Commute z' q := fun q hq h => hq.2 ((hsame q hq.1).1 h)
      obtain ⟨g, hg, hgl⟩ := exists_sameLine hp2 hp1 hz₀p hz'p hz₀3 hz'3 hO6 hOp hz₀O hz'O
        hz₀f hz'f
      have hgp : Commute g p := by
        rcases hg with rfl | rfl
        exacts [hz₀p.inv_left.mul_left hz'p, hz₀p.mul_left hz'p]
      have hgM : g ∈ Bridge.nCore D p := S.mem_nCore_of_sameLine hp hgp fun q hq => by
        by_cases hqO : q ∈ O
        · exact hgl q hqO
        · have h0 : Commute z₀ q := by
            by_contra h
            exact hqO ⟨hq, h⟩
          have h1 : Commute z' q := (hsame q hq).2 h0
          have hgq : Commute g q := by
            rcases hg with rfl | rfl
            exacts [h0.inv_left.mul_left h1, h0.mul_left h1]
          left
          rw [hgq.eq, mul_inv_cancel_right]
      rcases hg with rfl | rfl
      · rw [show z' = z₀ * (z₀⁻¹ * z') by group]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
          (Subgroup.mem_sup_left hgM)
      · rw [show z' = z₀⁻¹ * (z₀ * z') by group]
        exact Subgroup.mul_mem _
          (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)))
          (Subgroup.mem_sup_left hgM)
  obtain ⟨P, hPk, hP, -, hcov⟩ := T.exists_transversal hp
  rw [h5] at hPk
  set U : Finset G → Set G := fun Q => {q | ∃ a ∈ Q, q = a ∨ q = p * a} with hU
  have hline : ∀ a y : G, (y = a ∨ y = p * a) → ∀ q, (q = y ∨ q = p * y) ↔ (q = a ∨ q = p * a) :=
    fun a y hay q => ⟨fun h => sameLine_trans hp2 hay h,
      fun h => sameLine_trans hp2 (sameLine_symm hp2 hay) h⟩
  have hFU : ∀ c ∈ Γ, ∃ Q ∈ P.powersetCard 2, F c = U Q := by
    intro c hc
    have hon : ∀ i, ∃ a ∈ P, x c i = a ∨ x c i = p * a := by
      intro i
      obtain ⟨hxD, hpx, -⟩ := hx c hc i
      have hxp : x c i ≠ p := ne_of_mem_collinearSet hD hp (hx c hc i)
      rcases hcov (x c i) hxD hpx hxp with h | h
      · exact ⟨_, h, Or.inl rfl⟩
      · exact ⟨_, h, Or.inr (by rw [← mul_assoc, hp2, one_mul])⟩
    obtain ⟨a₀, ha₀, e₀⟩ := hon 0
    obtain ⟨a₁, ha₁, e₁⟩ := hon 1
    have hne : a₀ ≠ a₁ := by
      rintro rfl
      rcases e₀ with e₀ | e₀ <;> rcases e₁ with e₁ | e₁
      · exact h10 c hc (e₁.trans e₀.symm)
      · exact h10' c hc (by rw [e₁, e₀])
      · exact h10' c hc (by rw [e₀, e₁, ← mul_assoc, hp2, one_mul])
      · exact h10 c hc (e₁.trans e₀.symm)
    refine ⟨{a₀, a₁}, Finset.mem_powersetCard.2 ⟨?_, Finset.card_pair hne⟩, ?_⟩
    · intro a ha
      rw [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      exacts [ha₀, ha₁]
    · ext q
      constructor
      · rintro ⟨hq, hzq⟩
        obtain ⟨i, hi⟩ := (commute_zEl_iff (hcfg c hc) (hW c hc) hq).1 hzq
        fin_cases i
        · exact ⟨a₀, by simp, (hline a₀ _ e₀ q).1 hi⟩
        · exact ⟨a₁, by simp, (hline a₁ _ e₁ q).1 hi⟩
      · rintro ⟨a, ha, hqa⟩
        rw [Finset.mem_insert, Finset.mem_singleton] at ha
        obtain ⟨i, hi⟩ : ∃ i, q = x c i ∨ q = p * x c i := by
          rcases ha with rfl | rfl
          · exact ⟨0, (hline _ _ e₀ q).2 hqa⟩
          · exact ⟨1, (hline _ _ e₁ q).2 hqa⟩
        have hq : q ∈ collinearSet D p := by
          rcases hi with rfl | rfl
          · exact hx c hc i
          · exact mul_mem_collinearSet hD hp (hx c hc i)
        exact ⟨hq, (commute_zEl_iff (hcfg c hc) (hW c hc) hq).2 ⟨i, hi⟩⟩
  have hF10 : (F '' Γ).ncard ≤ 10 := by
    have hsub : F '' Γ ⊆ ((P.powersetCard 2).image U : Finset (Set G)) := by
      rintro _ ⟨c, hc, rfl⟩
      obtain ⟨Q, hQ, e⟩ := hFU c hc
      rw [e, Finset.mem_coe]
      exact Finset.mem_image_of_mem U hQ
    calc (F '' Γ).ncard
        ≤ (((P.powersetCard 2).image U : Finset (Set G)) : Set (Set G)).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ((P.powersetCard 2).image U).card := Set.ncard_coe_finset _
      _ ≤ (P.powersetCard 2).card := Finset.card_image_le
      _ = 10 := by rw [Finset.card_powersetCard, hPk]; rfl
  have h1 : Γ.ncard ≤ 45 * (Z '' Γ).ncard := ncard_le_mul_ncard_image Γ Z 45 (by
    rintro _ ⟨c₀, hc₀, rfl⟩
    exact hfib c₀ hc₀)
  set Pr : G → Set G × Subgroup G := fun c => (F c, Z c) with hPr
  have h2 : (Z '' Γ).ncard ≤ (Pr '' Γ).ncard := by
    have e : Z '' Γ = Prod.snd '' (Pr '' Γ) := by rw [Set.image_image]
    rw [e]
    exact Set.ncard_image_le (Set.toFinite _)
  have h3 : (Pr '' Γ).ncard ≤ 4 * (Prod.fst '' (Pr '' Γ)).ncard :=
    ncard_le_mul_ncard_image _ Prod.fst 4 (by
      rintro _ ⟨_, ⟨c₀, hc₀, rfl⟩, rfl⟩
      have hfin : {Zs | ∃ c ∈ Γ, F c = F c₀ ∧ Zs = Z c}.Finite :=
        ((Set.toFinite Γ).image Z).subset (by
          rintro _ ⟨c, hc, -, rfl⟩
          exact ⟨c, hc, rfl⟩)
      refine (Set.ncard_le_ncard_of_injOn Prod.snd ?_ ?_ hfin).trans (hsyl c₀ hc₀)
      · rintro _ ⟨⟨c, hc, rfl⟩, hFc⟩
        exact ⟨c, hc, hFc, rfl⟩
      · rintro ⟨a1, b1⟩ ⟨-, hfst1⟩ ⟨a2, b2⟩ ⟨-, hfst2⟩ hsnd
        simp only at hfst1 hfst2 hsnd
        rw [hfst1, hfst2, hsnd])
  have h4 : Prod.fst '' (Pr '' Γ) = F '' Γ := by rw [Set.image_image]
  rw [h4] at h3
  calc Γ.ncard ≤ 45 * (Z '' Γ).ncard := h1
    _ ≤ 45 * (4 * 10) :=
        Nat.mul_le_mul_left _ (h2.trans (h3.trans (Nat.mul_le_mul_left _ hF10)))
    _ = 1800 := by norm_num

end CFSG.Timmesfeld.Moufang.Deep

namespace CFSG.Timmesfeld.Moufang

open Deep

theorem excWorldCInput : ExcWorldCInput := by
  intro G _ D hH hsing hNL hPl hten hW1 _ _ p hp _ _ _ _ _ _ _ _
  have S : FiveLineSetting G D := ⟨hH, hsing, hNL, hPl, hten, hW1⟩
  have hWC : ∀ c ∈ D, ∀ p ∈ D, p ∈ nbhd D c 4 → p ∉ nbhd D c 3 → ∀ x : Fin 2 → G,
      (∀ i, x i ∈ collinearSet D p) → (∀ i, x i ∈ nbhd D c 3) → x 1 ≠ x 0 → x 1 ≠ p * x 0 →
      ∀ q ∈ offLines D p x, ¬ Commute (zEl p c x) q :=
    fun c hc p hp hp4 hp3 x hx hx3 h10 h10' q hq hzq =>
      false_of_commute_offLines S.hclass S.root S.sing S.commLambda S.noLevi S.noPolar S.noPlane
        S.p1 hW1 hc hp hp4 hp3 hx hx3 h10 h10' hq hzq
  have hlow := S.le_ncard_four hp fun w hw3 hw2 => S.exists_far hp hw3 hw2
  have hup := S.ncard_four_le hWC hp
  omega

end CFSG.Timmesfeld.Moufang

module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.Models.PGLSimple
import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut

public section

namespace CFSG.RankThree.PartTwo.Sec20.SimsYKO3

open CFSG
open CFSG.Assembly.RankThreeEven (projSL)

private theorem eq_one_of_isPGroup_range {K H : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    [Group H] (f : K →* H) {p : ℕ} [Fact p.Prime] (hf : IsPGroup p f.range) : f = 1 := by
  by_contra hne
  obtain ⟨k, hk⟩ : ∃ k, f k ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (MonoidHom.ext h)
  have : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have : Nontrivial f.range :=
    ⟨⟨⟨f k, k, rfl⟩, 1, fun h => hk (congrArg Subtype.val h)⟩⟩
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Group.IsNilpotent f.range := hf.isNilpotent
  exact Group.IsPerfect.not_isNilpotent f.range this

private theorem ker_le_of_perfect {X : Type*} [Group X] [Group.IsPerfect X] {N : Subgroup X}
    [N.Normal] (hN : Group.IsSolvable N) (hsimple : IsSimpleGroup (X ⧸ N)) {M : Type*} [Monoid M]
    (ρ : X →* M) (hρ : ∃ x, ρ x ≠ 1) : ρ.ker ≤ N := by
  by_contra hK
  set K := ρ.ker with hKdef
  have hmap : K.map (QuotientGroup.mk' N) = ⊤ := by
    have : (K.map (QuotientGroup.mk' N)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map (QuotientGroup.mk' N)) with h | h
    · exfalso
      apply hK
      intro k hk
      have : (QuotientGroup.mk' N k) ∈ K.map (QuotientGroup.mk' N) := ⟨k, hk, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    · exact h
  let g : N →* X ⧸ K := (QuotientGroup.mk' K).comp N.subtype
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K q
    have hx : QuotientGroup.mk' N x ∈ K.map (QuotientGroup.mk' N) := by
      rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨k, hk, hkx⟩ := hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkx
    refine ⟨⟨k⁻¹ * x, hkx⟩, ?_⟩
    change QuotientGroup.mk' K (k⁻¹ * x) = QuotientGroup.mk' K x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : (k⁻¹ * x)⁻¹ * x = x⁻¹ * k * x⁻¹⁻¹ := by group
    rw [this]
    exact (inferInstance : K.Normal).conj_mem k hk x⁻¹
  have : Group.IsSolvable N := hN
  have hsolv : Group.IsSolvable (X ⧸ K) := Group.isSolvable_of_surjective hg
  have hnt : Nontrivial (X ⧸ K) := by
    obtain ⟨x, hx⟩ := hρ
    refine ⟨⟨QuotientGroup.mk' K x, 1, fun h => hx ?_⟩⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, MonoidHom.mem_ker] at h
    exact h
  exact Group.IsPerfect.not_isSolvable (X ⧸ K) hsolv

theorem card_projSL_two_four : Nat.card (projSL 2 (GaloisField 2 2)) = 60 := by
  rw [Nat.card_congr (CFSG.PGLModel.projSLEquivStatedProj 2 (GaloisField 2 2)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num),
    GaloisField.card 2 2 (by norm_num)]
  decide

theorem sixty_dvd_card_range {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hK : Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 2 (GaloisField 2 2)))
    {H : Type*} [Group H] (f : K →* H) (hf : f ≠ 1) : 60 ∣ Nat.card f.range := by
  obtain ⟨e⟩ := hK
  obtain ⟨k, hk⟩ : ∃ k, f k ≠ 1 := by
    by_contra h
    push Not at h
    exact hf (MonoidHom.ext h)
  have hNsolv : Group.IsSolvable (CFSG.pCore 2 K) := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := K)).isNilpotent
    infer_instance
  have hsimple : IsSimpleGroup (K ⧸ CFSG.pCore 2 K) := by
    have hcard : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
    have : IsSimpleGroup (projSL 2 (GaloisField 2 2)) :=
      CFSG.PGLModel.isSimpleGroup_projSL_of_two_le _ (by norm_num)
        (Or.inr (by rw [hcard]; norm_num)) (Or.inr (by rw [hcard]; norm_num))
    exact e.isSimpleGroup
  have hker : f.ker ≤ CFSG.pCore 2 K :=
    ker_le_of_perfect hNsolv hsimple f ⟨k, hk⟩
  have h60K : 60 ∣ Nat.card (K ⧸ CFSG.pCore 2 K) := by
    rw [Nat.card_congr e.toEquiv, card_projSL_two_four]
  have h60ker : 60 ∣ f.ker.index :=
    h60K.trans (by rw [← Subgroup.index_eq_card]; exact Subgroup.index_dvd_of_le hker)
  rwa [Subgroup.index_ker] at h60ker

theorem eq_one_of_not_five_dvd {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hK : Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 2 (GaloisField 2 2)))
    {H : Type*} [Group H] [Finite H] (h5 : ¬ 5 ∣ Nat.card H) (f : K →* H) : f = 1 := by
  by_contra hf
  exact h5 ((dvd_trans (by norm_num : 5 ∣ 60) (sixty_dvd_card_range hK f hf)).trans
    (Subgroup.card_subgroup_dvd_card f.range))

theorem exists_pow_five_pow_eq_one {K : Type*} [Group K] [Finite K] {H : Type*} [Group H]
    (f : K →* H) (h5 : 5 ∣ Nat.card f.range) : ∃ k : K, f k ≠ 1 ∧ ∃ a : ℕ, k ^ (5 ^ a) = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 h5
  obtain ⟨k₀, hk₀⟩ := f.rangeRestrict_surjective y
  obtain ⟨a, m, hm5, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos k₀).ne' 5 (by norm_num)
  refine ⟨k₀ ^ m, fun h => hm5 ?_, a, ?_⟩
  · have h1 : y ^ m = 1 := by
      rw [← hk₀, ← map_pow]
      exact Subtype.ext h
    rw [← hy]
    exact orderOf_dvd_of_pow_eq_one h1
  · rw [← pow_mul, mul_comm, ← hm]
    exact pow_orderOf_eq_one k₀

private theorem eq_one_of_forall_commute {K H : Type*} [Group K] [Group.IsPerfect K] [Group H]
    (f : K →* H) (h : ∀ a b : K, f a * f b = f b * f a) : f = 1 := by
  have hle : commutator K ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h a b
  rw [Group.IsPerfect.commutator_eq_top] at hle
  exact MonoidHom.ext fun g => MonoidHom.mem_ker.mp (hle (Subgroup.mem_top g))

theorem eq_one_of_isCyclic {K : Type*} [Group K] [Group.IsPerfect K] {E : Type*} [Group E]
    [IsCyclic E] (κ : K →* MulAut E) : κ = 1 := by
  refine eq_one_of_forall_commute κ fun a b => ?_
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (κ a).toMonoidHom
  obtain ⟨n, hn⟩ := MonoidHom.map_cyclic (κ b).toMonoidHom
  ext g
  rw [MulAut.mul_apply, MulAut.mul_apply]
  change κ a (κ b g) = κ b (κ a g)
  have hm' : ∀ g, κ a g = g ^ m := hm
  have hn' : ∀ g, κ b g = g ^ n := hn
  rw [hn', hm', hm', hn', ← zpow_mul, ← zpow_mul, mul_comm]

private def restrictAct {K Y : Type*} [Group K] [Group Y] (ρ : K →* MulAut Y) (X : Subgroup Y)
    (hX : ∀ k : K, ∀ x ∈ X, ρ k x ∈ X) : K →* MulAut X where
  toFun k :=
    { toFun := fun x => ⟨ρ k x, hX k x x.2⟩
      invFun := fun x => ⟨ρ k⁻¹ x, hX k⁻¹ x x.2⟩
      left_inv := fun x => Subtype.ext (by
        change (ρ k⁻¹) ((ρ k) x) = x
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun x => Subtype.ext (by
        change (ρ k) ((ρ k⁻¹) x) = x
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun x y => Subtype.ext (map_mul (ρ k) (x : Y) (y : Y)) }
  map_one' := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    change ρ 1 x = x
    rw [map_one, MulAut.one_apply]
  map_mul' a b := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    change ρ (a * b) x = ρ a (ρ b x)
    rw [map_mul, MulAut.mul_apply]

private theorem apply_eq_of_restrictAct_eq_one {K Y : Type*} [Group K] [Group Y]
    (ρ : K →* MulAut Y) (X : Subgroup Y) (hX : ∀ k : K, ∀ x ∈ X, ρ k x ∈ X)
    (h : restrictAct ρ X hX = 1) (k : K) {x : Y} (hx : x ∈ X) : ρ k x = x := by
  have := congrArg (fun g : K →* MulAut X => ((g k ⟨x, hx⟩ : X) : Y)) h
  exact this

private theorem map_eq_of_invariant {K Y : Type*} [Group K] [Group Y] (ρ : K →* MulAut Y)
    (X : Subgroup Y) (hX : ∀ k : K, ∀ x ∈ X, ρ k x ∈ X) (k : K) :
    X.map (ρ k).toMonoidHom = X := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hX k x hx
  · intro x hx
    refine ⟨ρ k⁻¹ x, hX k⁻¹ x hx, ?_⟩
    change (ρ k) ((ρ k⁻¹) x) = x
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

private def quotAct {K Y : Type*} [Group K] [Group Y] (ρ : K →* MulAut Y) (X : Subgroup Y)
    [X.Normal] (hX : ∀ k : K, ∀ x ∈ X, ρ k x ∈ X) : K →* MulAut (Y ⧸ X) where
  toFun k := QuotientGroup.congr X X (ρ k) (map_eq_of_invariant ρ X hX k)
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    change ((ρ 1 x : Y) : Y ⧸ X) = x
    rw [map_one, MulAut.one_apply]
  map_mul' a b := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    change ((ρ (a * b) x : Y) : Y ⧸ X) = ((ρ a (ρ b x) : Y) : Y ⧸ X)
    rw [map_mul, MulAut.mul_apply]

variable {E : Type*} [Group E] [Finite E]

theorem eq_bot_or_eq_top_of_invariant {K : Type*} [Group K] [Group.IsPerfect K]
    (hEc : ∀ a b : E, a * b = b * a) (hE5 : ∀ a : E, a ^ 5 = 1) (hE25 : Nat.card E = 25)
    (κ : K →* MulAut E) (hκ : κ ≠ 1)
    (X : Subgroup E) (hX : ∀ k : K, ∀ x ∈ X, κ k x ∈ X) : X = ⊥ ∨ X = ⊤ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hbot, htop⟩ := hcon
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcardX : Nat.card X = 5 := by
    have hdvd : Nat.card X ∣ 5 ^ 2 := by
      have := Subgroup.card_subgroup_dvd_card X
      rwa [hE25] at this
    obtain ⟨i, hi, hXi⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 hdvd
    interval_cases i
    · exact absurd (Subgroup.eq_bot_of_card_eq X (by simpa using hXi)) hbot
    · simpa using hXi
    · exact absurd ((Subgroup.card_eq_iff_eq_top X).1 (by rw [hXi, hE25]; norm_num)) htop
  haveI : X.Normal := ⟨fun n hn g => by rw [hEc g n, mul_inv_cancel_right]; exact hn⟩
  have hcardQ : Nat.card (E ⧸ X) = 5 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup X
    rw [hE25, hcardX] at h
    omega
  haveI : IsCyclic X := isCyclic_of_prime_card hcardX
  haveI : IsCyclic (E ⧸ X) := isCyclic_of_prime_card hcardQ
  have h1 := eq_one_of_isCyclic (restrictAct κ X hX)
  have h2 := eq_one_of_isCyclic (quotAct κ X hX)
  have hfix : ∀ k : K, ∀ x ∈ X, κ k x = x := fun k x hx =>
    apply_eq_of_restrictAct_eq_one κ X hX h1 k hx
  have hquot : ∀ k : K, ∀ v : E, v⁻¹ * κ k v ∈ X := by
    intro k v
    have := congrArg (fun g : K →* MulAut (E ⧸ X) => (g k) (v : E ⧸ X)) h2
    exact QuotientGroup.eq.1 this.symm
  apply hκ
  refine eq_one_of_forall_commute κ fun a b => MulEquiv.ext fun v => ?_
  change κ a (κ b v) = κ b (κ a v)
  have e1 : κ a (κ b v) = κ a v * (v⁻¹ * κ b v) := by
    conv_lhs => rw [show κ b v = v * (v⁻¹ * κ b v) by group]
    rw [map_mul, hfix a _ (hquot b v)]
  have e2 : κ b (κ a v) = κ b v * (v⁻¹ * κ a v) := by
    conv_lhs => rw [show κ a v = v * (v⁻¹ * κ a v) by group]
    rw [map_mul, hfix b _ (hquot a v)]
  rw [e1, e2, hEc v⁻¹ (κ b v), hEc v⁻¹ (κ a v), ← mul_assoc, ← mul_assoc,
    hEc (κ a v) (κ b v)]

private theorem not_five_dvd_card_mulAut {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (h8 : Nat.card P ∣ 8) : ¬ 5 ∣ Nat.card (MulAut P) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 P) := ⟨hP⟩
  have hel : CFSG.IsElementaryAbelian 2 (P ⧸ frattini P) :=
    CFSG.isElementaryAbelian_quotient_frattini
  obtain ⟨n, hn⟩ := (hP.to_quotient (frattini P)).exists_card_eq
  have hn3 : n ≤ 3 := by
    by_contra hlt
    have h1 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ n ≤ 8 := by
      rw [← hn]
      exact Nat.le_of_dvd (by norm_num) ((Subgroup.card_quotient_dvd_card (frattini P)).trans h8)
    omega
  have hexp : ∀ x : P ⧸ frattini P, x ^ 2 = 1 := fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hel.exponent_dvd_p x
  obtain ⟨e⟩ := SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (fun a b => hel.toIsMulCommutative.is_comm.comm a b) hexp hn
  have h5 : ¬ 5 ∣ Nat.card (MulAut (P ⧸ frattini P)) := by
    rw [SectionRank.Ccomm.card_mulAut_eq_card_GL e, SectionRank.Ccomm.card_GL_zmod]
    interval_cases n <;> decide
  obtain ⟨m, hm⟩ := (SectionRank.Ccomm.isPGroup_ker_autQuotient_frattini hP).exists_card_eq
  have hcard := (SectionRank.Ccomm.autQuotient (frattini P)).ker.index_mul_card
  rw [Subgroup.index_ker, hm] at hcard
  rw [← hcard]
  intro h
  rcases (Nat.Prime.dvd_mul (by norm_num)).1 h with h | h
  · exact h5 (h.trans (Subgroup.card_subgroup_dvd_card _))
  · exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h) (by norm_num)

private theorem card_dvd_eight {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hK : Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 2 (GaloisField 2 2)))
    (hEc : ∀ a b : E, a * b = b * a) (hE5 : ∀ a : E, a ^ 5 = 1) (hE25 : Nat.card E = 25)
    (κ : K →* MulAut E) (hκ : κ ≠ 1)
    (N₀ : Subgroup (MulAut E)) (hN₀2 : IsPGroup 2 N₀) (hN₀K : N₀ ≤ κ.range)
    (hN₀n : ∀ k : K, ∀ n ∈ N₀, κ k * n * (κ k)⁻¹ ∈ N₀) : Nat.card N₀ ∣ 8 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h480 : Nat.card (MulAut E) = 480 := by
    obtain ⟨e⟩ := SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hEc hE5 (n := 2)
      (by rw [hE25]; norm_num)
    rw [SectionRank.Ccomm.card_mulAut_eq_card_GL e, SectionRank.Ccomm.card_GL_zmod]
    decide
  let N' : Subgroup κ.range := N₀.subgroupOf κ.range
  haveI : N'.Normal := ⟨fun n hn g => by
    obtain ⟨k, hk⟩ := g.2
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hk]
    exact hN₀n k _ hn⟩
  let φ : K →* κ.range ⧸ N' := (QuotientGroup.mk' N').comp κ.rangeRestrict
  have hφ : φ ≠ 1 := by
    intro h
    apply hκ
    have hle : κ.range ≤ N₀ := by
      rintro _ ⟨k, rfl⟩
      have := DFunLike.congr_fun h k
      simpa [φ, N', QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] using this
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact eq_one_of_isPGroup_range κ (hN₀2.to_le hle)
  have h60 : 60 ∣ Nat.card (κ.range ⧸ N') :=
    (sixty_dvd_card_range hK φ hφ).trans (Subgroup.card_subgroup_dvd_card _)
  have hcardR : Nat.card κ.range = Nat.card (κ.range ⧸ N') * Nat.card N' :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N'
  have hN'card : Nat.card N' = Nat.card N₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀K).toEquiv
  have hdvd : Nat.card κ.range ∣ 480 := h480 ▸ Subgroup.card_subgroup_dvd_card κ.range
  obtain ⟨c, hc⟩ := h60
  rw [hcardR, hc, hN'card] at hdvd
  have h8 : c * Nat.card N₀ ∣ 8 := by
    refine Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 60) ?_
    convert hdvd using 1
    ring
  exact (Dvd.intro_left c rfl).trans h8

theorem eq_one_or_eq_inv_of_comm {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hK : Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 2 (GaloisField 2 2)))
    (hEc : ∀ a b : E, a * b = b * a) (hE5 : ∀ a : E, a ^ 5 = 1) (hE25 : Nat.card E = 25)
    (κ : K →* MulAut E) (hκ : κ ≠ 1)
    (N₀ : Subgroup (MulAut E)) (hN₀2 : IsPGroup 2 N₀) (hN₀K : N₀ ≤ κ.range)
    (hN₀n : ∀ k : K, ∀ n ∈ N₀, κ k * n * (κ k)⁻¹ ∈ N₀)
    (t : MulAut E) (ht : t * t = 1) (htK : ∀ k : K, t * κ k * t⁻¹ * (κ k)⁻¹ ∈ N₀) :
    t = 1 ∨ ∀ v : E, t v = v⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψ : restrictAct ((MulAut.conj : MulAut E →* MulAut (MulAut E)).comp κ) N₀
      (fun k n hn => hN₀n k n hn) = 1 :=
    eq_one_of_not_five_dvd hK (not_five_dvd_card_mulAut hN₀2
      (card_dvd_eight hK hEc hE5 hE25 κ hκ N₀ hN₀2 hN₀K hN₀n)) _
  have hcent : ∀ k : K, ∀ n ∈ N₀, κ k * n * (κ k)⁻¹ = n := fun k n hn =>
    apply_eq_of_restrictAct_eq_one ((MulAut.conj : MulAut E →* MulAut (MulAut E)).comp κ) N₀
      (fun k n hn => hN₀n k n hn) hψ k hn
  let f : K →* N₀ :=
    { toFun := fun k => ⟨t * κ k * t⁻¹ * (κ k)⁻¹, htK k⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have h := hcent a _ (htK b)
        change t * κ (a * b) * t⁻¹ * (κ (a * b))⁻¹ =
          (t * κ a * t⁻¹ * (κ a)⁻¹) * (t * κ b * t⁻¹ * (κ b)⁻¹)
        calc t * κ (a * b) * t⁻¹ * (κ (a * b))⁻¹
            = (t * κ a * t⁻¹ * (κ a)⁻¹) * (κ a * (t * κ b * t⁻¹ * (κ b)⁻¹) * (κ a)⁻¹) := by
              rw [map_mul]; group
          _ = _ := by rw [h]) }
  have hf : f = 1 := eq_one_of_isPGroup_range f (p := 2) (hN₀2.to_subgroup f.range)
  have htc : ∀ k : K, t * κ k = κ k * t := fun k => by
    have h1 : t * κ k * t⁻¹ * (κ k)⁻¹ = 1 := congrArg Subtype.val (DFunLike.congr_fun hf k)
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  have htt : ∀ v : E, t (t v) = v := fun v => by
    have := congrArg (fun s : MulAut E => s v) ht
    simpa using this
  let X : Subgroup E :=
    { carrier := {v | t v = v}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      one_mem' := map_one t
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv, ha] }
  have hXinv : ∀ k : K, ∀ x ∈ X, κ k x ∈ X := by
    intro k x hx
    change t (κ k x) = κ k x
    have hx' : t x = x := hx
    calc t (κ k x) = (t * κ k) x := rfl
      _ = (κ k * t) x := by rw [htc k]
      _ = κ k x := by rw [MulAut.mul_apply, hx']
  rcases eq_bot_or_eq_top_of_invariant hEc hE5 hE25 κ hκ X hXinv with hX | hX
  · right
    intro v
    have hw : v * t v ∈ X := by
      change t (v * t v) = v * t v
      rw [map_mul, htt, hEc]
    rw [hX, Subgroup.mem_bot] at hw
    exact eq_inv_of_mul_eq_one_right hw
  · left
    ext v
    have : v ∈ X := hX ▸ Subgroup.mem_top v
    exact this

end CFSG.RankThree.PartTwo.Sec20.SimsYKO3

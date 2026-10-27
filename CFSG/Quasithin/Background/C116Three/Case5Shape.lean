module

public import CFSG.Quasithin.Background.C116Three.L3Pair

import CFSG.Quasithin.Vol2.KGFactC31E8
import CFSG.Quasithin.H13.NQRigidWMGroups
import CFSG.Quasithin.Background.G64RealizeSec
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.EmptyFaithful.R3c23PairAFac

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] [Finite V]

private theorem commV_map_mem {K K' : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) {b : MulAut V} (hb : b ∈ K') {w : V}
    (hw : w ∈ commV K) : b w ∈ commV K := by
  unfold commV at hw ⊢
  induction hw using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨x, hx, v, rfl⟩ := hz
    have hc : b (x v) = x (b v) := by
      have h := congrArg (fun φ : MulAut V => φ v) (hcomm x hx b hb)
      simp only [MulAut.mul_apply] at h
      exact h.symm
    rw [map_mul, map_inv, hc]
    exact Subgroup.subset_closure ⟨x, hx, b v, rfl⟩
  | one => simp
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  | inv y _ hy => rw [map_inv]; exact inv_mem hy

private theorem fixer_of_inter {K K' : Subgroup (MulAut V)}
    (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) (hint : commV K ⊓ commV K' = ⊥) :
    ∀ b ∈ K', ∀ w ∈ commV K, b w = w := by
  intro b hb w hw
  have h1 : b w * w⁻¹ ∈ commV K' := Subgroup.subset_closure ⟨b, hb, w, rfl⟩
  have h2 : b w * w⁻¹ ∈ commV K := mul_mem (commV_map_mem hcomm hb hw) (inv_mem hw)
  have h3 : b w * w⁻¹ ∈ commV K ⊓ commV K' := ⟨h2, h1⟩
  rw [hint, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.1 h3

private theorem commV_map_mem_of_normalizes {K : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ x ∈ K, g * x * g⁻¹ ∈ K) {w : V} (hw : w ∈ commV K) : g w ∈ commV K := by
  unfold commV at hw ⊢
  induction hw using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨x, hx, v, rfl⟩ := hz
    have hc : g (x v) = (g * x * g⁻¹) (g v) := by simp [MulAut.mul_apply]
    rw [map_mul, map_inv, hc]
    exact Subgroup.subset_closure ⟨_, hg x hx, g v, rfl⟩
  | one => simp
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  | inv y _ hy => rw [map_inv]; exact inv_mem hy

private theorem comm_of_act_trivial {K : Subgroup (MulAut V)}
    (htriv : ∀ g ∈ K, ∀ y ∈ commV K, g y = y) : ∀ g ∈ K, ∀ h ∈ K, g * h = h * g := by
  intro g hg h hh
  ext u
  simp only [MulAut.mul_apply]
  have hp : h u * u⁻¹ ∈ commV K := Subgroup.subset_closure ⟨h, hh, u, rfl⟩
  have hq : g u * u⁻¹ ∈ commV K := Subgroup.subset_closure ⟨g, hg, u, rfl⟩
  have e1 : g (h u) = (h u * u⁻¹) * g u := by
    calc g (h u) = g ((h u * u⁻¹) * u) := congrArg g (inv_mul_cancel_right _ _).symm
      _ = (h u * u⁻¹) * g u := by rw [map_mul, htriv g hg _ hp]
  have e2 : h (g u) = (g u * u⁻¹) * h u := by
    calc h (g u) = h ((g u * u⁻¹) * u) := congrArg h (inv_mul_cancel_right _ _).symm
      _ = (g u * u⁻¹) * h u := by rw [map_mul, htriv h hh _ hq]
  rw [e1, e2]
  ac_rfl

private theorem false_of_comm_of_card {G : Type*} [Group G] [IsSimpleGroup G] [Finite G]
    (hG : Nat.card G = 168) (hcomm : ∀ g h : G, g * h = h * g) : False := by
  haveI : Fintype G := Fintype.ofFinite G
  have hdvd : 2 ∣ Fintype.card G := by
    rw [← Nat.card_eq_fintype_card, hG]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 hdvd
  haveI : (Subgroup.zpowers x).Normal :=
    ⟨fun n hn g => by
      have e : g * n * g⁻¹ = n := by rw [hcomm g n, mul_inv_cancel_right]
      rw [e]; exact hn⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.zpowers x) with h | h
  · have hx1 : x = 1 := by
      have hmem : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
      rw [h] at hmem
      exact Subgroup.mem_bot.1 hmem
    rw [hx1, orderOf_one] at hx
    norm_num at hx
  · have h2 : Nat.card (Subgroup.zpowers x) = Nat.card G := by rw [h, Subgroup.card_top]
    rw [Nat.card_zpowers, hx, hG] at h2
    norm_num at h2

private def fixFreeSet (K : Subgroup (MulAut V)) (w : V) : Set V :=
  {x | x ∈ commV K ∧ x ≠ 1 ∧ x ≠ w}

private theorem fixFreeSet_ncard {K : Subgroup (MulAut V)} {w : V}
    (hcard : Nat.card ↥(commV K) = 2 ^ 3) (hw : w ∈ commV K) (hw1 : w ≠ 1) :
    Nat.card ↥(fixFreeSet K w) = 6 := by
  have h1 : fixFreeSet K w = (commV K : Set V) \ {1, w} := by
    ext x; simp [fixFreeSet, and_assoc]
  have h2 : ({1, w} : Set V) ⊆ (commV K : Set V) :=
    Set.insert_subset_iff.2 ⟨(commV K).one_mem, Set.singleton_subset_iff.2 hw⟩
  have h3 : (commV K : Set V).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]; simpa using hcard
  rw [Nat.card_coe_set_eq, h1, Set.ncard_sdiff h2, h3, Set.ncard_pair (Ne.symm hw1)]

private theorem act_trivial_of_fixed {K : Subgroup (MulAut V)} [IsSimpleGroup ↥K]
    (hKc : Nat.card ↥K = 168) (hcard : Nat.card ↥(commV K) = 2 ^ 3) {w : V} (hw : w ∈ commV K)
    (hw1 : w ≠ 1) (hfix : ∀ g ∈ K, g w = w) : ∀ g ∈ K, ∀ y ∈ commV K, g y = y := by
  have hact : ∀ g ∈ K, ∀ x ∈ fixFreeSet K w, (g : MulAut V) x ∈ fixFreeSet K w := by
    intro g hg x hx
    obtain ⟨hx1, hx2, hx3⟩ := hx
    refine ⟨commV_map_mem_of_normalizes
      (fun y hy => K.mul_mem (K.mul_mem hg hy) (K.inv_mem hg)) hx1, ?_, ?_⟩
    · intro h
      apply hx2
      exact (g : MulAut V).injective (by rw [h, map_one])
    · intro h
      apply hx3
      apply (g : MulAut V).injective
      rw [h, hfix g hg]
  letI : MulAction K ↥(fixFreeSet K w) :=
    { smul := fun g x => ⟨(g : MulAut V) x.1, hact g g.2 x.1 x.2⟩
      one_smul := fun x => Subtype.ext rfl
      mul_smul := fun g h x => Subtype.ext rfl }
  have hfin : Nat.card ↥(fixFreeSet K w) = 6 := fixFreeSet_ncard hcard hw hw1
  rcases Subgroup.Normal.eq_bot_or_eq_top
    (MulAction.toPermHom K ↥(fixFreeSet K w)).ker with h | h
  · exfalso
    have hinj := (MonoidHom.ker_eq_bot_iff _).1 h
    have hdvd := Subgroup.card_dvd_of_injective _ hinj
    rw [hKc, Nat.card_perm, hfin] at hdvd
    norm_num [Nat.factorial] at hdvd
  · intro g hg y hy
    have hk : (⟨g, hg⟩ : K) ∈ (MulAction.toPermHom K ↥(fixFreeSet K w)).ker := by
      rw [h]; exact Subgroup.mem_top _
    have hperm := MonoidHom.mem_ker.1 hk
    have hact1 : ∀ x : ↥(fixFreeSet K w), (⟨g, hg⟩ : K) • x = x := fun x => by
      have := congrArg (fun σ : Equiv.Perm ↥(fixFreeSet K w) => σ x) hperm
      exact this
    by_cases h1 : y = 1
    · subst h1; exact map_one (g : MulAut V)
    by_cases h2 : y = w
    · subst h2; exact hfix g hg
    have hy' : y ∈ fixFreeSet K w := ⟨hy, h1, h2⟩
    have := congrArg Subtype.val (hact1 ⟨y, hy'⟩)
    exact this

private theorem no_fixed_of_SL3 {K : Subgroup (MulAut V)}
    (hK : Nonempty (↥K ≃* ↥(StatedSL 3 (ZMod 2)))) (hcard : Nat.card ↥(commV K) = 2 ^ 3)
    {w : V} (hw : w ∈ commV K) (hfix : ∀ g ∈ K, g w = w) : w = 1 := by
  by_contra hw1
  obtain ⟨e⟩ := hK
  haveI : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) :=
    CFSG.Quasithin.KGC31.E8.isSimpleGroup_statedSL3
  haveI : IsSimpleGroup ↥K := e.isSimpleGroup
  haveI : Finite ↥K := Finite.of_equiv _ e.toEquiv.symm
  have hKc : Nat.card ↥K = 168 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three_zmod_two]
  have htriv := act_trivial_of_fixed hKc hcard hw hw1 hfix
  exact false_of_comm_of_card hKc
    (fun g h => Subtype.ext (comm_of_act_trivial htriv g.1 g.2 h.1 h.2))

private theorem eq_of_le_simple {K L : Subgroup (MulAut V)} [IsSimpleGroup ↥K] (hLK : L ≤ K)
    (hLn : ∀ x ∈ K, ∀ l ∈ L, x * l * x⁻¹ ∈ L) (hL : L ≠ ⊥) : L = K := by
  haveI : (L.subgroupOf K).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hLn _ g.2 _ hn⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top (L.subgroupOf K) with h | h
  · exfalso
    apply hL
    rw [eq_bot_iff]
    intro x hx
    have hxK : x ∈ K := hLK hx
    have hm : (⟨x, hxK⟩ : ↥K) ∈ L.subgroupOf K := Subgroup.mem_subgroupOf.2 hx
    rw [h, Subgroup.mem_bot] at hm
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hm
  · exact le_antisymm hLK (Subgroup.subgroupOf_eq_top.1 h)

private theorem ne_bot_of_quasisimple {L : Subgroup (MulAut V)} (hq : CFSG.IsQuasisimple ↥L) :
    L ≠ ⊥ := by
  rintro rfl
  obtain ⟨a, b, hab⟩ := hq.2.2
  apply hab
  have hs : ∀ x : (↥(⊥ : Subgroup (MulAut V)) ⧸ Subgroup.center ↥(⊥ : Subgroup (MulAut V))),
      x = 1 := by
    intro x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    have hq1 : q = 1 := Subtype.ext (Subgroup.mem_bot.1 q.2)
    rw [hq1]
    rfl
  rw [hs a, hs b]

private theorem c5_conj_part {X L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (hconj : L₂ = L₁.map (MulAut.conj τ).toMonoidHom)
    (hτN : τ ∈ Subgroup.normalizer (ffJ X : Set (MulAut V)))
    (hL₁J : L₁ ≤ ffJ X) (hn₁ : ∀ x ∈ ffJ X, ∀ k ∈ L₁, x * k * x⁻¹ ∈ L₁) :
    L₂ ≤ ffJ X ∧ ∀ x ∈ ffJ X, ∀ k ∈ L₂, x * k * x⁻¹ ∈ L₂ := by
  have hfw : ∀ g ∈ ffJ X, τ * g * τ⁻¹ ∈ ffJ X := fun g hg =>
    (Subgroup.mem_normalizer_iff.mp hτN g).mp hg
  have hbk : ∀ g ∈ ffJ X, τ⁻¹ * g * τ ∈ ffJ X := fun g hg => by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hτN) g).mp hg
    rwa [inv_inv] at h
  have hmem : ∀ k ∈ L₂, ∃ a ∈ L₁, τ * a * τ⁻¹ = k := by
    intro k hk
    rw [hconj, Subgroup.mem_map] at hk
    obtain ⟨a, ha, hak⟩ := hk
    exact ⟨a, ha, hak⟩
  refine ⟨?_, ?_⟩
  · intro k hk
    obtain ⟨a, ha, rfl⟩ := hmem k hk
    exact hfw a (hL₁J ha)
  · intro x hx k hk
    obtain ⟨a, ha, rfl⟩ := hmem k hk
    have hy : τ⁻¹ * x * τ * a * (τ⁻¹ * x * τ)⁻¹ ∈ L₁ := hn₁ (τ⁻¹ * x * τ) (hbk x hx) a ha
    have e : x * (τ * a * τ⁻¹) * x⁻¹ = τ * (τ⁻¹ * x * τ * a * (τ⁻¹ * x * τ)⁻¹) * τ⁻¹ := by
      group
    rw [e, hconj]
    exact Subgroup.mem_map_of_mem (MulAut.conj τ).toMonoidHom hy

private theorem c5_false_of_card_six {G L : Subgroup (MulAut V)} (hG : Nat.card ↥G = 6)
    (hLG : L ≤ G) (hq : CFSG.IsQuasisimple ↥L) : False := by
  haveI : Group.IsSolvable ↥G := twoG_isSolvable_of_card_six hG
  have hsol : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLG)
      (Subgroup.inclusion_injective hLG)
  haveI : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr (ne_bot_of_quasisimple hq)
  haveI : Group.IsPerfect ↥L := hq.1
  exact Group.IsPerfect.not_isSolvable ↥L hsol

private theorem c5_sub {A₂ L : Subgroup (MulAut V)} (hLA : L ≤ A₂)
    (hn : ∀ x ∈ A₂, ∀ k ∈ L, x * k * x⁻¹ ∈ L) (hq : CFSG.IsQuasisimple ↥L)
    (hA₂ : (Nonempty (↥A₂ ≃* ↥(StatedSL 3 (ZMod 2))) ∧ ∃ k : ℕ, k ≤ 2 ∧
        DirectSumOfCopies A₂ (commV A₂) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) k) ∨
      ∃ n, BinaryNaturalSL A₂ (commV A₂) (fixV A₂ ⊓ commV A₂) 2 n) : L = A₂ := by
  rcases hA₂ with ⟨⟨e⟩, -⟩ | ⟨n, K, hF, hFin, hK, π, hπ⟩
  · haveI : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) :=
      CFSG.Quasithin.KGC31.E8.isSimpleGroup_statedSL3
    haveI : IsSimpleGroup ↥A₂ := e.isSimpleGroup
    exact eq_of_le_simple hLA hn (ne_bot_of_quasisimple hq)
  · have hinj : Function.Injective π :=
      G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    let e : ↥A₂ ≃* ↥(StatedSL 2 K) := (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm
    have hn2 : 2 ≤ n := by
      by_contra hlt
      push Not at hlt
      interval_cases n
      · exfalso
        have := Finite.one_lt_card (α := K)
        rw [pow_zero] at hK
        omega
      · have h6 : Nat.card ↥A₂ = 6 := by
          rw [Nat.card_congr e.toEquiv, twoG_card_statedSL_two, hK]
          norm_num
        exact (c5_false_of_card_six h6 hLA hq).elim
    haveI := twoG_charP_two hK
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    haveI := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
    haveI : IsSimpleGroup ↥A₂ := e.isSimpleGroup
    exact eq_of_le_simple hLA hn (ne_bot_of_quasisimple hq)

theorem case5_shape (hV : ∀ v : V, v ^ 2 = 1) {X L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}
    (P : JPair X L₁ L₂ τ) (h5 : B56Case5 (ffJ X)) : Case5Out X L₁ L₂ := by
  obtain ⟨A₁, A₂, hsup, hdisj, hcomm, ⟨hsumC, hintC⟩, ⟨e₁⟩, hcard₁, -, hA₂⟩ := h5
  haveI : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) :=
    CFSG.Quasithin.KGC31.E8.isSimpleGroup_statedSL3
  haveI : IsSimpleGroup ↥A₁ := e₁.isSimpleGroup
  have hτN : τ ∈ Subgroup.normalizer (ffJ X : Set (MulAut V)) :=
    CFSG.Quasithin.B6.le_normalizer_ffJ X P.τ_mem
  have hn₁ : ∀ x ∈ ffJ X, ∀ k ∈ L₁, x * k * x⁻¹ ∈ L₁ :=
    fun x hx k hk => (Subgroup.mem_normalizer_iff.mp (P.Jn x hx) k).mp hk
  obtain ⟨hL₂J, hn₂⟩ := c5_conj_part P.conj hτN P.L₁J hn₁
  have hA₁J : A₁ ≤ ffJ X := by rw [← hsup]; exact le_sup_left
  have hA₂J : A₂ ≤ ffJ X := by rw [← hsup]; exact le_sup_right
  have hLa : L₁ ≤ A₁ ∨ L₁ ≤ A₂ :=
    CFSG.Quasithin.InternalSec.le_or_le_of_sup_eq hsup hcomm P.L₁J hn₁ P.q₁
  have hLb : L₂ ≤ A₁ ∨ L₂ ≤ A₂ :=
    CFSG.Quasithin.InternalSec.le_or_le_of_sup_eq hsup hcomm hL₂J hn₂ P.q₂
  have hcommV : Nat.card ↥(commV L₂) = Nat.card ↥(commV L₁) := by
    rw [← commV_map_conj P.conj]
    exact Subgroup.card_map_of_injective τ.injective
  let ec : ↥L₁ ≃* ↥L₂ :=
    (Subgroup.equivMapOfInjective L₁ (MulAut.conj τ).toMonoidHom (MulAut.conj τ).injective).trans
      (MulEquiv.subgroupCongr P.conj.symm)
  have hn₁A₁ : ∀ x ∈ A₁, ∀ k ∈ L₁, x * k * x⁻¹ ∈ L₁ := fun x hx k hk => hn₁ x (hA₁J hx) k hk
  have hn₂A₁ : ∀ x ∈ A₁, ∀ k ∈ L₂, x * k * x⁻¹ ∈ L₂ := fun x hx k hk => hn₂ x (hA₁J hx) k hk
  have hn₁A₂ : ∀ x ∈ A₂, ∀ k ∈ L₁, x * k * x⁻¹ ∈ L₁ := fun x hx k hk => hn₁ x (hA₂J hx) k hk
  have hn₂A₂ : ∀ x ∈ A₂, ∀ k ∈ L₂, x * k * x⁻¹ ∈ L₂ := fun x hx k hk => hn₂ x (hA₂J hx) k hk
  have hcontra : L₁ = L₂ → False := fun h =>
    CFSG.Quasithin.InternalSec.not_commute_of_isQuasisimple P.q₁
      (fun a ha b hb => P.comm a ha b (h ▸ hb))
  rcases hLa with h1 | h1
  ·
    have hL₁eq : L₁ = A₁ := eq_of_le_simple h1 hn₁A₁ (ne_bot_of_quasisimple P.q₁)
    rcases hLb with h2 | h2
    · exact (hcontra (hL₁eq.trans (eq_of_le_simple h2 hn₂A₁ (ne_bot_of_quasisimple P.q₂)).symm)).elim
    · have hL₂eq : L₂ = A₂ := c5_sub h2 hn₂A₂ P.q₂ hA₂
      exact ⟨A₁, A₂, hsup.symm, hdisj, hcomm, hL₁eq, hL₂eq,
        ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
          ⟨(MulEquiv.subgroupCongr hL₁eq).trans e₁⟩⟩,
        hintC, fixer_of_inter hcomm hintC, hcard₁,
        fun w hw hfix => no_fixed_of_SL3 ⟨e₁⟩ hcard₁ hw hfix⟩
  ·
    have hL₁eq : L₁ = A₂ := c5_sub h1 hn₁A₂ P.q₁ hA₂
    rcases hLb with h2 | h2
    ·
      have hL₂eq : L₂ = A₁ := eq_of_le_simple h2 hn₂A₁ (ne_bot_of_quasisimple P.q₂)
      have hSL₁ : Nonempty (↥L₁ ≃* ↥(StatedSL 3 (ZMod 2))) :=
        ⟨ec.trans ((MulEquiv.subgroupCongr hL₂eq).trans e₁)⟩
      have hSL₂ : Nonempty (↥A₂ ≃* ↥(StatedSL 3 (ZMod 2))) :=
        ⟨(MulEquiv.subgroupCongr hL₁eq).symm.trans hSL₁.some⟩
      have hc₂ : Nat.card ↥(commV A₂) = 2 ^ 3 := by
        rw [← hL₁eq, ← hcommV, hL₂eq]
        exact hcard₁
      have hcomm' : ∀ a ∈ A₂, ∀ b ∈ A₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
      have hint' : commV A₂ ⊓ commV A₁ = ⊥ := by rw [inf_comm]; exact hintC
      exact ⟨A₂, A₁, by rw [sup_comm]; exact hsup.symm, by rw [inf_comm]; exact hdisj, hcomm',
        hL₁eq, hL₂eq, ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, hSL₁⟩, hint',
        fixer_of_inter hcomm' hint', hc₂,
        fun w hw hfix => no_fixed_of_SL3 hSL₂ hc₂ hw hfix⟩
    · exact (hcontra (hL₁eq.trans (c5_sub h2 hn₂A₂ P.q₂ hA₂).symm)).elim

end CFSG.Quasithin.C116Three

module

public import CFSG.Quasithin.Background.RealizesFaithful
public import CFSG.Quasithin.Vol2.Ch12Sec6L1d
public import CFSG.Quasithin.Background.B5Part3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

namespace S126L1e

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.QuasithinUnique S126 S126P
open scoped IsMulCommutative commutatorElement Pointwise

theorem eq_bot_of_perfect {Q : Type*} [Group Q] [Finite Q] (h2 : IsPGroup 2 Q)
    (hperf : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤) : (⊤ : Subgroup Q) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.1 h2.isNilpotent
  have h : ∀ k, (⊤ : Subgroup Q).lowerCentralSeries k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Subgroup.lowerCentralSeries_succ, ih, hperf]
  exact (h n).symm.trans hn

variable {G : Type} [Group G] [Finite G]

theorem eq_or_le_ker {B N : Subgroup G} (hBp : ⁅B, B⁆ = B) {Q : Type} [Group Q]
    [IsSimpleGroup Q] (f : ↥B →* Q) (hf : Function.Surjective f) (hk : IsPGroup 2 ↥f.ker)
    (hNB : N ≤ B) (hNn : B ≤ Subgroup.normalizer (N : Set G)) :
    N = B ∨ ∀ x (hx : x ∈ N), (⟨x, hNB hx⟩ : ↥B) ∈ f.ker := by
  set N₀ := N.subgroupOf B with hN₀def
  have hN₀ : N₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNB).mpr hNn
  have := hN₀.map f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N₀.map f) with h | h
  · right
    intro x hx
    have h1 : f ⟨x, hNB hx⟩ ∈ N₀.map f := ⟨⟨x, hNB hx⟩, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact h1
  · left
    have h2 : IsPGroup 2 (↥B ⧸ N₀) := by
      intro q
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
      have hb : f b ∈ N₀.map f := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnb⟩ := hb
      have hk' : n⁻¹ * b ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hnb, inv_mul_cancel]
      obtain ⟨e, he⟩ := hk ⟨_, hk'⟩
      refine ⟨e, ?_⟩
      have h1 : (QuotientGroup.mk b : ↥B ⧸ N₀) = QuotientGroup.mk (n⁻¹ * b) := by
        rw [QuotientGroup.eq]
        have := hN₀.conj_mem _ (N₀.inv_mem hn) b⁻¹
        simpa [mul_assoc] using this
      rw [h1, ← QuotientGroup.mk_pow]
      have h3 : (n⁻¹ * b) ^ 2 ^ e = 1 := congrArg Subtype.val he
      rw [h3, QuotientGroup.mk_one]
    have hBtop : ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ = (⊤ : Subgroup ↥B) := by
      apply Subgroup.map_injective B.subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hBp]
    have hperf : ⁅(⊤ : Subgroup (↥B ⧸ N₀)), (⊤ : Subgroup (↥B ⧸ N₀))⁆ =
        (⊤ : Subgroup (↥B ⧸ N₀)) := by
      have h4 := congrArg (Subgroup.map (QuotientGroup.mk' N₀)) hBtop
      rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective N₀)] at h4
    have h5 := eq_bot_of_perfect h2 hperf
    apply le_antisymm hNB
    intro b hb
    have h6 : (QuotientGroup.mk ⟨b, hb⟩ : ↥B ⧸ N₀) ∈ (⊤ : Subgroup (↥B ⧸ N₀)) :=
      Subgroup.mem_top _
    rw [h5, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h6
    exact h6

variable {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem inf_centralizer_le (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    L ⊓ Subgroup.centralizer (V : Set G) ≤
      Subgroup.centralizer (reducedAggregate (L ⊔ T) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH
  have hN : L ⊔ T ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    B2F.le_normalizer_inf (sup_le Subgroup.le_normalizer hyp.normalizes)
      (B2F.le_normalizer_centralizer (sup_le hLV hTV))
  have hle := LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_left) hN
    (S126T2.isPGroup_CL h1222 hH)
  exact hle.trans (A4.pCoreOf_le_centralizer_of_isTwoReducedIn (S126L1d.isTwoReducedIn_R2 L T))

omit [Finite G] in
theorem actsAs_one_of_mem (F : Frame126 T L V) {x : G}
    (hx : x ∈ Subgroup.centralizer (V : Set G)) : ActsAs F x 1 := by
  intro v w hw
  have : w = v := Subtype.ext (by
    rw [hw, (Subgroup.mem_centralizer_iff.1 hx v v.2).symm, mul_inv_cancel_right])
  rw [this, dAct_one]

theorem mem_centralizer_of_comm (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {j : G} (hjT : j ∈ T)
    (hj : ∀ l ∈ L, l * j * l⁻¹ * j⁻¹ ∈ Subgroup.centralizer (V : Set G)) :
    j ∈ Subgroup.centralizer (V : Set G) := by
  have hyp := hH.hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hVL : ⁅V, L⁆ = V := hyp.irrPlus.2.2.2.1
  have hjV : j ∈ Subgroup.normalizer (V : Set G) := S126L19b.T_le_normalizer_V h1222 hH hjT
  have hjL : j ∈ Subgroup.normalizer (L : Set G) := hyp.normalizes hjT
  obtain ⟨σ, -, hσ⟩ := actsAs_of_mem_T F hjT
  have hcomm : ∀ τ : ↥(alternatingGroup (Fin 8)), (τ : Equiv.Perm (Fin 8)) * σ = σ * τ := by
    intro τ
    obtain ⟨g, hgL, hgτ⟩ := Setup.mem_autOn_iff.1 (F.π τ).2
    have hτ : ActsAs F (g : G) τ := actsAs_of_pi F g.2 τ hgτ
    have hc := hτ.commutator hσ g.2 hjV
    have hmem : (g : G) * j * (g : G)⁻¹ * j⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hjV)
        (Subgroup.inv_mem _ g.2)) (Subgroup.inv_mem _ hjV)
    have h1 := hc.unique (actsAs_one_of_mem F (hj _ hgL)) hmem
    calc (τ : Equiv.Perm (Fin 8)) * σ =
        ((τ : Equiv.Perm (Fin 8)) * σ * (τ : Equiv.Perm (Fin 8))⁻¹ * σ⁻¹) * (σ * τ) := by group
      _ = σ * τ := by rw [h1, one_mul]
  have hσ1 : σ = 1 := by
    rcases S126T2.eq_of_comm (τ := σ) (fun a ha =>
        (hcomm ⟨a, (S126T2.mem_A6s.1 ha).2.2⟩).symm) with h | h
    · exact h
    · exfalso
      have hcy : S126T2.cy 0 2 3 ∈ alternatingGroup (Fin 8) :=
        Equiv.Perm.mem_alternatingGroup.2 (S126T2.sign_cy (by decide) (by decide))
      have h2 := hcomm ⟨_, hcy⟩
      rw [h] at h2
      have h3 : S126T2.cy 0 2 3 * Equiv.swap 0 1 = Equiv.swap 0 1 * S126T2.cy 0 2 3 := h2
      exact absurd h3 (by decide)
  rw [hσ1] at hσ
  exact S126L1b.mem_centralizer_of_actsAs_one F hVL hLV hjL hjV hσ

theorem eq_commutator_of_not_le (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) : L = ⁅L, thompsonJ T⁆ := by
  have hyp := hH.hyp
  have hJT : thompsonJ T ≤ T := thompsonJ_le_self T
  have hNL : ⁅L, thompsonJ T⁆ ≤ L :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hJT.trans hyp.normalizes)
  obtain ⟨φ, hφs, hφk⟩ := hH.alt8
  have : IsSimpleGroup ↥(alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have hk : IsPGroup 2 ↥φ.ker := by
    rw [hφk, ← Subgroup.inf_subgroupOf_left]
    exact (S126T2.isPGroup_CL h1222 hH).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  rcases eq_or_le_ker hyp.maximal.1.2.1.2.1 φ hφs hk hNL
    (Subgroup.normalizer_commutator_ge_left L (thompsonJ T)) with h | h
  · exact h.symm
  · exfalso
    apply hJ
    intro j hj
    refine mem_centralizer_of_comm h1222 F hH (hJT hj) fun l hl => ?_
    have hc : l * j * l⁻¹ * j⁻¹ ∈ ⁅L, thompsonJ T⁆ := by
      have := Subgroup.commutator_mem_commutator hl hj
      rwa [commutatorElement_def] at this
    have h1 := h _ hc
    rw [hφk] at h1
    exact Subgroup.mem_subgroupOf.1 h1

section Realize

variable {V' : Type*} [CommGroup V']

omit [Finite G] in
theorem injective_of_faithful {D : FFModel} (hD : D.Faithful) {H : Subgroup (MulAut V')}
    {U Z : Subgroup V'} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) :
    Function.Injective π :=
  CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful_on hD h

omit [Finite G] in
theorem card_eq_of_realizesVia_bot {D : FFModel} {H : Subgroup (MulAut V')} {U : Subgroup V'}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U ⊥ π) :
    Nat.card ↥U = Nat.card (↥D.sec ⧸ D.ker.subgroupOf D.sec) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβ1, -⟩ := h
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβ1 u).1 hu))
  exact Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩)

omit [Finite G] in
theorem card_le_of_le_sup [Finite V'] {P U₁ U₂ : Subgroup V'} (hP : P ≤ U₁ ⊔ U₂)
    (h : P ⊓ U₂ = ⊥) : Nat.card ↥P ≤ Nat.card ↥U₁ := by
  have h1 : Nat.card ↥P * Nat.card ↥U₂ ≤ Nat.card ↥(U₁ ⊔ U₂) := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective (fun x : ↥P × ↥U₂ => (⟨(x.1 : V') * x.2,
      Subgroup.mul_mem _ (hP x.1.2) (Subgroup.mem_sup_right x.2.2)⟩ : ↥(U₁ ⊔ U₂))) ?_
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have hab' : (a : V') * b = a' * b' := congrArg Subtype.val hab
    have hx : (a' : V')⁻¹ * a = b' * (b : V')⁻¹ := by
      calc (a' : V')⁻¹ * a = (a' : V')⁻¹ * ((a : V') * b) * (b : V')⁻¹ := by group
        _ = (a' : V')⁻¹ * ((a' : V') * b') * (b : V')⁻¹ := by rw [hab']
        _ = b' * (b : V')⁻¹ := by group
    have hmem : (a' : V')⁻¹ * a ∈ P ⊓ U₂ :=
      ⟨P.mul_mem (P.inv_mem a'.2) a.2, hx ▸ U₂.mul_mem b'.2 (U₂.inv_mem b.2)⟩
    rw [h, Subgroup.mem_bot] at hmem
    have ha : (a : V') = a' := by
      calc (a : V') = a' * ((a' : V')⁻¹ * a) := by group
        _ = a' := by rw [hmem, mul_one]
    have hb : (b : V') = b' := by
      rw [ha] at hab'
      exact mul_left_cancel hab'
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have h2 : Nat.card ↥(U₁ ⊔ U₂) ≤ Nat.card ↥U₁ * Nat.card ↥U₂ := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_surjective (fun x : ↥U₁ × ↥U₂ =>
      (⟨(x.1 : V') * x.2, Subgroup.mul_mem_sup x.1.2 x.2.2⟩ : ↥(U₁ ⊔ U₂))) ?_
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hy
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hpos : 0 < Nat.card ↥U₂ := Nat.card_pos
  exact Nat.le_of_mul_le_mul_right (h1.trans h2) hpos

end Realize

theorem card_sec_four :
    Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 4 → ZMod 2))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin 4 → ZMod 2))).subgroupOf ⊤) = 16 := by
  rw [Subgroup.bot_subgroupOf]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (⊥ : Subgroup ↥(⊤ : Subgroup (Multiplicative (Fin 4 → ZMod 2))))
  rw [Subgroup.card_bot, mul_one] at h1
  rw [← h1, Subgroup.card_top,
    show Nat.card (Multiplicative (Fin 4 → ZMod 2)) = Nat.card (Fin 4 → ZMod 2) from rfl,
    Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]
  norm_num

theorem card_statedSL_three_ne {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : Nat.card ↥(Assembly.LowTwoRank.StatedSL 3 F) ≠ 20160 := by
  rw [← Nat.card_congr (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)]
  have hI : Finset.Icc 2 3 = {2, 3} := by decide
  have e : 3 * (3 - 1) / 2 = 3 := rfl
  rw [hI, Finset.prod_pair (by norm_num), e, hF]
  intro h
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | rfl | hn
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 512 ≤ (2 ^ n) ^ 3 := by
      calc 512 = 8 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h8 3
    have h2 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ n) ^ 2 := by
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h8 2
      omega
    have h3 : 511 ≤ (2 ^ n) ^ 3 - 1 := by omega
    have := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    omega

theorem card_statedSL_five_ne : Nat.card ↥(Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) ≠ 20160 := by
  rw [← Nat.card_congr (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 (ZMod 2)).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
  have hI : Finset.Icc 2 5 = {2, 3, 4, 5} := by decide
  rw [hI]
  norm_num

theorem commutator_le_of_bot (h51 : AsB51) (h1222 : Stmt12_2_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V)
    (hJ : L = ⁅L, thompsonJ T⁆) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    ⁅reducedAggregate (L ⊔ T), L⁆ ≤ V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hH.hyp
  have := hyp.simple
  set W := reducedAggregate (L ⊔ T) with hWdef
  have hred : IsTwoReducedIn (L ⊔ T) W := S126L1d.isTwoReducedIn_R2 L T
  have hWe : IsElemAbelian 2 W := hred.2.2.1
  have : IsMulCommutative ↥W := hWe.1
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hWe.2 w w.2)
  have hVW : V ≤ W := hyp.irrPlus.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hVL : ⁅V, L⁆ = V := hyp.irrPlus.2.2.2.1
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := hyp.normalizes
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans hred.2.1
  have hTsyl : IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right
  have hncV : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    apply hyp.irrPlus.2.1
    rw [← hVL, Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h
  have hnc : ¬ L ≤ Subgroup.centralizer (W : Set G) := fun h =>
    hncV (h.trans (Subgroup.centralizer_le hVW))
  have hO2Y : pCoreOf 2 (autOn (L ⊔ T) W) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hO2L : pCoreOf 2 (autOn L W) = ⊥ := by
    have hn : ((autOn L W).subgroupOf (autOn (L ⊔ T) W)).Normal := by
      refine ⟨fun k hk x => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      exact autOn_normal_of (sup_le Subgroup.le_normalizer hTN) _ x.2 _ hk
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _
      (autOn_le_autOn_of_le le_sup_left) hn
    rw [hO2Y] at this
    exact le_bot_iff.1 this
  have hq : CFSG.IsQuasisimple ↥(autOn L W) := isQuasisimple_autOn hLW hyp.quasisimple hO2L hnc
  have hloc : LocalSQTK G := (qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
  have hQne : pCoreOf 2 (L ⊔ T) ≠ ⊥ := fun h =>
    hyp.irrPlus.2.1 (le_bot_iff.1 (h ▸ hVW.trans (reducedAggregate_le_pCoreOf _)))
  have hSL : SQTKGroup ↥L := sqtkGroup_mono (sqtkGroup_of_localSQTK hloc hQne) le_sup_left
  have hSQ : SQTKGroup ↥(autOn L W) := sqtkGroup_autOn hLW hSL
    ((S126T2.isPGroup_CL h1222 hH).to_le (inf_le_inf_left L (Subgroup.centralizer_le hVW)))
  obtain ⟨A, -, hA, hLA⟩ := S126L1d.exists_offender hred hTsyl le_sup_left hTN hq hnc hJ
  have h2 : ∀ y ∈ L ⊔ T, ∃ e : ℕ, y ^ 2 ^ e ∈ L ⊔ Subgroup.centralizer (W : Set G) :=
    fun y hy => (S126L1d.exists_two_pow_mem hTsyl.2.1 hTN hy).imp fun _ he =>
      (le_sup_left : L ≤ L ⊔ Subgroup.centralizer (W : Set G)) he
  have hb51 := (b51Hyp_ffJ_autOn hred.2.1 le_sup_left (sup_le Subgroup.le_normalizer hTN) h2
    hO2Y hq hSQ hA hLA).1
  obtain ⟨⟨-, hcases⟩, -⟩ := h51 ↥W hW2 _ _ hb51
  set K := autOn L W with hKdef
  set U := commV K with hUdef
  have hUmap : U.map W.subtype = ⁅W, L⁆ := map_commV_autOn hLW
  have hVU : V.subgroupOf W ≤ U := by
    intro v hv
    have h1 : (v : G) ∈ U.map W.subtype := by
      rw [hUmap]
      have h2 : (v : G) ∈ V := hv
      rw [← hVL] at h2
      exact Subgroup.commutator_mono hVW le_rfl h2
    obtain ⟨u, hu, hue⟩ := h1
    rwa [show u = v from Subtype.ext hue] at hu
  have hVinv : ∀ a : ↥K, ∀ v ∈ V.subgroupOf W, (a : MulAut ↥W) v ∈ V.subgroupOf W := by
    intro a v hv
    obtain ⟨g, hg, hga⟩ := Subgroup.mem_map.1 a.2
    rw [Subgroup.mem_subgroupOf] at hg
    rw [Subgroup.mem_subgroupOf]
    show (((a : MulAut ↥W) v : ↥W) : G) ∈ V
    rw [← hga, A5Mod.conjAct_apply_coe]
    exact (Subgroup.mem_normalizer_iff.1 (hLV hg) v).1 hv
  have hirrV : ∀ D : Subgroup ↥W, D ≤ V.subgroupOf W → XMod.IsInv ↥K D →
      D = ⊥ ∨ D = V.subgroupOf W := by
    intro D hDV hDinv
    set J := D.map W.subtype with hJdef
    have hJV : J ≤ V := by
      rintro _ ⟨d, hd, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hDV hd)
    have hconj : ∀ l ∈ L, ∀ x ∈ J, l * x * l⁻¹ ∈ J := by
      rintro l hl _ ⟨d, hd, rfl⟩
      have ha : conjAct W ⟨l, hLW hl⟩ ∈ K := conjAct_mem_autOn hLW hl
      refine ⟨_, hDinv ⟨_, ha⟩ d hd, ?_⟩
      exact Setup.coe_conjAct_apply _ _
    have hLJ : L ≤ Subgroup.normalizer (J : Set G) := fun l hl =>
      Subgroup.mem_normalizer_iff.2 fun x => ⟨hconj l hl x, fun hx => by
        have := hconj l⁻¹ (L.inv_mem hl) _ hx
        simpa [mul_assoc] using this⟩
    rcases hyp.irrPlus.2.2.2.2.2.1 J (by rw [hZ]; exact bot_le) hJV hLJ with h | h
    · left
      rw [hZ] at h
      exact (Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective).1 h
    · right
      rw [← Subgroup.comap_map_eq_self_of_injective W.subtype_injective D, ← hJdef, h]
      rfl
  have h64 : 64 ≤ Nat.card ↥(V.subgroupOf W) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVW).toEquiv]
    exact S126F.card_D8.trans (Nat.card_le_card_of_surjective F.β F.β_surj)
  have hK : Nat.card ↥K = 20160 := by
    obtain ⟨φ, hφs, hφk⟩ := hH.alt8
    have hker : (autOnHom hLW).ker = φ.ker := by
      ext l
      rw [mem_ker_autOnHom, hφk, Subgroup.mem_subgroupOf]
      exact ⟨fun h => Subgroup.centralizer_le hVW h,
        fun h => inf_centralizer_le h1222 hH ⟨l.2, h⟩⟩
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
        (autOnHom_surjective hLW)).toEquiv,
      Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv,
      Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hcardSL : ∀ {n : ℕ} {F : Type} [Field F] [Finite F] {I : Subgroup ↥W}
      {π : ↥(Assembly.LowTwoRank.StatedSL n F) →* ↥K},
      (FFModel.nat (Assembly.LowTwoRank.StatedSL n F)).RealizesVia K I ⊥ π →
      Nat.card ↥(Assembly.LowTwoRank.StatedSL n F) = 20160 := fun hr =>
    (Nat.card_congr (Equiv.ofBijective _
      ⟨injective_of_faithful (FFModel.nat_faithful _) hr, hr.1⟩)).trans hK
  have hUV : U ≤ V.subgroupOf W := by
    rcases hcases with hi | hii | ⟨n, hiii⟩ | hiv
    ·
      obtain ⟨-, -, hcommU, hirrSec⟩ := hi.1
      have hFix : fixV K = (Subgroup.centralizer (L : Set G)).subgroupOf W := fixV_autOn_eq hLW
      set Fx := XMod.fixed (↥K) U with hFxdef
      have hFK : Fx ≤ fixV K := fun f hf' a ha => hf'.2 ⟨a, ha⟩
      have hJinv : XMod.IsInv (↥K) (V.subgroupOf W ⊔ Fx) := by
        intro a x hx
        have hle : (V.subgroupOf W ⊔ Fx) ≤ (V.subgroupOf W ⊔ Fx).comap
            ((a : MulAut ↥W) : ↥W →* ↥W) := by
          refine sup_le (fun v hv => ?_) (fun f hf' => ?_)
          · exact Subgroup.mem_comap.2 (le_sup_left (a := V.subgroupOf W) (hVinv a v hv))
          · refine Subgroup.mem_comap.2 (le_sup_right (b := Fx) ?_)
            show (a : MulAut ↥W) f ∈ Fx
            have h1 : (a : MulAut ↥W) f = f := hf'.2 a
            rw [h1]
            exact hf'
        exact hle hx
      have hUle : U ≤ V.subgroupOf W ⊔ fixV K := by
        rcases hirrSec.2 _ hJinv le_sup_right (sup_le hVU hirrSec.1.le) with h | h
        · exfalso
          obtain ⟨v, hvV, hvL⟩ : ∃ v ∈ V, v ∉ Subgroup.centralizer (L : Set G) := by
            by_contra hall
            push Not at hall
            apply hncV
            intro l hl
            rw [Subgroup.mem_centralizer_iff]
            intro w hw
            exact (Subgroup.mem_centralizer_iff.1 (hall w hw) l hl).symm
          have h1 : (⟨v, hVW hvV⟩ : ↥W) ∈ Fx := h ▸ le_sup_left (a := V.subgroupOf W) hvV
          have h2 := hFK h1
          rw [hFix] at h2
          exact hvL h2
        · exact (le_of_eq h.symm).trans (sup_le_sup_left hFK _)
      show commV K ≤ V.subgroupOf W
      rw [← hcommU]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨a, u, hu, rfl⟩
      obtain ⟨v, hv, f, hf, rfl⟩ := Subgroup.mem_sup.1 (hUle hu)
      have hfa : a • f = f := hf a a.2
      have hva : a • v ∈ V.subgroupOf W := hVinv a v hv
      show a • (v * f) * (v * f)⁻¹ ∈ V.subgroupOf W
      rw [smul_mul', hfa, show a • v * f * (v * f)⁻¹ = a • v * v⁻¹ by group]
      exact (V.subgroupOf W).mul_mem hva ((V.subgroupOf W).inv_mem hv)
    ·
      exfalso
      obtain ⟨-, n, F, _, _, hF, I, π, -, -, hreal, -⟩ := hii
      exact card_statedSL_three_ne hF (hcardSL (hreal 0))
    ·
      exfalso
      obtain ⟨-, hn', π, U₁, U₂, hdir, hreal₁, hreal₂⟩ := hiii
      rcases hn' with rfl | rfl
      · have hU₁ : Nat.card ↥U₁ = 16 := (card_eq_of_realizesVia_bot hreal₁).trans card_sec_four
        have hU₂ : Nat.card ↥U₂ = 16 := (card_eq_of_realizesVia_bot hreal₂).trans card_sec_four
        have hinv : XMod.IsInv ↥K (V.subgroupOf W ⊓ U₂) := fun a x hx =>
          ⟨hVinv a x hx.1, hreal₂.2.2.2.1 a x hx.2⟩
        rcases hirrV _ inf_le_left hinv with h | h
        · have := card_le_of_le_sup (hVU.trans hdir.1.ge) h
          omega
        · have hle : V.subgroupOf W ≤ U₂ := h ▸ inf_le_right
          have := Subgroup.card_le_of_le hle
          omega
      · exact card_statedSL_five_ne (hcardSL hreal₁)
    ·
      exfalso
      obtain ⟨-, n, hn', k, hk1, -, I, π, -, -, hsup, hreal⟩ := hiv
      rcases hn' with rfl | rfl
      · have hπ := (hreal ⟨0, hk1⟩).1
        have hirr : ∀ i, XMod.IsIrr ↥K (I i) := fun i =>
          B5.isIrr_of_realizes (by norm_num) (hreal i)
        have hiso : ∀ i j, XMod.Iso ↥K (I i) (I j) := fun i j =>
          B5.iso_of_realizes hπ (hreal i) (hreal j)
        have hVirr : XMod.IsIrr ↥K (V.subgroupOf W) := by
          refine ⟨fun a v hv => hVinv a v hv, bot_lt_iff_ne_bot.2 fun h0 => ?_,
            fun D hD _ hDV => hirrV D hDV hD⟩
          rw [h0, Subgroup.card_bot] at h64
          omega
        have hVI : V.subgroupOf W ≤ ⨆ i, I i := by
          rw [bot_sup_eq] at hsup
          rw [hsup]
          exact hVU
        obtain ⟨φ, -⟩ := B5.iso_of_irr_le_iSup I hirr hiso ⟨0, hk1⟩ hVirr hVI
        have h1 : Nat.card ↥(V.subgroupOf W) = 16 := ((Nat.card_congr φ.toEquiv).trans
          (card_eq_of_realizesVia_bot (hreal ⟨0, hk1⟩))).trans card_sec_four
        omega
      · exact card_statedSL_five_ne (hcardSL (hreal ⟨0, hk1⟩))
  rw [← hUmap]
  rintro _ ⟨u, hu, rfl⟩
  exact hUV hu

theorem commutator_le_V (h51 : AsB51) (h1222 : Stmt12_2_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    ⁅reducedAggregate (L ⊔ T), L⁆ ≤ V := by
  have hLJ := eq_commutator_of_not_le h1222 F hH hJ
  by_cases hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥
  · exact commutator_le_of_bot h51 h1222 F hH hLJ hZ
  · exact S126L1d.commutator_le h51 h1222 hH hLJ hZ

end S126L1e

end CFSG.Quasithin.H13

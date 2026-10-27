module

public import CFSG.RankThree.PartOne.S12.Sec12FusSplit
public import CFSG.RankThree.PartOne.S12K.OutOfLayer
public import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S9.Vanishing.Basic

public section

namespace CFSG.RankThree.PartOne.K1214

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.OutStructure
open Subgroup

variable {G : Type} [Group G]

theorem comparable_of_outPChain {p : ℕ} (J : Subgroup G) [Group.IsPerfect J]
    (h : OutPChain p (J ⧸ center J)) {P : Subgroup G} (hP : IsPGroup p P)
    (hPN : P ≤ normalizer (J : Set G)) {u v : G} (hu : u ∈ P) (hv : v ∈ P) :
    u ∈ zpowers v ⊔ (P ⊓ (J ⊔ centralizer (J : Set G))) ∨
      v ∈ zpowers u ⊔ (P ⊓ (J ⊔ centralizer (J : Set G))) := by
  obtain ⟨D, E, hID, hD2, hpE, hD4⟩ := h
  set ρ := actionOnQuot J with hρ
  have hρmem : ∀ {a : G} (ha : a ∈ normalizer (J : Set G)),
      ρ ⟨a, ha⟩ ∈ Inn (J ⧸ center J) ↔ a ∈ J ⊔ centralizer (J : Set G) :=
    fun ha => actionOnQuot_mem_inner_iff J ha
  have hpow : ∀ {a : G} (ha : a ∈ P), ∃ k : ℕ, a ^ (p ^ k) = 1 := fun {a} ha => by
    obtain ⟨k, hk⟩ := hP ⟨a, ha⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hρpow : ∀ {a : G} (ha : a ∈ P) (k : ℕ), a ^ (p ^ k) = 1 →
      (ρ ⟨a, hPN ha⟩) ^ (p ^ k) = 1 := fun {a} ha k hk => by
    rw [← map_pow]
    have : (⟨a, hPN ha⟩ : normalizer (J : Set G)) ^ (p ^ k) = 1 :=
      Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hun := hPN hu
  have hvn := hPN hv
  obtain ⟨k, hk⟩ := hpow hu
  obtain ⟨l, hl⟩ := hpow hv
  have hαD : ∃ k : ℕ, (ρ ⟨u, hun⟩) ^ (p ^ k) ∈ D := ⟨k, by rw [hρpow hu k hk]; exact D.one_mem⟩
  have hβD : ∃ k : ℕ, (ρ ⟨v, hvn⟩) ^ (p ^ k) ∈ D := ⟨l, by rw [hρpow hv l hl]; exact D.one_mem⟩
  have hcrit : ∀ {a b : G} (ha : a ∈ P) (hb : b ∈ P) (m : ℤ),
      ρ ⟨a, hPN ha⟩ * (ρ ⟨b, hPN hb⟩) ^ m ∈ D → a * b ^ m ∈ J ⊔ centralizer (J : Set G) := by
    intro a b ha hb m hm
    have hbm : b ^ m ∈ P := P.zpow_mem hb m
    have hab : a * b ^ m ∈ P := P.mul_mem ha hbm
    have himg : ρ ⟨a * b ^ m, hPN hab⟩ = ρ ⟨a, hPN ha⟩ * (ρ ⟨b, hPN hb⟩) ^ m := by
      rw [← map_zpow, ← map_mul]
      rfl
    obtain ⟨j, hj⟩ := hpow hab
    have hinner : ρ ⟨a * b ^ m, hPN hab⟩ ∈ Inn (J ⧸ center J) :=
      hD2 _ (himg ▸ hm) j (hρpow hab j hj ▸ (Inn _).one_mem)
    exact (hρmem _).mp hinner
  have hP' : ∀ {a b : G}, a ∈ P → b ∈ P → ∀ m : ℤ, a * b ^ m ∈ J ⊔ centralizer (J : Set G) →
      a ∈ zpowers b ⊔ (P ⊓ (J ⊔ centralizer (J : Set G))) := by
    intro a b ha hb m h1
    have hbm : b ^ m ∈ P := P.zpow_mem hb m
    have hab : a * b ^ m ∈ P := P.mul_mem ha hbm
    have : a = (a * b ^ m) * b ^ (-m) := by group
    rw [this]
    exact Subgroup.mul_mem _ (mem_sup_right ⟨hab, h1⟩) (mem_sup_left (zpow_mem (mem_zpowers b) _))
  have hαE := hpE _ hαD
  have hβE := hpE _ hβD
  rcases hD4 _ hαE _ hβE hαD hβD with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact Or.inl (hP' hu hv m (hcrit hu hv m hm))
  · exact Or.inr (hP' hv hu m (hcrit hv hu m hm))

section Ctx

variable [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {b : G}
  {K I X P Q : Subgroup G}

theorem prime_five_le (ctx : Fus12Ctx G p A c L E) : p.Prime ∧ 5 ≤ p := by
  have h := ctx.hyp
  have hp := h.prime
  refine ⟨hp, ?_⟩
  have h3 := h.three_lt
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · obtain rfl : p = 4 := by omega
    exact absurd hp (by norm_num)
  · exact h5

theorem zI_pPrime (h112 : InSec11Two) (ctx : Fus12Ctx G p A c L E)
    (hL : Layer1212 p A c L E b K I) (hF : Field1213 p A c L b K I) :
    ¬ p ∣ Nat.card (Subgroup.center ↥I) := by
  obtain ⟨hbA, -, hb1⟩ := hL.b_mem
  exact (h112 G p A ctx.hyp.setup b hbA hb1 I ⟨⟨hF.star0.1, hF.two⟩, hF.star0.2⟩).2.1

omit [Finite G] in
theorem I_le_centralizer (hL : Layer1212 p A c L E b K I) :
    I ≤ Subgroup.centralizer ({b} : Set G) :=
  (mem_thetaComponentsAt_iff.mp hL.I_mem).1

omit [Finite G] in
theorem I_perfect (hL : Layer1212 p A c L E b K I) : Group.IsPerfect ↥I :=
  isPerfect_of_mem_thetaComponentsAt hL.I_mem

omit [Finite G] in
theorem P_isPGroup (hC : Choice1212 p E b I X P Q) : IsPGroup p ↥P := hC.P_sylow.1.2.1

theorem R_sylow (ctx : Fus12Ctx G p A c L E) (hL : Layer1212 p A c L E b K I)
    (hC : Choice1212 p E b I X P Q) : IsSylowOf p (P ⊓ I) I := by
  have : Fact p.Prime := ⟨(prime_five_le ctx).1⟩
  rw [Vanish.isSylowOf_iff_abg]
  exact inf_isSylowOf_of_le_normalizer (Vanish.isSylowOf_iff_abg.mp hC.P_sylow.1)
    (I_le_centralizer hL) hC.P_norm

theorem inf_sup_centralizer_eq_Q (h112 : InSec11Two) (ctx : Fus12Ctx G p A c L E)
    (hL : Layer1212 p A c L E b K I) (hC : Choice1212 p E b I X P Q)
    (hF : Field1213 p A c L b K I) :
    P ⊓ (I ⊔ Subgroup.centralizer (I : Set G)) = Q := by
  have : Fact p.Prime := ⟨(prime_five_le ctx).1⟩
  rw [hC.Q_eq]
  exact inf_sup_centralizer_eq (Vanish.isSylowOf_iff_abg.mp hC.P_sylow.1) (I_le_centralizer hL)
    hC.P_norm (zI_pPrime h112 ctx hL hF)

theorem comparable (h112 : InSec11Two) (ctx : Fus12Ctx G p A c L E)
    (hL : Layer1212 p A c L E b K I) (hC : Choice1212 p E b I X P Q)
    (hF : Field1213 p A c L b K I) :
    ∀ u ∈ P, ∀ v ∈ P, u ∈ zpowers v ⊔ Q ∨ v ∈ zpowers u ⊔ Q := by
  obtain ⟨hp, hp5⟩ := prime_five_le ctx
  have : Group.IsPerfect ↥I := I_perfect hL
  obtain ⟨r, hr1, hr12, hrow, -⟩ := ctx.facts.three.2
  have hOut : OutPNice p (↥I ⧸ Subgroup.center ↥I) :=
    S12K.outPNice_of_layerModel hp hp5 hF.model ⟨r, hr1, hr12, hrow⟩
  have hPQ := inf_sup_centralizer_eq_Q h112 ctx hL hC hF
  intro u hu v hv
  have := comparable_of_outPChain I hOut.toChain (P_isPGroup hC) hC.P_norm hu hv
  rwa [hPQ] at this

theorem exists_f (h112 : InSec11Two) (ctx : Fus12Ctx G p A c L E)
    (hL : Layer1212 p A c L E b K I) (hC : Choice1212 p E b I X P Q)
    (hF : Field1213 p A c L b K I) : ∃ f ∈ P, P = Q ⊔ zpowers f :=
  exists_sup_zpowers_eq_of_comparable (Sec12Fus.q_normal hC).1 (comparable h112 ctx hL hC hF)

end Ctx

end CFSG.RankThree.PartOne.K1214

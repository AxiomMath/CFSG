module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22K
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22L

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lem12223Extra : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H P U I : Subgroup G) (h : G) (n : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Concl12_2_20 T L V n →
    Pre12_2_21 T L V H P U I h 3 → U ≤ pCoreOf 2 H →
    Nat.card P = 27 → (∀ x ∈ P, x ^ 3 = 1) → Nat.card ((frattini ↥P).map P.subtype) = 3 →
    (∀ f ∈ (frattini ↥P).map P.subtype, ∀ x ∈ P, f * x = x * f) →
    (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (V : Set G) →
    (∀ x ∈ V, ∀ f ∈ (frattini ↥P).map P.subtype, x * f * x⁻¹ * f⁻¹ ∈ pCoreOf 2 H) →
    pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ⊓
        Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) ≤
      Subgroup.centralizer (P : Set G) →
    (∃ X : Subgroup G, X ≠ ⊥ ∧
      X ≤ V ⊓ (pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) ∧
      (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (X : Set G) ∧
      X ⊓ Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) = ⊥) →
    False

namespace Lem22

variable {G : Type} [Group G] [Finite G]

theorem extra_of_pre (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) {T L V H P U I : Subgroup G}
    {h : G} {n p : ℕ} (hyp : Hyp1223 G T L V) (hC : Concl12_2_20 T L V n)
    (hpre : Pre12_2_21 T L V H P U I h p) (hUO : U ≤ pCoreOf 2 H) (hΦ1 : frattini ↥P ≠ ⊥) :
    Nat.card P = p ^ 3 ∧ (∀ x ∈ P, x ^ p = 1) ∧
      Nat.card ((frattini ↥P).map P.subtype) = p ∧
      ∀ f ∈ (frattini ↥P).map P.subtype, ∀ x ∈ P, f * x = x * f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVO := Lem21.not_le_pCoreOf_of_pre hpre
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, hHPT, hPΦ, hhP, hhM, -, -, -, -, -, -, -, hidx,
    -, -⟩ := hpre
  have : Fact p.Prime := ⟨hp⟩
  set Q := pCoreOf 2 H with hQ
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  have hP1 : P ≠ ⊥ := fun h0 => hh1 (by rw [h0] at hhP; exact Subgroup.mem_bot.mp hhP)
  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 hyp hred
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)
  have hmin := Lem7.minParabolic h331 hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hO2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hOH : Q ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHO : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hconjO : ∀ g ∈ H, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hHO hg) y).mp hy
  have hUV : U ⊓ V = Q ⊓ V :=
    ((Lem21.eq_or_le_of_relIndex_eq_two (inf_le_inf_right V hUO) inf_le_right hidx).resolve_right
      fun hle => hVO (hle.trans inf_le_left)).symm
  have hidx' : (V ⊓ Q).relIndex V = 2 := by rw [inf_comm, ← hUV]; exact hidx
  obtain ⟨v, hvV, hvO⟩ := IsConcreteLE.not_le_iff_exists.mp hVO
  have hv2 := hV2 v hvV
  have hvH : v ∈ H := hTH (hVT hvV)
  have hVL := le_pCoreOf_L hyp hVT hV2
  obtain ⟨m, hmv, hmP, hmcomm, hminv⟩ := exists_inv_conj_frattini h331 hyp hHs hsol hp hp2 hPp
    hPH hPi hHPT hPΦ hVT hTV hVL hidx' hP1 hvV hv2 hvO
  have hPO : ∀ y ∈ P, y ∈ Q → y = 1 := fun y hyP hyO =>
    eq_one_of_mem_of_mem hp hp2 hPp hO2 hyP hyO
  have hmP' : ∀ x ∈ P, m * x * m⁻¹ ∈ P := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hmP x).mp hx
  have hm2O : m * m ∈ Q := by
    obtain ⟨q, hq, rfl⟩ : ∃ q ∈ Q, q * v = m := ⟨m * v⁻¹, hmv, by group⟩
    have e : q * v * (q * v) = q * (v * q * v⁻¹) * (v * v) := by group
    rw [e, ← pow_two v, hv2, mul_one]
    exact Q.mul_mem hq (hconjO v hvH q hq)
  have hm2 : ∀ x ∈ P, (m * m) * x * (m * m)⁻¹ = x := by
    intro x hx
    have h1 : (m * m) * x * (m * m)⁻¹ * x⁻¹ ∈ P := by
      have e : (m * m) * x * (m * m)⁻¹ = m * (m * x * m⁻¹) * m⁻¹ := by group
      rw [e]
      exact P.mul_mem (hmP' _ (hmP' x hx)) (P.inv_mem hx)
    have h2 : (m * m) * x * (m * m)⁻¹ * x⁻¹ ∈ Q := by
      have e : (m * m) * x * (m * m)⁻¹ * x⁻¹ = (m * m) * (x * (m * m)⁻¹ * x⁻¹) := by group
      rw [e]
      exact Q.mul_mem hm2O (hconjO x (hPH hx) _ (Q.inv_mem hm2O))
    exact mul_inv_eq_one.mp (hPO _ h1 h2)
  have hZ := comm_of_mem_frattini hp hp2 hPp hmP hmcomm hminv hm2
  have hexp := pow_eq_one_of_inv hp hp2 hPp hmP hmcomm hminv hm2
  have hQ1 : Q ≠ ⊥ := by
    intro h0
    have h1 := hidx'
    rw [h0, inf_bot_eq, Subgroup.relIndex_bot_left] at h1
    obtain ⟨hn, hcardV, -⟩ := hC
    rw [hcardV] at h1
    rcases hn with rfl | rfl | rfl <;> norm_num at h1
  have hrank : ∀ E : Subgroup G, E ≤ P → IsMulCommutative ↥E → Nat.card E ≤ p ^ 2 := by
    intro E hEP hEc
    obtain ⟨k, hk⟩ := (hPp.to_le hEP).exists_card_eq
    have hEe : CFSG.Open.IsElemAbelian p E := ⟨hEc, fun x hx => hexp x (hEP hx)⟩
    have h1 := CFSG.SectionRank.le_pRank hp.one_lt (hEP.trans hPH) hEe hk
    have h2 := CFSG.Quasithin.pRank_le_two_of_pCoreOf_ne_bot hyp.qtke hQ1 hp hp2
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos (h1.trans h2)
  obtain ⟨hcard, hΦp⟩ := card_eq_of_rank hp hPp hexp hZ hΦ1 hrank
  exact ⟨hcard, hexp, hΦp, hZ⟩

end Lem22

theorem lem12223Three_of_extra (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hX : Lem12223Extra) :
    Lem12223Three := by
  intro G _ _ T L V H P U I h n hyp hNE hC hpre hUO _ hΦ1 hΦV hVΦ hcent hXfpf
  obtain ⟨hcard, hexp, hΦp, hZ⟩ := Lem22.extra_of_pre h331 h1222 hyp hC hpre hUO hΦ1
  exact hX G T L V H P U I h n hyp hNE hC hpre hUO (by rw [hcard]; norm_num) hexp hΦp hZ hΦV hVΦ
    hcent hXfpf

theorem lem12222Frattini_of_extra (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1216 : Stmt12_2_16)
    (hKG : KGBorelOvergroupThree) (hX : Lem12223Extra) : Lem12222Frattini :=
  lem12222Frattini_of_three h331 h1222 h1216 hKG (lem12223Three_of_extra h331 h1222 hX)

end CFSG.Quasithin.H13

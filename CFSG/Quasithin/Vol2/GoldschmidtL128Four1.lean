module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma6
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma8

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace L128Four

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ}

theorem isTwoReducedIn (h1222 : Stmt12_2_2) (h : Hyp1281One G T L V n) :
    IsTwoReducedIn (L ⊔ T) V := by
  have hyp := h.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -⟩ := hall V hyp.irrPlus
  exact isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVT.trans le_sup_right, hred⟩

theorem pCoreOf_le_centralizer (h1222 : Stmt12_2_2) (h : Hyp1281One G T L V n) :
    pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) :=
  (isTwoReducedIn h1222 h).2.2.2 _ (LieType.BorelTits.pCoreOf_le 2 _)
    (LieType.BorelTits.le_normalizer_pCoreOf 2 _) fun d hd => by
      obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T) ⟨d, hd⟩
      refine ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
      rw [this]
      exact Subgroup.one_mem _

theorem inf_centralizer_le_pCoreOf (h1222 : Stmt12_2_2) (h : Hyp1281One G T L V n) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := h.hyp
  have hred := isTwoReducedIn h1222 h
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hCL : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [inf_centralizer_eq_pCoreOf h1222 h]
    exact LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hC2 : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
    intro c
    obtain ⟨k, hk⟩ := L1286.exists_two_pow_mem_of_mem_sup hyp.sylow.1 hyp.normalizes c.2.1
    have hkC : (c : G) ^ 2 ^ k ∈ L ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨hk, pow_mem c.2.2 _⟩
    obtain ⟨m, hm⟩ := hCL ⟨_, hkC⟩
    have hm' : ((c : G) ^ 2 ^ k) ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    refine ⟨k + m, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, hm']
  have hCN : L ⊔ T ≤ Subgroup.normalizer
      (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hLTV)
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hCN hC2

theorem pCoreOf_eq_inf_pCoreOf_sup (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 L = L ⊓ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (le_inf (LieType.BorelTits.pCoreOf_le 2 L) ?_) ?_
  · exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
      (sup_le (LieType.BorelTits.le_normalizer_pCoreOf 2 L)
        (hTL.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
      (LieType.BorelTits.pCoreOf_isPGroup 2 L)
  · refine LieType.BorelTits.le_pCoreOf 2 inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun l hl =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl,
          LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hl)⟩)
      ((LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)

theorem inf_centralizer_eq_inf_pCoreOf (h1222 : Stmt12_2_2) (h : Hyp1281One G T L V n) :
    L ⊓ Subgroup.centralizer (V : Set G) = L ⊓ pCoreOf 2 (L ⊔ T) := by
  rw [inf_centralizer_eq_pCoreOf h1222 h, pCoreOf_eq_inf_pCoreOf_sup h.hyp.normalizes]

theorem not_U_le_centralizer (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (hs : Setting1282One G T L V n V₁ V₂) :
    ¬ u128 V V₁ ≤ Subgroup.centralizer (V : Set G) := by
  intro hUC
  have hVZ : V ≤ zU128 V V₁ := fun v hv =>
    ⟨le_conjClosure V _ hv, Subgroup.mem_centralizer_iff.2 fun u hu =>
      (Subgroup.mem_centralizer_iff.1 (hUC hu) v hv).symm⟩
  have h3 := lemma12_8_8_three h1222 h12213 hs
  rw [inf_eq_left.2 hVZ] at h3
  have hcard := hs.hyp.card_sq.1
  have h1 := hs.v1.2.1
  rw [← h3, hcard] at h1
  have hn : 3 ≤ n := by rcases hs.hyp.n_mem with rfl | rfl | rfl <;> omega
  have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem not_U_le_pCoreOf (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (hs : Setting1282One G T L V n V₁ V₂) : ¬ u128 V V₁ ≤ pCoreOf 2 (L ⊔ T) :=
  fun h => not_U_le_centralizer h1222 h12213 hs (h.trans (pCoreOf_le_centralizer h1222 hs.hyp))

theorem V_eq_conjClosure (h12213 : Stmt12_2_13) (hs : Setting1282One G T L V n V₁ V₂) :
    V = conjClosure V₁ L := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hs.hyp.hyp.irrPlus.2.2.1
  refine le_antisymm (fun v hv => ?_)
    (conjClosure_le fun l hl z hz => (Subgroup.mem_normalizer_iff.mp (hLV hl) z).mp (hs.v1.1 hz))
  by_cases hv1 : v = 1
  · rw [hv1]
    exact Subgroup.one_mem _
  have hsq : v ^ 2 = 1 := hs.hyp.card_sq.2.1 v hv
  have hz2 : Nat.card (Subgroup.zpowers v) = 2 := by
    rw [Nat.card_zpowers]
    refine (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsq) |>.resolve_left ?_
    intro h1
    exact hv1 (orderOf_eq_one_iff.mp h1)
  obtain ⟨l, hl, hlz⟩ := (lemma12_8_3 h12213 G T L V n hs.hyp).2.1 1 V₁ (Subgroup.zpowers v) hs.v1.1
    (Subgroup.zpowers_le.mpr hv) (by simpa using hs.v1.2.1) (by simpa using hz2)
  have hvz : v ∈ CFSG.conjugate V₁ l := hlz ▸ Subgroup.mem_zpowers v
  have h1 : l * v * l⁻¹ ∈ V₁ := SteinbergBS.mem_conjugate_iff.1 hvz
  have h2 := mem_conjClosure (L.inv_mem hl) h1
  have e : l⁻¹ * (l * v * l⁻¹) * l⁻¹⁻¹ = v := by group
  rwa [e] at h2

end L128Four

end CFSG.Quasithin.H13

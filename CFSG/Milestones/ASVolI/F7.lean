module

public import CFSG.Quasithin.Background.RonanF713Main
public import CFSG.Quasithin.Background.F7TwoInvSQTKProved
public import CFSG.Quasithin.Background.F7TwoClaimC

public section

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.F7
open scoped Pointwise

structure HypF_7_1 {G : Type} [Group G] (G₀ G₁ G₂ T : Subgroup G) : Prop where
  finite₁ : Finite G₁
  finite₂ : Finite G₂
  charTwo : CharTwo G₁
  sylow_inf : IsSylowTwoOf T (G₁ ⊓ G₂)
  sylow₁ : IsSylowTwoOf T G₁
  sylow₂ : IsSylowTwoOf T G₂
  gen : G₀ = G₁ ⊔ G₂
  o2_trivial : pCoreOf 2 G₀ = ⊥

structure HypF_7_6 {G : Type} [Group G] (G₀ G₁ G₂ T V : Subgroup G) : Prop where
  toHypF_7_1 : HypF_7_1 G₀ G₁ G₂ T
  reduced : IsTwoReducedIn G₁ V
  cT : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (G₁ ⊓ Subgroup.centralizer (V : Set G))

end CFSG.ASVolI.ChF

namespace CFSG.Quasithin.CosetGeom

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

variable {G : Type*} [Group G]

section Loc

variable {G₀ G₁ G₂ T V : Subgroup G}

private theorem loc_pCoreOf_isPGroup (p : ℕ) (H : Subgroup G) : IsPGroup p (pCoreOf p H) :=
  (CFSG.pCore_isPGroup (p := p) (G := ↥H)).map H.subtype

private theorem loc_pCoreOf_mono {K H : Subgroup G} (hKH : K ≤ H)
    (hN : H ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 K ≤ pCoreOf 2 H :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
    (hN.trans (normalizer_le_normalizer_pCoreOf 2 K)) (loc_pCoreOf_isPGroup 2 K)

private theorem loc_pCoreOf_inf_le {K H : Subgroup G} (hKH : K ≤ H) :
    pCoreOf 2 H ⊓ K ≤ pCoreOf 2 K := by
  refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((loc_pCoreOf_isPGroup 2 H).to_le inf_le_left)
  refine F7.le_normalizer_inf ?_ Subgroup.le_normalizer
  exact hKH.trans (le_normalizer_pCoreOf 2 H)

private theorem loc_finite_of_le {H K : Subgroup G} [Finite H] (h : K ≤ H) : Finite K :=
  Finite.of_injective (fun x : K => (⟨x.1, h x.2⟩ : H))
    fun a b hab => Subtype.ext (congrArg (fun y : H => (y : G)) hab)

private theorem loc_chain_stabilizes {H : Subgroup G} [Finite H] {f : ℕ → Subgroup G}
    (hf : Antitone f) (hfH : ∀ n, f n ≤ H) : ∃ n₀ : ℕ, ∀ m, n₀ ≤ m → f n₀ = f m := by
  haveI : Finite (Subgroup H) :=
    Finite.of_injective (fun K : Subgroup H => (K : Set H)) SetLike.coe_injective
  obtain ⟨n₀, hn₀⟩ := WellFoundedLT.antitone_chain_condition
    (f := fun n => (f n).subgroupOf H) (fun m n hmn => Subgroup.subgroupOf_mono H (hf hmn))
  refine ⟨n₀, fun m hm => ?_⟩
  have key : ∀ K : Subgroup G, K ≤ H → (K.subgroupOf H).map H.subtype = K :=
    fun K hK => Subgroup.map_subgroupOf_eq_of_le hK
  calc f n₀ = ((f n₀).subgroupOf H).map H.subtype := (key _ (hfH n₀)).symm
    _ = ((f m).subgroupOf H).map H.subtype := by rw [hn₀ m hm]
    _ = f m := key _ (hfH m)

private theorem loc_pCoreOf_stab_inf_ballStab_le {β γ : CosetGeom G₀ G₁ G₂} (h : γ ∈ nbrs β) :
    pCoreOf 2 (stab β) ⊓ ballStab 1 γ ≤ pCoreOf 2 (stab β ⊓ stab γ) ⊓ ballStab 1 γ ∧
      pCoreOf 2 (stab β ⊓ stab γ) ⊓ ballStab 1 γ ≤ pCoreOf 2 (ballStab 1 γ) := by
  have hadj : (graph G₀ G₁ G₂).Adj β γ := h
  have hβ : ballStab 1 γ ≤ stab β :=
    ballStab_le_stab_of_dist_le (by rw [dist_comm]; exact (dist_eq_one_iff_adj.mpr hadj).le)
  have hγ : ballStab 1 γ ≤ stab γ := ballStab_le_stab 1 γ
  refine ⟨fun x hx => ⟨loc_pCoreOf_inf_le (inf_le_left : stab β ⊓ stab γ ≤ stab β)
    ⟨hx.1, hβ hx.2, hγ hx.2⟩, hx.2⟩, ?_⟩
  refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((loc_pCoreOf_isPGroup 2 _).to_le inf_le_left)
  refine F7.le_normalizer_inf ?_ Subgroup.le_normalizer
  exact (le_inf hβ hγ).trans (le_normalizer_pCoreOf 2 _)

private theorem loc_pCoreOf_ballStab_le (hG : G₀ = G₁ ⊔ G₂) {n : ℕ} (hn : 0 < n)
    {α γ δ : CosetGeom G₀ G₁ G₂} (hγ : γ ∈ ballLT n α) (hδ : δ ∈ nbrs γ) :
    pCoreOf 2 (ballStab n α) ≤ pCoreOf 2 (ballStab 1 γ) ∧
      pCoreOf 2 (ballStab n α) ≤ pCoreOf 2 (stab γ ⊓ stab δ) := by
  have key : ∀ d : ℕ, ∀ γ : CosetGeom G₀ G₁ G₂, dist α γ = d → d < n →
      pCoreOf 2 (ballStab n α) ≤ pCoreOf 2 (ballStab 1 γ) := by
    intro d
    induction d with
    | zero =>
      intro γ hd _
      obtain rfl : α = γ := (dist_eq_zero_iff hG).mp hd
      exact loc_pCoreOf_mono (ballStab_antitone α (Nat.succ_le_of_lt hn))
        ((ballStab_le_stab 1 α).trans (le_normalizer_ballStab n α))
    | succ d ih =>
      intro γ hd hdn
      obtain ⟨β, hβ, hdβ⟩ := exists_adj_dist_eq hG hd
      have h1 : pCoreOf 2 (ballStab n α) ≤ pCoreOf 2 (ballStab 1 β) := ih β hdβ (by omega)
      have h2 : pCoreOf 2 (ballStab 1 β) ≤ pCoreOf 2 (stab β) :=
        loc_pCoreOf_mono (ballStab_le_stab 1 β) (le_normalizer_ballStab 1 β)
      have h3 : pCoreOf 2 (ballStab n α) ≤ ballStab 1 γ := by
        refine (pCoreOf_le 2 _).trans ?_
        intro x hx
        refine mem_ballStab.mpr fun δ hδ => mem_ballStab.mp hx δ ?_
        have := dist_triangle hG α γ δ
        omega
      have h4 := loc_pCoreOf_stab_inf_ballStab_le (β := β) (γ := γ) hβ.symm
      intro x hx
      exact h4.2 (h4.1 ⟨h2 (h1 hx), h3 hx⟩)
  have h1 := key (dist α γ) γ rfl hγ
  refine ⟨h1, h1.trans ?_⟩
  have hadj : (graph G₀ G₁ G₂).Adj γ δ := hδ
  have hle : ballStab 1 γ ≤ stab γ ⊓ stab δ :=
    le_inf (ballStab_le_stab 1 γ) (ballStab_le_stab_of_dist_le (dist_eq_one_iff_adj.mpr hadj).le)
  exact loc_pCoreOf_mono hle (inf_le_left.trans (le_normalizer_ballStab 1 γ))

private theorem loc_isSylowTwoOf_pCoreOf_le {T H : Subgroup G} (h : IsSylowTwoOf T H) :
    pCoreOf 2 H ≤ T := by
  obtain ⟨S, hS⟩ := F7.isSylowTwoOf_exists_sylow h
  have : (pCore 2 H).Normal := CFSG.pCore_normal (p := 2) (G := ↥H)
  have hle : pCore 2 H ≤ (S : Subgroup H) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).le_sylow_of_normal S
  rintro _ ⟨y, hy, rfl⟩
  have := hle hy
  rw [hS] at this
  simpa [Subgroup.mem_subgroupOf] using this

private theorem loc_isSylowTwoOf_pCoreOf_le_pCoreOf {T H K : Subgroup G} (hT : IsSylowTwoOf T H)
    (hTK : T ≤ K) (hKH : K ≤ H) : pCoreOf 2 H ≤ pCoreOf 2 K :=
  le_pCoreOf_of_le_normalizer 2 ((loc_isSylowTwoOf_pCoreOf_le hT).trans hTK)
    (hKH.trans (le_normalizer_pCoreOf 2 H)) (loc_pCoreOf_isPGroup 2 H)

private theorem loc_isSylowTwoOf_exists_conj_le {T H : Subgroup G} [Finite H]
    (h : IsSylowTwoOf T H) {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    ∃ x ∈ H, P ≤ conjSub x T := by
  obtain ⟨S, hS⟩ := F7.isSylowTwoOf_exists_sylow h
  have hP' : IsPGroup 2 (P.subgroupOf H) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq H S Q
  refine ⟨x, x.2, fun y hy => ?_⟩
  have h1 : (⟨y, hPH hy⟩ : H) ∈ Q := hQ (by simpa [Subgroup.mem_subgroupOf] using hy)
  rw [← hx] at h1
  have h2 : (⟨y, hPH hy⟩ : H) ∈ ((x • S : Sylow 2 H) : Subgroup H) := h1
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
  have h3 : (MulAut.conj x)⁻¹ • (⟨y, hPH hy⟩ : H) ∈ (S : Subgroup H) := h2
  rw [hS] at h3
  rw [mem_conjSub]
  simpa [Subgroup.mem_subgroupOf, MulAut.conj_inv_apply, mul_assoc] using h3

private theorem loc_relIndex_sup_eq_of_le_normalizer {D T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

private theorem loc_not_two_dvd_relIndex_inf {T H D : Subgroup G} [Finite T] (hTH : T ≤ H)
    (hDH : D ≤ H) (hT : ¬ 2 ∣ T.relIndex H) (hTN : T ≤ Subgroup.normalizer (D : Set G)) :
    ¬ 2 ∣ (T ⊓ D).relIndex D := by
  have h1 : (T ⊓ D).relIndex T * T.relIndex (T ⊔ D) = (T ⊓ D).relIndex (T ⊔ D) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
  have h2 : (T ⊓ D).relIndex D * D.relIndex (T ⊔ D) = (T ⊓ D).relIndex (T ⊔ D) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
  have h3 : D.relIndex (T ⊔ D) = (T ⊓ D).relIndex T :=
    (loc_relIndex_sup_eq_of_le_normalizer hTN).trans (Subgroup.inf_relIndex_left T D).symm
  have h4 : 0 < (T ⊓ D).relIndex T :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := ((T ⊓ D).subgroupOf T)))
  have h5 : (T ⊓ D).relIndex D = T.relIndex (T ⊔ D) := by
    refine Nat.eq_of_mul_eq_mul_left h4 ?_
    rw [h3] at h2
    rw [mul_comm ((T ⊓ D).relIndex T) ((T ⊓ D).relIndex D), h2, ← h1]
  rw [h5]
  intro hd
  apply hT
  rw [← Subgroup.relIndex_mul_relIndex T (T ⊔ D) H le_sup_left (sup_le hTH hDH)]
  exact hd.mul_right _

private theorem loc_isSylowTwoOf_inf_normal {T H N : Subgroup G} [Finite H] (h : IsSylowTwoOf T H)
    (hNH : N ≤ H) (hTN : T ≤ Subgroup.normalizer (N : Set G)) : IsSylowTwoOf (T ⊓ N) N := by
  haveI : Finite T := loc_finite_of_le h.1
  exact isSylowTwoOf_of_relIndex inf_le_right (h.2.1.to_le inf_le_left)
    (loc_not_two_dvd_relIndex_inf h.1 hNH (isSylowTwoOf_odd_relIndex h) hTN)

private theorem loc_oTwoPrime_eq_of_normal_sylow {Q X : Subgroup G} [Finite X]
    (hQ : IsSylowTwoOf Q X) (hn : X ≤ Subgroup.normalizer (Q : Set G)) : oTwoPrime X = Q := by
  refine le_antisymm ?_ (le_oTwoPrime_of_isPGroup hQ.2.1 hQ.1)
  rw [oTwoPrime, Subgroup.closure_le]
  rintro x ⟨hxX, n, hn2⟩
  have hz : IsPGroup 2 (Subgroup.zpowers x) := by
    have hd : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, hk]
  have hzX : Subgroup.zpowers x ≤ X := by
    rw [Subgroup.zpowers_le]; exact hxX
  obtain ⟨h, hhX, hle⟩ := loc_isSylowTwoOf_exists_conj_le hQ hzX hz
  have hx' : x ∈ conjSub h Q := hle (Subgroup.mem_zpowers x)
  rw [mem_conjSub] at hx'
  have := (Subgroup.mem_normalizer_iff.mp (hn hhX) (h⁻¹ * x * h)).mp hx'
  simpa [mul_assoc] using this

private theorem loc_pCoreOf_stab_eq (hyp : AmalgamHyp G₀ G₁ G₂ T) {α β : CosetGeom G₀ G₁ G₂}
    (h : β ∈ nbrs α) :
    pCoreOf 2 (stab α) = pCoreOf 2 (stab α ⊓ stab β) ⊓ ballStab 1 α := by
  have hadj : (graph G₀ G₁ G₂).Adj α β := h
  have hle : pCoreOf 2 (stab α) ≤ pCoreOf 2 (stab α ⊓ stab β) := by
    obtain ⟨S, hS, hSle⟩ := exists_isSylowTwoOf_stab_inf hyp hadj
    exact loc_isSylowTwoOf_pCoreOf_le_pCoreOf hS hSle inf_le_left
  have hle2 : pCoreOf 2 (stab α) ≤ ballStab 1 α := by
    rw [ballStab_one_eq_coreIn hyp.gen hadj]
    exact le_coreIn (pCoreOf_le 2 _) (le_normalizer_pCoreOf 2 _) (hle.trans (pCoreOf_le 2 _))
  refine le_antisymm (le_inf hle hle2) ?_
  have h4 := (loc_pCoreOf_stab_inf_ballStab_le (β := β) (γ := α) hadj.symm).2
  rw [inf_comm (stab β) (stab α)] at h4
  exact h4.trans (loc_pCoreOf_mono (ballStab_le_stab 1 α) (le_normalizer_ballStab 1 α))

private theorem loc_pCoreOf_stab_le_ballStab_one (hyp : AmalgamHyp G₀ G₁ G₂ T)
    (α : CosetGeom G₀ G₁ G₂) : pCoreOf 2 (stab α) ≤ ballStab 1 α := by
  obtain ⟨β, hβ⟩ := exists_adj α
  rw [loc_pCoreOf_stab_eq hyp hβ]
  exact inf_le_right

private theorem loc_pCoreOf_eq_inf_centralizer (hyp : AmalgamHypV G₀ G₁ G₂ T V) :
    pCoreOf 2 G₁ = T ⊓ Subgroup.centralizer (V : Set G) := by
  rw [hyp.cT]
  apply le_antisymm
  · have hD : pCoreOf 2 G₁ ≤ Subgroup.centralizer (V : Set G) := by
      refine hyp.reduced.2.2.2 (pCoreOf 2 G₁) (pCoreOf_le 2 G₁) (le_normalizer_pCoreOf 2 G₁) ?_
      intro d hd
      obtain ⟨k, hk⟩ := loc_pCoreOf_isPGroup 2 G₁ ⟨d, hd⟩
      have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      exact ⟨k, by rw [this]; exact Subgroup.one_mem _⟩
    exact le_pCoreOf_of_le_normalizer 2 (le_inf (pCoreOf_le 2 G₁) hD)
      (inf_le_left.trans (le_normalizer_pCoreOf 2 G₁)) (loc_pCoreOf_isPGroup 2 G₁)
  · exact loc_pCoreOf_mono inf_le_left (le_normalizer_inf_centralizer hyp)

private theorem loc_pCoreOf_le_centralizer (hyp : AmalgamHypV G₀ G₁ G₂ T V) :
    pCoreOf 2 G₁ ≤ Subgroup.centralizer (V : Set G) := by
  rw [loc_pCoreOf_eq_inf_centralizer hyp]
  exact inf_le_right

private theorem loc_ballStab_one_γ₀_pCoreOf (hyp : AmalgamHypV G₀ G₁ G₂ T V) :
    pCoreOf 2 (ballStab 1 (γ₀ G₀ G₁ G₂)) = pCoreOf 2 G₁ := by
  have hQ := loc_pCoreOf_eq_inf_centralizer hyp
  have hQ₂ : pCoreOf 2 G₁ ≤ G₁ ⊓ G₂ :=
    le_inf (pCoreOf_le 2 G₁) (by rw [hQ]; exact inf_le_left.trans hyp.sylow₂.1)
  have hQball : pCoreOf 2 G₁ ≤ ballStab 1 (γ₀ G₀ G₁ G₂) :=
    ((ballStab_one_γ₀ hyp.gen).2.2) ⟨hQ₂, le_normalizer_pCoreOf 2 G₁⟩
  have hbG := ballStab_one_γ₀_le hyp.toAmalgamHyp
  apply le_antisymm
  · exact loc_pCoreOf_mono hbG (le_normalizer_ballStab_γ₀ hyp.toAmalgamHyp 1)
  · exact le_pCoreOf_of_le_normalizer 2 hQball (hbG.trans (le_normalizer_pCoreOf 2 G₁))
      (loc_pCoreOf_isPGroup 2 G₁)

private theorem loc_oTwoPrime_centralizer_eq_pCoreOf [Finite G₁] (hyp : AmalgamHypV G₀ G₁ G₂ T V) :
    oTwoPrime (G₁ ⊓ Subgroup.centralizer (V : Set G)) = pCoreOf 2 (ballStab 1 (γ₀ G₀ G₁ G₂)) ∧
      pCoreOf 2 (ballStab 1 (γ₀ G₀ G₁ G₂)) = pCoreOf 2 G₁ := by
  have hball := loc_ballStab_one_γ₀_pCoreOf hyp
  refine ⟨?_, hball⟩
  have hQ := loc_pCoreOf_eq_inf_centralizer hyp
  have hsyl : IsSylowTwoOf (pCoreOf 2 G₁) (G₁ ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [hQ]
    have := loc_isSylowTwoOf_inf_normal hyp.sylow₁
      (N := G₁ ⊓ Subgroup.centralizer (V : Set G)) inf_le_left
      (hyp.sylow₁.1.trans (le_normalizer_inf_centralizer hyp))
    rwa [← inf_assoc, inf_eq_left.mpr hyp.sylow₁.1] at this
  haveI : Finite ↥(G₁ ⊓ Subgroup.centralizer (V : Set G)) := loc_finite_of_le inf_le_left
  rw [loc_oTwoPrime_eq_of_normal_sylow hsyl (inf_le_left.trans (le_normalizer_pCoreOf 2 G₁)),
    hball]

private theorem loc_V_le_ballStab_one (hyp : AmalgamHypV G₀ G₁ G₂ T V) :
    V ≤ ballStab 1 (γ₀ G₀ G₁ G₂) :=
  (V_le_pCoreOf hyp).trans ((loc_ballStab_one_γ₀_pCoreOf hyp).ge.trans (pCoreOf_le 2 _))

private theorem loc_exists_ballStab_eq_bot [Finite G₁] [Finite G₂] {T : Subgroup G}
    (hyp : AmalgamHyp G₀ G₁ G₂ T) :
    ∃ n : ℕ, 0 < n ∧ ∀ γ : CosetGeom G₀ G₁ G₂, ballStab n γ = ⊥ := by
  have hG := hyp.gen
  have h₁ := hyp.le₁
  have h₂ := hyp.le₂
  have hadj : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) := adj_γ₀_γ₁
  have hle₀ : ∀ n, ballStab n (γ₀ G₀ G₁ G₂) ≤ G₁ := fun n => by
    have := ballStab_le_stab n (γ₀ G₀ G₁ G₂)
    rwa [stab_γ₀ h₁] at this
  have hle₁ : ∀ n, ballStab n (γ₁ G₀ G₁ G₂) ≤ G₂ := fun n => by
    have := ballStab_le_stab n (γ₁ G₀ G₁ G₂)
    rwa [stab_γ₁ h₂] at this
  obtain ⟨n₀, hn₀⟩ := loc_chain_stabilizes (H := G₁) (ballStab_antitone (γ₀ G₀ G₁ G₂)) hle₀
  obtain ⟨n₁, hn₁⟩ := loc_chain_stabilizes (H := G₂) (ballStab_antitone (γ₁ G₀ G₁ G₂)) hle₁
  have e0 : ∀ m, n₀ ≤ m → ballStab n₀ (γ₀ G₀ G₁ G₂) = ballStab m (γ₀ G₀ G₁ G₂) := hn₀
  have e1 : ∀ m, n₁ ≤ m → ballStab n₁ (γ₁ G₀ G₁ G₂) = ballStab m (γ₁ G₀ G₁ G₂) := hn₁
  set n := max n₀ n₁ + 1 with hn
  have hs0 : ballStab (n + 1) (γ₀ G₀ G₁ G₂) = ballStab n (γ₀ G₀ G₁ G₂) :=
    (e0 (n + 1) (by omega)).symm.trans (e0 n (by omega))
  have hs1 : ballStab (n + 1) (γ₁ G₀ G₁ G₂) = ballStab n (γ₁ G₀ G₁ G₂) :=
    (e1 (n + 1) (by omega)).symm.trans (e1 n (by omega))
  have hK : ballStab n (γ₀ G₀ G₁ G₂) = ballStab n (γ₁ G₀ G₁ G₂) := by
    refine le_antisymm ?_ ?_
    · calc ballStab n (γ₀ G₀ G₁ G₂) = ballStab (n + 1) (γ₀ G₀ G₁ G₂) := hs0.symm
        _ ≤ ballStab n (γ₁ G₀ G₁ G₂) := ballStab_succ_le_of_adj hadj n
    · calc ballStab n (γ₁ G₀ G₁ G₂) = ballStab (n + 1) (γ₁ G₀ G₁ G₂) := hs1.symm
        _ ≤ ballStab n (γ₀ G₀ G₁ G₂) := ballStab_succ_le_of_adj hadj.symm n
  set K := ballStab n (γ₀ G₀ G₁ G₂) with hKdef
  have hKG₁ : K ≤ G₁ := hle₀ n
  have hN1 : G₁ ≤ Subgroup.normalizer (K : Set G) := by
    have := le_normalizer_ballStab n (γ₀ G₀ G₁ G₂)
    rwa [stab_γ₀ h₁] at this
  have hN2 : G₂ ≤ Subgroup.normalizer (K : Set G) := by
    have := le_normalizer_ballStab n (γ₁ G₀ G₁ G₂)
    rw [stab_γ₁ h₂, ← hK] at this
    exact this
  have hN0 : G₀ ≤ Subgroup.normalizer (K : Set G) := by
    rw [hG]; exact sup_le hN1 hN2
  have hKbot : K = ⊥ := by
    have hR : pCoreOf 2 K ≤ ⊥ := by
      rw [← hyp.o2_trivial]
      exact loc_pCoreOf_mono (hKG₁.trans h₁) hN0
    have hinf : K ⊓ pCoreOf 2 G₁ ≤ ⊥ := by
      refine le_trans ?_ hR
      rw [inf_comm]
      exact loc_pCoreOf_inf_le hKG₁
    have hcomm : ⁅K, pCoreOf 2 G₁⁆ = ⊥ := by
      refine le_bot_iff.mp (le_trans (commutator_le_inf_of_normalizes ?_ ?_) hinf)
      · exact hKG₁.trans (le_normalizer_pCoreOf 2 G₁)
      · exact (pCoreOf_le 2 G₁).trans hN1
    have hcent : K ≤ Subgroup.centralizer (pCoreOf 2 G₁ : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hle : K ≤ pCoreOf 2 G₁ := fun x hx => hyp.charTwo ⟨hKG₁ hx, hcent hx⟩
    exact le_bot_iff.mp (le_trans (le_inf le_rfl hle) hinf)
  refine ⟨n, by omega, fun γ => ?_⟩
  cases hv : vtype γ with
  | false =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hv
    rw [hg, ballStab_smul, ← hKdef, hKbot, conjSub_bot]
  | true =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hv
    rw [hg, ballStab_smul, ← hK, hKbot, conjSub_bot]

private theorem loc_critDist_spec [Finite G₁] [Finite G₂] (hyp : AmalgamHypV G₀ G₁ G₂ T V)
    (hV : V ≠ ⊥) :
    0 < critDist G₀ G₁ G₂ V ∧ V ≤ ballStab (critDist G₀ G₁ G₂ V) (γ₀ G₀ G₁ G₂) ∧
      ¬ V ≤ ballStab (critDist G₀ G₁ G₂ V + 1) (γ₀ G₀ G₁ G₂) := by
  set S := {n : ℕ | 0 < n ∧ V ≤ ballStab n (γ₀ G₀ G₁ G₂)} with hS
  have hne : S.Nonempty := ⟨1, Nat.one_pos, loc_V_le_ballStab_one hyp⟩
  obtain ⟨n, -, hbot⟩ := loc_exists_ballStab_eq_bot hyp.toAmalgamHyp
  have hbdd : BddAbove S := by
    refine ⟨n, fun m hm => ?_⟩
    by_contra hlt
    push Not at hlt
    have : V ≤ ballStab n (γ₀ G₀ G₁ G₂) := hm.2.trans (ballStab_antitone _ hlt.le)
    rw [hbot] at this
    exact hV (le_bot_iff.mp this)
  have hmem : sSup S ∈ S := Nat.sSup_mem hne hbdd
  refine ⟨hmem.1, hmem.2, fun h => ?_⟩
  have : critDist G₀ G₁ G₂ V + 1 ∈ S := ⟨Nat.succ_pos _, h⟩
  have := le_csSup hbdd this
  have hb : critDist G₀ G₁ G₂ V = sSup S := rfl
  omega

private theorem loc_le_critDist [Finite G₁] [Finite G₂] (hyp : AmalgamHypV G₀ G₁ G₂ T V)
    (hV : V ≠ ⊥) {m : ℕ} (hm : 0 < m) (h : V ≤ ballStab m (γ₀ G₀ G₁ G₂)) :
    m ≤ critDist G₀ G₁ G₂ V := by
  obtain ⟨n, -, hbot⟩ := loc_exists_ballStab_eq_bot hyp.toAmalgamHyp
  have hbdd : BddAbove {n : ℕ | 0 < n ∧ V ≤ ballStab n (γ₀ G₀ G₁ G₂)} := by
    refine ⟨n, fun m hm => ?_⟩
    by_contra hlt
    push Not at hlt
    have : V ≤ ballStab n (γ₀ G₀ G₁ G₂) := hm.2.trans (ballStab_antitone _ hlt.le)
    rw [hbot] at this
    exact hV (le_bot_iff.mp this)
  exact le_csSup hbdd ⟨hm, h⟩

private theorem loc_V_le_stab_of_dist_le [Finite G₁] [Finite G₂] (hyp : AmalgamHypV G₀ G₁ G₂ T V)
    (hV : V ≠ ⊥) {δ : CosetGeom G₀ G₁ G₂} (h : dist (γ₀ G₀ G₁ G₂) δ ≤ critDist G₀ G₁ G₂ V) :
    V ≤ stab δ :=
  (loc_critDist_spec hyp hV).2.1.trans (ballStab_le_stab_of_dist_le h)

private theorem loc_V_le_pCoreOf_of_dist_lt [Finite G₁] [Finite G₂] (hyp : AmalgamHypV G₀ G₁ G₂ T V)
    (hV : V ≠ ⊥) {γ δ : CosetGeom G₀ G₁ G₂} (hγ : γ ∈ ballLT (critDist G₀ G₁ G₂ V) (γ₀ G₀ G₁ G₂))
    (hδ : δ ∈ nbrs γ) :
    V ≤ pCoreOf 2 (ballStab 1 γ) ∧ V ≤ pCoreOf 2 (stab γ ⊓ stab δ) := by
  obtain ⟨hb0, hVb, -⟩ := loc_critDist_spec hyp hV
  have hV2 : V ≤ pCoreOf 2 (ballStab (critDist G₀ G₁ G₂ V) (γ₀ G₀ G₁ G₂)) :=
    le_pCoreOf_of_le_normalizer 2 hVb
      ((ballStab_le_stab _ _).trans ((stab_γ₀ hyp.le₁).le.trans hyp.normalizes)) hyp.isPGroup
  have := loc_pCoreOf_ballStab_le hyp.gen hb0 hγ hδ
  exact ⟨hV2.trans this.1, hV2.trans this.2⟩

private theorem loc_exists_dist_eq_critDist_not_le [Finite G₁] [Finite G₂]
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) :
    ∃ α : CosetGeom G₀ G₁ G₂, dist (γ₀ G₀ G₁ G₂) α = critDist G₀ G₁ G₂ V ∧
      ¬ V ≤ ballStab 1 α := by
  obtain ⟨hb0, hVb, hVb1⟩ := loc_critDist_spec hyp hV
  have : ∃ β : CosetGeom G₀ G₁ G₂, dist (γ₀ G₀ G₁ G₂) β ≤ critDist G₀ G₁ G₂ V + 1 ∧
      ¬ V ≤ stab β := by
    by_contra hcon
    push Not at hcon
    exact hVb1 (fun x hx => mem_ballStab.mpr fun β hβ => hcon β hβ hx)
  obtain ⟨β, hβ1, hβ2⟩ := this
  have hβ : dist (γ₀ G₀ G₁ G₂) β = critDist G₀ G₁ G₂ V + 1 := by
    by_contra hne
    exact hβ2 (loc_V_le_stab_of_dist_le hyp hV (by omega))
  obtain ⟨α, hαβ, hα⟩ := exists_adj_dist_eq hyp.gen hβ
  refine ⟨α, hα, fun hle => hβ2 ?_⟩
  have hadj : (graph G₀ G₁ G₂).Adj α β := hαβ.symm
  exact hle.trans (ballStab_le_stab_of_dist_le (dist_eq_one_iff_adj.mpr hadj).le)

private theorem loc_isLeast_critDist [Finite G₁] [Finite G₂] (hyp : AmalgamHypV G₀ G₁ G₂ T V)
    (hV : V ≠ ⊥) :
    IsLeast {n : ℕ | ∃ γ ∈ sphere n (γ₀ G₀ G₁ G₂), ¬ V ≤ ballStab 1 γ} (critDist G₀ G₁ G₂ V) := by
  refine ⟨?_, fun n ⟨γ, hγ, hVγ⟩ => ?_⟩
  · obtain ⟨α, hα, hVα⟩ := loc_exists_dist_eq_critDist_not_le hyp hV
    exact ⟨α, hα, hVα⟩
  · by_contra hlt
    push Not at hlt
    obtain ⟨δ, hδ⟩ := exists_adj γ
    have hγ' : γ ∈ ballLT (critDist G₀ G₁ G₂ V) (γ₀ G₀ G₁ G₂) := by
      show dist (γ₀ G₀ G₁ G₂) γ < _
      have : dist (γ₀ G₀ G₁ G₂) γ = n := hγ
      omega
    exact hVγ ((loc_V_le_pCoreOf_of_dist_lt hyp hV hγ' hδ).1.trans (pCoreOf_le 2 _))

private theorem loc_V_le_ballStab_one_of_W0 (hyp : AmalgamHyp G₀ G₁ G₂ T) (hV2 : IsPGroup 2 V)
    {γ' : CosetGeom G₀ G₁ G₂} (hfin : Finite (stab γ')) (hT : IsSylowTwoOf T (stab γ'))
    (g : G₀) (hW : weakClosureW0 T V ≤ pCoreOf 2 (stab γ')) (hVγ : V ≤ stab (g • γ')) :
    V ≤ ballStab 1 (g • γ') := by
  rw [stab_smul] at hVγ
  have hP : conjSub (g : G)⁻¹ V ≤ stab γ' := (conjSub_le_iff _).mpr (by rwa [inv_inv])
  obtain ⟨x, hx, hle⟩ := loc_isSylowTwoOf_exists_conj_le hT hP (isPGroup_conjSub hV2)
  have h1 : V ≤ conjSub ((g : G) * x) T := by
    have := conjSub_mono (g : G) hle
    rwa [conjSub_inv_conjSub, ← conjSub_mul] at this
  have h2 : conjSub ((g : G) * x)⁻¹ V ≤ weakClosureW0 T V :=
    conjSub_le_weakClosureW0 ((conjSub_le_iff _).mpr (by simpa using h1))
  have h3 : V ≤ conjSub ((g : G) * x) (pCoreOf 2 (stab γ')) := by
    rw [le_conjSub_iff]
    exact h2.trans hW
  have h4 : conjSub ((g : G) * x) (stab γ') = stab (g • γ') := by
    rw [conjSub_mul, F7.conjSub_eq_of_mem hx, stab_smul]
  rw [← pCoreOf_conjSub, h4] at h3
  exact h3.trans (loc_pCoreOf_stab_le_ballStab_one hyp _)

private theorem loc_even_critDist_of_weakClosureW0_le_G₂ [Finite G₁] [Finite G₂]
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) (hW : weakClosureW0 T V ≤ pCoreOf 2 G₂) :
    Even (critDist G₀ G₁ G₂ V) := by
  obtain ⟨γ, hγ, hVγ⟩ := loc_exists_dist_eq_critDist_not_le hyp hV
  by_contra hodd
  have hvt : vtype γ = true :=
    vtype_eq_true_of_odd hyp.gen (by rw [hγ]; exact Nat.not_even_iff_odd.mp hodd)
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hvt
  apply hVγ
  rw [hg]
  have hfin : Finite (stab (γ₁ G₀ G₁ G₂)) := by
    rw [stab_γ₁ hyp.le₂]; infer_instance
  refine loc_V_le_ballStab_one_of_W0 hyp.toAmalgamHyp hyp.isPGroup (γ' := γ₁ G₀ G₁ G₂) hfin ?_
    g ?_ ?_
  · rw [stab_γ₁ hyp.le₂]; exact hyp.sylow₂
  · rw [stab_γ₁ hyp.le₂]; exact hW
  · rw [← hg]; exact loc_V_le_stab_of_dist_le hyp hV hγ.le

private theorem loc_odd_critDist_of_weakClosureW0_le_G₁ [Finite G₁] [Finite G₂]
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) (hW : weakClosureW0 T V ≤ pCoreOf 2 G₁) :
    Odd (critDist G₀ G₁ G₂ V) := by
  obtain ⟨γ, hγ, hVγ⟩ := loc_exists_dist_eq_critDist_not_le hyp hV
  by_contra hodd
  have hvt : vtype γ = false :=
    vtype_eq_false_of_even hyp.gen (by rw [hγ]; exact Nat.not_odd_iff_even.mp hodd)
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hvt
  apply hVγ
  rw [hg]
  have hfin : Finite (stab (γ₀ G₀ G₁ G₂)) := by
    rw [stab_γ₀ hyp.le₁]; infer_instance
  refine loc_V_le_ballStab_one_of_W0 hyp.toAmalgamHyp hyp.isPGroup (γ' := γ₀ G₀ G₁ G₂) hfin ?_
    g ?_ ?_
  · rw [stab_γ₀ hyp.le₁]; exact hyp.sylow₁
  · rw [stab_γ₀ hyp.le₁]; exact hW
  · rw [← hg]; exact loc_V_le_stab_of_dist_le hyp hV hγ.le

private theorem loc_V_le_stab_of_mem_walk_support [Finite G₁] [Finite G₂]
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    {δ : CosetGeom G₀ G₁ G₂} (p : (graph G₀ G₁ G₂).Walk (γ₀ G₀ G₁ G₂) δ)
    (hp : p.length ≤ critDist G₀ G₁ G₂ V) {v : CosetGeom G₀ G₁ G₂} (hv : v ∈ p.support) :
    V ≤ stab v := by
  classical
  refine loc_V_le_stab_of_dist_le hyp hV ?_
  have h1 : dist (γ₀ G₀ G₁ G₂) v ≤ (p.takeUntil v hv).length := SimpleGraph.dist_le _
  have h2 := SimpleGraph.Walk.length_takeUntil_le_length p hv
  omega

private theorem loc_conjSub_V_le_pCoreOf [Finite G₁] [Finite G₂] (hyp : AmalgamHypV G₀ G₁ G₂ T V)
    (hV : V ≠ ⊥) (g : G₀) {γ δ : CosetGeom G₀ G₁ G₂}
    (hγ : dist (g • γ₀ G₀ G₁ G₂) γ < critDist G₀ G₁ G₂ V) (hδ : δ ∈ nbrs γ) :
    conjSub (g : G) V ≤ pCoreOf 2 (ballStab 1 γ) ∧
      conjSub (g : G) V ≤ pCoreOf 2 (stab γ ⊓ stab δ) := by
  have hγ' : g⁻¹ • γ ∈ ballLT (critDist G₀ G₁ G₂ V) (γ₀ G₀ G₁ G₂) := by
    show dist (γ₀ G₀ G₁ G₂) (g⁻¹ • γ) < _
    have := dist_smul g (γ₀ G₀ G₁ G₂) (g⁻¹ • γ)
    rw [smul_inv_smul] at this
    rw [← this]; exact hγ
  have hδ' : g⁻¹ • δ ∈ nbrs (g⁻¹ • γ) := (smul_adj g⁻¹).mpr hδ
  obtain ⟨h1, h2⟩ := loc_V_le_pCoreOf_of_dist_lt hyp hV hγ' hδ'
  constructor
  · have := conjSub_mono (g : G) h1
    rwa [← pCoreOf_conjSub, ← ballStab_smul, smul_inv_smul] at this
  · have := conjSub_mono (g : G) h2
    rwa [← pCoreOf_conjSub, conjSub_inf, ← stab_smul, ← stab_smul, smul_inv_smul,
      smul_inv_smul] at this

private theorem loc_commutator_V_Vv_eq_bot [Finite G₁] [Finite G₂]
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) {δ : CosetGeom G₀ G₁ G₂} (hδ : δ ∈ Γ0 G₀ G₁ G₂)
    (hd : dist (γ₀ G₀ G₁ G₂) δ < critDist G₀ G₁ G₂ V) : ⁅V, Vv V δ⁆ = ⊥ := by
  obtain ⟨g, rfl⟩ := mem_Γ0_iff_exists.mp hδ
  rw [Vv_smul_γ₀ hyp.normalizes]
  obtain ⟨nb, hnb⟩ := exists_adj (γ₀ G₀ G₁ G₂)
  have h1 := (loc_conjSub_V_le_pCoreOf hyp hV g (γ := γ₀ G₀ G₁ G₂) (δ := nb)
    (by rw [dist_comm]; exact hd) hnb).1
  have h2 := (loc_oTwoPrime_centralizer_eq_pCoreOf hyp).2
  have h3 : conjSub (g : G) V ≤ Subgroup.centralizer (V : Set G) :=
    h1.trans ((h2.le).trans (loc_pCoreOf_le_centralizer hyp))
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h3

private theorem loc_commutator_Vv_Vv_eq_bot [Finite G₁] [Finite G₂]
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) {ν μ : CosetGeom G₀ G₁ G₂}
    (hν : ν ∈ Γ0 G₀ G₁ G₂) (hμ : μ ∈ Γ0 G₀ G₁ G₂) (hd : dist ν μ < critDist G₀ G₁ G₂ V) :
    ⁅Vv V ν, Vv V μ⁆ = ⊥ := by
  obtain ⟨g, rfl⟩ := mem_Γ0_iff_exists.mp hν
  have hμ' : g⁻¹ • μ ∈ Γ0 G₀ G₁ G₂ := by
    obtain ⟨h, rfl⟩ := mem_Γ0_iff_exists.mp hμ
    exact mem_Γ0_iff_exists.mpr ⟨g⁻¹ * h, by rw [mul_smul]⟩
  have hd' : dist (γ₀ G₀ G₁ G₂) (g⁻¹ • μ) < critDist G₀ G₁ G₂ V := by
    have := dist_smul g (γ₀ G₀ G₁ G₂) (g⁻¹ • μ)
    rw [smul_inv_smul] at this
    rw [← this]; exact hd
  have h := loc_commutator_V_Vv_eq_bot hyp hV hμ' hd'
  have h' := congrArg (conjSub (g : G)) h
  rw [conjSub_bot, ← conjSub_commutator, ← Vv_smul hyp.normalizes, smul_inv_smul] at h'
  rw [Vv_smul_γ₀ hyp.normalizes]
  exact h'

private theorem loc_isElemAbelian_Vv_γ₁ [Finite G₁] [Finite G₂] (hyp : AmalgamHypV G₀ G₁ G₂ T V)
    (hV : V ≠ ⊥) (hb : 2 < critDist G₀ G₁ G₂ V) : IsElemAbelian 2 (Vv V (γ₁ G₀ G₁ G₂)) := by
  have hN := hyp.normalizes
  have e : Vv V (γ₁ G₀ G₁ G₂) = ⨆ x : {x : G₀ ⧸ G₁.subgroupOf G₀ //
      (graph G₀ G₁ G₂).Adj (γ₁ G₀ G₁ G₂) (Sum.inl x)}, Vv0 V x.1 := by
    rw [show Vv V (γ₁ G₀ G₁ G₂) = ⨆ (x : G₀ ⧸ G₁.subgroupOf G₀)
      (_ : (graph G₀ G₁ G₂).Adj (γ₁ G₀ G₁ G₂) (Sum.inl x)), Vv0 V x from Vv_inr _]
    exact iSup_subtype'
  rw [e]
  refine isElemAbelian_iSup _ (fun x => ?_) (fun i j x hx y hy => ?_)
  · exact isElemAbelian_Vv_of_mem_Γ0 (G₀ := G₀) (G₁ := G₁) (G₂ := G₂) hN hyp.elemAbelian
      (ν := Sum.inl x.1) ⟨x.1, rfl⟩
  · have hν : (Sum.inl i.1 : CosetGeom G₀ G₁ G₂) ∈ Γ0 G₀ G₁ G₂ := ⟨i.1, rfl⟩
    have hμ : (Sum.inl j.1 : CosetGeom G₀ G₁ G₂) ∈ Γ0 G₀ G₁ G₂ := ⟨j.1, rfl⟩
    have hd : dist (Sum.inl i.1 : CosetGeom G₀ G₁ G₂) (Sum.inl j.1) < critDist G₀ G₁ G₂ V := by
      have h1 := dist_triangle hyp.gen (Sum.inl i.1 : CosetGeom G₀ G₁ G₂) (γ₁ G₀ G₁ G₂)
        (Sum.inl j.1)
      have h2 : dist (Sum.inl i.1 : CosetGeom G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) = 1 := by
        rw [dist_comm]; exact dist_eq_one_iff_adj.mpr i.2
      have h3 : dist (γ₁ G₀ G₁ G₂) (Sum.inl j.1 : CosetGeom G₀ G₁ G₂) = 1 :=
        dist_eq_one_iff_adj.mpr j.2
      omega
    have hcomm := loc_commutator_Vv_Vv_eq_bot hyp hV hν hμ hd
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
    exact ((Subgroup.mem_centralizer_iff.mp this) y hy).symm

private theorem loc_Vv_γ₁_le_pCoreOf [Finite G₁] [Finite G₂] (hyp : AmalgamHypV G₀ G₁ G₂ T V)
    (hV : V ≠ ⊥) (hb : 2 ≤ critDist G₀ G₁ G₂ V) : Vv V (γ₁ G₀ G₁ G₂) ≤ pCoreOf 2 G₂ := by
  have h₂ : G₂ ≤ G₀ := hyp.le₂
  have hd1 : dist (γ₀ G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) = 1 := dist_eq_one_iff_adj.mpr adj_γ₀_γ₁
  have hγ1 : γ₁ G₀ G₁ G₂ ∈ ballLT (critDist G₀ G₁ G₂ V) (γ₀ G₀ G₁ G₂) := by
    show dist (γ₀ G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) < _
    omega
  have hδ : γ₀ G₀ G₁ G₂ ∈ nbrs (γ₁ G₀ G₁ G₂) := adj_γ₀_γ₁.symm
  have hV1 : V ≤ pCoreOf 2 (ballStab 1 (γ₁ G₀ G₁ G₂)) :=
    (loc_V_le_pCoreOf_of_dist_lt hyp hV hγ1 hδ).1
  have hle : ballStab 1 (γ₁ G₀ G₁ G₂) ≤ G₂ := by
    have := ballStab_le_stab 1 (γ₁ G₀ G₁ G₂)
    rwa [stab_γ₁ h₂] at this
  have hN : G₂ ≤ Subgroup.normalizer (ballStab 1 (γ₁ G₀ G₁ G₂) : Set G) := by
    have := le_normalizer_ballStab 1 (γ₁ G₀ G₁ G₂)
    rwa [stab_γ₁ h₂] at this
  have hVG₂ : V ≤ pCoreOf 2 G₂ := hV1.trans (loc_pCoreOf_mono hle hN)
  rw [Vv_γ₁ h₂ hyp.normalizes]
  refine conjClosure_le fun h hh z hz => ?_
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₂ hh) z).mp (hVG₂ hz)

private theorem loc_frattini_Vv_γ₁ [Finite G₁] [Finite G₂] (hyp : AmalgamHypV G₀ G₁ G₂ T V)
    (hV : V ≠ ⊥) (hb : 2 < critDist G₀ G₁ G₂ V) : frattini (Vv V (γ₁ G₀ G₁ G₂)) = ⊥ := by
  have h := loc_isElemAbelian_Vv_γ₁ hyp hV hb
  have hle : Vv V (γ₁ G₀ G₁ G₂) ≤ G₂ :=
    (loc_Vv_γ₁_le_pCoreOf hyp hV (by omega)).trans (pCoreOf_le 2 G₂)
  haveI : Finite ↥(Vv V (γ₁ G₀ G₁ G₂)) := loc_finite_of_le hle
  have : Fact (IsPGroup 2 (Vv V (γ₁ G₀ G₁ G₂))) := ⟨isPGroup_of_isElemAbelian h⟩
  exact (CFSG.frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mpr
    (isElementaryAbelian_of_isElemAbelian h)

private theorem loc_Vv_γ₁_le_pCoreOf_stab_inf [Finite G₁] [Finite G₂]
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) {γ γ' : CosetGeom G₀ G₁ G₂}
    (hγ' : γ ∈ nbrs γ') (hd : dist (γ₁ G₀ G₁ G₂) γ' + 2 = critDist G₀ G₁ G₂ V) :
    Vv V (γ₁ G₀ G₁ G₂) ≤ pCoreOf 2 (stab γ' ⊓ stab γ) := by
  rw [show Vv V (γ₁ G₀ G₁ G₂) = ⨆ (x : G₀ ⧸ G₁.subgroupOf G₀)
    (_ : (graph G₀ G₁ G₂).Adj (γ₁ G₀ G₁ G₂) (Sum.inl x)), Vv0 V x from Vv_inr _]
  refine iSup₂_le fun x hx => ?_
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [Vv0_mk hyp.normalizes]
    refine (loc_conjSub_V_le_pCoreOf hyp hV g (γ := γ') (δ := γ) ?_ hγ').2
    have h1 : dist (g • γ₀ G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) = 1 := by
      rw [smul_γ₀]; exact dist_eq_one_iff_adj.mpr hx.symm
    have := dist_triangle hyp.gen (g • γ₀ G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) γ'
    omega

private theorem loc_Vv_le_pCoreOf_stab_inf [Finite G₁] [Finite G₂]
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) {γ γ₂ : CosetGeom G₀ G₁ G₂}
    (hγ₂ : γ₂ ∈ nbrs (γ₁ G₀ G₁ G₂)) (hd : dist γ γ₂ + 2 = critDist G₀ G₁ G₂ V) :
    Vv V γ ≤ pCoreOf 2 (stab (γ₁ G₀ G₁ G₂) ⊓ stab γ₂) := by
  have hγ₂' : (γ₁ G₀ G₁ G₂) ∈ nbrs γ₂ := mem_nbrs_symm hγ₂
  rw [inf_comm]
  cases γ with
  | inl x =>
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [Vv_inl, Vv0_mk hyp.normalizes]
      refine (loc_conjSub_V_le_pCoreOf hyp hV g (γ := γ₂) (δ := γ₁ G₀ G₁ G₂) ?_ hγ₂').2
      rw [smul_γ₀]
      omega
  | inr y =>
    rw [Vv_inr]
    refine iSup₂_le fun x hx => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [Vv0_mk hyp.normalizes]
      refine (loc_conjSub_V_le_pCoreOf hyp hV g (γ := γ₂) (δ := γ₁ G₀ G₁ G₂) ?_ hγ₂').2
      have h1 : dist (g • γ₀ G₀ G₁ G₂) (Sum.inr y : CosetGeom G₀ G₁ G₂) = 1 := by
        rw [smul_γ₀]; exact dist_eq_one_iff_adj.mpr hx.symm
      have := dist_triangle hyp.gen (g • γ₀ G₀ G₁ G₂) (Sum.inr y : CosetGeom G₀ G₁ G₂) γ₂
      omega

private theorem loc_commutator_Vv_γ₁_Vv_le [Finite G₁] [Finite G₂]
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) {γ : CosetGeom G₀ G₁ G₂}
    (hgeo : dist (γ₁ G₀ G₁ G₂) γ + 1 = critDist G₀ G₁ G₂ V) (hb : 2 ≤ critDist G₀ G₁ G₂ V) :
    ⁅Vv V (γ₁ G₀ G₁ G₂), Vv V γ⁆ ≤ Vv V (γ₁ G₀ G₁ G₂) ⊓ Vv V γ := by
  obtain ⟨⟨γ', hγ', hd'⟩, ⟨γ₂, hγ₂, hd₂⟩⟩ := exists_nbrs_of_geodesic hyp.gen hgeo hb
  apply commutator_le_inf_of_normalizes
  · refine ((loc_Vv_γ₁_le_pCoreOf_stab_inf hyp hV hγ' hd').trans (pCoreOf_le 2 _)).trans ?_
    exact inf_le_right.trans (stab_le_normalizer_Vv hyp.normalizes γ)
  · refine ((loc_Vv_le_pCoreOf_stab_inf hyp hV hγ₂ hd₂).trans (pCoreOf_le 2 _)).trans ?_
    exact inf_le_left.trans (stab_le_normalizer_Vv hyp.normalizes (γ₁ G₀ G₁ G₂))

private theorem loc_quadratic_Vv_γ₁_Vv [Finite G₁] [Finite G₂] (hyp : AmalgamHypV G₀ G₁ G₂ T V)
    (hV : V ≠ ⊥) {γ : CosetGeom G₀ G₁ G₂}
    (hgeo : dist (γ₁ G₀ G₁ G₂) γ + 1 = critDist G₀ G₁ G₂ V)
    (hb : 3 ≤ critDist G₀ G₁ G₂ V) (hodd : Odd (critDist G₀ G₁ G₂ V)) :
    IsElemAbelian 2 (Vv V (γ₁ G₀ G₁ G₂)) ∧ IsElemAbelian 2 (Vv V γ) ∧
      ⁅⁅Vv V (γ₁ G₀ G₁ G₂), Vv V γ⁆, Vv V γ⁆ = ⊥ ∧
      ⁅⁅Vv V γ, Vv V (γ₁ G₀ G₁ G₂)⁆, Vv V (γ₁ G₀ G₁ G₂)⁆ = ⊥ := by
  have hA := loc_isElemAbelian_Vv_γ₁ hyp hV (by omega)
  have hvt : vtype γ = true := by
    have h1 := (vtype_eq_iff_even_dist hyp.gen (γ₁ G₀ G₁ G₂) γ).mpr
      (by obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩)
    rw [vtype_γ₁] at h1
    exact h1.symm
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hvt
  have hB : IsElemAbelian 2 (Vv V γ) := by
    rw [hg, Vv_smul hyp.normalizes]
    exact isElemAbelian_conjSub hA
  have hc := loc_commutator_Vv_γ₁_Vv_le hyp hV hgeo (by omega)
  refine ⟨hA, hB, ?_, ?_⟩
  · refine le_bot_iff.mp ((Subgroup.commutator_mono (hc.trans inf_le_right) le_rfl).trans ?_)
    rw [commutator_self_eq_bot hB]
  · have hc' : ⁅Vv V γ, Vv V (γ₁ G₀ G₁ G₂)⁆ ≤ Vv V (γ₁ G₀ G₁ G₂) := by
      rw [Subgroup.commutator_comm]; exact hc.trans inf_le_left
    refine le_bot_iff.mp ((Subgroup.commutator_mono hc' le_rfl).trans ?_)
    rw [commutator_self_eq_bot hA]

private theorem loc_commutator_V_Vv_of_even [Finite G₁] [Finite G₂]
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) (hb : Even (critDist G₀ G₁ G₂ V))
    {γ : CosetGeom G₀ G₁ G₂} (hγ : dist (γ₀ G₀ G₁ G₂) γ = critDist G₀ G₁ G₂ V)
    (hVγ : ¬ V ≤ ballStab 1 γ) :
    ⁅V, Vv V γ⁆ ≠ ⊥ ∧ ⁅V, Vv V γ⁆ ≤ V ⊓ Vv V γ ∧ Vv V γ ≤ G₁ ∧
      ⁅⁅V, Vv V γ⁆, Vv V γ⁆ = ⊥ := by
  have hN := hyp.normalizes
  have hvt : vtype γ = false := vtype_eq_false_of_even hyp.gen (by rw [hγ]; exact hb)
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hvt
  subst hg
  rw [Vv_smul_γ₀ hN]
  have hVstab0 : V ≤ stab (g • γ₀ G₀ G₁ G₂) := loc_V_le_stab_of_dist_le hyp hV hγ.le
  have hVstab : V ≤ conjSub (g : G) G₁ := by
    rw [stab_smul, stab_γ₀ hyp.le₁] at hVstab0
    exact hVstab0
  have hVγG₁ : conjSub (g : G) V ≤ G₁ := by
    have h1 : dist (γ₀ G₀ G₁ G₂) (g⁻¹ • γ₀ G₀ G₁ G₂) ≤ critDist G₀ G₁ G₂ V := by
      have := dist_smul g⁻¹ (γ₀ G₀ G₁ G₂) (g • γ₀ G₀ G₁ G₂)
      rw [inv_smul_smul] at this
      rw [dist_comm, this, hγ]
    have h2 := loc_V_le_stab_of_dist_le hyp hV h1
    rw [stab_smul, stab_γ₀ hyp.le₁, Subgroup.coe_inv] at h2
    exact (conjSub_le_iff _).mpr (by simpa using h2)
  have hnormV : conjSub (g : G) V ≤ Subgroup.normalizer (V : Set G) := hVγG₁.trans hN
  have hnormW : V ≤ Subgroup.normalizer (conjSub (g : G) V : Set G) :=
    hVstab.trans (conjSub_le_normalizer hN)
  have hcl : ⁅V, conjSub (g : G) V⁆ ≤ V ⊓ conjSub (g : G) V :=
    commutator_le_inf_of_normalizes hnormW hnormV
  have hWabel : IsElemAbelian 2 (conjSub (g : G) V) := isElemAbelian_conjSub hyp.elemAbelian
  refine ⟨fun hbot => ?_, hcl, hVγG₁, ?_⟩
  · have hcent : V ≤ Subgroup.centralizer (conjSub (g : G) V : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have h1 : V ≤ oTwoPrime (stab (g • γ₀ G₀ G₁ G₂) ⊓
        Subgroup.centralizer (conjSub (g : G) V : Set G)) :=
      le_oTwoPrime_of_isPGroup hyp.isPGroup (le_inf hVstab0 hcent)
    have h2 : oTwoPrime (stab (g • γ₀ G₀ G₁ G₂) ⊓
        Subgroup.centralizer (conjSub (g : G) V : Set G)) =
        pCoreOf 2 (ballStab 1 (g • γ₀ G₀ G₁ G₂)) := by
      rw [stab_smul, stab_γ₀ hyp.le₁, conjSub_centralizer, ← conjSub_inf, ← conjSub_oTwoPrime,
        (loc_oTwoPrime_centralizer_eq_pCoreOf hyp).1, ← pCoreOf_conjSub, ← ballStab_smul]
    exact hVγ (h1.trans (h2.le.trans (pCoreOf_le 2 _)))
  · refine le_bot_iff.mp ((Subgroup.commutator_mono (hcl.trans inf_le_right) le_rfl).trans ?_)
    rw [commutator_self_eq_bot hWabel]

private theorem loc_odd_critDist_of_not_isFFModule [Finite G₁] [Finite G₂]
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    (hFF : ¬ @IsFFModule V (commGroupOfElemAbelian hyp.elemAbelian) (autOn G₁ V)) :
    Odd (critDist G₀ G₁ G₂ V) := by
  by_contra hodd
  have hb : Even (critDist G₀ G₁ G₂ V) := Nat.not_odd_iff_even.mp hodd
  obtain ⟨γ, hγ, hVγ⟩ := loc_exists_dist_eq_critDist_not_le hyp hV
  obtain ⟨hnt, -, hG1, -⟩ := loc_commutator_V_Vv_of_even hyp hV hb hγ hVγ
  have hN := hyp.normalizes
  have hvt : vtype γ = false := vtype_eq_false_of_even hyp.gen (by rw [hγ]; exact hb)
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hvt
  subst hg
  rw [Vv_smul_γ₀ hN] at hnt hG1
  have hVstab : V ≤ conjSub (g : G) G₁ := by
    have := loc_V_le_stab_of_dist_le hyp hV hγ.le
    rwa [stab_smul, stab_γ₀ hyp.le₁] at this
  apply hFF
  by_cases hle : Nat.card (conjSub (g : G) V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) ≤
      Nat.card (V ⊓ Subgroup.centralizer (conjSub (g : G) V : Set G) : Subgroup G)
  · exact isFFModule_of_card_le hyp.elemAbelian hG1 hN (isElemAbelian_conjSub hyp.elemAbelian)
      hnt (card_conjSub _ _).symm hle
  · push Not at hle
    have hW'G : conjSub (g : G)⁻¹ V ≤ G₁ := by
      rw [conjSub_le_iff, inv_inv]; exact hVstab
    have hnt' : ⁅V, conjSub (g : G)⁻¹ V⁆ ≠ ⊥ := by
      intro h
      apply hnt
      have h' := congrArg (conjSub (g : G)) h
      rw [conjSub_bot, ← conjSub_commutator, conjSub_inv_conjSub] at h'
      rwa [Subgroup.commutator_comm]
    have e1 : Nat.card (conjSub (g : G)⁻¹ V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) =
        Nat.card (V ⊓ Subgroup.centralizer (conjSub (g : G) V : Set G) : Subgroup G) := by
      rw [← card_conjSub (g : G), conjSub_inf, conjSub_inv_conjSub, conjSub_centralizer]
    have e2 : Nat.card (V ⊓ Subgroup.centralizer (conjSub (g : G)⁻¹ V : Set G) : Subgroup G) =
        Nat.card (conjSub (g : G) V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
      rw [← card_conjSub (g : G)⁻¹ (conjSub (g : G) V ⊓ Subgroup.centralizer (V : Set G)),
        conjSub_inf, conjSub_conjSub_inv, ← conjSub_centralizer]
    exact isFFModule_of_card_le hyp.elemAbelian hW'G hN (isElemAbelian_conjSub hyp.elemAbelian)
      hnt' (card_conjSub _ _).symm (by rw [e1, e2]; exact hle.le)

private theorem loc_two_le_critDist_of_le_pCoreOf [Finite G₁] [Finite G₂]
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) (hVG₂ : V ≤ pCoreOf 2 G₂) :
    2 ≤ critDist G₀ G₁ G₂ V := by
  have hN := hyp.normalizes
  obtain ⟨hb0, -, -⟩ := loc_critDist_spec hyp hV
  have hb1 : critDist G₀ G₁ G₂ V ≠ 1 := by
    intro hb1
    obtain ⟨α, hα, hVα⟩ := loc_exists_dist_eq_critDist_not_le hyp hV
    rw [hb1] at hα
    have hαn : α ∈ nbrs (γ₀ G₀ G₁ G₂) := (dist_eq_one_iff_adj.mp hα)
    have hγ₁n : γ₁ G₀ G₁ G₂ ∈ nbrs (γ₀ G₀ G₁ G₂) := adj_γ₀_γ₁
    obtain ⟨x, hx, hxγ⟩ := stab_transitive_on_nbrs hγ₁n hαn
    apply hVα
    rw [← hxγ, ballStab_smul, le_conjSub_iff]
    have hxG₁ : (x : G) ∈ G₁ := by rwa [stab_γ₀ hyp.le₁] at hx
    have hV' : conjSub (x : G)⁻¹ V = V := F7.conjSub_eq_of_mem_normalizer (inv_mem (hN hxG₁))
    rw [hV']
    refine hVG₂.trans ?_
    have := loc_pCoreOf_stab_le_ballStab_one hyp.toAmalgamHyp (γ₁ G₀ G₁ G₂)
    rwa [stab_γ₁ hyp.le₂] at this
  omega

private theorem loc_isElemAbelian_conjClosure_of_not_isFFModule [Finite G₁] [Finite G₂]
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) (hVG₂ : V ≤ pCoreOf 2 G₂)
    (hFF : ¬ @IsFFModule V (commGroupOfElemAbelian hyp.elemAbelian) (autOn G₁ V)) :
    IsElemAbelian 2 (conjClosure V G₂) := by
  have hodd := loc_odd_critDist_of_not_isFFModule hyp hV hFF
  have hb2 := loc_two_le_critDist_of_le_pCoreOf hyp hV hVG₂
  have hb3 : 2 < critDist G₀ G₁ G₂ V := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have h := loc_isElemAbelian_Vv_γ₁ hyp hV hb3
  rwa [Vv_γ₁ hyp.le₂ hyp.normalizes] at h

private theorem loc_critDist_eq_one_of_not_le_pCoreOf [Finite G₁] [Finite G₂]
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) (h : ¬ V ≤ pCoreOf 2 G₂) :
    critDist G₀ G₁ G₂ V = 1 := by
  have hb0 := (loc_critDist_spec hyp hV).1
  have hle : critDist G₀ G₁ G₂ V ≤ 1 := by
    refine (loc_isLeast_critDist hyp hV).2 ⟨γ₁ G₀ G₁ G₂, ?_, ?_⟩
    · exact dist_eq_one_iff_adj.mpr adj_γ₀_γ₁
    · intro hV'
      apply h
      have hle1 : ballStab 1 (γ₁ G₀ G₁ G₂) ≤ G₂ := by
        have := ballStab_le_stab 1 (γ₁ G₀ G₁ G₂)
        rwa [stab_γ₁ hyp.le₂] at this
      have hN2 : G₂ ≤ Subgroup.normalizer (ballStab 1 (γ₁ G₀ G₁ G₂) : Set G) := by
        have := le_normalizer_ballStab 1 (γ₁ G₀ G₁ G₂)
        rwa [stab_γ₁ hyp.le₂] at this
      have hbG₁ : ballStab 1 (γ₁ G₀ G₁ G₂) ≤ G₁ :=
        (((ballStab_one_γ₁ hyp.gen).1).le.trans (coreIn_le_right _ _)).trans inf_le_left
      have hV2 : V ≤ pCoreOf 2 (ballStab 1 (γ₁ G₀ G₁ G₂)) :=
        le_pCoreOf_of_le_normalizer 2 hV' (hbG₁.trans hyp.normalizes) hyp.isPGroup
      exact hV2.trans (loc_pCoreOf_mono hle1 hN2)
  omega

private theorem loc_critDist_eq_two_of_nonabelian [Finite G₁] [Finite G₂]
    (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥) (hVG₂ : V ≤ pCoreOf 2 G₂)
    (hna : ¬ ∀ x ∈ Vv V (γ₁ G₀ G₁ G₂), ∀ y ∈ Vv V (γ₁ G₀ G₁ G₂), x * y = y * x) :
    critDist G₀ G₁ G₂ V = 2 := by
  have hb2 := loc_two_le_critDist_of_le_pCoreOf hyp hV hVG₂
  by_contra hne
  have hb3 : 2 < critDist G₀ G₁ G₂ V := by omega
  exact hna fun x hx y hy => isElemAbelian_comm (loc_isElemAbelian_Vv_γ₁ hyp hV hb3) hx hy

end Loc

end CFSG.Quasithin.CosetGeom

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom CFSG.Quasithin.F7
open CFSG.ASVolI.ChF
open scoped Pointwise

private theorem asvol_amalgam {G : Type} [Group G] {G₀ G₁ G₂ T : Subgroup G}
    (h : HypF_7_1 G₀ G₁ G₂ T) : AmalgamHyp G₀ G₁ G₂ T :=
  ⟨h.gen, h.charTwo, h.sylow₁, h.sylow₂, h.o2_trivial⟩

private theorem asvol_amalgamV {G : Type} [Group G] {G₀ G₁ G₂ T V : Subgroup G}
    (h : HypF_7_6 G₀ G₁ G₂ T V) : AmalgamHypV G₀ G₁ G₂ T V :=
  ⟨asvol_amalgam h.toHypF_7_1, h.reduced, h.cT⟩

@[expose] def F_7_3 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T : Subgroup G), HypF_7_1 G₀ G₁ G₂ T →
    ∀ γ : CosetGeom G₀ G₁ G₂,
      (MulAction.orbit G₀ (γ₀ G₀ G₁ G₂) = Γ0 G₀ G₁ G₂ ∧
        MulAction.orbit G₀ (γ₁ G₀ G₁ G₂) = Γ1 G₀ G₁ G₂ ∧
        Γ0 G₀ G₁ G₂ ∪ Γ1 G₀ G₁ G₂ = Set.univ ∧ Disjoint (Γ0 G₀ G₁ G₂) (Γ1 G₀ G₁ G₂)) ∧
      ((∀ u v : CosetGeom G₀ G₁ G₂, (graph G₀ G₁ G₂).Adj u v →
          ∃ g : G₀, g • ({γ₀ G₀ G₁ G₂, γ₁ G₀ G₁ G₂} : Set (CosetGeom G₀ G₁ G₂)) = {u, v}) ∧
        (∀ g : G₀, g • ({γ₀ G₀ G₁ G₂, γ₁ G₀ G₁ G₂} : Set (CosetGeom G₀ G₁ G₂)) =
            {γ₀ G₀ G₁ G₂, γ₁ G₀ G₁ G₂} ↔ (g : G) ∈ G₁ ⊓ G₂)) ∧
      (graph G₀ G₁ G₂).Connected ∧
      ((∀ x : G₀, (x : G) ∈ stab γ ↔ x • γ = γ) ∧ stab γ ≤ G₀ ∧
        (∀ g : G₀, stab (g • γ₀ G₀ G₁ G₂) = conjSub (g : G) G₁ ∧
          stab (g • γ₁ G₀ G₁ G₂) = conjSub (g : G) G₂) ∧
        stab (γ₀ G₀ G₁ G₂) = G₁ ∧ stab (γ₁ G₀ G₁ G₂) = G₂) ∧
      (∀ δ ∈ nbrs γ, ∀ δ' ∈ nbrs γ, ∃ g : G₀, (g : G) ∈ stab γ ∧ g • δ = δ') ∧
      (∀ n : ℕ, ballStab n γ ≤ stab γ ∧ ((ballStab n γ).subgroupOf (stab γ)).Normal) ∧
      ((ballStab 1 (γ₀ G₀ G₁ G₂) = coreIn (G₁ ⊓ G₂) G₁ ∧
          IsGreatest {N : Subgroup G | N ≤ G₁ ⊓ G₂ ∧ (N.subgroupOf G₁).Normal}
            (ballStab 1 (γ₀ G₀ G₁ G₂))) ∧
        (ballStab 1 (γ₁ G₀ G₁ G₂) = coreIn (G₁ ⊓ G₂) G₂ ∧
          IsGreatest {N : Subgroup G | N ≤ G₁ ⊓ G₂ ∧ (N.subgroupOf G₂).Normal}
            (ballStab 1 (γ₁ G₀ G₁ G₂)))) ∧
      (∃ n : ℕ, 0 < n ∧ ∀ δ : CosetGeom G₀ G₁ G₂, ballStab n δ = ⊥)

theorem as_F_7_3 : F_7_3 := by
  intro G _ G₀ G₁ G₂ T hyp γ
  haveI := hyp.finite₁
  haveI := hyp.finite₂
  have hA := asvol_amalgam hyp
  have h₁ : G₁ ≤ G₀ := hA.le₁
  have h₂ : G₂ ≤ G₀ := hA.le₂
  have hG : G₀ = G₁ ⊔ G₂ := hyp.gen
  have hset0 : {N : Subgroup G | N ≤ G₁ ⊓ G₂ ∧ (N.subgroupOf G₁).Normal} =
      {N : Subgroup G | N ≤ G₁ ⊓ G₂ ∧ G₁ ≤ Subgroup.normalizer (N : Set G)} := by
    ext N
    exact ⟨fun h => ⟨h.1, (Subgroup.normal_subgroupOf_iff_le_normalizer (h.1.trans inf_le_left)).mp h.2⟩,
      fun h => ⟨h.1, (Subgroup.normal_subgroupOf_iff_le_normalizer (h.1.trans inf_le_left)).mpr h.2⟩⟩
  have hset1 : {N : Subgroup G | N ≤ G₁ ⊓ G₂ ∧ (N.subgroupOf G₂).Normal} =
      {N : Subgroup G | N ≤ G₁ ⊓ G₂ ∧ G₂ ≤ Subgroup.normalizer (N : Set G)} := by
    ext N
    exact ⟨fun h => ⟨h.1, (Subgroup.normal_subgroupOf_iff_le_normalizer (h.1.trans inf_le_right)).mp h.2⟩,
      fun h => ⟨h.1, (Subgroup.normal_subgroupOf_iff_le_normalizer (h.1.trans inf_le_right)).mpr h.2⟩⟩
  refine ⟨⟨CFSG.Quasithin.CosetGeom.orbit_γ₀_eq_Γ0, CFSG.Quasithin.CosetGeom.orbit_γ₁_eq_Γ1,
      Set.range_inl_union_range_inr, ?_⟩,
    ⟨fun u v huv => CFSG.Quasithin.CosetGeom.exists_smul_edge_set huv,
      fun g => CFSG.Quasithin.CosetGeom.smul_edge_eq_iff h₁ h₂ g⟩,
    CFSG.Quasithin.CosetGeom.connected hG,
    ⟨fun x => ⟨CFSG.Quasithin.CosetGeom.smul_eq_of_mem_stab,
        CFSG.Quasithin.CosetGeom.mem_stab_of_smul_eq⟩,
      CFSG.Quasithin.CosetGeom.stab_le γ,
      fun g => ⟨by rw [CFSG.Quasithin.CosetGeom.stab_smul, CFSG.Quasithin.CosetGeom.stab_γ₀ h₁],
        by rw [CFSG.Quasithin.CosetGeom.stab_smul, CFSG.Quasithin.CosetGeom.stab_γ₁ h₂]⟩,
      CFSG.Quasithin.CosetGeom.stab_γ₀ h₁, CFSG.Quasithin.CosetGeom.stab_γ₁ h₂⟩,
    fun δ hδ δ' hδ' => CFSG.Quasithin.CosetGeom.stab_transitive_on_nbrs hδ hδ',
    fun n => CFSG.Quasithin.CosetGeom.ballStab_normal n γ,
    ⟨⟨(CFSG.Quasithin.CosetGeom.ballStab_one_γ₀ hG).1, ?_⟩,
      ⟨(CFSG.Quasithin.CosetGeom.ballStab_one_γ₁ hG).1, ?_⟩⟩,
    CFSG.Quasithin.CosetGeom.loc_exists_ballStab_eq_bot hA⟩
  · unfold Γ0 Γ1
    exact Set.disjoint_left.mpr (by rintro _ ⟨x, rfl⟩ ⟨y, hy⟩; exact Sum.inr_ne_inl hy)
  · rw [hset0]; exact (CFSG.Quasithin.CosetGeom.ballStab_one_γ₀ hG).2
  · rw [hset1]; exact (CFSG.Quasithin.CosetGeom.ballStab_one_γ₁ hG).2

@[expose] def F_7_4 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T : Subgroup G), HypF_7_1 G₀ G₁ G₂ T →
    ∀ β γ : CosetGeom G₀ G₁ G₂, γ ∈ nbrs β →
      pCoreOf 2 (stab β) ⊓ ballStab 1 γ ≤ pCoreOf 2 (stab β ⊓ stab γ) ⊓ ballStab 1 γ ∧
      pCoreOf 2 (stab β ⊓ stab γ) ⊓ ballStab 1 γ ≤ pCoreOf 2 (ballStab 1 γ)

theorem as_F_7_4 : F_7_4 := by
  intro G _ G₀ G₁ G₂ T hyp β γ h
  exact CFSG.Quasithin.CosetGeom.loc_pCoreOf_stab_inf_ballStab_le h

@[expose] def F_7_5 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T : Subgroup G), HypF_7_1 G₀ G₁ G₂ T →
    ∀ (α : CosetGeom G₀ G₁ G₂) (n : ℕ), 0 < n → ∀ γ ∈ ballLT n α, ∀ δ ∈ nbrs γ,
      pCoreOf 2 (ballStab n α) ≤ pCoreOf 2 (ballStab 1 γ) ∧
      pCoreOf 2 (ballStab n α) ≤ pCoreOf 2 (stab γ ⊓ stab δ)

theorem as_F_7_5 : F_7_5 := by
  intro G _ G₀ G₁ G₂ T hyp α n hn γ hγ δ hδ
  exact CFSG.Quasithin.CosetGeom.loc_pCoreOf_ballStab_le hyp.gen hn hγ hδ

@[expose] def F_7_7 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T V : Subgroup G), HypF_7_6 G₀ G₁ G₂ T V →
    (oTwoPrime (G₁ ⊓ Subgroup.centralizer (V : Set G)) = pCoreOf 2 (ballStab 1 (γ₀ G₀ G₁ G₂)) ∧
      pCoreOf 2 (ballStab 1 (γ₀ G₀ G₁ G₂)) = pCoreOf 2 G₁) ∧
    (∀ α β : CosetGeom G₀ G₁ G₂, β ∈ nbrs α →
      pCoreOf 2 (stab α) = pCoreOf 2 (stab α ⊓ stab β) ⊓ ballStab 1 α)

theorem as_F_7_7 : F_7_7 := by
  intro G _ G₀ G₁ G₂ T V hyp
  haveI := hyp.toHypF_7_1.finite₁
  haveI := hyp.toHypF_7_1.finite₂
  have hV := asvol_amalgamV hyp
  exact ⟨CFSG.Quasithin.CosetGeom.loc_oTwoPrime_centralizer_eq_pCoreOf hV,
    fun α β h => CFSG.Quasithin.CosetGeom.loc_pCoreOf_stab_eq hV.toAmalgamHyp h⟩

@[expose] def F_7_8 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T V : Subgroup G), HypF_7_6 G₀ G₁ G₂ T V → V ≠ ⊥ →
    IsGreatest {n : ℕ | 0 < n ∧ V ≤ ballStab n (γ₀ G₀ G₁ G₂)} (critDist G₀ G₁ G₂ V)

theorem as_F_7_8 : F_7_8 := by
  intro G _ G₀ G₁ G₂ T V hyp hV
  haveI := hyp.toHypF_7_1.finite₁
  haveI := hyp.toHypF_7_1.finite₂
  have hA := asvol_amalgamV hyp
  obtain ⟨hb0, hVb, -⟩ := CFSG.Quasithin.CosetGeom.loc_critDist_spec hA hV
  exact ⟨⟨hb0, hVb⟩, fun n hn => CFSG.Quasithin.CosetGeom.loc_le_critDist hA hV hn.1 hn.2⟩

@[expose] def F_7_9 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T V : Subgroup G), HypF_7_6 G₀ G₁ G₂ T V → V ≠ ⊥ →
    (∀ γ ∈ ballLT (critDist G₀ G₁ G₂ V) (γ₀ G₀ G₁ G₂), ∀ δ ∈ nbrs γ,
      V ≤ pCoreOf 2 (ballStab 1 γ) ∧ V ≤ pCoreOf 2 (stab γ ⊓ stab δ)) ∧
    (∃ α ∈ sphere (critDist G₀ G₁ G₂ V) (γ₀ G₀ G₁ G₂), ¬ V ≤ ballStab 1 α) ∧
    IsLeast {n : ℕ | ∃ γ ∈ sphere n (γ₀ G₀ G₁ G₂), ¬ V ≤ ballStab 1 γ} (critDist G₀ G₁ G₂ V) ∧
    (weakClosureW0 T V ≤ pCoreOf 2 G₂ → Even (critDist G₀ G₁ G₂ V))

theorem as_F_7_9 : F_7_9 := by
  intro G _ G₀ G₁ G₂ T V hyp hV
  haveI := hyp.toHypF_7_1.finite₁
  haveI := hyp.toHypF_7_1.finite₂
  have hA := asvol_amalgamV hyp
  refine ⟨fun γ hγ δ hδ => CFSG.Quasithin.CosetGeom.loc_V_le_pCoreOf_of_dist_lt hA hV hγ hδ,
    ?_, CFSG.Quasithin.CosetGeom.loc_isLeast_critDist hA hV,
    fun hW => CFSG.Quasithin.CosetGeom.loc_even_critDist_of_weakClosureW0_le_G₂ hA hV hW⟩
  obtain ⟨α, hα, hVα⟩ := CFSG.Quasithin.CosetGeom.loc_exists_dist_eq_critDist_not_le hA hV
  exact ⟨α, hα, hVα⟩

@[expose] def F_7_10 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T V : Subgroup G), HypF_7_6 G₀ G₁ G₂ T V → V ≠ ⊥ →
    2 ≤ critDist G₀ G₁ G₂ V →
      Vv V (γ₁ G₀ G₁ G₂) ≤ pCoreOf 2 G₂ ∧ IsPGroup 2 (Vv V (γ₁ G₀ G₁ G₂))

theorem as_F_7_10 : F_7_10 := by
  intro G _ G₀ G₁ G₂ T V hyp hV hb
  haveI := hyp.toHypF_7_1.finite₁
  haveI := hyp.toHypF_7_1.finite₂
  have hA := asvol_amalgamV hyp
  have hconj : Vv V (γ₁ G₀ G₁ G₂) ≤ pCoreOf 2 G₂ :=
    CFSG.Quasithin.CosetGeom.loc_Vv_γ₁_le_pCoreOf hA hV (by omega)
  exact ⟨hconj, (CFSG.Quasithin.CosetGeom.loc_pCoreOf_isPGroup 2 G₂).to_le hconj⟩

@[expose] def F_7_11 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T V : Subgroup G) (hyp : HypF_7_6 G₀ G₁ G₂ T V), V ≠ ⊥ →
    ∀ γ : CosetGeom G₀ G₁ G₂, dist (γ₀ G₀ G₁ G₂) γ = critDist G₀ G₁ G₂ V →
      ¬ V ≤ ballStab 1 γ →
      (∀ n : ℕ, n ≤ critDist G₀ G₁ G₂ V → ∀ δ : CosetGeom G₀ G₁ G₂,
        ∀ p : (graph G₀ G₁ G₂).Walk (γ₀ G₀ G₁ G₂) δ, p.length = n → ∀ v ∈ p.support, V ≤ stab v) ∧
      (Even (critDist G₀ G₁ G₂ V) →
        (⁅V, Vv V γ⁆ ≠ ⊥ ∧ ⁅V, Vv V γ⁆ ≤ V ⊓ Vv V γ) ∧ Vv V γ ≤ G₁ ∧
          (¬ Vv V γ ≤ Subgroup.centralizer (V : Set G) ∧ ⁅⁅V, Vv V γ⁆, Vv V γ⁆ = ⊥)) ∧
      (∀ δ ∈ Γ0 G₀ G₁ G₂, dist (γ₀ G₀ G₁ G₂) δ < critDist G₀ G₁ G₂ V → ⁅V, Vv V δ⁆ = ⊥) ∧
      (2 < critDist G₀ G₁ G₂ V → frattini ↥(Vv V (γ₁ G₀ G₁ G₂)) = ⊥) ∧
      (2 ≤ critDist G₀ G₁ G₂ V → dist (γ₁ G₀ G₁ G₂) γ + 1 = critDist G₀ G₁ G₂ V →
        ∀ γ' ∈ nbrs γ, dist (γ₁ G₀ G₁ G₂) γ' + 2 = critDist G₀ G₁ G₂ V →
          Vv V (γ₁ G₀ G₁ G₂) ≤ pCoreOf 2 (stab γ' ⊓ stab γ)) ∧
      (3 ≤ critDist G₀ G₁ G₂ V → Odd (critDist G₀ G₁ G₂ V) →
        (∀ γ₂ ∈ nbrs (γ₁ G₀ G₁ G₂), dist γ₂ γ + 2 = critDist G₀ G₁ G₂ V →
          Vv V γ ≤ pCoreOf 2 (stab (γ₁ G₀ G₁ G₂) ⊓ stab γ₂)) ∧
        (dist (γ₁ G₀ G₁ G₂) γ + 1 = critDist G₀ G₁ G₂ V →
          ⁅Vv V (γ₁ G₀ G₁ G₂), Vv V γ⁆ ≤ Vv V (γ₁ G₀ G₁ G₂) ⊓ Vv V γ ∧
          ⁅⁅Vv V (γ₁ G₀ G₁ G₂), Vv V γ⁆, Vv V γ⁆ = ⊥ ∧
          ⁅⁅Vv V γ, Vv V (γ₁ G₀ G₁ G₂)⁆, Vv V (γ₁ G₀ G₁ G₂)⁆ = ⊥)) ∧
      ((¬ @IsFFModule ↥V (commGroupOfElemAbelian hyp.reduced.2.2.1) (autOn G₁ V)) →
        Odd (critDist G₀ G₁ G₂ V)) ∧
      (V ≤ pCoreOf 2 G₂ →
        (¬ @IsFFModule ↥V (commGroupOfElemAbelian hyp.reduced.2.2.1) (autOn G₁ V)) →
          IsElemAbelian 2 (conjClosure V G₂))

theorem as_F_7_11 : F_7_11 := by
  intro G _ G₀ G₁ G₂ T V hyp hV γ hγ hVγ
  haveI := hyp.toHypF_7_1.finite₁
  haveI := hyp.toHypF_7_1.finite₂
  have hA := asvol_amalgamV hyp
  refine ⟨fun n hn δ p hp v hv =>
      CFSG.Quasithin.CosetGeom.loc_V_le_stab_of_mem_walk_support hA hV p (by omega) hv,
    fun hEven => ?_, fun δ hδ hd => CFSG.Quasithin.CosetGeom.loc_commutator_V_Vv_eq_bot hA hV hδ hd,
    fun hb => CFSG.Quasithin.CosetGeom.loc_frattini_Vv_γ₁ hA hV hb,
    fun hb hgeo γ' hγ' hd' =>
      CFSG.Quasithin.CosetGeom.loc_Vv_γ₁_le_pCoreOf_stab_inf hA hV (mem_nbrs_symm hγ') hd',
    fun h3 hodd => ⟨fun γ₂ hγ₂ hd₂ =>
        CFSG.Quasithin.CosetGeom.loc_Vv_le_pCoreOf_stab_inf hA hV hγ₂
          (by rw [CFSG.Quasithin.CosetGeom.dist_comm]; exact hd₂), fun hgeo =>
        ⟨CFSG.Quasithin.CosetGeom.loc_commutator_Vv_γ₁_Vv_le hA hV hgeo (by omega),
          (CFSG.Quasithin.CosetGeom.loc_quadratic_Vv_γ₁_Vv hA hV hgeo h3 hodd).2.2.1,
          (CFSG.Quasithin.CosetGeom.loc_quadratic_Vv_γ₁_Vv hA hV hgeo h3 hodd).2.2.2⟩⟩,
    fun hFF => CFSG.Quasithin.CosetGeom.loc_odd_critDist_of_not_isFFModule hA hV hFF,
    fun hVG₂ hFF => CFSG.Quasithin.CosetGeom.loc_isElemAbelian_conjClosure_of_not_isFFModule
      hA hV hVG₂ hFF⟩
  · have hc := CFSG.Quasithin.CosetGeom.loc_commutator_V_Vv_of_even hA hV hEven hγ hVγ
    refine ⟨⟨hc.1, hc.2.1⟩, hc.2.2.1, fun h => hc.1 ?_, hc.2.2.2⟩
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h

@[expose] def F_7_12 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T V : Subgroup G), HypF_7_6 G₀ G₁ G₂ T V → V ≠ ⊥ →
    (¬ V ≤ pCoreOf 2 G₂ → critDist G₀ G₁ G₂ V = 1) ∧
    (V ≤ pCoreOf 2 G₂ →
      ¬ (∀ x ∈ Vv V (γ₁ G₀ G₁ G₂), ∀ y ∈ Vv V (γ₁ G₀ G₁ G₂), x * y = y * x) →
      critDist G₀ G₁ G₂ V = 2)

theorem as_F_7_12 : F_7_12 := by
  intro G _ G₀ G₁ G₂ T V hyp hV
  haveI := hyp.toHypF_7_1.finite₁
  haveI := hyp.toHypF_7_1.finite₂
  have hA := asvol_amalgamV hyp
  exact ⟨fun h => CFSG.Quasithin.CosetGeom.loc_critDist_eq_one_of_not_le_pCoreOf hA hV h,
    fun hVG₂ hna => CFSG.Quasithin.CosetGeom.loc_critDist_eq_two_of_nonabelian hA hV hVG₂ hna⟩

@[expose] def F_7_13 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T V : Subgroup G), HypF_7_6 G₀ G₁ G₂ T V → V ≠ ⊥ →
    ∀ γ : CosetGeom G₀ G₁ G₂, dist (γ₀ G₀ G₁ G₂) γ = critDist G₀ G₁ G₂ V →
      ¬ V ≤ ballStab 1 γ → dist (γ₁ G₀ G₁ G₂) γ + 1 = critDist G₀ G₁ G₂ V →
      (3 ≤ critDist G₀ G₁ G₂ V ∧ Odd (critDist G₀ G₁ G₂ V)) →
      IsUniqueMaxOver G₂ T (G₂ ⊓ Subgroup.normalizer (V : Set G)) →
      E1.nParam G₂ = 1 →
      ∀ A : Subgroup G, A ≤ Vv V (γ₁ G₀ G₁ G₂) → ¬ A ≤ ballStab 1 γ →
        (∃ α ∈ nbrs γ, (A ⊓ Subgroup.normalizer (Vv V α : Set G)).relIndex A = 2) ∧
        (CFSG.SectionRank.IsSQTKCat ↥G₂ →
          ∃ α ∈ nbrs γ, (A ⊓ Subgroup.normalizer (Vv V α : Set G)).relIndex A = 2 ∧
            ∃ h : G, h ∈ stab γ ∧ conjSub h⁻¹ A ≤ stab α ∧
            ¬ IsPGroup 2 ↥(A ⊔ conjSub h⁻¹ A))

section F713


theorem as_F_7_13
    : F_7_13 := by
  intro G _ G₀ G₁ G₂ T V hyp hV γ hd hVγ hgeo ha hb hc A hA₁ hA₂
  haveI := hyp.toHypF_7_1.finite₁
  haveI := hyp.toHypF_7_1.finite₂
  have hA := asvol_amalgamV hyp
  exact CFSG.Quasithin.RonanF713.f713_main
    (CFSG.Quasithin.F7Two.claimCE1_of_invAutGenSQTK CFSG.Quasithin.F7Two.invAutGenSQTK_proved) hA
    ⟨hd, hVγ, hgeo⟩ ha.1 ha.2 hb hc hA₁ hA₂
    (isElemAbelian_mono
      (CFSG.Quasithin.CosetGeom.loc_isElemAbelian_Vv_γ₁ hA hV (by have := ha.1; omega)) hA₁)
    (fun β hβ hdβ => CFSG.Quasithin.CosetGeom.loc_Vv_γ₁_le_pCoreOf_stab_inf hA hV hβ hdβ)
    (CFSG.Quasithin.CosetGeom.loc_pCoreOf_stab_le_ballStab_one hA.toAmalgamHyp γ)

end F713

@[expose] def F_7_14 : Prop :=
  ∀ (G : Type) [Group G] (G₀ G₁ G₂ T V : Subgroup G), HypF_7_6 G₀ G₁ G₂ T V → V ≠ ⊥ →
    (weakClosureW0 T V ≤ pCoreOf 2 G₁ → critDist G₀ G₁ G₂ V % 2 = (0 + 1) % 2) ∧
    (weakClosureW0 T V ≤ pCoreOf 2 G₂ → critDist G₀ G₁ G₂ V % 2 = (1 + 1) % 2)

theorem as_F_7_14 : F_7_14 := by
  intro G _ G₀ G₁ G₂ T V hyp hV
  haveI := hyp.toHypF_7_1.finite₁
  haveI := hyp.toHypF_7_1.finite₂
  have hA := asvol_amalgamV hyp
  refine ⟨fun hW => ?_, fun hW => ?_⟩
  · obtain ⟨k, hk⟩ := CFSG.Quasithin.CosetGeom.loc_odd_critDist_of_weakClosureW0_le_G₁ hA hV hW
    omega
  · obtain ⟨k, hk⟩ := CFSG.Quasithin.CosetGeom.loc_even_critDist_of_weakClosureW0_le_G₂ hA hV hW
    omega

end CFSG.ASVolI

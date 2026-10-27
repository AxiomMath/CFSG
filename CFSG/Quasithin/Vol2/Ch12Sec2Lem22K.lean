module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22J
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22F

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def KGBorelOvergroupThree : Prop :=
  ∀ (V : Type) [Group V] [Finite V] (n : ℕ), (n = 3 ∨ n = 4 ∨ n = 5) → Nat.card V = 2 ^ n →
    (∀ x y : V, x * y = y * x) → (∀ x : V, x ^ 2 = 1) →
    ∀ (S X : Subgroup (MulAut V)) (p : ℕ), IsSylowTwoOf S ⊤ → p.Prime → p ≠ 2 →
      IsPGroup p ↥X → X ≠ ⊥ → (∀ s ∈ S, ∀ x ∈ X, ∃ x' ∈ X, ∃ s' ∈ S, s * x = x' * s') → p = 3

@[expose] def Lem12223Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H P U I : Subgroup G) (h : G) (n : ℕ),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Concl12_2_20 T L V n →
    Pre12_2_21 T L V H P U I h 3 → U ≤ pCoreOf 2 H → ¬ IsCyclic ↥P → frattini ↥P ≠ ⊥ →
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

omit [Finite G] in
theorem isSylowTwoOf_subgroupOf_of_le {S K C : Subgroup G} (hKC : K ≤ C)
    (h : IsSylowTwoOf S K) : IsSylowTwoOf (S.subgroupOf C) (K.subgroupOf C) := by
  obtain ⟨hSK, hS2, hidx⟩ := h
  refine ⟨fun x hx => hSK hx, ?_, ?_⟩
  · exact hS2.of_equiv (Subgroup.subgroupOfEquivOfLe (hSK.trans hKC)).symm
  · have h2 : ((S.subgroupOf C).subgroupOf (K.subgroupOf C)).index = (S.subgroupOf K).index :=
      Subgroup.relIndex_subgroupOf (H := S) (K := K) (L := C) hKC
    rw [h2]
    exact hidx

theorem isSylowTwoOf_map_hom {X Y : Type} [Group X] [Group Y] [Finite X] {S K : Subgroup X}
    (hS : IsSylowTwoOf S K) (f : X →* Y) : IsSylowTwoOf (S.map f) (K.map f) := by
  obtain ⟨hSK, hp, hidx⟩ := hS
  refine ⟨Subgroup.map_mono hSK, hp.map f, fun h => hidx ?_⟩
  let f' : ↥K →* ↥(K.map f) := (f.comp K.subtype).codRestrict (K.map f)
    (fun k => ⟨k, k.2, rfl⟩)
  have hf' : Function.Surjective f' := by
    rintro ⟨_, k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  have he : (S.subgroupOf K).map f' = (S.map f).subgroupOf (K.map f) := by
    ext ⟨y, hy⟩
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨k, hk, hky⟩
      rw [Subgroup.mem_subgroupOf] at hk
      exact ⟨k, hk, congrArg Subtype.val hky⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hSK hs⟩, hs, rfl⟩
  have := Subgroup.index_map_dvd (S.subgroupOf K) hf'
  rw [he] at this
  exact h.trans this

theorem prime_eq_three_of_pre (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (hKG : KGBorelOvergroupThree) {T L V H P U I : Subgroup G} {h : G} {n p : ℕ}
    (hyp : Hyp1223 G T L V) (hC : Concl12_2_20 T L V n)
    (hpre : Pre12_2_21 T L V H P U I h p)
    (hΦV : (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (V : Set G))
    (hΦnt : ∃ f ∈ (frattini ↥P).map P.subtype, ∃ x ∈ V, f * x * f⁻¹ ≠ x) : p = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, -, -, hhP, hhM, -⟩ := hpre
  set Q := pCoreOf 2 H with hQ
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  have hP1 : P ≠ ⊥ := fun h0 => hh1 (by rw [h0] at hhP; exact Subgroup.mem_bot.mp hhP)
  have hΦP : Φ ≤ P := frattini_map_le P
  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 hyp hred
  have hmin := Lem7.minParabolic h331 hyp hHs
  have hTH : T ≤ H := hmin.isSylow.1
  have hQT : Q ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hOH : Q ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHO : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hfr : ∀ g ∈ H, ∃ q ∈ Q, q * g ∈ Subgroup.normalizer (P : Set G) := fun g hg =>
    exists_mul_mem_normalizer h331 hyp hHs hsol hp hp2 hPp hPH hPi hP1 hg
  have hHΦ := le_normalizer_frattini_sup hPH hHO hOH hfr
  obtain ⟨hn345, hcardV, hautL, ⟨hcommV, -⟩, -⟩ := hC
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hTLT : IsSylowTwoOf T (L ⊔ T) := isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right
  have hS : IsSylowTwoOf (autOn T V) ⊤ := by
    have h1 := isSylowTwoOf_map_hom (isSylowTwoOf_subgroupOf_of_le hLTV hTLT) (conjAct V)
    have h2 : autOn (L ⊔ T) V = ⊤ := by
      rw [eq_top_iff, ← hautL]
      exact Subgroup.map_mono (Subgroup.comap_mono le_sup_left)
    have h3 : ((L ⊔ T).subgroupOf (Subgroup.normalizer (V : Set G))).map (conjAct V) = ⊤ := h2
    rw [h3] at h1
    exact h1
  have hXp : IsPGroup p ↥(autOn Φ V) := by
    have h1 : IsPGroup p ↥(Φ.subgroupOf (Subgroup.normalizer (V : Set G))) :=
      (hPp.to_le hΦP).of_equiv (Subgroup.subgroupOfEquivOfLe hΦV).symm
    exact h1.map (conjAct V)
  have hX1 : autOn Φ V ≠ ⊥ := by
    obtain ⟨f, hf, x, hx, hfx⟩ := hΦnt
    intro h0
    have hmem : conjAct V ⟨f, hΦV hf⟩ ∈ autOn Φ V :=
      ⟨⟨f, hΦV hf⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
    rw [h0, Subgroup.mem_bot] at hmem
    apply hfx
    have := congrArg (fun σ : MulAut ↥V => ((σ ⟨x, hx⟩ : ↥V) : G)) hmem
    exact this
  have hSX : ∀ s ∈ autOn T V, ∀ x ∈ autOn Φ V, ∃ x' ∈ autOn Φ V, ∃ s' ∈ autOn T V,
      s * x = x' * s' := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨f, hf, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ht hf
    have htf : (t : G) * f * (t : G)⁻¹ ∈ Φ ⊔ Q :=
      (Subgroup.mem_normalizer_iff.mp (hHΦ (hTH ht)) f).mp (Subgroup.mem_sup_left hf)
    have hΦQ : Φ ≤ Subgroup.normalizer (Q : Set G) := hΦP.trans (hPH.trans hHO)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hΦQ] at htf
    obtain ⟨f', hf', q, hq, hfq⟩ := htf
    have hfq' : f' * q = (t : G) * f * (t : G)⁻¹ := hfq
    have hqt : q * t ∈ T := T.mul_mem (hQT hq) ht
    refine ⟨conjAct V ⟨f', hΦV hf'⟩, ⟨⟨f', hΦV hf'⟩, Subgroup.mem_subgroupOf.mpr hf', rfl⟩,
      conjAct V ⟨q * t, hTV hqt⟩, ⟨⟨q * t, hTV hqt⟩, Subgroup.mem_subgroupOf.mpr hqt, rfl⟩, ?_⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (t : G) * f = ((t : G) * f * (t : G)⁻¹) * t := by group
      _ = f' * q * t := by rw [← hfq']
      _ = f' * (q * t) := by group
  have hcomm' : ∀ x y : ↥V, x * y = y * x := fun x y => hcommV.is_comm.comm x y
  have hsq : ∀ x : ↥V, x ^ 2 = 1 := hV2'
  exact hKG ↥V n hn345 hcardV hcomm' hsq (autOn T V) (autOn Φ V) p hS hp hp2 hXp hX1 hSX

end Lem22

theorem lem12222Frattini_of_three (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1216 : Stmt12_2_16)
    (hKG : KGBorelOvergroupThree) (h3 : Lem12223Three) : Lem12222Frattini := by
  intro G _ _ T L V H P U I h n p hyp hNE hC hpre hUO hPnc
  by_contra hΦ1
  obtain ⟨hΦV, hVΦ, hcent, X, hX1, hXle, hΦX, hXC⟩ :=
    Lem22.facts_of_pre h331 h1222 h1216 hyp hNE hC hpre hUO hPnc
  have hΦnt : ∃ f ∈ (frattini ↥P).map P.subtype, ∃ x ∈ V, f * x * f⁻¹ ≠ x := by
    obtain ⟨⟨x, hxX⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX1
    have hx1' : x ≠ 1 := fun h0 => hx1 (Subtype.ext h0)
    by_contra hno
    push Not at hno
    apply hx1'
    have hxC : x ∈ X ⊓ Subgroup.centralizer
        (((frattini ↥P).map P.subtype : Subgroup G) : Set G) := by
      refine ⟨hxX, Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
      have := hno f hf x (hXle hxX).1
      calc f * x = (f * x * f⁻¹) * f := by group
        _ = x * f := by rw [this]
    rw [hXC, Subgroup.mem_bot] at hxC
    exact hxC
  have hp3 := Lem22.prime_eq_three_of_pre h331 h1222 hKG hyp hC hpre hΦV hΦnt
  subst hp3
  exact h3 G T L V H P U I h n hyp hNE hC hpre hUO hPnc hΦ1 hΦV hVΦ hcent
    ⟨X, hX1, hXle, hΦX, hXC⟩

end CFSG.Quasithin.H13

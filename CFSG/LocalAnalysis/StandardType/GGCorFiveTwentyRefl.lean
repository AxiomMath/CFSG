module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridgeStab
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

section Quot

variable {G : Type} [Group G] [Finite G]

theorem card_fix_mul_of_pseudoReflection {M : Type*} [Group M] {p : ℕ} (hp : p.Prime)
    {Bs : Subgroup G} (hcomm : ∀ a b : ↥Bs, a * b = b * a) {A : Subgroup M}
    (f : ↥Bs →* ↥A) (hf : Function.Surjective f) (hker : Nat.card f.ker = p)
    {φ : MulAut ↥Bs} (hφ : GGIsPseudoReflection p φ) (hφk : ∀ c ∈ f.ker, φ c = c)
    {ρ : ↥A → ↥A} (hρ : ∀ c, ρ (f c) = f (φ c)) :
    Nat.card {a : ↥A // ρ a = a} * p = Nat.card ↥A := by
  let δ : ↥Bs →* ↥Bs :=
    { toFun := fun c => c⁻¹ * φ c
      map_one' := by simp
      map_mul' := fun c c' => by
        rw [map_mul, mul_inv_rev, hcomm c'⁻¹ c⁻¹, mul_assoc, mul_assoc, ← mul_assoc c'⁻¹,
          hcomm c'⁻¹ (φ c), mul_assoc] }
  have hδ : ∀ c, δ c = c⁻¹ * φ c := fun _ => rfl
  have hδker : ∀ c, c ∈ δ.ker ↔ φ c = c := by
    intro c
    rw [MonoidHom.mem_ker, hδ, inv_mul_eq_one, eq_comm]
  have hH : Nat.card δ.ker * p = Nat.card ↥Bs := by
    rw [← hφ.2]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight hδker)
  have hfix : ∀ c, f (φ c) = f c → φ c = c := by
    intro c hc
    have hk : δ c ∈ f.ker := by
      rw [MonoidHom.mem_ker, hδ, map_mul, map_inv, hc, inv_mul_cancel]
    have hφδ : φ (δ c) = δ c := hφk _ hk
    have hφc : φ c = c * δ c := by rw [hδ, mul_inv_cancel_left]
    have hpow : ∀ n : ℕ, (φ ^ n) c = c * δ c ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hφδ, hφc, mul_assoc, ← pow_succ']
    have h1 : δ c ^ (p - 1) = 1 := by
      have h2 := hpow (p - 1)
      rw [hφ.1, MulAut.one_apply] at h2
      exact (mul_eq_left.mp h2.symm)
    have h3 : δ c ^ p = 1 := by
      have hd : orderOf (⟨δ c, hk⟩ : f.ker) ∣ p := hker ▸ orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at hd
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    have h4 : δ c = 1 := by
      have e : δ c = δ c ^ p * (δ c ^ (p - 1))⁻¹ := by
        rw [← pow_sub _ (Nat.sub_le p 1), Nat.sub_sub_self hp.one_lt.le, pow_one]
      rw [e, h1, h3, inv_one, mul_one]
    rw [hφc, h4, mul_one]
  let F : ↥δ.ker →* ↥A := f.comp δ.ker.subtype
  have hFr : ∀ a : ↥A, a ∈ F.range ↔ ρ a = a := by
    intro a
    constructor
    · rintro ⟨c, rfl⟩
      change ρ (f c) = f c
      rw [hρ, (hδker c).mp c.2]
    · intro ha
      obtain ⟨c, rfl⟩ := hf a
      have h1 : f (φ c) = f c := by rw [← hρ, ha]
      exact ⟨⟨c, (hδker c).mpr (hfix c h1)⟩, rfl⟩
  have hkle : f.ker ≤ δ.ker := fun c hc => (hδker c).mpr (hφk c hc)
  have hFk : Nat.card F.ker = p := by
    rw [← hker]
    refine Nat.card_congr
      { toFun := fun c => ⟨(c : ↥δ.ker), c.2⟩
        invFun := fun c => ⟨⟨c, hkle c.2⟩, c.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcF := card_range_mul_card_ker F
  rw [hFk] at hcF
  have hcf := card_range_mul_card_ker f
  rw [hker, MonoidHom.range_eq_top_of_surjective f hf, Subgroup.card_top] at hcf
  have hfx : Nat.card {a : ↥A // ρ a = a} = Nat.card F.range :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a => (hFr a).symm)
  rw [hfx, hcF]
  have h2 : Nat.card δ.ker * p = Nat.card ↥A * p := by rw [hH, hcf]
  exact Nat.eq_of_mul_eq_mul_right hp.pos h2

end Quot

section Conj

variable {G : Type} [Group G]

theorem ggGamma_conj_normalizer (L : Subgroup G) {B : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (g : Subgroup.normalizer (L : Set G)) (b : B)
    (hgb : (g : G) * b * (g : G)⁻¹ ∈ B) :
    L.normalizerMonoidHom g * ggGamma L hBN b * (L.normalizerMonoidHom g)⁻¹ =
      ggGamma L hBN ⟨(g : G) * b * (g : G)⁻¹, hgb⟩ := by
  ext l
  rw [← map_inv, MulAut.mul_apply, MulAut.mul_apply, normalizerMonoidHom_coe, ggGamma_coe,
    normalizerMonoidHom_coe, ggGamma_coe]
  push_cast
  group

theorem conj_pow_eq_of_conj {M H : Type*} [Group M] [Group H] (γ : H →* M) {β : M}
    {φ : MulAut H} (h : ∀ c, β * γ c * β⁻¹ = γ (φ c)) (n : ℕ) (c : H) :
    β ^ n * γ c * (β ^ n)⁻¹ = γ ((φ ^ n) c) := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    have e : (φ ^ (n + 1)) c = φ ((φ ^ n) c) := by rw [pow_succ', MulAut.mul_apply]
    rw [e, ← h, ← ih, pow_succ']
    group

end Conj

section Config

variable {G : Type} [Group G] [Finite G]

theorem exists_ggAutomizer_of_reflBridge {p r : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G}
    (hp : p.Prime) (hBst : GGBstar p B Bs) (hS : LargeEvenSStar p B x L)
    (h4 : 4 ≤ LargeEvenTwoLocalRank p G)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) (hbr : GGTorusReflBridge p r R I) {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs)
    (hφp : GGIsPseudoReflection p φ) :
    ∃ ψ ∈ ggAutomizer L Bs, ∀ b : ↥Bs, (((ψ b)⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers x := by
  classical
  have hBs : IsElemAbelian p Bs := hBst.2.1
  have hxB : x ∈ Bs := hBst.1 hS.2.1
  have := Fact.mk hp
  have hBBs : B ≤ Bs := hBst.1
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hBsN
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hBst.2.2.2
  obtain ⟨g, hgx, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_of_sstar hS hnc hgx
  set γ := ggGamma L hBsN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBsN b, ggBeta_mem L θ hBsN hBs3 b, fun l => ggBeta_ggQuotHom L hBsN θ b l⟩
  have hcA := card_range_ggGamma_mul L hBN hp hS
  have hcβ := card_range_ggBeta_mul L θ hp hS hL hBN
  have hAβ : Nat.card (ggGamma L hBN).range = Nat.card (ggBeta L θ hBN).range :=
    Nat.eq_of_mul_eq_mul_right hp.pos (hcA.trans hcβ.symm)
  have hle : Nat.card (ggGamma L hBN).range ≤ Nat.card γ.range := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  have hr : p ^ r ≤ Nat.card γ.range := by
    refine le_trans ?_ hle
    rw [hAβ]
    exact pow_le_card_range_ggBeta hp hS hL θ hBN hlift
  have h3' : p ^ 3 ≤ Nat.card γ.range := by
    refine le_trans ?_ hle
    have h4' := pow_four_le_card_of_bmax hp hS.1 h4
    rw [← hcA, pow_succ] at h4'
    exact Nat.le_of_mul_le_mul_right h4' hp.pos
  have hker : ∀ b : Bs, γ b = 1 ↔ (b : G) ∈ Subgroup.zpowers x := fun b => by
    rw [hγ, ggGamma_eq_one_iff, ← inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxB hS.2.2.1
      hS.2.2.2.1.1 hS.2.2.2.2]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  set β : MulAut L := L.normalizerMonoidHom ⟨g, hgL⟩ with hβ
  have hφmem : ∀ b : Bs, g * (b : G) * g⁻¹ ∈ Bs := fun b => by
    rw [← hφg b]
    exact (φ b).2
  have hconj : ∀ b : Bs, β * γ b * β⁻¹ = γ (φ b) := by
    intro b
    rw [hβ, hγ, ggGamma_conj_normalizer L hBsN ⟨g, hgL⟩ b (hφmem b)]
    congr 1
    exact Subtype.ext (hφg b).symm
  have hNβ : ∀ a ∈ γ.range, β * a * β⁻¹ ∈ γ.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨φ b, (hconj b).symm⟩
  have hpowβ : ∀ a ∈ γ.range, β ^ (p - 1) * a * (β ^ (p - 1))⁻¹ = a := by
    rintro _ ⟨b, rfl⟩
    rw [conj_pow_eq_of_conj γ hconj, hφp.1, MulAut.one_apply]
  have hxBs1 : orderOf (⟨x, hxB⟩ : Bs) = p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hBs.2 x hxB) hS.2.2.1
  have hkerγ : γ.rangeRestrict.ker = (Subgroup.zpowers x).subgroupOf Bs := by
    ext b
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker]
  have hkcard : Nat.card γ.rangeRestrict.ker = p := by
    rw [hkerγ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hxB)).toEquiv, Nat.card_zpowers,
      orderOf_eq_prime (hBs.2 x hxB) hS.2.2.1]
  have hgx' : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hgx
  have hφk : ∀ c ∈ γ.rangeRestrict.ker, φ c = c := by
    intro c hc
    rw [hkerγ, Subgroup.mem_subgroupOf] at hc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
    apply Subtype.ext
    rw [hφg c, ← hk, (Commute.zpow_right hgx' k).eq, mul_inv_cancel_right]
  have hfixβ : Nat.card {a : γ.range // β * (a : MulAut L) * β⁻¹ = a} * p =
      Nat.card γ.range := by
    have h := card_fix_mul_of_pseudoReflection hp hBc γ.rangeRestrict
      γ.rangeRestrict_surjective hkcard hφp hφk
      (ρ := fun a => ⟨β * (a : MulAut L) * β⁻¹, hNβ a a.2⟩)
      (fun c => Subtype.ext (hconj c))
    rw [← h]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by
      rw [Subtype.ext_iff])
  have hcompat : ∀ l : L, ggLAut L θ ⟨g, hgL⟩ (ggQuotHom θ l) = ggQuotHom θ (β l) := by
    intro l
    rw [ggQuotHom_apply, ggQuotHom_apply, ggLAut_apply]
  obtain ⟨n, hn1, hn2⟩ := hbr L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
    hL γ.range hA hAI hr h3' β (ggLAut L θ ⟨g, hgL⟩) hcompat hNβ hpowβ hfixβ
  have hnB : ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := by
    intro b hb
    obtain ⟨htp, htA⟩ := hn1 (γ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
    have htG : ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) = n * b * (n : G)⁻¹ * b⁻¹ := by
      push_cast
      rw [hγ, ggGamma_coe]
      group
    have htC : ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      have h1 := congrArg Subtype.val (htA (γ ⟨b', hb'⟩) ⟨⟨b', hb'⟩, rfl⟩)
      rw [hγ, ggGamma_coe] at h1
      calc b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G)
          = b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) * b'⁻¹ * b' := by group
        _ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) * b' := by rw [h1]
    have htp' : ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) ^ p = 1 := by
      have := congrArg Subtype.val htp
      simpa using this
    have htB := hSC _ htC htp'
    have e : (n : G) * b * (n : G)⁻¹ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) * b := by
      rw [htG]
      group
    rw [e]
    exact Bs.mul_mem htB hb
  have hnN : (n : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    have h := mem_normalizer_of_forall_conj_mem (W := Bs) (g := (n : G)⁻¹) (fun w hw => by
      simpa using hnB w hw)
    simpa using Subgroup.inv_mem _ h
  refine ⟨ggConjAut Bs hnN, ggConjAut_mem_ggAutomizer n.2 hnN, fun b => ?_⟩
  have h1 : γ (ggConjAut Bs hnN b) = γ (φ b) := by
    rw [← hconj, ← hn2 _ ⟨b, rfl⟩, ← ggGamma_conj L hBsN n b (hnB b b.2)]
    rfl
  have h2 : γ ((ggConjAut Bs hnN b)⁻¹ * φ b) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  exact (hker _).mp h2

theorem exists_ggAutomizer_L_of_reflBridge {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) (hbr : GGTorusReflBridge p r R I) {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs)
    (hφp : GGIsPseudoReflection p φ) :
    ∃ ψ ∈ ggAutomizer L Bs, ∀ b : ↥Bs, (((ψ b)⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers x :=
  exists_ggAutomizer_of_reflBridge hcfg.1.2.2.2.2.2.1.1 hcfg.2.1 hcfg.1.2.2.2.2.2.2.1
    hcfg.1.2.2.2.2.2.1.2.2.2 hnc hL θ hBsN hBs3 hlift hbr hφ hφp

end Config

section Lab

variable {G : Type} [Group G]

@[expose] def GGInnerDiagOnLabel (S : ℕ → LargeEvenLabel → Prop) (p : ℕ) (Bs L : Subgroup G) :
    Prop :=
  LargeEvenMarking L (fun lab _ _ I _ θ => S p lab ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
    ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)

theorem GGInnerDiagOn.label {Bs L : Subgroup G} (S : ℕ → LargeEvenLabel → Prop) (p : ℕ)
    (h : GGInnerDiagOn Bs L) : GGInnerDiagOnLabel (fun p lab => S p lab ∨ ¬ S p lab) p Bs L :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨em _, hP⟩) h

theorem GGInnerDiagOnLabel.elim_or {S T : ℕ → LargeEvenLabel → Prop} {p : ℕ} {Bs L : Subgroup G}
    (h : GGInnerDiagOnLabel (fun p lab => S p lab ∨ T p lab) p Bs L) :
    GGInnerDiagOnLabel S p Bs L ∨ GGInnerDiagOnLabel T p Bs L := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hST, -⟩ := largeEvenRawDatum_exists hraw
  rcases hST with h | h
  · exact Or.inl ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _, hP⟩ => ⟨hs, hna, θ', h, hP⟩) hraw⟩
  · exact Or.inr ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _, hP⟩ => ⟨hs, hna, θ', h, hP⟩) hraw⟩

end Lab

@[expose] def GGPseudoReflStabModInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel S p Bs L →
      ∀ φ ∈ ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs, GGIsPseudoReflection p φ →
        ∃ ψ ∈ ggAutomizer (ggG0 p B x L D J) Bs, (∀ b : ↥Bs, (b : G) = x → ψ b = b) ∧
          ∀ b : ↥Bs, (((ψ b)⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers x

theorem ggPseudoReflStabModInputOn_of (h : GGPseudoReflStabModInput)
    (S : ℕ → LargeEvenLabel → Prop) : GGPseudoReflStabModInputOn S :=
  fun G _ _ p B Bs x L D J hH _ => h G p B Bs x L D J hH

theorem GGPseudoReflStabModInputOn.or {S T : ℕ → LargeEvenLabel → Prop}
    (hS : GGPseudoReflStabModInputOn S) (hT : GGPseudoReflStabModInputOn T) :
    GGPseudoReflStabModInputOn fun p lab => S p lab ∨ T p lab := by
  intro G _ _ p B Bs x L D J hH hL
  rcases hL.elim_or with h | h
  · exact hS G p B Bs x L D J hH h
  · exact hT G p B Bs x L D J hH h

theorem ggPseudoReflStabModInput_of_on {S : ℕ → LargeEvenLabel → Prop}
    (hS : GGPseudoReflStabModInputOn S)
    (hT : GGPseudoReflStabModInputOn fun p lab => ¬ S p lab) : GGPseudoReflStabModInput := by
  intro G _ _ p B Bs x L D J hH
  exact (hS.or hT) G p B Bs x L D J hH (hH.2.2.1.1.label S p)

theorem ggPseudoReflStabModInputOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflBridge p r R I) :
    GGPseudoReflStabModInputOn S := by
  intro G _ _ p B Bs x L D J hH hM φ hφ hφp
  have hcfg := hH.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3⟩, r, hlift, hbr⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨ψ, hψ, hmod⟩ := exists_ggAutomizer_L_of_reflBridge hcfg (ha₀ G p B x L hcfg.1) hL θ
    hBsN h3 hlift hbr hφ hφp
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.1.2.2.2.2.2.2.1.2.2.2.1.1
  refine ⟨ψ, ggAutomizer_mono Bs (le_ggG0_left p B x L D J) hψ, fun b hb => ?_, hmod⟩
  have hc : (⟨x, hb ▸ b.2⟩ : ↥Bs) = b := Subtype.ext hb.symm
  rw [← hc]
  exact ggAutomizer_apply_eq_of_le_centralizer hLx hψ

theorem ggPseudoReflStabInput_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflBridge p r R I)
    (hrest : GGPseudoReflStabModInputOn fun p lab => ¬ S p lab) : GGPseudoReflStabInput :=
  ggPseudoReflStabInput_of_mod
    (ggPseudoReflStabModInput_of_on (ggPseudoReflStabModInputOn_of_labels ha₀ h) hrest)

end CFSG.StandardType

end

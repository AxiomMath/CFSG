module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptF2a
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptF2b
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptK
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLem125
public import CFSG.Assembly.OpenBridges
public import CFSG.Quasithin.Vol2.Ch10SecKIK2j
public import CFSG.Quasithin.EmptyFaithful.E22QPlumb
public import CFSG.Quasithin.Vol2.Ch6Conj
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptDefs

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

theorem f2_le_normalizer_of_comm {G : Type} [Group G] {A B : Subgroup G}
    (h : ⁅A, B⁆ ≤ B) : A ≤ Subgroup.normalizer (B : Set G) := by
  have key : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B := by
    intro a ha b hb
    have hc : ⁅a, b⁆ ∈ B := h (Subgroup.commutator_mem_commutator ha hb)
    have e : a * b * a⁻¹ = ⁅a, b⁆ * b := by
      rw [commutatorElement_def]; group
    rw [e]
    exact B.mul_mem hc hb
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key a ha x
  · intro hx
    have h2 := key a⁻¹ (A.inv_mem ha) _ hx
    have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
    rwa [e] at h2

theorem f2_twoLocal_centralizer {G : Type} [Group G] [Finite G] {z : G} (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) :
    IsTwoLocal (Subgroup.centralizer ({z} : Set G)) ∧
      pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := by
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hcard : Nat.card (Subgroup.zpowers z) = 2 ^ 1 := by
    rw [Nat.card_zpowers, hord]; norm_num
  have hP2 : IsPGroup 2 (Subgroup.zpowers z) := IsPGroup.of_card hcard
  have hPne : Subgroup.zpowers z ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]; exact hz1
  have hPle : Subgroup.zpowers z ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
  have hCN : Subgroup.centralizer ({z} : Set G) =
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    apply le_antisymm
    · intro x hx
      have hxz : Commute x z := (Subgroup.mem_centralizer_iff.1 hx z (Set.mem_singleton z)).symm
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
        refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
        rw [(hxz.zpow_right k).eq]
        group
      · intro hh
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
        refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
        have hc' : x⁻¹ * z ^ k = z ^ k * x⁻¹ := (hxz.zpow_right k).inv_left.eq
        have h4 : x⁻¹ * z ^ k * x = z ^ k := by rw [hc']; group
        calc z ^ k = x⁻¹ * z ^ k * x := h4.symm
          _ = x⁻¹ * (x * h * x⁻¹) * x := by rw [hk]
          _ = h := by group
    · intro x hx
      rw [Subgroup.mem_normalizer_iff] at hx
      have hzP : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
      have hxz' : x * z * x⁻¹ ∈ Subgroup.zpowers z := (hx z).1 hzP
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxz'
      have hk' : z ^ k = z ∨ z ^ k = 1 := by
        have hmod : z ^ (k % 2) = z ^ k := by
          have := zpow_mod_orderOf z k
          rw [hord] at this
          exact_mod_cast this
        rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h0 | h1
        · right; rw [← hmod, h0, zpow_zero]
        · left; rw [← hmod, h1, zpow_one]
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      rcases hk' with hkz | hk1
      · rw [hkz] at hk
        calc z * x = (x * z * x⁻¹) * x := by rw [← hk]
          _ = x * z := by group
      · exfalso
        apply hz1
        have h2 : x * z * x⁻¹ = 1 := hk.symm.trans hk1
        calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
          _ = 1 := by rw [h2]; group
  refine ⟨⟨Subgroup.zpowers z, hPne, hP2, hCN⟩, ?_⟩
  intro hbot
  apply hPne
  apply eq_bot_iff.2
  rw [← hbot]
  exact le_pCoreOf_of_le_normalizer hPle (hCN ▸ le_rfl) hP2

theorem f2_center_conj {G : Type} [Group G] {H K N : Subgroup G} {t : G} (ht : t ∈ H)
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hK : ∀ a ∈ K, (∀ x ∈ K, ⁅a, x⁆ ∈ N) → a ∈ N) :
    ∀ a ∈ K.map (MulAut.conj t).toMonoidHom,
      (∀ y ∈ K.map (MulAut.conj t).toMonoidHom, ⁅a, y⁆ ∈ N) → a ∈ N := by
  intro a ha hay
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 ha
  have ht' : t⁻¹ ∈ H := H.inv_mem ht
  have hkN : k ∈ N := by
    apply hK k hk
    intro x hx
    have hy : t * x * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    have h1 : ⁅t * k * t⁻¹, t * x * t⁻¹⁆ ∈ N := hay _ hy
    have e1 : ⁅t * k * t⁻¹, t * x * t⁻¹⁆ = t * ⁅k, x⁆ * t⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e1] at h1
    have h2 := hN t⁻¹ ht' _ h1
    have e2 : t⁻¹ * (t * ⁅k, x⁆ * t⁻¹) * t⁻¹⁻¹ = ⁅k, x⁆ := by group
    rwa [e2] at h2
  have := hN t ht k hkN
  simpa [MulAut.conj_apply, mul_assoc] using this

theorem f2_dvd_card_of_psl {X : Type} [Group X] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h : IsPSL 2 q 1 X) : q ∣ Nat.card X := by
  have h' : IsPSL 2 q 1 ↥(⊤ : Subgroup X) := IsPSL.of_mulEquiv (Subgroup.topEquiv).symm h
  have := CFSG.Quasithin.Vol2.Ch10.SecC.C10KH.prime_dvd_card_of_isPSL_two hq hq2 h'
  rwa [Subgroup.card_top] at this

theorem f2_exists_elt {G : Type} [Group G] [Finite G] (K : Subgroup G) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card K) : ∃ x ∈ K, orderOf x = q := by
  haveI := Fact.mk hq
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥K) q
    (by rw [← Nat.card_eq_fintype_card]; exact hdvd)
  refine ⟨x, x.2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact hx

theorem f2_pRank_le_two {G : Type} [Group G] [Finite G] {H : Subgroup G} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hH : IsTwoLocal H) (he : CFSG.Open.evenRank G ≤ 2) :
    CFSG.Open.pRank q H ≤ 2 :=
  (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank q hq hq2 H hH).trans he

theorem f2_caseB {G : Type} [Group G] [Finite G] {G₀ K K' C : Subgroup G} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hG0 : IsTwoLocal G₀) (he : CFSG.Open.evenRank G ≤ 2)
    (hKG : K ≤ G₀) (hK'G : K' ≤ G₀) (hCG : C ≤ G₀)
    (hKK' : ⁅K, K'⁆ ≤ pCoreOf 2 G₀) (hKC : ⁅K, C⁆ ≤ pCoreOf 2 G₀)
    (hK'C : ⁅K', C⁆ ≤ pCoreOf 2 G₀)
    (hKcen : ∀ a ∈ K, (∀ x ∈ K, ⁅a, x⁆ ∈ pCoreOf 2 G₀) → a ∈ pCoreOf 2 G₀)
    (hK'cen : ∀ a ∈ K', (∀ x ∈ K', ⁅a, x⁆ ∈ pCoreOf 2 G₀) → a ∈ pCoreOf 2 G₀)
    (hqK : q ∣ Nat.card K) (hqK' : q ∣ Nat.card K') (hqC : q ∣ Nat.card C) : False := by
  have hN : ∀ h ∈ G₀, ∀ n ∈ pCoreOf 2 G₀, h * n * h⁻¹ ∈ pCoreOf 2 G₀ := by
    intro h hh n hn
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 G₀ hh) n).1 hn
  have hN2 : IsPGroup 2 (pCoreOf 2 G₀) := pCoreOf_isPGroup 2 G₀
  have hNle : pCoreOf 2 G₀ ≤ G₀ := Subgroup.map_subtype_le _
  obtain ⟨x, hxK, hox⟩ := f2_exists_elt K hq hqK
  obtain ⟨y, hyK', hoy⟩ := f2_exists_elt K' hq hqK'
  obtain ⟨w, hwC, how⟩ := f2_exists_elt C hq hqC
  have hind := f2_indep (H := G₀) (N := pCoreOf 2 G₀) (A := K) (B := K') (C := C)
    hNle hN hN2 hKG hK'G hCG hq hq2 hKK' hKC hK'C hKcen hK'cen
    hxK hyK' hwC hox hoy how
  have h3 := f2_pRank_ge_three (H := G₀) (N := pCoreOf 2 G₀)
    hNle hN hN2 hq hq2 (hKG hxK) (hK'G hyK') (hCG hwC) hox hoy how
    (hKK' (Subgroup.commutator_mem_commutator hxK hyK'))
    (hKC (Subgroup.commutator_mem_commutator hxK hwC))
    (hK'C (Subgroup.commutator_mem_commutator hyK' hwC)) hind
  have h2 := f2_pRank_le_two hq hq2 hG0 he
  omega


theorem f2_pCoreOf_le_self {G : Type} [Group G] (X : Subgroup G) : pCoreOf 2 X ≤ X :=
  Subgroup.map_subtype_le _

theorem f2_mem_normalizer_of_conj_eq {G : Type} [Group G] (X : Subgroup G) (g : G)
    (h : X.map (MulAut.conj g⁻¹).toMonoidHom = X) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : x ∈ X.map (MulAut.conj g⁻¹).toMonoidHom := by rw [h]; exact hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
    have e : g * x * g⁻¹ = y := by
      rw [← hyx]
      show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y
      group
    rw [e]
    exact hy
  · intro hx
    have hx' : x ∈ X.map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.mem_map.2 ⟨g * x * g⁻¹, hx, by
        show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
        group⟩
    rw [h] at hx'
    exact hx'

theorem f2_dvd_card_sub {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (K : Subgroup G) (h : IsPSL 2 q 1 (↥K ⧸ CFSG.pCore 2 ↥K)) : q ∣ Nat.card K := by
  have h1 := f2_dvd_card_of_psl hq hq2 h
  have h2 := Subgroup.card_mul_index (CFSG.pCore 2 ↥K)
  rw [← h2]
  exact Dvd.dvd.mul_left h1 _

theorem f2_card_map_conj {G : Type} [Group G] (X : Subgroup G) (h : G) :
    Nat.card (X.map (MulAut.conj h).toMonoidHom) = Nat.card X :=
  Subgroup.card_map_of_injective (MulEquiv.injective _)

theorem f2_card_conj {G : Type} [Group G] (X : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate X g) = Nat.card X :=
  f2_card_map_conj X g⁻¹


theorem leafF2_holds (h36 : A36ForSQTK) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : LeafF2 := by
  intro G _ _ T M L D H K TL L2 e F hg
  obtain ⟨g, hg⟩ := hg
  classical
  have c : NFConfig G T M L D H K := F.nf
  obtain ⟨z, hz⟩ : ∃ z : G, z = g⁻¹ * e * g := ⟨_, rfl⟩
  rw [← hz] at hg
  have hΩT : quasithinOmegaOneCenter T ≤ T := (Subgroup.closure_le _).2 fun _ hx => hx.1.1
  have hz1 : z ≠ 1 := by
    intro h
    apply F.e_ne
    calc e = g * (g⁻¹ * e * g) * g⁻¹ := by group
      _ = 1 := by rw [← hz, h]; group
  have hz2 : z ^ 2 = 1 := by
    have : z ^ 2 = g⁻¹ * e ^ 2 * g := by rw [hz, pow_two, pow_two]; group
    rw [this, F.e_sq]; group
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : Subgroup G, G₀ = Subgroup.centralizer ({z} : Set G) := ⟨_, rfl⟩
  have hmemG₀ : ∀ x : G, x ∈ G₀ ↔ z * x = x * z := by
    intro x
    rw [hG₀, Subgroup.mem_centralizer_iff]
    simp
  obtain ⟨hG₀loc, hpc⟩ : IsTwoLocal G₀ ∧ pCoreOf 2 G₀ ≠ ⊥ := by
    rw [hG₀]; exact f2_twoLocal_centralizer hz2 hz1
  have hΩG₀ : ∀ X : Subgroup G, X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
      X ≤ G₀ := by
    intro X hX x hx
    rw [hmemG₀]
    exact Subgroup.mem_centralizer_iff.1 (hX hx) z hg
  have hKΩ : K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    nf_le_centralizer_Z h36 c.hyp c.inH_H₀ c.K_comp c.nonfaithful
  have hK₀Ω : conjClosure K T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    nf_conjClosure_le_centralizer_Z h36 c.hyp c.inH_H₀ c.K_comp c.nonfaithful
  have hKG₀ : K ≤ G₀ := hΩG₀ K hKΩ
  have hK₀G₀ : conjClosure K T ≤ G₀ := hΩG₀ _ hK₀Ω
  have hTG₀ : T ≤ G₀ := hΩG₀ T (fun t ht => L246C127.le_centralizer_omegaOneCenter T ht)
  have hG₀N : G₀ ≤ Subgroup.normalizer (conjClosure K T : Set G) := by
    obtain ⟨M', hM'max, hM'G⟩ := exists_maxTwoLocal_ge hG₀loc
    have hInM : InM (K ⊔ T) M' := ⟨hM'max, (sup_le hKG₀ hTG₀).trans hM'G⟩
    have hM'eq := (c.uniqueM h128 h37 h38 h39).2 M' hInM
    rw [← hM'eq]
    exact hM'G
  have hKcomp : K ∈ cComp G₀ :=
    lemma_1_2_7_one c.hyp.qtke c.hyp.simple c.hyp.nonabelian (a37ForSQTK_of_cat h37)
      (a39ForSQTK_of_cat h39) c.hyp.sylow (c.isMaximalLocal h128) ⟨sup_le hKG₀ hTG₀, hpc⟩
  obtain ⟨t', ht'T, -, hK'H, hKK', hK₀eq, -⟩ :=
    CFSG.Quasithin.H13.NFConfig.exists_pair c h37 h38
  have hK'G₀ : K.map (MulAut.conj t').toMonoidHom ∈ cComp G₀ :=
    map_conj_mem_cComp hKcomp (hTG₀ ht'T)
  set K' : Subgroup G := K.map (MulAut.conj t').toMonoidHom with hK'def
  have hK'leG₀ : K' ≤ G₀ := le_of_mem_cComp hK'G₀
  have hKsub : K ≤ conjClosure K T := by rw [hK₀eq]; exact le_sup_left
  have hK'sub : K' ≤ conjClosure K T := by rw [hK₀eq]; exact le_sup_right
  haveI : IsSimpleGroup G := c.hyp.simple
  have hLS : LocalSQTK G := (qtkeCore_of_cat c.hyp.nonabelian c.hyp.qtke).1
  have hev : CFSG.Open.evenRank G ≤ 2 := by
    have := (qtkeCore_of_cat c.hyp.nonabelian c.hyp.qtke).2.2
    rwa [CFSG.Assembly.evenRank_eq_open G] at this
  have h1 := Vol2Native.lemma_1_2_1_two hLS h37 hpc hKcomp hK'G₀ hKK'
  have hcomm : ⁅K, K'⁆ ≤ pCoreOf 2 G₀ := h1.1.trans h1.2
  have hcK1 : ⁅K, K'⁆ ≤ K := (h1.1.trans inf_le_left).trans (f2_pCoreOf_le_self K)
  have hcK2 : ⁅K, K'⁆ ≤ K' := (h1.1.trans inf_le_right).trans (f2_pCoreOf_le_self K')
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    f2_le_normalizer_of_comm (by rw [Subgroup.commutator_comm]; exact hcK1)
  have hKN' : K ≤ Subgroup.normalizer (K' : Set G) := f2_le_normalizer_of_comm hcK2
  have hK₀N : conjClosure K T ≤ Subgroup.normalizer (K : Set G) := by
    rw [hK₀eq]; exact sup_le Subgroup.le_normalizer hK'N
  have hK₀N' : conjClosure K T ≤ Subgroup.normalizer (K' : Set G) := by
    rw [hK₀eq]; exact sup_le hKN' Subgroup.le_normalizer
  have hpK : pCoreOf 2 K ≤ pCoreOf 2 G₀ := f2_pCoreOf_le_sandwich hKsub hK₀N hK₀G₀ hG₀N
  have hpK' : pCoreOf 2 K' ≤ pCoreOf 2 G₀ := f2_pCoreOf_le_sandwich hK'sub hK₀N' hK₀G₀ hG₀N
  obtain ⟨q, hq, hq24, hmod⟩ := c.model
  have hq2 : q ≠ 2 := by omega
  have hKcen : ∀ a ∈ K, (∀ x ∈ K, ⁅a, x⁆ ∈ pCoreOf 2 G₀) → a ∈ pCoreOf 2 G₀ :=
    f2_center_mod hKG₀ hpK (CFSG.Quasithin.E2.E22N.plumb_psl_simple hmod)
      (CFSG.Quasithin.E2.E22N.plumb_psl_nonab hq hmod)
  have hNG₀ : ∀ h ∈ G₀, ∀ n ∈ pCoreOf 2 G₀, h * n * h⁻¹ ∈ pCoreOf 2 G₀ := by
    intro h hh n hn
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 G₀ hh) n).1 hn
  have hK'cen : ∀ a ∈ K', (∀ x ∈ K', ⁅a, x⁆ ∈ pCoreOf 2 G₀) → a ∈ pCoreOf 2 G₀ :=
    f2_center_conj (hTG₀ ht'T) hNG₀ hKcen
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) := hKsub.trans F.K0_e
  have hK'e : K' ≤ Subgroup.centralizer ({e} : Set G) := hK'sub.trans F.K0_e
  have hTLe : TL ≤ Subgroup.centralizer ({e} : Set G) := by
    rw [← F.T_e]; exact inf_le_right
  have hconjG₀ : ∀ X : Subgroup G, X ≤ Subgroup.centralizer ({e} : Set G) →
      CFSG.conjugate X g ≤ G₀ := by
    intro X hX x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
    rw [hmemG₀]
    have hek : e * k = k * e := Subgroup.mem_centralizer_iff.1 (hX hk) e (Set.mem_singleton e)
    show z * (g⁻¹ * k * g⁻¹⁻¹) = (g⁻¹ * k * g⁻¹⁻¹) * z
    rw [inv_inv, hz]
    calc g⁻¹ * e * g * (g⁻¹ * k * g) = g⁻¹ * (e * k) * g := by group
      _ = g⁻¹ * (k * e) * g := by rw [hek]
      _ = g⁻¹ * k * g * (g⁻¹ * e * g) := by group
  have hKgG₀ : CFSG.conjugate K g ≤ G₀ := hconjG₀ K hKe
  have hK'gG₀ : CFSG.conjugate K' g ≤ G₀ := hconjG₀ K' hK'e
  have hlocK : CFSG.Open.quasithinIsLocal TL K :=
    f2_isLocal_TL c.hyp.sylow F.TL_le F.T_e F.e_T F.e_ne F.e_sq F.K0_e
      (le_normalizer_conjClosure K T) hKsub (cComp_of_isLocal c.K_isLocal)
  have hloc'T : CFSG.Open.quasithinIsLocal T K' :=
    isLocal_of_mem_cComp_of_sylow c.isSylowTwoOf_H₀ c.O hK'H
  have hlocK' : CFSG.Open.quasithinIsLocal TL K' :=
    f2_isLocal_TL c.hyp.sylow F.TL_le F.T_e F.e_T F.e_ne F.e_sq F.K0_e
      (le_normalizer_conjClosure K T) hK'sub (cComp_of_isLocal hloc'T)
  have hlocKg : CFSG.Open.quasithinIsLocal (CFSG.conjugate TL g) (CFSG.conjugate K g) :=
    quasithinIsLocal_map (MulAut.conj g⁻¹) hlocK
  have hlocK'g : CFSG.Open.quasithinIsLocal (CFSG.conjugate TL g) (CFSG.conjugate K' g) :=
    quasithinIsLocal_map (MulAut.conj g⁻¹) hlocK'
  have hTL2 : IsPGroup 2 TL := c.hyp.sylow.1.to_le F.TL_le
  have hTLg2 : IsPGroup 2 (CFSG.conjugate TL g) := hTL2.map (MulAut.conj g⁻¹).toMonoidHom
  have hTLg : CFSG.conjugate TL g ≤ G₀ := hconjG₀ TL hTLe
  obtain ⟨S', hS'G, hTLS'⟩ := CFSG.Quasithin.A4.exists_isSylowTwoOf_ge hTLg hTLg2
  have hTsyl : IsSylowTwoOf T G₀ := isSylowTwoOf_of_quasithinIsSylowTwo c.hyp.sylow hTG₀
  have hcardS' : Nat.card S' = Nat.card T := by rw [hS'G.card_eq, hTsyl.card_eq]
  have hRcard : Nat.card (CFSG.conjugate TL g) = Nat.card TL := f2_card_conj TL g
  have hidx : (CFSG.conjugate TL g).relIndex S' ≤ 2 := by
    have h2 := Subgroup.relIndex_mul_card (CFSG.conjugate TL g) S'
    have hRS : CFSG.conjugate TL g ⊓ S' = CFSG.conjugate TL g := inf_eq_left.2 hTLS'
    rw [hRS, hcardS', hRcard] at h2
    have hpos : 0 < Nat.card TL := Nat.card_pos
    apply Nat.le_of_mul_le_mul_right _ hpos
    rw [h2]
    exact F.TL_idx
  obtain ⟨J₁, ⟨hJ₁c, hKgJ₁⟩, -⟩ :=
    Vol2Native.lemma_1_2_5 hLS h37 h39 hpc hS'G hTLS' hidx hlocKg hKgG₀
  obtain ⟨J₂, ⟨hJ₂c, hK'gJ₂⟩, -⟩ :=
    Vol2Native.lemma_1_2_5 hLS h37 h39 hpc hS'G hTLS' hidx hlocK'g hK'gG₀
  have hKg_card : Nat.card (CFSG.conjugate K g) = Nat.card K := f2_card_conj K g
  have hK'card : Nat.card K' = Nat.card K := f2_card_map_conj K t'
  have hK'g_card : Nat.card (CFSG.conjugate K' g) = Nat.card K := (f2_card_conj K' g).trans hK'card
  have hqK : q ∣ Nat.card K := f2_dvd_card_sub hq hq2 K hmod
  have hqK' : q ∣ Nat.card K' := hK'card ▸ hqK
  have hqKg : q ∣ Nat.card (CFSG.conjugate K g) := hKg_card ▸ hqK
  have hqK'g : q ∣ Nat.card (CFSG.conjugate K' g) := hK'g_card ▸ hqK
  have caseB : ∀ (C J : Subgroup G), J ∈ cComp G₀ → C ≤ J → C ≤ G₀ → q ∣ Nat.card C →
      J ≠ K → J ≠ K' → False := by
    intro C J hJc hCJ hCG hqC hJK hJK'
    have hKJ : ⁅K, J⁆ ≤ pCoreOf 2 G₀ :=
      (h1.1.trans h1.2).trans (le_refl _) |>.trans (le_refl _) |> fun _ =>
        (Vol2Native.lemma_1_2_1_two hLS h37 hpc hKcomp hJc (Ne.symm hJK)).1.trans
          (Vol2Native.lemma_1_2_1_two hLS h37 hpc hKcomp hJc (Ne.symm hJK)).2
    have hK'J : ⁅K', J⁆ ≤ pCoreOf 2 G₀ :=
      (Vol2Native.lemma_1_2_1_two hLS h37 hpc hK'G₀ hJc (Ne.symm hJK')).1.trans
        (Vol2Native.lemma_1_2_1_two hLS h37 hpc hK'G₀ hJc (Ne.symm hJK')).2
    exact f2_caseB hq hq2 hG₀loc hev hKG₀ hK'leG₀ hCG hcomm
      ((Subgroup.commutator_mono le_rfl hCJ).trans hKJ)
      ((Subgroup.commutator_mono le_rfl hCJ).trans hK'J) hKcen hK'cen hqK hqK' hqC
  by_cases hA : CFSG.conjugate K g = K ∨ CFSG.conjugate K g = K'
  · by_cases hB : CFSG.conjugate K' g = K ∨ CFSG.conjugate K' g = K'
    ·
      have hKK'g : CFSG.conjugate K g ≠ CFSG.conjugate K' g := fun h =>
        hKK' (Subgroup.map_injective (MulEquiv.injective (MulAut.conj g⁻¹)) h)
      have hsup : CFSG.conjugate K g ⊔ CFSG.conjugate K' g = K ⊔ K' := by
        rcases hA with h1' | h1' <;> rcases hB with h2' | h2'
        · exact absurd (h1'.trans h2'.symm) hKK'g
        · rw [h1', h2']
        · rw [h1', h2', sup_comm]
        · exact absurd (h1'.trans h2'.symm) hKK'g
      have hconjK₀ : (K ⊔ K').map (MulAut.conj g⁻¹).toMonoidHom = K ⊔ K' := by
        rw [Subgroup.map_sup]; exact hsup
      have hgN : g ∈ Subgroup.normalizer (conjClosure K T : Set G) :=
        f2_mem_normalizer_of_conj_eq _ g (by rw [hK₀eq]; exact hconjK₀)
      have hCeN : Subgroup.centralizer ({e} : Set G) ≤
          Subgroup.normalizer (conjClosure K T : Set G) := by
        intro x hx
        have hxe : e * x = x * e := Subgroup.mem_centralizer_iff.1 hx e (Set.mem_singleton e)
        have hgx : g⁻¹ * x * g ∈ G₀ := by
          rw [hmemG₀]
          calc z * (g⁻¹ * x * g) = g⁻¹ * (e * x) * g := by rw [hz]; group
            _ = g⁻¹ * (x * e) * g := by rw [hxe]
            _ = (g⁻¹ * x * g) * z := by rw [hz]; group
        have key : g * (g⁻¹ * x * g) * g⁻¹ ∈ Subgroup.normalizer (conjClosure K T : Set G) :=
          mul_mem (mul_mem hgN (hG₀N hgx)) (inv_mem hgN)
        rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at key
      exact F.L2_notM (fun x hx => hCeN (F.L2_e hx))
    · have hJ₂K : J₂ ≠ K := by
        intro h
        apply hB
        left
        exact Subgroup.eq_of_le_of_card_ge (by rw [h] at hK'gJ₂; exact hK'gJ₂)
          (le_of_eq hK'g_card.symm)
      have hJ₂K' : J₂ ≠ K' := by
        intro h
        apply hB
        right
        exact Subgroup.eq_of_le_of_card_ge (by rw [h] at hK'gJ₂; exact hK'gJ₂)
          (le_of_eq (hK'card.trans hK'g_card.symm))
      exact caseB _ J₂ hJ₂c hK'gJ₂ hK'gG₀ hqK'g hJ₂K hJ₂K'
  · have hJ₁K : J₁ ≠ K := by
      intro h
      apply hA
      left
      exact Subgroup.eq_of_le_of_card_ge (by rw [h] at hKgJ₁; exact hKgJ₁)
        (le_of_eq hKg_card.symm)
    have hJ₁K' : J₁ ≠ K' := by
      intro h
      apply hA
      right
      exact Subgroup.eq_of_le_of_card_ge (by rw [h] at hKgJ₁; exact hKgJ₁)
        (le_of_eq (hK'card.trans hKg_card.symm))
    exact caseB _ J₁ hJ₁c hKgJ₁ hKgG₀ hqKg hJ₁K hJ₁K'

end CFSG.Quasithin.H13.NF314pt


module

public import CFSG.Quasithin.H13.U3S134Co
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Basic
public import CFSG.Quasithin.EmptyFaithful.T1531In68b
public import CFSG.Quasithin.H13.Sp62C3Verify

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem inP1_of_pres45 : ∀ σ : Perm (Fin 6), Pres45 σ → A6.InP1 σ := by decide +kernel

theorem gens_not_mem : ¬ A6.InP2 c012 ∧ ¬ A6.InP1 c2perm ∧ ¬ A6.InD6 c012 ∧
    ¬ A6.InD6 c2perm := by
  decide

theorem alt_transitive : ∀ τ : Perm (Fin 6),
    (∃ σ : Perm (Fin 6), Perm.sign σ = 1 ∧ G6.permAct 6 σ A6.e0123 = G6.permAct 6 τ A6.e0123) ∧
    (∃ σ : Perm (Fin 6), Perm.sign σ = 1 ∧ G6.permAct 6 σ A6.e45 = G6.permAct 6 τ A6.e45) := by
  decide +kernel

theorem c2_conj_not_mem : A6.InD6 (swap 0 2 * swap 1 3) ∧
    swap (0 : Fin 6) 2 * swap 1 3 ∈ alternatingGroup (Fin 6) ∧
    ¬ A6.InD6 (c2perm * (swap 0 2 * swap 1 3) * c2perm⁻¹) := by
  simp only [Perm.mem_alternatingGroup]
  decide

theorem c012_conj_not_mem : A6.InD6 (swap 0 1 * swap 4 5) ∧
    swap (0 : Fin 6) 1 * swap 4 5 ∈ alternatingGroup (Fin 6) ∧
    ¬ A6.InD6 (c012 * (swap 0 1 * swap 4 5) * c012⁻¹) := by
  simp only [Perm.mem_alternatingGroup]
  decide

theorem dvd_three_of_odd_dvd {n : ℕ} (h : n ∣ 24) (hn : ¬ 2 ∣ n) : n ∣ 3 := by
  have h24 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
  rw [h24] at h
  exact (Nat.Coprime.pow_right 3
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hn).symm).dvd_of_dvd_mul_left h

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem eq_alt_or_top {Y : Subgroup (Perm (Fin 6))} (hY : alternatingGroup (Fin 6) ≤ Y) :
    Y = alternatingGroup (Fin 6) ∨ Y = ⊤ := by
  have h := relIndex_mul_index hY
  rw [alternatingGroup.index_eq_two] at h
  rcases (Nat.dvd_prime Nat.prime_two).1 (Dvd.intro_left _ h) with h1 | h1
  · right
    exact index_eq_one.1 h1
  · left
    rw [h1] at h
    have h2 : (alternatingGroup (Fin 6)).relIndex Y = 1 := by omega
    exact le_antisymm (relIndex_eq_one.1 h2) hY

theorem s134_isPGroup_inf_centralizer (S : A6.Setting134 G T L V)
    (hA6 : quasithinO2QuotientIso L ↥(alternatingGroup (Fin 6))) :
    IsPGroup 2 ↥(L ⊓ centralizer (V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ, hker⟩ := hA6
  set C : Subgroup ↥L := (centralizer (V : Set G)).subgroupOf L with hC
  have hCn : C.Normal := by
    refine ⟨fun c hc l => ?_⟩
    rw [hC, mem_subgroupOf] at hc ⊢
    have hl : (l : G) ∈ normalizer (V : Set G) := S.frame.L_le l.2
    rw [mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : (l : G)⁻¹ * v * l ∈ V := by
      have := (mem_normalizer_iff.mp (inv_mem hl) v).mp hv
      simpa using this
    have h1 := hc _ hv'
    simp only [coe_mul, InvMemClass.coe_inv]
    calc v * ((l : G) * c * (l : G)⁻¹) = l * (((l : G)⁻¹ * v * l) * c) * (l : G)⁻¹ := by group
      _ = l * (c * ((l : G)⁻¹ * v * l)) * (l : G)⁻¹ := by rw [h1]
      _ = (l : G) * c * (l : G)⁻¹ * v := by group
  have hmap : (C.map φ).Normal := hCn.map φ hφ
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases hmap.eq_bot_or_eq_top with h | h
  ·
    have hCle : C ≤ CFSG.Open.pCore 2 ↥L := by
      rw [← hker]
      intro c hc
      have : φ c ∈ C.map φ := ⟨c, hc, rfl⟩
      rw [h, mem_bot] at this
      exact this
    have hp : IsPGroup 2 ↥C := (CFSG.LieType.BorelTits.pCore_isPGroup 2).to_le hCle
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hp ⟨⟨x, (mem_inf.1 hx).1⟩, by rw [hC, mem_subgroupOf]; exact (mem_inf.1 hx).2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg (fun y : ↥C => ((y : ↥L) : G)) hk
    simpa using this
  ·
    exfalso
    have hLC : ∀ l : ↥L, ∃ c ∈ C, ∃ q ∈ CFSG.Open.pCore 2 ↥L, l = c * q := by
      intro l
      have : φ l ∈ C.map φ := by rw [h]; exact mem_top _
      obtain ⟨c, hc, hcl⟩ := this
      refine ⟨c, hc, c⁻¹ * l, ?_, by group⟩
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hcl, inv_mul_cancel]
    have hO2 : ∀ q ∈ CFSG.Open.pCore 2 ↥L, (q : G) ∈ centralizer (V : Set G) := by
      intro q hq
      have hq' : (q : G) ∈ pCoreOf 2 L := by
        exact coe_mem_pCoreOf_iff.2 hq
      exact s134_pCoreOf_le_centralizer S hq' |> fun h => centralizer_le S.irr.1 h
    apply S.irr.2.1
    rw [← S.irr.2.2.2.1, commutator_eq_bot_iff_le_centralizer, le_centralizer_iff]
    intro l hl
    obtain ⟨c, hc, q, hq, hlcq⟩ := hLC ⟨l, hl⟩
    have h1 : (l : G) = c * q := congrArg Subtype.val hlcq
    rw [h1]
    exact mul_mem (by rw [hC, mem_subgroupOf] at hc; exact hc) (hO2 q hq)

theorem s134_normalizer_le_sup (h1222 : Stmt12_2_2) (S : A6.Setting134 G T L V) {z : G}
    (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G)) :
    normalizer (L : Set G) ≤ L ⊔ normalizer (L : Set G) ⊓ centralizer ({z} : Set G) := by
  intro m hm
  have hmN : m ∈ normalizer (V : Set G) := A6.Setting134.normalizer_L_le S h1222 hm
  obtain ⟨hzV, hzW⟩ := S.mem_V1_iff.1 hz
  have hψz : (S.frame.ψ ⟨z, hzV⟩ : A6.P6) = A6.e0123 ∨
      (S.frame.ψ ⟨z, hzV⟩ : A6.P6) = A6.e45 := by
    rcases A6.W1_cases _ (S.frame.ψ ⟨z, hzV⟩).2 hzW with h | h | h | h
    · exfalso
      apply hzL
      have : (⟨z, hzV⟩ : ↥V) = 1 := S.frame.ψ.injective (Subtype.ext (by rw [h, map_one]; rfl))
      rw [show z = 1 from congrArg Subtype.val this]
      exact one_mem _
    · exfalso
      apply hzL
      have : (⟨z, hzV⟩ : ↥V) = ⟨S.zV, S.zV_mem_V⟩ :=
        S.frame.ψ.injective (Subtype.ext (by rw [h, S.psi_zV]))
      exact (S.mem_centralizer_L_iff ⟨z, hzV⟩).2 (Or.inr this)
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨σ, hσA, hσ⟩ : ∃ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) ∧
      G6.permAct 6 σ (S.frame.ψ ⟨z, hzV⟩) = G6.permAct 6 (S.frame.ρ ⟨m, hmN⟩)
        (S.frame.ψ ⟨z, hzV⟩) := by
    rcases hψz with h | h
    · obtain ⟨σ, hs, he⟩ := (alt_transitive (S.frame.ρ ⟨m, hmN⟩)).1
      exact ⟨σ, Perm.mem_alternatingGroup.2 hs, by rw [h]; exact he⟩
    · obtain ⟨σ, hs, he⟩ := (alt_transitive (S.frame.ρ ⟨m, hmN⟩)).2
      exact ⟨σ, Perm.mem_alternatingGroup.2 hs, by rw [h]; exact he⟩
  obtain ⟨⟨l, hlN⟩, hlL, hlσ⟩ := (S.frame.image_L σ).2 hσA
  have hc : l⁻¹ * m ∈ centralizer ({z} : Set G) := by
    have hfix := (S.conj_eq_iff (⟨l, hlN⟩⁻¹ * ⟨m, hmN⟩) ⟨z, hzV⟩).2 (by
      apply Subtype.ext
      rw [G6.coreAct_coe, map_mul, map_inv, hlσ, map_mul, MulAut.mul_apply, ← hσ,
        ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
    rw [mem_centralizer_singleton_iff]
    simp only [coe_mul, InvMemClass.coe_inv] at hfix
    calc l⁻¹ * m * z = l⁻¹ * m * z * (l⁻¹ * m)⁻¹ * (l⁻¹ * m) := by group
      _ = z * (l⁻¹ * m) := by rw [hfix]
  have hlM : l ∈ normalizer (L : Set G) := le_normalizer hlL
  have : m = l * (l⁻¹ * m) := by group
  rw [this]
  exact mul_mem (mem_sup_left hlL)
    (mem_sup_right (mem_inf.2 ⟨mul_mem (inv_mem hlM) hm, hc⟩))

theorem s134_isPGroup_CMV (S : A6.Setting134 G T L V)
    (hA6 : quasithinO2QuotientIso L ↥(alternatingGroup (Fin 6)))
    (hM : normalizer (L : Set G) = L ⊔ T) :
    IsPGroup 2 ↥(normalizer (L : Set G) ⊓ centralizer (V : Set G)) := by
  have hCL := s134_isPGroup_inf_centralizer S hA6
  rintro ⟨x, hx⟩
  obtain ⟨hxM, hxC⟩ := mem_inf.1 hx
  rw [hM] at hxM
  obtain ⟨k, hk⟩ := pow_two_mem_of_sup S.T_le_NL S.h13.faithful.1.1 hxM
  have hxkC : x ^ 2 ^ k ∈ centralizer (V : Set G) := pow_mem hxC _
  obtain ⟨j, hj⟩ := hCL ⟨x ^ 2 ^ k, mem_inf.2 ⟨hk, hxkC⟩⟩
  refine ⟨k + j, Subtype.ext ?_⟩
  have h1 : (x ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [pow_add, pow_mul, h1]

theorem s134_CMV_le_T (S : A6.Setting134 G T L V)
    (hp : IsPGroup 2 ↥(normalizer (L : Set G) ⊓ centralizer (V : Set G))) (h1222 : Stmt12_2_2) :
    normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤ T := by
  have hTsyl : IsSylowTwoOf T (normalizer (L : Set G)) :=
    A5.isSylowTwoOf_of_le S.h13.sylow S.T_le_NL
  have hn : ((normalizer (L : Set G) ⊓ centralizer (V : Set G)).subgroupOf
      (normalizer (L : Set G))).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun m hm => ?_
    have hmV : m ∈ normalizer (V : Set G) := A6.Setting134.normalizer_L_le S h1222 hm
    refine mem_normalizer_inf (le_normalizer hm) ?_
    rw [mem_normalizer_iff]
    intro c
    have key : ∀ g ∈ normalizer (V : Set G), ∀ c ∈ centralizer (V : Set G),
        g * c * g⁻¹ ∈ centralizer (V : Set G) := by
      intro g hg c hc
      rw [mem_centralizer_iff] at hc ⊢
      intro v hv
      have hv' : g⁻¹ * v * g ∈ V := by
        have := (mem_normalizer_iff.mp (inv_mem hg) v).mp hv
        simpa using this
      have h1 := hc _ hv'
      calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * v := by group
    refine ⟨fun hc => key m hmV c hc, fun hc => ?_⟩
    have := key m⁻¹ (inv_mem hmV) _ hc
    simpa [mul_assoc] using this
  exact (CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
    inf_le_left hn hp).trans (pCoreOf_two_le_of_isSylowTwoOf hTsyl)

theorem s134_pCoreOf_M_le (S : A6.Setting134 G T L V) :
    pCoreOf 2 (normalizer (L : Set G)) ≤ centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowTwoOf T (normalizer (L : Set G)) :=
    A5.isSylowTwoOf_of_le S.h13.sylow S.T_le_NL
  have hOT : pCoreOf 2 (normalizer (L : Set G)) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsyl
  have hLTM : L ⊔ T ≤ normalizer (L : Set G) := sup_le le_normalizer S.T_le_NL
  have h1 : pCoreOf 2 (normalizer (L : Set G)) ≤ pCoreOf 2 (L ⊔ T) :=
    CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
      (hOT.trans le_sup_right) ((normal_subgroupOf_iff_le_normalizer (hOT.trans le_sup_right)).2
        (hLTM.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _)))
      (LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hred : IsTwoReducedIn (L ⊔ T) (reducedAggregate (L ⊔ T)) :=
    isTwoReducedIn_reducedAggregate (L ⊔ T)
  refine h1.trans (le_trans ?_ (centralizer_le S.irr.1))
  refine hred.2.2.2 _ (LieType.BorelTits.pCoreOf_le 2 _)
    (LieType.BorelTits.le_normalizer_pCoreOf 2 _) fun d hd => ?_
  obtain ⟨k, hk⟩ := (LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)) ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [this]
  exact one_mem _

theorem s134_quot_M (h1222 : Stmt12_2_2) (S : A6.Setting134 G T L V)
    (hp : IsPGroup 2 ↥(normalizer (L : Set G) ⊓ centralizer (V : Set G))) :
    quasithinO2QuotientIso (normalizer (L : Set G)) ↥(alternatingGroup (Fin 6)) ∨
      quasithinO2QuotientIso (normalizer (L : Set G)) (Perm (Fin 6)) := by
  have hMV : normalizer (L : Set G) ≤ normalizer (V : Set G) :=
    A6.Setting134.normalizer_L_le S h1222
  set ρ' : ↥(normalizer (L : Set G)) →* Perm (Fin 6) :=
    S.frame.ρ.comp (inclusion hMV) with hρ'
  have hker : ρ'.ker = CFSG.Open.pCore 2 ↥(normalizer (L : Set G)) := by
    ext x
    rw [MonoidHom.mem_ker, ← coe_mem_pCoreOf_iff]
    have h1 : ρ' x = 1 ↔ (x : G) ∈ centralizer (V : Set G) := by
      rw [hρ', MonoidHom.comp_apply]
      exact s134_rho_eq_one_iff S _
    rw [h1]
    constructor
    · intro hx
      refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2
        (normalizer (L : Set G) ⊓ centralizer (V : Set G)) _ inf_le_left ?_ hp
        (mem_inf.2 ⟨x.2, hx⟩)
      refine (normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun m hm => ?_
      have hmV : m ∈ normalizer (V : Set G) := hMV hm
      refine mem_normalizer_inf (le_normalizer hm) ?_
      rw [mem_normalizer_iff]
      intro c
      have key : ∀ g ∈ normalizer (V : Set G), ∀ c ∈ centralizer (V : Set G),
          g * c * g⁻¹ ∈ centralizer (V : Set G) := by
        intro g hg c hc
        rw [mem_centralizer_iff] at hc ⊢
        intro v hv
        have hv' : g⁻¹ * v * g ∈ V := by
          have := (mem_normalizer_iff.mp (inv_mem hg) v).mp hv
          simpa using this
        have h1 := hc _ hv'
        calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
          _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
          _ = g * c * g⁻¹ * v := by group
      refine ⟨fun hc => key m hmV c hc, fun hc => ?_⟩
      have := key m⁻¹ (inv_mem hmV) _ hc
      simpa [mul_assoc] using this
    · intro hx
      exact s134_pCoreOf_M_le S hx
  have hA : alternatingGroup (Fin 6) ≤ ρ'.range := by
    intro σ hσ
    obtain ⟨g, hgL, hgσ⟩ := (S.frame.image_L σ).2 hσ
    refine ⟨⟨g, le_normalizer hgL⟩, ?_⟩
    rw [hρ', MonoidHom.comp_apply]
    rw [show inclusion hMV ⟨(g : G), le_normalizer hgL⟩ = g from Subtype.ext rfl]
    exact hgσ
  rcases eq_alt_or_top hA with h | h
  · left
    refine ⟨ρ'.codRestrict _ (fun x => h ▸ ⟨x, rfl⟩), ?_, ?_⟩
    · rintro ⟨σ, hσ⟩
      rw [← h] at hσ
      obtain ⟨x, hx⟩ := hσ
      exact ⟨x, Subtype.ext hx⟩
    · rw [← hker]
      ext x
      simp only [MonoidHom.mem_ker]
      constructor
      · intro hx
        exact congrArg Subtype.val hx
      · intro hx
        exact Subtype.ext hx
  · right
    refine ⟨ρ', fun σ => ?_, hker⟩
    have : σ ∈ ρ'.range := by rw [h]; exact mem_top σ
    exact this

theorem relIndex_sup_eq {K T : Subgroup G} (hTK : T ≤ normalizer (K : Set G)) :
    T.relIndex (K ⊔ T) = (K ⊓ T).relIndex K := by
  have h1 := CFSG.QuasithinUnique.Lin2.card_sup_mul_card_inf hTK
  have h2 := relIndex_mul_card T (K ⊔ T)
  rw [inf_eq_left.2 le_sup_right] at h2
  have h3 := relIndex_mul_card (K ⊓ T) K
  rw [inf_eq_left.2 inf_le_left] at h3
  rw [sup_comm] at h1
  have hT : 0 < Nat.card ↥T := Nat.card_pos
  have hKT : 0 < Nat.card ↥(K ⊓ T) := Nat.card_pos
  rw [inf_comm] at h1
  have : T.relIndex (K ⊔ T) * Nat.card ↥T * Nat.card ↥(K ⊓ T) =
      (K ⊓ T).relIndex K * Nat.card ↥(K ⊓ T) * Nat.card ↥T := by
    rw [h2, h3, h1, mul_comm]
  have h4 : T.relIndex (K ⊔ T) * Nat.card ↥(K ⊓ T) * Nat.card ↥T =
      (K ⊓ T).relIndex K * Nat.card ↥(K ⊓ T) * Nat.card ↥T := by
    rw [← this]; ring
  exact Nat.eq_of_mul_eq_mul_right hKT (Nat.eq_of_mul_eq_mul_right hT h4)

theorem quot_S3_of_index_three {X P : Subgroup G} (hsyl : IsSylowTwoOf P X)
    (h3 : P.relIndex X = 3) (hN : ¬ X ≤ normalizer (P : Set G)) :
    quasithinO2QuotientIso X (Perm (Fin 3)) := by
  obtain ⟨e⟩ := nonempty_quotient_pCore_of_relIndex_eq_three' hsyl h3 hN
  refine (quasithinO2QuotientIso_iff X _).2 ⟨?_⟩
  exact (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open (↥X) 2)).trans e

theorem s134_relIndex_three (S : A6.Setting134 G T L V) {K : Subgroup G}
    {P : Subgroup (Perm (Fin 6))}
    (hP : Nat.card ↥(P ⊓ alternatingGroup (Fin 6)) = 24) (hKL : K ≤ L)
    (hKP : ∀ x : ↥(normalizer (V : Set G)), (x : G) ∈ K → S.frame.ρ x ∈ P)
    (hCK : K ⊓ centralizer (V : Set G) ≤ T) (hTK : T ≤ normalizer (K : Set G))
    {k : G} (hk : k ∈ K) (hkD : ¬ A6.InD6 (S.frame.ρ ⟨k, S.frame.L_le (hKL hk)⟩)) :
    (K ⊓ T).relIndex K = 3 := by
  have hKV : K ≤ normalizer (V : Set G) := hKL.trans S.frame.L_le
  set f : ↥K →* Perm (Fin 6) := S.frame.ρ.comp (inclusion hKV) with hf
  set H : Subgroup ↥K := (K ⊓ T).subgroupOf K with hH
  have hker : f.ker ≤ H := by
    intro x hx
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply] at hx
    have hxC : (x : G) ∈ centralizer (V : Set G) := (s134_rho_eq_one_iff S _).1 hx
    rw [hH, mem_subgroupOf]
    exact mem_inf.2 ⟨x.2, hCK (mem_inf.2 ⟨x.2, hxC⟩)⟩
  have h1 : (H.map f).relIndex ((⊤ : Subgroup ↥K).map f) = H.index := by
    rw [relIndex_map_map, sup_eq_left.2 hker, top_sup_eq, relIndex_top_right]
  have hrange : (⊤ : Subgroup ↥K).map f ≤ P ⊓ alternatingGroup (Fin 6) := by
    rintro _ ⟨x, -, rfl⟩
    refine mem_inf.2 ⟨hKP _ x.2, ?_⟩
    obtain ⟨⟨y, hyN⟩, hyL, hyσ⟩ : ∃ g : ↥(normalizer (V : Set G)), (g : G) ∈ L ∧
        S.frame.ρ g = f x := ⟨inclusion hKV x, hKL x.2, rfl⟩
    exact (S.frame.image_L _).1 ⟨⟨y, hyN⟩, hyL, hyσ⟩
  have h24 : Nat.card ↥((⊤ : Subgroup ↥K).map f) ∣ 24 := by
    rw [← hP]
    exact card_dvd_of_le hrange
  have hdvd : H.index ∣ 24 := by
    rw [← h1]
    exact (relIndex_dvd_card _ _).trans h24
  have hsyl : IsSylowTwoOf (K ⊓ T) K := by
    have hTsyl : IsSylowTwoOf T (K ⊔ T) := A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right
    have := A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTK)
    rwa [inf_comm] at this
  have hodd : ¬ 2 ∣ H.index := hsyl.2.2
  have h3 : H.index ∣ 3 := dvd_three_of_odd_dvd hdvd hodd
  rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
  · exfalso
    have hle : H = ⊤ := index_eq_one.1 h
    have hkT : (⟨k, hk⟩ : ↥K) ∈ H := hle ▸ mem_top _
    rw [hH, mem_subgroupOf] at hkT
    exact hkD (S.frame.T_D _ (mem_inf.1 hkT).2)
  · exact h

theorem s134_L2T_quot (S : A6.Setting134 G T L V)
    (hCT : normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤ T) :
    quasithinO2QuotientIso (l2Of S ⊔ T) (Perm (Fin 3)) := by
  have hTsyl : IsSylowTwoOf T (l2Of S ⊔ T) := A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right
  have hTK := s134_T_le_normalizer_L2 S
  obtain ⟨c, hcL2, hcN, hcρ⟩ := s134_exists_c2_mem_L2 S
  have hKP : ∀ x : ↥(normalizer (V : Set G)), (x : G) ∈ l2Of S → S.frame.ρ x ∈ A6.P2sub :=
    fun x hx => (s134_normalizer_V2_iff S x.2).1 (s134_L2_le_normalizer_V2 S hx)
  have hCK : l2Of S ⊓ centralizer (V : Set G) ≤ T := fun x hx =>
    hCT (mem_inf.2 ⟨le_normalizer (s134_L2_le_L S (mem_inf.1 hx).1), (mem_inf.1 hx).2⟩)
  have h3 : (l2Of S ⊓ T).relIndex (l2Of S) = 3 :=
    s134_relIndex_three S A6.card_P2A6 (s134_L2_le_L S) hKP hCK hTK hcL2
      (by rw [show (⟨c, S.frame.L_le (s134_L2_le_L S hcL2)⟩ : ↥(normalizer (V : Set G))) =
        ⟨c, hcN⟩ from rfl, hcρ]; exact gens_not_mem.2.2.2)
  refine quot_S3_of_index_three hTsyl (by rw [relIndex_sup_eq hTK, h3]) fun hN => ?_
  have hcT := hN (le_sup_left (b := T) hcL2)
  obtain ⟨hD, hA, hnot⟩ := c2_conj_not_mem
  obtain ⟨t, htT, htσ⟩ := S.frame.DA_T _ hD hA
  have hct : c * (t : G) * c⁻¹ ∈ T := (mem_normalizer_iff.mp hcT t).mp htT
  have hD' := S.frame.T_D ⟨c * t * c⁻¹, S.frame.T_le hct⟩ hct
  apply hnot
  have e : (⟨c * t * c⁻¹, S.frame.T_le hct⟩ : ↥(normalizer (V : Set G))) =
      ⟨c, hcN⟩ * t * ⟨c, hcN⟩⁻¹ := rfl
  rwa [e, map_mul, map_mul, map_inv, hcρ, htσ] at hD'

theorem s134_rho_mem_sup (S : A6.Setting134 G T L V) {K : Subgroup G}
    (hKV : K ≤ normalizer (V : Set G)) {P : Subgroup (Perm (Fin 6))}
    (hDP : A6.D6sub ≤ P) (hKP : ∀ x : ↥(normalizer (V : Set G)), (x : G) ∈ K → S.frame.ρ x ∈ P)
    (x : ↥(normalizer (V : Set G))) (hx : (x : G) ∈ K ⊔ T) : S.frame.ρ x ∈ P := by
  have hle : K ⊔ T ≤ (P.comap S.frame.ρ).map (normalizer (V : Set G)).subtype := by
    refine sup_le (fun k hk => ⟨⟨k, hKV hk⟩, hKP _ hk, rfl⟩) (fun t ht => ?_)
    exact ⟨⟨t, S.frame.T_le ht⟩, hDP (S.frame.T_D ⟨t, S.frame.T_le ht⟩ ht), rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

theorem s134_overgroups_M (h1222 : Stmt12_2_2) (S : A6.Setting134 G T L V)
    (hp : IsPGroup 2 ↥(normalizer (L : Set G) ⊓ centralizer (V : Set G))) :
    ∀ Y : Subgroup G, T ≤ Y → Y ≤ normalizer (L : Set G) →
      Y = T ∨ Y = L₁Of L (fsuV1 T V) ⊔ T ∨ Y = l2Of S ⊔ T ∨ Y = normalizer (L : Set G) := by
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set M := normalizer (L : Set G) with hM
  have hTsyl : IsSylowTwoOf T M := A5.isSylowTwoOf_of_le S.h13.sylow S.T_le_NL
  have hL1L : L₁ ≤ L := (oTwoRes_le _).trans inf_le_left
  have hL1N : L₁ ≤ normalizer (fsuV1 T V : Set G) := (oTwoRes_le _).trans inf_le_right
  obtain ⟨A₁, A₂, hT₁, hT₂, h₁M, h₂M, h₁₂, h₂₁, hA₁, hA₂, hcls⟩ :
      ∃ A₁ A₂ : Subgroup G, T ≤ A₁ ∧ T ≤ A₂ ∧ A₁ ≤ M ∧ A₂ ≤ M ∧ ¬ A₁ ≤ A₂ ∧ ¬ A₂ ≤ A₁ ∧
        A₁ ≠ M ∧ A₂ ≠ M ∧
        ∀ Y : Subgroup G, T ≤ Y → Y ≤ M → Y = T ∨ Y = A₁ ∨ Y = A₂ ∨ Y = M := by
    rcases s134_quot_M h1222 S hp with h | h
    · obtain ⟨P₀, X₁, X₂, hP, hP', hc, h1, h2, h12, h21⟩ := A6.modelData_A6.exists_data
      exact A6.overgroups_transport h hTsyl hP hP' hc h1 h2 h12 h21
    · obtain ⟨P₀, X₁, X₂, hP, hP', hc, h1, h2, h12, h21⟩ := A6.modelData_S6.exists_data
      exact A6.overgroups_transport h hTsyl hP hP' hc h1 h2 h12 h21
  obtain ⟨y, hyL1, hyN, hyρ⟩ := s134_exists_mem_L1 S c012_props.1 c012_props.2.1
    c012_props.2.2
  obtain ⟨c, hcL2, hcN, hcρ⟩ := s134_exists_c2_mem_L2 S
  have hP1 : ∀ x : ↥(normalizer (V : Set G)), (x : G) ∈ L₁ ⊔ T → S.frame.ρ x ∈ A6.P1sub :=
    s134_rho_mem_sup S (hL1L.trans S.frame.L_le) (fun σ hσ => (A6.D6sub_le hσ).1)
      (fun x hx => inP1_of_pres45 _ (s134_pres45 S x (hL1N hx)))
  have hP2 : ∀ x : ↥(normalizer (V : Set G)), (x : G) ∈ l2Of S ⊔ T → S.frame.ρ x ∈ A6.P2sub :=
    s134_rho_mem_sup S ((s134_L2_le_L S).trans S.frame.L_le) (fun σ hσ => (A6.D6sub_le hσ).2)
      (fun x hx => (s134_normalizer_V2_iff S x.2).1 (s134_L2_le_normalizer_V2 S hx))
  have hyM : y ∈ M := le_normalizer (hL1L hyL1)
  have hcM : c ∈ M := le_normalizer (s134_L2_le_L S hcL2)
  have hy1 : y ∈ L₁ ⊔ T := le_sup_left (b := T) hyL1
  have hc2 : c ∈ l2Of S ⊔ T := le_sup_left (b := T) hcL2
  have hyT : y ∉ T := fun h => gens_not_mem.2.2.1 (by
    have := S.frame.T_D ⟨y, hyN⟩ h; rwa [hyρ] at this)
  have hcT : c ∉ T := fun h => gens_not_mem.2.2.2 (by
    have := S.frame.T_D ⟨c, hcN⟩ h; rwa [hcρ] at this)
  have hy2 : y ∉ l2Of S ⊔ T := fun h => gens_not_mem.1 (by
    have := hP2 ⟨y, hyN⟩ h; rwa [hyρ] at this)
  have hc1 : c ∉ L₁ ⊔ T := fun h => gens_not_mem.2.1 (by
    have := hP1 ⟨c, hcN⟩ h; rwa [hcρ] at this)
  have hL1T_M : L₁ ⊔ T ≤ M := sup_le (hL1L.trans le_normalizer) S.T_le_NL
  have hL2T_M : l2Of S ⊔ T ≤ M := sup_le ((s134_L2_le_L S).trans le_normalizer) S.T_le_NL
  have hcase1 := hcls _ le_sup_right hL1T_M
  have hcase2 := hcls _ le_sup_right hL2T_M
  have hne1T : L₁ ⊔ T ≠ T := fun h => hyT (h ▸ hy1)
  have hne1M : L₁ ⊔ T ≠ M := fun h => hc1 (h ▸ hcM)
  have hne2T : l2Of S ⊔ T ≠ T := fun h => hcT (h ▸ hc2)
  have hne2M : l2Of S ⊔ T ≠ M := fun h => hy2 (h ▸ hyM)
  have hne12 : L₁ ⊔ T ≠ l2Of S ⊔ T := fun h => hy2 (h ▸ hy1)
  intro Y hTY hYM
  rcases hcls Y hTY hYM with h | h | h | h
  · exact Or.inl h
  · right
    rcases hcase1 with e | e | e | e
    · exact absurd e hne1T
    · exact Or.inl (h.trans e.symm)
    · rcases hcase2 with f | f | f | f
      · exact absurd f hne2T
      · exact Or.inr (Or.inl (h.trans f.symm))
      · exact absurd (e.trans f.symm) hne12
      · exact absurd f hne2M
    · exact absurd e hne1M
  · right
    rcases hcase1 with e | e | e | e
    · exact absurd e hne1T
    · rcases hcase2 with f | f | f | f
      · exact absurd f hne2T
      · exact absurd (e.trans f.symm) hne12
      · exact Or.inr (Or.inl (h.trans f.symm))
      · exact absurd f hne2M
    · exact Or.inl (h.trans e.symm)
    · exact absurd e hne1M
  · exact Or.inr (Or.inr (Or.inr h))

end CFSG.Quasithin.H13.U3

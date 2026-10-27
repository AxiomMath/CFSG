module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCFin
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TB

public section

namespace CFSG.Quasithin.H13.T614

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable abbrev mk614 (K : Subgroup G) : ↥K →* ModO2 K :=
  QuotientGroup.mk' (CFSG.pCore 2 ↥K)

@[expose] noncomputable def sylImg614 (K T : Subgroup G) : Subgroup (ModO2 K) :=
  ((T ⊓ K).subgroupOf K).map (mk614 K)

@[expose] noncomputable def hImg614 (K H : Subgroup G) : Subgroup (ModO2 K) :=
  (H.subgroupOf K).map (mk614 K)

theorem mk614_eq_one_of_mem_pCoreOf {K : Subgroup G} {x : G} (hxK : x ∈ K)
    (hx : x ∈ pCoreOf 2 K) : mk614 K ⟨x, hxK⟩ = 1 := by
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hyeq : y = ⟨x, hxK⟩ := Subtype.ext hyx
  rw [← hyeq]
  exact (QuotientGroup.eq_one_iff y).mpr hy

theorem sylImg614_spec {K T X : Subgroup G} (hXK : X ≤ K)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hsyl : IsSylowTwoOf T (K ⊔ T))
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hX5 : (X ⊓ T).relIndex X = 5) :
    IsSylowTwoOf (sylImg614 K T) ⊤ ∧ sylImg614 K T ≤ hImg614 K (X ⊔ (T ⊓ K)) ∧
      (sylImg614 K T).relIndex (hImg614 K (X ⊔ (T ⊓ K))) = 5 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsylK : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hsyl le_sup_left (sup_le Subgroup.le_normalizer hTK)
  have hOK : pCoreOf 2 K ≤ T ⊓ K := B6.pCoreOf_two_le_of_isSylowTwoOf hsylK
  have hkerS : (mk614 K).ker ≤ (T ⊓ K).subgroupOf K := by
    intro k hk
    rw [QuotientGroup.ker_mk'] at hk
    rw [Subgroup.mem_subgroupOf]
    exact hOK (mem_pCoreOf_of_mem_pCore614 hk)
  have hH₀K : X ⊔ (T ⊓ K) ≤ K := sup_le hXK inf_le_right
  have hSH : (T ⊓ K).subgroupOf K ≤ (X ⊔ (T ⊓ K)).subgroupOf K := fun k hk => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact Subgroup.mem_sup_right hk
  have hSyl : IsSylowTwoOf (sylImg614 K T) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact (hsylK.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm).map _
    · show ¬ 2 ∣ (sylImg614 K T).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      intro h2
      exact hsylK.2.2 (h2.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))
  have hSP : sylImg614 K T ≤ hImg614 K (X ⊔ (T ⊓ K)) := Subgroup.map_mono hSH
  refine ⟨hSyl, hSP, ?_⟩
  unfold sylImg614 hImg614
  rw [Subgroup.relIndex_map_map, sup_eq_left.mpr hkerS,
    sup_eq_left.mpr (hkerS.trans hSH), Subgroup.relIndex_subgroupOf hH₀K]
  have hTKX : T ⊓ K ≤ Subgroup.normalizer (X : Set G) := inf_le_left.trans hTX
  have hXT : X ⊓ (T ⊓ K) = X ⊓ T := by
    rw [inf_comm T K, ← inf_assoc, inf_eq_left.mpr hXK]
  have h1 := B6.relIndex_sup_eq_of_le_normalizer hTKX
  rw [sup_comm] at h1
  have h2 := Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_left : X ⊓ (T ⊓ K) ≤ X)
    (le_sup_left : X ≤ X ⊔ (T ⊓ K))
  have h3 := Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_right : X ⊓ (T ⊓ K) ≤ T ⊓ K)
    (le_sup_right : T ⊓ K ≤ X ⊔ (T ⊓ K))
  rw [Subgroup.inf_relIndex_right] at h3
  rw [hXT] at h2 h3
  rw [hX5, h1] at h2
  have hne : X.relIndex (T ⊓ K) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h4 : X.relIndex (T ⊓ K) * (T ⊓ K).relIndex (X ⊔ (T ⊓ K)) =
      X.relIndex (T ⊓ K) * 5 := by
    rw [h3, ← h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) h4

theorem not_thompsonJ_le_centralizerMod614 (hT0 : TitsOrderFact) (hB : TitsBasicFact)
    (hO5 : TitsOver5Fact) {T K X : Subgroup G} (htits : IsTits (ModO2 K))
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hsyl : IsSylowTwoOf T (K ⊔ T))
    (hXK : X ≤ K) (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hX5 : (X ⊓ T).relIndex X = 5)
    (hL4 : pCoreOf 2 (X ⊔ (T ⊓ K)) ≤
      thompsonJ T ⊔ centralizerMod (pCoreOf 2 K) (Subgroup.normalizer (K : Set G)) K) :
    ¬ thompsonJ T ≤ centralizerMod (pCoreOf 2 K) (Subgroup.normalizer (K : Set G)) K := by
  intro hJC
  classical
  obtain ⟨hS1, hS2, hS3⟩ := sylImg614_spec hXK hTK hsyl hTX hX5
  have hPeq : hImg614 K (X ⊔ (T ⊓ K)) = titsH614 (sylImg614 K T) :=
    hO5 (ModO2 K) htits _ _ hS1 hS2 hS3
  have hZQ : Subgroup.center (ModO2 K) = ⊥ := (hB _ htits).2.2
  have hC_all : thompsonJ T ⊔ centralizerMod (pCoreOf 2 K) (Subgroup.normalizer (K : Set G)) K ≤
      centralizerMod (pCoreOf 2 K) (Subgroup.normalizer (K : Set G)) K :=
    sup_le hJC le_rfl
  set S := sylImg614 K T with hSdef
  set P := hImg614 K (X ⊔ (T ⊓ K)) with hPdef
  set Z : Subgroup (ModO2 K) := (Subgroup.center ↥S).map S.subtype with hZdef
  have hPZ : ∀ x ∈ P, ∀ z ∈ Z, x * z = z * x := by
    intro x hx z hz
    rw [hPeq] at hx
    exact ((Subgroup.mem_centralizer_iff.mp hx) z hz).symm
  have hZS : Z ≤ S := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hZP : Z ≤ P := hZS.trans hS2
  have hS_ne : S ≠ ⊥ := by
    intro h0
    apply hS1.2.2
    show 2 ∣ S.relIndex ⊤
    rw [Subgroup.relIndex_top_right, h0, Subgroup.index_bot, hT0 _ htits]
    norm_num
  have hZne : Z ≠ ⊥ := by
    haveI : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS_ne
    haveI := IsPGroup.center_nontrivial hS1.2.1
    obtain ⟨y, hy⟩ := exists_ne (1 : Subgroup.center ↥S)
    intro hbot
    have hyZ : ((y : ↥S) : ModO2 K) ∈ Z := ⟨(y : ↥S), y.2, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hyZ
    apply hy
    apply Subtype.ext
    apply Subtype.ext
    simpa using hyZ
  set H₀ := X ⊔ (T ⊓ K) with hH₀def
  have hH₀K : H₀ ≤ K := sup_le hXK inf_le_right
  set Zk : Subgroup K := (Subgroup.comap (mk614 K) Z) ⊓ H₀.subgroupOf K with hZkdef
  set Zh : Subgroup G := Zk.map K.subtype with hZhdef
  have hZh_mem : ∀ g ∈ Zh, ∃ y : K, y ∈ Zk ∧ (y : G) = g := by
    intro g hg
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
    exact ⟨y, hy, hyg⟩
  have hZk_H : ∀ y ∈ Zk, (y : G) ∈ H₀ := fun y hy => Subgroup.mem_subgroupOf.mp hy.2
  have hZk_Z : ∀ y ∈ Zk, mk614 K y ∈ Z := fun y hy => hy.1
  have hgP : ∀ g (hg : g ∈ H₀) (hgK : g ∈ K), mk614 K ⟨g, hgK⟩ ∈ P := by
    intro g hg hgK
    exact Subgroup.mem_map.mpr ⟨⟨g, hgK⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hconjZh : ∀ g ∈ H₀, ∀ x ∈ Zh, g * x * g⁻¹ ∈ Zh := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := hZh_mem x hx
    have hgK : g ∈ K := hH₀K hg
    have hc := hPZ _ (hgP g hg hgK) _ (hZk_Z y hy)
    refine Subgroup.mem_map.mpr ⟨⟨g, hgK⟩ * y * (⟨g, hgK⟩ : K)⁻¹, ⟨?_, ?_⟩, ?_⟩
    · show mk614 K (⟨g, hgK⟩ * y * (⟨g, hgK⟩ : K)⁻¹) ∈ Z
      rw [map_mul, map_mul, map_inv]
      have e : mk614 K ⟨g, hgK⟩ * mk614 K y * (mk614 K ⟨g, hgK⟩)⁻¹ = mk614 K y := by
        rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      rw [e]
      exact hZk_Z y hy
    · refine Subgroup.mem_subgroupOf.mpr ?_
      show g * (y : G) * g⁻¹ ∈ H₀
      exact H₀.mul_mem (H₀.mul_mem hg (hZk_H y hy)) (H₀.inv_mem hg)
    · simp
  have hN : H₀ ≤ Subgroup.normalizer (Zh : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconjZh g hg x
    · intro hx
      have := hconjZh g⁻¹ (H₀.inv_mem hg) _ hx
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [e] at this
  have hZhH : Zh ≤ H₀ := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := hZh_mem g hg
    exact hZk_H y hy
  have hZhp : IsPGroup 2 ↥Zh := by
    rintro ⟨g, hg⟩
    obtain ⟨y, hy, rfl⟩ := hZh_mem g hg
    have hyS : mk614 K y ∈ S := hZS (hZk_Z y hy)
    obtain ⟨a, ha⟩ := hS1.2.1 ⟨mk614 K y, hyS⟩
    have ha' : mk614 K y ^ 2 ^ a = 1 := congrArg Subtype.val ha
    have h1 : mk614 K (y ^ 2 ^ a) = 1 := by rw [map_pow]; exact ha'
    have h2 : y ^ 2 ^ a ∈ (mk614 K).ker := MonoidHom.mem_ker.mpr h1
    rw [QuotientGroup.ker_mk'] at h2
    obtain ⟨b, hb⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥K) ⟨y ^ 2 ^ a, h2⟩
    have hb' : (y ^ 2 ^ a) ^ 2 ^ b = 1 := congrArg Subtype.val hb
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg (fun w : K => (w : G)) hb'
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    show (y : G) ^ 2 ^ (a + b) = 1
    rw [pow_add, pow_mul]
    exact this
  have hle : Zh ≤ pCoreOf 2 H₀ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZhH hN hZhp
  have hZbot : Z = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzc : z ∈ Subgroup.center (ModO2 K) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨⟨u, hu⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) q
      show mk614 K ⟨u, hu⟩ * z = z * mk614 K ⟨u, hu⟩
      have hzP := hZP hz
      rw [hPdef, hImg614, Subgroup.mem_map] at hzP
      obtain ⟨⟨k, hkK⟩, hkH', hkz⟩ := hzP
      have hkZh : k ∈ Zh := by
        refine Subgroup.mem_map.mpr ⟨⟨k, hkK⟩, ⟨?_, hkH'⟩, rfl⟩
        show mk614 K ⟨k, hkK⟩ ∈ Z
        rw [hkz]
        exact hz
      have hkC := hC_all (hL4 (hle hkZh))
      have hcomm : ∀ v (hvK : v ∈ K), mk614 K ⟨k, hkK⟩ * mk614 K ⟨v, hvK⟩ =
          mk614 K ⟨v, hvK⟩ * mk614 K ⟨k, hkK⟩ := by
        intro v hvK
        have hxK : k * v * k⁻¹ * v⁻¹ ∈ K :=
          K.mul_mem (K.mul_mem (K.mul_mem hkK hvK) (K.inv_mem hkK)) (K.inv_mem hvK)
        have hc := mk614_eq_one_of_mem_pCoreOf (K := K) hxK (hkC.2.2 v hvK)
        have e : (⟨k * v * k⁻¹ * v⁻¹, hxK⟩ : K) =
            ⟨k, hkK⟩ * ⟨v, hvK⟩ * ⟨k, hkK⟩⁻¹ * ⟨v, hvK⟩⁻¹ := rfl
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at hc
        calc mk614 K ⟨k, hkK⟩ * mk614 K ⟨v, hvK⟩
            = (mk614 K ⟨k, hkK⟩ * mk614 K ⟨v, hvK⟩ * (mk614 K ⟨k, hkK⟩)⁻¹ *
                (mk614 K ⟨v, hvK⟩)⁻¹) * (mk614 K ⟨v, hvK⟩ * mk614 K ⟨k, hkK⟩) := by group
          _ = mk614 K ⟨v, hvK⟩ * mk614 K ⟨k, hkK⟩ := by rw [hc, one_mul]
      rw [← hkz]
      exact (hcomm u hu).symm
    rw [hZQ, Subgroup.mem_bot] at hzc
    exact hzc
  exact hZne hZbot

theorem conjAct_apply614 {V : Subgroup G} (n : Subgroup.normalizer (V : Set G)) (v : V) :
    ((conjAct V n : MulAut V) v : G) = (n : G) * (v : G) * (n : G)⁻¹ := by
  rfl

theorem autOn_pCoreOf_le614 {V H : Subgroup G} (hHV : H ≤ Subgroup.normalizer (V : Set G)) :
    autOn (pCoreOf 2 H) V ≤ pCoreOf 2 (autOn H V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYA : autOn (pCoreOf 2 H) V ≤ autOn H V :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ (CFSG.LieType.BorelTits.pCoreOf_le 2 H))
  have hp : IsPGroup 2 ↥(autOn (pCoreOf 2 H) V) := by
    have hY2 : IsPGroup 2 ↥((pCoreOf 2 H).subgroupOf (Subgroup.normalizer (V : Set G))) := by
      rintro ⟨x, hx⟩
      obtain ⟨k, hk⟩ :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val hk
    exact hY2.map (conjAct V)
  have hstep : ∀ a ∈ autOn H V, ∀ b ∈ autOn (pCoreOf 2 H) V,
      a * b * a⁻¹ ∈ autOn (pCoreOf 2 H) V := by
    intro a ha b hb
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hb
    have hyH : (y : G) ∈ H := Subgroup.mem_subgroupOf.mp hy
    have hwP : (w : G) ∈ pCoreOf 2 H := Subgroup.mem_subgroupOf.mp hw
    have hcon : (y : G) * (w : G) * (y : G)⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hyH) (w : G)).mp hwP
    refine Subgroup.mem_map.mpr ⟨y * w * y⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ?_
      show ((y * w * y⁻¹ : Subgroup.normalizer (V : Set G)) : G) ∈ pCoreOf 2 H
      simpa using hcon
    · rw [map_mul, map_mul, map_inv]
  have hNorm : autOn H V ≤ Subgroup.normalizer ((autOn (pCoreOf 2 H) V : Subgroup (MulAut V)) :
      Set (MulAut V)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      exact hstep a ha b hb
    · intro hb
      have := hstep a⁻¹ (Subgroup.inv_mem _ ha) _ hb
      have e : a⁻¹ * (a * b * a⁻¹) * a⁻¹⁻¹ = b := by group
      rwa [e] at this
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hYA hNorm hp

theorem zV_le_omegaOne614 (hO3 : L216CoreFact) {T M L V K X : Subgroup G}
    (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4) (hXL : X ≤ L)
    (hX2 : X = oTwoUpper X) (hX5 : (X ⊓ T).relIndex X = 5)
    (hXn : ((X ⊓ T).subgroupOf X).Normal) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hXK : X ≤ K) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hCT : CharTwo (K ⊔ T)) :
    (V ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) ≤
      quasithinOmegaOneCenter (pCoreOf 2 (K ⊔ T)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsylKT : IsSylowTwoOf T (K ⊔ T) := h.toHyp5_0_1.isSylowTwoOf le_sup_right
  have hQT : pCoreOf 2 (K ⊔ T) ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hsylKT
  have hQN : X ⊔ T ≤ Subgroup.normalizer ((pCoreOf 2 (K ⊔ T) : Subgroup G) : Set G) :=
    (sup_le (hXK.trans le_sup_left) le_sup_right).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T))
  have hQX : pCoreOf 2 (K ⊔ T) ≤ pCoreOf 2 (X ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right) hQN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ T))
  have hHV : X ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (hXL.trans h.L_le_normalizer) h.T_le_normalizer
  have hWsub : autOn (pCoreOf 2 (K ⊔ T)) V ≤ autOn (T ⊓ L) V := by
    have e := hO3 G T M L V X h horth hXL hX2 hX5 hXn hTX
    calc autOn (pCoreOf 2 (K ⊔ T)) V ≤ autOn (pCoreOf 2 (X ⊔ T)) V :=
          Subgroup.map_mono (Subgroup.subgroupOf_mono _ hQX)
      _ ≤ pCoreOf 2 (autOn (X ⊔ T) V) := autOn_pCoreOf_le614 hHV
      _ = autOn (T ⊓ L) V := e
  intro z hz
  obtain ⟨hzV, hzC⟩ := hz
  have hcomm : ∀ q ∈ pCoreOf 2 (K ⊔ T), q * z = z * q := by
    intro q hq
    have hqN : q ∈ Subgroup.normalizer (V : Set G) := (hQT.trans h.T_le_normalizer) hq
    have hmem : conjAct V ⟨q, hqN⟩ ∈ autOn (pCoreOf 2 (K ⊔ T)) V :=
      Subgroup.mem_map.mpr ⟨⟨q, hqN⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    obtain ⟨w, hw, hwq⟩ := Subgroup.mem_map.mp (hWsub hmem)
    have hwT : (w : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp hw
    have hzw : (w : G) * z = z * (w : G) := (Subgroup.mem_centralizer_iff.mp hzC) w hwT
    have hact : (w : G) * z * (w : G)⁻¹ = q * z * q⁻¹ := by
      have := congrArg (fun φ : MulAut V => ((φ ⟨z, hzV⟩ : V) : G)) hwq
      simp only [conjAct_apply614] at this
      exact this
    have hz1 : (w : G) * z * (w : G)⁻¹ = z := by
      rw [hzw, mul_assoc, mul_inv_cancel, mul_one]
    exact mul_inv_eq_iff_eq_mul.mp (hact.symm.trans hz1)
  have hzcent : z ∈ Subgroup.centralizer ((pCoreOf 2 (K ⊔ T) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hcomm q hq
  have hzT : z ∈ K ⊔ T := (le_sup_right : T ≤ K ⊔ T) (h.le_T hzV)
  have hzQ : z ∈ pCoreOf 2 (K ⊔ T) := hCT ⟨hzT, hzcent⟩
  have hz2 : z ^ 2 = 1 := h.isElemAbelian.2 z hzV
  unfold quasithinOmegaOneCenter
  exact Subgroup.subset_closure ⟨⟨hzQ, hzcent⟩, hz2⟩

end CFSG.Quasithin.H13.T614

end

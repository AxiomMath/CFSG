module

public import CFSG.Quasithin.H13.A5F91
public import CFSG.Quasithin.H13.A5Producer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem isTwoReducedIn_of_comm (hVLT : V ≤ L ⊔ T)
    (hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G)) (hV : IsElemAbelian 2 V)
    (hc : ∀ g ∈ L ⊔ T, (∀ l ∈ L, ∃ k : ℕ,
      (g * l * g⁻¹ * l⁻¹) ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G)) →
        g ∈ Subgroup.centralizer (V : Set G)) :
    IsTwoReducedIn (L ⊔ T) V := by
  refine ⟨hVLT, hLTV, hV, fun D hDLT hDn hD2 d hd => hc d (hDLT hd) fun l hl => hD2 _ ?_⟩
  have h1 : l * d⁻¹ * l⁻¹ ∈ D :=
    (Subgroup.mem_normalizer_iff.mp (hDn (le_sup_left (a := L) hl)) _).mp (D.inv_mem hd)
  have e : d * l * d⁻¹ * l⁻¹ = d * (l * d⁻¹ * l⁻¹) := by group
  rw [e]
  exact D.mul_mem hd h1

theorem pCoreOf_le_centralizer_of_reduced (h : IsTwoReducedIn (L ⊔ T) V) :
    pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) :=
  h.2.2.2 _ (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) fun d hd => by
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T) ⟨d, hd⟩
      refine ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
      rw [this]
      exact Subgroup.one_mem _

theorem pCoreOf_le_pCoreOf_sup (hTN : T ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
    (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      (hTN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem pCoreOf_le_of_sylow (hT : quasithinIsSylowTwo T) {H : Subgroup G} (hTH : T ≤ H) :
    pCoreOf 2 H ≤ T := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have := pCoreOf_two_le_sylow H P (hP ▸ hTH)
  rwa [hP] at this

omit [Finite G] in
theorem comm_mem_of_central {P Z : Subgroup G} (hPL : P ≤ L) (hZL : Z ≤ L)
    (hLP : L ≤ Subgroup.normalizer (P : Set G)) (hperf : ⁅L, L⁆ = L)
    (hZ : ∀ c ∈ Z, ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ P) {y : G}
    (hy : ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ Z) {l : G} (hl : l ∈ L) : l * y * l⁻¹ * y⁻¹ ∈ P := by
  have hN : (P.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hPL]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.mp (hLP hk) h).mp hh
  let π := QuotientGroup.mk' (P.subgroupOf L)
  have hπ : ∀ x : ↥L, π x = 1 ↔ (x : G) ∈ P := fun x =>
    (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf
  have hcen : ∀ c x : ↥L, (c : G) ∈ Z → π c * π x = π x * π c := by
    intro c x hc
    have h1 : π (c * x * c⁻¹ * x⁻¹) = 1 := (hπ _).2 (hZ c hc x x.2)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π c * π x = (π c * π x * (π c)⁻¹ * (π x)⁻¹) * (π x * π c) := by group
      _ = π x * π c := by rw [h1, one_mul]
  have hcL : ∀ x : ↥L, (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ L := fun x => hZL (hy x x.2)
  let c : ↥L → ↥L := fun x => ⟨(x : G) * y * (x : G)⁻¹ * y⁻¹, hcL x⟩
  have hcZ : ∀ x : ↥L, ((c x : ↥L) : G) ∈ Z := fun x => hy x x.2
  have hcmul : ∀ a b : ↥L, c (a * b) = a * c b * a⁻¹ * c a := by
    intro a b
    apply Subtype.ext
    simp only [c, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hcomm : ∀ a b : ↥L, π (c a) * π (c b) = π (c b) * π (c a) := fun a b =>
    hcen (c a) (c b) (hcZ a)
  let f : ↥L →* ↥L ⧸ P.subgroupOf L :=
    { toFun := fun x => π (c x)
      map_one' := by
        have : c 1 = 1 := Subtype.ext (by simp [c])
        simp only [this, map_one]
      map_mul' := by
        intro a b
        show π (c (a * b)) = π (c a) * π (c b)
        rw [hcmul, map_mul, map_mul, map_mul, map_inv]
        have h2 : π a * π (c b) * (π a)⁻¹ = π (c b) := by
          rw [← hcen (c b) a (hcZ b)]
          group
        rw [h2, hcomm] }
  have hker : ⁅L, L⁆ ≤ f.ker.map L.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⟨a * b * a⁻¹ * b⁻¹, L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha))
      (L.inv_mem hb)⟩, ?_, by rw [commutatorElement_def]; rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have e : (⟨a * b * a⁻¹ * b⁻¹, L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha))
        (L.inv_mem hb)⟩ : ↥L) = ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h3 : f ⟨a, ha⟩ * f ⟨b, hb⟩ = f ⟨b, hb⟩ * f ⟨a, ha⟩ := hcomm _ _
    rw [h3]
    group
  rw [hperf] at hker
  obtain ⟨x, hx, rfl⟩ := hker hl
  exact (hπ (c x)).1 (MonoidHom.mem_ker.1 hx)

omit [Finite G] in
theorem comm_mem_of_centralizer {P : Subgroup G} (hPL : P ≤ L)
    (hLP : L ≤ Subgroup.normalizer (P : Set G)) (hperf : ⁅L, L⁆ = L)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hZ : ∀ c ∈ L ⊓ Subgroup.centralizer (V : Set G), ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ P) {y : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) (hyV : y ∈ Subgroup.centralizer (V : Set G))
    {l : G} (hl : l ∈ L) : l * y * l⁻¹ * y⁻¹ ∈ P := by
  refine comm_mem_of_central hPL inf_le_left hLP hperf hZ (fun l hl => ⟨?_, ?_⟩) hl
  · have : y * l⁻¹ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyL _).mp (L.inv_mem hl)
    have e : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
    rw [e]
    exact L.mul_mem hl this
  · exact (Subgroup.centralizer (V : Set G)).mul_mem
      (A5.conj_mem_centralizer_of_mem_normalizer (hLV hl) hyV)
      ((Subgroup.centralizer (V : Set G)).inv_mem hyV)

omit [Finite G] in
theorem inf_centralizer_eq_pCoreOf (hT2 : IsPGroup 2 T) (hO2T : pCoreOf 2 (L ⊔ T) ≤ T)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hO2 : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G))
    (hcomm : ∀ l ∈ L, ∀ t ∈ T ⊓ Subgroup.centralizer (V : Set G), l * t * l⁻¹ * t⁻¹ ∈ T) :
    T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) := by
  refine le_antisymm ?_ (le_inf hO2T hO2)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right)
    (sup_le ?_ ?_) (hT2.to_le inf_le_left)
  · refine A5.le_normalizer_of_forall_conj_mem fun l hl t ht => ⟨?_, ?_⟩
    · have e : l * t * l⁻¹ = (l * t * l⁻¹ * t⁻¹) * t := by group
      rw [e]
      exact T.mul_mem (hcomm l hl t ht) ht.1
    · exact A5.conj_mem_centralizer_of_mem_normalizer (hLV hl) ht.2
  · refine A5.le_normalizer_of_forall_conj_mem fun s hs t ht => ⟨?_, ?_⟩
    · exact T.mul_mem (T.mul_mem hs ht.1) (T.inv_mem hs)
    · exact A5.conj_mem_centralizer_of_mem_normalizer (hTV hs) ht.2

theorem pCoreOf_eq_bot_of_not_le {M X : Subgroup G} (huniq : IsUniqueM (L ⊔ T) M)
    (hLT : L ⊔ T ≤ X) (hX : ¬ X ≤ M) : pCoreOf 2 X = ⊥ := by
  by_contra h
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 X : Set G)) :=
    ⟨pCoreOf 2 X, h, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hXM' : X ≤ M' := (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X).trans hle
  have := huniq.2 M' ⟨hM', hLT.trans hXM'⟩
  exact hX (this ▸ hXM')

theorem coreIn_le_pCoreOf_of {H V₁ Vp M : Subgroup G} (huniq : IsUniqueM (L ⊔ T) M)
    (hTH : T ≤ H) (hHM : ¬ H ≤ M) (hHchar : CharTwo H)
    (hHV₁ : H ≤ Subgroup.centralizer (V₁ : Set G)) (hVp : IsElemAbelian 2 Vp) (hV₁Vp : V₁ ≤ Vp)
    (hCVL : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hO2L : pCoreOf 2 L ≤ T)
    (hCL : ∀ y ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G),
      ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L)
    (hodd : ∀ y ∈ H, y ∈ Subgroup.centralizer (Vp : Set G) → (∃ m : ℕ, Odd m ∧ y ^ m = 1) →
      y ∈ Subgroup.centralizer (V : Set G)) :
    coreIn (centralizerMod V₁ H Vp) H ≤ pCoreOf 2 H := by
  set K := coreIn (centralizerMod V₁ H Vp) H with hKdef
  have hKH : K ≤ H := coreIn_le_left _ _
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_coreIn _ _
  have hgenVp : ∀ y ∈ K, (∃ m : ℕ, Odd m ∧ y ^ m = 1) →
      y ∈ Subgroup.centralizer (Vp : Set G) := by
    rintro y hyK ⟨m, hm, hym⟩
    have hyC : y ∈ centralizerMod V₁ H Vp := coreIn_le_right _ _ hyK
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hyz : ∀ c ∈ V₁, y * c * y⁻¹ = c := by
      intro c hc
      have := Subgroup.mem_centralizer_iff.mp (hHV₁ (hKH hyK)) c hc
      calc y * c * y⁻¹ = c * y * y⁻¹ := by rw [this]
        _ = c := by group
    have := A5.conj_eq_of_odd_of_comm hVp hV₁Vp hm hym hyz hyC.2.2 hu
    calc u * y = y * u * y⁻¹ * y := by rw [this]
      _ = y * u := by group
  have hYV : oTwoRes K ≤ Subgroup.centralizer (V : Set G) :=
    (Subgroup.closure_le _).2 fun y hy => hodd y (hKH hy.1) (hgenVp y hy.1 hy.2) hy.2
  have hYH : H ≤ Subgroup.normalizer (oTwoRes K : Set G) :=
    A5.le_normalizer_oTwoRes_of_le_normalizer hHK
  have hLY : L ≤ Subgroup.normalizer (oTwoRes K : Set G) := by
    refine A5.le_normalizer_oTwoRes_of_gen fun l hl y hyK ⟨m, hm, hym⟩ => ?_
    have hyY : y ∈ oTwoRes K := Subgroup.subset_closure ⟨hyK, m, hm, hym⟩
    have hyCV : y ∈ Subgroup.centralizer (V : Set G) := hYV hyY
    have hcomm : l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L := hCL y ⟨hCVL hyCV, hyCV⟩ l hl
    have hmem : l * y * l⁻¹ ∈ oTwoRes K ⊔ pCoreOf 2 L := by
      have e : l * y * l⁻¹ = (l * y * l⁻¹ * y⁻¹) * y := by group
      rw [e]
      exact Subgroup.mul_mem _ (le_sup_right (a := oTwoRes K) hcomm)
        (le_sup_left (a := oTwoRes K) hyY)
    refine A5.mem_of_odd_of_mem_sup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      ((hO2L.trans hTH).trans hYH) hmem hm ?_
    rw [conj_pow, hym]
    group
  have hY : oTwoRes K = ⊥ := by
    by_contra hY
    have hchar : CharTwo (oTwoRes K) :=
      A4.charTwo_of_normal ((oTwoRes_le K).trans hKH) hYH hHchar
    have hO2 : pCoreOf 2 (oTwoRes K) ≠ ⊥ := by
      intro h0
      apply hY
      have hle : oTwoRes K ≤ oTwoRes K ⊓
          Subgroup.centralizer (pCoreOf 2 (oTwoRes K) : Set G) := by
        intro x hx
        refine ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
        rw [h0] at hy
        rw [show y = 1 from hy]
        simp
      have := hle.trans hchar
      rw [h0] at this
      exact le_bot_iff.mp this
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (oTwoRes K) : Set G)) :=
      ⟨_, hO2, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, rfl⟩
    have hN := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (oTwoRes K)
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hLTM' : L ⊔ T ≤ M' := sup_le (hLY.trans (hN.trans hle))
      ((hTH.trans hYH).trans (hN.trans hle))
    have := huniq.2 M' ⟨hM', hLTM'⟩
    exact hHM (this ▸ (hYH.trans (hN.trans hle)))
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKH hHK
    (A5.isPGroup_of_oTwoRes_eq_bot hY)

theorem hypF91_of {V₁ Vp H M : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hfaith : quasithinIsFaithfulLocal T L) (hEven : quasithinEvenCharacteristic G)
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hred : IsTwoReducedIn (L ⊔ T) V)
    (hcT : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T))
    (huniq : IsUniqueM (L ⊔ T) M) (hcard : Nat.card V₁ = 2) (hV₁Vp : V₁ < Vp) (hVpV : Vp ≤ V)
    (hTV₁ : T ≤ Subgroup.normalizer (V₁ : Set G)) (hH : InH (L₁Of L V₁ ⊔ T) H)
    (hHV₁ : H ≤ Subgroup.centralizer (V₁ : Set G)) (hHM : ¬ H ≤ M)
    (hker : coreIn (centralizerMod V₁ H Vp) H ≤ pCoreOf 2 H)
    (hb₁ : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (Vp : Set G))
    (hb₂ : ∀ W : Subgroup G, V₁ ≤ W → W ≤ Vp →
      L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (W : Set G) → W = V₁ ∨ W = Vp)
    (hc : H ⊓ Subgroup.normalizer (Vp : Set G) ≤ Subgroup.normalizer (V : Set G))
    (he : ∀ g ∈ H, ⁅V, conjSub g⁻¹ V⁆ ≤ V ⊓ conjSub g⁻¹ V → ⁅Vp, conjSub g⁻¹ V⁆ ≤ V₁ →
      ⁅conjSub g⁻¹ Vp, V⁆ ≤ V₁ → ⁅Vp, conjSub g⁻¹ V⁆ = ⊥ ∧ ⁅conjSub g⁻¹ Vp, V⁆ = ⊥) :
    HypF91 T V L V₁ Vp H where
  sylow := A5.isSylowTwoOf_of_le hT le_top
  elemAbelian := hred.2.2.1
  normalizes_L := hTN
  oTwoRes_eq := A5.oTwoRes_eq_of_faithful hfaith
  charTwo_L := A5.charTwo_of_faithful hEven hT hfaith
  reduced := hred
  cT := hcT
  card_V₁ := hcard
  V₁_lt_Vp := hV₁Vp
  Vp_le_V := hVpV
  T_normalizes_V₁ := hTV₁
  H_le_centralizer := hHV₁
  L₁T_le_H := hH.1
  charTwo_H := by
    obtain ⟨P, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
    exact CFSG.Quasithin.charTwo_of_inH hEven P ⟨le_sup_right.trans hH.1, hH.2⟩
  ker_le := hker
  L₁T_normalizes_Vp := hb₁
  irred := hb₂
  normalizer_le := hc
  o2_trivial := pCoreOf_eq_bot_of_not_le huniq le_sup_left fun h => hHM (le_sup_right.trans h)
  weak_e := he

end CFSG.Quasithin.H13.A6

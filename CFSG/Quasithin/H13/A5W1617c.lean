module

public import CFSG.Quasithin.H13.A5W1617b
public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.Quasithin.H13.A5W1617a
public import CFSG.Quasithin.H13.A5Y1367b

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits (pCoreOf_le pCoreOf_isPGroup normalizer_le_normalizer_pCoreOf)

theorem relIndex_centralizer_le_two {G : Type*} [Group G] [Finite G] {P : Subgroup G} {a v : G}
    (hv : v ∈ Subgroup.centralizer (P : Set G)) (hv2 : v ^ 2 = 1)
    (ha : ∀ p ∈ P, a * p * a⁻¹ * p⁻¹ ∈ Subgroup.zpowers v) :
    (P ⊓ Subgroup.centralizer ({a} : Set G)).relIndex P ≤ 2 := by
  have hcomm : ∀ p ∈ P, ∀ c ∈ Subgroup.zpowers v, c * p = p * c := by
    intro p hp c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact ((Commute.zpow_left (Subgroup.mem_centralizer_iff.mp hv p hp).symm k).eq)
  let f : ↥P →* ↥(Subgroup.zpowers v) :=
    { toFun := fun p => ⟨a * p * a⁻¹ * (p : G)⁻¹, ha p p.2⟩
      map_one' := by ext; simp
      map_mul' := fun p q => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        calc a * (↑p * ↑q) * a⁻¹ * (↑p * ↑q)⁻¹
            = a * ↑p * a⁻¹ * (a * ↑q * a⁻¹ * (↑q)⁻¹) * (↑p)⁻¹ := by group
          _ = a * ↑p * a⁻¹ * ((↑p)⁻¹ * (a * ↑q * a⁻¹ * (↑q)⁻¹)) := by
              rw [mul_assoc (a * ↑p * a⁻¹)]
              congr 1
              have h2 := hcomm (p : G)⁻¹ (P.inv_mem p.2) _ (ha q q.2)
              exact h2
          _ = a * ↑p * a⁻¹ * (↑p)⁻¹ * (a * ↑q * a⁻¹ * (↑q)⁻¹) := by group }
  have hker : (P ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf P = f.ker := by
    ext p
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_inf]
    constructor
    · rintro ⟨-, hp⟩
      apply Subtype.ext
      show a * (p : G) * a⁻¹ * (p : G)⁻¹ = 1
      have := Subgroup.mem_centralizer_singleton_iff.mp hp
      rw [← this]
      group
    · intro hp
      refine ⟨p.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : a * (p : G) * a⁻¹ * (p : G)⁻¹ = 1 := congrArg Subtype.val hp
      have h2 : a * (p : G) = (p : G) * a := by
        calc a * (p : G) = a * (p : G) * a⁻¹ * (p : G)⁻¹ * ((p : G) * a) := by group
          _ = (p : G) * a := by rw [h1, one_mul]
      exact h2.symm
  show ((P ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf P).index ≤ 2
  rw [hker, Subgroup.index_ker]
  calc Nat.card ↥f.range ≤ Nat.card ↥(Subgroup.zpowers v) := Subgroup.card_le_card_group _
    _ = orderOf v := Nat.card_zpowers v
    _ ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hv2)

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem not_le_centralizer_z_of_inYz {K : Subgroup G} (hK : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) :
    ¬ K ≤ Subgroup.centralizer ({S.z} : Set G) := by
  intro hKz
  obtain ⟨-, x, hx, hxz⟩ := S.inXz_autOn hK hT
  obtain ⟨⟨k, hkN⟩, hk, rfl⟩ := Setup.mem_autOn_iff.1 hx
  apply hxz
  apply Subtype.ext
  rw [InternalSec.coe_conjAct_apply]
  have hkz : k * S.z = S.z * k := Subgroup.mem_centralizer_singleton_iff.mp (hKz hk)
  show k * S.z * k⁻¹ = S.z
  rw [hkz]
  group

theorem not_le_centralizer_conj (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7)
    (h39 : Vol2Native.A39ForSQTKCat) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G)) (hK : K ∈ lFamily S.Tv)
    (hTK : S.Tv ≤ Subgroup.normalizer (K : Set G))
    (hz : ¬ K ≤ Subgroup.centralizer ({S.z} : Set G)) (g : G)
    (haT : ∀ t ∈ S.Tv, (g * S.z * g⁻¹) * t * (g * S.z * g⁻¹)⁻¹ * t⁻¹ ∈ Subgroup.zpowers S.v12) :
    ¬ K ≤ Subgroup.centralizer ({g * S.z * g⁻¹} : Set G) := by
  set a := g * S.z * g⁻¹ with ha
  intro hKa
  have : IsSimpleGroup G := S.h13.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ga := Subgroup.centralizer ({a} : Set G) with hGa
  set φ : G ≃* G := MulAut.conj g with hφ
  set T' := T.map φ.toMonoidHom with hT'
  have hφz : φ S.z = a := rfl
  have hT'syl : quasithinIsSylowTwo T' := by
    refine ⟨(isPGroup_map_equiv_iff 2 φ T).mpr S.h13.sylow.1, ?_⟩
    rw [hT', show T.map φ.toMonoidHom = T.map (φ : G →* G) from rfl, Subgroup.index_map_equiv]
    exact S.h13.sylow.2
  have hzT : ∀ t ∈ T, t * S.z = S.z * t := by
    intro t ht
    have := S.conj_z_of_mem_T ht
    calc t * S.z = t * S.z * t⁻¹ * t := by group
      _ = S.z * t := by rw [this]
  have haT' : ∀ t ∈ T', t * a = a * t := by
    rintro _ ⟨t, ht, rfl⟩
    show φ t * φ S.z = φ S.z * φ t
    rw [← map_mul, ← map_mul, hzT t ht]
  have hT'Ga : T' ≤ Ga := fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (haT' t ht)
  have hsylGa : IsSylowTwoOf T' Ga := isSylowTwoOf_of_le hT'syl hT'Ga
  set O := pCoreOf 2 Ga with hOdef
  have ha2 : a ^ 2 = 1 := by
    rw [ha, show (g * S.z * g⁻¹) ^ 2 = g * S.z ^ 2 * g⁻¹ by rw [pow_two, pow_two]; group,
      S.z_sq]
    group
  have ha1 : a ≠ 1 := by
    intro h
    apply S.z_ne_one
    have : g⁻¹ * a * g = 1 := by rw [h]; group
    rwa [ha, show g⁻¹ * (g * S.z * g⁻¹) * g = S.z by group] at this
  have haO : a ∈ O := by
    have hle : Subgroup.zpowers a ≤ Ga :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    have hN : Ga ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
      intro x hx
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hx).symm k).eq)
    have h2 : IsPGroup 2 (Subgroup.zpowers a) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one]; exact orderOf_eq_prime ha2 ha1)
    exact le_pCoreOf_of_normalizes hle hN h2 (Subgroup.mem_zpowers _)
  have hOne : O ≠ ⊥ := fun h => ha1 (by rw [h, Subgroup.mem_bot] at haO; exact haO)
  have hGachar : CharTwo Ga := by
    obtain ⟨S', hS'⟩ := exists_sylow_of_quasithinIsSylowTwo hT'syl
    exact CFSG.Quasithin.charTwo_of_inH S.h13.qtke.2.1 S' ⟨by rw [hS']; exact hT'Ga, hOne⟩
  have hOGa : O ≤ Ga := pCoreOf_le 2 Ga
  have hGaO : Ga ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 Ga)
  have hO2 : IsPGroup 2 O := pCoreOf_isPGroup 2 Ga
  have hfin : ∀ A B : Subgroup G, A.relIndex B ≠ 0 := fun A B => Subgroup.index_ne_zero_of_finite
  have hsylTv := S.isSylowTwoOf_Tv h1222 h517
  have hvTv : S.v12 ∈ Subgroup.centralizer (S.Tv : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.mp (S.Tv_le_Gv ht)
  have hv2 : S.v12 ^ 2 = 1 := S.elemAbelian_V.2 _ S.v12_mem_V
  set R := S.Tv ⊓ Ga with hR
  have hRidx : R.relIndex S.Tv ≤ 2 := relIndex_centralizer_le_two hvTv hv2 haT
  have hR2 : IsPGroup 2 R := S.isPGroup_T.to_le (inf_le_left.trans inf_le_left)
  obtain ⟨T'', hRT'', hT''⟩ := exists_isSylowTwoOf_of_le (show R ≤ Ga from inf_le_right) hR2
  have hTvT : S.Tv ≤ T := inf_le_left
  have hRTv : R ≤ S.Tv := inf_le_left
  have hcardT'' : Nat.card ↥T'' ≤ 4 * Nat.card ↥R := by
    have h1 : Nat.card ↥T'' = Nat.card ↥T := by
      rw [hT''.card_eq, ← hsylGa.card_eq, hT', card_map_equiv]
    have h2 : Nat.card ↥T = 2 * Nat.card ↥S.Tv := by
      have := Subgroup.relIndex_mul_card S.Tv T
      rw [show S.Tv.relIndex T = 2 from S.index_Tv, inf_eq_left.mpr hTvT] at this
      exact this.symm
    have h3 : Nat.card ↥S.Tv ≤ 2 * Nat.card ↥R := by
      have := Subgroup.relIndex_mul_card R S.Tv
      rw [inf_eq_left.mpr hRTv] at this
      rw [← this]
      exact Nat.mul_le_mul_right _ hRidx
    omega
  have hOT'' : O ≤ T'' := pCoreOf_two_le_of_isSylowTwoOf hT''
  have hidx : (O ⊓ Subgroup.normalizer (K : Set G)).relIndex O ≤ 4 := by
    have hRN : O ⊓ R ≤ O ⊓ Subgroup.normalizer (K : Set G) :=
      inf_le_inf_left _ (inf_le_left.trans hTK)
    have h1 : R.relIndex T'' * Nat.card ↥R = Nat.card ↥T'' := by
      have := Subgroup.relIndex_mul_card R T''
      rwa [inf_eq_left.mpr hRT''] at this
    have h2 : R.relIndex T'' ≤ 4 :=
      Nat.le_of_mul_le_mul_right (h1.trans_le hcardT'') Nat.card_pos
    calc (O ⊓ Subgroup.normalizer (K : Set G)).relIndex O ≤ (O ⊓ R).relIndex O :=
          Subgroup.relIndex_le_of_le_left hRN (hfin _ _)
      _ = R.relIndex O := by rw [inf_comm, Subgroup.inf_relIndex_right]
      _ ≤ R.relIndex T'' := Subgroup.relIndex_le_of_le_right hOT'' (hfin _ _)
      _ ≤ 4 := h2
  have hKp : ⁅K, K⁆ = K := perfect_of_mem_cComp hK
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := hKa.trans hGaO
  have hcon := fun {o : G} (ho : o ∈ O) => le_normalizer_conj_of_perfect hKp hKO hidx ho
  set Y := conjClosure K O with hY
  have hKY : K ≤ Y := le_conjClosure K O
  have hYK : Y ≤ Subgroup.normalizer (K : Set G) := by
    refine conjClosure_le fun o ho x hx => ?_
    have h1 := hcon (O.inv_mem ho) hx
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    intro y
    have h2 := h1 (o⁻¹ * y * o)
    have e1 : ∀ w : G, w ∈ K.map (MulAut.conj o⁻¹).toMonoidHom ↔ o * w * o⁻¹ ∈ K := by
      intro w
      rw [Subgroup.mem_map_equiv]
      simp
    rw [e1, e1] at h2
    rw [show o * (o⁻¹ * y * o) * o⁻¹ = y by group,
      show o * (x * (o⁻¹ * y * o) * x⁻¹) * o⁻¹ = o * x * o⁻¹ * y * (o * x * o⁻¹)⁻¹ by group] at h2
    exact h2
  have hYKO : Y ≤ K ⊔ O := conjClosure_le fun o ho x hx =>
    (K ⊔ O).mul_mem ((K ⊔ O).mul_mem (Subgroup.mem_sup_right ho) (Subgroup.mem_sup_left hx))
      ((K ⊔ O).inv_mem (Subgroup.mem_sup_right ho))
  have hKON : K ⊔ O ≤ Subgroup.normalizer (Y : Set G) := by
    refine sup_le ?_ (le_normalizer_conjClosure K O)
    intro k hk
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
    · have key : ∀ y ∈ Y, k * y * k⁻¹ ∈ Y := by
        intro y hy
        refine Subgroup.closure_induction (p := fun y _ => k * y * k⁻¹ ∈ Y) ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨o, ho, w, hw, rfl⟩
          have hko : k * o * k⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hKO hk) o).mp ho
          have hkw : k * w * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hw) (K.inv_mem hk)
          have := mem_conjClosure hko hkw
          rwa [show k * o * k⁻¹ * (k * w * k⁻¹) * (k * o * k⁻¹)⁻¹ = k * (o * w * o⁻¹) * k⁻¹ by
            group] at this
        · simp [Y.one_mem]
        · intro y₁ y₂ _ _ h₁ h₂
          have := Y.mul_mem h₁ h₂
          rwa [show k * y₁ * k⁻¹ * (k * y₂ * k⁻¹) = k * (y₁ * y₂) * k⁻¹ by group] at this
        · intro y _ h
          have := Y.inv_mem h
          rwa [show (k * y * k⁻¹)⁻¹ = k * y⁻¹ * k⁻¹ by group] at this
      exact key x hx
    · have key : ∀ y ∈ Y, k⁻¹ * y * k⁻¹⁻¹ ∈ Y := by
        intro y hy
        refine Subgroup.closure_induction (p := fun y _ => k⁻¹ * y * k⁻¹⁻¹ ∈ Y) ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨o, ho, w, hw, rfl⟩
          have hk' : k⁻¹ ∈ K := K.inv_mem hk
          have hko : k⁻¹ * o * k⁻¹⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hKO hk') o).mp ho
          have hkw : k⁻¹ * w * k⁻¹⁻¹ ∈ K := K.mul_mem (K.mul_mem hk' hw) (K.inv_mem hk')
          have := mem_conjClosure hko hkw
          rwa [show k⁻¹ * o * k⁻¹⁻¹ * (k⁻¹ * w * k⁻¹⁻¹) * (k⁻¹ * o * k⁻¹⁻¹)⁻¹ =
            k⁻¹ * (o * w * o⁻¹) * k⁻¹⁻¹ by group] at this
        · simp [Y.one_mem]
        · intro y₁ y₂ _ _ h₁ h₂
          have := Y.mul_mem h₁ h₂
          rwa [show k⁻¹ * y₁ * k⁻¹⁻¹ * (k⁻¹ * y₂ * k⁻¹⁻¹) = k⁻¹ * (y₁ * y₂) * k⁻¹⁻¹ by
            group] at this
        · intro y _ h
          have := Y.inv_mem h
          rwa [show (k⁻¹ * y * k⁻¹⁻¹)⁻¹ = k⁻¹ * y⁻¹ * k⁻¹⁻¹ by group] at this
      have := key x hx
      rwa [inv_inv] at this
  have hsubKO : IsSubnormal K (K ⊔ O) :=
    IsSubnormal.step hKY ((Subgroup.normal_subgroupOf_iff_le_normalizer hKY).2 hYK)
      (IsSubnormal.step hYKO ((Subgroup.normal_subgroupOf_iff_le_normalizer hYKO).2 hKON)
        (IsSubnormal.refl _))
  have hzV1 : S.z ∈ S.V1 := S.mem_V1.2 (Or.inr rfl)
  have hKTvG : K ⊔ S.Tv ≤ Subgroup.centralizer ({S.v12} : Set G) := sup_le hKG S.Tv_le_Gv
  have hKTvchar : CharTwo (K ⊔ S.Tv) := C1GN.charTwo_of_le hF hsylTv le_sup_right hKTvG
  have hsylKTv : IsSylowTwoOf S.Tv (K ⊔ S.Tv) := B6.isSylowTwoOf_mono hsylTv le_sup_right hKTvG
  have hzc : S.z ∈ centerOf (pCoreOf 2 (K ⊔ S.Tv)) :=
    omegaOneCenter_le_centerOf_pCoreOf_of_sylowIn le_sup_right hsylKTv.2.1 hsylKTv.2.2 hKTvchar
      (S.V1_le_omega_Tv hzV1)
  have hzΩ : S.z ∈ omegaOneCenterOf (pCoreOf 2 (K ⊔ S.Tv)) :=
    Subgroup.subset_closure ⟨hzc, S.z_sq⟩
  have hzK : ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ S.Tv)), K⁆ ≠ ⊥ := by
    intro h
    apply hz
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.commutator_mem_commutator hzΩ hk
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have hXK : IsXClass K :=
    ⟨ne_bot_of_mem_cComp hK, (C2Nine.oTwoUpper_eq_of_perfect hKp).symm,
      A4.charTwo_of_subnormal (subnormal_of_mem_cComp hK) hKTvchar⟩
  have hVK := (a4_9 hXK (subnormal_of_mem_cComp hK)).mp hzK
  have hΩK' := (a4_9 hXK hsubKO).mpr hVK
  have hOKO : O ≤ pCoreOf 2 (K ⊔ O) :=
    le_pCoreOf_of_normalizes le_sup_right (sup_le hKO Subgroup.le_normalizer) hO2
  have hKOGa : K ⊔ O ≤ Ga := sup_le hKa hOGa
  have hΩ : omegaOneCenterOf (pCoreOf 2 (K ⊔ O)) ≤ omegaOneCenterOf O := by
    refine Subgroup.closure_mono ?_
    rintro x ⟨hxc, hx2⟩
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hxc
    have hxCO : x ∈ Subgroup.centralizer (O : Set G) := Subgroup.centralizer_le hOKO hxC
    have hxO : x ∈ O := hGachar (Subgroup.mem_inf.mpr ⟨hKOGa (pCoreOf_le 2 _ hxP), hxCO⟩)
    exact ⟨Subgroup.mem_inf.mpr ⟨hxO, hxCO⟩, hx2⟩
  have hΩK : ⁅omegaOneCenterOf O, K⁆ ≠ ⊥ := fun h =>
    hΩK' (le_bot_iff.mp (h ▸ Subgroup.commutator_mono hΩ le_rfl))
  have hKspan : K ≤ cCompSpan Ga :=
    (Vol2Native.lemma_1_2_1_one hloc h39 hOne) ▸ le_perfectCore_of_perfect hKa hKp
  obtain ⟨K₁, hK₁, hK₁z⟩ : ∃ K₁ ∈ cComp Ga, ⁅omegaOneCenterOf O, K₁⁆ ≠ ⊥ := by
    by_contra hcon
    apply hΩK
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine hKspan.trans (sSup_le fun K₂ hK₂ => ?_)
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    by_contra h
    exact hcon ⟨K₂, hK₂, h⟩
  have hK₁Ga : K₁ ≤ Ga := le_of_mem_cComp hK₁
  have hK₁p : ⁅K₁, K₁⁆ = K₁ := perfect_of_mem_cComp hK₁
  have hK₁char : CharTwo K₁ := A4.charTwo_of_subnormal (subnormal_of_mem_cComp hK₁) hGachar
  have hXK₁ : IsXClass K₁ :=
    ⟨ne_bot_of_mem_cComp hK₁, (C2Nine.oTwoUpper_eq_of_perfect hK₁p).symm, hK₁char⟩
  have hOT' : O ≤ T' := pCoreOf_two_le_of_isSylowTwoOf hsylGa
  have hK₁T'Ga : K₁ ⊔ T' ≤ Ga := sup_le hK₁Ga hT'Ga
  have hK₁f : quasithinIsFaithfulLocal T' K₁ := by
    refine ⟨⟨hT'syl.1, cComp_mem_of_le hK₁ le_sup_left hK₁T'Ga,
      (isSylowTwoOf_of_le hT'syl le_sup_right).2.2, ?_⟩, fun N hNL hN hpow =>
        C2Nine.eq_of_perfect_of_pow_mem hK₁p hNL hN hpow,
      (quasithinGenFitting_eq_pCoreOf_iff K₁ 2).mpr hK₁char, ?_⟩
    · intro h0
      apply hOne
      have := le_pCoreOf_of_normalizes (hOT'.trans le_sup_right) (hK₁T'Ga.trans hGaO) hO2
      rw [h0] at this
      exact le_bot_iff.mp this
    · rw [← VY_eq_quasithinV2]
      exact (a4_9 hXK₁ (subnormal_of_mem_cComp hK₁)).mp hK₁z
  set K₁' := K₁.map φ.symm.toMonoidHom with hK₁'
  have hK₁'f : quasithinIsFaithfulLocal T K₁' := by
    have := quasithinIsFaithfulLocal_map φ.symm hK₁f
    rwa [hT', map_equiv_symm_map_equiv] at this
  have hQ₁ : QTH13 G T K₁' :=
    { S.h13 with faithful := hK₁'f, a5 := fun _ K hK => S.h13.a5 S.a5 K hK }
  obtain ⟨V₁, ⟨S₁⟩⟩ := exists_setting h132two h132fsu h132A5 hQ₁ (S.h13.a5 S.a5 K₁' hK₁'f)
  have hZ₁ := S₁.omegaOneCenter_inf_centralizer_L h331 h1327
  have hzC : S.z ∈ Subgroup.centralizer (K₁' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    have hka : k * a = a * k := Subgroup.mem_centralizer_singleton_iff.mp (hK₁Ga hk)
    have e : φ.symm.toMonoidHom k = g⁻¹ * k * g := by simp [hφ, MulAut.conj_symm_apply]
    rw [e]
    calc g⁻¹ * k * g * S.z = g⁻¹ * (k * a) * g := by rw [ha]; group
      _ = g⁻¹ * (a * k) * g := by rw [hka]
      _ = S.z * (g⁻¹ * k * g) := by rw [ha]; group
  have hz1 : S.z ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K₁' : Set G) :=
    Subgroup.mem_inf.mpr ⟨S.z_mem_omegaOneCenter, hzC⟩
  rw [hZ₁, Subgroup.mem_bot] at hz1
  exact S.z_ne_one hz1

end Setting

end CFSG.Quasithin.H13.A5

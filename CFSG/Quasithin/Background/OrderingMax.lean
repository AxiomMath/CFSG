module

public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.CharTwoLocal
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

private theorem normalizer_le_normalizer_centralizer (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ c ∈ Subgroup.centralizer (S : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.mp hg s).mp hs
    have h := hc _ hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * s := by group
  intro c
  refine ⟨fun hc => key g hg c hc, fun hc => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hc

private theorem le_normalizer_inf {S A B : Subgroup G}
    (hA : S ≤ Subgroup.normalizer (A : Set G)) (hB : S ≤ Subgroup.normalizer (B : Set G)) :
    S ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hA hg) x,
    Subgroup.mem_normalizer_iff.mp (hB hg) x]

private theorem le_normalizer_centralizer {S V : Subgroup G}
    (h : S ≤ Subgroup.normalizer (V : Set G)) :
    S ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
  h.trans (normalizer_le_normalizer_centralizer V)

section FiniteSection

variable [Finite G]

omit [Finite G] in
private theorem isPGroup_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) :
    IsPGroup 2 E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem pCoreOf_ne_bot_of_isTwoLocal {M : Subgroup G} (hM : IsTwoLocal M) :
    pCoreOf 2 M ≠ ⊥ := by
  obtain ⟨P, hP, hP2, rfl⟩ := hM
  intro h
  apply hP
  have := le_pCoreOf_normalizer 2 P hP2
  rw [h] at this
  exact le_bot_iff.mp this

theorem inH_of_inM {X M : Subgroup G} (h : InM X M) : InH X M :=
  ⟨h.2, pCoreOf_ne_bot_of_isTwoLocal h.1.1⟩

theorem exists_maxTwoLocal_ge {L : Subgroup G} (hL : IsTwoLocal L) :
    ∃ M : Subgroup G, quasithinIsMaxTwoLocal M ∧ L ≤ M := by
  obtain ⟨M, ⟨hM, hLM⟩, hmax⟩ := Set.exists_max_image
    {K : Subgroup G | IsTwoLocal K ∧ L ≤ K} (fun K => Nat.card K) (Set.toFinite _)
    ⟨L, hL, le_rfl⟩
  refine ⟨M, ⟨hM, fun H hH hMH => ?_⟩, hLM⟩
  exact (Subgroup.eq_of_le_of_card_ge hMH (hmax H ⟨hH, hLM.trans hMH⟩)).symm

theorem exists_inM_of_pCoreOf_ne_bot {H : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) :
    ∃ M : Subgroup G, InM H M := by
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
    ⟨pCoreOf 2 H, hH, pCoreOf_isPGroup 2 H, rfl⟩
  obtain ⟨M, hM, hle⟩ := exists_maxTwoLocal_ge hloc
  exact ⟨M, hM, (le_normalizer_pCoreOf 2 H).trans hle⟩

private theorem quasithinOmegaOneCenter_ne_bot {T : Subgroup G} (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥) :
    quasithinOmegaOneCenter T ≠ ⊥ := by
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT
  have hc : Nontrivial (Subgroup.center T) := hT2.center_nontrivial
  have hcp : IsPGroup 2 (Subgroup.center T) := hT2.to_subgroup _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hcp
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.card_eq_one_iff_unique] at hn
    exact not_subsingleton (Subgroup.center T) hn.1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center T) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  set g : G := ((x : T) : G) with hg
  have hgT : g ∈ T := (x : T).2
  have hgC : g ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨t, ht⟩)
  have hg2 : g ^ 2 = 1 := by
    have := congrArg (fun y : Subgroup.center T => ((y : T) : G)) hx2
    simpa using this
  have hg1 : g ≠ 1 := by
    intro h
    exact hx1 (Subtype.ext (Subtype.ext h))
  intro h
  have hmem : g ∈ quasithinOmegaOneCenter T := Subgroup.subset_closure ⟨⟨hgT, hgC⟩, hg2⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hg1 hmem

omit [Finite G] in
theorem VZ_ne_bot {T H : Subgroup G} (hZ : quasithinOmegaOneCenter T ≠ ⊥) : VZ T H ≠ ⊥ := fun h =>
  hZ (le_bot_iff.mp ((le_conjClosure (quasithinOmegaOneCenter T) H).trans h.le))

theorem ne_bot_of_inH (T : Sylow 2 G) {H : Subgroup G} (hH : InH (T : Subgroup G) H) :
    (T : Subgroup G) ≠ ⊥ := fun h => hH.2 (le_bot_iff.mp (h ▸ pCoreOf_two_le_sylow H T hH.1))

private theorem inf_center_ne_bot {T U : Subgroup G} (hT : IsPGroup 2 T) (hUT : U ≤ T)
    (hUn : T ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyU : (y : G) ∈ U := hy.1
  have hyC : (y : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) := ⟨hyU, y.2, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem charTwo_of_inH (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G) {H : Subgroup G}
    (hH : InH (T : Subgroup G) H) : CharTwo H := by
  have hTH : (T : Subgroup G) ≤ H := hH.1
  have hUT : pCoreOf 2 H ≤ T := pCoreOf_two_le_sylow H T hTH
  have hU2 : IsPGroup 2 (pCoreOf 2 H) := pCoreOf_isPGroup 2 H
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hZ : pCoreOf 2 H ⊓ ((T : Subgroup G) ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ :=
    inf_center_ne_bot T.isPGroup' hUT (hTH.trans hHN) hH.2
  have hSyl : IsSylowTwoOf (T : Subgroup G) ⊤ := by
    refine ⟨le_top, T.isPGroup', ?_⟩
    have : ((T : Subgroup G).subgroupOf ⊤).index = (T : Subgroup G).index :=
      Subgroup.relIndex_top_right _
    rw [this]
    exact T.not_dvd_index
  have hN : CharTwo (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
    CT.charTwo_normalizer_of_inf_center hEven hSyl hU2 hZ
  have hX : CharTwo (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G)) :=
    CT.CharTwo.inf_centralizer hN Subgroup.le_normalizer hU2
  have hNX : Subgroup.normalizer (pCoreOf 2 H : Set G) ≤ Subgroup.normalizer
      ((Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer
      (normalizer_le_normalizer_centralizer (pCoreOf 2 H))
  set X := Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓
    Subgroup.centralizer (pCoreOf 2 H : Set G) with hXdef
  have hNP : Subgroup.normalizer (pCoreOf 2 H : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    hNX.trans (normalizer_le_normalizer_pCoreOf 2 X)
  have hPN : pCoreOf 2 X ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (pCoreOf_le 2 X).trans inf_le_left
  have hP2 : IsPGroup 2 (pCoreOf 2 X) := pCoreOf_isPGroup 2 X
  have hPT : pCoreOf 2 X ≤ T :=
    (le_pCoreOf_of_le_normalizer 2 hPN hNP hP2).trans
      (pCoreOf_two_le_sylow _ T (hTH.trans hHN))
  have hPU : pCoreOf 2 X ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hPT.trans hTH) (hHN.trans hNP) hP2
  intro h hh
  obtain ⟨hhH, hhC⟩ := hh
  exact hPU (hX ⟨⟨hHN hhH, hhC⟩, Subgroup.centralizer_le hPU hhC⟩)

theorem isHv_of_inM (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G) {M : Subgroup G}
    (hM : InM (T : Subgroup G) M) : IsHv (T : Subgroup G) M := by
  have hF : CharTwo M := hEven M hM.1.1 ⟨T, hM.2⟩
  obtain ⟨-, hel⟩ := conjClosure_le_centerOf_pCoreOf M T hM.2 hF le_rfl
  have hVne : VZ (T : Subgroup G) M ≠ ⊥ :=
    VZ_ne_bot (quasithinOmegaOneCenter_ne_bot T.isPGroup' (ne_bot_of_inH T (inH_of_inM hM)))
  have hloc : IsTwoLocal (Subgroup.normalizer (VZ (T : Subgroup G) M : Set G)) :=
    ⟨_, hVne, isPGroup_of_isElemAbelian hel, rfl⟩
  exact (hM.1.2 _ hloc (le_normalizer_conjClosure _ _)).symm

omit [Finite G] in
private theorem relIndex_sup_eq_of_le_normalizer {D T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

private theorem not_two_dvd_relIndex_inf {S D : Subgroup G} (hS : ¬ 2 ∣ S.index)
    (hSN : S ≤ Subgroup.normalizer (D : Set G)) : ¬ 2 ∣ (S ⊓ D).relIndex D := by
  have h1 : (S ⊓ D).relIndex S * S.relIndex (S ⊔ D) = (S ⊓ D).relIndex (S ⊔ D) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
  have h2 : (S ⊓ D).relIndex D * D.relIndex (S ⊔ D) = (S ⊓ D).relIndex (S ⊔ D) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
  have h3 : D.relIndex (S ⊔ D) = (S ⊓ D).relIndex S :=
    (relIndex_sup_eq_of_le_normalizer hSN).trans (Subgroup.inf_relIndex_left S D).symm
  have h4 : 0 < (S ⊓ D).relIndex S :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := ((S ⊓ D).subgroupOf S)))
  have h5 : (S ⊓ D).relIndex D = S.relIndex (S ⊔ D) := by
    refine Nat.eq_of_mul_eq_mul_left h4 ?_
    rw [h3] at h2
    rw [mul_comm ((S ⊓ D).relIndex S) ((S ⊓ D).relIndex D), h2, ← h1]
  rw [h5]
  exact fun h => hS (h.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))

theorem exists_mul_of_sylow {M C R : Subgroup G} (hCM : C ≤ M)
    (hN : M ≤ Subgroup.normalizer (C : Set G)) (hRC : R ≤ C) (hR : IsPGroup 2 R)
    (hodd : ¬ 2 ∣ R.relIndex C) :
    ∀ m ∈ M, ∃ n ∈ M ⊓ Subgroup.normalizer (R : Set G), ∃ c ∈ C, m = n * c := by
  have hRM : R ≤ M := hRC.trans hCM
  have hnormal : (C.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have hR'C : R.subgroupOf M ≤ C.subgroupOf M := Subgroup.subgroupOf_mono M hRC
  have hp : IsPGroup 2 ((R.subgroupOf M).subgroupOf (C.subgroupOf M)) :=
    (hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRM).symm).of_equiv
      (Subgroup.subgroupOfEquivOfLe hR'C).symm
  have hidx : ¬ 2 ∣ ((R.subgroupOf M).subgroupOf (C.subgroupOf M)).index := by
    have h : ((R.subgroupOf M).subgroupOf (C.subgroupOf M)).index = R.relIndex C :=
      Subgroup.relIndex_subgroupOf hCM
    rw [h]
    exact hodd
  let P : Sylow 2 (C.subgroupOf M) := hp.toSylow hidx
  have hfrat := Sylow.normalizer_sup_eq_top P
  have hmap : Subgroup.map (C.subgroupOf M).subtype (P : Subgroup (C.subgroupOf M)) =
      R.subgroupOf M := by
    simp only [P, IsPGroup.toSylow_coe]
    exact Subgroup.map_subgroupOf_eq_of_le hR'C
  rw [hmap] at hfrat
  intro m hm
  have hm' : (⟨m, hm⟩ : M) ∈ (⊤ : Subgroup M) := Subgroup.mem_top _
  rw [← hfrat] at hm'
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hm'
  refine ⟨(y : G), ?_, (z : G), Subgroup.mem_subgroupOf.mp hz, (congrArg Subtype.val hyz).symm⟩
  have : (y : G) ∈ (Subgroup.normalizer ((R.subgroupOf M : Subgroup M) : Set M)).map M.subtype :=
    ⟨y, hy, rfl⟩
  rwa [CT.map_subtype_normalizer hRM] at this

@[expose] def IsOrdMaximalIn (T : Subgroup G) (𝓕 : Subgroup G → Prop) (H : Subgroup G) : Prop :=
  𝓕 H ∧ ∀ H' : Subgroup G, 𝓕 H' → OrdLE T H H' → H' = H

@[expose] def InHv (T H : Subgroup G) : Prop := InH T H ∧ IsHv T H

theorem exists_isOrdMaximalIn_ge {T : Subgroup G} {𝓕 : Subgroup G → Prop}
    (h𝓕 : ∀ K, 𝓕 K → IsHv T K) {H : Subgroup G} (hH : 𝓕 H) :
    ∃ K, IsOrdMaximalIn T 𝓕 K ∧ OrdLE T H K := by
  obtain ⟨K, ⟨hK𝓕, hHK⟩, hmax⟩ := Set.exists_max_image
    {K : Subgroup G | 𝓕 K ∧ OrdLE T H K} (fun K => Nat.card (VZ T K)) (Set.toFinite _)
    ⟨H, hH, ordLE_refl T H⟩
  refine ⟨K, ⟨hK𝓕, fun K' hK' hKK' => ?_⟩, hHK⟩
  have hHK' : OrdLE T H K' := ordLE_trans (h𝓕 H hH) hHK hKK'
  have hV : VZ T K = VZ T K' :=
    Subgroup.eq_of_le_of_card_ge (VZ_le_of_ordLE hKK') (hmax K' ⟨hK', hHK'⟩)
  exact (eq_of_VZ_eq (h𝓕 K hK𝓕) (h𝓕 K' hK') hV).symm

omit [Finite G] in
theorem isUniqueM_of_isOrdMaximalIn {T M X : Subgroup G}
    (hmax : IsOrdMaximalIn T (InM T) M) (hX : InH T X) (hXM : X ≤ M)
    (hcov : ∀ m ∈ M, ∃ x ∈ X, ∃ c ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G), m = x * c) :
    IsUniqueM X M := by
  refine ⟨⟨hmax.1.1, hXM⟩, fun M₂ hM₂ => ?_⟩
  refine hmax.2 M₂ ⟨hM₂.1, hX.1.trans hM₂.2⟩ ?_
  intro m hm
  obtain ⟨x, hx, c, hc, rfl⟩ := hcov m hm
  exact ⟨x, ⟨hXM hx, hM₂.2 hx⟩, c, hc, rfl⟩

theorem isOrdMaximalIn_inHv_iff (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G)
    {H : Subgroup G} :
    IsOrdMaximalIn (T : Subgroup G) (InHv (T : Subgroup G)) H ↔
      IsOrdMaximalIn (T : Subgroup G) (InM (T : Subgroup G)) H := by
  have hMv : ∀ M, InM (T : Subgroup G) M → InHv (T : Subgroup G) M := fun M hM =>
    ⟨inH_of_inM hM, isHv_of_inM hEven T hM⟩
  have hforward : ∀ K, IsOrdMaximalIn (T : Subgroup G) (InHv (T : Subgroup G)) K →
      InM (T : Subgroup G) K := by
    rintro K ⟨hHv, hmax⟩
    obtain ⟨M₂, hM₂⟩ := exists_inM_of_pCoreOf_ne_bot hHv.1.2
    have hM₂T : InM (T : Subgroup G) M₂ := ⟨hM₂.1, hHv.1.1.trans hM₂.2⟩
    have heq : M₂ = K := hmax M₂ (hMv M₂ hM₂T) (ordLE_of_le hM₂.2)
    rw [heq] at hM₂T
    exact hM₂T
  constructor
  · intro h
    exact ⟨hforward H h, fun M' hM' hle => h.2 M' (hMv M' hM') hle⟩
  · intro h
    obtain ⟨K, hK, hHK⟩ := exists_isOrdMaximalIn_ge (T := (T : Subgroup G))
      (𝓕 := InHv (T : Subgroup G)) (fun _ hK => hK.2) (hMv H h.1)
    have hKH : K = H := h.2 K (hforward K hK) hHK
    rw [hKH] at hK
    exact hK

namespace A57

@[expose] def CaseA (T M V : Subgroup G) : Prop := V = VZ T M

@[expose] def CaseB (T M V : Subgroup G) : Prop :=
  V = conjClosure (quasithinOmegaOneCenter T ⊓ V) M ∧
    ∀ M' : Subgroup G, IsOrdMaximalIn T (InM T) M' → M' = M

omit [Finite G] in
private theorem exists_Z' {T M V : Subgroup G} (h : CaseA T M V ∨ CaseB T M V) :
    ∃ Z' : Subgroup G, Z' ≤ quasithinOmegaOneCenter T ∧ V = conjClosure Z' M := by
  rcases h with h | h
  · exact ⟨quasithinOmegaOneCenter T, le_rfl, h⟩
  · exact ⟨quasithinOmegaOneCenter T ⊓ V, inf_le_left, h.1⟩

omit [Finite G] in
private theorem conjAct_apply_coe (V : Subgroup G) (g : Subgroup.normalizer (V : Set G))
    (v : V) : ((conjAct V g v : V) : G) = g * v * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) v

omit [Finite G] in
private theorem conjAct_eq_one_of_mem_centralizer {V : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (V : Set G)) (hcn : c ∈ Subgroup.normalizer (V : Set G)) :
    conjAct V ⟨c, hcn⟩ = 1 := by
  ext v
  rw [conjAct_apply_coe, MulAut.one_apply]
  have h := Subgroup.mem_centralizer_iff.mp hc v v.2
  show c * (v : G) * c⁻¹ = v
  rw [← h, mul_inv_cancel_right]

omit [Finite G] in
private theorem autOn_eq_of_factor {M N V : Subgroup G} (hNM : N ≤ M)
    (hMn : M ≤ Subgroup.normalizer (V : Set G))
    (hfac : ∀ m ∈ M, ∃ n ∈ N, ∃ c ∈ M ⊓ Subgroup.centralizer (V : Set G), m = n * c) :
    autOn M V = autOn N V := by
  apply le_antisymm
  · rintro φ ⟨g, hg, rfl⟩
    obtain ⟨n, hn, c, hc, hm⟩ := hfac (g : G) (Subgroup.mem_subgroupOf.mp hg)
    have hnn : n ∈ Subgroup.normalizer (V : Set G) := hMn (hNM hn)
    have hcn : c ∈ Subgroup.normalizer (V : Set G) := hMn hc.1
    have hg' : g = ⟨n, hnn⟩ * ⟨c, hcn⟩ := Subtype.ext hm
    rw [hg', map_mul, conjAct_eq_one_of_mem_centralizer hc.2 hcn, mul_one]
    exact Subgroup.mem_map.mpr ⟨⟨n, hnn⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
  · exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ hNM)

private theorem facts (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G) {M V Z' : Subgroup G}
    (hM : InM (T : Subgroup G) M) (hZ' : Z' ≤ quasithinOmegaOneCenter (T : Subgroup G))
    (hV : V = conjClosure Z' M) :
    IsElemAbelian 2 V ∧ M ≤ Subgroup.normalizer (V : Set G) ∧
      V ≤ (T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) ∧
      (T : Subgroup G) ≤ M ⊓ Subgroup.normalizer
        (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ∧
      (∀ m ∈ M, ∃ n ∈ M ⊓ Subgroup.normalizer
        (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G),
          ∃ c ∈ M ⊓ Subgroup.centralizer (V : Set G), m = n * c) ∧
      V = conjClosure Z' (M ⊓ Subgroup.normalizer
        (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) := by
  have hTM : (T : Subgroup G) ≤ M := hM.2
  have hF : CharTwo M := hEven M hM.1.1 ⟨T, hTM⟩
  have hVn : M ≤ Subgroup.normalizer (V : Set G) := by
    rw [hV]
    exact le_normalizer_conjClosure Z' M
  obtain ⟨hle, hel⟩ := conjClosure_le_centerOf_pCoreOf M T hTM hF hZ'
  rw [← hV] at hle hel
  have hVT : V ≤ T := hle.trans (inf_le_left.trans (pCoreOf_two_le_sylow M T hTM))
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => by
      have := hel.1
      exact setLike_mul_comm hv hx
  have hTV : (T : Subgroup G) ≤ Subgroup.normalizer (V : Set G) := hTM.trans hVn
  have hTN : (T : Subgroup G) ≤ M ⊓ Subgroup.normalizer
      (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    le_inf hTM (le_normalizer_inf Subgroup.le_normalizer (le_normalizer_centralizer hTV))
  have hfac : ∀ m ∈ M, ∃ n ∈ M ⊓ Subgroup.normalizer
      (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G),
        ∃ c ∈ M ⊓ Subgroup.centralizer (V : Set G), m = n * c := by
    have hN : M ≤ Subgroup.normalizer
        ((M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
      le_normalizer_inf Subgroup.le_normalizer (le_normalizer_centralizer hVn)
    refine exists_mul_of_sylow inf_le_left hN (inf_le_inf_right _ hTM)
      (T.isPGroup'.to_le inf_le_left) ?_
    have h := not_two_dvd_relIndex_inf (S := (T : Subgroup G))
      (D := M ⊓ Subgroup.centralizer (V : Set G)) T.not_dvd_index (hTM.trans hN)
    have heq : (T : Subgroup G) ⊓ (M ⊓ Subgroup.centralizer (V : Set G)) =
        (T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) :=
      le_antisymm (inf_le_inf_left _ inf_le_right)
        (le_inf inf_le_left (le_inf (inf_le_left.trans hTM) inf_le_right))
    rwa [heq] at h
  refine ⟨hel, hVn, le_inf hVT hVC, hTN, hfac, ?_⟩
  apply le_antisymm
  · refine (le_of_eq hV).trans (conjClosure_le fun m hm z hz => ?_)
    obtain ⟨n, hn, c, hc, rfl⟩ := hfac m hm
    have hzV : z ∈ V := by
      rw [hV]
      exact le_conjClosure Z' M hz
    have hcz : c * z = z * c := (Subgroup.mem_centralizer_iff.mp hc.2 z hzV).symm
    have : n * c * z * (n * c)⁻¹ = n * z * n⁻¹ := by
      calc n * c * z * (n * c)⁻¹ = n * (c * z) * c⁻¹ * n⁻¹ := by group
        _ = n * z * n⁻¹ := by rw [hcz]; group
    rw [this]
    exact mem_conjClosure hn hz
  · exact (conjClosure_mono le_rfl inf_le_left).trans (le_of_eq hV.symm)

theorem eq_pCoreOf_and_charTwo (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G)
    {M V : Subgroup G} (hM : InM (T : Subgroup G) M)
    (hV : CaseA (T : Subgroup G) M V ∨ CaseB (T : Subgroup G) M V) :
    pCoreOf 2 (M ⊓ Subgroup.normalizer
        (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) =
        (T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) ∧
      CharTwo (M ⊓ Subgroup.normalizer
        (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) := by
  obtain ⟨Z', hZ', hVZ'⟩ := exists_Z' hV
  obtain ⟨hel, hVn, hVR, hTN, hfac, hVN⟩ := facts hEven T hM hZ' hVZ'
  have hF : CharTwo M := hEven M hM.1.1 ⟨T, hM.2⟩
  have hRM : (T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) ≤ M := inf_le_left.trans hM.2
  have hR2 : IsPGroup 2 ((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :=
    T.isPGroup'.to_le inf_le_left
  have hFN := CT.CharTwo.inf_normalizer hF hRM hR2
  refine ⟨le_antisymm ?_ ?_, hFN⟩
  · have hred := isTwoReducedIn_conjClosure _ T hTN hFN hZ'
    rw [← hVN] at hred
    have hD : pCoreOf 2 (M ⊓ Subgroup.normalizer
        (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) ≤
        Subgroup.centralizer (V : Set G) := by
      refine hred.2.2.2 _ (pCoreOf_le 2 _) (le_normalizer_pCoreOf 2 _) fun d hd => ?_
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (M ⊓ Subgroup.normalizer
        (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) ⟨d, hd⟩
      refine ⟨k, ?_⟩
      have : d ^ 2 ^ k = 1 := congrArg Subtype.val hk
      rw [this]
      exact Subgroup.one_mem _
    exact le_inf (pCoreOf_two_le_sylow _ T hTN) hD
  · exact le_pCoreOf_of_le_normalizer 2 (le_inf hRM Subgroup.le_normalizer) inf_le_right hR2

theorem isTwoReducedIn_normalizer (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G)
    {M V : Subgroup G} (hM : InM (T : Subgroup G) M)
    (hV : CaseA (T : Subgroup G) M V ∨ CaseB (T : Subgroup G) M V) :
    IsTwoReducedIn (M ⊓ Subgroup.normalizer
      (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) V := by
  obtain ⟨Z', hZ', hVZ'⟩ := exists_Z' hV
  obtain ⟨hel, hVn, hVR, hTN, hfac, hVN⟩ := facts hEven T hM hZ' hVZ'
  have hF : CharTwo M := hEven M hM.1.1 ⟨T, hM.2⟩
  have hFN := CT.CharTwo.inf_normalizer hF (inf_le_left.trans hM.2)
    (T.isPGroup'.to_le (inf_le_left : (T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) ≤ T))
  have := isTwoReducedIn_conjClosure _ T hTN hFN hZ'
  rwa [← hVN] at this

theorem autOn_eq (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G)
    {M V : Subgroup G} (hM : InM (T : Subgroup G) M)
    (hV : CaseA (T : Subgroup G) M V ∨ CaseB (T : Subgroup G) M V) :
    autOn M V = autOn (M ⊓ Subgroup.normalizer
      (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) V := by
  obtain ⟨Z', hZ', hVZ'⟩ := exists_Z' hV
  obtain ⟨hel, hVn, hVR, hTN, hfac, hVN⟩ := facts hEven T hM hZ' hVZ'
  exact autOn_eq_of_factor inf_le_left hVn hfac

theorem isUniqueM (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G) {M V : Subgroup G}
    (hmax : IsOrdMaximalIn (T : Subgroup G) (InM (T : Subgroup G)) M)
    (hV : CaseA (T : Subgroup G) M V ∨ (V ≠ ⊥ ∧ CaseB (T : Subgroup G) M V)) :
    IsUniqueM (M ⊓ Subgroup.normalizer
      (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) M := by
  have hM : InM (T : Subgroup G) M := hmax.1
  have hV' : CaseA (T : Subgroup G) M V ∨ CaseB (T : Subgroup G) M V := hV.imp_right And.right
  obtain ⟨Z', hZ', hVZ'⟩ := exists_Z' hV'
  obtain ⟨hel, hVn, hVR, hTN, hfac, hVN⟩ := facts hEven T hM hZ' hVZ'
  have hVne : V ≠ ⊥ := by
    rcases hV with h | h
    · rw [h]
      exact VZ_ne_bot (quasithinOmegaOneCenter_ne_bot T.isPGroup'
        (ne_bot_of_inH T (inH_of_inM hM)))
    · exact h.1
  have hpc := (eq_pCoreOf_and_charTwo hEven T hM hV').1
  have hNH : InH (T : Subgroup G) (M ⊓ Subgroup.normalizer
      (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) := by
    refine ⟨hTN, ?_⟩
    rw [hpc]
    exact fun h => hVne (le_bot_iff.mp (hVR.trans h.le))
  rcases hV with h | ⟨-, hB⟩
  · refine isUniqueM_of_isOrdMaximalIn hmax hNH inf_le_left fun m hm => ?_
    obtain ⟨n, hn, c, hc, hmeq⟩ := hfac m hm
    exact ⟨n, hn, c, by rw [← h]; exact hc, hmeq⟩
  · refine ⟨⟨hM.1, inf_le_left⟩, fun M₁ hM₁ => ?_⟩
    have hM₁T : InM (T : Subgroup G) M₁ := ⟨hM₁.1, hTN.trans hM₁.2⟩
    obtain ⟨K, hK, hle⟩ := exists_isOrdMaximalIn_ge (T := (T : Subgroup G))
      (𝓕 := InM (T : Subgroup G)) (fun _ hK => isHv_of_inM hEven T hK) hM₁T
    have hKM : K = M := hB.2 K hK
    rw [hKM] at hle
    have hZ'V : Z' ≤ V := by
      rw [hVZ']
      exact le_conjClosure Z' M
    have hgen : V = conjClosure (V ⊓ quasithinOmegaOneCenter (T : Subgroup G)) (M₁ ⊓ M) := by
      apply le_antisymm
      · exact (le_of_eq hVN).trans
          (conjClosure_mono (le_inf hZ'V hZ') (le_inf hM₁.2 inf_le_left))
      · refine conjClosure_le fun g hg z hz => ?_
        exact (Subgroup.mem_normalizer_iff.mp (hVn hg.2) z).mp hz.1
    have hM₁M : M₁ ≤ M := le_of_ordLE_of_normal hM.1 hle hVne
      (isPGroup_of_isElemAbelian hel) hVn hgen
    exact (hM₁.1.2 M hM.1.1 hM₁M).symm

theorem main (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G) {M V : Subgroup G}
    (hmax : IsOrdMaximalIn (T : Subgroup G) (InM (T : Subgroup G)) M)
    (hV : CaseA (T : Subgroup G) M V ∨ (V ≠ ⊥ ∧ CaseB (T : Subgroup G) M V)) :
    (pCoreOf 2 (M ⊓ Subgroup.normalizer
        (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) =
        (T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) ∧
      CharTwo (M ⊓ Subgroup.normalizer
        (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))) ∧
    IsTwoReducedIn (M ⊓ Subgroup.normalizer
      (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) V ∧
    autOn M V = autOn (M ⊓ Subgroup.normalizer
      (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) V ∧
    IsUniqueM (M ⊓ Subgroup.normalizer
      (((T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) M := by
  have hV' : CaseA (T : Subgroup G) M V ∨ CaseB (T : Subgroup G) M V := hV.imp_right And.right
  exact ⟨eq_pCoreOf_and_charTwo hEven T hmax.1 hV', isTwoReducedIn_normalizer hEven T hmax.1 hV',
    autOn_eq hEven T hmax.1 hV', isUniqueM hEven T hmax hV⟩

end A57

@[expose] def VFamily (T : Subgroup G) : Set (Subgroup G) :=
  {W | ∃ H : Subgroup G, InH T H ∧ W = VZ T H}

omit [Finite G] in
theorem VZ_mem_VFamily {T H : Subgroup G} (hH : InH T H) : VZ T H ∈ VFamily T := ⟨H, hH, rfl⟩

omit [Finite G] in
theorem VZ_eq_of_ordLE_of_ordLE {T H K : Subgroup G} (h₁ : OrdLE T H K) (h₂ : OrdLE T K H) :
    VZ T H = VZ T K :=
  le_antisymm (VZ_le_of_ordLE h₁) (VZ_le_of_ordLE h₂)

namespace A510

omit [Finite G] in
theorem le_normalizer_of_le {T H K : Subgroup G} (hK : InH T K)
    (hmax : Maximal (· ∈ VFamily T) (VZ T H)) (h : VZ T H ≤ VZ T K) :
    K ≤ Subgroup.normalizer (VZ T H : Set G) := by
  have heq : VZ T K = VZ T H := le_antisymm (hmax.2 (VZ_mem_VFamily hK) h) h
  rw [← heq]
  exact le_normalizer_conjClosure _ _

omit [Finite G] in
theorem le_normalizer_of_ordLE {T H K : Subgroup G} (hK : InH T K)
    (hmax : Maximal (· ∈ VFamily T) (VZ T H)) (h : OrdLE T H K) :
    K ≤ Subgroup.normalizer (VZ T H : Set G) :=
  le_normalizer_of_le hK hmax (VZ_le_of_ordLE h)

theorem isUniqueM_normalizer (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G)
    {H : Subgroup G} (hH : InH (T : Subgroup G) H)
    (hmax : Maximal (· ∈ VFamily (T : Subgroup G)) (VZ (T : Subgroup G) H)) :
    IsUniqueM H (Subgroup.normalizer (VZ (T : Subgroup G) H : Set G)) := by
  have hF : CharTwo H := charTwo_of_inH hEven T hH
  obtain ⟨-, hel⟩ := conjClosure_le_centerOf_pCoreOf H T hH.1 hF le_rfl
  have hVne : VZ (T : Subgroup G) H ≠ ⊥ :=
    VZ_ne_bot (quasithinOmegaOneCenter_ne_bot T.isPGroup' (ne_bot_of_inH T hH))
  have hloc : IsTwoLocal (Subgroup.normalizer (VZ (T : Subgroup G) H : Set G)) :=
    ⟨_, hVne, isPGroup_of_isElemAbelian hel, rfl⟩
  have huniq : ∀ M₂ : Subgroup G, InM H M₂ →
      M₂ = Subgroup.normalizer (VZ (T : Subgroup G) H : Set G) := by
    intro M₂ hM₂
    have hM₂H : InH (T : Subgroup G) M₂ :=
      ⟨hH.1.trans hM₂.2, pCoreOf_ne_bot_of_isTwoLocal hM₂.1.1⟩
    have hle : M₂ ≤ Subgroup.normalizer (VZ (T : Subgroup G) H : Set G) :=
      le_normalizer_of_ordLE hM₂H hmax (ordLE_of_le hM₂.2)
    exact (hM₂.1.2 _ hloc hle).symm
  obtain ⟨M₂, hM₂⟩ := exists_inM_of_pCoreOf_ne_bot hH.2
  have hN : Subgroup.normalizer (VZ (T : Subgroup G) H : Set G) = M₂ := (huniq M₂ hM₂).symm
  refine ⟨⟨?_, ?_⟩, huniq⟩
  · rw [hN]
    exact hM₂.1
  · rw [hN]
    exact hM₂.2

theorem isOrdMaximalIn_normalizer (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G)
    {H : Subgroup G} (hH : InH (T : Subgroup G) H)
    (hmax : Maximal (· ∈ VFamily (T : Subgroup G)) (VZ (T : Subgroup G) H)) :
    IsOrdMaximalIn (T : Subgroup G) (InM (T : Subgroup G))
      (Subgroup.normalizer (VZ (T : Subgroup G) H : Set G)) := by
  have h3 := isUniqueM_normalizer hEven T hH hmax
  have hNM : InM (T : Subgroup G) (Subgroup.normalizer (VZ (T : Subgroup G) H : Set G)) :=
    ⟨h3.1.1, hH.1.trans h3.1.2⟩
  have hNH := inH_of_inM hNM
  have hHN : OrdLE (T : Subgroup G) H (Subgroup.normalizer (VZ (T : Subgroup G) H : Set G)) :=
    ordLE_of_le h3.1.2
  have hVV : VZ (T : Subgroup G) (Subgroup.normalizer (VZ (T : Subgroup G) H : Set G)) =
      VZ (T : Subgroup G) H :=
    le_antisymm (hmax.2 (VZ_mem_VFamily hNH) (VZ_le_of_ordLE hHN)) (VZ_le_of_ordLE hHN)
  have hmaxN : Maximal (· ∈ VFamily (T : Subgroup G))
      (VZ (T : Subgroup G) (Subgroup.normalizer (VZ (T : Subgroup G) H : Set G))) := by
    rw [hVV]
    exact hmax
  refine ⟨hNM, fun M hM hle => ?_⟩
  have hMN : M ≤ Subgroup.normalizer
      (VZ (T : Subgroup G) (Subgroup.normalizer (VZ (T : Subgroup G) H : Set G)) : Set G) :=
    le_normalizer_of_ordLE (inH_of_inM hM) hmaxN hle
  rw [hVV] at hMN
  exact (hM.1.2 _ h3.1.1.1 hMN).symm

end A510

end FiniteSection

end CFSG.Quasithin

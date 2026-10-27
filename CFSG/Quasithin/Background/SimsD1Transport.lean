module

public import CFSG.Quasithin.Background.SimsD1Embed
public import CFSG.Quasithin.Background.SimsD1TransGrp
public import CFSG.Quasithin.Background.SimsD1TransMod

public section

namespace CFSG.Quasithin.SimsD1.Transport

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] noncomputable def qSub {G : Type} [Group G] (H V : Subgroup G) (hH : Finite H)
    (hVH : V ≤ H) (hE : IsElemAbelian 2 V) : WithTop ℚ :=
  haveI : Finite V := haveI := hH; Finite.of_injective (Subgroup.inclusion hVH)
    (Subgroup.inclusion_injective hVH)
  @qOf ↥V (commGroupOfElemAbelian hE) this (autOn H V)

theorem commutator_le_of_le {G : Type} [Group G] {H X Y : Subgroup G} (hX : X ≤ H)
    (hY : Y ≤ H) : ⁅X, Y⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem (hX hx) (hY hy)) (H.inv_mem (hX hx))) (H.inv_mem (hY hy))

theorem conjClosure_le_of_le {G : Type} [Group G] {H V K : Subgroup G} (hV : V ≤ H)
    (hK : K ≤ H) : conjClosure V K ≤ H :=
  conjClosure_le fun _ hg _ hv => H.mul_mem (H.mul_mem (hK hg) (hV hv)) (H.inv_mem (hK hg))

section Img

variable {G F : Type} [Group G] [Group F] {H : Subgroup G}

@[expose] def img (ι : ↥H →* F) (X : Subgroup G) : Subgroup F := (X.subgroupOf H).map ι

theorem exists_map_subtype {X : Subgroup G} (hX : X ≤ H) :
    ∃ Y : Subgroup ↥H, Y.map H.subtype = X :=
  ⟨X.subgroupOf H, Subgroup.map_subgroupOf_eq_of_le hX⟩

theorem img_map_subtype (ι : ↥H →* F) (Y : Subgroup ↥H) : img ι (Y.map H.subtype) = Y.map ι :=
  congrArg (Subgroup.map ι) (Subgroup.comap_map_eq_self_of_injective H.subtype_injective Y)

variable {ι : ↥H →* F}

theorem img_le_img_iff (hι : Function.Injective ι) {X Y : Subgroup G} (hX : X ≤ H) :
    img ι X ≤ img ι Y ↔ X ≤ Y := by
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  rw [img_map_subtype, img, Subgroup.map_le_map_iff_of_injective hι,
    Subgroup.map_le_iff_le_comap]
  rfl

theorem img_mono {X Y : Subgroup G} (h : X ≤ Y) : img ι X ≤ img ι Y :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem img_inj (hι : Function.Injective ι) {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    img ι X = img ι Y ↔ X = Y := by
  refine ⟨fun h => le_antisymm ((img_le_img_iff hι hX).1 h.le) ((img_le_img_iff hι hY).1 h.ge),
    fun h => h ▸ rfl⟩

theorem img_bot : img ι (⊥ : Subgroup G) = ⊥ := by
  rw [img, Subgroup.bot_subgroupOf, Subgroup.map_bot]

theorem img_eq_bot_iff (hι : Function.Injective ι) {X : Subgroup G} (hX : X ≤ H) :
    img ι X = ⊥ ↔ X = ⊥ := by
  rw [← img_bot (ι := ι), img_inj hι hX bot_le]

theorem img_inf (hι : Function.Injective ι) (X Y : Subgroup G) :
    img ι (X ⊓ Y) = img ι X ⊓ img ι Y :=
  (congrArg (Subgroup.map ι) (Subgroup.comap_inf X Y H.subtype)).trans
    (Subgroup.map_inf_eq _ _ ι hι)

theorem img_sup {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    img ι (X ⊔ Y) = img ι X ⊔ img ι Y := by
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  obtain ⟨Y, rfl⟩ := exists_map_subtype hY
  rw [← Subgroup.map_sup]
  simp only [img_map_subtype]
  exact Subgroup.map_sup X Y ι

theorem img_commutator {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    img ι ⁅X, Y⁆ = ⁅img ι X, img ι Y⁆ := by
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  obtain ⟨Y, rfl⟩ := exists_map_subtype hY
  rw [← Subgroup.map_commutator]
  simp only [img_map_subtype]
  exact Subgroup.map_commutator X Y ι

theorem img_pCoreOf (hι : Function.Injective ι) (p : ℕ) {X : Subgroup G} (hX : X ≤ H) :
    img ι (pCoreOf p X) = pCoreOf p (img ι X) := by
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  rw [TransGrp.pCoreOf_map_eq _ H.subtype_injective, img_map_subtype, img_map_subtype,
    TransGrp.pCoreOf_map_eq _ hι]

theorem img_thompsonJ (hι : Function.Injective ι) {X : Subgroup G} (hX : X ≤ H) :
    img ι (thompsonJ X) = thompsonJ (img ι X) := by
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  rw [TransGrp.thompsonJ_map_eq _ H.subtype_injective, img_map_subtype, img_map_subtype,
    TransGrp.thompsonJ_map_eq _ hι]

theorem img_centerOf (hι : Function.Injective ι) {X : Subgroup G} (hX : X ≤ H) :
    img ι (centerOf X) = centerOf (img ι X) := by
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  rw [TransGrp.centerOf_map_eq _ H.subtype_injective, img_map_subtype, img_map_subtype,
    TransGrp.centerOf_map_eq _ hι]

theorem img_twoResidual (hι : Function.Injective ι) {X : Subgroup G} (hX : X ≤ H) :
    img ι (twoResidual X) = twoResidual (img ι X) := by
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  rw [TransGrp.twoResidual_map_eq _ H.subtype_injective, img_map_subtype, img_map_subtype,
    TransGrp.twoResidual_map_eq _ hι]

theorem img_twoPrimeResidual (hι : Function.Injective ι) {X : Subgroup G} (hX : X ≤ H) :
    img ι (twoPrimeResidual X) = twoPrimeResidual (img ι X) := by
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  rw [TransGrp.twoPrimeResidual_map_eq _ H.subtype_injective, img_map_subtype, img_map_subtype,
    TransGrp.twoPrimeResidual_map_eq _ hι]

theorem img_conjClosure {V K : Subgroup G} (hV : V ≤ H) (hK : K ≤ H) :
    img ι (conjClosure V K) = conjClosure (img ι V) (img ι K) := by
  obtain ⟨V, rfl⟩ := exists_map_subtype hV
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  rw [TransGrp.conjClosure_map_eq]
  simp only [img_map_subtype]
  exact (TransGrp.conjClosure_map_eq ι V K).symm

theorem img_inf_centralizer (hι : Function.Injective ι) {K X : Subgroup G} (hK : K ≤ H)
    (hX : X ≤ H) :
    img ι (K ⊓ Subgroup.centralizer (X : Set G)) =
      img ι K ⊓ Subgroup.centralizer ((img ι X : Subgroup F) : Set F) := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  rw [← TransGrp.map_inf_centralizer_eq _ H.subtype_injective]
  simp only [img_map_subtype]
  exact TransGrp.map_inf_centralizer_eq _ hι K X

theorem le_normalizer_img_iff (hι : Function.Injective ι) {K X : Subgroup G} (hK : K ≤ H)
    (hX : X ≤ H) :
    img ι K ≤ Subgroup.normalizer ((img ι X : Subgroup F) : Set F) ↔
      K ≤ Subgroup.normalizer (X : Set G) := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  rw [img_map_subtype, img_map_subtype, TransGrp.le_normalizer_map_iff _ hι,
    TransGrp.le_normalizer_map_iff _ H.subtype_injective]

theorem le_centralizer_img_iff (hι : Function.Injective ι) {K X : Subgroup G} (hK : K ≤ H)
    (hX : X ≤ H) :
    img ι K ≤ Subgroup.centralizer ((img ι X : Subgroup F) : Set F) ↔
      K ≤ Subgroup.centralizer (X : Set G) := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  rw [img_map_subtype, img_map_subtype, TransGrp.le_centralizer_map_iff _ hι,
    TransGrp.le_centralizer_map_iff _ H.subtype_injective]

theorem normal_img_iff (hι : Function.Injective ι) {X K : Subgroup G} (hXK : X ≤ K)
    (hK : K ≤ H) :
    ((img ι X).subgroupOf (img ι K)).Normal ↔ (X.subgroupOf K).Normal := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨X, rfl⟩ := exists_map_subtype (hXK.trans hK)
  have hXK' : X ≤ K := (Subgroup.map_le_map_iff_of_injective H.subtype_injective).1 hXK
  rw [img_map_subtype, img_map_subtype, TransGrp.normal_subgroupOf_map_iff _ hι hXK',
    TransGrp.normal_subgroupOf_map_iff _ H.subtype_injective hXK']

theorem isElemAbelian_img_iff (hι : Function.Injective ι) {X : Subgroup G} (hX : X ≤ H)
    (p : ℕ) : IsElemAbelian p (img ι X) ↔ IsElemAbelian p X := by
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  rw [img_map_subtype, TransGrp.isElemAbelian_map_iff _ hι,
    TransGrp.isElemAbelian_map_iff _ H.subtype_injective]

theorem isMaxElemAbelian_img_iff (hι : Function.Injective ι) {K C : Subgroup G} (hK : K ≤ H)
    (hC : C ≤ H) : IsMaxElemAbelian (img ι K) (img ι C) ↔ IsMaxElemAbelian K C := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨C, rfl⟩ := exists_map_subtype hC
  rw [img_map_subtype, img_map_subtype, TransGrp.isMaxElemAbelian_map_iff _ hι,
    TransGrp.isMaxElemAbelian_map_iff _ H.subtype_injective]

theorem isSylowTwoOf_img_iff (hι : Function.Injective ι) {S K : Subgroup G} (hS : S ≤ H)
    (hK : K ≤ H) : IsSylowTwoOf (img ι S) (img ι K) ↔ IsSylowTwoOf S K := by
  obtain ⟨S, rfl⟩ := exists_map_subtype hS
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  rw [img_map_subtype, img_map_subtype, TransGrp.isSylowTwoOf_map_iff _ hι,
    TransGrp.isSylowTwoOf_map_iff _ H.subtype_injective]

theorem isUniqueMaxOver_img_iff (hι : Function.Injective ι) {K T M : Subgroup G} (hK : K ≤ H)
    (hT : T ≤ H) (hM : M ≤ H) :
    IsUniqueMaxOver (img ι K) (img ι T) (img ι M) ↔ IsUniqueMaxOver K T M := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨T, rfl⟩ := exists_map_subtype hT
  obtain ⟨M, rfl⟩ := exists_map_subtype hM
  simp only [img_map_subtype]
  rw [TransGrp.isUniqueMaxOver_map_iff _ hι,
    TransGrp.isUniqueMaxOver_map_iff _ H.subtype_injective]

theorem isMinParabolicOf_img_iff (hι : Function.Injective ι) {K P : Subgroup G} (hK : K ≤ H)
    (hP : P ≤ H) : IsMinParabolicOf (img ι K) (img ι P) ↔ IsMinParabolicOf K P := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨P, rfl⟩ := exists_map_subtype hP
  rw [img_map_subtype, img_map_subtype, TransGrp.isMinParabolicOf_map_iff _ hι,
    TransGrp.isMinParabolicOf_map_iff _ H.subtype_injective]

theorem isChiefStep_img_iff (hι : Function.Injective ι) {K U L N : Subgroup G} (hK : K ≤ H)
    (hU : U ≤ H) (hL : L ≤ H) (hN : N ≤ H) :
    IsChiefStep (img ι K) (img ι U) (img ι L) (img ι N) ↔ IsChiefStep K U L N := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨U, rfl⟩ := exists_map_subtype hU
  obtain ⟨L, rfl⟩ := exists_map_subtype hL
  obtain ⟨N, rfl⟩ := exists_map_subtype hN
  simp only [img_map_subtype]
  rw [TransGrp.isChiefStep_map_iff _ hι,
    TransGrp.isChiefStep_map_iff _ H.subtype_injective]

theorem isCentralStep_img_iff (hι : Function.Injective ι) {K L N : Subgroup G} (hK : K ≤ H)
    (hL : L ≤ H) (hN : N ≤ H) :
    IsCentralStep (img ι K) (img ι L) (img ι N) ↔ IsCentralStep K L N := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨L, rfl⟩ := exists_map_subtype hL
  obtain ⟨N, rfl⟩ := exists_map_subtype hN
  simp only [img_map_subtype]
  rw [TransGrp.isCentralStep_map_iff _ hι,
    TransGrp.isCentralStep_map_iff _ H.subtype_injective]

theorem isChiefSeriesFrom_img_iff (hι : Function.Injective ι) {K U N : Subgroup G} (hK : K ≤ H)
    (hU : U ≤ H) (hN : N ≤ H) (c : ℕ) :
    IsChiefSeriesFrom (img ι K) (img ι U) (img ι N) c ↔ IsChiefSeriesFrom K U N c := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨U, rfl⟩ := exists_map_subtype hU
  obtain ⟨N, rfl⟩ := exists_map_subtype hN
  simp only [img_map_subtype]
  rw [TransGrp.isChiefSeriesFrom_map_iff _ hι,
    TransGrp.isChiefSeriesFrom_map_iff _ H.subtype_injective]

theorem relIndex_img (hι : Function.Injective ι) {K L : Subgroup G} (hK : K ≤ H) (hL : L ≤ H) :
    (img ι K).relIndex (img ι L) = K.relIndex L := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨L, rfl⟩ := exists_map_subtype hL
  rw [img_map_subtype, img_map_subtype, TransGrp.relIndex_map_eq _ hι,
    TransGrp.relIndex_map_eq _ H.subtype_injective]

theorem isTwoReducedIn_img_iff (hι : Function.Injective ι) {K V : Subgroup G} (hK : K ≤ H)
    (hV : V ≤ H) : IsTwoReducedIn (img ι K) (img ι V) ↔ IsTwoReducedIn K V := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨V, rfl⟩ := exists_map_subtype hV
  rw [img_map_subtype, img_map_subtype, TransMod.isTwoReducedIn_map _ hι,
    TransMod.isTwoReducedIn_map _ H.subtype_injective]

theorem isFFInt_img_iff (hι : Function.Injective ι) {K V : Subgroup G} (hK : K ≤ H)
    (hV : V ≤ H) (hE : IsElemAbelian 2 V) (hE' : IsElemAbelian 2 (img ι V)) :
    IsFFInt (img ι K) (img ι V) hE' ↔ IsFFInt K V hE := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨V, rfl⟩ := exists_map_subtype hV
  have hEV : IsElemAbelian 2 V := (TransGrp.isElemAbelian_map_iff _ H.subtype_injective 2 V).1 hE
  exact (TransMod.isFFInt_of_map_eq ι hι (img_map_subtype ι K).symm (img_map_subtype ι V).symm
    hEV hE').trans (TransMod.isFFInt_map H.subtype H.subtype_injective hEV hE).symm

theorem isDualFFInt_img_iff (hι : Function.Injective ι) {K V : Subgroup G} (hK : K ≤ H)
    (hV : V ≤ H) (hE : IsElemAbelian 2 V) (hE' : IsElemAbelian 2 (img ι V)) :
    IsDualFFInt (img ι K) (img ι V) hE' ↔ IsDualFFInt K V hE := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨V, rfl⟩ := exists_map_subtype hV
  have hEV : IsElemAbelian 2 V := (TransGrp.isElemAbelian_map_iff _ H.subtype_injective 2 V).1 hE
  exact (TransMod.isDualFFInt_of_map_eq ι hι (img_map_subtype ι K).symm
    (img_map_subtype ι V).symm hEV hE').trans
    (TransMod.isDualFFInt_map H.subtype H.subtype_injective hEV hE).symm

theorem qInt_img [Finite F] [Finite H] (hι : Function.Injective ι) {K V : Subgroup G}
    (hK : K ≤ H) (hVK : V ≤ K) (hfin : Finite K) (hE : IsElemAbelian 2 V)
    (hE' : IsElemAbelian 2 (img ι V)) :
    qInt (img ι K) (img ι V) hE' = qSub K V hfin hVK hE := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  obtain ⟨V, rfl⟩ := exists_map_subtype (hVK.trans hK)
  have hEV : IsElemAbelian 2 V := (TransGrp.isElemAbelian_map_iff _ H.subtype_injective 2 V).1 hE
  haveI : Finite ↥(V.map H.subtype) :=
    (TransMod.finite_map_iff H.subtype H.subtype_injective).2 inferInstance
  exact (TransMod.qOf_autOn_of_map_eq ι hι (img_map_subtype ι K).symm (img_map_subtype ι V).symm
    hEV hE').trans (TransMod.qOf_autOn_map H.subtype H.subtype_injective hEV hE).symm

theorem isSQTKCat_img_iff (hι : Function.Injective ι) {K : Subgroup G} (hK : K ≤ H) :
    CFSG.SectionRank.IsSQTKCat ↥(img ι K) ↔ CFSG.SectionRank.IsSQTKCat ↥K := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  rw [img_map_subtype, TransGrp.isSQTKCat_map_iff _ hι,
    TransGrp.isSQTKCat_map_iff _ H.subtype_injective]

theorem isSolvable_img_iff (hι : Function.Injective ι) {K : Subgroup G} (hK : K ≤ H) :
    Group.IsSolvable ↥(img ι K) ↔ Group.IsSolvable ↥K := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  rw [img_map_subtype, TransGrp.isSolvable_map_iff _ hι,
    TransGrp.isSolvable_map_iff _ H.subtype_injective]

theorem charTwo_img_iff (hι : Function.Injective ι) {K : Subgroup G} (hK : K ≤ H) :
    CharTwo (img ι K) ↔ CharTwo K := by
  obtain ⟨K, rfl⟩ := exists_map_subtype hK
  rw [img_map_subtype, TransGrp.charTwo_map_iff _ hι,
    TransGrp.charTwo_map_iff _ H.subtype_injective]

theorem comm_img_iff (hι : Function.Injective ι) {X : Subgroup G} (hX : X ≤ H) :
    (∀ x ∈ img ι X, ∀ y ∈ img ι X, x * y = y * x) ↔ ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  rw [img_map_subtype]
  constructor
  · rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hxy := h (ι x) ⟨x, hx, rfl⟩ (ι y) ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul] at hxy
    rw [← map_mul, ← map_mul, hι hxy]
  · rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hxy := h (H.subtype x) ⟨x, hx, rfl⟩ (H.subtype y) ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul] at hxy
    rw [← map_mul, ← map_mul, H.subtype_injective hxy]

theorem exists_img_of_le (hι : Function.Injective ι) {X : Subgroup G} {N : Subgroup F}
    (hX : X ≤ H) (hN : N ≤ img ι X) : ∃ K : Subgroup G, K ≤ X ∧ img ι K = N := by
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  rw [img_map_subtype] at hN
  refine ⟨(N.comap ι).map H.subtype, Subgroup.map_mono (TransGrp.comap_le_of_le_map ι hι hN), ?_⟩
  rw [img_map_subtype]
  exact TransGrp.map_comap_of_le_map ι hN

theorem img_conj {X : Subgroup G} (hX : X ≤ H) (g : ↥H) :
    img ι (X.map (MulAut.conj (g : G)⁻¹).toMonoidHom) =
      (img ι X).map (MulAut.conj (ι g)⁻¹).toMonoidHom := by
  obtain ⟨X, rfl⟩ := exists_map_subtype hX
  have h1 : (X.map H.subtype).map (MulAut.conj (g : G)⁻¹).toMonoidHom =
      (X.map (MulAut.conj g⁻¹).toMonoidHom).map H.subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [h1, img_map_subtype, img_map_subtype, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

end Img

section Emb

variable {G : Type} [Group G]

structure Emb (G₁ G₂ T : Subgroup G) (F : Type) [Group F] where
  ι₁ : ↥G₁ →* F
  ι₂ : ↥G₂ →* F
  inj₁ : Function.Injective ι₁
  inj₂ : Function.Injective ι₂
  le₁ : T ≤ G₁
  le₂ : T ≤ G₂
  agree : ∀ (t : G) (ht : t ∈ T), ι₁ ⟨t, le₁ ht⟩ = ι₂ ⟨t, le₂ ht⟩

variable {G₁ G₂ T V M₂ : Subgroup G} {F : Type} [Group F]

theorem Emb.img_eq (e : Emb G₁ G₂ T F) {X : Subgroup G} (hX : X ≤ T) :
    img e.ι₁ X = img e.ι₂ X :=
  Embed.map_subgroupOf_eq e.le₁ e.le₂ e.agree hX

theorem exists_emb [Finite G₁] [Finite G₂] (h₁ : T ≤ G₁) (h₂ : T ≤ G₂) :
    ∃ (F : Type) (_ : Group F) (_ : Finite F), Nonempty (Emb G₁ G₂ T F) := by
  obtain ⟨F, _, _, ι₁, ι₂, i₁, i₂, hag⟩ := Embed.exists_finite_embedding h₁ h₂
  exact ⟨F, _, ‹_›, ⟨⟨ι₁, ι₂, i₁, i₂, h₁, h₂, hag⟩⟩⟩

theorem le_of_isUniqueMaxOver {H M : Subgroup G} (h : IsUniqueMaxOver H T M) : M ≤ H :=
  (show M ∈ maxOver H T from h ▸ Set.mem_singleton M).1.1.le

theorem d11Hyp_img (e : Emb G₁ G₂ T F) (h : D11Hyp G₁ G₂ T V M₂) :
    D11Hyp (img e.ι₁ G₁) (img e.ι₂ G₂) (img e.ι₁ T) (img e.ι₁ V) (img e.ι₂ M₂) := by
  have hV₁ : V ≤ G₁ := h.reduced.1
  have hM₂ : M₂ ≤ G₂ := le_of_isUniqueMaxOver h.unique_max
  have hR₁ : pCoreOf 2 G₁ ≤ G₁ := CFSG.LieType.BorelTits.pCoreOf_le 2 G₁
  have hRT : pCoreOf 2 G₁ ≤ T := h.centralizer ▸ inf_le_left
  refine ⟨(isSylowTwoOf_img_iff e.inj₁ e.le₁ le_rfl).2 h.sylow₁, ?_,
    (isTwoReducedIn_img_iff e.inj₁ le_rfl hV₁).2 h.reduced,
    fun h0 => h.nontrivial ((img_eq_bot_iff e.inj₁ hV₁).1 h0), ?_, ?_, ?_⟩
  · rw [e.img_eq le_rfl]
    exact (isSylowTwoOf_img_iff e.inj₂ e.le₂ le_rfl).2 h.sylow₂
  · rw [e.img_eq le_rfl]
    exact (isUniqueMaxOver_img_iff e.inj₂ le_rfl e.le₂ hM₂).2 h.unique_max
  · rw [← img_pCoreOf e.inj₁ 2 le_rfl, ← img_inf_centralizer e.inj₁ e.le₁ hV₁, h.centralizer]
  · intro N hN hnorm
    rw [← img_pCoreOf e.inj₁ 2 le_rfl] at hN
    obtain ⟨K, hKR, rfl⟩ := exists_img_of_le e.inj₁ hR₁ hN
    have hKT : K ≤ T := hKR.trans hRT
    have hK₁ : K ≤ G₁ := hKR.trans hR₁
    have hKs : img e.ι₁ K ≤ img e.ι₁ G₁ ⊔ img e.ι₂ G₂ :=
      (img_mono hK₁).trans le_sup_left
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKs, sup_le_iff] at hnorm
    obtain ⟨hn₁, hn₂⟩ := hnorm
    rw [le_normalizer_img_iff e.inj₁ le_rfl hK₁] at hn₁
    rw [e.img_eq hKT, le_normalizer_img_iff e.inj₂ le_rfl (hKT.trans e.le₂)] at hn₂
    have hK : K = ⊥ := h.no_normal K hKR
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hK₁.trans le_sup_left)).2 (sup_le hn₁ hn₂))
    rw [hK, img_bot]

end Emb

end CFSG.Quasithin.SimsD1.Transport

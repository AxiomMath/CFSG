module

public import CFSG.Quasithin.Vol2.Ch12Sec9Final1291
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma6
public import CFSG.Quasithin.Vol2.Ch3Sec1Aux
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Background.F9Tilde

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace L1295A

variable {G : Type} [Group G] [Finite G]

structure Am (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) (V₁ H₁ : Subgroup G) :
    Prop where
  h1222 : Stmt12_2_2
  h37 : A37ForSQTK
  h38 : A38ForSQTK
  h39 : A39ForSQTK
  cx : Cx1291 G T L V n
  v1 : IsTSub T V V₁ 1
  ab : IsMulCommutative ↥(u128 V V₁)
  hstar : IsHStar T (Subgroup.normalizer (L : Set G)) H₁
  nV₁ : H₁ ≤ Subgroup.normalizer (V₁ : Set G)
  nL₁ : H₁ ≤ Subgroup.normalizer (lOne L V₁ : Set G)
  comm : ⁅lOne L V₁, oTwoUpper H₁⁆ ≤ pCoreOf 2 (lOne L V₁)

variable {T L V : Subgroup G} {n : ℕ} {V₁ H₁ : Subgroup G}

omit [Finite G] in
theorem lOne_le_normalizer : lOne L V₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
  (oTwoUpper_le _).trans inf_le_right

namespace Am

variable (A : Am G T L V n V₁ H₁)
include A

theorem T_le : T ≤ H₁ := A.hstar.1.1

theorem le_normalizer : H₁ ⊔ lOne L V₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
  sup_le A.nV₁ lOne_le_normalizer

theorem nLOne : H₁ ⊔ lOne L V₁ ≤ Subgroup.normalizer (lOne L V₁ : Set G) :=
  sup_le A.nL₁ Subgroup.le_normalizer

theorem V_le_T : V ≤ T := (A.cx.hyp.hyp.le_and_normalizes A.h1222).1

theorem V₁_ne_bot : V₁ ≠ ⊥ := by
  intro hb
  have h1 := A.v1.2.1
  rw [hb, Subgroup.card_bot] at h1
  norm_num at h1

theorem isHz : IsHzOne T L V₁ (H₁ ⊔ lOne L V₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV₁H : V₁ ≤ H₁ ⊔ lOne L V₁ :=
    ((A.v1.1.trans A.V_le_T).trans A.T_le).trans le_sup_left
  have hV₁p : IsPGroup 2 V₁ := A.cx.hyp.hyp.sylow.1.to_le (A.v1.1.trans A.V_le_T)
  have hO : V₁ ≤ pCoreOf 2 (H₁ ⊔ lOne L V₁) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hV₁H A.le_normalizer hV₁p
  refine ⟨⟨sup_le le_sup_right (A.T_le.trans le_sup_left), fun hb => A.V₁_ne_bot ?_⟩,
    A.le_normalizer, fun hle => A.hstar.2.1 (le_sup_left.trans hle)⟩
  exact le_bot_iff.1 (hb ▸ hO)

theorem hF : HypF98 T V L V₁ V (H₁ ⊔ lOne L V₁) :=
  L1286.hypF98_of_abelian A.h1222 A.h37 A.h38 A.h39 A.cx.hyp A.v1 A.ab A.isHz

theorem centralizerMod_eq :
    centralizerMod V₁ (H₁ ⊔ lOne L V₁) (conjClosure V (H₁ ⊔ lOne L V₁)) =
      pCoreOf 2 (H₁ ⊔ lOne L V₁) :=
  lemma12_8_4_four A.h1222 A.h37 A.h38 A.h39 G T L V n A.cx.hyp V₁ _ A.v1 A.isHz

theorem pCoreOf_lOne_le : pCoreOf 2 (lOne L V₁) ≤ pCoreOf 2 (H₁ ⊔ lOne L V₁) :=
  LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_right)
    (A.nLOne.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    (LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem elemAb : IsElemAbelian 2 (tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))) :=
  A.hF.toHypF91.isElemAbelian_tilde

theorem secMk_mem_normalizer (x : ↥(H₁ ⊔ lOne L V₁)) :
    secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, A.le_normalizer x.2⟩ ∈
      Subgroup.normalizer
        ((tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)) :
          Subgroup (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) :
            Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) :=
  secMk_mem_normalizer_secImg (le_normalizer_conjClosure V _ x.2)

omit A in
@[expose] noncomputable def rho (A : Am G T L V n V₁ H₁) :
    ↥(H₁ ⊔ lOne L V₁) →* MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))) :=
  (conjAct _).comp
    (((secMk (Subgroup.normalizer (V₁ : Set G)) V₁).comp
      (Subgroup.inclusion A.le_normalizer)).codRestrict _ A.secMk_mem_normalizer)

theorem rho_apply (x : ↥(H₁ ⊔ lOne L V₁))
    (u : ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))) :
    ((A.rho x u : ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))) :
        SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) =
      secMk _ V₁ ⟨x, A.le_normalizer x.2⟩ * u *
        (secMk _ V₁ ⟨x, A.le_normalizer x.2⟩)⁻¹ :=
  conjAct_apply_coe' _ _ u

theorem uH_le : conjClosure V (H₁ ⊔ lOne L V₁) ≤ Subgroup.normalizer (V₁ : Set G) :=
  A.hF.toHypF91.conjClosure_Vp_le_pCoreOf.trans
    ((LieType.BorelTits.pCoreOf_le 2 _).trans A.le_normalizer)

omit A in
@[expose] def uMk (A : Am G T L V n V₁ H₁) {w : G} (hw : w ∈ conjClosure V (H₁ ⊔ lOne L V₁)) :
    ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))) :=
  ⟨secMk _ V₁ ⟨w, A.uH_le hw⟩, secMk_mem_secImg hw⟩

theorem exists_uMk (u : ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))) :
    ∃ w, ∃ hw : w ∈ conjClosure V (H₁ ⊔ lOne L V₁), A.uMk hw = u := by
  obtain ⟨⟨w, hwN⟩, hw, hwu⟩ := mem_secImg.1 u.2
  exact ⟨w, hw, Subtype.ext hwu⟩

theorem rho_uMk_eq_iff (x : ↥(H₁ ⊔ lOne L V₁)) {w : G}
    (hw : w ∈ conjClosure V (H₁ ⊔ lOne L V₁)) :
    A.rho x (A.uMk hw) = A.uMk hw ↔ (x : G) * w * (x : G)⁻¹ * w⁻¹ ∈ V₁ := by
  have key : A.rho x (A.uMk hw) = A.uMk hw ↔
      secMk _ V₁ ⟨x, A.le_normalizer x.2⟩ * secMk _ V₁ ⟨w, A.uH_le hw⟩ =
        secMk _ V₁ ⟨w, A.uH_le hw⟩ * secMk _ V₁ ⟨x, A.le_normalizer x.2⟩ := by
    rw [← Subtype.coe_inj, rho_apply]
    constructor
    · intro h
      simp only [uMk] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h
    · intro h
      simp only [uMk]
      rw [mul_inv_eq_iff_eq_mul]
      exact h
  rw [key]
  constructor
  · intro h
    exact commutator_mem_of_secMk_commute
      (x := (⟨(x : G), A.le_normalizer x.2⟩ : ↥(Subgroup.normalizer (V₁ : Set G))))
      (y := (⟨w, A.uH_le hw⟩ : ↥(Subgroup.normalizer (V₁ : Set G)))) h
  · intro h
    exact secMk_comm_of_commutator_mem
      (x := (⟨(x : G), A.le_normalizer x.2⟩ : ↥(Subgroup.normalizer (V₁ : Set G))))
      (y := (⟨w, A.uH_le hw⟩ : ↥(Subgroup.normalizer (V₁ : Set G)))) h

theorem rho_eq_one_iff (x : ↥(H₁ ⊔ lOne L V₁)) :
    A.rho x = 1 ↔ (x : G) ∈ pCoreOf 2 (H₁ ⊔ lOne L V₁) := by
  rw [← A.centralizerMod_eq]
  constructor
  · intro h
    refine ⟨x.2, A.le_normalizer x.2, fun w hw => ?_⟩
    rw [← A.rho_uMk_eq_iff x hw, h]
    rfl
  · rintro ⟨-, -, h⟩
    refine MulEquiv.ext fun u => ?_
    obtain ⟨w, hw, rfl⟩ := A.exists_uMk u
    exact (A.rho_uMk_eq_iff x hw).2 (h w hw)

theorem rho_comm {x y : ↥(H₁ ⊔ lOne L V₁)}
    (h : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 (H₁ ⊔ lOne L V₁)) :
    A.rho x * A.rho y = A.rho y * A.rho x := by
  have h1 : A.rho (x * y * x⁻¹ * y⁻¹) = 1 := (A.rho_eq_one_iff _).2 h
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc A.rho x * A.rho y = (A.rho x * A.rho y * (A.rho x)⁻¹ * (A.rho y)⁻¹) * A.rho y *
        A.rho x := by group
    _ = A.rho y * A.rho x := by rw [h1, one_mul]

theorem autOn_eq_map {X : Subgroup G} (hX : X ≤ H₁ ⊔ lOne L V₁) :
    autOn (tildeOf V₁ X) (tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁))) =
      (X.subgroupOf (H₁ ⊔ lOne L V₁)).map A.rho := by
  ext a
  rw [mem_autOn_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x', hx'X, hx's⟩ := mem_secImg.1 hs
    refine ⟨⟨x', hX hx'X⟩, hx'X, ?_⟩
    show conjAct _ _ = conjAct _ s
    congr 1
    exact Subtype.ext hx's
  · rintro ⟨x, hxX, rfl⟩
    exact ⟨⟨_, A.secMk_mem_normalizer x⟩, secMk_mem_secImg hxX, rfl⟩

omit A in
@[expose] noncomputable def Ls (A : Am G T L V n V₁ H₁) :
    Subgroup (MulAut ↥(tildeOf V₁ (conjClosure V (H₁ ⊔ lOne L V₁)))) :=
  ((lOne L V₁).subgroupOf (H₁ ⊔ lOne L V₁)).map A.rho

theorem rho_mem_cent_of_comm {x : ↥(H₁ ⊔ lOne L V₁)}
    (hx : ∀ l ∈ lOne L V₁, l * x * l⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 (lOne L V₁)) :
    A.rho x ∈ Subgroup.centralizer (A.Ls : Set _) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨l, hl, rfl⟩
  exact A.rho_comm (A.pCoreOf_lOne_le (hx l hl))

theorem rho_mem_sup (x : ↥(H₁ ⊔ lOne L V₁)) :
    A.rho x ∈ Subgroup.centralizer (A.Ls : Set _) ⊔ A.Ls := by
  have hn : n ≠ 3 := by rcases A.cx.n45 with h | h <;> omega
  set K := ((Subgroup.centralizer (A.Ls : Set _) ⊔ A.Ls).comap A.rho).map
    (H₁ ⊔ lOne L V₁).subtype with hK
  have hmem : ∀ y (hy : y ∈ H₁ ⊔ lOne L V₁),
      A.rho ⟨y, hy⟩ ∈ Subgroup.centralizer (A.Ls : Set _) ⊔ A.Ls → y ∈ K :=
    fun y hy h => ⟨⟨y, hy⟩, h, rfl⟩
  have hL : lOne L V₁ ≤ K := fun y hy =>
    hmem y (Subgroup.mem_sup_right hy)
      (Subgroup.mem_sup_right ⟨⟨y, Subgroup.mem_sup_right hy⟩, hy, rfl⟩)
  have hO : oTwoUpper H₁ ≤ K := by
    intro y hy
    have hyH : y ∈ H₁ ⊔ lOne L V₁ := Subgroup.mem_sup_left (oTwoUpper_le H₁ hy)
    refine hmem y hyH (Subgroup.mem_sup_left (A.rho_mem_cent_of_comm fun l hl => ?_))
    have := A.comm (Subgroup.commutator_mem_commutator hl hy)
    rwa [commutatorElement_def] at this
  have hT : T ≤ K := by
    intro t ht
    have htH : t ∈ H₁ ⊔ lOne L V₁ := Subgroup.mem_sup_left (A.T_le ht)
    obtain ⟨b, hb, hbt⟩ := lOne_inner A.h1222 A.cx.hyp hn A.v1 (A.cx.hyp.hyp.normalizes ht)
      ((A.cx.hyp.hyp.le_and_normalizes A.h1222).2 ht) (A.v1.2.2 ht)
    have hbH : b ∈ H₁ ⊔ lOne L V₁ := Subgroup.mem_sup_right hb
    have hcH : b⁻¹ * t ∈ H₁ ⊔ lOne L V₁ := Subgroup.mul_mem _ (Subgroup.inv_mem _ hbH) htH
    have hc : A.rho ⟨b⁻¹ * t, hcH⟩ ∈ Subgroup.centralizer (A.Ls : Set _) := by
      refine A.rho_mem_cent_of_comm fun l hl => ?_
      have h1 := Subgroup.inv_mem _ (hbt l hl)
      rwa [show ((b⁻¹ * t) * l * (b⁻¹ * t)⁻¹ * l⁻¹)⁻¹ = l * (b⁻¹ * t) * l⁻¹ * (b⁻¹ * t)⁻¹ by
        group] at h1
    refine hmem t htH ?_
    have e : (⟨t, htH⟩ : ↥(H₁ ⊔ lOne L V₁)) = ⟨b, hbH⟩ * ⟨b⁻¹ * t, hcH⟩ :=
      Subtype.ext (by simp)
    rw [e, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨⟨b, hbH⟩, hb, rfl⟩)
      (Subgroup.mem_sup_left hc)
  have hH₁ : H₁ ≤ K := by
    have hsyl : IsSylowTwoOf T H₁ := isSylowTwoOf_of_quasithinIsSylowTwo A.cx.hyp.hyp.sylow A.T_le
    rw [← sup_twoResidual_eq hsyl, F6.twoResidual_eq_oTwoUpper]
    exact sup_le hT hO
  obtain ⟨x', hx', hxx'⟩ := (sup_le hH₁ hL) x.2
  have : x' = x := Subtype.ext hxx'
  rw [← this]
  exact hx'

theorem rho_mem_cent_of_le {x : ↥(H₁ ⊔ lOne L V₁)}
    (hx : (x : G) ∈ pCoreOf 2 (lOne L V₁ ⊔ T)) :
    A.rho x ∈ Subgroup.centralizer (A.Ls : Set _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine A.rho_mem_cent_of_comm fun l hl => ?_
  set R := pCoreOf 2 (lOne L V₁ ⊔ T) with hR
  have hTL₁ : T ≤ Subgroup.normalizer (lOne L V₁ : Set G) :=
    le_normalizer_lOne A.cx.hyp.hyp.normalizes A.v1.2.2
  have hLT : lOne L V₁ ⊔ T ≤ Subgroup.normalizer (lOne L V₁ : Set G) :=
    sup_le Subgroup.le_normalizer hTL₁
  have hRn : lOne L V₁ ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hxN := hLT (LieType.BorelTits.pCoreOf_le 2 _ hx)
  have hmemL : l * x * l⁻¹ * (x : G)⁻¹ ∈ lOne L V₁ := by
    have h1 := (Subgroup.mem_normalizer_iff.1 hxN l⁻¹).1 (inv_mem hl)
    have := (lOne L V₁).mul_mem hl h1
    rwa [show l * ((x : G) * l⁻¹ * (x : G)⁻¹) = l * x * l⁻¹ * (x : G)⁻¹ by group] at this
  have hmemR : l * x * l⁻¹ * (x : G)⁻¹ ∈ R := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (hRn (Subgroup.mem_sup_left hl)) x).1 hx
    exact R.mul_mem h1 (R.inv_mem hx)
  have hLR : lOne L V₁ ⊓ R ≤ pCoreOf 2 (lOne L V₁) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      ((le_inf Subgroup.le_normalizer ((le_sup_left : lOne L V₁ ≤ lOne L V₁ ⊔ T).trans hRn)).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
      ((LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
  exact hLR ⟨hmemL, hmemR⟩

theorem pCoreOf_range_eq_bot : pCoreOf 2 A.rho.range = ⊥ := by
  have h4 := (lemma12_8_4_of_four A.h1222 (lemma12_8_4_four A.h1222 A.h37 A.h38 A.h39)) G T L V n
    A.cx.hyp V₁ _ A.v1 A.isHz
  have hred := h4.2.1.2
  have h1 := pCoreOf_autOn_eq_bot_of_isTwoReducedIn hred
  rw [A.autOn_eq_map le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h1
  exact h1

end Am

end L1295A

end CFSG.Quasithin.H13

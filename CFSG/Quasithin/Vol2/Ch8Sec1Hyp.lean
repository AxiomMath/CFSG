module

public import CFSG.Quasithin.Vol2.Ch8Sec1LH
public import CFSG.Quasithin.Vol2.Ch8Sec1C48
public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Quasithin.Vol2.Ch12Sec8OneCComp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Setting811

variable {T L V M : Subgroup G} (S : Setting811 T L V M) {N : ℕ} {x : IntMod V S.elem}

include S

noncomputable def rhoLH (x : IntMod V S.elem) : ↥(S.cLH x) →* ↥(S.cY x) :=
  (convHom S.elem (S.cLH x) (S.LH_le_normalizer x)).codRestrict (S.cY x) fun l => by
    rw [← S.autI_LH x, ← range_convHom S.elem (S.cLH x) (S.LH_le_normalizer x)]
    exact ⟨l, rfl⟩

theorem rhoLH_surjective (x : IntMod V S.elem) : Function.Surjective (S.rhoLH x) := by
  intro y
  have hy : (y : MulAut (IntMod V S.elem)) ∈ (convHom S.elem (S.cLH x) (S.LH_le_normalizer x)).range
    := by rw [range_convHom, S.autI_LH x]; exact y.2
  obtain ⟨l, hl⟩ := hy
  exact ⟨l, Subtype.ext hl⟩

theorem rhoLH_eq_one_iff (x : IntMod V S.elem) (l : ↥(S.cLH x)) :
    S.rhoLH x l = 1 ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [← convI_eq_one_iff S.elem ⟨l, S.LH_le_normalizer x l.2⟩]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem pCore_le_ker_rhoLH (hN : N = 20160 ∨ N = 443520) (hx : O2Data (autI S.elem L) x N) :
    CFSG.pCore 2 ↥(S.cLH x) ≤ (S.rhoLH x).ker := by
  intro p hp
  rw [MonoidHom.mem_ker, rhoLH_eq_one_iff]
  exact S.pCoreOf_LH_le hN hx ((mem_pCoreOf_iff' p).2 hp)

noncomputable def psiLH (hN : N = 20160 ∨ N = 443520) (hx : O2Data (autI S.elem L) x N) :
    ModO2 (S.cLH x) →* ↥(S.cY x) :=
  QuotientGroup.lift _ (S.rhoLH x) (S.pCore_le_ker_rhoLH hN hx)

theorem psiLH_surjective (hN : N = 20160 ∨ N = 443520) (hx : O2Data (autI S.elem L) x N) :
    Function.Surjective (S.psiLH hN hx) := by
  intro y
  obtain ⟨l, rfl⟩ := S.rhoLH_surjective x y
  exact ⟨QuotientGroup.mk l, rfl⟩

theorem pCoreOf_L_inf_le (x : IntMod V S.elem) :
    pCoreOf 2 L ⊓ S.cLH x ≤ pCoreOf 2 (S.cLH x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((pCoreOf_isPGroup 2 L).to_le inf_le_left)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := Subgroup.mem_normalizer_iff.1
    (le_normalizer_pCoreOf 2 L ((S.LH_le x) hg).1) y
  have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hg) y
  exact ⟨fun hy => ⟨h1.1 hy.1, h2.1 hy.2⟩, fun hy => ⟨h1.2 hy.1, h2.2 hy.2⟩⟩

theorem ker_psiLH_le_center (hN : N = 20160 ∨ N = 443520) (hx : O2Data (autI S.elem L) x N) :
    (S.psiLH hN hx).ker ≤ Subgroup.center (ModO2 (S.cLH x)) := by
  intro z hz
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
  have hkV : (k : G) ∈ Subgroup.centralizer (V : Set G) :=
    (S.rhoLH_eq_one_iff x k).1 hz
  rw [Subgroup.mem_center_iff]
  intro w
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective w
  have hc : ⁅(k : G), (l : G)⁆ ∈ pCoreOf 2 L :=
    S.commutator_mem_pCoreOf hN hx ⟨((S.LH_le x) k.2).1, hkV⟩ ((S.LH_le x) l.2).1
  have hc' : ⁅k, l⁆ ∈ CFSG.pCore 2 ↥(S.cLH x) := by
    rw [← mem_pCoreOf_iff']
    have e : ((⁅k, l⁆ : ↥(S.cLH x)) : G) = ⁅(k : G), (l : G)⁆ := by
      simp [commutatorElement_def]
    rw [e]
    exact S.pCoreOf_L_inf_le x ⟨hc, e ▸ (⁅k, l⁆ : ↥(S.cLH x)).2⟩
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥(S.cLH x)) ⁅k, l⁆ = 1 :=
    (QuotientGroup.eq_one_iff _).2 hc'
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem center_le_ker_psiLH (hN : N = 20160 ∨ N = 443520) (hx : O2Data (autI S.elem L) x N) :
    Subgroup.center (ModO2 (S.cLH x)) ≤ (S.psiLH hN hx).ker := by
  have : IsSimpleGroup ↥(S.cY x) := hx.1
  have hZ := center_eq_bot_of_card hN hx.2.1
  intro z hz
  rw [MonoidHom.mem_ker]
  have hzc : S.psiLH hN hx z ∈ Subgroup.center ↥(S.cY x) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := S.psiLH_surjective hN hx y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz w]
  rw [hZ, Subgroup.mem_bot] at hzc
  exact hzc

theorem isQuasisimple_LH (hN : N = 20160 ∨ N = 443520) (hx : O2Data (autI S.elem L) x N) :
    CFSG.IsQuasisimple (ModO2 (S.cLH x)) := by
  have : IsSimpleGroup ↥(S.cY x) := hx.1
  have hker : Subgroup.center (ModO2 (S.cLH x)) = (S.psiLH hN hx).ker :=
    le_antisymm (S.center_le_ker_psiLH hN hx) (S.ker_psiLH_le_center hN hx)
  let e := (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (S.psiLH_surjective hN hx))
  refine ⟨Group.isPerfect_def.2 (commutator_quotient_eq_top
    (commutator_coe_eq_top_of_perfect (perfectCore_perfect _)) _), e.isSimpleGroup, ?_⟩
  have hZ := center_eq_bot_of_card hN hx.2.1
  by_contra hc
  push Not at hc
  obtain ⟨y, hy⟩ := exists_ne (1 : ↥(S.cY x))
  apply hy
  have hyZ : y ∈ Subgroup.center ↥(S.cY x) := by
    rw [Subgroup.mem_center_iff]
    intro w
    have := hc (e.symm w) (e.symm y)
    have h2 := congrArg e this
    simpa using h2
  rw [hZ, Subgroup.mem_bot] at hyZ
  exact hyZ

theorem mem_cComp_LH (hN : N = 20160 ∨ N = 443520) (hx : O2Data (autI S.elem L) x N) :
    S.cLH x ∈ cComp (S.cH x ⊓ M) := by
  refine mem_cComp_of_quasisimple_quotient (fun Nn _ hp => ?_) (S.isQuasisimple_LH hN hx)
    (A3.subnormal_of_normal (S.LH_le_MH x) ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (S.LH_le_MH x)).2 (S.MH_le_normalizer_LH x)))
  have hc : commutator (↥(S.cLH x) ⧸ Nn) = ⊤ :=
    commutator_quotient_eq_top (commutator_coe_eq_top_of_perfect (perfectCore_perfect _)) _
  rw [eq_top_iff]
  intro g _
  have := eq_one_of_isPGroup_of_perfect hp hc (g : ↥(S.cLH x) ⧸ Nn)
  exact (QuotientGroup.eq_one_iff g).1 this

theorem centralizer_V_le_H
    (x : IntMod V S.elem) :
    Subgroup.centralizer (V : Set G) ≤ S.cH x :=
  Subgroup.centralizer_le (by rintro _ rfl; exact x.val_mem)

theorem Q_le_T : pCoreOf 2 (L ⊔ T) ≤ T := S.q_eq ▸ inf_le_left

theorem Q_le_centralizer : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) :=
  S.q_eq ▸ inf_le_right

theorem Q_le_MH
    (x : IntMod V S.elem) : pCoreOf 2 (L ⊔ T) ≤ S.cH x ⊓ M :=
  le_inf (S.Q_le_centralizer.trans (S.centralizer_V_le_H x)) (S.Q_le_T.trans S.T_le_M)

theorem MH_le_normalizer (hx1 : x ≠ 1) : S.cH x ⊓ M ≤ Subgroup.normalizer (V : Set G) := by
  intro g hg
  by_contra hgN
  have h := S.ti g hg.2 hgN
  have hxmem : x.val ∈ V ⊓ CFSG.conjugate V g := by
    refine ⟨x.val_mem, ?_⟩
    have hgx := Subgroup.mem_centralizer_iff.1 hg.1 x.val rfl
    refine ⟨x.val, x.val_mem, ?_⟩
    show g⁻¹ * x.val * g⁻¹⁻¹ = x.val
    calc g⁻¹ * x.val * g⁻¹⁻¹ = g⁻¹ * (x.val * g) := by group
      _ = g⁻¹ * (g * x.val) := by rw [hgx]
      _ = x.val := by group
  rw [h, Subgroup.mem_bot] at hxmem
  exact hx1 (IntMod.val_injective hxmem)

theorem pCoreOf_M_le_MH
    (x : IntMod V S.elem) : pCoreOf 2 M ≤ S.cH x ⊓ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Sylow 2 G := S.sylow.2.1.toSylow (by
    have h : ¬ 2 ∣ T.relIndex ⊤ := S.sylow.2.2
    rwa [Subgroup.relIndex_top_right] at h)
  have hT' : (T' : Subgroup G) = T := rfl
  have hOT : pCoreOf 2 M ≤ T := hT' ▸ pCoreOf_two_le_sylow M T' (hT' ▸ S.T_le_M)
  have hOQ : pCoreOf 2 M ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right)
      (S.LT_le.trans (le_normalizer_pCoreOf 2 M)) (pCoreOf_isPGroup 2 M)
  exact hOQ.trans (S.Q_le_MH x)

theorem conjClosure_LH (x : IntMod V S.elem) : conjClosure (S.cLH x) (S.cH x ⊓ M) = S.cLH x :=
  le_antisymm (conjClosure_le fun _ hh z hz =>
    (Subgroup.mem_normalizer_iff.1 (S.MH_le_normalizer_LH x hh) z).1 hz)
    (le_conjClosure _ _)

theorem le_centralizer_of_pGroup (hN : N = 20160 ∨ N = 443520) (hx : O2Data (autI S.elem L) x N)
    {P : Subgroup G} (hPN : P ≤ Subgroup.normalizer (V : Set G)) (hp : IsPGroup 2 P)
    (hle : autI S.elem P ≤ S.cY x) (hnorm : S.cLH x ≤ Subgroup.normalizer (P : Set G)) :
    P ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup ↥(S.cY x) := hx.1
  have hp' : IsPGroup 2 ↥(autI S.elem P) := hp.comap_subtype.map _
  have hnormal : ((autI S.elem P).subgroupOf (S.cY x)).Normal := by
    refine ⟨fun φ hφ y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hφ ⊢
    have hy : (y : MulAut (IntMod V S.elem)) ∈ autI S.elem (S.cLH x) := by
      rw [S.autI_LH x]; exact y.2
    obtain ⟨l, hl, hly⟩ := (mem_autI S.elem).1 hy
    obtain ⟨q, hq, hqφ⟩ := (mem_autI S.elem).1 hφ
    have hlq : (l : G) * q * (l : G)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.1 (hnorm hl) q).1 hq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hly, ← hqφ, ← map_mul, ← map_inv, ← map_mul]
    exact (mem_autI S.elem).2 ⟨l * q * l⁻¹, by simpa using hlq, rfl⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((autI S.elem P).subgroupOf (S.cY x)) with
    h | h
  · have hbot : autI S.elem P = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot] at h
      exact eq_bot_iff.2 fun φ hφ => (Subgroup.disjoint_def.1 h) hφ (hle hφ)
    exact (autI_eq_bot_iff S.elem hPN).1 hbot
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at h
    exact not_isPGroup_two_of_card hN hx.2.1 (hp'.to_le h)

theorem V_le_center (hN : N = 20160 ∨ N = 443520) (hx : O2Data (autI S.elem L) x N) :
    V ≤ centerOf (pCoreOf 2 (S.cLH x ⊔ pCoreOf 2 (L ⊔ T))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQN : pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer (V : Set G) :=
    S.Q_le_T.trans S.T_le_normalizer
  have hLQN : S.cLH x ⊔ pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (S.LH_le_normalizer x) hQN
  have hLHQ : S.cLH x ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    ((S.LH_le x).trans inf_le_left).trans (le_sup_left.trans (le_normalizer_pCoreOf 2 (L ⊔ T)))
  have hVQ : V ≤ pCoreOf 2 (L ⊔ T) := by
    rw [← S.q_eq]
    refine le_inf S.V_le_T fun v hv => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := S.elem.1
    exact (setLike_mul_comm hw hv)
  have hQP : pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 (S.cLH x ⊔ pCoreOf 2 (L ⊔ T)) :=
    le_pCoreOf_of_le_normalizer 2 le_sup_right
    (sup_le hLHQ Subgroup.le_normalizer) (pCoreOf_isPGroup 2 _)
  have hautQ : autI S.elem (pCoreOf 2 (L ⊔ T)) = ⊥ :=
    autI_eq_bot_of_le_centralizer S.elem S.Q_le_centralizer
  have hautLQ : autI S.elem (S.cLH x ⊔ pCoreOf 2 (L ⊔ T)) = S.cY x := by
    rw [autI, Subgroup.subgroupOf_sup (S.LH_le_normalizer x) hQN, Subgroup.map_sup, ← autI,
      ← autI, hautQ, sup_bot_eq, S.autI_LH x]
  have hPC : pCoreOf 2 (S.cLH x ⊔ pCoreOf 2 (L ⊔ T)) ≤ Subgroup.centralizer (V : Set G) :=
    S.le_centralizer_of_pGroup hN hx ((pCoreOf_le 2 _).trans hLQN) (pCoreOf_isPGroup 2 _)
      (hautLQ ▸ autI_mono S.elem (pCoreOf_le 2 _))
      (le_sup_left.trans (le_normalizer_pCoreOf 2 _))
  refine fun v hv => ⟨hQP (hVQ hv), Subgroup.mem_centralizer_iff.2 fun p hp => ?_⟩
  exact (Subgroup.mem_centralizer_iff.1 (hPC hp) v hv).symm

theorem cgsIn_le (x : IntMod V S.elem) :
    cgsIn (S.cH x) (pCoreOf 2 (L ⊔ T)) ≤ S.cH x ⊓ M := by
  refine iSup_le fun C => iSup_le fun hC => iSup_le fun hC1 => iSup_le fun hchar => ?_
  rw [← S.q_eq] at hC hchar
  exact le_inf inf_le_left (inf_le_right.trans (S.normalizer_char_le C hC hC1 hchar))

omit S in
theorem charTwo_of_pCoreOf_le'
    {M' Y : Subgroup G} (hM : CharTwo M') (hOY : pCoreOf 2 M' ≤ Y)
    (hYM : Y ≤ M') : CharTwo Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : pCoreOf 2 M' ≤ pCoreOf 2 Y :=
    le_pCoreOf_of_le_normalizer 2 hOY (hYM.trans (le_normalizer_pCoreOf 2 M'))
      (pCoreOf_isPGroup 2 M')
  intro z hz
  have hzC : z ∈ Subgroup.centralizer (pCoreOf 2 M' : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle) hz.2
  exact hle (hM ⟨hYM hz.1, hzC⟩)

theorem mem_zpowers_le_pCoreOf (x : IntMod V S.elem) : x.val ∈ pCoreOf 2 (S.cH x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Subgroup.zpowers x.val ≤ pCoreOf 2 (S.cH x) := by
    refine le_pCoreOf_of_le_normalizer 2 ?_ ?_
      ((show IsPGroup 2 V from fun v => ⟨1, Subtype.ext (by simpa using S.elem.2 v.1 v.2)⟩).to_le
        ((Subgroup.zpowers_le).2 x.val_mem))
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      rfl
    · intro h hh
      have hc : Commute h x.val := (Subgroup.mem_centralizer_iff.1 hh x.val rfl).symm
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨k, rfl⟩
        refine ⟨k, ?_⟩
        simp only
        rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        simp only at hk
        have h2 : h * x.val ^ k * h⁻¹ = x.val ^ k := by
          rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
        calc x.val ^ k = h⁻¹ * (h * x.val ^ k * h⁻¹) * h := by group
          _ = h⁻¹ * (h * y * h⁻¹) * h := by rw [h2, hk]
          _ = y := by group
  exact hle (Subgroup.mem_zpowers _)

theorem hypC28
    (hN : N = 20160 ∨ N = 443520) (hx : O2Data (autI S.elem L) x N) (hx1 : x ≠ 1)
    (hsyl : IsSylowTwoOf (T ⊓ S.cH x) (S.cH x ⊓ M)) :
    HypC28 (S.cH x) (pCoreOf 2 (L ⊔ T)) (S.cH x ⊓ M) (S.cLH x) V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxO := S.mem_zpowers_le_pCoreOf x
  have hO2 : pCoreOf 2 (S.cH x) ≠ ⊥ := fun h => by
    rw [h, Subgroup.mem_bot] at hxO
    exact hx1 (IntMod.val_injective (hxO.trans IntMod.val_one.symm))
  refine
    { sqtk := S.localSQTK _ hO2
      pgroup := pCoreOf_isPGroup 2 _
      le_M := S.Q_le_MH x
      le_H := inf_le_left
      charTwo := charTwo_of_pCoreOf_le' S.charTwo (S.pCoreOf_M_le_MH x) inf_le_right
      pCore_ne := hO2
      comp := S.mem_cComp_LH hN hx
      sylow := ?_
      cgs := S.cgsIn_le x
      V_le := by rw [S.conjClosure_LH x]; exact S.V_le_LH hx
      V_ne := fun h => hx1 (IntMod.val_injective
        (((Subgroup.eq_bot_iff_forall V).1 h x.val x.val_mem).trans IntMod.val_one.symm))
      V_elem := S.elem
      V_comm := by rw [S.conjClosure_LH x]; exact S.commutator_V_LH hx
      V_center := by rw [S.conjClosure_LH x]; exact S.V_le_center hN hx
      V_norm := fun g hg => ⟨hg.1, S.normalizer_le hg.2⟩ }
  rw [S.conjClosure_LH x]
  set Q := pCoreOf 2 (L ⊔ T)
  set Cs := centralizerSection (S.cH x ⊓ M) (S.cLH x) (pCoreOf 2 (S.cLH x))
  have hCle : Cs ≤ S.cH x ⊓ M := centralizerSection_le_left _ _ _
  have hnorm : S.cH x ⊓ M ≤ Subgroup.normalizer (Cs : Set G) := by
    intro g hg
    have hgX := S.MH_le_normalizer_LH x hg
    have hgZ := normalizer_le_normalizer_pCoreOf 2 (S.cLH x) hgX
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact conj_mem_centralizerSection (Subgroup.le_normalizer hg) hgX hgZ
    · intro hc
      have := conj_mem_centralizerSection (Subgroup.le_normalizer ((S.cH x ⊓ M).inv_mem hg))
        (Subgroup.inv_mem _ hgX) (Subgroup.inv_mem _ hgZ) hc
      simpa [mul_assoc] using this
  have h1 := A4.isSylowTwoOf_inf_normal hsyl hCle hnorm
  have heq : T ⊓ S.cH x ⊓ Cs = Q := by
    refine le_antisymm ?_ ?_
    · rintro t ⟨⟨htT, -⟩, htC⟩
      rw [show Q = T ⊓ Subgroup.centralizer (V : Set G) from S.q_eq.symm]
      refine ⟨htT, S.mem_centralizer_of_comm hx (S.MH_le_normalizer hx1 htC.1) fun l hl => ?_⟩
      exact S.pCoreOf_LH_le hN hx (htC.2.2.2 l hl)
    · intro q hq
      have hqMH := S.Q_le_MH x hq
      refine ⟨⟨S.Q_le_T hq, hqMH.1⟩, hqMH, S.MH_le_normalizer_LH x hqMH,
        normalizer_le_normalizer_pCoreOf 2 (S.cLH x) (S.MH_le_normalizer_LH x hqMH), ?_⟩
      intro l hl
      have hlQ : l * q * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1
        (le_normalizer_pCoreOf 2 (L ⊔ T) (le_sup_left (a := L) ((S.LH_le x) hl).1)) q).1 hq
      have hqL : q * l⁻¹ * q⁻¹ ∈ S.cLH x := (Subgroup.mem_normalizer_iff.1
        (S.MH_le_normalizer_LH x hqMH) l⁻¹).1 (Subgroup.inv_mem _ hl)
      have hmem : l * q * l⁻¹ * q⁻¹ ∈ Q ⊓ S.cLH x := by
        refine ⟨Q.mul_mem hlQ (Q.inv_mem hq), ?_⟩
        have : l * q * l⁻¹ * q⁻¹ = l * (q * l⁻¹ * q⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ hl hqL
      refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
        ((pCoreOf_isPGroup 2 (L ⊔ T)).to_le inf_le_left) hmem
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have e1 := Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 (L ⊔ T)
        (le_sup_left (a := L) ((S.LH_le x) hg).1)) y
      have e2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hg) y
      exact ⟨fun hy => ⟨e1.1 hy.1, e2.1 hy.2⟩, fun hy => ⟨e1.2 hy.1, e2.2 hy.2⟩⟩
  rw [heq] at h1
  exact h1

theorem centralizer_le_of_sylow
    (hC48 : ASC48Statement G) (hN : N = 20160 ∨ N = 443520)
    (hx : O2Data (autI S.elem L) x N) (hx1 : x ≠ 1)
    (hsyl : IsSylowTwoOf (T ⊓ S.cH x) (S.cH x ⊓ M)) : S.cH x ≤ M := by
  by_contra hnot
  have hlt : S.cH x ⊓ M < S.cH x :=
    lt_of_le_of_ne inf_le_left fun h => hnot (inf_eq_left.1 h)
  exact false_of_c48Conclusion (S.psiLH hN hx) (S.psiLH_surjective hN hx)
    (by rw [hx.2.1]; exact hN) S.card (hC48 _ _ _ _ _ (S.hypC28 hN hx hx1 hsyl) hlt)

omit [Finite G] S in
theorem isSylowTwoOf_cjSub {E X : Subgroup G} (hE : IsSylowTwoOf E X) (g : G) :
    IsSylowTwoOf (cjSub g E) (cjSub g X) := by
  refine ⟨Subgroup.map_mono hE.1, hE.2.1.map _, ?_⟩
  have h : ((cjSub g E).subgroupOf (cjSub g X)).index = (E.subgroupOf X).index :=
    Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) E X
      (MulAut.conj g).injective
  rw [h]
  exact hE.2.2

omit [Finite G] S in
theorem isSylowTwoOf_of_le {A B X : Subgroup G} (hA : IsSylowTwoOf A X) (hAB : A ≤ B)
    (hBX : B ≤ X) (hB : IsPGroup 2 B) : IsSylowTwoOf B X :=
  ⟨hBX, hB, fun h => hA.2.2 (h.trans (Subgroup.relIndex_dvd_of_le_left X hAB))⟩

theorem centralizer_le
    (hC48 : ASC48Statement G) (hN : N = 20160 ∨ N = 443520)
    (hx : O2Data (autI S.elem L) x N) (hx1 : x ≠ 1) : S.cH x ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXN := S.MH_le_normalizer hx1
  obtain ⟨E, hE, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : ⊥ ≤ S.cH x ⊓ M) IsPGroup.of_bot
  have hTN : IsSylowTwoOf T (Subgroup.normalizer (V : Set G)) := by
    refine ⟨S.T_le_normalizer, S.sylow.2.1, fun h => S.sylow.2.2 ?_⟩
    have h1 := Subgroup.relIndex_dvd_index_of_le (H := T) S.T_le_normalizer
    change 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact h.trans h1
  obtain ⟨g, hg, hgE⟩ := exists_conj_le_of_isSylowTwoOf hTN (hE.1.trans hXN) hE.2.1
  have hgM : g ∈ M := S.normalizer_le hg
  set x' : IntMod V S.elem := convI S.elem ⟨g, hg⟩ x
  have hx'v : x'.val = g * x.val * g⁻¹ := convI_apply_val S.elem _ _
  have hCx' : S.cH x' = cjSub g (S.cH x) := by
    ext y
    rw [mem_cjSub, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq, hx'v]
    constructor
    · intro h
      calc x.val * (g⁻¹ * y * g) = g⁻¹ * ((g * x.val * g⁻¹) * y) * g := by group
        _ = g⁻¹ * (y * (g * x.val * g⁻¹)) * g := by rw [h]
        _ = g⁻¹ * y * g * x.val := by group
    · intro h
      calc g * x.val * g⁻¹ * y = g * (x.val * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * x.val) * g⁻¹ := by rw [h]
        _ = y * (g * x.val * g⁻¹) := by group
  have hMiff : ∀ y : G, y ∈ M ↔ g⁻¹ * y * g ∈ M := by
    intro y
    constructor
    · intro h
      exact M.mul_mem (M.mul_mem (M.inv_mem hgM) h) hgM
    · intro h
      have := M.mul_mem (M.mul_mem hgM h) (M.inv_mem hgM)
      simpa [mul_assoc] using this
  have hX' : S.cH x' ⊓ M = cjSub g (S.cH x ⊓ M) := by
    ext y
    rw [Subgroup.mem_inf, hCx', mem_cjSub, mem_cjSub, Subgroup.mem_inf, hMiff]
  have hsyl' : IsSylowTwoOf (T ⊓ S.cH x') (S.cH x' ⊓ M) := by
    rw [hX']
    refine isSylowTwoOf_of_le (isSylowTwoOf_cjSub hE g) ?_ ?_
      (S.sylow.2.1.to_le inf_le_left)
    · refine le_inf hgE ?_
      rw [hCx']
      exact Subgroup.map_mono (hE.1.trans inf_le_left)
    · rw [← hX']
      exact le_inf inf_le_right (inf_le_left.trans S.T_le_M)
  have hx'1 : x' ≠ 1 := by
    intro h
    exact hx1 ((map_eq_one_iff _ (convI S.elem ⟨g, hg⟩).injective).1 h)
  have hμ : convI S.elem ⟨g, hg⟩ ∈
      Subgroup.normalizer (autI S.elem L : Set (MulAut (IntMod V S.elem))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro φ
    have hgL := S.le_normalizer_L hgM
    constructor
    · intro hφ
      obtain ⟨l, hl, rfl⟩ := (mem_autI S.elem).1 hφ
      rw [← map_inv, ← map_mul, ← map_mul]
      refine (mem_autI S.elem).2 ⟨_, ?_, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hgL l).1 hl
    · intro hφ
      obtain ⟨l, hl, hle⟩ := (mem_autI S.elem).1 hφ
      have : φ = convI S.elem (⟨g, hg⟩⁻¹ * l * ⟨g, hg⟩) := by
        rw [map_mul, map_mul, hle, map_inv]
        group
      rw [this]
      refine (mem_autI S.elem).2 ⟨_, ?_, rfl⟩
      have := (Subgroup.mem_normalizer_iff''.1 hgL l).1 hl
      simpa using this
  have hx' : O2Data (autI S.elem L) x' N := O2Data.of_normalizer hμ hx
  have hle := S.centralizer_le_of_sylow hC48 hN hx' hx'1 hsyl'
  intro y hy
  have hy' : g * y * g⁻¹ ∈ S.cH x' := by
    rw [hCx', mem_cjSub]
    simpa [mul_assoc] using hy
  have := M.mul_mem (M.mul_mem (M.inv_mem hgM) (hle hy')) hgM
  simpa [mul_assoc] using this

end Setting811

end CFSG.Quasithin.H13

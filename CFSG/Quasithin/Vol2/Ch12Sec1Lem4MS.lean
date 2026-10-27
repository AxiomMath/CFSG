module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem6Comp
public import CFSG.Quasithin.Background.C2PushY
public import CFSG.Quasithin.EmptyFaithful.SBd7Ms

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix CFSG.LieType.BorelTits
open scoped Pointwise

namespace Sec1214

variable {G : Type} [Group G] [Finite G]

theorem ker_eq_pCore {X : Type*} [Group X] [Finite X] {m : ℕ} (hm : 3 ≤ m)
    {f : X →* SpecialLinearGroup (Fin m) (ZMod 2)} (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : f.ker = CFSG.pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (le_sSup ⟨MonoidHom.normal_ker f, hk⟩) ?_
  have : ((CFSG.pCore 2 X).map f).Normal := Subgroup.Normal.map CFSG.pCore_normal f hf
  have h := KGH91.NatCoord.eq_bot_of_normal_isPGroup hm (CFSG.pCore_isPGroup.map f)
  rwa [Subgroup.map_eq_bot_iff] at h

structure Setting (T L V V₁ V₂ : Subgroup G) (v : G) (T₀ : Subgroup G) where
  S : Sec1216Lv.Setting T L V V₁ V₂ 4 v
  h331 : Stmt3_3_1
  hT₀ : quasithinIsSylowTwo T₀
  hT₁T₀ : T ⊓ Subgroup.normalizer (V₁ : Set G) ≤ T₀
  hT₀v : T₀ ≤ Subgroup.centralizer ({v} : Set G)
  hT₀N : T₀ ≤ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G)
  hT₀M : ¬ T₀ ≤ Subgroup.normalizer (L : Set G)

namespace Setting

variable {T L V V₁ V₂ T₀ : Subgroup G} {v : G} (c : Setting T L V V₁ V₂ v T₀)
include c

theorem T₁_two : IsPGroup 2 ↥(T ⊓ Subgroup.normalizer (V₁ : Set G)) :=
  c.S.ctx.hyp.sylow.1.to_le inf_le_left

theorem G₀_le : Sec1216Lv.lv L v ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G)) ≤
    Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({v} : Set G) :=
  sup_le (le_inf ((Sec1216Lv.lv_le_L L v).trans Subgroup.le_normalizer)
    (Sec1216Lv.lv_le_centralizer L v)) (le_inf c.S.ctx.T₁_le_NL c.S.ctx.T₁_le)

theorem isSylowTwoOf_G₀ : IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G))
    (Sec1216Lv.lv L v ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G))) := by
  have := c.S.ctx.hVe.1
  exact Sec1215.isSylowTwoOf_of_le_of_le
    (Sec1215.isSylowTwoOf_inf_normalizer c.S.ctx.hyp c.S.ctx.hTL).2 le_sup_right
    (c.G₀_le.trans fun m hm => ⟨hm.1, Sec1215.mem_normalizer_of_mem_centralizer c.S.ctx.hyp
      c.S.ctx.v_mem_V₁ c.S.ctx.v_ne_one hm.1 hm.2⟩)

theorem coe_G₀ : ((Sec1216Lv.lv L v ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G)) : Subgroup G) :
    Set G) = (Sec1216Lv.lv L v : Set G) * ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) :
      Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _ c.S.T₁_le_normalizer_lv

theorem conj_mem_T₁ {t s : G} (ht : t ∈ T) (hs : s ∈ T ⊓ Subgroup.normalizer (V₁ : Set G)) :
    t * s * t⁻¹ ∈ T ⊓ Subgroup.normalizer (V₁ : Set G) := by
  have := c.S.ctx.hVe.1
  refine ⟨T.mul_mem (T.mul_mem ht hs.1) (T.inv_mem ht), ?_⟩
  by_cases htV : t ∈ Subgroup.normalizer (V₁ : Set G)
  · exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem htV hs.2)
      ((Subgroup.normalizer _).inv_mem htV)
  have htV' : t⁻¹ ∉ Subgroup.normalizer (V₁ : Set G) := fun h =>
    htV (by simpa using (Subgroup.normalizer (V₁ : Set G)).inv_mem h)
  have hsw := Sec121Swap.swap_of_hyp121 c.S.ctx.hyp (c.S.ctx.hTL ht) htV
  have hsw' := Sec121Swap.swap_of_hyp121 c.S.ctx.hyp (c.S.ctx.hTL (T.inv_mem ht)) htV'
  refine Sec121Swap.mem_normalizer_of_conj_mem fun a ha => ?_
  have h1 : s * (t⁻¹ * a * t⁻¹⁻¹) * s⁻¹ ∈ V₂ :=
    c.S.ctx.conj_V₂ (c.S.ctx.T₁_le_NL hs) hs.2 (hsw'.1 a ha)
  have e : t * s * t⁻¹ * a * (t * s * t⁻¹)⁻¹ = t * (s * (t⁻¹ * a * t⁻¹⁻¹) * s⁻¹) * t⁻¹ := by
    group
  rw [e]
  exact hsw.2 _ h1

theorem T_le_normalizer_T₁ :
    T ≤ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) :=
  fun _ ht => Sec121Swap.mem_normalizer_of_conj_mem fun _ hs => c.conj_mem_T₁ ht hs

theorem pCoreOf_L_le : pCoreOf 2 L ≤ T ⊓ Subgroup.normalizer (V₁ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer c.S.ctx.hTL
  have hOL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
      (fun g hg => normalizer_le_normalizer_pCoreOf 2 L (hLTN hg)) (pCoreOf_isPGroup 2 L)
  rw [setup121Q_holds G T L V V₁ V₂ 4 c.S.ctx.hyp c.S.ctx.hTL] at hOL
  exact hOL.trans (inf_le_inf_left _ ((Subgroup.centralizer_le (by
    exact_mod_cast c.S.ctx.V₁_le)).trans (Subgroup.centralizer_le_normalizer _)))

theorem le_of_lv_le {X : Subgroup G} (hLv : Sec1216Lv.lv L v ≤ X) (hO : pCoreOf 2 L ≤ X)
    {l : G} (hl : l ∈ L) (hlX : l ∈ X) (hlv : l ∉ Subgroup.centralizer ({v} : Set G)) :
    L ≤ X := by
  classical
  set x₀ := c.S.C₁.E v with hx₀
  set H : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)) := (X.subgroupOf L).map c.S.C₁.ρ with hH
  have hstab : VecStab.vecStab x₀ ≤ H := fun g hg => by
    obtain ⟨l', hl', rfl⟩ := c.S.exists_mem_lv hg
    exact ⟨l', Subgroup.mem_subgroupOf.mpr (hLv hl'), rfl⟩
  have hg₁H : c.S.C₁.ρ ⟨l, hl⟩ ∈ H := ⟨⟨l, hl⟩, Subgroup.mem_subgroupOf.mpr hlX, rfl⟩
  have hg₁ : ((c.S.C₁.ρ ⟨l, hl⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x₀ ≠ x₀ := fun h =>
    hlv ((c.S.mem_centralizer_iff ⟨l, hl⟩).mpr h)
  have hne0 : ∀ g : SpecialLinearGroup (Fin 4) (ZMod 2),
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x₀ ≠ 0 := fun g h0 => by
    apply c.S.x₀_ne
    have := VecStab.inv_mulVec_mulVec g x₀
    rw [h0, mulVec_zero] at this
    exact this.symm
  have htop : H = ⊤ := by
    rw [eq_top_iff]
    intro h _
    by_cases hy : (h : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x₀ = x₀
    · exact hstab hy
    obtain ⟨A, hA₀, hA⟩ := Sec1216Gen.exists_sl_fix c.S.x₀_ne (hne0 _) hg₁ (hne0 h) hy
    have hk : A * c.S.C₁.ρ ⟨l, hl⟩ ∈ H := H.mul_mem (hstab hA₀) hg₁H
    have hk' : (A * c.S.C₁.ρ ⟨l, hl⟩)⁻¹ * h ∈ VecStab.vecStab x₀ := by
      rw [VecStab.mem_vecStab, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec]
      have e : ((A * c.S.C₁.ρ ⟨l, hl⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x₀ = (h : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x₀ := by
        rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hA]
      rw [← e, VecStab.inv_mulVec_mulVec]
    have := H.mul_mem hk (hstab hk')
    rwa [mul_inv_cancel_left] at this
  intro x hx
  have hρx : c.S.C₁.ρ ⟨x, hx⟩ ∈ H := htop ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hρx
  have hk : y⁻¹ * ⟨x, hx⟩ ∈ c.S.C₁.ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  obtain ⟨ι⟩ := c.S.ctx.hyp.iso
  rw [c.S.C₁.ker_eq (by norm_num) ι] at hk
  have hxO : ((y⁻¹ * ⟨x, hx⟩ : ↥L) : G) ∈ pCoreOf 2 L :=
    ⟨_, CFSG.LieType.BorelTits.le_pCore 2 CFSG.pCore_normal CFSG.pCore_isPGroup hk, rfl⟩
  have := X.mul_mem (Subgroup.mem_subgroupOf.mp hy) (hO hxO)
  simpa using this

theorem conj_v_mem {t : G} (ht : t ∈ T) (htV : t ∉ Subgroup.normalizer (V₁ : Set G)) :
    t * v * t⁻¹ ∈ c.S.ctx.U₂ ∧ t * v * t⁻¹ ≠ 1 ∧
      ∀ s ∈ T ⊓ Subgroup.normalizer (V₁ : Set G), s * (t * v * t⁻¹) * s⁻¹ = t * v * t⁻¹ := by
  have := c.S.ctx.hVe.1
  have hsw := Sec121Swap.swap_of_hyp121 c.S.ctx.hyp (c.S.ctx.hTL ht) htV
  have hwV : t * v * t⁻¹ ∈ V₂ := hsw.1 v c.S.ctx.v_mem_V₁
  have hwT : ∀ s ∈ T ⊓ Subgroup.normalizer (V₁ : Set G), s * (t * v * t⁻¹) * s⁻¹ =
      t * v * t⁻¹ := by
    intro s hs
    have h1 := c.conj_mem_T₁ (T.inv_mem ht) hs
    have h2 : (t⁻¹ * s * t⁻¹⁻¹) * v * (t⁻¹ * s * t⁻¹⁻¹)⁻¹ = v := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (c.S.ctx.T₁_le h1)
      rw [this, mul_inv_cancel_right]
    calc s * (t * v * t⁻¹) * s⁻¹ =
        t * ((t⁻¹ * s * t⁻¹⁻¹) * v * (t⁻¹ * s * t⁻¹⁻¹)⁻¹) * t⁻¹ := by group
      _ = t * v * t⁻¹ := by rw [h2]
  refine ⟨⟨hwV, c.S.pairing_eq_zero hwV hwT⟩, fun h => c.S.ctx.v_ne_one ?_, hwT⟩
  have e : v = t⁻¹ * (t * v * t⁻¹) * t := by group
  rw [e, h]
  group

theorem exists_conj_not_mem {t : G} (ht : t ∈ T) (htV : t ∉ Subgroup.normalizer (V₁ : Set G)) :
    ∃ l ∈ Sec1216Lv.lv L v, t⁻¹ * l * t ∉ Subgroup.centralizer ({v} : Set G) := by
  obtain ⟨hwU, hw1, -⟩ := c.conj_v_mem ht htV
  by_contra hcon
  push Not at hcon
  apply hw1
  refine c.S.eq_one_of_fixed hwU fun l hl => ?_
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hcon l hl)
  calc l * (t * v * t⁻¹) * l⁻¹ = t * ((t⁻¹ * l * t) * v * (t⁻¹ * l * t)⁻¹) * t⁻¹ := by group
    _ = t * v * t⁻¹ := by rw [h1, mul_inv_cancel_right]

theorem le_of_lv_le_of_T {X : Subgroup G} (hLv : Sec1216Lv.lv L v ≤ X) (hO : pCoreOf 2 L ≤ X)
    (hT : T ≤ X) : L ≤ X := by
  have := c.S.ctx.hVe.1
  obtain ⟨t, ht, htV⟩ := Sec121Swap.exists_mem_not_normalizer c.S.ctx.hyp c.S.ctx.hTL
  obtain ⟨l, hl, hlv⟩ := c.exists_conj_not_mem ht htV
  have hlL : t⁻¹ * l * t ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (c.S.ctx.hTL (T.inv_mem ht)) l).mp
      (Sec1216Lv.lv_le_L L v hl)
    simpa using this
  exact c.le_of_lv_le hLv hO hlL
    (X.mul_mem (X.mul_mem (X.inv_mem (hT ht)) (hLv hl)) (hT ht)) hlv

theorem isUniqueM_sup : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G)) := by
  have hqs := Sec121Thm.isQuasisimple_of_hyp121 c.S.ctx.hyp
  have hLT : conjClosure L T = L :=
    le_antisymm (conjClosure_le fun t ht l hl =>
      (Subgroup.mem_normalizer_iff.mp (c.S.ctx.hTL ht) l).mp hl) (le_conjClosure L T)
  obtain ⟨⟨hMmax, -, huniqLT⟩, -⟩ :=
    (c.h331 G T c.S.ctx.hyp.simple c.S.ctx.hyp.nonabelian c.S.ctx.hyp.qtke
      c.S.ctx.hyp.sylow).2 L c.S.ctx.hyp.maximal hqs
  rw [hLT] at hMmax huniqLT
  exact ⟨⟨hMmax, sup_le Subgroup.le_normalizer c.S.ctx.hTL⟩, fun M' hM' => huniqLT M' hM'.1 hM'.2⟩

theorem normalizer_le {C : Subgroup G} (hC1 : C ≠ ⊥) (hC2 : IsPGroup 2 C)
    (hLT : L ⊔ T ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.normalizer (C : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨M'', hM'', hle⟩ := exists_maxTwoLocal_ge ⟨C, hC1, hC2, rfl⟩
  rw [← c.isUniqueM_sup.2 M'' ⟨hM'', hLT.trans hle⟩]
  exact hle

theorem ms3 {C : Subgroup G} (hCR : C ≤ T ⊓ Subgroup.normalizer (V₁ : Set G)) (hC1 : C ≠ ⊥)
    (hCc : (C.subgroupOf (T ⊓ Subgroup.normalizer (V₁ : Set G))).Characteristic)
    (hG₀ : Sec1216Lv.lv L v ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G)) ≤
      Subgroup.normalizer (C : Set G)) : False := by
  have hNC : Subgroup.normalizer
      ((T ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (C : Set G) := by
    have h1 := normalizer_le_normalizer_map_of_characteristic
      (C.subgroupOf (T ⊓ Subgroup.normalizer (V₁ : Set G)))
    rwa [Subgroup.map_subgroupOf_eq_of_le hCR] at h1
  have hT : T ≤ Subgroup.normalizer (C : Set G) := c.T_le_normalizer_T₁.trans hNC
  have hL : L ≤ Subgroup.normalizer (C : Set G) :=
    c.le_of_lv_le_of_T (le_sup_left.trans hG₀)
      (c.pCoreOf_L_le.trans (Subgroup.le_normalizer.trans hNC)) hT
  exact c.hT₀M ((c.hT₀N.trans hNC).trans
    (c.normalizer_le hC1 (c.T₁_two.to_le hCR) (sup_le hL hT)))

theorem exists_isModO2Surj : ∃ α : ↥(Sec1216Lv.lv L v) →*
    ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)), IsModO2Surj (Sec1216Lv.lv L v) α := by
  obtain ⟨f, hf, hfk⟩ := c.S.exists_levi
  let f' : ↥(Sec1216Lv.lv L v) →* SpecialLinearGroup (Fin 3) (ZMod 2) := f
  refine ⟨(CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)).toMonoidHom.comp f',
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)).surjective.comp hf, ?_⟩
  have hker :
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)).toMonoidHom.comp
        f').ker = f'.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  rw [hker]
  exact ker_eq_pCore le_rfl hf hfk

theorem isMSPair : IsMSPair (Sec1216Lv.lv L v ⊔ (T ⊓ Subgroup.normalizer (V₁ : Set G)))
    (T ⊓ Subgroup.normalizer (V₁ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := c.S.ctx.hVe.1
  set T₁ := T ⊓ Subgroup.normalizer (V₁ : Set G) with hT₁
  set G₀ := Sec1216Lv.lv L v ⊔ T₁ with hG₀
  have hsyl := c.isSylowTwoOf_G₀
  have hsq : IsSQTKIn G₀ := IsSQTKIn.mono (sqtkGroup_of_pCoreOf_ne_bot c.S.ctx.hyp.qtke
    c.S.ctx.hyp.simple c.S.ctx.hyp.nonabelian (fun hb => c.S.ctx.v_ne_one (by
      have := c.S.ctx.zpowers_le_Qv (Subgroup.mem_zpowers v)
      rwa [hb, Subgroup.mem_bot] at this))) (c.G₀_le.trans inf_le_right)
  have hTM : T ≤ Subgroup.normalizer (L : Set G) := c.S.ctx.hTL
  have hTsyl : IsSylowTwoOf T (Subgroup.normalizer (L : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo c.S.ctx.hyp.sylow hTM
  have hOM : pCoreOf 2 (Subgroup.normalizer (L : Set G)) ≤ T₁ := by
    refine le_inf (B6.pCoreOf_two_le_of_isSylowTwoOf hTsyl) ?_
    have h1 := InternalSec.pCoreOf_le_centralizer_of_isPrimeReduced c.S.ctx.hyp.le
      c.S.ctx.hyp.reduced (IsSubnormal.refl _)
    exact h1.trans ((Subgroup.centralizer_le (by exact_mod_cast c.S.ctx.V₁_le)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hOM1 : pCoreOf 2 (Subgroup.normalizer (L : Set G)) ≠ ⊥ := by
    intro hb
    apply Sec121Thm.ne_bot_of_hyp121 c.S.ctx.hyp
    rw [eq_bot_iff, ← hb]
    exact le_pCoreOf_of_le_normalizer 2 c.S.ctx.hyp.le
      (Sec121Q.normalizer_le_of_hyp121 c.S.ctx.hyp)
      (fun x => ⟨1, Subtype.ext (by simpa using c.S.ctx.hVe.2 x x.2)⟩)
  have hMchar : CharTwo (Subgroup.normalizer (L : Set G)) :=
    charTwo_of_inH c.S.ctx.hyp.qtke.2.1 (c.S.ctx.hyp.sylow.1.toSylow c.S.ctx.hyp.sylow.2)
      ⟨hTM, hOM1⟩
  have hchar : CharTwo G₀ :=
    C2Push.charTwo_of_pCoreOf_le hMchar (hOM.trans le_sup_right) (c.G₀_le.trans inf_le_left)
  have hcomp : Sec1216Lv.lv L v ∈ cComp G₀ := c.S.mem_lFamily
  obtain ⟨α, hα⟩ := c.exists_isModO2Surj
  have hLie := SBd7.isRankTwoLie2Derived_of_modO2 α hα.1 hα.2
  have hms3 : ∀ C : Subgroup G, C ≤ T₁ → C ≠ ⊥ → (C.subgroupOf T₁).Characteristic →
      ¬ G₀ ≤ Subgroup.normalizer (C : Set G) := fun C hCR hC1 hCc hG => c.ms3 hCR hC1 hCc hG
  have hT₁1 : T₁ ≠ ⊥ := by
    intro hb
    apply c.S.ctx.v_ne_one
    have := c.S.ctx.V_le_T₁ c.S.ctx.v_mem_V
    rwa [← hT₁, hb, Subgroup.mem_bot] at this
  have hnorm : ¬ G₀ ≤ Subgroup.normalizer (T₁ : Set G) :=
    hms3 T₁ le_rfl hT₁1 (by rw [Subgroup.subgroupOf_self]; infer_instance)
  set H' := G₀ ⊓ Subgroup.normalizer (T₁ : Set G) with hH'
  have hT₁H' : T₁ ≤ H' := le_inf hsyl.1 Subgroup.le_normalizer
  have hlt : H' < G₀ := lt_of_le_of_ne inf_le_left fun h => hnorm (h ▸ inf_le_right)
  have hodd : ¬ 2 ∣ H'.relIndex G₀ := by
    intro h2
    apply hsyl.2.2
    rw [← Subgroup.relIndex]
    rw [← Subgroup.relIndex_mul_relIndex T₁ H' G₀ hT₁H' inf_le_left]
    exact Dvd.dvd.mul_left h2 _
  have hO : T₁ = pCoreOf 2 H' := by
    have hsyl' : IsSylowTwoOf T₁ H' := Sec1215.isSylowTwoOf_of_le_of_le hsyl hT₁H' inf_le_left
    exact le_antisymm (le_pCoreOf_of_le_normalizer 2 hT₁H' inf_le_right c.T₁_two)
      (B6.pCoreOf_two_le_of_isSylowTwoOf hsyl')
  exact ⟨⟨hsq, hchar, Sec1216Lv.lv L v, hcomp, c.coe_G₀, hLie⟩, Or.inl ⟨H', hlt, hodd, hO⟩,
    hms3⟩

end Setting

end Sec1214

end CFSG.Quasithin.H13

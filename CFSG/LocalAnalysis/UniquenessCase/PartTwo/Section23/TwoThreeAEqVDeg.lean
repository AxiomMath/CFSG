module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveApply
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.BarSubISup
public import CFSG.GroupTheory.PCoreOfSubnormal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.GLTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.ActionOnSub
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeAEqV
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def commMap {W : Type} [CommGroup W] (s : MulAut W) : W →* W where
  toFun w := s w * w⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv]
    ac_rfl

theorem mem_fixV_zpowers_iff {W : Type} [CommGroup W] {s : MulAut W} {w : W} :
    w ∈ fixV (Subgroup.zpowers s) ↔ s w = w := by
  rw [mem_fixV]
  refine ⟨fun h => h s (Subgroup.mem_zpowers s), fun h x hx => ?_⟩
  have hH : Subgroup.zpowers s ≤
      { carrier := {y : MulAut W | y w = w}
        mul_mem' := by
          intro a b ha hb
          have ha' : a w = w := ha
          have hb' : b w = w := hb
          show (a * b) w = w
          rw [MulAut.mul_apply, hb', ha']
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          have h2 : a⁻¹ (a w) = w := by
            rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
          calc a⁻¹ w = a⁻¹ (a w) := by rw [ha]
            _ = w := h2 } :=
    Subgroup.zpowers_le.mpr h
  exact hH hx

theorem ker_commMap {W : Type} [CommGroup W] (s : MulAut W) :
    (commMap s).ker = fixV (Subgroup.zpowers s) := by
  ext w
  rw [MonoidHom.mem_ker, mem_fixV_zpowers_iff]
  exact mul_inv_eq_one

theorem eq_one_or_eq_of_mem_zpowers {W : Type} [CommGroup W] (s : MulAut W) (hs : s ^ 2 = 1)
    {x : MulAut W} (hx : x ∈ Subgroup.zpowers s) : x = 1 ∨ x = s := by
  have hs' : s * s = 1 := by simpa [pow_two] using hs
  have hle : Subgroup.zpowers s ≤
      { carrier := {y : MulAut W | y = 1 ∨ y = s}
        mul_mem' := by
          intro a b ha hb
          have ha' : a = 1 ∨ a = s := ha
          have hb' : b = 1 ∨ b = s := hb
          rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2 <;> rw [h1, h2]
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact Or.inr rfl
          · exact Or.inl hs'
        one_mem' := Or.inl rfl
        inv_mem' := by
          intro a ha
          have ha' : a = 1 ∨ a = s := ha
          rcases ha' with h1 | h1 <;> rw [h1]
          · exact Or.inl inv_one
          · exact Or.inr (inv_eq_of_mul_eq_one_right hs') } :=
    Subgroup.zpowers_le.mpr (Or.inr rfl)
  exact hle hx

theorem range_commMap {W : Type} [CommGroup W] (s : MulAut W) (hs : s ^ 2 = 1) :
    (commMap s).range = commV (Subgroup.zpowers s) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, rfl⟩
    exact Subgroup.subset_closure ⟨s, Subgroup.mem_zpowers s, w, rfl⟩
  · unfold commV
    rw [Subgroup.closure_le]
    rintro u ⟨x, hx, v, rfl⟩
    rcases eq_one_or_eq_of_mem_zpowers s hs hx with h1 | h1
    · rw [h1]
      have h2 : (1 : MulAut W) v * v⁻¹ = 1 := by simp
      rw [h2]
      exact ⟨1, map_one (commMap s)⟩
    · rw [h1]
      exact ⟨v, rfl⟩

theorem card_commV_zpowers_mul_card_fixV {W : Type} [CommGroup W] [Finite W] (s : MulAut W)
    (hs : s ^ 2 = 1) :
    Nat.card ↥(commV (Subgroup.zpowers s)) * Nat.card ↥(fixV (Subgroup.zpowers s)) =
      Nat.card W := by
  have h1 : Nat.card (W ⧸ (commMap s).ker) = Nat.card ↥(commV (Subgroup.zpowers s)) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (commMap s)).toEquiv,
      range_commMap s hs]
  rw [ker_commMap s] at h1
  rw [← h1]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (fixV (Subgroup.zpowers s))).symm

theorem rk_commV_zpowers_eq_rkIdx_fixV {W : Type} [CommGroup W] [Finite W] (s : MulAut W)
    (hs : s ^ 2 = 1) :
    rk ↥(commV (Subgroup.zpowers s)) = rkIdx (fixV (Subgroup.zpowers s)) := by
  unfold rk rkIdx
  have hcard := card_commV_zpowers_mul_card_fixV s hs
  rw [mul_comm] at hcard
  have hidx : (fixV (Subgroup.zpowers s)).index = Nat.card ↥(commV (Subgroup.zpowers s)) :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos
      ((Subgroup.card_mul_index (fixV (Subgroup.zpowers s))).trans hcard.symm)
  rw [hidx]

theorem commV_zpowers_map_mem {W : Type} [CommGroup W] (s : MulAut W) {x : MulAut W}
    (hx : Commute x s) {u : W} (hu : u ∈ commV (Subgroup.zpowers s)) :
    x u ∈ commV (Subgroup.zpowers s) := by
  have hc : ∀ k ∈ Subgroup.zpowers s, x * k = k * x := by
    intro k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact (hx.zpow_right n).eq
  induction hu using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, v, rfl⟩ := hy
    have hcomp : x (k v) = k (x v) := by
      have h1 : (x * k) v = (k * x) v := by rw [hc k hk]
      simpa only [MulAut.mul_apply] using h1
    rw [map_mul, map_inv, hcomp]
    exact Subgroup.subset_closure ⟨k, hk, x v, rfl⟩
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem le_stabSub_commV {W : Type} [CommGroup W] (s : MulAut W) (X : Subgroup (MulAut W))
    (h : ∀ x ∈ X, Commute x s) : X ≤ stabSub (commV (Subgroup.zpowers s)) := by
  intro x hx
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have h1 : x⁻¹ (x u) ∈ commV (Subgroup.zpowers s) :=
      commV_zpowers_map_mem s (h x hx).inv_left hu
    rwa [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h1
  · exact commV_zpowers_map_mem s (h x hx)

theorem dMinDeg_le_rk_of_nontrivial_mulAut {K B : Type} [Group K] [Finite K] [CommGroup B]
    [Finite B] (hB : ∀ b : B, b ^ 2 = 1) (φ : K →* MulAut B) (hφ : φ ≠ 1) :
    dMinDeg K ≤ rk B := by
  classical
  haveI : ExpTwo B := ⟨fun b => by simpa [pow_two] using hB b⟩
  haveI : Module.Finite (ZMod 2) (Additive B) := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod 2) (Additive B) = rk B := by
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive B)
    rw [Nat.card_congr Additive.toMul, Nat.card_zmod] at hcard
    rw [rk, hcard, padicValNat.prime_pow]
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive B) hfr
  let ψ : K →* (Additive B ≃ₗ[ZMod 2] Additive B) := toGL.comp φ
  have hψ : ψ ≠ 1 := by
    intro h
    refine hφ (MonoidHom.ext fun k => toGL_injective ?_)
    have h1 := congrArg (fun f : K →* (Additive B ≃ₗ[ZMod 2] Additive B) => f k) h
    simpa [ψ] using h1.trans (map_one toGL).symm
  let σ : (Additive B ≃ₗ[ZMod 2] Additive B) ≃*
      Matrix.GeneralLinearGroup (Fin (rk B)) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive B)).symm.trans
      (Matrix.GeneralLinearGroup.toLin' b).symm
  refine Nat.sInf_le ⟨σ.toMonoidHom.comp ψ, ?_⟩
  intro h
  refine hψ (MonoidHom.ext fun k => ?_)
  have h1 := congrArg (fun f : K →* Matrix.GeneralLinearGroup (Fin (rk B)) (ZMod 2) => f k) h
  have h2 : σ (ψ k) = 1 := by simpa using h1
  have h3 := congrArg σ.symm h2
  simpa using h3

theorem commV_zpowers_ne_bot {W : Type} [CommGroup W] (s : MulAut W) (hs : s ≠ 1) :
    commV (Subgroup.zpowers s) ≠ ⊥ := by
  obtain ⟨v, hv⟩ : ∃ v : W, s v ≠ v := by
    by_contra h
    push Not at h
    exact hs (MulEquiv.ext fun v => by simpa using h v)
  have hw : s v * v⁻¹ ≠ 1 := fun h => hv (mul_inv_eq_one.mp h)
  have hmem : s v * v⁻¹ ∈ commV (Subgroup.zpowers s) :=
    Subgroup.subset_closure ⟨s, Subgroup.mem_zpowers s, v, rfl⟩
  intro hbot
  exact hw (Subgroup.mem_bot.mp (hbot ▸ hmem))

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

private theorem n_lt_rkIdx_fixV_of_nontrivial_bar2 (c : Ctx23L D Ch) (hDeg : KMinDegLow)
    (h207 : S20_7 D) (h209 : S20_9 D) (hE : UC22P20gExcFacts) (h1930 : H1930 D)
    {s : MulAut (Vtil ⊥ c.V (isElemAbelian_V_basic c))} (hs1 : s ≠ 1)
    (hs2 : orderOf s = 2)
    (hact : ∃ K ∈ calC c.L,
      ∃ f : Bar2 K →* MulAut ↥(commV (Subgroup.zpowers s)), f ≠ 1) :
    c.n + 1 < rkIdx (fixV (Subgroup.zpowers s)) := by
  obtain ⟨K, hK, f, hf⟩ := hact
  obtain ⟨P, hP, hPL0⟩ := exists_minTInvParabolic c h209 h1930
  have hshape : S20_7Shape (Bar2 c.L) := s20_7Shape_of h207 h1930 c.hL.1
  have hNP : NParam (Hinf P) c.n := by rw [← hPL0]; exact c.hn
  have h2n : 2 < c.n := by have h := three_le_n c hE h207 h1930; omega
  have hd : c.n + 1 < dMinDeg (Bar2 K) := hDeg c.L K P c.n hshape hK hP.1.1 hNP h2n
  have hsq : s ^ 2 = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [hs2] at h
  have hVtil : ∀ v : Vtil ⊥ c.V (isElemAbelian_V_basic c), v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H x => rw [← QuotientGroup.mk_pow]; simp [IntMod.sq_eq_one]
  have hWsq : ∀ w : ↥(commV (Subgroup.zpowers s)), w ^ 2 = 1 := fun w =>
    Subtype.ext (hVtil (w : Vtil ⊥ c.V (isElemAbelian_V_basic c)))
  have hle : dMinDeg (Bar2 K) ≤ rk ↥(commV (Subgroup.zpowers s)) :=
    dMinDeg_le_rk_of_nontrivial_mulAut hWsq f hf
  rw [← rk_commV_zpowers_eq_rkIdx_fixV s hsq]
  omega

@[expose] noncomputable def actN (c : Ctx23L D Ch) (x : c.N) :
    MulAut (Vtil ⊥ c.V (isElemAbelian_V_basic c)) :=
  actTil ⊥ c.V (isElemAbelian_V_basic c)
    ⟨(x : G), mem_stabTil_bot (uc22p22v_le_normalizer_conjClosure c.N D.Z x.2)⟩

theorem pCoreOf_le_centralizer_V_of_mem_calC {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h208 : S20_8 D) (h1930 : H1930 D) {K : Subgroup G}
    (hK : K ∈ calC c.L) :
    CFSG.Open.pCoreOf 2 K ≤ Subgroup.centralizer (c.V : Set G) := by
  have hsubL : CFSG.Open.IsSubnormal K c.L := hK.1
  have hsubN : CFSG.Open.IsSubnormal c.L c.N := (N_facts c h208 h1930).2.2.1
  have h1 : CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 c.L := by
    rw [CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hsubL]
    exact inf_le_right
  have h2 : CFSG.Open.pCoreOf 2 c.L ≤ CFSG.Open.pCoreOf 2 c.N := by
    rw [CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hsubN]
    exact inf_le_right
  exact (h1.trans h2).trans (Subgroup.le_centralizer_iff.mp (V_le_centralizer_pCore c))

private noncomputable def resBarSub {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {W : Subgroup (Vtil ⊥ c.V (isElemAbelian_V_basic c))} {K : Subgroup G}
    (hKW : barSub ⊥ c.V (isElemAbelian_V_basic c) K ≤ stabSub W) :
    ↥(barSub ⊥ c.V (isElemAbelian_V_basic c) K) →* MulAut W :=
  (resHom W).comp (Subgroup.inclusion hKW)

private theorem resBarSub_apply {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {W : Subgroup (Vtil ⊥ c.V (isElemAbelian_V_basic c))} {K : Subgroup G}
    (hKW : barSub ⊥ c.V (isElemAbelian_V_basic c) K ≤ stabSub W)
    (ψ : ↥(barSub ⊥ c.V (isElemAbelian_V_basic c) K)) (w : W) :
    ((resBarSub c hKW ψ w : W) : Vtil ⊥ c.V (isElemAbelian_V_basic c)) = ψ.1 (w : _) :=
  resHom_apply W ⟨ψ.1, hKW ψ.2⟩ w

private theorem resBarSub_ne_one {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {W : Subgroup (Vtil ⊥ c.V (isElemAbelian_V_basic c))} {K : Subgroup G}
    (hKW : barSub ⊥ c.V (isElemAbelian_V_basic c) K ≤ stabSub W)
    (hact : ¬ barSub ⊥ c.V (isElemAbelian_V_basic c) K ≤ centSub W) :
    resBarSub c hKW ≠ 1 := by
  intro h
  apply hact
  intro ψ hψ
  rw [mem_centSub]
  intro w hw
  have h1 : resBarSub c hKW ⟨ψ, hψ⟩ = 1 := by rw [h]; rfl
  have h2 : resBarSub c hKW ⟨ψ, hψ⟩ ⟨w, hw⟩ = ⟨w, hw⟩ := by
    simpa using congrArg (fun f : MulAut W => f ⟨w, hw⟩) h1
  calc ψ w = ((resBarSub c hKW ⟨ψ, hψ⟩ ⟨w, hw⟩ : W) :
        Vtil ⊥ c.V (isElemAbelian_V_basic c)) := (resBarSub_apply c hKW ⟨ψ, hψ⟩ ⟨w, hw⟩).symm
    _ = ((⟨w, hw⟩ : W) : Vtil ⊥ c.V (isElemAbelian_V_basic c)) := by rw [h2]
    _ = w := rfl

private theorem pCore_le_ker_comp {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h208 : S20_8 D) (h1930 : H1930 D)
    {W : Subgroup (Vtil ⊥ c.V (isElemAbelian_V_basic c))} {K : Subgroup G}
    (hK : K ∈ calC c.L)
    (hKW : barSub ⊥ c.V (isElemAbelian_V_basic c) K ≤ stabSub W)
    (hKstab : K ≤ stabTil (⊥ : Subgroup G) c.V)
    (φ₁ : ↥K →* ↥(barSub ⊥ c.V (isElemAbelian_V_basic c) K))
    (hφ₁ : ∀ k : ↥K, (φ₁ k).1 =
      actTil ⊥ c.V (isElemAbelian_V_basic c) ⟨(k : G), hKstab k.2⟩) :
    CFSG.pCore 2 ↥K ≤ ((resBarSub c hKW).comp φ₁).ker := by
  intro k hk
  rw [MonoidHom.mem_ker]
  have hV : IsElemAbelian 2 c.V := isElemAbelian_V_basic c
  have hkc : (k : G) ∈ Subgroup.centralizer (c.V : Set G) :=
    pCoreOf_le_centralizer_V_of_mem_calC c h208 h1930 hK
      (Subgroup.mem_map_of_mem K.subtype hk)
  have hone : actTil ⊥ c.V hV ⟨(k : G), hKstab k.2⟩ = 1 := by
    refine (actTil_eq_one_iff ⊥ c.V hV ⟨(k : G), hKstab k.2⟩).mpr ?_
    intro v hv
    rw [Subgroup.mem_bot]
    have h1 := Subgroup.mem_centralizer_iff.mp hkc v hv
    rw [h1.symm]
    group
  have h2 : φ₁ k = 1 := by
    refine Subtype.ext ?_
    rw [hφ₁ k]
    exact hone
  show resBarSub c hKW (φ₁ k) = 1
  rw [h2, map_one]

theorem exists_nontrivial_bar2_hom {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h208 : S20_8 D) (h1930 : H1930 D)
    {W : Subgroup (Vtil ⊥ c.V (isElemAbelian_V_basic c))} {K : Subgroup G}
    (hK : K ∈ calC c.L)
    (hW : barSub ⊥ c.V (isElemAbelian_V_basic c) c.L ≤ stabSub W)
    (hact : ¬ barSub ⊥ c.V (isElemAbelian_V_basic c) K ≤ centSub W) :
    ∃ f : Bar2 K →* MulAut W, f ≠ 1 := by
  classical
  have hV : IsElemAbelian 2 c.V := isElemAbelian_V_basic c
  have hKle : K ≤ c.L := hK.1.le
  have hKstab : K ≤ stabTil (⊥ : Subgroup G) c.V := fun k hk =>
    mem_stabTil_bot (uc22p22v_le_normalizer_conjClosure c.N D.Z (L_le_N c (hKle hk)))
  have hKW : barSub ⊥ c.V hV K ≤ stabSub W := (barSub_mono ⊥ c.V hV hKle).trans hW
  have hφ₂ := resBarSub_ne_one c hKW hact
  let φ₁ : ↥K →* ↥(barSub ⊥ c.V hV K) :=
    MonoidHom.codRestrict ((actTil ⊥ c.V hV).comp (Subgroup.inclusion hKstab))
      (barSub ⊥ c.V hV K) (fun k => actTil_mem_barSub ⊥ c.V hV k.2 (hKstab k.2))
  have hφ₁ : Function.Surjective φ₁ := by
    intro ψ
    obtain ⟨g, hgK, hg⟩ := (mem_barSub ⊥ c.V hV K ψ.1).1 ψ.2
    refine ⟨⟨(g : G), hgK⟩, Subtype.ext ?_⟩
    show actTil ⊥ c.V hV ⟨(g : G), hKstab hgK⟩ = ψ.1
    rw [show (⟨(g : G), hKstab hgK⟩ : ↥(stabTil (⊥ : Subgroup G) c.V)) = g from
      Subtype.ext rfl]
    exact hg
  have hker := pCore_le_ker_comp c h208 h1930 hK hKW hKstab φ₁ (fun _ => rfl)
  refine ⟨QuotientGroup.lift (CFSG.pCore 2 ↥K) ((resBarSub c hKW).comp φ₁) hker, ?_⟩
  intro h
  refine hφ₂ (MonoidHom.ext fun ψ => ?_)
  obtain ⟨k, rfl⟩ := hφ₁ ψ
  have h1 := congrArg (fun f : Bar2 K →* MulAut W => f (QuotientGroup.mk k)) h
  simpa [QuotientGroup.lift_mk] using h1

theorem exists_calC_not_le_centSub {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    {W : Subgroup (Vtil ⊥ c.V (isElemAbelian_V_basic c))} (hWne : W ≠ ⊥) :
    ∃ K ∈ calC c.L, ¬ barSub ⊥ c.V (isElemAbelian_V_basic c) K ≤ centSub W := by
  classical
  have hV : IsElemAbelian 2 c.V := isElemAbelian_V_basic c
  obtain ⟨K, hK, hLK⟩ := c.hL.1.2.2.2
  have hLstab : c.L ≤ stabTil (⊥ : Subgroup G) c.V := fun l hl =>
    mem_stabTil_bot (uc22p22v_le_normalizer_conjClosure c.N D.Z (L_le_N c hl))
  have hKtle : ∀ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom ≤ c.L := by
    intro t
    rw [hLK]
    exact le_iSup (fun t : D.T => K.map (MulAut.conj (t : G)).toMonoidHom) t
  have hKtstab : ∀ t : D.T,
      K.map (MulAut.conj (t : G)).toMonoidHom ≤ stabTil (⊥ : Subgroup G) c.V :=
    fun t => (hKtle t).trans hLstab
  have hKtcalC : ∀ t : D.T, K.map (MulAut.conj (t : G)).toMonoidHom ∈ calC c.L :=
    fun t => UC6S846.calC_map c.L (MulAut.conj (t : G))
      (Subgroup.mem_normalizer_iff_map_conj_eq.1 (c.hL.1.1 t.2)) hK
  by_contra hcon
  have hcon' : ∀ K' : Subgroup G, K' ∈ calC c.L →
      barSub ⊥ c.V hV K' ≤ centSub W := by
    intro K' hK'
    by_contra h
    exact hcon ⟨K', hK', h⟩
  have hcent : barSub ⊥ c.V hV c.L ≤ centSub W := by
    rw [hLK, barSub_iSup_of_le (V₀ := ⊥) hV hKtstab]
    exact iSup_le fun t => hcon' _ (hKtcalC t)
  have hbot : W ≤ fixV (barSub ⊥ c.V hV c.L) := by
    intro w hw φ hφ
    exact (mem_centSub.mp (hcent hφ)) w hw
  rw [fixV_barSub_eq_bot c hV le_rfl (uc22p22v_le_normalizer_conjClosure c.N D.Z)] at hbot
  exact hWne (le_bot_iff.mp hbot)

theorem n_lt_rkIdx_fixV (c : Ctx23L D Ch) (hDeg : KMinDegLow)
    (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D) (hE : UC22P20gExcFacts)
    (h1930 : H1930 D)
    {s : MulAut (Vtil ⊥ c.V (isElemAbelian_V_basic c))} (hs1 : s ≠ 1)
    (hs2 : orderOf s = 2)
    (hcomm : ∀ l ∈ barSub ⊥ c.V (isElemAbelian_V_basic c) c.L, Commute l s) :
    c.n + 1 < rkIdx (fixV (Subgroup.zpowers s)) := by
  have hV : IsElemAbelian 2 c.V := isElemAbelian_V_basic c
  have hstab : barSub ⊥ c.V hV c.L ≤ stabSub (commV (Subgroup.zpowers s)) :=
    le_stabSub_commV s _ hcomm
  have hne : commV (Subgroup.zpowers s) ≠ ⊥ := commV_zpowers_ne_bot s hs1
  obtain ⟨K, hK, hKact⟩ := exists_calC_not_le_centSub c hne
  exact n_lt_rkIdx_fixV_of_nontrivial_bar2 c hDeg h207 h209 hE h1930 hs1 hs2
    ⟨K, hK, exists_nontrivial_bar2_hom c h208 h1930 hK hstab hKact⟩

theorem n_lt_rkIdx_fixV_of_mem_N (c : Ctx23L D Ch) (hDeg : KMinDegLow)
    (h207 : S20_7 D) (h208 : S20_8 D) (h209 : S20_9 D) (hE : UC22P20gExcFacts)
    (h1930 : H1930 D) {x : c.N} (hs1 : actN c x ≠ 1) (hs2 : orderOf (actN c x) = 2)
    (hcomm : ∀ l ∈ barSub ⊥ c.V (isElemAbelian_V_basic c) c.L, Commute l (actN c x)) :
    c.n + 1 < rkIdx (fixV (Subgroup.zpowers (actN c x))) :=
  n_lt_rkIdx_fixV c hDeg h207 h208 h209 hE h1930 hs1 hs2 hcomm

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

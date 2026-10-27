module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
public import CFSG.LocalAnalysis.StandardType.GGF4QTwoReduction
public import CFSG.LocalAnalysis.StandardType.FF81.Reduction
public import CFSG.LocalAnalysis.StandardType.FF81.CurtisA2
public import CFSG.LargeExtraspecial.A2ModOrdCard
public import CFSG.LocalAnalysis.StandardType.GGF4QTwoOmegaNbrCore
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.Adapters.StatedClassicalOrders
import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreDeltaTransfer
import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreAbsorption

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

namespace FF81

variable {G : Type} [Group G]

theorem centralizer_conj_le_of_fusC {b : G} {L : Subgroup G} {z : Fin 3 → ↥L}
    (hloc : LocalFacts b L z) {g : G}
    (hg : g * b * g⁻¹ ∈ Subgroup.centralizer ({b} : Set G)) :
    Subgroup.centralizer ({g * b * g⁻¹} : Set G) ≤ Subgroup.centralizer ({b} : Set G) ⊔
      Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G) := by
  obtain ⟨n, hn, c, hc, he⟩ := hloc.fusC g hg
  set H := Subgroup.centralizer ({b} : Set G) ⊔
    Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G) with hH
  have hcn : c * n ∈ H := H.mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hn)
  intro w hw
  have hab : c * (n * b * n⁻¹) * c⁻¹ = (c * n) * b * (c * n)⁻¹ := by group
  rw [he, hab, Subgroup.mem_centralizer_iff] at hw
  have hw1 := hw _ (Set.mem_singleton _)
  have hw' : (c * n)⁻¹ * w * (c * n) ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro h rfl
    calc h * ((c * n)⁻¹ * w * (c * n))
        = (c * n)⁻¹ * ((c * n) * h * (c * n)⁻¹ * w) * (c * n) := by group
      _ = (c * n)⁻¹ * (w * ((c * n) * h * (c * n)⁻¹)) * (c * n) := by rw [hw1]
      _ = (c * n)⁻¹ * w * (c * n) * h := by group
  have hw2 : w = (c * n) * ((c * n)⁻¹ * w * (c * n)) * (c * n)⁻¹ := by group
  rw [hw2]
  exact H.mul_mem (H.mul_mem hcn (Subgroup.mem_sup_left hw')) (H.inv_mem hcn)

theorem iSup_frame_le {b : G} {L : Subgroup G} {z : Fin 3 → ↥L} {K : ℕ → Subgroup G} {t : G}
    [Finite G] (hloc : LocalFacts b L z) (hLb : L ≤ Subgroup.centralizer ({b} : Set G))
    (hmeet : ∃ g : G, g * b * g⁻¹ ∈ L) (hK : FrameSystem 5 b L K t) :
    (⨆ i : Fin (5 + 2), K (i : ℕ)) ≤ Subgroup.centralizer ({b} : Set G) ⊔
      Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G) := by
  set H := Subgroup.centralizer ({b} : Set G) ⊔
    Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G) with hH
  have hKL : ∀ j : Fin 5, K ((j : ℕ) + 2) ≤ L := fun j => by
    rw [← hK.sysL.2.1]
    exact le_iSup (fun i : Fin 5 => K ((i : ℕ) + 2)) j
  have hcomm : ∀ (X : Subgroup G) (w : G), (∀ a ∈ X, a * w = w * a) →
      ∀ g : G, g * b * g⁻¹ ∈ Subgroup.zpowers w →
        g * b * g⁻¹ ∈ Subgroup.centralizer ({b} : Set G) → X ≤ H := by
    intro X w hXw g hgw hgC a ha
    refine centralizer_conj_le_of_fusC hloc hgC ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro h rfl
    obtain ⟨k, hk⟩ := hgw
    rw [← hk]
    exact ((Commute.zpow_left (hXw a ha).symm k)).eq.symm ▸ rfl
  refine iSup_le fun i => ?_
  rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ 2 ≤ (i : ℕ) by omega) with h0 | h1 | h2
  ·
    rw [h0]
    obtain ⟨g, hg⟩ := hmeet
    exact hcomm (K 0) (g * b * g⁻¹) (fun a ha => (hK.comm_L a ha _ hg))
      g (Subgroup.mem_zpowers _) (hLb hg)
  ·
    rw [h1]
    obtain ⟨w, hwK, -, ⟨g, hgw⟩⟩ := hK.conj_b 3 (by norm_num)
    have hwL : w ∈ L := hKL 1 hwK
    have hgw' : g * b * g⁻¹ ∈ Subgroup.zpowers w := by
      rw [← hgw]
      exact Subgroup.mem_zpowers _
    have hgC : g * b * g⁻¹ ∈ Subgroup.centralizer ({b} : Set G) :=
      (Subgroup.zpowers_le.mpr (hLb hwL)) hgw'
    refine hcomm (K 1) w (fun a ha => ?_) g hgw' hgC
    exact hK.sysL'.2.2.1 (1 : Fin 5) (3 : Fin 5) (by decide) (by unfold adjA; decide) a ha w hwK
  ·
    obtain ⟨j, hj⟩ : ∃ j : Fin 5, (j : ℕ) + 2 = i := ⟨⟨(i : ℕ) - 2, by omega⟩, by simp; omega⟩
    rw [← hj]
    exact ((hKL j).trans hLb).trans le_sup_left

theorem card_ggAutomizer_le_384_of_monomial [Finite G] {Bs : Subgroup G} (x : Fin 4 → G)
    (hgen : ∀ c : G, (∀ i, x i * c = c * x i) → c ∈ Subgroup.centralizer (Bs : Set G))
    (hmono : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∃ (σ : Equiv.Perm (Fin 4))
      (ε : Fin 4 → ZMod 3), (∀ i, ε i ≠ 0) ∧ ∀ i, n * x i * n⁻¹ = x (σ i) ^ (ε i).val) :
    Nat.card (ggAutomizer ⊤ Bs) ≤ 384 := by
  classical
  have key : ∀ φ : ↥(ggAutomizer ⊤ Bs), ∃ (g : G)
      (q : Equiv.Perm (Fin 4) × (Fin 4 → {e : ZMod 3 // e ≠ 0})),
      (∀ b : ↥Bs, (((φ : MulAut ↥Bs) b : ↥Bs) : G) = g * b * g⁻¹) ∧
        ∀ i, g * x i * g⁻¹ = x (q.1 i) ^ ((q.2 i : ZMod 3)).val := by
    intro φ
    obtain ⟨g, -, hgN, hφ⟩ := mem_ggAutomizer_iff.mp φ.2
    obtain ⟨σ, ε, hε, hσ⟩ := hmono g hgN
    exact ⟨g, (σ, fun i => ⟨ε i, hε i⟩), hφ, hσ⟩
  choose g F hg hF using key
  have hinj : Function.Injective F := by
    intro φ ψ h
    have hc : (g ψ)⁻¹ * g φ ∈ Subgroup.centralizer (Bs : Set G) := by
      refine hgen _ fun i => ?_
      have e1 := hF φ i
      rw [h] at e1
      have e3 : g φ * x i * (g φ)⁻¹ = g ψ * x i * (g ψ)⁻¹ := e1.trans (hF ψ i).symm
      calc x i * ((g ψ)⁻¹ * g φ) = (g ψ)⁻¹ * (g ψ * x i * (g ψ)⁻¹) * g φ := by group
        _ = (g ψ)⁻¹ * (g φ * x i * (g φ)⁻¹) * g φ := by rw [e3]
        _ = (g ψ)⁻¹ * g φ * x i := by group
    refine Subtype.ext (MulEquiv.ext fun b => Subtype.ext ?_)
    rw [hg φ b, hg ψ b]
    have hb := Subgroup.mem_centralizer_iff.mp hc b b.2
    calc g φ * b * (g φ)⁻¹ = g ψ * (b * ((g ψ)⁻¹ * g φ)) * (g φ)⁻¹ := by rw [hb]; group
      _ = g ψ * b * (g ψ)⁻¹ := by group
  calc Nat.card (ggAutomizer ⊤ Bs)
      ≤ Nat.card (Equiv.Perm (Fin 4) × (Fin 4 → {e : ZMod 3 // e ≠ 0})) :=
        Nat.card_le_card_of_injective F hinj
    _ = 384 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm, Fintype.card_fun,
        Fintype.card_fin]
      rfl

theorem normalizer_le_sup_centralizer_of_automizer_le {L K Bs : Subgroup G}
    (h : ggAutomizer ⊤ Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs) :
    Subgroup.normalizer (Bs : Set G) ≤ (L ⊔ K) ⊔ Subgroup.centralizer (Bs : Set G) := by
  intro n hn
  have hφ : ggConjAut Bs hn ∈ ggAutomizer (L ⊔ K) Bs :=
    (sup_le (ggAutomizer_mono Bs le_sup_left) (ggAutomizer_mono Bs le_sup_right))
      (h (ggConjAut_mem_ggAutomizer (Subgroup.mem_top n) hn))
  obtain ⟨g, hgLK, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
  have hc : g⁻¹ * n ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have e : n * b * n⁻¹ = g * b * g⁻¹ := hg ⟨b, hb⟩
    calc b * (g⁻¹ * n) = g⁻¹ * (g * b * g⁻¹) * n := by group
      _ = g⁻¹ * (n * b * n⁻¹) * n := by rw [e]
      _ = g⁻¹ * n * b := by group
  have hn' : n = g * (g⁻¹ * n) := by group
  rw [hn']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgLK) (Subgroup.mem_sup_right hc)

theorem mem_normalizer_sup {A C : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hC : g ∈ Subgroup.normalizer (C : Set G)) : g ∈ Subgroup.normalizer ((A ⊔ C : Subgroup G) : Set G) := by
  have key : ∀ c : G, c ∈ Subgroup.normalizer (A : Set G) → c ∈ Subgroup.normalizer (C : Set G) →
      A ⊔ C ≤ (A ⊔ C).comap (MulAut.conj c).toMonoidHom := fun c hcA hcC =>
    sup_le (fun a ha => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hcA a).mp ha))
      (fun a ha => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hcC a).mp ha))
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact key g hA hC hh
  · intro hh
    have h2 := key g⁻¹ (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hC) hh
    simpa [MulAut.conj_apply, mul_assoc] using h2

theorem sup_eq_top_of_end [IsSimpleGroup G] {L K Bs M : Subgroup G} {b : G} (hM : M ≠ ⊥)
    (hMLK : M ≤ L ⊔ K) (hbN : b ∈ Subgroup.normalizer ((L ⊔ K : Subgroup G) : Set G))
    (hbBs : b ∈ Bs)
    (htop : ⊤ ≤ Subgroup.centralizer ({b} : Set G) ⊔ Subgroup.normalizer (Bs : Set G))
    (hCb : Subgroup.centralizer ({b} : Set G) = Subgroup.zpowers b ⊔ M)
    (hNBs : Subgroup.normalizer (Bs : Set G) ≤ (L ⊔ K) ⊔ Subgroup.centralizer (Bs : Set G)) :
    L ⊔ K = ⊤ := by
  set H := L ⊔ K with hH
  have hHN : H ≤ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer
  have hCbN : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (H : Set G) := by
    rw [hCb]
    exact sup_le (Subgroup.zpowers_le.mpr hbN) (hMLK.trans hHN)
  have hCBs : Subgroup.centralizer (Bs : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbBs)
  have hNN : Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (H : Set G) :=
    hNBs.trans (sup_le hHN (hCBs.trans hCbN))
  have htopN : Subgroup.normalizer (H : Set G) = ⊤ :=
    top_le_iff.mp (htop.trans (sup_le hCbN hNN))
  have : H.Normal := Subgroup.normalizer_eq_top_iff.mp htopN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
  · exact absurd (eq_bot_iff.mpr (hMLK.trans h.le)) hM
  · exact h

theorem card_of_ggHasLabel_E6_two
    {R : Type} [Group R] (hna : ∃ a c : R, a * c ≠ c * a)
    (h : GGHasLabel ⟨.E6, 0, 1⟩ R) : Nat.card R = ordE6 2 := by
  have h' := largeEvenRawDatum_markedModel (lab := ⟨.E6, 0, 1⟩)
    (by unfold LargeEvenInLambda2; norm_num) (Q := fun R' _ _ _ => Nonempty (R ≃* R'))
    (fun R' _ _ _ ⟨e⟩ => by
      obtain ⟨a, c, hac⟩ := hna
      exact ⟨e a, e c, fun hh => hac (e.injective (by rw [map_mul, map_mul, hh]))⟩) h
  obtain ⟨R', _, I, F, ⟨e⟩, hM⟩ := largeEvenRawDatum_exists h'
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_E6
    (by simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM)

theorem end_facts
    [Finite G] [IsSimpleGroup G] (hna : ∃ a c : G, a * c ≠ c * a)
    (hchar : IsCharTwoType G) (hKP : KProper InCatalog G)
    (hCurtis : CurtisA2) (hLoc : LocalSetup) (h1 : PropOne) (h2 : PropTwo)
    (hFrame : FrameStep) (hY : ConstructY)
    {B Bs M : Subgroup G} {b : G} (hA : HypA G 5 b M) (hbBs : b ∈ Bs) (hBst : GGBstar 3 B Bs)
    (hcard : Nat.card Bs = 3 ^ 4) (hNM : Bs ≤ Subgroup.normalizer (M : Set G))
    (hcen : Bs ⊓ Subgroup.centralizer (M : Set G) = Subgroup.zpowers b)
    (hZ : Subgroup.center M = ⊥) (hG : Nat.card G = ordE6 2) :
    ⊤ ≤ Subgroup.centralizer ({b} : Set G) ⊔ Subgroup.normalizer (Bs : Set G) ∧
      Subgroup.centralizer ({b} : Set G) = Subgroup.zpowers b ⊔ M ∧
      (Nat.card (ggAutomizer ⊤ Bs) = 1152 ∨ Nat.card (ggAutomizer ⊤ Bs) ≤ 384) ∧ M ≠ ⊥ := by
  classical
  obtain ⟨z₀, hz₀⟩ := exists_model_of_statedClassicalModel (Or.inl rfl) hA.model
  have hinner : ∀ β ∈ Bs, ∃ m ∈ M, ∀ k ∈ M, β * k * β⁻¹ = m * k * m⁻¹ := by
    intro β hβ
    have hβN := hNM hβ
    have hα3 : M.normalizerMonoidHom ⟨β, hβN⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have h3 : (⟨β, hβN⟩ : ↥(Subgroup.normalizer (M : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hBst.2.1.2 β hβ)
      rw [h3, map_one]
    obtain ⟨m, hm⟩ := hz₀.inner_odd _ 3 (by decide) hα3
    refine ⟨m, m.2, fun k hk => ?_⟩
    have e := congrArg (fun φ : MulAut ↥M => ((φ ⟨k, hk⟩ : ↥M) : G)) hm
    simpa only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv] using e
  have h27 : Nat.card ↥(Bs ⊓ M) = 27 :=
    card_bstar_inf_of_split hBst hZ hNM hinner hcen hcard hA.ord
  have hsplit := ggBstar_split_of_inner hBst hZ hNM hinner
  have hM1 : M ≠ ⊥ := by
    rintro rfl
    rw [inf_bot_eq, Subgroup.card_bot] at h27
    exact absurd h27 (by norm_num)
  have hMna : ∃ a ∈ M, ∃ c ∈ M, a * c ≠ c * a := by
    by_contra hcon
    push Not at hcon
    have htop : Subgroup.center ↥M = ⊤ := by
      rw [eq_top_iff]
      intro m _
      rw [Subgroup.mem_center_iff]
      intro n
      exact Subtype.ext (hcon n n.2 m m.2)
    have h1' : Nat.card ↥M = 1 := by
      have := Subgroup.card_top (G := ↥M)
      rw [← htop, hZ, Subgroup.card_bot] at this
      exact this.symm
    have h2' : Nat.card ↥(Bs ⊓ M) ≤ Nat.card ↥M := Subgroup.card_le_of_le inf_le_right
    omega
  have hE : CFSG.Assembly.IsElemAbelian 3 ((Bs ⊓ M).subgroupOf M) :=
    CFSG.Open.IsElemAbelian.subgroupOf (CFSG.Open.IsElemAbelian.mono hBst.2.1 inf_le_left) M
  have hEcard : Nat.card ((Bs ⊓ M).subgroupOf M) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h27]
  obtain ⟨g, hg⟩ := hz₀.torus _ hE hEcard
  set z : Fin 3 → ↥M := fun i => g * z₀ i * g⁻¹ with hzdef
  have hz : GGFF.Model ↥M z := hz₀.conj g
  have hz1 : ∀ v, CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v =
      g * CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z₀ v * g⁻¹ := fun v =>
    GGFF.vecElt_map (MulAut.conj g) z₀ v
  have hz2 : ∀ v, CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v =
      ((CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v : ↥M) : G) := fun v =>
    GGFF.vecElt_map M.subtype z v
  have hpow : ∀ i, GGFF.zs z i ^ 3 = 1 := fun i => by
    simpa using congrArg Subtype.val (hz.pow_z i)
  have hcomm : ∀ i j, GGFF.zs z i * GGFF.zs z j = GGFF.zs z j * GGFF.zs z i := fun i j => by
    simpa using congrArg Subtype.val (hz.comm_z i j)
  have htor : GGFF.tor (GGFF.zs z) = Bs ⊓ M := by
    ext w
    rw [GGFF.mem_tor hpow hcomm]
    constructor
    · rintro ⟨v, rfl⟩
      rw [hz2]
      exact Subgroup.mem_subgroupOf.mp ((hg _).mpr ⟨v, hz1 v⟩)
    · intro hw
      obtain ⟨v, hv⟩ := (hg ⟨w, hw.2⟩).mp (Subgroup.mem_subgroupOf.mpr hw)
      refine ⟨v, ?_⟩
      rw [hz2, hz1, ← hv]
  have hBt : GGFF.Bt b z = Bs := by
    show Subgroup.zpowers b ⊔ GGFF.tor (GGFF.zs z) = Bs
    rw [htor]
    refine le_antisymm (sup_le (Subgroup.zpowers_le.mpr hbBs) inf_le_left) fun w hw => ?_
    obtain ⟨t, ht, c, hc, rfl⟩ := hsplit w hw
    rw [hcen] at hc
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left hc)
  have hloc : LocalFacts b M z := hLoc G hna hchar 5 b M hA z hz
  have hmeet : ∃ g : G, g * b * g⁻¹ ∈ M := h1 G hna hchar hKP 5 b M hA z hz hloc
  have hout : PropTwoOut b M z := h2 G hna hchar 5 b M hA z hz hloc hmeet
  have hafter : AfterProp2 b M z := ⟨hz, hloc, hmeet, hout⟩
  obtain ⟨Kf, t, hKf⟩ := hFrame G hna hchar 5 b M hA z hafter
  have hYd := hY hCurtis G hna hchar 5 b M hA Kf t ⟨z, hafter, hKf⟩
  have hle := iSup_frame_le hloc hA.le hmeet hKf
  have hYtop : (⨆ i : Fin (5 + 2), Kf (i : ℕ)) = ⊤ := by
    rcases hYd.lab with hPSL | ⟨-, hE6⟩
    · exfalso
      have hc := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hPSL
      have hdvd := Subgroup.card_subgroup_dvd_card (⨆ i : Fin (5 + 2), Kf (i : ℕ))
      rw [hc, hG] at hdvd
      revert hdvd
      decide
    · apply Subgroup.eq_top_of_card_eq
      rw [hG]
      obtain ⟨a, ha, c, hc, hac⟩ := hMna
      exact card_of_ggHasLabel_E6_two
        ⟨⟨a, hYd.le ha⟩, ⟨c, hYd.le hc⟩, fun h => hac (congrArg Subtype.val h)⟩ hE6
  have hCb : Subgroup.centralizer ({b} : Set G) = Subgroup.zpowers b ⊔ M := by
    have h := hYd.cen_b
    rw [hYtop, inf_top_eq] at h
    exact h
  have hgen : ∀ c : G, (∀ i, xs b z i * c = c * xs b z i) →
      c ∈ Subgroup.centralizer ((GGFF.Bt b z : Subgroup G) : Set G) := by
    intro c hc
    rw [GGFF.SettingCore.Bt_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro w (rfl | rfl | rfl | rfl)
    · exact hc 0
    · exact hc 1
    · exact hc 2
    · exact hc 3
  refine ⟨?_, hCb, ?_, hM1⟩
  · rw [← hYtop, ← hBt]
    exact hle
  · rw [← hBt]
    rcases hout with ⟨hmono, -⟩ | ⟨-, h1152, -, -⟩
    · exact Or.inr (card_ggAutomizer_le_384_of_monomial (xs b z) hgen hmono.2)
    · exact Or.inl h1152

end FF81

theorem card_eq_ordE6_of_mulEquiv_ggU
    {G : Type} [Group G] [IsSimpleGroup G] (hna : ∃ a c : G, a * c ≠ c * a)
    (e : G ≃* (ggU .E6 0 1).K) : Nat.card G = ordE6 2 := by
  have hadm : StatedLieAdmissible .E6 0 2 1 := ⟨Nat.prime_two, le_refl 1, rfl⟩
  have hrk : 2 ≤ (ggU .E6 0 1).D.rank := by
    rw [lieUniversal_rank_eq_bnRank .E6 0 2 1 Nat.prime_two hadm (by decide)]
    decide
  obtain ⟨-, hM⟩ := ggU_perfect_lieModel hadm hrk
  have hcG : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, c, hac⟩ := hna
      have ha : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
      exact hac (Subgroup.mem_center_iff.mp ha c).symm
  have hZ : Subgroup.center (ggU .E6 0 1).K = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    have hk' : e.symm k ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff] at hk ⊢
      intro g
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hk (e g)
    rw [hcG, Subgroup.mem_bot] at hk'
    rw [Subgroup.mem_bot]
    simpa using congrArg e hk'
  have hc := CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_E6 hM
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).toEquiv] at hc
  rw [Nat.card_congr e.toEquiv, hc]

theorem ff81bG0Input_of_pieces
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hLoc : FF81.LocalSetup) (h1 : FF81.PropOne) (h2 : FF81.PropTwo) (hFrame : FF81.FrameStep)
    (hY : FF81.ConstructY) : FF81bG0Input := by
  have hCurtis : FF81.CurtisA2 := FF81.curtisA2_holds
  intro G _ _ B Bs x L D J hR hW hq y K hNb hWK hmark ⟨e⟩
  have hAt : GGSecFiveWeylAt 3 B Bs x L D J CoxeterMatrix.F₄ := ⟨y, K, hNb, hWK⟩
  obtain ⟨⟨hsimp, hna, hKP, hchar, -, hβ, hS, hst⟩, hBs, hDJ⟩ := hR.1
  have := hsimp
  have hcardBs : Nat.card Bs = 3 ^ 4 := card_bstar_F4 hTBF hWI hR hW hAt
  have hBB : Nat.card B = 3 ^ twoLocalPrimeRank 3 G := hS.1.2.1
  have hm4 : twoLocalPrimeRank 3 G ≤ 4 := by
    have hle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBs.1
    rw [hBB, hcardBs] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  have hBBs : B = Bs := by
    apply Subgroup.eq_of_le_of_card_ge hBs.1
    rw [hcardBs, hBB]
    exact Nat.pow_le_pow_right (by norm_num) hβ.2.2.2
  have hG : Nat.card G = ordE6 2 := card_eq_ordE6_of_mulEquiv_ggU hna e
  have hNL : Bs ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨-, lab, -, hraw⟩ := hq
    obtain ⟨R, _, I, F, -, -, θ, -, hN, -⟩ := largeEvenRawDatum_exists hraw
    exact hN
  have hNK : Bs ≤ Subgroup.normalizer (K : Set G) :=
    hBBs ▸ (isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ hNb)).2
  have h1152 : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) = 1152 := by
    obtain ⟨f, -⟩ := hWK
    rw [← Nat.card_congr f.toEquiv, FrameRoute.coxeterF4_eq]
    exact CFSG.RankThree.PartOne.K133H.card_weylGroup_F4
  have hjoin : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  have hAut : Nat.card (ggAutomizer ⊤ Bs) = 1152 ∨ Nat.card (ggAutomizer ⊤ Bs) ≤ 384 →
      Subgroup.normalizer (Bs : Set G) ≤ (L ⊔ K) ⊔ Subgroup.centralizer (Bs : Set G) := by
    intro h
    have hle := Subgroup.card_le_of_le hjoin
    rcases h with h | h
    · exact FF81.normalizer_le_sup_centralizer_of_automizer_le
        (Subgroup.eq_of_le_of_card_ge hjoin (by omega)).ge
    · omega
  have hKG0 : K ≤ ggG0 3 B x L D J :=
    le_sup_of_le_right (le_iSup_of_le y (le_iSup_of_le K (le_iSup_of_le ⟨hNb.1, hNb.2⟩ le_rfl)))
  have hfin : ∀ hLK : L ⊔ K = ⊤, ggG0 3 B x L D J = ⊤ := fun hLK => by
    rw [eq_top_iff, ← hLK]
    exact sup_le le_sup_left hKG0
  rcases hmark with hmL | hmK
  ·
    have hxB : x ∈ B := hS.2.1
    have hx1 : x ≠ 1 := hS.2.2.1
    have hox : orderOf x = 3 := orderOf_eq_prime (hS.1.1.2 x hxB) hx1
    have hLC : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
    have hN := le_normalizer_of_sstar_markingA hS (by norm_num) hmL
    have hZ : Subgroup.center L = ⊥ :=
      center_eq_bot_of_f4EndMarking
        (P := fun lab => lab.tag = .A ∧ lab.rank = 5 ∧ lab.n = 1)
        (fun lab hl => ⟨Or.inl ⟨hl.1, hl.2.1⟩, hl.2.2⟩) hmL
    have hM := statedClassicalModel_of_markingA hmL hZ
    have hA2 : ∀ P : Sylow 3 ↥(Subgroup.centralizer (L : Set G)), IsCyclic P := fun P =>
      isCyclic_sylow_of_le_centralizer_of_forall hS.2.2.2.2 le_rfl P
    have hA3 := (twoLocalPrimeRank_centralizer_eq_of_config hR.1).symm
    have hA4 := ffNotWeaklyClosed_of_conj
      (FrameRoute.ggFrameA4Input_F4 hTBF hWI G B Bs x L D J hR hW hAt hq x hxB hx1)
    have hA : FF81.HypA G 5 x L := ⟨Or.inl rfl, hox, hLC, hN, hM, hA2, hA3, hA4⟩
    have hxBs : x ∈ Bs := hBs.1 hxB
    obtain ⟨htop, hCb, hcard, hL1⟩ := FF81.end_facts hna hchar hKP hCurtis hLoc h1 h2 hFrame hY
      hA hxBs hBs hcardBs hNL (GGConfig.bstar_inf_centralizer_L hR.1) hZ hG
    have hxL : x ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun l hl =>
        (Subgroup.mem_centralizer_iff.mp (hLC hl) x (Set.mem_singleton x)).symm)
    exact hfin (FF81.sup_eq_top_of_end hL1 le_sup_left
      (FF81.mem_normalizer_sup hxL (hNK hxBs)) hxBs htop hCb (hAut hcard))
  ·
    obtain ⟨-, hyB, hy1, hKy, hPC, -⟩ := hNb.1
    have hy3 : y ^ 3 = 1 := hS.1.1.2 y hyB
    have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have hZ : Subgroup.center K = ⊥ :=
      center_eq_bot_of_f4EndMarking
        (P := fun lab => lab.tag = .A ∧ lab.rank = 5 ∧ lab.n = 1)
        (fun lab hl => ⟨Or.inl ⟨hl.1, hl.2.1⟩, hl.2.2⟩) hmK
    obtain ⟨U, E, hUK, hEK, hU, hU2, hEU, hE, hEcard⟩ :=
      exists_torus_of_markingA (n := 5) le_rfl hmK
    have hcycK : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S →
        IsCyclic S := fun S hS' hS3 =>
      isCyclic_of_le_centralizer_of_torus hZ hUK hEK hU hU2 hEU hE hEcard
        (by omega) hS' hS3
    have hcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
      ⟨hKy, hPC.2.1, isQuasisimple_of_largeEvenMarking hmK⟩
    have hN := le_normalizer_of_isComponentOf_cyclic hcomp
      (fun S _ hSK hS3 => hcycK S hSK hS3)
      ⟨E, hEK, (haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩; IsPGroup.of_card hEcard),
        not_isCyclic_of_isElemAbelian_three_pow hE hEcard (by norm_num)⟩
    have hM := statedClassicalModel_of_markingA hmK hZ
    have hA2 : ∀ P : Sylow 3 ↥(Subgroup.centralizer (K : Set G)), IsCyclic P := fun P =>
      isCyclic_sylow_of_le_centralizer_of_forall hcycK le_rfl P
    have hyK : y ∉ K := by
      intro hyK'
      have : (⟨y, hyK'⟩ : K) ∈ Subgroup.center K := by
        rw [Subgroup.mem_center_iff]
        intro k
        exact Subtype.ext
          (Subgroup.mem_centralizer_iff.mp (hKy k.2) y (Set.mem_singleton y)).symm
      rw [hZ, Subgroup.mem_bot] at this
      exact hy1 (congrArg Subtype.val this)
    have hA3 : twoLocalPrimeRank 3 G =
        twoLocalPrimeRank 3 ↥(Subgroup.centralizer ({y} : Set G)) := by
      have h1' := le_twoLocalPrimeRank_centralizer_of_torus hy3 hy1 hKy hyK hUK hEK
        hU hU2 hEU hE hEcard
      have h2' : twoLocalPrimeRank 3 ↥(Subgroup.centralizer ({y} : Set G)) ≤
          twoLocalPrimeRank 3 G :=
        CFSG.LargeEvenClassification.Helpers.twoLocalPRank_subgroup_le
          (by norm_num : 1 < 3) (Subgroup.centralizer ({y} : Set G))
      have h4 : 4 ≤ twoLocalPrimeRank 3 G := hβ.2.2.2
      omega
    have hA4 := ffNotWeaklyClosed_of_conj
      (FrameRoute.ggFrameA4Input_F4 hTBF hWI G B Bs x L D J hR hW hAt hq y hyB hy1)
    have hA : FF81.HypA G 5 y K := ⟨Or.inl rfl, hoy, hKy, hN, hM, hA2, hA3, hA4⟩
    have hyBs : y ∈ Bs := hBs.1 hyB
    have hcen : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y :=
      hBBs ▸ inf_centralizer_eq_zpowers_of_sHat hNb.1
    obtain ⟨htop, hCb, hcard, hK1⟩ := FF81.end_facts hna hchar hKP hCurtis hLoc h1 h2 hFrame hY
      hA hyBs hBs hcardBs hNK hcen hZ hG
    have hyK' : y ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun k hk =>
        (Subgroup.mem_centralizer_iff.mp (hKy hk) y (Set.mem_singleton y)).symm)
    exact hfin (FF81.sup_eq_top_of_end hK1 le_sup_right
      (FF81.mem_normalizer_sup (hNL hyBs) hyK') hyBs htop hCb (hAut hcard))

end CFSG.StandardType

end
